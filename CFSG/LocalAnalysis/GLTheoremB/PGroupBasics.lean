module

public import CFSG.LocalAnalysis.GLTheoremB.Defs
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.GLBDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

theorem elemAbelian_comm {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem isElemAbelian_mono {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem exists_mul_of_mem_sup {A B : Subgroup G} (hAB : A ≤ Subgroup.centralizer (B : Set G))
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (hAB ha) b hb).symm
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ a ∈ A, ∃ b ∈ B, x = a * b) ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, B.one_mem, (mul_one x).symm⟩
    · exact ⟨1, A.one_mem, x, hx, (one_mul x).symm⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  · rintro x y - - ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hc a' ha' b hb]
      _ = a * a' * (b * b') := by group
  · rintro x - ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by
        rw [← hc a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)]

theorem isElemAbelian_sup_of_commute {p : ℕ} {A B : Subgroup G} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    IsElemAbelian p (A ⊔ B) := by
  have hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (hAB ha) b hb).symm
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_of_mem_sup hAB x.2
    obtain ⟨a', ha', b', hb', hy⟩ := exists_mul_of_mem_sup hAB y.2
    change (x : G) * y = y * x
    rw [hx, hy]
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hc a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [elemAbelian_comm hA ha ha', elemAbelian_comm hB hb hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hc a ha b' hb']
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hAB hx
    have hab : Commute a b := hc a ha b hb
    rw [hab.mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

theorem exists_le_isElemAbelian_card {p : ℕ} [Fact p.Prime] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian p E) {n : ℕ} (hn : p ^ n ∣ Nat.card E) :
    ∃ K : Subgroup G, K ≤ E ∧ IsElemAbelian p K ∧ Nat.card K = p ^ n := by
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime p hn
  refine ⟨K'.map E.subtype, Subgroup.map_subtype_le K', ?_, ?_⟩
  · exact isElemAbelian_mono hE (Subgroup.map_subtype_le K')
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK']

theorem not_isCyclic_of_isElemAbelian {p : ℕ} [Fact p.Prime] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian p E) (hcard : p ^ 2 ≤ Nat.card E) : ¬ IsCyclic E := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have h1 : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : g ^ p = 1 := Subtype.ext (by simpa using hE.2 g.1 g.2)
  have h3 : orderOf g ≤ p := Nat.le_of_dvd (Fact.out : p.Prime).pos (orderOf_dvd_of_pow_eq_one h2)
  have h4 : p < p ^ 2 := by
    have := (Fact.out : p.Prime).one_lt
    nlinarith
  omega

theorem exists_card_eq_pow {p : ℕ} [Fact p.Prime] [Finite G] {P : Subgroup G} (hP : IsPGroup p P) :
    ∃ k : ℕ, Nat.card P = p ^ k :=
  IsPGroup.iff_card.1 hP

theorem mem_gLBConj {g y : G} {H : Subgroup G} : y ∈ GLBConj g H ↔ g * y * g⁻¹ ∈ H := by
  unfold GLBConj
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro h
    exact ⟨g * y * g⁻¹, h, by simp [mul_assoc]⟩

theorem gLBConj_gLBConj (x y : G) (H : Subgroup G) :
    GLBConj x (GLBConj y H) = GLBConj (y * x) H := by
  ext z
  simp only [mem_gLBConj]
  rw [show y * (x * z * x⁻¹) * y⁻¹ = y * x * z * (y * x)⁻¹ by group]

theorem gLBConj_one (H : Subgroup G) : GLBConj 1 H = H := by
  ext z
  simp [mem_gLBConj]

theorem gLBConj_mono (g : G) {H K : Subgroup G} (h : H ≤ K) : GLBConj g H ≤ GLBConj g K :=
  fun _ hz => mem_gLBConj.2 (h (mem_gLBConj.1 hz))

theorem gLBConj_eq_of_mem_normalizer {g : G} {Q : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) : GLBConj g Q = Q := by
  ext z
  rw [mem_gLBConj]
  exact ((Subgroup.mem_normalizer_iff.1 hg) z).symm

theorem isPPlane_gLBConj {p : ℕ} (g : G) {D : Subgroup G} (hD : IsPPlane p D) :
    IsPPlane p (GLBConj g D) := by
  refine ⟨CFSG.SectionRank.isElemAbelian_map hD.1 _, ?_⟩
  rw [GLBConj, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  exact hD.2

theorem le_normalizer_gLBConj {Q D : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (Q : Set G)) (hD : Q ≤ Subgroup.normalizer (D : Set G)) :
    Q ≤ Subgroup.normalizer (GLBConj y D : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hq' : y * q * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hy q).1 hq
  rw [mem_gLBConj, mem_gLBConj, show y * (q * h * q⁻¹) * y⁻¹ =
    (y * q * y⁻¹) * (y * h * y⁻¹) * (y * q * y⁻¹)⁻¹ by group]
  exact (Subgroup.mem_normalizer_iff.1 (hD hq') (y * h * y⁻¹))

theorem isConnectingStep_symm {p : ℕ} {X A B : Subgroup G} (h : IsConnectingStep p X A B) :
    IsConnectingStep p X B A :=
  ⟨h.2.1, h.1, Subgroup.le_centralizer_iff.1 h.2.2⟩

theorem reflTransGen_isConnectingStep_symm {p : ℕ} {X E E' : Subgroup G}
    (hr : Relation.ReflTransGen (IsConnectingStep p X) E E') :
    Relation.ReflTransGen (IsConnectingStep p X) E' E := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (isConnectingStep_symm hbc) ih

theorem IsTwoConnectedIn.symm' {p : ℕ} {X E E' : Subgroup G} (h : IsTwoConnectedIn p X E E') :
    IsTwoConnectedIn p X E' E :=
  ⟨h.2.1, h.1, reflTransGen_isConnectingStep_symm h.2.2⟩

theorem IsTwoConnectedIn.trans' {p : ℕ} {X E E' E'' : Subgroup G} (h₁ : IsTwoConnectedIn p X E E')
    (h₂ : IsTwoConnectedIn p X E' E'') : IsTwoConnectedIn p X E E'' :=
  ⟨h₁.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩

theorem IsTwoConnectedIn.mono' {p : ℕ} {X Y E E' : Subgroup G} (hXY : X ≤ Y)
    (h : IsTwoConnectedIn p X E E') : IsTwoConnectedIn p Y E E' := by
  have hs : IsConnectingStep p X ≤ IsConnectingStep p Y := fun A B hAB =>
    ⟨⟨hAB.1.1.trans hXY, hAB.1.2⟩, ⟨hAB.2.1.1.trans hXY, hAB.2.1.2⟩, hAB.2.2⟩
  exact ⟨⟨h.1.1.trans hXY, h.1.2⟩, ⟨h.2.1.1.trans hXY, h.2.1.2⟩,
    Relation.ReflTransGen.mono hs _ _ h.2.2⟩

theorem isTwoConnectedIn_of_le {p : ℕ} {X A E : Subgroup G} (hA : IsNoncyclicElemAbelianIn p X A)
    (hE : IsNoncyclicElemAbelianIn p X E) (hAE : A ≤ E) : IsTwoConnectedIn p X A E :=
  ⟨hA, hE, Relation.ReflTransGen.single ⟨hA, hE, fun _ ha => Subgroup.mem_centralizer_iff.2
    fun _ he => elemAbelian_comm hE.2.1 he (hAE ha)⟩⟩

end CFSG.LocalAnalysis.GLTheoremB

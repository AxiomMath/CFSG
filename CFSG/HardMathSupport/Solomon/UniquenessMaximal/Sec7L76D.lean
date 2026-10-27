module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85Aux
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.Prop98Proof

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_dvd_card_sup_of_coprime {S W : Subgroup G} (hSW : S ≤ Subgroup.normalizer (W : Set G))
    (hS : ¬ 3 ∣ Nat.card S) (hW : ¬ 3 ∣ Nat.card W) : ¬ 3 ∣ Nat.card (S ⊔ W : Subgroup G) := by
  intro hd
  have h := Lemma85Aux.card_sup_mul_card_inf' hSW
  have h1 : 3 ∣ Nat.card S * Nat.card W := h ▸ Dvd.dvd.mul_right hd _
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h1 with h2 | h2
  · exact hS h2
  · exact hW h2

omit [Finite G] in
private theorem conj_mem_closure_three {Y : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (Y : Set G)) {z : G}
    (hz : z ∈ Subgroup.closure {g : G | g ∈ Y ∧ IsPGroup 3 (Subgroup.zpowers g)}) :
    b * z * b⁻¹ ∈ Subgroup.closure {g : G | g ∈ Y ∧ IsPGroup 3 (Subgroup.zpowers g)} := by
  induction hz using Subgroup.closure_induction with
  | mem g hg =>
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.1 hb g).1 hg.1, ?_⟩
    have hmap : Subgroup.zpowers (b * g * b⁻¹) =
        (Subgroup.zpowers g).map (MulAut.conj b).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hmap]
    exact hg.2.map _
  | one => simp
  | mul x y _ _ hx hy =>
    have := mul_mem hx hy
    convert this using 1
    group
  | inv x _ hx =>
    have := inv_mem hx
    convert this using 1
    group

theorem le_normalizer_closure_three {B Y : Subgroup G} (hBY : B ≤ Subgroup.normalizer (Y : Set G)) :
    B ≤ Subgroup.normalizer
      (Subgroup.closure {g : G | g ∈ Y ∧ IsPGroup 3 (Subgroup.zpowers g)} : Set G) := by
  intro b hb
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  exact conj_mem_closure_three (hBY hb) hz

theorem frattini_two {S W I : Subgroup G} (hS : IsPGroup 2 S)
    (hSmax : ∀ Q : Subgroup G, IsPGroup 2 Q → S ≤ Q → Q ≤ S ⊔ W → Q = S)
    (hSW : S ≤ Subgroup.normalizer (W : Set G)) (hWI : W ≤ I)
    (hcomm : ∀ s ∈ S, ∀ g ∈ I, s * g * s⁻¹ * g⁻¹ ∈ W) :
    ∀ g ∈ I, ∃ j ∈ I ⊓ Subgroup.normalizer (S : Set G), ∃ w ∈ W, g = j * w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg
  set R : Subgroup G := S ⊔ W with hR
  have hSR : S ≤ R := le_sup_left
  let Q' : Subgroup G := S.map (MulAut.conj g⁻¹).toMonoidHom
  have hQ'R : Q' ≤ R := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 := hcomm s⁻¹ (inv_mem hs) g⁻¹ (inv_mem hg)
    have h2 : g⁻¹ * s * g⁻¹⁻¹ = s * (s⁻¹ * g⁻¹ * s⁻¹⁻¹ * g⁻¹⁻¹) := by group
    show g⁻¹ * s * g⁻¹⁻¹ ∈ R
    rw [h2]
    exact mul_mem (hSR hs) ((le_sup_right : W ≤ S ⊔ W) h1)
  have hQ'2 : IsPGroup 2 Q' := hS.map _
  have hmax : ∀ Q'' : Subgroup G, S ≤ Q'' → Q'' ≤ R → IsPGroup 2 Q'' → Q'' = S :=
    fun Q'' h1 h2 h3 => hSmax Q'' h3 h1 h2
  obtain ⟨P1, hP1⟩ := Lemma85Aux.exists_sylow_of_max hSR hS hmax
  obtain ⟨P2, hP2⟩ : ∃ P2 : Sylow 2 ↥R, Q'.subgroupOf R ≤ (P2 : Subgroup ↥R) :=
    (IsPGroup.of_equiv hQ'2 (Subgroup.subgroupOfEquivOfLe hQ'R).symm).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (↥R) P1 P2
  let T : Subgroup G := (P2 : Subgroup ↥R).map R.subtype
  have hcT : Nat.card T = Nat.card S := by
    have h1 : Nat.card T = Nat.card (P2 : Subgroup ↥R) :=
      Subgroup.card_map_of_injective R.subtype_injective
    have h2 : Nat.card (P1 : Subgroup ↥R) = Nat.card S := by
      rw [hP1]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSR).toEquiv
    rw [h1, P2.card_eq_multiplicity, ← P1.card_eq_multiplicity, h2]
  have hQ'T : Q' ≤ T := fun x hx =>
    ⟨⟨x, hQ'R hx⟩, hP2 (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hS'T : ∀ q ∈ S, h.1 * q * h.1⁻¹ ∈ T := by
    intro q hq
    have h1 : (⟨q, hSR hq⟩ : ↥R) ∈ (P1 : Subgroup ↥R) := by
      rw [hP1]; exact hq
    have h2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj h) (P1 : Subgroup ↥R) h1
    rw [← Sylow.coe_subgroup_smul, hh] at h2
    exact ⟨_, h2, by simp⟩
  have hcQ' : Nat.card Q' = Nat.card S := Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hQ'eq : Q' = T :=
    Subgroup.eq_of_le_of_card_ge hQ'T (by rw [hcQ', hcT])
  have hhR : h.1 ∈ (↑(W ⊔ S) : Set G) := by
    rw [sup_comm]; exact h.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left W S hSW] at hhR
  obtain ⟨w, hw, s', hs', hws⟩ := hhR
  have hwx : ∀ x ∈ S, w * x * w⁻¹ ∈ Q' := by
    intro x hx
    rw [hQ'eq]
    have := hS'T (s'⁻¹ * x * s') (S.mul_mem (S.mul_mem (S.inv_mem hs') hx) hs')
    rw [← hws] at this
    convert this using 1
    group
  have hwI : w ∈ I := hWI hw
  refine ⟨g * w, ⟨I.mul_mem hg hwI, ?_⟩, w⁻¹, W.inv_mem hw, by group⟩
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨s, hs, hse⟩ := hwx x hx
  have hse' : g⁻¹ * s * g⁻¹⁻¹ = w * x * w⁻¹ := hse
  have : g * w * x * (g * w)⁻¹ = s := by
    calc g * w * x * (g * w)⁻¹ = g * (w * x * w⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ := by rw [hse']
      _ = s := by group
  rw [this]; exact hs

theorem barX_closure_three_eq {N Y : Subgroup G} (_hYN : Y ≤ N)
    (hsimple : IsSimpleGroup ↥(barX 3 N Y)) (hdiv : 3 ∣ Nat.card (barX 3 N Y)) :
    barX 3 N (Subgroup.closure {g : G | g ∈ Y ∧ IsPGroup 3 (Subgroup.zpowers g)}) =
      barX 3 N Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z : Subgroup G := Subgroup.closure {g : G | g ∈ Y ∧ IsPGroup 3 (Subgroup.zpowers g)} with hZ
  have hZY : Z ≤ Y := (Subgroup.closure_le Y).2 fun g hg => hg.1
  have hMY : barX 3 N Z ≤ barX 3 N Y := barX_mono 3 hZY
  have key : ∀ c ∈ barX 3 N Y, ∀ m ∈ barX 3 N Z, c * m * c⁻¹ ∈ barX 3 N Z := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy hz
    refine ⟨y * z * y⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact conj_mem_closure_three (Subgroup.le_normalizer hy) hz
  have hnorm : ((barX 3 N Z).subgroupOf (barX 3 N Y)).Normal :=
    ⟨fun m hm c => Subgroup.mem_subgroupOf.2 (key _ c.2 _ hm)⟩
  have := hnorm
  rcases hsimple.eq_bot_or_eq_top_of_normal ((barX 3 N Z).subgroupOf (barX 3 N Y)) with hbot | htop
  · exfalso
    obtain ⟨yb, hyb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(barX 3 N Y)) 3 hdiv
    obtain ⟨y, hy, hyc⟩ := yb.2
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.1 hy
    set n := orderOf (y : G) with hn
    have hn0 : n ≠ 0 := (orderOf_pos _).ne'
    set m := n / 3 ^ n.factorization 3 with hm
    have hcop : Nat.Coprime 3 m := Nat.coprime_ordCompl Nat.prime_three hn0
    have hg3 : IsPGroup 3 (Subgroup.zpowers ((y : G) ^ m)) := by
      have h1 : 3 ^ n.factorization 3 * m = n := Nat.ordProj_mul_ordCompl_eq_self n 3
      have hpow : ((y : G) ^ m) ^ 3 ^ n.factorization 3 = 1 := by
        rw [← pow_mul, mul_comm, h1]
        exact pow_orderOf_eq_one _
      rintro ⟨x, k, rfl⟩
      refine ⟨n.factorization 3, Subtype.ext ?_⟩
      show (((y : G) ^ m) ^ k) ^ 3 ^ n.factorization 3 = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]
    have hmem : yb ^ m ∈ (barX 3 N Z).subgroupOf (barX 3 N Y) := by
      rw [Subgroup.mem_subgroupOf]
      show yb.1 ^ m ∈ barX 3 N Z
      rw [← hyc, ← map_pow]
      refine ⟨y ^ m, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact Subgroup.subset_closure ⟨pow_mem hyY m, hg3⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have := orderOf_dvd_of_pow_eq_one hmem
    rw [hyb] at this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop this
  · exact le_antisymm hMY (Subgroup.subgroupOf_eq_top.1 htop)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

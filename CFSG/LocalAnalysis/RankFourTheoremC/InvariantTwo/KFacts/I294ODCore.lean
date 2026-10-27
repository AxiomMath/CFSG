module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294Lemmas
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

structure ODFamily (p n : ℕ) {L : Type} [Group L] {G C : Type} [Group G] [CommGroup C]
    (Φ : G →* MulAut L) (det : G →* C) (Z : Subgroup G) : Prop where
  central : ∀ z ∈ Z, ∀ B : G, z * B = B * z
  ker_eq : ∀ B, Φ B = 1 ↔ B ∈ Z
  det_center : ∀ w : C, (∃ z ∈ Z, det z = w) ↔ ∃ c : C, w = c ^ n
  comm_mem : ∀ α β : MulAut L, α * β * α⁻¹ * β⁻¹ ∈ Φ.range
  inner_of_det : ∀ B, (∃ c : C, det B = c ^ n) →
    Φ B ∈ (MulAut.conj : L →* MulAut L).range
  exists_det_one : ∀ ℓ : L, ∃ B, det B = 1 ∧ Φ B = MulAut.conj ℓ
  lift : ∀ α : MulAut L, ∃ (κ : ℤ) (t : G →* G), (∀ B, α * Φ B * α⁻¹ = Φ (t B)) ∧
    (∀ B, det (t B) = det B ^ κ) ∧ ∀ z ∈ Z, t z = z ^ κ
  cyclic : IsCyclic C
  torus3 : ∀ B : G, B ^ p = 1 → ∃ f : (Fin 3 → Multiplicative (ZMod p)) →* L,
    Function.Injective f ∧ ∀ a, Φ B (f a) = f a
  monomial : p + 3 ≤ n → ∀ B : G, B ^ p ∈ Z → (∀ w ∈ Z, w ^ p ≠ B ^ p) →
    ∃ E : Subgroup L, IsElemAbelian p E ∧ p ^ (p + 1) ≤ Nat.card E ∧ ∀ e ∈ E, Φ B e ∈ E
  det_nonpower : n = p → ∀ B : G, B ^ p ∈ Z → (∀ w ∈ Z, w ^ p ≠ B ^ p) →
    ∀ c : C, det B ≠ c ^ n
  comm_ne : n = p → ∀ A B : G, B ^ p ∈ Z → (∀ w ∈ Z, w ^ p ≠ B ^ p) → A * B = B * A →
    A ^ p = 1 → A ∈ Z

section Basic

variable {p n : ℕ} {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]
  {G C : Type} [Group G] [CommGroup C] {Φ : G →* MulAut L} {det : G →* C} {Z : Subgroup G}

noncomputable abbrev odC (L : Subgroup X) [L.Normal] : X →* MulAut L := MulAut.conjNormal

theorem odC_injective (hcen : centralizer (L : Set X) = ⊥) : Function.Injective (odC L) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgc : g ∈ centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hg ⟨h, hh⟩)
    have h2 : g * h * g⁻¹ = h := by simpa [odC, MulAut.conjNormal_apply] using h1
    calc h * g = (g * h * g⁻¹) * g := by rw [h2]
      _ = g * h := by group
  rw [hcen, Subgroup.mem_bot] at hgc
  exact hgc

theorem odC_of_mem {ℓ : X} (hℓ : ℓ ∈ L) : odC L ℓ = MulAut.conj (⟨ℓ, hℓ⟩ : L) :=
  MulAut.conjNormal_val (h := ⟨ℓ, hℓ⟩)

theorem ODFamily.inv_mul_mem (hF : ODFamily p n Φ det Z) {B B' : G} (h : Φ B = Φ B') :
    B⁻¹ * B' ∈ Z := by
  rw [← hF.ker_eq, map_mul, map_inv, h, inv_mul_cancel]

theorem ODFamily.exists_scalar (hF : ODFamily p n Φ det Z) {B B' : G} (h : Φ B = Φ B') :
    ∃ w ∈ Z, B' = B * w := by
  refine ⟨B⁻¹ * B', hF.inv_mul_mem h, ?_⟩
  group

theorem od_exists_lift (hF : ODFamily p n Φ det Z) [Fact p.Prime] (hp5 : 5 ≤ p)
    {D : Subgroup X} (hD : IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2) {z g : X}
    (hz : z ∈ D) (hz1 : z ≠ 1) (hg : IsPlaneDiagonal p D z g) :
    ∀ u ∈ D, ∃ B : G, Φ B = odC L u := by
  intro u hu
  obtain ⟨d', -, hdd⟩ := exists_commutator_of_isPlaneDiagonal hp5 hD hDcard hz hz1 hg u hu
  have h1 := hF.comm_mem (odC L d')⁻¹ (odC L g)
  have h2 : (odC L d')⁻¹ * odC L g * ((odC L d')⁻¹)⁻¹ * (odC L g)⁻¹ = odC L u := by
    rw [hdd]
    simp only [map_mul, map_inv, inv_inv]
  rw [h2] at h1
  exact h1

theorem od_card_torus [Fact p.Prime] (k : ℕ) :
    Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem od_torus_pow [Fact p.Prime] {k : ℕ} (a : Fin k → Multiplicative (ZMod p)) : a ^ p = 1 := by
  funext i
  change (a i) ^ p = 1
  rw [← ofAdd_toAdd (a i), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem od_three_le_pRank_of_torus [Fact p.Prime] {x : X}
    (f : (Fin 3 → Multiplicative (ZMod p)) →* L) (hf : Function.Injective f)
    (hfix : ∀ a, odC L x (f a) = f a) : 3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set X)) := by
  have hp : p.Prime := Fact.out
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm a b)
    (fun a => od_torus_pow a) (od_card_torus 3) (L.subtype.comp f)
    (Subtype.val_injective.comp hf) ?_
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := congrArg Subtype.val (hfix a)
  simp only [odC, MulAut.conjNormal_apply] at h1
  change ((f a : L) : X) * x = x * ((f a : L) : X)
  calc ((f a : L) : X) * x = (x * (f a : X) * x⁻¹) * x := by rw [h1]
    _ = x * (f a : X) := by group

theorem od_mem_normalizer_of_conj_subset {x : X} {E : Subgroup X}
    (h : ∀ e ∈ E, x * e * x⁻¹ ∈ E) : x ∈ normalizer (E : Set X) := by
  have hle : E.map (MulAut.conj x).toMonoidHom ≤ E := by
    rintro _ ⟨e, he, rfl⟩
    exact h e he
  have hcard : Nat.card (E.map (MulAut.conj x).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have heq : E.map (MulAut.conj x).toMonoidHom = E :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [mem_normalizer_iff]
  intro e
  refine ⟨h e, fun he => ?_⟩
  rw [← heq] at he
  obtain ⟨e₁, he₁, he₁e⟩ := he
  have : e₁ = e := by
    have h2 : x * e₁ * x⁻¹ = x * e * x⁻¹ := he₁e
    simpa using h2
  rw [← this]
  exact he₁

theorem od_three_le_pRank_of_normalizes [Fact p.Prime] (hp5 : 5 ≤ p) {x : X} (hx : orderOf x = p)
    {E : Subgroup L} (hE : IsElemAbelian p E) (hcard : p ^ (p + 1) ≤ Nat.card E)
    (hnorm : ∀ e ∈ E, odC L x e ∈ E) : 3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set X)) := by
  have hp : p.Prime := Fact.out
  set E' : Subgroup X := E.map L.subtype with hE'
  have hE'el : IsElemAbelian p E' := IsElemAbelian.map hE _
  have hE'card : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective L.subtype_injective
  have hE'norm : ∀ e ∈ E', x * e * x⁻¹ ∈ E' := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨odC L x e, hnorm e he, ?_⟩
    simp [odC, MulAut.conjNormal_apply]
  have hxN : x ∈ normalizer (E' : Set X) := od_mem_normalizer_of_conj_subset hE'norm
  have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  have hE'p : IsPGroup p E' := fun e => ⟨1, Subtype.ext (by simpa using hE'el.2 e e.2)⟩
  have hzp : IsPGroup p (zpowers x) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hx]; exact (pow_one p).symm)
  have hzN : zpowers x ≤ normalizer (E' : Set X) := zpowers_le.2 hxN
  have hP : IsPGroup p ↥(E' ⊔ zpowers x) := hE'p.to_sup_of_normal_left' hzp hzN
  set P : Subgroup X := E' ⊔ zpowers x with hPdef
  have hEP : E' ≤ P := le_sup_left
  have hPN : P ≤ normalizer (E' : Set X) := sup_le le_normalizer hzN
  haveI : (E'.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hEP).2 hPN
  have hxP : x ∈ P := mem_sup_right (mem_zpowers x)
  have hxPord : orderOf (⟨x, hxP⟩ : P) = p := by rw [← hx]; exact Subgroup.orderOf_mk x hxP
  have hEPel : IsElemAbelian p (E'.subgroupOf P) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact hE'el.comm (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2)
    · apply Subtype.ext
      simpa using hE'el.2 _ (Subgroup.mem_subgroupOf.1 hy)
  have hEPcard : p ^ (p + 1) ≤ Nat.card (E'.subgroupOf P) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hE'card]
    exact hcard
  have h3 := three_le_pRank_centralizer_of_normal hp5 hP hxPord hEPel hEPcard
  have h4 := CFSG.SectionRank.pRank_le_map hp.one_lt P.subtype P.subtype_injective
    (centralizer ({(⟨x, hxP⟩ : P)} : Set P))
  have h5 : (centralizer ({(⟨x, hxP⟩ : P)} : Set P)).map P.subtype ≤ centralizer ({x} : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Subgroup.mem_centralizer_singleton_iff.1 hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hy')
  exact h3.trans (h4.trans (CFSG.SectionRank.pRank_mono hp.one_lt h5))

theorem od_pow_mem (hF : ODFamily p n Φ det Z) {x : X} (hx : x ^ p = 1) {B : G}
    (hB : Φ B = odC L x) : B ^ p ∈ Z := by
  rw [← hF.ker_eq, map_pow, hB, ← map_pow, hx, map_one]

theorem od_not_pow [Fact p.Prime] (hF : ODFamily p n Φ det Z) {x : X}
    (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) {B : G} (hB : Φ B = odC L x) :
    ∀ w ∈ Z, w ^ p ≠ B ^ p := by
  intro w hw hwp
  have hwB : w⁻¹ * B = B * w⁻¹ := hF.central w⁻¹ (Z.inv_mem hw) B
  have hB'p : (w⁻¹ * B) ^ p = 1 := by
    rw [(show Commute w⁻¹ B from hwB).mul_pow, inv_pow, hwp, inv_mul_cancel]
  have hΦ : Φ (w⁻¹ * B) = odC L x := by
    rw [map_mul, (hF.ker_eq _).2 (Z.inv_mem hw), one_mul, hB]
  obtain ⟨f, hf, hfix⟩ := hF.torus3 _ hB'p
  rw [hΦ] at hfix
  have := od_three_le_pRank_of_torus f hf hfix
  omega

theorem od_inner_iff (hF : ODFamily p n Φ det Z) (B : G) :
    Φ B ∈ (MulAut.conj : L →* MulAut L).range ↔ ∃ c : C, det B = c ^ n := by
  refine ⟨fun ⟨ℓ, hℓ⟩ => ?_, hF.inner_of_det B⟩
  obtain ⟨B₀, hdet, hΦ⟩ := hF.exists_det_one ℓ
  have hz : B₀⁻¹ * B ∈ Z := hF.inv_mul_mem (by rw [hΦ, hℓ])
  have h1 : det B = det (B₀⁻¹ * B) := by rw [map_mul, map_inv, hdet, inv_one, one_mul]
  rw [h1]
  exact (hF.det_center _).1 ⟨_, hz, rfl⟩

theorem od_inner_iff_mem (hcen : centralizer (L : Set X) = ⊥) (u : X) :
    odC L u ∈ (MulAut.conj : L →* MulAut L).range ↔ u ∈ L := by
  constructor
  · rintro ⟨ℓ, hℓ⟩
    have h : odC L u = odC L (ℓ : X) := by rw [← hℓ, odC_of_mem ℓ.2]
    rw [odC_injective hcen h]
    exact ℓ.2
  · intro hu
    exact ⟨⟨u, hu⟩, (odC_of_mem hu).symm⟩

theorem od_class_eq (hF : ODFamily p n Φ det Z) {B B' : G} (h : Φ B = Φ B') :
    (QuotientGroup.mk (det B) : C ⧸ (powMonoidHom n : C →* C).range) =
      QuotientGroup.mk (det B') := by
  obtain ⟨w, hw, rfl⟩ := hF.exists_scalar h
  rw [map_mul, QuotientGroup.mk_mul]
  have : (QuotientGroup.mk (det w) : C ⧸ (powMonoidHom n : C →* C).range) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    obtain ⟨c, hc⟩ := (hF.det_center _).1 ⟨w, hw, rfl⟩
    exact ⟨c, by rw [hc]; rfl⟩
  rw [this, mul_one]

theorem od_exists_class_hom (hF : ODFamily p n Φ det Z) {D : Subgroup X}
    (hlift : ∀ u ∈ D, ∃ B : G, Φ B = odC L u) :
    ∃ ψ : D →* C ⧸ (powMonoidHom n : C →* C).range, ∀ (u : D) (B : G), Φ B = odC L u →
      ψ u = QuotientGroup.mk (det B) := by
  choose Bl hBl using hlift
  let f : D → G := fun u => Bl u.1 u.2
  have hf : ∀ u : D, Φ (f u) = odC L u := fun u => hBl u.1 u.2
  refine ⟨{ toFun := fun u => QuotientGroup.mk (det (f u)), map_one' := ?_, map_mul' := ?_ },
    fun u B hB => od_class_eq hF (by rw [hf, hB])⟩
  · have h1 : Φ (f 1) = Φ 1 := by rw [hf, map_one]; simp
    have := od_class_eq hF h1
    simpa using this
  · intro u v
    have h1 : Φ (f (u * v)) = Φ (f u * f v) := by
      rw [map_mul, hf, hf, hf]
      simp
    have := od_class_eq hF h1
    simpa [map_mul, QuotientGroup.mk_mul] using this

theorem od_exists_inner [Fact p.Prime] (hF : ODFamily p n Φ det Z)
    (hcen : centralizer (L : Set X) = ⊥) {D : Subgroup X} (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) (hlift : ∀ u ∈ D, ∃ B : G, Φ B = odC L u) :
    ∃ u ∈ D, u ≠ 1 ∧ u ∈ L := by
  have hp : p.Prime := Fact.out
  obtain ⟨ψ, hψ⟩ := od_exists_class_hom hF hlift
  by_contra hno
  push Not at hno
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    by_contra hu1
    obtain ⟨B, hB⟩ := hlift u.1 u.2
    have h1 := hψ u B hB
    rw [hu, eq_comm, QuotientGroup.eq_one_iff] at h1
    obtain ⟨c, hc⟩ := h1
    have hinn : Φ B ∈ (MulAut.conj : L →* MulAut L).range := hF.inner_of_det B ⟨c, hc.symm⟩
    rw [hB, od_inner_iff_mem hcen] at hinn
    exact hno u.1 u.2 (fun h => hu1 (Subtype.ext h)) hinn
  haveI := hF.cyclic
  haveI : IsCyclic (C ⧸ (powMonoidHom n : C →* C).range) :=
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  haveI : IsCyclic ψ.range := inferInstance
  haveI : IsCyclic D :=
    isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm
      (MonoidHom.ofInjective hinj).symm.surjective
  obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := D)
  have h1 : orderOf gen = p ^ 2 := (orderOf_eq_card_of_forall_mem_zpowers hgen).trans hDcard
  have h2 : gen ^ p = 1 := Subtype.ext (hD.2 gen gen.2)
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [h1] at h3
  have h4 := Nat.le_of_dvd hp.pos h3
  nlinarith [hp.two_le]

end Basic

section Commutators

variable {G : Type*} [Group G]

theorem od_conj_pow_mul {a b β : G} (h : a * b * a⁻¹ = β * b) (hc : ∀ g : G, β * g = g * β)
    (i : ℕ) : a ^ i * b * (a ^ i)⁻¹ = β ^ i * b := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e1 : a ^ (i + 1) * b * (a ^ (i + 1))⁻¹ = a ^ i * (a * b * a⁻¹) * (a ^ i)⁻¹ := by
      rw [pow_succ, mul_inv_rev]; group
    have e2 : a ^ i * (β * b) * (a ^ i)⁻¹ = β * (a ^ i * b * (a ^ i)⁻¹) := by
      calc a ^ i * (β * b) * (a ^ i)⁻¹ = (a ^ i * β) * b * (a ^ i)⁻¹ := by group
        _ = (β * a ^ i) * b * (a ^ i)⁻¹ := by rw [hc (a ^ i)]
        _ = β * (a ^ i * b * (a ^ i)⁻¹) := by group
    rw [e1, h, e2, ih, pow_succ', mul_assoc]

theorem od_comm_pow_pow {a b β : G} (h : a * b * a⁻¹ * b⁻¹ = β) (hc : ∀ g : G, β * g = g * β)
    (i j : ℕ) : a ^ i * b ^ j * (a ^ i)⁻¹ * (b ^ j)⁻¹ = β ^ (i * j) := by
  have h1 : a * b * a⁻¹ = β * b := by rw [← h]; group
  have h2 := od_conj_pow_mul h1 hc i
  have h3 : a ^ i * b ^ j * (a ^ i)⁻¹ = (β ^ i) ^ j * b ^ j := by
    rw [← conj_pow, h2]
    exact (show Commute (β ^ i) b from (Commute.pow_left (hc b) i)).mul_pow j
  calc a ^ i * b ^ j * (a ^ i)⁻¹ * (b ^ j)⁻¹ = (β ^ i) ^ j * b ^ j * (b ^ j)⁻¹ := by rw [h3]
    _ = β ^ (i * j) := by rw [mul_inv_cancel_right, ← pow_mul]

theorem od_comm_mul_central_left {a y z : G} (h : ∀ g : G, z * g = g * z) :
    (a * z) * y * (a * z)⁻¹ * y⁻¹ = a * y * a⁻¹ * y⁻¹ := by
  have hzy : z * y * z⁻¹ = y := by rw [h y]; group
  calc (a * z) * y * (a * z)⁻¹ * y⁻¹ = a * (z * y * z⁻¹) * a⁻¹ * y⁻¹ := by group
    _ = a * y * a⁻¹ * y⁻¹ := by rw [hzy]

theorem od_comm_mul_central_right {x b w : G} (h : ∀ g : G, w * g = g * w) :
    x * (b * w) * x⁻¹ * (b * w)⁻¹ = x * b * x⁻¹ * b⁻¹ := by
  have hwx : w * x⁻¹ * w⁻¹ = x⁻¹ := by rw [h x⁻¹]; group
  calc x * (b * w) * x⁻¹ * (b * w)⁻¹ = x * b * (w * x⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = x * b * x⁻¹ * b⁻¹ := by rw [hwx]

theorem od_comm_scalar {a b z₁ z₀ : G} (h₁ : ∀ g : G, z₁ * g = g * z₁)
    (h₀ : ∀ g : G, z₀ * g = g * z₀) :
    (a * z₁) * (b * z₀) * (a * z₁)⁻¹ * (b * z₀)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  rw [od_comm_mul_central_right h₀, od_comm_mul_central_left h₁]

end Commutators


section Endgame

variable {p n : ℕ} {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]
  {G C : Type} [Group G] [CommGroup C] {Φ : G →* MulAut L} {det : G →* C} {Z : Subgroup G}

theorem od_endgame [Fact p.Prime] (hF : ODFamily p n Φ det Z) (hn : n = p)
    (hcen : centralizer (L : Set X) = ⊥) {u₀ u₁ x g : X} {a b i j : ℕ}
    (hu₀L : u₀ ∈ L) (hu₀1 : u₀ ≠ 1) (hu₀p : u₀ ^ p = 1) (hu₁L : u₁ ∉ L) (hu₁p : u₁ ^ p = 1)
    (hcomm : u₀ * u₁ = u₁ * u₀) (hxp : x ^ p = 1) (hx : x = u₀ ^ i * u₁ ^ j)
    (hg₀ : g * u₀ * g⁻¹ = u₀ ^ a) (hg₁ : g * u₁ * g⁻¹ = u₁ ^ b)
    (hab : a * b % p = 1) (hb1 : b % p ≠ 1) {B₁ Bx : G} (hB₁ : Φ B₁ = odC L u₁)
    (hBx : Φ Bx = odC L x) (hBxp : ∀ w ∈ Z, w ^ p ≠ Bx ^ p) : False := by
  have hp : p.Prime := Fact.out
  obtain ⟨ℓ₀, hℓ₀det, hℓ₀Φ⟩ := hF.exists_det_one ⟨u₀, hu₀L⟩
  have hℓ₀Φ' : Φ ℓ₀ = odC L u₀ := by rw [hℓ₀Φ, odC_of_mem hu₀L]
  have hB₁Z : B₁ ^ p ∈ Z := od_pow_mem hF hu₁p hB₁
  have hℓ₀Z : ℓ₀ ^ p ∈ Z := od_pow_mem hF hu₀p hℓ₀Φ'
  have hBxZ : Bx ^ p ∈ Z := od_pow_mem hF hxp hBx
  have hdetB₁ : ¬ ∃ c : C, det B₁ = c ^ n := by
    intro hc
    have h1 := hF.inner_of_det B₁ hc
    rw [hB₁, od_inner_iff_mem hcen] at h1
    exact hu₁L h1
  set β : G := B₁ * ℓ₀ * B₁⁻¹ * ℓ₀⁻¹ with hβdef
  have hβZ : β ∈ Z := by
    rw [← hF.ker_eq]
    have h1 : Φ β = odC L (u₁ * u₀ * u₁⁻¹ * u₀⁻¹) := by
      simp only [hβdef, map_mul, map_inv, hB₁, hℓ₀Φ']
    have h2 : u₁ * u₀ * u₁⁻¹ * u₀⁻¹ = 1 := by rw [← hcomm]; group
    rw [h1, h2, map_one]
  have hβc : ∀ g' : G, β * g' = g' * β := hF.central β hβZ
  obtain ⟨κ, t, ht1, ht2, ht3⟩ := hF.lift (odC L g)
  have hΦt₁ : Φ (B₁ ^ b) = Φ (t B₁) := by
    have e : Φ (t B₁) = odC L (u₁ ^ b) := by
      rw [← ht1, hB₁, ← hg₁]
      simp only [map_mul, map_inv]
    rw [e, map_pow, hB₁, map_pow]
  have hΦt₀ : Φ (ℓ₀ ^ a) = Φ (t ℓ₀) := by
    have e : Φ (t ℓ₀) = odC L (u₀ ^ a) := by
      rw [← ht1, hℓ₀Φ', ← hg₀]
      simp only [map_mul, map_inv]
    rw [e, map_pow, hℓ₀Φ', map_pow]
  obtain ⟨z₁, hz₁, htB₁⟩ := hF.exists_scalar hΦt₁
  obtain ⟨z₀, hz₀, htℓ₀⟩ := hF.exists_scalar hΦt₀
  have htβ : t β = β ^ (b * a) := by
    have h1 : t β = t B₁ * t ℓ₀ * (t B₁)⁻¹ * (t ℓ₀)⁻¹ := by
      simp only [hβdef, map_mul, map_inv]
    rw [h1, htB₁, htℓ₀, od_comm_scalar (hF.central z₁ hz₁) (hF.central z₀ hz₀)]
    exact od_comm_pow_pow hβdef.symm hβc b a
  have hκ : β ^ κ = β ^ (b * a) := by rw [← ht3 β hβZ, htβ]
  have hdz : ∃ c : C, det z₁ = c ^ n := (hF.det_center (det z₁)).1 ⟨z₁, hz₁, rfl⟩
  have hdk : ∃ c : C, det B₁ ^ (κ - (b : ℤ)) = c ^ n := by
    obtain ⟨c, hc⟩ := hdz
    refine ⟨c, ?_⟩
    have h1 : det B₁ ^ κ = det B₁ ^ b * det z₁ := by
      rw [← ht2 B₁, htB₁, map_mul, map_pow]
    rw [zpow_sub, zpow_natCast, h1, hc, mul_comm (det B₁ ^ b) (c ^ n), mul_inv_cancel_right]
  have hdp : ∃ c : C, det B₁ ^ p = c ^ n := by
    obtain ⟨c, hc⟩ := (hF.det_center (det (B₁ ^ p))).1 ⟨_, hB₁Z, rfl⟩
    exact ⟨c, by rw [← map_pow]; exact hc⟩
  have hpκ : (p : ℤ) ∣ κ - (b : ℤ) := l212in_dvd_of_pow_mem hp hdetB₁ hdp hdk
  by_cases hβ1 : β = 1
  ·
    have hc₁ : B₁ * ℓ₀ = ℓ₀ * B₁ := by
      have h1 : B₁ * ℓ₀ * B₁⁻¹ * ℓ₀⁻¹ = 1 := by rw [← hβdef]; exact hβ1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hΦx : Φ (ℓ₀ ^ i * B₁ ^ j) = Φ Bx := by
      rw [map_mul, map_pow, map_pow, hℓ₀Φ', hB₁, hBx, hx, map_mul, map_pow, map_pow]
    obtain ⟨w, hw, hBxeq⟩ := hF.exists_scalar hΦx
    have hcℓ : ℓ₀ * Bx = Bx * ℓ₀ := by
      rw [hBxeq]
      have c1 : Commute ℓ₀ (ℓ₀ ^ i) := (Commute.refl ℓ₀).pow_right i
      have c2 : Commute ℓ₀ (B₁ ^ j) := (show Commute ℓ₀ B₁ from hc₁.symm).pow_right j
      have c3 : Commute ℓ₀ w := (hF.central w hw ℓ₀).symm
      exact (c1.mul_right c2).mul_right c3
    have hw₀ : ∃ w₀ ∈ Z, w₀ ^ p = ℓ₀ ^ p := by
      by_contra hno
      push Not at hno
      exact hF.det_nonpower hn ℓ₀ hℓ₀Z (fun w hw h => hno w hw h) 1
        (by rw [hℓ₀det, one_pow])
    obtain ⟨w₀, hw₀Z, hw₀p⟩ := hw₀
    have hA : (w₀⁻¹ * ℓ₀) ^ p = 1 := by
      rw [(show Commute w₀⁻¹ ℓ₀ from hF.central w₀⁻¹ (Z.inv_mem hw₀Z) ℓ₀).mul_pow, inv_pow,
        hw₀p, inv_mul_cancel]
    have hAB : (w₀⁻¹ * ℓ₀) * Bx = Bx * (w₀⁻¹ * ℓ₀) := by
      rw [mul_assoc, hcℓ, ← mul_assoc, hF.central w₀⁻¹ (Z.inv_mem hw₀Z) Bx, mul_assoc]
    have hAZ := hF.comm_ne hn _ Bx hBxZ hBxp hAB hA
    have hℓZ : ℓ₀ ∈ Z := by
      have := Z.mul_mem hw₀Z hAZ
      simpa using this
    have h1 : odC L u₀ = 1 := by rw [← hℓ₀Φ']; exact (hF.ker_eq _).2 hℓZ
    exact hu₀1 (odC_injective hcen (by rw [h1, map_one]))
  ·
    have hβp : β ^ p = 1 := by
      have h1 := od_comm_pow_pow hβdef.symm hβc p 1
      have h2 : B₁ ^ p * ℓ₀ ^ 1 * (B₁ ^ p)⁻¹ * (ℓ₀ ^ 1)⁻¹ = 1 := by
        rw [pow_one, hF.central (B₁ ^ p) hB₁Z ℓ₀]; group
      rw [h2, mul_one] at h1
      exact h1.symm
    have horder : orderOf β = p := orderOf_eq_prime hβp hβ1
    have hκ' : β ^ (κ - ((b * a : ℕ) : ℤ)) = 1 := by
      rw [zpow_sub, hκ, zpow_natCast, mul_inv_cancel]
    have hdvd : (p : ℤ) ∣ κ - ((b * a : ℕ) : ℤ) := by
      have := orderOf_dvd_iff_zpow_eq_one.2 hκ'
      rwa [horder] at this
    have h1 : (κ : ZMod p) = (b : ZMod p) := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hpκ
      push_cast at this
      exact sub_eq_zero.1 this
    have h2 : (κ : ZMod p) = (b : ZMod p) * (a : ZMod p) := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
      push_cast at this
      exact sub_eq_zero.1 this
    have h3 : (a : ZMod p) * (b : ZMod p) = 1 := by
      have := congrArg (Nat.cast : ℕ → ZMod p) hab
      rwa [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one] at this
    have h4 : (b : ZMod p) = 1 := by
      calc (b : ZMod p) = κ := h1.symm
        _ = (b : ZMod p) * (a : ZMod p) := h2
        _ = (a : ZMod p) * (b : ZMod p) := mul_comm _ _
        _ = 1 := h3
    have h5 : b % p = 1 % p :=
      (ZMod.natCast_eq_natCast_iff' b 1 p).1 (by rw [h4, Nat.cast_one])
    exact hb1 (by rw [h5]; exact Nat.mod_eq_of_lt hp.one_lt)

end Endgame

section Plane

variable {p : ℕ} {X : Type} [Group X] [Finite X]

theorem od_pow_eq_pow_of_natCast [Fact p.Prime] {u : X} (hu : u ^ p = 1) {m k : ℕ}
    (h : (m : ZMod p) = k) : u ^ m = u ^ k := by
  have hmod : ∀ r : ℕ, u ^ r = u ^ (r % p) := by
    intro r
    conv_lhs => rw [← Nat.mod_add_div r p, pow_add, pow_mul, hu, one_pow, mul_one]
  rw [hmod m, hmod k, (ZMod.natCast_eq_natCast_iff' m k p).1 h]

theorem od_zpowers_eq [Fact p.Prime] {y z : X} (hz : z ^ p = 1) (hz1 : z ≠ 1) (hy : y ^ p = 1)
    (hy1 : y ≠ 1) (h : y ∈ Subgroup.zpowers z) : Subgroup.zpowers y = Subgroup.zpowers z := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 h) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hz hz1, orderOf_eq_prime hy hy1]

theorem od_exists_eigen [Fact p.Prime] {D : Subgroup X} (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) {z g : X} (hz : z ∈ D) (hz1 : z ≠ 1) {a b : ℕ}
    (hab : (a : ZMod p) ≠ b) (hga : g * z * g⁻¹ = z ^ a)
    (hgd : ∀ d ∈ D, d ∉ Subgroup.zpowers z → ∃ c : ℕ, g * d * g⁻¹ = d ^ b * z ^ c) :
    ∃ δ ∈ D, δ ∉ Subgroup.zpowers z ∧ g * δ * g⁻¹ = δ ^ b := by
  have hp : p.Prime := Fact.out
  have hzp : z ^ p = 1 := hD.2 z hz
  obtain ⟨d, hd, hdz⟩ : ∃ d ∈ D, d ∉ Subgroup.zpowers z := by
    by_contra hno
    push Not at hno
    have hcard := Subgroup.card_le_of_le (fun x hx => hno x hx : D ≤ Subgroup.zpowers z)
    rw [hDcard, Nat.card_zpowers, orderOf_eq_prime hzp hz1] at hcard
    nlinarith [hp.two_le]
  obtain ⟨c, hc⟩ := hgd d hd hdz
  have hba : (b : ZMod p) - a ≠ 0 := fun h => hab (sub_eq_zero.1 h).symm
  obtain ⟨s, hsc⟩ : ∃ s : ℕ, (s : ZMod p) * ((b : ZMod p) - a) = c :=
    ⟨((c : ZMod p) * ((b : ZMod p) - a)⁻¹).val, by
      rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hba, mul_one]⟩
  have hcomm : ∀ u ∈ D, ∀ v ∈ D, u * v = v * u := fun u hu v hv => hD.comm hu hv
  have hzs : z ^ s ∈ D := D.pow_mem hz s
  refine ⟨d * z ^ s, D.mul_mem hd hzs, ?_, ?_⟩
  · intro h
    apply hdz
    have h1 : d = (d * z ^ s) * (z ^ s)⁻¹ := by group
    rw [h1]
    exact mul_mem h (inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) s))
  · have hcs : Commute d (z ^ s) := hcomm d hd _ hzs
    have e1 : g * (d * z ^ s) * g⁻¹ = (g * d * g⁻¹) * (g * z * g⁻¹) ^ s := by
      rw [conj_pow]; group
    rw [e1, hc, hga, hcs.mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
    congr 1
    refine od_pow_eq_pow_of_natCast hzp ?_
    have key : (c : ZMod p) = (s : ZMod p) * b - (s : ZMod p) * a := by
      rw [← hsc]; ring
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, key]
    ring

end Plane

section Main

variable {p n : ℕ} {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]
  {G C : Type} [Group G] [CommGroup C] {Φ : G →* MulAut L} {det : G →* C} {Z : Subgroup G}

theorem od_core [Fact p.Prime] (hF : ODFamily p n Φ det Z) (hp5 : 5 ≤ p) (hpn : p ∣ n)
    (hn0 : 0 < n) (hcen : centralizer (L : Set X) = ⊥) {D : Subgroup X} (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) {z g : X} (hz : z ∈ D) (hz1 : z ≠ 1)
    (hg : IsPlaneDiagonal p D z g) {x : X} (hxD : x ∈ D) (hx1 : x ≠ 1)
    (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) : False := by
  have hp : p.Prime := Fact.out
  have hlift := od_exists_lift hF hp5 hD hDcard hz hz1 hg
  obtain ⟨Bx, hBx⟩ := hlift x hxD
  have hxp : x ^ p = 1 := hD.2 x hxD
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hBxZ : Bx ^ p ∈ Z := od_pow_mem hF hxp hBx
  have hBxp : ∀ w ∈ Z, w ^ p ≠ Bx ^ p := od_not_pow hF hx2 hBx
  have hnp : n = p := by
    by_contra hne
    obtain ⟨k, hk⟩ := hpn
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · simp at hk; omega
      · simp at hk; exact absurd hk hne
      · omega
    have hn3 : p + 3 ≤ n := by nlinarith
    obtain ⟨E, hE, hEc, hEn⟩ := hF.monomial hn3 Bx hBxZ hBxp
    have h3 := od_three_le_pRank_of_normalizes hp5 hxo hE hEc (fun e he => hBx ▸ hEn e he)
    omega
  have hxL : x ∉ L := by
    intro hxL
    have h1 : Φ Bx ∈ (MulAut.conj : L →* MulAut L).range := by
      rw [hBx]; exact (od_inner_iff_mem hcen x).2 hxL
    obtain ⟨c, hc⟩ := (od_inner_iff hF Bx).1 h1
    exact hF.det_nonpower hnp Bx hBxZ hBxp c hc
  obtain ⟨u, huD, hu1, huL⟩ := od_exists_inner hF hcen hD hDcard hlift
  have hgN : g ∈ normalizer (D : Set X) := hg.1
  obtain ⟨-, -, a, b, hab, hord, hga, hgd⟩ := hg
  have hcomm : ∀ u ∈ D, ∀ v ∈ D, u * v = v * u := fun u hu v hv => hD.comm hu hv
  have hab' : (a : ZMod p) * (b : ZMod p) = 1 := by
    have := congrArg (Nat.cast : ℕ → ZMod p) hab
    rwa [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one] at this
  have ha1 : (a : ZMod p) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hb1 : (b : ZMod p) ≠ 1 := by
    intro h
    apply ha1
    rw [h, mul_one] at hab'
    exact hab'
  have hne : (a : ZMod p) ≠ b := by
    intro h
    have h2 : (a : ZMod p) ^ 2 = 1 := by rw [sq]; nth_rw 2 [h]; exact hab'
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at h3
    have h4 := Nat.le_of_dvd (by norm_num) h3
    omega
  have ha1' : a % p ≠ 1 := fun h => ha1 (by rw [← ZMod.natCast_mod, h, Nat.cast_one])
  have hb1' : b % p ≠ 1 := fun h => hb1 (by rw [← ZMod.natCast_mod, h, Nat.cast_one])
  by_cases huz : u ∈ Subgroup.zpowers z
  ·
    have hzu : Subgroup.zpowers u = Subgroup.zpowers z :=
      od_zpowers_eq (hD.2 z hz) hz1 (hD.2 u huD) hu1 huz
    have hzL : z ∈ L := by
      have : z ∈ Subgroup.zpowers u := hzu ▸ Subgroup.mem_zpowers z
      exact (Subgroup.zpowers_le.2 huL) this
    obtain ⟨δ, hδD, hδz, hgδ⟩ := od_exists_eigen hD hDcard hz hz1 hne hga hgd
    obtain ⟨s', t', hxst⟩ := exists_pow_mul_pow_of_mem_plane hD hDcard hz hz1 hδD hδz hxD
    have hδL : δ ∉ L := by
      intro h
      apply hxL
      rw [hxst]
      exact mul_mem (pow_mem h s') (pow_mem hzL t')
    obtain ⟨B₁, hB₁⟩ := hlift δ hδD
    exact od_endgame hF hnp hcen (u₀ := z) (u₁ := δ) (x := x) (g := g) (a := a) (b := b)
      (i := t') (j := s') hzL hz1 (hD.2 z hz) hδL (hD.2 δ hδD) (hcomm z hz δ hδD) hxp
      (by rw [hxst]; exact ((show Commute δ z from hcomm δ hδD z hz).pow_pow s' t').eq)
      hga hgδ hab hb1' hB₁ hBx hBxp
  ·
    have hvD : g * u * g⁻¹ ∈ D := (mem_normalizer_iff.1 hgN u).1 huD
    have hvL : g * u * g⁻¹ ∈ L := Subgroup.Normal.conj_mem inferInstance u huL g
    have hvu : g * u * g⁻¹ ∈ Subgroup.zpowers u := by
      by_contra hvu
      apply hxL
      obtain ⟨s', t', hxst⟩ := exists_pow_mul_pow_of_mem_plane hD hDcard huD hu1 hvD hvu hxD
      rw [hxst]
      exact mul_mem (pow_mem hvL s') (pow_mem huL t')
    obtain ⟨c, hc⟩ := hgd u huD huz
    have hzc : z ^ c = 1 := by
      by_contra hzc1
      have hzcmem : z ^ c ∈ Subgroup.zpowers u := by
        have h1 : z ^ c = (u ^ b)⁻¹ * (g * u * g⁻¹) := by rw [hc]; group
        rw [h1]
        exact mul_mem (inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) b)) hvu
      have hzcp : (z ^ c) ^ p = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hD.2 z hz, one_pow]
      have h1 := od_zpowers_eq (hD.2 u huD) hu1 hzcp hzc1 hzcmem
      have h2 : Subgroup.zpowers (z ^ c) = Subgroup.zpowers z :=
        od_zpowers_eq (hD.2 z hz) hz1 hzcp hzc1 (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) c)
      apply huz
      rw [← h2, h1]
      exact Subgroup.mem_zpowers u
    have hgu : g * u * g⁻¹ = u ^ b := by rw [hc, hzc, mul_one]
    obtain ⟨s', t', hxst⟩ := exists_pow_mul_pow_of_mem_plane hD hDcard hz hz1 huD huz hxD
    have hzL : z ∉ L := by
      intro h
      apply hxL
      rw [hxst]
      exact mul_mem (pow_mem huL s') (pow_mem h t')
    obtain ⟨B₁, hB₁⟩ := hlift z hz
    exact od_endgame hF hnp hcen (u₀ := u) (u₁ := z) (x := x) (g := g) (a := b) (b := a)
      (i := s') (j := t') huL hu1 (hD.2 u huD) hzL (hD.2 z hz) (hcomm u huD z hz) hxp hxst
      hgu hga (by rw [mul_comm]; exact hab) ha1' hB₁ hBx hBxp

end Main

end CFSG.LocalAnalysis.RankFourTheoremC

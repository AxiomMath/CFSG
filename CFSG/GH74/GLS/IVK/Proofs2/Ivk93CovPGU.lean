module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovSurj
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93UBlock

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.Sp4Rec
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
  CFSG.ComponentClassification.OddClassSelector
open scoped MatrixGroups

section Arith

theorem ivk93cov_toNat_two (q : ℕ) (hq : 1 ≤ q) :
    (((q : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have : (((q : ℕ) : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1]
    ring
  rw [this, Int.toNat_natCast]

theorem ivk93cov_toNat_three (q : ℕ) : (((q : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
  have : (((q : ℕ) : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [this, Int.toNat_natCast]

theorem ivk93cov_toNat_four (q : ℕ) (hq : 1 ≤ q) :
    (((q : ℕ) : ℤ) ^ 4 - (-1) ^ 4).toNat = q ^ 4 - 1 := by
  have h1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have : (((q : ℕ) : ℤ) ^ 4 - (-1) ^ 4) = ((q ^ 4 - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1]
    ring
  rw [this, Int.toNat_natCast]

theorem ivk93cov_psu3_ne {q k : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1) (hk8 : 8 ≤ k) (hk11 : k ≤ 11) :
    2 * (q ^ (3 * (3 - 1) / 2) * (∏ i ∈ Finset.Icc 2 3, (((q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
      Nat.gcd 3 (q + 1)) ≠ k.factorial := by
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  have hexp : 3 * (3 - 1) / 2 = 3 := by norm_num
  rw [hI, Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3), ivk93cov_toNat_two q (by omega),
    ivk93cov_toNat_three q, hexp]
  have hk : k.factorial ≤ 39916800 := by
    have : k.factorial ≤ (11 : ℕ).factorial := Nat.factorial_le hk11
    simpa [Nat.factorial] using this
  by_cases hbig : 11 ≤ q
  · intro h
    have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hgpos : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / 3 ≤
        q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) :=
      Nat.div_le_div_left hg hgpos
    have hq3 : 1331 ≤ q ^ 3 := by
      calc 1331 = 11 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hbig 3
    have hq2 : 121 ≤ q ^ 2 := by
      calc 121 = 11 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hbig 2
    have hP : 1331 * (120 * 1332) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
      Nat.mul_le_mul hq3 (Nat.mul_le_mul (by omega) (by omega))
    have h2 : 1331 * (120 * 1332) / 3 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / 3 :=
      Nat.div_le_div_right hP
    norm_num at h2
    omega
  · have hq' : q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 9 := by omega
    rcases hq' with rfl | rfl | rfl | rfl <;>
    · interval_cases k <;> norm_num [Nat.factorial]

theorem ivk93cov_psu4_ne {q k : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1) (hk8 : 8 ≤ k) (hk11 : k ≤ 11) :
    2 * (q ^ (4 * (4 - 1) / 2) * (∏ i ∈ Finset.Icc 2 4, (((q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
      Nat.gcd 4 (q + 1)) ≠ k.factorial := by
  have hI : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [hI, Finset.prod_insert (by simp), Finset.prod_pair (by norm_num : (3 : ℕ) ≠ 4),
    ivk93cov_toNat_two q (by omega), ivk93cov_toNat_three q, ivk93cov_toNat_four q (by omega)]
  have hexp : 4 * (4 - 1) / 2 = 6 := by norm_num
  rw [hexp]
  have hk : k.factorial ≤ 39916800 := by
    have : k.factorial ≤ (11 : ℕ).factorial := Nat.factorial_le hk11
    simpa [Nat.factorial] using this
  by_cases hbig : 5 ≤ q
  · intro h
    have hg : Nat.gcd 4 (q + 1) ≤ 4 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hgpos : 0 < Nat.gcd 4 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) / 4 ≤
        q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) / Nat.gcd 4 (q + 1) :=
      Nat.div_le_div_left hg hgpos
    have hq6 : 15625 ≤ q ^ 6 := by
      calc 15625 = 5 ^ 6 := by norm_num
        _ ≤ q ^ 6 := Nat.pow_le_pow_left hbig 6
    have hq2 : 25 ≤ q ^ 2 := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hbig 2
    have hq3 : 125 ≤ q ^ 3 := by
      calc 125 = 5 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hbig 3
    have hq4 : 625 ≤ q ^ 4 := by
      calc 625 = 5 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hbig 4
    have hP : 15625 * (24 * (126 * 624)) ≤
        q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) :=
      Nat.mul_le_mul hq6 (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega)))
    have h2 : 15625 * (24 * (126 * 624)) / 4 ≤
        q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) / 4 :=
      Nat.div_le_div_right hP
    norm_num at h2
    omega
  · have hq' : q = 3 := by omega
    subst hq'
    interval_cases k <;> norm_num [Nat.factorial]

theorem ivk93cov_psu_ne {p f d k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (p ^ f) ^ 2) (hd : d = 3 ∨ d = 4) (hk8 : 8 ≤ k)
    (hk11 : k ≤ 11) :
    2 * Nat.card (StatedProj (StatedSU d (p ^ f) K)) ≠ k.factorial := by
  have hq3 : 3 ≤ p ^ f := by
    have h1 := hp.two_le
    have h2 : 3 ≤ p := by omega
    exact h2.trans (Nat.le_self_pow (by omega) p)
  have hqodd : (p ^ f) % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hf hK (by omega)]
  rcases hd with rfl | rfl
  · exact ivk93cov_psu3_ne hq3 hqodd hk8 hk11
  · exact ivk93cov_psu4_ne hq3 hqodd hk8 hk11

end Arith

namespace Ivk93Cov

variable {J : Type} [Group J] [Finite J] {x : J} {n : ℕ} {B : Subgroup J}

theorem two_mul_card_quot_center (h : Ivk93Cov x n B) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) (ψ : Q →* ↥B) (hψ : Function.Surjective ψ) :
    2 * Nat.card (Q ⧸ center Q) = n.factorial := by
  obtain ⟨N, -, h1, h2⟩ := h.surj_quasisimple_card hQ ψ hψ
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q)
  have hNpos : 0 < Nat.card ↥N := Nat.card_pos
  have h4 : Nat.card ↥N * n.factorial = Nat.card ↥N * (2 * Nat.card (Q ⧸ center Q)) := by
    rw [← h1, h3, h2]
    ring
  exact (Nat.eq_of_mul_eq_mul_left hNpos h4).symm

end Ivk93Cov

section Lifts

theorem ivk93cov_pComponent_lift_map {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hcentral : f.ker ≤ center X) [f.range.Normal]
    [Group.IsSolvable (Y ⧸ f.range)] {L : Subgroup Y} (h : IsPComponent 2 L) :
    ∃ M : Subgroup X, IsPComponent 2 M ∧ M.map f = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : f.rangeRestrict.ker ≤ center X := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hcentral
  obtain ⟨hle, hr⟩ :=
    CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient 2 f.range L h
  obtain ⟨M, hM, hm, -⟩ := CatalogueBCentralQuotient.pComponent_exists_lift 2
    f.rangeRestrict f.rangeRestrict_surjective hc _ hr
  have h1 : (M.map f.rangeRestrict).map f.range.subtype = M.map f := by
    rw [map_map]
    rfl
  refine ⟨M, hM, ?_⟩
  rw [← h1, hm, map_subgroupOf_eq_of_le hle]

end Lifts

section Block

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

theorem ivk93cov_su_half_block (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} {W F : Submodule E V}
    (hWs : (B.domRestrict₁₂ W W).IsSymm) (hWl : (B.domRestrict₁₂ W W).SeparatingLeft)
    (hW1 : 1 ≤ finrank E W) (hF0 : F ≠ ⊥)
    {Y : Type} [Group Y] (ι : Y →* sesqUnitaryGroup B) (hιi : Function.Injective ι)
    (hYF : ∀ y : Y, ∀ w ∈ F, unitaryOp (ι y) w = w)
    (ρ : Y →* sesqUnitaryGroup (B.domRestrict₁₂ W W)) (hρi : Function.Injective ρ)
    (hρc : CFSG.IsComponent ρ.range)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hker : ∀ y : Y, σ y = 1 → ι y ∈ sesqNormOneScalars h B) :
    2 ≤ finrank E W ∧
      (finrank E W = 2 → p ^ f ≠ 3 ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k),
        Nat.card k = p ^ f ∧ Nonempty (SL(2, k) ≃* ↥X)) ∧
      (3 ≤ finrank E W →
        Nonempty (↥X ⧸ center ↥X ≃* StatedProj (StatedSU (finrank E W) (p ^ f) E))) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  obtain ⟨hsigma, hne, hk0⟩ := CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f h.card_eq_sq
  have hsig := CatalogueBUnitaryTwo.unitaryFieldConjugation_apply p f h.card_eq_sq
  have hnd := CatalogueBUnitaryB.nondegenerate_of_isSymm hWs hWl
  obtain ⟨hdim2, h23, hρeq⟩ := eq_unitarySpecial_of_isComponent h hp hW1 hWs hWl hρc
  let eρ := MonoidHom.ofInjective hρi
  refine ⟨hdim2, fun hd2 => ?_, fun h3 => ?_⟩
  · have hq3 : p ^ f ≠ 3 := fun h3' => h23 (by rw [hd2, h3'])
    have hσi : Function.Injective σ := by
      rw [injective_iff_map_eq_one]
      intro y hy
      exact hιi (by rw [map_one]; exact eq_one_of_mem_sesqNormOneScalars (hker y hy) hF0 (hYF y))
    obtain ⟨eU⟩ := nonempty_unitarySpecial_equiv h (B.domRestrict₁₂ W W)
    obtain ⟨hkp, -, -, eSL, -⟩ := CatalogueBUnitaryTwo.unitary_field_two_special_linear_isomorphism
      p f h.card_eq_sq (B.domRestrict₁₂ W W) hWs hnd hd2
    exact ⟨hq3, _, inferInstance, inferInstance, hkp,
      ⟨((MulEquiv.ofBijective σ ⟨hσi, hσs⟩).symm.trans
        (eρ.trans ((MulEquiv.subgroupCongr hρeq).trans (eU.trans eSL)))).symm⟩⟩
  · obtain ⟨F⟩ : Nonempty (↥(sesqUnitaryGroup (B.domRestrict₁₂ W W)) ≃*
        ↥(CatalogueBUnitaryIsometry.isometryGroup
          (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq)
          (B.domRestrict₁₂ W W))) :=
      ⟨CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h (B.domRestrict₁₂ W W)⟩
    obtain ⟨e2⟩ : Nonempty (↥ρ.range ≃* ↥(ρ.range.map F.toMonoidHom)) :=
      ⟨ρ.range.equivMapOfInjective F.toMonoidHom F.injective⟩
    have hφi : Function.Injective (eρ.symm.toMonoidHom.comp e2.symm.toMonoidHom) :=
      eρ.symm.injective.comp e2.symm.injective
    exact nonempty_quotient_psu
      (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq) h.prime hp h.one_le
      h.card_eq_sq h3 (B.domRestrict₁₂ W W) hWs hnd hsigma hne hsig
      (isComponent_map_of_isComponent F hρc)
      (σ.comp (eρ.symm.toMonoidHom.comp e2.symm.toMonoidHom))
      (hσs.comp (eρ.symm.surjective.comp e2.symm.surjective))
      (CFSG.ComponentClassification.OddClassSelector.ker_comp_le_center _ hφi σ hσk)

theorem ivk93cov_block_of_half (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} {A : sesqUnitaryGroup B} {W F : Submodule E V}
    (hWs : (B.domRestrict₁₂ W W).IsSymm) (hWl : (B.domRestrict₁₂ W W).SeparatingLeft)
    (hW1 : 1 ≤ finrank E W) (hF0 : F ≠ ⊥)
    (e : centralizer ({A} : Set (sesqUnitaryGroup B)) ≃*
      sesqUnitaryGroup (B.domRestrict₁₂ W W) × sesqUnitaryGroup (B.domRestrict₁₂ F F))
    (hFe : ∀ g : centralizer ({A} : Set (sesqUnitaryGroup B)),
      F.subtype ∘ₗ (((e g).2 : LinearMap.GeneralLinearGroup E F) : Module.End E F) =
        unitaryOp (g : sesqUnitaryGroup B) ∘ₗ F.subtype)
    {N : Subgroup (centralizer ({A} : Set (sesqUnitaryGroup B)))} (hNc : CFSG.IsComponent N)
    (hleft : ∀ n ∈ N, (e n).2 = 1)
    {M : Subgroup (centralizer ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} :
      Set (sesqProjUnitary h B)))} (hM : N.map (centralizerImageHom A) = M) :
    2 ≤ finrank E W ∧
      (finrank E W = 2 → p ^ f ≠ 3 ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k),
        Nat.card k = p ^ f ∧ Nonempty (SL(2, k) ≃* ↥M)) ∧
      (3 ≤ finrank E W →
        Nonempty (↥M ⧸ center ↥M ≃* StatedProj (StatedSU (finrank E W) (p ^ f) E))) := by
  classical
  obtain ⟨ρ, hρi, hρc, -⟩ := restrict_component e hNc hleft
  let ι : N →* sesqUnitaryGroup B :=
    (centralizer ({A} : Set (sesqUnitaryGroup B))).subtype.comp N.subtype
  have hιi : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hYF : ∀ n : N, ∀ w ∈ F, unitaryOp (ι n) w = w := by
    intro n w hw
    have h4 := LinearMap.congr_fun (hFe (n : centralizer ({A} : Set (sesqUnitaryGroup B)))) ⟨w, hw⟩
    rw [hleft n n.2] at h4
    exact h4.symm
  let σ : N →* M := ((centralizerImageHom A).comp N.subtype).codRestrict M
    (fun n => hM ▸ Subgroup.mem_map_of_mem _ n.2)
  have hσs : Function.Surjective σ := by
    intro m
    have hm : (m : centralizer ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} :
        Set (sesqProjUnitary h B))) ∈ N.map (centralizerImageHom A) := hM ▸ m.2
    obtain ⟨n, hn, hnm⟩ := hm
    exact ⟨⟨n, hn⟩, Subtype.ext hnm⟩
  have hker0 : ∀ n : N, σ n = 1 → centralizerImageHom A (n : centralizer ({A} :
      Set (sesqUnitaryGroup B))) = 1 := fun n hn => congrArg Subtype.val hn
  have hσk : σ.ker ≤ center N := by
    intro n hn
    have h1 := ker_centralizerImageHom_le_center (h := h) A (hker0 n hn)
    rw [mem_center_iff] at h1 ⊢
    intro y
    exact Subtype.ext (h1 (y : centralizer ({A} : Set (sesqUnitaryGroup B))))
  have hker : ∀ n : N, σ n = 1 → ι n ∈ sesqNormOneScalars h B := by
    intro n hn
    have h1 := congrArg Subtype.val (hker0 n hn)
    exact (QuotientGroup.eq_one_iff _).mp h1
  exact ivk93cov_su_half_block h hp hWs hWl hW1 hF0 ι hιi hYF ρ hρi hρc σ hσs hσk hker

theorem ivk93cov_block_cases {G : Type} [Group G] {M : Subgroup G} {d nV : ℕ} (hd : 2 ≤ d)
    (hdn : d < nV)
    (b : d = 2 → p ^ f ≠ 3 ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = p ^ f ∧ Nonempty (SL(2, k) ≃* ↥M))
    (b' : 3 ≤ d → Nonempty (↥M ⧸ center ↥M ≃* StatedProj (StatedSU d (p ^ f) E))) :
    (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = p ^ f ∧ p ^ f ≠ 3 ∧
        Nonempty (SL(2, k) ≃* ↥M)) ∨
      (∃ d' : ℕ, 3 ≤ d' ∧ d' < nV ∧
        Nonempty (↥M ⧸ center ↥M ≃* StatedProj (StatedSU d' (p ^ f) E))) := by
  by_cases hd2 : d = 2
  · obtain ⟨hq3, k, hF, hFin, hk, hSL⟩ := b hd2
    exact Or.inl ⟨k, hF, hFin, hk, hq3, hSL⟩
  · exact Or.inr ⟨d, by omega, hdn, b' (by omega)⟩

theorem ivk93cov_exists_surj_of_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    {N : Subgroup G} {M : Subgroup H} (hm : N.map f = M) :
    ∃ σ : ↥N →* ↥M, Function.Surjective σ := by
  refine ⟨((f.comp N.subtype).codRestrict M (fun n => hm ▸ Subgroup.mem_map_of_mem _ n.2)), ?_⟩
  intro m
  have hm' : (m : H) ∈ N.map f := hm ▸ m.2
  obtain ⟨n, hn, hnm⟩ := hm'
  exact ⟨⟨n, hn⟩, Subtype.ext hnm⟩

theorem ivk93cov_gl_component {W : Type} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    [Finite E] (hW : 1 ≤ finrank E W) {G : Type} [Group G]
    (eC : G ≃* LinearMap.GeneralLinearGroup E W) {N : Subgroup G} (hN : IsPComponent 2 N) :
    2 ≤ finrank E W ∧ Nonempty (SL(finrank E W, E) ≃* ↥N) := by
  let eGL := eC.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv E W).trans
    (CatalogueBAlternatingIsometry.basisMatrixEquiv (Module.finBasis E W)))
  obtain ⟨h2m, -, -, k₁, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ E hW 2 _
    (CatalogueBAlternating.pComponent_map_equiv 2 eGL _ hN)
  exact ⟨h2m, ⟨((CatalogueBGeneralLinear.rangeEquivSpecialLinear _ E).symm.trans
    (MulEquiv.subgroupCongr k₁.symm)).trans
    (N.equivMapOfInjective eGL.toMonoidHom eGL.injective).symm⟩⟩

theorem ivk93cov_lift_data (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {A : sesqUnitaryGroup B} (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    {M : Subgroup (centralizer
      ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} : Set (sesqProjUnitary h B)))}
    (hM : IsPComponent 2 M) :
    CFSG.IsQuasisimple ↥M ∧ ∃ N : Subgroup (centralizer ({A} : Set (sesqUnitaryGroup B))),
      CFSG.IsComponent N ∧ IsPComponent 2 N ∧ N.map (centralizerImageHom A) = M := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨l, -, -, -, -, -, -, -, -, -, hnormal, hindex, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  rw [← range_centralizerImageHom] at hnormal hindex
  have := hnormal
  have := CatalogueRelativeB.quotient_solvable_of_index_le_two _ hindex
  obtain ⟨N, hN₁, hm⟩ := ivk93cov_pComponent_lift_map (centralizerImageHom A)
    (ker_centralizerImageHom_le_center A) hM
  have hq := projective_unitary_involution_centralizer_p_components h hp hn hB hBl _ hA 2
    Nat.prime_two M hM
  exact ⟨hq, N, ivk93_isComponent_of_pComponent hN₁
    (centralizer_lift_pComponent_quasisimple h hp hn hB hBl hA 2 Nat.prime_two N hN₁), hN₁, hm⟩

theorem ivk93cov_sides {G G₁ G₂ : Type*} [Group G] [Group G₁] [Group G₂] [Finite G₁] [Finite G₂]
    (e : G ≃* G₁ × G₂) {N : Subgroup G} (hN : CFSG.IsComponent N) :
    (∀ n ∈ N, (e n).2 = 1) ∨ (∀ n ∈ N, ((e.trans MulEquiv.prodComm) n).2 = 1) := by
  rcases CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      (isComponent_map_of_isComponent e hN) with k | k
  · exact Or.inl fun n hn => k _ (mem_map_of_mem _ hn)
  · exact Or.inr fun n hn => k _ (mem_map_of_mem _ hn)

theorem ivk93cov_half_cases (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} {A : sesqUnitaryGroup B} {W F : Submodule E V}
    (hWs : (B.domRestrict₁₂ W W).IsSymm) (hWl : (B.domRestrict₁₂ W W).SeparatingLeft)
    (hW1 : 1 ≤ finrank E W) (hF0 : F ≠ ⊥)
    (e : centralizer ({A} : Set (sesqUnitaryGroup B)) ≃*
      sesqUnitaryGroup (B.domRestrict₁₂ W W) × sesqUnitaryGroup (B.domRestrict₁₂ F F))
    (hFe : ∀ g : centralizer ({A} : Set (sesqUnitaryGroup B)),
      F.subtype ∘ₗ (((e g).2 : LinearMap.GeneralLinearGroup E F) : Module.End E F) =
        unitaryOp (g : sesqUnitaryGroup B) ∘ₗ F.subtype)
    {N : Subgroup (centralizer ({A} : Set (sesqUnitaryGroup B)))} (hNc : CFSG.IsComponent N)
    (hleft : ∀ n ∈ N, (e n).2 = 1)
    {M : Subgroup (centralizer ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} :
      Set (sesqProjUnitary h B)))} (hM : N.map (centralizerImageHom A) = M) {nV : ℕ}
    (hdn : finrank E W < nV) :
    (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = p ^ f ∧ p ^ f ≠ 3 ∧
        Nonempty (SL(2, k) ≃* ↥M)) ∨
      (∃ d' : ℕ, 3 ≤ d' ∧ d' < nV ∧
        Nonempty (↥M ⧸ center ↥M ≃* StatedProj (StatedSU d' (p ^ f) E))) := by
  obtain ⟨hd, b, b'⟩ := ivk93cov_block_of_half h hp hWs hWl hW1 hF0 e hFe hNc hleft hM
  exact ivk93cov_block_cases hd hdn b b'

theorem ivk93cov_unitary_split (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) {A : sesqUnitaryGroup B} {P Q : Submodule E V}
    (hP : P ≠ ⊥) (hQ : Q ≠ ⊥) (hcompl : IsCompl P Q)
    (hsepP : (B.domRestrict₁₂ P P).SeparatingLeft) (hsepQ : (B.domRestrict₁₂ Q Q).SeparatingLeft)
    (e : centralizer ({A} : Set (sesqUnitaryGroup B)) ≃*
      sesqUnitaryGroup (B.domRestrict₁₂ P P) × sesqUnitaryGroup (B.domRestrict₁₂ Q Q))
    (he : ∀ g : centralizer ({A} : Set (sesqUnitaryGroup B)),
      P.subtype ∘ₗ (((e g).1 : LinearMap.GeneralLinearGroup E P) : Module.End E P) =
          unitaryOp (g : sesqUnitaryGroup B) ∘ₗ P.subtype ∧
        Q.subtype ∘ₗ (((e g).2 : LinearMap.GeneralLinearGroup E Q) : Module.End E Q) =
          unitaryOp (g : sesqUnitaryGroup B) ∘ₗ Q.subtype)
    {N : Subgroup (centralizer ({A} : Set (sesqUnitaryGroup B)))} (hc : CFSG.IsComponent N)
    {M : Subgroup (centralizer ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} :
      Set (sesqProjUnitary h B)))} (hm : N.map (centralizerImageHom A) = M) :
    (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = p ^ f ∧ p ^ f ≠ 3 ∧
        Nonempty (SL(2, k) ≃* ↥M)) ∨
      (∃ d' : ℕ, 3 ≤ d' ∧ d' < finrank E V ∧
        Nonempty (↥M ⧸ center ↥M ≃* StatedProj (StatedSU d' (p ^ f) E))) := by
  classical
  have : Finite E := h.finite
  have hsymm : ∀ X : Submodule E V, (B.domRestrict₁₂ X X).IsSymm := fun X =>
    ⟨fun x y => hB.eq (x : V) (y : V)⟩
  have hP1 : 1 ≤ finrank E P := Submodule.one_le_finrank_iff.mpr hP
  have hQ1 : 1 ≤ finrank E Q := Submodule.one_le_finrank_iff.mpr hQ
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rcases ivk93cov_sides e hc with l₁ | r₁
  · exact ivk93cov_half_cases h hp (hsymm P) hsepP hP1 hQ e (fun g => (he g).2) hc l₁ hm
      (by omega)
  · exact ivk93cov_half_cases h hp (hsymm Q) hsepQ hQ1 hP (e.trans MulEquiv.prodComm)
      (fun g => (he g).1) hc r₁ hm (by omega)

theorem ivk93cov_unitary_paired (h : UnitaryFieldData p f E) [FiniteDimensional E V]
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} {A : sesqUnitaryGroup B} {P : Submodule E V} (hP : P ≠ ⊥)
    (h2m : 2 * finrank E P = finrank E V)
    (eC : centralizer ({A} : Set (sesqUnitaryGroup B)) ≃* LinearMap.GeneralLinearGroup E P)
    {N : Subgroup (centralizer ({A} : Set (sesqUnitaryGroup B)))} (hN : IsPComponent 2 N)
    {M : Subgroup (centralizer ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} :
      Set (sesqProjUnitary h B)))} (hm : N.map (centralizerImageHom A) = M) :
    ∃ m : ℕ, 2 ≤ m ∧ 2 * m = finrank E V ∧ ∃ ψ : SL(m, E) →* ↥M, Function.Surjective ψ := by
  have : Finite E := h.finite
  have hP1 : 1 ≤ finrank E P := Submodule.one_le_finrank_iff.mpr hP
  obtain ⟨h2m', ⟨φ⟩⟩ := ivk93cov_gl_component hP1 eC hN
  obtain ⟨σ, hσs⟩ := ivk93cov_exists_surj_of_map _ hm
  exact ⟨_, h2m', h2m, σ.comp φ.toMonoidHom, hσs.comp φ.surjective⟩

theorem ivk93cov_structure_cases (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {A : sesqUnitaryGroup B} (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2) :
    (∃ P Q : Submodule E V, P ≠ ⊥ ∧ Q ≠ ⊥ ∧ IsCompl P Q ∧
      (B.domRestrict₁₂ P P).SeparatingLeft ∧ (B.domRestrict₁₂ Q Q).SeparatingLeft ∧
      ∃ e : centralizer ({A} : Set (sesqUnitaryGroup B)) ≃*
          sesqUnitaryGroup (B.domRestrict₁₂ P P) × sesqUnitaryGroup (B.domRestrict₁₂ Q Q),
        ∀ g : centralizer ({A} : Set (sesqUnitaryGroup B)),
          P.subtype ∘ₗ (((e g).1 : LinearMap.GeneralLinearGroup E P) : Module.End E P) =
              unitaryOp (g : sesqUnitaryGroup B) ∘ₗ P.subtype ∧
            Q.subtype ∘ₗ (((e g).2 : LinearMap.GeneralLinearGroup E Q) : Module.End E Q) =
              unitaryOp (g : sesqUnitaryGroup B) ∘ₗ Q.subtype) ∨
    (∃ P : Submodule E V, P ≠ ⊥ ∧ 2 * finrank E P = finrank E V ∧
      Nonempty (centralizer ({A} : Set (sesqUnitaryGroup B)) ≃*
        LinearMap.GeneralLinearGroup E P)) := by
  obtain ⟨l, -, -, hN, hP, hMne, hcompl, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  rcases hN with hN | hN
  · obtain ⟨-, hsepP, hsepM, e, he⟩ := hsplit hN
    exact Or.inl ⟨_, _, hP, hMne, hcompl, hsepP, hsepM, e, he⟩
  · obtain ⟨-, -, -, h2m, -, -, eC, -⟩ := hpaired hN
    exact Or.inr ⟨_, hP, h2m, ⟨eC⟩⟩

theorem ivk93cov_unitary_block (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    [FiniteDimensional E V] (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    {M : Subgroup (centralizer
      ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} : Set (sesqProjUnitary h B)))}
    (hM : IsPComponent 2 M) :
    CFSG.IsQuasisimple ↥M ∧
      ((∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = p ^ f ∧ p ^ f ≠ 3 ∧
          Nonempty (SL(2, k) ≃* ↥M)) ∨
        (∃ d : ℕ, 3 ≤ d ∧ d < finrank E V ∧
          Nonempty (↥M ⧸ center ↥M ≃* StatedProj (StatedSU d (p ^ f) E))) ∨
        (∃ m : ℕ, 2 ≤ m ∧ 2 * m = finrank E V ∧
          ∃ ψ : SL(m, E) →* ↥M, Function.Surjective ψ)) := by
  obtain ⟨hq, N, hc, hN₁, hm⟩ := ivk93cov_lift_data h hp hn hB hBl hA hM
  refine ⟨hq, ?_⟩
  rcases ivk93cov_structure_cases h hp hn hB hBl hA with
    ⟨P, Q, hP, hQ, hcompl, hsepP, hsepQ, e, he⟩ | ⟨P, hP, h2m, ⟨eC⟩⟩
  · rcases ivk93cov_unitary_split h hp hB hP hQ hcompl hsepP hsepQ e he hc hm with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (ivk93cov_unitary_paired h hP h2m eC hN₁ hm))

end Block

section JLevel

theorem ivk93cov_psu_embedding {p f : ℕ} {K : Type} [Field K] (hud : UnitaryFieldData p f K)
    {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1) :
    ∃ φ : StatedProj (StatedSU (2 * r + ε) (p ^ f) K) →* sesqProjUnitary hud (hypForm hud r ε),
      Function.Injective φ ∧ φ.range.Normal := by
  classical
  have : Fact p.Prime := ⟨hud.prime⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud hr hε).1
  set θ := (hypPSUEquivStatedProj hud hR (by omega)).symm
  set ι : hypPSU hud r ε →* sesqProjUnitary hud (hypForm hud r ε) :=
    (projSpecial hud (hypForm hud r ε)).subtype.comp (hypModelEquiv hud).toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp (hypModelEquiv hud).injective
  set φ := ι.comp θ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := hι.comp θ.injective
  have hrange : φ.range = projSpecial hud (hypForm hud r ε) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (hypModelEquiv hud (θ y)).2
    · intro hz
      obtain ⟨w, hw⟩ := (hypModelEquiv hud).surjective ⟨z, hz⟩
      refine ⟨θ.symm w, ?_⟩
      rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        hιdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hw]
      rfl
  refine ⟨φ, hφ, ?_⟩
  rw [hrange]
  infer_instance

theorem ivk93cov_exists_unitary {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)
    [Finite (StatedProj (StatedSU (2 * r + ε) (p ^ f) K))]
    {x : StatedProj (StatedSU (2 * r + ε) (p ^ f) K)} {n : ℕ}
    {B : Subgroup (StatedProj (StatedSU (2 * r + ε) (p ^ f) K))} (h : Ivk93Cov x n B) :
    ∃ hud : UnitaryFieldData p f K, ∃ A : sesqUnitaryGroup (hypForm hud r ε),
      orderOf (QuotientGroup.mk A : sesqProjUnitary hud (hypForm hud r ε)) = 2 ∧
      ∃ M : Subgroup (centralizer
          ({QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε)) A} :
            Set (sesqProjUnitary hud (hypForm hud r ε)))),
        IsPComponent 2 M ∧ ∃ χ : ↥M →* ↥B, Function.Surjective χ := by
  classical
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨φ, hφ, hnorm⟩ := ivk93cov_psu_embedding hud hr hε
  have hK₁ := isPComponent_map_of_normal φ hφ h.le h.comp.2
  obtain ⟨A, hA⟩ := QuotientGroup.mk'_surjective (sesqNormOneScalars hud (hypForm hud r ε)) (φ x)
  rw [← hA] at hK₁
  refine ⟨hud, A, ?_, _, hK₁.2, ((B.equivMapOfInjective φ hφ).symm.toMonoidHom).comp
    (Subgroup.subgroupOfEquivOfLe hK₁.1).toMonoidHom, ?_⟩
  · change orderOf ((QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε))) A) = 2
    rw [hA, orderOf_injective φ hφ x, h.ord]
  · exact (B.equivMapOfInjective φ hφ).symm.surjective.comp
      (Subgroup.subgroupOfEquivOfLe hK₁.1).surjective

theorem ivk93cov_psu_false {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) {r ε : ℕ} (hr : r = 2) (hε : ε ≤ 1)
    [Finite (StatedProj (StatedSU (2 * r + ε) (p ^ f) K))]
    {x : StatedProj (StatedSU (2 * r + ε) (p ^ f) K)} {n : ℕ}
    {B : Subgroup (StatedProj (StatedSU (2 * r + ε) (p ^ f) K))} (h : Ivk93Cov x n B) :
    False := by
  classical
  obtain ⟨hud, A, hA, M, hM, χ, hχ⟩ := ivk93cov_exists_unitary hp hf hK (by omega) hε h
  have : Fact p.Prime := ⟨hp⟩
  have hdim : finrank K (HypIndex r ε → K) = 2 * r + ε := UnitaryHigher.finrank_hypIndex_fun
  have hq3 : 3 ≤ p ^ f := by
    have h1 := hp.two_le
    have h2 : 3 ≤ p := by omega
    exact h2.trans (Nat.le_self_pow (by omega) p)
  have hqodd : (p ^ f) % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  obtain ⟨hq, hcases⟩ := ivk93cov_unitary_block hud hp2 (V := HypIndex r ε → K) (by omega)
    (hypForm_isSymm hud) (hypForm_separatingLeft hud) hA hM
  rcases hcases with ⟨k, _, _, hk, hq3', ⟨e⟩⟩ | ⟨d, hd3, hdn, ⟨e⟩⟩ | ⟨m, hm2, hm, ψ, hψ⟩
  ·
    have hkodd : Odd (Nat.card k) := by
      rw [hk]
      exact (hp.odd_of_ne_two hp2).pow
    have hk5 : 5 ≤ Nat.card k := by
      rw [hk]
      omega
    exact h.false_of_surj_sl2 hkodd hk5 (χ.comp e.toMonoidHom) (hχ.comp e.surjective)
  ·
    have h1 : 2 * Nat.card (↥M ⧸ center ↥M) = n.factorial :=
      h.two_mul_card_quot_center hq χ hχ
    rw [Nat.card_congr e.toEquiv] at h1
    exact ivk93cov_psu_ne hp hp2 hf hK (by omega) h.eight h.le_eleven h1
  ·
    have hm' : m = 2 := by omega
    subst hm'
    have hoddK : Odd (Nat.card K) := by
      rw [hK]
      exact ((hp.odd_of_ne_two hp2).pow).pow
    have h5 : 5 ≤ Nat.card K := by
      rw [hK]
      nlinarith
    exact h.false_of_surj_sl2 hoddK h5 (χ.comp ψ) (hχ.comp hψ)

theorem ivk93cov_u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk93CovEmpty (fun X _ => LieModel X .PSU 4 p f) := by
  intro p f hp hp2 hf _
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ n B hc => ?_
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨φ⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  have : Finite (StatedProj (StatedSU (2 * 2 + 0) (p ^ f) K)) := Finite.of_equiv _ φ.toEquiv
  exact ivk93cov_psu_false hp hp2 hf hK (r := 2) (ε := 0) rfl (by norm_num) (hc.of_equiv φ)

theorem ivk93cov_u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 →
    Ivk93CovEmpty (fun X _ => LieModel X .PSU 5 p f) := by
  intro p f hp hf hmod
  have hp2 : p ≠ 2 := by
    intro h2
    subst h2
    have : (2 : ℕ) ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ n B hc => ?_
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨φ⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  have : Finite (StatedProj (StatedSU (2 * 2 + 1) (p ^ f) K)) := Finite.of_equiv _ φ.toEquiv
  exact ivk93cov_psu_false hp hp2 hf hK (r := 2) (ε := 1) rfl (by norm_num) (hc.of_equiv φ)

end JLevel

end CFSG.GH74.GLS.IVK.Proofs2

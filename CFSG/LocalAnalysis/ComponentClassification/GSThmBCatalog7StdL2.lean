module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdArith
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4L2Inv
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CentralProd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStab
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdRows

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open CatalogueSchreierLinearTwo (semilinearAction semilinearAction_inr semilinearEquivAut)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem two_dvd_mul_sq_sub (x : ℕ) : 2 ∣ x * (x ^ 2 - 1) := by
  rcases Nat.even_or_odd x with h | h
  · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp h) _
  · exact Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd h.pow odd_one)) _

theorem half_mul_sq_sub_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    a * (a ^ 2 - 1) / 2 < b * (b ^ 2 - 1) / 2 := by
  apply Nat.div_lt_div_of_lt_of_dvd (two_dvd_mul_sq_sub b)
  have h1 : a ^ 2 - 1 ≤ b ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hab.le 2) 1
  have h2 : 0 < b ^ 2 - 1 := by
    have : 2 ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  calc a * (a ^ 2 - 1) ≤ a * (b ^ 2 - 1) := Nat.mul_le_mul_left _ h1
    _ < b * (b ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hab h2

variable {F : Type} [Field F] [Finite F]

theorem pComponent_fixed_psl2 (hpp : IsOddPrimePower (Nat.card F))
    (h9 : 9 < Nat.card F) {α : MulAut (PSL2 F)} (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {L : Subgroup (PSL2 F)} (hL : L ≤ fixedSubgroup α)
    (hLc : IsPComponent 2 (L.subgroupOf (fixedSubgroup α))) :
    ∃ s : ℕ, Nat.card F = s ^ 2 ∧ IsSimpleGroup L ∧ Nat.card L = s * (s ^ 2 - 1) / 2 := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_isOddPrimePower hpp
  obtain ⟨g, hgα⟩ := (semilinearEquivAut F).surjective α
  have hgα' : semilinearAction F g = α := hgα
  have hgg : g * g = 1 := (semilinearEquivAut F).injective (by rw [map_mul, hgα, hα2, map_one])
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hα1 (by rw [← hgα', map_one])
  have hLp : ⁅L, L⁆ = L := commutator_eq_self_of_isPComponent hL hLc
  have hLb : L ≠ ⊥ := CatFactsSp4.ne_bot_of_isPComponent hLc
  have hfixL : ∀ y ∈ L, α y = y := fun y hy => hL hy
  by_cases hr : g.right = 1
  ·
    exfalso
    have hgt : g = SemidirectProduct.inl g.left := SemidirectProduct.ext rfl hr
    have ht2 : g.left * g.left = 1 := by
      have := congrArg SemidirectProduct.left hgg
      simpa [hr] using this
    have ht1 : g.left ≠ 1 := by
      intro h
      apply hg1
      rw [hgt, h, map_one]
    have hTp : ⁅L.map (incl F), L.map (incl F)⁆ = L.map (incl F) := by
      rw [← Subgroup.map_commutator, hLp]
    have hTg : ∀ x ∈ L.map (incl F), x * SemidirectProduct.inl g.left =
        SemidirectProduct.inl g.left * x := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← hgt]
      exact ((commute_incl_iff g y).mpr (by rw [hgα']; exact hfixL y hy)).symm
    have hTb := CatFactsSp4.perfect_centralizer_inl_eq_bot h2 ht2 ht1 hTg hTp
    apply hLb
    rw [eq_bot_iff]
    intro y hy
    have : incl F y ∈ L.map (incl F) := ⟨y, hy, rfl⟩
    rw [hTb, mem_bot] at this
    rw [mem_bot]
    exact incl_injective F (this.trans (map_one _).symm)
  have hgo : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hpp g hgo hr
  have hσσ' : g.right * g.right = 1 := by
    have := congrArg SemidirectProduct.right hgg
    simpa using this
  have hσ : orderOf g.right = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσσ') hr
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield g.right hσ
  have hσσ : ∀ x, g.right (g.right x) = x := fun x => by
    have := congrArg (fun τ : F ≃+* F => τ x) hσσ'
    simpa using this
  obtain ⟨c, hc⟩ : ∃ c : MulAut (PSL2 F), c = semilinearAction F (SemidirectProduct.inl C) :=
    ⟨_, rfl⟩
  have hgC : g = SemidirectProduct.inl C * SemidirectProduct.inr g.right *
      (SemidirectProduct.inl C)⁻¹ := by
    rw [← hC]
    group
  have hαc : α = c * psl2FieldAut F g.right * c⁻¹ := by
    rw [← hgα', hc]
    conv_lhs => rw [hgC]
    rw [map_mul, map_mul, map_inv, semilinearAction_inr]
  have hL₁p : ⁅(L.map (c⁻¹).toMonoidHom).map (incl F), (L.map (c⁻¹).toMonoidHom).map (incl F)⁆ =
      (L.map (c⁻¹).toMonoidHom).map (incl F) := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hLp]
  have hL₁σ : ∀ x ∈ (L.map (c⁻¹).toMonoidHom).map (incl F),
      x * SemidirectProduct.inr g.right = SemidirectProduct.inr g.right * x := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    symm
    rw [commute_incl_iff, semilinearAction_inr]
    have h1 := hfixL y hy
    rw [hαc] at h1
    have h3 := congrArg (c⁻¹ : MulAut (PSL2 F)) h1
    simpa [MulAut.mul_apply] using h3
  have hL₁le := CatFactsSp4.perfect_centralizer_inr_le hK₀ h90 hσσ hL₁σ hL₁p
  have hLN' : L ≤ ((psl2Sub K₀).range).map c.toMonoidHom := by
    intro y hy
    obtain ⟨w, hw⟩ := hL₁le ⟨(c⁻¹ : MulAut (PSL2 F)) y, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨psl2Sub K₀ w, ⟨w, rfl⟩, ?_⟩
    have hw' : psl2Sub K₀ w = (c⁻¹ : MulAut (PSL2 F)) y := incl_injective F hw
    change c (psl2Sub K₀ w) = y
    rw [hw']
    simp
  have hN'fix : ((psl2Sub K₀).range).map c.toMonoidHom ≤ fixedSubgroup α := by
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    change α (c (psl2Sub K₀ w)) = c (psl2Sub K₀ w)
    have hw : psl2FieldAut F g.right (psl2Sub K₀ w) = psl2Sub K₀ w :=
      psl2Sub_mem_fieldCent hK₀ w
    rw [hαc]
    simp [MulAut.mul_apply, hw]
  have hK₀4 : 4 ≤ Nat.card K₀ := by
    by_contra hlt
    push Not at hlt
    have : Nat.card K₀ ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hs0 : IsSimpleGroup (PSL2 K₀) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK₀4
  let e₁ : PSL2 K₀ ≃* (psl2Sub K₀).range := MonoidHom.ofInjective (psl2Sub_injective K₀)
  let e₂ : (psl2Sub K₀).range ≃* ((psl2Sub K₀).range).map c.toMonoidHom :=
    ((psl2Sub K₀).range).equivMapOfInjective c.toMonoidHom c.injective
  have hsN' : IsSimpleGroup (((psl2Sub K₀).range).map c.toMonoidHom) :=
    (e₁.trans e₂).isSimpleGroup_congr.mp hs0
  obtain ⟨-, -, hsn, -, -⟩ := hLc
  have hsn' := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hN'fix hsn
  have hLeq : L = ((psl2Sub K₀).range).map c.toMonoidHom := by
    rcases hsn'.eq_bot_or_top_of_isSimpleGroup hsN' with h | h
    · exfalso
      apply hLb
      rw [subgroupOf_eq_bot] at h
      exact le_bot_iff.mp (fun y hy => h.le_bot ⟨hy, hLN' hy⟩)
    · rw [subgroupOf_eq_top] at h
      exact le_antisymm hLN' h
  have hodd : Odd (Nat.card K₀) := by
    obtain ⟨p, n, -, hpo, -, hpn⟩ := hpp
    have : Odd (Nat.card K₀ ^ 2) := by rw [← hcard, hpn]; exact hpo.pow
    exact (Nat.odd_pow_iff two_ne_zero).mp this
  refine ⟨Nat.card K₀, hcard, hLeq ▸ hsN', ?_⟩
  rw [hLeq, ← Nat.card_congr (e₁.trans e₂).toEquiv,
    psl2_card_formula K₀ (isOddPrimePower_of_odd_card K₀ hodd)]

variable {H : Type} [Group H] [Finite H]

theorem pComponent_of_psl2
    (hC : centralizer (generalizedFitting H : Set H) = ⊥) (hpp : IsOddPrimePower (Nat.card F))
    (h9 : 9 < Nat.card F) (e : ↥(generalizedFitting H) ≃* PSL2 F) {x : H} (hx : orderOf x = 2)
    {L : Subgroup H} (hLx : L ≤ centralizer ({x} : Set H)) (hLG : L ≤ generalizedFitting H)
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set H)))) :
    ∃ s : ℕ, Nat.card F = s ^ 2 ∧ IsSimpleGroup L ∧ Nat.card L = s * (s ^ 2 - 1) / 2 := by
  obtain ⟨α, hα2, hα1, L', hL'α, hL'c, ⟨φ⟩⟩ := exists_fixed_pComponent hC hx hLx hLG hL e
  obtain ⟨s, hs, hsimp, hcard⟩ :=
    pComponent_fixed_psl2 hpp h9 (by rw [← pow_two]; exact hα2) hα1 hL'α hL'c
  exact ⟨s, hs, φ.isSimpleGroup_congr.mp hsimp, (Nat.card_congr φ.toEquiv).symm.trans hcard⟩

omit [Finite H] in
theorem card_quot_eq_of_simple {L : Subgroup H} (hs : IsSimpleGroup L)
    (h1 : Nat.card (L ⧸ pPrimeCore 2 L) ≠ 1) : Nat.card (L ⧸ pPrimeCore 2 L) = Nat.card L := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 L)
  rcases hs.eq_bot_or_eq_top_of_normal (pPrimeCore 2 L) with h | h
  · have h' : Nat.card (pPrimeCore 2 L) = 1 := by rw [h, Subgroup.card_bot]
    rw [h', mul_one] at hc
    exact hc.symm
  · exfalso
    apply h1
    rw [h]
    exact Subgroup.index_top

theorem rowL2 : RowL2 := by
  intro H _ _ c p f hp hp2 hf h5 hm
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hm
  have hpp : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hp2 hf hF
  have h9 : 9 < Nat.card F := by
    by_contra hle
    push Not at hle
    have hd := c.ordL2sq_dvd_of_equiv e
    rw [psl2_card_formula F hpp] at hd
    have h2F : 1 < Nat.card F := Finite.one_lt_card
    have hpos : 0 < Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
      have := half_mul_sq_sub_lt (a := 1) le_rfl h2F
      rwa [show 1 * (1 ^ 2 - 1) / 2 = 0 from rfl] at this
    have h1 := Nat.le_of_dvd hpos hd
    have h2 : Nat.card F * (Nat.card F ^ 2 - 1) / 2 ≤ 9 * (9 ^ 2 - 1) / 2 :=
      Nat.div_le_div_right
        (Nat.mul_le_mul hle (Nat.sub_le_sub_right (Nat.pow_le_pow_left hle 2) 1))
    have h3 := ordL2sq_mono c.five_le
    have h4 : ordL2sq 5 = 7800 := by decide
    have h5' : 9 * (9 ^ 2 - 1) / 2 = 360 := by norm_num
    omega
  obtain ⟨s, hs, hKs, hKc⟩ := pComponent_of_psl2 c.centralizer_eq_bot hpp h9 e c.orderOf_b c.K_le
    c.K_le_G c.isPComponent_K
  obtain ⟨s', hs', hJs, hJc⟩ := pComponent_of_psl2 c.centralizer_eq_bot hpp h9 e c.orderOf_a
    c.J_le c.J_le_G c.isPComponent_J
  have hss : s' = s := Nat.pow_left_injective two_ne_zero (hs'.symm.trans hs)
  obtain ⟨-, -, -, -, FK, _, _, hFK, ⟨eK⟩⟩ := lieModel_psl2_data c.type_K
  obtain ⟨-, -, -, -, FJ, _, _, hFJ, ⟨eJ⟩⟩ := lieModel_psl2_data c.type_J
  have hf1 := c.one_le
  have hq5 := c.five_le
  have hQK : Nat.card FK = (c.p ^ c.f) ^ 2 := by rw [hFK, ← pow_mul, mul_comm]
  have hKb : Nat.card (c.K ⧸ pPrimeCore 2 c.K) =
      (c.p ^ c.f) ^ 2 * (((c.p ^ c.f) ^ 2) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eK.toEquiv,
      psl2_card_formula FK (isOddPrimePower_of c.prime c.ne_two (by omega) hFK), hQK]
  have hJb : Nat.card (c.J ⧸ pPrimeCore 2 c.J) = c.p ^ c.f * ((c.p ^ c.f) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eJ.toEquiv,
      psl2_card_formula FJ (isOddPrimePower_of c.prime c.ne_two c.one_le hFJ), hFJ]
  have hlt : c.p ^ c.f * ((c.p ^ c.f) ^ 2 - 1) / 2 <
      (c.p ^ c.f) ^ 2 * (((c.p ^ c.f) ^ 2) ^ 2 - 1) / 2 :=
    half_mul_sq_sub_lt (by omega) (by nlinarith)
  have hJ1 : 1 < c.p ^ c.f * ((c.p ^ c.f) ^ 2 - 1) / 2 := by
    have := half_mul_sq_sub_lt (a := 2) (by norm_num) (show 2 < c.p ^ c.f by omega)
    have h3 : 2 * (2 ^ 2 - 1) / 2 = 3 := by norm_num
    omega
  have hK := card_quot_eq_of_simple hKs (by rw [hKb]; omega)
  have hJ := card_quot_eq_of_simple hJs (by rw [hJb]; omega)
  rw [hKb, hKc] at hK
  rw [hJb, hJc, hss] at hJ
  exact absurd (hJ.trans hK.symm) (ne_of_lt hlt)

end Catalog7Std

end CFSG.ComponentClassification.GSThmB

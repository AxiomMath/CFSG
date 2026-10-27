module

public import CFSG.LocalAnalysis.EvenBN.G2.SeriesCenters
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases
public import CFSG.LocalAnalysis.EvenBN.Common.NaturalModuleBridge
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise MatrixGroups

namespace FieldNaturalAux

open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule (actionFixed mem_actionFixed
  even_linear_two_half_fixed_module_transitivity)

section SL2

variable {k : Type*} [Field k]

theorem sl2_commutator_top [Finite k] (h4 : 4 ≤ Nat.card k) :
    ⁅(⊤ : Subgroup SL(2, k)), (⊤ : Subgroup SL(2, k))⁆ = ⊤ := by
  have := CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four h4)
  have h := Group.IsPerfect.commutator_eq_top (G := SL(2, k))
  rwa [commutator_def] at h

theorem sl2_hom_trivial [Finite k] (h4 : 4 ≤ Nat.card k) {A : Type*}
    [CommGroup A] (f : SL(2, k) →* A) (g : SL(2, k)) : f g = 1 := by
  have hle : ⁅(⊤ : Subgroup SL(2, k)), (⊤ : Subgroup SL(2, k))⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  rw [sl2_commutator_top h4] at hle
  exact MonoidHom.mem_ker.1 (hle (Subgroup.mem_top g))

end SL2

section Action

variable {k : Type*} [Field k] [Finite k] [CharP k 2]

theorem actionFixed_top_eq_bot {A : Type*} [CommGroup A] [Finite A] {n : ℕ} (hn : 2 ≤ n)
    (hk : Nat.card k = 2 ^ n) (hA : Nat.card A = (2 ^ n) ^ 2) (ρ : SL(2, k) →* MulAut A)
    (hρ : ρ ≠ 1) : actionFixed ρ ⊤ = ⊥ := by
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  by_contra hC
  set C := actionFixed ρ ⊤ with hCdef
  have hmap : ∀ j, C.map (ρ j : A →* A) = C := by
    intro j
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      have h1 : ρ j c = c := hc j (Subgroup.mem_top j)
      show ρ j c ∈ C
      rw [h1]
      exact hc
    · intro hx
      exact ⟨x, hx, hx j (Subgroup.mem_top j)⟩
  haveI : C.Normal := Subgroup.normal_of_comm C
  set ρb := CFSG.SL2MinimalFaithful.quotientAction ρ C hmap with hρbdef
  by_cases hρb : ρb = 1
  · apply hρ
    refine MonoidHom.ext fun g => MulEquiv.ext fun a => ?_
    have hfix : ∀ h : SL(2, k), a⁻¹ * ρ h a ∈ C := by
      intro h
      have h1 : ρb h (a : A ⧸ C) = (a : A ⧸ C) := by
        rw [hρb]
        rfl
      rw [hρbdef, CFSG.SL2MinimalFaithful.quotientAction_mk] at h1
      exact QuotientGroup.eq.1 h1.symm
    let f : SL(2, k) →* A := MonoidHom.mk' (fun h => a⁻¹ * ρ h a) (fun h₁ h₂ => by
      have hc₂ := hfix h₂
      have e : ρ h₂ a = a * (a⁻¹ * ρ h₂ a) := by group
      show a⁻¹ * ρ (h₁ * h₂) a = (a⁻¹ * ρ h₁ a) * (a⁻¹ * ρ h₂ a)
      rw [map_mul, MulAut.mul_apply, e, map_mul, hfix h₂ h₁ (Subgroup.mem_top h₁)]
      group)
    have := sl2_hom_trivial h4 f g
    simp only [f, MonoidHom.mk'_apply] at this
    rw [MonoidHom.one_apply, MulAut.one_apply]
    exact (inv_mul_eq_one.1 this).symm
  · have hV : IsPGroup 2 (A ⧸ C) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 2 * n) (by rw [hA, ← pow_mul, mul_comm])
      exact hA2.to_quotient C
    have h1 := sl2_card_sq_le_of_ne_one (MulEquiv.refl SL(2, k)) hk hn ρb hV hρb
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup C
    have hCpos : 0 < Nat.card C := Nat.card_pos
    rw [hk] at h1
    rw [hA] at h2
    have h3 : Nat.card C ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have : (2 ^ n) ^ 2 * 2 ≤ (2 ^ n) ^ 2 := by
        calc (2 ^ n) ^ 2 * 2 ≤ Nat.card (A ⧸ C) * Nat.card C := Nat.mul_le_mul h1 hlt
          _ = (2 ^ n) ^ 2 := h2.symm
      have hp : 0 < (2 ^ n) ^ 2 := by positivity
      omega
    exact hC (Subgroup.card_eq_one.1 (by omega))

end Action

section Matrix

variable {k : Type*} [Field k]

theorem coe_upperElt' (t : k) :
    ((upperElt k t : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![1, t; 0, 1] := rfl

theorem apply_one_zero_eq_zero {g : SL(2, k)} {s t : k} (ht : t ≠ 0)
    (h : upperElt k t * g = g * upperElt k s) : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
  have h1 := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_upperElt', Matrix.mul_apply,
    Fin.sum_univ_two] at h1
  simp at h1
  rcases h1 with h1 | h1
  · exact absurd h1 ht
  · exact h1

theorem coe_conj_upperElt (g : SL(2, k)) (t : k) :
    ((g * upperElt k t * g⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      !![1 - (g : Matrix (Fin 2) (Fin 2) k) 0 0 * (g : Matrix (Fin 2) (Fin 2) k) 1 0 * t,
        (g : Matrix (Fin 2) (Fin 2) k) 0 0 ^ 2 * t;
        -((g : Matrix (Fin 2) (Fin 2) k) 1 0 ^ 2 * t),
        1 + (g : Matrix (Fin 2) (Fin 2) k) 0 0 * (g : Matrix (Fin 2) (Fin 2) k) 1 0 * t] := by
  obtain ⟨a, b, c, d, h, rfl⟩ := exists_eq_mkSL g
  rw [mkSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_mkSL, coe_upperElt', Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

theorem conj_upper_mem_of_apply_zero {g : SL(2, k)}
    (hg : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) {x : SL(2, k)}
    (hx : x ∈ upperUnipotent k) : g * x * g⁻¹ ∈ upperUnipotent k := by
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff k).1 hx
  rw [mem_upperUnipotent_iff]
  refine ⟨(g : Matrix (Fin 2) (Fin 2) k) 0 0 ^ 2 * t, ?_⟩
  ext i j
  rw [coe_conj_upperElt]
  fin_cases i <;> fin_cases j <;> simp [coe_upperElt', hg]

theorem inv_apply_one_zero {g : SL(2, k)} (hg : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    ((g⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [hg]

end Matrix

section Module

variable {k : Type*} [Field k] [Finite k] [CharP k 2]

theorem natural_module_fixed {m : ℕ} (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m)
    {V : Type*} [CommGroup V] [Finite V] (hV : Nat.card V = (2 ^ m) ^ 2)
    (ρ : SL(2, k) →* MulAut V) (hρ : ρ ≠ 1)
    (hB : 2 ^ m ≤ Nat.card (actionFixed ρ (upperUnipotent k))) :
    Nat.card (actionFixed ρ (upperUnipotent k)) = 2 ^ m ∧
      ∀ u ∈ upperUnipotent k, u ≠ 1 → ∀ v : V, ρ u v = v →
        v ∈ actionFixed ρ (upperUnipotent k) := by
  have hD := actionFixed_top_eq_bot hm hk hV ρ hρ
  have hB' : Nat.card (actionFixed ρ (upperUnipotent k)) = 2 ^ m :=
    le_antisymm (CFSG.LocalAnalysis.EvenBN.U4.card_actionFixed_upperUnipotent_le hV ρ hD) hB
  refine ⟨hB', fun u hu hu1 v huv => ?_⟩
  obtain ⟨-, -, -, -, htrans, hstab, -⟩ :=
    even_linear_two_half_fixed_module_transitivity hk hV ρ hD hB'
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a₀ ∈ actionFixed ρ (upperUnipotent k), a₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : actionFixed ρ (upperUnipotent k) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [hbot, Subgroup.card_bot] at hB'
    have : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  by_cases hv1 : v = 1
  · rw [hv1]
    exact one_mem _
  obtain ⟨g, hg⟩ := htrans a₀ v ha₀1 hv1
  have hinv : ρ g⁻¹ v = a₀ := by
    rw [← hg, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have h1 : ρ (g⁻¹ * u * g) a₀ = a₀ := by
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hg, huv, hinv]
  have hmem : g⁻¹ * u * g ∈ upperUnipotent k := (hstab a₀ ha₀ ha₀1 _).1 h1
  obtain ⟨s₀, hs₀⟩ := (mem_upperUnipotent_iff k).1 hmem
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff k).1 hu
  have ht : t ≠ 0 := by
    rintro rfl
    exact hu1 (upperElt_zero k)
  have h2 : upperElt k t * g = g * upperElt k s₀ := by
    rw [← hs₀]
    group
  have hg10 := apply_one_zero_eq_zero ht h2
  intro s hs
  have h3 : g⁻¹ * s * g ∈ upperUnipotent k := by
    have := conj_upper_mem_of_apply_zero (inv_apply_one_zero hg10) hs
    rwa [inv_inv] at this
  have h4 : ρ (g⁻¹ * s * g) a₀ = a₀ := ha₀ _ h3
  calc ρ s v = ρ (g * (g⁻¹ * s * g)) a₀ := by
        rw [← hg, ← MulAut.mul_apply, ← map_mul]
        congr 2
        group
    _ = v := by rw [map_mul, MulAut.mul_apply, h4, hg]

end Module

section Main

variable {Γ : Type*} [Group Γ] [Finite Γ]

open CFSG.Open

theorem exists_conjAction {E V : Subgroup Γ} (hEV : E ≤ normalizer (V : Set Γ)) {k : Type*}
    [Field k] (φ : ↥E →* SL(2, k)) (hs : Function.Surjective φ) (hker : φ.ker = V.subgroupOf E)
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    ∃ ρ : SL(2, k) →* MulAut ↥V, ∀ (x : ↥E) (e : ↥V), ((ρ (φ x) e : ↥V) : Γ) = x * e * x⁻¹ := by
  let c : ↥E →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hEV)
  have hc : ∀ x e, ((c x e : ↥V) : Γ) = x * e * x⁻¹ := fun x e => rfl
  have hk : φ.ker ≤ c.ker := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    ext e
    rw [hc]
    show (x : Γ) * e * (x : Γ)⁻¹ = e
    have := hcomm _ hx _ e.2
    rw [this, mul_inv_cancel_right]
  let ρ₀ := QuotientGroup.lift φ.ker c hk
  let ι := (QuotientGroup.quotientKerEquivOfSurjective φ hs).symm
  refine ⟨ρ₀.comp ι.toMonoidHom, fun x e => ?_⟩
  have hι : ι (φ x) = (x : ↥E ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hι, ρ₀, QuotientGroup.lift_mk]
  exact hc x e

theorem involution_mem_of_natural_normalized {k : Type*} [Field k] [Finite k] [CharP k 2]
    {m : ℕ} (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) {E V P D : Subgroup Γ} (hVE : V ≤ E)
    (hEV : E ≤ normalizer (V : Set Γ)) (hV : IsElemAbelian 2 V)
    (hVc : Nat.card V = (2 ^ m) ^ 2) (φ : E →* SL(2, k)) (hφ : Function.Surjective φ)
    (hker : φ.ker = V.subgroupOf E) (hPE : P ≤ E)
    (hφP : (P.subgroupOf E).map φ = upperUnipotent k)
    (hfix : 2 ^ m ≤ Nat.card (V ⊓ centralizer (P : Set Γ) : Subgroup Γ))
    (hnc : ¬ E ≤ centralizer (V : Set Γ)) (hD : IsElemAbelian 2 D)
    (hDc : Nat.card D = (2 ^ m) ^ 2) (hDP : D ≤ P) (hDV : D ≠ V) :
    ∀ x ∈ P, x * x = 1 → x ∈ V ∨ x ∈ D := by
  classical
  obtain ⟨hVcomm, hV2⟩ := hV
  obtain ⟨hDcomm, hD2⟩ := hD
  have hVc' : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hDc' : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hDcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← sq]; exact hV2 v hv
  have hDsq : ∀ v ∈ D, v * v = 1 := fun v hv => by rw [← sq]; exact hD2 v hv
  letI : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with mul_comm := fun a b => Subtype.ext (hVc' a a.2 b b.2) }
  obtain ⟨ρ, hρ⟩ := exists_conjAction hEV φ hφ hker hVc'
  set U := upperUnipotent k with hU
  have hρ1 : ρ ≠ 1 := by
    intro h1
    apply hnc
    intro x hx
    rw [mem_centralizer_iff]
    intro v hv
    have := hρ ⟨x, hx⟩ ⟨v, hv⟩
    rw [h1, MonoidHom.one_apply, MulAut.one_apply] at this
    have this' : v = x * v * x⁻¹ := this
    calc v * x = x * v * x⁻¹ * x := by rw [← this']
      _ = x * v := by group
  have hφU : ∀ p (hp : p ∈ P), φ ⟨p, hPE hp⟩ ∈ U := fun p hp => by
    rw [← hφP]
    exact ⟨⟨p, hPE hp⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩
  have hUφ : ∀ s ∈ U, ∃ p, ∃ hp : p ∈ P, φ ⟨p, hPE hp⟩ = s := fun s hs => by
    rw [← hφP] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    exact ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩
  have hfixiff : ∀ w : V, w ∈ actionFixed ρ U ↔ (w : Γ) ∈ centralizer (P : Set Γ) := by
    intro w
    rw [mem_actionFixed, mem_centralizer_iff]
    constructor
    · intro h p hp
      have h5 := congrArg Subtype.val (h _ (hφU p hp))
      rw [hρ] at h5
      have h6 : p * (w : Γ) * p⁻¹ = w := h5
      calc p * w = (p * w * p⁻¹) * p := by group
        _ = w * p := by rw [h6]
    · intro h s hs
      obtain ⟨p, hp, rfl⟩ := hUφ s hs
      apply Subtype.ext
      rw [hρ]
      show p * (w : Γ) * p⁻¹ = w
      calc p * w * p⁻¹ = w * p * p⁻¹ := by rw [h p hp]
        _ = w := by group
  have hmapfix : (actionFixed ρ U).map V.subtype = V ⊓ centralizer (P : Set Γ) := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Subgroup.mem_inf.2 ⟨a.2, (hfixiff a).1 ha⟩
    · intro hy
      obtain ⟨hyV, hyC⟩ := Subgroup.mem_inf.1 hy
      exact ⟨⟨y, hyV⟩, (hfixiff ⟨y, hyV⟩).2 hyC, rfl⟩
  have hcard1 : Nat.card (actionFixed ρ U) =
      Nat.card (V ⊓ centralizer (P : Set Γ) : Subgroup Γ) := by
    rw [← hmapfix, Subgroup.card_map_of_injective V.subtype_injective]
  obtain ⟨hB, hstabfix⟩ := natural_module_fixed hk hm hVc ρ hρ1 (hcard1 ▸ hfix)
  have hCVcard : Nat.card (V ⊓ centralizer (P : Set Γ) : Subgroup Γ) = 2 ^ m := hcard1 ▸ hB
  have claimA : ∀ x ∈ P, x ∉ V → ∀ w ∈ V, x * w = w * x → w ∈ centralizer (P : Set Γ) := by
    intro x hx hxV w hw hxw
    set u := φ ⟨x, hPE hx⟩ with hu
    have hu1 : u ≠ 1 := by
      intro h1
      apply hxV
      have : (⟨x, hPE hx⟩ : E) ∈ φ.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact this
    have hfixw : ρ u ⟨w, hw⟩ = ⟨w, hw⟩ := by
      apply Subtype.ext
      rw [hu, hρ]
      calc x * w * x⁻¹ = w * x * x⁻¹ := by rw [hxw]
        _ = w := by group
    exact (hfixiff ⟨w, hw⟩).1 (hstabfix u (hφU x hx) hu1 _ hfixw)
  obtain ⟨x₀, hx₀D, hx₀V⟩ : ∃ x₀ ∈ D, x₀ ∉ V := by
    by_contra hcon
    push Not at hcon
    exact hDV (Subgroup.eq_of_le_of_card_ge hcon (by rw [hDc, hVc]))
  have hDVle : D ⊓ V ≤ V ⊓ centralizer (P : Set Γ) := by
    intro w hw
    obtain ⟨hwD, hwV⟩ := Subgroup.mem_inf.1 hw
    exact Subgroup.mem_inf.2 ⟨hwV, claimA x₀ (hDP hx₀D) hx₀V w hwV (hDc' x₀ hx₀D w hwD)⟩
  have hDVcard : Nat.card (V ⊓ D : Subgroup Γ) ≤ 2 ^ m := by
    rw [inf_comm]
    exact hCVcard ▸ Subgroup.card_le_of_le hDVle
  have hφD : Nat.card ((D.subgroupOf E).map φ) * Nat.card (V ⊓ D : Subgroup Γ) =
      Nat.card D := by
    rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf (hDP.trans hPE)]
    exact Subgroup.relIndex_mul_card V D
  have hφDU : (D.subgroupOf E).map φ ≤ U :=
    hφP ▸ Subgroup.map_mono (Subgroup.comap_mono hDP)
  have hφDle : Nat.card ((D.subgroupOf E).map φ) ≤ 2 ^ m := by
    have h2 := Subgroup.card_le_of_le hφDU
    rwa [hU, CFSG.Timmesfeld.RankOne.card_upperUnipotent, hk] at h2
  have hpos : 0 < 2 ^ m := by positivity
  have hφDcard : Nat.card ((D.subgroupOf E).map φ) = 2 ^ m := by
    rw [hDc] at hφD
    by_contra hne
    have hlt : Nat.card ((D.subgroupOf E).map φ) < 2 ^ m := lt_of_le_of_ne hφDle hne
    have : Nat.card ((D.subgroupOf E).map φ) * Nat.card (V ⊓ D : Subgroup Γ) <
        2 ^ m * 2 ^ m := by
      calc _ ≤ Nat.card ((D.subgroupOf E).map φ) * 2 ^ m := Nat.mul_le_mul_left _ hDVcard
        _ < 2 ^ m * 2 ^ m := Nat.mul_lt_mul_of_pos_right hlt hpos
    rw [hφD, sq] at this
    exact lt_irrefl _ this
  have hVDcard : Nat.card (V ⊓ D : Subgroup Γ) = 2 ^ m := by
    rw [hDc, hφDcard] at hφD
    have : 2 ^ m * Nat.card (V ⊓ D : Subgroup Γ) = 2 ^ m * 2 ^ m := by rw [hφD, sq]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hφDeq : (D.subgroupOf E).map φ = U :=
    Subgroup.eq_of_le_of_card_ge hφDU (by
      rw [hφDcard, hU, CFSG.Timmesfeld.RankOne.card_upperUnipotent, hk])
  have hVDeq : V ⊓ D = V ⊓ centralizer (P : Set Γ) :=
    Subgroup.eq_of_le_of_card_ge (by rw [inf_comm]; exact hDVle) (by rw [hCVcard, hVDcard])
  intro y hyP hy2
  by_cases hyV : y ∈ V
  · exact Or.inl hyV
  right
  have hyU : φ ⟨y, hPE hyP⟩ ∈ (D.subgroupOf E).map φ := by
    rw [hφDeq]
    exact hφU y hyP
  obtain ⟨xE, hxE, hxφ⟩ := hyU
  have hxD : (xE : Γ) ∈ D := Subgroup.mem_subgroupOf.1 hxE
  have hw : y * (xE : Γ)⁻¹ ∈ V := by
    have : (⟨y, hPE hyP⟩ : E) * xE⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxφ, mul_inv_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at this
    simpa using this
  have hxV : (xE : Γ) ∉ V := by
    intro hxV'
    apply hyV
    have : y = (y * (xE : Γ)⁻¹) * xE := by group
    rw [this]
    exact mul_mem hw hxV'
  have hxx : (xE : Γ) * xE = 1 := hDsq _ hxD
  have hww : (y * (xE : Γ)⁻¹) * (y * (xE : Γ)⁻¹) = 1 := hVsq _ hw
  have hycomm : (xE : Γ) * (y * (xE : Γ)⁻¹) = (y * (xE : Γ)⁻¹) * xE := by
    set w : Γ := y * (xE : Γ)⁻¹ with hwdef
    set x : Γ := (xE : Γ) with hxdef
    have hy : y = w * x := by rw [hwdef]; group
    have key : (w * x) * (w * x) = 1 := by rw [← hy]; exact hy2
    calc x * w = x * w * ((w * x) * (w * x)) := by rw [key, mul_one]
      _ = x * (w * w) * (x * (w * x)) := by group
      _ = (x * x) * (w * x) := by rw [hww, mul_one]; group
      _ = w * x := by rw [hxx, one_mul]
  have hwC := claimA xE (hDP hxD) hxV _ hw hycomm
  have hwD : y * (xE : Γ)⁻¹ ∈ D := by
    have : y * (xE : Γ)⁻¹ ∈ V ⊓ centralizer (P : Set Γ) := Subgroup.mem_inf.2 ⟨hw, hwC⟩
    rw [← hVDeq] at this
    exact (Subgroup.mem_inf.1 this).2
  have hy' : y = (y * (xE : Γ)⁻¹) * xE := by group
  rw [hy']
  exact mul_mem hwD hxD

end Main

end FieldNaturalAux

namespace FieldCase

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem involution_mem_of_natural {k : Type*} [Field k] [Finite k] [CharP k 2] {m : ℕ}
    (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) {E V P D : Subgroup Γ} (hVE : V ≤ E)
    (hEV : E ≤ normalizer (V : Set Γ)) (hV : IsElemAbelian 2 V) (hVc : Nat.card V = (2 ^ m) ^ 2)
    (φ : E →* SL(2, k)) (hφ : Function.Surjective φ) (hker : φ.ker = V.subgroupOf E)
    (hP : IsSylowOf 2 P E)
    (hfix : 2 ^ m ≤ Nat.card (V ⊓ centralizer (P : Set Γ) : Subgroup Γ))
    (hnc : ¬ E ≤ centralizer (V : Set Γ)) (hD : IsElemAbelian 2 D)
    (hDc : Nat.card D = (2 ^ m) ^ 2) (hDP : D ≤ P) (hDV : D ≠ V) :
    ∀ x ∈ P, x * x = 1 → x ∈ V ∨ x ∈ D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hPE : P ≤ E := hP.le
  have hcardQ : Nat.card ((P.subgroupOf E).map φ) = Nat.card k := by
    have h : Nat.card ((Q : Subgroup E).map φ) = Nat.card k :=
      Common.card_sylow_two_eq (MulEquiv.refl SL(2, k)) (Q.mapSurjective hφ)
    rwa [hQ] at h
  obtain ⟨g, hg⟩ := Common.exists_conj_eq_upperUnipotent hk hcardQ
  refine FieldNaturalAux.involution_mem_of_natural_normalized hk hm hVE hEV hV hVc
    ((MulAut.conj g).toMonoidHom.comp φ) ((MulAut.conj g).surjective.comp hφ) ?_ hPE ?_ hfix hnc
    hD hDc hDP hDV
  · rw [MonoidHom.ker_comp_of_injective φ _ (MulAut.conj g).injective]
    exact hker
  · rw [← Subgroup.map_map]
    exact hg

end FieldCase

namespace FieldNaturalAux

section Quotient

open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient (bar proj Bar)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (commutator_mem_iff_proj)

variable {G : Type*} [Group G]

theorem isElemAbelian_bar {A M : Subgroup G} (h : ElemModulo A M) :
    IsElemAbelian 2 (bar A M) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨y₁, hy₁, e₁⟩ := a.2
    obtain ⟨y₂, hy₂, e₂⟩ := b.2
    apply Subtype.ext
    show (a : Bar A) * b = b * a
    rw [← e₁, ← e₂, ← map_mul, ← map_mul, NormalizerQuotient.proj_eq_proj_iff]
    have h1 := (h (y₂ : G)⁻¹ (inv_mem hy₂) (y₁ : G)⁻¹ (inv_mem hy₁)).2
    have e : ((y₁ * y₂ : normalizer (A : Set G)) : G)⁻¹ * ((y₂ * y₁ : normalizer (A : Set G)) : G)
        = ⁅(y₂ : G)⁻¹, (y₁ : G)⁻¹⁆ := by
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact h1
  · obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, NormalizerQuotient.proj_eq_one_iff]
    rw [sq]
    exact (h y hy y hy).1

theorem bar_isSylowOf [Finite G] {A R K : Subgroup G} (hAR : A ≤ R)
    (hK : K ≤ normalizer (A : Set G)) (hRK : IsSylowOf 2 R K) :
    IsSylowOf 2 (bar A R) (bar A K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hp, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hRK
  refine CFSG.ABGLocalTools.isSylowOf_iff.2
    ⟨NormalizerQuotient.bar_mono hle, NormalizerQuotient.isPGroup_bar hp, ?_⟩
  have hRN : R ≤ normalizer (A : Set G) := hle.trans hK
  have h1 := NormalizerQuotient.card_bar_mul hAR hRN
  have h2 := NormalizerQuotient.card_bar_mul (hAR.trans hle) hK
  have h3 := Subgroup.relIndex_mul_card (H := bar A R) (K := bar A K)
  have h4 := Subgroup.relIndex_mul_card (H := R) (K := K)
  rw [inf_of_le_left (NormalizerQuotient.bar_mono hle)] at h3
  rw [inf_of_le_left hle] at h4
  have e : (bar A R).relIndex (bar A K) = R.relIndex K := by
    have hApos : 0 < Nat.card A := Nat.card_pos
    have hRpos : 0 < Nat.card (bar A R) := Nat.card_pos
    have : (bar A R).relIndex (bar A K) * Nat.card (bar A R) * Nat.card A =
        R.relIndex K * Nat.card (bar A R) * Nat.card A := by
      calc _ = Nat.card (bar A K) * Nat.card A := by rw [h3]
        _ = Nat.card K := h2
        _ = R.relIndex K * Nat.card R := h4.symm
        _ = _ := by rw [mul_assoc, h1]
    exact Nat.eq_of_mul_eq_mul_right hRpos (Nat.eq_of_mul_eq_mul_right hApos this)
  rw [e]
  exact hdvd

theorem bar_inj {A X X' : Subgroup G} (hAX : A ≤ X) (hAX' : A ≤ X')
    (hX : X ≤ normalizer (A : Set G)) (hX' : X' ≤ normalizer (A : Set G)) :
    bar A X = bar A X' ↔ X = X' := by
  constructor
  · intro h
    rw [← NormalizerQuotient.lift_bar hAX hX, ← NormalizerQuotient.lift_bar hAX' hX', h]
  · rintro rfl
    rfl

theorem exists_phi_bar {A M N : Subgroup G} (hAM : A ≤ M) (hNA : N ≤ normalizer (A : Set G))
    {k : Type*} [Field k] (π : N →* SL(2, k)) (hπ : Function.Surjective π)
    (hker : π.ker = M.subgroupOf N) :
    ∃ φ : bar A N →* SL(2, k), Function.Surjective φ ∧
      φ.ker = (bar A M).subgroupOf (bar A N) := by
  set N' : Subgroup (normalizer (A : Set G)) := N.subgroupOf (normalizer (A : Set G))
  let β : N' →* ↥(bar A N) := (proj A).subgroupMap N'
  have hβ : Function.Surjective β := (proj A).subgroupMap_surjective N'
  let π' : N' →* SL(2, k) := π.comp (Subgroup.subgroupOfEquivOfLe hNA).toMonoidHom
  have hle : β.ker ≤ π'.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : proj A x.1 = 1 := congrArg Subtype.val hx
    have h2 : (x.1 : G) ∈ A := NormalizerQuotient.proj_eq_one_iff.1 h1
    have h3 : (⟨(x.1 : G), x.2⟩ : N) ∈ π.ker := by
      rw [hker]
      exact Subgroup.mem_subgroupOf.2 (hAM h2)
    exact h3
  let φ : ↥(bar A N) →* SL(2, k) := MonoidHom.liftOfSurjective β hβ ⟨π', hle⟩
  have hφ : ∀ y : normalizer (A : Set G), ∀ hy : (y : G) ∈ N,
      φ ⟨proj A y, ⟨y, hy, rfl⟩⟩ = π ⟨y, hy⟩ := fun y hy => by
    have := MonoidHom.liftOfRightInverse_comp_apply β (Function.surjInv hβ)
      (Function.rightInverse_surjInv hβ) ⟨π', hle⟩ ⟨y, hy⟩
    exact this
  refine ⟨φ, ?_, ?_⟩
  · intro s
    obtain ⟨n, rfl⟩ := hπ s
    exact ⟨⟨proj A ⟨n, hNA n.2⟩, ⟨⟨n, hNA n.2⟩, n.2, rfl⟩⟩, hφ ⟨n, hNA n.2⟩ n.2⟩
  · ext e
    obtain ⟨y, hy, hye⟩ := e.2
    have he : e = ⟨proj A y, ⟨y, hy, rfl⟩⟩ := Subtype.ext hye.symm
    rw [MonoidHom.mem_ker, he, Subgroup.mem_subgroupOf]
    show φ ⟨proj A y, ⟨y, hy, rfl⟩⟩ = 1 ↔ proj A y ∈ bar A M
    rw [hφ y hy, NormalizerQuotient.mem_bar_iff hAM y]
    have : π ⟨y, hy⟩ = 1 ↔ (⟨y, hy⟩ : N) ∈ π.ker := Iff.rfl
    rw [this, hker]
    exact Subgroup.mem_subgroupOf


theorem involution_mem_of_natural_mod {G : Type*} [Group G] [Finite G]
    {k : Type*} [Field k] [Finite k] [CharP k 2] {m : ℕ}
    (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) {W M N P D F : Subgroup G}
    (hWM : W ≤ M) (hMN : M ≤ N) (hNW : N ≤ normalizer (W : Set G))
    (hNM : N ≤ normalizer (M : Set G)) (hMel : ElemModulo W M)
    (hMc : Nat.card M = (2 ^ m) ^ 2 * Nat.card W)
    (π : N →* SL(2, k)) (hπ : Function.Surjective π) (hker : π.ker = M.subgroupOf N)
    (hP : IsSylowOf 2 P N) (hWP : W ≤ P)
    (hWF : W ≤ F) (hFM : F ≤ M) (hFP : ∀ f ∈ F, ∀ p ∈ P, ⁅f, p⁆ ∈ W)
    (hFc : Nat.card F = 2 ^ m * Nat.card W)
    (hnc : ¬ ∀ n ∈ N, ∀ x ∈ M, ⁅x, n⁆ ∈ W)
    (hDel : ElemModulo W D) (hWD : W ≤ D) (hDc : Nat.card D = (2 ^ m) ^ 2 * Nat.card W)
    (hDP : D ≤ P) (hDM : D ≠ M) :
    ∀ x ∈ P, x * x = 1 → x ∈ M ∨ x ∈ D := by
  classical
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hPN : P ≤ N := hP.le
  have hPW : P ≤ normalizer (W : Set G) := hPN.trans hNW
  have hMW : M ≤ normalizer (W : Set G) := hMN.trans hNW
  have hDW : D ≤ normalizer (W : Set G) := hDP.trans hPW
  have hFW : F ≤ normalizer (W : Set G) := hFM.trans hMW
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_bar hWM hNW π hπ hker
  have hVc : Nat.card (bar W M) = (2 ^ m) ^ 2 := by
    have h := NormalizerQuotient.card_bar_mul hWM hMW
    rw [hMc] at h
    exact Nat.eq_of_mul_eq_mul_right hWpos h
  have hDc' : Nat.card (bar W D) = (2 ^ m) ^ 2 := by
    have h := NormalizerQuotient.card_bar_mul hWD hDW
    rw [hDc] at h
    exact Nat.eq_of_mul_eq_mul_right hWpos h
  have hFc' : Nat.card (bar W F) = 2 ^ m := by
    have h := NormalizerQuotient.card_bar_mul hWF hFW
    rw [hFc] at h
    exact Nat.eq_of_mul_eq_mul_right hWpos h
  have hfix : 2 ^ m ≤
      Nat.card (bar W M ⊓ centralizer (bar W P : Set (Bar W)) : Subgroup (Bar W)) := by
    rw [← hFc']
    refine Subgroup.card_le_of_le fun y hy => ?_
    obtain ⟨f, hf, rfl⟩ := hy
    refine Subgroup.mem_inf.2 ⟨NormalizerQuotient.bar_mono hFM ⟨f, hf, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro z ⟨p, hp, rfl⟩
    exact (commutator_mem_iff_proj f.2 p.2).2 (hFP f hf p hp)
  have hnc' : ¬ bar W N ≤ centralizer (bar W M : Set (Bar W)) := by
    intro hE
    apply hnc
    intro n hn x hx
    have hnN : n ∈ normalizer (W : Set G) := hNW hn
    have hxN : x ∈ normalizer (W : Set G) := hMW hx
    have h1 : proj W ⟨n, hnN⟩ ∈ bar W N := NormalizerQuotient.proj_mem_bar hn
    have h2 : proj W ⟨x, hxN⟩ ∈ bar W M := NormalizerQuotient.proj_mem_bar hx
    have h3 := Subgroup.mem_centralizer_iff.1 (hE h1) _ h2
    exact (commutator_mem_iff_proj hxN hnN).1 h3.symm
  have key := FieldCase.involution_mem_of_natural (Γ := Bar W) hk hm
    (NormalizerQuotient.bar_mono hMN) (NormalizerQuotient.bar_le_normalizer_bar hWM hNM)
    (isElemAbelian_bar hMel) hVc φ hφs hφk (bar_isSylowOf hWP hNW hP) hfix hnc'
    (isElemAbelian_bar hDel) hDc' (NormalizerQuotient.bar_mono hDP)
    (fun h => hDM ((bar_inj hWD hWM hDW hMW).1 h))
  intro x hx hx2
  have hxW : x ∈ normalizer (W : Set G) := hPW hx
  have hyy : proj W ⟨x, hxW⟩ * proj W ⟨x, hxW⟩ = 1 := by
    rw [← map_mul]
    have : (⟨x, hxW⟩ * ⟨x, hxW⟩ : normalizer (W : Set G)) = 1 := Subtype.ext hx2
    rw [this, map_one]
  rcases key _ (NormalizerQuotient.proj_mem_bar hx) hyy with h | h
  · exact Or.inl ((NormalizerQuotient.mem_bar_iff hWM ⟨x, hxW⟩).1 h)
  · exact Or.inr ((NormalizerQuotient.mem_bar_iff hWD ⟨x, hxW⟩).1 h)

end Quotient

theorem exists_pi {G : Type*} [Group G] {k : Type*} [Field k] {X CU NC : Subgroup G}
    (hNCN : NC ≤ normalizer (X : Set G))
    (hbar : barSub X NC = normalClosure (barSub X CU : Set (BarM X)))
    (ψ : normalClosure (barSub X CU : Set (BarM X)) ≃* SL(2, k)) :
    ∃ π : NC →* SL(2, k), Function.Surjective π ∧ π.ker = X.subgroupOf NC := by
  let ρ₁ : NC →* normalClosure (barSub X CU : Set (BarM X)) :=
    ((barMap X).comp (Subgroup.inclusion hNCN)).codRestrict _ fun n => by
      rw [← hbar]
      exact ⟨⟨(n : G), hNCN n.2⟩, mem_subgroupOf.mpr n.2, rfl⟩
  have hρ₁surj : Function.Surjective ρ₁ := by
    rintro ⟨x, hx⟩
    rw [← hbar] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨⟨m, mem_subgroupOf.mp hm⟩, Subtype.ext rfl⟩
  refine ⟨ψ.toMonoidHom.comp ρ₁, ψ.surjective.comp hρ₁surj, ?_⟩
  ext n
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  change ψ (ρ₁ n) = 1 ↔ (n : G) ∈ X
  refine (map_eq_one_iff ψ ψ.injective).trans ?_
  rw [Subtype.ext_iff]
  exact CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_one_iff
    (a := ⟨(n : G), hNCN n.2⟩)

end FieldNaturalAux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem field_involution_mem_yamadaM₆_or_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (hsyl : IsSylowOf 2 (yamadaP d t) (yamadaN₂ d t)) {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f)
    (hF : FieldAlternative (yamadaBarK₂ d t) (yamadaT₂ d t) f) :
    ∀ x ∈ yamadaP d t, x * x = 1 → x ∈ yamadaM₆ d t ∨ x ∈ yamadaD₇ d t := by
  classical
  have hf2 : 2 ≤ f := h.two_le
  obtain ⟨hN₂W, -, hcen, -, -, -⟩ := h.yamadaN₂_centers hW d hK hQ hsyl hex
  obtain ⟨-, -, hW₃c, hF₅c, hM₆c, -⟩ := h.yamada_series_card hW d hK hQ
  have hD₇c := h.card_yamadaD₇ hW d hK hQ
  have hY₂W₃ : yamadaY₂ d t ≤ yamadaW₃ d t := (h.yamada_5_46_1 hW d hK hQ).1
  have hU₁W₃ : yamadaU₁ d t ≤ yamadaW₃ d t := (yamadaU₁_le_yamadaY₂ d t).trans hY₂W₃
  have hW₃M₆ : yamadaW₃ d t ≤ yamadaM₆ d t := h.yamadaW₃_le_yamadaM₆ hW d hK hQ
  have hM₆N₂ : yamadaM₆ d t ≤ yamadaN₂ d t := yamadaM₆_le_yamadaN₂ d t
  have hKN : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    (commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) :
        yamadaK₂ d ≤ L ⊓ normalizer (d.Y : Set G)).trans
      (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).2
  have hN₂M₆ : yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) :=
    yamadaN₂_le_normalizer d t hKN
  have hM₆P : yamadaM₆ d t ≤ yamadaP d t := h.yamadaM₆_le_yamadaP hW d hK hQ
  have hD₇P : yamadaD₇ d t ≤ yamadaP d t := yamadaD₇_le_yamadaP d t
  have hW₃D₇ : yamadaW₃ d t ≤ yamadaD₇ d t := h.yamadaW₃_le_yamadaD₇ hW d hK hQ
  have hF₅M₆ : yamadaF₅ d t ≤ yamadaM₆ d t := h.yamadaF₅_le_yamadaM₆ hW d hK hQ
  have hW₃F₅ : yamadaW₃ d t ≤ yamadaF₅ d t := Q44.W₃_le_F₅ d t
  obtain ⟨k₂, _, _, hcard, ψ, -, -⟩ := hF
  have hk₂ : Nat.card k₂ = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm]
  haveI : CharP k₂ 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hk₂
  obtain ⟨π, hπ, hπk⟩ := FieldNaturalAux.exists_pi (CU := yamadaK₂ d) hN₂M₆
    (barSub_yamadaN₂ d t hKN) ψ
  have hq2 : (2 : ℕ) ^ (2 * f) = Nat.card K ^ 2 := by
    rw [hK, ← pow_mul, mul_comm]
  have hq1 : 1 < Nat.card K := hQ.one_lt
  have hMc : Nat.card (yamadaM₆ d t) = (2 ^ (2 * f)) ^ 2 * Nat.card (yamadaW₃ d t) := by
    rw [hM₆c, hW₃c, hq2, ← pow_mul]
    ring
  have hDc : Nat.card (yamadaD₇ d t) = (2 ^ (2 * f)) ^ 2 * Nat.card (yamadaW₃ d t) := by
    rw [hD₇c, hW₃c, hq2, ← pow_mul]
    ring
  have hFc : Nat.card (yamadaF₅ d t) = 2 ^ (2 * f) * Nat.card (yamadaW₃ d t) := by
    rw [hF₅c, hW₃c, hq2]
    ring
  have hnc : ¬ ∀ n ∈ yamadaN₂ d t, ∀ x ∈ yamadaM₆ d t, ⁅x, n⁆ ∈ yamadaW₃ d t := by
    intro hall
    have hW₃N₂ : yamadaW₃ d t ≤ yamadaN₂ d t := hW₃M₆.trans hM₆N₂
    have hM₆W₃ : yamadaM₆ d t ≤ yamadaW₃ d t := by
      intro x hx
      have hxc : x ∈ centerMod (yamadaW₃ d t) (yamadaN₂ d t) :=
        (CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.mem_centerMod_iff hW₃N₂).2
          ⟨hM₆N₂ hx, hN₂W (hM₆N₂ hx), fun a ha _ => hall a ha x hx⟩
      rw [hcen] at hxc
      exact hxc
    have heq : Nat.card (yamadaM₆ d t) = Nat.card (yamadaW₃ d t) := by
      rw [le_antisymm hM₆W₃ hW₃M₆]
    rw [hM₆c, hW₃c] at heq
    have := Nat.pow_right_injective hq1 heq
    omega
  have hDM : yamadaD₇ d t ≠ yamadaM₆ d t := by
    intro hDM
    obtain ⟨-, -, -, -, -, hinf, -⟩ := h.yamada_5_57_2 hW d hK hQ
    rw [hDM, inf_idem] at hinf
    have heq : Nat.card (yamadaM₆ d t) = Nat.card (yamadaF₅ d t) := by rw [hinf]
    rw [hM₆c, hF₅c] at heq
    have := Nat.pow_right_injective hq1 heq
    omega
  exact FieldNaturalAux.involution_mem_of_natural_mod hk₂ (by omega) hW₃M₆ hM₆N₂ hN₂W hN₂M₆
    (h.elemModulo_yamadaM₆ hW d hK hQ |>.mono hY₂W₃) hMc π hπ hπk hsyl (hW₃M₆.trans hM₆P)
    hW₃F₅ hF₅M₆ (fun f hf p hp => hY₂W₃ (h.commutator_yamadaF₅_yamadaP_le hW d hK hQ f hf p hp))
    hFc hnc (h.elemModulo_yamadaD₇ hW d hK hQ |>.mono hU₁W₃) hW₃D₇ hDc hD₇P hDM

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2

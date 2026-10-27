module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzGlueSetting
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigW
public import CFSG.GroupTheory.Commutator.JoinNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Tools46

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_fixedLayer_le_wGroup
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hK : Assembly.KProper Blueprint.Catalog G) {t x : G} {P : Subgroup G} (ht : orderOf t = 2)
    (hPt : P ≤ centralizer ({t} : Set G))
    (hP : IsPComponent 2 (P.subgroupOf (centralizer ({t} : Set G))))
    (hxP : x ∈ P) (hx : orderOf x = 2) (hxt : x ≠ t)
    (hx1 : centralizer ({x} : Set G) ≠ ⊤) (hxt1 : centralizer ({x * t} : Set G) ≠ ⊤) :
    ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤
      ⁅oddIn P, P⁆ ⊓ wGroup (zpowers x ⊔ zpowers t) := by
  have hxtc : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hPt hxP)
  have htx : t * x = x * t := hxtc.symm
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have hx2 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa [pow_two] using h
  have hxHcomm : ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right hxtc j).eq
  have zpowers_pair : ∀ {u : G}, u * u = 1 → ∀ y : G,
      y ∈ Subgroup.zpowers u ↔ y = 1 ∨ y = u := by
    intro u hu2 y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
      · left
        have h2 : u ^ (2 : ℤ) = 1 := by simpa [zpow_natCast, pow_two] using hu2
        rw [hm, _root_.zpow_mul, h2, _root_.one_zpow]
      · right
        have h2 : u ^ (2 : ℤ) = 1 := by simpa [zpow_natCast, pow_two] using hu2
        have h2m : u ^ ((2 : ℤ) * m) = 1 := by
          rw [_root_.zpow_mul, h2, _root_.one_zpow]
        rw [hm, _root_.zpow_add_one, h2m]
        simp
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  have hxn : x ∉ Subgroup.zpowers t := by
    intro hmem
    rcases (zpowers_pair ht2 x).mp hmem with h1 | h1
    · have hxne1 : x ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hx
        norm_num at hx
      exact hxne1 h1
    · exact hxt h1
  obtain ⟨hEelem, hEcard⟩ := GrS5.elemTwo_zpowers_sup hx2 (isElemTwo_zpowers ht2) hxHcomm hxn
  have hE4 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers t) = 4 := by
    rw [hEcard, Nat.card_zpowers, ht]
  have hE2 : ∀ e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers t, e * e = 1 := hEelem.2
  have hBx : ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤
      (pPrimeCore 2 (centralizer ({x} : Set G))).map
        (centralizer ({x} : Set G)).subtype := by
    have h := GrS5.commutator_oddCore_pLayer_le (hS := hS) (hU := hU) (hheld := hheld)
      (hK := hK) (b := t) (e := x) (L := P) ht hPt hP htx hx1
    simpa only [oddIn, gsFixedLayer] using h
  have hPinfC : P ⊓ centralizer ({x} : Set G) = P ⊓ centralizer ({x * t} : Set G) := by
    ext y
    constructor
    · rintro ⟨hyP, hyC⟩
      refine ⟨hyP, ?_⟩
      change y ∈ Subgroup.centralizer ({x} : Set G) at hyC
      change y ∈ Subgroup.centralizer ({x * t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
      have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp (hPt hyP)
      calc y * (x * t) = (y * x) * t := by group
        _ = (x * y) * t := by rw [hyC]
        _ = x * (y * t) := by group
        _ = x * (t * y) := by rw [hyt]
        _ = (x * t) * y := by group
    · rintro ⟨hyP, hyC⟩
      refine ⟨hyP, ?_⟩
      change y ∈ Subgroup.centralizer ({x * t} : Set G) at hyC
      change y ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
      have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp (hPt hyP)
      have h1 : (x * t) * t = x := by rw [mul_assoc, ht2, mul_one]
      calc y * x = y * ((x * t) * t) := by rw [h1]
        _ = (y * (x * t)) * t := by group
        _ = ((x * t) * y) * t := by rw [hyC]
        _ = (x * t) * (y * t) := by group
        _ = (x * t) * (t * y) := by rw [hyt]
        _ = ((x * t) * t) * y := by group
        _ = x * y := by rw [h1]
  have hOx : oddIn P ⊓ centralizer ({x} : Set G) =
      oddIn P ⊓ centralizer ({x * t} : Set G) := by
    have hOle : oddIn P ≤ P := Subgroup.map_subtype_le _
    calc oddIn P ⊓ centralizer ({x} : Set G)
        = (oddIn P ⊓ P) ⊓ centralizer ({x} : Set G) := by rw [inf_eq_left.mpr hOle]
      _ = oddIn P ⊓ (P ⊓ centralizer ({x} : Set G)) := by rw [inf_assoc]
      _ = oddIn P ⊓ (P ⊓ centralizer ({x * t} : Set G)) := by rw [hPinfC]
      _ = (oddIn P ⊓ P) ⊓ centralizer ({x * t} : Set G) := by rw [inf_assoc]
      _ = oddIn P ⊓ centralizer ({x * t} : Set G) := by rw [inf_eq_left.mpr hOle]
  have hgs : gsFixedLayer P x = gsFixedLayer P (x * t) := by
    rw [gsFixedLayer, gsFixedLayer, hPinfC]
  have hBxt : ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤
      (pPrimeCore 2 (centralizer ({x * t} : Set G))).map
        (centralizer ({x * t} : Set G)).subtype := by
    have h := GrS5.commutator_oddCore_pLayer_le (hS := hS) (hU := hU) (hheld := hheld)
      (hK := hK) (b := t) (e := x * t) (L := P) ht hPt hP ?_ hxt1
    · change ⁅oddIn P ⊓ centralizer ({x * t} : Set G), gsFixedLayer P (x * t)⁆ ≤
        (pPrimeCore 2 (centralizer ({x * t} : Set G))).map
          (centralizer ({x * t} : Set G)).subtype at h
      rw [← hOx, ← hgs] at h
      exact h
    · calc t * (x * t) = (t * x) * t := by group
        _ = (x * t) * t := by rw [htx]
  have hOdd : oddIn P ≤ oddIn (centralizer ({t} : Set G)) := by
    rw [oddIn, oddIn, ← CFSG.pPrimeCore_map_subgroupOf (p := 2) P
      (centralizer ({t} : Set G)) hPt]
    exact Subgroup.map_mono (Walter.map_pPrimeCore_le_of_isSubnormal hP.choose_spec.2.1)
  have hcomm_le_Ct : ⁅oddIn P, P⁆ ≤ oddIn (centralizer ({t} : Set G)) := by
    have hcomm := Subgroup.commutator_le_map_commutator
      (f := (centralizer ({t} : Set G)).subtype)
      (H₁ := pPrimeCore 2 (centralizer ({t} : Set G))) (H₂ := ⊤)
      (K₁ := oddIn P) (K₂ := P) hOdd ?_
    · haveI : (pPrimeCore 2 (centralizer ({t} : Set G))).Normal := CFSG.pPrimeCore_normal
      refine hcomm.trans ?_
      exact Subgroup.map_mono (Subgroup.commutator_le_left
        (H₁ := pPrimeCore 2 (centralizer ({t} : Set G))) (H₂ := ⊤))
    · rw [Subgroup.map_top, Subgroup.range_subtype]
      exact hPt
  have hBt : ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤
      (pPrimeCore 2 (centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype := by
    have h := (Subgroup.commutator_mono
      (inf_le_left : oddIn P ⊓ centralizer ({x} : Set G) ≤ oddIn P)
      ((gsFixedLayer_le_inf P x).trans
        (inf_le_left : P ⊓ centralizer ({x} : Set G) ≤ P))).trans hcomm_le_Ct
    simpa only [oddIn] using h
  have hWle : ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤
      wGroup (Subgroup.zpowers x ⊔ Subgroup.zpowers t) := by
    rw [wGroup_eq_iInf_of_four hE4 hE2]
    refine le_iInf fun e => le_iInf fun he => le_iInf fun he1 => ?_
    have hefour : e = 1 ∨ e = x ∨ e = t ∨ e = x * t := by
      obtain ⟨i, h, hh, rfl⟩ :=
        GrS5.mem_zpowers_sup (z := x) (H := Subgroup.zpowers t) hxHcomm he
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hxi : x ^ i = 1 ∨ x ^ i = x :=
        (zpowers_pair hx2 (x ^ i)).mp (Subgroup.zpow_mem_zpowers x i)
      have htj : t ^ j = 1 ∨ t ^ j = t :=
        (zpowers_pair ht2 (t ^ j)).mp (Subgroup.zpow_mem_zpowers t j)
      rcases hxi with hxi | hxi <;> rcases htj with htj | htj
      · exact Or.inl (by rw [hxi, htj]; simp)
      · exact Or.inr (Or.inr (Or.inl (by rw [hxi, htj]; simp)))
      · exact Or.inr (Or.inl (by rw [hxi, htj]; simp))
      · exact Or.inr (Or.inr (Or.inr (by rw [hxi, htj])))
    rcases hefour with rfl | rfl | rfl | rfl
    · exact absurd rfl he1
    · exact hBx
    · exact hBt
    · exact hBxt
  exact le_inf (Subgroup.commutator_mono
      (inf_le_left : oddIn P ⊓ centralizer ({x} : Set G) ≤ oddIn P)
      ((gsFixedLayer_le_inf P x).trans
        (inf_le_left : P ⊓ centralizer ({x} : Set G) ≤ P))) hWle

theorem commutator_oddIn_le_of_kleinFour {P E H W : Subgroup G} (hE : IsKleinFour E)
    (hEP : E ≤ P) (hHP : H ≤ P) (hPW : P ≤ normalizer (W : Set G))
    (hbal : ∀ f ∈ E, f ≠ 1 → ⁅oddIn P ⊓ centralizer ({f} : Set G), H⁆ ≤ W)
    (hnc : ∀ N : Subgroup G, N ≤ P → (N.subgroupOf P).Normal → H ≤ N → N = P) :
    ⁅oddIn P, P⁆ ≤ W := by
  let U : Subgroup G := oddIn P
  let R0 : Subgroup G := W ⊓ U
  have hUP : U ≤ P := Subgroup.map_subtype_le _
  have hEPN : E ≤ normalizer (U : Set G) := hEP.trans (GrS4.le_normalizer_oddIn_self P)
  have hHPN : H ≤ normalizer (U : Set G) := hHP.trans (GrS4.le_normalizer_oddIn_self P)
  have hR0normP : P ≤ normalizer (R0 : Set G) :=
    (le_inf hPW (GrS4.le_normalizer_oddIn_self P)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := W) (K := U))
  have hodd : Odd (Nat.card U) := odd_card_oddIn P
  have hcop : Nat.Coprime 2 (Nat.card U) := Nat.coprime_two_left.mpr hodd
  have hgen : U ≤ ⨆ (f : G) (_ : f ∈ E) (_ : f ≠ 1),
      U ⊓ centralizer ({f} : Set G) :=
    CFSG.ComponentClassification.Sol76.Sig.le_iSup_inf_centralizer_of_isKleinFour
      hE hEPN hcop
  have hgen' : U ≤ ⨆ i : {f : G // f ∈ E ∧ f ≠ 1},
      U ⊓ centralizer ({i.1} : Set G) := by
    refine hgen.trans ?_
    refine iSup_le fun f => iSup_le fun hfE => iSup_le fun hf1 => ?_
    exact le_iSup_of_le ⟨f, hfE, hf1⟩ le_rfl
  have hUH : ⁅U, H⁆ ≤ U :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := H) (K := U)).mp hHPN
  have hUHR0 : ⁅U, H⁆ ≤ R0 := by
    have hsup : ⁅⨆ i : {f : G // f ∈ E ∧ f ≠ 1},
        U ⊓ centralizer ({i.1} : Set G), H⁆ ≤ R0 := by
      refine CFSG.GroupTheory.commutator_iSup_left_le_of_le_normalizer
        (A := fun i : {f : G // f ∈ E ∧ f ≠ 1} =>
          U ⊓ centralizer ({i.1} : Set G)) (Y := H) (N := R0) ?_ ?_
      · intro i
        exact (inf_le_left.trans hUP).trans hR0normP
      · intro i
        exact le_inf (hbal i.1 i.2.1 i.2.2)
          ((Subgroup.commutator_mono inf_le_left le_rfl).trans hUH)
    exact (Subgroup.commutator_mono hgen' le_rfl).trans hsup
  let N0 : Subgroup G :=
    { carrier := {p : G | p ∈ P ∧ ∀ u ∈ U, ⁅u, p⁆ ∈ R0}
      one_mem' := by
        refine ⟨P.one_mem, fun u _ => ?_⟩
        simpa [commutatorElement_def] using R0.one_mem
      mul_mem' := by
        rintro p q ⟨hpP, hp⟩ ⟨hqP, hq⟩
        refine ⟨P.mul_mem hpP hqP, fun u hu => ?_⟩
        have e : ⁅u, p * q⁆ = ⁅u, p⁆ * (p * ⁅u, q⁆ * p⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact R0.mul_mem (hp u hu)
          ((Subgroup.mem_normalizer_iff.mp (hR0normP hpP) _).mp (hq u hu))
      inv_mem' := by
        rintro p ⟨hpP, hp⟩
        refine ⟨P.inv_mem hpP, fun u hu => ?_⟩
        have e : ⁅u, p⁻¹⁆ = p⁻¹ * (⁅u, p⁆)⁻¹ * p := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff''.mp (hR0normP hpP) _).mp
          (R0.inv_mem (hp u hu)) }
  have hN0leP : N0 ≤ P := fun p hp => hp.1
  have hconjN0 : ∀ p ∈ P, ∀ n : G, n ∈ N0 → p * n * p⁻¹ ∈ N0 := by
    intro p hp n ⟨hnP, hn⟩
    refine ⟨P.mul_mem (P.mul_mem hp hnP) (P.inv_mem hp), fun u hu => ?_⟩
    have e : ⁅u, p * n * p⁻¹⁆ = p * ⁅p⁻¹ * u * p, n⁆ * p⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hu' : p⁻¹ * u * p ∈ U :=
      (Subgroup.mem_normalizer_iff''.mp (GrS4.le_normalizer_oddIn_self P hp) u).mp hu
    exact (Subgroup.mem_normalizer_iff.mp (hR0normP hp) _).mp (hn _ hu')
  have hN0normP : P ≤ normalizer (N0 : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hconjN0 p hp n
    · intro hn
      have h := hconjN0 p⁻¹ (P.inv_mem hp) (p * n * p⁻¹) hn
      rwa [show p⁻¹ * (p * n * p⁻¹) * (p⁻¹)⁻¹ = n by group] at h
  have hHN0 : H ≤ N0 := by
    intro h hh
    exact ⟨hHP hh, fun u hu => Subgroup.commutator_le.mp hUHR0 u hu h hh⟩
  have hN0eq : N0 = P :=
    hnc N0 hN0leP ((Subgroup.normal_subgroupOf_iff_le_normalizer hN0leP).mpr hN0normP) hHN0
  refine Subgroup.commutator_le.mpr ?_
  intro u hu p hp
  have hpN0 : p ∈ N0 := hN0eq ▸ hp
  exact (Subgroup.mem_inf.mp (hpN0.2 u hu)).1

end CFSG.ComponentClassification.GrSLit.L34Sec5S

module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdQuot
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdFusion
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdSign
public import CFSG.GH74.GLS.C3.Layer1.EvenSporTransfer

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped commutatorElement

section Sign

attribute [local instance] Classical.decEq Fintype.ofFinite

open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.Generic.S45

variable {X : Type} [Group X] [Finite X]

theorem exists_units_hom_eq_neg_one_of_swap {U : Subgroup X} [U.Normal]
    (hU : Odd (Nat.card U)) {t : X} (ht : t ^ 2 = 1) {K : Subgroup X}
    (hperf : ∀ L : Subgroup X, L ≤ centralizer ({t} : Set X) → ⁅L, L⁆ = L → L ≤ K)
    {Q : Subgroup (X ⧸ U)} (hQ : IsComponent Q)
    (hQt : Q.map (MulAut.conj (QuotientGroup.mk' U t)).toMonoidHom ≠ Q)
    (hKQ : K.map (QuotientGroup.mk' U) ≤
      Q ⊔ Q.map (MulAut.conj (QuotientGroup.mk' U t)).toMonoidHom) :
    ∃ ε : X →* ℤˣ, ε t = -1 := by
  classical
  let π : X →* X ⧸ U := QuotientGroup.mk' U
  let tbar : X ⧸ U := π t
  have htbar : tbar * tbar = 1 := by
    dsimp [tbar]
    simpa [pow_two, map_mul] using congrArg π ht
  have hperfbar : ∀ L : Subgroup (X ⧸ U),
      L ≤ centralizer ({tbar} : Set (X ⧸ U)) → ⁅L, L⁆ = L → L ≤ K.map π := by
    intro L hL hLp
    exact le_map_of_perfect_le_centralizer_quotient hU ht hperf hL hLp
  have hne : conjSub tbar Q ≠ Q := by
    simpa [conjSub, tbar, π] using hQt
  have hKQ' : K.map π ≤ Q ⊔ conjSub tbar Q := by
    simpa [conjSub, tbar, π] using hKQ
  have hfix : ∀ B : Subgroup (X ⧸ U), IsComponent B → B ≠ Q → B ≠ conjSub tbar Q →
      conjSub tbar B = B := by
    intro B hB hBQ hBQt
    exact conjSub_eq_of_perfect_le_sup htbar hQ hne hKQ' hperfbar hB hBQ hBQt
  have hsign := sign_compPermHom_eq_neg_one htbar hQ hne hfix
  let ε : X →* ℤˣ :=
    (@Equiv.Perm.sign (Comp (X ⧸ U)) _ (Fintype.ofFinite _)).comp
      ((compPermHom (X := X ⧸ U)).comp π)
  refine ⟨ε, ?_⟩
  have hεt : ε t = (@Equiv.Perm.sign (Comp (X ⧸ U)) _ (Fintype.ofFinite _))
      (compPermHom tbar) := rfl
  exact hεt.trans hsign

end Sign

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem false_of_units_hom_of_isExtremalIn
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (P : Sylow 2 G) {t z : G}
    (hz : orderOf z = 2) (hzP : z ∈ (P : Subgroup G))
    (hzc : ∀ p ∈ (P : Subgroup G), p * z = z * p) (ht : orderOf t = 2)
    (htP : t ∈ (P : Subgroup G))
    (htx : CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 (P : Subgroup G) t)
    (hZ : ∀ w ∈ (P : Subgroup G) ⊓ centralizer ({t} : Set G),
      (∀ s ∈ (P : Subgroup G) ⊓ centralizer ({t} : Set G), w * s = s * w) → orderOf w = 2 →
        w = z ∨ w = t ∨ w = z * t)
    (hzt : ∀ y : G, y⁻¹ * t * y ≠ z) (hzzt : ∀ y : G, y⁻¹ * (z * t) * y ≠ z)
    (ε : ↥(centralizer ({z} : Set G)) →* ℤˣ) (htC : t ∈ centralizer ({z} : Set G))
    (hεt : ε ⟨t, htC⟩ = -1) : False := by
  classical
  let C : Subgroup G := centralizer ({z} : Set G)
  have hPC : (P : Subgroup G) ≤ C := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hzc p hp).symm
  let εP : ↥P →* ℤˣ := ε.comp (Subgroup.inclusion hPC)
  have hεPt : εP ⟨t, htP⟩ = -1 := by
    have h : (Subgroup.inclusion hPC ⟨t, htP⟩ : ↥C) = ⟨t, htC⟩ := Subtype.ext rfl
    rw [show εP ⟨t, htP⟩ = ε (Subgroup.inclusion hPC ⟨t, htP⟩) from rfl, h, hεt]
  have hsurj : Function.Surjective εP := by
    intro u
    rcases Int.units_eq_one_or u with rfl | hu
    · exact ⟨1, map_one εP⟩
    · rw [hu]
      exact ⟨⟨t, htP⟩, hεPt⟩
  let M : Subgroup G := εP.ker.map (P : Subgroup G).subtype
  have hMP : M ≤ (P : Subgroup G) := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact p.2
  have hindex : εP.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hPtop : (⊤ : Subgroup ↥P).map (P : Subgroup G).subtype = (P : Subgroup G) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hrel : M.relIndex (P : Subgroup G) = 2 := by
    have h := Subgroup.relIndex_map_map_of_injective (f := (P : Subgroup G).subtype)
      εP.ker (⊤ : Subgroup ↥P) (P : Subgroup G).subtype_injective
    rw [hPtop] at h
    rw [h, Subgroup.relIndex_top_right, hindex]
  have htM : t ∉ M := by
    intro htm
    obtain ⟨p, hpker, hpval⟩ := Subgroup.mem_map.mp htm
    have hp1 : εP p = 1 := MonoidHom.mem_ker.mp hpker
    have hpt : p = ⟨t, htP⟩ := Subtype.ext hpval
    rw [hpt, hεPt] at hp1
    have h2 : ((1 : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) := congrArg (fun u : ℤˣ => (u : ℤ)) hp1.symm
    norm_num at h2
  have hmin : ∀ y ∈ (P : Subgroup G), y ∉ M → orderOf t ≤ orderOf y := by
    intro y _ hyM
    have hy1 : y ≠ 1 := by
      rintro rfl
      exact hyM M.one_mem
    have hpos : 0 < orderOf y := orderOf_pos y
    have hne : orderOf y ≠ 1 := fun h1 => hy1 (orderOf_eq_one_iff.mp h1)
    rw [ht]
    omega
  obtain ⟨g, hgM, hgext⟩ := CFSG.EvenSporTransfer.exists_extremal_conj_of_thompson
    (T := (P : Subgroup G)) (U := M) (x := t) (Sylow.isPGroup' P)
    (P.not_dvd_index' (by dsimp [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite))
    hMP hrel htP htM hmin hno
  obtain ⟨x, hxC, hxconj⟩ := exists_mem_centralizer_conj_of_isExtremalIn
    (P := (P : Subgroup G)) (t := t) (z := z) (g := g)
    hzP hzc hz htx hZ hzt hzzt (hMP hgM) hgext
  let v : G := g⁻¹ * t * g
  have hvC : v ∈ C := by
    rw [show v = x⁻¹ * t * x from hxconj.symm]
    exact C.mul_mem (C.mul_mem (C.inv_mem hxC) htC) hxC
  have hCx : (⟨x, hxC⟩ : ↥C)⁻¹ * ⟨t, htC⟩ * ⟨x, hxC⟩ = ⟨v, hvC⟩ := by
    apply Subtype.ext
    exact hxconj
  have hεv : ε ⟨v, hvC⟩ = 1 := by
    obtain ⟨p, hpker, hpval⟩ := Subgroup.mem_map.mp hgM
    have hp1 : εP p = 1 := MonoidHom.mem_ker.mp hpker
    have h : (⟨v, hvC⟩ : ↥C) = Subgroup.inclusion hPC p := Subtype.ext hpval.symm
    rw [h]
    exact hp1
  have hεneg : ε ⟨v, hvC⟩ = -1 := by
    rw [← hCx, map_mul, map_mul, map_inv, hεt]
    rw [mul_comm ((ε ⟨x, hxC⟩)⁻¹) (-1), mul_assoc, inv_mul_cancel, mul_one]
  have h1 : (1 : ℤˣ) = -1 := hεv.symm.trans hεneg
  have h2 : ((1 : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) := congrArg (fun u : ℤˣ => (u : ℤ)) h1
  norm_num at h2

end Transfer

end CFSG.ComponentClassification.GrSLit.L34Sec5S

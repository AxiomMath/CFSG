module

public import CFSG.GH74.Generic.BProg.B2.T4PGVTL2
import CFSG.GH74.GLS.IVK.Proofs2.GHInvStar

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.ComponentClassification.Burgoyne.PSL CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.KGroups.L3Eps CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3 (omega3_equiv_psl2)
open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg.B2 CFSG.GH74.Generic.BProg.B2.PumpupTableBasic
  CFSG.GH74.Generic.BProg.B2.PumpupTableL2 CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3
open scoped MatrixGroups commutatorElement

theorem q3Out_l3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hf : Odd f) :
    Q3EmptyOut (fun X _ => LieModel X .PSL 3 p f) := by
  intro N _ _ H t L hs htH hH
  have hnorm : H.Normal := hs.normal
  have ht2 : t * t = 1 := by
    have := hs.inv
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq this)
  have hst := stated_of_lieModel (Or.inl rfl) hH
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hst
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hFodd : Odd (Nat.card F) := by rw [hF]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hFodd
  have hF2 : ringChar F ≠ 2 := fun h => h2 (by
    have : CharP F 2 := h ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)
  have hF5 : 5 ≤ Nat.card F := by rw [hF]; exact h5
  have h3 : Nat.card F ≠ 3 := by omega
  let c : MulAut ↥H := MulAut.conjNormal t
  have hc2 : c * c = 1 := by
    change MulAut.conjNormal t * MulAut.conjNormal t = 1
    rw [← map_mul, ht2, map_one]
  have hout : c ∉ (inner ↥H : Subgroup (MulAut ↥H)) := fun hin =>
    htH (mem_of_conjNormal_mem_inner H hs.faithful hin)
  have hc2' : conjAutEquiv e c * conjAutEquiv e c = 1 := by
    rw [← conjAutEquiv_mul, hc2, conjAutEquiv_one]
  have hout' : conjAutEquiv e c ∉
      (inner (projectiveSL 3 F) : Subgroup (MulAut (projectiveSL 3 F))) :=
    fun h => hout (conjAutEquiv_mem_inner e h)
  obtain ⟨A, hAs, hA⟩ := lin_involution_form hp hF hf h2 hc2' hout'
  obtain ⟨N0, hq, hfix, hconj, hcomm, ⟨eN⟩⟩ := lin_graph_centralizer_psl2 hF2 h3 hAs
  rw [← hA] at hfix hconj hcomm
  have hfixK : ∀ x : ↥H, c x = x → conjAutEquiv e c (e x) = e x := fun x hx => by
    rw [conjAutEquiv_apply, hx]
  set S : Subgroup ↥H := N0.map (e.symm : projectiveSL 3 F →* ↥H) with hSdef
  have hmemS : ∀ x : ↥H, x ∈ S ↔ e x ∈ N0 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, hx, by simp⟩
  have hSq : IsQuasisimple ↥S :=
    LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap e.symm N0) hq
  set C : Subgroup ↥H := (H ⊓ Subgroup.centralizer ({t} : Set N)).subgroupOf H with hC
  have hmemC : ∀ x : ↥H, x ∈ C ↔ c x = x := by
    intro x
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      change t * (x : N) * t⁻¹ = x
      rw [← hx]
      group
    · intro hx
      refine ⟨x.2, ?_⟩
      have := congrArg Subtype.val hx
      change t * (x : N) * t⁻¹ = x at this
      calc (x : N) * t = (t * (x : N) * t⁻¹) * t := by rw [this]
        _ = t * x := by group
  have hSC : S ≤ C := by
    intro x hx
    rw [hmemC]
    have hx' := (hmemS x).1 hx
    apply e.injective
    have h1 := hfix (e x) hx'
    rw [conjAutEquiv_apply] at h1
    exact h1
  have hSn : ∀ x ∈ C, ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    intro x hx s hs
    rw [hmemS] at hs ⊢
    rw [map_mul, map_mul, map_inv]
    exact hconj (e x) (hfixK x ((hmemC x).1 hx)) (e s) hs
  have hSc : ∀ x ∈ C, ∀ z ∈ C, ⁅x, z⁆ ∈ S := by
    intro x hx z hz
    rw [hmemS, map_commutatorElement]
    exact hcomm (e x) (e z) (hfixK x ((hmemC x).1 hx)) (hfixK z ((hmemC z).1 hz))
  have hB : IsCompIn C (L.subgroupOf H) := by
    have hCH : H ⊓ Subgroup.centralizer ({t} : Set N) ≤ H := inf_le_left
    exact ⟨Subgroup.comap_mono hs.comp.1,
      (CFSG.GH74.GLS.LU.Local.isComponent_subgroupOf_iff' (K := L)
        (M := H ⊓ Subgroup.centralizer ({t} : Set N)) (H := H) hCH).2 hs.comp.2⟩
  have hLS : L.subgroupOf H = S :=
    CFSG.GH74.GLS.IVK.GHInv.eq_of_isCompIn_of_normal_quasisimple hSq hSC hSn hSc hB
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  let eL : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    (Subgroup.subgroupOfEquivOfLe hLH).symm.trans ((MulEquiv.subgroupCongr hLS).trans
      ((MulEquiv.subgroupMap e.symm N0).symm.trans eN))
  exact hs.false_of_psl2 hp hp2 (lieModel_psl2_of_equiv hp hf.pos (by omega) hF eL)

end CFSG.GH74.Generic.BProg.B2.T4.PGV

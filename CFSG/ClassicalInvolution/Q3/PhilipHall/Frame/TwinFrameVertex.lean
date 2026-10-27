module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.Q3T7P24V01
public import CFSG.ClassicalInvolution.Asc77.AscT8T1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace TwinFrame

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

section Elements

variable [Finite G]

theorem isElemAbelian_of_frameData (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) :
    IsElemAbelian 2 (Subgroup.closure ({z, u, t} : Set G)) :=
  Asc77.T8T.isElemAbelian_closure_three h.hz.sq h.hu2 h.ht.sq h.comm_zu (A7Q.Gen.comm_zt hΩ h)
    h.htu.symm

theorem mem_closure_cases (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) {x : G}
    (hx : x ∈ Subgroup.closure ({z, u, t} : Set G)) :
    x = 1 ∨ x = z ∨ x = t ∨ x = z * t ∨ x = u ∨ x = z * u ∨ x = u * t ∨ x = z * u * t := by
  have hzt : z * t = t * z := A7Q.Gen.comm_zt hΩ h
  have hzu : z * u = u * z := h.comm_zu
  have hut : u * t = t * u := h.htu.symm
  have hcl : Subgroup.closure ({z, u, t} : Set G) =
      Subgroup.closure ({z, u} : Set G) ⊔ Subgroup.zpowers t := by
    rw [Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    ext y
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff, or_assoc]
  have hcomm : Commutes (Subgroup.closure ({z, u} : Set G)) (Subgroup.zpowers t) := by
    have hle : Subgroup.closure ({z, u} : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hzt
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hut
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have : Commute a t := Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
    exact (this.zpow_right i).eq
  rw [hcl] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hcomm hx
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.ht.sq) h.ht.ne_one
  rcases T7B.mem_closure_pair h.hz.sq h.hu2 h.hz.ne_one h.hu1 hzu ha with
    rfl | rfl | rfl | rfl <;>
  rcases T7A.eq_one_or_eq_of_mem_zpowers ht2 hb with rfl | rfl <;> simp

end Elements

section VertexZ

variable [Finite G]

theorem commutator_component_modOdd_of_solvable {M : Subgroup G} {z : G}
    (hsub : IsSubnormal M (Subgroup.centralizer ({z} : Set G))) (hsolv : Group.IsSolvable ↥M)
    {L : Subgroup (OddQuot z)} (hL : CFSG.IsComponent L) : ⁅L, modOdd z M⁆ = ⊥ := by
  have hMC : M ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hsub
  exact (CFSG.LocalCores.component_solvable_centralizer
    (Q3.Q3T7P24.isSolvable_modOdd_of_solvable hMC hsolv)
    (Q3.Q3T7P24.isSubnormal_modOdd_of_subnormal hsub)).1 L hL

theorem hyp51At_z (hΩ : HypOmegaGen Ω) (hsolv : ∀ M ∈ Ω, Group.IsSolvable ↥M)
    {K K' J : Subgroup G} {z u t : G} (h : TwinFrameData Ω K K' z u J t) :
    Hyp51At (Subgroup.closure ({z, u, t} : Set G)) z := by
  have hB := isElemAbelian_of_frameData hΩ h
  have hzB : z ∈ Subgroup.closure ({z, u, t} : Set G) := z_mem z u t
  have huB : u ∈ Subgroup.closure ({z, u, t} : Set G) := u_mem z u t
  have hz1 : z ≠ 1 := h.hz.ne_one
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet h.hz h.hK'
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_unique h.hz
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_unique hzK'
  have hKsub := isSubnormal_of_hypOmegaGen hΩ h.mem h.hz
  have hK'sub := isSubnormal_of_hypOmegaGen hΩ h.hK'.1 hzK'
  have hnorm : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ h.hK'.1 h.mem h.hne hzK' h.hz
  obtain ⟨x, hxK, y, hyK', hxy⟩ :=
    Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hnorm h.hu
  have hx' : x ∈ Subgroup.centralizer ({z} : Set G) := hKz hxK
  have hy' : y ∈ Subgroup.centralizer ({z} : Set G) := hK'z hyK'
  have huC : u ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h.comm_zu.symm
  have hno : ∀ L : Subgroup (OddQuot z), CFSG.IsComponent L → MovedByAll
      (Subgroup.closure ({z, u, t} : Set G)) z L → False := by
    intro L hL hmov
    have hxm : oddQuotMk z ⟨u, huC⟩ ∈ modOdd z (Subgroup.closure ({z, u, t} : Set G)) :=
      oddQuotMk_mem_modOdd huB huC
    have hnot := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 huB h.hu1 h.huz huC
    obtain ⟨w, hw, hwne⟩ := hmov _ hxm hnot
    apply hwne
    have hcx : ∀ v ∈ L, v * oddQuotMk z ⟨x, hx'⟩ = oddQuotMk z ⟨x, hx'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk z ⟨x, hx'⟩⁆ ∈ ⁅L, modOdd z K⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd hxK hx')
      rw [commutator_component_modOdd_of_solvable hKsub (hsolv K h.mem) hL, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hcy : ∀ v ∈ L, v * oddQuotMk z ⟨y, hy'⟩ = oddQuotMk z ⟨y, hy'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk z ⟨y, hy'⟩⁆ ∈ ⁅L, modOdd z K'⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd hyK' hy')
      rw [commutator_component_modOdd_of_solvable hK'sub (hsolv K' h.hK'.1) hL,
        Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have e1 : oddQuotMk z ⟨u, huC⟩ = oddQuotMk z ⟨x, hx'⟩ * oddQuotMk z ⟨y, hy'⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hxy
    rw [e1, mul_assoc, ← hcy w hw, ← mul_assoc, ← hcx w hw, mul_assoc]
  exact ⟨fun L₁ L₂ h1 _ m1 _ => (hno L₁ h1 m1).elim, fun L hL hm => (hno L hL hm).elim⟩

end VertexZ

end TwinFrame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

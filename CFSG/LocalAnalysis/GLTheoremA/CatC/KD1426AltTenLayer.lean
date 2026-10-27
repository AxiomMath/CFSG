module

public import CFSG.LocalAnalysis.GLTheoremA.S6.AltFix
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltInner
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426AltTenLayer

variable {Y : Type} [Group Y] [Finite Y]

theorem layer_three_cycle {K : Subgroup Y} (hK : K.Normal)
    (π : ↥K ≃* alternatingGroup (Fin 10)) (a : Y) (σ : alternatingGroup (Fin 10))
    (hσ3 : σ ^ 3 = 1) (hσc : ((σ : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).support.card = 3)
    (hcomm : ∀ k : ↥K, π (KD264Inner.conjKequiv K hK a k) = σ * π k * σ⁻¹) :
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set Y))
        (((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom).map K.subtype) ∧
      GLAPLayer 3 (K ⊓ Subgroup.centralizer ({a} : Set Y)) =
        ((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom).map K.subtype := by
  classical
  set F : Subgroup ↥(alternatingGroup (Fin 10)) := altFix (σ : Equiv.Perm (Fin 10)) with hF
  set π' : ↥K →* ↥(alternatingGroup (Fin 10)) := π.toMonoidHom with hπ'
  have hπinj : Function.Injective π' := π.injective
  have hkerπ : π'.ker = ⊥ := (MonoidHom.ker_eq_bot_iff π').2 hπinj
  set X' : Subgroup ↥K := (Subgroup.centralizer ({a} : Set Y)).subgroupOf K with hX'
  have hX'K : X'.map K.subtype = K ⊓ Subgroup.centralizer ({a} : Set Y) := by
    rw [hX', Subgroup.subgroupOf_map_subtype, inf_comm]
  have hcomm_iff : ∀ k : ↥K, a * (k : Y) = (k : Y) * a ↔ σ * π k = π k * σ := by
    intro k
    have hconj : KD264Inner.conjKequiv K hK a k = k ↔ a * (k : Y) = (k : Y) * a := by
      constructor
      · intro h
        have h2 := congrArg Subtype.val h
        simp only [KD264Inner.conjKequiv_apply] at h2
        calc a * (k : Y) = (a * (k : Y) * a⁻¹) * a := by group
          _ = (k : Y) * a := by rw [h2]
      · intro h
        apply Subtype.ext
        simp only [KD264Inner.conjKequiv_apply]
        rw [h]
        group
    have hinjiff : KD264Inner.conjKequiv K hK a k = k ↔ π (KD264Inner.conjKequiv K hK a k) = π k :=
      ⟨fun h => by rw [h], fun h => π.injective h⟩
    rw [← hconj, hinjiff, hcomm k]
    exact mul_inv_eq_iff_eq_mul
  have hXπ : X'.map π' = Subgroup.centralizer ({σ} : Set ↥(alternatingGroup (Fin 10))) := by
    ext t
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk2 : (k : Y) ∈ Subgroup.centralizer ({a} : Set Y) := hk
      rw [Subgroup.mem_centralizer_iff] at hk2
      have hk' : a * (k : Y) = (k : Y) * a := hk2 a (Set.mem_singleton a)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hcomm_iff k).1 hk'
    · intro ht
      obtain ⟨k, rfl⟩ := π.surjective t
      refine ⟨k, ?_, rfl⟩
      show (k : Y) ∈ Subgroup.centralizer ({a} : Set Y)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hcomm_iff k).2 (Subgroup.mem_centralizer_iff.1 ht σ rfl)
  have hF_comp : GLAPComponent 3 (Subgroup.centralizer ({σ} : Set ↥(alternatingGroup (Fin 10))))
      F := by
    have hcyc : ((σ : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).cycleType = {3} :=
      (card_support_eq_three_iff.1 hσc).cycleType
    exact altFix_isPComponent_cycle (p := 3) Nat.prime_three (by norm_num) hcyc (by norm_num)
      (by norm_num)
  have hF_comp' : GLAPComponent 3 (X'.map π') F := by
    rw [hXπ]
    exact hF_comp
  obtain ⟨L1, hL1, hL1map⟩ := exists_glaPComponent_map_eq (p := 3) Nat.prime_three π' (A := X')
    (by rw [hkerπ, inf_bot_eq, Subgroup.card_bot]; exact Nat.coprime_one_right 3) hF_comp'
  have hL1eq : L1 = F.comap π' := by
    rw [← hL1map, Subgroup.comap_map_eq_self_of_injective hπinj]
  have hker_sub : Nat.Coprime 3 (Nat.card ↥(X' ⊓ K.subtype.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff K.subtype).2 K.subtype_injective, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set Y))
      ((F.comap π').map K.subtype) := by
    rw [← hX'K, ← hL1eq]
    exact glaPComponent_map (p := 3) Nat.prime_three K.subtype hker_sub hL1
  have hupper : GLAPLayer 3 (K ⊓ Subgroup.centralizer ({a} : Set Y)) ≤
      (F.comap π').map K.subtype := by
    unfold GLAPLayer
    apply sSup_le
    intro L hL
    rw [← hX'K] at hL
    obtain ⟨L2, hL2, hL2map⟩ := exists_glaPComponent_map_eq (p := 3) Nat.prime_three K.subtype
      (A := X') hker_sub hL
    have hker_pi : Nat.Coprime 3 (Nat.card ↥(X' ⊓ π'.ker)) := by
      rw [hkerπ, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right 3
    have hc2 := glaPComponent_map (p := 3) Nat.prime_three π' hker_pi hL2
    rw [hXπ] at hc2
    have hEq := altFix_unique_of_component (p := 3) Nat.prime_three (by norm_num) hσ3 hc2
    have hEq1 : L2.map π' = F := hEq.1
    have hL2eq : L2 = F.comap π' := by
      rw [← hEq1, Subgroup.comap_map_eq_self_of_injective hπinj]
    rw [← hL2map, hL2eq]
  refine ⟨hJ, le_antisymm hupper ?_⟩
  unfold GLAPLayer
  exact le_sSup hJ

end CFSG.LocalAnalysis.GLTheoremA.KD1426AltTenLayer

end

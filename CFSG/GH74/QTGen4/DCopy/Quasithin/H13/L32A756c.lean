module

public import CFSG.Quasithin.H13.L32A756c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

namespace Ctx753

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G}

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem θG_eq_one_of_comm_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4) (h13314 : A6.Stmt13_3_14_F4)
    (h1222 : Stmt12_2_2_F4) {u : G} (hu : u ∈ conjClosure V (hz T V))
    (hc : ∀ q ∈ pCoreOf 2 (hz T V), q * u = u * q) : C.θG e u = 1 := by
  by_contra hne
  have hF := C.hF98
  have hUeq : conjClosure V (hz T V) = fsuU T V := C.conjClosure_eq
  set Cq := conjClosure V (hz T V) ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) with hCq
  have hHC : hz T V ≤ Subgroup.normalizer (Cq : Set G) := by
    intro k hk
    rw [← conjSub_eq_self_iff, hCq, conjSub_inf, ← conjSub_centralizer,
      conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ hk),
      conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ hk)]
  have huC : u ∈ Cq := ⟨hu, Subgroup.mem_centralizer_iff.mpr fun q hq => hc q hq⟩
  have hV1C : fsuV1 T V ≤ Cq := le_inf ((inf_le_left : fsuV1 T V ≤ V).trans
    (le_conjClosure V _)) fun z hz => Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (Subgroup.mem_centralizer_iff.mp (pCoreOf_le 2 _ hq) z hz).symm

  have hdec : ∀ v ∈ conjClosure V (hz T V), ∃ c ∈ Cq, C.θG e (c⁻¹ * v) = 1 := by
    intro v hv
    by_cases hv1 : C.θG e v = 1
    · exact ⟨1, one_mem _, by rw [inv_one, one_mul]; exact hv1⟩
    · obtain ⟨k, hk, hkθ⟩ := C.exists_K_θG E hne hv1
      have hkH := C.le_hz hk
      refine ⟨k * u * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hHC hkH) u).mp huC, ?_⟩
      have hcU : k * u * k⁻¹ ∈ conjClosure V (hz T V) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V _ hkH) u).mp hu
      rw [C.θG_mul e (inv_mem hcU) hv, C.θG_inv e hcU, C.θG_conj E hkH hu, hkθ, inv_mul_cancel]

  have hUK : ⁅conjClosure V (hz T V), K⁆ ≤ Cq := by
    rw [Subgroup.commutator_le]
    intro v hv k hk
    have hkH := C.le_hz hk
    obtain ⟨c, hcC, hcv⟩ := hdec v hv
    have hcU : c ∈ conjClosure V (hz T V) := hcC.1
    set u₀ := c⁻¹ * v with hu₀
    have hu₀U : u₀ ∈ conjClosure V (hz T V) := mul_mem (inv_mem hcU) hv
    have hvu : v = c * u₀ := by rw [hu₀]; group

    have hu₀k : u₀ * k * u₀⁻¹ * k⁻¹ ∈ fsuV1 T V := by
      have h1 : C.θG e (k * u₀ * k⁻¹) = C.θG e u₀ := by
        rw [C.θG_conj E hkH hu₀U, hcv, map_one]
      have h2 := C.mem_V1_of_θG E hkH hu₀U h1
      have hcomm : ∀ a ∈ conjClosure V (hz T V), ∀ b ∈ conjClosure V (hz T V), a * b = b * a :=
        fun a ha b hb => F7.isElemAbelian_comm hF.F911_3 ha hb
      have hku : k * u₀⁻¹ * k⁻¹ ∈ conjClosure V (hz T V) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V _ hkH) _).mp (inv_mem hu₀U)
      have e1 : u₀ * k * u₀⁻¹ * k⁻¹ = (u₀⁻¹ * (k * u₀ * k⁻¹))⁻¹ := by
        rw [show u₀ * k * u₀⁻¹ * k⁻¹ = u₀ * (k * u₀⁻¹ * k⁻¹) by group,
          hcomm _ hu₀U _ hku]
        group
      rw [e1]
      exact inv_mem h2
    have hckC : c * k * c⁻¹ * k⁻¹ ∈ Cq := by
      have : k * c⁻¹ * k⁻¹ ∈ Cq := (Subgroup.mem_normalizer_iff.mp (hHC hkH) _).mp (inv_mem hcC)
      rw [show c * k * c⁻¹ * k⁻¹ = c * (k * c⁻¹ * k⁻¹) by group]
      exact mul_mem hcC this
    rw [commutatorElement_def, hvu, ← comm_mul_comm_F4 C.hyp hMod hkH (hUeq ▸ hcU) (hUeq ▸ hu₀U)]
    exact mul_mem hckC (hV1C hu₀k)
  have hUC : conjClosure V (hz T V) ≤ Cq := by
    have := C.comm_eq
    rw [← hUeq] at this
    rw [this]
    exact hUK

  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2_F4 h13322 hMod h1222
  have h41 := lemma14_7_4_one_F4 C.hyp h13322 hMod h13314 hV2
  rw [show A6.g1 T V = hz T V from normalizer_eq_centralizer_of_card_eq_two hF.card_V₁] at h41
  have hb : ⁅V₂, pCoreOf 2 (hz T V)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw q hq
    have hwC : w ∈ Cq := hUC (le_conjClosure V _ (hV2.2.1 hw))
    rw [Subgroup.mem_bot, commutatorElement_def,
      ← Subgroup.mem_centralizer_iff.mp hwC.2 q hq, mul_inv_cancel_right, mul_inv_cancel]
  rw [h41] at hb
  have := hF.card_V₁
  rw [hb, Subgroup.card_bot] at this
  omega

end Ctx753

end CFSG.Quasithin.H13.L32A

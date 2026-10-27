module

public import CFSG.Quasithin.H13.L32AL24
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems143

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem isElemAbelian_fsuU_of_F4 (h : Hyp147 G T L V) (hMod : StmtL32NModule_F4) :
    IsElemAbelian 2 (fsuU T V) := by
  rw [F7.isElemAbelian_iff]
  have hV := (hMod G T L V h.hyp h.fsu).1
  refine ⟨fun x hx y hy => fsuU_comm h hx hy, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, -, v, hv, rfl⟩ := hx
    rw [conj_pow, F7.isElemAbelian_pow_eq_one hV hv]
    group
  | one => simp
  | mul a b ha hb iha ihb =>
    rw [(Commute.mul_pow (fsuU_comm h ha hb) 2), iha, ihb, one_mul]
  | inv a _ iha =>
    rw [inv_pow, iha, inv_one]

theorem mem_u0_iff_F4 (h : Hyp147 G T L V) (hMod : StmtL32NModule_F4) {u : G} :
    u ∈ u0 T V ↔ u ∈ fsuU T V ∧ ∀ k ∈ kz T V, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  rw [mem_u0]
  constructor
  · rintro ⟨hu, -, hk⟩
    refine ⟨hu, fun k hk' => ?_⟩
    have := inv_mem (hk k hk')
    rwa [show (u * k * u⁻¹ * k⁻¹)⁻¹ = k * u * k⁻¹ * u⁻¹ by group] at this
  · rintro ⟨hu, hk⟩
    refine ⟨hu, ?_, fun k hk' => ?_⟩
    · have hV1U : fsuV1 T V ≤ fsuU T V := inf_le_left.trans (le_conjClosure V _)
      exact F8.le_normalizer_of_le (isElemAbelian_fsuU_of_F4 h hMod) hV1U hu
    · have := inv_mem (hk k hk')
      rwa [show (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ by group] at this

theorem hz_le_normalizer_u0_F4 (h : Hyp147 G T L V) (hMod : StmtL32NModule_F4) :
    hz T V ≤ Subgroup.normalizer (u0 T V : Set G) := by
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  have hHN : hz T V = Subgroup.normalizer (fsuV1 T V : Set G) :=
    (normalizer_eq_centralizer_of_card_two hV1).symm
  exact le_normalizer_centralizerMod hHN.le (hHN.le.trans (le_normalizer_conjClosure V _))
    (le_normalizer_oTwoUpper (hz T V))

theorem fsuV1_le_u0_F4 (h : Hyp147 G T L V) (hMod : StmtL32NModule_F4) : fsuV1 T V ≤ u0 T V := by
  intro z hz0
  refine (mem_u0_iff_F4 h hMod).mpr ⟨inf_le_left.trans (le_conjClosure V _) hz0, fun k hk => ?_⟩
  have hkH : k ∈ hz T V := oTwoUpper_le _ hk
  rw [(Subgroup.mem_centralizer_iff.mp hkH z hz0).symm, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

end CFSG.Quasithin.H13.L32A

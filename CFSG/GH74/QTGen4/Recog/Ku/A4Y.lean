module

public import CFSG.GH74.QTGen4.Recog.Ku.A3V2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem orbit_conjL (h : KuHyp G T M H P z) :
    MulAction.orbit (conjM (oTwoUpper M)) z = (pCoreOf 2 M : Set G) \ {1} := by
  ext v
  constructor
  · intro hv
    obtain ⟨c, rfl⟩ := MulAction.mem_orbit_iff.mp hv
    obtain ⟨m, hm, hmc⟩ := Subgroup.mem_map.mp c.2
    have hmc' : ConjAct.toConjAct m = (c : ConjAct G) := hmc
    have hact : c • z = m * z * m⁻¹ := by
      show (c : ConjAct G) • z = _
      rw [← hmc', ConjAct.toConjAct_smul]
    have hmN : m ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      h.oTwoUpper_le_normalizer_V hm
    have hz : z ∈ pCoreOf 2 M := h.z_mem_pCoreOf
    refine ⟨?_, ?_⟩
    · rw [hact]
      exact (Subgroup.mem_normalizer_iff.mp hmN z).mp hz
    · intro hone
      rw [Set.mem_singleton_iff] at hone
      apply h.z_ne_one
      have h1 : m * z * m⁻¹ = 1 := hact.symm.trans hone
      have h2 : m * z = m * 1 := by
        rw [mul_one]
        exact mul_inv_eq_one.mp h1
      exact mul_left_cancel h2
  · rintro ⟨hv, hv1⟩
    obtain ⟨g, hg, hgv⟩ :=
      IsNatModCh5.exists_conj_eq h.mNat h.z_mem_pCoreOf hv h.z_ne_one
        (fun e => hv1 (Set.mem_singleton_iff.mpr e))
    refine MulAction.mem_orbit_iff.mpr
      ⟨⟨ConjAct.toConjAct g, Subgroup.mem_map_of_mem _ hg⟩, ?_⟩
    show (ConjAct.toConjAct g : ConjAct G) • z = v
    rw [ConjAct.toConjAct_smul, hgv]

theorem card_L_inf_centralizer_z (h : KuHyp G T M H P z) :
    Nat.card ↥(oTwoUpper M ⊓ Subgroup.centralizer ({z} : Set G)) = 64 := by
  have hcardS : Nat.card ↥(conjM (oTwoUpper M)) = 960 := by
    rw [conjM, Subgroup.card_map_of_injective
      (f := (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom)
      (ConjAct.toConjAct : G ≃* ConjAct G).injective]
    exact h.card_oTwoUpper
  have hV16 : ((pCoreOf 2 M : Subgroup G) : Set G).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact h.vCard
  have hidx : (MulAction.stabilizer (conjM (oTwoUpper M)) z).index = 15 := by
    rw [MulAction.index_stabilizer, orbit_conjL h,
      Set.ncard_sdiff_singleton_of_mem
        (show (1 : G) ∈ (pCoreOf 2 M : Set G) from (pCoreOf 2 M).one_mem), hV16]
  have hL := Subgroup.card_mul_index (MulAction.stabilizer (conjM (oTwoUpper M)) z)
  rw [hidx, hcardS] at hL
  have hstab : Nat.card ↥(MulAction.stabilizer (conjM (oTwoUpper M)) z) = 64 := by omega
  have hf : Function.Injective (conjMVal (oTwoUpper M)) :=
    (ConjAct.toConjAct : G ≃* ConjAct G).symm.injective.comp Subtype.val_injective
  have hmap : (MulAction.stabilizer (conjM (oTwoUpper M)) z).map (conjMVal (oTwoUpper M)) =
      oTwoUpper M ⊓ Subgroup.centralizer ({z} : Set G) := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hcS : c • z = z := MulAction.mem_stabilizer_iff.mp hc
      obtain ⟨m, hm, hmc⟩ := Subgroup.mem_map.mp c.2
      have hmc' : ConjAct.toConjAct m = (c : ConjAct G) := hmc
      have hfc : conjMVal (oTwoUpper M) c = m := by
        show ConjAct.ofConjAct (c : ConjAct G) = m
        rw [← hmc', ConjAct.ofConjAct_toConjAct]
      rw [hfc]
      have hcS' : m * z * m⁻¹ = z := by
        have : c • z = m * z * m⁻¹ := by
          show (c : ConjAct G) • z = _
          rw [← hmc', ConjAct.toConjAct_smul]
        rw [← this]; exact hcS
      exact ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hcS')⟩
    · rintro ⟨hgL, hgC⟩
      have hcomm : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
      refine ⟨⟨ConjAct.toConjAct g, Subgroup.mem_map_of_mem _ hgL⟩, ?_, ?_⟩
      · show (ConjAct.toConjAct g : ConjAct G) • z = z
        rw [ConjAct.toConjAct_smul]
        exact mul_inv_eq_iff_eq_mul.mpr hcomm
      · show ConjAct.ofConjAct (ConjAct.toConjAct g) = g
        exact ConjAct.ofConjAct_toConjAct g
  have hcardMap : Nat.card ↥(oTwoUpper M ⊓ Subgroup.centralizer ({z} : Set G)) =
      Nat.card ↥(MulAction.stabilizer (conjM (oTwoUpper M)) z) := by
    rw [← hmap, Subgroup.card_map_of_injective hf]
  exact hcardMap.trans hstab

theorem kuR_eq_L_inf_centralizer_z (h : KuHyp G T M H P z) :
    kuR T M = oTwoUpper M ⊓ Subgroup.centralizer ({z} : Set G) := by
  have hle : kuR T M ≤ oTwoUpper M ⊓ Subgroup.centralizer ({z} : Set G) := by
    intro r hr
    exact ⟨hr.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp h.z_mem_kuV2.2 r hr)⟩
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (by rw [h.card_kuR, h.card_L_inf_centralizer_z]))

end KuHyp

end CFSG.GH74.QTGen4.Ku

module

public import CFSG.GH74.QTGen4.Recog.Ku.Orders
public import CFSG.Quasithin.Vol2.Ch6NatMod

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

abbrev conjM (M : Subgroup G) : Subgroup (ConjAct G) :=
  M.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom

abbrev conjMVal (M : Subgroup G) : ↥(conjM M) →* G :=
  ((ConjAct.toConjAct : G ≃* ConjAct G).symm.toMonoidHom).comp (conjM M).subtype

namespace KuHyp

variable {T M H P : Subgroup G} {z : G}

theorem z_ne_one (h : KuHyp G T M H P z) : z ≠ 1 := by
  intro h1
  have hc := h.card_zpowers
  rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc
  norm_num at hc

theorem transitive_V [Finite G] (h : KuHyp G T M H P z) :
    ∀ v ∈ pCoreOf 2 M, v ≠ 1 → ∃ m ∈ M, m * z * m⁻¹ = v := by
  intro v hv hv1
  obtain ⟨g, hg, hgz⟩ :=
    IsNatModCh5.exists_conj_eq h.mNat h.z_mem_pCoreOf hv h.z_ne_one hv1
  exact ⟨g, oTwoUpper_le M hg, hgz⟩

theorem orbit_conjM [Finite G] (h : KuHyp G T M H P z) :
    MulAction.orbit (conjM M) z = (pCoreOf 2 M : Set G) \ {1} := by
  ext v
  constructor
  · intro hv
    obtain ⟨c, rfl⟩ := MulAction.mem_orbit_iff.mp hv
    obtain ⟨m, hm, hmc⟩ := Subgroup.mem_map.mp c.2
    have hmc' : ConjAct.toConjAct m = (c : ConjAct G) := hmc
    have hact : c • z = m * z * m⁻¹ := by
      show (c : ConjAct G) • z = _
      rw [← hmc', ConjAct.toConjAct_smul]
    have hmN : m ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
      rw [← h.mNorm]; exact hm
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
    obtain ⟨m, hm, hmv⟩ :=
      h.transitive_V v hv (fun e => hv1 (Set.mem_singleton_iff.mpr e))
    refine MulAction.mem_orbit_iff.mpr
      ⟨⟨ConjAct.toConjAct m, Subgroup.mem_map_of_mem _ hm⟩, ?_⟩
    show (ConjAct.toConjAct m : ConjAct G) • z = v
    rw [ConjAct.toConjAct_smul, hmv]

theorem card_M_inf_H [Finite G] (h : KuHyp G T M H P z) :
    Nat.card ↥(M ⊓ H) = 128 := by
  have hcardS : Nat.card ↥(conjM M) = 1920 := by
    rw [conjM, Subgroup.card_map_of_injective
      (f := (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom)
      (ConjAct.toConjAct : G ≃* ConjAct G).injective]
    exact h.card_M
  have hV16 : ((pCoreOf 2 M : Subgroup G) : Set G).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact h.vCard
  have hidx : (MulAction.stabilizer (conjM M) z).index = 15 := by
    rw [MulAction.index_stabilizer, orbit_conjM h,
      Set.ncard_sdiff_singleton_of_mem
        (show (1 : G) ∈ (pCoreOf 2 M : Set G) from (pCoreOf 2 M).one_mem), hV16]
  have hL := Subgroup.card_mul_index (MulAction.stabilizer (conjM M) z)
  rw [hidx, hcardS] at hL
  have hstab : Nat.card ↥(MulAction.stabilizer (conjM M) z) = 128 := by omega
  have hf : Function.Injective (conjMVal M) :=
    (ConjAct.toConjAct : G ≃* ConjAct G).symm.injective.comp Subtype.val_injective
  have hmap : (MulAction.stabilizer (conjM M) z).map (conjMVal M) = M ⊓ H := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hcS : c • z = z := MulAction.mem_stabilizer_iff.mp hc
      obtain ⟨m, hm, hmc⟩ := Subgroup.mem_map.mp c.2
      have hmc' : ConjAct.toConjAct m = (c : ConjAct G) := hmc
      have hfc : conjMVal M c = m := by
        show ConjAct.ofConjAct (c : ConjAct G) = m
        rw [← hmc', ConjAct.ofConjAct_toConjAct]
      rw [hfc]
      have hcS' : m * z * m⁻¹ = z := by
        have : c • z = m * z * m⁻¹ := by
          show (c : ConjAct G) • z = _
          rw [← hmc', ConjAct.toConjAct_smul]
        rw [← this]; exact hcS
      refine ⟨hm, ?_⟩
      rw [h.hCz]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hcS')
    · rintro ⟨hgM, hgH⟩
      have hgH' : g ∈ H := hgH
      rw [h.hCz] at hgH'
      have hcomm : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hgH'
      refine ⟨⟨ConjAct.toConjAct g, Subgroup.mem_map_of_mem _ hgM⟩, ?_, ?_⟩
      · show (ConjAct.toConjAct g : ConjAct G) • z = z
        rw [ConjAct.toConjAct_smul]
        exact mul_inv_eq_iff_eq_mul.mpr hcomm
      · show ConjAct.ofConjAct (ConjAct.toConjAct g) = g
        exact ConjAct.ofConjAct_toConjAct g
  have hcardMap : Nat.card ↥(M ⊓ H) = Nat.card ↥(MulAction.stabilizer (conjM M) z) := by
    rw [← hmap, Subgroup.card_map_of_injective hf]
  exact hcardMap.trans hstab

theorem T_eq_inf [Finite G] (h : KuHyp G T M H P z) : T = M ⊓ H := by
  have hle : T ≤ M ⊓ H := le_inf h.tM h.tH
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [h.card_T, h.card_M_inf_H]))

end KuHyp

end CFSG.GH74.QTGen4.Ku

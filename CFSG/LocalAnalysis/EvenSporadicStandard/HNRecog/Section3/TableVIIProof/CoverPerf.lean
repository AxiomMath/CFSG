module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.CoverBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Equiv

open scoped commutatorElement

variable {Y : Type*} [Group Y] [Finite Y] {w : Y} {π : Y →* Perm (Fin 5)}

private lemma tableVII_coverperf_commutator_mul_left_of_central {G : Type*} [Group G] {z s t : G}
    (hz : ∀ x : G, z * x = x * z) : ⁅z * s, t⁆ = ⁅s, t⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_eq_one_iff_mul_comm.mpr (hz t), mul_one]
  rw [hz ⁅s, t⁆, mul_assoc, mul_inv_cancel, mul_one]

private lemma tableVII_coverperf_commutator_mul_right_of_central {G : Type*} [Group G] {t z s : G}
    (hz : ∀ x : G, z * x = x * z) : ⁅t, z * s⁆ = ⁅t, s⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_eq_one_iff_mul_comm.mpr (hz t).symm, one_mul]
  rw [hz ⁅t, s⁆, mul_assoc, mul_inv_cancel, mul_one]

theorem tableVII_cover_no_compl (hC : TableVIICover Y w π) (K : Subgroup Y)
    (hK : K ≤ commutator Y) (hKw : K ⊓ Subgroup.zpowers w = ⊥)
    (hsup : Subgroup.zpowers w ⊔ K = commutator Y) : False := by
  have hwcenter : w ∈ Subgroup.center Y :=
    Subgroup.mem_center_iff.mpr fun y => (tableVII_cover_central hC y).symm
  have hcen : ∀ z ∈ Subgroup.zpowers w, ∀ x : Y, z * x = x * z := by
    intro z hz x
    have hz' : z ∈ Subgroup.center Y := Subgroup.zpowers_le.mpr hwcenter hz
    exact (Subgroup.mem_center_iff.mp hz' x).symm
  haveI hznorm : (Subgroup.zpowers w).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hwcenter)
  have hφker : (π.domRestrict K).ker = ⊥ := by
    rw [MonoidHom.ker_domRestrict, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hmem : (x : Y) ∈ K ⊓ Subgroup.zpowers w := ⟨x.2, hC.ker_eq ▸ hx⟩
    rw [hKw] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hinj : Function.Injective (π.domRestrict K) :=
    (MonoidHom.ker_eq_bot_iff _).mp hφker
  have hker_map : (Subgroup.zpowers w).map π = ⊥ :=
    (Subgroup.map_eq_bot_iff (Subgroup.zpowers w)).mpr (by rw [hC.ker_eq])
  have hKmap : K.map π = alternatingGroup (Fin 5) := by
    have h1 : (commutator Y).map π = alternatingGroup (Fin 5) := by
      rw [tableVII_cover_comm_eq hC, Subgroup.map_comap_eq_self_of_surjective hC.surj]
    have h2 : (commutator Y).map π = K.map π := by
      rw [← hsup, Subgroup.map_sup, hker_map, bot_sup_eq]
    exact h2.symm.trans h1
  have hKperf_le : ⁅K, K⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hg₁ hg₂) (K.inv_mem hg₁)) (K.inv_mem hg₂)
  have hK_le_perf : K ≤ ⁅K, K⁆ := by
    intro k hk
    have hcommmap : (⁅K, K⁆).map π = alternatingGroup (Fin 5) := by
      rw [Subgroup.map_commutator, hKmap]
      exact commutator_alternatingGroup_eq_self (by simp)
    have hπk : π k ∈ (⁅K, K⁆).map π := by
      rw [hcommmap, ← hKmap]
      exact ⟨k, hk, rfl⟩
    obtain ⟨k', hk', hk'eq⟩ := Subgroup.mem_map.mp hπk
    have hmem : k' * k⁻¹ ∈ K ⊓ Subgroup.zpowers w := by
      refine ⟨K.mul_mem (hKperf_le hk') (K.inv_mem hk), ?_⟩
      rw [← hC.ker_eq]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hk'eq]; group)
    rw [hKw] at hmem
    have h1 : k' * k⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    have h2 : k' = k := mul_inv_eq_one.mp h1
    rwa [h2] at hk'
  have hKperf : ⁅K, K⁆ = K := le_antisymm hKperf_le hK_le_perf
  have hcomm_comm_le : ⁅commutator Y, commutator Y⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    rw [← hsup] at hu hv
    change u ∈ (↑(Subgroup.zpowers w ⊔ K) : Set Y) at hu
    change v ∈ (↑(Subgroup.zpowers w ⊔ K) : Set Y) at hv
    rw [Subgroup.normal_mul (N := Subgroup.zpowers w) (H := K)] at hu hv
    obtain ⟨a, ha, k, hk, rfl⟩ := Set.mem_mul.mp hu
    obtain ⟨b, hb, k', hk', rfl⟩ := Set.mem_mul.mp hv
    rw [tableVII_coverperf_commutator_mul_left_of_central (hcen a ha),
      tableVII_coverperf_commutator_mul_right_of_central (hcen b hb)]
    exact hKperf_le (Subgroup.commutator_mem_commutator hk hk')
  have hKeq : K = ⁅commutator Y, commutator Y⁆ := by
    refine le_antisymm ?_ hcomm_comm_le
    calc K = ⁅K, K⁆ := hKperf.symm
      _ ≤ ⁅commutator Y, commutator Y⁆ := Subgroup.commutator_mono hK hK
  have hKnormal : K.Normal := by
    rw [hKeq]
    infer_instance
  have hKcard : Nat.card K = 60 := by
    calc Nat.card K = Nat.card (π.domRestrict K).range :=
          Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      _ = Nat.card (K.map π) := by rw [MonoidHom.domRestrict_range]
      _ = Nat.card (alternatingGroup (Fin 5)) := by rw [hKmap]
      _ = 60 := tableVII_perm_card_alternating
  haveI : K.Normal := hKnormal
  have hqcard : Nat.card (Y ⧸ K) = 4 := by
    have h := (Subgroup.card_eq_card_quotient_mul_card_subgroup K).symm
    rw [tableVII_cover_card hC, hKcard] at h
    omega
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hqcomm : IsMulCommutative (Y ⧸ K) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hqcard]; norm_num)
  have hcomm_le : commutator Y ≤ K :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hqcomm
  have hwK : w ∈ K := hcomm_le (hC.le_comm (Subgroup.mem_zpowers w))
  have hwbot : w ∈ (⊥ : Subgroup Y) := by
    have : w ∈ K ⊓ Subgroup.zpowers w := ⟨hwK, Subgroup.mem_zpowers w⟩
    rwa [hKw] at this
  exact hC.ne_one (Subgroup.mem_bot.mp hwbot)

end CFSG.EvenSporadicStandard.HNRecog.Section3

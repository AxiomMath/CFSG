module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeM10

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier

@[expose] noncomputable def ruThreeGamma : Subgroup (Equiv.Perm (Fin 4060) × Equiv.Perm (Fin 11)) :=
  closure (prodGens 4060 11 ruThreeC0Gens ruThreeM '' {k | k < ruThreeC0Gens.size})

theorem ruThreeM_size : ruThreeM.size = ruThreeC0Gens.size := by
  simp [ruThreeM, ruThreeC0Gens]

theorem map_fst_ruThreeGamma : ruThreeGamma.map (MonoidHom.fst _ _) = ruThreeC0 := by
  rw [ruThreeGamma, MonoidHom.map_closure, ruThreeC0, Set.image_image]
  rfl

theorem map_snd_ruThreeGamma : ruThreeGamma.map (MonoidHom.snd _ _) = ruThreeT := by
  rw [ruThreeGamma, MonoidHom.map_closure, ruThreeT, Set.image_image, ← ruThreeM_size]
  rfl

theorem ruThreeGamma_spec :
    (∀ x, x ∈ ruThreeGamma ↔ ∃ i < ruThreeGraphCert.pts.size,
      prodDec 4060 11 ruThreeGraphCert.pts[i]! = x) ∧
    Nat.card ruThreeGamma = 2160 := by
  have h := prodOK_spec ruThreeKeys_lt ruThree_graph_check.1
  exact ⟨h.1, h.2.trans ruThree_graph_check.2.1⟩

theorem ruThree_gens_valid {k : ℕ} (hk : k < ruThreeC0Gens.size) :
    validA 4060 ruThreeC0Gens[k]! = true ∧ validA 11 ruThreeM[k]! = true := by
  have h := ruThree_graph_check.1
  simp only [prodOK, Bool.and_eq_true] at h
  have := allLt_spec h.1.2 hk
  simpa [Bool.and_eq_true] using this

theorem ruThreeX0_mem_C0 :
    ruThreeLine 0 ∈ ruThreeC0 := by
  have hlt : 0 < ruThreeC0Gens.size := by simp [ruThreeC0Gens]
  have h0 : permOfArr 4060 ruThreeC0Gens[0]! = ruThreeLine 0 :=
    eq_of_eqA (rep_of_validA (enumOK_gens_valid (centOKP_enum ruThree_case0_check.2.2.2.2.1) hlt))
      (rep_ruThreeLine 0) ruThree_case0_check.2.2.2.2.2.1
  rw [← h0]
  exact subset_closure (mem_permsA hlt)

theorem ruThree_pair_mem :
    (ruThreeLine 0, (1 : Equiv.Perm (Fin 11))) ∈ ruThreeGamma := by
  have hlt : 0 < ruThreeC0Gens.size := by simp [ruThreeC0Gens]
  have h0 : permOfArr 4060 ruThreeC0Gens[0]! = ruThreeLine 0 :=
    eq_of_eqA (rep_of_validA (ruThree_gens_valid hlt).1) (rep_ruThreeLine 0)
      ruThree_case0_check.2.2.2.2.2.1
  have hm : permOfArr 11 ruThreeM[0]! = 1 :=
    eq_of_eqA (rep_of_validA (ruThree_gens_valid hlt).2) rep_idA ruThree_graph_check.2.2.2
  have := subset_closure (Set.mem_image_of_mem (prodGens 4060 11 ruThreeC0Gens ruThreeM)
    (show 0 ∈ {k | k < ruThreeC0Gens.size} from hlt))
  rwa [prodGens, h0, hm] at this

theorem exists_ruThreeHom0 :
    ∃ φ : ↥ruThreeC0 →* Equiv.Perm (Fin 11), φ.range = ruThreeT ∧
      φ.ker = (zpowers (ruThreeLine 0)).subgroupOf ruThreeC0 := by
  obtain ⟨hmem, hcard⟩ := ruThreeGamma_spec
  have hcard' : Nat.card ruThreeGamma = Nat.card ruThreeC0 := by rw [hcard, ruThreeC0_spec.2]
  obtain ⟨φ, hφ1, hφ2, hφr⟩ := exists_graph_hom ruThreeGamma ruThreeC0 map_fst_ruThreeGamma hcard'
  refine ⟨φ, hφr.trans map_snd_ruThreeGamma, ?_⟩
  ext a
  simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro ha
    have hΓ : ((a : Equiv.Perm (Fin 4060)), (1 : Equiv.Perm (Fin 11))) ∈ ruThreeGamma := by
      simpa [ha] using hφ1 a
    obtain ⟨i, hi, hdec⟩ := (hmem _).1 hΓ
    have hk := allLt_spec ruThree_graph_check.2.2.1 hi
    have hv : prodValid 4060 11 ruThreeGraphCert.pts[i]! = true := by
      have h := ruThree_graph_check.1
      simp only [prodOK, Bool.and_eq_true] at h
      exact arrCertOK_valid h.2 hi
    simp only [prodValid, Bool.and_eq_true] at hv
    have hr1 := rep_of_validA hv.1
    have hr2 := rep_of_validA hv.2
    simp only [prodDec, Prod.mk.injEq] at hdec
    have h2 : eqA 11 (blk2 4060 11 ruThreeGraphCert.pts[i]!) (idA 11) = true :=
      (eqA_iff hr2 rep_idA).2 hdec.2
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hk
    rcases hk with ((hk | hk) | hk) | hk
    · rw [h2] at hk
      exact absurd hk (by simp)
    · rw [← hdec.1, (eqA_iff hr1 rep_idA).1 hk]
      exact one_mem _
    · rw [← hdec.1, (eqA_iff hr1 (rep_ruThreeLine 0)).1 hk]
      exact mem_zpowers _
    · rw [← hdec.1, (eqA_iff hr1 (rep_compA (rep_ruThreeLine 0) (rep_ruThreeLine 0))).1 hk]
      exact mul_mem (mem_zpowers _) (mem_zpowers _)
  · intro ha
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 ha
    have hX : φ ⟨ruThreeLine 0, ruThreeX0_mem_C0⟩ = 1 := hφ2 _ _ ruThree_pair_mem
    have : a = (⟨ruThreeLine 0, ruThreeX0_mem_C0⟩ : ruThreeC0) ^ k := Subtype.ext (by simp [← hk])
    rw [this, map_zpow, hX, one_zpow]

theorem exists_ruThreeHom :
    ∃ φ : ↥ruThreeC0 →* M10, Function.Surjective φ ∧
      φ.ker = (zpowers (ruThreeLine 0)).subgroupOf ruThreeC0 := by
  obtain ⟨φ0, hrange, hker⟩ := exists_ruThreeHom0
  have hrange' : φ0.range = M10emb.range := hrange.trans range_M10emb.symm
  let φ1 : ↥ruThreeC0 →* M10emb.range :=
    φ0.codRestrict M10emb.range fun c => hrange' ▸ ⟨c, rfl⟩
  let e : M10 ≃* M10emb.range := MonoidHom.ofInjective M10emb_injective
  refine ⟨e.symm.toMonoidHom.comp φ1, ?_, ?_⟩
  · intro m
    have hm : M10emb m ∈ φ0.range := hrange' ▸ ⟨m, rfl⟩
    obtain ⟨c, hc⟩ := hm
    refine ⟨c, ?_⟩
    have : φ1 c = e m := Subtype.ext hc
    simp [this]
  · rw [← hker]
    ext c
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.map_eq_one_iff e.symm]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end CFSG.EvenSporadicStandard.RuStd.S2

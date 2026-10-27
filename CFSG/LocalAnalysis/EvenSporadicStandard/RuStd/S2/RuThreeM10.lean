module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInv

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.RankThree.Native

@[expose] noncomputable def M10emb : M10 →* Equiv.Perm (Fin 11) :=
  NativeSporadic.M11.subtype.comp (MulAction.stabilizer ↥NativeSporadic.M11 (0 : Fin 11)).subtype

theorem M10emb_injective : Function.Injective M10emb :=
  NativeSporadic.M11.subtype_injective.comp (Subgroup.subtype_injective _)

@[expose] noncomputable def ruThreeT : Subgroup (Equiv.Perm (Fin 11)) :=
  closure (permsA 11 ruThreeM)

theorem rep_ruThreeM11_zero : CFSG.Monster.B.Co2.Rep 11 ruThreeM11[0]!
    (List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] *
      List.formPerm [7, 8]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_ruThreeM11_one : CFSG.Monster.B.Co2.Rep 11 ruThreeM11[1]!
    (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem M11_eq_closure : NativeSporadic.M11 = closure (permsA 11 ruThreeM11) := by
  have h : permsA 11 ruThreeM11 =
      {(List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] *
        List.formPerm [7, 8]), (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8])} := by
    ext g
    simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    have hsz : ruThreeM11.size = 2 := rfl
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [hsz] at hk
      interval_cases k
      · exact Or.inl (CFSG.RankThree.Native.permOfArr_eq_of_rep rep_ruThreeM11_zero)
      · exact Or.inr (CFSG.RankThree.Native.permOfArr_eq_of_rep rep_ruThreeM11_one)
    · rintro (rfl | rfl)
      · exact ⟨0, by rw [hsz]; norm_num,
          CFSG.RankThree.Native.permOfArr_eq_of_rep rep_ruThreeM11_zero⟩
      · exact ⟨1, by rw [hsz]; norm_num,
          CFSG.RankThree.Native.permOfArr_eq_of_rep rep_ruThreeM11_one⟩
  rw [h]
  rfl

theorem ruThreeKeys11_lt : ∀ q ∈ ruThreeKeys11, q < 11 := by decide

theorem ruThreeM11_enum :
    enumOK 11 ruThreeM11 ruThreeKeys11 ruThreeM11Cert = true :=
  ruThree_M10_check.1

theorem ruThreeT_enum :
    enumOK 11 ruThreeM ruThreeKeys11 ruThreeTCert = true :=
  ruThree_M10_check.2.1

theorem range_M10emb : M10emb.range = ruThreeT := by
  obtain ⟨-, -, hstab, hcover, -, -⟩ := ruThree_M10_check
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    obtain ⟨⟨g, hg⟩, hs⟩ := m
    have hg0 : g 0 = 0 := by
      have := MulAction.mem_stabilizer_iff.1 hs
      simpa [Subgroup.smul_def] using this
    have hg' : g ∈ closure (permsA 11 ruThreeM11) := M11_eq_closure ▸ hg
    obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep ruThreeKeys11_lt ruThreeM11_enum hg'
    have hi0 : (ruThreeM11Cert.pts[i]!)[0]! = 0 := by
      rw [hrep.apply (by norm_num : 0 < 11)]
      exact congrArg Fin.val hg0
    have hc := allLt_spec hcover hi
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hc
    rcases hc with hc | hc
    · exact absurd hi0 hc
    · exact enumOK_mem_of_any ruThreeKeys11_lt ruThreeT_enum hrep hc
  · rw [ruThreeT, closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' := allLt_spec hstab hk
    simp only [Bool.and_eq_true, beq_iff_eq] at hk'
    have hval : validA 11 ruThreeM[k]! = true := enumOK_gens_valid ruThreeT_enum hk
    have hrep := rep_of_validA hval
    have hmem : permOfArr 11 ruThreeM[k]! ∈ NativeSporadic.M11 := by
      rw [M11_eq_closure]
      exact enumOK_mem_of_any ruThreeKeys11_lt ruThreeM11_enum hrep hk'.1
    have h0 : permOfArr 11 ruThreeM[k]! 0 = 0 := by
      have h := hrep.apply (by norm_num : 0 < 11)
      apply Fin.ext
      exact h.symm.trans hk'.2
    refine ⟨⟨⟨_, hmem⟩, ?_⟩, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    simpa [Subgroup.smul_def] using h0

theorem exists_M10emb_eq {t : Equiv.Perm (Fin 11)}
    (ht : t ∈ ruThreeT) : ∃ m : M10, M10emb m = t := by
  rw [← range_M10emb] at ht
  exact ht

theorem center_M10_eq_bot : Subgroup.center M10 = ⊥ := by
  obtain ⟨-, -, -, -, hcenter, -⟩ := ruThree_M10_check
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply M10emb_injective
  rw [map_one]
  have hZT : M10emb z ∈ ruThreeT := by rw [← range_M10emb]; exact ⟨z, rfl⟩
  obtain ⟨k, hk, hkZ⟩ := enumOK_exists_rep ruThreeKeys11_lt ruThreeT_enum hZT
  have hall : (allLt ruThreeM.size fun l => commA 11 ruThreeTCert.pts[k]! ruThreeM[l]!) =
      true := by
    rw [allLt_iff]
    intro l hl
    have hval : validA 11 ruThreeM[l]! = true := enumOK_gens_valid ruThreeT_enum hl
    have hgT : permOfArr 11 ruThreeM[l]! ∈ ruThreeT := subset_closure (mem_permsA hl)
    obtain ⟨m, hm⟩ := exists_M10emb_eq hgT
    refine (commA_iff hkZ (rep_of_validA hval)).2 ?_
    rw [← hm, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz m).symm]
  have hc := allLt_spec hcenter hk
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hc
  rcases hc with hc | hc
  · rw [hall] at hc
    exact absurd hc (by simp)
  · exact (eqA_iff hkZ rep_idA).1 hc

theorem M10_no_odd_normal (K : Subgroup M10) [K.Normal]
    (hodd : Odd (Nat.card K)) : K = ⊥ := by
  obtain ⟨-, -, -, -, -, hoddOK⟩ := ruThree_M10_check
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  by_contra hk1
  have hinv : ∃ t ∈ K, orderOf t = 2 := by
    have hκT : M10emb k ∈ ruThreeT := by rw [← range_M10emb]; exact ⟨k, rfl⟩
    obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep ruThreeKeys11_lt ruThreeT_enum hκT
    have hc := allLt_spec hoddOK hi
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at hc
    rcases hc with (hc | ⟨e, -, hinvE⟩) | ⟨a, ha, hinva⟩
    · exact absurd (M10emb_injective (((eqA_iff hrep rep_idA).1 hc).trans (map_one _).symm)) hk1
    · refine ⟨k ^ e, K.pow_mem hk e, ?_⟩
      rw [← orderOf_injective M10emb M10emb_injective, map_pow]
      exact orderOf_eq_two_of_invA (rep_powArr hrep e) hinvE
    · obtain ⟨j, hj, hja⟩ := List.getElem_of_mem ha
      have hj' : j < ruThreeTCert.pts.size := by simpa using hj
      have haeq : ruThreeTCert.pts[j]! = a := by
        rw [getElem!_pos ruThreeTCert.pts j hj', ← hja]
        simp
      have hjval : validA 11 a = true :=
        haeq ▸ (enumOK_spec ruThreeKeys11_lt ruThreeT_enum).2.2 j hj'
      have hjT : permOfArr 11 a ∈ ruThreeT :=
        enumOK_mem_of_mem ruThreeKeys11_lt ruThreeT_enum (rep_of_validA hjval) ha
      obtain ⟨g, hg⟩ := exists_M10emb_eq hjT
      refine ⟨k * (g * k * g⁻¹), K.mul_mem hk (Subgroup.Normal.conj_mem inferInstance k hk g), ?_⟩
      rw [← orderOf_injective M10emb M10emb_injective, map_mul, map_mul, map_mul, map_inv, hg]
      have := orderOf_eq_two_of_invA (rep_compA hrep (rep_conjA hjval hrep)) hinva
      rwa [CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_of_validA hjval)] at this
  obtain ⟨t, htK, ht2⟩ := hinv
  have hdvd := Subgroup.orderOf_dvd_natCard K htK
  rw [ht2] at hdvd
  obtain ⟨j, hj⟩ := hodd
  omega

end CFSG.EvenSporadicStandard.RuStd.S2

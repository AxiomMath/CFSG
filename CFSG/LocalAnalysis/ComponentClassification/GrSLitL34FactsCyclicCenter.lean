module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicCenterModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs47C

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem l34CyclicCenterSylowFact :
    L34CyclicCenterSylowFact := by
  intro G _ _ J P hJ hL hP hcyc h4 a ha hao
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hJ hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨ζe, -⟩ := exists_zeta hP hqker
  have hkcyc : IsCyclic q.ker := isCyclic_of_surjective ζe.toMonoidHom ζe.surjective
  have hk4 : Nat.card q.ker = 4 := by rw [← Nat.card_congr ζe.toEquiv, h4]
  obtain ⟨g, -, hg⟩ := cyclic_four hk4
  obtain ⟨haP, haZ⟩ := mem_inf.mp ha
  have hâk : jq J ⟨a, hP.1 haP⟩ ∈ q.ker := by
    rw [hqker]
    exact (mem_zStarIn_iff _).1 haZ
  have ha2 : a * a = 1 := by rw [← pow_two, ← hao, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hao
    exact absurd hao (by norm_num)
  have hmulP : ∀ {u v : G} (hu : u ∈ P) (hv : v ∈ P),
      jq J ⟨u * v, hP.1 (P.mul_mem hu hv)⟩ = jq J ⟨u, hP.1 hu⟩ * jq J ⟨v, hP.1 hv⟩ :=
    fun hu hv => by rw [← map_mul]; rfl
  have hâ2 : jq J ⟨a, hP.1 haP⟩ * jq J ⟨a, hP.1 haP⟩ = 1 := by
    rw [← hmulP haP haP]
    have : (⟨a * a, hP.1 (P.mul_mem haP haP)⟩ : J) = 1 := Subtype.ext ha2
    rw [this, map_one]
  have hâ1 : jq J ⟨a, hP.1 haP⟩ ≠ 1 := fun h => ha1 (eq_one_of_jq_eq_one hP.1 hP2 haP h)
  have hâg : (⟨_, hâk⟩ : q.ker) = g * g := by
    rcases (hg ⟨_, hâk⟩).1.1 (Subtype.ext hâ2) with h | h
    · exact absurd (congrArg Subtype.val h) hâ1
    · exact h
  have hk1 : ∀ d ∈ q.ker, d * d = 1 → d = 1 ∨ d = jq J ⟨a, hP.1 haP⟩ := by
    intro d hd hd2
    rcases (hg ⟨d, hd⟩).1.1 (Subtype.ext hd2) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · rw [← hâg] at h
      exact Or.inr (congrArg Subtype.val h)
  have hk2 : ∀ d ∈ q.ker, d * d = 1 ∨ d * d = jq J ⟨a, hP.1 haP⟩ := by
    intro d hd
    rcases (hg ⟨d, hd⟩).2 with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · rw [← hâg] at h
      exact Or.inr (congrArg Subtype.val h)
  have hza : ∀ {c : G} (hc : c ∈ P),
      jq J ⟨c, hP.1 hc⟩ = 1 ∨ jq J ⟨c, hP.1 hc⟩ = jq J ⟨a, hP.1 haP⟩ → c ∈ zpowers a := by
    intro c hc h
    rcases h with h | h
    · rw [eq_one_of_jq_eq_one hP.1 hP2 hc h]
      exact one_mem _
    · rw [eq_of_jq_eq hP.1 hP2 hc haP h]
      exact mem_zpowers a
  have hTP : ∀ {u : G} (hu : u ∈ P), q (jq J ⟨u, hP.1 hu⟩) ∈ T0 := fun hu =>
    (hT _).2 ⟨_, hu, _, rfl⟩
  have hcomm : ∀ {u v : G} (hu : u ∈ P) (hv : v ∈ P),
      q (jq J ⟨u, hP.1 hu⟩) * q (jq J ⟨v, hP.1 hv⟩) =
        q (jq J ⟨v, hP.1 hv⟩) * q (jq J ⟨u, hP.1 hu⟩) →
      q (jq J ⟨u, hP.1 hu⟩) * q (jq J ⟨u, hP.1 hu⟩) = 1 → u⁻¹ * v⁻¹ * u * v ∈ zpowers a := by
    intro u v hu hv huv hu2
    have hm : u⁻¹ * v⁻¹ * u * v ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem (P.inv_mem hu) (P.inv_mem hv)) hu) hv
    have e : (⟨u⁻¹ * v⁻¹ * u * v, hP.1 hm⟩ : J) = (⟨u, hP.1 hu⟩ : J)⁻¹ *
        (⟨v, hP.1 hv⟩ : J)⁻¹ * ⟨u, hP.1 hu⟩ * ⟨v, hP.1 hv⟩ := rfl
    have hdk : (jq J ⟨u, hP.1 hu⟩)⁻¹ * (jq J ⟨v, hP.1 hv⟩)⁻¹ * jq J ⟨u, hP.1 hu⟩ *
        jq J ⟨v, hP.1 hv⟩ ∈ q.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      generalize q (jq J ⟨u, hP.1 hu⟩) = s at huv ⊢
      generalize q (jq J ⟨v, hP.1 hv⟩) = t at huv ⊢
      rw [mul_assoc s⁻¹ t⁻¹ s, ← mul_assoc, mul_assoc _ s t, huv]
      group
    have hu2k : jq J ⟨u, hP.1 hu⟩ * jq J ⟨u, hP.1 hu⟩ ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      exact hu2
    have hd2 := sq_comm_eq_one (hqker ▸ hdk) (hqker ▸ hu2k)
    apply hza hm
    rw [e]
    simp only [map_mul, map_inv]
    exact hk1 _ hdk hd2
  obtain ⟨hA8, hAZ⟩ := hQ.exists_A0 hâk hâ1 hâ2
  have hAT := hAZ.trans (comap_mono (inf_le_right : Z0 ≤ T0))
  refine ⟨pullP J P hP.1 _, pullP_le _,
    ⟨isElemTwo_pullP hP2 hA8.1, by rw [card_pullP hP2 hT hAT, hA8.2]⟩,
    mem_pullP.2 ⟨haP, mem_sup_right (mem_sup_right (mem_zpowers _))⟩, ?_, ?_⟩
  · intro c hc p hp
    obtain ⟨hcP, hcA⟩ := mem_pullP.1 hc
    have hcZ := hAZ hcA
    refine hcomm hcP hp ((mem_centralizer_iff.mp hcZ.1) _ (hTP hp)).symm ?_
    rw [← map_mul, hA8.1.2 _ hcA, map_one]
  · intro B hBP _ hBs
    have hBinv : ∀ {u : G} (hu : u ∈ B),
        q (jq J ⟨u, hP.1 (hBP hu)⟩) * q (jq J ⟨u, hP.1 (hBP hu)⟩) = 1 := by
      intro u hu
      have hk : jq J ⟨u * u, hP.1 (P.mul_mem (hBP hu) (hBP hu))⟩ ∈ q.ker := by
        rw [hqker]
        exact (mem_zStarIn_iff _).1 (hBs u hu)
      rw [hmulP (hBP hu) (hBP hu), MonoidHom.mem_ker, map_mul] at hk
      exact hk
    obtain ⟨U, hUeq, hUT, hUsq, hBU⟩ : ∃ U : Subgroup (Equiv.Perm (Fin 42)), (U = U1 ∨ U = U2) ∧
        U ≤ T0 ∧ (∀ t ∈ U, t * t = 1) ∧
        ∀ {u : G} (hu : u ∈ B), q (jq J ⟨u, hP.1 (hBP hu)⟩) ∈ U := by
      by_cases h1 : ∀ {u : G} (hu : u ∈ B), q (jq J ⟨u, hP.1 (hBP hu)⟩) ∈ U1
      · exact ⟨U1, Or.inl rfl, U1_le_T0, fun t ht => U1_mul_self ht, h1⟩
      · push Not at h1
        obtain ⟨u₁, hu₁, hn1⟩ := h1
        have hu₁2 := (involution_mem_U (hTP (hBP hu₁)) (hBinv hu₁)).resolve_left hn1
        refine ⟨U2, Or.inr rfl, U2_le_T0, fun t ht => U2_mul_self ht, fun {u} hu => ?_⟩
        by_contra hn2
        have hu1 := (involution_mem_U (hTP (hBP hu)) (hBinv hu)).resolve_right hn2
        have hprod := involution_mem_U (hTP (hBP (B.mul_mem hu₁ hu)))
          (hBinv (B.mul_mem hu₁ hu))
        rw [hmulP (hBP hu₁) (hBP hu), map_mul] at hprod
        rcases hprod with hp1 | hp2
        · exact hn1 (by simpa using U1.mul_mem hp1 (U1.inv_mem hu1))
        · exact hn2 (by simpa using U2.mul_mem (U2.inv_mem hu₁2) hp2)
    have hZU : Z0 ≤ U := by
      rcases hUeq with rfl | rfl
      · exact Z0_le_U1
      · exact Z0_le_U2
    have hcardU : Nat.card U = 16 := by
      rcases hUeq with rfl | rfl
      · exact card_U1
      · exact card_U2
    refine ⟨pullP J P hP.1 (U.comap q), pullP_le _, pullP_mono (hAZ.trans (comap_mono hZU)),
      fun z hz => ?_, fun u hu => mem_pullP.2 ⟨hBP hu, hBU hu⟩, ?_, fun u hu v hv => ?_,
      fun u hu => ?_⟩
    · obtain ⟨hzP, hzZ⟩ := mem_inf.mp hz
      refine mem_pullP.2 ⟨hzP, ?_⟩
      have hk : jq J ⟨z, hP.1 hzP⟩ ∈ q.ker := by
        rw [hqker]
        exact (mem_zStarIn_iff _).1 hzZ
      rw [mem_comap, MonoidHom.mem_ker.mp hk]
      exact one_mem _
    · rw [card_pullP hP2 hT (comap_mono hUT),
        card_comap_eq q U (fun t ht => hqsurj t (T0_le_S (hUT ht))), hcardU, hk4]
    · obtain ⟨huP, huU⟩ := mem_pullP.1 hu
      obtain ⟨hvP, hvU⟩ := mem_pullP.1 hv
      exact hcomm huP hvP (comm_of_mul_self (hUsq _ huU) (hUsq _ hvU)
        (hUsq _ (U.mul_mem huU hvU))) (hUsq _ huU)
    · obtain ⟨huP, huU⟩ := mem_pullP.1 hu
      obtain ⟨w, hw, hww⟩ := hQ.exists_sq_eq (hTP huP) (hUsq _ huU)
      apply hza (P.mul_mem huP huP)
      rw [hmulP huP huP, hww]
      exact hk2 w hw

end CFSG.ComponentClassification.GrSLit.L34Facts

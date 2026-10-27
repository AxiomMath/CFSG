module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4RealStd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsReal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsOutInv
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4OuterStd

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UnbalancedCorr
  CFSG.ComponentClassification.UnbalancedGS CFSG.ComponentClassification.GrSLit.L34Facts GrS4

theorem l34OuterInvolutionCenterInvStep_of_local
    {G : Type} [Group G] [Finite G]
    {J S : Subgroup G} {a b : G}
    (h1 : L34OuterCentralizerCosetFact) (h2 : L34OuterFixedInvolutionFact)
    (h3 : L34OuterCommutatorFact)
    (hJ : ⁅J, J⁆ = J) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hS : IsSylowTwoIn S (normalizer (J : Set G)))
    (hZc : IsCyclic ↥(S ⊓ zStarIn J))
    (hZ4 : Nat.card ↥(S ⊓ zStarIn J) = 4)
    (haZ : a ∈ S ⊓ zStarIn J)
    (hinv : ∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J)
    (hbS : b ∈ S) (hbb : b * b = 1) (hbK : b ∉ withKernel J)
    (hbinv : ∀ z ∈ S ⊓ zStarIn J, b * z * b⁻¹ = z⁻¹) :
    (∀ y ∈ S ⊓ centralizer ({b} : Set G),
        (∀ t ∈ S ⊓ centralizer ({b} : Set G), y * t = t * y) → y * y = 1 →
          y ∈ J ∨ b * y ∈ J) ∧
      (∃ z ∈ J ⊓ (S ⊓ centralizer ({b} : Set G)),
          (∀ t ∈ S ⊓ centralizer ({b} : Set G), z * t = t * z) ∧
            z * z = 1 ∧ z ≠ 1 ∧ z ≠ a) ∧
      ∀ z ∈ J ⊓ (S ⊓ centralizer ({b} : Set G)),
        (∀ t ∈ S ⊓ centralizer ({b} : Set G), z * t = t * z) → z * z = 1 →
          ∃ s ∈ S, s⁻¹ * b * s = b * z := by
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  have hP : IsSylowTwoIn (S ⊓ J) J := isSylowTwoIn_inf hS
  have hP2 : IsPGroup 2 (S ⊓ J : Subgroup G) := isPGroup_of_isSylowTwoIn hP
  have hPJ : S ⊓ J ≤ J := inf_le_right
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  have hSP : ∀ s ∈ S, s ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) := fun s hs =>
    inf_mem_normalizer (le_normalizer hs) (hSN hs)
  have hbN : b ∈ normalizer (J : Set G) := hSN hbS
  have hb1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  obtain ⟨q, l, ρ, hρ, hQ, hβ, hT⟩ := exists_outer_standard hJ hL34 hbN hbb hbK hP (hSP b hbS)
  have hρR : ρ ∈ R := by
    rcases hρ with rfl | rfl | rfl
    exacts [r₂_mem_R, r₃_mem_R, r₄_mem_R]
  have hZiff : ∀ g, g ∈ S ⊓ zStarIn J ↔ g ∈ S ⊓ J ∧ g ∈ zStarIn J := fun g => by
    simp only [mem_inf]
    exact ⟨fun h => ⟨⟨h.1, (map_subtype_le _ : zStarIn J ≤ J) h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  obtain ⟨hkc, hk4⟩ := ker_isCyclic_card_of_std hP hZiff hZc hZ4 hQ.ker hT
  obtain ⟨ψ, hψR, hψ⟩ := exists_realization_hom hSN hQ.qS hQ.qsurj hQ.ker
  have hψb : ψ ⟨b, hbS⟩ = ρ⁻¹ := by
    have h := realization_unique (β := betaHat J hbN) hQ.qsurj (R.inv_mem (hψR ⟨b, hbS⟩)) hρR
      (fun e => by rw [hψ ⟨b, hbS⟩ e, inv_inv]) hβ
    rw [← h, inv_inv]
  have hcomm : ∀ s : ↥S, (s : G) * b = b * s → ψ s * ρ = ρ * ψ s := by
    intro s hs
    have e1 : ψ s * ψ ⟨b, hbS⟩ = ψ ⟨b, hbS⟩ * ψ s := by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext hs)
    rw [hψb] at e1
    calc ψ s * ρ = ρ * (ρ⁻¹ * ψ s) * ρ := by group
      _ = ρ * (ψ s * ρ⁻¹) * ρ := by rw [e1]
      _ = ρ * ψ s := by group
  have hfix : ∀ p (hp : p ∈ S ⊓ J), betaHat J hbN (jq J ⟨p, hPJ hp⟩) = jq J ⟨p, hPJ hp⟩ →
      p ∈ S ⊓ centralizer ({b} : Set G) := by
    intro p hp hpb
    have h := (conj_eq_iff_betaHat hPJ hP2 hbN (hSP b hbS) hp).2 hpb
    refine mem_inf.mpr ⟨hp.1, mem_centralizer_singleton_iff.mpr ?_⟩
    calc p * b = b * (b⁻¹ * p * b) := by group
      _ = b * p := by rw [h]
  refine ⟨fun y hyX hyZ hyy => ?_, ?_, fun z hzJX hzZ hzz => ?_⟩
  ·
    have hyS : y ∈ S := (mem_inf.mp hyX).1
    have hyb : y * b = b * y := mem_centralizer_singleton_iff.mp (mem_inf.mp hyX).2
    have hrr : ψ ⟨y, hyS⟩ * ψ ⟨y, hyS⟩ = 1 := by
      rw [← map_mul]
      exact (congrArg ψ (Subtype.ext hyy : (⟨y, hyS⟩ * ⟨y, hyS⟩ : ↥S) = 1)).trans (map_one ψ)
    have hrF : ∀ e, q e ∈ T0 → betaHat J hbN e = e →
        ψ ⟨y, hyS⟩ * q e = q e * ψ ⟨y, hyS⟩ := by
      intro e he hbe
      obtain ⟨p, hpP, hpJ, rfl⟩ := (hT e).1 he
      have hpX := hfix p hpP hbe
      have hyp : y⁻¹ * p * y = p := by
        calc y⁻¹ * p * y = y⁻¹ * (y * p) := by rw [mul_assoc, hyZ p hpX]
          _ = p := by group
      have hfy := (conj_eq_iff_betaHat hPJ hP2 (hSN hyS) (hSP y hyS) hpP).1 hyp
      have e2 := hψ ⟨y, hyS⟩ (jq J ⟨p, hpJ⟩)
      rw [show betaHat J (hSN (⟨y, hyS⟩ : ↥S).2) (jq J ⟨p, hpJ⟩) = jq J ⟨p, hpJ⟩ from hfy] at e2
      calc ψ ⟨y, hyS⟩ * q (jq J ⟨p, hpJ⟩) =
          ψ ⟨y, hyS⟩ * ((ψ ⟨y, hyS⟩)⁻¹ * q (jq J ⟨p, hpJ⟩) * ψ ⟨y, hyS⟩) := by rw [← e2]
        _ = q (jq J ⟨p, hpJ⟩) * ψ ⟨y, hyS⟩ := by group
    rcases h1 (Jhat J) q l hQ hkc hk4 ρ hρ (betaHat J hbN) hβ (ψ ⟨y, hyS⟩) (hψR _)
        (mul_inv_mem_T0_of_realization hSN hQ.qsurj hT hψ ⟨y, hyS⟩ (hSP y hyS))
        (hcomm ⟨y, hyS⟩ hyb) hrr hrF with hrS | hrS
    · exact Or.inl (mem_of_mem_withKernel hS hinv hyS
        (mem_withKernel_of_realization_mem_S hJ hSN hQ.qsurj hQ.ker hψ ⟨y, hyS⟩ hrS) hyy)
    · right
      have hbyS : b * y ∈ S := mul_mem hbS hyS
      have hr1 : (ψ ⟨y, hyS⟩)⁻¹ = ψ ⟨y, hyS⟩ := inv_eq_of_mul_eq_one_right hrr
      have hψby : ψ ⟨b * y, hbyS⟩ = (ψ ⟨y, hyS⟩ * ρ)⁻¹ := by
        rw [show (⟨b * y, hbyS⟩ : ↥S) = ⟨b, hbS⟩ * ⟨y, hyS⟩ from rfl, map_mul, hψb, mul_inv_rev,
          hr1]
      have hW := mem_withKernel_of_realization_mem_S hJ hSN hQ.qsurj hQ.ker hψ ⟨b * y, hbyS⟩
        (by rw [hψby]; exact inv_mem hrS)
      have hbyy : b * y * (b * y) = 1 := by
        calc b * y * (b * y) = b * (y * b) * y := by group
          _ = b * b * (y * y) := by rw [hyb]; group
          _ = 1 := by rw [hbb, hyy, one_mul]
      exact mem_of_mem_withKernel hS hinv hbyS hW hbyy
  ·
    set X : Subgroup G := S ⊓ centralizer ({b} : Set G) with hXdef
    set Y : Subgroup (Equiv.Perm (Fin 42)) := (X.subgroupOf S).map ψ with hYdef
    have hY2 : IsPGroup 2 ↥Y := (hS2.to_subgroup (X.subgroupOf S)).map ψ
    have hbX : b ∈ X := mem_inf.mpr ⟨hbS, mem_centralizer_singleton_iff.mpr rfl⟩
    have hρY : ρ ∈ Y := by
      have h : ψ ⟨b, hbS⟩ ∈ Y := mem_map_of_mem ψ (mem_subgroupOf.mpr hbX)
      rw [hψb] at h
      simpa using Y.inv_mem h
    have hYR : Y ≤ R := by
      rintro _ ⟨s, -, rfl⟩
      exact hψR s
    have hYT : ∀ r ∈ Y, ∀ t ∈ T0, r * t * r⁻¹ ∈ T0 := by
      rintro _ ⟨s, -, rfl⟩
      exact mul_inv_mem_T0_of_realization hSN hQ.qsurj hT hψ s (hSP s s.2)
    have hYρ : ∀ r ∈ Y, r * ρ = ρ * r := by
      rintro _ ⟨s, hs, rfl⟩
      exact hcomm s (mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_subgroupOf.mp hs)).2)
    have hYF : ∀ e, q e ∈ T0 → betaHat J hbN e = e → q e ∈ Y := by
      intro e he hbe
      obtain ⟨p, hpP, hpJ, rfl⟩ := (hT e).1 he
      have hpX := hfix p hpP hbe
      rw [← realization_eq_of_mem hSN hQ.qS hQ.qsurj hψR hψ ⟨p, hpP.1⟩ hpJ]
      exact mem_map_of_mem ψ (mem_subgroupOf.mpr hpX)
    obtain ⟨w, hwT, hww, hw1, hwfix⟩ :=
      h2 (Jhat J) q l hQ hkc hk4 ρ hρ (betaHat J hbN) hβ Y hY2 hYR hYT hYρ hρY hYF
    obtain ⟨p, hpP, hpJ, rfl⟩ := (hT _).1 hwT
    have hpX : p ∈ X := hfix p hpP (hwfix ρ hρY (betaHat J hbN) hβ)
    refine ⟨p, mem_inf.mpr ⟨hpJ, hpX⟩, fun t ht => ?_, ?_, ?_, ?_⟩
    · have htS : t ∈ S := (mem_inf.mp ht).1
      have hmem : (ψ ⟨t, htS⟩)⁻¹ ∈ Y := Y.inv_mem (mem_map_of_mem ψ (mem_subgroupOf.mpr ht))
      have hβt := hwfix _ hmem (betaHat J (hSN htS)) (fun e => by rw [hψ ⟨t, htS⟩ e, inv_inv])
      have h := (conj_eq_iff_betaHat hPJ hP2 (hSN htS) (hSP t htS) hpP).2 hβt
      calc p * t = t * (t⁻¹ * p * t) := by group
        _ = t * p := by rw [h]
    · refine eq_one_of_jq_eq_one hPJ hP2 (mul_mem hpP hpP) ?_
      exact (map_mul (jq J) ⟨p, hpJ⟩ ⟨p, hpJ⟩).trans hww
    · rintro rfl
      exact hw1 (by rw [show (⟨1, hpJ⟩ : ↥J) = 1 from rfl, map_one, map_one])
    · rintro rfl
      apply hw1
      rw [← MonoidHom.mem_ker, hQ.ker]
      exact (mem_zStarIn_iff hpJ).1 (mem_inf.mp haZ).2
  ·
    have hzJ : z ∈ J := (mem_inf.mp hzJX).1
    have hzX := (mem_inf.mp hzJX).2
    have hzP : z ∈ S ⊓ J := mem_inf.mpr ⟨(mem_inf.mp hzX).1, hzJ⟩
    have hzb : z * b = b * z := mem_centralizer_singleton_iff.mp (mem_inf.mp hzX).2
    have hwT : q (jq J ⟨z, hzJ⟩) ∈ T0 := (hT _).2 ⟨z, hzP, hzJ, rfl⟩
    have hww : jq J ⟨z, hzJ⟩ * jq J ⟨z, hzJ⟩ = 1 := by
      rw [← map_mul]
      exact (congrArg (jq J) (Subtype.ext hzz : (⟨z, hzJ⟩ * ⟨z, hzJ⟩ : ↥J) = 1)).trans
        (map_one _)
    have hβw : betaHat J hbN (jq J ⟨z, hzJ⟩) = jq J ⟨z, hzJ⟩ := by
      refine (conj_eq_iff_betaHat hPJ hP2 hbN (hSP b hbS) hzP).1 ?_
      calc b⁻¹ * z * b = b⁻¹ * (b * z) := by rw [mul_assoc, hzb]
        _ = z := by group
    have hinvk : ∀ e ∈ q.ker, betaHat J hbN e = e⁻¹ := by
      intro e he
      have he1 : q e ∈ T0 := by
        rw [MonoidHom.mem_ker.mp he]
        exact one_mem _
      obtain ⟨p, hpP, hpJ, rfl⟩ := (hT e).1 he1
      have hpZ : p ∈ S ⊓ zStarIn J :=
        mem_inf.mpr ⟨hpP.1, (mem_zStarIn_iff hpJ).2 (hQ.ker ▸ he)⟩
      have h := hbinv p hpZ
      rw [betaHat_jq, ← map_inv]
      congr 1
      apply Subtype.ext
      rw [coe_conjJ, Subgroup.coe_inv, ← h, hb1]
    obtain ⟨v, hvT, hv⟩ :=
      h3 (Jhat J) q l hQ hkc hk4 ρ hρ (betaHat J hbN) hβ hinvk _ hwT hww hβw
    obtain ⟨p, hpP, hpJ, rfl⟩ := (hT v).1 hvT
    have hcP : b⁻¹ * p * b ∈ S ⊓ J := conj_mem_of_mem_normalizer (hSP b hbS) hpP
    have hmem : (b⁻¹ * p * b)⁻¹ * p ∈ S ⊓ J := mul_mem (inv_mem hcP) hpP
    have e1 : jq J ⟨(b⁻¹ * p * b)⁻¹ * p, hPJ hmem⟩ = jq J ⟨z, hzJ⟩ := by
      rw [← hv, betaHat_jq, ← map_inv, ← map_mul]
      rfl
    have e2 := eq_of_jq_eq hPJ hP2 hmem hzP e1
    refine ⟨p, hpP.1, ?_⟩
    calc p⁻¹ * b * p = b * ((b⁻¹ * p * b)⁻¹ * p) := by group
      _ = b * z := by rw [e2]


theorem l34OuterInvolutionCenterInvStep_of_facts
    (h1 : L34OuterCentralizerCosetFact)
    (h2 : L34OuterFixedInvolutionFact) (h3 : L34OuterCommutatorFact) :
    L34OuterInvolutionCenterInvStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl b hbS hbb hbK hbinv
  obtain ⟨hbase, hU3, hL34, -, hS, haS, -⟩ := id hset
  have hJ : ⁅J, J⁆ = J := GSThmB.commutator_eq_self_of_isPComponent hU3.2.2.2.1 hU3.2.2.2.2.1
  have hZne : S ⊓ zStarIn J ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hZ4
    norm_num at hZ4
  have haZ : a ∈ S ⊓ zStarIn J := hZ hZne
  exact l34OuterInvolutionCenterInvStep_of_local h1 h2 h3 hJ hL34 hS hZc hZ4 haZ hinv
    hbS hbb hbK hbinv

end CFSG.ComponentClassification.GrSLit

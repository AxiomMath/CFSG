module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Z

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G]

theorem le_normalizer_of_card_eq_two_mul [Finite G] {A B : Subgroup G} (hAB : A ≤ B)
    (hc : Nat.card B = 2 * Nat.card A) : B ≤ Subgroup.normalizer (A : Set G) := by
  have h1 := Subgroup.relIndex_mul_card A B
  rw [inf_eq_left.mpr hAB, hc] at h1
  have hA0 : 0 < Nat.card A := Nat.card_pos
  have h2 : A.relIndex B = 2 := Nat.eq_of_mul_eq_mul_right hA0 h1
  have h3 : (A.subgroupOf B).Normal := Subgroup.normal_of_index_eq_two h2
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mp h3

theorem mem_normalizer_inf' {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hA x, hB x]

theorem isSylow2In_inf_of_le_normalizer' [Finite G] {V C H : Subgroup G} (hV : IsSylow2In V C)
    (hHC : H ≤ C) (hn : C ≤ Subgroup.normalizer (H : Set G)) : IsSylow2In (V ⊓ H) H := by
  refine ⟨inf_le_right, hV.2.1.to_le inf_le_left, ?_⟩
  intro T hTH hT2 hle
  obtain ⟨V', hV', hTV'⟩ := IsSylow2In.exists_ge hT2 (hTH.trans hHC)
  obtain ⟨x, hxC, hx⟩ := exists_conjSub_eq_of_isSylow2In hV hV'
  have hxH : conjSub x⁻¹ H = H :=
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer (H : Set G)).inv_mem (hn hxC))
  have hTV : conjSub x⁻¹ T ≤ V ⊓ H := by
    refine le_inf ?_ ?_
    · have := conjSub_mono (n := x⁻¹) (hTV'.trans hx.symm.le)
      rwa [conjSub_inv_conjSub] at this
    · have := conjSub_mono (n := x⁻¹) hTH
      rwa [hxH] at this
  have hcard : Nat.card T ≤ Nat.card ↥(V ⊓ H) := by
    rw [← AscL62.natCard_conjSub x⁻¹ T]
    exact Subgroup.card_le_of_le hTV
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

variable [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G} {z j : G}

theorem exists_cfg64 (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j) (hJs : J ∈ omegaStarNbr Ω K)
    (hJnot : J ∉ omegaNbr Ω K) : ∃ u v : G, ∃ R T : Subgroup G, Cfg64 Ω K J z j u v R T := by
  obtain ⟨-, hJK, U', hU', hU'J, hU'N⟩ := hJs
  have hKJ : K ≠ J := Ne.symm hJK
  obtain ⟨-, T₀, hT₀, -⟩ := hΩ.omega1 J hJ
  have hzj := ne_of_not_mem_omegaNbr hΩ hK hJ hKJ hz hj hJnot hT₀
  have hKnot := not_mem_omegaNbr_symm hΩ hK hJ hz hj hzj hJnot
  have hP : Pair Ω K J z j := ⟨hK, hJ, hz, hj, hzj⟩
  obtain ⟨-, -, -, -, -, -, -, -, hU'4⟩ := exists_data_of_mem_USet hΩ hU'
  have hU'2 := isPGroup_of_mem_USet hΩ hU'
  have hjU' : j ∈ U' := AscL62.mem_of_uniqueInvolution_of_pGroup hj hU'J hU'2 (by omega)
  obtain ⟨V, hV, hU'V⟩ := IsSylow2In.exists_ge hU'2
    (le_inf hU'J (le_centralizer_of_le_normalizer' hz hU'N))
  have hV4 : 4 ≤ Nat.card V := hU'4.trans (Subgroup.card_le_of_le hU'V)
  have hjV : j ∈ V := hU'V hjU'
  have hVU : V ∈ USet Ω := sylow_cent_mem_USet hΩ hK hJ hz hj hzj hJnot hV hjV (by omega)
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  obtain ⟨-, R, hR, hcfg, -, hUN, hcomm, hdich⟩ :=
    hP.symm.bootstrap hΩ hVJ hV.2.1 hjV (hV.1.trans inf_le_right) hV4
  rcases hdich with hRC | ⟨C, hUC, hCR, hCc, hCcard, -, -, -, -, -⟩
  · exfalso
    have hRc : R ≤ Subgroup.centralizer ({j} : Set G) := fun x hx =>
      ((SetLike.ext_iff.mp hRC x).mpr hx).2
    have h8 := eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)
    exact hKnot ⟨hK, hKJ, R, mem_RSet_of_isSylow2In hK hR, hR.1,
      le_normalizer_of_le_centralizer hΩ hJ hK hJK hj hR.1 hR.2.1 (by omega) hRc⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
  have hCg := AscL62.eq_zpowers_of_generator g hg
  have hVcyc : IsCyclic ↥V := by
    obtain ⟨-, -, -, hcyc, -⟩ := hVU
    exact hcyc
  obtain ⟨gv, hgv⟩ := IsCyclic.exists_generator (α := ↥V)
  have hVg := AscL62.eq_zpowers_of_generator gv hgv
  set u : G := (g : G) with hu
  set v : G := (gv : G) with hv
  rw [hUC, hCg] at hUN hcomm
  rw [hCg] at hCR hCcard hCc
  rw [hVg] at hVU hVJ hcfg hjV
  have hUV : Commutes (Subgroup.zpowers u) (Subgroup.zpowers v) := fun a ha b hb =>
    hcomm a ha b (hVg ▸ hb)
  have hUU : Subgroup.zpowers u ∈ USet Ω := mem_USet_of_natCard hK hR hCR hCc hCcard
  have hU2 : IsPGroup 2 ↥(Subgroup.zpowers u) := hR.2.1.to_le hCR
  have hV2 : IsPGroup 2 ↥(Subgroup.zpowers v) := hVg ▸ hV.2.1
  have hUK : Subgroup.zpowers u ≤ K := hCR.trans hR.1
  have hbot : ∀ {A B : Subgroup G}, A ≤ K → B ≤ J → IsPGroup 2 ↥B → A ⊓ B = ⊥ := by
    intro A B hAK hBJ hB2
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    exact hP.eq_one_of_mem_of_mem (hAK hg.1) (hBJ hg.2)
      (AscL62.orderOf_eq_two_pow_of_isPGroup hB2 hg.2)
  have hVcard : Nat.card (Subgroup.zpowers v) = Nat.card (Subgroup.zpowers u) := by
    obtain ⟨RV, -, JV, hJV, hRVJV, hVRV, -, hRVcard, -⟩ := exists_data_of_mem_USet hΩ hVU
    have e : JV = J := eq_of_mem_USet hΩ hVU hJV hJ (hVRV.trans hRVJV.1) hVJ
    subst e
    have := natCard_isSylow2In_eq hΩ hJV hK hRVJV hR
    omega
  have hUVcard : Nat.card ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) =
      Nat.card (Subgroup.zpowers u) * Nat.card (Subgroup.zpowers u) := by
    have h := card_sup_mul_card_inf_of_le_normalizer (AscL62.le_normalizer_of_commutes hUV)
    rwa [hbot hUK hVJ hV2, Subgroup.card_bot, mul_one, hVcard] at h
  have hVR : Subgroup.zpowers v ≤ Subgroup.normalizer (R : Set G) := fun y hy =>
    mem_normalizer_iff_conjSub_eq.mpr (hcfg.norm y hy)
  have hRVcard : Nat.card ↥(Subgroup.zpowers v ⊔ R) =
      Nat.card (Subgroup.zpowers u) * Nat.card R := by
    have h := card_sup_mul_card_inf_of_le_normalizer hVR
    rwa [inf_comm, hbot hR.1 hVJ hV2, Subgroup.card_bot, mul_one, hVcard] at h
  have hRN : R ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
    have hle : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ Subgroup.zpowers v ⊔ R :=
      sup_le (hCR.trans le_sup_right) le_sup_left
    refine le_sup_right.trans (le_normalizer_of_card_eq_two_mul hle ?_)
    rw [hRVcard, hUVcard, hCcard]
    ring
  have hUV2 : IsPGroup 2 ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) :=
    IsPGroup.to_sup_of_normal_right' hU2 hV2 (AscL62.le_normalizer_of_commutes hUV)
  have hUVM : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ J ⊔ Subgroup.zpowers u :=
    sup_le le_sup_right (hVJ.trans le_sup_left)
  obtain ⟨S, hS, hUVS⟩ := IsSylow2In.exists_ge hUV2 hUVM
  have hMN : J ⊔ Subgroup.zpowers u ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer hUN
  have hT : IsSylow2In (S ⊓ J) J := isSylow2In_inf_of_le_normalizer' hS le_sup_left hMN
  have hvT : Subgroup.zpowers v ≤ S ⊓ J := le_inf (le_sup_right.trans hUVS) hVJ
  have hUT : Subgroup.zpowers u ≤ Subgroup.normalizer ((S ⊓ J : Subgroup G) : Set G) :=
    fun a ha => mem_normalizer_inf' (Subgroup.le_normalizer (hUVS (Subgroup.mem_sup_left ha)))
      (hUN ha)
  have hTcard : Nat.card ↥(S ⊓ J) = Nat.card R := natCard_isSylow2In_eq hΩ hJ hK hT hR
  have hUTcard : Nat.card ↥(Subgroup.zpowers u ⊔ (S ⊓ J)) =
      Nat.card (Subgroup.zpowers u) * Nat.card R := by
    have h := card_sup_mul_card_inf_of_le_normalizer hUT
    rwa [hbot hUK inf_le_right (hS.2.1.to_le inf_le_left), Subgroup.card_bot, mul_one,
      hTcard] at h
  have hTN : S ⊓ J ≤ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
    have hle : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ Subgroup.zpowers u ⊔ (S ⊓ J) :=
      sup_le le_sup_left (hvT.trans le_sup_right)
    refine le_sup_right.trans (le_normalizer_of_card_eq_two_mul hle ?_)
    rw [hUTcard, hUVcard, hCcard]
    ring
  exact ⟨u, v, R, S ⊓ J,
    ⟨hΩ, hK, hJ, hKJ, hz, hj, hJnot, hKnot, hUU, hUK, hVU, hVJ, hUV, hR, hT, hCR, hvT, hRN, hTN⟩⟩


end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

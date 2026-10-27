module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpW

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem perpA3_mem_USet_of_etaG {η : Set (Subgroup G)} (hη : η ∈ etaG Ω) {U : Subgroup G}
    (hU : U ∈ η) : U ∈ USet Ω := by
  obtain ⟨S, hS, -⟩ := hη
  exact (hS.1 hU).1

private theorem perpA3_natCard_of_mem_USet (h : EndHyp Ω) {U : Subgroup G} (hU : U ∈ USet Ω) :
    Nat.card U = 4 := by
  obtain ⟨R, -, J, hJ, hRJ, -, -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet h.thmD.hyp hU
  have hRJeq : J = R := hRJ.2.2 J le_rfl (h.thmD.two J hJ) hRJ.1
  rw [← hRJeq, h.card_eq_eight hJ] at hcard
  omega

theorem exists_wSet_of_omegaStar (h : EndHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaStarNbr Ω K) (hJn : J ∉ omegaNbr Ω K) :
    ∃ W ∈ WSet Ω, K ∈ DSet Ω W ∧ J ∈ DSet Ω W ∧
      ∃ n ∈ Subgroup.normalizer (W : Set G), conjSub n K = J := by
  have hyp := h.thmD.hyp
  have hJΩ : J ∈ Ω := hJ.1
  have hJK : J ≠ K := hJ.2.1
  have hKJ : K ≠ J := fun e => hJK e.symm
  have hKo : IsPGroup 2 K := h.thmD.two K hK
  have hJo : IsPGroup 2 J := h.thmD.two J hJΩ
  have hJ8 : Nat.card J = 8 := h.card_eq_eight hJΩ
  obtain ⟨-, hU4, -, hV4, -, hKJN⟩ := pair_structure h hK hJ hJn
  set U : Subgroup G := K ⊓ Subgroup.normalizer (J : Set G) with hUdef
  set V : Subgroup G := J ⊓ Subgroup.normalizer (K : Set G) with hVdef
  set X : Subgroup G := U ⊔ V with hXdef
  have hVJ : V ≤ J := by rw [hVdef]; exact inf_le_left
  have hVo : IsPGroup 2 V := hJo.to_le hVJ
  have hVK : V ≤ Subgroup.normalizer (K : Set G) := by rw [hVdef]; exact inf_le_right
  obtain ⟨S, hVKS⟩ := IsPGroup.exists_le_sylow (hVo.to_sup_of_normal_right' hKo hVK)
  have hKS : K ≤ (S : Subgroup G) := le_sup_right.trans hVKS
  have hVS : V ≤ (S : Subgroup G) := le_sup_left.trans hVKS
  have hJnS : ¬ J ≤ (S : Subgroup G) := by
    intro hJS
    have hcomm : Commutes K J :=
      Q3CP.l67Gen G Ω hyp S K (TC.mem_RSet_of_isPGroup hK hKo) J
        (TC.mem_RSet_of_isPGroup hJΩ hJo) hKS hJS hKJ
    have hJN : J ≤ Subgroup.normalizer (K : Set G) :=
      AscL62.le_normalizer_of_commutes hcomm.symm
    exact hJn ((TC.mem_omegaNbr_iff hyp h.thmD.two).mpr ⟨hJΩ, hJK, hJN⟩)
  have hJSV : J ⊓ (S : Subgroup G) = V := by
    have hVT : V ≤ J ⊓ (S : Subgroup G) := le_inf hVJ hVS
    have hle8 : Nat.card ↥(J ⊓ (S : Subgroup G)) ≤ 8 := by
      have := Subgroup.card_le_of_le (inf_le_left : J ⊓ (S : Subgroup G) ≤ J)
      rwa [hJ8] at this
    have hge4 : 4 ≤ Nat.card ↥(J ⊓ (S : Subgroup G)) := by
      have := Subgroup.card_le_of_le hVT
      rwa [hV4] at this
    have hdvd4 : 4 ∣ Nat.card ↥(J ⊓ (S : Subgroup G)) := by
      have := Subgroup.card_dvd_of_le hVT
      rwa [hV4] at this
    have hne8 : Nat.card ↥(J ⊓ (S : Subgroup G)) ≠ 8 := by
      intro e
      apply hJnS
      have heq : J ⊓ (S : Subgroup G) = J :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
      calc J = J ⊓ (S : Subgroup G) := heq.symm
        _ ≤ (S : Subgroup G) := inf_le_right
    have hT4 : Nat.card ↥(J ⊓ (S : Subgroup G)) = 4 := by omega
    exact (Subgroup.eq_of_le_of_card_ge hVT (by omega)).symm
  obtain ⟨η, hη, hηS, hinvS, hKη⟩ := h.exists_wSet_of_le hK S hKS
  set W : Subgroup G := ⨆ Y ∈ η, Y with hWdef
  have hW : W ∈ WSet Ω := ⟨η, hη, rfl⟩
  have hWS : W ≤ (S : Subgroup G) := iSup₂_le hηS
  have hWo : IsPGroup 2 W := S.isPGroup'.to_le hWS
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := TC.etaSpan_comm hyp hη
  have hWW : Commutes W W := fun x hx y hy => hWab x hx y hy
  have hcard4 : ∀ Y ∈ η, Nat.card ↥Y = 4 := fun Y hY =>
    perpA3_natCard_of_mem_USet h (perpA3_mem_USet_of_etaG hη hY)
  have hJc4 : Nat.card ↥(J ⊓ (S : Subgroup G)) = 4 := by rw [hJSV, hV4]
  have hJη : J ⊓ W ∈ η :=
    Sec6Gen.l6_11Gen G Ω hyp S η hη hηS J hJΩ (by omega)
  have hJWV : J ⊓ W = V := by
    have hle : J ⊓ W ≤ V := by
      rw [← hJSV]
      exact inf_le_inf_left J hWS
    have hJc := hcard4 _ hJη
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hVW : V ≤ W := by
    have h1 : J ⊓ W ≤ W := inf_le_right
    rw [hJWV] at h1
    exact h1
  obtain ⟨zK, hzK⟩ := Sec6Gen.exists_uniqueInvolution hyp hK
  obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution hyp hJΩ
  have hzJV : zJ ∈ V := AscL62.mem_of_uniqueInvolution_of_pGroup hzJ hVJ hVo (by omega)
  have hzJW : zJ ∈ W := hVW hzJV
  have hKW_K : K ⊓ W ≤ K := inf_le_left
  have hKW_o : IsPGroup 2 ↥(K ⊓ W) := hKo.to_le hKW_K
  have hKW_c : 3 ≤ Nat.card ↥(K ⊓ W) := by
    have := hcard4 _ hKη
    omega
  have hKW_cent : K ⊓ W ≤ Subgroup.centralizer ({zJ} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hWab a (Subgroup.mem_inf.mp ha).2 zJ hzJW
  have hKWN : K ⊓ W ≤ Subgroup.normalizer (J : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hyp hJΩ hK hJK hzJ hKW_K hKW_o hKW_c hKW_cent
  have hKWU : K ⊓ W = U := by
    have hle : K ⊓ W ≤ U := by
      rw [hUdef]
      exact le_inf hKW_K hKWN
    have hc := hcard4 _ hKη
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hUW : U ≤ W := by
    have h1 : K ⊓ W ≤ W := inf_le_right
    rw [hKWU] at h1
    exact h1
  have hXW : X ≤ W := sup_le hUW hVW
  have hWC : W ≤ Subgroup.centralizer (X : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hWab x (hXW hx) w hw
  obtain ⟨g, hgP, hgK⟩ := h.thmD.aEmpty K hK J hJ hJn zK zJ hzK hzJ
  have hpn : pairNormalizers K J zK zJ ≤ K ⊔ J := by
    unfold pairNormalizers
    exact sup_le (le_trans inf_le_left le_sup_left) (le_trans inf_le_left le_sup_right)
  have hgX : conjSub g X = X := mem_normalizer_iff_conjSub_eq.mp (hKJN (hpn hgP))
  have hcomm' : Commutes (conjSub g W) (conjSub g W) := hWW.conjSub g
  have hgWC : conjSub g W ≤ Subgroup.centralizer (X : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxX : x ∈ conjSub g X := by rw [hgX]; exact hx
    exact hcomm' x (conjSub_mono (n := g) hXW hxX) w hw
  have hgWo : IsPGroup 2 (conjSub g W) := hWo.map (MulAut.conj g).toMonoidHom
  obtain ⟨R₁, hR₁, hWR₁⟩ := IsSylow2In.exists_ge hWo hWC
  obtain ⟨R₂, hR₂, hgWR₂⟩ := IsSylow2In.exists_ge hgWo hgWC
  obtain ⟨c, hcC, hcR⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hR₂ hR₁
  obtain ⟨S', hR₁S'⟩ := IsPGroup.exists_le_sylow hR₁.2.1
  have hWS' : W ≤ (S' : Subgroup G) := hWR₁.trans hR₁S'
  have hcgS' : conjSub (c * g) W ≤ (S' : Subgroup G) := by
    rw [conjSub_mul]
    exact ((conjSub_mono (n := c) hgWR₂).trans hcR.le).trans hR₁S'
  have hnW : conjSub (c * g) W = W := wSet_weaklyClosed h hW S' hWS' (c * g) hcgS'
  have hn : c * g ∈ Subgroup.normalizer (W : Set G) := mem_normalizer_iff_conjSub_eq.mpr hnW
  have hVcJ : V ≤ conjSub c J := by
    intro v hv
    have hcv : v * c = c * v :=
      Subgroup.mem_centralizer_iff.mp hcC v ((le_sup_right : V ≤ U ⊔ V) hv)
    have h1 := conj_mem_conjSub (n := c) (hVJ hv)
    rwa [← hcv, mul_inv_cancel_right] at h1
  have hcJΩ : conjSub c J ∈ Ω := hyp.conjInvariant c J hJΩ
  have hJeq : J = conjSub c J :=
    Sec6Gen.eq_of_le_of_le hyp hJΩ hcJΩ hVo (by omega) hVJ hVcJ
  have hnK : conjSub (c * g) K = J := by
    rw [conjSub_mul, hgK, ← hJeq]
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs =>
    mem_normalizer_iff_conjSub_eq.mpr
      (TC.conjSub_etaSpan_eq (hinvS s hs) (hinvS s⁻¹ (inv_mem hs)))
  have hKN : K ≤ Subgroup.normalizer (W : Set G) := fun k hk => hSN k (hKS hk)
  have hKD : K ∈ DSet Ω W := h.mem_dSet_iff.mpr ⟨hK, hKN⟩
  have hJN : J ≤ Subgroup.normalizer (W : Set G) := by
    intro x hx
    rw [← hnK] at hx
    have hk : (c * g)⁻¹ * x * (c * g) ∈ K := mem_conjSub_iff.mp hx
    have hxe := mul_mem (mul_mem hn (hKN hk)) (inv_mem hn)
    rwa [show c * g * ((c * g)⁻¹ * x * (c * g)) * (c * g)⁻¹ = x by group] at hxe
  have hJD : J ∈ DSet Ω W := h.mem_dSet_iff.mpr ⟨hJΩ, hJN⟩
  exact ⟨W, hW, hKD, hJD, c * g, hn, hnK⟩

end CFSG.ClassicalInvolution.Q3.Sec13

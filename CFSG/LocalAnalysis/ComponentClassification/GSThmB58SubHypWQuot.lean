module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubHypW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuot

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Hyp52W

variable {H : Type} [Group H] [Finite H]

namespace QuotAux

theorem isPGroup_S (h : Hyp52W H) : IsPGroup 2 h.S := by
  obtain ⟨R, hR⟩ := h.S_sylow
  have h1 : IsPGroup 2 (h.S.subgroupOf (centralizer ({h.a} : Set H) ⊓
      normalizer (h.J : Set H))) := hR ▸ R.isPGroup'
  have h2 := h1.map (centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)).subtype
  rwa [map_subgroupOf_eq_of_le h.S_le] at h2

theorem isPGroup_B (h : Hyp52W H) : IsPGroup 2 h.B :=
  (isPGroup_S h).to_le (h.B_le.trans inf_le_left)

theorem a_mem_S (h : Hyp52W H) : h.a ∈ h.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := h.S_sylow
  have haC : h.a ∈ centralizer ({h.a} : Set H) := mem_centralizer_singleton_iff.mpr rfl
  have haN : h.a ∈ normalizer (h.J : Set H) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← mem_centralizer_singleton_iff.mp (h.J_le hy), mul_inv_cancel_right]
      exact hy
    · intro hy
      have hc : Commute h.a (h.a * y * h.a⁻¹) :=
        (mem_centralizer_singleton_iff.mp (h.J_le hy)).symm
      have h2 : y = h.a * y * h.a⁻¹ := by
        calc y = h.a⁻¹ * (h.a * y * h.a⁻¹) * h.a := by group
          _ = (h.a * y * h.a⁻¹) * h.a⁻¹ * h.a := by rw [hc.inv_left.eq]
          _ = h.a * y * h.a⁻¹ := by group
      rw [h2]
      exact hy
  let a' : ↥(centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)) :=
    ⟨h.a, mem_inf.mpr ⟨haC, haN⟩⟩
  have hcen : zpowers a' ≤ center ↥(centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)) := by
    rw [zpowers_le, mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp g.2).1)
  have : (zpowers a').Normal := normal_of_le_center hcen
  have hp : IsPGroup 2 (zpowers a') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.orderOf_a, pow_one])
  have h1 : a' ∈ (R : Subgroup _) := hp.le_sylow_of_normal R (mem_zpowers a')
  rw [hR] at h1
  exact h1

theorem a_mem_P (h : Hyp52W H) : h.a ∈ h.S ⊓ coreActionKernel h.J :=
  mem_inf.mpr ⟨a_mem_S h, GSLit.mem_coreActionKernel_of_le_centralizer h.J_le⟩

end QuotAux

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 H)

theorem quotient_oddCore (h : Hyp52W H) :
    ∃ h' : Hyp52W (H ⧸ pPrimeCore 2 H),
      h'.a = QuotientGroup.mk' (pPrimeCore 2 H) h.a ∧
      h'.J = h.J.map (QuotientGroup.mk' (pPrimeCore 2 H)) ∧
      h'.S = h.S.map (QuotientGroup.mk' (pPrimeCore 2 H)) ∧
      h'.B = h.B.map (QuotientGroup.mk' (pPrimeCore 2 H)) ∧
      h'.K = h.K.map (QuotientGroup.mk' (pPrimeCore 2 H)) ∧
      h'.x = QuotientGroup.mk' (pPrimeCore 2 H) h.x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := OddQuot.not_two_dvd_card_ker (H := H)
  have hS2 : IsPGroup 2 h.S := QuotAux.isPGroup_S h
  have hB2 : IsPGroup 2 h.B := QuotAux.isPGroup_B h
  have hSN : h.S ≤ normalizer (h.J : Set H) := h.S_le.trans inf_le_right
  have hSC : h.S ≤ centralizer ({h.a} : Set H) := h.S_le.trans inf_le_left
  have hBS : h.B ≤ h.S := h.B_le.trans inf_le_left
  have hBJ : h.B ≤ normalizer (h.J : Set H) := hBS.trans hSN
  have ha2 : h.a * h.a = 1 := by rw [← sq, ← h.orderOf_a, pow_orderOf_eq_one]
  have hW : normalizer ((h.B.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) =
      (normalizer (h.B : Set H)).map π := OddQuot.normalizer_map_eq hB2
  have hCa : centralizer ({π h.a} : Set (H ⧸ pPrimeCore 2 H)) =
      (centralizer ({h.a} : Set H)).map π := OddQuot.centralizer_singleton_map_eq ha2
  have hfixB : GSLit.fixedLayer (h.J.map π) (h.B.map π) = (GSLit.fixedLayer h.J h.B).map π :=
    (OddQuot.map_fixedLayer hB2 hBJ).symm
  have hlayer : layerIn (normalizer ((h.B.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H))) =
      (layerIn (normalizer (h.B : Set H))).map π := by
    rw [hW, OddQuot.map_layerIn π hO]
  have hP : (h.S ⊓ coreActionKernel h.J).map π = h.S.map π ⊓ coreActionKernel (h.J.map π) :=
    OddQuot.map_inf_coreActionKernel hSN
  have hT : (h.S ⊓ coreActionKernel h.J ⊓ normalizer (h.B : Set H)).map π =
      h.S.map π ⊓ coreActionKernel (h.J.map π) ⊓
        normalizer ((h.B.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) := by
    have e1 : h.S ⊓ coreActionKernel h.J ⊓ normalizer (h.B : Set H) =
        h.S ⊓ coreActionKernel h.J ⊓ (h.S ⊓ normalizer (h.B : Set H)) :=
      le_antisymm (le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
        (le_inf inf_le_left (inf_le_right.trans inf_le_right))
    rw [e1, OddQuot.map_inf_of_le hS2 inf_le_left inf_le_left, hP,
      OddQuot.map_inf_normalizer hS2 hBS]
    exact le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      (le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
  have hBxS : conjugate h.B h.x ≤ h.S := by
    intro y hy
    rw [mem_conjugate_iff] at hy
    have h1 := mul_mem (mul_mem (inv_mem h.x_mem) (hBS hy)) h.x_mem
    rwa [show h.x⁻¹ * (h.x * y * h.x⁻¹) * h.x = y by group] at h1
  have hinf : h.B.map π ⊓ conjugate (h.B.map π) (π h.x) = ⊥ := by
    rw [← map_conjugate, ← OddQuot.map_inf_of_le hS2 hBS hBxS, h.inf_conjugate_x, Subgroup.map_bot]
  have hBne : h.B.map π ≠ ⊥ := by
    intro hbot
    apply h.B_ne_bot
    have h1 : h.B ≤ h.B ⊓ pPrimeCore 2 H := le_inf le_rfl (by
      rw [← QuotientGroup.ker_mk' (pPrimeCore 2 H)]
      exact (Subgroup.map_eq_bot_iff _).mp hbot)
    rw [OddQuot.inf_pPrimeCore_eq_bot hB2] at h1
    exact le_bot_iff.mp h1
  obtain ⟨e, he⟩ := OddQuot.exists_wbar_equiv hB2
  have hJBW : GSLit.fixedLayer h.J h.B ≤ normalizer (h.B : Set H) :=
    (GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_right.trans (centralizer_le_normalizer _))
  have himg : wbarImage (h.B.map π) (GSLit.fixedLayer (h.J.map π) (h.B.map π)) =
      (wbarImage h.B (GSLit.fixedLayer h.J h.B)).map e.toMonoidHom := by
    rw [hfixB, OddQuot.map_wbarImage e he hJBW]
  have hcen : ∀ (ha : h.a ∈ normalizer (h.B : Set H))
      (ha' : π h.a ∈ normalizer ((h.B.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H))),
      centralizer ({wbarMk (h.B.map π) ⟨π h.a, ha'⟩} : Set (Wbar (h.B.map π))) =
        (centralizer ({wbarMk h.B ⟨h.a, ha⟩} : Set (Wbar h.B))).map e.toMonoidHom := by
    intro ha ha'
    rw [OddQuot.map_centralizer_singleton_equiv, he]
    rfl
  have hCN : centralizer ({π h.a} : Set (H ⧸ pPrimeCore 2 H)) ⊓
      normalizer ((h.J.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) =
      (centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)).map π := by
    refine le_antisymm ?_ (le_inf ((map_mono inf_le_left).trans hCa.ge)
      ((map_mono inf_le_right).trans (le_normalizer_map π)))
    rintro z ⟨hz1, hz2⟩
    rw [hCa] at hz1
    obtain ⟨g, hg, rfl⟩ := mem_map.mp hz1
    obtain ⟨hgX, hgc⟩ := OddQuot.isPComponent_conjugate_subgroupOf hg h.J_le h.isPComponent_J
    have heq : conjugate h.J g = h.J := OddQuot.eq_of_map_eq π hO hgX h.J_le hgc
      h.isPComponent_J (by rw [map_conjugate]; exact conjugate_eq_of_mem_normalizer hz2)
    exact mem_map_of_mem π (mem_inf.mpr ⟨hg, mem_normalizer_of_conjugate_eq heq⟩)
  have hker : normalizer ((h.B.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) ⊓
      coreActionKernel (layerIn (normalizer ((h.B.map π : Subgroup _) :
        Set (H ⧸ pPrimeCore 2 H)))) =
      (normalizer (h.B : Set H) ⊓ coreActionKernel (layerIn (normalizer (h.B : Set H)))).map π := by
    rw [hlayer, OddQuot.map_inf_coreActionKernel (OddQuot.le_normalizer_layerIn _), hW]
  set X9 := GSLit.fixedLayer h.J h.B ⊔ oddCoreIn (normalizer (h.B : Set H)) with hX9
  have hX9map : GSLit.fixedLayer (h.J.map π) (h.B.map π) ⊔
      oddCoreIn (normalizer ((h.B.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H))) =
      X9.map π := by
    rw [hX9, Subgroup.map_sup, hfixB, hW, OddQuot.map_oddCoreIn π hO]
  have hX9W : X9 ≤ normalizer (h.B : Set H) := sup_le hJBW (map_subtype_le _)
  have hWO : normalizer (h.B : Set H) ⊓ pPrimeCore 2 H ≤ X9 :=
    (OddQuot.inf_pPrimeCore_le_oddCoreIn _).trans le_sup_right
  have h9 : layerIn (normalizer ((h.B.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H))) ⊓
      normalizer ((X9.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) =
      (layerIn (normalizer (h.B : Set H)) ⊓ normalizer (X9 : Set H)).map π := by
    rw [hlayer]
    refine le_antisymm ?_ (le_inf (map_mono inf_le_left)
      ((map_mono inf_le_right).trans (le_normalizer_map π)))
    rintro _ ⟨⟨y, hy, rfl⟩, hyN⟩
    exact mem_map_of_mem π (mem_inf.mpr ⟨hy, OddQuot.mem_normalizer_of_map hX9W hWO
      (map_subtype_le _ hy) hyN⟩)
  obtain ⟨eK⟩ := OddQuot.nonempty_quotient_fusionZStar_equiv π hO h.K
  obtain ⟨eJ⟩ := OddQuot.nonempty_quotient_fusionZStar_equiv π hO h.J
  obtain ⟨eJ'⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hO h.J
  refine ⟨{
    a := π h.a
    J := h.J.map π
    S := h.S.map π
    B := h.B.map π
    K := h.K.map π
    x := π h.x
    kProper := OddQuot.kProper_quotient h.kProper _
    kGroup_normalizer := OddQuot.isKGroupCat_of_surjective h.kGroup_normalizer
      (OddQuot.normalizerMap h.B) (OddQuot.normalizerMap_surjective hB2)
    normalizer_ne_top := by
      intro htop
      have hx : π h.x ∈ normalizer ((h.B.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) :=
        htop ▸ mem_top _
      rw [conjugate_eq_of_mem_normalizer hx, inf_idem] at hinf
      exact hBne hinf
    orderOf_a := orderOf_mk_eq_two OddQuot.odd_card_pPrimeCore h.orderOf_a
    J_le := by
      rw [hCa]
      exact map_mono h.J_le
    isPComponent_J := by
      rw [hCa]
      exact OddQuot.isPComponent_map π hO h.J_le h.isPComponent_J
    smallType := OddQuot.smallType_of_equiv eJ' eJ h.smallType
    S_le := le_inf ((map_mono hSC).trans hCa.ge) ((map_mono hSN).trans (le_normalizer_map π))
    S_sylow := by
      rw [hCN]
      exact OddQuot.exists_sylow_map π h.S_le h.S_sylow
    B_le := by
      rw [← hP]
      exact map_mono h.B_le
    B_ne_bot := hBne
    a_mem_normalizer := le_normalizer_map π (mem_map_of_mem π h.a_mem_normalizer)
    isComponent_bar := by
      rw [himg, hcen h.a_mem_normalizer]
      exact ⟨map_mono h.isComponent_bar.1, OddQuot.isComponent_subgroupOf_map_equiv e
        h.isComponent_bar.1 h.isComponent_bar.2⟩
    isStandard_bar := by
      rw [himg]
      exact OddQuot.isStandardSubgroup_map_equiv e h.isStandard_bar
    conjClosure_eq := by
      rw [hlayer, hfixB, ← OddQuot.map_conjClosure, h.conjClosure_eq]
    commutator_eq := by
      rw [hlayer, ← MonoidHom.map_zpowers, ← map_commutator, h.commutator_eq]
    B_le_kernel := by
      rw [hker]
      exact map_mono h.B_le_kernel
    B_sylow_kernel := by
      rw [hker]
      exact OddQuot.exists_sylow_map π h.B_le_kernel h.B_sylow_kernel
    isoCorr_of_le_T := by
      intro E' hE' hcard
      rw [← hT] at hE'
      set E := (h.S ⊓ coreActionKernel h.J ⊓ normalizer (h.B : Set H)) ⊓ E'.comap π with hE
      have hEmap : E.map π = E' := OddQuot.map_inf_comap_eq hE'
      have hET : E ≤ h.S ⊓ coreActionKernel h.J ⊓ normalizer (h.B : Set H) := inf_le_left
      have hES : E ≤ h.S := hET.trans (inf_le_left.trans inf_le_left)
      have hE2 : IsPGroup 2 E := hS2.to_le hES
      have hcE : Nat.card (E.map π) = Nat.card E := OddQuot.card_map_of_isPGroup hE2
      have hcB : Nat.card (h.B.map π) = Nat.card h.B := OddQuot.card_map_of_isPGroup hB2
      have hcard' : Nat.card h.B < Nat.card E := by
        rw [← hEmap, hcE, hcB] at hcard
        exact hcard
      obtain ⟨L, hL⟩ := h.isoCorr_of_le_T E hET hcard'
      refine ⟨L.map π, ?_⟩
      rw [← hEmap]
      exact OddQuot.isoCorrSub_map hE2 (hES.trans hSN) h.orderOf_a hL
    isoCorr_of_mem := by
      intro E' hE' haE'
      rw [← hP] at hE'
      set E := (h.S ⊓ coreActionKernel h.J) ⊓ E'.comap π with hE
      have hEmap : E.map π = E' := OddQuot.map_inf_comap_eq hE'
      have hEP : E ≤ h.S ⊓ coreActionKernel h.J := inf_le_left
      have hES : E ≤ h.S := hEP.trans inf_le_left
      have hE2 : IsPGroup 2 E := hS2.to_le hES
      have haE : h.a ∈ E := mem_inf.mpr ⟨QuotAux.a_mem_P h, Subgroup.mem_comap.mpr haE'⟩
      obtain ⟨L, hL⟩ := h.isoCorr_of_mem E hEP haE
      refine ⟨L.map π, ?_⟩
      rw [← hEmap]
      exact OddQuot.isoCorrSub_map hE2 (hES.trans hSN) h.orderOf_a hL
    x_mem := mem_map_of_mem π h.x_mem
    inf_conjugate_x := hinf
    x_sq_mem := by
      rw [← map_pow]
      exact hT.le (mem_map_of_mem π h.x_sq_mem)
    sylow_layer := by
      obtain ⟨R, hR1, hR2, hR3⟩ := h.sylow_layer
      refine ⟨R.map π, ?_, ?_, ?_⟩
      · exact (map_mono hR1).trans (le_inf (map_mono inf_le_left)
          ((map_mono inf_le_right).trans (le_normalizer_map π)))
      · rw [hX9map, h9]
        exact map_mono hR2
      · rw [hX9map, h9]
        exact OddQuot.exists_sylow_map π hR2 hR3
    isPComponent_K := by
      rw [hW]
      exact ⟨map_mono h.isPComponent_K.1, OddQuot.isPComponent_map π hO h.isPComponent_K.1
        h.isPComponent_K.2⟩
    layer_eq_K := by
      rw [← map_conjugate, ← Subgroup.map_sup, h.layer_eq_K, hlayer]
    type_K := by
      rcases h.type_K with hR | ⟨hne, ⟨eKJ⟩⟩
      · exact Or.inl (OddQuot.gsRestricted_of_mulEquiv eK hR)
      · refine Or.inr ⟨fun heq => hne ?_, ⟨eK.symm.trans (eKJ.trans eJ)⟩⟩
        obtain ⟨haX, hac⟩ := OddQuot.isPComponent_conjugate_subgroupOf h.a_mem_normalizer
          h.isPComponent_K.1 h.isPComponent_K.2
        exact OddQuot.eq_of_map_eq π hO haX h.isPComponent_K.1 hac h.isPComponent_K.2
          (by rw [map_conjugate]; exact heq) }, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Hyp52W

end CFSG.ComponentClassification.GSThmB

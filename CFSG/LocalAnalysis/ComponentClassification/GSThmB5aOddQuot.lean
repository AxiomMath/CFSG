module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitContainmentTransfer

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace OddQuot

variable {H : Type*} [Group H] [Finite H]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 H)

theorem le_normalizer_layerIn (X : Subgroup H) : X ≤ normalizer (layerIn X : Set H) := by
  intro w hw
  have : (pLayer X 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  have : (pLayer X 2).Normal := inferInstance
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨n, hn, rfl⟩ := mem_map.mp hy
    exact mem_map.mpr ⟨⟨w, hw⟩ * n * ⟨w, hw⟩⁻¹, this.conj_mem n hn _, rfl⟩
  · intro hy
    obtain ⟨n, hn, hny⟩ := mem_map.mp hy
    have h1 := this.conj_mem n hn ⟨w, hw⟩⁻¹
    refine mem_map.mpr ⟨⟨w, hw⟩⁻¹ * n * ⟨w, hw⟩⁻¹⁻¹, h1, ?_⟩
    change w⁻¹ * (n : H) * w⁻¹⁻¹ = y
    have hny' : (n : H) = w * y * w⁻¹ := hny
    rw [hny']
    group

omit [Finite H] in
theorem isPComponent_conjugate_subgroupOf {L X : Subgroup H} {g : H} (hg : g ∈ X)
    (hLX : L ≤ X) (hL : IsPComponent 2 (L.subgroupOf X)) :
    conjugate L g ≤ X ∧ IsPComponent 2 ((conjugate L g).subgroupOf X) := by
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [mem_conjugate_iff] at hy
    have h := mul_mem (mul_mem (inv_mem hg) (hLX hy)) hg
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h
  · have h := isPComponent_conjugate hL (⟨g, hg⟩ : X)
    rwa [conjugate_subgroupOf_eq] at h

omit [Finite H] in
theorem mem_normalizer_of_map {W X : Subgroup H} {y : H} (hXW : X ≤ W)
    (hWO : W ⊓ pPrimeCore 2 H ≤ X) (hy : y ∈ W)
    (hy' : π y ∈ normalizer ((X.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H))) :
    y ∈ normalizer (X : Set H) := by
  have key : ∀ z ∈ W, π z ∈ normalizer ((X.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) →
      ∀ x ∈ X, z * x * z⁻¹ ∈ X := by
    intro z hz hz' x hx
    have h1 : π (z * x * z⁻¹) ∈ X.map π := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hz' (π x)).mp (mem_map_of_mem π hx)
    obtain ⟨x', hx', hxx'⟩ := mem_map.mp h1
    have h2 : x'⁻¹ * (z * x * z⁻¹) ∈ W ⊓ pPrimeCore 2 H := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem (hXW hx'))
        (mul_mem (mul_mem hz (hXW hx)) (inv_mem hz)), ?_⟩
      rw [← QuotientGroup.ker_mk' (pPrimeCore 2 H), MonoidHom.mem_ker, map_mul, map_inv, hxx',
        inv_mul_cancel]
    have h3 := mul_mem hx' (hWO h2)
    rwa [mul_inv_cancel_left] at h3
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key y hy hy' x, fun hx => ?_⟩
  have h1 := key y⁻¹ (inv_mem hy) (by rw [map_inv]; exact inv_mem hy') _ hx
  rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at h1

theorem map_inf_normalizer {S E : Subgroup H} (hS : IsPGroup 2 S) (hES : E ≤ S) :
    (S ⊓ normalizer (E : Set H)).map π =
      S.map π ⊓ normalizer ((E.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) := by
  refine le_antisymm (le_inf (map_mono inf_le_left)
    ((map_mono inf_le_right).trans (le_normalizer_map π))) ?_
  rintro _ ⟨⟨s, hs, rfl⟩, hsN⟩
  refine mem_map_of_mem π (mem_inf.mpr ⟨hs, ?_⟩)
  have hconj : conjugate E s⁻¹ ≤ S := by
    intro y hy
    rw [mem_conjugate_iff, inv_inv] at hy
    have h := mul_mem (mul_mem hs (hES hy)) (inv_mem hs)
    rwa [show s * (s⁻¹ * y * s) * s⁻¹ = y by group] at h
  have hmap : (conjugate E s⁻¹).map π = E.map π := by
    rw [map_conjugate, map_inv]
    exact conjugate_eq_of_mem_normalizer (inv_mem hsN)
  have heq : conjugate E s⁻¹ = E :=
    le_antisymm (le_of_map_le hS hconj hES hmap.le) (le_of_map_le hS hES hconj hmap.ge)
  rw [mem_normalizer_iff]
  intro y
  have h1 : s * y * s⁻¹ ∈ conjugate E s⁻¹ ↔ s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ ∈ E := mem_conjugate_iff
  rw [heq, show s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y by group] at h1
  exact h1.symm

theorem isoCorrSub_map {a : H} {J E L : Subgroup H} (hE : IsPGroup 2 E)
    (hEJ : E ≤ normalizer (J : Set H)) (ha : orderOf a = 2) (hc : IsoCorrSub a J E L) :
    IsoCorrSub (π a) (J.map π) (E.map π) (L.map π) := by
  have hO := not_two_dvd_card_ker (H := H)
  obtain ⟨hLN, hLc, hLa, hsup, hfix⟩ := hc
  have hza : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ha, pow_one])
  have haL : zpowers a ≤ normalizer (L : Set H) :=
    zpowers_le.mpr (mem_normalizer_of_conjugate_eq hLa)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [normalizer_map_eq hE]
    exact map_mono hLN
  · rw [normalizer_map_eq hE]
    exact isPComponent_map π hO hLN hLc
  · rw [← map_conjugate, hLa]
  · rw [← map_fixedLayer hE hEJ, ← map_oddCoreIn π hO L, ← Subgroup.map_sup, hsup]
  · rw [← map_fixedLayer hE hEJ, hfix, map_layerIn π hO, ← centralizer_zpowers_eq,
      ← centralizer_zpowers_eq,
      map_inf_centralizer π hza haL (not_two_dvd_card_ker_domRestrict π hO L),
      MonoidHom.map_zpowers]

end OddQuot

namespace Hyp52

variable {H : Type} [Group H] [Finite H]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 H)

theorem quotient_oddCore (h : Hyp52 H) :
    ∃ h' : Hyp52 (H ⧸ pPrimeCore 2 H), h'.a = π h.a ∧ h'.J = h.J.map π ∧ h'.S = h.S.map π ∧
      h'.B = h.B.map π ∧ h'.K = h.K.map π ∧ h'.x = π h.x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := OddQuot.not_two_dvd_card_ker (H := H)
  have hS2 : IsPGroup 2 h.S := B5a.isPGroup_S h
  have hB2 : IsPGroup 2 h.B := B5a.isPGroup_B h
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
    isoCorr_of_lt := by
      intro E' hE' hcard
      rw [← hP] at hE'
      set E := (h.S ⊓ coreActionKernel h.J) ⊓ E'.comap π with hE
      have hEmap : E.map π = E' := OddQuot.map_inf_comap_eq hE'
      have hEP : E ≤ h.S ⊓ coreActionKernel h.J := inf_le_left
      have hES : E ≤ h.S := hEP.trans inf_le_left
      have hE2 : IsPGroup 2 E := hS2.to_le hES
      have hcE : Nat.card (E.map π) = Nat.card E := OddQuot.card_map_of_isPGroup hE2
      have hcB : Nat.card (h.B.map π) = Nat.card h.B := OddQuot.card_map_of_isPGroup hB2
      have hcN : ∀ F : Subgroup H, F ≤ h.S →
          Nat.card ↥(h.S.map π ⊓ normalizer ((F.map π : Subgroup _) :
            Set (H ⧸ pPrimeCore 2 H))) = Nat.card ↥(h.S ⊓ normalizer (F : Set H)) := by
        intro F hF
        rw [← OddQuot.map_inf_normalizer hS2 hF,
          OddQuot.card_map_of_isPGroup (hS2.to_le inf_le_left)]
      have hcard' : Nat.card h.B < Nat.card E ∨ (Nat.card E = Nat.card h.B ∧
          Nat.card ↥(h.S ⊓ normalizer (h.B : Set H)) <
            Nat.card ↥(h.S ⊓ normalizer (E : Set H))) := by
        rw [← hEmap] at hcard
        rw [hcN h.B hBS, hcN E hES, hcE, hcB] at hcard
        exact hcard
      obtain ⟨L, hL⟩ := h.isoCorr_of_lt E hEP hcard'
      refine ⟨L.map π, ?_⟩
      rw [← hEmap]
      exact OddQuot.isoCorrSub_map hE2 (hES.trans hSN) h.orderOf_a hL
    x_mem := mem_map_of_mem π h.x_mem
    inf_conjugate_x := hinf
    x_sq_mem := by
      rw [← map_pow]
      have h2 : (h.S ⊓ coreActionKernel h.J ⊓ normalizer (h.B : Set H)).map π ≤
          h.S.map π ⊓ coreActionKernel (h.J.map π) ⊓
            normalizer ((h.B.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) :=
        le_inf ((map_mono inf_le_left).trans hP.le)
          ((map_mono inf_le_right).trans (le_normalizer_map π))
      exact h2 (mem_map_of_mem π h.x_sq_mem)
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

end Hyp52

end CFSG.ComponentClassification.GSThmB

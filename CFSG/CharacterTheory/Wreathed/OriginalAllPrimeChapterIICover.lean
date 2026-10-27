module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeChapterIIQGroup
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeSettingValid
public import CFSG.CharacterTheory.Wreathed.ComponentCoverFactorizations
import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion CFSG.ABGLocalTools ChapterII
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

open SmallerRecognitionOriginalField ComponentCoverFactorizations in
theorem wreathedSetting_cover_qgroup
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G) :
    ∀ H : Subgroup G, (wreathedSetting n S e p f).T ≤ H → oddCoreIn H ≠ ⊥ →
      ((wreathedSetting n S e p f).L₀ : Set G) ⊆
        (H : Set G) * ((wreathedSetting n S e p f).ON : Set G) →
        CFSG.ABGQGroups.HasQCharPower H (wreathedSetting n S e p f).q ∧
          oddCoreIn H ⊔ (H ⊓ (wreathedSetting n S e p f).N) = H := by
  intro H hTH hO hcov
  have hσ := wreathedSetting_isValid hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  set σ := wreathedSetting n S e p f with hσdef
  set N := involutionCentralizer n S e
  set π := centralizerOddCoreMap n S e
  have hxH : wreathModelHom S e (Original.x (2 ^ n)) ∈ H := hTH σ.x_mem_T
  have hO' : CFSG.oddCore H ≠ ⊥ := fun h => hO (by rw [oddCoreIn, h, Subgroup.map_bot])
  have hproper : H < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    have hnorm : (oddCoreIn H).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      exact le_normalizer_oddCoreIn H (htop ▸ Subgroup.mem_top g)
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exact hO h
    · have hodd := odd_card_oddCoreIn H
      rw [h, Subgroup.card_top] at hodd
      have h2 : 2 ∣ Nat.card G := by
        rw [← hσ.x_order]
        exact orderOf_dvd_natCard _
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e H := by
    intro m hm
    obtain ⟨l, rfl⟩ := centralizerOddCoreMap_surjective n S e m
    have hl : (l : G) ∈ σ.L₀ := ⟨l, hm, rfl⟩
    obtain ⟨k, hk, o, ho, hko⟩ := hcov hl
    have ho2 : o ∈ (centralizerOddCore n S e).map N.subtype := ho
    obtain ⟨o', ho', rfl⟩ := ho2
    have hko' : k = (l : G) * (o' : G)⁻¹ := by
      rw [← hko]
      simp
    have hkN : k ∈ N := hko' ▸ N.mul_mem l.property (N.inv_mem o'.property)
    refine ⟨⟨k, hkN⟩, hk, ?_⟩
    have hkl : (⟨k, hkN⟩ : N) = l * o'⁻¹ := Subtype.ext hko'
    have ho'1 : π o' = 1 := (QuotientGroup.eq_one_iff o').mpr ho'
    rw [hkl, map_mul, map_inv, ho'1, inv_one, mul_one]
  obtain ⟨hfac, -, hint⟩ :=
    smaller_recognition_factors_every_involution_containing_component_covering_subgroup
      hnonab n hn S e hfour p f hp hpodd hf hq.le hlocal hrec H hproper hxH hcover hO'
  have hfac' : ∀ h ∈ H, ∃ a ∈ CFSG.oddCore H, ∃ b ∈ H ⊓ N, (a : G) * b = h := by
    intro h hh
    have h' : h ∈ ((CFSG.oddCore H).map H.subtype : Set G) * (H ⊓ N : Set G) := by
      rw [← hfac]
      exact hh
    obtain ⟨_, ⟨a, ha, rfl⟩, b, hb, hab⟩ := h'
    exact ⟨a, ha, b, hb, hab⟩
  have hsup : oddCoreIn H ⊔ (H ⊓ σ.N) = H := by
    apply le_antisymm (sup_le (oddCoreIn_le H) inf_le_left)
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := hfac' h hh
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, ha, rfl⟩) (Subgroup.mem_sup_right hb)
  refine ⟨⟨?_, hpodd.pow, ?_⟩, hsup⟩
  ·
    set J := H.subgroupOf N
    have hQJb : IsQGroup (ComponentCoveringLocal.originalImage n S e H) :=
      isQGroup_of_layer_le hnonab n hn S e hfour _ hcover
    have hkerπ : Odd (Nat.card π.ker) := by
      rw [show π.ker = centralizerOddCore n S e from QuotientGroup.ker_mk' _]
      exact centralizerOddCore_card_odd n S e
    have hQJ : IsQGroup J :=
      (isQGroup_iff_of_oddKernel (π.subgroupMap J) (π.subgroupMap_surjective J)
        (odd_card_ker_subgroupMap π hkerπ J)).mp hQJb
    let ψ : J →* H := (N.subtype.comp J.subtype).codRestrict H (fun j => j.2)
    have hψ : Function.Injective ψ := by
      intro a b hab
      have h : ((ψ a : H) : G) = ((ψ b : H) : G) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
    let φ : J →* H ⧸ CFSG.oddCore H := (QuotientGroup.mk' (CFSG.oddCore H)).comp ψ
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore H) y
      obtain ⟨a, ha, b, ⟨hbH, hbN⟩, hab⟩ := hfac' h h.2
      have hbJ : (⟨b, hbN⟩ : N) ∈ J := hbH
      refine ⟨⟨⟨b, hbN⟩, hbJ⟩, ?_⟩
      have hh : h = a * ψ ⟨⟨b, hbN⟩, hbJ⟩ := Subtype.ext hab.symm
      have ha1 : QuotientGroup.mk' (CFSG.oddCore H) a = 1 :=
        (QuotientGroup.eq_one_iff a).mpr ha
      change QuotientGroup.mk' _ (ψ _) = QuotientGroup.mk' _ h
      rw [hh, map_mul, ha1, one_mul]
    have hφker : Odd (Nat.card φ.ker) := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact (odd_card_oddCore H).of_dvd_nat (Subgroup.card_comap_dvd_of_injective _ ψ hψ)
    exact isQGroup_quotient_oddCore_iff.mp ((isQGroup_iff_of_oddKernel φ hφ hφker).mpr hQJ)
  ·
    obtain ⟨F, hF, hFfin, hFcard, ψ₀, hψ₀, hker₀⟩ := hσ.L₀_quotient
    set Λ : Subgroup H := σ.L₀.subgroupOf H
    set πH := QuotientGroup.mk' (CFSG.oddCore H)
    have hOL : ∀ x : H, (x : G) ∈ σ.L₀ → (x ∈ CFSG.oddCore H ↔ (x : G) ∈ σ.ON) := by
      intro x hxL
      have hxN : (x : G) ∈ N := hσ.L₀_le_N hxL
      constructor
      · intro hx
        have hmem : (x : G) ∈ (CFSG.oddCore H).map H.subtype ⊓ N := ⟨⟨x, hx, rfl⟩, hxN⟩
        rw [hint] at hmem
        exact hmem.1
      · intro hx
        have hmem : (x : G) ∈ (centralizerOddCore n S e).map N.subtype ⊓ H := ⟨hx, x.2⟩
        rw [← hint] at hmem
        exact (Subgroup.mem_map_iff_mem H.subtype_injective).mp hmem.1
    let incl : Λ →* σ.L₀ := (H.subtype.comp Λ.subtype).codRestrict σ.L₀ (fun x => x.2)
    let ψΛ : Λ →* Matrix.SpecialLinearGroup (Fin 2) F := ψ₀.comp incl
    have hψΛ : Function.Surjective ψΛ := by
      intro y
      obtain ⟨l, rfl⟩ := hψ₀ y
      obtain ⟨h, hh, o, ho, hho⟩ := hcov l.2
      have hoL : o ∈ σ.L₀ := hσ.ON_le_L₀ ho
      have hhL : h ∈ σ.L₀ := by
        have h1 := σ.L₀.mul_mem l.2 (σ.L₀.inv_mem hoL)
        rwa [← hho, mul_inv_cancel_right] at h1
      refine ⟨⟨⟨h, hh⟩, hhL⟩, ?_⟩
      have hl : l = ⟨h, hhL⟩ * ⟨o, hoL⟩ := Subtype.ext hho.symm
      have ho1 : ψ₀ ⟨o, hoL⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hker₀]
        exact ho
      change ψ₀ ⟨h, hhL⟩ = ψ₀ l
      rw [hl, map_mul, ho1, mul_one]
    have hkerEq : (πH.subgroupMap Λ).ker = ψΛ.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Subtype.coe_inj,
        MonoidHom.subgroupMap_apply_coe, OneMemClass.coe_one, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      change _ ↔ ψ₀ (incl x) = 1
      rw [← MonoidHom.mem_ker, hker₀]
      exact hOL x x.2
    let eΛ : Λ.map πH ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
      (QuotientGroup.quotientKerEquivOfSurjective _ (πH.subgroupMap_surjective Λ)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
          (QuotientGroup.quotientKerEquivOfSurjective ψΛ hψΛ))
    have hnormal : (Λ.map πH).Normal := by
      constructor
      rintro _ ⟨l, hl, rfl⟩ y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore H) y
      obtain ⟨a, ha, b, ⟨-, hbN⟩, hab⟩ := hfac' h h.2
      have hb : ((a⁻¹ * h : H) : G) = b := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hab, inv_mul_cancel_left]
      refine ⟨(a⁻¹ * h) * l * (a⁻¹ * h)⁻¹, ?_, ?_⟩
      · change (((a⁻¹ * h) * l * (a⁻¹ * h)⁻¹ : H) : G) ∈ σ.L₀
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hb]
        exact (Subgroup.mem_normalizer_iff.mp (hσ.N_le_normalizer_L₀ hbN) _).mp hl
      · have hπa : πH a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
        change πH ((a⁻¹ * h) * l * (a⁻¹ * h)⁻¹) = πH h * πH l * (πH h)⁻¹
        rw [map_mul, map_mul, map_inv, map_mul, map_inv, hπa, inv_one, one_mul]
    exact ⟨Λ.map πH, F, hF, hFfin, hnormal, hFcard, ⟨eΛ⟩⟩

end CFSG.Wreathed.OriginalAllPrime

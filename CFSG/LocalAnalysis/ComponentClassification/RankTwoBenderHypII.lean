module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderHypIICore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Linear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvolutionInner

public section

namespace CFSG.ComponentClassification.RankTwoBender

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

theorem e4Inner_of_bender {X : Type} [Group X] [Finite X] (hX : fusionIsBenderGroup X) :
    E4Inner X := by
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact e4Inner_of_mulEquiv_psl2 hf e
  · exact e4Inner_of_mulEquiv_psu3 hf e
  · intro α _ hα _ _
    exact Or.inl (CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover.exists_eq_conj_of_suzuki
      ha e α hα)

theorem fusionIsBenderGroup_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : fusionIsBenderGroup Y) : fusionIsBenderGroup X := by
  rcases hY with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.trans e'⟩⟩)

section Elements

variable {G : Type*} [Group G]

theorem isPGroup_zpowers_of_mul_self' {g : G} (hg : g * g = 1) : IsPGroup 2 (zpowers g) := by
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hg])
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem mem_of_mem_normalizer_of_mul_self [Finite G] (U : Sylow 2 G) {g : G}
    (hgN : g ∈ normalizer ((U : Subgroup G) : Set G)) (hg : g * g = 1) : g ∈ (U : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers g ⊔ (U : Subgroup G) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_mul_self' hg) U.isPGroup'
      (zpowers_le.mpr hgN)
  have heq := U.is_maximal' hp le_sup_right
  exact heq ▸ (le_sup_left : zpowers g ≤ _) (mem_zpowers g)

end Elements

theorem mem_sup_centralizer_of_inner {H : Type*} [Group H] {B : Subgroup H} {t : H}
    (ht : t ∈ normalizer (B : Set H)) {b : B}
    (hb : B.normalizerMonoidHom ⟨t, ht⟩ = MulAut.conj b) :
    t ∈ B ⊔ centralizer (B : Set H) := by
  have hc : (b : H)⁻¹ * t ∈ centralizer (B : Set H) := by
    rw [mem_centralizer_iff]
    intro z hz
    have h := congrArg (fun φ : MulAut B => ((φ ⟨z, hz⟩ : B) : H)) hb
    simp only [normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply, coe_mul, coe_inv] at h
    calc z * ((b : H)⁻¹ * t) = (b : H)⁻¹ * (b * z * (b : H)⁻¹) * t := by group
      _ = (b : H)⁻¹ * (t * z * t⁻¹) * t := by rw [h]
      _ = (b : H)⁻¹ * t * z := by group
  have := mul_mem_sup b.2 hc
  rwa [mul_inv_cancel_left] at this

theorem hypII_of_bender {A : Type} [Group A] [Finite A] (hA : fusionIsBenderGroup A) :
    HypII A := by
  intro H _ _ B T ⟨eB⟩ hTF hTX
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTe, hT4, hTN, hTC⟩ := hTF
  obtain ⟨X, hXP, hTsyl, hX2, htight⟩ := hTX
  have : Finite B := Finite.of_equiv A eB.symm.toEquiv
  have hBb : fusionIsBenderGroup B := fusionIsBenderGroup_of_mulEquiv' eB hA
  have : IsSimpleGroup B := isSimpleGroup_of_bender hBb
  have hZ : center B = ⊥ := center_eq_bot_of_bender hBb
  have hPN : T ⊔ B ≤ normalizer (B : Set H) := sup_le hTN le_normalizer
  have hXN : X ≤ normalizer (B : Set H) := hXP.trans hPN
  have hTX : T ≤ X := hTsyl.le
  have hBP : B ≤ T ⊔ B := le_sup_right
  let α : T →* MulAut B := B.normalizerMonoidHom.comp (inclusion hTN)
  have hT2 : ∀ t : T, t * t = 1 := fun t => Subtype.ext (by
    have := hTe.2 t t.2
    rwa [sq] at this)
  have hα2 : ∀ t : T, α t * α t = 1 := by
    intro t
    rw [← map_mul, hT2 t, map_one]
  have hαcomm : ∀ t u : T, α t * α u = α u * α t := by
    intro t u
    rw [← map_mul, ← map_mul, hTe.1.is_comm.comm t u]
  have hαker : ∀ t : T, α t = 1 → t = 1 := by
    intro t ht
    have hmem : (inclusion hTN t : normalizer (B : Set H)) ∈ B.normalizerMonoidHom.ker := ht
    rw [normalizerMonoidHom_ker, mem_subgroupOf] at hmem
    have : (t : H) ∈ T ⊓ centralizer (B : Set H) := ⟨t.2, hmem⟩
    rw [hTC] at this
    exact Subtype.ext (mem_bot.mp this)
  have hinner : ∀ t : T, (∃ b : B, α t = MulAut.conj b) → (t : H) ∈ B ⊔ centralizer (B : Set H) :=
    fun t ⟨b, hb⟩ => mem_sup_centralizer_of_inner (hTN t.2) hb
  intro t ht
  by_contra hout
  set t' : T := ⟨t, ht⟩ with ht'
  have hout' : ¬ ∃ b : B, α t' = MulAut.conj b := fun h => hout (hinner t' h)
  have ht'1 : t' ≠ 1 := by
    rintro h
    apply hout'
    refine ⟨1, ?_⟩
    rw [h, map_one, map_one]
  obtain ⟨u, hu1, hut⟩ : ∃ u : T, u ≠ 1 ∧ u ≠ t' := by
    by_contra hall
    push Not at hall
    have hinj : Function.Injective fun v : T => decide (v = 1) := by
      intro v w hvw
      by_cases hv : v = 1
      · have hw : w = 1 := by simpa [hv] using hvw.symm
        rw [hv, hw]
      · have hw : w ≠ 1 := by simpa [hv] using hvw.symm
        rw [hall v hv, hall w hw]
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    omega
  obtain ⟨s, hs1, ⟨b, hsb⟩⟩ : ∃ s : T, s ≠ 1 ∧ ∃ b : B, α s = MulAut.conj b := by
    rcases e4Inner_of_bender hBb (α t') (α u) (hα2 t') (hα2 u) (hαcomm t' u) with h | h | h
    · exact absurd h hout'
    · exact ⟨u, hu1, h⟩
    · refine ⟨t' * u, ?_, ?_⟩
      · intro h1
        apply hut
        rw [mul_eq_one_iff_eq_inv.mp h1, inv_eq_of_mul_eq_one_right (hT2 u)]
      · rwa [map_mul]
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hs1 (hαker s (by rw [hsb, map_one]))
  have hb2 : b * b = 1 := by
    have h : MulAut.conj (b * b) = 1 := by rw [map_mul, ← hsb, hα2]
    have hbZ : b * b ∈ center B := by
      rw [mem_center_iff]
      intro y
      have h' := DFunLike.congr_fun h y
      simp only [MulAut.conj_apply, MulAut.one_apply] at h'
      calc y * (b * b) = b * b * y * (b * b)⁻¹ * (b * b) := by rw [h']
        _ = b * b * y := by group
    rw [hZ] at hbZ
    exact mem_bot.mp hbZ
  set c : H := (b : H)⁻¹ * s with hcdef
  have hc : c ∈ centralizer (B : Set H) := by
    rw [mem_centralizer_iff]
    intro z hz
    have h := congrArg (fun φ : MulAut B => ((φ ⟨z, hz⟩ : B) : H)) hsb
    simp only [α, MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe, coe_inclusion,
      MulAut.conj_apply, coe_mul, coe_inv] at h
    calc z * ((b : H)⁻¹ * s) = (b : H)⁻¹ * (b * z * (b : H)⁻¹) * s := by group
      _ = (b : H)⁻¹ * (s * z * (s : H)⁻¹) * s := by rw [h]
      _ = (b : H)⁻¹ * s * z := by group
  have hsbc : (s : H) = b * c := by rw [hcdef, mul_inv_cancel_left]
  have hsX : (s : H) ∈ X := hTX s.2
  have hsH1 : (s : H) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hsH2 : (s : H) * s = 1 := by
    have := hTe.2 s s.2
    rwa [sq] at this
  obtain ⟨U, hbU⟩ := (isPGroup_zpowers_of_mul_self' hb2).exists_le_sylow
  have hbU' : b ∈ (U : Subgroup B) := hbU (mem_zpowers b)
  let F : Subgroup B :=
    { carrier := {x | ∃ c' : H, c' ∈ centralizer (B : Set H) ∧ (x : H) * c' ∈ X}
      one_mem' := ⟨1, one_mem _, by rw [coe_one, mul_one]; exact one_mem X⟩
      mul_mem' := by
        rintro x y ⟨c₁, hc₁, hx⟩ ⟨c₂, hc₂, hy⟩
        refine ⟨c₁ * c₂, mul_mem hc₁ hc₂, ?_⟩
        have hc₁y : c₁ * (y : H) = y * c₁ := (mem_centralizer_iff.mp hc₁ y y.2).symm
        have key : ((x * y : B) : H) * (c₁ * c₂) = ((x : H) * c₁) * ((y : H) * c₂) := by
          rw [coe_mul]
          calc (x : H) * y * (c₁ * c₂) = x * (y * c₁) * c₂ := by group
            _ = x * (c₁ * y) * c₂ := by rw [hc₁y]
            _ = (x * c₁) * (y * c₂) := by group
        rw [key]
        exact mul_mem hx hy
      inv_mem' := by
        rintro x ⟨c₁, hc₁, hx⟩
        refine ⟨c₁⁻¹, inv_mem hc₁, ?_⟩
        have hc₁x : c₁ * (x : H) = x * c₁ := (mem_centralizer_iff.mp hc₁ x x.2).symm
        have : ((x : H) * c₁)⁻¹ = (x : H)⁻¹ * c₁⁻¹ := by rw [← hc₁x, mul_inv_rev]
        rw [coe_inv, ← this]
        exact inv_mem hx }
  have hbF : b ∈ F := ⟨c, hc, by rw [← hsbc]; exact hsX⟩
  have hFnorm : ∀ y : B, (y : H) ∈ normalizer (X : Set H) → ∀ x ∈ F, y * x * y⁻¹ ∈ F := by
    rintro y hy x ⟨c₁, hc₁, hx⟩
    refine ⟨c₁, hc₁, ?_⟩
    have hc₁y : c₁ * (y : H)⁻¹ = (y : H)⁻¹ * c₁ :=
      (mem_centralizer_iff.mp hc₁ _ (B.inv_mem y.2)).symm
    rw [coe_mul, coe_mul, coe_inv, show (y : H) * x * (y : H)⁻¹ * c₁ = y * x * (c₁ * (y : H)⁻¹)
      by rw [hc₁y]; group, show (y : H) * x * (c₁ * (y : H)⁻¹) = y * (x * c₁) * (y : H)⁻¹ by group]
    exact (mem_normalizer_iff.mp hy _).mp hx
  have hFnorm' : ∀ y : B, (y : H) ∈ normalizer (X : Set H) →
      y ∈ normalizer ((F : Subgroup B) : Set B) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hFnorm y hy x, fun h => ?_⟩
    have := hFnorm y⁻¹ (by rw [coe_inv]; exact inv_mem hy) _ h
    rwa [inv_inv, show y⁻¹ * (y * x * y⁻¹) * y = x by group] at this
  have hUX : ∀ v ∈ (U : Subgroup B), (v : H) ∈ normalizer (X : Set H) := by
    intro v hv
    have hvb : v * b = b * v :=
      (mem_centralizer_iff.mp (mem_centralizer_of_involution hBb U hbU' (by rw [sq, hb2])) v hv)
    have hvc : (v : H) * c = c * v := mem_centralizer_iff.mp hc v v.2
    refine mem_normalizer_of_commute_involution hXP htight hsX hsH1 hsH2 (hBP v.2) ?_
    rw [hsbc, ← mul_assoc, show (v : H) * b = b * v from congrArg Subtype.val hvb, mul_assoc,
      hvc, ← mul_assoc]
  have hUF : (U : Subgroup B) ≤ normalizer ((F : Subgroup B) : Set B) :=
    fun v hv => hFnorm' v (hUX v hv)
  have hFU : F ≤ normalizer ((U : Subgroup B) : Set B) := by
    rcases le_normalizer_or_eq_top hBb U (le_sup_left : (U : Subgroup B) ≤ (U : Subgroup B) ⊔ F)
      with hK | hK
    · exact le_sup_right.trans hK
    · exfalso
      have hFn : F.Normal := by
        rw [← normalizer_eq_top_iff, eq_top_iff, ← hK]
        exact sup_le hUF le_normalizer
      rcases hFn.eq_bot_or_eq_top with hF | hF
      · rw [hF] at hbF
        exact hb1 (mem_bot.mp hbF)
      · refine false_of_twoNilpotent_cover inferInstance hZ (even_card_of_bender hBb) hXN hX2 ?_
        intro x hx
        have : (⟨x, hx⟩ : B) ∈ F := hF ▸ mem_top _
        exact this
  have ht2 : (t : H) * t = 1 := by
    have := hTe.2 t ht
    rwa [sq] at this
  have htH1 : (t : H) ≠ 1 := fun h => ht'1 (Subtype.ext h)
  have hfix : ∀ x : B, α t' x = x → x ∈ normalizer ((U : Subgroup B) : Set B) := by
    intro x hx
    have hxt : (x : H) * t = t * x := by
      have h := congrArg Subtype.val hx
      simp only [α, MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe,
        coe_inclusion] at h
      calc (x : H) * t = t * x * t⁻¹ * t := by rw [h]
        _ = t * x := by group
    have hxX := mem_normalizer_of_commute_involution hXP htight (hTX ht) htH1 ht2 (hBP x.2) hxt
    have hxbF : x * b * x⁻¹ ∈ F := hFnorm x hxX b hbF
    have hxbU : x * b * x⁻¹ ∈ (U : Subgroup B) :=
      mem_of_mem_normalizer_of_mul_self U (hFU hxbF)
        (by rw [show x * b * x⁻¹ * (x * b * x⁻¹) = x * (b * b) * x⁻¹ by group, hb2, mul_one,
          mul_inv_cancel])
    have hbx : b ∈ ((x⁻¹ • U : Sylow 2 B) : Subgroup B) := by
      rw [Omega.mem_conj_smul_iff, inv_inv]
      exact hxbU
    have := eq_of_mem_of_mem hBb hb1 hbx hbU'
    have hxinv : x⁻¹ ∈ normalizer ((U : Subgroup B) : Set B) :=
      Sylow.smul_eq_iff_mem_normalizer.mp this
    simpa using inv_mem hxinv
  obtain ⟨y, hy⟩ := bender_involution_automorphism_inner B hBb (α t') (hα2 t') ⟨U, hfix⟩
  exact hout' ⟨y, hy⟩

end CFSG.ComponentClassification.RankTwoBender

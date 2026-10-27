module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4HomoDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

@[expose] def GMS42Residual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T U₁ : Subgroup G), Sec3 G L T → Foundation →
    Nonempty (rankTwoQuot L ≃* PSL(2, GaloisField 2 4)) → Sec3.Facts L T (2 ^ 4) →
    Lemma313 L T (2 ^ 4) → Sec4Homo L T U₁ (2 ^ 4) →
    Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4 →
    (∃ t₀ ∈ T ⊓ centralizer (L : Set G), t₀ ≠ 1 ∧ ∀ u ∈ U₁, t₀ * u * t₀⁻¹ = u⁻¹) →
    ¬ T ≤ gmsV L T →
    ∀ v ∈ gmsV L T, ∀ g : G, g * v * g⁻¹ ∈ U₁ ⊔ T → g * v * g⁻¹ ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G))

@[expose] def GMS42ResidualU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T U₁ : Subgroup G), Sec3 G L T → Foundation →
    Nonempty (rankTwoQuot L ≃* PSL(2, GaloisField 2 4)) → Sec3.Facts L T (2 ^ 4) →
    Lemma313 L T (2 ^ 4) → Sec4Homo L T U₁ (2 ^ 4) →
    Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4 → ¬ T ≤ gmsV L T →
    ∀ (U : Subgroup G) (g : G), U ≤ gmsV L T → IsElemAbelian 2 (rightConjugate U g) →
    rightConjugate U g ≤ U₁ ⊔ T →
    (∀ x ∈ rightConjugate U g, Nat.card (⁅gmsV L T, zpowers x⁆ : Subgroup G) ≤ 4) →
    ∀ u ∈ U₁, u ∉ gmsA L T → ∀ t₀ ∈ T ⊓ centralizer (L : Set G), t₀ ≠ 1 →
    (∀ v ∈ U₁, t₀ * v * t₀⁻¹ = v⁻¹) → u * t₀ ∈ rightConjugate U g →
    ∀ w ∈ rightConjugate U g, w ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G)) →
    Nat.card (gmsV L T ⊓ centralizer ({w} : Set G) : Subgroup G) = 16 → False

variable {G : Type} [Group G] [Finite G]

namespace Sec4Homo

variable {L T U₁ : Subgroup G} {f : ℕ}

theorem inf_A_bound (hE : Sec4Homo L T U₁ (2 ^ f))
    (h : Sec3 G L T) (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f))
    (hX : Sec3.Facts L T (2 ^ f)) {x : G} (hx : x ∈ U₁ ⊔ T) (hxx : x * x = 1)
    (hxW : x ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G))) {D : Subgroup G} (hDV : D ≤ gmsV L T)
    (hDC : D ≤ centralizer ({x} : Set G)) :
    Nat.card D * 2 ^ f ≤ Nat.card (gmsV L T) * Nat.card (D ⊓ gmsA L T : Subgroup G) ∧
      Nat.card (D ⊓ gmsA L T : Subgroup G) ^ 2 ≤ 2 ^ f := by
  refine ⟨?_, ?_⟩
  · have h1 := card_mul_card_le hDV (le_sup_left : gmsA L T ≤ gmsV L T)
    rwa [(hX.sylow h).1] at h1
  · have h1 := hE.card_sq_le_of_involution h hf e hX hx hxx hxW
    have h2 : Nat.card (D ⊓ gmsA L T : Subgroup G) ≤
        Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) : Subgroup G) :=
      card_le_of_le (le_inf inf_le_right (inf_le_left.trans hDC))
    exact (Nat.pow_le_pow_left h2 2).trans h1

theorem rightConjugate_eq
    (hE : Sec4Homo L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f)) {g : G}
    (hg : rightConjugate (gmsV L T) g ≤ U₁ ⊔ T) : rightConjugate (gmsV L T) g = gmsV L T := by
  have hT₀ := h.isElemAbelian_T₀ hF
  obtain ⟨hVcard, hVel, -, -, -⟩ := hX.vFacts h hF
  have hA := (hX.sylow h).1
  have hT₀4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) := by
    obtain ⟨F, hF4, -, hF4c⟩ := h.exists_four_le
    rw [← hF4c]
    exact card_le_of_le hF4
  have hq : 8 ≤ 2 ^ f := (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
  set E := rightConjugate (gmsV L T) g with hEdef
  have hEel : IsElemAbelian 2 E := isElemAbelian_map _ hVel
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hEel.2 x hx
  have hEcard : Nat.card E = Nat.card (gmsV L T) := rightConjugate_card _ _
  by_cases hEW : E ≤ U₁ ⊔ (T ⊓ centralizer (L : Set G))
  · by_cases hEV : E ≤ gmsV L T
    · exact Subgroup.eq_of_le_of_card_ge hEV hEcard.ge
    · exfalso
      obtain ⟨-, hEVA, hcard⟩ := hE.elem_le_W hT₀ hEW hEel hEV
      have h1 := card_le_of_le hEVA
      rw [hA] at h1
      rw [hEcard, hVcard] at hcard
      have h2 := Nat.mul_le_mul_left (2 ^ f) hT₀4
      linarith
  · exfalso
    obtain ⟨x, hxE, hxW⟩ := IsConcreteLE.not_le_iff_exists.mp hEW
    have hcard2 := hE.card_le_two_mul h hf e hg hE2
    have hxC : ∀ y ∈ E, y * x = x * y := fun y hy =>
      congrArg Subtype.val (hEel.1.is_comm.comm ⟨y, hy⟩ ⟨x, hxE⟩)
    by_cases hEWV : E ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ gmsV L T
    · obtain ⟨h1, h2⟩ := hE.inf_A_bound h hf e hX (hg hxE) (hE2 x hxE) hxW hEWV
        (fun y hy => mem_centralizer_singleton_iff.mpr (hxC y (mem_inf.mp hy).1))
      rw [hEcard] at hcard2
      set d := Nat.card ((E ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G)))) ⊓ gmsA L T : Subgroup G)
      set c := Nat.card (E ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) : Subgroup G)
      set Q := 2 ^ f
      have h5 := Nat.mul_le_mul_right Q hcard2
      have h3 : Nat.card (gmsV L T) * Q ≤ Nat.card (gmsV L T) * (2 * d) := by
        calc Nat.card (gmsV L T) * Q ≤ 2 * c * Q := h5
          _ = 2 * (c * Q) := by ring
          _ ≤ 2 * (Nat.card (gmsV L T) * d) := Nat.mul_le_mul_left 2 h1
          _ = Nat.card (gmsV L T) * (2 * d) := by ring
      have h4 := Nat.le_of_mul_le_mul_left h3 Nat.card_pos
      have h6 := Nat.mul_le_mul h4 h4
      have h7 := Nat.mul_le_mul_left Q hq
      have h8 : 2 * d * (2 * d) = 4 * d ^ 2 := by ring
      linarith
    · obtain ⟨-, hA', hc2⟩ := hE.elem_le_W hT₀ inf_le_right
        (isElemAbelian_of_le hEel inf_le_left) hEWV
      have h5 : (E ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G)))) ⊓ gmsV L T ≤ E ⊓ gmsA L T :=
        le_inf (inf_le_left.trans inf_le_left) hA'
      have h6 := card_le_of_le h5
      have h7 : Nat.card (E ⊓ gmsA L T : Subgroup G) ≤ 2 ^ f := hA ▸ card_le_of_le inf_le_right
      rw [hEcard, hVcard] at hcard2
      have h9 := Nat.mul_le_mul_left (2 ^ f) hT₀4
      have h8 : Nat.card (E ⊓ gmsA L T : Subgroup G) = 2 ^ f := le_antisymm h7 (by linarith)
      have hAE : gmsA L T ≤ E := by
        have := Subgroup.eq_of_le_of_card_ge (inf_le_right : E ⊓ gmsA L T ≤ gmsA L T)
          (by rw [h8, hA])
        rw [← this]
        exact inf_le_left
      exact hxW (hE.mem_W_of_commute h hf e (hg hxE) fun a ha => (hxC a (hAE ha)).symm)

theorem isSylowOf_top
    (hE : Sec4Homo L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f)) :
    IsSylowOf 2 (U₁ ⊔ T) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hns
  obtain ⟨S, hS₀S, z, hzS, hzN, hzS₀⟩ :=
    exists_mem_normalizer_of_not_isSylowOf hE.sylow.isPGroup hns
  have hVS₀ : gmsV L T ≤ U₁ ⊔ T :=
    (sup_le (inf_le_left.trans inf_le_left) inf_le_left).trans le_sup_right
  have hle : rightConjugate (gmsV L T) z⁻¹ ≤ U₁ ⊔ T := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have h1 := (mem_normalizer_iff.mp hzN _).mp (hVS₀ hx)
    simpa [mul_assoc] using h1
  have hzV : z ∈ normalizer (gmsV L T : Set G) := by
    have h1 := (rightConjugate_eq_self_iff _ _).mp (hE.rightConjugate_eq h hF hf e hX hle)
    simpa using inv_mem h1
  have hP : IsPGroup 2 ((U₁ ⊔ T) ⊔ zpowers z : Subgroup G) :=
    S.isPGroup'.to_le (sup_le hS₀S (zpowers_le.mpr hzS))
  have heq := hE.sylow.eq_of_le le_sup_left (sup_le hE.sylow.le (zpowers_le.mpr hzV)) hP
  exact hzS₀ (heq ▸ mem_sup_right (mem_zpowers _))

theorem false_of_homo
    (hE : Sec4Homo L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f)) (hres : GMS42ResidualU) : False := by
  have hT₀ := h.isElemAbelian_T₀ hF
  obtain ⟨hVcard, hVel, -, -, -⟩ := hX.vFacts h hF
  have hA := (hX.sylow h).1
  have hT₀4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) := by
    obtain ⟨F, hF4, -, hF4c⟩ := h.exists_four_le
    rw [← hF4c]
    exact card_le_of_le hF4
  have hq : 8 ≤ 2 ^ f := (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨-, hS₀p, hS₀idx⟩ := isSylowOf_iff.mp (hE.isSylowOf_top h hF hf e hX)
  rw [relIndex_top_right] at hS₀idx
  let S : Sylow 2 G := hS₀p.toSylow hS₀idx
  have hSc : (S : Subgroup G) = U₁ ⊔ T := IsPGroup.toSylow_coe hS₀p hS₀idx
  have hVT : gmsV L T ≤ T := sup_le (inf_le_left.trans inf_le_left) inf_le_left
  have hVS : gmsV L T ≤ S := hSc ▸ hVT.trans le_sup_right
  have hV1 : gmsV L T ≠ ⊥ := fun hb => h.T₀_ne_bot (le_bot_iff.mp (hb ▸ le_sup_right))
  have hNV := hE.S₀_le_normalizer_V h hF hf e
  have hwc : ∀ g : G, rightConjugate (gmsV L T) g ≤ S → rightConjugate (gmsV L T) g = gmsV L T :=
    fun g hg => hE.rightConjugate_eq h hF hf e hX (hSc ▸ hg)
  have hbound : ∀ w ∈ U₁ ⊔ T, w * w = 1 → w ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G)) → ∀ k : ℕ,
      Nat.card (⁅gmsV L T, zpowers w⁆ : Subgroup G) ≤ k → 2 ^ f ≤ k ^ 2 := by
    intro w hwS hww hwW k hk
    have hc := card_le_card_inf_centralizer_mul hVel.1 (hNV hwS)
    obtain ⟨h1, h2⟩ := hE.inf_A_bound h hf e hX hwS hww hwW
      (inf_le_left : gmsV L T ⊓ centralizer ({w} : Set G) ≤ gmsV L T) inf_le_right
    set D := gmsV L T ⊓ centralizer ({w} : Set G)
    set d := Nat.card (D ⊓ gmsA L T : Subgroup G)
    have h3 : Nat.card (gmsV L T) ≤ Nat.card D * k := hc.trans (Nat.mul_le_mul_left _ hk)
    have h4 : Nat.card (gmsV L T) * 2 ^ f ≤ Nat.card (gmsV L T) * (k * d) := by
      calc Nat.card (gmsV L T) * 2 ^ f ≤ Nat.card D * k * 2 ^ f := Nat.mul_le_mul_right _ h3
        _ = k * (Nat.card D * 2 ^ f) := by ring
        _ ≤ k * (Nat.card (gmsV L T) * d) := Nat.mul_le_mul_left k h1
        _ = Nat.card (gmsV L T) * (k * d) := by ring
    have h5 := Nat.le_of_mul_le_mul_left h4 Nat.card_pos
    have h6 := Nat.mul_le_mul h5 h5
    have h7 : k * d * (k * d) ≤ k ^ 2 * 2 ^ f := by
      calc k * d * (k * d) = k ^ 2 * d ^ 2 := by ring
        _ ≤ k ^ 2 * 2 ^ f := Nat.mul_le_mul_left _ h2
    exact Nat.le_of_mul_le_mul_right (h6.trans h7) (by positivity)
  by_cases hsc : ∃ v ∈ gmsV L T, ∃ g : G, g⁻¹ * v * g ∈ (S : Subgroup G) ∧ g⁻¹ * v * g ∉ gmsV L T
  · obtain ⟨U, hUV, g, hUg, hUgV, hgold⟩ :=
      GoldschmidtFour.goldschmidt_theorem_four_holds G S (gmsV L T) hVS hVel hwc hsc
    set U' := rightConjugate U g with hU'def
    have hU'S : U' ≤ U₁ ⊔ T := hSc ▸ hUg
    have hU'el : IsElemAbelian 2 U' := isElemAbelian_map _ (isElemAbelian_of_le hVel hUV)
    have hU'2 : ∀ x ∈ U', x * x = 1 := fun x hx => by rw [← sq]; exact hU'el.2 x hx
    have hidx := relIndex_mul_card (gmsV L T) U'
    rw [inf_comm] at hidx
    have hpos : 0 < Nat.card (U' ⊓ gmsV L T : Subgroup G) := Nat.card_pos
    by_cases hU'W : U' ≤ U₁ ⊔ (T ⊓ centralizer (L : Set G))
    · obtain ⟨⟨u, hu, t₀, ht₀, -, huA, hxU', -⟩, -, hc⟩ := hE.elem_le_W hT₀ hU'W hU'el hUgV
      have hidx2 : (gmsV L T).relIndex U' ≤ 2 := by nlinarith
      have hb := (hgold _ hxU').trans hidx2
      have hcomm := hE.card_le_commutator h hF hX hu huA ht₀
      omega
    · obtain ⟨w, hwU', hwW⟩ := IsConcreteLE.not_le_iff_exists.mp hU'W
      have hcard := hE.card_le_two_mul h hf e hU'S hU'2
      by_cases hU'WV : U' ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ gmsV L T
      · have h1 : Nat.card (U' ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) : Subgroup G) ≤
            Nat.card (U' ⊓ gmsV L T : Subgroup G) := card_le_of_le (le_inf inf_le_left hU'WV)
        have hidx2 : (gmsV L T).relIndex U' ≤ 2 := by nlinarith
        have := hbound w (hU'S hwU') (hU'2 w hwU') hwW 2 ((hgold w hwU').trans hidx2)
        norm_num at this
        omega
      · obtain ⟨⟨u, hu, t₀, ht₀, ht₀1, huA, hxU', hinv⟩, -, hc2⟩ :=
          hE.elem_le_W hT₀ inf_le_right (isElemAbelian_of_le hU'el inf_le_left) hU'WV
        have h1 : Nat.card ((U' ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G)))) ⊓ gmsV L T :
            Subgroup G) ≤ Nat.card (U' ⊓ gmsV L T : Subgroup G) :=
          card_le_of_le (inf_le_inf_right _ inf_le_left)
        have hidx4 : (gmsV L T).relIndex U' ≤ 4 := by nlinarith
        have hcomm := hE.card_le_commutator h hF hX hu huA ht₀
        have hT₀eq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4 := by
          have := (hgold _ (mem_inf.mp hxU').1).trans hidx4
          omega
        have hq16 := hbound w (hU'S hwU') (hU'2 w hwU') hwW 4 ((hgold w hwU').trans hidx4)
        have hf4 : f ≤ 4 := by
          by_contra hlt
          push Not at hlt
          have : 2 ^ 5 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hlt
          norm_num at hq16 this
          omega
        have hTV : ¬ T ≤ gmsV L T := fun hle => hwW (by
          have : U₁ ⊔ T ≤ U₁ ⊔ (T ⊓ centralizer (L : Set G)) :=
            sup_le le_sup_left (hle.trans hE.V_le)
          exact this (hU'S hwU'))
        obtain rfl | rfl : f = 3 ∨ f = 4 := by omega
        · exact hTV (h.le_V_of_odd hf ⟨1, rfl⟩ e)
        ·
          have hCw : Nat.card (gmsV L T ⊓ centralizer ({w} : Set G) : Subgroup G) = 16 := by
            have hc := card_le_card_inf_centralizer_mul hVel.1 (hNV (hU'S hwU'))
            have hb := (hgold w hwU').trans hidx4
            obtain ⟨h1, h2⟩ := hE.inf_A_bound h hf e hX (hU'S hwU') (hU'2 w hwU') hwW
              (inf_le_left : gmsV L T ⊓ centralizer ({w} : Set G) ≤ gmsV L T) inf_le_right
            rw [hVcard, hT₀eq] at hc h1
            set c := Nat.card (gmsV L T ⊓ centralizer ({w} : Set G) : Subgroup G)
            set d := Nat.card ((gmsV L T ⊓ centralizer ({w} : Set G)) ⊓ gmsA L T : Subgroup G)
            have hd : d ≤ 4 := by nlinarith
            norm_num at hc h1 h2
            have h3 : 64 ≤ c * 4 := hc.trans (Nat.mul_le_mul_left _ hb)
            omega
          exact hres G L T U₁ h hF ⟨e⟩ hX h313 hE hT₀eq hTV U g hUV hU'el hU'S
            (fun x hx => (hgold x hx).trans hidx4) u hu huA t₀ ht₀ ht₀1 hinv (mem_inf.mp hxU').1
            w hwU' hwW hCw
  · push Not at hsc
    exact h.hyp.lemma34 S hVS hVel.1 hV1 hsc

end Sec4Homo

end CFSG.ComponentClassification.GMS78

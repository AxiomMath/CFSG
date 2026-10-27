module

public import CFSG.GF2Type.Smith1979.CaseI25Num
public import CFSG.GF2Type.Smith1979.W4AsSurvL216
public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.Filter
public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.CentLbar
public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.Theta
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaMinusOddCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4MinusC

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S7
  CFSG.LargeExtraspecial.S8 CFSG.Open Subgroup Module
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.GF2Type.Smith1979.CaseI25Transfer (tM nuOn mem_NLbar_of_mem_Lbar)

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section Transfer

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hfusL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ normalizer (S.Lbar g : Set S.O) →
    x * t * x⁻¹ ∈ S.Lbar g)
include H C ht hfusL

theorem nu_fusion_w4 (ν : NLbar S g →* Multiplicative (ZMod 2)) {P : Subgroup S.Mbar}
    (hPN : ∀ x ∈ P, (x : S.O) ∈ normalizer (S.Lbar g : Set S.O)) (hcP : tM ht ∈ P)
    (hPle : P ≤ (NLbar S g).subgroupOf S.Mbar) :
    ∀ x : S.Mbar, ∀ h : x * tM ht * x⁻¹ ∈ P,
      nuOn ν P hPle ⟨x * tM ht * x⁻¹, h⟩ = nuOn ν P hPle ⟨tM ht, hcP⟩ := by
  intro x h
  have hxN : (x : S.O) * t * (x : S.O)⁻¹ ∈ normalizer (S.Lbar g : Set S.O) := hPN _ h
  have hL : (x : S.O) * t * (x : S.O)⁻¹ ∈ S.Lbar g := hfusL _ x.2 hxN
  have hD : (x : S.O) * t * (x : S.O)⁻¹ ∈ Delta S g t := by
    rw [CaseIClosure.Delta_eq_class_inter H C ht]
    exact ⟨hL, x, x.2, rfl⟩
  obtain ⟨n, hn, hnx⟩ := hD
  have e : (⟨(x : S.O) * t * (x : S.O)⁻¹, mem_NLbar_of_mem_Lbar hL⟩ : NLbar S g) =
      ⟨n, hn⟩ * ⟨t, mem_NLbar_of_mem_Lbar ht⟩ * ⟨n, hn⟩⁻¹ := Subtype.ext hnx
  have key := CaseI25Transfer.nu_conj_eq ν ⟨n, hn⟩ ⟨t, mem_NLbar_of_mem_Lbar ht⟩
  rw [← e] at key
  exact key

include ht1 in
theorem not_mem_commutator_Mbar_w4 (ν : NLbar S g →* Multiplicative (ZMod 2))
    (hν : ν ⟨t, mem_NLbar_of_mem_Lbar ht⟩ ≠ 1) :
    t ∉ (_root_.commutator S.Mbar).map S.Mbar.subtype := by
  haveI : Finite S.Mbar := inferInstance
  obtain ⟨P, hsyl, hcP, hPN⟩ := CaseI25Transfer.exists_sylow_data H C ht
  have hPle : P ≤ (NLbar S g).subgroupOf S.Mbar := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨x.2, hPN x hx⟩
  obtain ⟨Q, hQP, hQn, hab, hcQ, hfus⟩ :=
    CaseI25Transfer.exists_quotient_of_character P (nuOn ν P hPle) hcP hν
      (nu_fusion_w4 H C ht hfusL ν hPN hcP hPle)
  have hc := CaseI25Transfer.not_mem_commutator_of_fusion hsyl hQP hQn hab hcP
    (CaseI25Transfer.orderOf_tM_eq_two H ht ht1) hcQ hfus
  intro hmem
  obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.mp hmem
  have hxc : x = tM ht := Subtype.ext hxt
  rw [hxc] at hx
  exact hc hx

end Transfer

section Character

open Classical

variable {t : S.O}
  (hΔmul : ∀ l₁ ∈ S.Lbar g, ∀ l₂ ∈ S.Lbar g, (l₁ * l₂ ∈ Delta S g t ↔ ¬ (l₁ ∈ Delta S g t ↔
    l₂ ∈ Delta S g t)))

@[expose] noncomputable def deltaChar : S.Lbar g →* Multiplicative (ZMod 2) where
  toFun l := if (l : S.O) ∈ Delta S g t then Multiplicative.ofAdd 1 else 1
  map_one' := by
    have h := hΔmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    have h1 : (1 : S.O) ∉ Delta S g t := fun h1 => (h.mp h1) (Iff.rfl)
    simp [h1]
  map_mul' a b := by
    have h := hΔmul a a.2 b b.2
    have hab : ((a * b : S.Lbar g) : S.O) = (a : S.O) * b := rfl
    rw [hab]
    by_cases ha : (a : S.O) ∈ Delta S g t <;> by_cases hb : (b : S.O) ∈ Delta S g t
    · have : (a : S.O) * b ∉ Delta S g t := fun hm => h.mp hm (iff_of_true ha hb)
      simp only [ha, hb, this, if_true, if_false]
      decide
    · have : (a : S.O) * b ∈ Delta S g t := h.mpr fun hiff => hb (hiff.mp ha)
      simp [ha, hb, this]
    · have : (a : S.O) * b ∈ Delta S g t := h.mpr fun hiff => ha (hiff.mpr hb)
      simp [ha, hb, this]
    · have : (a : S.O) * b ∉ Delta S g t := fun hm => h.mp hm (iff_of_false ha hb)
      simp [ha, hb, this]

theorem deltaChar_apply (l : S.Lbar g) :
    deltaChar hΔmul l = if (l : S.O) ∈ Delta S g t then Multiplicative.ofAdd 1 else 1 := rfl

theorem deltaChar_conj (n : NLbar S g) (l : S.Lbar g) :
    deltaChar hΔmul (Case25.conjLbar S g n l) = deltaChar hΔmul l := by
  have hiff : (((Case25.conjLbar S g n l : S.Lbar g) : S.O) ∈ Delta S g t) ↔
      (l : S.O) ∈ Delta S g t := by
    rw [Case25.coe_conjLbar]
    constructor
    · intro h
      have := Case25.conj_mem_Delta (inv_mem n.2) h
      simpa [mul_assoc] using this
    · exact Case25.conj_mem_Delta n.2
  rw [deltaChar_apply, deltaChar_apply, if_congr hiff rfl rfl]

include hΔmul in
theorem not_mem_commutator_Mbar_of_deltaChar (H : Hyp4 S g) (C : Cons311 S g)
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hfusL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ normalizer (S.Lbar g : Set S.O) →
      x * t * x⁻¹ ∈ S.Lbar g) :
    t ∉ (_root_.commutator S.Mbar).map S.Mbar.subtype := by
  obtain ⟨ν, hν⟩ := Case25.exists_nu_extending H C (deltaChar hΔmul) (deltaChar_conj hΔmul)
  refine not_mem_commutator_Mbar_w4 H C ht ht1 hfusL ν ?_
  rw [hν t ht, deltaChar_apply, if_pos (mem_Delta_self S g t)]
  decide

end Character

section DeltaFour

open CFSG.Assembly (InCatalog KProper)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open Classical

theorem sixteen_dvd_card_inf_NLbar (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hΔ4 : (Delta S g t).ncard = 4) {θ : S.O}
    (hθ3 : θ ^ 3 = 1) (hθN : θ ∈ NLbar S g)
    (hθC : ∀ l ∈ S.Lbar g, θ * l = l * θ ↔ l = 1 ∨ l = t)
    (hΔmul : ∀ l₁ ∈ S.Lbar g, ∀ l₂ ∈ S.Lbar g, (l₁ * l₂ ∈ Delta S g t ↔
      ¬ (l₁ ∈ Delta S g t ↔ l₂ ∈ Delta S g t)))
    {Y : Subgroup S.O} (hYn : ∀ m ∈ S.Mbar, ∀ y ∈ Y, m * y * m⁻¹ ∈ Y) (hθY : θ ∈ Y)
    (hKY : ∀ l ∈ S.Lbar g, l ∉ Delta S g t → l ∈ Y) :
    16 ∣ Nat.card ↥(Y ⊓ NLbar S g) := by
  have hΔL : ∀ x ∈ Delta S g t, x ∈ S.Lbar g := fun x hx => Case25.delta_subset_Lbar ht hx
  have hθt : θ * t = t * θ := (hθC t ht).mpr (Or.inr rfl)
  have hθN₁ : θ ∈ Y ⊓ NLbar S g := ⟨hθY, hθN⟩
  obtain ⟨δ, hδ, hδt⟩ : ∃ δ ∈ Delta S g t, δ ≠ t := by
    by_contra hcon
    push Not at hcon
    have hsub : Delta S g t ⊆ {t} := fun x hx => hcon x hx
    have := Set.ncard_le_ncard hsub (Set.finite_singleton t)
    rw [Set.ncard_singleton, hΔ4] at this
    omega
  obtain ⟨y, hy, rfl⟩ := hδ
  obtain ⟨e, he⟩ : ∃ e, e = y * θ * y⁻¹ := ⟨_, rfl⟩
  have heN₁ : e ∈ Y ⊓ NLbar S g := by
    rw [he]
    exact Subgroup.mem_inf.mpr ⟨hYn y (Subgroup.mem_inf.mp hy).1 θ hθY,
      mul_mem (mul_mem hy hθN) (inv_mem hy)⟩
  have hnotfix : ∀ x ∈ S.Lbar g, x ≠ 1 → x ≠ t → θ * x * θ⁻¹ ≠ x := by
    intro x hx hx1 hxt hcon
    have : θ * x = x * θ := by
      calc θ * x = θ * x * θ⁻¹ * θ := by group
        _ = x * θ := by rw [hcon]
    rcases (hθC x hx).mp this with h | h
    · exact hx1 h
    · exact hxt h
  obtain ⟨t', ht'⟩ : ∃ t', t' = e * t * e⁻¹ := ⟨_, rfl⟩
  have ht'O : t' ∈ Delta S g t := by rw [ht']; exact ⟨e, heN₁.2, rfl⟩
  have ht'L := hΔL _ ht'O
  have ht't : t' ≠ t := by
    intro hcon
    have hc : θ * (y⁻¹ * t * y) = (y⁻¹ * t * y) * θ := by
      have h0 : y * θ * y⁻¹ * t * (y * θ * y⁻¹)⁻¹ = t := by rw [← he, ← ht']; exact hcon
      calc θ * (y⁻¹ * t * y) = y⁻¹ * ((y * θ * y⁻¹) * t * (y * θ * y⁻¹)⁻¹) * y * θ := by group
        _ = y⁻¹ * t * y * θ := by rw [h0]
    have hyL : y⁻¹ * t * y ∈ S.Lbar g := by
      have h0 := Case25.conj_mem_Delta (inv_mem hy) (mem_Delta_self S g t)
      rw [inv_inv] at h0
      exact hΔL _ h0
    rcases (hθC _ hyL).mp hc with h | h
    · apply ht1
      calc t = y * (y⁻¹ * t * y) * y⁻¹ := by group
        _ = 1 := by rw [h]; group
    · apply hδt
      calc y * t * y⁻¹ = y * (y⁻¹ * t * y) * y⁻¹ := by rw [h]
        _ = t := by group
  have ht'1 : t' ≠ 1 := by
    intro h
    apply ht1
    calc t = e⁻¹ * (e * t * e⁻¹) * e := by group
      _ = 1 := by rw [← ht', h]; group
  have hθ2 : θ ^ 2 = θ⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hθ3]
  have ha1t' : θ * t' * θ⁻¹ ≠ t' := hnotfix t' ht'L ht'1 ht't
  have ha2t' : θ⁻¹ * t' * θ ≠ t' := by
    intro h
    apply ha1t'
    calc θ * t' * θ⁻¹ = θ * (θ⁻¹ * t' * θ) * θ⁻¹ := by rw [h]
      _ = t' := by group
  have ha12 : θ * t' * θ⁻¹ ≠ θ⁻¹ * t' * θ := by
    intro h
    apply ha2t'
    have h1 : θ * (θ * t' * θ⁻¹) * θ⁻¹ = t' := by rw [h]; group
    have hθθ : θ * θ = θ⁻¹ := by rw [← pow_two, hθ2]
    have hθθ' : θ⁻¹ * θ⁻¹ = θ := by rw [← mul_inv_rev, hθθ, inv_inv]
    calc θ⁻¹ * t' * θ = (θ * θ) * t' * (θ⁻¹ * θ⁻¹) := by rw [hθθ, hθθ']
      _ = θ * (θ * t' * θ⁻¹) * θ⁻¹ := by simp only [mul_assoc]
      _ = t' := h1
  have hta1 : t ≠ θ * t' * θ⁻¹ := by
    intro h
    apply ht't
    calc t' = θ⁻¹ * (θ * t' * θ⁻¹) * θ := by group
      _ = θ⁻¹ * t * θ := by rw [← h]
      _ = t := by rw [mul_assoc, ← hθt]; group
  have hta2 : t ≠ θ⁻¹ * t' * θ := by
    intro h
    apply ht't
    calc t' = θ * (θ⁻¹ * t' * θ) * θ⁻¹ := by group
      _ = θ * t * θ⁻¹ := by rw [← h]
      _ = t := by rw [hθt]; group
  have hOΔ : {x | ∃ n ∈ Y ⊓ NLbar S g, x = n * t * n⁻¹} ⊆ Delta S g t := by
    rintro x ⟨n, hn, rfl⟩
    exact ⟨n, hn.2, rfl⟩
  have hAO : ({t, t', θ * t' * θ⁻¹, θ⁻¹ * t' * θ} : Set S.O) ⊆
      {x | ∃ n ∈ Y ⊓ NLbar S g, x = n * t * n⁻¹} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, by group⟩
    · exact ⟨e, heN₁, ht'⟩
    · exact ⟨θ * e, mul_mem hθN₁ heN₁, by rw [ht']; group⟩
    · exact ⟨θ⁻¹ * e, mul_mem (inv_mem hθN₁) heN₁, by rw [ht']; group⟩
  have hA4 : ({t, t', θ * t' * θ⁻¹, θ⁻¹ * t' * θ} : Set S.O).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair ha12]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1t'.symm, ha2t'.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ht't.symm, hta1, hta2⟩
  have hOcard : {x | ∃ n ∈ Y ⊓ NLbar S g, x = n * t * n⁻¹}.ncard = 4 := by
    apply le_antisymm
    · rw [← hΔ4]
      exact Set.ncard_le_ncard hOΔ (Set.toFinite _)
    · rw [← hA4]
      exact Set.ncard_le_ncard hAO (Set.toFinite _)
  have hidx : ((centralizer ({t} : Set S.O)).subgroupOf (Y ⊓ NLbar S g)).index = 4 := by
    rw [← CaseIClosure.ncard_conj_orbit (Y ⊓ NLbar S g) t]
    exact hOcard
  have hN₁card : Nat.card ↥(Y ⊓ NLbar S g) =
      4 * Nat.card ↥((Y ⊓ NLbar S g) ⊓ centralizer ({t} : Set S.O)) := by
    have h1 := Subgroup.index_mul_card ((centralizer ({t} : Set S.O)).subgroupOf (Y ⊓ NLbar S g))
    rw [hidx] at h1
    rw [← h1, ← Subgroup.inf_subgroupOf_left]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hL8 : Nat.card (S.Lbar g) = 8 := by rw [C.card_Lbar, hw]; norm_num
  have hft : deltaChar hΔmul ⟨t, ht⟩ = Multiplicative.ofAdd 1 := by
    rw [deltaChar_apply, if_pos (mem_Delta_self S g t)]
  have hfsurj : Function.Surjective (deltaChar hΔmul) := by
    intro z
    have hz : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
    rcases hz z with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨⟨t, ht⟩, hft⟩
  have hK4 : Nat.card (deltaChar hΔmul).ker = 4 := by
    have h1 := Subgroup.card_ker_mul_card_range (deltaChar hΔmul)
    rw [(deltaChar hΔmul).range_eq_top_of_surjective hfsurj, Subgroup.card_top, hL8] at h1
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [h2] at h1
    omega
  have hmemK : ∀ l : S.Lbar g, l ∈ (deltaChar hΔmul).ker → (l : S.O) ∉ Delta S g t := by
    intro l hl hlΔ
    rw [MonoidHom.mem_ker, deltaChar_apply, if_pos hlΔ] at hl
    exact absurd hl (by decide)
  have hKmC : (deltaChar hΔmul).ker.map (S.Lbar g).subtype ≤
      (Y ⊓ NLbar S g) ⊓ centralizer ({t} : Set S.O) := by
    rintro _ ⟨l, hl, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hKY l l.2 (hmemK l hl),
      Case25.Lbar_le_NLbar l.2⟩,
      mem_centralizer_singleton_iff.mpr (Lbar_comm S H.conj_mem ht l.2).symm⟩
  have h4 : 4 ∣ Nat.card ↥((Y ⊓ NLbar S g) ⊓ centralizer ({t} : Set S.O)) := by
    have h1 := Subgroup.card_dvd_of_le hKmC
    rwa [card_map_of_injective (S.Lbar g).subtype_injective, hK4] at h1
  rw [hN₁card]
  exact (show 16 = 4 * 4 from rfl) ▸ Nat.mul_dvd_mul_left 4 h4

theorem card_NLbar_dvd_192 (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hP : ¬ PlusAt H C)
    (hΔ4 : (Delta S g t).ncard = 4)
    (hΔmul : ∀ l₁ ∈ S.Lbar g, ∀ l₂ ∈ S.Lbar g, (l₁ * l₂ ∈ Delta S g t ↔
      ¬ (l₁ ∈ Delta S g t ↔ l₂ ∈ Delta S g t))) :
    Nat.card (NLbar S g) ∣ 192 := by
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem ht
  have hL8 : Nat.card (S.Lbar g) = 8 := by rw [C.card_Lbar, hw]; norm_num
  have hcl : Subgroup.closure (Delta S g t) = S.Lbar g := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      exact fun x hx => Case25.delta_subset_Lbar ht hx
    · intro l hl
      by_cases hlΔ : l ∈ Delta S g t
      · exact Subgroup.subset_closure hlΔ
      · have htl : t * l ∈ Delta S g t :=
          (hΔmul t ht l hl).mpr fun h => hlΔ (h.mp (mem_Delta_self S g t))
        have e1 : l = t * (t * l) := by rw [← mul_assoc, htt, one_mul]
        rw [e1]
        exact mul_mem (Subgroup.subset_closure (mem_Delta_self S g t))
          (Subgroup.subset_closure htl)
  have hker : (Case25.permDelta S g t).ker = (S.Lbar g).subgroupOf (NLbar S g) := by
    ext n
    rw [MonoidHom.mem_ker, Case25.permDelta_eq_one_iff hcl ht n, Subgroup.mem_subgroupOf]
    constructor
    · intro hn
      exact mem_Lbar_of_centralizes_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP n.2.1 hn
    · intro hn l hl
      exact Lbar_comm S H.conj_mem hn hl
  have h1 := Subgroup.card_ker_mul_card_range (Case25.permDelta S g t)
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Case25.Lbar_le_NLbar).toEquiv,
    hL8] at h1
  have h2 : Nat.card (Case25.permDelta S g t).range ∣ 24 := by
    have h3 := Subgroup.card_subgroup_dvd_card (Case25.permDelta S g t).range
    rw [Nat.card_perm, Nat.card_coe_set_eq, hΔ4] at h3
    exact h3
  rw [← h1]
  exact (show 192 = 8 * 24 from rfl) ▸ Nat.mul_dvd_mul_left 8 h2

theorem not_two_pow_seven_dvd_card_Mbar (H : Hyp4 S g) (C : Cons311 S g)
    (hN : Nat.card (NLbar S g) ∣ 192) : ¬ 2 ^ 7 ∣ Nat.card S.Mbar := by
  intro h2
  obtain ⟨T, hTsyl, -, hTN⟩ := Case25.exists_sylow_le_NLbar H C
  have hT : Nat.card T = 2 ^ (Nat.card S.Mbar).factorization 2 := hTsyl.card_eq
  have h3 : 7 ≤ (Nat.card S.Mbar).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
  have h4 : 2 ^ 7 ∣ Nat.card T := by
    rw [hT]
    exact pow_dvd_pow 2 h3
  have h5 : 2 ^ 7 ∣ 192 := (h4.trans (Subgroup.card_dvd_of_le hTN)).trans hN
  norm_num at h5

theorem card_O_w4 (hw : S.width = 4) (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) : Nat.card S.O = 348364800 := by
  have h8 : finrank (ZMod 2) S.Qt = 8 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  rw [W4As.Surv.card_orthogonalGroup_plus_eight S.q_nondegenerate h8
    ⟨Vt S g t, h4, fun v hv => q_eq_zero_of_mem_Vt H ht1 hv⟩]
  norm_num

theorem false_of_layer_delta_four (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hF : FilterW4MinusInCatalog)
    (hΔ4 : (Delta S g t).ncard = 4) {θ : S.O}
    (hθR : θ ∈ ⁅Rbar S g t, Rbar S g t⁆) (hθ3 : θ ^ 3 = 1) (hθN : θ ∈ NLbar S g)
    (hθC : ∀ l ∈ S.Lbar g, θ * l = l * θ ↔ l = 1 ∨ l = t)
    (hΔmul : ∀ l₁ ∈ S.Lbar g, ∀ l₂ ∈ S.Lbar g, (l₁ * l₂ ∈ Delta S g t ↔
      ¬ (l₁ ∈ Delta S g t ↔ l₂ ∈ Delta S g t)))
    (hΔK : ∀ l ∈ S.Lbar g, l ∉ Delta S g t → ∃ a ∈ S.Lbar g, l = a⁻¹ * (θ * a * θ⁻¹))
    (h60 : 60 ∣ Nat.card (⁅Rbar S g t, Rbar S g t⁆ : Subgroup S.O))
    (hNcard : Nat.card (NLbar S g) ∣ 192) (hO : Nat.card S.O = 348364800)
    (E : Subgroup S.Mbar) (hEn : E.Normal) (hZ3 : Nat.card (center E) ∣ 3)
    (hXs : IsSimpleGroup (E ⧸ center E)) (hXnab : ∃ a b : E ⧸ center E, a * b ≠ b * a)
    (hXcat : InCatalog (E ⧸ center E)) (hRE : ⁅Rbar S g t, Rbar S g t⁆ ≤ E.map S.Mbar.subtype)
    (htE : t ∉ E.map S.Mbar.subtype) : False := by
  have hEmn : ∀ m ∈ S.Mbar, ∀ x ∈ E.map S.Mbar.subtype, m * x * m⁻¹ ∈ E.map S.Mbar.subtype := by
    rintro m hm _ ⟨x, hx, rfl⟩
    exact ⟨⟨m, hm⟩ * x * ⟨m, hm⟩⁻¹, hEn.conj_mem x hx ⟨m, hm⟩, rfl⟩
  have hθE : θ ∈ E.map S.Mbar.subtype := hRE hθR
  have hKE : ∀ l ∈ S.Lbar g, l ∉ Delta S g t → l ∈ E.map S.Mbar.subtype := by
    intro l hl hlΔ
    obtain ⟨a, ha, hla⟩ := hΔK l hl hlΔ
    have haM : a⁻¹ ∈ S.Mbar := inv_mem (S.Lbar_le_Mbar g ha)
    have e1 : l = (a⁻¹ * θ * a⁻¹⁻¹) * θ⁻¹ := by rw [hla]; group
    rw [e1]
    exact mul_mem (hEmn _ haM _ hθE) (inv_mem hθE)
  have h16N := sixteen_dvd_card_inf_NLbar hw H C ht ht1 hΔ4 hθ3 hθN hθC hΔmul hEmn hθE hKE
  have hEm_card : Nat.card (E.map S.Mbar.subtype) = Nat.card E :=
    card_map_of_injective S.Mbar.subtype_injective
  have hEX : Nat.card E = Nat.card (E ⧸ center E) * Nat.card (center E) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h5 : 5 ∣ Nat.card (E ⧸ center E) := by
    have h1 : 5 ∣ Nat.card E := by
      rw [← hEm_card]
      exact (dvd_trans (by norm_num : 5 ∣ 60) h60).trans (Subgroup.card_dvd_of_le hRE)
    rw [hEX] at h1
    exact (Nat.Coprime.coprime_dvd_right hZ3 (by norm_num : Nat.Coprime 5 3)).dvd_of_dvd_mul_right
      h1
  have hord : Nat.card (E ⧸ center E) ∣ 348364800 := by
    rw [← hO]
    exact ((Dvd.intro _ hEX.symm).trans (Subgroup.card_subgroup_dvd_card E)).trans
      (Subgroup.card_subgroup_dvd_card S.Mbar)
  have h16 : 2 ^ 4 ∣ Nat.card (E ⧸ center E) := by
    have h1 : 16 ∣ Nat.card E := by
      rw [← hEm_card]
      exact h16N.trans (Subgroup.card_dvd_of_le inf_le_left)
    rw [hEX] at h1
    exact (Nat.Coprime.coprime_dvd_right hZ3 (by norm_num : Nat.Coprime 16 3)).dvd_of_dvd_mul_right
      h1
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem ht
  have htM : (⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar) ∉ E := fun h => htE ⟨_, h, rfl⟩
  haveI := hEn
  have h2idx : 2 ∣ E.index :=
    Case25.two_dvd_index_of_not_mem E (Subtype.ext htt) htM
  have h64 : ¬ 2 ^ 6 ∣ Nat.card (E ⧸ center E) := by
    intro h
    have h1 : 2 ^ 6 ∣ Nat.card E := h.trans (Dvd.intro _ hEX.symm)
    apply not_two_pow_seven_dvd_card_Mbar H C hNcard
    rw [← E.card_mul_index, show (2 : ℕ) ^ 7 = 2 ^ 6 * 2 from rfl]
    exact Nat.mul_dvd_mul h1 h2idx
  haveI : IsSimpleGroup (E ⧸ center E) := hXs
  exact hF hXcat hXnab hord h5 h16 h64


theorem false_of_delta_four [IsSimpleGroup G] (hCE : CentralExtInput.{0}) (hw : S.width = 4)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hP : ¬ PlusAt H C) (hS : SchreierFor InCatalog)
    (hK : KProper InCatalog G) (hIrr : S5.Irr S) (hsw : ¬ Nonempty (S5.SwapData S g))
    (hF : FilterW4MinusInCatalog) (hΔ4 : (Delta S g t).ncard = 4) {θ : S.O}
    (hθR : θ ∈ ⁅Rbar S g t, Rbar S g t⁆) (hθ3 : θ ^ 3 = 1) (hθN : θ ∈ NLbar S g)
    (hθC : ∀ l ∈ S.Lbar g, θ * l = l * θ ↔ l = 1 ∨ l = t)
    (hΔmul : ∀ l₁ ∈ S.Lbar g, ∀ l₂ ∈ S.Lbar g, (l₁ * l₂ ∈ Delta S g t ↔
      ¬ (l₁ ∈ Delta S g t ↔ l₂ ∈ Delta S g t)))
    (hΔK : ∀ l ∈ S.Lbar g, l ∉ Delta S g t → ∃ a ∈ S.Lbar g, l = a⁻¹ * (θ * a * θ⁻¹))
    (hfusL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ normalizer (S.Lbar g : Set S.O) →
      x * t * x⁻¹ ∈ S.Lbar g) : False := by
  have hodd := W4Minus.card_oddCore_dvd_three_not_plus H hNo C hP hw
  have hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) :=
    (W4Five.timmesfeld_5_2_w4_of_no_swap hCE hIrr H hNo C (S45Q.hyp45Q H C) hw hsw).resolve_left
      (W4Five.timmesfeldLayer_ne_bot_w4 H C hodd)
  have hM : S.M ≠ ⊤ := Case25.M_ne_top_of_isSimpleGroup S
  obtain ⟨hEn, hEperf, -, hZ3, hXs, hXnab, hXcat⟩ := Case25.layer_data hK hM hq hodd
  have hRE : ⁅Rbar S g t, Rbar S g t⁆ ≤ (timmesfeldLayer S.Mbar).map S.Mbar.subtype :=
    Case25.perfect_le_layer_map hS hK hM hq hodd
      ((Subgroup.commutator_le_self _).trans Rbar_le_Mbar)
      (commutator_commutator_Rbar_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP)
  have h60 := sixty_dvd_card_commutator_Rbar_w4 hCE H hNo C ht ht1 hVQ hΩ h4 hP
  have hNcard := card_NLbar_dvd_192 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP hΔ4 hΔmul
  have hO := card_O_w4 hw H ht1 h4
  have hEcomm : (timmesfeldLayer S.Mbar).map S.Mbar.subtype ≤
      (_root_.commutator S.Mbar).map S.Mbar.subtype := by
    apply Subgroup.map_mono
    calc timmesfeldLayer S.Mbar = ⁅timmesfeldLayer S.Mbar, timmesfeldLayer S.Mbar⁆ :=
          hEperf.symm
      _ ≤ ⁅(⊤ : Subgroup S.Mbar), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = _root_.commutator S.Mbar := (_root_.commutator_def S.Mbar).symm
  have htE : t ∉ (timmesfeldLayer S.Mbar).map S.Mbar.subtype := fun h =>
    not_mem_commutator_Mbar_of_deltaChar hΔmul H C ht ht1 hfusL (hEcomm h)
  exact false_of_layer_delta_four hw H C ht ht1 hF hΔ4 hθR hθ3 hθN hθC hΔmul hΔK h60 hNcard hO
    (timmesfeldLayer S.Mbar) hEn hZ3 hXs hXnab hXcat hRE htE

end DeltaFour

end CFSG.GF2Type.Smith1979.W4MinusC

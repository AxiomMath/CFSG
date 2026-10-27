module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S
public import CFSG.ClassicalInvolution.Q3.Sec13AECoverEven
public import CFSG.ClassicalInvolution.Q3.TL3T61
public import CFSG.ClassicalInvolution.Q3.TL3T35
public import CFSG.ClassicalInvolution.Q3.TL3T52A
public import CFSG.ClassicalInvolution.Q3.TL3T12_6E8Sec
public import CFSG.ClassicalInvolution.Q3.TL3T42
public import CFSG.ClassicalInvolution.Q3.TL3T47
public import CFSG.ClassicalInvolution.Q3.TL3T48
public import CFSG.ClassicalInvolution.Q3.TL3T51
public import CFSG.ClassicalInvolution.Q3.TL3T57
public import CFSG.ClassicalInvolution.Q3.TL3T58
public import CFSG.ClassicalInvolution.Q3.TL3T60
public import CFSG.ClassicalInvolution.Q3.TL4AECoverH
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GCoc
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GSpan
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Twins

variable {Y : Type} [Group Y]

structure FourTwins (P : Set (Subgroup Y)) (z : Y) (A₁ A₂ A₃ A₄ : Subgroup Y) : Prop where
  m₁ : A₁ ∈ P
  m₂ : A₂ ∈ P
  m₃ : A₃ ∈ P
  m₄ : A₄ ∈ P
  z₁ : IsUniqueInvolution A₁ z
  z₂ : IsUniqueInvolution A₂ z
  z₃ : IsUniqueInvolution A₃ z
  z₄ : IsUniqueInvolution A₄ z
  ne₁₂ : A₁ ≠ A₂
  ne₁₃ : A₁ ≠ A₃
  ne₁₄ : A₁ ≠ A₄
  ne₂₃ : A₂ ≠ A₃
  ne₂₄ : A₂ ≠ A₄
  ne₃₄ : A₃ ≠ A₄

theorem bool_four (b₁ b₂ b₃ b₄ : Bool) :
    b₁ = b₂ ∨ b₁ = b₃ ∨ b₁ = b₄ ∨ b₂ = b₃ ∨ b₂ = b₄ ∨ b₃ = b₄ := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> simp

end Twins

section Exclusion

variable {Y : Type} [Group Y] [Finite Y] {Ω P : Set (Subgroup Y)}

theorem false_of_same_four_set {n : ℕ} (hn : 5 ≤ n) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (hPΩ : P ⊆ Ω) (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker)
    {α : Finset (Fin n)} {h : α.card = 4} {A₁ A₂ A₃ A₄ : Subgroup Y} {b₁ b₂ b₃ b₄ : Bool}
    (m₁ : A₁ ∈ P) (m₂ : A₂ ∈ P) (m₃ : A₃ ∈ P) (m₄ : A₄ ∈ P)
    (hl₁ : (A₁.subgroupOf (pSpan P)).map I.φ = memBar α h b₁)
    (hl₂ : (A₂.subgroupOf (pSpan P)).map I.φ = memBar α h b₂)
    (hl₃ : (A₃.subgroupOf (pSpan P)).map I.φ = memBar α h b₃)
    (hl₄ : (A₄.subgroupOf (pSpan P)).map I.φ = memBar α h b₄)
    (ne₁₂ : A₁ ≠ A₂) (ne₁₃ : A₁ ≠ A₃) (ne₁₄ : A₁ ≠ A₄) (ne₂₃ : A₂ ≠ A₃) (ne₂₄ : A₂ ≠ A₄)
    (ne₃₄ : A₃ ≠ A₄) : False := by
  have key : ∀ {B C : Subgroup Y} (hB : B ∈ P) (hC : C ∈ P) {b c : Bool},
      (B.subgroupOf (pSpan P)).map I.φ = memBar α h b →
      (C.subgroupOf (pSpan P)).map I.φ = memBar α h c → b = c → B = C := by
    intro B C hB hC b c hb hc hbc
    subst hbc
    exact aeIdent_eq_of_map_eq hΩ h2 hPΩ hn I hk hB hC (hb.trans hc.symm)
  rcases bool_four b₁ b₂ b₃ b₄ with h' | h' | h' | h' | h' | h'
  · exact ne₁₂ (key m₁ m₂ hl₁ hl₂ h')
  · exact ne₁₃ (key m₁ m₃ hl₁ hl₃ h')
  · exact ne₁₄ (key m₁ m₄ hl₁ hl₄ h')
  · exact ne₂₃ (key m₂ m₃ hl₂ hl₃ h')
  · exact ne₂₄ (key m₂ m₄ hl₂ hl₄ h')
  · exact ne₃₄ (key m₃ m₄ hl₃ hl₄ h')

theorem false_of_four_twins {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 8) (hPΩ : P ⊆ Ω)
    (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {z : Y} {A₁ A₂ A₃ A₄ : Subgroup Y}
    (F : FourTwins P z A₁ A₂ A₃ A₄) : False := by
  obtain ⟨α₁, h₁, b₁, hl₁⟩ := I.label A₁ F.m₁
  obtain ⟨α₂, h₂', b₂, hl₂⟩ := I.label A₂ F.m₂
  obtain ⟨α₃, h₃, b₃, hl₃⟩ := I.label A₃ F.m₃
  obtain ⟨α₄, h₄, b₄, hl₄⟩ := I.label A₄ F.m₄
  have e₁ := I.map_eq_zBar hn F.m₁ (h8 _ (hPΩ F.m₁)) hl₁ F.z₁
  have e₂ := I.map_eq_zBar hn F.m₂ (h8 _ (hPΩ F.m₂)) hl₂ F.z₂
  have e₃ := I.map_eq_zBar hn F.m₃ (h8 _ (hPΩ F.m₃)) hl₃ F.z₃
  have e₄ := I.map_eq_zBar hn F.m₄ (h8 _ (hPΩ F.m₄)) hl₄ F.z₄
  have a₂ : α₂ = α₁ := eq_of_zBar_eq hn8 (e₂.symm.trans e₁)
  have a₃ : α₃ = α₁ := eq_of_zBar_eq hn8 (e₃.symm.trans e₁)
  have a₄ : α₄ = α₁ := eq_of_zBar_eq hn8 (e₄.symm.trans e₁)
  subst a₂ a₃ a₄
  exact false_of_same_four_set hn hΩ h2 hPΩ I hk F.m₁ F.m₂ F.m₃ F.m₄ hl₁ hl₂ hl₃ hl₄ F.ne₁₂ F.ne₁₃
    F.ne₁₄ F.ne₂₃ F.ne₂₄ F.ne₃₄

@[expose] def NoOrderFive {n : ℕ} (H : Subgroup (AEQ n)) : Prop :=
  ∀ g ∈ H, g ^ 5 = 1 → g = 1

theorem false_of_order_five {n : ℕ} {Q : Set (Subgroup Y)} {H : Subgroup (AEQ n)}
    (φ : ↥(pSpan Q) →* AEQ n) (hk : IsPGroup 2 φ.ker) (hrange : φ.range = H)
    (hno : NoOrderFive H) (y : ↥(pSpan Q)) (hy : orderOf y = 5) : False := by
  have hmem : φ y ∈ H := hrange ▸ ⟨y, rfl⟩
  have h5 : φ y ^ 5 = 1 := by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  have h1 : φ y = 1 := hno _ hmem h5
  obtain ⟨j, hj⟩ := hk ⟨y, h1⟩
  have hj' : y ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hdvd : 5 ∣ 2 ^ j := hy ▸ orderOf_dvd_of_pow_eq_one hj'
  have : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd
  omega

theorem twin_z_of_trans₈ {P : Set (Subgroup Y)} {n : ℕ} (I : AEIdent P n) (hn : 5 ≤ n)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    (htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L')
    {J₀ J₀' : Subgroup Y} (hJ₀ : J₀ ∈ P) (hJ₀' : J₀' ∈ P) {δ : Finset (Fin n)}
    {hδ : δ.card = 4} {c : Bool}
    (hlab₀ : (J₀.subgroupOf (pSpan P)).map I.φ = memBar δ hδ c)
    (hlab₀' : (J₀'.subgroupOf (pSpan P)).map I.φ = memBar δ hδ (!c))
    (hz₀ : ∀ u u' : Y, IsUniqueInvolution J₀ u → IsUniqueInvolution J₀' u' → u = u') :
    ∀ (α : Finset (Fin n)) (h : α.card = 4), ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = memBar α h true →
      (L'.subgroupOf (pSpan P)).map I.φ = memBar α h false →
      ∀ u u' : Y, IsUniqueInvolution L u → IsUniqueInvolution L' u' → u = u' := by
  intro α h L hL L' hL' hlab hlab' u u' hu hu'
  obtain ⟨x, hx, hxL⟩ := htrans J₀ hJ₀ L hL
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (piSub n) (I.φ ⟨x, hx⟩)
  have hc1 := TL4.AECov.map_conjSub_eq I J₀ ⟨x, hx⟩
  have hc2 := TL4.AECov.map_conjSub_eq I J₀' ⟨x, hx⟩
  rw [hxL, hlab₀, ← hw] at hc1
  rw [hlab₀', ← hw] at hc2
  obtain ⟨c₁, hc₁⟩ := exists_conj_memBar_map w δ hδ c
  obtain ⟨c₂, hc₂⟩ := exists_conj_memBar_map w δ hδ (!c)
  rw [hc₁] at hc1
  rw [hc₂] at hc2
  have hδα : δ.map w.perm.toEmbedding = α := eq_of_memBar_eq' hn (hc1.symm.trans hlab)
  have hne : c₂ ≠ c₁ := by
    intro e
    rw [e] at hc₂
    have := conjSub_injective (mkQ n w) (hc₁.trans hc₂.symm)
    cases c
    · exact memBar_true_ne_false hn δ hδ this.symm
    · exact memBar_true_ne_false hn δ hδ this
  have hc₁t : c₁ = true := by
    by_contra hf
    have : c₁ = false := by cases c₁ <;> simp_all
    subst this
    subst hδα
    exact memBar_true_ne_false hn _ h (hlab.symm.trans hc1)
  have hc₂f : c₂ = false := by cases c₂ <;> simp_all
  subst hc₁t hc₂f
  have hxJ' : conjSub x J₀' = L' := by
    refine hinj _ (hconj J₀' hJ₀' x hx) L' hL' ?_
    rw [hc2, hlab']
    subst hδα
    rfl
  have hJ₀L : conjSub x⁻¹ L = J₀ := by rw [← hxL, conjSub_inv_conjSub]
  have hJ₀L' : conjSub x⁻¹ L' = J₀' := by rw [← hxJ', conjSub_inv_conjSub]
  have hv := hu.conj x⁻¹
  rw [hJ₀L] at hv
  have hv' := hu'.conj x⁻¹
  rw [hJ₀L'] at hv'
  have e := hz₀ _ _ hv hv'
  calc u = x * (x⁻¹ * u * x⁻¹⁻¹) * x⁻¹ := by group
    _ = x * (x⁻¹ * u' * x⁻¹⁻¹) * x⁻¹ := by rw [e]
    _ = u' := by group



theorem zBar_eq_cases {n : ℕ} {α β : Finset (Fin n)} {h : α.card = 4} {h' : β.card = 4}
    (he : zBar α h = zBar β h') : α = β ∨ ∀ x, x ∈ α ↔ x ∉ β := by
  classical
  rcases mkQ_eq_iff.mp he with h1 | h1
  · left
    have := range_eq_of_zOf_eq (inv_mul_eq_one.mp h1)
    rw [range_emb, range_emb] at this
    exact_mod_cast this
  · right
    intro x
    have hv : (zOf (emb α h)).vec x + (zOf (emb β h')).vec x = 1 := by
      have h2 := congrFun (congrArg Wr.vec h1) x
      rw [Wr.mul_vec, zOf_inv, zOf_perm] at h2
      exact h2
    rw [zOf_vec_apply, zOf_vec_apply] at hv
    have e1 : x ∈ Set.range (emb α h) ↔ x ∈ α := by rw [range_emb]; rfl
    have e2 : x ∈ Set.range (emb β h') ↔ x ∈ β := by rw [range_emb]; rfl
    by_cases h4 : x ∈ α
    · have h4' : x ∈ Set.range (emb α h) := e1.mpr h4
      by_cases h5 : x ∈ β
      · have h5' := e2.mpr h5
        rw [if_pos h4', if_pos h5'] at hv
        exact absurd hv (by decide)
      · exact ⟨fun _ => h5, fun _ => h4⟩
    · have h4' : x ∉ Set.range (emb α h) := fun hh => h4 (e1.mp hh)
      by_cases h5 : x ∈ β
      · exact ⟨fun hh => absurd hh h4, fun hh => absurd h5 hh⟩
      · have h5' : x ∉ Set.range (emb β h') := fun hh => h5 (e2.mp hh)
        rw [if_neg h4', if_neg h5'] at hv
        exact absurd hv (by decide)

end Exclusion

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

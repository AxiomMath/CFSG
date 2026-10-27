module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndBasic

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.J2End

section FourConj

variable {U : Type*} [Group U]

theorem commute_of_mem_fourSet {p q z x : U} (hp : p * z = z * p) (hq : q * z = z * q)
    (hx : x ∈ fourSet p q) : x * z = z * x := by
  rcases mem_four hx with h | h | h | h <;> rw [h]
  · rw [one_mul, mul_one]
  · exact hp
  · exact hq
  · rw [mul_assoc, hq, ← mul_assoc, hp, mul_assoc]

theorem commute_fourSet {p q e₁ e₂ x y : U} (hp₁ : p * e₁ = e₁ * p) (hp₂ : p * e₂ = e₂ * p)
    (hq₁ : q * e₁ = e₁ * q) (hq₂ : q * e₂ = e₂ * q) (hx : x ∈ fourSet p q)
    (hy : y ∈ fourSet e₁ e₂) : x * y = y * x := by
  have h1 : x * e₁ = e₁ * x := commute_of_mem_fourSet hp₁ hq₁ hx
  have h2 : x * e₂ = e₂ * x := commute_of_mem_fourSet hp₂ hq₂ hx
  exact (commute_of_mem_fourSet h1.symm h2.symm hy).symm

theorem conj_mem_fourSet {e₁ e₂ y : U} (a : U) (hy : y ∈ fourSet e₁ e₂) :
    a * y * a⁻¹ ∈ fourSet (a * e₁ * a⁻¹) (a * e₂ * a⁻¹) := by
  rcases mem_four hy with h | h | h | h <;> rw [h]
  · rw [mul_one, mul_inv_cancel]; exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · refine Or.inr (Or.inr (Or.inr (Set.mem_singleton_iff.mpr ?_)))
    group

end FourConj

structure SwapFacts {W : Type*} [Group W] (e₁ e₂ c₁ c₂ a₀ b₀ : W) : Prop where
  e₁_sq : e₁ * e₁ = 1
  e₂_sq : e₂ * e₂ = 1
  comm : e₁ * e₂ = e₂ * e₁
  e₁_ne : e₁ ≠ 1
  e₂_ne : e₂ ≠ 1
  c₁_comm : c₁ * e₁ = e₁ * c₁
  c₁_swap : c₁ * e₂ = e₁ * e₂ * c₁
  c₂_comm : c₂ * e₂ = e₂ * c₂
  c₂_swap : c₂ * e₁ = e₂ * e₁ * c₂
  f₁_e₁ : a₀ * e₁ * a₀⁻¹ * e₁ = e₁ * (a₀ * e₁ * a₀⁻¹)
  f₁_e₂ : a₀ * e₁ * a₀⁻¹ * e₂ = e₂ * (a₀ * e₁ * a₀⁻¹)
  f₂_e₁ : a₀ * e₂ * a₀⁻¹ * e₁ = e₁ * (a₀ * e₂ * a₀⁻¹)
  f₂_e₂ : a₀ * e₂ * a₀⁻¹ * e₂ = e₂ * (a₀ * e₂ * a₀⁻¹)
  f₁_not : a₀ * e₁ * a₀⁻¹ ∉ fourSet e₁ e₂
  g₁_mem : ∃ x ∈ fourSet e₁ e₂, ∃ y ∈ fourSet (a₀ * e₁ * a₀⁻¹) (a₀ * e₂ * a₀⁻¹),
    b₀ * e₁ * b₀⁻¹ = x * y
  g₂_mem : ∃ x ∈ fourSet e₁ e₂, ∃ y ∈ fourSet (a₀ * e₁ * a₀⁻¹) (a₀ * e₂ * a₀⁻¹),
    b₀ * e₂ * b₀⁻¹ = x * y
  g₁_not : b₀ * e₁ * b₀⁻¹ ∉ fourSet e₁ e₂
  g₁_not' : b₀ * e₁ * b₀⁻¹ ∉ fourSet (a₀ * e₁ * a₀⁻¹) (a₀ * e₂ * a₀⁻¹)

section End

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {W : Type*} [Group W]
  {ψ : normalizer (A : Set G) →* W}

theorem conj_config (hA : AS76b.Hyp31 A) {g y : G}
    (hne : rightConjugate (centralizer (A : Set G)) y ≠
      rightConjugate (centralizer (A : Set G)) g)
    {T' : Subgroup G} (hT' : IsSylowOf 2 T' (rightConjugate (centralizer (A : Set G)) y))
    (hTN : T' ≤ normalizer (rightConjugate A g : Set G)) :
    IsSylowOf 2 (rightConjugate T' g⁻¹) (rightConjugate (centralizer (A : Set G)) (y * g⁻¹)) ∧
      y * g⁻¹ ∉ normalizer (A : Set G) ∧ rightConjugate T' g⁻¹ ≤ normalizer (A : Set G) := by
  refine ⟨?_, fun h => ?_, fun x hx => ?_⟩
  · rw [← rightConjugate_mul]
    exact isSylowOf_conj hT' g⁻¹
  · rw [← hA.standard.2.2.2.1, ← rightConjugate_eq_self_iff] at h
    apply hne
    rw [show y = y * g⁻¹ * g by group, ← rightConjugate_mul, h]
  · have hx' := hTN ((mem_rightConjugate_iff _ g⁻¹ x).mp hx)
    rw [mem_normalizer_conj_iff] at hx'
    simpa [mul_assoc] using hx'

omit [Finite G] in
theorem commute_of_mem (hψ : IsActionHom A ⊤ ψ) (hZ : Odd (Nat.card (center A))) {c t : G}
    (hc : c ∈ A) (ht : t ∈ A) (ht2 : t ^ 2 = 1)
    (h : ψ ⟨c, le_normalizer hc⟩ * ψ ⟨t, le_normalizer ht⟩ =
      ψ ⟨t, le_normalizer ht⟩ * ψ ⟨c, le_normalizer hc⟩) : c * t = t * c :=
  commute_of_decomp (t := ⟨t, le_normalizer ht⟩) hψ hZ hc ht (one_mem _) (mul_one t).symm ht2
    rfl h

omit [Finite G] in
theorem map_conj_mk {c t : G} (hc : c ∈ A) (ht : t ∈ A) (hct : c * t * c⁻¹ ∈ A) :
    ψ ⟨c * t * c⁻¹, le_normalizer hct⟩ =
      ψ ⟨c, le_normalizer hc⟩ * ψ ⟨t, le_normalizer ht⟩ * (ψ ⟨c, le_normalizer hc⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem exists_conj_of_mem_fourSet {U : Type*} [Group U] {e₁ e₂ a x : U}
    (hx : x ∈ fourSet (a * e₁ * a⁻¹) (a * e₂ * a⁻¹)) : ∃ y ∈ fourSet e₁ e₂, x = a * y * a⁻¹ := by
  rcases mem_four hx with h | h | h | h <;> rw [h]
  · exact ⟨1, Or.inl rfl, by group⟩
  · exact ⟨e₁, Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨e₂, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  · exact ⟨e₁ * e₂, Or.inr (Or.inr (Or.inr rfl)), by group⟩

theorem false_of_swapFacts [Finite W] (h32 : AS76b.Lemma32) (hA : AS76b.Hyp31 A)
    {X₀ : Type*} [Group X₀] (hW : AutModel X₀ W ⊤) (e : ↥A ⧸ center ↥A ≃* X₀)
    (hψ : IsActionHom A ⊤ ψ) {e₁ e₂ c₁ c₂ a₀ b₀ : W} (hF : SwapFacts e₁ e₂ c₁ c₂ a₀ b₀)
    (hc : YCensus17 (⊤ : Subgroup W)
      (fun E => ∃ w : W, E = (closure ({e₁, e₂} : Set W)).map (MulAut.conj w).toMonoidHom))
    (h175 : ∀ t : normalizer (A : Set G), (t : G) ^ 2 = 1 → (∃ w : W, ψ t = w * e₁ * w⁻¹) →
      Odd (Nat.card (center A)))
    {g : G} (hg : g ∉ normalizer (A : Set G)) {R T : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hTN : T ≤ normalizer (A : Set G)) (hTR : ∀ t ∈ T, ∀ r ∈ R, t * r = r * t) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨he₁, he₂, he, he₁1, he₂1, hc₁, hc₁', hc₂, hc₂', hf₁₁, hf₁₂, hf₂₁, hf₂₂, hf₁n, hg₁m,
    hg₂m, hg₁n, hg₁n'⟩ := hF
  have hWX : ⁅(⊤ : Subgroup W), ⊤⁆ ≤ (⊤ : Subgroup W) := le_top
  have hTab := sq_eq_one_of_isSylowOf h32 hA hT
  obtain ⟨w, hw⟩ := exc17_of_sylow h32 hA hW hWX e hψ hc hg
    (hT.of_le (le_inf hT.le hTN) inf_le_left) hT
  have hsurj : ∀ x ∈ fourSet e₁ e₂, ∃ s, ∃ hs : s ∈ T, ψ ⟨s, hTN hs⟩ = w * x * w⁻¹ := by
    intro x hx
    have h1 : w * x * w⁻¹ ∈ (T.subgroupOf (normalizer (A : Set G))).map ψ := by
      rw [hw]
      exact ⟨x, (mem_closure_pair_iff he₁ he₂ he).mpr hx, rfl⟩
    obtain ⟨m, hm, hme⟩ := h1
    exact ⟨m, hm, hme⟩
  have hover : ∀ s (hs : s ∈ T), ∃ x ∈ fourSet e₁ e₂, ψ ⟨s, hTN hs⟩ = w * x * w⁻¹ := by
    intro s hs
    have h1 : ψ ⟨s, hTN hs⟩ ∈ (T.subgroupOf (normalizer (A : Set G))).map ψ := ⟨_, hs, rfl⟩
    rw [hw] at h1
    obtain ⟨x, hx, hxe⟩ := h1
    exact ⟨x, (mem_closure_pair_iff he₁ he₂ he).mp hx, hxe.symm⟩
  obtain ⟨t₁, ht₁, hψ₁⟩ := hsurj e₁ (Or.inr (Or.inl rfl))
  have ht₁1 : t₁ ≠ 1 := by
    intro h1
    apply he₁1
    have h2 : w * e₁ * w⁻¹ = 1 := by
      rw [← hψ₁, show (⟨t₁, hTN ht₁⟩ : normalizer (A : Set G)) = 1 from Subtype.ext h1, map_one]
    have := congrArg (fun y => w⁻¹ * y * w) h2
    simpa [mul_assoc] using this
  have hZ : Odd (Nat.card (center A)) := h175 ⟨t₁, hTN ht₁⟩ (hTab t₁ ht₁) ⟨w, hψ₁⟩
  have hTA : T ≤ A := le_of_swap h32 hA hψ hZ hg hT hTN hR hTR he₁ he₂ he he₁1 he₂1 hc₁ hc₁'
    hc₂ hc₂' hw
  have hTψ : ∀ s (hs : s ∈ T), ψ ⟨s, hTN hs⟩ = ψ ⟨s, le_normalizer (hTA hs)⟩ := fun _ _ => rfl
  have key : ∀ (c : G) (hc : c ∈ A) (c₀ : W), ψ ⟨c, le_normalizer hc⟩ = w * c₀ * w⁻¹ →
      (∀ y ∈ fourSet e₁ e₂, ∀ z ∈ fourSet e₁ e₂, c₀ * y * c₀⁻¹ * z = z * (c₀ * y * c₀⁻¹)) →
      c₀ * e₁ * c₀⁻¹ ∉ fourSet e₁ e₂ →
      (∀ t ∈ T, ∀ t' ∈ T, t * (c * t' * c⁻¹) = c * t' * c⁻¹ * t) ∧
        rightConjugate T c⁻¹ ≤ rightConjugate A g := by
    intro c hcA c₀ hce hcomm hnot
    have hmem : ∀ t' ∈ T, c * t' * c⁻¹ ∈ A := fun t' ht' =>
      A.mul_mem (A.mul_mem hcA (hTA ht')) (A.inv_mem hcA)
    have hψc : ∀ t' (ht' : t' ∈ T), ∃ y ∈ fourSet e₁ e₂,
        ψ ⟨c * t' * c⁻¹, le_normalizer (hmem t' ht')⟩ = w * (c₀ * y * c₀⁻¹) * w⁻¹ := by
      intro t' ht'
      obtain ⟨y, hy, hye⟩ := hover t' ht'
      refine ⟨y, hy, ?_⟩
      rw [map_conj_mk hcA (hTA ht') (hmem t' ht'), hce, ← hTψ t' ht', hye]
      group
    have hTc : ∀ t ∈ T, ∀ t' ∈ T, t * (c * t' * c⁻¹) = c * t' * c⁻¹ * t := by
      intro t ht t' ht'
      obtain ⟨y, hy, hye⟩ := hover t ht
      obtain ⟨y', hy', hye'⟩ := hψc t' ht'
      refine (commute_of_mem hψ hZ (hmem t' ht') (hTA ht) (hTab t ht) ?_).symm
      rw [hye', ← hTψ t ht, hye]
      exact conj_comm w (hcomm y' hy' y hy)
    refine ⟨hTc, ?_⟩
    set Tc := rightConjugate T c⁻¹ with hTcdef
    have hTcmem : ∀ x, x ∈ Tc ↔ c⁻¹ * x * c ∈ T := fun x => by
      rw [hTcdef, mem_rightConjugate_iff, inv_inv]
    have hTcS : IsSylowOf 2 Tc (rightConjugate (centralizer (A : Set G)) (g * c⁻¹)) := by
      rw [← rightConjugate_mul]
      exact isSylowOf_conj hT c⁻¹
    have hTcT : ∀ x ∈ Tc, ∀ t ∈ T, x * t = t * x := by
      intro x hx t ht
      have h1 := hTc t ht _ ((hTcmem x).mp hx)
      rw [show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at h1
      exact h1.symm
    have hne : rightConjugate (centralizer (A : Set G)) (g * c⁻¹) ≠
        rightConjugate (centralizer (A : Set G)) g := by
      intro heq
      have hTcK : Tc ≤ rightConjugate (centralizer (A : Set G)) g := heq ▸ hTcS.le
      have hTN' : T ≤ normalizer (Tc : Set G) := fun t ht =>
        Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
          hTcT x hx t ht)
      have hpg := IsPGroup.to_sup_of_normal_right' hT.isPGroup hTcS.isPGroup hTN'
      have hsup := hT.eq_of_le le_sup_left (sup_le hT.le hTcK) hpg
      have hx1 : c * t₁ * c⁻¹ ∈ Tc := by
        rw [hTcmem, show c⁻¹ * (c * t₁ * c⁻¹) * c = t₁ by group]
        exact ht₁
      have hx : c * t₁ * c⁻¹ ∈ T := by
        rw [← hsup]
        exact mem_sup_right hx1
      obtain ⟨y, hy, hye⟩ := hover _ hx
      apply hnot
      have h1 : w * (c₀ * e₁ * c₀⁻¹) * w⁻¹ = w * y * w⁻¹ := by
        rw [← hye]
        rw [show (⟨c * t₁ * c⁻¹, hTN hx⟩ : normalizer (A : Set G)) =
          ⟨c * t₁ * c⁻¹, le_normalizer (hmem t₁ ht₁)⟩ from rfl,
          map_conj_mk hcA (hTA ht₁) (hmem t₁ ht₁), hce,
          ← hTψ t₁ ht₁, hψ₁]
        group
      have h2 : c₀ * e₁ * c₀⁻¹ = y := by
        have := congrArg (fun z => w⁻¹ * z * w) h1
        simpa [mul_assoc] using this
      rw [h2]
      exact hy
    have hTcN : Tc ≤ normalizer (rightConjugate A g : Set G) := fun x hx =>
      mem_normalizer_conj_of_commute hA (hT.le ht₁) ht₁1 (hTab t₁ ht₁) (hTcT x hx t₁ ht₁)
    obtain ⟨hS', hy', hN'⟩ := conj_config hA hne hTcS hTcN
    obtain ⟨w', hw'⟩ := exc17_of_sylow h32 hA hW hWX e hψ hc hy'
      (hS'.of_le (le_inf hS'.le hN') inf_le_left) hS'
    have hR' : IsSylowOf 2 (rightConjugate T g⁻¹) (centralizer (A : Set G)) := by
      have := isSylowOf_conj hT g⁻¹
      rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
    have hTR' : ∀ x ∈ rightConjugate Tc g⁻¹, ∀ r ∈ rightConjugate T g⁻¹, x * r = r * x := by
      intro x hx r hr
      rw [mem_rightConjugate_iff, inv_inv] at hx hr
      have h1 := hTcT _ hx _ hr
      calc x * r = g * ((g⁻¹ * x * g) * (g⁻¹ * r * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * r * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
        _ = r * x := by group
    have hle := le_of_swap h32 hA hψ hZ hy' hS' hN' hR' hTR' he₁ he₂ he he₁1 he₂1 hc₁ hc₁' hc₂
      hc₂' hw'
    intro x hx
    rw [mem_rightConjugate_iff]
    have : g * x * g⁻¹ ∈ rightConjugate Tc g⁻¹ := by
      rw [mem_rightConjugate_iff, inv_inv]
      rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hx
    exact hle this
  have hcommE : ∀ {p q : W}, p * e₁ = e₁ * p → p * e₂ = e₂ * p → q * e₁ = e₁ * q →
      q * e₂ = e₂ * q → ∀ (c₀ : W), c₀ * e₁ * c₀⁻¹ = p → c₀ * e₂ * c₀⁻¹ = q →
      ∀ y ∈ fourSet e₁ e₂, ∀ z ∈ fourSet e₁ e₂, c₀ * y * c₀⁻¹ * z = z * (c₀ * y * c₀⁻¹) := by
    intro p q hp₁ hp₂ hq₁ hq₂ c₀ hp hq y hy z hz
    have h1 := conj_mem_fourSet c₀ hy
    rw [hp, hq] at h1
    exact commute_fourSet hp₁ hp₂ hq₁ hq₂ h1 hz
  have hE : ∀ {x : W}, x ∈ fourSet e₁ e₂ → x * e₁ = e₁ * x ∧ x * e₂ = e₂ * x := fun hx =>
    ⟨commute_of_mem_fourSet rfl he.symm hx, commute_of_mem_fourSet he rfl hx⟩
  have hFc : ∀ {x : W}, x ∈ fourSet (a₀ * e₁ * a₀⁻¹) (a₀ * e₂ * a₀⁻¹) →
      x * e₁ = e₁ * x ∧ x * e₂ = e₂ * x := fun hx =>
    ⟨commute_of_mem_fourSet hf₁₁ hf₂₁ hx, commute_of_mem_fourSet hf₁₂ hf₂₂ hx⟩
  have hG : ∀ {g' : W}, (∃ x ∈ fourSet e₁ e₂, ∃ y ∈ fourSet (a₀ * e₁ * a₀⁻¹) (a₀ * e₂ * a₀⁻¹),
      g' = x * y) → g' * e₁ = e₁ * g' ∧ g' * e₂ = e₂ * g' := by
    rintro g' ⟨x, hx, y, hy, rfl⟩
    obtain ⟨hx₁, hx₂⟩ := hE hx
    obtain ⟨hy₁, hy₂⟩ := hFc hy
    exact ⟨by rw [mul_assoc, hy₁, ← mul_assoc, hx₁, mul_assoc],
      by rw [mul_assoc, hy₂, ← mul_assoc, hx₂, mul_assoc]⟩
  obtain ⟨a, ha, hae⟩ := hψ.exists_eq (w * a₀ * w⁻¹) (mem_top _)
  obtain ⟨b, hb, hbe⟩ := hψ.exists_eq (w * b₀ * w⁻¹) (mem_top _)
  obtain ⟨hTa, hTaA⟩ := key a ha a₀ hae (hcommE hf₁₁ hf₁₂ hf₂₁ hf₂₂ a₀ rfl rfl) hf₁n
  obtain ⟨-, hTbA⟩ := key b hb b₀ hbe (hcommE (hG hg₁m).1 (hG hg₁m).2 (hG hg₂m).1 (hG hg₂m).2
    b₀ rfl rfl) hg₁n
  obtain ⟨x₁, hx₁, y₁, hy₁, hg₁⟩ := hg₁m
  obtain ⟨y, hy, rfl⟩ := exists_conj_of_mem_fourSet hy₁
  obtain ⟨t, ht, hψt⟩ := hsurj x₁ hx₁
  obtain ⟨t', ht', hψt'⟩ := hsurj y hy
  have huA : a * t' * a⁻¹ ∈ A := A.mul_mem (A.mul_mem ha (hTA ht')) (A.inv_mem ha)
  have hvA : b * t₁ * b⁻¹ ∈ A := A.mul_mem (A.mul_mem hb (hTA ht₁)) (A.inv_mem hb)
  have htuA : t * (a * t' * a⁻¹) ∈ A := A.mul_mem (hTA ht) huA
  have htu2 : (t * (a * t' * a⁻¹)) ^ 2 = 1 := by
    rw [Commute.mul_pow (hTa t ht t' ht') 2, hTab t ht, one_mul, conj_pow, hTab t' ht', mul_one,
      mul_inv_cancel]
  have hv2 : (b * t₁ * b⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hTab t₁ ht₁, mul_one, mul_inv_cancel]
  have heq : (⟨t * (a * t' * a⁻¹), le_normalizer htuA⟩ : normalizer (A : Set G)) =
      ⟨b * t₁ * b⁻¹, le_normalizer hvA⟩ := by
    refine eq_of_map_eq hψ hZ htu2 hv2 (A.mul_mem (A.inv_mem htuA) hvA) ?_
    rw [map_conj_mk hb (hTA ht₁) hvA, hbe, ← hTψ t₁ ht₁, hψ₁,
      show (⟨t * (a * t' * a⁻¹), le_normalizer htuA⟩ : normalizer (A : Set G)) =
        ⟨t, le_normalizer (hTA ht)⟩ * ⟨a * t' * a⁻¹, le_normalizer huA⟩ from Subtype.ext rfl,
      map_mul, map_conj_mk ha (hTA ht') huA, hae, ← hTψ t ht, ← hTψ t' ht', hψt, hψt']
    calc w * x₁ * w⁻¹ * (w * a₀ * w⁻¹ * (w * y * w⁻¹) * (w * a₀ * w⁻¹)⁻¹)
        = w * (x₁ * (a₀ * y * a₀⁻¹)) * w⁻¹ := by group
      _ = w * (b₀ * e₁ * b₀⁻¹) * w⁻¹ := by rw [hg₁]
      _ = w * b₀ * w⁻¹ * (w * e₁ * w⁻¹) * (w * b₀ * w⁻¹)⁻¹ := by group
  have heqG : t * (a * t' * a⁻¹) = b * t₁ * b⁻¹ := congrArg Subtype.val heq
  have huAg : a * t' * a⁻¹ ∈ rightConjugate A g := hTaA (by
    rw [mem_rightConjugate_iff, inv_inv, show a⁻¹ * (a * t' * a⁻¹) * a = t' by group]
    exact ht')
  have hvAg : b * t₁ * b⁻¹ ∈ rightConjugate A g := hTbA (by
    rw [mem_rightConjugate_iff, inv_inv, show b⁻¹ * (b * t₁ * b⁻¹) * b = t₁ by group]
    exact ht₁)
  have htAg : t ∈ rightConjugate A g := by
    have h1 := mul_mem hvAg (inv_mem huAg)
    rwa [← heqG, mul_inv_cancel_right] at h1
  have ht1 : t = 1 := by
    have hgA : g * t * g⁻¹ ∈ A := (mem_rightConjugate_iff _ g t).mp htAg
    have hgK : g * t * g⁻¹ ∈ centralizer (A : Set G) := (mem_rightConjugate_iff _ g t).mp (hT.le ht)
    have h2 : (g * t * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hTab t ht, mul_one, mul_inv_cancel]
    have h3 := eq_one_of_mem_of_sq_eq_one hZ hgA hgK h2
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  apply hg₁n'
  have hψeq : ψ ⟨b * t₁ * b⁻¹, le_normalizer hvA⟩ = ψ ⟨a * t' * a⁻¹, le_normalizer huA⟩ := by
    congr 1
    apply Subtype.ext
    show b * t₁ * b⁻¹ = a * t' * a⁻¹
    rw [← heqG, ht1, one_mul]
  rw [map_conj_mk hb (hTA ht₁) hvA, map_conj_mk ha (hTA ht') huA, hbe, hae, ← hTψ t₁ ht₁,
    ← hTψ t' ht', hψ₁, hψt'] at hψeq
  have h1 : b₀ * e₁ * b₀⁻¹ = a₀ * y * a₀⁻¹ := by
    have := congrArg (fun z => w⁻¹ * z * w) hψeq
    calc b₀ * e₁ * b₀⁻¹ = w⁻¹ * (w * b₀ * w⁻¹ * (w * e₁ * w⁻¹) * (w * b₀ * w⁻¹)⁻¹) * w := by
          group
      _ = w⁻¹ * (w * a₀ * w⁻¹ * (w * y * w⁻¹) * (w * a₀ * w⁻¹)⁻¹) * w := this
      _ = a₀ * y * a₀⁻¹ := by group
  rw [h1]
  exact conj_mem_fourSet a₀ hy

end End

end CFSG.ComponentClassification.RankTwoSporadic.Co1

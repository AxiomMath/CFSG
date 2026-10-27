module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion

public section

namespace CFSG.AGLEmbedding

variable {X : Type} [Group X]

theorem mem_centralizer_map_conj_of_mem {L : Subgroup X} {y : X}
    (hy : y ∈ Subgroup.centralizer (L : Set X)) (ν : X) :
    ν * y * ν⁻¹ ∈ Subgroup.centralizer
      ((L.map (MulAut.conj ν).toMonoidHom : Subgroup X) : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  have hky : k * y = y * k := Subgroup.mem_centralizer_iff.mp hy k hk
  change ν * k * ν⁻¹ * (ν * y * ν⁻¹) = ν * y * ν⁻¹ * (ν * k * ν⁻¹)
  calc ν * k * ν⁻¹ * (ν * y * ν⁻¹) = ν * (k * y) * ν⁻¹ := by group
    _ = ν * (y * k) * ν⁻¹ := by rw [hky]
    _ = ν * y * ν⁻¹ * (ν * k * ν⁻¹) := by group

theorem conj_mem_conjMap {L : Subgroup X} {k : X} (hk : k ∈ L) (ν : X) :
    ν * k * ν⁻¹ ∈ L.map (MulAut.conj ν).toMonoidHom :=
  ⟨k, hk, rfl⟩

variable [Finite X]

omit [Finite X] in
theorem card_eq_nine_or_of_not_isCyclic {E R : Subgroup X} (hER : E ≤ R)
    (hRc : Nat.card R = 27) (hnc : ¬ IsCyclic E) : Nat.card E = 9 ∨ Nat.card E = 27 := by
  have hdvd : Nat.card E ∣ 27 := hRc ▸ Subgroup.card_dvd_of_le hER
  have h27 : (27 : ℕ) = 3 ^ 3 := by norm_num
  rw [h27, Nat.dvd_prime_pow Nat.prime_three] at hdvd
  obtain ⟨k, hk, hEk⟩ := hdvd
  interval_cases k
  · exfalso
    apply hnc
    have : Subsingleton E := by
      rw [pow_zero] at hEk
      exact (Nat.card_eq_one_iff_unique.mp hEk).1
    exact isCyclic_of_subsingleton
  · exfalso
    apply hnc
    rw [pow_one] at hEk
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card hEk
  · left; rw [hEk]; norm_num
  · right; rw [hEk]; norm_num

theorem false_of_conj_mem_inf {Rb K₁ : Subgroup X} {y ν : X}
    (hRc : Nat.card Rb = 27) (hEc : Nat.card (Rb ⊓ K₁ : Subgroup X) = 9)
    (hνR : ∀ r ∈ Rb, ν * r * ν⁻¹ ∈ Rb)
    (hcomp : K₁.map (MulAut.conj ν).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj ν).toMonoidHom ≤ Subgroup.centralizer (K₁ : Set X))
    (hKC : K₁ ⊓ Subgroup.centralizer (K₁ : Set X) = ⊥)
    (hy : y ∈ Subgroup.centralizer (K₁ : Set X))
    (hyE : ν * y * ν⁻¹ ∈ Rb ⊓ K₁) (hy1 : ν * y * ν⁻¹ ≠ 1) : False := by
  have hyc := mem_centralizer_map_conj_of_mem hy ν
  rcases hcomp with heq | hle
  · rw [heq] at hyc
    have hm : ν * y * ν⁻¹ ∈ K₁ ⊓ Subgroup.centralizer (K₁ : Set X) := ⟨hyE.2, hyc⟩
    rw [hKC, Subgroup.mem_bot] at hm
    exact hy1 hm
  · have hE'R : (Rb ⊓ K₁).map (MulAut.conj ν).toMonoidHom ≤ Rb := by
      rintro _ ⟨e, he, rfl⟩
      exact hνR e he.1
    have hE'C : (Rb ⊓ K₁).map (MulAut.conj ν).toMonoidHom ≤
        Subgroup.centralizer (K₁ : Set X) := by
      rintro _ ⟨e, he, rfl⟩
      exact hle ⟨e, he.2, rfl⟩
    have hdisj : (Rb ⊓ K₁) ⊓ (Rb ⊓ K₁).map (MulAut.conj ν).toMonoidHom = ⊥ := by
      rw [eq_bot_iff, ← hKC]
      exact inf_le_inf inf_le_right hE'C
    have hinj : Function.Injective (MulAut.conj ν).toMonoidHom :=
      fun a b h => (MulAut.conj ν).injective h
    have hcard' : Nat.card ((Rb ⊓ K₁).map (MulAut.conj ν).toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective hinj, hEc]
    have h := mul_card_le_of_inf_eq_bot (inf_le_left : Rb ⊓ K₁ ≤ Rb) hE'R hdisj
    rw [hEc, hcard', hRc] at h
    norm_num at h

theorem mem_zpowers_of_isCompL34 {Rb Tb K₁ : Subgroup X} {ζ z₁ : X}
    (hab : ∀ a ∈ Rb, ∀ b ∈ Rb, a * b = b * a)
    (hexp : ∀ r ∈ Rb, r ^ 3 = 1)
    (hRc : Nat.card Rb = 27) (hTc : Nat.card Tb = 9) (hTR : Tb ≤ Rb) (hζR : ζ ∈ Rb)
    (hdec : ∀ r ∈ Rb, ∃ t ∈ Tb, ∃ i : ℕ, r = t * ζ ^ i)
    (htr : ∀ t ∈ Tb, t ≠ 1 → ∀ s ∈ Tb, s ≠ 1 → ∃ ν : X, ν * ζ * ν⁻¹ = ζ ∧
      (∀ x ∈ Tb, ν * x * ν⁻¹ ∈ Tb) ∧ (∀ r ∈ Rb, ν * r * ν⁻¹ ∈ Rb) ∧ ν * t * ν⁻¹ = s)
    (hcomp : ∀ ν : X, K₁.map (MulAut.conj ν).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj ν).toMonoidHom ≤ Subgroup.centralizer (K₁ : Set X))
    (hKC : K₁ ⊓ Subgroup.centralizer (K₁ : Set X) = ⊥)
    (hnc : ¬ IsCyclic (Rb ⊓ K₁ : Subgroup X))
    (hz₁R : z₁ ∈ Rb) (hz₁K : z₁ ∉ K₁) (hz₁C : z₁ ∈ Subgroup.centralizer (K₁ : Set X)) :
    z₁ ∈ Subgroup.zpowers ζ := by
  have hζ3 : ζ ^ 3 = 1 := hexp ζ hζR
  have hmod : ∀ j : ℕ, ζ ^ j = ζ ^ (j % 3) := fun j => by
    conv_lhs => rw [← Nat.mod_add_div j 3, pow_add, pow_mul, hζ3, one_pow, mul_one]
  have hζT : ζ ∉ Tb := by
    intro hζ
    have hle : Rb ≤ Tb := fun r hr => by
      obtain ⟨t, ht, i, rfl⟩ := hdec r hr
      exact Tb.mul_mem ht (Tb.pow_mem hζ i)
    have := Subgroup.card_le_of_le hle
    rw [hRc, hTc] at this
    norm_num at this
  have hz₁1 : z₁ ≠ 1 := fun h => hz₁K (h ▸ K₁.one_mem)
  have hz₁o : orderOf z₁ = 3 := orderOf_eq_prime (hexp z₁ hz₁R) hz₁1
  have hEz : (Rb ⊓ K₁) ⊓ Subgroup.zpowers z₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxz⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    have h := mem_zpowers_of_mem_zpowers_of_prime Nat.prime_three hz₁o hxz hx1
    exact hz₁K ((Subgroup.zpowers_le.mpr hxE.2) h)
  have hEc : Nat.card (Rb ⊓ K₁ : Subgroup X) = 9 := by
    rcases card_eq_nine_or_of_not_isCyclic inf_le_left hRc hnc with h | h
    · exact h
    · exfalso
      have h' := mul_card_le_of_inf_eq_bot (inf_le_left : Rb ⊓ K₁ ≤ Rb)
        (Subgroup.zpowers_le.mpr hz₁R) hEz
      rw [h, hRc, Nat.card_zpowers, hz₁o] at h'
      norm_num at h'
  have hET : ∃ u ∈ Rb ⊓ K₁, u ∈ Tb ∧ u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : (Rb ⊓ K₁) ⊓ Tb = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      exact (Subgroup.mem_bot).mpr (hcon x hx1 hx2)
    have h := mul_card_le_of_inf_eq_bot (inf_le_left : Rb ⊓ K₁ ≤ Rb) hTR hbot
    rw [hEc, hTc, hRc] at h
    norm_num at h
  have hA : ∀ y ∈ Subgroup.centralizer (K₁ : Set X), ∀ ν : X,
      (∀ r ∈ Rb, ν * r * ν⁻¹ ∈ Rb) → ν * y * ν⁻¹ ∈ Rb ⊓ K₁ → ν * y * ν⁻¹ ≠ 1 → False :=
    fun y hy ν hνR hyE hy1 => false_of_conj_mem_inf hRc hEc hνR (hcomp ν) hKC hy hyE hy1
  have hmixed : ∀ t' ∈ Tb, t' ≠ 1 → t' * ζ ∈ Subgroup.centralizer (K₁ : Set X) → False := by
    intro t' ht' ht'1 hyC
    have hconjζ : ∀ ν : X, ν * ζ * ν⁻¹ = ζ → ∀ s : X, ν * t' * ν⁻¹ = s →
        ν * (t' * ζ) * ν⁻¹ = s * ζ := fun ν hνζ s hs => by
      calc ν * (t' * ζ) * ν⁻¹ = (ν * t' * ν⁻¹) * (ν * ζ * ν⁻¹) := by group
        _ = s * ζ := by rw [hs, hνζ]
    have hsζ1 : ∀ s ∈ Tb, s * ζ ≠ 1 := fun s hs h1 => hζT (by
      have : ζ = s⁻¹ := by
        calc ζ = s⁻¹ * (s * ζ) := by group
          _ = s⁻¹ := by rw [h1, mul_one]
      rw [this]; exact Tb.inv_mem hs)
    have hB1 : ∀ s ∈ Tb, s ≠ 1 → s * ζ ∈ Rb ⊓ K₁ → False := fun s hs hs1 hsE => by
      obtain ⟨ν, hνζ, -, hνR, hνt⟩ := htr t' ht' ht'1 s hs hs1
      have he := hconjζ ν hνζ s hνt
      exact hA _ hyC ν hνR (he ▸ hsE) (he ▸ hsζ1 s hs)
    have hB : ∀ s ∈ Tb, s * ζ ∈ Rb ⊓ K₁ → False := fun s hs hsE => by
      by_cases hs1 : s = 1
      · subst hs1
        rw [one_mul] at hsE
        obtain ⟨u, huE, huT, hu1⟩ := hET
        exact hB1 u huT hu1 ((Rb ⊓ K₁).mul_mem huE hsE)
      · exact hB1 s hs hs1 hsE
    have hle : Rb ⊓ K₁ ≤ Tb := by
      intro e he
      by_contra heT
      obtain ⟨s, hs, j, hej⟩ := hdec e he.1
      rw [hmod j] at hej
      have hj3 : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases hj : j % 3
      · rw [pow_zero, mul_one] at hej
        exact heT (hej ▸ hs)
      · rw [pow_one] at hej
        exact hB s hs (hej ▸ he)
      · have hsq : e ^ 2 = (s * s) * ζ := by
          have hc : s * ζ = ζ * s := hab s (hTR hs) ζ hζR
          rw [hej]
          calc (s * ζ ^ 2) ^ 2 = s * ζ ^ 2 * (s * ζ ^ 2) := pow_two _
            _ = s * s * ζ ^ 4 := by
              rw [show ζ ^ 2 = ζ * ζ from pow_two ζ,
                show ζ ^ 4 = ζ * ζ * ζ * ζ by simp only [pow_succ, pow_zero, one_mul]]
              calc s * (ζ * ζ) * (s * (ζ * ζ)) = s * (ζ * (ζ * s)) * (ζ * ζ) := by group
                _ = s * (ζ * (s * ζ)) * (ζ * ζ) := by rw [← hc]
                _ = s * ((ζ * s) * ζ) * (ζ * ζ) := by group
                _ = s * ((s * ζ) * ζ) * (ζ * ζ) := by rw [← hc]
                _ = s * s * (ζ * ζ * ζ * ζ) := by group
            _ = s * s * ζ := by rw [hmod 4]; norm_num
        exact hB (s * s) (Tb.mul_mem hs hs) (hsq ▸ (Rb ⊓ K₁).pow_mem he 2)
    have hETb : Rb ⊓ K₁ = Tb := Subgroup.eq_of_le_of_card_ge hle (by rw [hEc, hTc])
    have ht'i : t'⁻¹ ∈ Tb := Tb.inv_mem ht'
    have ht'i1 : t'⁻¹ ≠ 1 := inv_ne_one.mpr ht'1
    obtain ⟨ν, hνζ, -, -, hνt⟩ := htr t' ht' ht'1 t'⁻¹ ht'i ht'i1
    have hTK : Tb ≤ K₁ := hETb ▸ inf_le_right
    have hK : K₁.map (MulAut.conj ν).toMonoidHom = K₁ := by
      rcases hcomp ν with h | h
      · exact h
      · exfalso
        have hmem : ν * t' * ν⁻¹ ∈ K₁ ⊓ Subgroup.centralizer (K₁ : Set X) :=
          ⟨hνt ▸ hTK ht'i, h (conj_mem_conjMap (hTK ht') ν)⟩
        rw [hKC, Subgroup.mem_bot, hνt] at hmem
        exact ht'i1 hmem
    have hyC' := mem_centralizer_map_conj_of_mem hyC ν
    rw [hK, hconjζ ν hνζ t'⁻¹ hνt] at hyC'
    have h2 : t' * t' ∈ Subgroup.centralizer (K₁ : Set X) := by
      have h := Subgroup.mul_mem _ hyC (Subgroup.inv_mem _ hyC')
      have e : t' * ζ * (t'⁻¹ * ζ)⁻¹ = t' * t' := by group
      rwa [e] at h
    have hm : t' * t' ∈ K₁ ⊓ Subgroup.centralizer (K₁ : Set X) :=
      ⟨hTK (Tb.mul_mem ht' ht'), h2⟩
    rw [hKC, Subgroup.mem_bot] at hm
    have h3 : t' ^ 3 = 1 := hexp t' (hTR ht')
    apply ht'1
    calc t' = t' ^ 3 * (t' * t')⁻¹ := by group
      _ = 1 := by rw [h3, hm]; group
  obtain ⟨t₁, ht₁, i, hz₁eq⟩ := hdec z₁ hz₁R
  rw [hmod i] at hz₁eq
  have hi3 : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hi : i % 3
  · rw [pow_zero, mul_one] at hz₁eq
    subst hz₁eq
    obtain ⟨u, huE, huT, hu1⟩ := hET
    obtain ⟨ν, -, -, hνR, hν⟩ := htr z₁ ht₁ hz₁1 u huT hu1
    exact (hA z₁ hz₁C ν hνR (hν ▸ huE) (hν ▸ hu1)).elim
  · rw [pow_one] at hz₁eq
    by_cases ht1 : t₁ = 1
    · rw [hz₁eq, ht1, one_mul]
      exact Subgroup.mem_zpowers ζ
    · exact (hmixed t₁ ht₁ ht1 (hz₁eq ▸ hz₁C)).elim
  · by_cases ht1 : t₁ = 1
    · rw [hz₁eq, ht1, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers ζ) 2
    · exfalso
      have hc : t₁ * ζ = ζ * t₁ := hab t₁ (hTR ht₁) ζ hζR
      have hsq : z₁ ^ 2 = (t₁ * t₁) * ζ := by
        rw [hz₁eq]
        calc (t₁ * ζ ^ 2) ^ 2 = t₁ * (ζ * ζ) * (t₁ * (ζ * ζ)) := by rw [pow_two, pow_two]
          _ = t₁ * (ζ * (ζ * t₁)) * (ζ * ζ) := by group
          _ = t₁ * (ζ * (t₁ * ζ)) * (ζ * ζ) := by rw [← hc]
          _ = t₁ * ((ζ * t₁) * ζ) * (ζ * ζ) := by group
          _ = t₁ * ((t₁ * ζ) * ζ) * (ζ * ζ) := by rw [← hc]
          _ = t₁ * t₁ * ζ ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = t₁ * t₁ * ζ := by rw [hmod 4]; norm_num
      have ht2 : t₁ * t₁ ≠ 1 := fun h => ht1 (by
        have h3 : t₁ ^ 3 = 1 := hexp t₁ (hTR ht₁)
        calc t₁ = t₁ ^ 3 * (t₁ * t₁)⁻¹ := by group
          _ = 1 := by rw [h3, h]; group)
      exact hmixed (t₁ * t₁) (Tb.mul_mem ht₁ ht₁) ht2
        (hsq ▸ Subgroup.pow_mem _ hz₁C 2)

end CFSG.AGLEmbedding

module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGenMain

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem isKleinFour_of_card_four_sq {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem thirteen_le_of_e8 {S : Type} [Group S] [Finite S] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (h9 : p ^ f ≠ 9) (hL : Blueprint.LieModel S .PSL 2 p f)
    {E : Subgroup (MulAut S)} (hE2 : ∀ x ∈ E, x * x = 1) (hE8 : Nat.card E = 8) :
    13 ≤ p ^ f := by
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hL
  have hodd := isOddPrimePower_of hp hp2 hf hF
  set E' := E.map (autEquiv e).toMonoidHom with hE'
  have hE'2 : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change autEquiv e x * autEquiv e x = 1
    rw [← map_mul, hE2 x hx, map_one]
  have hE'8 : Nat.card E' = 8 := by
    rw [hE', card_map_of_injective (autEquiv e).injective, hE8]
  obtain ⟨x₀, hx₀E, hx₀r⟩ := exists_right_ne_one_of_card_eight hodd E' hE'2 hE'8.ge
  have hψ2 : x₀.right * x₀.right = 1 := by
    have := congrArg SemidirectProduct.right (hE'2 x₀ hx₀E)
    rwa [SemidirectProduct.mul_right, SemidirectProduct.one_right] at this
  obtain ⟨m, hm⟩ := even_of_ringAut hp hF hψ2 hx₀r
  have hq : p ^ f = (p ^ m) ^ 2 := by rw [hm, ← pow_mul, mul_two]
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hm1 : 1 ≤ m := by omega
  have hpm : 3 ≤ p ^ m := le_trans hp3 (Nat.le_self_pow (by omega) p)
  by_contra h
  push Not at h
  rw [hq] at h h9
  have h4 : p ^ m ≤ 3 := by nlinarith
  have h3 : p ^ m = 3 := by omega
  rw [h3] at h9
  norm_num at h9

theorem footeL2FourgroupGeneration :
    ∀ (Y : Type) [Group Y] [Finite Y] (S : Subgroup Y), S.Normal →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ p ^ f ≠ 9 ∧
        Blueprint.LieModel ↥S .PSL 2 p f) →
      ∀ E : Subgroup Y, (∀ e ∈ E, e ^ 2 = 1) → Nat.card E = 8 →
        E ⊓ centralizer (S : Set Y) = ⊥ →
        S ≤ ⨆ (X : Subgroup Y) (_ : X ≤ E) (_ : 4 ≤ Nat.card X), normalizer (X : Set Y) := by
  rintro Y _ _ S hSn ⟨p, f, hp, hp2, hf, -, h9, hL⟩ E hE2 hE8 hEC
  have := hSn
  set ι : E →* MulAut S := (MulAut.conjNormal : Y →* MulAut S).comp E.subtype with hιdef
  have hιapp : ∀ (x : E) (s : S), ((ι x s : S) : Y) = (x : Y) * s * (x : Y)⁻¹ := fun x s =>
    MulAut.conjNormal_apply (x : Y) s
  have hι : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxC : (x : Y) ∈ E ⊓ centralizer (S : Set Y) := by
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [mem_centralizer_iff]
      intro s hs
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hx ⟨s, hs⟩)
      rw [hιapp] at h1
      change (x : Y) * s * (x : Y)⁻¹ = s at h1
      calc s * x = (x : Y) * s * (x : Y)⁻¹ * x := by rw [h1]
        _ = x * s := by group
    rw [hEC, mem_bot] at hxC
    exact (mem_bot).mpr (Subtype.ext hxC)
  have hÊ2 : ∀ x ∈ ι.range, x * x = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
      exact hE2 x x.2)
    rw [this, map_one]
  have hÊ8 : Nat.card ι.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, hE8]
  have h13 := thirteen_le_of_e8 hp hp2 hf h9 hL hÊ2 hÊ8
  have hgen := fourgroup_fix_generation hp hp2 h13 hL hÊ2 hÊ8
  set T := ⨆ (X : Subgroup Y) (_ : X ≤ E) (_ : 4 ≤ Nat.card X), normalizer (X : Set Y) with hT
  have hle : (⨆ (W : Subgroup (MulAut S)) (_ : W ≤ ι.range) (_ : Nat.card W = 4),
      ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S)) ≤
        T.comap S.subtype := by
    refine iSup_le fun W => iSup_le fun hWE => iSup_le fun hW4 => ?_
    intro s hs
    set X := (W.comap ι).map E.subtype with hX
    have hXE : X ≤ E := map_subtype_le _
    have hX4 : Nat.card X = 4 := by
      rw [hX, card_map_of_injective E.subtype_injective, ← card_map_of_injective hι,
        map_comap_eq_self hWE, hW4]
    have hsN : (s : Y) ∈ normalizer (X : Set Y) := by
      apply centralizer_le_normalizer
      rw [mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      have hfix : ι x s = s := mem_iInf.mp (mem_iInf.mp hs (ι x)) hx
      have h1 := congrArg Subtype.val hfix
      rw [hιapp] at h1
      change (x : Y) * s = s * x
      calc (x : Y) * s = (x : Y) * s * (x : Y)⁻¹ * x := by group
        _ = s * x := by rw [h1]
    exact (show normalizer (X : Set Y) ≤ T from
      le_iSup₂_of_le X hXE (le_iSup_of_le hX4.ge le_rfl)) hsN
  rw [hgen] at hle
  intro s hs
  exact hle (mem_top ⟨s, hs⟩)

theorem foote47FourgroupGeneration_psl2 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h9 : p ^ f ≠ 9)
    (hL : Blueprint.LieModel S .PSL 2 p f) (T : Subgroup (MulAut S))
    (hT : ∃ F : Subgroup (MulAut S), F ≤ T ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8) :
    ⨆ (W : Subgroup (MulAut S)) (_ : IsKleinFour W)
      (_ : ∃ F : Subgroup (MulAut S), W ≤ F ∧ F ≤ T ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8),
        ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S) = ⊤ := by
  obtain ⟨F₀, hF₀T, hF₀2, hF₀8⟩ := hT
  have h13 := thirteen_le_of_e8 hp hp2 hf h9 hL hF₀2 hF₀8
  rw [eq_top_iff, ← fourgroup_fix_generation hp hp2 h13 hL hF₀2 hF₀8]
  refine iSup_le fun W => iSup_le fun hWF => iSup_le fun hW4 => ?_
  have hK : IsKleinFour W := isKleinFour_of_card_four_sq hW4 fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]; exact hF₀2 _ (hWF x.2))
  exact le_iSup₂_of_le W hK (le_iSup_of_le ⟨F₀, hWF, hF₀T, hF₀2, hF₀8⟩ le_rfl)

end CFSG.ComponentClassification.AutL2Facts

module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Frame

public section

namespace CFSG.ClassicalInvolution.NDB.FourFrame

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth CFSG.ClassicalInvolution.Asc77 QuadraticMap

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

section Frame

variable (fr : Frame Q)

theorem nd_span (hQ : (polarBilin Q).Nondegenerate) : PolarNondegOn Q fr.span :=
  Asc77.polarNondegOn_of_isCompl hQ fr.isCompl_span_perp
    (fun _ hx _ hy => polar_perp_of_mem_span fr hx hy)

theorem nd_perp (hQ : (polarBilin Q).Nondegenerate) : PolarNondegOn Q fr.perp :=
  Asc77.polarNondegOn_of_isCompl hQ fr.isCompl_span_perp.symm
    (fun _ hx _ hy => by rw [polar_comm]; exact polar_perp_of_mem_span fr hy hx)

theorem splitInv (hQ : (polarBilin Q).Nondegenerate) :
    SplitInv Q fr.span fr.perp (fr.La (-1)) where
  ndS := nd_span fr hQ
  ndT := nd_perp fr hQ
  orth := fun _ hx _ hy => polar_perp_of_mem_span fr hx hy
  top := fr.isCompl_span_perp.sup_eq_top
  negS := fun _ hx => La_neg_one_of_mem_span fr hx
  fixT := fun _ hx => La_neg_one_of_mem_perp fr hx

theorem exists_decomp (x : V) : ∃ s ∈ fr.span, ∃ t ∈ fr.perp, x = s + t := by
  have hx : x ∈ fr.span ⊔ fr.perp := by rw [fr.isCompl_span_perp.sup_eq_top]; trivial
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
  exact ⟨s, hs, t, ht, rfl⟩

theorem mem_span_of_neg (h2 : (2 : F) ≠ 0) {x : V} (hx : fr.La (-1) x = -x) : x ∈ fr.span := by
  obtain ⟨s, hs, t, ht, rfl⟩ := exists_decomp fr x
  rw [map_add, La_neg_one_of_mem_span fr hs, La_neg_one_of_mem_perp fr ht, neg_add] at hx
  have h1 : (2 : F) • t = 0 := by
    rw [two_smul]
    have h3 : t = -t := add_left_cancel hx
    nth_rewrite 2 [h3]
    exact add_neg_cancel t
  rw [smul_eq_zero.mp h1 |>.resolve_left h2, add_zero]
  exact hs

theorem mem_perp_of_fix (h2 : (2 : F) ≠ 0) {x : V} (hx : fr.La (-1) x = x) : x ∈ fr.perp := by
  obtain ⟨s, hs, t, ht, rfl⟩ := exists_decomp fr x
  rw [map_add, La_neg_one_of_mem_span fr hs, La_neg_one_of_mem_perp fr ht] at hx
  have h1 : (2 : F) • s = 0 := by
    rw [two_smul]
    have h3 : -s = s := add_right_cancel hx
    nth_rewrite 1 [← h3]
    exact neg_add_cancel s
  rw [smul_eq_zero.mp h1 |>.resolve_left h2, zero_add]
  exact ht

theorem map_mem_span (h2 : (2 : F) ≠ 0) {b : V ≃ₗ[F] V} (hb : fr.La (-1) * b = b * fr.La (-1))
    {x : V} (hx : x ∈ fr.span) : b x ∈ fr.span := by
  refine mem_span_of_neg fr h2 ?_
  have h := congrArg (fun g : V ≃ₗ[F] V => g x) hb
  simp only [LinearEquiv.mul_apply] at h
  rw [h, La_neg_one_of_mem_span fr hx, map_neg]

theorem map_mem_perp (h2 : (2 : F) ≠ 0) {b : V ≃ₗ[F] V} (hb : fr.La (-1) * b = b * fr.La (-1))
    {x : V} (hx : x ∈ fr.perp) : b x ∈ fr.perp := by
  refine mem_perp_of_fix fr h2 ?_
  have h := congrArg (fun g : V ≃ₗ[F] V => g x) hb
  simp only [LinearEquiv.mul_apply] at h
  rw [h, La_neg_one_of_mem_perp fr hx]

theorem span_ne_bot : fr.span ≠ ⊥ := by
  intro h
  have := finrank_span_eq_four fr
  rw [h, finrank_bot] at this
  omega

theorem three_le_finrank_perp [FiniteDimensional F V] (hV : 7 ≤ Module.finrank F V) :
    3 ≤ Module.finrank F fr.perp := by
  have := ModelFacts.finrank_perp_add_four fr
  omega

theorem perp_ne_bot [FiniteDimensional F V] (hV : 7 ≤ Module.finrank F V) : fr.perp ≠ ⊥ := by
  intro h
  have := three_le_finrank_perp fr hV
  rw [h, finrank_bot] at this
  omega

end Frame

theorem commute_of_scalars {S T : Submodule F V} (hdec : ∀ x : V, ∃ s ∈ S, ∃ t ∈ T, x = s + t)
    {g b : V ≃ₗ[F] V} {c₁ c₂ : F} (hgS : ∀ x ∈ S, g x = c₁ • x) (hgT : ∀ x ∈ T, g x = c₂ • x)
    (hbS : ∀ x ∈ S, b x ∈ S) (hbT : ∀ x ∈ T, b x ∈ T) : g * b = b * g := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨s, hs, t, ht, rfl⟩ := hdec x
  simp only [LinearEquiv.mul_apply, map_add, hgS s hs, hgT t ht, map_smul, hgS _ (hbS s hs),
    hgT _ (hbT t ht)]

theorem range_le_of_img_le₃ {X : Type} [Group X] (e : ↥(elementaryGroup Q) →* X)
    {J₁ J₂ J₃ : Subgroup (V ≃ₗ[F] V)} (h₁ : J₁ ≤ elementaryGroup Q) (h₂ : J₂ ≤ elementaryGroup Q)
    (h₃ : J₃ ≤ elementaryGroup Q) (hgen : elementaryGroup Q ≤ J₁ ⊔ J₂ ⊔ J₃) {P : Subgroup X}
    (hP₁ : img e J₁ ≤ P) (hP₂ : img e J₂ ≤ P) (hP₃ : img e J₃ ≤ P) : e.range ≤ P := by
  set K : Subgroup (V ≃ₗ[F] V) := (P.comap e).map (elementaryGroup Q).subtype with hK
  have hJ : ∀ J : Subgroup (V ≃ₗ[F] V), J ≤ elementaryGroup Q → img e J ≤ P → J ≤ K := by
    intro J hJE hJP y hy
    refine ⟨⟨y, hJE hy⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    exact hJP ((mem_img_iff e).mpr ⟨⟨y, hJE hy⟩, hy, rfl⟩)
  rintro _ ⟨g, rfl⟩
  have hgK : (g : V ≃ₗ[F] V) ∈ K :=
    (sup_le (sup_le (hJ J₁ h₁ hP₁) (hJ J₂ h₂ hP₂)) (hJ J₃ h₃ hP₃)) (hgen g.2)
  obtain ⟨g', hg', hg'g⟩ := hgK
  have : g' = g := Subtype.ext hg'g
  subst this
  exact hg'

section Generation

variable (fr₁ fr₂ fr₃ : Frame Q)

theorem elementaryGroup_le_frames (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hc : fr₁.La (-1) * fr₂.La (-1) = fr₂.La (-1) * fr₁.La (-1))
    (h3 : fr₁.La (-1) * fr₂.La (-1) = fr₃.La (-1)) (P : HypPair Q) (he₁ : P.e ∈ fr₁.span)
    (he₂ : P.e ∈ fr₂.span) (hf₁ : P.f ∈ fr₁.span) (hf₂ : P.f ∈ fr₂.span) {u : V}
    (hu₁ : u ∈ fr₁.span) (hu₂ : u ∈ fr₂.perp) (hu : Q u ≠ 0) :
    elementaryGroup Q ≤ elemOn Q fr₁.span ⊔ elemOn Q fr₂.span ⊔ elemOn Q fr₃.perp := by
  set H : Subgroup (V ≃ₗ[F] V) := elemOn Q fr₁.span ⊔ elemOn Q fr₂.span ⊔ elemOn Q fr₃.perp
    with hH
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    sup_le (sup_le (elemOn_le_elementaryGroup.trans (elementaryGroup_le_orthogonalGroup Q))
      (elemOn_le_elementaryGroup.trans (elementaryGroup_le_orthogonalGroup Q)))
      (elemOn_le_elementaryGroup.trans (elementaryGroup_le_orthogonalGroup Q))
  have hmem₁ : ∀ {x y : V}, x ∈ fr₁.span → y ∈ fr₁.span → eichler Q x y ∈ H := fun hx hy =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (eichler_mem_elemOn hx hy))
  have hmem₂ : ∀ {x y : V}, x ∈ fr₂.span → y ∈ fr₂.span → eichler Q x y ∈ H := fun hx hy =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (eichler_mem_elemOn hx hy))
  have hmem₃ : ∀ {x y : V}, x ∈ fr₃.perp → y ∈ fr₃.perp → eichler Q x y ∈ H := fun hx hy =>
    Subgroup.mem_sup_right (eichler_mem_elemOn hx hy)
  have he₃ : P.e ∈ fr₃.perp := by
    refine mem_perp_of_fix fr₃ h2 ?_
    rw [← h3, LinearEquiv.mul_apply, La_neg_one_of_mem_span fr₂ he₂, map_neg,
      La_neg_one_of_mem_span fr₁ he₁, neg_neg]
  have hU : ∀ w, polar Q P.e w = 0 → eichler Q P.e w ∈ H := by
    intro w hw
    obtain ⟨s, hs, t, ht, rfl⟩ := exists_decomp fr₁ w
    obtain ⟨t₂, ht₂, t₀, ht₀, rfl⟩ := exists_decomp fr₂ t
    have hb : fr₂.La (-1) t₂ = -t₂ := La_neg_one_of_mem_span fr₂ ht₂
    have hb' : fr₂.La (-1) t₀ = t₀ := La_neg_one_of_mem_perp fr₂ ht₀
    have hbt : fr₂.La (-1) (t₂ + t₀) ∈ fr₁.perp := map_mem_perp fr₁ h2 hc ht
    rw [map_add, hb, hb'] at hbt
    have ht₀₁ : t₀ ∈ fr₁.perp := by
      have h := fr₁.perp.add_mem ht hbt
      have e1 : t₂ + t₀ + (-t₂ + t₀) = (2 : F) • t₀ := by rw [two_smul]; abel
      rw [e1] at h
      have := fr₁.perp.smul_mem (2 : F)⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at this
    have ht₀₃ : t₀ ∈ fr₃.perp := by
      refine mem_perp_of_fix fr₃ h2 ?_
      rw [← h3, LinearEquiv.mul_apply, hb', La_neg_one_of_mem_perp fr₁ ht₀₁]
    have hp₀ : polar Q P.e t₀ = 0 := polar_perp_of_mem_span fr₂ he₂ ht₀
    have hpt : polar Q P.e (t₂ + t₀) = 0 := polar_perp_of_mem_span fr₁ he₁ ht
    have hp₂ : polar Q P.e t₂ = 0 := by
      rw [polar_add_right, hp₀, add_zero] at hpt
      exact hpt
    have hps : polar Q P.e s = 0 := by
      rw [polar_add_right, hpt, add_zero] at hw
      exact hw
    rw [← eichler_mul hps hpt, ← eichler_mul hp₂ hp₀]
    exact mul_mem (hmem₁ he₁ hs) (mul_mem (hmem₂ he₂ ht₂) (hmem₃ he₃ ht₀₃))
  have hup : u ∈ P.perp := HypPair.mem_perp.mpr
    ⟨polar_perp_of_mem_span fr₂ he₂ hu₂, polar_perp_of_mem_span fr₂ hf₂ hu₂⟩
  set s : F := (Q u)⁻¹ with hs_def
  have hs : Q u * s * 1 = 1 := by rw [hs_def, mul_inv_cancel₀ hu, mul_one]
  have hweyl : (eichler Q P.e (s • u) * eichler Q P.f ((1 : F) • u) * eichler Q P.e (s • u)) P.e =
      (-((1 : F) ^ 2 * Q u)) • P.f := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, eichler_e_apply_e, eichler_f_apply_e P hup,
      map_sub, map_add, map_smul, map_smul, eichler_e_apply_e, eichler_e_apply_a P hup,
      eichler_e_apply_f P hup]
    match_scalars
    · linear_combination (Q u * s * 1 - 1) * hs
    · linear_combination (-1) * hs
    · ring
  have hsu : s • u ∈ fr₁.span := fr₁.span.smul_mem s hu₁
  have hu1 : (1 : F) • u ∈ fr₁.span := fr₁.span.smul_mem 1 hu₁
  have hwmem : eichler Q P.e (s • u) * eichler Q P.f ((1 : F) • u) * eichler Q P.e (s • u) ∈ H :=
    mul_mem (mul_mem (hmem₁ he₁ hsu) (hmem₁ hf₁ hu1)) (hmem₁ he₁ hsu)
  refine elementaryGroup_le_of_subgroup' H hQ hHO hU ⟨_, hwmem, -((1 : F) ^ 2 * Q u), ?_, hweyl⟩
  rw [neg_ne_zero]
  exact mul_ne_zero (by norm_num) hu

end Generation

section Main

variable [Finite F] [FiniteDimensional F V] (fr₁ fr₂ fr₃ : Frame Q)

theorem alphaOf_frames_eq_bot (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hV : 7 ≤ Module.finrank F V)
    (hc : fr₁.La (-1) * fr₂.La (-1) = fr₂.La (-1) * fr₁.La (-1))
    (h3 : fr₁.La (-1) * fr₂.La (-1) = fr₃.La (-1)) (P : HypPair Q) (he₁ : P.e ∈ fr₁.span)
    (he₂ : P.e ∈ fr₂.span) (hf₁ : P.f ∈ fr₁.span) (hf₂ : P.f ∈ fr₂.span) {u : V}
    (hu₁ : u ∈ fr₁.span) (hu₂ : u ∈ fr₂.perp) (hu : Q u ≠ 0) {X : Type} [Group X] [Finite X]
    (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e) [e.range.Normal]
    (hcent : ∀ x : X, (∀ y ∈ e.range, x * y = y * x) → x = 1) :
    alphaOf (Subgroup.closure ({e ⟨fr₁.La (-1), fr₁.La_mem_elementaryGroup (-1)⟩,
      e ⟨fr₂.La (-1), fr₂.La_mem_elementaryGroup (-1)⟩} : Set X)) = ⊥ := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  set a₁ : ↥(elementaryGroup Q) := ⟨fr₁.La (-1), fr₁.La_mem_elementaryGroup (-1)⟩ with ha₁
  set a₂ : ↥(elementaryGroup Q) := ⟨fr₂.La (-1), fr₂.La_mem_elementaryGroup (-1)⟩ with ha₂
  have ha₁sq : a₁ * a₁ = 1 := Subtype.ext fr₁.La_neg_one_mul_self
  have ha₂sq : a₂ * a₂ = 1 := Subtype.ext fr₂.La_neg_one_mul_self
  have ha₁₂ : a₁ * a₂ = a₂ * a₁ := Subtype.ext hc
  have ha₃ : ((a₁ * a₂ : ↥(elementaryGroup Q)) : V ≃ₗ[F] V) = fr₃.La (-1) := h3
  have hx : e a₁ * e a₁ = 1 := by rw [← map_mul, ha₁sq, map_one]
  have hy : e a₂ * e a₂ = 1 := by rw [← map_mul, ha₂sq, map_one]
  have hxy : e a₁ * e a₂ = e a₂ * e a₁ := by rw [← map_mul, ← map_mul, ha₁₂]
  set B : Subgroup X := Subgroup.closure ({e a₁, e a₂} : Set X) with hB
  have hBmem := fun {b : X} (hb : b ∈ B) => mem_closure_pair_involutions hx hy hxy hb
  have hB2 : ∀ b ∈ B, b * b = 1 := by
    intro b hb
    rcases hBmem hb with rfl | rfl | rfl | rfl
    · simp
    · exact hx
    · exact hy
    · have : (e a₁ * e a₂) * (e a₁ * e a₂) = e a₁ * (e a₂ * e a₁) * e a₂ := by group
      rw [this, ← hxy]
      calc e a₁ * (e a₁ * e a₂) * e a₂ = (e a₁ * e a₁) * (e a₂ * e a₂) := by group
        _ = 1 := by rw [hx, hy, one_mul]
  have hBL : B ≤ e.range := by
    rw [hB, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨a₁, rfl⟩
    · exact ⟨a₂, rfl⟩
  have hme₁ : e a₁ ∈ B := Subgroup.subset_closure (Set.mem_insert _ _)
  have hme₂ : e a₂ ∈ B := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hme₃' : e (a₁ * a₂) = e a₁ * e a₂ := map_mul e a₁ a₂
  have hme₃ : e (a₁ * a₂) ∈ B := by rw [hme₃']; exact B.mul_mem hme₁ hme₂
  have hD₁ : LocalData e a₁ fr₁.span fr₁.perp :=
    ⟨splitInv fr₁ hQ, hker, span_ne_bot fr₁, perp_ne_bot fr₁ hV⟩
  have hD₂ : LocalData e a₂ fr₂.span fr₂.perp :=
    ⟨splitInv fr₂ hQ, hker, span_ne_bot fr₂, perp_ne_bot fr₂ hV⟩
  have hD₃ : LocalData e (a₁ * a₂) fr₃.span fr₃.perp :=
    ⟨by rw [ha₃]; exact splitInv fr₃ hQ, hker, span_ne_bot fr₃, perp_ne_bot fr₃ hV⟩
  have layS : ∀ fr : Frame Q, LayerGenOn Q fr.span := fun fr =>
    layerGenOn_of_regular hodd h5 (nd_span fr hQ)
  have layT : ∀ fr : Frame Q, LayerGenOn Q fr.perp := fun fr =>
    layerGenOn_of_regular hodd h5 (nd_perp fr hQ)
  have hdS : ∀ fr : Frame Q, 3 ≤ Module.finrank F fr.span := fun fr => by
    rw [finrank_span_eq_four]; omega
  set P₁ : Subgroup X := img e (elemOn Q fr₁.span ⊔ elemOn Q fr₁.perp) with hP₁
  set P₂ : Subgroup X := img e (elemOn Q fr₂.span ⊔ elemOn Q fr₂.perp) with hP₂
  set P₃ : Subgroup X := img e (elemOn Q fr₃.span ⊔ elemOn Q fr₃.perp) with hP₃
  have hfin : ∀ N : Subgroup X, (∀ n ∈ N, n * e a₁ = e a₁ * n ∧ n * e a₂ = e a₂ * n) →
      ⁅N, B⁆ = ⊥ := by
    intro N hN
    refine commutator_eq_bot_of_comm fun n hn b hb => ?_
    obtain ⟨c₁, c₂⟩ := hN n hn
    rcases hBmem hb with rfl | rfl | rfl | rfl
    · simp
    · exact c₁
    · exact c₂
    · rw [← mul_assoc, c₁, mul_assoc, c₂, ← mul_assoc]
  have hcomm_of : ∀ (g b : ↥(elementaryGroup Q)),
      (g : V ≃ₗ[F] V) * (b : V ≃ₗ[F] V) = (b : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) →
      e g * e b = e b * e g := fun g b h => by
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext h)
  have hc₁₃ : fr₃.La (-1) * fr₁.La (-1) = fr₁.La (-1) * fr₃.La (-1) := by
    rw [← h3, mul_assoc, ← hc]
  have hc₂₃ : fr₃.La (-1) * fr₂.La (-1) = fr₂.La (-1) * fr₃.La (-1) := by
    rw [← h3, mul_assoc, fr₂.La_neg_one_mul_self, mul_one, hc, ← mul_assoc,
      fr₂.La_neg_one_mul_self, one_mul]
  have hodd_comm : ∀ (a : ↥(elementaryGroup Q)) (fr : Frame Q), LocalData e a fr.span fr.perp →
      ∀ N : Subgroup X, N ≤ e.range ⊓ Subgroup.centralizer ({e a} : Set X) →
      (∀ x ∈ e.range ⊓ Subgroup.centralizer ({e a} : Set X), ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      Odd (Nat.card N) → ∀ (b : ↥(elementaryGroup Q)),
      fr.La (-1) * (b : V ≃ₗ[F] V) = (b : V ≃ₗ[F] V) * fr.La (-1) →
      ∀ n ∈ N, n * e b = e b * n := by
    intro a fr hD N hNle hNnorm hoddN b hb n hn
    obtain ⟨g, rfl⟩ := (hNle hn).1
    obtain ⟨c₁, hc₁⟩ := exists_smul_left_of_odd hodd hD (layS fr) (layT fr) hNle hNnorm hoddN hn
      (hdS fr)
    obtain ⟨c₂, hc₂⟩ := exists_smul_right_of_odd hodd hD (layS fr) (layT fr) hNle hNnorm hoddN hn
      (three_le_finrank_perp fr hV)
    exact hcomm_of g b (commute_of_scalars (exists_decomp fr) hc₁ hc₂
      (fun x hx => map_mem_span fr h2 hb hx) (fun x hx => map_mem_perp fr h2 hb hx))
  refine alphaOf_eq_bot_of_layers e.range hcent B hBL hB2 {P₁, P₂, P₃} ?_ ?_ ?_
  ·
    intro Pf hPf
    rcases hPf with rfl | hPf
    · exact ⟨e a₁, hme₁, hD₁.ne_one h2, le_inf (img_le_range e _) (img_join_le_centralizer hD₁),
        fun x hx p hp => conj_mem_img h2 hD₁ hx hp, img_join_perfect hD₁ (layS fr₁) (layT fr₁),
        fun N hNle hNnorm hodd' =>
          commutator_img_eq_bot h2 hD₁ (layS fr₁) (layT fr₁) hNle hNnorm hodd'⟩
    · rcases hPf with rfl | hPf
      · exact ⟨e a₂, hme₂, hD₂.ne_one h2,
          le_inf (img_le_range e _) (img_join_le_centralizer hD₂),
          fun x hx p hp => conj_mem_img h2 hD₂ hx hp, img_join_perfect hD₂ (layS fr₂) (layT fr₂),
          fun N hNle hNnorm hodd' =>
            commutator_img_eq_bot h2 hD₂ (layS fr₂) (layT fr₂) hNle hNnorm hodd'⟩
      · rw [Set.mem_singleton_iff] at hPf
        subst hPf
        exact ⟨e (a₁ * a₂), hme₃, hD₃.ne_one h2,
          le_inf (img_le_range e _) (img_join_le_centralizer hD₃),
          fun x hx p hp => conj_mem_img h2 hD₃ hx hp, img_join_perfect hD₃ (layS fr₃) (layT fr₃),
          fun N hNle hNnorm hodd' =>
            commutator_img_eq_bot h2 hD₃ (layS fr₃) (layT fr₃) hNle hNnorm hodd'⟩
  ·
    intro a ha ha1 N hNle hNnorm hodd'
    rcases hBmem ha with rfl | rfl | rfl | rfl
    · exact absurd rfl ha1
    · refine hfin N fun n hn =>
        ⟨((Subgroup.mem_centralizer_iff.mp (hNle hn).2) (e a₁) rfl).symm, ?_⟩
      exact hodd_comm a₁ fr₁ hD₁ N hNle hNnorm hodd' a₂ hc n hn
    · refine hfin N fun n hn =>
        ⟨?_, ((Subgroup.mem_centralizer_iff.mp (hNle hn).2) (e a₂) rfl).symm⟩
      exact hodd_comm a₂ fr₂ hD₂ N hNle hNnorm hodd' a₁ hc.symm n hn
    · rw [← hme₃'] at hNle hNnorm
      exact hfin N fun n hn =>
        ⟨hodd_comm (a₁ * a₂) fr₃ hD₃ N hNle hNnorm hodd' a₁ hc₁₃ n hn,
          hodd_comm (a₁ * a₂) fr₃ hD₃ N hNle hNnorm hodd' a₂ hc₂₃ n hn⟩
  ·
    set Pj : Subgroup X := ⨆ Pf ∈ ({P₁, P₂, P₃} : Set (Subgroup X)), Pf with hPj
    have hP₁le : P₁ ≤ Pj := le_iSup₂_of_le P₁ (by simp) le_rfl
    have hP₂le : P₂ ≤ Pj := le_iSup₂_of_le P₂ (by simp) le_rfl
    have hP₃le : P₃ ≤ Pj := le_iSup₂_of_le P₃ (by simp) le_rfl
    exact range_le_of_img_le₃ e elemOn_le_elementaryGroup elemOn_le_elementaryGroup
      elemOn_le_elementaryGroup
      (elementaryGroup_le_frames fr₁ fr₂ fr₃ h2 hQ hc h3 P he₁ he₂ hf₁ hf₂ hu₁ hu₂ hu)
      ((img_mono e (le_sup_left : elemOn Q fr₁.span ≤ _)).trans hP₁le)
      ((img_mono e (le_sup_left : elemOn Q fr₂.span ≤ _)).trans hP₂le)
      ((img_mono e (le_sup_right : elemOn Q fr₃.perp ≤ _)).trans hP₃le)

end Main

end CFSG.ClassicalInvolution.NDB.FourFrame

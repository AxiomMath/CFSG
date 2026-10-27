module

public import CFSG.LieType.Ree.LargeReeHeightQuotient
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesCoverTrivial
public import CFSG.LocalAnalysis.ComponentInitial.InvariantFormRetraction

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem f4_height_check : ∀ k < Tag.F4.rootCertificate.roots.length,
    height (Tag.F4.rootCertificate.root k) ≤ 11 := by
  decide +kernel

theorem height_le_eleven
    {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α) : height α ≤ 11 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check F4.tag)).1 hα
  exact f4_height_check k hk

variable {K : Type} [Field K]

theorem heightSeries_twelve :
    heightSeries F4.tag K 12 = ⊥ :=
  iSup₂_eq_bot.2 fun _ hα => absurd (height_le_eleven hα.1) (by linarith [hα.2.2])

open _root_.Classical in
@[expose] def heightProj
    (h : ℤ) (x : ModGL F4.tag K) : HeightQuot K h :=
  if hx : x ∈ heightSeries F4.tag K h then QuotientGroup.mk ⟨x, hx⟩ else 1

theorem heightProj_of_mem
    {h : ℤ} {x : ModGL F4.tag K} (hx : x ∈ heightSeries F4.tag K h) :
    heightProj h x = QuotientGroup.mk ⟨x, hx⟩ := by
  unfold heightProj
  exact dite_eq_left hx

theorem heightProj_mul
    {h : ℤ} {x y : ModGL F4.tag K} (hx : x ∈ heightSeries F4.tag K h)
    (hy : y ∈ heightSeries F4.tag K h) :
    heightProj h (x * y) = heightProj h x * heightProj h y := by
  rw [heightProj_of_mem hx, heightProj_of_mem hy, heightProj_of_mem (mul_mem hx hy),
    ← QuotientGroup.mk_mul]
  rfl

theorem heightProj_conj
    (a : ℕ) (t : Kˣ × Kˣ) {h : ℤ} {x : ModGL F4.tag K}
    (hx : x ∈ heightSeries F4.tag K h) :
    heightProj h (torusPair a t * x * (torusPair a t)⁻¹) =
      heightQuotSmul a h t (heightProj h x) := by
  rw [heightProj_of_mem hx, heightProj_of_mem (torusPair_conj_mem_heightSeries a t hx),
    heightQuotSmul_mk]
  exact congrArg QuotientGroup.mk (Subtype.ext (coe_heightConj a h t ⟨x, hx⟩).symm)

theorem mem_heightSeries_succ_of_heightProj
    {h : ℤ} {x : ModGL F4.tag K}
    (hx : x ∈ heightSeries F4.tag K h) (h1 : heightProj h x = 1) :
    x ∈ heightSeries F4.tag K (h + 1) := by
  rw [heightProj_of_mem hx, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

variable [Finite K] [CharP K F4.prime] (a : ℕ)

@[expose] def series
    (i : ℕ) : Subgroup (ModGL F4.tag K) :=
  F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K (12 - (i : ℤ))

theorem series_succ
    (i : ℕ) :
    series (K := K) a (i + 1) = F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K (11 - i) := by
  rw [series]
  congr 2
  push_cast
  ring

theorem series_eq
    (i : ℕ) :
    series (K := K) a i = F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K ((11 - i) + 1) := by
  rw [series]
  congr 2
  ring

theorem reeFixedPosUnipotent_le_heightSeries_one :
    F4.reeFixedPosUnipotent K a ≤ heightSeries F4.tag K 1 := by
  rw [heightSeries_one]
  exact inf_le_left

theorem torusPair_conj_mem_reeFixedPosUnipotent
    (hK : Nat.card K = F4.prime ^ (2 * a + 1))
    (t : Kˣ × Kˣ) {x : ModGL F4.tag K} (hx : x ∈ F4.reeFixedPosUnipotent K a) :
    torusPair a t * x * (torusPair a t)⁻¹ ∈ F4.reeFixedPosUnipotent K a := by
  obtain ⟨hxU, hxΓ⟩ := Subgroup.mem_inf.1 hx
  have hτ := torusPair_mem_reeGamma a hK t
  exact Subgroup.mem_inf.2 ⟨torusPair_conj_mem_rootSpan a t (fun _ hα => hα.1) hxU,
    mul_mem (mul_mem hτ hxΓ) (inv_mem hτ)⟩

section Factors

variable {a}

theorem commutator_mem_inf_succ
    {h : ℤ} {x g : ModGL F4.tag K}
    (hx : x ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h)
    (hg : g ∈ F4.reeFixedPosUnipotent K a) :
    x⁻¹ * g⁻¹ * x * g ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K (h + 1) := by
  obtain ⟨hxU, hxV⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (mul_mem (inv_mem hxU) (inv_mem hg)) hxU) hg, ?_⟩
  have hgV := reeFixedPosUnipotent_le_heightSeries_one a hg
  have hc := commutator_heightSeries_le K h 1
    (Subgroup.commutator_mem_commutator (inv_mem hxV) (inv_mem hgV))
  rwa [commutatorElement_def, inv_inv, inv_inv] at hc

theorem sq_mem_inf_succ
    {h : ℤ} {x : ModGL F4.tag K}
    (hx : x ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h) :
    x ^ 2 ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K (h + 1) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨hxU, hxV⟩ := Subgroup.mem_inf.1 hx
  exact Subgroup.mem_inf.2 ⟨pow_mem hxU 2, sq_mem_heightSeries_succ hxV⟩

theorem mem_inf_succ_of_forall
    (ha : 2 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {h : ℤ}
    {x : ModGL F4.tag K} (hx : x ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h)
    (hfix : ∀ t : Kˣ × Kˣ, (torusPair a t * x * (torusPair a t)⁻¹)⁻¹ * x ∈
      F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K (h + 1)) :
    x ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K (h + 1) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨hxU, hxV⟩ := Subgroup.mem_inf.1 hx
  exact Subgroup.mem_inf.2 ⟨hxU, mem_heightSeries_succ_of_forall a ha hK hxV
    fun t => (Subgroup.mem_inf.1 (hfix t)).2⟩

theorem form_eq_zero_of_inf
    (ha : 2 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (h h' : ℤ)
    (b : ModGL F4.tag K → ModGL F4.tag K → ZMod 2)
    (hb₁ : ∀ x ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h,
      ∀ x' ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h,
      ∀ y ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h', b (x * x') y = b x y + b x' y)
    (hb₂ : ∀ x ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h,
      ∀ y ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h',
      ∀ y' ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h', b x (y * y') = b x y + b x y')
    (hb₃ : ∀ x ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K (h + 1),
      ∀ y ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h', b x y = 0)
    (hb₄ : ∀ x ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h,
      ∀ y ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K (h' + 1), b x y = 0)
    (hb₅ : ∀ (t : Kˣ × Kˣ), ∀ x ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h,
      ∀ y ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h',
      b (torusPair a t * x * (torusPair a t)⁻¹) (torusPair a t * y * (torusPair a t)⁻¹) = b x y) :
    ∀ x ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h,
      ∀ y ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K h', b x y = 0 := by
  classical
  have : CharP K 2 := ‹CharP K F4.prime›
  have hK' : Nat.card K = F4.prime ^ (2 * a + 1) := hK
  have := Fintype.ofFinite (Kˣ × Kˣ)
  have hT : Odd (Fintype.card (Kˣ × Kˣ)) := by
    rw [← Nat.card_eq_fintype_card]
    exact odd_card_torus a hK
  let _ := heightQuotAction (K := K) a h
  let _ := heightQuotAction (K := K) a h'
  have hW : ∀ (t : Kˣ × Kˣ) {k : ℤ} {x : ModGL F4.tag K},
      x ∈ F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K k →
        torusPair a t * x * (torusPair a t)⁻¹ ∈
          F4.reeFixedPosUnipotent K a ⊓ heightSeries F4.tag K k := fun t _ _ hx =>
    Subgroup.mem_inf.2 ⟨torusPair_conj_mem_reeFixedPosUnipotent a hK' t (Subgroup.mem_inf.1 hx).1,
      torusPair_conj_mem_heightSeries a t (Subgroup.mem_inf.1 hx).2⟩
  exact form_eq_zero_of_image (T := Kˣ × Kˣ) (Q := HeightQuot K h) (Q' := HeightQuot K h')
    (M := ModGL F4.tag K) hT heightQuot_sq_eq_one heightQuot_sq_eq_one
    (fun B h₁ h₂ h₃ => heightQuot_form_eq_zero a ha hK B h₁ h₂ h₃)
    (fun t x => torusPair a t * x * (torusPair a t)⁻¹) _ _
    (fun t _ hx => hW t hx) (fun t _ hy => hW t hy) (heightProj h) (heightProj h')
    (fun _ hx _ hx' => heightProj_mul (Subgroup.mem_inf.1 hx).2 (Subgroup.mem_inf.1 hx').2)
    (fun _ hy _ hy' => heightProj_mul (Subgroup.mem_inf.1 hy).2 (Subgroup.mem_inf.1 hy').2)
    (fun t _ hx => heightProj_conj a t (Subgroup.mem_inf.1 hx).2)
    (fun t _ hy => heightProj_conj a t (Subgroup.mem_inf.1 hy).2)
    b hb₁ hb₂
    (fun x hx y hy h1 => hb₃ x (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1,
      mem_heightSeries_succ_of_heightProj (Subgroup.mem_inf.1 hx).2 h1⟩) y hy)
    (fun x hx y hy h1 => hb₄ x hx y (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hy).1,
      mem_heightSeries_succ_of_heightProj (Subgroup.mem_inf.1 hy).2 h1⟩))
    hb₅

end Factors

theorem ker_eq_bot_of_reeGamma
    (ha : 2 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {E : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] (η : E →* F4.reeGamma K a)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker) :
    η.ker = ⊥ := by
  have hK' : Nat.card K = F4.prime ^ (2 * a + 1) := hK
  have := finite_modGL (τ := F4.tag) (K := K)
  have : Fact F4.prime.Prime := ⟨Nat.prime_two⟩
  refine ker_eq_bot_of_coprime_central_series η hη hC h2 (U := F4.reeFixedPosUnipotent K a)
    reeFixedPosUnipotent_le_reeGamma isPGroup_reeFixedPosUnipotent_subgroupOf
    not_dvd_index_reeFixedPosUnipotent (odd_card_torus a hK) (torusPair a)
    (torusPair_mem_reeGamma a hK')
    (fun t x hx => torusPair_conj_mem_reeFixedPosUnipotent a hK' t hx)
    11 (series a) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    rw [series, Nat.cast_zero, sub_zero, heightSeries_twelve, inf_bot_eq]
  ·
    rw [series, show (12 : ℤ) - (11 : ℕ) = 1 by norm_num]
    exact inf_eq_left.2 (reeFixedPosUnipotent_le_heightSeries_one a)
  ·
    intro i _
    rw [series_succ, series_eq]
    exact inf_le_inf_left _ (heightSeries_antitone (by omega))
  ·
    intro i _ t x hx
    rw [series] at hx ⊢
    obtain ⟨hxU, hxV⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨torusPair_conj_mem_reeFixedPosUnipotent a hK' t hxU,
      torusPair_conj_mem_heightSeries a t hxV⟩
  ·
    intro i _ x hx g hg
    rw [series_succ] at hx
    rw [series_eq]
    exact commutator_mem_inf_succ hx hg
  ·
    intro i _ x hx
    rw [series_succ] at hx
    rw [series_eq]
    exact sq_mem_inf_succ hx
  ·
    intro i _ x hx hfix
    rw [series_succ] at hx
    rw [series_eq] at hfix ⊢
    exact mem_inf_succ_of_forall ha hK hx hfix
  ·
    intro i _ j _ b
    rw [series_succ, series_succ, series_eq a i, series_eq a j]
    exact form_eq_zero_of_inf ha hK _ _ b

end CFSG.LieType.Ree.LargeReeCover

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley ReeTag LargeReeCover

theorem large_Ree_large_even_field_central_two_cover_trivial
    {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {f : ℕ} (hf : 5 ≤ f) (hJ : CFSG.Blueprint.LieModel J .twistedF4 0 2 f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  rcases hJ with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hR⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  swap
  · exact absurd ht (by decide)
  obtain ⟨-, a, hfa, K, _, _, hK, ⟨e₀⟩⟩ := id hR
  have ha : 2 ≤ a := by omega
  have hK2 : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have : CharP K F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK2
  obtain ⟨e⟩ := (large_Ree_model_Schreier J 2 f hR).2.2.2.2.2 a K hfa hK ⟨e₀⟩
  set η' : E →* F4.reeGamma K a := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_reeGamma a ha hK2 η' (e.surjective.comp hη) (hker' ▸ hC)
    (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LieType.Ree

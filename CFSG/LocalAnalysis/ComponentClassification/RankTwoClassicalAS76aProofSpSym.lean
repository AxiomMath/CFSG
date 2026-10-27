module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpFour
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviInner
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviSym
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpAut

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (spInner spInner_eq_conj
  exceptionalAut)
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)
open scoped MatrixGroups commutatorElement

section Proj

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem exists_eq_spInner_mul_fieldAut_of_four (hK : Nat.card K = 4)
    {α : MulAut (StatedProj (StatedSp (1 + 1) K))} (h2 : α * α = 1) :
    ∃ (g : StatedSp (1 + 1) K) (φ : K ≃+* K), α = spInner 2 K g * fieldAut 2 K φ := by
  by_cases h1 : α = 1
  · exact ⟨1, 1, by rw [h1, map_one, map_one, mul_one]⟩
  have hord : orderOf α = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact h2) h1
  obtain ⟨Fr, hFr, hFrord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (show 1 ≤ 2 by norm_num) (show Nat.card K = 2 ^ 2 by rw [hK]; norm_num)
  obtain ⟨-, -, -, -, -, -, -, -, -, hinv⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure
      (show 1 ≤ 2 by norm_num) hFr hFrord hzp
  obtain ⟨g, j, hj, hαeq⟩ := hinv α hord
  rcases hj with rfl | rfl
  · exact ⟨g, 1, by rw [hαeq, pow_zero, map_one]⟩
  · exact ⟨g, Fr, by
      rw [hαeq, CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_sq hFr]⟩

theorem exists_inner_of_fixes_sp_four (hK : Nat.card K = 4)
    {α : MulAut (StatedProj (StatedSp (1 + 1) K))} (h2 : α * α = 1)
    (hW : ∀ w ∈ spBarW K 1, α w = w) :
    ∃ l ∈ spBarL K 1, ∀ x ∈ spBarL K 1, α x = l * x * l⁻¹ := by
  obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut_of_four hK h2
  obtain ⟨hφ, hg⟩ := fix_spBarW (m := 1) g φ hW
  rw [fieldAut_sp_eq_one hφ, mul_one]
  obtain ⟨t, rfl⟩ := hg
  exact ⟨proj (1 + 1) K (spL K 1 t), ⟨t, rfl⟩, fun x _ => by
    rw [spInner_eq_conj, MulAut.conj_apply]⟩

theorem last_one : (Fin.last 1 : Fin (1 + 1)) = 1 := rfl

omit [CharP K 2] [Finite K] in
theorem exists_longBlock_of_mem_range_spL {g : StatedSp (1 + 1) K} (hg : g ∈ (spL K 1).range) :
    ∃ a : SL(2, K), g = longBlock K (1 + 1) 0 a := by
  rw [range_spL, last_one, coords_one_compl, ← range_longBlock] at hg
  obtain ⟨a, rfl⟩ := hg
  exact ⟨a, rfl⟩

omit [Finite K] in
theorem eq_one_of_spInner_eq_one {g : StatedSp (1 + 1) K} (h : spInner 2 K g = 1) : g = 1 := by
  have hc : g ∈ center (StatedSp (1 + 1) K) := by
    rw [mem_center_iff]
    intro y
    have h1 := congrArg (fun α : MulAut (StatedProj (StatedSp (1 + 1) K)) => α (proj (1 + 1) K y)) h
    simp only [spInner_eq_conj, MulAut.one_apply] at h1
    rw [conj_proj_sp] at h1
    have h2 := proj_sp_injective h1
    calc y * g = g * y * g⁻¹ * g := by rw [h2]
      _ = g * y := by group
  rwa [center_statedSp_eq_bot (by norm_num), mem_bot] at hc

theorem eq_one_of_fixes_sp_five (hK : Nat.card K = 4)
    {α : MulAut (StatedProj (StatedSp (1 + 1) K))} (h2 : α * α = 1)
    (hW : ∀ w ∈ spBarW K 1, α w = w) {ω : K} (hω0 : ω ≠ 0)
    (hx : α (proj (1 + 1) K (longBlock K (1 + 1) 0 (fiveSL ω))) =
      proj (1 + 1) K (longBlock K (1 + 1) 0 (fiveSL ω))) : α = 1 := by
  obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut_of_four hK h2
  obtain ⟨hφ, hg⟩ := fix_spBarW (m := 1) g φ hW
  rw [fieldAut_sp_eq_one hφ, mul_one] at h2 hx ⊢
  obtain ⟨a, rfl⟩ := exists_longBlock_of_mem_range_spL hg
  rw [spInner_eq_conj, conj_proj_sp] at hx
  have h3 := proj_sp_injective hx
  rw [← map_inv, ← map_mul, ← map_mul] at h3
  have h4 := longBlock_injective _ h3
  have hcomm : (a : Matrix (Fin 2) (Fin 2) K) * fiveM ω = fiveM ω * a := by
    have h5 : a * fiveSL ω = fiveSL ω * a := by
      calc a * fiveSL ω = a * fiveSL ω * a⁻¹ * a := by group
        _ = fiveSL ω * a := by rw [h4]
    exact congrArg Subtype.val h5
  rw [← map_mul] at h2
  have h6 := eq_one_of_spInner_eq_one h2
  rw [← map_mul] at h6
  have h7 : a * a = 1 := longBlock_injective _ (h6.trans (map_one _).symm)
  have hsq : (a : Matrix (Fin 2) (Fin 2) K) * a = (1 : K) • 1 := by
    rw [one_smul, ← Matrix.SpecialLinearGroup.coe_mul, h7, Matrix.SpecialLinearGroup.coe_one]
  have ha := eq_smul_one_of_mul_fiveM hω0 hcomm hsq
  have h00 : (a : Matrix (Fin 2) (Fin 2) K) 0 0 * (a : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have := congrFun (congrFun hsq 0) 0
    rw [ha] at this
    simpa [Matrix.smul_mul] using this
  have ha1 : a = 1 := by
    apply Subtype.ext
    rw [ha, eq_one_of_mul_self_eq_one h00, one_smul, Matrix.SpecialLinearGroup.coe_one]
  rw [ha1, map_one, map_one]

omit [CharP K 2] [Finite K] in
theorem spBarW_one_eq :
    spBarW K 1 = (suppGroup (coords (1 : Fin (1 + 1)))).map (proj (1 + 1) K) := by
  rw [spBarW, MonoidHom.range_comp, range_spW, last_one]

omit [CharP K 2] [Finite K] in
theorem spBarL_one_eq :
    spBarL K 1 = (suppGroup (coords (0 : Fin (1 + 1)))).map (proj (1 + 1) K) := by
  rw [spBarL, MonoidHom.range_comp, range_spL, last_one, coords_one_compl]

omit [CharP K 2] [Finite K] in
theorem map_conj_suppGroup_coords {s : StatedSp (1 + 1) K}
    (hs : ∀ t, mat _ K s *ᵥ Pi.single t 1 = Pi.single (swapCoord t) 1) (k : Fin (1 + 1)) :
    ((suppGroup (coords k)).map (proj (1 + 1) K)).map (MulAut.conj (proj (1 + 1) K s)).toMonoidHom =
      (suppGroup (coords (Equiv.swap 0 1 k))).map (proj (1 + 1) K) := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj (proj (1 + 1) K s)).toMonoidHom.comp (proj (1 + 1) K) =
      (proj (1 + 1) K).comp (MulAut.conj s).toMonoidHom := by
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  rw [hcomp, ← Subgroup.map_map]
  congr 1
  ext y
  rw [mem_map_equiv, MulAut.conj_symm_apply, ← conj_mem_suppGroup_coords_iff hs k (s⁻¹ * y * s),
    show s * (s⁻¹ * y * s) * s⁻¹ = y by group]

@[expose] noncomputable def spPair : SL(2, K) × SL(2, K) →* StatedSp (1 + 1) K :=
  (longBlock K (1 + 1) 0).noncommCoprod (longBlock K (1 + 1) 1) fun a b =>
    commute_longRootSp2 (by decide) ⟨a, rfl⟩ ⟨b, rfl⟩

omit [CharP K 2] [Finite K] in
theorem spPair_apply (a b : SL(2, K)) :
    spPair (a, b) = longBlock K (1 + 1) 0 a * longBlock K (1 + 1) 1 b :=
  MonoidHom.noncommCoprod_apply _ _ _ _

omit [CharP K 2] [Finite K] in
theorem spPair_one_left (b : SL(2, K)) : spPair (1, b) = longBlock K (1 + 1) 1 b := by
  rw [spPair_apply, map_one, one_mul]

end Proj

section Lift

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSp (1 + 1) K)}

theorem outerFree_sp_four (hK : Nat.card K = 4) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (h4 : ∃ s : Finset K, s.card = 4) (σ : MulAut ↥A)
    (hσ : σ * σ = 1) (hfix : ∀ y : ↥A, (y : G) ∈ spLeviW θ → σ y = y) :
    ∃ l ∈ spLeviL θ, ∀ z : ↥A, (z : G) ∈ spLeviL θ → ((σ z : ↥A) : G) = l * z * l⁻¹ := by
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  obtain ⟨lb, hlb, hinner⟩ := exists_inner_of_fixes_sp_four hK (inducedAut_sq hθ hσ hα)
    (inducedAut_fix_of_levLift hθ (commutator_spBarW h4) le_rfl hfix hα)
  exact exists_inner_levLift_of hker hθ (commutator_spBarL h4) σ hα hlb hinner

omit [Finite K] in
theorem det_fiveSL_sub_one_ne_zero {ω : K} (hω0 : ω ≠ 0) :
    ((fiveSL ω : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0 := by
  have h : ((fiveSL ω : Matrix (Fin 2) (Fin 2) K) - 1).det = -ω := by
    rw [Matrix.det_fin_two]
    simp [fiveSL, fiveM]
  rw [h]
  exact neg_ne_zero.mpr hω0

omit [Finite K] in
theorem exists_spPair_of_mem_centralizer {ω : K} (hω0 : ω ≠ 0)
    {x : G} (hxA : x ∈ A)
    (hxθ : θ ⟨x, hxA⟩ = proj (1 + 1) K (longBlock K (1 + 1) 0 (fiveSL ω))) {m : G}
    (hm : m ∈ centralizer ((⊥ ⊔ zpowers x : Subgroup G) : Set G)) (hmA : m ∈ A) :
    ∃ a b : SL(2, K), θ ⟨m, hmA⟩ = proj (1 + 1) K (spPair (a, b)) ∧
      a * fiveSL ω = fiveSL ω * a := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective _ (θ ⟨m, hmA⟩)
  have h1 := mem_centralizer_iff.mp hm x (mem_sup_right (mem_zpowers x))
  have h2 : θ ⟨m, hmA⟩ * θ ⟨x, hxA⟩ = θ ⟨x, hxA⟩ * θ ⟨m, hmA⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext h1.symm)
  rw [hxθ, ← hg] at h2
  change proj (1 + 1) K g * _ = _ * proj (1 + 1) K g at h2
  rw [← map_mul, ← map_mul] at h2
  obtain ⟨a, b, hab, hX⟩ := exists_longBlock_mul_longBlock (det_fiveSL_sub_one_ne_zero hω0)
    (proj_sp_injective h2)
  refine ⟨a, b, ?_, hX⟩
  rw [← hg, hab, spPair_apply]
  rfl

omit [Finite K] [CharP K 2] in
theorem spPair_conj_longBlock_one (a b Y : SL(2, K)) :
    spPair (a, b) * longBlock K (1 + 1) 1 Y * (spPair (a, b))⁻¹ =
      longBlock K (1 + 1) 1 (b * Y * b⁻¹) := by
  rw [← spPair_one_left, ← spPair_one_left, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp

omit [Finite K] [CharP K 2] in
theorem proj_spPair_mem_normalizer (a b : SL(2, K)) :
    proj (1 + 1) K (spPair (a, b)) ∈ normalizer (spBarW K 1 : Set _) := by
  have key : ∀ a b : SL(2, K), ∀ w ∈ spBarW K 1,
      proj (1 + 1) K (spPair (a, b)) * w * (proj (1 + 1) K (spPair (a, b)))⁻¹ ∈ spBarW K 1 := by
    rintro a b _ ⟨Y, rfl⟩
    refine ⟨b * Y * b⁻¹, ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, spW, last_one, spPair_conj_longBlock_one]
  refine mem_normalizer_iff.mpr fun w => ⟨key a b w, fun hw => ?_⟩
  have h := key a⁻¹ b⁻¹ _ hw
  have hinv : spPair (a⁻¹, b⁻¹) = (spPair (a, b))⁻¹ := by
    rw [← map_inv]
    rfl
  rwa [hinv, map_inv, inv_inv, show (proj (1 + 1) K (spPair (a, b)))⁻¹ *
    (proj (1 + 1) K (spPair (a, b)) * w * (proj (1 + 1) K (spPair (a, b)))⁻¹) *
      proj (1 + 1) K (spPair (a, b)) = w by group] at h

omit [Finite K] [CharP K 2] in
theorem commutatorElement_proj_spPair_mem {a b a' b' : SL(2, K)} (h : a * a' = a' * a) :
    ⁅proj (1 + 1) K (spPair (a, b)), proj (1 + 1) K (spPair (a', b'))⁆ ∈ spBarW K 1 := by
  rw [← map_commutatorElement, ← map_commutatorElement]
  have hc : ⁅((a, b) : SL(2, K) × SL(2, K)), (a', b')⁆ = (1, ⁅b, b'⁆) := by
    refine Prod.ext ?_ rfl
    change ⁅a, a'⁆ = 1
    rw [commutatorElement_def, h, mul_inv_cancel_right, mul_inv_cancel]
  rw [hc, spPair_one_left]
  exact ⟨⁅b, b'⁆, by simp only [MonoidHom.comp_apply]; rw [spW, last_one]⟩

theorem sym_sp_four [Finite G] (hA : commutator ↥A = ⊤) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hZ : Odd (Nat.card (center ↥A))) (hK : Nat.card K = 4)
    (h4 : ∃ s : Finset K, s.card = 4) :
    ∃ (D' : Subgroup G) (s x : G), spLeviW θ = D' ⊔ spLeviW θ ∧ s ∈ A ∧
      rightConjugate (spLeviW θ) s = spLeviL θ ∧ rightConjugate (spLeviL θ) s = spLeviW θ ∧
      rightConjugate D' s = D' ∧ x ∈ spLeviL θ ∧ orderOf x = 5 ∧
      AS76b.layerCentralizer A (D' ⊔ zpowers x) = spLeviW θ ∧
      NoInvolutoryCentralizing A (D' ⊔ zpowers x ⊔ spLeviW θ) := by
  obtain ⟨ω, hω0, -, hω⟩ := exists_cube_root_of_card_four hK
  obtain ⟨s₀, hs₀, hss⟩ := exists_spSwap (K := K)
  obtain ⟨sA, hsA⟩ := hθ (proj (1 + 1) K s₀)
  have hsinv : s₀⁻¹ = s₀ := inv_eq_of_mul_eq_one_right hss
  have hsθ : (θ ⟨(sA : G), sA.2⟩)⁻¹ = proj (1 + 1) K s₀ := by
    rw [show (⟨(sA : G), sA.2⟩ : ↥A) = sA from rfl, hsA, ← map_inv, hsinv]
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hX : proj (1 + 1) K (longBlock K (1 + 1) 0 (fiveSL ω)) ∈ spBarL K 1 := by
    obtain ⟨S, hS⟩ := longBlock_zero_mem_range_spL le_rfl (fiveSL ω)
    exact ⟨S, by simp only [MonoidHom.comp_apply]; rw [hS]; rfl⟩
  have hX5 : proj (1 + 1) K (longBlock K (1 + 1) 0 (fiveSL ω)) ^ 5 = 1 := by
    rw [← map_pow, ← map_pow, fiveSL_pow_five hω, map_one, map_one]
  have hX1 : proj (1 + 1) K (longBlock K (1 + 1) 0 (fiveSL ω)) ≠ 1 := by
    intro h
    have h1 := proj_sp_injective (h.trans (map_one _).symm)
    exact fiveSL_ne_one ω (longBlock_injective _ (h1.trans (map_one _).symm))
  obtain ⟨x, hxL, hxA, hxθ, hx5⟩ := exists_mem_levLift_orderOf hker hθ hZ (f := 2) le_rfl
    (by rw [hK]; norm_num) (commutator_spBarL h4) ((longBlockEquivOne K).trans (spBarLEquiv K 1))
    hX hX5 hX1
  refine ⟨⊥, sA, x, (bot_sup_eq _).symm, sA.2, ?_, ?_, Subgroup.map_bot _, hxL, hx5, ?_, ?_⟩
  · rw [spLeviW, rightConjugate_levLift sA.2, hsθ, spBarW_one_eq, map_conj_suppGroup_coords hs₀,
      Equiv.swap_apply_right, spLeviL, spBarL_one_eq]
  · rw [spLeviL, rightConjugate_levLift sA.2, hsθ, spBarL_one_eq, map_conj_suppGroup_coords hs₀,
      Equiv.swap_apply_left, spLeviW, spBarW_one_eq]
  · refine layerCentralizer_eq_levLift hker hθ (commutator_spBarW h4) (isQuasisimple_spBarW h4)
      ?_ ?_ ?_
    · refine le_inf levLift_le ?_
      rw [le_centralizer_iff]
      refine sup_le bot_le ?_
      rw [zpowers_le]
      exact le_centralizer_iff.mp (levLift_le_centralizer_levLift hker
        (fun _ hs _ hs' => spBarW_commute_spBarL hs hs')) hxL
    · intro m hmM hm
      obtain ⟨a, b, hab, -⟩ := exists_spPair_of_mem_centralizer hω0 hxA hxθ (mem_inf.mp hmM).2 hm
      rw [hab]
      exact proj_spPair_mem_normalizer a b
    · intro a ha b hb haA hbA
      obtain ⟨a₀, a₁, ha', hac⟩ :=
        exists_spPair_of_mem_centralizer hω0 hxA hxθ (mem_inf.mp ha).2 haA
      obtain ⟨b₀, b₁, hb', hbc⟩ :=
        exists_spPair_of_mem_centralizer hω0 hxA hxθ (mem_inf.mp hb).2 hbA
      rw [ha', hb']
      refine commutatorElement_proj_spPair_mem (Subtype.ext ?_)
      exact commute_of_mul_fiveM (congrArg Subtype.val hac) (congrArg Subtype.val hbc)
  · intro σ hσ hfix
    obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
    have hW := inducedAut_fix_of_levLift hθ (commutator_spBarW h4) le_sup_right hfix hα
    have hx : α (proj (1 + 1) K (longBlock K (1 + 1) 0 (fiveSL ω))) =
        proj (1 + 1) K (longBlock K (1 + 1) 0 (fiveSL ω)) := by
      rw [← hxθ, hα, hfix ⟨x, hxA⟩ (mem_sup_left (mem_sup_right (mem_zpowers x)))]
    have h1 := eq_one_of_fixes_sp_five hK (inducedAut_sq hθ hσ hα) hW hω0 hx
    exact eq_one_of_theta_eq hker hA σ fun a => by rw [← hα, h1, MulAut.one_apply]

end Lift

end CFSG.ComponentClassification.RankTwoClassical

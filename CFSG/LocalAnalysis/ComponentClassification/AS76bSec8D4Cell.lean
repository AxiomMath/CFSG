module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Unip
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenWeyl
public import CFSG.LieType.Ree.LargeReeA1Pair
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.GraphFixedRootBruhat
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement Matrix

section Weyl

open CFSG.ComponentClassification.UnbalancedCatalog

@[expose] def d4Sum4 : Fin TwistTag.D4.tag.rank → ℤ :=
  trialityRoot 3 + permLattice TwistTag.D4.perm (trialityRoot 3) +
    permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 3)

@[expose] def d4ThetaBar : Fin TwistTag.D4.foldedTag.rank → ℤ := ![1, 2]

@[expose] def d4SumBar : Fin TwistTag.D4.foldedTag.rank → ℤ := ![2, 3]

theorem foldMap_thetaBar : TwistTag.D4.foldMap d4ThetaBar = trialityRoot 5 := by
  decide +kernel

theorem foldMap_sumBar : TwistTag.D4.foldMap d4SumBar = d4Sum4 := by
  decide +kernel

theorem weylG2_stab_g2v
    (w : WeylGroup .G2) (h : w • g2v = g2v) :
    w = 1 ∨ w = simple .G2 g2ia := by
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩
  · exact Or.inl (eq_one_of_smul ha hr)
  · exact Or.inr (eq_simple_a_of_smul ha hr)
  all_goals rw [smul_g2v, ha, hr] at h; exact absurd h (by decide +kernel)

theorem weylG2_stab_g2c
    (w : WeylGroup .G2) (h : w • g2c = g2c) :
    w = 1 ∨ w = simple .G2 g2ir := by
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩
  · exact Or.inl (eq_one_of_smul ha hr)
  · rw [smul_g2c, ha, hr] at h; exact absurd h (by decide +kernel)
  · exact Or.inr (eq_simple_r_of_smul ha hr)
  all_goals rw [smul_g2c, ha, hr] at h; exact absurd h (by decide +kernel)

theorem relWeyl_stab_theta
    {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) (h : w • trialityRoot 5 = trialityRoot 5) :
    w = 1 ∨ w = TwistTag.D4.orbitReflection ⟨0, by decide⟩ := by
  set w' : relWeylTwist TwistTag.D4 := ⟨w, hw⟩
  have h1 : TwistTag.D4.foldMap (foldedWeylEquiv TwistTag.D4 w' • d4ThetaBar) =
      TwistTag.D4.foldMap d4ThetaBar := by
    rw [← smul_foldMap_foldedWeylEquiv, foldMap_thetaBar]
    exact h
  rcases weylG2_stab_g2v _ (TwistTag.D4.foldMap_injective h1) with h3 | h3
  · left
    have : w' = 1 := (foldedWeylEquiv TwistTag.D4).injective (by rw [h3, map_one]; rfl)
    exact congrArg Subtype.val this
  · right
    have : w' = ⟨_, TwistTag.D4.orbitReflection_mem ⟨0, by decide⟩⟩ :=
      (foldedWeylEquiv TwistTag.D4).injective (by rw [h3, foldedWeylEquiv_orbitReflection]; rfl)
    exact congrArg Subtype.val this

theorem relWeyl_stab_sum4
    {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) (h : w • d4Sum4 = d4Sum4) :
    w = 1 ∨ w = TwistTag.D4.orbitReflection ⟨1, by decide⟩ := by
  set w' : relWeylTwist TwistTag.D4 := ⟨w, hw⟩
  have h1 : TwistTag.D4.foldMap (foldedWeylEquiv TwistTag.D4 w' • d4SumBar) =
      TwistTag.D4.foldMap d4SumBar := by
    rw [← smul_foldMap_foldedWeylEquiv, foldMap_sumBar]
    exact h
  rcases weylG2_stab_g2c _ (TwistTag.D4.foldMap_injective h1) with h3 | h3
  · left
    have : w' = 1 := (foldedWeylEquiv TwistTag.D4).injective (by rw [h3, map_one]; rfl)
    exact congrArg Subtype.val this
  · right
    have : w' = ⟨_, TwistTag.D4.orbitReflection_mem ⟨1, by decide⟩⟩ :=
      (foldedWeylEquiv TwistTag.D4).injective (by rw [h3, foldedWeylEquiv_orbitReflection]; rfl)
    exact congrArg Subtype.val this

theorem posRoot_cases
    {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (hpos : 0 < height γ) :
    (∃ j : Fin 6, (j = 0 ∨ j = 2 ∨ j = 3) ∧ ∃ i : Fin 3,
      γ = permLattice (TwistTag.D4.perm ^ (i : ℕ)) (trialityRoot j)) ∨
    γ = trialityRoot 1 ∨ γ = trialityRoot 4 ∨ γ = trialityRoot 5 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hγ
  have key : ∀ k : Fin 24, 0 < height (TwistTag.D4.tag.rootCertificate.root k) →
      (∃ j : Fin 6, (j = 0 ∨ j = 2 ∨ j = 3) ∧ ∃ i : Fin 3,
        TwistTag.D4.tag.rootCertificate.root k =
          permLattice (TwistTag.D4.perm ^ (i : ℕ)) (trialityRoot j)) ∨
      TwistTag.D4.tag.rootCertificate.root k = trialityRoot 1 ∨
      TwistTag.D4.tag.rootCertificate.root k = trialityRoot 4 ∨
      TwistTag.D4.tag.rootCertificate.root k = trialityRoot 5 := by
    decide +kernel
  exact key ⟨k, hk⟩ hpos

end Weyl

section Sep

variable {τ : Tag} {K : Type} [Field K]

theorem coeff_eq_zero_of_prod_mem_posUnipotent
    (L : List (Fin τ.rank → ℤ))
    (hnd : L.Nodup) (hL : ∀ γ ∈ L, IsRoot τ γ)
    (hcomm : L.Pairwise fun γ δ => ∀ a b : K, Commute (pinnedX τ K γ a) (pinnedX τ K δ b))
    (c : (Fin τ.rank → ℤ) → K)
    (h : (L.map fun γ => pinnedX τ K γ (c γ)).prod ∈ posUnipotent τ K) :
    ∀ γ ∈ L, height γ < 0 → c γ = 0 := by
  classical
  set p : (Fin τ.rank → ℤ) → Bool := fun γ => decide (height γ < 0) with hp
  set Ln := L.filter p with hLn
  set Lp := L.filter (fun γ => !p γ) with hLp
  have hperm : (Ln ++ Lp).Perm L := List.filter_append_perm p L
  have hpw : (L.map fun γ => pinnedX τ K γ (c γ)).Pairwise Commute :=
    List.pairwise_map.2 (hcomm.imp fun h => h _ _)
  have hprod : (L.map fun γ => pinnedX τ K γ (c γ)).prod =
      (Ln.map fun γ => pinnedX τ K γ (c γ)).prod *
        (Lp.map fun γ => pinnedX τ K γ (c γ)).prod := by
    rw [← List.prod_append, ← List.map_append]
    exact (List.Perm.prod_eq' (hperm.symm.map _) hpw)
  have hpos : (Lp.map fun γ => pinnedX τ K γ (c γ)).prod ∈ posUnipotent τ K := by
    refine pinnedX_list_prod_mem_posUnipotent Lp (fun γ hγ => ?_) c
    obtain ⟨hγL, hγp⟩ := List.mem_filter.1 hγ
    refine ⟨hL γ hγL, ?_⟩
    rcases IsRoot.height_pos_or_neg (hL γ hγL) with h1 | h1
    · exact h1
    · simp [hp, h1] at hγp
  have hneg : (Ln.map fun γ => pinnedX τ K γ (c γ)).prod ∈ negUnipotent τ K := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hγL, hγp⟩ := List.mem_filter.1 hγ
    exact pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ height α < 0})
      ⟨hL γ hγL, by simpa [hp] using hγp⟩ (c γ)
  have hmem : (Ln.map fun γ => pinnedX τ K γ (c γ)).prod ∈ posUnipotent τ K := by
    have := mul_mem h (inv_mem hpos)
    rwa [hprod, mul_inv_cancel_right] at this
  have h1 : (Ln.map fun γ => pinnedX τ K γ (c γ)).prod = 1 := by
    have h2 := Subgroup.mem_inf.2 ⟨hmem, hneg⟩
    rw [CFSG.LieType.Chevalley.posUnipotent_inf_negUnipotent] at h2
    exact h2
  have h0 : (Ln.map fun γ => pinnedX τ K γ (c γ)).prod =
      (Ln.map fun γ => pinnedX τ K γ ((fun _ => (0 : K)) γ)).prod := by
    rw [h1]
    simp only [pinnedX_zero, List.map_const', List.prod_replicate, one_pow]
  intro γ hγ hγn
  exact CFSG.LieType.Ree.pinnedX_list_prod_injective_neg Ln (hnd.filter _)
    (fun α hα => ⟨hL α (List.mem_of_mem_filter hα), by
      simpa [hp] using (List.mem_filter.1 hα).2⟩) c _ h0 γ
    (List.mem_filter.2 ⟨hγ, by simpa [hp] using hγn⟩)

end Sep

section SepFin

variable {τ : Tag} {K : Type} [Field K]

theorem coeff_eq_zero_of_prod_ofFn_mem_posUnipotent
    {n : ℕ}
    (γ : Fin n → Fin τ.rank → ℤ) (hinj : Function.Injective γ) (hroot : ∀ i, IsRoot τ (γ i))
    (hcomm : ∀ i j, i ≠ j → ∀ a b : K, Commute (pinnedX τ K (γ i) a) (pinnedX τ K (γ j) b))
    (c : Fin n → K)
    (h : (List.ofFn fun i => pinnedX τ K (γ i) (c i)).prod ∈ posUnipotent τ K) :
    ∀ i, height (γ i) < 0 → c i = 0 := by
  classical
  intro i hi
  have : Nonempty (Fin n) := ⟨i⟩
  set c' : (Fin τ.rank → ℤ) → K := fun δ => c (Function.invFun γ δ) with hc'def
  have hc' : ∀ j, c' (γ j) = c j := fun j => by
    simp only [hc'def, Function.leftInverse_invFun hinj j]
  have hL : (List.ofFn fun j => pinnedX τ K (γ j) (c j)) =
      (List.ofFn γ).map fun δ => pinnedX τ K δ (c' δ) := by
    rw [List.map_ofFn]
    congr 1
    funext j
    simp only [Function.comp, hc']
  rw [← hc']
  refine coeff_eq_zero_of_prod_mem_posUnipotent (List.ofFn γ) (List.nodup_ofFn.2 hinj) ?_ ?_ c'
    (hL ▸ h) (γ i) (List.mem_ofFn.2 ⟨i, rfl⟩) hi
  · intro δ hδ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hδ
    exact hroot j
  · rw [List.pairwise_ofFn]
    intro j l hjl a b
    exact hcomm j l hjl.ne a b

end SepFin

section BorelA

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem d4x₁_conj_d4vA
    (s d e f : K) :
    d4x₁ K σ s * d4v K σ 0 0 d e f * (d4x₁ K σ s)⁻¹ =
      d4v K σ 0 0 d ((s * d + σ (s * d) + σ (σ (s * d))) + e) f := by
  have hconj : ∀ y, d4x₁ K σ s * y * (d4x₁ K σ s)⁻¹ = ⁅d4x₁ K σ s, y⁆ * y := fun y => by
    simp only [commutatorElement_def]
    group
  rw [← MulAut.conj_apply, d4v, map_mul, map_mul, map_mul, map_mul, MulAut.conj_apply,
    MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply,
    d4x₂_zero, d4x₃_zero, mul_one, mul_inv_cancel, hconj, comm_d4x₁_d4x₄ σ hσ,
    (commute_d4x₁_d4x₅ σ s e).eq, mul_inv_cancel_right, (commute_d4x₁_d4x₆ σ s f).eq,
    mul_inv_cancel_right, one_mul]
  simp only [one_mul, d4x₄_eq_d4v σ, d4x₅_eq_d4v σ, d4x₆_eq_d4v σ, d4v_mul σ hσ]
  exact d4v_congr σ (by ring) (by ring) (by ring) (by ring) (by simp)

include hσ in
theorem d4v_conj_d4vA
    (b c d' e' f' D E F : K) :
    d4v K σ b c d' e' f' * d4v K σ 0 0 D E F * (d4v K σ b c d' e' f')⁻¹ =
      d4v K σ 0 0 D E ((D * c + σ (D * c) + σ (σ (D * c))) + E * b + F) := by
  rw [d4v_inv σ hσ, d4v_mul σ hσ, d4v_mul σ hσ]
  refine d4v_congr σ (by rw [add_zero, add_self_d4]) (by rw [add_zero, add_self_d4])
    (by rw [add_comm d' D, add_assoc, add_self_d4, add_zero])
    (by rw [add_comm e' E, add_assoc, add_self_d4, add_zero]) ?_
  simp only [mul_zero, map_zero, add_zero, zero_add, add_mul, map_add]
  rw [mul_comm c d']
  linear_combination (d' * c + σ (d' * c) + σ (σ (d' * c)) + e' * b + f') *
    (CharTwo.two_eq_zero : (2 : K) = 0)

end BorelA

section BorelCoord

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

omit [CharP K 2] in
theorem ringEquiv_cube_d4 (hσ : ∀ c, σ (σ (σ c)) = c) : σ ^ 3 = 1 :=
  RingEquiv.ext fun c => by rw [ringEquiv_pow_three_apply, hσ]; rfl

omit [CharP K 2] in
theorem toRingHom_pow_three_d4 (hσ : ∀ c, σ (σ (σ c)) = c) : σ.toRingHom ^ 3 = 1 := by
  ext c
  simp only [RingHom.coe_pow, Function.iterate_succ, Function.comp_apply, Function.iterate_zero,
    id_eq, RingHom.one_def, RingHom.id_apply]
  exact hσ c

omit [CharP K 2] in
theorem d4v_injective
    {b c d e f b' c' d' e' f' : K}
    (h : d4v K σ b c d e f = d4v K σ b' c' d' e' f') :
    b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' := by
  have h' : d4x₁ K σ 0 * d4v K σ b c d e f = d4x₁ K σ 0 * d4v K σ b' c' d' e' f' := by rw [h]
  exact (d4coord_injective σ h').2

include hσ in
theorem exists_borel_coords
    [Finite K] {b : ModGL TwistTag.D4.tag K}
    (hb : b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom) :
    ∃ (a : Kˣ) (β : (trialityFixedField K σ.toRingHom)ˣ) (a₁ b₁ c₁ d₁ e₁ f₁ : K),
      σ b₁ = b₁ ∧ σ e₁ = e₁ ∧ σ f₁ = f₁ ∧
        trialityOuterTorus K σ a * trialityMiddleTorus K σ β ∈
          graphFixedRootTorus TwistTag.D4 K σ.toRingHom ∧
        d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁ ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ∧
        b = trialityOuterTorus K σ a * trialityMiddleTorus K σ β *
          (d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁) := by
  have hb' : b ∈ (graphFixedRootBorel TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) :=
    hb
  rw [graphFixedRootBorel_eq_mul σ.surjective] at hb'
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  obtain ⟨-, ⟨e, he⟩, -⟩ :=
    even_triality_faithful_torus_coordinates K σ (ringEquiv_cube_d4 σ hσ)
  obtain ⟨⟨a, β⟩, hab⟩ := e.surjective ⟨h, hh⟩
  have hh' : h = trialityOuterTorus K σ a * trialityMiddleTorus K σ β := by
    rw [← he, hab]
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, hb₁, he₁, hf₁, rfl⟩ :=
    exists_d4coord σ (toRingHom_pow_three_d4 σ hσ) hu
  exact ⟨a, β, a₁, b₁, c₁, d₁, e₁, f₁, hb₁, he₁, hf₁, hh' ▸ hh, hu, by rw [hh']⟩

include hσ in
theorem borel_conj_d4vA
    (a : Kˣ) (β : (trialityFixedField K σ.toRingHom)ˣ)
    (a₁ b₁ c₁ d₁ e₁ f₁ D E F : K) :
    trialityOuterTorus K σ a * trialityMiddleTorus K σ β *
        (d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁) * d4v K σ 0 0 D E F *
        (trialityOuterTorus K σ a * trialityMiddleTorus K σ β *
          (d4x₁ K σ a₁ * d4v K σ b₁ c₁ d₁ e₁ f₁))⁻¹ =
      d4v K σ 0 0 (σ a ^ 2 * σ (σ a) ^ 2 * ((a : K) * σ a * σ (σ a))⁻¹ * D)
        (((a : K) * σ a * σ (σ a)) * (((trialityFixedUnit K σ β : Kˣ) : K)⁻¹ *
          ((a₁ * D + σ (a₁ * D) + σ (σ (a₁ * D))) + E)))
        (((trialityFixedUnit K σ β : Kˣ) : K) *
          ((D * c₁ + σ (D * c₁) + σ (σ (D * c₁))) + E * b₁ + F)) := by
  have e : ∀ x y u v A : ModGL TwistTag.D4.tag K, x * y * (u * v) * A * (x * y * (u * v))⁻¹ =
      x * (y * (u * (v * A * v⁻¹) * u⁻¹) * y⁻¹) * x⁻¹ := fun x y u v A => by group
  rw [e, d4v_conj_d4vA σ hσ, d4x₁_conj_d4vA σ hσ, hm_conj_d4v, ho_conj_d4v σ hσ]
  simp only [mul_zero]

end BorelCoord

section CentZ

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

omit [CharP K 2] in
theorem exists_cell_d4
    {g : ModGL TwistTag.D4.tag K} (hg : g ∈ d4C K σ) :
    ∃ w ∈ relWeylTwist TwistTag.D4, ∃ b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom,
      ∃ b' ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom,
        g = b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * b' := by
  have hg' : g ∈ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom : Set _) := hg
  rw [graphFixedRootGroup_eq_iUnion σ.surjective] at hg'
  obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hgw
  exact ⟨w, hw, b, hb, b', hb', rfl⟩

include hσ in
theorem borel_conj_d4x₆
    [Finite K] {b : ModGL TwistTag.D4.tag K}
    (hb : b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ c : K, b * d4x₆ K c * b⁻¹ = d4x₆ K (μ * c) := by
  obtain ⟨a, β, a₁, b₁, c₁, d₁, e₁, f₁, -, -, -, -, -, rfl⟩ := exists_borel_coords σ hσ hb
  refine ⟨((trialityFixedUnit K σ β : Kˣ) : K), Units.ne_zero _, fun c => ?_⟩
  rw [d4x₆_eq_d4v σ, borel_conj_d4vA σ hσ, d4x₆_eq_d4v σ]
  refine d4v_congr σ rfl rfl (by simp) (by simp) (by simp)

omit [CharP K 2] in
theorem d4x₆_mem_posUnipotent
    (c : K) :
    d4x₆ K c ∈ posUnipotent TwistTag.D4.tag K :=
  pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α})
    ⟨isRoot_trialityRoot' 5, by decide⟩ c

include hσ in
theorem weyl_theta_of_commute
    [Finite K] {w : WeylGroup TwistTag.D4.tag}
    {b b' : ModGL TwistTag.D4.tag K} (hb : b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom)
    (hb' : b' ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom)
    (hz : b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * b' * d4z K *
      (b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * b')⁻¹ = d4z K) :
    w • trialityRoot 5 = trialityRoot 5 ∧ ∀ c : K,
      b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * b' * d4x₆ K c *
        (b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * b')⁻¹ = d4x₆ K c := by
  obtain ⟨μ₁, hμ₁, h₁⟩ := borel_conj_d4x₆ σ hσ hb'
  obtain ⟨μ₂, hμ₂, h₂⟩ := borel_conj_d4x₆ σ hσ (inv_mem hb)
  obtain ⟨μ₃, -, h₃⟩ := borel_conj_d4x₆ σ hσ hb
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K w with hn
  have hconj : ∀ x : K, n * d4x₆ K x * n⁻¹ = pinnedX TwistTag.D4.tag K (w • trialityRoot 5) x :=
    fun x => canonicalRep_mul_pinnedX_mul_inv_of_two CharTwo.two_eq_zero w
      (isRoot_trialityRoot' 5) x
  have e1 : ∀ x, b * n * b' * d4x₆ K x * (b * n * b')⁻¹ =
      b * (n * (b' * d4x₆ K x * b'⁻¹) * n⁻¹) * b⁻¹ := fun x => by group
  have hkey : pinnedX TwistTag.D4.tag K (w • trialityRoot 5) μ₁ = d4x₆ K μ₂ := by
    have h0 := hz
    rw [d4z, e1, h₁, mul_one, hconj] at h0
    calc pinnedX TwistTag.D4.tag K (w • trialityRoot 5) μ₁ =
        b⁻¹ * (b * pinnedX TwistTag.D4.tag K (w • trialityRoot 5) μ₁ * b⁻¹) * b⁻¹⁻¹ := by group
      _ = d4x₆ K μ₂ := by rw [h0, h₂, mul_one]
  have hwθ : w • trialityRoot 5 = trialityRoot 5 := by
    by_contra hne
    have hroot := IsRoot.smul (isRoot_trialityRoot' 5) w
    rcases IsRoot.height_pos_or_neg hroot with hp | hneg
    · have hinj := pinnedX_list_prod_injective [w • trialityRoot 5, trialityRoot 5]
        (by simp [hne]) (by
          intro α hα
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
          rcases hα with rfl | rfl
          · exact ⟨hroot, hp⟩
          · exact ⟨isRoot_trialityRoot' 5, by decide⟩)
        (fun γ => if γ = w • trialityRoot 5 then μ₁ else 0)
        (fun γ => if γ = trialityRoot 5 then μ₂ else 0) (by
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            ite_true, hne, Ne.symm hne, ite_false, pinnedX_zero, one_mul]
          exact hkey)
        (w • trialityRoot 5) (List.mem_cons_self)
      simp only [ite_true, hne, ite_false] at hinj
      exact hμ₁ hinj
    · have h0 := coeff_eq_zero_of_prod_mem_posUnipotent [w • trialityRoot 5]
        (List.nodup_singleton _) (by simpa using hroot) (List.pairwise_singleton _ _)
        (fun _ => μ₁) (by
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          rw [hkey]
          exact d4x₆_mem_posUnipotent _)
        (w • trialityRoot 5) (List.mem_singleton_self _) hneg
      exact hμ₁ h0
  refine ⟨hwθ, fun c => ?_⟩
  have hμ : μ₁ = μ₂ := by
    rw [hwθ] at hkey
    exact pinnedX_injective _ _ _ hkey
  have hμ₃ : μ₃ * μ₂ = 1 := by
    have h4 : b * d4x₆ K μ₂ * b⁻¹ = d4x₆ K 1 := by
      rw [← mul_one μ₂, ← h₂ 1]
      group
    rw [h₃] at h4
    exact pinnedX_injective _ _ _ h4
  rw [e1, h₁, hconj, hwθ]
  change b * d4x₆ K (μ₁ * c) * b⁻¹ = d4x₆ K c
  rw [h₃, ← mul_assoc, hμ, hμ₃, one_mul]

end CentZ

section CentT

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] def d4RootsA : Fin 5 → Fin TwistTag.D4.tag.rank → ℤ :=
  ![trialityRoot 3, permLattice TwistTag.D4.perm (trialityRoot 3),
    permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 3), trialityRoot 4, trialityRoot 5]

omit [CharP K 2] in
theorem ofFn_d4RootsA
    (w : WeylGroup TwistTag.D4.tag) (D E F : K) :
    (List.ofFn fun i => pinnedX TwistTag.D4.tag K (w • d4RootsA i)
        (![D, σ D, σ (σ D), E, F] i)).prod =
      pinnedX TwistTag.D4.tag K (w • trialityRoot 3) D *
        (pinnedX TwistTag.D4.tag K (w • permLattice TwistTag.D4.perm (trialityRoot 3)) (σ D) *
          (pinnedX TwistTag.D4.tag K (w • permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 3))
            (σ (σ D)) * (pinnedX TwistTag.D4.tag K (w • trialityRoot 4) E *
              pinnedX TwistTag.D4.tag K (w • trialityRoot 5) F))) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem canonicalRep_conj_d4vA
    (w : WeylGroup TwistTag.D4.tag) (D E F : K) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K w * d4v K σ 0 0 D E F *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ =
      (List.ofFn fun i => pinnedX TwistTag.D4.tag K (w • d4RootsA i)
        (![D, σ D, σ (σ D), E, F] i)).prod := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e : ∀ (n a₁ a₂ a₃ a₄ a₅ : ModGL TwistTag.D4.tag K),
      n * (a₁ * a₂ * a₃ * a₄ * a₅) * n⁻¹ = (n * a₁ * n⁻¹) * ((n * a₂ * n⁻¹) * ((n * a₃ * n⁻¹) *
        ((n * a₄ * n⁻¹) * ((n * a₅ * n⁻¹) * 1)))) := fun n a₁ a₂ a₃ a₄ a₅ => by group
  have r1 : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm (trialityRoot 3)) := by
    simpa using (isRoot_trialityRoot 3 1).1
  rw [d4v, d4x₂_zero, d4x₃_zero, one_mul, one_mul, d4x₄, coe_trialityOrbitProd, d4x₅, d4x₆, e,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_trialityRoot' 3),
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w r1,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_trialityRoot 3 2).1,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_trialityRoot' 4),
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_trialityRoot' 5)]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  rfl

omit [CharP K 2] in
theorem d4coord_mem_posUnipotent
    (a b c d e f : K) :
    d4x₁ K σ a * d4v K σ b c d e f ∈ posUnipotent TwistTag.D4.tag K := by
  rw [← d4factors_prod]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  exact rootSpan_mono (trialityOrbit_pos j) (d4factors_mem σ a b c d e f j)

omit [CharP K 2] in
theorem d4v_mem_posUnipotent
    (b c d e f : K) :
    d4v K σ b c d e f ∈ posUnipotent TwistTag.D4.tag K := by
  have h := d4coord_mem_posUnipotent σ 0 b c d e f
  rwa [d4x₁_zero, one_mul] at h

include hσ in
theorem borel_conj_d4t
    [Finite K] {b : ModGL TwistTag.D4.tag K}
    (hb : b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom) :
    ∃ l ε φ : K, l ≠ 0 ∧ σ ε = ε ∧ σ φ = φ ∧ b * d4t K σ * b⁻¹ = d4v K σ 0 0 l ε φ := by
  obtain ⟨a, β, a₁, b₁, c₁, d₁, e₁, f₁, -, -, -, -, -, rfl⟩ := exists_borel_coords σ hσ hb
  have hβ : σ ((trialityFixedUnit K σ β : Kˣ) : K) = (trialityFixedUnit K σ β : Kˣ) :=
    sigma_trialityFixedUnit β
  have hT : ∀ x : K, σ (x + σ x + σ (σ x)) = x + σ x + σ (σ x) := fun x => by
    rw [map_add, map_add, hσ]
    ring
  have hN : σ ((a : K) * σ a * σ (σ a)) = (a : K) * σ a * σ (σ a) := by
    rw [map_mul, map_mul, hσ]
    ring
  refine ⟨_, _, _, ?_, ?_, ?_, by rw [d4t, d4x₄_eq_d4v σ, borel_conj_d4vA σ hσ]⟩
  · have ha : (a : K) ≠ 0 := a.ne_zero
    have hσa : σ (a : K) ≠ 0 := (map_ne_zero σ).2 ha
    have hσσa : σ (σ (a : K)) ≠ 0 := (map_ne_zero σ).2 hσa
    simp only [mul_one]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hσa) (pow_ne_zero _ hσσa))
      (inv_ne_zero (mul_ne_zero (mul_ne_zero ha hσa) hσσa))
  · simp only [map_mul, map_inv₀, map_add, mul_one, add_zero, hβ, hσ]
    ring
  · simp only [map_mul, map_add, add_zero, one_mul, zero_mul, hβ, hσ]
    ring

theorem trialityRoot_orthogonal
    : ∀ j : Fin 6, (j = 0 ∨ j = 2 ∨ j = 3) →
    trialityRoot j ⬝ᵥ (TwistTag.D4.tag.symmetrizedCartan *ᵥ
        permLattice TwistTag.D4.perm (trialityRoot j)) = 0 ∧
      trialityRoot j ⬝ᵥ (TwistTag.D4.tag.symmetrizedCartan *ᵥ
        permLattice (TwistTag.D4.perm ^ 2) (trialityRoot j)) = 0 ∧
      permLattice TwistTag.D4.perm (trialityRoot j) ⬝ᵥ (TwistTag.D4.tag.symmetrizedCartan *ᵥ
        permLattice (TwistTag.D4.perm ^ 2) (trialityRoot j)) = 0 := by
  decide +kernel

omit [CharP K 2] in
include hσ in
theorem orbit_rot
    (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 3) (i : Fin 3) (l : K) :
    ∃ μ : K, (μ = 0 → l = 0) ∧
      pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ (i : ℕ)) (trialityRoot j)) l *
        (pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm
            (permLattice (TwistTag.D4.perm ^ (i : ℕ)) (trialityRoot j))) (σ l) *
          pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm (permLattice TwistTag.D4.perm
            (permLattice (TwistTag.D4.perm ^ (i : ℕ)) (trialityRoot j)))) (σ (σ l))) =
        (trialityOrbitProd K σ.toRingHom (trialityRoot j) μ : ModGL TwistTag.D4.tag K) := by
  obtain ⟨o₁, o₂, o₃⟩ := trialityRoot_orthogonal j hj
  have r₀ := isRoot_trialityRoot' j
  have r₁ : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm (trialityRoot j)) := by
    simpa using (isRoot_trialityRoot j 1).1
  have r₂ := (isRoot_trialityRoot j 2).1
  have c₁ := commute_pinnedX_of_rootForm_eq_zero K r₀ r₁ o₁
  have c₂ := commute_pinnedX_of_rootForm_eq_zero K r₀ r₂ o₂
  have c₃ := commute_pinnedX_of_rootForm_eq_zero K r₁ r₂ o₃
  fin_cases i
  · refine ⟨l, id, ?_⟩
    simp only [pow_zero]
    rw [coe_trialityOrbitProd, permLattice_D4_perm_perm, mul_assoc]
    rfl
  · refine ⟨σ (σ l), fun h => by simpa using h, ?_⟩
    simp only [pow_one]
    rw [coe_trialityOrbitProd, permLattice_D4_perm_perm, permLattice_D4_perm_perm_sq]
    change _ = pinnedX TwistTag.D4.tag K (trialityRoot j) (σ (σ l)) *
      pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm (trialityRoot j)) (σ (σ (σ l))) *
        pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) (trialityRoot j))
          (σ (σ (σ (σ l))))
    simp only [hσ]
    rw [← mul_assoc, ((c₁ _ _).symm.mul_left (c₂ _ _).symm).eq, mul_assoc]
  · refine ⟨σ l, fun h => by simpa using h, ?_⟩
    rw [coe_trialityOrbitProd, permLattice_D4_perm_perm_sq]
    change _ = pinnedX TwistTag.D4.tag K (trialityRoot j) (σ l) *
      pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm (trialityRoot j)) (σ (σ l)) *
        pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) (trialityRoot j))
          (σ (σ (σ l)))
    simp only [hσ]
    rw [((c₂ _ _).symm.mul_right (c₃ _ _).symm).eq]

omit [CharP K 2] in
theorem fixedRoot_factor
    {δ : Fin TwistTag.D4.tag.rank → ℤ} (hδ : IsRoot TwistTag.D4.tag δ)
    (hfix : permLattice TwistTag.D4.perm δ = δ) {ε : K} (hneg : height δ < 0 → ε = 0) :
    ∃ b e f : K, pinnedX TwistTag.D4.tag K δ ε = d4v K σ b 0 0 e f := by
  rcases IsRoot.height_pos_or_neg hδ with hp | hn
  · rcases posRoot_cases hδ hp with ⟨j, hj, i, rfl⟩ | rfl | rfl | rfl
    · exfalso
      revert hfix
      rcases hj with rfl | rfl | rfl <;> fin_cases i <;> decide +kernel
    · exact ⟨ε, 0, 0, d4x₂_eq_d4v σ ε⟩
    · exact ⟨0, ε, 0, d4x₅_eq_d4v σ ε⟩
    · exact ⟨0, 0, ε, d4x₆_eq_d4v σ ε⟩
  · rw [hneg hn, pinnedX_zero]
    exact ⟨0, 0, 0, (d4v_zero σ).symm⟩

end CentT

section CentT2

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

theorem d4RootsA_isRoot
    (i : Fin 5) : IsRoot TwistTag.D4.tag (d4RootsA i) := by
  fin_cases i
  · exact isRoot_trialityRoot' 3
  · show IsRoot _ (permLattice TwistTag.D4.perm (trialityRoot 3))
    simpa using (isRoot_trialityRoot 3 1).1
  · exact (isRoot_trialityRoot 3 2).1
  · exact isRoot_trialityRoot' 4
  · exact isRoot_trialityRoot' 5

theorem d4RootsA_injective : Function.Injective d4RootsA := by
  decide +kernel

theorem d4RootsA_ne_neg : ∀ i j : Fin 5, d4RootsA i ≠ -d4RootsA j := by
  decide +kernel

theorem d4RootsA_add_not_isRoot
    (i j : Fin 5) (hij : i ≠ j) :
    ¬ IsRoot TwistTag.D4.tag (d4RootsA i + d4RootsA j) := by
  intro h
  obtain ⟨k, hk, hkv⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 h
  have key : ∀ i j : Fin 5, i ≠ j → ∀ k : Fin 24,
      TwistTag.D4.tag.rootCertificate.root k ≠ d4RootsA i + d4RootsA j := by
    decide +kernel
  exact key i j hij ⟨k, hk⟩ hkv

omit [CharP K 2] in
theorem commute_d4RootsA
    (w : WeylGroup TwistTag.D4.tag) (i j : Fin 5) (hij : i ≠ j)
    (a c : K) : Commute (pinnedX TwistTag.D4.tag K (w • d4RootsA i) a)
      (pinnedX TwistTag.D4.tag K (w • d4RootsA j) c) := by
  have hroot : ∀ i, IsRoot TwistTag.D4.tag (w • d4RootsA i) := fun i =>
    IsRoot.smul (d4RootsA_isRoot i) w
  refine (simply_laced_root_commutator_unit TwistTag.D4.tag (Or.inl rfl) (hroot i) (hroot j)
    ?_ ?_).2 ?_ K _ (mem_rootSubgroup.2 ⟨a, rfl⟩) _ (mem_rootSubgroup.2 ⟨c, rfl⟩)
  · exact fun h => hij (d4RootsA_injective (smul_left_cancel w h))
  · intro h
    rw [← smul_neg] at h
    exact d4RootsA_ne_neg i j (smul_left_cancel w h)
  · intro h
    rw [← smul_add] at h
    have h' := IsRoot.smul h w⁻¹
    rw [inv_smul_smul] at h'
    exact d4RootsA_add_not_isRoot i j hij h'

include hσ in
theorem weyl_t_of_commute
    [Finite K] {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) {b b' : ModGL TwistTag.D4.tag K}
    (hb : b ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom)
    (hb' : b' ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom)
    (ht : b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * b' * d4t K σ *
      (b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * b')⁻¹ = d4t K σ) :
    w = 1 ∨ w = TwistTag.D4.orbitReflection ⟨1, by decide⟩ := by
  obtain ⟨l₁, ε₁, φ₁, hl₁, -, -, h₁⟩ := borel_conj_d4t σ hσ hb'
  obtain ⟨l₂, ε₂, φ₂, hl₂, -, -, h₂⟩ := borel_conj_d4t σ hσ (inv_mem hb)
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K w with hn
  have hkey : n * d4v K σ 0 0 l₁ ε₁ φ₁ * n⁻¹ = d4v K σ 0 0 l₂ ε₂ φ₂ := by
    rw [← h₁, ← h₂]
    calc n * (b' * d4t K σ * b'⁻¹) * n⁻¹ =
        b⁻¹ * (b * n * b' * d4t K σ * (b * n * b')⁻¹) * b⁻¹⁻¹ := by group
      _ = b⁻¹ * d4t K σ * b⁻¹⁻¹ := by rw [ht]
  have hρ : ∀ v, w • permLattice TwistTag.D4.perm v = permLattice TwistTag.D4.perm (w • v) :=
    (mem_relWeylTwist_iff_smul TwistTag.D4).1 hw
  have hroot : ∀ i, IsRoot TwistTag.D4.tag (w • d4RootsA i) := fun i =>
    IsRoot.smul (d4RootsA_isRoot i) w
  have hsep := coeff_eq_zero_of_prod_ofFn_mem_posUnipotent (fun i => w • d4RootsA i)
    (fun i j h => d4RootsA_injective (smul_left_cancel w h)) hroot
    (commute_d4RootsA w) ![l₁, σ l₁, σ (σ l₁), ε₁, φ₁] (by
      rw [← canonicalRep_conj_d4vA σ w, hkey]
      exact d4v_mem_posUnipotent σ _ _ _ _ _)
  rw [canonicalRep_conj_d4vA σ w, ofFn_d4RootsA σ w] at hkey
  have hpos : 0 < height (w • trialityRoot 3) := by
    rcases IsRoot.height_pos_or_neg (hroot 0) with h | h
    · exact h
    · exact absurd (hsep 0 h) hl₁
  have hfix₄ : permLattice TwistTag.D4.perm (w • trialityRoot 4) = w • trialityRoot 4 := by
    rw [← hρ]
    exact congrArg (w • ·) (by decide +kernel)
  have hfix₅ : permLattice TwistTag.D4.perm (w • trialityRoot 5) = w • trialityRoot 5 := by
    rw [← hρ]
    exact congrArg (w • ·) (by decide +kernel)
  obtain ⟨b₄, e₄, f₄, hf₄⟩ := fixedRoot_factor σ (δ := w • trialityRoot 4) (ε := ε₁) (hroot 3)
    hfix₄ (hsep 3)
  obtain ⟨b₅, e₅, f₅, hf₅⟩ := fixedRoot_factor σ (δ := w • trialityRoot 5) (ε := φ₁) (hroot 4)
    hfix₅ (hsep 4)
  rw [hf₄, hf₅, d4v_mul σ hσ] at hkey
  rcases posRoot_cases (γ := w • trialityRoot 3) (hroot 0) hpos with ⟨j, hj, i, hji⟩ | hfix | hfix |
      hfix
  · have e₁ : w • permLattice TwistTag.D4.perm (trialityRoot 3) = permLattice TwistTag.D4.perm
        (permLattice (TwistTag.D4.perm ^ (i : ℕ)) (trialityRoot j)) := by
      rw [hρ]
      exact congrArg _ hji
    have e₂ : w • permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 3) =
        permLattice TwistTag.D4.perm (permLattice TwistTag.D4.perm
          (permLattice (TwistTag.D4.perm ^ (i : ℕ)) (trialityRoot j))) := by
      rw [← permLattice_D4_perm_perm, hρ, hρ]
      exact congrArg _ (congrArg _ hji)
    obtain ⟨μ, hμ, hrot⟩ := orbit_rot σ hσ j hj i l₁
    have hre : ∀ x y z u : ModGL TwistTag.D4.tag K, x * (y * (z * u)) = (x * (y * z)) * u :=
      fun x y z u => by group
    rw [hji, e₁, e₂, hre, hrot] at hkey
    rcases hj with rfl | rfl | rfl
    · exfalso
      have h0 : d4x₁ K σ μ * d4v K σ (b₄ + b₅) (0 + 0) (0 + 0) (e₄ + e₅)
          ((0 * 0 + σ (0 * 0) + σ (σ (0 * 0))) + (e₄ * b₅ + f₄) + f₅) =
          d4x₁ K σ 0 * d4v K σ 0 0 l₂ ε₂ φ₂ := by
        rw [d4x₁_zero, one_mul]
        exact hkey
      exact hl₁ (hμ (d4coord_injective σ h0).1)
    · exfalso
      have h0 := hkey
      change d4x₃ K σ μ * _ = _ at h0
      rw [d4x₃_eq_d4v σ, d4v_mul σ hσ] at h0
      exact hl₂ (by simpa using ((d4v_injective σ h0).2.2.1).symm)
    · have hsum : w • d4Sum4 = d4Sum4 := by
        rw [d4Sum4, smul_add, smul_add, hji, e₁, e₂]
        fin_cases i <;> decide +kernel
      exact relWeyl_stab_sum4 hw hsum
  all_goals exfalso
  all_goals apply (by decide +kernel :
    permLattice TwistTag.D4.perm (trialityRoot 3) ≠ trialityRoot 3)
  all_goals refine smul_left_cancel w ((hρ (trialityRoot 3)).trans ?_)
  all_goals rw [hfix]
  all_goals decide +kernel

end CentT2

end CFSG.ComponentClassification.RankTwoExceptional.D4

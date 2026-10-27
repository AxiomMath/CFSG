module

public import CFSG.LieType.Chevalley.GraphFixedRankOneBruhat
public import CFSG.LieType.Chevalley.RankOneCentralImage

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley Matrix

section Map

variable {L K : Type} [Field L] [Field K] (f : L →+* K)

theorem map_uSL (s : L) : SpecialLinearGroup.map f (uSL s) = uSL (f s) :=
  SL2_ext (by simp [coe_uSL]) (by simp [coe_uSL]) (by simp [coe_uSL]) (by simp [coe_uSL])

theorem map_vSL (s : L) : SpecialLinearGroup.map f (vSL s) = vSL (f s) :=
  SL2_ext (by simp [coe_vSL]) (by simp [coe_vSL]) (by simp [coe_vSL]) (by simp [coe_vSL])

theorem map_HSL (u : Lˣ) : SpecialLinearGroup.map f (HSL u) = HSL (Units.map f.toMonoidHom u) :=
  SL2_ext (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL])

theorem map_WSL : SpecialLinearGroup.map f WSL = WSL :=
  SL2_ext (by simp [coe_WSL]) (by simp [coe_WSL]) (by simp [coe_WSL]) (by simp [coe_WSL])

end Map

variable (t : TwistTag) (K : Type) [Field K]

@[expose] def rankOneHom
    (i : Fin t.tag.rank) : SL2 K →* ModGL t.tag K :=
  (exceptional_ordinary_rank_one_central_image (τ := t.tag) (K := K) i).choose

variable {t K}

theorem rankOneHom_uSL
    (i : Fin t.tag.rank) (c : K) :
    rankOneHom t K i (uSL c) = xUnit t.tag K i c :=
  (exceptional_ordinary_rank_one_central_image (τ := t.tag) (K := K) i).choose_spec.1 c

theorem rankOneHom_vSL
    (i : Fin t.tag.rank) (c : K) :
    rankOneHom t K i (vSL c) = yUnit t.tag K i c :=
  (exceptional_ordinary_rank_one_central_image (τ := t.tag) (K := K) i).choose_spec.2.1 c

theorem rankOneHom_HSL
    (i : Fin t.tag.rank) (u : Kˣ) :
    rankOneHom t K i (HSL u) = torusElt t.tag K i u :=
  (exceptional_ordinary_rank_one_central_image (τ := t.tag) (K := K) i).choose_spec.2.2.1 u

theorem rankOneHom_WSL
    (i : Fin t.tag.rank) : rankOneHom t K i WSL = weylElt t.tag K i 1 :=
  (exceptional_ordinary_rank_one_central_image (τ := t.tag) (K := K) i).choose_spec.2.2.2.1

theorem rankOneHom_range
    (i : Fin t.tag.rank) :
    (rankOneHom t K i).range =
      Subgroup.closure (Set.range (xUnit t.tag K i) ∪ Set.range (yUnit t.tag K i)) :=
  (exceptional_ordinary_rank_one_central_image (τ := t.tag) (K := K) i).choose_spec.2.2.2.2.1

theorem SL2_hom_ext {G : Type*} [Group G] {φ ψ : SL2 K →* G} (hu : ∀ s, φ (uSL s) = ψ (uSL s))
    (hH : ∀ u, φ (HSL u) = ψ (HSL u)) (hW : φ WSL = ψ WSL) : φ = ψ :=
  MonoidHom.ext fun g => SL2_induction (p := fun g => φ g = ψ g)
    (fun g g' h h' => by rw [map_mul, map_mul, h, h']) hu hH hW g

theorem commute_rankOneHom
    {a : Fin t.foldedTag.rank} {i j : Fin t.tag.rank}
    (hi : i ∈ t.orbit a) (hj : j ∈ t.orbit a) (hij : i ≠ j) (g g' : SL2 K) :
    Commute (rankOneHom t K i g) (rankOneHom t K j g') := by
  have hgen : ∀ x ∈ Set.range (xUnit t.tag K i) ∪ Set.range (yUnit t.tag K i),
      ∀ y ∈ Set.range (xUnit t.tag K j) ∪ Set.range (yUnit t.tag K j), Commute x y := by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · exact commute_xUnit_xUnit K hi hj c d
    · exact commute_xUnit_yUnit K hi hj hij c d
    · exact (commute_xUnit_yUnit K hj hi (Ne.symm hij) d c).symm
    · exact commute_yUnit_yUnit K hi hj hij c d
  have hle : Subgroup.closure (Set.range (xUnit t.tag K i) ∪ Set.range (yUnit t.tag K i)) ≤
      Subgroup.centralizer
        (Subgroup.closure (Set.range (xUnit t.tag K j) ∪ Set.range (yUnit t.tag K j)) :
          Set (ModGL t.tag K)) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    have hle' : Subgroup.closure (Set.range (xUnit t.tag K j) ∪ Set.range (yUnit t.tag K j)) ≤
        Subgroup.centralizer {x} :=
      (Subgroup.closure_le _).2 fun y hy z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (hgen z hx y hy).eq
    exact Subgroup.mem_centralizer_iff.2 fun y hy => (hle' hy x rfl).symm
  have hg : rankOneHom t K i g ∈ (rankOneHom t K i).range := ⟨g, rfl⟩
  have hg' : rankOneHom t K j g' ∈ (rankOneHom t K j).range := ⟨g', rfl⟩
  rw [rankOneHom_range] at hg hg'
  exact ((Subgroup.mem_centralizer_iff.1 (hle hg)) _ hg').symm

variable (t K) (σ : K →+* K)

@[expose] def orbitRankOneHom
    (a : Fin t.foldedTag.rank) :
    SL2 (orbitField t K σ a) →* ModGL t.tag K where
  toFun g := ((List.range (t.orbit a).card).map fun k =>
    rankOneHom t K ((t.perm ^ k) (t.orbitMin a))
      (SpecialLinearGroup.map ((σ ^ k).comp (orbitField t K σ a).subtype) g)).prod
  map_one' := by simp
  map_mul' g g' := by
    simp only [map_mul]
    refine list_prod_map_mul_of_commute_of_ne List.nodup_range _ _ fun k hk l hl hkl => ?_
    have hk' := List.mem_range.1 hk
    have hl' := List.mem_range.1 hl
    refine commute_rankOneHom (a := a) (t.perm_pow_mem_orbit (t.orbitMin_mem a) k)
      (t.perm_pow_mem_orbit (t.orbitMin_mem a) l) (fun h => hkl ?_) _ _
    exact congrArg Fin.val (injective_pow_orbitMin t a (a₁ := ⟨k, hk'⟩) (a₂ := ⟨l, hl'⟩) h)

variable {t K σ}

theorem orbitRankOneHom_apply
    (a : Fin t.foldedTag.rank) (g : SL2 (orbitField t K σ a)) :
    orbitRankOneHom t K σ a g = ((List.range (t.orbit a).card).map fun k =>
      rankOneHom t K ((t.perm ^ k) (t.orbitMin a))
        (SpecialLinearGroup.map ((σ ^ k).comp (orbitField t K σ a).subtype) g)).prod :=
  rfl

theorem orbitRankOneHom_uSL
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    orbitRankOneHom t K σ a (uSL c) = orbitX t K σ a c := by
  rw [orbitRankOneHom_apply, coe_orbitX]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [map_uSL, rankOneHom_uSL]
  rfl

theorem orbitRankOneHom_vSL
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    orbitRankOneHom t K σ a (vSL c) = orbitY t K σ a c := by
  rw [orbitRankOneHom_apply, coe_orbitY]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [map_vSL, rankOneHom_vSL]
  rfl

theorem orbitRankOneHom_HSL
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    orbitRankOneHom t K σ a (HSL u) = orbitH t K σ a u := by
  rw [orbitRankOneHom_apply, coe_orbitH]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [map_HSL, rankOneHom_HSL]

theorem orbitRankOneHom_WSL
    (a : Fin t.foldedTag.rank) :
    orbitRankOneHom t K σ a WSL = orbitN t K σ a 1 := by
  rw [orbitRankOneHom_apply, coe_orbitN_one, t.orbitWord_eq_map_range, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [map_WSL, rankOneHom_WSL]
  rfl

theorem orbitRankOneHom_range
    (a : Fin t.foldedTag.rank) :
    (orbitRankOneHom t K σ a).range = Subgroup.closure
      (Set.range (fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K)) ∪
        Set.range (fun c : orbitField t K σ a => (orbitY t K σ a c : ModGL t.tag K))) := by
  set M := Subgroup.closure
    (Set.range (fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K)) ∪
      Set.range (fun c : orbitField t K σ a => (orbitY t K σ a c : ModGL t.tag K)))
  have hx : ∀ c, (orbitX t K σ a c : ModGL t.tag K) ∈ M := fun c =>
    Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
  have hy : ∀ c, (orbitY t K σ a c : ModGL t.tag K) ∈ M := fun c =>
    Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  have hn : ∀ u : (orbitField t K σ a)ˣ, (orbitN t K σ a u : ModGL t.tag K) ∈ M := fun u => by
    rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨g, rfl⟩
    refine SL2_induction (p := fun g => orbitRankOneHom t K σ a g ∈ M)
      (fun g g' h h' => by rw [map_mul]; exact mul_mem h h') (fun s => ?_) (fun u => ?_) ?_ g
    · rw [orbitRankOneHom_uSL]
      exact hx s
    · rw [orbitRankOneHom_HSL, orbitH, Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (hn u) (inv_mem (hn 1))
    · rw [orbitRankOneHom_WSL]
      exact hn 1
  · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨uSL c, orbitRankOneHom_uSL a c⟩
    · exact ⟨vSL c, orbitRankOneHom_vSL a c⟩

theorem canonicalRep_orbitReflection_not_mem_borelGroup
    (a : Fin t.foldedTag.rank) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∉ borelGroup t.tag K := by
  intro h
  have h1 : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
      bruhatCell t.tag K 1 := by
    refine mem_bruhatCell.2 ⟨canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a), h, 1,
      one_mem _, ?_⟩
    rw [canonicalRep_one, mul_one, mul_one]
  exact Set.disjoint_left.1 (disjoint_bruhatCell (t.orbitReflection_ne_one a))
    (canonicalRep_mem_bruhatCell (t.orbitReflection a)) h1

theorem orbitH_mem_torusGroup
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    (orbitH t K σ a u : ModGL t.tag K) ∈ torusGroup t.tag K := by
  rw [coe_orbitH_eq]
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact torusElt_mem_torusGroup j _

theorem eq_smul_one_of_mem_ker_orbitRankOneHom
    {a : Fin t.foldedTag.rank}
    {g : SL2 (orbitField t K σ a)} (hg : g ∈ (orbitRankOneHom t K σ a).ker) :
    ∃ l : (orbitField t K σ a)ˣ, (l : orbitField t K σ a) ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) =
        (l : orbitField t K σ a) • (1 : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) := by
  rw [MonoidHom.mem_ker] at hg
  obtain ⟨-, -, -, hHU, -⟩ := triangular_borel_structure.{0, 0} t.tag K
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 1 0 = 0
  · rw [eq_HSL_mul_uSL hc, map_mul, orbitRankOneHom_HSL, orbitRankOneHom_uSL] at hg
    generalize hu : Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc) = u at hg
    generalize hb : (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 0 1 /
      (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 0 0 = b at hg
    have hu00 : (u : orbitField t K σ a) = (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 0 0 :=
      by rw [← hu, Units.val_mk0]
    have hxb : (orbitX t K σ a b : ModGL t.tag K) = (orbitH t K σ a u : ModGL t.tag K)⁻¹ :=
      eq_inv_of_mul_eq_one_right hg
    have hxH : (orbitX t K σ a b : ModGL t.tag K) ∈ torusGroup t.tag K ⊓ posUnipotent t.tag K :=
      Subgroup.mem_inf.2 ⟨hxb ▸ inv_mem (orbitH_mem_torusGroup a u),
        (Subgroup.mem_inf.1 (orbitX_mem_graphFixedPosUnipotent t σ a b)).1⟩
    rw [hHU, Subgroup.mem_bot] at hxH
    have hb0 : b = 0 := orbitX_injective σ a (Subtype.ext (by rw [orbitX_zero]; exact hxH))
    have hh1 : (orbitH t K σ a u : ModGL t.tag K) = 1 := by
      rw [hxH, one_eq_inv] at hxb
      exact hxb
    have hsq : (u : orbitField t K σ a) ^ 2 = 1 := by
      have h := orbitH_mul_orbitX_mul_inv t σ a u 1
      have h' : orbitH t K σ a u = 1 := Subtype.ext hh1
      rw [h', one_mul, inv_one, mul_one, mul_one] at h
      exact (orbitX_injective σ a h).symm
    refine ⟨u, hsq, ?_⟩
    have h01 : (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 0 1 = 0 := by
      rw [hb0] at hb
      rcases div_eq_zero_iff.1 hb with h | h
      · exact h
      · exact absurd h (SL2_apply_zero_zero_ne_zero hc)
    have hdet := det_SL2 g
    rw [hc, mul_zero, sub_zero, ← hu00] at hdet
    have h11 : (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 1 1 = u := by
      have h2 : (u : orbitField t K σ a) * u = 1 := by rw [← sq]; exact hsq
      calc (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 1 1 =
            u * u * (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 1 1 := by rw [h2, one_mul]
        _ = u * (u * (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 1 1) := by ring
        _ = u := by rw [hdet, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, hc, h11, ← hu00]
  · rw [eq_uSL_mul_HSL_mul_WSL_mul_uSL hc, map_mul, map_mul, map_mul, orbitRankOneHom_uSL,
      orbitRankOneHom_HSL, orbitRankOneHom_WSL, orbitRankOneHom_uSL] at hg
    exfalso
    refine canonicalRep_orbitReflection_not_mem_borelGroup (K := K) a ?_
    rw [canonicalRep_orbitReflection_eq_orbitN t σ a]
    set x₁ := (orbitX t K σ a ((g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 0 0 /
      (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 1 0) : ModGL t.tag K)
    set x₂ := (orbitX t K σ a ((g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 1 1 /
      (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 1 0) : ModGL t.tag K)
    set h := (orbitH t K σ a (Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) 1 0)
      (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)) : ModGL t.tag K)
    have hxB : ∀ c, (orbitX t K σ a c : ModGL t.tag K) ∈ borelGroup t.tag K := fun c =>
      Subgroup.mem_sup_right (Subgroup.mem_inf.1 (orbitX_mem_graphFixedPosUnipotent t σ a c)).1
    have hhB : h ∈ borelGroup t.tag K := Subgroup.mem_sup_left (orbitH_mem_torusGroup a _)
    have e : (orbitN t K σ a 1 : ModGL t.tag K) = h⁻¹ * x₁⁻¹ * x₂⁻¹ := by
      calc (orbitN t K σ a 1 : ModGL t.tag K) =
            h⁻¹ * x₁⁻¹ * (x₁ * h * (orbitN t K σ a 1 : ModGL t.tag K) * x₂) * x₂⁻¹ := by group
        _ = h⁻¹ * x₁⁻¹ * x₂⁻¹ := by rw [hg, mul_one]
    rw [e]
    exact mul_mem (mul_mem (inv_mem hhB) (inv_mem (hxB _))) (inv_mem (hxB _))

theorem exceptional_fixed_rank_one_central_image
    (t : TwistTag) (K : Type) [Field K]
    (σ : K →+* K) (a : Fin t.foldedTag.rank) :
    ∃ R : SL2 (orbitField t K σ a) →* ModGL t.tag K,
      (∀ c, R (uSL c) = orbitX t K σ a c) ∧ (∀ c, R (vSL c) = orbitY t K σ a c) ∧
      (∀ u, R (HSL u) = orbitH t K σ a u) ∧ R WSL = orbitN t K σ a 1 ∧
      (orbitN t K σ a 1 : ModGL t.tag K) =
        canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∧
      R.range = Subgroup.closure
        (Set.range (fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K)) ∪
          Set.range (fun c : orbitField t K σ a => (orbitY t K σ a c : ModGL t.tag K))) ∧
      Subgroup.closure
          (Set.range (fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K)) ∪
            Set.range (fun c : orbitField t K σ a => (orbitY t K σ a c : ModGL t.tag K))) ≤
        graphFixedRootGroup t K σ ∧
      (∀ g ∈ R.ker, ∃ l : (orbitField t K σ a)ˣ, (l : orbitField t K σ a) ^ 2 = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) =
          (l : orbitField t K σ a) • (1 : Matrix (Fin 2) (Fin 2) (orbitField t K σ a))) ∧
      ∀ ρ' : Fin t.tag.rank → SL2 K →* ModGL t.tag K,
        (∀ i c, ρ' i (uSL c) = xUnit t.tag K i c) → (∀ i u, ρ' i (HSL u) = torusElt t.tag K i u) →
        (∀ i, ρ' i WSL = weylElt t.tag K i 1) → ∀ g, R g =
          ((List.range (t.orbit a).card).map fun k => ρ' ((t.perm ^ k) (t.orbitMin a))
            (SpecialLinearGroup.map ((σ ^ k).comp (orbitField t K σ a).subtype) g)).prod := by
  refine ⟨orbitRankOneHom t K σ a, orbitRankOneHom_uSL a, orbitRankOneHom_vSL a,
    orbitRankOneHom_HSL a, orbitRankOneHom_WSL a,
    (canonicalRep_orbitReflection_eq_orbitN t σ a).symm,
    orbitRankOneHom_range a, (Subgroup.closure_le _).2 ?_,
    fun g hg => eq_smul_one_of_mem_ker_orbitRankOneHom hg, fun ρ' hu hH hW g => ?_⟩
  · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
        (orbitX_mem_graphFixedPosUnipotent t σ a c)
    · exact graphFixedNegUnipotent_le_graphFixedRootGroup t K σ
        (orbitY_mem_graphFixedNegUnipotent t σ a c)
  · have hρ : ∀ i, ρ' i = rankOneHom t K i := fun i => SL2_hom_ext
      (fun s => by rw [hu, rankOneHom_uSL]) (fun u => by rw [hH, rankOneHom_HSL])
      (by rw [hW, rankOneHom_WSL])
    simp only [hρ]
    rfl

end CFSG.LieType.Chevalley

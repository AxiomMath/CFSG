module

public import CFSG.Fischer.Classification.PartIII.U.SixAdm
public import CFSG.Fischer.Classification.PartIII.U.Points117
public import CFSG.Fischer.Classification.SRG.Pair

public section

namespace CFSG.Fischer.Classification.LocalU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification LocalR3 F3

theorem normOneCompl_restrict_six_two {v : Fin 6 → ZMod 3} (hv : diagF3 6 2 v v = 1)
    {f' : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)} (hf' : IsF3Form f')
    (e : perpOne (diagF3 6 2) v ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (he : ∀ a b : perpOne (diagF3 6 2) v, f' (e a) (e b) = diagF3 6 2 a b) : NormOneCompl f' := by
  obtain ⟨e', he'⟩ := exists_isometry_restrict_diagF3 (n := 5) (by norm_num) (δ := 2)
    (by decide) hv hf' e he
  exact NormOneCompl.of_isometry e' he' normOneCompl_diagF3_five_two

theorem ncard_localClass_six_two {w : Fin 6 → ZMod 3} (hw : diagF3 6 2 w w = 1) :
    (LocalClass (D3 (diagF3 6 2)) (reflBar (diagF3 6 2) w)).ncard = 36 := by
  have hf : IsF3Form (diagF3 6 2) := isF3Form_diagF3 (by decide)
  obtain ⟨f', Ψ, e, hf', he, hΨ, -, -, -⟩ := exists_starChart_six hf hw
  obtain ⟨e', he'⟩ := exists_isometry_restrict_diagF3 (n := 5) (by norm_num) (δ := 2)
    (by decide) hw hf' e he
  have h1 : (D3 f').ncard = 36 := (ncard_D3_of_isometry e' he').trans ncard_D3_diagF3_five_two
  rw [← hΨ.image_eq, hΨ.injOn.ncard_image] at h1
  exact h1

@[expose] def rep12 : Fin 12 → Fin 4 → ZMod 3 :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 1, 1, 1], ![1, 1, 1, 2],
    ![1, 1, 2, 1], ![1, 1, 2, 2], ![1, 2, 1, 1], ![1, 2, 1, 2], ![1, 2, 2, 1], ![1, 2, 2, 2]]

theorem exists_rep12 : ∀ a b c d : ZMod 3, a * a + b * b + c * c + d * d = 1 →
    ∃ i : Fin 12, rep12 i = ![a, b, c, d] ∨ rep12 i = -![a, b, c, d] := by
  decide +kernel

theorem ncard_sPt_le_six_two {z₀ : Fin 6 → ZMod 3} (hz₀0 : z₀ ≠ 0)
    (hz₀ : diagF3 6 2 z₀ z₀ = 0) : (sPt (diagF3 6 2) z₀).ncard ≤ 36 := by
  have hf : IsF3Form (diagF3 6 2) := isF3Form_diagF3 (by decide)
  set f := diagF3 6 2 with hfdef
  have hsymm : ∀ {a b : Fin 6 → ZMod 3}, f a b = 0 → f b a = 0 := fun h => by
    rw [hf.symm]; exact h
  obtain ⟨y, hyy, hz₀y, -⟩ := exists_hyp_partner_of_dual hf (k := 0) (b := Fin.elim0)
    (b' := Fin.elim0) (fun i => i.elim0) (fun _ _ i => i.elim0) hz₀0 hz₀ (fun i => i.elim0)
  have hyz₀ : f y z₀ = 1 := by rw [hf.symm]; exact hz₀y
  obtain ⟨w₀, hw₀, hw₀b⟩ := exists_norm_perp_of_dual hf (k := 2) (by norm_num)
    (b := ![z₀, y]) (b' := ![y, z₀])
    (fun i j => by fin_cases i <;> fin_cases j <;> simp [hz₀, hyy, hz₀y, hyz₀])
    (fun x hx i => by
      have h0 : f x y = 0 := hx 0
      have h1 : f x z₀ = 0 := hx 1
      fin_cases i <;> simp [h0, h1]) one_ne_zero
  have hw₀y : f w₀ y = 0 := hw₀b 0
  have hw₀z₀ : f w₀ z₀ = 0 := hw₀b 1
  obtain ⟨u₁, hu₁, hu₁b⟩ := exists_norm_perp_of_dual hf (k := 3) (by norm_num)
    (b := ![w₀, z₀, y]) (b' := ![w₀, y, z₀])
    (fun i j => by
      fin_cases i <;> fin_cases j <;>
        simp [hw₀, hz₀, hyy, hz₀y, hyz₀, hw₀y, hw₀z₀, hsymm hw₀y, hsymm hw₀z₀])
    (fun x hx i => by
      have h0 : f x w₀ = 0 := hx 0
      have h1 : f x y = 0 := hx 1
      have h2 : f x z₀ = 0 := hx 2
      fin_cases i <;> simp [h0, h1, h2]) one_ne_zero
  have hu₁w₀ : f u₁ w₀ = 0 := hu₁b 0
  have hu₁y : f u₁ y = 0 := hu₁b 1
  have hu₁z₀ : f u₁ z₀ = 0 := hu₁b 2
  obtain ⟨u₂, hu₂, hu₂b⟩ := exists_norm_perp_of_dual hf (k := 4) (by norm_num)
    (b := ![w₀, u₁, z₀, y]) (b' := ![w₀, u₁, y, z₀])
    (fun i j => by
      fin_cases i <;> fin_cases j <;>
        simp [hw₀, hu₁, hz₀, hyy, hz₀y, hyz₀, hw₀y, hw₀z₀, hu₁w₀, hu₁y, hu₁z₀, hsymm hw₀y,
          hsymm hw₀z₀, hsymm hu₁w₀, hsymm hu₁y, hsymm hu₁z₀])
    (fun x hx i => by
      have h0 : f x w₀ = 0 := hx 0
      have h1 : f x u₁ = 0 := hx 1
      have h2 : f x y = 0 := hx 2
      have h3 : f x z₀ = 0 := hx 3
      fin_cases i <;> simp [h0, h1, h2, h3]) one_ne_zero
  have hu₂w₀ : f u₂ w₀ = 0 := hu₂b 0
  have hu₂u₁ : f u₂ u₁ = 0 := hu₂b 1
  have hu₂z₀ : f u₂ z₀ = 0 := hu₂b 3
  obtain ⟨u₃, hu₃, hu₃w₀, hu₃u₁, hu₃u₂, hu₃z₀⟩ := normOneCompl₃_diagF3_six_two hw₀ hu₁ hu₂
    (hsymm hu₁w₀) (hsymm hu₂w₀) (hsymm hu₂u₁) hz₀0 hz₀ (hsymm hw₀z₀) (hsymm hu₁z₀)
    (hsymm hu₂z₀)
  rw [← hfdef] at hu₃ hu₃w₀ hu₃u₁ hu₃u₂ hu₃z₀
  obtain ⟨y', hy'y', hz₀y', hy'b⟩ := exists_hyp_partner_perp hf (u := ![w₀, u₁, u₂, u₃])
    (fun i j => by
      fin_cases i <;> fin_cases j <;>
        simp [hw₀, hu₁, hu₂, hu₃, hu₁w₀, hu₂w₀, hu₂u₁, hu₃w₀, hu₃u₁, hu₃u₂, hsymm hu₁w₀,
          hsymm hu₂w₀, hsymm hu₂u₁, hsymm hu₃w₀, hsymm hu₃u₁, hsymm hu₃u₂])
    hz₀0 hz₀ (fun i => by
      fin_cases i <;> simp [hsymm hw₀z₀, hsymm hu₁z₀, hsymm hu₂z₀, hsymm hu₃z₀])
  have hy'w₀ : f y' w₀ = 0 := hy'b 0
  have hy'u₁ : f y' u₁ = 0 := hy'b 1
  have hy'u₂ : f y' u₂ = 0 := hy'b 2
  have hy'u₃ : f y' u₃ = 0 := hy'b 3
  have hy'z₀ : f y' z₀ = 1 := by rw [hf.symm]; exact hz₀y'
  have key : ∀ v, v = f v w₀ • w₀ + f v u₁ • u₁ + f v u₂ • u₂ + f v u₃ • u₃ + f v y' • z₀ +
      f v z₀ • y' := fun v => by
    have h := eq_sum_of_dual hf (b := ![w₀, u₁, u₂, u₃, z₀, y'])
      (b' := ![w₀, u₁, u₂, u₃, y', z₀])
      (fun i j => by
        fin_cases i <;> fin_cases j <;>
          simp [hw₀, hu₁, hu₂, hu₃, hz₀, hy'y', hz₀y', hy'z₀, hu₁w₀, hu₂w₀, hu₂u₁, hu₃w₀,
            hu₃u₁, hu₃u₂, hy'w₀, hy'u₁, hy'u₂, hy'u₃, hw₀z₀, hu₁z₀, hu₂z₀, hu₃z₀, hsymm hu₁w₀,
            hsymm hu₂w₀, hsymm hu₂u₁, hsymm hu₃w₀, hsymm hu₃u₁, hsymm hu₃u₂, hsymm hy'w₀,
            hsymm hy'u₁, hsymm hy'u₂, hsymm hy'u₃, hsymm hw₀z₀, hsymm hu₁z₀, hsymm hu₂z₀,
            hsymm hu₃z₀]) v
    rw [Fin.sum_univ_six] at h
    exact h
  set comb : (Fin 4 → ZMod 3) → Fin 6 → ZMod 3 := fun a =>
    a 0 • w₀ + a 1 • u₁ + a 2 • u₂ + a 3 • u₃ with hcomb
  have hsub : sPt f z₀ ⊆ Set.range (fun p : Fin 12 × ZMod 3 =>
      reflBar f (comb (rep12 p.1) + p.2 • z₀)) := by
    rintro _ ⟨v, hv, hvz, rfl⟩
    have hk := key v
    rw [hvz, zero_smul, add_zero] at hk
    generalize f v w₀ = a₀, f v u₁ = a₁, f v u₂ = a₂, f v u₃ = a₃, f v y' = c at hk
    subst hk
    have hn : a₀ * a₀ + a₁ * a₁ + a₂ * a₂ + a₃ * a₃ = 1 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hw₀, hu₁, hu₂, hu₃, hz₀, hu₁w₀, hu₂w₀, hu₂u₁, hu₃w₀, hu₃u₁, hu₃u₂, hw₀z₀, hu₁z₀,
        hu₂z₀, hu₃z₀, hsymm hu₁w₀, hsymm hu₂w₀, hsymm hu₂u₁, hsymm hu₃w₀, hsymm hu₃u₁,
        hsymm hu₃u₂, hsymm hw₀z₀, hsymm hu₁z₀, hsymm hu₂z₀, hsymm hu₃z₀] at hv
      linear_combination hv
    obtain ⟨i, h | h⟩ := exists_rep12 a₀ a₁ a₂ a₃ hn
    · refine ⟨(i, c), ?_⟩
      show reflBar f (comb (rep12 i) + c • z₀) = _
      rw [h]
      rfl
    · refine ⟨(i, -c), ?_⟩
      show reflBar f (comb (rep12 i) + (-c) • z₀) = _
      rw [h, ← reflBar_neg]
      congr 1
      simp only [hcomb, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      module
  calc (sPt f z₀).ncard ≤ (Set.range (fun p : Fin 12 × ZMod 3 =>
        reflBar f (comb (rep12 p.1) + p.2 • z₀))).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_range _)
    _ ≤ (Set.univ : Set (Fin 12 × ZMod 3)).ncard := by
        rw [← Set.image_univ]
        exact Set.ncard_image_le Set.finite_univ
    _ = 36 := by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
          ZMod.card]

theorem not_isSquare_of_bound {N B : ℕ} (hB : N < B * B) (h : ∀ r < B, r * r ≠ N) :
    ¬ IsSquare (N : ℤ) := by
  rintro ⟨r, hr⟩
  have h1 : r.natAbs * r.natAbs = N := by
    have := congrArg Int.natAbs hr
    rw [Int.natAbs_mul, Int.natAbs_natCast] at this
    exact this.symm
  by_cases hr' : r.natAbs < B
  · exact h _ hr' h1
  · have : B * B ≤ r.natAbs * r.natAbs := Nat.mul_le_mul (not_lt.1 hr') (not_lt.1 hr')
    omega

theorem disc_117 : ∀ μ < 36, 0 < μ → μ ≠ 22 → μ ≠ 27 →
    ∀ r < 43, r * r ≠ (36 - μ) * (36 - μ) + 4 * (117 - μ) := by
  decide

theorem le_ncard_muSet_of_params_117 {X : Type} [Group X] {E : Set X} (hH : Hyp X E)
    (hna : NonabelianCommutator X) {d e x : X} (hd : d ∈ E) (he : e ∈ LocalClass E d)
    (hx : x ∈ E) (hxd : x * d ≠ d * x) (hk : (LocalClass E d).ncard = 117)
    (hℓ : (LocalClass E d ∩ LocalClass E e).ncard = 36) (hμ : 0 < (muSet E d x).ncard) :
    36 ≤ (muSet E d x).ncard := by
  by_contra hlt
  rw [not_le] at hlt
  have hfin := Pair.finite hH.pair
  have hE : 0 < E.ncard := (Set.ncard_pos (Set.toFinite E)).2 ⟨d, hd⟩
  by_cases h22 : (muSet E d x).ncard = 22 ∨ (muSet E d x).ncard = 27
  · classical
    have : Fintype E := Fintype.ofFinite E
    have hpar := (Pair.isSRGWith_commGraph hH hna hd he hx hxd).param_eq _ hE
    rw [hk, hℓ] at hpar
    rcases h22 with h | h <;> rw [h] at hpar <;> omega
  · rw [not_or] at h22
    have hsq : ¬ IsSquare ((((36 : ℕ) : ℤ) - ((muSet E d x).ncard : ℤ)) ^ 2 +
        4 * (((117 : ℕ) : ℤ) - ((muSet E d x).ncard : ℤ))) := by
      have hcast : (((36 : ℕ) : ℤ) - ((muSet E d x).ncard : ℤ)) ^ 2 +
          4 * (((117 : ℕ) : ℤ) - ((muSet E d x).ncard : ℤ)) =
          (((36 - (muSet E d x).ncard) * (36 - (muSet E d x).ncard) +
            4 * (117 - (muSet E d x).ncard) : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hlt.le, Nat.cast_sub (by omega : (muSet E d x).ncard ≤ 117)]
        ring
      rw [hcast]
      refine not_isSquare_of_bound (B := 43) ?_ (disc_117 _ hlt hμ h22.1 h22.2)
      have : 36 - (muSet E d x).ncard ≤ 35 := by omega
      have : 117 - (muSet E d x).ncard ≤ 116 := by omega
      nlinarith
    obtain ⟨-, h2⟩ := Pair.even_and_conference_of_not_isSquare hH hna hd he hx hxd hk hℓ rfl hsq
    have h1 : (1 : ℤ) ≤ E.ncard := by exact_mod_cast hE
    have h3 : (0 : ℤ) < ((36 : ℕ) : ℤ) - ((muSet E d x).ncard : ℤ) := by
      have : ((muSet E d x).ncard : ℤ) < 36 := by exact_mod_cast hlt
      push_cast
      linarith
    have h4 : (0 : ℤ) ≤ ((E.ncard : ℤ) - 1) * (((36 : ℕ) : ℤ) - ((muSet E d x).ncard : ℤ)) :=
      mul_nonneg (by linarith) h3.le
    push_cast at h2 h4
    linarith

end CFSG.Fischer.Classification.LocalU

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer LocalR3 F3 LocalU

theorem classicalConclusion_of_localR3_diagF3_six_two {G : Type} [Group G] {D : Set G}
    (hH : Hyp G D) (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D)
    (φ : LocalQuotient D d ≃* R3 (diagF3 6 2)) (hφ : φ '' LocalImages D d = D3 (diagF3 6 2)) :
    ClassicalConclusion G D := by
  have hf : IsF3Form (diagF3 6 2) := isF3Form_diagF3 (by decide)
  have hH' := hH
  obtain ⟨hP, hZ, hS⟩ := hH'
  have hna : ∃ a b : commutator G, a * b ≠ b * a := hnab
  obtain ⟨x, hx, hxd⟩ : ∃ x ∈ D, x * d ≠ d * x := by
    by_contra! h
    have hdZ : d ∈ Subgroup.center G := (Pair.mem_center_iff hP).2 h
    rw [hZ, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  have hι := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd)
    φ hφ
  have hadm := isAdm_image_muSet_six hP hZ hS hd hf (Good := NormOneCompl)
    (fun v hv f' hf' e he => normOneCompl_restrict_six_two hv hf' e he) comparison_normOneCompl
    φ hφ hx hxd
  obtain ⟨f₀, hf₀⟩ := Pair.muSet_nonempty hP (Pair.connected_of_nonabelian hP hS hna) hd hx hxd
  obtain ⟨w₀, hw₀, hwg⟩ := mem_D3_iff.1 (hι.mem hf₀.1)
  have hg₀ : reflBar (diagF3 6 2) w₀ ∈ (φ ∘ lqMap D d) '' muSet D d x := by
    rw [hwg]
    exact ⟨f₀, hf₀, rfl⟩
  obtain ⟨z₀, hz₀, hS₀⟩ := exists_isIsoPt_of_isAdm hf (by norm_num) hadm hw₀ hg₀
  have hsub := subset_sPt_of_isAdm hf (by norm_num) hadm hw₀ hg₀ hz₀ hS₀
  have hk : (LocalClass D d).ncard = 117 := by
    rw [← hι.injOn.ncard_image, hι.image_eq, ncard_D3_diagF3_six_two]
  have hℓ : (LocalClass D d ∩ LocalClass D f₀).ncard = 36 := by
    rw [← localClass_localClass_eq_inter,
      ← (hι.injOn.mono (localClass_subset _ _)).ncard_image, hι.image_localClass hf₀.1, ← hwg,
      ncard_localClass_six_two hw₀]
  have hμ : (muSet D d x).ncard = ((φ ∘ lqMap D d) '' muSet D d x).ncard :=
    ((hι.injOn.mono (muSet_subset_localClass d x)).ncard_image).symm
  have h36 := le_ncard_muSet_of_params_117 hH hnab hd hf₀.1 hx hxd hk hℓ (by
    rw [hμ]
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨_, hg₀⟩)
  have hle := ncard_sPt_le_six_two hz₀.1 hz₀.2.1
  have hM : (φ ∘ lqMap D d) '' muSet D d x = sPt (diagF3 6 2) z₀ :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  refine classicalConclusion_of_localR3_of_muSet hH hnab hd (by norm_num) hf φ hφ hx hxd hz₀.1
    hz₀.2.1 ?_
  rw [← hM, Set.image_comp, lqMap_image (muSet_subset_localClass d x)]

end CFSG.Fischer.Classification

module

public import CFSG.LieType.Chevalley.E6SignedGraphRankOneGroups

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]

theorem height_rho
    (v : E6Vec) : height (rho v) = height v :=
  height_permLattice _ _

theorem height_orbitVec_diagramOrbit
    (α : E6Vec) :
    height (orbitVec (TwistTag.E6.diagramOrbit α)) = 2 * height α := by
  rw [orbitVec_diagramOrbit, vecOf]
  split_ifs
  · rw [two_nsmul, height_add]
    ring
  · rw [height_add, height_rho]
    ring

theorem diagramOrbit_subset_pos_iff
    {α : E6Vec} (hα : IsRoot TwistTag.E6.tag α) :
    (TwistTag.E6.diagramOrbit α : Set E6Vec) ⊆ {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β} ↔
      0 < height α := by
  refine ⟨fun h => (h (TwistTag.E6.self_mem_diagramOrbit α)).2, fun h β hβ => ?_⟩
  have hβ' : β ∈ TwistTag.E6.diagramOrbit α := hβ
  refine ⟨TwistTag.E6.isRoot_of_mem_diagramOrbit hα hβ', ?_⟩
  rw [TwistTag.E6.height_of_mem_diagramOrbit hβ']
  exact h

theorem diagramOrbit_subset_neg_iff
    {α : E6Vec} (hα : IsRoot TwistTag.E6.tag α) :
    (TwistTag.E6.diagramOrbit α : Set E6Vec) ⊆ {β | IsRoot TwistTag.E6.tag β ∧ height β < 0} ↔
      height α < 0 := by
  refine ⟨fun h => (h (TwistTag.E6.self_mem_diagramOrbit α)).2, fun h β hβ => ?_⟩
  have hβ' : β ∈ TwistTag.E6.diagramOrbit α := hβ
  refine ⟨TwistTag.E6.isRoot_of_mem_diagramOrbit hα hβ', ?_⟩
  rw [TwistTag.E6.height_of_mem_diagramOrbit hβ']
  exact h

theorem height_orbitVec_pos_iff
    {O : Finset E6Vec} (hO : O ∈ orbits) :
    0 < height (orbitVec O) ↔
      (O : Set E6Vec) ⊆ {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β} := by
  obtain ⟨⟨α, hα, rfl⟩, -⟩ := hO
  rw [height_orbitVec_diagramOrbit, diagramOrbit_subset_pos_iff hα]
  omega

theorem height_orbitVec_neg_iff
    {O : Finset E6Vec} (hO : O ∈ orbits) :
    height (orbitVec O) < 0 ↔
      (O : Set E6Vec) ⊆ {β | IsRoot TwistTag.E6.tag β ∧ height β < 0} := by
  obtain ⟨⟨α, hα, rfl⟩, -⟩ := hO
  rw [height_orbitVec_diagramOrbit, diagramOrbit_subset_neg_iff hα]
  omega

theorem diagramRootOrbits_sign
    {O : Finset E6Vec} (hO : O ∈ TwistTag.E6.diagramRootOrbits) :
    (∀ α ∈ O, IsRoot TwistTag.E6.tag α ∧ 0 < height α) ∨
      ∀ α ∈ O, IsRoot TwistTag.E6.tag α ∧ height α < 0 := by
  obtain ⟨α, hα, rfl⟩ := hO
  rcases IsRoot.height_pos_or_neg hα with h | h
  · exact Or.inl fun β hβ => (diagramOrbit_subset_pos_iff hα).2 h hβ
  · exact Or.inr fun β hβ => (diagramOrbit_subset_neg_iff hα).2 h hβ

theorem orbitImage_sign
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    (∀ α ∈ orbitImage w a, IsRoot TwistTag.E6.tag α ∧ 0 < height α) ∨
      ∀ α ∈ orbitImage w a, IsRoot TwistTag.E6.tag α ∧ height α < 0 := by
  have key : ∀ α ∈ orbitImage w a, IsRoot TwistTag.E6.tag α ∧
      height α = height (w • (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec)) := by
    intro α hα
    rcases orbit_pair_or_single a with ⟨-, ho, -⟩ | ⟨-, ho, -⟩
    · rw [orbitImage_pair ho, Finset.mem_insert, Finset.mem_singleton] at hα
      rcases hα with rfl | rfl
      · exact ⟨IsRoot.smul (isRoot_single _ _) w, rfl⟩
      · exact ⟨IsRoot.smul (isRoot_single _ _) w, by
          rw [smul_single_perm_eq_rho hw, height_rho]⟩
    · rw [orbitImage_single ho, Finset.mem_singleton] at hα
      subst hα
      exact ⟨IsRoot.smul (isRoot_single _ _) w, rfl⟩
  rcases IsRoot.height_pos_or_neg
      (IsRoot.smul (isRoot_single TwistTag.E6.tag (TwistTag.E6.orbitMin a)) w) with h | h
  · refine Or.inl fun α hα => ⟨(key α hα).1, ?_⟩
    rw [(key α hα).2]
    exact h
  · refine Or.inr fun α hα => ⟨(key α hα).1, ?_⟩
    rw [(key α hα).2]
    exact h

theorem neg_orbitImage_sign
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    (∀ α ∈ (orbitImage w a).image (fun α => -α), IsRoot TwistTag.E6.tag α ∧ 0 < height α) ∨
      ∀ α ∈ (orbitImage w a).image (fun α => -α), IsRoot TwistTag.E6.tag α ∧ height α < 0 := by
  rcases orbitImage_sign hw a with h | h
  · refine Or.inr fun α hα => ?_
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hα
    refine ⟨IsRoot.neg (h β hβ).1, ?_⟩
    rw [height_neg]
    linarith [(h β hβ).2]
  · refine Or.inl fun α hα => ?_
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hα
    refine ⟨IsRoot.neg (h β hβ).1, ?_⟩
    rw [height_neg]
    linarith [(h β hβ).2]

theorem twistA_conj_mem_rootSpan
    {O : Finset E6Vec} (hO : O ∈ TwistTag.E6.diagramRootOrbits)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ rootSpan TwistTag.E6.tag K (O : Set E6Vec)) :
    twistA K * x * (twistA K)⁻¹ ∈ rootSpan TwistTag.E6.tag K (O : Set E6Vec) := by
  obtain ⟨α, hα, rfl⟩ := hO
  obtain ⟨w, hw, a, he⟩ := TwistTag.E6.exists_diagramOrbit_eq hα
  have he' : TwistTag.E6.diagramOrbit α = orbitImage w a := he
  rw [he', rootSpan_orbitImage] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  have hgen : ∀ k ∈ TwistTag.E6.orbit a, ∀ d : K,
      xUnit TwistTag.E6.tag K k d ∈ rootSpan TwistTag.E6.tag K (simpleSet a) := fun k hk d => by
    rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan (S := simpleSet a) ⟨k, hk, rfl⟩ d
  have hi := TwistTag.E6.orbitMin_mem a
  have hj := TwistTag.E6.perm_mem_orbit hi
  have hjj := TwistTag.E6.perm_mem_orbit hj
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rcases orbit_pair_or_single a with ⟨-, -, hword⟩ | ⟨-, -, hword⟩
  · obtain ⟨c, d, rfl⟩ := exists_eq_pair hword hy
    rw [conj_conj_mul, twistA_conj_canonicalRep_xUnit hw, twistA_conj_canonicalRep_xUnit hw,
      ← conj_mul]
    exact ⟨_, mul_mem (hgen _ hj _) (hgen _ hjj _), rfl⟩
  · obtain ⟨c, rfl⟩ := exists_eq_single hword hy
    rw [twistA_conj_canonicalRep_xUnit hw]
    exact ⟨_, hgen _ hj _, rfl⟩

theorem conj_ofFn_prod {G : Type*} [Group G] (p : G) {k : ℕ} (v : Fin k → G) :
    p * (List.ofFn v).prod * p⁻¹ = (List.ofFn fun j => p * v j * p⁻¹).prod := by
  have h := map_list_prod (MulAut.conj p).toMonoidHom (List.ofFn v)
  rw [List.map_ofFn] at h
  exact h

theorem grouped_pos
    {k : ℕ} (F : Fin k → Finset E6Vec) (hF : Function.Injective F)
    (hrange : ∀ P, P ∈ Set.range F ↔ P ∈ TwistTag.E6.diagramRootOrbits ∧
      (P : Set E6Vec) ⊆ {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α}) :
    (∀ u u' : Fin k → ModGL TwistTag.E6.tag K,
      (∀ j, u j ∈ rootSpan TwistTag.E6.tag K (F j : Set E6Vec)) →
      (∀ j, u' j ∈ rootSpan TwistTag.E6.tag K (F j : Set E6Vec)) →
      (List.ofFn u).prod = (List.ofFn u').prod → u = u') ∧
    ∀ g ∈ posUnipotent TwistTag.E6.tag K, ∃ u : Fin k → ModGL TwistTag.E6.tag K,
      (∀ j, u j ∈ rootSpan TwistTag.E6.tag K (F j : Set E6Vec)) ∧ (List.ofFn u).prod = g := by
  have hFj : ∀ j, F j ∈ TwistTag.E6.diagramRootOrbits ∧
      (F j : Set E6Vec) ⊆ {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α} :=
    fun j => (hrange (F j)).1 ⟨j, rfl⟩
  have hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j) := fun i j hij => by
    obtain ⟨⟨α, -, hα⟩, -⟩ := hFj i
    obtain ⟨⟨β, -, hβ⟩, -⟩ := hFj j
    rw [← hα, ← hβ]
    exact TwistTag.E6.disjoint_diagramOrbit (by rw [hα, hβ]; exact hF.ne hij)
  have hpos : ∀ j, ∀ α ∈ F j, IsRoot TwistTag.E6.tag α ∧ 0 < height α :=
    fun j α hα => (hFj j).2 hα
  have hcl : ∀ j, ∀ α ∈ F j, ∀ β ∈ F j, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ¬IsRoot TwistTag.E6.tag (a • α + b • β) := fun j α hα β hβ a b ha hb => by
    obtain ⟨⟨γ, hγ, hγO⟩, -⟩ := hFj j
    rw [← hγO] at hα hβ
    exact TwistTag.E6.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit hγ hα hβ ha hb
  have hS : ∀ α ∈ {α : E6Vec | IsRoot TwistTag.E6.tag α ∧ 0 < height α},
      IsRoot TwistTag.E6.tag α ∧ 0 < height α := fun α hα => hα
  have hclosed : ∀ α ∈ {α : E6Vec | IsRoot TwistTag.E6.tag α ∧ 0 < height α},
      ∀ β ∈ {α : E6Vec | IsRoot TwistTag.E6.tag α ∧ 0 < height α}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot TwistTag.E6.tag (a • α + b • β) →
          a • α + b • β ∈ {α : E6Vec | IsRoot TwistTag.E6.tag α ∧ 0 < height α} :=
    fun α hα β hβ a b ha hb hr => by
      refine ⟨hr, ?_⟩
      rw [height_nsmul_add_nsmul]
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith [hα.2, hβ.2]
  have hSO : ∀ α, α ∈ {α : E6Vec | IsRoot TwistTag.E6.tag α ∧ 0 < height α} ↔ ∃ j, α ∈ F j :=
    fun α => by
      refine ⟨fun hα => ?_, fun ⟨j, hj⟩ => hpos j α hj⟩
      obtain ⟨j, hj⟩ := (hrange (TwistTag.E6.diagramOrbit α)).2
        ⟨⟨α, hα.1, rfl⟩, (diagramOrbit_subset_pos_iff hα.1).2 hα.2⟩
      exact ⟨j, hj ▸ TwistTag.E6.self_mem_diagramOrbit α⟩
  exact ⟨fun u u' hu hu' h => eq_of_prod_rootSpan_eq hdisj hpos hcl hu hu' h,
    fun g hg => exists_prod_rootSpan_eq hdisj hS hclosed hSO hg⟩

theorem grouped_neg
    {k : ℕ} (F : Fin k → Finset E6Vec) (hF : Function.Injective F)
    (hrange : ∀ P, P ∈ Set.range F ↔ P ∈ TwistTag.E6.diagramRootOrbits ∧
      (P : Set E6Vec) ⊆ {α | IsRoot TwistTag.E6.tag α ∧ height α < 0}) :
    (∀ u u' : Fin k → ModGL TwistTag.E6.tag K,
      (∀ j, u j ∈ rootSpan TwistTag.E6.tag K (F j : Set E6Vec)) →
      (∀ j, u' j ∈ rootSpan TwistTag.E6.tag K (F j : Set E6Vec)) →
      (List.ofFn u).prod = (List.ofFn u').prod → u = u') ∧
    ∀ g ∈ negUnipotent TwistTag.E6.tag K, ∃ u : Fin k → ModGL TwistTag.E6.tag K,
      (∀ j, u j ∈ rootSpan TwistTag.E6.tag K (F j : Set E6Vec)) ∧ (List.ofFn u).prod = g := by
  obtain ⟨w₀, hw₀, h₀⟩ := TwistTag.E6.exists_reversesSigns_mem_relWeylTwist
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀
  have himg := image_smul_posRoots_of_reversesSigns h₀
  set F' : Fin k → Finset E6Vec := fun j => (F j).image fun α => w₀⁻¹ • α with hF'def
  have hFw : ∀ j, (F' j).image (fun α => w₀ • α) = F j := fun j => by
    rw [hF'def, Finset.image_image]
    simp [Function.comp_def]
  have hF' : Function.Injective F' := fun i j h => hF (by rw [← hFw i, ← hFw j, h])
  have hFj : ∀ j, F j ∈ TwistTag.E6.diagramRootOrbits ∧
      (F j : Set E6Vec) ⊆ {α | IsRoot TwistTag.E6.tag α ∧ height α < 0} :=
    fun j => (hrange (F j)).1 ⟨j, rfl⟩
  have hpos' : ∀ γ, IsRoot TwistTag.E6.tag γ ∧ height γ < 0 →
      IsRoot TwistTag.E6.tag (w₀⁻¹ • γ) ∧ 0 < height (w₀⁻¹ • γ) := fun γ hγ => by
    have hγ' : γ ∈ {α | IsRoot TwistTag.E6.tag α ∧ height α < 0} := hγ
    rw [← himg] at hγ'
    obtain ⟨β, hβ, rfl⟩ := hγ'
    rwa [inv_smul_smul]
  have hrange' : ∀ P, P ∈ Set.range F' ↔ P ∈ TwistTag.E6.diagramRootOrbits ∧
      (P : Set E6Vec) ⊆ {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α} := fun P => by
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨⟨γ, hγ, hγF⟩, hsub⟩ := hFj j
      refine ⟨⟨w₀⁻¹ • γ, IsRoot.smul hγ w₀⁻¹, ?_⟩, fun β hβ => ?_⟩
      · rw [TwistTag.E6.diagramOrbit_smul (inv_mem hw₀), hγF]
      · obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hβ
        exact hpos' δ (hsub hδ)
    · rintro ⟨⟨α, hα, rfl⟩, hsub⟩
      have hαp : 0 < height α := (diagramOrbit_subset_pos_iff hα).1 hsub
      have hneg : height (w₀ • α) < 0 := by
        have : w₀ • α ∈ (fun α => w₀ • α) '' {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α} :=
          ⟨α, ⟨hα, hαp⟩, rfl⟩
        rw [himg] at this
        exact this.2
      obtain ⟨j, hj⟩ := (hrange (TwistTag.E6.diagramOrbit (w₀ • α))).2
        ⟨⟨w₀ • α, IsRoot.smul hα w₀, rfl⟩,
          (diagramOrbit_subset_neg_iff (IsRoot.smul hα w₀)).2 hneg⟩
      refine ⟨j, ?_⟩
      rw [hF'def]
      simp only
      rw [hj, TwistTag.E6.diagramOrbit_smul hw₀, Finset.image_image]
      simp [Function.comp_def]
  obtain ⟨hinj, hsurj⟩ := grouped_pos (K := K) F' hF' hrange'
  have hmapj : ∀ j, (rootSpan TwistTag.E6.tag K (F' j : Set E6Vec)).map
      (MulAut.conj n).toMonoidHom = rootSpan TwistTag.E6.tag K (F j : Set E6Vec) := fun j => by
    have hroots : ∀ α ∈ (F' j : Set E6Vec), IsRoot TwistTag.E6.tag α := fun α hα =>
      ((hrange' (F' j)).1 ⟨j, rfl⟩).2 hα |>.1
    rw [(canonical_weyl_root_transport TwistTag.E6.tag K).1 w₀ _ hroots, ← Finset.coe_image,
      hFw]
  have hback : ∀ (v : Fin k → ModGL TwistTag.E6.tag K),
      (∀ j, v j ∈ rootSpan TwistTag.E6.tag K (F j : Set E6Vec)) →
        ∀ j, n⁻¹ * v j * n ∈ rootSpan TwistTag.E6.tag K (F' j : Set E6Vec) := fun v hv j => by
    have h := hv j
    rw [← hmapj j] at h
    obtain ⟨y, hy, hyx⟩ := h
    rw [← hyx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show n⁻¹ * (n * y * n⁻¹) * n = y by group]
    exact hy
  have hprod : ∀ v : Fin k → ModGL TwistTag.E6.tag K,
      (List.ofFn fun j => n⁻¹ * v j * n).prod = n⁻¹ * (List.ofFn v).prod * n := fun v => by
    have h := conj_ofFn_prod n⁻¹ v
    rw [inv_inv] at h
    exact h.symm
  refine ⟨fun u u' hu hu' h => ?_, fun g hg => ?_⟩
  · have h' := hinj _ _ (hback u hu) (hback u' hu') (by rw [hprod, hprod, h])
    funext j
    exact mul_left_cancel (mul_right_cancel (congrFun h' j))
  · have hneg : (posUnipotent TwistTag.E6.tag K).map (MulAut.conj n).toMonoidHom =
        negUnipotent TwistTag.E6.tag K := by
      have h := (canonical_weyl_root_transport TwistTag.E6.tag K).1 w₀
        {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α} fun α hα => hα.1
      rw [himg] at h
      exact h
    rw [← hneg] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    obtain ⟨v, hv, rfl⟩ := hsurj y hy
    refine ⟨fun j => n * v j * n⁻¹, fun j => ?_, ?_⟩
    · rw [← hmapj j]
      exact ⟨v j, hv j, rfl⟩
    · rw [← conj_ofFn_prod]
      rfl

theorem fixed_list_prod {m e : ℕ} (V : Fin (m + e) → Subgroup (ModGL TwistTag.E6.tag K))
    (R : Fin m → Subgroup (ModGL TwistTag.E6.tag K)) (hR : ∀ i, V (Fin.castAdd e i) = R i)
    (U : Subgroup (ModGL TwistTag.E6.tag K))
    (hadj : ∀ j, V j ≤ adjointGroup TwistTag.E6.tag K)
    (hA : ∀ j, ∀ x ∈ V j, twistA K * x * (twistA K)⁻¹ ∈ V j) (hU : ∀ j, V j ≤ U)
    (hexcl : ∀ j : Fin e, V (Fin.natAdd m j) ⊓ fixedGroup K = ⊥)
    (hinj : ∀ u u' : Fin (m + e) → ModGL TwistTag.E6.tag K, (∀ j, u j ∈ V j) →
      (∀ j, u' j ∈ V j) → (List.ofFn u).prod = (List.ofFn u').prod → u = u')
    (hsurj : ∀ g ∈ U, ∃ u : Fin (m + e) → ModGL TwistTag.E6.tag K, (∀ j, u j ∈ V j) ∧
      (List.ofFn u).prod = g) :
    Function.Injective (fun g : (i : Fin m) → ↥(R i ⊓ fixedGroup K) =>
        (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) ∧
      Set.range (fun g : (i : Fin m) → ↥(R i ⊓ fixedGroup K) =>
        (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) =
        ((U ⊓ fixedGroup K : Subgroup (ModGL TwistTag.E6.tag K)) :
          Set (ModGL TwistTag.E6.tag K)) := by
  have hsplit : ∀ u : Fin (m + e) → ModGL TwistTag.E6.tag K, (List.ofFn u).prod =
      (List.ofFn fun i => u (Fin.castAdd e i)).prod *
        (List.ofFn fun j => u (Fin.natAdd m j)).prod := by
    intro u
    conv_lhs => rw [← Fin.append_castAdd_natAdd (f := u)]
    rw [List.ofFn_fin_append, List.prod_append]
  have hext : ∀ g : (i : Fin m) → ↥(R i ⊓ fixedGroup K),
      (∀ j, Fin.append (fun i => (g i : ModGL TwistTag.E6.tag K)) (fun _ : Fin e => 1) j ∈ V j) ∧
      (List.ofFn (Fin.append (fun i => (g i : ModGL TwistTag.E6.tag K))
        (fun _ : Fin e => 1))).prod =
          (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod := by
    intro g
    refine ⟨fun j => ?_, ?_⟩
    · induction j using Fin.addCases with
      | left i =>
        rw [Fin.append_left, hR]
        exact (Subgroup.mem_inf.1 (g i).2).1
      | right i =>
        rw [Fin.append_right]
        exact one_mem _
    · rw [List.ofFn_fin_append, List.prod_append, List.ofFn_const, List.prod_replicate, one_pow,
        mul_one]
  refine ⟨fun g g' h => ?_, Set.Subset.antisymm ?_ fun x hx => ?_⟩
  · obtain ⟨hg, hgp⟩ := hext g
    obtain ⟨hg', hgp'⟩ := hext g'
    have h' := hinj _ _ hg hg' (hgp.trans (h.trans hgp'.symm))
    funext i
    have hi := congrFun h' (Fin.castAdd e i)
    simp only [Fin.append_left] at hi
    exact Subtype.ext hi
  · rintro _ ⟨g, rfl⟩
    show (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod ∈ U ⊓ fixedGroup K
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    have hgi := Subgroup.mem_inf.1 (g i).2
    refine Subgroup.mem_inf.2 ⟨hU (Fin.castAdd e i) ?_, hgi.2⟩
    rw [hR]
    exact hgi.1
  · obtain ⟨hxU, hxΓ⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨u, hu, rfl⟩ := hsurj _ hxU
    have hfix := conj_twistA_eq_of_mem hxΓ
    rw [conj_ofFn_prod] at hfix
    have hu' := hinj _ _ (fun j => hA j _ (hu j)) hu hfix
    have huΓ : ∀ j, u j ∈ fixedGroup K := fun j => by
      refine mem_fixedGroup.2 ⟨hadj j (hu j), ?_⟩
      exact (mul_inv_eq_iff_eq_mul.1 (congrFun hu' j)).symm
    have h1 : ∀ j : Fin e, u (Fin.natAdd m j) = 1 := fun j => by
      have h := Subgroup.mem_inf.2 ⟨hu (Fin.natAdd m j), huΓ (Fin.natAdd m j)⟩
      rw [hexcl j] at h
      exact Subgroup.mem_bot.1 h
    refine ⟨fun i => ⟨u (Fin.castAdd e i), Subgroup.mem_inf.2 ⟨?_, huΓ _⟩⟩, ?_⟩
    · rw [← hR]
      exact hu _
    · show (List.ofFn fun i => u (Fin.castAdd e i)).prod = (List.ofFn u).prod
      rw [hsplit u]
      simp only [h1, List.ofFn_const, List.prod_replicate, one_pow, mul_one]

theorem isNilpotent_negUnipotent
    : Group.IsNilpotent (negUnipotent TwistTag.E6.tag K) := by
  obtain ⟨w₀, -, h₀⟩ := TwistTag.E6.exists_reversesSigns_mem_relWeylTwist
  have h := (canonical_weyl_root_transport TwistTag.E6.tag K).1 w₀
    {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α} fun α hα => hα.1
  rw [image_smul_posRoots_of_reversesSigns h₀] at h
  have hpos := (positive_root_height_series TwistTag.E6.tag K).2.2.2.2.1
  have e := Subgroup.equivMapOfInjective (posUnipotent TwistTag.E6.tag K)
    (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀)).toMonoidHom
    (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀)).injective
  have hnil := (Group.isNilpotent_congr e).1 hpos
  change Group.IsNilpotent
    ↥(rootSpan TwistTag.E6.tag K {α | IsRoot TwistTag.E6.tag α ∧ height α < 0})
  rw [← h]
  exact hnil

theorem mem_normalizer_sup_of_mem {G : Type*} [Group G] {H H' : Subgroup G} {g : G}
    (h : g ∈ Subgroup.normalizer (H : Set G)) (h' : g ∈ Subgroup.normalizer (H' : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ H' : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h h' ⊢
  rw [Subgroup.map_sup, h, h']

theorem conj_mem_fixedGroup_iff {h : ModGL TwistTag.E6.tag K} (hh : h ∈ fixedGroup K)
    (x : ModGL TwistTag.E6.tag K) : x ∈ fixedGroup K ↔ h * x * h⁻¹ ∈ fixedGroup K := by
  refine ⟨fun hx => mul_mem (mul_mem hh hx) (inv_mem hh), fun hx => ?_⟩
  have h' := mul_mem (mul_mem (inv_mem hh) hx) hh
  rwa [show h⁻¹ * (h * x * h⁻¹) * h = x by group] at h'

end CFSG.LieType.Chevalley.E6SignedGraph

module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.OddSplitGenerationFinal
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.HardMathSupport.Seitz.Proving.OrderThreeSLConj

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  RootOps
open scoped commutatorElement

section Bridge

variable
  {K : Type} [Field K]

theorem conj_sup_le {n : ModGL .G2 K} {β γ : Fin Tag.G2.rank → ℤ}
    (h1 : ∀ c : K, ∃ d : K, n * pinnedX .G2 K β c * n⁻¹ = pinnedX .G2 K γ d)
    (h2 : ∀ c : K, ∃ d : K, n * pinnedX .G2 K (-β) c * n⁻¹ = pinnedX .G2 K (-γ) d) :
    ∀ g ∈ rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β),
      n * g * n⁻¹ ∈ rootSubgroup .G2 K γ ⊔ rootSubgroup .G2 K (-γ) := by
  have key : rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β) ≤
      (rootSubgroup .G2 K γ ⊔ rootSubgroup .G2 K (-γ)).comap (MulAut.conj n).toMonoidHom := by
    refine sup_le ?_ ?_
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      obtain ⟨d, hd⟩ := h1 c
      change n * pinnedX .G2 K β c * n⁻¹ ∈ rootSubgroup .G2 K γ ⊔ rootSubgroup .G2 K (-γ)
      rw [hd]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨d, rfl⟩)
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      obtain ⟨d, hd⟩ := h2 c
      change n * pinnedX .G2 K (-β) c * n⁻¹ ∈ rootSubgroup .G2 K γ ⊔ rootSubgroup .G2 K (-γ)
      rw [hd]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨d, rfl⟩)
  intro g hg
  exact key hg

theorem weyl_range_step (i : Fin Tag.G2.rank) {β γ : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β)
    (e1 : reflect .G2 i β = γ) (e2 : reflect .G2 i (-β) = -γ) :
    ∀ g ∈ rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β),
      weylElt .G2 K i 1 * g * (weylElt .G2 K i 1)⁻¹ ∈
        rootSubgroup .G2 K γ ⊔ rootSubgroup .G2 K (-γ) := by
  refine conj_sup_le (fun c => ?_) (fun c => ?_)
  · refine ⟨(allRootWeylSign .G2 i β : K) * c, ?_⟩
    rw [weylElt_one_mul_pinnedX_mul_inv K i hβ c, e1]
  · refine ⟨(allRootWeylSign .G2 i (-β) : K) * c, ?_⟩
    rw [weylElt_one_mul_pinnedX_mul_inv K i (IsRoot.neg hβ) c, e2]


theorem refl_R_v : reflect .G2 iR gV = gU := List.ofFn_injective (by decide +kernel)
theorem refl_R_nv : reflect .G2 iR (-gV) = -gU := List.ofFn_injective (by decide +kernel)
theorem refl_A_u : reflect .G2 iA gU = gR := List.ofFn_injective (by decide +kernel)
theorem refl_A_nu : reflect .G2 iA (-gU) = -gR := List.ofFn_injective (by decide +kernel)
theorem refl_R_a : reflect .G2 iR gA = gB := List.ofFn_injective (by decide +kernel)
theorem refl_R_na : reflect .G2 iR (-gA) = -gB := List.ofFn_injective (by decide +kernel)
theorem refl_A_b : reflect .G2 iA gB = gC := List.ofFn_injective (by decide +kernel)
theorem refl_A_nb : reflect .G2 iA (-gB) = -gC := List.ofFn_injective (by decide +kernel)

@[expose] def x0 (K : Type) [Field K] : ModGL .G2 K := weylElt .G2 K iA 1 * weylElt .G2 K iR 1

theorem x0_range_v : ∀ g ∈ rootSubgroup .G2 K gV ⊔ rootSubgroup .G2 K (-gV),
    x0 K * g * (x0 K)⁻¹ ∈ rootSubgroup .G2 K gR ⊔ rootSubgroup .G2 K (-gR) := by
  intro g hg
  have h1 := weyl_range_step iR isRoot_gV refl_R_v refl_R_nv g hg
  have h2 := weyl_range_step iA isRoot_gU refl_A_u refl_A_nu _ h1
  have e : x0 K * g * (x0 K)⁻¹ = weylElt .G2 K iA 1 * (weylElt .G2 K iR 1 * g *
      (weylElt .G2 K iR 1)⁻¹) * (weylElt .G2 K iA 1)⁻¹ := by unfold x0; group
  rw [e]; exact h2

theorem x0_range_a : ∀ g ∈ rootSubgroup .G2 K gA ⊔ rootSubgroup .G2 K (-gA),
    x0 K * g * (x0 K)⁻¹ ∈ rootSubgroup .G2 K gC ⊔ rootSubgroup .G2 K (-gC) := by
  intro g hg
  have h1 := weyl_range_step iR isRoot_gA refl_R_a refl_R_na g hg
  have h2 := weyl_range_step iA isRoot_gB refl_A_b refl_A_nb _ h1
  have e : x0 K * g * (x0 K)⁻¹ = weylElt .G2 K iA 1 * (weylElt .G2 K iR 1 * g *
      (weylElt .G2 K iR 1)⁻¹) * (weylElt .G2 K iA 1)⁻¹ := by unfold x0; group
  rw [e]; exact h2


theorem iform_r_c : iform (τ := .G2) gR gC = 0 := by decide +kernel
theorem not_root_r_add_c : ¬ IsRoot .G2 (gR + gC) := by
  rw [isRoot_iff_mem_artifactRoots]; decide +kernel
theorem not_root_r_sub_c : ¬ IsRoot .G2 (gR - gC) := by
  rw [isRoot_iff_mem_artifactRoots]; decide +kernel

theorem commute_L_r_c : ∀ g ∈ (rootSL2 .G2 K gR).range, ∀ h ∈ (rootSL2 .G2 K gC).range,
    g * h = h * g :=
  exceptional_Lang_strongly_orthogonal_root_rank_one_commutation .G2 K isRoot_gR isRoot_gC
    iform_r_c not_root_r_add_c not_root_r_sub_c

theorem rootSL2_gR : rootSL2 .G2 K gR = simpleRootSL2 .G2 K iR := by
  rw [gR_eq]
  ext A : 1
  rw [rootSL2_apply, pinnedData_single]
  simp [pinnedWeyl, pinnedData_single]

theorem M_eq : (uSL (1 : K) * vSL (-1) * uSL 2 : SL2 K) = Coordinator.orderThreeSL K :=
  Subtype.ext (by rw [M_val]; rfl)

theorem zr_eq_rootSL2 : zr K = rootSL2 .G2 K gR (Coordinator.orderThreeSL K) := by
  rw [rootSL2_gR, ← M_eq, ← zr_eq_rho]

theorem orderThreeSL_cube : Coordinator.orderThreeSL K ^ 3 = 1 := by
  rw [← M_eq, ← M_cube]

theorem orderThreeSL_ne_one : Coordinator.orderThreeSL K ≠ 1 := by
  intro h
  have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [Coordinator.orderThreeSL] at this


theorem conj_pair [Finite K] (h3 : 3 ∣ Nat.card K + 1) :
    ∃ x ∈ adjointGroup .G2 K,
      x * rootSL2 .G2 K gV (Coordinator.orderThreeSL K) * x⁻¹ = zr K ∧
      ∃ B : SL2 K, x * rootSL2 .G2 K gA (Coordinator.orderThreeSL K) * x⁻¹ =
        rootSL2 .G2 K gC B := by
  set M := Coordinator.orderThreeSL K with hM
  have hv : x0 K * rootSL2 .G2 K gV M * (x0 K)⁻¹ ∈ (rootSL2 .G2 K gR).range := by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot isRoot_gR]
    apply x0_range_v
    rw [← CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot isRoot_gV]; exact ⟨M, rfl⟩
  obtain ⟨A₁, hA₁⟩ := hv
  have hinjV := CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := .G2) (K := K) gV
  have hinjR := CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := .G2) (K := K) gR
  have hcube : A₁ ^ 3 = 1 := by
    apply hinjR
    rw [map_pow, hA₁, conj_pow, ← map_pow, orderThreeSL_cube, map_one, map_one]
    group
  have hA1 : A₁ ≠ 1 := by
    intro h
    rw [h, map_one] at hA₁
    have h1 : rootSL2 .G2 K gV M = 1 := by
      have := congrArg (fun g => (x0 K)⁻¹ * g * x0 K) hA₁
      simpa [mul_assoc] using this.symm
    exact orderThreeSL_ne_one (hinjV (h1.trans (map_one _).symm))
  obtain ⟨S, hS⟩ := Proving.exists_conj_eq_orderThreeSL h3 hcube hA1
  have hea : x0 K * rootSL2 .G2 K gA M * (x0 K)⁻¹ ∈ (rootSL2 .G2 K gC).range := by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot isRoot_gC]
    apply x0_range_a
    rw [← CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot isRoot_gA]; exact ⟨M, rfl⟩
  obtain ⟨B, hB⟩ := hea
  have hx0 : x0 K ∈ adjointGroup .G2 K := by
    unfold x0
    exact Subgroup.mul_mem _ (weylElt_mem_adjointGroup _ _) (weylElt_mem_adjointGroup _ _)
  refine ⟨rootSL2 .G2 K gR S * x0 K, ?_, ?_, B, ?_⟩
  · exact Subgroup.mul_mem _ ((exceptional_Lang_root_rank_one_data .G2 K gR).2.2.2.2.1 S) hx0
  · have e : rootSL2 .G2 K gR S * x0 K * rootSL2 .G2 K gV M * (rootSL2 .G2 K gR S * x0 K)⁻¹ =
        rootSL2 .G2 K gR S * (x0 K * rootSL2 .G2 K gV M * (x0 K)⁻¹) * (rootSL2 .G2 K gR S)⁻¹ := by
      group
    rw [e, ← hA₁, ← map_inv, ← map_mul, ← map_mul, hS, zr_eq_rootSL2]
  · have e : rootSL2 .G2 K gR S * x0 K * rootSL2 .G2 K gA M * (rootSL2 .G2 K gR S * x0 K)⁻¹ =
        rootSL2 .G2 K gR S * (x0 K * rootSL2 .G2 K gA M * (x0 K)⁻¹) * (rootSL2 .G2 K gR S)⁻¹ := by
      group
    rw [e, ← hB]
    have hc := commute_L_r_c (K := K) _ ⟨S, rfl⟩ _ ⟨B, rfl⟩
    rw [hB] at hc ⊢
    rw [hc]; group


theorem exists_ne_zero_ne_one [Finite K] (hK : 3 ≤ Nat.card K) : ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  classical
  have := Fintype.ofFinite K
  by_contra! h
  have hle : Fintype.card K ≤ ({0, 1} : Finset K).card := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card fun t _ => by
      by_cases h0 : t = 0
      · simp [h0]
      · simp [h t h0]
  have := Finset.card_le_two (a := (0 : K)) (b := 1)
  rw [Nat.card_eq_fintype_card] at hK
  omega

theorem three_ne_zero_of_dvd [Finite K] (h3 : 3 ∣ Nat.card K + 1) : (3 : K) ≠ 0 := by
  intro h
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hd : ringChar K ∣ 3 := (ringChar.spec K 3).1 (by exact_mod_cast h)
  have h3p := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd
  rw [Nat.card_eq_fintype_card, hcard, h3p] at h3
  have : 3 ∣ 3 ^ (n : ℕ) := dvd_pow_self 3 n.ne_zero
  omega

theorem centralizer_sup_top [Finite K] (h3 : 3 ∣ Nat.card K + 1) (hK : 3 ≤ Nat.card K) :
    Subgroup.centralizer {Coordinator.zStd K} ⊔ Subgroup.centralizer {Coordinator.eStd K} =
      (⊤ : Subgroup (adjointGroup .G2 K)) := by
  obtain ⟨x, hx, hxz, B, hxe⟩ := conj_pair (K := K) h3
  have hzrA : zr K ∈ adjointGroup .G2 K := by
    rw [zr_eq_rootSL2]; exact (exceptional_Lang_root_rank_one_data .G2 K gR).2.2.2.2.1 _
  have hcB : rootSL2 .G2 K gC B ∈ adjointGroup .G2 K :=
    (exceptional_Lang_root_rank_one_data .G2 K gC).2.2.2.2.1 B
  refine Coordinator.centralizer_sup_eq_top_of_conj (x := ⟨x, hx⟩) (a := ⟨zr K, hzrA⟩)
    (b := ⟨rootSL2 .G2 K gC B, hcB⟩) (Or.inl (Subtype.ext ?_)) (Or.inl (Subtype.ext ?_)) ?_
  · exact hxz
  · exact hxe
  set D := Subgroup.centralizer {(⟨zr K, hzrA⟩ : adjointGroup .G2 K)} ⊔
    Subgroup.centralizer {(⟨rootSL2 .G2 K gC B, hcB⟩ : adjointGroup .G2 K)} with hD
  set H := D.map (adjointGroup .G2 K).subtype with hH
  have memA : ∀ (h : ModGL .G2 K) (hA : h ∈ adjointGroup .G2 K), h * zr K = zr K * h → h ∈ H :=
    fun h hA hc => ⟨⟨h, hA⟩, Subgroup.mem_sup_left (by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact Subtype.ext hc), rfl⟩
  have memB : ∀ (h : ModGL .G2 K) (hA : h ∈ adjointGroup .G2 K),
      h * rootSL2 .G2 K gC B = rootSL2 .G2 K gC B * h → h ∈ H :=
    fun h hA hc => ⟨⟨h, hA⟩, Subgroup.mem_sup_right (by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact Subtype.ext hc), rfl⟩
  have hzr_range : zr K ∈ (rootSL2 .G2 K gR).range := ⟨Coordinator.orderThreeSL K, zr_eq_rootSL2.symm⟩
  have hB_range : rootSL2 .G2 K gC B ∈ (rootSL2 .G2 K gC).range := ⟨B, rfl⟩
  have hcomm_cB : ∀ A : SL2 K, rootSL2 .G2 K gR A * rootSL2 .G2 K gC B =
      rootSL2 .G2 K gC B * rootSL2 .G2 K gR A := fun A =>
    commute_L_r_c _ ⟨A, rfl⟩ _ hB_range
  have hcomm_zr : ∀ h ∈ (rootSL2 .G2 K gC).range, h * zr K = zr K * h := fun h hh =>
    (commute_L_r_c _ hzr_range _ hh).symm
  have hUc : ∀ t : K, pinnedX .G2 K gC t ∈ (rootSL2 .G2 K gC).range := fun t => by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot isRoot_gC]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨t, rfl⟩)
  have hUnc : ∀ t : K, pinnedX .G2 K (-gC) t ∈ (rootSL2 .G2 K gC).range := fun t => by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot isRoot_gC]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨t, rfl⟩)
  have hle : adjointGroup .G2 K ≤ H := by
    refine adjointGroup_le_of_centralizer H ?_ ?_ ?_ ?_ ?_
      (exists_ne_zero_ne_one hK) (three_ne_zero_of_dvd h3)
    · intro t
      have e : xUnit .G2 K iR t = rootSL2 .G2 K gR (uSL t) := by
        rw [rootSL2_gR, simpleRootSL2_uSL]
      rw [e]
      exact memB _ ((exceptional_Lang_root_rank_one_data .G2 K gR).2.2.2.2.1 _) (hcomm_cB _)
    · intro t
      have e : yUnit .G2 K iR t = rootSL2 .G2 K gR (vSL t) := by
        rw [rootSL2_gR, simpleRootSL2_vSL]
      rw [e]
      exact memB _ ((exceptional_Lang_root_rank_one_data .G2 K gR).2.2.2.2.1 _) (hcomm_cB _)
    · intro t
      exact memA _ (pinnedX_mem_adjointGroup _ _) (hcomm_zr _ (hUc t))
    · intro t
      exact memA _ (pinnedX_mem_adjointGroup _ _) (hcomm_zr _ (hUnc t))
    · intro g hg hfix
      refine memA g (Qg_le_adjointGroup hg) ?_
      have : zr K * g = g * zr K := by
        rw [mul_inv_eq_iff_eq_mul] at hfix; exact hfix
      exact this.symm
  rw [eq_top_iff]
  intro g _
  obtain ⟨y, hy, hyg⟩ := hle g.2
  have : y = g := Subtype.ext hyg
  rw [← this]; exact hy

end Bridge

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

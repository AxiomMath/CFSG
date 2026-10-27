module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeTIFacts.Frontier
public import CFSG.CharacterTheory.Semidihedral.AllPrimeDataInputs
public import CFSG.CharacterTheory.Semidihedral.AllPrimeNbarFacts

public section

namespace CFSG.Semidihedral.AllPrime

noncomputable section

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.AllPrime.QDTI
open CFSG.Wreathed.OriginalAllPrime.TIFacts CFSG.QuasiDihedralFusion
open scoped Pointwise

theorem qdti_seven_le {p f : ℕ} (hpodd : Odd p) (hq : 5 < p ^ f) : 7 ≤ p ^ f := by
  obtain ⟨k, hk⟩ := hpodd.pow (n := f)
  omega

theorem qdti_charP {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ f) : CharP F p := by
  have : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hcard)

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem frontier_TI_F₀_abelian
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (frontier_F₀_eq_T : (frontierSetting S fS t p f).D ⊓
      Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G) =
        (frontierSetting S fS t p f).T) :
    ∀ g ∈ (frontierSetting S fS t p f).F₀, ∀ h ∈ (frontierSetting S fS t p f).F₀,
      g * h = h * g := by
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  intro g hg h hh
  change g ∈ (frontierSetting S fS t p f).D ⊓
    Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G) at hg
  change h ∈ (frontierSetting S fS t p f).D ⊓
    Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G) at hh
  rw [frontier_F₀_eq_T] at hg hh
  exact (Subgroup.mem_centralizer_iff.mp ((frontierSetting S fS t p f).T_le_C hσ hg) h hh).symm

omit [Finite G] [IsSimpleGroup G] in
theorem frontier_TI_F₀_omega
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (_hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (_ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (frontier_F₀_eq_T : (frontierSetting S fS t p f).D ⊓
      Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G) =
        (frontierSetting S fS t p f).T) :
    ∀ g ∈ (frontierSetting S fS t p f).F₀, g ^ 2 = 1 → g ∈ (frontierSetting S fS t p f).T := by
  intro g hg _
  change g ∈ (frontierSetting S fS t p f).D ⊓
    Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G) at hg
  rwa [frontier_F₀_eq_T] at hg

omit [Finite G] [IsSimpleGroup G] in
theorem frontier_TI_C_eq
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (_hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (_ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (frontier_C_eq : oddCoreIn (frontierSetting S fS t p f).C ⊔
      ((frontierSetting S fS t p f).D ⊓
        Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G)) =
          (frontierSetting S fS t p f).C) :
    oddCoreIn (frontierSetting S fS t p f).C ⊔ (frontierSetting S fS t p f).F₀ =
      (frontierSetting S fS t p f).C :=
  frontier_C_eq

omit [Finite G] [IsSimpleGroup G] in
theorem frontier_TI_commutator_le
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (_hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (_ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (frontier_commutator_N_le_L₀ :
      ⁅(frontierSetting S fS t p f).N, (frontierSetting S fS t p f).N⁆ ≤
        (frontierSetting S fS t p f).L₀) :
    ⁅(frontierSetting S fS t p f).N, (frontierSetting S fS t p f).N⁆ ≤
      (frontierSetting S fS t p f).L₀ :=
  frontier_commutator_N_le_L₀

theorem frontier_TI_cyclic
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ J : Subgroup G, (frontierSetting S fS t p f).IsLayerComplement J →
      IsCyclic ((frontierSetting S fS t p f).C ⊓ J : Subgroup G) := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, -, -, ha, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  exact hφ.cyclic (isCyclic_layerM_inf_cenU hodd ha)

theorem frontier_TI_centralizer_le
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ J : Subgroup G, (frontierSetting S fS t p f).IsLayerComplement J →
      ∀ g ∈ (frontierSetting S fS t p f).C,
        g ∈ Subgroup.centralizer (((frontierSetting S fS t p f).C ⊓ J : Subgroup G) : Set G) →
          g ∈ (frontierSetting S fS t p f).L := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, -, -, -, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have hF5 : 5 ≤ Nat.card F := by rw [hcard]; omega
  set σ := frontierSetting S fS t p f with hσdef
  refine hφ.centralizer_le (B := (σ.L.subgroupOf σ.N).map (frontierModelMap S fS t p f Psi))
    ?_ le_rfl
  intro g hg hgc
  have hr := right_eq_one_of_centralizes hodd hF5 hg hgc
  have hLM : layerM F a A hfix ≤ (σ.L.subgroupOf σ.N).map (frontierModelMap S fS t p f Psi) := by
    rw [← hφ.map_L₀]
    exact Subgroup.map_mono (Subgroup.comap_mono le_sup_left)
  have hσv := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  have hu : originalU F a A hfix ∈ (σ.L.subgroupOf σ.N).map (frontierModelMap S fS t p f Psi) := by
    rw [← hφ.map_x₂]
    exact ⟨⟨σ.x₂, hφ.x₂_mem⟩, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right hσv.x₂_mem), rfl⟩
  rw [decomp g, hr, map_one, mul_one]
  refine Subgroup.mul_mem _ (hLM ⟨_, rfl⟩) ?_
  rcases C2_cases g.left.right with h | h
  · rw [h, map_one, map_one]
    exact Subgroup.one_mem _
  · rw [h]
    exact hu

theorem frontier_TI_signalizer_le
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ U ∈ signalizers (frontierSetting S fS t p f).N
      (frontierSetting S fS t p f).C r, U ≤ (frontierSetting S fS t p f).L₀ := by
  obtain ⟨F, _, _, A, a, hfix, Psi, -, hA, -, -, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  exact hφ.signalizer_le (signalizer_le_layerM hA)

omit [Finite G] [IsSimpleGroup G] in
theorem frontier_deltaEpsMinus_iff {n : ℕ} (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G) (p f : ℕ) :
    (frontierSetting S fS t p f).DeltaEpsMinus ↔ p ^ f % 4 = 3 := by
  change (1 = 1 ∧ p ^ f % 4 = 3) ∨ (1 ≠ 1 ∧ p ^ f % 4 = 1) ↔ _
  simp

theorem frontier_TI_layer_signalizer
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ J : Subgroup G, (frontierSetting S fS t p f).IsLayerComplement J →
      ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ X ∈ signalizers J (frontierSetting S fS t p f).C r,
        X ≠ ⊥ → (frontierSetting S fS t p f).DeltaEpsMinus ∧
          r = (frontierSetting S fS t p f).p := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, -, -, ha, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have hq7 : 7 ≤ Nat.card F := by rw [hcard]; exact qdti_seven_le hpodd hq
  have := qdti_charP hp hcard
  intro J hJ r hr hr2 X hX hXne
  have hne : (X.subgroupOf (frontierSetting S fS t p f).N).map
      (frontierModelMap S fS t p f Psi) ≠ ⊥ := fun h =>
    hXne (hφ.eq_bot_of_map_eq_bot hJ hX.1 h)
  obtain ⟨h3, hrp⟩ := layer_signalizer_model hodd ha hq7 hp r hr hr2 _
    (hφ.map_mem_signalizers hJ hX) hne
  refine ⟨(frontier_deltaEpsMinus_iff S fS t p f).mpr (hcard ▸ h3), hrp⟩

theorem qdti_sd_conj_s {n : ℕ} (hn : 4 ≤ n) :
    r n ^ 2 ^ (n - 3) * s n * (r n ^ 2 ^ (n - 3))⁻¹ = z n * s n := by
  have h1 := sd_s_conj_quarter hn
  have hs : s n * s n = 1 := by
    have h := pow_orderOf_eq_one (s n)
    rw [orderOf_s n (by omega)] at h
    rw [← pow_two]
    exact h
  have hv2 : (r n ^ 2 ^ (n - 3)) * (r n ^ 2 ^ (n - 3)) = z n := by
    rw [← pow_add, z, half, ← two_mul, show 2 * 2 ^ (n - 3) = 2 ^ (n - 2) by
      rw [← pow_succ']; congr 1; omega]
  have hz2 : z n * z n = 1 := by
    have h := pow_orderOf_eq_one (z n)
    rw [orderOf_z n (by omega)] at h
    rw [← pow_two]
    exact h
  have hzc : ∀ g, z n * g = g * z n := fun g =>
    (Subgroup.mem_center_iff.mp (z_mem_center n hn) g).symm
  set v := r n ^ 2 ^ (n - 3) with hv
  have h2 : v * s n = s n * v⁻¹ := by
    have : s n * v * s n = v⁻¹ := by
      rw [← h1, inv_eq_of_mul_eq_one_right hs]
    calc v * s n = s n * (s n * v * s n) := by
          rw [← mul_assoc, ← mul_assoc, hs, one_mul]
      _ = s n * v⁻¹ := by rw [this]
  have hvinv : v⁻¹ = v * z n := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hv2, hz2]
  calc v * s n * v⁻¹ = s n * v⁻¹ * v⁻¹ := by rw [h2]
    _ = s n * (v * v) * (z n * z n) := by
      rw [hvinv]
      calc s n * (v * z n) * (v * z n) = s n * v * (z n * v) * z n := by group
        _ = s n * v * (v * z n) * z n := by rw [hzc]
        _ = s n * (v * v) * (z n * z n) := by group
    _ = z n * s n := by rw [hv2, hz2, mul_one, hzc]

theorem frontier_TI_layer_signalizer_pair
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ J : Subgroup G, (frontierSetting S fS t p f).IsLayerComplement J →
      (frontierSetting S fS t p f).DeltaEpsMinus →
      ∃ Q Qs : Subgroup G, Q ∈ signalizers J (frontierSetting S fS t p f).C
          (frontierSetting S fS t p f).p ∧
        Qs ∈ signalizers J (frontierSetting S fS t p f).C (frontierSetting S fS t p f).p ∧
        Nat.card Q = (frontierSetting S fS t p f).q ∧
        Nat.card Qs = (frontierSetting S fS t p f).q ∧ Q ≠ Qs ∧ J = Q ⊔ Qs ∧
        (∃ z ∈ (frontierSetting S fS t p f).D, TotallyInverted.conjSub z Q = Qs) ∧
        (∀ X ∈ signalizers J (frontierSetting S fS t p f).C (frontierSetting S fS t p f).p,
          X ≤ Q ∨ X ≤ Qs) ∧
        (∀ X : Subgroup G, X ≤ Q → (frontierSetting S fS t p f).C ≤
          Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Q) ∧
        (∀ X : Subgroup G, X ≤ Qs → (frontierSetting S fS t p f).C ≤
          Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Qs) := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, hA, -, ha, hPsiZ, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have hq7 : 7 ≤ Nat.card F := by rw [hcard]; exact qdti_seven_le hpodd hq
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  set σ := frontierSetting S fS t p f with hσdef
  intro J hJ hδε
  have h3 : Nat.card F % 4 = 3 := by
    rw [hcard]
    exact (frontier_deltaEpsMinus_iff S fS t p f).mp hδε
  obtain ⟨b, hb⟩ := (neg_coefficient_square_iff F a hodd ha).mpr h3
  have hl : b ^ 2 = -(a : F) := by rw [hb]; ring
  have hl' : (-b) ^ 2 = -(a : F) := by rw [neg_sq]; exact hl
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by simpa using hl.symm)
  have hJN := hφ.J_le_N hJ
  obtain ⟨hz, -, -, hsC, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  set v := r n ^ 2 ^ (n - 3) with hvdef
  have hvD : (fS v : G) ∈ σ.D := by
    rw [hσdef, frontierSetting_D hn S fS t ht p f]
    have := sdFourSubgroup_isKleinFour hn
    exact ⟨v, (sd_kleinFour_facts hn (sdFourSubgroup n)).2.2.1, rfl⟩
  have hvN : (fS v : G) ∈ σ.N := frontier_S_le_C hn S fS t ht p f (fS v).2
  have hsN : (fS (s n) : G) ∈ σ.N := hφ.x₂_mem
  have htN : t ∈ σ.N := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hu : frontierModelMap S fS t p f Psi ⟨(fS (s n) : G), hsN⟩ = originalU F a A hfix :=
    hφ.map_x₂
  have hZ : frontierModelMap S fS t p f Psi ⟨t, htN⟩ = originalZ F a A hfix := by
    change Psi.symm (nu t (tInC t)) = _
    rw [← hPsiZ, MulEquiv.symm_apply_apply]
  have hkey : (⟨(fS v : G), hvN⟩ : σ.N) * ⟨(fS (s n) : G), hsN⟩ * (⟨(fS v : G), hvN⟩ : σ.N)⁻¹ =
      ⟨t, htN⟩ * ⟨(fS (s n) : G), hsN⟩ := by
    apply Subtype.ext
    change (fS v : G) * (fS (s n) : G) * (fS v : G)⁻¹ = t * (fS (s n) : G)
    rw [← hz, ← Subgroup.coe_inv, ← map_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
      ← Subgroup.coe_mul, ← map_mul, ← map_mul, ← map_mul, qdti_sd_conj_s hn]
  have hvconj : frontierModelMap S fS t p f Psi ⟨(fS v : G), hvN⟩ * originalU F a A hfix *
      (frontierModelMap S fS t p f Psi ⟨(fS v : G), hvN⟩)⁻¹ =
        originalZ F a A hfix * originalU F a A hfix := by
    rw [← hu, ← hZ, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hkey]
  have hQ' := rootM_mem_signalizers (hfix := hfix) hodd hA hp hcard hl
  have hQs' := rootM_mem_signalizers (hfix := hfix) hodd hA hp hcard hl'
  obtain ⟨Q, hQJ, hQimg⟩ := hφ.exists_of_le hJ hQ'.1
  obtain ⟨Qs, hQsJ, hQsimg⟩ := hφ.exists_of_le hJ hQs'.1
  have hirr : ∀ {P : Subgroup G} {l : F}, l ^ 2 = -(a : F) → P ≤ J →
      (P.subgroupOf σ.N).map (frontierModelMap S fS t p f Psi) = rootM F a A hfix l →
      ∀ X : Subgroup G, X ≤ P → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = P := by
    intro P l hl₀ hPJ hPimg X hXP hCX
    have hXJ := hXP.trans hPJ
    have hle : (X.subgroupOf σ.N).map (frontierModelMap S fS t p f Psi) ≤ rootM F a A hfix l :=
      hPimg ▸ Subgroup.map_mono (subgroupOf_mono_of_le hXP σ.N)
    have hnorm : cenU F a A hfix ≤
        Subgroup.normalizer
          (((X.subgroupOf σ.N).map (frontierModelMap S fS t p f Psi) : Subgroup _) : Set _) := by
      change Subgroup.centralizer {originalU F a A hfix} ≤ _
      rw [← hφ.map_C]
      exact hφ.le_normalizer_map (hXJ.trans hJN) hCX
    rcases rootM_irreducible hodd hl₀ _ hle hnorm with h | h
    · exact Or.inl (hφ.eq_bot_of_map_eq_bot hJ hXJ h)
    · exact Or.inr (hφ.eq_of_map_eq_map hJ hXJ hPJ (h.trans hPimg.symm))
  refine ⟨Q, Qs, hφ.mem_signalizers_of_map hJ hQJ (hQimg ▸ hQ'),
    hφ.mem_signalizers_of_map hJ hQsJ (hQsimg ▸ hQs'), ?_, ?_, ?_, ?_, ⟨_, hvD, ?_⟩, ?_,
    hirr hl hQJ hQimg, hirr hl' hQsJ hQsimg⟩
  · rw [← hφ.card_map hJ hQJ, hQimg, card_rootM, hcard]
    rfl
  · rw [← hφ.card_map hJ hQsJ, hQsimg, card_rootM, hcard]
    rfl
  · intro h
    apply rootM_ne (hfix := hfix) hodd hb0
    rw [← hQimg, ← hQsimg, h]
  · apply hφ.eq_of_map_eq_map hJ le_rfl (sup_le hQJ hQsJ)
    rw [hφ.map_J hJ, Subgroup.subgroupOf_sup (hQJ.trans hJN) (hQsJ.trans hJN), Subgroup.map_sup,
      hQimg, hQsimg, layerM_eq_sup hodd hb0]
  · apply hφ.eq_of_map_eq_map hJ (IsModelMap.conjSub_le hJ hvN hQJ) hQsJ
    rw [hφ.map_conjSub hvN (hQJ.trans hJN), hQimg, hQsimg, conjSub_rootM hA hl hvconj]
  · intro X hX
    rcases signalizer_le_rootM_or hodd ha hq7 hp hp2 hl (hφ.map_mem_signalizers hJ hX) with
      h | h
    · exact Or.inl (hφ.le_of_map_le hJ hX.1 hQJ (hQimg ▸ h))
    · exact Or.inr (hφ.le_of_map_le hJ hX.1 hQsJ (hQsimg ▸ h))

theorem frontier_TI_permutable_le
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ J : Subgroup G, (frontierSetting S fS t p f).IsLayerComplement J →
      ∀ U : Subgroup G, U ≤ (frontierSetting S fS t p f).N → Odd (Nat.card U) →
        (U : Set G) * ((frontierSetting S fS t p f).C : Set G) =
          ((frontierSetting S fS t p f).C : Set G) * (U : Set G) →
        ∃ (p' : ℕ) (X : Subgroup G), p'.Prime ∧
          X ∈ signalizers J (frontierSetting S fS t p f).C p' ∧
          U ≤ (frontierSetting S fS t p f).C ⊔ X ⊔ (frontierSetting S fS t p f).ON := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, hA, -, ha, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have hq7 : 7 ≤ Nat.card F := by rw [hcard]; exact qdti_seven_le hpodd hq
  exact hφ.permutable_le (permutable_model hodd ha hq7 hA hp hcard)

theorem frontier_tiFacts_of
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (frontier_F₀_eq_T : (frontierSetting S fS t p f).D ⊓
      Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G) =
        (frontierSetting S fS t p f).T)
    (frontier_C_eq : oddCoreIn (frontierSetting S fS t p f).C ⊔
      ((frontierSetting S fS t p f).D ⊓
        Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G)) =
          (frontierSetting S fS t p f).C)
    (frontier_commutator_N_le_L₀ :
      ⁅(frontierSetting S fS t p f).N, (frontierSetting S fS t p f).N⁆ ≤
        (frontierSetting S fS t p f).L₀) :
    (frontierSetting S fS t p f).TIFacts where
  F₀_abelian := frontier_TI_F₀_abelian hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel frontier_F₀_eq_T
  F₀_omega := frontier_TI_F₀_omega hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel frontier_F₀_eq_T
  C_eq := frontier_TI_C_eq hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
    frontier_C_eq
  commutator_le := frontier_TI_commutator_le hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel frontier_commutator_N_le_L₀
  cyclic := frontier_TI_cyclic hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  centralizer_le := frontier_TI_centralizer_le hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel
  signalizer_le := frontier_TI_signalizer_le hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel
  layer_signalizer := frontier_TI_layer_signalizer hGnonab n hn S fS t ht hnonab hcentral hnc p f
    hp hpodd hf hq hmodel
  layer_signalizer_pair := frontier_TI_layer_signalizer_pair hGnonab n hn S fS t ht hnonab
    hcentral hnc p f hp hpodd hf hq hmodel
  permutable_le := frontier_TI_permutable_le hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel

theorem frontier_tiFacts
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (frontierSetting S fS t p f).TIFacts :=
  frontier_tiFacts_of hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
    (frontier_F₀_eq_T n hn S fS t ht p f) (frontier_C_eq n hn S fS t ht p f)
    (frontier_commutator_N_le_L₀ hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
      hmodel)

end

end CFSG.Semidihedral.AllPrime

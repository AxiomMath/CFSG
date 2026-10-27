module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6D4T2Shape
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Inner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6D4T2Tab

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4T

set_option maxRecDepth 100000

structure E6D4T2Std {L : Type}
    [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ) (i : KernelComponent (rootCharHom a)) where
  v : WeylGroup Tag.E6
  hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)
  hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i
  hker : componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a)

section Std

theorem e6d4t2_three_ne_zero {L : Type} [Field L] [CharP L 2] : ((3 : ℕ) : L) ≠ 0 := by
  have h3 : ((3 : ℕ) : L) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, CharP.cast_eq_zero L 2, zero_add, Nat.cast_one]
  rw [h3]
  exact one_ne_zero

theorem e6d4t2_diag_pow_three {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    (hap : ∀ j, a j ^ 3 = 1) :
    rootDiagUnit Tag.E6 a ^ 3 = 1 := by
  have h1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
    (rootDiagUnitHom Tag.E6 L).map_pow a 3
  have h2 : a ^ 3 = 1 := funext fun j => by rw [Pi.pow_apply, hap j, Pi.one_apply]
  rw [← h1, h2, CFSG.LieType.Chevalley.rootDiagUnit_one]

theorem e6d4t2_exists_std
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (hk24 : (kernelRoots (rootCharHom a)).ncard = 24) (i : KernelComponent (rootCharHom a)) :
    Nonempty (E6D4T2Std S a i) := by
  have h3 : ((3 : ℕ) : L) ≠ 0 := e6d4t2_three_ne_zero
  obtain ⟨hr, hc⟩ := d4t2_class_of_card h3 hap hk24 i
  have hker : componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) :=
    Set.eq_of_subset_of_ncard_le (componentRoots_subset_kernelRoots _ i)
      (by rw [hc, hk24]) (finite_kernelRoots_E6 _)
  obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime Nat.prime_three h3 facts_E6 kacCount_E6_four
    (by decide) (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT
    (e6d4t2_diag_pow_three hap) i hr hc
  exact ⟨⟨v, hv, hρ, hker⟩⟩

theorem e6d4t2_rootChar_std
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} {S : LangSetup Tag.E6 L p₀}
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    {i : KernelComponent (rootCharHom a)} (std : E6D4T2Std S a i) :
    ∃ z : Lˣ, z ^ 3 = 1 ∧ z ≠ 1 ∧ ∀ x, rootChar a (std.v • x) = z ^ (x 0 + x 5) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hΨ := std.hΨ
  have hall : kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i :=
    fun γ hγ => std.hker ▸ hγ
  set v := std.v with hv
  have hker : ∀ γ, IsRoot .E6 γ → rootChar a (v • γ) = 1 →
      γ ∈ parabolicRoots .E6 (d4Nodes .E6) := by
    intro γ hγ h1
    have hmem : v • γ ∈ componentRoots (rootCharHom a) i :=
      hall ⟨(isRoot_smul_iff v).2 hγ, h1⟩
    rw [hΨ] at hmem
    obtain ⟨α, hα, hαe⟩ := hmem
    rwa [(smul_left_cancel_iff v).1 hαe] at hα
  have hJ : ∀ j ∈ d4Set .E6, rootChar a (v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = 1 := by
    intro j hj
    have hmem : v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨_, single_mem_parabolicRoots hj, rfl⟩
    exact hmem.1.2
  have hout : ∀ γ, IsRoot .E6 γ → γ 0 ≠ 0 → rootChar a (v • γ) ≠ 1 := fun γ hγ h0 h1 =>
    h0 ((hker γ hγ h1).2 0 fun h => absurd h.1 (by decide))
  have hout5 : ∀ γ, IsRoot .E6 γ → γ 5 ≠ 0 → rootChar a (v • γ) ≠ 1 := fun γ hγ h0 h1 =>
    h0 ((hker γ hγ h1).2 5 fun h => absurd h.2 (by decide))
  have hcube : ∀ x, rootChar a x ^ 3 = 1 := fun x => by
    rw [rootChar, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap j, one_zpow]
  obtain ⟨z, hz⟩ : ∃ z, rootChar a (v • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) = z := ⟨_, rfl⟩
  have hz1 : z ≠ 1 := hz ▸ hout _ (IsRoot.basis 0) (by decide)
  have hz5 : rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) ≠ 1 :=
    hout5 _ (IsRoot.basis 5) (by decide)
  have hγ : IsRoot .E6 (Pi.single 0 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 +
      Pi.single 5 1 : Fin Tag.E6.rank → ℤ) := by
    have e : (Pi.single 0 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1 :
        Fin Tag.E6.rank → ℤ) =
        reflect .E6 0 (reflect .E6 2 (reflect .E6 3 (reflect .E6 4 (Pi.single 5 1)))) := by
      decide +kernel
    rw [e]
    exact .reflect _ (.reflect _ (.reflect _ (.reflect _ (.basis _))))
  have h05 : z * rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) ≠ 1 := by
    have h := hout _ hγ (by decide)
    simp only [smul_add, rootChar_add, hJ 2 ⟨by decide, by decide⟩, hJ 3 ⟨by decide, by decide⟩,
      hJ 4 ⟨by decide, by decide⟩, mul_one, hz] at h
    exact h
  have hq3 : ∀ y : Lˣ, y ^ 3 = 1 → y ≠ 1 → (y : L) ^ 2 + y + 1 = 0 := by
    intro y h3 h1
    have h3' : (y : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
    have h1' : (y : L) ≠ 1 := fun h => h1 (Units.ext h)
    have : ((y : L) - 1) * ((y : L) ^ 2 + y + 1) = 0 := by linear_combination h3'
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1')
  have hz5' : rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ)) = z := by
    have e0 := hq3 z (hz ▸ hcube _) hz1
    have e5 := hq3 _ (hcube _) hz5
    set y := rootChar a (v • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ))
    have : ((y : L) - z) * ((y : L) + z + 1) = 0 := by linear_combination e5 - e0
    rcases mul_eq_zero.1 this with h | h
    · exact Units.ext (sub_eq_zero.1 h)
    · refine absurd (Units.ext ?_) h05
      rw [Units.val_mul, Units.val_one]
      linear_combination (z : L) * h - e0
  have hcJ : ∀ c : Fin Tag.E6.rank, c ≠ 0 → c ≠ 5 → 1 ≤ c.val ∧ c.val ≤ 4 := by decide
  refine ⟨z, hz ▸ hcube _, hz1, fun x => ?_⟩
  rw [d4t2out_rootChar_smul a v x, Finset.prod_eq_mul (0 : Fin Tag.E6.rank) 5 (by decide)
    (fun c _ hc => by rw [hJ c (hcJ c hc.1 hc.2), one_zpow])
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h),
    hz, hz5', zpow_add]

@[expose] def e6d4t2WSig
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) : Subgroup (WeylGroup Tag.E6) :=
  Subgroup.closure ((fun α => rootReflection α) '' kernelRoots (rootCharHom a))

theorem e6d4t2_kernelReflectionGroup_le
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) :
    kernelReflectionGroup a ≤ e6d4t2WSig a := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, j, hα, rfl⟩
  exact Subgroup.subset_closure ⟨_, hα, rootReflection_eq_conj rfl⟩

theorem e6d4t2_conj_mem
    {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ} {u : WeylGroup Tag.E6}
    (hu : ∀ γ ∈ kernelRoots (rootCharHom a), u • γ ∈ kernelRoots (rootCharHom a))
    {x : WeylGroup Tag.E6} (hx : x ∈ e6d4t2WSig a) : u * x * u⁻¹ ∈ e6d4t2WSig a := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨u • γ, hu γ hγ, ?_⟩
    exact rootReflection_smul_root u hγ.1
  | one => simpa using one_mem _
  | mul x y _ _ hx hy =>
    have : u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem e6d4t2_rootChar_t
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} {S : LangSetup Tag.E6 L p₀}
    {a : Fin Tag.E6.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    (std : E6D4T2Std S a i) {z : Lˣ}
    (hz : ∀ x, rootChar a (std.v • x) = z ^ (x 0 + x 5)) (x : Fin Tag.E6.rank → ℤ) :
    rootChar a ((std.v * e6d4t2W0 * std.v⁻¹) • x) = (rootChar a x)⁻¹ := by
  have h1 : (std.v * e6d4t2W0 * std.v⁻¹) • x = std.v • (e6d4t2W0 • (std.v⁻¹ • x)) := by
    simp only [mul_smul]
  have hx := hz (std.v⁻¹ • x)
  rw [smul_inv_smul] at hx
  have e0 : e6Graph.symm 0 = 5 := by decide
  have e5 : e6Graph.symm 5 = 0 := by decide
  rw [h1, hz, e6d4t2_w0_smul, hx, ← zpow_neg]
  congr 1
  simp only [Pi.neg_apply, permLattice, Function.comp_apply, e0, e5]
  ring

theorem e6d4t2_centralizer_kernel
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} {S : LangSetup Tag.E6 L p₀}
    {a : Fin Tag.E6.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    (std : E6D4T2Std S a i) {Z : WeylGroup Tag.E6}
    (hZ : ∀ γ ∈ kernelRoots (rootCharHom a), Z • γ = γ) : Z = 1 := by
  have h1 : std.v⁻¹ * Z * std.v = 1 := by
    refine e6d4t2_centralizer_trivial fun j hj => ?_
    have hmem : std.v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ kernelRoots (rootCharHom a) := by
      rw [← std.hker, std.hΨ]
      exact ⟨_, single_mem_parabolicRoots hj, rfl⟩
    rw [mul_smul, mul_smul, hZ _ hmem, inv_smul_smul]
  have : Z = std.v * (std.v⁻¹ * Z * std.v) * std.v⁻¹ := by group
  rw [this, h1]
  group

end Std

end CFSG.LocalAnalysis.GLTheoremA.T158

end

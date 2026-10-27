module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.E0Elements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoLang
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoCent
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.RankOneFixed

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem exists_pow_isPGroup_three {G : Type*} [Group G] [Finite G] (x : G) :
    ∃ m : ℕ, m % 3 = 1 ∧ IsPGroup 3 (Subgroup.zpowers (x ^ m)) := by
  obtain ⟨s, u, hu, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  refine ⟨u * u, ?_, ?_⟩
  · have : u % 3 = 1 ∨ u % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  · have hpow : (x ^ (u * u)) ^ (3 ^ s) = 1 := by
      rw [← pow_mul, show u * u * 3 ^ s = orderOf x * u by rw [hN]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
    have hdvd : orderOf (x ^ (u * u)) ∣ 3 ^ s := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, hk]

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂]
  {σ : K₂ ≃+* K₂}

theorem QPlusModel.exists_twistEmb_eq (M : QPlusModel K σ) {t : ModGL .G2 K₂}
    (ht : t ∈ M.gamma) : ∃ x : adjointGroup .G2 K, twistEmb (K := K) M.g x = t := by
  have : t ∈ (⊤ : Subgroup (adjointGroup .G2 K)).map (twistEmb (K := K) M.g) := by
    rw [map_twistEmb_top]; exact ht
  obtain ⟨x, -, hx⟩ := this
  exact ⟨x, hx⟩

theorem QPlusModel.torusTorsion_three_le_gamma (M : QPlusModel K σ)
    (hσ : ∀ c, σ c = c ^ Nat.card K) (h3 : 3 ∣ Nat.card K + 1) :
    torusTorsion K₂ 3 ≤ M.gamma := fun t ht => by
  have := torusTorsion_mono h3 ht
  rw [← M.torus_inf_gamma hσ] at this
  exact this.2

abbrev QPlusModel.E0G (M : QPlusModel K σ) : Subgroup (adjointGroup .G2 K) :=
  (torusTorsion K₂ 3).comap (twistEmb (K := K) M.g)

theorem QPlusModel.pow_three_eq_one_of_mem_E0G (M : QPlusModel K σ)
    {x : adjointGroup .G2 K} (hx : x ∈ M.E0G) : x ^ 3 = 1 := by
  apply twistEmb_injective (K := K) M.g
  rw [map_pow, map_one]
  exact (mem_torusTorsion_iff.1 hx).2

theorem QPlusModel.isPGroup_E0G (M : QPlusModel K σ) : IsPGroup 3 M.E0G := fun g =>
  ⟨1, Subtype.ext (by simpa using M.pow_three_eq_one_of_mem_E0G g.2)⟩

theorem QPlusModel.exists_rho0_element (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) :
    ∃ x : adjointGroup .G2 K, ∃ h : twistEmb (K := K) M.g x ∈ monomialSubgroup .G2 K₂,
      weylQuotientHom .G2 K₂ ⟨_, h⟩ = rho0 := by
  have ha0 : IsRoot .G2 (vec 1 0) := isRoot_of_mem_rootList (by decide)
  have h30 : IsRoot .G2 (vec 1 3) := isRoot_of_mem_rootList (by decide)
  obtain ⟨cα, hcαΓ, hcαm, hcαw⟩ := M.exists_fixed_weyl hdeg hσ ha0
  obtain ⟨cβ, hcβΓ, hcβm, hcβw⟩ := M.exists_fixed_weyl hdeg hσ h30
  obtain ⟨x₀, hx₀⟩ := M.exists_twistEmb_eq (mul_mem hcαΓ hcβΓ)
  have hmono : twistEmb (K := K) M.g x₀ ∈ monomialSubgroup .G2 K₂ := by
    rw [hx₀]; exact mul_mem hcαm hcβm
  refine ⟨x₀, hmono, ?_⟩
  have : (⟨twistEmb (K := K) M.g x₀, hmono⟩ : monomialSubgroup .G2 K₂) =
      ⟨_, hcαm⟩ * ⟨_, hcβm⟩ := Subtype.ext hx₀
  rw [this, map_mul, hcαw, hcβw]
  rfl

theorem QPlusModel.exists_sylow_E0G (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {ζ : K₂ˣ} (hζ : orderOf ζ = 3) :
    ∃ (P₀ : Sylow 3 (adjointGroup .G2 K)) (n : adjointGroup .G2 K),
      M.E0G ≤ P₀ ∧ n ∈ P₀ ∧
        ∃ h : twistEmb (K := K) M.g n ∈ monomialSubgroup .G2 K₂,
          weylQuotientHom .G2 K₂ ⟨_, h⟩ = rho0 := by
  have : Finite (Module.End K₂ (RootModule .G2 K₂)) := Module.finite_of_finite K₂
  have hfin : Finite (adjointGroup .G2 K) := by
    have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
    infer_instance
  obtain ⟨x₀, hx₀m, hx₀w⟩ := M.exists_rho0_element hdeg hσ
  obtain ⟨m, hm1, hmP⟩ := exists_pow_isPGroup_three x₀
  set n := x₀ ^ m with hn
  have hnm : twistEmb (K := K) M.g n ∈ monomialSubgroup .G2 K₂ := by
    rw [hn, map_pow]; exact pow_mem hx₀m m
  have hnw : weylQuotientHom .G2 K₂ ⟨_, hnm⟩ = rho0 := by
    have : (⟨twistEmb (K := K) M.g n, hnm⟩ : monomialSubgroup .G2 K₂) =
        ⟨_, hx₀m⟩ ^ m := by
      apply Subtype.ext
      have h : twistEmb (K := K) M.g n = (twistEmb (K := K) M.g x₀) ^ m := by
        rw [hn, map_pow]
      exact h
    rw [this, map_pow, hx₀w, ← pow_mod_orderOf, orderOf_rho0, hm1, pow_one]
  have hconj : ∀ k : ℕ, ∀ y ∈ M.E0G, n ^ k * y * (n ^ k)⁻¹ ∈ M.E0G := by
    intro k y hy
    obtain ⟨i, j, hij⟩ := exists_cubeTuple3_of_mem_torusTorsion hζ hy
    have := conj_pow_cubeTuple3 hζ hnm hnw i j k
    show twistEmb (K := K) M.g (n ^ k * y * (n ^ k)⁻¹) ∈ torusTorsion K₂ 3
    rw [map_mul, map_mul, map_inv, map_pow, hij, this]
    exact rootDiagUnit_cubeTuple3_mem_torusTorsion hζ _ _
  have hconj' : ∀ g ∈ Subgroup.zpowers n, ∀ y ∈ M.E0G, g * y * g⁻¹ ∈ M.E0G := by
    intro g hg y hy
    obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.2 hg
    exact hconj k y hy
  have hnorm : Subgroup.zpowers n ≤ Subgroup.normalizer (M.E0G : Set _) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj' g hg y hy, fun hy => ?_⟩
    have := hconj' g⁻¹ (inv_mem hg) _ hy
    simpa [mul_assoc] using this
  have hS := hmP.to_sup_of_normal_right' M.isPGroup_E0G hnorm
  obtain ⟨P₀, hP₀⟩ := hS.exists_le_sylow
  exact ⟨P₀, n, le_trans le_sup_right hP₀, hP₀ (Subgroup.mem_sup_left (Subgroup.mem_zpowers n)), hnm, hnw⟩

theorem QPlusModel.twistEmb_mem_gamma (M : QPlusModel K σ) (x : adjointGroup .G2 K) :
    twistEmb (K := K) M.g x ∈ M.gamma := by
  show _ ∈ conjEntrywiseImage K M.g
  rw [← map_twistEmb_top]
  exact Subgroup.mem_map_of_mem _ trivial

theorem cube_root_facts {ζ : K₂ˣ} (hζ : orderOf ζ = 3) :
    (ζ : K₂) ^ 2 + ζ + 1 = 0 ∧ (ζ : K₂) ≠ 1 := by
  have hprim : IsPrimitiveRoot (ζ : K₂) 3 := by
    have := IsPrimitiveRoot.orderOf ζ
    rw [hζ] at this
    exact IsPrimitiveRoot.coe_units_iff.2 this
  refine ⟨?_, hprim.ne_one (by norm_num)⟩
  have := hprim.geom_sum_eq_zero (by norm_num)
  simp [Finset.sum_range_succ] at this
  linear_combination this

theorem fin3_add_eq_right : ∀ i j : Fin 3, i + j = j → i = 0 := by decide

theorem QPlusModel.central_mem_E0 (M : QPlusModel K σ) (hσ : ∀ c, σ c = c ^ Nat.card K)
    (h3 : 3 ∣ Nat.card K + 1) {ζ : K₂ˣ} (hζ : orderOf ζ = 3)
    {P₀ : Sylow 3 (adjointGroup .G2 K)} {n : adjointGroup .G2 K}
    (hE : M.E0G ≤ (P₀ : Subgroup (adjointGroup .G2 K))) (hnP : n ∈ P₀)
    (hnm : twistEmb (K := K) M.g n ∈ monomialSubgroup .G2 K₂)
    (hnw : weylQuotientHom .G2 K₂ ⟨_, hnm⟩ = rho0)
    {z : adjointGroup .G2 K} (hzc : ∀ x ∈ P₀, x * z = z * x) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    ∃ j : Fin 3, j ≠ 0 ∧ twistEmb (K := K) M.g z = rootDiagUnit .G2 (cubeTuple3 ζ 0 j) := by
  obtain ⟨hω, hω1⟩ := cube_root_facts hζ
  have hzA : twistEmb (K := K) M.g z ∈ adjointGroup .G2 K₂ := by
    have := M.twistEmb_mem_gamma z
    rw [M.gamma_eq_fixed hσ] at this
    exact this.1
  have hcomm : ∀ x ∈ torusTorsion K₂ 3, twistEmb (K := K) M.g z * x = x * twistEmb (K := K) M.g z := by
    intro t ht
    obtain ⟨x, hx⟩ := M.exists_twistEmb_eq (M.torusTorsion_three_le_gamma hσ h3 ht)
    have hxE : x ∈ M.E0G := by
      show twistEmb (K := K) M.g x ∈ torusTorsion K₂ 3
      rw [hx]; exact ht
    rw [← hx, ← map_mul, ← map_mul, hzc x (hE hxE)]
  have hT := centralizer_torusTorsion_three_le (ζ : K₂) hω hω1 _ hzA hcomm
  have hz3' : twistEmb (K := K) M.g z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  obtain ⟨i, j, hij⟩ := exists_cubeTuple3_of_mem_torusTorsion hζ
    (mem_torusTorsion_iff.2 ⟨hT, hz3'⟩)
  have hn := hzc n hnP
  have hcn : twistEmb (K := K) M.g n * twistEmb (K := K) M.g z *
      (twistEmb (K := K) M.g n)⁻¹ = twistEmb (K := K) M.g z := by
    rw [← map_mul, hn, map_mul, mul_assoc, mul_inv_cancel, mul_one]
  rw [hij, conj_cubeTuple3 hζ hnm hnw] at hcn
  have hc := (cubeTuple3_injective hζ (rootDiagUnit_injective hcn)).2
  have hi : i = 0 := fin3_add_eq_right i j hc
  subst hi
  refine ⟨j, ?_, hij⟩
  rintro rfl
  apply hz1
  apply twistEmb_injective (K := K) M.g
  rw [hij, cubeTuple3_zero, rootDiagUnit_one, map_one]

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

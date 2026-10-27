module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeTIFacts.Frontier
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data
import CFSG.CharacterTheory.Semidihedral.AllPrimeTIFacts
import CFSG.LocalAnalysis.ABGTheoremB.IV9Reflection
import CFSG.CharacterTheory.Semidihedral.AllPrimeIV9ReflectionArith
import CFSG.CharacterTheory.Semidihedral.MatrixInvertedOddElements
import CFSG.CharacterTheory.Semidihedral.InvertedOrderSixteen
import CFSG.LocalAnalysis.ABGTheoremB.IV9SylowK
public import CFSG.CharacterTheory.Semidihedral.AllPrimeLayerFacts

public section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open CFSG.Semidihedral.MatrixTorus CFSG.Wreathed.OriginalAllPrime.TIFacts

private theorem frontier_v_facts {G : Type} [Group G] {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    ∃ v ∈ (frontierSetting S fS t p f).D, v * v = (frontierSetting S fS t p f).x ∧
      (frontierSetting S fS t p f).x₂ * v * (frontierSetting S fS t p f).x₂⁻¹ = v⁻¹ := by
  set ι := FocalFusion.ambientHom n (S : Subgroup G) fS with hι
  have := sdFourSubgroup_isKleinFour hn
  refine ⟨ι (r n ^ 2 ^ (n - 3)), ?_, ?_, ?_⟩
  · rw [frontierSetting_D hn S fS t ht p f]
    exact Subgroup.mem_map_of_mem _ (sd_kleinFour_facts hn (sdFourSubgroup n)).2.2.1
  · change ι (r n ^ 2 ^ (n - 3)) * ι (r n ^ 2 ^ (n - 3)) = t
    have e : 2 ^ (n - 3) + 2 ^ (n - 3) = 2 ^ (n - 2) := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    rw [← map_mul, ← pow_add, e, map_pow, ht]
    rfl
  · change ι (s n) * ι (r n ^ 2 ^ (n - 3)) * (ι (s n))⁻¹ = (ι (r n ^ 2 ^ (n - 3)))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, sd_s_conj_quarter hn, map_inv]

private theorem exists_commutator_of_inverted {G : Type} [Group G]
    {σ : CFSG.ABGTheoremB.Setting G} {F : Type} [Field F] {A : Subgroup (F ≃+* F)} {a : Fˣ}
    {hfix : ∀ τ : A, (τ : F ≃+* F) (a : F) = a} {φ : σ.N →* OriginalH F a A hfix}
    (hφ : IsModelMap σ φ (QDTI.layerM F a A hfix) (originalU F a A hfix))
    {Y : Matrix.SpecialLinearGroup (Fin 2) F} (hY : MatrixCoverData.beta F a Y = Y⁻¹)
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hYs : orderOf Y = s) :
    ∃ g ∈ σ.N, (σ.x₂ * g * σ.x₂⁻¹ * g⁻¹) ^ s ∈ σ.ON ∧ σ.x₂ * g * σ.x₂⁻¹ * g⁻¹ ∉ σ.ON := by
  obtain ⟨g, hg⟩ := hφ.surjective (originalSlInH F a A hfix Y)
  set x₂N : σ.N := ⟨σ.x₂, hφ.x₂_mem⟩ with hx₂N
  set c : σ.N := x₂N * g * x₂N⁻¹ * g⁻¹ with hc
  have hφc : φ c = originalSlInH F a A hfix (Y⁻¹ * Y⁻¹) := by
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, hg, hφ.map_x₂, QDTI.conj_u_slIn, hY,
      ← map_inv, ← map_mul]
  have hmem : ∀ z : σ.N, (z : G) ∈ σ.ON ↔ φ z = 1 := by
    intro z
    rw [← MonoidHom.mem_ker, hφ.ker_eq, Subgroup.mem_subgroupOf]
  have hYY : Y⁻¹ * Y⁻¹ = (Y ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
  refine ⟨g, g.2, ?_, ?_⟩
  · have h : ((c ^ s : σ.N) : G) ∈ σ.ON := by
      rw [hmem, map_pow, hφc, ← map_pow, hYY, inv_pow, ← pow_mul, mul_comm, pow_mul, ← hYs,
        pow_orderOf_eq_one, one_pow, inv_one, map_one]
    simpa [hc, hx₂N] using h
  · intro h
    have h' : (c : G) ∈ σ.ON := by simpa [hc, hx₂N] using h
    rw [hmem, hφc, ← map_one (originalSlInH F a A hfix)] at h'
    have h2 : Y ^ 2 = 1 := by
      rw [← inv_eq_one, ← hYY]
      exact QDTI.slIn_injective h'
    have hdvd : s ∣ 2 := hYs ▸ orderOf_dvd_of_pow_eq_one h2
    exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp hdvd)

private theorem frontier_II510_of_sq_lt {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
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
    {ℓ : ℕ} (hℓ : (frontierSetting S fS t p f).HypIV7 ℓ)
    (d : (frontierSetting S fS t p f).IV7Data ℓ) {W : Subgroup G}
    (hKW : Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G))
    (hCW : Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
      solvRadIn (Subgroup.normalizer (d.R : Set G)))
    (hrefl : (W ⊓ Subgroup.centralizer {(frontierSetting S fS t p f).x₂}).relIndex W = ℓ)
    (hbig : ℓ ^ 2 < Nat.card W) (hexc : ¬ ((ℓ = 3 ∨ ℓ = 5) ∧ 8 ∣ p ^ f - 1)) :
    ∃ u ∈ Subgroup.normalizer (d.R : Set G), ∃ s k : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ ℓ ∧
      u ^ (s ^ k) ∈ Subgroup.centralizer (W : Set G) ∧
      u ∉ Subgroup.centralizer (W : Set G) ∧
      (frontierSetting S fS t p f).x₂ * u * (frontierSetting S fS t p f).x₂⁻¹ * u ∈
        Subgroup.centralizer (W : Set G) ∧
      ∃ a ∈ W ⊓ Subgroup.centralizer {(frontierSetting S fS t p f).x₂}, a ≠ 1 ∧
        u * a = a * u := by
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  have hN := frontier_nStructure hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel
  have hZ : centerOf ((frontierSetting S fS t p f).S : Subgroup G) ≤
      Subgroup.zpowers (frontierSetting S fS t p f).x :=
    (frontierSetting_centerOf_S hn S fS t ht p f).le
  obtain ⟨F, hF, hFfin, A, a, hfix, Psi, hcard, -, -, ha, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact absurd hpodd (by decide)
  have hℓ2 : ℓ ≠ 2 := fun h => by
    have hdvd := hℓ.dvd_ON
    rw [h] at hdvd
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn (frontierSetting S fS t p f).N))
      (even_iff_two_dvd.mpr hdvd)
  have hodd : Odd (Nat.card F) := hcard ▸ hpodd.pow
  obtain ⟨s, hs, hs2, hsℓ, Y, hY, hYs⟩ : ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ ℓ ∧
      ∃ Y : Matrix.SpecialLinearGroup (Fin 2) F, MatrixCoverData.beta F a Y = Y⁻¹ ∧
        orderOf Y = s := by
    rcases iv9Reflection_prime_cases hp hp2 hq hℓ.prime hℓ2 with
      ⟨s, hs, hs2, hsℓ, hdvd⟩ | ⟨s, hs, hs2, hsℓ, hdvd⟩ | ⟨hq3, hpℓ⟩ | hex
    · obtain ⟨Y, hY, hYs⟩ := exists_beta_eq_inv_orderOf a ha hodd hs hs2
        (Or.inl (hcard ▸ hdvd))
      exact ⟨s, hs, hs2, hsℓ, Y, hY, hYs⟩
    · obtain ⟨Y, hY, hYs⟩ := exists_beta_eq_inv_orderOf a ha hodd hs hs2
        (Or.inr (Or.inl (hcard ▸ hdvd)))
      exact ⟨s, hs, hs2, hsℓ, Y, hY, hYs⟩
    · have hchar : CharP F p := qdti_charP hp hcard
      obtain ⟨Y, hY, hYs⟩ := exists_beta_eq_inv_orderOf a ha hodd hp hp2
        (Or.inr (Or.inr ⟨hcard ▸ hq3, hchar⟩))
      exact ⟨p, hp, hp2, hpℓ, Y, hY, hYs⟩
    · exact absurd hex hexc
  obtain ⟨g, hgN, hgs, hg1⟩ := exists_commutator_of_inverted hφ hY hs hs2 hYs
  exact Setting.reflection_element_of_commutator hσ hN hZ hℓ d hKW hCW hrefl hbig hs hs2 hsℓ hgN
    hgs hg1

private theorem exists_order_sixteen_of_eight_dvd {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (h8 : 8 ∣ p ^ f - 1) {ℓ : ℕ} (hℓ : (frontierSetting S fS t p f).HypIV7 ℓ)
    (d : (frontierSetting S fS t p f).IV7Data ℓ) :
    ∃ ρ ∈ Subgroup.normalizer (d.R : Set G), ρ ∈ (frontierSetting S fS t p f).N ∧
      ((frontierSetting S fS t p f).x₂ * ρ * (frontierSetting S fS t p f).x₂⁻¹ * ρ = 1 ∨
        (frontierSetting S fS t p f).x₂ * ρ * (frontierSetting S fS t p f).x₂⁻¹ * ρ =
          (frontierSetting S fS t p f).x) ∧
      ρ ^ 8 = (frontierSetting S fS t p f).x ∧ orderOf (ρ ^ 4) = 4 := by
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  obtain ⟨-, ht2, -, -, hs2, hst⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨F', _, _, A', rho', data'⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  have h2part := data'.two_part
  rw [data'.field_card] at h2part
  have hn5 : 5 ≤ n := by
    obtain ⟨m, hm⟩ : ∃ m, p ^ f = m + 1 := ⟨p ^ f - 1, by omega⟩
    have e : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
      rw [hm, Nat.add_sub_cancel, show (m + 1) ^ 2 = m * (m + 2) + 1 by ring, Nat.add_sub_cancel]
    have h2 : 2 ∣ p ^ f + 1 := even_iff_two_dvd.mp hpodd.pow.add_one
    have h16 : 2 ^ 4 ∣ (p ^ f) ^ 2 - 1 := by
      rw [e, show (2 : ℕ) ^ 4 = 8 * 2 by norm_num]
      exact Nat.mul_dvd_mul h8 h2
    have hne : (p ^ f) ^ 2 - 1 ≠ 0 := by
      rw [e]
      exact Nat.mul_ne_zero (by omega) (by omega)
    have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hne).mp h16
    have heq := Nat.pow_right_injective (le_refl 2) h2part
    omega
  obtain ⟨S₁, hDS₁, hS₁K⟩ := Setting.exists_sylow_two_between_D_and_normalizer_R _ hσ hℓ d
  set e : SemidihedralGroup n ≃* (S₁ : Subgroup G) := fS.trans (Sylow.equiv S S₁) with he
  set ι₁ := FocalFusion.ambientHom n (S₁ : Subgroup G) e with hι₁
  have hinj : Function.Injective ι₁ := FocalFusion.ambientHom_injective n _ e
  have hz₁ : ι₁ (z n) = t := frontier_sylow_z_eq hn S fS t ht p f _ e hDS₁
  have hx₂D : (fS (s n) : G) ∈ (frontierSetting S fS t p f).D :=
    (frontierSetting S fS t p f).T_le_D hσ (frontierSetting S fS t p f).x₂_mem_T
  have hx₂S₁ : (fS (s n) : G) ∈ (S₁ : Subgroup G) := hDS₁ hx₂D
  set a : SemidihedralGroup n := e.symm ⟨(fS (s n) : G), hx₂S₁⟩ with ha
  have hιa : ι₁ a = (fS (s n) : G) := by
    change ((e (e.symm ⟨(fS (s n) : G), hx₂S₁⟩) : (S₁ : Subgroup G)) : G) = _
    rw [MulEquiv.apply_symm_apply]
  have ha2 : orderOf a = 2 := by rw [← orderOf_injective ι₁ hinj a, hιa, hs2]
  have haz : a ≠ z n := fun h => hst (by rw [← hιa, h, hz₁])
  obtain ⟨ρ₀, hinv₀, h8₀, h4₀⟩ := exists_inverted_order_sixteen hn5 a ha2 haz
  have hρS₁ : ι₁ ρ₀ ∈ (S₁ : Subgroup G) := ambientHom_mem _ e ρ₀
  refine ⟨ι₁ ρ₀, (hS₁K hρS₁).1, (hS₁K hρS₁).2, ?_, ?_, ?_⟩
  · have key : ι₁ (a * ρ₀ * a⁻¹ * ρ₀) =
        (fS (s n) : G) * ι₁ ρ₀ * (fS (s n) : G)⁻¹ * ι₁ ρ₀ := by
      rw [map_mul, map_mul, map_mul, map_inv, hιa]
    change (fS (s n) : G) * ι₁ ρ₀ * (fS (s n) : G)⁻¹ * ι₁ ρ₀ = 1 ∨
      (fS (s n) : G) * ι₁ ρ₀ * (fS (s n) : G)⁻¹ * ι₁ ρ₀ = t
    rw [← key]
    rcases hinv₀ with h | h
    · left
      rw [h, map_one]
    · right
      rw [h, hz₁]
  · change ι₁ ρ₀ ^ 8 = t
    rw [← map_pow, h8₀, hz₁]
  · rw [← map_pow, orderOf_injective ι₁ hinj, h4₀]

theorem frontier_II510 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
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
    ∀ r : ℕ, (frontierSetting S fS t p f).HypIV7 r →
      ∀ d : (frontierSetting S fS t p f).IV7Data r, ∀ W : Subgroup G, W ≤ d.R →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
      (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) → (∀ w ∈ W, w ^ r = 1) →
      Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      (W ⊓ Subgroup.centralizer {(frontierSetting S fS t p f).x₂}).relIndex W = r →
      ∃ u ∈ Subgroup.normalizer (d.R : Set G), ∃ s k : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧
        u ^ (s ^ k) ∈ Subgroup.centralizer (W : Set G) ∧
        u ∉ Subgroup.centralizer (W : Set G) ∧
        (frontierSetting S fS t p f).x₂ * u * (frontierSetting S fS t p f).x₂⁻¹ * u ∈
          Subgroup.centralizer (W : Set G) ∧
        ∃ a ∈ W ⊓ Subgroup.centralizer {(frontierSetting S fS t p f).x₂}, a ≠ 1 ∧
          u * a = a * u := by
  intro ℓ hℓ d W hWR hKW hWab hWr hCW hrefl
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  have hN := frontier_nStructure hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel
  have hZ : centerOf ((frontierSetting S fS t p f).S : Subgroup G) ≤
      Subgroup.zpowers (frontierSetting S fS t p f).x :=
    (frontierSetting_centerOf_S hn S fS t ht p f).le
  obtain ⟨v, hvD, hv2, hvinv⟩ := frontier_v_facts hn S fS t ht p f
  have hbig := Setting.sq_lt_card_of_reflection hσ hN hZ hℓ d hWR hKW hWab hWr hCW hrefl hvD
    hv2 hvinv
  by_cases hexc : (ℓ = 3 ∨ ℓ = 5) ∧ 8 ∣ p ^ f - 1
  · exfalso
    obtain ⟨ρ, hρK, hρN, hρinv, hρ8, hρ4⟩ := exists_order_sixteen_of_eight_dvd hGnonab n hn S fS
      t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hexc.2 hℓ d
    exact Setting.false_of_order_sixteen hσ hN hZ hℓ d hWR hKW hWab hWr hCW hrefl hexc.1 hρK
      hρN hρinv hρ8 hρ4
  · exact frontier_II510_of_sq_lt hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
      hmodel hℓ d hKW hCW hrefl hbig hexc

end CFSG.Semidihedral.AllPrime

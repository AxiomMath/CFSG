module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts
import CFSG.RankThree.PartOne.AUTSL.Interface
import CFSG.RankThree.SubgroupLists.SchurCommutant
public import CFSG.RankThree.Classical2.MatrixFrobeniusLang
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace CaseBParts

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open CFSG.RankThree.Classical2 (twistedProd)
open scoped commutatorElement

section PartA

theorem l3ao_h1_pow_sub_pow_eq_mul {Q d i : ℕ} (h : i ≤ d) :
    Q ^ d - Q ^ i = Q ^ i * (Q ^ (d - i) - 1) := by
  rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' h]

theorem l3ao_h1_odd_prod_pow_sub_one {Q : ℕ} (hQ : Even Q) (hQ2 : 2 ≤ Q) (d : ℕ) :
    Odd (∏ i : Fin d, (Q ^ (d - (i : ℕ)) - 1)) := by
  refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun i _ => ?_
  have hi : d - (i : ℕ) ≠ 0 := by have := i.2; omega
  have hev : Even (Q ^ (d - (i : ℕ))) := hQ.pow_of_ne_zero hi
  have hpos : 1 ≤ Q ^ (d - (i : ℕ)) := Nat.one_le_pow _ _ (by omega)
  exact Nat.Even.sub_odd hpos hev odd_one

theorem l3ao_h1_sum_fin_val (d : ℕ) : ∑ i : Fin d, (i : ℕ) = d * (d - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) d, ← Finset.sum_range_id_mul_two d,
    Nat.mul_div_cancel _ two_pos]

theorem l3ao_h1_card_GL_eq_pow_mul_odd {K : Type} [Field K] [Finite K] {Q : ℕ}
    (hK : Nat.card K = Q) (hQ : Even Q) (hQ2 : 2 ≤ Q) (d : ℕ) :
    ∃ u, Odd u ∧ Nat.card (GL (Fin d) K) = Q ^ (d * (d - 1) / 2) * u := by
  have : Fintype K := Fintype.ofFinite K
  refine ⟨_, l3ao_h1_odd_prod_pow_sub_one hQ hQ2 d, ?_⟩
  rw [Matrix.card_GL_field, Fintype.card_eq_nat_card, hK, ← l3ao_h1_sum_fin_val,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => l3ao_h1_pow_sub_pow_eq_mul i.2.le

theorem l3ao_h1_padicValNat_two_card_GL {K : Type} [Field K] [Finite K] {e : ℕ}
    (hK : Nat.card K = 2 ^ e) (he : 1 ≤ e) (d : ℕ) :
    padicValNat 2 (Nat.card (GL (Fin d) K)) = e * (d * (d - 1) / 2) := by
  have hQ : Even (2 ^ e) := even_two.pow_of_ne_zero (by omega)
  have hQ2 : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ e := Nat.pow_le_pow_right two_pos he
  obtain ⟨u, hu, hcard⟩ := l3ao_h1_card_GL_eq_pow_mul_odd hK hQ hQ2 d
  rw [hcard, ← pow_mul, padicValNat.mul (by positivity) hu.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)),
    add_zero]

theorem l3ao_v2_card_GL {F : Type} [Field F] [Finite F] {e : ℕ} (hF : Nat.card F = 2 ^ e)
    (he : 1 ≤ e) (d : ℕ) :
    (Nat.card (GL (Fin d) F)).factorization 2 = e * (d * (d - 1) / 2) := by
  rw [Nat.factorization_def _ Nat.prime_two]
  exact l3ao_h1_padicValNat_two_card_GL hF he d

theorem l3ao_linearEquiv_mulEquiv_GL {F : Type} [Field F] [Finite F] (U : Type) [AddCommGroup U]
    [Module F U] [Module.Finite F U] :
    Nonempty ((U ≃ₗ[F] U) ≃* GL (Fin (Module.finrank F U)) F) := by
  let b : Module.Basis (Fin (Module.finrank F U)) F U := Module.finBasis F U
  exact ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv F U).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv)⟩

theorem l3ao_finite_linearEquiv {F : Type} [Field F] [Finite F] (U : Type) [AddCommGroup U]
    [Module F U] [Module.Finite F U] : Finite (U ≃ₗ[F] U) := by
  obtain ⟨φ⟩ := l3ao_linearEquiv_mulEquiv_GL (F := F) U
  haveI : Finite (GL (Fin (Module.finrank F U)) F) := inferInstance
  exact Finite.of_equiv _ φ.symm.toEquiv

theorem l3ao_v2_card_linearEquiv {F : Type} [Field F] [Finite F] {e : ℕ} (hF : Nat.card F = 2 ^ e)
    (he : 1 ≤ e) (U : Type) [AddCommGroup U] [Module F U] [Module.Finite F U] :
    (Nat.card (U ≃ₗ[F] U)).factorization 2 =
      e * (Module.finrank F U * (Module.finrank F U - 1) / 2) := by
  obtain ⟨φ⟩ := l3ao_linearEquiv_mulEquiv_GL (F := F) U
  rw [Nat.card_congr φ.toEquiv]
  exact l3ao_v2_card_GL hF he (Module.finrank F U)

end PartA

section PartB

variable {K : Type} [Field K]

theorem l3ao_stab_hom (H : Subgroup (SpecialLinearGroup (Fin 3) K)) (W : Submodule K (Fin 3 → K))
    (hW : ∀ g ∈ H, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) :
    ∃ θ : H →* (W ≃ₗ[K] W) × (((Fin 3 → K) ⧸ W) ≃ₗ[K] ((Fin 3 → K) ⧸ W)),
      ∀ g : H, θ g = 1 ↔
        (∀ w ∈ W, ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w) ∧
        ∀ v : Fin 3 → K,
          ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ W := by
  have hmap : ∀ g : H, W.map
      (SpecialLinearGroup.toLin' (g : SpecialLinearGroup (Fin 3) K)).toLinearMap = W := by
    intro g
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hW (g : SpecialLinearGroup (Fin 3) K) g.2 w hw
    · intro w hw
      refine Submodule.mem_map.mpr ⟨(SpecialLinearGroup.toLin' (g : SpecialLinearGroup (Fin 3) K)).symm w,
        ?_, (SpecialLinearGroup.toLin' (g : SpecialLinearGroup (Fin 3) K)).apply_symm_apply w⟩
      have h1 := hW ((g : SpecialLinearGroup (Fin 3) K)⁻¹) (H.inv_mem g.2) w hw
      rw [SpecialLinearGroup.toLin'_symm_apply, Matrix.toLin'_apply]
      exact h1
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ₁ : H →* (W ≃ₗ[K] W), ∀ (g : H) (w : W),
      ((θ₁ g w : W) : Fin 3 → K) =
        ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (w : Fin 3 → K) := by
    refine ⟨MonoidHom.mk' (fun g : H =>
      (SpecialLinearGroup.toLin' (g : SpecialLinearGroup (Fin 3) K)).ofSubmodules W W (hmap g)) ?_, ?_⟩
    · intro a b
      apply LinearEquiv.ext
      rintro ⟨x, hx⟩
      apply Subtype.ext
      simp [LinearEquiv.ofSubmodules_apply]
    · intro g w
      rfl
  obtain ⟨θ₂, hθ₂⟩ : ∃ θ₂ : H →* (((Fin 3 → K) ⧸ W) ≃ₗ[K] ((Fin 3 → K) ⧸ W)),
      ∀ (g : H) (v : Fin 3 → K), θ₂ g (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
    refine ⟨MonoidHom.mk' (fun g : H =>
      Submodule.Quotient.equiv W W (SpecialLinearGroup.toLin' (g : SpecialLinearGroup (Fin 3) K))
        (hmap g)) ?_, ?_⟩
    · intro a b
      apply LinearEquiv.ext
      intro x
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W x
      simp [Submodule.Quotient.equiv_apply]
    · intro g v
      rfl
  have hk1 : ∀ g : H, θ₁ g = 1 ↔
      ∀ w ∈ W, ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w := by
    intro g
    constructor
    · intro h w hw
      have h' : ((θ₁ g ⟨w, hw⟩ : W) : Fin 3 → K) = w :=
        congrArg Subtype.val (LinearEquiv.congr_fun h ⟨w, hw⟩)
      rw [hθ₁] at h'
      exact h'
    · intro h
      apply LinearEquiv.ext
      rintro ⟨w, hw⟩
      apply Subtype.ext
      rw [hθ₁]
      exact h w hw
  have hk2 : ∀ g : H, θ₂ g = 1 ↔
      ∀ v : Fin 3 → K, ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ W := by
    intro g
    constructor
    · intro h v
      have h' := LinearEquiv.congr_fun h (Submodule.Quotient.mk v)
      rw [hθ₂] at h'
      exact (Submodule.Quotient.eq W).mp h'
    · intro h
      apply LinearEquiv.ext
      intro x
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W x
      rw [hθ₂]
      exact (Submodule.Quotient.eq W).mpr (h v)
  refine ⟨θ₁.prod θ₂, fun g => ?_⟩
  rw [MonoidHom.prod_apply, Prod.mk_eq_one, hk1, hk2]

theorem l3ao_h2_apply_of_fix (W : Submodule K (Fin 3 → K)) (A B : Matrix (Fin 3) (Fin 3) K)
    (v : Fin 3 → K) (hA : ∀ w ∈ W, A *ᵥ w = w) (hB : B *ᵥ v - v ∈ W) :
    A *ᵥ (B *ᵥ v) = A *ᵥ v + (B *ᵥ v - v) := by
  calc A *ᵥ (B *ᵥ v) = A *ᵥ (v + (B *ᵥ v - v)) := by congr 1; abel
    _ = A *ᵥ v + A *ᵥ (B *ᵥ v - v) := Matrix.mulVec_add _ _ _
    _ = A *ᵥ v + (B *ᵥ v - v) := by rw [hA _ hB]

theorem l3ao_unip_comm (W : Submodule K (Fin 3 → K)) (g₁ g₂ : SpecialLinearGroup (Fin 3) K)
    (h₁W : ∀ w ∈ W, (g₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w)
    (h₁V : ∀ v : Fin 3 → K, (g₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ W)
    (h₂W : ∀ w ∈ W, (g₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w)
    (h₂V : ∀ v : Fin 3 → K, (g₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ W) :
    g₁ * g₂ = g₂ * g₁ := by
  have key : ∀ v : Fin 3 → K,
      (g₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        = (g₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
    intro v
    rw [l3ao_h2_apply_of_fix W _ _ v h₁W (h₂V v), l3ao_h2_apply_of_fix W _ _ v h₂W (h₁V v)]
    abel
  have hM : (g₁ : Matrix (Fin 3) (Fin 3) K) * (g₂ : Matrix (Fin 3) (Fin 3) K)
      = (g₂ : Matrix (Fin 3) (Fin 3) K) * (g₁ : Matrix (Fin 3) (Fin 3) K) := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact key _
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congrFun (congrFun hM i) j

theorem l3ao_scalar_eq_one (W : Submodule K (Fin 3 → K)) (hW : W ≠ ⊥)
    (g : SpecialLinearGroup (Fin 3) K) (hg : g ∈ LinearFlag.scalars 3 K)
    (hfix : ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w) : g = 1 := by
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.mp hg
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hcw : ((c : K) - 1) • w = 0 := by
    have h := hfix w hwW
    rw [hc, CFSG.RankThree.SubgroupLists.scalar_mulVec_eq_smul] at h
    rw [sub_smul, one_smul, h, sub_self]
  have hc1 : (c : K) = 1 := by
    rcases smul_eq_zero.mp hcw with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw0
  have hmat : (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hc, hc1, map_one]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congrFun (congrFun hmat i) j

theorem l3ao_h2_map_subtype_top {G : Type} [Group G] (S : Subgroup G) :
    Subgroup.map S.subtype (⊤ : Subgroup S) = S := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem l3ao_perfect_of_simple {G : Type} [Group G] (S : Subgroup G) (hS : IsSimpleGroup S)
    (hnc : ¬ ∀ a b : S, a * b = b * a) : ⁅S, S⁆ = S := by
  rcases Subgroup.Normal.eq_bot_or_eq_top
      (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S) with hbot | htop
  · exfalso
    apply hnc
    intro a b
    have hab := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hbot, Subgroup.mem_bot] at hab
    exact commutatorElement_eq_one_iff_mul_comm.mp hab
  · have h1 := congrArg (Subgroup.map S.subtype) htop
    rw [Subgroup.map_commutator, l3ao_h2_map_subtype_top] at h1
    exact h1

theorem l3ao_irreducible [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ (2 * f))
    (H : Subgroup (SpecialLinearGroup (Fin 3) K)) (S : Subgroup (LinearFlag.projectiveSL 3 K))
    (hS : IsSimpleGroup S) (hnc : ¬ ∀ a b : S, a * b = b * a)
    (hHS : ∀ h ∈ H, LinearFlag.proj 3 K h ∈ S)
    (hSH : ∀ s ∈ S, ∃ h ∈ H, LinearFlag.proj 3 K h = s)
    (hv2 : 3 * f ≤ (Nat.card S).factorization 2)
    (W : Submodule K (Fin 3 → K))
    (hW : ∀ g ∈ H, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hbot, htop⟩ := hcon
  obtain ⟨θ, hθ⟩ := l3ao_stab_hom H W hW
  let ψ : H →* S :=
    { toFun := fun h => ⟨LinearFlag.proj 3 K (h : SpecialLinearGroup (Fin 3) K), hHS h h.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  have hψsurj : Function.Surjective ψ := fun s => by
    obtain ⟨h, hh, hs⟩ := hSH s s.2
    exact ⟨⟨h, hh⟩, Subtype.ext hs⟩
  have hker : ∀ a : H, a ∈ θ.ker →
      (∀ w ∈ W, ((a : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w) ∧
      ∀ v : Fin 3 → K,
        ((a : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ W :=
    fun a ha => (hθ a).1 (MonoidHom.mem_ker.1 ha)
  have hcomm : ∀ a ∈ θ.ker, ∀ b ∈ θ.ker, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (l3ao_unip_comm W a b (hker a ha).1 (hker a ha).2 (hker b hb).1
      (hker b hb).2)
  have hnorm : (θ.ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψsurj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (θ.ker.map ψ) with hbotN | htopN
  ·
    have hinj : Function.Injective θ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro n hn
      have hn1 : ψ n = 1 := by
        have h1 : ψ n ∈ θ.ker.map ψ := Subgroup.mem_map_of_mem ψ hn
        rw [hbotN] at h1
        exact Subgroup.mem_bot.1 h1
      have hproj : LinearFlag.proj 3 K (n : SpecialLinearGroup (Fin 3) K) = 1 :=
        congrArg Subtype.val hn1
      have hsc : (n : SpecialLinearGroup (Fin 3) K) ∈ LinearFlag.scalars 3 K :=
        LinearFlag.proj_eq_one_iff.1 hproj
      have h1 : (n : SpecialLinearGroup (Fin 3) K) = 1 :=
        l3ao_scalar_eq_one W hbot _ hsc (hker n hn).1
      exact Subgroup.mem_bot.2 (Subtype.ext h1)
    have he : 1 ≤ 2 * f := by omega
    have hfinW := l3ao_finite_linearEquiv (F := K) W
    have hfinQ := l3ao_finite_linearEquiv (F := K) ((Fin 3 → K) ⧸ W)
    have hdvdH : Nat.card H ∣
        Nat.card ((W ≃ₗ[K] W) × (((Fin 3 → K) ⧸ W) ≃ₗ[K] ((Fin 3 → K) ⧸ W))) :=
      Subgroup.card_dvd_of_injective θ hinj
    have hdvdS : Nat.card S ∣ Nat.card H := Subgroup.card_dvd_of_surjective hψsurj
    rw [Nat.card_prod] at hdvdH
    have hne1 : Nat.card (W ≃ₗ[K] W) ≠ 0 := Nat.card_pos.ne'
    have hne2 : Nat.card (((Fin 3 → K) ⧸ W) ≃ₗ[K] ((Fin 3 → K) ⧸ W)) ≠ 0 := Nat.card_pos.ne'
    have hSne : Nat.card S ≠ 0 := Nat.card_pos.ne'
    have hle := (Nat.factorization_le_iff_dvd hSne (mul_ne_zero hne1 hne2)).2
      (hdvdS.trans hdvdH) 2
    rw [Nat.factorization_mul hne1 hne2, Finsupp.add_apply,
      l3ao_v2_card_linearEquiv hK he W, l3ao_v2_card_linearEquiv hK he] at hle
    have hsum : Module.finrank K ((Fin 3 → K) ⧸ W) + Module.finrank K W = 3 := by
      rw [Submodule.finrank_quotient_add_finrank W]
      simp
    have h1 : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.2 hbot
    have h2 : Module.finrank K W < 3 := by
      have := Submodule.finrank_lt htop
      simpa using this
    rcases (by omega : (Module.finrank K W = 1 ∧ Module.finrank K ((Fin 3 → K) ⧸ W) = 2) ∨
        (Module.finrank K W = 2 ∧ Module.finrank K ((Fin 3 → K) ⧸ W) = 1)) with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb, show (1 * (1 - 1) / 2 : ℕ) = 0 by norm_num,
        show (2 * (2 - 1) / 2 : ℕ) = 1 by norm_num] at hle
      omega
    · rw [ha, hb, show (1 * (1 - 1) / 2 : ℕ) = 0 by norm_num,
        show (2 * (2 - 1) / 2 : ℕ) = 1 by norm_num] at hle
      omega
  ·
    apply hnc
    intro a b
    obtain ⟨n₁, hn₁, rfl⟩ := Subgroup.mem_map.1 (by rw [htopN]; exact Subgroup.mem_top a)
    obtain ⟨n₂, hn₂, rfl⟩ := Subgroup.mem_map.1 (by rw [htopN]; exact Subgroup.mem_top b)
    rw [← map_mul, ← map_mul, hcomm n₁ hn₁ n₂ hn₂]

end PartB

section PartC

variable {K : Type} [Field K]

@[expose] def l3aoPhi (B : GL (Fin 3) K) (τ : K ≃+* K) : MulAut (SpecialLinearGroup (Fin 3) K) :=
  CatalogueBHigherLinearAction.slConjugation 3 K B *
    CatalogueBHigherLinearField.slFieldAut (Fin 3) K τ

theorem l3ao_phi_apply (B : GL (Fin 3) K) (τ : K ≃+* K) (g : SpecialLinearGroup (Fin 3) K) :
    ((l3aoPhi B τ g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K).map τ *
        ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have hF : ((CatalogueBHigherLinearField.slFieldAut (Fin 3) K τ g :
      SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K).map τ := by
    ext i j
    exact CatalogueBHigherLinearField.slFieldEquiv_entry (Fin 3) τ g i j
  simp only [l3aoPhi, MulAut.mul_apply]
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, hF]

theorem l3ao_descend_phi (B : GL (Fin 3) K) (τ : K ≃+* K) :
    descendAut 3 K (l3aoPhi B τ) = conjAut 3 K B * fieldAut 3 K τ := by
  rw [l3aoPhi, map_mul]
  rfl

@[expose] def l3aoG (B : GL (Fin 3) K) (τ : K ≃+* K) (S : Subgroup (projectiveSL 3 K)) :
    Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | proj 3 K g ∈ S ∧ l3aoPhi B τ g = g}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · rw [map_mul]
      exact S.mul_mem ha1 hb1
    · rw [map_mul, ha2, hb2]
  one_mem' := ⟨by rw [map_one]; exact S.one_mem, map_one _⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · rw [map_inv]
      exact S.inv_mem ha1
    · rw [map_inv, ha2]

theorem l3ao_mem_G {B : GL (Fin 3) K} {τ : K ≃+* K} {S : Subgroup (projectiveSL 3 K)}
    {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ l3aoG B τ S ↔ proj 3 K g ∈ S ∧
      (B : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K).map τ =
        (g : Matrix (Fin 3) (Fin 3) K) * B := by
  have hBinv : ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (B : Matrix (Fin 3) (Fin 3) K) = 1 := Units.inv_mul B
  have hBinv' : (B : Matrix (Fin 3) (Fin 3) K) *
      ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := Units.mul_inv B
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h3 := congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h2
    simp only [l3ao_phi_apply] at h3
    calc (B : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K).map τ
        = (B : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K).map τ *
            (((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) := by
          rw [hBinv, Matrix.mul_one]
      _ = ((B : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K).map τ *
            ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * (B : Matrix (Fin 3) (Fin 3) K) := by
          simp only [Matrix.mul_assoc]
      _ = (g : Matrix (Fin 3) (Fin 3) K) * B := by rw [h3]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    apply Subtype.ext
    rw [l3ao_phi_apply, h2, Matrix.mul_assoc, hBinv', Matrix.mul_one]

theorem l3ao_comm_mul_central {G : Type} [Group G] (a b z w : G)
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' : ∀ x : G, x * z = z * x := Subgroup.mem_center_iff.1 hz
  have hw' : ∀ x : G, x * w = w * x := Subgroup.mem_center_iff.1 hw
  have hzc : ∀ y : G, z * y * z⁻¹ = y := fun y => by rw [← hz' y, mul_inv_cancel_right]
  have h1 : a * z * (b * w) * (a * z)⁻¹ = a * (b * w) * a⁻¹ := by
    rw [_root_.mul_inv_rev]
    calc a * z * (b * w) * (z⁻¹ * a⁻¹) = a * (z * (b * w) * z⁻¹) * a⁻¹ := by simp only [mul_assoc]
      _ = a * (b * w) * a⁻¹ := by rw [hzc]
  have h2 : a * (b * w) * a⁻¹ = a * b * a⁻¹ * w := by
    calc a * (b * w) * a⁻¹ = a * b * (w * a⁻¹) := by simp only [mul_assoc]
      _ = a * b * (a⁻¹ * w) := by rw [← hw' a⁻¹]
      _ = a * b * a⁻¹ * w := by simp only [mul_assoc]
  rw [commutatorElement_def, commutatorElement_def, h1, h2, _root_.mul_inv_rev]
  calc a * b * a⁻¹ * w * (w⁻¹ * b⁻¹) = a * b * a⁻¹ * (w * w⁻¹) * b⁻¹ := by simp only [mul_assoc]
    _ = a * b * a⁻¹ * b⁻¹ := by rw [mul_inv_cancel, mul_one]

theorem l3ao_G_surj {B : GL (Fin 3) K} {τ : K ≃+* K} {S : Subgroup (projectiveSL 3 K)}
    (hS : ⁅S, S⁆ = S) (hfix : ∀ s ∈ S, (conjAut 3 K B * fieldAut 3 K τ) s = s) :
    ∀ s ∈ S, ∃ g ∈ l3aoG B τ S, proj 3 K g = s := by
  classical
  set At : Subgroup (SpecialLinearGroup (Fin 3) K) := S.comap (proj 3 K) with hAt
  have hcent : ∀ g ∈ At, ∃ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K),
      l3aoPhi B τ g = g * z := by
    intro g hg
    have h1 : proj 3 K (l3aoPhi B τ g) = proj 3 K g := by
      have h2 := descendAut_proj 3 K (l3aoPhi B τ) g
      rw [l3ao_descend_phi] at h2
      rw [← h2]
      exact hfix _ hg
    have h2 : g⁻¹ * l3aoPhi B τ g ∈ scalars 3 K :=
      (LinearFlag.proj_eq_proj_iff (n := 3) (K := K)).1 h1.symm
    rw [scalars_eq_center] at h2
    exact ⟨g⁻¹ * l3aoPhi B τ g, h2, (mul_inv_cancel_left g _).symm⟩
  have hcomm : ∀ g₁ ∈ At, ∀ g₂ ∈ At, ⁅g₁, g₂⁆ ∈ l3aoG B τ S := by
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨z₁, hz₁, h₁⟩ := hcent g₁ hg₁
    obtain ⟨z₂, hz₂, h₂⟩ := hcent g₂ hg₂
    refine ⟨?_, ?_⟩
    · have h3 : proj 3 K ⁅g₁, g₂⁆ = ⁅proj 3 K g₁, proj 3 K g₂⁆ := map_commutatorElement _ _ _
      rw [h3, commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem hg₁ hg₂) (S.inv_mem hg₁)) (S.inv_mem hg₂)
    · change l3aoPhi B τ ⁅g₁, g₂⁆ = ⁅g₁, g₂⁆
      rw [map_commutatorElement, h₁, h₂]
      exact l3ao_comm_mul_central g₁ g₂ z₁ z₂ hz₁ hz₂
  have hle : ⁅At, At⁆ ≤ l3aoG B τ S := Subgroup.commutator_le.2 hcomm
  have hmap : (⁅At, At⁆).map (proj 3 K) = S := by
    rw [Subgroup.map_commutator, hAt,
      Subgroup.map_comap_eq_self_of_surjective (proj_surjective 3 K)]
    exact hS
  intro s hs
  have hs' : s ∈ (⁅At, At⁆).map (proj 3 K) := by
    rw [hmap]
    exact hs
  obtain ⟨g, hg, hgs⟩ := Subgroup.mem_map.1 hs'
  exact ⟨g, hle hg, hgs⟩

end PartC

section PartD

variable {K : Type} [Field K]

theorem l3ao_h5_twisted_succ (τ : K ≃+* K) (A : Matrix (Fin 3) (Fin 3) K) (j : ℕ) :
    twistedProd (⇑τ) A (j + 1) = A * (twistedProd (⇑τ) A j).map (⇑τ) :=
  CFSG.RankThree.Classical2.twistedProd_succ (τ : K →+* K) A j

theorem l3ao_twisted_comm (τ : K ≃+* K) (B g : Matrix (Fin 3) (Fin 3) K)
    (hrel : B * g.map τ = g * B) (j : ℕ) :
    twistedProd (⇑τ) B j * g.map ((⇑τ)^[j]) =
      g * twistedProd (⇑τ) B j := by
  induction j with
  | zero => simp [CFSG.RankThree.Classical2.twistedProd_zero, Matrix.map_id]
  | succ j ih =>
    have hg : g.map ((⇑τ)^[j + 1]) = (g.map ((⇑τ)^[j])).map (⇑τ) := by
      rw [Matrix.map_map, Function.iterate_succ']
    have e2 : (twistedProd (⇑τ) B j * g.map ((⇑τ)^[j])).map (⇑τ) =
        (twistedProd (⇑τ) B j).map (⇑τ) * (g.map ((⇑τ)^[j])).map (⇑τ) := Matrix.map_mul
    have e3 : (g * twistedProd (⇑τ) B j).map (⇑τ) =
        g.map (⇑τ) * (twistedProd (⇑τ) B j).map (⇑τ) := Matrix.map_mul
    have h1 : (twistedProd (⇑τ) B j).map (⇑τ) * g.map ((⇑τ)^[j + 1]) =
        g.map (⇑τ) * (twistedProd (⇑τ) B j).map (⇑τ) := by
      rw [hg, ← e2, ih, e3]
    rw [l3ao_h5_twisted_succ, Matrix.mul_assoc, h1, ← Matrix.mul_assoc B (g.map (⇑τ)), hrel,
      Matrix.mul_assoc]

theorem l3ao_h5_map_smul (τ : K ≃+* K) (c : K) (M : Matrix (Fin 3) (Fin 3) K) :
    (c • M).map (⇑τ) = τ c • M.map (⇑τ) := by
  ext i j
  simp [Matrix.map_apply, smul_eq_mul, map_mul]

theorem l3ao_h5_prod_range_succ (τ : K ≃+* K) (d : K) (j : ℕ) :
    ∏ i ∈ Finset.range (j + 1), (τ ^ i) d = d * τ (∏ i ∈ Finset.range j, (τ ^ i) d) := by
  have e : ∀ i : ℕ, (τ ^ (i + 1)) d = τ ((τ ^ i) d) := fun i => by rw [pow_succ']; rfl
  have e0 : (τ ^ 0) d = d := by rw [pow_zero]; rfl
  rw [Finset.prod_range_succ', map_prod]
  simp only [e, e0]
  exact mul_comm _ _

theorem l3ao_twisted_smul (τ : K ≃+* K) (B : Matrix (Fin 3) (Fin 3) K) (d : K) (j : ℕ) :
    twistedProd (⇑τ) (d • B) j =
      (∏ i ∈ Finset.range j, (τ ^ i) d) • twistedProd (⇑τ) B j := by
  induction j with
  | zero => simp [CFSG.RankThree.Classical2.twistedProd_zero]
  | succ j ih =>
    rw [l3ao_h5_twisted_succ τ (d • B) j, ih, l3ao_h5_twisted_succ τ B j, l3ao_h5_map_smul,
      l3ao_h5_prod_range_succ, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem l3ao_h5_twisted_add (τ : K ≃+* K) (A : Matrix (Fin 3) (Fin 3) K) (a b : ℕ) :
    twistedProd (⇑τ) A (a + b) = twistedProd (⇑τ) A a * (twistedProd (⇑τ) A b).map (⇑τ)^[a] :=
  CFSG.RankThree.Classical2.twistedProd_add (τ : K →+* K) A a b

theorem l3ao_h5_scalar_map (τ : K ≃+* K) (c : K) :
    (Matrix.scalar (Fin 3) c).map (⇑τ) = Matrix.scalar (Fin 3) (τ c) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply, h]

theorem l3ao_h5_scalar_eq_smul_one (c : K) :
    Matrix.scalar (Fin 3) c = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem l3ao_twisted_scalar_fixed [Finite K] (τ : K ≃+* K) (B : Matrix (Fin 3) (Fin 3) K)
    (hB : IsUnit B.det) (c : K)
    (hc : twistedProd (⇑τ) B (orderOf τ) = Matrix.scalar (Fin 3) c) :
    τ c = c := by
  have hiter : (⇑τ)^[orderOf τ] = id := by
    rw [← RingAut.coe_pow, pow_orderOf_eq_one]
    rfl
  have hP1 : twistedProd (⇑τ) B 1 = B := by
    have h := l3ao_h5_twisted_succ τ B 0
    rw [CFSG.RankThree.Classical2.twistedProd_zero, Matrix.map_one (⇑τ) (map_zero τ) (map_one τ), Matrix.mul_one] at h
    exact h
  have hA : twistedProd (⇑τ) B (orderOf τ + 1) = Matrix.scalar (Fin 3) c * B := by
    rw [l3ao_h5_twisted_add, hP1, hiter, Matrix.map_id, hc]
  have hB' : twistedProd (⇑τ) B (orderOf τ + 1) = B * Matrix.scalar (Fin 3) (τ c) := by
    rw [l3ao_h5_twisted_succ, hc, l3ao_h5_scalar_map]
  have key : Matrix.scalar (Fin 3) c * B = B * Matrix.scalar (Fin 3) (τ c) := hA.symm.trans hB'
  rw [l3ao_h5_scalar_eq_smul_one, l3ao_h5_scalar_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one] at key
  have key2 : (c - τ c) • B = 0 := by
    rw [sub_smul, key, sub_self]
  rcases smul_eq_zero.mp key2 with h | h
  · exact (sub_eq_zero.mp h).symm
  · exfalso
    rw [h, Matrix.det_zero] at hB
    exact not_isUnit_zero hB

theorem l3ao_twisted_det_unit (τ : K ≃+* K) (B : Matrix (Fin 3) (Fin 3) K) (hB : IsUnit B.det)
    (j : ℕ) : IsUnit (twistedProd (⇑τ) B j).det := by
  induction j with
  | zero =>
    rw [CFSG.RankThree.Classical2.twistedProd_zero]
    simp
  | succ j ih =>
    have hs : twistedProd (⇑τ) B (j + 1) = B * (twistedProd (⇑τ) B j).map τ :=
      CFSG.RankThree.Classical2.twistedProd_succ (τ : K →+* K) B j
    rw [hs, Matrix.det_mul]
    refine hB.mul ?_
    have h1 : ((twistedProd (⇑τ) B j).map τ).det = τ (twistedProd (⇑τ) B j).det :=
      (RingHom.map_det (τ : K →+* K) _).symm
    rw [h1]
    exact ih.map τ

theorem l3ao_fixedField [Finite K] {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ e) (τ : K ≃+* K) :
    orderOf τ ∣ e ∧ ∃ k₀ : Subfield K, (∀ c : K, c ∈ k₀ ↔ τ c = c) ∧
      Nat.card k₀ = 2 ^ (e / orderOf τ) := by
  have hiter : ∀ x : K, (⇑τ)^[orderOf τ] x = x := fun x => by
    rw [← RingAut.coe_pow, pow_orderOf_eq_one]
    rfl
  have hstep : ∀ (c : K) (v : K), τ.toAddEquiv (c • v) = τ c • τ.toAddEquiv v := fun c v => by
    simp [smul_eq_mul]
  obtain ⟨hdvd, k₀, hk₀, hcard, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis Nat.prime_two he hK τ rfl
      (Module.finrank_self K) τ.toAddEquiv hstep hiter
  refine ⟨hdvd, k₀, fun c => ?_, hcard⟩
  exact Set.ext_iff.mp hk₀ c

theorem l3ao_descent [Finite K] {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ e) (τ : K ≃+* K)
    (B : Matrix (Fin 3) (Fin 3) K) (hB : IsUnit B.det)
    (hper : twistedProd (⇑τ) B (orderOf τ) = 1) :
    ∃ M : Matrix (Fin 3) (Fin 3) K, IsUnit M.det ∧ B * M.map τ = M := by
  have hiter : ∀ x : K, (⇑τ)^[orderOf τ] x = x := fun x => by
    rw [← RingAut.coe_pow, pow_orderOf_eq_one]
    rfl
  have hper' : ∀ v : Fin 3 → K,
      twistedProd (⇑τ) B (orderOf τ) *ᵥ ((⇑τ)^[orderOf τ] ∘ v) = v := by
    intro v
    rw [hper, Matrix.one_mulVec]
    funext i
    exact hiter (v i)
  exact CFSG.RankThree.Classical2.exists_isUnit_det_fixed Nat.prime_two he hK τ rfl B hB hper'

theorem l3ao_h7_lift (k₀ : Subfield K) (u : Matrix.GeneralLinearGroup (Fin 3) K)
    (hu : ∀ i j, (u : Matrix (Fin 3) (Fin 3) K) i j ∈ k₀)
    (hu' : ∀ i j, ((u⁻¹ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k₀) :
    u ∈ (Matrix.GeneralLinearGroup.map (n := Fin 3) k₀.subtype).range := by
  let A : Matrix (Fin 3) (Fin 3) k₀ :=
    Matrix.of fun i j => ⟨(u : Matrix (Fin 3) (Fin 3) K) i j, hu i j⟩
  let B : Matrix (Fin 3) (Fin 3) k₀ :=
    Matrix.of fun i j =>
      ⟨((u⁻¹ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j, hu' i j⟩
  have hA : A.map k₀.subtype = (u : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    rfl
  have hB : B.map k₀.subtype =
      ((u⁻¹ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    rfl
  have hone : (1 : Matrix (Fin 3) (Fin 3) k₀).map k₀.subtype = 1 :=
    Matrix.map_one k₀.subtype (map_zero k₀.subtype) (map_one k₀.subtype)
  have hAB : A * B = 1 := by
    refine Matrix.map_injective k₀.subtype.injective ?_
    show (A * B).map k₀.subtype = (1 : Matrix (Fin 3) (Fin 3) k₀).map k₀.subtype
    rw [Matrix.map_mul, hA, hB, hone]
    exact u.mul_inv
  have hBA : B * A = 1 := by
    refine Matrix.map_injective k₀.subtype.injective ?_
    show (B * A).map k₀.subtype = (1 : Matrix (Fin 3) (Fin 3) k₀).map k₀.subtype
    rw [Matrix.map_mul, hA, hB, hone]
    exact u.inv_mul
  rw [MonoidHom.mem_range]
  refine ⟨Units.mk A B hAB hBA, ?_⟩
  apply Units.ext
  ext i j
  rfl

theorem l3ao_count [Finite K] (τ : K ≃+* K) (k₀ : Subfield K) (hk₀ : ∀ c : K, c ∈ k₀ ↔ τ c = c)
    {e₀ : ℕ} (he₀ : 1 ≤ e₀) (hcard : Nat.card k₀ = 2 ^ e₀)
    (G : Subgroup (SpecialLinearGroup (Fin 3) K)) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : IsUnit M.det)
    (hfix : ∀ g ∈ G,
      (M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M).map τ =
        M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M) :
    (Nat.card G).factorization 2 ≤ e₀ * 3 := by
  obtain ⟨φ, hφinj, hφval⟩ : ∃ φ : SpecialLinearGroup (Fin 3) K →* Matrix.GeneralLinearGroup (Fin 3) K,
      Function.Injective φ ∧ ∀ g : SpecialLinearGroup (Fin 3) K,
        ((φ g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M := by
    refine ⟨(MulEquiv.toMonoidHom (MulAut.conj ((Matrix.nonsingInvUnit M hM)⁻¹))).comp
      Matrix.SpecialLinearGroup.toGL, ?_, ?_⟩
    · exact (MulEquiv.injective (MulAut.conj ((Matrix.nonsingInvUnit M hM)⁻¹))).comp
        Matrix.SpecialLinearGroup.toGL_injective
    · intro g
      rfl
  have hfix' : ∀ g ∈ G, ∀ i j,
      τ ((M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M) i j) =
        (M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M) i j := by
    intro g hg i j
    have h := congrFun (congrFun (hfix g hg) i) j
    rw [Matrix.map_apply] at h
    exact h
  have hle : G.map φ ≤ (Matrix.GeneralLinearGroup.map (n := Fin 3) k₀.subtype).range := by
    rintro x ⟨g, hg, rfl⟩
    apply l3ao_h7_lift k₀ (φ g)
    · intro i j
      rw [hφval g]
      exact (hk₀ _).2 (hfix' g hg i j)
    · intro i j
      rw [← map_inv φ g, hφval g⁻¹]
      exact (hk₀ _).2 (hfix' g⁻¹ (G.inv_mem hg) i j)
  have hι : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 3) k₀.subtype) := by
    intro x y hxy
    apply Units.ext
    refine Matrix.map_injective k₀.subtype.injective ?_
    exact congrArg Units.val hxy
  have hS : Nat.card (G.map φ) = Nat.card G := Subgroup.card_map_of_injective hφinj
  have hT : Nat.card ((Matrix.GeneralLinearGroup.map (n := Fin 3) k₀.subtype).range) =
      Nat.card (Matrix.GeneralLinearGroup (Fin 3) k₀) :=
    (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
  have hdvd : Nat.card G ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 3) k₀) := by
    have h1 := Subgroup.card_dvd_of_le hle
    rw [hS, hT] at h1
    exact h1
  rcases Nat.eq_zero_or_pos (Nat.card G) with h0 | hpos
  · rw [h0, Nat.factorization_zero]
    simp
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) k₀) ≠ 0 := by
    intro h0
    have hv := l3ao_v2_card_GL (F := ↥k₀) hcard he₀ 3
    rw [h0, Nat.factorization_zero] at hv
    simp at hv
    omega
  have hfac := (Nat.factorization_le_iff_dvd hpos.ne' hGL).2 hdvd
  have h2 : (Nat.card G).factorization 2 ≤
      (Nat.card (Matrix.GeneralLinearGroup (Fin 3) k₀)).factorization 2 := hfac 2
  rw [l3ao_v2_card_GL (F := ↥k₀) hcard he₀ 3] at h2
  have h3 : (3 : ℕ) * (3 - 1) / 2 = 3 := by norm_num
  rw [h3] at h2
  exact h2

end PartD

section PartE

variable {K : Type} [Field K] [Finite K]

theorem l3ao_tau_eq_one {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ (2 * f))
    (G : Subgroup (SpecialLinearGroup (Fin 3) K))
    (hcomm : ∀ M : Matrix (Fin 3) (Fin 3) K,
      (∀ g ∈ G, (g : Matrix (Fin 3) (Fin 3) K) * M = M * g) → ∃ c : K, M = Matrix.scalar (Fin 3) c)
    (hv2 : 3 * f ≤ (Nat.card G).factorization 2)
    (τ : K ≃+* K) (hτ : Odd (orderOf τ)) (B : GL (Fin 3) K)
    (hrel : ∀ g ∈ G, (B : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K).map τ =
      (g : Matrix (Fin 3) (Fin 3) K) * B) : τ = 1 := by
  classical
  have he : 1 ≤ 2 * f := by omega
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun τ : K ≃+* K => (τ : K → K)) (fun _ _ h => RingEquiv.ext (congrFun h))
  have hpos : 0 < orderOf τ := orderOf_pos τ
  have hid : (⇑τ)^[orderOf τ] = id := by
    rw [← RingAut.coe_pow, pow_orderOf_eq_one]
    rfl
  have hBdet : IsUnit (B : Matrix (Fin 3) (Fin 3) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  set P := twistedProd (⇑τ) (B : Matrix (Fin 3) (Fin 3) K) (orderOf τ) with hP
  obtain ⟨c, hc⟩ := hcomm P (fun g hg => by
    have h1 := l3ao_twisted_comm τ (B : Matrix (Fin 3) (Fin 3) K)
      (g : Matrix (Fin 3) (Fin 3) K) (hrel g hg) (orderOf τ)
    rw [hid, Matrix.map_id] at h1
    exact h1.symm)
  have hτc : τ c = c := l3ao_twisted_scalar_fixed τ _ hBdet c hc
  have hc0 : c ≠ 0 := by
    intro h0
    have hu := l3ao_twisted_det_unit τ _ hBdet (orderOf τ)
    rw [← hP, hc, h0, Matrix.scalar_apply, Matrix.det_diagonal] at hu
    simp at hu
  obtain ⟨d, hd⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq τ (c := c⁻¹) (by rw [map_inv₀, hτc])
  have hd0 : d ≠ 0 := by
    intro h0
    have : ∏ i ∈ Finset.range (orderOf τ), (τ ^ i) d = 0 :=
      Finset.prod_eq_zero (i := 0) (Finset.mem_range.2 hpos) (by simp [h0])
    rw [hd] at this
    exact hc0 (inv_eq_zero.1 this)
  have hB'det : IsUnit (d • (B : Matrix (Fin 3) (Fin 3) K)).det := by
    rw [Matrix.det_smul]
    exact ((isUnit_iff_ne_zero.2 (pow_ne_zero _ hd0))).mul hBdet
  have hper : twistedProd (⇑τ) (d • (B : Matrix (Fin 3) (Fin 3) K)) (orderOf τ) = 1 := by
    rw [l3ao_twisted_smul, hd, ← hP, hc]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp [hc0]
  have hrel' : ∀ g ∈ G, (d • (B : Matrix (Fin 3) (Fin 3) K)) *
      (g : Matrix (Fin 3) (Fin 3) K).map τ =
        (g : Matrix (Fin 3) (Fin 3) K) * (d • (B : Matrix (Fin 3) (Fin 3) K)) := by
    intro g hg
    rw [Matrix.smul_mul, Matrix.mul_smul, hrel g hg]
  obtain ⟨M, hMdet, hM⟩ := l3ao_descent he hK τ _ hB'det hper
  obtain ⟨hdvd, k₀, hk₀, hk₀card⟩ := l3ao_fixedField he hK τ
  have hfix : ∀ g ∈ G, (M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M).map τ =
      M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M := by
    intro g hg
    have hMX : M * (M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M) =
        (g : Matrix (Fin 3) (Fin 3) K) * M := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv M hMdet,
        Matrix.one_mul]
    have h1 : M.map τ * (M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M).map τ =
        (g : Matrix (Fin 3) (Fin 3) K).map τ * M.map τ := by
      have := congrArg (fun A => A.map τ) hMX
      simpa [Matrix.map_mul] using this
    have h2 : M * (M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M).map τ =
        (g : Matrix (Fin 3) (Fin 3) K) * M := by
      calc M * (M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M).map τ
          = ((d • (B : Matrix (Fin 3) (Fin 3) K)) * M.map τ) *
              (M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M).map τ := by rw [hM]
        _ = (d • (B : Matrix (Fin 3) (Fin 3) K)) * (M.map τ *
              (M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M).map τ) := by rw [Matrix.mul_assoc]
        _ = (d • (B : Matrix (Fin 3) (Fin 3) K)) *
              ((g : Matrix (Fin 3) (Fin 3) K).map τ * M.map τ) := by rw [h1]
        _ = ((d • (B : Matrix (Fin 3) (Fin 3) K)) *
              (g : Matrix (Fin 3) (Fin 3) K).map τ) * M.map τ := by rw [← Matrix.mul_assoc]
        _ = ((g : Matrix (Fin 3) (Fin 3) K) * (d • (B : Matrix (Fin 3) (Fin 3) K))) *
              M.map τ := by rw [hrel' g hg]
        _ = (g : Matrix (Fin 3) (Fin 3) K) *
              ((d • (B : Matrix (Fin 3) (Fin 3) K)) * M.map τ) := by rw [Matrix.mul_assoc]
        _ = (g : Matrix (Fin 3) (Fin 3) K) * M := by rw [hM]
    calc (M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M).map τ
        = M⁻¹ * (M * (M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M).map τ) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul M hMdet, Matrix.one_mul]
      _ = M⁻¹ * ((g : Matrix (Fin 3) (Fin 3) K) * M) := by rw [h2]
      _ = M⁻¹ * (g : Matrix (Fin 3) (Fin 3) K) * M := by rw [Matrix.mul_assoc]
  have he₀ : 1 ≤ 2 * f / orderOf τ := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hpos
  have hcount := l3ao_count τ k₀ hk₀ he₀ hk₀card G M hMdet hfix
  have hq : orderOf τ * (2 * f / orderOf τ) = 2 * f := Nat.mul_div_cancel' hdvd
  have hfq : f ≤ 2 * f / orderOf τ := by omega
  have hle2 : orderOf τ ≤ 2 := by
    have h3 : orderOf τ * f ≤ 2 * f := by
      calc orderOf τ * f ≤ orderOf τ * (2 * f / orderOf τ) := Nat.mul_le_mul_left _ hfq
        _ = 2 * f := hq
    exact Nat.le_of_mul_le_mul_right h3 (by omega)
  have hone : orderOf τ = 1 := by
    obtain ⟨k, hk⟩ := hτ
    omega
  exact orderOf_eq_one_iff.1 hone

theorem l3ao_h8_sq_pow_odd {M : Type*} [Monoid M] {x : M} {r : ℕ} (hr : Odd r) (hx : x ^ r = 1) :
    (x * x) ^ ((r + 1) / 2) = x := by
  obtain ⟨m, rfl⟩ := hr
  have h2m : 2 * ((2 * m + 1 + 1) / 2) = 2 * m + 1 + 1 := by omega
  rw [← sq, ← pow_mul, h2m, pow_succ, hx, one_mul]

theorem l3ao_semilinear_of_odd (σ : MulAut (projectiveSL 3 K)) (hodd : Odd (orderOf σ)) :
    ∃ (B : GL (Fin 3) K) (τ : K ≃+* K), σ = conjAut 3 K B * fieldAut 3 K τ ∧ Odd (orderOf τ) := by
  have hstd : σ ∈ standardAutGroup 3 K := by
    rw [(automorphism_generation (K := K) (n := 3) le_rfl).1]
    exact Subgroup.mem_top _
  have hE : σ ∈ semilinearAutGroup 3 K := by
    rcases mem_or_mul_dualAut_mem hstd with h | h
    · exact h
    · have hδδ : dualAut 3 K * dualAut 3 K = 1 :=
        (standard_automorphism_transport (K := K) (n := 3)).2.2.2.1
      have h2 : σ * σ ∈ semilinearAutGroup 3 K := by
        have e : σ * σ = (σ * dualAut 3 K) *
            (dualAut 3 K * (σ * dualAut 3 K) * dualAut 3 K) := by
          calc σ * σ = σ * 1 * σ * 1 := by group
            _ = σ * (dualAut 3 K * dualAut 3 K) * σ * (dualAut 3 K * dualAut 3 K) := by
                rw [hδδ]
            _ = _ := by group
        rw [e]
        exact mul_mem h (dualAut_mul_mul_dualAut_mem h)
      have hpow := pow_mem h2 ((orderOf σ + 1) / 2)
      rwa [l3ao_h8_sq_pow_odd hodd (pow_orderOf_eq_one σ)] at hpow
  obtain ⟨B, τ, hB⟩ := mem_semilinearAutGroup_iff.mp hE
  refine ⟨B, τ, hB, ?_⟩
  have hfp : CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.linearFieldPart K
      (le_rfl : (3 : ℕ) ≤ 3) σ = τ := by
    have h := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.linearFieldPart_eq (K := K)
      (le_rfl : (3 : ℕ) ≤ 3) (A := B) (σ := τ) (ε := 0) zero_le_one
    rw [pow_zero, mul_one, ← hB] at h
    exact h
  have hdvd : orderOf τ ∣ orderOf σ := by
    rw [← hfp]
    exact orderOf_map_dvd (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.linearFieldPart K
      (le_rfl : (3 : ℕ) ≤ 3)) σ
  exact Odd.of_dvd_nat hodd hdvd

theorem l3ao_core {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ (2 * f))
    (S : Subgroup (projectiveSL 3 K)) (hS : IsSimpleGroup S)
    (hnc : ¬ ∀ a b : S, a * b = b * a) (hv2 : 3 * f ≤ (Nat.card S).factorization 2)
    (σ : MulAut (projectiveSL 3 K)) (hσ : ∀ s ∈ S, σ s = s) (hodd : Odd (orderOf σ)) :
    σ = 1 := by
  classical
  obtain ⟨B, τ, hσeq, hτodd⟩ := l3ao_semilinear_of_odd σ hodd
  have hSperf : ⁅S, S⁆ = S := l3ao_perfect_of_simple S hS hnc
  have hfixS : ∀ s ∈ S, (conjAut 3 K B * fieldAut 3 K τ) s = s := by
    intro s hs
    rw [← hσeq]
    exact hσ s hs
  have hGS := l3ao_G_surj hSperf hfixS
  have hHS : ∀ g ∈ l3aoG B τ S, proj 3 K g ∈ S := fun g hg => (l3ao_mem_G.1 hg).1
  have hrel : ∀ g ∈ l3aoG B τ S, (B : Matrix (Fin 3) (Fin 3) K) *
      (g : Matrix (Fin 3) (Fin 3) K).map τ = (g : Matrix (Fin 3) (Fin 3) K) * B :=
    fun g hg => (l3ao_mem_G.1 hg).2
  let ψ : l3aoG B τ S →* S :=
    { toFun := fun g => ⟨proj 3 K (g : SpecialLinearGroup (Fin 3) K), hHS g g.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  have hψsurj : Function.Surjective ψ := fun s => by
    obtain ⟨g, hg, hs⟩ := hGS s s.2
    exact ⟨⟨g, hg⟩, Subtype.ext hs⟩
  have hv2G : 3 * f ≤ (Nat.card (l3aoG B τ S)).factorization 2 := by
    refine hv2.trans ?_
    have hSne : Nat.card S ≠ 0 := Nat.card_pos.ne'
    have hGne : Nat.card (l3aoG B τ S) ≠ 0 := Nat.card_pos.ne'
    exact (Nat.factorization_le_iff_dvd hSne hGne).2 (Subgroup.card_dvd_of_surjective hψsurj) 2
  have hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ g ∈ l3aoG B τ S, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => l3ao_irreducible hf hK (l3aoG B τ S) S hS hnc hHS hGS hv2 W hW
  have hcomm : ∀ M : Matrix (Fin 3) (Fin 3) K,
      (∀ g ∈ l3aoG B τ S, (g : Matrix (Fin 3) (Fin 3) K) * M = M * g) →
        ∃ c : K, M = Matrix.scalar (Fin 3) c := by
    let GG : Subgroup (GL (Fin 3) K) := (l3aoG B τ S).map Matrix.SpecialLinearGroup.toGL
    have hirrGG : CFSG.RepresentationTheory.IsIrreducibleMatrixRep GG.subtype := by
      intro W hW
      refine hirr W (fun g hg w hw => ?_)
      exact hW ⟨Matrix.SpecialLinearGroup.toGL g, Subgroup.mem_map_of_mem _ hg⟩ w hw
    rcases CFSG.RankThree.SubgroupLists.scalar_commutant_or_cyclic Nat.prime_three hirrGG with
      h | ⟨hcyc, -, -⟩
    · intro M hM
      refine h M (fun g hg => ?_)
      obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.1 hg
      exact hM g₀ hg₀
    · exfalso
      apply hnc
      have hcommGG : ∀ a b : GG, a * b = b * a := fun a b => hcyc.commGroup.mul_comm a b
      have hcommG : ∀ g₁ ∈ l3aoG B τ S, ∀ g₂ ∈ l3aoG B τ S, g₁ * g₂ = g₂ * g₁ := by
        intro g₁ hg₁ g₂ hg₂
        have := hcommGG ⟨Matrix.SpecialLinearGroup.toGL g₁, Subgroup.mem_map_of_mem _ hg₁⟩
          ⟨Matrix.SpecialLinearGroup.toGL g₂, Subgroup.mem_map_of_mem _ hg₂⟩
        have h2 := congrArg Subtype.val this
        simp only [Subgroup.coe_mul] at h2
        rw [← map_mul, ← map_mul] at h2
        exact Matrix.SpecialLinearGroup.toGL_injective h2
      intro a b
      obtain ⟨g₁, hg₁, hga⟩ := hGS a a.2
      obtain ⟨g₂, hg₂, hgb⟩ := hGS b b.2
      apply Subtype.ext
      change (a : projectiveSL 3 K) * b = b * a
      rw [← hga, ← hgb, ← map_mul, ← map_mul, hcommG g₁ hg₁ g₂ hg₂]
  have hτ1 : τ = 1 := l3ao_tau_eq_one hf hK (l3aoG B τ S) hcomm hv2G τ hτodd B hrel
  have hB : ∃ c : K, (B : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
    refine hcomm B (fun g hg => ?_)
    have h1 := hrel g hg
    rw [hτ1] at h1
    have h2 : (g : Matrix (Fin 3) (Fin 3) K).map ⇑(1 : K ≃+* K) = (g : Matrix (Fin 3) (Fin 3) K) := by
      ext i j
      rfl
    rw [h2] at h1
    exact h1.symm
  obtain ⟨c, hc⟩ := hB
  rw [hσeq, hτ1, map_one, mul_one]
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, hc]
  have hcomm' : Commute (Matrix.scalar (Fin 3) c) (g : Matrix (Fin 3) (Fin 3) K) :=
    Matrix.scalar_commute c (fun r' => Commute.all c r') _
  rw [hcomm'.eq, ← hc, Matrix.mul_assoc]
  have hinv : (B : Matrix (Fin 3) (Fin 3) K) * ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
    Units.mul_inv B
  rw [hinv, Matrix.mul_one]

end PartE

theorem l3ao_main (f : ℕ) (hf : 2 ≤ f) (X : Type) [Group X] (A : Subgroup X)
    (hX : LieModel X .PSL 3 2 (2 * f)) (hA : LieModel A .PSU 3 2 f)
    (σ : MulAut X) (hσ : ∀ a ∈ A, σ a = a) (hodd : Odd (orderOf σ)) : σ = 1 := by
  classical
  obtain ⟨K, hF, hfin, e, hK, -⟩ :=
    CFSG.RankThree.PartOne.AUTSL.aut_of_lieModel_psl (n := 3) (p := 2) (f := 2 * f) le_rfl hX
  let S : Subgroup (LinearFlag.projectiveSL 3 K) := A.map e.toMonoidHom
  let hAS : A ≃* S := A.equivMapOfInjective e.toMonoidHom e.injective
  have hAsimple : IsSimpleGroup A :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 hA
  have hSsimple : IsSimpleGroup S := by
    haveI := hAsimple
    exact hAS.symm.isSimpleGroup
  have hnc : ¬ ∀ a b : S, a * b = b * a := by
    intro h
    obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 hA
    apply hab
    apply hAS.injective
    rw [map_mul, map_mul]
    exact h _ _
  have hv2 : 3 * f ≤ (Nat.card S).factorization 2 := by
    rw [← Nat.card_congr hAS.toEquiv,
      CFSG.LocalAnalysis.EvenBN.GMSK.factorization_two_card_of_lieModel_PSU3 hA]
  have hσ' : ∀ s ∈ S, (MulAut.congr e σ) s = s := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hs
    rw [MulAut.congr_apply]
    change e (σ (e.symm (e a))) = e a
    rw [MulEquiv.symm_apply_apply, hσ a ha]
  have hodd' : Odd (orderOf (MulAut.congr e σ)) := by
    rw [MulEquiv.orderOf_eq (MulAut.congr e)]
    exact hodd
  have h1 : MulAut.congr e σ = 1 :=
    l3ao_core (K := K) (by omega) hK S hSsimple hnc hv2 (MulAut.congr e σ) hσ' hodd'
  exact (MulAut.congr e).injective (by rw [h1, map_one])

theorem l3AutOdd : L3AutOddStatement := by
  intro f hf X _ A hX hA τ _ _ _ σ hσ hodd
  exact l3ao_main f hf X A hX hA σ hσ hodd

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5

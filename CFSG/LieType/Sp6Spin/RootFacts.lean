module

public import CFSG.LieType.Sp6Spin.Setup
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LieType.Sp6Spin

open CFSG.LieType.TorusWeights CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin
  QuadraticMap

attribute [local instance] Fintype.ofFinite Classical.propDecidable

namespace SpinSetting

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (S : SpinSetting K V)

theorem A_zero (r : RootSubgroupIndex 3) : S.A r 0 = 1 := by
  simpa only [A] using rootOp_zero (ρ := S.ρ) (x := elt (F := K) r) (elt_zero r)

theorem ψ_elt_apply (r : RootSubgroupIndex 3) (c : K) (v : V) :
    S.ψ (elt r c) v = ∑ k ∈ Finset.range (Nat.card Kˣ + 1), c ^ k • S.A r k v := by
  rw [← S.ρ_apply (elt (F := K) r c) v,
    rho_eq_sum (ρ := S.ρ) (x := elt (F := K) r) c]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, A]

theorem A_conj {g : StatedSp 3 K} {r r' : RootSubgroupIndex 3}
    (hg : ∀ c : K, g * elt r c * g⁻¹ = elt r' c) (k : ℕ) :
    S.A r' k = S.ρ g * S.A r k * S.ρ g⁻¹ := by
  simpa only [A] using rootOp_conj_elt (ρ := S.ρ) (x := elt (F := K) r)
    (x' := elt (F := K) r') hg k

theorem A_eq_zero_iff_of_conj {g : StatedSp 3 K} {r r' : RootSubgroupIndex 3}
    (hg : ∀ c : K, g * elt r c * g⁻¹ = elt r' c) (k : ℕ) :
    S.A r' k = 0 ↔ S.A r k = 0 := by
  have hg' : ∀ c : K, g⁻¹ * elt r' c * (g⁻¹)⁻¹ = elt r c := by
    intro c
    rw [inv_inv]
    calc g⁻¹ * elt r' c * g = g⁻¹ * (g * elt r c * g⁻¹) * g := by rw [hg c]
      _ = elt r c := by group
  constructor
  · intro h
    rw [S.A_conj hg' k, h]
    simp
  · intro h
    rw [S.A_conj hg k, h]
    simp

theorem A_eq_zero (r : RootSubgroupIndex 3) (k : ℕ)
    (h : ∀ a, S.mult a ≠ 0 → S.mult (a + (k : ZMod (Nat.card Kˣ)) • rootWt K r) = 0) :
    S.A r k = 0 := by
  refine ext_of_wtSpace (diagHom 3 K) S.ρ (f := S.A r k) (g := 0) fun a v hv => ?_
  change v ∈ S.X a at hv
  by_cases hm : S.mult a = 0
  · have hv0 : v = 0 := by
      rw [S.X_eq_bot_iff.mpr hm] at hv
      simpa using hv
    rw [hv0]
    simp
  · have hmem := S.A_mem r hv k
    rw [S.X_eq_bot_iff.mpr (h a hm)] at hmem
    exact hmem

theorem exists_A_eq_mul (r : RootSubgroupIndex 3) {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ Nat.card Kˣ) (hk : ∀ l : ℕ, k ≠ 2 ^ l) :
    ∃ i j : ℕ, 0 < i ∧ 0 < j ∧ i ≠ j ∧ i + j = k ∧ S.A r k = S.A r i * S.A r j :=
  exists_rootOp_eq_mul (ρ := S.ρ) (x := elt (F := K) r) (elt_add r) hk1 hkN hk

theorem Q_eq_zero {a : Fin 3 → ZMod (Nat.card Kˣ)} (ha : a ≠ 0) {v : V} (hv : v ∈ S.X a) :
    S.Q v = 0 := by
  refine quad_eq_zero_of_mem_wtSpace (diagHom 3 K) S.ρ (Q := S.Q) ?_ ha hv
  intro g u
  rw [S.ρ_apply]
  exact S.map_Q g u

theorem ψ_injective : Function.Injective S.ψ := by
  classical
  haveI : FiniteDimensional K V := S.finiteDimensional
  have hcenter : Subgroup.center (StatedSp 3 K) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [CFSG.LieType.Universal.Symplectic.center_eq 3 K, Subgroup.mem_subgroupOf,
      CFSG.Open.StatedScalars, MonoidHom.mem_range] at hg
    obtain ⟨u, hu⟩ := hg
    have hmem : (g : GL (Fin 3 ⊕ Fin 3) K) ∈ TauCeti.GLSymplectic (Fin 3) K := by
      rw [← CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 3) (K := K)]
      exact g.2
    have hsp := TauCeti.GLSymplectic.mem_iff.1 hmem
    rw [← hu, Matrix.GeneralLinearGroup.coe_scalar] at hsp
    have hJ : (Matrix.scalar (Fin 3 ⊕ Fin 3) (u : K)) * Matrix.J (Fin 3) K *
        (Matrix.scalar (Fin 3 ⊕ Fin 3) (u : K)).transpose =
        ((u : K) * u) • Matrix.J (Fin 3) K := by
      simp only [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.transpose_smul,
        Matrix.transpose_one, smul_smul]
    rw [hJ] at hsp
    have h1 := congrFun (congrFun hsp (Sum.inl 0)) (Sum.inr 0)
    simp only [Matrix.smul_apply, Matrix.J, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_neg, mul_one, neg_inj] at h1
    have hu2 : ((u : K) + 1) * ((u : K) + 1) = 0 := by
      linear_combination h1 + ((u : K) + 1) * (CharTwo.two_eq_zero : (2 : K) = 0)
    have hu1 : (u : K) = 1 := by
      rw [mul_self_eq_zero, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hu2
      exact hu2
    rw [Subgroup.mem_bot]
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_one, Units.val_one, ← hu, Matrix.GeneralLinearGroup.coe_scalar, hu1,
      Matrix.scalar_apply, Matrix.diagonal_one]
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple 3 K (by norm_num)
      (Or.inl (Or.inr S.card_le))
  haveI : IsSimpleGroup (StatedSp 3 K ⧸ Subgroup.center (StatedSp 3 K)) := hsimple
  haveI : IsSimpleGroup (StatedSp 3 K) :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientBot (G := StatedSp 3 K))).symm.isSimpleGroup
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.ker S.ψ) with hker | hker
  · exact hker
  · exfalso
    have hψ1 : S.ψ = 1 := MonoidHom.ker_eq_top_iff.mp hker
    obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 :=
      Module.finrank_pos_iff_exists_ne_zero.mp (by rw [S.finrank_eq]; norm_num)
    have hinv : ∀ g, ∀ w ∈ (Submodule.span K {v} : Submodule K V),
        S.ψ g w ∈ Submodule.span K {v} := by
      intro g w hw
      have hg1 : S.ψ g = 1 := by rw [hψ1]; rfl
      simpa [hg1] using hw
    rcases S.irred (Submodule.span K {v}) hinv with hbot | htop
    · have hvbot : v ∈ (⊥ : Submodule K V) := by
        rw [← hbot]
        exact Submodule.mem_span_singleton_self v
      exact hv (by simpa using hvbot)
    · have h1 : Module.finrank K (Submodule.span K {v}) = 1 := finrank_span_singleton hv
      have h8 : Module.finrank K (Submodule.span K {v}) = 8 := by
        rw [htop, finrank_top, S.finrank_eq]
      omega

end SpinSetting

end CFSG.LieType.Sp6Spin

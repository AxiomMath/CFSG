module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.OrthRadical
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.OrthPerp
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.OrthShell
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.BilinRoot
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank

theorem two_pow_le_card_of_pomega {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] [CharP K p]
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) (hnd : (polarBilin Q).Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {P P' P'' : HypPair Q} (h1 : P.Orth P') (h2 : P.Orth P'') (h3 : P'.Orth P'')
    {L : Subgroup (MulAut W)} (θ : ↥L ≃* StatedProj (StatedOmega Q₀)) :
    2 ^ (orderOf (2 : ZMod p) *
      ((Nat.card K - 1) * Nat.card K ^ (Fintype.card ι - 4) / (p - 1))) ≤ Nat.card W := by
  classical
  let π : ↥L →* ProjElementary Q :=
    (statedProjEquiv hQ hE).toMonoidHom.comp θ.toMonoidHom
  have hπinj : Function.Injective π := (statedProjEquiv hQ hE).injective.comp θ.injective
  have hπ : Function.Surjective π := (statedProjEquiv hQ hE).surjective.comp θ.surjective
  have hker : π.ker = ⊥ := (MonoidHom.ker_eq_bot_iff π).2 hπinj
  have hker' : π.ker ≤ Subgroup.center ↥L := by rw [hker]; exact bot_le
  have hZ : ¬ p ∣ Nat.card π.ker := by
    rw [hker, Subgroup.card_bot]
    exact (Fact.out : p.Prime).not_dvd_one
  let ψ : elementaryGroup Q →* ProjElementary Q := QuotientGroup.mk' _
  set V₀ := hypPerp P
  have hV₀ : Nontrivial V₀ := by
    refine ⟨⟨⟨P'.e, ?_⟩, 0, fun h => P'.e_ne_zero (congrArg Subtype.val h)⟩⟩
    exact ⟨by rw [polar_comm]; exact h1.ee, by rw [polar_comm]; exact h1.fe⟩
  let u : Multiplicative V₀ →* ProjElementary Q := ψ.comp (eichlerRadical P)
  have hu : Function.Injective u := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    rw [MonoidHom.mem_ker] at hw
    have hmem : eichlerRadical P w ∈ (scalars K (ι → K)).subgroupOf (elementaryGroup Q) :=
      (QuotientGroup.eq_one_iff _).1 hw
    rw [Subgroup.mem_subgroupOf, mem_scalars] at hmem
    obtain ⟨c, hc⟩ := hmem
    have h0 := eq_zero_of_eichler_eq_smul P (Multiplicative.toAdd w).2 hc
    rw [Subgroup.mem_bot]
    have : Multiplicative.toAdd w = 0 := Subtype.ext h0
    simpa using congrArg Multiplicative.ofAdd this
  let ext' : elementaryGroup (perpForm P) →* elementaryGroup Q :=
    { toFun := fun g => ⟨extHom P g, extHom_mem_elementaryGroup P g.2⟩
      map_one' := by ext1; simp
      map_mul' := fun a b => by ext1; simp }
  let t : elementaryGroup (perpForm P) →* ProjElementary Q := ψ.comp ext'
  let ρ : elementaryGroup (perpForm P) → V₀ →ₗ[K] V₀ :=
    fun g => ((g : V₀ ≃ₗ[K] V₀) : V₀ →ₗ[K] V₀)
  have hρ : ∀ g x y, polarBilin (perpForm P) (ρ g x) (ρ g y) = polarBilin (perpForm P) x y := by
    intro g x y
    simp only [polarBilin_apply_apply]
    exact polar_map_of_mem (elementaryGroup_le_orthogonalGroup _ g.2) x y
  have htu : ∀ g v, t g * u (Multiplicative.ofAdd v) * (t g)⁻¹ =
      u (Multiplicative.ofAdd (ρ g v)) := by
    intro g v
    have key : ext' g * eichlerRadical P (Multiplicative.ofAdd v) * (ext' g)⁻¹ =
        eichlerRadical P (Multiplicative.ofAdd (ρ g v)) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact extHom_mul_eichler_mul_inv P g.2 v
    show ψ (ext' g) * ψ (eichlerRadical P (Multiplicative.ofAdd v)) * (ψ (ext' g))⁻¹ =
      ψ (eichlerRadical P (Multiplicative.ofAdd (ρ g v)))
    rw [← map_inv, ← map_mul, ← map_mul, key]
  have hdim : Module.finrank K V₀ = Fintype.card ι - 2 := by
    rw [finrank_hypPerp, Module.finrank_fintype_fun_eq_card]
  have hnd₀ := nondegenerate_perpForm hnd P
  have hP₀ := hypPairPerp_orth h1 h2 h3
  have horb : ∀ y : V₀, y ≠ 0 → (Nat.card K - 1) * Nat.card K ^ (Fintype.card ι - 4) ≤
      Nat.card (Set.range fun g : elementaryGroup (perpForm P) => ρ g y) := by
    intro y hy
    have hshell := card_shell_ge (hypPairPerp h1) (perpForm P y)
    rw [hdim, show Fintype.card ι - 2 - 2 = Fintype.card ι - 4 by omega] at hshell
    refine hshell.trans ?_
    have : Finite V₀ := Module.finite_of_finite K
    refine Nat.card_le_card_of_injective
      (fun v => ⟨v.1, ?_⟩) (fun a b h => Subtype.ext (by
        have := congrArg Subtype.val h
        simpa using this))
    obtain ⟨g, hg, hgv⟩ := exists_mem_elementaryGroup_apply_eq hnd₀ hP₀ hy v.2.1 v.2.2.symm
    exact ⟨⟨g, hg⟩, hgv⟩
  have h := two_pow_le_card_of_bilinear_root hW hp2 π hπ hker' hZ (polarBilin (perpForm P)) hnd₀
    u hu t ρ ρ hρ htu horb
  exact h

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

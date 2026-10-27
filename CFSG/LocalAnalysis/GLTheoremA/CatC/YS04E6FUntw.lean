module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6FBruhat
public import CFSG.HardMathSupport.Lang.E6Descent.OuterDescentE
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OutStep
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6FGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.YS04E6F

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.HardMathSupport.Lang.E6Descent

variable {K : Type} [Field K]

theorem entrywiseAdjointAut_mul_rootDiagAut (T : K ≃+* K) (a : Fin Tag.E6.rank → Kˣ) :
    entrywiseAdjointAut Tag.E6 T * rootDiagAut Tag.E6 K a =
      rootDiagAut Tag.E6 K (twU T a) * entrywiseAdjointAut Tag.E6 T := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  simp only [MulAut.mul_apply, coe_entrywiseAdjointAut, coe_rootDiagAut, map_mul, map_inv,
    entrywise_rootDiagUnit]

theorem eq_of_comm (T : K ≃+* K) {g : adjointGroup Tag.E6 K} {a : Fin Tag.E6.rank → Kˣ}
    (hcomm : (MulAut.conj g * rootDiagAut Tag.E6 K a) * entrywiseAdjointAut Tag.E6 T =
      entrywiseAdjointAut Tag.E6 T * (MulAut.conj g * rootDiagAut Tag.E6 K a)) :
    Units.map (entrywiseHom T.toRingHom) (g : ModGL Tag.E6 K) =
      g * rootDiagUnit Tag.E6 (a * (twU T a)⁻¹) := by
  set Ts := entrywiseAdjointAut Tag.E6 T with hTs
  have h2 : (MulAut.conj g * rootDiagAut Tag.E6 K a) * Ts =
      (MulAut.conj (Ts g) * rootDiagAut Tag.E6 K (twU T a)) * Ts := by
    calc (MulAut.conj g * rootDiagAut Tag.E6 K a) * Ts
        = Ts * (MulAut.conj g * rootDiagAut Tag.E6 K a) := hcomm
      _ = (Ts * MulAut.conj g) * rootDiagAut Tag.E6 K a := by rw [mul_assoc]
      _ = (MulAut.conj (Ts g) * Ts) * rootDiagAut Tag.E6 K a := by rw [mulAut_mul_conj]
      _ = MulAut.conj (Ts g) * (Ts * rootDiagAut Tag.E6 K a) := by rw [mul_assoc]
      _ = MulAut.conj (Ts g) * (rootDiagAut Tag.E6 K (twU T a) * Ts) := by
            rw [hTs, entrywiseAdjointAut_mul_rootDiagAut]
      _ = (MulAut.conj (Ts g) * rootDiagAut Tag.E6 K (twU T a)) * Ts := by rw [mul_assoc]
  have h1 : MulAut.conj g * rootDiagAut Tag.E6 K a =
      MulAut.conj (Ts g) * rootDiagAut Tag.E6 K (twU T a) := mul_right_cancel h2
  have h3 : MulAut.conj (g⁻¹ * Ts g) = rootDiagAut Tag.E6 K (a * (twU T a)⁻¹) := by
    have h4 : MulAut.conj (Ts g) =
        MulAut.conj g * rootDiagAut Tag.E6 K a * (rootDiagAut Tag.E6 K (twU T a))⁻¹ :=
      eq_mul_inv_of_mul_eq h1.symm
    have h5 : rootDiagAut Tag.E6 K (a * (twU T a)⁻¹) =
        rootDiagAut Tag.E6 K a * (rootDiagAut Tag.E6 K (twU T a))⁻¹ := by
      have := map_mul (rootDiagAutHom Tag.E6 K) a (twU T a)⁻¹
      rw [map_inv] at this
      exact this
    rw [h5, map_mul, map_inv, h4]
    group
  have h6 := conj_eq_rootDiagAut _ _ h3
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at h6
  exact eq_mul_of_inv_mul_eq h6

theorem card_le_three_of_inndiag [Finite K] (E : Subgroup (MulAut (adjointGroup Tag.E6 K)))
    (hE : ∀ x ∈ E, ∃ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
      x = MulAut.conj g * rootDiagAut Tag.E6 K a)
    (hEI : E ⊓ inner (adjointGroup Tag.E6 K) = ⊥) : Nat.card E ≤ 3 := by
  classical
  obtain ⟨Φ, -, hΦker, hΦcard⟩ := exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  haveI : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  set ψ : E →* Outer (adjointGroup Tag.E6 K) :=
    (QuotientGroup.mk' (inner (adjointGroup Tag.E6 K))).comp E.subtype with hψ
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : MulAut (adjointGroup Tag.E6 K)) ∈ inner (adjointGroup Tag.E6 K) :=
      (QuotientGroup.eq_one_iff _).1 hx
    have : (x : MulAut (adjointGroup Tag.E6 K)) ∈ E ⊓ inner (adjointGroup Tag.E6 K) :=
      ⟨x.2, hx'⟩
    rw [hEI, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hψmem : ∀ x : E, ψ x ∈ Φ.ker := by
    intro x
    obtain ⟨g, a, hga⟩ := hE x x.2
    rw [hΦker]
    refine ⟨a, ?_⟩
    change (QuotientGroup.mk (rootDiagAut Tag.E6 K a) : Outer (adjointGroup Tag.E6 K)) =
      QuotientGroup.mk' (inner (adjointGroup Tag.E6 K)) (x : MulAut (adjointGroup Tag.E6 K))
    rw [hga, map_mul, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff
      (N := inner (adjointGroup Tag.E6 K)) (MulAut.conj g)).2
      (MonoidHom.mem_range.2 ⟨g, rfl⟩), one_mul]
    rfl
  have hle : Nat.card E ≤ Nat.card Φ.ker := by
    refine Nat.card_le_card_of_injective (fun x => (⟨ψ x, hψmem x⟩ : Φ.ker)) ?_
    intro x y hxy
    exact hψinj (congrArg Subtype.val hxy)
  have hdet : Tag.E6.cartan.det.natAbs = 3 := by rw [det_cartan_E6]; rfl
  rw [hdet] at hΦcard
  exact hle.trans (Nat.le_of_dvd (by norm_num) hΦcard)

theorem meets_inner_E6_untw [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    (D : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hD : IsElemAbelian 3 D)
    (hc : Nat.card D = 9) : ∃ x ∈ D ⊓ inner (adjointGroup Tag.E6 K), x ≠ 1 := by
  classical
  obtain ⟨Θ, -, -, hker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨Φ, -, hΦker, hΦcard⟩ := exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
  obtain ⟨ℓ, f, hℓ, hf, hKℓ⟩ : ∃ ℓ f : ℕ, ℓ.Prime ∧ 1 ≤ f ∧ Nat.card K = ℓ ^ f := by
    haveI := Fintype.ofFinite K
    obtain ⟨n, hp', hn⟩ := FiniteField.card K (ringChar K)
    exact ⟨ringChar K, n, hp', n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨hcardAut, hcyc⟩ := card_ringAut_and_isCyclic hℓ K hKℓ
  haveI : IsCyclic (RingAut K) := hcyc
  haveI : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  haveI : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  have hkerΘ : ∀ α : MulAut (adjointGroup Tag.E6 K), α ∈ Θ.ker ↔
      ∃ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
        α = MulAut.conj g * rootDiagAut Tag.E6 K a := by
    intro α
    rw [hker]
    constructor
    · rintro ⟨g, a, h⟩
      refine ⟨g, a, MulEquiv.ext fun x => Subtype.ext ?_⟩
      rw [h x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    · rintro ⟨g, a, rfl⟩
      refine ⟨g, a, fun x => ?_⟩
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
  have hM : ∀ y : Multiplicative (ZMod (exactE Tag.E6)), y ^ 2 = 1 := fun y =>
    (by decide : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1) y
  refine CFSG.LocalAnalysis.GLTheoremA.YS04E6F.meets_inner_of_data (inner (adjointGroup Tag.E6 K))
    Θ ?_ ?_ ?_ D hD hc
  · intro F hF
    exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_le_three_of_elemAbelian_prod
      (R := RingAut K) (M := Multiplicative (ZMod (exactE Tag.E6))) hM F hF
  · intro E hEker hE hEI
    exact card_le_three_of_inndiag E (fun x hx => (hkerΘ x).1 (hEker hx)) hEI
  · intro α hα3 hΘα
    have hnd : ∀ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
        α ≠ MulAut.conj g * rootDiagAut Tag.E6 K a := fun g a h =>
      hΘα (MonoidHom.mem_ker.1 ((hkerΘ α).2 ⟨g, a, h⟩))
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨d, T, r, j, ψ, hfd, hTord, hcardT, hT, hTjord, hαr, hψ⟩ :=
      exists_conj_entrywise_of_not_innerDiag Tag.E6 (Or.inl rfl) hf K hKℓ Nat.prime_three
        (by norm_num) α hα3 hnd
    refine ⟨ψ, fun δ hδ hcomm => ?_⟩
    have hψα : ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.E6 (T ^ j) := by
      rw [entrywiseAdjointAut_pow, ← hψ, conj_pow, hαr]
    obtain ⟨g, a, hδ'⟩ := (hkerΘ δ).1 hδ
    have hT' := exists_cube_of_fixed (T ^ j) hTjord h3
    rw [hψα, hδ'] at hcomm
    have hmat := eq_of_comm (T ^ j) hcomm
    have hdC := rootDiagUnit_mem_adjointGroup_of_twist (T ^ j) (hcube_E6 (T ^ j) hT') g.2 a hmat
    have hdd : MulAut.conj (⟨rootDiagUnit Tag.E6 a, hdC⟩ : adjointGroup Tag.E6 K) =
        rootDiagAut Tag.E6 K a :=
      MulEquiv.ext fun x => Subtype.ext (by rw [coe_rootDiagAut]; rfl)
    exact ⟨g * ⟨rootDiagUnit Tag.E6 a, hdC⟩, by rw [map_mul, hdd, hδ']⟩

end CFSG.LocalAnalysis.GLTheoremA.YS04E6F

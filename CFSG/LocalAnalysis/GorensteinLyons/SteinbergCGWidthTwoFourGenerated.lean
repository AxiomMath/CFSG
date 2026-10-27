module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCGCoreOrthogonal
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLSmallBinaryOrthogonal
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSymplecticSixLayer
public import CFSG.LinearAlgebra.SteinbergBQKernelBlocks

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup Module CFSG.RankThree.GroupTheory.SteinbergBY SteinbergCG
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open TauCeti.QuadraticMap (orthogonalGroup)
open QuadraticMap (polar polarBilin)
open CFSG.LargeEvenClassification.Helpers (pGeneratorRank pGeneratorRank_le_generators
  pGeneratorRank_generators)
open scoped commutatorElement IsMulCommutative

namespace SteinbergCG

theorem card_quotient_layer_le_of_le {X : Type*} [Group X] [Finite X] (K C : Subgroup X)
    (hCK : C ≤ K) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (φ : K →* Multiplicative V) (hφker : φ.ker = C.subgroupOf K) (W WR : Submodule (ZMod 2) V)
    (hWR : WR ≤ W) (hW : ∀ v, v ∈ W ↔ Multiplicative.ofAdd v ∈ φ.range)
    (hWRsub : ∀ v ∈ WR, ∃ k : K, (k : X) ∈ ⁅K, (⊤ : Subgroup X)⁆ ∧
      φ k = Multiplicative.ofAdd v)
    (hCM : C ≤ (frattini K).map K.subtype ⊔ ⁅K, ⊤⁆) :
    Nat.card (K ⧸ ((frattini K).map K.subtype ⊔ ⁅K, ⊤⁆).subgroupOf K) ≤
      2 ^ (finrank (ZMod 2) W - finrank (ZMod 2) WR) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  set M := (frattini K).map K.subtype ⊔ ⁅K, ⊤⁆ with hMdef
  set Mk := M.subgroupOf K with hMkdef
  have hKφ : Nat.card K = Nat.card C * Nat.card W := by
    rw [card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
    congr 1
    · rw [hφker]
      exact Nat.card_congr (subgroupOfEquivOfLe hCK).toEquiv
    · exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun x => by
        rw [hW]
        rfl)
  let φM : Mk →* Multiplicative V := φ.comp Mk.subtype
  have hMk : Nat.card C * Nat.card WR ≤ Nat.card Mk := by
    have h1 : Nat.card C ≤ Nat.card φM.ker := by
      refine Nat.card_le_card_of_injective
        (fun c => ⟨⟨⟨(c : X), hCK c.2⟩, mem_subgroupOf.mpr (hCM c.2)⟩, ?_⟩) ?_
      · rw [MonoidHom.mem_ker]
        change φ ⟨(c : X), hCK c.2⟩ = 1
        rw [← MonoidHom.mem_ker, hφker, mem_subgroupOf]
        exact c.2
      · intro c d hcd
        have := congrArg (fun x : φM.ker => (((x : Mk) : K) : X)) hcd
        exact Subtype.ext this
    have h2 : Nat.card WR ≤ Nat.card φM.range := by
      refine Nat.card_le_card_of_injective
        (fun v : WR => (⟨Multiplicative.ofAdd (v : V), ?_⟩ : φM.range)) ?_
      · obtain ⟨k, hkM, hk⟩ := hWRsub v v.2
        exact ⟨⟨k, mem_subgroupOf.mpr (mem_sup_right hkM)⟩, hk⟩
      · intro v w hvw
        have := congrArg (fun x : φM.range => Multiplicative.toAdd (x : Multiplicative V)) hvw
        exact Subtype.ext this
    calc Nat.card C * Nat.card WR ≤ Nat.card φM.ker * Nat.card φM.range :=
          Nat.mul_le_mul h1 h2
      _ = Nat.card Mk := by
          rw [card_eq_card_quotient_mul_card_subgroup φM.ker,
            Nat.card_congr (QuotientGroup.quotientKerEquivRange φM).toEquiv, mul_comm]
  have hWcard : Nat.card W = Nat.card WR * 2 ^ (finrank (ZMod 2) W - finrank (ZMod 2) WR) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := WR), Nat.card_zmod, ← pow_add]
    congr 1
    have := Submodule.finrank_mono hWR
    omega
  have hKMk := card_eq_card_quotient_mul_card_subgroup Mk
  have hpos : 0 < Nat.card Mk := Nat.card_pos
  have key : Nat.card Mk * Nat.card (K ⧸ Mk) ≤
      Nat.card Mk * 2 ^ (finrank (ZMod 2) W - finrank (ZMod 2) WR) := by
    calc Nat.card Mk * Nat.card (K ⧸ Mk) = Nat.card K := by rw [hKMk, mul_comm]
      _ = Nat.card C * Nat.card WR * 2 ^ (finrank (ZMod 2) W - finrank (ZMod 2) WR) := by
          rw [hKφ, hWcard]
          ring
      _ ≤ Nat.card Mk * 2 ^ (finrank (ZMod 2) W - finrank (ZMod 2) WR) :=
          Nat.mul_le_mul_right _ hMk
  exact Nat.le_of_mul_le_mul_left key hpos

section Orth

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem two_mul_finrank_le_of_forall_eq_zero (hb : (polarBilin q).Nondegenerate)
    {W : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, q w = 0) :
    2 * finrank (ZMod 2) W ≤ finrank (ZMod 2) V := by
  have hle : W ≤ LinearMap.BilinForm.orthogonal (polarBilin q) W := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [QuadraticMap.polarBilin_apply_apply, polar, hW _ (W.add_mem hw hx), hW w hw, hW x hx,
      sub_zero, sub_zero]
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hb] at h1
  have h2 := Submodule.finrank_le W
  omega

theorem isCyclic_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2) :
    IsCyclic G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  rcases (show Nat.card G = 1 ∨ Nat.card G = 2 by omega) with h1 | h2
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact isCyclic_of_subsingleton
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card h2

theorem card_le_two_of_finrank_moved_le_one (hb : (polarBilin q).Nondegenerate)
    (hV : finrank (ZMod 2) V = 4) (A : Subgroup (orthogonalGroup q)) (R : Submodule (ZMod 2) V)
    (hR : ∀ g ∈ A, ∀ v, (g : V ≃ₗ[ZMod 2] V) v - v ∈ R) (hR1 : finrank (ZMod 2) R ≤ 1) :
    Nat.card A ≤ 2 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (orthogonalGroup q) :=
    have := CFSG.LinearAlgebra.SteinbergBQ.finite_linearEquiv_zmod2 (V := V)
    inferInstance
  set T := LinearMap.BilinForm.orthogonal (polarBilin q) R with hTdef
  have hfixT : ∀ g ∈ A, ∀ u ∈ T, (g : V ≃ₗ[ZMod 2] V) u = u := by
    intro g hg u hu
    rw [← sub_eq_zero]
    refine hb.2 _ fun v => ?_
    have h1 : polar q v ((g : V ≃ₗ[ZMod 2] V) u) =
        polar q (((g⁻¹ : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) v) u := by
      conv_lhs => rw [← show (g : V ≃ₗ[ZMod 2] V)
          (((g⁻¹ : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) v) = v from by
        change ((g * g⁻¹ : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) v = v
        rw [mul_inv_cancel]
        rfl]
      exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup g.2 _ _
    have h2 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hu) _ (hR _ (inv_mem hg) v)
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_left, sub_eq_zero] at h2
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_right, h1, h2, sub_self]
  rcases (show finrank (ZMod 2) R = 0 ∨ finrank (ZMod 2) R = 1 by omega) with h0 | h1
  ·
    have hA : A = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [mem_bot]
      have hR0 := Submodule.finrank_eq_zero.mp h0
      refine Subtype.ext (LinearEquiv.ext fun v => ?_)
      have := hR g hg v
      rw [hR0, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    rw [hA, card_bot]
    norm_num
  · have hT3 : finrank (ZMod 2) T = 3 := by
      rw [hTdef, LinearMap.BilinForm.finrank_orthogonal hb, hV, h1]
    refine (card_le_of_le fun g hg => ?_).trans
      (SmallBinaryOrthogonal.card_pointwiseStab_hyperplane hb hV T hT3)
    exact fun u hu => hfixT g hg u hu

theorem pGeneratorRank_add_le_four (hb : (polarBilin q).Nondegenerate)
    (hV : finrank (ZMod 2) V = 4) (A : Subgroup (orthogonalGroup q)) (hA : IsPGroup 2 A)
    (W WR : Submodule (ZMod 2) V) (hWinv : ∀ g ∈ A, ∀ w ∈ W, (g : V ≃ₗ[ZMod 2] V) w ∈ W)
    (hWR : WR = Submodule.span (ZMod 2)
      {v | ∃ g ∈ A, ∃ w ∈ W, v = (g : V ≃ₗ[ZMod 2] V) w - w}) {dN : ℕ}
    (hdN : dN ≤ finrank (ZMod 2) W - finrank (ZMod 2) WR ∨
      (dN ≤ 1 + (finrank (ZMod 2) W - finrank (ZMod 2) WR) ∧ ∀ w ∈ W, q w = 0)) :
    pGeneratorRank 2 A + dN ≤ 4 := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (orthogonalGroup q) :=
    have := CFSG.LinearAlgebra.SteinbergBQ.finite_linearEquiv_zmod2 (V := V)
    inferInstance
  obtain ⟨-, a, c, hac⟩ :=
    ((small_binary_orthogonal_two_subgroups_and_stabilizers q hb (Or.inr hV)).2 hV).1 A hA
  have hdA2 : pGeneratorRank 2 A ≤ 2 := by
    have h := pGeneratorRank_le_generators Nat.prime_two hA {a, c}
      (by rw [Finset.coe_insert, Finset.coe_singleton]; exact hac)
    exact h.trans Finset.card_le_two
  have hdA1 : IsCyclic A → pGeneratorRank 2 A ≤ 1 := fun _ =>
    SymplecticSixLayer.pGeneratorRank_le_one_of_isCyclic Nat.prime_two hA
  have hdA0 : A = ⊥ → pGeneratorRank 2 A = 0 := by
    intro h
    have h1 := SymplecticSixLayer.pGeneratorRank_le_log_card 2 (X := A)
    have h2 : Nat.card A = 1 := by rw [h, card_bot]
    rw [h2, Nat.log_one_right] at h1
    omega
  have hmem : ∀ g ∈ A, ∀ w ∈ W, (g : V ≃ₗ[ZMod 2] V) w - w ∈ WR := fun g hg w hw =>
    hWR ▸ Submodule.subset_span ⟨g, hg, w, hw, rfl⟩
  have hWRW : WR ≤ W := by
    rw [hWR, Submodule.span_le]
    rintro _ ⟨g, hg, w, hw, rfl⟩
    exact W.sub_mem (hWinv g hg w hw) hw
  have hW4 : finrank (ZMod 2) W ≤ 4 := hV ▸ Submodule.finrank_le W
  have hWRle : finrank (ZMod 2) WR ≤ finrank (ZMod 2) W := Submodule.finrank_mono hWRW
  have hts : (∀ w ∈ W, q w = 0) → finrank (ZMod 2) W ≤ 2 := fun h => by
    have := two_mul_finrank_le_of_forall_eq_zero hb h
    omega
  have hfix : finrank (ZMod 2) WR = 0 → A ≤ SmallBinaryOrthogonal.pointwiseStab q W := by
    intro h0 g hg w hw
    have := hmem g hg w hw
    rw [Submodule.finrank_eq_zero.mp h0, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have hst3 : finrank (ZMod 2) W = 3 → finrank (ZMod 2) WR = 0 → Nat.card A ≤ 2 :=
    fun h3 h0 => (card_le_of_le (hfix h0)).trans
      (SmallBinaryOrthogonal.card_pointwiseStab_hyperplane hb hV W h3)
  have hst2 : finrank (ZMod 2) W = 2 → (∀ w ∈ W, q w = 0) → finrank (ZMod 2) WR = 0 →
      Nat.card A ≤ 2 := fun h2 hq h0 => (card_le_of_le (hfix h0)).trans
    (SmallBinaryOrthogonal.card_pointwiseStab_plane hb hV W h2 hq)
  have hst4 : finrank (ZMod 2) W = 4 → finrank (ZMod 2) WR ≤ 1 → Nat.card A ≤ 2 := by
    intro h4 h1
    have hWtop : W = ⊤ := Submodule.eq_top_of_finrank_eq (h4.trans hV.symm)
    exact card_le_two_of_finrank_moved_le_one hb hV A WR
      (fun g hg v => hmem g hg v (hWtop ▸ Submodule.mem_top)) h1
  have hA1 : finrank (ZMod 2) W = 4 → finrank (ZMod 2) WR = 0 → A = ⊥ := by
    intro h4 h0
    have hWtop : W = ⊤ := Submodule.eq_top_of_finrank_eq (h4.trans hV.symm)
    rw [eq_bot_iff]
    intro g hg
    rw [mem_bot]
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    exact hfix h0 hg v (hWtop ▸ Submodule.mem_top)
  rcases hdN with hdN | ⟨hdN, hq0⟩
  · by_cases hAc : IsCyclic A
    · by_cases hAt : A = ⊥
      · rw [hdA0 hAt]
        omega
      · have h1 := hdA1 hAc
        have h4 : finrank (ZMod 2) W = 4 → 1 ≤ finrank (ZMod 2) WR := fun h4 => by
          by_contra h0
          exact hAt (hA1 h4 (by omega))
        omega
    · have h3 : finrank (ZMod 2) W = 3 → 1 ≤ finrank (ZMod 2) WR := fun h3 => by
        by_contra h0
        exact hAc (isCyclic_of_card_le_two (hst3 h3 (by omega)))
      have h4 : finrank (ZMod 2) W = 4 → 2 ≤ finrank (ZMod 2) WR := fun h4 => by
        by_contra h0
        exact hAc (isCyclic_of_card_le_two (hst4 h4 (by omega)))
      omega
  · have h2 := hts hq0
    by_cases hAc : IsCyclic A
    · have := hdA1 hAc
      omega
    · have h3 : finrank (ZMod 2) W = 2 → 1 ≤ finrank (ZMod 2) WR := fun hW2 => by
        by_contra h0
        exact hAc (isCyclic_of_card_le_two (hst2 hW2 hq0 (by omega)))
      omega

end Orth

theorem pGeneratorRank_le_four_of_extraspecial {H : Type*} [Group H] [Finite H]
    (hH : CFSG.IsCharacteristicP 2 H) (hQ : IsExtraspecialPGroup 2 (CFSG.pCore 2 H))
    (hQ32 : Nat.card (CFSG.pCore 2 H) = 32) (P : Subgroup H) (hP : IsPGroup 2 P) :
    pGeneratorRank 2 P ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_center_eq_zpowers hQ.2.2.2
  have HQ := commPairHyp_of_extraspecial hQ hz
  have := HQ.isElementaryAbelian_quotient
  have : Finite (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) :=
    inferInstanceAs (Finite (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)))
  have : FiniteDimensional (ZMod 2) (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) :=
    Module.Finite.of_finite
  have hdim : finrank (ZMod 2) (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) = 4 :=
    finrank_quotient_center (w := 2) hQ (by rw [hQ32]; norm_num)
  have hb := polarBilin_sqQuad_nondegenerate HQ hz
  have hker := ker_coreOrth hH hQ HQ hz
  set K := (CFSG.pCore 2 H).subgroupOf P with hKdef
  set C := ((center (CFSG.pCore 2 H)).map (CFSG.pCore 2 H).subtype).subgroupOf P with hCdef
  have hCK : C ≤ K := fun x hx => by
    obtain ⟨c, -, hc⟩ := mem_subgroupOf.mp hx
    rw [hKdef, mem_subgroupOf, ← hc]
    exact c.2
  have : K.Normal := CFSG.pCore_normal.subgroupOf P
  have hK2 : IsPGroup 2 K := hP.to_subgroup K
  let φ : K →* Multiplicative (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) :=
    { toFun := fun x => Multiplicative.ofAdd (Additive.ofMul
        ((⟨((x : P) : H), x.2⟩ : CFSG.pCore 2 H) : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφker : φ.ker = C.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hCdef, mem_subgroupOf]
    change Multiplicative.ofAdd (Additive.ofMul
      ((⟨((x : P) : H), x.2⟩ : CFSG.pCore 2 H) : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) =
        Multiplicative.ofAdd (Additive.ofMul 1) ↔ _
    refine ((Multiplicative.ofAdd.injective.comp Additive.ofMul.injective).eq_iff).trans ?_
    refine (QuotientGroup.eq_one_iff _).trans ?_
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨c, hc, hceq⟩
      obtain rfl : c = ⟨((x : P) : H), x.2⟩ := Subtype.ext hceq
      exact hc
  let W : Submodule (ZMod 2) (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) :=
    { carrier := {v | Multiplicative.ofAdd v ∈ φ.range}
      add_mem' := fun {u v} hu hv => by
        change Multiplicative.ofAdd u * Multiplicative.ofAdd v ∈ φ.range
        exact mul_mem hu hv
      zero_mem' := one_mem φ.range
      smul_mem' := fun a {v} hv => by
        rcases SymplecticSixLayer.zmod_two_cases a with rfl | rfl
        · rw [zero_smul]
          exact one_mem φ.range
        · rwa [one_smul] }
  have hWmem : ∀ v, v ∈ W ↔ Multiplicative.ofAdd v ∈ φ.range := fun _ => Iff.rfl
  have hconj : ∀ h ∈ P, ∀ x : K, ∃ y : K, ((y : P) : H) = h * ((x : P) : H) * h⁻¹ ∧
      Multiplicative.toAdd (φ y) = ((coreOrth HQ hz h : orthogonalGroup (sqQuad HQ hz)) :
        Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) ≃ₗ[ZMod 2] _)
          (Multiplicative.toAdd (φ x)) := by
    intro h hh x
    have hQm : h * ((x : P) : H) * h⁻¹ ∈ CFSG.pCore 2 H := CFSG.pCore_normal.conj_mem _ x.2 h
    have hPm : h * ((x : P) : H) * h⁻¹ ∈ P := mul_mem (mul_mem hh (x : P).2) (inv_mem hh)
    refine ⟨⟨⟨_, hPm⟩, hQm⟩, rfl, ?_⟩
    rw [coreOrth_apply]
    change Additive.ofMul ((⟨h * ((x : P) : H) * h⁻¹, hQm⟩ : CFSG.pCore 2 H) :
        CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) =
      Additive.ofMul (centerQuotientHom (CFSG.pCore 2 H) (MulAut.conjNormal h)
        ((⟨((x : P) : H), x.2⟩ : CFSG.pCore 2 H) : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)))
    rw [CFSG.ComponentClassification.CentralCover.centerQuotientHom_apply_mk]
    rfl
  set A := P.map (coreOrth HQ hz) with hAdef
  have hA2 : IsPGroup 2 A := hP.map _
  have hWinv : ∀ g ∈ A, ∀ w ∈ W, (g : Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) ≃ₗ[ZMod 2]
      _) w ∈ W := by
    rintro _ ⟨h, hh, rfl⟩ w hw
    obtain ⟨x, hx⟩ := (hWmem w).mp hw
    obtain ⟨y, -, hy⟩ := hconj h hh x
    rw [hWmem]
    refine ⟨y, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hy, hx]
    rfl
  set WR : Submodule (ZMod 2) (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) :=
    Submodule.span (ZMod 2) {v | ∃ g ∈ A, ∃ w ∈ W,
      v = (g : Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) ≃ₗ[ZMod 2] _) w - w}
    with hWRdef
  have hWRW : WR ≤ W := by
    rw [hWRdef, Submodule.span_le]
    rintro _ ⟨g, hg, w, hw, rfl⟩
    exact W.sub_mem (hWinv g hg w hw) hw
  have hWRsub : ∀ v ∈ WR, ∃ k : K, (k : P) ∈ ⁅K, (⊤ : Subgroup P)⁆ ∧
      φ k = Multiplicative.ofAdd v := by
    let WRsub : Submodule (ZMod 2) (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) :=
      { carrier := {v | ∃ k : K, (k : P) ∈ ⁅K, (⊤ : Subgroup P)⁆ ∧ φ k = Multiplicative.ofAdd v}
        add_mem' := fun {u v} ⟨k, hk, hku⟩ ⟨l, hl, hlv⟩ =>
          ⟨k * l, mul_mem hk hl, by rw [map_mul, hku, hlv]; rfl⟩
        zero_mem' := ⟨1, one_mem _, map_one φ⟩
        smul_mem' := fun a {v} hv => by
          rcases SymplecticSixLayer.zmod_two_cases a with rfl | rfl
          · rw [zero_smul]
            exact ⟨1, one_mem _, map_one φ⟩
          · rwa [one_smul] }
    have hle : WR ≤ WRsub := by
      rw [hWRdef, Submodule.span_le]
      rintro _ ⟨_, ⟨h, hh, rfl⟩, w, hw, rfl⟩
      obtain ⟨x, hx⟩ := (hWmem w).mp hw
      obtain ⟨y, hy, hyφ⟩ := hconj h hh x
      refine ⟨y * x⁻¹, ?_, ?_⟩
      · have e : ((y * x⁻¹ : K) : P) = ⁅(x : P), ⟨h, hh⟩⁆⁻¹ := by
          apply Subtype.ext
          change ((y : P) : H) * ((x : P) : H)⁻¹ = _
          rw [hy]
          simp only [commutatorElement_def, Subgroup.coe_inv, Subgroup.coe_mul]
          group
        rw [e]
        exact inv_mem (commutator_mem_commutator x.2 (mem_top _))
      · rw [map_mul, map_inv]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_inv, hyφ, hx, toAdd_ofAdd, toAdd_ofAdd, sub_eq_add_neg]
    exact fun v hv => hle hv
  obtain ⟨-, -, -, -, dP, dQ, dN, hdP, hdQ, hdN, hle, -⟩ :=
    p_group_Frattini_coinvariant_generator_bound hP K rfl
  have hdPeq : pGeneratorRank 2 P = dP := by
    rw [pGeneratorRank, hdP, Nat.log_pow (by norm_num)]
  have hdQeq : pGeneratorRank 2 (P ⧸ K) = dQ := by
    rw [pGeneratorRank, hdQ, Nat.log_pow (by norm_num)]
  have hdQA : pGeneratorRank 2 (P ⧸ K) = pGeneratorRank 2 A := by
    let ψ : P →* orthogonalGroup (sqQuad HQ hz) := (coreOrth HQ hz).comp P.subtype
    have hkerψ : K = ψ.ker := by
      ext x
      rw [hKdef, mem_subgroupOf, MonoidHom.mem_ker]
      change (x : H) ∈ CFSG.pCore 2 H ↔ coreOrth HQ hz x = 1
      rw [← MonoidHom.mem_ker, hker]
    have hrange : ψ.range = A := by rw [MonoidHom.range_comp, range_subtype]
    exact SymplecticSixLayer.pGeneratorRank_congr ((QuotientGroup.quotientMulEquivOfEq hkerψ).trans
      ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange)))
  have hlayer := SymplecticSixLayer.card_quotient_layer_le hP K C hCK φ hφker W WR hWRW hWmem
    hWRsub
  rw [hdN] at hlayer
  have hdNC : dN ≤ pGeneratorRank 2 C +
      (finrank (ZMod 2) W - finrank (ZMod 2) WR) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp hlayer
  have hCcard : Nat.card C ≤ 2 := by
    calc Nat.card C ≤ Nat.card ((center (CFSG.pCore 2 H)).map (CFSG.pCore 2 H).subtype) :=
          Nat.card_le_card_of_injective (fun x => ⟨((x : P) : H), x.2⟩) fun x y hxy => by
            have h := congrArg
              (fun t : (center (CFSG.pCore 2 H)).map (CFSG.pCore 2 H).subtype => (t : H)) hxy
            exact Subtype.ext (Subtype.ext h)
      _ = 2 := by rw [card_map_of_injective (Subgroup.subtype_injective _), hQ.2.2.2]
  have hdC1 : pGeneratorRank 2 C ≤ 1 := by
    refine (SymplecticSixLayer.pGeneratorRank_le_log_card 2).trans
      ((Nat.log_mono_right hCcard).trans ?_)
    simpa using (Nat.log_pow (b := 2) (by norm_num) 1).le
  have hdisj : dN ≤ finrank (ZMod 2) W - finrank (ZMod 2) WR ∨
      (dN ≤ 1 + (finrank (ZMod 2) W - finrank (ZMod 2) WR) ∧ ∀ w ∈ W, sqQuad HQ hz w = 0) := by
    by_cases hC : C = ⊥
    · left
      have hdC0 : pGeneratorRank 2 C = 0 := by
        have h1 := SymplecticSixLayer.pGeneratorRank_le_log_card 2 (X := C)
        have h2 : Nat.card C = 1 := by rw [hC, card_bot]
        rw [h2, Nat.log_one_right] at h1
        omega
      omega
    · by_cases hq0 : ∀ w ∈ W, sqQuad HQ hz w = 0
      · right
        exact ⟨by omega, hq0⟩
      · left
        push Not at hq0
        obtain ⟨w, hw, hqw⟩ := hq0
        obtain ⟨x, hx⟩ := (hWmem w).mp hw
        have hwx : w = Additive.ofMul
            ((⟨((x : P) : H), x.2⟩ : CFSG.pCore 2 H) : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) :=
          (congrArg Multiplicative.toAdd hx).symm
        have hq1 : sqVal z ((⟨((x : P) : H), x.2⟩ : CFSG.pCore 2 H) :
            CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) = 1 :=
          SmallBinaryOrthogonal.eq_one_of_ne_zero (by
            rw [sqQuad_apply, hwx] at hqw
            exact hqw)
        have hsq : (⟨((x : P) : H), x.2⟩ : CFSG.pCore 2 H) ^ 2 = z := by
          rw [HQ.sq_eq_zpow_sqVal hz, hq1]
          exact pow_one z
        have : Fact (IsPGroup 2 K) := ⟨hK2⟩
        have hx2 : x ^ 2 ∈ frattini K := CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) x
        have hCM : C ≤ (frattini K).map K.subtype ⊔ ⁅K, ⊤⁆ := by
          intro c hc
          obtain ⟨c', hc', hc'eq⟩ := mem_subgroupOf.mp hc
          rw [hz] at hc'
          rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two HQ.orderOf_eq hc' with h1 | h1
          · have : c = 1 := by
              apply Subtype.ext
              rw [← hc'eq, h1]
              rfl
            rw [this]
            exact one_mem _
          · refine mem_sup_left ⟨x ^ 2, hx2, ?_⟩
            apply Subtype.ext
            rw [← hc'eq, h1, ← hsq]
            rfl
        have h1 := card_quotient_layer_le_of_le K C hCK φ hφker W WR hWRW hWmem hWRsub hCM
        rw [hdN] at h1
        exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have htable := pGeneratorRank_add_le_four hb hdim A hA2 W WR hWinv hWRdef hdisj
  omega

end SteinbergCG

theorem extraspecial_width_two_subgroups_four_generated {H : Type*} [Group H] [Finite H]
    (hH : CFSG.IsCharacteristicP 2 H) (hQ : IsExtraspecialPGroup 2 (CFSG.pCore 2 H))
    (hQ32 : Nat.card (CFSG.pCore 2 H) = 32) :
    (∀ P : Subgroup H, IsPGroup 2 P → ∃ S : Finset H, S.card ≤ 4 ∧ closure (S : Set H) = P) ∧
    ∀ P : Subgroup H, IsPGroup 2 P → ∀ (N : Subgroup P) [N.Normal],
      CFSG.IsElementaryAbelian 2 (P ⧸ N) → Nat.card (P ⧸ N) ≤ 2 ^ 4 := by
  refine ⟨fun P hP => ?_, fun P hP N _ hEA => ?_⟩
  · have hd := pGeneratorRank_le_four_of_extraspecial hH hQ hQ32 P hP
    obtain ⟨S, hS, hScard⟩ := pGeneratorRank_generators Nat.prime_two hP
    refine ⟨S.map ⟨P.subtype, P.subtype_injective⟩, by rw [Finset.card_map]; omega, ?_⟩
    rw [Finset.coe_map, Function.Embedding.coeFn_mk, ← MonoidHom.map_closure, hS,
      ← MonoidHom.range_eq_map, range_subtype]
  · have hd := pGeneratorRank_le_four_of_extraspecial hH hQ hQ32 P hP
    have hle : frattini P ≤ N := CFSG.SectionRank.Ccomm.frattini_le_of_quotient_elementary
      (p := 2) N (fun a b => hEA.is_comm.comm a b)
      (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hEA.exponent_dvd_p a)
    have hdvd : N.index ∣ (frattini P).index := index_dvd_of_le hle
    have hΦ : (frattini P).index = 2 ^ pGeneratorRank 2 P :=
      SymplecticSixLayer.card_frattini_quotient_eq_pow Nat.prime_two hP
    calc Nat.card (P ⧸ N) = N.index := rfl
      _ ≤ (frattini P).index := Nat.le_of_dvd (by rw [hΦ]; positivity) hdvd
      _ = 2 ^ pGeneratorRank 2 P := hΦ
      _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hd

end CFSG.LocalAnalysis.GorensteinLyons

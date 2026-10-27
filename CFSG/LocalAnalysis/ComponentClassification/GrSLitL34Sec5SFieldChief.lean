module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourConjugacy
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabA
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.MinimalNormal

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem exists_elemAbelian_card_of_lieModel_psl_three {X : Type} [Group X] [Finite X] {m : ℕ}
    (hX : Blueprint.LieModel X .PSL 3 2 m) :
    ∃ E : Subgroup X, Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ (2 * m) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  set V := (QuasithinUnique.Fin257.L3.V1 : Subgroup (LinearFlag.projectiveSL 3 K))
  refine ⟨V.map e.symm.toMonoidHom, ?_, ?_⟩
  · have hV := QuasithinUnique.Fin257.L3.isElemAbelian_V1 (F := K)
    refine ⟨?_, ?_⟩
    · have := hV.1
      exact isMulCommutative_iff_of_setLike.mpr fun a ha b hb => by
        obtain ⟨a', ha', rfl⟩ := ha
        obtain ⟨b', hb', rfl⟩ := hb
        rw [← map_mul, ← map_mul, (isMulCommutative_iff_of_setLike.mp this) a' ha' b' hb']
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hV.2 a ha, map_one]
  · rw [card_map_of_injective e.symm.injective, GH74.QTGen4.DSGen4.L34.card_V1, hK, ← pow_mul,
      mul_comm]

theorem exists_conj_of_lieModel_psl_three {X : Type} [Group X] [Finite X] {m : ℕ}
    (hX : Blueprint.LieModel X .PSL 3 2 m) {x y : X}
    (hx : x * x = 1) (hx1 : x ≠ 1) (hy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ g : X, g * x * g⁻¹ = y := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  have hx' : e x * e x = 1 := by rw [← map_mul, hx, map_one]
  have hy' : e y * e y = 1 := by rw [← map_mul, hy, map_one]
  have hx1' : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  have hy1' : e y ≠ 1 := fun h => hy1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g₁, hg₁⟩ := LinearFieldFour.exists_conj_eq_wP_one (e x) hx' hx1'
  obtain ⟨g₂, hg₂⟩ := LinearFieldFour.exists_conj_eq_wP_one (e y) hy' hy1'
  set c := (LinearFlag.proj 3 K g₂)⁻¹ * LinearFlag.proj 3 K g₁
  refine ⟨e.symm c, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
  have h : c * e x * c⁻¹ = (LinearFlag.proj 3 K g₂)⁻¹ * (LinearFlag.proj 3 K g₁ * e x *
      (LinearFlag.proj 3 K g₁)⁻¹) * LinearFlag.proj 3 K g₂ := by
    simp only [c]
    group
  rw [h, hg₁, ← hg₂]
  group


theorem fusionZStar_eq_fusionOddCore_of_lieModel_psl_three (hGA : Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] [Group.IsPerfect X] {m : ℕ} (hm : 3 ≤ m)
    (hX : Blueprint.LieModel (X ⧸ Open.fusionZStar X) .PSL 3 2 m) :
    Open.fusionZStar X = Open.fusionOddCore X := by
  classical
  set O := Open.fusionOddCore X with hO
  set Z := Open.fusionZStar X with hZ
  have hOZ : O ≤ Z := fun x hx => by
    change QuotientGroup.mk' O x ∈ center (X ⧸ O)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  set q : X ⧸ O →* X ⧸ Z := QuotientGroup.map O Z (MonoidHom.id X) hOZ with hqdef
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
    exact ⟨QuotientGroup.mk' O x, rfl⟩
  have hker : q.ker = center (X ⧸ O) := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk' Z x = 1) ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have : Group.IsPerfect (X ⧸ O) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  obtain ⟨-, h, -, -, -, hmap, -⟩ :=
    RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier q hq hker.le
  have hdvd : Nat.card (center (X ⧸ O)) ∣
      Nat.card (RankThree.PerfectCover.hopfMultiplier (X ⧸ Z)) := by
    rw [← hker, ← hmap]
    exact Subgroup.card_map_dvd _ _
  have hcl := LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel hX (by decide)
  obtain ⟨-, ⟨e⟩⟩ := hGA (X ⧸ Z) .PSL 3 2 m ⟨hcl.1, Or.inl hcl⟩
  have hex : Blueprint.Multiplier.exceptionalOrders .PSL 3 2 m = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  have hM : Nat.card (RankThree.PerfectCover.hopfMultiplier (X ⧸ Z)) =
      Nat.gcd 3 (2 ^ m - 1) := by
    let e' := (RankThree.PerfectCover.hopfMultiplierEquivGriess (X ⧸ Z)).symm.trans e
    rw [Nat.card_congr e'.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod]
    have hg1 : (Blueprint.Multiplier.genericOrders .PSL 3 2 m).1 = Nat.gcd 3 (2 ^ m - 1) := rfl
    have hg2 : (Blueprint.Multiplier.genericOrders .PSL 3 2 m).2 = 1 := rfl
    have hc : ∀ k : ℕ, Nat.card (Multiplicative (ZMod k)) = k := fun k => by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    simp only [hc, hg1, hg2, hex]
    simp
  have hodd : Odd (Nat.card (center (X ⧸ O))) := by
    refine Odd.of_dvd_nat ?_ (hdvd.trans (hM ▸ Nat.gcd_dvd_left 3 (2 ^ m - 1)))
    decide
  have hcen : center (X ⧸ O) = ⊥ := by
    have hle : center (X ⧸ O) ≤ Open.fusionOddCore (X ⧸ O) :=
      le_sSup ⟨inferInstance, hodd⟩
    rw [EvenSporadicStandard.Fin76b.fusionOddCore_quotient_eq_bot] at hle
    exact le_bot_iff.mp hle
  change (center (X ⧸ O)).comap (QuotientGroup.mk' O) = O
  rw [hcen, MonoidHom.comap_bot, QuotientGroup.ker_mk']

end CFSG.ComponentClassification.GrSLit.L34Sec5S

namespace CFSG.ComponentClassification.Walter86

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem exists_irreducible_chiefFactor_dvd_card_centralizer {U Y : Subgroup X} [hUn : U.Normal]
    [hYn : Y.Normal] (hUodd : Odd (Nat.card U)) (hYperf : ⁅Y, Y⁆ = Y) (hne : ⁅U, Y⁆ ≠ ⊥) :
    ∃ (p : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (_ : Finite V)
        (ρ : Representation (ZMod p) X V),
        ρ.IsIrreducible ∧ (∃ g ∈ Y, ∃ v : V, ρ g v ≠ v) ∧
        (∀ g ∈ ⁅U, Y⁆, ∀ v : V, ρ g v = v) ∧
        ∀ u : X, u ^ 2 = 1 →
          p ^ Module.finrank (ZMod p) (LinearMap.ker (ρ u - 1)) ∣
            Nat.card ↥(⁅U, Y⁆ ⊓ centralizer ({u} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Set (Subgroup X) := {R | R.Normal ∧ R ≤ U ∧ ¬ ⁅U, Y⁆ ≤ R} with hSdef
  have hbot : (⊥ : Subgroup X) ∈ S := ⟨inferInstance, bot_le, fun h => hne (le_bot_iff.mp h)⟩
  obtain ⟨R, ⟨hRn, hRU, hRc⟩, hRmax⟩ := (Set.toFinite S).exists_maximal ⟨⊥, hbot⟩
  have := hRn
  set π := QuotientGroup.mk' R with hπ
  have hCU : ⁅U, Y⁆ ≤ U := Subgroup.commutator_le_left U Y
  set W := (⁅U, Y⁆).map π with hW
  have hWn : W.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective R)
  have hWne : W ≠ ⊥ := by
    rw [Ne, hW, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hRc
  have hWmin : ∀ N : Subgroup (X ⧸ R), N.Normal → N ≤ W → N = ⊥ ∨ N = W := by
    intro N hN hNW
    by_cases hc : ⁅U, Y⁆ ≤ N.comap π
    · exact Or.inr (le_antisymm hNW (Subgroup.map_le_iff_le_comap.mpr hc))
    · left
      have hMU : N.comap π ≤ U := by
        have h1 : N.comap π ≤ W.comap π := Subgroup.comap_mono hNW
        rw [hW, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
        exact h1.trans (sup_le hCU hRU)
      have hRM : R ≤ N.comap π := by
        intro r hr
        have h1 : π r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
        rw [Subgroup.mem_comap, h1]
        exact one_mem N
      have hle := hRmax ⟨hN.comap π, hMU, hc⟩ hRM
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R q
      exact (Subgroup.mem_bot).mpr ((QuotientGroup.eq_one_iff g).mpr (hle hq))
  have hWodd : Odd (Nat.card W) :=
    hUodd.of_dvd_nat ((Subgroup.card_map_dvd ⁅U, Y⁆ π).trans (Subgroup.card_dvd_of_le hCU))
  have : Group.IsSolvable W := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hWodd
  obtain ⟨p, hp, hWcomm, hWexp⟩ :=
    CFSG.EvenSporadicStandard.HNRecog.GH73.minimal_normal_elementary_of_solvable W hWne hWmin
  have hpf : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hWne
    have hw2 : w ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hWexp _ w.2)
    have hdvd : 2 ∣ Nat.card W := orderOf_eq_prime hw2 hw1 ▸ orderOf_dvd_natCard w
    exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr hdvd)
  let : CommGroup W :=
    { (inferInstance : Group W) with mul_comm := fun a b => Subtype.ext (hWcomm a a.2 b b.2) }
  have hexpV : ∀ v : Additive W, p • v = 0 := by
    intro v
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hWexp _ (Additive.toMul v).2)
  let hmod : Module (ZMod p) (Additive W) := AddCommGroup.zmodModule (n := p) hexpV
  let θ : X →* MulAut W := MulAut.conjNormal.comp π
  let f : X → (Additive W →ₗ[ZMod p] Additive W) := fun g =>
    AddMonoidHom.toZModLinearMap p (MonoidHom.toAdditive (θ g).toMonoidHom)
  have hf : ∀ g v, Additive.toMul (f g v) = θ g (Additive.toMul v) := fun _ _ => rfl
  let ρ : Representation (ZMod p) X (Additive W) :=
    { toFun := f
      map_one' := LinearMap.ext fun v => Additive.toMul.injective (by
        rw [hf, map_one]; rfl)
      map_mul' := fun g h => LinearMap.ext fun v => Additive.toMul.injective (by
        rw [hf, Module.End.mul_apply, hf, hf, map_mul]; rfl) }
  have hρ : ∀ (g : X) (v : Additive W), ρ g v = Additive.ofMul (θ g (Additive.toMul v)) :=
    fun _ _ => rfl
  have hθ : ∀ (g : X) (w : W), ((θ g w : W) : X ⧸ R) = π g * w * (π g)⁻¹ := fun _ _ => rfl
  have hfix : ∀ (g : X) (v : Additive W),
      ρ g v = v ↔ π g * ((Additive.toMul v : W) : X ⧸ R) * (π g)⁻¹ =
        ((Additive.toMul v : W) : X ⧸ R) := by
    intro g v
    rw [hρ, ← hθ]
    constructor
    · intro h
      exact congrArg (fun w => ((Additive.toMul w : W) : X ⧸ R)) h
    · intro h
      exact Additive.toMul.injective (Subtype.ext h)
  have hirr : ρ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
      obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hWne
      have hmem : Additive.ofMul w ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
      rw [← h] at hmem
      have h0 : Additive.ofMul w = 0 := (Submodule.mem_bot _).mp hmem
      exact hw1 (Additive.ofMul.injective h0)
    refine { toNontrivial := hnt, eq_bot_or_eq_top := fun σ => ?_ }
    let N : Subgroup (X ⧸ R) :=
      { carrier := {q | ∃ h : q ∈ W, Additive.ofMul (⟨q, h⟩ : W) ∈ σ.toSubmodule}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨W.mul_mem ha hb, ?_⟩
          have h := σ.toSubmodule.add_mem ha' hb'
          rw [← ofMul_mul] at h
          exact h
        one_mem' := ⟨W.one_mem, σ.toSubmodule.zero_mem⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          exact ⟨W.inv_mem ha, σ.toSubmodule.neg_mem ha'⟩ }
    have hNn : N.Normal := ⟨fun q ⟨hq, hq'⟩ g' => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R g'
      exact ⟨hWn.conj_mem q hq _, σ.apply_mem_toSubmodule g hq'⟩⟩
    rcases hWmin N hNn (fun q ⟨hq, _⟩ => hq) with hN | hN
    · left
      apply Subrepresentation.toSubmodule_injective
      show σ.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro v hv
      have hvN : ((Additive.toMul v : W) : X ⧸ R) ∈ N := ⟨(Additive.toMul v).2, hv⟩
      rw [hN] at hvN
      have h1 : Additive.toMul v = 1 := Subtype.ext ((Subgroup.mem_bot).mp hvN)
      rw [Submodule.mem_bot, ← ofMul_toMul v, h1, ofMul_one]
    · right
      apply Subrepresentation.toSubmodule_injective
      show σ.toSubmodule = ⊤
      rw [eq_top_iff]
      intro v _
      have hvN : ((Additive.toMul v : W) : X ⧸ R) ∈ N := by
        rw [hN]
        exact (Additive.toMul v).2
      obtain ⟨_, h⟩ := hvN
      exact h
  have hYact : ∃ g ∈ Y, ∃ v : Additive W, ρ g v ≠ v := by
    by_contra hcon
    push Not at hcon
    have h1 : ⁅⁅U, Y⁆, Y⁆ ≤ R := by
      rw [Subgroup.commutator_le]
      intro c hc g hg
      have hcw : π c ∈ W := Subgroup.mem_map_of_mem π hc
      have h2 := (hfix g (Additive.ofMul ⟨π c, hcw⟩)).mp (hcon g hg _)
      have h3 : π c * π g = π g * π c := by
        change π g * π c * (π g)⁻¹ = π c at h2
        rw [mul_inv_eq_iff_eq_mul] at h2
        exact h2.symm
      apply (QuotientGroup.eq_one_iff _).mp
      change π ⁅c, g⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h3
    have h3 : ⁅⁅U.map π, Y.map π⁆, Y.map π⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk']
      exact h1
    have h4 : ⁅⁅Y.map π, Y.map π⁆, U.map π⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate
        (by rw [Subgroup.commutator_comm (Y.map π) (U.map π)]; exact h3) h3
    have h5 : ⁅Y.map π, Y.map π⁆ = Y.map π := by rw [← Subgroup.map_commutator, hYperf]
    rw [h5, Subgroup.commutator_comm, ← Subgroup.map_commutator] at h4
    exact hWne h4
  have htriv : ∀ g ∈ ⁅U, Y⁆, ∀ v : Additive W, ρ g v = v := by
    intro g hg v
    rw [hfix]
    have hgw : π g ∈ W := Subgroup.mem_map_of_mem π hg
    rw [hWcomm (π g) hgw _ (Additive.toMul v).2, mul_inv_cancel_right]
  have hcount : ∀ u : X, u ^ 2 = 1 →
      p ^ Module.finrank (ZMod p) (LinearMap.ker (ρ u - 1)) ∣
        Nat.card ↥(⁅U, Y⁆ ⊓ centralizer ({u} : Set X)) := by
    intro u hu
    set D := ⁅U, Y⁆ with hD
    have hDn : D.Normal := Subgroup.commutator_normal U Y
    let φ : ↥(D ⊓ centralizer ({u} : Set X)) →* ↥W :=
      { toFun := fun x => ⟨π (x : X), Subgroup.mem_map_of_mem π (Subgroup.mem_inf.mp x.2).1⟩
        map_one' := Subtype.ext (map_one π)
        map_mul' := fun x y => Subtype.ext (map_mul π (x : X) (y : X)) }
    have hφ : ∀ x : ↥(D ⊓ centralizer ({u} : Set X)), ((φ x : W) : X ⧸ R) = π (x : X) :=
      fun _ => rfl
    have hrange : ∀ w : W, w ∈ φ.range ↔ ρ u (Additive.ofMul w) = Additive.ofMul w := by
      intro w
      rw [hfix]
      constructor
      · rintro ⟨x, rfl⟩
        have hxu : u * (x : X) = x * u :=
          (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2).symm
        change π u * π x * (π u)⁻¹ = π x
        rw [← map_mul, ← map_inv, ← map_mul, hxu, mul_inv_cancel_right]
      · intro hw
        let fD : ↥D →* ↥W := π.subgroupMap D
        have hfs : Function.Surjective fD := π.subgroupMap_surjective D
        have hDU : D ≤ U := Subgroup.commutator_le_left U Y
        have hker : Odd (Nat.card fD.ker) :=
          hUodd.of_dvd_nat ((Subgroup.card_subgroup_dvd_card fD.ker).trans
            (Subgroup.card_dvd_of_le hDU))
        have hinv : Function.Involutive (MulAut.conjNormal u : MulAut ↥D) := by
          intro x
          apply Subtype.ext
          rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
          have hu' : u * u = 1 := by rw [← pow_two, hu]
          rw [inv_eq_of_mul_eq_one_right hu']
          calc u * (u * (x : X) * u) * u = (u * u) * x * (u * u) := by simp only [mul_assoc]
            _ = x := by rw [hu', one_mul, mul_one]
        have hequiv : ∀ x : ↥D, fD (MulAut.conjNormal u x) = MulAut.conjNormal (π u) (fD x) := by
          intro x
          apply Subtype.ext
          rw [MulAut.conjNormal_apply]
          change π ((MulAut.conjNormal u x : ↥D) : X) = _
          rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv]
          rfl
        have hwfix : MulAut.conjNormal (π u) w = w := by
          apply Subtype.ext
          rw [MulAut.conjNormal_apply]
          exact hw
        obtain ⟨x, hx, hxfix⟩ := CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_odd_kernel
          (MulAut.conjNormal u) (MulAut.conjNormal (π u)) hinv fD hfs hker hequiv w hwfix
        have hxfix' : u * (x : X) * u⁻¹ = x := by
          have := congrArg Subtype.val hxfix
          rwa [MulAut.conjNormal_apply] at this
        have hxc : (x : X) ∈ centralizer ({u} : Set X) := by
          rw [mem_centralizer_singleton_iff]
          rw [mul_inv_eq_iff_eq_mul] at hxfix'
          exact hxfix'.symm
        refine ⟨⟨x, Subgroup.mem_inf.mpr ⟨x.2, hxc⟩⟩, Subtype.ext ?_⟩
        rw [hφ]
        exact congrArg Subtype.val hx
    have hcard : Nat.card ↥(LinearMap.ker (ρ u - 1)) = Nat.card ↥φ.range := by
      refine Nat.card_congr
        { toFun := fun v => ⟨Additive.toMul (v : Additive W), (hrange _).mpr ?_⟩
          invFun := fun w => ⟨Additive.ofMul (w : W), ?_⟩
          left_inv := fun v => rfl
          right_inv := fun w => rfl }
      · have hv := v.2
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
        exact hv
      · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
        exact (hrange w).mp w.2
    have : Fintype (Additive W) := Fintype.ofFinite _
    have : Fintype ↥(LinearMap.ker (ρ u - 1)) := Fintype.ofFinite _
    have hpow : Nat.card ↥(LinearMap.ker (ρ u - 1)) =
        p ^ Module.finrank (ZMod p) (LinearMap.ker (ρ u - 1)) := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
    rw [← hpow, hcard]
    exact Subgroup.card_range_dvd φ
  exact ⟨p, hpf, hp2, Additive W, inferInstance, hmod, inferInstance, ρ, hirr, hYact, htriv,
    hcount⟩

end CFSG.ComponentClassification.Walter86

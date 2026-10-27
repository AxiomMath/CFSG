module

public import CFSG.GF2Type.Smith1980Orth.S3Types
public import CFSG.GF2Type.Smith1980Orth.Transport
public import CFSG.LargeExtraspecial.S14SMKDeltaRank
public import CFSG.LargeExtraspecial.S14SMKTransOuter
public import CFSG.LargeExtraspecial.S14SMKTransLift
public import CFSG.LargeExtraspecial.S14SMKDelta32
import Mathlib.GroupTheory.GroupAction.Quotient
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.LargeExtraspecial.PSL10Fix
public import CFSG.LargeExtraspecial.S12InspUse
public import CFSG.LargeExtraspecial.S14C12Lit
public import CFSG.LargeExtraspecial.S14SMEPath
public import CFSG.LargeExtraspecial.S14SMHDefs
public import CFSG.LargeExtraspecial.S14SMIDefs
public import CFSG.LargeExtraspecial.S14SMKDivMain
public import CFSG.LargeExtraspecial.S14W4LocCase
public import CFSG.LargeExtraspecial.S3cOddCore
public import CFSG.LargeExtraspecial.S3cSix
public import CFSG.LargeExtraspecial.S9GenA
public import CFSG.LargeExtraspecial.S9GenG
public import CFSG.LargeExtraspecial.S9PD
public import CFSG.LargeExtraspecial.S9RBQOdd
public import CFSG.LargeExtraspecial.S9TwoB
public import CFSG.LargeExtraspecial.S9TwoN
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Sporadic.Th.KernelOrder
public import CFSG.Sporadic.Th.KernelOrderBase
public import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.Max3Aut
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

namespace CaseB

section Basic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem lin_apply_inv_apply' (g : V ≃ₗ[ZMod 2] V) (v : V) : g (g⁻¹ v) = v := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]
  rfl

@[expose] def pstab (Q : QuadraticForm (ZMod 2) V) (Z : Submodule (ZMod 2) V) :
    Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {e | (∀ v, Q (e v) = Q v) ∧ ∀ z ∈ Z, e z = z}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun v => ?_, fun z hz => ?_⟩
    · rw [LinearEquiv.mul_apply, ha1, hb1]
    · rw [LinearEquiv.mul_apply, hb2 z hz, ha2 z hz]
  one_mem' := ⟨fun v => rfl, fun z _ => rfl⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun v => ?_, fun z hz => ?_⟩
    · have := ha1 (a⁻¹ v)
      rw [lin_apply_inv_apply'] at this
      exact this.symm
    · have := ha2 z hz
      calc a⁻¹ z = a⁻¹ (a z) := by rw [this]
        _ = z := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

theorem mem_pstab_iff {Q : QuadraticForm (ZMod 2) V} {Z : Submodule (ZMod 2) V}
    {e : V ≃ₗ[ZMod 2] V} : e ∈ pstab Q Z ↔ (∀ v, Q (e v) = Q v) ∧ ∀ z ∈ Z, e z = z :=
  Iff.rfl

private theorem polar_apply_of_isometry {Q : QuadraticForm (ZMod 2) V} {e : V ≃ₗ[ZMod 2] V}
    (he : ∀ v, Q (e v) = Q v) (u v : V) : polar Q (e u) (e v) = polar Q u v := by
  simp only [polar, ← map_add, he]

private theorem zmod_two_add_eq_zero {a b : ZMod 2} : a + b = 0 ↔ a = b := by
  revert a b
  decide

private theorem exists_Yr (Q : QuadraticForm (ZMod 2) V) {W : Submodule (ZMod 2) V}
    (hW : ∀ y ∈ W, ∀ y' ∈ W, polar Q y y' = 0) (r : V) :
    ∃ Y : Submodule (ZMod 2) V, ∀ y, y ∈ Y ↔ y ∈ W ∧ Q y = polar Q r y := by
  refine ⟨{ carrier := {y | y ∈ W ∧ Q y = polar Q r y}
            add_mem' := ?_
            zero_mem' := ?_
            smul_mem' := ?_ }, fun y => Iff.rfl⟩
  · rintro y y' ⟨hy, hqy⟩ ⟨hy', hqy'⟩
    refine ⟨W.add_mem hy hy', ?_⟩
    rw [map_add_eq, hW y hy y' hy', add_zero, hqy, hqy', polar_add_right]
  · exact ⟨W.zero_mem, by simp⟩
  · rintro c y ⟨hy, hqy⟩
    refine ⟨W.smul_mem c hy, ?_⟩
    have hc : c * c = c := by
      revert c
      decide
    rw [QuadraticMap.map_smul, polar_smul_right, hqy, smul_eq_mul, smul_eq_mul, hc]

end Basic

section Count

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private instance instFiniteOfFD : Finite V := Module.finite_of_finite (ZMod 2)

private theorem card_orbit_le_of_sub_mem {Q : QuadraticForm (ZMod 2) V}
    {Z : Submodule (ZMod 2) V} {r : V} {Y : Submodule (ZMod 2) V}
    (hY : ∀ e ∈ pstab Q Z, e r - r ∈ Y) :
    Nat.card (MulAction.orbit ↥(pstab Q Z) r) ≤ 2 ^ finrank (ZMod 2) Y := by
  have h1 : Nat.card (MulAction.orbit ↥(pstab Q Z) r) ≤ Nat.card Y := by
    refine Nat.card_le_card_of_injective (fun v => ⟨v.1 - r, ?_⟩) ?_
    · obtain ⟨⟨e, he⟩, hv⟩ := v.2
      have : e r = v.1 := hv
      rw [← this]
      exact hY e he
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (sub_left_inj.mp this)
  have h2 : Nat.card Y = 2 ^ finrank (ZMod 2) Y := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Y), Nat.card_zmod]
  exact h1.trans h2.le

private noncomputable def stabEquiv (Q : QuadraticForm (ZMod 2) V) (Z : Submodule (ZMod 2) V)
    (r : V) :
    MulAction.stabilizer ↥(pstab Q Z) r ≃ pstab Q (Z ⊔ Submodule.span (ZMod 2) {r}) where
  toFun e := ⟨(e.1 : V ≃ₗ[ZMod 2] V), e.1.2.1, fun z hz => by
    have hr : (e.1 : V ≃ₗ[ZMod 2] V) r = r := MulAction.mem_stabilizer_iff.mp e.2
    obtain ⟨z₁, hz₁, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_add, map_smul, hr, e.1.2.2 z₁ hz₁]⟩
  invFun e := ⟨⟨(e : V ≃ₗ[ZMod 2] V), e.2.1, fun z hz => e.2.2 z (Submodule.mem_sup_left hz)⟩,
    MulAction.mem_stabilizer_iff.mpr (e.2.2 r (Submodule.mem_sup_right
      (Submodule.mem_span_singleton_self r)))⟩
  left_inv e := rfl
  right_inv e := rfl

theorem card_pstab_le (Q : QuadraticForm (ZMod 2) V) (hQ : Q.polarBilin.Nondegenerate)
    {P : Submodule (ZMod 2) V}
    (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P) :
    ∀ n : ℕ, ∀ Z : Submodule (ZMod 2) V, P ≤ Z → finrank (ZMod 2) V = finrank (ZMod 2) Z + n →
      Nat.card (pstab Q Z) ≤ 2 ^ (n.choose 2 + min n 1) := by
  intro n
  induction n with
  | zero =>
    intro Z hPZ hdim
    have hZ : Z = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    subst hZ
    have : Subsingleton (pstab Q ⊤) := by
      refine ⟨fun a b => Subtype.ext (LinearEquiv.ext fun v => ?_)⟩
      rw [a.2.2 v Submodule.mem_top, b.2.2 v Submodule.mem_top]
    have h1 : Nat.card (pstab Q ⊤) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr this
    simpa using h1
  | succ n ih =>
    intro Z hPZ hdim
    set B : LinearMap.BilinForm (ZMod 2) V := Q.polarBilin with hB
    set Zp := LinearMap.BilinForm.orthogonal B Z with hZp
    have hZpdim : finrank (ZMod 2) Zp = n + 1 := by
      have h := LinearMap.BilinForm.finrank_orthogonal hQ Z
      rw [← hZp] at h
      omega
    have hZpP : Zp ≤ P := by
      have := LinearMap.BilinForm.orthogonal_le (B := B) hPZ
      rwa [hP] at this
    have hiso : ∀ y ∈ Zp, ∀ y' ∈ Zp, polar Q y y' = 0 := by
      intro y hy y' hy'
      have hyZ : y ∈ Z := hPZ (hZpP hy)
      have := LinearMap.BilinForm.mem_orthogonal_iff.mp hy' y hyZ
      simpa [hB, polarBilin_apply_apply] using this
    have hcard : ∀ r : V, Nat.card (pstab Q Z) = Nat.card (MulAction.orbit ↥(pstab Q Z) r) *
        Nat.card (pstab Q (Z ⊔ Submodule.span (ZMod 2) {r})) := fun r => by
      rw [← Nat.card_congr (stabEquiv Q Z r), ← Nat.card_prod,
        Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥(pstab Q Z) r)]
    have hsub : ∀ (r : V) (Y : Submodule (ZMod 2) V),
        (∀ y, y ∈ Y ↔ y ∈ Zp ∧ Q y = polar Q r y) → ∀ e ∈ pstab Q Z, e r - r ∈ Y := by
      intro r Y hY e he
      rw [hY]
      refine ⟨?_, ?_⟩
      · rw [hZp, LinearMap.BilinForm.mem_orthogonal_iff]
        intro z hz
        have h := polar_apply_of_isometry he.1 z r
        rw [he.2 z hz] at h
        show B z (e r - r) = 0
        rw [hB, polarBilin_apply_apply, QuadraticMap.polar_sub_right, h, sub_self]
      · have h1 := map_add_eq Q r (e r - r)
        rw [add_sub_cancel, he.1 r] at h1
        have h2 : Q r + (Q (e r - r) + polar Q r (e r - r)) = Q r + 0 := by
          rw [← add_assoc, ← h1, add_zero]
        exact zmod_two_add_eq_zero.mp (add_left_cancel h2)
    have hc2 : (n + 1).choose 2 = n + n.choose 2 := by
      have := Nat.choose_succ_succ' n 1
      rw [Nat.choose_one_right] at this
      exact this
    by_cases hA : ∃ r, r ∉ Z ∧ ∃ y ∈ Zp, Q y ≠ polar Q r y
    · obtain ⟨r, hrZ, y₁, hy₁, hne⟩ := hA
      obtain ⟨Y, hY⟩ := exists_Yr Q hiso r
      have hYlt : Y < Zp := by
        refine lt_of_le_of_ne (fun y hy => ((hY y).mp hy).1) ?_
        intro h
        exact hne (((hY y₁).mp (h ▸ hy₁)).2)
      have hYdim : finrank (ZMod 2) Y ≤ n := by
        have := Submodule.finrank_lt_finrank_of_lt hYlt
        omega
      have horb := card_orbit_le_of_sub_mem (hsub r Y hY)
      have hdim' : finrank (ZMod 2) V =
          finrank (ZMod 2) (Z ⊔ Submodule.span (ZMod 2) {r} : Submodule (ZMod 2) V) + n := by
        rw [Submodule.finrank_sup_span_singleton hrZ]
        omega
      have hst := ih (Z ⊔ Submodule.span (ZMod 2) {r}) (hPZ.trans le_sup_left) hdim'
      rw [hcard r]
      calc _ ≤ 2 ^ n * 2 ^ (n.choose 2 + min n 1) :=
            Nat.mul_le_mul (horb.trans (Nat.pow_le_pow_right (by norm_num) hYdim)) hst
        _ = 2 ^ (n + (n.choose 2 + min n 1)) := (pow_add 2 n _).symm
        _ ≤ 2 ^ ((n + 1).choose 2 + min (n + 1) 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
    · push Not at hA
      have hn : n = 0 := by
        by_contra hn
        have h2 : 1 < finrank (ZMod 2) Zp := by omega
        obtain ⟨x, hx0⟩ :=
          Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank (ZMod 2) Zp)
        obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_finrank h2 hx0
        rw [LinearIndependent.pair_iff] at hxy
        have hy0 : y ≠ 0 := fun h => by
          have := (hxy 0 1 (by rw [h]; simp)).2
          exact one_ne_zero this
        have hxy0 : x + y ≠ 0 := fun h => by
          have := (hxy 1 1 (by rw [one_smul, one_smul]; exact h)).1
          exact one_ne_zero this
        have hQadd : Q ((x + y : Zp) : V) = Q (x : V) + Q (y : V) := by
          rw [Submodule.coe_add, map_add_eq, hiso x x.2 y y.2, add_zero]
        obtain ⟨y₀, hy₀, hy₀0, hy₀Q⟩ : ∃ y₀ ∈ Zp, y₀ ≠ 0 ∧ Q y₀ = 0 := by
          have hx0' : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
          have hy0' : (y : V) ≠ 0 := fun h => hy0 (Subtype.ext h)
          have hxy0' : ((x + y : Zp) : V) ≠ 0 := fun h => hxy0 (Subtype.ext h)
          by_cases hqx : Q (x : V) = 0
          · exact ⟨x, x.2, hx0', hqx⟩
          by_cases hqy : Q (y : V) = 0
          · exact ⟨y, y.2, hy0', hqy⟩
          refine ⟨((x + y : Zp) : V), (x + y : Zp).2, hxy0', ?_⟩
          rw [hQadd]
          revert hqx hqy
          generalize Q (x : V) = a
          generalize Q (y : V) = b
          revert a b
          decide
        obtain ⟨r, hr⟩ : ∃ r, polar Q r y₀ ≠ 0 := by
          by_contra hcon
          push Not at hcon
          refine hy₀0 (hQ.2 y₀ fun r => ?_)
          rw [hB, polarBilin_apply_apply]
          exact hcon r
        have hrZ : r ∉ Z := fun hrZ => hr (by
          have := LinearMap.BilinForm.mem_orthogonal_iff.mp hy₀ r hrZ
          simpa [hB, polarBilin_apply_apply] using this)
        have := hA r hrZ y₀ hy₀
        rw [hy₀Q] at this
        exact hr this.symm
      subst hn
      have hZne : Z ≠ ⊤ := fun h => by
        rw [h, finrank_top] at hdim
        omega
      obtain ⟨r, hrZ⟩ : ∃ r, r ∉ Z := by
        by_contra hall
        push Not at hall
        exact hZne (eq_top_iff.mpr fun v _ => hall v)
      obtain ⟨Y, hY⟩ := exists_Yr Q hiso r
      have hYle : Y ≤ Zp := fun y hy => ((hY y).mp hy).1
      have horb := card_orbit_le_of_sub_mem (hsub r Y hY)
      have hYdim : finrank (ZMod 2) Y ≤ 1 := (Submodule.finrank_mono hYle).trans (by omega)
      have hdim' : finrank (ZMod 2) V =
          finrank (ZMod 2) (Z ⊔ Submodule.span (ZMod 2) {r} : Submodule (ZMod 2) V) + 0 := by
        rw [Submodule.finrank_sup_span_singleton hrZ]
        omega
      have hst := ih (Z ⊔ Submodule.span (ZMod 2) {r}) (hPZ.trans le_sup_left) hdim'
      rw [hcard r]
      refine le_trans
        (Nat.mul_le_mul (horb.trans (Nat.pow_le_pow_right (by norm_num) hYdim)) hst) ?_
      norm_num [Nat.choose]

theorem card_pstab_le_of_orthogonal_eq (Q : QuadraticForm (ZMod 2) V)
    (hQ : Q.polarBilin.Nondegenerate) {P : Submodule (ZMod 2) V}
    (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P) :
    Nat.card (pstab Q P) ≤
      2 ^ ((finrank (ZMod 2) P).choose 2 + min (finrank (ZMod 2) P) 1) := by
  have h := LinearMap.BilinForm.finrank_orthogonal hQ P
  rw [hP] at h
  have h2 := Submodule.finrank_le P
  exact card_pstab_le Q hQ hP (finrank (ZMod 2) P) P le_rfl (by omega)

end Count

end CaseB

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private instance instFiniteDimensionalVtCaseB (g : G) (t : S.O) :
    FiniteDimensional (ZMod 2) (Vt S g t) :=
  Module.Finite.of_finite

theorem finrank_le_width_of_isotropic {W : Submodule (ZMod 2) S.Qt}
    (hW : ∀ a ∈ W, ∀ b ∈ W, polar S.q a b = 0) : finrank (ZMod 2) W ≤ S.width := by
  have hle : W ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin W := fun a ha => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    show S.q.polarBilin b a = 0
    rw [polarBilin_apply_apply]
    exact hW b hb a ha
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
  rw [S.finrank_Qt_eq_two_mul_width] at h2
  omega

namespace S2Data

section Rel

variable {M1 : Subgroup S.O} (D : S2Data S M1)

local notation "ρV" => D.resC

theorem eq_one_of_mem_sup_of_mem_Cbar {e : S.O} (he : e ∈ D.Obar ⊔ zpowers D.t)
    (heC : e ∈ D.Cbar) : e = 1 := by
  rcases D.eq_one_or_eq_t_of_mem_Obar_sup_of_comm he (D.comm_of_mem_Cbar heC) with h | h
  · exact h
  · exact absurd (h ▸ heC) D.t_notMem_Cbar

theorem mem_Obar_cases {s : S.O} (hs : s ∈ D.Obar) :
    s = 1 ∨ s = D.k ∨ s = D.k * D.k := by
  rw [D.Obar_eq_zpowers] at hs
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hs
  have hpow : D.k ^ n = D.k ^ (n % 3) := by simpa using zpow_eq_zpow_emod' n D.k_cube
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
  · exact Or.inl (by rw [hpow, h, zpow_zero])
  · exact Or.inr (Or.inl (by rw [hpow, h, zpow_one]))
  · exact Or.inr (Or.inr (by rw [hpow, h, zpow_two]))

theorem mem_sup_cases {s : S.O} (hs : s ∈ D.Obar ⊔ zpowers D.t) :
    s = 1 ∨ s = D.k ∨ s = D.k * D.k ∨ s = D.t ∨ s = D.k * D.t ∨ s = D.k * D.k * D.t := by
  rcases D.mem_Obar_sup_cases hs with h | h | h | h
  · rcases D.mem_Obar_cases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [h, pow_two])))))

theorem card_Obar_sup_le_six :
    Nat.card ↥(D.Obar ⊔ zpowers D.t) ≤ 6 := by
  classical
  have hsub : ((D.Obar ⊔ zpowers D.t : Subgroup S.O) : Set S.O) ⊆
      (({1, D.k, D.k * D.k, D.t, D.k * D.t, D.k * D.k * D.t} : Finset S.O) : Set S.O) := by
    intro s hs
    rcases D.mem_sup_cases hs with h | h | h | h | h | h <;> simp [h]
  calc Nat.card ↥(D.Obar ⊔ zpowers D.t)
      = Set.ncard ((D.Obar ⊔ zpowers D.t : Subgroup S.O) : Set S.O) :=
        (Nat.card_coe_set_eq _).symm
    _ ≤ Set.ncard (({1, D.k, D.k * D.k, D.t, D.k * D.t, D.k * D.k * D.t} : Finset S.O) :
        Set S.O) := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ({1, D.k, D.k * D.k, D.t, D.k * D.t, D.k * D.k * D.t} : Finset S.O).card :=
        Set.ncard_coe_finset _
    _ ≤ 6 := Finset.card_le_six

theorem exists_eq_mul_of_mul_self_eq_one_of_mem_M1 {x : S.O} (hxM : x ∈ M1)
    (hxx : x * x = 1) :
    ∃ s : S.O, ∃ c : D.Cbar, (s = 1 ∨ D.IsTInv s) ∧ (c : S.O) * c = 1 ∧
      x = s * (c : S.O) := by
  obtain ⟨s, hs, c, hc, rfl⟩ := D.exists_mul_Cbar_of_mem_M1 hxM
  have hsc : s * c = c * s := mem_centralizer_iff.mp hc.2 s hs
  have h2 : (s * s) * (c * c) = 1 := by
    calc (s * s) * (c * c) = s * (s * c) * c := by group
      _ = s * (c * s) * c := by rw [hsc]
      _ = (s * c) * (s * c) := by group
      _ = 1 := hxx
  have hss : s * s = 1 := by
    refine D.eq_one_of_mem_sup_of_mem_Cbar (mul_mem hs hs) ?_
    rw [eq_inv_of_mul_eq_one_left h2]
    exact inv_mem (mul_mem hc hc)
  have hcc : c * c = 1 := by
    rw [hss, one_mul] at h2
    exact h2
  refine ⟨s, ⟨c, hc⟩, ?_, hcc, rfl⟩
  rcases D.mem_Obar_sup_cases hs with h | h | h | h
  · left
    have h3 : s ^ 3 = 1 := S13.pow_three_eq_one D.card_Obar h
    calc s = s ^ 3 * (s * s)⁻¹ := by group
      _ = 1 := by rw [h3, hss, inv_one, mul_one]
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, pow_two])))

theorem resC_resC_apply {c : D.Cbar} (hcc : (c : S.O) * c = 1)
    (w : Vt S D.g D.t) : ρV c (ρV c w) = w := by
  apply Subtype.ext
  rw [D.coe_resC_apply, D.coe_resC_apply, ← coe_mul_apply, hcc]
  rfl

theorem resC_mem_orthogonalGroup (c : D.Cbar) :
    ρV c ∈ TauCeti.QuadraticMap.orthogonalGroup D.QV :=
  D.range_resC_le_orthogonalGroup (fun _ hv => D.QV_eq_zero_iff hv) ⟨c, rfl⟩

theorem eq_one_of_apply_coord {s : S.O} (hs : s ∈ D.Obar ⊔ zpowers D.t)
    {p p' q q' : Vt S D.g D.t} (hp : p ≠ 0) (hq : q ≠ 0)
    (h1 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (p', 0)) = D.coord (p, 0))
    (h2 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (0, q')) = D.coord (0, q)) : s = 1 := by
  rcases D.mem_sup_cases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    simp only [D.k_apply_coord] at h1
    have h3 := Prod.mk.inj (D.coord.injective h1)
    exact hp h3.1.symm
  · exfalso
    simp only [coe_mul_apply, D.k_apply_coord] at h1
    have h3 := Prod.mk.inj (D.coord.injective h1)
    simp only [add_zero, zero_add] at h3
    exact hp (h3.1.symm.trans h3.2)
  · exfalso
    simp only [D.t_apply_coord] at h2
    have h3 := Prod.mk.inj (D.coord.injective h2)
    simp only [zero_add] at h3
    exact hq (h3.2.symm.trans h3.1)
  · exfalso
    simp only [coe_mul_apply, D.t_apply_coord, D.k_apply_coord] at h1
    have h3 := Prod.mk.inj (D.coord.injective h1)
    exact hp h3.1.symm
  · exfalso
    simp only [coe_mul_apply, D.t_apply_coord, D.k_apply_coord] at h1
    have h3 := Prod.mk.inj (D.coord.injective h1)
    simp only [add_zero, zero_add] at h3
    exact hp (h3.1.symm.trans h3.2)

theorem finrank_commSpace_Cbar (c : D.Cbar) :
    finrank (ZMod 2) (commSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      2 * finrank (ZMod 2) (commSpace (ρV c)) := by
  let φ : (commSpace (ρV c) × commSpace (ρV c)) →ₗ[ZMod 2] S.Qt :=
    (D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt).comp
      (LinearMap.prodMap (commSpace (ρV c)).subtype (commSpace (ρV c)).subtype)
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 := D.coord.injective hab
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h1)) (Subtype.ext (congrArg Prod.snd h1))
  have hrange : LinearMap.range φ = commSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact (D.mem_commSpace_Cbar_iff_coord c).mpr ⟨a.1, b.1, a.2, b.2, rfl⟩
    · intro hx
      obtain ⟨u, v, hu, hv, rfl⟩ := (D.mem_commSpace_Cbar_iff_coord c).mp hx
      exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_prod]
  ring

end Rel

section Full

variable (D : S2Data S)

local notation "ρV" => D.resC

end Full

end S2Data

end CFSG.GF2Type.Smith1980Orth

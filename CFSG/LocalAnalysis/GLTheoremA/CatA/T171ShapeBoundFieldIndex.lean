module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenField
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L J A : Subgroup G} {d b : G} {p N n : ℕ}
variable {K : Type} [Field K] [Finite K]

private theorem conj_scalar_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (A : GL ι K) (c : Kˣ) :
    MulAut.conj A (Matrix.GeneralLinearGroup.scalar ι c) =
      Matrix.GeneralLinearGroup.scalar ι c := by
  rw [MulAut.conj_apply]
  exact mul_inv_eq_iff_eq_mul.mpr (TypeA.PGLTor.scalar_mul_comm c A).symm

private theorem scalar_mul_left {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {c X Y : GL ι K} (hc : ∀ T : GL ι K, c * T = T * c) :
    X * (c * Y) = c * (X * Y) := by
  calc X * (c * Y) = (X * c) * Y := by group
    _ = (c * X) * Y := by rw [← hc X]
    _ = c * (X * Y) := by group

private theorem scalar_conj_cancel {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {c X Y Z : GL ι K} (hc : ∀ T : GL ι K, c * T = T * c) :
    (c * X) * Y * (c * X)⁻¹ * Z = X * Y * X⁻¹ * Z := by
  have h1 : (c * X) * Y * (c * X)⁻¹ = X * Y * X⁻¹ := by
    rw [mul_inv_rev, hc X]
    calc (X * c) * Y * (X⁻¹ * c⁻¹)
        = X * (c * Y) * (X⁻¹ * c⁻¹) := by group
      _ = X * (Y * c) * (X⁻¹ * c⁻¹) := by rw [hc Y]
      _ = X * Y * (c * (X⁻¹ * c⁻¹)) := by group
      _ = X * Y * (X⁻¹ * (c * c⁻¹)) := by
          rw [show c * (X⁻¹ * c⁻¹) = X⁻¹ * (c * c⁻¹) from by rw [← mul_assoc, hc X⁻¹]; group]
      _ = X * Y * X⁻¹ := by simp
  rw [h1]

theorem LiftMap.exists_commChar {H : Subgroup (GL (Fin N) K)} {S : Set (GL (Fin N) K)}
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj H}
    {hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) S,
      LargeEvenInduces θ (conjRel a) φ}
    {hS : S ⊆ Subgroup.normalizer (H : Set (GL (Fin N) K))} [Nonempty (Fin N)]
    (M : LiftMap (L := L) (A := A) θ hact hS)
    (hsetup : Setup p L J A d b) {lam : Kˣ}
    (hDp : (M.mat ⟨d, hsetup.d_mem⟩) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) lam)
    (hker : ∀ X : Subgroup.normalizer (H : Set (GL (Fin N) K)),
      TableB.projConj H X = 1 → (X : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K) :
    ∃ χ : ↥A →* Kˣ, (∀ a, χ a ^ p = 1) ∧
      ∀ a : ↥A, M.mat a * M.mat ⟨d, hsetup.d_mem⟩ =
        Matrix.GeneralLinearGroup.scalar (Fin N) (χ a) *
          (M.mat ⟨d, hsetup.d_mem⟩ * M.mat a) := by
  classical
  set D : GL (Fin N) K := M.mat ⟨d, hsetup.d_mem⟩ with hD
  set ρ := TableB.projConj H with hρ
  have hAnorm : A ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S11.le_normalizer_of_innerDiag hsetup.idiag
  let χ₀ : ↥A → Kˣ := fun a =>
    Classical.choose (M.commutator_mem_scalars (L := L) (A := A) hsetup a hker)
  have χ₀_spec : ∀ a : ↥A,
      (Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ a) : GL (Fin N) K) =
        M.mat a * D * (M.mat a)⁻¹ * D⁻¹ := fun a =>
    Classical.choose_spec (M.commutator_mem_scalars (L := L) (A := A) hsetup a hker)
  have hDpD : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) lam := by
    rw [hD]; exact hDp
  have hQ : ∀ a : ↥A, M.mat a * D =
      Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ a) * (D * M.mat a) := by
    intro a
    calc M.mat a * D
        = (M.mat a * D * (M.mat a)⁻¹ * D⁻¹) * (D * M.mat a) := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ a) * (D * M.mat a) := by
          rw [← χ₀_spec a]
  have hρ_prod : ∀ a b : ↥A,
      ρ ⟨M.mat (a * b), hS (M.mem (a * b))⟩ =
        ρ ⟨M.mat a * M.mat b,
          Subgroup.mul_mem _ (hS (M.mem a)) (hS (M.mem b))⟩ := by
    intro a b
    have hcomm : (a : G) * (b : G) = (b : G) * (a : G) :=
      IsElemAbelian.comm hsetup.elem a.2 b.2
    have hprod : LargeEvenInduces θ (conjRel ((a : G) * (b : G)))
        (ρ ⟨M.mat a, hS (M.mem a)⟩ * ρ ⟨M.mat b, hS (M.mem b)⟩) :=
      largeEvenInduces_mul (hAnorm a.2) (hAnorm b.2) hcomm (M.ind a) (M.ind b)
    have hprod' : LargeEvenInduces θ (conjRel ((a * b : ↥A) : G))
        (ρ ⟨M.mat a * M.mat b,
          Subgroup.mul_mem _ (hS (M.mem a)) (hS (M.mem b))⟩) := by
      rw [show (⟨M.mat a * M.mat b,
          Subgroup.mul_mem _ (hS (M.mem a)) (hS (M.mem b))⟩ :
          Subgroup.normalizer (H : Set (GL (Fin N) K))) =
          ⟨M.mat a, hS (M.mem a)⟩ * ⟨M.mat b, hS (M.mem b)⟩ from rfl, map_mul]
      simpa only [Subgroup.coe_mul] using hprod
    exact largeEvenInduces_unique (φ := ρ ⟨M.mat (a * b), hS (M.mem (a * b))⟩)
      (ψ := ρ ⟨M.mat a * M.mat b, Subgroup.mul_mem _ (hS (M.mem a)) (hS (M.mem b))⟩)
      (M.ind (a * b)) hprod'
      (conjRel_total (hAnorm (A.mul_mem a.2 b.2)))
  have hmul : ∀ a b : ↥A, χ₀ (a * b) = χ₀ a * χ₀ b := by
    intro a b
    let X : Subgroup.normalizer (H : Set (GL (Fin N) K)) :=
      ⟨M.mat (a * b) * (M.mat a * M.mat b)⁻¹,
        Subgroup.mul_mem _ (hS (M.mem (a * b)))
          (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hS (M.mem a)) (hS (M.mem b))))⟩
    have hX1 : ρ X = 1 := by
      have hXdef : X = (⟨M.mat (a * b), hS (M.mem (a * b))⟩ :
          Subgroup.normalizer (H : Set (GL (Fin N) K))) *
          (⟨M.mat a * M.mat b,
            Subgroup.mul_mem _ (hS (M.mem a)) (hS (M.mem b))⟩)⁻¹ := rfl
      rw [hXdef, map_mul, map_inv, hρ_prod a b, mul_inv_cancel]
    obtain ⟨s, hs⟩ := hker X hX1
    have hXval : (X : GL (Fin N) K) = M.mat (a * b) * (M.mat a * M.mat b)⁻¹ := rfl
    have hMab : M.mat (a * b) =
        Matrix.GeneralLinearGroup.scalar (Fin N) s * (M.mat a * M.mat b) := by
      rw [hs, hXval]
      group
    have hMb : M.mat b * D * (M.mat b)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ b) * D := by
      rw [hQ b]
      group
    have hmain : (Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ (a * b)) : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ b * χ₀ a) := by
      rw [χ₀_spec (a * b)]
      calc M.mat (a * b) * D * (M.mat (a * b))⁻¹ * D⁻¹
          = (Matrix.GeneralLinearGroup.scalar (Fin N) s * (M.mat a * M.mat b)) * D *
              (Matrix.GeneralLinearGroup.scalar (Fin N) s * (M.mat a * M.mat b))⁻¹ *
                D⁻¹ := by rw [hMab]
        _ = M.mat a * M.mat b * D * (M.mat a * M.mat b)⁻¹ * D⁻¹ := by
            exact scalar_conj_cancel (fun T => TypeA.PGLTor.scalar_mul_comm s T)
        _ = M.mat a * M.mat b * D * (M.mat b)⁻¹ * (M.mat a)⁻¹ * D⁻¹ := by
            rw [mul_inv_rev]
            group
        _ = M.mat a * (M.mat b * D * (M.mat b)⁻¹) * (M.mat a)⁻¹ * D⁻¹ := by group
        _ = M.mat a * (Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ b) * D) *
              (M.mat a)⁻¹ * D⁻¹ := by rw [hMb]
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ b) *
              (M.mat a * D * (M.mat a)⁻¹ * D⁻¹) := by
            rw [scalar_mul_left (fun T => TypeA.PGLTor.scalar_mul_comm (χ₀ b) T)]
            group
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ b) *
              Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ a) := by
            rw [← χ₀_spec a]
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ b * χ₀ a) := (map_mul _ _ _).symm
    have harg : χ₀ (a * b) = χ₀ b * χ₀ a :=
      TypeA.PGLTor.scalar_injective hmain
    rw [harg, mul_comm]
  have hpow : ∀ a : ↥A, χ₀ a ^ p = 1 := by
    intro a
    have hconj : MulAut.conj (M.mat a) D =
        Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ a) * D := by
      rw [MulAut.conj_apply, hQ a]
      group
    have hconjpow : MulAut.conj (M.mat a) (D ^ p) =
        (Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ a) * D) ^ p := by
      rw [map_pow, hconj]
    have hfix : MulAut.conj (M.mat a) (D ^ p) = D ^ p := by
      rw [hDpD]
      exact conj_scalar_eq (M.mat a) lam
    have hscalar : (Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ a) * D) ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin N) ((χ₀ a) ^ p) * D ^ p := by
      rw [(TypeA.PGLTor.commute_scalar (χ₀ a) D).mul_pow, map_pow]
    have heq : D ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin N) ((χ₀ a) ^ p) * D ^ p := by
      calc D ^ p = MulAut.conj (M.mat a) (D ^ p) := hfix.symm
        _ = (Matrix.GeneralLinearGroup.scalar (Fin N) (χ₀ a) * D) ^ p := hconjpow
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) ((χ₀ a) ^ p) * D ^ p := hscalar
    have h1 : (1 : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) ((χ₀ a) ^ p) := by
      have h := congrArg (· * (D ^ p)⁻¹) heq
      simpa [mul_assoc] using h
    have h2 : (1 : Kˣ) = (χ₀ a) ^ p :=
      TypeA.PGLTor.scalar_injective (by simpa using h1)
    exact h2.symm
  exact ⟨MonoidHom.mk' χ₀ hmul, hpow, hQ⟩

theorem exists_index_of_commChar {H : Subgroup (GL (Fin N) K)} {S : Set (GL (Fin N) K)}
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj H}
    {hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) S,
      LargeEvenInduces θ (conjRel a) φ}
    {hS : S ⊆ Subgroup.normalizer (H : Set (GL (Fin N) K))} [Nonempty (Fin N)]
    (M : LiftMap (L := L) (A := A) θ hact hS)
    (hsetup : Setup p L J A d b) (hp : p.Prime) (χ : ↥A →* Kˣ)
    (hQ : ∀ a : ↥A, M.mat a * M.mat ⟨d, hsetup.d_mem⟩ =
      Matrix.GeneralLinearGroup.scalar (Fin N) (χ a) *
        (M.mat ⟨d, hsetup.d_mem⟩ * M.mat a))
    (hχp : ∀ a, χ a ^ p = 1) :
    ∃ A₀ : Subgroup G, ∃ hA₀A : A₀ ≤ A, Nat.card A ≤ p * Nat.card A₀ ∧
      ∀ a (ha : a ∈ A₀), M.mat ⟨a, hA₀A ha⟩ * M.mat ⟨d, hsetup.d_mem⟩ =
        M.mat ⟨d, hsetup.d_mem⟩ * M.mat ⟨a, hA₀A ha⟩ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let χk : Subgroup ↥A := χ.ker
  let A₀ : Subgroup G := χk.map A.subtype
  have hA₀A : A₀ ≤ A := Subgroup.map_subtype_le χk
  have hcardA₀ : Nat.card A₀ = Nat.card χk := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
  have hcard : Nat.card χk * Nat.card χ.range = Nat.card ↥A :=
    Subgroup.card_ker_mul_card_range χ
  have hrange : Nat.card χ.range ≤ p := by
    have hmem : ∀ y : χ.range, (y : Kˣ) ^ p = 1 := by
      rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := hy
      exact hχp a
    have hinj : Function.Injective
        (fun y : χ.range => (⟨(y : Kˣ), hmem y⟩ : {z : Kˣ // z ^ p = 1})) := by
      intro y z hyz
      exact Subtype.ext (congrArg (fun w : {z : Kˣ // z ^ p = 1} => (w : Kˣ)) hyz)
    have h1 : Nat.card χ.range ≤ Nat.card {z : Kˣ // z ^ p = 1} :=
      Nat.card_le_card_of_injective _ hinj
    have h2 : Nat.card {z : Kˣ // z ^ p = 1} ≤ p := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact IsCyclic.card_pow_eq_one_le hp.pos
    exact le_trans h1 h2
  refine ⟨A₀, hA₀A, ?_, ?_⟩
  · rw [hcardA₀]
    calc Nat.card ↥A = Nat.card χk * Nat.card χ.range := hcard.symm
      _ ≤ Nat.card χk * p := Nat.mul_le_mul_left _ hrange
      _ = p * Nat.card χk := mul_comm _ _
  · intro a ha
    rw [show A₀ = χk.map A.subtype from rfl, Subgroup.mem_map] at ha
    obtain ⟨k, hk, hka⟩ := ha
    have hχk : χ k = 1 := MonoidHom.mem_ker.mp hk
    have hsub : (⟨a, hA₀A ha⟩ : ↥A) = k := Subtype.ext hka.symm
    have h := hQ ⟨a, hA₀A ha⟩
    rw [hsub, hχk, map_one, one_mul] at h
    simpa only [hsub] using h

theorem linFieldTypeIndex_of_three_le {θ : ↥L ⧸ Subgroup.center ↥L ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin N) K)}
    {hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) (Set.univ : Set (GL (Fin N) K)),
      LargeEvenInduces θ (conjRel a) φ}
    {hS : (Set.univ : Set (GL (Fin N) K)) ⊆ Subgroup.normalizer
      (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))} [Nonempty (Fin N)] (hN : 3 ≤ N)
    (M : LiftMap (L := L) (A := A) (S := (Set.univ : Set (GL (Fin N) K))) θ hact hS)
    (hsetup : Setup p L J A d b) {lam : Kˣ}
    (hDp : (M.mat ⟨d, hsetup.d_mem⟩) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) lam) :
    ∃ A₀ : Subgroup G, ∃ hA₀A : A₀ ≤ A, Nat.card A ≤ p * Nat.card A₀ ∧
      ∀ a (ha : a ∈ A₀), M.mat ⟨a, hA₀A ha⟩ * M.mat ⟨d, hsetup.d_mem⟩ =
        M.mat ⟨d, hsetup.d_mem⟩ * M.mat ⟨a, hA₀A ha⟩ := by
  obtain ⟨χ, hχp, hQ⟩ := M.exists_commChar (L := L) (A := A) hsetup hDp
    (fun X hX => linKernelScalar_of_three_le hN X hX)
  exact exists_index_of_commChar M hsetup hsetup.prime χ hQ hχp

theorem uniFieldTypeIndex_of_side (h : UnitaryFieldData 2 n K)
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n K N)}
    {hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 n K N)) (LargeEvenGUSet (Fin N) K (2 ^ n)),
      LargeEvenInduces θ (conjRel a) φ}
    {hS : LargeEvenGUSet (Fin N) K (2 ^ n) ⊆ Subgroup.normalizer
      (unitarySU 2 n K N : Set (GL (Fin N) K))} [Nonempty (Fin N)]
    (hN : 3 ≤ N) (hNq : (N, 2 ^ n) ≠ (3, 2)) (hpq : p ∣ 2 ^ n + 1)
    (M : LiftMap (L := L) (A := A) (S := LargeEvenGUSet (Fin N) K (2 ^ n)) θ hact hS)
    (hsetup : Setup p L J A d b) {lam : Kˣ}
    (hDp : (M.mat ⟨d, hsetup.d_mem⟩) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) lam) :
    ∃ A₀ : Subgroup G, ∃ hA₀A : A₀ ≤ A, Nat.card A ≤ p * Nat.card A₀ ∧
      ∀ a (ha : a ∈ A₀), M.mat ⟨a, hA₀A ha⟩ * M.mat ⟨d, hsetup.d_mem⟩ =
        M.mat ⟨d, hsetup.d_mem⟩ * M.mat ⟨a, hA₀A ha⟩ := by
  obtain ⟨χ, hχp, hQ⟩ := M.exists_commChar (L := L) (A := A) hsetup hDp
    (fun X hX => uniKernelScalar h hN hNq hsetup.prime hpq X hX)
  exact exists_index_of_commChar M hsetup hsetup.prime χ hQ hχp

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

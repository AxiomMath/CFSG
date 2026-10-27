module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreTor

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open scoped commutatorElement
open Equiv

@[expose] def PermBound (r m : ℕ) : Prop :=
  ∀ B : Subgroup (Perm (Fin m)), (∀ b ∈ B, b ^ r = 1) → (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) →
    Nat.card B * Nat.card {u : Fin m → ZMod r //
      ∑ i, u i = 0 ∧ ∀ b ∈ B, ∃ c : ZMod r, ∀ i, u (b⁻¹ i) - u i = c} ≤ r ^ (m - 1)

section Basic

variable {C : Type} [CommGroup C] {m : ℕ}

theorem monT_inv (t : Fin m → C) : monT t⁻¹ = (monT t)⁻¹ :=
  map_inv (SemidirectProduct.inl : (Fin m → C) →* Mon C m) t

theorem monT_injective : Function.Injective (monT : (Fin m → C) → Mon C m) :=
  SemidirectProduct.inl_injective

theorem monT_comm (s t : Fin m → C) : monT s * monT t = monT t * monT s := by
  rw [← monT_mul, ← monT_mul, mul_comm]

theorem mon_conj_monT (x : Mon C m) (t : Fin m → C) :
    x * monT t * x⁻¹ = monT (t ∘ x.right.symm) := by
  have hx := mon_eq_monT_mul_monS x
  have hA : ∀ s : Fin m → C, monT x.left * monT s * (monT x.left)⁻¹ = monT s := by
    intro s
    rw [mul_inv_eq_iff_eq_mul, monT_comm]
  calc x * monT t * x⁻¹
      = (monT x.left * monS x.right) * monT t * (monT x.left * monS x.right)⁻¹ := by
        rw [← hx]
    _ = monT x.left * (monS x.right * monT t * (monS x.right)⁻¹) * (monT x.left)⁻¹ := by
        group
    _ = monT (t ∘ x.right.symm) := by
        rw [monS_mul_monT_mul_monS_inv, hA]

theorem mon_comm_monT (x : Mon C m) (t : Fin m → C) :
    ⁅x, monT t⁆ = monT ((t ∘ x.right.symm) * t⁻¹) := by
  rw [commutatorElement_def, mon_conj_monT, ← monT_inv, ← monT_mul]

theorem eq_monT_of_right_eq_one {x : Mon C m} (h : x.right = 1) : x = monT x.left :=
  SemidirectProduct.ext rfl h

theorem monPerm_monScalar (z : C) : monPerm (monScalar C m z) = 1 := monPerm_monT _

end Basic

section Main

variable {r m : ℕ} [hr : Fact r.Prime] {C : Type} [CommGroup C] [Finite C]

theorem card_pow_ker_eq [Nontrivial C] [IsCyclic C] (hCr : IsPGroup r C) :
    Nat.card (powMonoidHom r : C →* C).ker = r := by
  refine le_antisymm (card_pow_ker_le hr.out.pos) (le_card_pow_ker ?_)
  obtain ⟨n, hn, hnc⟩ := hCr.nontrivial_iff_card.1 inferInstance
  exact hnc ▸ dvd_pow_self r hn.ne'

noncomputable def torsionEquiv [Nontrivial C] [IsCyclic C] (hCr : IsPGroup r C) :
    (powMonoidHom r : C →* C).ker ≃* Multiplicative (ZMod r) :=
  mulEquivOfPrimeCardEq (p := r) (card_pow_ker_eq hCr) (by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod r) ≃ ZMod r), Nat.card_zmod])

noncomputable def torsionLog [Nontrivial C] [IsCyclic C] (hCr : IsPGroup r C) :
    (powMonoidHom r : C →* C).ker → ZMod r :=
  fun y => Multiplicative.toAdd (torsionEquiv hCr y)

theorem torsionLog_mul [Nontrivial C] [IsCyclic C] (hCr : IsPGroup r C)
    (y y' : ↥(powMonoidHom r : C →* C).ker) :
    torsionLog hCr (y * y') = torsionLog hCr y + torsionLog hCr y' := by
  simp [torsionLog]

theorem torsionLog_injective [Nontrivial C] [IsCyclic C] (hCr : IsPGroup r C) :
    Function.Injective (torsionLog hCr : ↥(powMonoidHom r : C →* C).ker → ZMod r) := by
  intro y y' h
  exact (torsionEquiv hCr).injective (Multiplicative.toAdd.injective h)

theorem torsionLog_prod [Nontrivial C] [IsCyclic C] (hCr : IsPGroup r C) {ι : Type} [Fintype ι]
    (y : ι → ↥(powMonoidHom r : C →* C).ker) :
    torsionLog hCr (∏ i, y i) = ∑ i, torsionLog hCr (y i) := by
  simp [torsionLog, map_prod]

theorem monCore_of_perm (hperm : PermBound r m) (hm : 4 ≤ m) [Nontrivial C] (hCc : IsCyclic C)
    (hCr : IsPGroup r C) (C₀ : Subgroup C) (P : Subgroup (Mon C m))
    (hdet : ∀ x ∈ P, monDet x = 1) (hpow : ∀ x ∈ P, x ^ r ∈ C₀.map (monScalar C m))
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ C₀.map (monScalar C m)) :
    Nat.card P ≤ r ^ (m - 1) * Nat.card ↥(C₀ ⊓ Ωsc r m C) := by
  classical
  have hm0 : 0 < m := by omega
  let i0 : Fin m := ⟨0, hm0⟩
  let π' : P →* Perm (Fin m) := monPerm.comp P.subtype
  have hcardP := Subgroup.card_ker_mul_card_range π'
  have hBmem : ∀ b ∈ π'.range, ∃ x : Mon C m, x ∈ P ∧ x.right = b := by
    intro b hb
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hb
    exact ⟨x, x.2, hx⟩
  have hBp : ∀ b ∈ π'.range, b ^ r = 1 := by
    intro b hb
    obtain ⟨x, hxP, rfl⟩ := hBmem b hb
    obtain ⟨z, -, hz⟩ := Subgroup.mem_map.1 (hpow x hxP)
    have h1 : monPerm (x ^ r) = 1 := by rw [← hz]; exact monPerm_monScalar z
    rwa [map_pow] at h1
  have hBc : ∀ b ∈ π'.range, ∀ b' ∈ π'.range, b * b' = b' * b := by
    intro b hb b' hb'
    obtain ⟨x, hxP, rfl⟩ := hBmem b hb
    obtain ⟨y, hyP, rfl⟩ := hBmem b' hb'
    obtain ⟨z, -, hz⟩ := Subgroup.mem_map.1 (hcomm x hxP y hyP)
    have h1 : monPerm ⁅x, y⁆ = 1 := by rw [← hz]; exact monPerm_monScalar z
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hker_right : ∀ x : π'.ker, ((x : P) : Mon C m).right = 1 := fun x => MonoidHom.mem_ker.1 x.2
  have hker_eq : ∀ x : π'.ker, ((x : P) : Mon C m) = monT (((x : P) : Mon C m).left) :=
    fun x => eq_monT_of_right_eq_one (hker_right x)
  have hpowK : ∀ x : π'.ker, ∃ z ∈ C₀, ∀ i, (((x : P) : Mon C m).left i) ^ r = z := by
    intro x
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 (hpow _ (x : P).2)
    refine ⟨z, hz, fun i => ?_⟩
    have h1 : monT (fun _ : Fin m => z) = monT ((((x : P) : Mon C m).left) ^ r) := by
      have : ((x : P) : Mon C m) ^ r = monT ((((x : P) : Mon C m).left) ^ r) := by
        conv_lhs => rw [hker_eq x]
        exact (map_pow (SemidirectProduct.inl : (Fin m → C) →* Mon C m) _ r).symm
      rw [← this, ← hzx]
      rfl
    exact (congrFun (monT_injective h1) i).symm
  have hdetK : ∀ x : π'.ker, ∏ i, ((x : P) : Mon C m).left i = 1 := by
    intro x
    have := hdet _ (x : P).2
    rwa [hker_eq x, monDet_monT] at this
  have hcommK : ∀ y ∈ P, ∀ x : π'.ker, ∃ z ∈ C₀, ∀ i,
      ((x : P) : Mon C m).left (y.right.symm i) * (((x : P) : Mon C m).left i)⁻¹ = z := by
    intro y hy x
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 (hcomm y hy _ (x : P).2)
    refine ⟨z, hz, fun i => ?_⟩
    have h1 : monT (fun _ : Fin m => z) =
        monT ((((x : P) : Mon C m).left ∘ y.right.symm) * (((x : P) : Mon C m).left)⁻¹) := by
      rw [← mon_comm_monT, ← hker_eq x]
      exact hzx
    exact (congrFun (monT_injective h1) i).symm
  let ψ : π'.ker →* C := MonoidHom.mk' (fun x => (((x : P) : Mon C m).left i0) ^ r) (by
    intro x y
    have hx := hker_right x
    have hmul : ((((x * y : π'.ker) : P) : Mon C m)).left =
        ((x : P) : Mon C m).left * ((y : P) : Mon C m).left := by
      change (((x : P) : Mon C m) * ((y : P) : Mon C m)).left = _
      rw [SemidirectProduct.mul_left, hx]
      simp
    rw [hmul, Pi.mul_apply, mul_pow])
  have hψ : ∀ x : π'.ker, ψ x = (((x : P) : Mon C m).left i0) ^ r := fun x => rfl
  have hrange : ψ.range ≤ C₀ ⊓ Ωsc r m C := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hpowK x
    rw [hψ, hzx i0]
    exact ⟨hz, ((x : P) : Mon C m).left, hdetK x, hzx⟩
  have hker_mem : ∀ x : ψ.ker, ∀ i,
      ((((x : π'.ker) : P) : Mon C m).left i) ∈ (powMonoidHom r : C →* C).ker := by
    intro x i
    obtain ⟨z, hz, hzx⟩ := hpowK (x : π'.ker)
    have h2 : ψ (x : π'.ker) = 1 := MonoidHom.mem_ker.1 x.2
    have h1 : z = 1 := by
      rw [hψ, hzx i0] at h2
      exact h2
    rw [MonoidHom.mem_ker, powMonoidHom_apply, hzx i, h1]
  haveI : NeZero r := ⟨hr.out.ne_zero⟩
  let uOf : ψ.ker → (Fin m → ZMod r) := fun x i =>
    torsionLog hCr ⟨(((x : π'.ker) : P) : Mon C m).left i, hker_mem x i⟩
  have huU : ∀ x : ψ.ker, ∑ i, uOf x i = 0 ∧ ∀ b ∈ π'.range,
      ∃ c : ZMod r, ∀ i, uOf x (b⁻¹ i) - uOf x i = c := by
    intro x
    refine ⟨?_, ?_⟩
    · have h1 : ∏ i, (⟨(((x : π'.ker) : P) : Mon C m).left i, hker_mem x i⟩ :
          (powMonoidHom r : C →* C).ker) = 1 := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_finset_prod, Subgroup.coe_one]
        exact hdetK _
      have h2 := torsionLog_prod hCr (fun i => (⟨(((x : π'.ker) : P) : Mon C m).left i,
        hker_mem x i⟩ : (powMonoidHom r : C →* C).ker))
      rw [h1] at h2
      have h0 : torsionLog hCr (1 : (powMonoidHom r : C →* C).ker) = 0 := by simp [torsionLog]
      rw [h0] at h2
      exact h2.symm
    · intro b hb
      obtain ⟨y, hyP, rfl⟩ := hBmem b hb
      obtain ⟨z, hz, hzi⟩ := hcommK y hyP (x : π'.ker)
      have hzCk : z ∈ (powMonoidHom r : C →* C).ker := by
        rw [← hzi i0]
        exact Subgroup.mul_mem _ (hker_mem x _) (Subgroup.inv_mem _ (hker_mem x i0))
      refine ⟨torsionLog hCr ⟨z, hzCk⟩, fun i => ?_⟩
      have h1 : (⟨(((x : π'.ker) : P) : Mon C m).left (y.right.symm i), hker_mem x _⟩ :
          (powMonoidHom r : C →* C).ker) =
          ⟨z, hzCk⟩ * ⟨(((x : π'.ker) : P) : Mon C m).left i, hker_mem x i⟩ := by
        apply Subtype.ext
        change _ = z * _
        rw [← hzi i]
        simp
      have h2 := congrArg (torsionLog hCr) h1
      rw [torsionLog_mul] at h2
      change torsionLog hCr ⟨(((x : π'.ker) : P) : Mon C m).left (y.right.symm i), hker_mem x _⟩ -
        torsionLog hCr _ = _
      rw [h2]
      ring
  have hinj : Function.Injective uOf := by
    intro x x' h
    have h1 : ∀ i, (((x : π'.ker) : P) : Mon C m).left i =
        (((x' : π'.ker) : P) : Mon C m).left i := fun i => by
      have := torsionLog_injective hCr (congrFun h i)
      exact congrArg Subtype.val this
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rw [hker_eq (x : π'.ker), hker_eq (x' : π'.ker)]
    congr 1
    funext i
    exact h1 i
  have hkerle : Nat.card ψ.ker ≤ Nat.card {u : Fin m → ZMod r //
      ∑ i, u i = 0 ∧ ∀ b ∈ π'.range, ∃ c : ZMod r, ∀ i, u (b⁻¹ i) - u i = c} := by
    let g : ψ.ker → {u : Fin m → ZMod r //
      ∑ i, u i = 0 ∧ ∀ b ∈ π'.range, ∃ c : ZMod r, ∀ i, u (b⁻¹ i) - u i = c} :=
      fun x => ⟨uOf x, huU x⟩
    have hg : Function.Injective g := by
      intro x x' h
      exact hinj (congrArg Subtype.val h)
    exact Nat.card_le_card_of_injective g hg
  have hKcard := Subgroup.card_ker_mul_card_range ψ
  have hrange_card : Nat.card ψ.range ≤ Nat.card ↥(C₀ ⊓ Ωsc r m C) :=
    Subgroup.card_le_of_le hrange
  have hperm' := hperm π'.range hBp hBc
  calc Nat.card P = Nat.card π'.ker * Nat.card π'.range := hcardP.symm
    _ = (Nat.card ψ.ker * Nat.card ψ.range) * Nat.card π'.range := by rw [hKcard]
    _ ≤ (Nat.card {u : Fin m → ZMod r //
          ∑ i, u i = 0 ∧ ∀ b ∈ π'.range, ∃ c : ZMod r, ∀ i, u (b⁻¹ i) - u i = c} *
        Nat.card ↥(C₀ ⊓ Ωsc r m C)) * Nat.card π'.range :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hkerle hrange_card)
    _ = (Nat.card π'.range * Nat.card {u : Fin m → ZMod r //
          ∑ i, u i = 0 ∧ ∀ b ∈ π'.range, ∃ c : ZMod r, ∀ i, u (b⁻¹ i) - u i = c}) *
        Nat.card ↥(C₀ ⊓ Ωsc r m C) := by ring
    _ ≤ r ^ (m - 1) * Nat.card ↥(C₀ ⊓ Ωsc r m C) := Nat.mul_le_mul_right _ hperm'

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore

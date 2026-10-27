module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUniqueFinal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Monster.B.TwoA.Amalgam

section Generic

variable {G : Type*} [Group G]

theorem mul_self_mem_range_conj_of_index_le_two {A : Type*} [Group A] [Finite (MulAut A)]
    (hO : (MulAut.conj : A →* MulAut A).range.index ≤ 2) (σ : MulAut A) :
    σ * σ ∈ (MulAut.conj : A →* MulAut A).range := by
  have h0 : (MulAut.conj : A →* MulAut A).range.index ≠ 0 := FiniteIndex.index_ne_zero
  rcases (show (MulAut.conj : A →* MulAut A).range.index = 1 ∨
      (MulAut.conj : A →* MulAut A).range.index = 2 by omega) with h | h
  · rw [index_eq_one] at h
    rw [h]
    exact mem_top _
  · exact mul_self_mem_of_index_two h σ

theorem mul_self_mem_range_conj_of_mulEquiv {A B : Type*} [Group A] [Group B]
    [Finite (MulAut B)] (hO : (MulAut.conj : B →* MulAut B).range.index ≤ 2) (ι : A ≃* B)
    (σ : MulAut A) : σ * σ ∈ (MulAut.conj : A →* MulAut A).range := by
  rw [← congr_mem_range_conj_iff ι, map_mul]
  exact mul_self_mem_range_conj_of_index_le_two hO _

theorem exists_conj_eq_of_odd {L : Subgroup G}
    (hsq : ∀ σ : MulAut L, σ * σ ∈ (MulAut.conj : L →* MulAut L).range) {x : G}
    (hx : x ∈ normalizer (L : Set G)) (hodd : Odd (orderOf x)) :
    ∃ l ∈ L, ∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹ := by
  set τ := L.normalizerMonoidHom ⟨x, hx⟩ with hτ
  obtain ⟨j, hj⟩ := hodd
  have hτm : τ ^ (2 * j + 1) = 1 := by
    rw [hτ, ← map_pow, ← hj]
    convert map_one L.normalizerMonoidHom
    exact Subtype.ext (by rw [coe_pow, pow_orderOf_eq_one, coe_one])
  have hτmem : τ ∈ (MulAut.conj : L →* MulAut L).range := by
    have e : τ = (τ * τ) ^ (j + 1) := by
      rw [← sq, ← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, hτm, one_mul]
    rw [e]
    exact pow_mem (hsq τ) _
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.1 hτmem
  refine ⟨l, l.2, fun y hy => ?_⟩
  have h := congrArg (fun f : MulAut L => ((f ⟨y, hy⟩ : L) : G)) hl
  simp only [MulAut.conj_apply, coe_mul, coe_inv] at h
  rw [h]
  rfl

theorem exists_conj_eq_sq {L : Subgroup G}
    (hsq : ∀ σ : MulAut L, σ * σ ∈ (MulAut.conj : L →* MulAut L).range) {x : G}
    (hx : x ∈ normalizer (L : Set G)) :
    ∃ l ∈ L, ∀ y ∈ L, x * x * y * (x * x)⁻¹ = l * y * l⁻¹ := by
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.1 (hsq (L.normalizerMonoidHom ⟨x, hx⟩))
  refine ⟨l, l.2, fun y hy => ?_⟩
  rw [← map_mul] at hl
  have h := congrArg (fun f : MulAut L => ((f ⟨y, hy⟩ : L) : G)) hl
  simp only [MulAut.conj_apply, coe_mul, coe_inv] at h
  rw [h]
  rfl

theorem inv_mul_mem_centralizer {L : Subgroup G} {x l : G}
    (h : ∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹) : l⁻¹ * x ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  calc y * (l⁻¹ * x) = l⁻¹ * (l * y * l⁻¹) * x := by group
    _ = l⁻¹ * (x * y * x⁻¹) * x := by rw [h y hy]
    _ = l⁻¹ * x * y := by group

theorem mul_self_mem_sup_centralizer {L : Subgroup G}
    (hsq : ∀ σ : MulAut L, σ * σ ∈ (MulAut.conj : L →* MulAut L).range) {x : G}
    (hx : x ∈ normalizer (L : Set G)) : x * x ∈ L ⊔ centralizer (L : Set G) := by
  obtain ⟨l, hlL, hl⟩ := exists_conj_eq_sq hsq hx
  have e : x * x = l * (l⁻¹ * (x * x)) := by group
  rw [e]
  exact mul_mem_sup hlL (inv_mul_mem_centralizer hl)

theorem mem_of_odd_orderOf {L : Subgroup G}
    (hsq : ∀ σ : MulAut L, σ * σ ∈ (MulAut.conj : L →* MulAut L).range)
    (hK : IsPGroup 2 (centralizer (L : Set G))) {x : G} (hx : x ∈ normalizer (L : Set G))
    (hodd : Odd (orderOf x)) : x ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hlL, hl⟩ := exists_conj_eq_of_odd hsq hx hodd
  set k := l⁻¹ * x with hkdef
  have hkC : k ∈ centralizer (L : Set G) := inv_mul_mem_centralizer hl
  have hxk : x = l * k := by rw [hkdef]; group
  have hlk : Commute l k := ((mem_centralizer_iff.1 hkC) l hlL)
  have hkm : k ^ orderOf x ∈ L := by
    have h1 : (l * k) ^ orderOf x = 1 := by rw [← hxk, pow_orderOf_eq_one]
    rw [hlk.mul_pow] at h1
    have h2 : k ^ orderOf x = (l ^ orderOf x)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_mem (pow_mem hlL _)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.1 hK) ⟨k, hkC⟩
  rw [Subgroup.orderOf_mk] at ha
  have hcop : (orderOf x).Coprime (orderOf k) := by
    rw [ha]
    exact Nat.Coprime.pow_right a
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd.not_two_dvd_nat))
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
  have hkL : k ∈ L := hn ▸ pow_mem hkm n
  rw [hxk]
  exact mul_mem hlL hkL

theorem mul_self_ne_of_mem_closure_odd {L : Subgroup G} {d : G} (hdL : ∀ s ∈ L, s * s ≠ d)
    (hodd : ∀ x : G, x * d = d * x → Odd (orderOf x) → x ∈ L) (g : G) {s : G}
    (hs : s ∈ closure {h : G | h * (g * d * g⁻¹) = g * d * g⁻¹ * h ∧ Odd (orderOf h)}) :
    s * s ≠ g * d * g⁻¹ := by
  set f : G →* G := (MulAut.conj g⁻¹).toMonoidHom with hf
  have hfx : ∀ x, f x = g⁻¹ * x * g := fun x => by
    rw [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hle : closure {h : G | h * (g * d * g⁻¹) = g * d * g⁻¹ * h ∧ Odd (orderOf h)} ≤
      L.comap f := by
    rw [closure_le]
    rintro h ⟨hc, ho⟩
    rw [SetLike.mem_coe, mem_comap, hfx]
    refine hodd _ ?_ ?_
    · calc g⁻¹ * h * g * d = g⁻¹ * (h * (g * d * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * d * g⁻¹ * h) * g := by rw [hc]
        _ = d * (g⁻¹ * h * g) := by group
    · rw [← hfx, hf, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      exact ho
  intro hss
  have hfs : f s ∈ L := hle hs
  apply hdL _ hfs
  rw [← map_mul, hss, hfx]
  group

theorem commute_of_odd_of_mem_cyclic [Finite G] {C : Subgroup G} (hC : IsCyclic C) {w h : G}
    (hw : w ∈ C) (hw4 : orderOf w = 4) (hh : h * w * h⁻¹ ∈ C) (hodd : Odd (orderOf h)) :
    h * w = w * h := by
  have hx4 : orderOf (h * w * h⁻¹) = 4 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hw4]
  rcases CFSG.ComponentClassification.M12Cover.CyclicKernel.eq_or_eq_inv_of_orderOf_eq_four hC hw hh
      hw4 hx4 with e | e
  · calc h * w = h * w * h⁻¹ * h := by group
      _ = w * h := by rw [e]
  · exfalso
    set α := MulAut.conj h with hα
    have hαw : α w = w⁻¹ := by rw [hα, MulAut.conj_apply, e]
    have hαw' : α w⁻¹ = w := by rw [map_inv, hαw, inv_inv]
    have heven : ∀ i : ℕ, (α ^ (2 * i)) w = w := by
      intro i
      induction i with
      | zero => rw [mul_zero, pow_zero, MulAut.one_apply]
      | succ i ih =>
        rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, pow_succ, pow_succ, MulAut.mul_apply,
          MulAut.mul_apply, hαw, hαw', ih]
    obtain ⟨j, hj⟩ := hodd
    have hαm : α ^ (2 * j + 1) = 1 := by
      rw [hα, ← map_pow, ← hj, pow_orderOf_eq_one, map_one]
    have h1 : (α ^ (2 * j + 1)) w = w⁻¹ := by
      rw [pow_succ', MulAut.mul_apply, heven, hαw]
    rw [hαm, MulAut.one_apply] at h1
    have h2 : w ^ 2 = 1 := by
      rw [sq]
      calc w * w = w⁻¹ * w := by rw [← h1]
        _ = 1 := inv_mul_cancel w
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hw4] at h3
    exact absurd h3 (by decide)

end Generic

section Eam

variable {G : Type*} [Group G]

theorem mul_self_mem_range_conj_of_iota
    {L : Type*} [Group L] (ι : L ≃* commutator Eam)
    (σ : MulAut L) : σ * σ ∈ (MulAut.conj : L →* MulAut L).range := by
  have : Finite (MulAut (commutator Eam)) := inferInstance
  exact mul_self_mem_range_conj_of_mulEquiv coverOuterLeTwo ι σ

end Eam

end CFSG.EvenSmallLie.TwoE6

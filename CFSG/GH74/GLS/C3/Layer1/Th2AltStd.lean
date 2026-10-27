module

public import CFSG.GH74.GLS.C3.Layer1.BkIvk73Fin
public import CFSG.GH74.GLS.C3.Layer1.Th2AltInv

public section

namespace CFSG.GH74.GLS.Th2.AltStd

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer1.Bk

theorem fixes_support_of_perfect {m : ℕ} (K' : Subgroup (alternatingGroup (Fin m)))
    [Group.IsPerfect ↥K'] (u : Perm (Fin m)) (hc : u.support.card ≤ 4)
    (hKu : ∀ k ∈ K', (k : Perm (Fin m)) * u = u * (k : Perm (Fin m))) :
    ∀ k ∈ K', ∀ p ∈ u.support, (k : Perm (Fin m)) p = p := by
  classical
  have hinv : ∀ k : ↥K', ∀ p : Fin m,
      ((k.1 : Perm (Fin m)) p) ∈ u.support ↔ p ∈ u.support := by
    intro k p
    have hk := hKu k.1 k.2
    have h1 : u (((k.1 : alternatingGroup (Fin m)) : Perm (Fin m)) p) =
        ((k.1 : alternatingGroup (Fin m)) : Perm (Fin m)) (u p) := by
      have := congrArg (fun f : Perm (Fin m) => f p) hk
      simpa [Perm.mul_apply] using this.symm
    rw [Equiv.Perm.mem_support, Equiv.Perm.mem_support, h1]
    exact not_congr ((k.1 : alternatingGroup (Fin m)) : Perm (Fin m)).injective.eq_iff
  let φ : ↥K' →* Perm {p // p ∈ u.support} :=
    { toFun := fun k => (k.1 : Perm (Fin m)).subtypePerm (hinv k)
      map_one' := Equiv.ext fun p => Subtype.ext rfl
      map_mul' := fun k l => Equiv.ext fun p => Subtype.ext rfl }
  have hsolv : Group.IsSolvable (Perm {p // p ∈ u.support}) := by
    apply Equiv.Perm.isSolvable
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hc
  have hperf : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hbot : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial φ.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  intro k hk p hp
  have h1 : φ ⟨k, hk⟩ = 1 := by
    have : φ ⟨k, hk⟩ ∈ φ.range := ⟨⟨k, hk⟩, rfl⟩
    rw [hbot] at this
    exact this
  have h2 := congrArg (fun f : Perm {p // p ∈ u.support} => (f ⟨p, hp⟩ : Fin m)) h1
  simpa [φ] using h2

theorem exists_conj_stdAlt_of_perfect {n : ℕ} (hn : 5 ≤ n)
    (K' : Subgroup (alternatingGroup (Fin (n + 4)))) [Group.IsPerfect ↥K']
    (hcard : Nat.card (alternatingGroup (Fin n)) ≤ Nat.card ↥K')
    {u : alternatingGroup (Fin (n + 4))} (hu4 : numMoved (u : Perm (Fin (n + 4))) = 4)
    (hKu : ∀ k ∈ K', k * u = u * k) :
    ∃ σ : Perm (Fin (n + 4)), K'.map (conjA σ).toMonoidHom = stdAlt n := by
  classical
  set u₀ : Perm (Fin (n + 4)) := (u : Perm (Fin (n + 4))) with hu₀
  have h4 : u₀.support.card = 4 := hu4
  have hKu' : ∀ k ∈ K', (k : Perm (Fin (n + 4))) * u₀ = u₀ * (k : Perm (Fin (n + 4))) := fun k hk => by
    have := congrArg (fun a : alternatingGroup (Fin (n + 4)) => (a : Perm (Fin (n + 4)))) (hKu k hk)
    simpa using this
  have hfix := fixes_support_of_perfect K' u₀ h4.le hKu'
  have hcF : Fintype.card {p // p ∈ u₀.support} = Fintype.card {p : Fin (n + 4) // n ≤ p.val} := by
    rw [Fintype.card_coe, h4, card_subtype_ge]
  let e₀ : {p // p ∈ u₀.support} ≃ {p : Fin (n + 4) // n ≤ p.val} := Fintype.equivOfCardEq hcF
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (fun a : {p // p ∈ u₀.support} => a.1)
    (fun a => (e₀ a).1) Subtype.val_injective (fun a b h => e₀.injective (Subtype.ext h))
  refine ⟨σ, ?_⟩
  have hle : K'.map (conjA σ).toMonoidHom ≤ stdAlt n := by
    rintro _ ⟨k, hk, rfl⟩ i hi
    have hia : (e₀ (e₀.symm ⟨i, hi⟩)).1 = i := by simp
    have hσa : σ (e₀.symm ⟨i, hi⟩).1 = i := by rw [hσ, hia]
    have hkfix := hfix k hk _ (e₀.symm ⟨i, hi⟩).2
    have h1 : σ⁻¹ i = (e₀.symm ⟨i, hi⟩).1 := by
      rw [Equiv.Perm.inv_eq_iff_eq, hσa]
    show (σ * (k : Perm (Fin (n + 4))) * σ⁻¹) i = i
    rw [Perm.mul_apply, Perm.mul_apply, h1, hkfix, hσa]
  have hcard' : Nat.card (stdAlt n) ≤ Nat.card (K'.map (conjA σ).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (conjA σ).injective]
    exact (card_stdAlt_le n (by omega)).trans hcard
  exact Subgroup.eq_of_le_of_card_ge hle hcard'

theorem numMoved_of_cycleType_two_two {m : ℕ} {σ : Perm (Fin m)} (h : σ.cycleType = {2, 2}) :
    numMoved σ = 4 := by
  rw [numMoved_eq_card_support, ← Equiv.Perm.sum_cycleType, h]
  rfl

theorem numMoved_of_cycleType_two_four {m : ℕ} {σ : Perm (Fin m)} (h : σ.cycleType = {2, 2, 2, 2}) :
    numMoved σ = 8 := by
  rw [numMoved_eq_card_support, ← Equiv.Perm.sum_cycleType, h]
  rfl

open CFSG.GH74.GLS.Th2.AltInv in
theorem alt_types {m : ℕ} (hm : m = 9 ∨ m = 10 ∨ m = 11) {X : Type} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin m)) {x : X} (hx : orderOf x = 2)
    (h5 : 5 ∣ Nat.card ↥(centralizer ({x} : Set X)))
    {W : Subgroup X} (hW : Nat.card ↥W = 2 ^ (Nat.card X).factorization 2) {v : X}
    (hv2 : orderOf v = 2) (hvc : ∀ w ∈ W, w * v = v * w) :
    numMoved ((e x : alternatingGroup (Fin m)) : Perm (Fin m)) = 4 ∧
      numMoved ((e v : alternatingGroup (Fin m)) : Perm (Fin m)) = 8 := by
  have hm11 : m ≤ 11 := by omega
  have : NeZero m := ⟨by omega⟩
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hXcard : Nat.card X = m.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  obtain ⟨hn5, hn2⟩ := numerics hm
  rw [← hXcard] at hn2
  set k := (Nat.card X).factorization 2 with hk
  have hone : ∀ {y : X}, orderOf y = 2 → e y * e y = 1 ∧ e y ≠ 1 := by
    intro y hy
    refine ⟨by rw [← map_mul, orderOf_two_sq hy, map_one], fun h => ?_⟩
    have : y = 1 := e.injective (by rw [h, map_one])
    rw [this, orderOf_one] at hy
    omega
  obtain ⟨hx'2, hx'1⟩ := hone hx
  obtain ⟨hv'2, hv'1⟩ := hone hv2
  have hCx : Nat.card ↥(centralizer ({x} : Set X)) = Nat.card ↥(centralizer ({e x} : Set _)) :=
    card_centralizer_equiv e x
  have hCv : Nat.card ↥(centralizer ({v} : Set X)) = Nat.card ↥(centralizer ({e v} : Set _)) :=
    card_centralizer_equiv e v
  have hAx := card_centralizer_alt hx'2 hx'1
  have hAv := card_centralizer_alt hv'2 hv'1
  have htype_x : ((e x : alternatingGroup (Fin m)) : Perm (Fin m)).cycleType = {2, 2} := by
    rcases cycleType_involution hm11 hx'2 hx'1 with h | h
    · exact h
    · exfalso
      have hS := nat_card_centralizer_two_four h
      have : 5 ∣ (m - 8).factorial * 384 := by
        rw [← hS, ← hAx]
        exact (hCx ▸ h5).mul_right 2
      exact hn5 this
  have hCxval : Nat.card ↥(centralizer ({x} : Set X)) = (m - 4).factorial * 4 := by
    have hS := nat_card_centralizer_two_two htype_x
    rw [hCx]
    omega
  have h2k : 2 ^ k ∣ Nat.card ↥(centralizer ({v} : Set X)) := by
    have hle : W ≤ centralizer ({v} : Set X) := fun w hw =>
      mem_centralizer_singleton_iff.2 (hvc w hw)
    rw [← hW]
    exact Subgroup.card_dvd_of_le hle
  have htype_v : ((e v : alternatingGroup (Fin m)) : Perm (Fin m)).cycleType = {2, 2, 2, 2} := by
    rcases cycleType_involution hm11 hv'2 hv'1 with h | h
    · exfalso
      have hS := nat_card_centralizer_two_two h
      have : Nat.card ↥(centralizer ({v} : Set X)) = (m - 4).factorial * 4 := by
        rw [hCv]
        omega
      rw [this] at h2k
      exact hn2 h2k
    · exact h
  exact ⟨numMoved_of_cycleType_two_two htype_x, numMoved_of_cycleType_two_four htype_v⟩

end CFSG.GH74.GLS.Th2.AltStd
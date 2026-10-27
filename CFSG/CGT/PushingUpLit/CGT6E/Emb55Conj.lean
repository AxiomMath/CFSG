module

public import CFSG.Quasithin.Background.ConjTransport
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

@[expose] def conjSub (q : MulAut V) (Y : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  Y.map (MulAut.conj q).toMonoidHom

theorem mem_conjSub {q x : MulAut V} {Y : Subgroup (MulAut V)} :
    x ∈ conjSub q Y ↔ ∃ y ∈ Y, q * y * q⁻¹ = x := by
  simp [conjSub, MulAut.conj_apply]

theorem conj_mem_conjSub {q y : MulAut V} {Y : Subgroup (MulAut V)} (hy : y ∈ Y) :
    q * y * q⁻¹ ∈ conjSub q Y :=
  mem_conjSub.mpr ⟨y, hy, rfl⟩

theorem card_conjSub (q : MulAut V) (Y : Subgroup (MulAut V)) :
    Nat.card (conjSub q Y) = Nat.card Y :=
  (Nat.card_congr (Y.equivMapOfInjective (MulAut.conj q).toMonoidHom
    (MulAut.conj q).injective).toEquiv).symm

theorem card_commV_conjSub (q : MulAut V) (Y : Subgroup (MulAut V)) :
    Nat.card (commV (conjSub q Y)) = Nat.card (commV Y) :=
  CFSG.Quasithin.ConjTransport.card_commV_map_conj Y q

theorem mem_commV_conjSub {q : MulAut V} {Y : Subgroup (MulAut V)} {u : V} :
    u ∈ commV (conjSub q Y) ↔ q⁻¹ u ∈ commV Y :=
  CFSG.Quasithin.ConjTransport.mem_commV_map_conj_iff

theorem klein_inv [Finite V] {U P : Subgroup V} (hU : Nat.card U = 4) (hPU : P ≤ U)
    {g : MulAut V} (hg : g ^ 3 = 1) (hgP : ∀ p ∈ P, g p ∈ P)
    (hfpf : ∀ u ∈ U, g u = u → u = 1) : P = ⊥ ∨ P = U := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hP1, hP2⟩ := hcon
  obtain ⟨p, hpP, hp1⟩ : ∃ p ∈ P, p ≠ 1 := by
    by_contra hh
    push Not at hh
    exact hP1 ((Subgroup.eq_bot_iff_forall P).mpr hh)
  have h3 : ∀ v : V, g (g (g v)) = v := fun v => by
    have h : (g ^ 3) v = v := by rw [hg]; rfl
    simpa [pow_succ, MulAut.mul_apply] using h
  have hgp : g p ∈ P := hgP p hpP
  have hggp : g (g p) ∈ P := hgP _ hgp
  have e1 : g p ≠ p := fun h => hp1 (hfpf p (hPU hpP) h)
  have e2 : g (g p) ≠ p := fun h => e1 (by
    have := congrArg g h
    rw [h3] at this
    exact this.symm)
  have n0 : p ≠ 1 := hp1
  have n1 : g p ≠ 1 := fun h => hp1 (g.injective (by rw [h, map_one]))
  have n2 : g (g p) ≠ 1 := fun h => n1 (g.injective (by rw [h, map_one]))
  let f : Fin 4 → P := ![⟨1, P.one_mem⟩, ⟨p, hpP⟩, ⟨g p, hgp⟩, ⟨g (g p), hggp⟩]
  have hinj : Function.Injective f := by
    intro i j hij
    have hij' : ((f i : P) : V) = (f j : V) := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij' ⊢ <;>
      first
      | exact absurd hij'.symm n0
      | exact absurd hij' n0
      | exact absurd hij'.symm n1
      | exact absurd hij' n1
      | exact absurd hij'.symm n2
      | exact absurd hij' n2
      | exact absurd hij' e1
      | exact absurd hij'.symm e1
      | exact absurd hij' e2
      | exact absurd hij'.symm e2
  have h4 : 4 ≤ Nat.card P := by
    have := Nat.card_le_card_of_injective f hinj
    simpa using this
  have hle : Nat.card P ≤ Nat.card U := Subgroup.card_le_of_le hPU
  exact hP2 (Subgroup.eq_of_le_of_card_ge hPU (by omega))

theorem zpowers_eq_of_card_three {M : Type*} [Group M] {K : Subgroup M} (hK : Nat.card K = 3)
    {k : M} (hk : k ∈ K) (hk1 : k ≠ 1) : Subgroup.zpowers k = K := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hle : Subgroup.zpowers k ≤ K := Subgroup.zpowers_le.mpr hk
  have hdvd : Nat.card (Subgroup.zpowers k) ∣ 3 := hK ▸ Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers] at hdvd
  have hne : orderOf k ≠ 1 := fun h => hk1 (orderOf_eq_one_iff.mp h)
  have h3 : orderOf k = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, h3, hK])

end CFSG.CGT.PushingUpLit.CGT6E

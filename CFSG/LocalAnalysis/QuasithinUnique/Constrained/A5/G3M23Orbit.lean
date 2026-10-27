module

public import Certificates.Certificate17025
public import Certificates.Certificate9951

public section

namespace CFSG.QuasithinUnique.A5.G3.M23

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

theorem nxt_spec : ∀ i : Fin 23, evalW tGens (wd i) i = nxt i :=
  Certificates.certificate17025.1

theorem cyc : ∀ y z : Fin 23, tau y = tau z → ∃ k : Fin 16, nxt^[k.val] y = z :=
  Certificates.certificate17025.2.1

theorem exists_mem_closure_iter (y : Fin 23) (k : ℕ) :
    ∃ t ∈ Subgroup.closure {g | g ∈ tGens}, t y = nxt^[k] y := by
  induction k with
  | zero => exact ⟨1, Subgroup.one_mem _, rfl⟩
  | succ k ih =>
    obtain ⟨t, ht, hty⟩ := ih
    refine ⟨evalW tGens (wd (nxt^[k] y)) * t, Subgroup.mul_mem _ (evalW_mem_closure _ _) ht, ?_⟩
    rw [Perm.mul_apply, hty, nxt_spec, Function.iterate_succ_apply']

theorem exists_mem_closure_eq (y z : Fin 23) (h : tau y = tau z) :
    ∃ t ∈ Subgroup.closure {g | g ∈ tGens}, t y = z := by
  obtain ⟨k, hk⟩ := cyc y z h
  obtain ⟨t, ht, hty⟩ := exists_mem_closure_iter y k.val
  exact ⟨t, ht, hty.trans hk⟩

theorem closure_tGens_fix_zero :
    ∀ t ∈ Subgroup.closure {g | g ∈ tGens}, t 0 = 0 := by
  have h : Subgroup.closure {g | g ∈ tGens} ≤ MulAction.stabilizer (Perm (Fin 23)) (0 : Fin 23) := by
    rw [Subgroup.closure_le]
    intro g hg
    have hg' : g ∈ tGens := hg
    show g 0 = 0
    exact Certificates.certificate9951.1 g hg'
  intro t ht
  exact h ht

theorem exists_pat (S : Finset (Fin 23)) (hfib : ∀ y z, tau y = tau z → (y ∈ S ↔ z ∈ S)) :
    ∃ pat : Fin 4 → Bool, S = Finset.univ.filter (fun y => pat (tau y) = true) := by
  classical
  refine ⟨fun l => decide (∃ y, tau y = l ∧ y ∈ S), ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  constructor
  · intro hy
    exact ⟨y, rfl, hy⟩
  · rintro ⟨z, hz, hzS⟩
    exact (hfib z y hz).mp hzS

theorem pat_card_cases : ∀ pat : Fin 4 → Bool, pat 0 = true →
    (Finset.univ.filter (fun y => pat (tau y) = true)).card ∣ 1920 →
    pat = ![true, false, false, false] ∨ pat = ![true, true, false, false] ∨
      pat = ![true, false, true, false] :=
  Certificates.certificate17025.2.2.1

theorem pat_card_cases' : ∀ pat : Fin 4 → Bool, pat 1 = true → pat 0 = false → pat 2 = false →
    (Finset.univ.filter (fun y => pat (tau y) = true)).card ∣ 1920 →
    pat = ![false, true, false, false] :=
  Certificates.certificate17025.2.2.2

section Orbits

variable {Y : Subgroup (Perm (Fin 23))}

theorem orbit_fiber
    (hT : Subgroup.closure {g | g ∈ tGens} ≤ Y) (x y z : Fin 23)
    (h : tau y = tau z) (hy : y ∈ MulAction.orbit ↥Y x) : z ∈ MulAction.orbit ↥Y x := by
  obtain ⟨t, ht, hty⟩ := exists_mem_closure_eq y z h
  obtain ⟨⟨u, hu⟩, rfl⟩ := hy
  refine ⟨⟨t * u, Y.mul_mem (hT ht) hu⟩, ?_⟩
  show (t * u) x = z
  rw [Perm.mul_apply]
  exact hty

theorem orbit_pattern
    (hT : Subgroup.closure {g | g ∈ tGens} ≤ Y) (x : Fin 23) :
    ∃ pat : Fin 4 → Bool, (∀ y, y ∈ MulAction.orbit ↥Y x ↔ pat (tau y) = true) ∧
      Nat.card (MulAction.orbit ↥Y x) =
        (Finset.univ.filter (fun y => pat (tau y) = true)).card := by
  classical
  obtain ⟨pat, hpat⟩ := exists_pat (Finset.univ.filter (fun y => y ∈ MulAction.orbit ↥Y x))
    (fun y z h => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hy => orbit_fiber hT x y z h hy, fun hz => orbit_fiber hT x z y h.symm hz⟩)
  have hiff : ∀ y, y ∈ MulAction.orbit ↥Y x ↔ pat (tau y) = true := by
    intro y
    have := congrArg (fun S => y ∈ S) hpat
    simpa using this
  refine ⟨pat, hiff, ?_⟩
  have hset : MulAction.orbit ↥Y x = {y | pat (tau y) = true} := by
    ext y
    exact hiff y
  rw [hset, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card' {y | pat (tau y) = true}]
  congr 1
  ext y
  simp

theorem card_orbit_dvd (x : Fin 23) : Nat.card (MulAction.orbit ↥Y x) ∣ Nat.card ↥Y := by
  refine Dvd.intro (Nat.card (MulAction.stabilizer ↥Y x)) ?_
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer ↥Y x]
  exact Subgroup.index_mul_card (MulAction.stabilizer ↥Y x)

theorem orbit_zero_cases
    (hT : Subgroup.closure {g | g ∈ tGens} ≤ Y) (hcard : Nat.card ↥Y = 1920) :
    (∀ y, y ∈ MulAction.orbit ↥Y (0 : Fin 23) ↔ tau y = 0) ∨
    Nat.card (MulAction.orbit ↥Y (0 : Fin 23)) = 3 ∨
    (∀ y, y ∈ MulAction.orbit ↥Y (0 : Fin 23) ↔ (tau y = 0 ∨ tau y = 2)) := by
  obtain ⟨pat, hiff, hcard'⟩ := orbit_pattern hT (0 : Fin 23)
  have h0 : pat 0 = true := by
    have := (hiff 0).mp (MulAction.mem_orbit_self _)
    simpa [tau] using this
  have hdvd : (Finset.univ.filter (fun y => pat (tau y) = true)).card ∣ 1920 := by
    rw [← hcard', ← hcard]
    exact card_orbit_dvd 0
  rcases pat_card_cases pat h0 hdvd with h | h | h
  · left
    intro y
    rw [hiff, h]
    revert y
    exact Certificates.certificate9951.2.1
  · right; left
    rw [hcard', h]
    exact Certificates.certificate9951.2.2.1
  · right; right
    intro y
    rw [hiff, h]
    revert y
    exact Certificates.certificate9951.2.2.2.1

theorem orbit_nineteen
    (hT : Subgroup.closure {g | g ∈ tGens} ≤ Y) (hcard : Nat.card ↥Y = 1920)
    (hp : ∀ y, y ∈ MulAction.orbit ↥Y (0 : Fin 23) ↔ (tau y = 0 ∨ tau y = 2)) :
    ∀ y, y ∈ MulAction.orbit ↥Y (19 : Fin 23) ↔ tau y = 1 := by
  obtain ⟨pat, hiff, hcard'⟩ := orbit_pattern hT (19 : Fin 23)
  have hdisj : ∀ y, y ∈ MulAction.orbit ↥Y (19 : Fin 23) →
      ¬ (tau y = 0 ∨ tau y = 2) := by
    intro y hy hy0
    have h0 : y ∈ MulAction.orbit ↥Y (0 : Fin 23) := (hp y).mpr hy0
    have e1 : MulAction.orbit ↥Y y = MulAction.orbit ↥Y (19 : Fin 23) :=
      MulAction.orbit_eq_iff.mpr hy
    have e2 : MulAction.orbit ↥Y y = MulAction.orbit ↥Y (0 : Fin 23) :=
      MulAction.orbit_eq_iff.mpr h0
    have h19 : (19 : Fin 23) ∈ MulAction.orbit ↥Y (0 : Fin 23) := by
      rw [← e2, e1]
      exact MulAction.mem_orbit_self _
    have := (hp 19).mp h19
    revert this
    exact Certificates.certificate9951.2.2.2.2.1
  have h1 : pat 1 = true := by
    have := (hiff 19).mp (MulAction.mem_orbit_self _)
    simpa [tau] using this
  have hn0 : pat 0 = false := by
    by_contra hne
    have hne' : pat 0 = true := by simpa using hne
    have h0 : (0 : Fin 23) ∈ MulAction.orbit ↥Y (19 : Fin 23) := by
      rw [hiff]
      simpa [tau] using hne'
    exact hdisj 0 h0 (Or.inl (by decide))
  have hn2 : pat 2 = false := by
    by_contra hne
    have hne' : pat 2 = true := by simpa using hne
    have h5 : (5 : Fin 23) ∈ MulAction.orbit ↥Y (19 : Fin 23) := by
      rw [hiff]
      simpa [tau] using hne'
    exact hdisj 5 h5 (Or.inr (by decide))
  have hdvd : (Finset.univ.filter (fun y => pat (tau y) = true)).card ∣ 1920 := by
    rw [← hcard', ← hcard]
    exact card_orbit_dvd 19
  have h := pat_card_cases' pat h1 hn0 hn2 hdvd
  intro y
  rw [hiff, h]
  revert y
  exact Certificates.certificate9951.2.2.2.2.2

end Orbits

end CFSG.QuasithinUnique.A5.G3.M23

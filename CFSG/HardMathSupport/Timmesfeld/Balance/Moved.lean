module

public import CFSG.HardMathSupport.Timmesfeld.Balance.CompCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Balance.Diagonal
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ClassicalInvolution.Balance.LocalBalance

universe u

section Orbit

variable {Y : Type*} [Group Y] {p : ℕ}

omit [Group Y] in
theorem exists_mul_mod_eq_one (hp : p.Prime) {n : ℕ} (hn : ¬ p ∣ n) : ∃ k : ℕ, (n * k) % p = 1 := by
  have := Fact.mk hp
  have hn0 : (n : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  refine ⟨((n : ZMod p)⁻¹).val, ?_⟩
  have h1 : ((n * ((n : ZMod p)⁻¹).val : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact mul_inv_cancel₀ hn0
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h1
  rw [this]
  exact Nat.mod_eq_of_lt hp.one_lt

theorem dvd_of_conjSub_pow_eq (hp : p.Prime) {L : Subgroup Y} {f : Y} (hf : f ^ p = 1)
    (hmoved : conjSub f L ≠ L) {n : ℕ} (h : conjSub (f ^ n) L = L) : p ∣ n := by
  by_contra hn
  obtain ⟨k, hk⟩ := exists_mul_mod_eq_one hp hn
  apply hmoved
  have h1 : conjSub ((f ^ n) ^ k) L = L := conjSub_pow_eq h k
  rw [← pow_mul, pow_eq_pow_mod _ hf, hk, pow_one] at h1
  exact h1

theorem conjSub_pow_ne_self (hp : p.Prime) {L : Subgroup Y} {f : Y} (hf : f ^ p = 1)
    (hmoved : conjSub f L ≠ L) {i : ℕ} (hi0 : 0 < i) (hip : i < p) :
    conjSub (f ^ i) L ≠ L := fun h =>
  absurd (Nat.le_of_dvd hi0 (dvd_of_conjSub_pow_eq hp hf hmoved h)) (not_le.2 hip)

theorem isComponent_conjSub' {L : Subgroup Y} (hL : IsComponent L) (g : Y) :
    IsComponent (conjSub g L) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hL

theorem conjSub_comm_of_mul_comm {g h : Y} (hgh : g * h = h * g) (K : Subgroup Y) :
    conjSub g (conjSub h K) = conjSub h (conjSub g K) := by
  rw [conjSub_conjSub, conjSub_conjSub, hgh]

theorem conjSub_pow_mul_pow_cancel (hp : p.Prime) {f : Y} (hf : f ^ p = 1) (i : ℕ)
    (K : Subgroup Y) : conjSub (f ^ (i * (p - 1))) (conjSub (f ^ i) K) = K := by
  rw [conjSub_conjSub, ← pow_add]
  have h : i * (p - 1) + i = p * i := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [h, pow_mul, hf, one_pow, conjSub_one]

theorem eq_conjSub_pow_of_conjSub_pow_eq (hp : p.Prime) {f : Y} (hf : f ^ p = 1) {i : ℕ}
    {K K' : Subgroup Y} (h : conjSub (f ^ i) K = K') : K = conjSub (f ^ (i * (p - 1))) K' := by
  rw [← h, conjSub_pow_mul_pow_cancel hp hf]

theorem pow_eq_one_of_dvd {f : Y} (hf : f ^ p = 1) {n : ℕ} (hn : p ∣ n) : f ^ n = 1 := by
  obtain ⟨c, rfl⟩ := hn
  rw [pow_mul, hf, one_pow]

theorem conj_ofFn_prod (d : Y) : ∀ {n : ℕ} (g : Fin n → Y),
    d * (List.ofFn g).prod * d⁻¹ = (List.ofFn fun i => d * g i * d⁻¹).prod
  | 0, g => by simp
  | n + 1, g => by
    have ih := conj_ofFn_prod d (fun i : Fin n => g i.succ)
    simp only [List.ofFn_succ, List.prod_cons]
    rw [← ih]
    group

theorem commute_prod_ofFn_iff (hp : 0 < p) (w : Y) (g : Fin p → Y)
    (h : ∀ i : Fin p, (i : ℕ) ≠ 0 → Commute w (g i)) :
    Commute w (List.ofFn g).prod ↔ Commute w (g ⟨0, hp⟩) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hQ : Commute w (List.ofFn fun i : Fin n => g i.succ).prod :=
    Commute.list_prod_right _ _ (fun z hz => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
      exact h i.succ (Nat.succ_ne_zero _))
  have h0 : (⟨0, hp⟩ : Fin (n + 1)) = 0 := rfl
  rw [h0, List.ofFn_succ, List.prod_cons]
  constructor
  · intro hP
    have := hP.mul_right hQ.inv_right
    simpa using this
  · intro h0'
    exact h0'.mul_right hQ

theorem commute_inv_mul_of_prod_eq (hp : 0 < p) (w : Y) (g h : Fin p → Y)
    (hgh : (List.ofFn g).prod = (List.ofFn h).prod)
    (hg : ∀ i : Fin p, (i : ℕ) ≠ 0 → Commute w (g i))
    (hh : ∀ i : Fin p, (i : ℕ) ≠ 0 → Commute w (h i)) :
    Commute w ((g ⟨0, hp⟩)⁻¹ * h ⟨0, hp⟩) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hQg : Commute w (List.ofFn fun i : Fin n => g i.succ).prod :=
    Commute.list_prod_right _ _ (fun z hz => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
      exact hg i.succ (Nat.succ_ne_zero _))
  have hQh : Commute w (List.ofFn fun i : Fin n => h i.succ).prod :=
    Commute.list_prod_right _ _ (fun z hz => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
      exact hh i.succ (Nat.succ_ne_zero _))
  have h0 : (⟨0, hp⟩ : Fin (n + 1)) = 0 := rfl
  rw [h0]
  rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons] at hgh
  have : (g 0)⁻¹ * h 0 =
      (List.ofFn fun i : Fin n => g i.succ).prod * (List.ofFn fun i : Fin n => h i.succ).prod⁻¹ :=
    calc (g 0)⁻¹ * h 0
        = (g 0)⁻¹ * (h 0 * (List.ofFn fun i : Fin n => h i.succ).prod) *
            (List.ofFn fun i : Fin n => h i.succ).prod⁻¹ := by group
      _ = (g 0)⁻¹ * (g 0 * (List.ofFn fun i : Fin n => g i.succ).prod) *
            (List.ofFn fun i : Fin n => h i.succ).prod⁻¹ := by rw [← hgh]
      _ = _ := by group
  rw [this]
  exact hQg.mul_right hQh.inv_right

end Orbit

variable {Y : Type u} [Group Y] [Finite Y] {p : ℕ}


theorem commute_of_moved_p (hp : p.Prime) {L : Subgroup Y} (hL : IsComponent L)
    (hLp : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) {f : Y} (hf : f ^ p = 1)
    (hmoved : conjSub f L ≠ L) {d : Y}
    (hd : d ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({f} : Set Y))) :
    ∀ x ∈ L, d * x = x * d := by
  have hp0 : 0 < p := hp.pos
  have hdf : d * f = f * d :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.map_subtype_le _ hd : d ∈ Subgroup.centralizer ({f} : Set Y))
  have hdfp : ∀ i : ℕ, f ^ i * d = d * f ^ i := fun i =>
    (Commute.pow_left (show Commute f d from hdf.symm) i).eq
  have hcop : (orderOf d).Coprime p :=
    CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf hp hd
  obtain ⟨Δ, hΔC, hΔcomp, hΔdvd, hΔmem⟩ := exists_diagonal_component_p hp hL hf hmoved
  have hΔp : ¬ Nat.Coprime p (Nat.card Δ) := fun hc =>
    Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_refl p) (hLp.trans hΔdvd) hc
  have hdΔ := commute_of_mem_gLAPPrimeCoreOf_of_isComponent hp hΔC hΔcomp hΔp hd
  have hrel : ∀ x ∈ L, (List.ofFn fun i : Fin p =>
      d * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * d⁻¹).prod =
      (List.ofFn fun i : Fin p => f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹).prod := by
    intro x hx
    rw [← conj_ofFn_prod, hdΔ _ (hΔmem x hx)]
    group
  have hcommL : ∀ x ∈ L, ∀ w ∈ L, ∀ i : Fin p, (i : ℕ) ≠ 0 →
      Commute w (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) := by
    intro x hx w hw i hi
    exact commute_of_isComponent_of_ne hL (isComponent_conjSub' hL _)
      (conjSub_pow_ne_self hp hf hmoved (Nat.pos_of_ne_zero hi) i.2).symm w hw _
      (conj_mem_conjSub hx)
  have hLd : IsComponent (conjSub d L) := isComponent_conjSub' hL d
  have hex : ∃ j : ℕ, conjSub d L = conjSub (f ^ j) L := by
    by_contra hcon
    push Not at hcon
    have hne : ∀ i : ℕ, conjSub (f ^ i) (conjSub d L) ≠ L := fun i hi =>
      hcon (i * (p - 1)) (eq_conjSub_pow_of_conjSub_pow_eq hp hf hi)
    obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_isQuasisimple hL.1
    have hall : ∀ x ∈ L, ∀ w ∈ L, w * x = x * w := by
      intro x hx w hw
      have hy : ∀ i : Fin p,
          Commute w (d * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * d⁻¹) := by
        intro i
        have hmem : d * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * d⁻¹ ∈
            conjSub (f ^ (i : ℕ)) (conjSub d L) := by
          rw [conjSub_comm_of_mul_comm (hdfp i)]
          exact conj_mem_conjSub (conj_mem_conjSub hx)
        exact commute_of_isComponent_of_ne hL (isComponent_conjSub' hLd _)
          (hne i).symm w hw _ hmem
      have hP : Commute w (List.ofFn fun i : Fin p =>
          d * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * d⁻¹).prod :=
        Commute.list_prod_right _ _ (fun z hz => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
          exact hy i)
      rw [hrel x hx] at hP
      have hx0 := (commute_prod_ofFn_iff hp0 w
        (fun i : Fin p => f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹)
        (fun i hi => hcommL x hx w hw i hi)).1 hP
      have := hx0.eq
      simpa using this
    exact hab (hall a ha b hb).symm
  obtain ⟨j, hj⟩ := hex
  have hdL : conjSub d L = L := by
    have hu : conjSub (f ^ (j * (p - 1))) (conjSub d L) = L := by
      rw [hj, conjSub_pow_mul_pow_cancel hp hf]
    have hud : conjSub (f ^ (j * (p - 1)) * d) L = L := by
      rw [← conjSub_conjSub]
      exact hu
    have hpow := conjSub_pow_eq hud (orderOf d)
    rw [(show Commute (f ^ (j * (p - 1))) d from hdfp _).mul_pow, pow_orderOf_eq_one,
      mul_one, ← pow_mul] at hpow
    have hdvd := dvd_of_conjSub_pow_eq hp hf hmoved hpow
    have hpm : ¬ p ∣ orderOf d := fun h =>
      Nat.not_coprime_of_dvd_of_dvd hp.one_lt h (dvd_refl p) hcop
    have hpp1 : ¬ p ∣ p - 1 := fun h =>
      absurd (Nat.le_of_dvd (by have := hp.two_le; omega) h) (by have := hp.pos; omega)
    have hpj : p ∣ j := by
      rcases hp.dvd_mul.1 hdvd with h | h
      · exact (hp.dvd_mul.1 h).resolve_right hpp1
      · exact absurd h hpm
    rw [hj, pow_eq_one_of_dvd hf hpj, conjSub_one]
  have hdc : ∀ i : ℕ, conjSub d (conjSub (f ^ i) L) = conjSub (f ^ i) L := by
    intro i
    rw [conjSub_comm_of_mul_comm (hdfp i).symm, hdL]
  have hiff : ∀ h, d * h * d⁻¹ ∈ L ↔ h ∈ L := by
    intro h
    have := mem_conjSub_iff (g := d) (L := L) (y := d * h * d⁻¹)
    rw [hdL] at this
    have e : d⁻¹ * (d * h * d⁻¹) * d = h := by group
    rw [e] at this
    exact this
  refine commute_of_central_displacement hL.1 hiff ?_
  intro x hx w hw
  have hh : ∀ i : Fin p, (i : ℕ) ≠ 0 →
      Commute w (d * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * d⁻¹) := by
    intro i hi
    have hmem : d * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * d⁻¹ ∈ conjSub (f ^ (i : ℕ)) L := by
      rw [← hdc i]
      exact conj_mem_conjSub (conj_mem_conjSub hx)
    exact commute_of_isComponent_of_ne hL (isComponent_conjSub' hL _)
      (conjSub_pow_ne_self hp hf hmoved (Nat.pos_of_ne_zero hi) i.2).symm w hw _ hmem
  have := (commute_inv_mul_of_prod_eq hp0 w
    (fun i : Fin p => f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹)
    (fun i : Fin p => d * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * d⁻¹)
    (hrel x hx).symm (fun i hi => hcommL x hx w hw i hi) hh).eq
  simpa using this

end CFSG.HardMathSupport.Timmesfeld.Balance

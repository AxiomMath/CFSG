module

public import Certificates.Data.Kernel.E64CC
public import CFSG.Certificates.Kernel.PermCent.OrbGroup
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.KC.E64CCSound

open CFSG.KC.E64CC CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup
open CFSG.KLie.CT (fget)

abbrev Rep (P : Nat) (σ : Equiv.Perm (Fin 14)) : Prop := PRep 14 4 P σ

theorem ap_eq (p x : Nat) : ap p x = pg 4 (mask 4) p x := rfl

theorem rep_ap {P : Nat} {σ : Equiv.Perm (Fin 14)} (h : Rep P σ) (x : Fin 14) :
    ap P x = σ x := h x

theorem beq_true {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem allN14 {f : Nat → Bool} (h : allN 14 f = true) : ∀ x : Fin 14, f x = true :=
  fun x => PK.allN_iff.1 h x x.2

theorem rep_eqK {P Q : Nat} {σ : Equiv.Perm (Fin 14)} (hP : Rep P σ) (h : eqK P Q = true) :
    Rep Q σ := fun x => by
  have := beq_true (allN14 h x)
  rw [← hP x]
  exact this.symm

theorem rep_eqK' {P Q : Nat} {σ : Equiv.Perm (Fin 14)} (hQ : Rep Q σ) (h : eqK P Q = true) :
    Rep P σ := fun x => by
  have := beq_true (allN14 h x)
  rw [← hQ x]
  exact this

theorem eqK_of_rep {P Q : Nat} {σ : Equiv.Perm (Fin 14)} (hP : Rep P σ) (hQ : Rep Q σ) :
    eqK P Q = true := by
  unfold eqK
  rw [PK.allN_iff]
  intro i hi
  have e : ap P i = ap Q i := (rep_ap hP ⟨i, hi⟩).trans (rep_ap hQ ⟨i, hi⟩).symm
  rw [e]
  exact Nat.beq_refl _

theorem rep_idK {P : Nat} (h : idK P = true) : Rep P 1 := fun x => by
  have := beq_true (allN14 h x)
  rw [ap_eq] at this
  rw [this]
  rfl

theorem commK_iff {X G : Nat} {σ τ : Equiv.Perm (Fin 14)} (hX : Rep X σ) (hG : Rep G τ) :
    commK X G = true ↔ σ * τ = τ * σ := by
  have key : ∀ x : Fin 14, ap X (ap G x) = (σ (τ x) : Nat) ∧ ap G (ap X x) = (τ (σ x) : Nat) :=
    fun x => by
      rw [rep_ap hG x, rep_ap hX x, rep_ap hX, rep_ap hG]
      exact ⟨rfl, rfl⟩
  constructor
  · intro h
    refine Equiv.ext fun x => Fin.ext ?_
    have := beq_true (allN14 h x)
    rw [(key x).1, (key x).2] at this
    exact this
  · intro h
    unfold commK
    rw [PK.allN_iff]
    intro i hi
    rw [(key ⟨i, hi⟩).1, (key ⟨i, hi⟩).2]
    have e : σ (τ ⟨i, hi⟩) = τ (σ ⟨i, hi⟩) := by
      rw [← Equiv.Perm.mul_apply, h, Equiv.Perm.mul_apply]
    rw [e]
    exact Nat.beq_refl _

theorem exists_ne_pi {X : Nat} {σ : Equiv.Perm (Fin 14)} (hX : Rep X σ) (h : isPiK X = false) :
    ∃ x : Fin 14, (σ x : Nat) ≠ (x + 7) % 14 := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  have : isPiK X = true := by
    unfold isPiK
    rw [PK.allN_iff]
    intro i hi
    rw [rep_ap hX ⟨i, hi⟩, hc ⟨i, hi⟩]
    exact Nat.beq_refl _
  rw [this] at h
  exact absurd h (by decide)

theorem rep_eq3K {r p q : Nat} {σ τ : Equiv.Perm (Fin 14)} (hp : Rep p σ) (hq : Rep q τ)
    (h : eq3K r p q = true) : Rep r (σ * τ) := fun x => by
  have := beq_true (allN14 h x)
  rw [ap_eq] at this
  rw [this, rep_ap hq x, rep_ap hp]
  rfl

theorem rep_mulK {p q : Nat} {σ τ : Equiv.Perm (Fin 14)} (hp : Rep p σ) (hq : Rep q τ) :
    Rep (mulK p q) (σ * τ) :=
  prep_pcomp (by norm_num) hp hq

theorem rep_pidn : Rep (pidn 14 4) 1 := prep_pidn (by norm_num) (by norm_num)

theorem bitK_eq (M i : Nat) : bitK M i = M.testBit i := by
  unfold bitK
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h1 : Nat.land (Nat.shiftRight M i) 1 = M / 2 ^ i % 2 := by
    change (M >>> i) &&& 1 = M / 2 ^ i % 2
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.and_one_is_mod _
  rw [h1]
  cases h : decide (M / 2 ^ i % 2 = 1)
  · rw [decide_eq_false_iff_not] at h
    exact Bool.eq_false_iff.2 fun h2 => h (beq_true h2)
  · rw [decide_eq_true_eq] at h
    rw [h]
    rfl

theorem testBit_lor' (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

theorem testBit_one_shiftLeft (a x : Nat) : (Nat.shiftLeft 1 a).testBit x = decide (a = x) := by
  change (1 <<< a).testBit x = decide (a = x)
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem testBit_orF {f : Nat → Nat} {i : Nat} :
    ∀ {n : Nat}, (orF f n).testBit i = true → ∃ j < n, f j = i
  | 0, h => by simp [orF] at h
  | n + 1, h => by
    change (Nat.lor (orF f n) (Nat.shiftLeft 1 (f n))).testBit i = true at h
    rw [testBit_lor', Bool.or_eq_true, testBit_one_shiftLeft, decide_eq_true_eq] at h
    rcases h with h | h
    · obtain ⟨j, hj, e⟩ := testBit_orF h
      exact ⟨j, by omega, e⟩
    · exact ⟨n, by omega, h⟩

theorem testBit_mask3 (a b c x : Nat) :
    (mask3 a b c).testBit x = true ↔ x = a ∨ x = b ∨ x = c := by
  unfold mask3
  rw [testBit_lor', testBit_lor', testBit_one_shiftLeft, testBit_one_shiftLeft,
    testBit_one_shiftLeft]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ((h | h) | h) <;> simp [h]
  · rintro (h | h | h) <;> simp [h]

theorem mask3_iff {a b c a' b' c' : Nat} (h : mask3 a b c = mask3 a' b' c') (x : Nat) :
    (x = a ∨ x = b ∨ x = c) ↔ (x = a' ∨ x = b' ∨ x = c') := by
  rw [← testBit_mask3, ← testBit_mask3, h]

theorem evW_mem {D : Nat → Nat} {st : Nat} {γ : Nat → Equiv.Perm (Fin 14)}
    (hγ : ∀ l < 6, Rep (g6 D st l) (γ l)) (wd : Nat) :
    ∃ σ ∈ Subgroup.closure (γ '' {l | l < 6}), Rep (evW D st wd) σ := by
  unfold evW
  generalize fget wd 0 8 = n
  induction n with
  | zero => exact ⟨1, one_mem _, rep_pidn⟩
  | succ n ih =>
    obtain ⟨σ, hσ, hr⟩ := ih
    have hl : fget (Nat.shiftRight wd 8) n 3 % 6 < 6 := Nat.mod_lt _ (by norm_num)
    exact ⟨σ * γ _, mul_mem hσ (Subgroup.subset_closure ⟨_, hl, rfl⟩),
      rep_mulK hr (hγ _ hl)⟩

theorem closure_subset {X : Type*} [Group X] [Finite X] {γ : Nat → X} {U : Set X} (h1 : 1 ∈ U)
    (hU : ∀ l < 6, ∀ u ∈ U, γ l * u ∈ U) : ∀ y ∈ Subgroup.closure (γ '' {l | l < 6}), y ∈ U := by
  have hall : ∀ g ∈ Subgroup.closure (γ '' {l | l < 6}), ∀ y ∈ U, g * y ∈ U := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact hU l hl
    | one =>
      intro y hy
      rwa [one_mul]
    | mul a b _ _ ha hb =>
      intro y hy
      rw [mul_assoc]
      exact ha _ (hb y hy)
    | inv a _ ha =>
      intro y hy
      obtain ⟨z, hz, e⟩ := surj_of_mapsTo (fun z => a * z) (fun u v e => by simpa using e) ha y hy
      have e2 : a⁻¹ * y = z := by
        rw [← e]
        group
      rw [e2]
      exact hz
  intro y hy
  have := hall y hy 1 h1
  rwa [mul_one] at this

variable {D T : Nat → Nat} {N : Nat}

theorem ixK_spec {k : Nat} (h : ixK D T N k = true) :
    D (28 + k) < N ∧ eqK (T (D (28 + k))) (D k) = true := by
  unfold ixK at h
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at h
  exact h

theorem piK_spec (h : piK T N = true) : ∀ i < N, isPiK (T i) = false := by
  unfold piK at h
  rw [PK.allN_iff] at h
  intro i hi
  simpa using h i hi

theorem cmK_spec {k : Nat} (h : cmK D T N k = true) :
    ∀ i < N, cenK (T i) (D (2 * k)) (D (2 * k + 1)) = true → (D (70 + k)).testBit i = true := by
  unfold cmK at h
  simp only [PK.strictB_eq, Nat.add_eq, Nat.mul_eq] at h
  rw [PK.allN_iff] at h
  intro i hi hc
  have := h i hi
  rw [PK.bIf_eq, if_pos hc, bitK_eq] at this
  exact this

theorem cenK_iff {X A B : Nat} {σ α β : Equiv.Perm (Fin 14)} (hX : Rep X σ) (hA : Rep A α)
    (hB : Rep B β) : cenK X A B = true ↔ σ * α = α * σ ∧ σ * β = β * σ := by
  unfold cenK
  rw [PK.bAnd_eq, Bool.and_eq_true, commK_iff hX hA, commK_iff hX hB]

theorem clK_spec {k : Nat} (h : clK D k = true) {i : Nat} (hi : (D (70 + k)).testBit i = true) :
    ∃ j < 32, fget (D (56 + k)) j 14 = i := by
  unfold clK at h
  simp only [PK.strictB_eq, Nat.add_eq] at h
  rw [beq_true h] at hi
  exact testBit_orF hi

@[expose] def uSet (D : Nat → Nat) (st : Nat) : Set (Equiv.Perm (Fin 14)) :=
  {σ | ∃ u < Nat.shiftRight st 32, Rep (D (2450 + (fld(st, 16, 65535) + u))) σ}

theorem setK_spec {s : Nat} (h : setK D s = true) {γ : Nat → Equiv.Perm (Fin 14)}
    (hγ : ∀ l < 6, Rep (g6 D (D (84 + s)) l) (γ l)) (hsz : 0 < Nat.shiftRight (D (84 + s)) 32) :
    ∀ y ∈ Subgroup.closure (γ '' {l | l < 6}), y ∈ uSet D (D (84 + s)) := by
  unfold setK at h
  simp only [Nat.add_eq] at h
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, PK.allN_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine closure_subset ⟨0, hsz, ?_⟩ ?_
  · rw [Nat.add_zero]
    exact rep_idK h1
  · rintro l hl σ ⟨u, hu, hr⟩
    obtain ⟨hv, he⟩ := h2 u hu l hl
    exact ⟨_, hv, rep_eq3K (hγ l hl) hr he⟩

theorem outK_spec {st t : Nat} {τ : Equiv.Perm (Fin 14)} (ht : Rep t τ)
    (h : outK D st t = true) : 0 < Nat.shiftRight st 32 ∧ τ ∉ uSet D st := by
  unfold outK at h
  simp only [Nat.add_eq] at h
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, PK.allN_iff, Nat.blt_eq] at h
  refine ⟨h.1, ?_⟩
  rintro ⟨u, hu, hr⟩
  have := h.2 u hu
  rw [Bool.not_eq_true', ← Bool.not_eq_true] at this
  exact this (eqK_of_rep hr ht)

theorem witK_spec {st t wx wy : Nat} {τ : Equiv.Perm (Fin 14)} (ht : Rep t τ)
    {γ : Nat → Equiv.Perm (Fin 14)} (hγ : ∀ l < 6, Rep (g6 D st l) (γ l))
    (h : witK D st t wx wy = true) :
    ∃ x ∈ Subgroup.closure (γ '' {l | l < 6}), ∃ y ∈ Subgroup.closure (γ '' {l | l < 6}),
      τ * (y * x) = x * y := by
  unfold witK at h
  simp only [PK.strictB_eq] at h
  obtain ⟨x, hx, hxr⟩ := evW_mem hγ wx
  obtain ⟨y, hy, hyr⟩ := evW_mem hγ wy
  refine ⟨x, hx, y, hy, ?_⟩
  have h1 := rep_mulK ht (rep_mulK hyr hxr)
  have h2 := rep_mulK hxr hyr
  exact prep_eq h1 (rep_eqK h2 (by
    unfold eqK at h ⊢
    rw [PK.allN_iff] at h ⊢
    intro i hi
    rw [beq_true (h i hi)]
    exact Nat.beq_refl _))

theorem resK_spec {r : Nat} (h : resK D T r = true) :
    (Nat.shiftRight (D (328 + r)) 24 = 0 → witK D (D (84 + fld(D (328 + r), 14, 1023)))
        (T (fget (D (328 + r)) 0 14)) (D (1035 + r)) (D (1742 + r)) = true) ∧
      (Nat.shiftRight (D (328 + r)) 24 ≠ 0 → outK D (D (84 + fld(D (328 + r), 14, 1023)))
        (T (fget (D (328 + r)) 0 14)) = true) := by
  unfold resK at h
  simp only [PK.strictB_eq, PK.bIf_eq, Nat.add_eq] at h
  constructor
  · intro h0
    rwa [if_pos (by rw [h0]; rfl)] at h
  · intro h0
    rwa [if_neg (fun e => h0 (beq_true e))] at h

theorem tripK_spec {k₁ k₂ k₃ : Nat} (h : tripK D k₁ k₂ k₃ = true) {j : Nat} (hj : j < 32)
    (hc0 : fget (D (56 + k₁)) j 14 ≠ 0)
    (hc2 : (D (70 + k₂)).testBit (fget (D (56 + k₁)) j 14) = true)
    (hc3 : (D (70 + k₃)).testBit (fget (D (56 + k₁)) j 14) = true) :
    ∃ r, r ≠ 0 ∧ r < 708 ∧ fget (D (328 + r)) 0 14 = fget (D (56 + k₁)) j 14 ∧
      fld(D (328 + r), 14, 1023) < 245 ∧
      setIs (D (84 + fld(D (328 + r), 14, 1023))) k₁ k₂ k₃ = true := by
  unfold tripK at h
  simp only [PK.strictB_eq, Nat.add_eq, Nat.mul_eq] at h
  rw [PK.allN_iff] at h
  have := h j hj
  rw [PK.bIf_eq, if_pos (by
    rw [PK.bAnd_eq, PK.bAnd_eq, bitK_eq, bitK_eq, hc2, hc3, Bool.and_true, Bool.and_true,
      Bool.not_eq_true']
    exact Bool.eq_false_iff.2 fun e => hc0 (beq_true e))] at this
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at this
  obtain ⟨h0, hlt, he, hs2, hs⟩ := this
  exact ⟨_, fun e => by rw [e] at h0; exact absurd h0 (by decide), hlt, beq_true he, hs2, hs⟩

end CFSG.KC.E64CCSound

end

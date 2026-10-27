module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructSylow

public section

namespace CFSG.OddStandard.AltStdSmall4.N0

open Subgroup Equiv Equiv.Perm AltStdCycTwo

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

@[expose] def bz (z g : G) : G := g * z * g⁻¹ * z⁻¹

@[expose] def cm (x y : G) : G := x * y * x⁻¹ * y⁻¹

theorem cm_mul_left (x x' y : G) : cm (x * x') y = x * cm x' y * x⁻¹ * cm x y := by
  simp only [cm]; group

theorem cm_mul_right (x y y' : G) : cm x (y * y') = cm x y * (y * cm x y' * y⁻¹) := by
  simp only [cm]; group

theorem cm_inv (x y : G) : (cm x y)⁻¹ = cm y x := by
  simp only [cm]; group

theorem cm_self (x : G) : cm x x = 1 := by simp [cm]

theorem cm_conj (g x y : G) : cm (g * x * g⁻¹) (g * y * g⁻¹) = g * cm x y * g⁻¹ := by
  simp only [cm]; group

section Setup

variable [Finite G] {Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
  (hn : 8 ≤ n) (c : Config G L Q n θ z)
  (hF : ∃ g ∈ N0 θ hn z, g * z * g⁻¹ = z * w θ hn)
  {P O : Subgroup G} {s : G} (hS : SetupData θ hn z P O s)

include c

theorem bz_mem_E {g : G} (hg : g ∈ N0 θ hn z) : bz z g ∈ E θ hn := comm_z_mem_E hn c hg

omit c in
theorem bz_eq_one_iff (g : G) : bz z g = 1 ↔ g * z = z * g := by
  rw [bz]
  constructor
  · intro h
    calc g * z = g * z * g⁻¹ * z⁻¹ * (z * g) := by group
      _ = z * g := by rw [h, one_mul]
  · intro h
    rw [h]
    group

theorem bz_mul {x y : G} (hx : x ∈ D0 θ hn z) (hy : y ∈ D0 θ hn z) :
    bz z (x * y) = bz z x * bz z y := by
  have hu := bz_mem_E hn c (Subgroup.mem_inf.1 hy).1
  have hv := bz_mem_E hn c (Subgroup.mem_inf.1 hx).1
  have hxu : x * bz z y = bz z y * x :=
    ((mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2) _ hu).symm
  have huv := E_comm hn c hu hv
  calc bz z (x * y) = x * bz z y * (z * x⁻¹ * z⁻¹) := by simp only [bz]; group
    _ = bz z y * x * (z * x⁻¹ * z⁻¹) := by rw [hxu]
    _ = bz z y * bz z x := by simp only [bz]; group
    _ = bz z x * bz z y := huv

theorem bz_conj_of_comm {g : G} (hg : g * z = z * g) (x : G) :
    bz z (g * x * g⁻¹) = g * bz z x * g⁻¹ := by
  have hg' : g⁻¹ * z * g = z := by rw [mul_assoc, ← hg]; group
  calc bz z (g * x * g⁻¹) = g * x * (g⁻¹ * z * g) * x⁻¹ * g⁻¹ * z⁻¹ := by simp only [bz]; group
    _ = g * x * z * x⁻¹ * (g⁻¹ * z⁻¹ * g) * g⁻¹ := by rw [hg']; group
    _ = g * bz z x * g⁻¹ := by
        have : g⁻¹ * z⁻¹ * g = z⁻¹ := by
          rw [show g⁻¹ * z⁻¹ * g = (g⁻¹ * z * g)⁻¹ by group, hg']
        rw [this]; simp only [bz]; group

omit c in
theorem bz_of_comm {g : G} (hg : g * z = z * g) : bz z g = 1 := by
  rw [bz, hg]; group

theorem bz_inv {x : G} (hx : x ∈ D0 θ hn z) : bz z x⁻¹ = (bz z x)⁻¹ := by
  have h := bz_mul hn c hx (inv_mem hx)
  rw [mul_inv_cancel, show bz z (1 : G) = 1 by simp [bz]] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem z_mul_eps_not_mem_E (k : Fin 8) : z * eps θ hn k ∉ E θ hn := by
  intro h
  obtain ⟨l, hl⟩ := (mem_E_iff θ hn _).1 h
  apply z_not_mem_L c
  have : z = eps θ hn l * eps θ hn k := by
    rw [← hl, mul_assoc, eps_mul_self, mul_one]
  rw [this]
  exact mul_mem (eps_mem_L θ hn l) (eps_mem_L θ hn k)

theorem B0_mul_mem_E_iff {x y : G} (hx : x ∈ B0 θ hn z) (hy : y ∈ B0 θ hn z) :
    x * y ∈ E θ hn ↔ (x ∈ E θ hn ↔ y ∈ E θ hn) := by
  obtain ⟨i, rfl | rfl⟩ := (mem_B0_iff hn c x).1 hx <;>
    obtain ⟨j, rfl | rfl⟩ := (mem_B0_iff hn c y).1 hy
  · simp only [eps_mul, eps_mem_E]
  · have h1 : eps θ hn i * (z * eps θ hn j) = z * eps θ hn (i ^^^ j) := by
      rw [← mul_assoc, eps_comm_z hn c, mul_assoc, eps_mul]
    rw [h1]
    simp only [eps_mem_E, true_iff]
    exact ⟨fun h => absurd h (z_mul_eps_not_mem_E hn c _),
      fun h => absurd h (z_mul_eps_not_mem_E hn c _)⟩
  · have h1 : z * eps θ hn i * eps θ hn j = z * eps θ hn (i ^^^ j) := by
      rw [mul_assoc, eps_mul]
    rw [h1]
    simp only [eps_mem_E, iff_true]
    exact ⟨fun h => absurd h (z_mul_eps_not_mem_E hn c _),
      fun h => absurd h (z_mul_eps_not_mem_E hn c _)⟩
  · have h1 : z * eps θ hn i * (z * eps θ hn j) = eps θ hn (i ^^^ j) := by
      rw [show z * eps θ hn i * (z * eps θ hn j) = z * (eps θ hn i * z) * eps θ hn j by group,
        eps_comm_z hn c, show z * (z * eps θ hn i) * eps θ hn j = (z * z) * (eps θ hn i *
          eps θ hn j) by group, c.ot.cyc.mul_self, one_mul, eps_mul]
    rw [h1]
    simp only [eps_mem_E, true_iff]
    exact ⟨fun h => absurd h (z_mul_eps_not_mem_E hn c _),
      fun h => absurd h (z_mul_eps_not_mem_E hn c _)⟩

include hS

theorem P_le_N0 : P ≤ N0 θ hn z := fun _ hx => (Subgroup.mem_inf.1 (hS.P_le hx)).1

theorem P_comm_eps {p : G} (hp : p ∈ P) (i : Fin 8) : p * eps θ hn i = eps θ hn i * p :=
  (mem_centralizer_E_iff θ hn p).1 (Subgroup.mem_inf.1 (hS.P_le hp)).2 i

theorem P_comm_E {p : G} (hp : p ∈ P) {e : G} (he : e ∈ E θ hn) : p * e = e * p := by
  obtain ⟨i, rfl⟩ := (mem_E_iff θ hn e).1 he
  exact P_comm_eps hn c hS hp i

theorem conj_s_mem {p : G} (hp : p ∈ P) : s * p * s⁻¹ ∈ P :=
  (mem_normalizer_iff.1 hS.s_norm p).1 hp

theorem conj_s_pow_mem (k : ℕ) {p : G} (hp : p ∈ P) : s ^ k * p * (s ^ k)⁻¹ ∈ P :=
  (mem_normalizer_iff.1 (pow_mem hS.s_norm k) p).1 hp

theorem s_pow_comm_z (k : ℕ) : s ^ k * z = z * s ^ k := (Commute.pow_left hS.s_comm k).eq

theorem s_pow_conj_eps (k : ℕ) (i : Fin 8) :
    s ^ k * eps θ hn i * (s ^ k)⁻¹ = eps θ hn ((mPerm ^ k) i) :=
  pow_conj_eps θ hn hS.s_conj k i

theorem P_mem_B0_of_comm {p : G} (hp : p ∈ P) (hpz : p * z = z * p) : p ∈ B0 θ hn z := by
  have hpC : p ∈ C0 θ hn z := (mem_C0_iff hn c p).2 ⟨fun i => P_comm_eps hn c hS hp i, hpz⟩
  obtain ⟨k, hk⟩ := hS.P_pgroup ⟨p, hp⟩
  have : p ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact mem_B0_of_two_pow hn c hpC this

theorem P_inv_mul_mem_B0 {p q : G} (hp : p ∈ P) (hq : q ∈ P) (h : bz z p = bz z q) :
    p⁻¹ * q ∈ B0 θ hn z := by
  apply P_mem_B0_of_comm hn c hS (mul_mem (inv_mem hp) hq)
  rw [← bz_eq_one_iff, bz_mul hn c (inv_mem (hS.P_le hp)) (hS.P_le hq)]
  have h1 : bz z p⁻¹ * bz z p = 1 := by
    rw [← bz_mul hn c (inv_mem (hS.P_le hp)) (hS.P_le hp), inv_mul_cancel, bz]; group
  rw [← h, h1]

include hF in
theorem P_trans (j : Fin 8) : ∃ p ∈ P, bz z p = eps θ hn j := by
  obtain ⟨d, hd, hdz⟩ := exists_D0_conj_z_eq hn c hF j
  obtain ⟨p, hp, o, ho, rfl⟩ := hS.decomp d hd
  have hoz : o * z = z * o := ((mem_C0_iff hn c o).1 (hS.O_le ho)).2
  refine ⟨p, hp, ?_⟩
  have h1 : p * z * p⁻¹ = z * eps θ hn j := by
    rw [← hdz]
    calc p * z * p⁻¹ = p * (o * z * o⁻¹) * p⁻¹ := by rw [hoz]; group
      _ = p * o * z * (p * o)⁻¹ := by group
  rw [bz, h1, ← eps_comm_z hn c j, mul_inv_cancel_right]

omit hS in
theorem forall_of_gen {X : Subgroup G} {K : Set G} (hXN : X ≤ D0 θ hn z) (hKX : K ⊆ X)
    (hK : ∀ x ∈ X, ∀ y ∈ X, bz z x = bz z y → x⁻¹ * y ∈ K)
    {g₀ g₁ g₂ : G} (h₀ : g₀ ∈ X) (h₁ : g₁ ∈ X) (h₂ : g₂ ∈ X)
    (hb₀ : bz z g₀ = eps θ hn 1) (hb₁ : bz z g₁ = eps θ hn 2) (hb₂ : bz z g₂ = eps θ hn 4)
    (F : G → Prop) (hFK : ∀ x ∈ K, F x) (hFmul : ∀ x ∈ X, ∀ y ∈ X, F x → F y → F (x * y))
    (hF₀ : F g₀) (hF₁ : F g₁) (hF₂ : F g₂) (hF1 : F 1) : ∀ p ∈ X, F p := by
  intro p hp
  obtain ⟨j, hj⟩ := (mem_E_iff θ hn _).1 (bz_mem_E hn c (Subgroup.mem_inf.1 (hXN hp)).1)
  set a : G := if j.val % 2 = 1 then g₀ else 1 with ha
  set b : G := if (j.val / 2) % 2 = 1 then g₁ else 1 with hb
  set d : G := if (j.val / 4) % 2 = 1 then g₂ else 1 with hd
  have haX : a ∈ X := by rw [ha]; split_ifs; exacts [h₀, one_mem _]
  have hbX : b ∈ X := by rw [hb]; split_ifs; exacts [h₁, one_mem _]
  have hdX : d ∈ X := by rw [hd]; split_ifs; exacts [h₂, one_mem _]
  have hFa : F a := by rw [ha]; split_ifs; exacts [hF₀, hF1]
  have hFb : F b := by rw [hb]; split_ifs; exacts [hF₁, hF1]
  have hFd : F d := by rw [hd]; split_ifs; exacts [hF₂, hF1]
  have hba : bz z a = eps θ hn (if j.val % 2 = 1 then 1 else 0) := by
    rw [ha]; split_ifs
    · exact hb₀
    · rw [eps_zero, bz]; group
  have hbb : bz z b = eps θ hn (if (j.val / 2) % 2 = 1 then 2 else 0) := by
    rw [hb]; split_ifs
    · exact hb₁
    · rw [eps_zero, bz]; group
  have hbd : bz z d = eps θ hn (if (j.val / 4) % 2 = 1 then 4 else 0) := by
    rw [hd]; split_ifs
    · exact hb₂
    · rw [eps_zero, bz]; group
  have habd : a * b * d ∈ X := mul_mem (mul_mem haX hbX) hdX
  have hw : bz z (a * b * d) = bz z p := by
    rw [bz_mul hn c (hXN (mul_mem haX hbX)) (hXN hdX), bz_mul hn c (hXN haX) (hXN hbX),
      hba, hbb, hbd, eps_mul, eps_mul, hj]
    have hidx : ∀ j : Fin 8, (((if j.val % 2 = 1 then 1 else 0) ^^^
        (if (j.val / 2) % 2 = 1 then 2 else 0)) ^^^ (if (j.val / 4) % 2 = 1 then 4 else 0) :
          Fin 8) = j := by decide
    rw [hidx]
  have hk := hK _ habd _ hp hw
  have hp' : p = a * b * d * ((a * b * d)⁻¹ * p) := by group
  rw [hp']
  exact hFmul _ habd _ (hKX hk) (hFmul _ (mul_mem haX hbX) _ hdX (hFmul _ haX _ hbX hFa hFb) hFd)
    (hFK _ hk)

theorem cm_mem_P {p q : G} (hp : p ∈ P) (hq : q ∈ P) : cm p q ∈ P := by
  rw [cm]
  exact mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq)

theorem cm_mem_B0 {p q : G} (hp : p ∈ P) (hq : q ∈ P) : cm p q ∈ B0 θ hn z := by
  apply P_mem_B0_of_comm hn c hS (cm_mem_P hn c hS hp hq)
  rw [← bz_eq_one_iff]
  have hpD := hS.P_le hp
  have hqD := hS.P_le hq
  rw [cm, bz_mul hn c (mul_mem (mul_mem hpD hqD) (inv_mem hpD)) (inv_mem hqD),
    bz_mul hn c (mul_mem hpD hqD) (inv_mem hpD), bz_mul hn c hpD hqD, bz_inv hn c hpD,
    bz_inv hn c hqD]
  have hE := E_comm hn c (bz_mem_E hn c (P_le_N0 hn c hS hp))
    (bz_mem_E hn c (P_le_N0 hn c hS hq))
  rw [hE]
  group

theorem conj_P_mem_B0 {p : G} (hp : p ∈ P) {x : G} (hx : x ∈ B0 θ hn z) :
    p * x * p⁻¹ ∈ B0 θ hn z :=
  (mem_normalizer_iff.1 (P_le_N0 hn c hS hp) x).1 hx

include hF

theorem conj_mem_E_iff {g : G} (hg : g ∈ N0 θ hn z) (x : G) :
    g * x * g⁻¹ ∈ E θ hn ↔ x ∈ E θ hn :=
  ((mem_normalizer_iff.1 (N0_le_normalizer_E hn c hF hg)) x).symm

theorem cc_mul_left {p p' q : G} (hp : p ∈ P) (hp' : p' ∈ P) (hq : q ∈ P) :
    cm (p * p') q ∈ E θ hn ↔ (cm p q ∈ E θ hn ↔ cm p' q ∈ E θ hn) := by
  rw [cm_mul_left, B0_mul_mem_E_iff hn c (conj_P_mem_B0 hn c hS hp (cm_mem_B0 hn c hS hp' hq))
    (cm_mem_B0 hn c hS hp hq), conj_mem_E_iff hn c hF hS (P_le_N0 hn c hS hp)]
  exact iff_comm

omit hF in
theorem cc_symm (p q : G) : cm q p ∈ E θ hn ↔ cm p q ∈ E θ hn := by
  rw [← cm_inv, inv_mem_iff]

omit hF in
theorem cc_B0 {x : G} (hx : x ∈ B0 θ hn z) {q : G} (hq : q ∈ P) : cm x q ∈ E θ hn := by
  obtain ⟨i, rfl | rfl⟩ := (mem_B0_iff hn c x).1 hx
  · rw [cm, ← P_comm_eps hn c hS hq i, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · rw [cm_mul_left, show cm (eps θ hn i) q = 1 by
      rw [cm, ← P_comm_eps hn c hS hq i, mul_inv_cancel_right, mul_inv_cancel],
      mul_one, mul_inv_cancel, one_mul, ← cm_inv]
    exact inv_mem (bz_mem_E hn c (P_le_N0 hn c hS hq))

theorem cc_s {p q : G} : cm (s * p * s⁻¹) (s * q * s⁻¹) ∈ E θ hn ↔ cm p q ∈ E θ hn := by
  rw [cm_conj, conj_mem_E_iff hn c hF hS hS.s_N0]

theorem cc_congr_left {p p' q : G} (hp : p ∈ P) (hp' : p' ∈ P) (hq : q ∈ P)
    (h : bz z p = bz z p') : cm p q ∈ E θ hn ↔ cm p' q ∈ E θ hn := by
  have hx := P_inv_mul_mem_B0 hn c hS hp hp' h
  have : p' = p * (p⁻¹ * p') := by group
  rw [this, cc_mul_left hn c hF hS hp (hS.B0_le hx) hq]
  simp only [cc_B0 hn c hS hx hq, iff_true]

theorem cm_mem_E {p q : G} (hp : p ∈ P) (hq : q ∈ P) : cm p q ∈ E θ hn := by
  obtain ⟨p₀, hp₀, hb₀⟩ := P_trans hn c hF hS 1
  set pk : ℕ → G := fun k => s ^ k * p₀ * (s ^ k)⁻¹ with hpk
  have hpkP : ∀ k, pk k ∈ P := fun k => conj_s_pow_mem hn c hS k hp₀
  have hbk : ∀ k, bz z (pk k) = eps θ hn ((mPerm ^ k) 1) := by
    intro k
    rw [hpk, bz_conj_of_comm c (s_pow_comm_z hn c hS k), hb₀, s_pow_conj_eps hn c hS]
  have hsucc : ∀ k, pk (k + 1) = s * pk k * s⁻¹ := by
    intro k
    simp only [hpk, pow_succ']
    group
  have hshift : ∀ k l, cm (pk (k + 1)) (pk (l + 1)) ∈ E θ hn ↔ cm (pk k) (pk l) ∈ E θ hn := by
    intro k l
    rw [hsucc, hsucc, cc_s hn c hF hS]
  have hadj : ∀ k, cm (pk k) (pk (k + 1)) ∈ E θ hn ↔ cm (pk 0) (pk 1) ∈ E θ hn := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [hshift, ih]
  have hm : ∀ k : Fin 8, (mPerm ^ (k : ℕ)) 1 = ![1, 2, 4, 3, 6, 7, 5, 1] k := by decide
  have hb : ∀ k : Fin 8, bz z (pk k) = eps θ hn (![1, 2, 4, 3, 6, 7, 5, 1] k) :=
    fun k => by rw [hbk, hm]
  have hb0 : bz z (pk 0) = eps θ hn 1 := hb 0
  have hb1 : bz z (pk 1) = eps θ hn 2 := hb 1
  have hb2 : bz z (pk 2) = eps θ hn 4 := hb 2
  have hb3 : bz z (pk 3) = eps θ hn 3 := hb 3
  have hb6 : bz z (pk 6) = eps θ hn 5 := hb 6
  have hb7 : bz z (pk 7) = eps θ hn 1 := hb 7
  have hD : ∀ k, pk k ∈ D0 θ hn z := fun k => hS.P_le (hpkP k)
  have hb01 : bz z (pk 0 * pk 1) = eps θ hn 3 := by
    rw [bz_mul hn c (hD 0) (hD 1), hb0, hb1, eps_mul]; rfl
  have hb02 : bz z (pk 0 * pk 2) = eps θ hn 5 := by
    rw [bz_mul hn c (hD 0) (hD 2), hb0, hb2, eps_mul]; rfl
  set A := cm (pk 0) (pk 1) ∈ E θ hn with hA
  have hX' : cm (pk 0) (pk 2) ∈ E θ hn := by
    have e1 : cm (pk 2) (pk 3) ∈ E θ hn ↔ A := hadj 2
    have e2 := cc_symm hn c hS (pk 2) (pk 3)
    have e3 := cc_congr_left hn c hF hS (hpkP 3) (mul_mem (hpkP 0) (hpkP 1)) (hpkP 2)
      (by rw [hb3, hb01])
    have e4 := cc_mul_left hn c hF hS (hpkP 0) (hpkP 1) (hpkP 2)
    have e5 : cm (pk 1) (pk 2) ∈ E θ hn ↔ A := hadj 1
    have key : A ↔ (cm (pk 0) (pk 2) ∈ E θ hn ↔ A) :=
      e1.symm.trans (e2.symm.trans (e3.trans (e4.trans (iff_congr Iff.rfl e5))))
    by_cases hA : A
    · exact (key.1 hA).2 hA
    · by_contra hX
      exact hA (key.2 ⟨fun h => absurd h hX, fun h => absurd h hA⟩)
  have hA' : A := by
    have e1 : cm (pk 6) (pk 7) ∈ E θ hn ↔ A := hadj 6
    have e2 := cc_congr_left hn c hF hS (hpkP 6) (mul_mem (hpkP 0) (hpkP 2)) (hpkP 7)
      (by rw [hb6, hb02])
    have e3 := cc_mul_left hn c hF hS (hpkP 0) (hpkP 2) (hpkP 7)
    have e4 := cc_symm hn c hS (pk 0) (pk 7)
    have e5 := cc_congr_left hn c hF hS (hpkP 7) (hpkP 0) (hpkP 0) (by rw [hb7, hb0])
    have e6 := cc_symm hn c hS (pk 2) (pk 7)
    have e7 := cc_congr_left hn c hF hS (hpkP 7) (hpkP 0) (hpkP 2) (by rw [hb7, hb0])
    have h00 : cm (pk 0) (pk 0) ∈ E θ hn := by rw [cm_self]; exact one_mem _
    have h07 : cm (pk 0) (pk 7) ∈ E θ hn := e4.1 (e5.2 h00)
    have h27 : cm (pk 2) (pk 7) ∈ E θ hn := e6.1 (e7.2 hX')
    exact e1.1 (e2.2 (e3.2 (iff_of_true h07 h27)))
  have h12 : cm (pk 1) (pk 2) ∈ E θ hn := (show cm (pk 1) (pk 2) ∈ E θ hn ↔ A from hadj 1).2 hA'
  have h02 : cm (pk 0) (pk 2) ∈ E θ hn := hX'
  have hgen := forall_of_gen hn c hS.P_le (fun x hx => hS.B0_le hx)
    (fun x hx y hy h => P_inv_mul_mem_B0 hn c hS hx hy h) (hpkP 0) (hpkP 1) (hpkP 2) hb0 hb1 hb2
  have hstep1 : ∀ i : Fin 3, ∀ p ∈ P, cm p (pk i) ∈ E θ hn := by
    intro i
    refine hgen (fun p => cm p (pk i) ∈ E θ hn) (fun x hx => cc_B0 hn c hS hx (hpkP i))
      (fun x hx y hy h1 h2 => (cc_mul_left hn c hF hS hx hy (hpkP i)).2 (iff_of_true h1 h2))
      ?_ ?_ ?_ (by rw [cm, one_mul, inv_one, mul_one, mul_inv_cancel]; exact one_mem _)
    all_goals
      fin_cases i
      all_goals first
        | exact (by rw [cm_self]; exact one_mem _)
        | exact hA'
        | exact h12
        | exact h02
        | exact (cc_symm hn c hS _ _).2 hA'
        | exact (cc_symm hn c hS _ _).2 h12
        | exact (cc_symm hn c hS _ _).2 h02
  have hstep2 : ∀ q ∈ P, cm p q ∈ E θ hn := by
    refine hgen (fun q => cm p q ∈ E θ hn)
      (fun x hx => (cc_symm hn c hS _ _).1 (cc_B0 hn c hS hx hp))
      (fun x hx y hy h1 h2 => (cc_symm hn c hS _ _).1 ((cc_mul_left hn c hF hS hx hy hp).2
        (iff_of_true ((cc_symm hn c hS _ _).2 h1) ((cc_symm hn c hS _ _).2 h2))))
      (hstep1 0 p hp) (hstep1 1 p hp) (hstep1 2 p hp)
      (by rw [cm, mul_one, inv_one, mul_one, mul_inv_cancel]; exact one_mem _)
  exact hstep2 q hq

end Setup

end CFSG.OddStandard.AltStdSmall4.N0

module

public import Certificates.Data.Kernel.Pk442010
public import CFSG.Certificates.Kernel.A45Cls.PockSound
public import CFSG.Certificates.Kernel.OrbFindSound
public import CFSG.Certificates.Kernel.PermCent.OrbGroup
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KC.Pk442010

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.EnumSound

local notation "P45" => Equiv.Perm (Fin 45)

local notation "PR" => PRep 45 6

theorem hn45' : (45 : Nat) < 2 ^ 32 := by norm_num

theorem lnK_lt (w L k : Nat) : lnK w L k < 2 ^ w := by
  unfold lnK
  rw [show Nat.mul w k = w * k from rfl, PK.fld_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem lnK_shift (w L k : Nat) : Nat.shiftRight (lnK w L k) w = 0 :=
  (PK.shiftRight_eq_zero_iff _ _).2 (lnK_lt w L k)

variable {gp gq gr gs gt : P45}

theorem prep_pc {p q : Nat} (hp : PR p gp) (hq : PR q gq) : PR (pc p q) (gp * gq) :=
  prep_pcomp hn45' hp hq

theorem e2_sound {r p q : Nat} (h : e2 r p q = true) (hr : PR r gr) (hp : PR p gp)
    (hq : PR q gq) : gr = gp * gq :=
  prep_unique hr (eq2_prep h hp hq)

theorem e2_of_eq {r p q : Nat} (hr : PR r gr) (hp : PR p gp) (hq : PR q gq) (e : gr = gp * gq) :
    e2 r p q = true := by
  unfold e2
  rw [eq2_iff]
  intro i hi
  rw [prep_at hr hi, prep_at hq hi, hp (gq ⟨i, hi⟩), e]
  rfl

theorem e22_of_eq {p q r s : Nat} (hp : PR p gp) (hq : PR q gq) (hr : PR r gr) (hs : PR s gs)
    (e : gp * gq = gr * gs) : e22 p q r s = true := by
  unfold e22 eq22
  rw [PK.allN_iff]
  intro i hi
  have h1 := congrArg (fun g : P45 => ((g ⟨i, hi⟩ : Fin 45) : Nat)) e
  simp only [Equiv.Perm.mul_apply] at h1
  rw [prep_at hq hi, hp (gq ⟨i, hi⟩), prep_at hs hi, hr (gs ⟨i, hi⟩), h1]
  exact Nat.beq_refl _

theorem e32_sound {p q s r t : Nat} (h : e32 p q s r t = true) (hp : PR p gp) (hq : PR q gq)
    (hs : PR s gs) (hr : PR r gr) (ht : PR t gt) : gp * gq * gs = gr * gt := by
  unfold e32 at h
  rw [PK.allN_iff] at h
  refine Equiv.ext fun x => Fin.ext ?_
  have e := Nat.eq_of_beq_eq_true (h x x.2)
  unfold ev at e
  rw [hs x, hq (gs x), hp (gq (gs x)), ht x, hr (gt x)] at e
  exact e

theorem e23_of_eq {p q r s t : Nat} (hp : PR p gp) (hq : PR q gq) (hr : PR r gr) (hs : PR s gs)
    (ht : PR t gt) (e : gp * gq = gr * gs * gt) : e23 p q r s t = true := by
  unfold e23
  rw [PK.allN_iff]
  intro i hi
  have h1 := congrArg (fun g : P45 => ((g ⟨i, hi⟩ : Fin 45) : Nat)) e
  simp only [Equiv.Perm.mul_apply] at h1
  unfold ev
  rw [prep_at hq hi, hp (gq ⟨i, hi⟩), prep_at ht hi, hs (gt ⟨i, hi⟩), hr (gs (gt ⟨i, hi⟩)), h1]
  exact Nat.beq_refl _

theorem invP_sound {p q : Nat} (h : invP p q = true) (hp : PR p gp) (hq : PR q gq) :
    gp * gq = 1 := by
  unfold invP at h
  rw [PK.allN_iff] at h
  refine Equiv.ext fun x => Fin.ext ?_
  have e := Nat.eq_of_beq_eq_true (h x x.2)
  unfold ev at e
  rw [hq x, hp (gq x)] at e
  exact e

theorem cube1_iff {p : Nat} (hp : PR p gp) : cube1 p = true ↔ gp ^ 3 = 1 := by
  rw [← OrbFind.pow_three']
  unfold cube1
  rw [PK.allN_iff]
  constructor
  · intro h
    refine Equiv.ext fun x => Fin.ext ?_
    have e := Nat.eq_of_beq_eq_true (h x x.2)
    unfold ev at e
    rw [hp x, hp (gp x), hp (gp (gp x))] at e
    exact e
  · intro e i hi
    have h1 := congrArg (fun g : P45 => ((g ⟨i, hi⟩ : Fin 45) : Nat)) e
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h1
    unfold ev
    rw [prep_at hp hi, hp (gp ⟨i, hi⟩), hp (gp (gp ⟨i, hi⟩)), h1]
    exact Nat.beq_refl _

theorem pow9_iff {p : Nat} (hp : PR p gp) : pow9 p = true ↔ gp ^ 9 = 1 := by
  unfold pow9
  rw [PK.strictB_eq, cube1_iff (prep_pc hp (prep_pc hp hp)), OrbFind.pow_three', ← pow_mul]

theorem isId_iff {p : Nat} (hp : PR p gp) : isId p = true ↔ gp = 1 := isIdK_iff hp

theorem beq_sound {p q : Nat} (h : Nat.beq p q = true) (hp : PR p gp) (hq : PR q gq) : gp = gq :=
  prep_unique hp (Nat.eq_of_beq_eq_true h ▸ hq)

variable {N csW : Nat} {T S R B Q Q1 Q2 : Nat → Nat} {c ρ β q q1 q2 : Nat → P45}

theorem isCode_spec {d : Nat} (h : isCode csW d = true) : ∃ i < 24, csAt csW i = d := by
  obtain ⟨i, hi, e⟩ := exN_spec h
  exact ⟨i, hi, Nat.eq_of_beq_eq_true e⟩

theorem homK_spec (h : homK csW R = true) (hR : ∀ i < 24, PR (R (csAt csW i)) (ρ (csAt csW i))) :
    ∀ i < 24, ∀ j < 24, (∃ k < 24, csAt csW k = mulC (csAt csW i) (csAt csW j)) ∧
      ρ (mulC (csAt csW i) (csAt csW j)) = ρ (csAt csW i) * ρ (csAt csW j) := by
  simp only [homK, PK.allN_iff, PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true] at h
  intro i hi j hj
  obtain ⟨h1, h2⟩ := h i hi j hj
  obtain ⟨k, hk, e⟩ := isCode_spec h1
  have hRk := hR k hk
  rw [e] at hRk
  exact ⟨⟨k, hk, e⟩, e2_sound h2 hRk (hR i hi) (hR j hj)⟩

theorem injK_spec (h : injK csW R = true) (hR : ∀ i < 24, PR (R (csAt csW i)) (ρ (csAt csW i))) :
    ∀ i < 24, csAt csW i = 28 ∨ ρ (csAt csW i) ≠ 1 := by
  simp only [injK, PK.allN_iff, PK.strictB_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  intro i hi
  rcases h i hi with h1 | h1
  · exact Or.inl (Nat.eq_of_beq_eq_true h1)
  · refine Or.inr fun e => ?_
    rw [(isId_iff (hR i hi)).2 e] at h1
    exact Bool.false_ne_true h1.symm

theorem memRK_spec (h : memRK N T S csW R = true) : ∀ i < 24, ∃ m < N, T m = R (csAt csW i) :=
  fun i hi => memK_spec (PK.allN_iff.1 h i hi)

theorem hitK_spec {t : Nat} (h : hitK csW R t = true) : ∃ i < 24, R (csAt csW i) = t := by
  obtain ⟨i, hi, e⟩ := exN_spec h
  exact ⟨i, hi, Nat.eq_of_beq_eq_true e⟩

theorem subK_spec {t : Nat} (h : subK N T S Q t = true) (hQ : ∀ j < 8, PR (Q j) (q j)) :
    (∀ j < 8, ∃ m < N, T m = Q j) ∧ (∃ j < 8, q j = 1) ∧ (∃ j < 8, Q j = t) ∧
      (∀ j < 8, ∀ k < 8, ∃ l < 8, q l = q j * q k) ∧ ∀ j < 8, ∃ k < 8, q j * q k = 1 := by
  simp only [subK, Bool.and_eq_true, PK.allN_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun j hj => memK_spec (h1 j hj), ?_, ?_, fun j hj k hk => ?_, fun j hj => ?_⟩
  · obtain ⟨j, hj, e⟩ := exN_spec h2
    exact ⟨j, hj, (isId_iff (hQ j hj)).1 e⟩
  · obtain ⟨j, hj, e⟩ := exN_spec h3
    exact ⟨j, hj, Nat.eq_of_beq_eq_true e⟩
  · obtain ⟨l, hl, e⟩ := exN_spec (h4 j hj k hk)
    exact ⟨l, hl, e2_sound e (hQ l hl) (hQ j hj) (hQ k hk)⟩
  · obtain ⟨k, hk, e⟩ := exN_spec (h5 j hj)
    exact ⟨k, hk, invP_sound e (hQ j hj) (hQ k hk)⟩

theorem centK_spec (h : centK N T csW R Q = true)
    (hR : ∀ i < 24, PR (R (csAt csW i)) (ρ (csAt csW i))) (hQ : ∀ j < 8, PR (Q j) (q j))
    (hT : ∀ k < N, PR (T k) (c k)) :
    (∀ i < 24, ∀ j < 8, ρ (csAt csW i) * q j = q j * ρ (csAt csW i)) ∧
      ∀ k < N, (∀ j < 8, c k * q j = q j * c k) → ∃ i < 24, ρ (csAt csW i) = c k := by
  simp only [centK, Bool.and_eq_true, PK.allN_iff, PK.strictB_eq, Bool.or_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi j hj => eq22_sound (h1 i hi j hj) (hR i hi) (hQ j hj) (hQ j hj) (hR i hi),
    fun k hk hc => ?_⟩
  rcases h2 k hk with h3 | h3
  · obtain ⟨j, hj, e⟩ := exN_spec h3
    rw [e22_of_eq (hT k hk) (hQ j hj) (hQ j hj) (hT k hk) (hc j hj)] at e
    exact absurd e (by decide)
  · obtain ⟨i, hi, e⟩ := exN_spec h3
    exact ⟨i, hi, beq_sound e (hR i hi) (hT k hk)⟩

theorem conjK_spec {g : Nat} {g0 : P45} (h : conjK csW R B g = true)
    (hR : ∀ i < 24, PR (R (csAt csW i)) (ρ (csAt csW i))) (hg : PR g g0) :
    g0 * g0 = 1 ∧ ∀ i < 24, PR (B (csAt csW i)) (g0 * ρ (csAt csW i) * g0) := by
  simp only [conjK, Bool.and_eq_true, PK.allN_iff, PK.strictB_eq] at h
  exact ⟨invP_sound h.1 hg hg, fun i hi => eq3_prep (h.2 i hi) hg (hR i hi) hg⟩

theorem commK_spec (h : commK csW R B = true)
    (hR : ∀ i < 24, PR (R (csAt csW i)) (ρ (csAt csW i)))
    (hB : ∀ i < 24, PR (B (csAt csW i)) (β (csAt csW i))) :
    (∀ i < 24, ∀ j < 24, ρ (csAt csW i) * β (csAt csW j) = β (csAt csW j) * ρ (csAt csW i)) ∧
      ∃ i < 24, ∀ j < 24, R (csAt csW i) ≠ B (csAt csW j) := by
  simp only [commK, Bool.and_eq_true, PK.allN_iff, PK.strictB_eq, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi j hj => eq22_sound (h1 i hi j hj) (hR i hi) (hB j hj) (hB j hj) (hR i hi), ?_⟩
  obtain ⟨i, hi, e⟩ := exN_spec h2
  rw [PK.allN_iff] at e
  refine ⟨i, hi, fun j hj he => ?_⟩
  have e' := e j hj
  rw [he, Nat.beq_refl] at e'
  exact absurd e' (by decide)

theorem nsK_spec {t : Nat} {t0 : P45} (h : nsK N T Q t = true) (hT : ∀ k < N, PR (T k) (c k))
    (hQ : ∀ j < 8, PR (Q j) (q j)) (ht : PR t t0) :
    ∀ k < N, c k ^ 3 = 1 → ¬ (∀ j < 8, c k * q j = q j * c k) →
      ∀ j < 8, ∃ l < 8, q j * q l * c k = c k * q l ∨ t0 * q j * q l * c k = c k * q l := by
  simp only [nsK, PK.allN_iff, PK.strictB_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  intro k hk h3 hnc j hj
  rcases h k hk with (h1 | h1) | h1
  · rw [(cube1_iff (hT k hk)).2 h3] at h1
    exact absurd h1 (by decide)
  · exact absurd (fun j hj => eq22_sound (h1 j hj) (hT k hk) (hQ j hj) (hQ j hj) (hT k hk)) hnc
  · obtain ⟨l, hl, e⟩ := exN_spec (h1 j hj)
    rw [Bool.or_eq_true] at e
    refine ⟨l, hl, ?_⟩
    rcases e with e | e
    · exact Or.inl (e32_sound e (hQ j hj) (hQ l hl) (hT k hk) (hT k hk) (hQ l hl))
    · exact Or.inr (e32_sound e (prep_pc ht (hQ j hj)) (hQ l hl) (hT k hk) (hT k hk) (hQ l hl))

theorem lnK6_div {P a : Nat} : Nat.div (lnK 6 P a) 8 < 8 := by
  have := lnK_lt 6 P a
  change lnK 6 P a / 8 < 8
  omega

theorem lnK6_mod {P a : Nat} : Nat.mod (lnK 6 P a) 8 < 8 := Nat.mod_lt _ (by norm_num)

theorem prodK_spec {P : Nat} (h : prodK Q1 Q2 P = true) (hQ1 : ∀ j < 8, PR (Q1 j) (q1 j))
    (hQ2 : ∀ j < 8, PR (Q2 j) (q2 j)) :
    ∀ a < 32, ∀ b < a, q1 (Nat.div (lnK 6 P a) 8) * q2 (Nat.mod (lnK 6 P a) 8) ≠
      q1 (Nat.div (lnK 6 P b) 8) * q2 (Nat.mod (lnK 6 P b) 8) := by
  simp only [prodK, PK.allN_iff, PK.strictB_eq, Bool.not_eq_true'] at h
  intro a ha b hb e
  have e' := e22_of_eq (hQ1 _ lnK6_div) (hQ2 _ lnK6_mod) (hQ1 _ lnK6_div) (hQ2 _ lnK6_mod) e
  rw [h a ha b hb] at e'
  exact absurd e' (by decide)

theorem eWK_spec {W : Nat} (h : eWK N T csW R B W = true)
    (hR : ∀ i < 24, PR (R (csAt csW i)) (ρ (csAt csW i)))
    (hB : ∀ i < 24, PR (B (csAt csW i)) (β (csAt csW i))) (hT : ∀ k < N, PR (T k) (c k)) :
    ∀ k < N, eL W k ≠ 0 → ∃ i < 24, ∃ j < 24, c k = ρ (csAt csW i) * β (csAt csW j) := by
  simp only [eWK, PK.allN_iff, PK.strictB_eq, Bool.or_eq_true, PK.bAnd_eq,
    Bool.and_eq_true] at h
  intro k hk hne
  rcases h k hk with h1 | ⟨h1, h2, h3⟩
  · exact absurd (Nat.eq_of_beq_eq_true h1) hne
  · obtain ⟨i, hi, ei⟩ := isCode_spec h1
    obtain ⟨j, hj, ej⟩ := isCode_spec h2
    have hRi := hR i hi
    have hBj := hB j hj
    rw [ei] at hRi
    rw [ej] at hBj
    refine ⟨i, hi, j, hj, ?_⟩
    rw [ei, ej]
    exact e2_sound h3 (hT k hk) hRi hBj

theorem eAllK_spec {W : Nat} (h : eAllK N T S csW R B W = true)
    (hR : ∀ i < 24, PR (R (csAt csW i)) (ρ (csAt csW i)))
    (hB : ∀ i < 24, PR (B (csAt csW i)) (β (csAt csW i))) (hT : ∀ k < N, PR (T k) (c k)) :
    ∀ i < 24, ∀ j < 24, ∃ m < N, c m = ρ (csAt csW i) * β (csAt csW j) ∧ eL W m ≠ 0 := by
  simp only [eAllK, PK.allN_iff, PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  intro i hi j hj
  obtain ⟨h1, h2, h3⟩ := h i hi j hj
  have hm := Nat.blt_eq.mp h1
  refine ⟨_, hm, prep_unique (hT _ hm) ?_, fun e => ?_⟩
  · rw [Nat.eq_of_beq_eq_true h2]
    exact prep_pc (hR i hi) (hB j hj)
  · rw [e, Nat.beq_refl] at h3
    exact absurd h3 (by decide)

theorem e9K_spec {W : Nat} (h : e9K N T W = true) (hT : ∀ k < N, PR (T k) (c k)) :
    ∀ k < N, c k ^ 9 = 1 → eL W k ≠ 0 := by
  simp only [e9K, PK.allN_iff, Bool.or_eq_true, Bool.not_eq_true'] at h
  intro k hk h9 e
  rcases h k hk with h1 | h1
  · rw [e, Nat.beq_refl] at h1
    exact absurd h1 (by decide)
  · rw [(pow9_iff (hT k hk)).2 h9] at h1
    exact absurd h1 (by decide)

theorem eGK_spec {g W : Nat} {g0 : P45} (h : eGK N T S g W = true) (hT : ∀ k < N, PR (T k) (c k))
    (hg : PR g g0) : ∀ k < N, ∃ m < N, c m = c k * g0 ∧ (eL W m ≠ 0 ↔ eL W k = 0) := by
  simp only [eGK, PK.allN_iff, PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true] at h
  intro k hk
  obtain ⟨h1, h2, h3⟩ := h k hk
  have hm := Nat.blt_eq.mp h1
  refine ⟨_, hm, prep_unique (hT _ hm) ?_, ?_⟩
  · rw [Nat.eq_of_beq_eq_true h2]
    exact prep_pc (hT k hk) hg
  · cases hk0 : Nat.beq (eL W k) 0
    · rw [hk0] at h3
      have e1 := Nat.eq_of_beq_eq_true h3
      have e2 : eL W k ≠ 0 := fun e => by rw [e, Nat.beq_refl] at hk0; exact absurd hk0 (by decide)
      exact ⟨fun h' => absurd e1 h', fun h' => absurd h' e2⟩
    · rw [hk0] at h3
      have e1 := Nat.eq_of_beq_eq_true hk0
      refine ⟨fun _ => e1, fun _ e => ?_⟩
      change (!Nat.beq (eL W _) 0) = true at h3
      rw [e, Nat.beq_refl] at h3
      exact absurd h3 (by decide)

theorem noOddK_spec {W : Nat} (h : noOddK N T W = true) (hT : ∀ k < N, PR (T k) (c k)) :
    ∀ k < N, c k ≠ 1 → c k ^ 3 = 1 → ∃ s < N, ∃ s' < N, c s * c s' = 1 ∧
      (c k * (c s * c k * c s')) ^ 3 ≠ 1 := by
  simp only [noOddK, PK.allN_iff, PK.strictB_eq, Bool.or_eq_true, Bool.not_eq_true',
    PK.bAnd_eq, Bool.and_eq_true] at h
  intro k hk h1 h3
  rcases h k hk with (h4 | h4) | ⟨-, h5, h6, h7, h8⟩
  · exact absurd ((isId_iff (hT k hk)).1 h4) h1
  · rw [(cube1_iff (hT k hk)).2 h3] at h4
    exact absurd h4 (by decide)
  · have hs := Nat.blt_eq.mp h5
    have hs' := Nat.blt_eq.mp h6
    refine ⟨_, hs, _, hs', invP_sound h7 (hT _ hs) (hT _ hs'), fun e => ?_⟩
    have hp := prep_pc (hT k hk) (prep_pc (hT _ hs) (prep_pc (hT k hk) (hT _ hs')))
    rw [← mul_assoc (c _) (c k)] at hp
    rw [(cube1_iff hp).2 e] at h8
    exact absurd h8 (by decide)

theorem ord9K_spec (h : ord9K N T = true) (hT : ∀ k < N, PR (T k) (c k)) :
    ∀ k < N, c k ^ 9 = 1 → c k ^ 3 = 1 := by
  simp only [ord9K, PK.allN_iff, PK.strictB_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  intro k hk h9
  rcases h k hk with h1 | h1
  · rw [(pow9_iff (hT k hk)).2 h9] at h1
    exact absurd h1 (by decide)
  · exact (cube1_iff (hT k hk)).1 h1

theorem uK_spec {U : Nat} (h : uK N T U = true) (hT : ∀ k < N, PR (T k) (c k)) :
    (∀ a < 12, lnK 7 U a < N) ∧ (∃ k < 12, c (lnK 7 U k) = 1) ∧
      (∀ a < 12, ∀ b < 12, ∃ k < 12, c (lnK 7 U k) = c (lnK 7 U a) * c (lnK 7 U b)) ∧
      (∀ a < 12, ∃ b < 12, c (lnK 7 U a) * c (lnK 7 U b) = 1) ∧
      ∀ k < N, c k ^ 3 = 1 → ∃ j < 12, c (lnK 7 U j) = c k := by
  simp only [uK, Bool.and_eq_true, PK.allN_iff, PK.strictB_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hl : ∀ a < 12, lnK 7 U a < N := fun a ha => Nat.blt_eq.mp (h1 a ha)
  have hU : ∀ a < 12, PR (uAt T U a) (c (lnK 7 U a)) := fun a ha => hT _ (hl a ha)
  refine ⟨hl, ?_, fun a ha b hb => ?_, fun a ha => ?_, fun k hk h3' => ?_⟩
  · obtain ⟨k, hk, e⟩ := exN_spec h3
    exact ⟨k, hk, (isId_iff (hU k hk)).1 e⟩
  · obtain ⟨k, hk, e⟩ := exN_spec (h4 a ha b hb)
    exact ⟨k, hk, e2_sound e (hU k hk) (hU a ha) (hU b hb)⟩
  · obtain ⟨b, hb, e⟩ := exN_spec (h5 a ha)
    exact ⟨b, hb, invP_sound e (hU a ha) (hU b hb)⟩
  · rcases h6 k hk with h7 | h7
    · rw [(cube1_iff (hT k hk)).2 h3'] at h7
      exact absurd h7 (by decide)
    · obtain ⟨j, hj, e⟩ := exN_spec h7
      exact ⟨j, hj, beq_sound e (hU j hj) (hT k hk)⟩

theorem inQ8_spec {x a t ta b ba bt bta : Nat} {gx ga gt' gb : P45}
    (h : inQ8 x a t ta b ba bt bta = true) (hx : PR x gx) (ha : PR a ga) (ht : PR t gt')
    (hta : PR ta (gt' * ga)) (hb : PR b gb) (hba : PR ba (gb * ga)) (hbt : PR bt (gb * gt'))
    (hbta : PR bta (gb * (gt' * ga))) :
    gx ∈ [1, ga, gt', gt' * ga, gb, gb * ga, gb * gt', gb * (gt' * ga)] := by
  simp only [inQ8, Bool.or_eq_true] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact Or.inl ((isId_iff hx).1 h)
  · exact Or.inr (Or.inl (beq_sound h hx ha))
  · exact Or.inr (Or.inr (Or.inl (beq_sound h hx ht)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (beq_sound h hx hta))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (beq_sound h hx hb)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (beq_sound h hx hba))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (beq_sound h hx hbt)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (beq_sound h hx hbta)))))))

theorem pairK_spec {t : Nat} {t0 : P45} (h : pairK N T Q1 Q2 t = true)
    (hT : ∀ k < N, PR (T k) (c k)) (hQ1 : ∀ j < 8, PR (Q1 j) (q1 j))
    (hQ2 : ∀ j < 8, PR (Q2 j) (q2 j)) (ht : PR t t0) :
    ∀ i < N, ∀ j < N, c i * c i = t0 → c j * c j = t0 → c j * c i = t0 * c i * c j →
      (∀ k < 8, q1 k ∈ [1, c i, t0, t0 * c i, c j, c j * c i, c j * t0, c j * (t0 * c i)]) ∨
        ∀ k < 8, q2 k ∈ [1, c i, t0, t0 * c i, c j, c j * c i, c j * t0, c j * (t0 * c i)] := by
  simp only [pairK, PK.allN_iff, PK.strictB_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  intro i hi j hj hii hjj hji
  have ha := hT i hi
  have hb := hT j hj
  rcases h i hi with h1 | h1
  · rw [e2_of_eq ht ha ha hii.symm] at h1
    exact absurd h1 (by decide)
  rcases h1 j hj with (h2 | h2) | h2
  · rw [e2_of_eq ht hb hb hjj.symm] at h2
    exact absurd h2 (by decide)
  · rw [e23_of_eq hb ha ht ha hb hji] at h2
    exact absurd h2 (by decide)
  have hta := prep_pc ht ha
  rcases h2 with h3 | h3
  · exact Or.inl fun k hk => inQ8_spec (h3 k hk) (hQ1 k hk) ha ht hta hb (prep_pc hb ha)
      (prep_pc hb ht) (prep_pc hb hta)
  · exact Or.inr fun k hk => inQ8_spec (h3 k hk) (hQ2 k hk) ha ht hta hb (prep_pc hb ha)
      (prep_pc hb ht) (prep_pc hb hta)

end CFSG.KC.Pk442010

end

module

public import Certificates.Data.Kernel.Fi22Twist.Dj
public import CFSG.Certificates.Kernel.Fi22Twist.PairSound
public import CFSG.Certificates.Kernel.Fi22Twist.LeafSound
public import CFSG.Certificates.Kernel.Common.PcChain

public section

namespace CFSG.KS.Fi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist Subgroup

theorem djK_spec {DF : ℕ → ℕ} {R j : ℕ} (h : djK DF R j = true) :
    (∀ i < 3510,
      ap (rowR R (3 * j)) (ap (rowR R (3 * j)) (ap (rowR R (3 * j)) i)) = i ∧
      ap (rowR R (3 * j + 1)) (ap (rowR R (3 * j + 1)) (ap (rowR R (3 * j + 1)) i)) = i ∧
      ap (rowR R (3 * j + 2)) (ap (rowR R (3 * j + 2)) (ap (rowR R (3 * j + 2)) i)) = i ∧
      ap (rowR R (3 * j)) (ap (rowR R (3 * j + 1)) i) =
        ap (rowR R (3 * j + 1)) (ap (rowR R (3 * j)) i) ∧
      ap (rowR R (3 * j)) (ap (rowR R (3 * j + 2)) i) =
        ap (rowR R (3 * j + 2)) (ap (rowR R (3 * j)) i) ∧
      ap (rowR R (3 * j + 1)) (ap (rowR R (3 * j + 2)) i) =
        ap (rowR R (3 * j + 2)) (ap (rowR R (3 * j + 1)) i)) ∧
    ∀ e < 27, ∀ e' < e, kAp (DF (27 * j + e')) baseKey ≠ kAp (DF (27 * j + e)) baseKey := by
  unfold djK at h
  simp only [strictB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨fun i hi => ?_, fun e he e' he' hq => ?_⟩
  · have r := CFSG.KS.allN_spec h1 i hi
    obtain ⟨a1, r⟩ := (CFSG.KS.bAnd_iff _ _).1 r
    obtain ⟨a2, r⟩ := (CFSG.KS.bAnd_iff _ _).1 r
    obtain ⟨a3, r⟩ := (CFSG.KS.bAnd_iff _ _).1 r
    obtain ⟨a4, r⟩ := (CFSG.KS.bAnd_iff _ _).1 r
    obtain ⟨a5, a6⟩ := (CFSG.KS.bAnd_iff _ _).1 r
    exact ⟨Nat.eq_of_beq_eq_true a1, Nat.eq_of_beq_eq_true a2, Nat.eq_of_beq_eq_true a3,
      Nat.eq_of_beq_eq_true a4, Nat.eq_of_beq_eq_true a5, Nat.eq_of_beq_eq_true a6⟩
  · have e2 := not_tt (CFSG.KS.allN_spec (CFSG.KS.allN_spec h2 e he) e' he')
    have e3 : Nat.beq (kAp (DF (27 * j + e')) baseKey) (kAp (DF (27 * j + e)) baseKey) = true :=
      Eq.mpr Nat.beq_eq hq
    exact absurd (e2.symm.trans e3) Bool.false_ne_true

theorem pt_ext {x y : Equiv.Perm (Fin 3510)}
    (h : ∀ z < 3510, pt (MonoidHom.id _) x z = pt (MonoidHom.id _) y z) : x = y := by
  ext ⟨z, hz⟩
  have e := h z hz
  unfold pt at e
  rw [dif_pos hz, dif_pos hz] at e
  exact e

theorem kAp_base_eq {d d' : ℕ} (h : ∀ z < 3510, ap d z = ap d' z) :
    kAp d baseKey = kAp d' baseKey := by
  have hb : ∀ l < 6, ap d (cg baseKey l) = ap d' (cg baseKey l) := fun l hl => h _ (bp_lt6 l hl)
  unfold kAp
  rw [hb (nat_lit 0) (by decide), hb (nat_lit 1) (by decide), hb (nat_lit 2) (by decide),
    hb (nat_lit 3) (by decide), hb (nat_lit 4) (by decide), hb (nat_lit 5) (by decide)]

theorem pow3_mod {G : Type*} [Monoid G] {x : G} (h : x ^ 3 = 1) (n : ℕ) : x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h, one_pow, mul_one]

theorem dj_card {DF : ℕ → ℕ} {R j : ℕ} {gx gy gz : Equiv.Perm (Fin 3510)}
    (hx : ∀ z < 3510, ap (rowR R (3 * j)) z = pt (MonoidHom.id _) gx z)
    (hy : ∀ z < 3510, ap (rowR R (3 * j + 1)) z = pt (MonoidHom.id _) gy z)
    (hz : ∀ z < 3510, ap (rowR R (3 * j + 2)) z = pt (MonoidHom.id _) gz z)
    (hd : ∀ e < 27, ∃ d ∈ closure ({gx, gy, gz} : Set (Equiv.Perm (Fin 3510))),
      ∀ z < 3510, ap (DF (27 * j + e)) z = pt (MonoidHom.id _) d z)
    (hc : djK DF R j = true) :
    Nat.card (closure ({gx, gy, gz} : Set (Equiv.Perm (Fin 3510)))) = 27 := by
  classical
  obtain ⟨hr, hk⟩ := djK_spec hc
  have cube : ∀ {g : Equiv.Perm (Fin 3510)} {P : ℕ},
      (∀ z < 3510, ap P z = pt (MonoidHom.id _) g z) →
      (∀ i < 3510, ap P (ap P (ap P i)) = i) → g ^ 3 = 1 := by
    intro g P hg h3
    refine pt_ext fun i hi => ?_
    have e := h3 i hi
    rw [hg i hi, hg _ (pt_lt _ g hi), hg _ (pt_lt _ g (pt_lt _ g hi))] at e
    rw [pt_one, pow_three, pt_mul, pt_mul]
    exact e
  have comm : ∀ {g g' : Equiv.Perm (Fin 3510)} {P Q : ℕ},
      (∀ z < 3510, ap P z = pt (MonoidHom.id _) g z) →
      (∀ z < 3510, ap Q z = pt (MonoidHom.id _) g' z) →
      (∀ i < 3510, ap P (ap Q i) = ap Q (ap P i)) → g' * g = g * g' := by
    intro g g' P Q hg hg' hpq
    refine pt_ext fun i hi => ?_
    have e := hpq i hi
    rw [hg' i hi, hg i hi, hg _ (pt_lt _ g' hi), hg' _ (pt_lt _ g hi)] at e
    rw [pt_mul, pt_mul]
    exact e.symm
  have x3 := cube hx fun i hi => (hr i hi).1
  have y3 := cube hy fun i hi => (hr i hi).2.1
  have z3 := cube hz fun i hi => (hr i hi).2.2.1
  have cyx : Commute gy gx := comm hx hy fun i hi => (hr i hi).2.2.2.1
  have czx : Commute gz gx := comm hx hz fun i hi => (hr i hi).2.2.2.2.1
  have czy : Commute gz gy := comm hy hz fun i hi => (hr i hi).2.2.2.2.2
  set C := closure ({gx, gy, gz} : Set (Equiv.Perm (Fin 3510))) with hC
  have mx : gx ∈ C := subset_closure (Set.mem_insert _ _)
  have my : gy ∈ C := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have mz : gz ∈ C := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  let F : Fin 3 × Fin 3 × Fin 3 → Equiv.Perm (Fin 3510) := fun t =>
    gx ^ (t.1 : ℕ) * gy ^ (t.2.1 : ℕ) * gz ^ (t.2.2 : ℕ)
  have h1 : (1 : Equiv.Perm (Fin 3510)) ∈ Set.range F := ⟨(0, 0, 0), by simp [F]⟩
  have hcl : ∀ w ∈ Set.range F, ∀ g ∈ ({gx, gy, gz} : Set (Equiv.Perm (Fin 3510))),
      w * g ∈ Set.range F := by
    rintro _ ⟨⟨a, b, c⟩, rfl⟩ g hg
    rcases hg with hg | hg | hg
    · rw [hg]
      refine ⟨(⟨((a : ℕ) + 1) % 3, Nat.mod_lt _ (by norm_num)⟩, b, c), ?_⟩
      change gx ^ (((a : ℕ) + 1) % 3) * gy ^ (b : ℕ) * gz ^ (c : ℕ) =
        gx ^ (a : ℕ) * gy ^ (b : ℕ) * gz ^ (c : ℕ) * gx
      have c1 : Commute (gy ^ (b : ℕ) * gz ^ (c : ℕ)) gx :=
        (cyx.pow_left _).mul_left (czx.pow_left _)
      rw [← pow3_mod x3, pow_succ]
      simp only [mul_assoc]
      rw [← mul_assoc (gy ^ (b : ℕ)), c1.eq]
    · rw [hg]
      refine ⟨(a, ⟨((b : ℕ) + 1) % 3, Nat.mod_lt _ (by norm_num)⟩, c), ?_⟩
      change gx ^ (a : ℕ) * gy ^ (((b : ℕ) + 1) % 3) * gz ^ (c : ℕ) =
        gx ^ (a : ℕ) * gy ^ (b : ℕ) * gz ^ (c : ℕ) * gy
      rw [← pow3_mod y3, pow_succ]
      simp only [mul_assoc]
      rw [(czy.pow_left (c : ℕ)).eq]
    · have hg' : g = gz := hg
      rw [hg']
      refine ⟨(a, b, ⟨((c : ℕ) + 1) % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      change gx ^ (a : ℕ) * gy ^ (b : ℕ) * gz ^ (((c : ℕ) + 1) % 3) =
        gx ^ (a : ℕ) * gy ^ (b : ℕ) * gz ^ (c : ℕ) * gz
      rw [← pow3_mod z3, pow_succ]
      simp only [mul_assoc]
  have hsub := CFSG.KC.PcChain.closure_sub_of_mul h1 hcl
  let F' : Fin 3 × Fin 3 × Fin 3 → C := fun t =>
    ⟨F t, mul_mem (mul_mem (pow_mem mx _) (pow_mem my _)) (pow_mem mz _)⟩
  have hsurj : Function.Surjective F' := by
    rintro ⟨w, hw⟩
    obtain ⟨t, ht⟩ := hsub w hw
    exact ⟨t, Subtype.ext ht⟩
  have hle := Nat.card_le_card_of_surjective F' hsurj
  choose d hdm hdz using hd
  let f : Fin 27 → C := fun e => ⟨d e e.2, hdm e e.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hab' : d a a.2 = d b b.2 := congrArg Subtype.val hab
    by_contra hne
    have hne' : (a : ℕ) ≠ b := fun h => hne (Fin.ext h)
    have hpt : ∀ z < 3510, ap (DF (27 * j + a)) z = ap (DF (27 * j + b)) z := fun z hz => by
      rw [hdz a a.2 z hz, hdz b b.2 z hz, hab']
    have hkey := kAp_base_eq hpt
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
    · exact hk b b.2 a hlt hkey
    · exact hk a a.2 b hlt hkey.symm
  have hge := Nat.card_le_card_of_injective f hinj
  have e27 : Nat.card (Fin 27) = 27 := by simp
  have e3 : Nat.card (Fin 3 × Fin 3 × Fin 3) = 27 := by simp
  rw [e3] at hle
  rw [e27] at hge
  omega

end CFSG.KS.Fi22Twist

end

module

public import Certificates.Data.Kernel.Spor.ClsK
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.Group

public section

namespace CFSG.KS.ClsK

open CFSG.KC.Enum CFSG.KS CFSG.KS.PSearch CFSG.KS.Raw CFSG.KS.Raw.Orb

variable {n w idn N b : Nat} {T : Nat → Nat} {ks reps tg : List Nat}
  {G : Subgroup (Equiv.Perm (Fin n))} {X : Nat → Equiv.Perm (Fin n)}

theorem itP_spec {P : Nat} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g) (k : Nat) (x : Fin n) :
    itP w (mask w) P k x = ((g ^ k) x : Nat) := by
  induction k with
  | zero => rw [pow_zero, Equiv.Perm.one_apply] <;> rfl
  | succ k ih =>
    change pg w (mask w) P (itP w (mask w) P k x) = _
    rw [ih, hP, pow_succ', Equiv.Perm.mul_apply]

theorem movK_ne {P k : Nat} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g)
    (hks : ∀ p ∈ ks, p < n) (h : movK w (mask w) P k ks = true) :
    ∃ p ∈ ks, ∃ hp : p < n, (g ^ k) ⟨p, hp⟩ ≠ ⟨p, hp⟩ := by
  induction ks with
  | nil => exact absurd h Bool.false_ne_true
  | cons q ks ih =>
    change bIf(Nat.beq (itP w (mask w) P k q) q, movK w (mask w) P k ks, true) = true at h
    have hq := hks q List.mem_cons_self
    by_cases e : Nat.beq (itP w (mask w) P k q) q = true
    · rw [e] at h
      obtain ⟨p, hp, hp', hne⟩ := ih (fun p hp => hks p (List.mem_cons_of_mem _ hp)) h
      exact ⟨p, List.mem_cons_of_mem _ hp, hp', hne⟩
    · refine ⟨q, List.mem_cons_self, hq, fun e' => e ?_⟩
      have := itP_spec hP k ⟨q, hq⟩
      rw [e'] at this
      rw [Nat.beq_eq]
      exact this

theorem movK_pow_ne_one {P k : Nat} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g)
    (hks : ∀ p ∈ ks, p < n) (h : movK w (mask w) P k ks = true) : g ^ k ≠ 1 := by
  obtain ⟨p, -, hp, e⟩ := movK_ne hP hks h
  intro h1
  rw [h1] at e
  exact e rfl

theorem cjK_spec {H R Q : Nat} {h r x : Equiv.Perm (Fin n)} (hH : PRep n w H h)
    (hR : PRep n w R r) (hx : PRep n w Q x) (hks : ∀ p ∈ ks, p < n)
    (hc : cjK w (mask w) H R Q ks = true) :
    ∀ p ∈ ks, ∀ hp : p < n, (h * r) ⟨p, hp⟩ = (x * h) ⟨p, hp⟩ := by
  induction ks with
  | nil => intro p hp; exact absurd hp List.not_mem_nil
  | cons q ks ih =>
    change bAnd(Nat.beq (pg w (mask w) H (pg w (mask w) R q))
      (pg w (mask w) Q (pg w (mask w) H q)), cjK w (mask w) H R Q ks) = true at hc
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hc
    intro p hp hp'
    rcases List.mem_cons.1 hp with rfl | hp
    · apply Fin.ext
      have e := Nat.eq_of_beq_eq_true hc.1
      have hR' : pg w (mask w) R p = r ⟨p, hp'⟩ := hR ⟨p, hp'⟩
      have hH' : pg w (mask w) H p = h ⟨p, hp'⟩ := hH ⟨p, hp'⟩
      rw [hR', hH, hH', hx] at e
      exact e
    · exact ih (fun p hp => hks p (List.mem_cons_of_mem _ hp)) hc.2 p hp hp'

theorem clsK_bRec_true (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = true ↔
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp

theorem ptK_facts {m i t : Nat} (h : ptK w m idn N T ks reps i t = true) :
    (T i ≠ idn → movK w m (T i) (nat_lit 1) ks = true) ∧
    (t = 0 → T i ≠ idn →
      movK w m (T i) (nat_lit 2) ks = true ∧ movK w m (T i) (nat_lit 5) ks = true) ∧
    (t ≠ 0 → Nat.mod (Nat.sub t (nat_lit 1)) (nat_lit 4) < reps.length ∧
      Nat.div (Nat.sub t (nat_lit 1)) (nat_lit 4) < N ∧
      cjK w m (T (Nat.div (Nat.sub t (nat_lit 1)) (nat_lit 4)))
        (T (nthN reps (Nat.mod (Nat.sub t (nat_lit 1)) (nat_lit 4)))) (T i) ks = true) := by
  unfold ptK at h
  simp only [CFSG.KS.Raw.Orb.strictB_eq, clsK_bRec_true, Bool.eq_false_iff, Nat.beq_eq,
    Nat.blt_eq, ne_eq, Bool.false_eq_true, and_false, false_and, or_false, false_or,
    and_true, true_and] at h
  refine ⟨fun he => by tauto, fun ht he => by tauto, fun ht => by tauto⟩

theorem tagsK_spec {m : Nat} : ∀ {tg : List Nat} {i : Nat},
    tagsK w m idn N T ks reps tg i = true →
      ∀ j < tg.length, ptK w m idn N T ks reps (i + j) (tg.getD j 0) = true
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | t :: tg, i, h, j, hj => by
    change bAnd(ptK w m idn N T ks reps i t, tagsK w m idn N T ks reps tg (Nat.succ i)) = true at h
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    cases j with
    | zero =>
      rw [List.getD_cons_zero, Nat.add_zero]
      exact h.1
    | succ j =>
      have := tagsK_spec h.2 j (by simp only [List.length_cons] at hj; omega)
      rw [List.getD_cons_succ, show i + (j + 1) = Nat.succ i + j by omega]
      exact this

theorem cntK_spec (c : Nat) : ∀ tg : List Nat, ∃ S : Finset ℕ, S.card = cntK c tg ∧
    ∀ i ∈ S, i < tg.length ∧ tg.getD i 0 ≠ 0 ∧ (tg.getD i 0 - 1) % 4 = c
  | [] => ⟨∅, rfl, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | t :: tg => by
    obtain ⟨S, hS, hm⟩ := cntK_spec c tg
    have hS1 : ∀ i ∈ S.map ⟨Nat.succ, Nat.succ_injective⟩, i < (t :: tg).length ∧
        (t :: tg).getD i 0 ≠ 0 ∧ ((t :: tg).getD i 0 - 1) % 4 = c := by
      intro i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hi
      obtain ⟨h1, h2, h3⟩ := hm a ha
      simp only [Function.Embedding.coeFn_mk, Nat.succ_eq_add_one, List.getD_cons_succ,
        List.length_cons]
      exact ⟨by omega, h2, h3⟩
    have h0 : 0 ∉ S.map ⟨Nat.succ, Nat.succ_injective⟩ := by simp
    have e : cntK c (t :: tg) = nIf(Nat.beq t 0, cntK c tg,
        nIf(Nat.beq (Nat.mod (Nat.sub t 1) 4) c, Nat.succ (cntK c tg), cntK c tg)) := rfl
    by_cases ht : t ≠ 0 ∧ (t - 1) % 4 = c
    · refine ⟨insert 0 (S.map ⟨Nat.succ, Nat.succ_injective⟩), ?_, fun i hi => ?_⟩
      · rw [Finset.card_insert_of_notMem h0, Finset.card_map, hS, e]
        simp only [CFSG.KS.Raw.Orb.nIf_eq]
        rw [if_neg (by rw [Nat.beq_eq]; exact ht.1), if_pos (by rw [Nat.beq_eq]; exact ht.2)]
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · exact ⟨by simp, ht.1, ht.2⟩
        · exact hS1 i hi
    · refine ⟨S.map ⟨Nat.succ, Nat.succ_injective⟩, ?_, hS1⟩
      rw [Finset.card_map, hS, e]
      simp only [CFSG.KS.Raw.Orb.nIf_eq]
      by_cases t0 : t = 0
      · rw [if_pos (by rw [Nat.beq_eq]; exact t0)]
      · rw [if_neg (by rw [Nat.beq_eq]; exact t0),
          if_neg (by rw [Nat.beq_eq]; exact fun h => ht ⟨t0, h⟩)]

theorem clsK_spec (hX : ∀ i < N, PRep n w (T i) (X i)) (hmem : ∀ i < N, X i ∈ G)
    (hall : ∀ g ∈ G, ∃ i < N, X i = g) (hidn : PRep n w idn 1) (hks : ∀ p ∈ ks, p < n)
    (h : clsK w (mask w) idn N T ks reps tg b = true) :
    (∀ c < reps.length, nthN reps c < N ∧ ∃ S : Finset ℕ, b ≤ S.card ∧
      ∀ i ∈ S, i < N ∧ ∃ k < N, X k * X (nthN reps c) * (X k)⁻¹ = X i) ∧
    ∀ i < N, X i = 1 ∨ (X i ^ 2 ≠ 1 ∧ X i ^ 5 ≠ 1) ∨
      ∃ c < reps.length, ∃ k < N, X k * X (nthN reps c) * (X k)⁻¹ = X i := by
  classical
  simp only [clsK, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hlen, htags, -, hrp⟩ := h
  have hlen' : tg.length = N := Nat.eq_of_beq_eq_true hlen
  have hrp' := CFSG.KS.Raw.Orb.allN_iff.1 hrp
  have hpt : ∀ i < N, ptK w (mask w) idn N T ks reps i (tg.getD i 0) = true := fun i hi => by
    have := tagsK_spec (i := 0) htags i (by omega)
    rwa [Nat.zero_add] at this
  have hone : ∀ g ∈ G, (∀ p ∈ ks, ∀ hp : p < n, g ⟨p, hp⟩ = ⟨p, hp⟩) → g = 1 := by
    intro g hg hfix
    obtain ⟨i, hi, rfl⟩ := hall g hg
    by_cases he : T i = idn
    · exact Equiv.ext fun x => Fin.ext (by rw [← hX i hi x, he, hidn x])
    · obtain ⟨p, hp, hp', e⟩ := movK_ne (hX i hi) hks ((ptK_facts (hpt i hi)).1 he)
      rw [pow_one] at e
      exact absurd (hfix p hp hp') e
  have heq : ∀ a ∈ G, ∀ c ∈ G, (∀ p ∈ ks, ∀ hp : p < n, a ⟨p, hp⟩ = c ⟨p, hp⟩) → a = c := by
    intro a ha c hc e
    have := hone (c⁻¹ * a) (G.mul_mem (G.inv_mem hc) ha) fun p hp hp' => by
      rw [Equiv.Perm.mul_apply, e p hp hp']
      exact Equiv.symm_apply_apply c _
    rwa [inv_mul_eq_one, eq_comm] at this
  have hconj : ∀ i < N, tg.getD i 0 ≠ 0 → (tg.getD i 0 - 1) % 4 < reps.length ∧
      ∃ k < N, X k * X (nthN reps ((tg.getD i 0 - 1) % 4)) * (X k)⁻¹ = X i := by
    intro i hi ht
    obtain ⟨h1, h2, h3⟩ := (ptK_facts (hpt i hi)).2.2 ht
    have hr0 := hrp' _ h1
    simp only [Bool.and_eq_true] at hr0
    have hr := Nat.blt_eq.mp hr0.1
    refine ⟨h1, (tg.getD i 0 - 1) / 4, h2, ?_⟩
    have e := heq _ (G.mul_mem (hmem _ h2) (hmem _ hr)) _ (G.mul_mem (hmem i hi) (hmem _ h2))
      (cjK_spec (hX _ h2) (hX _ hr) (hX i hi) hks h3)
    have e' : X ((tg.getD i 0 - 1) / 4) * X (nthN reps ((tg.getD i 0 - 1) % 4)) =
        X i * X ((tg.getD i 0 - 1) / 4) := e
    rw [e']
    group
  refine ⟨fun c hc => ?_, fun i hi => ?_⟩
  · have hr0 := hrp' c hc
    simp only [Bool.and_eq_true] at hr0
    obtain ⟨S, hS, hSm⟩ := cntK_spec c tg
    refine ⟨Nat.blt_eq.mp hr0.1, S, by rw [hS]; exact Nat.le_of_ble_eq_true hr0.2,
      fun i hiS => ?_⟩
    obtain ⟨hi, ht, hc'⟩ := hSm i hiS
    obtain ⟨-, k, hk, e⟩ := hconj i (by omega) ht
    rw [hc'] at e
    exact ⟨by omega, k, hk, e⟩
  · by_cases ht : tg.getD i 0 = 0
    · by_cases he : T i = idn
      · left
        exact Equiv.ext fun x => Fin.ext (by rw [← hX i hi x, he, hidn x])
      · right
        left
        obtain ⟨h2, h5⟩ := (ptK_facts (hpt i hi)).2.1 ht he
        exact ⟨movK_pow_ne_one (hX i hi) hks h2, movK_pow_ne_one (hX i hi) hks h5⟩
    · right
      right
      obtain ⟨hc, k, hk, e⟩ := hconj i hi ht
      exact ⟨_, hc, k, hk, e⟩

theorem card_mul_le_of_clsK (hX : ∀ i < N, PRep n w (T i) (X i)) (hmem : ∀ i < N, X i ∈ G)
    (hall : ∀ g ∈ G, ∃ i < N, X i = g) (hcard : Nat.card G = N) (hidn : PRep n w idn 1)
    (hks : ∀ p ∈ ks, p < n) (h : clsK w (mask w) idn N T ks reps tg b = true)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ G) (hg1 : g ≠ 1) (hg25 : g ^ 2 = 1 ∨ g ^ 5 = 1) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin n))) ⊓ G) * b ≤ N := by
  classical
  obtain ⟨hS, hpt⟩ := clsK_spec hX hmem hall hidn hks h
  obtain ⟨i0, hi0, rfl⟩ := hall g hg
  set Gf : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter (· ∈ G)
  have hGf : Gf = (Finset.range N).image X := by
    ext x
    simp only [Gf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_range]
    exact ⟨fun hx => hall x hx, fun ⟨i, hi, e⟩ => e ▸ hmem i hi⟩
  have hcG : Gf.card = N := by
    rw [← hcard, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hinj : Set.InjOn X (Finset.range N : Set ℕ) := by
    rw [← Finset.card_image_iff, ← hGf, hcG, Finset.card_range]
  rcases hpt i0 hi0 with h1 | ⟨h2, h5⟩ | ⟨c, hc, k0, hk0, e0⟩
  · exact absurd h1 hg1
  · rcases hg25 with e | e
    · exact absurd e h2
    · exact absurd e h5
  obtain ⟨-, S, hbS, hSm⟩ := hS c hc
  set r := X (nthN reps c)
  have hκ : ∀ i ∈ S, ∃ κ ∈ G, κ * X i0 * κ⁻¹ = X i := by
    intro i hi
    obtain ⟨-, k, hk, e⟩ := hSm i hi
    refine ⟨X k * (X k0)⁻¹, G.mul_mem (hmem k hk) (G.inv_mem (hmem k0 hk0)), ?_⟩
    rw [← e, ← e0]
    group
  choose! κ hκG hκe using hκ
  set K := Subgroup.centralizer ({X i0} : Set (Equiv.Perm (Fin n))) ⊓ G
  set Kf : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter (· ∈ K)
  have hcK : Nat.card K = Kf.card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hmaps : ∀ x ∈ S ×ˢ Kf, (fun x : ℕ × Equiv.Perm (Fin n) => κ x.1 * x.2) x ∈ Gf := by
    rintro ⟨i, z⟩ hx
    rw [Finset.mem_product] at hx
    have hz : z ∈ K := (Finset.mem_filter.1 hx.2).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, G.mul_mem (hκG i hx.1) (Subgroup.mem_inf.1 hz).2⟩
  have hconj : ∀ i ∈ S, ∀ z ∈ K, (κ i * z) * X i0 * (κ i * z)⁻¹ = X i := by
    intro i hi z hz
    have hzc : z * X i0 = X i0 * z :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hz).1)
    rw [← hκe i hi, mul_inv_rev, ← mul_assoc, mul_assoc (κ i) z, hzc]
    group
  have hinj2 : Set.InjOn (fun x : ℕ × Equiv.Perm (Fin n) => κ x.1 * x.2)
      ((S ×ˢ Kf : Finset (ℕ × Equiv.Perm (Fin n))) : Set (ℕ × Equiv.Perm (Fin n))) := by
    rintro ⟨i, z⟩ hx ⟨j, z'⟩ hy e
    simp only [Finset.mem_coe, Finset.mem_product] at hx hy
    have hz : z ∈ K := (Finset.mem_filter.1 hx.2).2
    have hz' : z' ∈ K := (Finset.mem_filter.1 hy.2).2
    have e' : κ i * z = κ j * z' := e
    have hij : X i = X j := by
      rw [← hconj i hx.1 z hz, ← hconj j hy.1 z' hz', e']
    have hij' : i = j := hinj (by simpa using (hSm i hx.1).1) (by simpa using (hSm j hy.1).1) hij
    subst hij'
    exact Prod.ext rfl (mul_left_cancel e')
  have hle := Finset.card_le_card_of_injOn _ hmaps hinj2
  rw [Finset.card_product, hcG] at hle
  rw [hcK]
  calc Kf.card * b ≤ Kf.card * S.card := Nat.mul_le_mul_left _ hbS
    _ = S.card * Kf.card := Nat.mul_comm _ _
    _ ≤ N := hle

end CFSG.KS.ClsK

end

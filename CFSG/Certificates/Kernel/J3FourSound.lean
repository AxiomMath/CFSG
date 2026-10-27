module

public import Certificates.Data.Kernel.J3Four
public import CFSG.Certificates.Kernel.YoshQ.TabNSound
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.KD.J3Four

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KS.PF Subgroup

@[expose] def PRep (n x : ℕ) (X : Equiv.Perm (Fin n)) : Prop :=
  ∀ q (hq : q < n), pg 13 (mask 13) x q = (X ⟨q, hq⟩ : ℕ)

theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_eq (c : Bool) : Bool.rec (motive := fun _ => Bool) true false c = !c := by
  cases c <;> rfl

section Packed

variable {n : ℕ}

theorem prep_pmN (hn : n < 2 ^ 32) {x y : ℕ} {X Y : Equiv.Perm (Fin n)} (hx : PRep n x X)
    (hy : PRep n y Y) : PRep n (pmN n 13 x y) (X * Y) := by
  intro q hq
  have hyq := hy q hq
  have hlt : pg 13 (mask 13) y q < n := by rw [hyq]; exact (Y ⟨q, hq⟩).isLt
  rw [pmN, pg_pcomp hn hq, pg_mod hlt, hx _ hlt, Equiv.Perm.mul_apply]
  congr 2
  exact Fin.ext hyq

theorem prep_pidn (hn : n + 1 < 2 ^ 13) : PRep n (pidn n 13) 1 := by
  intro q hq
  rw [pg_pidn (by omega) hn hq]
  rfl

theorem prep_eq {x y : ℕ} {X Y : Equiv.Perm (Fin n)} (hx : PRep n x X) (hy : PRep n y Y) :
    eqN n 13 x y = true ↔ X = Y := by
  unfold eqN
  rw [Nat.beq_eq, ← tabN_inj_iff (n := n) (by decide) (by decide)]
  constructor
  · intro h
    ext ⟨q, hq⟩
    have e := h q hq
    rw [ap_tabN (by decide), ap_tabN (by decide), pg_mod hq, pg_mod hq, hx q hq, hy q hq] at e
    exact e
  · rintro rfl q hq
    rw [ap_tabN (by decide), ap_tabN (by decide), pg_mod hq, pg_mod hq, hx q hq, hy q hq]

end Packed

theorem lenN_eq (L : List ℕ) : lenN L = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [lenN, List.length_cons] at ih ⊢; rw [ih]

theorem lenR_eq (R : List (ℕ × List ℕ)) : lenR R = R.length := by
  induction R with
  | nil => rfl
  | cons a R ih => simp only [lenR, List.length_cons] at ih ⊢; rw [ih]

theorem letOK_iff (m : ℕ) (w : List ℕ) : letOK m w = true ↔ ∀ a ∈ w, a < m := by
  induction w with
  | nil => simp [letOK]
  | cons a w ih =>
    have e : letOK m (a :: w) = (Nat.blt a m && letOK m w) := bAnd_eq _ _
    rw [e, Bool.and_eq_true, ih, Nat.blt_eq]
    simp

section Words

variable {n : ℕ} {G Gi : List ℕ} {σ : ℕ → Equiv.Perm (Fin n)}

noncomputable def wordP (σ : ℕ → Equiv.Perm (Fin n)) (w : List ℕ) : Equiv.Perm (Fin n) :=
  (w.map σ).prod

theorem wImg_eq (hG : ∀ i < G.length, PRep n (getN G i) (σ i)) {w : List ℕ}
    (hw : ∀ a ∈ w, a < G.length) (q : ℕ) (hq : q < n) :
    wImg G w q = (wordP σ w ⟨q, hq⟩ : ℕ) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ih' := ih (fun b hb => hw b (List.mem_cons_of_mem a hb))
    have hlt : wImg G w q < n := by rw [ih']; exact Fin.isLt _
    change pg 13 (mask 13) (getN G a) (wImg G w q) = _
    rw [hG a (hw a (List.mem_cons_self ..)) _ hlt]
    simp only [wordP, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    congr 2
    exact Fin.ext ih'

theorem wInv_eq (hGi : ∀ i < Gi.length, PRep n (getN Gi i) (σ i)⁻¹) {w : List ℕ}
    (hw : ∀ a ∈ w, a < Gi.length) (q : ℕ) (hq : q < n) :
    wInv Gi w q = ((wordP σ w)⁻¹ ⟨q, hq⟩ : ℕ) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
    have ha := hGi a (hw a (List.mem_cons_self ..)) q hq
    have hlt : pg 13 (mask 13) (getN Gi a) q < n := by rw [ha]; exact Fin.isLt _
    change wInv Gi w (pg 13 (mask 13) (getN Gi a) q) = _
    rw [ih (fun b hb => hw b (List.mem_cons_of_mem a hb)) _ hlt]
    simp only [wordP, List.map_cons, List.prod_cons, mul_inv_rev, Equiv.Perm.mul_apply]
    congr 2
    exact Fin.ext ha

theorem wordN_rep {σ' : ℕ → Equiv.Perm (Fin 6156)} (hG : ∀ i < G.length, PRep 6156 (getN G i) (σ' i))
    {w : List ℕ} (hw : ∀ a ∈ w, a < G.length) : PRep 6156 (wordN G w) (wordP σ' w) := by
  induction w with
  | nil => exact prep_pidn (by decide)
  | cons a w ih =>
    change PRep 6156 (pmN 6156 13 (getN G a) (wordN G w)) _
    simp only [wordP, List.map_cons, List.prod_cons] at ih ⊢
    exact prep_pmN (by decide) (hG a (hw a (List.mem_cons_self ..)))
      (ih fun b hb => hw b (List.mem_cons_of_mem a hb))

end Words

noncomputable def keyP {n : ℕ} (Y : Equiv.Perm (Fin n)) : List ℕ → ℕ
  | [] => 0
  | p :: pts => Nat.lor (if h : p < n then (Y ⟨p, h⟩ : ℕ) else 0) (keyP Y pts <<< 13)

theorem keysN_eq {n : ℕ} {G Gi : List ℕ} {x : ℕ} {w : List ℕ} {σ : ℕ → Equiv.Perm (Fin n)}
    {X : Equiv.Perm (Fin n)} (hG : ∀ i < G.length, PRep n (getN G i) (σ i))
    (hGi : ∀ i < Gi.length, PRep n (getN Gi i) (σ i)⁻¹) (hx : PRep n x X)
    (hw : ∀ a ∈ w, a < G.length) (hw' : ∀ a ∈ w, a < Gi.length) :
    ∀ pts : List ℕ, (∀ p ∈ pts, p < n) →
      keysN G Gi x pts w = keyP ((wordP σ w)⁻¹ * X * wordP σ w) pts
  | [], _ => rfl
  | p :: pts, hpts => by
    have hp := hpts p (List.mem_cons_self ..)
    change Nat.lor (keyN G Gi x p w) (keysN G Gi x pts w <<< 13) = _
    rw [keysN_eq hG hGi hx hw hw' pts fun q hq => hpts q (List.mem_cons_of_mem p hq), keyP,
      dif_pos hp]
    congr 1
    have e1 := wImg_eq hG hw p hp
    have hlt : wImg G w p < n := by rw [e1]; exact Fin.isLt _
    have e2 := hx _ hlt
    have hlt2 : pg 13 (mask 13) x (wImg G w p) < n := by rw [e2]; exact Fin.isLt _
    unfold keyN
    rw [wInv_eq hGi hw' _ hlt2, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    congr 2
    apply Fin.ext
    change pg 13 (mask 13) x (wImg G w p) = _
    rw [e2]
    congr 2
    exact Fin.ext e1

theorem conjGo_spec {G Gi : List ℕ} {x : ℕ} {pts : List ℕ} {m : ℕ} :
    ∀ (R : List (ℕ × List ℕ)) (lo : ℕ), conjGo G Gi x pts m R lo = true →
      (∀ r ∈ R, lo ≤ r.1 ∧ letOK m r.2 = true ∧ keysN G Gi x pts r.2 = r.1) ∧
        R.Pairwise (fun r s => r.1 < s.1)
  | [], _, _ => ⟨by simp, List.Pairwise.nil⟩
  | (k, w) :: R, lo, h => by
    have e : conjGo G Gi x pts m ((k, w) :: R) lo =
        bAnd(Nat.ble lo k, bAnd(letOK m w, bAnd(Nat.beq (keysN G Gi x pts w) k,
          conjGo G Gi x pts m R (k + 1)))) := rfl
    rw [e, bAnd_eq, bAnd_eq, bAnd_eq] at h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨ih1, ih2⟩ := conjGo_spec R (k + 1) h4
    refine ⟨?_, List.Pairwise.cons (fun s hs => (ih1 s hs).1) ih2⟩
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨h1, h2, h3⟩
    · have := ih1 r hr
      exact ⟨by omega, this.2⟩

theorem conjOK_sound {n : ℕ} {G Gi : List ℕ} {x : ℕ} {pts : List ℕ} {R : List (ℕ × List ℕ)}
    (σ : ℕ → Equiv.Perm (Fin n)) (X : Equiv.Perm (Fin n)) (hlen : Gi.length = G.length)
    (hG : ∀ i < G.length, PRep n (getN G i) (σ i))
    (hGi : ∀ i < G.length, PRep n (getN Gi i) (σ i)⁻¹) (hx : PRep n x X)
    (hpts : ∀ p ∈ pts, p < n) (h : conjOK G Gi x pts R = true) :
    R.length ≤ Nat.card {y | ∃ k ∈ closure (σ '' {i | i < G.length}), y = k⁻¹ * X * k} := by
  rw [conjOK, lenN_eq] at h
  obtain ⟨h1, h2⟩ := conjGo_spec R 0 h
  have hGi' : ∀ i < Gi.length, PRep n (getN Gi i) (σ i)⁻¹ := by rw [hlen]; exact hGi
  have hkey : ∀ r ∈ R, r.1 = keyP ((wordP σ r.2)⁻¹ * X * wordP σ r.2) pts := by
    intro r hr
    obtain ⟨-, hl, hk⟩ := h1 r hr
    have hw := (letOK_iff _ _).1 hl
    rw [← hk]
    exact keysN_eq hG hGi' hx hw (by rw [hlen]; exact hw) pts hpts
  let f : ℕ × List ℕ → Equiv.Perm (Fin n) := fun r => (wordP σ r.2)⁻¹ * X * wordP σ r.2
  have hnd : (R.map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine h2.imp_of_mem ?_
    intro r s hr hs hrs e
    have := hkey r hr
    rw [hkey s hs] at hrs
    rw [this] at hrs
    change keyP (f r) pts < keyP (f s) pts at hrs
    rw [e] at hrs
    exact lt_irrefl _ hrs
  have hsub : ((R.map f).toFinset : Set (Equiv.Perm (Fin n))) ⊆
      {y | ∃ k ∈ closure (σ '' {i | i < G.length}), y = k⁻¹ * X * k} := by
    intro y hy
    simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    refine ⟨wordP σ r.2, list_prod_mem ?_, rfl⟩
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
    exact subset_closure ⟨a, (letOK_iff _ _).1 (h1 r hr).2.1 a ha, rfl⟩
  calc R.length = (R.map f).toFinset.card := by
        rw [List.toFinset_card_of_nodup hnd, List.length_map]
    _ = ((R.map f).toFinset : Set (Equiv.Perm (Fin n))).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := by
        rw [Nat.card_coe_set_eq]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem powSq_rep {B A : Equiv.Perm (Fin 6156)} :
    ∀ (f b e acc : ℕ), PRep 6156 b B → PRep 6156 acc A →
      PRep 6156 (powSq f b e acc) (B ^ (e % 2 ^ f) * A)
  | 0, b, e, acc, _, hA => by
    change PRep 6156 acc _
    rw [pow_zero, Nat.mod_one, pow_zero, one_mul]
    exact hA
  | f + 1, b, e, acc, hB, hA => by
    change PRep 6156 (strictN (nIf(Nat.beq (Nat.land e 1) 1, pmN 6156 13 b acc, acc)) fun acc' =>
      strictN (pmN 6156 13 b b) fun b' => powSq f b' (e >>> 1) acc') _
    rw [strictN_eq', strictN_eq']
    have hBB := prep_pmN (by decide) hB hB
    have key : e % 2 ^ (f + 1) = 2 * ((e >>> 1) % 2 ^ f) + e % 2 := by
      rw [Nat.shiftRight_eq_div_pow, pow_one, pow_succ, mul_comm (2 ^ f) 2, Nat.mod_mul]
      omega
    have hand : Nat.land e 1 = e % 2 := Nat.and_one_is_mod e
    rcases Nat.mod_two_eq_zero_or_one e with h0 | h1
    · have hb : Nat.beq (Nat.land e 1) 1 = false := by rw [hand, h0]; rfl
      rw [hb]
      have := powSq_rep f (b := pmN 6156 13 b b) (e >>> 1) acc (B := B * B) hBB hA
      rw [key, h0, Nat.add_zero, pow_mul, ← pow_two] at *
      simpa [pow_two] using this
    · have hb : Nat.beq (Nat.land e 1) 1 = true := by rw [hand, h1]; rfl
      rw [hb]
      have := powSq_rep f (b := pmN 6156 13 b b) (e >>> 1) (pmN 6156 13 b acc) (B := B * B)
        (A := B * A) hBB (prep_pmN (by decide) hB hA)
      rw [key, h1, pow_succ, pow_mul]
      simpa [pow_two, mul_assoc] using this

theorem ordOK_sound {x p : ℕ} {X : Equiv.Perm (Fin 6156)} (hx : PRep 6156 x X)
    (h : ordOK x p = true) : X ^ p = 1 ∧ X ≠ 1 := by
  have hid := prep_pidn (n := 6156) (by decide)
  have e : ordOK x p = (Nat.blt p 32 && (eqN 6156 13 (powSq 5 x p (pidn 6156 13)) (pidn 6156 13) &&
      !eqN 6156 13 x (pidn 6156 13))) := by
    unfold ordOK
    rw [bIf_eq, bAnd_eq, bAnd_eq]
  rw [e] at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  obtain ⟨hp, hpow, hne⟩ := h
  refine ⟨?_, ?_⟩
  · have := (prep_eq (powSq_rep 5 x p _ hx hid) hid).1 hpow
    rwa [mul_one, Nat.mod_eq_of_lt (by norm_num; omega)] at this
  · intro h1
    rw [h1] at hx
    rw [(prep_eq hx hid).2 rfl] at hne
    exact Bool.noConfusion hne

theorem commAll_spec {t : ℕ} {T : Equiv.Perm (Fin 6156)} {σ : ℕ → Equiv.Perm (Fin 6156)}
    (ht : PRep 6156 t T) : ∀ (G : List ℕ), (∀ i < G.length, PRep 6156 (getN G i) (σ i)) →
      commAll t G = true → ∀ i < G.length, T * σ i = σ i * T
  | [], _, _ => by simp
  | g :: G, hG, h => by
    have e : commAll t (g :: G) = (eqN 6156 13 (pmN 6156 13 t g) (pmN 6156 13 g t) &&
        commAll t G) := bAnd_eq _ _
    rw [e, Bool.and_eq_true] at h
    have hg := hG 0 (by simp)
    intro i hi
    cases i with
    | zero => exact (prep_eq (prep_pmN (by decide) ht hg) (prep_pmN (by decide) hg ht)).1 h.1
    | succ i =>
      exact commAll_spec (σ := fun j => σ (j + 1)) ht G
        (fun j hj => hG (j + 1) (by simp; omega)) h.2 i (by simpa using hi)

theorem centralOK_sound {G : List ℕ} {t : ℕ} {T : Equiv.Perm (Fin 6156)}
    {σ : ℕ → Equiv.Perm (Fin 6156)} (hG : ∀ i < G.length, PRep 6156 (getN G i) (σ i))
    (ht : PRep 6156 t T) (h : centralOK G t = true) :
    (∀ i < G.length, T * σ i = σ i * T) ∧ T * T = 1 ∧ T ≠ 1 := by
  have hid := prep_pidn (n := 6156) (by decide)
  have e : centralOK G t = (commAll t G && (eqN 6156 13 (pmN 6156 13 t t) (pidn 6156 13) &&
      !eqN 6156 13 t (pidn 6156 13))) := by
    unfold centralOK
    rw [bIf_eq, bAnd_eq, bAnd_eq]
  rw [e] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨commAll_spec ht G hG h1, (prep_eq (prep_pmN (by decide) ht ht) hid).1 h2, ?_⟩
  intro h1'
  rw [h1'] at ht
  rw [(prep_eq ht hid).2 rfl] at h3
  exact Bool.noConfusion h3

theorem rowK_sound {G Gi wx : List ℕ} {p : ℕ} {pts : List ℕ} {R : List (ℕ × List ℕ)} {c : ℕ}
    (σ : ℕ → Equiv.Perm (Fin 6156)) (hlen : Gi.length = G.length)
    (hG : ∀ i < G.length, PRep 6156 (getN G i) (σ i))
    (hGi : ∀ i < G.length, PRep 6156 (getN Gi i) (σ i)⁻¹) (hpts : ∀ q ∈ pts, q < 6156)
    (h : rowK G Gi wx p pts R c = true) :
    R.length = c ∧ wordP σ wx ∈ closure (σ '' {i | i < G.length}) ∧ wordP σ wx ^ p = 1 ∧
      wordP σ wx ≠ 1 ∧ c ≤ Nat.card {y | ∃ k ∈ closure (σ '' {i | i < G.length}),
        y = k⁻¹ * wordP σ wx * k} := by
  have e : rowK G Gi wx p pts R c = (Nat.beq (lenR R) c && (letOK (lenN G) wx &&
      (ordOK (wordN G wx) p && conjOK G Gi (wordN G wx) pts R))) := by
    unfold rowK
    rw [strictB_eq', bAnd_eq, bAnd_eq, bAnd_eq]
  rw [e] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenR_eq, lenN_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hw := (letOK_iff _ _).1 h2
  have hx := wordN_rep hG hw
  obtain ⟨o1, o2⟩ := ordOK_sound hx h3
  refine ⟨h1, list_prod_mem ?_, o1, o2, h1 ▸ conjOK_sound σ _ hlen hG hGi hx hpts h4⟩
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
  exact subset_closure ⟨a, hw a ha, rfl⟩

section Groups

variable {G : Type*} [Group G]

theorem card_cent_le (K : Subgroup G) [Finite K] {x : G} {m : ℕ}
    (hm : m ≤ Nat.card {y | ∃ k ∈ K, y = k⁻¹ * x * k}) :
    Nat.card ↥(K ⊓ centralizer {x}) * m ≤ Nat.card K := by
  set S := {y | ∃ k ∈ K, y = k⁻¹ * x * k}
  have hS : ∀ y : S, ∃ k : K, (y : G) = (k : G)⁻¹ * x * k := fun y => by
    obtain ⟨k, hk, e⟩ := y.2
    exact ⟨⟨k, hk⟩, e⟩
  choose kf hkf using hS
  let F : ↥(K ⊓ centralizer {x}) × S → K := fun cy =>
    ⟨cy.1 * kf cy.2, K.mul_mem (mem_inf.1 cy.1.2).1 (kf cy.2).2⟩
  have hF : Function.Injective F := by
    rintro ⟨c, y⟩ ⟨c', y'⟩ e
    have e' : (c : G) * kf y = c' * kf y' := congrArg Subtype.val e
    have hc : x * c = c * x := (mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2).symm
    have hc' : x * c' = c' * x := (mem_centralizer_singleton_iff.1 (mem_inf.1 c'.2).2).symm
    have conj : ∀ (d : G) (k : G), x * d = d * x → (d * k)⁻¹ * x * (d * k) = k⁻¹ * x * k := by
      intro d k hd
      rw [mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc x, hd]
      group
    have hy : y = y' := by
      apply Subtype.ext
      calc (y : G) = (kf y : G)⁻¹ * x * kf y := hkf y
        _ = ((c : G) * kf y)⁻¹ * x * ((c : G) * kf y) := (conj c _ hc).symm
        _ = ((c' : G) * kf y')⁻¹ * x * ((c' : G) * kf y') := by rw [e']
        _ = (kf y' : G)⁻¹ * x * kf y' := conj c' _ hc'
        _ = y' := (hkf y').symm
    subst hy
    have : (c : G) = c' := mul_right_cancel e'
    rw [Subtype.ext this]
  have hfin : Finite (↥(K ⊓ centralizer {x}) × S) := Finite.of_injective F hF
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod] at this
  calc Nat.card ↥(K ⊓ centralizer {x}) * m ≤ Nat.card ↥(K ⊓ centralizer {x}) * Nat.card S :=
        Nat.mul_le_mul_left _ hm
    _ ≤ _ := this

theorem eq_one_of_card_le (C : Subgroup G) [Finite C] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : G} (hx : x ∈ C) (hox : orderOf x = p) (hC : Nat.card C ≤ p) :
    ∀ y ∈ C, y * y = 1 → y = 1 := by
  intro y hy hyy
  have hcard : Nat.card C = p := le_antisymm hC (by
    rw [← hox, ← Nat.card_zpowers]
    exact card_le_of_le (zpowers_le.2 hx))
  have h1 : orderOf y ∣ p := by
    rw [← hcard, ← orderOf_mk y hy]
    exact orderOf_dvd_natCard _
  have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hyy)
  have hco : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have : orderOf y ∣ 1 := by
    rw [← hco]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

theorem eq_of_card_le (C : Subgroup G) [Finite C] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x t : G} (hx : x ∈ C) (hox : orderOf x = p) (ht : t ∈ C) (htt : t * t = 1) (ht1 : t ≠ 1)
    (hxt : t * x = x * t) (hC : Nat.card C ≤ 2 * p) :
    ∀ y ∈ C, y * y = 1 → y = 1 ∨ y = t := by
  intro y hy hyy
  have hot : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hco : (orderOf x).Coprime (orderOf t) := by
    rw [hox, hot, Nat.coprime_two_right]
    exact hodd
  have hcomm : Commute x t := hxt.symm
  have ho : orderOf (x * t) = 2 * p := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, hox, hot, mul_comm]
  have hz : zpowers (x * t) = C := eq_of_le_of_card_ge (zpowers_le.2 (C.mul_mem hx ht))
    (by rw [Nat.card_zpowers, ho]; exact hC)
  rw [← hz] at hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  have h2k : (x * t) ^ (2 * k) = 1 := by
    rw [mul_comm (2 : ℤ) k, zpow_mul, zpow_two]
    exact hyy
  have hk : ((2 * p : ℕ) : ℤ) ∣ 2 * k := by
    rw [← ho]
    exact orderOf_dvd_iff_zpow_eq_one.2 h2k
  have hpk : (p : ℤ) ∣ k := by
    push_cast at hk
    exact (mul_dvd_mul_iff_left two_ne_zero).1 hk
  obtain ⟨j, rfl⟩ := hpk
  have hxp : x ^ p = 1 := hox ▸ pow_orderOf_eq_one x
  have hgp : (x * t) ^ p = t := by
    rw [hcomm.mul_pow, hxp, one_mul]
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_succ, pow_mul, pow_two, htt, one_pow, one_mul]
  rw [zpow_mul, zpow_natCast, hgp, ← zpow_mod_orderOf, hot]
  rcases Int.emod_two_eq_zero_or_one j with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem pgroup23_of_sylow (K : Subgroup G) [Finite K] {p a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (ha : a ≤ 30) (hb : b ≤ 30) (hK : Nat.card K = 2 ^ a * 3 ^ b * p) {x t : G}
    (hx : x ∈ K) (hox : orderOf x = p) (htc : ∀ k ∈ K, k * t = t * k)
    (hC : ∀ y ∈ K ⊓ centralizer {x}, y * y = 1 → y = 1 ∨ y = t) :
    ∀ w ∈ K, w * w = 1 → w ≠ 1 → w ≠ t → Nat.card ↥(K ⊓ centralizer {w}) ∣ 2 ^ 30 * 3 ^ 30 := by
  intro w hw hww hw1 hwt
  have hCK : Nat.card ↥(K ⊓ centralizer {w}) ∣ 2 ^ a * 3 ^ b * p := hK ▸ card_dvd_of_le inf_le_left
  have h23 : 2 ^ a * 3 ^ b ∣ 2 ^ 30 * 3 ^ 30 := mul_dvd_mul (pow_dvd_pow 2 ha) (pow_dvd_pow 3 hb)
  by_cases hpC : p ∣ Nat.card ↥(K ⊓ centralizer {w})
  · exfalso
    have : Fact p.Prime := ⟨hp⟩
    have : Finite ↥(K ⊓ centralizer {w}) :=
      Finite.of_injective (inclusion (inf_le_left : K ⊓ centralizer {w} ≤ K)) (inclusion_injective _)
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpC
    have hyK : (y : G) ∈ K := (mem_inf.1 y.2).1
    have hyw : Commute (y : G) w := mem_centralizer_singleton_iff.1 (mem_inf.1 y.2).2
    have hoy : orderOf (y : G) = p := by rw [orderOf_coe]; exact hy
    have hnd : ¬ p ∣ 2 ^ a * 3 ^ b := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h))
    have hfac : (Nat.card K).factorization p = 1 := by
      rw [hK, Nat.factorization_mul (by positivity) hp.ne_zero, Finsupp.add_apply,
        hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hnd]
    have cx : Nat.card (zpowers (⟨x, hx⟩ : K)) = p ^ (Nat.card K).factorization p := by
      rw [hfac, pow_one, Nat.card_zpowers, orderOf_mk, hox]
    have cy : Nat.card (zpowers (⟨y, hyK⟩ : K)) = p ^ (Nat.card K).factorization p := by
      rw [hfac, pow_one, Nat.card_zpowers, orderOf_mk, hoy]
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K (Sylow.ofCard _ cy) (Sylow.ofCard _ cx)
    have hmem : (⟨x, hx⟩ : K) ∈ ((g • Sylow.ofCard _ cy : Sylow p K) : Subgroup K) := by
      rw [hg]
      exact mem_zpowers _
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    have hxk : x = (g : G) * (y : G) ^ k * (g : G)⁻¹ := by
      have e := congrArg Subtype.val hk
      simp only [coe_zpow, coe_mul, coe_inv] at e
      rw [e]
      group
    have hc : (y : G) ^ k * w = w * (y : G) ^ k := (hyw.zpow_left k).eq
    have hu : (g : G) * w * (g : G)⁻¹ ∈ K ⊓ centralizer {x} := by
      refine mem_inf.2 ⟨K.mul_mem (K.mul_mem g.2 hw) (K.inv_mem g.2), ?_⟩
      rw [mem_centralizer_singleton_iff, hxk]
      calc (g : G) * w * (g : G)⁻¹ * ((g : G) * (y : G) ^ k * (g : G)⁻¹) =
            (g : G) * (w * (y : G) ^ k) * (g : G)⁻¹ := by group
        _ = (g : G) * ((y : G) ^ k * w) * (g : G)⁻¹ := by rw [hc]
        _ = _ := by group
    rcases hC _ hu (by
        calc (g : G) * w * (g : G)⁻¹ * ((g : G) * w * (g : G)⁻¹) =
              (g : G) * (w * w) * (g : G)⁻¹ := by group
          _ = 1 := by rw [hww]; group) with h | h
    · exact hw1 (by
        calc w = (g : G)⁻¹ * ((g : G) * w * (g : G)⁻¹) * g := by group
          _ = 1 := by rw [h]; group)
    · exact hwt (by
        calc w = (g : G)⁻¹ * ((g : G) * w * (g : G)⁻¹) * g := by group
          _ = (g : G)⁻¹ * (t * g) := by rw [h, mul_assoc]
          _ = (g : G)⁻¹ * (g * t) := by rw [htc g g.2]
          _ = t := by group)
  · have hcop : Nat.Coprime (Nat.card ↥(K ⊓ centralizer {w})) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpC).symm
    exact (hcop.dvd_of_dvd_mul_right hCK).trans h23

end Groups

section Rows

variable {G Gi wx pts : List ℕ} {p c a b : ℕ} {R : List (ℕ × List ℕ)}
  {σ : ℕ → Equiv.Perm (Fin 6156)}

theorem orderOf_wordP (hp : p.Prime) (h1 : wordP σ wx ^ p = 1) (h2 : wordP σ wx ≠ 1) :
    orderOf (wordP σ wx) = p := by
  have : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime h1 h2

theorem four_of_rowK_central (hlen : Gi.length = G.length)
    (hG : ∀ i < G.length, PRep 6156 (getN G i) (σ i))
    (hGi : ∀ i < G.length, PRep 6156 (getN Gi i) (σ i)⁻¹) (hpts : ∀ q ∈ pts, q < 6156)
    (hrow : rowK G Gi wx p pts R c = true) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (ha : a ≤ 30) (hb : b ≤ 30)
    (hK : Nat.card (closure (σ '' {i | i < G.length})) = 2 ^ a * 3 ^ b * p)
    (hKc : Nat.card (closure (σ '' {i | i < G.length})) ≤ c * (2 * p))
    {t : ℕ} {T : Equiv.Perm (Fin 6156)} (ht : PRep 6156 t T) (hcen : centralOK G t = true)
    (hT : T ∈ closure (σ '' {i | i < G.length})) :
    ∀ w ∈ closure (σ '' {i | i < G.length}), w * w = 1 → w ≠ 1 → w ≠ T →
      Nat.card ↥(closure (σ '' {i | i < G.length}) ⊓ centralizer {w}) ∣ 2 ^ 30 * 3 ^ 30 := by
  set K := closure (σ '' {i | i < G.length})
  obtain ⟨-, hxK, hx1, hx2, hcnt⟩ := rowK_sound σ hlen hG hGi hpts hrow
  obtain ⟨hTσ, hTT, hT1⟩ := centralOK_sound hG ht hcen
  have hox := orderOf_wordP hp hx1 hx2
  have hcentral : K ≤ centralizer {T} := by
    rw [closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact mem_centralizer_singleton_iff.2 (hTσ i hi).symm
  have hcK : ∀ k ∈ K, k * T = T * k := fun k hk => mem_centralizer_singleton_iff.1 (hcentral hk)
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at hKc
      exact absurd hKc (Nat.not_le.2 (Nat.card_pos (α := K)))
    · exact h
  have hle := card_cent_le K hcnt
  have hCle : Nat.card ↥(K ⊓ centralizer {wordP σ wx}) ≤ 2 * p := by
    by_contra hcon
    have : c * (2 * p) < Nat.card ↥(K ⊓ centralizer {wordP σ wx}) * c := by
      rw [mul_comm c]
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_le hcon) hc0
    omega
  have hxC : wordP σ wx ∈ K ⊓ centralizer {wordP σ wx} :=
    mem_inf.2 ⟨hxK, mem_centralizer_singleton_iff.2 rfl⟩
  have hTC : T ∈ K ⊓ centralizer {wordP σ wx} :=
    mem_inf.2 ⟨hT, mem_centralizer_singleton_iff.2 (hcK _ hxK).symm⟩
  exact pgroup23_of_sylow K hp hp2 hp3 ha hb hK hxK hox hcK
    (eq_of_card_le _ hp hp2 hxC hox hTC hTT hT1 (hcK _ hxK).symm hCle)

theorem four_of_rowK (hlen : Gi.length = G.length)
    (hG : ∀ i < G.length, PRep 6156 (getN G i) (σ i))
    (hGi : ∀ i < G.length, PRep 6156 (getN Gi i) (σ i)⁻¹) (hpts : ∀ q ∈ pts, q < 6156)
    (hrow : rowK G Gi wx p pts R c = true) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (ha : a ≤ 30) (hb : b ≤ 30)
    (hK : Nat.card (closure (σ '' {i | i < G.length})) = 2 ^ a * 3 ^ b * p)
    (hKc : Nat.card (closure (σ '' {i | i < G.length})) ≤ c * p) :
    ∀ w ∈ closure (σ '' {i | i < G.length}), w * w = 1 → w ≠ 1 →
      Nat.card ↥(closure (σ '' {i | i < G.length}) ⊓ centralizer {w}) ∣ 2 ^ 30 * 3 ^ 30 := by
  set K := closure (σ '' {i | i < G.length})
  obtain ⟨-, hxK, hx1, hx2, hcnt⟩ := rowK_sound σ hlen hG hGi hpts hrow
  have hox := orderOf_wordP hp hx1 hx2
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at hKc
      exact absurd hKc (Nat.not_le.2 (Nat.card_pos (α := K)))
    · exact h
  have hle := card_cent_le K hcnt
  have hCle : Nat.card ↥(K ⊓ centralizer {wordP σ wx}) ≤ p := by
    by_contra hcon
    have : c * p < Nat.card ↥(K ⊓ centralizer {wordP σ wx}) * c := by
      rw [mul_comm c]
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_le hcon) hc0
    omega
  have hxC : wordP σ wx ∈ K ⊓ centralizer {wordP σ wx} :=
    mem_inf.2 ⟨hxK, mem_centralizer_singleton_iff.2 rfl⟩
  intro w hw hww hw1
  exact pgroup23_of_sylow K hp hp2 hp3 ha hb hK hxK hox (t := 1) (fun k _ => by group)
    (fun y hy hyy => Or.inl (eq_one_of_card_le _ hp hp2 hxC hox hCle y hy hyy)) w hw hww hw1 hw1

end Rows

end CFSG.KD.J3Four

end

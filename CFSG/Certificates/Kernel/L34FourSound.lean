module

public import Certificates.Data.Kernel.L34Four
public import CFSG.Certificates.Kernel.J3FourSound

public section

namespace CFSG.KD.L34Four

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KS.PF Subgroup
open CFSG.KD.J3Four (PRep getN lenN letOK conjOK lenR prep_pmN prep_pidn prep_eq lenN_eq lenR_eq
  letOK_iff conjOK_sound strictN_eq' strictB_eq' bAnd_eq bIf_eq card_cent_le eq_of_card_le
  pgroup23_of_sylow)

@[expose] noncomputable def wv (σ : ℕ → Equiv.Perm (Fin 42)) (w : List ℕ) : Equiv.Perm (Fin 42) :=
  (w.map σ).prod

@[expose] noncomputable def cgv (σ : ℕ → Equiv.Perm (Fin 42)) (W : List (List ℕ)) (j : ℕ) :
    Equiv.Perm (Fin 42) :=
  wv σ (W.getD j [])

theorem prep_pm {x y : ℕ} {X Y : Equiv.Perm (Fin 42)} (hx : PRep 42 x X) (hy : PRep 42 y Y) :
    PRep 42 (pm x y) (X * Y) :=
  prep_pmN (by norm_num) hx hy

theorem prep_one : PRep 42 one 1 := prep_pidn (by norm_num)

theorem prep_eq' {x y : ℕ} {X Y : Equiv.Perm (Fin 42)} (hx : PRep 42 x X) (hy : PRep 42 y Y) :
    eq x y = true ↔ X = Y :=
  prep_eq hx hy

theorem pg_eq_of_eqN {n w a b q : ℕ} (h : eqN n w a b = true) (hq : q < n) :
    pg w (mask w) a q = pg w (mask w) b q := by
  unfold eqN at h
  rw [Nat.beq_eq] at h
  rw [← pg_mod (n := n) hq, h, pg_mod hq]

theorem pg_eq_of_eq {a b q : ℕ} (h : eq a b = true) (hq : q < 42) :
    pg 13 (mask 13) a q = pg 13 (mask 13) b q :=
  pg_eq_of_eqN h hq

theorem prep_of_eq' {x y : ℕ} {X : Equiv.Perm (Fin 42)} (h : eq x y = true) (hx : PRep 42 x X) :
    PRep 42 y X := fun q hq => (pg_eq_of_eq h hq).symm.trans (hx q hq)

theorem pg_pm {x y q : ℕ} (hq : q < 42) (hy : pg 13 (mask 13) y q < 42) :
    pg 13 (mask 13) (pm x y) q = pg 13 (mask 13) x (pg 13 (mask 13) y q) := by
  unfold pm pmN
  rw [pg_pcomp (by norm_num) hq, pg_mod (n := nat_lit 42) (w := nat_lit 13) hy]

theorem pg_one {q : ℕ} (hq : q < 42) : pg 13 (mask 13) one q = q := by
  unfold one
  exact pg_pidn (by norm_num) (by norm_num) hq

theorem prep_inv {g gi : ℕ} {X : Equiv.Perm (Fin 42)} (hg : PRep 42 g X)
    (h : eq (pm gi g) one = true) : PRep 42 gi X⁻¹ := by
  intro s hs
  have hq := (X⁻¹ ⟨s, hs⟩).isLt
  have hgq : pg 13 (mask 13) g (X⁻¹ ⟨s, hs⟩ : ℕ) = s := by
    rw [hg _ hq]
    simp
  have e1 := pg_eq_of_eq h hq
  rw [pg_pm hq (by rw [hgq]; exact hs), hgq, pg_one hq] at e1
  exact e1

theorem lenW_eq (L : List (List ℕ)) : lenW L = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [lenW, List.length_cons] at ih ⊢; rw [ih]

theorem getW_eq : ∀ (L : List (List ℕ)) (i : ℕ), getW L i = L.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => getW_eq L i

variable {σ : ℕ → Equiv.Perm (Fin 42)}

theorem wv_mem (K : Subgroup (Equiv.Perm (Fin 42))) {m : ℕ} (hK : ∀ i < m, σ i ∈ K) {w : List ℕ}
    (hw : ∀ a ∈ w, a < m) : wv σ w ∈ K := by
  refine list_prod_mem ?_
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
  exact hK a (hw a ha)

theorem wordN_rep {G : List ℕ} (hG : ∀ i < G.length, PRep 42 (getN G i) (σ i)) {w : List ℕ}
    (hw : ∀ a ∈ w, a < G.length) : PRep 42 (wordN G w) (wv σ w) := by
  induction w with
  | nil => exact prep_one
  | cons a w ih =>
    change PRep 42 (pm (getN G a) (wordN G w)) _
    simp only [wv, List.map_cons, List.prod_cons] at ih ⊢
    exact prep_pm (hG a (hw a (List.mem_cons_self ..)))
      (ih fun b hb => hw b (List.mem_cons_of_mem a hb))

theorem powSq_rep {B A : Equiv.Perm (Fin 42)} :
    ∀ (f b e acc : ℕ), PRep 42 b B → PRep 42 acc A →
      PRep 42 (powSq f b e acc) (B ^ (e % 2 ^ f) * A)
  | 0, b, e, acc, _, hA => by
    change PRep 42 acc _
    rw [pow_zero, Nat.mod_one, pow_zero, one_mul]
    exact hA
  | f + 1, b, e, acc, hB, hA => by
    change PRep 42 (strictN (nIf(Nat.beq (Nat.land e 1) 1, pm b acc, acc)) fun acc' =>
      strictN (pm b b) fun b' => powSq f b' (e >>> 1) acc') _
    rw [strictN_eq', strictN_eq']
    have hBB := prep_pm hB hB
    have key : e % 2 ^ (f + 1) = 2 * ((e >>> 1) % 2 ^ f) + e % 2 := by
      rw [Nat.shiftRight_eq_div_pow, pow_one, pow_succ, mul_comm (2 ^ f) 2, Nat.mod_mul]
      omega
    have hand : Nat.land e 1 = e % 2 := Nat.and_one_is_mod e
    rcases Nat.mod_two_eq_zero_or_one e with h0 | h1
    · have hb : Nat.beq (Nat.land e 1) 1 = false := by rw [hand, h0]; rfl
      rw [hb]
      have := powSq_rep f (b := pm b b) (e >>> 1) acc (B := B * B) hBB hA
      rw [key, h0, Nat.add_zero, pow_mul, ← pow_two] at *
      simpa [pow_two] using this
    · have hb : Nat.beq (Nat.land e 1) 1 = true := by rw [hand, h1]; rfl
      rw [hb]
      have := powSq_rep f (b := pm b b) (e >>> 1) (pm b acc) (B := B * B)
        (A := B * A) hBB (prep_pm hB hA)
      rw [key, h1, pow_succ, pow_mul]
      simpa [pow_two, mul_assoc] using this

theorem ordOK_sound {x p : ℕ} {X : Equiv.Perm (Fin 42)} (hx : PRep 42 x X)
    (h : ordOK x p = true) : X ^ p = 1 ∧ X ≠ 1 := by
  have e : ordOK x p = (Nat.blt p 32 && (eq (powSq 5 x p one) one && !eq x one)) := by
    unfold ordOK
    rw [bIf_eq, bAnd_eq, bAnd_eq]
  rw [e] at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  obtain ⟨hp, hpow, hne⟩ := h
  refine ⟨?_, ?_⟩
  · have := (prep_eq' (powSq_rep 5 x p _ hx prep_one) prep_one).1 hpow
    rwa [mul_one, Nat.mod_eq_of_lt (by norm_num; omega)] at this
  · intro h1
    rw [h1] at hx
    rw [(prep_eq' hx prep_one).2 rfl] at hne
    exact Bool.noConfusion hne

theorem cgOK_sound {G Gc Gci : List ℕ} {W : List (List ℕ)} {r : ℕ} {Rr : Equiv.Perm (Fin 42)}
    (hG : ∀ i < G.length, PRep 42 (getN G i) (σ i)) (hr : PRep 42 r Rr)
    (h : cgOK G r W Gc Gci = true) :
    Gci.length = Gc.length ∧ ∀ j < Gc.length, (∀ a ∈ W.getD j [], a < G.length) ∧
      PRep 42 (getN Gc j) (cgv σ W j) ∧ PRep 42 (getN Gci j) (cgv σ W j)⁻¹ ∧
      cgv σ W j * Rr = Rr * cgv σ W j := by
  unfold cgOK at h
  rw [bAnd_eq, bAnd_eq] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenW_eq, lenN_eq] at h
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨h2, fun j hj => ?_⟩
  have h4 := CFSG.KS.allN_spec h3 j hj
  rw [strictB_eq', bAnd_eq, bAnd_eq, bAnd_eq] at h4
  simp only [Bool.and_eq_true] at h4
  obtain ⟨l, e1, e2, e3⟩ := h4
  rw [getW_eq, letOK_iff] at l
  rw [getW_eq] at e1
  have hg : PRep 42 (getN Gc j) (cgv σ W j) := prep_of_eq' e1 (wordN_rep hG l)
  exact ⟨l, hg, prep_inv hg e2, (prep_eq' (prep_pm hg hr) (prep_pm hr hg)).1 e3⟩

theorem rowL_sound {G : List ℕ} {i : ℕ} {W : List (List ℕ)} {Gc Gci wx : List ℕ} {p : ℕ}
    {pts : List ℕ} {R : List (ℕ × List ℕ)} {c : ℕ}
    (hG : ∀ k < G.length, PRep 42 (getN G k) (σ k)) (hpts : ∀ q ∈ pts, q < 42)
    (h : rowL G i W Gc Gci wx p pts R c = true) :
    i < G.length ∧
      (∀ K : Subgroup (Equiv.Perm (Fin 42)), (∀ k < G.length, σ k ∈ K) →
        ∀ j < Gc.length, cgv σ W j ∈ K) ∧
      (∀ j < Gc.length, cgv σ W j * σ i = σ i * cgv σ W j) ∧
      wv (cgv σ W) wx ∈ closure (cgv σ W '' {j | j < Gc.length}) ∧
      wv (cgv σ W) wx ^ p = 1 ∧ wv (cgv σ W) wx ≠ 1 ∧
      c ≤ Nat.card {y | ∃ k ∈ closure (cgv σ W '' {j | j < Gc.length}),
        y = k⁻¹ * wv (cgv σ W) wx * k} := by
  unfold rowL at h
  rw [bAnd_eq, strictB_eq', bAnd_eq, bAnd_eq, bAnd_eq, strictB_eq', bAnd_eq] at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, lenN_eq, lenR_eq] at h
  obtain ⟨hi, hcg, hc, hwx, ho, hconj⟩ := h
  have hr := hG i hi
  obtain ⟨hlen, hcs⟩ := cgOK_sound hG hr hcg
  rw [letOK_iff] at hwx
  have hGc : ∀ j < Gc.length, PRep 42 (getN Gc j) (cgv σ W j) := fun j hj => (hcs j hj).2.1
  have hx := wordN_rep hGc hwx
  obtain ⟨o1, o2⟩ := ordOK_sound hx ho
  refine ⟨hi, fun K hK j hj => wv_mem K hK (hcs j hj).1, fun j hj => (hcs j hj).2.2.2,
    wv_mem (closure (cgv σ W '' {j | j < Gc.length})) (fun j hj => subset_closure ⟨j, hj, rfl⟩)
      hwx, o1, o2, ?_⟩
  rw [← hc]
  exact conjOK_sound (cgv σ W) _ hlen hGc (fun j hj => (hcs j hj).2.2.1) hx hpts hconj

section Groups

variable {Γ : Type*} [Group Γ]

theorem four_of_cent (K : Subgroup Γ) [Finite K] {p a b m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (ha : a ≤ 30) (hb : b ≤ 30) (hK : Nat.card K = 2 ^ a * 3 ^ b * p) {x t : Γ}
    (hx : x ∈ K) (hox : orderOf x = p) (htK : t ∈ K) (htt : t * t = 1) (ht1 : t ≠ 1)
    (htc : ∀ k ∈ K, k * t = t * k) (hm : m ≤ Nat.card {y | ∃ k ∈ K, y = k⁻¹ * x * k})
    (hKc : Nat.card K ≤ m * (2 * p)) :
    ∀ w ∈ K, w * w = 1 → w ≠ 1 → w ≠ t → Nat.card ↥(K ⊓ centralizer {w}) ∣ 2 ^ 30 * 3 ^ 30 := by
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, zero_mul] at hKc
      exact absurd hKc (Nat.not_le.2 (Nat.card_pos (α := K)))
    · exact h
  have hle := card_cent_le K hm
  have hCle : Nat.card ↥(K ⊓ centralizer {x}) ≤ 2 * p := by
    by_contra hcon
    have : m * (2 * p) < Nat.card ↥(K ⊓ centralizer {x}) * m := by
      rw [mul_comm m]
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_le hcon) hm0
    omega
  have : Finite ↥(K ⊓ centralizer {x}) :=
    Finite.of_injective (inclusion (inf_le_left : K ⊓ centralizer {x} ≤ K)) (inclusion_injective _)
  have hxC : x ∈ K ⊓ centralizer {x} := mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 rfl⟩
  have htC : t ∈ K ⊓ centralizer {x} :=
    mem_inf.2 ⟨htK, mem_centralizer_singleton_iff.2 (htc _ hx).symm⟩
  exact pgroup23_of_sylow K hp hp2 hp3 ha hb hK hx hox htc
    (eq_of_card_le _ hp hp2 hxC hox htC htt ht1 (htc _ hx).symm hCle)

end Groups

theorem four_of_rowL {G : List ℕ} {i : ℕ} {W : List (List ℕ)} {Gc Gci wx : List ℕ} {p : ℕ}
    {pts : List ℕ} {R : List (ℕ × List ℕ)} {c a b : ℕ} (R' : Subgroup (Equiv.Perm (Fin 42)))
    (hG : ∀ k < G.length, PRep 42 (getN G k) (σ k)) (hGR : ∀ k < G.length, σ k ∈ R')
    (hpts : ∀ q ∈ pts, q < 42) (h : rowL G i W Gc Gci wx p pts R c = true) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (ha : a ≤ 30) (hb : b ≤ 30)
    (hK : Nat.card ↥(R' ⊓ centralizer {σ i}) = 2 ^ a * 3 ^ b * p)
    (hKc : Nat.card ↥(R' ⊓ centralizer {σ i}) ≤ c * (2 * p)) (hrr : σ i * σ i = 1)
    (hr1 : σ i ≠ 1) :
    ∀ w ∈ R' ⊓ centralizer {σ i}, w * w = 1 → w ≠ 1 → w ≠ σ i →
      Nat.card ↥((R' ⊓ centralizer {σ i}) ⊓ centralizer {w}) ∣ 2 ^ 30 * 3 ^ 30 := by
  obtain ⟨hi, hmem, hcomm, hxK, hx1, hx2, hcnt⟩ := rowL_sound hG hpts h
  set K := R' ⊓ centralizer {σ i}
  have hcl : closure (cgv σ W '' {j | j < Gc.length}) ≤ K := by
    rw [closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact mem_inf.2 ⟨hmem R' hGR j hj, mem_centralizer_singleton_iff.2 (hcomm j hj)⟩
  have : Fact p.Prime := ⟨hp⟩
  have hox : orderOf (wv (cgv σ W) wx) = p := orderOf_eq_prime hx1 hx2
  have hsub : {y | ∃ k ∈ closure (cgv σ W '' {j | j < Gc.length}),
      y = k⁻¹ * wv (cgv σ W) wx * k} ⊆ {y | ∃ k ∈ K, y = k⁻¹ * wv (cgv σ W) wx * k} := by
    rintro y ⟨k, hk, rfl⟩
    exact ⟨k, hcl hk, rfl⟩
  have hm : c ≤ Nat.card {y | ∃ k ∈ K, y = k⁻¹ * wv (cgv σ W) wx * k} :=
    hcnt.trans (Nat.card_mono (Set.toFinite _) hsub)
  have hrK : σ i ∈ K := mem_inf.2 ⟨hGR i hi, mem_centralizer_singleton_iff.2 rfl⟩
  exact four_of_cent K hp hp2 hp3 ha hb hK (hcl hxK) hox hrK hrr hr1
    (fun k hk => mem_centralizer_singleton_iff.1 (mem_inf.1 hk).2) hm hKc

end CFSG.KD.L34Four

end

module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CFSG.Certificates.Kernel.PkCV

open CFSG.Certificates CFSG.KS.PK CFSG.KC.Enum CFSG.KS.PF CFSG.Certificates.Kernel.PkEnum CFSG.GH74.KGroups
  CFSG.Sporadic.Schreier

variable {n : Nat} [hs : Small n]

theorem ev_toCV (a : VP n) : ev (toCV a) = pkp a := by
  ext i
  rw [ev_apply, pkp_apply]
  have hf : ∀ x < n, fd (wd n) a.1.1 x < 2 ^ wC n :=
    fun x hx => (a.2 x hx).1.trans (by have := lt_wC n; omega)
  exact pg_pmk hs.lt hf i.2

theorem ev_cOf (σ : Equiv.Perm (Fin n)) : ev (cOf σ) = σ := by
  ext i
  rw [ev_apply]
  have hf : ∀ x < n, (if h : x < n then (σ ⟨x, h⟩ : Nat) else 0) < 2 ^ wC n := fun x hx => by
    rw [dif_pos hx]
    exact (σ _).2.trans (by have := lt_wC n; omega)
  change pg (wC n) (CFSG.KS.mask (wC n)) (cOf σ).1 i = _
  rw [cOf, pg_pmk hs.lt hf i.2, dif_pos i.2]

theorem productsC_map (Ts : List (List (VP n))) :
    (productsC (Ts.map (List.map toCV))).map ev = (productsV Ts).map pkp := by
  induction Ts with
  | nil =>
    change [ev 1] = [pkp (oneV n)]
    rw [ev_one, pkp_oneV]
  | cons T Ts ih =>
    simp only [List.map_cons, productsC, productsV, List.map_flatMap, List.flatMap_map]
    congr 1
    funext t
    rw [List.map_map, List.map_map]
    have h1 : (ev ∘ fun x => toCV t * x) = fun x => pkp t * ev x := by
      funext x
      simp only [Function.comp_apply, ev_mul, ev_toCV]
    have h2 : (pkp ∘ mulV t) = fun x => pkp t * pkp x := by
      funext x
      simp only [Function.comp_apply, pkp_mulV]
    rw [h1, h2]
    have h3 := congrArg (List.map (fun x => pkp t * x)) ih
    simp only [List.map_map] at h3
    exact h3

theorem elemsT_eq_elemsC (Q : RawSchreierDatum n) : elemsT Q = (elemsC Q).map ev := by
  rw [elemsT_eq_elemsV, elemsV, enumV, elemsC, ← productsC_map, List.map_map]
  rfl

theorem sift_ev (Q : RawSchreierDatum n) (c : CV n) (i : Nat) : Q.sift (ev c) i = siftC Q c i := by
  rw [sift_eq_siftP, siftP, siftC]

theorem ev_mul' (a b : CV n) : ev a * ev b = ev (a * b) := (ev_mul a b).symm

theorem ev_inv' (a : CV n) : (ev a)⁻¹ = ev a⁻¹ := (ev_inv a).symm

theorem ev_pow' (a : CV n) (k : Nat) : ev a ^ k = ev (a ^ k) :=
  (map_pow (evHom n) a k).symm

theorem one_eq_ev : (1 : Equiv.Perm (Fin n)) = ev 1 := ev_one.symm

theorem ev_eq_iff (a b : CV n) : ev a = ev b ↔ a = b := ev_injective.eq_iff

theorem decide_ev_eq (a b : CV n) [Decidable (ev a = ev b)] :
    decide (ev a = ev b) = decide (a = b) := by
  simp only [ev_eq_iff]

theorem beq_ev [BEq (Equiv.Perm (Fin n))] [LawfulBEq (Equiv.Perm (Fin n))] (a b : CV n) :
    (ev a == ev b) = decide (a = b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ev_eq_iff]

theorem mem_map_ev (L : List (CV n)) (a : CV n) : ev a ∈ L.map ev ↔ a ∈ L := by
  rw [List.mem_map]
  exact ⟨fun ⟨b, hb, h⟩ => ev_injective h ▸ hb, fun h => ⟨a, h, rfl⟩⟩

theorem decide_mem_map_ev (L : List (CV n)) (a : CV n) [Decidable (ev a ∈ L.map ev)] :
    decide (ev a ∈ L.map ev) = decide (a ∈ L) := by
  simp only [mem_map_ev]

theorem contains_ev [BEq (Equiv.Perm (Fin n))] [LawfulBEq (Equiv.Perm (Fin n))]
    (L : List (Equiv.Perm (Fin n))) (a : CV n) :
    L.contains (ev a) = decide (a ∈ L.map cOf) := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_iff]
  conv_lhs => rw [← List.map_id L]
  have h : (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) = ev ∘ cOf := funext fun σ => (ev_cOf σ).symm
  rw [h, ← List.map_map, mem_map_ev]

theorem decide_mem_ev (L : List (Equiv.Perm (Fin n))) (a : CV n) [Decidable (ev a ∈ L)] :
    decide (ev a ∈ L) = decide (a ∈ L.map cOf) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  conv_lhs => rw [← List.map_id L]
  have h : (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) = ev ∘ cOf := funext fun σ => (ev_cOf σ).symm
  rw [h, ← List.map_map, mem_map_ev]

theorem orderIs_ev (g : CV n) (m : Nat) : orderIs (ev g) m = orderIs g m := by
  unfold orderIs
  simp only [ev_pow', one_eq_ev, ev_eq_iff]

theorem orderIsP_ev (g : CV n) (m : Nat) (ps : List Nat) :
    orderIsP (ev g) m ps = orderIsP g m ps := by
  unfold orderIsP
  simp only [ev_pow', one_eq_ev, ev_eq_iff]

theorem orderIs_eq_orderIsP {M : Type*} [Monoid M] [DecidableEq M] (g : M) {m : Nat}
    (hm : 0 < m) (ps : List Nat) (hps : ∀ p, p.Prime → p ∣ m → p ∈ ps)
    (hps' : ∀ p ∈ ps, p.Prime ∧ p ∣ m) : orderIs g m = orderIsP g m ps := by
  rw [Bool.eq_iff_iff, orderIs_iff g hm]
  unfold orderIsP
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one g, fun p hp => ?_⟩
    obtain ⟨hpr, hpd⟩ := hps' p hp
    apply pow_ne_one_of_lt_orderOf
    · exact (Nat.div_pos (Nat.le_of_dvd hm hpd) hpr.pos).ne'
    · rw [h]
      exact Nat.div_lt_self hm hpr.one_lt
  · rintro ⟨h1, h2⟩
    exact orderOf_eq_of_pow_and_pow_div_prime hm h1 fun p hp hpd => h2 p (hps p hp hpd)

theorem beq_cv (a b : CV n) : (a == b) = decide (a = b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]

theorem bne_def' {α : Type*} [BEq α] (a b : α) : (a != b) = !(a == b) := rfl

theorem contains_map_ev (L : List (CV n)) (a : CV n) [BEq (Equiv.Perm (Fin n))]
    [LawfulBEq (Equiv.Perm (Fin n))] : (L.map ev).contains (ev a) = decide (a ∈ L) := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, mem_map_ev, decide_eq_true_iff]

theorem contains_cv (L : List (CV n)) (a : CV n) : L.contains a = decide (a ∈ L) := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_iff]

theorem nodup_map_ev (L : List (CV n)) : (L.map ev).Nodup ↔ L.Nodup :=
  List.nodup_map_iff ev_injective

theorem dedup_map_ev (L : List (CV n)) : (L.map ev).dedup = L.dedup.map ev :=
  (List.dedup_map_of_injective ev_injective L)

theorem allFin_id {m : Nat} (σ : Equiv.Perm (Fin m)) :
    (List.finRange m).all (fun i => σ i == i) = decide (σ = 1) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
  simp only [beq_iff_eq]
  exact ⟨fun h => Equiv.ext fun i => h i (List.mem_finRange i), fun h i _ => by rw [h]; rfl⟩

theorem allFin_sq {m : Nat} (σ : Equiv.Perm (Fin m)) :
    (List.finRange m).all (fun i => σ (σ i) == i) = decide (σ * σ = 1) := allFin_id (σ * σ)

theorem allFin_comm {m : Nat} (a b : Equiv.Perm (Fin m)) :
    (List.finRange m).all (fun i => a (b i) == b (a i)) = decide (a * b = b * a) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
  simp only [beq_iff_eq]
  exact ⟨fun h => Equiv.ext fun i => h i (List.mem_finRange i), fun h i _ => by
    have := congrArg (fun σ : Equiv.Perm (Fin m) => σ i) h
    exact this⟩

theorem map_finRange_eq_iff {m : Nat} (σ τ : Equiv.Perm (Fin m)) :
    (List.finRange m).map σ = (List.finRange m).map τ ↔ σ = τ := by
  rw [List.map_inj_left]
  exact ⟨fun h => Equiv.ext fun i => h i (List.mem_finRange i), fun h i _ => by rw [h]⟩

theorem decide_comm_ev (g : CV n) (σ : Equiv.Perm (Fin n)) :
    decide (ev g * σ = σ * ev g) = decide (g * cOf σ = cOf σ * g) := by
  conv_lhs => rw [← ev_cOf σ]
  rw [ev_mul', ev_mul', decide_ev_eq]

theorem decide_conj_ev (g : CV n) (σ τ : Equiv.Perm (Fin n)) :
    decide (ev g * σ * (ev g)⁻¹ = τ) = decide (g * cOf σ * g⁻¹ = cOf τ) := by
  conv_lhs => rw [← ev_cOf σ, ← ev_cOf τ]
  rw [ev_inv', ev_mul', ev_mul', decide_ev_eq]

theorem decide_conj_mem_ev (g : CV n) (σ : Equiv.Perm (Fin n)) (L : List (Equiv.Perm (Fin n))) :
    decide (ev g * σ * (ev g)⁻¹ ∈ L) = decide (g * cOf σ * g⁻¹ ∈ L.map cOf) := by
  conv_lhs => rw [← ev_cOf σ]
  rw [ev_inv', ev_mul', ev_mul', decide_mem_ev]

theorem comm_fast (a b : CV n) : decide (a * b = b * a) = eq22C a b b a := (eq22C_eq a b b a).symm

theorem conj_fast (c g d : CV n) : decide (c * g * c⁻¹ = d) = eq22C c g d c := by
  rw [eq22C_eq, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, mul_inv_eq_iff_eq_mul]

theorem sq_fast (a : CV n) : decide (a * a = 1) = powOneC a 2 := by
  rw [powOneC_eq, pow_two]

theorem pow_fast (a : CV n) (k : Nat) : decide (a ^ k = 1) = powOneC a k := (powOneC_eq a k).symm

theorem eq_ev_cOf (σ : Equiv.Perm (Fin n)) : σ = ev (cOf σ) := (ev_cOf σ).symm

end CFSG.Certificates.Kernel.PkCV

end

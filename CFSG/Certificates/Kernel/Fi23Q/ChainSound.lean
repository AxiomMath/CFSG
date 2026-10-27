module

public import Certificates.Data.Kernel.Fi23Q.Chain
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.KS.Fi23Q

open CFSG.KC.Enum CFSG.KC.Fi23Q CFSG.KC.Pc3

variable {G : Type*} [Group G]

@[expose] def prs : List (List G) → List G
  | [] => [1]
  | L :: Ls => L.flatMap fun x => (prs Ls).map (x * ·)

theorem length_prs : ∀ Ls : List (List G), (prs Ls).length = (Ls.map List.length).prod
  | [] => rfl
  | L :: Ls => by
    rw [prs, List.length_flatMap, List.map_cons, List.prod_cons]
    simp only [List.length_map, length_prs Ls]
    rw [List.map_const', List.sum_replicate, smul_eq_mul]

theorem prs_mem (K : Subgroup G) :
    ∀ Ls : List (List G), (∀ L ∈ Ls, ∀ x ∈ L, x ∈ K) → ∀ z ∈ prs Ls, z ∈ K
  | [], _, z, hz => by
    rw [prs, List.mem_singleton] at hz
    rw [hz]
    exact K.one_mem
  | L :: Ls, h, z, hz => by
    rw [prs, List.mem_flatMap] at hz
    obtain ⟨x, hx, hz⟩ := hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    exact K.mul_mem (h L List.mem_cons_self x hx)
      (prs_mem K Ls (fun L' hL' => h L' (List.mem_cons_of_mem _ hL')) w hw)

@[expose] def ChainP (act : G → ℕ → ℕ) : List (ℕ × List G) → Prop
  | [] => True
  | l :: R => (l.2.map fun y => act y l.1).Nodup ∧ (∀ m ∈ R, ∀ y ∈ m.2, act y l.1 = l.1) ∧
      ChainP act R

section Act

variable {act : G → ℕ → ℕ} (hmul : ∀ g h x, act (g * h) x = act g (act h x))
  (hone : ∀ x, act 1 x = x)
include hmul hone

theorem fix_prs {p : ℕ} :
    ∀ R : List (ℕ × List G), (∀ m ∈ R, ∀ y ∈ m.2, act y p = p) →
      ∀ z ∈ prs (R.map Prod.snd), act z p = p
  | [], _, z, hz => by
    rw [List.map_nil, prs, List.mem_singleton] at hz
    rw [hz, hone]
  | m :: R, hR, z, hz => by
    rw [List.map_cons, prs, List.mem_flatMap] at hz
    obtain ⟨x, hx, hz⟩ := hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    rw [hmul, fix_prs R (fun m' hm' => hR m' (List.mem_cons_of_mem _ hm')) w hw,
      hR m List.mem_cons_self x hx]

theorem prs_nodup : ∀ Ls : List (ℕ × List G), ChainP act Ls → (prs (Ls.map Prod.snd)).Nodup
  | [], _ => List.nodup_singleton _
  | l :: R, ⟨h1, h2, h3⟩ => by
    have ih := prs_nodup R h3
    rw [List.map_cons, prs, List.nodup_flatMap]
    refine ⟨fun x _ => ih.map (mul_right_injective x), ?_⟩
    have hp : List.Pairwise (fun a b => act a l.1 ≠ act b l.1) l.2 := List.pairwise_map.1 h1
    refine hp.imp fun {a b} hab => ?_
    intro z hz1 hz2
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hz1
    obtain ⟨w, hw, e⟩ := List.mem_map.1 hz2
    apply hab
    have fu := fix_prs hmul hone R h2 u hu
    have fw := fix_prs hmul hone R h2 w hw
    calc act a l.1 = act (a * u) l.1 := by rw [hmul, fu]
      _ = act (b * w) l.1 := by rw [e]
      _ = act b l.1 := by rw [hmul, fw]

end Act

theorem allL_iff {L : List ℕ} {f : ℕ → Bool} : allL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => simp [allL]
  | cons x t ih =>
    change (Bool.rec (motive := fun _ => Bool) false (allL t f) (f x)) = true ↔ _
    rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, ih]
    simp

theorem notInN_iff {x : ℕ} {L : List ℕ} : notInN x L = true ↔ x ∉ L := by
  induction L with
  | nil => simp [notInN]
  | cons y t ih =>
    change (Bool.rec (motive := fun _ => Bool) false (notInN x t) (!Nat.beq x y)) = true ↔ _
    have e : (!Nat.beq x y) = true ↔ x ≠ y := by
      rw [Bool.not_eq_true', ← Bool.not_eq_true, Nat.beq_eq]
    rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, ih, e, List.mem_cons, not_or]

theorem nodupN_iff {L : List ℕ} : nodupN L = true ↔ L.Nodup := by
  induction L with
  | nil => simp [nodupN]
  | cons x t ih =>
    change (Bool.rec (motive := fun _ => Bool) false (nodupN t) (notInN x t)) = true ↔ _
    rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, ih, notInN_iff, List.nodup_cons]

theorem fixL_iff {H : ℕ → ℕ} {n p : ℕ} {R : List (ℕ × List ℕ)} :
    fixL H n p R = true ↔ ∀ m ∈ R, ∀ v ∈ m.2, imgV H n v p = p := by
  induction R with
  | nil => simp [fixL]
  | cons m t ih =>
    change (Bool.rec (motive := fun _ => Bool) false (fixL H n p t)
      (allL m.2 fun v => Nat.beq (imgV H n v p) p)) = true ↔ _
    rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, ih, allL_iff]
    simp [Nat.beq_eq]

theorem chainP_of {H : ℕ → ℕ} {n : ℕ} {act : G → ℕ → ℕ} {E : ℕ → G}
    (hW : ∀ v, vecOK n v = true → ∀ x < 31671, imgV H n v x = act (E v) x) :
    ∀ Ls : List (ℕ × List ℕ), chainB H n Ls = true →
      ChainP act (Ls.map fun l => (l.1, l.2.map E)) ∧ ∀ l ∈ Ls, ∀ v ∈ l.2, vecOK n v = true
  | [], _ => ⟨trivial, fun _ h => absurd h List.not_mem_nil⟩
  | l :: R, h => by
    change (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false (chainB H n R) (fixL H n l.1 R))
          (nodupN (l.2.map fun v => imgV H n v l.1)))
        (allL l.2 (vecOK n)))
      (Nat.blt l.1 31671)) = true at h
    simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨hp, hv, hd, hf, hR⟩ := h
    rw [Nat.blt_eq] at hp
    rw [allL_iff] at hv
    rw [nodupN_iff] at hd
    rw [fixL_iff] at hf
    obtain ⟨ihC, ihV⟩ := chainP_of hW R hR
    have hmap : (l.2.map fun v => imgV H n v l.1) = (l.2.map E).map fun y => act y l.1 := by
      rw [List.map_map]
      exact List.map_congr_left fun v hv' => hW v (hv v hv') l.1 hp
    refine ⟨⟨by rw [← hmap]; exact hd, ?_, ihC⟩, ?_⟩
    · intro m hm y hy
      obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
      obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hy
      rw [← hW v (ihV m' hm' v hv') l.1 hp]
      exact hf m' hm' v hv'
    · intro l' hl' v hv'
      rcases List.mem_cons.1 hl' with rfl | hl'
      · exact hv v hv'
      · exact ihV l' hl' v hv'

theorem length_le_card [Finite G] (K : Subgroup G) {L : List G} (hL : L.Nodup)
    (hK : ∀ z ∈ L, z ∈ K) : L.length ≤ Nat.card K := by
  classical
  rw [← List.toFinset_card_of_nodup hL, ← Set.ncard_coe_finset]
  change _ ≤ Nat.card (K : Set G)
  rw [Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard (fun z hz => hK z (List.mem_toFinset.1 hz))

end CFSG.KS.Fi23Q

end

module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.KC.B433Alt

open Subgroup

variable {n : ℕ}

theorem length_le_ncard_orbit (S : Set (Equiv.Perm (Fin n))) (b : ℕ) (hb : b < n) (P : List ℕ)
    (hlt : ∀ p ∈ P, p < n) (h0 : P.head? = some b)
    (hstep : ∀ i (hi : i < P.length), 0 < i → ∃ j < i, ∃ hj : j < P.length, ∃ g ∈ closure S,
      (g ⟨P[j], hlt _ (List.getElem_mem hj)⟩ : ℕ) = P[i])
    (hnd : P.Nodup) : P.length ≤ (MulAction.orbit (closure S) (⟨b, hb⟩ : Fin n)).ncard := by
  classical
  have hmem : ∀ i (hi : i < P.length), (⟨P[i], hlt _ (List.getElem_mem hi)⟩ : Fin n) ∈
      MulAction.orbit (closure S) (⟨b, hb⟩ : Fin n) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hi, Option.some_inj] at h0
        have e : (⟨P[0], hlt _ (List.getElem_mem hi)⟩ : Fin n) = ⟨b, hb⟩ := Fin.ext h0
        rw [e]
        exact MulAction.mem_orbit_self _
      · obtain ⟨j, hj, hjl, g, hg, hgj⟩ := hstep i hi hpos
        obtain ⟨⟨h, hh⟩, hhb⟩ := ih j hj hjl
        refine ⟨⟨g * h, (closure S).mul_mem hg hh⟩, ?_⟩
        apply Fin.ext
        change ((g * h) ⟨b, hb⟩ : ℕ) = P[i]
        rw [Equiv.Perm.mul_apply]
        have hhb' : h ⟨b, hb⟩ = ⟨P[j], hlt _ (List.getElem_mem hjl)⟩ := hhb
        rw [hhb', hgj]
  let F : List (Fin n) := P.pmap (fun p hp => (⟨p, hp⟩ : Fin n)) hlt
  have hF : F.Nodup := List.Nodup.pmap (fun _ _ _ _ h => congrArg Fin.val h) hnd
  have hsub : (↑F.toFinset : Set (Fin n)) ⊆ MulAction.orbit (closure S) (⟨b, hb⟩ : Fin n) := by
    intro x hx
    obtain ⟨i, hi, hx'⟩ := List.getElem_of_mem (List.mem_toFinset.1 hx)
    rw [← hx', List.getElem_pmap]
    exact hmem i (by simpa [F] using hi)
  have hlen : F.length = P.length := List.length_pmap
  calc P.length = F.toFinset.card := by rw [List.toFinset_card_of_nodup hF, hlen]
    _ = (↑F.toFinset : Set (Fin n)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub

@[expose] def lvSet : List (Fin n × Set (Equiv.Perm (Fin n)) × ℕ) → Set (Equiv.Perm (Fin n))
  | [] => ∅
  | x :: l => x.2.1 ∪ lvSet l

@[expose] def LvValid (E : Set (Equiv.Perm (Fin n))) :
    List (Fin n × Set (Equiv.Perm (Fin n)) × ℕ) → Prop
  | [] => True
  | x :: l => (∀ g ∈ E ∪ lvSet l, g x.1 = x.1) ∧
      x.2.2 ≤ (MulAction.orbit (closure x.2.1) x.1).ncard ∧ LvValid E l

theorem level_le_card (S R : Set (Equiv.Perm (Fin n))) (b : Fin n) (c : ℕ)
    (hR : ∀ g ∈ R, g b = b) (hc : c ≤ (MulAction.orbit (closure S) b).ncard) :
    c * Nat.card (closure R) ≤ Nat.card (closure (S ∪ R)) := by
  classical
  set H := closure (S ∪ R) with hH
  have hSH : closure S ≤ H := closure_mono Set.subset_union_left
  have hRH : closure R ≤ H := closure_mono Set.subset_union_right
  have horb : (MulAction.orbit (closure S) b).ncard ≤ (MulAction.orbit H b).ncard := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro x ⟨⟨g, hg⟩, rfl⟩
    exact ⟨⟨g, hSH hg⟩, rfl⟩
  have hfixR : ∀ g ∈ closure R, g b = b := by
    intro g hg
    induction hg using closure_induction with
    | mem g hg => exact hR g hg
    | one => rfl
    | mul x y _ _ hx hy => rw [Equiv.Perm.mul_apply, hy, hx]
    | inv x _ hx =>
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hx.symm
  have hstab : Nat.card (closure R) ≤ Nat.card (MulAction.stabilizer H b) := by
    refine Nat.card_le_card_of_injective
      (fun g => ⟨⟨g, hRH g.2⟩, (MulAction.mem_stabilizer_iff).2 (hfixR g g.2)⟩) ?_
    intro g h hgh
    apply Subtype.ext
    have := congrArg (fun x : MulAction.stabilizer H b => ((x : H) : Equiv.Perm (Fin n))) hgh
    exact this
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer H b)
  rw [MulAction.index_stabilizer] at hcard
  calc c * Nat.card (closure R) ≤ (MulAction.orbit H b).ncard * Nat.card (MulAction.stabilizer H b) :=
        Nat.mul_le_mul (hc.trans horb) hstab
    _ = Nat.card H := by rw [mul_comm]; exact hcard

theorem chain_le_card (E : Set (Equiv.Perm (Fin n))) (q : ℕ) (hq : q ≤ Nat.card (closure E)) :
    ∀ lv : List (Fin n × Set (Equiv.Perm (Fin n)) × ℕ), LvValid E lv →
      (lv.map fun x => x.2.2).prod * q ≤ Nat.card (closure (E ∪ lvSet lv))
  | [], _ => by simpa [lvSet] using hq
  | x :: l, ⟨hfix, hc, hl⟩ => by
    have ih := chain_le_card E q hq l hl
    have h1 := level_le_card x.2.1 (E ∪ lvSet l) x.1 x.2.2 hfix hc
    have e : x.2.1 ∪ (E ∪ lvSet l) = E ∪ lvSet (x :: l) := by
      simp only [lvSet]
      ext g
      simp only [Set.mem_union]
      tauto
    rw [e] at h1
    calc ((x :: l).map fun x => x.2.2).prod * q = x.2.2 * ((l.map fun x => x.2.2).prod * q) := by
          simp only [List.map_cons, List.prod_cons]
          ring
      _ ≤ x.2.2 * Nat.card (closure (E ∪ lvSet l)) := Nat.mul_le_mul_left _ ih
      _ ≤ _ := h1

theorem lcm_le_card (E : List (Equiv.Perm (Fin n))) :
    (E.map orderOf).foldr Nat.lcm 1 ≤ Nat.card (closure {g | g ∈ E}) := by
  have hdvd : ∀ l : List (Equiv.Perm (Fin n)), (∀ g ∈ l, g ∈ closure {g | g ∈ E}) →
      (l.map orderOf).foldr Nat.lcm 1 ∣ Nat.card (closure {g | g ∈ E}) := by
    intro l
    induction l with
    | nil => intro _; exact one_dvd _
    | cons g l ih =>
      intro hl
      simp only [List.map_cons, List.foldr_cons]
      refine Nat.lcm_dvd ?_ (ih fun h hh => hl h (List.mem_cons_of_mem _ hh))
      have := orderOf_dvd_natCard (⟨g, hl g List.mem_cons_self⟩ : closure {g | g ∈ E})
      rwa [Subgroup.orderOf_mk] at this
  exact Nat.le_of_dvd Nat.card_pos (hdvd E fun g hg => subset_closure hg)

theorem card_ge_25 {G : Type*} [Group G] [Finite G] {x y : G} (hx : x ^ 5 = 1) (hx1 : x ≠ 1)
    (hy : y ^ 5 = 1) (hxy : x * y = y * x) (hyx : ∀ i < 5, y ≠ x ^ i) :
    25 ≤ Nat.card (closure ({x, y} : Set G)) := by
  classical
  have hp : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set P := closure ({x, y} : Set G) with hP
  have hc : ∀ a ∈ ({x, y} : Set G), ∀ b ∈ ({x, y} : Set G), a * b = b * a := by
    rintro a (rfl | rfl) b (rfl | rfl)
    · rfl
    · exact hxy
    · exact hxy.symm
    · rfl
  have hexp : ∀ g ∈ P, g ^ 5 = 1 := by
    have hc' : ∀ g ∈ P, ∀ h ∈ P, g * h = h * g := fun g hg h hh =>
      Set.centralizer_centralizer_comm_of_comm (fun a ha b hb _ => hc a ha b hb) g
        (closure_le_centralizer_centralizer _ hg) h (closure_le_centralizer_centralizer _ hh)
    intro g hg
    induction hg using closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl
      · exact hx
      · exact hy
    | one => exact one_pow 5
    | mul a b ha hb iha ihb => rw [(Commute.mul_pow (hc' a ha b hb) 5), iha, ihb, one_mul]
    | inv a _ ih => rw [inv_pow, ih, inv_one]
  have hpg : IsPGroup 5 P := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hexp g g.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hpg
  have hox : orderOf x = 5 := orderOf_eq_prime hx hx1
  have hzle : zpowers x ≤ P := (zpowers_le).2 (subset_closure (Set.mem_insert x _))
  have hyP : y ∈ P := subset_closure (Set.mem_insert_of_mem x rfl)
  have hyz : y ∉ zpowers x := by
    rintro ⟨k, hk⟩
    apply hyx (k % 5).toNat (by omega)
    rw [← hk]
    change x ^ k = x ^ (k % 5).toNat
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    have h := zpow_mod_orderOf x k
    rw [hox] at h
    exact h.symm
  have hlt : zpowers x < P := lt_of_le_of_ne hzle fun h => hyz (h ▸ hyP)
  have hcardlt : Nat.card (zpowers x) < Nat.card P := Subgroup.card_lt_of_lt hlt
  rw [Nat.card_zpowers, hox, hm] at hcardlt
  have hm2 : 2 ≤ m := by
    by_contra h
    push Not at h
    interval_cases m <;> simp at hcardlt
  rw [hm]
  calc 25 = 5 ^ 2 := by norm_num
    _ ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) hm2

end CFSG.KC.B433Alt

end

module

public import CFSG.Certificates.Kernel.Sp6Insp443.CentSound
public import CFSG.Certificates.Kernel.Sp6Insp443.SixSound
public import Certificates.Data.Kernel.Sp6Insp443.Six

public section

namespace CFSG.KS.Sp6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31

variable {n w : Nat}

theorem mprod_succ_left (x : Nat → Equiv.Perm (Fin n)) (m k : Nat) :
    mprod x m (k + 1) = bitSel x m 0 * mprod (fun j => x (j + 1)) (m / 2) k := by
  rw [mprod, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, mprod]
  congr 1
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, bitSel, Nat.succ_eq_add_one, shiftRight_succ_half]

theorem exists_mprod_eq_eElt : ∀ {k : Nat} (x : Nat → Equiv.Perm (Fin n)) (c : Fin k → ZMod 2),
    ∃ s < 2 ^ k, mprod x s k = eElt (fun i : Fin k => x i) c
  | 0, x, c => ⟨0, by norm_num, by rw [mprod_zero]; simp [eElt]⟩
  | k + 1, x, c => by
    obtain ⟨s, hs, e⟩ := exists_mprod_eq_eElt (fun j => x (j + 1)) (fun i => c i.succ)
    have hc := ZMod.val_lt (c 0)
    refine ⟨(c 0).val + 2 * s, by rw [pow_succ]; omega, ?_⟩
    rw [mprod_succ_left, eElt_succ]
    have h2 : ((c 0).val + 2 * s) / 2 = s := by omega
    rw [h2, e]
    congr 1
    unfold bitSel
    rw [land_shiftRight_zero]
    have h3 : ((c 0).val + 2 * s) % 2 = (c 0).val := by omega
    rw [h3]
    have h4 : (c 0).val = 0 ∨ (c 0).val = 1 := by omega
    rcases h4 with h4 | h4
    · rw [if_pos h4, h4, pow_zero]
    · rw [if_neg (by omega), h4, pow_one]
      rfl

theorem mprod_mem_closure (x : Nat → Equiv.Perm (Fin n)) (s k : Nat) :
    mprod x s k ∈ Subgroup.closure (Set.range fun i : Fin k => x i) := by
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  unfold bitSel
  split_ifs
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨⟨j, List.mem_range.1 hj⟩, rfl⟩

theorem exists_mprod_of_mem_closure {k : Nat} {x : Nat → Equiv.Perm (Fin n)}
    (hsq : ∀ j < k, x j * x j = 1) (hc : ∀ i < k, ∀ j < k, Commute (x i) (x j))
    {a : Equiv.Perm (Fin n)} (ha : a ∈ Subgroup.closure (Set.range fun i : Fin k => x i)) :
    ∃ s < 2 ^ k, mprod x s k = a := by
  obtain ⟨c, rfl⟩ := exists_eElt_of_mem_closure (fun i => hsq i i.2) (fun i j => hc i i.2 j j.2) ha
  exact exists_mprod_eq_eElt x c

theorem exists_lanes_inv {P c : Nat}
    (h : allN c (fun j => permOK n w (mask w) (n * w) (laneK (n * w) P j)
      (laneK (n * w) P j)) = true) :
    ∃ x : Nat → Equiv.Perm (Fin n), ∀ j < c, PRep n w (laneK (n * w) P j) (x j) ∧ x j * x j = 1 := by
  have h0 : ∀ j, ∃ v : Equiv.Perm (Fin n), j < c →
      PRep n w (laneK (n * w) P j) v ∧ v * v = 1 := by
    intro j
    by_cases hj : j < c
    · have hp := Orb.allN_iff.1 h j hj
      obtain ⟨v, hv⟩ := SporSch.MOC.exists_prep hp
      refine ⟨v, fun _ => ⟨hv, ?_⟩⟩
      have hvi := prep_inv_of_permOK hp hv
      have e := SporSch.MOC.prep_unique hv hvi
      calc v * v = v * v⁻¹ := by rw [← e]
        _ = 1 := mul_inv_cancel v
    · exact ⟨1, fun h' => absurd h' hj⟩
  choose x hx using h0
  exact ⟨x, fun j hj => hx j hj⟩

theorem forall₂_of_tabsPK {P c : Nat} {Ts : List Table} {x : Nat → Equiv.Perm (Fin n)}
    (hT : tabsPK n w (mask w) (n * w) P Ts 0 = true) (hlen : Ts.length = c)
    (hx : ∀ j < c, PRep n w (laneK (n * w) P j) (x j)) :
    List.Forall₂ (Rep n) Ts (List.ofFn fun i : Fin c => x i) := by
  subst hlen
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h1 h2 => ?_⟩
  have := rep_of_tabPK (hx i h1) (by simpa using tabsPK_spec hT i h1)
  simpa [List.getElem?_eq_getElem h1] using this

theorem commute_of_commPK (hn : n < 2 ^ 32) (hw : 0 < w) {P c : Nat}
    {x : Nat → Equiv.Perm (Fin n)} (hx : ∀ j < c, PRep n w (laneK (n * w) P j) (x j))
    (h : allN c (fun i => commPK n w (mask w) (n * w) P c (laneK (n * w) P i)) = true) :
    ∀ i < c, ∀ j < c, Commute (x i) (x j) := fun i hi j hj =>
  ((commPK_iff hn hw (hx i hi) c hx).1 (Orb.allN_iff.1 h i hi)) j hj

theorem memPK_span_iff (hn : n < 2 ^ 32) (hw : 0 < w) {idn P S c G : Nat}
    {x : Nat → Equiv.Perm (Fin n)} (hid : PRep n w idn 1)
    (hx : ∀ j < c, PRep n w (laneK (n * w) P j) (x j)) (hsq : ∀ j < c, x j * x j = 1)
    (hc : ∀ i < c, ∀ j < c, Commute (x i) (x j))
    (hsp : spanPK n w (mask w) (n * w) idn P S c = true) {g : Equiv.Perm (Fin n)}
    (hG : PRep n w G g) (sG : G >>> (n * w) = 0) :
    memPK (n * w) S (2 ^ c) G = true ↔ g ∈ Subgroup.closure (Set.range fun i : Fin c => x i) := by
  rw [memPK_iff hw hG sG _ (spanPK_prep hn hid hsp hx)]
  constructor
  · rintro ⟨s, -, rfl⟩
    exact mprod_mem_closure x s c
  · intro h
    exact exists_mprod_of_mem_closure hsq hc h

theorem patK_congr {nw c : Nat} {S : Nat → Nat} {g g' : Nat} : ∀ m,
    (∀ r < m, memPK nw (S r) c g = memPK nw (S r) c g') → patK nw S c m g = patK nw S c m g'
  | 0, _ => rfl
  | m + 1, h => by
    have e : ∀ q, patK nw S c (m + 1) q =
        Nat.add (patK nw S c m q) (nIf(memPK nw (S m) c q, Nat.shiftLeft (nat_lit 1) m,
          nat_lit 0)) := fun q => rfl
    rw [e, e, patK_congr m (fun r hr => h r (by omega)), h m (by omega)]

end CFSG.KS.Sp6I

end

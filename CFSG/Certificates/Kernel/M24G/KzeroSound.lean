module

public import Certificates.Data.Kernel.M24G.Kzero
import CFSG.Certificates.Kernel.M24G.BfsReplaySound
import CFSG.Certificates.Kernel.M24G.ReplayFacts
import CFSG.Certificates.Kernel.M24G.IdxSound
import CFSG.Certificates.Kernel.M24G.FixOctSound
public import CFSG.Certificates.Kernel.M24G.DuadSound

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G
open scoped CFSG.KC.M24G.FixOctEq

theorem kzeroMul_eq (a b : Array Nat) : Native.kzeroMul a b = mulTabF a b := by
  unfold Native.kzeroMul mulTabF
  rw [range24_map]
  simp only [get!_nat]

theorem kzeroKey_eq : Native.kzeroKey = kzeroKeyF := by
  funext t
  unfold kzeroKeyF
  split
  · rename_i h
    unfold Native.kzeroKey
    have e := duad_map_getD t.toList (by rw [Array.length_toList, h])
    rw [← e, List.foldl_map]
    simp only [get!_nat]
  · rfl

theorem kzeroSteps_eq : Native.s0Tabs.map Native.kzeroMul = kzeroStepsF := by
  unfold kzeroStepsF
  congr 1
  funext a b
  exact kzeroMul_eq a b

theorem kz_foldl_inj : ∀ (l1 l2 : List Nat) (c1 c2 : Nat), l1.length = l2.length →
    (∀ x ∈ l1, x < 24) → (∀ x ∈ l2, x < 24) →
    l1.foldl (fun acc x => (acc <<< 5) ||| x) c1 = l2.foldl (fun acc x => (acc <<< 5) ||| x) c2 →
    c1 = c2 ∧ l1 = l2
  | [], [], c1, c2, _, _, _, h => ⟨by simpa using h, rfl⟩
  | x :: l1, y :: l2, c1, c2, hl, h1, h2, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨e, rfl⟩ := kz_foldl_inj l1 l2 _ _ (by simpa using hl)
      (fun z hz => h1 z (List.mem_cons_of_mem _ hz)) (fun z hz => h2 z (List.mem_cons_of_mem _ hz)) h
    have hx := h1 x List.mem_cons_self
    have hy := h2 y List.mem_cons_self
    have h32 : (2 : Nat) ^ 5 = 32 := rfl
    rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.lt_of_lt_of_le hx (by decide)),
      ← Nat.shiftLeft_add_eq_or_of_lt (Nat.lt_of_lt_of_le hy (by decide)), Nat.shiftLeft_eq,
      Nat.shiftLeft_eq, h32] at e
    have e2 : c1 = c2 ∧ x = y := by omega
    exact ⟨e2.1, by rw [e2.2]⟩
  | [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _ => by simp at hl

theorem kzeroKeyF_inj {a b : Array Nat} (ha : DuadV a) (hb : DuadV b)
    (e : kzeroKeyF a = kzeroKeyF b) : a = b := by
  unfold kzeroKeyF at e
  rw [if_pos ha.1, if_pos hb.1] at e
  exact Array.toList_inj.1 (kz_foldl_inj _ _ 0 0 (by rw [Array.length_toList, Array.length_toList,
    ha.1, hb.1]) ha.2 hb.2 e).2

variable {fuel : Nat} {L : List (Array Nat)} {par gen : List Nat} {pos : KTree (Nat × Nat)}

theorem kz_LV (h : replayOK kzeroKeyF kzeroStepsF Native.kzeroId fuel L par gen pos = true) :
    ∀ y ∈ L, DuadV y := by
  have hS : ∀ g ∈ Native.s0Tabs, duadValidT g = true := by decide
  refine replay_induction h DuadV (duadV_of _ (by decide)) fun x _ s hs => ?_
  unfold kzeroStepsF at hs
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hs
  exact duadV_mulTabF (duadV_of g (hS g hg)) x

theorem kzeroSyl_eq
    (h : replayOK kzeroKeyF kzeroStepsF Native.kzeroId 1100 L par gen pos = true) :
    Native.kzeroSyl () = (L.toArray, par.toArray, gen.toArray) := by
  unfold Native.kzeroSyl
  rw [kzeroKey_eq, kzeroSteps_eq]
  exact bfs_eq_of_replayOK h

theorem kzeroPair_eq : (Native.kzeroHs ()).getD 4 (#[], #[]) = kzeroPairF := rfl

theorem kzeroK0List_eq {KL : List (Array Nat)}
    (h : replayOK kzeroKeyF kzeroStepsF Native.kzeroId 1100 L par gen pos = true)
    (hk : kzeroK0F pos L kzeroPairF = KL) : Native.kzeroK0List () = KL := by
  have hpos := (replay_facts h).1
  have hV := kz_LV h
  have hp1 : DuadV kzeroPairF.1 := duadV_of _ (by decide)
  unfold Native.kzeroK0List Native.kzeroK0
  rw [kzeroSyl_eq h, kzeroPair_eq, ← hk]
  simp only [List.toList_toArray]
  unfold kzeroK0F
  apply List.filter_congr
  intro t _
  rw [Bool.eq_iff_iff, Array.contains_iff, List.mem_toArray, Option.isSome_iff_exists,
    Native.kzeroConj, kzeroMul_eq, kzeroMul_eq]
  have hy : DuadV (mulTabF kzeroPairF.1 (mulTabF t kzeroPairF.2)) := duadV_mulTabF hp1 _
  constructor
  · intro hm
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hm
    refine ⟨i, (findK_eq_some kzeroKeyF hpos _ i).2 ⟨hi, ?_⟩⟩
    unfold kzeroConjF
    rw [e]
  · rintro ⟨i, hf⟩
    obtain ⟨hi, e⟩ := (findK_eq_some kzeroKeyF hpos _ i).1 hf
    unfold kzeroConjF at e
    rw [← kzeroKeyF_inj (hV _ (List.getElem_mem hi)) hy e]
    exact List.getElem_mem hi

end CFSG.KC.M24G

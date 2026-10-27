module

public import CFSG.Quasithin.Background.HMathieuBits

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelOrbitBits

open CFSG.Quasithin.H.Mathieu

@[expose] def pushNew (todo : List ℕ) (seen : ℕ) : List ℕ → List ℕ × ℕ
  | [] => (todo, seen)
  | n :: ns =>
    if seen.testBit n then pushNew todo seen ns
    else pushNew (n :: todo) (seen ||| 1 <<< n) ns

@[expose] def orbitBits (cs : List (List ℕ)) : ℕ → List ℕ → ℕ → ℕ
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, m :: todo, seen =>
    let r := pushNew todo seen (cs.map fun c => actM c m)
    orbitBits cs fuel r.1 r.2

theorem pushNew_spec (P : ℕ → Prop) : ∀ (ns todo : List ℕ) (seen : ℕ), (∀ n ∈ ns, P n) →
    (∀ m ∈ todo, P m) → (∀ n, seen.testBit n = true → P n) →
    (∀ m ∈ (pushNew todo seen ns).1, P m) ∧
      ∀ n, (pushNew todo seen ns).2.testBit n = true → P n
  | [], todo, seen, _, ht, hs => ⟨ht, hs⟩
  | n :: ns, todo, seen, hn, ht, hs => by
    have hPn : P n := hn n List.mem_cons_self
    have hns : ∀ k ∈ ns, P k := fun k hk => hn k (List.mem_cons_of_mem n hk)
    by_cases h : seen.testBit n = true
    · rw [pushNew, if_pos h]
      exact pushNew_spec P ns todo seen hns ht hs
    · rw [pushNew, if_neg h]
      refine pushNew_spec P ns (n :: todo) (seen ||| 1 <<< n) hns (fun m hm => ?_) (fun k hk => ?_)
      · rcases List.mem_cons.1 hm with rfl | hm
        · exact hPn
        · exact ht m hm
      · rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow] at hk
        rcases hk with hk | hk
        · exact hs k hk
        · rw [← of_decide_eq_true hk]
          exact hPn

theorem orbitBits_spec (cs : List (List ℕ)) (P : ℕ → Prop)
    (hP : ∀ c ∈ cs, ∀ m, P m → P (actM c m)) :
    ∀ (fuel : ℕ) (todo : List ℕ) (seen : ℕ), (∀ m ∈ todo, P m) →
      (∀ n, seen.testBit n = true → P n) →
      ∀ n, (orbitBits cs fuel todo seen).testBit n = true → P n
  | 0, _, _, _, hs => hs
  | _ + 1, [], _, _, hs => hs
  | fuel + 1, m :: todo, seen, ht, hs => by
    have hPm : P m := ht m List.mem_cons_self
    have hns : ∀ n ∈ cs.map (fun c => actM c m), P n := by
      intro n hn
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hn
      exact hP c hc m hPm
    obtain ⟨h1, h2⟩ := pushNew_spec P _ todo seen hns
      (fun k hk => ht k (List.mem_cons_of_mem m hk)) hs
    exact orbitBits_spec cs P hP fuel _ _ h1 h2

theorem orbitBits_root_spec (cs : List (List ℕ)) (P : ℕ → Prop)
    (hP : ∀ c ∈ cs, ∀ m, P m → P (actM c m)) (r : ℕ) (hr : P r) (fuel : ℕ) :
    ∀ n, (orbitBits cs fuel [r] (1 <<< r)).testBit n = true → P n := by
  refine orbitBits_spec cs P hP fuel [r] (1 <<< r) (fun m hm => ?_) (fun n hn => ?_)
  · rw [List.mem_singleton.1 hm]
    exact hr
  · rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hn
    rw [← of_decide_eq_true hn]
    exact hr

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelOrbitBits

module

public import CFSG.Certificates.Kernel.Co1Sub.SlpSound

public section

namespace CFSG.KC.Co1Sub

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.TabMatGrp

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

theorem invsK_spec : ∀ {B Bi : List Nat}, invsK B Bi = true →
    Bi.length = B.length ∧ ∀ i < B.length, mulS (B.getD i 0) (Bi.getD i 0) = oneS
  | [], [], _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | m :: B, mi :: Bi, h => by
    change andB (Nat.beq (mulS m mi) oneS) (invsK B Bi) = true at h
    rw [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨l, hs⟩ := invsK_spec h.2
    refine ⟨by simp [l], fun i hi => ?_⟩
    rcases i with _ | i
    · exact h.1
    · exact hs i (by simpa using hi)

theorem pickL_eq (L : List Nat) : ∀ idx : List Nat, pickL L idx = idx.map fun i => L.getD i 0
  | [] => rfl
  | i :: idx => by
    change getL 0 L i :: pickL L idx = _
    rw [getL_zero_eq, pickL_eq L idx, List.map_cons]

theorem slpK_spec {B Bi M Mi : List Nat} {W : List (List Nat)} (h : slpK B Bi W M Mi = true) :
    M.length = W.length ∧ Mi.length = W.length ∧
      ∀ t < W.length, ∀ c ∈ W.getD t [], c / 2 < B.length + t := by
  unfold slpK at h
  rw [strictB_eq, lenL_eq_length] at h
  obtain ⟨h1, h2, hs⟩ := slpAt_spec W 0 h
  exact ⟨by simpa using h1, by simpa using h2, fun t ht => by simpa using (hs t ht).1⟩

variable {G : Type*} [Group G] {φ : G →* GL (Fin 24) (ZMod 2)}

@[expose] noncomputable def slpVal (base : ℕ → G) (nB : ℕ) (W : List (List ℕ)) (k : ℕ) : G :=
  if k < nB then base k else
    ((W.getD (k - nB) []).map fun c => if _h : c / 2 < k then
      (if c % 2 = 1 then (slpVal base nB W (c / 2))⁻¹ else slpVal base nB W (c / 2)) else 1).prod
termination_by k

theorem slpVal_base (base : ℕ → G) (nB : ℕ) (W : List (List ℕ)) {k : ℕ} (hk : k < nB) :
    slpVal base nB W k = base k := by
  rw [slpVal, if_pos hk]

theorem slpVal_word (base : ℕ → G) (nB : ℕ) (W : List (List ℕ)) (t : ℕ)
    (hr : ∀ c ∈ W.getD t [], c / 2 < nB + t) :
    slpVal base nB W (nB + t) = ((W.getD t []).map (letG (slpVal base nB W))).prod := by
  rw [slpVal, if_neg (by omega), Nat.add_sub_cancel_left]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  rw [dif_pos (hr c hc)]
  rfl

theorem slpVal_mem (base : ℕ → G) (nB : ℕ) (W : List (List ℕ)) (K : Subgroup G)
    (hK : ∀ i < nB, base i ∈ K) : ∀ k, slpVal base nB W k ∈ K := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [slpVal]
    split_ifs with hk
    · exact hK k hk
    · refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      split_ifs with h1 h2
      · exact K.inv_mem (ih _ h1)
      · exact ih _ h1
      · exact K.one_mem

theorem slpK_mem {base : ℕ → G} (K : Subgroup G) {B Bi M Mi : List Nat} {W : List (List Nat)}
    (h : slpK B Bi W M Mi = true)
    (hB : ∀ i < B.length, MatP 24 (B.getD i 0) = matOf φ (base i) ∧
      MatP 24 (Bi.getD i 0) = matOf φ (base i)⁻¹)
    (hK : ∀ i < B.length, base i ∈ K) :
    ∀ t < W.length, ∃ g ∈ K, MatP 24 (M.getD t 0) = matOf φ g ∧
      MatP 24 (Mi.getD t 0) = matOf φ g⁻¹ := by
  obtain ⟨-, -, hr⟩ := slpK_spec h
  have hB' : ∀ i < B.length, MatP 24 (B.getD i 0) = matOf φ (slpVal base B.length W i) ∧
      MatP 24 (Bi.getD i 0) = matOf φ (slpVal base B.length W i)⁻¹ := fun i hi => by
    rw [slpVal_base base _ W hi]
    exact hB i hi
  have hs := slpK_sound h hB' fun t ht => slpVal_word base _ W t (hr t ht)
  intro t ht
  obtain ⟨-, h1, h2⟩ := hs t ht
  exact ⟨_, slpVal_mem base _ W K hK _, h1, h2⟩

end CFSG.KC.Co1Sub

end

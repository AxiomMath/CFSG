module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRootR
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Roots
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Tests

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co2

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification.RankTwoSporadic.RootR
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.KC.Census CFSG.KC.Census.Base CFSG.Certificates CFSG.Sporadic.Co2Cert
  CFSG.Sporadic.Co2Schreier

@[expose] def co2BaseR : List ℕ := [0, 1, 2, 3, 5, 4]

@[expose] def co2Deg : List ℕ := [32, 32, 24]

@[expose] def co2Len : List ℕ := [18, 17, 15]

@[expose] noncomputable def co2CheckR (L : ℕ → ℕ) (pxs : List ℕ) (rs : List RootR) : Bool :=
  (List.range 11).all (fun k => eqA 2300 (unpackP 2300 12 (L k)) co2StrongArrs[k]!) &&
    invLB 12 11 L 2300 && Nat.beq pxs.length 3 && Nat.beq rs.length 3 &&
    (List.range 3).all fun i =>
      eqA 2300 (unpackP 2300 12 (pxs.getD i 0)) (co2Xs.getD i #[]) &&
      Nat.beq (rs.getD i default).d.xs.length (co2Len.getD i 0) &&
      rootCheckR 2300 12 11 L co2BaseR (co2Deg.getD i 0) 5 pxs i (rs.getD i default)

section P


theorem co2StrongR_mem {k : ℕ} (hk : k < 11) : permOfArr 2300 co2StrongArrs[k]! ∈ co2P := by
  have hc : k < co2Q.strongCount := by rw [co2Q_strongCount]; exact hk
  have h := RawSchreierDatum.strong_get_mem_originalSubgroup co2Q co2Q_valid.1 ⟨k, hc⟩
  rw [co2Q_strong_get, co2Q_originalSubgroup] at h
  exact h

theorem co2BaseOf : BaseOf co2P co2BaseR := by
  refine ⟨by decide, fun g hg h => ?_⟩
  have hQ : ValidSchreier co2Q := co2Q_valid.1
  obtain ⟨hlev, hterm, -⟩ := RawSchreierDatum.schreier_chain_order co2Q hQ
  have h1 := hlev co2Q.baseCount le_rfl
  rw [hterm] at h1
  have hmem : g ∈ co2Q.originalSubgroup ⊓ fixingSubgroup (Equiv.Perm (Fin 2300))
      {b | b ∈ co2Q.base.toList.take co2Q.baseCount} := by
    rw [Subgroup.mem_inf]
    refine ⟨by rw [co2Q_originalSubgroup]; exact hg, ?_⟩
    rw [mem_fixingSubgroup_iff]
    intro b hb
    have hb' : b.val ∈ co2Q.base.toList.map Fin.val := List.mem_map_of_mem (List.mem_of_mem_take hb)
    rw [co2Q_base] at hb'
    exact h b.val b.2 hb'
  rw [← h1] at hmem
  exact Subgroup.mem_bot.1 hmem

end P

@[expose] noncomputable def co2Let (k : ℕ) : Equiv.Perm (Fin 2300) :=
  if k < 11 then permOfArr 2300 co2StrongArrs[k]! else (permOfArr 2300 co2StrongArrs[k - 11]!)⁻¹

set_option maxRecDepth 100000 in
theorem co2Letters_of {L : ℕ → ℕ}
    (h1 : (List.range 11).all (fun k => eqA 2300 (unpackP 2300 12 (L k)) co2StrongArrs[k]!) =
      true) (h2 : invLB 12 11 L 2300 = true) : Letters 2300 12 11 L co2Let := by
  have hinv : ∀ k < 11, ∀ p < 2300, at' 12 (L k) p < 2300 ∧
      at' 12 (L (11 + k)) (at' 12 (L k) p) = p := by
    intro k hk p hp
    unfold invLB at h2
    have := List.all_eq_true.1 (List.all_eq_true.1 h2 k (List.mem_range.2 hk)) p
      (List.mem_range.2 hp)
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at this
    exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩
  have hrep : ∀ k < 11, Rep 2300 co2StrongArrs[k]! (permOfArr 2300 co2StrongArrs[k]!) ∧
      ∀ p < 2300, (co2StrongArrs[k]!)[p]! = at' 12 (L k) p := by
    intro k hk
    have he := List.all_eq_true.1 h1 k (List.mem_range.2 hk)
    have hget : ∀ p < 2300, (co2StrongArrs[k]!)[p]! = at' 12 (L k) p := by
      intro p hp
      have := allLt_spec he hp
      rw [beq_iff_eq, SP.unpackP_get, if_pos hp] at this
      exact this.symm
    refine ⟨(rep_permOfArr (r := unpackP 2300 12 (L (11 + k))) ?_).1, hget⟩
    unfold isInvA
    rw [allLt_iff]
    intro i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [hget i hi, SP.unpackP_get, if_pos (hinv k hk i hi).1]
    exact hinv k hk i hi
  refine ⟨fun k hk p hp => ?_, fun k hk => ?_⟩
  · by_cases h11 : k < 11
    · rw [co2Let, if_pos h11, ← (hrep k h11).1.apply hp, (hrep k h11).2 p hp]
    · have hj : k - 11 < 11 := by omega
      rw [co2Let, if_neg h11]
      set g := permOfArr 2300 co2StrongArrs[k - 11]!
      set q := g⁻¹ ⟨p, hp⟩
      have hq : at' 12 (L (k - 11)) q = p := by
        rw [← (hrep _ hj).2 q q.2, (hrep _ hj).1.apply q.2]
        change ((g (g⁻¹ ⟨p, hp⟩) : Fin 2300) : ℕ) = p
        simp
      have := (hinv _ hj q q.2).2
      rw [hq, show 11 + (k - 11) = k by omega] at this
      exact this
  · simp only [co2Let, if_pos hk, if_neg (show ¬ 11 + k < 11 by omega),
      show 11 + k - 11 = k by omega]

theorem co2Let_mem {k : ℕ}
    (hk : k < 2 * 11) : co2Let k ∈ co2P := by
  unfold co2Let
  split_ifs with h
  · exact co2StrongR_mem h
  · exact co2P.inv_mem (co2StrongR_mem (by omega))

theorem root_in_W {n : ℕ} {W : Subgroup (Equiv.Perm (Fin n))} (x : ↥W) (y : ℕ → ↥W) (i : ℕ)
    {T : Subgroup (Equiv.Perm (Fin n))} (hT : T ≤ W ⊓ centralizer {(x : Equiv.Perm (Fin n))})
    (hcard : Nat.card T =
      2 ^ (Nat.card ↥(W ⊓ centralizer {(x : Equiv.Perm (Fin n))})).factorization 2)
    (hw : ∀ b ∈ T, b ^ 2 = 1 → b ≠ 1 → b ≠ x → MonoW W true (closure {(x : Equiv.Perm (Fin n)), b}) ∨
      ∃ j < i, ∃ g ∈ W, g * b * g⁻¹ = y j ∨ g * (x * b) * g⁻¹ = y j) :
    IsSylowOf 2 (T.subgroupOf W) (centralizer {x}) ∧
      ∀ b ∈ T.subgroupOf W, b ^ 2 = 1 → b ≠ 1 → b ≠ x →
        MonoW (W.subgroupOf W) true (closure {x, b}) ∨
          ∃ j < i, IsConj b (y j) ∨ IsConj (x * b) (y j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTW : T ≤ W := hT.trans inf_le_left
  refine ⟨CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_, fun b hb hb2 hb1 hbx => ?_⟩
  · intro b hb
    rw [mem_subgroupOf] at hb
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hT hb).2)
  · rw [card_centralizer_subtype, ← hcard]
    exact Nat.card_congr (subgroupOfEquivOfLe hTW).toEquiv
  · have hbT : (b : Equiv.Perm (Fin n)) ∈ T := by rwa [mem_subgroupOf] at hb
    have hb2' : (b : Equiv.Perm (Fin n)) ^ 2 = 1 := by rw [← coe_pow, hb2, coe_one]
    have hb1' : (b : Equiv.Perm (Fin n)) ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
    have hbx' : (b : Equiv.Perm (Fin n)) ≠ x := fun h1 => hbx (Subtype.ext h1)
    rcases hw _ hbT hb2' hb1' hbx' with hM | ⟨j, hj, g, hg, hc | hc⟩
    · left
      have hXmap : (W.subgroupOf W).map W.subtype = W := by
        rw [subgroupOf_map_subtype, inf_idem]
      have hEmap : (closure ({x, b} : Set ↥W)).map W.subtype =
          closure {(x : Equiv.Perm (Fin n)), (b : Equiv.Perm (Fin n))} := by
        rw [MonoidHom.map_closure, Set.image_pair]
        rfl
      rw [← monoW_map_iff W.subtype W.subtype_injective, hXmap, hEmap]
      exact hM
    · exact Or.inr ⟨j, hj, Or.inl (isConj_iff.mpr ⟨⟨g, hg⟩, Subtype.ext (by simpa using hc)⟩)⟩
    · exact Or.inr ⟨j, hj, Or.inr (isConj_iff.mpr ⟨⟨g, hg⟩, Subtype.ext (by simpa using hc)⟩)⟩


@[expose] noncomputable def co2X₀ (j : ℕ) : Equiv.Perm (Fin 2300) := [locZ, locT, locU].getD j 1

theorem rep_co2X₀ {j : ℕ} (hj : j < 3) : Rep 2300 (co2Xs.getD j #[]) (co2X₀ j) := by
  interval_cases j
  · simp only [co2Xs, co2X₀, List.getD_cons_zero]
    exact rep_z
  · simp only [co2Xs, co2X₀, List.getD_cons_succ, List.getD_cons_zero]
    exact rep_t
  · simp only [co2Xs, co2X₀, List.getD_cons_succ, List.getD_cons_zero]
    exact rep_u

theorem co2X₀_mem {j : ℕ} (hj : j < 3) : co2X₀ j ∈ co2P := by
  interval_cases j
  · exact zP.2
  · exact tP.2
  · exact uP.2

theorem card_co2X₀ {j : ℕ} (hj : j < 3) :
    (Nat.card ↥(co2P ⊓ centralizer {co2X₀ j})).factorization 2 = co2Len.getD j 0 := by
  interval_cases j
  · change (Nat.card ↥(co2P ⊓ centralizer {locZ})).factorization 2 = 18
    rw [card_centralizer_locZ, show (743178240 : ℕ) = 2 ^ 18 * 2835 by norm_num,
      factorization_two_pow_mul 18 2835 (by decide)]
  · change (Nat.card ↥(co2P ⊓ centralizer {locT})).factorization 2 = 17
    rw [card_centralizer_locT, show (41287680 : ℕ) = 2 ^ 17 * 315 by norm_num,
      factorization_two_pow_mul 17 315 (by decide)]
  · change (Nat.card ↥(co2P ⊓ centralizer {locU})).factorization 2 = 15
    rw [card_centralizer_locU, show (1474560 : ℕ) = 2 ^ 15 * 45 by norm_num,
      factorization_two_pow_mul 15 45 (by decide)]

set_option maxRecDepth 100000 in
theorem co2_yCensus17R {L : ℕ → ℕ} {pxs : List ℕ} {rs : List RootR}
    (h : co2CheckR L pxs rs = true) : YCensus17 (co2P.subgroupOf co2P) (fun _ => False) := by
  classical
  unfold co2CheckR at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hlet, hinvL⟩, -⟩, -⟩, hroots⟩ := h
  have HL := co2Letters_of hlet hinvL
  have hℓ : ∀ k < 2 * 11, co2Let k ∈ co2P := fun k hk => co2Let_mem hk
  have hri : ∀ i < 3, eqA 2300 (unpackP 2300 12 (pxs.getD i 0)) (co2Xs.getD i #[]) = true ∧
      (rs.getD i default).d.xs.length = co2Len.getD i 0 ∧
      rootCheckR 2300 12 11 L co2BaseR (co2Deg.getD i 0) 5 pxs i (rs.getD i default) = true := by
    intro i hi
    have := List.all_eq_true.1 hroots i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1, Nat.eq_of_beq_eq_true this.1.2, this.2⟩
  have hX₀ : ∀ i < 3, ∀ p (hp : p < 2300), at' 12 (pxs.getD i 0) p = (co2X₀ i ⟨p, hp⟩ : ℕ) := by
    intro i hi p hp
    have he := allLt_spec (hri i hi).1 hp
    rw [beq_iff_eq, SP.unpackP_get, if_pos hp] at he
    rw [he]
    exact rep_co2X₀ hi ⟨p, hp⟩
  have hroot : ∀ i < 3, ∃ T : Subgroup (Equiv.Perm (Fin 2300)),
      T ≤ co2P ⊓ centralizer {co2X₀ i} ∧ Nat.card T = 2 ^ co2Len.getD i 0 ∧
      ∀ b ∈ T, b ^ 2 = 1 → b ≠ 1 → b ≠ co2X₀ i → MonoW co2P true (closure {co2X₀ i, b}) ∨
        ∃ j < i, ∃ g ∈ co2P, g * b * g⁻¹ = co2X₀ j ∨ g * (co2X₀ i * b) * g⁻¹ = co2X₀ j := by
    intro i hi
    obtain ⟨T, hT, hc, hw⟩ := root_of_rootCheckR co2BaseOf HL hℓ (X₀ := co2X₀)
      (fun j hj => hX₀ j (by omega)) (fun j hj => co2X₀_mem (by omega)) (hri i hi).2.2
    exact ⟨T, hT, by rw [hc, (hri i hi).2.1], hw⟩
  choose! T hT hc hw using hroot
  let x : ℕ → ↥co2P := fun i => if hi : i < 3 then ⟨co2X₀ i, co2X₀_mem hi⟩ else 1
  have hx : ∀ i (hi : i < 3), ((x i : ↥co2P) : Equiv.Perm (Fin 2300)) = co2X₀ i :=
    fun i hi => by simp only [x, hi, dite_true]
  have hW : ∀ i < 3, IsSylowOf 2 ((T i).subgroupOf co2P) (centralizer {x i}) ∧
      ∀ b ∈ (T i).subgroupOf co2P, b ^ 2 = 1 → b ≠ 1 → b ≠ x i →
        MonoW (co2P.subgroupOf co2P) true (closure {x i, b}) ∨
          ∃ j < i, IsConj b (x j) ∨ IsConj (x i * b) (x j) := by
    intro i hi
    refine root_in_W (x i) x i (by rw [hx i hi]; exact hT i hi)
      (by rw [hx i hi, hc i hi, card_co2X₀ hi]) fun b hb hb2 hb1 hbx => ?_
    rw [hx i hi] at hbx ⊢
    rcases hw i hi b hb hb2 hb1 hbx with hM | ⟨j, hj, g, hg, he⟩
    · exact Or.inl hM
    · exact Or.inr ⟨j, hj, g, hg, by rw [hx j (by omega)]; exact he⟩
  have hN : (co2P.subgroupOf co2P).Normal := by
    rw [subgroupOf_self]
    infer_instance
  have hidx : (co2P.subgroupOf co2P).index ≤ 2 := by
    rw [subgroupOf_self, index_top]
    norm_num
  refine yCensus17_of_roots (k := 3) hN hidx x (fun i => (T i).subgroupOf co2P)
    (fun i hi => (hW i hi).1) (fun a ha ha2 ha1 => ?_)
    (fun i hi b hb hb2 hb1 hbx => (hW i hi).2 b hb hb2 hb1 hbx)
  have ha2' : (a : Equiv.Perm (Fin 2300)) ^ 2 = 1 := by rw [← coe_pow, ha2, coe_one]
  have ha1' : (a : Equiv.Perm (Fin 2300)) ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
  obtain ⟨c, hcm, w, hw, hwc⟩ := co2_conj_root a a.2 ha2' ha1'
  have key : ∀ i (hi : i < 3), co2X₀ i = c → ∃ i < 3, IsConj a (x i) := fun i hi hi' =>
    ⟨i, hi, isConj_iff.mpr ⟨⟨w, hw⟩, Subtype.ext (by simp only [coe_mul, coe_inv, hx i hi, hi', hwc])⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
  rcases hcm with rfl | rfl | rfl
  · exact key 0 (by norm_num) rfl
  · exact key 1 (by norm_num) rfl
  · exact key 2 (by norm_num) rfl

end CFSG.ComponentClassification.RankTwoSporadic.Co2

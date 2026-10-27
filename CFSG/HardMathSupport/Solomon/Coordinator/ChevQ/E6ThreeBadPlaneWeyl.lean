module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjOrbit
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

set_option linter.unusedSectionVars false

local instance e6PWNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def e6PWD0Vec : Fin Tag.E6.rank → ZMod 3 := ![0, 1, 0, 0, 1, 1]

@[expose] def e6PWComb (i j : ZMod 3) (x : Fin Tag.E6.rank → ZMod 3) :
    Fin Tag.E6.rank → ZMod 3 :=
  i • e6KacVec + j • x

@[expose] def e6PWTable :
    List ((Fin Tag.E6.rank → ZMod 3) × List (Fin 6) × (ZMod 3 × ZMod 3) × (ZMod 3 × ZMod 3)) :=
  [
    (e6ConjVec 0 1 0 0 1 1, [], (1, 0), (0, 1)),
    (e6ConjVec 0 1 0 1 1 1, [], (1, 0), (2, 1)),
    (e6ConjVec 0 1 0 2 1 1, [], (1, 0), (1, 1)),
    (e6ConjVec 0 2 0 0 2 2, [], (1, 0), (0, 2)),
    (e6ConjVec 0 2 0 1 2 2, [], (1, 0), (1, 2)),
    (e6ConjVec 0 2 0 2 2 2, [], (1, 0), (2, 2)),
    (e6ConjVec 0 1 0 0 2 2, [1], (1, 0), (1, 2)),
    (e6ConjVec 0 1 0 1 2 2, [1], (1, 0), (2, 2)),
    (e6ConjVec 0 1 0 2 2 2, [1], (1, 0), (0, 2)),
    (e6ConjVec 0 2 0 0 1 1, [1], (1, 0), (1, 1)),
    (e6ConjVec 0 2 0 1 1 1, [1], (1, 0), (0, 1)),
    (e6ConjVec 0 2 0 2 1 1, [1], (1, 0), (2, 1)),
    (e6ConjVec 1 0 1 0 1 1, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3], (1, 0), (2, 1)),
    (e6ConjVec 1 0 1 1 1 1, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3], (1, 0), (1, 1)),
    (e6ConjVec 1 0 1 2 1 1, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3], (1, 0), (0, 1)),
    (e6ConjVec 2 0 2 0 2 2, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3], (1, 0), (2, 2)),
    (e6ConjVec 2 0 2 1 2 2, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3], (1, 0), (0, 2)),
    (e6ConjVec 2 0 2 2 2 2, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3], (1, 0), (1, 2)),
    (e6ConjVec 1 0 1 0 2 2, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 1], (1, 0), (2, 1)),
    (e6ConjVec 1 0 1 1 2 2, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 1], (1, 0), (1, 1)),
    (e6ConjVec 1 0 1 2 2 2, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 1], (1, 0), (0, 1)),
    (e6ConjVec 2 0 2 0 1 1, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 1], (1, 0), (2, 2)),
    (e6ConjVec 2 0 2 1 1 1, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 1], (1, 0), (0, 2)),
    (e6ConjVec 2 0 2 2 1 1, [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 1], (1, 0), (1, 2)),
    (e6ConjVec 1 1 1 0 0 0, [3, 4, 5, 2, 3, 4, 0, 2, 3], (2, 0), (1, 1)),
    (e6ConjVec 1 1 1 1 0 0, [3, 4, 5, 2, 3, 4, 0, 2, 3], (2, 0), (0, 1)),
    (e6ConjVec 1 1 1 2 0 0, [3, 4, 5, 2, 3, 4, 0, 2, 3], (2, 0), (2, 1)),
    (e6ConjVec 2 2 2 0 0 0, [3, 4, 5, 2, 3, 4, 0, 2, 3], (2, 0), (1, 2)),
    (e6ConjVec 2 2 2 1 0 0, [3, 4, 5, 2, 3, 4, 0, 2, 3], (2, 0), (2, 2)),
    (e6ConjVec 2 2 2 2 0 0, [3, 4, 5, 2, 3, 4, 0, 2, 3], (2, 0), (0, 2)),
    (e6ConjVec 1 2 1 0 0 0, [3, 4, 5, 2, 3, 4, 0, 2, 3, 1], (2, 0), (0, 1)),
    (e6ConjVec 1 2 1 1 0 0, [3, 4, 5, 2, 3, 4, 0, 2, 3, 1], (2, 0), (2, 1)),
    (e6ConjVec 1 2 1 2 0 0, [3, 4, 5, 2, 3, 4, 0, 2, 3, 1], (2, 0), (1, 1)),
    (e6ConjVec 2 1 2 0 0 0, [3, 4, 5, 2, 3, 4, 0, 2, 3, 1], (2, 0), (0, 2)),
    (e6ConjVec 2 1 2 1 0 0, [3, 4, 5, 2, 3, 4, 0, 2, 3, 1], (2, 0), (1, 2)),
    (e6ConjVec 2 1 2 2 0 0, [3, 4, 5, 2, 3, 4, 0, 2, 3, 1], (2, 0), (2, 2))
  ]

theorem e6PW_words : ∀ p ∈ e6PWTable,
    e6Wact p.2.1 e6KacVec = e6PWComb p.2.2.1.1 p.2.2.1.2 p.1 ∧
      e6Wact p.2.1 e6PWD0Vec = e6PWComb p.2.2.2.1 p.2.2.2.2 p.1 := by
  decide +kernel

theorem e6PW_complete : ∀ a b c d e f : ZMod 3,
    e6KerCount (e6PWComb 0 1 (e6ConjVec a b c d e f)) = 24 →
    e6KerCount (e6PWComb 1 1 (e6ConjVec a b c d e f)) = 24 →
    e6KerCount (e6PWComb 2 1 (e6ConjVec a b c d e f)) = 24 →
    ∃ p ∈ e6PWTable, p.1 = e6ConjVec a b c d e f := by
  decide +kernel

theorem e6PW_exists_word (x : Fin Tag.E6.rank → ZMod 3)
    (h0 : e6KerCount (e6PWComb 0 1 x) = 24) (h1 : e6KerCount (e6PWComb 1 1 x) = 24)
    (h2 : e6KerCount (e6PWComb 2 1 x) = 24) :
    ∃ l : List (Fin Tag.E6.rank), (∃ i j : ZMod 3, e6Wact l e6KacVec = e6PWComb i j x) ∧
      ∃ i j : ZMod 3, e6Wact l e6PWD0Vec = e6PWComb i j x := by
  have hx : x = e6ConjVec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨p, hp, hpx⟩ := e6PW_complete (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    (by rw [← hx]; exact h0) (by rw [← hx]; exact h1) (by rw [← hx]; exact h2)
  obtain ⟨hw0, hw1⟩ := e6PW_words p hp
  rw [hpx, ← hx] at hw0 hw1
  exact ⟨p.2.1, ⟨_, _, hw0⟩, _, _, hw1⟩

section Torus

variable {K : Type} [Field K]
  {ω : Kˣ}

theorem e6PW_exists_torV (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {b : Fin Tag.E6.rank → Kˣ}
    (hb : ∀ i, b i ^ 3 = 1) : ∃ x : Fin Tag.E6.rank → ZMod 3, torV ω x = b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprim : IsPrimitiveRoot ω 3 := IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime h3 h1)
  choose m hm3 hm using fun i =>
    hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 (b i)).2 (hb i))
  refine ⟨fun i => (m i : ZMod 3), funext fun i => ?_⟩
  show ω ^ ((m i : ZMod 3)).val = b i
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hm3 i)]
  exact hm i

theorem e6PW_pow_val_add (h3 : ω ^ 3 = 1) (a b : ZMod 3) :
    ω ^ (a + b).val = ω ^ a.val * ω ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ h3).symm

theorem e6PW_pow_val_mul (h3 : ω ^ 3 = 1) (a b : ZMod 3) :
    ω ^ (a * b).val = (ω ^ b.val) ^ a.val := by
  rw [ZMod.val_mul, ← pow_mul, mul_comm b.val]
  exact (pow_eq_pow_mod _ h3).symm

theorem e6PW_torV_add (h3 : ω ^ 3 = 1) (x y : Fin Tag.E6.rank → ZMod 3) :
    torV ω (x + y) = torV ω x * torV ω y := by
  funext i
  exact e6PW_pow_val_add h3 (x i) (y i)

theorem e6PW_torV_smul (h3 : ω ^ 3 = 1) (c : ZMod 3) (x : Fin Tag.E6.rank → ZMod 3) :
    torV ω (c • x) = torV ω x ^ c.val := by
  funext i
  exact e6PW_pow_val_mul h3 c (x i)

theorem e6PW_torV_d0 : torV ω e6PWD0Vec = e6D0Char ω := by
  funext i
  have key : ∀ j : Fin Tag.E6.rank, (e6PWD0Vec j = 0 ∧ e6D0Char ω j = 1) ∨
      (e6PWD0Vec j = 1 ∧ e6D0Char ω j = ω) := by
    intro j
    fin_cases j
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  rcases key i with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [torV, h0, h1]
    simp
  · rw [torV, h0, h1]
    have h : (1 : ZMod 3).val = 1 := rfl
    rw [h, pow_one]

theorem e6PW_rootDiagUnit_mul (a b : Fin Tag.E6.rank → Kˣ) :
    rootDiagUnit .E6 (a * b) = (rootDiagUnit .E6 a : ModGL .E6 K) * rootDiagUnit .E6 b :=
  Units.ext (rootDiag_mul_rootDiag a b).symm

theorem e6PW_rootDiagUnit_pow (a : Fin Tag.E6.rank → Kˣ) (n : ℕ) :
    rootDiagUnit .E6 (a ^ n) = (rootDiagUnit .E6 a : ModGL .E6 K) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Units.ext rootDiag_one
  | succ n ih => rw [pow_succ, e6PW_rootDiagUnit_mul, ih, pow_succ]

theorem e6PW_rootDiagUnit_comb (h3 : ω ^ 3 = 1) (i j : ZMod 3) (x : Fin Tag.E6.rank → ZMod 3) :
    rootDiagUnit .E6 (torV ω (e6PWComb i j x)) =
      (rootDiagUnit .E6 (e6LineChar ω) : ModGL .E6 K) ^ i.val *
        rootDiagUnit .E6 (torV ω x) ^ j.val := by
  rw [e6PWComb, e6PW_torV_add h3, e6PW_torV_smul h3, e6PW_torV_smul h3, torV_e6KacVec,
    e6PW_rootDiagUnit_mul, e6PW_rootDiagUnit_pow, e6PW_rootDiagUnit_pow]

theorem e6PW_pow_mul_torV (h3 : ω ^ 3 = 1) {k : ℕ} (hk : k < 3) (x : Fin Tag.E6.rank → ZMod 3) :
    (rootDiagUnit .E6 (e6LineChar ω) : ModGL .E6 K) ^ k * rootDiagUnit .E6 (torV ω x) =
      rootDiagUnit .E6 (torV ω (e6PWComb (k : ZMod 3) 1 x)) := by
  rw [e6PW_rootDiagUnit_comb h3, ZMod.val_natCast, Nat.mod_eq_of_lt hk,
    show (1 : ZMod 3).val = 1 from rfl, pow_one]

open scoped Classical in
theorem e6PW_finrank_torV (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (x : Fin Tag.E6.rank → ZMod 3) :
    Module.finrank K (LinearMap.ker (((rootDiagUnit .E6 (torV ω x) : ModGL .E6 K) :
      Module.End K (RootModule .E6 K)) - 1)) = 6 + e6KerCount x := by
  have e : ((rootDiagUnit .E6 (torV ω x) : ModGL .E6 K) : Module.End K (RootModule .E6 K)) =
      rootDiag (torV ω x) := rfl
  rw [e, finrank_ker_rootDiag_sub_one_card, card_filter_rootChar_torV h3 h1]
  rfl

theorem e6PW_conj_mem (h3 : ω ^ 3 = 1) (l : List (Fin Tag.E6.rank))
    {y x : Fin Tag.E6.rank → ZMod 3} (h : ∃ i j : ZMod 3, e6Wact l y = e6PWComb i j x) :
    canonicalRep (coxeterSystem .E6) K (l.map (simple .E6)).prod * rootDiagUnit .E6 (torV ω y) *
        (canonicalRep (coxeterSystem .E6) K (l.map (simple .E6)).prod)⁻¹ ∈
      Subgroup.zpowers (rootDiagUnit .E6 (e6LineChar ω) : ModGL .E6 K) ⊔
        Subgroup.zpowers (rootDiagUnit .E6 (torV ω x) : ModGL .E6 K) := by
  obtain ⟨i, j, hij⟩ := h
  rw [canonicalRep_conj_rootDiagUnit, weylTuple_prod_torV h3, hij, e6PW_rootDiagUnit_comb h3]
  exact mul_mem (Subgroup.mem_sup_left (pow_mem (Subgroup.mem_zpowers _) _))
    (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers _) _))

theorem e6PlaneWeyl_proved : E6PlaneWeylStmt := by
  intro K _ _ ω h3 h1 b hb hpat
  obtain ⟨x, rfl⟩ := e6PW_exists_torV h3 h1 hb
  have hc : ∀ k : ℕ, k < 3 → e6KerCount (e6PWComb (k : ZMod 3) 1 x) = 24 := by
    intro k hk
    have h := hpat k hk
    rw [e6PW_pow_mul_torV h3 hk, e6PW_finrank_torV h3 h1] at h
    omega
  obtain ⟨l, hw0, hw1⟩ := e6PW_exists_word x (by simpa using hc 0 (by norm_num))
    (by simpa using hc 1 (by norm_num)) (by simpa using hc 2 (by norm_num))
  refine ⟨(canonicalRep (coxeterSystem .E6) K (l.map (simple .E6)).prod)⁻¹,
    inv_mem (canonicalRep_mem_adjointGroup (coxeterSystem .E6) K _), ?_, ?_⟩
  · have key := e6PW_conj_mem h3 l hw0
    rw [torV_e6KacVec] at key
    rwa [inv_inv]
  · have key := e6PW_conj_mem h3 l hw1
    rw [e6PW_torV_d0] at key
    rwa [inv_inv]

end Torus

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end

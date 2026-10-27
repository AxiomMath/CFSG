module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSAutCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSModel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchClassify

public section


namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open KFacts

attribute [local irreducible] sAct sMt sGinv p9List p9Index a9LinTab a9CoTab sNfTab sMTab sKOrb
  sCanon sTree sInvList sY

theorem sMul_zero_zero : sMul 0 0 = 0 := sMul_zero_left (by norm_num)

theorem sInv_ok : invOK sMul sInv 65536 = true := by
  have h := sAut_check1
  unfold sAutCheck1 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1

theorem sKFacts : KFacts 65536 sMul a9K := by
  have h := sAut_check1
  unfold sAutCheck1 at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  refine ⟨fun v hv => (h1 v hv).1, fun v hv => (h1 v hv).2, fun v w hv hw => h2 v hv w hw,
    fun c hc hcomm => ?_⟩
  rcases h3 c hc with h | h
  · exfalso
    rw [List.all_eq_false] at h
    obtain ⟨j, hj, hne⟩ := h
    simp only [beq_iff_eq] at hne
    exact hne (hcomm j (List.mem_range.1 hj))
  · exact h

section Check1


theorem sCheck1_parts : (∀ l, l < 7 → sAutData.g l < 65536) ∧
    (∀ x, x < 65536 → sAutData.nfE x < 2 ^ 7 ∧ sAutData.nfA x < 2 ^ 9 ∧
      x = sMul (wprodN sMul 7 sAutData.g (sAutData.nfE x)) (a9K.lin (sAutData.nfA x))) ∧
    (∀ i, i < 7 → ∀ j, j < i + 1 → sAutData.relA i j < 2 ^ 9 ∧
      (if j < i then sConj (sAutData.g i) (sAutData.g j) else sMul (sAutData.g i) (sAutData.g i)) =
        sMul (wprodN sMul i sAutData.g (sAutData.relE i j)) (a9K.lin (sAutData.relA i j))) ∧
    (∀ g ∈ sGens, g < 65536) ∧
    treeOK sMul sGens 65536 (fun c => sTree.1[c]!) (fun c => sTree.2.1[c]!)
      (fun c => sTree.2.2[c]!) = true := by
  have h := sAut_check1
  unfold sAutCheck1 at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h4, fun x hx => ⟨(h5 x hx).1.1, (h5 x hx).1.2, (h5 x hx).2⟩,
    fun i hi j hj => ⟨(h6 i hi j hj).1, (h6 i hi j hj).2⟩, h7, h8⟩

end Check1

section Check2


theorem sCheck2_parts :
    (∀ v, v < 512 → orbOK sMul sInv 65536 (a9K.lin v) (sKOrb[v]!) = true ∧
      orbClosed sMul sInv sGens (a9K.lin v) (sKOrb[v]!) = true) ∧
    (∀ e, e < 128 → ∀ v, v < 512 → sAutData.M e v < 2 ^ 9 ∧
      a9K.lin (sAutData.M e v) = sConj (wprodN sMul 7 sAutData.g e) (a9K.lin v)) ∧
    (∀ j, j < 7 → ∀ i, i < 9 → sAutData.cb j i < 2 ^ (i + 1) ∧
      a9K.lin (sAutData.cb j i) = sConj (sAutData.g j) (a9K.lin (2 ^ i))) ∧
    (∀ V ∈ nSearch 9 7 sAutData.M sAutData.cb sAutData.olen, ∃ k, k < 8 ∧ ∃ e, e < 128 ∧
      ∀ i, i < 9 → V.getD i 0 = sAutData.M e (sAutData.P k i)) ∧
    (∀ k, k < 8 → ∀ i, i < 9 → sAutData.P k i < 2 ^ 9) ∧
    (∀ k, k < 8 → ∀ i, i < 7 → sAutData.h k i < 65536) := by
  have h := sAut_check2
  unfold sAutCheck2 at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, fun e he v hv => h2 e he v hv, fun j hj i hi => h3 j hj i hi, fun V hV => ?_, h5, h6⟩
  obtain ⟨k, hk, e, he, hP⟩ := h4 V hV
  exact ⟨k, hk, e, he, hP⟩

end Check2

section Check3


theorem sCheck3_parts :
    (∀ k, k < 8 → ∀ i, i < 7 → ∀ v, v < 512 →
      a9K.co (sConj (sAutData.h k i) (a9K.lin (sAutData.Pk k v))) =
        sAutData.Pk k (a9K.co (sConj (sAutData.g i) (a9K.lin v)))) ∧
    (∀ k, k < 8 → ∀ i, i < 7 → ∀ d ∈ sAutData.R k i, d < 2 ^ 9) ∧
    (∀ k, k < 8 → ∀ i, i < 7 → ∀ d, d < 512 → sAutData.cA k i d < 2 ^ 9 ∧
      sAutData.cD k i d ∈ sAutData.R k i ∧
      (∀ l, l < i → sMul (a9K.lin (sAutData.cA k i d)) (sAutData.h k l) =
        sMul (sAutData.h k l) (a9K.lin (sAutData.cA k i d))) ∧
      sConj (a9K.lin (sAutData.cA k i d)) (sMul (sAutData.h k i) (a9K.lin d)) =
        sMul (sAutData.h k i) (a9K.lin (sAutData.cD k i d))) := by
  have h := sAut_check3
  unfold sAutCheck3 at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, fun k hk i hi d hd => ⟨(h3 k hk i hi d hd).1.1.1, (h3 k hk i hi d hd).1.1.2,
    (h3 k hk i hi d hd).1.2, (h3 k hk i hi d hd).2⟩⟩

end Check3

theorem sGen : Gen sMul sGens 65536 := gen_of_treeOK sCheck1_parts.2.2.2.2

theorem sGens_lt : ∀ g ∈ sGens, g < 65536 := sCheck1_parts.2.2.2.1

theorem sAutFacts (h0 : sMul 0 0 = 0) : AutFacts 65536 sMul sInv sAutData := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := sCheck1_parts
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := sCheck2_parts
  obtain ⟨d1, d2, d3⟩ := sCheck3_parts
  exact
    { h0 := h0
      inv_ok := sInv_ok
      kf := sKFacts
      g_lt := g1
      nf := g2
      rel := fun i hi j hj => g3 i hi j (by omega)
      gens_lt := g4
      gen := gen_of_treeOK g5
      olen := fun v hv => ⟨_, (c1 v hv).1, (c1 v hv).2, rfl⟩
      M_eq := c2
      cb_eq := c3
      leaves := c4
      P_lt := c5
      h_lt := c6
      h_act := d1
      R_lt := d2
      canon := d3 }

section Y

variable {H : Type*} [Group H] (Φ : CodeIso H 65536 sMul)

@[expose] def YProp (x : H) : Prop :=
  x * x = 1 ∧ x ≠ 1 ∧ (MulAction.orbit (ConjAct H) x).ncard = 8 ∧
    Nat.card {z : H // z * z = 1 ∧ z ≠ 1 ∧ z * x = x * z} = 1343

theorem yProp_map (γ : H ≃* H) (x : H) : YProp (γ x) ↔ YProp x := by
  unfold YProp
  have hcard : Nat.card {z : H // z * z = 1 ∧ z ≠ 1 ∧ z * γ x = γ x * z} =
      Nat.card {z : H // z * z = 1 ∧ z ≠ 1 ∧ z * x = x * z} := by
    refine Nat.card_congr
      { toFun := fun z => ⟨γ.symm z, ?_⟩
        invFun := fun z => ⟨γ z, ?_⟩
        left_inv := fun z => Subtype.ext (γ.apply_symm_apply _)
        right_inv := fun z => Subtype.ext (γ.symm_apply_apply _) }
    · obtain ⟨h1, h2, h3⟩ := z.2
      refine ⟨γ.injective ?_, fun h => h2 ?_, γ.injective ?_⟩
      · rw [map_mul, MulEquiv.apply_symm_apply, h1, map_one]
      · rw [← γ.apply_symm_apply z.1, h, map_one]
      · rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h3]
    · obtain ⟨h1, h2, h3⟩ := z.2
      refine ⟨by rw [← map_mul, h1, map_one], fun h => h2 (γ.injective (by rw [h, map_one])),
        by rw [← map_mul, ← map_mul, h3]⟩
  rw [hcard, CodeIso.ncard_orbit_map, ← map_mul, γ.map_eq_one_iff, Ne, γ.map_eq_one_iff]

theorem sCheck4_parts : (∀ c ∈ sInvList, orbOK sMul sInv 65536 c (sInvRec c) = true ∧
      (orbClosed sMul sInv sGens c (sInvRec c) = true ∨ 8 < (sInvRec c).length)) ∧
    (∀ c, c < 65536 → ((∀ y ∈ sY, sMul c y = sMul y c) ↔ a9K.In c)) := by
  have h := sAut_check4
  unfold sAutCheck4 at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at h
  refine ⟨h.1, fun c hc => ?_⟩
  have h2 := h.2 c hc
  rw [Bool.beq_eq_decide_eq, decide_eq_true_eq] at h2
  constructor
  · intro hall
    have : (sY.all fun y => sMul c y == sMul y c) = true := by
      simp only [List.all_eq_true, beq_iff_eq]; exact hall
    rw [this] at h2
    have h3 := h2.symm
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h3
    exact h3
  · intro hin
    have h3 : (decide (a9K.co c < 2 ^ 9) && a9K.lin (a9K.co c) == c) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]; exact hin
    rw [h3] at h2
    simpa only [List.all_eq_true, beq_iff_eq] using h2

theorem mem_sInvList {c : ℕ} : c ∈ sInvList ↔ c < 65536 ∧ sMul c c = 0 ∧ c ≠ 0 := by
  unfold sInvList
  simp [List.mem_filter, List.mem_range]

theorem sNinv_eq (x : H) :
    sNinv (Φ.f x) = Nat.card {z : H // z * z = 1 ∧ z ≠ 1 ∧ z * x = x * z} := by
  have h0 := sMul_zero_zero
  have hc := Φ.card_eq (fun d => sMul d d == 0 && d != 0 && sMul d (Φ.f x) == sMul (Φ.f x) d)
  unfold sNinv sInvList
  rw [List.filter_filter]
  have e : ∀ d : H, ((sMul (Φ.f d) (Φ.f d) == 0 && Φ.f d != 0 &&
      sMul (Φ.f d) (Φ.f x) == sMul (Φ.f x) (Φ.f d)) = true ↔
      d * d = 1 ∧ d ≠ 1 ∧ d * x = x * d) := by
    intro d
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ← Φ.map_mul, ← Φ.f_one h0,
      Φ.f_eq_iff, and_assoc]
  rw [Nat.card_congr (Equiv.subtypeEquivRight e).symm, hc]
  exact congrArg List.length (List.filter_congr fun d _ => by rw [Bool.and_comm])

theorem f_mul_self_iff (x : H) : sMul (Φ.f x) (Φ.f x) = 0 ↔ x * x = 1 := by
  rw [← Φ.map_mul, ← Φ.f_one sMul_zero_zero, Φ.f_eq_iff]

theorem f_ne_zero_iff (x : H) : Φ.f x ≠ 0 ↔ x ≠ 1 := by
  rw [← Φ.f_one sMul_zero_zero, Ne, Φ.f_eq_iff]

theorem mem_sY_iff (x : H) : Φ.f x ∈ sY ↔ YProp x := by
  obtain ⟨h4a, -⟩ := sCheck4_parts
  have hsY : ∀ c, c ∈ sY ↔ c ∈ sInvList ∧ orbClosed sMul sInv sGens c (sInvRec c) = true ∧
      (sInvRec c).length = 8 ∧ sNinv c = 1343 := by
    intro c
    unfold sY
    rw [List.mem_filter]
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  obtain ⟨-, -, -, -, gG⟩ := sCheck1_parts
  have hG := gen_of_treeOK gG
  have hgl : ∀ g ∈ sGens, g < 65536 := sCheck1_parts.2.2.2.1
  rw [hsY, mem_sInvList, f_mul_self_iff, f_ne_zero_iff, sNinv_eq]
  unfold YProp
  constructor
  · rintro ⟨⟨-, h1, h2⟩, hC, hlen, hN⟩
    have hmem : Φ.f x ∈ sInvList := mem_sInvList.2 ⟨Φ.lt x, (f_mul_self_iff Φ x).2 h1,
      (f_ne_zero_iff Φ x).2 h2⟩
    refine ⟨h1, h2, ?_, hN⟩
    rw [Φ.ncard_eq sMul_zero_zero sInv_ok hgl hG (h4a _ hmem).1 hC, hlen]
  · rintro ⟨h1, h2, h3, hN⟩
    have hmem : Φ.f x ∈ sInvList := mem_sInvList.2 ⟨Φ.lt x, (f_mul_self_iff Φ x).2 h1,
      (f_ne_zero_iff Φ x).2 h2⟩
    obtain ⟨hok, hcl⟩ := h4a _ hmem
    have hle := Φ.length_le_ncard sMul_zero_zero sInv_ok hok
    rw [h3] at hle
    have hC : orbClosed sMul sInv sGens (Φ.f x) (sInvRec (Φ.f x)) = true :=
      hcl.resolve_right (by omega)
    refine ⟨⟨Φ.lt x, h1, h2⟩, hC, ?_, hN⟩
    rw [← Φ.ncard_eq sMul_zero_zero sInv_ok hgl hG hok hC, h3]

theorem sChar : ∀ γ : H ≃* H, ∀ x : H, Mem Φ a9K x → Mem Φ a9K (γ x) := by
  intro γ x hx
  have hlt : ∀ y ∈ sY, y < 65536 := fun y hy => by
    unfold sY at hy
    exact (mem_sInvList.1 (List.mem_of_mem_filter hy)).1
  refine char_of_Y Φ (Y := sY) hlt (fun γ y hy => ?_) sCheck4_parts.2 γ hx
  have hylt : y < 65536 := hlt y hy
  have h1 := (mem_sY_iff Φ (Φ.g y)).1 (by rwa [Φ.f_g hylt])
  exact (mem_sY_iff Φ _).2 ((yProp_map γ _).2 h1)

theorem sClassify (γ : H ≃* H) : ∃ s : H, ∃ k, k < 8 ∧ ∃ ds ∈ sAutData.fSearch sMul sInv k,
    ∀ x : H, Φ.f (γ x) = sConj (Φ.f s) (sAutData.F sMul k ds (Φ.f x)) :=
  (sAutFacts sMul_zero_zero).classify Φ (sChar Φ) γ

end Y

end CFSG.EvenSmallLie.OmegaEight.SpBranch

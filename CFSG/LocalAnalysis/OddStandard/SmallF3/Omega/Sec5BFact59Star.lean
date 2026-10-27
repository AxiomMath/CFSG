module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BFact59Bits
import all Certificates.Data.Asc82Fact59
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartCoord
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartPerm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.OddStandard.SmallF3.Omega.Fact59Check CFSG.OddStandard.SmallF3.Omega.Fact59Bridge

private def PairMeet {α : Type} (a b c d : α) : Prop := a = c ∨ a = d ∨ b = c ∨ b = d

private def PairSame {α : Type} (a b c d : α) : Prop := (a = c ∧ b = d) ∨ (a = d ∧ b = c)

private lemma pairMeet_of_same {α : Type} {u v p q c a : α} (hs : PairSame p q c a)
    (hm : PairMeet u v p q) : PairMeet u v c a := by
  unfold PairSame PairMeet at *
  grind

private lemma not_pairSame_of_same {α : Type} {u v p q c a : α} (hs : PairSame p q c a)
    (hn : ¬PairSame u v p q) : ¬PairSame u v c a := by
  unfold PairSame at *
  grind

private lemma pair_four {α : Type} {c a0 a1 u v s t : α} (hc0 : c ≠ a0) (hc1 : c ≠ a1)
    (h01 : a0 ≠ a1) (huv : u ≠ v) (hst : s ≠ t) (hu0 : PairMeet u v c a0)
    (hu1 : PairMeet u v c a1) (hnu0 : ¬PairSame u v c a0) (hnu1 : ¬PairSame u v c a1)
    (hs0 : PairMeet s t c a0) (hs1 : PairMeet s t c a1) (hns0 : ¬PairSame s t c a0)
    (hns1 : ¬PairSame s t c a1) (hus : PairMeet u v s t) (hnus : ¬PairSame u v s t)
    (huc : u ≠ c) (hvc : v ≠ c) : False := by
  unfold PairMeet PairSame at *
  grind

private lemma pair_two {α : Type} {x0 y0 x1 y1 : α} (h0 : x0 ≠ y0) (h1 : x1 ≠ y1)
    (hm : PairMeet x0 y0 x1 y1) (hn : ¬PairSame x0 y0 x1 y1) :
    ∃ c a0 a1, c ≠ a0 ∧ c ≠ a1 ∧ a0 ≠ a1 ∧ PairSame x0 y0 c a0 ∧ PairSame x1 y1 c a1 := by
  unfold PairMeet PairSame at *
  rcases hm with h | h | h | h
  · exact ⟨x0, y0, y1, by grind⟩
  · exact ⟨x0, y0, x1, by grind⟩
  · exact ⟨y0, x0, y1, by grind⟩
  · exact ⟨y0, x0, x1, by grind⟩

private lemma star_of_meet {α : Type} (x y : Fin 6 → α) (hxy : ∀ i, x i ≠ y i)
    (hm : ∀ i j, i ≠ j → PairMeet (x i) (y i) (x j) (y j))
    (hn : ∀ i j, i ≠ j → ¬PairSame (x i) (y i) (x j) (y j)) :
    ∃ c, ∀ i, x i = c ∨ y i = c := by
  obtain ⟨c, a0, a1, hc0, hc1, h01, hs0, hs1⟩ :=
    pair_two (hxy 0) (hxy 1) (hm 0 1 (by decide)) (hn 0 1 (by decide))
  have key : ∀ i j : Fin 6, i ≠ 0 → i ≠ 1 → j ≠ 0 → j ≠ 1 → i ≠ j → x i = c ∨ y i = c := by
    intro i j hi0 hi1 hj0 hj1 hij
    by_contra h
    push Not at h
    exact pair_four hc0 hc1 h01 (hxy i) (hxy j) (pairMeet_of_same hs0 (hm i 0 hi0))
      (pairMeet_of_same hs1 (hm i 1 hi1)) (not_pairSame_of_same hs0 (hn i 0 hi0))
      (not_pairSame_of_same hs1 (hn i 1 hi1)) (pairMeet_of_same hs0 (hm j 0 hj0))
      (pairMeet_of_same hs1 (hm j 1 hj1)) (not_pairSame_of_same hs0 (hn j 0 hj0))
      (not_pairSame_of_same hs1 (hn j 1 hj1)) (hm i j hij) (hn i j hij) h.1 h.2
  refine ⟨c, fun i => ?_⟩
  unfold PairSame at hs0 hs1
  fin_cases i
  · grind
  · grind
  · exact key 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact key 3 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact key 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact key 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)

private lemma inD_zero : inD 0 = false := by
  decide +kernel

private lemma hp_symm : ∀ a c : Fin 8, heartPair a.val c.val = heartPair c.val a.val := by
  decide +kernel

private lemma hp_cls : ∀ n : Fin 64, inD n.val = true →
    ∃ a : Fin 8, ∃ c : Fin 8, a ≠ c ∧ heartPair a.val c.val = n.val := by
  decide +kernel

private lemma hp_adj : ∀ a c d e : Fin 8, a ≠ c → d ≠ e →
    inD (heartPair a.val c.val ^^^ heartPair d.val e.val) = true →
      a = d ∨ a = e ∨ c = d ∨ c = e := by
  decide +kernel

private lemma inD_iff (n : ℕ) (hn : n < 64) :
    inD n = true ↔ vecOfNat n ∈ pairSet6 := by
  interval_cases n <;> (unfold pairSet6; decide +kernel)

private lemma vecOfNat_xor (a b : ℕ) : vecOfNat (a ^^^ b) = vecOfNat a + vecOfNat b := by
  funext i
  simp only [vecOfNat, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i.val <;> cases b.testBit i.val <;> decide

private lemma single_mem : ∀ i : Fin 6, Pi.single i (1 : ZMod 2) ∈ pairSet6 := by
  unfold pairSet6
  decide +kernel

private lemma single_add_mem : ∀ i j : Fin 6, i ≠ j →
    Pi.single i (1 : ZMod 2) + Pi.single j 1 ∈ pairSet6 := by
  unfold pairSet6
  decide +kernel

theorem exists_perm_heart (g : (Fin 6 → ZMod 2) → (Fin 6 → ZMod 2))
    (had : ∀ v w, g (v + w) = g v + g w) (hg : ∀ v, v ∈ pairSet6 ↔ g v ∈ pairSet6) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ i : Fin 6, natOfVec (g (Pi.single i 1))
      = heartPair (σ (Fin.castLE (by norm_num : 6 ≤ 8) i)).val (σ 6).val := by
  obtain ⟨b, hb⟩ : ∃ b : Fin 6 → ℕ, ∀ i, b i = natOfVec (g (Pi.single i 1)) := ⟨_, fun _ => rfl⟩
  have hb_lt : ∀ i, b i < 64 := fun i => by
    rw [hb]
    exact natOfVec_lt _
  have hvb : ∀ i, vecOfNat (b i) = g (Pi.single i 1) := fun i => by
    rw [hb]
    exact vecOfNat_natOfVec _
  have hbD : ∀ i, inD (b i) = true := fun i => by
    rw [inD_iff _ (hb_lt i), hvb]
    exact (hg _).mp (single_mem i)
  have hbbD : ∀ i j, i ≠ j → inD (b i ^^^ b j) = true := fun i j hij => by
    have hlt : b i ^^^ b j < 2 ^ 6 := Nat.xor_lt_two_pow (hb_lt i) (hb_lt j)
    rw [inD_iff _ hlt, vecOfNat_xor, hvb, hvb, ← had]
    exact (hg _).mp (single_add_mem i j hij)
  have hb_ne : ∀ i j, i ≠ j → b i ≠ b j := fun i j hij h => by
    have := hbbD i j hij
    rw [h, Nat.xor_self, inD_zero] at this
    exact Bool.false_ne_true this
  have hcl : ∀ i, ∃ x y : Fin 8, x ≠ y ∧ heartPair x.val y.val = b i :=
    fun i => hp_cls ⟨b i, hb_lt i⟩ (hbD i)
  choose x y hxy hxyb using hcl
  have hm : ∀ i j, i ≠ j → PairMeet (x i) (y i) (x j) (y j) := fun i j hij =>
    hp_adj (x i) (y i) (x j) (y j) (hxy i) (hxy j) (by rw [hxyb, hxyb]; exact hbbD i j hij)
  have hn : ∀ i j, i ≠ j → ¬PairSame (x i) (y i) (x j) (y j) := by
    rintro i j hij (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · apply hb_ne i j hij
      rw [← hxyb i, ← hxyb j, h1, h2]
    · apply hb_ne i j hij
      rw [← hxyb i, ← hxyb j, h1, h2, hp_symm]
  obtain ⟨c, hc⟩ := star_of_meet x y hxy hm hn
  let z : Fin 6 → Fin 8 := fun i => if x i = c then y i else x i
  have hz_ne : ∀ i, z i ≠ c := fun i => by
    by_cases h : x i = c
    · simp only [z, h, if_true]
      exact fun h' => hxy i (h.trans h'.symm)
    · simp only [z, h, if_false]
      exact h
  have hz_hp : ∀ i, heartPair (z i).val c.val = b i := fun i => by
    by_cases h : x i = c
    · simp only [z, h, if_true]
      rw [← hxyb i, h, hp_symm]
    · have hy : y i = c := (hc i).resolve_left h
      simp only [z, h, if_false]
      rw [← hxyb i, hy]
  have hz_inj : Function.Injective z := fun i j hij => by
    by_contra h
    apply hb_ne i j h
    rw [← hz_hp i, ← hz_hp j, hij]
  obtain ⟨r, hrc, hzr⟩ : ∃ r : Fin 8, r ≠ c ∧ ∀ i, z i ≠ r := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin 8)) ⊆ insert c (Finset.univ.image z) := by
      intro a _
      by_cases hac : a = c
      · rw [hac]
        exact Finset.mem_insert_self _ _
      · obtain ⟨i, hi⟩ := h a hac
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le c (Finset.univ.image z)
    have h3 := Finset.card_image_le (s := (Finset.univ : Finset (Fin 6))) (f := z)
    rw [Finset.card_univ, Fintype.card_fin] at h1 h3
    omega
  have hz_ne' : ∀ i, c ≠ z i := fun i h => hz_ne i h.symm
  have hzr' : ∀ i, r ≠ z i := fun i h => hzr i h.symm
  let f : Fin 8 → Fin 8 := ![z 0, z 1, z 2, z 3, z 4, z 5, c, r]
  have hf : Function.Injective f := by
    intro a a' haa
    fin_cases a <;> fin_cases a' <;>
      simp [f, hz_inj.eq_iff, hz_ne, hz_ne', hzr, hzr', hrc, hrc.symm] at haa ⊢
  let σ : Equiv.Perm (Fin 8) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hσz : ∀ i : Fin 6, σ (Fin.castLE (by norm_num : 6 ≤ 8) i) = z i := by
    intro i
    fin_cases i <;> rfl
  have hσ6 : σ 6 = c := rfl
  refine ⟨σ, fun i => ?_⟩
  rw [← hb i, hσz i, hσ6]
  exact (hz_hp i).symm

private lemma permVec_single (σ : Equiv.Perm (Fin 8)) (i : Fin 8) :
    permVec σ (Pi.single i (1 : ZMod 2)) = Pi.single (σ i) 1 := by
  funext j
  simp only [permVec, Function.comp_apply, Pi.single_apply]
  by_cases h : j = σ i
  · have h' : σ.symm j = i := by rw [Equiv.symm_apply_eq]; exact h
    simp [h, h']
  · have h' : σ.symm j ≠ i := fun hh => h ((Equiv.symm_apply_eq σ).mp hh)
    simp [h, h']

private def evenLift (v : Fin 6 → ZMod 2) : Fin 8 → ZMod 2 :=
  Fin.snoc (Fin.snoc v (∑ i, v i)) 0

private lemma castLE6_8_eq (i : Fin 6) :
    Fin.castLE (by norm_num : 6 ≤ 8) i = Fin.castSucc (Fin.castSucc i) := rfl

private lemma snoc_add {n : ℕ} (f g : Fin n → ZMod 2) (a b : ZMod 2) :
    Fin.snoc (α := fun _ => ZMod 2) (f + g) (a + b)
      = Fin.snoc (α := fun _ => ZMod 2) f a + Fin.snoc (α := fun _ => ZMod 2) g b := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [Fin.snoc_last]
  | cast i => simp [Fin.snoc_castSucc]

private lemma evenLift_add (v w : Fin 6 → ZMod 2) :
    evenLift (v + w) = evenLift v + evenLift w := by
  rw [evenLift, evenLift, evenLift]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [snoc_add v w (∑ i, v i) (∑ i, w i)]
  have h := snoc_add (Fin.snoc v (∑ i, v i)) (Fin.snoc w (∑ i, w i)) (0 : ZMod 2) 0
  simp only [add_zero] at h
  rw [h]

private lemma evenLift_even (v : Fin 6 → ZMod 2) : IsEvenVec (evenLift v) := by
  unfold IsEvenVec evenLift
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, Fin.snoc_castSucc, add_zero]
  exact CharTwo.add_self_eq_zero _

private lemma heartCoord_evenLift (v : Fin 6 → ZMod 2) : heartCoord (evenLift v) = v := by
  funext i
  simp only [heartCoord, evenLift, castLE6_8_eq, Fin.snoc_castSucc, Fin.snoc_last, Pi.add_apply,
    Pi.zero_apply]
  exact add_zero (v i)

private lemma evenLift_single (i : Fin 6) :
    evenLift (Pi.single i (1 : ZMod 2))
      = Pi.single (Fin.castLE (by norm_num : 6 ≤ 8) i) (1 : ZMod 2) + Pi.single 6 1 := by
  fin_cases i <;> funext j <;> fin_cases j <;> decide +kernel

private lemma eq_of_agree_single {f h : (Fin 6 → ZMod 2) → (Fin 6 → ZMod 2)}
    (hf : ∀ v w, f (v + w) = f v + f w) (hh : ∀ v w, h (v + w) = h v + h w)
    (hs : ∀ i : Fin 6, f (Pi.single i 1) = h (Pi.single i 1)) : f = h := by
  let F : (Fin 6 → ZMod 2) →+ (Fin 6 → ZMod 2) := AddMonoidHom.mk' f hf
  let H : (Fin 6 → ZMod 2) →+ (Fin 6 → ZMod 2) := AddMonoidHom.mk' h hh
  have hsum : ∀ v : Fin 6 → ZMod 2,
      v = ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), Pi.single i (1 : ZMod 2) := by
    intro v
    funext j
    rw [Finset.sum_apply]
    by_cases hj : v j = 0
    · rw [hj]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_filter] at hi
      have hij : i ≠ j := by intro hh; rw [hh] at hi; exact hi.2 hj
      change (Pi.single (M := fun _ => ZMod 2) i (1 : ZMod 2)) j = 0
      rw [Pi.single_eq_of_ne (Ne.symm hij)]
    · have hvj : v j = 1 := zmod2_eq_one_of_ne_zero hj
      rw [hvj]
      symm
      have hsingle : ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0),
            (Pi.single (M := fun _ => ZMod 2) i (1 : ZMod 2)) j
          = (Pi.single (M := fun _ => ZMod 2) j (1 : ZMod 2)) j :=
        Finset.sum_eq_single (s := Finset.univ.filter (fun i => v i ≠ 0))
          (f := fun i => (Pi.single (M := fun _ => ZMod 2) i (1 : ZMod 2)) j) j
          (fun i _ hij => by
              change (Pi.single (M := fun _ => ZMod 2) i (1 : ZMod 2)) j = 0
              rw [Pi.single_eq_of_ne (Ne.symm hij)])
          (fun hj' => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) hj')
      rw [hsingle, Pi.single_eq_same (M := fun _ => ZMod 2) j 1]
  funext v
  have hF : f v = ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), F (Pi.single i (1 : ZMod 2)) := by
    conv_lhs => rw [hsum v]
    change F (∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), Pi.single i (1 : ZMod 2))
      = ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), F (Pi.single i (1 : ZMod 2))
    rw [map_sum]
  have hH : h v = ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), H (Pi.single i (1 : ZMod 2)) := by
    conv_lhs => rw [hsum v]
    change H (∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), Pi.single i (1 : ZMod 2))
      = ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), H (Pi.single i (1 : ZMod 2))
    rw [map_sum]
  rw [hF, hH]
  apply Finset.sum_congr rfl
  intro i _
  change f (Pi.single i (1 : ZMod 2)) = h (Pi.single i (1 : ZMod 2))
  exact hs i

private lemma natOfVec_heartCoord_pair {a b : Fin 8} (hab : a ≠ b) :
    natOfVec (heartCoord (Pi.single a (1 : ZMod 2) + Pi.single b 1)) = heartPair a.val b.val := by
  revert a b
  decide +kernel

theorem asc82Fact59_proof : Asc82Fact59 := by
  intro g had hg
  obtain ⟨σ, hbasis⟩ := exists_perm_heart g had hg
  let gσ : (Fin 6 → ZMod 2) → (Fin 6 → ZMod 2) :=
    fun v => heartCoord (permVec σ (evenLift v))
  have hgσ_add : ∀ v w, gσ (v + w) = gσ v + gσ w := by
    intro v w
    simp only [gσ, evenLift_add, sec5b_permVec_add, sec5b_heartCoord_add]
  have hagree : ∀ i : Fin 6, g (Pi.single i 1) = gσ (Pi.single i 1) := by
    intro i
    have hne : σ (Fin.castLE (by norm_num : 6 ≤ 8) i) ≠ σ 6 := by
      intro hh
      have hval : i.val = 6 := by
        simpa using congrArg Fin.val (σ.injective hh)
      omega
    have hgσ : gσ (Pi.single i (1 : ZMod 2))
        = heartCoord (Pi.single (σ (Fin.castLE (by norm_num : 6 ≤ 8) i)) (1 : ZMod 2)
            + Pi.single (σ 6) 1) := by
      simp only [gσ, evenLift_single, sec5b_permVec_add, permVec_single]
    rw [hgσ, ← vecOfNat_natOfVec (g (Pi.single i 1)), hbasis i, ← natOfVec_heartCoord_pair hne,
      vecOfNat_natOfVec]
  have hg_eq : g = gσ := eq_of_agree_single had hgσ_add hagree
  refine ⟨σ, ?_⟩
  intro w hw
  rw [hg_eq]
  change heartCoord (permVec σ (evenLift (heartCoord w))) = heartCoord (permVec σ w)
  rcases sec5b_heartCoord_inj (evenLift_even (heartCoord w)) hw (heartCoord_evenLift (heartCoord w))
    with hw' | hw'
  · conv_rhs => rw [hw']
  · conv_rhs => rw [hw', sec5b_permVec_add, sec5b_permVec_one, sec5b_heartCoord_add_one]

end CFSG.OddStandard.SmallF3.Omega

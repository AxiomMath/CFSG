module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhUnions
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

public section

namespace CFSG.EvenSmallLie.OmegaEight

open Finset

@[expose] def IsClique9 {Ω : Type*} (Y : Finset Ω) (adj : Ω → Ω → Prop) (K : Finset Ω) : Prop :=
  K ⊆ Y ∧ K.card = 9 ∧ ∀ a ∈ K, ∀ b ∈ K, a ≠ b → adj a b

theorem false_of_star_orientation {N Ω : Type*} [Group N] [MulAction N Ω] [Fintype Ω]
    [DecidableEq Ω] (Y : Finset Ω) (z : Ω) (horb : ∀ y, y ∈ Y ↔ ∃ n : N, n • z = y)
    (adj : Ω → Ω → Prop) (hadj : ∀ (n : N) a b, adj a b → adj (n • a) (n • b))
    {K₁ K₂ K₃ : Finset Ω} (hK₁ : IsClique9 Y adj K₁) (hK₂ : IsClique9 Y adj K₂)
    (hK₃ : IsClique9 Y adj K₃) (hz₁ : z ∈ K₁) (hz₂ : z ∈ K₂) (h₁₂ : K₁ ≠ K₂)
    (hthrough : ∀ K, IsClique9 Y adj K → z ∈ K → K = K₁ ∨ K = K₂)
    (hfix : ∀ n : N, n • z = z → ∀ y ∈ K₁, n • y ∈ K₁) {w₁ w₂ : Ω} (hw₁ : w₁ ∈ K₁)
    (hw₁' : w₁ ∈ K₃) (hw₂ : w₂ ∈ K₂) (hw₂' : w₂ ∈ K₃) (h₃₁ : K₃ ≠ K₁) (h₃₂ : K₃ ≠ K₂) :
    False := by
  classical
  have hinj : ∀ n : N, Function.Injective fun K : Finset Ω => K.image (n • ·) :=
    fun n => image_injective (MulAction.injective n)
  have hYsmul : ∀ (n : N) y, y ∈ Y → n • y ∈ Y := by
    intro n y hy
    obtain ⟨m, rfl⟩ := (horb y).mp hy
    exact (horb _).mpr ⟨n * m, mul_smul n m z⟩
  have himg : ∀ (n : N) K, IsClique9 Y adj K → IsClique9 Y adj (K.image (n • ·)) := by
    intro n K ⟨hKY, hK9, hKadj⟩
    refine ⟨fun x hx => ?_, ?_, ?_⟩
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact hYsmul n y (hKY hy)
    · rw [card_image_of_injective _ (MulAction.injective n), hK9]
    · intro a ha b hb hab
      obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
      obtain ⟨b', hb', rfl⟩ := mem_image.mp hb
      exact hadj n a' b' (hKadj a' ha' b' hb' fun e => hab (by rw [e]))
  have himg_inv : ∀ (n : N) (K : Finset Ω), (K.image (n • ·)).image (n⁻¹ • ·) = K := by
    intro n K
    rw [image_image]
    simp [Function.comp_def]
  have hthrough' : ∀ (n : N) K, IsClique9 Y adj K → n • z ∈ K →
      K = K₁.image (n • ·) ∨ K = K₂.image (n • ·) := by
    intro n K hK hnz
    have hK' := himg n⁻¹ K hK
    have hzK' : z ∈ K.image (n⁻¹ • ·) := mem_image.mpr ⟨n • z, hnz, inv_smul_smul n z⟩
    rcases hthrough _ hK' hzK' with h | h
    · left
      rw [← h]
      rw [image_image]
      simp [Function.comp_def]
    · right
      rw [← h]
      rw [image_image]
      simp [Function.comp_def]
  have hzY : z ∈ Y := hK₁.1 hz₁
  have hK₂orb : ∃ n : N, K₂ = K₁.image (n • ·) := by
    obtain ⟨n₁, hn₁⟩ := (horb w₁).mp (hK₁.1 hw₁)
    obtain ⟨n₂, hn₂⟩ := (horb w₂).mp (hK₂.1 hw₂)
    have a1 := hthrough' n₁ K₁ hK₁ (hn₁ ▸ hw₁)
    have a3 := hthrough' n₁ K₃ hK₃ (hn₁ ▸ hw₁')
    have b2 := hthrough' n₂ K₂ hK₂ (hn₂ ▸ hw₂)
    have b3 := hthrough' n₂ K₃ hK₃ (hn₂ ▸ hw₂')
    by_cases c1 : K₁ = K₂.image (n₁ • ·)
    · refine ⟨n₁⁻¹, ?_⟩
      rw [c1, himg_inv]
    by_cases c2 : K₂ = K₁.image (n₂ • ·)
    · exact ⟨n₂, c2⟩
    have e1 : K₁ = K₁.image (n₁ • ·) := a1.resolve_right c1
    have e2 : K₂ = K₂.image (n₂ • ·) := b2.resolve_left c2
    have e3 : K₃ = K₂.image (n₁ • ·) := a3.resolve_left fun h => h₃₁ (h.trans e1.symm)
    have e4 : K₃ = K₁.image (n₂ • ·) := b3.resolve_right fun h => h₃₂ (h.trans e2.symm)
    refine ⟨n₁⁻¹ * n₂, ?_⟩
    have : K₂ = (K₁.image (n₂ • ·)).image (n₁⁻¹ • ·) := by
      rw [← e4, e3, himg_inv]
    rw [this, image_image]
    refine image_congr fun x _ => ?_
    simp [mul_smul]
  obtain ⟨m₂, hm₂⟩ := hK₂orb
  set Sig : Finset (Finset Ω) := univ.filter fun K => ∃ n : N, K = K₁.image (n • ·)
  have hSigclq : ∀ K ∈ Sig, IsClique9 Y adj K := by
    intro K hK
    simp only [Sig, mem_filter, mem_univ, true_and] at hK
    obtain ⟨n, rfl⟩ := hK
    exact himg n K₁ hK₁
  have hK₁Sig : K₁ ∈ Sig := by
    simp only [Sig, mem_filter, mem_univ, true_and]
    exact ⟨1, by simp⟩
  have hSig_smul : ∀ (n : N) K, K ∈ Sig → K.image (n • ·) ∈ Sig := by
    intro n K hK
    simp only [Sig, mem_filter, mem_univ, true_and] at hK ⊢
    obtain ⟨m, rfl⟩ := hK
    refine ⟨n * m, ?_⟩
    rw [image_image]
    refine image_congr fun x _ => ?_
    simp [mul_smul]
  have htwo : ∀ y ∈ Y, (Sig.filter fun K => y ∈ K).card = 2 := by
    intro y hy
    obtain ⟨n, rfl⟩ := (horb y).mp hy
    have hne : K₁.image (n • ·) ≠ K₂.image (n • ·) := fun h => h₁₂ (hinj n h)
    have heq : (Sig.filter fun K => n • z ∈ K) = {K₁.image (n • ·), K₂.image (n • ·)} := by
      ext K
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hK, hzK⟩
        exact hthrough' n K (hSigclq K hK) hzK
      · rintro (rfl | rfl)
        · exact ⟨hSig_smul n K₁ hK₁Sig, mem_image_of_mem _ hz₁⟩
        · refine ⟨hSig_smul n K₂ ?_, mem_image_of_mem _ hz₂⟩
          rw [hm₂]
          exact hSig_smul m₂ K₁ hK₁Sig
    rw [heq, card_pair hne]
  have hcountA := card_mul_eq_card_mul (fun (K : Finset Ω) y => y ∈ K) (s := Sig) (t := Y)
    (m := 9) (n := 2) (fun K hK => ?_) (fun y hy => htwo y hy)
  rotate_left
  · have hKY := (hSigclq K hK).1
    have : Y.bipartiteAbove (fun (K : Finset Ω) y => y ∈ K) K = K := by
      ext y
      simp only [mem_bipartiteAbove]
      exact ⟨fun h => h.2, fun h => ⟨hKY h, h⟩⟩
    rw [this, (hSigclq K hK).2.1]
  have hchoice : ∀ y ∈ Y, ∃ n : N, n • z = y := fun y hy => (horb y).mp hy
  let F : Ω → Finset Ω := fun y =>
    if hy : y ∈ Y then K₁.image ((hchoice y hy).choose • ·) else ∅
  have hFwd : ∀ (n : N) y, n • z = y → F y = K₁.image (n • ·) := by
    intro n y hn
    have hy : y ∈ Y := (horb y).mpr ⟨n, hn⟩
    simp only [F, hy, dite_true]
    set m := (hchoice y hy).choose
    have hm : m • z = y := (hchoice y hy).choose_spec
    have hfz : (n⁻¹ * m) • z = z := by rw [mul_smul, hm, ← hn, inv_smul_smul]
    have hK₁fix : K₁.image ((n⁻¹ * m) • ·) = K₁ := by
      apply eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨y', hy', rfl⟩ := mem_image.mp hx
        exact hfix _ hfz y' hy'
      · rw [card_image_of_injective _ (MulAction.injective _)]
    calc K₁.image (m • ·) = (K₁.image ((n⁻¹ * m) • ·)).image (n • ·) := by
          rw [image_image]
          refine image_congr fun x _ => ?_
          simp [mul_smul]
      _ = K₁.image (n • ·) := by rw [hK₁fix]
  have hFSig : ∀ y ∈ Y, F y ∈ Sig := by
    intro y hy
    obtain ⟨n, hn⟩ := (horb y).mp hy
    rw [hFwd n y hn]
    exact hSig_smul n K₁ hK₁Sig
  have hcountB := card_eq_sum_card_fiberwise hFSig
  have hfib : ∀ K ∈ Sig, (Y.filter fun y => F y = K).card = (Y.filter fun y => F y = K₁).card := by
    intro K hK
    simp only [Sig, mem_filter, mem_univ, true_and] at hK
    obtain ⟨m, rfl⟩ := hK
    symm
    apply card_nbij' (m • ·) (m⁻¹ • ·)
    · intro y hy
      simp only [coe_filter, Set.mem_ofPred_eq] at hy ⊢
      refine ⟨hYsmul m y hy.1, ?_⟩
      obtain ⟨n, hn⟩ := (horb y).mp hy.1
      have h2 : K₁.image (n • ·) = K₁ := (hFwd n y hn).symm.trans hy.2
      rw [hFwd (m * n) (m • y) (by rw [mul_smul, hn])]
      calc K₁.image ((m * n) • ·) = (K₁.image (n • ·)).image (m • ·) := by
            rw [image_image]
            refine image_congr fun x _ => ?_
            simp [mul_smul]
        _ = K₁.image (m • ·) := by rw [h2]
    · intro y hy
      simp only [coe_filter, Set.mem_ofPred_eq] at hy ⊢
      refine ⟨hYsmul m⁻¹ y hy.1, ?_⟩
      obtain ⟨n, hn⟩ := (horb y).mp hy.1
      have h1 := hFwd (m⁻¹ * n) (m⁻¹ • y) (by rw [mul_smul, hn])
      have h2 := hFwd n y hn
      rw [h2] at hy
      have h3 : K₁.image (n • ·) = K₁.image (m • ·) := hy.2
      rw [h1]
      have h4 : K₁.image ((m⁻¹ * n) • ·) = (K₁.image (n • ·)).image (m⁻¹ • ·) := by
        rw [image_image]
        refine image_congr fun x _ => ?_
        simp [mul_smul]
      rw [h4, h3, himg_inv]
    · intro y _
      exact inv_smul_smul m y
    · intro y _
      exact smul_inv_smul m y
  rw [sum_congr rfl hfib, sum_const, smul_eq_mul] at hcountB
  have hSigpos : 0 < Sig.card := card_pos.mpr ⟨K₁, hK₁Sig⟩
  rw [hcountB] at hcountA
  have h' : Sig.card * 9 = Sig.card * ((Y.filter fun y => F y = K₁).card * 2) := by
    rw [hcountA, mul_assoc]
  have h9 := Nat.eq_of_mul_eq_mul_left hSigpos h'
  omega

@[expose] def starNine : Finset FrameVec := insert frameZ (univ.image frameE)

@[expose] def starNine' : Finset FrameVec := insert frameZ (univ.image fun i => frameZ + frameE i)

@[expose] def starZero : Finset FrameVec :=
  insert (frameE 0) (insert (frameZ + frameE 0) ((univ.erase 0).image fun j => frameE 0 + frameE j))

instance (v : FrameVec) : Decidable (v ∈ frameFortyFive) :=
  inferInstanceAs (Decidable (frameCls v = 1 ∨ frameCls v = 2 ∨ frameCls v = 8 ∨ frameCls v = 9))

@[expose] def fortyFiveSet : Finset FrameVec := univ.filter fun v => v ∈ frameFortyFive

@[expose] def fortyFiveAdj (a b : FrameVec) : Prop := a + b ∈ frameFortyFive

theorem isClique9_of {K : Finset FrameVec} (h1 : ∀ v ∈ K, v ∈ frameFortyFive) (h2 : K.card = 9)
    (h3 : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → a + b ∈ frameFortyFive) :
    IsClique9 fortyFiveSet fortyFiveAdj K :=
  ⟨fun v hv => mem_filter.mpr ⟨mem_univ v, h1 v hv⟩, h2, h3⟩

theorem star_cliques :
    IsClique9 fortyFiveSet fortyFiveAdj starNine ∧ IsClique9 fortyFiveSet fortyFiveAdj starNine' ∧
      IsClique9 fortyFiveSet fortyFiveAdj starZero :=
  ⟨isClique9_of (by decide +kernel) (by decide +kernel) (by decide +kernel),
    isClique9_of (by decide +kernel) (by decide +kernel) (by decide +kernel),
    isClique9_of (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem star_facts : frameZ ∈ starNine ∧ frameZ ∈ starNine' ∧ starNine ≠ starNine' ∧
    frameE 0 ∈ starNine ∧ frameE 0 ∈ starZero ∧ frameZ + frameE 0 ∈ starNine' ∧
    frameZ + frameE 0 ∈ starZero ∧ starZero ≠ starNine ∧ starZero ≠ starNine' := by
  decide +kernel

theorem star_through_aux : ∀ n < 256, (frameDecode n ∈ frameFortyFive ∧
    frameDecode n + frameZ ∈ frameFortyFive) → frameDecode n ∈ starNine ∨
      frameDecode n ∈ starNine' := by
  decide +kernel

theorem star_cross : ∀ a ∈ starNine, ∀ b ∈ starNine', a ≠ frameZ → b ≠ frameZ →
    a + b ∈ frameFortyFive → b = a + frameZ := by
  decide +kernel

theorem clique_through_frameZ (K : Finset FrameVec)
    (hK : IsClique9 fortyFiveSet fortyFiveAdj K) (hzK : frameZ ∈ K) :
    K = starNine ∨ K = starNine' := by
  obtain ⟨hKY, hK9, hKadj⟩ := hK
  have hsub : ∀ a ∈ K, a ∈ starNine ∨ a ∈ starNine' := by
    intro a ha
    by_cases haz : a = frameZ
    · left
      rw [haz]
      exact star_facts.1
    · have h1 : a ∈ frameFortyFive := (mem_filter.mp (hKY ha)).2
      have h2 : a + frameZ ∈ frameFortyFive := hKadj a ha frameZ hzK haz
      obtain ⟨n, hn, rfl⟩ := frameDecode_surjective a
      exact star_through_aux n hn ⟨h1, h2⟩
  by_cases hA : K ⊆ starNine
  · exact Or.inl (eq_of_subset_of_card_le hA (by rw [hK9, star_cliques.1.2.1]))
  by_cases hB : K ⊆ starNine'
  · exact Or.inr (eq_of_subset_of_card_le hB (by rw [hK9, star_cliques.2.1.2.1]))
  exfalso
  obtain ⟨b, hbK, hbA⟩ := not_subset.mp hA
  obtain ⟨a, haK, haB⟩ := not_subset.mp hB
  have ha1 : a ∈ starNine := (hsub a haK).resolve_right haB
  have hb2 : b ∈ starNine' := (hsub b hbK).resolve_left hbA
  have haz : a ≠ frameZ := fun h => haB (h ▸ star_facts.2.1)
  have hbz : b ≠ frameZ := fun h => hbA (h ▸ star_facts.1)
  have hab : a ≠ b := fun h => hbA (h ▸ ha1)
  have hba : b = a + frameZ := star_cross a ha1 b hb2 haz hbz (hKadj a haK b hbK hab)
  have hK3 : K ⊆ {frameZ, a, b} := by
    intro c hc
    simp only [mem_insert, mem_singleton]
    by_cases hcz : c = frameZ
    · exact Or.inl hcz
    rcases hsub c hc with hc1 | hc2
    · by_contra hcne
      have hca : c ≠ a := fun h => hcne (Or.inr (Or.inl h))
      have hcb : c ≠ b := fun h => hbA (h ▸ hc1)
      have h' := star_cross c hc1 b hb2 hcz hbz (hKadj c hc b hbK hcb)
      rw [hba] at h'
      exact hca (add_right_cancel h'.symm)
    · by_contra hcne
      have hcb : c ≠ b := fun h => hcne (Or.inr (Or.inr h))
      have hac : a ≠ c := fun h => haB (h ▸ hc2)
      have h' := star_cross a ha1 c hc2 haz hcz (hKadj a haK c hc hac)
      exact hcb (h'.trans hba.symm)
  have h1 := card_le_card hK3
  have h2 : ({frameZ, a, b} : Finset FrameVec).card ≤ 3 := card_le_three
  omega

theorem orbit_ne_frameFortyFive {N : Type*} [Group N] [MulAction N FrameVec]
    (hadd : ∀ (n : N) (x y : FrameVec), n • (x + y) = n • x + n • y)
    (hup : ∀ n : N, n • frameZ = frameZ → ∃ σ ∈ frameAut, ∀ v, n • v = permVec σ v) :
    MulAction.orbit N frameZ ≠ frameFortyFive := by
  intro horb
  have hY : ∀ y, y ∈ fortyFiveSet ↔ ∃ n : N, n • frameZ = y := by
    intro y
    rw [fortyFiveSet, mem_filter, ← horb]
    exact ⟨fun h => h.2, fun h => ⟨mem_univ y, h⟩⟩
  have hadj : ∀ (n : N) a b, fortyFiveAdj a b → fortyFiveAdj (n • a) (n • b) := by
    intro n a b hab
    unfold fortyFiveAdj at hab ⊢
    rw [← hadd, ← horb]
    rw [← horb] at hab
    obtain ⟨m, hm⟩ := hab
    change m • frameZ = a + b at hm
    exact ⟨n * m, by change (n * m) • frameZ = _; rw [mul_smul, hm]⟩
  have hfix : ∀ n : N, n • frameZ = frameZ → ∀ y ∈ starNine, n • y ∈ starNine := by
    intro n hn y hy
    obtain ⟨σ, -, hσ⟩ := hup n hn
    rw [hσ]
    simp only [starNine, mem_insert, mem_image, mem_univ, true_and] at hy ⊢
    rcases hy with rfl | ⟨i, rfl⟩
    · exact Or.inl (permVec_frameZ σ)
    · exact Or.inr ⟨σ i, (permVec_frameE σ i).symm⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := star_facts
  exact false_of_star_orientation fortyFiveSet frameZ hY fortyFiveAdj hadj star_cliques.1
    star_cliques.2.1 star_cliques.2.2 h1 h2 h3 clique_through_frameZ hfix h4 h5 h6 h7 h8 h9

end CFSG.EvenSmallLie.OmegaEight

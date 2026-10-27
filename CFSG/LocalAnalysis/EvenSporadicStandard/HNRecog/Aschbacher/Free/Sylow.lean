module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Setup

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

variable {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]

private abbrev A5 : Type := alternatingGroup (Fin 5)

private theorem natCard_A5 : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem natCard_A5WrTwo : Nat.card A5WrTwo = 7200 := by
  haveI : Finite (Multiplicative (ZMod 2)) := inferInstance
  rw [RegularWreathProduct.card]
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [h5, h2]
  norm_num

private theorem exists_snd_ne_one_mem {S : Subgroup (A5 × A5)} (hS : IsPGroup 2 S)
    (hcard : 16 ≤ Nat.card S) : ∃ y : A5, y ≠ 1 ∧ (1, y) ∈ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f1 : A5 × A5 →* A5 := MonoidHom.fst A5 A5
  let f1S : S →* A5 := f1.comp S.subtype
  have hrange : f1S.range = S.map f1 := by
    change (f1.comp S.subtype).range = S.map f1
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map (g := f1) (f := S.subtype),
      Subgroup.map_top, Subgroup.range_subtype]
  have hS1 : IsPGroup 2 (S.map f1) := hS.map f1
  obtain ⟨n, hn⟩ := hS1.exists_card_eq
  have hdvd : 2 ^ n ∣ 60 := by
    have h := Subgroup.card_subgroup_dvd_card (S.map f1)
    rwa [natCard_A5, hn] at h
  have hfac60 : Nat.factorization 60 2 = 2 := by
    rw [show (60 : ℕ) = 2 ^ 2 * 15 by norm_num,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]
  have hn2 : n ≤ 2 := by
    have h := (Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (k := n) (n := 60)
      (by norm_num) (by norm_num)).mp hdvd
    rwa [hfac60] at h
  have hS1card : Nat.card (S.map f1) ≤ 4 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
      _ = 4 := by norm_num
  have hker : 4 ≤ Nat.card f1S.ker := by
    have h := Subgroup.card_ker_mul_card_range f1S
    rw [hrange] at h
    have h1 : 4 * Nat.card (S.map f1) ≤ Nat.card f1S.ker * Nat.card (S.map f1) := by
      calc 4 * Nat.card (S.map f1) ≤ 16 := by
            simpa using Nat.mul_le_mul_left 4 hS1card
        _ ≤ Nat.card S := hcard
        _ = Nat.card f1S.ker * Nat.card (S.map f1) := h.symm
    exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  have hne : f1S.ker ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha_fst : (a.1 : A5 × A5).1 = 1 := by
    have hmem : f1S a.1 = 1 := MonoidHom.mem_ker.mp a.2
    simpa [f1S, f1] using hmem
  refine ⟨(a.1 : A5 × A5).2, ?_, ?_⟩
  · intro hy
    exact ha (Subtype.ext (Subtype.ext (Prod.ext ha_fst hy)))
  · have h1 : (a.1 : A5 × A5) = (1, (a.1 : A5 × A5).2) := Prod.ext ha_fst rfl
    rw [← h1]
    exact a.1.2

private theorem exists_fst_ne_one_mem {S : Subgroup (A5 × A5)} (hS : IsPGroup 2 S)
    (hcard : 16 ≤ Nat.card S) : ∃ x : A5, x ≠ 1 ∧ (x, 1) ∈ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f2 : A5 × A5 →* A5 := MonoidHom.snd A5 A5
  let f2S : S →* A5 := f2.comp S.subtype
  have hrange : f2S.range = S.map f2 := by
    change (f2.comp S.subtype).range = S.map f2
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map (g := f2) (f := S.subtype),
      Subgroup.map_top, Subgroup.range_subtype]
  have hS1 : IsPGroup 2 (S.map f2) := hS.map f2
  obtain ⟨n, hn⟩ := hS1.exists_card_eq
  have hdvd : 2 ^ n ∣ 60 := by
    have h := Subgroup.card_subgroup_dvd_card (S.map f2)
    rwa [natCard_A5, hn] at h
  have hfac60 : Nat.factorization 60 2 = 2 := by
    rw [show (60 : ℕ) = 2 ^ 2 * 15 by norm_num,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]
  have hn2 : n ≤ 2 := by
    have h := (Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (k := n) (n := 60)
      (by norm_num) (by norm_num)).mp hdvd
    rwa [hfac60] at h
  have hS1card : Nat.card (S.map f2) ≤ 4 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
      _ = 4 := by norm_num
  have hker : 4 ≤ Nat.card f2S.ker := by
    have h := Subgroup.card_ker_mul_card_range f2S
    rw [hrange] at h
    have h1 : 4 * Nat.card (S.map f2) ≤ Nat.card f2S.ker * Nat.card (S.map f2) := by
      calc 4 * Nat.card (S.map f2) ≤ 16 := by
            simpa using Nat.mul_le_mul_left 4 hS1card
        _ ≤ Nat.card S := hcard
        _ = Nat.card f2S.ker * Nat.card (S.map f2) := h.symm
    exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  have hne : f2S.ker ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha_snd : (a.1 : A5 × A5).2 = 1 := by
    have hmem : f2S a.1 = 1 := MonoidHom.mem_ker.mp a.2
    simpa [f2S, f2] using hmem
  refine ⟨(a.1 : A5 × A5).1, ?_, ?_⟩
  · intro hx
    exact ha (Subtype.ext (Subtype.ext (Prod.ext hx ha_snd)))
  · have h1 : (a.1 : A5 × A5) = ((a.1 : A5 × A5).1, 1) := Prod.ext rfl ha_snd
    rw [← h1]
    exact a.1.2

theorem AschbacherHyp.exists_sylow_meets_factors [Finite C] (hC : AschbacherHyp C Q)
    (θ : ↥(commutator C) →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))
    (hθs : Function.Surjective θ) (hθk : ∀ l : ↥(commutator C), θ l = 1 ↔ (l : C) ∈ Q)
    {t : C} (ht : t ∉ commutator C) (ht2 : t ^ 2 = 1) :
    ∃ T : Sylow 2 C, t ∈ T ∧
      (∃ x : alternatingGroup (Fin 5), x ≠ 1 ∧
        ∃ l : ↥(commutator C), (l : C) ∈ (T : Subgroup C) ∧ θ l = (x, 1)) ∧
      (∃ y : alternatingGroup (Fin 5), y ≠ 1 ∧
        ∃ l : ↥(commutator C), (l : C) ∈ (T : Subgroup C) ∧ θ l = (1, y)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hQfin : Finite Q := hC.plus.finite
  let L : Subgroup C := commutator C
  have hcardQ : Nat.card Q = 2 ^ 9 := by
    have h := hC.plus.2.1
    norm_num at h ⊢
    exact h
  have hcardQuot : Nat.card (C ⧸ Q) = 7200 := by
    obtain ⟨e⟩ := hC.quotient
    rw [Nat.card_congr e.toEquiv, natCard_A5WrTwo]
  have hcardC : Nat.card C = 2 ^ 14 * 225 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Q, hcardQuot, hcardQ]
    norm_num
  have hfac : Nat.factorization (Nat.card C) 2 = 14 := by
    rw [hcardC, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 225)]
  have ht_order : orderOf t ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ht2
  have hzpg : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    simpa using ht_order
  obtain ⟨T, hTle⟩ := hzpg.exists_le_sylow
  have htT : t ∈ T := hTle (Subgroup.mem_zpowers t)
  have hcardT : Nat.card T = 2 ^ 14 := by
    rw [Sylow.card_eq_multiplicity, hfac]
  let M : Subgroup C := (T : Subgroup C) ⊓ L
  have hMleT : M ≤ (T : Subgroup C) := inf_le_left
  have hMleL : M ≤ L := inf_le_right
  have hcardT2 : Nat.card M * L.relIndex T = Nat.card T := by
    have hrel := Subgroup.relIndex_mul_card (H := L) (K := (T : Subgroup C))
    rw [inf_comm] at hrel
    rw [mul_comm]
    exact hrel
  have hr2 : L.relIndex T ≤ 2 := by
    have hdiv : L.relIndex T ∣ L.index :=
      Subgroup.relIndex_dvd_index_of_normal (H := L) (K := (T : Subgroup C))
    have hidx : L.index = 2 := hC.index_commutator
    rw [hidx] at hdiv
    exact Nat.le_of_dvd (by norm_num) hdiv
  have hcardM : 2 ^ 13 ≤ Nat.card M := by
    have h : Nat.card M * L.relIndex T = 2 ^ 14 := by
      rw [hcardT2, hcardT]
    have h2 : 2 ^ 13 * 2 ≤ Nat.card M * 2 := by
      calc 2 ^ 13 * 2 = 2 ^ 14 := by norm_num
        _ = Nat.card M * L.relIndex T := h.symm
        _ ≤ Nat.card M * 2 := Nat.mul_le_mul_left _ hr2
    exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
  let φ : M →* (A5 × A5) :=
    { toFun := fun m => θ ⟨(m : C), hMleL m.2⟩
      map_one' := by
        rw [show (⟨((1 : M) : C), hMleL (1 : M).2⟩ : L) = 1 from Subtype.ext rfl, map_one]
      map_mul' := fun a b => by
        rw [show (⟨((a * b : M) : C), hMleL (a * b).2⟩ : L) =
              ⟨(a : C), hMleL a.2⟩ * ⟨(b : C), hMleL b.2⟩ from Subtype.ext rfl, map_mul] }
  let S : Subgroup (A5 × A5) := φ.range
  have hker_le_cardQ : Nat.card φ.ker ≤ Nat.card Q := by
    let f : φ.ker → Q := fun k =>
      ⟨(k.1 : C), (hθk ⟨(k.1 : C), hMleL k.1.2⟩).mp (by
        have hk : φ k.1 = 1 := MonoidHom.mem_ker.mp k.2
        simpa [φ] using hk)⟩
    refine Nat.card_le_card_of_injective f ?_
    intro k k' h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : Q => (q : C)) h
  have hS_p : IsPGroup 2 S := by
    have hM_p : IsPGroup 2 M := T.isPGroup'.to_le hMleT
    exact hM_p.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hS16 : 16 ≤ Nat.card S := by
    have hM := Subgroup.card_ker_mul_card_range φ
    have hker9 : Nat.card φ.ker ≤ 2 ^ 9 := hker_le_cardQ.trans (le_of_eq hcardQ)
    have hle : Nat.card φ.ker * Nat.card S ≤ 2 ^ 9 * Nat.card S :=
      Nat.mul_le_mul_right _ hker9
    have hge : 2 ^ 9 * 2 ^ 4 ≤ Nat.card φ.ker * Nat.card S := by
      calc 2 ^ 9 * 2 ^ 4 = 2 ^ 13 := by norm_num
        _ ≤ Nat.card M := hcardM
        _ = Nat.card φ.ker * Nat.card S := hM.symm
    have hfin : 2 ^ 9 * 2 ^ 4 ≤ 2 ^ 9 * Nat.card S := hge.trans hle
    have h := Nat.le_of_mul_le_mul_left hfin (by norm_num : (0 : ℕ) < 2 ^ 9)
    simpa using h
  obtain ⟨y, hy, hys⟩ := exists_snd_ne_one_mem (S := S) hS_p hS16
  obtain ⟨x, hx, hxs⟩ := exists_fst_ne_one_mem (S := S) hS_p hS16
  refine ⟨T, htT, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (show (x, 1) ∈ φ.range from hxs)
    exact ⟨x, hx, ⟨⟨(m : C), hMleL m.2⟩, hMleT m.2, by simpa [φ] using hm⟩⟩
  · obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (show (1, y) ∈ φ.range from hys)
    exact ⟨y, hy, ⟨⟨(m : C), hMleL m.2⟩, hMleT m.2, by simpa [φ] using hm⟩⟩

end CFSG.EvenSporadicStandard.HNRecog
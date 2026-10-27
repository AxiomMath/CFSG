module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Mask

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open Equiv

structure Enum (S : Subgroup (Perm (Fin 24))) where
  N : ℕ
  e : ℕ → Perm (Fin 24)
  mulIdx : ℕ → ℕ → ℕ
  cols : ℕ → List ℕ
  mem : ∀ i < N, e i ∈ S
  surj : ∀ x ∈ S, ∃ i < N, e i = x
  inj : ∀ i < N, ∀ j < N, e i = e j → i = j
  pos : 0 < N
  zero : e 0 = 1
  mul : ∀ i < N, e i ≠ 1 → e i * e i = 1 → ∀ j < N, mulIdx i j < N ∧ e (mulIdx i j) = e i * e j
  fixed : ∀ i < N, ∀ m < 4096, act (e i) (synOfMask m) = synOfMask m → xorImg (cols i) m = m

section Search

variable (mulIdx : ℕ → ℕ → ℕ) (cols : ℕ → List ℕ)

@[expose] def validExt (V : List ℕ) (c : ℕ) : Bool :=
  !V.contains c && V.all fun v => v == 0 || decide (c < mulIdx c v)

@[expose] def extV (V : List ℕ) (c : ℕ) : List ℕ := V ++ V.map (mulIdx c)

@[expose] def extF (F : List ℕ) (c : ℕ) : List ℕ :=
  let cs := cols c
  F.filter fun m => xorImg cs m == m

@[expose] def extC (cand : List ℕ) (c : ℕ) : List ℕ :=
  cand.filter fun d => decide (c < d) && mulIdx c d == mulIdx d c

@[expose] def children (d : List ℕ → List ℕ → List ℕ → Bool) (V F cand : List ℕ) : Bool :=
  cand.all fun c =>
    !validExt mulIdx V c || d (extV mulIdx V c) (extF cols F c) (extC mulIdx cand c)

@[expose] def dfs : ℕ → List ℕ → List ℕ → List ℕ → Bool
  | 0, V, F, _ => decide (V.length * F.length ≤ 2 ^ 11)
  | n + 1, V, F, cand =>
      decide (V.length * F.length ≤ 2 ^ 11) && children mulIdx cols (dfs n) V F cand

end Search

@[expose] def extSub (U : Subgroup (Perm (Fin 24))) (c : Perm (Fin 24)) (hc : c * c = 1)
    (hcomm : ∀ u ∈ U, c * u = u * c) : Subgroup (Perm (Fin 24)) where
  carrier := {x | x ∈ U ∨ ∃ u ∈ U, x = c * u}
  mul_mem' := by
    rintro x y (hx | ⟨u, hu, rfl⟩) (hy | ⟨v, hv, rfl⟩)
    · exact Or.inl (U.mul_mem hx hy)
    · refine Or.inr ⟨x * v, U.mul_mem hx hv, ?_⟩
      rw [← mul_assoc, ← hcomm x hx, mul_assoc]
    · exact Or.inr ⟨u * y, U.mul_mem hu hy, by rw [mul_assoc]⟩
    · refine Or.inl ?_
      have : c * u * (c * v) = u * v := by
        calc c * u * (c * v) = c * (u * c) * v := by simp only [mul_assoc]
          _ = c * (c * u) * v := by rw [← hcomm u hu]
          _ = (c * c) * u * v := by simp only [mul_assoc]
          _ = u * v := by rw [hc, one_mul]
      rw [this]
      exact U.mul_mem hu hv
  one_mem' := Or.inl U.one_mem
  inv_mem' := by
    rintro x (hx | ⟨u, hu, rfl⟩)
    · exact Or.inl (U.inv_mem hx)
    · refine Or.inr ⟨u⁻¹, U.inv_mem hu, ?_⟩
      have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
      rw [mul_inv_rev, hcinv]
      exact (hcomm u⁻¹ (U.inv_mem hu)).symm

theorem mem_extSub {U : Subgroup (Perm (Fin 24))} {c : Perm (Fin 24)} {hc : c * c = 1}
    {hcomm : ∀ u ∈ U, c * u = u * c} {x : Perm (Fin 24)} :
    x ∈ extSub U c hc hcomm ↔ x ∈ U ∨ ∃ u ∈ U, x = c * u := Iff.rfl

variable {S : Subgroup (Perm (Fin 24))}

@[expose] def Enum.IdxList (E : Enum S) (V : List ℕ) (U : Subgroup (Perm (Fin 24))) : Prop :=
  V.Nodup ∧ ∀ i, i ∈ V ↔ i < E.N ∧ E.e i ∈ U

theorem Enum.IdxList.length_eq {E : Enum S} {V : List ℕ} {U : Subgroup (Perm (Fin 24))}
    (h : E.IdxList V U) (hUS : U ≤ S) : V.length = Nat.card U := by
  have hbij : Function.Bijective (fun i : {i // i ∈ V} =>
      (⟨E.e i.1, ((h.2 i.1).1 i.2).2⟩ : U)) := by
    constructor
    · intro i j hij
      apply Subtype.ext
      exact E.inj i.1 ((h.2 i.1).1 i.2).1 j.1 ((h.2 j.1).1 j.2).1 (congrArg Subtype.val hij)
    · intro u
      obtain ⟨i, hi, hiu⟩ := E.surj u.1 (hUS u.2)
      refine ⟨⟨i, (h.2 i).2 ⟨hi, hiu ▸ u.2⟩⟩, Subtype.ext hiu⟩
  rw [← natCard_subtype_mem V h.1, Nat.card_congr (Equiv.ofBijective _ hbij)]

theorem card_fixSyn_le {U : Subgroup (Perm (Fin 24))} {F : List ℕ}
    (hF : ∀ s ∈ fixSyn U, ∃ m ∈ F, synOfMask m = s) : Nat.card (fixSyn U) ≤ F.length := by
  classical
  have hsub : fixSyn U ⊆ synOfMask '' (F.toFinset : Set ℕ) := by
    intro s hs
    obtain ⟨m, hm, rfl⟩ := hF s hs
    exact ⟨m, by simpa using hm, rfl⟩
  have hfin : (F.toFinset : Set ℕ).Finite := Finset.finite_toSet _
  calc Nat.card (fixSyn U) = (fixSyn U).ncard := Nat.card_coe_set_eq _
    _ ≤ (synOfMask '' (F.toFinset : Set ℕ)).ncard :=
        Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ (F.toFinset : Set ℕ).ncard := Set.ncard_image_le hfin
    _ = F.toFinset.card := Set.ncard_coe_finset _
    _ ≤ F.length := List.toFinset_card_le F

structure Node (E : Enum S) (U B : Subgroup (Perm (Fin 24))) (t : ℕ) (V F cand : List ℕ) :
    Prop where
  idx : E.IdxList V U
  fmask : ∀ m ∈ F, m < 4096
  fix : ∀ s ∈ fixSyn U, ∃ m ∈ F, synOfMask m = s
  cand : ∀ i < E.N, t ≤ i → E.e i ≠ 1 → E.e i * E.e i = 1 → (∀ u ∈ U, E.e i * u = u * E.e i) →
    i ∈ cand
  least : ∀ i < E.N, E.e i ∈ B → E.e i ∉ U → t ≤ i

theorem Node.bound {E : Enum S} {U B : Subgroup (Perm (Fin 24))} {t : ℕ} {V F cand : List ℕ}
    (hN : Node E U B t V F cand) (hUS : U ≤ S) (hle : V.length * F.length ≤ 2 ^ 11) :
    Nat.card U * Nat.card (fixSyn U) ≤ 2 ^ 11 := by
  rw [← hN.idx.length_eq hUS]
  exact (Nat.mul_le_mul le_rfl (card_fixSyn_le hN.fix)).trans hle

theorem idxList_ext (E : Enum S) {U B : Subgroup (Perm (Fin 24))} {V : List ℕ} {c : ℕ}
    (hUB : U ≤ B) (hBS : B ≤ S) (hV : E.IdxList V U) (hcN : c < E.N) (hc1 : E.e c ≠ 1)
    (hcsq : E.e c * E.e c = 1) (hcU : E.e c ∉ U) (hcomm : ∀ u ∈ U, E.e c * u = u * E.e c) :
    E.IdxList (extV E.mulIdx V c) (extSub U (E.e c) hcsq hcomm) := by
  have hrow : ∀ j < E.N, E.mulIdx c j < E.N ∧ E.e (E.mulIdx c j) = E.e c * E.e j :=
    fun j hj => E.mul c hcN hc1 hcsq j hj
  have hVN : ∀ v ∈ V, v < E.N ∧ E.e v ∈ U := fun v hv => (hV.2 v).1 hv
  refine ⟨?_, ?_⟩
  · rw [extV, List.nodup_append]
    refine ⟨hV.1, ?_, ?_⟩
    · refine List.Nodup.map_on ?_ hV.1
      intro v₁ hv₁ v₂ hv₂ h
      have h1 := (hrow v₁ (hVN v₁ hv₁).1).2
      have h2 := (hrow v₂ (hVN v₂ hv₂).1).2
      rw [h, h2] at h1
      exact E.inj v₁ (hVN v₁ hv₁).1 v₂ (hVN v₂ hv₂).1 (mul_left_cancel h1).symm
    · intro x hx y hy hxy
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hy
      subst hxy
      have h1 := (hrow v (hVN v hv).1).2
      have hxU := (hVN _ hx).2
      rw [h1] at hxU
      apply hcU
      have := U.mul_mem hxU (U.inv_mem (hVN v hv).2)
      simpa using this
  · intro i
    rw [extV, List.mem_append, List.mem_map, mem_extSub]
    constructor
    · rintro (hi | ⟨v, hv, rfl⟩)
      · exact ⟨(hVN i hi).1, Or.inl (hVN i hi).2⟩
      · exact ⟨(hrow v (hVN v hv).1).1, Or.inr ⟨E.e v, (hVN v hv).2, (hrow v (hVN v hv).1).2⟩⟩
    · rintro ⟨hiN, hiU | ⟨u, hu, hiu⟩⟩
      · exact Or.inl ((hV.2 i).2 ⟨hiN, hiU⟩)
      · obtain ⟨j, hj, hju⟩ := E.surj u (hBS (hUB hu))
        have hjV : j ∈ V := (hV.2 j).2 ⟨hj, hju ▸ hu⟩
        refine Or.inr ⟨j, hjV, ?_⟩
        refine E.inj _ (hrow j hj).1 i hiN ?_
        rw [(hrow j hj).2, hju, hiu]

theorem validExt_of_least (E : Enum S) {U B : Subgroup (Perm (Fin 24))} {V : List ℕ} {c : ℕ}
    (hUB : U ≤ B) (hV : E.IdxList V U) (hcN : c < E.N) (hc1 : E.e c ≠ 1)
    (hcsq : E.e c * E.e c = 1) (hcB : E.e c ∈ B) (hcU : E.e c ∉ U)
    (hmin : ∀ i, i < E.N → E.e i ∈ B → E.e i ∉ U → c ≤ i) :
    validExt E.mulIdx V c = true := by
  simp only [validExt, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq]
  refine ⟨?_, fun v hv => ?_⟩
  · have : c ∉ V := fun h => hcU ((hV.2 c).1 h).2
    simpa using this
  · by_cases hv0 : v = 0
    · exact Or.inl hv0
    · right
      obtain ⟨hvN, hvU⟩ := (hV.2 v).1 hv
      obtain ⟨hmN, hme⟩ := E.mul c hcN hc1 hcsq v hvN
      have hB : E.e (E.mulIdx c v) ∈ B := by rw [hme]; exact B.mul_mem hcB (hUB hvU)
      have hnU : E.e (E.mulIdx c v) ∉ U := by
        intro h
        rw [hme] at h
        apply hcU
        have := U.mul_mem h (U.inv_mem hvU)
        simpa using this
      refine lt_of_le_of_ne (hmin _ hmN hB hnU) ?_
      intro hcm
      have h1 : E.e c = E.e c * E.e v := by
        have := hme
        rw [← hcm] at this
        exact this
      have h2 : E.e v = 1 := mul_left_cancel (a := E.e c) (h1.symm.trans (mul_one _).symm)
      apply hv0
      exact E.inj v hvN 0 E.pos (by rw [h2, E.zero])

theorem children_sound (E : Enum S) {B U : Subgroup (Perm (Fin 24))} {t : ℕ} {V F cand : List ℕ}
    (hUB : U ≤ B) (hBS : B ≤ S) (hB2 : ∀ b ∈ B, b * b = 1)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hN : Node E U B t V F cand) (hne : ¬ B ≤ U)
    (d : List ℕ → List ℕ → List ℕ → Bool)
    (hd : ∀ (U' : Subgroup (Perm (Fin 24))) (t' : ℕ) (V' F' cand' : List ℕ), U ≤ U' → U' ≤ B →
      Nat.card U' = 2 * Nat.card U → Node E U' B t' V' F' cand' → d V' F' cand' = true →
      Nat.card B * Nat.card (fixSyn B) ≤ 2 ^ 11)
    (hch : children E.mulIdx E.cols d V F cand = true) :
    Nat.card B * Nat.card (fixSyn B) ≤ 2 ^ 11 := by
  classical
  have hex : ∃ i, i < E.N ∧ E.e i ∈ B ∧ E.e i ∉ U := by
    obtain ⟨x, hxB, hxU⟩ := IsConcreteLE.not_le_iff_exists.1 hne
    obtain ⟨i, hi, rfl⟩ := E.surj x (hBS hxB)
    exact ⟨i, hi, hxB, hxU⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ i, i < E.N → E.e i ∈ B → E.e i ∉ U → Nat.find hex ≤ i :=
    fun i hi h1 h2 => Nat.find_min' hex ⟨hi, h1, h2⟩
  generalize Nat.find hex = c at hspec hmin
  obtain ⟨hcN, hcB, hcU⟩ := hspec
  have hcsq : E.e c * E.e c = 1 := hB2 _ hcB
  have hc1 : E.e c ≠ 1 := fun h => hcU (h ▸ U.one_mem)
  have hcomm : ∀ u ∈ U, E.e c * u = u * E.e c := fun u hu => hBc _ hcB u (hUB hu)
  have htc : t ≤ c := hN.least c hcN hcB hcU
  have hccand : c ∈ cand := hN.cand c hcN htc hc1 hcsq hcomm
  have hvalid := validExt_of_least E hUB hN.idx hcN hc1 hcsq hcB hcU hmin
  have hdc : d (extV E.mulIdx V c) (extF E.cols F c) (extC E.mulIdx cand c) = true := by
    have := List.all_eq_true.1 hch c hccand
    simpa [hvalid] using this
  have hUU' : U ≤ extSub U (E.e c) hcsq hcomm := fun x hx => Or.inl hx
  have hecU' : E.e c ∈ extSub U (E.e c) hcsq hcomm := Or.inr ⟨1, U.one_mem, (mul_one _).symm⟩
  have hU'B : extSub U (E.e c) hcsq hcomm ≤ B := by
    rintro x (hx | ⟨u, hu, rfl⟩)
    · exact hUB hx
    · exact B.mul_mem hcB (hUB hu)
  have hidx := idxList_ext E hUB hBS hN.idx hcN hc1 hcsq hcU hcomm
  have hcardU' : Nat.card (extSub U (E.e c) hcsq hcomm) = 2 * Nat.card U := by
    rw [← hidx.length_eq (hU'B.trans hBS), extV, List.length_append, List.length_map,
      hN.idx.length_eq (hUB.trans hBS)]
    ring
  refine hd _ (c + 1) _ _ _ hUU' hU'B hcardU' ⟨hidx, ?_, ?_, ?_, ?_⟩ hdc
  · intro m hm
    simp only [extF, List.mem_filter, beq_iff_eq] at hm
    exact hN.fmask m hm.1
  · intro s hs
    have hsU : s ∈ fixSyn U := fun b hb => hs b (hUU' hb)
    obtain ⟨m, hmF, hms⟩ := hN.fix s hsU
    refine ⟨m, ?_, hms⟩
    simp only [extF, List.mem_filter, beq_iff_eq]
    exact ⟨hmF, E.fixed c hcN m (hN.fmask m hmF) (by rw [hms]; exact hs _ hecU')⟩
  · intro i hiN hti hi1 hisq hicomm
    have hicomm' : ∀ u ∈ U, E.e i * u = u * E.e i := fun u hu => hicomm u (hUU' hu)
    have hic : i ∈ cand := hN.cand i hiN (by omega) hi1 hisq hicomm'
    refine List.mem_filter.2 ⟨hic, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨by omega, ?_⟩
    obtain ⟨h1N, h1e⟩ := E.mul c hcN hc1 hcsq i hiN
    obtain ⟨h2N, h2e⟩ := E.mul i hiN hi1 hisq c hcN
    apply E.inj _ h1N _ h2N
    rw [h1e, h2e]
    exact (hicomm _ hecU').symm
  · intro i hiN hiB hiU'
    have hiU : E.e i ∉ U := fun h => hiU' (hUU' h)
    have h1 := hmin i hiN hiB hiU
    have h2 : i ≠ c := by
      rintro rfl
      exact hiU' hecU'
    omega

theorem dfs_sound (E : Enum S) : ∀ (n : ℕ) {B U : Subgroup (Perm (Fin 24))} {t : ℕ}
    {V F cand : List ℕ}, U ≤ B → B ≤ S → (∀ b ∈ B, b * b = 1) →
    (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) → Nat.card B ≤ 2 ^ n * Nat.card U →
    Node E U B t V F cand → dfs E.mulIdx E.cols n V F cand = true →
    Nat.card B * Nat.card (fixSyn B) ≤ 2 ^ 11 := by
  intro n
  induction n with
  | zero =>
    intro B U t V F cand hUB hBS hB2 hBc hcard hN hdfs
    have hle : V.length * F.length ≤ 2 ^ 11 := of_decide_eq_true hdfs
    have hUeq : U = B := Subgroup.eq_of_le_of_card_ge hUB (by simpa using hcard)
    subst hUeq
    exact hN.bound hBS hle
  | succ n ih =>
    intro B U t V F cand hUB hBS hB2 hBc hcard hN hdfs
    simp only [dfs, Bool.and_eq_true] at hdfs
    obtain ⟨hle', hch⟩ := hdfs
    have hle : V.length * F.length ≤ 2 ^ 11 := of_decide_eq_true hle'
    by_cases hBU : B ≤ U
    · have hUeq : U = B := le_antisymm hUB hBU
      subst hUeq
      exact hN.bound hBS hle
    · refine children_sound E hUB hBS hB2 hBc hN hBU _ ?_ hch
      intro U' t' V' F' cand' hUU' hU'B hcardU' hN' hd
      refine ih hU'B hBS hB2 hBc ?_ hN' hd
      calc Nat.card B ≤ 2 ^ (n + 1) * Nat.card U := hcard
        _ = 2 ^ n * Nat.card U' := by rw [hcardU']; ring

theorem offenderBound_of_dfs (E : Enum S) (hS : Nat.card S ≤ 2 ^ 10) (invs : List ℕ)
    (hinv : ∀ i < E.N, E.e i ≠ 1 → E.e i * E.e i = 1 → i ∈ invs)
    (h : children E.mulIdx E.cols (dfs E.mulIdx E.cols 9) [0] (List.range 4096) invs =
      true) : OffenderBound S := by
  intro B hBS hB2 hBc hB0
  have hnode : Node E ⊥ B 0 [0] (List.range 4096) invs := by
    refine ⟨⟨List.nodup_singleton 0, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro i
      constructor
      · intro hi
        rw [List.mem_singleton] at hi
        subst hi
        exact ⟨E.pos, by rw [E.zero]; exact Subgroup.one_mem _⟩
      · rintro ⟨hiN, hi⟩
        rw [Subgroup.mem_bot] at hi
        rw [List.mem_singleton]
        exact E.inj i hiN 0 E.pos (by rw [hi, E.zero])
    · intro m hm
      exact List.mem_range.1 hm
    · intro s _
      obtain ⟨m, hm, hms⟩ := synOfMask_surj s
      exact ⟨m, List.mem_range.2 hm, hms⟩
    · intro i hiN _ hi1 hisq _
      exact hinv i hiN hi1 hisq
    · intro i _ _ _
      exact Nat.zero_le _
  refine children_sound E bot_le hBS hB2 hBc hnode (fun hle => hB0 (le_bot_iff.1 hle)) _ ?_ h
  intro U' t' V' F' cand' _ hU'B hcardU' hN' hd
  refine dfs_sound E 9 hU'B hBS hB2 hBc ?_ hN' hd
  rw [Subgroup.card_bot] at hcardU'
  rw [hcardU']
  calc Nat.card B ≤ Nat.card S := Subgroup.card_le_of_le hBS
    _ ≤ 2 ^ 10 := hS
    _ = 2 ^ 9 * (2 * 1) := by norm_num

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

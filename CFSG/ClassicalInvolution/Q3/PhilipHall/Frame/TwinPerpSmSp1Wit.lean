module

public import Certificates.Data.TwinPerpSmSp1Wit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSp1Base
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord wordPerm wordPerm_mem letters_of_all
  mapWord_rep)
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal (IsQ8Pair q8Hom zmod4Pow
  zmod4Pow_zero)
open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (Q16Data qGens qCert)
open Certificates.TwinPerpSmSp1

set_option linter.unusedSectionVars false

@[expose] def IsQ8Witness {G : Type*} [Group G] (Q : Subgroup G) (z c : G) : Prop :=
  (c * z = z * c ∧ (∃ q ∈ Q, c * q * c⁻¹ ∉ Q) ∧
    ∃ a ∈ Q, ∃ b ∈ Q, a * (c * b * c⁻¹) ≠ (c * b * c⁻¹) * a) ∨
  ∃ k ∈ Q, (∃ a ∈ Q, k * a ≠ a * k) ∧ (c * k * c⁻¹) * z = z * (c * k * c⁻¹) ∧
    ∃ q ∈ Q, (c * k * c⁻¹) * q * (c * k * c⁻¹)⁻¹ ∉ Q

@[expose] def q8Perm {G : Type*} [Group G] (ξ η : G) : ℕ → G
  | 0 => 1
  | 1 => ξ
  | 2 => ξ * ξ
  | 3 => ξ * ξ * ξ
  | 4 => η
  | 5 => η * ξ
  | 6 => η * (ξ * ξ)
  | _ => η * (ξ * ξ * ξ)

theorem rep_q8Elt {n : ℕ} {x y : Array ℕ} {ξ η : Equiv.Perm (Fin n)} (hx : Rep n x ξ)
    (hy : Rep n y η) : ∀ j : ℕ, Rep n (q8Elt n x y j) (q8Perm ξ η j)
  | 0 => rep_idA
  | 1 => hx
  | 2 => rep_compA hx hx
  | 3 => rep_compA (rep_compA hx hx) hx
  | 4 => hy
  | 5 => rep_compA hy hx
  | 6 => rep_compA hy (rep_compA hx hx)
  | _ + 7 => rep_compA hy (rep_compA (rep_compA hx hx) hx)

theorem q8Perm_mem {X : Type} [Group X] {ξ η : X} (hq : IsQ8Pair ξ η) :
    ∀ j : ℕ, q8Perm ξ η j ∈ (q8Hom hq).range := by
  have hξ : ξ ∈ (q8Hom hq).range := ⟨QuaternionGroup.a 1, by
    show zmod4Pow ξ 1 = ξ
    unfold zmod4Pow
    rw [show (1 : ZMod 4).val = 1 from rfl, pow_one]⟩
  have hη : η ∈ (q8Hom hq).range := ⟨QuaternionGroup.xa 0, by
    show η * zmod4Pow ξ 0 = η
    rw [zmod4Pow_zero, mul_one]⟩
  intro j
  match j with
  | 0 => exact Subgroup.one_mem _
  | 1 => exact hξ
  | 2 => exact Subgroup.mul_mem _ hξ hξ
  | 3 => exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hξ hξ) hξ
  | 4 => exact hη
  | 5 => exact Subgroup.mul_mem _ hη hξ
  | 6 => exact Subgroup.mul_mem _ hη (Subgroup.mul_mem _ hξ hξ)
  | _ + 7 => exact Subgroup.mul_mem _ hη (Subgroup.mul_mem _ (Subgroup.mul_mem _ hξ hξ) hξ)

theorem exists_q8Perm_eq {X : Type} [Group X] {ξ η : X} (hq : IsQ8Pair ξ η) {g : X}
    (hg : g ∈ (q8Hom hq).range) : ∃ j < 8, q8Perm ξ η j = g := by
  obtain ⟨e, rfl⟩ := hg
  have h3 : ξ * ξ * ξ = ξ ^ 3 := by rw [pow_succ, pow_two]
  cases e with
  | a i =>
    show ∃ j < 8, q8Perm ξ η j = ξ ^ i.val
    have hv : i.val < 4 := ZMod.val_lt i
    generalize i.val = v at hv ⊢
    interval_cases v
    · exact ⟨0, by norm_num, (pow_zero ξ).symm⟩
    · exact ⟨1, by norm_num, (pow_one ξ).symm⟩
    · exact ⟨2, by norm_num, (pow_two ξ).symm⟩
    · exact ⟨3, by norm_num, h3⟩
  | xa i =>
    show ∃ j < 8, q8Perm ξ η j = η * ξ ^ i.val
    have hv : i.val < 4 := ZMod.val_lt i
    generalize i.val = v at hv ⊢
    interval_cases v
    · exact ⟨4, by norm_num, by rw [pow_zero, mul_one]; rfl⟩
    · exact ⟨5, by norm_num, by rw [pow_one]; rfl⟩
    · exact ⟨6, by norm_num, by rw [pow_two]; rfl⟩
    · exact ⟨7, by norm_num, by rw [← h3]; rfl⟩

theorem commA_iff {n : ℕ} {a b : Array ℕ} {α β : Equiv.Perm (Fin n)} (ha : Rep n a α)
    (hb : Rep n b β) : commA n a b = true ↔ α * β = β * α :=
  eqA_iff (rep_compA ha hb) (rep_compA hb ha)

theorem not_mem_of_outsideA {n : ℕ} {x y c a : Array ℕ} {ξ η γ α : Equiv.Perm (Fin n)}
    (hx : Rep n x ξ) (hy : Rep n y η) (hc : Rep n c γ) (ha : Rep n a α) (hq : IsQ8Pair ξ η)
    (h : outsideA n x y c a = true) : γ * α * γ⁻¹ ∉ (q8Hom hq).range := by
  intro hmem
  obtain ⟨j, hj, hjeq⟩ := exists_q8Perm_eq hq hmem
  have h1 := allLt_spec h hj
  simp only [Bool.not_eq_true'] at h1
  have he : γ * α = q8Perm ξ η j * γ := by rw [hjeq]; group
  rw [(eqA_iff (rep_compA hc ha) (rep_compA (rep_q8Elt hx hy j) hc)).2 he] at h1
  exact absurd h1 (by decide)

theorem isQ8Witness_of_wit4 {n : ℕ} {x y c : Array ℕ} {ξ η : Equiv.Perm (Fin n)}
    (hx : Rep n x ξ) (hy : Rep n y η) (hc : validA n c = true) (hq : IsQ8Pair ξ η)
    (h : wit4 n x y c = true) : IsQ8Witness (q8Hom hq).range (ξ ^ 2) (permOfArr n c) := by
  have hγ := rep_of_validA hc
  have hγi := rep_inv_of_validA hc
  have hξQ := q8Perm_mem hq 1
  have hηQ := q8Perm_mem hq 4
  simp only [wit4, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hcz, hout⟩, hnc⟩ := h
  refine Or.inl ⟨?_, ?_, ?_⟩
  · rw [pow_two]
    exact (commA_iff hγ (rep_compA hx hx)).1 hcz
  · rcases hout with hout | hout
    · exact ⟨ξ, hξQ, not_mem_of_outsideA hx hy hγ hx hq hout⟩
    · exact ⟨η, hηQ, not_mem_of_outsideA hx hy hγ hy hq hout⟩
  · have hcx := rep_compA (rep_compA hγ hx) hγi
    have hcy := rep_compA (rep_compA hγ hy) hγi
    have key : ∀ {a b : Array ℕ} {α β : Equiv.Perm (Fin n)}, Rep n a α → Rep n b β →
        commA n a b = false → α * β ≠ β * α := fun ha hb hab he => by
      rw [(commA_iff ha hb).2 he] at hab
      exact absurd hab (by decide)
    rcases hnc with ((h1 | h1) | h1) | h1
    · exact ⟨ξ, hξQ, ξ, hξQ, key hx hcx h1⟩
    · exact ⟨ξ, hξQ, η, hηQ, key hx hcy h1⟩
    · exact ⟨η, hηQ, ξ, hξQ, key hy hcx h1⟩
    · exact ⟨η, hηQ, η, hηQ, key hy hcy h1⟩

theorem isQ8Witness_of_wit5 {n : ℕ} {x y g : Array ℕ} {ξ η : Equiv.Perm (Fin n)}
    (hx : Rep n x ξ) (hy : Rep n y η) (hg : validA n g = true) (hq : IsQ8Pair ξ η)
    (h : wit5 n x y g = true) : IsQ8Witness (q8Hom hq).range (ξ ^ 2) (permOfArr n g) := by
  have hγ := rep_of_validA hg
  have hγi := rep_inv_of_validA hg
  unfold wit5 at h
  rw [List.any_eq_true] at h
  obtain ⟨j, hj, hjt⟩ := h
  have hj8 : j < 8 := List.mem_range.1 hj
  have hk := rep_q8Elt hx hy j
  have hv := rep_compA (rep_compA hγ hk) hγi
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hjt
  obtain ⟨⟨hnc, hvz⟩, hout⟩ := hjt
  refine Or.inr ⟨q8Perm ξ η j, q8Perm_mem hq j, ?_, ?_, ?_⟩
  · rcases hnc with h1 | h1
    · refine ⟨ξ, q8Perm_mem hq 1, fun he => ?_⟩
      rw [(commA_iff hk hx).2 he] at h1
      exact absurd h1 (by decide)
    · refine ⟨η, q8Perm_mem hq 4, fun he => ?_⟩
      rw [(commA_iff hk hy).2 he] at h1
      exact absurd h1 (by decide)
  · rw [pow_two]
    exact (commA_iff hv (rep_compA hx hx)).1 hvz
  · rcases hout with hout | hout
    · exact ⟨ξ, q8Perm_mem hq 1, not_mem_of_outsideA hx hy hv hx hq hout⟩
    · exact ⟨η, q8Perm_mem hq 4, not_mem_of_outsideA hx hy hv hy hq hout⟩

theorem q8Wit_sound (D : Q8WitData) (h : q8WitCheck D = true) {ξ η : Equiv.Perm (Fin D.syl.n)}
    (hξ : ξ ∈ Subgroup.closure (permsA D.syl.n (qGens D.syl)))
    (hη : η ∈ Subgroup.closure (permsA D.syl.n (qGens D.syl))) (hq : IsQ8Pair ξ η) :
    ∃ k < D.cW.size, IsQ8Witness (q8Hom hq).range (ξ ^ 2) (wordPerm D.syl.n D.xg D.cW[k]!) := by
  unfold q8WitCheck q8WitCheck' at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, hkeys, -, hQenum, -, hxg, hcW, hcs, hfree⟩ := h
  have hqk : ∀ p ∈ D.syl.qKeys, p < D.syl.n := fun p hp => by
    simpa using List.all_eq_true.1 hkeys p hp
  have hxgv : ∀ l < D.xg.size, validA D.syl.n D.xg[l]! = true := fun l hl => allLt_spec hxg hl
  have hcWl := letters_of_all hcW
  obtain ⟨i, hi, hxi⟩ := enumOK_exists_rep hqk hQenum hξ
  obtain ⟨j, hj, hyj⟩ := enumOK_exists_rep hqk hQenum hη
  obtain ⟨-, -, hval⟩ := enumOK_spec hqk hQenum
  have hsqi : ((qCert D.syl).pts.map fun y => compA D.syl.n y y)[i]! =
      compA D.syl.n (qCert D.syl).pts[i]! (qCert D.syl).pts[i]! :=
    CFSG.RankThree.PartTwo.Sec4.Item434SporE81.getElem!_map' (qCert D.syl).pts _ hi
  have hsqj : ((qCert D.syl).pts.map fun y => compA D.syl.n y y)[j]! =
      compA D.syl.n (qCert D.syl).pts[j]! (qCert D.syl).pts[j]! :=
    CFSG.RankThree.PartTwo.Sec4.Item434SporE81.getElem!_map' (qCert D.syl).pts _ hj
  have hx2 := rep_compA hxi hxi
  have hy2 := rep_compA hyj hyj
  have hxinv : Rep D.syl.n (invCand D.syl.n (qCert D.syl).pts[i]!) ξ⁻¹ := by
    have := rep_inv_of_validA (hval i hi)
    rwa [permOfArr_eq_of_rep hxi] at this
  obtain ⟨h4, h2, hc, hne⟩ := id hq
  have hci := allLt_spec hfree hi
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hci
  rcases hci with (hc1 | hc2) | hc3
  · rw [hsqi] at hc1
    exact absurd (by rw [pow_two]; exact (eqA_iff hx2 rep_idA).1 hc1) hne
  · have h4' : ξ * ξ * (ξ * ξ) = 1 := by
      rw [← h4]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [hsqi, (eqA_iff (rep_compA hx2 hx2) rep_idA).2 h4'] at hc2
    exact absurd hc2 (by decide)
  · have hcj := allLt_spec hc3 hj
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hcj
    rcases hcj with (hj1 | hj2) | hj3
    · have h2' : η * η = ξ * ξ := by rw [← pow_two, ← pow_two]; exact h2
      rw [hsqi, hsqj, (eqA_iff hy2 hx2).2 h2'] at hj1
      exact absurd hj1 (by decide)
    · have hyx : η * ξ = ξ⁻¹ * η := by
        rw [← hc]
        group
      rw [(eqA_iff (rep_compA hyj hxi) (rep_compA hxinv hyj)).2 hyx] at hj2
      exact absurd hj2 (by decide)
    · rw [Array.any_eq_true] at hj3
      obtain ⟨k, hk, hkt⟩ := hj3
      have hkc : k < D.cW.size := by simpa [cands] using hk
      have hck : (cands D)[k]! = (cands D)[k] := getElem!_pos (cands D) k hk
      have hrep := mapWord_rep hxgv hcWl hkc
      have hcv : validA D.syl.n (cands D)[k]! = true := allLt_spec hcs hk
      have heq : permOfArr D.syl.n (cands D)[k]! = wordPerm D.syl.n D.xg D.cW[k]! :=
        permOfArr_eq_of_rep hrep
      refine ⟨k, hkc, ?_⟩
      rw [← heq]
      rw [← hck, Bool.or_eq_true] at hkt
      rcases hkt with hkt | hkt
      · exact isQ8Witness_of_wit4 hxi hyj hcv hq hkt
      · exact isQ8Witness_of_wit5 hxi hyj hcv hq hkt

theorem pg_valid_of_q8WitCheck (D : Q8WitData) (h : q8WitCheck D = true) :
    ∀ l < D.syl.pg.size, validA D.syl.n D.syl.pg[l]! = true := by
  unfold q8WitCheck q8WitCheck' at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  exact fun l hl => allLt_spec h.1 hl

theorem xg_valid_of_q8WitCheck (D : Q8WitData) (h : q8WitCheck D = true) :
    ∀ l < D.xg.size, validA D.syl.n D.xg[l]! = true := by
  unfold q8WitCheck q8WitCheck' at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  exact fun l hl => allLt_spec h.2.2.2.2.2.1 hl

theorem card_syl_of_q8WitCheck (D : Q8WitData) (h : q8WitCheck D = true) :
    Nat.card ↥(Subgroup.closure (permsA D.syl.n (qGens D.syl))) = D.syl.qOrd := by
  unfold q8WitCheck q8WitCheck' at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, hkeys, -, hQenum, hQcard, -⟩ := h
  have hqk : ∀ p ∈ D.syl.qKeys, p < D.syl.n := fun p hp => by
    simpa using List.all_eq_true.1 hkeys p hp
  exact (enumOK_spec hqk hQenum).2.1.trans hQcard

theorem syl_le_of_q8WitCheck (D : Q8WitData) (h : q8WitCheck D = true)
    (W : Subgroup (Equiv.Perm (Fin D.syl.n)))
    (hW : ∀ l < D.syl.pg.size, permOfArr D.syl.n D.syl.pg[l]! ∈ W) :
    Subgroup.closure (permsA D.syl.n (qGens D.syl)) ≤ W := by
  unfold q8WitCheck q8WitCheck' at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hpg, -, hqW, -⟩ := h
  have hpgv : ∀ l < D.syl.pg.size, validA D.syl.n D.syl.pg[l]! = true :=
    fun l hl => allLt_spec hpg hl
  have hqWl := letters_of_all hqW
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < D.syl.qW.size := by simpa [qGens] using hk
  show permOfArr D.syl.n (D.syl.qW.map (posWord D.syl.n D.syl.pg))[k]! ∈ W
  rw [permOfArr_eq_of_rep (mapWord_rep hpgv hqWl hk')]
  exact wordPerm_mem hW (hqWl k hk')

theorem hwit_of_q8WitCheck {d : ℕ} (D : Q8WitData) (hd : D.syl.n = d) (h : q8WitCheck D = true)
    (P : Subgroup (Equiv.Perm (Fin d))) (hP : ∀ l < D.xg.size, permOfArr d D.xg[l]! ∈ P) :
    ∀ x ∈ Subgroup.closure (permsA d (qGens D.syl)),
      ∀ y ∈ Subgroup.closure (permsA d (qGens D.syl)), ∀ hq : IsQ8Pair x y,
        ∃ c ∈ P, IsQ8Witness (q8Hom hq).range (x ^ 2) c := by
  subst hd
  intro x hx y hy hq
  have hcW : D.cW.all (fun w => w.all fun l => decide (l < D.xg.size)) = true := by
    have h' := h
    unfold q8WitCheck q8WitCheck' at h'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h'
    exact h'.2.2.2.2.2.2.1
  have hcWl := letters_of_all hcW
  obtain ⟨k, hk, hw⟩ := q8Wit_sound D h hx hy hq
  exact ⟨_, wordPerm_mem hP (hcWl k hk), hw⟩

theorem smallAutModel_of_rankTwo {X₀ W : Type*} [Group X₀] [Group W] {X : Subgroup W}
    (hW : CFSG.ComponentClassification.RankTwoSporadic.AutModel X₀ W X) {d : ℕ}
    (ι : W →* Equiv.Perm (Fin d)) (hι : Function.Injective ι) :
    CFSG.Sporadic.SmallOddCore.AutModel (X.map ι) ι.range where
  le := Subgroup.map_le_range ι X
  conj_mem := by
    rintro _ ⟨w, rfl⟩ _ ⟨p, hp, rfl⟩
    haveI := hW.normal
    exact ⟨w * p * w⁻¹, hW.normal.conj_mem p hp w, by simp only [map_mul, map_inv]⟩
  surj α := by
    obtain ⟨e, he⟩ : ∃ e : ↥X ≃* ↥(X.map ι), ∀ r : ↥X,
        ((e r : ↥(X.map ι)) : Equiv.Perm (Fin d)) = ι r :=
      ⟨Subgroup.equivMapOfInjective X ι hι,
        fun r => Subgroup.coe_equivMapOfInjective_apply X ι hι r⟩
    have h3 : ∀ q : ↥(X.map ι), (q : Equiv.Perm (Fin d)) = ι (e.symm q : W) := fun q => by
      rw [← he, MulEquiv.apply_symm_apply]
    obtain ⟨w, hw⟩ := hW.exists_conj ((MulAut.congr e.symm) α)
    refine ⟨ι w, ⟨w, rfl⟩, fun p => ?_⟩
    have h1 := hw (e.symm p)
    have h2 : (((MulAut.congr e.symm) α) (e.symm p) : W) = (e.symm (α p) : W) := by
      simp [MulAut.congr_apply]
    rw [h2] at h1
    rw [h3 (α p), h1, map_mul, map_mul, map_inv, ← h3 p]
  inj := by
    rintro _ ⟨w, rfl⟩ hc
    have hw : w ∈ Subgroup.centralizer (X : Set W) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      apply hι
      rw [map_mul, map_mul]
      exact (hc (ι p) ⟨p, hp, rfl⟩).symm
    rw [hW.centralizer_eq_bot, Subgroup.mem_bot] at hw
    rw [hw, map_one]

theorem exists_conj_le_of_card {G : Type*} [Group G] [Finite G] {R S₀ T : Subgroup G}
    (hS₀R : S₀ ≤ R) (hTR : T ≤ R) (hT : IsPGroup 2 ↥T) {k m : ℕ} (hk : Nat.card S₀ = 2 ^ k)
    (hm : ¬ 2 ∣ m) (hcard : 2 ^ k * m = Nat.card R) :
    ∃ w ∈ R, ∀ x ∈ T, w * x * w⁻¹ ∈ S₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eS := Subgroup.subgroupOfEquivOfLe hS₀R
  let eT := Subgroup.subgroupOfEquivOfLe hTR
  have hS'2 : IsPGroup 2 ↥(S₀.subgroupOf R) := (IsPGroup.of_card hk).of_equiv eS.symm
  have hS'card : Nat.card ↥(S₀.subgroupOf R) = 2 ^ k := by
    rw [Nat.card_congr eS.toEquiv, hk]
  have hidx : (S₀.subgroupOf R).index = m := by
    have h1 := Subgroup.card_mul_index (S₀.subgroupOf R)
    rw [hS'card, ← hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hT'2 : IsPGroup 2 ↥(T.subgroupOf R) := hT.of_equiv eT.symm
  obtain ⟨P, hP⟩ := hT'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥R P (hS'2.toSylow (by rw [hidx]; exact hm))
  refine ⟨(g : G), g.2, fun x hx => ?_⟩
  have hxP : (⟨x, hTR hx⟩ : ↥R) ∈ (P : Subgroup ↥R) := hP hx
  have hmem : (g * ⟨x, hTR hx⟩ * g⁻¹ : ↥R) ∈ ((g • P : Sylow 2 ↥R) : Subgroup ↥R) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hxP, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  rw [hg, IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

theorem exists_q8Pair_core {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R)) :
    ∃ p q : Y, ∃ hpq : IsQ8Pair p q, (q8Hom hpq).range = tightCore R := by
  obtain ⟨r', hr', ⟨e'⟩⟩ := h.core.datum.quat
  set S' : Subgroup Y := (S : Subgroup R).map R.subtype with hS'
  have hQ : CFSG.ComponentClassification.AschbacherTheorem3.IsQuaternionTwoGroup S' :=
    ⟨r', hr', ⟨(Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
      R.subtype_injective).symm.trans e'⟩⟩
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal.exists_q8Pair hQ
  have hS'K : S' ≤ tightCore R := h.core.datum.sylow_core.1
  refine ⟨p, q, hpq, ?_⟩
  have hle : (q8Hom hpq).range ≤ tightCore R := by
    rintro _ ⟨e, rfl⟩
    exact hS'K (CFSG.ClassicalInvolution.Q3.TA3.q8Hom_mem hpq hp hq e)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_core_eq_eight h hK2, MonoidHom.range_eq_map, Subgroup.card_map_of_injective
    (CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal.q8Hom_injective hpq),
    Subgroup.card_top, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem q8Hom_range_map {X Z : Type} [Group X] [Group Z] {p q : X} (hpq : IsQ8Pair p q)
    (f : X →* Z) (hf : Function.Injective f) :
    (q8Hom (hpq.map f hf)).range = (q8Hom hpq).range.map f := by
  have e : q8Hom (hpq.map f hf) = f.comp (q8Hom hpq) := by
    ext x
    cases x with
    | a i =>
      show zmod4Pow (f p) i = f (zmod4Pow p i)
      unfold zmod4Pow
      rw [map_pow]
    | xa i =>
      show f q * zmod4Pow (f p) i = f (q * zmod4Pow p i)
      unfold zmod4Pow
      rw [map_mul, map_pow]
  rw [e, MonoidHom.range_comp]

theorem noTwinS_of_q8Wit {n d : ℕ} {P R : Subgroup (Equiv.Perm (Fin d))}
    (hM : CFSG.Sporadic.SmallOddCore.AutModel P R) (S₀ : Subgroup (Equiv.Perm (Fin d)))
    (hS₀R : S₀ ≤ R) {k m : ℕ} (hk : Nat.card S₀ = 2 ^ k) (hm : ¬ 2 ∣ m)
    (hcard : 2 ^ k * m = Nat.card R)
    (hwit : ∀ x ∈ S₀, ∀ y ∈ S₀, ∀ hq : IsQ8Pair x y,
      ∃ c ∈ P, IsQ8Witness (q8Hom hq).range (x ^ 2) c)
    {Pr : ∀ (F : Type) [Group F], Prop}
    (hPr : ∀ (Y : Type) [Group Y] [Finite Y] (R' : Subgroup Y) (S : Sylow 2 R') (t : Y),
      PerpHypS n Y R' S t → Pr ↥(genFittingFStar Y) →
        Nonempty (↥(genFittingFStar Y) ≃* ↥P) ∧ IsPGroup 2 ↥(tightCore R')) :
    NoTwinS n Pr := by
  intro Y _ _ R' S t h _ hF
  obtain ⟨⟨θ⟩, hK2⟩ := hPr Y R' S t h hF
  haveI := h.core.simple
  haveI : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  have hιinj : Function.Injective (hM.embed (genFittingFStar Y) θ) :=
    hM.embed_injective (genFittingFStar Y) θ hC
  obtain ⟨p, q, hpq, hKeq⟩ := exists_q8Pair_core h hK2
  have hpK : p ∈ tightCore R' := by
    rw [← hKeq]
    exact q8Perm_mem hpq 1
  have hqK : q ∈ tightCore R' := by
    rw [← hKeq]
    exact q8Perm_mem hpq 4
  have hKR : (tightCore R').map (hM.embed (genFittingFStar Y) θ) ≤ R := by
    rintro _ ⟨y, -, rfl⟩
    exact hM.embed_mem (genFittingFStar Y) θ y
  obtain ⟨w, hwR, hw⟩ := exists_conj_le_of_card hS₀R hKR
    (hK2.map (hM.embed (genFittingFStar Y) θ)) hk hm hcard
  obtain ⟨φ, hφinj, hφapp⟩ : ∃ φ : Y →* Equiv.Perm (Fin d), Function.Injective φ ∧
      ∀ y, φ y = w * hM.embed (genFittingFStar Y) θ y * w⁻¹ :=
    ⟨(MulAut.conj w).toMonoidHom.comp (hM.embed (genFittingFStar Y) θ),
      (MulAut.conj w).injective.comp hιinj, fun y => rfl⟩
  have hφS : ∀ y ∈ tightCore R', φ y ∈ S₀ := fun y hy => by
    rw [hφapp]
    exact hw _ ⟨y, hy, rfl⟩
  obtain ⟨c, hcP, hc⟩ := hwit (φ p) (hφS p hpK) (φ q) (hφS q hqK) (hpq.map φ hφinj)
  rw [q8Hom_range_map hpq φ hφinj, hKeq] at hc
  obtain ⟨m, hm⟩ : ∃ m : Y, φ m = c := by
    have hc' : w⁻¹ * c * w⁻¹⁻¹ ∈ P := hM.conj_mem _ (R.inv_mem hwR) c hcP
    refine ⟨(θ.symm ⟨_, hc'⟩ : Y), ?_⟩
    rw [hφapp, hM.embed_coe (genFittingFStar Y) θ, MulEquiv.apply_symm_apply]
    show w * (w⁻¹ * c * w⁻¹⁻¹) * w⁻¹ = c
    group
  have hpt : p ^ 2 = t := by
    have hz := uniqueInv_core h
    have h1 : p ^ 2 * p ^ 2 = 1 := by rw [← pow_add]; exact hpq.1
    rcases hz.unique (p ^ 2) ((tightCore R').pow_mem hpK 2) h1 with h2 | h2
    · exact absurd h2 hpq.2.2.2
    · exact h2
  rw [← map_pow, hpt, ← hm] at hc
  unfold IsQ8Witness at hc
  rcases hc with ⟨hzc, ⟨q₀, hq₀, hq₀'⟩, a, ha, b, hb, hab⟩ |
      ⟨k₀, hk₀, ⟨a, ha, hka⟩, hvz, q₀, hq₀, hq₀'⟩
  ·
    have hmt : m ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hφinj
      rw [map_mul, map_mul]
      exact hzc
    obtain ⟨κ, hκ, rfl⟩ := hq₀
    obtain ⟨α, hα, rfl⟩ := ha
    obtain ⟨β, hβ, rfl⟩ := hb
    have hne : conjSub m (tightCore R') ≠ tightCore R' := by
      intro heq
      apply hq₀'
      have h1 : m * κ * m⁻¹ ∈ tightCore R' := by
        rw [← heq]
        exact conj_mem_conjSub hκ
      refine ⟨_, h1, ?_⟩
      simp only [map_mul, map_inv]
    refine false_of_omega4_comm h hK2 hmt hne hα (conj_mem_conjSub hβ) (fun he => hab ?_)
    have := congrArg φ he
    simpa only [map_mul, map_inv] using this
  ·
    obtain ⟨κ, hκ, rfl⟩ := hk₀
    obtain ⟨α, hα, rfl⟩ := ha
    obtain ⟨ρ, hρ, rfl⟩ := hq₀
    have hk2 : IsPGroup 2 ↥(Subgroup.zpowers κ) :=
      hK2.to_le (Subgroup.zpowers_le.2 hκ)
    refine false_of_omega5 (g := m) h hκ hk2 ⟨α, hα, fun he => hka ?_⟩ ?_ ?_
    · have := congrArg φ he
      simpa only [map_mul] using this
    · apply hφinj
      simpa only [map_mul, map_inv] using hvz
    · intro hN
      apply hq₀'
      have h1 : (m * κ * m⁻¹) * ρ * (m * κ * m⁻¹)⁻¹ ∈ tightCore R' := by
        rw [Subgroup.mem_normalizer_iff] at hN
        exact (hN ρ).1 hρ
      refine ⟨_, h1, ?_⟩
      simp only [map_mul, map_inv]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1

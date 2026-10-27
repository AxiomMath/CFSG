module

public import CFSG.GF2Type.SmithTypeE.E7.TrCode
public import CFSG.GF2Type.SmithTypeE.DMod.TD6
public import Certificates.Certificate38790

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod CFSG.RankThree.OrthogonalInvolutions Module

theorem tr7ChkClass_holds : tr7ChkClass = true :=
  Certificates.certificate38790

theorem tr7Chk12_of_lt {j : ℕ} (hj : j < 7) :
    tr7Chk12 j = true := by
  have h := tr7ChkClass_holds
  unfold tr7ChkClass at h
  simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.1 h.1 j (List.mem_range.2 hj)

theorem tr7ChkInt_holds : tr7ChkInt = true := by
  have h := tr7ChkClass_holds
  unfold tr7ChkClass at h
  simp only [Bool.and_eq_true] at h
  exact h.2

@[expose] noncomputable def repV12 (j : ℕ) : V12 ≃ₗ[ZMod 2] V12 :=
  ((tr7RepLines j).map fun p => siegelEquiv (dec12 p.1) (dec12 p.2)).prod

theorem repV12_dec12_aux :
    ∀ (L : List (ℕ × ℕ)), (∀ p ∈ L, TsPair (dec12 p.1) (dec12 p.2) ∧ qf p.1 = false ∧
        qf p.2 = false ∧ bf p.1 p.2 = false) →
      ∀ x : ℕ, ((L.map fun p => siegelEquiv (dec12 p.1) (dec12 p.2)).prod) (dec12 x) =
        dec12 (L.foldr (fun p acc => sgl p.1 p.2 acc) x)
  | [], _, x => by simp
  | p :: L, h, x => by
    obtain ⟨-, hq1, hq2, hb⟩ := h p (List.mem_cons_self ..)
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, LinearEquiv.mul_apply]
    rw [repV12_dec12_aux L (fun q hq => h q (List.mem_cons_of_mem _ hq)) x]
    exact siegelEquiv_dec12 hq1 hq2 hb _

section Rep

variable {j : ℕ} (hj : j < 7)

include hj in
theorem rep_lines_ok : ∀ p ∈ tr7RepLines j, 0 < p.1 ∧ p.1 < 4096 ∧ 0 < p.2 ∧ p.2 < 4096 ∧
    p.1 ≠ p.2 ∧ qf p.1 = false ∧ qf p.2 = false ∧ bf p.1 p.2 = false := by
  have h := tr7Chk12_of_lt hj
  unfold tr7Chk12 at h
  simp only [Bool.and_eq_true] at h
  intro p hp
  have h1 := List.all_eq_true.1 h.1.1.1.1.1.1 p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, hn⟩, he⟩, hf⟩, hg⟩ := h1
  exact ⟨ha, hb, hc, hd, hn, he, hf, hg⟩

include hj in
theorem repV12_dec12 (x : ℕ) : repV12 j (dec12 x) = dec12 (tr7Rep12 j x) := by
  have hok := rep_lines_ok hj
  unfold repV12 tr7Rep12
  exact repV12_dec12_aux _ (fun p hp => by
    obtain ⟨h0, h1, h2, h3, hn, hq1, hq2, hb⟩ := hok p hp
    exact ⟨tsPair_dec12 hq1 hq2 hb, hq1, hq2, hb⟩) x

theorem sub_eq_add_V12 (a b : V12) : a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (add_self_V12 b)]

include hj in
theorem dec12_rep_mem (x : ℕ) : dec12 (tr7Rep12 j x ^^^ x) ∈ commSpace (repV12 j) := by
  rw [dec12_xor, ← repV12_dec12 hj, ← sub_eq_add_V12]
  exact sub_mem_commSpace _ _

theorem chk12_parts (hj : j < 7) :
    (tr7Bs12 j).length = tr7Dim12 j ∧ (tr7Bs12 j).all (· < 4096) = true ∧
    tr7IndepOK (tr7Bs12 j) = true ∧
    (∀ x < 4096, tr7Red (tr7Ech (tr7Cols12 j)) (tr7Rep12 j x ^^^ x) = 0) ∧
    (∀ x < 4096, tr7Rep12 j (tr7Rep12 j x) = x) ∧
    (if j < 4 then (List.range (2 ^ (tr7Bs12 j).length)).all (fun m => !qf (tr7XorSel (tr7Bs12 j) m))
      else (tr7Bs12 j).any qf) = true := by
  have h := tr7Chk12_of_lt hj
  unfold tr7Chk12 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hlen⟩, hlt⟩, hind⟩, hred⟩, hinv⟩, hlet⟩ := h
  refine ⟨hlen, hlt, hind, fun x hx => ?_, fun x hx => ?_, hlet⟩
  · have := List.all_eq_true.1 hred x (List.mem_range.2 hx)
    simpa using this
  · have := List.all_eq_true.1 hinv x (List.mem_range.2 hx)
    simpa using this

include hj in
theorem bs12_mem : ∀ b ∈ tr7Bs12 j, dec12 b ∈ commSpace (repV12 j) := by
  intro b hb
  unfold tr7Bs12 tr7Bs at hb
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
  exact dec_ech_mem dec12_xor (U := commSpace (repV12 j)) (tr7Cols12 j) (fun v hv => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
    exact dec12_rep_mem hj _) e he

include hj in
theorem commSpace_le_span12 :
    commSpace (repV12 j) ≤ Submodule.span (ZMod 2) {u | ∃ b ∈ tr7Bs12 j, u = dec12 b} := by
  obtain ⟨-, -, -, hred, -, -⟩ := chk12_parts hj
  rintro _ ⟨v, rfl⟩
  obtain ⟨x, hx, rfl⟩ := dec12_surj v
  have e : ((repV12 j : V12 →ₗ[ZMod 2] V12) - 1) (dec12 x) = dec12 (tr7Rep12 j x ^^^ x) := by
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, repV12_dec12 hj, dec12_xor, sub_eq_add_V12]
    rfl
  rw [e]
  refine dec_red_mem dec12_xor (tr7Ech (tr7Cols12 j)) _ (fun e he => ?_) ?_
  · exact Submodule.subset_span ⟨e.2, List.mem_map.2 ⟨e, he, rfl⟩, rfl⟩
  · rw [hred x hx, dec12_zero]
    exact Submodule.zero_mem _

include hj in
theorem finrank_commSpace_repV12 : finrank (ZMod 2) (commSpace (repV12 j)) = tr7Dim12 j := by
  obtain ⟨hlen, hlt, hind, -, -, -⟩ := chk12_parts hj
  apply le_antisymm
  · calc finrank (ZMod 2) (commSpace (repV12 j))
        ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) {u | ∃ b ∈ tr7Bs12 j, u = dec12 b}) :=
          Submodule.finrank_mono (commSpace_le_span12 hj)
      _ ≤ (tr7Bs12 j).length := finrank_span_le _
      _ = tr7Dim12 j := hlen
  · calc tr7Dim12 j = (tr7Bs12 j).length := hlen.symm
      _ ≤ finrank (ZMod 2) (commSpace (repV12 j)) :=
          le_finrank_of_indep dec12_xor dec12_inj (fun b hb => by
            have := List.all_eq_true.1 hlt b hb
            simpa using this) (bs12_mem hj) hind

include hj in
theorem repV12_mul_self : repV12 j * repV12 j = 1 := by
  obtain ⟨-, -, -, -, hinv, -⟩ := chk12_parts hj
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨x, hx, rfl⟩ := dec12_surj v
  rw [LinearEquiv.mul_apply, repV12_dec12 hj, repV12_dec12 hj, hinv x hx]
  rfl

include hj in
theorem repV12_mem_omega : repV12 j ∈ omegaGroup Q12 Q12_polarBilin_nondegenerate := by
  rw [← omegaPlus_eq_omegaGroup]
  have hok := rep_lines_ok hj
  unfold repV12
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
  obtain ⟨h0, h1, h2, h3, hn, hq1, hq2, hb⟩ := hok p hp
  exact siegelEquiv_mem_omega (tsPair_dec12 hq1 hq2 hb)
    (dec12_ne_zero h1 (by omega))

include hj in
theorem repV12_ne_one (hl : 1 ≤ tr7Dim12 j) : repV12 j ≠ 1 := by
  intro h
  have := finrank_commSpace_repV12 hj
  rw [h] at this
  have h0 : commSpace (1 : V12 ≃ₗ[ZMod 2] V12) = ⊥ := by
    ext v
    simp only [Submodule.mem_bot, mem_commSpace]
    constructor
    · rintro ⟨w, rfl⟩
      simp
    · rintro rfl
      exact ⟨0, by simp⟩
  rw [h0, finrank_bot] at this
  omega

include hj in
theorem orderOf_repV12 (hl : 1 ≤ tr7Dim12 j) : orderOf (repV12 j) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ (repV12_ne_one hj hl)
  rw [pow_two]
  exact repV12_mul_self hj

include hj in
theorem suzukiLetter_repV12_a (hj4 : j < 4) : suzukiLetter Q12 (repV12 j) = .a := by
  obtain ⟨-, -, -, -, -, hlet⟩ := chk12_parts hj
  rw [if_pos hj4] at hlet
  rw [suzukiLetter_eq_a_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [finrank_commSpace_repV12 hj]
    interval_cases j <;> decide
  · obtain ⟨m, hm, rfl⟩ := exists_xorSel_of_mem_span dec12_xor (tr7Bs12 j)
      (commSpace_le_span12 hj hx)
    have h1 := List.all_eq_true.1 hlet m (List.mem_range.2 hm)
    rw [Q12_apply, q12_dec12]
    simp only [Bool.not_eq_true'] at h1
    simp [h1, bit]

include hj in
theorem suzukiLetter_repV12_c (hj4 : 4 ≤ j) : suzukiLetter Q12 (repV12 j) = .c := by
  obtain ⟨-, -, -, -, -, hlet⟩ := chk12_parts hj
  rw [if_neg (by omega)] at hlet
  rw [suzukiLetter_eq_c_iff]
  refine ⟨?_, ?_⟩
  · rw [finrank_commSpace_repV12 hj]
    interval_cases j <;> decide
  · obtain ⟨b, hb, hqb⟩ := List.any_eq_true.1 hlet
    refine ⟨dec12 b, bs12_mem hj b hb, ?_⟩
    rw [Q12_apply, q12_dec12, hqb]
    simp [bit]

theorem chkInt_parts :
    tr7BsInt.length = 7 ∧ tr7BsInt.all (· < 4096) = true ∧ tr7IndepOK tr7BsInt = true ∧
    (∀ v ∈ tr7Bs12 2 ++ tr7Bs12 3, tr7Red (tr7Ech (tr7Bs12 2 ++ tr7Bs12 3)) v = 0) := by
  have h := tr7ChkInt_holds
  unfold tr7ChkInt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen, hlt⟩, hind⟩, hred⟩ := h
  refine ⟨hlen, hlt, hind, fun v hv => ?_⟩
  have := List.all_eq_true.1 hred v hv
  simpa using this

theorem finrank_sup_commSpace :
    finrank (ZMod 2) ↥(commSpace (repV12 2) ⊔ commSpace (repV12 3)) = 7 := by
  obtain ⟨hlen, hlt, hind, hred⟩ := chkInt_parts
  have h2 : (2 : ℕ) < 7 := by norm_num
  have h3 : (3 : ℕ) < 7 := by norm_num
  apply le_antisymm
  · have hle : commSpace (repV12 2) ⊔ commSpace (repV12 3) ≤
        Submodule.span (ZMod 2) {u | ∃ b ∈ tr7BsInt, u = dec12 b} := by
      have hsub : ∀ v ∈ tr7Bs12 2 ++ tr7Bs12 3,
          dec12 v ∈ Submodule.span (ZMod 2) {u | ∃ b ∈ tr7BsInt, u = dec12 b} := by
        intro v hv
        refine dec_red_mem dec12_xor (tr7Ech (tr7Bs12 2 ++ tr7Bs12 3)) v (fun e he => ?_) ?_
        · exact Submodule.subset_span ⟨e.2, List.mem_map.2 ⟨e, he, rfl⟩, rfl⟩
        · rw [hred v hv, dec12_zero]
          exact Submodule.zero_mem _
      refine sup_le ?_ ?_
      · refine (commSpace_le_span12 h2).trans (Submodule.span_le.2 ?_)
        rintro _ ⟨b, hb, rfl⟩
        exact hsub b (List.mem_append_left _ hb)
      · refine (commSpace_le_span12 h3).trans (Submodule.span_le.2 ?_)
        rintro _ ⟨b, hb, rfl⟩
        exact hsub b (List.mem_append_right _ hb)
    calc finrank (ZMod 2) ↥(commSpace (repV12 2) ⊔ commSpace (repV12 3))
        ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) {u | ∃ b ∈ tr7BsInt, u = dec12 b}) :=
          Submodule.finrank_mono hle
      _ ≤ tr7BsInt.length := finrank_span_le _
      _ = 7 := hlen
  · calc 7 = tr7BsInt.length := hlen.symm
      _ ≤ _ := le_finrank_of_indep dec12_xor dec12_inj (fun b hb => by
            have := List.all_eq_true.1 hlt b hb
            simpa using this) (fun b hb => by
            unfold tr7BsInt tr7Bs at hb
            obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
            refine dec_ech_mem dec12_xor (U := commSpace (repV12 2) ⊔ commSpace (repV12 3))
              (tr7Bs12 2 ++ tr7Bs12 3) (fun v hv => ?_) e he
            rcases List.mem_append.1 hv with hv | hv
            · exact Submodule.mem_sup_left (bs12_mem h2 v hv)
            · exact Submodule.mem_sup_right (bs12_mem h3 v hv)) hind

theorem finrank_inf_commSpace_odd :
    Odd (finrank (ZMod 2) ↥(commSpace (repV12 3) ⊓ commSpace (repV12 2))) := by
  have h2 : (2 : ℕ) < 7 := by norm_num
  have h3 : (3 : ℕ) < 7 := by norm_num
  have e := Submodule.finrank_sup_add_finrank_inf_eq (commSpace (repV12 2)) (commSpace (repV12 3))
  rw [finrank_sup_commSpace, finrank_commSpace_repV12 h2, finrank_commSpace_repV12 h3] at e
  rw [inf_comm]
  have : finrank (ZMod 2) ↥(commSpace (repV12 2) ⊓ commSpace (repV12 3)) = 5 := by
    simp only [tr7Dim12] at e
    norm_num at e
    omega
  rw [this]
  decide

open TauCeti.QuadraticMap in
theorem conj_of_type {t : V12 ≃ₗ[ZMod 2] V12}
    (htΩ : t ∈ omegaGroup Q12 Q12_polarBilin_nondegenerate) (htt : t * t = 1) (ht1 : t ≠ 1)
    (hj : j < 7) (hl : 1 ≤ tr7Dim12 j)
    (hlet : suzukiLetter Q12 (repV12 j) = suzukiLetter Q12 t)
    (hfr : finrank (ZMod 2) (commSpace (repV12 j)) = finrank (ZMod 2) (commSpace t))
    (hnot : ¬ (suzukiLetter Q12 t = .a ∧ finrank (ZMod 2) (commSpace t) = 6)) :
    ∃ g ∈ omegaGroup Q12 Q12_polarBilin_nondegenerate, g * t * g⁻¹ = repV12 j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hrO : repV12 j ∈ orthogonalGroup Q12 := (repV12_mem_omega hj).1
  have hr2 := orderOf_repV12 hj hl
  obtain ⟨g, hg, hgt⟩ := (isConj_iff_suzukiLetter_eq Q12_polarBilin_nondegenerate htΩ.1 ht2 hrO
    hr2).mpr ⟨hlet, hfr⟩
  have hset := omega_conj_eq_of_not_typeA_half Q12_polarBilin_nondegenerate (m := 6)
    (by rw [finrank_V12]) htΩ ht2 hnot
  have hmem : repV12 j ∈ {x | ∃ g ∈ orthogonalGroup Q12, g * t * g⁻¹ = x} := ⟨g, hg, hgt⟩
  rw [← hset] at hmem
  exact hmem

open TauCeti.QuadraticMap in
theorem conj_of_type_a6 {t : V12 ≃ₗ[ZMod 2] V12}
    (htΩ : t ∈ omegaGroup Q12 Q12_polarBilin_nondegenerate) (htt : t * t = 1) (ht1 : t ≠ 1)
    (hta : suzukiLetter Q12 t = .a) (ht6 : finrank (ZMod 2) (commSpace t) = 6) :
    ∃ j, (j = 2 ∨ j = 3) ∧ ∃ g ∈ omegaGroup Q12 Q12_polarBilin_nondegenerate,
      g * t * g⁻¹ = repV12 j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := Q12_polarBilin_nondegenerate
  have h2 : (2 : ℕ) < 7 := by norm_num
  have h3 : (3 : ℕ) < 7 := by norm_num
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hr2O : repV12 2 ∈ orthogonalGroup Q12 := (repV12_mem_omega h2).1
  have hr3O : repV12 3 ∈ orthogonalGroup Q12 := (repV12_mem_omega h3).1
  have hr2o := orderOf_repV12 h2 (by decide)
  have hr3o := orderOf_repV12 h3 (by decide)
  have hr2a := suzukiLetter_repV12_a h2 (by norm_num)
  have hr3a := suzukiLetter_repV12_a h3 (by norm_num)
  have hf2 : finrank (ZMod 2) (commSpace (repV12 2)) = 6 := by
    rw [finrank_commSpace_repV12 h2]; rfl
  have hf3 : finrank (ZMod 2) (commSpace (repV12 3)) = 6 := by
    rw [finrank_commSpace_repV12 h3]; rfl
  have hn : finrank (ZMod 2) V12 = 2 * 6 := by rw [finrank_V12]
  obtain ⟨g₁, hg₁, hg₁t⟩ := (isConj_iff_suzukiLetter_eq hQ hr2O hr2o htΩ.1
    (orderOf_eq_prime (by rw [pow_two]; exact htt) ht1)).mpr
    ⟨hta.trans hr2a.symm, ht6.trans hf2.symm⟩
  by_cases hg₁Ω : g₁ ∈ omegaGroup Q12 hQ
  · refine ⟨2, Or.inl rfl, g₁⁻¹, inv_mem hg₁Ω, ?_⟩
    rw [← hg₁t]
    group
  · obtain ⟨g₂, hg₂, hg₂r⟩ := (isConj_iff_suzukiLetter_eq hQ hr2O hr2o hr3O hr3o).mpr
      ⟨hr3a.trans hr2a.symm, hf3.trans hf2.symm⟩
    have hg₂Ω : g₂ ∉ omegaGroup Q12 hQ := by
      intro h
      have := (mem_omegaGroup_iff_even_finrank_inf hQ hn hr2a hf2 hg₂).1 h
      rw [hg₂r] at this
      exact (Nat.not_even_iff_odd.2 finrank_inf_commSpace_odd) this
    have hodd1 : (finrank (ZMod 2) (commSpace g₁) : ZMod 2) = 1 := by
      have : ¬ Even (finrank (ZMod 2) (commSpace g₁)) := fun he => hg₁Ω ⟨hg₁, he⟩
      exact (ZMod.natCast_eq_one_iff_odd).mpr (Nat.not_even_iff_odd.mp this)
    have hodd2 : (finrank (ZMod 2) (commSpace g₂) : ZMod 2) = 1 := by
      have : ¬ Even (finrank (ZMod 2) (commSpace g₂)) := fun he => hg₂Ω ⟨hg₂, he⟩
      exact (ZMod.natCast_eq_one_iff_odd).mpr (Nat.not_even_iff_odd.mp this)
    have hhΩ : g₁ * g₂⁻¹ ∈ omegaGroup Q12 hQ := by
      refine ⟨mul_mem hg₁ (inv_mem hg₂), ?_⟩
      rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hQ hg₁ (inv_mem hg₂),
        natCast_finrank_commSpace_inv hQ hg₂, hodd1, hodd2]
      rfl
    refine ⟨3, Or.inr rfl, (g₁ * g₂⁻¹)⁻¹, inv_mem hhΩ, ?_⟩
    rw [← hg₁t, ← hg₂r]
    group

open TauCeti.QuadraticMap in
theorem exists_conj_repV12 {t : V12 ≃ₗ[ZMod 2] V12}
    (htΩ : t ∈ omegaGroup Q12 Q12_polarBilin_nondegenerate) (htt : t * t = 1) (ht1 : t ≠ 1) :
    ∃ j, j < 7 ∧ ∃ g ∈ omegaGroup Q12 Q12_polarBilin_nondegenerate, g * t * g⁻¹ = repV12 j := by
  have hl_even := htΩ.2
  have hl1 := one_le_finrank_commSpace ht1
  have hl6 : 2 * finrank (ZMod 2) (commSpace t) ≤ 12 :=
    (two_mul_finrank_commSpace_le htt).trans (by rw [finrank_V12])
  have hl : finrank (ZMod 2) (commSpace t) = 2 ∨ finrank (ZMod 2) (commSpace t) = 4 ∨
      finrank (ZMod 2) (commSpace t) = 6 := by
    obtain ⟨k, hk⟩ := hl_even
    omega
  by_cases hq : ∀ x ∈ commSpace t, Q12 x = 0
  · have hta : suzukiLetter Q12 t = .a := suzukiLetter_eq_a_iff.mpr ⟨hl_even, hq⟩
    rcases hl with h | h | h
    · refine ⟨0, by norm_num, conj_of_type htΩ htt ht1 (by norm_num) (by decide)
        ((suzukiLetter_repV12_a (by norm_num) (by norm_num)).trans hta.symm)
        ((finrank_commSpace_repV12 (by norm_num)).trans (by rw [h]; rfl))
        (fun hc => by omega)⟩
    · refine ⟨1, by norm_num, conj_of_type htΩ htt ht1 (by norm_num) (by decide)
        ((suzukiLetter_repV12_a (by norm_num) (by norm_num)).trans hta.symm)
        ((finrank_commSpace_repV12 (by norm_num)).trans (by rw [h]; rfl))
        (fun hc => by omega)⟩
    · obtain ⟨j, hj, hg⟩ := conj_of_type_a6 htΩ htt ht1 hta h
      refine ⟨j, by rcases hj with rfl | rfl <;> norm_num, hg⟩
  · have htc : suzukiLetter Q12 t = .c := suzukiLetter_eq_c_iff.mpr ⟨hl_even, by
      push Not at hq
      exact hq⟩
    have hnot : ¬ (suzukiLetter Q12 t = .a ∧ finrank (ZMod 2) (commSpace t) = 6) := by
      rintro ⟨h, -⟩
      rw [htc] at h
      exact absurd h (by decide)
    rcases hl with h | h | h
    · refine ⟨4, by norm_num, conj_of_type htΩ htt ht1 (by norm_num) (by decide)
        ((suzukiLetter_repV12_c (by norm_num) (by norm_num)).trans htc.symm)
        ((finrank_commSpace_repV12 (by norm_num)).trans (by rw [h]; rfl)) hnot⟩
    · refine ⟨5, by norm_num, conj_of_type htΩ htt ht1 (by norm_num) (by decide)
        ((suzukiLetter_repV12_c (by norm_num) (by norm_num)).trans htc.symm)
        ((finrank_commSpace_repV12 (by norm_num)).trans (by rw [h]; rfl)) hnot⟩
    · refine ⟨6, by norm_num, conj_of_type htΩ htt ht1 (by norm_num) (by decide)
        ((suzukiLetter_repV12_c (by norm_num) (by norm_num)).trans htc.symm)
        ((finrank_commSpace_repV12 (by norm_num)).trans (by rw [h]; rfl)) hnot⟩

end Rep

section Transport


theorem exists_conj_rep (a : TD6) (ha : a * a = 1) (ha1 : a ≠ 1) :
    ∃ j, j < 7 ∧ ∃ hm : repV12 j ∈ CFSG.Open.timmesfeldOmegaPlus 6, ∃ g : TD6,
      g * a * g⁻¹ = omegaTD6 ⟨repV12 j, hm⟩ := by
  obtain ⟨t, rfl⟩ := omegaTD6.surjective a
  have htΩ : (t : V12 ≃ₗ[ZMod 2] V12) ∈ omegaGroup Q12 Q12_polarBilin_nondegenerate := by
    rw [← omegaPlus_eq_omegaGroup]
    exact t.2
  have htt : (t : V12 ≃ₗ[ZMod 2] V12) * t = 1 := by
    have h : omegaTD6 (t * t) = 1 := by rw [map_mul]; exact ha
    have h2 : t * t = 1 := omegaTD6.injective (h.trans (map_one omegaTD6).symm)
    exact congrArg Subtype.val h2
  have ht1 : (t : V12 ≃ₗ[ZMod 2] V12) ≠ 1 := by
    intro h
    apply ha1
    have : t = 1 := Subtype.ext h
    rw [this, map_one]
  obtain ⟨j, hj, g, hgΩ, hg⟩ := exists_conj_repV12 htΩ htt ht1
  have hm : repV12 j ∈ CFSG.Open.timmesfeldOmegaPlus 6 := by
    rw [omegaPlus_eq_omegaGroup]
    exact repV12_mem_omega hj
  have hgm : g ∈ CFSG.Open.timmesfeldOmegaPlus 6 := by
    rw [omegaPlus_eq_omegaGroup]
    exact hgΩ
  refine ⟨j, hj, hm, omegaTD6 ⟨g, hgm⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hg

end Transport

end CFSG.GF2Type.SmithTypeE.E7

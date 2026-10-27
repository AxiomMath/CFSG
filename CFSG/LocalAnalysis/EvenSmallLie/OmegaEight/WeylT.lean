module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCoords
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylTCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAut

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer

theorem tPlusGensArr_size : tPlusGensArr.size = 13 := by simp [tPlusGensArr, pPlusGens]

theorem isId_iff {x : Array ℕ} {X : Equiv.Perm (Fin 240)} (hx : Rep 240 x X) :
    isId x = true ↔ X = 1 := eqA_iff hx rep_idA

theorem rep_tElt {i : ℕ} (hi : i < 8192) :
    Rep 240 (tElt tPlusCert i false) (permOfArr 240 (tElt tPlusCert i false)) :=
  (rep_permOfArr (t_facts.valid i hi)).1

theorem rep_tPlusGen {k : ℕ} (hk : k < 13) :
    Rep 240 tPlusGensArr[k]! (permOfArr 240 tPlusGensArr[k]!) :=
  (rep_permOfArr (t_facts.gens k hk).1).1

theorem tPlusGen_mul_self {k : ℕ} (hk : k < 13) :
    permOfArr 240 tPlusGensArr[k]! * permOfArr 240 tPlusGensArr[k]! = 1 :=
  (isId_iff (rep_compA (rep_tPlusGen hk) (rep_tPlusGen hk))).1 (t_facts.gens k hk).2

theorem tPlusGen_mem_permsA {k : ℕ} (hk : k < 13) :
    permOfArr 240 tPlusGensArr[k]! ∈ permsA 240 tPlusGensArr :=
  ⟨k, show k < tPlusGensArr.size by rw [tPlusGensArr_size]; exact hk, rfl⟩

theorem mem_closure_of_tElt : ∀ i < 8192, ∀ {X : Equiv.Perm (Fin 240)},
    Rep 240 (tElt tPlusCert i false) X → X ∈ closure (permsA 240 tPlusGensArr) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi X hX
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [(isId_iff hX).1 t_facts.id0]
      exact one_mem _
    · obtain ⟨k, hk, j, hj, he⟩ := t_facts.tree i hi hpos
      have hJ := rep_tElt (hj.trans hi)
      rw [eq_of_eqA hX (rep_compA (rep_tPlusGen hk) hJ) he]
      exact mul_mem (subset_closure (tPlusGen_mem_permsA hk)) (ih j hj (hj.trans hi) hJ)

theorem exists_tElt_of_mem_closure {X : Equiv.Perm (Fin 240)}
    (hX : X ∈ closure (permsA 240 tPlusGensArr)) :
    ∃ i < 8192, Rep 240 (tElt tPlusCert i false) X := by
  have step : ∀ g ∈ permsA 240 tPlusGensArr, ∀ Y : Equiv.Perm (Fin 240),
      (∃ i < 8192, Rep 240 (tElt tPlusCert i false) Y) →
        ∃ i < 8192, Rep 240 (tElt tPlusCert i false) (g * Y) := by
    rintro _ ⟨k, hk, rfl⟩ Y ⟨i, hi, hY⟩
    rw [Set.mem_ofPred_eq, tPlusGensArr_size] at hk
    obtain ⟨j, hj, he⟩ := t_facts.closed i hi k hk
    exact ⟨j, hj, rep_of_eqA (rep_compA (rep_tPlusGen hk) hY) he⟩
  refine closure_induction_left (p := fun Y _ => ∃ i < 8192, Rep 240 (tElt tPlusCert i false) Y)
    ⟨0, by norm_num, ?_⟩ (fun g hg Y _ hY => step g hg Y hY) (fun g hg Y _ hY => ?_) hX
  · have h0 := rep_tElt (i := 0) (by norm_num)
    rwa [(isId_iff h0).1 t_facts.id0] at h0
  · obtain ⟨k, hk, rfl⟩ := hg
    rw [Set.mem_ofPred_eq, tPlusGensArr_size] at hk
    rw [inv_eq_of_mul_eq_one_right (tPlusGen_mul_self hk)]
    exact step _ (tPlusGen_mem_permsA hk) Y hY

theorem tPlusGensArr_sign {k : ℕ} (hk : k < 7) :
    tPlusGensArr[k]! = signArr (frameDecode (1 + 2 ^ (k + 1))) := by
  rw [tPlusGensArr, getElem!_pos _ k (by simp [pPlusGens]; omega)]
  simp only [List.getElem_toArray]
  rw [List.getElem_append_left (by simpa using hk)]
  simp

theorem tPlusGensArr_perm {k : ℕ} (hk : k < 6) :
    tPlusGensArr[7 + k]! = permArr (pPlusGens.getD k 1) := by
  rw [tPlusGensArr, getElem!_pos _ (7 + k) (by simp [pPlusGens]; omega)]
  simp only [List.getElem_toArray]
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_map, List.length_range, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by simpa [pPlusGens] using hk)]
  congr 2
  omega

theorem frameDecode_basis_mem {k : ℕ} (hk : k < 7) : frameDecode (1 + 2 ^ (k + 1)) ∈ evenSub := by
  rw [mem_evenSub_iff_frameWt]
  interval_cases k <;> decide

theorem tGenWords_lt {k : ℕ} (hk : k < 13) : ∀ r ∈ tGenWords.getD k [], r < 240 := by
  interval_cases k <;> decide

theorem tGenWords_even {k : ℕ} (hk : k < 13) : Even (tGenWords.getD k []).length := by
  interval_cases k <;> decide

theorem tPlusGen_eq_wordPerm {k : ℕ} (hk : k < 13) :
    permOfArr 240 tPlusGensArr[k]! = wordPerm (tGenWords.getD k []) := by
  have h := allLt_spec tGen_check hk
  exact permOfArr_eq_of_rep (rep_of_eqA (rep_wordArr _ (tGenWords_lt hk)) (eqA_symm h))

theorem tPlusGen_mem_wPlus {k : ℕ} (hk : k < 13) : permOfArr 240 tPlusGensArr[k]! ∈ wPlus := by
  rw [tPlusGen_eq_wordPerm hk]
  exact wordPerm_mem_wPlus (tGenWords_lt hk) (tGenWords_even hk)

theorem mem_pPlusGens {σ : Equiv.Perm (Fin 8)} :
    σ ∈ pPlusGens ↔ ∃ k < 6, pPlusGens.getD k 1 = σ := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
    exact ⟨k, by simpa [pPlusGens] using hk, by rw [List.getD_eq_getElem]⟩
  · rintro ⟨k, hk, rfl⟩
    rw [List.getD_eq_getElem _ _ (by simpa [pPlusGens] using hk)]
    exact List.getElem_mem _

theorem permMat_pPlusGens_mem_wPlus {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ pPlusGens) :
    permMat σ ∈ wPlus := by
  obtain ⟨k, hk, rfl⟩ := mem_pPlusGens.1 hσ
  have := tPlusGen_mem_wPlus (k := 7 + k) (by omega)
  rwa [tPlusGensArr_perm hk] at this

theorem permOfArr_tPlusGens {k : ℕ} (hk : k < 13) :
    permOfArr 240 tPlusGensArr[k]! ∈ signPerm '' (evenSub : Set FrameVec) ∪
      {g | ∃ σ ∈ pPlusGens, permMat σ = g} := by
  rcases Nat.lt_or_ge k 7 with h7 | h7
  · left
    rw [tPlusGensArr_sign h7]
    exact ⟨_, frameDecode_basis_mem h7, rfl⟩
  · right
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h7
    rw [tPlusGensArr_perm (by omega)]
    exact ⟨_, mem_pPlusGens.2 ⟨j, by omega, rfl⟩, rfl⟩

theorem tPlusSub_eq : tPlusSub = closure (permsA 240 tPlusGensArr) := by
  apply le_antisymm
  · rw [tPlusSub, closure_le]
    rintro g (⟨v, hv, rfl⟩ | ⟨σ, hσ, rfl⟩)
    · obtain ⟨i, hi, he⟩ := t_facts.sign _ (frameEncode_lt v) (by simpa using framePop_even hv)
      rw [signArrs_encode] at he
      exact mem_closure_of_tElt i hi (rep_of_eqA (rep_signArr hv) he)
    · obtain ⟨k, hk, rfl⟩ := mem_pPlusGens.1 hσ
      refine subset_closure ⟨7 + k, show 7 + k < tPlusGensArr.size by
        rw [tPlusGensArr_size]; omega, ?_⟩
      change permOfArr 240 tPlusGensArr[7 + k]! = _
      rw [tPlusGensArr_perm hk]
      rfl
  · rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [Set.mem_ofPred_eq, tPlusGensArr_size] at hk
    exact subset_closure (permOfArr_tPlusGens hk)

theorem tPlusSub_le_wPlus : tPlusSub ≤ wPlus := by
  rw [tPlusSub, closure_le]
  rintro g (⟨v, hv, rfl⟩ | ⟨σ, hσ, rfl⟩)
  · exact signPerm_mem_wPlus hv
  · exact permMat_pPlusGens_mem_wPlus hσ

theorem eSub_le_tPlusSub : eSub ≤ tPlusSub := by
  rw [eSub, closure_le]
  exact fun g hg => subset_closure (Or.inl hg)

theorem exists_rep_of_mem_tPlusSub {x : Equiv.Perm (Fin 240)} (hx : x ∈ tPlusSub) :
    ∃ i < 8192, Rep 240 (tElt tPlusCert i false) x := by
  rw [tPlusSub_eq] at hx
  exact exists_tElt_of_mem_closure hx

theorem mem_tPlusSub_of_rep {i : ℕ} (hi : i < 8192) {x : Equiv.Perm (Fin 240)}
    (hx : Rep 240 (tElt tPlusCert i false) x) : x ∈ tPlusSub := by
  rw [tPlusSub_eq]
  exact mem_closure_of_tElt i hi hx

theorem card_tPlusSub : Nat.card tPlusSub = 2 ^ 13 := by
  let f : Fin 8192 → tPlusSub := fun i =>
    ⟨permOfArr 240 (tElt tPlusCert i false), mem_tPlusSub_of_rep i.2 (rep_tElt i.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => ?_, fun x => ?_⟩
    · by_contra hij
      have hd := t_facts.distinct i i.2 j j.2 (fun e => hij (Fin.ext e))
      rw [(eqA_iff (rep_tElt i.2) (rep_tElt j.2)).2 (congrArg Subtype.val h)] at hd
      exact Bool.noConfusion hd
    · obtain ⟨i, hi, hr⟩ := exists_rep_of_mem_tPlusSub x.2
      exact ⟨⟨i, hi⟩, Subtype.ext (permOfArr_eq_of_rep hr)⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem rep_s0Arr : Rep 240 s0Arr sZero := by
  rw [sZero_eq_refl]
  exact rep_refl (by norm_num)

theorem sZero_conj_tPlusGen {k : ℕ} (hk : k < 13) :
    sZero * permOfArr 240 tPlusGensArr[k]! * sZero ∈ tPlusSub := by
  obtain ⟨j, hj, he⟩ := t_facts.s0 k hk
  rw [tPlusSub_eq]
  exact mem_closure_of_tElt j hj
    (rep_of_eqA (rep_compA (rep_compA rep_s0Arr (rep_tPlusGen hk)) rep_s0Arr) he)

theorem sZero_conj_mem_tPlusSub {x : Equiv.Perm (Fin 240)} (hx : x ∈ tPlusSub) :
    sZero * x * sZero ∈ tPlusSub := by
  have hs : sZero⁻¹ = sZero := inv_eq_of_mul_eq_one_right sZero_mul_self
  have hle : tPlusSub ≤ tPlusSub.comap (MulAut.conj sZero).toMonoidHom := by
    conv_lhs => rw [tPlusSub_eq]
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [Set.mem_ofPred_eq, tPlusGensArr_size] at hk
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hs]
    exact sZero_conj_tPlusGen hk
  have := hle hx
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hs] at this

theorem tPlusSub_le_tSub : tPlusSub ≤ tSub := by
  rw [tPlusSub, closure_le]
  rintro g (hg | ⟨σ, hσ, rfl⟩)
  · exact subset_closure (Or.inl hg)
  · exact subset_closure (Or.inr ⟨σ, List.mem_cons_of_mem _ hσ, rfl⟩)

theorem sZero_mem_tSub : sZero ∈ tSub :=
  subset_closure (Or.inr ⟨Equiv.swap 0 1, List.mem_cons_self, sZero_eq_permMat.symm⟩)

theorem mem_tSub_iff {x : Equiv.Perm (Fin 240)} :
    x ∈ tSub ↔ x ∈ tPlusSub ∨ x * sZero ∈ tPlusSub := by
  have hs : sZero⁻¹ = sZero := inv_eq_of_mul_eq_one_right sZero_mul_self
  constructor
  · intro hx
    have key : ∀ g, (g ∈ tPlusSub ∨ g = sZero) → ∀ y, (y ∈ tPlusSub ∨ y * sZero ∈ tPlusSub) →
        (g * y ∈ tPlusSub ∨ g * y * sZero ∈ tPlusSub) := by
      rintro g (hgT | rfl) y hy
      · rcases hy with hy | hy
        · exact Or.inl (mul_mem hgT hy)
        · exact Or.inr (by rw [mul_assoc]; exact mul_mem hgT hy)
      · rcases hy with hy | hy
        · exact Or.inr (sZero_conj_mem_tPlusSub hy)
        · left
          have := sZero_conj_mem_tPlusSub hy
          rwa [show sZero * (y * sZero) * sZero = sZero * y * (sZero * sZero) by group,
            sZero_mul_self, mul_one] at this
    have hgen : ∀ g ∈ signPerm '' (evenSub : Set FrameVec) ∪
        {g | ∃ σ ∈ Equiv.swap 0 1 :: pPlusGens, permMat σ = g}, g ∈ tPlusSub ∨ g = sZero := by
      rintro g (hg | ⟨σ, hσ, rfl⟩)
      · exact Or.inl (subset_closure (Or.inl hg))
      · rcases List.mem_cons.1 hσ with rfl | hσ
        · exact Or.inr sZero_eq_permMat.symm
        · exact Or.inl (subset_closure (Or.inr ⟨σ, hσ, rfl⟩))
    refine closure_induction_left (p := fun y _ => y ∈ tPlusSub ∨ y * sZero ∈ tPlusSub)
      (Or.inl (one_mem _)) (fun g hg y _ hy => key g (hgen g hg) y hy)
      (fun g hg y _ hy => key g⁻¹ ?_ y hy) hx
    rcases hgen g hg with h | rfl
    · exact Or.inl (inv_mem h)
    · exact Or.inr hs
  · rintro (h | h)
    · exact tPlusSub_le_tSub h
    · have := mul_mem (tPlusSub_le_tSub h) sZero_mem_tSub
      rwa [mul_assoc, sZero_mul_self, mul_one] at this

theorem tSub_le_wE8 : tSub ≤ wE8 := by
  intro x hx
  rcases mem_tSub_iff.1 hx with h | h
  · exact wPlus_le (tPlusSub_le_wPlus h)
  · have := mul_mem (wPlus_le (tPlusSub_le_wPlus h)) sZero_mem_wE8
    rwa [mul_assoc, sZero_mul_self, mul_one] at this

theorem tPlusSub_eq_inf : tPlusSub = tSub ⊓ wPlus := by
  apply le_antisymm (le_inf tPlusSub_le_tSub tPlusSub_le_wPlus)
  intro x hx'
  obtain ⟨hx, hxw⟩ := mem_inf.1 hx'
  rcases mem_tSub_iff.1 hx with h | h
  · exact h
  · exfalso
    apply sZero_not_mem_wPlus
    have := mul_mem (inv_mem hxw) (tPlusSub_le_wPlus h)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this

theorem card_tSub : Nat.card tSub = 2 ^ 14 := by
  set f : tSub →* ℤˣ := Equiv.Perm.sign.comp tSub.subtype with hf
  have hker : f.ker = tPlusSub.subgroupOf tSub := by
    ext ⟨g, hg⟩
    rw [MonoidHom.mem_ker, mem_subgroupOf, tPlusSub_eq_inf, mem_inf, mem_wPlus_iff]
    simp [hf, hg, tSub_le_wE8 hg]
  have hrange : Nat.card f.range = 2 := by
    have htop : f.range = ⊤ := by
      rw [eq_top_iff]
      rintro u -
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact one_mem _
      · exact ⟨⟨sZero, sZero_mem_tSub⟩, by
          change Equiv.Perm.sign sZero = -1
          rw [sZero_eq_refl, sign_refl (by norm_num)]⟩
    rw [htop, card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange, hker] at h1
  have h2 : Nat.card (tPlusSub.subgroupOf tSub) = Nat.card tPlusSub :=
    Nat.card_congr (subgroupOfEquivOfLe tPlusSub_le_tSub).toEquiv
  rw [h2, card_tPlusSub] at h1
  rw [← h1]
  norm_num

theorem tElt_true (c : ArrCert) (i : ℕ) : tElt c i true = compA 240 (tElt c i false) s0Arr := by
  simp only [tElt, ite_true, Bool.false_eq_true, ite_false]

theorem exists_rep_of_mem_tSub {x : Equiv.Perm (Fin 240)} (hx : x ∈ tSub) :
    ∃ i < 8192, ∃ b ∈ [false, true], Rep 240 (tElt tPlusCert i b) x := by
  rcases mem_tSub_iff.1 hx with h | h
  · obtain ⟨i, hi, hrep⟩ := exists_rep_of_mem_tPlusSub h
    exact ⟨i, hi, false, by simp, hrep⟩
  · obtain ⟨i, hi, hrep⟩ := exists_rep_of_mem_tPlusSub h
    refine ⟨i, hi, true, by simp, ?_⟩
    have := rep_compA hrep rep_s0Arr
    rw [mul_assoc, sZero_mul_self, mul_one] at this
    rw [tElt_true]
    exact this

theorem factorization_card_wE8 : (Nat.card wE8).factorization 2 = 14 := by
  rw [card_wE8, Nat.factorization_def _ Nat.prime_two,
    show (696729600 : ℕ) = 2 ^ 14 * 42525 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

@[expose] def tSylow : Sylow 2 wE8 :=
  Sylow.ofCard (tSub.subgroupOf wE8) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe tSub_le_wE8).toEquiv, card_tSub,
      factorization_card_wE8])

theorem commA'_of_comm {x g : Array ℕ} {X G : Equiv.Perm (Fin 240)} (hx : Rep 240 x X)
    (hg : Rep 240 g G) (h : X * G = G * X) : commA' x g = true :=
  (eqA_iff (rep_compA hx hg) (rep_compA hg hx)).2 h

theorem eqA_negArr_iff {x : Array ℕ} {X : Equiv.Perm (Fin 240)} (hx : Rep 240 x X) :
    eqA 240 x negArr = true ↔ X = zPerm := eqA_iff hx rep_negArr

theorem tPlusGen_mem {k : ℕ} (hk : k < 13) : permOfArr 240 tPlusGensArr[k]! ∈ tPlusSub := by
  rw [tPlusSub_eq]
  exact subset_closure ⟨k, show k < tPlusGensArr.size by rw [tPlusGensArr_size]; exact hk, rfl⟩

theorem center_tSub {x : Equiv.Perm (Fin 240)} (hx : x ∈ tSub)
    (hc : ∀ y ∈ tSub, x * y = y * x) : x = 1 ∨ x = zPerm := by
  obtain ⟨i, hi, b, hb, hrep⟩ := exists_rep_of_mem_tSub hx
  have h := t_facts.cent i hi b hb ⟨allLt_iff.2 fun k hk => commA'_of_comm hrep (rep_tPlusGen hk)
    (hc _ (tPlusSub_le_tSub (tPlusGen_mem hk))), commA'_of_comm hrep rep_s0Arr
      (hc _ sZero_mem_tSub)⟩
  rcases h with h | h
  · exact Or.inl ((isId_iff hrep).1 h)
  · exact Or.inr ((eqA_negArr_iff hrep).1 h)

theorem center_tPlusSub {x : Equiv.Perm (Fin 240)} (hx : x ∈ tPlusSub)
    (hc : ∀ y ∈ tPlusSub, x * y = y * x) : x = 1 ∨ x = zPerm := by
  obtain ⟨i, hi, hrep⟩ := exists_rep_of_mem_tPlusSub hx
  have h := t_facts.centPlus i hi (allLt_iff.2 fun k hk => commA'_of_comm hrep (rep_tPlusGen hk)
    (hc _ (tPlusGen_mem hk)))
  rcases h with h | h
  · exact Or.inl ((isId_iff hrep).1 h)
  · exact Or.inr ((eqA_negArr_iff hrep).1 h)

theorem exists_conj_mem_tSub {x : Equiv.Perm (Fin 240)} (hx : x ∈ wE8) {k : ℕ}
    (hk : x ^ (2 ^ k) = 1) : ∃ g ∈ wE8, g * x * g⁻¹ ∈ tSub := by
  set X : wE8 := ⟨x, hx⟩
  have hX : X ^ (2 ^ k) = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk)
  have hp : IsPGroup 2 (zpowers X) := by
    rintro ⟨y, n, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change ((X ^ n) ^ (2 ^ k) : wE8) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hX, one_zpow]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq wE8 Q tSylow
  have hXQ : X ∈ (Q : Subgroup wE8) := hQ (mem_zpowers X)
  have hmem : MulAut.conj g X ∈ ((g • Q : Sylow 2 wE8) : Subgroup wE8) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul X (MulAut.conj g) _ hXQ
  rw [hg] at hmem
  refine ⟨g, g.2, ?_⟩
  have h2 : (MulAut.conj g X : wE8) ∈ tSub.subgroupOf wE8 := hmem
  rw [mem_subgroupOf, MulAut.conj_apply] at h2
  exact h2

theorem mem_wPlus_of_mul_self_eq_zPerm {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (h : w * w = zPerm) : w ∈ wPlus := by
  have h4 : w ^ (2 ^ 2) = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, sq w, h, sq, zPerm_mul_self]
  obtain ⟨g, hg, hgt⟩ := exists_conj_mem_tSub hw h4
  by_contra hwp
  obtain ⟨i, hi, b, hb, hrep⟩ := exists_rep_of_mem_tSub hgt
  have hsq : (g * w * g⁻¹) * (g * w * g⁻¹) = zPerm := by
    rw [show g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ by group, h,
      zPerm_comm g hg, mul_assoc, mul_inv_cancel, mul_one]
  have hnot : g * w * g⁻¹ ∉ wPlus := fun hc => hwp (by
    have := conj_mem_wPlus (inv_mem hg) hc
    rwa [show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at this)
  cases b with
  | false =>
    exact hnot (tPlusSub_le_wPlus (mem_tPlusSub_of_rep hi hrep))
  | true =>
    have h1 := t_facts.sqz i hi
    rw [(eqA_iff (rep_compA hrep hrep) rep_negArr).2 hsq] at h1
    exact absurd h1 (by decide)

theorem rho_facts {k : ℕ} (hk : k < 25) :
    Rep 240 rhoArrs[k]! (permOfArr 240 rhoArrs[k]!) ∧
      Rep 240 (invCand 240 rhoArrs[k]!) (permOfArr 240 rhoArrs[k]!)⁻¹ ∧
      permOfArr 240 rhoArrs[k]! ∈ wE8 := by
  have h := allLt_spec rhoWord_check hk
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := rep_permOfArr h.1
  have hw : ∀ r ∈ rhoWords.getD k [], r < 240 := by interval_cases k <;> decide
  have hr := rep_wordArr _ hw
  rw [eq_of_eqA h1 hr h.2]
  exact ⟨by rwa [← eq_of_eqA h1 hr h.2], by rwa [← eq_of_eqA h1 hr h.2], wordPerm_mem _ hw⟩

theorem rep_conjA' {g x : Array ℕ} {G X : Equiv.Perm (Fin 240)} (hg : Rep 240 g G)
    (hgi : Rep 240 (invCand 240 g) G⁻¹) (hx : Rep 240 x X) : Rep 240 (conjA' g x) (G * X * G⁻¹) :=
  rep_compA (rep_compA hg hx) hgi

theorem frameMaskOf_lt (x : Array ℕ) : frameMaskOf x < 256 := Nat.mod_lt _ (by norm_num)

theorem mem_e1Sub_of_memE1 {y : Array ℕ} {Y : Equiv.Perm (Fin 240)} (hy : Rep 240 y Y)
    (h : memE1 frameArrs y = true) : Y ∈ e1Sub := by
  rw [memE1, frameArrs_get (frameMaskOf_lt y)] at h
  exact mem_e1Sub.2 ⟨_, (eq_of_eqA hy (rep_frameArr _) h).symm⟩

theorem conj_e1Sub {x : Equiv.Perm (Fin 240)} (hx : x ∈ wE8) (hxx : x * x = 1) :
    ∃ g ∈ wE8, g * x * g⁻¹ ∈ e1Sub := by
  obtain ⟨g, hg, hgt⟩ := exists_conj_mem_tSub hx (k := 1) (by rw [pow_one, sq, hxx])
  obtain ⟨i, hi, b, hb, hrep⟩ := exists_rep_of_mem_tSub hgt
  have hsq : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hxx, mul_one,
      mul_inv_cancel]
  rcases t_facts.w8 i hi b hb ((isId_iff (rep_compA hrep hrep)).2 hsq) with h | h
  · refine ⟨g, hg, ?_⟩
    rw [(isId_iff hrep).1 h]
    exact one_mem _
  · rw [w8OK, List.any_eq_true] at h
    obtain ⟨k, hk, hmem⟩ := h
    rw [List.mem_range] at hk
    obtain ⟨hr, hri, hrw⟩ := rho_facts hk
    refine ⟨permOfArr 240 rhoArrs[k]! * g, mul_mem hrw hg, ?_⟩
    have := mem_e1Sub_of_memE1 (rep_conjA' hr hri hrep) hmem
    rwa [show permOfArr 240 rhoArrs[k]! * (g * x * g⁻¹) * (permOfArr 240 rhoArrs[k]!)⁻¹ =
      permOfArr 240 rhoArrs[k]! * g * x * (permOfArr 240 rhoArrs[k]! * g)⁻¹ by group] at this

theorem conj_e1PlusSub {x : Equiv.Perm (Fin 240)} (hx : x ∈ wPlus) (hxx : x * x = 1) :
    ∃ g ∈ wPlus, g * x * g⁻¹ ∈ e1PlusSub := by
  obtain ⟨g, hg, hge⟩ := conj_e1Sub (wPlus_le hx) hxx
  obtain ⟨v, hv⟩ := mem_e1Sub.1 hge
  have hvw : frameElt v ∈ wPlus := by rw [hv]; exact conj_mem_wPlus hg hx
  have hve := (frameElt_mem_wPlus_iff v).1 hvw
  by_cases hgp : g ∈ wPlus
  · exact ⟨g, hgp, mem_e1PlusSub.2 ⟨v, hve, hv⟩⟩
  · have hsg : sZero * g ∈ wPlus := mem_wPlus_iff.2 ⟨mul_mem sZero_mem_wE8 hg, by
      rw [map_mul, sign_eq_neg_one_of_not_mem sZero_mem_wE8 sZero_not_mem_wPlus,
        sign_eq_neg_one_of_not_mem hg hgp]
      decide⟩
    refine ⟨sZero * g, hsg, mem_e1PlusSub.2 ⟨v, hve, ?_⟩⟩
    rw [show sZero * g * x * (sZero * g)⁻¹ = sZero * (g * x * g⁻¹) * sZero⁻¹ by group, ← hv,
      sZero_eq_frameElt, frameElt_inv, ← frameElt_add, ← frameElt_add, add_comm (frameE 0),
      add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem pairMasks_spec : ∀ m ∈ pairMasks, m < 256 ∧ framePop m % 2 = 0 := by decide

theorem fgOK_spec {t : Array ℕ} {X : Equiv.Perm (Fin 240)} (ht : Rep 240 t X)
    (h : fgOK signArrs t = true) : ∃ v ∈ evenSub,
      (signPerm v * X) * (signPerm v * X) ≠ 1 ∧ (signPerm v * X) * (signPerm v * X) ≠ zPerm ∧
        ((signPerm v * X) * (signPerm v * X)) * ((signPerm v * X) * (signPerm v * X)) = 1 := by
  rw [fgOK, List.any_eq_true] at h
  obtain ⟨m, hm, hc⟩ := h
  have hm' := pairMasks_spec m hm
  have hv : frameDecode m ∈ evenSub := by
    rw [mem_evenSub_iff_frameWt, frameWt_frameDecode m hm'.1]
    exact hm'.2
  rw [signArrs_get hm'.1] at hc
  have hS := rep_signArr hv
  have hc' := rep_compA (rep_compA hS ht) (rep_compA hS ht)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  refine ⟨frameDecode m, hv, fun he => ?_, fun he => ?_, (isId_iff (rep_compA hc' hc')).1 h3⟩
  · rw [← isId_iff hc'] at he
    rw [he] at h1
    exact absurd h1 (by decide)
  · rw [← eqA_negArr_iff hc'] at he
    rw [he] at h2
    exact absurd h2 (by decide)

theorem foursGroupCondition_wPlus : FoursGroupCondition wPlus := by
  intro φ hφ hout
  obtain ⟨w, hw, hφw⟩ := exists_conj_eq φ
  have hwp : w ∉ wPlus := fun h => hout ⟨w, h⟩ (by
    ext x
    rw [hφw, MulAut.conj_apply]
    rfl)
  have hww : w * w = 1 := by
    have hc : ∀ x ∈ wPlus, w * w * x = x * (w * w) := by
      intro x hx
      have h1 := congrArg (fun ψ : MulAut wPlus => ((ψ ⟨x, hx⟩ : wPlus) : Equiv.Perm (Fin 240))) hφ
      simp only [MulAut.mul_apply, MulAut.one_apply] at h1
      rw [hφw, hφw] at h1
      calc w * w * x = (w * (w * x * w⁻¹) * w⁻¹) * (w * w) := by group
        _ = x * (w * w) := by rw [h1]
    rcases centralizer_wPlus (mul_mem hw hw) hc with h | h
    · exact h
    · exact absurd (mem_wPlus_of_mul_self_eq_zPerm hw h) hwp
  obtain ⟨g, hg, hgt⟩ := exists_conj_mem_tSub hw (k := 1) (by rw [pow_one, sq, hww])
  obtain ⟨i, hi, b, hb, hrep⟩ := exists_rep_of_mem_tSub hgt
  have hnot : g * w * g⁻¹ ∉ wPlus := fun hc => hwp (by
    have := conj_mem_wPlus (inv_mem hg) hc
    rwa [show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at this)
  have htrue : b = true := by
    cases b with
    | false => exact absurd (tPlusSub_le_wPlus (mem_tPlusSub_of_rep hi hrep)) hnot
    | true => rfl
  subst htrue
  have hsq : (g * w * g⁻¹) * (g * w * g⁻¹) = 1 := by
    rw [show g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ by group, hww, mul_one,
      mul_inv_cancel]
  obtain ⟨v, hv, hc1, hc2, hc3⟩ :=
    fgOK_spec hrep (t_facts.fg i hi ((isId_iff (rep_compA hrep hrep)).2 hsq))
  set S := signPerm v
  set t := g * w * g⁻¹
  have hS2 : S * S = 1 := signPerm_mul_self hv
  have hl : g⁻¹ * S * g ∈ wPlus := by
    have := conj_mem_wPlus (inv_mem hg) (signPerm_mem_wPlus hv)
    rwa [inv_inv] at this
  have hval : ((⟨g⁻¹ * S * g, hl⟩ : wPlus) * (φ ⟨g⁻¹ * S * g, hl⟩)⁻¹ : wPlus) =
      (g⁻¹ * ((S * t) * (S * t)) * g : Equiv.Perm (Fin 240)) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hφw]
    simp only [t]
    have hw1 : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have hS1 : S⁻¹ = S := inv_eq_of_mul_eq_one_right hS2
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, hw1, hS1]
    group
  refine ⟨⟨g⁻¹ * S * g, hl⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, sq, hval, Subgroup.coe_one]
    rw [show g⁻¹ * (S * t * (S * t)) * g * (g⁻¹ * (S * t * (S * t)) * g) =
      g⁻¹ * ((S * t * (S * t)) * (S * t * (S * t))) * g by group, hc3, mul_one, inv_mul_cancel]
  · rw [mem_center_wPlus, hval]
    rintro (h | h)
    · apply hc1
      calc S * t * (S * t) = g * (g⁻¹ * (S * t * (S * t)) * g) * g⁻¹ := by group
        _ = 1 := by rw [h, mul_one, mul_inv_cancel]
    · apply hc2
      calc S * t * (S * t) = g * (g⁻¹ * (S * t * (S * t)) * g) * g⁻¹ := by group
        _ = zPerm := by rw [h, zPerm_comm g hg, mul_assoc, mul_inv_cancel, mul_one]

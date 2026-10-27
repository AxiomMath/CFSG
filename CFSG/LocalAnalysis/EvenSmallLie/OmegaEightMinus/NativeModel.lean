
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeModelBase

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeCheck

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEightMinus

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf size_pushWords pushWords_getElem!
  chain_strong_spec extract_getElem! mem_normalizer_of_conj_mem)

theorem omegaChain_ok :
    rawChainOK 136 (omegaS.extract 0 10) omegaS (omegaBase.map Fin.val).toArray
        (wordsOf 10 omegaWords) 4 = true ∧
      rawOrbitSizes 136 omegaS (omegaBase.map Fin.val).toArray = [136, 63, 30, 16, 8, 3, 2] := by
  have h := omegaChain_check
  simp only [omegaChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem autChain_ok :
    rawChainOK 136 (autS.extract 0 11) autS (autBase.map Fin.val).toArray
        (wordsOf 11 autWords) 4 = true ∧
      rawOrbitSizes 136 autS (autBase.map Fin.val).toArray = [136, 63, 30, 16, 6, 4, 2, 2] := by
  have h := autChain_check
  simp only [autChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem sylowChain_ok :
    rawChainOK 136 (sylowS.extract 0 6) sylowS (sylowBase.map Fin.val).toArray
        (wordsOf 6 sylowWords) 4 = true ∧
      rawOrbitSizes 136 sylowS (sylowBase.map Fin.val).toArray = [64, 2, 8, 4, 2] := by
  have h := sylowChain_check
  simp only [sylowChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem card_omegaT : Nat.card omegaT = 197406720 := by
  rw [omegaT, omegaQ, ofArrays_card (by norm_num) omegaChain_ok.1, omegaChain_ok.2]
  rfl

theorem card_autT : Nat.card autT = 394813440 := by
  rw [autT, autQ, ofArrays_card (by norm_num) autChain_ok.1, autChain_ok.2]
  rfl

theorem card_sylowT : Nat.card sylowT = 8192 := by
  rw [sylowT, sylowQ, ofArrays_card (by norm_num) sylowChain_ok.1, sylowChain_ok.2]
  rfl

theorem rep_gen
    {i : ℕ} (hi : i < 11) : Rep 136 genArrs[i]! (gen i) := by
  have h := (chain_strong_spec (hn := by norm_num) (hk := by rw [autS_size]; norm_num)
    (hb := by decide) autChain_ok.1 i (by rw [autS_size]; omega)).1
  rwa [autS_getElem! hi] at h

theorem rep_gen_inv
    {i : ℕ} (hi : i < 11) : Rep 136 (invCand 136 genArrs[i]!) (gen i)⁻¹ := by
  have h := (chain_strong_spec (hn := by norm_num) (hk := by rw [autS_size]; norm_num)
    (hb := by decide) autChain_ok.1 i (by rw [autS_size]; omega)).2.1
  rwa [OmegaEight.getElem!_rawInvs' (by rw [autS_size]; omega), autS_getElem! hi] at h

theorem structure_ok : ∀ i < 10,
    eqA 136 (conjArr genArrs[10]! genArrs[i]!) genArrs[rvPerm.getD i 0]! = true := by
  have h := structure_check
  simp only [structureCheck, List.all_eq_true, List.mem_range] at h
  exact h

theorem conj_gen_rv {i : ℕ} (hi : i < 10) :
    gen 10 * gen i * (gen 10)⁻¹ = gen (rvPerm.getD i 0) :=
  eq_of_eqA (rep_conjArr (rep_gen (by norm_num)) (rep_gen_inv (by norm_num))
    (rep_gen (by omega))) (rep_gen (by have := rvPerm_lt hi; omega)) (structure_ok i hi)

theorem conj_mem_omegaT_of_gen
    {g : Equiv.Perm (Fin 136)} (hg : g ∈ omegaT) :
    gen 10 * g * (gen 10)⁻¹ ∈ omegaT := by
  have hle : omegaT ≤ omegaT.comap (MulAut.conj (gen 10)).toMonoidHom := by
    calc omegaT = Subgroup.closure {g | ∃ i < 10, gen i = g} := omegaT_eq
      _ ≤ _ := by
        rw [Subgroup.closure_le]
        rintro _ ⟨i, hi, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          conj_gen_rv hi]
        exact gen_mem_omegaT (rvPerm_lt hi)
  have := hle hg
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem autT_le_normalizer
    : autT ≤ Subgroup.normalizer (omegaT : Set (Equiv.Perm (Fin 136))) := by
  rw [autT_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  by_cases h10 : i < 10
  · exact Subgroup.le_normalizer (gen_mem_omegaT h10)
  · rw [show i = 10 by omega]
    exact mem_normalizer_of_conj_mem fun g hg => conj_mem_omegaT_of_gen hg

theorem conj_mem_omegaT {a : Equiv.Perm (Fin 136)} (ha : a ∈ autT)
    {g : Equiv.Perm (Fin 136)} : g ∈ omegaT ↔ a * g * a⁻¹ ∈ omegaT :=
  Subgroup.mem_normalizer_iff.1 (autT_le_normalizer ha) g

theorem sgen_spec {j : ℕ} (hj : j < 18) :
    Rep 136 omegaS[j]! (sgen j) ∧ Rep 136 (rawInvs 136 omegaS)[j]! (sgen j)⁻¹ ∧
      sgen j ∈ omegaT :=
  chain_strong_spec (hn := by norm_num) (hk := by rw [omegaS_size]; norm_num) (hb := by decide)
    omegaChain_ok.1 j (by rw [omegaS_size]; exact hj)

theorem stab_ok
    : (∀ j ∈ stabIdx, j < omegaS.size ∧ (omegaS[j]!)[0]! = 0) ∧
    ∀ p < 135, ∃ j ∈ stabIdx, (omegaS[j]!)[p + 1]! ≠ p + 1 := by
  have h := stab_check
  simp only [stabCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq,
    beq_iff_eq, bne_iff_ne, List.mem_range] at h
  exact h

theorem sgen_fix_zero {j : ℕ} (hj : j ∈ stabIdx) : sgen j 0 = 0 := by
  have h := stab_ok.1 j hj
  rw [omegaS_size] at h
  apply Fin.ext
  have e := (sgen_spec h.1).1 0
  rw [← e]
  exact h.2

theorem exists_sgen_moves
    {p : Fin 136} (hp : p ≠ 0) : ∃ j ∈ stabIdx, sgen j p ≠ p := by
  obtain ⟨j, hj, hne⟩ := stab_ok.2 (p - 1) (by have := p.2; omega)
  have hp1 : (p : ℕ) - 1 + 1 = p := by
    have : (p : ℕ) ≠ 0 := fun h => hp (Fin.ext h)
    omega
  rw [hp1] at hne
  have hjs := (stab_ok.1 j hj).1
  rw [omegaS_size] at hjs
  refine ⟨j, hj, fun h => hne ?_⟩
  rw [(sgen_spec hjs).1.apply p.2, h]

theorem fix_of_comm
    {a : Equiv.Perm (Fin 136)} (ha : ∀ g ∈ omegaT, g * a = a * g) : a 0 = 0 := by
  by_contra hne
  obtain ⟨j, hj, hmove⟩ := exists_sgen_moves hne
  have hjs := (stab_ok.1 j hj).1
  rw [omegaS_size] at hjs
  have hcomm := congrArg (fun f : Equiv.Perm (Fin 136) => f 0) (ha _ (sgen_spec hjs).2.2)
  simp only [Equiv.Perm.mul_apply, sgen_fix_zero hj] at hcomm
  exact hmove hcomm

theorem tree_ok : treeLit.2.2[0]! = 0 ∧ ∀ i < 135,
    treeLit.1[i + 1]! < 136 ∧ treeLit.2.1[i + 1]! < 10 ∧
      treeLit.2.2[treeLit.1[i + 1]!]! < treeLit.2.2[i + 1]! ∧
      (genArrs[treeLit.2.1[i + 1]!]!)[treeLit.1[i + 1]!]! = i + 1 := by
  have h := tree_check
  simp only [treeLitCheck, treeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact ⟨h.1, fun i hi => ⟨(h.2 i hi).1.1.1, (h.2 i hi).1.1.2, (h.2 i hi).1.2, (h.2 i hi).2⟩⟩

theorem exists_omegaT_apply_zero
    (x : Fin 136) : ∃ g ∈ omegaT, g 0 = x := by
  obtain ⟨-, hstep⟩ := tree_ok
  suffices H : ∀ d, ∀ y : ℕ, y < 136 → treeLit.2.2[y]! = d →
      ∃ g ∈ omegaT, ((g 0 : Fin 136) : ℕ) = y by
    obtain ⟨g, hg, e⟩ := H _ x x.2 rfl
    exact ⟨g, hg, Fin.ext e⟩
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro y hy hd
    rcases Nat.eq_zero_or_pos y with rfl | hpos
    · exact ⟨1, omegaT.one_mem, rfl⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hstep (y - 1) (by omega)
      rw [show y - 1 + 1 = y by omega] at h1 h2 h3 h4
      obtain ⟨g, hg, e⟩ := ih _ (hd ▸ h3) _ h1 rfl
      refine ⟨gen treeLit.2.1[y]! * g, omegaT.mul_mem (gen_mem_omegaT h2) hg, ?_⟩
      rw [Equiv.Perm.mul_apply, ← rep_gen (by omega) (g 0), e, h4]

theorem centralizer_omegaT
    : Subgroup.centralizer (omegaT : Set (Equiv.Perm (Fin 136))) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_centralizer_iff] at ha
  rw [Subgroup.mem_bot]
  refine Equiv.ext fun p => ?_
  obtain ⟨g, hg, rfl⟩ := exists_omegaT_apply_zero p
  have h := congrArg (fun f : Equiv.Perm (Fin 136) => f 0) (ha g hg)
  simp only [Equiv.Perm.mul_apply, fix_of_comm ha] at h
  rw [Equiv.Perm.one_apply]
  exact h.symm

@[expose] def autConj : autT →* MulAut omegaT :=
  (Subgroup.normalizerMonoidHom omegaT).comp (Subgroup.inclusion autT_le_normalizer)

theorem autConj_apply (a : autT) (g : omegaT) :
    ((autConj a g : omegaT) : Equiv.Perm (Fin 136)) = a * g * (a : Equiv.Perm (Fin 136))⁻¹ :=
  rfl

theorem autConj_injective : Function.Injective autConj := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have hc : (a : Equiv.Perm (Fin 136)) ∈
      Subgroup.centralizer (omegaT : Set (Equiv.Perm (Fin 136))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := congrArg (fun α : MulAut omegaT => ((α ⟨h, hh⟩ : omegaT) : Equiv.Perm (Fin 136)))
      (MonoidHom.mem_ker.1 ha)
    simp only [autConj_apply, MulAut.one_apply] at h1
    calc h * a = a * h * (a : Equiv.Perm (Fin 136))⁻¹ * a := by rw [h1]
      _ = a * h := by group
  rw [centralizer_omegaT, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.2 (Subtype.ext hc)

theorem card_autT_eq : Nat.card autT = 2 * Nat.card omegaT := by
  rw [card_autT, card_omegaT]

end CFSG.EvenSmallLie.OmegaEightMinus

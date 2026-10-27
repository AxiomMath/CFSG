module

public import CFSG.RankThree.Native.Fi22FiveCentralizers
public import Certificates.Certificate13506
public import Certificates.Certificate13507
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.EvenSmallLie.OmegaEight CFSG.RankThree.Native CFSG.ComponentClassification.J2Cover

@[expose] def i242Stab (σ : Fin 120 → Fin 3510) : Subgroup (Equiv.Perm (Fin 3510)) where
  carrier := {g | ∀ p, (∃ v, σ v = p) ↔ ∃ v, σ v = g p}
  mul_mem' := fun {g h} hg hh p => (hh p).trans (hg (h p))
  one_mem' := fun _ => Iff.rfl
  inv_mem' := fun {g} hg p => by
    have := hg (g⁻¹ p)
    rw [show g (g⁻¹ p) = p by simp] at this
    exact this.symm

@[expose] noncomputable def i242ResFun (σ : Fin 120 → Fin 3510) (g : i242Stab σ) (v : Fin 120) :
    Fin 120 :=
  Classical.choose (((g.2 (σ v)).1 ⟨v, rfl⟩))

theorem i242ResFun_spec (σ : Fin 120 → Fin 3510) (g : i242Stab σ) (v : Fin 120) :
    σ (i242ResFun σ g v) = (g : Equiv.Perm (Fin 3510)) (σ v) :=
  Classical.choose_spec (((g.2 (σ v)).1 ⟨v, rfl⟩))

theorem i242ResFun_inv {σ : Fin 120 → Fin 3510} (hσ : Function.Injective σ) (g : i242Stab σ)
    (v : Fin 120) : i242ResFun σ g⁻¹ (i242ResFun σ g v) = v := by
  apply hσ
  rw [i242ResFun_spec σ g⁻¹, i242ResFun_spec σ g]
  simp

theorem i242ResFun_inv' {σ : Fin 120 → Fin 3510} (hσ : Function.Injective σ) (g : i242Stab σ)
    (v : Fin 120) : i242ResFun σ g (i242ResFun σ g⁻¹ v) = v := by
  apply hσ
  rw [i242ResFun_spec σ g, i242ResFun_spec σ g⁻¹]
  simp

@[expose] noncomputable def i242Res {σ : Fin 120 → Fin 3510} (hσ : Function.Injective σ) :
    i242Stab σ →* Equiv.Perm (Fin 120) where
  toFun g := ⟨i242ResFun σ g, i242ResFun σ g⁻¹, i242ResFun_inv hσ g, i242ResFun_inv' hσ g⟩
  map_one' := by
    refine Equiv.ext fun v => hσ ?_
    rw [Equiv.Perm.coe_one, id]
    exact i242ResFun_spec σ 1 v
  map_mul' g h := by
    refine Equiv.ext fun v => hσ ?_
    show σ (i242ResFun σ (g * h) v) = σ (i242ResFun σ g (i242ResFun σ h v))
    rw [i242ResFun_spec σ (g * h), i242ResFun_spec σ g, i242ResFun_spec σ h]
    rfl

theorem i242Res_spec {σ : Fin 120 → Fin 3510} (hσ : Function.Injective σ) (g : i242Stab σ)
    (v : Fin 120) : σ (i242Res hσ g v) = (g : Equiv.Perm (Fin 3510)) (σ v) :=
  i242ResFun_spec σ g v

@[expose] def i242Sig (v : Fin 120) : Fin 3510 :=
  ⟨i242Sigma.getD v 0 % 3510, Nat.mod_lt _ (by norm_num)⟩

theorem i242_action_facts :
    (∀ r < 8, lettersOK 12 (i242Words.getD r []) = true) ∧
    (∀ v < 120, i242Sigma.getD v 0 < 3510 ∧ i242SigmaInv[i242Sigma.getD v 0]! = v) ∧
    (∀ p < 3510, i242SigmaInv[p]! ≤ 120 ∧
      (120 ≤ i242SigmaInv[p]! ∨ i242Sigma.getD i242SigmaInv[p]! 0 = p)) ∧
    ∀ r < 8, (∀ v < 120, (i242YArr r)[i242Sigma.getD v 0]! =
        i242Sigma.getD ((genArrs[r]!)[v]!) 0) ∧
      ∀ p < 3510, (i242SigmaInv[(i242YArr r)[p]!]! < 120 ↔ i242SigmaInv[p]! < 120) := by
  have h := Certificates.certificate13507
  simp only [i242ActionCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen, hlet⟩, _⟩, _⟩, _⟩, hF⟩, hG⟩, hH⟩ := h
  refine ⟨fun r hr => hlet _ ?_, hF, hG, fun r hr => ?_⟩
  · rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  obtain ⟨h1, h2⟩ := hH r hr
  have hy : i242YArrs[r]! = i242YArr r := by
    rw [i242YArrs, getElem!_pos _ r (by simpa using hr), Array.getElem_map]
    simp
  rw [hy] at h1 h2
  exact ⟨h1, fun p hp => by simpa using h2 p hp⟩

theorem i242S_size : i242S.size = 17 := by
  rw [i242S, size_pushWords]
  simp [i242YArrs, omegaWords]

@[expose] noncomputable def i242Q : RawSchreierDatum 3510 :=
  RawSchreierDatum.ofArrays 3510 (by norm_num) i242S 8 (by rw [i242S_size]; norm_num) i242Base
    (by decide) (wordsOf 8 omegaWords)

@[expose] noncomputable def i242Y : Subgroup (Equiv.Perm (Fin 3510)) := i242Q.originalSubgroup

theorem i242_chain :
    rawChainOK 3510 (i242S.extract 0 8) i242S (i242Base.map Fin.val).toArray
        (wordsOf 8 omegaWords) 4 = true ∧
      rawOrbitSizes 3510 i242S (i242Base.map Fin.val).toArray = [120, 63, 30, 12, 8, 4, 2] := by
  have h := Certificates.certificate13506
  simp only [i242ChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem i242_card_Y : Nat.card i242Y = 174182400 := by
  rw [i242Y, i242Q, ofArrays_card (by norm_num) i242_chain.1, i242_chain.2]
  rfl

@[expose] noncomputable def i242y (r : ℕ) : Equiv.Perm (Fin 3510) := permOfArr 3510 (i242YArr r)

theorem i242S_getElem! {r : ℕ} (hr : r < 8) : i242S[r]! = i242YArr r := by
  rw [i242S, pushWords_getElem! _ _ (by simp [i242YArrs]; omega)]
  rw [i242YArrs, getElem!_pos _ r (by simpa using hr), Array.getElem_map]
  simp

theorem i242_rep_y {r : ℕ} (hr : r < 8) :
    Rep 3510 (i242YArr r) (i242y r) := by
  have h := rep_permOfArr_of_chainOK i242_chain.1 (by rw [i242S_size]; omega : r < i242S.size)
  rwa [i242S_getElem! hr] at h

theorem i242Y_eq : i242Y = Subgroup.closure {g | ∃ i < 8, i242y i = g} := by
  rw [i242Y, i242Q, ofArrays_originalSubgroup]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [i242y, i242S_getElem! hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [i242y, i242S_getElem! hi]⟩

theorem i242y_mem_Y {r : ℕ} (hr : r < 8) : i242y r ∈ i242Y := by
  rw [i242Y_eq]
  exact Subgroup.subset_closure ⟨r, hr, rfl⟩

@[expose] def i242J : Subgroup (Equiv.Perm (Fin 3510)) := ⨆ i : Fin 6, fi22FiveD i

theorem i242DGens_size : i242DGens.size = 12 := by simp [i242DGens]

theorem i242DGens_getElem! {j : ℕ} (hj : j < 12) :
    i242DGens[j]! = (fi22FiveDGenArrs (j / 2))[j % 2]! := by
  rw [i242DGens, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem i242y_mem_J
    {r : ℕ}
    (hr : r < 8) : i242y r ∈ i242J := by
  have hS : ∀ j < i242DGens.size, Rep 3510 i242DGens[j]! (permOfArr 3510 i242DGens[j]!) ∧
      Rep 3510 (rawInvs 3510 i242DGens)[j]! (permOfArr 3510 i242DGens[j]!)⁻¹ ∧
      permOfArr 3510 i242DGens[j]! ∈ i242J := by
    intro j hj
    rw [i242DGens_size] at hj
    rw [getElem!_rawInvs' (by rw [i242DGens_size]; exact hj), i242DGens_getElem! hj]
    have hi : j / 2 < 6 := by omega
    have hl : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hv := valid_dgen ⟨j / 2, hi⟩ hl
    refine ⟨rep_of_validA hv, rep_inv_of_validA hv, ?_⟩
    refine le_iSup (fun i : Fin 6 => fi22FiveD i) ⟨j / 2, hi⟩ ?_
    rw [fi22FiveD_eq]
    exact Subgroup.subset_closure (mem_permsA (by rw [fi22FiveDGenArrs_size]; exact hl))
  obtain ⟨g, hg, hrep⟩ := wordA_mem' hS (i242Words.getD r [])
    (by rw [i242DGens_size]; exact (i242_action_facts.1 r hr))
  have : i242y r = g := (i242_rep_y hr).unique hrep
  rw [this]
  exact hg

theorem i242Y_le_J :
    i242Y ≤ i242J := by
  rw [i242Y_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact i242y_mem_J hi

theorem i242Sig_val (v : Fin 120) :
    ((i242Sig v : Fin 3510) : ℕ) = i242Sigma.getD v 0 :=
  Nat.mod_eq_of_lt (i242_action_facts.2.1 v v.2).1

theorem i242Sig_injective : Function.Injective i242Sig := by
  intro v w h
  have hv := (i242_action_facts.2.1 v v.2).2
  have hw := (i242_action_facts.2.1 w w.2).2
  have h' : i242Sigma.getD v 0 = i242Sigma.getD w 0 := by
    rw [← i242Sig_val v, ← i242Sig_val w, h]
  rw [h'] at hv
  exact Fin.ext (hv.symm.trans hw)

theorem i242_mem_range_iff (p : Fin 3510) :
    (∃ v, i242Sig v = p) ↔ i242SigmaInv[(p : ℕ)]! < 120 := by
  constructor
  · rintro ⟨v, rfl⟩
    rw [i242Sig_val v, (i242_action_facts.2.1 v v.2).2]
    exact v.2
  · intro h
    have hp := (i242_action_facts.2.2.1 p p.2).2
    rcases hp with hp | hp
    · omega
    · refine ⟨⟨i242SigmaInv[(p : ℕ)]!, h⟩, Fin.ext ?_⟩
      rw [i242Sig_val]
      exact hp

set_option maxRecDepth 100000 in
theorem i242y_mem_stab {r : ℕ}
    (hr : r < 8) : i242y r ∈ i242Stab i242Sig := by
  intro p
  have h := (i242_action_facts.2.2.2 r hr).2 p p.2
  have e : (i242YArr r)[(p : ℕ)]! = ((i242y r p : Fin 3510) : ℕ) := (i242_rep_y hr).apply p.2
  rw [e] at h
  exact (i242_mem_range_iff p).trans (h.symm.trans (i242_mem_range_iff (i242y r p)).symm)

theorem i242Y_le_stab :
    i242Y ≤ i242Stab i242Sig := by
  rw [i242Y_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact i242y_mem_stab hi

@[expose] noncomputable def i242RhoY :
    i242Y →* Equiv.Perm (Fin 120) :=
  (i242Res i242Sig_injective).comp (Subgroup.inclusion i242Y_le_stab)

theorem i242RhoY_spec
    (g : i242Y) (v : Fin 120) :
    i242Sig (i242RhoY g v) = (g : Equiv.Perm (Fin 3510)) (i242Sig v) :=
  i242Res_spec i242Sig_injective _ v

set_option maxRecDepth 100000 in
theorem i242RhoY_y
    {r : ℕ} (hr : r < 8) :
    i242RhoY ⟨i242y r, i242y_mem_Y hr⟩ = gen1 r := by
  refine Equiv.ext fun v => i242Sig_injective ?_
  rw [i242RhoY_spec]
  show i242y r (i242Sig v) = i242Sig (gen1 r v)
  apply Fin.ext
  have h1 := (i242_rep_y hr).apply (i242Sig v).2
  rw [← h1, i242Sig_val, i242Sig_val]
  have h2 := (rep_gen1 hr).apply v.2
  rw [← h2, copy0Arr_getElem! _ v.2]
  exact (i242_action_facts.2.2.2 r hr).1 v v.2

theorem i242RhoY_range :
    (i242RhoY).range = omega1T := by
  have hle : omega1T ≤ i242RhoY.range := by
    rw [omega1T_eq, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨⟨i242y i, i242y_mem_Y hi⟩, i242RhoY_y hi⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_omega1T, ← i242_card_Y]
  exact Nat.card_le_card_of_surjective _ i242RhoY.rangeRestrict_surjective

theorem i242RhoY_bijective :
    Function.Bijective (i242RhoY).rangeRestrict :=
  i242RhoY.rangeRestrict_surjective.bijective_of_nat_card_le (by
    rw [i242RhoY_range, card_omega1T, i242_card_Y])

@[expose] noncomputable def i242YEquiv :
    i242Y ≃* omega1T :=
  (MulEquiv.ofBijective i242RhoY.rangeRestrict i242RhoY_bijective).trans
    (MulEquiv.subgroupCongr i242RhoY_range)

theorem i242_exists_Y :
    ∃ Y : Subgroup (Equiv.Perm (Fin 3510)), Y ≤ ⨆ i : Fin 6, fi22FiveD i ∧
      Nonempty (Y ≃* omegaT) :=
  ⟨i242Y, i242Y_le_J, ⟨i242YEquiv.trans omegaRestrictEquiv.symm⟩⟩

end CFSG.HardMathSupport.Solomon.Coordinator

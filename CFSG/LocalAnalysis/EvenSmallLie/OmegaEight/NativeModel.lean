module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModelBase

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheck

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover

section Arrays

variable {n : ℕ}

end Arrays

section Chains

variable {n : ℕ} {hn : 1 ≤ n} {S : Array (Array ℕ)} {k : ℕ} {hk : k ≤ S.size}
  {base : List (Fin n)} {hb : base.Nodup} {W : Array (List ℤ)}

end Chains

theorem omegaChain_ok :
    rawChainOK 360 (omegaS.extract 0 8) omegaS (omegaBase.map Fin.val).toArray
        (wordsOf 8 omegaWords) 4 = true ∧
      rawOrbitSizes 360 omegaS (omegaBase.map Fin.val).toArray = [120, 63, 30, 12, 8, 4, 2] := by
  have h := omegaChain_check
  simp only [omegaChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem autChain_ok :
    rawChainOK 360 (autS.extract 0 10) autS (autBase.map Fin.val).toArray
        (wordsOf 10 autWords) 4 = true ∧
      rawOrbitSizes 360 autS (autBase.map Fin.val).toArray = [360, 63, 30, 12, 8, 4, 4] := by
  have h := autChain_check
  simp only [autChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem omega1Chain_ok :
    rawChainOK 120 (omega1S.extract 0 8) omega1S (omega1Base.map Fin.val).toArray
        (wordsOf 8 omegaWords) 4 = true ∧
      rawOrbitSizes 120 omega1S (omega1Base.map Fin.val).toArray =
        [120, 63, 30, 12, 8, 4, 2] := by
  have h := omega1Chain_check
  simp only [omega1ChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem sylowChain_ok :
    rawChainOK 360 (sylowS.extract 0 5) sylowS (sylowBase.map Fin.val).toArray
        (wordsOf 5 sylowWords) 4 = true ∧
      rawOrbitSizes 360 sylowS (sylowBase.map Fin.val).toArray = [64, 2, 8, 4, 2] := by
  have h := sylowChain_check
  simp only [sylowChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem card_omegaT : Nat.card omegaT = 174182400 := by
  rw [omegaT, omegaQ, ofArrays_card (by norm_num) omegaChain_ok.1, omegaChain_ok.2]
  rfl

theorem card_autT : Nat.card autT = 1045094400 := by
  rw [autT, autQ, ofArrays_card (by norm_num) autChain_ok.1, autChain_ok.2]
  rfl

theorem card_omega1T : Nat.card omega1T = 174182400 := by
  rw [omega1T, omega1Q, ofArrays_card (by norm_num) omega1Chain_ok.1, omega1Chain_ok.2]
  rfl

theorem card_sylowT : Nat.card sylowT = 8192 := by
  rw [sylowT, sylowQ, ofArrays_card (by norm_num) sylowChain_ok.1, sylowChain_ok.2]
  rfl

theorem rep_gen
    {i : ℕ} (hi : i < 10) : Rep 360 genArrs[i]! (gen i) := by
  have h := (chain_strong_spec (hn := by norm_num) (hk := by rw [autS_size]; norm_num)
    (hb := by decide) autChain_ok.1 i (by rw [autS_size]; omega)).1
  rwa [autS_getElem! hi] at h

theorem rep_gen_inv
    {i : ℕ} (hi : i < 10) : Rep 360 (invCand 360 genArrs[i]!) (gen i)⁻¹ := by
  have h := (chain_strong_spec (hn := by norm_num) (hk := by rw [autS_size]; norm_num)
    (hb := by decide) autChain_ok.1 i (by rw [autS_size]; omega)).2.1
  rwa [getElem!_rawInvs' (by rw [autS_size]; omega), autS_getElem! hi] at h

theorem structure_ok : (∀ i < 8,
    (eqA 360 (conjArr genArrs[8]! genArrs[i]!) genArrs[rhoPerm.getD i 0]! = true ∧
      eqA 360 (conjArr genArrs[9]! genArrs[i]!) genArrs[tauPerm.getD i 0]! = true ∧
      ∀ p < 360, (p < 120 ↔ (genArrs[i]!)[p]! < 120))) ∧
    ∀ p < 360, (genArrs[8]!)[p]! = (p + 120) % 360 := by
  have h := structure_check
  simp only [structureCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_decide] at h
  exact ⟨fun i hi => ⟨(h.1 i hi).1.1, (h.1 i hi).1.2, (h.1 i hi).2⟩, h.2⟩

theorem conj_gen_rho {i : ℕ} (hi : i < 8) :
    gen 8 * gen i * (gen 8)⁻¹ = gen (rhoPerm.getD i 0) :=
  eq_of_eqA (rep_conjArr (rep_gen (by norm_num)) (rep_gen_inv (by norm_num))
    (rep_gen (by omega))) (rep_gen (by have := rhoPerm_lt hi; omega)) (structure_ok.1 i hi).1

theorem conj_gen_tau {i : ℕ} (hi : i < 8) :
    gen 9 * gen i * (gen 9)⁻¹ = gen (tauPerm.getD i 0) :=
  eq_of_eqA (rep_conjArr (rep_gen (by norm_num)) (rep_gen_inv (by norm_num))
    (rep_gen (by omega))) (rep_gen (by have := tauPerm_lt hi; omega)) (structure_ok.1 i hi).2.1

theorem conj_mem_omegaT_of_gen
    {a : Equiv.Perm (Fin 360)} (ha : a = gen 8 ∨ a = gen 9)
    {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT) : a * g * a⁻¹ ∈ omegaT := by
  have hle : omegaT ≤ omegaT.comap (MulAut.conj a).toMonoidHom := by
    calc omegaT = Subgroup.closure {g | ∃ i < 8, gen i = g} := omegaT_eq
      _ ≤ _ := by
        rw [Subgroup.closure_le]
        rintro _ ⟨i, hi, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rcases ha with rfl | rfl
        · rw [conj_gen_rho hi]
          exact gen_mem_omegaT (rhoPerm_lt hi)
        · rw [conj_gen_tau hi]
          exact gen_mem_omegaT (tauPerm_lt hi)
  have := hle hg
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem autT_le_normalizer
    : autT ≤ Subgroup.normalizer (omegaT : Set (Equiv.Perm (Fin 360))) := by
  rw [autT_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  by_cases h8 : i < 8
  · exact Subgroup.le_normalizer (gen_mem_omegaT h8)
  · refine mem_normalizer_of_conj_mem fun g hg => conj_mem_omegaT_of_gen ?_ hg
    by_cases h9 : i = 8
    · exact Or.inl (by rw [h9])
    · exact Or.inr (by rw [show i = 9 by omega])

theorem conj_mem_omegaT {a : Equiv.Perm (Fin 360)} (ha : a ∈ autT)
    {g : Equiv.Perm (Fin 360)} : g ∈ omegaT ↔ a * g * a⁻¹ ∈ omegaT :=
  Subgroup.mem_normalizer_iff.1 (autT_le_normalizer ha) g

theorem gen_mem_stab0 {i : ℕ} (hi : i < 8) : gen i ∈ stab0 := by
  intro p
  rw [← (rep_gen (by omega : i < 10)).apply p.2]
  exact (structure_ok.1 i hi).2.2 p p.2

theorem omegaT_le_stab0 : omegaT ≤ stab0 := by
  rw [omegaT_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact gen_mem_stab0 hi

@[expose] def omegaRes : omegaT →* Equiv.Perm (Fin 120) :=
  res0.comp (Subgroup.inclusion omegaT_le_stab0)

theorem rep_gen1
    {i : ℕ} (hi : i < 8) : Rep 120 (copy0Arr genArrs[i]!) (gen1 i) := by
  have h := (chain_strong_spec (hn := by norm_num) (hk := by rw [omega1S_size]; norm_num)
    (hb := by decide) omega1Chain_ok.1 i (by rw [omega1S_size]; omega)).1
  rwa [omega1S_getElem! hi] at h

theorem sgen_spec {j : ℕ} (hj : j < 17) :
    Rep 360 omegaS[j]! (sgen j) ∧ Rep 360 (rawInvs 360 omegaS)[j]! (sgen j)⁻¹ ∧
      sgen j ∈ omegaT :=
  chain_strong_spec (hn := by norm_num) (hk := by rw [omegaS_size]; norm_num) (hb := by decide)
    omegaChain_ok.1 j (by rw [omegaS_size]; exact hj)

theorem stab_ok
    : (∀ j ∈ stabIdx, j < omegaS.size ∧ (omegaS[j]!)[0]! = 0) ∧
    ∀ p < 359, ∃ j ∈ stabIdx, (omegaS[j]!)[p + 1]! ≠ p + 1 := by
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
    {p : Fin 360} (hp : p ≠ 0) : ∃ j ∈ stabIdx, sgen j p ≠ p := by
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
    {a : Equiv.Perm (Fin 360)} (ha : ∀ g ∈ omegaT, g * a = a * g)
    {c : Equiv.Perm (Fin 360)} (hc : c ∈ autT) : a (c 0) = c 0 := by
  by_contra hne
  have hp : c⁻¹ (a (c 0)) ≠ 0 := fun h => hne (by simpa using congrArg c h)
  obtain ⟨j, hj, hmove⟩ := exists_sgen_moves hp
  have hjs := (stab_ok.1 j hj).1
  rw [omegaS_size] at hjs
  have hmem : c * sgen j * c⁻¹ ∈ omegaT := (conj_mem_omegaT hc).1 (sgen_spec hjs).2.2
  have hcomm := congrArg (fun f : Equiv.Perm (Fin 360) => f (c 0)) (ha _ hmem)
  simp only [Equiv.Perm.mul_apply] at hcomm
  rw [show c⁻¹ (c 0) = 0 by simp, sgen_fix_zero hj] at hcomm
  apply hmove
  apply c.injective
  have e : c (c⁻¹ (a (c 0))) = a (c 0) := by simp
  rw [e]
  exact hcomm

theorem tree_ok : treeLit.2.2[0]! = 0 ∧ ∀ i < 119,
    treeLit.1[i + 1]! < 120 ∧ treeLit.2.1[i + 1]! < 8 ∧
      treeLit.2.2[treeLit.1[i + 1]!]! < treeLit.2.2[i + 1]! ∧
      (genArrs[treeLit.2.1[i + 1]!]!)[treeLit.1[i + 1]!]! = i + 1 := by
  have h := tree_check
  simp only [treeLitCheck, treeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact ⟨h.1, fun i hi => ⟨(h.2 i hi).1.1.1, (h.2 i hi).1.1.2, (h.2 i hi).1.2, (h.2 i hi).2⟩⟩

theorem exists_omegaT_apply_zero
    {x : Fin 360} (hx : (x : ℕ) < 120) : ∃ g ∈ omegaT, g 0 = x := by
  obtain ⟨-, hstep⟩ := tree_ok
  suffices H : ∀ d, ∀ y : ℕ, y < 120 → treeLit.2.2[y]! = d →
      ∃ g ∈ omegaT, ((g 0 : Fin 360) : ℕ) = y by
    obtain ⟨g, hg, e⟩ := H _ x hx rfl
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

theorem gen8_val
    (q : Fin 360) : ((gen 8 q : Fin 360) : ℕ) = (q + 120) % 360 := by
  rw [← rep_gen (by norm_num) q]
  exact structure_ok.2 q q.2

theorem centralizer_omegaT
    : Subgroup.centralizer (omegaT : Set (Equiv.Perm (Fin 360))) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_centralizer_iff] at ha
  rw [Subgroup.mem_bot]
  refine Equiv.ext fun p => ?_
  obtain ⟨c, hc, x, hx, rfl⟩ : ∃ c ∈ autT, ∃ x : Fin 360, (x : ℕ) < 120 ∧ c x = p := by
    have h8 := gen_mem_autT (by norm_num : 8 < 10)
    by_cases h1 : (p : ℕ) < 120
    · exact ⟨1, autT.one_mem, p, h1, rfl⟩
    by_cases h2 : (p : ℕ) < 240
    · refine ⟨gen 8, h8, ⟨p - 120, by omega⟩, by simp; omega, Fin.ext ?_⟩
      rw [gen8_val]
      simp only
      omega
    · refine ⟨gen 8 * gen 8, autT.mul_mem h8 h8, ⟨p - 240, by omega⟩, by simp; omega,
        Fin.ext ?_⟩
      rw [Equiv.Perm.mul_apply, gen8_val, gen8_val]
      simp only
      have := p.2
      omega
  obtain ⟨g, hg, hgx⟩ := exists_omegaT_apply_zero hx
  have hg' : c * g * c⁻¹ ∈ omegaT := (conj_mem_omegaT hc).1 hg
  have hfix : a (c 0) = c 0 := fix_of_comm ha hc
  have key : a ((c * g * c⁻¹) (c 0)) = (c * g * c⁻¹) (c 0) := by
    have h := congrArg (fun f : Equiv.Perm (Fin 360) => f (c 0)) (ha _ hg')
    simp only [Equiv.Perm.mul_apply] at h ⊢
    rw [hfix] at h
    exact h.symm
  have e1 : (c * g * c⁻¹) (c 0) = c x := by simp [hgx]
  rw [e1] at key
  rw [Equiv.Perm.one_apply]
  exact key

@[expose] def autConj : autT →* MulAut omegaT :=
  (Subgroup.normalizerMonoidHom omegaT).comp (Subgroup.inclusion autT_le_normalizer)

theorem omegaRes_apply_val (g : omegaT) (j : Fin 120) :
    ((omegaRes g j : Fin 120) : ℕ) = ((g : Equiv.Perm (Fin 360)) ⟨j, by omega⟩ : ℕ) := rfl

theorem omegaRes_gen {i : ℕ} (hi : i < 8) :
    omegaRes ⟨gen i, gen_mem_omegaT hi⟩ = gen1 i := by
  ext j
  rw [omegaRes_apply_val, ← (rep_gen1 hi).apply j.2, copy0Arr_getElem! _ j.2]
  exact ((rep_gen (by omega : i < 10)).apply (by omega : (j : ℕ) < 360)).symm

theorem omega1T_le_range : omega1T ≤ omegaRes.range := by
  rw [omega1T_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨⟨gen i, gen_mem_omegaT hi⟩, omegaRes_gen hi⟩

theorem omegaRes_range : omegaRes.range = omega1T := by
  refine (Subgroup.eq_of_le_of_card_ge omega1T_le_range ?_).symm
  rw [card_omega1T, ← card_omegaT]
  exact Nat.card_le_card_of_surjective _ omegaRes.rangeRestrict_surjective

theorem omegaRes_rangeRestrict_bijective
    : Function.Bijective omegaRes.rangeRestrict :=
  omegaRes.rangeRestrict_surjective.bijective_of_nat_card_le (by
    rw [omegaRes_range, card_omega1T, card_omegaT])

@[expose] def omegaRestrictEquiv : omegaT ≃* omega1T :=
  (MulEquiv.ofBijective omegaRes.rangeRestrict omegaRes_rangeRestrict_bijective).trans
    (MulEquiv.subgroupCongr omegaRes_range)

theorem omegaRestrictEquiv_apply (g : omegaT) :
    (omegaRestrictEquiv g : Equiv.Perm (Fin 120)) = omegaRes g := rfl

theorem omegaRes_injective
    : Function.Injective omegaRes := fun _ _ h =>
  omegaRes_rangeRestrict_bijective.1 (Subtype.ext h)

theorem autConj_apply (a : autT) (g : omegaT) :
    ((autConj a g : omegaT) : Equiv.Perm (Fin 360)) = a * g * (a : Equiv.Perm (Fin 360))⁻¹ :=
  rfl

theorem autConj_injective : Function.Injective autConj := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have hc : (a : Equiv.Perm (Fin 360)) ∈
      Subgroup.centralizer (omegaT : Set (Equiv.Perm (Fin 360))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := congrArg (fun α : MulAut omegaT => ((α ⟨h, hh⟩ : omegaT) : Equiv.Perm (Fin 360)))
      (MonoidHom.mem_ker.1 ha)
    simp only [autConj_apply, MulAut.one_apply] at h1
    calc h * a = a * h * (a : Equiv.Perm (Fin 360))⁻¹ * a := by rw [h1]
      _ = a * h := by group
  rw [centralizer_omegaT, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.2 (Subtype.ext hc)

theorem map_autConj_omegaT :
    (omegaT.subgroupOf autT).map autConj = (MulAut.conj : omegaT →* MulAut omegaT).range := by
  ext α
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hr
    refine ⟨⟨r, hr⟩, MulEquiv.ext fun g => Subtype.ext ?_⟩
    rw [autConj_apply, MulAut.conj_apply]
    rfl
  · rintro ⟨p, rfl⟩
    refine ⟨⟨p, omegaT_le_autT p.2⟩, by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact p.2,
      ?_⟩
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [autConj_apply, MulAut.conj_apply]
    rfl

theorem card_autT_eq : Nat.card autT = 6 * Nat.card omegaT := by
  rw [card_autT, card_omegaT]

end CFSG.EvenSmallLie.OmegaEight

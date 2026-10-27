module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.PolyIndep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E6Rep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverTwRank

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

theorem orbit_card_one_or_two : ∀ a : Fin TwistTag.E6.foldedTag.rank,
    (TwistTag.E6.orbit a).card = 1 ∨ (TwistTag.E6.orbit a).card = 2 := by decide

theorem orbit_one_data : ∀ a : Fin TwistTag.E6.foldedTag.rank, (TwistTag.E6.orbit a).card = 1 →
    TwistTag.E6.orbit a = {TwistTag.E6.orbitMin a} := by decide

theorem orbit_two_data : ∀ a : Fin TwistTag.E6.foldedTag.rank, (TwistTag.E6.orbit a).card = 2 →
    TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a ∧
      TwistTag.E6.orbit a = {TwistTag.E6.orbitMin a, TwistTag.E6.perm (TwistTag.E6.orbitMin a)} := by
  decide

theorem mem_orbit_orbitIndex' : ∀ i : Fin TwistTag.E6.tag.rank,
    i ∈ TwistTag.E6.orbit (TwistTag.E6.orbitIndex i) := by decide

@[expose] def twMoves (b : ℕ) : List ℕ :=
  (List.finRange 6).filterMap (fun i => if e6Data.wt b i = -1 then some (e6Data.weyl b i) else none) ++
  (List.finRange 4).map (fun a =>
    (TwistTag.E6.orbitWord a).foldr (fun i b => e6Data.weyl b i) b)

@[expose] def twStep (S : List ℕ) : List ℕ := (S ++ S.flatMap twMoves).eraseDups

@[expose] def twIter : ℕ → List ℕ
  | 0 => [0]
  | N + 1 => twStep (twIter N)

@[expose] def twReachCheck (N : ℕ) : Bool :=
  (List.range e6Data.d).all fun a => decide (a ∈ twIter N)

theorem tw_reach : twReachCheck 20 = true := by decide +kernel

theorem mem_twMoves {b b' : ℕ} (h : b' ∈ twMoves b) :
    (∃ i : Fin Tag.E6.rank, e6Data.wt b i = -1 ∧ b' = e6Data.weyl b i) ∨
      ∃ a : Fin TwistTag.E6.foldedTag.rank,
        (TwistTag.E6.orbitWord a).foldr (fun i b => e6Data.weyl b i) b = b' := by
  unfold twMoves at h
  rw [List.mem_append] at h
  rcases h with h | h
  · left
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 h
    by_cases hw : e6Data.wt b i = -1
    · rw [if_pos hw] at hi
      exact ⟨i, hw, (Option.some.inj hi).symm⟩
    · rw [if_neg hw] at hi
      exact absurd hi (by simp)
  · right
    obtain ⟨a, -, ha⟩ := List.mem_map.1 h
    exact ⟨a, ha⟩

section Facts

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e6_y_wt (i : Fin TwistTag.E6.tag.rank) :
    e6Data.wt (↑(⟨0, by decide⟩ : Fin e6Data.d)) i = if i = e6n0 then 1 else 0 := e6_wt_zero i

theorem minRep_xm_e6Y (i : Fin TwistTag.E6.tag.rank) (c : K) :
    minRep e6Data_valid K (e6Data_valid.xm K (Pi.single i 1) c) (e6Y27 : Fin e6Data.d →₀ K) =
      e6Y27 := by
  rw [minRep_xm]
  have h := e6Data_valid.rootOp_single_apply (R := K) i ⟨0, by decide⟩
  have hw : e6Data.wt (↑(⟨0, by decide⟩ : Fin e6Data.d)) i ≠ -1 := by
    rw [e6_y_wt]; split_ifs <;> decide
  rw [if_neg hw] at h
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply]
  change _ + c • e6Data.rootOp K (Pi.single i 1) (Finsupp.single ⟨0, by decide⟩ 1) = _
  rw [h, smul_zero, add_zero]

theorem minRep_nm_e6Y {i : Fin TwistTag.E6.tag.rank} (hi : i ≠ e6n0) :
    minRep e6Data_valid K (e6Data_valid.nm K i) (e6Y27 : Fin e6Data.d →₀ K) = e6Y27 := by
  have hw : e6Data.wt (↑(⟨0, by decide⟩ : Fin e6Data.d)) i = 0 := by
    rw [e6_y_wt, if_neg hi]
  have h := minRep_nm_single e6Data_valid (K := K) i ⟨0, by decide⟩
  rw [if_neg (by rw [hw]; decide), e6Data_valid.sRefl_eq_self hw] at h
  exact h

theorem minRep_list_prod_fix {M : Type*} [Monoid M] (ρ : M →* Module.End K (Fin e6Data.d →₀ K))
    (y : Fin e6Data.d →₀ K) (l : List M) (h : ∀ x ∈ l, ρ x y = y) : ρ l.prod y = y := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons, map_mul, Module.End.mul_apply, ih (fun z hz => h z (List.mem_cons_of_mem _ hz)),
      h x List.mem_cons_self]

end Facts

section Rep

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

@[expose] def twRep27 :
    Representation K ↥(TwistedE6.fixedGroup K σ) (Fin e6Data.d →₀ K) :=
  pullRep e6Data_valid (TwistedE6.fixedGroup K σ).subtype

theorem twRep27_apply (g : ↥(TwistedE6.fixedGroup K σ)) :
    twRep27 σ g = minRep e6Data_valid K (g : ↥(e6Data_valid.minGroup K)) := rfl

variable (a : Fin TwistTag.E6.foldedTag.rank)

@[expose] def xkTerm (k : ℕ) (c : K) : ↥(e6Data_valid.minGroup K) :=
  e6Data_valid.xm K (Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) 1) ((σ ^ k) c)

theorem minOrbitHom_uSL_eq (c : orbitField TwistTag.E6 K σ a) :
    minOrbitHom σ a (uSL c) =
      ((List.range (TwistTag.E6.orbit a).card).map fun k => xkTerm σ a k (c : K)).prod :=
  minOrbitHom_uSL σ a c

theorem minRep_xkTerm (k : ℕ) (c : K) :
    minRep e6Data_valid K (xkTerm σ a k c) =
      1 + ((σ ^ k) c) • e6Data.rootOp K
        (Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) 1) :=
  minRep_xm e6Data_valid _ _

theorem minRep_uSL_card_one (ha : (TwistTag.E6.orbit a).card = 1) (c : orbitField TwistTag.E6 K σ a) :
    minRep e6Data_valid K (minOrbitHom σ a (uSL c)) = minRep e6Data_valid K (xkTerm σ a 0 c) := by
  rw [minOrbitHom_uSL_eq, ha]
  simp

theorem minRep_uSL_card_two (ha : (TwistTag.E6.orbit a).card = 2) (c : orbitField TwistTag.E6 K σ a) :
    minRep e6Data_valid K (minOrbitHom σ a (uSL c)) =
      minRep e6Data_valid K (xkTerm σ a 0 c) * minRep e6Data_valid K (xkTerm σ a 1 c) := by
  rw [minOrbitHom_uSL_eq, ha]
  simp [List.range_succ, map_mul]

theorem natCard_eq_q_sq_fintype (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∃ i : Fintype K, @Fintype.card K i = (2 ^ f) ^ 2 :=
  ⟨Fintype.ofFinite K, (@Nat.card_eq_fintype_card K (Fintype.ofFinite K)).symm.trans hK⟩

include hf hK hσ in
theorem rootOp_mem_of_stable (S : Submodule K (Fin e6Data.d →₀ K)) (v : Fin e6Data.d →₀ K)
    (hv : ∀ c : orbitField TwistTag.E6 K σ a, minRep e6Data_valid K (minOrbitHom σ a (uSL c)) v - v ∈ S)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ TwistTag.E6.orbit a) :
    e6Data.rootOp K (Pi.single i 1) v ∈ S := by
  rcases orbit_card_one_or_two a with ha | ha
  · have hi' : i = TwistTag.E6.orbitMin a := by
      have := orbit_one_data a ha
      rw [this, Finset.mem_singleton] at hi
      exact hi
    have h1 := hv 1
    rw [minRep_uSL_card_one σ a ha, minRep_xkTerm] at h1
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply] at h1
    rw [hi']
    simpa using h1
  · obtain ⟨hne, hset⟩ := orbit_two_data a ha
    obtain ⟨hfin, hcard⟩ := natCard_eq_q_sq_fintype hK
    have hq : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hmem : ∀ c : K, c ∈ orbitField TwistTag.E6 K σ a := fun c => by
      rw [mem_orbitField, ha]
      simp only [pow_two, RingHom.mul_def, RingHom.id_apply]
      exact sigma_sigma_eq hK σ hσ c
    have key := mem_of_forall_poly hq hcard S σ hσ
      (e6Data.rootOp K (Pi.single (TwistTag.E6.orbitMin a) 1) v)
      (e6Data.rootOp K (Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1) v)
      (e6Data.rootOp K (Pi.single (TwistTag.E6.orbitMin a) 1)
        (e6Data.rootOp K (Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1) v))
      (fun c => by
        have h1 := hv ⟨c, hmem c⟩
        rw [minRep_uSL_card_two σ a ha, minRep_xkTerm, minRep_xkTerm] at h1
        simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
          LinearMap.smul_apply, map_add, map_smul, pow_zero, pow_one, RingHom.coe_one,
          Equiv.Perm.coe_one, Equiv.Perm.one_apply, id_eq] at h1
        convert h1 using 1
        simp only [smul_add, add_smul, smul_smul]
        rw [mul_comm c (σ c)]
        abel)
    rw [hset] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact key.1
    · exact key.2.1

include hf hK hσ in
theorem rootOp_eq_zero_of_mem_fixU_tw {v : Fin e6Data.d →₀ K}
    (hv : v ∈ (twistedE6CoverData hf hK σ hσ).datum.fixU (twRep27 σ))
    (i : Fin TwistTag.E6.tag.rank) : e6Data.rootOp K (Pi.single i 1) v = 0 := by
  have hi := mem_orbit_orbitIndex' i
  have := rootOp_mem_of_stable hf hK σ hσ (TwistTag.E6.orbitIndex i) ⊥ v (fun c => by
    have h := ((twistedE6CoverData hf hK σ hσ).datum.mem_fixU _).1 hv
      (hatX hf hK σ hσ (TwistTag.E6.orbitIndex i) c)
      ((twistedE6CoverRankOne hf hK σ hσ).x_mem_lU (TwistTag.E6.orbitIndex i) c)
    have h' : minRep e6Data_valid K (minOrbitHom σ (TwistTag.E6.orbitIndex i) (uSL c)) v = v := h
    rw [h', sub_self]
    exact Submodule.zero_mem _) hi
  exact (Submodule.mem_bot K).1 this

include hf hK hσ in
theorem fixU_le_line_tw {v : Fin e6Data.d →₀ K}
    (hv : v ∈ (twistedE6CoverData hf hK σ hσ).datum.fixU (twRep27 σ)) :
    ∃ c : K, v = c • (e6Y27 : Fin e6Data.d →₀ K) :=
  ⟨v ⟨0, by decide⟩, eq_smul_of_rootOp_eq_zero e6Data_valid e6_dominant
    (fun i => rootOp_eq_zero_of_mem_fixU_tw hf hK σ hσ hv i)⟩

include hf hK hσ in
theorem e6Y27_mem_fixU_tw :
    (e6Y27 : Fin e6Data.d →₀ K) ∈ (twistedE6CoverData hf hK σ hσ).datum.fixU (twRep27 σ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (Fin e6Data.d →₀ K) := ⟨⟨e6Y27, 0, e6Y27_ne_zero⟩⟩
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1
    ((twistedE6CoverData hf hK σ hσ).datum.fixU_ne_bot (p := 2) (twRep27 σ))
  obtain ⟨c, rfl⟩ := fixU_le_line_tw hf hK σ hσ hx
  have hc : c ≠ 0 := by rintro rfl; exact hx0 (zero_smul _ _)
  have := Submodule.smul_mem _ c⁻¹ hx
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem foldr_sRefl_val (l : List (Fin Tag.E6.rank)) (b : Fin e6Data.d) :
    ((l.foldr (fun i b => e6Data_valid.sRefl i b) b : Fin e6Data.d) : ℕ) =
      l.foldr (fun i b => e6Data.weyl b i) (b : ℕ) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [e6Data_valid.sRefl_val, ih]

@[expose] def InSpan (S : Submodule K (Fin e6Data.d →₀ K)) (b : ℕ) : Prop :=
  ∃ h : b < e6Data.d, (Finsupp.single (⟨b, h⟩ : Fin e6Data.d) (1 : K)) ∈ S

include hf hK hσ in
theorem inSpan_moves (S : Submodule K (Fin e6Data.d →₀ K))
    (hS : ∀ g : ↥(TwistedE6.fixedGroup K σ), ∀ w ∈ S, twRep27 σ g w ∈ S) {b : ℕ}
    (hb : InSpan S b) : ∀ b' ∈ twMoves b, InSpan S b' := by
  obtain ⟨hbd, hvb⟩ := hb
  intro b' hb'
  rcases mem_twMoves hb' with ⟨i, hw, rfl⟩ | ⟨a, rfl⟩
  ·
    · have hroot := rootOp_mem_of_stable hf hK σ hσ (TwistTag.E6.orbitIndex i) S
        (Finsupp.single ⟨b, hbd⟩ 1) (fun c => by
          have := hS (hatX hf hK σ hσ (TwistTag.E6.orbitIndex i) c) _ hvb
          exact sub_mem this hvb) (mem_orbit_orbitIndex' i)
      rw [e6Data_valid.rootOp_single_apply i ⟨b, hbd⟩, if_pos hw] at hroot
      have hlt : e6Data.weyl b i < e6Data.d :=
        (e6Data_valid.sRefl_val i ⟨b, hbd⟩) ▸ (e6Data_valid.sRefl i ⟨b, hbd⟩).2
      refine ⟨hlt, ?_⟩
      have e : (⟨e6Data.weyl b i, hlt⟩ : Fin e6Data.d) = e6Data_valid.sRefl i ⟨b, hbd⟩ :=
        Fin.ext (e6Data_valid.sRefl_val i ⟨b, hbd⟩).symm
      rw [e]
      exact hroot
  ·
    obtain ⟨ε, hε, hε'⟩ := minRep_prod_nm_single e6Data_valid (K := K)
      ((TwistTag.E6.orbitWord a)) ⟨b, hbd⟩
    have hnh : twRep27 σ ((twistedE6CoverData hf hK σ hσ).nhat a) (Finsupp.single ⟨b, hbd⟩ 1) ∈ S :=
      hS _ _ hvb
    have hnc : twRep27 σ ((twistedE6CoverData hf hK σ hσ).nhat a) (Finsupp.single ⟨b, hbd⟩ 1) =
        ε • Finsupp.single ((TwistTag.E6.orbitWord a).foldr (fun i b => e6Data_valid.sRefl i b)
          ⟨b, hbd⟩) 1 := by
      rw [twRep27_apply, nhat_coe hf hK σ hσ a, minOrbitHom_WSL]
      exact hε'
    rw [hnc] at hnh
    have hε0 : ε ≠ 0 := by
      rintro rfl
      rcases hε with h | h <;> simp at h
    have hmem := Submodule.smul_mem S ε⁻¹ hnh
    rw [smul_smul, inv_mul_cancel₀ hε0, one_smul] at hmem
    have hlt : (TwistTag.E6.orbitWord a).foldr (fun i b => e6Data.weyl b i) b < e6Data.d :=
      (foldr_sRefl_val _ ⟨b, hbd⟩) ▸ (((TwistTag.E6.orbitWord a).foldr
        (fun i b => e6Data_valid.sRefl i b) ⟨b, hbd⟩)).2
    refine ⟨hlt, ?_⟩
    have e : (⟨(TwistTag.E6.orbitWord a).foldr (fun i b => e6Data.weyl b i) b, hlt⟩ :
        Fin e6Data.d) = (TwistTag.E6.orbitWord a).foldr (fun i b => e6Data_valid.sRefl i b)
          ⟨b, hbd⟩ := Fin.ext (foldr_sRefl_val _ ⟨b, hbd⟩).symm
    rw [e]
    exact hmem

include hf hK hσ in
theorem orbitSpan_twRep27 : orbitSpan (twRep27 σ) (e6Y27 : Fin e6Data.d →₀ K) = ⊤ := by
  set S := orbitSpan (twRep27 σ) (e6Y27 : Fin e6Data.d →₀ K) with hSdef
  have hS : ∀ g : ↥(TwistedE6.fixedGroup K σ), ∀ w ∈ S, twRep27 σ g w ∈ S :=
    fun g w hw => orbitSpan_stable (twRep27 σ) _ g hw
  have hiter : ∀ N, ∀ b ∈ twIter N, InSpan S b := by
    intro N
    induction N with
    | zero =>
      intro b hb
      simp only [twIter, List.mem_singleton] at hb
      subst hb
      exact ⟨by decide, mem_orbitSpan_self (twRep27 σ) _⟩
    | succ N ih =>
      intro b hb
      simp only [twIter, twStep, List.mem_eraseDups, List.mem_append, List.mem_flatMap] at hb
      rcases hb with hb | ⟨b₀, hb₀, hb⟩
      · exact ih b hb
      · exact inSpan_moves hf hK σ hσ S hS (ih b₀ hb₀) b hb
  refine (Submodule.eq_top_iff').2 fun v => ?_
  induction v using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add f g hf hg => exact add_mem hf hg
  | single b c =>
    have hb : (b : ℕ) ∈ twIter 20 := by
      have := tw_reach
      simp only [twReachCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at this
      exact this b b.2
    obtain ⟨hlt, hmem⟩ := hiter 20 b hb
    have := Submodule.smul_mem S c hmem
    rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at this

include hf hK hσ in
theorem isSimpleRep_twRep27 : IsSimpleRep (twRep27 σ) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (Fin e6Data.d →₀ K) := ⟨⟨e6Y27, 0, e6Y27_ne_zero⟩⟩
  (twistedE6CoverData hf hK σ hσ).datum.isSimpleRep_of_fixU (p := 2) (twRep27 σ)
    (y := (e6Y27 : Fin e6Data.d →₀ K)) (fun _ hx => fixU_le_line_tw hf hK σ hσ hx)
    (orbitSpan_twRep27 hf hK σ hσ)

@[expose] abbrev twA0 : Fin TwistTag.E6.foldedTag.rank := ⟨0, by decide⟩

theorem orbitIndex_e6n0 : TwistTag.E6.orbitIndex e6n0 = twA0 := by decide

theorem orbit_twA0_data : TwistTag.E6.orbitMin twA0 = e6n0 ∧
    TwistTag.E6.perm e6n0 = (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) ∧
    (TwistTag.E6.orbit twA0).card = 2 := by decide

theorem e6_wt_node5 : e6Data.wt (↑(⟨0, by decide⟩ : Fin e6Data.d))
    (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) = 0 := by decide

@[expose] def hkTerm (k : ℕ) (u : (orbitField TwistTag.E6 K σ a)ˣ) : ↥(e6Data_valid.minGroup K) :=
  e6Data_valid.hm K ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a))
    (Units.map ((σ ^ k).comp (orbitField TwistTag.E6 K σ a).subtype).toMonoidHom u)

theorem minOrbitHom_HSL_eq (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    minOrbitHom σ a (HSL u) =
      ((List.range (TwistTag.E6.orbit a).card).map fun k => hkTerm σ a k u).prod :=
  minOrbitHom_HSL σ a u

theorem perm_pow_ne_e6n0 (ha : a ≠ twA0) (k : ℕ) :
    (TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a) ≠ e6n0 := by
  intro h
  have hmem := TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a) k
  have hmem' := (TwistTag.mem_orbit_iff TwistTag.E6).1 hmem
  rw [h, orbitIndex_e6n0] at hmem'
  exact ha hmem'.symm

theorem minRep_Psi_uSL_fix (c : orbitField TwistTag.E6 K σ a) :
    minRep e6Data_valid K (minOrbitHom σ a (uSL c)) (e6Y27 : Fin e6Data.d →₀ K) = e6Y27 := by
  rw [minOrbitHom_uSL_eq]
  refine minRep_list_prod_fix (minRep e6Data_valid K) e6Y27 _ ?_
  intro x hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  exact minRep_xm_e6Y _ _

theorem minRep_Psi_WSL_fix (ha : a ≠ twA0) :
    minRep e6Data_valid K (minOrbitHom σ a WSL) (e6Y27 : Fin e6Data.d →₀ K) = e6Y27 := by
  rw [minOrbitHom_WSL]
  refine minRep_list_prod_fix (minRep e6Data_valid K) e6Y27 _ ?_
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  have hmem := (TwistTag.mem_orbitWord (t := TwistTag.E6)).1 hi
  have hmem' := (TwistTag.mem_orbit_iff TwistTag.E6).1 hmem
  refine minRep_nm_e6Y (fun h => ha ?_)
  rw [← hmem', h, orbitIndex_e6n0]

theorem minRep_hkTerm_single (k : ℕ) (u : (orbitField TwistTag.E6 K σ a)ˣ) (b : Fin e6Data.d) :
    minRep e6Data_valid K (hkTerm σ a k u) (Finsupp.single b 1) =
      ((((Units.map ((σ ^ k).comp (orbitField TwistTag.E6 K σ a).subtype).toMonoidHom u) ^
        e6Data.wt (↑b) ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) : Kˣ)) : K) •
        Finsupp.single b 1 :=
  minRep_hm_single e6Data_valid _ _ _

set_option maxRecDepth 10000 in
theorem minRep_Psi_HSL_fix (ha : a ≠ twA0) (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    minRep e6Data_valid K (minOrbitHom σ a (HSL u)) (e6Y27 : Fin e6Data.d →₀ K) = e6Y27 := by
  rw [minOrbitHom_HSL_eq]
  refine minRep_list_prod_fix (minRep e6Data_valid K) e6Y27 _ ?_
  intro x hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  have h := minRep_hkTerm_single σ a k u ⟨0, by decide⟩
  have hw : e6Data.wt (↑(⟨0, by decide⟩ : Fin e6Data.d))
      ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) = 0 := by
    rw [e6_y_wt, if_neg (perm_pow_ne_e6n0 a ha k)]
  rw [hw, zpow_zero, Units.val_one, one_smul] at h
  unfold e6Y27
  exact h

include hf hK hσ in
theorem card_orbitField_even : (2 : ℕ) ∣ Nat.card (orbitField TwistTag.E6 K σ a) := by
  have h := card_orbitField_e6 hf hK σ hσ a
  rw [h]
  have hf0 : f ≠ 0 := by omega
  have hd : (TwistTag.E6.orbit a).card ≠ 0 := by
    rcases orbit_card_one_or_two a with h1 | h1 <;> omega
  exact dvd_pow (dvd_pow_self 2 hf0) hd

include hf hK hσ in
theorem twHecke_zero (ha : a ≠ twA0) :
    (twistedE6CoverData hf hK σ hσ).datum.heckeT (twRep27 σ) a (e6Y27 : Fin e6Data.d →₀ K) = 0 := by
  have : ∀ s, Fintype (orbitField TwistTag.E6 K σ s) := fun s => Fintype.ofFinite _
  rw [(twistedE6CoverRankOne hf hK σ hσ).heckeT_datum (twRep27 σ) a]
  have hterm : ∀ c : orbitField TwistTag.E6 K σ a,
      twRep27 σ (hatX hf hK σ hσ a c * (twistedE6CoverData hf hK σ hσ).nhat a)
        (e6Y27 : Fin e6Data.d →₀ K) = e6Y27 := by
    intro c
    rw [map_mul, Module.End.mul_apply]
    have h1 : twRep27 σ ((twistedE6CoverData hf hK σ hσ).nhat a) (e6Y27 : Fin e6Data.d →₀ K) =
        e6Y27 := by
      rw [twRep27_apply, nhat_coe hf hK σ hσ a]
      exact minRep_Psi_WSL_fix σ a ha
    have h2 : twRep27 σ (hatX hf hK σ hσ a c) (e6Y27 : Fin e6Data.d →₀ K) = e6Y27 :=
      minRep_Psi_uSL_fix σ a c
    rw [h1, h2]
  refine (Finset.sum_eq_card_nsmul (fun c _ => hterm c)).trans ?_
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K,
    (CharP.cast_eq_zero_iff K 2 _).2 (card_orbitField_even hf hK σ hσ a), zero_smul]

theorem minRep_Psi_HSL_a0 (u : (orbitField TwistTag.E6 K σ twA0)ˣ) :
    minRep e6Data_valid K (minOrbitHom σ twA0 (HSL u)) (e6Y27 : Fin e6Data.d →₀ K) =
      (((u : orbitField TwistTag.E6 K σ twA0) : K)) • e6Y27 := by
  rw [minOrbitHom_HSL_eq, orbit_twA0_data.2.2]
  have hprod : ((List.range 2).map fun k => hkTerm σ twA0 k u).prod =
      hkTerm σ twA0 0 u * hkTerm σ twA0 1 u := by
    simp [List.range_succ]
  rw [hprod, map_mul, Module.End.mul_apply]
  have h1 := minRep_hkTerm_single σ twA0 1 u ⟨0, by decide⟩
  have h0 := minRep_hkTerm_single σ twA0 0 u ⟨0, by decide⟩
  have hw1 : e6Data.wt (↑(⟨0, by decide⟩ : Fin e6Data.d))
      ((TwistTag.E6.perm ^ 1) (TwistTag.E6.orbitMin twA0)) = 0 := by
    rw [pow_one, orbit_twA0_data.1, orbit_twA0_data.2.1]
    exact e6_wt_node5
  have hw0 : e6Data.wt (↑(⟨0, by decide⟩ : Fin e6Data.d))
      ((TwistTag.E6.perm ^ 0) (TwistTag.E6.orbitMin twA0)) = 1 := by
    rw [e6_y_wt]
    simp [orbit_twA0_data.1]
  rw [hw1, zpow_zero, Units.val_one, one_smul] at h1
  rw [hw0, zpow_one] at h0
  unfold e6Y27
  rw [h1, h0]
  rfl

@[expose] def twChi27 (g : ↥(TwistedE6.fixedGroup K σ)) : K :=
  twRep27 σ g (e6Y27 : Fin e6Data.d →₀ K) ⟨0, by decide⟩

include hf hK hσ in
theorem twRep27_H (h : ↥(TwistedE6.fixedGroup K σ))
    (hh : h ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ)) :
    twRep27 σ h (e6Y27 : Fin e6Data.d →₀ K) = twChi27 σ h • e6Y27 := by
  obtain ⟨c, hc⟩ := fixU_le_line_tw hf hK σ hσ
    ((twistedE6CoverData hf hK σ hσ).datum.act_H_mem_fixU (twRep27 σ) hh
      (e6Y27_mem_fixU_tw hf hK σ hσ))
  have : twChi27 σ h = c := by
    unfold twChi27
    rw [hc]
    simp [e6Y27]
  rw [this, hc]

include hf hK hσ in
theorem twRep27_isCoverType :
    IsCoverType (twistedE6CoverRankOne hf hK σ hσ) (twRep27 σ) (e6Y27 : Fin e6Data.d →₀ K)
      (twChi27 σ) (Finset.univ.erase twA0) := by
  refine ⟨e6Y27_mem_fixU_tw hf hK σ hσ, e6Y27_ne_zero, twRep27_H hf hK σ hσ, fun s => ?_⟩
  by_cases hs : s = twA0
  · subst hs
    refine ⟨fun h => absurd rfl (Finset.mem_erase.1 h).1, fun h => ?_⟩
    exfalso
    obtain ⟨h1, -⟩ := h
    have hcard : 2 < Nat.card (orbitField TwistTag.E6 K σ twA0) := by
      rw [card_orbitField_e6 hf hK σ hσ, orbit_twA0_data.2.2]
      have hq : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      nlinarith
    have hu : Nontrivial (orbitField TwistTag.E6 K σ twA0)ˣ := by
      rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_units]
      omega
    obtain ⟨u, hu1⟩ := exists_ne (1 : (orbitField TwistTag.E6 K σ twA0)ˣ)
    have := h1 u
    change twChi27 σ (hatH hf hK σ hσ twA0 u) = 1 at this
    have hchi : twChi27 σ (hatH hf hK σ hσ twA0 u) = ((u : orbitField TwistTag.E6 K σ twA0) : K) := by
      unfold twChi27
      rw [twRep27_apply]
      change minRep e6Data_valid K (minOrbitHom σ twA0 (HSL u)) e6Y27 ⟨0, by decide⟩ = _
      rw [minRep_Psi_HSL_a0]
      simp [e6Y27]
    rw [hchi] at this
    exact hu1 (Units.ext (Subtype.ext (by simpa using this)))
  · refine ⟨fun _ => ⟨fun u => ?_, twHecke_zero hf hK σ hσ s hs⟩,
      fun _ => Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩⟩
    change twChi27 σ (hatH hf hK σ hσ s u) = 1
    unfold twChi27
    rw [twRep27_apply]
    change minRep e6Data_valid K (minOrbitHom σ s (HSL u)) e6Y27 ⟨0, by decide⟩ = 1
    rw [minRep_Psi_HSL_fix σ s hs u]
    simp [e6Y27]

end Rep

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

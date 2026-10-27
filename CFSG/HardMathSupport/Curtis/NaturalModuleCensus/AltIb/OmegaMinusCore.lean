module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusBlocks
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusLevi
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusAux
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusProps

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

open Matrix CFSG.Assembly.LowTwoRank CFSG.Open CFSG.AGLEmbedding.LieOut CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell
  (cnt StepCoord topN pCast_ne_zero card_GL_congr card_GL_eq_mul_card_SL
    perfect_eq_bot_of_card_le_one)

variable {r : ℕ} {F : Type} [Field F] {b c : F} {S : Finset ℕ}

section Blocks

@[expose] def BlockTy (r : ℕ) (F : Type) [Field F] (S : Finset ℕ) : Fin S.card ⊕ Unit → Type
  | Sum.inl ℓ => GL (StepCoord r S ℓ) F
  | Sum.inr _ => GL (Idx (topN r S)) F

noncomputable instance instGroupBlockTy {S : Finset ℕ} : ∀ i : Fin S.card ⊕ Unit,
    Group (BlockTy r F S i)
  | Sum.inl _ => inferInstanceAs (Group (GL _ F))
  | Sum.inr _ => inferInstanceAs (Group (GL _ F))

instance instFiniteBlockTy [Finite F] {S : Finset ℕ} :
    ∀ i : Fin S.card ⊕ Unit, Finite (BlockTy r F S i)
  | Sum.inl _ => inferInstanceAs (Finite (GL _ F))
  | Sum.inr _ => inferInstanceAs (Finite (GL _ F))

@[expose] noncomputable def blockHom (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) :
    ∀ i : Fin S.card ⊕ Unit, ↥(JΩ r F b c S) →* BlockTy r F S i
  | Sum.inl ℓ => stepHom hS ℓ.2
  | Sum.inr _ => topHomGL hS

@[expose] noncomputable def omFlagBlocks (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {p : ℕ}
    (hp0 : (p : F) ≠ 0) : FlagBlocks p ↥(JΩ r F b c S) :=
  { ι := Fin S.card ⊕ Unit
    H := BlockTy r F S
    grp := instGroupBlockTy
    ρ := blockHom hS
    inj_of_pow := fun g he hall => eq_one_of_blocks_trivial hS hp0 he
      (fun ℓ hℓ => hall (Sum.inl ⟨ℓ, hℓ⟩))
      (Subtype.ext (show topHomGL hS g = 1 from hall (Sum.inr ()))) }

end Blocks

section Orders

variable [Finite F]

theorem not_sq_dvd_card_step {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F)
    (hpq : ¬ p ∣ Nat.card F - 1) (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) [CharP F 2] (ℓ : ℕ)
    (hA1 : ∀ X : Subgroup (GL (Idx r) F), X ≤ JΩ r F b c S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X) :
    ¬ p ^ 2 ∣ Nat.card (GL (StepCoord r S ℓ) F) := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  rw [card_GL_congr (Fintype.equivFin (StepCoord r S ℓ))]
  set k := Fintype.card (StepCoord r S ℓ) with hk
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0]
    have : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    rw [Nat.card_of_subsingleton (1 : GL (Fin 0) F)]
    intro hd
    have := Nat.le_of_dvd one_pos hd
    rcases hp57 with rfl | rfl <;> omega
  · have : NeZero k := ⟨hpos.ne'⟩
    rw [card_GL_eq_mul_card_SL]
    intro hd
    have hcop : Nat.Coprime (p ^ 2) (Nat.card F - 1) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq)
    exact not_sq_dvd_card_SL_of_lift hp57 hK hA1 (stepLeviΩ S ℓ) (stepLeviΩ_injective S ℓ)
      (fun hk' A => stepLeviΩ_mem hS hk' A) (hcop.dvd_of_dvd_mul_left hd)

end Orders

section Nonsplit

variable [Finite F] [CharP F 2]

theorem false_of_nonsplit (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hSQ : OmegaMinusSmallQS)
    (hr : 3 ≤ r) {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F)
    (hpq : ¬ p ∣ Nat.card F - 1) (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r)
    (hA1 : ∀ X : Subgroup (GL (Idx r) F), X ≤ JΩ r F b c S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X)
    {x : GL (Idx r) F} (hxΩ : x ∈ Ωm r F b c) (hxp : x ^ p = 1)
    (hfix : ∀ g ∈ Ωm r F b c, g * x = x * g → g ∈ JΩ r F b c S)
    {V E : Subgroup (GL (Idx r) F)} (hVJ : V ≤ JΩ r F b c S)
    (hVx : V ≤ Subgroup.centralizer ({x} : Set (GL (Idx r) F))) (hV : ⁅V, V⁆ = V) (hEV : E ≤ V)
    (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) : False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp0 : (p : F) ≠ 0 := pCast_ne_zero hp hp2
  have hxJ : x ∈ JΩ r F b c S := hfix x hxΩ rfl
  set J := JΩ r F b c S with hJ
  let B : FlagBlocks p ↥J := omFlagBlocks hS hp0
  have hBfin : ∀ i, Finite (B.H i) := fun i => instFiniteBlockTy i
  have hE' : ∀ e ∈ E.subgroupOf J, e ^ p = 1 := fun e he => Subtype.ext (by
    have := hEel.2 _ (Subgroup.mem_subgroupOf.1 he)
    simpa using this)
  have hEc' : p ^ 2 ≤ Nat.card (E.subgroupOf J) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEV.trans hVJ)).toEquiv, hEc]
  have hxV : ∀ v ∈ V.subgroupOf J, v * (⟨x, hxJ⟩ : ↥J) = ⟨x, hxJ⟩ * v := by
    intro v hv
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.1 (hVx (Subgroup.mem_subgroupOf.1 hv)) x
      (Set.mem_singleton x)
    exact this.symm
  have hV' : ⁅V.subgroupOf J, V.subgroupOf J⁆ = V.subgroupOf J := commutator_subgroupOf_eq hVJ hV
  have hEV' : E.subgroupOf J ≤ V.subgroupOf J := fun e he =>
    Subgroup.mem_subgroupOf.2 (hEV (Subgroup.mem_subgroupOf.1 he))
  have hpg : ∀ {H : Type} [Group H] (ρ : ↥J →* H),
      ∀ y ∈ (E.subgroupOf J).map ρ, y ^ p = 1 := by
    intro H _ ρ y hy
    obtain ⟨e, he, rfl⟩ := hy
    rw [← map_pow, hE' e he, map_one]
  have hP : ∀ {H : Type} [Group H] (ρ : ↥J →* H),
      ⁅(V.subgroupOf J).map ρ, (V.subgroupOf J).map ρ⁆ = (V.subgroupOf J).map ρ := by
    intro H _ ρ
    rw [← Subgroup.map_commutator, hV']
  have hm : topN r S = 0 ∨ ¬ p ^ 2 ∣ Nat.card ↥(Ωm (topN r S) F b c) := by
    rcases Nat.eq_zero_or_pos (topN r S) with h0 | hpos
    · exact Or.inl h0
    · exact Or.inr (not_sq_dvd_card_top_of_lift hirr hSQ hpos hA1 (topLevi S)
        (topLevi_injective S) (fun A => topLevi_mem hS A))
  have hcyc_top : IsCyclic ↥((E.subgroupOf J).map (topHomGL hS)) :=
    isCyclic_of_perfect_top hp57 hK hm
      (P := (V.subgroupOf J).map (topHomGL hS))
      (by rintro _ ⟨g, -, rfl⟩; exact topHomGL_mem_orthGroup hS g)
      (hP (topHomGL hS)) (Subgroup.map_mono hEV') (isPGroup_of_pow_eq_one (hpg _))
  refine FlagBlocks.false_of_nonsplit' B hp (fun i => i = Sum.inr ()) (fun i j hi hj => hi.trans hj.symm)
    ?_ hV' hEV' hE' hEc' (x := ⟨x, hxJ⟩) (Subtype.ext (by simpa using hxp)) hxV
    (fun i hi => ?_) ?_
  · intro i hi
    rcases i with ℓ | u
    · exact not_sq_dvd_card_step hp57 hK hpq hS ℓ.1 hA1
    · exact absurd rfl hi
  · rcases i with ℓ | u
    · exact absurd hi (by simp)
    · exact hcyc_top
  · intro i hi hx1 hdvd
    rcases i with ℓ | u
    · by_cases hk2 : 2 ≤ Fintype.card (StepCoord r S ℓ.1)
      · exact false_of_step_escape hirr hr hS hpodd hxΩ hxp hfix ℓ.2 hxJ hx1 hk2
      · have hPbot := perfect_eq_bot_of_card_le_one (K := F) (κ := StepCoord r S ℓ.1)
          (by omega) (hP (stepHom hS ℓ.2))
        have hdvd' : p ∣ Nat.card ↥((V.subgroupOf J).map (stepHom hS ℓ.2)) := hdvd
        rw [hPbot, Subgroup.card_bot] at hdvd'
        have := Nat.le_of_dvd one_pos hdvd'
        rcases hp57 with rfl | rfl <;> omega
    · exact absurd rfl hi

end Nonsplit

section Split

variable [Finite F] [CharP F 2]

theorem levi_data_top {G : Type} [Group G] {J : Subgroup G} {p : ℕ}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hSQ : OmegaMinusSmallQS) (hpq : p ∣ Nat.card F - 1)
    (hno : NoAp p (↥(Ωm 1 F b c) ⧸ Subgroup.center ↥(Ωm 1 F b c))) {m : ℕ} (hm : m = 1)
    (φ : ↥(Ωm m F b c) →* G) (hφ : Function.Injective φ) (hφJ : ∀ A, φ A ∈ J) :
    φ.range ≤ J ∧ CFSG.Open.IsQuasisimple ↥φ.range ∧ p ∣ Nat.card φ.range ∧
      NoAp p (↥φ.range ⧸ Subgroup.center ↥φ.range) := by
  subst hm
  have e := MonoidHom.ofInjective hφ
  refine ⟨by rintro _ ⟨A, rfl⟩; exact hφJ A, ?_, ?_, ?_⟩
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm
      (isQuasisimple_top hirr hSQ le_rfl)
  · rw [← Nat.card_congr e.toEquiv]
    have := card_pow_dvd_card_Ωm (F := F) 1 b c
    rw [pow_one] at this
    exact hpq.trans this
  · exact noAp_center_quotient_of_surjective e.symm.toMonoidHom (MulEquiv.surjective _) hno

theorem eq_one_of_orth_zero (hSS : OmegaMinusSmallSplit) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hpq : p ∣ Nat.card F - 1) {m : ℕ} (hm : m = 0)
    {g : GL (Idx m) F} (hg : g ∈ orthGroup (Qm m F b c)) (hgp : g ^ p = 1) : g = 1 := by
  subst hm
  exact (hSS F b c hirr p hp57 hpq).1 g hg hgp

theorem false_of_split (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hSQ : OmegaMinusSmallQS)
    (hSS : OmegaMinusSmallSplit) (hr : 3 ≤ r) {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) (hpq : p ∣ Nat.card F - 1)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r)
    (hA1 : ∀ X : Subgroup (GL (Idx r) F), X ≤ JΩ r F b c S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X)
    (hA2 : ∀ X₁ X₂ : Subgroup (GL (Idx r) F), X₁ ≤ JΩ r F b c S → X₂ ≤ JΩ r F b c S →
      CFSG.Open.IsQuasisimple ↥X₁ → CFSG.Open.IsQuasisimple ↥X₂ →
      X₂ ≤ Subgroup.centralizer (X₁ : Set (GL (Idx r) F)) → p ∣ Nat.card X₁ →
      p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False)
    {x : GL (Idx r) F} (hxΩ : x ∈ Ωm r F b c) (hxp : x ^ p = 1)
    (hfix : ∀ g ∈ Ωm r F b c, g * x = x * g → g ∈ JΩ r F b c S)
    {V E : Subgroup (GL (Idx r) F)} (hVJ : V ≤ JΩ r F b c S)
    (hVx : V ≤ Subgroup.centralizer ({x} : Set (GL (Idx r) F))) (hV : ⁅V, V⁆ = V) (hEV : E ≤ V)
    (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) : False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have hp0 : (p : F) ≠ 0 := pCast_ne_zero hp hp2
  have hK4 : 4 ≤ Nat.card F := by
    rcases hK with h2 | h4
    · rw [h2] at hpq
      have : p ≤ 1 := Nat.le_of_dvd one_pos (by simpa using hpq)
      rcases hp57 with rfl | rfl <;> omega
    · exact h4
  have hxJ : x ∈ JΩ r F b c S := hfix x hxΩ rfl
  set J := JΩ r F b c S with hJ
  let B : FlagBlocks p ↥J := omFlagBlocks hS hp0
  have hBfin : ∀ i, Finite (B.H i) := fun i => instFiniteBlockTy i
  have hE' : ∀ e ∈ E.subgroupOf J, e ^ p = 1 := fun e he => Subtype.ext (by
    have := hEel.2 _ (Subgroup.mem_subgroupOf.1 he)
    simpa using this)
  have hEc' : p ^ 2 ≤ Nat.card (E.subgroupOf J) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEV.trans hVJ)).toEquiv, hEc]
  have hV' : ⁅V.subgroupOf J, V.subgroupOf J⁆ = V.subgroupOf J := commutator_subgroupOf_eq hVJ hV
  have hEV' : E.subgroupOf J ≤ V.subgroupOf J := fun e he =>
    Subgroup.mem_subgroupOf.2 (hEV (Subgroup.mem_subgroupOf.1 he))
  have hpg : ∀ {H : Type} [Group H] (ρ : ↥J →* H),
      ∀ y ∈ (E.subgroupOf J).map ρ, y ^ p = 1 := by
    intro H _ ρ y hy
    obtain ⟨e, he, rfl⟩ := hy
    rw [← map_pow, hE' e he, map_one]
  have hP : ∀ {H : Type} [Group H] (ρ : ↥J →* H),
      ⁅(V.subgroupOf J).map ρ, (V.subgroupOf J).map ρ⁆ = (V.subgroupOf J).map ρ := by
    intro H _ ρ
    rw [← Subgroup.map_commutator, hV']
  have hnk : ∀ ℓ : ℕ, ¬ (Fintype.card (StepCoord r S ℓ) = 2 ∧ Nat.card F = 2) :=
    fun ℓ h => by have := h.2; omega
  have hstep_le : ∀ ℓ : ℕ, Fintype.card (StepCoord r S ℓ) ≤ 2 := by
    intro ℓ
    by_contra hk
    push Not at hk
    refine not_sq_dvd_card_SL_of_lift hp57 hK hA1 (stepLeviΩ S ℓ) (stepLeviΩ_injective S ℓ)
      (fun hk' A => stepLeviΩ_mem hS hk' A) ?_
    have h1 := SpCell.pow_dvd_card_SL (K := F) (Fintype.card (StepCoord r S ℓ)) (by omega)
    exact ((pow_dvd_pow_of_dvd hpq 2).trans (pow_dvd_pow _ (by omega))).trans h1
  have htop_le : topN r S ≤ 1 := by
    by_contra hm
    push Not at hm
    refine not_sq_dvd_card_top_of_lift hirr hSQ (by omega) hA1 (topLevi S) (topLevi_injective S)
      (fun A => topLevi_mem hS A) ?_
    exact ((pow_dvd_pow_of_dvd hpq 2).trans (pow_dvd_pow _ (by omega))).trans
      (card_pow_dvd_card_Ωm (F := F) (topN r S) b c)
  have hcyc_step : ∀ ℓ : Fin S.card, IsCyclic ↥((E.subgroupOf J).map (stepHom hS ℓ.2)) := by
    intro ℓ
    exact isCyclic_of_perfect_gl_two hK hp57 (hstep_le ℓ.1) (hP (stepHom hS ℓ.2))
      (Subgroup.map_mono hEV') (isPGroup_of_pow_eq_one (hpg _))
  have hm : topN r S = 0 ∨ ¬ p ^ 2 ∣ Nat.card ↥(Ωm (topN r S) F b c) := by
    rcases Nat.eq_zero_or_pos (topN r S) with h0 | hpos
    · exact Or.inl h0
    · exact Or.inr (not_sq_dvd_card_top_of_lift hirr hSQ hpos hA1 (topLevi S)
        (topLevi_injective S) (fun A => topLevi_mem hS A))
  have hcyc_top : IsCyclic ↥((E.subgroupOf J).map (topHomGL hS)) :=
    isCyclic_of_perfect_top hp57 hK hm
      (P := (V.subgroupOf J).map (topHomGL hS))
      (by rintro _ ⟨g, -, rfl⟩; exact topHomGL_mem_orthGroup hS g)
      (hP (topHomGL hS)) (Subgroup.map_mono hEV') (isPGroup_of_pow_eq_one (hpg _))
  have act_step : ∀ ℓ : Fin S.card, (E.subgroupOf J).map (stepHom hS ℓ.2) ≠ ⊥ →
      Fintype.card (StepCoord r S ℓ.1) = 2 := by
    intro ℓ hne
    by_contra hk2
    have hk := hstep_le ℓ.1
    have hPbot := perfect_eq_bot_of_card_le_one (K := F) (by omega) (hP (stepHom hS ℓ.2))
    apply hne
    have := Subgroup.map_mono (f := stepHom hS ℓ.2) hEV'
    rw [hPbot] at this
    exact le_bot_iff.1 this
  have act_top : (E.subgroupOf J).map (topHomGL hS) ≠ ⊥ → topN r S = 1 := by
    intro hne
    rcases Nat.eq_zero_or_pos (topN r S) with h0 | h1
    · exfalso
      apply hne
      refine (Subgroup.eq_bot_iff_forall _).2 ?_
      rintro _ ⟨e, he, rfl⟩
      have hO := topHomGL_mem_orthGroup hS e
      have hpe : (topHomGL hS e) ^ p = 1 := by rw [← map_pow, hE' e he, map_one]
      exact eq_one_of_orth_zero hSS hirr hp57 hpq h0 hO hpe
    · omega
  have hcomm_sub : ∀ (X₁ X₂ : Subgroup (GL (Idx r) F)),
      (∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) → X₂ ≤ Subgroup.centralizer (X₁ : Set (GL (Idx r) F)) :=
    fun X₁ X₂ h b hb => Subgroup.mem_centralizer_iff.2 fun a ha => h a ha b hb
  have hstepdata : ∀ ℓ : Fin S.card, (E.subgroupOf J).map (stepHom hS ℓ.2) ≠ ⊥ →
      (stepLeviΩ S ℓ.1).range ≤ J ∧ CFSG.Open.IsQuasisimple ↥(stepLeviΩ S ℓ.1).range ∧
        p ∣ Nat.card (stepLeviΩ S ℓ.1).range ∧
        NoAp p (↥(stepLeviΩ S ℓ.1).range ⧸ Subgroup.center ↥(stepLeviΩ S ℓ.1).range) :=
    fun ℓ hi => SpCell.levi_data_sl2 (J := J) hp57 hK hpq (act_step ℓ hi) (stepLeviΩ S ℓ.1)
      (stepLeviΩ_injective S ℓ.1) (fun A => stepLeviΩ_mem hS (hnk _) A)
  have hnoAp1 := (hSS F b c hirr p hp57 hpq).2
  have hdata_top : (E.subgroupOf J).map (topHomGL hS) ≠ ⊥ →
      (topLevi S).range ≤ J ∧ CFSG.Open.IsQuasisimple ↥(topLevi S).range ∧
        p ∣ Nat.card (topLevi S).range ∧
        NoAp p (↥(topLevi S).range ⧸ Subgroup.center ↥(topLevi S).range) :=
    fun hj => levi_data_top (J := J) hirr hSQ hpq hnoAp1 (act_top hj) (topLevi S)
      (topLevi_injective S) (fun A => topLevi_mem hS A)
  refine B.false_of_split hp hE' hEc' (E := E.subgroupOf J) ?_ ?_
  · intro i
    rcases i with ℓ | u
    · exact hcyc_step ℓ
    · exact hcyc_top
  · intro i j hij hi hj
    rcases i with ℓ | u <;> rcases j with ℓ' | u'
    · have hne : ℓ.1 ≠ ℓ'.1 := fun h => hij (by rw [Fin.ext h])
      obtain ⟨hX₁J, hX₁q, hX₁p, hX₁n⟩ := hstepdata ℓ hi
      obtain ⟨hX₂J, hX₂q, hX₂p, hX₂n⟩ := hstepdata ℓ' hj
      refine hA2 _ _ hX₁J hX₂J hX₁q hX₂q (hcomm_sub _ _ ?_) hX₁p hX₂p hX₁n hX₂n
      rintro _ ⟨A, rfl⟩ _ ⟨B', rfl⟩
      exact stepLeviΩ_commute_stepLeviΩ hne A B'
    · obtain ⟨hX₁J, hX₁q, hX₁p, hX₁n⟩ := hstepdata ℓ hi
      obtain ⟨hX₂J, hX₂q, hX₂p, hX₂n⟩ := hdata_top hj
      refine hA2 _ _ hX₁J hX₂J hX₁q hX₂q (hcomm_sub _ _ ?_) hX₁p hX₂p hX₁n hX₂n
      rintro _ ⟨A, rfl⟩ _ ⟨B', rfl⟩
      exact stepLeviΩ_commute_topLevi ℓ.2 A B'
    · obtain ⟨hX₁J, hX₁q, hX₁p, hX₁n⟩ := hdata_top hi
      obtain ⟨hX₂J, hX₂q, hX₂p, hX₂n⟩ := hstepdata ℓ' hj
      refine hA2 _ _ hX₁J hX₂J hX₁q hX₂q (hcomm_sub _ _ ?_) hX₁p hX₂p hX₁n hX₂n
      rintro _ ⟨A, rfl⟩ _ ⟨B', rfl⟩
      exact (stepLeviΩ_commute_topLevi ℓ'.2 B' A).symm
    · exact hij rfl

end Split

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

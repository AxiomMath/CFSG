module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusLevi
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusEscape
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusQ4

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.Open
open CFSG.AGLEmbedding.LieOut
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

variable {n : ℕ} {F : Type} [Field F]

section Cores

variable {J : Type*} [Group J] {p : ℕ}

theorem FlagBlocks.false_of_nonsplit' (B : FlagBlocks p J) (hp : p.Prime) [∀ i, Finite (B.H i)]
    (top : B.ι → Prop) (htop : ∀ i j, top i → top j → i = j)
    (hH : ∀ i, ¬ top i → ¬ p ^ 2 ∣ Nat.card (B.H i)) {V E : Subgroup J} [Finite E]
    (hV : ⁅V, V⁆ = V) (hEV : E ≤ V) (hE : ∀ e ∈ E, e ^ p = 1) (hEc : p ^ 2 ≤ Nat.card E)
    {x : J} (hx : x ^ p = 1) (hxV : ∀ v ∈ V, v * x = x * v)
    (hesc : ∀ i, ¬ top i → B.ρ i x = 1 → p ∣ Nat.card (V.map (B.ρ i)) → False)
    (hcycTop : ∀ i, top i → IsCyclic ↥(E.map (B.ρ i))) : False := by
  have hbot : ∀ i, ¬ top i → E.map (B.ρ i) = ⊥ := fun i hi =>
    map_eq_bot_of_transfer (B.ρ i) hp (hH i hi) hV hEV hE hx hxV (hesc i hi)
  have hcyc : ∀ i, IsCyclic ↥(E.map (B.ρ i)) := by
    intro i
    by_cases hi : top i
    · exact hcycTop i hi
    · rw [hbot i hi]
      infer_instance
  obtain ⟨i, j, hij, hi, hj⟩ := B.exists_two_ne_bot_map hp hE hEc hcyc
  have hti : top i := by_contra fun h => hi (hbot i h)
  have htj : top j := by_contra fun h => hj (hbot j h)
  exact hij (htop i j hti htj)

end Cores

theorem exists_cut_ge_two (hn : 4 ≤ n) {S : Finset ℕ} (ht : topN n S ≤ 2) :
    ∃ i ∈ S, 2 ≤ i := by
  by_contra hcon
  push Not at hcon
  have hcnt : ∀ a : Fin n, 1 ≤ (a : ℕ) → cnt S a = S.card := by
    intro a ha
    refine le_antisymm (cnt_le_card S a) (not_lt.1 fun h => ?_)
    obtain ⟨i, hi, hai⟩ := exists_cut_of_cnt_lt_card S h
    have := hcon i hi
    omega
  let f : Fin 3 → {a : Fin n // cnt S a = S.card} := fun j =>
    ⟨⟨j.val + 1, by have := j.isLt; omega⟩, hcnt _ (by simp)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg (fun z : {a : Fin n // cnt S a = S.card} => (z.1 : ℕ)) hab
    simp only [f] at this
    exact Fin.ext (by omega)
  have h3 := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at h3
  have : topN n S = Fintype.card {a : Fin n // cnt S a = S.card} := rfl
  omega

section Nonsplit

variable [Finite F] [CharP F 2] {S : Finset ℕ}

theorem false_of_nonsplit_D {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) (hpq : ¬ p ∣ Nat.card F - 1) (hn : 4 ≤ n)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n)
    (hA1 : ∀ X : Subgroup ↥(Om n F), X ≤ JO n F S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X)
    {x : ↥(Om n F)} (hxp : x ^ p = 1)
    (hfix : ∀ g : ↥(Om n F), g * x = x * g → g ∈ JO n F S)
    {V E : Subgroup ↥(Om n F)} (hVJ : V ≤ JO n F S)
    (hVx : V ≤ Subgroup.centralizer ({x} : Set ↥(Om n F))) (hV : ⁅V, V⁆ = V) (hEV : E ≤ V)
    (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hTop : IsCyclic ↥((E.subgroupOf (JO n F S)).map ((topHom hS).comp (jToJfl S)))) : False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have hp0 : (p : F) ≠ 0 := pCast_ne_zero hp hp2
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hxJ : x ∈ JO n F S := hfix x rfl
  set J := JO n F S with hJ
  let B : FlagBlocks p ↥J := blocksD hS hp0
  have hBfin : ∀ i, Finite (B.H i) := fun i => instFiniteBlockTy (S := S) i
  have hE' : ∀ e ∈ E.subgroupOf J, e ^ p = 1 := fun e he => Subtype.ext (by
    have := hEel.2 _ (Subgroup.mem_subgroupOf.1 he)
    simpa using this)
  have hH : ∀ i, ¬ (i = Sum.inr ()) → ¬ p ^ 2 ∣ Nat.card (B.H i) := by
    intro i hi
    rcases i with ℓ | _
    · exact not_sq_dvd_card_step_D hp57 hK hpq hS hA1 ℓ.1
    · exact absurd rfl hi
  have hEc' : p ^ 2 ≤ Nat.card (E.subgroupOf J) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEV.trans hVJ)).toEquiv, hEc]
  have hxV : ∀ v ∈ V.subgroupOf J, v * (⟨x, hxJ⟩ : ↥J) = ⟨x, hxJ⟩ * v := by
    intro v hv
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.1 (hVx (Subgroup.mem_subgroupOf.1 hv)) x
      (Set.mem_singleton x)
    exact this.symm
  have hV' := commutator_subgroupOf_eq hVJ hV
  refine FlagBlocks.false_of_nonsplit' B hp (fun i => i = Sum.inr ())
    (fun i j hi hj => hi.trans hj.symm) hH hV'
    (fun e he => Subgroup.mem_subgroupOf.2 (hEV (Subgroup.mem_subgroupOf.1 he))) hE' hEc'
    (x := ⟨x, hxJ⟩) (Subtype.ext (by simpa using hxp)) hxV ?_ ?_
  · intro i hi hx1 hdvd
    rcases i with ℓ | u
    · by_cases hk2 : 2 ≤ Fintype.card (StepCoord n S ℓ.1)
      · exact false_of_step_escape_D hn hS hodd hp0 hxp hfix ℓ.2 hxJ hx1 hk2
      · have hPbot := perfect_eq_bot_of_card_le_one (K := F) (by omega)
          (show ⁅(V.subgroupOf J).map ((stepHom hS ℓ.2).comp (jToJfl S)),
            (V.subgroupOf J).map ((stepHom hS ℓ.2).comp (jToJfl S))⁆ =
            (V.subgroupOf J).map ((stepHom hS ℓ.2).comp (jToJfl S)) by
            rw [← Subgroup.map_commutator, hV'])
        have hdvd' : p ∣ Nat.card ↥((V.subgroupOf J).map ((stepHom hS ℓ.2).comp (jToJfl S))) :=
          hdvd
        rw [hPbot, Subgroup.card_bot] at hdvd'
        have := Nat.le_of_dvd one_pos hdvd'
        rcases hp57 with rfl | rfl <;> omega
    · exact absurd rfl hi
  · intro i hi
    rcases i with ℓ | u
    · exact absurd hi (by simp)
    · exact hTop

end Nonsplit

section Split

variable [Finite F] [CharP F 2] {S : Finset ℕ}

theorem false_of_split_D {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) (hpq : p ∣ Nat.card F - 1)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) (htop0 : topN n S = 0)
    (hA1 : ∀ X : Subgroup ↥(Om n F), X ≤ JO n F S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X)
    (hA2 : ∀ X₁ X₂ : Subgroup ↥(Om n F), X₁ ≤ JO n F S → X₂ ≤ JO n F S →
      CFSG.Open.IsQuasisimple ↥X₁ → CFSG.Open.IsQuasisimple ↥X₂ →
      X₂ ≤ Subgroup.centralizer (X₁ : Set ↥(Om n F)) → p ∣ Nat.card X₁ →
      p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False)
    {x : ↥(Om n F)} (hxp : x ^ p = 1)
    (hfix : ∀ g : ↥(Om n F), g * x = x * g → g ∈ JO n F S)
    {V E : Subgroup ↥(Om n F)} (hVJ : V ≤ JO n F S) (hV : ⁅V, V⁆ = V) (hEV : E ≤ V)
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
  have hxJ : x ∈ JO n F S := hfix x rfl
  set J := JO n F S with hJ
  let B : FlagBlocks p ↥J := blocksD hS hp0
  have hV' : ⁅V.subgroupOf J, V.subgroupOf J⁆ = V.subgroupOf J := commutator_subgroupOf_eq hVJ hV
  have hEV' : E.subgroupOf J ≤ V.subgroupOf J := fun e he =>
    Subgroup.mem_subgroupOf.2 (hEV (Subgroup.mem_subgroupOf.1 he))
  have hE' : ∀ e ∈ E.subgroupOf J, e ^ p = 1 := fun e he => Subtype.ext (by
    have := hEel.2 _ (Subgroup.mem_subgroupOf.1 he)
    simpa using this)
  have hEc' : p ^ 2 ≤ Nat.card (E.subgroupOf J) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEV.trans hVJ)).toEquiv, hEc]
  have hpg : ∀ {H : Type} [Group H] (ρ : ↥J →* H),
      ∀ y ∈ (E.subgroupOf J).map ρ, y ^ p = 1 := by
    intro H _ ρ y hy
    obtain ⟨e, he, rfl⟩ := hy
    rw [← map_pow, hE' e he, map_one]
  have hP : ∀ {H : Type} [Group H] (ρ : ↥J →* H),
      ⁅(V.subgroupOf J).map ρ, (V.subgroupOf J).map ρ⁆ = (V.subgroupOf J).map ρ := by
    intro H _ ρ
    rw [← Subgroup.map_commutator, hV']
  have hcyc_step : ∀ ℓ : Fin S.card,
      IsCyclic ↥((E.subgroupOf J).map ((stepHom hS ℓ.2).comp (jToJfl S))) := by
    intro ℓ
    exact isCyclic_of_perfect_gl (step_card_le_two_D hp57 hK hpq hS hA1 ℓ.1) hK4 hp hp2
      (hP ((stepHom hS ℓ.2).comp (jToJfl S))) (Subgroup.map_mono hEV')
      (isPGroup_of_pow_eq_one (hpg _))
  have hsub : Subsingleton ↥(StatedSp (topN n S) F) := by
    rw [htop0]
    exact ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
  have hcyc_top : IsCyclic ↥((E.subgroupOf J).map ((topHom hS).comp (jToJfl S))) := by
    have : Subsingleton ↥((E.subgroupOf J).map ((topHom hS).comp (jToJfl S))) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (α := ↥(StatedSp (topN n S) F)) _ _)⟩
    infer_instance
  have htopbot : (E.subgroupOf J).map ((topHom hS).comp (jToJfl S)) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun y _ => Subsingleton.elim y 1
  have act_step : ∀ ℓ : Fin S.card,
      (E.subgroupOf J).map ((stepHom hS ℓ.2).comp (jToJfl S)) ≠ ⊥ →
      Fintype.card (StepCoord n S ℓ.1) = 2 := by
    intro ℓ hne
    by_contra hk2
    have hk := step_card_le_two_D hp57 hK hpq hS hA1 ℓ.1
    have hPbot := perfect_eq_bot_of_card_le_one (K := F) (by omega)
      (hP ((stepHom hS ℓ.2).comp (jToJfl S)))
    apply hne
    have := Subgroup.map_mono (f := (stepHom hS ℓ.2).comp (jToJfl S)) hEV'
    rw [hPbot] at this
    exact le_bot_iff.1 this
  have hcomm_sub : ∀ (X₁ X₂ : Subgroup ↥(Om n F)),
      (∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) → X₂ ≤ Subgroup.centralizer (X₁ : Set ↥(Om n F)) :=
    fun X₁ X₂ h b hb => Subgroup.mem_centralizer_iff.2 fun a ha => h a ha b hb
  refine B.false_of_split hp hE' hEc' (E := E.subgroupOf J) ?_ ?_
  · intro i
    rcases i with ℓ | u
    · exact hcyc_step ℓ
    · exact hcyc_top
  · intro i j hij hi hj
    rcases i with ℓ | u <;> rcases j with ℓ' | u'
    · have hne : ℓ.1 ≠ ℓ'.1 := fun h => hij (by rw [Fin.ext h])
      obtain ⟨φ, hφinj, hφ, hφJ, hX₁J, hX₁q, hX₁p, hX₁n⟩ :=
        levi_data_sl2_D hp57 hK hpq hS ℓ.1 (act_step ℓ hi)
      obtain ⟨φ', hφ'inj, hφ', hφ'J, hX₂J, hX₂q, hX₂p, hX₂n⟩ :=
        levi_data_sl2_D hp57 hK hpq hS ℓ'.1 (act_step ℓ' hj)
      refine hA2 _ _ hX₁J hX₂J hX₁q hX₂q (hcomm_sub _ _ ?_) hX₁p hX₂p hX₁n hX₂n
      rintro _ ⟨A, rfl⟩ _ ⟨B', rfl⟩
      exact stepLeviO_commute ℓ.2 ℓ'.2 hne φ φ' hφ hφ' A B'
    · exact absurd htopbot hj
    · exact absurd htopbot hi
    · exact hij rfl

end Split

section Top

variable [Finite F] [CharP F 2] {S : Finset ℕ}

theorem card_eq_four_or_eight_le (h4 : 4 ≤ Nat.card F) : Nat.card F = 4 ∨ 8 ≤ Nat.card F := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ, Nat.card F = 2 ^ f := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨m, -, hm⟩ := FiniteField.card (K := F) 2
    exact ⟨m, by rw [Nat.card_eq_fintype_card]; exact hm⟩
  rw [hf] at h4 ⊢
  rcases Nat.lt_or_ge f 3 with h | h
  · interval_cases f <;> simp_all
  · right
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h

theorem card_sl2_quot : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F ⧸
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have hz : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = 1 := by
    rw [CFSG.AGLEmbedding.ParabPrime.sl2_center_eq_bot (k := F), Subgroup.card_bot]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  rw [hz, mul_one, card_SL2_eq] at h
  exact h.symm

theorem noAp_sl2_of_dvd_sq {p : ℕ} (hp57 : p = 5 ∨ p = 7) (h8 : 8 ≤ Nat.card F)
    (hp : p ∣ Nat.card F ^ 2 - 1) :
    NoAp p (Matrix.SpecialLinearGroup (Fin 2) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  have hprime : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  by_cases h1 : p ∣ Nat.card F - 1
  · exact noAp_sl2 hp57 h1
  · obtain ⟨f, hf⟩ : ∃ f : ℕ, Nat.card F = 2 ^ f := by
      have : Fintype F := Fintype.ofFinite F
      obtain ⟨m, -, hm⟩ := FiniteField.card (K := F) 2
      exact ⟨m, by rw [Nat.card_eq_fintype_card]; exact hm⟩
    have hq1 : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
      have : 1 ≤ Nat.card F := by omega
      zify [this, Nat.one_le_pow 2 _ this]
      ring
    have h2 : p ∣ Nat.card F + 1 :=
      ((Nat.Prime.dvd_mul hprime).1 (hq1 ▸ hp)).resolve_left h1
    have h16 : 16 ≤ Nat.card F := by
      rcases Nat.lt_or_ge f 4 with hf4 | hf4
      · have hf3 : f = 3 := by
          rw [hf] at h8
          by_contra hne
          have : f ≤ 2 := by omega
          have : 2 ^ f ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
          omega
        subst hf3
        rw [hf] at h2
        rcases hp57 with rfl | rfl <;> omega
      · rw [hf]
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf4
    refine NoAp.of_card_lt ?_
    rw [card_sl2_quot]
    have hbig : 4080 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := by
      have h1' : 16 * (16 ^ 2 - 1) ≤ Nat.card F * (Nat.card F ^ 2 - 1) :=
        Nat.mul_le_mul h16 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h16 2) 1)
      simpa using h1'
    rcases hp57 with rfl | rfl
    · rw [card_alt_five]; omega
    · rw [card_alt_seven]; omega

theorem top2_aux {t : ℕ} (ht : t = 2) (h4 : 4 ≤ Nat.card F) {X : Type*} [Group X]
    (ψ : ↥(Om t F) →* X) (hψ : Function.Injective ψ) :
    ∃ φ₁ φ₂ : Matrix.SpecialLinearGroup (Fin 2) F →* X, Function.Injective φ₁ ∧
      Function.Injective φ₂ ∧ (∀ A B, φ₁ A * φ₂ B = φ₂ B * φ₁ A) ∧
      (∀ A B, φ₁ A = φ₂ B → A = 1) ∧ (∀ A, ∃ B, φ₁ A = ψ B) ∧ (∀ A, ∃ B, φ₂ A = ψ B) := by
  subst ht
  refine ⟨ψ.comp (j1Om h4), ψ.comp (j2Om h4), fun A B h => ?_, fun A B h => ?_, fun A B => ?_,
    fun A B h => ?_, fun A => ⟨_, rfl⟩, fun A => ⟨_, rfl⟩⟩
  · exact j1Om_injective h4 (hψ h)
  · exact j2Om_injective h4 (hψ h)
  · simp only [MonoidHom.comp_apply, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (j1_j2_commute (F := F) A B).eq
  · have := hψ h
    exact (eq_one_of_j1_eq_j2 (congrArg Subtype.val this)).1

theorem top2_package (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) (ht : topN n S = 2) (h4 : 4 ≤ Nat.card F) :
    ∃ φ₁ φ₂ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(Om n F), Function.Injective φ₁ ∧
      Function.Injective φ₂ ∧ (∀ A, φ₁ A ∈ JO n F S) ∧ (∀ A, φ₂ A ∈ JO n F S) ∧
      (∀ A B, φ₁ A * φ₂ B = φ₂ B * φ₁ A) := by
  obtain ⟨ψ, hψinj, hψJ, -⟩ := exists_topLeviO (n := n) (F := F) (S := S) hS
  obtain ⟨φ₁, φ₂, h1, h2, hc, -, he1, he2⟩ := top2_aux ht h4 ψ hψinj
  refine ⟨φ₁, φ₂, h1, h2, fun A => ?_, fun A => ?_, hc⟩
  · obtain ⟨B, hB⟩ := he1 A
    rw [hB]; exact hψJ B
  · obtain ⟨B, hB⟩ := he2 A
    rw [hB]; exact hψJ B

theorem false_of_top2 {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n)
    (ht : topN n S = 2) (h8 : 8 ≤ Nat.card F) (hpd : p ∣ Nat.card F ^ 2 - 1)
    (hA2 : ∀ X₁ X₂ : Subgroup ↥(Om n F), X₁ ≤ JO n F S → X₂ ≤ JO n F S →
      CFSG.Open.IsQuasisimple ↥X₁ → CFSG.Open.IsQuasisimple ↥X₂ →
      X₂ ≤ Subgroup.centralizer (X₁ : Set ↥(Om n F)) → p ∣ Nat.card X₁ →
      p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False) : False := by
  have h4 : 4 ≤ Nat.card F := by omega
  obtain ⟨φ₁, φ₂, hi₁, hi₂, hJ₁, hJ₂, hc⟩ := top2_package hS ht h4
  have hdata : ∀ (φ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(Om n F)), Function.Injective φ →
      (∀ A, φ A ∈ JO n F S) → φ.range ≤ JO n F S ∧ CFSG.Open.IsQuasisimple ↥φ.range ∧
        p ∣ Nat.card φ.range ∧ NoAp p (↥φ.range ⧸ Subgroup.center ↥φ.range) := by
    intro φ hφ hφJ
    have e := MonoidHom.ofInjective hφ
    refine ⟨by rintro _ ⟨A, rfl⟩; exact hφJ A, ?_, ?_, ?_⟩
    · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm
        (open_of_isQuasisimple (LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4))
    · rw [← Nat.card_congr e.toEquiv, card_SL2_eq]
      refine Dvd.dvd.mul_left ?_ _
      exact hpd
    · exact noAp_center_quotient_of_surjective e.symm.toMonoidHom (MulEquiv.surjective _)
        (noAp_sl2_of_dvd_sq hp57 h8 hpd)
  obtain ⟨hX₁J, hX₁q, hX₁p, hX₁n⟩ := hdata φ₁ hi₁ hJ₁
  obtain ⟨hX₂J, hX₂q, hX₂p, hX₂n⟩ := hdata φ₂ hi₂ hJ₂
  refine hA2 _ _ hX₁J hX₂J hX₁q hX₂q ?_ hX₁p hX₂p hX₁n hX₂n
  intro b hb
  obtain ⟨B, rfl⟩ := hb
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨A, rfl⟩
  exact (hc A B)

end Top

section TopCases

variable [Finite F] [CharP F 2] {S : Finset ℕ}

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (leviSp coe_leviSp)

theorem slLevi_mem_om (m : ℕ) (hperf : ¬ (m = 2 ∧ Nat.card F = 2))
    (A : Matrix.SpecialLinearGroup (Fin m) F) :
    ((leviSp (Matrix.SpecialLinearGroup.toGL A) : StatedSp m F) : GL (Fin m ⊕ Fin m) F) ∈
      Om m F := by
  set f : Matrix.SpecialLinearGroup (Fin m) F →* GL (Fin m ⊕ Fin m) F :=
    (StatedSp m F).subtype.comp (leviSp.comp Matrix.SpecialLinearGroup.toGL) with hf
  have hrange : f.range ≤ orthGroup (StatedQuadPlus m F) := by
    rintro _ ⟨B, rfl⟩
    exact leviSp_mem_orthGroup (Matrix.SpecialLinearGroup.toGL B)
  have hA' : f A ∈ Subgroup.map f ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin m) F)), ⊤⁆ :=
    Subgroup.mem_map_of_mem f (by rw [perfect_SL _ hperf]; exact Subgroup.mem_top A)
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map] at hA'
  exact Subgroup.commutator_mono hrange hrange hA'

@[expose] noncomputable def slOm (m : ℕ) (hperf : ¬ (m = 2 ∧ Nat.card F = 2)) :
    Matrix.SpecialLinearGroup (Fin m) F →* ↥(Om m F) :=
  ((StatedSp m F).subtype.comp (leviSp.comp Matrix.SpecialLinearGroup.toGL)).codRestrict (Om m F)
    (slLevi_mem_om m hperf)

theorem slOm_injective (m : ℕ) (hperf : ¬ (m = 2 ∧ Nat.card F = 2)) :
    Function.Injective (slOm (F := F) m hperf) := by
  intro A B h
  have h1 : ((leviSp (Matrix.SpecialLinearGroup.toGL A) : StatedSp m F) : GL (Fin m ⊕ Fin m) F) =
      ((leviSp (Matrix.SpecialLinearGroup.toGL B) : StatedSp m F) : GL (Fin m ⊕ Fin m) F) :=
    congrArg (fun g : ↥(Om m F) => (g : GL (Fin m ⊕ Fin m) F)) h
  have h' := congrArg (fun g : GL (Fin m ⊕ Fin m) F =>
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F)) h1
  simp only [coe_leviSp, Matrix.fromBlocks_inj] at h'
  exact Matrix.SpecialLinearGroup.toGL_injective (Units.ext h'.1)

theorem topN_le_two_of_split {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) (hpq : p ∣ Nat.card F - 1)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n)
    (hA1 : ∀ X : Subgroup ↥(Om n F), X ≤ JO n F S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X) : topN n S ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have hperf : ¬ (topN n S = 2 ∧ Nat.card F = 2) := fun h => by omega
  obtain ⟨ψ, hψinj, hψJ, -⟩ := exists_topLeviO (n := n) (F := F) (S := S) hS
  refine not_sq_dvd_card_SL hp57 hK hA1 (ψ.comp (slOm (topN n S) hperf))
    (hψinj.comp (slOm_injective _ hperf)) (fun A => hψJ _) ?_
  have h1 := pow_dvd_card_SL (K := F) (topN n S) (by omega)
  exact ((pow_dvd_pow_of_dvd hpq 2).trans (pow_dvd_pow _ (by omega))).trans h1

theorem topN_eq_zero_of_split {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) (hpq : p ∣ Nat.card F - 1)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) (hS1 : n - 1 ∈ S → n ∈ S) (hSne : S.Nonempty)
    (hA1 : ∀ X : Subgroup ↥(Om n F), X ≤ JO n F S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X)
    (hA2 : ∀ X₁ X₂ : Subgroup ↥(Om n F), X₁ ≤ JO n F S → X₂ ≤ JO n F S →
      CFSG.Open.IsQuasisimple ↥X₁ → CFSG.Open.IsQuasisimple ↥X₂ →
      X₂ ≤ Subgroup.centralizer (X₁ : Set ↥(Om n F)) → p ∣ Nat.card X₁ →
      p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False) : topN n S = 0 := by
  have hle := topN_le_two_of_split hp57 hK hpq hS hA1
  have h1 := topN_ne_one hS hS1 hSne
  by_contra h0
  have h2 : topN n S = 2 := by omega
  have hK4 : 4 ≤ Nat.card F := by
    rcases hK with h2 | h4
    · rw [h2] at hpq
      have : p ≤ 1 := Nat.le_of_dvd one_pos (by simpa using hpq)
      rcases hp57 with rfl | rfl <;> omega
    · exact h4
  have h8 : 8 ≤ Nat.card F := by
    rcases card_eq_four_or_eight_le hK4 with h | h
    · rw [h] at hpq
      rcases hp57 with rfl | rfl <;> omega
    · exact h
  have hpd : p ∣ Nat.card F ^ 2 - 1 := by
    have hq1 : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
      have : 1 ≤ Nat.card F := by omega
      zify [this, Nat.one_le_pow 2 _ this]
      ring
    rw [hq1]
    exact Dvd.dvd.mul_right hpq _
  exact false_of_top2 hp57 hS h2 h8 hpd hA2

omit [Finite F] in
theorem isCyclic_map_topHom {E' : Subgroup ↥(JO n F S)} (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n)
    (h : IsCyclic ↥(E'.map ((topHomGL hS).comp (jToJfl S)))) :
    IsCyclic ↥(E'.map ((topHom hS).comp (jToJfl S))) := by
  have hcomp : (StatedSp (topN n S) F).subtype.comp ((topHom hS).comp (jToJfl S)) =
      (topHomGL hS).comp (jToJfl S) := rfl
  rw [← hcomp, ← Subgroup.map_map] at h
  have e := Subgroup.equivMapOfInjective (E'.map ((topHom hS).comp (jToJfl S)))
    (StatedSp (topN n S) F).subtype (Subgroup.subtype_injective _)
  have := h
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem eq_one_of_pow_top2 {t : ℕ} (ht : t = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {y : GL (Fin t ⊕ Fin t) F}
    (hy : ∀ v, StatedQuadPlus t F ((y : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) F) *ᵥ v) =
      StatedQuadPlus t F v) (hyp : y ^ p = 1) : y = 1 := by
  subst ht
  exact eq_one_of_pow_eq_one_of_not_dvd hp hp2 hpq (Subgroup.subset_closure hy) hyp

end TopCases

section Flag

variable [Finite F] [CharP F 2] {S : Finset ℕ}

theorem false_of_nonsplit_D_full {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) (hpq : ¬ p ∣ Nat.card F - 1) (hn : 4 ≤ n)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) (hS1 : n - 1 ∈ S → n ∈ S) (hSne : S.Nonempty)
    (hA1 : ∀ X : Subgroup ↥(Om n F), X ≤ JO n F S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X)
    (hA2 : ∀ X₁ X₂ : Subgroup ↥(Om n F), X₁ ≤ JO n F S → X₂ ≤ JO n F S →
      CFSG.Open.IsQuasisimple ↥X₁ → CFSG.Open.IsQuasisimple ↥X₂ →
      X₂ ≤ Subgroup.centralizer (X₁ : Set ↥(Om n F)) → p ∣ Nat.card X₁ →
      p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False)
    {x : ↥(Om n F)} (hxp : x ^ p = 1)
    (hfix : ∀ g : ↥(Om n F), g * x = x * g → g ∈ JO n F S)
    {V E : Subgroup ↥(Om n F)} (hVJ : V ≤ JO n F S)
    (hVx : V ≤ Subgroup.centralizer ({x} : Set ↥(Om n F))) (hV : ⁅V, V⁆ = V) (hEV : E ≤ V)
    (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) : False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  refine false_of_nonsplit_D hp57 hK hpq hn hS hA1 hxp hfix hVJ hVx hV hEV hEel hEc ?_
  set J := JO n F S with hJ
  have hE' : ∀ e ∈ E.subgroupOf J, e ^ p = 1 := fun e he => Subtype.ext (by
    have := hEel.2 _ (Subgroup.mem_subgroupOf.1 he)
    simpa using this)
  rcases (by omega : topN n S = 0 ∨ topN n S = 1 ∨ topN n S = 2 ∨ 3 ≤ topN n S) with
    h0 | h1 | h2 | h3
  · have hsub : Subsingleton ↥(StatedSp (topN n S) F) := by
      rw [h0]
      exact ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
    have : Subsingleton ↥((E.subgroupOf J).map ((topHom hS).comp (jToJfl S))) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (α := ↥(StatedSp (topN n S) F)) _ _)⟩
    infer_instance
  · exact absurd h1 (topN_ne_one hS hS1 hSne)
  · by_cases hpd : p ∣ Nat.card F ^ 2 - 1
    · have h4 : 4 ≤ Nat.card F := by
        rcases hK with h2' | h4
        · rw [h2'] at hpd
          exfalso
          rcases hp57 with rfl | rfl <;> omega
        · exact h4
      rcases card_eq_four_or_eight_le h4 with hF4 | hF8
      · exfalso
        have hp5 : p = 5 := by
          rw [hF4] at hpd
          rcases hp57 with h | h
          · exact h
          · rw [h] at hpd; omega
        obtain ⟨i, hiS, hi2⟩ := exists_cut_ge_two hn (le_of_eq h2)
        subst hp5
        exact false_of_q4 hn hF4 hS hiS hi2 hxp hfix
      · exfalso
        exact false_of_top2 hp57 hS h2 hF8 hpd hA2
    · have hbot : (E.subgroupOf J).map ((topHom hS).comp (jToJfl S)) = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        rintro _ ⟨e, he, rfl⟩
        have hpe : (topHomGL hS (jToJfl S e)) ^ p = 1 := by
          rw [← map_pow, ← map_pow, hE' e he, map_one, map_one]
        have h1' := eq_one_of_pow_top2 h2 hp hp2 hpd
          (y := topHomGL hS (jToJfl S e)) (topHom_preserves hS e) hpe
        exact Subtype.ext h1'
      rw [hbot]
      infer_instance
  · exact isCyclic_map_topHom hS (isCyclic_map_top_of_A1 hp57 h3 hS hA1 (E.subgroupOf J) hE')

theorem false_of_flag_D {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) (hn : 4 ≤ n)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) (hS1 : n - 1 ∈ S → n ∈ S) (hSne : S.Nonempty)
    (hA1 : ∀ X : Subgroup ↥(Om n F), X ≤ JO n F S → CFSG.Open.IsQuasisimple ↥X →
      ¬ p ^ 2 ∣ Nat.card X)
    (hA2 : ∀ X₁ X₂ : Subgroup ↥(Om n F), X₁ ≤ JO n F S → X₂ ≤ JO n F S →
      CFSG.Open.IsQuasisimple ↥X₁ → CFSG.Open.IsQuasisimple ↥X₂ →
      X₂ ≤ Subgroup.centralizer (X₁ : Set ↥(Om n F)) → p ∣ Nat.card X₁ →
      p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False)
    {x : ↥(Om n F)} (hxp : x ^ p = 1)
    (hfix : ∀ g : ↥(Om n F), g * x = x * g → g ∈ JO n F S)
    {V E : Subgroup ↥(Om n F)} (hVJ : V ≤ JO n F S)
    (hVx : V ≤ Subgroup.centralizer ({x} : Set ↥(Om n F))) (hV : ⁅V, V⁆ = V) (hEV : E ≤ V)
    (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) : False := by
  by_cases hpq : p ∣ Nat.card F - 1
  · exact false_of_split_D hp57 hK hpq hS (topN_eq_zero_of_split hp57 hK hpq hS hS1 hSne hA1 hA2)
      hA1 hA2 hxp hfix hVJ hV hEV hEel hEc
  · exact false_of_nonsplit_D_full hp57 hK hpq hn hS hS1 hSne hA1 hA2 hxp hfix hVJ hVx hV hEV
      hEel hEc

end Flag

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

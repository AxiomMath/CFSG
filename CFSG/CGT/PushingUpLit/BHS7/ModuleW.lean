module

public import CFSG.CGT.PushingUpLit.BHS.HomTransfer
public import CFSG.CGT.PushingUpLit.BHS6.Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

omit [Group Γ] in
theorem commutator_eq_bot_of_quadratic [Group Γ] {K W : Subgroup Γ}
    (hK : K ≤ Subgroup.closure {x | x ∈ K ∧ Odd (orderOf x)})
    (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hKW : K ≤ Subgroup.normalizer (W : Set Γ))
    (hq : ⁅⁅W, K⁆, K⁆ = ⊥) : ⁅W, K⁆ = ⊥ := by
  have hodd : ∀ x ∈ K, Odd (orderOf x) → ∀ w ∈ W, x * w = w * x := by
    intro x hx hxo w hw
    set u : Γ := x * w * x⁻¹ * w⁻¹ with hu
    have hvW : x * w * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hKW hx) w).mp hw
    have huW : u ∈ W := W.mul_mem hvW (W.inv_mem hw)
    have huK : u ∈ (⁅W, K⁆ : Subgroup Γ) := by
      have h1 : ⁅w, x⁆ ∈ (⁅W, K⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hw hx
      have h2 := (⁅W, K⁆ : Subgroup Γ).inv_mem h1
      rwa [commutatorElement_inv] at h2
    have hux : u * x = x * u := by
      have h1 : ⁅u, x⁆ ∈ (⁅⁅W, K⁆, K⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator huK hx
      rw [hq, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have huu : u * u = 1 := by
      have := hW2 u huW
      rwa [pow_two] at this
    have e1 : x * w * x⁻¹ = u * w := by rw [hu]; group
    have hsq : x ^ 2 * w = w * x ^ 2 := by
      have h3 : x * (x * w * x⁻¹) * x⁻¹ = w := by
        rw [e1]
        calc x * (u * w) * x⁻¹ = (x * u * x⁻¹) * (x * w * x⁻¹) := by group
          _ = u * (u * w) := by rw [e1, show x * u * x⁻¹ = u by rw [← hux]; group]
          _ = (u * u) * w := by group
          _ = w := by rw [huu, one_mul]
      calc x ^ 2 * w = (x * (x * w * x⁻¹) * x⁻¹) * x ^ 2 := by simp only [pow_two]; group
        _ = w * x ^ 2 := by rw [h3]
    obtain ⟨j, hj⟩ := hxo
    have hxpow : x = (x ^ 2) ^ (j + 1) := by
      calc x = x ^ orderOf x * x := by rw [pow_orderOf_eq_one, one_mul]
        _ = x ^ (2 * (j + 1)) := by rw [← pow_succ, hj]; ring_nf
        _ = (x ^ 2) ^ (j + 1) := by rw [pow_mul]
    have hcomm : Commute (x ^ 2) w := hsq
    rw [hxpow]
    exact (hcomm.pow_left (j + 1)).eq
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro w hw k hk
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  have hkc : k ∈ Subgroup.centralizer (W : Set Γ) := by
    have hle : Subgroup.closure {x | x ∈ K ∧ Odd (orderOf x)} ≤
        Subgroup.centralizer (W : Set Γ) := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      exact Subgroup.mem_centralizer_iff.mpr fun w hw => (hodd x hx.1 hx.2 w hw).symm
    exact hle (hK hk)
  exact Subgroup.mem_centralizer_iff.mp hkc w hw

omit [Group Γ] in
theorem opResidual_le_closure_odd' [Group Γ] (A : Subgroup Γ) :
    opResidual 2 A ≤ Subgroup.closure {x | x ∈ opResidual 2 A ∧ Odd (orderOf x)} := by
  rw [opResidual]
  refine Subgroup.closure_mono fun x hx => ?_
  exact ⟨mem_opResidual_of_coprime hx.1 hx.2, Nat.coprime_two_right.mp hx.2⟩

omit [Group Γ] in
theorem le_normalizer_opResidual' [Group Γ] (P : Subgroup Γ) :
    P ≤ Subgroup.normalizer (opResidual 2 P : Set Γ) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (opResidual_le 2 P)).mp (opResidual_normal 2 P)

section Finite

variable [Finite Γ] {P T M V : Subgroup Γ}

theorem le_sup_opResidual (hT : IsSylowOf 2 T P) : P ≤ T ⊔ opResidual 2 P := by
  have h := le_inf_sup_of_two_pow_mem hT (le_refl P) Subgroup.le_normalizer
    (le_normalizer_opResidual' P) (fun k hk => exists_pow_mem_opResidual hk)
  rwa [inf_of_le_right hT.1] at h

theorem exists_minimal_module (hPV : P ≤ Subgroup.normalizer (V : Set Γ))
    (hK : ⁅V, opResidual 2 P⁆ ≠ ⊥) :
    ∃ W : Subgroup Γ, W ≤ V ∧ P ≤ Subgroup.normalizer (W : Set Γ) ∧
      ⁅W, opResidual 2 P⁆ ≠ ⊥ ∧
      ∀ X : Subgroup Γ, X ≤ V → P ≤ Subgroup.normalizer (X : Set Γ) →
        ⁅X, opResidual 2 P⁆ ≠ ⊥ → X ≤ W → X = W := by
  obtain ⟨W, ⟨hWV, hWP, hWK⟩, hmin⟩ := (wellFounded_lt (α := Subgroup Γ)).has_min
    {X : Subgroup Γ | X ≤ V ∧ P ≤ Subgroup.normalizer (X : Set Γ) ∧ ⁅X, opResidual 2 P⁆ ≠ ⊥}
    ⟨V, le_rfl, hPV, hK⟩
  refine ⟨W, hWV, hWP, hWK, fun X hXV hXP hXK hXW => ?_⟩
  by_contra hne
  exact hmin X ⟨hXV, hXP, hXK⟩ (lt_of_le_of_ne hXW hne)

omit [Finite Γ] in
theorem commutator_eq_self_of_minimal (hV2 : ∀ v ∈ V, v ^ 2 = 1) {W : Subgroup Γ} (hWV : W ≤ V)
    (hWP : P ≤ Subgroup.normalizer (W : Set Γ)) (hWK : ⁅W, opResidual 2 P⁆ ≠ ⊥)
    (hmin : ∀ X : Subgroup Γ, X ≤ V → P ≤ Subgroup.normalizer (X : Set Γ) →
      ⁅X, opResidual 2 P⁆ ≠ ⊥ → X ≤ W → X = W) : ⁅W, opResidual 2 P⁆ = W := by
  have hKP : opResidual 2 P ≤ P := opResidual_le 2 P
  have hle : ⁅W, opResidual 2 P⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro w hw k hk
    have h1 : k * w⁻¹ * k⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hWP (hKP hk)) w⁻¹).mp
      (W.inv_mem hw)
    have h2 : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
    rw [h2]
    exact W.mul_mem hw h1
  by_contra hne
  have hlt : ⁅W, opResidual 2 P⁆ < W := lt_of_le_of_ne hle hne
  have hPn : P ≤ Subgroup.normalizer ((⁅W, opResidual 2 P⁆ : Subgroup Γ) : Set Γ) := fun g hg =>
    mem_normalizer_commutator (hWP hg) (le_normalizer_opResidual' P hg)
  have hq : ⁅⁅W, opResidual 2 P⁆, opResidual 2 P⁆ = ⊥ := by
    by_contra hq
    exact hlt.ne (hmin _ (hle.trans hWV) hPn hq hle)
  exact hWK (commutator_eq_bot_of_quadratic (opResidual_le_closure_odd' P)
    (fun w hw => hV2 w (hWV hw)) (fun k hk => hWP (hKP hk)) hq)

omit [Finite Γ] in
theorem eq_or_eq_of_irreducible {W : Subgroup Γ}
    (hmin : ∀ X : Subgroup Γ, X ≤ V → P ≤ Subgroup.normalizer (X : Set Γ) →
      ⁅X, opResidual 2 P⁆ ≠ ⊥ → X ≤ W → X = W) (hWV : W ≤ V)
    {Y : Subgroup Γ} (hYP : P ≤ Subgroup.normalizer (Y : Set Γ))
    (hY0 : W ⊓ (V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ)) ≤ Y) (hYW : Y ≤ W) :
    Y = W ⊓ (V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ)) ∨ Y = W := by
  by_cases hYW' : Y = W
  · exact Or.inr hYW'
  left
  have hcen : ⁅Y, opResidual 2 P⁆ = ⊥ := by
    by_contra hne
    exact hYW' (hmin Y (hYW.trans hWV) hYP hne hYW)
  refine le_antisymm (fun y hy => ⟨hYW hy, hWV (hYW hy), ?_⟩) hY0
  show y ∈ Subgroup.centralizer (opResidual 2 P : Set Γ)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : ⁅y, k⁆ ∈ (⁅Y, opResidual 2 P⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hy hk
  rw [hcen, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

end Finite

@[expose] def stabTrivSub (P W W₀ : Subgroup Γ)
    (hW₀ : P ≤ Subgroup.normalizer (W₀ : Set Γ)) : Subgroup Γ where
  carrier := {x | x ∈ P ∧ ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ W₀}
  mul_mem' := by
    rintro x y ⟨hxP, hx⟩ ⟨hyP, hy⟩
    refine ⟨P.mul_mem hxP hyP, fun w hw => ?_⟩
    have h1 : x * y * w * (x * y)⁻¹ * w⁻¹ =
        (x * (y * w * y⁻¹ * w⁻¹) * x⁻¹) * (x * w * x⁻¹ * w⁻¹) := by group
    rw [h1]
    exact W₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hW₀ hxP) _).mp (hy w hw)) (hx w hw)
  one_mem' := ⟨P.one_mem, fun w _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hxP, hx⟩
    refine ⟨P.inv_mem hxP, fun w hw => ?_⟩
    have h1 : x⁻¹ * w * x⁻¹⁻¹ * w⁻¹ = x⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp (hW₀ (P.inv_mem hxP)) _).mp (W₀.inv_mem (hx w hw))

theorem le_normalizer_stabTrivSub {P W W₀ : Subgroup Γ} (hW : P ≤ Subgroup.normalizer (W : Set Γ))
    (hW₀ : P ≤ Subgroup.normalizer (W₀ : Set Γ)) :
    P ≤ Subgroup.normalizer (stabTrivSub P W W₀ hW₀ : Set Γ) := by
  intro g hg
  have key : ∀ g ∈ P, ∀ x ∈ stabTrivSub P W W₀ hW₀,
      g * x * g⁻¹ ∈ stabTrivSub P W W₀ hW₀ := by
    intro g hg x hx
    refine ⟨P.mul_mem (P.mul_mem hg hx.1) (P.inv_mem hg), fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hW (P.inv_mem hg)) w).mp hw
    have h1 : g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ * w⁻¹ =
        g * (x * (g⁻¹ * w * g⁻¹⁻¹) * x⁻¹ * (g⁻¹ * w * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp (hW₀ hg) _).mp (hx.2 _ hw')
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (P.inv_mem hg) _ hx
  simpa [mul_assoc] using this

section Finite

variable [Finite Γ] {P T M V : Subgroup Γ}

theorem stabTrivSub_inf_le_pCoreOf (hT : IsSylowOf 2 T P) (hMP : M < P)
    (hMu : ∀ X : Subgroup Γ, T ≤ X → X < P → X ≤ M) {W W₀ : Subgroup Γ}
    (hW : P ≤ Subgroup.normalizer (W : Set Γ)) (hW₀ : P ≤ Subgroup.normalizer (W₀ : Set Γ))
    (hnot : ¬ opResidual 2 P ≤ stabTrivSub P W W₀ hW₀) :
    stabTrivSub P W W₀ hW₀ ⊓ T ≤ pCoreOf 2 P := by
  set N : Subgroup Γ := stabTrivSub P W W₀ hW₀ with hN
  have hNP : N ≤ P := fun x hx => hx.1
  have hNn := le_normalizer_stabTrivSub hW hW₀
  by_cases hNM : N ≤ M
  · have h33 : P ≤ Subgroup.normalizer ((N ⊓ T : Subgroup Γ) : Set Γ) :=
      three_three_a hT hMP hMu hNP hNn hNM
    have hNT : N ⊓ T ≤ P := inf_le_left.trans hNP
    have hnorm : ((N ⊓ T).subgroupOf P).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).mpr h33
    exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hNT hnorm
      (hT.2.1.to_le inf_le_right)
  · exact absurd (three_three_b hT hMu hNP hNn hNM) hnot

end Finite

structure IsModuleW (P T V W : Subgroup Γ) : Prop where
  le_V : W ≤ V
  normalized : P ≤ Subgroup.normalizer (W : Set Γ)
  comm_eq : ⁅W, opResidual 2 P⁆ = W
  ne_bot : W ≠ ⊥
  irreducible : ∀ Y : Subgroup Γ, P ≤ Subgroup.normalizer (Y : Set Γ) →
    W ⊓ (V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ)) ≤ Y → Y ≤ W →
    Y = W ⊓ (V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ)) ∨ Y = W
  pCore_comm_le : ⁅W, pCoreOf 2 P⁆ ≤ V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ)
  cen_le : ∀ x ∈ T, (∀ w ∈ W,
    x * w * x⁻¹ * w⁻¹ ∈ V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ)) → x ∈ pCoreOf 2 P

section Finite

variable [Finite Γ] {P T M V : Subgroup Γ}

theorem exists_isModuleW (hT : IsSylowOf 2 T P) (hMP : M < P)
    (hMu : ∀ X : Subgroup Γ, T ≤ X → X < P → X ≤ M) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hPV : P ≤ Subgroup.normalizer (V : Set Γ)) (hK : ⁅V, opResidual 2 P⁆ ≠ ⊥) :
    ∃ W : Subgroup Γ, IsModuleW P T V W := by
  obtain ⟨W, hWV, hWP, hWK, hmin⟩ := exists_minimal_module hPV hK
  have hcomm := commutator_eq_self_of_minimal hV2 hWV hWP hWK hmin
  have hne : W ≠ ⊥ := fun h0 => hWK (by rw [h0]; exact Subgroup.commutator_bot_left _)
  have hQP : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set Γ) := le_normalizer_pCoreOf_self P
  have hpc : ⁅W, pCoreOf 2 P⁆ ≤ V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ) := by
    have hW2 : IsPGroup 2 ↥W := fun x => ⟨1, Subtype.ext (by simpa using hV2 x (hWV x.2))⟩
    have hQ2 : IsPGroup 2 ↥(pCoreOf 2 P) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 P
    have hQW : pCoreOf 2 P ≤ Subgroup.normalizer (W : Set Γ) := fun q hq =>
      hWP (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 P hq)
    have hlt := commutator_lt_of_isPGroup hW2 hQ2 hQW hne
    have hYP : P ≤ Subgroup.normalizer ((⁅W, pCoreOf 2 P⁆ : Subgroup Γ) : Set Γ) := fun g hg =>
      mem_normalizer_commutator (hWP hg) (hQP hg)
    have hYK : ⁅⁅W, pCoreOf 2 P⁆, opResidual 2 P⁆ = ⊥ := by
      by_contra hne'
      exact hlt.ne (hmin _ (hlt.le.trans hWV) hYP hne' hlt.le)
    intro y hy
    refine ⟨hWV (hlt.le hy), Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    have h1 : ⁅y, k⁆ ∈ (⁅⁅W, pCoreOf 2 P⁆, opResidual 2 P⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator hy hk
    rw [hYK, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  refine ⟨W, hWV, hWP, hcomm, hne,
    fun Y hYP hY0 hYW => eq_or_eq_of_irreducible hmin hWV hYP hY0 hYW, hpc, ?_⟩
  have hW₀ : P ≤ Subgroup.normalizer ((V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ) :
      Subgroup Γ) : Set Γ) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hPV hg,
      B6.le_normalizer_centralizer (le_normalizer_opResidual' P) hg⟩
  have hnot : ¬ opResidual 2 P ≤ stabTrivSub P W (V ⊓ Subgroup.centralizer
      (opResidual 2 P : Set Γ)) hW₀ := by
    intro hle
    apply hne
    have hWW₀ : W ≤ V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ) := by
      rw [← hcomm, Subgroup.commutator_le]
      intro w hw k hk
      have h1 := (hle hk).2 w hw
      have h2 : ⁅w, k⁆ = (k * w * k⁻¹ * w⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
      rw [h2]
      exact (V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ)).inv_mem h1
    have : ⁅W, opResidual 2 P⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro w hw k hk
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (hWW₀ hw).2 k hk).symm
    rw [← hcomm, this]
  intro x hxT hx
  exact stabTrivSub_inf_le_pCoreOf hT hMP hMu hWP hW₀ hnot ⟨⟨hT.1 hxT, hx⟩, hxT⟩

end Finite

end CFSG.CGT.PushingUpLit.BHS7

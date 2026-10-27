module

public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCuts
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarConj

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.AGLEmbedding.LeviBlock
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r : ℕ}

theorem scalar_eq_one_of_isometry {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgs : g ∈ scalars K V) {v₀ : V}
    (hv₀ : Q v₀ ≠ 0) : g = 1 := by
  obtain ⟨a, ha⟩ := mem_scalars.1 hgs
  have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg v₀
  rw [ha, QuadraticMap.map_smul, smul_eq_mul] at h1
  have hcc : a * a = 1 := mul_right_cancel₀ hv₀ (by rw [one_mul]; exact h1)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h8 : (a - 1) ^ 2 = 0 := by linear_combination hcc + (1 - a) * h2
  have ha1 : a = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h8)
  exact LinearEquiv.ext fun v => by rw [ha, ha1, one_smul]; rfl

theorem exists_quadTail_ne_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ v : (Fin r ⊕ Fin r → K) × (Fin 2 → K), quadTail r (minusTailForm K b c) v ≠ 0 := by
  refine ⟨((0 : Fin r ⊕ Fin r → K), Pi.single 0 1), ?_⟩
  rw [quadTail_tail, minusTailForm_apply]
  simp

theorem scalars_subgroupOf_orthDerived_eq_bot (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (scalars K ((Fin r ⊕ Fin r → K) × (Fin 2 → K))).subgroupOf
      (orthDerived (quadTail r (minusTailForm K b c))) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  obtain ⟨v₀, hv₀⟩ := exists_quadTail_ne_zero (r := r) hirr
  have hgs : ((g : ↥(orthDerived (quadTail r (minusTailForm K b c)))) :
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) ∈
        scalars K ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) := Subgroup.mem_subgroupOf.1 hg
  have hgo := orthDerived_le_orthogonalGroup_of_commutator
    (quadTail r (minusTailForm K b c)) (g : ↥(orthDerived (quadTail r (minusTailForm K b c)))).2
  have h1 := scalar_eq_one_of_isometry hgo hgs hv₀
  exact Subtype.ext h1

theorem exists_semiSim_aux {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQnd : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ finrank K V)
    (hD4 : finrank K V = 8 → ¬ ∃ U : Submodule K V, finrank K U = 4 ∧ ∀ u ∈ U, Q u = 0)
    (hE : orthDerived Q = orthElementaryGroup Q)
    (hbot : (scalars K V).subgroupOf (orthDerived Q) = ⊥) (α : MulAut ↥(orthElementaryGroup Q)) :
    ∃ (σ : K ≃+* K) (F : V ≃+ V) (hF : ∀ (a : K) (v : V), F (a • v) = σ a • F v) (μ : K),
      μ ≠ 0 ∧ (∀ v, Q (F v) = μ * σ (Q v)) ∧
        ∀ g : ↥(orthElementaryGroup Q),
          ((α g : ↥(orthElementaryGroup Q)) : V ≃ₗ[K] V) =
            semilinConj F σ hF (g : V ≃ₗ[K] V) := by
  classical
  let e₁ : ↥(orthElementaryGroup Q) ≃* ↥(orthDerived Q) := MulEquiv.subgroupCongr hE.symm
  let e₂ : ProjOrthDerived Q ≃* ↥(orthDerived Q) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let ε : ↥(orthElementaryGroup Q) ≃* ProjOrthDerived Q := e₁.trans e₂.symm
  obtain ⟨σ, F, hF, μ, hμ, hFQ, hind⟩ :=
    orthogonal_aut_semilinear_of_seven_le Q hQnd hdim hD4 ((MulAut.congr ε) α)
  refine ⟨σ, F, hF, μ, hμ, hFQ, fun g => ?_⟩
  have hg0 : (g : V ≃ₗ[K] V) ∈ orthDerived Q := by rw [hE]; exact g.2
  have hg1 : semilinConj F σ hF (g : V ≃ₗ[K] V) ∈ orthDerived Q :=
    semilinConj_mem_orthDerived F σ hF μ hFQ hg0
  have hα0 : ((α g : ↥(orthElementaryGroup Q)) : V ≃ₗ[K] V) ∈ orthDerived Q := by
    rw [hE]; exact (α g).2
  have key := hind ⟨g, hg0⟩ ⟨semilinConj F σ hF g, hg1⟩ fun v => rfl
  have hε : ε g = QuotientGroup.mk ⟨g, hg0⟩ := by
    apply e₂.injective
    simp only [ε, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have hεα : ε (α g) = QuotientGroup.mk ⟨(α g : V ≃ₗ[K] V), hα0⟩ := by
    apply e₂.injective
    simp only [ε, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have h2 : (MulAut.congr ε α) (ε g) = ε (α g) := by
    simp [MulAut.congr_apply]
  rw [hε, hεα] at h2
  rw [h2] at key
  have h3 := QuotientGroup.eq.1 key
  have h4 := hbot ▸ h3
  rw [Subgroup.mem_bot] at h4
  have h5 : (⟨(α g : V ≃ₗ[K] V), hα0⟩ : ↥(orthDerived Q))⁻¹ *
      ⟨semilinConj F σ hF g, hg1⟩ = 1 := h4
  have h6 := inv_mul_eq_one.1 h5
  exact congrArg Subtype.val h6

theorem exists_semiSim (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (α : MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
    ∃ (σ : K ≃+* K) (F : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃+
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))
      (hF : ∀ (a : K) (v : (Fin r ⊕ Fin r → K) × (Fin 2 → K)), F (a • v) = σ a • F v) (μ : K),
      μ ≠ 0 ∧ (∀ v, quadTail r (minusTailForm K b c) (F v) =
          μ * σ (quadTail r (minusTailForm K b c) v)) ∧
        ∀ g : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))),
          ((α g : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
            ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) =
            semilinConj F σ hF (g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) := by
  have hani := anisotropic_minusTailForm hirr
  have hfr : finrank K ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) = 2 * r + 2 := by
    rw [finrank_tailSpace, finrank_fin_two_fun]
  refine exists_semiSim_aux (quadTail r (minusTailForm K b c))
    (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)) (by omega) ?_
    (commutator_orthogonalGroup_quadTail_minus hr hirr)
    (scalars_subgroupOf_orthDerived_eq_bot hirr) α
  rintro h8 ⟨U, hU4, hU0⟩
  have := finrank_le_of_totSing_tail hani hU0
  omega

structure SemiData (K : Type) [Field K] (r : ℕ) (b c : K) where
  σ : K ≃+* K
  F : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃+ ((Fin r ⊕ Fin r → K) × (Fin 2 → K))
  hF : ∀ (a : K) (v : (Fin r ⊕ Fin r → K) × (Fin 2 → K)), F (a • v) = σ a • F v
  μ : K
  hμ : μ ≠ 0
  hFQ : ∀ v, quadTail r (minusTailForm K b c) (F v) =
    μ * σ (quadTail r (minusTailForm K b c) v)

@[expose] def SemiData.Induces {r : ℕ} {b c : K} (S : SemiData K r b c)
    (α : MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : Prop :=
  ∀ g : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))),
    ((α g : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) =
      semilinConj S.F S.σ S.hF (g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _)

theorem exists_semiData (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (α : MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
    ∃ S : SemiData K r b c, S.Induces α := by
  obtain ⟨σ, F, hF, μ, hμ, hFQ, h⟩ := exists_semiSim hr hirr α
  exact ⟨⟨σ, F, hF, μ, hμ, hFQ⟩, h⟩

section Flag

variable {s : ℕ} {d : Fin (s + 1) → ℕ}

def semilinImage {V : Type} [AddCommGroup V] [Module K V] (F : V ≃+ V) (σ : K ≃+* K)
    (hF : ∀ (a : K) (v : V), F (a • v) = σ a • F v) (S : Submodule K V) : Submodule K V where
  carrier := F '' (S : Set V)
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, S.add_mem hx hy, map_add F x y⟩
  zero_mem' := ⟨0, S.zero_mem, map_zero F⟩
  smul_mem' := by
    rintro a _ ⟨x, hx, rfl⟩
    exact ⟨σ.symm a • x, S.smul_mem _ hx, by rw [hF, σ.apply_symm_apply]⟩

theorem natCard_semilinImage {V : Type} [AddCommGroup V] [Module K V] (F : V ≃+ V) (σ : K ≃+* K)
    (hF : ∀ (a : K) (v : V), F (a • v) = σ a • F v) (S : Submodule K V) :
    Nat.card (semilinImage F σ hF S) = Nat.card S := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun x : S => (⟨F x, ⟨x, x.2, rfl⟩⟩ :
    semilinImage F σ hF S)) ⟨fun x y h => Subtype.ext (F.injective (congrArg Subtype.val h)),
      fun ⟨_, ⟨x, hx, rfl⟩⟩ => ⟨⟨x, hx⟩, rfl⟩⟩)

theorem mem_flag_iff_of_normalizes (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hd : OrthCuts r d)
    {σ : K ≃+* K} {F : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃+ ((Fin r ⊕ Fin r → K) × (Fin 2 → K))}
    (hF : ∀ (a : K) (v : (Fin r ⊕ Fin r → K) × (Fin 2 → K)), F (a • v) = σ a • F v) {μ : K}
    (hFQ : ∀ v, quadTail r (minusTailForm K b c) (F v) =
      μ * σ (quadTail r (minusTailForm K b c) v))
    (hnorm : ∀ u ∈ orthParab r (minusTailForm K b c) d, ∃ x ∈ orthParab r (minusTailForm K b c) d,
      ∀ v, ((u : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
          ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) v =
        F (((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
          ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) (F.symm v))) (i : Fin (s + 1))
    (v : (Fin r ⊕ Fin r → K) × (Fin 2 → K)) :
    F v ∈ tailFlag K (Fin 2 → K) r (d i) ↔ v ∈ tailFlag K (Fin 2 → K) r (d i) := by
  have hani := anisotropic_minusTailForm hirr
  set T := tailFlag K (Fin 2 → K) r (d i) with hT
  have hdi : d i ≤ r := (hd.mono.monotone (Fin.le_last i)).trans hd.last
  have hWT : semilinImage F σ hF T = T := by
    rcases Nat.eq_zero_or_pos (d i) with h0 | hpos
    · have hbot : T = ⊥ := by rw [hT, h0, tailFlag_zero]
      rw [hbot]
      refine le_antisymm ?_ bot_le
      rintro _ ⟨x, hx, rfl⟩
      have hx0 : x = 0 := (Submodule.mem_bot K).1 (SetLike.mem_coe.1 hx)
      rw [hx0, map_zero]
      exact Submodule.zero_mem _
    · have hA : ∃ a : Fin 2 → K, a ≠ 0 := ⟨Pi.single 0 1, fun h => by
        simpa using congrFun h 0⟩
      have hWinv : ∀ u ∈ tailUnipotent r (minusTailForm K b c),
          (semilinImage F σ hF T).map ((u : _ ≃ₗ[K] _) : _ →ₗ[K] _) ≤ semilinImage F σ hF T := by
        intro u hu
        have hux : (⟨u, tailUnipotent_le hu⟩ : ↥(orthElementaryGroup (quadTail r
            (minusTailForm K b c)))) ∈ orthParab r (minusTailForm K b c) d := by
          rw [mem_orthParab]
          intro j
          exact map_tailFlag_of_mem_tailUnipotent hani
            ((hd.mono.monotone (Fin.le_last j)).trans hd.last) hu
        obtain ⟨x, hx, hxu⟩ := hnorm _ hux
        rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        refine ⟨((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
          ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) w, ?_, ?_⟩
        · have := mapsTo_of_mem_orthParab hx i w hw
          exact this
        · have := hxu (F w)
          rw [AddEquiv.symm_apply_apply] at this
          exact this.symm
      have hWs : ∀ w ∈ semilinImage F σ hF T, quadTail r (minusTailForm K b c) w = 0 := by
        rintro _ ⟨x, hx, rfl⟩
        rw [hFQ, quadTail_eq_zero_of_mem_tailFlag hx, map_zero, mul_zero]
      have hW0 : semilinImage F σ hF T ≠ ⊥ := by
        intro hbot
        have hTpos : T ≠ ⊥ := by
          intro h
          have := finrank_tailFlag (K := K) (A := Fin 2 → K) hdi
          rw [← hT, h, finrank_bot] at this
          omega
        obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTpos
        have : F x ∈ semilinImage F σ hF T := ⟨x, hx, rfl⟩
        rw [hbot, Submodule.mem_bot] at this
        exact hx0 (F.injective (by rw [this, map_zero]))
      obtain ⟨k, hk1, hkr, hk⟩ := eq_tailFlag_of_invariant hani hA hW0 hWs hWinv
      have hcard := natCard_semilinImage F σ hF T
      rw [hk] at hcard
      have h1 : Nat.card (tailFlag K (Fin 2 → K) r k) = Nat.card K ^ k := by
        rw [Module.natCard_eq_pow_finrank (K := K), finrank_tailFlag hkr]
      have h2 : Nat.card T = Nat.card K ^ d i := by
        rw [Module.natCard_eq_pow_finrank (K := K), hT, finrank_tailFlag hdi]
      rw [h1, h2] at hcard
      have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
      have hkd : k = d i := Nat.pow_right_injective hK2 hcard
      rw [hk, hkd]
  constructor
  · intro h
    have h' : F v ∈ semilinImage F σ hF T := by rw [hWT]; exact h
    obtain ⟨v', hv', hvv'⟩ := h'
    rwa [F.injective hvv'] at hv'
  · intro h
    have h' : F v ∈ semilinImage F σ hF T := ⟨v, h, rfl⟩
    rwa [hWT] at h'

end Flag

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

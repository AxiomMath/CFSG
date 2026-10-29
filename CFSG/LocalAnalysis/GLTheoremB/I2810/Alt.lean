module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.AltBasic
import CFSG.LocalAnalysis.GLTheoremB.I2810.AltOverlap
import CFSG.LocalAnalysis.GLTheoremB.I2810.AltDegree
import CFSG.LocalAnalysis.GLTheoremB.I2810.AltCent
import CFSG.LocalAnalysis.GLTheoremB.I2810.AltCentre
import CFSG.LocalAnalysis.GLTheoremB.I2810.Blocks
import CFSG.LocalAnalysis.GLTheoremB.I2810.BlocksChief

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section CaseOneTwo
open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem omega_alt_iso {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (h : Setup28 W K S) (hR : Red28 W K S) {a : X} {U₁ U₂ : Subgroup X}
    (hts : TransSection K (vOf W K S) U₁ U₂ a) (hAlt : InAlt ↥(bar W K))
    (hΩ : OmegaModelWith Q W K a U₁ U₂) :
    ∃ n₀ : ℕ, 5 ≤ n₀ ∧ Nonempty (↥(alternatingGroup (Fin n₀)) ≃*
      (↥(StatedOmega Q) ⧸ Subgroup.center ↥(StatedOmega Q))) := by
  obtain ⟨θ, t, hsurj, hkerW, -, -, -, -, hiso⟩ := hΩ
  obtain ⟨-, n₀, hn₀, ⟨eA⟩⟩ := hAlt
  refine ⟨n₀, hn₀, ?_⟩
  haveI : Group.IsPerfect ↥(bar W K) := hR.quasi.1
  have hnt : ∃ k : ↥K, θ k ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨k, hk, x, hx, hxk⟩ := hts.nontriv
    obtain ⟨φ, -, hφker, hequiv⟩ := hiso
    have h1 := hequiv ⟨k, hk⟩ ⟨x, hx⟩ ⟨k * x * k⁻¹, hts.inv₁ k hk x hx⟩ rfl
    rw [hall ⟨k, hk⟩] at h1
    simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec, ofAdd_toAdd] at h1
    have h2 : φ (⟨k * x * k⁻¹, hts.inv₁ k hk x hx⟩ * (⟨x, hx⟩ : ↥U₁)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hφker _).1 h2
    apply hxk
    have h4 : ⁅x, k⁆ = (k * x * k⁻¹ * x⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h4]
    exact U₂.inv_mem h3
  set θ' := AltBasic.barLift (W := W) θ hkerW with hθ'
  have hcomp : ∀ k : ↥K, θ' (toBar W K k) = θ k := AltBasic.barLift_toBar θ hkerW
  have hsurj' : Function.Surjective θ' := by
    intro g
    obtain ⟨k, rfl⟩ := hsurj g
    exact ⟨toBar W K k, hcomp k⟩
  have hnt' : ∃ g, θ' g ≠ 1 := by
    obtain ⟨k, hk⟩ := hnt
    exact ⟨toBar W K k, by rw [hcomp]; exact hk⟩
  have hker : θ'.ker ≤ Subgroup.center ↥(bar W K) :=
    AltBasic.ker_le_center_of_quasisimple hR.quasi θ' hnt'
  obtain ⟨eΩ⟩ := AltBasic.nonempty_quotCenter_equiv θ' hsurj' hker
  exact ⟨eA.symm.trans eΩ⟩

theorem alt_omega_plus_degree {n₀ n : ℕ} (hn₀ : 5 ≤ n₀) (hn : 1 ≤ n)
    (e : ↥(alternatingGroup (Fin n₀)) ≃*
      (↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))) ⧸
        Subgroup.center ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))))) : n = 2 :=
  AltDegree.plus_degree hn₀ hn e

theorem alt_omega_minus_degree {n₀ n : ℕ} (hn₀ : 5 ≤ n₀) (hn : 1 ≤ n)
    (e : ↥(alternatingGroup (Fin n₀)) ≃*
      (↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) ⧸
        Subgroup.center ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)))) : n = 1 :=
  AltDegree.minus_degree hn₀ hn e

theorem omegaMinusFour_equiv (n : ℕ) (hn : n = 1) :
    ∃ (θ' : ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) ≃* ↥(alternatingGroup (Fin 5)))
      (β : (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → ZMod 2) ≃+ AltHeart 5),
      ∀ (g : ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)))
          (v : Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → ZMod 2),
        β (Matrix.mulVec ((g : GL (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) (ZMod 2)) :
            Matrix _ _ (ZMod 2)) v) = altHeartAct 5 (θ' g : Equiv.Perm (Fin 5)) (β v) := by
  subst hn
  exact AltOverlap.equiv4

theorem omegaMinusFour_swap (n : ℕ) (hn : n = 1)
    (θ' : ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) ≃* ↥(alternatingGroup (Fin 5)))
    (β : (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → ZMod 2) ≃+ AltHeart 5)
    (hβ : ∀ (g : ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)))
          (v : Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → ZMod 2),
        β (Matrix.mulVec ((g : GL (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) (ZMod 2)) :
            Matrix _ _ (ZMod 2)) v) = altHeartAct 5 (θ' g : Equiv.Perm (Fin 5)) (β v)) :
    ∀ t : GL (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) (ZMod 2), IsTransvection t →
      (∀ x, StatedQuadMinus (n + 1) (ZMod 2) 1 1 (Matrix.mulVec (t : Matrix _ _ (ZMod 2)) x) =
        StatedQuadMinus (n + 1) (ZMod 2) 1 1 x) →
      t ∈ Subgroup.normalizer (StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1) : Set _) →
      ∃ σ : Equiv.Perm (Fin 5), σ.IsSwap ∧
        ∀ g g' : ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)),
          (g' : GL (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) (ZMod 2)) = t * g * t⁻¹ →
            (θ' g' : Equiv.Perm (Fin 5)) = σ * (θ' g : Equiv.Perm (Fin 5)) * σ⁻¹ := by
  subst hn
  intro t ht hQ _
  exact AltOverlap.swap_of_transvection4 θ' t ht hQ

theorem omega_to_alt_five {a : X} {U₁ U₂ : Subgroup X} (hm : OmegaMinus W K a U₁ U₂ 1) :
    AltModel W K a U₁ U₂ := by
  obtain ⟨θ, t, hsurj, hker, htr, hQt, htn, hconj, hiso⟩ := hm
  obtain ⟨θ', β, hβ⟩ := omegaMinusFour_equiv 1 rfl
  obtain ⟨σ, hσ, hswap⟩ := omegaMinusFour_swap 1 rfl θ' β hβ t htr hQt htn
  refine ⟨5, θ'.toMonoidHom.comp θ, σ, le_rfl, θ'.surjective.comp hsurj, fun k hk => ?_, hσ,
    fun k k' hk' => hswap (θ k) (θ k') (hconj k k' hk'), ?_⟩
  · simp [hker k hk]
  · exact AltBasic.chiefFactorIso_comp hiso θ'.toMonoidHom β _ fun g v => hβ g v

theorem omegaPlusSix_equiv (n : ℕ) (hn : n = 2) :
    ∃ (θ' : ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))) ≃* ↥(alternatingGroup (Fin 8)))
      (β : (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ≃+ AltHeart 8),
      ∀ (g : ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))))
          (v : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2),
        β (Matrix.mulVec ((g : GL (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2)) : Matrix _ _ (ZMod 2)) v) =
          altHeartAct 8 (θ' g : Equiv.Perm (Fin 8)) (β v) := by
  subst hn
  exact AltOverlap.equiv6

theorem omegaPlusSix_swap (n : ℕ) (hn : n = 2)
    (θ' : ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))) ≃* ↥(alternatingGroup (Fin 8)))
    (β : (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ≃+ AltHeart 8)
    (hβ : ∀ (g : ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))))
          (v : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2),
        β (Matrix.mulVec ((g : GL (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2)) : Matrix _ _ (ZMod 2)) v) =
          altHeartAct 8 (θ' g : Equiv.Perm (Fin 8)) (β v)) :
    ∀ t : GL (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2), IsTransvection t →
      (∀ x, StatedQuadPlus (n + 1) (ZMod 2) (Matrix.mulVec (t : Matrix _ _ (ZMod 2)) x) =
        StatedQuadPlus (n + 1) (ZMod 2) x) →
      t ∈ Subgroup.normalizer (StatedOmega (StatedQuadPlus (n + 1) (ZMod 2)) : Set _) →
      ∃ σ : Equiv.Perm (Fin 8), σ.IsSwap ∧
        ∀ g g' : ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))),
          (g' : GL (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2)) = t * g * t⁻¹ →
            (θ' g' : Equiv.Perm (Fin 8)) = σ * (θ' g : Equiv.Perm (Fin 8)) * σ⁻¹ := by
  subst hn
  intro t ht hQ _
  exact AltOverlap.swap_of_transvection6 θ' t ht hQ

theorem omega_to_alt_eight {a : X} {U₁ U₂ : Subgroup X} (hm : OmegaPlus W K a U₁ U₂ 2) :
    AltModel W K a U₁ U₂ := by
  obtain ⟨θ, t, hsurj, hker, htr, hQt, htn, hconj, hiso⟩ := hm
  obtain ⟨θ', β, hβ⟩ := omegaPlusSix_equiv 2 rfl
  obtain ⟨σ, hσ, hswap⟩ := omegaPlusSix_swap 2 rfl θ' β hβ t htr hQt htn
  refine ⟨8, θ'.toMonoidHom.comp θ, σ, by norm_num, θ'.surjective.comp hsurj, fun k hk => ?_, hσ,
    fun k k' hk' => hswap (θ k) (θ k') (hconj k k' hk'), ?_⟩
  · simp [hker k hk]
  · exact AltBasic.chiefFactorIso_comp hiso θ'.toMonoidHom β _ fun g v => hβ g v

theorem centMax_of_alt_center (h : Setup28 W K S) (hR : Red28 W K S) {a : X} {U₁ U₂ : Subgroup X}
    (_hts : TransSection K (vOf W K S) U₁ U₂ a) (haS : a ∈ S) (hna : a ∉ kerAct W K S)
    (hS2 : Nat.card ↥(indAut W K S) = 2) (hm : AltModel W K a U₁ U₂)
    (hZ : Subgroup.center ↥(bar W K) = ⊥) : CentMax W K S a :=
  AltCent.centMax_core h hR haS hna hS2 hZ hm

theorem threeElt_of_alt_center (h : Setup28 W K S) (hR : Red28 W K S) {a : X}
    {U₁ U₂ : Subgroup X} (_hts : TransSection K (vOf W K S) U₁ U₂ a) (haS : a ∈ S)
    (_hna : a ∉ kerAct W K S) (_hS2 : Nat.card ↥(indAut W K S) = 2) (hm : AltModel W K a U₁ U₂)
    (hZ : Subgroup.center ↥(bar W K) = ⊥) : ThreeElt W K S a :=
  AltCent.threeElt_core h hR haS hZ hm

theorem hyp28Two_center (h : Setup28 W K S) (h2 : Hyp28Two W K S) :
    Subgroup.center ↥(bar W K) = ⊥ :=
  AltCentre.center_bot_of_hyp28Two h h2

theorem alt_final (h : Setup28 W K S) (hR : Red28 W K S) {U₁ U₂ : Subgroup X}
    (sf : SingleFactor K (vOf W K S) U₁ U₂)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S)
    (hS2 : Nat.card ↥(indAut W K S) = 2) (hblock : IsGLBlock (⊤ : Subgroup X) K) {a : X}
    (haS : a ∈ S) (hna : a ∉ kerAct W K S) (hm : AltModel W K a U₁ U₂) :
    ∃ (n : ℕ) (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))),
      5 ≤ n ∧ ActsLikeTranspositionCQ (bar W S) (bar W K) n e ∧ IsGLBlock (⊤ : Subgroup X) K ∧
        ∀ V U : Subgroup X, IsNoncentralChiefFactor K (pCoreOf 2 K) V U →
          ChiefFactorIso K U V
            ((e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(bar W K)))).comp (toBar W K))
            (fun σ x => altHeartAct n (σ : Equiv.Perm (Fin n)) x) := by
  obtain ⟨m, θ, σ, hm5, hsurj, hker, hσ, hconj, hiso⟩ := hm
  obtain ⟨e, he⟩ := AltBasic.exists_iso_of_alt hR hm5 θ hsurj hker
  have hρ : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(bar W K)))).comp
      (toBar W K) = θ :=
    MonoidHom.ext fun k => he k
  refine ⟨m, e, hm5, ⟨hS2, σ, hσ, ?_⟩, hblock, fun V U hU => ?_⟩
  · have hKa : ∀ k : X, k ∈ K → a * k * a⁻¹ ∈ K := fun k hk =>
      (Subgroup.mem_normalizer_iff.1 (h.hN haS) k).1 hk
    have hmem : (QuotientGroup.mk a : X ⧸ W) ∈
        Subgroup.normalizer ((bar W K : Subgroup (X ⧸ W)) : Set (X ⧸ W)) :=
      Subgroup.le_normalizer_map (QuotientGroup.mk' W) ⟨a, h.hN haS, rfl⟩
    set α : MulAut ↥(bar W K) := (bar W K).normalizerMonoidHom ⟨QuotientGroup.mk a, hmem⟩ with hα
    have hαS : α ∈ indAut W K S :=
      ⟨⟨QuotientGroup.mk a, hmem⟩, Subgroup.mem_subgroupOf.2 ⟨a, haS, rfl⟩, rfl⟩
    have hαk : ∀ k k' : ↥K, (k' : X) = a * k * a⁻¹ → α (toBar W K k) = toBar W K k' := by
      intro k k' hk'
      apply Subtype.ext
      show (QuotientGroup.mk a : X ⧸ W) * QuotientGroup.mk (k : X) * (QuotientGroup.mk a)⁻¹ =
        QuotientGroup.mk (k' : X)
      rw [hk']
      simp
    have hα1 : α ≠ 1 := by
      intro h1
      apply hna
      refine ⟨haS, fun k hk => ?_⟩
      have h0 := hαk ⟨k, hk⟩ ⟨a * k * a⁻¹, hKa k hk⟩ rfl
      rw [h1, MulAut.one_apply] at h0
      have h2 : (QuotientGroup.mk (k : X) : X ⧸ W) = QuotientGroup.mk (a * k * a⁻¹) :=
        congrArg Subtype.val h0
      have h3 : (k : X)⁻¹ * (a * k * a⁻¹) ∈ W := QuotientGroup.eq.1 h2
      have h4 := Subgroup.Normal.conj_mem inferInstance _ h3 (k : X)
      have h5 : ⁅a, k⁆ = (k : X) * ((k : X)⁻¹ * (a * k * a⁻¹)) * (k : X)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [h5]
      exact (by simpa using h4)
    have hcases : ∀ φ ∈ indAut W K S, φ = 1 ∨ φ = α := by
      intro φ hφ
      by_cases h1 : φ = 1
      · exact Or.inl h1
      · refine Or.inr ?_
        have := AltBasic.eq_of_card_two hS2 ⟨φ, hφ⟩ ⟨α, hαS⟩
          (fun h' => h1 (congrArg Subtype.val h')) (fun h' => hα1 (congrArg Subtype.val h'))
        exact congrArg Subtype.val this
    have hσ2 : σ * σ = 1 := by
      obtain ⟨x, y, -, hs⟩ := hσ
      rw [hs]
      exact Equiv.swap_mul_self x y
    have hC2 : MulAut.conjNormal (H := alternatingGroup (Fin m)) σ *
        MulAut.conjNormal (H := alternatingGroup (Fin m)) σ = 1 := by
      rw [← map_mul, hσ2, map_one]
    have hzp : ∀ ρ ∈ Subgroup.zpowers (MulAut.conjNormal (H := alternatingGroup (Fin m)) σ),
        ρ = 1 ∨ ρ = MulAut.conjNormal (H := alternatingGroup (Fin m)) σ := by
      intro ρ hρ
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hρ
      obtain ⟨i, rfl | rfl⟩ := Int.even_or_odd' j
      · left
        rw [zpow_mul, zpow_two, hC2, one_zpow]
      · right
        rw [zpow_add_one, zpow_mul, zpow_two, hC2, one_zpow, one_mul]
    have hind : InducesOn e α (MulAut.conjNormal (H := alternatingGroup (Fin m)) σ) := by
      intro x
      obtain ⟨k, rfl⟩ := BlocksChief.toBar_surjective W K x
      rw [hαk k ⟨a * k * a⁻¹, hKa k k.2⟩ rfl, he, he]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact hconj k ⟨a * k * a⁻¹, hKa k k.2⟩ rfl
    refine ⟨fun φ hφ => ?_, fun ρ hρ => ?_⟩
    · rcases hcases φ hφ with rfl | rfl
      · exact ⟨1, Subgroup.one_mem _, fun x => by simp⟩
      · exact ⟨_, Subgroup.mem_zpowers _, hind⟩
    · rcases hzp ρ hρ with rfl | rfl
      · exact ⟨1, Subgroup.one_mem _, fun x => by simp⟩
      · exact ⟨α, hαS, hind⟩
  · rw [hρ]
    exact chief_transfer h hR sf hE θ _ hiso hU

end CaseOneTwo

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

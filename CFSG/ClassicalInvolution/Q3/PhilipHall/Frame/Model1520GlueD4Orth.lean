module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Orth
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinear
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Rigid

variable {K : Type} [Field K] [Finite K]

theorem eichlerImages_cube {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (hK3 : Nat.card K = 3) {W : Submodule K V} {s : ProjOrthDerived Q}
    (hs : s ∈ eichlerImages Q W) : s ^ 3 = 1 := by
  obtain ⟨P, -, -, w, hw, hE', rfl⟩ := hs
  have hpol : polar Q P.e w = 0 := (HypPair.mem_perp.mp hw.2).1
  have h3 : (⟨eichler Q P.e w, hE'⟩ : orthDerived Q) * ⟨eichler Q P.e w, hE'⟩ *
      ⟨eichler Q P.e w, hE'⟩ = 1 := Subtype.ext (eichler_pow_three hK3 hpol)
  rw [pow_succ, pow_two, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h3]
  rfl

theorem rigid3_of_orth_abs_set (hK3 : Nat.card K = 3) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (W : Submodule K V)
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate) (hW3 : 3 ≤ finrank K W)
    (hW'3 : 3 ≤ finrank K (suppPerp Q W)) (τ : ProjOrthDerived Q)
    (S : Set (ProjOrthDerived Q))
    (hS : eichlerImages Q W ∪ eichlerImages Q (suppPerp Q W) ⊆ S) (hS3 : ∀ s ∈ S, s ^ 3 = 1)
    (hτ : ∀ s ∈ S, s * τ = τ * s)
    (hind : ∀ α : MulAut (ProjOrthDerived Q), (∃ k : ℕ, α ^ (3 ^ k) = 1) → (∀ s ∈ S, α s = s) →
      CFSG.RankThree.PartOne.KCOrthogonalAut.InducedBySemilinear Q α) :
    Rigid3 (ProjOrthDerived Q) τ := by
  have hK2 : Nat.card K = 2 → False := fun h => by omega
  have hW' : (polarBilin (Q.comp (suppPerp Q W).subtype)).Nondegenerate :=
    nondegenerate_polarBilin_restrict
      (polarNondegOn_suppPerp hQ (polarNondegOn_of_nondegenerate hW))
  have hdim : 3 ≤ finrank K (V) := hW3.trans (Submodule.finrank_le W)
  refine ⟨S, fun s hs => ⟨hS3 s hs, hτ s hs⟩, ?_⟩
  intro α ⟨k, hk⟩ hfixS
  obtain ⟨σ, F, hF, μ, -, hFQ, hκ⟩ := hind α ⟨k, hk⟩ hfixS
  have hcommU : ∀ U : Submodule K (V), (U = W ∨ U = suppPerp Q W) →
      EichlerComm Q U F := by
    intro U hU P he hf w hw v
    have hpol : polar Q P.e w = 0 := (HypPair.mem_perp.mp hw.2).1
    have hEmem : eichler Q P.e w ∈ orthDerived Q :=
      eichler_mem_orthDerived_of_regular hQ hdim (fun h => absurd h hK2) P hw.2
    have hs : (QuotientGroup.mk ⟨eichler Q P.e w, hEmem⟩ : ProjOrthDerived Q) ∈
        eichlerImages Q W ∪ eichlerImages Q (suppPerp Q W) := by
      rcases hU with rfl | rfl
      · exact Or.inl ⟨P, he, hf, w, hw, hEmem, rfl⟩
      · exact Or.inr ⟨P, he, hf, w, hw, hEmem, rfl⟩
    exact commute_of_fixed_order_three hK3 F σ hF μ hFQ α hκ hEmem (eichler_pow_three hK3 hpol)
      P.e_ne_zero (hfixS _ (hS hs)) v
  have hscal : ∀ U : Submodule K (V), (U = W ∨ U = suppPerp Q W) →
      (polarBilin (Q.comp U.subtype)).Nondegenerate → 3 ≤ finrank K U →
      (∀ c, σ c = c) ∧ ∃ c : K, c ≠ 0 ∧ ∀ w ∈ U, F w = c • w := by
    intro U hU hUnd hU3
    have hsing : ∃ e ∈ U, e ≠ 0 ∧ Q e = 0 := by
      obtain ⟨P'⟩ := CFSG.RankThree.Classical.nonempty_hypPair_of_finite hUnd hU3
      exact ⟨(P'.e : V), P'.e.2, fun h0 => P'.e_ne_zero (Subtype.ext h0), P'.Q_e⟩
    exact scalar_restriction_of_eichlerComm F σ (hcommU U hU) μ hFQ hQ hUnd hU3 hsing
      (elementaryMapsMem_of_regular hUnd hU3 (fun h => absurd h hK2)) hF
  obtain ⟨hσ, cW, hcW0, hcW⟩ := hscal W (Or.inl rfl) hW hW3
  obtain ⟨-, cW', hcW'0, hcW'⟩ := hscal _ (Or.inr rfl) hW' hW'3
  have hsq : ∀ c : K, c ≠ 0 → c * c = 1 := by
    intro c hc0
    have := Fintype.ofFinite K
    have hcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK3]
    have h := FiniteField.pow_card_sub_one_eq_one c hc0
    rw [hcard] at h
    simpa [pow_two] using h
  have hFF : ∀ y, F (F y) = y := by
    intro y
    have hWreg := polarNondegOn_of_nondegenerate hW
    obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp
      (by rw [(isCompl_suppPerp hWreg).sup_eq_top]; trivial : y ∈ W ⊔ suppPerp Q W)
    rw [map_add, map_add, hcW w hw, hcW' w' hw', hF, hF, hσ, hσ, hcW w hw, hcW' w' hw',
      smul_smul, smul_smul, hsq cW hcW0, hsq cW' hcW'0, one_smul, one_smul]
  have hsymm : ∀ y, F.symm y = F y := fun y => (AddEquiv.symm_apply_eq F).mpr (hFF y).symm
  have hαα : α * α = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      have hg' : semilinConj F σ hF (g : _ ≃ₗ[K] _) ∈ orthDerived Q :=
        semilinConj_mem_orthDerived F σ hF μ hFQ g.2
      have hg'' : semilinConj F σ hF (semilinConj F σ hF (g : _ ≃ₗ[K] _)) ∈ orthDerived Q :=
        semilinConj_mem_orthDerived F σ hF μ hFQ hg'
      have h1 := hκ g ⟨_, hg'⟩ (fun v => rfl)
      have h2 := hκ ⟨_, hg'⟩ ⟨_, hg''⟩ (fun v => rfl)
      show α (α (QuotientGroup.mk g)) = QuotientGroup.mk g
      rw [h1, h2]
      congr 1
      refine Subtype.ext (LinearEquiv.ext fun v => ?_)
      show F (F ((g : _ ≃ₗ[K] _) (F.symm (F.symm v)))) = (g : _ ≃ₗ[K] _) v
      rw [hFF, hsymm, hsymm, hFF]
  have h2 : orderOf α ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hαα)
  have h3 : orderOf α ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hg := Nat.dvd_gcd h2 h3
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

end Rigid

section Final

variable {G : Type} [Group G] [Finite G]

theorem model1520_of_orth_abs_set {X : Subgroup G} {t : G} (htX : t ∈ X) (ht : t * t = 1)
    {K : Type} [Field K] [Finite K] (hK3 : Nat.card K = 3) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate)
    (hP : Group.IsPerfect (ProjOrthDerived Q))
    (e : ↥X ⧸ Subgroup.center ↥X ≃* ProjOrthDerived Q) (W : Submodule K (V))
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate) (hW3 : 3 ≤ finrank K W)
    (hW'3 : 3 ≤ finrank K (suppPerp Q W)) (h : V ≃ₗ[K] V)
    (hh : h ∈ orthDerived Q) (a b : K) (ha : ∀ w ∈ W, h w = a • w)
    (hb : ∀ w ∈ suppPerp Q W, h w = b • w)
    (het : e (QuotientGroup.mk ⟨t, htX⟩) = QuotientGroup.mk ⟨h, hh⟩)
    (T : Set (ProjOrthDerived Q))
    (hT : ∀ s ∈ T, s ^ 3 = 1 ∧ s * QuotientGroup.mk ⟨h, hh⟩ = QuotientGroup.mk ⟨h, hh⟩ * s)
    (hind : ∀ α : MulAut (ProjOrthDerived Q), (∃ k : ℕ, α ^ (3 ^ k) = 1) →
      (∀ s ∈ eichlerImages Q W ∪ eichlerImages Q (suppPerp Q W) ∪ T, α s = s) →
      CFSG.RankThree.PartOne.KCOrthogonalAut.InducedBySemilinear Q α) : Model1520 X t := by
  have hK2 : Nat.card K = 2 → False := fun h => by omega
  have hWreg := polarNondegOn_of_nondegenerate hW
  have hW' : (polarBilin (Q.comp (suppPerp Q W).subtype)).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_suppPerp hQ hWreg)
  have hWW : suppPerp Q (suppPerp Q W) = W :=
    LinearMap.BilinForm.orthogonal_orthogonal hQ (QuadraticMap.isSymm_polarBilin Q).isRefl W
  refine model1520_of_rigid3 htX ht hP e het
    (rigid3_of_orth_abs_set hK3 Q hQ W hW hW3 hW'3 _
      (eichlerImages Q W ∪ eichlerImages Q (suppPerp Q W) ∪ T) Set.subset_union_left ?_ ?_ hind)
  · rintro s ((hs | hs) | hs)
    · exact eichlerImages_cube hK3 hs
    · exact eichlerImages_cube hK3 hs
    · exact (hT s hs).1
  · have hcommE : ∀ s ∈ eichlerImages Q W ∪ eichlerImages Q (suppPerp Q W),
        s * QuotientGroup.mk ⟨h, hh⟩ = QuotientGroup.mk ⟨h, hh⟩ * s := by
      intro s hs
      have key : ∀ (U : Submodule K (V)), (polarBilin (Q.comp U.subtype)).Nondegenerate →
          3 ≤ finrank K U → (U = W ∨ U = suppPerp Q W) → s ∈ eichlerImages Q U →
          s * QuotientGroup.mk ⟨h, hh⟩ = QuotientGroup.mk ⟨h, hh⟩ * s := by
        rintro U hUnd hU3 hU ⟨P, he, hf, w, hw, hE', rfl⟩
        have hEs := elementaryMapsMem_of_regular hUnd hU3 (fun h => absurd h hK2) P he hf w hw
        have hE1 : ∀ x ∈ U, eichler Q P.e w x ∈ U := fun x hx => supportedDerived_apply_mem hEs hx
        have hE2 : ∀ x ∈ suppPerp Q U, eichler Q P.e w x = x := fun x hx =>
          supportedDerived_apply_perp hEs hx
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        refine Subtype.ext (LinearEquiv.ext fun v => ?_)
        show eichler Q P.e w (h v) = h (eichler Q P.e w v)
        rcases hU with rfl | rfl
        · exact (commute_of_scalar_blocks (isCompl_suppPerp hWreg) h _ a b ha hb hE1 hE2 v).symm
        · rw [hWW] at hE2
          exact (commute_of_scalar_blocks (isCompl_suppPerp hWreg).symm h _ b a hb ha hE1 hE2 v).symm
      rcases hs with hs | hs
      · exact key W hW hW3 (Or.inl rfl) hs
      · exact key _ hW' hW'3 (Or.inr rfl) hs
    rintro s ((hs | hs) | hs)
    · exact hcommE s (Or.inl hs)
    · exact hcommE s (Or.inr hs)
    · exact (hT s hs).2

end Final

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux

module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseIAux
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFixedRootVec
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoShadowDim
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoDefs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree


theorem twE6CaseI_rankTwo (hT : E6CaseITable) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (q : ℕ) (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hK3 : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : IsElemAbelian 3 E₀)
    (hc : Nat.card E₀ = 3 ^ 3) {h₀ : twistedE6RootGroup K σ} (hh₀ : h₀ ∈ E₀) (hh₀1 : h₀ ≠ 1)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (ha : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (h₀ : ModGL TwistTag.E6.tag K) *
      g0 = rootDiagUnit TwistTag.E6.tag a)
    (haΦ : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
      (rootChar a α = 1 ↔ (3 : ℤ) ∣ α 3))
    (hmono : ∀ x ∈ E₀, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∃ w : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    (hplane : ∀ y ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∀ u : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
            g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u →
          (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → u • γ = γ →
            (3 : ℤ) ∣ γ 3) →
          twE6FixDim K σ y = 24 → TwE6All24PlaneIn K σ E₀)
    {x₁ : twistedE6RootGroup K σ} (hx₁ : x₁ ∈ E₀)
    {t₁ : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht₁ : t₁ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    {w₁ : WeylGroup TwistTag.E6.tag} (hw₁ : w₁ ≠ 1)
    (hx₁w : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x₁ : ModGL TwistTag.E6.tag K) *
      g0 = t₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₁)
    {x₂ : twistedE6RootGroup K σ} (hx₂ : x₂ ∈ E₀)
    {t₂ : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht₂ : t₂ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    {w₂ : WeylGroup TwistTag.E6.tag} (hw₂ : w₂ ∉ Subgroup.zpowers w₁)
    (hx₂w : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x₂ : ModGL TwistTag.E6.tag K) *
      g0 = t₂ * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₂)
    (hn₁ : E6FixesNode3 w₁) (hn₂ : E6FixesNode3 w₂) :
    TwE6All24PlaneIn K σ E₀ ∨ NormalizesRGroup (ringChar K) E₀ := by
  have hw₁3 := pow_eq_one_of_twE6Frame_eq (hE₀.2 x₁ hx₁) ht₁ hx₁w
  have hw₂3 := pow_eq_one_of_twE6Frame_eq (hE₀.2 x₂ hx₂) ht₂ hx₂w
  have hcomm : Commute w₁ w₂ := commute_of_twE6Frame_eq (hE₀.comm hx₁ hx₂) ht₁ ht₂ hx₁w hx₂w
  have hppE : ∀ a b : ℕ, x₁ ^ a * x₂ ^ b ∈ E₀ := fun a b =>
    mul_mem (pow_mem hx₁ a) (pow_mem hx₂ b)
  have hpp : ∀ a b : ℕ, ∃ s ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((x₁ ^ a * x₂ ^ b : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
        s * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
          (w₁ ^ a * w₂ ^ b) := by
    intro a b
    obtain ⟨s₁, hs₁, e₁⟩ := exists_twE6Frame_pow_eq ht₁ hx₁w a
    obtain ⟨s₂, hs₂, e₂⟩ := exists_twE6Frame_pow_eq ht₂ hx₂w b
    exact exists_twE6Frame_mul_eq hs₁ hs₂ e₁ e₂
  rcases hT.2 w₁ w₂ hw₁3 hw₁ hw₂3 hcomm hw₂ hn₁ hn₂ with ⟨i, j, hk3⟩ |
    ⟨γ, hγr, hγ3, hγ1, hγ2, i, j, k, l, hdet, h2A2, h2A2'⟩
  ·
    obtain ⟨s, hs, hy⟩ := hpp i j
    have hN : ∀ μ : Fin TwistTag.E6.tag.rank → ℤ,
        μ + (w₁ ^ i * w₂ ^ j) • μ + (w₁ ^ i * w₂ ^ j) • (w₁ ^ i * w₂ ^ j) • μ = 0 := hk3
    refine Or.inl (hplane _ (hppE i j) s hs _ hy (fun δ hδ hwδ => ?_) ?_)
    · refine absurd ?_ hδ.ne_zero
      have h := hN δ
      rw [hwδ, hwδ] at h
      funext m
      have h' := congrFun h m
      simp only [Pi.add_apply, Pi.zero_apply] at h' ⊢
      omega
    · exact twE6FixDim_eq_24_of_kind3A2 hK3 (hE₀.2 _ (hppE i j)) hs
        (pow_eq_one_of_twE6Frame_eq (hE₀.2 _ (hppE i j)) hs hy) hy hN
  obtain ⟨γ, hγr, hγ3, hγ1, hγ2⟩ : ∃ γ' : Fin TwistTag.E6.tag.rank → ℤ,
      IsRoot TwistTag.E6.tag γ' ∧ (3 : ℤ) ∣ γ' 3 ∧ w₁ • γ' = γ' ∧ w₂ • γ' = γ' :=
    ⟨γ, hγr, hγ3, hγ1, hγ2⟩
  have hstab : ∀ a b : ℕ, (w₁ ^ a * w₂ ^ b) • γ = γ := fun a b =>
    MulAction.mem_stabilizer_iff.1 (mul_mem (pow_mem (MulAction.mem_stabilizer_iff.2 hγ1) a)
      (pow_mem (MulAction.mem_stabilizer_iff.2 hγ2) b))
  set F := twE6RootVecFixer K σ g0 ({γ, -γ} : Set (Fin TwistTag.E6.tag.rank → ℤ))
  have key : ∀ z ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∀ w : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL TwistTag.E6.tag K) *
            g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w →
          w • γ = γ → (∃ γ₁ γ₂, E6Kind2A2 w γ₁ γ₂ ∧ ∀ δ ∈ a2Roots γ₁ γ₂, (3 : ℤ) ∣ δ 3) →
            TwE6All24PlaneIn K σ E₀ ∨ z ∈ F := by
    rintro z hz t ht w hzw hwγ ⟨γ₁, γ₂, ⟨hγ, h₁, h₂, hfix, hμ, hN⟩, hΦ⟩
    by_cases hd : twE6FixDim K σ z = 24
    · exact Or.inl (hplane z hz t ht w hzw (fun δ hδ hwδ => hΦ δ (hfix δ hδ hwδ)) hd)
    have hv₁ := not_not.1 fun hne => hd ((twE6FixDim_eq_24_iff_of_kind2A2 hK3 (hE₀.2 z hz) ht
      (pow_eq_one_of_twE6Frame_eq (hE₀.2 z hz) ht hzw) hzw hγ h₁ h₂ hfix hμ hN).2 hne)
    have hγa : γ ∈ a2Roots γ₁ γ₂ := hfix γ hγr hwγ
    refine Or.inr (mem_twE6RootVecFixer.2 fun δ hδ => rootVec_fixed_of_kind2A2 (hE₀.2 z hz) ht
      hzw hγ h₁ h₂ hμ (Set.mem_insert _ _) ?_ hv₁)
    rcases hδ with hδ | hδ
    · rw [hδ]
      exact hγa
    · rw [Set.mem_singleton_iff] at hδ
      rw [hδ]
      exact neg_mem_a2Roots hγa
  have hh₀w : ∀ S : Subgroup (WeylGroup TwistTag.E6.tag),
      ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K), ∃ w ∈ S,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (h₀ : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w :=
    fun S => ⟨_, rootDiagUnit_mem_torusGroup a, 1, one_mem S, by
      rw [canonicalRep_one, mul_one]
      exact ha⟩
  have hh₀F : h₀ ∈ F := by
    refine mem_twE6RootVecFixer.2 fun δ hδ => ?_
    rw [ha]
    rcases hδ with hδ | hδ
    · rw [hδ]
      exact (rootDiagUnit_apply_rootVec_eq_self_iff a hγr).2 ((haΦ γ hγr).2 hγ3)
    · rw [Set.mem_singleton_iff] at hδ
      rw [hδ]
      refine (rootDiagUnit_apply_rootVec_eq_self_iff a (IsRoot.neg hγr)).2
        ((haΦ _ (IsRoot.neg hγr)).2 ?_)
      rw [Pi.neg_apply, dvd_neg]
      exact hγ3
  obtain ⟨s, hs, hy⟩ := hpp i j
  obtain ⟨s', hs', hy'⟩ := hpp k l
  have hya : x₁ ^ i * x₂ ^ j ∉ Subgroup.closure {h₀} := by
    intro hm
    obtain ⟨γ₁, γ₂, ⟨-, -, -, hfix, -⟩, hΦ⟩ := h2A2
    have hfix' : ∀ δ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag δ →
        (w₁ ^ i * w₂ ^ j) • δ = δ → (3 : ℤ) ∣ δ 3 := fun δ hδ hwδ => hΦ δ (hfix δ hδ hwδ)
    have hu1 : w₁ ^ i * w₂ ^ j ∈ (⊥ : Subgroup (WeylGroup TwistTag.E6.tag)) :=
      mem_of_twE6Frame_eq_of_mem_closure (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hh₀w ⊥) hm hs hy
    have h := hfix' _ (IsRoot.basis 3) (by rw [Subgroup.mem_bot.1 hu1, one_smul])
    rw [Pi.single_eq_same] at h
    omega
  have hy'a : x₁ ^ k * x₂ ^ l ∉ Subgroup.closure {h₀, x₁ ^ i * x₂ ^ j} := by
    intro hm
    have hu' : w₁ ^ k * w₂ ^ l ∈ Subgroup.zpowers (w₁ ^ i * w₂ ^ j) :=
      mem_of_twE6Frame_eq_of_mem_closure (fun z hz => by
        rcases hz with hz | hz
        · rw [hz]
          exact hh₀w _
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact ⟨s, hs, _, Subgroup.mem_zpowers _, hy⟩) hm hs' hy'
    have hmem : ∀ a b : ℕ, w₁ ^ a * w₂ ^ b ∈ Subgroup.zpowers (w₁ ^ i * w₂ ^ j) := by
      intro a b
      obtain ⟨c, d, e⟩ := exists_eq_pow_mul_pow_of_not_dvd hcomm hw₁3 hw₂3 hdet a b
      rw [e]
      exact mul_mem (pow_mem (Subgroup.mem_zpowers _) c) (pow_mem hu' d)
    have h1 := hmem 1 0
    have h2 := hmem 0 1
    rw [pow_one, pow_zero, mul_one] at h1
    rw [pow_zero, pow_one, one_mul] at h2
    exact hw₂ (mem_zpowers_of_pow_three_eq_one h1 hw₁3 hw₁ h2 hw₂3)
  have hcl := closure_three_eq_of_card_eq hc hh₀ (hppE i j) (hppE k l) hh₀1 hya hy'a
  rcases key _ (hppE i j) s hs _ hy (hstab i j) h2A2 with hP | hyF
  · exact Or.inl hP
  rcases key _ (hppE k l) s' hs' _ hy' (hstab k l) h2A2' with hP | hy'F
  · exact Or.inl hP
  right
  have hEF : ∀ x ∈ E₀, x ∈ F := by
    intro x hx
    rw [← hcl] at hx
    exact (Subgroup.closure_le F).2 (Set.insert_subset_iff.2 ⟨hh₀F,
      Set.insert_subset_iff.2 ⟨hyF, Set.singleton_subset_iff.2 hy'F⟩⟩) hx
  have hXst : ∀ z ∈ ({h₀, x₁ ^ i * x₂ ^ j, x₁ ^ k * x₂ ^ l} : Set (twistedE6RootGroup K σ)),
      ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
        ∃ w ∈ MulAction.stabilizer (WeylGroup TwistTag.E6.tag) γ,
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL TwistTag.E6.tag K) *
            g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w := by
    intro z hz
    rcases hz with hz | hz | hz
    · rw [hz]
      exact hh₀w _
    · rw [hz]
      exact ⟨s, hs, _, MulAction.mem_stabilizer_iff.2 (hstab i j), hy⟩
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact ⟨s', hs', _, MulAction.mem_stabilizer_iff.2 (hstab k l), hy'⟩
  refine normalizesRGroup_of_monomial_fixed_rootVec q K σ hK hσ hK3 E₀ Fr hFr v g0 hg0C hg0
    hγr (hv γ) fun x hx => ?_
  obtain ⟨t, ht, w, hxw⟩ := hmono x hx
  have hxc : x ∈ Subgroup.closure {h₀, x₁ ^ i * x₂ ^ j, x₁ ^ k * x₂ ^ l} := by
    rw [hcl]
    exact hx
  have hwγ := MulAction.mem_stabilizer_iff.1 (mem_of_twE6Frame_eq_of_mem_closure hXst hxc ht hxw)
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hxF := mem_twE6RootVecFixer.1 (hEF x hx)
  exact ⟨c, w, hxw, hwγ, hxF γ (Set.mem_insert _ _), hxF (-γ) (Set.mem_insert_of_mem _ rfl)⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end

module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3BendUtil
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinShape

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

section Aux

variable {G : Type} [Group G]

theorem mem_iff_of_conjugate_eq {X Y : Subgroup G} {g : G} (h : CFSG.conjugate X g = Y) (x : G) :
    x ∈ Y ↔ g * x * g⁻¹ ∈ X := by
  rw [← h]
  exact BenderBranch.mem_conjugate_iff

theorem exists_noncomm_of_isQuasisimple {X : Type*} [Group X] (hq : CFSG.IsQuasisimple X) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center X = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    exact Subgroup.mem_center_iff.mpr fun g => h g x
  have hS : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  obtain ⟨a, b, hab⟩ := hS.toNontrivial.exists_pair_ne
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  apply hab
  rw [QuotientGroup.eq]
  rw [hc]
  exact Subgroup.mem_top _

theorem fusionIsBenderGroup_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : Y ≃* X)
    (h : fusionIsBenderGroup X) : fusionIsBenderGroup Y := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.trans e'⟩⟩)

theorem isPGroup_sup_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : IsPGroup 2 ↥A) (hB : IsPGroup 2 ↥B) : IsPGroup 2 ↥(A ⊔ B) := by
  refine hA.to_sup_of_normal_right' hB fun a ha => ?_
  exact Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm)

theorem normalizer_sup_of_dichotomy [Finite G] {A B W : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hW : ∀ w ∈ W, ((∀ x, x ∈ A ↔ w * x * w⁻¹ ∈ A) ∧ (∀ x, x ∈ B ↔ w * x * w⁻¹ ∈ B)) ∨
      ((∀ x, x ∈ A ↔ w * x * w⁻¹ ∈ B) ∧ (∀ x, x ∈ B ↔ w * x * w⁻¹ ∈ A))) :
    W ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro w hw
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp hx
  have hconj : w * (a * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) := by group
  rw [hconj]
  rcases hW w hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((h1 _).mp ha))
      (Subgroup.mem_sup_right ((h2 _).mp hb))
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((h1 _).mp ha))
      (Subgroup.mem_sup_left ((h2 _).mp hb))

end Aux

theorem lemma253Bender (h252 : Lemma252) : Lemma253Bender := by
  intro G _ _ T M H S z hs ht k B hB hH U HU hUP L hL hBen hI
  have hinn : ∀ L' : Subgroup G, IsComponentIn L' H → Ch1.InducesInner z L' := fun L' hL' =>
    (h252 G T M H S z hs ht L' hL').2.1
  set Q : Subgroup G := pCoreOf 2 HU with hQ
  have hQ2 : IsPGroup 2 ↥Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 HU
  have hQHU : Q ≤ HU := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 HU
  have hHUN : HU ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 HU
  have hHUH : HU ≤ H := hUP.2
  have hOQ : pCoreOf 2 H ≤ Q :=
    hI _ (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
      (hHUH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H))
  have hX : CharTwo (H ⊓ Subgroup.normalizer (Q : Set G)) :=
    lemma253_one hs.setting B hB hH hUP hOQ
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hSne : ∀ S' : Subgroup G, IsSylowTwoOf S' L → S' ≠ ⊥ := by
    intro S' hS' h
    subst h
    exact Unc25G2.false_of_isSylowTwoOf_le_centralizer hq hS' bot_le
  have hfinish : ∀ S₀ : Subgroup G, IsSylowTwoOf S₀ L → S₀ ≤ Q → IsSylowTwoOf (Q ⊓ L) L := by
    intro S₀ hS₀ hS₀Q
    have hQL : S₀ ≤ Q ⊓ L := le_inf hS₀Q hS₀.1
    have : Q ⊓ L = S₀ := hS₀.eq_of_le hQL inf_le_right (hQ2.to_le inf_le_left)
    rw [this]
    exact hS₀
  have hcore : ∀ L₀ : Subgroup G, L ≤ L₀ → L₀ ≤ H → (L₀.subgroupOf H).IsSubnormal →
      HU ≤ Subgroup.normalizer (L₀ : Set G) →
      (∀ S' : Subgroup G, IsSylowTwoOf S' L₀ → S' ≠ ⊥) →
      ∃ P₂ : Subgroup G, P₂ ≤ L₀ ∧ P₂ ≠ ⊥ ∧ IsPGroup 2 ↥P₂ ∧
        HU ≤ Subgroup.normalizer (P₂ : Set G) ∧ P₂ ≤ Q := by
    intro L₀ hLL₀ hL₀H hsub hHUL₀ hS₀ne
    set XL : Subgroup G := L₀ ⊓ (H ⊓ Subgroup.normalizer (Q : Set G)) with hXL
    have hXLchar : CharTwo XL := charTwo_inf_of_isSubnormal hX inf_le_left hsub
    obtain ⟨x, hxL, hx1, hxc⟩ := exists_ne_one_centralizer hQ2 (hQHU.trans hHUL₀) hS₀ne
    have hxN : x ∈ Subgroup.normalizer (Q : Set G) := by
      refine mem_normalizer_of_conj_mem fun f hf => ?_
      have : x * f * x⁻¹ = f := by
        rw [← hxc f hf]
        group
      rw [this]
      exact hf
    have hxXL : x ∈ XL := ⟨hxL, hL₀H hxL, hxN⟩
    have hP₂ne : pCoreOf 2 XL ≠ ⊥ := by
      intro h
      have h' := hXLchar
      unfold CharTwo at h'
      rw [h] at h'
      have hx' : x ∈ XL ⊓ Subgroup.centralizer (((⊥ : Subgroup G) : Set G)) :=
        ⟨hxXL, Subgroup.mem_centralizer_iff.mpr fun g hg => by
          rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hg
          rw [hg, one_mul, mul_one]⟩
      exact hx1 (Subgroup.mem_bot.mp (h' hx'))
    have hHUXL : HU ≤ Subgroup.normalizer (XL : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf HU L₀ _ hHUL₀
        (CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf HU H _
          (hHUH.trans Subgroup.le_normalizer) (hHUN.trans Subgroup.le_normalizer))
    have hHUP₂ : HU ≤ Subgroup.normalizer (pCoreOf 2 XL : Set G) :=
      hHUXL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 XL)
    have hP₂L : pCoreOf 2 XL ≤ L₀ :=
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 XL).trans inf_le_left
    have hP₂2 : IsPGroup 2 ↥(pCoreOf 2 XL) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 XL
    exact ⟨pCoreOf 2 XL, hP₂L, hP₂ne, hP₂2, hHUP₂, hI _ (hP₂L.trans hL₀H) hP₂2 hHUP₂⟩
  by_cases hA : HU ≤ Subgroup.normalizer (L : Set G)
  ·
    obtain ⟨P₂, hP₂L, hP₂ne, hP₂2, hHUP₂, -⟩ :=
      hcore L le_rfl hL.1 hL.2.2 hA hSne
    obtain ⟨S₀, hS₀, -, hS₀N⟩ :=
      exists_sylow_normalized_single hBen hP₂L hP₂ne hP₂2 hA hHUP₂
    exact hfinish S₀ hS₀ (hI S₀ (hS₀.1.trans hL.1) hS₀.2.1 hS₀N)
  ·
    obtain ⟨h₀, hh₀U, hh₀N⟩ : ∃ h₀ ∈ HU, h₀ ∉ Subgroup.normalizer (L : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hA fun h hh => hcon h hh
    have hh₀H : h₀ ∈ H := hHUH hh₀U
    have hne : CFSG.conjugate L h₀ ≠ L := fun h =>
      hh₀N (BenderBranch.conjugate_eq_iff_mem_normalizer.mp h)
    set L' : Subgroup G := CFSG.conjugate L h₀ with hL'
    have hL'c : IsComponentIn L' H := Unc25G2.isComponentIn_conjugate hL hh₀H
    have hcomm : ⁅L, L'⁆ = ⊥ :=
      (BenderBranch.eq_or_commute_of_isComponentIn hL hL'c).resolve_left fun h => hne h.symm
    have hc : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := fun a ha b hb =>
      BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
    have hsimp : IsSimpleGroup ↥L := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hBen
    have hdisj : ∀ x, x ∈ L → x ∈ L' → x = 1 := fun x hxL hxL' =>
      BenderBranch.eq_one_of_commute_of_simple hsimp (exists_noncomm_of_isQuasisimple hq) hxL
        fun w hw => hc w hw x hxL'
    have hBen' : fusionIsBenderGroup ↥L' :=
      fusionIsBenderGroup_of_mulEquiv
        ((L.equivMapOfInjective (MulAut.conj h₀⁻¹).toMonoidHom (MulAut.conj h₀⁻¹).injective).symm)
        hBen
    have hd := conjugate_dichotomy hs ht hinn hL hh₀H hne
    have hdich : ∀ g ∈ H, ((∀ x, x ∈ L ↔ g * x * g⁻¹ ∈ L) ∧ (∀ x, x ∈ L' ↔ g * x * g⁻¹ ∈ L')) ∨
        ((∀ x, x ∈ L ↔ g * x * g⁻¹ ∈ L') ∧ (∀ x, x ∈ L' ↔ g * x * g⁻¹ ∈ L)) := by
      intro g hg
      have hd' : CFSG.conjugate L g = L ∨ CFSG.conjugate L g = L' := hd g hg
      have hB : CFSG.conjugate L' g = L ∨ CFSG.conjugate L' g = L' := by
        have : CFSG.conjugate L' g = CFSG.conjugate L (h₀ * g) := by
          rw [hL', BenderBranch.conjugate_conjugate]
        rw [this]
        exact hd (h₀ * g) (H.mul_mem hh₀H hg)
      have hinj : CFSG.conjugate L' g = CFSG.conjugate L g → False := fun h =>
        hne (BenderBranch.conjugate_inj.mp h)
      rcases hd' with h1 | h1 <;> rcases hB with h2 | h2
      · exact absurd (h2.trans h1.symm) hinj
      · exact Or.inl ⟨mem_iff_of_conjugate_eq h1, mem_iff_of_conjugate_eq h2⟩
      · exact Or.inr ⟨mem_iff_of_conjugate_eq h2, mem_iff_of_conjugate_eq h1⟩
      · exact absurd (h2.trans h1.symm) hinj
    have hHL₀ : H ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup G) : Set G) :=
      normalizer_sup_of_dichotomy hc hdich
    have hL₀H : L ⊔ L' ≤ H := sup_le hL.1 hL'c.1
    have hL₀sub : ((L ⊔ L').subgroupOf H).IsSubnormal :=
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hL₀H).mpr hHL₀).isSubnormal
    have hLnorm : L ⊔ L' ≤ Subgroup.normalizer (L : Set G) :=
      sup_le Subgroup.le_normalizer fun b hb =>
        Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb)
    have hLsub : (L.subgroupOf (L ⊔ L')).IsSubnormal :=
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hLnorm).isSubnormal
    have hS₀ne : ∀ S' : Subgroup G, IsSylowTwoOf S' (L ⊔ L') → S' ≠ ⊥ := by
      intro S' hS' h
      have := RankOneRecog.isSylowTwoOf_inf_of_subnormal hS' le_sup_left hLsub
      rw [h, bot_inf_eq] at this
      exact hSne _ this rfl
    obtain ⟨P₂, hP₂L, hP₂ne, hP₂2, hHUP₂, -⟩ :=
      hcore (L ⊔ L') le_sup_left hL₀H hL₀sub (hHUH.trans hHL₀) hS₀ne
    have hswap : ∃ w ∈ HU, (∀ x, x ∈ L ↔ w * x * w⁻¹ ∈ L') ∧ (∀ x, x ∈ L' ↔ w * x * w⁻¹ ∈ L) := by
      refine ⟨h₀, hh₀U, ?_⟩
      rcases hdich h₀ hh₀H with ⟨h1, -⟩ | h
      · exfalso
        apply hh₀N
        refine mem_normalizer_of_conj_mem fun x hx => ?_
        exact (h1 x).mp hx
      · exact h
    obtain ⟨S₁, S₂, hS₁, hS₂, hHUS⟩ := exists_sylow_normalized_pair hBen hBen' hc hdisj hP₂L
      hP₂ne hP₂2 hHUP₂ (fun w hw => hdich w (hHUH hw)) hswap
    have hS₁₂ : IsPGroup 2 ↥(S₁ ⊔ S₂) :=
      isPGroup_sup_of_commute (fun a ha b hb => hc a (hS₁.1 ha) b (hS₂.1 hb)) hS₁.2.1 hS₂.2.1
    have hS₁₂H : S₁ ⊔ S₂ ≤ H := sup_le (hS₁.1.trans hL.1) (hS₂.1.trans hL'c.1)
    have hS₁₂Q : S₁ ⊔ S₂ ≤ Q := hI _ hS₁₂H hS₁₂ hHUS
    exact hfinish S₁ hS₁ (le_sup_left.trans hS₁₂Q)

end CFSG.QuasithinUnique.Fin253

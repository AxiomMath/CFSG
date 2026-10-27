module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellExclusion

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section NormalHull

variable {G : Type*} [Group G] {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

namespace DoubleSetup

variable [Finite G] [Finite k] {α : (S : Subgroup G) ≃* (S : Subgroup G)} {A : Subgroup G} {g : G}
  (c : DoubleSetup S ρ ψ α A g)
include c

theorem absurd : False := by
  classical
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  obtain ⟨hBQ, hBS, hBle⟩ := c.seed.Bb_isMax α c.hV c.hV' c.hA g
  have hYB := c.Y_not_le_B
  have hYQ := c.Ysub_le_core
  have hYel : CFSG.Open.IsElemAbelian 2 (Ysub S α g) :=
    isElemAbelian_cj (isElemAbelian_aimg α.symm
      (isElemAbelian_cj (isElemAbelian_aimg α isElemAbelian_Fcore) g)) g
  have hFaQ := c.seed.aimg_Fcore_le_core α c.hV
  have hFaS : aimg (S : Subgroup G) α (Fcore G) ≤ (S : Subgroup G) := aimg_le
  have hFiS : aimg (S : Subgroup G) α.symm (Fcore G) ≤ (S : Subgroup G) := aimg_le
  have hPS : cj (aimg (S : Subgroup G) α (Fcore G)) g ≤ (S : Subgroup G) :=
    (cj_le_core hFaQ g).trans hQS
  have hUS : aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g) ≤
      (S : Subgroup G) := aimg_le
  set B := Bb S α A g with hB
  set C₁ := B ⊓ Subgroup.centralizer ((Ysub S α g : Subgroup G) : Set G) with hC₁
  have hAB : ⁅A, B⁆ ≤ C₁ := c.commutator_A_Bb_le
  have hC₁inv : ∀ a ∈ A, cj C₁ a = C₁ := by
    intro a ha
    apply cj_eq_of_forall_mem
    intro x hx
    have hcomm : a * x * a⁻¹ * x⁻¹ ∈ C₁ := hAB (Subgroup.commutator_mem_commutator ha hx.1)
    have : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
    rw [this]
    exact mul_mem hcomm hx
  have hC₁le : ∀ a ∈ A, C₁ ≤ Subgroup.centralizer ((cj (Ysub S α g) a : Subgroup G) : Set G) := by
    intro a ha
    have h1 : C₁ ≤ Subgroup.centralizer ((Ysub S α g : Subgroup G) : Set G) := inf_le_right
    have h2 := cj_mono (g := a) h1
    rw [hC₁inv a ha, ← centralizer_cj] at h2
    exact h2
  have hBP : ⁅B, Pminus S α g⁆ = ⊥ :=
    commutator_eq_bot_of_commute fun b hb y hy =>
      (isElemAbelian_iff.mp hBS.2.1).1 b hb y (Subgroup.mem_sup_left hy)
  have hPg : cj (Pminus S α g) g = aimg (S : Subgroup G) α.symm (Fcore G) := by
    rw [Pminus, cj_cj, c.hg2, cj_one]
  have hBgFi : ⁅cj B g, aimg (S : Subgroup G) α.symm (Fcore G)⁆ = ⊥ := by
    have := congrArg (fun H => cj H g) hBP
    simp only [cj_commutator, cj_bot, hPg] at this
    exact this
  have hBgS : cj B g ≤ (S : Subgroup G) := (cj_le_core hBle g).trans hQS
  have hBgC : cj B g ≤ (S : Subgroup G) ⊓ Subgroup.centralizer
      ((aimg (S : Subgroup G) α.symm (Fcore G) : Subgroup G) : Set G) :=
    le_inf hBgS fun x hx => Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (mul_comm_of_commutator_eq_bot hBgFi hx hw).symm
  have hαBgQ : aimg (S : Subgroup G) α (cj B g) ≤ CFSG.pCore 2 G := by
    have h1 := aimg_mono (S := (S : Subgroup G)) (α := α) hBgC
    rw [aimg_centralizer hFiS, aimg_self, aimg_aimg_symm Fcore_le_sylow] at h1
    exact h1.trans c.seed.sylow_inf_centralizer_Fcore_le
  have hαBgmax : IsMaxElemAbelian (CFSG.pCore 2 G) (aimg (S : Subgroup G) α (cj B g)) :=
    ⟨hαBgQ, isElemAbelian_aimg α (isElemAbelian_cj hBS.2.1 g), fun B' hB'Q hB'e => by
      rw [card_aimg hBgS, card_cj]; exact hBQ.2.2 B' hB'Q hB'e⟩
  have hE := c.seed.isMaxElemAbelian_tr_Fcore_sup α g (A' := aimg (S : Subgroup G) α (cj B g))
    (c.seed.isMaxElemAbelian_cj_of_core hαBgmax g)
  have hE'Q : tr (S : Subgroup G) α g (Fcore G) ⊔ (aimg (S : Subgroup G) α (cj B g) ⊓
      Subgroup.centralizer ((tr (S : Subgroup G) α g (Fcore G) : Subgroup G) : Set G)) ≤
      CFSG.pCore 2 G := sup_le (cj_le_core hFaQ g) (inf_le_left.trans hαBgQ)
  have hE'max := isMaxElemAbelian_core_of_le_cj hQS hE hE'Q
  set E' := tr (S : Subgroup G) α g (Fcore G) ⊔ (aimg (S : Subgroup G) α (cj B g) ⊓
      Subgroup.centralizer ((tr (S : Subgroup G) α g (Fcore G) : Subgroup G) : Set G)) with hE'def
  have hE'S : E' ≤ (S : Subgroup G) := hE'Q.trans hQS
  have hint : aimg (S : Subgroup G) α (cj B g) ⊓ Subgroup.centralizer
      ((cj (aimg (S : Subgroup G) α (Fcore G)) g : Subgroup G) : Set G) ≤ (S : Subgroup G) :=
    inf_le_left.trans aimg_le
  have hYC₁eq : Ysub S α g ⊔ C₁ = cj (aimg (S : Subgroup G) α.symm E') g := by
    rw [hE'def]
    show _ = cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g ⊔
      (aimg (S : Subgroup G) α (cj B g) ⊓ Subgroup.centralizer
        ((cj (aimg (S : Subgroup G) α (Fcore G)) g : Subgroup G) : Set G)))) g
    rw [aimg_sup hPS hint, aimg_centralizer hPS, aimg_symm_aimg hBgS, cj_sup, cj_inf, cj_cj,
      c.hg2, cj_one, ← centralizer_cj]
    rfl
  have hYC₁max : IsMaxElemAbelian (CFSG.pCore 2 G) (Ysub S α g ⊔ C₁) := by
    refine ⟨sup_le hYQ (inf_le_left.trans hBle), ?_, fun B' hB'Q hB'e => ?_⟩
    · rw [hYC₁eq]; exact isElemAbelian_cj (isElemAbelian_aimg α.symm hE'max.2.1) g
    · rw [hYC₁eq, card_cj, card_aimg hE'S]; exact hE'max.2.2 B' hB'Q hB'e
  have hYC : ∀ x ∈ Ysub S α g, ∀ y ∈ C₁, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx
  have hYx : ∀ x ∈ A, x ∉ CFSG.pCore 2 G → cj (Ysub S α g) x ≤ Ysub S α g ⊔ C₁ := by
    intro x hx hxQ
    have hx2 : x ^ 2 = 1 := (isElemAbelian_iff.mp c.hA.2.1).2 x hx
    have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact c.hg2
    have hcomm : ⁅cj (Ysub S α g) x, Ysub S α g⁆ = ⊥ := by
      have := (c.seed.mixed_conjugation_calculus α c.hV c.hV' c.hgH c.hgM hg2 c.hgH c.hgM hg2
        (maxElem_le_thompsonJ c.hA hx) hxQ hx2).2.2.2.1
      rw [Ysub, cj_cj]
      exact this
    refine maxElem_le_of_commute hYC₁max (cj_le_core hYQ x) (isElemAbelian_cj hYel x) ?_
    intro y hy u hu
    obtain ⟨y₁, hy₁, c₁, hc₁, rfl⟩ := mem_sup_of_commute hYC hu
    have h1 : y * y₁ = y₁ * y := mul_comm_of_commutator_eq_bot hcomm hy hy₁
    have h2 : y * c₁ = c₁ * y := Subgroup.mem_centralizer_iff.mp (hC₁le x hx hc₁) y hy
    calc y * (y₁ * c₁) = (y * y₁) * c₁ := by group
      _ = (y₁ * y) * c₁ := by rw [h1]
      _ = y₁ * (y * c₁) := by group
      _ = y₁ * (c₁ * y) := by rw [h2]
      _ = y₁ * c₁ * y := by group
  have hYC₁le : ∀ a ∈ A, cj (Ysub S α g ⊔ C₁) a ≤ Ysub S α g ⊔ C₁ := by
    intro a ha
    by_cases haQ : a ∈ CFSG.pCore 2 G
    · obtain ⟨x₀, hx₀, hx₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp c.hAQ
      have hy₀ : x₀⁻¹ * a ∈ A := mul_mem (A.inv_mem hx₀) ha
      have hy₀Q : x₀⁻¹ * a ∉ CFSG.pCore 2 G := by
        intro hQ
        apply hx₀Q
        have : x₀ = a * (x₀⁻¹ * a)⁻¹ := by group
        rw [this]
        exact mul_mem haQ ((CFSG.pCore 2 G).inv_mem hQ)
      have e1 : cj (Ysub S α g ⊔ C₁) a = cj (cj (Ysub S α g ⊔ C₁) x₀) (x₀⁻¹ * a) := by
        rw [cj_cj]; congr 1; group
      have h1 : cj (Ysub S α g ⊔ C₁) x₀ ≤ Ysub S α g ⊔ C₁ := by
        rw [cj_sup, hC₁inv x₀ hx₀]
        exact sup_le (hYx x₀ hx₀ hx₀Q) le_sup_right
      have h2 : cj (Ysub S α g ⊔ C₁) (x₀⁻¹ * a) ≤ Ysub S α g ⊔ C₁ := by
        rw [cj_sup, hC₁inv _ hy₀]
        exact sup_le (hYx _ hy₀ hy₀Q) le_sup_right
      rw [e1]
      exact (cj_mono h1).trans h2
    · rw [cj_sup, hC₁inv a ha]
      exact sup_le (hYx a ha haQ) le_sup_right
  have hYC₁eq' : ∀ a ∈ A, cj (Ysub S α g ⊔ C₁) a = Ysub S α g ⊔ C₁ := fun a ha =>
    cj_eq_of_le (hYC₁le a ha)
  have hBinv : ∀ a ∈ A, cj B a = B := fun a ha =>
    cj_eq_of_forall_mem fun b hb => c.Bb_normalized ha hb
  have hBY : ⁅B, Ysub S α g ⊔ C₁⁆ = ⁅B, Ysub S α g⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_comm, Subgroup.commutator_comm B (Ysub S α g)]
      exact commutator_sup_of_commute hYC fun y hy w hw =>
        (isElemAbelian_iff.mp hBS.2.1).1 y hy.1 w hw
    · exact Subgroup.commutator_mono le_rfl le_sup_left
  have hBYne : ⁅B, Ysub S α g⁆ ≠ ⊥ := by
    intro hb
    apply hYB
    exact maxElem_le_of_commute hBQ hYQ hYel fun y hy b hb' =>
      (mul_comm_of_commutator_eq_bot hb hb' hy).symm
  have hYg : cj (Ysub S α g) g = aimg (S : Subgroup G) α.symm
      (cj (aimg (S : Subgroup G) α (Fcore G)) g) := by
    rw [Ysub, cj_cj, c.hg2, cj_one]
  have h1 : cj ⁅B, Ysub S α g⁆ g = ⁅cj B g, aimg (S : Subgroup G) α.symm
      (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ := by
    rw [cj_commutator, hYg]
  have h2 : aimg (S : Subgroup G) α ⁅cj B g, aimg (S : Subgroup G) α.symm
      (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ =
      ⁅aimg (S : Subgroup G) α (cj B g), cj (aimg (S : Subgroup G) α (Fcore G)) g⁆ := by
    rw [aimg_commutator hBgS hUS, aimg_aimg_symm hPS]
  have hBgU : ⁅cj B g, aimg (S : Subgroup G) α.symm
      (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ ≤ (S : Subgroup G) :=
    commutator_le_of_le hBgS hUS
  have hne : ⁅aimg (S : Subgroup G) α (cj B g),
      tr (S : Subgroup G) α g (Fcore G)⁆ ≠ ⊥ := by
    intro hb
    apply hBYne
    have h3 : aimg (S : Subgroup G) α ⁅cj B g, aimg (S : Subgroup G) α.symm
        (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ = ⊥ := by rw [h2]; exact hb
    have h4 := (aimg_eq_bot_iff α hBgU).mp h3
    have h5 : cj ⁅B, Ysub S α g⁆ g = ⊥ := by rw [h1]; exact h4
    calc ⁅B, Ysub S α g⁆ = cj (cj ⁅B, Ysub S α g⁆ g) g⁻¹ := cj_inv_cj.symm
      _ = ⊥ := by rw [h5, cj_bot]
  have hcomm := (c.seed.tr_commutator_eq_of_ne_bot α g
    (c.seed.isMaxElemAbelian_cj_of_core hαBgmax g) hne).1
  have hZaeq : tr (S : Subgroup G) α g (Zfix S) = aimg (S : Subgroup G) α (Zfix S) :=
    cj_eq_of_le_center c.Za_central g
  rw [hZaeq] at hcomm
  have h7 : aimg (S : Subgroup G) α ⁅cj B g, aimg (S : Subgroup G) α.symm
      (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ = aimg (S : Subgroup G) α (Zfix S) := by
    rw [h2]; exact hcomm
  have h8 : ⁅cj B g, aimg (S : Subgroup G) α.symm
      (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ = Zfix S := by
    calc _ = aimg (S : Subgroup G) α.symm (aimg (S : Subgroup G) α ⁅cj B g,
            aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆) :=
          (aimg_symm_aimg hBgU).symm
      _ = aimg (S : Subgroup G) α.symm (aimg (S : Subgroup G) α (Zfix S)) := by rw [h7]
      _ = Zfix S := aimg_symm_aimg Zfix_le_sylow
  have hBYZ : ⁅B, Ysub S α g⁆ = cj (Zfix S) g := by
    have h9 : cj ⁅B, Ysub S α g⁆ g = Zfix S := by rw [h1, h8]
    calc ⁅B, Ysub S α g⁆ = cj (cj ⁅B, Ysub S α g⁆ g) g⁻¹ := cj_inv_cj.symm
      _ = cj (Zfix S) g⁻¹ := by rw [h9]
      _ = cj (Zfix S) g := by rw [c.g_inv]
  obtain ⟨a₀, ha₀, ha₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp c.hAQ
  have hcj : cj (cj (Zfix S) g) a₀ = cj (Zfix S) g := by
    rw [← hBYZ, ← hBY]
    calc cj ⁅B, Ysub S α g ⊔ C₁⁆ a₀ = ⁅cj B a₀, cj (Ysub S α g ⊔ C₁) a₀⁆ := cj_commutator
      _ = ⁅B, Ysub S α g ⊔ C₁⁆ := by rw [hBinv a₀ ha₀, hYC₁eq' a₀ ha₀]
  have hM := c.seed.normalizer_Zfix_le_Mnorm (mem_normalizer_of_cj_cj_eq hcj)
  exact c.hgM (c.seed.mem_Mnorm_of_conj_mem (c.hA.1 ha₀) ha₀Q hM)

end DoubleSetup

namespace IsSeed

variable [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem contained_translates_force_normal_hull
    (hVall : ∀ β : (S : Subgroup G) ≃* (S : Subgroup G),
      aimg (S : Subgroup G) β (Vmod G) ≤ CFSG.pCore 2 G) :
    (∀ α : (S : Subgroup G) ≃* (S : Subgroup G),
      ⁅Hone S, aimg (S : Subgroup G) α (Fcore G)⁆ ≤ Fcore G) ∧
    (Cstar S).Normal ∧ CFSG.Open.IsElemAbelian 2 (Cstar S) ∧ Cstar S ≤ CFSG.pCore 2 G ∧
    (∀ γ : (S : Subgroup G) ≃* (S : Subgroup G), aimg (S : Subgroup G) γ (Cstar S) = Cstar S) ∧
    Cstar S ≠ ⊥ := by
  classical
  have hcont : ∀ α : (S : Subgroup G) ≃* (S : Subgroup G),
      ⁅Hone S, aimg (S : Subgroup G) α (Fcore G)⁆ ≤ Fcore G := by
    intro α
    by_contra hα
    obtain ⟨A, hA, hAQ, g, hgH, hgM, hg⟩ := h.exists_A_g
    exact (⟨h, hVall α, hVall α.symm, hα, hA, hAQ, hgH, hgM, hg⟩ :
      DoubleSetup S ρ ψ α A g).absurd
  obtain ⟨-, hCel, hCQ, hCchar, hCne⟩ := h.hull_of_contained hVall
  refine ⟨hcont, ?_, hCel, hCQ, hCchar, hCne⟩
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  have hCS : Cstar S ≤ (S : Subgroup G) := iSup_le fun β => aimg_le
  have hFC : Fcore G ≤ Cstar S := by
    have := le_iSup (fun β : (S : Subgroup G) ≃* (S : Subgroup G) =>
      aimg (S : Subgroup G) β (Fcore G)) (MulEquiv.refl _)
    rwa [aimg_refl_of_le Fcore_le_sylow] at this
  have hH : ∀ y ∈ Hone S, ∀ x ∈ Cstar S, y * x * y⁻¹ ∈ Cstar S := by
    intro y hy
    have hle : Cstar S ≤ cj (Cstar S) y := by
      refine iSup_le fun β x hx => ?_
      have e : cj (Fcore G ⊔ aimg (S : Subgroup G) β (Fcore G)) y =
          Fcore G ⊔ aimg (S : Subgroup G) β (Fcore G) :=
        cj_sup_eq_of_commutator_le fun w hw =>
          hcont β (Subgroup.commutator_mem_commutator hy hw)
      have h1 : x ∈ cj (Fcore G ⊔ aimg (S : Subgroup G) β (Fcore G)) y := by
        rw [e]; exact Subgroup.mem_sup_right hx
      have h2 := mem_cj.mp h1
      rw [mem_cj]
      refine sup_le hFC (le_iSup (fun β : (S : Subgroup G) ≃* (S : Subgroup G) =>
        aimg (S : Subgroup G) β (Fcore G)) β) h2
    intro x hx
    exact mem_cj.mp (hle hx)
  have hQn : ∀ q ∈ CFSG.pCore 2 G, ∀ x ∈ Cstar S, q * x * q⁻¹ ∈ Cstar S := by
    intro q hq x hx
    have h1 : ((MulAut.conj (⟨q, hQS hq⟩ : (S : Subgroup G)) : (S : Subgroup G) ≃* (S : Subgroup G))
        ⟨x, hCS hx⟩ : (S : Subgroup G)).1 ∈ aimg (S : Subgroup G)
        (MulAut.conj (⟨q, hQS hq⟩ : (S : Subgroup G)) : (S : Subgroup G) ≃* (S : Subgroup G))
        (Cstar S) := mem_aimg_of_mem hx
    rw [hCchar] at h1
    exact h1
  refine ⟨fun n hn g' => ?_⟩
  have hg' : g' ∈ Hone S ⊔ CFSG.pCore 2 G := by rw [h.Hone_sup_core]; trivial
  obtain ⟨j, hj, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg'
  have : j * q * n * (j * q)⁻¹ = j * (q * n * q⁻¹) * j⁻¹ := by group
  rw [this]
  exact hH j hj _ (hQn q hq n hn)

theorem characteristic_obstruction_produces_Sylow_supplement
    (hchar : ∀ N : Subgroup G, N ≤ (S : Subgroup G) →
      (∀ γ : (S : Subgroup G) ≃* (S : Subgroup G), aimg (S : Subgroup G) γ N = N) → N.Normal →
      N = ⊥) :
    ∃ α : (S : Subgroup G) ≃* (S : Subgroup G),
      aimg (S : Subgroup G) α (Vmod G) ⊓ CFSG.pCore 2 G = aimg (S : Subgroup G) α (Zfix S) ∧
        (S : Subgroup G) = CFSG.pCore 2 G ⊔ aimg (S : Subgroup G) α (Vmod G) := by
  by_cases hall : ∀ β : (S : Subgroup G) ≃* (S : Subgroup G),
      aimg (S : Subgroup G) β (Vmod G) ≤ CFSG.pCore 2 G
  · exfalso
    obtain ⟨-, hnorm, -, hCQ, hCchar, hne⟩ := h.contained_translates_force_normal_hull hall
    exact hne (hchar _ (hCQ.trans (core_le_sylow S)) hCchar hnorm)
  · push Not at hall
    obtain ⟨α, hα⟩ := hall
    exact ⟨α, h.outside_translate α hα⟩

end IsSeed

end NormalHull

end CFSG.QuasithinUnique.Setup.Campbell

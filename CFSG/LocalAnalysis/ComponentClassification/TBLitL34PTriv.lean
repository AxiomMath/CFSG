module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PFrame
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOuter

public section

namespace CFSG.ComponentClassification.TBLit.L34P

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open scoped MatrixGroups

theorem isSimpleGroup_S : IsSimpleGroup ↥S := by
  obtain ⟨θ, -⟩ := exact_model.2.1
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4) :=
    (CFSG.LinearGroups.linear_projective_simple (K := F4) (n := 3) (by norm_num)
      (Or.inl le_rfl)).2.1
  exact (θ.symm.trans
    (LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3
      F4).symm).isSimpleGroup

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem commutator_S_eq {K : Subgroup X} (hK : ⁅K, K⁆ = K) {q : Jhat K →* Equiv.Perm (Fin 42)}
    (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s) : ⁅S, S⁆ = S := by
  have hr : q.range = S := le_antisymm (by rintro _ ⟨e, rfl⟩; exact hqS e) fun s hs => by
    obtain ⟨e, he⟩ := hqsurj s hs
    exact ⟨e, he⟩
  rw [← hr, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
    commutator_jhat hK]

theorem false_of_trivial {β γ : X} {K L : Subgroup X}
    (hK : ⁅K, K⁆ = K) (hKγ : K ≤ centralizer ({γ} : Set X))
    (hβN : β ∈ normalizer (K : Set X)) (hβ2 : β * β = 1) (hLK : L ≤ K)
    (hLβ : L ≤ centralizer ({β} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({β} : Set X) ⊓
      centralizer ({γ} : Set X))))
    {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F)) {q : Jhat K →* Equiv.Perm (Fin 42)}
    (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hqker : q.ker = center (Jhat K))
    (hβ : ∀ e, q (betaHat K hβN e) = 1 * q e * 1⁻¹) : False := by
  have : IsSimpleGroup ↥S := isSimpleGroup_S
  set φ := phiC K β q with hφ
  have hrange : φ.range = S := by
    have hc : centralizer ({1} : Set (Equiv.Perm (Fin 42))) ⊓ S = S := by
      ext y
      simp only [mem_inf, mem_centralizer_singleton_iff, one_mul, mul_one, true_and]
    apply le_antisymm
    · exact (range_le_of_realization hβN hqS hβ).trans inf_le_right
    · have hperf : ⁅centralizer ({1} : Set (Equiv.Perm (Fin 42))) ⊓ S,
          centralizer ({1} : Set (Equiv.Perm (Fin 42))) ⊓ S⁆ =
          centralizer ({1} : Set (Equiv.Perm (Fin 42))) ⊓ S := by
        rw [hc]
        exact commutator_S_eq hK hqS hqsurj
      have h := le_range_of_perfect hβN hβ2 hqsurj hqker hβ hperf
      rwa [hc] at h
  have hHC : K ⊓ centralizer ({β} : Set X) ≤
      centralizer ({β} : Set X) ⊓ centralizer ({γ} : Set X) :=
    fun x hx => ⟨hx.2, hKγ hx.1⟩
  have hLH : L ≤ K ⊓ centralizer ({β} : Set X) := le_inf hLK hLβ
  obtain ⟨-, -, hsub, -, -⟩ := hLc
  have hsubH : (L.subgroupOf (K ⊓ centralizer ({β} : Set X))).IsSubnormal := by
    have hc : (L.subgroupOf (centralizer ({β} : Set X) ⊓ centralizer ({γ} : Set X))).comap
        (Subgroup.inclusion hHC) = L.subgroupOf (K ⊓ centralizer ({β} : Set X)) := by
      ext x
      simp only [mem_comap, mem_subgroupOf, Subgroup.coe_inclusion]
    rw [← hc]
    exact hsub.comap _
  have hsubR := hsubH.map φ.rangeRestrict_surjective
  have : IsSimpleGroup ↥φ.range := (MulEquiv.subgroupCongr hrange).isSimpleGroup
  set A := (L.subgroupOf (K ⊓ centralizer ({β} : Set X))).map φ.rangeRestrict with hA
  have hkey : ∀ y, y ∈ (imageHom hLK q).range ↔
      ∃ h : y ∈ φ.range, (⟨y, h⟩ : φ.range) ∈ A := by
    intro y
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨⟨⟨s, hLH s.2⟩, rfl⟩, ⟨⟨s, hLH s.2⟩, mem_subgroupOf.mpr s.2, rfl⟩⟩
    · rintro ⟨h, t, ht, hte⟩
      refine ⟨⟨t, mem_subgroupOf.mp ht⟩, ?_⟩
      have h1 := congrArg Subtype.val hte
      exact h1
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hsubR with h | h
  · refine false_of_range_eq_bot hLK hodd e q hqker ?_
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy', hyA⟩ := (hkey y).1 hy
    rw [h, mem_bot] at hyA
    exact mem_bot.mpr (congrArg Subtype.val hyA)
  · have hRS : (imageHom hLK q).range = S := by
      ext y
      constructor
      · intro hy
        obtain ⟨hy', -⟩ := (hkey y).1 hy
        rwa [hrange] at hy'
      · intro hy
        have hy' : y ∈ φ.range := hrange ▸ hy
        refine (hkey y).2 ⟨hy', ?_⟩
        rw [h]
        exact mem_top _
    have h20160 : Nat.card (imageHom hLK q).range = 20160 := by rw [hRS, card_S]
    have : IsSimpleGroup ↥(imageHom hLK q).range := (MulEquiv.subgroupCongr hRS).isSimpleGroup
    have h1 := card_range_dvd_card_sl2 hLK e q (by rw [h20160]; norm_num)
    have h2 := card_sl2_dvd hLK (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd)
      e q hqker
    rw [h20160, card_sl2] at h1 h2
    exact false_of_dvd_of_dvd hodd h1 (by simpa using h2)

end CFSG.ComponentClassification.TBLit.L34P

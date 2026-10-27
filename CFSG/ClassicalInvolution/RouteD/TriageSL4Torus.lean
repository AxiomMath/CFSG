module

public import CFSG.ClassicalInvolution.RouteD.TriageSL4X0
public import CFSG.ClassicalInvolution.RouteD.TriageSL4Class
public import CFSG.ClassicalInvolution.RouteD.GapsFive

public section

namespace CFSG.ClassicalInvolution.RouteD

open scoped MatrixGroups commutatorElement
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL2)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjSub_eq_of_le_centralizer {y : G} {N : Subgroup G}
    (h : N ≤ Subgroup.centralizer ({y} : Set G)) : conjSub y N = N := by
  have hcomm : ∀ m ∈ N, m * y = y * m := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.mp (h hm)
  ext n
  rw [mem_conjSub_iff]
  constructor
  · intro hn
    have h1 : (y⁻¹ * n * y) * y = y * (y⁻¹ * n * y) := hcomm _ hn
    have h2 : n = y⁻¹ * n * y := by
      calc n = y * (y⁻¹ * n * y) * y⁻¹ := by group
        _ = (y⁻¹ * n * y) * y * y⁻¹ := by rw [h1]
        _ = y⁻¹ * n * y := by group
    rw [h2]
    exact hn
  · intro hn
    have h1 := hcomm n hn
    have h2 : y⁻¹ * n * y = n := by
      calc y⁻¹ * n * y = y⁻¹ * (n * y) := by group
        _ = y⁻¹ * (y * n) := by rw [h1]
        _ = n := by group
    rw [h2]
    exact hn

theorem conjSub_sq_normalizes {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hshape : LocalShapeT p f 2 .PSL 4 (conjClass K) z) {β : Subgroup G}
    (hβ : β ∈ conjClass K) {t : G} (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {j₁ j₂ T : Subgroup G}
    (hj₁ : j₁ ∈ conjClass K) (hj₂ : j₂ ∈ conjClass K) (hT : T ∈ conjClass K)
    (hKj₁ : Commutes K j₁) (hKj₂ : Commutes K j₂) (hKT : Commutes K T)
    (hβj₁ : Commutes β j₁) (hβj₂ : Commutes β j₂) (hj₁₂ : Commutes j₁ j₂)
    (hTj₁ : Commutes T j₁) (hTj₂ : T ≠ j₂) {x₀ : G} (hx₀ : IsClassicalMember p f j₁ x₀) {y : G}
    (hyK : K ≤ Subgroup.centralizer ({y} : Set G)) (hyT : T ≤ Subgroup.centralizer ({y} : Set G))
    (hyx : y * x₀ * y⁻¹ = x₀) : conjSub (y * y) β = β := by
  classical
  obtain ⟨Θ, hker, hrange, hnodes, hbig⟩ := x0_chain S hshape hβ ht hKβ hj₁ hj₂ hT hKj₁ hKj₂ hKT
    hβj₁ hβj₂ hj₁₂ hTj₁ hTj₂ hx₀
  have hΩ : InClass p f (conjClass K) := S.inClass
  have hex := S.exact
  have hsingle : ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g K := single_class K
  have hKΩ : K ∈ conjClass K := mem_conjClass_self K
  obtain ⟨c⟩ := TCtx.nonempty_A3 S.odd S.five hΩ hex hKΩ S.cls S.p1 hshape
  obtain ⟨cx⟩ := Gaps.exists_ctx_member c hsingle hshape hj₁ hx₀
  have hne : ∀ {A B : Subgroup G}, A ∈ conjClass K → Commutes A B → A ≠ B := by
    intro A B hA hAB hAeq
    subst hAeq
    exact not_commutes_self_of_mem hΩ hA hAB
  have hKx : K ∈ centralizingMembers (conjClass K) {x₀} :=
    mem_centralizingMembers_of_commutes hKΩ hx₀.mem hKj₁
  have hβx : β ∈ centralizingMembers (conjClass K) {x₀} :=
    mem_centralizingMembers_of_commutes hβ hx₀.mem hβj₁
  have hTx : T ∈ centralizingMembers (conjClass K) {x₀} :=
    mem_centralizingMembers_of_commutes hT hx₀.mem hTj₁
  have hyyx : (y * y) * x₀ * (y * y)⁻¹ = x₀ := by
    calc (y * y) * x₀ * (y * y)⁻¹ = y * (y * x₀ * y⁻¹) * y⁻¹ := by group
      _ = x₀ := by rw [hyx, hyx]
  set σ' := locAut hΩ.conjInvariant hyx with hσ'
  have hfixK := (locAut_fixed_iff hΩ cx.hP1 hyx hKx).mp hyK
  have hfixT := (locAut_fixed_iff hΩ cx.hP1 hyx hTx).mp hyT
  have hβbig : locImg (conjClass K) x₀ (conjSub y β) ≤ Θ.range := by
    have hmem : conjSub y β ∈ centralizingMembers (conjClass K) {x₀} := by
      have := centralizingMembers_conj hΩ.conjInvariant y x₀
      rw [hyx] at this
      rw [this]
      exact ⟨β, hβx, rfl⟩
    have hnc : ¬ Commutes K β := by
      obtain ⟨W, hW⟩ := hKβ
      exact not_commutes_of_linearBlockStandardPair hW
    have hKy : conjSub y K = K := conjSub_eq_of_le_centralizer hyK
    have hnc' : ¬ Commutes K (conjSub y β) := fun h => hnc
      ((commutes_conjSub_iff (K := K) (L := β) y).mp (by rw [hKy]; exact h))
    exact hbig _ hmem (fun h => hnc' (by rw [h]; exact hKj₁))
      (fun h => hnc' (by rw [h]; exact hKj₂))
  have hgen : ∀ k : Fin 3, ∀ u ∈ locImg (conjClass K) x₀ (![K, β, T] k), σ' u ∈ Θ.range := by
    intro k u hu
    rw [hrange]
    fin_cases k
    · rw [hfixK u hu]
      exact (le_iSup (fun k => locImg (conjClass K) x₀ (![K, β, T] k)) 0) hu
    · have : σ' u ∈ locImg (conjClass K) x₀ (conjSub y β) := by
        rw [← locAut_locImg hΩ.conjInvariant hyx β]
        exact ⟨u, hu, rfl⟩
      rw [← hrange]
      exact hβbig this
    · rw [hfixT u hu]
      exact (le_iSup (fun k => locImg (conjClass K) x₀ (![K, β, T] k)) 2) hu
  have hstab : ∀ x, σ' (Θ x) ∈ Θ.range := by
    have h1 : (Θ.range).map σ'.toMonoidHom ≤ Θ.range := by
      rw [hrange, Subgroup.map_iSup]
      refine iSup_le fun k => ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [← hrange]
      exact hgen k u hu
    intro x
    exact h1 ⟨Θ x, ⟨x, rfl⟩, rfl⟩
  have hnode₀ : Subgroup.map Θ (blockSL2 (GaloisField p f) 3 0).range =
      locImg (conjClass K) x₀ K := hnodes 0
  have hnode₁ : Subgroup.map Θ (blockSL2 (GaloisField p f) 3 1).range =
      locImg (conjClass K) x₀ β := hnodes 1
  have hnode₂ : Subgroup.map Θ (blockSL2 (GaloisField p f) 3 2).range =
      locImg (conjClass K) x₀ T := hnodes 2
  have hfix₀ : ∀ A : SL(2, GaloisField p f), σ' (Θ (blockSL2 (GaloisField p f) 3 0 A)) =
      Θ (blockSL2 (GaloisField p f) 3 0 A) := fun A => hfixK _ (by
    rw [← hnode₀]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hfix₂ : ∀ A : SL(2, GaloisField p f), σ' (Θ (blockSL2 (GaloisField p f) 3 2 A)) =
      Θ (blockSL2 (GaloisField p f) 3 2 A) := fun A => hfixT _ (by
    rw [← hnode₂]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hcl : LinearAutClassification (GaloisField p f) (3 + 1) :=
    CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification S.odd S.five (by omega)
  have hcard : Nat.card (GaloisField p f) = p ^ f :=
    GaloisField.card p f (by
      have := S.five
      rintro rfl
      simp at this)
  have hcls := blocks_classification (by have := S.five; omega) hcl Θ hker σ' hstab hfix₀ hfix₂
  have hβmap : ∀ u ∈ locImg (conjClass K) x₀ β, σ' (σ' u) ∈ locImg (conjClass K) x₀ β := by
    intro u hu
    rw [← hnode₁] at hu ⊢
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hu
    rcases hcls with ⟨μ, hμ⟩ | ⟨-, hsq⟩
    · rw [hμ, hμ, slConjugation_diagGL_blockSL2_eq, slConjugation_diagGL_blockSL2_eq]
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    · rw [hsq]
      exact ⟨_, ⟨A, rfl⟩, rfl⟩
  have hmem : conjSub (y * y) β ∈ centralizingMembers (conjClass K) {x₀} := by
    have := centralizingMembers_conj hΩ.conjInvariant (y * y) x₀
    rw [hyyx] at this
    rw [this]
    exact ⟨β, hβx, rfl⟩
  have hle : locImg (conjClass K) x₀ (conjSub (y * y) β) ≤ locImg (conjClass K) x₀ β := by
    rw [← locAut_locImg hΩ.conjInvariant hyyx β]
    rintro _ ⟨u, hu, rfl⟩
    show locAut hΩ.conjInvariant hyyx u ∈ _
    rw [locAut_mul hΩ.conjInvariant hyx hyx hyyx u]
    exact hβmap u hu
  have hle' : conjSub (y * y) β ≤ β := le_of_locImg_le hΩ cx.hP1 hmem hle
  refine Subgroup.eq_of_le_of_card_ge hle' ?_
  unfold conjSub
  rw [Subgroup.card_map_of_injective (MulAut.conj (y * y)).injective]

end CFSG.ClassicalInvolution.RouteD

module

public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem isSubnormal_of_forall_conj {K : Type} [Group K] {C L : Subgroup K} (hLC : L ≤ C)
    (hLn : ∀ g ∈ C, ∀ f ∈ L, g * f * g⁻¹ ∈ L) : IsSubnormal L C := by
  refine IsSubnormal.step hLC ?_ (IsSubnormal.refl C)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLC]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro f
  refine ⟨fun hf => hLn g hg f hf, fun hf => ?_⟩
  have := hLn g⁻¹ (C.inv_mem hg) _ hf
  simpa [mul_assoc] using this

theorem glaPLayer_ne_bot_of_block {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {C L : Subgroup K} (hLC : L ≤ C) (hLq : CFSG.IsQuasisimple ↥L)
    (hLn : ∀ g ∈ C, ∀ f ∈ L, g * f * g⁻¹ ∈ L) (hpL : p ∣ Nat.card L) :
    GLAPLayer p C ≠ ⊥ := by
  classical
  have hsn : IsSubnormal L C := isSubnormal_of_forall_conj hLC hLn
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  set L' : Subgroup ↥C := L.subgroupOf C with hL'
  have hL'q : CFSG.IsQuasisimple ↥L' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC).symm hLq
  have hnk : ¬ L' ≤ π.ker := by
    intro hle
    have h1 : L ≤ GLAPPrimeCoreOf p C := by
      intro x hx
      have hxC : x ∈ C := hLC hx
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      have hx' : (⟨x, hxC⟩ : ↥C) ∈ L' := hx
      have := hle hx'
      rwa [hπ, QuotientGroup.ker_mk'] at this
    exact not_dvd_card_glaPPrimeCoreOf hp C (hpL.trans (Subgroup.card_dvd_of_le h1))
  have hq : CFSG.IsQuasisimple ↥(L'.map π) := CFSG.LocalCores.isQuasisimple_map hL'q π hnk
  have hqo : CFSG.Open.IsQuasisimple ↥(barX p C L) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.1 hq
  have hcomp : IsComponentOf (barX p C L) ⊤ := by
    refine ⟨le_top, ?_, hqo⟩
    have := isSubnormal_barX (C := C) p hsn
    rwa [barX_self] at this
  obtain ⟨L₁, hL₁, hbar⟩ := exists_glaPComponent_barX_eq C hcomp
  intro hbot
  have hle : L₁ ≤ GLAPLayer p C := le_sSup hL₁
  rw [hbot, le_bot_iff] at hle
  have hnt : Nontrivial ↥(barX p C L) := isQuasisimple_nontrivial hqo
  have hne : barX p C L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 hnt
  apply hne
  rw [← hbar, hle]
  simp [barX]

theorem exists_block_map {G K : Type} [Group G] [Group K] (e : G ≃* K) {p : ℕ} {d : G}
    (h : ∃ L : Subgroup G, L ≤ Subgroup.centralizer ({d} : Set G) ∧ CFSG.IsQuasisimple ↥L ∧
      (∀ g ∈ Subgroup.centralizer ({d} : Set G), ∀ f ∈ L, g * f * g⁻¹ ∈ L) ∧
        p ∣ Nat.card L) :
    ∃ L : Subgroup K, L ≤ Subgroup.centralizer ({e d} : Set K) ∧ CFSG.IsQuasisimple ↥L ∧
      (∀ g ∈ Subgroup.centralizer ({e d} : Set K), ∀ f ∈ L, g * f * g⁻¹ ∈ L) ∧
        p ∣ Nat.card L := by
  obtain ⟨L, hLC, hLq, hLn, hpL⟩ := h
  refine ⟨L.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hLC hx)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    change e x * e d = e d * e x
    rw [← map_mul, ← map_mul, this]
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective L e.toMonoidHom e.injective) hLq
  · rintro g hg _ ⟨f, hf, rfl⟩
    obtain ⟨g', rfl⟩ := e.surjective g
    have hg' : g' ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      apply e.injective
      change e (g' * d) = e (d * g')
      rw [map_mul, map_mul]
      exact hg
    exact ⟨g' * f * g'⁻¹, hLn g' hg' f hf, by simp⟩
  · rwa [Subgroup.card_map_of_injective e.injective]

end CFSG.LocalAnalysis.GLTheoremA

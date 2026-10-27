module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29Comp

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification
open scoped commutatorElement

section Conj

variable {G : Type*} [Group G]

theorem i183_gLBConj_iSup_le {g : G} {ι : Sort*} {P : ι → Prop} {F : ι → Subgroup G}
    {T : Subgroup G} (h : ∀ i, P i → GLBConj g (F i) ≤ T) :
    GLBConj g (⨆ (i) (_ : P i), F i) ≤ T := by
  unfold GLBConj at h ⊢
  rw [Subgroup.map_le_iff_le_comap]
  exact iSup₂_le fun i hi => Subgroup.map_le_iff_le_comap.1 (h i hi)

theorem i183_mem_normalizer_of_gLBConj_le {g : G} {T : Subgroup G} (h₁ : GLBConj g T ≤ T)
    (h₂ : GLBConj g⁻¹ T ≤ T) : g ∈ Subgroup.normalizer (T : Set G) := by
  refine mem_normalizer_iff_gLBConj_eq.2 (le_antisymm h₁ ?_)
  have h := gLBConj_mono g h₂
  rwa [gLBConj_gLBConj_inv] at h

theorem i183_mem_normalizer_biSup {g : G} {S : Set (Subgroup G)}
    (h : ∀ L ∈ S, g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((⨆ L ∈ S, L : Subgroup G) : Set G) := by
  refine i183_mem_normalizer_of_gLBConj_le (i183_gLBConj_iSup_le fun L hL => ?_)
    (i183_gLBConj_iSup_le fun L hL => ?_)
  · rw [gLBConj_eq_of_mem_normalizer (h L hL)]
    exact le_iSup₂_of_le L hL le_rfl
  · rw [gLBConj_eq_of_mem_normalizer (Subgroup.inv_mem _ (h L hL))]
    exact le_iSup₂_of_le L hL le_rfl

theorem i183_le_normalizer_biSup {H : Subgroup G} {S : Set (Subgroup G)}
    (h : ∀ L ∈ S, H ≤ Subgroup.normalizer (L : Set G)) :
    H ≤ Subgroup.normalizer ((⨆ L ∈ S, L : Subgroup G) : Set G) :=
  fun _ hg => i183_mem_normalizer_biSup fun L hL => h L hL hg

theorem i183_mem_normalizer_sup {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hA hB ⊢
  unfold GLBConj at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem i183_mem_normalizer_inf {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← hA, ← hB]

end Conj

section Family

variable {G : Type*} [Group G]

@[expose] def i183Family (p : ℕ) (X J : Subgroup G) : Set (Subgroup G) :=
  {L | GLAPComponent p X L ∧ ¬ ⁅J, L⁆ ≤ GLAPPrimeCoreOf p X}

theorem i183_le_of_commutator {p : ℕ} {X L J T : Subgroup G} (hL : GLAPComponent p X L)
    (hJX : J ≤ X) (hJL : J ≤ Subgroup.normalizer (L : Set G))
    (hLT : L ≤ Subgroup.normalizer (T : Set G)) (hT : ⁅J, L⁆ ≤ T)
    (hne : ¬ ⁅J, L⁆ ≤ GLAPPrimeCoreOf p X) : L ≤ T := by
  have hJLL : ⁅J, L⁆ ≤ L := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.1 hJL
  have hNL : T ⊓ L ≤ L := inf_le_right
  have hLN : L ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := fun g hg =>
    i183_mem_normalizer_inf (hLT hg) (Subgroup.le_normalizer hg)
  have hNsn : IsSubnormal (T ⊓ L) X :=
    IsSubnormal.step hNL ((Subgroup.normal_subgroupOf_iff_le_normalizer hNL).2 hLN) hL.2.1
  have hNbL : barX p X (T ⊓ L) ≤ barX p X L := barX_mono p hNL
  have : ((barX p X (T ⊓ L)).subgroupOf (barX p X L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNbL).2 (barX_le_normalizer hLN)
  have hcomm : ⁅barX p X J, barX p X L⁆ ≤ barX p X (T ⊓ L) := by
    rw [← barX_commutator p hJX hL.1]
    exact barX_mono p (le_inf hT hJLL)
  have hcomm_ne : ⁅barX p X J, barX p X L⁆ ≠ ⊥ := by
    rw [← barX_commutator p hJX hL.1, Ne, i183_barX_eq_bot_iff (commutator_le_of_le' hJX hL.1)]
    exact hne
  have hLq : CFSG.Open.IsQuasisimple ↥(barX p X L) := hL.2.2.1.2.2
  rcases Quasisimple.normal_le_center_or_eq_top hLq
      ((barX p X (T ⊓ L)).subgroupOf (barX p X L)) with hc | ht
  · exfalso
    have h1 : ⁅⁅barX p X J, barX p X L⁆, barX p X L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hxN : x ∈ barX p X (T ⊓ L) := hcomm hx
      have hxc := Subgroup.mem_center_iff.1
        (hc (show (⟨x, hNbL hxN⟩ : ↥(barX p X L)) ∈
          (barX p X (T ⊓ L)).subgroupOf (barX p X L) from hxN)) ⟨y, hy⟩
      exact congrArg Subtype.val hxc
    have h2 : ⁅⁅barX p X L, barX p X J⁆, barX p X L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (barX p X L) (barX p X J)]
      exact h1
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
    rw [barX_perfect_of_glaPComponent hL, Subgroup.commutator_comm] at h3
    exact hcomm_ne h3
  · have hLN' : barX p X L ≤ barX p X (T ⊓ L) := Subgroup.subgroupOf_eq_top.1 ht
    by_contra hLT'
    refine hL.2.2.2 (T ⊓ L) (lt_of_le_of_ne hNL fun h => hLT' ?_) hNsn (le_antisymm hNbL hLN')
    rw [← h]
    exact inf_le_left

theorem i183_gLBConj_mem_family {p : ℕ} {X E J L : Subgroup G} (hEX : E ≤ X)
    (hJE : J ≤ Subgroup.centralizer (E : Set G)) (hL : L ∈ i183Family p X J) {e : G}
    (he : e ∈ E) : GLBConj e L ∈ i183Family p X J := by
  have hJe : GLBConj e J = J := by
    refine gLBConj_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_iff.1 (hJE hj) e he).symm
  refine ⟨?_, fun hle => hL.2 ?_⟩
  · have h := glaPComponent_gLBConj hL.1 e
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hEX he))] at h
  · have h1 : GLBConj e ⁅J, L⁆ = ⁅J, GLBConj e L⁆ := by
      conv_rhs => rw [← hJe]
      exact Subgroup.map_commutator _ _ _
    have hle' : GLBConj e ⁅J, L⁆ ≤ GLAPPrimeCoreOf p X := by
      rw [h1]
      exact hle
    have h2 := gLBConj_mono e⁻¹ hle'
    rwa [gLBConj_inv_gLBConj, gLBConj_eq_of_mem_normalizer
      (le_normalizer_glaPPrimeCoreOf p X (hEX (E.inv_mem he)))] at h2

variable [Finite G]

theorem i183_glaPPrimeCoreOf_le_normalizer {p : ℕ} {X L : Subgroup G}
    (hL : GLAPComponent p X L) : GLAPPrimeCoreOf p X ≤ Subgroup.normalizer (L : Set G) := by
  have hle : GLAPPrimeCoreOf p X ≤ preimBarX p X L := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    show QuotientGroup.mk' (GLAPPrimeCore p ↥X) n ∈ barX p X L
    rw [h1]
    exact Subgroup.one_mem _
  exact hle.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX p hL.1)).1
    (glaPComponent_normal_preimBarX hL))

theorem i183_le_normalizer_of_glaPComponent {p : ℕ} (hp : p.Prime) {X L L' : Subgroup G}
    (hL : GLAPComponent p X L) (hL' : GLAPComponent p X L') :
    L' ≤ Subgroup.normalizer (L : Set G) := by
  by_cases h : L = L'
  · subst h
    exact Subgroup.le_normalizer
  · exact fun g hg => LocalBalance.mem_normalizer_of_ne hp hL hL' h hg

theorem i183_glaPLayer_le_normalizer {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) : GLAPLayer p X ≤ Subgroup.normalizer (L : Set G) :=
  sSup_le fun _ hL' => i183_le_normalizer_of_glaPComponent hp hL hL'

end Family

section Join

variable {G : Type} [Group G] [Finite G]

theorem i183_le_iSup_family {p : ℕ} (hp : p.Prime) {X Y J : Subgroup G}
    (hJ : GLAPComponent p Y J) (hJL : J ≤ GLAPLayer p X) :
    J ≤ ⨆ L ∈ i183Family p X J, L := by
  have hJX : J ≤ X := hJL.trans (i183_glaPLayer_le p X)
  have hlay : barX p X J ≤ Layer.subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := by
    refine (barX_mono p hJL).trans ((i183_barX_le_iff (i183_glaPLayer_le p X)).2 ?_)
    exact sSup_le fun L hL => (i183_barX_le_iff hL.1).1 (Layer.component_le hL.2.2.1)
  have hperf : ⁅barX p X J, barX p X J⁆ = barX p X J := by
    rw [← barX_commutator p hJX hJX, glaPComponent_perfect hJ]
  have h1 := le_layer_diff_of_perfect
    {K | IsComponentOf K ⊤ ∧ ⁅barX p X J, K⁆ = ⊥} (fun K hK => hK.1) hperf hlay
    (fun K hK => Subgroup.commutator_eq_bot_iff_le_centralizer.1 hK.2)
  have h2 : barX p X J ≤ barX p X (⨆ L ∈ i183Family p X J, L) := by
    refine h1.trans (iSup₂_le fun K hK => ?_)
    obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq X hK.1
    refine barX_mono p (le_iSup₂_of_le L ⟨hL, fun hle => hK.2 ⟨hK.1, ?_⟩⟩ le_rfl)
    rw [← barX_commutator p hJX hL.1]
    exact (i183_barX_eq_bot_iff (commutator_le_of_le' hJX hL.1)).2 hle
  refine i183_le_of_le_sup hp hJ (i183_coprime_card_glaPPrimeCoreOf hp X)
    (i183_le_normalizer_biSup fun L hL => i183_glaPPrimeCoreOf_le_normalizer hL.1) ?_
  intro k hk
  obtain ⟨m, hm, hmk⟩ := exists_of_barX_le h2 hk (hJX hk)
  have e : k = m * (m⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right hmk)

theorem i183_iSup_family_eq {p : ℕ} (hp : p.Prime) {X Y J : Subgroup G}
    (hJ : GLAPComponent p Y J) (hJL : J ≤ GLAPLayer p X) :
    (⨆ L ∈ i183Family p X J, L) = ⨆ g ∈ GLAPLayer p X, GLBConj g J := by
  have hJX : J ≤ X := hJL.trans (i183_glaPLayer_le p X)
  have hJT : J ≤ ⨆ g ∈ GLAPLayer p X, GLBConj g J :=
    le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (gLBConj_one J).ge
  have hTn : GLAPLayer p X ≤
      Subgroup.normalizer ((⨆ g ∈ GLAPLayer p X, GLBConj g J : Subgroup G) : Set G) := by
    have key : ∀ k ∈ GLAPLayer p X, GLBConj k (⨆ g ∈ GLAPLayer p X, GLBConj g J) ≤
        ⨆ g ∈ GLAPLayer p X, GLBConj g J := fun k hk =>
      i183_gLBConj_iSup_le fun g hg => by
        rw [gLBConj_gLBConj]
        exact le_iSup₂_of_le (g * k) (Subgroup.mul_mem _ hg hk) le_rfl
    exact fun h hh =>
      i183_mem_normalizer_of_gLBConj_le (key h hh) (key h⁻¹ (Subgroup.inv_mem _ hh))
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    have hLlay : L ≤ GLAPLayer p X := le_sSup hL.1
    refine i183_le_of_commutator hL.1 hJX (hJL.trans (i183_glaPLayer_le_normalizer hp hL.1))
      (hLlay.trans hTn) ?_ hL.2
    rw [Subgroup.commutator_le]
    intro j hj l hl
    have h2 : l * j⁻¹ * l⁻¹ ∈ ⨆ g ∈ GLAPLayer p X, GLBConj g J := by
      refine (le_iSup₂_of_le l⁻¹ (Subgroup.inv_mem _ (hLlay hl)) le_rfl :
        GLBConj l⁻¹ J ≤ _) ?_
      rw [mem_gLBConj]
      have e : l⁻¹ * (l * j⁻¹ * l⁻¹) * l⁻¹⁻¹ = j⁻¹ := by group
      rw [e]
      exact J.inv_mem hj
    have e : ⁅j, l⁆ = j * (l * j⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (hJT hj) h2
  · refine iSup₂_le fun g hg => ?_
    rw [← gLBConj_eq_of_mem_normalizer (i183_le_normalizer_biSup
      (fun L hL => i183_glaPLayer_le_normalizer hp hL.1) hg)]
    exact gLBConj_mono g (i183_le_iSup_family hp hJ hJL)

end Join

end CFSG.HardMathSupport.Solomon.Coordinator

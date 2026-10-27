module

public import CFSG.ClassicalInvolution.Uniform.U7Comp
public import CFSG.ClassicalInvolution.Uniform.U5G2D4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement


section Model

theorem g2Adm3 : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .G2 0 3 1 :=
  ⟨Nat.prime_three, le_refl 1, rfl, by norm_num⟩

theorem g2_centralizer_le_normalizer {R : Subgroup G2Model} (hR : R ∈ G2Fund) {c : G2Model}
    (hc : IsUniqueInvolution R c) :
    Subgroup.centralizer ({c} : Set G2Model) ≤ Subgroup.normalizer (R : Set G2Model) := by
  intro g hg
  have hg' : g * c = c * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hgc : g * c * g⁻¹ = c := by rw [hg']; group
  have h1 : IsUniqueInvolution (conjSub g R) c := by
    have := hc.conj g
    rwa [hgc] at this
  exact normalizer_iff_conjSub_eq.mpr
    (noTwins_g2 (p := 3) (e := 1) (by norm_num) le_rfl R hR c hc g h1)

end Model

section Stabilizer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z j a : G}

theorem mem_of_invariant_g2_three (hgen : G2NonToralGenerate3) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (C : G2Comp Ω) {R S : Subgroup G2Model} (hR : R ∈ G2Fund)
    (h : QuotViol Ω (R.map C.ψ) (S.map C.ψ) z j a) {𝒮 : Set (Subgroup G)}
    (hnorm : ∀ M ∈ 𝒮, ∀ x : G, conjSub x M = M → x ∈ conjStab 𝒮)
    (htwin : ∀ M ∈ 𝒮, ∀ M' ∈ twinSet Ω M, M' ≠ M → M' ∈ 𝒮)
    (hKC : R.map C.ψ ∈ 𝒮) (hJC : S.map C.ψ ∈ 𝒮) {R' : Subgroup G2Model}
    (hR' : R' ∈ G2Fund) (hR'Ω : R'.map C.ψ ∈ Ω) : R'.map C.ψ ∈ 𝒮 := by
  set ψ := C.ψ with hψ
  have hinj : Function.Injective ψ := C.inj
  set Sg : Subgroup G2Model := (conjStab 𝒮).comap ψ with hSg
  have hN : Subgroup.normalizer (R : Set G2Model) ≤ Sg := by
    intro g hg
    refine hnorm _ hKC _ ?_
    rw [← AscQuot.map_conjSub, mem_normalizer_iff_conjSub_eq.mp hg]
  obtain ⟨c, hcz, hc⟩ := isUniqueInvolution_of_map hinj h.hz
  have hrange : R.map ψ ⊔ S.map ψ ≤ ψ.range :=
    sup_le (Subgroup.map_le_range _ _) (Subgroup.map_le_range _ _)
  obtain ⟨a₀, ha₀⟩ := hrange (mem_sup_of_mem_pairNormalizers h.ha)
  have haC : a ∈ conjStab 𝒮 := by
    have : pairNormalizers (R.map ψ) (S.map ψ) z j ≤ conjStab 𝒮 := by
      unfold pairNormalizers
      refine sup_le (inf_le_left.trans ?_) (inf_le_left.trans ?_)
      · intro x hx
        exact hnorm _ hKC x (conjSub_eq_self_of_mem hx)
      · intro x hx
        exact hnorm _ hJC x (conjSub_eq_self_of_mem hx)
    exact this h.ha
  have ha₀S : a₀ ∈ Sg := by
    show ψ a₀ ∈ conjStab 𝒮
    rw [ha₀]
    exact haC
  have hVn : pairNormalizers (R.map ψ) (S.map ψ) z j ≤
      Subgroup.normalizer ((Subgroup.closure {z, j} : Subgroup G) : Set G) :=
    sup_le inf_le_right inf_le_right
  have haV : a * z * a⁻¹ ∈ (Subgroup.closure {z, j} : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp (hVn h.ha) z).mp (Subgroup.subset_closure (by simp))
  have hVc : (Subgroup.closure {z, j} : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h.comm.symm
  have hazc : a * z * a⁻¹ * z = z * (a * z * a⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hVc haV)
  have haz : a * z * a⁻¹ ≠ z := by
    intro h2
    have h3 : a * z * a⁻¹ = a * j * a⁻¹ := h2.trans h.haj.symm
    exact h.ne (mul_left_cancel (mul_right_cancel h3))
  have hc'z : ψ (a₀ * c * a₀⁻¹) = a * z * a⁻¹ := by
    rw [map_mul, map_mul, map_inv, hcz, ha₀]
  have hc'sq : a₀ * c * a₀⁻¹ * (a₀ * c * a₀⁻¹) = 1 := by
    calc a₀ * c * a₀⁻¹ * (a₀ * c * a₀⁻¹) = a₀ * (c * c) * a₀⁻¹ := by group
      _ = 1 := by rw [hc.sq]; group
  have hc'1 : a₀ * c * a₀⁻¹ ≠ 1 := by
    intro h1
    apply hc.ne_one
    calc c = a₀⁻¹ * (a₀ * c * a₀⁻¹) * a₀ := by group
      _ = 1 := by rw [h1]; group
  have hcc' : c ≠ a₀ * c * a₀⁻¹ := by
    intro e
    apply haz
    rw [← hc'z, ← e, hcz]
  have hcomm : c * (a₀ * c * a₀⁻¹) = a₀ * c * a₀⁻¹ * c := by
    apply hinj
    have h1 : ψ (c * (a₀ * c * a₀⁻¹)) = z * (a * z * a⁻¹) := by rw [map_mul, hc'z, hcz]
    have h2 : ψ (a₀ * c * a₀⁻¹ * c) = a * z * a⁻¹ * z := by rw [map_mul, hc'z, hcz]
    rw [h1, h2]
    exact hazc.symm
  have hCS : Subgroup.centralizer ({c} : Set G2Model) ≤ Sg :=
    (g2_centralizer_le_normalizer hR hc).trans hN
  have hCS' : Subgroup.centralizer ({a₀ * c * a₀⁻¹} : Set G2Model) ≤ Sg := by
    intro x hx
    have hx' : x * (a₀ * c * a₀⁻¹) = a₀ * c * a₀⁻¹ * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    have hy : a₀⁻¹ * x * a₀ ∈ Subgroup.centralizer ({c} : Set G2Model) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc a₀⁻¹ * x * a₀ * c = a₀⁻¹ * (x * (a₀ * c * a₀⁻¹)) * a₀ := by group
        _ = a₀⁻¹ * (a₀ * c * a₀⁻¹ * x) * a₀ := by rw [hx']
        _ = c * (a₀⁻¹ * x * a₀) := by group
    have := Sg.mul_mem (Sg.mul_mem ha₀S (hCS hy)) (Sg.inv_mem ha₀S)
    have e : a₀ * (a₀⁻¹ * x * a₀) * a₀⁻¹ = x := by group
    rwa [e] at this
  have hSgtop : Sg = ⊤ := by
    have h1 := g2_pairGen3 hgen c (a₀ * c * a₀⁻¹) hc.sq hc'sq hc.ne_one hc'1 hcc' hcomm
    rw [eq_top_iff, ← h1]
    exact sup_le hCS hCS'
  have hall : ∀ g : G2Model, ψ g ∈ conjStab 𝒮 := fun g => by
    have : g ∈ Sg := hSgtop ▸ Subgroup.mem_top g
    exact this
  obtain ⟨z', hz'⟩ := hΩ.classical _ hR'Ω
  obtain ⟨c₂, -, hc₂⟩ := isUniqueInvolution_of_map hinj hz'.isUniqueInvolution_sl2
  obtain ⟨g, hg⟩ := Balance.Bootstrap.twoClassInvolutionsConj 3 .G2 0 1 (by norm_num)
    (Or.inl rfl) g2Adm3 R hR R' hR' c hc.mem c₂ hc₂.mem hc.sq hc₂.sq hc.ne_one hc₂.ne_one
    (fun y hy => hc.commute_of_mem hy) (fun y hy => hc₂.commute_of_mem hy)
  have hc'' : IsUniqueInvolution (conjSub g R) c₂ := by
    have := hc.conj g
    rwa [hg] at this
  have hK''C : (conjSub g R).map ψ ∈ 𝒮 := by
    rw [AscQuot.map_conjSub]
    exact (hall g _).mpr hKC
  by_cases hRR : R' = conjSub g R
  · rw [hRR]
    exact hK''C
  · have hne : R'.map ψ ≠ (conjSub g R).map ψ := fun e => hRR (Subgroup.map_injective hinj e)
    exact htwin _ hK''C _ ⟨hR'Ω, ψ c₂, isUniqueInvolution_map_of_inj hinj hc'',
      isUniqueInvolution_map_of_inj hinj hc₂⟩ hne

end Stabilizer

end CFSG.ClassicalInvolution.Uniform

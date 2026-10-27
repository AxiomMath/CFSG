module

public import CFSG.ClassicalInvolution.SmallCases.G2SLemA
public import CFSG.ClassicalInvolution.SmallCases.G2SModel
public import CFSG.ClassicalInvolution.SmallCases.G2SRange

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.Open (classicalInvolutionOddCore)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

namespace Ctx

variable {Ω : Set (Subgroup G)} {L : Subgroup G} {w : G}

theorem lemmaA (C : Ctx p f Ω L w) {A : Subgroup G} (hA : A ∈ nbhd Ω L) {a : G}
    (ha : IsClassicalMember p f A a) {s : G} (hs2 : s * s = 1) (hsw : s * w = w * s)
    (hsA : ∀ x ∈ A, s * x = x * s) :
    (∀ x ∈ layer Ω L, s * x = x * s) ∨ (∀ x ∈ layer Ω L, (s * a) * x = x * (s * a)) := by
  classical
  obtain ⟨D, i₁, hcard, htag, hrest⟩ := C.exists_data
  have hsw' : s * w * s⁻¹ = w := mul_inv_eq_iff_eq_mul.mpr hsw
  have hsN := C.mem_normalizer_of_cent hsw'
  have he : 1 ≤ D.exp i₁ := (D.admissible i₁).2.1
  have hψ : Function.Injective (D.hom i₁) :=
    injective_of_ker_le_center C.odd htag (D.rank i₁) he (D.hom i₁) (D.ker_le_center i₁)
  obtain ⟨R, hR, hAR, r, hrR, hr2, hr1, hrc, hr⟩ :=
    C.exists_model_involution D i₁ hcard htag hrest hA ha
  have haY : a ∈ locLayer Ω w :=
    le_centralizingLayer (C.nbhd_mem_centralizingMembers hA) ha.mem
  have ha2 : a * a = 1 := by
    have h2 : a ^ 2 = 1 := by rw [← ha.orderOf_eq_two]; exact pow_orderOf_eq_one a
    simpa [pow_two] using h2
  set mk := QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) with hmk
  set φ := actQuot Ω w s hsN with hφ
  have hrange : ∀ q ∈ (D.hom i₁).range, φ q ∈ (D.hom i₁).range := by
    intro q hq
    rw [C.range_eq D i₁ hcard htag hrest] at hq
    have hle : (⨆ N ∈ nbhd Ω L, locImg Ω w N) ≤
        (D.hom i₁).range.comap φ.toMonoidHom := by
      refine iSup₂_le fun N hN u hu => ?_
      obtain ⟨y, hy, rfl⟩ := hu
      have hN' : conjSub s N ∈ nbhd Ω L := by
        have := nbhd_conj C.inClass.conjInvariant s hN
        rwa [C.conjSub_eq_of_cent hsw'] at this
      have hmem : (⟨s * (y : G) * s⁻¹, Asc77.S24.conj_mem_of_mem_normalizer _ hsN y.2⟩ :
          ↥(locLayer Ω w)) ∈ (conjSub s N).subgroupOf (locLayer Ω w) :=
        Subgroup.mem_subgroupOf.mpr (conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hy))
      rw [Subgroup.mem_comap]
      show φ (mk y) ∈ (D.hom i₁).range
      rw [hφ, actQuot_mk]
      exact (C.nbhd_mem_compMembers D i₁ hcard htag hrest hN').2 ⟨_, hmem, rfl⟩
    exact hle hq
  have hfix : ∀ y ∈ R, φ (D.hom i₁ y) = D.hom i₁ y := by
    intro y hy
    have hmem : D.hom i₁ y ∈ locImg Ω w A := hAR ▸ Subgroup.mem_map_of_mem _ hy
    obtain ⟨x', hx', hxeq⟩ := hmem
    rw [← hxeq]
    exact actQuot_mk_of_comm Ω w hsN x'.2 (hsA x' (Subgroup.mem_subgroupOf.mp hx'))
  have hZ : ∀ g : (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K,
      (∀ x, g * x = x * g) → g = 1 := by
    intro g hg
    have hbot := center_modelUniv_g2d4_eq_bot C.odd htag (D.rank i₁) he
    have : g ∈ Subgroup.center (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K :=
      Subgroup.mem_center_iff.mpr fun x => (hg x).symm
    rw [hbot] at this
    exact this
  have hZR : ∀ g ∈ R, (∀ y ∈ R, g * y = y * g) → g * g = 1 → g = 1 ∨ g = r := by
    intro g hgR hgc _
    by_cases hg1 : g = 1
    · exact Or.inl hg1
    · right
      have hcard2 := card_center_locImg_dvd_two C.inClass C.exact
        (C.nbhd_mem_centralizingMembers hA)
      have mkc : ∀ c ∈ R, (∀ y ∈ R, c * y = y * c) →
          ∃ z : ↥(Subgroup.center ↥(locImg Ω w A)), (z : ↥(locImg Ω w A)).1 = D.hom i₁ c := by
        intro c hcR hcc
        have hm : D.hom i₁ c ∈ locImg Ω w A := hAR ▸ Subgroup.mem_map_of_mem _ hcR
        refine ⟨⟨⟨D.hom i₁ c, hm⟩, ?_⟩, rfl⟩
        rw [Subgroup.mem_center_iff]
        rintro ⟨u, hu⟩
        rw [hAR] at hu
        obtain ⟨y, hyR, rfl⟩ := hu
        apply Subtype.ext
        show D.hom i₁ y * D.hom i₁ c = D.hom i₁ c * D.hom i₁ y
        rw [← map_mul, ← map_mul, (hcc y hyR).symm]
      obtain ⟨zg, hzg⟩ := mkc g hgR hgc
      obtain ⟨zr, hzr⟩ := mkc r hrR hrc
      have hzg1 : zg ≠ 1 := by
        intro h
        apply hg1
        apply hψ
        rw [map_one, ← hzg, h]
        rfl
      have hzr1 : zr ≠ 1 := by
        intro h
        apply hr1
        apply hψ
        rw [map_one, ← hzr, h]
        rfl
      have := eq_of_card_dvd_two hcard2 hzg1 hzr1
      apply hψ
      rw [← hzg, ← hzr, this]
  have hdich := dichotomy_of_fg0 (D.hom i₁) hψ hZ (fg0Model_of_tag C.odd he htag hR) hZR φ
    (actQuot_sq Ω w hsN hs2) (fun g => hrange _ ⟨g, rfl⟩) hfix
  have hxmem : ∀ x ∈ layer Ω L, ∃ hxY : x ∈ locLayer Ω w, ∃ g,
      D.hom i₁ g = mk ⟨x, hxY⟩ := fun x hx =>
    ⟨C.layer_le_locLayer hx, C.mk_mem_range_of_mem_layer D i₁ hcard htag hrest hx _⟩
  rcases hdich with h1 | h2
  · left
    refine C.lift_trivial ?_
    intro x hx
    obtain ⟨hxY, g, hg⟩ := hxmem x hx
    have hφx : φ (mk ⟨x, hxY⟩) = mk ⟨x, hxY⟩ := by rw [← hg]; exact h1 g
    rw [hφ, actQuot_mk] at hφx
    exact mem_oddCoreOf_of_mk_eq (Asc77.S24.conj_mem_of_mem_normalizer _ hsN hxY) hxY hφx
  · right
    refine C.lift_trivial ?_
    intro x hx
    obtain ⟨hxY, g, hg⟩ := hxmem x hx
    have hax : a * x * a⁻¹ ∈ locLayer Ω w :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ haY hxY) (Subgroup.inv_mem _ haY)
    have hu : s * (a * x * a⁻¹) * s⁻¹ ∈ locLayer Ω w :=
      Asc77.S24.conj_mem_of_mem_normalizer _ hsN hax
    have hmka2 : mk ⟨a, haY⟩ * mk ⟨a, haY⟩ = 1 := by
      rw [← map_mul]
      have : (⟨a, haY⟩ : ↥(locLayer Ω w)) * ⟨a, haY⟩ = 1 := Subtype.ext ha2
      rw [this, map_one]
    have e1 : mk ⟨s * (a * x * a⁻¹) * s⁻¹, hu⟩ = φ (mk ⟨a * x * a⁻¹, hax⟩) :=
      (actQuot_mk Ω w hsN ⟨a * x * a⁻¹, hax⟩).symm
    have e2 : mk ⟨a * x * a⁻¹, hax⟩ = mk ⟨a, haY⟩ * mk ⟨x, hxY⟩ * (mk ⟨a, haY⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have e3 : φ (mk ⟨a, haY⟩) = mk ⟨a, haY⟩ :=
      actQuot_mk_of_comm Ω w hsN haY (hsA a ha.mem)
    have e4 : φ (mk ⟨x, hxY⟩) = mk ⟨a, haY⟩ * mk ⟨x, hxY⟩ * (mk ⟨a, haY⟩)⁻¹ := by
      rw [← hg, h2 g, hr]
    have key : mk ⟨s * (a * x * a⁻¹) * s⁻¹, hu⟩ = mk ⟨x, hxY⟩ := by
      calc mk ⟨s * (a * x * a⁻¹) * s⁻¹, hu⟩
          = φ (mk ⟨a, haY⟩ * mk ⟨x, hxY⟩ * (mk ⟨a, haY⟩)⁻¹) := by rw [e1, e2]
        _ = mk ⟨a, haY⟩ * (mk ⟨a, haY⟩ * mk ⟨x, hxY⟩ * (mk ⟨a, haY⟩)⁻¹) * (mk ⟨a, haY⟩)⁻¹ := by
          rw [map_mul, map_mul, map_inv, e3, e4]
        _ = (mk ⟨a, haY⟩ * mk ⟨a, haY⟩) * mk ⟨x, hxY⟩ *
            (mk ⟨a, haY⟩ * mk ⟨a, haY⟩)⁻¹ := by group
        _ = mk ⟨x, hxY⟩ := by rw [hmka2]; group
    have h3 := mem_oddCoreOf_of_mk_eq hu hxY key
    have e : (s * a) * x * (s * a)⁻¹ * x⁻¹ = s * (a * x * a⁻¹) * s⁻¹ * x⁻¹ := by group
    rw [e]
    exact h3

end Ctx

end CFSG.ClassicalInvolution.NDB.G2S

module

public import CFSG.ClassicalInvolution.SmallCases.G2SNorm
public import CFSG.ClassicalInvolution.SmallCases.G2SGenModel

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

theorem range_le_map_layer (C : Ctx p f Ω L w)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) (i₁ : Fin D.card) (hcard : D.card = 2)
    (htag : D.tag i₁ = .G2 ∨ D.tag i₁ = .trialityD4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) {u : locQuot Ω w}
    (hu : u ∈ (D.hom i₁).range) :
    ∃ x : ↥(locLayer Ω w), (x : G) ∈ layer Ω L ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) x = u := by
  rw [C.range_eq D i₁ hcard htag hrest] at hu
  have hle : (⨆ N ∈ nbhd Ω L, locImg Ω w N) ≤
      ((layer Ω L).subgroupOf (locLayer Ω w)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w))) := by
    refine iSup₂_le fun N hN v hv => ?_
    obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨y, Subgroup.mem_subgroupOf.mpr (le_layer hN (Subgroup.mem_subgroupOf.mp hy)), rfl⟩
  obtain ⟨x, hx, hxu⟩ := hle hu
  exact ⟨x, Subgroup.mem_subgroupOf.mp hx, hxu⟩

theorem layer_le_normalizer_of_pair (C : Ctx p f Ω L w) {M M' : Subgroup G}
    (hM : M ∈ nbhd Ω L) (hM' : M' ∈ nbhd Ω L) (hne : M ≠ M') {t s : G}
    (ht : IsClassicalMember p f M t) (hs : IsClassicalMember p f M' s) (hts : t * s = s * t)
    {Q : Subgroup G}
    (hQt : ∀ c : G, c * t * c⁻¹ = t → c ∈ Subgroup.normalizer (Q : Set G))
    (hQs : ∀ c : G, c * s * c⁻¹ = s → c ∈ Subgroup.normalizer (Q : Set G)) :
    layer Ω L ≤ Subgroup.normalizer (Q : Set G) := by
  classical
  obtain ⟨D, i₁, hcard, htag, hrest⟩ := C.exists_data
  have he : 1 ≤ D.exp i₁ := (D.admissible i₁).2.1
  have hψ : Function.Injective (D.hom i₁) :=
    injective_of_ker_le_center C.odd htag (D.rank i₁) he (D.hom i₁) (D.ker_le_center i₁)
  obtain ⟨R, hR, -, r, hrR, hr2, hr1, hrc, hr⟩ :=
    C.exists_model_involution D i₁ hcard htag hrest hM ht
  obtain ⟨R', hR', -, r', hr'R', hr'2, hr'1, hr'c, hr'⟩ :=
    C.exists_model_involution D i₁ hcard htag hrest hM' hs
  have htY : t ∈ locLayer Ω w :=
    le_centralizingLayer (C.nbhd_mem_centralizingMembers hM) ht.mem
  have hsY : s ∈ locLayer Ω w :=
    le_centralizingLayer (C.nbhd_mem_centralizingMembers hM') hs.mem
  have hsq : ∀ {N : Subgroup G} {u : G}, IsClassicalMember p f N u → u * u = 1 := by
    intro N u hu
    have h2 : u ^ 2 = 1 := by rw [← hu.orderOf_eq_two]; exact pow_orderOf_eq_one u
    simpa [pow_two] using h2
  set mk := QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) with hmk
  have hne' : r ≠ r' := by
    intro h
    have h1 : mk ⟨t, htY⟩ = mk ⟨s, hsY⟩ := by rw [← hr, ← hr', h]
    have h2 := eq_of_mk_eq_of_involutions C.p1 htY hsY (hsq ht) (hsq hs) h1
    subst h2
    exact hne (C.uniq M hM.1 M' hM'.1 t ht hs)
  have hcomm : r * r' = r' * r := by
    apply hψ
    rw [map_mul, map_mul, hr, hr', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hts
  have h5 : D.tag i₁ = .G2 → 5 ≤ p ^ D.exp i₁ := by
    intro hg
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · rw [h]
      exact C.five
    · rw [hg] at h
      exact absurd h (by decide)
  have hgen := model_sup_centralizer_eq_top C.odd (D.admissible i₁) htag h5 hr2 hr'2 hr1 hr'1
    hne' hcomm
  set T : Subgroup G := Subgroup.normalizer (Q : Set G) with hT
  set Hq : Subgroup (locQuot Ω w) :=
    ((T ⊓ layer Ω L).subgroupOf (locLayer Ω w)).map mk with hHq
  have key : ∀ {u : G} {ρ : (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K}
      (huY : u ∈ locLayer Ω w), u * u = 1 → D.hom i₁ ρ = mk ⟨u, huY⟩ →
      (∀ c : G, c * u * c⁻¹ = u → c ∈ T) →
      ∀ {e : (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K}, e * ρ = ρ * e →
        D.hom i₁ e ∈ Hq := by
    intro u ρ huY hu2 hρ hQ e hcomm
    obtain ⟨y, hyL, hy⟩ := C.range_le_map_layer D i₁ hcard htag hrest ⟨e, rfl⟩
    have hy' : mk y = D.hom i₁ e := hy
    have hyuY : (y : G) * u * (y : G)⁻¹ ∈ locLayer Ω w :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ y.2 huY) (Subgroup.inv_mem _ y.2)
    have hyu : (y : G) * u * (y : G)⁻¹ = u := by
      refine eq_of_mk_eq_of_involutions C.p1 hyuY huY ?_ hu2 ?_
      · calc (y : G) * u * (y : G)⁻¹ * ((y : G) * u * (y : G)⁻¹)
            = (y : G) * (u * u) * (y : G)⁻¹ := by group
          _ = 1 := by rw [hu2]; group
      · have e1 : (⟨(y : G) * u * (y : G)⁻¹, hyuY⟩ : ↥(locLayer Ω w)) = y * ⟨u, huY⟩ * y⁻¹ :=
          Subtype.ext rfl
        rw [e1, map_mul, map_mul, map_inv, hy', ← hρ, ← map_inv, ← map_mul, ← map_mul, hcomm]
        simp
    exact ⟨y, Subgroup.mem_subgroupOf.mpr ⟨hQ _ hyu, hyL⟩, hy'⟩
  have hrange : (D.hom i₁).range ≤ Hq := by
    have hsup : (D.hom i₁).range =
        (Subgroup.centralizer ({r} : Set _)).map (D.hom i₁) ⊔
          (Subgroup.centralizer ({r'} : Set _)).map (D.hom i₁) := by
      rw [← Subgroup.map_sup, hgen, Subgroup.map_top]
    rw [hsup]
    refine sup_le ?_ ?_
    · rintro _ ⟨e, he, rfl⟩
      exact key htY (hsq ht) hr hQt (Subgroup.mem_centralizer_singleton_iff.mp he)
    · rintro _ ⟨e, he, rfl⟩
      exact key hsY (hsq hs) hr' hQs (Subgroup.mem_centralizer_singleton_iff.mp he)
  refine le_of_perfect_of_cover (Y := locLayer Ω w) (Z := Asc77.oddCoreOf (locLayer Ω w))
    C.layer_le_locLayer (Asc77.oddCoreOf_le_self _) C.oddCore_central C.layer_le_commutator ?_
  intro x hx
  have hxY : x ∈ locLayer Ω w := C.layer_le_locLayer hx
  have hmem : mk ⟨x, hxY⟩ ∈ (D.hom i₁).range :=
    C.mk_mem_range_of_mem_layer D i₁ hcard htag hrest hx hxY
  obtain ⟨y, hy, hyx⟩ := hrange hmem
  have hy' := Subgroup.mem_subgroupOf.mp hy
  refine ⟨(y : G), hy'.1, ?_⟩
  have hO : y⁻¹ * ⟨x, hxY⟩ ∈ classicalInvolutionOddCore ↥(locLayer Ω w) := QuotientGroup.eq.mp hyx
  exact Asc77.mem_oddCoreOf_iff.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ y.2) hxY, hO⟩

end Ctx

end CFSG.ClassicalInvolution.NDB.G2S

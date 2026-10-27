module

public import CFSG.ClassicalInvolution.SmallCases.G2SBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.G2D4
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

namespace Ctx

variable {Ω : Set (Subgroup G)} {L : Subgroup G} {w : G}

theorem layer_eq (C : Ctx p f Ω L w) : centralizingLayer Ω {w} = L ⊔ layer Ω L := by
  unfold centralizingLayer layer
  rw [C.omega_eq, iSup_insert]

theorem exists_model_involution (C : Ctx p f Ω L w)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) (i₁ : Fin D.card) (hcard : D.card = 2)
    (htag : D.tag i₁ = .G2 ∨ D.tag i₁ = .trialityD4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) {M : Subgroup G}
    (hM : M ∈ nbhd Ω L) {u : G} (hu : IsClassicalMember p f M u) :
    ∃ (R : Subgroup (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K),
      R ∈ fundamentalSubgroups (D.tag i₁)
        (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).D ∧
      locImg Ω w M = R.map (D.hom i₁) ∧
      ∃ r ∈ R, r * r = 1 ∧ r ≠ 1 ∧ (∀ y ∈ R, r * y = y * r) ∧
        D.hom i₁ r = QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w))
          ⟨u, le_centralizingLayer (C.nbhd_mem_centralizingMembers hM) hu.mem⟩ := by
  have hψ : Function.Injective (D.hom i₁) :=
    injective_of_ker_le_center C.odd htag (D.rank i₁) (D.admissible i₁).2.1 (D.hom i₁)
      (D.ker_le_center i₁)
  have hMc := C.nbhd_mem_centralizingMembers hM
  obtain ⟨R, hRc⟩ := exists_corr_left C.inClass C.exact D
    (C.nbhd_mem_compMembers D i₁ hcard htag hrest hM)
  obtain ⟨huY, hum, husq, hu1, huc⟩ := image_involution_facts hMc hu
  rw [hRc.2.2] at hum huc
  obtain ⟨r, hrR, hr⟩ := hum
  refine ⟨R, hRc.2.1, hRc.2.2, r, hrR, ?_, ?_, ?_, hr⟩
  · exact hψ (by rw [map_mul, hr, husq, map_one])
  · intro h
    rw [h, map_one] at hr
    exact hu1 hr.symm
  · intro y hy
    apply hψ
    rw [map_mul, map_mul, hr]
    exact huc (D.hom i₁ y) ⟨y, hy, rfl⟩

theorem nbhd_transitive (C : Ctx p f Ω L w) {N N' : Subgroup G} (hN : N ∈ nbhd Ω L)
    (hN' : N' ∈ nbhd Ω L) : ∃ y ∈ centralizingLayer Ω {w}, N' = conjSub y N := by
  obtain ⟨D, i₁, hcard, htag, hrest⟩ := C.exists_data
  obtain ⟨wN, hwN⟩ := C.inClass.classical N hN.1
  obtain ⟨wN', hwN'⟩ := C.inClass.classical N' hN'.1
  obtain ⟨R, hR, -, r, hrR, hr2, hr1, hrc, hr⟩ :=
    C.exists_model_involution D i₁ hcard htag hrest hN hwN
  obtain ⟨R', hR', -, r', hr'R', hr'2, hr'1, hr'c, hr'⟩ :=
    C.exists_model_involution D i₁ hcard htag hrest hN' hwN'
  obtain ⟨g, hg⟩ := C.inv (D.tag i₁) (D.rank i₁) (D.exp i₁) C.odd htag (D.admissible i₁) R hR R'
    hR' r hrR r' hr'R' hr2 hr'2 hr1 hr'1 hrc hr'c
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (classicalInvolutionOddCore ↥(locLayer Ω w)) (D.hom i₁ g)
  refine ⟨(y : G), y.2, ?_⟩
  have hwNY : wN ∈ locLayer Ω w :=
    le_centralizingLayer (C.nbhd_mem_centralizingMembers hN) hwN.mem
  have hwN'Y : wN' ∈ locLayer Ω w :=
    le_centralizingLayer (C.nbhd_mem_centralizingMembers hN') hwN'.mem
  have h₁ : (y : G) * wN * (y : G)⁻¹ ∈ locLayer Ω w :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ y.2 hwNY) (Subgroup.inv_mem _ y.2)
  have hsq : ∀ {M : Subgroup G} {u : G}, IsClassicalMember p f M u → u * u = 1 := by
    intro M u hu
    have h2 : u ^ 2 = 1 := by rw [← hu.orderOf_eq_two]; exact pow_orderOf_eq_one u
    simpa [pow_two] using h2
  have heq : (y : G) * wN * (y : G)⁻¹ = wN' := by
    refine eq_of_mk_eq_of_involutions C.p1 h₁ hwN'Y ?_ (hsq hwN') ?_
    · calc (y : G) * wN * (y : G)⁻¹ * ((y : G) * wN * (y : G)⁻¹) =
          (y : G) * (wN * wN) * (y : G)⁻¹ := by group
        _ = 1 := by rw [hsq hwN]; group
    · have e1 : (⟨(y : G) * wN * (y : G)⁻¹, h₁⟩ : ↥(locLayer Ω w)) =
          y * ⟨wN, hwNY⟩ * y⁻¹ := Subtype.ext rfl
      rw [e1, map_mul, map_mul, map_inv, hy, ← hr, ← map_inv, ← map_mul, ← map_mul, hg, hr']
  have hcls : IsClassicalMember p f (conjSub (y : G) N) ((y : G) * wN * (y : G)⁻¹) :=
    hwN.conj _
  rw [heq] at hcls
  exact (C.uniq _ (C.inClass.conjInvariant _ N hN.1) N' hN'.1 wN' hcls hwN').symm

end Ctx

theorem generated_pair {K : Subgroup G} {z : G} (C : Ctx p f (𝒞 K) K z)
    (hconn : RouteD.DeltaConnected (𝒞 K)) {M : Subgroup G} (hM : M ∈ nbhd (𝒞 K) K) :
    ∀ N ∈ 𝒞 K, N ≤ layer (𝒞 K) K ⊔ layer (𝒞 K) M := by
  classical
  set G₀ : Subgroup G := layer (𝒞 K) K ⊔ layer (𝒞 K) M with hG₀
  have hKM : K ≤ layer (𝒞 K) M := le_layer (nbhd_symm C.mem hM)
  have hMK : M ≤ layer (𝒞 K) K := le_layer hM
  have hKG : K ≤ G₀ := hKM.trans le_sup_right
  have hMG : M ≤ G₀ := hMK.trans le_sup_left
  obtain ⟨h₀, hh₀⟩ := single_class K M hM.1
  have CM : Ctx p f (𝒞 K) M (h₀ * z * h₀⁻¹) := by
    rw [hh₀]
    exact C.conj h₀
  have hYK : centralizingLayer (𝒞 K) {z} ≤ G₀ := by
    rw [C.layer_eq]
    exact sup_le hKG le_sup_left
  have hYM : centralizingLayer (𝒞 K) {h₀ * z * h₀⁻¹} ≤ G₀ := by
    rw [CM.layer_eq]
    exact sup_le hMG le_sup_right
  set 𝔖 : Set (Subgroup G) := {N | N ∈ 𝒞 K ∧ ∃ g ∈ G₀, N = conjSub g K ∨ N = conjSub g M} with h𝔖
  have hsub : 𝔖 ⊆ 𝒞 K := fun N hN => hN.1
  have hne : 𝔖.Nonempty := ⟨K, mem_conjClass_self K, 1, G₀.one_mem, Or.inl (conjSub_one K).symm⟩
  have hcl : ∀ N ∈ 𝔖, ∀ L' ∈ 𝒞 K, L' ≠ N → Commutes N L' → L' ∈ 𝔖 := by
    rintro N ⟨hNΩ, g, hg, hNg⟩ L' hL'Ω hne' hcomm
    have hnb : L' ∈ nbhd (𝒞 K) N := ⟨hL'Ω, hne', hcomm⟩
    rcases hNg with rfl | rfl
    ·
      have h1 : conjSub g⁻¹ L' ∈ nbhd (𝒞 K) K := by
        have := nbhd_conj C.inClass.conjInvariant g⁻¹ hnb
        rwa [conjSub_inv_conjSub] at this
      obtain ⟨y, hy, hyeq⟩ := C.nbhd_transitive hM h1
      refine ⟨hL'Ω, g * y, G₀.mul_mem hg (hYK hy), Or.inr ?_⟩
      rw [conjSub_mul, ← hyeq, conjSub_conjSub_inv]
    ·
      have h1 : conjSub g⁻¹ L' ∈ nbhd (𝒞 K) M := by
        have := nbhd_conj C.inClass.conjInvariant g⁻¹ hnb
        rwa [conjSub_inv_conjSub] at this
      have hKnb : K ∈ nbhd (𝒞 K) M := nbhd_symm C.mem hM
      obtain ⟨y, hy, hyeq⟩ := CM.nbhd_transitive hKnb h1
      refine ⟨hL'Ω, g * y, G₀.mul_mem hg (hYM hy), Or.inl ?_⟩
      rw [conjSub_mul, ← hyeq, conjSub_conjSub_inv]
  have hΩsub : 𝒞 K ⊆ 𝔖 := subset_of_adj_closed hconn hsub hne hcl
  intro N hN
  obtain ⟨-, g, hg, hNg⟩ := hΩsub hN
  have hconjle : ∀ {A : Subgroup G}, A ≤ G₀ → conjSub g A ≤ G₀ := by
    intro A hA x hx
    rw [mem_conjSub_iff] at hx
    have := hA hx
    have h2 := G₀.mul_mem (G₀.mul_mem hg this) (G₀.inv_mem hg)
    simpa [mul_assoc] using h2
  rcases hNg with rfl | rfl
  · exact hconjle hKG
  · exact hconjle hMG

end CFSG.ClassicalInvolution.NDB.G2S

module

public import CFSG.ClassicalInvolution.Q3.Closure
import CFSG.ClassicalInvolution.Uniform.U3M11
import CFSG.ClassicalInvolution.Q3.Q3YAbs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3KC

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.Assembly.LowTwoRank


section Model

variable {X : Type} [Group X]

theorem exists_conj_image_of_special {c : CompData} (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (hG : t = .G2 ∨ t = .trialityD4) (hadm : StatedLieAdmissible t n 3 1)
    (hc : c = CompData.model t n) {R R' : Subgroup c.G} (hR : R ∈ c.fund) (hR' : R' ∈ c.fund)
    {ζ ζ' : X} (hζ : ζ ∈ R.map ψ) (hζ' : ζ' ∈ R'.map ψ) (hζ2 : ζ * ζ = 1) (hζ'2 : ζ' * ζ' = 1)
    (hζ1 : ζ ≠ 1) (hζ'1 : ζ' ≠ 1) (hζc : ∀ y ∈ R.map ψ, ζ * y = y * ζ)
    (hζ'c : ∀ y ∈ R'.map ψ, ζ' * y = y * ζ') : ∃ g : c.G, ψ g * ζ * (ψ g)⁻¹ = ζ' := by
  subst hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj : Function.Injective ψ :=
    RouteD.G2D4.injective_of_ker_le_center (p := 3) (by norm_num) hG n le_rfl ψ hker
  obtain ⟨u, huR, hu⟩ := hζ
  obtain ⟨u', hu'R, hu'⟩ := hζ'
  have hu2 : u * u = 1 := hinj (by rw [map_mul, hu, map_one, hζ2])
  have hu'2 : u' * u' = 1 := hinj (by rw [map_mul, hu', map_one, hζ'2])
  have hu1 : u ≠ 1 := fun h => hζ1 (by rw [← hu, h, map_one])
  have hu'1 : u' ≠ 1 := fun h => hζ'1 (by rw [← hu', h, map_one])
  have huc : ∀ y ∈ R, u * y = y * u := fun y hy =>
    hinj (by rw [map_mul, map_mul, hu]; exact hζc _ (Subgroup.mem_map_of_mem ψ hy))
  have hu'c : ∀ y ∈ R', u' * y = y * u' := fun y hy =>
    hinj (by rw [map_mul, map_mul, hu']; exact hζ'c _ (Subgroup.mem_map_of_mem ψ hy))
  obtain ⟨g, hg⟩ := twoClassInvolutionsConj 3 t n 1 (by norm_num) hG hadm R hR R' hR' u huR u'
    hu'R hu2 hu'2 hu1 hu'1 huc hu'c
  exact ⟨g, by rw [← hu, ← hu', ← hg, map_mul, map_mul, map_inv]⟩

end Model

section Link

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem exists_conj_involution_of_fund3 (hΩ : InClass3 Ω) {ι : Type}
    (D : LieSystemData3 ι (LocalQuot Ω a) (localFamily Ω a)) {i : ι}
    {R R' : Subgroup (D.kind i).G} (hR : R ∈ (D.kind i).fund) (hR' : R' ∈ (D.kind i).fund)
    {M K : Subgroup G} (hM : M ∈ centralizingMembers Ω {a}) (hK : K ∈ centralizingMembers Ω {a})
    (hMR : modOddIn (centralizingLayer Ω {a}) M = R.map (D.hom i))
    (hKR' : modOddIn (centralizingLayer Ω {a}) K = R'.map (D.hom i)) {z z' : G}
    (hz : IsClassicalMember3 M z) (hz' : IsClassicalMember3 K z') :
    ∃ w ∈ centralizingLayer Ω {a}, z' * (w * z * w⁻¹) ∈ oddCoreIn (centralizingLayer Ω {a}) := by
  set Y := centralizingLayer Ω {a} with hY
  have hMY : M ≤ Y := le_centralizingLayer hM
  have hKY : K ≤ Y := le_centralizingLayer hK
  by_cases hspecial : ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ),
      StatedLieAdmissible t n 3 1 ∧ D.kind i = CompData.model t n ∧ (t = .G2 ∨ t = .trialityD4)
  · obtain ⟨t, n, hadm, hc, hG⟩ := hspecial
    set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
    set zY : ↥Y := ⟨z, hMY hz.mem⟩ with hzY
    set zY' : ↥Y := ⟨z', hKY hz'.mem⟩ with hzY'
    have hzz : zY * zY = 1 := Subtype.ext hz.isCentralInvolution.sq
    have hzz' : zY' * zY' = 1 := Subtype.ext hz'.isCentralInvolution.sq
    have hζ2 : π zY * π zY = 1 := by rw [← map_mul, hzz, map_one]
    have hζ'2 : π zY' * π zY' = 1 := by rw [← map_mul, hzz', map_one]
    have hζ1 : π zY ≠ 1 :=
      Q3Y.mk_ne_one_of_involution Y (hMY hz.mem) hz.isCentralInvolution.sq hz.ne_one
    have hζ'1 : π zY' ≠ 1 :=
      Q3Y.mk_ne_one_of_involution Y (hKY hz'.mem) hz'.isCentralInvolution.sq hz'.ne_one
    have hζmem : π zY ∈ R.map (D.hom i) := by
      rw [← hMR]
      exact ⟨zY, Subgroup.mem_subgroupOf.2 hz.mem, rfl⟩
    have hζ'mem : π zY' ∈ R'.map (D.hom i) := by
      rw [← hKR']
      exact ⟨zY', Subgroup.mem_subgroupOf.2 hz'.mem, rfl⟩
    have hcentral : ∀ {M₀ : Subgroup G} {w₀ : G} (hM₀ : M₀ ≤ Y) (hw₀ : IsClassicalMember3 M₀ w₀),
        ∀ y ∈ modOddIn Y M₀, π ⟨w₀, hM₀ hw₀.mem⟩ * y = y * π ⟨w₀, hM₀ hw₀.mem⟩ := by
      intro M₀ w₀ hM₀ hw₀ y hy
      obtain ⟨m, hm, rfl⟩ := hy
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (hw₀.isCentralInvolution.central m
        (Subgroup.mem_subgroupOf.mp hm)))
    obtain ⟨g, hg⟩ := exists_conj_image_of_special (D.hom i) (D.ker_le_center i) hG hadm hc hR hR'
      hζmem hζ'mem hζ2 hζ'2 hζ1 hζ'1
      (fun y hy => hcentral hMY hz y (by rw [hMR]; exact hy))
      (fun y hy => hcentral hKY hz' y (by rw [hKR']; exact hy))
    obtain ⟨wT, hwT⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥Y) (D.hom i g)
    have h5 : π (wT * zY * wT⁻¹) = π zY' := by
      rw [map_mul, map_mul, map_inv, hwT]
      exact hg
    have h6 : (wT * zY * wT⁻¹)⁻¹ * zY' ∈ classicalInvolutionOddCore ↥Y :=
      QuotientGroup.eq.mp h5
    have hU : ((wT : G) * z * (wT : G)⁻¹)⁻¹ * z' ∈ oddCoreIn Y := ⟨_, h6, rfl⟩
    refine ⟨(wT : G), wT.2, ?_⟩
    have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'.isCentralInvolution.sq
    have := (oddCoreIn Y).inv_mem hU
    rwa [mul_inv_rev, inv_inv, hz'inv] at this
  · have hSC : (D.kind i).SingleClass := by
      rcases D.valid i with ⟨t, n, hfund, hadm, hc⟩ | hc | hc
      · have ht : ¬ (t = .G2 ∨ t = .trialityD4) := fun h => hspecial ⟨t, n, hadm, hc, h⟩
        push Not at ht
        rw [hc]
        exact ModelFacts.fundamentalSingleClass t n 3 1 Nat.prime_three hfund hadm ht.1 ht.2
      · rw [hc]
        intro S₁ hS₁ S₂ hS₂
        rw [Set.mem_singleton_iff.mp hS₁, Set.mem_singleton_iff.mp hS₂]
        exact ⟨1, by simp⟩
      · rw [hc]
        exact Uniform.m11_singleClass
    obtain ⟨g, hg⟩ := hSC R hR R' hR'
    obtain ⟨w, hwY, hmod⟩ := exists_conj_modOddIn_of_fund3 D hMR hKR' g hg
    have hK'' : IsClassicalMember3 (conjSub w M) (w * z * w⁻¹) := hz.conj w
    have hwC : w ∈ Subgroup.centralizer ({a} : Set G) :=
      centralizingLayer_le_centralizer Ω {a} hwY
    have hK''Y : conjSub w M ≤ Y :=
      le_centralizingLayer (conjSub_mem_centralizingMembers hΩ.conjInvariant hwC hM)
    exact ⟨w, hwY, mul_mem_oddCoreIn_of_modOddIn_eq3 hz' hK'' hKY hK''Y hmod⟩

variable {A : Subgroup G} {S : Set (Subgroup G)}

theorem involutionLink_of_lieCovers3' (hΩ : InClass3 Ω) (hIH : LocalLieSystems3 Ω) {a : G}
    (hnc : a ∉ Subgroup.center G) (hS : S ⊆ Ω)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember3 K z) (hcov : LieCovers3 Ω S a) :
    InvolutionLink3 Ω A S a := by
  intro M hMmem z hz
  obtain ⟨ι, -, ⟨D⟩⟩ := hIH {a} (fun h => hnc (h rfl))
  set Y := centralizingLayer Ω {a} with hY
  have hMfam : modOddIn Y M ∈ localFamily Ω a :=
    ⟨M.subgroupOf Y, ⟨M, hMmem, le_centralizingLayer hMmem, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  obtain ⟨K', hK'S, hK'a, hK'i⟩ := hcov ι D i
  have hK'mem : K' ∈ centralizingMembers Ω {a} := ⟨hS hK'S, hK'a⟩
  have hK'fam : modOddIn Y K' ∈ localFamily Ω a :=
    ⟨K'.subgroupOf Y, ⟨K', hK'mem, le_centralizingLayer hK'mem, rfl⟩, rfl⟩
  obtain ⟨j, R', hR', hK'R'⟩ := D.fundamental _ hK'fam
  have hij : j = i := by
    by_contra hne
    refine not_le_center_of_mem3 hΩ hK'mem ?_
    have h1 : modOddIn Y K' ≤ (D.hom j).range := hK'R' ▸ Subgroup.map_le_range _ _
    exact (le_inf hK'i h1).trans (range_inf_range_le_center3 D (Ne.symm hne))
  subst hij
  obtain ⟨z', hz'A, hK'z'⟩ := hinv K' hK'S
  obtain ⟨w, hwY, hU⟩ := exists_conj_involution_of_fund3 hΩ D hR hR' hMmem hK'mem hMR hK'R' hz
    hK'z'
  have hK'' : IsClassicalMember3 (conjSub w M) (w * z * w⁻¹) := hz.conj w
  obtain ⟨o, ho, hoz⟩ := exists_conj_of_mul_mem hK''.isCentralInvolution.sq
    hK'z'.isCentralInvolution.sq (odd_card_oddCoreIn _) hU
  have hoY : o ∈ centralizingLayer Ω {a} := oddCoreIn_le _ ho
  refine ⟨K', hK'S, z', hz'A, hK'z', w⁻¹ * o⁻¹, mul_mem (inv_mem hwY) (inv_mem hoY), ?_⟩
  rw [hoz]
  group

end Link

end CFSG.ClassicalInvolution.Q3.Q3KC

module

public import CFSG.ClassicalInvolution.SmallCases.NDB2Vertex
public import CFSG.ClassicalInvolution.SmallCases.NDB5Model
public import CFSG.ClassicalInvolution.SmallCases.NDB5Res

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ComponentClassification
open CFSG.Assembly.LowTwoRank
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf finite_perfectResidualOf_isPerfect)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

structure VertexLayer (Ω : Set (Subgroup G)) (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ : G)
    (hN : NormalizesLayer (exactFamily Ω z₁) z₁) (D : LocalLieSystemAt p f (exactFamily Ω z₁) z₁)
    (i₀ i₁ : Fin D.card) (R₂ R₃ : Subgroup (compModel D i₁).K) (r₂ r₃ : (compModel D i₁).K)
    (ι : SL(2, GaloisField p (D.exp i₁)) →* (compModel D i₁).K) (L : Subgroup G) : Prop where
  card : D.card = 2
  ne : i₀ ≠ i₁
  tag : D.tag i₁ = .PSp
  rank : D.rank i₁ = 2
  range₀ : modOdd z₁ K₁ = (secComponentHom hN D i₀).range
  inj₁ : Function.Injective (secComponentHom hN D i₁)
  comm : ∀ a ∈ (secComponentHom hN D i₀).range, ∀ b ∈ (secComponentHom hN D i₁).range,
    a * b = b * a
  fund₂ : R₂ ∈ fundamentalSubgroups (D.tag i₁) (compModel D i₁).D
  fund₃ : R₃ ∈ fundamentalSubgroups (D.tag i₁) (compModel D i₁).D
  ne₂₃ : R₂ ≠ R₃
  img₂ : R₂.map (secComponentHom hN D i₁) = modOdd z₁ (exactCore z₁ K₂)
  img₃ : R₃.map (secComponentHom hN D i₁) = modOdd z₁ (exactCore z₁ K₃)
  mem₂ : r₂ ∈ R₂
  mem₃ : r₃ ∈ R₃
  cen₂ : ∀ r ∈ R₂, r₂ * r₂ * r = r * (r₂ * r₂)
  cen₃ : ∀ r ∈ R₃, r₃ * r₃ * r = r * (r₃ * r₃)
  same : r₂ * r₂ * (r₃ * r₃)⁻¹ ∈ Subgroup.center (compModel D i₁).K
  sq₂ : ∀ h, secComponentHom hN D i₁ (r₂ * r₂) = oddQuotMk z₁ ⟨z₂, h⟩
  sq₃ : ∀ h, secComponentHom hN D i₁ (r₃ * r₃) = oddQuotMk z₁ ⟨z₃, h⟩
  t₁_mem : ∀ h, oddQuotMk z₁ ⟨t₁, h⟩ ∈ (secComponentHom hN D i₀).range
  t₂_eq : ∀ h, secComponentHom hN D i₁ r₂ = oddQuotMk z₁ ⟨t₂, h⟩
  t₃_eq : ∀ h, secComponentHom hN D i₁ r₃ = oddQuotMk z₁ ⟨t₃, h⟩
  tau : ∀ h, oddQuotMk z₁ ⟨t₂ * t₃, h⟩ = secComponentHom hN D i₁ (r₂ * r₃)
  ι_inj : Function.Injective ι
  ι_range : perfectResidualOf (Subgroup.centralizer ({r₂ * r₃} : Set (compModel D i₁).K)) =
    ι.range
  ι_mem : r₂ * r₂ * (r₃ * r₃)⁻¹ ∈ ι.range
  le : L ≤ Subgroup.centralizer ({z₁} : Set G) ⊓
    Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G)
  perfect : Group.IsPerfect ↥L
  normal : ∀ g ∈ Subgroup.centralizer ({z₁} : Set G) ⊓
    Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G), conjSub g L = L
  mem : z₁ ∈ L
  sec : IsSectionMember p f (Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G)) L z₁
  img : modOdd z₁ L = ι.range.map (secComponentHom hN D i₁)
  img_tau : ∀ h, modOdd z₁ L = perfectResidualOf ((secComponentHom hN D i₁).range ⊓
    Subgroup.centralizer ({oddQuotMk z₁ ⟨t₂ * t₃, h⟩} : Set (OddQuot z₁)))

namespace Layer

theorem inf_centralizer_eq_map {M Q : Type*} [Group M] [Group Q] (ψ : M →* Q)
    (hψ : Function.Injective ψ) (a : Q) (ha : ∀ m, a * ψ m = ψ m * a) (u : M) :
    ψ.range ⊓ Subgroup.centralizer ({a * ψ u} : Set Q) =
      (Subgroup.centralizer ({u} : Set M)).map ψ := by
  ext y
  simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨m, rfl⟩, hm⟩
    refine ⟨m, hψ ?_, rfl⟩
    rw [map_mul, map_mul]
    have h1 : a * (ψ m * ψ u) = a * (ψ u * ψ m) := by
      calc a * (ψ m * ψ u) = ψ m * (a * ψ u) := by rw [← mul_assoc, ha, mul_assoc]
        _ = a * ψ u * ψ m := hm
        _ = a * (ψ u * ψ m) := mul_assoc _ _ _
    exact mul_left_cancel h1
  · rintro ⟨m, hm, rfl⟩
    refine ⟨⟨m, rfl⟩, ?_⟩
    calc ψ m * (a * ψ u) = a * (ψ m * ψ u) := by rw [← mul_assoc, ← ha, mul_assoc]
      _ = a * (ψ u * ψ m) := by rw [← map_mul, hm, map_mul]
      _ = a * ψ u * ψ m := (mul_assoc _ _ _).symm

theorem conj_range_eq {Ω : Set (Subgroup G)} {z : G} (Cx : XCtx p f Ω z)
    {i₀ i₁ : Fin Cx.D.card} (hcard : Cx.D.card = 2) (hne : i₀ ≠ i₁)
    (hK : modOdd z Cx.K = (Cx.psi i₀).range) {w : OddQuot z} (hw : w ∈ (Cx.psi i₁).range)
    (hw1 : w ≠ 1) (hw2 : w * w = 1) (hwz : w ≠ oddQuotMk z ⟨z, XCtx.hzC z⟩) (c : OddQuot z) :
    (Cx.psi i₁).range.map (MulAut.conj c).toMonoidHom = (Cx.psi i₁).range := by
  set S := (Cx.psi i₁).range with hS
  set S' := S.map (MulAut.conj c).toMonoidHom with hS'
  have hJ : (memberJoin (exactFamily Ω z) z).Normal :=
    memberJoin_normal_of_normalizes Cx.hs.normalizes
  have hcS' : CFSG.IsComponent S' :=
    (isComponent_map_equiv_iff (MulAut.conj c) S).mpr (Cx.isComponent_range i₁)
  have hwS' : c * w * c⁻¹ ∈ S' := ⟨w, hw, rfl⟩
  have hcw1 : c * w * c⁻¹ ≠ 1 := fun h => hw1 (by
    have := congrArg (fun x => c⁻¹ * x * c) h
    simpa [mul_assoc] using this)
  obtain ⟨D', hD'Q, -⟩ := Cx.hs.lieDecomposition_comp Cx.hp
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 Cx.hq Cx.D
  rcases D'.eq_or_commutes_of_isComponentOf ((CFSG.isComponent_iff_open S').mp hcS') with
    ⟨i, hi⟩ | hcomm
  · obtain ⟨j, hj⟩ := hD'Q i
    have hSj : S' = (Cx.psi j).range := hi.trans hj.symm
    rcases Seed.eq_or_eq_of_card_two hcard hne j with rfl | rfl
    · exfalso
      have hU := Cx.isUniqueInvolution_modOdd Cx.K_tq Cx.K_cl
      have hmem : c * w * c⁻¹ ∈ modOdd z (exactCore z Cx.K) := by
        rw [Cx.exactCore_K, hK, ← hSj]
        exact hwS'
      have hsq : c * w * c⁻¹ * (c * w * c⁻¹) = 1 := by
        calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
          _ = 1 := by rw [hw2]; group
      rcases hU.unique _ hmem hsq with h | h
      · exact hcw1 h
      · apply hwz
        have hc := oddQuotMk_central (XCtx.hzC z) c
        calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
          _ = c⁻¹ * oddQuotMk z ⟨z, XCtx.hzC z⟩ * c := by rw [h]
          _ = oddQuotMk z ⟨z, XCtx.hzC z⟩ := by
            rw [mul_assoc, hc, inv_mul_cancel_left]
    · exact hSj
  · exfalso
    have hle : S' ≤ memberJoin (exactFamily Ω z) z := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, rfl⟩ := hy
      exact hJ.conj_mem _ (Cx.psi_mem_memberJoin i₁ k) c
    have hperf : ⁅S', S'⁆ = S' := Subgroup.isPerfect_iff.mp hcS'.1.1
    have hab : ⁅S', S'⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x (hle hx)
    have h0 : c * w * c⁻¹ ∈ (⊥ : Subgroup (OddQuot z)) := by
      rw [← hab, hperf]
      exact hwS'
    exact hcw1 (Subgroup.mem_bot.mp h0)

end Layer

theorem exists_vertexLayer {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ t₁ t₂ t₃ : G} (hK₁ : K₁ ∈ Ω)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hsh : PSpShape p f Ω z₁) (hK₂ : K₂ ∈ tqMembers Ω z₁)
    (hz₂ : IsClassicalMember p f K₂ z₂) (hK₃ : K₃ ∈ tqMembers Ω z₁)
    (hz₃ : IsClassicalMember p f K₃ z₃) (hprod : z₁ * z₂ = z₃) (ht₁ : t₁ ∈ K₁)
    (ht₂ : t₂ ∈ K₂) (ht₃ : t₃ ∈ K₃) (hsq₁ : t₁ * t₁ = z₁) (hsq₂ : t₂ * t₂ = z₂)
    (hsq₃ : t₃ * t₃ = z₃) (c₁₂ : t₁ * t₂ = t₂ * t₁) (c₁₃ : t₁ * t₃ = t₃ * t₁)
    (hs2 : t₁ * t₂ * t₃ * (t₁ * t₂ * t₃) = 1) :
    ∃ (D : LocalLieSystemAt p f (exactFamily Ω z₁) z₁) (i₀ i₁ : Fin D.card)
      (R₂ R₃ : Subgroup (compModel D i₁).K) (r₂ r₃ : (compModel D i₁).K)
      (ι : SL(2, GaloisField p (D.exp i₁)) →* (compModel D i₁).K) (L : Subgroup G),
      VertexLayer Ω K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ (normalizesLayer_exactFamily hΩ.conjInvariant) D
        i₀ i₁ R₂ R₃ r₂ r₃ ι L := by
  classical
  have hz₁c := isCentralInvolution_of_isClassicalMember hz₁
  have hz₂c := isCentralInvolution_of_isClassicalMember hz₂
  have hz₃c := isCentralInvolution_of_isClassicalMember hz₃
  have hc2 := ExactLayer.isPGroup_zpowers_of_sq_eq_one hz₁c.sq
  have hzC : z₁ ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcomm₁ : ∀ {u : G}, t₁ * u = u * t₁ → u ∈ Subgroup.centralizer ({z₁} : Set G) :=
    fun h => Subgroup.mem_centralizer_singleton_iff.mpr
      (by rw [← hsq₁]; exact (Axis.comm_sq h).symm)
  have ht₁C : t₁ ∈ Subgroup.centralizer ({z₁} : Set G) := hcomm₁ rfl
  have ht₂C : t₂ ∈ Subgroup.centralizer ({z₁} : Set G) := hcomm₁ c₁₂
  have ht₃C : t₃ ∈ Subgroup.centralizer ({z₁} : Set G) := hcomm₁ c₁₃
  have hz₂C : z₂ ∈ Subgroup.centralizer ({z₁} : Set G) := by
    rw [← hsq₂]
    exact Subgroup.mul_mem _ ht₂C ht₂C
  have hz₃C : z₃ ∈ Subgroup.centralizer ({z₁} : Set G) := by
    rw [← hprod]
    exact Subgroup.mul_mem _ hzC hz₂C
  have hsC : t₁ * t₂ * t₃ ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ht₁C ht₂C) ht₃C
  have htsC : t₂ * t₃ ∈ Subgroup.centralizer ({z₁} : Set G) := Subgroup.mul_mem _ ht₂C ht₃C
  obtain ⟨D, i₀, i₁, hcard2, hne, htag₁, hrank₁, hKbar, hinj, hcomm01, hcomp⟩ :=
    exists_pspVertex hΩ hp hq hK₁ hz₁ hsh
  set ψ₀ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D i₀ with hψ₀
  set ψ₁ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D i₁ with hψ₁
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz₁
  let Cx : XCtx p f Ω z₁ :=
    { K := K₁, hK := hK₁, hKz := hKz, hΩ := hΩ, hp := hp, hq := hq, D := D }
  have hsq1 : ∀ {u : G} (hu : u ∈ Subgroup.centralizer ({z₁} : Set G)), u * u = 1 →
      oddQuotMk z₁ ⟨u, hu⟩ * oddQuotMk z₁ ⟨u, hu⟩ = 1 := fun hu h => by
    rw [← map_mul]
    exact (congrArg (oddQuotMk z₁) (Subtype.ext h : (⟨_, hu⟩ :
      ↥(Subgroup.centralizer ({z₁} : Set G))) * ⟨_, hu⟩ = 1)).trans (map_one _)
  have hz₁sq := hsq1 hzC hz₁c.sq
  have hz₂sq := hsq1 hz₂C hz₂c.sq
  have hz₃sq := hsq1 hz₃C hz₃c.sq
  have he₃ : (⟨z₃, hz₃C⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) = ⟨z₁, hzC⟩ * ⟨z₂, hz₂C⟩ :=
    Subtype.ext hprod.symm
  have hne1 : ∀ {u : G} (hu : u ∈ Subgroup.centralizer ({z₁} : Set G)), u * u = 1 → u ≠ 1 →
      oddQuotMk z₁ ⟨u, hu⟩ ≠ 1 := fun hu h h1 e =>
    h1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext h) e))
  have hz₂1 := hne1 hz₂C hz₂c.sq hz₂c.ne_one
  have hz₁1 := hne1 hzC hz₁c.sq hz₁c.ne_one
  have hz₃1 := hne1 hz₃C hz₃c.sq hz₃c.ne_one
  have hne₂ : oddQuotMk z₁ ⟨z₂, hz₂C⟩ ≠ oddQuotMk z₁ ⟨z₁, hzC⟩ := by
    intro h
    apply hz₃1
    rw [he₃, map_mul, h, hz₁sq]
  have hne₃ : oddQuotMk z₁ ⟨z₃, hz₃C⟩ ≠ oddQuotMk z₁ ⟨z₁, hzC⟩ := by
    intro h
    apply hz₂1
    have e : (⟨z₂, hz₂C⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) = ⟨z₁, hzC⟩ * ⟨z₃, hz₃C⟩ :=
      Subtype.ext (show z₂ = z₁ * z₃ by rw [← hprod, ← mul_assoc, hz₁c.sq, one_mul])
    rw [e, map_mul, h, hz₁sq]
  obtain ⟨R₂, hR₂, hR₂img⟩ := hcomp K₂ hK₂ z₂ hz₂ hz₂C hne₂
  obtain ⟨R₃, hR₃, hR₃img⟩ := hcomp K₃ hK₃ z₃ hz₃ hz₃C hne₃
  have h4 : ∀ {t z : G}, t * t = z → z * z = 1 → t ^ 4 = 1 := fun ht hz => by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, ht, hz]
  have ht₂E : t₂ ∈ exactCore z₁ K₂ := Vertex.mem_exactCore_of_isPGroup hΩ hp hq hc2 hK₂ ht₂
    (Subgroup.mem_centralizer_singleton_iff.mp ht₂C)
    (Vertex.isPGroup_zpowers_of_pow_four (h4 hsq₂ hz₂c.sq))
  have ht₃E : t₃ ∈ exactCore z₁ K₃ := Vertex.mem_exactCore_of_isPGroup hΩ hp hq hc2 hK₃ ht₃
    (Subgroup.mem_centralizer_singleton_iff.mp ht₃C)
    (Vertex.isPGroup_zpowers_of_pow_four (h4 hsq₃ hz₃c.sq))
  obtain ⟨r₂, hr₂R, hr₂⟩ : oddQuotMk z₁ ⟨t₂, ht₂C⟩ ∈ R₂.map ψ₁ := by
    rw [hR₂img]
    exact oddQuotMk_mem_modOdd ht₂E ht₂C
  obtain ⟨r₃, hr₃R, hr₃⟩ : oddQuotMk z₁ ⟨t₃, ht₃C⟩ ∈ R₃.map ψ₁ := by
    rw [hR₃img]
    exact oddQuotMk_mem_modOdd ht₃E ht₃C
  have hx₂ : ψ₁ (r₂ * r₂) = oddQuotMk z₁ ⟨z₂, hz₂C⟩ := by
    rw [map_mul, hr₂, ← map_mul]
    exact congrArg (oddQuotMk z₁) (Subtype.ext hsq₂)
  have hx₃ : ψ₁ (r₃ * r₃) = oddQuotMk z₁ ⟨z₃, hz₃C⟩ := by
    rw [map_mul, hr₃, ← map_mul]
    exact congrArg (oddQuotMk z₁) (Subtype.ext hsq₃)
  have hcentral : ∀ {w : OddQuot z₁}, (∀ y : OddQuot z₁, w * y = y * w) →
      ∀ {c : (compModel D i₁).K}, ψ₁ c = w → c ∈ Subgroup.center (compModel D i₁).K := by
    intro w hw c hc
    rw [Subgroup.mem_center_iff]
    intro g
    apply hinj
    rw [map_mul, map_mul, hc]
    exact (hw (ψ₁ g)).symm
  have hcentR : ∀ {N : Subgroup G} {u : G} (hu : IsClassicalMember p f N u)
      (huC : u ∈ Subgroup.centralizer ({z₁} : Set G)) {R : Subgroup (compModel D i₁).K},
      R.map ψ₁ = modOdd z₁ (exactCore z₁ N) → ∀ {x : (compModel D i₁).K},
      ψ₁ x = oddQuotMk z₁ ⟨u, huC⟩ → ∀ r ∈ R, x * r = r * x := by
    intro N u hu huC R hR x hx r hr
    apply hinj
    have hmem : ψ₁ r ∈ modOdd z₁ (exactCore z₁ N) := hR ▸ ⟨r, hr, rfl⟩
    obtain ⟨k, hk, hkr⟩ := hmem
    rw [map_mul, map_mul, hx, ← hkr, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk z₁) (Subtype.ext
      ((isCentralInvolution_of_isClassicalMember hu).central _ (exactCore_le_left z₁ N hk)))
  have hR₂₃ : R₂ ≠ R₃ := by
    intro h
    have hU := Cx.isUniqueInvolution_modOdd hK₂ hz₂
    have hz₃mem : oddQuotMk z₁ ⟨z₃, hz₃C⟩ ∈ modOdd z₁ (exactCore z₁ K₂) := by
      rw [← hR₂img, h, hR₃img]
      exact oddQuotMk_mem_modOdd (mem_exactCore hz₃ hc2 hK₃.2) hz₃C
    have h23 := (hU.unique _ hz₃mem hz₃sq).resolve_left hz₃1
    apply hz₁1
    have h1 : oddQuotMk z₁ ⟨z₁, hzC⟩ * oddQuotMk z₁ ⟨z₂, hz₂C⟩ = oddQuotMk z₁ ⟨z₂, hz₂C⟩ := by
      rw [← map_mul, ← he₃]
      exact h23
    calc oddQuotMk z₁ ⟨z₁, hzC⟩
        = oddQuotMk z₁ ⟨z₁, hzC⟩ * oddQuotMk z₁ ⟨z₂, hz₂C⟩ * (oddQuotMk z₁ ⟨z₂, hz₂C⟩)⁻¹ := by
          group
      _ = 1 := by rw [h1, mul_inv_cancel]
  have hsame : r₂ * r₂ * (r₃ * r₃)⁻¹ ∈ Subgroup.center (compModel D i₁).K := by
    refine hcentral (w := (oddQuotMk z₁ ⟨z₁, hzC⟩)⁻¹) (fun y => ?_) ?_
    · have := oddQuotMk_central hzC y
      calc (oddQuotMk z₁ ⟨z₁, hzC⟩)⁻¹ * y
          = (oddQuotMk z₁ ⟨z₁, hzC⟩)⁻¹ * (y * oddQuotMk z₁ ⟨z₁, hzC⟩) *
            (oddQuotMk z₁ ⟨z₁, hzC⟩)⁻¹ := by group
        _ = y * (oddQuotMk z₁ ⟨z₁, hzC⟩)⁻¹ := by rw [← this]; group
    · rw [map_mul, map_inv, hx₂, hx₃, he₃, map_mul]
      group
  have hcen1 : ∀ {a : (compModel D i₁).K}, a * a * (a * a)⁻¹ ∈
      Subgroup.center (compModel D i₁).K := fun {a} => by
    rw [mul_inv_cancel]
    exact Subgroup.one_mem _
  have hx1 : r₂ * r₂ ≠ 1 := fun h => hz₂1 (by rw [← hx₂, h, map_one])
  have hx'1 : r₃ * r₃ ≠ 1 := fun h => hz₃1 (by rw [← hx₃, h, map_one])
  have h4' : 4 ≤ p ^ D.exp i₁ := Cx.four_le i₁ (by rw [htag₁]; decide)
  have hexp : D.exp i₁ = f := Cx.exp_eq i₁ (by rw [htag₁]; decide)
  obtain ⟨ι, hιinj, hιres, hιmem⟩ := Model.exists_iota_model hp (D.tag i₁) (D.rank i₁)
    (D.exp i₁) htag₁ hrank₁ (D.admissible i₁) h4' hR₂ hR₃ hR₂₃ (R₂.mul_mem hr₂R hr₂R)
    (hcentR hz₂ hz₂C hR₂img hx₂) hx1 (R₃.mul_mem hr₃R hr₃R) (hcentR hz₃ hz₃C hR₃img hx₃) hx'1
    hsame hr₂R hr₃R hcen1 hcen1
  have ht₁ψ : oddQuotMk z₁ ⟨t₁, ht₁C⟩ ∈ ψ₀.range := by
    rw [← hKbar]
    exact oddQuotMk_mem_modOdd ht₁ ht₁C
  have hτ : ∀ h, oddQuotMk z₁ ⟨t₂ * t₃, h⟩ = ψ₁ (r₂ * r₃) := by
    intro h
    rw [map_mul, hr₂, hr₃, ← map_mul]
    rfl
  have hsbar : oddQuotMk z₁ ⟨t₁ * t₂ * t₃, hsC⟩ =
      oddQuotMk z₁ ⟨t₁, ht₁C⟩ * ψ₁ (r₂ * r₃) := by
    rw [← hτ htsC, ← map_mul]
    exact congrArg (oddQuotMk z₁) (Subtype.ext (mul_assoc t₁ t₂ t₃))
  have ht₁c : ∀ m, oddQuotMk z₁ ⟨t₁, ht₁C⟩ * ψ₁ m = ψ₁ m * oddQuotMk z₁ ⟨t₁, ht₁C⟩ :=
    fun m => hcomm01 _ ht₁ψ _ ⟨m, rfl⟩
  set X : Subgroup G := (ψ₁.range.comap (oddQuotMk z₁)).map
    (Subgroup.centralizer ({z₁} : Set G)).subtype with hX
  set W : Subgroup G := X ⊓ Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G) with hW
  have hWC : W ≤ Subgroup.centralizer ({z₁} : Set G) :=
    inf_le_left.trans (Subgroup.map_subtype_le _)
  have hLW : perfectResidualOf W ≤ W := Subgroup.map_subtype_le _
  have hWimg : modOdd z₁ W =
      (Subgroup.centralizer ({r₂ * r₃} : Set (compModel D i₁).K)).map ψ₁ := by
    rw [hW, hX, SRes.modOdd_comap_inf_centralizer ψ₁.range hsC hs2, hsbar]
    exact Layer.inf_centralizer_eq_map ψ₁ hinj _ ht₁c (r₂ * r₃)
  have : Finite (compModel D i₁).K := Finite.of_injective ψ₁ hinj
  have hLimg : modOdd z₁ (perfectResidualOf W) = ι.range.map ψ₁ := by
    rw [SRes.modOdd_perfectResidualOf hWC, hWimg, SRes.perfectResidualOf_map, hιres]
  have hz₁L : z₁ ∈ perfectResidualOf W := by
    obtain ⟨y, hy⟩ := hιmem
    have hmem : ψ₁ (ι y) ∈ modOdd z₁ (perfectResidualOf W) := by
      rw [hLimg]
      exact ⟨ι y, ⟨y, rfl⟩, rfl⟩
    obtain ⟨k, hkL, hk⟩ := hmem
    refine SRes.mem_of_oddQuotMk_eq hz₁c.sq hkL ?_
    rw [hk, hy, map_mul, map_inv, hx₂, hx₃, he₃, map_mul, mul_inv_rev, ← mul_assoc,
      mul_inv_cancel, one_mul]
    exact inv_eq_of_mul_eq_one_right hz₁sq
  have hSn : ∀ c : OddQuot z₁, ψ₁.range.map (MulAut.conj c).toMonoidHom = ψ₁.range :=
    Layer.conj_range_eq Cx hcard2 hne hKbar (w := oddQuotMk z₁ ⟨z₂, hz₂C⟩) ⟨r₂ * r₂, hx₂⟩
      hz₂1 hz₂sq hne₂
  have hXc : ∀ g ∈ Subgroup.centralizer ({z₁} : Set G), ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv,
      ← hSn (oddQuotMk z₁ ⟨g, hg⟩)]
    exact ⟨oddQuotMk z₁ y, hy, rfl⟩
  have hXn : Subgroup.centralizer ({z₁} : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨hXc g hg h, fun hh => ?_⟩
    have h2 := hXc g⁻¹ (Subgroup.inv_mem _ hg) _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at h2
  have hLn : ∀ g ∈ Subgroup.centralizer ({z₁} : Set G) ⊓
      Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G),
      conjSub g (perfectResidualOf W) = perfectResidualOf W := by
    intro g hg
    have hgs : g * (t₁ * t₂ * t₃) * g⁻¹ = t₁ * t₂ * t₃ := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hg.2, mul_inv_cancel_right]
    rw [← Balance.Bootstrap.perfectResidualOf_conjSub]
    congr 1
    rw [hW, Asc77.conjSub_inf, conjSub_eq_of_mem_normalizer (hXn hg.1),
      Balance.conjSub_centralizer_singleton, hgs]
  have hle : perfectResidualOf W ≤ Subgroup.centralizer ({z₁} : Set G) ⊓
      Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G) := hLW.trans (le_inf hWC inf_le_right)
  have hnorm : ((perfectResidualOf W).subgroupOf (Subgroup.centralizer ({z₁} : Set G) ⊓
      Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr fun g hg =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hLn g hg)
  have hO : CFSG.Open.classicalInvolutionOddCore SL(2, GaloisField p (D.exp i₁)) = ⊥ := by
    rw [hexp]
    exact SRes.oddCore_sl2_eq_bot hz₂
  have hequiv := SRes.nonempty_equiv_of_modOdd_eq (hLW.trans hWC) (ψ₁.comp ι)
    (hinj.comp hιinj) (by rw [hLimg, MonoidHom.range_comp]) hO
  rw [hexp] at hequiv
  have hsec : IsSectionMember p f (Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G))
      (perfectResidualOf W) z₁ :=
    { le := hle.trans inf_le_right
      orderOf_eq_two := hz₁.orderOf_eq_two
      mem := hz₁L
      perfect := finite_perfectResidualOf_isPerfect W
      subnormal := isSubnormal_of_normal_subgroupOf hle hnorm
      nonempty_equiv := hequiv }
  have himgτ : ∀ h, modOdd z₁ (perfectResidualOf W) = perfectResidualOf (ψ₁.range ⊓
      Subgroup.centralizer ({oddQuotMk z₁ ⟨t₂ * t₃, h⟩} : Set (OddQuot z₁))) := by
    intro h
    rw [hτ h, ← one_mul (ψ₁ (r₂ * r₃)),
      Layer.inf_centralizer_eq_map ψ₁ hinj 1 (fun m => by rw [one_mul, mul_one]) (r₂ * r₃),
      SRes.perfectResidualOf_map, hιres, hLimg]
  exact ⟨D, i₀, i₁, R₂, R₃, r₂, r₃, ι, perfectResidualOf W,
    { card := hcard2, ne := hne, tag := htag₁, rank := hrank₁, range₀ := hKbar, inj₁ := hinj,
      comm := hcomm01, fund₂ := hR₂, fund₃ := hR₃, ne₂₃ := hR₂₃, img₂ := hR₂img,
      img₃ := hR₃img, mem₂ := hr₂R, mem₃ := hr₃R, cen₂ := hcentR hz₂ hz₂C hR₂img hx₂,
      cen₃ := hcentR hz₃ hz₃C hR₃img hx₃, same := hsame, sq₂ := fun _ => hx₂,
      sq₃ := fun _ => hx₃, t₁_mem := fun _ => ht₁ψ, t₂_eq := fun _ => hr₂,
      t₃_eq := fun _ => hr₃, tau := hτ, ι_inj := hιinj, ι_range := hιres, ι_mem := hιmem,
      le := hle, perfect := finite_perfectResidualOf_isPerfect W, normal := hLn, mem := hz₁L,
      sec := hsec, img := hLimg, img_tau := himgτ }⟩

end CFSG.ClassicalInvolution.NDB

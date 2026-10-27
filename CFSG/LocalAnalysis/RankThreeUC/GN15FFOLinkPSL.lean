module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOLinkPSLAut
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
public import CFSG.RankThree.PartTwo.Sec16.Item166ResProofDeltaSz
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOCentral
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOFamilies
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOVacuity

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.SectionRank.EvenCover CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearCover
open CFSG.QuasithinUnique.K1 (stdAut descendAut_stdAut)
open scoped commutatorElement

section Cover

theorem even_linear_perfect_odd_cover_map_compat
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n) {L : Type*} [Group L]
    [Finite L] [Group.IsPerfect L] (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSL n K)) :
    ∃ φ : StatedSL n K →* L, Function.Surjective φ ∧
      φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) ∧
      ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)).map φ = Subgroup.center L ∧
      ∀ h, centralQuotientMap e (φ h) = (h : StatedProj (StatedSL n K)) := by
  obtain ⟨hsurj, hcen, hdvd⟩ := pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ, -⟩ := even_linear_central_odd_extension_splitting_stated hn hsurj hcen
    (Odd.of_dvd_nat hodd hdvd)
  exact CFSG.QuasithinUnique.Setup.X5.perfect_cover_map_of_section_compat e σ hσ

end Cover

section LLevel

@[expose] noncomputable def descL (L : Type) [Group L] : MulAut L →* MulAut (L ⧸ Subgroup.center L) where
  toFun α := QuotientGroup.congr _ _ α (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' α β := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

theorem descL_mk {L : Type} [Group L] (α : MulAut L) (x : L) :
    descL L α (QuotientGroup.mk x) = QuotientGroup.mk (α x) := rfl

variable {G : Type} [Group G]

@[expose] noncomputable def betaHom {L : Subgroup G} {P : Type} [Group P]
    (e' : ↥L ⧸ Subgroup.center ↥L ≃* P) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut P :=
  ((MulAut.congr e').toMonoidHom.comp (descL ↥L)).comp (Subgroup.normalizerMonoidHom L)

end LLevel
section Inner

variable {G : Type} [Group G] {L : Subgroup G} {P : Type} [Group P]
  (e' : ↥L ⧸ Subgroup.center ↥L ≃* P)

theorem betaHom_apply (g : ↥(Subgroup.normalizer (L : Set G))) (x : ↥L) :
    betaHom e' g (e' (QuotientGroup.mk x)) =
      e' (QuotientGroup.mk (Subgroup.normalizerMonoidHom L g x)) := by
  show (MulAut.congr e') (descL ↥L (Subgroup.normalizerMonoidHom L g)) (e' (QuotientGroup.mk x)) = _
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem betaHom_mem_inner_of_inner (g : ↥(Subgroup.normalizer (L : Set G)))
    (hg : Subgroup.normalizerMonoidHom L g ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L) :
    betaHom e' g ∈ (MulAut.conj : P →* MulAut P).range := by
  obtain ⟨ℓ, hℓ⟩ := hg
  refine ⟨e' (QuotientGroup.mk ℓ), ?_⟩
  ext p
  obtain ⟨q, rfl⟩ := e'.surjective p
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [betaHom_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← hℓ]
  rfl

theorem betaHom_mem_inner_of_mem (g : ↥(Subgroup.normalizer (L : Set G)))
    (hg : (g : G) ∈ L ⊔ Subgroup.centralizer (L : Set G)) :
    betaHom e' g ∈ (MulAut.conj : P →* MulAut P).range :=
  betaHom_mem_inner_of_inner e' g
    ((QuotientGroup.eq_one_iff _).1 (JOut.outerHom_eq_one_of_mem_sup_centralizer hg))

theorem mem_of_betaHom_mem_inner [Group.IsPerfect ↥L] (g : ↥(Subgroup.normalizer (L : Set G)))
    (h : betaHom e' g ∈ (MulAut.conj : P →* MulAut P).range) :
    (g : G) ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, rfl⟩ := e'.surjective p
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
  have hmk : ∀ x : ↥L, (QuotientGroup.mk (Subgroup.normalizerMonoidHom L g x) :
      ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk (ℓ * x * ℓ⁻¹) := by
    intro x
    have h1 := congrArg (fun f : MulAut P => f (e' (QuotientGroup.mk x))) hp
    simp only [MulAut.conj_apply, betaHom_apply] at h1
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact (e'.injective h1).symm
  have hz : ∀ x : ↥L, (ℓ * x * ℓ⁻¹)⁻¹ * Subgroup.normalizerMonoidHom L g x ∈
      Subgroup.center ↥L := fun x => QuotientGroup.eq.1 (hmk x).symm
  let t : ↥L →* Subgroup.center ↥L :=
    { toFun := fun x => ⟨(ℓ * x * ℓ⁻¹)⁻¹ * Subgroup.normalizerMonoidHom L g x, hz x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (hz x) (ℓ * y * ℓ⁻¹)⁻¹
        simp only [map_mul, Subgroup.coe_mul]
        calc (ℓ * (x * y) * ℓ⁻¹)⁻¹ * (Subgroup.normalizerMonoidHom L g x *
              Subgroup.normalizerMonoidHom L g y)
            = ((ℓ * y * ℓ⁻¹)⁻¹ * ((ℓ * x * ℓ⁻¹)⁻¹ * Subgroup.normalizerMonoidHom L g x)) *
              Subgroup.normalizerMonoidHom L g y := by group
          _ = (((ℓ * x * ℓ⁻¹)⁻¹ * Subgroup.normalizerMonoidHom L g x) * (ℓ * y * ℓ⁻¹)⁻¹) *
              Subgroup.normalizerMonoidHom L g y := by rw [hc]
          _ = ((ℓ * x * ℓ⁻¹)⁻¹ * Subgroup.normalizerMonoidHom L g x) *
              ((ℓ * y * ℓ⁻¹)⁻¹ * Subgroup.normalizerMonoidHom L g y) := by group }
  have hker : commutator ↥L ≤ t.ker := Abelianization.commutator_subset_ker t
  have htop : t.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := ↥L)]
    exact hker
  have hinner : Subgroup.normalizerMonoidHom L g ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
    refine ⟨ℓ, ?_⟩
    ext x
    have hx : t x = 1 := by
      have : x ∈ t.ker := htop ▸ Subgroup.mem_top x
      exact this
    have hx' := congrArg Subtype.val hx
    simp only [t, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] at hx'
    rw [MulAut.conj_apply]
    exact congrArg Subtype.val (inv_mul_eq_one.1 hx')
  exact JOut.mem_sup_centralizer_of_outerHom_eq_one ((QuotientGroup.eq_one_iff _).2 hinner)

end Inner
section Lift

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

theorem lift_apply (hS : Group.IsPerfect (SpecialLinearGroup (Fin n) K))
    (e' : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n K)
    (φ' : SpecialLinearGroup (Fin n) K →* ↥L)
    (hcomp : ∀ x, e' (QuotientGroup.mk (φ' x)) = proj n K x)
    (g : ↥(Subgroup.normalizer (L : Set G))) (Θ : MulAut (SpecialLinearGroup (Fin n) K))
    (hΘ : descendAut n K Θ = betaHom e' g) (x : SpecialLinearGroup (Fin n) K) :
    φ' (Θ x) = Subgroup.normalizerMonoidHom L g (φ' x) := by
  have hmk : ∀ x, (QuotientGroup.mk (φ' (Θ x)) : ↥L ⧸ Subgroup.center ↥L) =
      QuotientGroup.mk (Subgroup.normalizerMonoidHom L g (φ' x)) := by
    intro x
    apply e'.injective
    rw [hcomp, ← descendAut_proj, hΘ, ← hcomp, betaHom_apply]
  have hz : ∀ x, (φ' (Θ x))⁻¹ * Subgroup.normalizerMonoidHom L g (φ' x) ∈
      Subgroup.center ↥L := fun x => QuotientGroup.eq.1 (hmk x)
  let t : SpecialLinearGroup (Fin n) K →* Subgroup.center ↥L :=
    { toFun := fun x => ⟨(φ' (Θ x))⁻¹ * Subgroup.normalizerMonoidHom L g (φ' x), hz x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (hz x) (φ' (Θ y))⁻¹
        simp only [map_mul, Subgroup.coe_mul]
        calc (φ' (Θ x) * φ' (Θ y))⁻¹ * (Subgroup.normalizerMonoidHom L g (φ' x) *
              Subgroup.normalizerMonoidHom L g (φ' y))
            = (φ' (Θ y))⁻¹ * ((φ' (Θ x))⁻¹ * Subgroup.normalizerMonoidHom L g (φ' x)) *
              Subgroup.normalizerMonoidHom L g (φ' y) := by group
          _ = ((φ' (Θ x))⁻¹ * Subgroup.normalizerMonoidHom L g (φ' x)) * (φ' (Θ y))⁻¹ *
              Subgroup.normalizerMonoidHom L g (φ' y) := by rw [hc]
          _ = ((φ' (Θ x))⁻¹ * Subgroup.normalizerMonoidHom L g (φ' x)) *
              ((φ' (Θ y))⁻¹ * Subgroup.normalizerMonoidHom L g (φ' y)) := by group }
  have hker : commutator (SpecialLinearGroup (Fin n) K) ≤ t.ker :=
    Abelianization.commutator_subset_ker t
  have htop : t.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := SpecialLinearGroup (Fin n) K)]
    exact hker
  have hx : t x = 1 := by
    have : x ∈ t.ker := htop ▸ Subgroup.mem_top x
    exact this
  have hx' := congrArg Subtype.val hx
  simp only [t, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] at hx'
  exact inv_mul_eq_one.1 hx'

end Lift
section Assembly

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] {n : ℕ}

theorem exists_std_data (hn3 : 3 ≤ n) (hS : Group.IsPerfect (SpecialLinearGroup (Fin n) K))
    (e' : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n K)
    (φ' : SpecialLinearGroup (Fin n) K →* ↥L)
    (hcomp : ∀ x, e' (QuotientGroup.mk (φ' x)) = proj n K x)
    (g : ↥(Subgroup.normalizer (L : Set G))) :
    ∃ (B : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ) (e₀ : ℤ), ε ≤ 1 ∧
      betaHom e' g = conjAut n K B * fieldAut n K σ * dualAut n K ^ ε ∧
      (∀ x : Kˣ,
        (if ε = 0 then Units.map (σ : K →* K) x else (Units.map (σ : K →* K) x)⁻¹) = x ^ e₀) ∧
      ∀ (c : Kˣ) (hc : c ^ n = 1),
        (g : G) * ((φ' (scalarElement c hc) : ↥L) : G) * (g : G)⁻¹ =
          ((φ' (scalarElement c hc) : ↥L) : G) ^ e₀ := by
  obtain ⟨B, σ, ε, hε, hβ⟩ := (automorphism_generation (K := K) hn3).2 (betaHom e' g)
  obtain ⟨e₀, he₀⟩ := exists_exponent σ ε
  refine ⟨B, σ, ε, e₀, hε, hβ, he₀, fun c hc => ?_⟩
  have hΘ : descendAut n K (stdAut B σ ε) = betaHom e' g := by
    rw [descendAut_stdAut]; exact hβ.symm
  have h1 := lift_apply hS e' φ' hcomp g (stdAut B σ ε) hΘ (scalarElement c hc)
  rw [stdAut_scalarElement_exp B σ ε hε e₀ he₀, map_zpow] at h1
  have h2 := congrArg (fun x : ↥L => (x : G)) h1
  simp only [Subgroup.coe_zpow] at h2
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
  exact h2.symm

end Assembly
section Main

theorem linkPSL'_holds :
    ∀ (G : Type) [Group G] [Finite G], CFSG.pCore 2 G = ⊥ → ∀ (L : Subgroup G),
      CFSG.Open.IsComponentOf L ⊤ →
      ∀ a y : G, a ∈ Subgroup.normalizer (L : Set G) → y ∈ Subgroup.normalizer (L : Set G) →
        a * y * a⁻¹ = y⁻¹ → ∀ r e : ℕ, r.Prime → r ≠ 2 → orderOf y = r ^ e →
        y ^ r ∈ L ⊔ Subgroup.centralizer (L : Set G) → y ∉ L ⊔ Subgroup.centralizer (L : Set G) →
        FamPSL (↥L ⧸ Subgroup.center ↥L) r → r ∣ Nat.card (Subgroup.center ↥L) →
        ∃ z ∈ L, z ≠ 1 ∧ orderOf z = r ∧ (∀ l ∈ L, l * z = z * l) ∧ a * z * a⁻¹ = z⁻¹ ∧
          Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  intro G _ _ hO2 L hL a y haN hyN hinv r e hr hr2 hord hyr hyX hF hrZ
  have hLc : CFSG.IsComponent L := (CFSG.isComponent_iff_open L).mpr hL
  have hLq : CFSG.IsQuasisimple ↥L := hLc.1
  have : Group.IsPerfect ↥L := hLq.1
  have hpL : CFSG.pCore 2 ↥L = ⊥ := by
    have h := CFSG.RankThree.PartTwo.Sec16.ProofDeltaSz166.map_pCore_le_pCore_of_isSubnormal
      (p := 2) hLc.2
    rw [hO2] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 (le_bot_iff.1 h)
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.odd_card_center_of_pCore_eq_bot hpL
  obtain ⟨n, f, hm, hdvd⟩ := hF
  obtain ⟨⟨-, -, hn2, -, -⟩, K, _, _, hK, ⟨e0⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have : Fact r.Prime := ⟨hr⟩
  have hn3 : 3 ≤ n := by
    have hrn : r ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
    have hn0 : 0 < n := by omega
    have := Nat.le_of_dvd hn0 hrn
    have := hr.two_le
    omega
  have hS : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl hn3)
  obtain ⟨φ, hφs, hker, hD, hcompat⟩ := even_linear_perfect_odd_cover_map_compat hn2 hodd e0
  let ε := specialLinearGroupEquivStatedSL n K
  let φ' : Matrix.SpecialLinearGroup (Fin n) K →* ↥L := φ.comp ε.toMonoidHom
  let e' : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n K :=
    (e0.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (projectiveSpecialLinearEquivProjectiveSL n K)
  have hcomp : ∀ x, e' (QuotientGroup.mk (φ' x)) = proj n K x := by
    intro x
    have h1 : e0 (QuotientGroup.mk (φ (ε x))) =
        (QuotientGroup.mk (ε x) : StatedProj (StatedSL n K)) := hcompat (ε x)
    have h2 : (projectiveSpecialLinearGroupEquivStatedProj n K).symm
        (QuotientGroup.mk (ε x) : StatedProj (StatedSL n K)) = QuotientGroup.mk x :=
      (MulEquiv.symm_apply_eq _).2 rfl
    change (projectiveSpecialLinearEquivProjectiveSL n K)
      ((projectiveSpecialLinearGroupEquivStatedProj n K).symm
        (e0 (QuotientGroup.mk (φ (ε x))))) = _
    rw [h1, h2]
    rfl
  let ga : ↥(Subgroup.normalizer (L : Set G)) := ⟨a, haN⟩
  let gy : ↥(Subgroup.normalizer (L : Set G)) := ⟨y, hyN⟩
  have hinv' : ga * gy * ga⁻¹ = gy⁻¹ := Subtype.ext hinv
  have hβinv : betaHom e' ga * betaHom e' gy * (betaHom e' ga)⁻¹ = (betaHom e' gy)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hinv', map_inv]
  have hβpow : (betaHom e' gy) ^ r ∈
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
    rw [← map_pow]
    exact betaHom_mem_inner_of_mem e' _ hyr
  have hβne : betaHom e' gy ∉
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := fun h =>
    hyX (mem_of_betaHom_mem_inner e' gy h)
  obtain ⟨B, σ, ε', e₀, hε, hβa, he₀, hexp⟩ := exists_std_data hn3 hS e' φ' hcomp ga
  have hdvd1 : (r : ℤ) ∣ e₀ + 1 :=
    prime_dvd_exponent_add_one hn3 hr hr2 hβinv hβpow hβne B σ ε' hε hβa e₀ he₀
  obtain ⟨zc, hzc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥L) r hrZ
  have hz_in : (zc : ↥L) ∈
      ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)).map φ := by
    rw [hD]; exact zc.2
  obtain ⟨d, hd, hdφ⟩ := hz_in
  rw [← map_center_eq_statedScalars n K] at hd
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hd
  rw [← scalars_eq_center] at hs
  obtain ⟨c, hc, hsc⟩ := hs
  have hsE : s = scalarElement c hc := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hsc, coe_scalarElement]
  have hφs : φ' (scalarElement c hc) = (zc : ↥L) := by
    rw [← hsE]; exact hdφ
  have hzord : orderOf (((zc : ↥L)) : G) = r := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hzc]
  have hconj : ∀ b ∈ Subgroup.normalizer (L : Set G), ∃ k : ℤ,
      b * ((zc : ↥L) : G) * b⁻¹ = ((zc : ↥L) : G) ^ k := by
    intro b hb
    obtain ⟨B', σ', ε'', e₁, -, -, -, hexp'⟩ := exists_std_data hn3 hS e' φ' hcomp ⟨b, hb⟩
    refine ⟨e₁, ?_⟩
    have h1 := hexp' c hc
    rw [hφs] at h1
    exact h1
  have hconj' : ∀ b ∈ Subgroup.normalizer (L : Set G), ∀ h ∈ Subgroup.zpowers ((zc : ↥L) : G),
      b * h * b⁻¹ ∈ Subgroup.zpowers ((zc : ↥L) : G) := by
    intro b hb h hh
    obtain ⟨k, hk⟩ := hconj b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have : b * ((zc : ↥L) : G) ^ m * b⁻¹ = (((zc : ↥L) : G) ^ k) ^ m := by
      rw [← hk, ← conj_zpow]
    rw [this, ← _root_.zpow_mul]
    exact Subgroup.zpow_mem_zpowers _ _
  refine ⟨((zc : ↥L) : G), (zc : ↥L).2, ?_, hzord, ?_, ?_, ?_⟩
  · intro h1
    have h2 : (zc : ↥L) = 1 := Subtype.ext h1
    have h3 : zc = 1 := Subtype.ext h2
    rw [h3, orderOf_one] at hzc
    exact hr.one_lt.ne hzc
  · intro l hl
    have := Subgroup.mem_center_iff.1 zc.2 ⟨l, hl⟩
    exact congrArg Subtype.val this
  · have h1 := hexp c hc
    rw [hφs] at h1
    have h2 : ((zc : ↥L) : G) ^ (e₀ + 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hzord]
      exact hdvd1
    rw [h1]
    rw [_root_.zpow_add_one] at h2
    exact eq_inv_of_mul_eq_one_left h2
  · intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj' b hb h hh, fun hh => ?_⟩
    have hb' : b⁻¹ ∈ Subgroup.normalizer (L : Set G) := (Subgroup.normalizer (L : Set G)).inv_mem hb
    have h1 := hconj' b⁻¹ hb' _ hh
    have e : b⁻¹ * (b * h * b⁻¹) * (b⁻¹)⁻¹ = h := by group
    rwa [e] at h1

theorem invertsOddOn_psl_of_noOffender
    (hvac : PSLNoOffender) : InvertsOddOn FamPSL := by
  intro G _ _ W _ _ _ ρ hρ hK hO2 A hAel hAb L hL hAN hLA a ha haK y hy hinv r e hr hr2 hord hyr
    hnn hF
  by_contra hyX
  obtain ⟨n, f, hm, hdvd⟩ := id hF
  have hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hLbot : L ≠ ⊥ := by
    rintro rfl
    have hs : IsSimpleGroup (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) := hL.2.2.2
    have := hs.toNontrivial
    have : Subsingleton ↥(⊥ : Subgroup G) := inferInstance
    have : Subsingleton (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) := inferInstance
    exact not_subsingleton _ ‹_›
  by_cases hrZ : r ∣ Nat.card (Subgroup.center ↥L)
  · obtain ⟨z, hzL, hz1, hzord, hzc, hzinv, hzN⟩ :=
      linkPSL'_holds G hO2 L hL a y (hAN ha) hy hinv r e hr hr2 hord hyr hyX hF hrZ
    exact false_of_inverts_central hρ hAel hAb hz1
      (by rw [hzord]; exact hr.odd_of_ne_two hr2) ha hzinv (fun b hb => hzN (hAN hb)) hperf hzL hzc
  · have hbot : ⁅L, A⁆ = ⊥ := by
      have hn2 : 2 ≤ n := hm.1.2.2.1
      have hf1 : 1 ≤ f := hm.1.2.1
      by_cases hn3 : n = 3
      · subst hn3
        have h3r : r = 3 :=
          (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hdvd.trans (Nat.gcd_dvd_left _ _))
        subst h3r
        have h3 : 3 ∣ 2 ^ f - 1 := hdvd.trans (Nat.gcd_dvd_right _ _)
        have hf2 : 2 ≤ f := by
          by_contra hlt
          have : f = 1 := by omega
          subst this
          norm_num at h3
        exact commutator_eq_bot_of_psl_three G W ρ hρ hO2 A hAel hAb L hL hrZ hf2 h3 hm
      · have hn4 : 4 ≤ n := by
          have hn2' : n ≠ 2 := by
            rintro rfl
            have h2 : r ∣ 2 := hdvd.trans (Nat.gcd_dvd_left _ _)
            exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
          omega
        exact commutator_eq_bot_of_psl_noOffenderAt (hvac n f r hn4 hr hr2 hdvd) G W ρ hρ hO2 A hAel
          hAb L hL hrZ hm
    rw [hLA] at hbot
    exact hLbot hbot

theorem ffOffenderInvertsOddPSL_of_noOffender
    (hvac : PSLNoOffender) : FFOffenderInvertsOddPSL :=
  invertsOddOn_psl_of_noOffender hvac

end Main
end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO

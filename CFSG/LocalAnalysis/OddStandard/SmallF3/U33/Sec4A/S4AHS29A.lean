module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutHS29
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR8C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

namespace S4A

section Transport

variable {G : Type} [Group G]

theorem nonempty_fixSub_equiv (R : Subgroup G) {a : G} (ha : a ∈ normalizer (R : Set G)) :
    Nonempty (↥(Outside.fixSub (R.normalizerMonoidHom ⟨a, ha⟩)) ≃*
      ↥(R ⊓ centralizer ({a} : Set G))) := by
  have hmap : (Outside.fixSub (R.normalizerMonoidHom ⟨a, ha⟩)).map R.subtype =
      R ⊓ centralizer ({a} : Set G) := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : a * (u : G) * a⁻¹ = (u : G) :=
        congrArg Subtype.val (show R.normalizerMonoidHom ⟨a, ha⟩ u = u from hu)
      refine Subgroup.mem_inf.mpr ⟨u.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (u : G) * a = (a * (u : G) * a⁻¹) * a := by rw [hu']
        _ = a * (u : G) := by group
    · rintro ⟨hgR, hgC⟩
      have hgc : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
      refine ⟨⟨g, hgR⟩, ?_, rfl⟩
      refine Subtype.ext ?_
      show a * g * a⁻¹ = g
      calc a * g * a⁻¹ = (g * a) * a⁻¹ := by rw [hgc]
        _ = g := by group
  exact ⟨(Subgroup.equivMapOfInjective _ R.subtype R.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

theorem hs29_transport [Finite G] {R : Subgroup G} (hcard : Nat.card R = 64)
    (hnab : ¬ IsMulCommutative R) {ρ a : G} (hρ : ρ ∈ normalizer (R : Set G))
    (ha : a ∈ normalizer (R : Set G)) (hρ3 : ρ ^ 3 = 1) (ha2 : a * a = 1)
    (hconj : a * ρ * a⁻¹ = ρ⁻¹) (hfpf : R ⊓ centralizer ({ρ} : Set G) = ⊥) :
    Nonempty (↥R ≃* SylSL3_4) ∧
      (Nonempty (↥(R ⊓ centralizer ({a} : Set G)) ≃* DihedralGroup 4) ∨
        Nonempty (↥(R ⊓ centralizer ({a} : Set G)) ≃* QuaternionGroup 2)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set rT : MulAut R := R.normalizerMonoidHom ⟨ρ, hρ⟩ with hrT
  set aT : MulAut R := R.normalizerMonoidHom ⟨a, ha⟩ with haT
  have hrT_apply : ∀ r : R, ((rT r : R) : G) = ρ * (r : G) * ρ⁻¹ := fun r => rfl
  have hfpf' : ∀ g : R, rT g = g → g = 1 := by
    intro g hg
    have h1 : ρ * (g : G) * ρ⁻¹ = (g : G) := by
      rw [← hrT_apply, hg]
    have h2 : (g : G) ∈ R ⊓ centralizer ({ρ} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨g.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g : G) * ρ = (ρ * (g : G) * ρ⁻¹) * ρ := by rw [h1]
        _ = ρ * (g : G) := by group
    rw [hfpf, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hrT3 : rT ^ 3 = 1 := by
    rw [hrT, ← map_pow]
    have : (⟨ρ, hρ⟩ : normalizer (R : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hρ3)
    rw [this, map_one]
  have hrT1 : rT ≠ 1 := by
    intro h1
    have hsub : Subsingleton R := ⟨fun x y => by
      have hx := hfpf' x (by rw [h1]; rfl)
      have hy := hfpf' y (by rw [h1]; rfl)
      rw [hx, hy]⟩
    have := Nat.card_of_subsingleton (1 : R)
    omega
  have haT2 : aT ^ 2 = 1 := by
    rw [haT, ← map_pow]
    have : (⟨a, ha⟩ : normalizer (R : Set G)) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using ha2)
    rw [this, map_one]
  have hconjT : aT * rT * aT⁻¹ = rT⁻¹ := by
    rw [haT, hrT, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hconj)
  have haT1 : aT ≠ 1 := by
    intro h1
    rw [h1, one_mul, inv_one, mul_one] at hconjT
    have h2 : rT * rT = 1 := by
      calc rT * rT = rT * rT⁻¹ := congrArg (rT * ·) hconjT
        _ = 1 := mul_inv_cancel rT
    have h3 : rT * rT * rT = 1 := by
      have := hrT3
      rwa [pow_succ, pow_two] at this
    apply hrT1
    calc rT = (rT * rT * rT) * (rT * rT)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  have hs : Outside.Sigma3Rel rT aT :=
    ⟨orderOf_eq_prime hrT3 hrT1, orderOf_eq_prime haT2 haT1, hconjT⟩
  have hnab' : ∃ x y : ↥R, x * y ≠ y * x := by
    by_contra hcon
    refine hnab (isMulCommutative_iff.mpr fun x y => ?_)
    by_contra hne
    exact hcon ⟨x, y, hne⟩
  obtain ⟨hiso, hfix⟩ := Outside.HS29 hcard hnab' hs hfpf'
  obtain ⟨e⟩ := nonempty_fixSub_equiv R ha
  refine ⟨hiso, ?_⟩
  rcases hfix with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr ⟨e.symm.trans f⟩

end Transport

section Step9

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem n4_mem_normalizer_R (h : L41GPh8 t L S x₁ x₂ lam rho) :
    rho ∈ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) ∧
      lam ∈ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) ∧
      t ∈ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) := by
  have hN := h.rfacts.normal_R
  have hρN : rho ∈ l41N t x₁ x₂ := n4_rho_mem_N h.toL41GPh1
  have hlamN : lam ∈ l41N t x₁ x₂ :=
    n4_K_le_N h.toL41GPh1 (Subgroup.subset_closure (by simp))
  have htN : t ∈ l41N t x₁ x₂ := pCoreOf_two_le _ (n4_t_mem_O h.toL41GPh3)
  exact ⟨mem_normalizer_of_conj_mem fun r hr => hN.2 rho hρN r hr,
    mem_normalizer_of_conj_mem fun r hr => hN.2 lam hlamN r hr,
    mem_normalizer_of_conj_mem fun r hr => hN.2 t htN r hr⟩

theorem l41_hs29_of (h : L41GPh8 t L S x₁ x₂ lam rho) : L41HS29Fact t x₁ x₂ lam rho := by
  classical
  by_cases hab : IsMulCommutative ↥(l41R t x₁ x₂ rho)
  · exact Or.inl hab
  · right
    obtain ⟨hρN, hlamN, htN⟩ := n4_mem_normalizer_R h
    have hcard : Nat.card ↥(l41R t x₁ x₂ rho) = 64 := h.rfacts.card_R.trans (by norm_num)
    have hρ3 : rho ^ 3 = 1 := n4_rho_cube h.toCtx0
    have hlam2 : lam * lam = 1 := n4_lam_sq h.toCtx0
    have hρL : rho ∈ L := h.rho_mem
    have hlamL : lam ∈ L := (generators_mem_L h.toCtx0).2.2
    have htc : ∀ g ∈ L, t * g = g * t := fun g hg =>
      n4_zpowers_t_comm h.toL41GPh5 (Subgroup.mem_zpowers t) hg
    have hlamt2 : lam * t * (lam * t) = 1 := by
      calc lam * t * (lam * t) = lam * (t * lam) * t := by group
        _ = lam * (lam * t) * t := by rw [htc lam hlamL]
        _ = (lam * lam) * (t * t) := by group
        _ = 1 := by rw [hlam2, t_mul_self h.hyp, one_mul]
    have hconj2 : lam * t * rho * (lam * t)⁻¹ = rho⁻¹ := by
      calc lam * t * rho * (lam * t)⁻¹ = lam * (t * rho * t⁻¹) * lam⁻¹ := by group
        _ = lam * rho * lam⁻¹ := by rw [n4_conj_eq_of_comm (htc rho hρL).symm]
        _ = rho⁻¹ := h.lam_rho
    obtain ⟨hiso, hfix1⟩ := hs29_transport hcard hab hρN hlamN hρ3 hlam2 h.lam_rho
      h.rfacts.cent_rho
    obtain ⟨-, hfix2⟩ := hs29_transport hcard hab hρN (Subgroup.mul_mem _ hlamN htN) hρ3 hlamt2
      hconj2 h.rfacts.cent_rho
    exact ⟨hiso, hfix1, hfix2⟩

end Step9

end S4A

theorem l41_hs29_holds : L41HS29Stmt :=
  fun h => S4A.l41_hs29_of h.toG

end CFSG.OddStandard.SmallF3.HarrisU33

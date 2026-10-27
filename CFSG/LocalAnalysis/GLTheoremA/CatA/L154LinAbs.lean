module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

theorem l154_exists_hom_lift {G H R Q : Type*} [Group G] [Group H] [Group R] [Group Q]
    (ρ : G →* Q) (Ψ : H →* Q) (q : H →* R) (hρΨ : ∀ g, ∃ h, Ψ h = ρ g)
    (hker : ∀ h, Ψ h = 1 → q h = 1) :
    ∃ Θ : G →* R, ∀ g h, Ψ h = ρ g → Θ g = q h := by
  choose m hm using hρΨ
  have key : ∀ g h, Ψ h = ρ g → q h = q (m g) := by
    intro g h hh
    have h1 : Ψ ((m g)⁻¹ * h) = 1 := by rw [map_mul, map_inv, hm g, hh, inv_mul_cancel]
    have h2 := hker _ h1
    rw [map_mul, map_inv] at h2
    exact (inv_mul_eq_one.1 h2).symm
  refine ⟨{ toFun := fun g => q (m g)
            map_one' := ?_
            map_mul' := ?_ }, fun g h hh => (key g h hh).symm⟩
  · show q (m 1) = 1
    have h1 : Ψ (m 1) = ρ 1 := hm 1
    rw [map_one] at h1
    exact hker _ h1
  · intro g g'
    show q (m (g * g')) = q (m g) * q (m g')
    rw [← map_mul]
    exact (key (g * g') (m g * m g') (by rw [map_mul, hm g, hm g', map_mul])).symm

theorem l154_centralizer_inv_singleton {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x = x * (x⁻¹ * g) * x := by group
      _ = x * (g * x⁻¹) * x := by rw [h]
      _ = x * g := by group
  · intro h
    calc g * x⁻¹ = x⁻¹ * (x * g) * x⁻¹ := by group
      _ = x⁻¹ * (g * x) * x⁻¹ := by rw [h]
      _ = x⁻¹ * g := by group

theorem l154_isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} {g : G} (h : g ^ p = 1) :
    IsPGroup p (Subgroup.zpowers g) := by
  rintro ⟨a, ha⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem l154_indAut_pow_eq_one {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hgp : g ^ p = 1) :
    MI.indAut p L g hg ^ p = 1 := by
  have e : (⟨g⁻¹, Subgroup.inv_mem _ hg⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 :=
    Subtype.ext (by simp [inv_pow, hgp])
  show chevAut p L ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ ^ p = 1
  rw [← map_pow, e, map_one]

theorem l154_exists_pSimple_equiv {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) {R : Type} [Group R] (hR : IsSimpleGroup R) (Θ : ↥J →* R)
    (hsurj : Function.Surjective Θ) (hker : Θ.ker ≤ Subgroup.center ↥J) :
    ∃ e : PSimple p J ≃* R, ∀ l : ↥J, e (QuotientGroup.mk (QuotientGroup.mk l)) = Θ l := by
  haveI := hR
  obtain ⟨hs, hna⟩ := chev_pSimple_simple_nonabelian hp hJ
  let π₁ : ↥J →* PSimple p J :=
    (QuotientGroup.mk' (Subgroup.center (PQuot p J))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥J))
  have hπ₁ : ∀ l : ↥J, π₁ l = QuotientGroup.mk (QuotientGroup.mk l) := fun l => rfl
  have hπ₁surj : Function.Surjective π₁ := by
    intro z
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective a
    exact ⟨l, rfl⟩
  have hker' : Θ.ker ≤ π₁.ker := by
    intro l hl
    have hlc : l ∈ Subgroup.center ↥J := hker hl
    rw [MonoidHom.mem_ker, hπ₁, QuotientGroup.eq_one_iff]
    refine Subgroup.mem_center_iff.2 fun b => ?_
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.1 hlc c)]
  let e₀ : R →* PSimple p J := MonoidHom.liftOfSurjective Θ hsurj ⟨π₁, hker'⟩
  have he₀ : ∀ l : ↥J, e₀ (Θ l) = π₁ l := fun l => MonoidHom.liftOfRightInverse_comp_apply Θ _ _ ⟨π₁, hker'⟩ l
  have hsurj₀ : Function.Surjective e₀ := by
    intro z
    obtain ⟨l, rfl⟩ := hπ₁surj z
    exact ⟨Θ l, he₀ l⟩
  have hinj₀ : Function.Injective e₀ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal e₀.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      obtain ⟨a', rfl⟩ := hsurj₀ a
      obtain ⟨b', rfl⟩ := hsurj₀ b
      have h1 : e₀ a' = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
      have h2 : e₀ b' = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
      rw [h1, h2]
  refine ⟨(MulEquiv.ofBijective e₀ ⟨hinj₀, hsurj₀⟩).symm, fun l => ?_⟩
  rw [MulEquiv.symm_apply_eq]
  exact (he₀ l).symm

end CFSG.LocalAnalysis.GLTheoremA.K155X

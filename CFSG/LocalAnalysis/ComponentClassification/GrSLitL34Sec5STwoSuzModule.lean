module

public import CFSG.LocalAnalysis.ComponentClassification.Walter86.ModuleReduction54
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TLayer
import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofLinAlg
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

section

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem rho_commutator_eq_one_iff {X M : Type*} [Group X] [Monoid M] (ρ : X →* M) (a b : X) :
    ρ ⁅a, b⁆ = 1 ↔ ρ a * ρ b = ρ b * ρ a := by
  have h : ρ.toHomUnits ⁅a, b⁆ = 1 ↔
      ρ.toHomUnits a * ρ.toHomUnits b = ρ.toHomUnits b * ρ.toHomUnits a := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  constructor
  · intro hρ
    exact congrArg Units.val (h.mp (Units.ext hρ))
  · intro hρ
    exact congrArg Units.val (h.mpr (Units.ext hρ))

private theorem two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp)

theorem rho_eq_one_or_neg_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {X V : Type*} [Group X]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (ρ : Representation (ZMod p) X V)
    (hirr : ρ.IsIrreducible) {z : X} (hz : z * z = 1) (hc : ∀ g, ρ z * ρ g = ρ g * ρ z) :
    ρ z = 1 ∨ ∀ v, ρ z v = -v := by
  have h2ne := two_ne_zero_zmod hp
  have hzz : ∀ v, ρ z (ρ z v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, hz, map_one, Module.End.one_apply]
  have hcg : ∀ g v, ρ z (ρ g v) = ρ g (ρ z v) := fun g v => by
    rw [← Module.End.mul_apply, hc g, Module.End.mul_apply]
  have := hirr
  obtain ⟨Sp, hmSp⟩ : ∃ S : Subrepresentation ρ, ∀ v, v ∈ S.toSubmodule ↔ ρ z v = v :=
    ⟨⟨LinearMap.eqLocus (ρ z) LinearMap.id, fun g v hv => by
        have hv' : ρ z v = v := hv
        show ρ z (ρ g v) = ρ g v
        rw [hcg, hv']⟩, fun v => Iff.rfl⟩
  obtain ⟨Sm, hmSm⟩ : ∃ S : Subrepresentation ρ, ∀ v, v ∈ S.toSubmodule ↔ ρ z v = -v :=
    ⟨⟨LinearMap.eqLocus (ρ z) (-LinearMap.id), fun g v hv => by
        have hv' : ρ z v = -v := hv
        show ρ z (ρ g v) = -ρ g v
        rw [hcg, hv', map_neg]⟩, fun v => Iff.rfl⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top Sp with hbp | hbp
  · rcases IsSimpleOrder.eq_bot_or_eq_top Sm with hbm | hbm
    · exfalso
      have hz0 : ∀ v : V, v = 0 := by
        intro v
        have e1 : v + ρ z v = 0 := by
          have hmem : (v + ρ z v) ∈ Sp.toSubmodule :=
            (hmSp _).mpr (by rw [map_add, hzz, add_comm (ρ z v) v])
          rw [hbp] at hmem
          exact (Submodule.mem_bot _).mp hmem
        have e2 : v - ρ z v = 0 := by
          have hmem : (v - ρ z v) ∈ Sm.toSubmodule :=
            (hmSm _).mpr (by rw [map_sub, hzz, neg_sub])
          rw [hbm] at hmem
          exact (Submodule.mem_bot _).mp hmem
        have h2v : (2 : ZMod p) • v = 0 := by
          rw [two_smul]
          calc v + v = (v + ρ z v) + (v - ρ z v) := by abel
            _ = 0 := by rw [e1, e2, add_zero]
        exact (smul_eq_zero.mp h2v).resolve_left h2ne
      apply (IsSimpleOrder.bot_ne_top (α := Subrepresentation ρ))
      apply Subrepresentation.toSubmodule_injective
      apply Submodule.ext
      intro v
      constructor
      · intro _
        exact Submodule.mem_top
      · intro _
        rw [hz0 v]
        exact Submodule.zero_mem _
    · right
      intro v
      have hv : v ∈ Sm.toSubmodule := by
        rw [hbm]
        exact Submodule.mem_top
      exact (hmSm v).mp hv
  · left
    apply LinearMap.ext
    intro v
    have hv : v ∈ Sp.toSubmodule := by
      rw [hbp]
      exact Submodule.mem_top
    exact (hmSp v).mp hv

theorem rho_commute_of_perfect {X V : Type*} [Group X] [Finite X] [AddCommGroup V] {p : ℕ}
    [Module (ZMod p) V] (hX : Group.IsPerfect X) (U : Subgroup X)
    (ρ : Representation (ZMod p) X V) (hU : ∀ u ∈ U, ∀ g, ρ ⁅u, g⁆ = 1) {y : X}
    (hy : ∀ g, ⁅y, g⁆ ∈ U) (g : X) : ρ y * ρ g = ρ g * ρ y := by
  have hUc : ∀ u ∈ U, ∀ h : X, ρ u * ρ h = ρ h * ρ u := fun u hu h =>
    (rho_commutator_eq_one_iff ρ u h).mp (hU u hu h)
  have : Group.IsPerfect X := hX
  let φ : X →* (Module.End (ZMod p) V)ˣ := MonoidHom.toHomUnits ρ
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have h2 : φ.rangeRestrict y ∈ Subgroup.upperCentralSeries φ.range 2 := by
    refine (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mpr fun γ => ?_
    obtain ⟨h, rfl⟩ := φ.rangeRestrict_surjective γ
    rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
    intro δ
    obtain ⟨k, rfl⟩ := φ.rangeRestrict_surjective δ
    rw [← map_commutatorElement]
    apply Subtype.ext
    apply Units.ext
    exact (hUc _ (hy h) k).symm
  have h1 : φ.rangeRestrict y ∈ Subgroup.center φ.range := by
    rw [← Group.IsPerfect.upperCentralSeries_eq_center φ.range (n := 2) (by norm_num)]
    exact h2
  have h3 := Subgroup.mem_center_iff.mp h1 (φ.rangeRestrict g)
  exact (congrArg (fun γ : φ.range => ((γ : (Module.End (ZMod p) V)ˣ) : Module.End (ZMod p) V))
    h3).symm

theorem eq_one_of_klein_fixed {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (a b : V →ₗ[ZMod p] V) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (h1 : ∀ v, a v = v → b v = v) (h2 : ∀ v, b v = v → a v = v)
    (h3 : ∀ v, (a * b) v = v → a v = v) : a = 1 ∧ b = 1 := by
  have ha1 : a = 1 := CFSG.RankThree.PartTwo.Sec13.Res7Proof.eq_one_of_fix_three
    (two_ne_zero_zmod hp) ha hb hab a (fun _ h => h) h2 h3
  exact ⟨ha1, LinearMap.ext fun v => h1 v (by rw [ha1, Module.End.one_apply])⟩

theorem exists_chiefModule {G : Type} [Group G] [Finite G] {C P : Subgroup G}
    (hP : FooteLit.IsTwoComponentIn P C) (hD : ⁅oddIn P, P⁆ ≠ ⊥) :
    ∃ (p : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ ∃ (V : Type) (_ : AddCommGroup V)
      (_ : Module (ZMod p) V) (_ : Finite V) (ρ : Representation (ZMod p) ↥P V),
      ρ.IsIrreducible ∧ (∀ g : ↥P, (∀ v, ρ g v = v) → g ∈ Open.fusionZStar ↥P) ∧
      (∀ u ∈ pPrimeCore 2 ↥P, ∀ g : ↥P, ∀ v, ρ ⁅u, g⁆ v = v) ∧
      ∀ t : ↥P, t * t = 1 → ∀ v, ρ t v = v →
        ∃ u ∈ pPrimeCore 2 ↥P, u * t = t * u ∧ ∀ g : ↥P, g * u = u * g → ρ g v = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥P := GSThmB.A10T.isPerfect_of_isPComponent hP.1 hP.2
  have hUodd : Odd (Nat.card (pPrimeCore 2 ↥P)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hYperf : ⁅(⊤ : Subgroup ↥P), ⊤⁆ = ⊤ := hperf.commutator_eq_top
  have hne : ⁅pPrimeCore 2 ↥P, (⊤ : Subgroup ↥P)⁆ ≠ ⊥ := by
    intro h
    apply hD
    have h' := congrArg (Subgroup.map P.subtype) h
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.subtype_range,
      Subgroup.map_bot] at h'
    exact h'
  obtain ⟨p, hp, hp2, V, iV, mV, fV, ρ, hirr, hYact, htriv, hlift⟩ :=
    Walter86.exists_irreducible_chiefFactor_of_commutator_ne_bot (X := ↥P)
      (U := pPrimeCore 2 ↥P) (Y := ⊤) hUodd hYperf hne
  have hker : ∀ g : ↥P, (∀ v, ρ g v = v) → g ∈ Open.fusionZStar ↥P := by
    intro g hg
    rw [Sol78.fusionZStar_eq_comap]
    have hQ := GSThmB.A10T.isQuasisimple_of_isPComponent hP.1 hP.2
    have hKm : ((MonoidHom.ker ρ).map (QuotientGroup.mk' (pPrimeCore 2 ↥P))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases LocalCores.quasisimple_normal_subgroups hQ hKm with htop | hcen
    · exfalso
      obtain ⟨g₀, -, v₀, hv₀⟩ := hYact
      have hmem : ∀ a : ↥P, ∃ u ∈ pPrimeCore 2 ↥P, ρ a = ρ u := by
        intro a
        have ha : QuotientGroup.mk' (pPrimeCore 2 ↥P) a ∈
            (MonoidHom.ker ρ).map (QuotientGroup.mk' (pPrimeCore 2 ↥P)) := by
          rw [htop]
          exact mem_top _
        obtain ⟨k, hk, hka⟩ := ha
        have hu : k⁻¹ * a ∈ pPrimeCore 2 ↥P := QuotientGroup.eq.mp hka
        refine ⟨k⁻¹ * a, hu, ?_⟩
        rw [map_mul, MonoidHom.mem_ker.mp ((MonoidHom.ker ρ).inv_mem hk), one_mul]
      have hcomm : ∀ a b : ↥P, ρ a * ρ b = ρ b * ρ a := by
        intro a b
        obtain ⟨u, hu, hau⟩ := hmem a
        obtain ⟨u', hu', hbu⟩ := hmem b
        rw [hau, hbu]
        refine (rho_commutator_eq_one_iff ρ u u').mp (LinearMap.ext fun v => ?_)
        exact htriv _ (Subgroup.commutator_mem_commutator hu (mem_top u')) v
      have hK : ⁅(⊤ : Subgroup ↥P), ⊤⁆ ≤ MonoidHom.ker ρ := by
        rw [Subgroup.commutator_le]
        intro a _ b _
        exact (MonoidHom.mem_ker).mpr ((rho_commutator_eq_one_iff ρ a b).mpr (hcomm a b))
      rw [hYperf] at hK
      have h1 : ρ g₀ = 1 := MonoidHom.mem_ker.mp (hK (mem_top g₀))
      exact hv₀ (congrArg (fun f : Module.End (ZMod p) V => f v₀) h1)
    · exact hcen ⟨g, (MonoidHom.mem_ker).mpr (LinearMap.ext hg), rfl⟩
  refine ⟨p, hp, hp2, V, iV, mV, fV, ρ, hirr, hker, ?_, ?_⟩
  · intro u hu g v
    exact htriv _ (Subgroup.commutator_mem_commutator hu (Subgroup.mem_top g)) v
  · intro t ht v hv
    obtain ⟨u, hu, htu, hfix⟩ := hlift t (by rw [pow_two]; exact ht) v hv
    exact ⟨u, hu, htu.symm, hfix⟩

end

section

open CFSG Subgroup
open scoped commutatorElement

private theorem zpow_eq_one_or_self {X : Type*} [Group X] {z : X} (hz : z * z = 1) (k : ℤ) :
    z ^ k = 1 ∨ z ^ k = z := by
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  have hk : z ^ k = z ^ (k % 2) :=
    calc z ^ k = z ^ (k % 2 + 2 * (k / 2)) := by rw [Int.emod_add_mul_ediv]
      _ = z ^ (k % 2) := by rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, zpow_zero]
  · right
    rw [hk, h, zpow_one]

private theorem exists_mem_notMem_finset {X : Type} [Group X] [Finite X] (A : Subgroup X)
    (s : Finset X) (hs : s.card < Nat.card A) : ∃ a ∈ A, a ∉ s := by
  by_contra h
  have hsub : (A : Set X) ⊆ (s : Set X) := fun a ha => by
    by_contra hn
    exact h ⟨a, ha, hn⟩
  have h1 : Nat.card (A : Set X) ≤ Nat.card (s : Set X) := Nat.card_mono s.finite_toSet hsub
  have h2 : Nat.card (s : Set X) = s.card := Nat.card_eq_finsetCard s
  exact absurd (lt_of_lt_of_le hs (h2 ▸ h1)) (lt_irrefl _)

private theorem rho_eq_pow_of_mul_mem {X : Type} [Group X] (U : Subgroup X)
    (hUo : Odd (Nat.card U)) {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : Representation (ZMod p) X V) (hUc : ∀ u ∈ U, ∀ g, ρ u * ρ g = ρ g * ρ u)
    {b h w : X} (hbb : b * b = 1) (hw : w ∈ U) (hb : b = h * w) :
    ρ b = ρ (h ^ Nat.card U) := by
  have hsq : ρ b ^ 2 = 1 := by rw [pow_two, ← map_mul, hbb, map_one]
  have hwU : w ^ Nat.card U = 1 := orderOf_dvd_iff_pow_eq_one.mp (U.orderOf_dvd_natCard hw)
  obtain ⟨r, hr⟩ := hUo
  have hcomm : Commute (ρ h) (ρ w) := (hUc w hw h).symm
  calc ρ b = ρ b ^ Nat.card U := by rw [hr, pow_succ, pow_mul, hsq, one_pow, one_mul]
    _ = ρ h ^ Nat.card U * ρ w ^ Nat.card U := by rw [hb, map_mul, hcomm.mul_pow]
    _ = ρ (h ^ Nat.card U) := by rw [← map_pow ρ w, hwU, map_one, mul_one, map_pow]

private theorem exists_fixing_elt {X : Type} [Group X] (U Z : Subgroup X) [U.Normal] [Z.Normal]
    (hUo : Odd (Nat.card U)) (z : X) (hz : z * z = 1) (hZ : Z = U ⊔ zpowers z)
    {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : Representation (ZMod p) X V) (hUc : ∀ u ∈ U, ∀ g, ρ u * ρ g = ρ g * ρ u)
    (A : Subgroup X) (hA : IsElemTwo A) (hzA : z ∈ A) (u : X) (hu : u ∈ A) (H : Subgroup X)
    (hHA : ∀ g : X, ⁅g, u⁆ ∈ Z → g ∈ H ⊔ Z) (a : X) (ha : a ∈ A) :
    ∃ b ∈ A, (b = a ∨ b = a * z) ∧ ∃ x ∈ H, ρ b = ρ x := by
  have haZ : a ∈ H ⊔ Z := by
    refine hHA a ?_
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hA.1 a ha u hu)]
    exact Z.one_mem
  obtain ⟨h, hh, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp haZ
  have hy' : y ∈ U ⊔ zpowers z := by rw [← hZ]; exact hy
  obtain ⟨w, hw, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  rcases zpow_eq_one_or_self hz k with hk | hk
  · refine ⟨h * (w * z ^ k), ha, Or.inl rfl, h ^ Nat.card U, H.pow_mem hh _, ?_⟩
    refine rho_eq_pow_of_mul_mem U hUo ρ hUc (hA.2 _ ha) hw ?_
    rw [hk, mul_one]
  · have hbA : h * (w * z ^ k) * z ∈ A := A.mul_mem ha hzA
    refine ⟨h * (w * z ^ k) * z, hbA, Or.inr rfl, h ^ Nat.card U, H.pow_mem hh _, ?_⟩
    refine rho_eq_pow_of_mul_mem U hUo ρ hUc (hA.2 _ hbA) hw ?_
    rw [hk]
    simp only [mul_assoc, hz, mul_one]

theorem false_of_twoSuz_parity {X : Type} [Group X] [Finite X] (hX : Group.IsPerfect X)
    (U Z : Subgroup X) [U.Normal] [Z.Normal] (hUo : Odd (Nat.card U)) (z : X) (hz : z * z = 1)
    (hZ : Z = U ⊔ zpowers z) (hZc : ∀ y ∈ Z, ∀ g : X, ⁅y, g⁆ ∈ U)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) X V) (hirr : ρ.IsIrreducible)
    (hker : ∀ g, (∀ v, ρ g v = v) → g ∈ Z) (hU1 : ∀ u ∈ U, ∀ g, ∀ v, ρ ⁅u, g⁆ v = v)
    (A : Subgroup X) (hA : IsElemTwo A) (hzA : z ∈ A) (hA8 : 8 ≤ Nat.card A)
    (hAZ : ∀ a ∈ A, a ∈ Z → a = 1 ∨ a = z)
    (hH : ∀ u ∈ A, u ≠ 1 → u ≠ z → ∃ H : Subgroup X, (∀ h ∈ H, h * u = u * h ∧ h * z = z * h) ∧
      (∀ g : X, ⁅g, u⁆ ∈ Z → g ∈ H ⊔ Z) ∧
      ∀ v ∈ ({u, u * z} : Set X), ∀ w, ρ v w = w → ∀ h ∈ H, ρ h w = w) : False := by
  classical
  have hU1' : ∀ u ∈ U, ∀ g, ρ ⁅u, g⁆ = 1 := fun u hu g => LinearMap.ext (hU1 u hu g)
  have hUc : ∀ u ∈ U, ∀ g, ρ u * ρ g = ρ g * ρ u := fun u hu g =>
    (rho_commutator_eq_one_iff ρ u g).mp (hU1' u hu g)
  have hzZ : z ∈ Z := by
    rw [hZ]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hzc : ∀ g, ρ z * ρ g = ρ g * ρ z := fun g =>
    rho_commute_of_perfect hX U ρ hU1' (fun g => hZc z hzZ g) g
  have hS : ∀ u ∈ A, u ≠ 1 → u ≠ z → ∀ a ∈ A, ∃ b ∈ A, (b = a ∨ b = a * z) ∧
      ∀ v ∈ ({u, u * z} : Set X), ∀ w, ρ v w = w → ρ b w = w := by
    intro u hu hu1 huz a ha
    obtain ⟨H, -, hHA, hHfix⟩ := hH u hu hu1 huz
    obtain ⟨b, hbA, hb, x, hx, hbx⟩ :=
      exists_fixing_elt U Z hUo z hz hZ ρ hUc A hA hzA u hu H hHA a ha
    exact ⟨b, hbA, hb, fun v hv w hw => by rw [hbx]; exact hHfix v hv w hw x hx⟩
  have hex : ∀ s : Finset X, s.card < 8 → ∃ a ∈ A, a ∉ s := fun s hs =>
    exists_mem_notMem_finset A s (lt_of_lt_of_le hs hA8)
  rcases rho_eq_one_or_neg_one hp ρ hirr hz hzc with hpos | hneg
  ·
    have hS' : ∀ u ∈ A, u ≠ 1 → u ≠ z → ∀ a ∈ A, ∀ w, ρ u w = w → ρ a w = w := by
      intro u hu hu1 huz a ha w hw
      obtain ⟨b, hbA, hb, hbfix⟩ := hS u hu hu1 huz a ha
      have h1 : ρ b w = w := hbfix u (Set.mem_insert u _) w hw
      have hρb : ρ b = ρ a := by
        rcases hb with hb | hb
        · rw [hb]
        · rw [hb, map_mul, hpos, mul_one]
      rwa [hρb] at h1
    obtain ⟨u₁, hu₁A, hu₁⟩ := hex {1, z} (lt_of_le_of_lt Finset.card_le_two (by norm_num))
    have hu₁1 : u₁ ≠ 1 := fun h => hu₁ (by simp [h])
    have hu₁z : u₁ ≠ z := fun h => hu₁ (by simp [h])
    obtain ⟨u₂, hu₂A, hu₂⟩ :=
      hex {1, z, u₁, u₁ * z} (lt_of_le_of_lt Finset.card_le_four (by norm_num))
    have hu₂1 : u₂ ≠ 1 := fun h => hu₂ (by simp [h])
    have hu₂z : u₂ ≠ z := fun h => hu₂ (by simp [h])
    have hu₂u₁ : u₂ ≠ u₁ := fun h => hu₂ (by simp [h])
    have hu₂u₁z : u₂ ≠ u₁ * z := fun h => hu₂ (by simp [h])
    have hu₁sq : u₁ * u₁ = 1 := hA.2 u₁ hu₁A
    have hu₂sq : u₂ * u₂ = 1 := hA.2 u₂ hu₂A
    have hu₃A : u₁ * u₂ ∈ A := A.mul_mem hu₁A hu₂A
    have hu₂eq : u₂ = u₁ * (u₁ * u₂) := by rw [← mul_assoc, hu₁sq, one_mul]
    have hu₃1 : u₁ * u₂ ≠ 1 := fun h => hu₂u₁ (by rw [hu₂eq, h, mul_one])
    have hu₃z : u₁ * u₂ ≠ z := fun h => hu₂u₁z (by rw [hu₂eq, h])
    have hρ₁ : ρ u₁ * ρ u₁ = 1 := by rw [← map_mul, hu₁sq, map_one]
    have hρ₂ : ρ u₂ * ρ u₂ = 1 := by rw [← map_mul, hu₂sq, map_one]
    have hρ₁₂ : ρ u₁ * ρ u₂ = ρ u₂ * ρ u₁ := by
      rw [← map_mul, ← map_mul, hA.1 u₁ hu₁A u₂ hu₂A]
    have hone := eq_one_of_klein_fixed hp (ρ u₁) (ρ u₂) hρ₁ hρ₂ hρ₁₂
      (fun v hv => hS' u₁ hu₁A hu₁1 hu₁z u₂ hu₂A v hv)
      (fun v hv => hS' u₂ hu₂A hu₂1 hu₂z u₁ hu₁A v hv)
      (fun v hv => hS' (u₁ * u₂) hu₃A hu₃1 hu₃z u₁ hu₁A v (by rwa [map_mul]))
    rcases hAZ u₁ hu₁A (hker u₁ fun v => by rw [hone.1, Module.End.one_apply]) with h | h
    · exact hu₁1 h
    · exact hu₁z h
  ·
    obtain ⟨u, huA, hu⟩ := hex {1, z} (lt_of_le_of_lt Finset.card_le_two (by norm_num))
    have hu1 : u ≠ 1 := fun h => hu (by simp [h])
    have huz : u ≠ z := fun h => hu (by simp [h])
    obtain ⟨b, hbA, hb, hbfix⟩ := hS u huA hu1 huz u huA
    obtain ⟨v, hvA, hv, hbv⟩ : ∃ v ∈ A, v ∈ ({u, u * z} : Set X) ∧ b = v * z := by
      rcases hb with hb | hb
      · exact ⟨u * z, A.mul_mem huA hzA, Set.mem_insert_of_mem _ (Set.mem_singleton _),
          by rw [hb, mul_assoc, hz, mul_one]⟩
      · exact ⟨u, huA, Set.mem_insert u _, hb⟩
    have hvv : v * v = 1 := hA.2 v hvA
    have hC : ∀ w, ρ v w = w → w = 0 := by
      intro w hw
      have h1 : ρ b w = w := hbfix v hv w hw
      have h2 : ρ b w = -w := by
        rw [hbv, map_mul, Module.End.mul_apply, hneg w, map_neg, hw]
      have h3 : w = -w := h1.symm.trans h2
      have h4 : (2 : ZMod p) • w = 0 := by
        rw [two_smul]
        calc w + w = w + -w := by rw [← h3]
          _ = 0 := add_neg_cancel w
      exact (smul_eq_zero.mp h4).resolve_left (two_ne_zero_zmod hp)
    have hvneg : ∀ w, ρ v w = -w := by
      intro w
      have hv2 : ρ v (ρ v w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, hvv, map_one, Module.End.one_apply]
      have hfix : ρ v (w + ρ v w) = w + ρ v w := by rw [map_add, hv2, add_comm]
      exact eq_neg_of_add_eq_zero_right (hC _ hfix)
    have hbZ : b ∈ Z := hker b fun w => by
      rw [hbv, map_mul, Module.End.mul_apply, hneg w, map_neg, hvneg w, neg_neg]
    rcases hAZ b hbA hbZ with h1 | h1 <;> rcases hb with h2 | h2
    · exact hu1 (h2.symm.trans h1)
    · exact huz (mul_right_cancel ((h2.symm.trans h1).trans hz.symm))
    · exact huz (h2.symm.trans h1)
    · exact hu1 (mul_right_cancel ((h2.symm.trans h1).trans (one_mul z).symm))

end

end CFSG.ComponentClassification.GrSLit.L34Sec5S

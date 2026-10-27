module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5STwoSuzFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitConn
public import CFSG.Holt.General.Components
public import CFSG.Holt.H78.Prelim
public import CFSG.GH74.Uniqueness.Section4Lemma45
public import CFSG.GH74.GLS.Stage1.Thm4.L96Sylow
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofTools

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

section

open CFSG Subgroup
open scoped commutatorElement

private theorem mem_fusionZStar_of_eq {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (hN : Open.fusionOddCore X = N) (x : X) :
    x ∈ Open.fusionZStar X ↔ (QuotientGroup.mk x : X ⧸ N) ∈ center (X ⧸ N) := by
  subst hN
  exact Iff.rfl

private theorem mem_fusionZStar_iff_mk {X : Type} [Group X] (x : X) :
    x ∈ Open.fusionZStar X ↔
      (QuotientGroup.mk x : X ⧸ pPrimeCore 2 X) ∈ center (X ⧸ pPrimeCore 2 X) :=
  mem_fusionZStar_of_eq
    (CFSG.ComponentClassification.UnbalancingLocal.fusionOddCore_eq_pPrimeCore X) x

private theorem mem_zpowers_of_sq_one {G : Type*} [Group G] {w : G} (hw : w * w = 1)
    {v : G} (hv : v ∈ zpowers w) : v = 1 ∨ v = w := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hv
  have hw2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hw
  have key : w ^ i = w ^ (i % 2) := by
    have e : i = 2 * (i / 2) + i % 2 := by omega
    calc w ^ i = w ^ (2 * (i / 2) + i % 2) := by rw [← e]
      _ = (w ^ (2 : ℤ)) ^ (i / 2) * w ^ (i % 2) := by rw [zpow_add, zpow_mul]
      _ = w ^ (i % 2) := by rw [hw2, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one i with h | h
  · left; rw [key, h, zpow_zero]
  · right; rw [key, h, zpow_one]

private theorem card_center_quot {X : Type} [Group X] [Finite X]
    (hZ : CFSG.ComponentClassification.RankTwoSporadic.Suz.SuzCentralTwoGroupOrderBound)
    (hperf : Group.IsPerfect X)
    (hS : Blueprint.NativeSporadic.IsSporadic (X ⧸ Open.fusionZStar X) .Suz)
    (hc : center (X ⧸ pPrimeCore 2 X) ≠ ⊥) :
    Nat.card (center (X ⧸ pPrimeCore 2 X)) = 2 := by
  obtain ⟨eS⟩ := CFSG.ComponentClassification.GrSLit.nonempty_quotient_center_equiv_fusionZStar X
  have := hperf
  have hsimpS : IsSimpleGroup (X ⧸ Open.fusionZStar X) :=
    CFSG.EvenSporadicStandard.Solomon78.suz_isSimpleGroup_of_isSporadic hS
  have hq : CFSG.Assembly.IsQuasisimple (X ⧸ pPrimeCore 2 X) :=
    ⟨Group.isPerfect_def.mp inferInstance, MulEquiv.isSimpleGroup eS⟩
  have hsp : Blueprint.NativeSporadic.IsSporadic
      ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) .Suz := by
    obtain ⟨eZ⟩ := hS
    exact ⟨eS.trans eZ⟩
  have hle : Nat.card (center (X ⧸ pPrimeCore 2 X)) ≤ 2 :=
    hZ (X ⧸ pPrimeCore 2 X) hq (CFSG.Holt.General.isPGroup_center_quotient_pPrimeCore X) hsp
  have hgt : 1 < Nat.card (center (X ⧸ pPrimeCore 2 X)) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hc
  have h2 : 2 ∣ Nat.card (center (X ⧸ pPrimeCore 2 X)) := by
    rcases (CFSG.Holt.General.isPGroup_center_quotient_pPrimeCore X).card_eq_or_dvd with h | h
    · omega
    · exact h
  omega

theorem exists_twoSuz_testConfig
    (hZ : CFSG.ComponentClassification.RankTwoSporadic.Suz.SuzCentralTwoGroupOrderBound)
    {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hS : Blueprint.NativeSporadic.IsSporadic (X ⧸ Open.fusionZStar X) .Suz)
    (hr : 3 ≤ pRank 2 X) (hc : center (X ⧸ pPrimeCore 2 X) ≠ ⊥) :
    ∃ (z : X) (A : Subgroup X), z * z = 1 ∧ z ∈ Open.fusionZStar X ∧
      Open.fusionZStar X = pPrimeCore 2 X ⊔ zpowers z ∧
      CFSG.ComponentClassification.GrSLit.IsElemTwo A ∧ z ∈ A ∧ 8 ≤ Nat.card A ∧
      ∀ a ∈ A, a ∈ Open.fusionZStar X → a = 1 ∨ a = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : Odd (Nat.card (pPrimeCore 2 X)) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hcard := card_center_quot hZ hperf hS hc
  obtain ⟨wa, hwa⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc
  obtain ⟨w, hwmem, hw1⟩ : ∃ w ∈ center (X ⧸ pPrimeCore 2 X), w ≠ 1 :=
    ⟨wa.1, wa.2, fun h => hwa (Subtype.ext h)⟩
  have hwo : orderOf w = 2 := by
    have h1 := orderOf_dvd_natCard (⟨w, hwmem⟩ : center (X ⧸ pPrimeCore 2 X))
    rw [hcard, Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have hw2 : w * w = 1 := by
    have h := pow_orderOf_eq_one w
    rw [hwo, pow_two] at h
    exact h
  obtain ⟨z, hz2, hzw⟩ := CFSG.GH74.Uniqueness.exists_involution_lift hO hw2
  have hzmk : (QuotientGroup.mk z : X ⧸ pPrimeCore 2 X) = w := hzw
  have hzZ : z ∈ Open.fusionZStar X :=
    (mem_fusionZStar_iff_mk z).mpr (by rw [hzmk]; exact hwmem)
  have hcen : ∀ v ∈ center (X ⧸ pPrimeCore 2 X), v = 1 ∨ v = w := by
    intro v hv
    have heq : zpowers w = center (X ⧸ pPrimeCore 2 X) :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hwmem)
        (le_of_eq (by rw [Nat.card_zpowers, hwo, hcard]))
    rw [← heq] at hv
    exact mem_zpowers_of_sq_one hw2 hv
  have hZeq : Open.fusionZStar X = pPrimeCore 2 X ⊔ zpowers z := by
    refine le_antisymm (fun x hx => ?_) (sup_le (fun x hx => ?_) (zpowers_le.mpr hzZ))
    · rcases hcen _ ((mem_fusionZStar_iff_mk x).mp hx) with h | h
      · exact Subgroup.mem_sup_left ((QuotientGroup.eq_one_iff x).mp h)
      · have hx' : z⁻¹ * x ∈ pPrimeCore 2 X := QuotientGroup.eq.mp (hzmk.trans h.symm)
        have hm := mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers z) :
          z ∈ pPrimeCore 2 X ⊔ zpowers z) (Subgroup.mem_sup_left hx' :
          z⁻¹ * x ∈ pPrimeCore 2 X ⊔ zpowers z)
        rwa [mul_inv_cancel_left] at hm
    · exact (mem_fusionZStar_iff_mk x).mpr
        (by rw [(QuotientGroup.eq_one_iff x).mpr hx]; exact one_mem _)
  have hPz : IsPGroup 2 (zpowers z) :=
    (CFSG.ComponentClassification.GrSLit.isElemTwo_zpowers hz2).isPGroup
  have hHolt := CFSG.Holt.H78.map_centralizer_eq_of_odd (pPrimeCore 2 X) hO hPz
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup X, C = centralizer ((zpowers z : Subgroup X) : Set X) :=
    ⟨_, rfl⟩
  rw [← hCdef] at hHolt
  have hmapc : (zpowers z).map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤
      center (X ⧸ pPrimeCore 2 X) := by
    rw [Subgroup.map_le_iff_le_comap, zpowers_le]
    exact Subgroup.mem_comap.mpr (by rw [hzw]; exact hwmem)
  have hlift : ∀ v : X ⧸ pPrimeCore 2 X, ∃ l ∈ C, QuotientGroup.mk' (pPrimeCore 2 X) l = v := by
    intro v
    have hmem : v ∈ C.map (QuotientGroup.mk' (pPrimeCore 2 X)) := by
      rw [hHolt]
      exact Subgroup.mem_centralizer_iff.mpr fun m hm =>
        (Subgroup.mem_center_iff.mp (hmapc hm) v).symm
    obtain ⟨l, hl, hlv⟩ := Subgroup.mem_map.mp hmem
    exact ⟨l, hl, hlv⟩
  let φ : C →* X ⧸ pPrimeCore 2 X := (QuotientGroup.mk' (pPrimeCore 2 X)).comp C.subtype
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr fun v => by
    obtain ⟨l, hl, hlv⟩ := hlift v
    exact ⟨⟨l, hl⟩, hlv⟩
  have hker : Odd (Nat.card φ.ker) := by
    rcases Nat.even_or_odd (Nat.card φ.ker) with he | ho
    · exfalso
      obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp he)
      have hk2 : k ^ 2 = 1 := by
        have h := pow_orderOf_eq_one k
        rw [hk] at h
        exact h
      have hkO : ((k : C) : X) ∈ pPrimeCore 2 X :=
        (QuotientGroup.eq_one_iff ((k : C) : X)).mp (MonoidHom.mem_ker.mp k.2)
      have hsq : ((k : C) : X) * ((k : C) : X) = 1 := by
        have h := congrArg (fun t : φ.ker => ((t : C) : X)) hk2
        simpa [pow_two] using h
      have hne : ((k : C) : X) ≠ 1 := by
        intro h1
        have hk1 : k = 1 := Subtype.ext (Subtype.ext h1)
        rw [hk1, orderOf_one] at hk
        norm_num at hk
      exact hne (CFSG.GH74.Uniqueness.eq_one_of_mem_of_sq_eq_one hO hkO hsq)
    · exact ho
  have hO2 : ¬ 2 ∣ Nat.card (pPrimeCore 2 X) := by
    rintro ⟨k, hk⟩
    obtain ⟨m, hm⟩ := hO
    omega
  have hpQ : CFSG.pRank 2 (X ⧸ pPrimeCore 2 X) = CFSG.pRank 2 X :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
      (pPrimeCore 2 X) hO2
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) (⊤ : Subgroup (X ⧸ pPrimeCore 2 X))
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, hpQ] at hEcard
  have h8 : 8 ≤ Nat.card E := by
    rw [hEcard]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hr)
  have hrangeE : E ≤ φ.range := by rw [hrange]; exact le_top
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  obtain ⟨E', hE'c, hE'2, hcardE'⟩ :=
    CFSG.GH74.GLS.Stage1.Thm4.L96.exists_elemAbelian_of_odd_kernel φ hker E hrangeE hEc hE.2
  have hE''c : ∀ a ∈ E'.map C.subtype, ∀ b ∈ E'.map C.subtype, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hE'c x hx y hy]
  have hE''2 : ∀ a ∈ E'.map C.subtype, a * a = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hE'2 x hx
    rw [pow_two] at h
    rw [← map_mul, h, map_one]
  have hE''el : CFSG.ComponentClassification.GrSLit.IsElemTwo (E'.map C.subtype) :=
    ⟨hE''c, hE''2⟩
  have hcomm : ∀ x ∈ zpowers z, ∀ y ∈ E'.map C.subtype, x * y = y * x := by
    intro x hx y hy
    obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.mp hy
    have hcC : (c : X) ∈ centralizer ((zpowers z : Subgroup X) : Set X) := by
      rw [← hCdef]; exact c.2
    exact (Subgroup.mem_centralizer_iff.mp hcC x hx)
  have hAel : CFSG.ComponentClassification.GrSLit.IsElemTwo (zpowers z ⊔ E'.map C.subtype) :=
    CFSG.ComponentClassification.GrSLit.IsElemTwo.sup
      (CFSG.ComponentClassification.GrSLit.isElemTwo_zpowers hz2) hE''el hcomm
  refine ⟨z, zpowers z ⊔ E'.map C.subtype, hz2, hzZ, hZeq, hAel,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers z), ?_, ?_⟩
  · have h1 : Nat.card (E'.map C.subtype) = Nat.card E' :=
      Subgroup.card_map_of_injective C.subtype_injective
    have h2 : Nat.card (E'.map C.subtype) ≤ Nat.card ↥(zpowers z ⊔ E'.map C.subtype) :=
      Subgroup.card_le_of_le le_sup_right
    omega
  · intro a haA haZ
    rcases hcen _ ((mem_fusionZStar_iff_mk a).mp haZ) with h | h
    · exact Or.inl (CFSG.GH74.Uniqueness.eq_one_of_mem_of_sq_eq_one hO
        ((QuotientGroup.eq_one_iff a).mp h) (hAel.2 a haA))
    · right
      have hzA : z ∈ zpowers z ⊔ E'.map C.subtype := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
      have haz : a * z ∈ zpowers z ⊔ E'.map C.subtype := mul_mem haA hzA
      have hmk : (QuotientGroup.mk (a * z) : X ⧸ pPrimeCore 2 X) = 1 := by
        rw [QuotientGroup.mk_mul, h, hzmk, hw2]
      have h1 : a * z = 1 :=
        CFSG.GH74.Uniqueness.eq_one_of_mem_of_sq_eq_one hO
          ((QuotientGroup.eq_one_iff (a * z)).mp hmk) (hAel.2 _ haz)
      exact (eq_inv_of_mul_eq_one_left h1).trans (inv_eq_of_mul_eq_one_right hz2)

theorem exists_doubleCentralizer_subgroup
    (hZ : CFSG.ComponentClassification.RankTwoSporadic.Suz.SuzCentralTwoGroupOrderBound)
    (hC : TwoSuzCentralizerFacts) {X : Type} [Group X] [Finite X]
    (hperf : Group.IsPerfect X)
    (hS : Blueprint.NativeSporadic.IsSporadic (X ⧸ Open.fusionZStar X) .Suz)
    (hc : center (X ⧸ pPrimeCore 2 X) ≠ ⊥) {u z : X} (hu : u * u = 1) (hz : z * z = 1)
    (huz : u * z = z * u) (hzZ : z ∈ Open.fusionZStar X) (huZ : u ∉ Open.fusionZStar X) :
    ∃ H : Subgroup X, (∀ h ∈ H, h * u = u * h ∧ h * z = z * h) ∧ ⁅H, H⁆ = H ∧
      HasSimpleQuotient3Quart ↥H ∧
      ∀ g : X, ⁅g, u⁆ ∈ Open.fusionZStar X → g ∈ H ⊔ Open.fusionZStar X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hperf
  have hO : Odd (Nat.card (pPrimeCore 2 X)) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hcard := card_center_quot hZ hperf hS hc
  have hΛS : Blueprint.NativeSporadic.IsSporadic
      ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) .Suz := by
    obtain ⟨eS⟩ := CFSG.ComponentClassification.GrSLit.nonempty_quotient_center_equiv_fusionZStar X
    obtain ⟨eZ⟩ := hS
    exact ⟨eS.trans eZ⟩
  obtain ⟨ub, hub⟩ : ∃ y : X ⧸ pPrimeCore 2 X, y = QuotientGroup.mk' (pPrimeCore 2 X) u :=
    ⟨_, rfl⟩
  have hu' : ub * ub = 1 := by rw [hub, ← map_mul, hu, map_one]
  have hunc : ub ∉ center (X ⧸ pPrimeCore 2 X) := by
    rw [hub]; exact fun h => huZ ((mem_fusionZStar_iff_mk u).mpr h)
  obtain ⟨hCperf, hCsimp⟩ := hC (X ⧸ pPrimeCore 2 X) inferInstance hΛS hcard ub hu' hunc
  have hkey : ∀ g : X ⧸ pPrimeCore 2 X, ⁅g, ub⁆ ∈ center (X ⧸ pPrimeCore 2 X) → ⁅g, ub⁆ = 1 :=
    fun g hg =>
      commutator_eq_one_of_perfect_centralizer (Z := center (X ⧸ pPrimeCore 2 X)) le_rfl hCperf hg
  obtain ⟨Cs, hCs⟩ : ∃ Cs : Subgroup ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)),
      Cs = centralizer ({QuotientGroup.mk ub} :
        Set ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X))) := ⟨_, rfl⟩
  rw [← hCs] at hCperf hCsimp
  have hmemC : ∀ g : X ⧸ pPrimeCore 2 X, ⁅g, ub⁆ = 1 →
      (QuotientGroup.mk g : (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) ∈ Cs := by
    intro g hg
    rw [hCs, Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (QuotientGroup.mk' (center (X ⧸ pPrimeCore 2 X))) hg
    rw [map_commutatorElement, map_one] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  have hcen' : ∀ v : X ⧸ pPrimeCore 2 X,
      (QuotientGroup.mk v : (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) ∈ Cs →
        ⁅v, ub⁆ = 1 := by
    intro v hv
    rw [hCs, Subgroup.mem_centralizer_singleton_iff] at hv
    have h : QuotientGroup.mk' (center (X ⧸ pPrimeCore 2 X)) ⁅v, ub⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hv
    exact hkey v ((QuotientGroup.eq_one_iff ⁅v, ub⁆).mp h)
  have hPel : CFSG.ComponentClassification.GrSLit.IsElemTwo (zpowers u ⊔ zpowers z : Subgroup X) :=
    CFSG.ComponentClassification.GrSLit.IsElemTwo.sup
      (CFSG.ComponentClassification.GrSLit.isElemTwo_zpowers hu)
      (CFSG.ComponentClassification.GrSLit.isElemTwo_zpowers hz) (by
        rintro x hx y hy
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
        exact ((show Commute u z from huz).zpow_zpow i j).eq)
  have hHolt := CFSG.Holt.H78.map_centralizer_eq_of_odd (pPrimeCore 2 X) hO
    hPel.isPGroup
  obtain ⟨L, hL⟩ : ∃ L : Subgroup X,
      L = centralizer ((zpowers u ⊔ zpowers z : Subgroup X) : Set X) := ⟨_, rfl⟩
  rw [← hL] at hHolt
  have hLuz : ∀ l ∈ L, u * l = l * u ∧ z * l = l * z := by
    intro l hl
    rw [hL] at hl
    exact ⟨Subgroup.mem_centralizer_iff.mp hl u (Subgroup.mem_sup_left (mem_zpowers u)),
      Subgroup.mem_centralizer_iff.mp hl z (Subgroup.mem_sup_right (mem_zpowers z))⟩
  have hLift : ∀ v : X ⧸ pPrimeCore 2 X, ⁅v, ub⁆ = 1 →
      ∃ l ∈ L, QuotientGroup.mk' (pPrimeCore 2 X) l = v := by
    intro v hv
    have hv' : ⁅v, QuotientGroup.mk' (pPrimeCore 2 X) u⁆ = 1 := by rw [← hub]; exact hv
    have hle : (zpowers u ⊔ zpowers z : Subgroup X).map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤
        centralizer {v} := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sup_le (zpowers_le.mpr (Subgroup.mem_comap.mpr ?_))
        (zpowers_le.mpr (Subgroup.mem_comap.mpr ?_))
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (commutatorElement_eq_one_iff_mul_comm.mp hv').symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_center_iff.mp ((mem_fusionZStar_iff_mk z).mp hzZ) v).symm
    have hmem : v ∈ L.map (QuotientGroup.mk' (pPrimeCore 2 X)) := by
      rw [hHolt]
      exact Subgroup.mem_centralizer_iff.mpr fun m hm =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hm)
    obtain ⟨l, hl, hlv⟩ := Subgroup.mem_map.mp hmem
    exact ⟨l, hl, hlv⟩
  let f0 : L →* (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X) :=
    (QuotientGroup.mk' (center (X ⧸ pPrimeCore 2 X))).comp
      ((QuotientGroup.mk' (pPrimeCore 2 X)).comp L.subtype)
  have hf0 : ∀ l : L, f0 l ∈ Cs := fun l => by
    have hl : (l : X) * u = u * (l : X) := ((hLuz l l.2).1).symm
    have hc' : ⁅QuotientGroup.mk' (pPrimeCore 2 X) (l : X), ub⁆ = 1 := by
      rw [hub, ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr hl, map_one]
    exact hmemC _ hc'
  let f : L →* Cs := f0.codRestrict Cs hf0
  have hfsurj : Function.Surjective f := by
    rintro ⟨c, hc⟩
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (center (X ⧸ pPrimeCore 2 X)) c
    obtain ⟨l, hl, hlv⟩ := hLift v (hcen' v hc)
    exact ⟨⟨l, hl⟩, Subtype.ext (congrArg (QuotientGroup.mk' (center (X ⧸ pPrimeCore 2 X))) hlv)⟩
  obtain ⟨D, hDperf, hDmap⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Proof156.exists_isPerfect_map_eq_top f hfsurj hCperf
  have hZsolv : Group.IsSolvable (Open.fusionZStar X) := by
    have hOZ : pPrimeCore 2 X ≤ Open.fusionZStar X := fun x hx =>
      (mem_fusionZStar_iff_mk x).mpr (by rw [(QuotientGroup.eq_one_iff x).mpr hx]; exact one_mem _)
    have : Group.IsSolvable (pPrimeCore 2 X) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hO
    have : Group.IsSolvable (center (X ⧸ pPrimeCore 2 X)) :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a.1)
    let g2 : Open.fusionZStar X →* center (X ⧸ pPrimeCore 2 X) :=
      MonoidHom.codRestrict ((QuotientGroup.mk' (pPrimeCore 2 X)).comp (Open.fusionZStar X).subtype)
        (center (X ⧸ pPrimeCore 2 X)) (fun x => (mem_fusionZStar_iff_mk x.1).mp x.2)
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hOZ) g2 fun x hx => ?_
    have hxO : x.1 ∈ pPrimeCore 2 X :=
      (QuotientGroup.eq_one_iff x.1).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
    exact MonoidHom.mem_range.mpr ⟨⟨x.1, hxO⟩, Subtype.ext rfl⟩
  have hDsimp : HasSimpleQuotient3Quart ↥D := by
    obtain ⟨M, hMn, hMs, hMsimp, hMdvd⟩ := hCsimp
    let φD : D →* Cs := f.comp D.subtype
    let ψ : D →* Cs ⧸ M := (QuotientGroup.mk' M).comp φD
    have hψ : Function.Surjective ψ := by
      intro q
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective M q
      have hc : c ∈ D.map f := by rw [hDmap]; exact Subgroup.mem_top c
      obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.mp hc
      exact ⟨⟨d, hd⟩, by show QuotientGroup.mk' M (f d) = QuotientGroup.mk' M c; rw [hdc]⟩
    have hle : φD.ker ≤ ψ.ker := fun d hd => by
      rw [MonoidHom.mem_ker] at hd ⊢
      show QuotientGroup.mk' M (φD d) = 1
      rw [hd, map_one]
    have hsolvN : Group.IsSolvable φD.ker := by
      have hk : ∀ k : φD.ker, ((k.1 : D) : L).1 ∈ Open.fusionZStar X := fun k => by
        have h1 : QuotientGroup.mk' (center (X ⧸ pPrimeCore 2 X))
            (QuotientGroup.mk' (pPrimeCore 2 X) ((k.1 : D) : L).1) = 1 :=
          congrArg Subtype.val (MonoidHom.mem_ker.mp k.2)
        exact (mem_fusionZStar_iff_mk _).mpr
          ((QuotientGroup.eq_one_iff (QuotientGroup.mk' (pPrimeCore 2 X) ((k.1 : D) : L).1)).mp h1)
      let ι : φD.ker →* Open.fusionZStar X :=
        MonoidHom.codRestrict (L.subtype.comp (D.subtype.comp φD.ker.subtype))
          (Open.fusionZStar X) fun k => hk k
      have hι : Function.Injective ι := by
        intro k1 k2 h
        have h1 : ((k1.1 : D) : L).1 = ((k2.1 : D) : L).1 :=
          congrArg (Subtype.val : Open.fusionZStar X → X) h
        have h2 : k1.1 = k2.1 := Subtype.ext (Subtype.ext h1)
        exact Subtype.ext h2
      have : Group.IsSolvable (Open.fusionZStar X) := hZsolv
      exact Group.isSolvable_of_isSolvable_injective (f := ι) hι
    have hsolvK : Group.IsSolvable ψ.ker := by
      have := hsolvN
      let g : ψ.ker →* M := MonoidHom.codRestrict (φD.comp ψ.ker.subtype) M fun k => by
        have h1 : QuotientGroup.mk' M (φD k.1) = 1 := MonoidHom.mem_ker.mp k.2
        exact (QuotientGroup.eq_one_iff (φD k.1)).mp h1
      refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) g fun k hk => ?_
      have hk1 : φD k.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
      exact MonoidHom.mem_range.mpr ⟨⟨k.1, hk1⟩, Subtype.ext rfl⟩
    refine ⟨ψ.ker, inferInstance, hsolvK, ?_, ?_⟩
    · exact MulEquiv.isSimpleGroup (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    · rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
      exact hMdvd
  refine ⟨D.map L.subtype, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨d, _, rfl⟩ := Subgroup.mem_map.mp hh
    exact ⟨((hLuz _ d.2).1).symm, ((hLuz _ d.2).2).symm⟩
  · have := hDperf
    rw [← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  · exact HasSimpleQuotient3Quart.of_mulEquiv
      (Subgroup.equivMapOfInjective D L.subtype L.subtype_injective) hDsimp
  · intro g hg
    have hg1 : QuotientGroup.mk' (pPrimeCore 2 X) ⁅g, u⁆ ∈ center (X ⧸ pPrimeCore 2 X) :=
      (mem_fusionZStar_iff_mk _).mp hg
    have hg2 : ⁅QuotientGroup.mk' (pPrimeCore 2 X) g, ub⁆ ∈ center (X ⧸ pPrimeCore 2 X) := by
      rw [hub, ← map_commutatorElement]; exact hg1
    have hcg := hmemC _ (hkey _ hg2)
    have hmap : (⟨_, hcg⟩ : Cs) ∈ D.map f := by rw [hDmap]; exact Subgroup.mem_top _
    obtain ⟨d, hd, hdeq⟩ := Subgroup.mem_map.mp hmap
    have hfd : (QuotientGroup.mk (QuotientGroup.mk' (pPrimeCore 2 X) (d : X)) :
        (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) =
        QuotientGroup.mk (QuotientGroup.mk' (pPrimeCore 2 X) g) :=
      congrArg Subtype.val hdeq
    have hz : (d : X)⁻¹ * g ∈ Open.fusionZStar X := by
      rw [mem_fusionZStar_iff_mk, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact QuotientGroup.eq.mp hfd
    have hdH : (d : X) ∈ D.map L.subtype := Subgroup.mem_map.mpr ⟨d, hd, rfl⟩
    have hm := mul_mem (Subgroup.mem_sup_left hdH : (d : X) ∈ D.map L.subtype ⊔ Open.fusionZStar X)
      (Subgroup.mem_sup_right hz : (d : X)⁻¹ * g ∈ D.map L.subtype ⊔ Open.fusionZStar X)
    rwa [mul_inv_cancel_left] at hm

end

end CFSG.ComponentClassification.GrSLit.L34Sec5S

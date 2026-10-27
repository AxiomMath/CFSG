module

public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977StandardCyclic
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.SignalizerFunctorTheorem.Inheritance.Quotient
public import CFSG.GroupTheory.CyclicSubgroup.NormalizerCommutator
public import CFSG.GroupTheory.CharacteristicNormalizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem eq_of_orderOf_eq_two_of_isCyclic' {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {u v : H} (hu : orderOf u = 2) (hv : orderOf v = 2) : u = v :=
  CFSG.EvenSporadicStandard.ThStd.eq_of_orderOf_eq_two_of_isCyclic hu hv

private theorem conj_injective_of_center_eq_bot {F : Type*} [Group F]
    (hcen : Subgroup.center F = ⊥) :
    Function.Injective (MulAut.conj : F →* MulAut F) := by
  intro x y hxy
  have h : MulAut.conj (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy]
    group
  have hcomm : ∀ z : F, (x⁻¹ * y) * z = z * (x⁻¹ * y) := by
    intro z
    have hz := congrArg (fun f : MulAut F => f z) h
    rw [MulAut.conj_apply, MulAut.one_apply] at hz
    calc (x⁻¹ * y) * z = ((x⁻¹ * y) * z * (x⁻¹ * y)⁻¹) * (x⁻¹ * y) := by group
      _ = z * (x⁻¹ * y) := by rw [hz]
  have hc : x⁻¹ * y ∈ Subgroup.center F :=
    Subgroup.mem_center_iff.mpr (fun z => (hcomm z).symm)
  rw [hcen, Subgroup.mem_bot] at hc
  exact inv_mul_eq_one.mp hc

private theorem mem_range_conj_of_odd_order {F : Type*} [Group F]
    (hOut : ∀ α β : MulAut F,
      α ∉ (MulAut.conj : F →* MulAut F).range →
      β ∉ (MulAut.conj : F →* MulAut F).range →
      α * β ∈ (MulAut.conj : F →* MulAut F).range)
    {α : MulAut F} (hodd : Odd (orderOf α)) :
    α ∈ (MulAut.conj : F →* MulAut F).range := by
  by_cases h : α ∈ (MulAut.conj : F →* MulAut F).range
  · exact h
  · have h2 : α ^ 2 ∈ (MulAut.conj : F →* MulAut F).range := by
      have := hOut α α h h
      simpa [sq] using this
    obtain ⟨k, hk⟩ := hodd
    have hα : α = (α ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      rw [show 2 * (k + 1) = orderOf α + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
    rw [hα]
    exact Subgroup.pow_mem _ h2 (k + 1)

private theorem exists_involution_of_isPGroup_two {H : Type*} [Group H] [Finite H]
    {R : Subgroup H} (hR : IsPGroup 2 R) (h2 : 2 ≤ Nat.card R) :
    ∃ t : H, t ∈ R ∧ orderOf t = 2 := by
  have hcard : 2 ∣ Nat.card ↥R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0, pow_zero] at hn
      omega
    · rw [hn]
      exact dvd_pow_self 2 hnpos.ne'
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 hcard
  exact ⟨(t : H), t.2, by rwa [Subgroup.orderOf_coe]⟩

omit [Finite G] in
private theorem commute_of_eq_or_eq_mul {u t₀ s x : G} (hux : u * x = x * u)
    (htx : t₀ * x = x * t₀) (hs : s = u ∨ s = u * t₀) : s * x = x * s := by
  rcases hs with rfl | rfl
  · exact hux
  · calc (u * t₀) * x = u * (t₀ * x) := by group
      _ = u * (x * t₀) := by rw [htx]
      _ = (u * x) * t₀ := by group
      _ = (x * u) * t₀ := by rw [hux]
      _ = x * (u * t₀) := by group

private theorem automizer_apply_eq_conj_of_mem {H : Type*} [Group H] {L : Subgroup H}
    (x : L) :
    CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer L
        ⟨x, Subgroup.le_normalizer x.2⟩ =
      MulAut.conj (QuotientGroup.mk' (Subgroup.center L) x) := by
  ext w
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) w
  change (QuotientGroup.mk' (Subgroup.center L)) (x * l * x⁻¹) =
    (QuotientGroup.mk' (Subgroup.center L)) x * (QuotientGroup.mk' (Subgroup.center L)) l *
      ((QuotientGroup.mk' (Subgroup.center L)) x)⁻¹
  rw [← map_mul, ← map_inv, ← map_mul]

theorem card_le_four_of_full_conj {J : Subgroup G} (hst : IsStandardSubgroup J)
    (hZ : Odd (Nat.card (center ↥J))) (hcen : center (↥J ⧸ center ↥J) = ⊥)
    (hOut : ∀ α β : MulAut (↥J ⧸ center ↥J),
      α ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      β ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      α * β ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    (hO : ∀ a : ↥J ⧸ center ↥J, orderOf a = 2 → ∀ W : Subgroup (↥J ⧸ center ↥J),
      W ≤ centralizer ({a} : Set (↥J ⧸ center ↥J)) →
      (∀ c ∈ centralizer ({a} : Set (↥J ⧸ center ↥J)), ∀ w ∈ W, c * w * c⁻¹ ∈ W) →
      Odd (Nat.card W) → W = ⊥)
    (hLc : ∀ a : ↥J ⧸ center ↥J, orderOf a = 2 →
      Nat.card (centralizer ((⁅centralizer ({a} : Set (↥J ⧸ center ↥J)),
        centralizer ({a} : Set (↥J ⧸ center ↥J))⁆ : Subgroup (↥J ⧸ center ↥J)) :
          Set (↥J ⧸ center ↥J))) = 4)
    (hLf : ∀ a : ↥J ⧸ center ↥J, orderOf a = 2 → ∀ α : MulAut (↥J ⧸ center ↥J),
      (∀ x ∈ ⁅centralizer ({a} : Set (↥J ⧸ center ↥J)), centralizer ({a} : Set (↥J ⧸ center ↥J))⁆,
        α x = x) →
      α ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    (Rs : Sylow 2 ↥(centralizer (J : Set G))) (hRcyc : IsCyclic Rs) (h4 : 4 ≤ Nat.card Rs)
    {g : G} (hg : g ∉ normalizer (J : Set G)) {R T : Subgroup G}
    (hRC : R ≤ centralizer (J : Set G)) (hR : IsPGroup 2 R) (hRcard : Nat.card R = Nat.card Rs)
    (hTg : T ≤ (centralizer (J : Set G)).map (MulAut.conj g).toMonoidHom)
    (hTN : T ≤ normalizer (J : Set G)) (hT : IsPGroup 2 T) (hTcard : Nat.card T = Nat.card Rs)
    (hRT : R ≤ centralizer (T : Set G)) :
    Nat.card Rs ≤ 4 ∧ ∃ u t₀ s : G, u ∈ J ∧ orderOf u = 2 ∧ t₀ ∈ R ∧ orderOf t₀ = 2 ∧ s ∈ T ∧
      orderOf s = 2 ∧ (s = u ∨ s = u * t₀) ∧ ∃ h : G, h⁻¹ * t₀ * h = s := by
  classical
  let C : Subgroup G := centralizer (J : Set G)
  let N : Subgroup G := normalizer (J : Set G)
  let F : Type := ↥J ⧸ center ↥J
  let q : ↥J →* F := QuotientGroup.mk' (center ↥J)
  let π : N →* MulAut F :=
    CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J
  let Cg : Subgroup G := C.map (MulAut.conj g).toMonoidHom
  have hperf : Group.IsPerfect ↥J := hst.1.1
  let : Group.IsPerfect ↥J := hperf
  have : Finite (MulAut F) :=
    Finite.of_injective (fun e : MulAut F => (e : F → F))
      (fun e₁ e₂ h => MulEquiv.ext (fun x => congrFun h x))
  have hNC : Subgroup.normalizer (C : Set G) = N := hst.2.2.2.1
  have hCN : C ≤ N := by rw [← hNC]; exact Subgroup.le_normalizer
  have hJN : J ≤ N := Subgroup.le_normalizer
  have hgC : g ∉ Subgroup.normalizer (C : Set G) := by rw [hNC]; exact hg
  have hginvC : g⁻¹ ∉ Subgroup.normalizer (C : Set G) := fun h =>
    hgC (by simpa using (Subgroup.normalizer (C : Set G)).inv_mem h)
  have hOddInf : Odd (Nat.card ↥(C ⊓ Cg)) := by
    change Odd (Nat.card ↥(C ⊓ C.map (MulAut.conj g).toMonoidHom))
    rw [CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv]
    exact hst.2.2.1 g⁻¹ hginvC
  have hTCbot : T ⊓ C = ⊥ := by
    have hle : T ⊓ C ≤ C ⊓ Cg := by
      rintro x ⟨hxT, hxC⟩
      exact ⟨hxC, hTg hxT⟩
    have hodd : Odd (Nat.card ↥(T ⊓ C)) := hOddInf.of_dvd_nat (Subgroup.card_dvd_of_le hle)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hT.to_le inf_le_left)
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero] at hk
      exact Subgroup.card_eq_one.mp hk
    · have h2 : 2 ∣ Nat.card ↥(T ⊓ C) := by
        rw [hk]
        exact dvd_pow_self 2 hkpos.ne'
      exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)
  have hRcyc' : IsCyclic R :=
    (CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.isCyclic_and_card_le_of_le
      Rs hRcyc hRC hR).1
  have hTcyc : IsCyclic T :=
    (CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.isCyclic_and_card_le_of_le_conj
      Rs hRcyc hTg hT).1
  have hconj_inj : Function.Injective (MulAut.conj : F →* MulAut F) :=
    conj_injective_of_center_eq_bot hcen
  obtain ⟨⟨y, hyT⟩, hgen⟩ := IsCyclic.exists_generator (α := T)
  have hyord : orderOf (⟨y, hyT⟩ : T) = Nat.card T :=
    orderOf_eq_card_of_forall_mem_zpowers hgen
  have h4T : 4 ≤ Nat.card T := by rw [hTcard]; exact h4
  have h4dvd : 4 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
    rw [hTcard] at hn
    have hn2 : 2 ≤ n := by
      by_contra h
      have h2 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hTcard, hn, show 4 = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 hn2
  let yT : T := (⟨y, hyT⟩ : T) ^ (Nat.card T / 4)
  have hyT4 : orderOf yT = 4 := by
    have h1 : orderOf yT = orderOf (⟨y, hyT⟩ : T) / (Nat.card T / 4) :=
      orderOf_pow_of_dvd (x := (⟨y, hyT⟩ : T)) (n := Nat.card T / 4)
        (by omega) (by rw [hyord]; exact Nat.div_dvd_of_dvd h4dvd)
    rw [h1, hyord]
    exact Nat.div_div_self h4dvd (by omega)
  let sT : T := yT ^ 2
  have hsT2 : orderOf sT = 2 := by
    have h : orderOf (yT ^ 2) = 4 / 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hyT4]; norm_num), hyT4]
    rw [show sT = yT ^ 2 from rfl, h]
  let s : G := (sT : G)
  have hsT : s ∈ T := sT.2
  have hs2 : orderOf s = 2 := by rw [show s = (sT : G) from rfl, Subgroup.orderOf_coe]; exact hsT2
  let sN : N := ⟨s, hTN hsT⟩
  let yN : N := ⟨(yT : G), hTN yT.2⟩
  have hsNpow : sN = yN ^ 2 := Subtype.ext (by
    show s = (yT : G) ^ 2
    rfl)
  have hπs : π sN = (π yN) ^ 2 := by rw [hsNpow, map_pow]
  have hInner : π sN ∈ (MulAut.conj : F →* MulAut F).range := by
    rw [hπs]
    by_cases hα : π yN ∈ (MulAut.conj : F →* MulAut F).range
    · exact Subgroup.pow_mem _ hα 2
    · have h := hOut (π yN) (π yN) hα hα
      simpa [sq] using h
  have hπs2 : orderOf (π sN) = 2 := by
    apply orderOf_eq_prime
    · rw [sq, ← map_mul]
      have hsN2 : sN * sN = 1 := Subtype.ext (by
        show s * s = 1
        have h := pow_orderOf_eq_one s
        rwa [hs2, pow_two] at h)
      rw [hsN2, map_one]
    · intro h1
      have hsC : s ∈ C := by
        have := (CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer_eq_one_iff
          J sN).mp h1
        exact this
      have hmem : s ∈ T ⊓ C := Subgroup.mem_inf.mpr ⟨hsT, hsC⟩
      rw [hTCbot] at hmem
      have hs1 : s = 1 := by simpa using hmem
      rw [hs1, orderOf_one] at hs2
      omega
  obtain ⟨abar, habar⟩ := hInner
  have habar2 : orderOf abar = 2 := by
    have h : orderOf (MulAut.conj abar) = 2 := by rw [habar]; exact hπs2
    exact (orderOf_injective (MulAut.conj : F →* MulAut F) hconj_inj abar).symm.trans h
  obtain ⟨xJ, hxJq⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) abar
  have hxq2 : orderOf (QuotientGroup.mk xJ : ↥J ⧸ Subgroup.center ↥J) = 2 := by
    have hx : (QuotientGroup.mk xJ : ↥J ⧸ Subgroup.center ↥J) = abar := hxJq
    rw [hx, habar2]
  obtain ⟨uJ, huJ2, huJq⟩ :=
    CFSG.OddStandard.SmallF3.Omega.exists_involution_lift_of_odd
      (N := Subgroup.center ↥J) hZ hxq2
  let u : G := (uJ : G)
  have huJ : u ∈ J := uJ.2
  have hu2 : orderOf u = 2 := by
    rw [show u = (uJ : G) from rfl, Subgroup.orderOf_coe]
    exact huJ2
  have huJq' : q uJ = abar := by
    change (QuotientGroup.mk uJ : ↥J ⧸ Subgroup.center ↥J) = abar
    rw [huJq]
    exact hxJq
  let uN : N := ⟨u, hJN huJ⟩
  have hπu : π uN = MulAut.conj abar := by
    have h' : π uN = MulAut.conj (q uJ) := by
      have hxeq : uN = ⟨uJ, Subgroup.le_normalizer uJ.2⟩ := Subtype.ext rfl
      rw [hxeq]
      exact automizer_apply_eq_conj_of_mem (H := G) (L := J) uJ
    rw [h', huJq']
  have husC : u⁻¹ * s ∈ C := by
    have hπ1 : π (uN⁻¹ * sN) = 1 := by
      rw [map_mul, map_inv, hπu, habar, inv_mul_cancel]
    have := (CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer_eq_one_iff
      J (uN⁻¹ * sN)).mp hπ1
    exact this
  have hcomm_su : s * u = u * s := by
    have hwJ : s * u * s⁻¹ ∈ J := by
      have hJmap : J.map (MulAut.conj s).toMonoidHom = J :=
        (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hTN hsT)
      have hmem : s * u * s⁻¹ ∈ J.map (MulAut.conj s).toMonoidHom :=
        ⟨u, huJ, by simp [MulAut.conj_apply]⟩
      rwa [hJmap] at hmem
    have hqw : q ⟨s * u * s⁻¹, hwJ⟩ = abar := by
      have hsapp := CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer_apply_mk
        J sN uJ
      rw [← habar] at hsapp
      change (MulAut.conj abar) (uJ : F) = (QuotientGroup.mk' (Subgroup.center ↥J))
        ⟨s * u * s⁻¹, hwJ⟩ at hsapp
      rw [MulAut.conj_apply, show (uJ : F) = abar from huJq'] at hsapp
      rw [mul_assoc, mul_inv_cancel, mul_one] at hsapp
      exact hsapp.symm
    have hwcenter : (⟨(s * u * s⁻¹) * u⁻¹, J.mul_mem hwJ (J.inv_mem huJ)⟩ : ↥J) ∈ Subgroup.center (↥J) := by
      have hmem : q ⟨(s * u * s⁻¹) * u⁻¹, J.mul_mem hwJ (J.inv_mem huJ)⟩ = 1 := by
        have huinv : q ⟨u⁻¹, J.inv_mem huJ⟩ = abar⁻¹ := by
          rw [show (⟨u⁻¹, J.inv_mem huJ⟩ : ↥J) = uJ⁻¹ from Subtype.ext rfl, map_inv, huJq']
        rw [show (⟨(s * u * s⁻¹) * u⁻¹, J.mul_mem hwJ (J.inv_mem huJ)⟩ : ↥J) =
            ⟨s * u * s⁻¹, hwJ⟩ * ⟨u⁻¹, J.inv_mem huJ⟩ from Subtype.ext rfl, map_mul,
          hqw, huinv, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center ↥J)
          (x := ⟨(s * u * s⁻¹) * u⁻¹, J.mul_mem hwJ (J.inv_mem huJ)⟩)).mp hmem
    have hw2 : (s * u * s⁻¹) * (s * u * s⁻¹) = 1 := by
      have hord : orderOf (s * u * s⁻¹) = 2 := by
        have h := MulEquiv.orderOf_eq (MulAut.conj s) u
        rwa [MulAut.conj_apply, hu2] at h
      have h := pow_orderOf_eq_one (s * u * s⁻¹)
      rwa [hord, pow_two] at h
    let wJ : ↥J := ⟨s * u * s⁻¹, hwJ⟩
    let zJ : ↥J := ⟨(s * u * s⁻¹) * u⁻¹, J.mul_mem hwJ (J.inv_mem huJ)⟩
    have hzcenter : zJ ∈ Subgroup.center ↥J := hwcenter
    have hz_eq : wJ = zJ * uJ := Subtype.ext (by
      show s * u * s⁻¹ = ((s * u * s⁻¹) * u⁻¹) * u
      group)
    have hwJ2 : wJ * wJ = 1 := Subtype.ext hw2
    have hcomm_z_u : uJ * zJ = zJ * uJ := Subgroup.mem_center_iff.mp hzcenter uJ
    have huJuJ : uJ * uJ = 1 := by
      have h := pow_orderOf_eq_one uJ
      rwa [huJ2, pow_two] at h
    have hzsq : zJ * zJ = 1 := by
      have h : (zJ * uJ) * (zJ * uJ) = 1 := by rw [← hz_eq]; exact hwJ2
      have h' : (zJ * uJ) * (zJ * uJ) = (zJ * zJ) * (uJ * uJ) := by
        calc (zJ * uJ) * (zJ * uJ) = zJ * (uJ * zJ) * uJ := by group
          _ = zJ * (zJ * uJ) * uJ := by rw [hcomm_z_u]
          _ = (zJ * zJ) * (uJ * uJ) := by group
      rw [h', huJuJ, mul_one] at h
      exact h
    have hz1 : zJ = 1 := by
      have hdvd : orderOf zJ ∣ Nat.card (Subgroup.center ↥J) :=
        Subgroup.orderOf_dvd_natCard _ hzcenter
      have hodd : Odd (orderOf zJ) := hZ.of_dvd_nat hdvd
      have hdvd2 : orderOf zJ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hzsq)
      have h1 : orderOf zJ = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
        · exact h1
        · exfalso
          rw [h2] at hodd
          norm_num at hodd
      exact orderOf_eq_one_iff.mp h1
    have hwu : wJ = uJ := by rw [hz_eq, hz1, one_mul]
    calc s * u = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [show s * u * s⁻¹ = u from congrArg Subtype.val hwu]
  have hus2 : (u⁻¹ * s) * (u⁻¹ * s) = 1 := by
    have hu2' : u * u = 1 := by
      have h := pow_orderOf_eq_one u
      rwa [hu2, pow_two] at h
    have hs2' : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rwa [hs2, pow_two] at h
    have hsu' : s * u⁻¹ = u⁻¹ * s := by
      rw [inv_eq_self_of_orderOf_eq_two hu2]
      exact hcomm_su
    calc (u⁻¹ * s) * (u⁻¹ * s) = u⁻¹ * (s * u⁻¹) * s := by group
      _ = u⁻¹ * (u⁻¹ * s) * s := by rw [hsu']
      _ = (u⁻¹ * u⁻¹) * (s * s) := by group
      _ = 1 := by
        rw [show u⁻¹ * u⁻¹ = u * u by rw [inv_eq_self_of_orderOf_eq_two hu2], hu2', hs2',
          one_mul]
  have hx_commR : ∀ r ∈ R, r * (u⁻¹ * s) = (u⁻¹ * s) * r := by
    intro r hr
    have hur : u * r = r * u :=
      Subgroup.mem_centralizer_iff.mp (hRC hr) u huJ
    have hur' : r * u⁻¹ = u⁻¹ * r := by
      rw [inv_eq_self_of_orderOf_eq_two hu2]
      exact hur.symm
    have hsr : s * r = r * s := Subgroup.mem_centralizer_iff.mp (hRT hr) s hsT
    calc r * (u⁻¹ * s) = (r * u⁻¹) * s := by group
      _ = (u⁻¹ * r) * s := by rw [hur']
      _ = u⁻¹ * (r * s) := by group
      _ = u⁻¹ * (s * r) := by rw [hsr]
      _ = (u⁻¹ * s) * r := by group
  have hxCR : u⁻¹ * s ∈ C ⊓ centralizer (R : Set G) :=
    Subgroup.mem_inf.mpr ⟨husC, Subgroup.mem_centralizer_iff.mpr hx_commR⟩
  have hxR : u⁻¹ * s ∈ R := by
    let P : Subgroup G := Subgroup.zpowers (u⁻¹ * s)
    have hPp : IsPGroup 2 P := by
      have hdvd : orderOf (u⁻¹ * s) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hus2)
      have hcard : Nat.card P ∣ 2 := by rw [Nat.card_zpowers]; exact hdvd
      exact IsPGroup.of_card_dvd_pow (p := 2) (n := 1) (by simpa using hcard)
    have hRnormP : R ≤ Subgroup.normalizer (P : Set G) := by
      intro r hr
      have hrx : r * (u⁻¹ * s) = (u⁻¹ * s) * r := hx_commR r hr
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change (Subgroup.zpowers (u⁻¹ * s)).map (MulAut.conj r).toMonoidHom =
        Subgroup.zpowers (u⁻¹ * s)
      rw [MonoidHom.map_zpowers]
      congr 1
      calc MulAut.conj r (u⁻¹ * s) = r * (u⁻¹ * s) * r⁻¹ := MulAut.conj_apply r _
        _ = ((u⁻¹ * s) * r) * r⁻¹ := by rw [hrx]
        _ = u⁻¹ * s := by group
    have hsupP : IsPGroup 2 (R ⊔ P : Subgroup G) := hR.to_sup_of_normal_right' hPp hRnormP
    have hsupC : R ⊔ P ≤ C := sup_le hRC (Subgroup.zpowers_le.mpr hxCR.1)
    have hcardR : Nat.card ↥(R ⊔ P) ≤ Nat.card ↥R := by
      have h := (CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.isCyclic_and_card_le_of_le
        Rs hRcyc hsupC hsupP).2
      rwa [← hRcard] at h
    have hsup_eq : R ⊔ P = R := by
      have hle : R ≤ R ⊔ P := le_sup_left
      exact (Subgroup.eq_of_le_of_card_ge hle hcardR).symm
    have hxP : u⁻¹ * s ∈ P := Subgroup.mem_zpowers _
    have : u⁻¹ * s ∈ R ⊔ P := Subgroup.mem_sup_right hxP
    rwa [hsup_eq] at this
  obtain ⟨t₀, ht₀R, ht₀2⟩ :=
    exists_involution_of_isPGroup_two hR (by rw [hRcard]; omega)
  have hs_eq : s = u ∨ s = u * t₀ := by
    have hx_t0 : u⁻¹ * s = 1 ∨ u⁻¹ * s = t₀ := by
      have hx2 : orderOf (u⁻¹ * s) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hus2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hx2 with h1 | h2
      · left; exact orderOf_eq_one_iff.mp h1
      · right
        have hx2R : orderOf (⟨u⁻¹ * s, hxR⟩ : R) = 2 := by simpa using h2
        have htR : orderOf (⟨t₀, ht₀R⟩ : R) = 2 := by simpa using ht₀2
        exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic' hx2R htR)
    rcases hx_t0 with h1 | h1
    · left
      calc s = u * (u⁻¹ * s) := by group
        _ = u := by rw [h1, mul_one]
    · right
      calc s = u * (u⁻¹ * s) := by group
        _ = u * t₀ := by rw [h1]
  have hs_conj_t0 : ∃ h : G, h⁻¹ * t₀ * h = s := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hRg_le : R.map (MulAut.conj g).toMonoidHom ≤ Cg := Subgroup.map_mono hRC
    have hRgp : IsPGroup 2 (R.map (MulAut.conj g).toMonoidHom) := hR.map _
    have hCgmax : ∀ P : Subgroup Cg, IsPGroup 2 P → Nat.card P ≤ Nat.card Rs := by
      intro P hP
      have hP' : IsPGroup 2 (P.map Cg.subtype) := hP.map _
      have hle : P.map Cg.subtype ≤ Cg := Subgroup.map_subtype_le _
      have h := (CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.isCyclic_and_card_le_of_le_conj
        Rs hRcyc hle hP').2
      rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective Cg)] at h
    have hTCgp : IsPGroup 2 (T.subgroupOf Cg) :=
      hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTg).symm
    obtain ⟨PT, hPTle⟩ := hTCgp.exists_le_sylow
    have hPTeq : (PT : Subgroup Cg) = T.subgroupOf Cg :=
      (Subgroup.eq_of_le_of_card_ge hPTle (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTg).toEquiv]
        have h := hCgmax (PT : Subgroup Cg) PT.isPGroup'
        rwa [← hTcard] at h)).symm
    have hRg_sub_p : IsPGroup 2 ((R.map (MulAut.conj g).toMonoidHom).subgroupOf Cg) :=
      hRgp.of_equiv (Subgroup.subgroupOfEquivOfLe hRg_le).symm
    obtain ⟨PR, hPRle⟩ := hRg_sub_p.exists_le_sylow
    have hPRmax : Nat.card PR ≤ Nat.card (R.map (MulAut.conj g).toMonoidHom) := by
      have h := hCgmax (PR : Subgroup Cg) PR.isPGroup'
      rwa [← hRcard, ← Subgroup.card_map_of_injective (K := R)
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective] at h
    have hPReq : (PR : Subgroup Cg) = (R.map (MulAut.conj g).toMonoidHom).subgroupOf Cg :=
      (Subgroup.eq_of_le_of_card_ge hPRle (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRg_le).toEquiv]
        exact hPRmax)).symm
    obtain ⟨hc, hhc⟩ := MulAction.exists_smul_eq (↥Cg) PR PT
    have hsub : (PR : Subgroup Cg).map (MulAut.conj hc).toMonoidHom =
        (PT : Subgroup Cg) := by
      have := congrArg (fun S : Sylow 2 ↥Cg => (S : Subgroup ↥Cg)) hhc
      rwa [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at this
    have ht0g_mem : g * t₀ * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom :=
      ⟨t₀, ht₀R, by simp [MulAut.conj_apply]⟩
    have ht0g_Cg : g * t₀ * g⁻¹ ∈ Cg := hRg_le ht0g_mem
    let x : ↥Cg := ⟨g * t₀ * g⁻¹, ht0g_Cg⟩
    have hxPR : x ∈ (PR : Subgroup Cg) := by
      rw [hPReq]
      exact Subgroup.mem_subgroupOf.mpr ht0g_mem
    have hconjx : MulAut.conj hc x ∈ (PT : Subgroup Cg) := by
      rw [← hsub]
      exact Subgroup.mem_map_of_mem _ hxPR
    have hconjxT : ((MulAut.conj hc x : ↥Cg) : G) ∈ T := by
      rw [hPTeq] at hconjx
      exact Subgroup.mem_subgroupOf.mp hconjx
    have hord : orderOf ((MulAut.conj hc x : ↥Cg) : G) = 2 := by
      have h1 : ((MulAut.conj hc x : ↥Cg) : G) = MulAut.conj (hc : G) (x : G) := by
        simp [MulAut.conj_apply]
      rw [h1, MulEquiv.orderOf_eq (MulAut.conj (hc : G)) (x : G)]
      have hxG : (x : G) = MulAut.conj g t₀ := by
        simp [x, MulAut.conj_apply]
      rw [hxG, MulEquiv.orderOf_eq (MulAut.conj g) t₀, ht₀2]
    have heq : ((MulAut.conj hc x : ↥Cg) : G) = s := by
      have h1 : orderOf (⟨((MulAut.conj hc x : ↥Cg) : G), hconjxT⟩ : T) = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact hord
      have h2 : orderOf (⟨s, hsT⟩ : T) = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact hs2
      exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic' h1 h2)
    refine ⟨g⁻¹ * (hc : G)⁻¹, ?_⟩
    calc (g⁻¹ * (hc : G)⁻¹)⁻¹ * t₀ * (g⁻¹ * (hc : G)⁻¹)
        = (hc : G) * g * t₀ * g⁻¹ * (hc : G)⁻¹ := by group
      _ = ((MulAut.conj hc x : ↥Cg) : G) := by
          rw [show ((MulAut.conj hc x : ↥Cg) : G) =
              MulAut.conj (hc : G) (x : G) from by simp [MulAut.conj_apply]]
          rw [show (x : G) = g * t₀ * g⁻¹ from rfl, MulAut.conj_apply]
          group
      _ = s := heq
  let Q0 : Subgroup G := Cg ⊓ N ⊓ centralizer ({s} : Set G)
  have hQ0N : Q0 ≤ N := (inf_le_left : Q0 ≤ _).trans inf_le_right
  have hTQ0 : T ≤ Q0 := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hTg hx, hTN hx⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : s * x = x * s := by
      have := (IsCyclic.isMulCommutative (α := T)).is_comm.comm ⟨s, hsT⟩ ⟨x, hx⟩
      simpa using congrArg Subtype.val this
    exact hcomm.symm
  have hQ0p : ∀ P : Subgroup G, P ≤ Q0 → IsPGroup 2 P → Nat.card P ≤ Nat.card Rs := by
    intro P hPQ hP
    exact (CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.isCyclic_and_card_le_of_le_conj
      Rs hRcyc (hPQ.trans ((inf_le_left : Q0 ≤ _).trans inf_le_left)) hP).2
  have hTQ0p : IsPGroup 2 (T.subgroupOf Q0) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTQ0).symm
  obtain ⟨PQ, hPQ⟩ := hTQ0p.exists_le_sylow
  have hPQeq : (PQ : Subgroup Q0) = T.subgroupOf Q0 := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hPQ
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTQ0).toEquiv, hTcard]
    have h := hQ0p ((PQ : Subgroup Q0).map Q0.subtype) (Subgroup.map_subtype_le _)
      (PQ.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective Q0)] at h
  have hPQcyc : IsCyclic (PQ : Subgroup Q0) := by
    rw [hPQeq]
    exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hTQ0).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTQ0).injective
  obtain ⟨hOcard, hQ0mul, hQ0inf, ⟨hOnorm, hOodd, hOindex, hOuniq⟩, hOchar⟩ :=
    CFSG.cyclic_sylow_normal_odd_complement PQ hPQcyc
  let O : Subgroup Q0 := pPrimeCore 2 Q0
  let Omap : Subgroup G := O.map Q0.subtype
  have hOmap_le_Q0 : Omap ≤ Q0 := Subgroup.map_subtype_le O
  have hOmap_le_N : Omap ≤ N := hOmap_le_Q0.trans hQ0N
  have hOmap_odd : Odd (Nat.card Omap) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Q0)]
    exact hOodd
  have hOmap_char : (Omap.subgroupOf Q0).Characteristic := by
    have hsub : Omap.subgroupOf Q0 = O := by
      ext x
      simp only [Omap, Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hxy : y = x := Subtype.ext hyx
        rw [hxy] at hy
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hsub]
    exact hOchar
  let CJuJ : Subgroup ↥J := centralizer ({uJ} : Set ↥J)
  let CJu : Subgroup G := J ⊓ centralizer ({u} : Set G)
  have hCJu_eq : CJu = CJuJ.map J.subtype := by
    ext x
    constructor
    · rintro ⟨hxJ, hxu⟩
      refine ⟨⟨x, hxJ⟩, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxu))
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        simpa using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))
  have hCJu_normQ0 : CJu ≤ Subgroup.normalizer (Q0 : Set G) := by
    intro x hx
    obtain ⟨hxJ, hxu⟩ := Subgroup.mem_inf.mp hx
    have hxN : x ∈ N := hJN hxJ
    have hxu' : u * x = x * u := (Subgroup.mem_centralizer_singleton_iff.mp hxu).symm
    have ht₀x : t₀ * x = x * t₀ :=
      (Subgroup.mem_centralizer_iff.mp (hRC ht₀R) x hxJ).symm
    have hxs : s * x = x * s := commute_of_eq_or_eq_mul hxu' ht₀x hs_eq
    have hxCs : x ∈ Subgroup.centralizer ({s} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxs.symm
    have hxCsNorm : x ∈ Subgroup.normalizer
        (Subgroup.centralizer ({s} : Set G) : Set G) := by
      have hconj_s : MulAut.conj x s = s := by
        show x * s * x⁻¹ = s
        calc x * s * x⁻¹ = (x * s) * x⁻¹ := rfl
          _ = (s * x) * x⁻¹ := by rw [hxs]
          _ = s := by group
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · calc (Subgroup.centralizer ({s} : Set G)).map (MulAut.conj x).toMonoidHom
            ≤ Subgroup.centralizer (((MulAut.conj x) '' ({s} : Set G)) : Set G) :=
              Subgroup.map_centralizer_le_centralizer_image _ _
          _ = Subgroup.centralizer ({s} : Set G) := by rw [Set.image_singleton, hconj_s]
      · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    have hxCg : x ∈ Subgroup.normalizer (Cg : Set G) := by
      have hCg_eq : Cg = centralizer ((J.map (MulAut.conj g).toMonoidHom) : Set G) := by
        exact (CFSG.StandardSubgroupAPI.centralizer_map_mulEquiv (MulAut.conj g) J).symm
      have hstConj : IsStandardSubgroup (J.map (MulAut.conj g).toMonoidHom) :=
        hst.map_mulEquiv (MulAut.conj g)
      have hs_mem : s ∈ centralizer ((J.map (MulAut.conj g).toMonoidHom) : Set G) := by
        rw [← hCg_eq]
        exact hTg hsT
      have hnorm := (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
        hstConj.assembly hs_mem hs2).1
      rw [hCg_eq]
      have hNCg : Subgroup.normalizer
          (centralizer ((J.map (MulAut.conj g).toMonoidHom) : Set G) : Set G) =
          Subgroup.normalizer ((J.map (MulAut.conj g).toMonoidHom) : Set G) :=
        hstConj.2.2.2.1
      rw [hNCg]
      exact hnorm hxCs
    have hxNself : x ∈ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer hxN
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr
        ⟨Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hxCg, hxNself⟩),
          hxCsNorm⟩)
  have hCJu_normO : CJu ≤ Subgroup.normalizer (Omap : Set G) :=
    hCJu_normQ0.trans (CFSG.GroupTheory.normalizer_le_normalizer_of_characteristic
      hOmap_le_Q0 hOmap_char)
  let OmapN : Subgroup N := Omap.subgroupOf N
  let K : Subgroup (MulAut F) := OmapN.map π
  have hOmapN_odd : Odd (Nat.card OmapN) := by
    rw [show Nat.card OmapN = Nat.card Omap from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOmap_le_N).toEquiv]
    exact hOmap_odd
  have hKodd : Odd (Nat.card K) := hOmapN_odd.of_dvd_nat (Subgroup.card_map_dvd _ _)
  let W : Subgroup F := K.comap (MulAut.conj : F →* MulAut F)
  have hWconj : W.map (MulAut.conj : F →* MulAut F) = K := by
    rw [show W.map (MulAut.conj : F →* MulAut F) =
        (MulAut.conj : F →* MulAut F).range ⊓ K from Subgroup.map_comap_eq _ _]
    rw [inf_eq_right.mpr]
    intro τ hτ
    exact mem_range_conj_of_odd_order hOut
      (hKodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hτ))
  have hWodd : Odd (Nat.card W) :=
    hKodd.of_dvd_nat (Subgroup.card_comap_dvd_of_injective K _ hconj_inj)
  have hKcomm : ∀ τ ∈ K, τ * (MulAut.conj abar) = (MulAut.conj abar) * τ := by
    intro τ hτ
    obtain ⟨oN, hoN, rfl⟩ := Subgroup.mem_map.mp hτ
    have hoQ0 : (oN : G) ∈ Q0 := hOmap_le_Q0 (Subgroup.mem_subgroupOf.mp hoN)
    have hoCs : (oN : G) * s = s * (oN : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hoQ0).2
    have hcommN : oN * sN = sN * oN := Subtype.ext hoCs
    have hπcomm : π oN * π sN = π sN * π oN := by rw [← map_mul, ← map_mul, hcommN]
    rw [habar]
    exact hπcomm
  have hWle : W ≤ centralizer ({abar} : Set F) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwK : MulAut.conj w ∈ K := Subgroup.mem_comap.mp hw
    have hcomm := hKcomm _ hwK
    have h : MulAut.conj (w * abar) = MulAut.conj (abar * w) := by
      rw [map_mul, map_mul, hcomm]
    exact hconj_inj h
  have hCJuJ_map : CJuJ.map q = centralizer ({abar} : Set F) := by
    have hqtop : (⊤ : Subgroup ↥J).map q = ⊤ := by
      rw [Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    have huJsq : uJ ^ 2 = 1 := by
      have h := pow_orderOf_eq_one uJ
      rwa [huJ2] at h
    have h := CFSG.SignalizerFunctorTheorem.map_inf_centralizer_eq
      (H := ↥J) (p := 2) Nat.prime_two (W := ⊤) (N := Subgroup.center ↥J) le_top
      (Nat.coprime_two_left.mpr hZ) (a := uJ) huJsq
    rw [hqtop] at h
    simpa [CJuJ, q, huJq'] using h
  have hUnormK : (centralizer ({abar} : Set F)).map (MulAut.conj : F →* MulAut F) ≤
      Subgroup.normalizer (K : Set (MulAut F)) := by
    intro τ hτ
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hτ
    have hy' : y ∈ CJuJ.map q := by rw [hCJuJ_map]; exact hy
    obtain ⟨xJ, hxJ, hxq⟩ := Subgroup.mem_map.mp hy'
    have hxJ' : (xJ : G) ∈ CJu := by
      rw [hCJu_eq]
      exact ⟨xJ, hxJ, rfl⟩
    have hxNormO : (xJ : G) ∈ Subgroup.normalizer (Omap : Set G) := hCJu_normO hxJ'
    have hxNormON : (⟨(xJ : G), hJN xJ.2⟩ : N) ∈
        Subgroup.normalizer (OmapN : Set N) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hOmap_le_N]
      exact hxNormO
    have hπnorm : π ⟨(xJ : G), hJN xJ.2⟩ ∈
        Subgroup.normalizer (K : Set (MulAut F)) :=
      Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hxNormON)
    have hπx : π ⟨(xJ : G), hJN xJ.2⟩ = MulAut.conj y := by
      have hxeq : (⟨(xJ : G), hJN xJ.2⟩ : N) =
          ⟨xJ, Subgroup.le_normalizer xJ.2⟩ := Subtype.ext rfl
      rw [hxeq, automizer_apply_eq_conj_of_mem (H := G) (L := J) xJ, ← hxq]
    rwa [hπx] at hπnorm
  have hWnorm : ∀ c ∈ centralizer ({abar} : Set F), ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    have hc' : MulAut.conj c ∈ Subgroup.normalizer (K : Set (MulAut F)) :=
      hUnormK (Subgroup.mem_map_of_mem _ hc)
    have hconjmem : MulAut.conj (c * w * c⁻¹) ∈ K := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hc' (MulAut.conj w)).mp
        (Subgroup.mem_comap.mp hw)
    have : MulAut.conj (c * w * c⁻¹) ∈ W.map (MulAut.conj : F →* MulAut F) := by
      rwa [hWconj]
    rwa [Subgroup.mem_map_iff_mem hconj_inj] at this
  have hWbot : W = ⊥ := hO abar habar2 W hWle hWnorm hWodd
  have hKbot : K = ⊥ := by rw [← hWconj, hWbot, Subgroup.map_bot]
  have hOmapC : Omap ≤ C := by
    intro o ho
    have hoK : π ⟨o, hOmap_le_N ho⟩ ∈ K :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ho)
    rw [hKbot] at hoK
    have hπo : π ⟨o, hOmap_le_N ho⟩ = 1 := by simpa using hoK
    exact (CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer_eq_one_iff
      J ⟨o, hOmap_le_N ho⟩).mp hπo
  let Q0N : Subgroup N := Q0.subgroupOf N
  let TN : Subgroup N := T.subgroupOf N
  let KQ : Subgroup (MulAut F) := Q0N.map π
  let KT : Subgroup (MulAut F) := TN.map π
  have hfactor : ∀ qN ∈ Q0N, ∃ o ∈ Omap, ∃ t ∈ T, (qN : G) = o * t := by
    intro qN hqN
    have hqQ0 : (qN : G) ∈ Q0 := Subgroup.mem_subgroupOf.mp hqN
    have hq' : (⟨(qN : G), hqQ0⟩ : Q0) ∈ (O : Set Q0) * (PQ : Set Q0) := by
      rw [hQ0mul]; trivial
    obtain ⟨o, ho, p, hp, hop⟩ := Set.mem_mul.mp hq'
    have hpT : (p : G) ∈ T := by
      have hp' : p ∈ T.subgroupOf Q0 := by rwa [← hPQeq]
      exact Subgroup.mem_subgroupOf.mp hp'
    refine ⟨(o : G), ⟨o, ho, rfl⟩, (p : G), hpT, ?_⟩
    have := congrArg Subtype.val hop
    simpa using this.symm
  have hKQeqKT : KQ = KT := by
    apply le_antisymm
    · intro τ hτ
      obtain ⟨qN, hqN, rfl⟩ := Subgroup.mem_map.mp hτ
      obtain ⟨o, hoO, t, htT, hqt⟩ := hfactor qN hqN
      have hπo1 : π ⟨o, hOmap_le_N hoO⟩ = 1 := by
        have hoK : π ⟨o, hOmap_le_N hoO⟩ ∈ K :=
          Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hoO)
        rw [hKbot] at hoK
        simpa using hoK
      have hqeq : qN = ⟨o, hOmap_le_N hoO⟩ * ⟨t, hTN htT⟩ := Subtype.ext hqt
      rw [hqeq, map_mul, hπo1, one_mul]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr htT)
    · intro x hx
      exact Subgroup.map_mono (fun y hy => Subgroup.mem_subgroupOf.mpr
        (hTQ0 (Subgroup.mem_subgroupOf.mp hy))) hx
  let πT : TN →* KT :=
    { toFun := fun t => ⟨π (t : N), Subgroup.mem_map_of_mem π t.2⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun a b => Subtype.ext (map_mul π (a : N) (b : N)) }
  have hπT_surj : Function.Surjective πT := by
    intro k
    obtain ⟨t, ht, htk⟩ := Subgroup.mem_map.mp k.2
    exact ⟨⟨t, ht⟩, Subtype.ext htk⟩
  have hπT_inj : Function.Injective πT := by
    intro a b hab
    have hπab : π (a : N) = π (b : N) := congrArg Subtype.val hab
    have hker : π ((a * b⁻¹ : TN) : N) = 1 := by
      rw [show ((a * b⁻¹ : TN) : N) = (a : N) * (b : N)⁻¹ from rfl, map_mul, map_inv,
        hπab, mul_inv_cancel]
    have hmemC : ((a * b⁻¹ : TN) : G) ∈ C := by
      have := (CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer_eq_one_iff
        J ((a * b⁻¹ : TN) : N)).mp hker
      exact this
    have hmemT : ((a * b⁻¹ : TN) : G) ∈ T := (a * b⁻¹).2
    have hmem : ((a * b⁻¹ : TN) : G) ∈ T ⊓ C := Subgroup.mem_inf.mpr ⟨hmemT, hmemC⟩
    rw [hTCbot] at hmem
    have h1 : ((a * b⁻¹ : TN) : G) = 1 := by simpa using hmem
    have h2 : (a : N) * (b : N)⁻¹ = 1 := by
      apply Subtype.ext
      simpa using h1
    have h3 : (a : N) = b := mul_inv_eq_one.mp h2
    exact Subtype.ext h3
  have hTNcyc : IsCyclic TN :=
    isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hTN).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTN).injective
  have hKTcyc : IsCyclic KT := isCyclic_of_surjective πT hπT_surj
  have hcardTN : Nat.card TN = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hcardKT : Nat.card KT = Nat.card TN := by
    let e : TN ≃ KT := Equiv.ofBijective πT ⟨hπT_inj, hπT_surj⟩
    exact (Nat.card_congr e).symm
  let U : Subgroup (MulAut F) :=
    (centralizer ({abar} : Set F)).map (MulAut.conj : F →* MulAut F)
  have hUnormKT : U ≤ Subgroup.normalizer (KT : Set (MulAut F)) := by
    have hUKQ : U ≤ Subgroup.normalizer (KQ : Set (MulAut F)) := by
      intro τ hτ
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hτ
      have hy' : y ∈ CJuJ.map q := by rw [hCJuJ_map]; exact hy
      obtain ⟨xJ, hxJ, hxq⟩ := Subgroup.mem_map.mp hy'
      have hxJ' : (xJ : G) ∈ CJu := by
        rw [hCJu_eq]; exact ⟨xJ, hxJ, rfl⟩
      have hxNormQ0 : (xJ : G) ∈ Subgroup.normalizer (Q0 : Set G) := hCJu_normQ0 hxJ'
      have hxNormQ0N : (⟨(xJ : G), hJN xJ.2⟩ : N) ∈
          Subgroup.normalizer (Q0N : Set N) := by
        rw [← Subgroup.subgroupOf_normalizer_eq hQ0N]
        exact hxNormQ0
      have hπnorm : π ⟨(xJ : G), hJN xJ.2⟩ ∈
          Subgroup.normalizer (KQ : Set (MulAut F)) :=
        Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hxNormQ0N)
      have hπx : π ⟨(xJ : G), hJN xJ.2⟩ = MulAut.conj y := by
        have hxeq : (⟨(xJ : G), hJN xJ.2⟩ : N) =
            ⟨xJ, Subgroup.le_normalizer xJ.2⟩ := Subtype.ext rfl
        rw [hxeq, automizer_apply_eq_conj_of_mem (H := G) (L := J) xJ, ← hxq]
      rwa [hπx] at hπnorm
    rwa [hKQeqKT] at hUKQ
  have hcomm_le : ⁅U, U⁆ ≤ Subgroup.centralizer (KT : Set (MulAut F)) :=
    CFSG.GroupTheory.CyclicSubgroup.commutator_le_centralizer KT U U hUnormKT hUnormKT
  let L : Subgroup F := ⁅centralizer ({abar} : Set F), centralizer ({abar} : Set F)⁆
  have hmapL : L.map (MulAut.conj : F →* MulAut F) = ⁅U, U⁆ := by
    rw [show L = ⁅centralizer ({abar} : Set F), centralizer ({abar} : Set F)⁆ from rfl,
      Subgroup.map_commutator]
  have hfixL : ∀ τ ∈ KT, ∀ l ∈ L, τ l = l := by
    intro τ hτ l hl
    have hconjl : MulAut.conj l ∈ ⁅U, U⁆ := by
      rw [← hmapL]
      exact Subgroup.mem_map_of_mem _ hl
    have hcomm : MulAut.conj l * τ = τ * MulAut.conj l :=
      (Subgroup.mem_centralizer_iff.mp (hcomm_le hconjl) τ hτ).symm
    have hτconj : τ * MulAut.conj l * τ⁻¹ = MulAut.conj l := by
      rw [← hcomm]; group
    have hconjτ : τ * MulAut.conj l * τ⁻¹ = MulAut.conj (τ l) := by
      ext z
      simp [MulAut.conj_apply, map_mul]
    rw [hconjτ] at hτconj
    exact hconj_inj hτconj
  have hKTinner : ∀ τ ∈ KT, τ ∈ (MulAut.conj : F →* MulAut F).range := fun τ hτ =>
    hLf abar habar2 τ (hfixL τ hτ)
  let yfun : KT → F := fun τ => (hKTinner τ τ.2).choose
  have hyfun : ∀ τ : KT, MulAut.conj (yfun τ) = (τ : MulAut F) :=
    fun τ => (hKTinner τ τ.2).choose_spec
  have hmem_cent : ∀ τ : KT, yfun τ ∈ centralizer (L : Set F) := by
    intro τ
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : MulAut.conj (yfun τ) l = l := by rw [hyfun]; exact hfixL τ τ.2 l hl
    rw [MulAut.conj_apply] at h1
    calc l * yfun τ = (yfun τ * l * (yfun τ)⁻¹) * yfun τ := by rw [h1]
      _ = yfun τ * l := by group
  let f : KT → centralizer (L : Set F) := fun τ => ⟨yfun τ, hmem_cent τ⟩
  have hf_inj : Function.Injective f := by
    intro τ1 τ2 h
    have hy : yfun τ1 = yfun τ2 := congrArg Subtype.val h
    have hτ : (τ1 : MulAut F) = τ2 := by
      rw [← hyfun τ1, ← hyfun τ2, hy]
    exact Subtype.ext hτ
  have hcard_le : Nat.card KT ≤ Nat.card (centralizer (L : Set F)) :=
    Nat.card_le_card_of_injective f hf_inj
  have hLcard : Nat.card (centralizer (L : Set F)) = 4 := hLc abar habar2
  have hboundT : Nat.card T ≤ 4 := by
    rw [← hcardTN, ← hcardKT]
    rw [hLcard] at hcard_le
    exact hcard_le
  have hbound : Nat.card Rs ≤ 4 := by rw [← hTcard]; exact hboundT
  exact ⟨hbound, u, t₀, s, huJ, hu2, ht₀R, ht₀2, hsT, hs2, hs_eq, hs_conj_t0⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end

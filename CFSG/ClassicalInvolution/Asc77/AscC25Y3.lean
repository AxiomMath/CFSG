module

public import CFSG.ClassicalInvolution.Asc77.AscC25X3
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace C25Y

section Odd

variable {G : Type} [Group G]

theorem exists_conj_of_involutions_odd [Finite G] {N : Subgroup G} (hN : Odd (Nat.card N))
    {u v : G} (hu : u * u = 1) (hv : v * v = 1) (huv : u * v ∈ N) :
    ∃ n ∈ N, v = n * u * n⁻¹ := by
  obtain ⟨k, hk⟩ := hN
  have hwk : (u * v) ^ (2 * k + 1) = 1 := by
    have h1 : (⟨u * v, huv⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
    have h2 : (u * v) ^ Nat.card N = 1 := congrArg Subtype.val h1
    rwa [hk] at h2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hwi : (u * v)⁻¹ = v * u := by rw [mul_inv_rev, hui, hvi]
  have hwu : (u * v) * u = u * (u * v)⁻¹ := by
    rw [hwi]
    group
  have hcomm : ∀ j : ℕ, (u * v) ^ j * u = u * ((u * v)⁻¹) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc (u * v) ^ (j + 1) * u = (u * v) ^ j * ((u * v) * u) := by rw [pow_succ, mul_assoc]
        _ = (u * v) ^ j * (u * (u * v)⁻¹) := by rw [hwu]
        _ = ((u * v) ^ j * u) * (u * v)⁻¹ := by rw [mul_assoc]
        _ = u * ((u * v)⁻¹) ^ j * (u * v)⁻¹ := by rw [ih]
        _ = u * ((u * v)⁻¹) ^ (j + 1) := by rw [pow_succ, mul_assoc]
  have hvw : v = u * (u * v) := by
    calc v = (u * u) * v := by rw [hu, one_mul]
      _ = u * (u * v) := by group
  have hpow : ((u * v)⁻¹) ^ k = (u * v) ^ (k + 1) := by
    have h1 : (u * v) ^ (k + 1) * (u * v) ^ k = 1 := by
      rw [← pow_add]
      convert hwk using 2
      ring
    rw [inv_pow]
    exact (eq_inv_of_mul_eq_one_left h1).symm
  refine ⟨(u * v) ^ k, N.pow_mem huv k, ?_⟩
  have key : (u * v) ^ k * u = v * (u * v) ^ k := by
    calc (u * v) ^ k * u = u * ((u * v)⁻¹) ^ k := hcomm k
      _ = u * (u * v) ^ (k + 1) := by rw [hpow]
      _ = u * ((u * v) * (u * v) ^ k) := by rw [pow_succ']
      _ = (u * (u * v)) * (u * v) ^ k := (mul_assoc u (u * v) ((u * v) ^ k)).symm
      _ = v * (u * v) ^ k := by rw [← hvw]
  calc v = v * (u * v) ^ k * ((u * v) ^ k)⁻¹ := by group
    _ = ((u * v) ^ k * u) * ((u * v) ^ k)⁻¹ := by rw [← key]

end Odd

section LayerAut

variable {G : Type} [Group G]

@[expose] noncomputable def conjOnSub (Y : Subgroup G) {b : G} (hb : conjSub b Y = Y) :
    ↥Y ≃* ↥Y :=
  (Subgroup.equivMapOfInjective Y (MulAut.conj b).toMonoidHom (MulAut.conj b).injective).trans
    (MulEquiv.subgroupCongr hb)

theorem coe_conjOnSub (Y : Subgroup G) {b : G} (hb : conjSub b Y = Y) (x : ↥Y) :
    ((conjOnSub Y hb x : ↥Y) : G) = b * (x : G) * b⁻¹ := rfl

@[expose] noncomputable def layerAut (Y : Subgroup G) {b : G} (hb : conjSub b Y = Y) :
    (↥Y ⧸ classicalInvolutionOddCore ↥Y) ≃* (↥Y ⧸ classicalInvolutionOddCore ↥Y) :=
  QuotientGroup.congr _ _ (conjOnSub Y hb)
    (CFSG.ComponentClassification.OddCore.equiv_invariant (conjOnSub Y hb))

theorem layerAut_mk (Y : Subgroup G) {b : G} (hb : conjSub b Y = Y) (x : ↥Y) :
    layerAut Y hb (QuotientGroup.mk x) = QuotientGroup.mk (conjOnSub Y hb x) := rfl

end LayerAut

section NC4

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem nc4_lift (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    {c : G} (hbC : c * z * c⁻¹ ∈ Subgroup.centralizer ({a} : Set G)) :
    ∀ {J : Subgroup (↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a))},
      J ∈ oddQuotientFamily (exactPair Ω a) →
      ∀ {y : ↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a)},
        y ∈ J → y * y * y * y = 1 → y * y ≠ 1 →
        layerAut (exactLayer Ω a)
          (conjSub_exactLayer hyp.std.setting.stand.hyp.conjInvariant hbC) y = y →
        ∃ M ∈ tqMembers Ω a, IsUniqueInvolution M (c * z * c⁻¹) := by
  classical
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hzK : IsUniqueInvolution K z := hs.hz
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  set b := c * z * c⁻¹ with hbdef
  have hb2 : b * b = 1 := by
    have hz2 : z * z = 1 := hzK.sq
    calc b * b = c * (z * z) * c⁻¹ := by rw [hbdef]; group
      _ = 1 := by rw [hz2]; group
  have hbY : conjSub b (exactLayer Ω a) = exactLayer Ω a :=
    conjSub_exactLayer hΩ.conjInvariant hbC
  set Y := exactLayer Ω a with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  intro J hJ y hyJ hy4 hy2 hfix
  obtain ⟨M₁, hM₁tq, rfl⟩ := T7H.exists_exactImg_of_mem hJ
  obtain ⟨g₁, hg₁⟩ := hst.trans M₁ hM₁tq.1
  have hzM₁ : IsUniqueInvolution M₁ (g₁ * z * g₁⁻¹) := by
    rw [← hg₁]
    exact hzK.conj g₁
  have hy_ord : orderOf y = 4 := by
    have h4 : y ^ 2 ^ (1 + 1) = 1 := by
      have : y ^ 2 ^ (1 + 1) = y * y * y * y := by simp [pow_succ, mul_assoc]
      rw [this]
      exact hy4
    have h2 : ¬ y ^ 2 ^ 1 = 1 := by simpa [pow_two] using hy2
    have := orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4
    simpa using this
  obtain ⟨c0, hcmem, hcy⟩ := Subgroup.mem_map.mp hyJ
  have hcM : (c0 : G) ∈ exactCore a M₁ := Subgroup.mem_subgroupOf.mp hcmem
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c0).ne'
  set c' : ↥Y := c0 ^ m with hc'
  have hc'k : c' ^ (2 ^ k) = 1 := by
    rw [hc', ← pow_mul, mul_comm, ← hkm]
    exact pow_orderOf_eq_one c0
  have hπc' : QuotientGroup.mk' N₀ c' = y ^ m := by
    rw [hc', map_pow, hcy]
  have hcop : Nat.Coprime (orderOf y) m := by
    rw [hy_ord]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
  have hym_ord : orderOf (y ^ m) = 4 := by
    rw [Nat.Coprime.orderOf_pow hcop, hy_ord]
  have hy44 : y ^ 4 = 1 := by
    rw [← hy_ord]
    exact pow_orderOf_eq_one y
  have hc'4 : c' ^ 4 = 1 := by
    have h1 : c' ^ 4 ∈ N₀ := by
      have h0 : QuotientGroup.mk' N₀ (c' ^ 4) = 1 := by
        rw [map_pow, hπc', ← pow_mul, mul_comm, pow_mul, hy44, one_pow]
      exact (QuotientGroup.eq_one_iff _).mp h0
    have h2 : orderOf (⟨c' ^ 4, h1⟩ : N₀) ∣ Nat.card N₀ := orderOf_dvd_natCard _
    have h3 : orderOf (⟨c' ^ 4, h1⟩ : N₀) ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe]
      refine orderOf_dvd_of_pow_eq_one ?_
      show (c' ^ 4) ^ (2 ^ k) = 1
      rw [← pow_mul, mul_comm, pow_mul, hc'k, one_pow]
    have h4 : Nat.Coprime (2 ^ k) (Nat.card N₀) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN₀odd)
    have h5 : orderOf (⟨c' ^ 4, h1⟩ : N₀) = 1 := Nat.eq_one_of_dvd_coprimes h4 h3 h2
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h5)
  have hc'2 : ¬ c' ^ 2 ^ 1 = 1 := by
    intro h'
    have h'' : c' ^ 2 = 1 := by simpa using h'
    have h3 : (y ^ m) ^ 2 = 1 := by
      rw [← hπc', ← map_pow, h'', map_one]
    have h4 : orderOf (y ^ m) ∣ 2 := orderOf_dvd_of_pow_eq_one h3
    rw [hym_ord] at h4
    omega
  have hc'_ord : orderOf c' = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) hc'2 (by simpa using hc'4)
    simpa using this
  set y₁ : G := (c' : G) with hy₁
  have hy₁M : y₁ ∈ M₁ :=
    exactCore_le_left a M₁ ((exactCore a M₁).pow_mem hcM m)
  have hy₁Y : y₁ ∈ Y := c'.2
  have hy₁4 : orderOf y₁ = 4 := by rw [hy₁, Subgroup.orderOf_coe]; exact hc'_ord
  have hfixc : QuotientGroup.mk' N₀ (conjOnSub Y hbY c') = QuotientGroup.mk' N₀ c' := by
    have h1 : layerAut Y hbY (QuotientGroup.mk' N₀ c') =
        QuotientGroup.mk' N₀ (conjOnSub Y hbY c') := layerAut_mk Y hbY c'
    have h2 : layerAut Y hbY (y ^ m) = y ^ m := by rw [map_pow, hfix]
    calc QuotientGroup.mk' N₀ (conjOnSub Y hbY c') = layerAut Y hbY (QuotientGroup.mk' N₀ c') :=
          h1.symm
      _ = layerAut Y hbY (y ^ m) := by rw [hπc']
      _ = y ^ m := h2
      _ = QuotientGroup.mk' N₀ c' := hπc'.symm
  have hcom : ⁅b, y₁⁆ ∈ oddCoreOf Y := by
    have h1 : conjOnSub Y hbY c' * c'⁻¹ ∈ N₀ := by
      have h0 : QuotientGroup.mk' N₀ (conjOnSub Y hbY c' * c'⁻¹) = 1 := by
        rw [map_mul, map_inv, hfixc, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h0
    refine Subgroup.mem_map.mpr ⟨_, h1, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOnSub,
      commutatorElement_def]
    rw [hy₁]
  have hR2 : IsPGroup 2 (Subgroup.zpowers y₁) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hy₁4]; norm_num)
  have hcN : b ∈ Subgroup.normalizer (oddCoreOf Y : Set G) :=
    T7L.mem_normalizer_oddCoreOf (mem_normalizer_iff_conjSub_eq.mpr hbY)
  have huN : y₁ ∈ Subgroup.normalizer (oddCoreOf Y : Set G) :=
    T7L.mem_normalizer_oddCoreOf (Subgroup.le_normalizer hy₁Y)
  obtain ⟨n, hn, hncent⟩ := T7L.exists_conj_centralizes hb2 (oddCoreOf_odd_natCard Y) hR2
    (Subgroup.zpowers_le.mpr huN) hcN
    (fun r hr => C25X.comm_mem_of_mem_zpowers huN hcom hr)
  have hnY : n ∈ Y := oddCoreIn_le _ hn
  have hnC : n ∈ Subgroup.centralizer ({a} : Set G) := exactLayer_le_centralizer Ω a hnY
  have hyc : (n * y₁ * n⁻¹) * b = b * (n * y₁ * n⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (hncent (conj_mem_conjSub (Subgroup.mem_zpowers y₁)))
  have hJ₀Ω : conjSub n M₁ ∈ Ω := hΩ.conjInvariant n M₁ hM₁tq.1
  have hJ₀z : IsUniqueInvolution (conjSub n M₁) (n * (g₁ * z * g₁⁻¹) * n⁻¹) := hzM₁.conj n
  have hyJ' : n * y₁ * n⁻¹ ∈ conjSub n M₁ := conj_mem_conjSub hy₁M
  have hy4' : orderOf (n * y₁ * n⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n) y₁
    simpa [MulAut.conj_apply, hy₁4] using this
  by_cases hbeq : b = n * (g₁ * z * g₁⁻¹) * n⁻¹
  · have hfin : IsUniqueInvolution (conjSub n M₁) b := by
      rw [hbeq]
      exact hJ₀z
    exact ⟨conjSub n M₁, conjSub_mem_tqMembers hΩ.conjInvariant hnC hM₁tq, hfin⟩
  · exfalso
    exact T7ER.not_commute_of_conj hs hyp.hW hyp.hE4 hJ₀Ω hJ₀z hbeq hyJ' hy4' hyc.symm

end NC4

section Single

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem exactImg_conjSub_layer {a : G} {M : Subgroup G} (x : ↥(exactLayer Ω a)) :
    T7H.exactImg Ω a (conjSub (x : G) M) =
      conjSub (QuotientGroup.mk x) (T7H.exactImg Ω a M) := by
  have hnc : (x : G) * a * (x : G)⁻¹ = a := T7H.mem_centralizer_of_mem_exactLayer
  have h1 : exactCore a (conjSub (x : G) M) = conjSub (x : G) (exactCore a M) := by
    have := exactCore_conjSub (x : G) a M
    rwa [hnc] at this
  unfold T7H.exactImg
  rw [h1, ← conjSub_subgroupOf, AscQuot.map_conjSub]
  rfl

theorem exists_centralizer_conj_of_member (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G}
    (ha2 : a * a = 1) (hzY : z ∈ exactLayer Ω a) (hK : K ∈ tqMembers Ω a)
    (D : LieSystemData p f (↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a))
      (oddQuotientFamily (exactPair Ω a)))
    (hD1 : D.card = 1) (hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    {M : Subgroup G} (hM : M ∈ tqMembers Ω a) {b : G} (hb : IsUniqueInvolution M b) :
    ∃ h ∈ Subgroup.centralizer ({a} : Set G), h * z * h⁻¹ = b := by
  classical
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hz : IsUniqueInvolution K z := hs.hz
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  obtain ⟨i, R₁, hR₁, hKbar⟩ := D.fundamental _ (T7H.exactImg_mem hK)
  obtain ⟨i', R₂, hR₂, hMbar⟩ := D.fundamental _ (T7H.exactImg_mem hM)
  have hii : i' = i := Fin.ext (by have h1 := i.2; have h2 := i'.2; omega)
  subst hii
  obtain ⟨g, hg⟩ := RouteD.Gaps.fundamentalSingleClass_of_ne D i' (hD4 i').1 (hD4 i').2
    R₁ hR₁ R₂ hR₂
  have hMK : T7H.exactImg Ω a M = conjSub (D.hom i' g) (T7H.exactImg Ω a K) := by
    rw [hMbar, hKbar, hg, AscQuot.map_conjSub]
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (D.hom i' g)
  have hxC : (x : G) ∈ Subgroup.centralizer ({a} : Set G) := exactLayer_le_centralizer Ω a x.2
  have hK₁ : conjSub (x : G) K ∈ tqMembers Ω a :=
    conjSub_mem_tqMembers hΩ.conjInvariant hxC hK
  have hb₁ : IsUniqueInvolution (conjSub (x : G) K) ((x : G) * z * (x : G)⁻¹) := hz.conj _
  have hb₁Y : (x : G) * z * (x : G)⁻¹ ∈ exactLayer Ω a :=
    (exactLayer Ω a).mul_mem ((exactLayer Ω a).mul_mem x.2 hzY) ((exactLayer Ω a).inv_mem x.2)
  have hbY : b ∈ exactLayer Ω a :=
    exactCore_le_exactLayer hM (T7H.isUniqueInvolution_exactCore hp hΩ hcpg hM hb).mem
  have hbarM := T7H.exactImg_isUnique hp hΩ hcpg hM hb hbY
  have hbar₁ := T7H.exactImg_isUnique hp hΩ hcpg hK₁ hb₁ hb₁Y
  have hEq : T7H.exactImg Ω a (conjSub (x : G) K) = T7H.exactImg Ω a M := by
    rw [exactImg_conjSub_layer, hMK, hx]
  rw [hEq] at hbar₁
  have hbb : T7H.toBar Ω a b hbY = T7H.toBar Ω a ((x : G) * z * (x : G)⁻¹) hb₁Y :=
    hbarM.eq hbar₁
  set u : ↥(exactLayer Ω a) := ⟨(x : G) * z * (x : G)⁻¹, hb₁Y⟩ with hu
  set v : ↥(exactLayer Ω a) := ⟨b, hbY⟩ with hv
  have hu2 : u * u = 1 := by
    apply Subtype.ext
    show ((x : G) * z * (x : G)⁻¹) * ((x : G) * z * (x : G)⁻¹) = 1
    calc ((x : G) * z * (x : G)⁻¹) * ((x : G) * z * (x : G)⁻¹) = (x : G) * (z * z) * (x : G)⁻¹ := by
          group
      _ = 1 := by rw [hz.sq]; group
  have hv2 : v * v = 1 := by
    apply Subtype.ext
    exact hb.sq
  have huv : u * v ∈ classicalInvolutionOddCore ↥(exactLayer Ω a) := by
    have h1 : u⁻¹ * v ∈ classicalInvolutionOddCore ↥(exactLayer Ω a) :=
      QuotientGroup.eq.mp hbb.symm
    rwa [inv_eq_of_mul_eq_one_right hu2] at h1
  obtain ⟨n, hn, hnv⟩ := exists_conj_of_involutions_odd
    (CFSG.ComponentClassification.OddCore.odd_card ↥(exactLayer Ω a)) hu2 hv2 huv
  refine ⟨(n : G) * (x : G), ?_, ?_⟩
  · exact (Subgroup.centralizer ({a} : Set G)).mul_mem
      (exactLayer_le_centralizer Ω a n.2) hxC
  · have h1 : b = (n : G) * ((x : G) * z * (x : G)⁻¹) * (n : G)⁻¹ := congrArg Subtype.val hnv
    rw [h1]
    group

end Single

end C25Y

end CFSG.ClassicalInvolution.Asc77

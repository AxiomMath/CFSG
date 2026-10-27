module

public import CFSG.ClassicalInvolution.Q3.Q3CHSec
public import CFSG.ClassicalInvolution.Q3.Q3NMClass
public import CFSG.ClassicalInvolution.Q3.Q3NMInner

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CH

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

@[expose] def M11OddAutInner3 : Prop :=
  ∀ s : ↥CFSG.Blueprint.NativeSporadic.M11, orderOf s = 2 →
    ∀ α : MulAut ↥CFSG.Blueprint.NativeSporadic.M11, Odd (orderOf α) →
      (∀ x ∈ Subgroup.centralizer ({s} : Set ↥CFSG.Blueprint.NativeSporadic.M11), α x = x) →
        α ∈ innSubgroup ↥CFSG.Blueprint.NativeSporadic.M11

theorem m11OddAutInner3_of_card_le
    (h : Nat.card (MulAut ↥CFSG.Blueprint.NativeSporadic.M11) ≤
      Nat.card ↥CFSG.Blueprint.NativeSporadic.M11) : M11OddAutInner3 := by
  intro _ _ α _ _
  have hinj := conj_injective_of_center_eq_bot (center_m11_eq_bot m11Facts)
  have : Finite (MulAut ↥CFSG.Blueprint.NativeSporadic.M11) :=
    Finite.of_injective (fun β : MulAut ↥CFSG.Blueprint.NativeSporadic.M11 =>
      (β : ↥CFSG.Blueprint.NativeSporadic.M11 → ↥CFSG.Blueprint.NativeSporadic.M11))
      fun β γ hβγ => MulEquiv.ext (congrFun hβγ)
  obtain ⟨x, hx⟩ := (hinj.bijective_of_nat_card_le h).2 α
  exact ⟨x, hx⟩

theorem m11OddAutInner3 :
    M11OddAutInner3 :=
  m11OddAutInner3_of_card_le CFSG.Sporadic.Schreier.m11_mulAut_card

theorem autOddFreeInner_m11 (hM11 : M11OddAutInner3) :
    AutOddFreeInner ↥CFSG.Blueprint.NativeSporadic.M11 :=
  autOddFreeInner_of_centralizing_inner (center_m11_eq_bot m11Facts)
    (fun x hx => m11OddCentralizerFree x hx) hM11

theorem autOddFreeInner_of_mulEquiv {X X' : Type} [Group X] [Finite X] [Group X'] [Finite X']
    (e : X ≃* X') (h : AutOddFreeInner X) : AutOddFreeInner X' := by
  intro 𝒳' hinn' f' hf'inn hf'
  set φ : MulAut X ≃* MulAut X' := MulAut.congr e with hφ
  set 𝒳 : Subgroup (MulAut X) := 𝒳'.map φ.symm.toMonoidHom with h𝒳
  have hinn : innSubgroup X ≤ 𝒳 := by
    rintro _ ⟨x, rfl⟩
    refine ⟨φ (MulAut.conj x), hinn' ⟨e x, ?_⟩, by simp⟩
    ext y
    simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
  let ε : ↥𝒳' ≃* ↥𝒳 := φ.symm.subgroupMap 𝒳'
  have hf : orderOf (ε f') = 2 := by rw [MulEquiv.orderOf_eq]; exact hf'
  have hεinn : ((ε f' : ↥𝒳) : MulAut X) ∈ innSubgroup X := by
    obtain ⟨x', hx'⟩ := hf'inn
    refine ⟨e.symm x', ?_⟩
    show MulAut.conj (e.symm x') = φ.symm (f' : MulAut X')
    refine (MulEquiv.eq_symm_apply φ).mpr ?_
    rw [← hx']
    ext y
    simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv ε f' (h 𝒳 hinn (ε f') hεinn hf)

theorem autOddFreeInnerOn_of_centralQuotient {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    {P : X ⧸ Subgroup.center X → Prop} (h : AutOddFreeInnerOn (X ⧸ Subgroup.center X) P) :
    AutOddFreeInnerOn X fun x => P (QuotientGroup.mk x) := by
  intro 𝒳 hinn f s hs hPs hf
  have hΦ := autToCentralQuotient_injective (X := X)
  set 𝒳' := 𝒳.map (autToCentralQuotient X) with h𝒳'
  have hinn' : innSubgroup (X ⧸ Subgroup.center X) ≤ 𝒳' := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective t
    refine ⟨MulAut.conj x, hinn ⟨x, rfl⟩, ?_⟩
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  let ε : ↥𝒳 ≃* ↥𝒳' := 𝒳.equivMapOfInjective (autToCentralQuotient X) hΦ
  have hf' : orderOf (ε f) = 2 := by rw [MulEquiv.orderOf_eq]; exact hf
  have hεs : MulAut.conj (QuotientGroup.mk s : X ⧸ Subgroup.center X) =
      ((ε f : ↥𝒳') : MulAut (X ⧸ Subgroup.center X)) := by
    show MulAut.conj (QuotientGroup.mk s) = autToCentralQuotient X (f : MulAut X)
    rw [← hs]
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv ε f (h 𝒳' hinn' (ε f) _ hεs hPs hf')

theorem sl2Three_eq_neg_one {g : SL(2, ZMod 3)} (h : g * g = 1) (h1 : g ≠ 1) : g = -1 := by
  have key : ∀ g : SL(2, ZMod 3), g * g = 1 → g = 1 ∨ g = -1 := by decide +kernel
  exact (key g h).resolve_left h1

theorem eq_one_of_mul_self_of_odd {Y : Type} [Group Y] {N : Subgroup Y} (hN : Odd (Nat.card N))
    {u : Y} (hu : u ∈ N) (hu2 : u * u = 1) : u = 1 := by
  have h1 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hu2)
  have h2 : orderOf u ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hu
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h3 | h3
  · exact orderOf_eq_one_iff.mp h3
  · exfalso
    rw [h3] at h2
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h2)

theorem mk_eq_mk_of_isClassicalMember3 {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {z : Y}
    (h : IsClassicalMember3 K z) {w : ↥K} (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    (QuotientGroup.mk w : ↥K ⧸ classicalInvolutionOddCore ↥K) =
      QuotientGroup.mk (⟨z, h.mem⟩ : ↥K) := by
  obtain ⟨e⟩ := h.nonempty_equiv
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥K)) := OddCore.odd_card _
  have hne : ∀ u : ↥K, u * u = 1 → u ≠ 1 →
      (QuotientGroup.mk u : ↥K ⧸ classicalInvolutionOddCore ↥K) ≠ 1 := fun u hu2 hu1 hmk =>
    hu1 (eq_one_of_mul_self_of_odd hodd ((QuotientGroup.eq_one_iff u).mp hmk) hu2)
  have hzz : (⟨z, h.mem⟩ : ↥K) * ⟨z, h.mem⟩ = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, sq] at this
  have hz1 : (⟨z, h.mem⟩ : ↥K) ≠ 1 := fun h1 => (isCentralInvolution_of_isClassicalMember3 h).ne_one
    (congrArg Subtype.val h1)
  apply e.injective
  have h1 := sl2Three_eq_neg_one (g := e (QuotientGroup.mk w))
    (by rw [← map_mul, ← QuotientGroup.mk_mul, hw2, QuotientGroup.mk_one, map_one])
    (fun h1 => hne w hw2 hw1 (by rw [← map_one e] at h1; exact e.injective h1))
  have h2 := sl2Three_eq_neg_one (g := e (QuotientGroup.mk ⟨z, h.mem⟩))
    (by rw [← map_mul, ← QuotientGroup.mk_mul, hzz, QuotientGroup.mk_one, map_one])
    (fun h1 => hne _ hzz hz1 (by rw [← map_one e] at h1; exact e.injective h1))
  rw [h1, h2]

theorem isClassicalMember3_map_center {X : Type} [Group X] [Finite X] {K : Subgroup X} {z : X}
    (h : IsClassicalMember3 K z) (hz : z ∉ Subgroup.center X) :
    IsClassicalMember3 (K.map (QuotientGroup.mk' (Subgroup.center X)))
      (QuotientGroup.mk' (Subgroup.center X) z) := by
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, sq] at this
  have hπz : QuotientGroup.mk' (Subgroup.center X) z ≠ 1 := fun h1 =>
    hz ((QuotientGroup.eq_one_iff z).mp h1)
  refine ⟨orderOf_eq_prime (by rw [sq, ← map_mul, hz2, map_one]) hπz,
    Subgroup.mem_map_of_mem _ h.mem, ?_, ?_⟩
  · have h1 := Components.chain_map (QuotientGroup.mk' (Subgroup.center X)) h.subnormal
    have h2 : (Subgroup.centralizer ({z} : Set X)).map (QuotientGroup.mk' (Subgroup.center X)) ≤
        Subgroup.centralizer
          ({QuotientGroup.mk' (Subgroup.center X) z} : Set (X ⧸ Subgroup.center X)) := by
      rintro _ ⟨c, hc, rfl⟩
      have hc' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc']
    refine isSubnormal_trans h1 (isSubnormal_of_normal_subgroupOf h2 ?_)
    rw [Subgroup.normal_subgroupOf_iff h2]
    rintro _ x ⟨c, hc', rfl⟩ hx
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) x
    have hc : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc'
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have hζ : x₀ * z * x₀⁻¹ * z⁻¹ ∈ Subgroup.center X := by
      have h3 : QuotientGroup.mk' (Subgroup.center X) (x₀ * z * x₀⁻¹ * z⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx]
        group
      exact (QuotientGroup.eq_one_iff _).mp h3
    refine ⟨x₀ * c * x₀⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    show x₀ * c * x₀⁻¹ ∈ Subgroup.centralizer ({z} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hw : x₀ * c * x₀⁻¹ * (x₀ * z * x₀⁻¹) = x₀ * z * x₀⁻¹ * (x₀ * c * x₀⁻¹) := by
      calc x₀ * c * x₀⁻¹ * (x₀ * z * x₀⁻¹) = x₀ * (c * z) * x₀⁻¹ := by group
        _ = x₀ * (z * c) * x₀⁻¹ := by rw [hc]
        _ = x₀ * z * x₀⁻¹ * (x₀ * c * x₀⁻¹) := by group
    have hz' : x₀ * z * x₀⁻¹ = (x₀ * z * x₀⁻¹ * z⁻¹) * z := by group
    rw [hz'] at hw
    have hcomm := Subgroup.mem_center_iff.mp hζ (x₀ * c * x₀⁻¹)
    calc x₀ * c * x₀⁻¹ * z
        = (x₀ * z * x₀⁻¹ * z⁻¹)⁻¹ * (x₀ * c * x₀⁻¹ * (x₀ * z * x₀⁻¹ * z⁻¹)) * z := by
          rw [hcomm]; group
      _ = (x₀ * z * x₀⁻¹ * z⁻¹)⁻¹ * (x₀ * c * x₀⁻¹ * ((x₀ * z * x₀⁻¹ * z⁻¹) * z)) := by group
      _ = (x₀ * z * x₀⁻¹ * z⁻¹)⁻¹ * ((x₀ * z * x₀⁻¹ * z⁻¹) * z * (x₀ * c * x₀⁻¹)) := by rw [hw]
      _ = z * (x₀ * c * x₀⁻¹) := by group
  · obtain ⟨e⟩ := h.nonempty_equiv
    set π := (QuotientGroup.mk' (Subgroup.center X)).subgroupMap K with hπ
    have hodd : Odd (Nat.card π.ker) := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
      have hw2 : orderOf (w : ↥K) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
      have hwZ : ((w : ↥K) : X) ∈ Subgroup.center X := by
        have h3 : π (w : ↥K) = 1 := w.2
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h3)
      have hww : (w : ↥K) * (w : ↥K) = 1 := mul_self_eq_one_of_orderOf_eq_two' hw2
      have hw1 : (w : ↥K) ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hw2; omega
      have hmk := mk_eq_mk_of_isClassicalMember3 h hww hw1
      rw [QuotientGroup.eq] at hmk
      have hu : (w : ↥K)⁻¹ * ⟨z, h.mem⟩ * ((w : ↥K)⁻¹ * ⟨z, h.mem⟩) = 1 := by
        apply Subtype.ext
        have hc : ((w : ↥K) : X)⁻¹ * z = z * ((w : ↥K) : X)⁻¹ :=
          (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hwZ) z).symm
        have hww' : ((w : ↥K) : X) * ((w : ↥K) : X) = 1 := congrArg Subtype.val hww
        show ((w : ↥K) : X)⁻¹ * z * (((w : ↥K) : X)⁻¹ * z) = 1
        calc ((w : ↥K) : X)⁻¹ * z * (((w : ↥K) : X)⁻¹ * z)
            = ((w : ↥K) : X)⁻¹ * (z * ((w : ↥K) : X)⁻¹) * z := by group
          _ = ((w : ↥K) : X)⁻¹ * (((w : ↥K) : X)⁻¹ * z) * z := by rw [hc]
          _ = (((w : ↥K) : X) * ((w : ↥K) : X))⁻¹ * (z * z) := by group
          _ = 1 := by rw [hww', hz2, inv_one, one_mul]
      have hu1 := eq_one_of_mul_self_of_odd (OddCore.odd_card _) hmk hu
      have hwz : (w : ↥K) = ⟨z, h.mem⟩ := by
        rw [inv_mul_eq_one] at hu1
        exact hu1
      have hwz' : ((w : ↥K) : X) = z := congrArg Subtype.val hwz
      exact hz (hwz' ▸ hwZ)
    exact ⟨(OddKernel.coreQuotientEquiv π (MonoidHom.subgroupMap_surjective _ K) hodd).symm.trans
      e⟩

@[expose] def ClassicalInner (L : Type) [Group L] (τ : MulAut L) : Prop :=
  ∃ y : L, MulAut.conj y = τ ∧
    ∃ K : Subgroup (L ⧸ Subgroup.center L), IsClassicalMember3 K (QuotientGroup.mk y)

theorem autOddFreeOn_classicalInner_of_inner {L : Type} [Group L] (h : AutOddFreeInner L) :
    AutOddFreeOn L (ClassicalInner L) :=
  h.toOn.mono fun _ ⟨y, hy, _⟩ => ⟨y, hy⟩

theorem autOddFreeOn_classicalInner_of_innerOn {L : Type} [Group L]
    (h : AutOddFreeInnerOn L fun y => ∃ K : Subgroup (L ⧸ Subgroup.center L),
      IsClassicalMember3 K (QuotientGroup.mk y)) :
    AutOddFreeOn L (ClassicalInner L) :=
  fun 𝒳 hinn f ⟨y, hy, hK⟩ hf => h 𝒳 hinn f y hy hK hf


theorem autOddFreeOn_range {X : Type} [Group X] [Finite X] (hM11 : M11OddAutInner3)
    {c : CompData}
    (hc : (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ c = CompData.model t n) ∨
      c = CompData.m11)
    (ψ : c.G →* X) (hker : ψ.ker ≤ Subgroup.center c.G) (hψ1 : ∃ x, ψ x ≠ 1) :
    AutOddFreeOn ↥ψ.range (ClassicalInner ↥ψ.range) := by
  rcases hc with ⟨t, n, ht, hadm, rfl⟩ | rfl
  · have hker' : ψ.rangeRestrict.ker ≤ Subgroup.center _ := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hker
    by_cases hD4 : t = .POmegaPlus ∧ n = 4
    · obtain ⟨rfl, rfl⟩ := hD4
      obtain ⟨hXq, hψ', hker'', hSq, hZS⟩ := centralQuotientData Nat.prime_three ht hadm ↥ψ.range
        ψ.rangeRestrict ψ.rangeRestrict_surjective hker'
      have : Group.IsPerfect ↥ψ.range := ⟨hXq.1⟩
      exact autOddFreeOn_classicalInner_of_innerOn (autOddFreeInnerOn_of_centralQuotient
        (autOddFreeInnerOn_D4 hSq hZS _ hψ' hker''))
    · refine autOddFreeOn_classicalInner_of_inner ?_
      by_cases hT : t = .trialityD4
      · subst hT
        have hn : n = 0 := hadm.2.2
        subst hn
        exact autOddFreeInnerTag_trialityD4 Nat.prime_three ht hadm _ ψ.rangeRestrict
          ψ.rangeRestrict_surjective hker'
      · exact autOddFreeInnerTag_of_not_D4 hD4 hT Nat.prime_three ht hadm _ ψ.rangeRestrict
          ψ.rangeRestrict_surjective hker'
  · obtain ⟨-, ⟨e⟩⟩ := range_m11 m11Facts rfl ψ hψ1
    exact autOddFreeOn_classicalInner_of_inner
      (autOddFreeInner_of_mulEquiv e.symm (autOddFreeInner_m11 hM11))

section Alpha

variable {G : Type} [Group G] [Finite G]

theorem oddQuotMk_mem_center_of_mem_zpowers {s e : G} (he : e ∈ Subgroup.zpowers s)
    (heC : e ∈ Subgroup.centralizer ({s} : Set G)) :
    oddQuotMk s ⟨e, heC⟩ ∈ Subgroup.center (OddQuot s) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hc : Commute (c : G) s := (Subgroup.mem_centralizer_singleton_iff.mp c.2)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  show oddQuotMk s c * oddQuotMk s ⟨s ^ k, heC⟩ = oddQuotMk s ⟨s ^ k, heC⟩ * oddQuotMk s c
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc.zpow_right k).eq

theorem exists_mul_central_of_mem_modOdd {A : Subgroup G} {s z₁ z₂ : G}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hAgen : A = Subgroup.closure {z₁, z₂, s})
    {w : OddQuot s} (hw : w ∈ modOdd s A) :
    ∃ d ∈ ({1, z₁, z₂, z₁ * z₂} : Set G), ∃ hdC : d ∈ Subgroup.centralizer ({s} : Set G),
      ∃ e ∈ Subgroup.center (OddQuot s), w = oddQuotMk s ⟨d, hdC⟩ * e := by
  obtain ⟨k, hkA, rfl⟩ := hw
  have hz₁A : z₁ ∈ A := hAgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hz₂A : z₂ ∈ A :=
    hAgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hsA : s ∈ A :=
    hAgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hset : ({z₁, z₂, s} : Set G) = ({z₁, z₂} : Set G) ∪ {s} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff, or_assoc]
  have hk : (k : G) ∈ Subgroup.closure ({z₁, z₂} : Set G) ⊔ Subgroup.zpowers s := by
    rw [Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, ← hset, ← hAgen]
    exact hkA
  have hCA := Lemma52Proof.le_centralizer_of_mem hA hsA
  have hle : Subgroup.closure ({z₁, z₂} : Set G) ≤ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hCA hz₁A
    · exact hCA hz₂A
  have hZC : Subgroup.zpowers s ≤ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.zpowers_le.mpr (Lemma52Proof.self_mem_centralizer_singleton s)
  obtain ⟨d, hd, e, he, hde⟩ := exists_mul_of_mem_sup_central hle (fun e he c hc => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hc) m).eq).symm) hk
  have hdset : d ∈ ({1, z₁, z₂, z₁ * z₂} : Set G) := by
    rcases TypeCSetup.mem_closure_pair (Lemma52Proof.mul_self_eq_one_of_mem hA hz₁A)
      (Lemma52Proof.mul_self_eq_one_of_mem hA hz₂A)
      (Subgroup.mem_centralizer_singleton_iff.mp (Lemma52Proof.le_centralizer_of_mem hA hz₂A hz₁A))
      hd with h | h | h | h <;> simp [h]
  refine ⟨d, hdset, hle hd, oddQuotMk s ⟨e, hZC he⟩,
    oddQuotMk_mem_center_of_mem_zpowers he (hZC he), ?_⟩
  rw [← map_mul]
  congr 1
  exact Subtype.ext hde

theorem conjOnNormalizer_eq_conj {H : Type} [Group H] {L : Subgroup H}
    (w : ↥(Subgroup.normalizer (L : Set H))) {d : H} (hd : d ∈ L) {e : H}
    (he : e ∈ Subgroup.center H) (hwe : (w : H) = d * e) :
    conjOnNormalizer L w = MulAut.conj (⟨d, hd⟩ : ↥L) := by
  refine MulEquiv.ext fun y => Subtype.ext ?_
  have hey : e * (y : H) = y * e := (Subgroup.mem_center_iff.mp he y).symm
  show (w : H) * y * (w : H)⁻¹ = d * y * d⁻¹
  rw [hwe, mul_inv_rev, mul_assoc d e, hey]
  group

theorem alphaOf_inducedImage_eq_bot_of_classical {A : Subgroup G} {s z₁ z₂ : G}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hAgen : A = Subgroup.closure {z₁, z₂, s})
    {L : Subgroup (OddQuot s)} (hrow : AutOddFreeOn ↥L (ClassicalInner ↥L))
    (hcl : ∀ d ∈ ({z₁, z₂, z₁ * z₂} : Set G), ∀ hdC : d ∈ Subgroup.centralizer ({s} : Set G),
      ∃ hdL : oddQuotMk s ⟨d, hdC⟩ ∈ L, ∃ K : Subgroup (↥L ⧸ Subgroup.center ↥L),
        IsClassicalMember3 K (QuotientGroup.mk ⟨oddQuotMk s ⟨d, hdC⟩, hdL⟩))
    (hz₁C : z₁ ∈ Subgroup.centralizer ({s} : Set G))
    (hmov : ∃ y ∈ L, oddQuotMk s ⟨z₁, hz₁C⟩ * y ≠ y * oddQuotMk s ⟨z₁, hz₁C⟩) :
    alphaOf (inducedImage L (modOdd s A)) = ⊥ := by
  have hz₁A : z₁ ∈ A := hAgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  obtain ⟨hz₁L, -⟩ := hcl z₁ (Set.mem_insert _ _) hz₁C
  refine alphaOf_eq_bot_of_on L (ClassicalInner ↥L) hrow _ ?_ ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    have hww : w * w = 1 := by
      apply Subtype.ext
      obtain ⟨k, hkA, hk⟩ := hw
      have hk' : oddQuotMk s k = (w : OddQuot s) := hk
      have hkk : k * k = 1 := Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hA hkA)
      show (w : OddQuot s) * w = 1
      rw [← hk', ← map_mul, hkk, map_one]
    rw [← map_mul, hww, map_one]
  · refine ⟨toInducedAutOn L ⟨oddQuotMk s ⟨z₁, hz₁C⟩, Subgroup.le_normalizer hz₁L⟩,
      ⟨_, oddQuotMk_mem_modOdd hz₁A hz₁C, rfl⟩, fun h1 => ?_⟩
    obtain ⟨y, hyL, hy⟩ := hmov
    apply hy
    have h2 : conjOnNormalizer L ⟨oddQuotMk s ⟨z₁, hz₁C⟩, Subgroup.le_normalizer hz₁L⟩ = 1 :=
      congrArg Subtype.val h1
    have h3 := congrArg (fun τ : MulAut ↥L => ((τ ⟨y, hyL⟩ : ↥L) : OddQuot s)) h2
    change oddQuotMk s ⟨z₁, hz₁C⟩ * y * (oddQuotMk s ⟨z₁, hz₁C⟩)⁻¹ = y at h3
    calc oddQuotMk s ⟨z₁, hz₁C⟩ * y
        = oddQuotMk s ⟨z₁, hz₁C⟩ * y * (oddQuotMk s ⟨z₁, hz₁C⟩)⁻¹ * oddQuotMk s ⟨z₁, hz₁C⟩ := by
          group
      _ = y * oddQuotMk s ⟨z₁, hz₁C⟩ := by rw [h3]
  · rintro _ ⟨w, hw, rfl⟩ hx1
    have hw' : (w : OddQuot s) ∈ modOdd s A := hw
    obtain ⟨d, hd, hdC, e, he, hwe⟩ := exists_mul_central_of_mem_modOdd hA hAgen hw'
    rcases hd with rfl | hd
    · exfalso
      apply hx1
      apply Subtype.ext
      have h1 := conjOnNormalizer_eq_conj w L.one_mem he
        (by rw [hwe, show oddQuotMk s ⟨1, hdC⟩ = 1 from map_one _])
      exact h1.trans (map_one _)
    · obtain ⟨hdL, K, hK⟩ := hcl d hd hdC
      exact ⟨⟨_, hdL⟩, (conjOnNormalizer_eq_conj w hdL he hwe).symm, K, hK⟩

theorem exists_classical_center {s z : G} {K : Subgroup G}
    (hK : IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) K z)
    (hzC : z ∈ Subgroup.centralizer ({s} : Set G)) {L : Subgroup (OddQuot s)}
    (hKL : modOdd s K ≤ L)
    (hnc : ∃ y ∈ L, oddQuotMk s ⟨z, hzC⟩ * y ≠ y * oddQuotMk s ⟨z, hzC⟩) :
    ∃ hzL : oddQuotMk s ⟨z, hzC⟩ ∈ L, ∃ K' : Subgroup (↥L ⧸ Subgroup.center ↥L),
      IsClassicalMember3 K' (QuotientGroup.mk ⟨oddQuotMk s ⟨z, hzC⟩, hzL⟩) := by
  obtain ⟨hzY, hcl⟩ := hK.toIn
  have h1 : IsClassicalMember3 (modOdd s K) (oddQuotMk s ⟨z, hzC⟩) := hcl.map_oddQuotient
  have h2 := h1.subgroupOf hKL
  have hz : (⟨oddQuotMk s ⟨z, hzC⟩, hKL h1.mem⟩ : ↥L) ∉ Subgroup.center ↥L := by
    intro hc
    obtain ⟨y, hyL, hy⟩ := hnc
    exact hy (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hyL⟩).symm)
  exact ⟨hKL h1.mem, _, isClassicalMember3_map_center h2 hz⟩

end Alpha

theorem hyp51At_of_layers (hM11 : M11OddAutInner3) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hBelow : CIT3Below (Nat.card G))
    {A : Subgroup G} {s z₁ z₂ : G} (hA : CFSG.Open.IsElemAbelian 2 A) (hsA : s ∈ A)
    (hz₁A : z₁ ∈ A) (hz₂A : z₂ ∈ A) (hAgen : A = Subgroup.closure {z₁, z₂, s}) (hs1 : s ≠ 1)
    (hz₁1 : z₁ ≠ 1) (hz₂1 : z₂ ≠ 1) (hz₁₂ : z₁ ≠ z₂) (hz₁s : z₁ ≠ s) (hz₂s : z₂ ≠ s)
    (hz₃s : z₁ * z₂ ≠ s) {L₁ L₂ L₃ : Subgroup G}
    (h₁ : IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L₁ z₁)
    (h₂ : IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L₂ z₂)
    (h₃ : IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L₃ (z₁ * z₂)) :
    Hyp51At A s := by
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
  have hsnc : ¬ ({s} : Set G) ⊆ Subgroup.center G := fun hs => hs1 (by
    have h1 : s ∈ Subgroup.center G := hs (Set.mem_singleton s)
    rwa [hZ, Subgroup.mem_bot] at h1)
  have hΦ := secData3_sFamily3 h₁ h₂ h₃
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hsnc
  have hz₁C : z₁ ∈ Subgroup.centralizer ({s} : Set G) := h₁.le h₁.mem
  have hz₂C : z₂ ∈ Subgroup.centralizer ({s} : Set G) := h₂.le h₂.mem
  have hz₃C : z₁ * z₂ ∈ Subgroup.centralizer ({s} : Set G) := h₃.le h₃.mem
  have hz₃A : z₁ * z₂ ∈ A := A.mul_mem hz₁A hz₂A
  have hz₃1 : z₁ * z₂ ≠ 1 := fun h => hz₁₂ (by
    have hz₂2 : z₂ * z₂ = 1 := Lemma52Proof.mul_self_eq_one_of_mem hA hz₂A
    calc z₁ = z₁ * z₂ * z₂ := by rw [mul_assoc, hz₂2, mul_one]
      _ = z₂ := by rw [h, one_mul])
  obtain ⟨j₁, hj₁⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_one s L₁ L₂ L₃)
  obtain ⟨j₂, hj₂⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_two s L₁ L₂ L₃)
  obtain ⟨j₃, hj₃⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_three s L₁ L₂ L₃)
  have hmov : ∀ {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1) (hbs : b ≠ s)
      (hbC : b ∈ Subgroup.centralizer ({s} : Set G)) {j : ι},
      oddQuotMk s ⟨b, hbC⟩ ∈ secComp hΦ D j → ∀ L : Subgroup (OddQuot s),
        CFSG.IsComponent L → MovedByAll A s L → L = secComp hΦ D j :=
    fun hbA hb1 hbs hbC _ hbj L hL hm =>
      eq_secComp_of_movedByAll hΦ D hA hsA hs1 hbA hb1 hbs hbC hbj hL hm
  have hm₁ := hmov hz₁A hz₁1 hz₁s hz₁C (hj₁ (oddQuotMk_mem_modOdd h₁.mem hz₁C))
  have hm₂ := hmov hz₂A hz₂1 hz₂s hz₂C (hj₂ (oddQuotMk_mem_modOdd h₂.mem hz₂C))
  have hm₃ := hmov hz₃A hz₃1 hz₃s hz₃C (hj₃ (oddQuotMk_mem_modOdd h₃.mem hz₃C))
  refine ⟨fun L L' hL hL' hm hm' => (hm₁ L hL hm).trans (hm₁ L' hL' hm').symm,
    fun L hL hm => ?_⟩
  have hnc : ∀ {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1) (hbs : b ≠ s)
      (hbC : b ∈ Subgroup.centralizer ({s} : Set G)),
      ∃ y ∈ L, oddQuotMk s ⟨b, hbC⟩ * y ≠ y * oddQuotMk s ⟨b, hbC⟩ :=
    fun hbA hb1 hbs hbC => hm _ (oddQuotMk_mem_modOdd hbA hbC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hA hsA hs1 hbA hb1 hbs hbC)
  have hle₁ : modOdd s L₁ ≤ L := (hm₁ L hL hm) ▸ hj₁
  have hle₂ : modOdd s L₂ ≤ L := (hm₂ L hL hm) ▸ hj₂
  have hle₃ : modOdd s L₃ ≤ L := (hm₃ L hL hm) ▸ hj₃
  have hcl : ∀ d ∈ ({z₁, z₂, z₁ * z₂} : Set G), ∀ hdC : d ∈ Subgroup.centralizer ({s} : Set G),
      ∃ hdL : oddQuotMk s ⟨d, hdC⟩ ∈ L, ∃ K : Subgroup (↥L ⧸ Subgroup.center ↥L),
        IsClassicalMember3 K (QuotientGroup.mk ⟨oddQuotMk s ⟨d, hdC⟩, hdL⟩) := by
    rintro d (rfl | rfl | rfl) hdC
    · exact exists_classical_center h₁ hdC hle₁ (hnc hz₁A hz₁1 hz₁s hdC)
    · exact exists_classical_center h₂ hdC hle₂ (hnc hz₂A hz₂1 hz₂s hdC)
    · exact exists_classical_center h₃ hdC hle₃ (hnc hz₃A hz₃1 hz₃s hdC)
  have hrow : AutOddFreeOn ↥L (ClassicalInner ↥L) := by
    have hL₁ := hm₁ L hL hm
    have hk := kind_of_isComponent_secComp hΦ D (hL₁ ▸ hL)
    subst hL₁
    exact autOddFreeOn_range hM11 hk _ (ker_comp_le_center D _ (sectionQuotientHom_injective _) j₁)
      (exists_comp_ne_one D _ (sectionQuotientHom_injective _) j₁)
  exact alphaOf_inducedImage_eq_bot_of_classical hA hAgen hrow hcl hz₁C
    (hnc hz₁A hz₁1 hz₁s hz₁C)

theorem hyp51At_of_layers'
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hBelow : CIT3Below (Nat.card G)) {A : Subgroup G}
    {s z₁ z₂ : G} (hA : CFSG.Open.IsElemAbelian 2 A) (hsA : s ∈ A) (hz₁A : z₁ ∈ A)
    (hz₂A : z₂ ∈ A) (hAgen : A = Subgroup.closure {z₁, z₂, s}) (hs1 : s ≠ 1) (hz₁1 : z₁ ≠ 1)
    (hz₂1 : z₂ ≠ 1) (hz₁₂ : z₁ ≠ z₂) (hz₁s : z₁ ≠ s) (hz₂s : z₂ ≠ s) (hz₃s : z₁ * z₂ ≠ s)
    {L₁ L₂ L₃ : Subgroup G} (h₁ : IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L₁ z₁)
    (h₂ : IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L₂ z₂)
    (h₃ : IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L₃ (z₁ * z₂)) :
    Hyp51At A s :=
  hyp51At_of_layers m11OddAutInner3 hnab hBelow hA hsA hz₁A hz₂A hAgen hs1 hz₁1 hz₂1 hz₁₂ hz₁s
    hz₂s hz₃s h₁ h₂ h₃

end CFSG.ClassicalInvolution.Q3.Q3CH

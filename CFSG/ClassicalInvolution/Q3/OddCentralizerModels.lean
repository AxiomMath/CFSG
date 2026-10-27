module

public import CFSG.ClassicalInvolution.Q3.OddCentralizerFree
public import CFSG.ClassicalInvolution.Q3.WeakBalance
public import CFSG.ClassicalInvolution.Q3.ClassicalFundamentalModels

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups commutatorElement

@[expose] def OddCoreFree (P : Type) [Group P] [Finite P] : Prop :=
  ∀ s : P, s * s = 1 → oddCoreIn (Subgroup.centralizer ({s} : Set P)) = ⊥

theorem oddCoreFreeInvolutions_of_oddCoreFree {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (h : OddCoreFree S) : OddCoreFreeInvolutions S := by
  intro s hs hss
  have hss' : (⟨s, hs⟩ : S) * ⟨s, hs⟩ = 1 := Subtype.ext hss
  rw [← map_centralizer_subtype hs, ← map_oddCoreIn_subtype, h _ hss', Subgroup.map_bot]

theorem OddCoreFree.of_mulEquiv {P P' : Type} [Group P] [Finite P] [Group P'] [Finite P']
    (e : P ≃* P') (h : OddCoreFree P') : OddCoreFree P := by
  intro s hs
  have hmap : (Subgroup.centralizer ({s} : Set P)).map e.toMonoidHom =
      Subgroup.centralizer ({e s} : Set P') := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hy]
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
  have h1 := map_oddCoreIn_le e.toMonoidHom hmap
  rw [h (e s) (by rw [← map_mul, hs, map_one]), le_bot_iff] at h1
  rw [eq_bot_iff]
  intro x hx
  have : e.toMonoidHom x ∈ (oddCoreIn (Subgroup.centralizer ({s} : Set P))).map e.toMonoidHom :=
    ⟨x, hx, rfl⟩
  rw [h1, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (e.injective (by simpa using this))

theorem oddCoreIn_centralizer_eq_bot_of_normal_isPGroup {P : Type} [Group P] [Finite P]
    {V : Subgroup P} (hVn : V.Normal) (hV : IsPGroup 2 V)
    (hC : Subgroup.centralizer (V : Set P) ≤ V) {s : P}
    (hs : s ∈ Subgroup.centralizer (V : Set P)) :
    oddCoreIn (Subgroup.centralizer ({s} : Set P)) = ⊥ := by
  set C := Subgroup.centralizer ({s} : Set P) with hCdef
  have hVC : V ≤ C := by
    intro v hv
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hs v hv
  have hVO : ∀ x, x ∈ V → x ∈ oddCoreIn C → x = 1 := by
    intro x hxV hxO
    obtain ⟨k, hk⟩ := hV ⟨x, hxV⟩
    have h1 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have h3 : Odd (orderOf x) :=
      Odd.of_dvd_nat (odd_card_oddCoreIn C) (Subgroup.orderOf_dvd_natCard _ hxO)
    have h4 : orderOf x = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr h3).pow_right k) h2
    exact orderOf_eq_one_iff.mp h4
  rw [eq_bot_iff]
  intro o ho
  rw [Subgroup.mem_bot]
  have hoV : o ∈ Subgroup.centralizer (V : Set P) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvC : v ∈ C := hVC hv
    have hcomm : ⁅o, v⁆ = 1 := by
      apply hVO
      · have : ⁅o, v⁆ = (o * v * o⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
        rw [this]
        exact V.mul_mem (hVn.conj_mem v hv o) (V.inv_mem hv)
      · have : ⁅o, v⁆ = o * (v * o⁻¹ * v⁻¹) := by simp only [commutatorElement_def]; group
        rw [this]
        exact (oddCoreIn C).mul_mem ho (conj_mem_oddCoreIn hvC ((oddCoreIn C).inv_mem ho))
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
  exact hVO o (hC hoV) ho

theorem exists_orderOf_eq_two_of_isQuasisimple {P : Type*} [Group P] [Finite P]
    (hP : CFSG.Open.IsQuasisimple P) : ∃ x : P, orderOf x = 2 := by
  have : Group.IsPerfect P := ⟨hP.1⟩
  have : Nontrivial P := CFSG.ComponentClassification.Quasisimple.nontrivial hP
  have h2 : 2 ∣ Nat.card P := by
    by_contra hnd
    have hodd : Odd (Nat.card P) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
    have hsolv : Group.IsSolvable P := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial P
    rw [Group.IsPerfect.commutator_eq_top] at hlt
    exact lt_irrefl _ hlt
  exact exists_prime_orderOf_dvd_card' 2 h2

theorem oddCoreFree_of_isQuasisimple {P : Type} [Group P] [Finite P]
    (hP : CFSG.Open.IsQuasisimple P)
    (h : ∀ s : P, orderOf s = 2 → oddCoreIn (Subgroup.centralizer ({s} : Set P)) = ⊥) :
    OddCoreFree P := by
  intro s hs
  by_cases hs1 : s = 1
  · subst hs1
    have hC1 : Subgroup.centralizer ({(1 : P)} : Set P) = ⊤ := by
      ext g
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [hC1]
    obtain ⟨x, hx⟩ := exists_orderOf_eq_two_of_isQuasisimple hP
    set S := oddCoreIn (⊤ : Subgroup P) with hS
    have hSn : S.Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (normalizer_oddCoreIn ⊤))
    have hSodd : Odd (Nat.card S) := odd_card_oddCoreIn _
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hP S with hc | htop
    · have hle : S ≤ oddCoreIn (Subgroup.centralizer ({x} : Set P)) := by
        refine le_oddCoreIn_of_normalizes ?_ ?_ hSodd
        · intro g hg
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_center_iff.mp (hc hg) x).symm
        · intro g _
          rw [Subgroup.normalizer_eq_top_iff.mpr hSn]
          trivial
      rw [h x hx] at hle
      exact le_bot_iff.mp hle
    · exfalso
      have hodd : Odd (Nat.card (⊤ : Subgroup P)) := htop ▸ hSodd
      rw [Subgroup.card_top] at hodd
      have h2 : 2 ∣ Nat.card P := hx ▸ orderOf_dvd_natCard x
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · exact h s (orderOf_eq_prime (by rwa [← sq] at hs) hs1)

theorem isQuasisimple_of_centralQuotient {K P : Type} [Group K] [Group P]
    (hK : CFSG.Open.IsQuasisimple K) (ψ : K →* P) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) : CFSG.Open.IsQuasisimple P :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm
    (CFSG.ComponentClassification.Quasisimple.central_quotient hK ψ.ker hker)

theorem mem_center_of_commutator_mem {K : Type} [Group K] [Group.IsPerfect K] {N : Subgroup K}
    (hN : N ≤ Subgroup.center K) {g : K} (hg : ∀ h : K, ⁅g, h⁆ ∈ N) :
    g ∈ Subgroup.center K := by
  have h1 : QuotientGroup.mk' (Subgroup.center K) g ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have h2 : QuotientGroup.mk' (Subgroup.center K) ⁅g, h⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hN (hg h))
    rw [map_commutatorElement] at h2
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  rw [Group.IsPerfect.center_quotient_center_eq_bot K, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem ker_comp_le_center {K X : Type} [Group K] [Group X] (φ : K →* X)
    (hsec : ∀ g : K, (∀ h : K, ⁅g, h⁆ ∈ φ.ker) → g ∈ Subgroup.center K) :
    ((QuotientGroup.mk' (Subgroup.center X)).comp φ).ker ≤ Subgroup.center K := by
  intro g hg
  apply hsec
  intro h
  have hgZ : φ g ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hg)
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hgZ (φ h)).symm

section SL23

private theorem sl23_center : ∀ g : SL(2, ZMod 3), (∀ y : SL(2, ZMod 3), y * g = g * y) →
    g = 1 ∨ g = -1 := by
  decide +kernel

private theorem sl23_secondCenter : ∀ g : SL(2, ZMod 3),
    (∀ h : SL(2, ZMod 3), ⁅g, h⁆ = 1 ∨ ⁅g, h⁆ = -1) → g = 1 ∨ g = -1 := by
  decide +kernel

private theorem sl23_selfCentralizing : ∀ g : SL(2, ZMod 3),
    (∀ q : SL(2, ZMod 3), q ^ 4 = 1 → ⁅g, q⁆ = 1 ∨ ⁅g, q⁆ = -1) → g ^ 4 = 1 := by
  decide +kernel

private theorem sl23_quaternionComm : ∀ q h : SL(2, ZMod 3), q ^ 4 = 1 → h ^ 4 = 1 →
    ⁅q, h⁆ = 1 ∨ ⁅q, h⁆ = -1 := by
  decide +kernel

private theorem sl23_sq_one : ∀ s : SL(2, ZMod 3), s * s = 1 → s = 1 ∨ s = -1 := by
  decide +kernel

private theorem sl23_neg_central : ∀ s : SL(2, ZMod 3), s * (-1) = (-1) * s := by
  decide +kernel

private theorem sl23_neg_mul_neg : (-1 : SL(2, ZMod 3)) * (-1) = 1 := by decide +kernel

theorem sl23_second_center {X : Type} [Group X] (φ : SL(2, ZMod 3) →* X)
    (hφ : φ.ker ≤ Subgroup.center SL(2, ZMod 3)) :
    ∀ g : SL(2, ZMod 3), (∀ h : SL(2, ZMod 3), ⁅g, h⁆ ∈ φ.ker) →
      g ∈ Subgroup.center SL(2, ZMod 3) := by
  intro g hg
  have h1 : ∀ h : SL(2, ZMod 3), ⁅g, h⁆ = 1 ∨ ⁅g, h⁆ = -1 := fun h =>
    sl23_center _ (fun y => Subgroup.mem_center_iff.mp (hφ (hg h)) y)
  rcases sl23_secondCenter g h1 with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_center_iff.mpr fun y => sl23_neg_central y

theorem oddCoreFree_of_sl23 {P : Type} [Group P] [Finite P] (ψ : SL(2, ZMod 3) →* P)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center SL(2, ZMod 3)) :
    OddCoreFree P := by
  have hkerpm : ∀ x ∈ ψ.ker, x = 1 ∨ x = -1 := fun x hx =>
    sl23_center _ (fun y => Subgroup.mem_center_iff.mp (hker hx) y)
  set V : Subgroup P := sl2ThreeQ.map ψ with hV
  have hVn : V.Normal := sl2ThreeQ_normal.map ψ hψ
  have hV2 : IsPGroup 2 V :=
    (IsPGroup.of_card (n := 3) (by rw [natCard_sl2ThreeQ]; norm_num) : IsPGroup 2 sl2ThreeQ).map ψ
  have hC : Subgroup.centralizer (V : Set P) ≤ V := by
    intro p hp
    obtain ⟨g, rfl⟩ := hψ p
    have h1 : ∀ q : SL(2, ZMod 3), q ^ 4 = 1 → ⁅g, q⁆ = 1 ∨ ⁅g, q⁆ = -1 := by
      intro q hq
      apply hkerpm
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hp (ψ q) ⟨q, mem_sl2ThreeQ_iff.mpr hq, rfl⟩).symm
    exact ⟨g, mem_sl2ThreeQ_iff.mpr (sl23_selfCentralizing g h1), rfl⟩
  intro s hs
  obtain ⟨h, rfl⟩ := hψ s
  have hh2 : h * h ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul]; exact hs
  have hhs : h ^ 4 = 1 := by
    have e : h ^ 4 = (h * h) * (h * h) := by simp [pow_succ, mul_assoc]
    rcases hkerpm _ hh2 with h' | h'
    · rw [e, h', one_mul]
    · rw [e, h', sl23_neg_mul_neg]
  have hs_cent : ψ h ∈ Subgroup.centralizer (V : Set P) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have hqh : ⁅q, h⁆ ∈ ψ.ker := by
      by_cases hneg : (-1 : SL(2, ZMod 3)) ∈ ψ.ker
      · rcases sl23_quaternionComm q h (mem_sl2ThreeQ_iff.mp hq) hhs with h' | h'
        · rw [h']; exact ψ.ker.one_mem
        · rw [h']; exact hneg
      · have hh1 : h * h = 1 := by
          rcases hkerpm _ hh2 with h' | h'
          · exact h'
          · exact absurd (h' ▸ hh2) hneg
        rcases sl23_sq_one h hh1 with h' | h'
        · rw [h']; simp
        · rw [h', commutatorElement_def, sl23_neg_central q]
          group
          exact ψ.ker.one_mem
    rw [MonoidHom.mem_ker, map_commutatorElement] at hqh
    exact commutatorElement_eq_one_iff_mul_comm.mp hqh
  exact oddCoreIn_centralizer_eq_bot_of_normal_isPGroup hVn hV2 hC hs_cent

end SL23

section M11

@[expose] def M11OddCentralizerFree : Prop :=
  ∀ t : ↥CFSG.Blueprint.NativeSporadic.M11, orderOf t = 2 →
    oddCoreIn (Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M11)) = ⊥

theorem center_m11_eq_bot (hM : M11Facts) :
    Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 = ⊥ := by
  obtain ⟨hsimple, hcard⟩ := hM
  have hnab : ∃ a b : ↥CFSG.Blueprint.NativeSporadic.M11, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : Std.Commutative (α := ↥CFSG.Blueprint.NativeSporadic.M11) (· * ·) :=
      ⟨fun a b => hcon a b⟩
    have : IsMulCommutative ↥CFSG.Blueprint.NativeSporadic.M11 := ⟨hcomm⟩
    have hp := IsSimpleGroup.prime_card (α := ↥CFSG.Blueprint.NativeSporadic.M11)
    rw [hcard] at hp
    norm_num at hp
  obtain ⟨a, b, hab⟩ := hnab
  rcases (inferInstance : (Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11).Normal
    ).eq_bot_or_eq_top with h | h
  · exact h
  · exact (hab (Subgroup.mem_center_iff.mp (by rw [h]; trivial : a ∈ _) b).symm).elim

theorem isQuasisimple_m11 (hM : M11Facts) :
    CFSG.Open.IsQuasisimple ↥CFSG.Blueprint.NativeSporadic.M11 := by
  have hcenter := center_m11_eq_bot hM
  obtain ⟨hsimple, hcard⟩ := hM
  have hnab : ∃ a b : ↥CFSG.Blueprint.NativeSporadic.M11, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : Std.Commutative (α := ↥CFSG.Blueprint.NativeSporadic.M11) (· * ·) :=
      ⟨fun a b => hcon a b⟩
    have : IsMulCommutative ↥CFSG.Blueprint.NativeSporadic.M11 := ⟨hcomm⟩
    have hp := IsSimpleGroup.prime_card (α := ↥CFSG.Blueprint.NativeSporadic.M11)
    rw [hcard] at hp
    norm_num at hp
  obtain ⟨a, b, hab⟩ := hnab
  have hcomm : commutator ↥CFSG.Blueprint.NativeSporadic.M11 = ⊤ := by
    rcases (inferInstance : (commutator ↥CFSG.Blueprint.NativeSporadic.M11).Normal
      ).eq_bot_or_eq_top with h | h
    · exfalso
      have h1 : ⁅a, b⁆ ∈ commutator ↥CFSG.Blueprint.NativeSporadic.M11 :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact hab h1
    · exact h
  exact ⟨hcomm, ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩

theorem oddCoreFree_of_m11 (hM : M11Facts) (hM1 : M11OddCentralizerFree) {P : Type} [Group P]
    [Finite P] (ψ : ↥CFSG.Blueprint.NativeSporadic.M11 →* P) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11) : OddCoreFree P := by
  have : Finite ↥CFSG.Blueprint.NativeSporadic.M11 :=
    Nat.finite_of_card_ne_zero (by rw [hM.2]; norm_num)
  have hq := isQuasisimple_m11 hM
  have hbot : ψ.ker = ⊥ := le_bot_iff.mp (by simpa [center_m11_eq_bot hM] using hker)
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hbot
  let e : ↥CFSG.Blueprint.NativeSporadic.M11 ≃* P := MulEquiv.ofBijective ψ ⟨hinj, hψ⟩
  exact OddCoreFree.of_mulEquiv e.symm (oddCoreFree_of_isQuasisimple hq hM1)

end M11

theorem oddCoreFreeInvolutions_map_range (h0 : ModelClauseZero) (h1 : ModelOddCentralizerFree3)
    (hM : M11Facts) (hM1 : M11OddCentralizerFree) {X : Type} [Group X] [Finite X] {c : CompData}
    (hc : c.Valid) (φ : c.G →* X) (hφ : φ.ker ≤ Subgroup.center c.G) :
    OddCoreFreeInvolutions (φ.range.map (QuotientGroup.mk' (Subgroup.center X))) := by
  rw [← MonoidHom.range_comp]
  apply oddCoreFreeInvolutions_of_oddCoreFree
  set ψ := ((QuotientGroup.mk' (Subgroup.center X)).comp φ).rangeRestrict with hψdef
  have hψ : Function.Surjective ψ := MonoidHom.rangeRestrict_surjective _
  have hkerψ : ψ.ker = ((QuotientGroup.mk' (Subgroup.center X)).comp φ).ker :=
    MonoidHom.ker_rangeRestrict _
  rcases hc with ⟨t, n, ht, hadm, rfl⟩ | rfl | rfl
  · have hK := (h0 t n 3 1 Nat.prime_three ht hadm).1
    have : Group.IsPerfect (CompData.model t n).G := ⟨hK.1⟩
    have hker' : ψ.ker ≤ Subgroup.center (CompData.model t n).G := by
      rw [hkerψ]
      exact ker_comp_le_center φ (fun g hg => mem_center_of_commutator_mem hφ hg)
    exact oddCoreFree_of_isQuasisimple (isQuasisimple_of_centralQuotient hK ψ hψ hker')
      (fun s hs => h1 t n Nat.prime_three ht hadm _ ψ hψ hker' s hs)
  · have hker' : ψ.ker ≤ Subgroup.center SL(2, ZMod 3) := by
      rw [hkerψ]
      exact ker_comp_le_center φ (sl23_second_center φ hφ)
    exact oddCoreFree_of_sl23 ψ hψ hker'
  · have hq := isQuasisimple_m11 hM
    have : Group.IsPerfect ↥CFSG.Blueprint.NativeSporadic.M11 := ⟨hq.1⟩
    have hker' : ψ.ker ≤ Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 := by
      rw [hkerψ]
      exact ker_comp_le_center φ (fun g hg => mem_center_of_commutator_mem hφ hg)
    exact oddCoreFree_of_m11 hM hM1 ψ hψ hker'

theorem oddCoreIn_centralizer_eq_bot_of_lieSystemData3 (h0 : ModelClauseZero)
    (h1 : ModelOddCentralizerFree3) (hM : M11Facts) (hM1 : M11OddCentralizerFree) {ι X : Type}
    [Finite ι] [Group X] [Finite X] {Φ : Set (Subgroup X)} (D : LieSystemData3 ι X Φ)
    (hO : oddCoreIn (⊤ : Subgroup X) = ⊥) (x : X) (hx : x * x = 1) :
    oddCoreIn (Subgroup.centralizer ({x} : Set X)) = ⊥ := by
  refine oddCoreIn_centralizer_eq_bot_of_centralProduct (fun i => (D.hom i).range) ?_ D.generate hO
    ?_ x hx
  · rintro i j hij _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact D.commute i j hij u v
  · intro i
    exact oddCoreFreeInvolutions_map_range h0 h1 hM hM1 (D.valid i) (D.hom i)
      (D.ker_le_center i)

theorem lieSystemOddCentralizer3_of_models (h0 : ModelClauseZero) (h1 : ModelOddCentralizerFree3)
    (hM : M11Facts) (hM1 : M11OddCentralizerFree) : LieSystemOddCentralizer3 := by
  intro Y _ _ Λ hΛ a ha
  obtain ⟨ι, hι, ⟨D⟩⟩ := hΛ
  set N := classicalInvolutionOddCore Y with hN
  set π := QuotientGroup.mk' N with hπ
  have hXO : oddCoreIn (⊤ : Subgroup (Y ⧸ N)) = ⊥ := by
    have hS : (oddCoreIn (⊤ : Subgroup (Y ⧸ N))).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (normalizer_oddCoreIn ⊤))
    have h2 := CFSG.ComponentClassification.OddCore.maximal (Y ⧸ N) (oddCoreIn ⊤) hS
      (odd_card_oddCoreIn _)
    have hcf : componentClassificationOddCore (Y ⧸ N) = ⊥ :=
      CFSG.ComponentClassification.OddCore.quotient_corefree Y
    rw [hcf] at h2
    exact le_bot_iff.mp h2
  have hX := fun x (hx : x * x = 1) =>
    oddCoreIn_centralizer_eq_bot_of_lieSystemData3 h0 h1 hM hM1 D hXO x hx
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, sq] at this
  have hπa : π a * π a = 1 := by rw [← map_mul, ha2, map_one]
  have h2 := map_oddCoreIn_le π (centralizer_map_oddCore ha)
  rw [hX (π a) hπa, le_bot_iff] at h2
  intro s hs
  have : π s ∈ (oddCoreIn (Subgroup.centralizer ({a} : Set Y))).map π := ⟨s, hs, rfl⟩
  rw [h2, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff s).mp this

end CFSG.ClassicalInvolution.Q3

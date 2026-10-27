module

public import CFSG.GH74.GLS.Balance.SL23Ext
import CFSG.Walter.AStar.Subnormal
public import CFSG.GH74.GLS.Balance.Defs

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped MatrixGroups commutatorElement

namespace SolvComp

theorem map_pCore_le_pCore_of_isSubnormal {H : Type*} [Group H] (p : ℕ) {K : Subgroup H}
    (hK : K.IsSubnormal) : (pCore p K).map K.subtype ≤ pCore p H := by
  have key : ∀ {X Y : Subgroup H}, X ≤ Y → Y ≤ normalizer (X : Set H) →
      (pCore p X).map X.subtype ≤ (pCore p Y).map Y.subtype := by
    intro X Y hXY hYN
    have hLY : (pCore p X).map X.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hXY
    have hle : ((pCore p X).map X.subtype).subgroupOf Y ≤ pCore p Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using CFSG.Walter.conj_mem_map_of_characteristic (hYN y.2) hl
      · exact ((pCore_isPGroup (p := p) (G := X)).map X.subtype).of_equiv
          (Subgroup.subgroupOfEquivOfLe hLY).symm
    calc (pCore p X).map X.subtype
        = (((pCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (pCore p Y).map Y.subtype := Subgroup.map_mono hle
  induction hK with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => CFSG.Walter.conj_mem_map_of_characteristic ?_ hl⟩,
      (pCore_isPGroup (p := p) (G := (⊤ : Subgroup H))).map _⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  | step X Y hXY hY hN ih =>
    exact (key hXY ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih


section Unpack

variable {X : Type} [Group X] [Finite X]

theorem map_le_pCore_of_isSubnormal {H : Type*} [Group H] {K : Subgroup H} (hK : K.IsSubnormal)
    {U : Subgroup ↥K} [U.Normal] (hU : IsPGroup 2 U) : U.map K.subtype ≤ pCore 2 H :=
  (Subgroup.map_mono (le_sSup ⟨inferInstance, hU⟩ : U ≤ pCore 2 ↥K)).trans
    (map_pCore_le_pCore_of_isSubnormal 2 hK)

theorem exists_ext {C V : Subgroup X} (hV : IsSolvTwoCompSL23In C V) :
    ∃ π : ↥V →* SL(2, ZMod 3), Function.Surjective π ∧ Odd (Nat.card π.ker) ∧
      (∀ v : ↥V, π v = 1 ↔ (v : X) ∈ pPrimeCoreOf 2 C) ∧
      (∀ v : ↥V, π v ^ 4 = 1 → (v : X) ∈ (pPrimePCore 2 ↥C).map C.subtype) := by
  obtain ⟨hVC, W, hWsub, ⟨e⟩, hVW⟩ := hV
  set q : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hq
  let ι : ↥V →* ↥C := Subgroup.inclusion hVC
  have hmem : ∀ v : ↥V, q (ι v) ∈ W := fun v => by
    have : ι v ∈ V.subgroupOf C := v.2
    rw [hVW] at this
    exact this
  let f : ↥V →* ↥W := (q.comp ι).codRestrict W hmem
  let π : ↥V →* SL(2, ZMod 3) := e.toMonoidHom.comp f
  have hπ : ∀ v : ↥V, π v = e (f v) := fun v => rfl
  have hker : ∀ v : ↥V, π v = 1 ↔ (v : X) ∈ pPrimeCoreOf 2 C := by
    intro v
    rw [hπ, e.map_eq_one_iff, Subtype.ext_iff]
    show q (ι v) = 1 ↔ _
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨ι v, h, rfl⟩
    · rintro ⟨c, hc, hcv⟩
      have : c = ι v := Subtype.ext hcv
      rw [← this]
      exact hc
  have hsurj : Function.Surjective π := by
    intro s
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥C) ((e.symm s : ↥W) : ↥C ⧸ pPrimeCore 2 ↥C)
    have hcV : c ∈ V.subgroupOf C := by
      rw [hVW]
      show q c ∈ W
      rw [hq]
      rw [hc]
      exact (e.symm s).2
    refine ⟨⟨c, hcV⟩, ?_⟩
    rw [hπ]
    have : f ⟨c, hcV⟩ = e.symm s := Subtype.ext hc
    rw [this, MulEquiv.apply_symm_apply]
  have hodd : Odd (Nat.card π.ker) := by
    have hker' : ∀ v : π.ker, ι v.1 ∈ pPrimeCore 2 ↥C := by
      intro v
      have h1 := (hker v.1).mp v.2
      obtain ⟨c, hc, hcv⟩ := h1
      have : c = ι v.1 := Subtype.ext hcv
      rw [← this]
      exact hc
    let g : ↥π.ker →* ↥(pPrimeCore 2 ↥C) :=
      (ι.comp π.ker.subtype).codRestrict (pPrimeCore 2 ↥C) hker'
    have hginj : Function.Injective g := by
      intro a b hab
      have : ι a.1 = ι b.1 := congrArg Subtype.val hab
      exact Subtype.ext (Subgroup.inclusion_injective hVC this)
    have hdvd := Subgroup.card_dvd_of_injective g hginj
    have hoddO : Odd (Nat.card (pPrimeCore 2 ↥C)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact Odd.of_dvd_nat hoddO hdvd
  have hQ : ∀ v : ↥V, π v ^ 4 = 1 → (v : X) ∈ (pPrimePCore 2 ↥C).map C.subtype := by
    intro v hv
    set Qw : Subgroup ↥W := SL23.Q8.comap e.toMonoidHom with hQw
    have : Qw.Normal := Subgroup.Normal.comap inferInstance _
    have hQw2 : IsPGroup 2 Qw := by
      intro g
      refine ⟨2, ?_⟩
      apply Subtype.ext
      apply e.injective
      have h4 : e.toMonoidHom g.1 ^ 4 = 1 := g.2
      show e ((g.1) ^ 2 ^ 2) = e 1
      rw [map_pow, map_one]
      exact h4
    have hfv : f v ∈ Qw := by
      show e.toMonoidHom (f v) ∈ SL23.Q8
      exact hv
    have h1 : ((f v : ↥W) : ↥C ⧸ pPrimeCore 2 ↥C) ∈ Qw.map W.subtype := ⟨f v, hfv, rfl⟩
    have h2 := map_le_pCore_of_isSubnormal hWsub hQw2 h1
    refine ⟨ι v, ?_, rfl⟩
    exact h2
  exact ⟨π, hsurj, hodd, hker, hQ⟩


end Unpack

section NoFinite

variable {X : Type} [Group X]

theorem isSubnormal_of_solv {C V : Subgroup X} (hV : IsSolvTwoCompSL23In C V) :
    (V.subgroupOf C).IsSubnormal := by
  obtain ⟨-, W, hWsub, -, hVW⟩ := hV
  rw [hVW]
  exact hWsub.comap _

theorem pPrimeCoreOf_le_of_solv {C V : Subgroup X} (hV : IsSolvTwoCompSL23In C V) :
    pPrimeCoreOf 2 C ≤ V := by
  obtain ⟨-, W, -, -, hVW⟩ := hV
  rintro _ ⟨c, hc, rfl⟩
  have h0 : QuotientGroup.mk' (pPrimeCore 2 ↥C) c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
  have h1 : c ∈ V.subgroupOf C := by
    rw [hVW]
    show QuotientGroup.mk' (pPrimeCore 2 ↥C) c ∈ W
    rw [h0]
    exact one_mem W
  exact h1

theorem pPrimeCoreOf_conj_mem {C : Subgroup X} {c o : X} (hc : c ∈ C) (ho : o ∈ pPrimeCoreOf 2 C) :
    c * o * c⁻¹ ∈ pPrimeCoreOf 2 C := by
  obtain ⟨o', ho', rfl⟩ := ho
  exact ⟨⟨c, hc⟩ * o' * ⟨c, hc⟩⁻¹, Subgroup.Normal.conj_mem inferInstance o' ho' ⟨c, hc⟩, rfl⟩

end NoFinite

section Unpack2

variable {X : Type} [Group X] [Finite X]

theorem odd_orderOf_of_mem_pPrimeCoreOf {C : Subgroup X} {o : X} (ho : o ∈ pPrimeCoreOf 2 C) :
    Odd (orderOf o) := by
  obtain ⟨o', ho', rfl⟩ := ho
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥C)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have h : orderOf (⟨o', ho'⟩ : pPrimeCore 2 ↥C) ∣ Nat.card (pPrimeCore 2 ↥C) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  exact Odd.of_dvd_nat hodd h

theorem eq_one_of_mem_pPrimeCoreOf_of_two_pow {C : Subgroup X} {o : X} (ho : o ∈ pPrimeCoreOf 2 C)
    {k : ℕ} (h : o ^ 2 ^ k = 1) : o = 1 :=
  SL23.eq_one_of_odd_of_two_pow (odd_orderOf_of_mem_pPrimeCoreOf ho) h

end Unpack2

section Normalizer

variable {X : Type} [Group X]

theorem mem_normalizer_map_subtype {K : Subgroup X} {H : Subgroup ↥K} {g : ↥K}
    (hg : g ∈ normalizer (H : Set ↥K)) :
    (g : X) ∈ normalizer ((H.map K.subtype : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨h', hh', rfl⟩
    exact ⟨g * h' * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg h').mp hh', rfl⟩
  · rintro ⟨z, hz, hzeq⟩
    refine ⟨g⁻¹ * z * g, ?_, ?_⟩
    · have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
      exact (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * z * g)).mpr (by rw [e]; exact hz)
    · have : (z : X) = (g : X) * h * (g : X)⁻¹ := hzeq
      show ((g⁻¹ * z * g : ↥K) : X) = h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, this]
      group

theorem map_conj_eq_of_mem_normalizer {A : Subgroup X} {g : X} (hg : g ∈ normalizer (A : Set X)) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    exact (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr (by rw [e]; exact hy)

theorem mem_normalizer_commutator {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((⁅A, B⁆ : Subgroup X) : Set X) := by
  have h : (⁅A, B⁆ : Subgroup X).map (MulAut.conj g).toMonoidHom = ⁅A, B⁆ := by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hA,
      map_conj_eq_of_mem_normalizer hB]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := (MulAut.conj g).injective hzy
    rw [← this]
    exact hz

end Normalizer

end SolvComp

end CFSG.GH74.GLS.Balance

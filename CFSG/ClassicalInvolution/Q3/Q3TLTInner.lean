module

public import CFSG.ClassicalInvolution.Q3.Q3TLT3Fusion
public import CFSG.ClassicalInvolution.Q3.Q3TLTInnerAb
public import CFSG.ClassicalInvolution.Q3.TL3Split

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

section Datum

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

namespace TightDatum

theorem mem_ker_act_iff (d : TightDatum R S t) (y : Subgroup.centralizer ({t} : Set G)) :
    y ∈ d.act.ker ↔ ∀ r ∈ R, ⁅(y : G), r⁆ ∈ oddCoreImg R :=
  d.act_eq_one_iff y.2

theorem nonempty_equiv_q8 (d : TightDatum R S t) {x : Subgroup.centralizer ({t} : Set G)}
    {k : ℕ} (hx : x ^ 3 ^ k = 1) (hx1 : d.act x ≠ 1) :
    Nonempty ((R ⧸ oddCore R) ≃* QuaternionGroup 2) := by
  obtain ⟨e1⟩ := QuaternionStructure.nonempty_mulEquiv_sylow_of_isPGroup_oddCore_quotient
    d.twoGroup S
  have hx3 : (x : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hx
  have hxR : ∃ r ∈ R, ⁅(x : G), r⁆ ∉ oddCoreImg R := by
    by_contra hcon
    push Not at hcon
    exact hx1 ((d.mem_ker_act_iff x).mpr hcon)
  obtain ⟨e2⟩ := tl3_nonempty_mulEquiv_q8 S d.quat d.twoGroup d.le_normalizer x.2 hx3 hxR
  exact ⟨e1.trans e2⟩

theorem act_pow_three_eq_one (d : TightDatum R S t)
    (e : (R ⧸ oddCore R) ≃* QuaternionGroup 2) {x : Subgroup.centralizer ({t} : Set G)}
    {k : ℕ} (hx : x ^ 3 ^ k = 1) : d.act x ^ 3 = 1 :=
  tl3_aut_pow_three_of_pow_three_pow e (by rw [← map_pow, hx, map_one])

theorem not_nine_dvd_natCard_range (d : TightDatum R S t)
    (e : (R ⧸ oddCore R) ≃* QuaternionGroup 2) : ¬ 9 ∣ Nat.card d.act.range := by
  intro h9
  have hA := tl3_natCard_mulAut_le e
  have hI := tl3_natCard_inn e
  have : Finite (MulAut (R ⧸ oddCore R)) :=
    Finite.of_injective (fun f : MulAut (R ⧸ oddCore R) => (f : (R ⧸ oddCore R) → _))
      DFunLike.coe_injective
  have hApos : 0 < Nat.card (MulAut (R ⧸ oddCore R)) := Nat.card_pos
  have h4A : 4 ∣ Nat.card (MulAut (R ⧸ oddCore R)) := by
    have := Subgroup.card_subgroup_dvd_card (MulAut.conj : (R ⧸ oddCore R) →*
      MulAut (R ⧸ oddCore R)).range
    rwa [hI] at this
  have h9A : 9 ∣ Nat.card (MulAut (R ⧸ oddCore R)) :=
    h9.trans (Subgroup.card_subgroup_dvd_card _)
  have h36 : 36 ∣ Nat.card (MulAut (R ⧸ oddCore R)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4A h9A
  have := Nat.le_of_dvd hApos h36
  omega

theorem exists_conj_range (d : TightDatum R S t) (e : (R ⧸ oddCore R) ≃* QuaternionGroup 2) :
    ∀ a ∈ d.act.range, ∀ b ∈ d.act.range, orderOf a = 3 → orderOf b = 3 →
      ∃ g ∈ d.act.range, g * b * g⁻¹ ∈ Subgroup.zpowers a := by
  intro a ha b hb hoa hob
  have hoa' : orderOf (⟨a, ha⟩ : d.act.range) = 3 := by rw [Subgroup.orderOf_mk]; exact hoa
  have hob' : orderOf (⟨b, hb⟩ : d.act.range) = 3 := by rw [Subgroup.orderOf_mk]; exact hob
  obtain ⟨g, hg⟩ := exists_conj_mem_zpowers_of_orderOf_eq_three (d.not_nine_dvd_natCard_range e)
    hoa' hob'
  refine ⟨g, g.2, ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  have := congrArg Subtype.val hn
  simpa using this

end TightDatum

end Datum

section Statements

@[expose] def TightInnerAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
    R ≤ Subgroup.centralizer ({t} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal →
    IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) →
    ∀ (x : G) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set G) → x ^ 3 ^ k = 1 →
      (∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) →
      ∃ d ∈ Subgroup.centralizer ({t} : Set G), (∀ r ∈ R, ⁅d, r⁆ ∈ oddCoreImg R) ∧
        ∀ y ∈ Subgroup.centralizer ({t} : Set G), (∀ r ∈ R, ⁅y, r⁆ ∈ oddCoreImg R) →
          x * y * x⁻¹ * (d * y * d⁻¹)⁻¹ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set G))

end Statements

section Main

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

namespace TightDatum

@[expose] def DiagFree (_d : TightDatum R S t) : Prop :=
  ∀ (x : G) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set G) → x ^ 3 ^ k = 1 →
    (∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) →
    ∃ (x' : G) (k' : ℕ), x' ∈ Subgroup.centralizer ({t} : Set G) ∧ x' ^ 3 ^ k' = 1 ∧
      (∃ r ∈ R, ⁅x', r⁆ ∉ oddCoreImg R) ∧
      ∀ y ∈ Subgroup.centralizer ({t} : Set G), (∀ r ∈ R, ⁅y, r⁆ ∈ oddCoreImg R) →
        ⁅x', y⁆ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set G))

@[expose] def InnerAct (_d : TightDatum R S t) : Prop :=
  ∀ (x : G) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set G) → x ^ 3 ^ k = 1 →
    (∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) →
    ∃ dd ∈ Subgroup.centralizer ({t} : Set G), (∀ r ∈ R, ⁅dd, r⁆ ∈ oddCoreImg R) ∧
      ∀ y ∈ Subgroup.centralizer ({t} : Set G), (∀ r ∈ R, ⁅y, r⁆ ∈ oddCoreImg R) →
        x * y * x⁻¹ * (dd * y * dd⁻¹)⁻¹ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set G))

omit [Finite G] in
theorem commutator_mem_oddCore_iff (x y : Subgroup.centralizer ({t} : Set G)) :
    ⁅x, y⁆ ∈ oddCore (Subgroup.centralizer ({t} : Set G)) ↔
      ⁅(x : G), (y : G)⁆ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set G)) := by
  rw [mem_oddCore_iff_coe_mem_oddCoreImg]
  rfl

omit [Finite G] in
theorem inner_mem_oddCore_iff (x y dd : Subgroup.centralizer ({t} : Set G)) :
    x * y * x⁻¹ * (dd * y * dd⁻¹)⁻¹ ∈ oddCore (Subgroup.centralizer ({t} : Set G)) ↔
      (x : G) * (y : G) * (x : G)⁻¹ * ((dd : G) * (y : G) * (dd : G)⁻¹)⁻¹ ∈
        oddCoreImg (Subgroup.centralizer ({t} : Set G)) := by
  rw [mem_oddCore_iff_coe_mem_oddCoreImg]
  rfl

theorem diagFree_iff_c (d : TightDatum R S t) : d.DiagFree ↔
    ∀ (x : Subgroup.centralizer ({t} : Set G)) (k : ℕ), x ^ 3 ^ k = 1 → d.act x ≠ 1 →
      ∃ (x' : Subgroup.centralizer ({t} : Set G)) (k' : ℕ), x' ^ 3 ^ k' = 1 ∧ d.act x' ≠ 1 ∧
        x' ∈ centModO d.act (oddCore (Subgroup.centralizer ({t} : Set G))) := by
  constructor
  · intro h x k hx hx1
    have hx3 : (x : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hx
    have hxR : ∃ r ∈ R, ⁅(x : G), r⁆ ∉ oddCoreImg R := by
      by_contra hcon
      push Not at hcon
      exact hx1 ((d.mem_ker_act_iff x).mpr hcon)
    obtain ⟨x', k', hx'C, hx'3, hx'R, hW⟩ := h (x : G) k x.2 hx3 hxR
    refine ⟨⟨x', hx'C⟩, k', Subtype.ext (by simpa using hx'3), ?_, ?_⟩
    · intro h1
      obtain ⟨r, hr, hnr⟩ := hx'R
      exact hnr ((d.act_eq_one_iff hx'C).mp h1 r hr)
    · intro y hy
      exact (commutator_mem_oddCore_iff _ _).mpr (hW (y : G) y.2 ((d.mem_ker_act_iff y).mp hy))
  · intro h x k hxC hx3 hxR
    have hx1 : d.act ⟨x, hxC⟩ ≠ 1 := fun h1 => by
      obtain ⟨r, hr, hnr⟩ := hxR
      exact hnr ((d.act_eq_one_iff hxC).mp h1 r hr)
    obtain ⟨x', k', hx', hx'1, hW⟩ := h ⟨x, hxC⟩ k (Subtype.ext (by simpa using hx3)) hx1
    refine ⟨(x' : G), k', x'.2, by simpa using congrArg Subtype.val hx', ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      exact hx'1 ((d.mem_ker_act_iff x').mpr hcon)
    · intro y hyC hy
      exact (commutator_mem_oddCore_iff x' ⟨y, hyC⟩).mp (hW ⟨y, hyC⟩
        ((d.mem_ker_act_iff ⟨y, hyC⟩).mpr hy))

theorem innerAct_iff_c (d : TightDatum R S t) : d.InnerAct ↔
    ∀ (x : Subgroup.centralizer ({t} : Set G)) (k : ℕ), x ^ 3 ^ k = 1 → d.act x ≠ 1 →
      ∃ dd ∈ d.act.ker, ∀ y ∈ d.act.ker, x * y * x⁻¹ * (dd * y * dd⁻¹)⁻¹ ∈
        oddCore (Subgroup.centralizer ({t} : Set G)) := by
  constructor
  · intro h x k hx hx1
    have hx3 : (x : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hx
    have hxR : ∃ r ∈ R, ⁅(x : G), r⁆ ∉ oddCoreImg R := by
      by_contra hcon
      push Not at hcon
      exact hx1 ((d.mem_ker_act_iff x).mpr hcon)
    obtain ⟨dd, hddC, hdd, hy⟩ := h (x : G) k x.2 hx3 hxR
    refine ⟨⟨dd, hddC⟩, (d.mem_ker_act_iff _).mpr hdd, fun y hyk => ?_⟩
    exact (inner_mem_oddCore_iff _ _ _).mpr (hy (y : G) y.2 ((d.mem_ker_act_iff y).mp hyk))
  · intro h x k hxC hx3 hxR
    have hx1 : d.act ⟨x, hxC⟩ ≠ 1 := fun h1 => by
      obtain ⟨r, hr, hnr⟩ := hxR
      exact hnr ((d.act_eq_one_iff hxC).mp h1 r hr)
    obtain ⟨dd, hdd, hy⟩ := h ⟨x, hxC⟩ k (Subtype.ext (by simpa using hx3)) hx1
    refine ⟨(dd : G), dd.2, (d.mem_ker_act_iff dd).mp hdd, fun y hyC hyR => ?_⟩
    exact (inner_mem_oddCore_iff ⟨x, hxC⟩ ⟨y, hyC⟩ dd).mp (hy ⟨y, hyC⟩
      ((d.mem_ker_act_iff ⟨y, hyC⟩).mpr hyR))

theorem td_iff_inner (d : TightDatum R S t) : d.DiagFree ↔ d.InnerAct := by
  set C := Subgroup.centralizer ({t} : Set G) with hC
  have hOn : (oddCore C).Normal := inferInstance
  by_cases hex : ∃ (x : C) (k : ℕ), x ^ 3 ^ k = 1 ∧ d.act x ≠ 1
  · obtain ⟨x₀, k₀, hx₀, hx₀1⟩ := hex
    obtain ⟨e⟩ := d.nonempty_equiv_q8 hx₀ hx₀1
    have key := forall_exists_centModO_iff_forall_exists_inner d.act (oddCore C)
      (fun x k hx => d.act_pow_three_eq_one e hx) (d.exists_conj_range e)
    rw [d.diagFree_iff_c, d.innerAct_iff_c]
    exact key
  · push Not at hex
    have hno : ∀ (x : G) (k : ℕ), x ∈ C → x ^ 3 ^ k = 1 → ¬ ∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R := by
      intro x k hxC hx3 ⟨r, hr, hnr⟩
      exact hnr ((d.act_eq_one_iff hxC).mp (hex ⟨x, hxC⟩ k (Subtype.ext (by simpa using hx3)))
        r hr)
    exact ⟨fun _ x k hxC hx3 hxR => (hno x k hxC hx3 hxR).elim,
      fun _ x k hxC hx3 hxR => (hno x k hxC hx3 hxR).elim⟩

end TightDatum

end Main

theorem tightDiagonalFree_iff_tightInnerAction : TightDiagonalFree ↔ TightInnerAction := by
  constructor
  · intro h G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2 x k hxC hx3 hxR
    have hd : TightDatum R S t := ⟨hS, ht, hto, hRC, hRn, h2⟩
    exact (hd.td_iff_inner.mp (h G hnab hlarge R S hS t ht hto hRC hRn h2)) x k hxC hx3 hxR
  · intro h G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2
    have hd : TightDatum R S t := ⟨hS, ht, hto, hRC, hRn, h2⟩
    exact hd.td_iff_inner.mpr (h G hnab hlarge R S hS t ht hto hRC hRn h2)

end CFSG.ClassicalInvolution.Q3

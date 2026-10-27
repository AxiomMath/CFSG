module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightFamily

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement MatrixGroups

namespace Fam

section Clauses

variable {Y : Type} [Group Y]

structure Clauses (Λ : Set (Subgroup Y)) : Prop where
  omega1 : ∀ K ∈ Λ, (∃ z : Y, IsUniqueInvolution K z) ∧
    ∃ P : Subgroup Y, IsSylow2In P K ∧ ¬ IsMulCommutative ↥P
  omega2 : ∀ K ∈ Λ, Subgroup.closure {x : Y | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} = K ∨
    Nonempty (↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, ZMod 3))
  omega3 : ∀ K ∈ Λ, ∀ J ∈ Λ, ∀ P Q : Subgroup Y, IsSylow2In P K → IsSylow2In Q J →
    Nat.card ↥P = Nat.card ↥Q
  omega4 : ∀ K ∈ Λ, ∀ J ∈ Λ, K ≠ J →
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J)
  omega5 : ∀ K ∈ Λ, ∀ J ∈ Λ, K ≠ J → ∀ z : Y, IsUniqueInvolution K z → ∀ v ∈ J,
    (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
      v ∈ Subgroup.normalizer (K : Set Y)

theorem Clauses.mono {Λ Λ' : Set (Subgroup Y)} (h : Clauses Λ) (hΛ : Λ' ⊆ Λ) : Clauses Λ' :=
  ⟨fun K hK => h.omega1 K (hΛ hK), fun K hK => h.omega2 K (hΛ hK),
    fun K hK J hJ => h.omega3 K (hΛ hK) J (hΛ hJ),
    fun K hK J hJ => h.omega4 K (hΛ hK) J (hΛ hJ),
    fun K hK J hJ => h.omega5 K (hΛ hK) J (hΛ hJ)⟩

theorem Clauses.hypOmegaGen {Λ : Set (Subgroup Y)} (h : Clauses Λ) (hc : ConjInvariant Λ) :
    HypOmegaGen Λ :=
  ⟨hc, h.omega1, h.omega2, h.omega3, h.omega4, h.omega5⟩

theorem Clauses.restrict [Finite Y] {Λ : Set (Subgroup Y)} (hΛ : Clauses Λ) (X : Subgroup Y) :
    Clauses (restrictFamily Λ X) where
  omega1 := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    obtain ⟨⟨z, hz⟩, P, hP, hPnc⟩ := hΛ.omega1 L hL
    refine ⟨⟨_, isUniqueInvolution_subgroupOf hz hLX⟩, P.subgroupOf X, hP.subgroupOf hLX, ?_⟩
    intro hc
    apply hPnc
    let e : P.subgroupOf X ≃* P := Subgroup.subgroupOfEquivOfLe (hP.1.trans hLX)
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 : e.symm a * e.symm b = e.symm b * e.symm a := hc.is_comm.comm _ _
    have h2 := congrArg e h1
    simpa using h2
  omega2 := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    rcases hΛ.omega2 L hL with h | h
    · left
      apply Subgroup.map_injective X.subtype_injective
      rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le hLX]
      conv_rhs => rw [← h]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.mem_subgroupOf, Subgroup.coe_subtype]
      constructor
      · rintro ⟨x, ⟨hxL, hx2⟩, rfl⟩
        exact ⟨hxL, isPGroup_zpowers_coe_iff.mpr hx2⟩
      · rintro ⟨hyL, hy2⟩
        exact ⟨⟨y, hLX hyL⟩, ⟨hyL, isPGroup_zpowers_coe_iff.mp hy2⟩, rfl⟩
    · right
      obtain ⟨e⟩ := h
      let φ : L.subgroupOf X ≃* L := Subgroup.subgroupOfEquivOfLe hLX
      exact ⟨(QuotientGroup.congr _ _ φ
        (CFSG.ComponentClassification.OddCore.equiv_invariant φ)).trans e⟩
  omega3 := by
    rintro _ ⟨K, hK, hKX, rfl⟩ _ ⟨J, hJ, hJX, rfl⟩ P Q hP hQ
    have hP' : IsSylow2In (P.map X.subtype) K := by
      have := isSylow2In_map_subtype_iff.mpr hP
      rwa [Subgroup.map_subgroupOf_eq_of_le hKX] at this
    have hQ' : IsSylow2In (Q.map X.subtype) J := by
      have := isSylow2In_map_subtype_iff.mpr hQ
      rwa [Subgroup.map_subgroupOf_eq_of_le hJX] at this
    have h := hΛ.omega3 K hK J hJ _ _ hP' hQ'
    rwa [Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.card_map_of_injective X.subtype_injective] at h
  omega4 := by
    rintro _ ⟨K, hK, hKX, rfl⟩ _ ⟨J, hJ, hJX, rfl⟩ hne
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := hΛ.omega4 K hK J hJ hKJ
    have hcard : Nat.card ↥(K.subgroupOf X ⊓ J.subgroupOf X) = Nat.card ↥(K ⊓ J) := by
      rw [inf_subgroupOf_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKX)).toEquiv
    rw [hcard]
    refine ⟨h1, fun h => ?_⟩
    have hle := h2 h
    rw [oddCoreOf_subgroupOf hKX, oddCoreOf_subgroupOf hJX]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hab : (⁅(a : Y), (b : Y)⁆) ∈ ⁅K, J⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb)
    exact ⟨Subgroup.mem_subgroupOf.mpr (hle hab).1, Subgroup.mem_subgroupOf.mpr (hle hab).2⟩
  omega5 := by
    rintro _ ⟨K, hK, hKX, rfl⟩ _ ⟨J, hJ, hJX, rfl⟩ hne z' hz' v hv hnc hv2 hvz
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    have hzK : IsUniqueInvolution K (z' : Y) := isUniqueInvolution_of_subgroupOf hz' hKX
    have hvJ : (v : Y) ∈ J := Subgroup.mem_subgroupOf.mp hv
    have hnc' : ¬ ∀ w ∈ J, (v : Y) * w = w * (v : Y) := by
      intro h
      apply hnc
      rintro ⟨w, hw⟩ hw'
      exact Subtype.ext (h w (Subgroup.mem_subgroupOf.mp hw'))
    have hv2' : IsPGroup 2 (Subgroup.zpowers (v : Y)) := isPGroup_zpowers_coe_iff.mpr hv2
    have hn := hΛ.omega5 K hK J hJ hKJ (z' : Y) hzK (v : Y) hvJ hnc' hv2'
      (congrArg Subtype.val hvz)
    exact (mem_normalizer_subgroupOf_iff hKX).mp hn

end Clauses

section Section

variable {Y : Type} [Group Y] [Finite Y]

theorem natCard_eq_of_isSylow2In {P Q L : Subgroup Y} (hP : IsSylow2In P L) (hQ : IsSylow2In Q L) :
    Nat.card ↥Q = Nat.card ↥P := by
  obtain ⟨x, -, hx⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hP hQ
  rw [← hx, AscL62.natCard_conjSub]

theorem exists_involution_of_nonabelian {P : Subgroup Y} (hP : IsPGroup 2 ↥P)
    (hnc : ¬ IsMulCommutative ↥P) : ∃ w ∈ P, w ≠ 1 ∧ w * w = 1 := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hnc
    have : Subsingleton ↥P := Nat.card_eq_one_iff_unique.mp (by simpa using hn) |>.1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  have h2 : 2 ∣ Nat.card ↥P := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 h2
  refine ⟨(w : Y), w.2, ?_, ?_⟩
  · intro h1
    have : orderOf (w : Y) = 1 := by rw [h1, orderOf_one]
    rw [Subgroup.orderOf_coe, hw] at this
    exact absurd this (by norm_num)
  · have := pow_orderOf_eq_one (w : Y)
    rwa [Subgroup.orderOf_coe, hw, pow_two] at this

theorem isMulCommutative_of_conjSub {P : Subgroup Y} (x : Y)
    (h : IsMulCommutative ↥(conjSub x P)) : IsMulCommutative ↥P := by
  refine ⟨⟨fun a b => ?_⟩⟩
  have ha : x * (a : Y) * x⁻¹ ∈ conjSub x P := conj_mem_conjSub a.2
  have hb : x * (b : Y) * x⁻¹ ∈ conjSub x P := conj_mem_conjSub b.2
  have := h.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩
  have h2 : x * (a : Y) * x⁻¹ * (x * (b : Y) * x⁻¹) = x * (b : Y) * x⁻¹ * (x * (a : Y) * x⁻¹) :=
    congrArg Subtype.val this
  apply Subtype.ext
  have h3 : x * ((a : Y) * b) * x⁻¹ = x * ((b : Y) * a) * x⁻¹ := by
    calc x * ((a : Y) * b) * x⁻¹ = x * (a : Y) * x⁻¹ * (x * (b : Y) * x⁻¹) := by group
      _ = x * (b : Y) * x⁻¹ * (x * (a : Y) * x⁻¹) := h2
      _ = x * ((b : Y) * a) * x⁻¹ := by group
  have := mul_left_cancel (mul_right_cancel h3)
  exact this

theorem member_data {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) {J : Subgroup Y} (hJ : J ∈ Ω)
    {C P : Subgroup Y} (hP : IsSylow2In P J) (hPC : P ≤ C) :
    ∃ z : Y, IsUniqueInvolution J z ∧ z ∈ tightCore (J ⊓ C) ∧
      IsSylow2In P (tightCore (J ⊓ C)) ∧ ¬ IsMulCommutative ↥P := by
  obtain ⟨⟨z, hz⟩, P', hP', hnc'⟩ := hΩ.omega1 J hJ
  obtain ⟨x, -, hx⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hP' hP
  have hnc : ¬ IsMulCommutative ↥P := by
    intro h
    rw [← hx] at h
    exact hnc' (isMulCommutative_of_conjSub x h)
  have hPle : P ≤ tightCore (J ⊓ C) := le_tightCore_of_isPGroup (le_inf hP.1 hPC) hP.2.1
  refine ⟨z, hz, ?_, ⟨hPle, hP.2.1, fun V' hV' h2 hle =>
    hP.2.2 V' (hV'.trans ((tightCore_le _).trans inf_le_left)) h2 hle⟩, hnc⟩
  obtain ⟨w, hwP, hw1, hw2⟩ := exists_involution_of_nonabelian hP.2.1 hnc
  have hwz : w = z := (hz.unique w (hP.1 hwP) hw2).resolve_left hw1
  exact hwz ▸ hPle hwP

theorem tightCore_inf_le_normalizer {J₁ J₂ : Subgroup Y} (C : Subgroup Y) (h : ⁅J₂, J₁⁆ ≤ J₁) :
    tightCore (J₂ ⊓ C) ≤ Subgroup.normalizer (tightCore (J₁ ⊓ C) : Set Y) := by
  intro b hb
  have hb' : b ∈ J₂ ⊓ C := tightCore_le _ hb
  refine mem_normalizer_of_conjSub_eq (conjSub_tightCore_of_mem_normalizer ?_)
  have key : J₂ ⊓ C ≤ Subgroup.normalizer ((J₁ ⊓ C : Subgroup Y) : Set Y) := by
    refine le_normalizer_of_conj_mem fun m hm x hx => ⟨?_, ?_⟩
    · have hc : m * x * m⁻¹ = ⁅m, x⁆ * x := by rw [commutatorElement_def]; group
      rw [hc]
      exact J₁.mul_mem (h (Subgroup.commutator_mem_commutator hm.1 hx.1)) hx.1
    · exact C.mul_mem (C.mul_mem hm.2 hx.2) (C.inv_mem hm.2)
  exact key hb'

def secFamily (Ω : Set (Subgroup Y)) (C : Subgroup Y) : Set (Subgroup Y) :=
  {L | ∃ J ∈ Ω, (∃ P : Subgroup Y, IsSylow2In P J ∧ P ≤ C) ∧ L = tightCore (J ⊓ C)}

theorem clauses_secFamily {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) (C : Subgroup Y) :
    Clauses (secFamily Ω C) where
  omega1 := by
    rintro _ ⟨J, hJ, ⟨P, hP, hPC⟩, rfl⟩
    obtain ⟨z, hz, hzm, hS, hnc⟩ := member_data hΩ hJ hP hPC
    exact ⟨⟨z, isUniqueInvolution_mono hz ((tightCore_le _).trans inf_le_left) hzm⟩, P, hS, hnc⟩
  omega2 := by
    rintro _ ⟨J, hJ, -, rfl⟩
    exact Or.inl (tightCore_tightCore _)
  omega3 := by
    rintro _ ⟨J₁, hJ₁, ⟨P₁, hP₁, hP₁C⟩, rfl⟩ _ ⟨J₂, hJ₂, ⟨P₂, hP₂, hP₂C⟩, rfl⟩ Q Q' hQ hQ'
    obtain ⟨-, -, -, hS₁, -⟩ := member_data hΩ hJ₁ hP₁ hP₁C
    obtain ⟨-, -, -, hS₂, -⟩ := member_data hΩ hJ₂ hP₂ hP₂C
    rw [natCard_eq_of_isSylow2In hS₁ hQ, natCard_eq_of_isSylow2In hS₂ hQ']
    exact hΩ.omega3 J₁ hJ₁ J₂ hJ₂ P₁ P₂ hP₁ hP₂
  omega4 := by
    rintro _ ⟨J₁, hJ₁, ⟨P₁, hP₁, hP₁C⟩, rfl⟩ _ ⟨J₂, hJ₂, ⟨P₂, hP₂, hP₂C⟩, rfl⟩ hne
    have hJJ : J₁ ≠ J₂ := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := hΩ.omega4 J₁ hJ₁ J₂ hJ₂ hJJ
    have hle₁ : tightCore (J₁ ⊓ C) ≤ J₁ := (tightCore_le _).trans inf_le_left
    have hle₂ : tightCore (J₂ ⊓ C) ≤ J₂ := (tightCore_le _).trans inf_le_left
    have hle : tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C) ≤ J₁ ⊓ J₂ := inf_le_inf hle₁ hle₂
    have hdvd : Nat.card ↥(tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C)) ∣ Nat.card ↥(J₁ ⊓ J₂) :=
      Subgroup.card_dvd_of_le hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpos' : Nat.card ↥(J₁ ⊓ J₂) ≠ 0 := Nat.card_pos.ne'
    have hval : padicValNat 2 (Nat.card ↥(tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C))) ≤
        padicValNat 2 (Nat.card ↥(J₁ ⊓ J₂)) := by
      rw [← padicValNat_dvd_iff_le hpos']
      exact (pow_padicValNat_dvd).trans hdvd
    refine ⟨hval.trans h1, fun heq => ?_⟩
    have h2dvd : 2 ∣ Nat.card ↥(tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C)) :=
      dvd_of_one_le_padicValNat heq.ge
    have hJJ1 : padicValNat 2 (Nat.card ↥(J₁ ⊓ J₂)) = 1 :=
      le_antisymm h1 (one_le_padicValNat_of_dvd hpos' (h2dvd.trans hdvd))
    have hcomm := h2 hJJ1
    have hc12 : ⁅J₁, J₂⁆ ≤ J₂ := hcomm.trans (inf_le_right.trans (oddCoreOf_le_self J₂))
    have hc21 : ⁅J₂, J₁⁆ ≤ J₁ := by
      rw [Subgroup.commutator_comm]
      exact hcomm.trans (inf_le_left.trans (oddCoreOf_le_self J₁))
    have hN1 : tightCore (J₂ ⊓ C) ≤ Subgroup.normalizer (tightCore (J₁ ⊓ C) : Set Y) :=
      tightCore_inf_le_normalizer C hc21
    have hN2 : tightCore (J₁ ⊓ C) ≤ Subgroup.normalizer (tightCore (J₂ ⊓ C) : Set Y) :=
      tightCore_inf_le_normalizer C hc12
    have hcR : ⁅tightCore (J₁ ⊓ C), tightCore (J₂ ⊓ C)⁆ ≤
        tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · have hb' : b * a⁻¹ * b⁻¹ ∈ tightCore (J₁ ⊓ C) :=
          (Subgroup.mem_normalizer_iff.mp (hN1 hb) a⁻¹).mp (Subgroup.inv_mem _ ha)
        have := Subgroup.mul_mem _ ha hb'
        simpa [mul_assoc] using this
      · have ha' : a * b * a⁻¹ ∈ tightCore (J₂ ⊓ C) :=
          (Subgroup.mem_normalizer_iff.mp (hN2 ha) b).mp hb
        exact Subgroup.mul_mem _ ha' (Subgroup.inv_mem _ hb)
    have hcJ : ⁅tightCore (J₁ ⊓ C), tightCore (J₂ ⊓ C)⁆ ≤ oddCoreOf J₁ ⊓ oddCoreOf J₂ :=
      (Subgroup.commutator_mono hle₁ hle₂).trans hcomm
    have hRo : ⁅tightCore (J₁ ⊓ C), tightCore (J₂ ⊓ C)⁆ ≤ oddCoreOf (tightCore (J₁ ⊓ C)) :=
      (le_inf (hcR.trans inf_le_left) (hcJ.trans inf_le_left)).trans (inf_oddCoreOf_le hle₁)
    have hRo' : ⁅tightCore (J₁ ⊓ C), tightCore (J₂ ⊓ C)⁆ ≤ oddCoreOf (tightCore (J₂ ⊓ C)) :=
      (le_inf (hcR.trans inf_le_right) (hcJ.trans inf_le_right)).trans (inf_oddCoreOf_le hle₂)
    exact le_inf hRo hRo'
  omega5 := by
    rintro _ ⟨J₁, hJ₁, ⟨P₁, hP₁, hP₁C⟩, rfl⟩ _ ⟨J₂, hJ₂, ⟨P₂, hP₂, hP₂C⟩, rfl⟩ hne z hz v hv hnc hv2 hvz
    have hJJ : J₁ ≠ J₂ := fun h => hne (by rw [h])
    obtain ⟨z₀, hz₀, hz₀m, -, -⟩ := member_data hΩ hJ₁ hP₁ hP₁C
    have hle₁ : tightCore (J₁ ⊓ C) ≤ J₁ := (tightCore_le _).trans inf_le_left
    have hzz : z = z₀ := hz.eq (isUniqueInvolution_mono hz₀ hle₁ hz₀m)
    subst hzz
    have hvJ₂C : v ∈ J₂ ⊓ C := tightCore_le _ hv
    have hnc' : ¬ ∀ w ∈ J₂, v * w = w * v := fun h =>
      hnc fun w hw => h w (((tightCore_le _).trans inf_le_left) hw)
    have hn := hΩ.omega5 J₁ hJ₁ J₂ hJ₂ hJJ z hz₀ v hvJ₂C.1 hnc' hv2 hvz
    have hvC : v ∈ C := hvJ₂C.2
    have hconj : conjSub v (J₁ ⊓ C) = J₁ ⊓ C := by
      rw [conjSub_inf, tl3_conjSub_eq_of_mem_normalizer hn, conjSub_eq_self_of_mem hvC]
    exact mem_normalizer_of_conjSub_eq
      (conjSub_tightCore_of_mem_normalizer (mem_normalizer_of_conjSub_eq hconj))

end Section

end Fam

section Main

variable {Y : Type} [Group Y] [Finite Y]

theorem hypOmegaGen_sectionFamily {K₀ : Subgroup Y}
    (hΩ : HypOmegaGen (CoreAssembly.conjClass K₀)) {C : Subgroup Y} {H : Subgroup ↥C}
    (hP : ∃ P : Subgroup Y, IsSylow2In P K₀ ∧ P ≤ C)
    (hH : tightCore (K₀.subgroupOf C) ≤ H) :
    HypOmegaGen (CoreAssembly.conjClass ((tightCore (K₀.subgroupOf C)).subgroupOf H)) := by
  obtain ⟨P, hP, hPC⟩ := hP
  have hcl := ((Fam.clauses_secFamily hΩ C).restrict C).restrict H
  refine (hcl.mono ?_).hypOmegaGen ?_
  · rintro _ ⟨h, rfl⟩
    have hcC : ((h : ↥C) : Y) ∈ C := (h : ↥C).2
    have hPc : conjSub ((h : ↥C) : Y) P ≤ C := by
      have := conjSub_mono (n := ((h : ↥C) : Y)) hPC
      rwa [conjSub_eq_self_of_mem hcC] at this
    have hL₀ : tightCore (conjSub ((h : ↥C) : Y) K₀ ⊓ C) ∈ Fam.secFamily
        (CoreAssembly.conjClass K₀) C :=
      ⟨conjSub ((h : ↥C) : Y) K₀, ⟨_, rfl⟩, ⟨_, hP.conj _, hPc⟩, rfl⟩
    have hL₀C : tightCore (conjSub ((h : ↥C) : Y) K₀ ⊓ C) ≤ C := (tightCore_le _).trans inf_le_right
    have e1 : conjSub (h : ↥C) (tightCore (K₀.subgroupOf C)) =
        (tightCore (conjSub ((h : ↥C) : Y) K₀ ⊓ C)).subgroupOf C := by
      rw [conjSub_tightCore, conjSub_subgroupOf]
      have : (conjSub ((h : ↥C) : Y) K₀).subgroupOf C =
          (conjSub ((h : ↥C) : Y) K₀ ⊓ C).subgroupOf C := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      rw [this, tightCore_subgroupOf inf_le_right]
    have hle : conjSub (h : ↥C) (tightCore (K₀.subgroupOf C)) ≤ H := by
      have := conjSub_mono (n := (h : ↥C)) hH
      rwa [conjSub_eq_self_of_mem h.2] at this
    refine ⟨conjSub (h : ↥C) (tightCore (K₀.subgroupOf C)),
      ⟨_, hL₀, hL₀C, e1⟩, hle, ?_⟩
    exact conjSub_subgroupOf H h _
  · rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, by simp only [conjSub_mul]⟩

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge

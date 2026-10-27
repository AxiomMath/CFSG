module

public import CFSG.ClassicalInvolution.Asc77.AscE187Sq

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

abbrev TwC (t : G) : Subgroup G := Subgroup.centralizer ({t} : Set G)

abbrev TwQ (t : G) : Type := ↥(TwC t) ⧸ classicalInvolutionOddCore ↥(TwC t)

@[expose] def twMk (t : G) : ↥(TwC t) →* TwQ t := QuotientGroup.mk' _

@[expose] def twImage (t : G) (M : Subgroup G) : Subgroup (TwQ t) :=
  (M.subgroupOf (TwC t)).map (twMk t)

@[expose] def twFamily (Ω : Set (Subgroup G)) (t : G) : Set (Subgroup (TwQ t)) :=
  {L | ∃ M ∈ Ω, IsUniqueInvolution M t ∧ L = twImage t M}

theorem mem_TwC_iff {t g : G} : g ∈ TwC t ↔ g * t = t * g :=
  Subgroup.mem_centralizer_singleton_iff

theorem t_mem_TwC (t : G) : t ∈ TwC t := mem_TwC_iff.mpr rfl

@[expose] def twT (t : G) : TwQ t := twMk t ⟨t, t_mem_TwC t⟩

theorem twMk_eq_one_iff (t : G) (c : ↥(TwC t)) :
    twMk t c = 1 ↔ c ∈ classicalInvolutionOddCore ↥(TwC t) :=
  QuotientGroup.eq_one_iff c

theorem twMk_surjective (t : G) : Function.Surjective (twMk t) :=
  QuotientGroup.mk'_surjective _

theorem twMk_comm (t : G) (c : ↥(TwC t)) : twMk t c * twT t = twT t * twMk t c := by
  rw [twT, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact mem_TwC_iff.mp c.2

theorem twT_mem_center (t : G) : twT t ∈ Subgroup.center (TwQ t) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨c, rfl⟩ := twMk_surjective t g
  exact twMk_comm t c

theorem centralizer_twT (t : G) : Subgroup.centralizer ({twT t} : Set (TwQ t)) = ⊤ := by
  rw [Subgroup.centralizer_eq_top_iff_subset]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact twT_mem_center t

theorem le_TwC_of_isUniqueInvolution {t : G} {M : Subgroup G} (h : IsUniqueInvolution M t) :
    M ≤ TwC t := fun _ hw => mem_TwC_iff.mpr (h.commute_of_mem hw).symm

section Finite

variable [Finite G]

theorem not_mem_oddCore_of_sq {t : G} (c : ↥(TwC t)) (hc2 : c * c = 1) (hc1 : c ≠ 1) :
    c ∉ classicalInvolutionOddCore ↥(TwC t) := fun hmem =>
  hc1 (eq_one_of_isPGroup_of_mem_odd (CFSG.ComponentClassification.OddCore.odd_card ↥(TwC t)) hmem
    (isPGroup_zpowers_of_mul_self_eq_one hc2 hc1))

theorem twT_ne_one {t : G} (ht : t * t = 1) (ht1 : t ≠ 1) : twT t ≠ 1 := fun h =>
  not_mem_oddCore_of_sq (t := t) ⟨t, t_mem_TwC t⟩ (Subtype.ext ht)
    (fun h' => ht1 (congrArg Subtype.val h')) ((twMk_eq_one_iff t _).mp h)

omit [Finite G] in
theorem twT_sq (t : G) (ht : t * t = 1) : twT t * twT t = 1 := by
  have h : (⟨t, t_mem_TwC t⟩ : ↥(TwC t)) * ⟨t, t_mem_TwC t⟩ = 1 := Subtype.ext ht
  rw [twT, ← map_mul, h, map_one]

omit [Finite G] in
theorem isClassicalMember_of_twin (hΩ : HypOmegaMod p f Ω) {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) : IsClassicalMember p f M t := by
  obtain ⟨z', hz'⟩ := hΩ.classical M hM
  have hzsq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'.orderOf_eq_two, pow_two] at this
  have hzne : z' ≠ 1 := by
    intro h
    have := hz'.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  obtain rfl : z' = t := (hMt.unique z' hz'.mem hzsq).resolve_left hzne
  exact hz'

theorem E187C.exists_twHom_of {M : Subgroup G} {t : G} (hMt : IsUniqueInvolution M t)
    (hsub : IsSubnormal M (Subgroup.centralizer ({t} : Set G))) :
    ∃ ψ : ↥M →* ↥(twImage t M), Function.Surjective ψ ∧
      ψ.ker = classicalInvolutionOddCore ↥M ∧
      ∀ x : ↥M, ((ψ x : ↥(twImage t M)) : TwQ t) =
        twMk t ⟨(x : G), le_TwC_of_isUniqueInvolution hMt x.2⟩ := by
  have hMC : M ≤ TwC t := le_TwC_of_isUniqueInvolution hMt
  let ψ : ↥M →* ↥(twImage t M) :=
    ((twMk t).comp (Subgroup.inclusion hMC)).codRestrict (twImage t M)
      fun x => ⟨Subgroup.inclusion hMC x, x.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨(a : G), ha⟩, rfl⟩
  have hψker : ψ.ker = classicalInvolutionOddCore ↥M := by
    ext x
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    have h1 := CFSG.ComponentClassification.OddCore.subnormal_mem_iff hsub (x : G) x.2
    have h2 : (twMk t (Subgroup.inclusion hMC x) = 1) ↔
        (Subgroup.inclusion hMC x) ∈ classicalInvolutionOddCore ↥(TwC t) :=
      twMk_eq_one_iff t _
    constructor
    · intro h
      refine h1.mpr ⟨hMC x.2, ?_⟩
      exact h2.mp h
    · intro h
      obtain ⟨hup, h3⟩ := h1.mp h
      exact h2.mpr h3
  exact ⟨ψ, hψs, hψker, fun x => rfl⟩

theorem exists_twHom (hΩ : HypOmegaMod p f Ω) {M : Subgroup G} {t : G} (hM : M ∈ Ω)
    (hMt : IsUniqueInvolution M t) :
    ∃ ψ : ↥M →* ↥(twImage t M), Function.Surjective ψ ∧
      ψ.ker = classicalInvolutionOddCore ↥M ∧
      ∀ x : ↥M, ((ψ x : ↥(twImage t M)) : TwQ t) =
        twMk t ⟨(x : G), le_TwC_of_isUniqueInvolution hMt x.2⟩ :=
  E187C.exists_twHom_of hMt (isClassicalMember_of_twin hΩ hM hMt).subnormal

theorem nonempty_equiv_sl2_twImage (hΩ : HypOmegaMod p f Ω) {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) :
    Nonempty (↥(twImage t M) ≃* SL(2, GaloisField p f)) := by
  obtain ⟨ψ, hψs, hψker, -⟩ := exists_twHom hΩ hM hMt
  obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hM
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hψker)).trans e⟩

omit [Finite G] in
theorem isSubnormal_twImage (hΩ : HypOmegaMod p f Ω) {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) : IsSubnormal (twImage t M) ⊤ := by
  have hMC : M ≤ TwC t := le_TwC_of_isUniqueInvolution hMt
  have hz' := isClassicalMember_of_twin hΩ hM hMt
  have h1 : IsSubnormal (M.subgroupOf (TwC t)) ⊤ :=
    (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hMC).mpr hz'.subnormal
  have h2 := CFSG.ComponentClassification.Components.chain_map (twMk t) h1
  rwa [Subgroup.map_top, MonoidHom.range_eq_top.mpr (twMk_surjective t)] at h2

theorem isUniqueInvolution_twImage {M : Subgroup G} {t : G} (hMt : IsUniqueInvolution M t) :
    IsUniqueInvolution (twImage t M) (twT t) := by
  have h1 : IsUniqueInvolution (M.subgroupOf (TwC t)) (⟨t, t_mem_TwC t⟩ : ↥(TwC t)) :=
    ⟨hMt.mem, fun h => hMt.ne_one (congrArg Subtype.val h), Subtype.ext hMt.sq,
      fun y hy hy2 => by
        rcases hMt.unique (y : G) hy (congrArg Subtype.val hy2) with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)⟩
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥(TwC t) ⊓ M.subgroupOf (TwC t))) :=
    (CFSG.ComponentClassification.OddCore.odd_card ↥(TwC t)).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_left)
  exact isUniqueInvolution_map_mk_of_odd hodd h1

theorem mem_oddCore_of_coe_mem_oddCoreOf (hΩ : HypOmegaMod p f Ω) {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) {x : ↥(TwC t)} (hx : (x : G) ∈ oddCoreOf M) :
    x ∈ classicalInvolutionOddCore ↥(TwC t) := by
  obtain ⟨h, hxN⟩ := mem_oddCoreOf_iff.mp hx
  obtain ⟨_, h'⟩ := (CFSG.ComponentClassification.OddCore.subnormal_mem_iff
    (isClassicalMember_of_twin hΩ hM hMt).subnormal (x : G) h).mp hxN
  exact h'

theorem commutes_twImage (hΩ : HypOmegaMod p f Ω) {M J : Subgroup G} {t : G} (hM : M ∈ Ω)
    (hJ : J ∈ Ω) (hMJ : M ≠ J) (hMt : IsUniqueInvolution M t) (hJt : IsUniqueInvolution J t) :
    Commutes (twImage t M) (twImage t J) := by
  have hc := hΩ.comm_le_oddCore_of_twin hM hJ hMJ hMt hJt
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have ha' : (a : G) ∈ M := Subgroup.mem_subgroupOf.mp ha
  have hb' : (b : G) ∈ J := Subgroup.mem_subgroupOf.mp hb
  have h1 : ((⁅a, b⁆ : ↥(TwC t)) : G) ∈ oddCoreOf M :=
    (hc (Subgroup.commutator_mem_commutator ha' hb')).1
  have h2 : twMk t ⁅a, b⁆ = 1 :=
    (twMk_eq_one_iff t _).mpr (mem_oddCore_of_coe_mem_oddCoreOf hΩ hM hMt h1)
  rw [map_commutatorElement] at h2
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

omit [Finite G] in
theorem twImage_conj (t : G) (M : Subgroup G) (c : ↥(TwC t)) :
    conjSub (twMk t c) (twImage t M) = twImage t (conjSub (c : G) M) := by
  ext y
  rw [mem_conjSub_iff]
  constructor
  · rintro ⟨m, hm, hmy⟩
    have hm' : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
    refine ⟨c * m * c⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (conj_mem_conjSub hm')
    · rw [map_mul, map_mul, map_inv, hmy]
      group
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ conjSub (c : G) M := Subgroup.mem_subgroupOf.mp hx
    rw [mem_conjSub_iff] at hx'
    refine ⟨c⁻¹ * x * c, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hx'
    · rw [map_mul, map_mul, map_inv]

omit [Finite G] in
theorem conjInvariant_twFamily (hΩ : HypOmegaMod p f Ω) (t : G) : ConjInvariant (twFamily Ω t) := by
  rintro n L ⟨M, hM, hMt, rfl⟩
  obtain ⟨c, rfl⟩ := twMk_surjective t n
  rw [twImage_conj]
  refine ⟨conjSub (c : G) M, hΩ.conjInvariant _ M hM, ?_, rfl⟩
  have hct : (c : G) * t * (c : G)⁻¹ = t := by
    rw [mem_TwC_iff.mp c.2]
    group
  have := hMt.conj (c : G)
  rwa [hct] at this

theorem HypOmega.of_commuting {Y : Type} [Group Y] [Finite Y] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Λ : Set (Subgroup Y)} (hconj : ConjInvariant Λ)
    (hcl : ∀ L ∈ Λ, ∃ z : Y, IsClassicalMember p f L z) (hex : ExactMembers Λ)
    (hcomm : ∀ K ∈ Λ, ∀ J ∈ Λ, K ≠ J → Commutes K J) : HypOmega p f Λ where
  conjInvariant := hconj
  classical := hcl
  exact := hex
  omega4 K hK J hJ hKJ := by
    have hc := hcomm K hK J hJ hKJ
    refine ⟨?_, fun _ => hc⟩
    obtain ⟨z, hz⟩ := hcl K hK
    obtain ⟨e⟩ := hz.nonempty_equiv_sl2 (hex K hK)
    have h2 : Nat.card (Subgroup.center ↥K) = 2 :=
      natCard_center_of_equiv_sl2 (odd_natCard_galoisField hp hq) e
    have hle : (K ⊓ J).subgroupOf K ≤ Subgroup.center ↥K := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2 x hx.2)
    have hdvd : Nat.card ((K ⊓ J).subgroupOf K) ∣ 2 := h2 ▸ Subgroup.card_dvd_of_le hle
    have hcard : Nat.card ↥(K ⊓ J) = Nat.card ((K ⊓ J).subgroupOf K) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ J ≤ K)).toEquiv).symm
    rw [hcard]
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h <;> rw [h] <;> simp
  omega5 K hK J hJ hKJ _ _ v hvJ _ _ _ :=
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hvJ (hcomm K hK J hJ hKJ).symm)

theorem twFamily_hypOmega (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (t : G) :
    HypOmega p f (twFamily Ω t) := by
  have hodd := odd_natCard_galoisField hp hq
  have h3 : 3 ≤ Nat.card (GaloisField p f) := by
    have := four_le_natCard_galoisField (p := p) (f := f) hq
    omega
  have hexM : ∀ {M : Subgroup G}, M ∈ Ω → IsUniqueInvolution M t →
      classicalInvolutionOddCore ↥(twImage t M) = ⊥ := by
    intro M hM hMt
    obtain ⟨e⟩ := nonempty_equiv_sl2_twImage hΩ hM hMt
    exact normal_odd_of_equiv_sl2 hodd h3 e _ inferInstance
      (CFSG.ComponentClassification.OddCore.odd_card _)
  have hex : ExactMembers (twFamily Ω t) := by
    rintro L ⟨M, hM, hMt, rfl⟩
    exact hexM hM hMt
  refine HypOmega.of_commuting hp hq (conjInvariant_twFamily hΩ t) ?_ hex ?_
  · rintro L ⟨M, hM, hMt, rfl⟩
    obtain ⟨e⟩ := nonempty_equiv_sl2_twImage hΩ hM hMt
    refine ⟨twT t, ?_⟩
    exact
      { orderOf_eq_two := orderOf_eq_prime (by rw [pow_two]; exact twT_sq t hMt.sq)
          (twT_ne_one hMt.sq hMt.ne_one)
        mem := ⟨⟨t, t_mem_TwC t⟩, Subgroup.mem_subgroupOf.mpr hMt.mem, rfl⟩
        perfect := isPerfect_of_equiv_sl2 (four_le_natCard_galoisField hq) e
        subnormal := by
          rw [centralizer_twT]
          exact isSubnormal_twImage hΩ hM hMt
        nonempty_equiv := ⟨((QuotientGroup.quotientMulEquivOfEq (hexM hM hMt)).trans
          QuotientGroup.quotientBot).trans e⟩ }
  · rintro _ ⟨M, hM, hMt, rfl⟩ _ ⟨J, hJ, hJt, rfl⟩ hne
    exact commutes_twImage hΩ hM hJ (fun h => hne (by rw [h])) hMt hJt

end Finite

end CFSG.ClassicalInvolution.Asc77

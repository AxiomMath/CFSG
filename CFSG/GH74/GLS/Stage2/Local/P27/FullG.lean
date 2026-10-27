module

public import CFSG.GH74.GLS.Stage2.Local.P27.FullGAux
public import CFSG.GH74.GLS.Stage2.Local.P27.FullFRes
public import CFSG.GH74.GLS.Stage2.Local.P27.OddGen
import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoOdd
import CFSG.GH74.GLS.Stage1.Main.P49HBase

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem inf_oResidual_le {O K T T₁ : Subgroup X} [O.Normal] [K.Normal]
    (hO : Odd (Nat.card ↥O)) (hT2 : IsPGroup 2 ↥T) (hTidx : ¬ 2 ∣ T.index)
    (hres : oPrimeResidual 2 X ⊔ O = O ⊔ K ⊔ T)
    (hT₁ : T₁ ≤ T) (hsup : (T ⊓ K) ⊔ T₁ = T) (hinf : T₁ ⊓ K = ⊥) (hdih : IsDihedral ↥T₁)
    {x : X} (hxT₁ : x ∈ T₁) (hx1 : x ≠ 1) (hxc : ∀ g : X, g * x = x * g) :
    T ⊓ oResidual 2 X ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M₀ : Subgroup X := O ⊔ K with hM₀
  have hπs : Function.Surjective (QuotientGroup.mk' M₀) := QuotientGroup.mk'_surjective M₀
  let π : X →* X ⧸ M₀ := QuotientGroup.mk' M₀
  have hker : ∀ a, π a = 1 ↔ a ∈ M₀ := fun a => QuotientGroup.eq_one_iff a
  have H1 : T ⊓ M₀ ≤ K := inf_sup_normal_le hO hT2
  have hinj : Function.Injective (π.comp T₁.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : π (a : X) = 1 := ha
    have hM : (a : X) ∈ M₀ := (hker _).1 ha'
    have hK' : (a : X) ∈ K := H1 ⟨hT₁ a.2, hM⟩
    have : (a : X) ∈ T₁ ⊓ K := ⟨a.2, hK'⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact Subtype.ext this
  let Tb : Subgroup (X ⧸ M₀) := T₁.map π
  have hrange : (π.comp T₁.subtype).range = Tb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : ↥T₁ ≃* ↥Tb := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hTbdih : IsDihedral ↥Tb := IsDihedral.of_mulEquiv e hdih
  have hπK : K.map π = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨k, hk, rfl⟩
    exact (hker k).2 (Subgroup.mem_sup_right hk)
  have hπO : O.map π = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨k, hk, rfl⟩
    exact (hker k).2 (Subgroup.mem_sup_left hk)
  have hπT : T.map π = Tb := by
    apply le_antisymm
    · conv_lhs => rw [← hsup]
      rw [Subgroup.map_sup]
      exact sup_le (le_trans (Subgroup.map_mono inf_le_right) (hπK ▸ bot_le)) le_rfl
    · exact Subgroup.map_mono hT₁
  have hπR : (oPrimeResidual 2 X).map π = Tb := by
    have h1 : (oPrimeResidual 2 X ⊔ O).map π = (O ⊔ K ⊔ T).map π := by rw [hres]
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, hπO, hπK, hπT] at h1
    simpa using h1
  have hTbN : Tb.Normal := by
    rw [← hπR]
    exact Subgroup.Normal.map
      (CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49H.oPrimeResidual_two_normal X) π hπs
  have hTb2 : IsPGroup 2 ↥Tb := by
    have := hT2.map π
    rwa [hπT] at this
  have hTbidx : ¬ 2 ∣ Tb.index := by
    have h := Subgroup.index_map_dvd T hπs
    rw [hπT] at h
    exact fun h2 => hTidx (h2.trans h)
  let S : Sylow 2 (X ⧸ M₀) := hTb2.toSylow hTbidx
  have hSN : (S : Subgroup (X ⧸ M₀)).Normal := hTbN
  have hTb_all : ∀ A : Subgroup (X ⧸ M₀), IsPGroup 2 ↥A → A ≤ Tb := by
    intro A hA
    obtain ⟨S', hS'⟩ := hA.exists_le_sylow
    have huniq : Unique (Sylow 2 (X ⧸ M₀)) := Sylow.unique_of_normal S hSN
    have hSS : S' = S := Subsingleton.elim _ _
    rw [hSS] at hS'
    exact hS'
  have hxb : π x ∈ Tb := Subgroup.mem_map_of_mem _ hxT₁
  have hxb1 : π x ≠ 1 := by
    intro h
    have hM : x ∈ M₀ := (hker x).1 h
    have : x ∈ T₁ ⊓ K := ⟨hxT₁, H1 ⟨hT₁ hxT₁, hM⟩⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact hx1 this
  have hxbc : ∀ q : X ⧸ M₀, q * π x = π x * q := by
    intro q
    obtain ⟨y, rfl⟩ := hπs q
    rw [← map_mul, ← map_mul, hxc y]
  have hodd : ∀ g : X ⧸ M₀, Odd (orderOf g) → ∀ d ∈ Tb, g * d * g⁻¹ = d := by
    intro g hg d hd
    exact Signalizer.L52Two.odd_centralizes (W := Tb) (D := Tb) hTb2 (Or.inr hTbdih) le_rfl hg
      (pow_orderOf_eq_one g)
      (fun _ => ⟨π x, hxb, hxb1, by rw [mul_inv_eq_iff_eq_mul]; exact hxbc g⟩) d hd
  set N : Subgroup X := oResidual 2 X with hN
  let Nb : Subgroup (X ⧸ M₀) := N.map π
  have hgen : Nb ≤ Subgroup.closure {y : X ⧸ M₀ | y ∈ Nb ∧ Odd (orderOf y)} := by
    show N.map π ≤ _
    rw [hN, oResidual, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ (Subgroup.subset_closure hc), ?_⟩
    have hc' : Nat.Coprime (orderOf c) 2 := hc
    have hodd' : Odd (orderOf c) := Nat.coprime_two_left.1 (Nat.coprime_comm.1 hc')
    exact Odd.of_dvd_nat hodd' (orderOf_map_dvd π c)
  have hc : ∀ u ∈ Nb, IsPGroup 2 ↥(zpowers u) → ∀ v ∈ Nb, u * v = v * u := by
    intro u hu hu2 v hv
    have huT : u ∈ Tb := hTb_all (zpowers u) hu2 (Subgroup.mem_zpowers u)
    have hNle : Nb ≤ centralizer ({u} : Set (X ⧸ M₀)) := by
      show N.map π ≤ _
      rw [Subgroup.map_le_iff_le_comap, hN, oResidual]
      refine (Subgroup.closure_le _).2 ?_
      intro c hcc
      show π c ∈ centralizer ({u} : Set (X ⧸ M₀))
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc' : Nat.Coprime (orderOf c) 2 := hcc
      have hodd' : Odd (orderOf c) := Nat.coprime_two_left.1 (Nat.coprime_comm.1 hc')
      have hodd'' : Odd (orderOf (π c)) := Odd.of_dvd_nat hodd' (orderOf_map_dvd π c)
      have := hodd (π c) hodd'' u huT
      rwa [mul_inv_eq_iff_eq_mul] at this
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hNle hv)).symm
  have hNb : Odd (Nat.card ↥Nb) := odd_card_of_two_elements_central hgen hc
  rintro s ⟨hsT, hsN⟩
  have hsNb : π s ∈ Nb := Subgroup.mem_map_of_mem _ hsN
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (π s) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hT2 ⟨s, hsT⟩
    refine ⟨k, ?_⟩
    have := congrArg (fun z : ↥T => π (z : X)) hk
    simpa [← map_pow] using this
  have h1 : π s = 1 := by
    have hd1 : orderOf (π s) ∣ Nat.card ↥Nb := by
      have := orderOf_dvd_natCard (⟨π s, hsNb⟩ : ↥Nb)
      rwa [Subgroup.orderOf_mk] at this
    have hd2 : orderOf (π s) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥Nb) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hNb)
    have := Nat.dvd_gcd hd2 hd1
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
  exact H1 ⟨hsT, (hker s).1 h1⟩

end Abstract

section GLevel

variable {G : Type} [Group G] [Finite G]

theorem fullG_of_data {x : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hx2 : orderOf x = 2)
    (hres : oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) =
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T)
    (hT1 : ∃ T₁ : Subgroup G, T₁ ≤ T ∧ (T ⊓ Jx x) ⊔ T₁ = T ∧ T₁ ⊓ Jx x = ⊥ ∧ x ∈ T₁ ∧
      IsDihedral ↥T₁)
    (hD₂ : IsDihedral ↥(T ⊓ Jx x)) : FullG x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁, hT₁T, hsup, hinf, hxT₁, hdih⟩ := hT1
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hTC : T ≤ C := hT.le
  have hJC : Jx x ≤ C := P34.Jx_le_centralizer x
  have hT₁C : T₁ ≤ C := hT₁T.trans hTC
  have hinjC : Function.Injective (Subgroup.map C.subtype) := Subgroup.map_injective C.subtype_injective
  let K : Subgroup ↥C := (Jx x).subgroupOf C
  let T' : Subgroup ↥C := T.subgroupOf C
  let T₁' : Subgroup ↥C := T₁.subgroupOf C
  let O : Subgroup ↥C := pPrimeCore 2 ↥C
  have : K.Normal := Jx_subgroupOf_normal x
  have : O.Normal := pPrimeCore_normal
  have hmK : K.map C.subtype = Jx x := Subgroup.map_subgroupOf_eq_of_le hJC
  have hmT : T'.map C.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTC
  have hmT₁ : T₁'.map C.subtype = T₁ := Subgroup.map_subgroupOf_eq_of_le hT₁C
  have hmO : O.map C.subtype = pPrimeCoreOf 2 C := rfl
  have hO : Odd (Nat.card ↥O) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hT2 : IsPGroup 2 ↥T' := hT.isPGroup.comap_subtype
  have hTidx : ¬ 2 ∣ T'.index := by
    obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
    have := Q.not_dvd_index
    rwa [hQ] at this
  have hres' : oPrimeResidual 2 ↥C ⊔ O = O ⊔ K ⊔ T' := by
    apply hinjC
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, hmK, hmT, hmO]
    exact hres
  have hT₁' : T₁' ≤ T' := fun a ha => Subgroup.mem_subgroupOf.2 (hT₁T (Subgroup.mem_subgroupOf.1 ha))
  have hsup' : (T' ⊓ K) ⊔ T₁' = T' := by
    apply hinjC
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ C.subtype_injective, hmT, hmK, hmT₁]
    exact hsup
  have hinf' : T₁' ⊓ K = ⊥ := by
    apply hinjC
    rw [Subgroup.map_inf _ _ _ C.subtype_injective, hmT₁, hmK, Subgroup.map_bot]
    exact hinf
  have hdih' : IsDihedral ↥T₁' :=
    IsDihedral.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hT₁C).symm hdih
  have hxC : x ∈ C := Subgroup.mem_centralizer_iff.2 (by simp)
  have hx1 : (⟨x, hxC⟩ : ↥C) ≠ 1 := by
    intro h
    have h1 : x = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hx2
    omega
  have hxc : ∀ g : ↥C, g * (⟨x, hxC⟩ : ↥C) = ⟨x, hxC⟩ * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hcore := inf_oResidual_le hO hT2 hTidx hres' hT₁' hsup' hinf' hdih'
    (Subgroup.mem_subgroupOf.2 hxT₁) hx1 hxc
  have heq : T ⊓ O2Of C = T ⊓ Jx x := by
    apply le_antisymm
    · rintro g ⟨hgT, hgN⟩
      obtain ⟨n, hn, rfl⟩ := hgN
      have hnK : n ∈ K := hcore ⟨Subgroup.mem_subgroupOf.2 hgT, hn⟩
      exact ⟨hgT, Subgroup.mem_subgroupOf.1 hnK⟩
    · exact inf_le_inf_left T (le_O2Of_of_perfect hJC (pLayerOf_two_perfect_P27 _))
  have hD : IsDihedral ↥(T ⊓ O2Of C) :=
    IsDihedral.of_mulEquiv (MulEquiv.subgroupCongr heq.symm) hD₂
  intro P
  exact isDihedral_sylow_of_inf hT (O2Of_le C) (le_normalizer_O2Of C) hD P

end GLevel

end CFSG.GH74.GLS.Stage2.Local.P27

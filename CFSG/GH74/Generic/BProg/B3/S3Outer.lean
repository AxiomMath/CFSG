module

public import CFSG.GH74.Generic.BProg.B3.S3OuterGlue
public import CFSG.GH74.Generic.BProg.B3.S3OuterPsl
public import CFSG.GH74.Generic.BProg.B3.S3OuterUni
public import CFSG.GH74.Generic.S3.L3FRankGlue

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Outer

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification CFSG.GH74.L5U5 Subgroup S3OuterCore
open scoped commutatorElement

theorem nonab_of_qShape3 {X : Type} [Group X] (h3 : QShape3 X) : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨p, f, hp, hp2, hq, hmod⟩ := h3
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have := Nat.odd_iff.mp hodd
    omega
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hs : IsSimpleGroup X := isSimpleGroup_of_lieModel_L3' hmod
  have hz : center X = ⊥ := by
    rcases hmod with hm | hm
    · exact S3.l3_center_eq_bot (Or.inl rfl) hp hp2 hf h5 hm
    · exact S3.l3_center_eq_bot (Or.inr rfl) hp hp2 hf h5 hm
  by_contra hcon
  push Not at hcon
  have htop : center X = ⊤ := eq_top_iff.2 fun g _ => Subgroup.mem_center_iff.2 fun h => hcon h g
  rw [hz] at htop
  have := hs.toNontrivial
  exact bot_ne_top htop

theorem outerCore_of_qShape3 {Y : Type} [Group Y] [Finite Y] (h3 : QShape3 Y) (hs : IsSimpleGroup Y)
    {α : MulAut Y} (hα2 : α * α = 1) (hout : α ∉ OuterAutomorphisms.inner Y) : OuterCore α := by
  classical
  have hnab := nonab_of_qShape3 h3
  obtain ⟨p, f, hp, hp2, hq, hmod⟩ := h3
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have := Nat.odd_iff.mp hodd
    omega
  rcases hmod with hm | hm
  ·
    obtain ⟨F, _, _, hFc, hpr, hf1, hF2, ψ, ρ, hinj, hψ⟩ :=
      exists_projective_rep hs hnab hp2 (le_refl 3) (stated_of_lieModel_PSL hm)
    have hα'2 : ρ α * ρ α = 1 := by rw [← map_mul, hα2, map_one]
    have hα'out : ρ α ∉ OuterAutomorphisms.inner (LinearFlag.projectiveSL 3 F) := by
      rintro ⟨x, hx⟩
      apply hout
      refine ⟨ψ.symm x, ?_⟩
      ext y
      apply ψ.injective
      rw [hψ α y, ← hx]
      simp [MulAut.conj_apply]
    exact OuterCore.of_mulEquiv ψ (fun y => hψ α y)
      (S3OuterPsl.outerCore_psl3 hpr hf1 hp2 hFc hF2 h5 hα'2 hα'out)
  ·
    obtain ⟨hadm, F, _, _, hF, ⟨e₀⟩⟩ := stated_of_lieModel_PSU hm
    have hf1 : 1 ≤ f := hadm.2.1
    have hU : UnitaryFieldData p f F := ⟨hp, hf1, by rw [hF, ← pow_mul, mul_comm]⟩
    obtain ⟨θ, hθ⟩ := KGroups.L3Eps.Uni.exists_cover_of_equiv hU e₀
    exact S3OuterUni.outerCore_unitary hU hp2 h5 hθ hα2 hout

theorem isPCompIn_of_comp_even {Y : Type} [Group Y] [Finite Y] {C K : Subgroup Y}
    (hK : IsCompIn C K) (hev : 2 ∣ Nat.card ↥K) : IsPCompIn 2 C K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hK.1, isPComponent_of_isComponent_of_not_le 2 hK.2 fun hle => ?_⟩
  have h1 : Nat.card ↥(K.subgroupOf C) ∣ Nat.card ↥(pPrimeCore 2 ↥C) := Subgroup.card_dvd_of_le hle
  have h2 : Nat.card ↥(K.subgroupOf C) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.1).toEquiv
  rw [h2] at h1
  have h3 := Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  have h4 := Nat.Coprime.eq_one_of_dvd h3 hev
  omega

theorem lemma302OuterData {X : Type} [Group X] [Finite X] {Kb : Subgroup X} (hKn : Kb.Normal)
    (hKs : IsSimpleGroup ↥Kb) (hK3 : QShape3 ↥Kb) {u : X} (hu : orderOf u = 2)
    (hout : ∀ k ∈ Kb, ∃ g ∈ Kb, u * g * u⁻¹ ≠ k * g * k⁻¹) :
    ∃ Lb : Subgroup X, IsPCompIn 2 (Kb ⊓ centralizer ({u} : Set X)) Lb ∧ 2 ≤ pRank 2 ↥Lb ∧
      ∃ t ∈ Lb, orderOf t = 2 ∧ ∃ k ∈ Kb, k * u * k⁻¹ = u * t := by
  have : Kb.Normal := hKn
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu, pow_two] at this
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  set α : MulAut ↥Kb := MulAut.conjNormal u with hα
  have hα2 : α * α = 1 := by rw [hα, ← map_mul, hu2, map_one]
  have hαout : α ∉ OuterAutomorphisms.inner ↥Kb := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hg, hne⟩ := hout (y : X) y.2
    apply hne
    have := congrArg (fun φ : MulAut ↥Kb => ((φ ⟨g, hg⟩ : ↥Kb) : X)) hy
    simpa [MulAut.conj_apply, hα, MulAut.conjNormal_apply] using this.symm
  obtain ⟨N, hNq, hNr, hNfix, hNnorm, t, ht, ht2, ht1, k, hk⟩ :=
    outerCore_of_qShape3 hK3 hKs hα2 hαout
  set Lb : Subgroup X := N.map Kb.subtype with hLb
  set C : Subgroup X := Kb ⊓ centralizer ({u} : Set X) with hC
  have hfixg : ∀ g : ↥Kb, (g : X) ∈ centralizer ({u} : Set X) → α g = g := by
    intro g hg
    apply Subtype.ext
    rw [hα, MulAut.conjNormal_apply]
    have := mem_centralizer_singleton_iff.1 hg
    calc u * (g : X) * u⁻¹ = (u * g) * u⁻¹ := rfl
      _ = (g * u) * u⁻¹ := by rw [← this]
      _ = g := by group
  have hLbC : Lb ≤ C := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n.2, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := congrArg Subtype.val (hNfix n hn)
    rw [hα, MulAut.conjNormal_apply] at h1
    change u * (n : X) * u⁻¹ = n at h1
    calc (n : X) * u = (u * (n : X) * u⁻¹) * u := by rw [h1]
      _ = u * n := by group
  have hnorm : (Lb.subgroupOf C).Normal := by
    refine ⟨fun a ha x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨n, hn, hna⟩ := ha
    have hxK : (x : X) ∈ Kb := x.2.1
    have hxu : (x : X) ∈ centralizer ({u} : Set X) := x.2.2
    have hf := hfixg ⟨x, hxK⟩ hxu
    obtain ⟨m, hm, hmn⟩ : ∃ m ∈ N, ((⟨x, hxK⟩ : ↥Kb) * n * (⟨x, hxK⟩ : ↥Kb)⁻¹ : ↥Kb) = m :=
      ⟨_, hNnorm ⟨x, hxK⟩ hf n hn, rfl⟩
    refine ⟨m, hm, ?_⟩
    have := congrArg Subtype.val hmn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, ← hna]
    exact this.symm
  have hq : IsQuasisimple ↥(Lb.subgroupOf C) :=
    LocalCores.isQuasisimple_of_mulEquiv
      ((N.equivMapOfInjective Kb.subtype Kb.subtype_injective).trans
        (Subgroup.subgroupOfEquivOfLe hLbC).symm) hNq
  have hcomp : IsCompIn C Lb := ⟨hLbC, hq, hnorm.isSubnormal⟩
  have htL : (t : X) ∈ Lb := ⟨t, ht, rfl⟩
  have ht2X : (t : X) * t = 1 := by
    have := congrArg Subtype.val ht2
    simpa using this
  have ht1X : (t : X) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hordt : orderOf (t : X) = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2X) ht1X
  have hev : 2 ∣ Nat.card ↥Lb := by
    have := Subgroup.orderOf_dvd_natCard Lb htL
    rwa [hordt] at this
  have hrank : 2 ≤ pRank 2 ↥Lb := by
    have h2 := CFSG.RankThree.PartOne.pRank_eq_of_mulEquiv_of_one_lt (p := 2) (by norm_num)
      (N.equivMapOfInjective Kb.subtype Kb.subtype_injective)
    exact h2 ▸ hNr
  refine ⟨Lb, isPCompIn_of_comp_even hcomp hev, hrank, t, htL, hordt, k, k.2, ?_⟩
  have hk' := congrArg Subtype.val hk
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hk'
  rw [hα, MulAut.conjNormal_apply] at hk'
  calc (k : X) * u * (k : X)⁻¹ = (k : X) * u⁻¹ * (k : X)⁻¹ := by rw [hui]
    _ = (u * u) * (k : X) * u⁻¹ * (k : X)⁻¹ := by rw [hu2]; group
    _ = u * (u * (k : X) * u⁻¹ * (k : X)⁻¹) := by group
    _ = u * t := by rw [hk']

theorem lemma302OuterFact : S3OuterGlue.Lemma302OuterFact := by
  intro X _ _ Kb hKn hKs hK3 u hu hout
  obtain ⟨Lb, hL, -, t, ht, hordt, k, hk, hkt⟩ := lemma302OuterData hKn hKs hK3 hu hout
  exact ⟨Lb, hL, t, ht, hordt, k, hk, hkt⟩

variable {G : Type} [Group G] [Finite G]

theorem outerCaseFusion_of {x : G} {K A : Subgroup G} (hyp : Hyp2 G) (hc : IsJ2Circ x K)
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) (_hsrc : IsSource2 x K A)
    (hC : pRank 2 ↥(CxK x K) ≤ 1) {y : G} (hyA : y ∈ A ⊓ K) (hy : orderOf y = 2) :
    S3Fusion.OuterCaseFusion x K y := by
  have hx : orderOf x = 2 := hc.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.1.1.1.2.2
  have hshape := S3Fusion.barShape_of_ctx hyp.gen4 hx hK h3 hC
  exact S3OuterGlue.outerCaseFusion_of_fact lemma302OuterFact hshape hx hK hyA.2 hy

end S3Outer

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

end CFSG.GH74.Generic.BProg.B3

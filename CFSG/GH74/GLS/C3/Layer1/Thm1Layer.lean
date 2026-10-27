module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1
open scoped commutatorElement

theorem isQuasisimple_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : IsQuasisimple A) : IsQuasisimple B := by
  refine LieType.CurtisTits.isQuasisimple_of_surjective (φ := e.toMonoidHom) hA e.surjective ?_
  obtain ⟨-, -, a, b, hab⟩ := hA
  by_contra h
  push Not at h
  apply hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ b
  have hx : x = 1 := e.injective (by simpa using h x)
  have hy : y = 1 := e.injective (by simpa using h y)
  simp [hx, hy]

theorem exists_pComponent_of_quotient_component {X : Type} [Group X] [Finite X]
    {Kh : Subgroup (X ⧸ pPrimeCore 2 X)} (hK : IsComponent Kh) :
    ∃ L : Subgroup X, IsPComponent 2 L ∧ L.map (QuotientGroup.mk' (pPrimeCore 2 X)) = Kh := by
  let π : X →* X ⧸ pPrimeCore 2 X := QuotientGroup.mk' (pPrimeCore 2 X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let S : Set (Subgroup X) := {J | J.IsSubnormal ∧ J.map π = Kh}
  have hS : S.Nonempty :=
    ⟨Kh.comap π, isSubnormal_comap π hK.2, by
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top_of_surjective _ hπ, top_inf_eq]⟩
  obtain ⟨L, hLS, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup X)) S hS
  exact ⟨L, ⟨Kh, hK, hLS.1, hLS.2, fun J hJ hJs hJm => hmin J ⟨hJs, hJm⟩ hJ⟩, hLS.2⟩

theorem pLayerOf_ne_bot_of_hom {G : Type} [Group G] [Finite G] {H : Subgroup G} {Y : Type}
    [Group Y] [Finite Y] (ρ : ↥H →* Y) (hρ : Function.Surjective ρ)
    (hodd : Odd (Nat.card ρ.ker)) (hY : pPrimeCore 2 Y = ⊥) {Kh : Subgroup Y}
    (hKh : IsComponent Kh) : pLayerOf 2 H ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker_le : ρ.ker ≤ pPrimeCore 2 ↥H :=
    GroupTheory.le_pPrimeCore_of_normal (MonoidHom.normal_ker ρ) (Nat.coprime_two_left.2 hodd)
  have hO_le : pPrimeCore 2 ↥H ≤ ρ.ker := by
    have hN : ((pPrimeCore 2 ↥H).map ρ).Normal :=
      (inferInstance : (pPrimeCore 2 ↥H).Normal).map ρ hρ
    have hcop : Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 ↥H).map ρ)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (pPrimeCore 2 ↥H) ρ)
        pPrimeCore_coprime_card
    have h1 := GroupTheory.le_pPrimeCore_of_normal hN hcop
    rw [hY] at h1
    intro x hx
    have := h1 (Subgroup.mem_map_of_mem ρ hx)
    rw [Subgroup.mem_bot] at this
    exact this
  have hO : pPrimeCore 2 ↥H = ρ.ker := le_antisymm hO_le hker_le
  let e : (↥H ⧸ pPrimeCore 2 ↥H) ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
  have hcm : Kh.comap e.toMonoidHom = Kh.map e.symm.toMonoidHom := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hmap : ↥(Kh.comap e.toMonoidHom) ≃* ↥Kh :=
    (MulEquiv.subgroupCongr hcm).trans (e.symm.subgroupMap Kh).symm
  have hKq : IsComponent (Kh.comap e.toMonoidHom) :=
    ⟨isQuasisimple_of_mulEquiv' hmap.symm hKh.1, isSubnormal_comap e.toMonoidHom hKh.2⟩
  obtain ⟨L, hL, hLmap⟩ := exists_pComponent_of_quotient_component hKq
  have hLne : L ≠ ⊥ := by
    intro hL0
    rw [hL0, Subgroup.map_bot] at hLmap
    have hsolv : Group.IsSolvable ↥(Kh.comap e.toMonoidHom) := by
      rw [← hLmap]
      infer_instance
    exact LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hKq.1 hsolv
  have hcomp : IsPCompIn 2 H (L.map H.subtype) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨l, -, rfl⟩
      exact l.2
    · have : (L.map H.subtype).subgroupOf H = L :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective L
      rw [this]
      exact hL
  intro hbot
  have hle : L.map H.subtype ≤ pLayerOf 2 H := le_sSup hcomp
  rw [hbot, le_bot_iff] at hle
  exact hLne ((Subgroup.map_eq_bot_iff_of_injective L H.subtype_injective).1 hle)

theorem exists_centralizing_mem_coset_of {G : Type} [Group G] [Finite G] {K Q : Subgroup G}
    (hQ2 : IsPGroup 2 ↥Q) (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K) {k : G} (hk : k ∈ K)
    (hQt : ∀ q ∈ Q, ⁅k, q⁆ ∈ pPrimeCoreOf 2 K) :
    ∃ c ∈ K, (∀ q ∈ Q, c * q = q * c) ∧ k⁻¹ * c ∈ pPrimeCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Set G := {x | x ∈ K ∧ k⁻¹ * x ∈ pPrimeCoreOf 2 K}
  have hS : ∀ q ∈ Q, ∀ x ∈ S, q * x * q⁻¹ ∈ S := by
    intro q hq x hx
    obtain ⟨hxK, hxO⟩ := hx
    refine ⟨hQK q hq x hxK, ?_⟩
    have hw : (⁅k, q⁆)⁻¹ ∈ pPrimeCoreOf 2 K := (pPrimeCoreOf 2 K).inv_mem (hQt q hq)
    have h1 := TwoThin.pPrimeCoreOf_normalized K (K.inv_mem hk) hw
    have h2 := U1a.pPrimeCoreOf_norm hQK hq hxO
    have h3 := (pPrimeCoreOf 2 K).mul_mem h1 h2
    convert h3 using 1
    simp only [commutatorElement_def]
    group
  let inst : MulAction ↥Q ↥S :=
    { smul := fun q x => ⟨(q : G) * x * (q : G)⁻¹, hS q q.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : ↥Q) : G) * x * ((1 : ↥Q) : G)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        show ((a * b : ↥Q) : G) * x * ((a * b : ↥Q) : G)⁻¹ =
          (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc]) }
  have hcard : ¬ 2 ∣ Nat.card ↥S := by
    let e : ↥(pPrimeCoreOf 2 K) ≃ ↥S :=
      { toFun := fun o => ⟨k * o, K.mul_mem hk (TwoThin.pPrimeCoreOf_le K o.2), by simp⟩
        invFun := fun x => ⟨k⁻¹ * x, x.2.2⟩
        left_inv := fun o => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by simp) }
    rw [← Nat.card_congr e]
    exact fun hd => (Nat.not_even_iff_odd.2 (TwoThin.card_pPrimeCoreOf_odd K))
      (even_iff_two_dvd.2 hd)
  obtain ⟨⟨x, hxK, hxO⟩, hfix⟩ := hQ2.nonempty_fixed_point_of_prime_not_dvd_card ↥S hcard
  refine ⟨x, hxK, fun q hq => ?_, hxO⟩
  have h : q * x * q⁻¹ = x := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hfix ⟨q, hq⟩)
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem exists_fixed_mem_coset {G : Type} [Group G] [Finite G] {K : Subgroup G} {f : G}
    (hf2 : orderOf f = 2) (hfN : f ∈ normalizer (K : Set G)) {k : G} (hk : k ∈ K)
    (hfix : ⁅k, f⁆ ∈ pPrimeCoreOf 2 K) :
    ∃ c ∈ K, f * c = c * f ∧ k⁻¹ * c ∈ pPrimeCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, sq] at this
  have hQ2 : IsPGroup 2 ↥(zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf2, pow_one])
  have hQN : zpowers f ≤ normalizer (K : Set G) := (zpowers_le).2 hfN
  obtain ⟨c, hcK, hcQ, hck⟩ := exists_centralizing_mem_coset_of (K := K) (Q := zpowers f) hQ2
    (fun q hq k' hk' => (Subgroup.mem_normalizer_iff.1 (hQN hq) k').1 hk') hk (fun q hq => by
      rcases mem_zpowers_of_mul_self hff hq with rfl | rfl
      · simp only [commutatorElement_one_right]
        exact (pPrimeCoreOf 2 K).one_mem
      · exact hfix)
  exact ⟨c, hcK, (hcQ f (mem_zpowers f)).symm, hck⟩

section CentMap

variable {G : Type} [Group G] {C K : Subgroup G}
  (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) {f : G} (hfC : f ∈ C)

include hfC in
theorem actHom_mk_cent (h : ↥(K ⊓ centralizer ({f} : Set G))) :
    Back.actHom hKN ⟨f, hfC⟩ (QuotientGroup.mk (⟨(h : G), h.2.1⟩ : ↥K)) =
      QuotientGroup.mk (⟨(h : G), h.2.1⟩ : ↥K) := by
  rw [Back.actHom_mk hKN ⟨f, hfC⟩ ⟨(h : G), h.2.1⟩]
  have hfh : f * (h : G) * f⁻¹ = (h : G) := by
    have := mem_centralizer_singleton_iff.1 h.2.2
    rw [← this]
    group
  congr 1
  exact Subtype.ext hfh

@[expose] noncomputable def centMap :
    ↥(K ⊓ centralizer ({f} : Set G)) →*
      ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)) :=
  ((QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp
    (Subgroup.inclusion (inf_le_left : K ⊓ centralizer ({f} : Set G) ≤ K))).codRestrict _
    (fun h => actHom_mk_cent hKN hfC h)

theorem centMap_apply (h : ↥(K ⊓ centralizer ({f} : Set G))) :
    ((centMap hKN hfC h : ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩))) : kBar K) =
      QuotientGroup.mk (⟨(h : G), h.2.1⟩ : ↥K) := rfl

theorem centMap_surjective [Finite G] (hf2 : orderOf f = 2) : Function.Surjective (centMap hKN hfC) := by
  rintro ⟨kb, hkb⟩
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective kb
  have h1 : (QuotientGroup.mk (⟨f * k * f⁻¹, hKN f hfC k hk⟩ : ↥K) : kBar K) =
      QuotientGroup.mk (⟨k, hk⟩ : ↥K) := hkb
  rw [QuotientGroup.eq] at h1
  have h2 : (f * k * f⁻¹)⁻¹ * k ∈ pPrimeCoreOf 2 K :=
    Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨K.mul_mem (K.inv_mem (hKN f hfC k hk)) hk, h1⟩
  have hfix : ⁅k, f⁆ ∈ pPrimeCoreOf 2 K := by
    have h3 := TwoThin.pPrimeCoreOf_normalized K hk h2
    have : ⁅k, f⁆ = k * ((f * k * f⁻¹)⁻¹ * k) * k⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact h3
  obtain ⟨c, hcK, hcf, hkc⟩ :=
    exists_fixed_mem_coset hf2 (U1a.mem_normalizer_of_norm hKN hfC) hk hfix
  refine ⟨⟨c, hcK, mem_centralizer_singleton_iff.2 hcf.symm⟩, Subtype.ext ?_⟩
  show (QuotientGroup.mk (⟨c, hcK⟩ : ↥K) : kBar K) = QuotientGroup.mk (⟨k, hk⟩ : ↥K)
  obtain ⟨hmem, h5⟩ := Back.Setup91.mem_pPrimeCoreOf_iff.1 hkc
  exact ((QuotientGroup.eq).2 h5).symm

theorem centMap_ker_odd [Finite G] : Odd (Nat.card (centMap hKN hfC).ker) := by
  have hle : (centMap hKN hfC).ker.map (K ⊓ centralizer ({f} : Set G)).subtype ≤
      pPrimeCoreOf 2 K := by
    rintro _ ⟨h, hh, rfl⟩
    have h0 : ((centMap hKN hfC h : ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩))) :
        kBar K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hh)
    rw [centMap_apply] at h0
    exact Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨h.2.1, (QuotientGroup.eq_one_iff _).1 h0⟩
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (K ⊓ centralizer ({f} : Set G)).subtype_injective] at hdvd
  exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) hdvd

theorem layer_ne_bot_of_good [Finite G] (hf2 : orderOf f = 2)
    (hgood : GoodC (kBar K) (Back.actHom hKN ⟨f, hfC⟩)) :
    pLayerOf 2 (K ⊓ centralizer ({f} : Set G)) ≠ ⊥ := by
  obtain ⟨Y, _, _, hY, ⟨Kh, hKh⟩, ⟨eqv⟩⟩ := hgood
  let ρ : ↥(K ⊓ centralizer ({f} : Set G)) →* Y := eqv.toMonoidHom.comp (centMap hKN hfC)
  have hρ : Function.Surjective ρ := eqv.surjective.comp (centMap_surjective hKN hfC hf2)
  have hker : ρ.ker = (centMap hKN hfC).ker := by
    ext h
    simp only [MonoidHom.mem_ker, ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ⟨fun h1 => eqv.injective (by rw [h1, map_one]), fun h1 => by rw [h1, map_one]⟩
  exact pLayerOf_ne_bot_of_hom ρ hρ (hker ▸ centMap_ker_odd hKN hfC) hY hKh

end CentMap

theorem orderOf_mul_eq_two_of_commute {M : Type*} [Group M] {f z : M} (hf2 : orderOf f = 2)
    (hz2 : orderOf z = 2) (hfz : f * z = z * f) (hne : f * z ≠ 1) : orderOf (f * z) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ hne
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, sq] at this
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  calc (f * z) ^ 2 = f * z * (f * z) := sq _
    _ = f * (z * f) * z := by simp only [mul_assoc]
    _ = f * (f * z) * z := by rw [← hfz]
    _ = (f * f) * (z * z) := by simp only [mul_assoc]
    _ = 1 := by rw [hff, hzz, one_mul]

end CFSG.GH74.GLS.C3.Layer1.Thm1

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1

theorem thm1_P31_layer_of
    (h2hb : IVK.IVK_1_2h_b) : B_thm1_P31_layer := by
  intro G _ _ hG hV x y K h𝒰 hshape hKN T hT f z hfT hf2 hfc hind hzP hz2 hzc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := h𝒰.1.1.2.1
  have hQ2 := card_le_two_of_noV2 hV h𝒰
  obtain ⟨hcen, hAut⟩ := kBar_autData h2hb hV h𝒰 hshape
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ := exists_E₁ hT.sylowT (by rw [h𝒰.2.2.1.2, hG.pRank_eq_four])
  have hfC : f ∈ centralizer ({x} : Set G) := hT.sylowT.le hfT
  have hzC : z ∈ centralizer ({x} : Set G) := hT.sylowT.le hzP.1
  obtain ⟨f₁, z₁, -, -, -, -, -, -, -, hz₁, hz₁2, hz₁c, hz₁u, -, -, -, hlay⟩ :=
    core_lift_G hKC hKN hT.sylowT hcen hAut hE₁T hE₁ hE₁16 hQ2
  have hzP' : (⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) ∈
      (T ⊓ K).subgroupOf (centralizer ({x} : Set G)) := hzP
  have hzz₁ : (⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) = z₁ := by
    rcases hz₁u ⟨z, hzC⟩ hzP' (fun q hq => Subtype.ext (hzc (q : G) hq)) with h | h
    · exfalso
      have : z = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at hz2
      omega
    · exact h
  have hfCT : (⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) ∈
      T.subgroupOf (centralizer ({x} : Set G)) := hfT
  have hf2' : orderOf (⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hf2
  have hfc' : ∀ p ∈ (T ⊓ K).subgroupOf (centralizer ({x} : Set G)),
      (⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) * p = p * ⟨f, hfC⟩ :=
    fun p hp => Subtype.ext (hfc p hp)
  have hφfinn : Back.actHom hKN ⟨f, hfC⟩ ∉ IVK.innAut (kBar K) := by
    obtain ⟨hfN, hF⟩ := hind
    exact not_mem_innAut_of_isFAutL2A7 hF
  rcases hlay ⟨f, hfC⟩ hfCT hf2' hfc' hφfinn with hg | ⟨hA7, hg⟩
  · exact Or.inl (layer_ne_bot_of_good hKN hfC hf2 hg)
  · refine Or.inr ⟨hA7, ?_⟩
    have hfzC : f * z ∈ centralizer ({x} : Set G) := Subgroup.mul_mem _ hfC hzC
    have hfz : f * z = z * f := hfc z hzP
    have hφz : Back.actHom hKN ⟨z, hzC⟩ ∈ IVK.innAut (kBar K) := by
      rw [Back.actHom_of_mem hKN hzP.2 hzC]
      exact ⟨_, rfl⟩
    have hφfz_eq : Back.actHom hKN ⟨f * z, hfzC⟩ =
        Back.actHom hKN ⟨f, hfC⟩ * Back.actHom hKN ⟨z, hzC⟩ := by
      have h1 := (Back.actHom hKN).map_mul ⟨f, hfC⟩ ⟨z, hzC⟩
      have e : (⟨f, hfC⟩ * ⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) = ⟨f * z, hfzC⟩ := rfl
      rw [e] at h1
      exact h1
    have hfz1 : f * z ≠ 1 := by
      intro h
      apply hφfinn
      have h1 : Back.actHom hKN ⟨f * z, hfzC⟩ = 1 := by
        have : (⟨f * z, hfzC⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext h
        rw [this, map_one]
      rw [hφfz_eq] at h1
      have h2 : Back.actHom hKN ⟨f, hfC⟩ = (Back.actHom hKN ⟨z, hzC⟩)⁻¹ :=
        eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact (IVK.innAut (kBar K)).inv_mem hφz
    have hfz2 : orderOf (f * z) = 2 := orderOf_mul_eq_two_of_commute hf2 hz2 hfz hfz1
    refine layer_ne_bot_of_good hKN hfzC hfz2 ?_
    rw [hφfz_eq, hzz₁]
    exact hg

end CFSG.GH74.GLS

module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Layer
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Model
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4E8
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

@[expose] def K94ClassG2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p f : ℕ), IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    Catalog K → Gen4 K → Open.twoRank K = 3 → p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (z : K) (I₁ I₂ : Subgroup K) (F₁ F₂ : Type) [Field F₁] [Field F₂] [Finite F₁] [Finite F₂],
      orderOf z = 2 → (∀ x ∈ I₁, ∀ y ∈ I₂, x * y = y * x) → I₁ ⊓ I₂ = zpowers z →
      Nonempty (↥I₁ ≃* SL(2, F₁)) → Nonempty (↥I₂ ≃* SL(2, F₂)) →
      (∀ x : K, (∃ k : ℕ, x ^ 2 ^ k = 1) → x * z = z * x →
        (∀ a ∈ I₁, x * a * x⁻¹ ∈ I₁) ∧ (∀ a ∈ I₂, x * a * x⁻¹ ∈ I₂)) →
      Nat.card F₁ = p ^ f → Nat.card F₂ = p ^ f → LieModel K .G2 0 p f

@[expose] def K94ClassD4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p f : ℕ), IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    Catalog K → Gen4 K → Open.twoRank K = 3 → p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (z : K) (I₁ I₂ : Subgroup K) (F₁ F₂ : Type) [Field F₁] [Field F₂] [Finite F₁] [Finite F₂],
      orderOf z = 2 → (∀ x ∈ I₁, ∀ y ∈ I₂, x * y = y * x) → I₁ ⊓ I₂ = zpowers z →
      Nonempty (↥I₁ ≃* SL(2, F₁)) → Nonempty (↥I₂ ≃* SL(2, F₂)) →
      (∀ x : K, (∃ k : ℕ, x ^ 2 ^ k = 1) → x * z = z * x →
        (∀ a ∈ I₁, x * a * x⁻¹ ∈ I₁) ∧ (∀ a ∈ I₂, x * a * x⁻¹ ∈ I₂)) →
      Nat.card F₁ = (p ^ f) ^ 3 → Nat.card F₂ = p ^ f → LieModel K .trialityD4 0 p f

@[expose] def K94Class : Prop := K94ClassG2 ∧ K94ClassD4

theorem unpack_four_subgroup {H : Type} [Group H] [Finite H] {z : H} {P : Sylow 2 H}
    {U : Subgroup H}
    (hZ : Subgroup.zpowers z = (Subgroup.center ↥(P : Subgroup H)).map (P : Subgroup H).subtype)
    (hzU : Subgroup.zpowers z ≤ U) (hUP : U ≤ (P : Subgroup H)) (hU4 : IsFourSubgroup U) :
    orderOf z = 2 ∧ ∃ u ∈ U, orderOf u = 2 ∧ u ≠ z ∧ u * z = z * u ∧
      ∀ s ∈ (P : Subgroup H), s * z = z * s := by
  have hzmem : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
  have hPz : ∀ s ∈ (P : Subgroup H), s * z = z * s := by
    intro s hs
    have hz' : z ∈ (Subgroup.center ↥(P : Subgroup H)).map (P : Subgroup H).subtype := hZ ▸ hzmem
    obtain ⟨c, hc, hcz⟩ := hz'
    rw [← hcz]
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc ⟨s, hs⟩))
  have hzU' : z ∈ U := hzU hzmem
  have hU2 : ∀ a ∈ U, a ^ 2 = 1 := fun a ha => by
    have := hU4.1
    exact elemPow_eq_one_of_isElementaryAbelian a ha
  have hz1 : z ≠ 1 := by
    intro h
    have hcen : (Subgroup.center ↥(P : Subgroup H)).map (P : Subgroup H).subtype = ⊥ := by
      rw [← hZ, h, Subgroup.zpowers_one_eq_bot]
    have hcen' : Subgroup.center ↥(P : Subgroup H) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (P : Subgroup H).subtype_injective).1 hcen
    have hnt : Nontrivial ↥(P : Subgroup H) := by
      refine Finite.one_lt_card_iff_nontrivial.mp ?_
      have h1 := Subgroup.card_le_of_le hUP
      have h2 := hU4.2
      omega
    have := (P.isPGroup').center_nontrivial
    have hbot := Subgroup.eq_bot_iff_forall _ |>.1 hcen'
    obtain ⟨c, hc⟩ := exists_ne (1 : ↥(Subgroup.center ↥(P : Subgroup H)))
    exact hc (Subtype.ext (hbot c.1 c.2))
  have hz2 : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; simpa [pow_two] using hU2 z hzU') hz1
  refine ⟨hz2, ?_⟩
  have hex : ∃ u ∈ U, u ∉ Subgroup.zpowers z := by
    by_contra hcon
    push Not at hcon
    have hle : U ≤ Subgroup.zpowers z := hcon
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hz2, hU4.2] at h1
    omega
  obtain ⟨u, huU, huz⟩ := hex
  have hu1 : u ≠ 1 := fun h => huz (h ▸ Subgroup.one_mem _)
  have huz' : u ≠ z := fun h => huz (h ▸ hzmem)
  refine ⟨u, huU, orderOf_eq_prime (by rw [pow_two]; simpa [pow_two] using hU2 u huU) hu1, huz',
    ?_, hPz⟩
  have := hU4.1
  have := (inferInstance : IsMulCommutative ↥U).is_comm.comm (⟨u, huU⟩ : ↥U) ⟨z, hzU'⟩
  exact congrArg Subtype.val this

theorem shape_z_eq {H : Type} [Group H] {z : H} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (S : Shape ↥(oPrimeResidualOf 2 (centralizer ({z} : Set H))) F₁ F₂) (hz : orderOf z = 2) :
    (S.z : H) = z := by
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hzC : z ∈ centralizer ({z} : Set H) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzY : z ∈ oPrimeResidualOf 2 (centralizer ({z} : Set H)) :=
    mem_oPrimeResidualOf_of_pow hzC (k := 1) (by simpa using hz2)
  have hJC₁ : S.J₁ ≤ centralizer ({z} : Set H) := S.J₁_le.trans (Subgroup.map_subtype_le _)
  have hJC₂ : S.J₂ ≤ centralizer ({z} : Set H) := S.J₂_le.trans (Subgroup.map_subtype_le _)
  rcases S.eq_one_or_eq_zH_of_centralizes hzY
      (fun x hx => (Subgroup.mem_centralizer_singleton_iff.1 (hJC₁ hx)).symm)
      (fun x hx => (Subgroup.mem_centralizer_singleton_iff.1 (hJC₂ hx)).symm) with h | h
  · exfalso
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · exact h.symm

theorem layer_lieModel_of_k94Class (h47 : IVK_4_7ab) (hK : K94Class)
    {H : Type} [Group H] [Finite H] {Gs : Type} [Group Gs] {z : H} {t : StatedLieTag} {p' f' : ℕ}
    (h5 : 5 ≤ p' ^ f') (hgen : Gen4 H) (hrk : CFSG.pRank 2 H ≤ 3) (hyp : Hyp94 H Gs z t p' f') :
    LieModel ↥(layer H) t 0 p' f' := by
  obtain ⟨hKgrp, hcore, ht, hp', hp'2, p, f, P, U, hp, hp2, hGs, hSS, hZ, hzU, hUP, hU4, hInv,
    hconj⟩ := hyp
  obtain ⟨hzord, u, huU, huord, huz, -, hPz⟩ := unpack_four_subgroup hZ hzU hUP hU4
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at huord
    exact absurd huord (by norm_num)
  have hzu : IsConj z u := hconj z (hzU (Subgroup.mem_zpowers z)) u huU hzord huord
  obtain ⟨F₁, F₂, _, _, _, _, hcards, ⟨S⟩⟩ :=
    exists_shape_of_isInvolutionCentralizerOfModel h47 ht hp' hp'2 h5 hInv
  have hzS : (S.z : H) = z := shape_z_eq S hzord
  have hodd : Odd (p' ^ f') := (hp'.odd_of_ne_two hp'2).pow
  have h4₁ : 4 ≤ Nat.card F₁ ∧ Odd (Nat.card F₁) := by
    rcases hcards with ⟨-, c1, -⟩ | ⟨-, c1, -⟩
    · rw [c1]
      exact ⟨by omega, hodd⟩
    · rw [c1]
      exact ⟨le_trans (by omega) (Nat.le_self_pow (by norm_num) _), hodd.pow⟩
  have h4₂ : 4 ≤ Nat.card F₂ ∧ Odd (Nat.card F₂) := by
    rcases hcards with ⟨-, -, c2⟩ | ⟨-, -, c2⟩ <;> rw [c2] <;> exact ⟨by omega, hodd⟩
  have hJ₁ := J₁_le_layer hzord hcore S h4₁.1
  have hJ₂ := J₂_le_layer hzord hcore S h4₂.1
  have hO₂ := pCore_two_eq_bot_of_shape S hzS hJ₁ hJ₂ P hPz hu1 huz hzu
  have hne : layer H ≠ ⊥ := by
    intro h
    have hzl : (S.z : H) ∈ layer H := hJ₁ S.zH_mem_J₁
    rw [h, Subgroup.mem_bot] at hzl
    exact S.zH_ne_one hzl
  obtain ⟨hs, hnab⟩ := isSimpleGroup_layer hcore hO₂ hne hrk
  have hcat : Catalog ↥(layer H) :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hKgrp (layer H)
      (MonoidHom.id ↥(layer H)) Function.surjective_id
  have hgen4 : Gen4 ↥(layer H) := Gen4.subgroup (layer H) hgen
  have hle3 : CFSG.pRank 2 ↥(layer H) ≤ 3 := by
    refine le_trans ?_ hrk
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥(layer H),
      CFSG.SectionRank.pRank_eq_open_pRank_top 2 H]
    exact CFSG.SectionRank.pRank_top_le_of_injective Nat.prime_two.one_lt (layer H).subtype
      (layer H).subtype_injective
  have hge3 : 3 ≤ CFSG.pRank 2 ↥(layer H) := by
    obtain ⟨E, hEle, hEc, hE2, hE8⟩ := S.exists_elementary_eight h4₁.2 h4₂.2
    have hEH : E.map (oPrimeResidualOf 2 (centralizer ({z} : Set H))).subtype ≤ layer H := by
      have h1 := Subgroup.map_mono (f := (oPrimeResidualOf 2 (centralizer ({z} : Set H))).subtype) hEle
      rw [Subgroup.map_sup] at h1
      exact h1.trans (sup_le hJ₁ hJ₂)
    refine le_pRank_two_of_comm_sq
      (V := (E.map (oPrimeResidualOf 2 (centralizer ({z} : Set H))).subtype).subgroupOf (layer H))
      ?_ ?_ (k := 3) ?_
    · intro x hx y hy
      rw [Subgroup.mem_subgroupOf] at hx hy
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      apply Subtype.ext
      show (x : H) * y = y * x
      rw [← hax, ← hby]
      exact congrArg Subtype.val (hEc a ha b hb)
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨a, ha, hax⟩ := hx
      apply Subtype.ext
      show (x : H) ^ 2 = 1
      rw [← hax]
      exact congrArg Subtype.val (hE2 a ha)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv,
        Subgroup.card_map_of_injective (oPrimeResidualOf 2 (centralizer ({z} : Set H))).subtype_injective, hE8]
      norm_num
  have htwo : Open.twoRank ↥(layer H) = 3 := by
    have h1 : Open.twoRank ↥(layer H) = CFSG.pRank 2 ↥(layer H) :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥(layer H)).symm
    omega
  have hzK : z ∈ layer H := hzS ▸ hJ₁ S.zH_mem_J₁
  have hJ₁K : S.J₁ ≤ layer H := hJ₁
  have hJ₂K : S.J₂ ≤ layer H := hJ₂
  have hz'ord : orderOf (⟨z, hzK⟩ : ↥(layer H)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hzord
  have hcomm : ∀ x ∈ S.J₁.subgroupOf (layer H), ∀ y ∈ S.J₂.subgroupOf (layer H), x * y = y * x :=
    fun x hx y hy => Subtype.ext (S.J_comm _ hx _ hy)
  have hinter : S.J₁.subgroupOf (layer H) ⊓ S.J₂.subgroupOf (layer H) =
      zpowers (⟨z, hzK⟩ : ↥(layer H)) := by
    have hinf : (S.J₁ ⊓ S.J₂).subgroupOf (layer H) =
        S.J₁.subgroupOf (layer H) ⊓ S.J₂.subgroupOf (layer H) := Subgroup.ext fun x => Iff.rfl
    rw [← hinf, S.J_inf, hzS]
    exact subgroupOf_zpowers (layer H) hzK
  have hnorm : ∀ x : ↥(layer H), (∃ k : ℕ, x ^ 2 ^ k = 1) → x * (⟨z, hzK⟩ : ↥(layer H)) =
      (⟨z, hzK⟩ : ↥(layer H)) * x →
      (∀ a ∈ S.J₁.subgroupOf (layer H), x * a * x⁻¹ ∈ S.J₁.subgroupOf (layer H)) ∧
        (∀ a ∈ S.J₂.subgroupOf (layer H), x * a * x⁻¹ ∈ S.J₂.subgroupOf (layer H)) := by
    rintro x ⟨k, hk⟩ hxz
    have hxC : (x : H) ∈ centralizer ({z} : Set H) :=
      Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hxz)
    have hxk : (x : H) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hxY := mem_oPrimeResidualOf_of_pow hxC hxk
    exact ⟨fun a ha => S.J₁_conj (x : H) hxY (a : H) ha, fun a ha => S.J₂_conj (x : H) hxY (a : H) ha⟩
  have e₁ : Nonempty (↥(S.J₁.subgroupOf (layer H)) ≃* SL(2, F₁)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hJ₁K).trans S.J₁Equiv⟩
  have e₂ : Nonempty (↥(S.J₂.subgroupOf (layer H)) ≃* SL(2, F₂)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hJ₂K).trans S.J₂Equiv⟩
  rcases hcards with ⟨rfl, c1, c2⟩ | ⟨rfl, c1, c2⟩
  · exact hK.1 ↥(layer H) p' f' hs hnab hcat hgen4 htwo hp' hp'2 h5 ⟨z, hzK⟩ _ _ F₁ F₂ hz'ord
      hcomm hinter e₁ e₂ hnorm c1 c2
  · exact hK.2 ↥(layer H) p' f' hs hnab hcat hgen4 htwo hp' hp'2 h5 ⟨z, hzK⟩ _ _ F₁ F₂ hz'ord
      hcomm hinter e₁ e₂ hnorm c1 c2

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94

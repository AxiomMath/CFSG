module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G33RFA7
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Br
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33E

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

section Lift

variable {G : Type} [Group G] [Finite G]

theorem isConj_of_inn_conj_image {C K : Subgroup G} (hKC : K ≤ C)
    (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K))) {f : G} (hfC : f ∈ C)
    (hff : f * f = 1) (hfinn : Back.actHom hKN ⟨f, hfC⟩ ∉ innAut (kBar K)) {u v : G}
    (huM : u ∈ K ⊔ zpowers f) (hvM : v ∈ K ⊔ zpowers f) (hu2 : orderOf u = 2)
    (hv2 : orderOf v = 2) (huC : u ∈ C) (hvC : v ∈ C) {g : MulAut (kBar K)}
    (hg : g ∈ innAut (kBar K))
    (h : g * Back.actHom hKN ⟨u, huC⟩ * g⁻¹ = Back.actHom hKN ⟨v, hvC⟩) : IsConj u v := by
  obtain ⟨kb, rfl⟩ := hg
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective kb
  have hkC : k ∈ C := hKC hk
  have hφk : Back.actHom hKN ⟨k, hkC⟩ =
      MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) := Back.actHom_of_mem hKN hk hkC
  have hkuC : k * u * k⁻¹ ∈ C := C.mul_mem (C.mul_mem hkC huC) (C.inv_mem hkC)
  have hφ : Back.actHom hKN ⟨k * u * k⁻¹, hkuC⟩ = Back.actHom hKN ⟨v, hvC⟩ := by
    have h1 : (⟨k * u * k⁻¹, hkuC⟩ : ↥C) = ⟨k, hkC⟩ * ⟨u, huC⟩ * ⟨k, hkC⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, hφk, ← h]
  have hkM : k ∈ K ⊔ zpowers f := Subgroup.mem_sup_left hk
  have hkuM : k * u * k⁻¹ ∈ K ⊔ zpowers f :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hkM huM) (Subgroup.inv_mem _ hkM)
  have hku2 : orderOf (k * u * k⁻¹) = 2 := by
    rw [← hu2]
    exact (MulAut.conj k).orderOf_eq u
  obtain ⟨h₀, hh₀, hh₀v⟩ := conj_of_same_image hKC hKN hcen hfC hff hfinn hkuM hvM hku2 hv2 hkuC
    hvC hφ
  exact isConj_iff.2 ⟨h₀⁻¹ * k, by rw [← hh₀v]; group⟩

end Lift

section RFLift

theorem rf_lift {X : Type} [Group X] [Finite X] {A : Type} [Group A] [Finite A] (φ : X →* MulAut A)
    (hRF : AutLevelRF A) (T P E₁ : Subgroup X) (hT2 : IsPGroup 2 ↥T) (hPT : P ≤ T)
    (hSyl : IsSylowOf 2 (P.map φ) (innAut A)) (hE₁T : E₁ ≤ T)
    (hE₁ : IsElementaryAbelian 2 ↥E₁) (hE₁16 : 16 ≤ Nat.card ↥E₁)
    (hker : Nat.card ↥(E₁ ⊓ φ.ker) ≤ 2) {f : X} (hfT : f ∈ T) (hf2 : orderOf f = 2)
    (hfc : ∀ p ∈ P, f * p = p * f) (hfinn : φ f ∉ innAut A)
    (hns : 25 ≤ Nat.card ↥(fixedSubgroup A (φ f))) {w : X} (hwP : w ∈ P) (hw2 : orderOf w = 2)
    (hwO : ¬ ∃ c ∈ oResidual 2 ↥(fixedSubgroup A (φ f)),
      (MulAut.conj (c : A) : MulAut A) = φ w) :
    ∃ g ∈ innAut A, g * (φ f * φ w) * g⁻¹ = φ f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut A) :=
    Finite.of_injective (fun σ : MulAut A => (σ : A → A)) (fun a b h => MulEquiv.ext (congrFun h))
  have hB2 : IsPGroup 2 ↥(T.map φ) :=
    hT2.of_surjective (φ.subgroupMap T) (φ.subgroupMap_surjective T)
  have hPB : P.map φ ≤ T.map φ ⊓ innAut A := le_inf (Subgroup.map_mono hPT) hSyl.le
  have hBinn : T.map φ ⊓ innAut A = P.map φ :=
    hSyl.eq_of_le hPB inf_le_right hB2.to_inf_left
  have hSylB : IsSylowOf 2 (T.map φ ⊓ innAut A) (innAut A) := by
    rw [hBinn]
    exact hSyl
  have hEB : E₁.map φ ≤ T.map φ := Subgroup.map_mono hE₁T
  have hE : IsElementaryAbelian 2 ↥(E₁.map φ) := by
    have := hE₁
    exact IsElementaryAbelian.map φ
  have hE8 : 8 ≤ Nat.card ↥(E₁.map φ) := by
    have h := card_eq_card_map_mul_card_inf_ker φ E₁
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(E₁.map φ) * Nat.card ↥(E₁ ⊓ φ.ker) ≤ 7 * 2 :=
      Nat.mul_le_mul (by omega) hker
    omega
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, sq] at this
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, sq] at this
  have hφf1 : φ f ≠ 1 := fun h => hfinn (h ▸ (innAut A).one_mem)
  have hσ2 : orderOf (φ f) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, hff, map_one]) hφf1
  have hσc : ∀ q ∈ T.map φ ⊓ innAut A, φ f * q = q * φ f := by
    intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ : q ∈ P.map φ := hBinn ▸ hq
    rw [← map_mul, ← map_mul, hfc q₀ hq₀]
  have hwB : φ w ∈ T.map φ ⊓ innAut A := hBinn ▸ Subgroup.mem_map_of_mem φ hwP
  have hφw1 : φ w ≠ 1 := fun h =>
    hwO ⟨1, (oResidual 2 ↥(fixedSubgroup A (φ f))).one_mem, by rw [h]; simp⟩
  have hφw2 : orderOf (φ w) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, hww, map_one]) hφw1
  have hσ : φ f ∈ T.map φ := Subgroup.mem_map_of_mem φ hfT
  have := hRF (T.map φ) hB2 hSylB (E₁.map φ) hEB hE hE8 (φ f) hσ hσ2 hfinn hσc hns (φ w) hwB hφw2
    hwO
  exact this

end RFLift

section Fus

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

theorem Env33.not_ex_oRes (E : Env33 x y K T V W f z) {w : G} (hw : w ∈ T ⊓ K)
    (hw2 : orderOf w = 2) (hwI : w ∉ layerI K f) :
    ¬ ∃ c ∈ oResidual 2 ↥(fixedSubgroup (kBar K) (Back.actHom E.hKN ⟨f, E.hfC⟩)),
      (MulAut.conj (c : kBar K) : MulAut (kBar K)) =
        Back.actHom E.hKN ⟨w, E.cfg.setup.sylowT.le hw.1⟩ := by
  rintro ⟨c, hc, hcw⟩
  apply E.not_mem_oRes hw hw2 hwI
  have hφw : Back.actHom E.hKN ⟨w, E.cfg.setup.sylowT.le hw.1⟩ =
      MulAut.conj (QuotientGroup.mk (⟨w, hw.2⟩ : ↥K) : kBar K) :=
    Back.actHom_of_mem E.hKN hw.2 _
  rw [hφw] at hcw
  have hc1 : (c : kBar K) = QuotientGroup.mk (⟨w, hw.2⟩ : ↥K) := E.hcen hcw
  have : c = centMap E.hKN E.hfC ⟨w, ⟨hw.2, mem_centralizer_singleton_iff.2 (E.hfP w hw).symm⟩⟩ :=
    Subtype.ext (by rw [centMap_apply]; exact hc1)
  rw [← this]
  exact hc

theorem Env33.card_fixed_ge (E : Env33 x y K T V W f z) :
    25 ≤ Nat.card ↥(fixedSubgroup (kBar K) (Back.actHom E.hKN ⟨f, E.hfC⟩)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := K ⊓ centralizer ({f} : Set G) with hX
  have hIX : layerI K f ≤ X := TwoThin.pLayerOf_le 2 _
  set cm := centMap E.hKN E.hfC with hcm
  let ρI : ↥(layerI K f) →* ↥(fixedSubgroup (kBar K) (Back.actHom E.hKN ⟨f, E.hfC⟩)) :=
    cm.comp (Subgroup.inclusion hIX)
  have hkerodd : Odd (Nat.card ρI.ker) := by
    have h1 : ρI.ker.map (Subgroup.inclusion hIX) ≤ cm.ker := by
      rintro _ ⟨a, ha, rfl⟩
      exact ha
    have h2 := Subgroup.card_dvd_of_le h1
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hIX)] at h2
    exact Odd.of_dvd_nat (centMap_ker_odd E.hKN E.hfC) h2
  have hkerle : ρI.ker ≤ pPrimeCore 2 ↥(layerI K f) :=
    GroupTheory.le_pPrimeCore_of_normal (MonoidHom.normal_ker ρI) (Nat.coprime_two_left.2 hkerodd)
  have hI : Nat.card ↥(layerI K f) = Nat.card ↥ρI.range * Nat.card ↥ρI.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρI.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρI).toEquiv]
  have hI' : Nat.card ↥(layerI K f) =
      Nat.card (pPrimeCore 2 ↥(layerI K f)) * Nat.card (kBar (layerI K f)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥(layerI K f)), mul_comm]
  have hle : Nat.card ↥ρI.ker ≤ Nat.card (pPrimeCore 2 ↥(layerI K f)) :=
    Subgroup.card_le_of_le hkerle
  have hkpos : 0 < Nat.card ↥ρI.ker := Nat.card_pos
  have hM : Nat.card (kBar (layerI K f)) ≤ Nat.card ↥ρI.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥ρI.range * Nat.card ↥ρI.ker <
        Nat.card (kBar (layerI K f)) * Nat.card (pPrimeCore 2 ↥(layerI K f)) :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hlt (le_refl _) hkpos)
        (Nat.mul_le_mul (le_refl _) hle)
    rw [← hI, hI', mul_comm] at this
    exact lt_irrefl _ this
  have hrange : Nat.card ↥ρI.range ≤
      Nat.card ↥(fixedSubgroup (kBar K) (Back.actHom E.hKN ⟨f, E.hfC⟩)) :=
    Subgroup.card_le_card_group _
  obtain ⟨r, hrodd, hr5, hIm, -⟩ := E.hr
  have h60 : 60 ≤ Nat.card (kBar (layerI K f)) := by
    rw [Thm1L34.card_kBar_of_hasL2Model hIm]
    obtain ⟨k, hk⟩ := hrodd
    have hk2 : 2 ≤ k := by omega
    rw [hk, PumpClass.ordA_one_odd]
    have h : 2 * 2 * (2 + 1) * (2 * 2 + 1) ≤ 2 * k * (k + 1) * (2 * k + 1) := by gcongr
    omega
  omega

theorem Env33.conj_fw_f (E : Env33 x y K T V W f z) (hG : C3Hyp G) (hRF : AutLevelRF (kBar K))
    {w : G} (hw : w ∈ T ⊓ K) (hw2 : orderOf w = 2) (hwI : w ∉ layerI K f) :
    IsConj (f * w) f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hKC : K ≤ C := E.cfg.hKx
  have hTC : T ≤ C := E.cfg.setup.sylowT.le
  have hPC : T ⊓ K ≤ C := inf_le_right.trans hKC
  have hfC : f ∈ C := E.hfC
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ :=
    exists_E₁ E.cfg.setup.sylowT (by rw [E.cfg.hu2.2.2.1.2, hG.pRank_eq_four])
  have hE₁C : E₁ ≤ C := hE₁T.trans hTC
  set φ := Back.actHom E.hKN with hφ
  have hT2 : IsPGroup 2 ↥(T.subgroupOf C) := E.cfg.setup.sylowT.isPGroup.comap_subtype
  have hPT : (T ⊓ K).subgroupOf C ≤ T.subgroupOf C := fun a ha =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 ha).1
  have hSylK : IsSylowOf 2 ((T ⊓ K).subgroupOf C) (K.subgroupOf C) := by
    have hCN : C ≤ normalizer (K : Set G) := fun c hc => U1a.mem_normalizer_of_norm E.hKN hc
    have h := E.cfg.setup.sylowT.inf_of_le_normalizer hKC hCN
    rw [← isSylowOf_map_subtype_iff C, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPC, inf_eq_left.2 hKC]
    exact h
  have hSyl : IsSylowOf 2 (((T ⊓ K).subgroupOf C).map φ) (innAut (kBar K)) := by
    have := isSylowOf_map_hom φ hSylK
    rwa [hφ, map_actHom_K hKC E.hKN] at this
  have hE₁T' : E₁.subgroupOf C ≤ T.subgroupOf C := fun a ha =>
    Subgroup.mem_subgroupOf.2 (hE₁T (Subgroup.mem_subgroupOf.1 ha))
  have hE₁' : IsElementaryAbelian 2 ↥(E₁.subgroupOf C) := by
    have := hE₁
    exact IsElementaryAbelian.subgroupOf hE₁C
  have hE₁16' : 16 ≤ Nat.card ↥(E₁.subgroupOf C) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁C).toEquiv]
    exact hE₁16
  have hker : Nat.card ↥(E₁.subgroupOf C ⊓ φ.ker) ≤ 2 := by
    have hinf : E₁.subgroupOf C ⊓ (CMK C K).subgroupOf C = (E₁ ⊓ CMK C K).subgroupOf C := by
      ext a
      simp [Subgroup.mem_subgroupOf]
    rw [hφ, Back.actHom_ker E.hKN, hinf]
    have hle : E₁ ⊓ CMK C K ≤ C := inf_le_left.trans hE₁C
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    obtain ⟨hab, hsq⟩ := Back.forall_of_isElementaryAbelian hE₁
    exact E.hQ2 _ inf_le_right (Back.isElementaryAbelian_of_forall
      (fun u hu v hv => hab u hu.1 v hv.1) (fun u hu => hsq u hu.1))
  have hfCT : (⟨f, hfC⟩ : ↥C) ∈ T.subgroupOf C := E.cfg.mem.1
  have hf2' : orderOf (⟨f, hfC⟩ : ↥C) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact E.cfg.hf2
  have hfc' : ∀ p ∈ (T ⊓ K).subgroupOf C, (⟨f, hfC⟩ : ↥C) * p = p * ⟨f, hfC⟩ := fun p hp =>
    Subtype.ext (E.hfP p hp)
  have hwP : (⟨w, hPC hw⟩ : ↥C) ∈ (T ⊓ K).subgroupOf C := hw
  have hw2' : orderOf (⟨w, hPC hw⟩ : ↥C) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hw2
  obtain ⟨g, hg, hgeq⟩ := rf_lift φ hRF (T.subgroupOf C) ((T ⊓ K).subgroupOf C)
    (E₁.subgroupOf C) hT2 hPT hSyl hE₁T' hE₁' hE₁16' hker hfCT hf2' hfc' E.hfout
    E.card_fixed_ge hwP hw2' (E.not_ex_oRes hw hw2 hwI)
  have hfwC : f * w ∈ C := C.mul_mem hfC (hPC hw)
  have hφfw : φ ⟨f * w, hfwC⟩ = φ ⟨f, hfC⟩ * φ ⟨w, hPC hw⟩ := by
    have h1 := (Back.actHom E.hKN).map_mul ⟨f, hfC⟩ ⟨w, hPC hw⟩
    exact h1
  have hfw : f * w = w * f := E.hfP w hw
  have hff : f * f = 1 := E.hf2'
  have hφw : φ ⟨w, hPC hw⟩ ∈ innAut (kBar K) := by
    rw [Back.actHom_of_mem E.hKN hw.2 (hPC hw)]
    exact ⟨_, rfl⟩
  have hfw1 : f * w ≠ 1 := by
    intro h
    apply E.hfout
    have h1 : φ ⟨f * w, hfwC⟩ = 1 := by
      have : (⟨f * w, hfwC⟩ : ↥C) = 1 := Subtype.ext h
      rw [this, map_one]
    rw [hφfw] at h1
    have h2 : φ ⟨f, hfC⟩ = (φ ⟨w, hPC hw⟩)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact (innAut (kBar K)).inv_mem hφw
  have hfw2 : orderOf (f * w) = 2 :=
    orderOf_mul_eq_two_of_commute E.cfg.hf2 hw2 hfw hfw1
  refine isConj_of_inn_conj_image hKC E.hKN E.hcen hfC hff E.hfout
    (Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers f)) (Subgroup.mem_sup_left hw.2))
    (Subgroup.mem_sup_right (mem_zpowers f)) hfw2 E.cfg.hf2 hfwC hfC hg ?_
  rw [hφfw]
  exact hgeq

theorem Env33.conj_w_z (E : Env33 x y K T V W f z) (hG : C3Hyp G) {w : G} (hw : w ∈ T ⊓ K)
    (hw2 : orderOf w = 2) : IsConj w z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hKC : K ≤ C := E.cfg.hKx
  have hTC : T ≤ C := E.cfg.setup.sylowT.le
  have hPC : T ⊓ K ≤ C := inf_le_right.trans hKC
  have hfC : f ∈ C := E.hfC
  have hzC : z ∈ C := hPC E.hzP
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ :=
    exists_E₁ E.cfg.setup.sylowT (by rw [E.cfg.hu2.2.2.1.2, hG.pRank_eq_four])
  obtain ⟨f₁, z₁, -, -, -, -, -, -, -, hz₁, hz₁2, hz₁c, hz₁u, hfus, -, -⟩ :=
    core_lift_G E.cfg.hKx E.hKN E.cfg.setup.sylowT E.hcen E.hAut hE₁T hE₁ hE₁16 E.hQ2
  have hzP : (⟨z, hzC⟩ : ↥C) ∈ (T ⊓ K).subgroupOf C := E.hzP
  have hzz₁ : (⟨z, hzC⟩ : ↥C) = z₁ := by
    rcases hz₁u ⟨z, hzC⟩ hzP (fun q hq => Subtype.ext (by
      have hq' : (q : G) ∈ T ⊓ K := hq
      exact (E.cfg.z_mem.2.2 (q : G) hq'.1).symm)) with h | h
    · exfalso
      have : z = 1 := congrArg Subtype.val h
      exact E.hz1 this
    · exact h
  have hfCT : (⟨f, hfC⟩ : ↥C) ∈ T.subgroupOf C := E.cfg.mem.1
  have hfC2 : orderOf (⟨f, hfC⟩ : ↥C) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact E.cfg.hf2
  have hfCc : ∀ p ∈ (T ⊓ K).subgroupOf C, (⟨f, hfC⟩ : ↥C) * p = p * ⟨f, hfC⟩ := fun p hp =>
    Subtype.ext (E.hfP p hp)
  have hwP' : (⟨w, hPC hw⟩ : ↥C) ∈ (T ⊓ K).subgroupOf C ⊔ zpowers (⟨f, hfC⟩ : ↥C) :=
    Subgroup.mem_sup_left hw
  have hw2' : orderOf (⟨w, hPC hw⟩ : ↥C) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hw2
  obtain ⟨g, hg, hgu⟩ := hfus ⟨f, hfC⟩ hfCT hfC2 hfCc E.hfout ⟨w, hPC hw⟩ hwP' hw2'
  rw [← hzz₁] at hgu
  have hφw : Back.actHom E.hKN ⟨w, hPC hw⟩ ∈ innAut (kBar K) := by
    rw [Back.actHom_of_mem E.hKN hw.2 (hPC hw)]
    exact ⟨_, rfl⟩
  have hφz : Back.actHom E.hKN ⟨z, hzC⟩ ∈ innAut (kBar K) := by
    rw [Back.actHom_of_mem E.hKN E.hzP.2 hzC]
    exact ⟨_, rfl⟩
  have hgw : g * Back.actHom E.hKN ⟨w, hPC hw⟩ * g⁻¹ ∈ innAut (kBar K) :=
    (innAut (kBar K)).mul_mem ((innAut (kBar K)).mul_mem hg hφw) ((innAut (kBar K)).inv_mem hg)
  rcases hgu with h | h | h
  · exact isConj_of_inn_conj_image E.cfg.hKx E.hKN E.hcen hfC E.hf2' E.hfout
      (Subgroup.mem_sup_left hw.2) (Subgroup.mem_sup_left E.hzP.2) hw2 E.hz2 (hPC hw) hzC hg h
  · exfalso
    apply E.hfout
    rw [← h]
    exact hgw
  · exfalso
    apply E.hfout
    have h1 : Back.actHom E.hKN ⟨f, hfC⟩ =
        (g * Back.actHom E.hKN ⟨w, hPC hw⟩ * g⁻¹) * (Back.actHom E.hKN ⟨z, hzC⟩)⁻¹ := by
      rw [h]; group
    rw [h1]
    exact (innAut (kBar K)).mul_mem hgw ((innAut (kBar K)).inv_mem hφz)

theorem Env33.fus33_of_rf (E : Env33 x y K T V W f z) (hG : C3Hyp G) (hRF : AutLevelRF (kBar K)) :
    Fus33 K T f z := fun _w hw hw2 hwI =>
  ⟨E.conj_w_z hG hw hw2, E.conj_fw_f hG hRF hw hw2 hwI⟩

theorem Env33.fus33 (h2hb : IVK_1_2h_b)
    (E : Env33 x y K T V W f z) (hG : C3Hyp G) : Fus33 K T f z := by
  refine E.fus33_of_rf hG ?_
  rcases E.hshape with h | ⟨⟨e7⟩⟩
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_l2_model_of_hasL2Model h
    exact autLevelRF_of_L2 h2hb hF e
  · exact autLevelRF_of_A7 e7

end Fus

end CFSG.GH74.GLS.C3.Layer1.Thm1G33


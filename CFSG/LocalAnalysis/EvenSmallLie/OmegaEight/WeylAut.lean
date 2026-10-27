module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCover

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] def quotientOmegaEquiv : wPlus ⧸ center wPlus ≃* omegaT :=
  quotientCenterEquiv.trans omegaRestrictEquiv.symm

@[expose] def pHat : wPlus →* omegaT :=
  quotientOmegaEquiv.toMonoidHom.comp (QuotientGroup.mk' (center wPlus))

theorem pHat_apply (x : wPlus) : pHat x = omegaRestrictEquiv.symm (pOnto x) := rfl

theorem omegaRestrictEquiv_pHat (x : wPlus) : omegaRestrictEquiv (pHat x) = pOnto x := by
  rw [pHat_apply, MulEquiv.apply_symm_apply]

theorem pHat_surjective : Function.Surjective pHat :=
  quotientOmegaEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

theorem pHat_eq_iff {x y : wPlus} : pHat x = pHat y ↔ y = x ∨ y = x * zPlus := by
  rw [pHat_apply, pHat_apply, omegaRestrictEquiv.symm.injective.eq_iff]
  constructor
  · intro h
    have hk : x⁻¹ * y ∈ pPlus.ker := by
      rw [← ker_pOnto, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rcases mem_ker_pPlus.1 hk with h1 | h1
    · exact Or.inl (by rw [← mul_inv_cancel_left x y, h1, mul_one])
    · exact Or.inr (by rw [← mul_inv_cancel_left x y, h1])
  · rintro (rfl | rfl)
    · rfl
    · rw [map_mul, show pOnto zPlus = 1 from (MonoidHom.mem_ker).1 (ker_pOnto ▸ zPlus_mem_ker),
        mul_one]

@[expose] def autHom : MulAut wPlus →* MulAut omegaT :=
  (MulAut.congr quotientOmegaEquiv).toMonoidHom.comp (centerQuotientHom wPlus)

theorem autHom_pHat (φ : MulAut wPlus) (x : wPlus) : autHom φ (pHat x) = pHat (φ x) := by
  change quotientOmegaEquiv (onCenterQuotient φ (quotientOmegaEquiv.symm
    (quotientOmegaEquiv (QuotientGroup.mk' (center wPlus) x)))) = _
  rw [MulEquiv.symm_apply_apply, onCenterQuotient_apply_mk]
  rfl

theorem autHom_injective : Function.Injective autHom :=
  (MulAut.congr quotientOmegaEquiv).injective.comp (centerQuotientHom_injective wPlus)

instance finite_mulAut_wPlus : Finite (MulAut wPlus) :=
  haveI := finite_mulAut_omegaT
  Finite.of_injective _ autHom_injective

theorem coe_pOnto (x : wPlus) : ((pOnto x : omega1T) : Equiv.Perm (Fin 120)) = pPlus x := rfl

theorem pHat_omLift {i : ℕ} (hi : i < 8) :
    pHat ⟨omLift i, omLift_mem hi⟩ = ⟨gen i, gen_mem_omegaT hi⟩ := by
  apply omegaRestrictEquiv.injective
  rw [omegaRestrictEquiv_pHat]
  apply Subtype.ext
  rw [coe_pOnto, pPlus_omLift hi, omegaRestrictEquiv_apply, omegaRes_gen hi]

theorem pHat_uPlus : pHat uPlus =
    ⟨gen 4, gen_mem_omegaT (by norm_num)⟩ * ⟨gen 6, gen_mem_omegaT (by norm_num)⟩ := by
  rw [← pHat_omLift (by norm_num : 4 < 8), ← pHat_omLift (by norm_num : 6 < 8), ← map_mul]
  rfl

theorem pHat_yPlus : pHat yPlus =
    ⟨gen 6, gen_mem_omegaT (by norm_num)⟩ * ⟨gen 0, gen_mem_omegaT (by norm_num)⟩ := by
  rw [← pHat_omLift (by norm_num : 6 < 8), ← pHat_omLift (by norm_num : 0 < 8), ← map_mul]
  rfl

@[expose] def rhoA : autT := ⟨gen 8, gen_mem_autT (by norm_num)⟩

theorem autEquiv_rhoA_uPlus : autEquiv rhoA (pHat uPlus) = pHat yPlus := by
  apply Subtype.ext
  rw [autEquiv_apply, pHat_uPlus, pHat_yPlus]
  change gen 8 * (gen 4 * gen 6) * (gen 8)⁻¹ = gen 6 * gen 0
  rw [show gen 8 * (gen 4 * gen 6) * (gen 8)⁻¹ =
      (gen 8 * gen 4 * (gen 8)⁻¹) * (gen 8 * gen 6 * (gen 8)⁻¹) by group,
    conj_gen_rho (by norm_num : 4 < 8), conj_gen_rho (by norm_num : 6 < 8)]
  rfl

theorem rhoT_not_mem (φ : MulAut wPlus) : autHom φ ≠ autEquiv rhoA := by
  intro h
  have h1 : pHat (φ uPlus) = pHat yPlus := by
    rw [← autHom_pHat, h, autEquiv_rhoA_uPlus]
  have hu : φ uPlus * φ uPlus = 1 := by rw [← map_mul, uPlus_mul_self, map_one]
  apply yPlus_mul_self_ne
  rcases pHat_eq_iff.1 h1 with h2 | h2
  · rw [h2, hu]
  · have hzc := mem_center_iff.1 zPlus_mem_center (φ uPlus)
    have hzz : zPlus * zPlus = 1 := Subtype.ext zPerm_mul_self
    rw [h2, show φ uPlus * zPlus * (φ uPlus * zPlus) = φ uPlus * (zPlus * φ uPlus) * zPlus by
      group, ← hzc, show φ uPlus * (φ uPlus * zPlus) * zPlus =
        φ uPlus * φ uPlus * (zPlus * zPlus) by group, hzz, hu, mul_one]

theorem card_le_two_mul_of_not_mem {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) (hG : Nat.card G = 6 * Nat.card H) {r : G} (hr3 : r ^ 3 = 1) (hr : r ∉ K) :
    Nat.card K ≤ 2 * Nat.card H := by
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hHK
  have hidx := Subgroup.card_mul_index K
  rw [hG, hd] at hidx
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hdm : d * K.index = 6 := by
    have : Nat.card H * (d * K.index) = Nat.card H * 6 := by rw [← mul_assoc, hidx, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  rcases Nat.lt_or_ge K.index 3 with h3 | h3
  · exfalso
    interval_cases hk : K.index
    · rw [mul_zero] at hdm
      exact absurd hdm (by norm_num)
    · exact hr ((Subgroup.index_eq_one.1 hk) ▸ mem_top r)
    · apply hr
      have hsq := Subgroup.sq_mem_of_index_two hk (r ^ 2)
      rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hr3, one_mul] at hsq
  · rw [hd]
    have hd2 : d ≤ 2 := by
      by_contra h
      push Not at h
      have : 3 * 3 ≤ d * K.index := Nat.mul_le_mul h h3
      omega
    nlinarith

@[expose] def autImage : Subgroup autT := autHom.range.comap autEquiv.toMonoidHom

theorem card_autImage : Nat.card autImage = Nat.card (MulAut wPlus) := by
  have e1 : autImage ≃ autHom.range :=
    { toFun a := ⟨autEquiv a, a.2⟩
      invFun b := ⟨autEquiv.symm b, by
        change autEquiv (autEquiv.symm (b : MulAut omegaT)) ∈ autHom.range
        rw [MulEquiv.apply_symm_apply]
        exact b.2⟩
      left_inv a := by simp
      right_inv b := by simp }
  rw [Nat.card_congr e1, Nat.card_congr (MonoidHom.ofInjective autHom_injective).toEquiv.symm]

theorem autHom_conj (x : wPlus) : autHom (MulAut.conj x) = MulAut.conj (pHat x) := by
  ext ω
  obtain ⟨y, rfl⟩ := pHat_surjective ω
  rw [autHom_pHat, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem omegaT_le_autImage : omegaT.subgroupOf autT ≤ autImage := by
  intro a ha
  rw [mem_subgroupOf] at ha
  obtain ⟨x, hx⟩ := pHat_surjective ⟨a, ha⟩
  refine ⟨MulAut.conj x, ?_⟩
  change autHom (MulAut.conj x) = autEquiv a
  rw [autHom_conj, hx]
  ext g
  rw [autEquiv_apply, MulAut.conj_apply]
  rfl

theorem gen8_pow_three : gen 8 ^ 3 = 1 := Equiv.ext fun q => Fin.ext (by
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, gen8_val, Equiv.Perm.one_apply]
  omega)

theorem rhoA_pow_three : rhoA ^ 3 = 1 := Subtype.ext (by
  rw [Subgroup.coe_pow]
  exact gen8_pow_three)

theorem rhoA_not_mem : rhoA ∉ autImage := fun ⟨φ, hφ⟩ => rhoT_not_mem φ hφ

theorem card_subgroupOf_of_le {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

theorem card_mulAut_wPlus_le : Nat.card (MulAut wPlus) ≤ 348364800 := by
  rw [← card_autImage]
  have hG : Nat.card autT = 6 * Nat.card (omegaT.subgroupOf autT) := by
    rw [card_autT_eq, card_subgroupOf_of_le omegaT_le_autT]
  have := card_le_two_mul_of_not_mem omegaT_le_autImage hG rhoA_pow_three rhoA_not_mem
  rwa [card_subgroupOf_of_le omegaT_le_autT, card_omegaT] at this

theorem conj_mem_wPlus {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8) {x : Equiv.Perm (Fin 240)}
    (hx : x ∈ wPlus) : w * x * w⁻¹ ∈ wPlus := by
  obtain ⟨hx1, hx2⟩ := mem_wPlus_iff.1 hx
  refine mem_wPlus_iff.2 ⟨mul_mem (mul_mem hw hx1) (inv_mem hw), ?_⟩
  rw [map_mul, map_mul, map_inv, hx2, mul_one, mul_inv_cancel]

@[expose] def conjAut : wE8 →* MulAut wPlus where
  toFun w :=
    { toFun x := ⟨w * x * (w : Equiv.Perm (Fin 240))⁻¹, conj_mem_wPlus w.2 x.2⟩
      invFun x := ⟨(w : Equiv.Perm (Fin 240))⁻¹ * x * w, by
        simpa using conj_mem_wPlus (inv_mem w.2) x.2⟩
      left_inv x := Subtype.ext (by simp [mul_assoc])
      right_inv x := Subtype.ext (by simp [mul_assoc])
      map_mul' x y := Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext x
    simp
  map_mul' w v := by
    ext x
    simp [mul_assoc]

theorem conjAut_apply (w : wE8) (x : wPlus) :
    ((conjAut w x : wPlus) : Equiv.Perm (Fin 240)) = w * x * (w : Equiv.Perm (Fin 240))⁻¹ := rfl

theorem mem_ker_conjAut {w : wE8} : w ∈ conjAut.ker ↔
    (w : Equiv.Perm (Fin 240)) = 1 ∨ (w : Equiv.Perm (Fin 240)) = zPerm := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    refine centralizer_wPlus w.2 fun x hx => ?_
    have := congrArg (fun φ : MulAut wPlus => ((φ ⟨x, hx⟩ : wPlus) : Equiv.Perm (Fin 240))) h
    simp only [conjAut_apply, MulAut.one_apply] at this
    calc (w : Equiv.Perm (Fin 240)) * x = w * x * (w : Equiv.Perm (Fin 240))⁻¹ * w := by group
      _ = x * w := by rw [this]
  · rintro (h | h)
    · ext x
      rw [conjAut_apply, h, one_mul, inv_one, mul_one]
      rfl
    · ext x
      rw [conjAut_apply, h, ← zPerm_comm x (wPlus_le x.2), mul_assoc, mul_inv_cancel, mul_one]
      rfl

theorem card_ker_conjAut : Nat.card conjAut.ker = 2 := by
  have e : conjAut.ker ≃ ({1, zPerm} : Finset (Equiv.Perm (Fin 240))) :=
    { toFun w := ⟨w.1.1, by
        rcases mem_ker_conjAut.1 w.2 with h | h <;> simp [h]⟩
      invFun g := ⟨⟨g.1, by
          rcases Finset.mem_insert.1 g.2 with h | h
          · rw [h]
            exact one_mem _
          · rw [Finset.mem_singleton.1 h]
            exact zPerm_mem_wE8⟩, by
        rw [mem_ker_conjAut]
        rcases Finset.mem_insert.1 g.2 with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_singleton.1 h)⟩
      left_inv w := rfl
      right_inv g := rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_pair (Ne.symm zPerm_ne_one)]

theorem card_mulAut_wPlus : Nat.card (MulAut wPlus) = 348364800 := by
  refine le_antisymm card_mulAut_wPlus_le ?_
  have h1 := Subgroup.card_mul_index conjAut.ker
  rw [Subgroup.index_ker, card_ker_conjAut, card_wE8] at h1
  have h2 : Nat.card conjAut.range = 348364800 := by omega
  rw [← h2]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

theorem conjAut_surjective : Function.Surjective conjAut := by
  have h1 := Subgroup.card_mul_index conjAut.ker
  rw [Subgroup.index_ker, card_ker_conjAut, card_wE8] at h1
  have h2 : Nat.card conjAut.range = Nat.card (MulAut wPlus) := by
    rw [card_mulAut_wPlus]
    omega
  have htop : conjAut.range = ⊤ := Subgroup.eq_top_of_card_eq _ h2
  exact MonoidHom.range_eq_top.1 htop

theorem exists_conj_eq (φ : MulAut wPlus) :
    ∃ w ∈ wE8, ∀ x : wPlus, ((φ x : wPlus) : Equiv.Perm (Fin 240)) = w * x * w⁻¹ := by
  obtain ⟨w, rfl⟩ := conjAut_surjective φ
  exact ⟨w, w.2, fun x => conjAut_apply w x⟩

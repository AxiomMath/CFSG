module

public import CFSG.CGT.Timmesfeld75.L2Aut

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section Involution

theorem exists_fixedPoint_of_involutive_of_odd {α : Type*} [Finite α] {f : α → α}
    (hf : Function.Involutive f) (hodd : Odd (Nat.card α)) : ∃ x, f x = x := by
  have := Fintype.ofFinite α
  let σ : Equiv.Perm α := hf.toPerm f
  have hσ : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    ext x
    exact hf x
  have h2 : ¬ 2 ∣ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card]
    exact hodd.not_two_dvd_nat
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) h2 hσ
  exact ⟨x, hx⟩

theorem exists_fixed_ne_one_of_involution {G : Type*} [Group G] [Finite G] {W : Subgroup G}
    (hW : W ≠ ⊥) (hWp : IsPGroup 2 W) {a : G} (haa : a * a = 1)
    (haW : ∀ w ∈ W, a * w * a⁻¹ ∈ W) : ∃ w ∈ W, w ≠ 1 ∧ a * w * a⁻¹ = w := by
  have hne : ∀ w : {w : ↥W // w ≠ 1}, a * (w.1 : G) * a⁻¹ ≠ 1 := fun w h1 => w.2 (Subtype.ext (by
    have : (w.1 : G) = a⁻¹ * (a * (w.1 : G) * a⁻¹) * a := by group
    rw [Subgroup.coe_one, this, h1]
    group))
  let f : {w : ↥W // w ≠ 1} → {w : ↥W // w ≠ 1} := fun w =>
    ⟨⟨a * (w.1 : G) * a⁻¹, haW _ w.1.2⟩, fun h1 => hne w (congrArg Subtype.val h1)⟩
  have hf : Function.Involutive f := fun w => by
    apply Subtype.ext
    apply Subtype.ext
    show a * (a * (w.1 : G) * a⁻¹) * a⁻¹ = w.1
    calc a * (a * (w.1 : G) * a⁻¹) * a⁻¹ = (a * a) * (w.1 : G) * (a * a)⁻¹ := by group
      _ = w.1 := by rw [haa]; group
  have hodd : Odd (Nat.card {w : ↥W // w ≠ 1}) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hWp
    have hn0 : n ≠ 0 := by
      rintro rfl
      have h1 := (Subgroup.one_lt_card_iff_ne_bot W).2 hW
      rw [hn] at h1
      simp at h1
    classical
    have := Fintype.ofFinite ↥W
    have hc : Nat.card {w : ↥W // w ≠ 1} = Nat.card W - 1 := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      have h1 := Fintype.card_subtype_compl (fun w : ↥W => w = 1)
      rw [Fintype.card_subtype_eq] at h1
      simp
    rw [hc, hn]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    exact ⟨2 ^ m - 1, by rw [pow_succ]; omega⟩
  obtain ⟨w, hw⟩ := exists_fixedPoint_of_involutive_of_odd hf hodd
  exact ⟨(w.1 : G), w.1.2, fun h1 => w.2 (Subtype.ext h1), congrArg (fun z => (z.1.1 : G)) hw⟩

end Involution

section SL

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sl2_exists_utriElt_of_unique_fixed (ψ : SL(2, F) ≃* SL(2, F)) (hψ : ∀ x, ψ (ψ x) = x)
    (hU : (utri F).map ψ.toMonoidHom = utri F)
    (huniq : ∀ g, (conjSubgroup g (utri F)).map ψ.toMonoidHom = conjSubgroup g (utri F) →
      conjSubgroup g (utri F) = utri F) :
    ∃ μ : F, μ ≠ 0 ∧ ∀ x, ψ x = utriElt μ * x * (utriElt μ)⁻¹ := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨g, σ, hg⟩ := exists_eq_conj_sl2FieldAut ψ
  have hgB : g ∈ borel F := by
    by_contra hgB
    have h1 : ψ (utriElt 1) ∈ utri F := by
      have : ψ (utriElt 1) ∈ (utri F).map ψ.toMonoidHom :=
        Subgroup.mem_map_of_mem _ (utriElt_mem_utri 1)
      rwa [hU] at this
    have h2' : ψ (utriElt 1) ∈ conjSubgroup g (utri F) := by
      rw [hg, sl2FieldAut_utriElt, map_one]
      exact conj_mem_conjSubgroup g (utriElt_mem_utri 1)
    have h4 : ψ (utriElt 1) ∈ utri F ⊓ conjSubgroup g (utri F) := ⟨h1, h2'⟩
    rw [utri_inf_conj_eq_bot hgB, Subgroup.mem_bot] at h4
    have : utriElt (1 : F) = 1 := ψ.injective (by rw [h4, map_one])
    exact utriElt_ne_one one_ne_zero this
  obtain ⟨μ, c, hgc⟩ : ∃ (μ : F) (c : Fˣ), g = utriElt μ * torusElt c := by
    have h10 : g 1 0 = 0 := hgB
    have hd := sl2_det g
    have ha0 : g 0 0 ≠ 0 := by
      intro h0
      rw [h0, h10] at hd
      simp at hd
    have e01 : g 0 0 * g 0 1 * (g 0 0)⁻¹ = g 0 1 := by field_simp
    have e11 : (g 0 0)⁻¹ = g 1 1 :=
      inv_eq_of_mul_eq_one_right (by linear_combination hd + g 0 1 * h10)
    refine ⟨g 0 0 * g 0 1, Units.mk0 (g 0 0) ha0, ?_⟩
    apply sl2_ext
    all_goals sl2_simp
    all_goals simp only [Units.val_mk0, Units.val_inv_eq_inv_val]
    · ring
    · linear_combination (-1 : F) * e01
    · rw [h10]
      ring
    · linear_combination (-1 : F) * e11
  have hψu : ∀ s : F, ψ (utriElt s) = utriElt ((c : F) ^ 2 * σ s) := by
    intro s
    rw [hg, sl2FieldAut_utriElt, hgc]
    calc utriElt μ * torusElt c * utriElt (σ s) * (utriElt μ * torusElt c)⁻¹
        = utriElt μ * (torusElt c * utriElt (σ s) * (torusElt c)⁻¹) * (utriElt μ)⁻¹ := by group
      _ = utriElt μ * utriElt ((c : F) ^ 2 * σ s) * (utriElt μ)⁻¹ := by
        rw [torusElt_mul_utriElt_mul_inv]
      _ = utriElt ((c : F) ^ 2 * σ s) := by
        rw [utriElt_inv, ← utriElt_add, ← utriElt_add]
        congr 1
        ring
  have hL : (ltri F).map ψ.toMonoidHom = conjSubgroup (utriElt μ) (ltri F) := by
    have hle : (ltri F).map ψ.toMonoidHom ≤ conjSubgroup (utriElt μ) (ltri F) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨r, rfl⟩ := mem_ltri_iff.1 hx
      show ψ (ltriElt r) ∈ _
      rw [hg, sl2FieldAut_ltriElt, hgc]
      have e1 : (utriElt μ * torusElt c) * ltriElt (σ r) * (utriElt μ * torusElt c)⁻¹ =
          utriElt μ * (torusElt c * ltriElt (σ r) * (torusElt c)⁻¹) * (utriElt μ)⁻¹ := by group
      rw [e1]
      exact conj_mem_conjSubgroup _ (conj_torusElt_mem_ltri (ltriElt_mem_ltri _))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_conjSubgroup, Subgroup.card_map_of_injective ψ.injective]
  have hP : ∀ x : F, (conjSubgroup (utriElt x) (ltri F)).map ψ.toMonoidHom =
      conjSubgroup (utriElt ((c : F) ^ 2 * σ x + μ)) (ltri F) := by
    intro x
    rw [map_conjSubgroup_mulEquiv, hψu, hL, conjSubgroup_conjSubgroup, ← utriElt_add]
  have hPne : ∀ x : F, conjSubgroup (utriElt x * wElt) (utri F) ≠ utri F := by
    intro x h
    have hmem : utriElt x * wElt ∈ Subgroup.normalizer (utri F : Set SL(2, F)) :=
      mem_normalizer_iff_conjSubgroup_eq.2 h
    rw [normalizer_utri] at hmem
    have h10 : (utriElt x * wElt : SL(2, F)) 1 0 = 0 := hmem
    rw [mul_apply_10, utriElt_apply_10, utriElt_apply_11, wElt_apply_00, wElt_apply_10] at h10
    simp at h10
  have hnofix : ∀ x : F, (c : F) ^ 2 * σ x + μ ≠ x := by
    intro x hx
    have hfix : (conjSubgroup (utriElt x * wElt) (utri F)).map ψ.toMonoidHom =
        conjSubgroup (utriElt x * wElt) (utri F) := by
      rw [← conjSubgroup_conjSubgroup, conjSubgroup_wElt_utri, hP x, hx]
    exact hPne x (huniq _ hfix)
  have hmm : ∀ H : Subgroup SL(2, F), (H.map ψ.toMonoidHom).map ψ.toMonoidHom = H := by
    intro H
    rw [Subgroup.map_map]
    have : ψ.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id _ := MonoidHom.ext hψ
    rw [this, Subgroup.map_id]
  have hc2 : (c : F) ^ 2 * σ ((c : F) ^ 2) = 1 := by
    have h1 := hψ (utriElt (1 : F))
    rw [hψu 1, map_one, mul_one, hψu ((c : F) ^ 2)] at h1
    exact utriElt_injective h1
  have hσσ : ∀ s, σ (σ s) = s := by
    intro s
    have h1 := hψ (utriElt s)
    rw [hψu s, hψu, map_mul, ← mul_assoc, hc2, one_mul] at h1
    exact utriElt_injective h1
  have hσμ : (c : F) ^ 2 * σ μ = μ := by
    have h0 := hmm (conjSubgroup (utriElt 0) (ltri F))
    rw [hP 0, hP] at h0
    have h1 := eq_of_conjSubgroup_utriElt_ltri_eq h0
    simp only [map_zero, mul_zero, zero_add] at h1
    linear_combination h1 - μ * h2
  by_cases hσ1 : σ = RingEquiv.refl F
  ·
    have hc2' : ((c : F) ^ 2) ^ 2 = 1 := by
      have := hc2
      rw [hσ1] at this
      simpa [sq] using this
    have hc2'' : (c : F) ^ 2 = 1 := CharTwo.sq_injective (by simpa using hc2')
    have hc1 : c = 1 := Units.ext (CharTwo.sq_injective (by simpa using hc2''))
    refine ⟨μ, fun h0 => hnofix 0 (by simp [h0]), fun x => ?_⟩
    rw [hg, hgc, hc1, torusElt_one, mul_one, hσ1, sl2FieldAut_refl]
    simp
  ·
    exfalso
    have hσ2 : orderOf σ = 2 := by
      refine orderOf_eq_prime ?_ hσ1
      rw [pow_two]
      ext x
      exact hσσ x
    have hker : (autAddMap σ).ker = (autFixedSubfield σ).toAddSubgroup := ker_autAddMap σ
    have hle : (autAddMap σ).range ≤ (autAddMap σ).ker := by
      rintro _ ⟨s, rfl⟩
      rw [AddMonoidHom.mem_ker, autAddMap_apply, autAddMap_apply, map_add, hσσ]
      linear_combination (s + σ s) * h2
    have hcard : Nat.card (autAddMap σ).ker ≤ Nat.card (autAddMap σ).range := by
      rw [natCard_range_autAddMap hσ2, hker]
      exact le_rfl
    have hrange : (autAddMap σ).range = (autAddMap σ).ker :=
      AddSubgroup.eq_of_le_of_card_ge hle hcard
    have h1mem : (1 : F) ∈ (autAddMap σ).range := by
      rw [hrange, hker]
      exact mem_autFixedSubfield.2 (map_one σ)
    obtain ⟨lam, hlam⟩ := h1mem
    rw [autAddMap_apply] at hlam
    refine hnofix (lam * μ) ?_
    rw [map_mul]
    linear_combination (σ lam) * hσμ - μ * hlam + (σ lam * μ) * h2

end SL

section Sylow

theorem exists_fixed_sylow_of_involutive {Q : Type*} [Group Q] [Finite Q] (φ : Q ≃* Q)
    (hφ : ∀ x, φ (φ x) = x) : ∃ P : Sylow 2 Q, (P : Subgroup Q).map φ.toMonoidHom = P := by
  let Φ : Sylow 2 Q → Sylow 2 Q := fun P =>
    Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective P
  have hΦ : Function.Involutive Φ := fun P => by
    apply Sylow.ext
    show ((P : Subgroup Q).map φ.toMonoidHom).map φ.toMonoidHom = P
    rw [Subgroup.map_map]
    have : φ.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id Q := MonoidHom.ext hφ
    rw [this, Subgroup.map_id]
  have hodd : Odd (Nat.card (Sylow 2 Q)) :=
    Nat.odd_iff.2 (by simpa [Nat.ModEq] using card_sylow_modEq_one 2 Q)
  obtain ⟨P, hP⟩ := exists_fixedPoint_of_involutive_of_odd hΦ hodd
  exact ⟨P, congrArg (fun P : Sylow 2 Q => (P : Subgroup Q)) hP⟩

theorem IsL2Pair.exists_involution_of_unique_fixed {Q : Type} [Group Q] {S : Subgroup Q} {q : ℕ}
    (h : IsL2Pair Q S q) (φ : Q ≃* Q) (hφ : ∀ x, φ (φ x) = x) (hS : S.map φ.toMonoidHom = S)
    (huniq : ∀ g, (conjSubgroup g S).map φ.toMonoidHom = conjSubgroup g S →
      conjSubgroup g S = S) :
    ∃ t ∈ S, t ≠ 1 ∧ ∀ x, φ x = t * x * t⁻¹ := by
  obtain ⟨F, _, _, _, e, -, hmapS, -, hmemS, -⟩ := h.exists_data
  let ψ : SL(2, F) ≃* SL(2, F) := e.symm.trans (φ.trans e)
  have hψx : ∀ x, ψ x = e (φ (e.symm x)) := fun x => rfl
  have hψψ : ∀ x, ψ (ψ x) = x := fun x => by
    rw [hψx, hψx, e.symm_apply_apply, hφ, e.apply_symm_apply]
  have hcomp : ψ.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp φ.toMonoidHom :=
    MonoidHom.ext fun x => by simp [hψx]
  have hψU : (utri F).map ψ.toMonoidHom = utri F := by
    rw [← hmapS, Subgroup.map_map, hcomp, ← Subgroup.map_map, hS]
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hψuniq : ∀ g, (conjSubgroup g (utri F)).map ψ.toMonoidHom = conjSubgroup g (utri F) →
      conjSubgroup g (utri F) = utri F := by
    intro g hg
    have hk : (conjSubgroup (e.symm g) S).map e.toMonoidHom = conjSubgroup g (utri F) := by
      rw [map_conjSubgroup_mulEquiv, e.apply_symm_apply, hmapS]
    have h1 : (conjSubgroup (e.symm g) S).map φ.toMonoidHom = conjSubgroup (e.symm g) S := by
      apply Subgroup.map_injective hinj
      rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map, hk]
      exact hg
    have h2 := huniq _ h1
    rw [← hk, h2, hmapS]
  obtain ⟨μ, hμ0, hψ'⟩ := sl2_exists_utriElt_of_unique_fixed ψ hψψ hψU hψuniq
  refine ⟨e.symm (utriElt μ), (hmemS _).2 (by rw [e.apply_symm_apply]; exact utriElt_mem_utri μ),
    fun h1 => utriElt_ne_one hμ0 ?_, fun x => ?_⟩
  · have := congrArg e h1
    rwa [e.apply_symm_apply, map_one] at this
  · apply e.injective
    have h1 := hψ' (e x)
    rw [hψx, e.symm_apply_apply] at h1
    rw [h1, map_mul, map_mul, map_inv, e.apply_symm_apply]

end Sylow

end CFSG.CGT.Timmesfeld75

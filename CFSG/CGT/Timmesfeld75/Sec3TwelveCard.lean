module

public import CFSG.CGT.Timmesfeld75.Sec3TwelveAlg
public import CFSG.CGT.Timmesfeld75.Sec3TwelveIrr
public import CFSG.CGT.Timmesfeld75.Sec3Stmts
public import CFSG.CGT.Timmesfeld75.Sec3Lift
public import CFSG.CGT.Timmesfeld75.Sec3GlobalConj

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section Data

variable {G : Type} [Group G]

structure Data312 (T T₁ X M : Subgroup G) [(M.subgroupOf X).Normal] (F : Type) [Field F]
    (a : G) where
  e : ↥X ⧸ M.subgroupOf X ≃* SL(2, F)
  σ : F ≃+* F
  hX : T ⊔ T₁ = X
  hM : cfgM T T₁ = M
  sec3 : Sec3 T T₁
  aa : a * a = 1
  aT : conjSubgroup a T = T
  aT₁ : conjSubgroup a T₁ = T₁
  eT : ((T.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))).map e.toMonoidHom = utri F
  eT₁ : ((T₁.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))).map e.toMonoidHom = ltri F
  ind : InducesFieldAut X M a e σ
  σ_ne : σ ≠ RingEquiv.refl F

end Data

section Basic

variable {G : Type} [Group G] {T T₁ X M : Subgroup G} [hN : (M.subgroupOf X).Normal]
  {F : Type} [Field F] {a : G}

theorem Data312.aX (D : Data312 T T₁ X M F a) : conjSubgroup a X = X := by
  rw [← D.hX, conjSubgroup_sup_eq_sup, D.aT, D.aT₁]

theorem Data312.aM (D : Data312 T T₁ X M F a) : conjSubgroup a M = M := by
  have h := cfgM_conj a T T₁
  rw [D.aT, D.aT₁] at h
  rw [← D.hM]
  exact h.symm

theorem Data312.mem_X (D : Data312 T T₁ X M F a) {y : G} (hy : y ∈ X) : a * y * a⁻¹ ∈ X := by
  have h := conj_mem_conjSubgroup a hy
  rwa [D.aX] at h

@[expose] def Data312.phi (D : Data312 T T₁ X M F a) :
    ↥X ⧸ M.subgroupOf X ≃* ↥X ⧸ M.subgroupOf X :=
  (D.e.trans (sl2FieldAut D.σ)).trans D.e.symm

theorem Data312.phi_mk (D : Data312 T T₁ X M F a) (x : ↥X) :
    D.phi (QuotientGroup.mk x) = QuotientGroup.mk ⟨a * x * a⁻¹, D.mem_X x.2⟩ := by
  obtain ⟨ha, h⟩ := D.ind
  show D.e.symm (sl2FieldAut D.σ (D.e (QuotientGroup.mk x))) = _
  rw [sl2FieldAut_eq_map, ← h x]
  exact D.e.symm_apply_apply _

theorem Data312.sq_eq (D : Data312 T T₁ X M F a) (s : F) : D.σ (D.σ s) = s := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (D.e.symm (utriElt s))
  have h1 : D.phi (D.phi (QuotientGroup.mk x)) = QuotientGroup.mk x := by
    rw [D.phi_mk, D.phi_mk]
    congr 1
    apply Subtype.ext
    show a * (a * (x : G) * a⁻¹) * a⁻¹ = x
    calc a * (a * (x : G) * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
      _ = x := by rw [D.aa]; group
  rw [hx] at h1
  have h2 := congrArg D.e h1
  simp only [Data312.phi, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h2
  rw [sl2FieldAut_utriElt, sl2FieldAut_utriElt] at h2
  exact utriElt_injective h2

theorem Data312.orderOf_σ (D : Data312 T T₁ X M F a) : orderOf D.σ = 2 := by
  refine orderOf_eq_prime ?_ D.σ_ne
  rw [pow_two]
  ext s
  exact D.sq_eq s

theorem Data312.phi_eq (D : Data312 T T₁ X M F a) :
    D.phi = quotConjAut X M a D.aX D.aM := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [D.phi_mk]
  rfl

theorem Data312.T_le_X (D : Data312 T T₁ X M F a) : T ≤ X := by
  rw [← D.hX]
  exact le_sup_left

theorem Data312.conj_mem_T (D : Data312 T T₁ X M F a) {t : G} (ht : t ∈ T) : a * t * a⁻¹ ∈ T := by
  have h := conj_mem_conjSubgroup a ht
  rwa [D.aT] at h

theorem Data312.σ_eq_refl_of_phi_eq (D : Data312 T T₁ X M F a) (h : ∀ y, D.phi y = y) :
    D.σ = RingEquiv.refl F := by
  ext s
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (D.e.symm (utriElt s))
  have h1 := congrArg D.e (h (QuotientGroup.mk x))
  simp only [Data312.phi, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
  rw [hx, MulEquiv.apply_symm_apply, sl2FieldAut_utriElt] at h1
  exact utriElt_injective h1

end Basic

section Eps

variable {G : Type} [Group G] {T T₁ X M : Subgroup G} [hN : (M.subgroupOf X).Normal]
  {F : Type} [Field F] {a : G}

@[expose] def Data312.eps (D : Data312 T T₁ X M F a) (t : ↥T) : F :=
  (D.e (QuotientGroup.mk (⟨(t : G), D.T_le_X t.2⟩ : ↥X))) 0 1

theorem Data312.e_mk_eq_utriElt (D : Data312 T T₁ X M F a) (t : ↥T) :
    D.e (QuotientGroup.mk (⟨(t : G), D.T_le_X t.2⟩ : ↥X)) = utriElt (D.eps t) := by
  have hmem : D.e (QuotientGroup.mk (⟨(t : G), D.T_le_X t.2⟩ : ↥X)) ∈ utri F := by
    rw [← D.eT]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 t.2))
  exact eq_utriElt_of_mem_utri hmem

theorem Data312.eps_mul (D : Data312 T T₁ X M F a) (s t : ↥T) :
    D.eps (s * t) = D.eps s + D.eps t := by
  have h : D.e (QuotientGroup.mk (⟨((s * t : ↥T) : G), D.T_le_X (s * t).2⟩ : ↥X)) =
      D.e (QuotientGroup.mk (⟨(s : G), D.T_le_X s.2⟩ : ↥X)) *
        D.e (QuotientGroup.mk (⟨(t : G), D.T_le_X t.2⟩ : ↥X)) := by
    rw [← map_mul]
    rfl
  rw [D.e_mk_eq_utriElt, D.e_mk_eq_utriElt, D.e_mk_eq_utriElt, ← utriElt_add] at h
  exact utriElt_injective h

theorem Data312.eps_surj (D : Data312 T T₁ X M F a) (s : F) : ∃ t : ↥T, D.eps t = s := by
  have hs : utriElt s ∈
      ((T.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))).map D.e.toMonoidHom := by
    rw [D.eT]
    exact utriElt_mem_utri s
  obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.1 hs
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩, ?_⟩
  have h := D.e_mk_eq_utriElt ⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩
  exact utriElt_injective (h.symm.trans hys)

theorem Data312.eps_eq_zero_iff (D : Data312 T T₁ X M F a) (t : ↥T) :
    D.eps t = 0 ↔ (t : G) ∈ M := by
  constructor
  · intro h
    have h1 := D.e_mk_eq_utriElt t
    rw [h, utriElt_zero] at h1
    have h2 : QuotientGroup.mk (⟨(t : G), D.T_le_X t.2⟩ : ↥X) =
        (1 : ↥X ⧸ M.subgroupOf X) := D.e.injective (h1.trans (map_one D.e).symm)
    have h3 : (⟨(t : G), D.T_le_X t.2⟩ : ↥X) ∈ M.subgroupOf X := (QuotientGroup.eq_one_iff _).1 h2
    exact Subgroup.mem_subgroupOf.1 h3
  · intro h
    have h2 : QuotientGroup.mk (⟨(t : G), D.T_le_X t.2⟩ : ↥X) = (1 : ↥X ⧸ M.subgroupOf X) :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h)
    have h1 := D.e_mk_eq_utriElt t
    rw [h2, map_one] at h1
    exact utriElt_injective (h1.symm.trans utriElt_zero.symm)

theorem Data312.eps_conj (D : Data312 T T₁ X M F a) (t : ↥T) :
    D.eps ⟨a * (t : G) * a⁻¹, D.conj_mem_T t.2⟩ = D.σ (D.eps t) := by
  obtain ⟨ha, h⟩ := D.ind
  apply utriElt_injective
  rw [← D.e_mk_eq_utriElt]
  have h1 := h ⟨(t : G), D.T_le_X t.2⟩
  refine h1.trans ?_
  rw [D.e_mk_eq_utriElt, ← sl2FieldAut_eq_map, sl2FieldAut_utriElt]

theorem Data312.not_mem_T (D : Data312 T T₁ X M F a) : a ∉ T := by
  intro haT
  apply D.σ_ne
  ext s
  obtain ⟨t, ht⟩ := D.eps_surj s
  have hc : a * (t : G) * a⁻¹ = t := by
    have := elemAbelian_mul_comm D.sec3.cfg.wc.1 haT t.2
    calc a * (t : G) * a⁻¹ = (t : G) * a * a⁻¹ := by rw [this]
      _ = t := by group
  have h1 := D.eps_conj t
  rw [show (⟨a * (t : G) * a⁻¹, D.conj_mem_T t.2⟩ : ↥T) = t from Subtype.ext hc, ht] at h1
  exact h1.symm

end Eps

section Step2

variable {G : Type} [Group G] [Finite G] {T T₁ X M : Subgroup G} [hN : (M.subgroupOf X).Normal]
  {F : Type} [Field F] {a : G}

omit [Finite G] in
theorem Data312.conj_eq_of_inf_centralizer_ne_bot (D : Data312 T T₁ X M F a) {g : G}
    (h : conjSubgroup g T ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥) :
    conjSubgroup a (conjSubgroup g T) = conjSubgroup g T := by
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  have hyT : y ∈ conjSubgroup g T := hy.1
  have hy1' : y ≠ 1 := fun h' => hy1 (Subtype.ext h')
  have hwc := D.sec3.cfg.wc.conj g
  have hay : a ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hy.2).symm
  exact mem_normalizer_iff_conjSubgroup_eq.1 (hwc.centralizer_le_normalizer hyT hy1' hay)

omit [Finite G] in
theorem Data312.exists_conj_inf_centralizer_eq_bot [Finite F] [CharP F 2]
    (D : Data312 T T₁ X M F a) :
    ∃ g ∈ X, conjSubgroup g T ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
  by_contra hcon
  push Not at hcon
  have hpair : IsL2Pair (↥X ⧸ M.subgroupOf X)
      ((T.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))) (Nat.card F) :=
    ⟨F, inferInstance, inferInstance, inferInstance, D.e, rfl, D.eT⟩
  have hφ : D.phi = MulEquiv.refl _ := by
    refine hpair.eq_refl_of_map_conjSubgroup_eq D.phi fun gq => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gq
    have h1 : conjSubgroup (QuotientGroup.mk g : ↥X ⧸ M.subgroupOf X)
        ((T.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))) =
        ((conjSubgroup (g : G) T).subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X)) :=
      (map_subgroupOf_conjSubgroup_of_mem X M T g.2).symm
    have h2 := D.conj_eq_of_inf_centralizer_ne_bot (hcon (g : G) g.2)
    rw [h1, D.phi_eq, ← map_subgroupOf_conjSubgroup_eq X M a D.aX D.aM (conjSubgroup (g : G) T), h2]
  exact D.σ_ne (D.σ_eq_refl_of_phi_eq fun y => by rw [hφ]; rfl)

theorem Data312.card_centralizer_sq [Finite F] [CharP F 2] (D : Data312 T T₁ X M F a) :
    Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) ^ 2 =
        Nat.card (normIn T T₁) ∧
      Nat.card ↥(normIn T₁ T ⊓ Subgroup.centralizer ({a} : Set G)) ^ 2 =
        Nat.card (normIn T₁ T) := by
  obtain ⟨g, hgX, hg⟩ := D.exists_conj_inf_centralizer_eq_bot
  have hS := D.sec3
  have hgX' : g ∈ T ⊔ T₁ := by rw [D.hX]; exact hgX
  have hLab : IsElemAbelian 2 (normIn T T₁) :=
    isElemAbelian_subgroup_of_le hS.cfg.wc.1 (normIn_le T T₁)
  have hL₁ab : IsElemAbelian 2 (normIn T₁ T) :=
    isElemAbelian_subgroup_of_le hS.cfg.wc₁.1 (normIn_le T₁ T)
  have haL : ∀ x ∈ normIn T T₁, a * x * a⁻¹ ∈ normIn T T₁ := fun x hx => by
    have h := conj_mem_conjSubgroup a hx
    rwa [← normIn_conj, D.aT, D.aT₁] at h
  have haL₁ : ∀ x ∈ normIn T₁ T, a * x * a⁻¹ ∈ normIn T₁ T := fun x hx => by
    have h := conj_mem_conjSubgroup a hx
    rwa [← normIn_conj, D.aT, D.aT₁] at h
  have h1 := natCard_le_natCard_centralizer_sq (normIn T T₁) hLab D.aa haL
  have h1' := natCard_le_natCard_centralizer_sq (normIn T₁ T) hL₁ab D.aa haL₁
  have hcard1 : Nat.card (normIn T₁ T) = Nat.card (normIn T T₁) := hS.card_normIn_swap
  have hMcard : Nat.card (cfgM T T₁) = Nat.card (normIn T T₁) ^ 2 := hS.card_cfgM_eq_sq
  have hLM : normIn T T₁ ≤ cfgM T T₁ := Cfg.normIn_le_cfgM_left T T₁
  have hL₁M : normIn T₁ T ≤ cfgM T T₁ := Cfg.normIn_le_cfgM_right T T₁
  have hPQ : (normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) ⊓
      (normIn T₁ T ⊓ Subgroup.centralizer ({a} : Set G)) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxT : x ∈ T := normIn_le _ _ hx.1.1
    have hxT₁ : x ∈ T₁ := normIn_le _ _ hx.2.1
    have : x ∈ T ⊓ T₁ := ⟨hxT, hxT₁⟩
    rwa [hS.cfg.inf] at this
  have hKcard := natCard_mul_natCard_le_of_inf_eq_bot
    (M := cfgM T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) (inf_le_inf_right _ hLM)
    (inf_le_inf_right _ hL₁M) hPQ
  have hgcon : conjSubgroup g (normIn T T₁) ⊓
      (cfgM T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hx1 : x ∈ conjSubgroup g T ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨conjSubgroup_mono (normIn_le T T₁) hx.1, hx.2.2⟩
    rwa [hg] at hx1
  have hpig := natCard_mul_natCard_le_of_inf_eq_bot (M := cfgM T T₁)
    (hS.cfg.conjSubgroup_normIn_le_cfgM hgX') inf_le_left hgcon
  rw [card_conjSubgroup, hMcard] at hpig
  rw [hcard1] at h1'
  rw [hcard1]
  have hℓ : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have hq0 : 0 < Nat.card ↥(normIn T₁ T ⊓ Subgroup.centralizer ({a} : Set G)) := Nat.card_pos
  have hp0 : 0 < Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) := Nat.card_pos
  generalize Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) = p at *
  generalize Nat.card ↥(normIn T₁ T ⊓ Subgroup.centralizer ({a} : Set G)) = q at *
  generalize Nat.card ↥(cfgM T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) = k at *
  generalize Nat.card (normIn T T₁) = ℓ at *
  have hkℓ : k ≤ ℓ := Nat.le_of_mul_le_mul_left (by nlinarith) hℓ
  have hpq : p * q ≤ ℓ := le_trans hKcard hkℓ
  have hsq : p ^ 2 * q ^ 2 ≤ ℓ ^ 2 := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hpq 2
  constructor
  · by_contra hne
    have hlt : ℓ < p ^ 2 := lt_of_le_of_ne h1 (Ne.symm hne)
    have : ℓ * q ^ 2 < p ^ 2 * q ^ 2 := Nat.mul_lt_mul_of_pos_right hlt (by positivity)
    nlinarith
  · by_contra hne
    have hlt : ℓ < q ^ 2 := lt_of_le_of_ne h1' (Ne.symm hne)
    have : p ^ 2 * ℓ < p ^ 2 * q ^ 2 := Nat.mul_lt_mul_of_pos_left hlt (by positivity)
    nlinarith

omit [Finite G] in
theorem Data312.conj_mem_normIn (D : Data312 T T₁ X M F a) {x : G} (hx : x ∈ normIn T T₁) :
    a * x * a⁻¹ ∈ normIn T T₁ := by
  have h := conj_mem_conjSubgroup a hx
  rwa [← normIn_conj, D.aT, D.aT₁] at h

end Step2

section Step3

variable {G : Type} [Group G] [Finite G] {T T₁ X M : Subgroup G} [hN : (M.subgroupOf X).Normal]
  {F : Type} [Field F] {a : G}

theorem Data312.exists_eps_centralizer [Finite F] [CharP F 2] (D : Data312 T T₁ X M F a) (s : F)
    (hs : D.σ s = s) : ∃ x : ↥T, a * (x : G) * a⁻¹ = x ∧ D.eps x = s := by
  have hS := D.sec3
  have hcard : Nat.card (normIn T T₁) =
      Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) ^ 2 :=
    D.card_centralizer_sq.1.symm
  have hL : IsElemAbelian 2 (normIn T T₁) :=
    isElemAbelian_subgroup_of_le hS.cfg.wc.1 (normIn_le T T₁)
  obtain ⟨t, ht⟩ := D.eps_surj s
  have ht'T : a * (t : G) * a⁻¹ ∈ T := D.conj_mem_T t.2
  have hl'T : (t : G)⁻¹ * (a * t * a⁻¹) ∈ T := T.mul_mem (T.inv_mem t.2) ht'T
  have hε : D.eps ⟨(t : G)⁻¹ * (a * t * a⁻¹), hl'T⟩ = 0 := by
    have h1 := D.eps_mul t ⟨(t : G)⁻¹ * (a * t * a⁻¹), hl'T⟩
    have h2 : t * (⟨(t : G)⁻¹ * (a * t * a⁻¹), hl'T⟩ : ↥T) = ⟨a * (t : G) * a⁻¹, ht'T⟩ :=
      Subtype.ext (by simp)
    rw [h2, D.eps_conj, ht, hs] at h1
    linear_combination (-1 : F) * h1
  have hl'M : (t : G)⁻¹ * (a * t * a⁻¹) ∈ M := (D.eps_eq_zero_iff _).1 hε
  have hl'L : (t : G)⁻¹ * (a * t * a⁻¹) ∈ normIn T T₁ := by
    rw [← hS.cfg.inf_cfgM, D.hM]
    exact ⟨hl'T, hl'M⟩
  have hl'a : a * ((t : G)⁻¹ * (a * t * a⁻¹)) * a⁻¹ = (t : G)⁻¹ * (a * t * a⁻¹) := by
    have hinv := elemAbelian_inv hL hl'L
    calc a * ((t : G)⁻¹ * (a * t * a⁻¹)) * a⁻¹
        = (a * t * a⁻¹)⁻¹ * ((a * a) * t * (a * a)⁻¹) := by group
      _ = ((t : G)⁻¹ * (a * t * a⁻¹))⁻¹ := by rw [D.aa]; group
      _ = (t : G)⁻¹ * (a * t * a⁻¹) := hinv
  have hcomm : a * ((t : G)⁻¹ * (a * t * a⁻¹)) = ((t : G)⁻¹ * (a * t * a⁻¹)) * a := by
    calc a * ((t : G)⁻¹ * (a * t * a⁻¹))
        = (a * ((t : G)⁻¹ * (a * t * a⁻¹)) * a⁻¹) * a := by group
      _ = ((t : G)⁻¹ * (a * t * a⁻¹)) * a := by rw [hl'a]
  obtain ⟨l, hl, hll⟩ := exists_eq_mul_conj_of_natCard_eq_sq (normIn T T₁) hL D.aa
    (fun x hx => D.conj_mem_normIn hx) hcard
    (w := (t : G)⁻¹ * (a * t * a⁻¹))
    ⟨hl'L, Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm⟩
  have hlT : l ∈ T := normIn_le _ _ hl
  have hlM : l ∈ M := by
    rw [← D.hM]
    exact Cfg.normIn_le_cfgM_left T T₁ hl
  have hl2 : (a * l * a⁻¹) * (a * l * a⁻¹) = 1 :=
    elemAbelian_mul_self hL (D.conj_mem_normIn hl)
  refine ⟨t * ⟨l, hlT⟩, ?_, ?_⟩
  · show a * ((t : G) * l) * a⁻¹ = (t : G) * l
    have e1 : a * (t : G) * a⁻¹ = (t : G) * ((t : G)⁻¹ * (a * t * a⁻¹)) := by group
    calc a * ((t : G) * l) * a⁻¹ = (a * t * a⁻¹) * (a * l * a⁻¹) := by group
      _ = (t : G) * ((t : G)⁻¹ * (a * t * a⁻¹)) * (a * l * a⁻¹) := by rw [← e1]
      _ = (t : G) * (l * (a * l * a⁻¹)) * (a * l * a⁻¹) := by rw [← hll]
      _ = (t : G) * l * ((a * l * a⁻¹) * (a * l * a⁻¹)) := by group
      _ = (t : G) * l := by rw [hl2]; group
  · rw [D.eps_mul, ht, (D.eps_eq_zero_iff ⟨l, hlT⟩).2 hlM, add_zero]

@[expose] def Data312.epsHom (D : Data312 T T₁ X M F a) :
    ↥(T ⊓ Subgroup.centralizer ({a} : Set G)) →* Multiplicative F where
  toFun x := Multiplicative.ofAdd (D.eps ⟨(x : G), (Subgroup.mem_inf.1 x.2).1⟩)
  map_one' := by
    have h : D.eps ⟨((1 : ↥(T ⊓ Subgroup.centralizer ({a} : Set G))) : G),
        (Subgroup.mem_inf.1 (1 : ↥(T ⊓ Subgroup.centralizer ({a} : Set G))).2).1⟩ = 0 :=
      (D.eps_eq_zero_iff _).2 M.one_mem
    exact congrArg Multiplicative.ofAdd h
  map_mul' x y := by
    have h := D.eps_mul ⟨(x : G), (Subgroup.mem_inf.1 x.2).1⟩
      ⟨(y : G), (Subgroup.mem_inf.1 y.2).1⟩
    exact (congrArg Multiplicative.ofAdd h).trans (ofAdd_add _ _)

omit [Finite G] in
theorem Data312.mem_ker_epsHom (D : Data312 T T₁ X M F a)
    (x : ↥(T ⊓ Subgroup.centralizer ({a} : Set G))) : x ∈ D.epsHom.ker ↔ (x : G) ∈ M := by
  rw [MonoidHom.mem_ker]
  show Multiplicative.ofAdd (D.eps ⟨(x : G), (Subgroup.mem_inf.1 x.2).1⟩) = 1 ↔ _
  rw [ofAdd_eq_one]
  exact D.eps_eq_zero_iff _

theorem Data312.mem_range_epsHom_iff [Finite F] [CharP F 2] (D : Data312 T T₁ X M F a)
    (y : Multiplicative F) : y ∈ D.epsHom.range ↔ D.σ (Multiplicative.toAdd y) =
      Multiplicative.toAdd y := by
  constructor
  · rintro ⟨x, rfl⟩
    have hx : a * (x : G) * a⁻¹ = x := by
      have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2
      calc a * (x : G) * a⁻¹ = ((x : G) * a) * a⁻¹ := by rw [this]
        _ = x := by group
    have h1 := D.eps_conj ⟨(x : G), (Subgroup.mem_inf.1 x.2).1⟩
    rw [show (⟨a * (x : G) * a⁻¹, D.conj_mem_T (Subgroup.mem_inf.1 x.2).1⟩ : ↥T) =
      ⟨(x : G), (Subgroup.mem_inf.1 x.2).1⟩ from Subtype.ext hx] at h1
    exact h1.symm
  · intro h
    obtain ⟨t, hta, hte⟩ := D.exists_eps_centralizer _ h
    have htC : (t : G) ∈ T ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨t.2, Subgroup.mem_centralizer_singleton_iff.2 (by
        calc (t : G) * a = (a * t * a⁻¹) * a := by rw [hta]
          _ = a * t := by group)⟩
    refine ⟨⟨(t : G), htC⟩, ?_⟩
    exact congrArg Multiplicative.ofAdd hte

theorem Data312.card_centralizer_T [Finite F] [CharP F 2] (D : Data312 T T₁ X M F a) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({a} : Set G)) =
      Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) *
        Nat.card (autFixedSubfield D.σ) := by
  have h := Subgroup.card_ker_mul_card_range D.epsHom
  rw [← h]
  congr 1
  · refine Nat.card_congr
      { toFun := fun x => ⟨((x : ↥(T ⊓ Subgroup.centralizer ({a} : Set G))) : G), ?_,
          (Subgroup.mem_inf.1 x.1.2).2⟩
        invFun := fun y => ⟨⟨(y : G), (normIn_le T T₁) (Subgroup.mem_inf.1 y.2).1,
          (Subgroup.mem_inf.1 y.2).2⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · rw [← D.sec3.cfg.inf_cfgM, D.hM]
      exact ⟨(Subgroup.mem_inf.1 x.1.2).1, (D.mem_ker_epsHom x.1).1 x.2⟩
    · rw [D.mem_ker_epsHom]
      rw [← D.hM]
      exact Cfg.normIn_le_cfgM_left T T₁ (Subgroup.mem_inf.1 y.2).1
  · refine Nat.card_congr
      { toFun := fun y => ⟨Multiplicative.toAdd (y : Multiplicative F),
          (D.mem_range_epsHom_iff _).1 y.2⟩
        invFun := fun s => ⟨Multiplicative.ofAdd (s : F), (D.mem_range_epsHom_iff _).2 s.2⟩
        left_inv := fun y => rfl
        right_inv := fun s => rfl }

theorem Data312.card_T_eq [Finite F] [CharP F 2] (D : Data312 T T₁ X M F a) :
    Nat.card T = Nat.card (normIn T T₁) * Nat.card F := by
  obtain ⟨n, hn, hFn⟩ := exists_natCard_eq_two_pow (F := F)
  have hpsl := exists_mulEquiv_psl_of_mulEquiv_sl2 hn.ne' hFn D.e
  have key : ∀ {X M : Subgroup G} [(M.subgroupOf X).Normal], T ⊔ T₁ = X → cfgM T T₁ = M →
      Nonempty (↥X ⧸ M.subgroupOf X ≃* PSL(2, GaloisField 2 n)) →
        Nat.card T = Nat.card (normIn T T₁) * 2 ^ n := by
    intro X M _ hX hM h
    subst hX
    subst hM
    exact D.sec3.card_eq_mul hn.ne' h
  rw [key D.hX D.hM hpsl, ← hFn]

theorem Data312.card_T_eq_sq [Finite F] [CharP F 2] (D : Data312 T T₁ X M F a) :
    Nat.card T = Nat.card ↥(T ⊓ Subgroup.centralizer ({a} : Set G)) ^ 2 := by
  rw [D.card_T_eq, D.card_centralizer_T, mul_pow, D.card_centralizer_sq.1,
    natCard_eq_sq_of_orderOf_eq_two D.orderOf_σ]

theorem Data312.exists_centralizer_not_mem_M [Finite F] [CharP F 2] (D : Data312 T T₁ X M F a) :
    ∃ x ∈ T, a * x * a⁻¹ = x ∧ x ∉ M := by
  obtain ⟨x, hxa, hxe⟩ := D.exists_eps_centralizer (1 : F) (map_one D.σ)
  refine ⟨x, x.2, hxa, fun hM => ?_⟩
  have h := (D.eps_eq_zero_iff x).2 hM
  rw [hxe] at h
  exact one_ne_zero h

omit [Finite G] in
theorem Data312.four_le_card [Finite F] [CharP F 2] (D : Data312 T T₁ X M F a) :
    4 ≤ Nat.card F := by
  have h := natCard_eq_sq_of_orderOf_eq_two D.orderOf_σ
  have h2 : 1 < Nat.card (autFixedSubfield D.σ) := Finite.one_lt_card
  rw [h]
  nlinarith

end Step3

section Irred

variable {G : Type} [Group G] [Finite G]

theorem Sec3.two_pow_le_card_of_normal {T T₁ X M : Subgroup G} [hN : (M.subgroupOf X).Normal]
    (hS : Sec3 T T₁) (hX : T ⊔ T₁ = X) (hM : cfgM T T₁ = M) {g : ℕ} (hg : 0 < g)
    (hpair : IsL2Pair (↥X ⧸ M.subgroupOf X)
      ((T.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))) (2 ^ g))
    {N₁ : Subgroup G} (hN₁ : N₁ ≤ M) (hnorm : ∀ x ∈ X, ∀ n ∈ N₁, x * n * x⁻¹ ∈ N₁)
    (hne : N₁ ≠ ⊥) : 2 ^ (2 * g) ≤ Nat.card N₁ := by
  subst hX
  subst hM
  have hN₁X : N₁ ≤ T ⊔ T₁ := hN₁.trans (cfgM_le_sup T T₁)
  have : (N₁.subgroupOf (T ⊔ T₁)).Normal := ⟨fun n hn y => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm y y.2 n hn⟩
  have hP : IsPGroup 2 ((cfgM T T₁).subgroupOf (T ⊔ T₁)) :=
    (isPGroup_two_of_isElemAbelian hS.cfg.isElemAbelian_cfgM).comap_subtype
  have hcard : Nat.card (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) =
      2 ^ g * ((2 ^ g) ^ 2 - 1) := hpair.card_eq_mul
  have hfpf : ∀ y : ↥(T ⊔ T₁), Odd (orderOf (QuotientGroup.mk y :
      ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))) →
      (QuotientGroup.mk y : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) ≠ 1 →
      ∀ n ∈ (cfgM T T₁).subgroupOf (T ⊔ T₁), y * n * y⁻¹ = n → n = 1 := by
    intro y hodd hy1 n hn hyn
    have h := hS.centralizer_cfgM_eq_bot_of_odd hpair y.2 hodd hy1 (n : G)
      (Subgroup.mem_subgroupOf.1 hn) (congrArg Subtype.val hyn)
    exact Subtype.ext h
  have hle : N₁.subgroupOf (T ⊔ T₁) ≤ (cfgM T T₁).subgroupOf (T ⊔ T₁) := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hN₁ (Subgroup.mem_subgroupOf.1 hx))
  have hne' : N₁.subgroupOf (T ⊔ T₁) ≠ ⊥ := by
    intro h
    apply hne
    refine (Subgroup.eq_bot_iff_forall N₁).2 fun n hn => ?_
    have hmem : (⟨n, hN₁X hn⟩ : ↥(T ⊔ T₁)) ∈ N₁.subgroupOf (T ⊔ T₁) :=
      Subgroup.mem_subgroupOf.2 hn
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have key := two_pow_two_mul_le_natCard_of_fpf ((cfgM T T₁).subgroupOf (T ⊔ T₁))
    (N₁.subgroupOf (T ⊔ T₁)) hle hP g hg hcard hfpf hne'
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₁X).toEquiv] at key

end Irred

end CFSG.CGT.Timmesfeld75

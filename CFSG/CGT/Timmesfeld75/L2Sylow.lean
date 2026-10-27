module

public import CFSG.CGT.Timmesfeld75.L2Defs
import CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2SylIASL2

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section ConjGeneric

variable {G : Type*} [Group G]

theorem conjSubgroup_eq_conjSubgroup_iff {a b : G} {T : Subgroup G} :
    conjSubgroup a T = conjSubgroup b T ↔ a⁻¹ * b ∈ Subgroup.normalizer (T : Set G) := by
  have key : conjSubgroup a⁻¹ (conjSubgroup a T) = T := by
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  rw [mem_normalizer_iff_conjSubgroup_eq, ← conjSubgroup_conjSubgroup]
  constructor
  · intro h
    rw [← h, key]
  · intro h
    refine (conjSubgroup_inj (g := a⁻¹)).1 ?_
    rw [key, h]

theorem conjSubgroup_inf_eq_inf (g : G) (S T : Subgroup G) :
    conjSubgroup g (S ⊓ T) = conjSubgroup g S ⊓ conjSubgroup g T :=
  Subgroup.map_inf S T _ (MulAut.conj g).injective

theorem conjSubgroup_bot (g : G) : conjSubgroup g (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _

theorem conjSubgroup_sup_eq_sup (g : G) (S T : Subgroup G) :
    conjSubgroup g (S ⊔ T) = conjSubgroup g S ⊔ conjSubgroup g T := Subgroup.map_sup S T _

theorem conjSubgroup_top (g : G) : conjSubgroup g (⊤ : Subgroup G) = ⊤ :=
  Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

theorem conj_mem_conjSubgroup {T : Subgroup G} {x : G} (g : G) (hx : x ∈ T) :
    g * x * g⁻¹ ∈ conjSubgroup g T := by
  rw [mem_conjSubgroup]
  simpa [mul_assoc] using hx

theorem centralizer_conj_singleton (g h : G) :
    Subgroup.centralizer ({g * h * g⁻¹} : Set G) = conjSubgroup g (Subgroup.centralizer {h}) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, mem_conjSubgroup,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    calc g⁻¹ * y * g * h = g⁻¹ * (y * (g * h * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * h * g⁻¹) * y) * g := by rw [hy]
      _ = h * (g⁻¹ * y * g) := by group
  · intro hy
    calc y * (g * h * g⁻¹) = g * ((g⁻¹ * y * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * y * g)) * g⁻¹ := by rw [hy]
      _ = (g * h * g⁻¹) * y := by group

theorem exists_conjSubgroup_eq_of_sylow [Finite G] (P Q : Sylow 2 G) :
    ∃ g : G, conjSubgroup g (P : Subgroup G) = (Q : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g, ?_⟩
  ext y
  rw [mem_conjSubgroup, ← hg]
  exact mem_smul_sylow_iff_inv_mul_mul_mem.symm

theorem isPGroup_two_zpowers_of_mul_self_eq_one {g : G} (hg : g * g = 1) :
    IsPGroup 2 (Subgroup.zpowers g) :=
  IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg))

end ConjGeneric

section Bruhat

variable {F : Type} [Field F]

theorem exists_borel_mul_wElt_mul_borel {g : SL(2, F)} (hg : g ∉ borel F) :
    ∃ b₁ ∈ borel F, ∃ b₂ ∈ borel F, g = b₁ * wElt * b₂ := by
  have hc : g 1 0 ≠ 0 := hg
  refine ⟨utriElt (g 0 0 / g 1 0), utri_le_borel (utriElt_mem_utri _),
    utriElt (g 1 1 * g 1 0) * torusElt (Units.mk0 (g 1 0) hc),
    Subgroup.mul_mem _ (utri_le_borel (utriElt_mem_utri _)) (torusElt_mem_borel _), ?_⟩
  have hd := sl2_det g
  apply sl2_ext
  all_goals sl2_simp
  all_goals simp only [Units.val_mk0, Units.val_inv_eq_inv_val]
  · field_simp
    ring
  · field_simp
    linear_combination (-(g 1 0)) * hd
  · ring
  · field_simp
    ring

theorem inf_borel_conj_utri_eq_bot {g : SL(2, F)} (hg : g ∉ borel F) :
    borel F ⊓ conjSubgroup g (utri F) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨s, hs⟩ := mem_utri_iff.1 (mem_conjSubgroup.1 hx2)
  have hx : x = g * utriElt s * g⁻¹ := by rw [← hs]; group
  have h10 : x 1 0 = 0 := hx1
  rw [hx, conj_utriElt_apply_10] at h10
  have hc : g 1 0 ≠ 0 := hg
  have hs0 : s = 0 := by
    have h2 : g 1 0 ^ 2 * s = 0 := by linear_combination (-1) * h10
    exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero 2 hc)
  rw [Subgroup.mem_bot, hx, hs0, utriElt_zero]
  group

theorem utri_inf_conj_eq_bot {g : SL(2, F)} (hg : g ∉ borel F) :
    utri F ⊓ conjSubgroup g (utri F) = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf_right _ utri_le_borel).trans (inf_borel_conj_utri_eq_bot hg).le)

theorem wElt_not_mem_borel : (wElt : SL(2, F)) ∉ borel F := by
  show ¬ ((wElt : SL(2, F)) 1 0 = 0)
  rw [wElt_apply_10]
  exact one_ne_zero

theorem conjSubgroup_wElt_utri : conjSubgroup wElt (utri F) = ltri F := by
  ext x
  rw [mem_conjSubgroup, mem_utri_entries, mem_ltri_entries]
  have e10 : (((wElt : SL(2, F))⁻¹ * x * wElt : SL(2, F)) 1 0) = - x 0 1 := by
    sl2_simp
    ring
  have e00 : (((wElt : SL(2, F))⁻¹ * x * wElt : SL(2, F)) 0 0) = x 1 1 := by
    sl2_simp
    ring
  rw [e10, e00, neg_eq_zero]
  have hd := sl2_det x
  constructor
  · rintro ⟨h01, h11⟩
    refine ⟨h01, ?_⟩
    rw [h01, h11] at hd
    linear_combination hd
  · rintro ⟨h01, h00⟩
    refine ⟨h01, ?_⟩
    rw [h01, h00] at hd
    linear_combination hd

end Bruhat

section TwoTransitive

variable {F : Type} [Field F]

theorem exists_conj_pair_normal_form {a b : SL(2, F)}
    (h : conjSubgroup a (utri F) ≠ conjSubgroup b (utri F)) :
    ∃ g : SL(2, F), conjSubgroup (g * a) (utri F) = utri F ∧
      conjSubgroup (g * b) (utri F) = ltri F := by
  have hab : a⁻¹ * b ∉ borel F := by
    intro hmem
    apply h
    rw [conjSubgroup_eq_conjSubgroup_iff, normalizer_utri]
    exact hmem
  obtain ⟨b₁, hb₁, b₂, hb₂, hbb⟩ := exists_borel_mul_wElt_mul_borel hab
  have hb₁' : conjSubgroup b₁⁻¹ (utri F) = utri F :=
    mem_normalizer_iff_conjSubgroup_eq.1 (by rw [normalizer_utri]; exact inv_mem hb₁)
  have hb₂' : conjSubgroup b₂ (utri F) = utri F :=
    mem_normalizer_iff_conjSubgroup_eq.1 (by rw [normalizer_utri]; exact hb₂)
  refine ⟨b₁⁻¹ * a⁻¹, ?_, ?_⟩
  · rw [mul_assoc, inv_mul_cancel, mul_one]
    exact hb₁'
  · rw [mul_assoc, hbb, ← mul_assoc, inv_mul_cancel_left, ← conjSubgroup_conjSubgroup, hb₂',
      conjSubgroup_wElt_utri]

theorem conjTwoTransitive_utri : ConjTwoTransitive SL(2, F) (utri F) := by
  intro a b c d hab hcd
  obtain ⟨g₁, h1a, h1b⟩ := exists_conj_pair_normal_form hab
  obtain ⟨g₂, h2c, h2d⟩ := exists_conj_pair_normal_form hcd
  refine ⟨g₂⁻¹ * g₁, ?_, ?_⟩
  · calc conjSubgroup (g₂⁻¹ * g₁ * a) (utri F)
        = conjSubgroup g₂⁻¹ (conjSubgroup (g₁ * a) (utri F)) := by
          rw [conjSubgroup_conjSubgroup, mul_assoc]
      _ = conjSubgroup g₂⁻¹ (conjSubgroup (g₂ * c) (utri F)) := by rw [h1a, h2c]
      _ = conjSubgroup c (utri F) := by rw [conjSubgroup_conjSubgroup, inv_mul_cancel_left]
  · calc conjSubgroup (g₂⁻¹ * g₁ * b) (utri F)
        = conjSubgroup g₂⁻¹ (conjSubgroup (g₁ * b) (utri F)) := by
          rw [conjSubgroup_conjSubgroup, mul_assoc]
      _ = conjSubgroup g₂⁻¹ (conjSubgroup (g₂ * d) (utri F)) := by rw [h1b, h2d]
      _ = conjSubgroup d (utri F) := by rw [conjSubgroup_conjSubgroup, inv_mul_cancel_left]

theorem inf_conjSubgroup_utri_eq_bot {a b : SL(2, F)}
    (h : conjSubgroup a (utri F) ≠ conjSubgroup b (utri F)) :
    conjSubgroup a (utri F) ⊓ conjSubgroup b (utri F) = ⊥ := by
  have hab : a⁻¹ * b ∉ borel F := by
    intro hmem
    apply h
    rw [conjSubgroup_eq_conjSubgroup_iff, normalizer_utri]
    exact hmem
  have h1 := utri_inf_conj_eq_bot hab
  have h2 := congrArg (conjSubgroup a) h1
  rwa [conjSubgroup_inf_eq_inf, conjSubgroup_conjSubgroup, mul_inv_cancel_left,
    conjSubgroup_bot] at h2

end TwoTransitive

section Gauss

variable {F : Type} [Field F]

theorem mem_sup_of_apply_10_ne_zero {g : SL(2, F)} (hc : g 1 0 ≠ 0) : g ∈ utri F ⊔ ltri F := by
  have hd := sl2_det g
  have hg : g = utriElt ((g 0 0 - 1) / g 1 0) * ltriElt (g 1 0) *
      utriElt ((g 1 1 - 1) / g 1 0) := by
    apply sl2_ext
    all_goals sl2_simp
    · field_simp
      ring
    · field_simp
      linear_combination (-1) * hd
    · ring
    · field_simp
      ring
  rw [hg]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (utriElt_mem_utri _))
    (Subgroup.mem_sup_right (ltriElt_mem_ltri _))) (Subgroup.mem_sup_left (utriElt_mem_utri _))

theorem utri_sup_ltri : utri F ⊔ ltri F = ⊤ := by
  rw [eq_top_iff]
  intro g _
  by_cases hc : g 1 0 = 0
  · have hd := sl2_det g
    have h00 : g 0 0 ≠ 0 := by
      intro h
      rw [h, hc] at hd
      simp at hd
    have hh : (ltriElt (1 : F) * g) 1 0 ≠ 0 := by
      rw [mul_apply_10, ltriElt_apply_10, ltriElt_apply_11, hc]
      simpa using h00
    have hmem := mem_sup_of_apply_10_ne_zero hh
    have hl : (ltriElt (1 : F))⁻¹ ∈ utri F ⊔ ltri F :=
      Subgroup.mem_sup_right (inv_mem (ltriElt_mem_ltri 1))
    have := Subgroup.mul_mem _ hl hmem
    simpa using this
  · exact mem_sup_of_apply_10_ne_zero hc

theorem utriElt_ne_one {s : F} (hs : s ≠ 0) : (utriElt s : SL(2, F)) ≠ 1 := fun h =>
  hs (utriElt_injective (h.trans utriElt_zero.symm))

theorem ltriElt_ne_one {t : F} (ht : t ≠ 0) : (ltriElt t : SL(2, F)) ≠ 1 := by
  intro h
  have h10 := congrArg (fun g : SL(2, F) => g 1 0) h
  simp only [ltriElt_apply_10, one_apply_10] at h10
  exact ht h10

end Gauss

section Card

variable {F : Type} [Field F] [Finite F]

theorem two_le_natCard_field : 2 ≤ Nat.card F := Finite.one_lt_card

theorem card_sl2 : Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2Syl.IASL2.natCard_sl2

end Card

section SylowSL

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_natCard_eq_two_pow : ∃ n : ℕ, 0 < n ∧ Nat.card F = 2 ^ n := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem isPGroup_utri : IsPGroup 2 (utri F) := by
  obtain ⟨n, -, hn⟩ := exists_natCard_eq_two_pow (F := F)
  exact IsPGroup.of_card (n := n) (card_utri.trans hn)

theorem odd_index_utri : Odd (utri F).index := by
  have h := Subgroup.card_mul_index (utri F)
  rw [card_utri, card_sl2] at h
  have hidx : (utri F).index = Nat.card F ^ 2 - 1 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  obtain ⟨n, hn1, hn⟩ := exists_natCard_eq_two_pow (F := F)
  rw [hidx, hn]
  refine Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) ?_ odd_one
  exact Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hn1.ne'⟩, two_ne_zero⟩

variable (F) in
@[expose] noncomputable def utriSylow : Sylow 2 SL(2, F) :=
  IsPGroup.toSylow isPGroup_utri (by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact odd_index_utri)

theorem coe_utriSylow : (utriSylow F : Subgroup SL(2, F)) = utri F := rfl

theorem exists_conjSubgroup_utri_eq_of_sylow (P : Sylow 2 SL(2, F)) :
    ∃ g : SL(2, F), conjSubgroup g (utri F) = (P : Subgroup SL(2, F)) :=
  exists_conjSubgroup_eq_of_sylow (utriSylow F) P

theorem exists_conj_utriElt_one {g : SL(2, F)} (hg : g * g = 1) (hg1 : g ≠ 1) :
    ∃ x : SL(2, F), x * utriElt 1 * x⁻¹ = g := by
  obtain ⟨P, hP⟩ := (isPGroup_two_zpowers_of_mul_self_eq_one hg).exists_le_sylow
  obtain ⟨x, hx⟩ := exists_conjSubgroup_utri_eq_of_sylow P
  have hgP : g ∈ conjSubgroup x (utri F) := by
    rw [hx]
    exact hP (Subgroup.mem_zpowers g)
  obtain ⟨s, hs⟩ := mem_utri_iff.1 (mem_conjSubgroup.1 hgP)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hg1
    rw [utriElt_zero] at hs
    have : g = x * (x⁻¹ * g * x) * x⁻¹ := by group
    rw [this, hs]
    group
  obtain ⟨b, hb, hbs⟩ := exists_mem_borel_conj_utriElt one_ne_zero hs0
  refine ⟨x * b, ?_⟩
  calc x * b * utriElt 1 * (x * b)⁻¹ = x * (b * utriElt 1 * b⁻¹) * x⁻¹ := by group
    _ = x * utriElt s * x⁻¹ := by rw [hbs]
    _ = g := by rw [← hs]; group

theorem isConj_of_mul_self_eq_one {g h : SL(2, F)} (hg : g * g = 1) (hg1 : g ≠ 1)
    (hh : h * h = 1) (hh1 : h ≠ 1) : IsConj g h := by
  obtain ⟨x, hx⟩ := exists_conj_utriElt_one hg hg1
  obtain ⟨y, hy⟩ := exists_conj_utriElt_one hh hh1
  refine isConj_iff.2 ⟨y * x⁻¹, ?_⟩
  rw [← hx, ← hy]
  group

theorem existsUnique_sylow_of_mul_self_eq_one {g : SL(2, F)} (hg : g * g = 1) (hg1 : g ≠ 1) :
    ∃! P : Sylow 2 SL(2, F), g ∈ (P : Subgroup SL(2, F)) := by
  obtain ⟨P, hP⟩ := (isPGroup_two_zpowers_of_mul_self_eq_one hg).exists_le_sylow
  refine ⟨P, hP (Subgroup.mem_zpowers g), fun Q hQ => ?_⟩
  by_contra hne
  obtain ⟨x, hx⟩ := exists_conjSubgroup_utri_eq_of_sylow P
  obtain ⟨y, hy⟩ := exists_conjSubgroup_utri_eq_of_sylow Q
  have hne' : conjSubgroup x (utri F) ≠ conjSubgroup y (utri F) := by
    rw [hx, hy]
    exact fun h => hne (Sylow.ext h).symm
  have hgx : g ∈ conjSubgroup x (utri F) := by
    rw [hx]
    exact hP (Subgroup.mem_zpowers g)
  have hgy : g ∈ conjSubgroup y (utri F) := by
    rw [hy]
    exact hQ
  have hmem : g ∈ conjSubgroup x (utri F) ⊓ conjSubgroup y (utri F) := ⟨hgx, hgy⟩
  rw [inf_conjSubgroup_utri_eq_bot hne', Subgroup.mem_bot] at hmem
  exact hg1 hmem

theorem centralizer_eq_of_mem_sylow {g : SL(2, F)} (hg1 : g ≠ 1) {P : Sylow 2 SL(2, F)}
    (hgP : g ∈ (P : Subgroup SL(2, F))) : Subgroup.centralizer ({g} : Set SL(2, F)) = P := by
  obtain ⟨x, hx⟩ := exists_conjSubgroup_utri_eq_of_sylow P
  have hgx : g ∈ conjSubgroup x (utri F) := by
    rw [hx]
    exact hgP
  obtain ⟨s, hs⟩ := mem_utri_iff.1 (mem_conjSubgroup.1 hgx)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hg1
    rw [utriElt_zero] at hs
    have : g = x * (x⁻¹ * g * x) * x⁻¹ := by group
    rw [this, hs]
    group
  have hg : g = x * utriElt s * x⁻¹ := by rw [← hs]; group
  rw [hg, centralizer_conj_singleton, centralizer_utriElt hs0, hx]

end SylowSL

end CFSG.CGT.Timmesfeld75

module

public import Certificates.Data.Kernel.Tower.L3Q
public import CFSG.Certificates.Kernel.Tower.Cls14Sound
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerFactsIso

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower Subgroup

variable {X : Type*} [Group X] {n : Nat} {mul : Nat → Nat → Nat} {dec : Nat → X}

theorem l3q_mem_of_count {N : Nat} {p : Nat → Bool} {f : Nat → Nat} (hcnt : cntB n p = N)
    (hf : ∀ j < N, f j < n ∧ p (f j) = true) (hmono : ∀ j, j + 1 < N → f j < f (j + 1)) :
    ∀ c < n, p c = true → ∃ j < N, f j = c := by
  classical
  have hst : ∀ i j, i < j → j < N → f i < f j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
      · exact lt_trans (ih h (by omega)) (hmono j hj)
      · exact hmono i hj
  let F := (Finset.range n).filter fun q => p q = true
  let I := (Finset.range N).image f
  have hIF : I ⊆ F := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    rw [Finset.mem_range] at hj
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hf j hj).1, (hf j hj).2⟩
  have hI : I.card = N := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb h
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    rcases Nat.lt_trichotomy a b with h1 | h1 | h1
    · exact absurd h (Nat.ne_of_lt (hst a b h1 hb))
    · exact h1
    · exact absurd h (Nat.ne_of_gt (hst b a h1 ha))
  have hFc : F.card = N := by rw [← hcnt, cntB_eq_card]
  have hEq : I = F := Finset.eq_of_subset_of_card_le hIF (by rw [hI, hFc])
  intro c hc hp
  have hcF : c ∈ F := Finset.mem_filter.2 ⟨Finset.mem_range.2 hc, hp⟩
  rw [← hEq] at hcF
  obtain ⟨j, hj, e⟩ := Finset.mem_image.1 hcF
  exact ⟨j, Finset.mem_range.1 hj, e⟩

theorem hOK_mem (M : IsModel (⊤ : Subgroup X) n mul dec) {t HL : Nat} (ht : t < n)
    (h : hOK n mul t HL = true) :
    ∀ x : X, x * dec t = dec t * x → ∃ j < 128, dec (hL HL j) = x := by
  simp only [hOK, Bool.and_eq_true, allB_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  intro x hx
  have hc := M.code_lt (mem_top x)
  have hxc := M.dec_code (mem_top x)
  have hp : Nat.beq (mul (M.code x) t) (mul t (M.code x)) = true := by
    rw [Nat.beq_eq, M.comm_iff hc ht, hxc]
    exact hx
  obtain ⟨j, hj, e⟩ := l3q_mem_of_count (f := hL HL) (Nat.eq_of_beq_eq_true h3)
    (fun j hj => ⟨Nat.le_of_ble_eq_true (h1 j hj).1, (h1 j hj).2⟩)
    (fun j hj => Nat.le_of_ble_eq_true (h2 j (by omega))) _ hc hp
  exact ⟨j, hj, by rw [e, hxc]⟩

theorem hOK16_mem (M : IsModel (⊤ : Subgroup X) n mul dec) {t HL : Nat}
    (h : hOK16 n mul t HL = true) :
    ∀ x : X, x * dec t = dec t * x → ∃ m < 256, dec (l16 HL m) = x := by
  simp only [hOK16, Bool.and_eq_true, allB_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have ht : t < n := Nat.le_of_ble_eq_true h0
  intro x hx
  have hc := M.code_lt (mem_top x)
  have hxc := M.dec_code (mem_top x)
  have hp : Nat.beq (mul (M.code x) t) (mul t (M.code x)) = true := by
    rw [Nat.beq_eq, M.comm_iff hc ht, hxc]
    exact hx
  obtain ⟨j, hj, e⟩ := l3q_mem_of_count (f := l16 HL) (Nat.eq_of_beq_eq_true h3)
    (fun j hj => ⟨Nat.le_of_ble_eq_true (h1 j hj).1, (h1 j hj).2⟩)
    (fun j hj => Nat.le_of_ble_eq_true (h2 j (by omega))) _ hc hp
  exact ⟨j, hj, by rw [e, hxc]⟩

theorem icB_sound (M : IsModel (⊤ : Subgroup X) n mul dec) (hn : n = 16384) {GS PT : Nat}
    (hT : treeB n 4 mul GS PT = true) {OT LB RP CZ GI nl : Nat}
    (hord : ordOK n mul OT = true) (hlab : labOK16 n 4 mul GS GI LB RP nl = true)
    (hcz : czOK16 n LB CZ = true) (hic : icB OT RP CZ nl = true) :
    ∀ x : X, x ^ 2 = 1 → x ≠ 1 → 2 ^ 8 ≤ Nat.card (centralizer {x} : Subgroup X) := by
  intro x hx2 hx1
  obtain ⟨hfin, hX⟩ := cls16_finite M
  have hc := M.code_lt (mem_top x)
  have hxc := M.dec_code (mem_top x)
  have hl := ((cls16_labParts hlab).2.2 _ hc).1
  obtain ⟨hr, hrep⟩ := cls16_rep M hlab hc
  generalize dec (lbW LB (M.code x)) = w at hrep
  generalize hR : l16 RP (lbL LB (M.code x)) = r at hr hrep
  have er : w⁻¹ * x * w⁻¹⁻¹ = dec r := by
    rw [← hxc, hrep]
    group
  have hr2 : dec r ^ 2 = 1 ∧ dec r ≠ 1 := by
    rw [← er]
    refine ⟨by rw [conj_pow, hx2]; group, fun h => hx1 ?_⟩
    have h' : w * (w⁻¹ * x * w⁻¹⁻¹) * w⁻¹ = w * 1 * w⁻¹ := by rw [h]
    simpa [mul_assoc] using h'
  have hoe := (cls16_oe_one M hord hr).2 ((M.dec_sq_iff hr).1 hr2)
  have hi := allB_eq_true.1 hic _ hl
  rw [hR, hoe] at hi
  simp only [Nat.beq_refl, Bool.not_true, Bool.false_or] at hi
  have h64 := Nat.le_of_ble_eq_true hi
  have ho := cls16_card M (by omega) hT hlab hcz hc
  rw [hxc] at ho
  have hcm := card_cent_mul x
  rw [hX, ho] at hcm
  by_contra hlt
  have hle : Nat.card (centralizer {x} : Subgroup X) ≤ 255 := by omega
  have hm := Nat.mul_le_mul h64 hle
  rw [hcm] at hm
  omega

end Certificates.KernelTower

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup

variable {X : Type*} [Group X]

theorem CycExt.incl_inj (D : ExtData X) : Function.Injective (CycExt.incl D) := fun _ _ h =>
  congrArg CycExt.k h

theorem CycExt.conj_y (D : ExtData X) (x : X) :
    (⟨1, true⟩ : CycExt D) * CycExt.incl D x * (⟨1, true⟩ : CycExt D)⁻¹ =
      CycExt.incl D (D.α x) := by
  change (⟨1, true⟩ * ⟨x, false⟩ * (⟨1, true⟩ : CycExt D)⁻¹ : CycExt D) = ⟨D.α x, false⟩
  rw [CycExt.inv_mk_true, CycExt.mk_mul_mk, CycExt.mk_mul_mk]
  simp only [CycExt.pw, CycExt.sq, ite_true, Bool.and_false, Bool.and_true, Bool.false_eq_true,
    ite_false, Bool.xor_false, Bool.xor_true, Bool.not_true, mul_one, one_mul, map_mul, map_inv,
    map_one, D.hαg, inv_one, CycExt.mk.injEq, and_true]
  group

theorem isPInv_of_incl {D : ExtData X} {a : X}
    (hc : 2 ^ 8 ≤ Nat.card (centralizer {a} : Subgroup X)) (h : IsPInv (CycExt.incl D a)) :
    IsPInv a := by
  have hφ := CycExt.incl_inj D
  rw [← isPInv_map_iff hφ]
  obtain ⟨h2, h1, hP⟩ := h
  have hfin : Finite (centralizer {CycExt.incl D a} : Subgroup (CycExt D)) :=
    Nat.finite_of_card_ne_zero (by rw [hP.1]; norm_num)
  have heq : (CycExt.incl D).range ⊓ centralizer {CycExt.incl D a} =
      centralizer {CycExt.incl D a} := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
    rw [card_cent_map hφ, hP.1]
    exact hc
  refine ⟨⟨a, rfl⟩, h2, h1, ?_⟩
  rw [heq]
  exact hP

theorem conj_of_inside {D : ExtData X} {t x₀ : X} (hα : D.α x₀ = t)
    (hcls : ∀ x : X, IsPInv x → Conj x t ∨ Conj x x₀)
    (hc : ∀ x : X, x ^ 2 = 1 → x ≠ 1 → 2 ^ 8 ≤ Nat.card (centralizer {x} : Subgroup X)) (a : X)
    (h : IsPInv (CycExt.incl D a)) : Conj (CycExt.incl D a) (CycExt.incl D t) := by
  have hφ := CycExt.incl_inj D
  have h2 : a ^ 2 = 1 := hφ (by rw [map_pow, h.1, map_one])
  have h1 : a ≠ 1 := fun e => h.2.1 (by rw [e, map_one])
  rcases hcls a (isPInv_of_incl (hc a h2 h1) h) with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨CycExt.incl D k, by rw [map_mul, map_mul, map_inv]⟩
  · refine ⟨CycExt.incl D k * (⟨1, true⟩ : CycExt D)⁻¹, ?_⟩
    have e := CycExt.conj_y D x₀
    rw [hα] at e
    rw [map_mul, map_mul, map_inv, ← e]
    group

theorem cycQ {D : ExtData X} (χ : X → Nat) (h01 : ∀ x, χ x = 0 ∨ χ x = 1)
    (hmul : ∀ a b, χ (a * b) = χ a ^^^ χ b) (hα : ∀ x, χ (D.α x) = χ x) (hg : χ D.g = 0)
    {t : X} (ht : χ t = 1) :
    ∃ Q : Subgroup (CycExt D), Q.index = 2 ∧ CycExt.incl D t ∉ Q := by
  have h1 : χ 1 = 0 := by
    have e := hmul 1 1
    rw [mul_one, Nat.xor_self] at e
    exact e
  have hψ : ∀ a b : CycExt D, χ (a * b).k = χ a.k ^^^ χ b.k := by
    rintro ⟨k, d⟩ ⟨k', d'⟩
    rw [CycExt.mk_mul_mk]
    cases d <;> cases d' <;>
      simp only [CycExt.pw, CycExt.sq, hmul, hα, hg, h1, ite_true, ite_false, Bool.and_true,
        Bool.and_false, Bool.false_eq_true, Nat.xor_zero]
  let Q : Subgroup (CycExt D) :=
    { carrier := {a | χ a.k = 0}
      mul_mem' := fun {a b} ha hb => by
        change χ (a * b).k = 0
        rw [hψ, ha, hb]
        rfl
      one_mem' := h1
      inv_mem' := fun {a} ha => by
        change χ a⁻¹.k = 0
        have e := hψ a⁻¹ a
        rw [inv_mul_cancel, CycExt.one_def] at e
        change χ 1 = _ at e
        change χ a.k = 0 at ha
        rw [h1, ha, Nat.xor_zero] at e
        exact e.symm }
  refine ⟨Q, Subgroup.index_eq_two_iff.mpr ⟨CycExt.incl D t, fun b => ?_⟩, ?_⟩
  · change Xor' (χ (b * CycExt.incl D t).k = 0) (χ b.k = 0)
    rw [hψ]
    change Xor' (χ b.k ^^^ χ t = 0) (χ b.k = 0)
    rw [ht]
    rcases h01 b.k with hb | hb <;> rw [hb] <;> simp [Xor']
  · change ¬ χ t = 0
    rw [ht]
    decide

theorem l3Facts_of_parts {D : ExtData X} {t x₀ : X} (hα : D.α x₀ = t) (χ : X → Nat)
    (h01 : ∀ x, χ x = 0 ∨ χ x = 1) (hmul : ∀ a b, χ (a * b) = χ a ^^^ χ b)
    (hχα : ∀ x, χ (D.α x) = χ x) (hg : χ D.g = 0) (ht : χ t = 1)
    (hcls : ∀ x : X, IsPInv x → Conj x t ∨ Conj x x₀)
    (hc : ∀ x : X, x ^ 2 = 1 → x ≠ 1 → 2 ^ 8 ≤ Nat.card (centralizer {x} : Subgroup X))
    (hout : ∀ x : CycExt D, x.d = true → ¬IsPInv x) : L3Facts (CycExt D) (CycExt.incl D t) := by
  obtain ⟨Q, hQ, htQ⟩ := cycQ χ h01 hmul hχα hg ht
  refine ⟨Q, hQ, htQ, fun x hx => ?_⟩
  obtain ⟨k, d⟩ := x
  cases d
  · exact conj_of_inside hα hcls hc k hx
  · exact absurd hx (hout _ rfl)

variable {Y Z : Type*} [Group Y] [Group Z]

theorem l3Facts_map (e : Y ≃* Z) {t : Y} (h : L3Facts Y t) : L3Facts Z (e t) := by
  obtain ⟨Q, hQ, ht, hP⟩ := h
  have hs : Function.Surjective (e.symm : Z →* Y) := e.symm.surjective
  refine ⟨Q.comap (e.symm : Z →* Y), by rw [Q.index_comap_of_surjective hs, hQ], ?_,
    fun z hz => ?_⟩
  · change e.symm (e t) ∉ Q
    rw [e.symm_apply_apply]
    exact ht
  · have hφ : Function.Injective (e : Y →* Z) := e.injective
    have hz' : IsPInv (e.symm z) := by
      rw [← isPInv_map_iff hφ]
      change IsPInvol (e : Y →* Z).range (e (e.symm z))
      rw [e.apply_symm_apply]
      have hr : (e : Y →* Z).range = ⊤ := MonoidHom.range_eq_top.2 e.surjective
      rw [hr, IsPInvol, top_inf_eq]
      exact ⟨mem_top z, hz⟩
    obtain ⟨k, hk⟩ := hP _ hz'
    refine ⟨e k, ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul, ← hk, e.apply_symm_apply]

theorem l3Facts_ofConj {G : Type*} [Group G] {φ : X →* G} (hφ : Function.Injective φ) {c : G}
    (hcN : c ∈ normalizer (φ.range : Set G)) (hc2 : c ^ 2 ∈ φ.range) (hcK : c ∉ φ.range)
    (hs : Function.Surjective (cycHom hφ hcN hc2)) {t : X}
    (h : L3Facts (CycExt (ExtData.ofConj hφ hcN hc2)) (CycExt.incl _ t)) : L3Facts G (φ t) := by
  have h' := l3Facts_map (MulEquiv.ofBijective _ ⟨cycHom_injective hφ hcN hc2 hcK, hs⟩) h
  have e : (MulEquiv.ofBijective _ ⟨cycHom_injective hφ hcN hc2 hcK, hs⟩)
      (CycExt.incl (ExtData.ofConj hφ hcN hc2) t) = φ t := cycHom_incl hφ hcN hc2 t
  rwa [e] at h'

end CFSG.OddStandard.AltStdSmall4.Tower

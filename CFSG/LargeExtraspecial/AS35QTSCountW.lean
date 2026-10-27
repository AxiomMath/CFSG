module

public import CFSG.LargeExtraspecial.AS35QTSCount

public section

namespace CFSG.LargeExtraspecial.AS35QTS

open Subgroup

variable {G : Type} [Group G]

theorem conj_inv_ne {h a b : G} (hne : h * b * h⁻¹ ≠ a) : h⁻¹ * a * h ≠ b :=
  fun e => hne (by rw [← e]; group)

theorem inv_conj_mul_self {h v : G} (hv : v * v = 1) : h⁻¹ * v * h * (h⁻¹ * v * h) = 1 := by
  rw [show h⁻¹ * v * h * (h⁻¹ * v * h) = h⁻¹ * (v * v) * h by group, hv]
  group

theorem inv_conj_injective {h a b : G} (e : h⁻¹ * a * h = h⁻¹ * b * h) : a = b := by
  have := congrArg (fun y => h * y * h⁻¹) e
  simpa using this

theorem inv_conj_ne_one {h v : G} (hv : v ≠ 1) : h⁻¹ * v * h ≠ 1 :=
  fun e => hv (inv_conj_injective (h := h) (by rw [e]; group))

theorem inv_conj_comm {h a b : G} (hab : a * b = b * a) :
    h⁻¹ * a * h * (h⁻¹ * b * h) = h⁻¹ * b * h * (h⁻¹ * a * h) := by
  have := commute_conj h⁻¹ hab
  simpa [mul_assoc] using this

namespace Chart

variable {S : Setting G} [Finite G] (T : Chart S)

section W

variable {t₀ : G} (hS : S.SixHyp) (ht₀ : t₀ ∈ S.DSet)
include hS ht₀

include T in
theorem mem_line_of_commute_w {x : G} (hx : IsConj S.z x)
    (hxw : x * (S.z * t₀) = S.z * t₀ * x) : x ∈ lineSet S S.z t₀ := by
  obtain ⟨h1, h2⟩ := T.commute_of_commute_zt hS ht₀ hx hxw
  exact ⟨hx, h1, h2⟩

include T in
theorem isConj_w_of_swap {v : G} (hv : v * v = 1) (hvz : v * S.z * v⁻¹ = t₀) :
    IsConj (S.z * t₀) v := by
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  refine (T.isConj_w_iff ht₀ hS).mpr ⟨hv, fun h => t0_ne ht₀ ?_, fun h => ?_⟩
  · rw [← hvz, h]
    group
  · have hsq : (S.z * v) ^ 2 = S.z * t₀ := by
      rw [pow_two, ← hvz, hvinv]
      group
    have h4 : (S.z * v) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq, pow_two, w_mul_self ht₀ hS]
    have := T.sq_eq_one_of_pow_four hS (IsConj.refl S.z) h h4
    rw [hsq] at this
    exact w_ne_one ht₀ this

include T in
theorem mem_pair_of_swap {x v : G} (hx : x ∈ lineSet S S.z t₀) (hv : v * v = 1)
    (hvz : v * S.z * v⁻¹ = t₀) (hw : S.z * t₀ ∈ zpowers (x * v)) : x = S.z ∨ x = t₀ := by
  have ht₀M := t0_mem_M ht₀ hS
  have hzt : t₀ * S.z = S.z * t₀ := S.mem_M_iff.mp ht₀M
  have ht₀z := t0_isConj ht₀
  have hne := t0_ne ht₀
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hvt : v * t₀ * v⁻¹ = S.z := by
    rw [← hvz]
    calc v * (v * S.z * v⁻¹) * v⁻¹ = (v * v) * S.z * (v * v)⁻¹ := by group
      _ = S.z := by rw [hv]; group
  have hxl := hx
  obtain ⟨hxz, hxz', hxt⟩ := hx
  have hcz : x * v * S.z * (x * v)⁻¹ = t₀ := by
    calc x * v * S.z * (x * v)⁻¹ = x * (v * S.z * v⁻¹) * x⁻¹ := by group
      _ = t₀ := by rw [hvz, hxt]; group
  have hct : x * v * t₀ * (x * v)⁻¹ = S.z := by
    calc x * v * t₀ * (x * v)⁻¹ = x * (v * t₀ * v⁻¹) * x⁻¹ := by group
      _ = S.z := by rw [hvt, hxz']; group
  have hc2 : (x * v) ^ 2 * t₀ = t₀ * (x * v) ^ 2 := by
    have : (x * v) ^ 2 * t₀ * ((x * v) ^ 2)⁻¹ = t₀ := by
      rw [pow_two]
      calc x * v * (x * v) * t₀ * (x * v * (x * v))⁻¹ =
          x * v * (x * v * t₀ * (x * v)⁻¹) * (x * v)⁻¹ := by group
        _ = t₀ := by rw [hct, hcz]
    calc (x * v) ^ 2 * t₀ = (x * v) ^ 2 * t₀ * ((x * v) ^ 2)⁻¹ * (x * v) ^ 2 := by group
      _ = t₀ * (x * v) ^ 2 := by rw [this]
  have hx''l : v * x * v⁻¹ ∈ lineSet S S.z t₀ := by
    have := conj_mem_lineSet S v hxl
    rw [hvz, hvt, lineSet_symm] at this
    exact this
  have hc2e : (x * v) ^ 2 = x * (v * x * v⁻¹) := by rw [pow_two, hvinv]; group
  have hcomm := T.commute_of_mem_lineSet_at hS (IsConj.refl S.z) ht₀z hzt hne hxl hx''l
  have hxx := S.mul_self_of_isConj hxz
  have hx''x'' := S.mul_self_of_isConj hx''l.1
  have hsq1 : x * (v * x * v⁻¹) * (x * (v * x * v⁻¹)) = 1 := by
    calc x * (v * x * v⁻¹) * (x * (v * x * v⁻¹)) =
        x * ((v * x * v⁻¹) * x) * (v * x * v⁻¹) := by group
      _ = x * (x * (v * x * v⁻¹)) * (v * x * v⁻¹) := by rw [hcomm]
      _ = 1 := by rw [← mul_assoc x x, hxx, one_mul, hx''x'']
  obtain ⟨k, hk⟩ := hw
  simp only at hk
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  ·
    have hwe : S.z * t₀ = (x * (v * x * v⁻¹)) ^ j := by
      rw [← hk, ← two_mul, zpow_mul, zpow_two, ← pow_two, hc2e]
    have hmem : S.z * t₀ ∈ zpowers (x * (v * x * v⁻¹)) := ⟨j, hwe.symm⟩
    rcases (Setting.mem_zpowers_iff_of_mul_self hsq1).mp hmem with h1 | h1
    · exact absurd h1 (w_ne_one ht₀)
    · have hne' : x ≠ v * x * v⁻¹ := by
        intro h
        apply w_ne_one ht₀
        rw [h1, ← h, hxx]
      rcases T.eq_of_mul_eq_at hS (IsConj.refl S.z) ht₀z hzt hne hxl hx''l
        (self_mem_lineSet S (IsConj.refl S.z) hzt) (mem_lineSet_right S ht₀z hzt) hne'
        hne.symm h1.symm with ⟨h2, -⟩ | ⟨h2, -⟩
      · exact Or.inl h2
      · exact Or.inr h2
  ·
    exfalso
    have hcj : ((x * v) ^ 2) ^ j * t₀ * (((x * v) ^ 2) ^ j)⁻¹ = t₀ := by
      rw [(Commute.zpow_left hc2 j).eq]
      group
    have hw' : (S.z * t₀) * S.z * (S.z * t₀)⁻¹ = t₀ := by
      rw [← hk, show (x * v) ^ (2 * j + 1) = ((x * v) ^ 2) ^ j * (x * v) by
        rw [zpow_add, zpow_one, zpow_mul, zpow_two, ← pow_two]]
      calc ((x * v) ^ 2) ^ j * (x * v) * S.z * (((x * v) ^ 2) ^ j * (x * v))⁻¹ =
          ((x * v) ^ 2) ^ j * (x * v * S.z * (x * v)⁻¹) * (((x * v) ^ 2) ^ j)⁻¹ := by group
        _ = t₀ := by rw [hcz, hcj]
    apply hne
    rw [← hw']
    calc S.z * t₀ * S.z * (S.z * t₀)⁻¹ = S.z * (t₀ * S.z) * t₀⁻¹ * S.z⁻¹ := by group
      _ = S.z := by rw [hzt]; group

include T in
theorem ncard_swap_fix {c : G} (hc : c ∈ lineSet S S.z t₀) (hcz : c ≠ S.z) (hct : c ≠ t₀) :
    {v : G | v * v = 1 ∧ v * S.z * v⁻¹ = t₀ ∧ v * c = c * v}.ncard = 16 := by
  classical
  have ht₀M := t0_mem_M ht₀ hS
  have hzt : t₀ * S.z = S.z * t₀ := S.mem_M_iff.mp ht₀M
  obtain ⟨hcD, hcz', hct'⟩ := hc
  obtain ⟨h, rfl⟩ := isConj_iff.mp hcD
  have hz'M : h⁻¹ * S.z * h ∈ S.M := conj_inv_mem_M S hcz'.symm
  have ht'M : h⁻¹ * t₀ * h ∈ S.M := conj_inv_mem_M S hct'.symm
  have hz'z : IsConj S.z (h⁻¹ * S.z * h) := by simpa using isConj_conj S h⁻¹ (IsConj.refl S.z)
  have ht'z : IsConj S.z (h⁻¹ * t₀ * h) := by simpa using isConj_conj S h⁻¹ (t0_isConj ht₀)
  have hp := T.th_mem_sl hS.weak hz'M hz'z (conj_inv_ne hcz)
  have hp' := T.th_mem_sl hS.weak ht'M ht'z (conj_inv_ne hct)
  have hpp : T.th (h⁻¹ * S.z * h) ≠ T.th (h⁻¹ * t₀ * h) := fun e =>
    t0_ne ht₀ (inv_conj_injective (T.th_injOn _ hz'M _ ht'M e)).symm
  have hcomm : mulC (T.th (h⁻¹ * S.z * h)) (T.th (h⁻¹ * t₀ * h)) =
      mulC (T.th (h⁻¹ * t₀ * h)) (T.th (h⁻¹ * S.z * h)) :=
    (T.th_comm hz'M ht'M).mp (inv_conj_comm hzt.symm)
  rw [← (qts_swap _ _ hp hp' hpp hcomm).1, ← Set.ncard_coe_finset]
  have hinj : Set.InjOn (fun v => T.th (h⁻¹ * v * h))
      {v : G | v * v = 1 ∧ v * S.z * v⁻¹ = t₀ ∧ v * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * v} :=
    fun v hv v' hv' e => inv_conj_injective
      (T.th_injOn _ (conj_inv_mem_M S hv.2.2) _ (conj_inv_mem_M S hv'.2.2) e)
  rw [← hinj.ncard_image]
  congr 1
  ext u
  simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_filter, List.mem_toFinset]
  constructor
  · rintro ⟨v, ⟨hv2, hvz, hvc⟩, rfl⟩
    have hvM := conj_inv_mem_M S hvc
    have hv1 : v ≠ 1 := fun e => t0_ne ht₀ (by rw [← hvz, e]; group)
    have hil := T.th_mem_il hvM (inv_conj_mul_self hv2) (inv_conj_ne_one hv1)
    refine ⟨hil, ?_⟩
    rw [← T.th_mul _ hvM _ hz'M, ← T.th_mul _ ht'M _ hvM]
    congr 1
    calc h⁻¹ * v * h * (h⁻¹ * S.z * h) = h⁻¹ * (v * S.z * v⁻¹) * (h * h⁻¹) * v * h := by group
      _ = h⁻¹ * t₀ * h * (h⁻¹ * v * h) := by rw [hvz]; group
  · rintro ⟨hu, hue⟩
    obtain ⟨v', hv'M, rfl⟩ := T.th_surj u (mem_il.mp hu).1
    obtain ⟨hv'2, -⟩ := T.mul_self_of_mem_il hv'M hu
    have hv'e : v' * (h⁻¹ * S.z * h) = h⁻¹ * t₀ * h * v' := by
      rw [← T.th_mul _ hv'M _ hz'M, ← T.th_mul _ ht'M _ hv'M] at hue
      exact T.th_injOn _ (S.M.mul_mem hv'M hz'M) _ (S.M.mul_mem ht'M hv'M) hue
    refine ⟨h * v' * h⁻¹, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [show h * v' * h⁻¹ * (h * v' * h⁻¹) = h * (v' * v') * h⁻¹ by group, hv'2]
      group
    · calc h * v' * h⁻¹ * S.z * (h * v' * h⁻¹)⁻¹ =
          h * (v' * (h⁻¹ * S.z * h)) * v'⁻¹ * h⁻¹ := by group
        _ = t₀ := by rw [hv'e]; group
    · have := commute_conj h (S.mem_M_iff.mp hv'M)
      simpa [mul_assoc] using this
    · show T.th (h⁻¹ * (h * v' * h⁻¹) * h) = T.th v'
      congr 1
      group

include T in
theorem not_fix_two {c c' v : G} (hc : c ∈ lineSet S S.z t₀) (hcz : c ≠ S.z) (hct : c ≠ t₀)
    (hc' : c' ∈ lineSet S S.z t₀) (hc't : c' ≠ t₀) (hcc : c ≠ c') (hc'z : c' ≠ S.z)
    (hv2 : v * v = 1) (hvz : v * S.z * v⁻¹ = t₀) (hvc : v * c = c * v) (hvc' : v * c' = c' * v) :
    False := by
  have ht₀M := t0_mem_M ht₀ hS
  have hzt : t₀ * S.z = S.z * t₀ := S.mem_M_iff.mp ht₀M
  have hcc' := T.commute_of_mem_lineSet_at hS (IsConj.refl S.z) (t0_isConj ht₀) hzt (t0_ne ht₀)
    hc hc'
  obtain ⟨hcD, hcz', hct'⟩ := hc
  obtain ⟨hc'D, hc'z', hc't'⟩ := hc'
  obtain ⟨h, rfl⟩ := isConj_iff.mp hcD
  have hz'M : h⁻¹ * S.z * h ∈ S.M := conj_inv_mem_M S hcz'.symm
  have ht'M : h⁻¹ * t₀ * h ∈ S.M := conj_inv_mem_M S hct'.symm
  have hq'M : h⁻¹ * c' * h ∈ S.M := conj_inv_mem_M S hcc'.symm
  have hvM : h⁻¹ * v * h ∈ S.M := conj_inv_mem_M S hvc
  have hconjz : ∀ {a : G}, IsConj S.z a → IsConj S.z (h⁻¹ * a * h) := fun ha => by
    simpa using isConj_conj S h⁻¹ ha
  have hp := T.th_mem_sl hS.weak hz'M (hconjz (IsConj.refl S.z)) (conj_inv_ne hcz)
  have hp' := T.th_mem_sl hS.weak ht'M (hconjz (t0_isConj ht₀)) (conj_inv_ne hct)
  have hq := T.th_mem_sl hS.weak hq'M (hconjz hc'D) (conj_inv_ne hcc)
  have hpp : T.th (h⁻¹ * S.z * h) ≠ T.th (h⁻¹ * t₀ * h) := fun e =>
    t0_ne ht₀ (inv_conj_injective (T.th_injOn _ hz'M _ ht'M e)).symm
  have hpq : mulC (T.th (h⁻¹ * S.z * h)) (T.th (h⁻¹ * t₀ * h)) =
      mulC (T.th (h⁻¹ * t₀ * h)) (T.th (h⁻¹ * S.z * h)) :=
    (T.th_comm hz'M ht'M).mp (inv_conj_comm hzt.symm)
  have hv1 : v ≠ 1 := fun e => t0_ne ht₀ (by rw [← hvz, e]; group)
  have hvil : T.th (h⁻¹ * v * h) ∈ il :=
    T.th_mem_il hvM (inv_conj_mul_self hv2) (inv_conj_ne_one hv1)
  have hvzt : h⁻¹ * v * h * (h⁻¹ * S.z * h) = h⁻¹ * t₀ * h * (h⁻¹ * v * h) := by
    calc h⁻¹ * v * h * (h⁻¹ * S.z * h) = h⁻¹ * (v * S.z * v⁻¹) * (h * h⁻¹) * v * h := by group
      _ = h⁻¹ * t₀ * h * (h⁻¹ * v * h) := by rw [hvz]; group
  have hsw : mulC (T.th (h⁻¹ * v * h)) (T.th (h⁻¹ * S.z * h)) =
      mulC (T.th (h⁻¹ * t₀ * h)) (T.th (h⁻¹ * v * h)) := by
    rw [← T.th_mul _ hvM _ hz'M, ← T.th_mul _ ht'M _ hvM, hvzt]
  have h1 := (qts_swap _ _ hp hp' hpp hpq).2 _ hq
    (fun e => hc'z (inv_conj_injective (T.th_injOn _ hq'M _ hz'M e)))
    (fun e => hc't (inv_conj_injective (T.th_injOn _ hq'M _ ht'M e)))
    ((T.th_comm hz'M hq'M).mp (inv_conj_comm hc'z'.symm)) _ hvil hsw
  exact h1 ((T.th_comm hvM hq'M).mp (inv_conj_comm hvc'))

include T in
theorem ncard_swap : {v : G | v * v = 1 ∧ v * S.z * v⁻¹ = t₀}.ncard = 48 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have ht₀M := t0_mem_M ht₀ hS
  have hzt : t₀ * S.z = S.z * t₀ := S.mem_M_iff.mp ht₀M
  have ht₀z := t0_isConj ht₀
  have hne := t0_ne ht₀
  set Δ := lineSet S S.z t₀ \ {S.z, t₀} with hΔ
  have hpair : ({S.z, t₀} : Set G) ⊆ lineSet S S.z t₀ := by
    rintro y (rfl | rfl)
    · exact self_mem_lineSet S (IsConj.refl _) hzt
    · exact mem_lineSet_right S ht₀z hzt
  have hΔ3 : Δ.ncard = 3 := by
    rw [hΔ, Set.ncard_sdiff hpair, T.ncard_lineSet_at hS (IsConj.refl _) ht₀z hzt hne,
      Set.ncard_pair hne.symm]
  have hmemΔ : ∀ {c}, c ∈ Δ ↔ c ∈ lineSet S S.z t₀ ∧ c ≠ S.z ∧ c ≠ t₀ := by
    intro c
    simp only [hΔ, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  set Δf := (Set.toFinite Δ).toFinset
  set Jc : G → Finset G := fun c =>
    Finset.univ.filter fun v => v * v = 1 ∧ v * S.z * v⁻¹ = t₀ ∧ v * c = c * v
  have hJ : {v : G | v * v = 1 ∧ v * S.z * v⁻¹ = t₀} = ↑(Δf.biUnion Jc) := by
    ext v
    simp only [Set.mem_ofPred_eq, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
      Set.Finite.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop, Jc,
      Δf]
    constructor
    · rintro ⟨hv2, hvz⟩
      have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
      have hvt : v * t₀ * v⁻¹ = S.z := by
        rw [← hvz]
        calc v * (v * S.z * v⁻¹) * v⁻¹ = (v * v) * S.z * (v * v)⁻¹ := by group
          _ = S.z := by rw [hv2]; group
      have hvz' : v⁻¹ * S.z * v = t₀ := by simpa [hvinv] using hvz
      have hvt' : v⁻¹ * t₀ * v = S.z := by simpa [hvinv] using hvt
      have hmaps : ∀ y ∈ Δ, v * y * v⁻¹ ∈ Δ := by
        intro y hy
        obtain ⟨hyl, hyz, hyt⟩ := hmemΔ.mp hy
        refine hmemΔ.mpr ⟨?_, fun e => hyt ?_, fun e => hyz ?_⟩
        · have := conj_mem_lineSet S v hyl
          rwa [hvz, hvt, lineSet_symm] at this
        · calc y = v⁻¹ * (v * y * v⁻¹) * v := by group
            _ = t₀ := by rw [e, hvz']
        · calc y = v⁻¹ * (v * y * v⁻¹) * v := by group
            _ = S.z := by rw [e, hvt']
      have hinv : ∀ y ∈ Δ, v * (v * y * v⁻¹) * v⁻¹ = y := by
        intro y _
        calc v * (v * y * v⁻¹) * v⁻¹ = (v * v) * y * (v * v)⁻¹ := by group
          _ = y := by rw [hv2]; group
      obtain ⟨c, hc, hcv⟩ := exists_fixed_of_involutive (Set.toFinite Δ) (by rw [hΔ3]; decide)
        (fun y => v * y * v⁻¹) hmaps hinv
      refine ⟨c, hc, hv2, hvz, ?_⟩
      calc v * c = v * c * v⁻¹ * v := by group
        _ = c * v := by rw [hcv]
    · rintro ⟨c, -, hv2, hvz, -⟩
      exact ⟨hv2, hvz⟩
  rw [hJ, Set.ncard_coe_finset, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (g := fun _ => 16), Finset.sum_const, smul_eq_mul,
      ← Set.ncard_eq_toFinset_card _ (Set.toFinite Δ), hΔ3]
    intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    obtain ⟨hcl, hcz, hct⟩ := hmemΔ.mp hc
    rw [← T.ncard_swap_fix hS ht₀ hcl hcz hct, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp [Jc]
  · intro c hc c' hc' hcc
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hc hc'
    obtain ⟨hcl, hcz, hct⟩ := hmemΔ.mp hc
    obtain ⟨hcl', hcz', hct'⟩ := hmemΔ.mp hc'
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    simp only [Jc, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
    exact T.not_fix_two hS ht₀ hcl hcz hct hcl' hct' hcc hcz' hv.1 hv.2.1 hv.2.2 hv'.2.2

include T in
theorem count_w (htc : T.th t₀ = t0c) : thompsonCount S.z (S.z * t₀) (S.z * t₀) = 99 := by
  classical
  have ht₀M := t0_mem_M ht₀ hS
  have hzt : t₀ * S.z = S.z * t₀ := S.mem_M_iff.mp ht₀M
  have ht₀z := t0_isConj ht₀
  have hne := t0_ne ht₀
  have htt := S.mul_self_of_isConj ht₀z
  have hww := w_mul_self ht₀ hS
  set P := {p : G × G | IsConj S.z p.1 ∧ IsConj (S.z * t₀) p.2 ∧
    S.z * t₀ ∈ zpowers (p.1 * p.2)} with hP
  set J := {v : G | v * v = 1 ∧ v * S.z * v⁻¹ = t₀} with hJ
  have hthw : T.th (S.z * t₀) = mulC tau0 t0c := by rw [T.th_mul _ (z_mem_M S) _ ht₀M, T.th_z, htc]
  have hPfacts : ∀ p ∈ P, p.1 ∈ lineSet S S.z t₀ ∧ p.2 * p.2 = 1 ∧
      p.2 * (S.z * t₀) = S.z * t₀ * p.2 := by
    rintro ⟨x, v⟩ ⟨hx, hv, hw⟩
    have hvv := ((T.isConj_w_iff ht₀ hS).mp hv).1
    obtain ⟨h1, h2⟩ := commute_of_mem_zpowers (S.mul_self_of_isConj hx) hvv hw hww
    exact ⟨T.mem_line_of_commute_w hS ht₀ hx h1, hvv, h2⟩
  have hsplit : P = {p ∈ P | p.2 * S.z = S.z * p.2} ∪ {p ∈ P | ¬ p.2 * S.z = S.z * p.2} := by
    ext p
    simp only [Set.mem_union, Set.mem_sep_iff]
    tauto
  have hdisj : Disjoint {p ∈ P | p.2 * S.z = S.z * p.2} {p ∈ P | ¬ p.2 * S.z = S.z * p.2} := by
    rw [Set.disjoint_left]
    rintro p ⟨-, h1⟩ ⟨-, h2⟩
    exact h2 h1
  have hPb : {p ∈ P | ¬ p.2 * S.z = S.z * p.2} = ({S.z, t₀} : Set G) ×ˢ J := by
    ext ⟨x, v⟩
    simp only [Set.mem_sep_iff, Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp, hvz⟩
      obtain ⟨hxl, hvv, hvw⟩ := hPfacts _ hp
      have hvswap : v * S.z * v⁻¹ = t₀ := by
        rcases T.eq_or_eq_of_commute_zt hS ht₀ hvw with h | h
        · exact absurd (by calc v * S.z = v * S.z * v⁻¹ * v := by group
            _ = S.z * v := by rw [h]) hvz
        · exact h
      exact ⟨T.mem_pair_of_swap hS ht₀ hxl hvv hvswap hp.2.2, hvv, hvswap⟩
    · rintro ⟨hx, hvv, hvswap⟩
      have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
      have hvt : v * t₀ * v⁻¹ = S.z := by
        rw [← hvswap]
        calc v * (v * S.z * v⁻¹) * v⁻¹ = (v * v) * S.z * (v * v)⁻¹ := by group
          _ = S.z := by rw [hvv]; group
      refine ⟨⟨?_, T.isConj_w_of_swap hS ht₀ hvv hvswap, ?_⟩, fun h => hne ?_⟩
      · rcases hx with hx | hx
        · rw [hx]
        · rw [hx]; exact ht₀z
      · refine ⟨2, ?_⟩
        simp only [zpow_two]
        rcases hx with hx | hx
        · rw [hx]
          calc S.z * v * (S.z * v) = S.z * (v * S.z * v⁻¹) := by rw [hvinv]; group
            _ = S.z * t₀ := by rw [hvswap]
        · rw [hx]
          calc t₀ * v * (t₀ * v) = t₀ * (v * t₀ * v⁻¹) := by rw [hvinv]; group
            _ = S.z * t₀ := by rw [hvt, hzt]
      · rw [← hvswap, h]
        group
  have hPa : {p ∈ P | p.2 * S.z = S.z * p.2}.ncard = 3 := by
    rw [← qts_nw]
    refine T.ncard_pairs_eq (fun p hp => ?_) (fun p hp => ?_) (fun x hx v hv hq => ?_) ?_
    · exact ⟨mem_M_of_mem_lineSet S (hPfacts p hp.1).1, S.mem_M_iff.mpr hp.2⟩
    · obtain ⟨hxl, hvv, hvw⟩ := hPfacts p hp.1
      have hxM := mem_M_of_mem_lineSet S hxl
      have hvM : p.2 ∈ S.M := S.mem_M_iff.mpr hp.2
      have hvt : p.2 * t₀ = t₀ * p.2 := by
        have : S.z * (p.2 * t₀) = S.z * (t₀ * p.2) := by
          calc S.z * (p.2 * t₀) = p.2 * (S.z * t₀) := by rw [← mul_assoc, ← hp.2, mul_assoc]
            _ = S.z * t₀ * p.2 := hvw
            _ = S.z * (t₀ * p.2) := by group
        exact mul_left_cancel this
      have h1 := (T.th_mem_lineIn_iff hS ht₀M hxM).mp hxl
      have h2 := (T.isConj_w_iff_th ht₀ hS hvM).mp hp.1.2.1
      simp only [Finset.mem_filter, Finset.mem_product, List.mem_toFinset, List.mem_filter,
        commB_iff]
      rw [← htc]
      refine ⟨⟨h1, h2, (T.th_comm ht₀M hvM).mp hvt.symm⟩, ?_⟩
      have h72 := qts_nz.1 _ (mem_lineIn.mp h1).1 _ h2
      rw [← T.th_mul _ hxM _ hvM] at h72 ⊢
      rw [← T.th_z, ← T.th_mul _ (z_mem_M S) _ ht₀M]
      exact (T.mem_zpowers_iff_zpowL (S.M.mul_mem hxM hvM) (S.M.mul_mem (z_mem_M S) ht₀M)
        h72).mp hp.1.2.2
    · simp only [Finset.mem_filter, Finset.mem_product, List.mem_toFinset, List.mem_filter,
        commB_iff] at hq
      obtain ⟨⟨h1, h2, -⟩, h3⟩ := hq
      rw [← htc] at h1 h3
      have hxl := (T.th_mem_lineIn_iff hS ht₀M hx).mpr h1
      refine ⟨⟨hxl.1, (T.isConj_w_iff_th ht₀ hS hv).mpr h2, ?_⟩, S.mem_M_iff.mp hv⟩
      have h72 := qts_nz.1 _ (mem_lineIn.mp h1).1 _ h2
      rw [← T.th_mul _ hx _ hv] at h72 h3
      rw [← T.th_z, ← T.th_mul _ (z_mem_M S) _ ht₀M] at h3
      exact (T.mem_zpowers_iff_zpowL (S.M.mul_mem hx hv) (S.M.mul_mem (z_mem_M S) ht₀M)
        h72).mpr h3
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_product, List.mem_toFinset, List.mem_filter] at hq
      exact ⟨mem_dl_codes (mem_lineIn.mp hq.1.1).1, (mem_il.mp (mem_wl.mp hq.1.2.1).1).1⟩
  rw [thompsonCount, ← hP, hsplit, Set.ncard_union_eq hdisj, hPa, hPb, Set.ncard_prod,
    Set.ncard_pair hne.symm, T.ncard_swap hS ht₀]

end W

end Chart

end CFSG.LargeExtraspecial.AS35QTS

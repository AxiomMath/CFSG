module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3F11
public import CFSG.Certificates.Kernel.G2Three.Sec1T3F13
public import CFSG.Certificates.Kernel.G2Three.Sec1T3CSound

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup
  CFSG.Open
open CFSG.OddStandard.HigherRank.G2Three.Sec1Proof (sGen sGen_zero sGen_one sGen_two sGen_three
  sGen_four)
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {elt : ℕ → Γ} {P C V Q : ℕ}

theorem f14c_bIf_eq (c t e : Bool) : bIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

theorem f14c_recOr_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) false (fun t ih => bIf(f t, true, ih)) n = true ↔
      ∃ t < n, f t = true
  | 0 => by simp
  | n + 1 => by
    simp only [Nat.rec_add_one]
    rw [f14c_bIf_eq]
    split_ifs with hf
    · exact ⟨fun _ => ⟨n, by omega, hf⟩, fun _ => rfl⟩
    · rw [f14c_recOr_iff f n]
      constructor
      · rintro ⟨t, ht, h⟩
        exact ⟨t, by omega, h⟩
      · rintro ⟨t, ht, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · exact ⟨t, ht, h⟩
        · exact absurd h hf

section Tables

variable (hR : RealT elt P C V Q)
include hR

theorem f14c_cenS_mset (X : ℕ) : ∀ {gs : List ℕ}, (∀ g ∈ gs, g < 128) →
    mset elt (cenS P C X gs) = {x | x ∈ mset elt X ∧ ∀ g ∈ gs, x * elt g = elt g * x}
  | [], _ => by
    ext x
    simp only [List.not_mem_nil, false_imp_iff, imp_true_iff, and_true, Set.mem_setOf_eq]
    rfl
  | g :: gs, hgs => by
    change mset elt (cenE P C (cenS P C X gs) g) = _
    rw [cenE_mset hR _ (hgs g List.mem_cons_self),
      f14c_cenS_mset X (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))]
    ext x
    simp only [Set.mem_setOf_eq, List.forall_mem_cons]
    tauto

theorem f14c_cenR_mset (X g : ℕ) : ∀ n,
    mset elt (Nat.rec (motive := fun _ => ℕ) X (fun t acc => cenE P C acc (genAt g t)) n) =
      {x | x ∈ mset elt X ∧ ∀ t < n, x * elt (genAt g t) = elt (genAt g t) * x}
  | 0 => by
    ext x
    simp only [Set.mem_setOf_eq, Nat.not_lt_zero, false_imp_iff, imp_true_iff, and_true]
    rfl
  | n + 1 => by
    simp only [Nat.rec_add_one]
    rw [cenE_mset hR _ (genAt_lt _ _), f14c_cenR_mset X g n]
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun t ht => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact h2 t ht
      · exact h3
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun t ht => h2 t (by omega)⟩, h2 n (by omega)⟩

theorem f14c_upS_mset (X Zm : ℕ) {gs : List ℕ} (hgs : ∀ g ∈ gs, g < 128) :
    mset elt (upS P C V X Zm gs) =
      {x | x ∈ mset elt X ∧ ∀ g ∈ gs, ⁅x, elt g⁆ ∈ mset elt Zm} := by
  have e : upS P C V X Zm gs = Nat.rec (motive := fun _ => ℕ) 0 (fun i acc =>
      nIf(bAnd(hasB X i, List.rec (motive := fun _ => Bool) true
          (fun g _ ih => bAnd(hasB Zm (commE P C V i g), ih)) gs),
        Nat.lor acc (Nat.shiftLeft 1 i), acc)) 128 := by
    simp only [upS, strictN_eq]
  rw [e, mset_recMaskId]
  ext x
  constructor
  · rintro ⟨i, hi, hc, rfl⟩
    rw [bAnd_eq, Bool.and_eq_true, listRecAnd_iff] at hc
    refine ⟨⟨i, hi, hc.1, rfl⟩, fun g hg => ?_⟩
    rw [← commE_elt hR hi (hgs g hg), mem_mset_iff hR.inj (i := commE P C V i g) (atR_lt _ _)]
    exact hc.2 g hg
  · rintro ⟨⟨i, hi, hb, rfl⟩, hc⟩
    refine ⟨i, hi, ?_, rfl⟩
    rw [bAnd_eq, Bool.and_eq_true, listRecAnd_iff]
    refine ⟨hb, fun g hg => ?_⟩
    have := hc g hg
    rw [← commE_elt hR hi (hgs g hg),
      mem_mset_iff hR.inj (i := commE P C V i g) (atR_lt _ _)] at this
    exact this

theorem f14c_invertK_spec {h X : ℕ} (hh : h < 128) (hc : invertK P C V h X = true) :
    ∀ y ∈ mset elt X, elt h * y * (elt h)⁻¹ = y⁻¹ := by
  change strictB X (fun X => allBelow 128 2 fun y =>
    bIf(hasB X y, Nat.beq (conjR (rowT P h) (rowT C (atR V h)) y) (atR V y), true)) = true at hc
  rw [strictB_eq] at hc
  rintro _ ⟨i, hi, hb, rfl⟩
  have := allBelow_spec hc (by decide) i hi
  rw [hb] at this
  have e := congrArg elt (Nat.eq_of_beq_eq_true this)
  rwa [conjR_elt hR hh hi, hR.inv hi] at e

theorem f14c_cycK_of_isCyclic [Finite Γ] {X : ℕ} {T : Subgroup Γ} (hX : mset elt X = (T : Set Γ))
    (hc : IsCyclic T) (h2 : 2 ≤ Nat.card T) : cycK P X = true := by
  have hfin : Finite T := by
    refine Set.Finite.to_subtype (((Set.finite_Iio 128).image elt).subset ?_)
    rw [← hX]
    rintro _ ⟨i, hi, -, rfl⟩
    exact ⟨i, hi, rfl⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T)
  have ho : orderOf g = Nat.card T := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgX : (g : Γ) ∈ mset elt X := by rw [hX]; exact g.2
  obtain ⟨i, hi, hb, he⟩ := hgX
  have hcard : Nat.card T = pop X := f11_card hR hX
  unfold cycK
  rw [strictB_eq, strictB_eq, f14c_recOr_iff]
  refine ⟨i, hi, ?_⟩
  rw [bAnd_eq, hb, Bool.true_and, not'_eq, Bool.not_eq_true', Bool.eq_false_iff]
  intro hp
  have hp' := congrArg elt (Nat.eq_of_beq_eq_true hp)
  rw [powE_elt hR hi, hR.one, he] at hp'
  have e : Nat.shiftRight (pop X) 1 = Nat.card T / 2 := by
    rw [hcard]
    change pop X >>> 1 = _
    rw [Nat.shiftRight_eq_div_pow]
  rw [e] at hp'
  have hg1 : g ^ (Nat.card T / 2) = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hp')
  have hd := orderOf_dvd_of_pow_eq_one hg1
  rw [ho] at hd
  have := Nat.le_of_dvd (by omega) hd
  omega

theorem f14c_isCyclic_of_cycK [Finite Γ] {X : ℕ} {T : Subgroup Γ} (hX : mset elt X = (T : Set Γ))
    (h2 : IsPGroup 2 T) (hc : cycK P X = true) : IsCyclic T := by
  have hfin : Finite T := by
    refine Set.Finite.to_subtype (((Set.finite_Iio 128).image elt).subset ?_)
    rw [← hX]
    rintro _ ⟨i, hi, -, rfl⟩
    exact ⟨i, hi, rfl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card T = pop X := f11_card hR hX
  unfold cycK at hc
  rw [strictB_eq, strictB_eq, f14c_recOr_iff] at hc
  obtain ⟨i, hi, hc⟩ := hc
  rw [bAnd_eq, Bool.and_eq_true, not'_eq, Bool.not_eq_true', Bool.eq_false_iff] at hc
  obtain ⟨hb, hp⟩ := hc
  have hxT : elt i ∈ T := by
    rw [← SetLike.mem_coe, ← hX]
    exact ⟨i, hi, hb, rfl⟩
  have hne : (elt i) ^ (Nat.card T / 2) ≠ 1 := by
    intro h1
    apply hp
    rw [Nat.beq_eq]
    refine hR.inj _ (powE_lt _ _) _ (by decide) ?_
    rw [powE_elt hR hi, hR.one]
    have e : Nat.shiftRight (pop X) 1 = Nat.card T / 2 := by
      rw [hcard]
      change pop X >>> 1 = _
      rw [Nat.shiftRight_eq_div_pow]
    rw [e]
    exact h1
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
  set x : T := ⟨elt i, hxT⟩
  have hxo : orderOf x ∣ 2 ^ n := hn ▸ orderOf_dvd_natCard x
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hxo
  refine isCyclic_of_orderOf_eq_card x ?_
  rw [hn, hjo]
  by_contra hjn
  have hjlt : j < n := lt_of_le_of_ne hj (fun h => hjn (by rw [h]))
  apply hne
  have hdvd : orderOf x ∣ Nat.card T / 2 := by
    rw [hjo, hn]
    have e : 2 ^ n / 2 = 2 ^ (n - 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.add_sub_cancel]
    rw [e]
    exact pow_dvd_pow 2 (by omega)
  have := orderOf_dvd_iff_pow_eq_one.1 hdvd
  exact congrArg Subtype.val this

end Tables

abbrev F14cZ4 : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

@[expose] def f14c_z4Code (a : F14cZ4) : ℕ :=
  4 * (Multiplicative.toAdd a.1).val + (Multiplicative.toAdd a.2).val

theorem f14c_z4Code_lt : ∀ a, f14c_z4Code a < 16 := by decide

theorem f14c_z4Code_surj : ∀ t : Fin 16, ∃ a, f14c_z4Code a = t.val := by decide

theorem f14c_z4M_code : ∀ a b : F14cZ4, z4M (f14c_z4Code a) (f14c_z4Code b) = f14c_z4Code (a * b) := by
  decide

theorem f14c_z4K_spec {u v Jm : ℕ} (h : z4K P u v Jm = true) :
    (∀ c < 16, ∀ d < 16, z4I P u v (z4M c d) = mulE P (z4I P u v c) (z4I P u v d)) ∧
      Nat.rec (motive := fun _ => Nat) 0
        (fun c acc => Nat.lor acc (Nat.shiftLeft 1 (z4I P u v c))) 16 = Jm ∧ pop Jm = 16 := by
  unfold z4K at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun c hc d hd => ?_, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩
  have := allBelow_spec h1 (by decide) (16 * c + d) (by omega)
  have e1 : Nat.shiftRight (16 * c + d) 4 = c := by
    change (16 * c + d) >>> 4 = c
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have e2 : Nat.land (16 * c + d) 15 = d := by
    change (16 * c + d) &&& (2 ^ 4 - 1) = d
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  dsimp only at this
  rw [e1, e2] at this
  exact Nat.eq_of_beq_eq_true this

theorem f14c_z4K_sound (hR : RealT elt P C V Q) {u v Jm : ℕ} (hu : u < 128) (hv : v < 128)
    (h : z4K P u v Jm = true) :
    ∃ φ : F14cZ4 →* Γ, Function.Injective φ ∧ Set.range φ = mset elt Jm ∧
      φ (Multiplicative.ofAdd 2, 1) = elt u ^ 2 := by
  classical
  obtain ⟨hmul, himg, hpop⟩ := f14c_z4K_spec h
  have hlt : ∀ c, z4I P u v c < 128 := fun c => atR_lt _ _
  let φ : F14cZ4 →* Γ :=
    { toFun := fun a => elt (z4I P u v (f14c_z4Code a))
      map_one' := by
        have e : f14c_z4Code 1 = 0 := by decide
        change elt (z4I P u v (f14c_z4Code 1)) = 1
        rw [e]
        unfold z4I
        rw [mulE_elt hR (powE_lt _ _) (powE_lt _ _), powE_elt hR hu, powE_elt hR hv]
        simp
      map_mul' := fun a b => by
        change elt (z4I P u v (f14c_z4Code (a * b))) = elt (z4I P u v (f14c_z4Code a)) *
          elt (z4I P u v (f14c_z4Code b))
        rw [← f14c_z4M_code, hmul _ (f14c_z4Code_lt a) _ (f14c_z4Code_lt b),
          mulE_elt hR (hlt _) (hlt _)] }
  have hrange : Set.range φ = mset elt Jm := by
    rw [← himg]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨z4I P u v (f14c_z4Code a), hlt _, ?_, rfl⟩
      rw [hasB_eq]
      refine (recLor_bit (fun k => Nat.shiftLeft 1 (z4I P u v k)) _ 16).2
        ⟨f14c_z4Code a, f14c_z4Code_lt a, ?_⟩
      change (1 <<< z4I P u v (f14c_z4Code a)).testBit _ = true
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
    · rintro ⟨k, -, hk, rfl⟩
      rw [hasB_eq] at hk
      obtain ⟨t, ht, hb⟩ := (recLor_bit (fun k => Nat.shiftLeft 1 (z4I P u v k)) _ 16).1 hk
      change (1 <<< z4I P u v t).testBit k = true at hb
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at hb
      obtain ⟨a, ha⟩ := f14c_z4Code_surj ⟨t, ht⟩
      refine ⟨a, ?_⟩
      change elt (z4I P u v (f14c_z4Code a)) = _
      rw [ha]
      change elt (z4I P u v t) = _
      rw [hb]
  refine ⟨φ, ?_, hrange, ?_⟩
  · have hcard : (Set.range φ).ncard = 16 := by
      rw [hrange, pop_sound hR.inj (repM_mset hR.inj Jm), hpop]
    have hu16 : (Finset.univ : Finset F14cZ4).card = 16 := by decide
    have hfin : (Finset.univ.image φ).card = (Finset.univ : Finset F14cZ4).card := by
      rw [hu16, ← Set.ncard_coe_finset, Finset.coe_image, Finset.coe_univ, Set.image_univ, hcard]
    intro a b hab
    exact (Finset.card_image_iff.1 hfin) (Finset.mem_coe.2 (Finset.mem_univ a))
      (Finset.mem_coe.2 (Finset.mem_univ b)) hab
  · have e : f14c_z4Code (Multiplicative.ofAdd 2, 1) = 8 := by decide
    change elt (z4I P u v (f14c_z4Code (Multiplicative.ofAdd 2, 1))) = _
    rw [e]
    unfold z4I
    rw [mulE_elt hR (powE_lt _ _) (powE_lt _ _), powE_elt hR hu, powE_elt hR hv]
    have e2 : Nat.shiftRight 8 2 = 2 := rfl
    have e3 : Nat.land 8 3 = 0 := rfl
    rw [e2, e3, pow_zero, mul_one]

theorem f14c_centralizer_closure_singleton (x : Γ) :
    centralizer ((closure {x} : Subgroup Γ) : Set Γ) = centralizer {x} := by
  ext y
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h g hg
    exact h g (subset_closure hg)
  · intro h g hg
    have hle : closure {x} ≤ centralizer {y} := by
      rw [closure_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact (h z rfl).symm
    exact ((mem_centralizer_iff.1 (hle hg)) y rfl).symm

theorem f14c_cen_closure (s : Set Γ) :
    ((cen (closure s) : Subgroup Γ) : Set Γ) = {x | x ∈ closure s ∧ ∀ g ∈ s, x * g = g * x} := by
  ext x
  simp only [cen, coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_centralizer_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun g hg => (h g (subset_closure hg)).symm⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun g hg => ?_⟩
    have hle : closure s ≤ centralizer {x} := by
      rw [closure_le]
      intro z hz
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact h z hz
    exact ((mem_centralizer_iff.1 (hle hg)) x rfl).symm

theorem f14c_mem_center_iff (T : Subgroup Γ) (w : T) : w ∈ center T ↔ (w : Γ) ∈ cen T := by
  rw [mem_center_iff, cen, mem_inf, mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨w.2, fun g hg => congrArg Subtype.val (h ⟨g, hg⟩)⟩
  · rintro ⟨-, h⟩ g
    exact Subtype.ext (h g g.2)

theorem f14c_zSeries_two (T : Subgroup Γ) (s : Set Γ) (hs : closure s = T) :
    (zSeries 2 T : Set Γ) = {x | x ∈ T ∧ ∀ g ∈ s, ⁅x, g⁆ ∈ cen T} := by
  have hT : ∀ {y}, y ∈ closure s → y ∈ T := fun hy => by rw [← hs]; exact hy
  have central : ∀ c ∈ cen T, ∀ y ∈ T, y * c * y⁻¹ = c := by
    intro c hc y hy
    rw [(mem_centralizer_iff.1 (mem_inf.1 hc).2) y hy, mul_inv_cancel_right]
  have key : ∀ x : Γ, (∀ w ∈ T, ⁅x, w⁆ ∈ cen T) ↔ ∀ g ∈ s, ⁅x, g⁆ ∈ cen T := by
    intro x
    refine ⟨fun h g hg => h g (hT (subset_closure hg)), fun h w hw => ?_⟩
    rw [← hs] at hw
    induction hw using closure_induction with
    | mem g hg => exact h g hg
    | one =>
      rw [commutatorElement_one_right]
      exact (cen T).one_mem
    | mul y1 y2 hy1 hy2 ih1 ih2 =>
      have e : ⁅x, y1 * y2⁆ = ⁅x, y1⁆ * (y1 * ⁅x, y2⁆ * y1⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e, central _ ih2 y1 (hT hy1)]
      exact (cen T).mul_mem ih1 ih2
    | inv y hy ih =>
      have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e, central _ ((cen T).inv_mem ih) y⁻¹ (T.inv_mem (hT hy))]
      exact (cen T).inv_mem ih
  ext x
  simp only [zSeries, coe_map, coe_subtype, Set.mem_image, SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, (key y).1 fun w hw => ?_⟩
    have := (Subgroup.mem_upperCentralSeries_succ_iff.1 hy) ⟨w, hw⟩
    rw [Subgroup.upperCentralSeries_one, f14c_mem_center_iff] at this
    exact this
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro w
    rw [Subgroup.upperCentralSeries_one, f14c_mem_center_iff]
    exact (key x).2 h w w.2

theorem f14c_closure_invols (A : Set Γ) :
    closure {x | x ∈ A ∧ x ≠ 1 ∧ x * x = 1} = closure {y | y ∈ A ∧ y ^ 2 = 1} := by
  apply le_antisymm
  · apply Subgroup.closure_mono
    rintro x ⟨hx, -, h2⟩
    exact ⟨hx, by rw [pow_two]; exact h2⟩
  · rw [closure_le]
    rintro y ⟨hy, h2⟩
    by_cases h1 : y = 1
    · rw [h1]
      exact one_mem _
    · exact subset_closure ⟨hy, h1, by rw [← pow_two]; exact h2⟩

theorem f14c_setOf_two (u v : Γ) : {x | x ∈ [u, v]} = ({u, v} : Set Γ) := by
  ext x
  simp

theorem f14c_isMaximalIn_iff [Finite Γ] {fr : Frame Γ} (hS2 : IsPGroup 2 fr.S)
    (hS64 : Nat.card fr.S = 64) (M : Subgroup Γ) :
    IsMaximalIn fr.S M ↔ M ≤ fr.S ∧ Nat.card M = 32 := by
  unfold IsMaximalIn
  rw [isMaximal_iff_card hS2, hS64]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

section Thompson

variable [Finite Γ] (hR : RealT elt P C V Q)
include hR

theorem f14c_thompson_j0U {L RG N Xm : ℕ} {G₀ W : Subgroup Γ} (hL : LatOK elt L N G₀)
    (hN : N ≤ 448)
    (hgen : ∀ k < N, ∀ K : Subgroup Γ, RepM elt (entL L k) (K : Set Γ) →
      K = closure (rgSet elt RG k))
    (hWG : W ≤ G₀) (hW : mset elt Xm = (W : Set Γ)) :
    thompsonSubgroup W = closure (mset elt (j0U P C V L RG N Xm)) := by
  have hWr : RepM elt Xm (W : Set Γ) := by
    rw [← hW]
    exact repM_mset hR.inj Xm
  rw [j0U_sound hR hL hN hgen hWG hWr, thompsonSubgroup_eq_iSup]
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun hAW => iSup_le fun hAc => iSup_le fun hAm => ?_
    intro x hx
    exact subset_closure (Set.mem_biUnion (x := A) ⟨⟨hAW, hAc⟩, fun B hB => hAm B hB.1 hB.2⟩ hx)
  · rw [closure_le]
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨A, ⟨⟨hAW, hAc⟩, hAm⟩, hx⟩ := hx
    have hmem : A ≤ ⨆ (A : Subgroup Γ) (_ : A ≤ W) (_ : IsMulCommutative A)
        (_ : ∀ B : Subgroup Γ, B ≤ W → IsMulCommutative B → Nat.card B ≤ Nat.card A), A :=
      le_iSup_of_le A (le_iSup_of_le hAW (le_iSup_of_le hAc
        (le_iSup_of_le (fun B h1 h2 => hAm B ⟨h1, h2⟩) le_rfl)))
    exact hmem hx

end Thompson

theorem fact14_3_of_twin [Finite Γ] {fr : Frame Γ} {L RG OR N R : ℕ}
    (hR : RealT elt P C V Q) (hg : ∀ s < 5, elt (s + 1) = sGen fr s)
    (hSs2 : IsPGroup 2 fr.Sσ) (hS64 : Nat.card fr.S = 64) (hZS : cen fr.S = fr.Z)
    (hlat : (∀ k < N, ∃ K : Subgroup Γ, K ≤ fr.Sσ ∧ RepM elt (latM L k) (K : Set Γ)) ∧
      ∀ K ≤ fr.Sσ, ∃ k < N, RepM elt (latM L k) (K : Set Γ))
    (hN : N ≤ 448) (hord : ordK L OR 0 N = true) (hrg : rgK L RG N = true)
    (hrgA : ∀ k < N, ∃ lo w, lo ≤ k ∧ k < lo + w ∧ w ≤ 448 ∧ rgAllK L OR RG N lo w = true)
    (h : f14cK P C V Q L RG N 1 2 3 4 5 R = true) :
    cen fr.B = closure {fr.b₁ * fr.b₂, fr.z} ∧ cen fr.B = omega1 (zSeries 2 fr.S) ∧
    IsMaximalIn fr.S fr.B ∧ ¬ IsCyclic ↥(cen fr.B) ∧
    (∀ M : Subgroup Γ, IsMaximalIn fr.S M → ¬ IsCyclic ↥(cen M) → M = fr.B) ∧
    thompsonSubgroup fr.S = thompsonSubgroup fr.B ∧
    thompsonSubgroup fr.B = closure {fr.b₁, fr.a₁ * fr.a₂ * fr.h₀} ∧
    Nonempty (↥(closure {fr.b₁, fr.a₁ * fr.a₂ * fr.h₀} : Subgroup Γ) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
    cen fr.B = omega1 (thompsonSubgroup fr.B) ∧
    ∀ y ∈ thompsonSubgroup fr.B, fr.h₀ * y * fr.h₀⁻¹ = y⁻¹ := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := f11_e1 hg
  have hinj := hR.inj
  have hSSs : fr.S ≤ fr.Sσ := by
    change closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} : Set Γ) ≤
      closure {fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀, fr.σ}
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hS2 : IsPGroup 2 fr.S := hSs2.to_le hSSs
  have hL : LatOK elt L N fr.Sσ := hlat
  have hord' : ∀ k < N, pop (entL L k) = ordAt OR k := ordK_spec hord hN
  have hallR : ∀ k < N, ∀ h < N, 2 * ordAt OR h = ordAt OR k →
      subM (entL L h) (entL L k) = true → outB (entL L h) (rgAt RG k) = true := by
    intro k hk h hh ho hs
    obtain ⟨lo, w, h1, h2, hw, hA⟩ := hrgA k hk
    have := rgAllK_spec hA hN hw (k - lo) (by omega) h hh
    rw [Nat.add_sub_cancel' h1] at this
    exact this ho hs
  have hgen : ∀ k < N, ∀ K : Subgroup Γ, RepM elt (entL L k) (K : Set Γ) →
      K = closure (rgSet elt RG k) := fun k hk K hK =>
    (rg_closure hinj hL hSs2 hN hrg hord' hallR hk hK).2
  have hall : ∀ K ≤ fr.S, ∃ k < N, mset elt (latM L k) = (K : Set Γ) := fun K hK => by
    obtain ⟨k, hk, hr⟩ := hlat.2 K (le_trans hK hSSs)
    exact ⟨k, hk, hr.eq_mset.symm⟩
  have hz : elt (atR Q 2) = fr.z := by
    rw [hR.sq (i := 2) (by norm_num), e2]
    exact (pow_two _).symm
  have hb1b2 : elt (mulE P 2 4) = fr.b₁ * fr.b₂ := by
    rw [mulE_elt hR (x := 2) (y := 4) (by norm_num) (by norm_num), e2, e4]
  have ha1a2h0 : elt (mulE P (mulE P 1 3) 5) = fr.a₁ * fr.a₂ * fr.h₀ := by
    rw [mulE_elt hR (f13_mulE_lt _ _ _) (by norm_num), mulE_elt hR (x := 1) (y := 3) (by norm_num)
      (by norm_num), e1, e3, e5]
  have lt2 : ∀ {u v : ℕ}, u < 128 → v < 128 → ∀ g ∈ [u, v], g < 128 := by
    intro u v hu hv g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hu
    · exact hv
  have lt4 : ∀ g ∈ [mulE P 1 3, 2, 4, 5], g < 128 := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact atR_lt _ _
    all_goals norm_num
  have lt1 : ∀ g ∈ [atR Q 2], g < 128 := by
    intro g hg
    rw [List.mem_singleton] at hg
    rw [hg]
    exact atR_lt _ _
  have cl2 : ∀ {u v : ℕ}, closure {x | ∃ g ∈ [u, v], elt g = x} = closure {elt u, elt v} := by
    intro u v
    rw [f13_setOf_eq_map, List.map_cons, List.map_cons, List.map_nil, f14c_setOf_two]
  simp only [f14cK, bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  set S := closK C [1, 2, 3, 4, 5] R with hSdef
  set Zm := closK C [atR Q 2] R with hZmdef
  set Bm := cenE P C S (mulE P 2 4) with hBmdef
  set ZB := cenS P C Bm [mulE P 1 3, 2, 4, 5] with hZBdef
  set J := closK C [2, mulE P (mulE P 1 3) 5] R with hJdef
  set Z2 := upS P C V S Zm [1, 2, 3, 4, 5] with hZ2def
  obtain ⟨c1, c2, c3, c4, c5, eB, eZB, cm1, eZ2, pB, ncyc, hall32, j1, j2, hz4, cm2, eJ, hinv⟩ := h
  rw [not'_eq, Bool.not_eq_true'] at ncyc
  have hS : mset elt S = (fr.S : Set Γ) := f11_S hR hg c1
  have hs5 : closure {x | ∃ g ∈ [1, 2, 3, 4, 5], elt g = x} = fr.S := by
    rw [f11_gens5 hg]
    rfl
  have hZm : mset elt Zm = (fr.Z : Set Γ) := by
    rw [hZmdef, closK_closure hR lt1 c2, f13_setOf_eq_map, List.map_cons, List.map_nil,
      f13_setOf_one, hz, ← zpowers_eq_closure]
    rfl
  have hB : mset elt Bm = (fr.B : Set Γ) := by
    rw [hBmdef, f13_cenE hR hS (f13_mulE_lt _ _ _), hb1b2]
    change _ = ((fr.S ⊓ centralizer ((closure {fr.b₁ * fr.b₂} : Subgroup Γ) : Set Γ) :
      Subgroup Γ) : Set Γ)
    rw [f14c_centralizer_closure_singleton]
    rfl
  set sB : Set Γ := {x | ∃ g ∈ [mulE P 1 3, 2, 4, 5], elt g = x} with hsB
  have hBcl : closure sB = fr.B := by
    apply SetLike.coe_injective
    rw [← closK_closure hR lt4 c3, ← eB, hB]
  have hZB : mset elt ZB = (cen fr.B : Set Γ) := by
    rw [hZBdef, f14c_cenS_mset hR _ lt4, ← hBcl, f14c_cen_closure, hBcl]
    ext x
    have hm : x ∈ mset elt Bm ↔ x ∈ fr.B := by
      rw [hB]
      rfl
    simp only [Set.mem_setOf_eq, hm]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, by rintro _ ⟨g, hg, rfl⟩; exact h g hg⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun g hg => h _ ⟨g, hg, rfl⟩⟩
  have hZ2 : mset elt Z2 = (zSeries 2 fr.S : Set Γ) := by
    rw [hZ2def, f14c_upS_mset hR _ _ (by decide), f14c_zSeries_two fr.S _ hs5, hS, hZm, ← hZS]
    ext x
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, by rintro _ ⟨g, hg, rfl⟩; exact h g hg⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun g hg => h _ ⟨g, hg, rfl⟩⟩
  have hJcl : mset elt J = (closure {fr.b₁, fr.a₁ * fr.a₂ * fr.h₀} : Set Γ) := by
    rw [hJdef, closK_closure hR (lt2 (by norm_num) (f13_mulE_lt _ _ _)) c5, cl2, e2, ha1a2h0]
  have hJS : mset elt J = (thompsonSubgroup fr.S : Set Γ) := by
    rw [joinK_sound hR j1, ← f14c_thompson_j0U hR hL hN hgen hSSs hS]
  have hBS : fr.B ≤ fr.S := inf_le_left
  have hJB : mset elt J = (thompsonSubgroup fr.B : Set Γ) := by
    rw [joinK_sound hR j2, ← f14c_thompson_j0U hR hL hN hgen (le_trans hBS hSSs) hB]
  obtain ⟨φ, hφi, hφr, hφz⟩ := f14c_z4K_sound hR (by norm_num) (atR_lt _ _) hz4
  have hz1 : fr.z ≠ 1 := by
    intro h1
    have h2 : φ (Multiplicative.ofAdd 2, 1) = φ 1 := by
      rw [hφz, map_one, e2]
      exact h1
    exact absurd (hφi h2) (by decide)
  have hcenB : cen fr.B = closure {fr.b₁ * fr.b₂, fr.z} := by
    apply SetLike.coe_injective
    rw [← hZB, eZB, closK_closure hR (lt2 (f13_mulE_lt _ _ _) (atR_lt _ _)) c4, cl2, hb1b2, hz]
  have hcardB : Nat.card fr.B = 32 := by rw [f11_card hR hB, pB]
  refine ⟨hcenB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply SetLike.coe_injective
    rw [← hZB, eZ2, closM_closure hR cm1, involM_mset hR, hZ2, f14c_closure_invols]
    rfl
  · exact (f14c_isMaximalIn_iff hS2 hS64 fr.B).2 ⟨hBS, hcardB⟩
  · intro hc
    have hzB : fr.z ∈ cen fr.B := by
      rw [hcenB]
      exact subset_closure (by simp)
    have h2 : 2 ≤ Nat.card (cen fr.B) :=
      Finite.one_lt_card_iff_nontrivial.2 ⟨⟨⟨fr.z, hzB⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
    rw [f14c_cycK_of_isCyclic hR hZB hc h2] at ncyc
    exact absurd ncyc (by decide)
  · intro M hM hMc
    obtain ⟨hMS, hcM⟩ := (f14c_isMaximalIn_iff hS2 hS64 M).1 hM
    obtain ⟨k, hk, hkM⟩ := hall M hMS
    have hkR : RepM elt (entL L k) (M : Set Γ) := by
      rw [entL_eq, ← hkM]
      exact repM_mset hinj _
    have hMgen : M = closure (rgSet elt RG k) := hgen k hk M hkR
    have hcen : mset elt (cenR P C (entL L k) (rgAt RG k)) = (cen M : Set Γ) := by
      unfold cenR
      rw [f14c_cenR_mset hR, entL_eq, hkM, hMgen, f14c_cen_closure, ← hMgen]
      ext x
      simp only [Set.mem_setOf_eq, rgSet]
      constructor
      · rintro ⟨hx, h⟩
        exact ⟨hx, by rintro _ ⟨t, ht, rfl⟩; exact h t ht⟩
      · rintro ⟨hx, h⟩
        exact ⟨hx, fun t ht => h _ ⟨t, ht, rfl⟩⟩
    have hcyc : cycK P (cenR P C (entL L k) (rgAt RG k)) = false := by
      cases hc : cycK P (cenR P C (entL L k) (rgAt RG k))
      · rfl
      · exact absurd (f14c_isCyclic_of_cycK hR hcen (hS2.to_le (le_trans inf_le_left hMS)) hc)
          hMc
    have hsub : subM (entL L k) S = true := by
      rw [subM_iff_subset hinj (entL_lt _ _), entL_eq, hkM, hS]
      exact hMS
    have hpop : Nat.beq (pop (entL L k)) 32 = true := by
      rw [Nat.beq_eq, ← hcM, entL_eq, ← f11_card hR hkM]
    have := allBelow_spec hall32 (by omega) k hk
    rw [f14c_bIf_eq, if_pos (by rw [hsub, hpop, hcyc]; rfl)] at this
    apply SetLike.coe_injective
    rw [← hB, ← Nat.eq_of_beq_eq_true this, entL_eq, hkM]
  · apply SetLike.coe_injective
    rw [← hJS, hJB]
  · apply SetLike.coe_injective
    rw [← hJB, hJcl]
  · have hrng : φ.range = closure {fr.b₁, fr.a₁ * fr.a₂ * fr.h₀} :=
      SetLike.coe_injective (by rw [MonoidHom.coe_range, hφr, hJcl])
    exact ⟨((MonoidHom.ofInjective hφi).trans (MulEquiv.subgroupCongr hrng)).symm⟩
  · apply SetLike.coe_injective
    rw [← hZB, eJ, closM_closure hR cm2, involM_mset hR, hJB, f14c_closure_invols]
    rfl
  · intro y hy
    have := f14c_invertK_spec hR (h := 5) (by norm_num) hinv y (by rw [hJB]; exact hy)
    rwa [e5] at this

end CFSG.KC.G2Three.Sec1T3

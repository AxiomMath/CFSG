module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3F13
public import CFSG.Certificates.Kernel.G2Three.Sec1T3CSound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabOps4

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup
open CFSG.OddStandard.HigherRank.G2Three.Sec1Proof (sGen sGen_zero sGen_one sGen_two sGen_three
  sGen_four)
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {elt : ℕ → Γ} {P C V Q : ℕ}

theorem f14ab_comm_closure {T : Set Γ} {x : Γ} (h : ∀ s ∈ T, x * s = s * x) :
    ∀ y ∈ closure T, x * y = y * x := by
  have hle : closure T ≤ centralizer {x} := by
    rw [closure_le]
    intro s hs
    rw [SetLike.mem_coe, mem_centralizer_iff]
    rintro _ rfl
    exact h s hs
  intro y hy
  exact mem_centralizer_iff.1 (hle hy) x rfl

theorem f14ab_cen_closure (T : Set Γ) :
    (cen (closure T) : Set Γ) = {x | x ∈ closure T ∧ ∀ s ∈ T, x * s = s * x} := by
  ext x
  simp only [cen, coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_centralizer_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨hx, fun s hs => (hc s (subset_closure hs)).symm⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun y hy => (f14ab_comm_closure h y hy).symm⟩

theorem f14ab_central {K : Subgroup Γ} {c y : Γ} (hc : c ∈ cen K) (hy : y ∈ K) :
    y * c = c * y :=
  mem_centralizer_iff.1 (mem_inf.1 hc).2 y hy

theorem f14ab_zSeries_two {T : Set Γ} {K : Subgroup Γ} (hK : closure T = K) :
    (zSeries 2 K : Set Γ) = {x | x ∈ K ∧ ∀ s ∈ T, ⁅x, s⁆ ∈ cen K} := by
  have hz0 : zSeries 0 K = ⊥ := by
    rw [zSeries, Subgroup.upperCentralSeries_zero, Subgroup.map_bot]
  have hz1 : ∀ x, x ∈ zSeries 1 K ↔ x ∈ cen K := by
    intro x
    rw [CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab.mem_zSeries_succ 0, hz0, cen, mem_inf,
      mem_centralizer_iff]
    simp only [mem_bot, commutatorElement_eq_one_iff_mul_comm, SetLike.mem_coe]
    exact and_congr Iff.rfl ⟨fun h y hy => (h y hy).symm, fun h y hy => (h y hy).symm⟩
  ext x
  rw [SetLike.mem_coe, CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab.mem_zSeries_succ 1]
  simp only [hz1, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h s hs => h s (hK ▸ subset_closure hs), fun h y hy => ?_⟩
  rw [← hK] at hy
  refine closure_induction (p := fun y _ => ⁅x, y⁆ ∈ cen K) (fun s hs => h s hs) ?_ ?_ ?_ hy
  · rw [commutatorElement_one_right]
    exact one_mem _
  · intro y y' hy _ h1 h2
    have hc := f14ab_central h2 (hK ▸ hy)
    have e : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e, hc, mul_inv_cancel_right]
    exact mul_mem h1 h2
  · intro y hy h1
    have hc := f14ab_central (inv_mem h1) (hK ▸ hy)
    have e : ⁅x, y⁻¹⁆ = y⁻¹ * (⁅x, y⁆⁻¹ * y) := by
      simp only [commutatorElement_def]
      group
    rw [e, ← hc, inv_mul_cancel_left]
    exact inv_mem h1

theorem f14ab_comm_of_sq {Y : Type} [Group Y] (h : ∀ q : Y, q * q = 1) (a b : Y) :
    a * b = b * a := by
  have hi : ∀ q : Y, q⁻¹ = q := fun q => inv_eq_of_mul_eq_one_right (h q)
  calc a * b = (a * b)⁻¹ := (hi _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hi, hi]

theorem f14ab_iso_of_range {H : Type} [Group H] (φ : H →* Γ) (hφ : Function.Injective φ)
    {K : Subgroup Γ} (h : Set.range φ = (K : Set Γ)) : Nonempty (↥K ≃* H) :=
  ⟨((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr (SetLike.coe_injective
    (by rw [MonoidHom.coe_range]; exact h)))).symm⟩

theorem f14ab_forall_setOf {gs : List ℕ} {p : Γ → Prop} :
    (∀ s ∈ {x | ∃ g ∈ gs, elt g = x}, p s) ↔ ∀ g ∈ gs, p (elt g) :=
  ⟨fun h g hg => h _ ⟨g, hg, rfl⟩, fun h _ ⟨g, hg, he⟩ => he ▸ h g hg⟩

theorem f14ab_setOf_two (u v : Γ) : {x | x ∈ [u, v]} = ({u, v} : Set Γ) := by
  ext x
  simp

theorem f14ab_setOf_four (u v w s : Γ) : {x | x ∈ [u, v, w, s]} = ({u, v, w, s} : Set Γ) := by
  ext x
  simp

theorem f14ab_subM_spec {a b : ℕ} (h : subM a b = true) : mset elt a ⊆ mset elt b :=
  subset_of_land (Nat.eq_of_beq_eq_true h)

theorem f14ab_mset_land (hinj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j) (a b : ℕ) :
    mset elt (Nat.land a b) = mset elt a ∩ mset elt b := by
  ext g
  constructor
  · rintro ⟨i, hi, hb, rfl⟩
    rw [hasB_eq] at hb
    change (a &&& b).testBit i = true at hb
    rw [Nat.testBit_and, Bool.and_eq_true] at hb
    exact ⟨⟨i, hi, by rw [hasB_eq]; exact hb.1, rfl⟩, ⟨i, hi, by rw [hasB_eq]; exact hb.2, rfl⟩⟩
  · rintro ⟨⟨i, hi, h1, rfl⟩, ⟨j, hj, h2, he⟩⟩
    have hji := hinj j hj i hi he
    subst hji
    refine ⟨j, hj, ?_, rfl⟩
    rw [hasB_eq] at h1 h2 ⊢
    change (a &&& b).testBit j = true
    rw [Nat.testBit_and, h1, h2]
    rfl


@[expose] def f14ab_q8Code : QuaternionGroup 2 → ℕ
  | .a i => i.val
  | .xa i => 4 + i.val

theorem f14ab_q8Code_lt : ∀ a, f14ab_q8Code a < 8 := by decide

theorem f14ab_q8Code_surj : ∀ t : Fin 8, ∃ a, f14ab_q8Code a = t.val := by decide

theorem f14ab_q8M_code : ∀ a b : QuaternionGroup 2,
    q8M (f14ab_q8Code a) (f14ab_q8Code b) = f14ab_q8Code (a * b) := by
  decide

theorem f14ab_q8K_spec {r s Qm : ℕ} (h : q8K P r s Qm = true) :
    (∀ u < 8, ∀ v < 8, d8I P r s (q8M u v) = mulE P (d8I P r s u) (d8I P r s v)) ∧
      Nat.rec (motive := fun _ => Nat) 0
        (fun k acc => Nat.lor acc (Nat.shiftLeft 1 (d8I P r s k))) 8 = Qm ∧ pop Qm = 8 := by
  unfold q8K at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun u hu v hv => ?_, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩
  have := allBelow_spec h1 (by decide) (8 * u + v) (by omega)
  have e1 : Nat.shiftRight (8 * u + v) 3 = u := by
    change (8 * u + v) >>> 3 = u
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have e2 : Nat.land (8 * u + v) 7 = v := by
    change (8 * u + v) &&& (2 ^ 3 - 1) = v
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  dsimp only at this
  rw [e1, e2] at this
  exact Nat.eq_of_beq_eq_true this

section Tables

variable (hR : RealT elt P C V Q)
include hR

theorem f14ab_q8K_sound {r s Qm : ℕ} (h : q8K P r s Qm = true) :
    ∃ φ : QuaternionGroup 2 →* Γ, Function.Injective φ ∧ Set.range φ = mset elt Qm := by
  classical
  obtain ⟨hmul, himg, hpop⟩ := f14ab_q8K_spec h
  let φ : QuaternionGroup 2 →* Γ :=
    { toFun := fun a => elt (d8I P r s (f14ab_q8Code a))
      map_one' := by
        change elt (d8I P r s 0) = 1
        have e : d8I P r s 0 = 0 := rfl
        rw [e, hR.one]
      map_mul' := fun a b => by
        change elt (d8I P r s (f14ab_q8Code (a * b))) = elt (d8I P r s (f14ab_q8Code a)) *
          elt (d8I P r s (f14ab_q8Code b))
        rw [← f14ab_q8M_code, hmul _ (f14ab_q8Code_lt a) _ (f14ab_q8Code_lt b),
          mulE_elt hR (d8I_lt _ _ _) (d8I_lt _ _ _)] }
  have hrange : Set.range φ = mset elt Qm := by
    rw [← himg]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨d8I P r s (f14ab_q8Code a), d8I_lt _ _ _, ?_, rfl⟩
      rw [hasB_eq]
      refine (recLor_bit (fun k => Nat.shiftLeft 1 (d8I P r s k)) _ 8).2
        ⟨f14ab_q8Code a, f14ab_q8Code_lt a, ?_⟩
      change (1 <<< d8I P r s (f14ab_q8Code a)).testBit _ = true
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
    · rintro ⟨k, -, hk, rfl⟩
      rw [hasB_eq] at hk
      obtain ⟨t, ht, hb⟩ := (recLor_bit (fun k => Nat.shiftLeft 1 (d8I P r s k)) _ 8).1 hk
      change (1 <<< d8I P r s t).testBit k = true at hb
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at hb
      obtain ⟨a, ha⟩ := f14ab_q8Code_surj ⟨t, ht⟩
      refine ⟨a, ?_⟩
      change elt (d8I P r s (f14ab_q8Code a)) = _
      rw [ha]
      change elt (d8I P r s t) = _
      rw [hb]
  refine ⟨φ, ?_, hrange⟩
  have hcard : (Set.range φ).ncard = 8 := by
    rw [hrange, pop_sound hR.inj (repM_mset hR.inj Qm), hpop]
  have hfin : (Finset.univ.image φ).card = (Finset.univ : Finset (QuaternionGroup 2)).card := by
    rw [Finset.card_univ, QuaternionGroup.card, ← Set.ncard_coe_finset, Finset.coe_image,
      Finset.coe_univ, Set.image_univ, hcard]
  intro a b hab
  exact (Finset.card_image_iff.1 hfin) (Finset.mem_coe.2 (Finset.mem_univ a))
    (Finset.mem_coe.2 (Finset.mem_univ b)) hab

theorem f14ab_card {X : ℕ} {K : Subgroup Γ} (h : mset elt X = (K : Set Γ)) :
    Nat.card K = pop X := by
  rw [← pop_sound hR.inj (repM_mset hR.inj X), h]
  exact Nat.card_coe_set_eq _

theorem f14ab_mset_sq (X : ℕ) : mset elt (imgR Q X) = (fun x => x * x) '' mset elt X :=
  mset_imgR Q X _ fun _ hi => hR.sq hi

theorem f14ab_cenS_mset (X : ℕ) : ∀ {gs : List ℕ}, (∀ g ∈ gs, g < 128) →
    mset elt (cenS P C X gs) = {x | x ∈ mset elt X ∧ ∀ g ∈ gs, x * elt g = elt g * x}
  | [], _ => by
    change mset elt X = _
    ext x
    simp
  | g :: gs, hgs => by
    change mset elt (cenE P C (cenS P C X gs) g) = _
    rw [cenE_mset hR _ (hgs g List.mem_cons_self),
      f14ab_cenS_mset X (fun k hk => hgs k (List.mem_cons_of_mem _ hk))]
    ext x
    simp only [Set.mem_setOf_eq, List.forall_mem_cons]
    tauto

theorem f14ab_cenS_closure {gs : List ℕ} (hgs : ∀ g ∈ gs, g < 128) {R : ℕ}
    (hc : closOK C gs R = true) :
    mset elt (cenS P C (closK C gs R) gs) = (cen (closure {x | ∃ g ∈ gs, elt g = x}) : Set Γ) := by
  rw [f14ab_cenS_mset hR _ hgs, closK_closure hR hgs hc, f14ab_cen_closure]
  ext x
  exact and_congr Iff.rfl (f14ab_forall_setOf (elt := elt) (p := fun s => x * s = s * x)).symm

theorem f14ab_cenR_mset (X g : ℕ) : mset elt (cenR P C X g) =
    {x | x ∈ mset elt X ∧ ∀ t < Nat.land g 7, x * elt (genAt g t) = elt (genAt g t) * x} := by
  have key : ∀ n, mset elt (Nat.rec (motive := fun _ => ℕ) X
      (fun t acc => cenE P C acc (genAt g t)) n) =
      {x | x ∈ mset elt X ∧ ∀ t < n, x * elt (genAt g t) = elt (genAt g t) * x} := by
    intro n
    induction n with
    | zero =>
      change mset elt X = _
      ext x
      simp
    | succ n ih =>
      change mset elt (cenE P C (Nat.rec (motive := fun _ => ℕ) X
        (fun t acc => cenE P C acc (genAt g t)) n) (genAt g n)) = _
      rw [cenE_mset hR _ (genAt_lt g n), ih]
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨hx, h⟩, h'⟩
        refine ⟨hx, fun t ht => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · exact h t ht
        · exact h'
      · rintro ⟨hx, h⟩
        exact ⟨⟨hx, fun t ht => h t (Nat.lt_succ_of_lt ht)⟩, h n (Nat.lt_succ_self n)⟩
  exact key _

theorem f14ab_upS_mset (X Zm : ℕ) {gs : List ℕ} (hgs : ∀ g ∈ gs, g < 128) :
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
    rw [bAnd_eq, Bool.and_eq_true] at hc
    have hc2 := (listRecAnd_iff (fun g => hasB Zm (commE P C V i g)) gs).1 hc.2
    refine ⟨⟨i, hi, hc.1, rfl⟩, fun g hg => ?_⟩
    rw [← commE_elt hR hi (hgs g hg), mem_mset_iff hR.inj (commE_lt P C V i g)]
    exact hc2 g hg
  · rintro ⟨⟨i, hi, hb, rfl⟩, hc⟩
    refine ⟨i, hi, ?_, rfl⟩
    rw [bAnd_eq, Bool.and_eq_true]
    refine ⟨hb, (listRecAnd_iff (fun g => hasB Zm (commE P C V i g)) gs).2 fun g hg => ?_⟩
    have := hc g hg
    rwa [← commE_elt hR hi (hgs g hg), mem_mset_iff hR.inj (commE_lt P C V i g)] at this

theorem f14ab_commSetM_mset (X Y : ℕ) :
    mset elt (commSetM P C V X Y) = {g | ∃ a ∈ mset elt X, ∃ b ∈ mset elt Y, ⁅a, b⁆ = g} := by
  have e : commSetM P C V X Y = Nat.rec (motive := fun _ => ℕ) 0 (fun x acc => nIf(hasB X x,
      Nat.lor acc (Nat.rec (motive := fun _ => ℕ) 0 (fun y acc2 =>
        nIf(hasB Y y, Nat.lor acc2 (Nat.shiftLeft 1 (commE P C V x y)), acc2)) 128), acc)) 128 := by
    simp only [commSetM, strictN_eq]
  rw [e, mset_recLorIf]
  ext g
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨x, ⟨hx, hbx⟩, hg⟩
    rw [mset_recMask (hasB Y) (fun y => commE P C V x y) (fun _ _ => atR_lt _ _)] at hg
    obtain ⟨y, hy, hby, rfl⟩ := hg
    exact ⟨elt x, ⟨x, hx, hbx, rfl⟩, elt y, ⟨y, hy, hby, rfl⟩, (commE_elt hR hx hy).symm⟩
  · rintro ⟨_, ⟨x, hx, hbx, rfl⟩, _, ⟨y, hy, hby, rfl⟩, rfl⟩
    refine ⟨x, ⟨hx, hbx⟩, ?_⟩
    rw [mset_recMask (hasB Y) (fun y => commE P C V x y) (fun _ _ => atR_lt _ _)]
    exact ⟨y, hy, hby, commE_elt hR hx hy⟩

theorem f14ab_closM_comm {X R : ℕ} {K : Subgroup Γ} (hX : mset elt X = (K : Set Γ))
    (hc : closMOK C (commSetM P C V X X) R = true) :
    mset elt (closM C (commSetM P C V X X) R) = ((⁅K, K⁆ : Subgroup Γ) : Set Γ) := by
  rw [closM_closure hR hc, f14ab_commSetM_mset hR, hX, Subgroup.commutator_def]
  rfl

theorem f14ab_conjM_mset {s : ℕ} (hs : s < 128) (X : ℕ) :
    mset elt (conjM P C V s X) = {g | ∃ x ∈ mset elt X, elt s * x * (elt s)⁻¹ = g} := by
  have e : conjM P C V s X = Nat.rec (motive := fun _ => ℕ) 0 (fun i acc =>
      nIf(hasB X i, Nat.lor acc (Nat.shiftLeft 1 (conjR (rowT P s) (rowT C (atR V s)) i)), acc))
      128 := by
    simp only [conjM, strictN_eq]
  rw [e, mset_recMask (hasB X) (fun i => conjR (rowT P s) (rowT C (atR V s)) i)
    fun _ _ => atR_lt _ _]
  ext g
  constructor
  · rintro ⟨i, hi, hb, rfl⟩
    exact ⟨elt i, ⟨i, hi, hb, rfl⟩, (conjR_elt hR hs hi).symm⟩
  · rintro ⟨_, ⟨i, hi, hb, rfl⟩, rfl⟩
    exact ⟨i, hi, hb, conjR_elt hR hs hi⟩

theorem f14ab_normM_spec {X N : ℕ} (h : normM P C V X N = true) :
    ∀ x ∈ mset elt X, ∀ y ∈ mset elt N, x * y * x⁻¹ ∈ mset elt N := by
  change strictB X (fun X => strictB N fun N =>
    allBelow 128 2 fun x => bIf(hasB X x, Nat.beq (conjM P C V x N) N, true)) = true at h
  rw [strictB_eq, strictB_eq] at h
  rintro _ ⟨i, hi, hb, rfl⟩ y hy
  have hbeq : Nat.beq (conjM P C V i N) N = true := by
    have h' := allBelow_spec h (by decide) i hi
    rw [hb] at h'
    exact h'
  rw [← Nat.eq_of_beq_eq_true hbeq, f14ab_conjM_mset hR hi]
  exact ⟨y, hy, rfl⟩

theorem f14ab_secProp_isE [Finite Γ] {X N f k : ℕ} {T W : Subgroup Γ} (hX : mset elt X = (T : Set Γ))
    (hN : mset elt N = (W : Set Γ)) (h : secEK P C V Q X N f = true) (hf : f = 2 ^ k) :
    SecProp T W (fun Y _ _ _ => IsE k Y) := by
  simp only [secEK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hWT : W ≤ T := by
    intro w hw
    have hw' : w ∈ mset elt N := by rw [hN]; exact hw
    have := f14ab_subM_spec h1 hw'
    rw [hX] at this
    exact this
  have hnorm : (W.subgroupOf T).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have hg : (g : Γ) ∈ mset elt X := by rw [hX]; exact g.2
    have hn' : (n : Γ) ∈ mset elt N := by rw [hN]; exact hn
    have := f14ab_normM_spec hR h2 _ hg _ hn'
    rw [hN] at this
    simpa using this
  refine ⟨hnorm, ?_⟩
  have hsq : ∀ q : ↥T ⧸ W.subgroupOf T, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H v =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
      have hv : (v : Γ) ∈ mset elt X := by rw [hX]; exact v.2
      have hvv : (v : Γ) * v ∈ mset elt N :=
        f14ab_subM_spec h3 (by rw [f14ab_mset_sq hR]; exact ⟨_, hv, rfl⟩)
      rw [hN] at hvv
      simpa using hvv
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (f14ab_comm_of_sq hsq a.1 b.1)⟩⟩, fun x _ => ?_⟩, ?_⟩
  · rw [pow_two]
    exact hsq x
  · have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (W.subgroupOf T)
    have e2 : Nat.card ↥(W.subgroupOf T) = Nat.card W :=
      Nat.card_congr (subgroupOfEquivOfLe hWT).toEquiv
    have hpos : 0 < pop N := by
      rw [← f14ab_card hR hN]
      exact Nat.card_pos
    rw [f14ab_card hR hX, e2, f14ab_card hR hN, h4, hf] at e1
    exact (Nat.eq_of_mul_eq_mul_right hpos e1).symm

end Tables

variable [Finite Γ] {fr : Frame Γ}

theorem f14ab_gens (hg : ∀ s < 5, elt (s + 1) = sGen fr s) :
    elt 1 = fr.a₁ ∧ elt 2 = fr.b₁ ∧ elt 3 = fr.a₂ ∧ elt 4 = fr.b₂ ∧ elt 5 = fr.h₀ := by
  have h0 := hg 0 (by norm_num)
  have h1 := hg 1 (by norm_num)
  have h2 := hg 2 (by norm_num)
  have h3 := hg 3 (by norm_num)
  have h4 := hg 4 (by norm_num)
  rw [sGen_zero] at h0
  rw [sGen_one] at h1
  rw [sGen_two] at h2
  rw [sGen_three] at h3
  rw [sGen_four] at h4
  exact ⟨h0, h1, h2, h3, h4⟩

theorem f14ab_one_lt {g : ℕ} (hg : g < 128) : ∀ x ∈ [g], x < 128 := by
  intro x hx
  rw [List.mem_singleton] at hx
  rw [hx]
  exact hg

theorem f14ab_masks (hR : RealT elt P C V Q) (hg : ∀ s < 5, elt (s + 1) = sGen fr s) {R : ℕ}
    (c5 : closOK C [1, 2, 3, 4, 5] R = true) (cz : closOK C [atR Q 2] R = true) :
    closure {x | ∃ g ∈ [1, 2, 3, 4, 5], elt g = x} = fr.S ∧
      mset elt (closK C [1, 2, 3, 4, 5] R) = (fr.S : Set Γ) ∧
      mset elt (closK C [atR Q 2] R) = (fr.Z : Set Γ) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := f14ab_gens hg
  have hT : closure {x | ∃ g ∈ [1, 2, 3, 4, 5], elt g = x} = fr.S := by
    rw [f13_setOf_eq_map]
    simp only [List.map_cons, List.map_nil, e1, e2, e3, e4, e5]
    rw [f13_setOf_five]
    rfl
  refine ⟨hT, ?_, ?_⟩
  · rw [closK_closure hR (by decide) c5, hT]
  · have ez : elt (atR Q 2) = fr.z := by
      rw [hR.sq (i := 2) (by norm_num), e2]
      exact (pow_two _).symm
    have hZ : fr.Z = closure {fr.z} := zpowers_eq_closure fr.z
    rw [closK_closure hR (f14ab_one_lt (atR_lt _ _)) cz, f13_setOf_eq_map]
    simp only [List.map_cons, List.map_nil, ez]
    rw [f13_setOf_one, hZ]

theorem f14ab_pair (hR : RealT elt P C V Q) {i j R : ℕ} (hi : i < 128) (hj : j < 128)
    (hc : closOK C [i, j] R = true) :
    mset elt (closK C [i, j] R) = (closure {elt i, elt j} : Set Γ) := by
  have hl : ∀ g ∈ [i, j], g < 128 := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    exacts [hi, hj]
  rw [closK_closure hR hl hc, f13_setOf_eq_map]
  simp only [List.map_cons, List.map_nil]
  rw [f14ab_setOf_two]

theorem f14ab_one (hR : RealT elt P C V Q) (hg : ∀ s < 5, elt (s + 1) = sGen fr s) {R : ℕ}
    (h : f14aK P C V Q 1 2 3 4 5 R = true) :
    cen fr.S = fr.Z ∧ zSeries 2 fr.S = ⁅fr.S, fr.S⁆ ∧ ⁅fr.S, fr.S⁆ = closure {fr.b₁, fr.b₂} ∧
      SecProp fr.S (zSeries 2 fr.S) (fun Y _ _ _ => IsE 3 Y) := by
  obtain ⟨-, e2, -, e4, -⟩ := f14ab_gens hg
  simp only [f14aK, bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨c5, cz, cb, hcen, hcm, hcl, hZ2b, hsec⟩ := h
  obtain ⟨hT, hS, hZ⟩ := f14ab_masks hR hg c5 cz
  have hl5 : ∀ g ∈ [1, 2, 3, 4, 5], g < 128 := by decide
  have hcenS := f14ab_cenS_closure hR hl5 c5
  rw [hT] at hcenS
  have h1 : cen fr.S = fr.Z := by
    apply SetLike.coe_injective
    rw [← hcenS, hcen, hZ]
  have hZ2 : mset elt (upS P C V (closK C [1, 2, 3, 4, 5] R) (closK C [atR Q 2] R)
      [1, 2, 3, 4, 5]) = (zSeries 2 fr.S : Set Γ) := by
    rw [f14ab_upS_mset hR _ _ hl5, hS, hZ, ← h1, f14ab_zSeries_two hT]
    ext x
    exact and_congr Iff.rfl
      (f14ab_forall_setOf (elt := elt) (p := fun s => ⁅x, s⁆ ∈ cen fr.S)).symm
  have hcomm := f14ab_closM_comm hR hS hcm
  have hB := f14ab_pair hR (i := 2) (j := 4) (by norm_num) (by norm_num) cb
  rw [e2, e4] at hB
  refine ⟨h1, ?_, ?_, f14ab_secProp_isE hR hS hZ2 hsec (by norm_num)⟩
  · apply SetLike.coe_injective
    rw [← hZ2, ← hcl, hcomm]
  · apply SetLike.coe_injective
    rw [← hcomm, hcl, hZ2b, hB]

theorem f14ab_two (hR : RealT elt P C V Q) (hg : ∀ s < 5, elt (s + 1) = sGen fr s)
    {L RG N R : ℕ} (hN : N ≤ 448)
    (hlat : ∀ K ≤ fr.S, ∃ k < N, RepM elt (latM L k) (K : Set Γ))
    (hgen : ∀ k < N, ∀ K : Subgroup Γ, RepM elt (entL L k) (K : Set Γ) →
      K = closure (rgSet elt RG k))
    (h : f14bK P C V Q L RG N 1 2 3 4 5 R = true) :
    Nonempty (↥(closure {fr.a₁, fr.b₁} : Subgroup Γ) ≃* QuaternionGroup 2) ∧
    Nonempty (↥(closure {fr.a₂, fr.b₂} : Subgroup Γ) ≃* QuaternionGroup 2) ∧
    (∀ u ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ), ∀ v ∈ (closure {fr.a₂, fr.b₂} : Subgroup Γ),
      u * v = v * u) ∧
    closure {fr.a₁, fr.b₁} ⊔ closure {fr.a₂, fr.b₂} = fr.A ∧
    closure {fr.a₁, fr.b₁} ⊓ closure {fr.a₂, fr.b₂} = fr.Z ∧
    IsExtraspecialTwo 2 fr.A ∧ (∀ X : Subgroup Γ, X ≤ fr.S → IsExtraspecialTwo 2 X → X = fr.A) := by
  obtain ⟨e1, e2, e3, e4, -⟩ := f14ab_gens hg
  simp only [f14bK, bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨c12, c34, c4, c5, cz, q1, q2, hcen2, -, hland, hpopA, hZA, hpopZA, hsqA, hcmA, hclA,
    hall⟩ := h
  obtain ⟨-, hS, hZ⟩ := f14ab_masks hR hg c5 cz
  have hA1 := f14ab_pair hR (i := 1) (j := 2) (by norm_num) (by norm_num) c12
  have hA2 := f14ab_pair hR (i := 3) (j := 4) (by norm_num) (by norm_num) c34
  rw [e1, e2] at hA1
  rw [e3, e4] at hA2
  have hl4 : ∀ g ∈ [1, 2, 3, 4], g < 128 := by decide
  have hT4 : closure {x | ∃ g ∈ [1, 2, 3, 4], elt g = x} = fr.A := by
    rw [f13_setOf_eq_map]
    simp only [List.map_cons, List.map_nil, e1, e2, e3, e4]
    rw [f14ab_setOf_four]
    rfl
  have hA : mset elt (closK C [1, 2, 3, 4] R) = (fr.A : Set Γ) := by
    rw [closK_closure hR hl4 c4, hT4]
  have hcenA := f14ab_cenS_closure hR hl4 c4
  rw [hT4] at hcenA
  have hcommA := f14ab_closM_comm hR hA hcmA
  have iso : ∀ {i j : ℕ} {Qm : ℕ} {K : Subgroup Γ}, mset elt Qm = (K : Set Γ) →
      q8K P i j Qm = true → Nonempty (↥K ≃* QuaternionGroup 2) := by
    intro i j Qm K hK hq
    obtain ⟨φ, hφ, hr⟩ := f14ab_q8K_sound hR hq
    exact f14ab_iso_of_range φ hφ (hr.trans hK)
  refine ⟨iso hA1 q1, iso hA2 q2, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv
    have hv' : v ∈ mset elt (cenS P C (closK C [3, 4] R) [1, 2]) := by
      rw [hcen2, hA2]
      exact hv
    rw [f14ab_cenS_mset hR _ (by decide)] at hv'
    have hc : ∀ s ∈ ({fr.a₁, fr.b₁} : Set Γ), v * s = s * v := by
      rintro s (rfl | rfl)
      · rw [← e1]
        exact hv'.2 1 (by decide)
      · rw [← e2]
        exact hv'.2 2 (by decide)
    exact (f14ab_comm_closure hc u hu).symm
  · rw [← Subgroup.closure_union]
    change _ = closure {fr.a₁, fr.b₁, fr.a₂, fr.b₂}
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · apply SetLike.coe_injective
    rw [coe_inf, ← hA1, ← hA2, ← f14ab_mset_land hR.inj, hland, hZ]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [f14ab_card hR hA, hpopA]
      norm_num
    · rw [f14ab_card hR hcenA, hpopZA]
    · apply SetLike.coe_injective
      rw [← hcommA, hclA, hcenA]
    · intro y hy
      have hy' : y ∈ mset elt (closK C [1, 2, 3, 4] R) := by rw [hA]; exact hy
      have hm := f14ab_subM_spec hsqA (by rw [f14ab_mset_sq hR]; exact ⟨y, hy', rfl⟩)
      rw [hcenA] at hm
      rw [pow_two]
      exact hm
  · intro X hXS hXe
    obtain ⟨hc32, hc2, -, hsqX⟩ := hXe
    obtain ⟨k, hk, hK⟩ := hlat X hXS
    have eK : mset elt (entL L k) = (X : Set Γ) := hK.eq_mset.symm
    have hf := allBelow_spec hall (by omega) k hk
    have k1 : subM (entL L k) (closK C [1, 2, 3, 4, 5] R) = true := by
      refine (subM_iff_subset hR.inj (entL_lt L k)).2 ?_
      rw [eK, hS]
      exact hXS
    have k2 : Nat.beq (pop (entL L k)) 32 = true := by
      rw [Nat.beq_eq, ← f14ab_card hR eK, hc32]
      norm_num
    have hZK : mset elt (cenR P C (entL L k) (rgAt RG k)) = (cen X : Set Γ) := by
      rw [f14ab_cenR_mset hR, eK, hgen k hk X hK, f14ab_cen_closure]
      ext x
      exact and_congr Iff.rfl
        ⟨fun h s ⟨t, ht, he⟩ => he ▸ h t ht, fun h t ht => h _ ⟨t, ht, rfl⟩⟩
    have k3 : Nat.beq (pop (cenR P C (entL L k) (rgAt RG k))) 2 = true := by
      rw [Nat.beq_eq, ← f14ab_card hR hZK, hc2]
    have k4 : subM (imgR Q (entL L k)) (cenR P C (entL L k) (rgAt RG k)) = true := by
      refine (subM_iff_subset hR.inj (imgR_lt _ _)).2 ?_
      rw [f14ab_mset_sq hR, eK, hZK]
      rintro _ ⟨y, hy, rfl⟩
      have := hsqX y hy
      rwa [pow_two] at this
    rw [k1, k2, k3, k4] at hf
    have hKA : entL L k = closK C [1, 2, 3, 4] R := Nat.eq_of_beq_eq_true hf
    apply SetLike.coe_injective
    rw [← eK, hKA, hA]

theorem fact14_12_of_twin {fr : Frame Γ} {elt : ℕ → Γ} {P C V Q L RG N R : ℕ}
    (hR : RealT elt P C V Q)
    (hg : ∀ s < 5, elt (s + 1) = sGen fr s)
    (hN : N ≤ 448)
    (hlat : (∀ k < N, ∃ K : Subgroup Γ, K ≤ fr.Sσ ∧ RepM elt (latM L k) (K : Set Γ)) ∧
      ∀ K ≤ fr.Sσ, ∃ k < N, RepM elt (latM L k) (K : Set Γ))
    (hgen : ∀ k < N, ∀ K : Subgroup Γ, RepM elt (entL L k) (K : Set Γ) →
      K = closure (rgSet elt RG k))
    (ha : f14aK P C V Q 1 2 3 4 5 R = true)
    (hb : f14bK P C V Q L RG N 1 2 3 4 5 R = true) :
    (cen fr.S = fr.Z ∧ zSeries 2 fr.S = ⁅fr.S, fr.S⁆ ∧ ⁅fr.S, fr.S⁆ = closure {fr.b₁, fr.b₂} ∧
      SecProp fr.S (zSeries 2 fr.S) (fun Y _ _ _ => IsE 3 Y)) ∧
    (Nonempty (↥(closure {fr.a₁, fr.b₁} : Subgroup Γ) ≃* QuaternionGroup 2) ∧
      Nonempty (↥(closure {fr.a₂, fr.b₂} : Subgroup Γ) ≃* QuaternionGroup 2) ∧
      (∀ u ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ), ∀ v ∈ (closure {fr.a₂, fr.b₂} : Subgroup Γ),
        u * v = v * u) ∧
      closure {fr.a₁, fr.b₁} ⊔ closure {fr.a₂, fr.b₂} = fr.A ∧
      closure {fr.a₁, fr.b₁} ⊓ closure {fr.a₂, fr.b₂} = fr.Z ∧
      IsExtraspecialTwo 2 fr.A ∧
      (∀ X : Subgroup Γ, X ≤ fr.S → IsExtraspecialTwo 2 X → X = fr.A)) :=
  have hSS : fr.S ≤ fr.Sσ := closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)
  ⟨f14ab_one hR hg ha, f14ab_two hR hg hN (fun K hK => hlat.2 K (hK.trans hSS)) hgen hb⟩

end CFSG.KC.G2Three.Sec1T3

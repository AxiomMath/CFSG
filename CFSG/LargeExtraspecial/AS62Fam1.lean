module

public import CFSG.LargeExtraspecial.AS35EFiveOne
public import CFSG.LargeExtraspecial.AS62Eu
public import CFSG.LargeExtraspecial.AS35DSixFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Asc77 CFSG.RankThree.OrthogonalInvolutions
open scoped IsMulCommutative

namespace AS62

variable {G : Type} [Group G] (S : Setting G)

theorem mul_self_of_mem_zConj {H : Subgroup G} {x : G} (hx : x ∈ S.zConj H) : x * x = 1 := by
  obtain ⟨k, -, rfl⟩ := hx
  rw [show k * S.z * k⁻¹ * (k * S.z * k⁻¹) = k * (S.z * S.z) * k⁻¹ by group, S.z_mul_z]
  group

theorem inv_eq_of_mem_zConj {H : Subgroup G} {x : G} (hx : x ∈ S.zConj H) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (mul_self_of_mem_zConj S hx)

theorem commute_of_mem_zConj {H : Subgroup G} (hA : S.IsAFive H) {a b : G}
    (ha : a ∈ S.zConj H) (hb : b ∈ S.zConj H) : a * b = b * a := by
  obtain ⟨_, _, -, hcomm, -⟩ := hA.1
  exact hcomm a ha b hb

theorem mul_five_eq_one {H : Subgroup G} (hA : S.IsAFive H) {a b c d e : G}
    (hmem : ∀ x, x ∈ S.zConj H ↔ x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : a * b * c * d * e = 1 := by
  classical
  have hC := hA.2
  obtain ⟨_, _, -, hcomm, -⟩ := hA.1
  set Ω := S.zConj H with hΩ
  set V := closure Ω with hV
  have : IsMulCommutative V := isMulCommutative_closure fun x hx y hy _ => hcomm x hx y hy
  set s : Finset G := {a, b, c, d, e} with hs
  have hsΩ : ∀ x, x ∈ s ↔ x ∈ Ω := fun x => by
    rw [hmem x]
    simp [hs]
  let g : G → V := fun x => if hx : x ∈ V then ⟨x, hx⟩ else 1
  have hg : ∀ x (hx : x ∈ V), g x = ⟨x, hx⟩ := fun x hx => by simp only [g, hx, ↓reduceDIte]
  set w : V := ∏ x ∈ s, g x with hw
  have hwH : ∀ k ∈ H, k * (w : G) * k⁻¹ = w := by
    intro k hk
    let φ : V →* V :=
      { toFun := fun v => ⟨k * v * k⁻¹, conj_mem_closure_conjIn hk v.2⟩
        map_one' := Subtype.ext (by
          change k * 1 * k⁻¹ = 1
          group)
        map_mul' := fun x y => Subtype.ext (by
          change k * ((x : G) * y) * k⁻¹ = k * x * k⁻¹ * (k * y * k⁻¹)
          group) }
    have h1 : φ w = ∏ x ∈ s, φ (g x) := map_prod φ _ _
    have h2 : ∏ x ∈ s, φ (g x) = ∏ x ∈ s, g x := by
      refine Finset.prod_nbij (fun x => k * x * k⁻¹) ?_ ?_ ?_ ?_
      · intro x hx
        rw [hsΩ] at hx ⊢
        exact conj_mem_conjIn_of_mem hk hx
      · intro x _ y _ hxy
        exact Setting.conj_injective k hxy
      · intro y hy
        refine ⟨k⁻¹ * y * k, ?_, by group⟩
        rw [Finset.mem_coe, hsΩ] at hy ⊢
        have := conj_mem_conjIn_of_mem (H.inv_mem hk) hy
        rwa [inv_inv] at this
      · intro x hx
        have hxV : x ∈ V := subset_closure ((hsΩ x).mp hx)
        rw [hg x hxV, hg _ (conj_mem_closure_conjIn hk hxV)]
        rfl
    exact congrArg Subtype.val (h1.trans h2)
  have hw1 : (w : G) = 1 := by
    have hwC : (w : G) ∈ Asc77.centerIn S.z H := by
      refine mem_inf.mpr ⟨w.2, mem_centralizer_iff.mpr fun k hk => ?_⟩
      calc k * (w : G) = k * w * k⁻¹ * k := by group
        _ = w * k := by rw [hwH k hk]
    rw [hC] at hwC
    exact hwC
  have hmemV : ∀ x, x ∈ s → x ∈ V := fun x hx => subset_closure ((hsΩ x).mp hx)
  have hval : (w : G) = a * (b * (c * (d * e))) := by
    rw [hw, Finset.prod_insert (by simp [hab, hac, had, hae]),
      Finset.prod_insert (by simp [hbc, hbd, hbe]), Finset.prod_insert (by simp [hcd, hce]),
      Finset.prod_pair hde, hg a (hmemV a (by simp [hs])), hg b (hmemV b (by simp [hs])),
      hg c (hmemV c (by simp [hs])), hg d (hmemV d (by simp [hs])),
      hg e (hmemV e (by simp [hs]))]
    rfl
  rw [show a * b * c * d * e = a * (b * (c * (d * e))) by simp only [mul_assoc], ← hval, hw1]

theorem exists_mul_eq_of_three {H : Subgroup G} (hA : S.IsAFive H) {a b c : G}
    (ha : a ∈ S.zConj H) (hb : b ∈ S.zConj H) (hc : c ∈ S.zConj H) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    ∃ d ∈ S.zConj H, ∃ e ∈ S.zConj H, d ≠ e ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ e ≠ a ∧ e ≠ b ∧
      e ≠ c ∧ a * b * c = d * e := by
  obtain ⟨_, _, h5, -⟩ := hA.1
  set Ω := S.zConj H with hΩ
  have hsub : ({a, b, c} : Set G) ⊆ Ω := by
    rintro x (rfl | rfl | rfl)
    · exact ha
    · exact hb
    · exact hc
  have h3 : ({a, b, c} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]
  have hdiff : (Ω \ {a, b, c}).ncard = 2 := by rw [Set.ncard_sdiff hsub, h5, h3]
  obtain ⟨d, e, hde, hdeq⟩ := Set.ncard_eq_two.mp hdiff
  have hd : d ∈ Ω \ {a, b, c} := by rw [hdeq]; exact Or.inl rfl
  have he : e ∈ Ω \ {a, b, c} := by rw [hdeq]; exact Or.inr rfl
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hd he
  obtain ⟨hdΩ, hda, hdb, hdc⟩ := hd
  obtain ⟨heΩ, hea, heb, hec⟩ := he
  have hmem : ∀ x, x ∈ Ω ↔ x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
    intro x
    constructor
    · intro hx
      by_cases hx3 : x ∈ ({a, b, c} : Set G)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx3
        tauto
      · have h' : x ∈ Ω \ {a, b, c} := ⟨hx, hx3⟩
        rw [hdeq] at h'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h'
        tauto
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ha
      · exact hb
      · exact hc
      · exact hdΩ
      · exact heΩ
  have h1 := mul_five_eq_one S hA hmem hab hac (Ne.symm hda) (Ne.symm hea) hbc (Ne.symm hdb)
    (Ne.symm heb) (Ne.symm hdc) (Ne.symm hec) hde
  refine ⟨d, hdΩ, e, heΩ, hde, hda, hdb, hdc, hea, heb, hec, ?_⟩
  calc a * b * c = a * b * c * d * e * (e⁻¹ * d⁻¹) := by group
    _ = e * d := by rw [h1, one_mul, inv_eq_of_mem_zConj S heΩ, inv_eq_of_mem_zConj S hdΩ]
    _ = d * e := commute_of_mem_zConj S hA heΩ hdΩ

theorem mem_Gamma_mul {H : Subgroup G} (hA : S.IsAFive H) {a v w : G} (ha : a ∈ S.zConj H)
    (hv : v ∈ S.zConj H) (hw : w ∈ S.zConj H) (haz : a ≠ S.z) (hvz : v ≠ S.z) (hwz : w ≠ S.z)
    (hav : a ≠ v) (haw : a ≠ w) (hvw : v ≠ w) : a ∈ Gamma S (v * w) := by
  obtain ⟨_, _, -, -, -, -, hsurj⟩ := hA.1
  set Ω := S.zConj H with hΩ
  have hzΩ : S.z ∈ Ω := self_mem_conjIn _ _
  set Z : Ω := ⟨S.z, hzΩ⟩
  set A : Ω := ⟨a, ha⟩
  set P : Ω := ⟨v, hv⟩
  set R : Ω := ⟨w, hw⟩
  have hne : ∀ {x y : Ω}, (x : G) ≠ y → x ≠ y := fun h h' => h (congrArg Subtype.val h')
  have hZA : Z ≠ A := hne (Ne.symm haz)
  have hZP : Z ≠ P := hne (Ne.symm hvz)
  have hZR : Z ≠ R := hne (Ne.symm hwz)
  have hPA : P ≠ A := hne (Ne.symm hav)
  have hRA : R ≠ A := hne (Ne.symm haw)
  have hPR : P ≠ R := hne hvw
  have hσ : Equiv.Perm.sign (Equiv.swap Z A * Equiv.swap P R) = 1 := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hZA, Equiv.Perm.sign_swap hPR]
    decide
  obtain ⟨k, hk⟩ := hsurj _ hσ
  have e1 := congrArg Subtype.val (DFunLike.congr_fun hk Z)
  have e2 := congrArg Subtype.val (DFunLike.congr_fun hk P)
  have e3 := congrArg Subtype.val (DFunLike.congr_fun hk R)
  rw [conjAct_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hZP hZR,
    Equiv.swap_apply_left] at e1
  rw [conjAct_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hZR) hRA] at e2
  rw [conjAct_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hZP) hPA] at e3
  change (k : G) * v * (k : G)⁻¹ = w at e2
  change (k : G) * w * (k : G)⁻¹ = v at e3
  refine ⟨k, mem_centralizer_singleton_iff.mpr ?_, e1⟩
  calc (k : G) * (v * w) = (k : G) * v * (k : G)⁻¹ * ((k : G) * w * (k : G)⁻¹) * k := by group
    _ = w * v * k := by rw [e2, e3]
    _ = v * w * k := by rw [commute_of_mem_zConj S hA hw hv]

theorem card_closure_zConj {H : Subgroup G} (hA : S.IsAFive H) :
    Nat.card (closure (S.zConj H)) = 16 := by
  obtain ⟨⟨_, _, -, -, hV, -, -⟩, hC⟩ := hA
  rw [hC, card_bot, mul_one] at hV
  exact hV

variable [Finite G] {S}

theorem isAFive_HAt (hS : S.SixFourConcl) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) : S.IsAFive (S.HAt h) :=
  (hS _ (S.isHStar_of_mem_ESet ht.1 hh).1).1

theorem exists_HAt_eq (hS : S.SixFourConcl) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) {p : G} (hp : p ∈ S.zConj (S.HAt h)) (hpz : p ≠ S.z) :
    ∃ k : G, k * S.z * k⁻¹ = p ∧ S.HAt k = S.HAt h := by
  obtain ⟨k, hk, rfl⟩ := hp
  have hkM : k ∉ S.M := fun hkM => hpz (S.conj_z_of_mem_M hkM)
  exact ⟨k, rfl, ((hS _ (S.isHStar_of_mem_ESet ht.1 hh).1).2 k hk hkM).1.symm⟩

theorem mem_DSet_of_mem_zConj (hS : S.SixFourConcl) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) {p : G} (hp : p ∈ S.zConj (S.HAt h)) (hpz : p ≠ S.z) :
    p ∈ S.DSet :=
  S.zConj_diff_subset_DSet hS ht hh hp hpz

theorem mem_M_of_mem_zConj (hS : S.SixFourConcl) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) {p : G} (hp : p ∈ S.zConj (S.HAt h)) : p ∈ S.M :=
  S.mem_M_iff.mpr (commute_of_mem_zConj S (isAFive_HAt hS ht hh) hp (self_mem_conjIn _ _))

theorem clPre_commSpace_eq (hS : S.SixFourConcl)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) {p : G} (hp : p ∈ S.zConj (S.HAt h)) (hpz : p ≠ S.z)
    (hpM : p ∈ S.M) :
    S.clPre (commSpace (S.rhoL hpM)) = closure (S.zConj (S.HAt h)) ⊓ S.QG := by
  have hpD := mem_DSet_of_mem_zConj hS ht hh hp hpz
  obtain ⟨k, hk, hkH⟩ := exists_HAt_eq hS ht hh hp hpz
  set V := closure (S.zConj (S.HAt h)) with hV
  have hle : S.clPre (commSpace (S.rhoL hpM)) ≤ V ⊓ S.QG := by
    intro x hx
    obtain ⟨hxQ, hcx⟩ := S.mem_clPre.mp hx
    refine mem_inf.mpr ⟨?_, hxQ⟩
    have h1 := S.mem_closure_zConj_of_cl_mem_commSpace hpD.1 hk hpM hxQ hcx
    rwa [hkH] at h1
  have hc8 : Nat.card (S.clPre (commSpace (S.rhoL hpM))) = 8 := by
    rw [S.card_clPre, S.card_submodule, (S.fiveOne_two hS hW hpD hpM).1.2.2.2.1]
    norm_num
  have hV16 := card_closure_zConj S (isAFive_HAt hS ht hh)
  have htV : t ∈ V := subset_closure (S.mem_zConj_of_mem_ESet ht.1 hh)
  have htQ := S.not_mem_QG_of_mem_ESet hW ht.1
  have hdvd : Nat.card ↥(V ⊓ S.QG) ∣ 2 ^ 4 := by
    have h1 := card_dvd_of_le (inf_le_left : V ⊓ S.QG ≤ V)
    rwa [hV16] at h1
  have hne : Nat.card ↥(V ⊓ S.QG) ≠ 16 := by
    intro h16
    have h1 : V ⊓ S.QG = V := eq_of_le_of_card_ge inf_le_left (by rw [h16, hV16])
    have h2 : t ∈ V ⊓ S.QG := by rw [h1]; exact htV
    exact htQ (mem_inf.mp h2).2
  have h8 : Nat.card ↥(V ⊓ S.QG) ≤ 8 := by
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hm'] at hne ⊢
    interval_cases m <;> simp at hne ⊢
  exact eq_of_le_of_card_ge hle (by rw [hc8]; exact h8)

theorem commSpace_eq_of_mem_zConj (hS : S.SixFourConcl)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) (htM : t ∈ S.M) {p : G} (hp : p ∈ S.zConj (S.HAt h))
    (hpz : p ≠ S.z) (hpM : p ∈ S.M) : commSpace (S.rhoL hpM) = commSpace (S.rhoL htM) := by
  have h1 := clPre_commSpace_eq hS hW ht hh hp hpz hpM
  have h2 := clPre_commSpace_eq hS hW ht hh (S.mem_zConj_of_mem_ESet ht.1 hh)
    (S.ne_z_of_mem_ESet ht.1) htM
  rw [← S.clSub_clPre (commSpace (S.rhoL hpM)), h1, ← h2, S.clSub_clPre]

theorem exists_mem_Gamma (hS : S.SixFourConcl) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) (htM : t ∈ S.M) {u : G} (hu : u ∈ S.QG) (hu1 : u ≠ 1)
    (huz : u ≠ S.z) (hcu : S.cl u ∈ commSpace (S.rhoL htM)) :
    ∃ s ∈ S.zConj (S.HAt h), s ≠ S.z ∧ S.z * s * u ∈ S.zConj (S.HAt h) ∧
      S.z * s * u ≠ S.z ∧ s ∈ Gamma S u ∧ S.z * s * u ∈ Gamma S u := by
  have hA := isAFive_HAt hS ht hh
  have hzΩ : S.z ∈ S.zConj (S.HAt h) := self_mem_conjIn _ _
  have htΩ := S.mem_zConj_of_mem_ESet ht.1 hh
  have htz := S.ne_z_of_mem_ESet ht.1
  have htt := mul_self_of_mem_zConj S htΩ
  have htinv : t⁻¹ = t := inv_eq_of_mem_zConj S htΩ
  obtain ⟨w, hw⟩ := mem_commSpace.mp hcu
  obtain ⟨y, hy, rfl⟩ := S.exists_cl w
  set p := y * t * y⁻¹ with hpdef
  have hpΩ : p ∈ S.zConj (S.HAt h) := conj_mem_conjIn_of_mem (le_sup_left (b := S.Qa h) hy) htΩ
  have hpz : p ≠ S.z := by
    intro h'
    apply htz
    calc t = y⁻¹ * p * y := by rw [hpdef]; group
      _ = S.z := by rw [h', mul_assoc, ← S.z_comm_QG hy]; group
  have hc : t * p = (t * y * t⁻¹) * y⁻¹ := by rw [hpdef, htinv]; group
  have htpQ : t * p ∈ S.QG := by
    rw [hc]
    exact S.QG.mul_mem (S.conj_mem_QG htM hy) (S.QG.inv_mem hy)
  have hcl : S.cl (t * p) = S.cl u := by
    rw [← hw, hc, S.cl_mul (S.conj_mem_QG htM hy) (S.QG.inv_mem hy), S.cl_inv hy,
      ← S.rhoL_cl htM hy, sub_eq_add_vec (ZMod 2)]
  have htp : t ≠ p := by
    intro h'
    rcases (S.cl_eq_cl_iff htpQ hu).mp hcl with h1 | h1 <;> rw [← h', htt] at h1
    · exact hu1 h1
    · exact huz (by rw [h1, one_mul])
  obtain ⟨a, haΩ, b, hbΩ, hab, haz, hat, hap, hbz, hbt, hbp, habeq⟩ :=
    exists_mul_eq_of_three S hA hzΩ htΩ hpΩ (Ne.symm htz) (Ne.symm hpz) htp
  rcases (S.cl_eq_cl_iff htpQ hu).mp hcl with rfl | rfl
  · have hb' : S.z * a * (t * p) = b := by
      calc S.z * a * (t * p) = a * (S.z * t * p) := by
            rw [commute_of_mem_zConj S hA hzΩ haΩ]; group
        _ = b := by rw [habeq, ← mul_assoc, mul_self_of_mem_zConj S haΩ, one_mul]
    refine ⟨a, haΩ, haz, by rw [hb']; exact hbΩ, by rw [hb']; exact hbz,
      mem_Gamma_mul S hA haΩ htΩ hpΩ haz htz hpz hat hap htp, ?_⟩
    rw [hb']
    exact mem_Gamma_mul S hA hbΩ htΩ hpΩ hbz htz hpz hbt hbp htp
  · have hu2 : t * p * S.z = a * b := by
      rw [← habeq, mul_assoc t p, commute_of_mem_zConj S hA hpΩ hzΩ, ← mul_assoc,
        commute_of_mem_zConj S hA htΩ hzΩ]
    have hp' : S.z * t * (t * p * S.z) = p := by
      calc S.z * t * (t * p * S.z) = S.z * (t * t) * p * S.z := by group
        _ = S.z * p * S.z := by rw [htt, mul_one]
        _ = p * S.z * S.z := by rw [commute_of_mem_zConj S hA hzΩ hpΩ]
        _ = p := by rw [mul_assoc, S.z_mul_z, mul_one]
    refine ⟨t, htΩ, htz, by rw [hp']; exact hpΩ, by rw [hp']; exact hpz, ?_, ?_⟩
    · rw [hu2]
      exact mem_Gamma_mul S hA htΩ haΩ hbΩ htz haz hbz (Ne.symm hat) (Ne.symm hbt) hab
    · rw [hp', hu2]
      exact mem_Gamma_mul S hA hpΩ haΩ hbΩ hpz haz hbz (Ne.symm hap) (Ne.symm hbp) hab

end AS62

end CFSG.LargeExtraspecial

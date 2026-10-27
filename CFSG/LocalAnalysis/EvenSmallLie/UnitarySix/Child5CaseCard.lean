module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DNorm
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp7

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open CFSG.Fischer Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaSec3

section General

variable {G : Type} [Group G]

theorem card_sup_dvd_mul {H N : Subgroup G} (hHN : H ≤ normalizer (N : Set G)) :
    Nat.card (H ⊔ N : Subgroup G) ∣ Nat.card H * Nat.card N := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N))
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
  have h3 : Nat.card (N.subgroupOf (H ⊔ N)) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have h4 : Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) = Nat.card (↥H ⧸ N.subgroupOf H) :=
    (Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN).toEquiv).symm
  rw [h1, h3, h4]
  exact Nat.mul_dvd_mul_right (Dvd.intro _ h2.symm) _

theorem card_le_of_dvd_mul {P : Subgroup G} (h2 : IsPGroup 2 P) (h : Nat.card P ∣ 2 ^ 6 * 45) :
    Nat.card P ≤ 2 ^ 6 := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at h
    norm_num at h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  rw [hn] at h ⊢
  have hc : Nat.Coprime (2 ^ n) 45 := Nat.Coprime.pow_left n (by norm_num)
  exact Nat.le_of_dvd (by norm_num) (hc.dvd_of_dvd_mul_right h)

end General

section Sig

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

theorem card_sig : Nat.card (sec3DData e t).Sig = 6 := by
  rw [show (sec3DData e t).Sig = toG e chSig.grp from rfl, card_toG_ch gensOK_chSig, card_chSig]

theorem card_lam : Nat.card (sec3DData e t).Λ = 60 := by
  rw [show (sec3DData e t).Λ = toG e chLam.grp from rfl, card_toG_ch gensOK_chLam, card_chLam]

theorem x₃_mul_self : (sec3DData e t).x₃ * (sec3DData e t).x₃ = 1 := by
  show gw e [4] * gw e [4] = 1
  rw [← gw_append, gw_eq_xId (b := []) (by decide) (by decide) (by decide), gw_nil]

theorem w₃_mul_self : gw e [17] * gw e [17] = 1 := by
  rw [← gw_append, gw_eq_xId (b := []) (by decide) (by decide) (by decide), gw_nil]

theorem e_eq_x₃_mul : (sec3DData e t).e = (sec3DData e t).x₃ * gw e [17] := by
  show gw e [4, 17] = gw e [4] * gw e [17]
  rw [← gw_append]
  rfl

theorem e_ne_one : (sec3DData e t).e ≠ 1 := by
  intro h
  have h1 := d_A₃_le_comm_e (e := e) (t := t)
  rw [h, zpowers_one_eq_bot, commutator_bot_right, bot_sup_eq] at h1
  have hfin : Finite (sec3DData e t).A₄ :=
    Nat.finite_of_card_ne_zero (by rw [d_card_A₄]; norm_num)
  have h2 := Subgroup.card_le_of_le h1
  rw [d_card_A₃, d_card_A₄] at h2
  norm_num at h2

theorem orderOf_e : orderOf (sec3DData e t).e = 3 := orderOf_eq_prime d_e_pow e_ne_one

theorem x₃_conj_e : (sec3DData e t).x₃ * (sec3DData e t).e * (sec3DData e t).x₃⁻¹ =
    (sec3DData e t).e⁻¹ := by
  have hx := x₃_mul_self (e := e) (t := t)
  have hxi : (sec3DData e t).x₃⁻¹ = (sec3DData e t).x₃ := inv_eq_of_mul_eq_one_right hx
  have hwi : (gw e [17])⁻¹ = gw e [17] := inv_eq_of_mul_eq_one_right w₃_mul_self
  rw [e_eq_x₃_mul, hxi, _root_.mul_inv_rev, hxi, hwi, ← mul_assoc, hx, one_mul]

theorem x₃_not_comm_e : (sec3DData e t).x₃ * (sec3DData e t).e ≠
    (sec3DData e t).e * (sec3DData e t).x₃ := by
  intro h
  have h1 : (sec3DData e t).e = (sec3DData e t).e⁻¹ := by
    rw [← x₃_conj_e, h, mul_inv_cancel_right]
  have h2 : (sec3DData e t).e ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel _
  have h3 : (sec3DData e t).e = 1 := by
    have h4 := d_e_pow (e := e) (t := t)
    rw [pow_succ, h2, one_mul] at h4
    exact h4
  exact e_ne_one h3

theorem sig_inf_cent_e : (sec3DData e t).Sig ⊓ centralizer ({(sec3DData e t).e} : Set G) =
    zpowers (sec3DData e t).e := by
  have hfin : Finite (sec3DData e t).Sig :=
    Nat.finite_of_card_ne_zero (by rw [card_sig]; norm_num)
  have hfin2 : Finite ((sec3DData e t).Sig ⊓ centralizer ({(sec3DData e t).e} : Set G) :
      Subgroup G) :=
    Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  have hle : zpowers (sec3DData e t).e ≤
      (sec3DData e t).Sig ⊓ centralizer ({(sec3DData e t).e} : Set G) :=
    zpowers_le.mpr ⟨d_e_mem_Sig, mem_centralizer_singleton_iff.mpr rfl⟩
  have h1 : Nat.card ((sec3DData e t).Sig ⊓ centralizer ({(sec3DData e t).e} : Set G) :
      Subgroup G) ∣ 6 := by
    rw [← card_sig (e := e) (t := t)]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h3 : 3 ∣ Nat.card ((sec3DData e t).Sig ⊓ centralizer ({(sec3DData e t).e} : Set G) :
      Subgroup G) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, orderOf_e] at this
  have h6 : Nat.card ((sec3DData e t).Sig ⊓ centralizer ({(sec3DData e t).e} : Set G) :
      Subgroup G) ≠ 6 := by
    intro h
    have heq : (sec3DData e t).Sig ⊓ centralizer ({(sec3DData e t).e} : Set G) =
        (sec3DData e t).Sig :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, card_sig])
    have hx : (sec3DData e t).x₃ ∈
        (sec3DData e t).Sig ⊓ centralizer ({(sec3DData e t).e} : Set G) := by
      rw [heq]
      exact d_x₃_mem_Sig
    exact x₃_not_comm_e (mem_centralizer_singleton_iff.mp hx.2)
  obtain ⟨c, hc⟩ : ∃ c, Nat.card ((sec3DData e t).Sig ⊓
      centralizer ({(sec3DData e t).e} : Set G) : Subgroup G) = c := ⟨_, rfl⟩
  rw [hc] at h1 h3 h6
  have hc3 : c = 3 := by
    have := Nat.le_of_dvd (by norm_num) h1
    interval_cases c <;> omega
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hc, hc3, Nat.card_zpowers, orderOf_e]

theorem sig_inf_A₃ : (sec3DData e t).Sig ⊓ (sec3DData e t).A₃ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  by_contra hx1
  have hfin : Finite (sec3DData e t).Sig :=
    Nat.finite_of_card_ne_zero (by rw [card_sig]; norm_num)
  have hfinI : Finite ((sec3DData e t).Sig ⊓ (sec3DData e t).A₃ : Subgroup G) :=
    Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  have hI2 : IsPGroup 2 ((sec3DData e t).Sig ⊓ (sec3DData e t).A₃ : Subgroup G) :=
    (IsPGroup.of_card (d_card_A₃ (e := e) (t := t))).to_le inf_le_right
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hI2
  have hdvd : Nat.card ((sec3DData e t).Sig ⊓ (sec3DData e t).A₃ : Subgroup G) ∣ 6 := by
    rw [← card_sig (e := e) (t := t)]
    exact Subgroup.card_dvd_of_le inf_le_left
  rw [hn] at hdvd
  have hn1 : n ≤ 1 := by
    by_contra h
    have h4 : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := h4.trans hdvd
    norm_num at this
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have hsub := (Nat.card_eq_one_iff_unique.mp hn).1
    exact hx1 (congrArg Subtype.val (Subsingleton.elim
      (⟨x, hx⟩ : ((sec3DData e t).Sig ⊓ (sec3DData e t).A₃ : Subgroup G)) 1))
  have hn2 : Nat.card ((sec3DData e t).Sig ⊓ (sec3DData e t).A₃ : Subgroup G) = 2 := by
    rw [hn, show n = 1 by omega, pow_one]
  have hy : (sec3DData e t).e * x * (sec3DData e t).e⁻¹ ∈
      (sec3DData e t).Sig ⊓ (sec3DData e t).A₃ :=
    Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem d_e_mem_Sig hx.1) (inv_mem d_e_mem_Sig),
      (mem_normalizer_iff.mp d_e_norm_A₃ x).mp hx.2⟩
  obtain ⟨y, -, hyu⟩ := (Nat.card_eq_two_iff' (1 : ((sec3DData e t).Sig ⊓
    (sec3DData e t).A₃ : Subgroup G))).mp hn2
  have hne1 : (⟨x, hx⟩ : ((sec3DData e t).Sig ⊓ (sec3DData e t).A₃ : Subgroup G)) ≠ 1 :=
    fun h => hx1 (congrArg Subtype.val h)
  have hne2 : (⟨_, hy⟩ : ((sec3DData e t).Sig ⊓ (sec3DData e t).A₃ : Subgroup G)) ≠ 1 := by
    intro h
    have h' : (sec3DData e t).e * x * (sec3DData e t).e⁻¹ = 1 := congrArg Subtype.val h
    apply hx1
    calc x = (sec3DData e t).e⁻¹ * ((sec3DData e t).e * x * (sec3DData e t).e⁻¹) *
          (sec3DData e t).e := by group
      _ = 1 := by rw [h']; group
  have hxy : (sec3DData e t).e * x * (sec3DData e t).e⁻¹ = x :=
    congrArg Subtype.val ((hyu _ hne2).trans (hyu _ hne1).symm)
  have hxe : x * (sec3DData e t).e = (sec3DData e t).e * x := by
    calc x * (sec3DData e t).e = (sec3DData e t).e * x * (sec3DData e t).e⁻¹ *
          (sec3DData e t).e := by rw [hxy]
      _ = (sec3DData e t).e * x := by group
  have hxz : x ∈ zpowers (sec3DData e t).e := by
    rw [← sig_inf_cent_e]
    exact ⟨hx.1, mem_centralizer_singleton_iff.mpr hxe⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hxz
  have h3 : ((sec3DData e t).e ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, d_e_pow, one_zpow]
  have h2' : ((sec3DData e t).e ^ k) ^ 2 = 1 := by
    have := pow_card_eq_one' (x := (⟨_, hx⟩ : ((sec3DData e t).Sig ⊓ (sec3DData e t).A₃ :
      Subgroup G)))
    rw [hn2] at this
    exact congrArg Subtype.val this
  apply hx1
  rw [pow_succ, h2', one_mul] at h3
  exact h3

theorem mem_lam_e_A₄ {g : G} (hgL : g ∈ L)
    (hge : g * (sec3DData e t).e = (sec3DData e t).e * g)
    (hgN : g ∈ normalizer ((sec3DData e t).A₃ : Set G)) :
    g ∈ (sec3DData e t).Λ ⊔ zpowers (sec3DData e t).e ⊔ (sec3DData e t).A₄ := by
  have hΛS : (sec3DData e t).Λ ≤ normalizer ((sec3DData e t).Sig : Set G) := fun l hl =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun s hs => (d_Λ_comm_Sig l hl s hs).symm)
  have hΛSA : (sec3DData e t).Λ ⊔ (sec3DData e t).Sig ≤
      normalizer ((sec3DData e t).A₃ : Set G) := sup_le d_Λ_le_NA₃ d_Sig_le_NA₃
  have hg : g ∈ (sec3DData e t).Λ ⊔ (sec3DData e t).Sig ⊔ (sec3DData e t).A₃ :=
    d_NLA₃_le_gen ⟨hgL, hgN⟩
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hΛSA] at hg
  obtain ⟨u, hu, a, ha, rfl⟩ := hg
  rw [coe_mul_of_left_le_normalizer_right _ _ hΛS] at hu
  obtain ⟨l, hl, s, hs, rfl⟩ := hu
  have hle : l * (sec3DData e t).e = (sec3DData e t).e * l := d_Λ_comm_Sig l hl _ d_e_mem_Sig
  have h1 : s * a * (sec3DData e t).e = (sec3DData e t).e * s * a := by
    calc s * a * (sec3DData e t).e = l⁻¹ * (l * s * a * (sec3DData e t).e) := by group
      _ = l⁻¹ * ((sec3DData e t).e * (l * s * a)) := by rw [hge]
      _ = l⁻¹ * ((sec3DData e t).e * l) * s * a := by group
      _ = l⁻¹ * (l * (sec3DData e t).e) * s * a := by rw [hle]
      _ = (sec3DData e t).e * s * a := by group
  have hc : s⁻¹ * (sec3DData e t).e * s * (sec3DData e t).e⁻¹ =
      a * ((sec3DData e t).e * a⁻¹ * (sec3DData e t).e⁻¹) := by
    calc s⁻¹ * (sec3DData e t).e * s * (sec3DData e t).e⁻¹ =
          s⁻¹ * ((sec3DData e t).e * s * a) * a⁻¹ * (sec3DData e t).e⁻¹ := by group
      _ = s⁻¹ * (s * a * (sec3DData e t).e) * a⁻¹ * (sec3DData e t).e⁻¹ := by rw [h1]
      _ = a * ((sec3DData e t).e * a⁻¹ * (sec3DData e t).e⁻¹) := by group
  have hcm : s⁻¹ * (sec3DData e t).e * s * (sec3DData e t).e⁻¹ ∈
      (sec3DData e t).Sig ⊓ (sec3DData e t).A₃ := by
    refine Subgroup.mem_inf.mpr
      ⟨mul_mem (mul_mem (mul_mem (inv_mem hs) d_e_mem_Sig) hs) (inv_mem d_e_mem_Sig), ?_⟩
    rw [hc]
    exact mul_mem ha ((mem_normalizer_iff.mp d_e_norm_A₃ a⁻¹).mp (inv_mem ha))
  rw [sig_inf_A₃, mem_bot] at hcm
  have hse : s * (sec3DData e t).e = (sec3DData e t).e * s := by
    calc s * (sec3DData e t).e = s * 1 * (sec3DData e t).e := by group
      _ = s * (s⁻¹ * (sec3DData e t).e * s * (sec3DData e t).e⁻¹) * (sec3DData e t).e := by
          rw [hcm]
      _ = (sec3DData e t).e * s := by group
  have hs' : s ∈ zpowers (sec3DData e t).e := by
    rw [← sig_inf_cent_e]
    exact ⟨hs, mem_centralizer_singleton_iff.mpr hse⟩
  have hae : a * (sec3DData e t).e = (sec3DData e t).e * a := by
    calc a * (sec3DData e t).e = s⁻¹ * (s * a * (sec3DData e t).e) := by group
      _ = s⁻¹ * ((sec3DData e t).e * s * a) := by rw [h1]
      _ = s⁻¹ * ((sec3DData e t).e * s) * a := by group
      _ = s⁻¹ * (s * (sec3DData e t).e) * a := by rw [hse]
      _ = (sec3DData e t).e * a := by group
  have ha4 : a ∈ (sec3DData e t).A₄ :=
    d_A₃_cent_e ⟨ha, mem_centralizer_singleton_iff.mpr hae⟩
  exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hl)) (mem_sup_left (mem_sup_right hs')))
    (mem_sup_right ha4)

theorem card_lam_e_A₄_dvd : Nat.card ((sec3DData e t).Λ ⊔ zpowers (sec3DData e t).e ⊔
    (sec3DData e t).A₄ : Subgroup G) ∣ 2 ^ 6 * 45 := by
  have hΛe : (sec3DData e t).Λ ≤ normalizer (zpowers (sec3DData e t).e : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [le_centralizer_iff]
    exact zpowers_le.mpr (mem_centralizer_iff.mpr fun l hl => d_Λ_comm_Sig l hl _ d_e_mem_Sig)
  have hΛeA : (sec3DData e t).Λ ⊔ zpowers (sec3DData e t).e ≤
      normalizer ((sec3DData e t).A₄ : Set G) :=
    sup_le d_Λ_le_normalizer (zpowers_le.mpr (centralizer_le_normalizer _ d_e_cent_A₄))
  have h1 := card_sup_dvd_mul hΛe
  have h2 := card_sup_dvd_mul hΛeA
  rw [card_lam, Nat.card_zpowers, orderOf_e] at h1
  rw [d_card_A₄] at h2
  calc _ ∣ Nat.card ((sec3DData e t).Λ ⊔ zpowers (sec3DData e t).e : Subgroup G) * 2 ^ 4 := h2
    _ ∣ 60 * 3 * 2 ^ 4 := Nat.mul_dvd_mul_right h1 _
    _ = 2 ^ 6 * 45 := by norm_num

theorem card_le_of_cent_e_norm_A₃ (P : Subgroup G)
    (hP : P ≤ L ⊓ centralizer ({(sec3DData e t).e} : Set G) ⊓
      normalizer ((sec3DData e t).A₃ : Set G)) (h2 : IsPGroup 2 P) : Nat.card P ≤ 2 ^ 6 := by
  have hPM : P ≤ (sec3DData e t).Λ ⊔ zpowers (sec3DData e t).e ⊔ (sec3DData e t).A₄ :=
    fun g hg => mem_lam_e_A₄ (hP hg).1.1 (mem_centralizer_singleton_iff.mp (hP hg).1.2) (hP hg).2
  exact card_le_of_dvd_mul h2 ((Subgroup.card_dvd_of_le hPM).trans card_lam_e_A₄_dvd)

end Sig

end CFSG.EvenSmallLie.UnitarySix.Child5

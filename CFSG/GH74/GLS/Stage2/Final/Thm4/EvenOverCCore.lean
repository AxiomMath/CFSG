module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOverCDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Cited
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {M : Subgroup G}

theorem Rigid.z_mem (h : Rigid z M) : z ∈ M := h.cen_le (mem_Cen_self z)

theorem Rigid.fitting_eq (h : Rigid z M) : Fs M = Fm M := (fitting_eq_of_odd h.odd).1

theorem Rigid.odd_Fm (h : Rigid z M) : Odd (Nat.card ↥(Fm M)) := by
  rw [← h.fitting_eq, card_Fs]
  exact h.odd

theorem Rigid.mem_Fm_of_centralizes (h : Rigid z M) {x : G} (hx : x ∈ M)
    (hc : ∀ y ∈ Fm M, x * y = y * x) : x ∈ Fm M := by
  refine mem_Fm_of_centralizes_Fs hx ?_
  rw [h.fitting_eq]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hc y hy).symm

private theorem Rigid.core_mul_self (h : Rigid z M) : z * z = 1 := by
  rw [← pow_two, ← h.z_ord]
  exact pow_orderOf_eq_one z

theorem Rigid.Fm_inf_Cen (h : Rigid z M) : Fm M ⊓ Cen z = ⊥ := by
  have h1 : pPrimeCore 2 ↥(Cen z) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 2 ↥(Cen z))
      (Cen z).subtype_injective).mp h.oddCore
  have hn : ((Fm M ⊓ Cen z).subgroupOf (Cen z)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff inf_le_right).mpr fun x c hx hc => ?_
    refine ⟨?_, (Cen z).mul_mem ((Cen z).mul_mem hc hx.2) ((Cen z).inv_mem hc)⟩
    exact (mem_normalizer_iff.mp (le_normalizer_Fm M (h.cen_le hc)) x).mp hx.1
  have hcard : Nat.Coprime 2 (Nat.card ↥((Fm M ⊓ Cen z).subgroupOf (Cen z))) := by
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : Fm M ⊓ Cen z ≤ Cen z)).toEquiv]
    exact Nat.coprime_two_left.mpr
      (Odd.of_dvd_nat h.odd_Fm (Subgroup.card_dvd_of_le inf_le_left))
  have h2 := (pPrimeCore_eq_bot_iff.mp h1) _ hn hcard
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hmem : (⟨x, hx.2⟩ : ↥(Cen z)) ∈ (Fm M ⊓ Cen z).subgroupOf (Cen z) :=
    Subgroup.mem_subgroupOf.mpr hx
  rw [h2, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem Rigid.inverts (h : Rigid z M) : Inverts z (Fm M) := by
  refine inverts_of_fixed_free h.core_mul_self (le_normalizer_Fm M h.z_mem) ?_
  intro d hd hzd
  have hmem : d ∈ Fm M ⊓ Cen z := ⟨hd, Subgroup.mem_centralizer_singleton_iff.mpr hzd.symm⟩
  rw [h.Fm_inf_Cen, Subgroup.mem_bot] at hmem
  exact hmem

omit [Finite G] in
private theorem core_inverts_comm {u : G} {A : Subgroup G} (h : Inverts u A) :
    ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  intro x hx y hy
  have h1 := h (x * y) (A.mul_mem hx hy)
  have h2 : u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) := by group
  rw [h2, h x hx, h y hy, mul_inv_rev] at h1
  have h3 := congrArg (fun t => t⁻¹) h1
  simpa using h3.symm

theorem Rigid.Fm_comm (h : Rigid z M) : ∀ x ∈ Fm M, ∀ y ∈ Fm M, x * y = y * x :=
  core_inverts_comm h.inverts

omit [Finite G] in
private theorem core_zpowers_cases {u : G} (hu : u * u = 1) {y : G} (hy : y ∈ zpowers u) :
    y = 1 ∨ y = u := by
  have hu2 : u ^ 2 = 1 := by rw [pow_two]; exact hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk := Int.mul_ediv_add_emod k 2
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← hk, h0, add_zero, zpow_mul, zpow_ofNat, hu2, one_zpow]
  · right
    rw [← hk, h1, zpow_add, zpow_mul, zpow_ofNat, hu2, one_zpow, one_mul, zpow_one]

omit [Finite G] in
private theorem core_zpowers_le_centralizer {u v : G} (hc : u * v = v * u) :
    zpowers v ≤ centralizer ((zpowers u : Subgroup G) : Set G) := by
  refine Subgroup.zpowers_le.mpr ?_
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact (Commute.zpow_left (show Commute u v from hc) k).eq

open scoped Pointwise in
omit [Finite G] in
private theorem core_four_mem {u v : G} (hu : u * u = 1) (hv : v * v = 1) (hc : u * v = v * u)
    {x : G} (hx : x ∈ zpowers u ⊔ zpowers v) : x = 1 ∨ x = u ∨ x = v ∨ x = u * v := by
  have hn : zpowers v ≤ normalizer ((zpowers u : Subgroup G) : Set G) :=
    (core_zpowers_le_centralizer hc).trans (Subgroup.centralizer_le_normalizer _)
  have hx' : x ∈ ((zpowers u : Subgroup G) : Set G) * (zpowers v : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  rcases core_zpowers_cases hu ha with rfl | rfl <;>
    rcases core_zpowers_cases hv hb with rfl | rfl <;> simp

omit [Finite G] in
private theorem core_four_group {u v : G} (hu : u * u = 1) (hv : v * v = 1) (hc : u * v = v * u)
    (hne : u ≠ v) (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) :
    IsElementaryAbelian 2 ↥(zpowers u ⊔ zpowers v) ∧
      Nat.card ↥(zpowers u ⊔ zpowers v) = 2 ^ 2 := by
  have hu' : u ^ 2 = 1 := by rw [pow_two]; exact hu
  have hv' : v ^ 2 = 1 := by rw [pow_two]; exact hv
  have : IsElementaryAbelian 2 ↥(zpowers u) := IsElementaryAbelian.zpowers_of_pow_eq_one hu'
  have : IsElementaryAbelian 2 ↥(zpowers v) := IsElementaryAbelian.zpowers_of_pow_eq_one hv'
  have hvc := core_zpowers_le_centralizer hc
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hvc, ?_⟩
  have hn : zpowers v ≤ normalizer ((zpowers u : Subgroup G) : Set G) :=
    hvc.trans (Subgroup.centralizer_le_normalizer _)
  have hdisj : Disjoint (zpowers u) (zpowers v) := by
    rw [Subgroup.disjoint_def]
    intro x hxu hxv
    rcases core_zpowers_cases hu hxu with h1 | h1
    · exact h1
    · rcases core_zpowers_cases hv hxv with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hne
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hn hdisj,
    Nat.card_zpowers, Nat.card_zpowers, hu2, hv2]
  norm_num

omit [Finite G] in
private theorem core_eq_one_of_odd {F : Subgroup G} (hF : Odd (Nat.card ↥F)) {w : G} (hw : w ∈ F)
    (hw2 : w * w = 1) : w = 1 := by
  have hdvd : orderOf w ∣ Nat.card ↥F := by
    have := orderOf_dvd_natCard (⟨w, hw⟩ : ↥F)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2)
  have h3 : orderOf w ∣ Nat.gcd 2 (Nat.card ↥F) := Nat.dvd_gcd h2 hdvd
  rw [Nat.coprime_two_left.mpr hF] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem Rigid.cenF_ne_bot (h : Rigid z M) {t : G} (ht : t ∈ Cen z) (ht2 : orderOf t = 2)
    (htz : t ≠ z) : Fm M ⊓ centralizer ({t} : Set G) ≠ ⊥ := by
  intro hbot
  have hz2 : z * z = 1 := h.core_mul_self
  have ht2' : t * t = 1 := mul_self_eq_one_of_orderOf_two ht2
  have hcomm : z * t = t * z := (Subgroup.mem_centralizer_singleton_iff.mp ht).symm
  obtain ⟨hVel, hVcard⟩ := core_four_group hz2 ht2' hcomm htz.symm h.z_ord ht2
  have hVn : zpowers z ⊔ zpowers t ≤ normalizer ((Fm M : Subgroup G) : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (le_normalizer_Fm M h.z_mem))
      (Subgroup.zpowers_le.mpr (le_normalizer_Fm M (h.cen_le ht)))
  have hcop : Nat.Coprime 2 (Nat.card ↥(Fm M)) := Nat.coprime_two_left.mpr h.odd_Fm
  have hgen := ig_11_23_thm G 2 Nat.prime_two _ (Fm M) hVel hVcard hcop hVn
  have hle : (⨆ (v : G) (_ : v ∈ zpowers z ⊔ zpowers t ∧ v ≠ 1),
      Fm M ⊓ centralizer ({v} : Set G)) ≤ centralizer ({z * t} : Set G) := by
    refine iSup₂_le fun v hv => ?_
    rcases core_four_mem hz2 ht2' hcomm hv.1 with rfl | rfl | rfl | rfl
    · exact absurd rfl hv.2
    · rw [h.Fm_inf_Cen]; exact bot_le
    · rw [hbot]; exact bot_le
    · exact inf_le_right
  have hztM : z * t ∈ M := M.mul_mem h.z_mem (h.cen_le ht)
  have hztF : z * t ∈ Fm M := h.mem_Fm_of_centralizes hztM fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hle (hgen hy))).symm
  have hzt2 : (z * t) * (z * t) = 1 := by
    calc z * t * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [hcomm]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [hz2, ht2', one_mul]
  have h1 := core_eq_one_of_odd h.odd_Fm hztF hzt2
  apply htz
  calc t = z⁻¹ * (z * t) := by group
    _ = z⁻¹ := by rw [h1, mul_one]
    _ = z := inv_eq_of_mul_eq_one_right hz2

theorem Rigid.exists_X (h : Rigid z M) {t : G} (ht : t ∈ Cen z) (ht2 : orderOf t = 2)
    (htz : t ≠ z) :
    ∃ (p : ℕ) (X : Subgroup G), p.Prime ∧ p ≠ 2 ∧ X ≤ centralizer ({t} : Set G) ∧
      IsPGroup p ↥X ∧ X ≠ ⊥ ∧
      (∀ c ∈ centralizer ({t} : Set G), c ∈ Cen z → c ∈ normalizer (X : Set G)) ∧
      ⁅X, zpowers z⁆ = X := by
  set A : Subgroup G := Fm M ⊓ centralizer ({t} : Set G) with hA
  have hAne : A ≠ ⊥ := h.cenF_ne_bot ht ht2 htz
  have hcardA : Nat.card ↥A ≠ 1 := fun h1 => hAne (Subgroup.eq_bot_of_card_eq _ h1)
  obtain ⟨p, hp, hpA⟩ := Nat.exists_prime_and_dvd hcardA
  have hpF : p ∣ Nat.card ↥(Fm M) := hpA.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h.odd_Fm) (even_iff_two_dvd.mpr hpF)
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hpow : ∀ (x : G) (k l : ℕ), x ^ (p ^ k) = 1 → x ^ (p ^ (k + l)) = 1 := by
    intro x k l hx
    rw [pow_add, pow_mul, hx, one_pow]
  let X : Subgroup G :=
    { carrier := {x | x ∈ A ∧ ∃ n : ℕ, x ^ (p ^ n) = 1}
      one_mem' := ⟨A.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, n, hn⟩ ⟨hb, m, hm⟩
        refine ⟨A.mul_mem ha hb, n + m, ?_⟩
        have hab : Commute a b := h.Fm_comm a ha.1 b hb.1
        have hb' : b ^ (p ^ (n + m)) = 1 := by rw [add_comm]; exact hpow b m n hm
        rw [hab.mul_pow, hpow a n m hn, hb', one_mul]
      inv_mem' := by
        rintro a ⟨ha, n, hn⟩
        exact ⟨A.inv_mem ha, n, by rw [inv_pow, hn, inv_one]⟩ }
  have hX : ∀ x : G, x ∈ X ↔ (x ∈ A ∧ ∃ n : ℕ, x ^ (p ^ n) = 1) := fun x => Iff.rfl
  have hinv := h.inverts
  have hnorm : ∀ c ∈ centralizer ({t} : Set G), c ∈ Cen z → ∀ x ∈ X, c * x * c⁻¹ ∈ X := by
    intro c hct hcz x hx
    obtain ⟨hxA, n, hn⟩ := (hX x).mp hx
    refine (hX _).mpr ⟨⟨?_, ?_⟩, n, ?_⟩
    · exact (mem_normalizer_iff.mp (le_normalizer_Fm M (h.cen_le hcz)) x).mp hxA.1
    · exact (centralizer ({t} : Set G)).mul_mem
        ((centralizer ({t} : Set G)).mul_mem hct hxA.2) ((centralizer ({t} : Set G)).inv_mem hct)
    · rw [conj_pow, hn, mul_one, mul_inv_cancel]
  have hzn : z ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hinv x ((hX x).mp hx).1.1]
      exact X.inv_mem hx
    · intro hx
      have hxF : x ∈ Fm M :=
        (mem_normalizer_iff.mp (le_normalizer_Fm M h.z_mem) x).mpr ((hX _).mp hx).1.1
      rw [hinv x hxF] at hx
      simpa using X.inv_mem hx
  refine ⟨p, X, hp, hp2, fun x hx => ((hX x).mp hx).1.2, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨-, n, hn⟩ := (hX x).mp x.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) p hpA
    intro hbot
    have hxp : (x : G) ^ p = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this
    have hxX : (x : G) ∈ X := (hX _).mpr ⟨x.2, 1, by rwa [pow_one]⟩
    rw [hbot, Subgroup.mem_bot] at hxX
    have hord : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
    rw [hxX, orderOf_one] at hord
    exact hp.one_lt.ne hord
  · intro c hct hcz
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hnorm c hct hcz x, fun hx => ?_⟩
    have h1 := hnorm c⁻¹ ((centralizer ({t} : Set G)).inv_mem hct) ((Cen z).inv_mem hcz) _ hx
    have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
    rwa [e] at h1
  · apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx g hg
      have hgn : g ∈ normalizer (X : Set G) := Subgroup.zpowers_le.mpr hzn hg
      rw [commutatorElement_def]
      have h1 := X.mul_mem hx ((mem_normalizer_iff.mp hgn x⁻¹).mp (X.inv_mem hx))
      simpa [mul_assoc] using h1
    · intro x hx
      obtain ⟨hxA, n, hn⟩ := (hX x).mp hx
      have hsq : x ^ 2 = ⁅x, z⁆ := by
        rw [commutatorElement_def, pow_two]
        have h1 := hinv x⁻¹ ((Fm M).inv_mem hxA.1)
        rw [inv_inv] at h1
        calc x * x = x * (z * x⁻¹ * z⁻¹) := by rw [h1]
          _ = x * z * x⁻¹ * z⁻¹ := by group
      refine mem_of_sq_mem (N := p ^ n) hpodd.pow hn ?_
      rw [hsq]
      exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers z)

end CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver

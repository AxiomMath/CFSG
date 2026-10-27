module

public import CFSG.GH74.Uniqueness.Section171Invol
public import CFSG.GH74.Uniqueness.Section176Basic
public import CFSG.GH74.Uniqueness.Section176Torus
public import CFSG.Quasithin.Background.A1a

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.mem_oTwoIn_of_ncard_omega
    (S : ZDSetup X Z M) {k : ℕ}
    (hΩ : (omega M).ncard = 2 ^ k + 1) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) : z ∈ oTwoIn M := by
  by_contra hzV
  have hz2 : orderOf z = 2 := S.invariant.1 z hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (S.invariant.mul_self_eq_one hz)
  have hX : Nat.card (zpowers (⟨z, hzM⟩ : ↥M)) = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz2]
  have hnot : ¬ zpowers (⟨z, hzM⟩ : ↥M) ≤ CFSG.Open.pCore 2 ↥M := by
    intro hle
    apply hzV
    refine ⟨⟨z, hzM⟩, ?_, rfl⟩
    exact hle (mem_zpowers _)
  obtain ⟨y, hy1, hyodd, hyinv⟩ := CFSG.Quasithin.baer_suzuki_involution hX hnot
  have hz1 : (⟨z, hzM⟩ : ↥M) ≠ 1 := by
    intro h
    have h1 : z = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hinv : z * (y : X) * z⁻¹ = (y : X)⁻¹ :=
    congrArg Subtype.val (hyinv _ (mem_zpowers _) hz1)
  have hyo : orderOf (y : X) = orderOf y := Subgroup.orderOf_coe y
  have hyo1 : orderOf (y : X) ≠ 1 := by
    rw [hyo]
    intro h
    exact hy1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hyo1
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hyo] at hpd
    exact (Nat.not_even_iff_odd.mpr hyodd) (even_iff_two_dvd.mpr hpd)
  set x : X := (y : X) ^ (orderOf (y : X) / p) with hx
  have hxo : orderOf x = p := orderOf_pow_orderOf_div (orderOf_pos _).ne' hpd
  have hxinv : z * x * z⁻¹ = x⁻¹ := by
    rw [hx, ← conj_pow, hinv, inv_pow]
  have hxM : x ∈ M := pow_mem y.2 _
  have hWcard : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, hxo]
  have hWodd : Odd (Nat.card (zpowers x)) := by
    rw [hWcard]
    exact hp.odd_of_ne_two hp2
  have hWp : IsPGroup p (zpowers x) := IsPGroup.of_card (n := 1) (by rw [hWcard, pow_one])
  have hWM : zpowers x ≤ M := zpowers_le.mpr hxM
  have hzN : z ∈ normalizer (zpowers x : Set X) := by
    refine mem_normalizer_zpowers_of_conj_mem ?_ ?_
    · rw [hxinv]
      exact inv_mem (mem_zpowers x)
    · rw [show z⁻¹ * x * z = z * x * z⁻¹ by rw [hzi], hxinv]
      exact inv_mem (mem_zpowers x)
  rcases S.theorem4.2 z hz hzM (zpowers x) hWodd hWM hzN with h | h
  ·
    have hzx : z * x = x * z := h x (mem_zpowers x)
    have hxx : x⁻¹ = x := by
      rw [← hxinv, hzx, mul_assoc, mul_inv_cancel, mul_one]
    have hdvd : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [sq]; exact inv_eq_iff_mul_eq_one.mp hxx)
    rw [hxo] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  ·
    have hfix : omegaFix M (zpowers x : Set X) = {M} := by
      ext β
      rw [Set.mem_singleton_iff]
      refine ⟨h β, fun hβ => ?_⟩
      rw [hβ]
      exact S.prodDisc.mem_omegaFix_iff.mpr ⟨self_mem_omega M, hWM⟩
    have hmod : 2 ^ k + 1 ≡ 1 [MOD p] := by
      have h1 := ncard_omega_modEq_ncard_omegaFix (M := M) hp hWp
      rwa [hfix, Set.ncard_singleton, hΩ] at h1
    have hdvd : p ∣ 2 ^ k := by
      have h1 := (Nat.modEq_iff_dvd' (Nat.le_add_left 1 (2 ^ k))).mp hmod.symm
      rwa [Nat.add_sub_cancel] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

theorem ZDSetup.u_not_mem_oTwoIn (S : ZDSetup X Z M) (h172 : Lemma172Stmt Z M) (c : Conf16 Z M)
    {n i e : ℕ} (hB : BenderSub Z M (cenHull Z c.u) n i e) : c.u ∉ oTwoIn M := by
  obtain ⟨-, -, hc1, -⟩ := h172 c n i e hB
  have hnle : ¬ c.D ⊓ centralizer ({c.t * c.u} : Set X) ≤
      c.D ⊓ centralizer ({c.t, c.u} : Set X) :=
    fun hle => hc1 (Subgroup.relIndex_eq_one.mpr hle)
  obtain ⟨g, hg, hg'⟩ : ∃ g ∈ c.D ⊓ centralizer ({c.t * c.u} : Set X),
      g ∉ c.D ⊓ centralizer ({c.t, c.u} : Set X) := by
    by_contra hcon
    push Not at hcon
    exact hnle fun g hg => hcon g hg
  obtain ⟨hgD, hgw⟩ := mem_inf.mp hg
  have hgw' : g * (c.t * c.u) = (c.t * c.u) * g := mem_centralizer_singleton_iff.mp hgw
  have ht2 : c.t * c.t = 1 := S.conf_t_sq c
  have hti : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right ht2
  have htu : c.t * c.u = c.u * c.t := c.t_mul_u_comm
  have hut : c.u = c.t * (c.t * c.u) := by rw [← mul_assoc, ht2, one_mul]
  have hgt : g * c.t ≠ c.t * g := by
    intro hgt
    apply hg'
    refine mem_inf.mpr ⟨hgD, mem_centralizer_iff.mpr ?_⟩
    rintro h (rfl | rfl)
    · exact hgt.symm
    · rw [hut]
      calc c.t * (c.t * c.u) * g = c.t * ((c.t * c.u) * g) := by group
        _ = c.t * (g * (c.t * c.u)) := by rw [hgw']
        _ = (c.t * g) * (c.t * c.u) := by group
        _ = (g * c.t) * (c.t * c.u) := by rw [hgt]
        _ = g * (c.t * (c.t * c.u)) := by group
  have hZs := S.prodDisc.isZStarIn_inf_conjugate_sup S.invariant c.ht c.htM
  have hfK : g * c.t * g⁻¹ * c.t⁻¹ ∈ pPrimeCoreIn c.D :=
    commutator_mem_pPrimeCoreIn hZs (mem_normalizer_inf_conjugate ht2) hgD
  have hf1 : g * c.t * g⁻¹ * c.t⁻¹ ≠ 1 := by
    intro h
    apply hgt
    have h1 : g * c.t * g⁻¹ = c.t := mul_inv_eq_one.mp h
    calc g * c.t = g * c.t * g⁻¹ * g := by group
      _ = c.t * g := by rw [h1]
  have hfodd : Odd (orderOf (g * c.t * g⁻¹ * c.t⁻¹)) :=
    Odd.of_dvd_nat (odd_card_pPrimeCoreIn c.D) (Subgroup.orderOf_dvd_natCard _ hfK)
  have hwg : Commute (c.t * c.u) g := (Commute.symm hgw')
  have hwt : Commute (c.t * c.u) c.t := by
    change (c.t * c.u) * c.t = c.t * (c.t * c.u)
    calc (c.t * c.u) * c.t = c.t * (c.u * c.t) := mul_assoc _ _ _
      _ = c.t * (c.t * c.u) := by rw [← htu]
  have hwf : Commute (c.t * c.u) (g * c.t * g⁻¹ * c.t⁻¹) :=
    ((hwg.mul_right hwt).mul_right hwg.inv_right).mul_right hwt.inv_right
  have hufu : c.u * (g * c.t * g⁻¹ * c.t⁻¹) * c.u⁻¹ = (g * c.t * g⁻¹ * c.t⁻¹)⁻¹ := by
    calc c.u * (g * c.t * g⁻¹ * c.t⁻¹) * c.u⁻¹
        = c.t * ((c.t * c.u) * (g * c.t * g⁻¹ * c.t⁻¹) * (c.t * c.u)⁻¹) * c.t⁻¹ := by
          conv_lhs => rw [hut]
          group
      _ = c.t * (g * c.t * g⁻¹ * c.t⁻¹) * c.t⁻¹ := by rw [hwf.eq, mul_inv_cancel_right]
      _ = c.t * g * c.t * g⁻¹ * (c.t * c.t) := by rw [hti]; group
      _ = c.t * g * c.t * g⁻¹ := by rw [ht2, mul_one]
      _ = (g * c.t * g⁻¹ * c.t⁻¹)⁻¹ := by simp only [mul_inv_rev, inv_inv, hti, mul_assoc]
  intro huV
  have hfM : g * c.t * g⁻¹ * c.t⁻¹ ∈ M := (mem_inf.mp (pPrimeCoreIn_le c.D hfK)).1
  have h1 := mul_mem huV (oTwoIn_conj_mem M hfM (inv_mem huV))
  have e : c.u * ((g * c.t * g⁻¹ * c.t⁻¹) * c.u⁻¹ * (g * c.t * g⁻¹ * c.t⁻¹)⁻¹) =
      ((g * c.t * g⁻¹ * c.t⁻¹) * (g * c.t * g⁻¹ * c.t⁻¹))⁻¹ := by
    calc c.u * ((g * c.t * g⁻¹ * c.t⁻¹) * c.u⁻¹ * (g * c.t * g⁻¹ * c.t⁻¹)⁻¹)
        = (c.u * (g * c.t * g⁻¹ * c.t⁻¹) * c.u⁻¹) * (g * c.t * g⁻¹ * c.t⁻¹)⁻¹ := by group
      _ = ((g * c.t * g⁻¹ * c.t⁻¹) * (g * c.t * g⁻¹ * c.t⁻¹))⁻¹ := by rw [hufu]; group
  rw [e] at h1
  have h2 := mem_of_mul_self_mem_of_odd_orderOf hfodd (inv_mem_iff.mp h1)
  exact hf1 (eq_one_of_mem_oTwoIn_of_odd h2 hfodd)

theorem ZDSetup.oTwoIn_inf_D_eq_bot (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M) (c : Conf16 Z M)
    (huV : c.u ∉ oTwoIn M) : oTwoIn M ⊓ c.D = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  by_contra hx1
  obtain ⟨hxV, hxD⟩ := mem_inf.mp hx
  obtain ⟨k, hk⟩ := exists_pow_orderOf_eq_two_of_mem_oTwoIn hxV hx1
  obtain ⟨-, d, hd, hyd⟩ := S.exists_conj_of_involution_dGrp h166 c (pow_mem hxD k) hk
  apply huV
  have e : c.u = d * x ^ k * d⁻¹ := by
    rw [hyd]
    group
  rw [e]
  exact oTwoIn_conj_mem M (mem_inf.mp hd).1 (pow_mem hxV k)

theorem ZDSetup.mem_Z_of_mem_oTwoIn (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M) (c : Conf16 Z M)
    (huV : c.u ∉ oTwoIn M) {y : X} (hyV : y ∈ oTwoIn M) (hy2 : orderOf y = 2) : y ∈ Z := by
  obtain ⟨-, -, ⟨-, hcl⟩, -, -⟩ := h166 c
  rcases hcl y hy2 with h | h
  · exact S.invariant.isConj_mem c.hz h.symm
  · exfalso
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    have huM : c.u ∈ M := (mem_inf.mp c.hu).1
    have hpg : IsPGroup 2 (zpowers c.u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, c.hu2, pow_one])
    have hgM : g⁻¹⁻¹ * c.u * g⁻¹ ∈ M := by
      rw [inv_inv, hg]
      exact oTwoIn_le M hyV
    obtain ⟨m, hm, hmu⟩ := S.exists_mem_conj_of_isPGroup huM hpg hgM
    have e1 : y = m⁻¹ * c.u * m := by rw [hmu, inv_inv, hg]
    apply huV
    have e2 : c.u = m * y * m⁻¹ := by
      rw [e1]
      group
    rw [e2]
    exact oTwoIn_conj_mem M hm hyV

theorem ZDSetup.mem_invertedSet_of_inverted (S : ZDSetup X Z M) (c : Conf16 Z M) {a : X}
    (haD : a ∈ c.D) (hodd : Odd (orderOf a)) (hinv : c.t * a * c.t⁻¹ = a⁻¹) :
    a ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn c.D) c.t := by
  have hZs := S.prodDisc.isZStarIn_inf_conjugate_sup S.invariant c.ht c.htM
  have hcomm := commutator_mem_pPrimeCoreIn hZs (mem_normalizer_inf_conjugate (S.conf_t_sq c)) haD
  have h3 : c.t * a⁻¹ * c.t⁻¹ = a := by
    have := congrArg (fun y => y⁻¹) hinv
    simpa [mul_inv_rev, mul_assoc] using this
  have e : a * c.t * a⁻¹ * c.t⁻¹ = a * a := by
    calc a * c.t * a⁻¹ * c.t⁻¹ = a * (c.t * a⁻¹ * c.t⁻¹) := by group
      _ = a * a := by rw [h3]
  rw [e] at hcomm
  exact ⟨mem_of_mul_self_mem_of_odd_orderOf hodd hcomm, hinv⟩

omit [Finite X] in
theorem conj_commutatorElement_eq_inv {t g : X} (ht : t * t = 1) :
    t * ⁅t, g⁆ * t⁻¹ = ⁅t, g⁆⁻¹ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [commutatorElement_def, hti]
  calc t * (t * g * t * g⁻¹) * t = (t * t) * g * t * g⁻¹ * t := by group
    _ = g * t * g⁻¹ * t := by rw [ht, one_mul]
    _ = (t * g * t * g⁻¹)⁻¹ := by simp only [mul_inv_rev, inv_inv, hti, mul_assoc]

theorem ZDSetup.two_pow_le_card_invertedSet (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M)
    (c : Conf16 Z M) {n i e : ℕ} (hB : BenderSub Z M (cenHull Z c.u) n i e) {A : Subgroup X}
    (hAF : A ≤ cenHull Z c.u) (hA : Nat.card A = 2 ^ n - 1)
    (hAI : (A : Set X) ⊆ CFSG.OddInversion.invertedSet (pPrimeCoreIn c.D) c.t) :
    2 ^ n ≤ Nat.card (CFSG.OddInversion.invertedSet (pPrimeCoreIn c.D) c.t) := by
  by_contra hlt
  push Not at hlt
  have hle : (CFSG.OddInversion.invertedSet (pPrimeCoreIn c.D) c.t).ncard ≤ (A : Set X).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    have h1 : Nat.card ↥(A : Set X) = Nat.card A := rfl
    omega
  have heq : (A : Set X) = CFSG.OddInversion.invertedSet (pPrimeCoreIn c.D) c.t :=
    Set.eq_of_subset_of_ncard_le hAI hle (Set.toFinite _)
  have ht2 : c.t * c.t = 1 := S.conf_t_sq c
  have htK : c.t ∈ normalizer (pPrimeCoreIn c.D : Set X) :=
    mem_normalizer_pPrimeCoreIn (mem_normalizer_inf_conjugate ht2)
  have hK : ⁅zpowers c.t, pPrimeCoreIn c.D⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [← SetLike.mem_coe, heq]
    rcases Bender.eq_one_or_eq_of_mem_zpowers ht2 hg₁ with rfl | rfl
    · rw [commutatorElement_one_left]
      exact ⟨one_mem _, by simp⟩
    · refine ⟨?_, conj_commutatorElement_eq_inv ht2⟩
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp htK g₂).mp hg₂) (inv_mem hg₂)
  have hzC : c.z ∈ centralizer ({c.u} : Set X) := (mem_inf.mp (c.hT1.le c.hz_T1.1)).1
  have hzF : c.z ∈ cenHull Z c.u := subset_closure ⟨c.hz, hzC⟩
  have htF : c.t ∈ cenHull Z c.u := subset_closure ⟨c.ht, c.ht_B⟩
  have hL : lSubgroup M c.z c.t ≤ cenHull Z c.u := by
    unfold lSubgroup
    exact sup_le (sup_le (zpowers_le.mpr hzF) (zpowers_le.mpr htF)) (hK.trans hAF)
  rw [h121 c.t c.z c.ht c.htM c.hz c.hzM c.hD] at hL
  exact hB.ne_top (top_le_iff.mp hL)

theorem ZDSetup.zNum_add_one_le (S : ZDSetup X Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M)
    (hzV : z ∈ oTwoIn M) : zNum Z M + 1 ≤ Nat.card (oTwoIn M) := by
  have hsub : insert (1 : X) (Z ∩ (M : Set X)) ⊆ (oTwoIn M : Set X) := by
    rintro y (rfl | ⟨hyZ, hyM⟩)
    · exact one_mem _
    · obtain ⟨m, hm, hmy⟩ := S.prodDisc.exists_conj_mem S.invariant hz hzM hyZ hyM
      rw [← hmy]
      have h1 := oTwoIn_conj_mem M (M.inv_mem hm) hzV
      rwa [inv_inv] at h1
  have h1 : (1 : X) ∉ Z ∩ (M : Set X) := fun h => by
    have h2 := S.invariant.1 1 h.1
    rw [orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem h1 (Set.toFinite _)] at h2
  unfold zNum
  rw [Nat.card_coe_set_eq]
  calc (Z ∩ (M : Set X)).ncard + 1 ≤ (oTwoIn M : Set X).ncard := h2
    _ = Nat.card (oTwoIn M) := (Nat.card_coe_set_eq _).symm

theorem ZDSetup.prop176
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M) (h166 : Cor166Stmt Z M)
    (h172 : Lemma172Stmt Z M) (h175 : Lemma175Stmt Z M) : Prop176Stmt Z M := by
  intro c n e hB
  have hΩ : (omega M).ncard = 2 ^ (2 * n) + 1 := by
    rw [h175 c n e hB, ← pow_mul, mul_comm]
  have hcardM := S.card_eq_ncard_omega_sub_one_mul c.htM
  rw [hΩ, Nat.add_sub_cancel] at hcardM
  have hzV : c.z ∈ oTwoIn M := S.mem_oTwoIn_of_ncard_omega hΩ c.hz c.hzM
  have huV : c.u ∉ oTwoIn M := S.u_not_mem_oTwoIn h172 c hB
  have hinf : oTwoIn M ⊓ c.D = ⊥ := S.oTwoIn_inf_D_eq_bot h166 c huV
  obtain ⟨hn2, A, hAD, hAcard, hAinv⟩ := S.exists_torus c hB
  have hqodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hAI : (A : Set X) ⊆ CFSG.OddInversion.invertedSet (pPrimeCoreIn c.D) c.t := fun a ha =>
    S.mem_invertedSet_of_inverted c (mem_inf.mp (hAD ha)).1
      (Odd.of_dvd_nat (hAcard ▸ hqodd) (Subgroup.orderOf_dvd_natCard A ha)) (hAinv a ha)
  have hfree : ∀ a ∈ A, ∀ v ∈ oTwoIn M, a * v = v * a → a = 1 ∨ v = 1 := by
    intro a ha v hv hav
    by_cases hv1 : v = 1
    · exact Or.inr hv1
    · left
      obtain ⟨k, hk⟩ := exists_pow_orderOf_eq_two_of_mem_oTwoIn hv hv1
      have hyV := pow_mem hv k
      exact (S.prodDisc.prop36c S.invariant c.ht c.htM).2 (v ^ k)
        ⟨S.mem_Z_of_mem_oTwoIn h166 c huV hyV hk, oTwoIn_le M hyV⟩ a (hAI ha)
        (Commute.pow_right hav k).eq
  have hAV : ∀ a ∈ A, ∀ v ∈ oTwoIn M, a * v * a⁻¹ ∈ oTwoIn M := fun a ha v hv =>
    oTwoIn_conj_mem M (mem_inf.mp (mem_inf.mp (hAD ha)).1).1 hv
  have hdvd := card_dvd_card_sub_one_of_semiregular hAV hfree
  rw [hAcard] at hdvd
  have hIcard := S.two_pow_le_card_invertedSet h121 c hB (hAD.trans inf_le_right) hAcard hAI
  rw [(S.prodDisc.prop36d S.invariant c.ht c.htM c.hz c.hzM).1] at hIcard
  have hlow := S.zNum_add_one_le c.hz c.hzM hzV
  have hsupM : oTwoIn M ⊔ c.D ≤ M := sup_le (oTwoIn_le M) inf_le_left
  have hup := (card_mul_card_le_card_sup hinf).trans (Subgroup.card_le_of_le hsupM)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_oTwoIn M)
  have hDpos : 0 < Nat.card c.D := Nat.card_pos
  have hk1 : n < k := by
    have h1 : 2 ^ n < 2 ^ k := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
  have hk2 : k ≤ 2 * n := by
    have h1 : 2 ^ k * Nat.card c.D ≤ 2 ^ (2 * n) * Nat.card c.D := by
      rw [← hk, ← hcardM]
      exact hup
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h1 hDpos)
  have hk3 : k = 2 * n := eq_two_mul_of_two_pow_sub_one_dvd hk1 hk2 (hk ▸ hdvd)
  refine ⟨?_, hinf⟩
  apply Subgroup.eq_of_le_of_card_ge hsupM
  rw [hcardM, ← hk3, ← hk]
  exact card_mul_card_le_card_sup hinf

theorem ZDSetup.false_of_stmts_prop176
    (S : ZDSetup X Z M)
    (hconf : ∀ _ : Ctx16 Z M, Nonempty (Conf16 Z M)) (h121 : Thm121Stmt Z M)
    (h163 : Lemma163Stmt Z M) (h166 : Cor166Stmt Z M) (h172 : Lemma172Stmt Z M)
    (h173 : Lemma173Stmt Z M) (h174 : Lemma174Stmt Z M) (h175 : Lemma175Stmt Z M) : False :=
  S.false_of_stmts hconf h163 h166 h173 h174 (S.prop176 h121 h166 h172 h175)

end CFSG.GH74.Uniqueness

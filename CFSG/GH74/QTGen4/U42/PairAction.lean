module

public import CFSG.GH74.QTGen4.U42.PairActionThree
public import CFSG.GH74.QTGen4.U42.PairExtB
public import CFSG.GH74.QTGen4.U42.PairExtC
public import CFSG.GH74.QTGen4.U42.CentralExtB

public section

namespace CFSG.GH74.QTGen4.U42

variable {G : Type*} [Group G] {H B T U : Subgroup G}

theorem nuHom_on_U (h : PairCore H B T U) (e : ↥U ≃* U0) (u : ↥U) :
    nuHom h.U_normal e (Subgroup.inclusion (h.U_le_T.trans (h.T_le_B.trans h.B_le_H)) u) =
      MulAut.conj (e u) := by
  apply MulEquiv.ext
  intro y
  change e (conjOn h.U_normal _ (e.symm y)) = e u * y * (e u)⁻¹
  have hk : conjOn h.U_normal
      (Subgroup.inclusion (h.U_le_T.trans (h.T_le_B.trans h.B_le_H)) u) (e.symm y) =
      u * e.symm y * u⁻¹ := Subtype.ext rfl
  rw [hk, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem zH_mem_center (h : PairCore H B T U) (e : ↥U ≃* U0) :
    zH h e ∈ Subgroup.center ↥H := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  have hfix := U0AutC.alpha_zc (nu h.U_normal e x)
  change e (conjOn h.U_normal x (e.symm zc)) = zc at hfix
  have hu : conjOn h.U_normal x (e.symm zc) = e.symm zc := by
    apply e.injective
    rw [hfix, MulEquiv.apply_symm_apply]
  have hv := congrArg Subtype.val hu
  exact mul_inv_eq_iff_eq_mul.mp hv

theorem zH_orderOf (h : PairCore H B T U) (e : ↥U ≃* U0) : orderOf (zH h e) = 2 := by
  have hpow : (e.symm zc) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    simpa only [pow_two] using U0AutC.zc_sq
  have hs : (zH h e) ^ 2 = 1 := by
    let j : ↥U →* ↥H := Subgroup.inclusion (h.U_le_T.trans (h.T_le_B.trans h.B_le_H))
    change (j (e.symm zc)) ^ 2 = 1
    rw [← map_pow, hpow, map_one]
  have hn : zH h e ≠ 1 := by
    intro hz
    have hu : e.symm zc = 1 := Subtype.ext (congrArg (fun x : ↥H => (x : G)) hz)
    have hv := congrArg e hu
    rw [MulEquiv.apply_symm_apply, map_one] at hv
    exact U0AutC.zc_ne_one hv
  exact orderOf_eq_prime hs hn

theorem nuHom_ker_sq (h : PairCore H B T U) (e : ↥U ≃* U0) (x : ↥H)
    (hx : nuHom h.U_normal e x = 1) : x ^ 2 = 1 := by
  exact sq_eq_one_of_mem_zpowers (zH h e) (zH_orderOf h e) x
    ((nu_eq_one_iff_mem_zpowers h h.U_normal e x).mp hx)

theorem nuHom_mem_inner_iff (h : PairCore H B T U) (e : ↥U ≃* U0) (x : ↥H) :
    nuHom h.U_normal e x ∈ U0AutC.Inn0 ↔ (x : G) ∈ U := by
  let j : ↥U →* ↥H := Subgroup.inclusion (h.U_le_T.trans (h.T_le_B.trans h.B_le_H))
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := (U0AutC.mem_Inn0_iff _).mp hx
    have hu : nuHom h.U_normal e (j (e.symm v)) = MulAut.conj v := by
      rw [nuHom_on_U h e, MulEquiv.apply_symm_apply]
    have hk : nu h.U_normal e (x * (j (e.symm v))⁻¹) = 1 := by
      change nuHom h.U_normal e (x * (j (e.symm v))⁻¹) = 1
      rw [map_mul, map_inv, hu, hv, mul_inv_cancel]
    have hxu : ((x * (j (e.symm v))⁻¹ : ↥H) : G) ∈ U :=
      h.centralizes _ (x * (j (e.symm v))⁻¹).2 ((nu_eq_one_iff h.U_normal e _).mp hk)
    have hm := U.mul_mem hxu (e.symm v).2
    change (x : G) * ((e.symm v : ↥U) : G)⁻¹ * ((e.symm v : ↥U) : G) ∈ U at hm
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm
  · intro hx
    apply (U0AutC.mem_Inn0_iff _).mpr
    refine ⟨e ⟨(x : G), hx⟩, ?_⟩
    exact (nuHom_on_U h e ⟨(x : G), hx⟩).symm

theorem card_map_nine_of_ker_sq {K L : Type*} [Group K] [Group L] [Finite K]
    (f : K →* L) (hker : ∀ x : K, f x = 1 → x ^ 2 = 1)
    (P : Subgroup K) (hP : Nat.card P = 9) : Nat.card (P.map f) = 9 := by
  let j : ↥P →* ↥(P.map f) :=
    { toFun := fun x => ⟨f x, ⟨x, x.2, rfl⟩⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun x y => Subtype.ext (f.map_mul x y) }
  have hinj : Function.Injective j := by
    intro x y hxy
    have hf : f ((x : K) * (y : K)⁻¹) = 1 := by
      have he : f (x : K) = f (y : K) := congrArg Subtype.val hxy
      rw [map_mul, map_inv, he, mul_inv_cancel]
    have h2 : (x * y⁻¹) ^ 2 = 1 := Subtype.ext (hker _ hf)
    have h9 : (x * y⁻¹) ^ 9 = 1 := by
      have hh := pow_card_eq_one' (G := ↥P) (x := x * y⁻¹)
      rwa [hP] at hh
    have hr : (x * y⁻¹) ^ 9 = x * y⁻¹ := by
      rw [show 9 = 2 * 4 + 1 by decide, pow_succ, pow_mul, h2, one_pow, one_mul]
    exact mul_inv_eq_one.mp (hr.symm.trans h9)
  have hsurj : Function.Surjective j := by
    rintro ⟨y, x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact (Nat.card_congr (MulEquiv.ofBijective j ⟨hinj, hsurj⟩).toEquiv).symm.trans hP

theorem exists_pair_action_three [Finite G] (h : PairCore H B T U) (e : ↥U ≃* U0) :
    ∃ P : Subgroup ↥H, Nat.card P = 9 ∧
      Nat.card (P.map (nuHom h.U_normal e)) = 9 ∧ P ⊔ T.subgroupOf H = ⊤ := by
  have hTH : T ≤ H := h.T_le_B.trans h.B_le_H
  have hc : Nat.card (T.subgroupOf H) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.T_two
  obtain ⟨P, hP, hPT⟩ := exists_card_nine_sup_eq_top (T.subgroupOf H) n (hc.trans hn)
    (by rw [hc]; exact h.card_eq)
  exact ⟨P, hP, card_map_nine_of_ker_sq (nuHom h.U_normal e) (nuHom_ker_sq h e) P hP, hPT⟩

theorem inner_le_map_T (h : PairCore H B T U) (e : ↥U ≃* U0) :
    U0AutC.Inn0 ≤ (T.subgroupOf H).map (nuHom h.U_normal e) := by
  intro a ha
  obtain ⟨u, rfl⟩ := (U0AutC.mem_Inn0_iff _).mp ha
  refine ⟨Subgroup.inclusion (h.U_le_T.trans (h.T_le_B.trans h.B_le_H)) (e.symm u), ?_, ?_⟩
  · exact h.U_le_T (e.symm u).2
  · rw [nuHom_on_U h e, MulEquiv.apply_symm_apply]

theorem exists_pair_normal_three [Finite G] (h : PairCore H B T U) (e : ↥U ≃* U0) :
    ∃ N : Subgroup ↥H, N.Normal ∧ U.subgroupOf H ≤ N ∧ N ⊔ B.subgroupOf H = ⊤ ∧
      ∀ x ∈ N, ((x : ↥H) : G) ^ 3 ∈ U := by
  obtain ⟨P, hP, hPa, hPT⟩ := exists_pair_action_three h e
  let f := nuHom h.U_normal e
  let N : Subgroup ↥H := (P.map f ⊔ U0AutC.Inn0).comap f
  have hN : N.Normal := three_part_comap_normal f (P.map f) hPa
  have hPN : P ≤ N := by
    intro x hx
    change f x ∈ P.map f ⊔ U0AutC.Inn0
    exact (le_sup_left : P.map f ≤ P.map f ⊔ U0AutC.Inn0) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hUN : U.subgroupOf H ≤ N := by
    intro x hx
    change f x ∈ P.map f ⊔ U0AutC.Inn0
    exact (le_sup_right : U0AutC.Inn0 ≤ P.map f ⊔ U0AutC.Inn0) ((nuHom_mem_inner_iff h e x).mpr hx)
  have hBN : N ⊔ B.subgroupOf H = ⊤ := by
    apply le_antisymm le_top
    rw [← hPT]
    exact sup_le (hPN.trans le_sup_left)
      ((show T.subgroupOf H ≤ B.subgroupOf H from fun _ hx => h.T_le_B hx).trans le_sup_right)
  refine ⟨N, hN, hUN, hBN, ?_⟩
  intro x hx
  have hc : f (x ^ 3) ∈ U0AutC.Inn0 := three_part_comap_cube f (P.map f) hPa x hx
  exact (nuHom_mem_inner_iff h e (x ^ 3)).mp hc

end CFSG.GH74.QTGen4.U42

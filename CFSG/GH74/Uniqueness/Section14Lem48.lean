module

public import CFSG.GH74.Uniqueness.Section14Lem48Aux
public import CFSG.GH74.Uniqueness.Section14Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

namespace Sec148

section Derived

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {t : X} {n r : ℕ}
  {L K J Mo P U T S2 : Subgroup X}

omit [Finite X] in
theorem U_comm_L (F : Facts14 Z M t n r L K J Mo P U T S2) {u l : X} (hu : u ∈ U)
    (hl : l ∈ L) : u * l = l * u := by
  have h := F.U_le_J hu
  rw [F.J_eq, Subgroup.mem_centralizer_iff] at h
  exact (h l hl).symm

omit [Finite X] in
theorem U_comm (F : Facts14 Z M t n r L K J Mo P U T S2) : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a :=
  comm_of_mul_self_eq_one F.U_sq

omit [Finite X] in
theorem Mo_le_T (F : Facts14 Z M t n r L K J Mo P U T S2) : Mo ≤ T := by
  rw [F.T_eq]
  exact F.Mo_le_P.trans le_sup_left

omit [Finite X] in
theorem U_le_T (F : Facts14 Z M t n r L K J Mo P U T S2) : U ≤ T := by
  rw [F.T_eq]
  exact le_sup_right

omit [Finite X] in
theorem P_le_T (F : Facts14 Z M t n r L K J Mo P U T S2) : P ≤ T := by
  rw [F.T_eq]
  exact le_sup_left

omit [Finite X] in
theorem mem_T (F : Facts14 Z M t n r L K J Mo P U T S2) {x : X} (hx : x ∈ T) :
    ∃ p ∈ P, ∃ u ∈ U, x = p * u := by
  rw [F.T_eq] at hx
  exact exists_mul_of_mem_sup (fun p hp u hu => (U_comm_L F hu (F.P_le_L hp)).symm) hx

omit [Finite X] in
theorem Mo_inf_U (F : Facts14 Z M t n r L K J Mo P U T S2) : Mo ⊓ U = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ L ⊓ J := ⟨F.P_le_L (F.Mo_le_P hx.1), F.U_le_J hx.2⟩
  rw [F.L_inf_J] at h1
  exact h1

omit [Finite X] in
theorem exists_ne_one_of_U (F : Facts14 Z M t n r L K J Mo P U T S2) : ∃ u ∈ U, u ≠ 1 := by
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp F.U_ne_bot
  exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩

omit [Finite X] in
theorem T_le_centralizer (F : Facts14 Z M t n r L K J Mo P U T S2) :
    T ≤ centralizer ((Mo ⊔ U : Subgroup X) : Set X) := by
  intro x hx
  obtain ⟨p, hp, u₁, hu₁, rfl⟩ := mem_T F hx
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hle : Mo ⊔ U ≤ centralizer ({p * u₁} : Set X) := by
    refine sup_le (fun m hm => ?_) (fun u hu => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : p * m = m * p := F.Mo_central p hp m hm
      have h2 : u₁ * m = m * u₁ := U_comm_L F hu₁ (F.P_le_L (F.Mo_le_P hm))
      calc m * (p * u₁) = (m * p) * u₁ := by rw [mul_assoc]
        _ = (p * m) * u₁ := by rw [h1]
        _ = p * (m * u₁) := by rw [mul_assoc]
        _ = p * (u₁ * m) := by rw [h2]
        _ = p * u₁ * m := by rw [mul_assoc]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : u * p = p * u := U_comm_L F hu (F.P_le_L hp)
      have h2 : u * u₁ = u₁ * u := U_comm F u hu u₁ hu₁
      calc u * (p * u₁) = (u * p) * u₁ := by rw [mul_assoc]
        _ = (p * u) * u₁ := by rw [h1]
        _ = p * (u * u₁) := by rw [mul_assoc]
        _ = p * (u₁ * u) := by rw [h2]
        _ = p * u₁ * u := by rw [mul_assoc]
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

omit [Finite X] in
theorem centralizer_le_T (F : Facts14 Z M t n r L K J Mo P U T S2) :
    centralizer ((Mo ⊔ U : Subgroup X) : Set X) ≤ T := by
  intro x hx
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_U F
  have h1 : x ∈ centralizer (Mo : Set X) :=
    centralizer_le (fun m hm => (le_sup_left : Mo ≤ Mo ⊔ U) hm) hx
  have h2 : x ∈ centralizer ({u} : Set X) :=
    centralizer_le (fun v hv => by
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact (le_sup_right : U ≤ Mo ⊔ U) hu) hx
  rw [← F.cent_Mo_u u hu hu1]
  exact ⟨h1, h2⟩

omit [Finite X] in
theorem centralizer_sup_eq (F : Facts14 Z M t n r L K J Mo P U T S2) :
    centralizer ((Mo ⊔ U : Subgroup X) : Set X) = T :=
  le_antisymm (centralizer_le_T F) (T_le_centralizer F)

omit [Finite X] in
theorem mem_sup_of_mul_self_eq_one (F : Facts14 Z M t n r L K J Mo P U T S2) {x : X} (hx : x ∈ T)
    (hx2 : x * x = 1) : x ∈ Mo ⊔ U := by
  obtain ⟨p, hp, u, hu, rfl⟩ := mem_T F hx
  have hpu : p * u = u * p := (U_comm_L F hu (F.P_le_L hp)).symm
  have hpp : p * p = 1 := by
    have e : p * u * (p * u) = p * p * (u * u) := by
      calc p * u * (p * u) = p * (u * p) * u := by group
        _ = p * (p * u) * u := by rw [← hpu]
        _ = p * p * (u * u) := by group
    rw [e, F.U_sq u hu, mul_one] at hx2
    exact hx2
  have hpMo : p ∈ Mo := by
    by_contra hnot
    exact F.P_sq_ne p hp hnot hpp
  exact Subgroup.mul_mem_sup hpMo hu

omit [Finite X] in
theorem D_norm_J (F : Facts14 Z M t n r L K J Mo P U T S2) {d : X} (hd : d ∈ dGrp M t) {j : X}
    (hj : j ∈ J) : d * j * d⁻¹ ∈ J := by
  have hdL : d ∈ normalizer (L : Set X) := F.D_norm_L hd
  rw [F.J_eq, Subgroup.mem_centralizer_iff] at hj ⊢
  intro l hl
  have hl' : d⁻¹ * l * d ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hdL) l).mp hl
    simpa using this
  have h := hj _ hl'
  calc l * (d * j * d⁻¹) = d * ((d⁻¹ * l * d) * j) * d⁻¹ := by group
    _ = d * (j * (d⁻¹ * l * d)) * d⁻¹ := by rw [h]
    _ = d * j * d⁻¹ * l := by group

theorem D_norm_U (F : Facts14 Z M t n r L K J Mo P U T S2) (hU2 : 2 < Nat.card U) {d : X}
    (hd : d ∈ dGrp M t) {u : X} (hu : u ∈ U) : d * u * d⁻¹ ∈ U := by
  refine mem_of_normal_sylow F.U_sylow_J (F.big_U hU2) (D_norm_J F hd (F.U_le_J hu)) (k := 1) ?_
  have h := F.U_sq u hu
  rw [pow_one, sq]
  calc d * u * d⁻¹ * (d * u * d⁻¹) = d * (u * u) * d⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem D_le_normalizer_U (F : Facts14 Z M t n r L K J Mo P U T S2) (hU2 : 2 < Nat.card U) :
    dGrp M t ≤ normalizer (U : Set X) := fun d hd =>
  mem_normalizer_of_forall (fun x hx => D_norm_U F hU2 hd hx)
    (fun x hx => by simpa using D_norm_U F hU2 (inv_mem hd) hx)

theorem D_le_normalizer_T (F : Facts14 Z M t n r L K J Mo P U T S2) (hU2 : 2 < Nat.card U) :
    dGrp M t ≤ normalizer (T : Set X) := by
  have key : ∀ d ∈ dGrp M t, ∀ x ∈ T, d * x * d⁻¹ ∈ T := by
    intro d hd x hx
    obtain ⟨p, hp, u, hu, rfl⟩ := mem_T F hx
    have e : d * (p * u) * d⁻¹ = (d * p * d⁻¹) * (d * u * d⁻¹) := by group
    rw [e]
    refine T.mul_mem (P_le_T F ?_) (U_le_T F (D_norm_U F hU2 hd hu))
    exact (Subgroup.mem_normalizer_iff.mp (F.D_norm_P hd) p).mp hp
  intro d hd
  exact mem_normalizer_of_forall (key d hd)
    (fun x hx => by simpa using key d⁻¹ (inv_mem hd) x hx)

theorem two_lt_card_U (F : Facts14 Z M t n r L K J Mo P U T S2) (hne : Nat.card U ≠ 2) :
    2 < Nat.card U := by
  obtain ⟨k, hk⟩ := F.U_sylow_J.isPGroup.exists_card_eq
  have h1 : Nat.card U ≠ 1 := fun h => F.U_ne_bot (Subgroup.card_eq_one.mp h)
  rcases k with _ | _ | k
  · rw [pow_zero] at hk
    exact absurd hk h1
  · rw [pow_one] at hk
    exact absurd hk hne
  · rw [hk]
    have : 2 ^ (k + 2) = 2 ^ k * 4 := by ring
    have := Nat.one_le_two_pow (n := k)
    omega

theorem exists_prime_elt (F : Facts14 Z M t n r L K J Mo P U T S2) :
    ∃ y ∈ J, (orderOf y).Prime ∧ orderOf y ∣ 2 ^ n - 1 := by
  obtain ⟨p, hp, hpJ, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp F.coprime_J
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) p hpJ
  refine ⟨y, y.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hy]
    exact hp
  · rw [Subgroup.orderOf_coe, hy]
    exact hpq

theorem exists_A (F : Facts14 Z M t n r L K J Mo P U T S2) (h147 : Concl147 n K J Mo U T S2)
    (hU2 : 2 < Nat.card U) :
    ∃ A : Subgroup X, A ≤ S2 ∧ A ⊓ T = ⊥ ∧ Nat.card A = 2 ^ n ∧ (∀ a ∈ A, a * a = 1) ∧
      K ≤ normalizer (A : Set X) := by
  obtain ⟨y, hyJ, hyp, hyd⟩ := exists_prime_elt F
  refine h147.complement y hyJ hyp hyd ?_
  exact mem_normalizer_of_forall (fun x hx => F.big_U hU2 y hyJ x hx)
    (fun x hx => by simpa using F.big_U hU2 y⁻¹ (inv_mem hyJ) x hx)

theorem exists_ne_one_of_card (F : Facts14 Z M t n r L K J Mo P U T S2) {A : Subgroup X}
    (hAcard : Nat.card A = 2 ^ n) : ∃ a ∈ A, a ≠ 1 := by
  have h1 : 1 < Nat.card A := by
    rw [hAcard]
    exact Nat.one_lt_two_pow (by have := F.three_le; omega)
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot A).mp h1)
  exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩

omit [Finite X] in
theorem centralizer_le_normalizer_L (F : Facts14 Z M t n r L K J Mo P U T S2) {u : X} (hu : u ∈ U)
    (hu1 : u ≠ 1) : centralizer ({u} : Set X) ≤ normalizer (L : Set X) := by
  have h1 : zpowers u ≤ J := Subgroup.zpowers_le.mpr (F.U_le_J hu)
  have h2 : zpowers u ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.mp h)
  refine le_trans ?_ (F.NY_le (zpowers u) h1 h2)
  have e : centralizer ({u} : Set X) = centralizer ((zpowers u : Subgroup X) : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [e]
  exact centralizer_le_normalizer _

omit [Finite X] in
theorem T_le_centralizer_u (F : Facts14 Z M t n r L K J Mo P U T S2) {u : X} (hu : u ∈ U)
    (hu1 : u ≠ 1) : T ≤ centralizer ({u} : Set X) := by
  intro x hx
  rw [← F.cent_Mo_u u hu hu1] at hx
  exact hx.2

omit [Finite X] in
theorem Mo_comm_S2 (h146 : Concl146 M t n K Mo U T S2) {a : X} (ha : a ∈ S2) :
    ∀ m ∈ Mo, m * a = a * m := fun m hm =>
  Subgroup.mem_centralizer_iff.mp (h146.S2_le_C0 ha) m hm

theorem exists_g (F : Facts14 Z M t n r L K J Mo P U T S2) (h146 : Concl146 M t n K Mo U T S2)
    {A : Subgroup X} (hAS : A ≤ S2) (hAT : A ⊓ T = ⊥) (hAsq : ∀ a ∈ A, a * a = 1) {a : X}
    (haA : a ∈ A) (ha1 : a ≠ 1) :
    ∃ g : X, g * a * g⁻¹ ∈ U ∧ ∀ w ∈ Mo ⊔ A, g * w * g⁻¹ ∈ Mo ⊔ U := by
  have haM : a ∈ M := h146.S2_le_M (hAS haA)
  have haMo : a ∉ Mo := fun h => ha1 (by
    have h' : a ∈ A ⊓ T := ⟨haA, Mo_le_T F h⟩
    rwa [hAT, Subgroup.mem_bot] at h')
  have haZ : a ∉ Z := fun h => haMo ((F.zM a haM).mp h).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hAsq a haA) ha1
  obtain ⟨g₀, hg₀⟩ := F.conj_U a hord haZ
  have hu1 : g₀ * a * g₀⁻¹ ≠ 1 := by
    intro h
    apply ha1
    have e : a = g₀⁻¹ * (g₀ * a * g₀⁻¹) * g₀ := by group
    rw [e, h]
    group
  have hcomm : ∀ m ∈ Mo, ∀ a' ∈ A, m * a' = a' * m := fun m hm a' ha' =>
    Mo_comm_S2 h146 (hAS ha') m hm
  have hWsq : ∀ w ∈ Mo ⊔ A, w * w = 1 := mul_self_eq_one_of_mem_sup F.Mo_sq hAsq hcomm
  have hWcomm := comm_of_mul_self_eq_one hWsq
  have hTsyl : ABGLocalTools.IsSylowOf 2 T (centralizer ({g₀ * a * g₀⁻¹} : Set X)) :=
    F.T_sylow.of_le (T_le_centralizer_u F hg₀ hu1) (centralizer_le_normalizer_L F hg₀ hu1)
  have hQmem : ∀ x ∈ (Mo ⊔ A).map (MulAut.conj g₀).toMonoidHom,
      ∃ w ∈ Mo ⊔ A, x = g₀ * w * g₀⁻¹ := by
    rintro x ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  have hQC : (Mo ⊔ A).map (MulAut.conj g₀).toMonoidHom ≤
      centralizer ({g₀ * a * g₀⁻¹} : Set X) := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hQmem x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hWcomm w hw a ((le_sup_right : A ≤ Mo ⊔ A) haA)
    calc g₀ * w * g₀⁻¹ * (g₀ * a * g₀⁻¹) = g₀ * (w * a) * g₀⁻¹ := by group
      _ = g₀ * (a * w) * g₀⁻¹ := by rw [h]
      _ = g₀ * a * g₀⁻¹ * (g₀ * w * g₀⁻¹) := by group
  have hQp : IsPGroup 2 ((Mo ⊔ A).map (MulAut.conj g₀).toMonoidHom) :=
    isPGroup_two_of_mul_self_eq_one (fun x hx => by
      obtain ⟨w, hw, rfl⟩ := hQmem x hx
      calc g₀ * w * g₀⁻¹ * (g₀ * w * g₀⁻¹) = g₀ * (w * w) * g₀⁻¹ := by group
        _ = 1 := by rw [hWsq w hw]; group)
  obtain ⟨c, hcC, hcQ⟩ := exists_conj_le_of_isSylowOf hQC hQp hTsyl
  refine ⟨c * g₀, ?_, fun w hw => ?_⟩
  · have hc := Subgroup.mem_centralizer_singleton_iff.mp hcC
    have e : c * g₀ * a * (c * g₀)⁻¹ = c * (g₀ * a * g₀⁻¹) * c⁻¹ := by group
    have e2 : c * (g₀ * a * g₀⁻¹) * c⁻¹ = g₀ * a * g₀⁻¹ := by rw [hc]; group
    rw [e, e2]
    exact hg₀
  · have h1 := hcQ _ ⟨w, hw, rfl⟩
    have e : c * g₀ * w * (c * g₀)⁻¹ = c * (g₀ * w * g₀⁻¹) * c⁻¹ := by group
    rw [e]
    refine mem_sup_of_mul_self_eq_one F h1 ?_
    calc c * (g₀ * w * g₀⁻¹) * c⁻¹ * (c * (g₀ * w * g₀⁻¹) * c⁻¹)
        = c * (g₀ * (w * w) * g₀⁻¹) * c⁻¹ := by group
      _ = 1 := by rw [hWsq w hw]; group

theorem exists_eq_conj (F : Facts14 Z M t n r L K J Mo P U T S2)
    (h146 : Concl146 M t n K Mo U T S2) {A : Subgroup X} (hAS : A ≤ S2) (hAT : A ⊓ T = ⊥)
    (hAcard : Nat.card A = 2 ^ n) {g : X} (hg : ∀ w ∈ Mo ⊔ A, g * w * g⁻¹ ∈ Mo ⊔ U) :
    ∀ x ∈ Mo ⊔ U, ∃ w ∈ Mo ⊔ A, x = g * w * g⁻¹ := by
  have hAMo : A ≤ normalizer (Mo : Set X) := fun a ha =>
    centralizer_le_normalizer _ (h146.S2_le_C0 (hAS ha))
  have hUMo : U ≤ normalizer (Mo : Set X) := by
    intro u hu
    refine centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact (U_comm_L F hu (F.P_le_L (F.Mo_le_P hm))).symm
  have h1 : Nat.card (Mo ⊔ A : Subgroup X) = 2 ^ n * 2 ^ n := by
    have h := card_sup_mul_card_inf' hAMo
    have hbot : Mo ⊓ A = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ A ⊓ T := ⟨hx.2, Mo_le_T F hx.1⟩
      rw [hAT] at this
      exact this
    rw [hbot, Subgroup.card_bot, mul_one, F.card_Mo, hAcard, sup_comm] at h
    exact h
  have h2 : Nat.card (Mo ⊔ U : Subgroup X) ≤ 2 ^ n * 2 ^ n := by
    have h := card_sup_mul_card_inf' hUMo
    rw [Mo_inf_U F, Subgroup.card_bot, mul_one, F.card_Mo, sup_comm] at h
    rw [h]
    exact Nat.mul_le_mul_left _ F.card_U_le
  have hQle : (Mo ⊔ A).map (MulAut.conj g).toMonoidHom ≤ Mo ⊔ U := by
    rintro x ⟨w, hw, rfl⟩
    exact hg w hw
  have hQcard : Nat.card ((Mo ⊔ A).map (MulAut.conj g).toMonoidHom) = 2 ^ n * 2 ^ n := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h1]
  have hEq : (Mo ⊔ A).map (MulAut.conj g).toMonoidHom = Mo ⊔ U :=
    Subgroup.eq_of_le_of_card_ge hQle (by rw [hQcard]; exact h2)
  intro x hx
  rw [← hEq] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact ⟨w, hw, rfl⟩

omit [Finite X] in
theorem K_le_M (F : Facts14 Z M t n r L K J Mo P U T S2) : K ≤ M := by
  rw [F.K_eq]
  exact inf_le_left.trans inf_le_left

omit [Finite X] in
theorem K_norm_W (F : Facts14 Z M t n r L K J Mo P U T S2) {A : Subgroup X}
    (hKA : K ≤ normalizer (A : Set X)) (hcomm : ∀ m ∈ Mo, ∀ a ∈ A, m * a = a * m) {k : X}
    (hk : k ∈ K) {w : X} (hw : w ∈ Mo ⊔ A) : k * w * k⁻¹ ∈ Mo ⊔ A := by
  obtain ⟨m, hm, a, ha, rfl⟩ := exists_mul_of_mem_sup hcomm hw
  have e : k * (m * a) * k⁻¹ = (k * m * k⁻¹) * (k * a * k⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem_sup (F.Mo_normal k (K_le_M F hk) m hm)
    ((Subgroup.mem_normalizer_iff.mp (hKA hk) a).mp ha)

omit [Finite X] in
theorem mem_normalizer_T (F : Facts14 Z M t n r L K J Mo P U T S2) {c : X}
    (h1 : ∀ w ∈ Mo ⊔ U, c * w * c⁻¹ ∈ Mo ⊔ U) (h2 : ∀ w ∈ Mo ⊔ U, c⁻¹ * w * c ∈ Mo ⊔ U) :
    c ∈ normalizer (T : Set X) := by
  have key : ∀ c : X, (∀ w ∈ Mo ⊔ U, c⁻¹ * w * c ∈ Mo ⊔ U) → ∀ x ∈ T, c * x * c⁻¹ ∈ T := by
    intro c hc x hx
    rw [← centralizer_sup_eq F, Subgroup.mem_centralizer_iff]
    intro w hw
    have hxc := Subgroup.mem_centralizer_iff.mp (T_le_centralizer F hx) (c⁻¹ * w * c) (hc w hw)
    calc w * (c * x * c⁻¹) = c * ((c⁻¹ * w * c) * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * w * c)) * c⁻¹ := by rw [hxc]
      _ = c * x * c⁻¹ * w := by group
  refine mem_normalizer_of_forall (key c h2) (fun x hx => ?_)
  have := key c⁻¹ (fun w hw => by simpa using h1 w hw) x hx
  simpa using this

omit [Finite X] in
theorem conj_mem_normalizer_T (F : Facts14 Z M t n r L K J Mo P U T S2) {A : Subgroup X}
    (hKA : K ≤ normalizer (A : Set X)) (hcomm : ∀ m ∈ Mo, ∀ a ∈ A, m * a = a * m) {g : X}
    (hg : ∀ w ∈ Mo ⊔ A, g * w * g⁻¹ ∈ Mo ⊔ U)
    (hW : ∀ x ∈ Mo ⊔ U, ∃ w ∈ Mo ⊔ A, x = g * w * g⁻¹) :
    ∀ k ∈ K, g * k * g⁻¹ ∈ normalizer (T : Set X) := by
  have key : ∀ k ∈ K, ∀ x ∈ Mo ⊔ U, g * k * g⁻¹ * x * (g * k * g⁻¹)⁻¹ ∈ Mo ⊔ U := by
    intro k hk x hx
    obtain ⟨w, hw, rfl⟩ := hW x hx
    have e : g * k * g⁻¹ * (g * w * g⁻¹) * (g * k * g⁻¹)⁻¹ = g * (k * w * k⁻¹) * g⁻¹ := by
      group
    rw [e]
    exact hg _ (K_norm_W F hKA hcomm hk hw)
  intro k hk
  refine mem_normalizer_T F (fun w hw => key k hk w hw) (fun w hw => ?_)
  have h := key k⁻¹ (K.inv_mem hk) w hw
  have e : g * k⁻¹ * g⁻¹ = (g * k * g⁻¹)⁻¹ := by group
  rw [e] at h
  simpa using h

theorem exists_s (F : Facts14 Z M t n r L K J Mo P U T S2) (h146 : Concl146 M t n K Mo U T S2)
    (hU2 : 2 < Nat.card U) {g : X} (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ normalizer (T : Set X)) :
    ∃ s ∈ S2, ∀ k ∈ K, s * (g * k * g⁻¹) * s⁻¹ ∈ dGrp M t := by
  have hBN : K.map (MulAut.conj g).toMonoidHom ≤ normalizer (T : Set X) := by
    rintro _ ⟨k, hk, rfl⟩
    exact hg k hk
  have hBodd : Odd (Nat.card (K.map (MulAut.conj g).toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, F.K_card]
    have h3 := F.three_le
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have : 0 < 2 ^ (n - 1) := by positivity
    exact ⟨2 ^ (n - 1) - 1, by omega⟩
  have hrel : Odd (U.relIndex (dGrp M t)) := by
    obtain ⟨-, -, hdvd⟩ := (ABGLocalTools.isSylowOf_iff (p := 2)).mp F.U_sylow_D
    rw [Nat.odd_iff]
    omega
  obtain ⟨s, hs, hsB⟩ := exists_conj_into_of_normal_two_sylow F.S2_sylow.le h146.normal
    F.S2_sylow.isPGroup (D_le_normalizer_T F hU2)
    (fun g hg => by
      obtain ⟨s, hs, d, hd, -, e⟩ := h146.normalizer_T g hg
      exact ⟨s, hs, d, hd, e⟩)
    ((U_le_T F).trans F.T_le_S2) F.U_sylow_D.le (D_le_normalizer_U F hU2)
    F.U_sylow_D.isPGroup hrel hBN hBodd
  exact ⟨s, hs, fun k hk => hsB _ ⟨k, hk, rfl⟩⟩

theorem U_le_sup (F : Facts14 Z M t n r L K J Mo P U T S2) (h146 : Concl146 M t n K Mo U T S2)
    (hU2 : 2 < Nat.card U) {A : Subgroup X} {g s : X} (hs : s ∈ S2)
    (hW : ∀ x ∈ Mo ⊔ U, ∃ w ∈ Mo ⊔ A, x = g * w * g⁻¹)
    (hsK : ∀ k ∈ K, s * (g * k * g⁻¹) * s⁻¹ ∈ dGrp M t) : ∀ u ∈ U, u ∈ Mo ⊔ A := by
  have hKD : K ≤ conjugate (dGrp M t) (s * g) := by
    intro k hk
    rw [mem_conjugate_iff]
    have e : s * g * k * (s * g)⁻¹ = s * (g * k * g⁻¹) * s⁻¹ := by group
    rw [e]
    exact hsK k hk
  have hcD := F.conj_D (s * g) hKD
  intro u hu
  have huD : u ∈ dGrp M t := F.U_sylow_D.le hu
  have h1 : s * g * u * (s * g)⁻¹ ∈ dGrp M t := by
    have : u ∈ conjugate (dGrp M t) (s * g) := by
      rw [hcD]
      exact huD
    exact mem_conjugate_iff.mp this
  have h2 : s * g * u * (s * g)⁻¹ ∈ U := by
    refine mem_of_normal_sylow F.U_sylow_D (fun d hd v hv => D_norm_U F hU2 hd hv) h1 (k := 1) ?_
    have h := F.U_sq u hu
    rw [pow_one, sq]
    calc s * g * u * (s * g)⁻¹ * (s * g * u * (s * g)⁻¹) = s * g * (u * u) * (s * g)⁻¹ := by group
      _ = 1 := by rw [h]; group
  have h3 : g * u * g⁻¹ = (s⁻¹ * (s * g * u * (s * g)⁻¹) * s * (s * g * u * (s * g)⁻¹)⁻¹) *
      (s * g * u * (s * g)⁻¹) := by group
  have h4 : s⁻¹ * (s * g * u * (s * g)⁻¹) * s * (s * g * u * (s * g)⁻¹)⁻¹ ∈ Mo := by
    have := h146.quot_center s⁻¹ (inv_mem hs) _ ((le_sup_right : U ≤ Mo ⊔ U) h2)
    simpa using this
  have h5 : g * u * g⁻¹ ∈ Mo ⊔ U := by
    rw [h3]
    exact Subgroup.mul_mem_sup h4 h2
  obtain ⟨w, hw, hgw⟩ := hW _ h5
  have : u = w := by simpa using hgw
  rw [this]
  exact hw

omit [Finite X] in
theorem false_of_U_le (F : Facts14 Z M t n r L K J Mo P U T S2) {A : Subgroup X}
    (hAT : A ⊓ T = ⊥) (hcomm : ∀ m ∈ Mo, ∀ a ∈ A, m * a = a * m)
    (h : ∀ u ∈ U, u ∈ Mo ⊔ A) : False := by
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_U F
  obtain ⟨m, hm, a, ha, rfl⟩ := exists_mul_of_mem_sup hcomm (h u hu)
  have haT : a ∈ T := by
    have e : a = m⁻¹ * (m * a) := by group
    rw [e]
    exact T.mul_mem (T.inv_mem (Mo_le_T F hm)) (U_le_T F hu)
  have ha1 : a = 1 := by
    have : a ∈ A ⊓ T := ⟨ha, haT⟩
    rw [hAT, Subgroup.mem_bot] at this
    exact this
  rw [ha1, mul_one] at hu hu1
  have hmU : m ∈ Mo ⊓ U := ⟨hm, hu⟩
  rw [Mo_inf_U F, Subgroup.mem_bot] at hmU
  exact hu1 hmU

end Derived

end Sec148

theorem lemma148 {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {t : X}
    {n r : ℕ} {L K J Mo P U T S2 : Subgroup X} (F : Facts14 Z M t n r L K J Mo P U T S2)
    (h146 : Concl146 M t n K Mo U T S2) (h147 : Concl147 n K J Mo U T S2) :
    Nat.card U = 2 := by
  by_contra hne
  have hU2 := Sec148.two_lt_card_U F hne
  obtain ⟨A, hAS, hAT, hAcard, hAsq, hKA⟩ := Sec148.exists_A F h147 hU2
  obtain ⟨a, haA, ha1⟩ := Sec148.exists_ne_one_of_card F hAcard
  obtain ⟨g, -, hgW⟩ := Sec148.exists_g F h146 hAS hAT hAsq haA ha1
  have hW := Sec148.exists_eq_conj F h146 hAS hAT hAcard hgW
  have hcomm : ∀ m ∈ Mo, ∀ a ∈ A, m * a = a * m := fun m hm a ha =>
    Sec148.Mo_comm_S2 h146 (hAS ha) m hm
  have hKg := Sec148.conj_mem_normalizer_T F hKA hcomm hgW hW
  obtain ⟨s, hs, hsK⟩ := Sec148.exists_s F h146 hU2 hKg
  exact Sec148.false_of_U_le F hAT hcomm (Sec148.U_le_sup F h146 hU2 hs hW hsK)

end CFSG.GH74.Uniqueness

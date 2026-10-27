module

public import CFSG.LocalAnalysis.EvenBN.GMS.LocalSetup

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

section General

variable {H : Type*} [Group H]

theorem le_normalizer_of_conj_mem {N K : Subgroup H}
    (hK : ∀ y ∈ N, ∀ k ∈ K, y * k * y⁻¹ ∈ K) : N ≤ normalizer (K : Set H) := fun y hy =>
  mem_normalizer_iff.mpr fun k => ⟨hK y hy k, fun hk => by
    have h1 := hK y⁻¹ (inv_mem hy) _ hk
    rwa [inv_inv, show y⁻¹ * (y * k * y⁻¹) * y = k by group] at h1⟩

theorem mem_or_exists_mul_of_mem_sup_zpowers {K : Subgroup H} {t x : H} (htt : t * t = 1)
    (htK : t ∈ normalizer (K : Set H)) (hx : x ∈ K ⊔ zpowers t) :
    x ∈ K ∨ ∃ k ∈ K, x = k * t := by
  have hle : zpowers t ≤ normalizer (K : Set H) := zpowers_le.mpr htK
  have hx' : x ∈ ((K ⊔ zpowers t : Subgroup H) : Set H) := hx
  rw [coe_mul_of_right_le_normalizer_left K _ hle] at hx'
  obtain ⟨k, hk, z, hz, hkz⟩ := hx'
  have hkz' : x = k * z := hkz.symm
  subst hkz'
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact htt
  obtain ⟨i, rfl | rfl⟩ := Int.even_or_odd' j
  · left
    rw [zpow_mul, ht2, one_zpow, mul_one]
    exact hk
  · right
    exact ⟨k, hk, by rw [zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]⟩

theorem exists_isSylowOf_le {p : ℕ} [Fact p.Prime] {E K : Subgroup H} (hEK : E ≤ K)
    (hE : IsPGroup p E) : ∃ P : Subgroup H, IsSylowOf p P K ∧ E ≤ P := by
  have hE' : IsPGroup p (E.subgroupOf K) := hE.of_equiv (subgroupOfEquivOfLe hEK).symm
  obtain ⟨P, hP⟩ := hE'.exists_le_sylow
  exact ⟨(P : Subgroup K).map K.subtype, ⟨P, rfl⟩, fun x hx => ⟨⟨x, hEK hx⟩, hP hx, rfl⟩⟩

variable [Finite H]

theorem card_le_two_mul_of_mul_mem {X K : Subgroup H}
    (hmul : ∀ a ∈ X, ∀ b ∈ X, a ∉ K → b ∉ K → a * b ∈ K) :
    Nat.card X ≤ 2 * Nat.card (X ⊓ K : Subgroup H) := by
  classical
  by_cases hXK : X ≤ K
  · rw [inf_eq_left.mpr hXK]
    omega
  obtain ⟨a, haX, haK⟩ := IsConcreteLE.not_le_iff_exists.mp hXK
  let F : X → Bool × (X ⊓ K : Subgroup H) := fun x =>
    if hx : (x : H) ∈ K then (true, ⟨x, mem_inf.mpr ⟨x.2, hx⟩⟩)
    else (false, ⟨a * x, mem_inf.mpr ⟨mul_mem haX x.2, hmul a haX x x.2 haK hx⟩⟩)
  have hF : Function.Injective F := by
    intro x y hxy
    by_cases hx : (x : H) ∈ K <;> by_cases hy : (y : H) ∈ K <;>
      simp only [F, hx, hy, dite_true, dite_false, Prod.mk.injEq] at hxy
    · exact Subtype.ext (congrArg (fun z : (X ⊓ K : Subgroup H) => (z : H)) hxy.2)
    · exact absurd hxy.1 (by decide)
    · exact absurd hxy.1 (by decide)
    · exact Subtype.ext (mul_left_cancel (congrArg (fun z : (X ⊓ K : Subgroup H) => (z : H))
        hxy.2))
  have h1 := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1

end General

namespace LocalSetting

variable {H : Type*} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H} {n : ℕ}

section Commutator

variable (h : LocalSetting A t U V D n)
include h

theorem V_comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.isElementaryAbelian_V.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem V_mul_self : ∀ v ∈ V, v * v = 1 := fun v hv => by
  have := h.isElementaryAbelian_V
  rw [← sq]
  exact elemPow_eq_one_of_isElementaryAbelian v hv

theorem t_conj_mem : ∀ v ∈ V, t * v * t ∈ V := fun v hv => by
  have h1 := (mem_normalizer_iff.mp h.t_mem_normalizer_V v).mp hv
  rwa [h.t_inv] at h1

theorem comm_mem : ∀ v ∈ V, v * t * v⁻¹ * t ∈ U := fun v hv => by
  rw [← h.closure_commutator]
  refine subset_closure ⟨v⁻¹, inv_mem hv, ?_⟩
  rw [inv_inv, h.t_inv]
  group

theorem comm_mul : ∀ a ∈ V, ∀ b ∈ V,
    a * b * t * (a * b)⁻¹ * t = (a * t * a⁻¹ * t) * (b * t * b⁻¹ * t) := by
  intro a ha b hb
  have ha' : t * a⁻¹ * t ∈ V := h.t_conj_mem _ (inv_mem ha)
  have hb' : t * b⁻¹ * t ∈ V := h.t_conj_mem _ (inv_mem hb)
  have htt := h.t_mul_t
  have e1 : a * b * t * (a * b)⁻¹ * t = a * ((b * (t * b⁻¹ * t)) * (t * a⁻¹ * t)) := by
    have e0 : t * b⁻¹ * t * (t * a⁻¹ * t) = t * b⁻¹ * (t * t) * a⁻¹ * t := by group
    calc a * b * t * (a * b)⁻¹ * t = a * (b * (t * b⁻¹ * (t * t) * a⁻¹ * t)) := by
          rw [htt]; group
      _ = a * (b * (t * b⁻¹ * t * (t * a⁻¹ * t))) := by rw [e0]
      _ = a * ((b * (t * b⁻¹ * t)) * (t * a⁻¹ * t)) := by group
  have e2 : (a * t * a⁻¹ * t) * (b * t * b⁻¹ * t) =
      a * ((t * a⁻¹ * t) * (b * (t * b⁻¹ * t))) := by group
  rw [e1, e2, h.V_comm _ (mul_mem hb hb') _ ha']

theorem comm_eq_one_iff : ∀ v ∈ V, v * t * v⁻¹ * t = 1 ↔ v ∈ U := by
  intro v hv
  rw [← h.V_inf_centralizer, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · intro h1
    refine ⟨hv, ?_⟩
    have h2 : v * t * v⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h.t_inv] at h2
    calc v * t = v * t * v⁻¹ * v := by group
      _ = t * v := by rw [h2]
  · rintro ⟨-, h1⟩
    rw [h1, mul_inv_cancel_right, h.t_mul_t]

theorem exists_comm_eq : ∀ u ∈ U, ∃ v ∈ V, v * t * v⁻¹ * t = u := by
  let φ : V →* H :=
    { toFun := fun v => v * t * (v : H)⁻¹ * t
      map_one' := by simp [h.t_mul_t]
      map_mul' := fun a b => h.comm_mul a a.2 b b.2 }
  have hle : U ≤ φ.range := by
    rw [← h.closure_commutator, closure_le]
    rintro x ⟨w, hw, rfl⟩
    refine ⟨⟨w⁻¹, inv_mem hw⟩, ?_⟩
    change w⁻¹ * t * w⁻¹⁻¹ * t = w⁻¹ * (t⁻¹ * w * t)
    rw [inv_inv, h.t_inv]
    group
  intro u hu
  obtain ⟨v, hv⟩ := hle hu
  exact ⟨v, v.2, hv⟩

theorem exists_conj_V : ∀ u ∈ U, ∃ v ∈ V, v⁻¹ * t * v = t * u := by
  intro u hu
  obtain ⟨v, hv, hvu⟩ := h.exists_comm_eq u hu
  refine ⟨v⁻¹, inv_mem hv, ?_⟩
  rw [inv_inv, ← hvu, ← h.t_mul_comm _ (h.comm_mem v hv)]
  calc v * t * v⁻¹ = v * t * v⁻¹ * (t * t) := by rw [h.t_mul_t, mul_one]
    _ = v * t * v⁻¹ * t * t := by group

end Commutator

section ElementaryAbelian

variable (h : LocalSetting A t U V D n)
include h

theorem card_B_le : Nat.card (U ⊔ zpowers t : Subgroup H) ≤ 2 * 2 ^ n := by
  have htN : t ∈ normalizer (U : Set H) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun u hu => h.t_mul_comm u hu)
  have h1 := card_le_two_mul_of_mul_mem (X := U ⊔ zpowers t) (K := U) fun a ha b hb haU hbU => by
    rcases mem_or_exists_mul_of_mem_sup_zpowers h.t_mul_t htN ha with ha' | ⟨u, hu, rfl⟩
    · exact absurd ha' haU
    rcases mem_or_exists_mul_of_mem_sup_zpowers h.t_mul_t htN hb with hb' | ⟨w, hw, rfl⟩
    · exact absurd hb' hbU
    rw [show u * t * (w * t) = u * (t * w) * t by group, ← h.t_mul_comm w hw,
      show u * (w * t) * t = u * w * (t * t) by group, h.t_mul_t, mul_one]
    exact mul_mem hu hw
  rw [inf_eq_right.mpr le_sup_left, h.card_U] at h1
  exact h1

theorem card_B_inf_centralizer_le (p : H) :
    Nat.card ((U ⊔ zpowers t) ⊓ centralizer ({p} : Set H) : Subgroup H) ≤
      2 * Nat.card (U ⊓ centralizer ({p} : Set H) : Subgroup H) := by
  have htN : t ∈ normalizer (U : Set H) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun u hu => h.t_mul_comm u hu)
  have h1 := card_le_two_mul_of_mul_mem (X := (U ⊔ zpowers t) ⊓ centralizer ({p} : Set H))
    (K := U) fun a ha b hb haU hbU => by
    rcases mem_or_exists_mul_of_mem_sup_zpowers h.t_mul_t htN (mem_inf.mp ha).1 with
      ha' | ⟨u, hu, rfl⟩
    · exact absurd ha' haU
    rcases mem_or_exists_mul_of_mem_sup_zpowers h.t_mul_t htN (mem_inf.mp hb).1 with
      hb' | ⟨w, hw, rfl⟩
    · exact absurd hb' hbU
    rw [show u * t * (w * t) = u * (t * w) * t by group, ← h.t_mul_comm w hw,
      show u * (w * t) * t = u * w * (t * t) by group, h.t_mul_t, mul_one]
    exact mul_mem hu hw
  have h2 : (U ⊔ zpowers t) ⊓ centralizer ({p} : Set H) ⊓ U = U ⊓ centralizer ({p} : Set H) := by
    rw [inf_comm, ← inf_assoc, inf_eq_left.mpr (le_sup_left : U ≤ U ⊔ zpowers t)]
  rw [h2] at h1
  exact h1

theorem inv_mul_mem_of_mul_self_mem {T : Subgroup H}
    (hT : IsSylowOf 2 T (centralizer ({t} : Set H))) (hUT : U ≤ T) {p p' : H} (hp : p ∈ T)
    (hp' : p' ∈ T) (hpB : p ∉ U ⊔ zpowers t) (hp'B : p' ∉ U ⊔ zpowers t)
    (hp2 : p * p ∈ U ⊔ zpowers t) (hp'2 : p' * p' ∈ U ⊔ zpowers t) :
    p⁻¹ * p' ∈ U ⊔ zpowers t := by
  have := h.B_normal hT hUT
  obtain ⟨hcyc, -⟩ := h.isCyclic_quotient hT hUT
  set N := (U ⊔ zpowers t).subgroupOf T
  have hmk : ∀ x : T, (QuotientGroup.mk x : T ⧸ N) = 1 ↔ (x : H) ∈ U ⊔ zpowers t := fun x => by
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hord : ∀ x : T, (x : H) * x ∈ U ⊔ zpowers t → (x : H) ∉ U ⊔ zpowers t →
      orderOf (QuotientGroup.mk x : T ⧸ N) = 2 := by
    intro x hx2 hxB
    refine orderOf_eq_prime ?_ (fun h1 => hxB ((hmk x).mp h1))
    rw [← QuotientGroup.mk_pow, sq, hmk]
    exact hx2
  have heq := eq_of_orderOf_eq_two_of_isCyclic_subgroup (X := (⊤ : Subgroup (T ⧸ N)))
    (Subgroup.isCyclic_of_le le_top) (mem_top _) (mem_top _)
    (hord ⟨p, hp⟩ hp2 hpB) (hord ⟨p', hp'⟩ hp'2 hp'B)
  rw [QuotientGroup.eq, mem_subgroupOf] at heq
  simpa using heq

theorem card_lt_of_le_T {T E : Subgroup H} (hT : IsSylowOf 2 T (centralizer ({t} : Set H)))
    (hUT : U ≤ T) (hET : E ≤ T) (hE : IsElementaryAbelian 2 E) :
    Nat.card E < (2 ^ n) ^ 2 := by
  have hq := h.four_le
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by
    have := hE
    rw [← sq]
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases hEB : E ≤ U ⊔ zpowers t
  · have h1 : Nat.card E ≤ Nat.card (U ⊔ zpowers t : Subgroup H) := card_le_of_le hEB
    have h2 := h.card_B_le
    calc Nat.card E ≤ 2 * 2 ^ n := h1.trans h2
      _ < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ = (2 ^ n) ^ 2 := (sq _).symm
  obtain ⟨p, hpE, hpB⟩ := IsConcreteLE.not_le_iff_exists.mp hEB
  have hmul : ∀ a ∈ E, ∀ b ∈ E, a ∉ U ⊔ zpowers t → b ∉ U ⊔ zpowers t →
      a * b ∈ U ⊔ zpowers t := by
    intro a ha b hb haB hbB
    have heq := h.inv_mul_mem_of_mul_self_mem hT hUT (hET ha) (hET hb) haB hbB
      (by rw [hE2 a ha]; exact one_mem _) (by rw [hE2 b hb]; exact one_mem _)
    have h1 : a * b = a⁻¹ * b := by rw [inv_eq_of_mul_eq_one_right (hE2 a ha)]
    rw [h1]
    exact heq
  have h1 := card_le_two_mul_of_mul_mem hmul
  have h2 : Nat.card (E ⊓ (U ⊔ zpowers t) : Subgroup H) ≤
      Nat.card ((U ⊔ zpowers t) ⊓ centralizer ({p} : Set H) : Subgroup H) :=
    card_le_of_le fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2,
      mem_centralizer_singleton_iff.mpr (hEc x (mem_inf.mp hx).1 p hpE)⟩
  have h3 := h.card_B_inf_centralizer_le p
  have h4 := h.card_inf_centralizer_sq_le hT hUT (hET hpE) hpB
  set c := Nat.card (U ⊓ centralizer ({p} : Set H) : Subgroup H)
  have h5 : Nat.card E ≤ 4 * c := by omega
  have h6 : Nat.card E ^ 2 ≤ 16 * 2 ^ n :=
    calc Nat.card E ^ 2 ≤ (4 * c) ^ 2 := Nat.pow_le_pow_left h5 2
      _ = 16 * c ^ 2 := by ring
      _ ≤ 16 * 2 ^ n := Nat.mul_le_mul_left _ h4
  have h7 : 16 * 2 ^ n < ((2 ^ n) ^ 2) ^ 2 := by
    have h8 : 16 ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul hq hq
    calc 16 * 2 ^ n < 2 ^ n * 2 ^ n * 2 ^ n * 2 ^ n := by nlinarith
      _ = ((2 ^ n) ^ 2) ^ 2 := by ring
  exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp (h6.trans_lt h7)

theorem card_lt_of_le_centralizer {E : Subgroup H} (hEC : E ≤ centralizer ({t} : Set H))
    (hE : IsElementaryAbelian 2 E) : Nat.card E < (2 ^ n) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hUT⟩ := h.exists_isSylowOf
  obtain ⟨P, hP, hEP⟩ := exists_isSylowOf_le hEC (@IsElementaryAbelian.isPGroup 2 E _ hE)
  obtain ⟨k, -, hk⟩ := hT.exists_mem_conj hP
  have := hE
  set E' := E.map (MulAut.conj k⁻¹).toMonoidHom
  have hE' : IsElementaryAbelian 2 E' := IsElementaryAbelian.map _
  have hE'T : E' ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := (hk x).mp (hEP hx)
    simpa using h1
  have hcard : Nat.card E' = Nat.card E :=
    card_map_of_injective (MulAut.conj k⁻¹).injective
  rw [← hcard]
  exact h.card_lt_of_le_T hT hUT hE'T hE'

theorem not_conjugate_le_centralizer (g : H) :
    ¬ CFSG.conjugate V g ≤ centralizer ({t} : Set H) := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.isElementaryAbelian_V
  have hel : IsElementaryAbelian 2 (CFSG.conjugate V g) := IsElementaryAbelian.map _
  have hcard : Nat.card (CFSG.conjugate V g) = Nat.card V :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have h1 := h.card_lt_of_le_centralizer hle hel
  rw [hcard, h.card_V] at h1
  exact lt_irrefl _ h1

theorem conj_not_mem_V (g : H) : g⁻¹ * t * g ∉ V := by
  intro hv
  apply h.not_conjugate_le_centralizer g⁻¹
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_centralizer_singleton_iff]
  change (MulAut.conj g⁻¹⁻¹) w * t = t * (MulAut.conj g⁻¹⁻¹) w
  rw [inv_inv, MulAut.conj_apply]
  have h1 := h.V_comm _ hv w hw
  calc g * w * g⁻¹ * t = g * (w * (g⁻¹ * t * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * t * g) * w) * g⁻¹ := by rw [h1]
    _ = t * (g * w * g⁻¹) := by group

theorem exists_eq_mul_of_conj_mem (g : H) (hg : g⁻¹ * t * g ∈ U ⊔ zpowers t) :
    ∃ u ∈ U, g⁻¹ * t * g = t * u := by
  have htN : t ∈ normalizer (U : Set H) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun u hu => h.t_mul_comm u hu)
  rcases mem_or_exists_mul_of_mem_sup_zpowers h.t_mul_t htN hg with hU | ⟨u, hu, hut⟩
  · exact absurd (h.U_le_V hU) (h.conj_not_mem_V g)
  · exact ⟨u, hu, by rw [hut, h.t_mul_comm u hu]⟩

theorem conj_not_mem_U (g : H) : g⁻¹ * t * g ∉ U := fun hU => h.conj_not_mem_V g (h.U_le_V hU)

theorem isStronglyClosedIn_U : CFSG.IsStronglyClosedIn (U ⊔ zpowers t) (U : Set H) := by
  have htN : t ∈ normalizer (U : Set H) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun u hu => h.t_mul_comm u hu)
  refine ⟨fun u hu => mem_sup_left hu, fun u hu g hg => ?_⟩
  rcases mem_or_exists_mul_of_mem_sup_zpowers h.t_mul_t htN hg with hU | ⟨u', hu', hut⟩
  · exact hU
  exfalso
  obtain ⟨v, -, hv⟩ := h.exists_conj_V u' hu'
  apply h.conj_not_mem_U (v * g⁻¹)
  have h1 : g⁻¹ * u * g = v⁻¹ * t * v := by rw [hut, hv, h.t_mul_comm u' hu']
  have h2 : (v * g⁻¹)⁻¹ * t * (v * g⁻¹) = u :=
    calc (v * g⁻¹)⁻¹ * t * (v * g⁻¹) = g * (v⁻¹ * t * v) * g⁻¹ := by group
      _ = g * (g⁻¹ * u * g) * g⁻¹ := by rw [h1]
      _ = u := by group
  rw [h2]
  exact hu

theorem normalizer_B_le : normalizer ((U ⊔ zpowers t : Subgroup H) : Set H) ≤
    normalizer (U : Set H) := by
  refine le_normalizer_of_conj_mem fun x hx u hu => ?_
  have h1 := (mem_normalizer_iff.mp hx u).mp (mem_sup_left hu)
  have h2 := h.isStronglyClosedIn_U.2 u hu x⁻¹
  rw [inv_inv] at h2
  exact h2 h1

theorem exists_conj_t_eq {x : H} (hx : x ∈ normalizer ((U ⊔ zpowers t : Subgroup H) : Set H)) :
    ∃ c ∈ U, x * t * x⁻¹ = t * c := by
  have h1 := (mem_normalizer_iff.mp hx t).mp (mem_sup_right (mem_zpowers t))
  have h2 := h.exists_eq_mul_of_conj_mem x⁻¹ (by rwa [inv_inv])
  rwa [inv_inv] at h2

end ElementaryAbelian

end LocalSetting

end CFSG.LocalAnalysis.EvenBN.GMS

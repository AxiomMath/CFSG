module

public import CFSG.GF2Type.CenterFour.CaseAClasses

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

private theorem oneClass_mem_conj_iff {H : Subgroup G} {g y : G} :
    y ∈ CFSG.conjugate H g ↔ g * y * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem oneClass_mem_centerAt_conj (z g t : G) :
    t ∈ centerAt (g⁻¹ * z * g) ↔ g * t * g⁻¹ ∈ centerAt z := by
  rw [centerAt_conj z g]
  exact oneClass_mem_conj_iff

private theorem oneClass_pow_four {a t : G} {n : ℕ} (hCa : Config a n) (ht : t ∈ centerAt a) :
    t ^ 4 = 1 := by
  obtain ⟨k, hZk, hk4, -⟩ := hCa.exists_generator
  rw [hZk] at ht
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have h4 : k ^ 4 = 1 := by
    rw [← hk4]
    exact pow_orderOf_eq_one k
  rw [← zpow_natCast, ← zpow_mul, mul_comm m, zpow_mul, zpow_natCast, h4, one_zpow]

private theorem oneClass_comm_centerAt {a u x : G} {n : ℕ} (hCa : Config a n)
    (hu : u ∈ centerAt a) (hx : x ∈ coreAt a) : u * x = x * u :=
  Subgroup.mem_centralizer_iff.mp (hCa.core_le_centralizer_center hx) u hu

private theorem oneClass_config_of_fused {z a : G} {n : ℕ} (hC : Config z n) (ha : Fused z a) :
    Config a n := by
  obtain ⟨g, rfl⟩ := ha
  exact hC.conj g

private theorem oneClass_mem_core_of_comm {z a x : G} {n : ℕ} (hC : Config z n) (hA : CaseA z)
    (ha : Fused z a) (hx : Fused z x) (hcomm : x * a = a * x) : x ∈ coreAt a := by
  obtain ⟨g, rfl⟩ := ha
  exact CaseA.mem_core (hC.conj g) (CaseA.conj hC hA g)
    ((Fused.symm (fused_conj z g)).trans hx) (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)

private theorem oneClass_centerAt_le {z a : G} {n : ℕ} (hC : Config z n) (ha : Fused z a)
    (haQ : a ∈ coreAt z) : centerAt a ≤ centralizer ({z} : Set G) := by
  obtain ⟨g, rfl⟩ := ha
  rw [centerAt_conj z g]
  exact (hC.center_le_iff g).mpr haQ

private theorem oneClass_inf_centerAt_eq_bot {a b : G} {n : ℕ} (hCa : Config a n)
    (hab : Fused a b) (hne : b ≠ a) : centerAt a ⊓ centerAt b = ⊥ := by
  obtain ⟨h, rfl⟩ := hab
  rw [centerAt_conj a h]
  by_contra hbot
  exact hne (hCa.eq_of_inf_conj_ne_bot h hbot)

private theorem oneClass_centerAt_comm {z a u x : G} {n : ℕ} (hC : Config z n) (hA : CaseA z)
    (hall : ∀ a x : G, Fused z a → a ∈ coreAt z → a ≠ z → Fused z x → x ∈ coreAt z → x ≠ z →
      a * x = x * a)
    (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z) (hu : u ∈ centerAt a)
    (hx : Fused z x) (hxQ : x ∈ coreAt z) (hxz : x ≠ z) : u * x = x * u :=
  oneClass_comm_centerAt (oneClass_config_of_fused hC ha) hu
    (oneClass_mem_core_of_comm hC hA ha hx (hall a x ha haQ haz hx hxQ hxz).symm)

private theorem oneClass_conj_mem_centerAt {z a x u y : G} {n : ℕ} (hC : Config z n) (hA : CaseA z)
    (hall : ∀ a x : G, Fused z a → a ∈ coreAt z → a ≠ z → Fused z x → x ∈ coreAt z → x ≠ z →
      a * x = x * a)
    (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z) (hu : u ∈ centerAt a)
    (hx : Fused z x) (hxQ : x ∈ coreAt z) (hxz : x ≠ z) (hy : y ∈ centerAt x) :
    u * y * u⁻¹ ∈ centerAt x := by
  have hux : u ∈ normalizer (centerAt x : Set G) := by
    rw [(oneClass_config_of_fused hC hx).normalizer_center]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (oneClass_centerAt_comm hC hA hall ha haQ haz hu hx hxQ hxz)
  exact (Subgroup.mem_normalizer_iff.mp hux y).mp hy

private theorem oneClass_comm_of_mem_centerAt {z a b u v : G} {n : ℕ} (hC : Config z n)
    (hA : CaseA z)
    (hall : ∀ a x : G, Fused z a → a ∈ coreAt z → a ≠ z → Fused z x → x ∈ coreAt z → x ≠ z →
      a * x = x * a)
    (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z)
    (hb : Fused z b) (hbQ : b ∈ coreAt z) (hbz : b ≠ z)
    (hu : u ∈ centerAt a) (hv : v ∈ centerAt b) : u * v = v * u := by
  by_cases hab : a = b
  · subst hab
    exact (oneClass_comm_centerAt (oneClass_config_of_fused hC hb) hv
      ((oneClass_config_of_fused hC hb).center_le_core hu)).symm
  · have hTI : centerAt a ⊓ centerAt b = ⊥ :=
      oneClass_inf_centerAt_eq_bot (oneClass_config_of_fused hC ha) ((Fused.symm ha).trans hb)
        (fun h => hab h.symm)
    have h1 : u * v * u⁻¹ ∈ centerAt b :=
      oneClass_conj_mem_centerAt hC hA hall ha haQ haz hu hb hbQ hbz hv
    have h2 : v * u * v⁻¹ ∈ centerAt a :=
      oneClass_conj_mem_centerAt hC hA hall hb hbQ hbz hv ha haQ haz hu
    have hcB : u * v * u⁻¹ * v⁻¹ ∈ centerAt b := mul_mem h1 (inv_mem hv)
    have hcA : u * v * u⁻¹ * v⁻¹ ∈ centerAt a := by
      have e : u * v * u⁻¹ * v⁻¹ = (v * u * v⁻¹ * u⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem (mul_mem h2 (inv_mem hu))
    have hmem := Subgroup.mem_inf.mpr ⟨hcA, hcB⟩
    rw [hTI, Subgroup.mem_bot] at hmem
    calc u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by group
      _ = v * u := by rw [hmem, one_mul]

private def oneClassT (z : G) : Set G :=
  {t | ∃ a : G, (Fused z a ∧ a ∈ coreAt z ∧ a ≠ z) ∧ t ∈ centerAt a}

private theorem oneClass_closure_comm {T : Set G} (hT : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) :
    ∀ y ∈ Subgroup.closure T, ∀ y' ∈ Subgroup.closure T, y * y' = y' * y := by
  have h1 : Subgroup.closure T ≤ Subgroup.centralizer T :=
    (Subgroup.closure_le _).mpr fun t ht =>
      Subgroup.mem_centralizer_iff.mpr fun t' ht' => hT t' ht' t ht
  have h2 : T ⊆ (Subgroup.centralizer (Subgroup.closure T : Set G) : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (h1 hy) t ht).symm
  have h3 : Subgroup.closure T ≤ Subgroup.centralizer (Subgroup.closure T : Set G) :=
    (Subgroup.closure_le _).mpr h2
  intro y hy y' hy'
  exact Subgroup.mem_centralizer_iff.mp (h3 hy') y hy

private theorem oneClass_closure_pow_four {T : Set G}
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) (h4 : ∀ t ∈ T, t ^ 4 = 1) :
    ∀ y ∈ Subgroup.closure T, y ^ 4 = 1 := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact h4 x hx
  | one => exact one_pow 4
  | mul a b ha hb iha ihb =>
    rw [Commute.mul_pow (oneClass_closure_comm hT a ha b hb), iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

private theorem oneClass_mem_T {z a t : G} (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z)
    (hta : t ∈ centerAt a) : t ∈ oneClassT z :=
  show ∃ a' : G, (Fused z a' ∧ a' ∈ coreAt z ∧ a' ≠ z) ∧ t ∈ centerAt a' from
    ⟨a, ⟨ha, haQ, haz⟩, hta⟩

private theorem oneClass_T_conj {z : G} {n : ℕ} (hC : Config z n) {h t : G}
    (hh : h ∈ centralizer ({z} : Set G)) (ht : t ∈ oneClassT z) :
    h * t * h⁻¹ ∈ oneClassT z := by
  obtain ⟨a, ⟨ha, haQ, haz⟩, hta⟩ := ht
  obtain ⟨g, rfl⟩ := ha
  refine oneClass_mem_T (a := h * (g⁻¹ * z * g) * h⁻¹) ⟨g * h⁻¹, ?_⟩
    (hC.conj_mem_core hh haQ) ?_ ?_
  · group
  · intro hz
    apply haz
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hh
    calc g⁻¹ * z * g = h⁻¹ * (h * (g⁻¹ * z * g) * h⁻¹) * h := by group
      _ = h⁻¹ * z * h := by rw [hz]
      _ = h⁻¹ * (z * h) := by group
      _ = h⁻¹ * (h * z) := by rw [hcomm.symm]
      _ = z := by group
  · have e : h * (g⁻¹ * z * g) * h⁻¹ = (g * h⁻¹)⁻¹ * z * (g * h⁻¹) := by group
    have e2 : g * h⁻¹ * (h * t * h⁻¹) * (g * h⁻¹)⁻¹ = g * t * g⁻¹ := by group
    rw [e, oneClass_mem_centerAt_conj, e2]
    exact (oneClass_mem_centerAt_conj z g t).mp hta

private theorem oneClass_closure_conj {z : G} {n : ℕ} (hC : Config z n) {h : G}
    (hh : h ∈ centralizer ({z} : Set G)) {y : G}
    (hy : y ∈ Subgroup.closure (oneClassT z)) :
    h * y * h⁻¹ ∈ Subgroup.closure (oneClassT z) := by
  have hle : Subgroup.closure (oneClassT z) ≤
      (Subgroup.closure (oneClassT z)).comap (MulAut.conj h).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun t ht => ?_
    exact Subgroup.subset_closure (oneClass_T_conj hC hh ht)
  exact hle hy

private theorem oneClass_T_comm {z : G} {n : ℕ} (hC : Config z n) (hA : CaseA z)
    (hall : ∀ a x : G, Fused z a → a ∈ coreAt z → a ≠ z → Fused z x → x ∈ coreAt z → x ≠ z →
      a * x = x * a) :
    ∀ t ∈ oneClassT z, ∀ t' ∈ oneClassT z, t * t' = t' * t := by
  intro t ht t' ht'
  obtain ⟨a, ⟨ha, haQ, haz⟩, hta⟩ := ht
  obtain ⟨b, ⟨hb, hbQ, hbz⟩, htb⟩ := ht'
  exact oneClass_comm_of_mem_centerAt hC hA hall ha haQ haz hb hbQ hbz hta htb

private theorem oneClass_T_pow_four {z : G} {n : ℕ} (hC : Config z n) :
    ∀ t ∈ oneClassT z, t ^ 4 = 1 := by
  intro t ht
  obtain ⟨a, ⟨ha, -, -⟩, hta⟩ := ht
  exact oneClass_pow_four (oneClass_config_of_fused hC ha) hta

private theorem oneClass_T_centralizer {z : G} {n : ℕ} (hC : Config z n) :
    ∀ t ∈ oneClassT z, t ∈ centralizer ({z} : Set G) := by
  intro t ht
  obtain ⟨a, ⟨ha, haQ, -⟩, hta⟩ := ht
  exact oneClass_centerAt_le hC ha haQ hta

private theorem oneClass_closure_le_centralizer {z : G} {n : ℕ} (hC : Config z n) :
    Subgroup.closure (oneClassT z) ≤ centralizer ({z} : Set G) :=
  (Subgroup.closure_le _).mpr fun t ht => oneClass_T_centralizer hC t ht

private theorem oneClass_subgroupOf_normal {z : G} (Y : Subgroup G)
    (hY : ∀ h ∈ centralizer ({z} : Set G), ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) :
    (Y.subgroupOf (centralizer ({z} : Set G))).Normal := by
  refine ⟨fun m hm g => Subgroup.mem_subgroupOf.mpr ?_⟩
  have hm' : (m : G) ∈ Y := Subgroup.mem_subgroupOf.mp hm
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact hY _ g.2 _ hm'

private theorem oneClass_subgroupOf_isPGroup {z : G} (Y : Subgroup G)
    (h4 : ∀ y ∈ Y, y ^ 4 = 1) :
    IsPGroup 2 ↥(Y.subgroupOf (centralizer ({z} : Set G))) := by
  intro x
  refine ⟨2, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simpa using h4 _ (Subgroup.mem_subgroupOf.mp x.2)

private theorem oneClass_closure_le_core {z : G} {n : ℕ} (hC : Config z n) (hA : CaseA z)
    (hall : ∀ a x : G, Fused z a → a ∈ coreAt z → a ≠ z → Fused z x → x ∈ coreAt z → x ≠ z →
      a * x = x * a) :
    Subgroup.closure (oneClassT z) ≤ coreAt z := by
  have hNorm := oneClass_subgroupOf_normal (z := z) (Subgroup.closure (oneClassT z))
    (fun h hh y hy => oneClass_closure_conj hC hh hy)
  have hPG := oneClass_subgroupOf_isPGroup (z := z) (Subgroup.closure (oneClassT z))
    (oneClass_closure_pow_four (oneClass_T_comm hC hA hall) (oneClass_T_pow_four hC))
  have hmem : (Subgroup.closure (oneClassT z)).subgroupOf (centralizer ({z} : Set G)) ∈
      {K : Subgroup ↥(centralizer ({z} : Set G)) | K.Normal ∧ IsPGroup 2 K} :=
    ⟨hNorm, hPG⟩
  have hle : (Subgroup.closure (oneClassT z)).subgroupOf (centralizer ({z} : Set G)) ≤
      CFSG.pCore 2 ↥(centralizer ({z} : Set G)) :=
    le_sSup hmem
  intro y hy
  have hyH : y ∈ centralizer ({z} : Set G) := oneClass_closure_le_centralizer hC hy
  have hyY : (⟨y, hyH⟩ : ↥(centralizer ({z} : Set G))) ∈
      (Subgroup.closure (oneClassT z)).subgroupOf (centralizer ({z} : Set G)) :=
    Subgroup.mem_subgroupOf.mpr hy
  have hyc : (⟨y, hyH⟩ : ↥(centralizer ({z} : Set G))) ∈
      CFSG.pCore 2 ↥(centralizer ({z} : Set G)) :=
    hle hyY
  unfold coreAt CFSG.inSubgroup
  exact Subgroup.mem_map.mpr ⟨⟨y, hyH⟩, hyc, rfl⟩

theorem CaseA.exists_not_commute (hC : Config z n) (hA : CaseA z) :
    ∃ a x : G, Fused z a ∧ a ∈ coreAt z ∧ a ≠ z ∧ Fused z x ∧ x ∈ coreAt z ∧ x ≠ z ∧
      a * x ≠ x * a := by
  by_contra hcon
  have hall : ∀ a x : G, Fused z a → a ∈ coreAt z → a ≠ z → Fused z x → x ∈ coreAt z → x ≠ z →
      a * x = x * a := by
    intro a x ha haQ haz hx hxQ hxz
    by_contra hax
    exact hcon ⟨a, x, ha, haQ, haz, hx, hxQ, hxz, hax⟩
  obtain ⟨g0, hg0Q, hg0ne⟩ := hC.exists_fused
  have hconj : CFSG.conjugate (centerAt z) g0 ≤ coreAt z := by
    rw [← centerAt_conj z g0]
    intro y hy
    exact oneClass_closure_le_core hC hA hall
      (Subgroup.subset_closure (oneClass_mem_T (fused_conj z g0) hg0Q hg0ne hy))
  exact hC.conj_center_not_le_core hg0Q hg0ne hconj

end CFSG.GF2Type.CenterFour

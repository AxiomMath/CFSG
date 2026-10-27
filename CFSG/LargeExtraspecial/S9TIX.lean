module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.LargeExtraspecial.S9.TIX

open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem conjSubgroup_mul (g h : G) (T : Subgroup G) :
    conjSubgroup (g * h) T = conjSubgroup g (conjSubgroup h T) := by
  ext x
  simp only [mem_conjSubgroup]
  rw [show (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h by group]

theorem conjSubgroup_one (T : Subgroup G) : conjSubgroup 1 T = T := by
  ext x
  simp [mem_conjSubgroup]

theorem conjSubgroup_eq_self_iff {g : G} {T : Subgroup G} :
    conjSubgroup g T = T ↔ g ∈ normalizer (T : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  rfl

theorem card_conjSubgroup (g : G) (T : Subgroup G) :
    Nat.card (conjSubgroup g T) = Nat.card T :=
  card_map_of_injective (MulAut.conj g).injective

theorem mem_normalizer_inf' {E F : Subgroup G} {g : G} (hE : g ∈ normalizer (E : Set G))
    (hF : g ∈ normalizer (F : Set G)) : g ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hE hF ⊢
  rw [map_inf_eq _ _ _ (MulAut.conj g).injective, hE, hF]

theorem le_normalizer_of_comm' {X N : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ N, x * y = y * x) :
    X ≤ normalizer (N : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h x hx y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 := h x hx _ hy
    have : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * ((x * y * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [← h1]
        _ = x * y * x⁻¹ := by group
    rw [this]
    exact hy

theorem exists_mul_of_mem_sup' {V U : Subgroup G} (hUV : U ≤ normalizer (V : Set G)) {x : G}
    (hx : x ∈ V ⊔ U) : ∃ v ∈ V, ∃ u ∈ U, x = v * u := by
  have hx' : x ∈ (V : Set G) * (U : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left V U hUV]
    exact hx
  obtain ⟨v, hv, u, hu, rfl⟩ := hx'
  exact ⟨v, hv, u, hu, rfl⟩

theorem comm_of_sq {T : Subgroup G} (hT : ∀ a ∈ T, a * a = 1) {a b : G} (ha : a ∈ T)
    (hb : b ∈ T) : a * b = b * a := by
  have hab := hT _ (mul_mem ha hb)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hT a ha)
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hT b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b * a := by rw [mul_inv_rev, hainv, hbinv]

@[expose] def IsTIIn (T X : Subgroup G) : Prop :=
  ∀ x ∈ X, T ⊓ conjSubgroup x T ≠ ⊥ → conjSubgroup x T = T

theorem IsTIIn.conj {T X : Subgroup G} (hT : IsTIIn T X) {g : G} (hg : g ∈ X) :
    IsTIIn (conjSubgroup g T) X := by
  intro c hc hne
  have e : conjSubgroup c (conjSubgroup g T) =
      conjSubgroup g (conjSubgroup (g⁻¹ * c * g) T) := by
    rw [← conjSubgroup_mul, ← conjSubgroup_mul]
    congr 1
    group
  have hgc : g⁻¹ * c * g ∈ X := mul_mem (mul_mem (inv_mem hg) hc) hg
  have hne' : T ⊓ conjSubgroup (g⁻¹ * c * g) T ≠ ⊥ := by
    intro hbot
    apply hne
    rw [e, eq_bot_iff]
    intro y ⟨hy1, hy2⟩
    have h1 : g⁻¹ * y * g ∈ T ⊓ conjSubgroup (g⁻¹ * c * g) T :=
      ⟨mem_conjSubgroup.mp hy1, mem_conjSubgroup.mp hy2⟩
    rw [hbot, mem_bot] at h1
    rw [mem_bot]
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  rw [e, hT _ hgc hne']

theorem mem_normalizer_of_commute_of_isTIIn {T X : Subgroup G} (hT : IsTIIn T X) {c x : G}
    (hcX : c ∈ X) (hx : x ∈ T) (hx1 : x ≠ 1) (hcx : c * x = x * c) :
    c ∈ normalizer (T : Set G) := by
  rw [← conjSubgroup_eq_self_iff]
  refine hT c hcX fun h => hx1 ?_
  have hmem : x ∈ T ⊓ conjSubgroup c T := by
    refine mem_inf.mpr ⟨hx, ?_⟩
    rw [mem_conjSubgroup, show c⁻¹ * x * c = x by rw [mul_assoc, ← hcx]; group]
    exact hx
  rw [h] at hmem
  exact mem_bot.mp hmem

theorem commutator_mem_of_isTIIn {T T' X : Subgroup G} (hT : ∀ a ∈ T, a * a = 1)
    (hT' : ∀ a ∈ T', a * a = 1) (hTI' : IsTIIn T' X) (hTX : T ≤ X) {a l : G} (ha : a ∈ T)
    (hl : l ∈ T') (hlN : l ∈ normalizer (T : Set G)) :
    a * l * a⁻¹ * l⁻¹ ∈ T ∧ a * l * a⁻¹ * l⁻¹ ∈ normalizer (T' : Set G) := by
  have hll : l * l = 1 := hT' l hl
  have hlinv : l⁻¹ = l := inv_eq_of_mul_eq_one_right hll
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hT a ha)
  have ha' : l * a * l ∈ T := by
    have := (mem_normalizer_iff.mp hlN a).mp ha
    rwa [hlinv] at this
  have hc_eq : a * l * a⁻¹ * l⁻¹ = a * (l * a * l) := by rw [hainv, hlinv]; group
  rw [hc_eq]
  refine ⟨mul_mem ha ha', ?_⟩
  by_cases hl1 : l = 1
  · rw [hl1, mul_one, one_mul, hT a ha]
    exact one_mem _
  refine mem_normalizer_of_commute_of_isTIIn hTI' (hTX (mul_mem ha ha')) hl hl1 ?_
  have hcomm : (l * a * l) * a = a * (l * a * l) := comm_of_sq hT ha' ha
  have h2 : l * (a * (l * a * l)) * l = a * (l * a * l) := by
    calc l * (a * (l * a * l)) * l = (l * a * l) * (l * (l * a * l) * l) := by
          rw [show (l * a * l) * (l * (l * a * l) * l) =
            l * a * (l * l) * (l * a * l) * l by group, hll, mul_one]
          group
      _ = (l * a * l) * a := by
          rw [show l * (l * a * l) * l = (l * l) * a * (l * l) by group, hll, one_mul, mul_one]
      _ = a * (l * a * l) := hcomm
  calc a * (l * a * l) * l = (l * (a * (l * a * l)) * l) * l := by rw [h2]
    _ = l * (a * (l * a * l)) * (l * l) := by group
    _ = l * (a * (l * a * l)) := by rw [hll, mul_one]

theorem exists_ne_one_commute {U : Subgroup G} (hU : ∀ a ∈ U, a * a = 1) (hU1 : U ≠ ⊥) {t : G}
    (htN : t ∈ normalizer (U : Set G)) (ht : t * t = 1) :
    ∃ x ∈ U, x ≠ 1 ∧ t * x = x * t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  obtain ⟨⟨u, hu⟩, hu1'⟩ := ne_bot_iff_exists_ne_one.mp hU1
  have hu1 : u ≠ 1 := fun h => hu1' (Subtype.ext h)
  have hσ : ∀ x ∈ U, t * x * t⁻¹ ∈ U := fun x hx => (mem_normalizer_iff.mp htN x).mp hx
  by_cases h : u * (t * u * t⁻¹) = 1
  · refine ⟨u, hu, hu1, ?_⟩
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hU u hu)
    have : t * u * t⁻¹ = u := by
      have h' := eq_inv_of_mul_eq_one_right h
      rwa [huinv] at h'
    calc t * u = t * u * t⁻¹ * t := by group
      _ = u * t := by rw [this]
  · refine ⟨u * (t * u * t⁻¹), mul_mem hu (hσ u hu), h, ?_⟩
    have e : t * (u * (t * u * t⁻¹)) * t⁻¹ = (t * u * t⁻¹) * u := by
      rw [htinv]
      calc t * (u * (t * u * t)) * t = t * u * t * u * (t * t) := by group
        _ = t * u * t * u := by rw [ht, mul_one]
    have e2 : t * (u * (t * u * t⁻¹)) * t⁻¹ = u * (t * u * t⁻¹) := by
      rw [e, comm_of_sq hU (hσ u hu) hu]
    calc t * (u * (t * u * t⁻¹)) = t * (u * (t * u * t⁻¹)) * t⁻¹ * t := by group
      _ = u * (t * u * t⁻¹) * t := by rw [e2]

theorem commute_commutator_of_involutions {t τ c : G} (ht : t * t = 1) (hτ : τ * τ = 1)
    (hc : c = t * τ * t⁻¹ * τ⁻¹) (hcc : c * c = 1) : t * c = c * t ∧ c * τ = τ * c := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hcinv' : c⁻¹ = τ * t * τ * t := by
    rw [hc, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, htinv, hτinv]
    group
  have e1 : t * c * t⁻¹ = τ * t * τ * t := by
    rw [hc, htinv, hτinv]
    calc t * (t * τ * t * τ) * t = (t * t) * τ * t * τ * t := by group
      _ = τ * t * τ * t := by rw [ht, one_mul]
  have e2 : τ * c * τ⁻¹ = τ * t * τ * t := by
    rw [hc, htinv, hτinv]
    calc τ * (t * τ * t * τ) * τ = τ * t * τ * t * (τ * τ) := by group
      _ = τ * t * τ * t := by rw [hτ, mul_one]
  constructor
  · have e : t * c * t⁻¹ = c := by rw [e1, ← hcinv', hcinv]
    calc t * c = t * c * t⁻¹ * t := by group
      _ = c * t := by rw [e]
  · have e : τ * c * τ⁻¹ = c := by rw [e2, ← hcinv', hcinv]
    calc c * τ = (τ * c * τ⁻¹) * τ := by rw [e]
      _ = τ * c := by group

structure Setup (A Ab L Lb M : Subgroup G) : Prop where
  sqA : ∀ a ∈ A, a * a = 1
  sqAb : ∀ a ∈ Ab, a * a = 1
  card : Nat.card A = Nat.card Ab
  tiA : IsTIIn A (A ⊔ Ab)
  tiAb : IsTIIn Ab (A ⊔ Ab)
  mix : ∀ x ∈ A ⊔ Ab, conjSubgroup x A ⊓ Ab ≠ ⊥ → conjSubgroup x A = Ab
  hL : L = A ⊓ normalizer (Ab : Set G)
  hLb : Lb = Ab ⊓ normalizer (A : Set G)
  hM : M = L ⊔ Lb
  ne_bot : L ≠ ⊥
  ne : L ≠ A

namespace Setup

variable {A Ab L Lb M : Subgroup G} (S : Setup A Ab L Lb M)
include S

theorem mem_L {x : G} : x ∈ L ↔ x ∈ A ∧ x ∈ normalizer (Ab : Set G) := by
  rw [S.hL, mem_inf]

theorem mem_Lb {x : G} : x ∈ Lb ↔ x ∈ Ab ∧ x ∈ normalizer (A : Set G) := by
  rw [S.hLb, mem_inf]

theorem L_le : L ≤ A := fun _ hx => (S.mem_L.mp hx).1

theorem Lb_le : Lb ≤ Ab := fun _ hx => (S.mem_Lb.mp hx).1

theorem comm_A {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := comm_of_sq S.sqA ha hb

theorem comm_Ab {a b : G} (ha : a ∈ Ab) (hb : b ∈ Ab) : a * b = b * a := comm_of_sq S.sqAb ha hb

theorem Ab_ne : Ab ≠ A := by
  intro h
  apply S.ne
  rw [S.hL, h]
  exact le_antisymm inf_le_left (le_inf le_rfl le_normalizer)

theorem mul_mem_M {l lb : G} (hl : l ∈ L) (hlb : lb ∈ Lb) : l * lb ∈ M := by
  rw [S.hM]
  exact mul_mem (mem_sup_left hl) (mem_sup_right hlb)

theorem L_le_M : L ≤ M := S.hM ▸ le_sup_left

theorem Lb_le_M : Lb ≤ M := S.hM ▸ le_sup_right

theorem inf_eq_bot : A ⊓ Ab = ⊥ := by
  by_contra hne
  apply S.Ab_ne
  have := S.mix 1 (one_mem _) (by rwa [conjSubgroup_one])
  rw [conjSubgroup_one] at this
  exact this.symm

theorem mem_Lb_of_commute {c a : G} (hc : c ∈ Ab) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hca : c * a = a * c) : c ∈ Lb :=
  S.mem_Lb.mpr ⟨hc, mem_normalizer_of_commute_of_isTIIn S.tiA (mem_sup_right hc) ha ha1 hca⟩

theorem mem_L_of_commute {c a : G} (hc : c ∈ A) (ha : a ∈ Ab) (ha1 : a ≠ 1)
    (hca : c * a = a * c) : c ∈ L :=
  S.mem_L.mpr ⟨hc, mem_normalizer_of_commute_of_isTIIn S.tiAb (mem_sup_left hc) ha ha1 hca⟩

theorem commutator_mem_L {a lb : G} (ha : a ∈ A) (hlb : lb ∈ Lb) :
    a * lb * a⁻¹ * lb⁻¹ ∈ L := by
  obtain ⟨hlbAb, hlbN⟩ := S.mem_Lb.mp hlb
  obtain ⟨h1, h2⟩ := commutator_mem_of_isTIIn S.sqA S.sqAb S.tiAb le_sup_left ha hlbAb hlbN
  exact S.mem_L.mpr ⟨h1, h2⟩

theorem commutator_mem_Lb {ab l : G} (hab : ab ∈ Ab) (hl : l ∈ L) :
    ab * l * ab⁻¹ * l⁻¹ ∈ Lb := by
  obtain ⟨hlA, hlN⟩ := S.mem_L.mp hl
  obtain ⟨h1, h2⟩ := commutator_mem_of_isTIIn S.sqAb S.sqA S.tiA le_sup_right hab hlA hlN
  exact S.mem_Lb.mpr ⟨h1, h2⟩

theorem comm_L_Lb {l lb : G} (hl : l ∈ L) (hlb : lb ∈ Lb) : l * lb = lb * l := by
  have h1 : l * lb * l⁻¹ * lb⁻¹ ∈ L := S.commutator_mem_L (S.L_le hl) hlb
  have h2 : l * lb * l⁻¹ * lb⁻¹ ∈ Ab := by
    have h3 : l * lb * l⁻¹ ∈ Ab :=
      (mem_normalizer_iff.mp (S.mem_L.mp hl).2 lb).mp (S.Lb_le hlb)
    exact mul_mem h3 (inv_mem (S.Lb_le hlb))
  have h4 : l * lb * l⁻¹ * lb⁻¹ ∈ A ⊓ Ab := mem_inf.mpr ⟨S.L_le h1, h2⟩
  rw [S.inf_eq_bot, mem_bot] at h4
  calc l * lb = l * lb * l⁻¹ * lb⁻¹ * (lb * l) := by group
    _ = lb * l := by rw [h4, one_mul]

theorem exists_mul_of_mem_M {x : G} (hx : x ∈ M) : ∃ l ∈ L, ∃ lb ∈ Lb, x = l * lb := by
  rw [S.hM] at hx
  exact exists_mul_of_mem_sup' (le_normalizer_of_comm' fun a ha b hb => (S.comm_L_Lb hb ha).symm)
    hx

theorem sq_M {x : G} (hx : x ∈ M) : x * x = 1 := by
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hx
  rw [show l * lb * (l * lb) = l * (lb * l) * lb by group, ← S.comm_L_Lb hl hlb,
    show l * (l * lb) * lb = (l * l) * (lb * lb) by group, S.sqA l (S.L_le hl),
    S.sqAb lb (S.Lb_le hlb), one_mul]

theorem A_le_normalizer_M : A ≤ normalizer (M : Set G) := by
  have key : ∀ a ∈ A, ∀ x ∈ M, a * x * a⁻¹ ∈ M := by
    intro a ha x hx
    obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hx
    have hc := S.commutator_mem_L ha hlb
    have e : a * (l * lb) * a⁻¹ = (l * (a * lb * a⁻¹ * lb⁻¹)) * lb := by
      have := S.comm_A ha (S.L_le hl)
      calc a * (l * lb) * a⁻¹ = (a * l) * lb * a⁻¹ := by group
        _ = (l * a) * lb * a⁻¹ := by rw [this]
        _ = (l * (a * lb * a⁻¹ * lb⁻¹)) * lb := by group
    rw [e]
    exact S.mul_mem_M (mul_mem hl hc) hlb
  intro a ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (S.sqA a ha)
  refine mem_normalizer_iff.mpr fun x => ⟨key a ha x, fun hx => ?_⟩
  have := key a ha _ hx
  rwa [show a * (a * x * a⁻¹) * a⁻¹ = x by rw [hainv]; rw [← mul_assoc, ← mul_assoc,
    S.sqA a ha, one_mul, mul_assoc, S.sqA a ha, mul_one]] at this

theorem Ab_le_normalizer_M : Ab ≤ normalizer (M : Set G) := by
  have key : ∀ a ∈ Ab, ∀ x ∈ M, a * x * a⁻¹ ∈ M := by
    intro a ha x hx
    obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hx
    have hc := S.commutator_mem_Lb ha hl
    have hcomm : a * lb = lb * a := S.comm_Ab ha (S.Lb_le hlb)
    have e : a * (l * lb) * a⁻¹ = l * ((a * l * a⁻¹ * l⁻¹) * lb) := by
      have hcLb := S.comm_L_Lb hl (mul_mem hc hlb)
      calc a * (l * lb) * a⁻¹ = a * l * a⁻¹ * (a * lb * a⁻¹) := by group
        _ = a * l * a⁻¹ * lb := by rw [hcomm]; group
        _ = (a * l * a⁻¹ * l⁻¹) * lb * l := by
            rw [show a * l * a⁻¹ * l⁻¹ * lb * l = a * l * a⁻¹ * (l⁻¹ * (lb * l)) by group,
              ← S.comm_L_Lb hl hlb]
            group
        _ = l * ((a * l * a⁻¹ * l⁻¹) * lb) := by rw [hcLb.symm]
    rw [e]
    exact S.mul_mem_M hl (mul_mem hc hlb)
  intro a ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (S.sqAb a ha)
  refine mem_normalizer_iff.mpr fun x => ⟨key a ha x, fun hx => ?_⟩
  have := key a ha _ hx
  rwa [show a * (a * x * a⁻¹) * a⁻¹ = x by rw [hainv]; rw [← mul_assoc, ← mul_assoc,
    S.sqAb a ha, one_mul, mul_assoc, S.sqAb a ha, mul_one]] at this

theorem sup_le_normalizer_M : A ⊔ Ab ≤ normalizer (M : Set G) :=
  sup_le S.A_le_normalizer_M S.Ab_le_normalizer_M

theorem inf_M : A ⊓ M = L := by
  refine le_antisymm (fun x hx => ?_) (le_inf S.L_le S.L_le_M)
  obtain ⟨hxA, hxM⟩ := mem_inf.mp hx
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hxM
  have hlbA : lb ∈ A := by
    have := mul_mem (inv_mem (S.L_le hl)) hxA
    rwa [inv_mul_cancel_left] at this
  have : lb ∈ A ⊓ Ab := mem_inf.mpr ⟨hlbA, S.Lb_le hlb⟩
  rw [S.inf_eq_bot, mem_bot] at this
  rw [this, mul_one]
  exact hl

theorem mem_L_of_commute_M {t m : G} (ht : t ∈ A) (htL : t ∉ L) (hm : m ∈ M)
    (htm : t * m = m * t) : m ∈ L := by
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hm
  have e : t * (l * lb) * t⁻¹ = (l * (t * lb * t⁻¹ * lb⁻¹)) * lb := by
    have := S.comm_A ht (S.L_le hl)
    calc t * (l * lb) * t⁻¹ = (t * l) * lb * t⁻¹ := by group
      _ = (l * t) * lb * t⁻¹ := by rw [this]
      _ = (l * (t * lb * t⁻¹ * lb⁻¹)) * lb := by group
  have hfix : t * (l * lb) * t⁻¹ = l * lb := by rw [htm]; group
  rw [e] at hfix
  have h1 : t * lb * t⁻¹ * lb⁻¹ = 1 := by
    have := mul_right_cancel hfix
    exact mul_left_cancel (this.trans (mul_one l).symm)
  have htlb : t * lb = lb * t := by
    calc t * lb = t * lb * t⁻¹ * lb⁻¹ * (lb * t) := by group
      _ = lb * t := by rw [h1, one_mul]
  by_cases hlb1 : lb = 1
  · rw [hlb1, mul_one]
    exact hl
  · exact absurd (S.mem_L_of_commute ht (S.Lb_le hlb) hlb1 htlb) htL

theorem conj_mem_L_of_commute_M {g a m : G} (hg : g ∈ normalizer (M : Set G))
    (ha : a ∈ A) (haL : a ∉ L) (hm : m ∈ M) (hcomm : m * (g⁻¹ * a * g) = (g⁻¹ * a * g) * m) :
    g * m * g⁻¹ ∈ L := by
  have hgm : g * m * g⁻¹ ∈ M := (mem_normalizer_iff.mp hg m).mp hm
  refine S.mem_L_of_commute_M ha haL hgm ?_
  calc a * (g * m * g⁻¹) = g * ((g⁻¹ * a * g) * m) * g⁻¹ := by group
    _ = g * (m * (g⁻¹ * a * g)) * g⁻¹ := by rw [hcomm]
    _ = g * m * g⁻¹ * a := by group

theorem conj_mem_of_commutator_mem {g t a : G} (hgX : g ∈ A ⊔ Ab) (ht : t ∈ A) (htL : t ∉ L)
    (ha : a ∈ A) (haL : a ∉ L) (hc : t * (g⁻¹ * a * g) * t⁻¹ * (g⁻¹ * a * g)⁻¹ ∈ M) :
    g⁻¹ * a * g ∈ A := by
  have hg := S.sup_le_normalizer_M hgX
  have hτT : g⁻¹ * a * g ∈ conjSubgroup g⁻¹ A := by
    rw [mem_conjSubgroup, inv_inv]
    simpa [mul_assoc] using ha
  have hTTI : IsTIIn (conjSubgroup g⁻¹ A) (A ⊔ Ab) := S.tiA.conj (inv_mem hgX)
  have hsuff : ∀ x, x ∈ A → x ∈ conjSubgroup g⁻¹ A → x ≠ 1 → g⁻¹ * a * g ∈ A := by
    intro x hxA hxT hx1
    have hne : A ⊓ conjSubgroup g⁻¹ A ≠ ⊥ := fun h => by
      have : x ∈ A ⊓ conjSubgroup g⁻¹ A := mem_inf.mpr ⟨hxA, hxT⟩
      rw [h, mem_bot] at this
      exact hx1 this
    have hTA : conjSubgroup g⁻¹ A = A := S.tiA g⁻¹ (inv_mem hgX) hne
    rw [← hTA]
    exact hτT
  have ht2 : t * t = 1 := S.sqA t ht
  have hτ2 : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    rw [show g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, S.sqA a ha]
    group
  have hcc : (t * (g⁻¹ * a * g) * t⁻¹ * (g⁻¹ * a * g)⁻¹) *
      (t * (g⁻¹ * a * g) * t⁻¹ * (g⁻¹ * a * g)⁻¹) = 1 := S.sq_M hc
  obtain ⟨htc, hτc⟩ := commute_commutator_of_involutions ht2 hτ2 rfl hcc
  have hcL : t * (g⁻¹ * a * g) * t⁻¹ * (g⁻¹ * a * g)⁻¹ ∈ L := S.mem_L_of_commute_M ht htL hc htc
  have hgcL := S.conj_mem_L_of_commute_M hg ha haL hc hτc
  have hcT : t * (g⁻¹ * a * g) * t⁻¹ * (g⁻¹ * a * g)⁻¹ ∈ conjSubgroup g⁻¹ A := by
    rw [mem_conjSubgroup, inv_inv]
    exact S.L_le hgcL
  by_cases hc1 : t * (g⁻¹ * a * g) * t⁻¹ * (g⁻¹ * a * g)⁻¹ = 1
  ·
    have htτ : t * (g⁻¹ * a * g) = (g⁻¹ * a * g) * t := by
      calc t * (g⁻¹ * a * g) = (t * (g⁻¹ * a * g) * t⁻¹ * (g⁻¹ * a * g)⁻¹) *
          ((g⁻¹ * a * g) * t) := by group
        _ = (g⁻¹ * a * g) * t := by rw [hc1, one_mul]
    have hτ1 : g⁻¹ * a * g ≠ 1 := by
      intro h
      apply haL
      have : a = 1 := by
        calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group
      rw [this]
      exact one_mem _
    have htNT : t ∈ normalizer (conjSubgroup g⁻¹ A : Set G) :=
      mem_normalizer_of_commute_of_isTIIn hTTI (mem_sup_left ht) hτT hτ1 htτ
    have hUe : ∀ x ∈ conjSubgroup g⁻¹ A ⊓ M, x * x = 1 := fun x hx => S.sq_M hx.2
    have hU1 : conjSubgroup g⁻¹ A ⊓ M ≠ ⊥ := by
      obtain ⟨⟨l, hl⟩, hl1'⟩ := ne_bot_iff_exists_ne_one.mp S.ne_bot
      have hl1 : l ≠ 1 := fun h => hl1' (Subtype.ext h)
      intro hbot
      have hmem : g⁻¹ * l * g ∈ conjSubgroup g⁻¹ A ⊓ M := by
        refine mem_inf.mpr ⟨?_, ?_⟩
        · rw [mem_conjSubgroup, inv_inv]
          simpa [mul_assoc] using S.L_le hl
        · have := (mem_normalizer_iff.mp (inv_mem hg) l).mp (S.L_le_M hl)
          simpa using this
      rw [hbot, mem_bot] at hmem
      apply hl1
      calc l = g * (g⁻¹ * l * g) * g⁻¹ := by group
        _ = 1 := by rw [hmem]; group
    have htNU : t ∈ normalizer ((conjSubgroup g⁻¹ A ⊓ M : Subgroup G) : Set G) :=
      mem_normalizer_inf' htNT (S.A_le_normalizer_M ht)
    obtain ⟨x, hxU, hx1, htx⟩ := exists_ne_one_commute hUe hU1 htNU ht2
    have hxL : x ∈ L := S.mem_L_of_commute_M ht htL hxU.2 htx
    exact hsuff x (S.L_le hxL) hxU.1 hx1
  · exact hsuff _ (S.L_le hcL) hcT hc1

end Setup

end CFSG.LargeExtraspecial.S9.TIX

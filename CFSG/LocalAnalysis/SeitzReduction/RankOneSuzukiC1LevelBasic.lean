module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1Stage
public import CFSG.LocalAnalysis.SeitzReduction.Endgame

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1

variable {G : Type*} [Group G]

theorem comm_mem_of_generators_normal {R A : Subgroup G} {P : G → Prop}
    (hgen : ∀ S : Subgroup G, (∀ g, P g → g ∈ S) → R ≤ S) (hPR : ∀ g, P g → g ∈ R)
    (hA : ∀ y ∈ R, ∀ b ∈ A, y * b * y⁻¹ ∈ A)
    (hP : ∀ g, P g → ∀ g', P g' → g * g' * g⁻¹ * g'⁻¹ ∈ A) :
    ∀ x ∈ R, ∀ x' ∈ R, x * x' * x⁻¹ * x'⁻¹ ∈ A := by
  let S : G → Subgroup G := fun x =>
    { carrier := {z | z ∈ R ∧ x * z * x⁻¹ * z⁻¹ ∈ A}
      mul_mem' := by
        rintro z z' ⟨hz, hzA⟩ ⟨hz', hz'A⟩
        refine ⟨mul_mem hz hz', ?_⟩
        have e : x * (z * z') * x⁻¹ * (z * z')⁻¹ =
            x * z * x⁻¹ * z⁻¹ * (z * (x * z' * x⁻¹ * z'⁻¹) * z⁻¹) := by group
        rw [e]
        exact mul_mem hzA (hA z hz _ hz'A)
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro z ⟨hz, hzA⟩
        refine ⟨inv_mem hz, ?_⟩
        have e : x * z⁻¹ * x⁻¹ * z⁻¹⁻¹ = z⁻¹ * (x * z * x⁻¹ * z⁻¹)⁻¹ * z⁻¹⁻¹ := by group
        rw [e]
        exact hA _ (inv_mem hz) _ (inv_mem hzA) }
  have hS : ∀ x, ∀ z ∈ S x, x * z * x⁻¹ * z⁻¹ ∈ A := fun x z hz => hz.2
  have hgen1 : ∀ g, P g → ∀ z ∈ R, g * z * g⁻¹ * z⁻¹ ∈ A := fun g hg z hz =>
    hS g z (hgen (S g) (fun g' hg' => ⟨hPR g' hg', hP g hg g' hg'⟩) hz)
  intro x hx x' hx'
  refine hS x x' (hgen (S x) (fun g hg => ⟨hPR g hg, ?_⟩) hx')
  have e : x * g * x⁻¹ * g⁻¹ = (g * x * g⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem (hgen1 g hg x hx)

def sqHom {V : Subgroup G} (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (m : ℕ) : V →* G :=
  MonoidHom.mk' (fun x => (x : G) ^ m) fun x y => by
    rw [Subgroup.coe_mul]
    exact (Commute.mul_pow (hcomm x x.2 y y.2) m)

def powKer {V : Subgroup G} (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (m : ℕ) : Subgroup G where
  carrier := {x | x ∈ V ∧ x ^ m = 1}
  mul_mem' := by
    rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
    exact ⟨mul_mem hx hy, by rw [(Commute.mul_pow (hcomm x hx y hy) m), hx1, hy1, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow m⟩
  inv_mem' := by
    rintro x ⟨hx, hx1⟩
    exact ⟨inv_mem hx, by rw [inv_pow, hx1, inv_one]⟩

theorem range_sqHom_le {V : Subgroup G} (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (m : ℕ) :
    (sqHom hcomm m).range ≤ V := by
  rintro _ ⟨x, rfl⟩
  exact pow_mem x.2 m

theorem card_eq_card_ker_mul_card_range [Finite G] {V : Subgroup G} {H : Type*} [Group H]
    (f : V →* H) : Nat.card V = Nat.card f.ker * Nat.card f.range := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

theorem card_ker_sqHom_le [Finite G] {V : Subgroup G} (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (m : ℕ) : Nat.card (sqHom hcomm m).ker ≤ Nat.card (powKer hcomm m) := by
  refine Nat.card_le_card_of_injective
    (fun x => (⟨((x : V) : G), (x : V).2, x.2⟩ : powKer hcomm m)) fun x y hxy => ?_
  exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))

theorem card_le_of_pow_eq_one [Finite G] {A : Subgroup G} :
    ∀ (k : ℕ) (V : Subgroup G), (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) →
      (∀ x ∈ V, x ^ 2 = 1 → x ∈ A) → (∀ x ∈ V, x ^ 2 ^ k = 1) → Nat.card V ≤ Nat.card A ^ k
  | 0, V, _, _, hpow => by
      have hV : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr fun x hx => by
        simpa using hpow x hx
      rw [hV, Subgroup.card_bot, pow_zero]
  | k + 1, V, hcomm, hΩ, hpow => by
      set f := sqHom hcomm 2 with hf
      have hker : Nat.card f.ker ≤ Nat.card A := by
        refine Nat.card_le_card_of_injective
          (fun x => (⟨((x : V) : G), hΩ _ (x : V).2 x.2⟩ : A)) fun x y hxy => ?_
        exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
      have hrange : Nat.card f.range ≤ Nat.card A ^ k := by
        refine card_le_of_pow_eq_one k f.range (fun x hx y hy =>
          hcomm x (range_sqHom_le hcomm 2 hx) y (range_sqHom_le hcomm 2 hy))
          (fun x hx hx2 => hΩ x (range_sqHom_le hcomm 2 hx) hx2) ?_
        rintro _ ⟨x, rfl⟩
        show ((x : G) ^ 2) ^ 2 ^ k = 1
        rw [← pow_mul, ← pow_succ']
        exact hpow x x.2
      rw [card_eq_card_ker_mul_card_range f, pow_succ']
      exact Nat.mul_le_mul hker hrange

theorem exists_sq_eq_of_pow_eq_one [Finite G] {A V : Subgroup G} {k : ℕ}
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hΩ : ∀ x ∈ V, x ^ 2 = 1 → x ∈ A)
    (hpow : ∀ x ∈ V, x ^ 2 ^ (k + 1) = 1) (hcard : Nat.card A ^ (k + 1) ≤ Nat.card V)
    {x : G} (hx : x ∈ V) (hxk : x ^ 2 ^ k = 1) : ∃ w ∈ V, x = w ^ 2 := by
  set f := sqHom hcomm 2 with hf
  have hle : f.range ≤ powKer hcomm (2 ^ k) := by
    rintro _ ⟨w, rfl⟩
    refine ⟨pow_mem w.2 2, ?_⟩
    show ((w : G) ^ 2) ^ 2 ^ k = 1
    rw [← pow_mul, ← pow_succ']
    exact hpow w w.2
  have hK : Nat.card (powKer hcomm (2 ^ k)) ≤ Nat.card A ^ k :=
    card_le_of_pow_eq_one k _ (fun x hx y hy => hcomm x hx.1 y hy.1)
      (fun x hx hx2 => hΩ x hx.1 hx2) fun x hx => hx.2
  have hker : Nat.card f.ker ≤ Nat.card A := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨((x : V) : G), hΩ _ (x : V).2 x.2⟩ : A)) fun x y hxy => ?_
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
  have hA0 : 0 < Nat.card A := Nat.card_pos
  have hrange : Nat.card A ^ k ≤ Nat.card f.range := by
    have h1 := card_eq_card_ker_mul_card_range f
    have h2 : Nat.card A * Nat.card A ^ k ≤ Nat.card A * Nat.card f.range := by
      calc Nat.card A * Nat.card A ^ k = Nat.card A ^ (k + 1) := by rw [pow_succ']
        _ ≤ Nat.card V := hcard
        _ = Nat.card f.ker * Nat.card f.range := h1
        _ ≤ Nat.card A * Nat.card f.range := Nat.mul_le_mul_right _ hker
    exact Nat.le_of_mul_le_mul_left h2 hA0
  have heq := Subgroup.eq_of_le_of_card_ge hle (hK.trans hrange)
  have hxK : x ∈ powKer hcomm (2 ^ k) := ⟨hx, hxk⟩
  rw [← heq] at hxK
  obtain ⟨w, hw⟩ := hxK
  exact ⟨w, w.2, hw.symm⟩

theorem exists_pow_eq_of_mem [Finite G] {A V : Subgroup G} {k : ℕ}
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hΩ : ∀ x ∈ V, x ^ 2 = 1 → x ∈ A)
    (hpow : ∀ x ∈ V, x ^ 2 ^ (k + 1) = 1) (hcard : Nat.card A ^ (k + 1) ≤ Nat.card V)
    {b : G} (hb : b ∈ A) : ∃ x ∈ V, x ^ 2 ^ k = b := by
  set g := sqHom hcomm (2 ^ k) with hg
  have hle : g.range ≤ A := by
    rintro _ ⟨x, rfl⟩
    refine hΩ _ (pow_mem x.2 _) ?_
    show ((x : G) ^ 2 ^ k) ^ 2 = 1
    rw [← pow_mul, ← pow_succ]
    exact hpow x x.2
  have hK : Nat.card (powKer hcomm (2 ^ k)) ≤ Nat.card A ^ k :=
    card_le_of_pow_eq_one k _ (fun x hx y hy => hcomm x hx.1 y hy.1)
      (fun x hx hx2 => hΩ x hx.1 hx2) fun x hx => hx.2
  have hker := (card_ker_sqHom_le hcomm (2 ^ k)).trans hK
  have hAk0 : 0 < Nat.card A ^ k := pow_pos Nat.card_pos k
  have hrange : Nat.card A ≤ Nat.card g.range := by
    have h1 := card_eq_card_ker_mul_card_range g
    have h2 : Nat.card A ^ k * Nat.card A ≤ Nat.card A ^ k * Nat.card g.range := by
      calc Nat.card A ^ k * Nat.card A = Nat.card A ^ (k + 1) := by rw [pow_succ]
        _ ≤ Nat.card V := hcard
        _ = Nat.card g.ker * Nat.card g.range := h1
        _ ≤ Nat.card A ^ k * Nat.card g.range := Nat.mul_le_mul_right _ hker
    exact Nat.le_of_mul_le_mul_left h2 hAk0
  have heq := Subgroup.eq_of_le_of_card_ge hle hrange
  rw [← heq] at hb
  obtain ⟨x, hx⟩ := hb
  exact ⟨x, x.2, hx⟩

theorem relIndex_sup_eq_relIndex_inf {H K : Subgroup G} (hK : H ≤ normalizer (K : Set G)) :
    K.relIndex (H ⊔ K) = (H ⊓ K).relIndex H := by
  set NG : Subgroup G := normalizer (K : Set G)
  have hKN : K ≤ NG := le_normalizer
  have : (K.subgroupOf NG).Normal :=
    (normal_subgroupOf_iff_le_normalizer (H := K) (K := NG) hKN).2 le_rfl
  calc K.relIndex (H ⊔ K) = (K.subgroupOf NG).relIndex ((H ⊔ K).subgroupOf NG) :=
        (relIndex_subgroupOf (H := K) (K := H ⊔ K) (L := NG) (sup_le hK hKN)).symm
    _ = (K.subgroupOf NG).relIndex ((H.subgroupOf NG) ⊔ (K.subgroupOf NG)) := by
        rw [subgroupOf_sup (A := H) (A' := K) (B := NG) hK hKN]
    _ = (K.subgroupOf NG).relIndex (H.subgroupOf NG) :=
        relIndex_sup_right (H.subgroupOf NG) (K.subgroupOf NG)
    _ = ((H.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex (H.subgroupOf NG) :=
        (inf_relIndex_left (H := H.subgroupOf NG) (K := K.subgroupOf NG)).symm
    _ = ((H ⊓ K).subgroupOf NG).relIndex (H.subgroupOf NG) := by
        rw [show (H.subgroupOf NG) ⊓ (K.subgroupOf NG) = (H ⊓ K).subgroupOf NG by
          ext x
          simp [mem_subgroupOf]]
    _ = (H ⊓ K).relIndex H := relIndex_subgroupOf (H := H ⊓ K) (K := H) (L := NG) hK

theorem comm_t_mul (x y t : G) :
    x * y * t * (x * y)⁻¹ * t⁻¹ = x * (y * t * y⁻¹ * t⁻¹) * x⁻¹ * (x * t * x⁻¹ * t⁻¹) := by
  group

end SzC1

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

section Basic

variable (h : SzC1Stage G L f a t T d V U U₁ k)
include h

theorem t_sq : t ^ 2 = 1 := h.start.sq_eq_one

theorem t_mul_self : t * t = 1 := by rw [← sq]; exact h.t_sq

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_self

theorem t_comm {y : G} (hy : y ∈ szT₁ L T) : y * t = t * y :=
  mem_centralizer_iff.mp h.start.mem_centralizer_szT₁ y hy

theorem V_comm {r : G} (hr : r ∈ V) {y : G} (hy : y ∈ szT₁ L T) : y * r = r * y :=
  mem_centralizer_iff.mp (h.le_centralizer hr) y hy

theorem t_mul_of_mem {r : G} (hr : r ∈ V) : t * r = r⁻¹ * t := by
  calc t * r = (t * r * t⁻¹) * t := by group
    _ = r⁻¹ * t := by rw [h.inv r hr]

theorem sup_le_U₁ : szT₁ L T ⊔ V ≤ U₁ := h.inf_eq ▸ inf_le_left

theorem T₁_le_U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans h.sup_le_U₁

theorem V_le_U₁ : V ≤ U₁ := le_sup_right.trans h.sup_le_U₁

theorem t_mem_U : t ∈ U := by
  rw [← h.sup_eq]
  exact mem_sup_right (mem_zpowers t)

theorem conj_mem_U₁ {x : G} (hx : x ∈ U) {w : G} (hw : w ∈ U₁) : x * w * x⁻¹ ∈ U₁ :=
  (mem_normalizer_iff.mp (h.U₁_normal hx) w).mp hw

theorem t_mem_normalizer_U₁ : t ∈ normalizer (U₁ : Set G) := h.U₁_normal h.t_mem_U

theorem mem_or_mul_t_mem {x : G} (hx : x ∈ U) : x ∈ U₁ ∨ x * t ∈ U₁ :=
  CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers h.t_mul_self h.t_mem_normalizer_U₁
    (by rw [h.sup_eq]; exact hx)

theorem conj_V {x : G} (hx : x ∈ U₁) {r : G} (hr : r ∈ V) : x * r * x⁻¹ ∈ V := by
  have e : x * r * x⁻¹ = r * (r⁻¹ * (x * r * x⁻¹)) := by group
  rw [e]
  exact mul_mem hr (h.le (h.conj_V₁ x hx r hr))

theorem U_le_normalizer_V : U ≤ normalizer (V : Set G) := by
  rw [← h.sup_eq]
  refine sup_le (fun x hx => mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => ?_)
    (zpowers_le.mpr (mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => ?_))
  · simpa using h.conj_V (inv_mem hx) hr
  · rw [h.t_inv, show t * r * t = t * r * t⁻¹ by rw [h.t_inv], h.inv r hr]
    exact inv_mem hr

theorem conj_V_of_mem_U {x : G} (hx : x ∈ U) {r : G} (hr : r ∈ V) : x * r * x⁻¹ ∈ V :=
  (mem_normalizer_iff.mp (h.U_le_normalizer_V hx) r).mp hr

theorem T₁_le_normalizer_V : szT₁ L T ≤ normalizer (V : Set G) := fun y hy =>
  mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => by
    rw [h.V_comm hr (inv_mem hy), inv_mul_cancel_right]
    exact hr

theorem exists_mul_of_mem_sup {x : G} (hx : x ∈ szT₁ L T ⊔ V) :
    ∃ y ∈ szT₁ L T, ∃ r ∈ V, x = y * r := by
  have hx' : x ∈ ((szT₁ L T ⊔ V : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right _ _ h.T₁_le_normalizer_V] at hx'
  obtain ⟨y, hy, r, hr, rfl⟩ := hx'
  exact ⟨y, hy, r, hr, rfl⟩

theorem sup_le_centralizer_V : szT₁ L T ⊔ V ≤ centralizer (V : Set G) :=
  sup_le (fun _ hy => mem_centralizer_iff.mpr fun _ hr => (h.V_comm hr hy).symm)
    (fun r hr => mem_centralizer_iff.mpr fun r' hr' => h.comm r' hr' r hr)

theorem t_mem_normalizer_sup : t ∈ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) := by
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
  obtain ⟨y, hy, r, hr, rfl⟩ := h.exists_mul_of_mem_sup hx
  have e : t⁻¹ * (y * r) * t = y * (t * r * t⁻¹) := by
    calc t⁻¹ * (y * r) * t = (t * y) * r * t := by rw [h.t_inv]; group
      _ = y * t * r * t := by rw [← h.t_comm hy]
      _ = y * (t * r * t⁻¹) := by rw [h.t_inv]; group
  rw [e, h.inv r hr]
  exact mul_mem (mem_sup_left hy) (mem_sup_right (inv_mem hr))

theorem t_mem_normalizer_T₁ : t ∈ normalizer (szT₁ L T : Set G) :=
  mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => by
    rw [h.t_inv, ← h.t_comm hy, mul_assoc, h.t_mul_self, mul_one]
    exact hy

theorem sq_mul_mul_t {y r : G} (hy : y ∈ szT₁ L T) (hr : r ∈ V) : (y * r * t) ^ 2 = y ^ 2 := by
  have e1 : t * y = y * t := (h.t_comm hy).symm
  have e3 : r * y = y * r := (h.V_comm hr hy).symm
  calc (y * r * t) ^ 2 = y * r * (t * y) * r * t := by rw [sq]; group
    _ = y * (r * y) * (t * r) * t := by rw [e1]; group
    _ = y * (y * r) * (r⁻¹ * t) * t := by rw [e3, h.t_mul_of_mem hr]
    _ = y * y * (t * t) := by group
    _ = y ^ 2 := by rw [h.t_mul_self, mul_one, sq]

theorem inf_eq_szA₁ : szT₁ L T ⊓ V = szA₁ (szT₁ L T) :=
  le_antisymm (fun _ hx => mem_szA₁.mpr ⟨(mem_inf.mp hx).1, h.le_centralizer (mem_inf.mp hx).2⟩)
    (le_inf (szA₁_le _) h.le)

theorem pow_mem_szA₁ {r : G} (hr : r ∈ V) : r ^ 2 ^ k ∈ szA₁ (szT₁ L T) := by
  refine h.omega _ (pow_mem hr _) ?_
  rw [← pow_mul, ← pow_succ]
  exact h.pow r hr

theorem comm_t_of_mem_V {r : G} (hr : r ∈ V) : r * t * r⁻¹ * t⁻¹ = r ^ 2 :=
  SzC1.comm_eq_sq_of_inv (h.inv r hr)

theorem comm_t_of_mem_T₁ {y : G} (hy : y ∈ szT₁ L T) : y * t * y⁻¹ * t⁻¹ = 1 := by
  rw [h.t_comm hy]
  group

theorem mem_T₁_of_comm {z : G} (hz : z ∈ U₁) (hzt : z * t = t * z) : z ∈ szT₁ L T := by
  have hz' : z ∈ U ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨h.U₁_le hz, mem_centralizer_singleton_iff.mpr hzt⟩
  rw [h.inf_centralizer] at hz'
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers h.t_mul_self
    h.t_mem_normalizer_T₁ hz' with h1 | h1
  · exact h1
  · exact absurd (by simpa using mul_mem (inv_mem hz) (h.T₁_le_U₁ h1)) h.t_not_mem

theorem chi_mul_left {x x' : G} (hx : x ∈ U₁) (hx' : x' ∈ U₁) {r : G} (hr : r ∈ V) :
    r⁻¹ * (x * x' * r * (x * x')⁻¹) = r⁻¹ * (x * r * x⁻¹) * (r⁻¹ * (x' * r * x'⁻¹)) := by
  have h1 := h.conj_szA₁ x (h.U₁_le hx) _ (h.conj_V₁ x' hx' r hr)
  calc r⁻¹ * (x * x' * r * (x * x')⁻¹) =
        r⁻¹ * (x * r * x⁻¹) * (x * (r⁻¹ * (x' * r * x'⁻¹)) * x⁻¹) := by group
    _ = _ := by rw [h1]

theorem chi_mul_right {x : G} (hx : x ∈ U₁) {r r' : G} (hr : r ∈ V) (hr' : r' ∈ V) :
    (r * r')⁻¹ * (x * (r * r') * x⁻¹) = r⁻¹ * (x * r * x⁻¹) * (r'⁻¹ * (x * r' * x⁻¹)) := by
  have e1 : r'⁻¹ * (r⁻¹ * (x * r * x⁻¹)) = (r⁻¹ * (x * r * x⁻¹)) * r'⁻¹ :=
    h.comm _ (inv_mem hr') _ (h.le (h.conj_V₁ x hx r hr))
  calc (r * r')⁻¹ * (x * (r * r') * x⁻¹) = r'⁻¹ * (r⁻¹ * (x * r * x⁻¹)) * (x * r' * x⁻¹) := by
        group
    _ = (r⁻¹ * (x * r * x⁻¹)) * r'⁻¹ * (x * r' * x⁻¹) := by rw [e1]
    _ = _ := by group

theorem chi_eq_one_of_mem_sup {x : G} (hx : x ∈ szT₁ L T ⊔ V) {r : G} (hr : r ∈ V) :
    r⁻¹ * (x * r * x⁻¹) = 1 := by
  rw [← mem_centralizer_iff.mp (h.sup_le_centralizer_V hx) r hr]
  group

theorem conj_T₁_mem {x : G} (hx : x ∈ U) {y : G} (hy : y ∈ szT₁ L T) : x * y * x⁻¹ ∈ szT₁ L T := by
  have e : x * y * x⁻¹ = y * (y⁻¹ * (x * y * x⁻¹)) := by group
  rw [e]
  exact mul_mem hy (szA₁_le _ (h.conj_T₁ x hx y hy))

theorem delta_mul_left {x x' : G} (hx : x ∈ U) (hx' : x' ∈ U) {y : G} (hy : y ∈ szT₁ L T) :
    y⁻¹ * (x * x' * y * (x * x')⁻¹) = y⁻¹ * (x * y * x⁻¹) * (y⁻¹ * (x' * y * x'⁻¹)) := by
  have h1 := h.conj_szA₁ x hx _ (h.conj_T₁ x' hx' y hy)
  calc y⁻¹ * (x * x' * y * (x * x')⁻¹) =
        y⁻¹ * (x * y * x⁻¹) * (x * (y⁻¹ * (x' * y * x'⁻¹)) * x⁻¹) := by group
    _ = _ := by rw [h1]

theorem delta_mul_right {x : G} (hx : x ∈ U) {y y' : G} (hy : y ∈ szT₁ L T)
    (hy' : y' ∈ szT₁ L T) :
    (y * y')⁻¹ * (x * (y * y') * x⁻¹) = y⁻¹ * (x * y * x⁻¹) * (y'⁻¹ * (x * y' * x⁻¹)) := by
  have e1 : y'⁻¹ * (y⁻¹ * (x * y * x⁻¹)) = (y⁻¹ * (x * y * x⁻¹)) * y'⁻¹ :=
    mem_centralizer_iff.mp (mem_szA₁.mp (h.conj_T₁ x hx y hy)).2 _ (inv_mem hy')
  calc (y * y')⁻¹ * (x * (y * y') * x⁻¹) = y'⁻¹ * (y⁻¹ * (x * y * x⁻¹)) * (x * y' * x⁻¹) := by
        group
    _ = (y⁻¹ * (x * y * x⁻¹)) * y'⁻¹ * (x * y' * x⁻¹) := by rw [e1]
    _ = _ := by group

theorem card_U₁ : Nat.card U₁ = (2 ^ f) ^ (k + 3) := by
  have h2 := RankOne.Endings.relIndex_sup_zpowers_eq_two h.t_not_mem h.t_mem_normalizer_U₁
    h.t_mul_self
  rw [h.sup_eq] at h2
  have h3 := relIndex_mul_card (H := U₁) (K := U)
  rw [h2, inf_of_le_left h.U₁_le, h.card_U] at h3
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3

end Basic

end SzC1Stage

end CFSG.SeitzReduction.RankOne

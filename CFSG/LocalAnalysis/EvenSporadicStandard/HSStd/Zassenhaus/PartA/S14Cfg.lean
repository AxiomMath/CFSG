module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerYCentralizer

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

@[expose] def AutFacts (H : Type) [Group H] : Prop :=
  (∀ x x' : H, orderOf x = 3 → orderOf x' = 3 → ∃ α : MulAut H, α x = x') ∧
  (∀ x : H, orderOf x = 3 → Nat.card (centralizer ({MulAut.conj x} : Set (MulAut H))) = 18) ∧
  Nat.card (MulAut H) = 1440 ∧
  (∀ m n : H, orderOf m = 3 → orderOf n = 3 → MulAut.conj m = MulAut.conj n → m = n)

structure S14Cfg (G : Type) [Group G] [Finite G] (t : G) where
  u : G
  u₁ : G
  x : G
  c₃ : G
  L₁ : Subgroup G
  K₁ : Subgroup G
  X : Subgroup G
  pair : PairData (centralizer ({u} : Set G)) L₁ t
  u_ord : orderOf u = 2
  u₁_mem : u₁ ∈ centralizer ({u} : Set G) ⊓ centralizer (L₁ : Set G) ⊓
    centralizer ((conjSub t L₁ : Subgroup G) : Set G)
  u₁_ord : orderOf u₁ = 2
  u₁_conj : t * u₁ * t⁻¹ = u * u₁
  F_eq : centralizer ({u} : Set G) ⊓ centralizer (L₁ : Set G) ⊓
    centralizer ((conjSub t L₁ : Subgroup G) : Set G) = zpowers u ⊔ zpowers u₁
  card_F : Nat.card ↥(centralizer ({u} : Set G) ⊓ centralizer (L₁ : Set G) ⊓
    centralizer ((conjSub t L₁ : Subgroup G) : Set G)) = 4
  x_mem : x ∈ L₁
  x_ord : orderOf x = 3
  X_le : X ≤ L₁ ⊓ centralizer ({x} : Set G)
  X_card : Nat.card X = 9
  X_three : ∀ g ∈ L₁ ⊓ centralizer ({x} : Set G), orderOf g = 3 → g ∈ X
  X_comm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a
  X_cube : ∀ a ∈ X, a ^ 3 = 1
  card_Cy : Nat.card (centralizer ({x * (t * x * t⁻¹)} : Set G)) = 259200
  c₃_K₁ : c₃ ∈ K₁
  c₃_L₁ : c₃ ∈ L₁
  c₃_ord : orderOf c₃ = 3
  c₃_x : c₃ * x = x * c₃
  c₃_nx : c₃ ∉ zpowers x
  K₁_x : ∀ a ∈ K₁, a * x = x * a
  K₁_xt : ∀ a ∈ K₁, a * (t * x * t⁻¹) = (t * x * t⁻¹) * a
  K₁_K₁t : ∀ a ∈ K₁, ∀ b ∈ K₁, a * (t * b * t⁻¹) = (t * b * t⁻¹) * a
  u₁_S5 : Nonempty (↥(K₁ ⊔ zpowers u₁) ≃* Equiv.Perm (Fin 5))
  u₁_K₁t : ∀ b ∈ K₁, u₁ * (t * b * t⁻¹) = (t * b * t⁻¹) * u₁
  cent_x_xt : centralizer ({x} : Set G) ⊓ centralizer ({t * x * t⁻¹} : Set G) =
    (zpowers x ⊔ zpowers (t * x * t⁻¹)) ⊔ (K₁ ⊔ zpowers u₁) ⊔ conjSub t (K₁ ⊔ zpowers u₁)
  rho_range : pair.rho.range = ⊤
  center_le : ∀ a ∈ L₁, (∀ b ∈ L₁, a * b = b * a) → a = 1 ∨ a = u

namespace S14Cfg

variable {G : Type} [Group G] [Finite G] {t : G} (c : S14Cfg G t)

include c

abbrev xt : G := t * c.x * t⁻¹

abbrev Asub : Subgroup G := zpowers c.x ⊔ zpowers c.xt

abbrev Bsub : Subgroup G := c.K₁ ⊔ zpowers c.u₁

abbrev Btsub : Subgroup G := conjSub t c.Bsub

abbrev Xt : Subgroup G := conjSub t c.X

abbrev Zc : Subgroup G := c.X ⊔ zpowers c.u₁

abbrev Jc : Subgroup G := centralizer (c.Zc : Set G)

abbrev y : G := c.x * c.xt

abbrev P : Subgroup G := centralizer ({c.u} : Set G)

theorem t_sq : t * t = 1 := c.pair.t_sq

theorem t_inv : t⁻¹ = t := c.pair.t_inv

theorem conj_xt : t * c.xt * t⁻¹ = c.x := conj_conj_of_sq c.t_sq c.x

theorem t_mem_P : t ∈ c.P := c.pair.t_mem

theorem u_sq : c.u * c.u = 1 := by
  have := pow_orderOf_eq_one c.u
  rwa [c.u_ord, pow_two] at this

theorem u_ne_one : c.u ≠ 1 := by
  intro h
  have := c.u_ord
  rw [h, orderOf_one] at this
  omega

theorem t_comm_u : t * c.u = c.u * t := mem_centralizer_singleton_iff.1 c.t_mem_P

theorem x_mem_P : c.x ∈ c.P := c.pair.K_le c.x_mem

theorem x_ne_one : c.x ≠ 1 := by
  intro h
  have := c.x_ord
  rw [h, orderOf_one] at this
  omega

theorem x_cube : c.x ^ 3 = 1 := by
  have := pow_orderOf_eq_one c.x
  rwa [c.x_ord] at this

theorem X_le_L₁ : c.X ≤ c.L₁ := fun _ ha => (c.X_le ha).1

theorem x_mem_X : c.x ∈ c.X :=
  c.X_three c.x ⟨c.x_mem, mem_centralizer_singleton_iff.2 rfl⟩ c.x_ord

theorem orderOf_eq_three_of_mem_X {a : G} (ha : a ∈ c.X) (ha1 : a ≠ 1) : orderOf a = 3 :=
  orderOf_eq_prime (c.X_cube a ha) ha1

theorem exists_conj_of_mem_Xt {b : G} (hb : b ∈ c.Xt) : ∃ b' ∈ c.X, t * b' * t⁻¹ = b := by
  obtain ⟨b', hb', rfl⟩ := hb
  exact ⟨b', hb', rfl⟩

theorem Xt_cube {a : G} (ha : a ∈ c.Xt) : a ^ 3 = 1 := by
  obtain ⟨b, hb, rfl⟩ := c.exists_conj_of_mem_Xt ha
  rw [conj_pow, c.X_cube b hb]
  simp

theorem Xt_le : c.Xt ≤ conjSub t c.L₁ := Subgroup.map_mono c.X_le_L₁

theorem xt_mem_Xt : c.xt ∈ c.Xt := ⟨c.x, c.x_mem_X, rfl⟩

theorem xt_cube : c.xt ^ 3 = 1 := c.Xt_cube c.xt_mem_Xt

theorem xt_ne_one : c.xt ≠ 1 := by
  intro h
  apply c.x_ne_one
  simpa using h

theorem orderOf_xt : orderOf c.xt = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime c.xt_cube c.xt_ne_one

theorem comm_L₁_conj {a b : G} (ha : a ∈ c.L₁) (hb : b ∈ conjSub t c.L₁) : Commute a b := by
  obtain ⟨b', hb', rfl⟩ := hb
  exact c.pair.comm a ha b' hb'

theorem c₃_cube : c.c₃ ^ 3 = 1 := by
  have := pow_orderOf_eq_one c.c₃
  rwa [c.c₃_ord] at this

theorem c₃_ne_one : c.c₃ ≠ 1 := by
  intro h
  have := c.c₃_ord
  rw [h, orderOf_one] at this
  omega

theorem c₃_mem_X : c.c₃ ∈ c.X :=
  c.X_three c.c₃ ⟨c.c₃_L₁, mem_centralizer_singleton_iff.2 c.c₃_x⟩ c.c₃_ord

theorem eq_one_of_central_cube {a : G} (ha : a ∈ c.L₁) (hc : ∀ b ∈ c.L₁, a * b = b * a)
    (h3 : a ^ 3 = 1) : a = 1 := by
  rcases c.center_le a ha hc with rfl | rfl
  · rfl
  · exfalso
    have : c.u ^ 3 = c.u := by rw [pow_succ, pow_two, c.u_sq, one_mul]
    rw [this] at h3
    exact c.u_ne_one h3

theorem eq_one_of_mem_L₁_of_mem_conj {a : G} (ha : a ∈ c.L₁) (hb : a ∈ conjSub t c.L₁)
    (h3 : a ^ 3 = 1) : a = 1 :=
  c.eq_one_of_central_cube ha (fun _ hb' => (c.comm_L₁_conj hb' hb).eq.symm) h3

theorem X_inf_Xt : c.X ⊓ c.Xt = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [mem_bot]
  exact c.eq_one_of_mem_L₁_of_mem_conj (c.X_le_L₁ ha.1) (c.Xt_le ha.2) (c.X_cube a ha.1)

theorem commute_X_Xt {a b : G} (ha : a ∈ c.X) (hb : b ∈ c.Xt) : Commute a b :=
  c.comm_L₁_conj (c.X_le_L₁ ha) (c.Xt_le hb)

theorem card_Xt : Nat.card c.Xt = 9 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, c.X_card]

theorem zpowers_x_inf_zpowers_c₃ : zpowers c.x ⊓ zpowers c.c₃ = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [mem_bot]
  by_contra hz
  have e1 := zpowers_eq_of_mem_of_ne_one c.x_cube c.x_ne_one hz1 hz
  have e2 := zpowers_eq_of_mem_of_ne_one c.c₃_cube c.c₃_ne_one hz2 hz
  apply c.c₃_nx
  rw [← e1, e2]
  exact mem_zpowers _

theorem X_eq : c.X = zpowers c.x ⊔ zpowers c.c₃ := by
  have hle : zpowers c.x ⊔ zpowers c.c₃ ≤ c.X :=
    sup_le (zpowers_le.2 c.x_mem_X) (zpowers_le.2 c.c₃_mem_X)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have hcm : Cm (zpowers c.x) (zpowers c.c₃) := cm_zpowers_zpowers c.c₃_x.symm
  rw [card_sup_of_cm hcm c.zpowers_x_inf_zpowers_c₃, Nat.card_zpowers, Nat.card_zpowers,
    c.x_ord, c.c₃_ord, c.X_card]

theorem u₁_comm_L₁ {k : G} (hk : k ∈ c.L₁) : k * c.u₁ = c.u₁ * k :=
  mem_centralizer_iff.1 c.u₁_mem.1.2 k hk

theorem u₁_comm_L₁t {k : G} (hk : k ∈ conjSub t c.L₁) : k * c.u₁ = c.u₁ * k :=
  mem_centralizer_iff.1 c.u₁_mem.2 k hk

theorem u₁_mul_u : c.u₁ * c.u = c.u * c.u₁ := mem_centralizer_singleton_iff.1 c.u₁_mem.1.1

theorem u₁_sq : c.u₁ * c.u₁ = 1 := by
  have := pow_orderOf_eq_one c.u₁
  rwa [c.u₁_ord, pow_two] at this

theorem u₁_ne_one : c.u₁ ≠ 1 := by
  intro h
  have := c.u₁_ord
  rw [h, orderOf_one] at this
  omega

theorem u₁_cube : c.u₁ ^ 3 = c.u₁ := by
  rw [pow_succ, pow_two, c.u₁_sq, one_mul]

theorem cm_x_K₁ : Cm (zpowers c.x) c.K₁ := cm_zpowers_left fun b hb => (c.K₁_x b hb).symm

theorem cm_xt_K₁ : Cm (zpowers c.xt) c.K₁ := cm_zpowers_left fun b hb => (c.K₁_xt b hb).symm

theorem cm_x_u₁ : Cm (zpowers c.x) (zpowers c.u₁) :=
  cm_zpowers_zpowers (c.u₁_comm_L₁ c.x_mem)

theorem cm_xt_u₁ : Cm (zpowers c.xt) (zpowers c.u₁) :=
  cm_zpowers_zpowers (c.u₁_comm_L₁t (c.Xt_le c.xt_mem_Xt))

theorem cm_x_B : Cm (zpowers c.x) c.Bsub := Cm.sup_right c.cm_x_K₁ c.cm_x_u₁

theorem cm_xt_B : Cm (zpowers c.xt) c.Bsub := Cm.sup_right c.cm_xt_K₁ c.cm_xt_u₁

theorem cm_A_B : Cm c.Asub c.Bsub := Cm.sup_left c.cm_x_B c.cm_xt_B

theorem cm_x_Bt : Cm (zpowers c.x) c.Btsub := by
  have := Cm.conj t c.cm_xt_B
  rwa [conjSub_zpowers, c.conj_xt] at this

theorem cm_xt_Bt : Cm (zpowers c.xt) c.Btsub := by
  have := Cm.conj t c.cm_x_B
  rwa [conjSub_zpowers] at this

theorem cm_A_Bt : Cm c.Asub c.Btsub := Cm.sup_left c.cm_x_Bt c.cm_xt_Bt

theorem cm_K₁_conjK₁ : Cm c.K₁ (conjSub t c.K₁) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  obtain ⟨k, hk, rfl⟩ := mem_conjSub.1 hb
  exact (c.K₁_K₁t a ha k hk).symm

theorem cm_u₁_conjK₁ : Cm (zpowers c.u₁) (conjSub t c.K₁) := by
  refine cm_zpowers_left fun b hb => ?_
  obtain ⟨k, hk, rfl⟩ := mem_conjSub.1 hb
  exact c.u₁_K₁t k hk

theorem cm_K₁_conju₁ : Cm c.K₁ (conjSub t (zpowers c.u₁)) := by
  have := Cm.conj t c.cm_u₁_conjK₁
  rw [conjSub_conjSub c.t_sq] at this
  exact this.symm

theorem cm_u₁_conju₁ : Cm (zpowers c.u₁) (conjSub t (zpowers c.u₁)) := by
  rw [conjSub_zpowers]
  refine cm_zpowers_zpowers ?_
  rw [c.u₁_conj]
  calc c.u₁ * (c.u * c.u₁) = (c.u₁ * c.u) * c.u₁ := by group
    _ = (c.u * c.u₁) * c.u₁ := by rw [c.u₁_mul_u]

theorem cm_B_Bt : Cm c.Bsub c.Btsub := by
  have h : Cm (c.K₁ ⊔ zpowers c.u₁) (conjSub t c.K₁ ⊔ conjSub t (zpowers c.u₁)) :=
    Cm.sup_left (Cm.sup_right c.cm_K₁_conjK₁ c.cm_K₁_conju₁)
      (Cm.sup_right c.cm_u₁_conjK₁ c.cm_u₁_conju₁)
  rwa [← conjSub_sup] at h

theorem cm_AB_Bt : Cm (c.Asub ⊔ c.Bsub) c.Btsub := Cm.sup_left c.cm_A_Bt c.cm_B_Bt

theorem Zc_le_AB : c.Zc ≤ c.Asub ⊔ c.Bsub := by
  refine sup_le ?_ (zpowers_le.2 (mem_sup_right (mem_sup_right (mem_zpowers _))))
  rw [c.X_eq]
  exact sup_le (le_sup_left.trans le_sup_left)
    (zpowers_le.2 (mem_sup_right (mem_sup_left c.c₃_K₁)))

theorem cm_X_Xt : Cm c.X c.Xt := by
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  exact (c.commute_X_Xt ha hb).eq.symm

theorem cm_X_u₁ : Cm c.X (zpowers c.u₁) := by
  refine Cm.symm (cm_zpowers_left fun b hb => ?_)
  exact (c.u₁_comm_L₁ (c.X_le_L₁ hb)).symm

theorem cm_Z_Xt : Cm c.Zc c.Xt := by
  refine Cm.sup_left c.cm_X_Xt ?_
  refine cm_zpowers_left fun b hb => ?_
  exact (c.u₁_comm_L₁t (c.Xt_le hb)).symm

theorem cm_Z_xt : Cm c.Zc (zpowers c.xt) :=
  c.cm_Z_Xt.mono le_rfl (zpowers_le.2 c.xt_mem_Xt)

theorem cm_Z_Bt : Cm c.Zc c.Btsub := c.cm_AB_Bt.mono c.Zc_le_AB le_rfl

theorem cm_Z_Z : Cm c.Zc c.Zc := by
  have h1 : Cm c.X c.X := fun a ha => mem_centralizer_iff.2 fun b hb => (c.X_comm a ha b hb).symm
  exact Cm.sup_left (Cm.sup_right h1 c.cm_X_u₁)
    (Cm.sup_right c.cm_X_u₁.symm (cm_zpowers_zpowers rfl))

theorem Zc_le_Jc : c.Zc ≤ c.Jc := c.cm_Z_Z

theorem xt_mem_J : c.xt ∈ c.Jc := c.cm_Z_xt.symm (mem_zpowers _)

theorem Xt_le_J : c.Xt ≤ c.Jc := c.cm_Z_Xt.symm

theorem Bt_le_J : c.Btsub ≤ c.Jc := c.cm_Z_Bt.symm

theorem mem_Zc_iff {z : G} : z ∈ c.Zc ↔ ∃ a ∈ c.X, ∃ w ∈ zpowers c.u₁, z = a * w :=
  mem_sup_iff_of_cm c.cm_X_u₁

theorem mem_X_of_cube {z : G} (hz : z ∈ c.Zc) (h3 : z ^ 3 = 1) : z ∈ c.X := by
  obtain ⟨a, ha, w, hw, rfl⟩ := c.mem_Zc_iff.1 hz
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self c.u₁_sq hw with rfl | rfl
  · simpa using ha
  · exfalso
    have hc : Commute a c.u₁ := (c.cm_X_u₁.comm ha (mem_zpowers _) : a * c.u₁ = c.u₁ * a)
    rw [hc.mul_pow, c.X_cube a ha, c.u₁_cube, one_mul] at h3
    exact c.u₁_ne_one h3

theorem eq_one_of_mem_Zc_Xt {z : G} (hz : z ∈ c.Zc) (hz' : z ∈ c.Xt) : z = 1 := by
  have h := c.mem_X_of_cube hz (c.Xt_cube hz')
  have : z ∈ c.X ⊓ c.Xt := ⟨h, hz'⟩
  rw [c.X_inf_Xt, mem_bot] at this
  exact this

@[expose] noncomputable def eB : ↥c.Bsub ≃* Equiv.Perm (Fin 5) := c.u₁_S5.some

theorem B_cent {b : G} (hb : b ∈ c.Bsub) (h1 : b * c.c₃ = c.c₃ * b) (h2 : b * c.u₁ = c.u₁ * b) :
    ∃ i : Fin 3, ∃ j : Fin 2, b = c.c₃ ^ (i : ℕ) * c.u₁ ^ (j : ℕ) := by
  let c3B : ↥c.Bsub := ⟨c.c₃, mem_sup_left c.c₃_K₁⟩
  let u1B : ↥c.Bsub := ⟨c.u₁, mem_sup_right (mem_zpowers _)⟩
  let bB : ↥c.Bsub := ⟨b, hb⟩
  have e1 : c.eB c3B * (c.eB c3B * c.eB c3B) = 1 := by
    rw [← map_mul, ← map_mul, ← map_one c.eB]
    congr 1
    apply Subtype.ext
    have := c.c₃_cube
    simpa [pow_succ, mul_assoc] using this
  have e2 : c.eB c3B ≠ 1 := by
    intro h
    apply c.c₃_ne_one
    have := c.eB.injective (h.trans (map_one c.eB).symm)
    exact congrArg Subtype.val this
  have e3 : c.eB u1B * c.eB u1B = 1 := by
    rw [← map_mul, ← map_one c.eB]
    congr 1
    exact Subtype.ext c.u₁_sq
  have e4 : c.eB u1B ≠ 1 := by
    intro h
    apply c.u₁_ne_one
    have := c.eB.injective (h.trans (map_one c.eB).symm)
    exact congrArg Subtype.val this
  have e5 : c.eB c3B * c.eB u1B = c.eB u1B * c.eB c3B := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (c.u₁_comm_L₁ c.c₃_L₁)
  have e6 : c.eB bB * c.eB c3B = c.eB c3B * c.eB bB := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h1
  have e7 : c.eB bB * c.eB u1B = c.eB u1B * c.eB bB := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h2
  obtain ⟨i, j, hij⟩ := s5_centralizer_pair _ _ e1 e2 e3 e4 e5 _ e6 e7
  refine ⟨i, j, ?_⟩
  have : bB = c3B ^ (i : ℕ) * u1B ^ (j : ℕ) := by
    apply c.eB.injective
    rw [hij, map_mul, map_pow, map_pow]
  exact congrArg Subtype.val this

abbrev Rc : Subgroup G := c.Jc ⊓ centralizer ({c.xt} : Set G)

theorem x_comm_xt : c.x * c.xt = c.xt * c.x := (c.pair.comm c.x c.x_mem c.x c.x_mem).eq

theorem cm_x_xt : Cm (zpowers c.x) (zpowers c.xt) := cm_zpowers_zpowers c.x_comm_xt

theorem Rc_le : c.Rc ≤ c.Zc ⊔ zpowers c.xt ⊔ c.Btsub := by
  rintro g ⟨hgJ, hgxt⟩
  have hx : c.x ∈ c.Zc := mem_sup_left c.x_mem_X
  have hgx : g ∈ centralizer ({c.x} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hgJ c.x hx).symm
  have hD : g ∈ centralizer ({c.x} : Set G) ⊓ centralizer ({t * c.x * t⁻¹} : Set G) :=
    ⟨hgx, hgxt⟩
  rw [c.cent_x_xt] at hD
  obtain ⟨m, hm, b', hb', rfl⟩ := (mem_sup_iff_of_cm c.cm_AB_Bt).1 hD
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_cm c.cm_A_B).1 hm
  have key : ∀ e ∈ c.Bsub, e ∈ c.Zc → e * (a * b * b') = (a * b * b') * e →
      e * b = b * e := fun e he _ h =>
    comm_middle (c.cm_A_B.comm ha he).symm (c.cm_B_Bt.comm he hb') h
  have hc3 : c.c₃ * b = b * c.c₃ := key c.c₃ (mem_sup_left c.c₃_K₁) (mem_sup_left c.c₃_mem_X)
    (mem_centralizer_iff.1 hgJ c.c₃ (mem_sup_left c.c₃_mem_X))
  have hu1 : c.u₁ * b = b * c.u₁ := key c.u₁ (mem_sup_right (mem_zpowers _))
    (mem_sup_right (mem_zpowers _))
    (mem_centralizer_iff.1 hgJ c.u₁ (mem_sup_right (mem_zpowers _)))
  obtain ⟨i, j, hij⟩ := c.B_cent hb hc3.symm hu1.symm
  have hbZ : b ∈ c.Zc := by
    rw [hij]
    exact mul_mem (mem_sup_left (pow_mem c.c₃_mem_X _))
      (mem_sup_right (pow_mem (mem_zpowers _) _))
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff_of_cm c.cm_x_xt).1 ha
  have hpZ : p ∈ c.Zc := mem_sup_left (zpowers_le.2 c.x_mem_X hp)
  have hqb : q * b = b * q := c.cm_A_B.comm (mem_sup_right hq) hb
  have e : p * q * b * b' = (p * b) * q * b' := by
    calc p * q * b * b' = p * (q * b) * b' := by group
      _ = p * (b * q) * b' := by rw [hqb]
      _ = (p * b) * q * b' := by group
  rw [e]
  exact mul_mem (mul_mem (mem_sup_left (mem_sup_left (mul_mem hpZ hbZ)))
    (mem_sup_left (mem_sup_right hq))) (mem_sup_right hb')

theorem le_Rc : c.Zc ⊔ zpowers c.xt ⊔ c.Btsub ≤ c.Rc := by
  refine le_inf (sup_le (sup_le c.Zc_le_Jc (zpowers_le.2 c.xt_mem_J)) c.Bt_le_J) ?_
  refine sup_le (sup_le ?_ ?_) ?_
  · intro z hz
    exact mem_centralizer_singleton_iff.2 (c.cm_Z_xt.comm hz (mem_zpowers _))
  · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
  · intro b hb
    exact mem_centralizer_singleton_iff.2 (c.cm_xt_Bt.comm (mem_zpowers _) hb).symm

theorem centralizer_xt_inf_J :
    c.Jc ⊓ centralizer ({c.xt} : Set G) =
      c.Zc ⊔ zpowers c.xt ⊔ conjSub t (c.K₁ ⊔ zpowers c.u₁) :=
  le_antisymm c.Rc_le c.le_Rc

end S14Cfg

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

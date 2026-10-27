module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTenBasic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen

open Subgroup

variable {G : Type} [Group G]

theorem map_conj_eq_of_mem_normalizer [Finite G] {B : Subgroup G} {g : G}
    (hg : g ∈ normalizer (B : Set G)) : B.map (MulAut.conj g).toMonoidHom = B := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hg x).mp hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem map_conj_inf_centralizer [Finite G] {B : Subgroup G} {g : G}
    (hg : g ∈ normalizer (B : Set G)) (u : G) :
    (B ⊓ centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom =
      B ⊓ centralizer ({g * u * g⁻¹} : Set G) := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, map_conj_eq_of_mem_normalizer hg,
    centralizer_conj]

theorem card_inf_centralizer_conj' [Finite G] {B : Subgroup G} {g : G}
    (hg : g ∈ normalizer (B : Set G)) (u : G) :
    Nat.card (B ⊓ centralizer ({g * u * g⁻¹} : Set G) : Subgroup G) =
      Nat.card (B ⊓ centralizer ({u} : Set G) : Subgroup G) := by
  rw [← map_conj_inf_centralizer hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]

variable [Finite G] {z : G} {fr : JankoFrame G z}

namespace Hyp

omit [Finite G] in
theorem M_le_C₁ (fr : JankoFrame G z) : fr.M ≤ centralizer (fr.P₁ : Set G) :=
  oddCoreOf_le _

omit [Finite G] in
theorem C₁_le_normalizer_M (fr : JankoFrame G z) :
    centralizer (fr.P₁ : Set G) ≤ normalizer (fr.M : Set G) :=
  le_normalizer_oddCoreOf _

theorem odd_card_M (fr : JankoFrame G z) : Odd (Nat.card fr.M) :=
  odd_card_oddCoreOf _

theorem P₁_le_M (fr : JankoFrame G z) : fr.P₁ ≤ fr.M :=
  le_oddCoreOf (P₁_le_C₁ fr) (C₁_le_normalizer_P₁ fr) (by rw [card_P₁]; decide)

theorem t_mem_normalizer_C₁ (fr : JankoFrame G z) :
    fr.t ∈ normalizer (centralizer (fr.P₁ : Set G) : Set G) :=
  mem_normalizer_centralizer (t_mem_normalizer_P₁ fr)

theorem t_mem_normalizer_M (fr : JankoFrame G z) : fr.t ∈ normalizer (fr.M : Set G) :=
  mem_normalizer_oddCoreOf (t_mem_normalizer_C₁ fr)

omit [Finite G] in
theorem z_mem_C₁ (fr : JankoFrame G z) : z ∈ centralizer (fr.P₁ : Set G) :=
  fr.F_le_centralizer fr.z_mem_F

omit [Finite G] in
theorem ℓ_mem_C₁ (fr : JankoFrame G z) : fr.ℓ ∈ centralizer (fr.P₁ : Set G) :=
  fr.F_le_centralizer fr.ℓ_mem_F

theorem odd_orderOf_of_mem_M (fr : JankoFrame G z) {x : G} (hx : x ∈ fr.M) :
    Odd (orderOf x) :=
  Odd.of_dvd_nat (odd_card_M fr) (Subgroup.orderOf_dvd_natCard _ hx)

theorem z_not_mem_M (h : Hyp fr) : z ∉ fr.M := fun hz => by
  have := odd_orderOf_of_mem_M fr hz
  rw [h.set.orderOf_z] at this
  exact (Nat.not_odd_iff_even.mpr even_two) this

theorem oddCore_eq_pPrimeCore (X : Type*) [Group X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem z_mem_S₁ (fr : JankoFrame G z) : z ∈ fr.S₁ := by
  obtain ⟨e⟩ := fr.S₁_quaternion
  have hcard : Nat.card fr.S₁ = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := fr.S₁) 2 (by rw [hcard]; norm_num)
  have hx' : orderOf (x : G) = 2 := by rwa [Subgroup.orderOf_coe]
  have := fr.eq_z_of_mem_F x (fr.S₁_le x.2) hx'
  have hx2 : (x : G) ∈ fr.S₁ := x.2
  rwa [this] at hx2

theorem exists_mul_of_mem_C₁ (h : Hyp fr) {g : G} (hg : g ∈ centralizer (fr.P₁ : Set G)) :
    ∃ c ∈ centralizer (fr.P₁ : Set G) ⊓ centralizer ({z} : Set G), ∃ k ∈ fr.M, g = c * k := by
  set C := centralizer (fr.P₁ : Set G)
  obtain ⟨Q, hQ⟩ := h.p7.isSylowOf_S₁
  obtain ⟨e⟩ := fr.S₁_quaternion
  have hquat : Nonempty ((Q : Subgroup C) ≃* QuaternionGroup (2 ^ (4 - 2))) :=
    ⟨((Q : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).trans
      ((MulEquiv.subgroupCongr hQ).trans e)⟩
  set zC : C := ⟨z, z_mem_C₁ fr⟩
  have hzQ : zC ∈ (Q : Subgroup C) := by
    have hz : z ∈ (Q : Subgroup C).map C.subtype := hQ ▸ z_mem_S₁ fr
    obtain ⟨w, hw, hwz⟩ := hz
    have : w = zC := Subtype.ext hwz
    exact this ▸ hw
  have hzord : orderOf zC = 2 := by
    rw [← Subgroup.orderOf_coe]; exact h.set.orderOf_z
  have hzz : zC * zC = 1 := (Walter.J1.orderOf_eq_two_iff.mp hzord).1
  have hcen := (CFSG.Adapters.brauer_suzuki 4 (by norm_num) Q hquat zC hzQ hzord).2
  obtain ⟨c, hc, k, hk, hgck⟩ := CFSG.Adapters.eq_centralizer_mul_oddCore hzz hcen ⟨g, hg⟩
  refine ⟨c, ⟨c.2, ?_⟩, k, ?_, congrArg Subtype.val hgck⟩
  · exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))
  · rw [oddCore_eq_pPrimeCore] at hk
    exact ⟨k, hk, rfl⟩

theorem centralizer_P₁_eq (h : Hyp fr) : centralizer (fr.P₁ : Set G) = fr.M ⊔ fr.F := by
  refine le_antisymm (fun g hg => ?_) (sup_le (M_le_C₁ fr) fr.F_le_centralizer)
  obtain ⟨c, hc, k, hk, rfl⟩ := exists_mul_of_mem_C₁ h hg
  rw [fr.centralizer_P₁] at hc
  refine mul_mem ?_ (mem_sup_left hk)
  exact (sup_le_sup_right (P₁_le_M fr) _) hc

theorem M_inf_F (h : Hyp fr) : fr.M ⊓ fr.F = ⊥ := by
  by_contra hne
  have hFn : fr.F ≤ normalizer ((fr.M ⊓ fr.F : Subgroup G) : Set G) := fun f hf =>
    inf_mem_normalizer (C₁_le_normalizer_M fr (fr.F_le_centralizer hf))
      (Subgroup.le_normalizer hf)
  exact z_not_mem_M h (fr.z_mem_of_normal _ inf_le_right hFn hne).1

theorem mem_P₁_sup_F (fr : JankoFrame G z) {x : G} (hx : x ∈ fr.P₁ ⊔ fr.F) :
    ∃ p ∈ fr.P₁, ∃ f ∈ fr.F, p * f = x := by
  have hle : fr.F ≤ normalizer (fr.P₁ : Set G) :=
    fr.F_le_centralizer.trans (C₁_le_normalizer_P₁ fr)
  have hx' : x ∈ ((fr.P₁ ⊔ fr.F : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hx'
  obtain ⟨p, hp, f, hf, hpf⟩ := Set.mem_mul.mp hx'
  exact ⟨p, hp, f, hf, hpf⟩

theorem M_inf_H (h : Hyp fr) : fr.M ⊓ centralizer ({z} : Set G) = fr.P₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf (P₁_le_M fr) (P₁_le_H fr))
  have hxC : x ∈ centralizer (fr.P₁ : Set G) ⊓ centralizer ({z} : Set G) :=
    ⟨M_le_C₁ fr hx.1, hx.2⟩
  rw [fr.centralizer_P₁] at hxC
  obtain ⟨p, hp, f, hf, rfl⟩ := mem_P₁_sup_F fr hxC
  have hfM : f ∈ fr.M := by
    have := fr.M.mul_mem (fr.M.inv_mem (P₁_le_M fr hp)) hx.1
    rwa [inv_mul_cancel_left] at this
  have hf1 : f = 1 := by
    have : f ∈ fr.M ⊓ fr.F := ⟨hfM, hf⟩
    rwa [M_inf_F h, mem_bot] at this
  rw [hf1, mul_one]
  exact hp

theorem M_ne_P₁ (h : Hyp fr) : fr.M ≠ fr.P₁ := by
  intro heq
  apply h.not_le
  rw [centralizer_P₁_eq h, heq]
  exact sup_le (P₁_le_H fr) fr.F_le

omit [Finite G] in
theorem t_ne_one (fr : JankoFrame G z) : fr.t ≠ 1 :=
  (Walter.J1.orderOf_eq_two_iff.mp fr.orderOf_t).2

theorem eq_one_of_mem_M (h : Hyp fr) {x : G} (hxM : x ∈ fr.M)
    (hxt : x ∈ centralizer ({fr.t} : Set G)) (hxz : x ∈ centralizer ({z} : Set G)) : x = 1 := by
  have hxP : x ∈ fr.P₁ := M_inf_H h ▸ (⟨hxM, hxz⟩ : x ∈ fr.M ⊓ centralizer ({z} : Set G))
  have : x ∈ fr.P₁ ⊓ centralizer ({fr.t} : Set G) := ⟨hxP, hxt⟩
  rwa [P₁_inf_centralizer_t, mem_bot] at this

theorem card_eq_of_le_M (h : Hyp fr) {B : Subgroup G} (hP₁B : fr.P₁ ≤ B) (hBM : B ≤ fr.M)
    (ht : fr.t ∈ normalizer (B : Set G)) (hz : z ∈ normalizer (B : Set G)) :
    Nat.card B = 3 * Nat.card (B ⊓ centralizer ({fr.t} : Set G) : Subgroup G) *
      Nat.card (B ⊓ centralizer ({fr.t * z} : Set G) : Subgroup G) := by
  have hBodd : Odd (Nat.card B) := Odd.of_dvd_nat (odd_card_M fr) (Subgroup.card_dvd_of_le hBM)
  have key := Walter.J1.card_mul_card_sq_eq_mul (t_mul_t fr) (z_mul_z fr) (t_ne_one fr)
    (z_ne_one fr) fr.t_ne (t_mul_z fr) B ht hz hBodd
  have h1 : B ⊓ centralizer ({fr.t} : Set G) ⊓ centralizer ({z} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxB, hxt⟩, hxz⟩
    exact eq_one_of_mem_M h (hBM hxB) hxt hxz
  have h2 : B ⊓ centralizer ({z} : Set G) = fr.P₁ := by
    refine le_antisymm (fun x hx => ?_) (le_inf hP₁B (P₁_le_H fr))
    exact M_inf_H h ▸ (⟨hBM hx.1, hx.2⟩ : x ∈ fr.M ⊓ centralizer ({z} : Set G))
  rw [h1, h2, card_bot, card_P₁] at key
  rw [one_pow, mul_one] at key
  rw [key]
  ring

theorem card_inf_tz_eq (fr : JankoFrame G z) {B : Subgroup G}
    (hy : fr.ℓ ^ 2 ∈ normalizer (B : Set G)) :
    Nat.card (B ⊓ centralizer ({fr.t * z} : Set G) : Subgroup G) =
      Nat.card (B ⊓ centralizer ({fr.t} : Set G) : Subgroup G) := by
  rw [← y_conj_t fr]
  exact card_inf_centralizer_conj' hy fr.t

omit [Finite G] in
theorem z_mem_normalizer_M (fr : JankoFrame G z) : z ∈ normalizer (fr.M : Set G) :=
  C₁_le_normalizer_M fr (z_mem_C₁ fr)

omit [Finite G] in
theorem y_mem_normalizer_M (fr : JankoFrame G z) : fr.ℓ ^ 2 ∈ normalizer (fr.M : Set G) :=
  C₁_le_normalizer_M fr (pow_mem (ℓ_mem_C₁ fr) 2)

theorem card_M_eq (h : Hyp fr) : Nat.card fr.M = 3 * Nat.card fr.At ^ 2 := by
  rw [card_eq_of_le_M h (P₁_le_M fr) le_rfl (t_mem_normalizer_M fr) (z_mem_normalizer_M fr),
    card_inf_tz_eq fr (y_mem_normalizer_M fr)]
  change 3 * Nat.card fr.At * Nat.card fr.At = _
  ring

theorem map_y_At (fr : JankoFrame G z) :
    fr.At.map (MulAut.conj (fr.ℓ ^ 2)).toMonoidHom = fr.Atz := by
  rw [JankoFrame.At, map_conj_inf_centralizer (y_mem_normalizer_M fr), y_conj_t]
  rfl

theorem card_Atz_eq (fr : JankoFrame G z) : Nat.card fr.Atz = Nat.card fr.At := by
  rw [← map_y_At fr, Subgroup.card_map_of_injective (MulAut.conj _).injective]

theorem At_inf_H (h : Hyp fr) : fr.At ⊓ centralizer ({z} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨hxM, hxt⟩, hxz⟩
  exact eq_one_of_mem_M h hxM hxt hxz

theorem At_ne_bot (h : Hyp fr) : fr.At ≠ ⊥ := by
  intro hA
  apply M_ne_P₁ h
  refine (Subgroup.eq_of_le_of_card_ge (P₁_le_M fr) ?_).symm
  rw [card_M_eq h, hA, card_bot, card_P₁]
  norm_num

omit [Finite G] in
theorem At_le_M (fr : JankoFrame G z) : fr.At ≤ fr.M := inf_le_left

omit [Finite G] in
theorem At_le_t (fr : JankoFrame G z) : fr.At ≤ centralizer ({fr.t} : Set G) := inf_le_right

omit [Finite G] in
theorem z_mem_normalizer_At (fr : JankoFrame G z) : z ∈ normalizer (fr.At : Set G) := by
  have hzt : z ∈ centralizer ({fr.t} : Set G) :=
    mem_centralizer_singleton_iff.mpr (t_mul_z fr).symm
  exact inf_mem_normalizer (z_mem_normalizer_M fr) (Subgroup.le_normalizer hzt)

theorem z_conj_of_mem_At (h : Hyp fr) {x : G} (hx : x ∈ fr.At) : z * x * z⁻¹ = x⁻¹ :=
  Walter.J1.inv_of_inf_centralizer_eq_bot (z_mul_z fr) (z_mem_normalizer_At fr) (At_inf_H h) x hx

theorem At_comm (h : Hyp fr) {a b : G} (ha : a ∈ fr.At) (hb : b ∈ fr.At) : a * b = b * a :=
  (mem_centralizer_iff.mp (Walter.J1.le_centralizer_of_inv (fun _ hx => z_conj_of_mem_At h hx)
    ha) b hb).symm

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen

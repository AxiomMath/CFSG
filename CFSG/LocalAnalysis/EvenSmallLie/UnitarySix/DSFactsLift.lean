module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsModel

public section

namespace CFSG.EvenSmallLie.UnitarySix

open Subgroup CFSG.Quasithin

variable {G : Type} [Group G] {L : Subgroup G} {Q : Type} [Group Q]

@[expose] def liftSub (π : L →* Q) (X : Subgroup Q) : Subgroup G :=
  (X.comap π).map L.subtype

theorem mem_liftSub {π : L →* Q} {X : Subgroup Q} {g : G} :
    g ∈ liftSub π X ↔ ∃ h : g ∈ L, π ⟨g, h⟩ ∈ X := by
  simp only [liftSub, mem_map, mem_comap, coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hX⟩
    exact ⟨⟨g, h⟩, hX, rfl⟩

theorem liftSub_le (π : L →* Q) (X : Subgroup Q) : liftSub π X ≤ L :=
  map_subtype_le _

@[expose] def imgSub (π : L →* Q) (B : Subgroup G) : Subgroup Q :=
  (B.subgroupOf L).map π

theorem le_liftSub_imgSub (π : L →* Q) {B : Subgroup G} (hB : B ≤ L) :
    B ≤ liftSub π (imgSub π B) := fun b hb =>
  mem_liftSub.2 ⟨hB hb, ⟨⟨b, hB hb⟩, hb, rfl⟩⟩

structure IsDoubleCover (t : G) (L : Subgroup G) (π : L →* Q) : Prop where
  surj : Function.Surjective π
  ker : ∀ y : L, π y = 1 ↔ (y : G) = 1 ∨ (y : G) = t
  t_mem : t ∈ L
  le_centralizer : L ≤ centralizer {t}
  orderOf_t : orderOf t = 2

theorem card_map_eq_of_ker_eq {X Y Z : Type*} [Group X] [Group Y] [Group Z] {f : X →* Y}
    {g : X →* Z} (hfg : f.ker = g.ker) (M : Subgroup X) :
    Nat.card (M.map f) = Nat.card (M.map g) := by
  rw [← MonoidHom.domRestrict_range, ← MonoidHom.domRestrict_range, ← Subgroup.index_ker,
    ← Subgroup.index_ker, MonoidHom.ker_domRestrict, MonoidHom.ker_domRestrict, hfg]

theorem liftSub_map_eq {π : L →* Q} {M : Subgroup L} (hM : π.ker ≤ M) :
    liftSub π (M.map π) = M.map L.subtype := by
  rw [liftSub, Subgroup.comap_map_eq, sup_eq_left.2 hM]

namespace IsDoubleCover

variable {t : G} {π : L →* Q}

theorem t_ne_one (H : IsDoubleCover t L π) : t ≠ 1 := fun h => by
  have := H.orderOf_t
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem t_sq (H : IsDoubleCover t L π) : t ^ 2 = 1 := by
  rw [← H.orderOf_t]
  exact pow_orderOf_eq_one t

theorem pi_t (H : IsDoubleCover t L π) : π ⟨t, H.t_mem⟩ = 1 :=
  (H.ker _).2 (Or.inr rfl)

theorem t_mem_liftSub (H : IsDoubleCover t L π) (X : Subgroup Q) : t ∈ liftSub π X :=
  mem_liftSub.2 ⟨H.t_mem, by rw [H.pi_t]; exact X.one_mem⟩

theorem comm_t (H : IsDoubleCover t L π) {g : G} (hg : g ∈ L) : g * t = t * g :=
  mem_centralizer_singleton_iff.1 (H.le_centralizer hg)

theorem eq_or_eq_mul_of_pi_eq (H : IsDoubleCover t L π) {y y' : L} (h : π y = π y') :
    (y' : G) = y ∨ (y' : G) = y * t := by
  have h1 : π (y⁻¹ * y') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  rcases (H.ker _).1 h1 with h2 | h2
  · left
    simp only [coe_mul, coe_inv] at h2
    rw [← inv_mul_eq_one.1 h2]
  · right
    simp only [coe_mul, coe_inv] at h2
    rw [← h2, mul_inv_cancel_left]

theorem card_ker (H : IsDoubleCover t L π) : Nat.card π.ker = 2 := by
  have hne : (⟨⟨t, H.t_mem⟩, (H.ker _).2 (Or.inr rfl)⟩ : π.ker) ≠ 1 := fun h =>
    H.t_ne_one (congrArg (fun z : π.ker => ((z : L) : G)) h)
  rw [Nat.card_eq_two_iff' 1]
  refine ⟨_, hne, fun y hy => ?_⟩
  rcases (H.ker y).1 y.2 with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hy
  · exact Subtype.ext (Subtype.ext h)

theorem card_eq_mul_card_ker [Finite L] (H : IsDoubleCover t L π) :
    Nat.card L = Nat.card Q * Nat.card π.ker := by
  have h1 := π.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 H.surj, Subgroup.card_top] at h1
  rw [← h1, mul_comm]

theorem card_liftSub [Finite L] (H : IsDoubleCover t L π) (X : Subgroup Q) :
    Nat.card (liftSub π X) = 2 * Nat.card X := by
  have := Finite.of_surjective π H.surj
  rw [liftSub, Subgroup.card_map_of_injective L.subtype_injective]
  have h1 := (X.comap π).card_mul_index
  rw [Subgroup.index_comap_of_surjective X H.surj, H.card_eq_mul_card_ker, H.card_ker,
    ← X.card_mul_index] at h1
  have hX : X.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : Nat.card (X.comap π) = Nat.card X * 2 :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hX) (by rw [h1]; ring)
  rw [this, mul_comm]

theorem card_le_two_mul_imgSub [Finite L] (H : IsDoubleCover t L π) {B : Subgroup G}
    (hB : B ≤ L) : Nat.card B ≤ 2 * Nat.card (imgSub π B) := by
  have := Finite.of_surjective π H.surj
  rw [← H.card_liftSub]
  have : Finite (liftSub π (imgSub π B)) := Finite.of_injective _
    (Subgroup.inclusion_injective (liftSub_le π _))
  exact Subgroup.card_le_of_le (le_liftSub_imgSub π hB)

theorem exists_mem_eq (H : IsDoubleCover t L π) (q : Q) : ∃ l : G, ∃ hl : l ∈ L, π ⟨l, hl⟩ = q := by
  obtain ⟨⟨l, hl⟩, h⟩ := H.surj q
  exact ⟨l, hl, h⟩

theorem pi_conj (π : L →* Q) {l y : G} (hl : l ∈ L) (hy : y ∈ L) :
    π ⟨l * y * l⁻¹, L.mul_mem (L.mul_mem hl hy) (L.inv_mem hl)⟩ =
      π ⟨l, hl⟩ * π ⟨y, hy⟩ * (π ⟨l, hl⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem mem_of_conj_mem {l y : G} (hl : l ∈ L) (hy : l * y * l⁻¹ ∈ L) : y ∈ L := by
  have := L.mul_mem (L.mul_mem (L.inv_mem hl) hy) hl
  simpa [mul_assoc] using this

theorem conjSubgroup_liftSub (π : L →* Q) (X : Subgroup Q) {l : G} (hl : l ∈ L) :
    conjSubgroup (liftSub π X) l =
      liftSub π (X.map (MulAut.conj (π ⟨l, hl⟩)⁻¹).toMonoidHom) := by
  ext x
  rw [mem_conjSubgroup_iff, mem_liftSub, mem_liftSub]
  constructor
  · rintro ⟨hx, hX⟩
    have hxL : x ∈ L := mem_of_conj_mem hl hx
    refine ⟨hxL, ⟨_, hX, ?_⟩⟩
    rw [pi_conj π hl hxL, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨hxL, ⟨y, hy, hyx⟩⟩
    refine ⟨L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl), ?_⟩
    rw [pi_conj π hl hxL, ← hyx, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : π ⟨l, hl⟩ * ((π ⟨l, hl⟩)⁻¹ * y * (π ⟨l, hl⟩)⁻¹⁻¹) * (π ⟨l, hl⟩)⁻¹ = y := by group
    rw [e]
    exact hy

theorem mem_normalizer_liftSub_iff (H : IsDoubleCover t L π) (X : Subgroup Q) {l : G}
    (hl : l ∈ L) : l ∈ normalizer (liftSub π X : Set G) ↔ π ⟨l, hl⟩ ∈ normalizer (X : Set Q) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro hN q
    obtain ⟨y, hy, rfl⟩ := H.exists_mem_eq q
    have h1 := hN y
    simp only [mem_liftSub] at h1
    rw [← pi_conj π hl hy]
    constructor
    · intro hq
      obtain ⟨_, h2⟩ := h1.1 ⟨hy, hq⟩
      exact h2
    · intro hq
      obtain ⟨_, h2⟩ := h1.2 ⟨_, hq⟩
      exact h2
  · intro hq g
    simp only [mem_liftSub]
    constructor
    · rintro ⟨hg, hgX⟩
      exact ⟨_, by rw [pi_conj π hl hg]; exact (hq _).1 hgX⟩
    · rintro ⟨hg', hgX⟩
      have hg := mem_of_conj_mem hl hg'
      exact ⟨hg, (hq _).2 (by rw [← pi_conj π hl hg]; exact hgX)⟩

theorem map_conj_inv_eq {X Y : Subgroup Q} {g : Q} (h : X.map (MulAut.conj g).toMonoidHom = Y) :
    Y.map (MulAut.conj g⁻¹).toMonoidHom = X := by
  rw [← h, Subgroup.map_map]
  convert Subgroup.map_id X
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply,
    MonoidHom.id_apply]
  group

section Todd

variable (H : IsDoubleCover t L π) (D : ToddParabolic Q)
include H

theorem card_toddLift [Finite L] : Nat.card (liftSub π D.A) = 2 ^ 10 := by
  rw [H.card_liftSub, D.card_A]
  norm_num

theorem toddLift_conj_class [Finite L] {B : Subgroup G} (hBL : B ≤ L)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hB : Nat.card B = 2 ^ 10) :
    ∃ l ∈ L, B = conjSubgroup (liftSub π D.A) l := by
  have hsq : ∀ x ∈ imgSub π B, x ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow]
    have : b ^ 2 = 1 := Subtype.ext (by simpa using hB2 _ hb)
    rw [this, map_one]
  have hle := H.card_le_two_mul_imgSub hBL
  obtain ⟨h9, hconj⟩ := D.exists_conj_eq_A hsq
  obtain ⟨g, hg⟩ := hconj (by omega)
  obtain ⟨l, hl, rfl⟩ := H.exists_mem_eq g
  refine ⟨l, hl, ?_⟩
  rw [conjSubgroup_liftSub π _ hl, map_conj_inv_eq hg]
  have : Finite (liftSub π (imgSub π B)) := Finite.of_injective _
    (Subgroup.inclusion_injective (liftSub_le π _))
  refine eq_of_le_of_card_ge (le_liftSub_imgSub π hBL) ?_
  rw [H.card_liftSub, hB]
  omega

theorem toddLift_fuse {s : G} (hs : s ∈ L) (hs2 : orderOf s = 2) :
    ∃ l ∈ L, l⁻¹ * s * l ∈ liftSub π D.A := by
  by_cases h1 : π ⟨s, hs⟩ = 1
  · exact ⟨1, L.one_mem, mem_liftSub.2 ⟨by simpa using hs, by simp [h1]⟩⟩
  · have ho : orderOf (π ⟨s, hs⟩) = 2 := by
      refine orderOf_eq_prime ?_ h1
      rw [← map_pow]
      have : (⟨s, hs⟩ : L) ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, ← hs2, pow_orderOf_eq_one]; rfl)
      rw [this, map_one]
    obtain ⟨g, hg⟩ := D.conj_into_A _ ho
    obtain ⟨l, hl, rfl⟩ := H.exists_mem_eq g
    refine ⟨l⁻¹, L.inv_mem hl, mem_liftSub.2 ⟨?_, ?_⟩⟩
    · rw [inv_inv]
      exact L.mul_mem (L.mul_mem hl hs) (L.inv_mem hl)
    · simp only [inv_inv]
      rw [pi_conj π hl hs]
      exact hg

theorem normalizer_subgroupOf_eq (X : Subgroup Q) :
    (normalizer (liftSub π X : Set G)).subgroupOf L = (normalizer (X : Set Q)).comap π := by
  ext y
  rw [mem_subgroupOf, mem_comap, H.mem_normalizer_liftSub_iff X y.2]

theorem toddLift_odd_index : Odd ((normalizer (liftSub π D.A : Set G)).relIndex L) := by
  rw [relIndex, H.normalizer_subgroupOf_eq, Subgroup.index_comap_of_surjective _ H.surj]
  exact D.odd_index_normalizer

theorem mem_toddLift_of_commute {l : G} (hl : l ∈ L)
    (hc : ∀ e ∈ liftSub π D.A, l * e = e * l) : l ∈ liftSub π D.A := by
  refine mem_liftSub.2 ⟨hl, ?_⟩
  rw [← D.centralizer_A]
  refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
  obtain ⟨e, he, rfl⟩ := H.exists_mem_eq a
  have := hc e (mem_liftSub.2 ⟨he, ha⟩)
  rw [← map_mul, ← map_mul]
  exact congrArg π (Subtype.ext this.symm)

theorem mem_normalizer_of_pi {l : G} (hl : l ∈ L) (h : π ⟨l, hl⟩ ∈ normalizer (D.A : Set Q)) :
    l ∈ normalizer (liftSub π D.A : Set G) ⊓ L :=
  ⟨(H.mem_normalizer_liftSub_iff D.A hl).2 h, hl⟩

theorem eq_of_forall_commute {e : G} (he : e ∈ liftSub π D.A)
    (hc : ∀ l ∈ normalizer (liftSub π D.A : Set G) ⊓ L, l * e = e * l) : e = 1 ∨ e = t := by
  obtain ⟨heL, heA⟩ := mem_liftSub.1 he
  refine (H.ker ⟨e, heL⟩).1 (D.eq_one_of_forall_conj heA fun k hk => ?_)
  obtain ⟨l, hl, rfl⟩ := H.exists_mem_eq k
  have h1 := hc l (H.mem_normalizer_of_pi D hl (D.K_le_normalizer hk))
  rw [← pi_conj π hl heL]
  congr 1
  refine Subtype.ext ?_
  change l * e * l⁻¹ = e
  rw [h1, mul_inv_cancel_right]

theorem toddLift_unique [Finite L] {B : Subgroup G}
    (hB : B ≤ normalizer (liftSub π D.A : Set G) ⊓ L) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hcard : Nat.card B = 2 ^ 10) : B = liftSub π D.A := by
  have hBL : B ≤ L := hB.trans inf_le_right
  have hsq : ∀ x ∈ imgSub π B, x ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow]
    have : b ^ 2 = 1 := Subtype.ext (by simpa using hB2 _ hb)
    rw [this, map_one]
  have hN : imgSub π B ≤ normalizer (D.A : Set Q) := by
    rintro _ ⟨b, hb, rfl⟩
    exact (H.mem_normalizer_liftSub_iff D.A b.2).1 (hB hb).1
  have hle := H.card_le_two_mul_imgSub hBL
  have h9 := (D.exists_conj_eq_A hsq).1
  have hX := D.eq_A_of_le_normalizer hN hsq (by omega)
  have hBE : B ≤ liftSub π D.A := hX ▸ le_liftSub_imgSub π hBL
  have : Finite (liftSub π D.A) := Finite.of_injective _
    (Subgroup.inclusion_injective (liftSub_le π _))
  exact eq_of_le_of_card_ge hBE (by rw [H.card_toddLift D, hcard])

theorem exists_odd_lift {k : Q} (hk : Odd (orderOf k)) :
    ∃ l : G, ∃ hl : l ∈ L, π ⟨l, hl⟩ = k ∧ Odd (orderOf l) := by
  obtain ⟨l, hl, rfl⟩ := H.exists_mem_eq k
  set m := orderOf (π ⟨l, hl⟩)
  have hpow : ∀ n : ℕ, π ⟨l ^ n, L.pow_mem hl n⟩ = π ⟨l, hl⟩ ^ n := fun n => by
    rw [← map_pow]
    rfl
  refine ⟨l ^ (m + 1), L.pow_mem hl _, ?_, ?_⟩
  · rw [hpow, pow_succ, pow_orderOf_eq_one, one_mul]
  · have hm : (l ^ m) ^ 2 = 1 := by
      rcases (H.ker ⟨l ^ m, L.pow_mem hl m⟩).1 (by rw [hpow, pow_orderOf_eq_one]) with h | h
      · change l ^ m = 1 at h
        rw [h, one_pow]
      · change l ^ m = t at h
        rw [h, H.t_sq]
    obtain ⟨j, hj⟩ := hk
    have h1 : (l ^ (m + 1)) ^ m = 1 := by
      rw [← pow_mul, show (m + 1) * m = m * 2 * (j + 1) by rw [hj]; ring, pow_mul, pow_mul, hm,
        one_pow]
    exact Odd.of_dvd_nat ⟨j, hj⟩ (orderOf_dvd_of_pow_eq_one h1)

theorem toddLift_gen :
    normalizer (liftSub π D.A : Set G) ⊓ L ≤ liftSub π D.A ⊔
      closure {y | y ∈ normalizer (liftSub π D.A : Set G) ⊓ L ∧ Odd (orderOf y)} := by
  set T := liftSub π D.A ⊔
    closure {y | y ∈ normalizer (liftSub π D.A : Set G) ⊓ L ∧ Odd (orderOf y)}
  have hTL : T ≤ L := sup_le (liftSub_le π _) ((closure_le _).2 fun y hy => hy.1.2)
  have hA : D.A ≤ imgSub π T := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := H.exists_mem_eq a
    exact ⟨⟨e, he⟩, le_sup_left (a := liftSub π D.A) (mem_liftSub.2 ⟨he, ha⟩), rfl⟩
  have hK : D.K ≤ imgSub π T := by
    refine D.K_le_closure_odd.trans ((closure_le _).2 fun k hk => ?_)
    obtain ⟨l, hl, hlk, hlo⟩ := H.exists_odd_lift hk.2
    have hlN := H.mem_normalizer_of_pi D hl (by rw [hlk]; exact D.K_le_normalizer hk.1)
    exact ⟨⟨l, hl⟩, le_sup_right (a := liftSub π D.A) (subset_closure ⟨hlN, hlo⟩), hlk⟩
  intro x hx
  have hq : π ⟨x, hx.2⟩ ∈ imgSub π T := by
    have h1 := (H.mem_normalizer_liftSub_iff D.A hx.2).1 hx.1
    rw [D.normalizer_A] at h1
    exact (sup_le hA hK) h1
  obtain ⟨y, hy, hyx⟩ := hq
  have hyT : (y : G) ∈ T := hy
  rcases H.eq_or_eq_mul_of_pi_eq hyx with h | h
  · change x = y at h
    rw [h]
    exact hyT
  · change x = y * t at h
    rw [h]
    exact T.mul_mem hyT (le_sup_left (a := liftSub π D.A) (H.t_mem_liftSub D.A))

theorem toddLift_sq [Finite L] [Group.IsPerfect L] (hker : π.ker = center L)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) :
    ∀ e ∈ liftSub π D.A, e ^ 2 = 1 := by
  have hZ : IsPGroup 2 (center L) := by
    rw [← hker]
    exact IsPGroup.of_card (n := 1) (by rw [H.card_ker, pow_one])
  obtain ⟨M, hZM, hMsq, hMcard⟩ := exists_elementary_preimage hZ hQ
  have hcard : Nat.card (M.map π) = 2 ^ 9 := by
    rw [card_map_eq_of_ker_eq (g := QuotientGroup.mk' (center L)) (by
      rw [hker, QuotientGroup.ker_mk']), hMcard]
  have hsq : ∀ x ∈ M.map π, x ^ 2 = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_pow, hMsq m hm, map_one]
  obtain ⟨g, hg⟩ := (D.exists_conj_eq_A hsq).2 hcard.ge
  obtain ⟨l, hl, rfl⟩ := H.exists_mem_eq g
  have hE : liftSub π D.A = conjSubgroup (M.map L.subtype) l⁻¹ := by
    have hπ : π ⟨l⁻¹, L.inv_mem hl⟩ = (π ⟨l, hl⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [← liftSub_map_eq (hker ▸ hZM), conjSubgroup_liftSub π _ (L.inv_mem hl), hπ, inv_inv,
      hg]
  rw [hE]
  refine SolomonWong.conjSubgroup_sq ?_ l⁻¹
  rintro _ ⟨m, hm, rfl⟩
  simpa using congrArg Subtype.val (hMsq m hm)

theorem sq_eq_one_of_sq_mem_center (hE : ∀ e ∈ liftSub π D.A, e ^ 2 = 1)
    (hker : π.ker = center L) (a : L) (ha : a ^ 2 ∈ center L) : a ^ 2 = 1 := by
  rw [← hker, MonoidHom.mem_ker, map_pow] at ha
  by_cases h1 : π a = 1
  · rcases (H.ker a).1 h1 with h | h
    · have : a = 1 := Subtype.ext h
      rw [this, one_pow]
    · refine Subtype.ext ?_
      rw [SubgroupClass.coe_pow, h, H.t_sq]
      rfl
  · obtain ⟨g, hg⟩ := D.conj_into_A _ (orderOf_eq_prime ha h1)
    obtain ⟨l, hl, rfl⟩ := H.exists_mem_eq g
    have hmem : l * a * l⁻¹ ∈ liftSub π D.A :=
      mem_liftSub.2 ⟨L.mul_mem (L.mul_mem hl a.2) (L.inv_mem hl), by
        rw [pi_conj π hl a.2]; exact hg⟩
    have h2 := hE _ hmem
    rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h2
    exact Subtype.ext (by rw [SubgroupClass.coe_pow, h2]; rfl)

end Todd

end IsDoubleCover

end CFSG.EvenSmallLie.UnitarySix

module

public import CFSG.GH74.GLS.C3.Layer1.P34Cfg

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open DihedralGroup Subgroup
open scoped commutatorElement

namespace PShape

def half (n : ℕ) : ZMod (2 ^ n) := ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))

def quarter (n : ℕ) : ZMod (2 ^ n) := ((2 ^ (n - 2) : ℕ) : ZMod (2 ^ n))

theorem half_add_half {n : ℕ} (hn : 1 ≤ n) : half n + half n = 0 := by
  unfold half
  rw [← Nat.cast_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hn]
  exact ZMod.natCast_self _

theorem half_neg {n : ℕ} (hn : 1 ≤ n) : -half n = half n := by
  rw [neg_eq_iff_add_eq_zero]
  exact half_add_half hn

theorem quarter_add_quarter {n : ℕ} (hn : 2 ≤ n) : quarter n + quarter n = half n := by
  unfold quarter half
  rw [← Nat.cast_add, ← two_mul, ← pow_succ']
  have h : n - 2 + 1 = n - 1 := by omega
  rw [h]

theorem double_eq_zero {n : ℕ} (hn : 1 ≤ n) {j : ZMod (2 ^ n)} (h : j + j = 0) :
    j = 0 ∨ j = half n := by
  have h1 : -j = j := by rw [neg_eq_iff_add_eq_zero]; exact h
  rcases (ZMod.neg_eq_self_iff j).mp h1 with h0 | h2
  · exact Or.inl h0
  · right
    have h3 : j.val = 2 ^ (n - 1) := by
      have h4 : 2 * j.val = 2 * 2 ^ (n - 1) := by
        rw [h2, ← pow_succ', Nat.sub_add_cancel hn]
      omega
    rw [← ZMod.natCast_zmod_val j, h3]
    rfl

theorem two_ne_zero_zmod {n : ℕ} (hn : 2 ≤ n) : (2 : ZMod (2 ^ n)) ≠ 0 := by
  intro h0
  have h : ((2 : ℕ) : ZMod (2 ^ n)) = 0 := by exact_mod_cast h0
  rw [ZMod.natCast_eq_zero_iff] at h
  have h1 := Nat.le_of_dvd (by norm_num) h
  have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem ev_or_odd {m : ℕ} (i : ZMod (2 ^ m)) :
    (∃ k, i = k + k) ∨ ∃ k, i = 1 + (k + k) := by
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  obtain ⟨t, ht | ht⟩ := Nat.even_or_odd' i.val
  · left
    refine ⟨(t : ZMod (2 ^ m)), ?_⟩
    rw [← ZMod.natCast_zmod_val i, ht]
    push_cast
    ring
  · right
    refine ⟨(t : ZMod (2 ^ m)), ?_⟩
    rw [← ZMod.natCast_zmod_val i, ht]
    push_cast
    ring

theorem not_ev_one {m : ℕ} (hm : 1 ≤ m) : ¬ ∃ k : ZMod (2 ^ m), (1 : ZMod (2 ^ m)) = k + k := by
  rintro ⟨k, hk⟩
  have hd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have h := congrArg (ZMod.castHom hd (ZMod 2)) hk
  rw [map_one, map_add, CharTwo.add_self_eq_zero] at h
  exact one_ne_zero h

section Abstract

variable {n : ℕ}

theorem card_dihedral (n : ℕ) : Nat.card (DihedralGroup (2 ^ n)) = 2 ^ (n + 1) := by
  rw [DihedralGroup.nat_card, pow_succ']

theorem sr_not_comm_r1 (hn : 2 ≤ n) (i : ZMod (2 ^ n)) : sr i * r 1 ≠ r 1 * sr i := by
  intro h
  simp only [sr_mul_r, r_mul_sr, sr.injEq] at h
  apply two_ne_zero_zmod hn
  calc (2 : ZMod (2 ^ n)) = (i + 1) - (i - 1) := by ring
    _ = 0 := by rw [h, sub_self]

theorem central_eq (hn : 2 ≤ n) {c : DihedralGroup (2 ^ n)} (h1 : c * r 1 = r 1 * c)
    (h2 : c * sr 0 = sr 0 * c) : c = 1 ∨ c = r (half n) := by
  rcases c with j | j
  · simp only [r_mul_sr, sr_mul_r, sr.injEq, zero_sub, zero_add] at h2
    have h3 : j + j = 0 := by rw [← neg_eq_iff_add_eq_zero]; exact h2
    rcases double_eq_zero (by omega) h3 with h | h
    · left
      rw [h]
      rfl
    · right
      rw [h]
  · exact absurd h1 (sr_not_comm_r1 hn j)

theorem invol_eq (hn : 2 ≤ n) {p : DihedralGroup (2 ^ n)} (hp : p * p = 1)
    (h1 : p * r 1 = r 1 * p) : p = 1 ∨ p = r (half n) := by
  rcases p with j | j
  · simp only [r_mul_r, ← r_zero, r.injEq] at hp
    rcases double_eq_zero (by omega) hp with h | h
    · left
      rw [h]
      rfl
    · right
      rw [h]
  · exact absurd h1 (sr_not_comm_r1 hn j)

theorem mem_closure_invol (g : DihedralGroup (2 ^ n)) :
    g ∈ closure {p : DihedralGroup (2 ^ n) | p * p = 1} := by
  rcases g with i | i
  · have h : (r i : DihedralGroup (2 ^ n)) = sr 0 * sr i := by simp
    rw [h]
    exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · exact subset_closure (by simp)

theorem comm_sr0_r1 :
    ⁅(sr 0 : DihedralGroup (2 ^ n)), (r 1 : DihedralGroup (2 ^ n))⁆ = r (-2) := by
  simp [commutatorElement_def]
  ring_nf

theorem comm_pow (hn : 2 ≤ n) :
    ⁅(sr 0 : DihedralGroup (2 ^ n)), (r 1 : DihedralGroup (2 ^ n))⁆ ^ (2 ^ (n - 2)) =
      r (half n) := by
  rw [comm_sr0_r1, r_pow]
  congr 1
  have h := quarter_add_quarter hn
  calc (-2 : ZMod (2 ^ n)) * ((2 ^ (n - 2) : ℕ) : ZMod (2 ^ n))
      = -(quarter n + quarter n) := by unfold quarter; push_cast; ring
    _ = half n := by rw [h, half_neg (by omega)]

theorem rot_mem_zpowers (i : ZMod (2 ^ n)) : (r i : DihedralGroup (2 ^ n)) ∈ zpowers (r 1) := by
  refine mem_zpowers_iff.mpr ⟨(i.val : ℤ), ?_⟩
  rw [r_one_zpow]
  simp

theorem card_zpowers_r1 (n : ℕ) :
    Nat.card (zpowers (r 1 : DihedralGroup (2 ^ n))) = 2 ^ n := by
  rw [Nat.card_zpowers, orderOf_r_one]

theorem cyclic_unique (hn : 2 ≤ n) (B : Subgroup (DihedralGroup (2 ^ n))) [IsCyclic B]
    (hB : Nat.card B = 2 ^ n) : B = zpowers (r 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := B)
  have hord : orderOf g = Nat.card B := orderOf_eq_card_of_forall_mem_zpowers hg
  have hrot : ∃ j, (g : DihedralGroup (2 ^ n)) = r j := by
    rcases hgg : (g : DihedralGroup (2 ^ n)) with j | j
    · exact ⟨j, rfl⟩
    · exfalso
      have h2 : g * g = 1 := Subtype.ext (by simp [hgg])
      have h3 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
      have h4 := Nat.le_of_dvd (by norm_num) h3
      have h5 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
  obtain ⟨j, hj⟩ := hrot
  have hle : B ≤ zpowers (r 1) := by
    intro b hb
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨b, hb⟩)
    have hb' : b = (g : DihedralGroup (2 ^ n)) ^ k := by
      rw [← Subgroup.coe_zpow, hk]
    rw [hb', hj]
    exact zpow_mem (rot_mem_zpowers j) k
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_zpowers_r1, hB])

end Abstract

section IndexTwo

variable {m : ℕ} {K L : Subgroup (DihedralGroup (2 ^ m))}

theorem index_eq_two_of_card {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (h : Nat.card K * 2 = Nat.card G) : K.index = 2 := by
  have h1 := Subgroup.card_mul_index K
  have hpos : 0 < Nat.card K := Nat.card_pos
  rw [← h] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos h1

theorem card_eq_of_two (hK : Nat.card K * 2 = Nat.card (DihedralGroup (2 ^ m))) :
    Nat.card K = 2 ^ m := by
  rw [card_dihedral, pow_succ'] at hK
  omega

theorem mem_r_iff (hK : K.index = 2) (h1 : r 1 ∉ K) (i : ZMod (2 ^ m)) :
    r i ∈ K ↔ ∃ k, i = k + k := by
  constructor
  · intro hi
    rcases ev_or_odd i with h | ⟨k, hk⟩
    · exact h
    · exfalso
      have h3 : (r i : DihedralGroup (2 ^ m)) = r 1 * (r k * r k) := by rw [hk]; simp
      rw [h3, Subgroup.mul_mem_iff_of_index_two hK] at hi
      exact h1 (hi.mpr (Subgroup.mul_self_mem_of_index_two hK _))
  · rintro ⟨k, rfl⟩
    have h3 : (r (k + k) : DihedralGroup (2 ^ m)) = r k * r k := by simp
    rw [h3]
    exact Subgroup.mul_self_mem_of_index_two hK _

theorem mem_sr_iff (hK : K.index = 2) (h1 : r 1 ∉ K) (i : ZMod (2 ^ m)) :
    sr i ∈ K ↔ (sr 0 ∈ K ↔ ∃ k, i = k + k) := by
  have h3 : (sr i : DihedralGroup (2 ^ m)) = sr 0 * r i := by simp
  rw [h3, Subgroup.mul_mem_iff_of_index_two hK, mem_r_iff hK h1]

theorem eq_of_sr0 (hK : K.index = 2) (hL : L.index = 2) (h1K : r 1 ∉ K) (h1L : r 1 ∉ L)
    (h0 : sr 0 ∈ K ↔ sr 0 ∈ L) : K = L := by
  ext g
  rcases g with i | i
  · rw [mem_r_iff hK h1K, mem_r_iff hL h1L]
  · rw [mem_sr_iff hK h1K, mem_sr_iff hL h1L, h0]

theorem r1_not_mem (hK : Nat.card K * 2 = Nat.card (DihedralGroup (2 ^ m)))
    (hnc : ¬ IsCyclic K) : r 1 ∉ K := by
  intro h1
  have hle : zpowers (r 1) ≤ K := zpowers_le.mpr h1
  have h2 : zpowers (r 1) = K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_zpowers_r1, card_eq_of_two hK])
  apply hnc
  rw [← h2]
  exact Subgroup.isCyclic_zpowers _

theorem sr1_mem (hK : K.index = 2) (h1 : r 1 ∉ K) (hs : sr 0 ∉ K) (hm : 1 ≤ m) : sr 1 ∈ K := by
  rw [mem_sr_iff hK h1]
  exact iff_of_false hs (not_ev_one hm)

theorem r2_mem_commutator (hK : K.index = 2) (hL : L.index = 2) (h1K : r 1 ∉ K)
    (h1L : r 1 ∉ L) (h0 : ¬ (sr 0 ∈ K ↔ sr 0 ∈ L)) (hm : 1 ≤ m) :
    (r 2 : DihedralGroup (2 ^ m)) ∈ ⁅K, L⁆ := by
  by_cases hK0 : sr 0 ∈ K
  · have hL0 : sr 0 ∉ L := fun h => h0 ⟨fun _ => h, fun _ => hK0⟩
    have h2 := commutator_mem_commutator hK0 (sr1_mem hL h1L hL0 hm)
    have h3 : ⁅(sr 0 : DihedralGroup (2 ^ m)), (sr 1 : DihedralGroup (2 ^ m))⁆ = r 2 := by
      simp [commutatorElement_def]
      ring_nf
    rwa [h3] at h2
  · have hL0 : sr 0 ∈ L := by
      by_contra h
      exact h0 (iff_of_false hK0 h)
    have h2 := commutator_mem_commutator (sr1_mem hK h1K hK0 hm) hL0
    have h3 : ⁅(sr 1 : DihedralGroup (2 ^ m)), (sr 0 : DihedralGroup (2 ^ m))⁆ = (r 2)⁻¹ := by
      simp [commutatorElement_def]
      ring_nf
    rw [h3] at h2
    simpa using inv_mem h2

theorem inf_eq_zpowers (hK : K.index = 2) (hL : L.index = 2) (h1K : r 1 ∉ K) (h1L : r 1 ∉ L)
    (h0 : ¬ (sr 0 ∈ K ↔ sr 0 ∈ L)) : K ⊓ L = zpowers (r 2) := by
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  ext g
  rcases g with i | i
  · rw [Subgroup.mem_inf, mem_r_iff hK h1K, mem_r_iff hL h1L, and_self]
    constructor
    · rintro ⟨k, rfl⟩
      refine mem_zpowers_iff.mpr ⟨(k.val : ℤ), ?_⟩
      rw [r_zpow]
      congr 1
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    · intro h
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
      rw [r_zpow] at hk
      exact ⟨(k : ZMod (2 ^ m)), by rw [← r.inj hk]; ring⟩
  · rw [Subgroup.mem_inf]
    constructor
    · rintro ⟨hKi, hLi⟩
      rw [mem_sr_iff hK h1K] at hKi
      rw [mem_sr_iff hL h1L] at hLi
      exfalso
      apply h0
      tauto
    · intro h
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
      rw [r_zpow] at hk
      cases hk

theorem card_zpowers_r2 (hm : 1 ≤ m) :
    Nat.card (zpowers (r 2 : DihedralGroup (2 ^ m))) * 2 = 2 ^ m := by
  rw [Nat.card_zpowers]
  have h1 : (r 2 : DihedralGroup (2 ^ m)) = r 1 ^ 2 := by
    rw [r_one_pow]
    simp
  have h2 : 2 ∣ orderOf (r 1 : DihedralGroup (2 ^ m)) := by
    rw [orderOf_r_one]
    exact dvd_pow_self 2 (by omega)
  rw [h1, orderOf_pow_of_dvd (by norm_num) h2, orderOf_r_one]
  exact Nat.div_mul_cancel (dvd_pow_self 2 (by omega))

theorem max_b (hm : 1 ≤ m) {A B : Subgroup (DihedralGroup (2 ^ m))}
    (hAc : Nat.card A * 2 = Nat.card (DihedralGroup (2 ^ m)))
    (hBc : Nat.card B * 2 = Nat.card (DihedralGroup (2 ^ m)))
    (hAnc : ¬ IsCyclic A) (hBnc : ¬ IsCyclic B) (hAB : A ≠ B) :
    Nat.card ↥(A ⊓ B) * 2 = Nat.card A ∧ A ⊓ B ≤ ⁅A, B⁆ := by
  have hA := index_eq_two_of_card hAc
  have hB := index_eq_two_of_card hBc
  have h1A := r1_not_mem hAc hAnc
  have h1B := r1_not_mem hBc hBnc
  have h0 : ¬ (sr 0 ∈ A ↔ sr 0 ∈ B) := fun h => hAB (eq_of_sr0 hA hB h1A h1B h)
  have hinf := inf_eq_zpowers hA hB h1A h1B h0
  refine ⟨?_, ?_⟩
  · rw [hinf, card_eq_of_two hAc]
    exact card_zpowers_r2 hm
  · rw [hinf]
    exact zpowers_le.mpr (r2_mem_commutator hA hB h1A h1B h0 hm)

theorem max_a {A B C : Subgroup (DihedralGroup (2 ^ m))}
    (hAc : Nat.card A * 2 = Nat.card (DihedralGroup (2 ^ m)))
    (hBc : Nat.card B * 2 = Nat.card (DihedralGroup (2 ^ m)))
    (hCc : Nat.card C * 2 = Nat.card (DihedralGroup (2 ^ m)))
    (hAnc : ¬ IsCyclic A) (hBnc : ¬ IsCyclic B) (hCnc : ¬ IsCyclic C) :
    A = B ∨ B = C ∨ A = C := by
  have hA := index_eq_two_of_card hAc
  have hB := index_eq_two_of_card hBc
  have hC := index_eq_two_of_card hCc
  have h1A := r1_not_mem hAc hAnc
  have h1B := r1_not_mem hBc hBnc
  have h1C := r1_not_mem hCc hCnc
  by_cases hAB : sr 0 ∈ A ↔ sr 0 ∈ B
  · exact Or.inl (eq_of_sr0 hA hB h1A h1B hAB)
  · by_cases hBC : sr 0 ∈ B ↔ sr 0 ∈ C
    · exact Or.inr (Or.inl (eq_of_sr0 hB hC h1B h1C hBC))
    · exact Or.inr (Or.inr (eq_of_sr0 hA hC h1A h1C (by tauto)))

end IndexTwo

section Transfer

variable {X : Type} [Group X] {n : ℕ}

def embed (D : Subgroup X) (e : ↥D ≃* DihedralGroup (2 ^ n)) : DihedralGroup (2 ^ n) →* X :=
  D.subtype.comp e.symm.toMonoidHom

theorem embed_injective (D : Subgroup X) (e : ↥D ≃* DihedralGroup (2 ^ n)) :
    Function.Injective (embed D e) :=
  Subtype.val_injective.comp e.symm.injective

theorem embed_mem (D : Subgroup X) (e : ↥D ≃* DihedralGroup (2 ^ n))
    (g : DihedralGroup (2 ^ n)) : embed D e g ∈ D :=
  (e.symm g).2

theorem exists_embed (D : Subgroup X) (e : ↥D ≃* DihedralGroup (2 ^ n)) {x : X} (hx : x ∈ D) :
    ∃ g, embed D e g = x :=
  ⟨e ⟨x, hx⟩, by simp [embed]⟩

theorem range_embed (D : Subgroup X) (e : ↥D ≃* DihedralGroup (2 ^ n)) :
    (embed D e).range = D := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact embed_mem D e g
  · intro hx
    exact exists_embed D e hx

theorem comap_map (D : Subgroup X) (e : ↥D ≃* DihedralGroup (2 ^ n)) {A : Subgroup X}
    (hA : A ≤ D) : (A.comap (embed D e)).map (embed D e) = A := by
  rw [Subgroup.map_comap_eq, range_embed]
  exact inf_eq_right.mpr hA

noncomputable def comapEquiv (D : Subgroup X) (e : ↥D ≃* DihedralGroup (2 ^ n)) {A : Subgroup X}
    (hA : A ≤ D) : ↥(A.comap (embed D e)) ≃* ↥A :=
  (Subgroup.equivMapOfInjective _ (embed D e) (embed_injective D e)).trans
    (MulEquiv.subgroupCongr (comap_map D e hA))

theorem card_comap (D : Subgroup X) (e : ↥D ≃* DihedralGroup (2 ^ n)) {A : Subgroup X}
    (hA : A ≤ D) : Nat.card ↥(A.comap (embed D e)) = Nat.card ↥A :=
  Nat.card_congr (comapEquiv D e hA).toEquiv

theorem not_isCyclic_comap (D : Subgroup X) (e : ↥D ≃* DihedralGroup (2 ^ n)) {A : Subgroup X}
    (hA : A ≤ D) (h : ¬ IsCyclic ↥A) : ¬ IsCyclic ↥(A.comap (embed D e)) := by
  intro hc
  exact h (isCyclic_of_surjective (comapEquiv D e hA).toMonoidHom (comapEquiv D e hA).surjective)

theorem comap_inj (D : Subgroup X) (e : ↥D ≃* DihedralGroup (2 ^ n)) {A B : Subgroup X}
    (hA : A ≤ D) (hB : B ≤ D) (h : A.comap (embed D e) = B.comap (embed D e)) : A = B := by
  calc A = (A.comap (embed D e)).map (embed D e) := (comap_map D e hA).symm
    _ = (B.comap (embed D e)).map (embed D e) := by rw [h]
    _ = B := comap_map D e hB

theorem not_isCyclic_of_dihedral {A : Subgroup X} (h : IsDihedralGE8 A) : ¬ IsCyclic ↥A := by
  obtain ⟨k, hk, ⟨f⟩⟩ := h
  intro hc
  have h1 : IsCyclic (DihedralGroup (2 ^ k)) :=
    isCyclic_of_surjective f.toMonoidHom f.surjective
  refine DihedralGroup.not_isCyclic ?_ h1
  have h2 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

end Transfer

end PShape

theorem dihedralShapeFacts : DihedralShapeFacts := by
  intro X _ _ D hD
  obtain ⟨n, hn, ⟨e⟩⟩ := hD
  have hinj := PShape.embed_injective D e
  have hcard : Nat.card ↥D = 2 ^ (n + 1) := by
    rw [Nat.card_congr e.toEquiv, PShape.card_dihedral]
  refine ⟨?_, IsPGroup.of_card hcard, ?_, ?_⟩
  · rw [hcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro a ha
    obtain ⟨g, rfl⟩ := PShape.exists_embed D e ha
    have h1 : PShape.embed D e g ∈
        (closure {p : DihedralGroup (2 ^ n) | p * p = 1}).map (PShape.embed D e) :=
      Subgroup.mem_map_of_mem _ (PShape.mem_closure_invol g)
    rw [MonoidHom.map_closure] at h1
    refine closure_mono ?_ h1
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨PShape.embed_mem D e p, ?_⟩
    rw [← map_mul, show p * p = 1 from hp, map_one]
  · intro z hzD hz2 hzc
    obtain ⟨g, rfl⟩ := PShape.exists_embed D e hzD
    have hg2 : orderOf g = 2 := by
      rw [← orderOf_injective (PShape.embed D e) hinj g]
      exact hz2
    have hgc : ∀ a : DihedralGroup (2 ^ n), a * g = g * a := fun a =>
      hinj (by rw [map_mul, map_mul]; exact hzc (PShape.embed D e a) (PShape.embed_mem D e a))
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hg2
      omega
    have hgh : g = r (PShape.half n) :=
      (PShape.central_eq hn (hgc (r 1)).symm (hgc (sr 0)).symm).resolve_left hg1
    subst hgh
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hcD hcc
      obtain ⟨h, rfl⟩ := PShape.exists_embed D e hcD
      have hhc : ∀ a : DihedralGroup (2 ^ n), a * h = h * a := fun a =>
        hinj (by rw [map_mul, map_mul]; exact hcc (PShape.embed D e a) (PShape.embed_mem D e a))
      rcases PShape.central_eq hn (hhc (r 1)).symm (hhc (sr 0)).symm with h1 | h1
      · left
        rw [h1, map_one]
      · right
        rw [h1]
    · refine ⟨PShape.embed D e (r (PShape.quarter n)), PShape.embed_mem D e _, ?_⟩
      rw [← map_mul, r_mul_r, PShape.quarter_add_quarter hn]
    · have h1 : ⁅PShape.embed D e (sr 0), PShape.embed D e (r 1)⁆ ∈ ⁅D, D⁆ :=
        commutator_mem_commutator (PShape.embed_mem D e _) (PShape.embed_mem D e _)
      have h2 : PShape.embed D e (r (PShape.half n)) =
          ⁅PShape.embed D e (sr 0), PShape.embed D e (r 1)⁆ ^ (2 ^ (n - 2)) := by
        rw [← map_commutatorElement, ← map_pow, PShape.comm_pow hn]
      rw [h2]
      exact pow_mem h1 _
    · have hA : Nat.card ↥(zpowers (PShape.embed D e (r 1))) = 2 ^ n := by
        rw [Nat.card_zpowers, orderOf_injective (PShape.embed D e) hinj, orderOf_r_one]
      refine ⟨zpowers (PShape.embed D e (r 1)), zpowers_le.mpr (PShape.embed_mem D e _),
        Subgroup.isCyclic_zpowers _, by rw [hA, hcard, pow_succ'], ?_, ?_⟩
      · intro B hBD hBcyc hBcard
        have hcyc : IsCyclic ↥(B.comap (PShape.embed D e)) :=
          isCyclic_of_surjective (PShape.comapEquiv D e hBD).symm.toMonoidHom
            (PShape.comapEquiv D e hBD).symm.surjective
        have hBc : Nat.card ↥(B.comap (PShape.embed D e)) = 2 ^ n := by
          rw [PShape.card_comap D e hBD, hBcard, hA]
        have h1 := PShape.cyclic_unique hn (B.comap (PShape.embed D e)) hBc
        rw [← PShape.comap_map D e hBD, h1, MonoidHom.map_zpowers]
      · intro p hpD hp2 hpc
        obtain ⟨h, rfl⟩ := PShape.exists_embed D e hpD
        have hh2 : h * h = 1 := hinj (by rw [map_mul, map_one]; exact hp2)
        have hh1 : h * r 1 = r 1 * h := hinj (by
          rw [map_mul, map_mul]
          exact hpc _ (mem_zpowers _))
        rcases PShape.invol_eq hn hh2 hh1 with h1 | h1
        · left
          rw [h1, map_one]
        · right
          rw [h1]

theorem dihedralMaxFacts : DihedralMaxFacts := by
  intro X _ _ W hW _h16
  obtain ⟨m, hm, ⟨e⟩⟩ := hW
  have hcardW : Nat.card ↥W = Nat.card (DihedralGroup (2 ^ m)) := Nat.card_congr e.toEquiv
  refine ⟨?_, ?_⟩
  · intro A B C hAW hBW hCW hA hB hC hAc hBc hCc
    rcases PShape.max_a (A := A.comap (PShape.embed W e)) (B := B.comap (PShape.embed W e))
      (C := C.comap (PShape.embed W e))
      (by rw [PShape.card_comap W e hAW, hAc, hcardW])
      (by rw [PShape.card_comap W e hBW, hBc, hcardW])
      (by rw [PShape.card_comap W e hCW, hCc, hcardW])
      (PShape.not_isCyclic_comap W e hAW (PShape.not_isCyclic_of_dihedral hA))
      (PShape.not_isCyclic_comap W e hBW (PShape.not_isCyclic_of_dihedral hB))
      (PShape.not_isCyclic_comap W e hCW (PShape.not_isCyclic_of_dihedral hC)) with h | h | h
    · exact Or.inl (PShape.comap_inj W e hAW hBW h)
    · exact Or.inr (Or.inl (PShape.comap_inj W e hBW hCW h))
    · exact Or.inr (Or.inr (PShape.comap_inj W e hAW hCW h))
  · intro A B hAW hBW hA hB hAc hBc hAB
    have hne : A.comap (PShape.embed W e) ≠ B.comap (PShape.embed W e) := fun h =>
      hAB (PShape.comap_inj W e hAW hBW h)
    obtain ⟨h1, h2⟩ := PShape.max_b (by omega) (A := A.comap (PShape.embed W e))
      (B := B.comap (PShape.embed W e))
      (by rw [PShape.card_comap W e hAW, hAc, hcardW])
      (by rw [PShape.card_comap W e hBW, hBc, hcardW])
      (PShape.not_isCyclic_comap W e hAW (PShape.not_isCyclic_of_dihedral hA))
      (PShape.not_isCyclic_comap W e hBW (PShape.not_isCyclic_of_dihedral hB)) hne
    have hABW : A ⊓ B ≤ W := inf_le_left.trans hAW
    refine ⟨?_, ?_⟩
    · rw [← PShape.card_comap W e hABW, ← PShape.card_comap W e hAW, Subgroup.comap_inf]
      exact h1
    · have h3 := Subgroup.map_mono (f := PShape.embed W e) h2
      rw [← Subgroup.comap_inf, PShape.comap_map W e hABW, Subgroup.map_commutator,
        PShape.comap_map W e hAW, PShape.comap_map W e hBW] at h3
      exact h3

end CFSG.GH74.GLS.C3.Layer1.P34

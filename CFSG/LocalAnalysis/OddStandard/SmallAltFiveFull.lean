module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveFocal
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStar

public section

namespace CFSG.OddStandard

open Subgroup Equiv CFSG.Open
open scoped Pointwise
open CFSG.ComponentClassification.StandardRecognition
  (glauberman_zStar_central_sylow_involution_univ)

variable {G : Type*} [Group G]

structure Full (L : Subgroup G) (S : Sylow 2 (centralizer (L : Set G))) (t : G)
    (e : L ≃* alternatingGroup (Fin 5)) : Prop where
  sector : Sector L S t
  perfect : commutator G = ⊤
  trivial_inter : L ⊓ centralizer (L : Set G) = ⊥
  four_le : 4 ≤ Nat.card (sg L S)
  surj_H : ∀ σ : Perm (Fin 5), ∃ h : normalizer (L : Set G),
    (h : G) ∈ centralizer ({t} : Set G) ∧ rhoOf e h = σ

@[expose] def qg (t : G) (Q : Sylow 2 (centralizer ({t} : Set G))) : Subgroup G :=
  (Q : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype

theorem qg_le_H (t : G) (Q : Sylow 2 (centralizer ({t} : Set G))) :
    qg t Q ≤ centralizer ({t} : Set G) := map_subtype_le _

theorem isPGroup_qg (t : G) (Q : Sylow 2 (centralizer ({t} : Set G))) : IsPGroup 2 (qg t Q) :=
  Q.isPGroup'.map _

theorem card_qg [Finite G] (t : G) (Q : Sylow 2 (centralizer ({t} : Set G))) :
    Nat.card (qg t Q) = 2 ^ (Nat.card (centralizer ({t} : Set G))).factorization 2 := by
  rw [qg, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    Sylow.card_eq_multiplicity]

section Full

variable [Finite G] {L : Subgroup G} {S : Sylow 2 (centralizer (L : Set G))} {t : G}
  {e : L ≃* alternatingGroup (Fin 5)}

theorem full_of_basic (e : L ≃* alternatingGroup (Fin 5)) (hs : Sector L S t)
    (hperf : commutator G = ⊤) (hZ : L ⊓ centralizer (L : Set G) = ⊥)
    (h4 : 4 ≤ Nat.card (sg L S)) : Full L S t e := by
  have hHM := (centralizer_t_facts hs).1
  have hLH := (centralizer_t_facts hs).2.1
  have hodd : ∃ h : normalizer (L : Set G), (h : G) ∈ centralizer ({t} : Set G) ∧
      Perm.sign (rhoOf e h) = -1 := by
    by_contra hne
    push Not at hne
    refine AltCase.false (e := e) ⟨hs, hperf, hZ, h4, ?_⟩
    intro h hh
    rw [Perm.mem_alternatingGroup]
    rcases Int.units_eq_one_or (Perm.sign (rhoOf e h)) with h1 | h1
    · exact h1
    · exact absurd h1 (hne h hh)
  obtain ⟨h₀, hh₀, hs₀⟩ := hodd
  refine ⟨hs, hperf, hZ, h4, fun σ => ?_⟩
  have hAX : alternatingGroup (Fin 5) ≤ (rhoH L t hHM e).range := by
    intro g hg
    obtain ⟨l, hl⟩ := e.surjective ⟨g, hg⟩
    refine ⟨⟨l, hLH l.2⟩, ?_⟩
    show rhoOf e ⟨(l : G), Subgroup.le_normalizer l.2⟩ = g
    rw [rhoOf_apply_of_mem e l.2]
    exact congrArg Subtype.val hl
  have hXtop := eq_top_of_alternatingGroup_le_of_exists_odd (rhoH L t hHM e).range hAX
    (σ := rhoOf e h₀) ⟨⟨h₀, hh₀⟩, rfl⟩ hs₀
  have : σ ∈ (rhoH L t hHM e).range := hXtop ▸ mem_top σ
  obtain ⟨⟨h, hh⟩, hρ⟩ := this
  exact ⟨⟨h, hHM hh⟩, hh, hρ⟩

theorem card_sg_eq_R (hs : Sector L S t) :
    Nat.card (sg L S) = 2 ^ (Nat.card
      (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact card_eq_of_maximal (le_inf sg_le_centralizer (sg_le_centralizer_t hs)) isPGroup_sg
    fun Q' hQ' hQ'2 hle => sg_maximal (hQ'.trans inf_le_left) hQ'2 hle

theorem Full.H_le_M (hf : Full L S t e) : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
  (centralizer_t_facts hf.sector).1

theorem Full.L_le_H (hf : Full L S t e) : L ≤ centralizer ({t} : Set G) :=
  (centralizer_t_facts hf.sector).2.1

theorem Full.card_H (hf : Full L S t e) :
    Nat.card (centralizer ({t} : Set G)) =
      120 * Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have hrange : (rhoH L t hf.H_le_M e).range = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    obtain ⟨h, hh, hρ⟩ := hf.surj_H σ
    exact ⟨⟨h, hh⟩, hρ⟩
  have h1 := card_eq_card_range_mul_card_ker (rhoH L t hf.H_le_M e)
  rw [hrange, ker_rhoH L t hf.H_le_M e, Subgroup.card_top] at h1
  rw [h1]
  congr 1
  · simp [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) ≤ centralizer ({t} : Set G))).toEquiv]
  congr 2
  ext x
  simp [mem_subgroupOf]

theorem Full.two_pow_card_H (hf : Full L S t e) :
    2 ^ (Nat.card (centralizer ({t} : Set G))).factorization 2 = 8 * Nat.card (sg L S) := by
  have hRpos : Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ≠ 0 :=
    Nat.card_pos.ne'
  rw [hf.card_H, Nat.factorization_mul (by norm_num) hRpos, Finsupp.add_apply, pow_add,
    ← card_sg_eq_R hf.sector]
  congr 1
  rw [show (Nat.factorization 120) 2 = 3 by decide +kernel]
  norm_num

theorem Full.card_qg_eq (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G))) :
    Nat.card (qg t Q) = 8 * Nat.card (sg L S) := by
  rw [card_qg, hf.two_pow_card_H]

omit [Finite G] in
theorem Full.qg_inf_R (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) :
    qg t Q ⊓ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) = sg L S := by
  have hle : sg L S ≤ qg t Q ⊓ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) :=
    le_inf hSQ (le_inf sg_le_centralizer (sg_le_centralizer_t hf.sector))
  have h2 : IsPGroup 2 (qg t Q ⊓ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) :
      Subgroup G) := (isPGroup_qg t Q).to_inf_left
  exact sg_maximal (inf_le_right.trans inf_le_left) h2 hle

theorem Full.card_P (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G))) :
    Nat.card (qg t Q ⊓ L : Subgroup G) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := card_inf_eq_of_normal (p := 2) (X := centralizer ({t} : Set G)) (N := L) (Q := qg t Q)
    hf.L_le_H (centralizer_t_facts hf.sector).2.2.1 (qg_le_H t Q) (card_qg t Q)
  rw [h1, Nat.card_congr e.toEquiv, card_alternatingGroup_five]
  decide +kernel

@[expose] noncomputable def Full.rho (hf : Full L S t e) :
    centralizer ({t} : Set G) →* Perm (Fin 5) :=
  rhoH L t hf.H_le_M e

theorem Full.rho_surjective (hf : Full L S t e) : Function.Surjective hf.rho := by
  intro σ
  obtain ⟨h, hh, hρ⟩ := hf.surj_H σ
  exact ⟨⟨h, hh⟩, hρ⟩

theorem Full.rho_eq_one_iff (hf : Full L S t e) (h : centralizer ({t} : Set G)) :
    hf.rho h = 1 ↔ (h : G) ∈ centralizer (L : Set G) := by
  have := ker_rhoH L t hf.H_le_M e
  rw [← mem_subgroupOf, ← this, MonoidHom.mem_ker]
  rfl

theorem Full.rho_of_mem_L (hf : Full L S t e) (h : centralizer ({t} : Set G)) (l : L)
    (hl : (h : G) = l) : hf.rho h = ((e l : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
  have : h = ⟨l, hf.L_le_H l.2⟩ := Subtype.ext hl
  rw [this]
  exact rhoOf_apply_of_mem e l.2

noncomputable def Full.rhoQ (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G))) :
    Sylow 2 (Perm (Fin 5)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Q.mapSurjective hf.rho_surjective

theorem Full.mem_rhoQ_iff (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (σ : Perm (Fin 5)) :
    σ ∈ (hf.rhoQ Q : Subgroup (Perm (Fin 5))) ↔
      ∃ q : centralizer ({t} : Set G), (q : G) ∈ qg t Q ∧ hf.rho q = σ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Full.rhoQ, Sylow.coe_mapSurjective, Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨q', hq', hqq⟩, rfl⟩
    have : q' = q := Subtype.ext hqq
    exact ⟨q, this ▸ hq', rfl⟩

noncomputable def Full.rhoAt (hf : Full L S t e) (g : G) : Perm (Fin 5) := by
  classical
  exact if h : g ∈ centralizer ({t} : Set G) then hf.rho ⟨g, h⟩ else 1

theorem Full.rhoAt_of_mem (hf : Full L S t e) {g : G} (hg : g ∈ centralizer ({t} : Set G)) :
    hf.rhoAt g = hf.rho ⟨g, hg⟩ := by
  classical
  simp [Full.rhoAt, hg]

theorem Full.rhoAt_mul (hf : Full L S t e) {a b : G} (ha : a ∈ centralizer ({t} : Set G))
    (hb : b ∈ centralizer ({t} : Set G)) : hf.rhoAt (a * b) = hf.rhoAt a * hf.rhoAt b := by
  rw [hf.rhoAt_of_mem (Subgroup.mul_mem _ ha hb), hf.rhoAt_of_mem ha, hf.rhoAt_of_mem hb,
    ← map_mul]
  rfl

theorem Full.rhoAt_inv (hf : Full L S t e) {a : G} (ha : a ∈ centralizer ({t} : Set G)) :
    hf.rhoAt a⁻¹ = (hf.rhoAt a)⁻¹ := by
  rw [hf.rhoAt_of_mem (Subgroup.inv_mem _ ha), hf.rhoAt_of_mem ha, ← map_inv]
  rfl

theorem Full.rhoAt_one (hf : Full L S t e) : hf.rhoAt 1 = 1 := by
  rw [hf.rhoAt_of_mem (Subgroup.one_mem _)]
  exact map_one hf.rho

theorem Full.rhoAt_eq_one_iff (hf : Full L S t e) {g : G} (hg : g ∈ centralizer ({t} : Set G)) :
    hf.rhoAt g = 1 ↔ g ∈ centralizer (L : Set G) := by
  rw [hf.rhoAt_of_mem hg]
  exact hf.rho_eq_one_iff ⟨g, hg⟩

theorem Full.rhoAt_of_mem_L (hf : Full L S t e) {l : G} (hl : l ∈ L) :
    hf.rhoAt l = ((e ⟨l, hl⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
  rw [hf.rhoAt_of_mem (hf.L_le_H hl)]
  exact hf.rho_of_mem_L _ ⟨l, hl⟩ rfl

theorem Full.rhoAt_of_mem_sg (hf : Full L S t e) {u : G} (hu : u ∈ sg L S) : hf.rhoAt u = 1 :=
  (hf.rhoAt_eq_one_iff (sg_le_centralizer_t hf.sector hu)).mpr (sg_le_centralizer hu)

theorem Full.rhoAt_conj (hf : Full L S t e) {a b : G} (ha : a ∈ centralizer ({t} : Set G))
    (hb : b ∈ centralizer ({t} : Set G)) :
    hf.rhoAt (b * a * b⁻¹) = hf.rhoAt b * hf.rhoAt a * (hf.rhoAt b)⁻¹ := by
  rw [hf.rhoAt_mul (Subgroup.mul_mem _ hb ha) (Subgroup.inv_mem _ hb), hf.rhoAt_mul hb ha,
    hf.rhoAt_inv hb]

theorem Full.sign_rhoAt_of_mem_L (hf : Full L S t e) {l : G} (hl : l ∈ L) :
    Perm.sign (hf.rhoAt l) = 1 := by
  rw [hf.rhoAt_of_mem_L hl]
  exact (Perm.mem_alternatingGroup).mp (e ⟨l, hl⟩).2

omit [Finite G] in
theorem Full.L_comm_sg (_hf : Full L S t e) {l u : G} (hl : l ∈ L) (hu : u ∈ sg L S) :
    l * u = u * l := mem_centralizer_iff.mp (sg_le_centralizer hu) l hl

omit [Finite G] in
theorem Full.L_inf_sg (hf : Full L S t e) : L ⊓ sg L S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ L ⊓ centralizer (L : Set G) := ⟨hx.1, sg_le_centralizer hx.2⟩
  rw [hf.trivial_inter] at h1
  exact h1

omit [Finite G] in
theorem Full.P_le_qg_sup (_hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) : (qg t Q ⊓ L) ⊔ sg L S ≤ qg t Q :=
  sup_le inf_le_left hSQ

theorem Full.card_PS (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G))) :
    Nat.card ((qg t Q ⊓ L) ⊔ sg L S : Subgroup G) = 4 * Nat.card (sg L S) := by
  rw [card_sup_of_commute (A := qg t Q ⊓ L) (B := sg L S)
    (fun a ha b hb => hf.L_comm_sg ha.2 hb) ?_, hf.card_P Q]
  rw [eq_bot_iff]
  intro x hx
  exact (eq_bot_iff.mp hf.L_inf_sg) ⟨hx.1.2, hx.2⟩

theorem Full.index_PS (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) :
    (((qg t Q ⊓ L) ⊔ sg L S).subgroupOf (qg t Q)).index = 2 := by
  have hA := hf.P_le_qg_sup Q hSQ
  have h1 := Subgroup.card_mul_index (((qg t Q ⊓ L) ⊔ sg L S).subgroupOf (qg t Q))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hf.card_PS Q,
    hf.card_qg_eq Q] at h1
  have hpos : 0 < 4 * Nat.card (sg L S) := by
    have : 0 < Nat.card (sg L S) := Nat.card_pos
    omega
  have h2 : (4 * Nat.card (sg L S)) * (((qg t Q ⊓ L) ⊔ sg L S).subgroupOf (qg t Q)).index =
      (4 * Nat.card (sg L S)) * 2 := by
    rw [h1]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos h2

theorem Full.exists_swap_qg (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G))) :
    ∃ h : centralizer ({t} : Set G), (h : G) ∈ qg t Q ∧
      ∃ i j : Fin 5, i ≠ j ∧ hf.rho h = swap i j := by
  obtain ⟨i, j, hij, hm⟩ := exists_swap_mem_sylow_two (hf.rhoQ Q)
  obtain ⟨q, hq, hqρ⟩ := (hf.mem_rhoQ_iff Q _).1 hm
  exact ⟨q, hq, i, j, hij, hqρ⟩

theorem Full.sign_rhoAt_of_mem_PS (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    {q : G} (hq : q ∈ (qg t Q ⊓ L) ⊔ sg L S) : Perm.sign (hf.rhoAt q) = 1 := by
  obtain ⟨p, hp, u, hu, rfl⟩ :=
    (mem_sup_iff_of_commute (A := qg t Q ⊓ L) (B := sg L S)
      (fun a ha b hb => hf.L_comm_sg ha.2 hb) q).1 hq
  rw [hf.rhoAt_mul (hf.L_le_H hp.2) (sg_le_centralizer_t hf.sector hu), map_mul,
    hf.rhoAt_of_mem_sg hu, hf.sign_rhoAt_of_mem_L hp.2]
  simp

theorem Full.mem_PS_iff_sign (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) {q : G} (hq : q ∈ qg t Q) :
    q ∈ (qg t Q ⊓ L) ⊔ sg L S ↔ Perm.sign (hf.rhoAt q) = 1 := by
  refine ⟨hf.sign_rhoAt_of_mem_PS Q, fun hsign => ?_⟩
  by_contra hnot
  obtain ⟨h, hhQ, i, j, hij, hρh⟩ := hf.exists_swap_qg Q
  have hidx := hf.index_PS Q hSQ
  have hsh : Perm.sign (hf.rhoAt (h : G)) = -1 := by
    rw [hf.rhoAt_of_mem h.2]
    show Perm.sign (hf.rho h) = -1
    rw [hρh, Perm.sign_swap hij]
  have hhA : (h : G) ∉ (qg t Q ⊓ L) ⊔ sg L S := fun hmem => by
    have := hf.sign_rhoAt_of_mem_PS Q hmem
    rw [hsh] at this
    exact absurd this (by decide)
  have hmul := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨q, hq⟩) (b := ⟨h.1, hhQ⟩)).2
    (by
      simp only [mem_subgroupOf]
      exact iff_of_false hnot hhA)
  rw [mem_subgroupOf] at hmul
  have h1 := hf.sign_rhoAt_of_mem_PS Q (show q * h ∈ _ from hmul)
  rw [hf.rhoAt_mul (qg_le_H t Q hq) h.2, map_mul, hsign, hsh] at h1
  exact absurd h1 (by decide)

omit [Finite G] in
theorem mul_self_eq_one_of_card_four (e : L ≃* alternatingGroup (Fin 5)) {X : Subgroup G}
    (hXL : X ≤ L) (hX : Nat.card X = 4) {p : G} (hp : p ∈ X) : p * p = 1 := by
  have h1 : orderOf p ∣ 4 := hX ▸ Subgroup.orderOf_dvd_natCard X hp
  have h2 : orderOf p ≠ 4 := by
    intro h
    apply orderOf_ne_four_alternatingGroup_five (e ⟨p, hXL hp⟩)
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, h]
  have h3 : orderOf p ∣ 2 := by
    have h4 : orderOf p ∣ 2 ^ 2 := by simpa using h1
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
    interval_cases k
    · simp [hk']
    · simp [hk']
    · exact absurd (by simpa using hk') h2
  rw [← sq]
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem Full.conj_mem_R (hf : Full L S t e) {x u : G} (hx : x ∈ centralizer ({t} : Set G))
    (hu : u ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) :
    x * u * x⁻¹ ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
  have hn := (centralizer_t_facts hf.sector).2.2.2
  have := hn.conj_mem ⟨u, hu.2⟩ (mem_subgroupOf.mpr hu) ⟨x, hx⟩
  exact mem_subgroupOf.mp this

theorem Full.mul_self_P (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G))) {p : G}
    (hp : p ∈ qg t Q ⊓ L) : p * p = 1 :=
  mul_self_eq_one_of_card_four e inf_le_right (hf.card_P Q) hp

theorem Full.klein_P (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G))) :
    Nonempty ((qg t Q ⊓ L : Subgroup G) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  nonempty_mulEquiv_klein (hf.card_P Q) fun _ hp => hf.mul_self_P Q hp

theorem Full.conj_mem_P (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G))) {x p : G}
    (hx : x ∈ qg t Q) (hp : p ∈ qg t Q ⊓ L) : x * p * x⁻¹ ∈ qg t Q ⊓ L := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hp.1) (Subgroup.inv_mem _ hx), ?_⟩
  exact (mem_normalizer_iff.mp (hf.H_le_M (qg_le_H t Q hx)) p).mp hp.2

theorem Full.conj_mem_sg (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) {x u : G} (hx : x ∈ qg t Q) (hu : u ∈ sg L S) :
    x * u * x⁻¹ ∈ sg L S := by
  rw [← hf.qg_inf_R Q hSQ]
  have hu' : u ∈ qg t Q ⊓ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
    rw [hf.qg_inf_R Q hSQ]
    exact hu
  exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hu'.1) (Subgroup.inv_mem _ hx),
    hf.conj_mem_R (qg_le_H t Q hx) hu'.2⟩

theorem Full.exists_conj_ne (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) {x : G} (hx : x ∈ qg t Q) {i j : Fin 5} (hij : i ≠ j)
    (hρx : hf.rhoAt x = swap i j) : ∃ p ∈ qg t Q ⊓ L, x * p * x⁻¹ ≠ p := by
  have hxH : x ∈ centralizer ({t} : Set G) := qg_le_H t Q hx
  have hD : swap i j ∈ (hf.rhoQ Q : Subgroup (Perm (Fin 5))) :=
    (hf.mem_rhoQ_iff Q _).2 ⟨⟨x, hxH⟩, hx, by rw [← hf.rhoAt_of_mem hxH]; exact hρx⟩
  obtain ⟨v, hvD, hsv, hne⟩ := exists_even_not_commute_swap_of_sylow (hf.rhoQ Q) hij hD
  obtain ⟨q, hq, hqv⟩ := (hf.mem_rhoQ_iff Q v).1 hvD
  have hqH : (q : G) ∈ centralizer ({t} : Set G) := q.2
  have hsign : Perm.sign (hf.rhoAt q) = 1 := by
    rw [hf.rhoAt_of_mem hqH]
    simpa using (congrArg Perm.sign hqv).trans hsv
  have hqA := (hf.mem_PS_iff_sign Q hSQ hq).2 hsign
  obtain ⟨p, hp, u, hu, hpu⟩ :=
    (mem_sup_iff_of_commute (A := qg t Q ⊓ L) (B := sg L S)
      (fun a ha b hb => hf.L_comm_sg ha.2 hb) q).1 hqA
  have hρp : hf.rhoAt p = v := by
    have h1 := congrArg hf.rhoAt hpu
    rw [hf.rhoAt_mul (hf.L_le_H hp.2) (sg_le_centralizer_t hf.sector hu),
      hf.rhoAt_of_mem_sg hu, mul_one, hf.rhoAt_of_mem hqH, hqv] at h1
    exact h1.symm
  refine ⟨p, hp, fun hcomm => hne ?_⟩
  have h2 := congrArg hf.rhoAt hcomm
  rw [hf.rhoAt_conj (hf.L_le_H hp.2) hxH, hρx, hρp] at h2
  calc swap i j * v = (swap i j * v * (swap i j)⁻¹) * swap i j := by group
    _ = v * swap i j := by rw [h2]

theorem Full.qg_eq_PS_sup (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) {h : G} (hh : h ∈ qg t Q) (hhA : h ∉ (qg t Q ⊓ L) ⊔ sg L S) :
    qg t Q = (qg t Q ⊓ L) ⊔ sg L S ⊔ zpowers h := by
  apply le_antisymm
  · intro q hq
    by_cases hqA : q ∈ (qg t Q ⊓ L) ⊔ sg L S
    · exact mem_sup_left hqA
    · have hidx := hf.index_PS Q hSQ
      have hmul := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨q, hq⟩) (b := ⟨h, hh⟩)).2
        (by
          simp only [mem_subgroupOf]
          exact iff_of_false hqA hhA)
      rw [mem_subgroupOf] at hmul
      have : q = (q * h) * h⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (mem_sup_left (show q * h ∈ _ from hmul))
        (mem_sup_right (Subgroup.inv_mem _ (mem_zpowers h)))
  · exact sup_le (hf.P_le_qg_sup Q hSQ) (zpowers_le.mpr hh)

theorem Full.exists_swap_of_involution (hf : Full L S t e)
    (Q : Sylow 2 (centralizer ({t} : Set G))) (hSQ : sg L S ≤ qg t Q) {x : G}
    (hx : x ∈ qg t Q) (hxA : x ∉ (qg t Q ⊓ L) ⊔ sg L S) (hx2 : x * x = 1) :
    ∃ i j : Fin 5, i ≠ j ∧ hf.rhoAt x = swap i j := by
  have hxH : x ∈ centralizer ({t} : Set G) := qg_le_H t Q hx
  have hsign : Perm.sign (hf.rhoAt x) = -1 := by
    rcases Int.units_eq_one_or (Perm.sign (hf.rhoAt x)) with h1 | h1
    · exact absurd ((hf.mem_PS_iff_sign Q hSQ hx).2 h1) hxA
    · exact h1
  have hsq : hf.rhoAt x * hf.rhoAt x = 1 := by
    rw [← hf.rhoAt_mul hxH hxH, hx2, hf.rhoAt_one]
  exact exists_swap_of_sign_eq_neg_one hsq hsign

theorem Full.exists_h (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) :
    ∃ h : G, h ∈ qg t Q ∧ (∃ i j : Fin 5, i ≠ j ∧ hf.rhoAt h = swap i j) ∧ h * h ∈ sg L S ∧
      qg t Q = (qg t Q ⊓ L) ⊔ sg L S ⊔ zpowers h := by
  obtain ⟨h, hhQ, i, j, hij, hρ⟩ := hf.exists_swap_qg Q
  have hρ' : hf.rhoAt (h : G) = swap i j := by rw [hf.rhoAt_of_mem h.2]; exact hρ
  have hhA : (h : G) ∉ (qg t Q ⊓ L) ⊔ sg L S := fun hmem => by
    have := hf.sign_rhoAt_of_mem_PS Q hmem
    rw [hρ', Perm.sign_swap hij] at this
    exact absurd this (by decide)
  refine ⟨h, hhQ, ⟨i, j, hij, hρ'⟩, ?_, hf.qg_eq_PS_sup Q hSQ hhQ hhA⟩
  have hsq : hf.rhoAt ((h : G) * h) = 1 := by
    rw [hf.rhoAt_mul h.2 h.2, hρ']
    simp [Equiv.swap_mul_self]
  have hmemC : (h : G) * h ∈ centralizer (L : Set G) :=
    (hf.rhoAt_eq_one_iff (Subgroup.mul_mem _ h.2 h.2)).1 hsq
  rw [← hf.qg_inf_R Q hSQ]
  exact ⟨Subgroup.mul_mem _ hhQ hhQ, hmemC, Subgroup.mul_mem _ h.2 h.2⟩

theorem Full.qdata (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) {x : G} (hx : x ∈ qg t Q) (hxA : x ∉ (qg t Q ⊓ L) ⊔ sg L S)
    (hx2 : x * x = 1) {s : G} {a : ℕ} (hgen : sg L S = zpowers s) (hord : orderOf s = 2 ^ a)
    (ha : 2 ≤ a) : QData (qg t Q ⊓ L) (sg L S) s x a := by
  obtain ⟨i, j, hij, hρ⟩ := hf.exists_swap_of_involution Q hSQ hx hxA hx2
  have hsS : s ∈ sg L S := hgen ▸ mem_zpowers s
  refine ⟨ha, hgen, hord, hf.klein_P Q, fun p hp => hf.L_comm_sg hp.2 hsS, ?_, hx2, hxA,
    fun p hp => hf.conj_mem_P Q hx hp, hf.conj_mem_sg Q hSQ hx hsS,
    hf.exists_conj_ne Q hSQ hx hij hρ⟩
  rw [eq_bot_iff]
  intro y hy
  exact (eq_bot_iff.mp hf.L_inf_sg) ⟨hy.1.2, hy.2⟩

theorem Full.group_eq (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) {x : G} (hx : x ∈ qg t Q) (hxA : x ∉ (qg t Q ⊓ L) ⊔ sg L S) :
    QData.group (qg t Q ⊓ L) (sg L S) x = qg t Q :=
  (hf.qg_eq_PS_sup Q hSQ hx hxA).symm

theorem Full.exists_conj_in_L (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    {p p' : G} (hp : p ∈ qg t Q ⊓ L) (hp' : p' ∈ qg t Q ⊓ L) (hp1 : p ≠ 1) (hp1' : p' ≠ 1) :
    ∃ l ∈ L, l * p * l⁻¹ = p' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup (alternatingGroup (Fin 5)) :=
    ((qg t Q ⊓ L).subgroupOf L).map e.toMonoidHom
  have hXcard : Nat.card X = 2 ^ (Nat.card (alternatingGroup (Fin 5))).factorization 2 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : qg t Q ⊓ L ≤ L)).toEquiv,
      hf.card_P Q, card_alternatingGroup_five]
    decide +kernel
  let P' : Sylow 2 (alternatingGroup (Fin 5)) := Sylow.ofCard X hXcard
  have hmem : ∀ {y : G} (hy : y ∈ qg t Q ⊓ L),
      e ⟨y, hy.2⟩ ∈ (P' : Subgroup (alternatingGroup (Fin 5))) := fun {y} hy =>
    ⟨⟨y, hy.2⟩, mem_subgroupOf.mpr hy, rfl⟩
  have hne : ∀ {y : G} (hy : y ∈ qg t Q ⊓ L), y ≠ 1 → e ⟨y, hy.2⟩ ≠ 1 := by
    intro y hy hy1 h
    apply hy1
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this
  obtain ⟨n, -, hn⟩ := exists_mem_normalizer_conj_of_sylow_two_alternatingGroup_five P'
    (hmem hp) (hmem hp') (hne hp hp1) (hne hp' hp1')
  refine ⟨(e.symm n : L), (e.symm n).2, ?_⟩
  have h1 : e.symm n * ⟨p, hp.2⟩ * (e.symm n)⁻¹ = ⟨p', hp'.2⟩ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hn
  exact congrArg Subtype.val h1

theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] : Odd (Nat.card (CFSG.oddCore X)) := by
  rw [CFSG.LocalAnalysis.oddCore_eq_pPrimeCore_two, ← Nat.coprime_two_left]
  exact CFSG.pPrimeCore_coprime_card

theorem Full.rho_eq_one_of_normal_odd (hf : Full L S t e)
    {N : Subgroup (centralizer ({t} : Set G))} (hNn : N.Normal) (hNodd : Odd (Nat.card N))
    {h : centralizer ({t} : Set G)} (hh : h ∈ N) : hf.rho h = 1 := by
  have hmapn : (N.map hf.rho).Normal := hNn.map hf.rho hf.rho_surjective
  have hmapodd : Odd (Nat.card (N.map hf.rho)) :=
    Odd.of_dvd_nat hNodd (N.card_map_dvd hf.rho)
  have hbot := @eq_bot_of_normal_odd_perm_five (N.map hf.rho) hmapn hmapodd
  have hhN : hf.rho h ∈ N.map hf.rho := ⟨h, hh, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hhN
  exact hhN

theorem Full.false_of_zStar (hf : Full L S t e)
    (hfac : ∀ g : G, ∃ c ∈ centralizer ({t} : Set G), ∃ k ∈ CFSG.oddCore G, g = c * k) :
    False := by
  have : Group.IsPerfect G := ⟨hf.perfect⟩
  have hψ : ∀ h : centralizer ({t} : Set G), (h : G) ∈ CFSG.oddCore G →
      (Perm.sign.comp hf.rho : centralizer ({t} : Set G) →* ℤˣ) h = 1 := by
    intro h hh
    have hNn : ((CFSG.oddCore G ⊓ centralizer ({t} : Set G)).subgroupOf
        (centralizer ({t} : Set G))).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [mem_subgroupOf] at hx ⊢
      refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hx.2) (Subgroup.inv_mem _ g.2)⟩
      exact (CFSG.oddCore_normal G).conj_mem _ hx.1 (g : G)
    have hNodd : Odd (Nat.card ((CFSG.oddCore G ⊓ centralizer ({t} : Set G)).subgroupOf
        (centralizer ({t} : Set G)))) := by
      have h1 : Nat.card ((CFSG.oddCore G ⊓ centralizer ({t} : Set G)).subgroupOf
          (centralizer ({t} : Set G))) ∣ Nat.card (CFSG.oddCore G) := by
        have e1 : Nat.card ((CFSG.oddCore G ⊓ centralizer ({t} : Set G)).subgroupOf
            (centralizer ({t} : Set G))) =
            Nat.card (CFSG.oddCore G ⊓ centralizer ({t} : Set G) : Subgroup G) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
        rw [e1]
        exact Subgroup.card_dvd_of_le inf_le_left
      exact Odd.of_dvd_nat (odd_card_oddCore G) h1
    have := hf.rho_eq_one_of_normal_odd hNn hNodd (h := h) (mem_subgroupOf.mpr ⟨hh, h.2⟩)
    show Perm.sign (hf.rho h) = 1
    rw [this, map_one]
  have h1 := hom_eq_one_of_factorization (H := centralizer ({t} : Set G)) (N := CFSG.oddCore G)
    hfac (Perm.sign.comp hf.rho) hψ
  obtain ⟨x, hx⟩ := hf.rho_surjective (swap 0 1)
  have h2 : (Perm.sign.comp hf.rho : centralizer ({t} : Set G) →* ℤˣ) x = -1 := by
    show Perm.sign (hf.rho x) = -1
    rw [hx, Perm.sign_swap (by decide)]
  have h3 : (Perm.sign.comp hf.rho : centralizer ({t} : Set G) →* ℤˣ) x = 1 := by
    rw [h1]
    rfl
  rw [h2] at h3
  exact absurd h3 (by decide)

theorem Full.PS_comm (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    {a b : G} (ha : a ∈ (qg t Q ⊓ L) ⊔ sg L S) (hb : b ∈ (qg t Q ⊓ L) ⊔ sg L S) :
    a * b = b * a := by
  have hP : ∀ p ∈ qg t Q ⊓ L, ∀ q ∈ qg t Q ⊓ L, p * q = q * p := fun p hp q hq =>
    comm_of_mul_self_eq_one (hf.mul_self_P Q hp) (hf.mul_self_P Q hq)
      (hf.mul_self_P Q (Subgroup.mul_mem _ hp hq))
  obtain ⟨p, hp, u, hu, rfl⟩ := (mem_sup_iff_of_commute (A := qg t Q ⊓ L) (B := sg L S)
    (fun a ha b hb => hf.L_comm_sg ha.2 hb) a).1 ha
  obtain ⟨p', hp', u', hu', rfl⟩ := (mem_sup_iff_of_commute (A := qg t Q ⊓ L) (B := sg L S)
    (fun a ha b hb => hf.L_comm_sg ha.2 hb) b).1 hb
  calc p * u * (p' * u') = p * (u * p') * u' := by group
    _ = p * (p' * u) * u' := by rw [← hf.L_comm_sg hp'.2 hu]
    _ = (p * p') * (u * u') := by group
    _ = (p' * p) * (u' * u) := by
      rw [hP p hp p' hp', sg_comm hf.sector u hu u' hu']
    _ = p' * (p * u') * u := by group
    _ = p' * (u' * p) * u := by rw [hf.L_comm_sg hp.2 hu']
    _ = p' * u' * (p * u) := by group

theorem Full.sq_mem_sg (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    {a : G} (ha : a ∈ (qg t Q ⊓ L) ⊔ sg L S) : a * a ∈ sg L S := by
  obtain ⟨p, hp, u, hu, rfl⟩ := (mem_sup_iff_of_commute (A := qg t Q ⊓ L) (B := sg L S)
    (fun a ha b hb => hf.L_comm_sg ha.2 hb) a).1 ha
  have : p * u * (p * u) = u * u := by
    calc p * u * (p * u) = p * (u * p) * u := by group
      _ = p * (p * u) * u := by rw [← hf.L_comm_sg hp.2 hu]
      _ = (p * p) * (u * u) := by group
      _ = u * u := by rw [hf.mul_self_P Q hp, one_mul]
  rw [this]
  exact Subgroup.mul_mem _ hu hu

theorem Full.eq_of_mul_self_eq_one_of_mem_PS (hf : Full L S t e)
    (Q : Sylow 2 (centralizer ({t} : Set G))) {a : G} (ha : a ∈ (qg t Q ⊓ L) ⊔ sg L S)
    (ha2 : a * a = 1) : ∃ p ∈ qg t Q ⊓ L, a = p ∨ a = p * t := by
  obtain ⟨p, hp, u, hu, rfl⟩ := (mem_sup_iff_of_commute (A := qg t Q ⊓ L) (B := sg L S)
    (fun a ha b hb => hf.L_comm_sg ha.2 hb) a).1 ha
  have huu : u * u = 1 := by
    have : p * u * (p * u) = u * u := by
      calc p * u * (p * u) = p * (u * p) * u := by group
        _ = p * (p * u) * u := by rw [← hf.L_comm_sg hp.2 hu]
        _ = (p * p) * (u * u) := by group
        _ = u * u := by rw [hf.mul_self_P Q hp, one_mul]
    rwa [this] at ha2
  refine ⟨p, hp, ?_⟩
  by_cases hu1 : u = 1
  · left
    rw [hu1, mul_one]
  · right
    have : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact huu) hu1
    rw [eq_t_of_orderOf_eq_two hf.sector hu this]

theorem Full.normalizer_fixes_t_of_no_outer (hf : Full L S t e)
    (Q : Sylow 2 (centralizer ({t} : Set G))) (hSQ : sg L S ≤ qg t Q)
    (hno : ∀ x ∈ qg t Q, x * x = 1 → x ∈ (qg t Q ⊓ L) ⊔ sg L S) :
    ∀ n ∈ normalizer ((qg t Q : Subgroup G) : Set G), n * t * n⁻¹ = t := by
  obtain ⟨h, hhQ, ⟨i, j, hij, hρ⟩, -, -⟩ := hf.exists_h Q hSQ
  obtain ⟨p₁, hp₁, hne⟩ := hf.exists_conj_ne Q hSQ hhQ hij hρ
  have hhA : h ∉ (qg t Q ⊓ L) ⊔ sg L S := fun hmem => by
    have := hf.sign_rhoAt_of_mem_PS Q hmem
    rw [hρ, Perm.sign_swap hij] at this
    exact absurd this (by decide)
  have hAchar : ∀ q ∈ qg t Q, q ∈ (qg t Q ⊓ L) ⊔ sg L S ↔
      ∀ e' ∈ qg t Q, e' * e' = 1 → q * e' = e' * q := by
    intro q hq
    refine ⟨fun hqA e' he' he'2 => hf.PS_comm Q hqA (hno e' he' he'2), fun hcomm => ?_⟩
    by_contra hqA
    have hidx := hf.index_PS Q hSQ
    have hhinv : h⁻¹ ∉ (qg t Q ⊓ L) ⊔ sg L S := fun hmem => hhA (by simpa using inv_mem hmem)
    have hmul := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨q, hq⟩)
      (b := ⟨h⁻¹, Subgroup.inv_mem _ hhQ⟩)).2 (by
        simp only [mem_subgroupOf]
        exact iff_of_false hqA hhinv)
    rw [mem_subgroupOf] at hmul
    have ha : q * h⁻¹ ∈ (qg t Q ⊓ L) ⊔ sg L S := hmul
    have h1 := hcomm p₁ hp₁.1 (hf.mul_self_P Q hp₁)
    have h2 := hf.PS_comm Q ha (mem_sup_left hp₁)
    apply hne
    have h3 : (q * h⁻¹) * (h * p₁ * h⁻¹) = (q * h⁻¹) * p₁ := by
      calc (q * h⁻¹) * (h * p₁ * h⁻¹) = (q * p₁) * h⁻¹ := by group
        _ = (p₁ * q) * h⁻¹ := by rw [h1]
        _ = p₁ * (q * h⁻¹) := by group
        _ = (q * h⁻¹) * p₁ := by rw [← h2]
    exact mul_left_cancel h3
  have hAn : ∀ n ∈ normalizer ((qg t Q : Subgroup G) : Set G),
      ∀ q ∈ (qg t Q ⊓ L) ⊔ sg L S, n * q * n⁻¹ ∈ (qg t Q ⊓ L) ⊔ sg L S := by
    intro n hn q hqA
    have hqQ : q ∈ qg t Q := hf.P_le_qg_sup Q hSQ hqA
    have hnqQ : n * q * n⁻¹ ∈ qg t Q := (mem_normalizer_iff.mp hn q).mp hqQ
    refine (hAchar _ hnqQ).2 fun e' he' he'2 => ?_
    have he'' : n⁻¹ * e' * n ∈ qg t Q := by
      have := (mem_normalizer_iff.mp (inv_mem hn) e').mp he'
      rwa [inv_inv] at this
    have he''2 : (n⁻¹ * e' * n) * (n⁻¹ * e' * n) = 1 := by
      calc (n⁻¹ * e' * n) * (n⁻¹ * e' * n) = n⁻¹ * (e' * e') * n := by group
        _ = 1 := by rw [he'2]; group
    have hc := (hAchar q hqQ).1 hqA (n⁻¹ * e' * n) he'' he''2
    calc n * q * n⁻¹ * e' = n * (q * (n⁻¹ * e' * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * e' * n) * q) * n⁻¹ := by rw [hc]
      _ = e' * (n * q * n⁻¹) := by group
  intro n hn
  obtain ⟨w, hw, hwt⟩ := exists_sq_eq_t hf.sector hf.four_le
  have hsq := hf.sq_mem_sg Q (hAn n hn w (mem_sup_right hw))
  have h1 : (n * w * n⁻¹) * (n * w * n⁻¹) = n * t * n⁻¹ := by
    rw [← hwt]
    group
  rw [h1] at hsq
  refine eq_t_of_orderOf_eq_two hf.sector hsq ?_
  rw [show n * t * n⁻¹ = MulAut.conj n t from rfl, MulEquiv.orderOf_eq]
  exact hf.sector.t_order

theorem Full.exists_involution (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) :
    ∃ x ∈ qg t Q, x ∉ (qg t Q ⊓ L) ⊔ sg L S ∧ x * x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hno : ∀ x ∈ qg t Q, x * x = 1 → x ∈ (qg t Q ⊓ L) ⊔ sg L S := fun x hx hx2 => by
    by_contra hxA
    exact hcon ⟨x, hx, hxA, hx2⟩
  have hNt := hf.normalizer_fixes_t_of_no_outer Q hSQ hno
  have hNle : normalizer ((qg t Q : Subgroup G) : Set G) ≤ centralizer ({t} : Set G) :=
    fun n hn => mem_centralizer_singleton_iff.mpr (by
      have h := hNt n hn
      calc n * t = (n * t * n⁻¹) * n := by group
        _ = t * n := by rw [h])
  have hQG : Nat.card (qg t Q) = 2 ^ (Nat.card G).factorization 2 :=
    card_eq_of_normalizer_le (qg_le_H t Q) (card_qg t Q) hNle
  let Qsyl : Sylow 2 G := Sylow.ofCard (qg t Q) hQG
  have hQsylcoe : (Qsyl : Subgroup G) = qg t Q := rfl
  have htQ : t ∈ qg t Q := hSQ hf.sector.t_mem
  obtain ⟨h, hhQ, ⟨i, j, hij, hρ⟩, hh2, hQeq⟩ := hf.exists_h Q hSQ
  obtain ⟨p₁, hp₁, hne⟩ := hf.exists_conj_ne Q hSQ hhQ hij hρ
  have hhH : h ∈ centralizer ({t} : Set G) := qg_le_H t Q hhQ
  have hp₁sq := hf.mul_self_P Q hp₁
  have hhpP : h * p₁ * h⁻¹ ∈ qg t Q ⊓ L := hf.conj_mem_P Q hhQ hp₁
  set v : G := p₁ * (h * p₁ * h⁻¹) with hv
  have hvP : v ∈ qg t Q ⊓ L := Subgroup.mul_mem _ hp₁ hhpP
  have hv1 : v ≠ 1 := by
    intro h1
    apply hne
    have h2 : h * p₁ * h⁻¹ = p₁⁻¹ := by
      have := congrArg (fun y => p₁⁻¹ * y) h1
      simpa [hv, mul_assoc] using this
    rw [h2]
    exact inv_eq_of_mul_eq_one_right hp₁sq
  have hvfix : h * v * h⁻¹ = v := by
    have hcomm : p₁ * (h * p₁ * h⁻¹) = (h * p₁ * h⁻¹) * p₁ :=
      comm_of_mul_self_eq_one hp₁sq (hf.mul_self_P Q hhpP)
        (hf.mul_self_P Q (Subgroup.mul_mem _ hp₁ hhpP))
    have hh2c : h * h * p₁ = p₁ * (h * h) := by
      have := hf.L_comm_sg hp₁.2 hh2
      exact this.symm
    calc h * v * h⁻¹ = (h * p₁ * h⁻¹) * (h * (h * p₁ * h⁻¹) * h⁻¹) := by rw [hv]; group
      _ = (h * p₁ * h⁻¹) * p₁ := by
        congr 1
        calc h * (h * p₁ * h⁻¹) * h⁻¹ = (h * h) * p₁ * (h * h)⁻¹ := by group
          _ = p₁ := by rw [hh2c]; group
      _ = v := by rw [hv, hcomm]
  have hvcent : ∀ q ∈ qg t Q, q * v = v * q := by
    have hA : (qg t Q ⊓ L) ⊔ sg L S ≤ centralizer ({v} : Set G) := by
      refine sup_le (fun a ha => mem_centralizer_singleton_iff.mpr ?_)
        (fun u hu => mem_centralizer_singleton_iff.mpr ?_)
      · exact comm_of_mul_self_eq_one (hf.mul_self_P Q ha) (hf.mul_self_P Q hvP)
          (hf.mul_self_P Q (Subgroup.mul_mem _ ha hvP))
      · exact (hf.L_comm_sg hvP.2 hu).symm
    have hh' : zpowers h ≤ centralizer ({v} : Set G) := by
      rw [zpowers_le]
      refine mem_centralizer_singleton_iff.mpr ?_
      calc h * v = (h * v * h⁻¹) * h := by group
        _ = v * h := by rw [hvfix]
    intro q hq
    rw [hQeq] at hq
    exact mem_centralizer_singleton_iff.mp (sup_le hA hh' hq)
  have htcent : ∀ q ∈ qg t Q, q * t = t * q := fun q hq =>
    mem_centralizer_singleton_iff.mp (qg_le_H t Q hq)
  have hiso : ∀ g : G, g⁻¹ * t * g ∈ qg t Q → g⁻¹ * t * g = t := by
    intro g hg
    set z' := g⁻¹ * t * g with hz'
    have hz'2 : z' * z' = 1 := by
      rw [hz']
      calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [show t * t = 1 from by rw [← sq, ← hf.sector.t_order, pow_orderOf_eq_one]]
                    group
    have hz'1 : z' ≠ 1 := by
      intro h1
      have h2 := hf.sector.t_order
      have : t = 1 := by
        have := congrArg (fun y => g * y * g⁻¹) h1
        simpa [hz', mul_assoc] using this
      rw [this, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    obtain ⟨p, hp, hpz⟩ := hf.eq_of_mul_self_eq_one_of_mem_PS Q (hno z' hg hz'2) hz'2
    by_cases hp1 : p = 1
    · rcases hpz with h1 | h1
      · rw [hp1] at h1
        exact absurd h1 (by simpa using hz'1)
      · rw [h1, hp1, one_mul]
    · exfalso
      obtain ⟨l, hl, hlpv⟩ := hf.exists_conj_in_L Q hp hvP hp1 hv1
      have hltc : l * t = t * l := mem_centralizer_iff.mp (t_mem_centralizer hf.sector) l hl
      have hz''eq : l * z' * l⁻¹ = v ∨ l * z' * l⁻¹ = v * t := by
        rcases hpz with h1 | h1
        · left
          rw [h1]
          exact hlpv
        · right
          rw [h1]
          calc l * (p * t) * l⁻¹ = (l * p * l⁻¹) * (l * t * l⁻¹) := by group
            _ = v * t := by rw [hlpv, hltc]; group
      have hz''cent : ∀ q ∈ qg t Q, q * (l * z' * l⁻¹) = (l * z' * l⁻¹) * q := by
        intro q hq
        rcases hz''eq with h1 | h1
        · rw [h1]
          exact hvcent q hq
        · rw [h1]
          calc q * (v * t) = (q * v) * t := by group
            _ = (v * q) * t := by rw [hvcent q hq]
            _ = v * (q * t) := by group
            _ = v * (t * q) := by rw [htcent q hq]
            _ = (v * t) * q := by group
      have hconj : (g * l⁻¹)⁻¹ * t * (g * l⁻¹) = l * z' * l⁻¹ := by
        rw [hz']
        group
      obtain ⟨n, hn, hnt⟩ := exists_mem_normalizer_conj Qsyl
        (fun u hu => htcent u hu) (fun u hu => hz''cent u hu) hconj
      have hnt' : n⁻¹ * t * n = t := by
        have := hNt n⁻¹ (inv_mem hn)
        rwa [inv_inv] at this
      have hzt : l * z' * l⁻¹ = t := by rw [← hnt, hnt']
      have hvt : v ∈ L ⊓ centralizer (L : Set G) := by
        refine ⟨hvP.2, ?_⟩
        rcases hz''eq with h1 | h1
        · rw [← h1, hzt]
          exact t_mem_centralizer hf.sector
        · have : v = t * t⁻¹ * v := by group
          have h2 : v = t * t⁻¹ := by
            calc v = (v * t) * t⁻¹ := by group
              _ = t * t⁻¹ := by rw [← h1, hzt]
          rw [h2, mul_inv_cancel]
          exact Subgroup.one_mem _
      rw [hf.trivial_inter, mem_bot] at hvt
      exact hv1 hvt
  have hzZ : (⟨t, htQ⟩ : (Qsyl : Subgroup G)) ∈ center (Qsyl : Subgroup G) :=
    mem_center_iff.mpr fun q => Subtype.ext (htcent q q.2)
  have hz : orderOf (⟨t, htQ⟩ : (Qsyl : Subgroup G)) = 2 :=
    (Subgroup.orderOf_mk t htQ).trans hf.sector.t_order
  have hz' := glauberman_zStar_central_sylow_involution_univ Qsyl ⟨t, htQ⟩ hzZ hz
    fun g hg => hiso g hg
  exact hf.false_of_zStar hz'.1

end Full

end CFSG.OddStandard

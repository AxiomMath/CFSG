module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroTwoPrelim
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZero

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open scoped Pointwise

theorem card_le_of_isPGroup_of_le_D4 {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {P K : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup p P) :
    Nat.card P ≤ p ^ (Nat.card K).factorization p := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : p ^ n ∣ Nat.card K := hn ▸ Subgroup.card_dvd_of_le hPK
  rw [hn]
  exact Nat.pow_le_pow_right hp.out.pos
    ((hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd)

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section CentralizerJ₀

variable {q : ℕ}

theorem J₀_map_le_centralizer (h : Setup G L f t) (d : TrialityD4Data L q) :
    d.J₀.map L.subtype ≤ centralizer ({t} : Set G) :=
  (map_subtype_le _).trans h.L_le_centralizer

theorem t_mem_centralizer_J₀ (h : Setup G L f t) (d : TrialityD4Data L q) :
    t ∈ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨j, -, rfl⟩
  exact mem_centralizer_iff.1 h.htL _ j.2

theorem t_mem_centralizer_leviJ₀ (h : Setup G L f t) (d : TrialityD4Data L q) :
    t ∈ centralizer ((d.leviJ₀.map L.subtype : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨l, -, rfl⟩
  exact mem_centralizer_iff.1 h.htL _ l.2

omit [Finite G] in
theorem mem_centralizer_of_coe_mem {E : Subgroup L} {l : L}
    (hl : (l : G) ∈ centralizer ((E.map L.subtype : Subgroup G) : Set G)) :
    l ∈ centralizer (E : Set L) :=
  mem_centralizer_iff.2 fun e he => Subtype.ext (mem_centralizer_iff.1 hl _ ⟨e, he, rfl⟩)

omit [Finite G] in
theorem coe_mem_centralizer_of_mem {E : Subgroup L} {l : L} (hl : l ∈ centralizer (E : Set L)) :
    (l : G) ∈ centralizer ((E.map L.subtype : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨e, he, rfl⟩
  exact congrArg Subtype.val (mem_centralizer_iff.1 hl e he)

theorem leviJ₀_map_le_centralizer_J₀_inf_centralizer (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) :
    d.leviJ₀.map L.subtype ≤
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) := by
  rw [h.centralizer_J₀_inf_centralizer_eq d]
  exact le_sup_of_le_left (map_mono d.leviJ₀_le_centralizer_J₀)

theorem centralizer_J₀_inf_centralizer_le_normalizer_leviJ₀ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) :
    centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer ((d.leviJ₀.map L.subtype : Subgroup G) : Set G) := by
  rw [h.centralizer_J₀_inf_centralizer_eq d]
  refine sup_le (map_le_normalizer_map fun g hg => mem_normalizer_fintype fun x hx => ?_)
    ((zpowers_le).2 (Subgroup.centralizer_le_normalizer _ (h.t_mem_centralizer_leviJ₀ d)))
  rw [← d.commutator_centralizer_J₀] at hx ⊢
  exact conj_mem_commutator (le_normalizer hg) hx

end CentralizerJ₀

theorem isSylowOf_sylowJ₀_sup_zpowers (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    IsSylowOf 2 (d.sylowJ₀.map L.subtype ⊔ zpowers t)
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G)) ∧
      Nat.card (d.sylowJ₀.map L.subtype ⊔ zpowers t : Subgroup G) = 2 * (2 ^ f) ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQcard := d.isSylowOf_sylowJ₀.card_eq
  have hcardQ : Nat.card (d.sylowJ₀.map L.subtype ⊔ zpowers t : Subgroup G) = 2 * (2 ^ f) ^ 3 := by
    rw [h.card_sup_zpowers (map_subtype_le _), card_map_of_injective L.subtype_injective,
      d.card_sylowJ₀]
  refine ⟨?_, hcardQ⟩
  rw [h.centralizer_J₀_inf_centralizer_eq d]
  refine isSylowOf_of_card (sup_le_sup_right (map_mono inf_le_right) _) ?_
  rw [hcardQ, h.card_sup_zpowers (map_subtype_le _), card_map_of_injective L.subtype_injective,
    Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, pow_add, pow_one, ← hQcard, d.card_sylowJ₀]

theorem two_pow_factorization_card_centralizer_J₀_inf_centralizer (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) :
    2 ^ (Nat.card (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⊓
      centralizer ({t} : Set G) : Subgroup G)).factorization 2 = 2 * (2 ^ f) ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS, hc⟩ := h.isSylowOf_sylowJ₀_sup_zpowers d
  rw [← hS.card_eq, hc]

section R₂

theorem J₀_map_le_normalizer_yamadaL₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    d.J₀.map L.subtype ≤ normalizer (yamadaL₂ d t : Set G) := fun _ hj =>
  le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d
    ⟨h.J₀_map_le_centralizer d hj, map_le_normalizer_map (d.J₀_le_J.trans d.J_le_normalizer_Y) hj⟩)

omit [Finite G] in
theorem J₀_map_le_normalizer_S {q : ℕ} (d : TrialityD4Data L q) :
    d.J₀.map L.subtype ≤ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
  map_le_normalizer_map (d.J₀_le_J.trans d.J_le_normalizer_S)

theorem J₀_map_le_normalizer_tM (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q) :
    d.J₀.map L.subtype ≤ normalizer ((d.M.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
  fun _ hj => mem_normalizer_sup (map_le_normalizer_map (d.J₀_le_J.trans d.J_le_normalizer_M) hj)
    (mem_normalizer_zpowers_of_comm_D4
      (mem_centralizer_singleton_iff.1 (h.J₀_map_le_centralizer d hj)))

theorem S_map_le_normalizer_tM (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q) :
    d.S.map L.subtype ≤ normalizer ((d.M.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
  fun _ hs => mem_normalizer_sup (map_le_normalizer_map d.S_le_normalizer_M hs)
    (mem_normalizer_zpowers_of_comm_D4 (mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)))

theorem yamadaL₂_le_normalizer_tM (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaL₂ d t ≤ normalizer ((d.M.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
  obtain ⟨hN, -⟩ := h.yamada_5_3_2_module d
  exact (normal_subgroupOf_iff_le_normalizer (h.tM_le_yamadaL₂ d)).1 hN

theorem yamadaR₂_le_normalizer_tM (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaR₂ d t ≤ normalizer ((d.M.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
  sup_le (h.yamadaL₂_le_normalizer_tM d) (h.S_map_le_normalizer_tM d)

theorem J₀_map_le_normalizer_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    d.J₀.map L.subtype ≤ normalizer (yamadaR₂ d t : Set G) := fun _ hj =>
  mem_normalizer_sup (h.J₀_map_le_normalizer_yamadaL₂ d hj) (J₀_map_le_normalizer_S d hj)

omit [Finite G] in
theorem J₀_map_le_centralizer_Y {q : ℕ} (d : TrialityD4Data L q) :
    d.J₀.map L.subtype ≤ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨j, hj, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact congrArg Subtype.val (mem_centralizer_iff.1 (d.Y_le_centralizer_J₀ hy) j hj).symm

theorem inv_mul_conj_mem_tM_of_mem_yamadaL₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {a x : G} (ha : a ∈ d.J₀.map L.subtype) (hx : x ∈ yamadaL₂ d t) :
    x⁻¹ * (a * x * a⁻¹) ∈ d.M.map L.subtype ⊔ zpowers t := by
  obtain ⟨hN, φ, hφ, -⟩ := h.yamada_5_3_2_module d
  have hy : a * x * a⁻¹ ∈ yamadaL₂ d t :=
    (mem_normalizer_iff.1 (h.J₀_map_le_normalizer_yamadaL₂ d ha) x).1 hx
  have hat : a * t = t * a := mem_centralizer_singleton_iff.1 (h.J₀_map_le_centralizer d ha)
  have hat' : a⁻¹ * t * a = t := by rw [mul_assoc, ← hat, inv_mul_cancel_left]
  have hz : t * x⁻¹ * t * x ∈ d.Y.map L.subtype := by
    rw [← hφ ⟨x, hx⟩]
    exact (φ (QuotientGroup.mk ⟨x, hx⟩)).2
  have haz : a * (t * x⁻¹ * t * x) = t * x⁻¹ * t * x * a :=
    (mem_centralizer_iff.1 (J₀_map_le_centralizer_Y d ha) _ hz).symm
  have key : (φ (QuotientGroup.mk ⟨a * x * a⁻¹, hy⟩) : G) = φ (QuotientGroup.mk ⟨x, hx⟩) := by
    rw [hφ, hφ]
    calc t * (a * x * a⁻¹)⁻¹ * t * (a * x * a⁻¹) =
        t * a * x⁻¹ * (a⁻¹ * t * a) * x * a⁻¹ := by group
      _ = a * t * x⁻¹ * t * x * a⁻¹ := by rw [hat', ← hat]
      _ = a * (t * x⁻¹ * t * x) * a⁻¹ := by group
      _ = t * x⁻¹ * t * x * a * a⁻¹ := by rw [haz]
      _ = t * x⁻¹ * t * x := by group
  have h3 : (QuotientGroup.mk (⟨x, hx⟩ : yamadaL₂ d t) : yamadaL₂ d t ⧸
      (d.M.map L.subtype ⊔ zpowers t).subgroupOf (yamadaL₂ d t)) =
        QuotientGroup.mk (⟨a * x * a⁻¹, hy⟩ : yamadaL₂ d t) :=
    (φ.injective (Subtype.ext key)).symm
  have h4 : (⟨x, hx⟩ : yamadaL₂ d t)⁻¹ * ⟨a * x * a⁻¹, hy⟩ ∈
      (d.M.map L.subtype ⊔ zpowers t).subgroupOf (yamadaL₂ d t) := QuotientGroup.eq.1 h3
  exact h4

theorem inv_mul_conj_mem_tM_of_mem_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {a x : G} (ha : a ∈ d.J₀.map L.subtype) (hx : x ∈ yamadaR₂ d t) :
    x⁻¹ * (a * x * a⁻¹) ∈ d.M.map L.subtype ⊔ zpowers t := by
  have hx' : x ∈ ((yamadaR₂ d t : Subgroup G) : Set G) := hx
  rw [h.coe_yamadaR₂ d] at hx'
  obtain ⟨l, hl, s, hs, rfl⟩ := hx'
  have h1 := h.inv_mul_conj_mem_tM_of_mem_yamadaL₂ d ha hl
  have h2 : s⁻¹ * (a * s * a⁻¹) ∈ d.M.map L.subtype := by
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    exact ⟨_, d.inv_mul_conj_mem_M hs₀ hj, rfl⟩
  have h3 : s⁻¹ * (l⁻¹ * (a * l * a⁻¹)) * s ∈ d.M.map L.subtype ⊔ zpowers t := by
    have := (mem_normalizer_iff.1 (h.S_map_le_normalizer_tM d (inv_mem hs)) _).1 h1
    rwa [inv_inv] at this
  have e : (l * s)⁻¹ * (a * (l * s) * a⁻¹) =
      s⁻¹ * (l⁻¹ * (a * l * a⁻¹)) * s * (s⁻¹ * (a * s * a⁻¹)) := by group
  rw [e]
  exact mul_mem h3 (mem_sup_left h2)

theorem tM_inf_centralizer_J₀ (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q) :
    (d.M.map L.subtype ⊔ zpowers t) ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) =
      d.Y.map L.subtype ⊔ zpowers t := by
  have hYM : d.Y ≤ d.M := d.Y_le_W.trans (d.W_le_F.trans d.F_le_M)
  apply le_antisymm
  · rintro x ⟨hx, hxc⟩
    rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hx with h1 | h1
    · obtain ⟨m, hm, rfl⟩ := h1
      have hmY : m ∈ d.Y := by
        rw [← d.M_inf_centralizer_J₀]
        exact ⟨hm, mem_centralizer_of_coe_mem hxc⟩
      exact mem_sup_left ⟨m, hmY, rfl⟩
    · obtain ⟨m, hm, hmx⟩ := h1
      have htx : t * x ∈ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
        mul_mem (h.t_mem_centralizer_J₀ d) hxc
      rw [← hmx] at htx
      have hmY : m ∈ d.Y := by
        rw [← d.M_inf_centralizer_J₀]
        exact ⟨hm, mem_centralizer_of_coe_mem htx⟩
      exact (h.mem_sup_zpowers_iff (map_subtype_le _)).2 (Or.inr ⟨m, hmY, hmx⟩)
  · refine sup_le (le_inf (le_sup_of_le_left (map_mono hYM)) ?_)
      ((zpowers_le).2 ⟨mem_sup_right (mem_zpowers t), h.t_mem_centralizer_J₀ d⟩)
    rintro _ ⟨y, hy, rfl⟩
    exact coe_mem_centralizer_of_mem (d.Y_le_centralizer_J₀ hy)

theorem relIndex_tM_yamadaL₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    (d.M.map L.subtype ⊔ zpowers t).relIndex (yamadaL₂ d t) = (2 ^ f) ^ 2 := by
  obtain ⟨hN, φ, -⟩ := h.yamada_5_3_2_module d
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr φ.toEquiv,
    card_map_of_injective L.subtype_injective, d.card_Y]

theorem yamadaL₂_inf_S (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaL₂ d t ⊓ d.S.map L.subtype = d.M.map L.subtype := by
  apply le_antisymm
  · rintro x ⟨hx2, hxS⟩
    have hxM : x ∈ d.M.map L.subtype ⊔ zpowers t := by
      rw [← (h.two_core_L₂ d).2.1]
      exact ⟨hx2, h.S_le_centralizer d hxS⟩
    rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hxM with h1 | h1
    · exact h1
    · exfalso
      apply h.t_not_mem_L
      have := mul_mem ((map_subtype_le _) h1) (inv_mem ((map_subtype_le _) hxS))
      rwa [mul_inv_cancel_right] at this
  · exact le_inf ((le_sup_left).trans (h.tM_le_yamadaL₂ d)) (map_mono d.M_le_S)

theorem relIndex_yamadaL₂_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    (yamadaL₂ d t).relIndex (yamadaR₂ d t) = 2 ^ f := by
  have h1 := ncard_mul_mul_card_inf (yamadaL₂ d t) (d.S.map L.subtype)
  rw [← h.coe_yamadaR₂ d, ← Nat.card_coe_set_eq, h.yamadaL₂_inf_S d,
    card_map_of_injective L.subtype_injective, card_map_of_injective L.subtype_injective,
    d.card_M, d.card_S] at h1
  have h2 := Subgroup.relIndex_mul_card (yamadaL₂ d t) (yamadaR₂ d t)
  rw [inf_eq_left.2 le_sup_left] at h2
  have h3 : (yamadaL₂ d t).relIndex (yamadaR₂ d t) * Nat.card (yamadaL₂ d t) * (2 ^ f) ^ 11 =
      2 ^ f * Nat.card (yamadaL₂ d t) * (2 ^ f) ^ 11 := by
    rw [h2]
    calc Nat.card (yamadaR₂ d t) * (2 ^ f) ^ 11 = Nat.card (yamadaL₂ d t) * (2 ^ f) ^ 12 := h1
      _ = 2 ^ f * Nat.card (yamadaL₂ d t) * (2 ^ f) ^ 11 := by ring
  have hpos : 0 < Nat.card (yamadaL₂ d t) * (2 ^ f) ^ 11 := Nat.mul_pos Nat.card_pos (by positivity)
  have h4 : (yamadaL₂ d t).relIndex (yamadaR₂ d t) * (Nat.card (yamadaL₂ d t) * (2 ^ f) ^ 11) =
      2 ^ f * (Nat.card (yamadaL₂ d t) * (2 ^ f) ^ 11) := by
    rw [← mul_assoc, ← mul_assoc]
    exact h3
  exact Nat.eq_of_mul_eq_mul_right hpos h4

theorem relIndex_tM_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    (d.M.map L.subtype ⊔ zpowers t).relIndex (yamadaR₂ d t) = (2 ^ f) ^ 3 := by
  rw [← Subgroup.relIndex_mul_relIndex (d.M.map L.subtype ⊔ zpowers t) (yamadaL₂ d t)
    (yamadaR₂ d t) (h.tM_le_yamadaL₂ d) le_sup_left,
    h.relIndex_tM_yamadaL₂ d, h.relIndex_yamadaL₂_yamadaR₂ d]
  ring

theorem card_yamadaR₂_inf_centralizer_J₀ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    Nat.card (yamadaR₂ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :
      Subgroup G) = 2 * (2 ^ f) ^ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : ¬ 2 ∣ Nat.card (d.J₀.map L.subtype : Subgroup G) := by
    rw [card_map_of_injective L.subtype_injective]
    exact d.odd_card_J₀.not_two_dvd_nat
  rw [card_inf_centralizer_eq_of_coprime_D4 (P := yamadaR₂ d t)
    ((h.tM_le_yamadaL₂ d).trans le_sup_left)
    (h.yamadaR₂_le_normalizer_tM d) (h.J₀_map_le_normalizer_yamadaR₂ d)
    (h.J₀_map_le_normalizer_tM d) (h.isPGroup_tM d) hA
    (fun a ha x hx => h.inv_mul_conj_mem_tM_of_mem_yamadaR₂ d ha hx),
    h.tM_inf_centralizer_J₀ d, h.card_sup_zpowers (map_subtype_le _),
    card_map_of_injective L.subtype_injective, d.card_Y, h.relIndex_tM_yamadaR₂ d]
  ring

end R₂

theorem isPGroup_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    IsPGroup 2 (yamadaR₂ d t : Subgroup G) :=
  (h.isPGroup_yamadaR₁_sup_yamadaL₂ d).to_le
    (sup_le le_sup_right ((le_sup_right : d.S.map L.subtype ≤ yamadaR₁ d t).trans le_sup_left))

theorem not_le_centralizer_of_isSylowOf_centralizer_J₀ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) :
    ¬ T ≤ centralizer ({t} : Set G) := by
  intro hTt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card T ≤ 2 * (2 ^ f) ^ 3 := by
    rw [← h.two_pow_factorization_card_centralizer_J₀_inf_centralizer d]
    exact card_le_of_isPGroup_of_le_D4 (le_inf hT.le hTt) hT.isPGroup
  have h2 : 2 * (2 ^ f) ^ 5 ≤ Nat.card T := by
    rw [← h.card_yamadaR₂_inf_centralizer_J₀ d, hT.card_eq]
    exact card_le_of_isPGroup_of_le_D4 inf_le_right ((h.isPGroup_yamadaR₂ d).to_le inf_le_left)
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
  have hq3 : 0 < (2 ^ f) ^ 3 := by positivity
  have h3 : 2 * (2 ^ f) ^ 5 = 2 * (2 ^ f) ^ 3 * ((2 ^ f) ^ 2) := by ring
  have h4 : 4 ≤ (2 ^ f) ^ 2 := by nlinarith
  nlinarith

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4

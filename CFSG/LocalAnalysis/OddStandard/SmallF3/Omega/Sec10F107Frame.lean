module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F1051Frame

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G} (F : PspFrame L)

open scoped Classical in
@[expose] noncomputable def phiG (g : G) : P45 :=
  if h : g ∈ normalizer (L : Set G) then F.φ ⟨g, h⟩ else 1

theorem phiG_of_mem {g : G} (h : g ∈ normalizer (L : Set G)) : F.phiG g = F.φ ⟨g, h⟩ :=
  dif_pos h

theorem phiG_mul {g h : G} (hg : g ∈ normalizer (L : Set G)) (hh : h ∈ normalizer (L : Set G)) :
    F.phiG (g * h) = F.phiG g * F.phiG h := by
  rw [F.phiG_of_mem hg, F.phiG_of_mem hh, F.phiG_of_mem ((normalizer (L : Set G)).mul_mem hg hh)]
  exact map_mul F.φ ⟨g, hg⟩ ⟨h, hh⟩

theorem phiG_inv {g : G} (hg : g ∈ normalizer (L : Set G)) : F.phiG g⁻¹ = (F.phiG g)⁻¹ := by
  rw [F.phiG_of_mem hg, F.phiG_of_mem ((normalizer (L : Set G)).inv_mem hg)]
  exact map_inv F.φ ⟨g, hg⟩

theorem phiG_one : F.phiG 1 = 1 := by
  rw [F.phiG_of_mem (normalizer (L : Set G)).one_mem]
  exact map_one F.φ

theorem phiG_psi (l : ↥L) : F.phiG (l : G) = F.ψ l := F.phiG_of_mem _

theorem phiG_mem_A {g : G} (hg : g ∈ normalizer (L : Set G)) :
    F.phiG g ∈ QA45.originalSubgroup := by
  rw [F.phiG_of_mem hg]
  exact F.mem_A _

theorem phiG_eq_one_iff {g : G} (hg : g ∈ normalizer (L : Set G)) :
    F.phiG g = 1 ↔ g ∈ centralizer (L : Set G) := by
  rw [F.phiG_of_mem hg]
  exact F.ker_iff ⟨g, hg⟩

theorem phiG_comm_psi {g : G} (hg : g ∈ normalizer (L : Set G)) (l : ↥L) :
    F.phiG g * F.ψ l = F.ψ l * F.phiG g ↔ g * l = l * g := by
  rw [F.phiG_of_mem hg]
  exact F.comm_phi_psi_iff ⟨g, hg⟩ l

open scoped Classical in
@[expose] noncomputable def imgS (S X : Subgroup G) : Subgroup P45 :=
  ((X ⊓ S).subgroupOf (normalizer (L : Set G))).map F.φ

@[expose] def preS (S : Subgroup G) (K : Subgroup P45) : Subgroup G :=
  (K.comap F.φ).map (normalizer (L : Set G)).subtype ⊓ S

theorem mem_imgS {S X : Subgroup G} (hS : S ≤ normalizer (L : Set G)) {p : P45} :
    p ∈ F.imgS S X ↔ ∃ x ∈ X, x ∈ S ∧ F.phiG x = p := by
  unfold imgS
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hy
    exact ⟨y, hy.1, hy.2, F.phiG_of_mem y.2⟩
  · rintro ⟨x, hxX, hxS, rfl⟩
    exact ⟨⟨x, hS hxS⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hxX, hxS⟩),
      (F.phiG_of_mem (hS hxS)).symm⟩

theorem mem_preS {S : Subgroup G} (hS : S ≤ normalizer (L : Set G)) {K : Subgroup P45} {x : G} :
    x ∈ F.preS S K ↔ x ∈ S ∧ F.phiG x ∈ K := by
  unfold preS
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hxS⟩
    refine ⟨hxS, ?_⟩
    show F.phiG (y : G) ∈ K
    rw [F.phiG_of_mem y.2]
    exact hy
  · rintro ⟨hxS, hK⟩
    exact ⟨⟨⟨x, hS hxS⟩, by rwa [F.phiG_of_mem (hS hxS)] at hK, rfl⟩, hxS⟩

structure Setup107 (L : Subgroup G) (t : G) (S : Subgroup G) : Prop where
  S_le_N : S ≤ normalizer (L : Set G)
  S_two : IsPGroup 2 S
  t_sq : t * t = 1
  t_ne : t ≠ 1
  t_comm : ∀ s ∈ S, s * t = t * s
  cent_S : centralizer (L : Set G) ⊓ S = zpowers t

namespace Setup107

variable {F} {t : G} {S : Subgroup G} (h : Setup107 L t S)

include h

theorem t_mem_inf : t ∈ centralizer (L : Set G) ⊓ S := by
  rw [h.cent_S]
  exact Subgroup.mem_zpowers t

theorem t_mem : t ∈ S := (Subgroup.mem_inf.1 h.t_mem_inf).2

theorem t_cent : t ∈ centralizer (L : Set G) := (Subgroup.mem_inf.1 h.t_mem_inf).1

theorem t_mem_N : t ∈ normalizer (L : Set G) := h.S_le_N h.t_mem

theorem phiG_t : F.phiG t = 1 :=
  (F.phiG_eq_one_iff h.t_mem_N).2 h.t_cent

theorem phiG_eq_one_iff_S {s : G} (hs : s ∈ S) : F.phiG s = 1 ↔ s = 1 ∨ s = t := by
  rw [F.phiG_eq_one_iff (h.S_le_N hs), ← mem_zpowers_of_sq h.t_sq, ← h.cent_S, Subgroup.mem_inf]
  exact ⟨fun hc => ⟨hc, hs⟩, fun hc => hc.1⟩

theorem phiG_eq_iff {s s' : G} (hs : s ∈ S) (hs' : s' ∈ S) :
    F.phiG s = F.phiG s' ↔ s' = s ∨ s' = s * t := by
  have hN := h.S_le_N
  have key : F.phiG s = F.phiG s' ↔ F.phiG (s⁻¹ * s') = 1 := by
    rw [F.phiG_mul ((normalizer (L : Set G)).inv_mem (hN hs)) (hN hs'), F.phiG_inv (hN hs)]
    exact ⟨fun e => by rw [e]; exact inv_mul_cancel _, fun e => inv_mul_eq_one.1 e⟩
  rw [key, h.phiG_eq_one_iff_S (S.mul_mem (S.inv_mem hs) hs')]
  constructor
  · rintro (e | e)
    · exact Or.inl (inv_mul_eq_one.1 e).symm
    · right
      rw [← e]
      group
  · rintro (e | e)
    · left
      rw [e]
      group
    · right
      rw [e]
      group

theorem imgS_le_A (X : Subgroup G) : F.imgS S X ≤ QA45.originalSubgroup := by
  intro p hp
  obtain ⟨x, -, hxS, rfl⟩ := (F.mem_imgS h.S_le_N).1 hp
  exact F.phiG_mem_A (h.S_le_N hxS)

theorem isPGroup_imgS {X : Subgroup G} (hXS : X ≤ S) : IsPGroup 2 (F.imgS S X) := by
  have hX : IsPGroup 2 X := h.S_two.to_le hXS
  have hN := hXS.trans h.S_le_N
  have h1 : IsPGroup 2 ↥(X.subgroupOf (normalizer (L : Set G))) :=
    hX.of_equiv (Subgroup.subgroupOfEquivOfLe hN).symm
  have h2 : F.imgS S X = (X.subgroupOf (normalizer (L : Set G))).map F.φ := by
    rw [imgS, inf_eq_left.2 hXS]
  rw [h2]
  exact h1.map F.φ

theorem card_eq_ker {X : Subgroup G} (hXS : X ≤ S) :
    ∃ k : ℕ, Nat.card X = k * Nat.card (F.imgS S X) ∧ (t ∈ X → k = 2) ∧ (t ∉ X → k = 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := hXS.trans h.S_le_N
  let f : ↥X →* P45 := F.φ.comp (Subgroup.inclusion hN)
  have hker : ∀ x : ↥X, x ∈ f.ker ↔ (x : G) = 1 ∨ (x : G) = t := by
    intro x
    rw [MonoidHom.mem_ker]
    show F.φ ⟨(x : G), hN x.2⟩ = 1 ↔ _
    rw [← F.phiG_of_mem (hN x.2)]
    exact h.phiG_eq_one_iff_S (hXS x.2)
  have hrange : f.range = F.imgS S X := by
    ext p
    rw [MonoidHom.mem_range, F.mem_imgS h.S_le_N]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, hXS x.2, F.phiG_of_mem (hN x.2)⟩
    · rintro ⟨x, hx, hxS, rfl⟩
      exact ⟨⟨x, hx⟩, (F.phiG_of_mem (hN hx)).symm⟩
  refine ⟨Nat.card f.ker, ?_, ?_, ?_⟩
  · rw [← hrange]
    exact (Subgroup.card_ker_mul_card_range f).symm
  · intro ht
    have hk : f.ker = (zpowers t).subgroupOf X := by
      ext x
      rw [hker, Subgroup.mem_subgroupOf, mem_zpowers_of_sq h.t_sq]
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_le.2 ht)).toEquiv,
      Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact h.t_sq) h.t_ne
  · intro ht
    have hk : f.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases (hker x).1 hx with h1 | h1
      · exact Subgroup.mem_bot.2 (Subtype.ext h1)
      · exact absurd (h1 ▸ x.2) ht
    rw [hk, Subgroup.card_bot]

theorem card_of_t_mem {X : Subgroup G} (hXS : X ≤ S) (ht : t ∈ X) :
    Nat.card X = 2 * Nat.card (F.imgS S X) := by
  obtain ⟨k, hk, h2, -⟩ := h.card_eq_ker (F := F) hXS
  rw [hk, h2 ht]

theorem card_of_t_not_mem {X : Subgroup G} (hXS : X ≤ S) (ht : t ∉ X) :
    Nat.card X = Nat.card (F.imgS S X) := by
  obtain ⟨k, hk, -, h1⟩ := h.card_eq_ker (F := F) hXS
  rw [hk, h1 ht, one_mul]

theorem imgS_preS {K : Subgroup P45} (hK : K ≤ F.imgS S S) : F.imgS S (F.preS S K) = K := by
  ext p
  rw [F.mem_imgS h.S_le_N]
  constructor
  · rintro ⟨x, hx, -, rfl⟩
    exact ((F.mem_preS h.S_le_N).1 hx).2
  · intro hp
    obtain ⟨x, -, hxS, rfl⟩ := (F.mem_imgS h.S_le_N).1 (hK hp)
    exact ⟨x, (F.mem_preS h.S_le_N).2 ⟨hxS, hp⟩, hxS, rfl⟩

theorem preS_imgS {X : Subgroup G} (hXS : X ≤ S) (ht : t ∈ X) :
    F.preS S (F.imgS S X) = X := by
  ext x
  rw [F.mem_preS h.S_le_N]
  constructor
  · rintro ⟨hxS, hx⟩
    obtain ⟨x', hx'X, hx'S, hxx'⟩ := (F.mem_imgS h.S_le_N).1 hx
    rcases (h.phiG_eq_iff hx'S hxS).1 hxx' with e | e
    · rw [e]
      exact hx'X
    · rw [e]
      exact X.mul_mem hx'X ht
  · intro hx
    exact ⟨hXS hx, (F.mem_imgS h.S_le_N).2 ⟨x, hx, hXS hx, rfl⟩⟩

theorem preS_le (K : Subgroup P45) : F.preS S K ≤ S := fun _ hx => ((F.mem_preS h.S_le_N).1 hx).1

theorem t_mem_preS (K : Subgroup P45) : t ∈ F.preS S K :=
  (F.mem_preS h.S_le_N).2 ⟨h.t_mem, by rw [h.phiG_t]; exact K.one_mem⟩

theorem card_preS {K : Subgroup P45} (hK : K ≤ F.imgS S S) :
    Nat.card (F.preS S K) = 2 * Nat.card K := by
  rw [h.card_of_t_mem (F := F) (h.preS_le K) (h.t_mem_preS K), h.imgS_preS hK]

theorem comm_imgS {X : Subgroup G} (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) :
    ∀ p ∈ F.imgS S X, ∀ q ∈ F.imgS S X, p * q = q * p := by
  intro p hp q hq
  obtain ⟨x, hx, hxS, rfl⟩ := (F.mem_imgS h.S_le_N).1 hp
  obtain ⟨y, hy, hyS, rfl⟩ := (F.mem_imgS h.S_le_N).1 hq
  rw [← F.phiG_mul (h.S_le_N hxS) (h.S_le_N hyS), ← F.phiG_mul (h.S_le_N hyS) (h.S_le_N hxS),
    hXc x hx y hy]

theorem sq_imgS {X : Subgroup G} (hXs : ∀ a ∈ X, a * a = 1) : ∀ p ∈ F.imgS S X, p * p = 1 := by
  intro p hp
  obtain ⟨x, hx, hxS, rfl⟩ := (F.mem_imgS h.S_le_N).1 hp
  rw [← F.phiG_mul (h.S_le_N hxS) (h.S_le_N hxS), hXs x hx, F.phiG_one]

end Setup107

end PspFrame

end CFSG.OddStandard.SmallF3.Omega

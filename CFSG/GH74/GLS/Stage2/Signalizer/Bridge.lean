module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Bridge

theorem pCore_quotient_pCore {A : Type} [Group A] (p : ℕ) [Fact p.Prime] :
    pCore p (A ⧸ pCore p A) = ⊥ := by
  set N : Subgroup A := pCore p A with hN
  set M : Subgroup (A ⧸ N) := pCore p (A ⧸ N) with hM
  set M' : Subgroup A := M.comap (QuotientGroup.mk' N) with hM'
  have hM'n : M'.Normal := (inferInstance : M.Normal).comap _
  have hpg : IsPGroup p ↥M' := by
    intro g
    have h1 := (pCore_isPGroup (p := p) (G := A ⧸ N)) ⟨QuotientGroup.mk' N g.1, g.2⟩
    obtain ⟨a, ha⟩ := h1
    have h2 : (g.1 ^ (p ^ a)) ∈ N := by
      have : (QuotientGroup.mk' N g.1) ^ (p ^ a) = 1 := by
        have := congrArg Subtype.val ha
        simpa using this
      rw [← map_pow] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    have h3 := (pCore_isPGroup (p := p) (G := A)) ⟨g.1 ^ (p ^ a), h2⟩
    obtain ⟨b, hb⟩ := h3
    refine ⟨a + b, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hb
    simp only [OneMemClass.coe_one, SubmonoidClass.coe_pow] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hle : M' ≤ N := le_sSup ⟨hM'n, hpg⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have : a ∈ M' := hx
  have := hle this
  simp only [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff _).mpr this

theorem exists_lift_centralizer {A : Type} [Group A] [Finite A] (N : Subgroup A) [N.Normal]
    (hN : Odd (Nat.card ↥N)) {z : A} (hz : z * z = 1) {a : A}
    (h : (QuotientGroup.mk z : A ⧸ N) * QuotientGroup.mk a = QuotientGroup.mk a * QuotientGroup.mk z) :
    ∃ c : A, c * z = z * c ∧ (QuotientGroup.mk c : A ⧸ N) = QuotientGroup.mk a := by
  classical
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  let T : Type := {x : A // (QuotientGroup.mk x : A ⧸ N) = QuotientGroup.mk a}
  have : Finite T := inferInstance
  have : Fintype T := Fintype.ofFinite T
  let f : T → T := fun x => ⟨z * x.1 * z⁻¹, by
    have hx := x.2
    show (QuotientGroup.mk (z * x.1 * z⁻¹) : A ⧸ N) = QuotientGroup.mk a
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hx, h, QuotientGroup.mk_inv,
      mul_inv_cancel_right]⟩
  have hf : Function.Involutive f := by
    intro x
    apply Subtype.ext
    show z * (z * x.1 * z⁻¹) * z⁻¹ = x.1
    rw [hzi]
    calc z * (z * x.1 * z) * z = (z * z) * x.1 * (z * z) := by group
      _ = x.1 := by rw [hz]; group
  let σ : Equiv.Perm T := hf.toPerm f
  have hσ : σ ^ 2 ^ 1 = 1 := by
    ext x
    simp [σ, pow_two, hf x]
  have hcard : Fintype.card T = Nat.card ↥N := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ⟨fun x => ⟨a⁻¹ * x.1, ?_⟩, fun n => ⟨a * n.1, ?_⟩, ?_, ?_⟩
    · have hx := x.2
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, inv_mul_cancel]
    · show (QuotientGroup.mk (a * n.1) : A ⧸ N) = QuotientGroup.mk a
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n.1).mpr n.2, mul_one]
    · intro x; apply Subtype.ext; simp
    · intro n; apply Subtype.ext; simp
  have hnd : ¬ 2 ∣ Fintype.card T := by
    rw [hcard]
    exact (Nat.not_even_iff_odd.mpr hN) ∘ even_iff_two_dvd.mpr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hnd hσ
  refine ⟨x.1, ?_, x.2⟩
  have : f x = x := hx
  have h2 := congrArg Subtype.val this
  simp only [f] at h2
  rw [hzi] at h2
  calc x.1 * z = (z * x.1 * z) * z := by rw [h2]
    _ = z * x.1 := by
      calc (z * x.1 * z) * z = z * x.1 * (z * z) := by group
        _ = z * x.1 := by rw [hz]; group

variable {G : Type} [Group G]

@[expose] def xBar (p : ℕ) (H X : Subgroup G) : Subgroup (Sec H (pCore p ↥H)) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (pCore p ↥H))

theorem mk_mem_normalizer_xBar (p : ℕ) {H X : Subgroup G} {c : ↥H}
    (hc : (c : G) ∈ normalizer (X : Set G)) :
    (QuotientGroup.mk c : Sec H (pCore p ↥H)) ∈
      normalizer ((xBar p H X : Subgroup (Sec H (pCore p ↥H))) : Set _) := by
  have fwd : ∀ c : ↥H, (c : G) ∈ normalizer (X : Set G) → ∀ y ∈ xBar p H X,
      (QuotientGroup.mk c : Sec H (pCore p ↥H)) * y * (QuotientGroup.mk c)⁻¹ ∈ xBar p H X := by
    intro c hc y hy
    obtain ⟨y', hy', rfl⟩ := hy
    refine ⟨c * y' * c⁻¹, ?_, ?_⟩
    · have : (c : G) * (y' : G) * (c : G)⁻¹ ∈ X := ((mem_normalizer_iff.mp hc) (y' : G)).mp hy'
      exact this
    · simp
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact fwd c hc y
  · intro hy
    have hc' : ((c⁻¹ : ↥H) : G) ∈ normalizer (X : Set G) := by
      have := (normalizer (X : Set G)).inv_mem hc
      simpa using this
    have := fwd c⁻¹ hc' _ hy
    simpa [mul_assoc] using this

variable [Finite G]

theorem sig4B_of_sub {z : G} (hz2 : orderOf z = 2) {H X : Subgroup G} {p : ℕ} (h : Sig4Sub G z H p X)
    (hnot : ¬ X ≤ Op p H) : Sig4B G z H (pCore p ↥H) h.A.z_mem p (xBar p H X) := by
  have hpr : Fact p.Prime := ⟨h.A.prime⟩
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz2] at this
    simpa [pow_two] using this
  have hodd : Odd (Nat.card ↥(pCore p ↥H)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := ↥H)).exists_card_eq
    rw [hn]
    exact (h.A.prime.odd_of_ne_two h.A.odd).pow
  refine ⟨h.proper, hodd, ⟨h.A.prime, h.A.odd, Subgroup.mem_top _, le_top, ?_, ?_, ?_, ?_⟩,
    pCore_quotient_pCore p⟩
  · have h1 : IsPGroup p ↥(X.subgroupOf H) :=
      h.A.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.A.X_le).symm
    exact h1.map (QuotientGroup.mk' (pCore p ↥H))
  · intro hbot
    apply hnot
    intro x hx
    have hxH : x ∈ H := h.A.X_le hx
    have hmem : (⟨x, hxH⟩ : ↥H) ∈ X.subgroupOf H := hx
    have hx1 : (QuotientGroup.mk' (pCore p ↥H) ⟨x, hxH⟩ : Sec H (pCore p ↥H)) ∈ xBar p H X :=
      ⟨_, hmem, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hx1
    exact ⟨⟨x, hxH⟩, (QuotientGroup.eq_one_iff _).mp hx1, rfl⟩
  · intro c _ hc
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
    obtain ⟨c₀, hc₀, hc₀a⟩ := exists_lift_centralizer (pCore p ↥H) hodd
      (z := (⟨z, h.A.z_mem⟩ : ↥H)) (Subtype.ext hzz) (a := a) hc'.symm
    have hcz : (c₀ : G) ∈ centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hc₀
    have hcn := h.A.inv (c₀ : G) c₀.2 hcz
    rw [← hc₀a]
    exact mk_mem_normalizer_xBar p hcn
  · have h1 : ⁅X.subgroupOf H, zpowers (⟨z, h.A.z_mem⟩ : ↥H)⁆ = X.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le h.A.X_le]
      simpa using h.A.comm
    unfold xBar zSec
    rw [show (QuotientGroup.mk ⟨z, h.A.z_mem⟩ : Sec H (pCore p ↥H)) =
      QuotientGroup.mk' (pCore p ↥H) ⟨z, h.A.z_mem⟩ from rfl, ← MonoidHom.map_zpowers,
      ← Subgroup.map_commutator, h1]

theorem signalizer_sub (h19 : B_signalizer_19_9) {z : G} (hz2 : orderOf z = 2) {H X : Subgroup G}
    {p : ℕ} (h : Sig4Sub G z H p X) :
    (∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → X ≤ centralizer ((Op r H : Subgroup G) : Set G)) ∧
      (X ≤ pPrimeCoreOf 2 H → X ≤ Op p H) := by
  have hz : z ∈ H := h.A.z_mem
  have hHz2 : orderOf (⟨z, hz⟩ : ↥H) = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  have hXp : IsPGroup p ↥(X.subgroupOf H) :=
    h.A.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.A.X_le).symm
  have hinv : ∀ c ∈ centralizer ({(⟨z, hz⟩ : ↥H)} : Set ↥H), c ∈ normalizer ((X.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro c hc
    have hcz : (c : G) ∈ centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
    have hcn := h.A.inv (c : G) c.2 hcz
    rw [mem_normalizer_iff] at hcn ⊢
    intro y
    exact hcn (y : G)
  have hcomm : ⁅X.subgroupOf H, zpowers (⟨z, hz⟩ : ↥H)⁆ = X.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le h.A.X_le]
    simpa using h.A.comm
  obtain ⟨h1, h2⟩ := h19 ↥H ⟨z, hz⟩ hHz2 p h.A.prime h.A.odd (X.subgroupOf H) hXp hinv hcomm
  refine ⟨fun r hr hr2 hrp => ?_, fun hX => ?_⟩
  · intro x hx y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hxH : x ∈ H := h.A.X_le hx
    have hmem : (⟨x, hxH⟩ : ↥H) ∈ X.subgroupOf H := hx
    have := Subgroup.mem_centralizer_iff.mp (h1 r hr hr2 hrp hmem) y₀ hy₀
    exact congrArg Subtype.val this
  · intro x hx
    have hxH : x ∈ H := h.A.X_le hx
    have hmem : (⟨x, hxH⟩ : ↥H) ∈ X.subgroupOf H := hx
    have hX' : X.subgroupOf H ≤ pPrimeCore 2 ↥H := by
      intro w hw
      obtain ⟨w₀, hw₀, hww⟩ := hX hw
      have : w₀ = w := Subtype.ext hww
      rwa [← this]
    exact ⟨⟨x, hxH⟩, h2 hX' hmem, rfl⟩

end Bridge

end CFSG.GH74.GLS.Stage2.Signalizer

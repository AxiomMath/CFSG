module

public import CFSG.HardMathSupport.Malle.Proving.IsolatedZStar
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreOddNormal

public section

namespace CFSG.HardMathSupport.Malle.Proving

open Subgroup

theorem exists_normal_complement_of_selfNormalizing {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (Q : Subgroup K) (hQ : IsPGroup p Q) (hndvd : ¬ p ∣ Q.index)
    (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hN : ∀ g : K, g ∈ normalizer (Q : Set K) → g ∈ Q) :
    ∃ F : Subgroup K, F.Normal ∧ IsComplement' F Q := by
  have : Fact p.Prime := ⟨hp⟩
  let P : Sylow p K := hQ.toSylow hndvd
  have hP : normalizer (P : Set K) ≤ centralizer (P : Set K) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro h hh
    exact hab h hh g (hN g hg)
  exact ⟨(MonoidHom.transferSylow P hP).ker, inferInstance,
    MonoidHom.ker_transferSylow_isComplement' P hP⟩

theorem mem_of_sq_mem {G : Type*} [Group G] (K : Subgroup G) {x : G} (hodd : Odd (orderOf x))
    (hsq : x ^ 2 ∈ K) : x ∈ K := by
  obtain ⟨m, hm⟩ := hodd
  have h1 : x ^ (2 * (m + 1)) = x := by
    calc x ^ (2 * (m + 1)) = x ^ (orderOf x + 1) := by rw [hm]; ring_nf
      _ = x := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
  have h2 : x = (x ^ 2) ^ (m + 1) := by rw [← pow_mul]; exact h1.symm
  rw [h2]
  exact K.pow_mem hsq _

theorem mem_of_commutator_mem_of_inverted {G : Type*} [Group G] (K : Subgroup G) {u x : G}
    (hodd : Odd (orderOf x)) (hc : x * u * x⁻¹ * u⁻¹ ∈ K) (hinv : u * x * u⁻¹ = x⁻¹) : x ∈ K := by
  have hx' : u * x⁻¹ * u⁻¹ = x := by
    have : u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ := by group
    rw [this, hinv, inv_inv]
  have heq : x * u * x⁻¹ * u⁻¹ = x ^ 2 := by
    rw [show x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) by group, hx', sq]
  exact mem_of_sq_mem K hodd (heq ▸ hc)

theorem odd_orderOf_of_isPGroup {G : Type*} [Group G] {p : ℕ} (hp : Odd p) {P : Subgroup G}
    (hP : IsPGroup p P) {x : G} (hx : x ∈ P) : Odd (orderOf x) := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := congrArg Subtype.val hk
  exact Odd.of_dvd_nat (hp.pow) (orderOf_dvd_of_pow_eq_one hk')

theorem mem_of_conj_mem_of_le {G : Type*} [Group G] [Finite G] {P : Subgroup G} {g n : G}
    (hg : ∀ x ∈ P, g * x * g⁻¹ ∈ P) (h : g * n * g⁻¹ ∈ P) : n ∈ P := by
  have hle : P.map (MulAut.conj g).toMonoidHom ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hcard : Nat.card P ≤ Nat.card (P.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq : P.map (MulAut.conj g).toMonoidHom = P := Subgroup.eq_of_le_of_card_ge hle hcard
  have hmem : g * n * g⁻¹ ∈ P.map (MulAut.conj g).toMonoidHom := by
    rw [heq]
    exact h
  obtain ⟨x, hx, hxn⟩ := Subgroup.mem_map.mp hmem
  have hxn' : g * x * g⁻¹ = g * n * g⁻¹ := hxn
  have : x = n := by simpa using hxn'
  exact this ▸ hx

theorem isPGroup_subgroupOf {G : Type*} [Group G] {p : ℕ} {P K : Subgroup G}
    (hP : IsPGroup p P) (hPK : P ≤ K) : IsPGroup p (P.subgroupOf K) :=
  hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm

theorem inf_normalizer_eq_of_odd {G : Type*} [Group G] {M K0 P : Subgroup G}
    (hK0M : K0 ≤ M) (hPK0 : P ≤ K0) (hK0odd : Odd (Nat.card K0))
    (hK0norm : ∀ g ∈ M, ∀ k ∈ K0, g * k * g⁻¹ ∈ K0)
    (hW : ∀ W : Subgroup G, Odd (Nat.card W) → P ≤ W → W ≤ M ⊓ normalizer (P : Set G) →
      (∀ g ∈ M ⊓ normalizer (P : Set G), ∀ w ∈ W, g * w * g⁻¹ ∈ W) → W = P) :
    K0 ⊓ normalizer (P : Set G) = P := by
  have hPN : P ≤ normalizer (P : Set G) := Subgroup.le_normalizer
  exact hW (K0 ⊓ normalizer (P : Set G))
    (Odd.of_dvd_nat hK0odd (Subgroup.card_dvd_of_le inf_le_left))
    (le_inf hPK0 hPN)
    (fun x hx => ⟨hK0M hx.1, hx.2⟩)
    (fun g hg w hw => ⟨hK0norm g hg.1 w hw.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hg.2 hw.2) (Subgroup.inv_mem _ hg.2)⟩)

theorem odd_normal_le_of_isolated {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {M P Z K0 : Subgroup G} (hPgrp : IsPGroup p P) (hPsyl : ¬ p ∣ P.relIndex M)
    (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hZP : Z ≤ P) (hZel : CFSG.Open.IsElemAbelian p Z)
    (hZcard : Nat.card Z = p ^ 2)
    (hC : ∀ z ∈ Z, z ≠ 1 → M ⊓ centralizer ({z} : Set G) ≤ normalizer (P : Set G))
    (hK0M : K0 ≤ M) (hPK0 : P ≤ K0) (hK0norm : ∀ g ∈ M, ∀ k ∈ K0, g * k * g⁻¹ ∈ K0)
    (hK0N : K0 ⊓ normalizer (P : Set G) = P) : K0 ≤ P := by
  have : Fact p.Prime := ⟨hp⟩
  have hpK0 : ¬ p ∣ P.relIndex K0 := fun h => by
    have e : P.relIndex K0 * K0.relIndex M = P.relIndex M := relIndex_mul_relIndex (H := P) (K := K0) (L := M) hPK0 hK0M
    exact hPsyl (h.trans (Dvd.intro _ e))
  have hQ : IsPGroup p (P.subgroupOf K0) := isPGroup_subgroupOf hPgrp hPK0
  have hab : ∀ x ∈ P.subgroupOf K0, ∀ y ∈ P.subgroupOf K0, x * y = y * x := fun x hx y hy =>
    Subtype.ext (by
      simp only [Subgroup.coe_mul]
      exact hPab _ (mem_subgroupOf.mp hx) _ (mem_subgroupOf.mp hy))
  have hN : ∀ g : K0, g ∈ normalizer ((P.subgroupOf K0 : Subgroup K0) : Set K0) →
      g ∈ P.subgroupOf K0 := by
    intro g hg
    have hgP : ∀ x ∈ P, g.1 * x * g.1⁻¹ ∈ P := by
      intro x hx
      have h1 := (mem_normalizer_iff.mp hg ⟨x, hPK0 hx⟩).mp (mem_subgroupOf.mpr hx)
      exact mem_subgroupOf.mp h1
    have hgN : g.1 ∈ normalizer (P : Set G) := by
      rw [mem_normalizer_iff]
      intro n
      exact ⟨fun hn => hgP n hn, fun hn => mem_of_conj_mem_of_le hgP hn⟩
    have hmem : g.1 ∈ K0 ⊓ normalizer (P : Set G) := ⟨g.2, hgN⟩
    rw [hK0N] at hmem
    exact mem_subgroupOf.mpr hmem
  obtain ⟨F, hFn, hFc⟩ := exists_normal_complement_of_selfNormalizing hp (P.subgroupOf K0) hQ
    hpK0 hab hN
  have hFGle : F.map K0.subtype ≤ K0 := by
    rintro _ ⟨f, _, rfl⟩
    exact f.2
  have hFGdisj : ∀ x ∈ F.map K0.subtype, x ∈ P → x = 1 := by
    intro x hx hxP
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : f ∈ F ⊓ P.subgroupOf K0 := ⟨hf, mem_subgroupOf.mpr hxP⟩
    rw [disjoint_iff.mp hFc.disjoint] at hmem
    have hf1 : f = 1 := Subgroup.mem_bot.mp hmem
    simp [hf1]
  have hFGnorm : ∀ z ∈ Z, ∀ x ∈ F.map K0.subtype, z * x * z⁻¹ ∈ F.map K0.subtype := by
    intro z hz x hx
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨(⟨z, hPK0 (hZP hz)⟩ : K0) * f * (⟨z, hPK0 (hZP hz)⟩ : K0)⁻¹,
      hFn.conj_mem f hf _, rfl⟩
  have hFGcard : Nat.card (F.map K0.subtype) = Nat.card F :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective K0)
  have hcoprime : ¬ p ∣ Nat.card (F.map K0.subtype) := by
    rw [hFGcard, ← hFc.index_eq_card]
    exact hpK0
  have hnorm : Z ≤ normalizer ((F.map K0.subtype : Subgroup G) : Set G) := by
    intro z hz
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hFGnorm z hz h hh, fun hh => ?_⟩
    have := hFGnorm z⁻¹ (Subgroup.inv_mem _ hz) _ hh
    simpa [mul_assoc] using this
  have hplane := CFSG.LargeEvenClassification.Helpers.coprime_plane_centralizers_generate hp Z
    (F.map K0.subtype) hZel hZcard hnorm hcoprime
  have hbot : (⨆ involution : {element : Z // element ≠ 1},
      (F.map K0.subtype) ⊓ centralizer {involution.val.val}) = ⊥ := by
    apply iSup_eq_bot.mpr
    rintro ⟨⟨z, hz⟩, hz1⟩
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxC⟩
    have hxK : x ∈ K0 := hFGle hxF
    have hxN : x ∈ normalizer (P : Set G) :=
      hC z hz (fun h => hz1 (Subtype.ext h)) ⟨hK0M hxK, hxC⟩
    have hxP : x ∈ P := by
      have hmem : x ∈ K0 ⊓ normalizer (P : Set G) := ⟨hxK, hxN⟩
      rw [hK0N] at hmem
      exact hmem
    exact Subgroup.mem_bot.mpr (hFGdisj x hxF hxP)
  have hFGbot : F.map K0.subtype = ⊥ := hplane.symm.trans hbot
  have hFbot : F = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    have h1 : (f : G) ∈ F.map K0.subtype := Subgroup.mem_map_of_mem K0.subtype hf
    rw [hFGbot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h1))
  have hQtop : P.subgroupOf K0 = ⊤ := by
    have h2 := hFc
    rw [hFbot] at h2
    exact isComplement'_bot_left.mp h2
  intro k hk
  have hkQ : (⟨k, hk⟩ : K0) ∈ P.subgroupOf K0 := by
    rw [hQtop]
    exact Subgroup.mem_top _
  exact mem_subgroupOf.mp hkQ

theorem le_normalizer_of_isolated {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) {M P Z : Subgroup G} (hPM : P ≤ M) (hPgrp : IsPGroup p P)
    (hPsyl : ¬ p ∣ P.relIndex M) (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hZP : Z ≤ P)
    (hZel : CFSG.Open.IsElemAbelian p Z) (hZcard : Nat.card Z = p ^ 2)
    (hC : ∀ z ∈ Z, z ≠ 1 → M ⊓ centralizer ({z} : Set G) ≤ normalizer (P : Set G))
    (hW : ∀ W : Subgroup G, Odd (Nat.card W) → P ≤ W → W ≤ M ⊓ normalizer (P : Set G) →
      (∀ g ∈ M ⊓ normalizer (P : Set G), ∀ w ∈ W, g * w * g⁻¹ ∈ W) → W = P)
    {u : G} (huM : u ∈ M) (hu1 : u ≠ 1) (hu2 : u * u = 1)
    (hinv : ∀ x ∈ P, u * x * u⁻¹ = x⁻¹)
    (hiso : ∀ g ∈ M, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) → g * u * g⁻¹ = u) :
    M ≤ normalizer (P : Set G) := by
  obtain ⟨Kc, hKn, hKodd, hKcomm⟩ := exists_odd_normal_commutators_of_isolated M huM hu1 hu2 hiso
  have hK0M : Kc.map M.subtype ≤ M := by
    rintro _ ⟨k, _, rfl⟩
    exact k.2
  have hK0odd : Odd (Nat.card (Kc.map M.subtype)) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective M)]
    exact hKodd
  have hK0norm : ∀ g ∈ M, ∀ k ∈ Kc.map M.subtype, g * k * g⁻¹ ∈ Kc.map M.subtype := by
    intro g hg k hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    exact Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : M) * k' * (⟨g, hg⟩ : M)⁻¹, hKn.conj_mem k' hk' _, rfl⟩
  have hcomm : ∀ g ∈ M, g * u * g⁻¹ * u⁻¹ ∈ Kc.map M.subtype := by
    intro g hg
    exact Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : M) * ⟨u, huM⟩ * (⟨g, hg⟩ : M)⁻¹ * (⟨u, huM⟩ : M)⁻¹,
      hKcomm ⟨g, hg⟩, rfl⟩
  have hPK0 : P ≤ Kc.map M.subtype := by
    intro x hx
    exact mem_of_commutator_mem_of_inverted _ (odd_orderOf_of_isPGroup hodd hPgrp hx)
      (hcomm x (hPM hx)) (hinv x hx)
  have hK0N := inf_normalizer_eq_of_odd hK0M hPK0 hK0odd hK0norm hW
  have hle := odd_normal_le_of_isolated hp hPgrp hPsyl hPab hZP hZel hZcard hC hK0M hPK0 hK0norm
    hK0N
  have heq : Kc.map M.subtype = P := le_antisymm hle hPK0
  intro g hg
  rw [mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have h1 := hK0norm g hg n (hPK0 hn)
    rw [heq] at h1
    exact h1
  · intro hn
    refine mem_of_conj_mem_of_le (fun x hx => ?_) hn
    have h1 := hK0norm g hg x (hPK0 hx)
    rw [heq] at h1
    exact h1

end CFSG.HardMathSupport.Malle.Proving

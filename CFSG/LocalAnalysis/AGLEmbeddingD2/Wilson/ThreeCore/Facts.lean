module

public import CFSG.Sporadic.SmallOddCore.GroupFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.AschbacherCoreTransport

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThreeCore

open Subgroup CFSG.RankThree.LocalRank CFSG.Sporadic.SmallOddCore

variable {M : Type*} [Group M]

theorem exists_conj_mem_of_card_prime [Finite M] {p : ℕ} [Fact p.Prime] {R S : Subgroup M}
    (hSR : S ≤ R) (hS : Nat.card S = p ^ (Nat.card R).factorization p) {t : M} (ht : t ∈ R)
    (htp : orderOf t = p) : ∃ x ∈ R, x⁻¹ * t * x ∈ S := by
  let S' : Sylow p R := Sylow.ofCard (S.subgroupOf R) (by
    rw [← hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hSR).toEquiv)
  have htRp : IsPGroup p (zpowers (⟨t, ht⟩ : R)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, htp, pow_one]
  obtain ⟨T, hT⟩ := htRp.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq R S' T
  refine ⟨x, x.2, ?_⟩
  have htT : (⟨t, ht⟩ : R) ∈ (T : Subgroup R) := hT (mem_zpowers _)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htT
  obtain ⟨s, hs, hst⟩ := htT
  have hsS : (s : M) ∈ S := by
    have : s ∈ S.subgroupOf R := by
      rwa [show ((S' : Subgroup R)) = S.subgroupOf R from Sylow.coe_ofCard _ _] at hs
    exact mem_subgroupOf.mp this
  have e : x⁻¹ * ⟨t, ht⟩ * x = s := by
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  rw [e']
  exact hsS

theorem aschbacherSolvableCore_eq_bot_of_witnesses (K : Subgroup M) [Finite K] (xs : List M)
    (hcover : ∀ y ∈ K, (orderOf y).Prime → orderOf y ≠ 3 → ∃ x ∈ xs, ∃ c ∈ K, y = c * x * c⁻¹)
    (hwit : ∀ x ∈ xs, ∀ N : Subgroup M, N ≤ K → (∀ c ∈ K, ∀ y ∈ N, c * y * c⁻¹ ∈ N) → x ∈ N →
      ∃ z ∈ N, 3 ∣ orderOf z) :
    aschbacherSolvableCore 3 ↥K = ⊥ := by
  set N₀ := aschbacherSolvableCore 3 ↥K
  have hN₀3 : ¬ 3 ∣ Nat.card N₀ :=
    (solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three).2.2.1
  set N := N₀.map K.subtype
  have hN3 : ¬ 3 ∣ Nat.card N := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hN₀3
  have hNK : N ≤ K := map_subtype_le _
  have hNn : ∀ c ∈ K, ∀ y ∈ N, c * y * c⁻¹ ∈ N := by
    intro c hc y hy
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    refine mem_map.mpr ⟨⟨c, hc⟩ * y' * ⟨c, hc⟩⁻¹,
      (aschbacherSolvableCore_normal 3 ↥K).conj_mem _ hy' _, ?_⟩
    simp
  by_contra hne
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card N₀) (by
    intro h1
    exact hne ((Subgroup.card_eq_one).mp h1))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N₀) q hqdvd
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact hN₀3 hqdvd
  have hyq : orderOf ((y : K) : M) = q := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  obtain ⟨x, hx, c, hc, hyc⟩ := hcover _ (y : K).2 (hyq ▸ hq) (hyq ▸ hq3)
  have hyN : ((y : K) : M) ∈ N := mem_map.mpr ⟨y, y.2, rfl⟩
  have hxN : x ∈ N := by
    have := hNn c⁻¹ (K.inv_mem hc) _ hyN
    rwa [hyc, show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this
  obtain ⟨z, hz, hz3⟩ := hwit x hx N hNK hNn hxN
  have : orderOf (⟨z, hz⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at this
  exact hN3 (hz3.trans this)

theorem aschbacherSolvableCore_inf_centralizer_conj (H : Subgroup M) [Finite M] {g : M}
    (hg : g ∈ H) {t : M} (ht : aschbacherSolvableCore 3 ↥(H ⊓ centralizer ({t} : Set M)) = ⊥) :
    aschbacherSolvableCore 3 ↥(H ⊓ centralizer ({g * t * g⁻¹} : Set M)) = ⊥ := by
  rw [inf_centralizer_conj H hg t]
  let e : ↥(H ⊓ centralizer ({t} : Set M)) ≃* ↥((H ⊓ centralizer ({t} : Set M)).map
      (MulAut.conj g).toMonoidHom) :=
    (H ⊓ centralizer ({t} : Set M)).equivMapOfInjective _ (MulAut.conj g).injective
  rw [Proving.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e, ht, Subgroup.map_bot]

theorem map_subtype_centralizer {H : Subgroup M} (b : H) :
    (centralizer ({b} : Set H)).map H.subtype = H ⊓ centralizer ({(b : M)} : Set M) := by
  ext x
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, Subgroup.coe_subtype]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, congrArg Subtype.val hc⟩
  · rintro ⟨hx, hxb⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxb, rfl⟩

theorem aschbacherSolvableCore_centralizer_subtype {H : Subgroup M} [Finite H] (b : H)
    (h : aschbacherSolvableCore 3 ↥(H ⊓ centralizer ({(b : M)} : Set M)) = ⊥) :
    aschbacherSolvableCore 3 (centralizer ({b} : Set H)) = ⊥ := by
  let e : centralizer ({b} : Set H) ≃* ↥(H ⊓ centralizer ({(b : M)} : Set M)) :=
    ((centralizer ({b} : Set H)).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_centralizer b))
  have hnat := Proving.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  rw [h] at hnat
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hnat.symm

theorem aschbacherSolvableCore_three_centralizer_eq_bot_iff {X Y : Type*} [Group X] [Group Y]
    [Finite X] (e : X ≃* Y) (b : X) :
    aschbacherSolvableCore 3 (centralizer ({b} : Set X)) = ⊥ ↔
      aschbacherSolvableCore 3 (centralizer ({e b} : Set Y)) = ⊥ := by
  let ψ : centralizer ({b} : Set X) ≃* centralizer ({e b} : Set Y) :=
    (e.subgroupMap (centralizer ({b} : Set X))).trans
      (MulEquiv.subgroupCongr (Proving.map_centralizer_singleton_eq e b))
  have hnat := Proving.aschbacherSolvableCore_map_mulEquiv Nat.prime_three ψ
  rw [hnat, Subgroup.map_eq_bot_iff_of_injective _ ψ.injective]

end CFSG.AGLEmbeddingD2.Wilson.ThreeCore

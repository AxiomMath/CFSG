module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermNZCore
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdNZPerm
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdNZGroup
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPairRep

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS AhatData

@[expose] def pairB {G : Type} [Group G] (z a : G) : Subgroup G :=
  centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G)

theorem mul_mem_centralizer_of_mem_normalizer {G : Type} [Group G] {L' : Subgroup G} {c x : G}
    (hc : c ∈ normalizer (L' : Set G)) (hx : x ∈ centralizer (L' : Set G)) :
    c * x * c⁻¹ ∈ centralizer (L' : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hc' : c⁻¹ ∈ normalizer (L' : Set G) := inv_mem hc
  have h1 : c⁻¹ * l * c ∈ L' := by
    have := (Subgroup.mem_normalizer_iff.1 hc' l).1 hl
    simpa using this
  have h2 := Subgroup.mem_centralizer_iff.1 hx _ h1
  calc l * (c * x * c⁻¹) = c * ((c⁻¹ * l * c) * x) * c⁻¹ := by group
    _ = c * (x * (c⁻¹ * l * c)) * c⁻¹ := by rw [h2]
    _ = c * x * c⁻¹ * l := by group

section Setup

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L L' : Subgroup G} {n : ℕ} {z a : G}
  (P : StdPair G L L' n z a)

include P in
theorem StdPair.B_le_normalizer : pairB z a ≤ normalizer (L : Set G) := fun _ hb =>
  P.setup.mem_normalizer_of_mem_centralizer hb.1

include P in
theorem StdPair.B_le_normalizer' : pairB z a ≤ normalizer (L' : Set G) := fun _ hb =>
  P.setup'.mem_normalizer_of_mem_centralizer hb.2

include P in
theorem StdPair.a_mem_B : a ∈ pairB z a :=
  ⟨P.a_mem_centralizer, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

include P in
theorem StdPair.mem_B_of_mem {l : G} (hl : l ∈ L) (hla : l ∈ centralizer ({a} : Set G)) :
    l ∈ pairB z a := ⟨P.le_centralizer hl, hla⟩

include P in
theorem StdPair.mem_B_of_mem_centralizer' {y : G} (hy : y ∈ centralizer (L' : Set G))
    (hyz : y ∈ centralizer ({z} : Set G)) : y ∈ pairB z a := ⟨hyz, P.centralizer'_le hy⟩

@[expose] noncomputable def StdPair.permB (M : AhatModel G n L) : ↥(pairB z a) →* Perm (Fin n) :=
  (M.permHom P.setup.hn).comp (Subgroup.inclusion P.B_le_normalizer)

theorem StdPair.permB_apply (M : AhatModel G n L) (b : ↥(pairB z a)) :
    P.permB M b = M.perm b (P.B_le_normalizer b.2) := rfl

theorem StdPair.permB_comm (M : AhatModel G n L) (b : ↥(pairB z a)) :
    P.permB M b * M.perm a P.a_mem_norm = M.perm a P.a_mem_norm * P.permB M b := by
  have hn := P.setup.hn
  rw [P.permB_apply, ← M.perm_mul hn (P.B_le_normalizer b.2) P.a_mem_norm,
    ← M.perm_mul hn P.a_mem_norm (P.B_le_normalizer b.2)]
  refine M.perm_congr ?_ _ _
  exact Subgroup.mem_centralizer_singleton_iff.1 b.2.2

@[expose] noncomputable def StdPair.thetaB (M : AhatModel G n L) :
    ↥(pairB z a) →* Perm (PairSet (M.perm a P.a_mem_norm)) :=
  pairAct (P.permB M) (P.permB_comm M)

@[expose] def pairNB (L' : Subgroup G) (z a : G) : Subgroup ↥(pairB z a) :=
  (centralizer (L' : Set G)).subgroupOf (pairB z a)

omit [Finite G] [IsSimpleGroup G] in
theorem pairNB_mem_iff (b : ↥(pairB z a)) :
    b ∈ pairNB L' z a ↔ (b : G) ∈ centralizer (L' : Set G) := Iff.rfl

include P in
theorem StdPair.normal_NB : (pairNB L' z a).Normal := ⟨fun x hx b => by
  rw [pairNB_mem_iff] at hx ⊢
  have := mul_mem_centralizer_of_mem_normalizer (P.B_le_normalizer' b.2) hx
  simpa using this⟩

end Setup

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L L' : Subgroup G} {n : ℕ} {z a : G}
  (P : StdPair G L L' n z a)

theorem transCount_pos_of_ne_one {n : ℕ} {σ : Perm (Fin n)} (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    0 < transCount σ := by
  have hs := card_support_eq_two_mul_transCount h2
  by_contra h0
  have h0' : transCount σ = 0 := by omega
  rw [h0'] at hs
  exact h1 (Equiv.Perm.card_support_eq_zero.1 (by omega))

include P in
theorem StdPair.cyclic_NB (V : Subgroup ↥(pairB z a)) (hV : V ≤ pairNB L' z a)
    (hp : IsPGroup 2 ↥V) : IsCyclic ↥V := by
  let e : ↥V ≃* ↥(V.map (pairB z a).subtype) :=
    Subgroup.equivMapOfInjective V _ (pairB z a).subtype_injective
  have hle : V.map (pairB z a).subtype ≤ centralizer (L' : Set G) := by
    rintro _ ⟨v, hv, rfl⟩
    exact hV hv
  have hc := P.setup'.cyclic _ hle (hp.of_equiv e)
  exact isCyclic_of_surjective (e.symm : ↥(V.map (pairB z a).subtype) →* ↥V) e.symm.surjective

theorem StdPair.transCount_eq_two_of_orderOf_four (M : AhatModel G n L) {y : G}
    (hy : y ∈ centralizer (L' : Set G)) (hyz : y ∈ centralizer ({z} : Set G))
    (hy4 : orderOf y = 4) : transCount (M.perm a P.a_mem_norm) = 2 := by
  classical
  have hn := P.setup.hn
  have hσ2 := P.perm_a_sq M
  have hσ1 := P.perm_a_ne_one M
  have hind := M.induces_perm hn a P.a_mem_norm
  have hyB : y ∈ pairB z a := P.mem_B_of_mem_centralizer' hy hyz
  let yB : ↥(pairB z a) := ⟨y, hyB⟩
  have hyN : yB ∈ pairNB L' z a := hy
  have hyB4 : orderOf yB = 4 := by
    rw [← hy4]
    exact Subgroup.orderOf_mk _ _
  have hy2 : y ^ 2 = a := by
    have hmem : y ^ 2 ∈ centralizer (L' : Set G) := pow_mem hy 2
    have hord : orderOf (y ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hy4]; norm_num), hy4]
    exact P.setup'.inv_unique _ hmem hord
  have hyy : yB * yB = ⟨a, P.a_mem_B⟩ := Subtype.ext (by
    show y * y = a
    rw [← pow_two]
    exact hy2)
  have := P.normal_NB
  obtain ⟨Y, hYn, hyY, hYN, hY4⟩ :=
    exists_normal_two_part_le (pairNB L' z a) (fun V hV hp => P.cyclic_NB V hV hp) hyN hyB4
  set σ := M.perm a P.a_mem_norm with hσdef
  let Θ := P.thetaB M
  have hΘa : Θ ⟨a, P.a_mem_B⟩ = 1 := pairActPerm_self _
  have hΘy2 : Θ (yB ^ 2) = 1 := by
    rw [pow_two, hyy]
    exact hΘa
  have hY := hY4 Θ hΘy2
  have hθP : Θ yB ∈ Y.map Θ := Subgroup.mem_map_of_mem Θ hyY
  have hθ2 : Θ yB * Θ yB = 1 := by
    rw [← map_mul, hyy]
    exact hΘa
  have hθ : ∀ q, Θ yB q ≠ q := by
    intro q
    refine pairActPerm_apply_ne hσ2 (P.permB_comm M yB) ?_ q
    rw [← map_mul, hyy]
    rfl
  have hnorm3 : ∀ c : Perm (PairSet σ), c.IsThreeCycle → ∀ p ∈ Y.map Θ, c * p * c⁻¹ ∈ Y.map Θ := by
    intro c hc p hp
    obtain ⟨ĉ, hĉ, hĉ3, hĉs, hĉc⟩ := exists_lift_threeCycle hσ2 hc
    have hQA : Subgroup.zpowers ĉ ≤ alternatingGroup (Fin n) :=
      Subgroup.zpowers_le.2 (Perm.mem_alternatingGroup.2 hĉs)
    have hQσ : ∀ q ∈ Subgroup.zpowers ĉ, q * σ = σ * q := by
      intro q hq
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      exact (Commute.zpow_left (show Commute ĉ σ from hĉ) k).eq
    have hS : Subgroup.closure ({ĉ} : Set (Perm (Fin n))) = Subgroup.zpowers ĉ :=
      (Subgroup.zpowers_eq_closure ĉ).symm
    have hodd : ∀ g ∈ ({ĉ} : Set (Perm (Fin n))), Odd (orderOf g) := by
      intro g hg
      rw [Set.mem_singleton_iff.1 hg]
      exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hĉ3)
    obtain ⟨x, hx, hxρ⟩ := hind.exists_mem_fixSub_of_odd_generated hQA hQσ hS hodd ĉ
      (Subgroup.mem_zpowers ĉ)
    have hhL : P.setup.emb M x ∈ L := P.setup.emb_mem M x
    have hhB : P.setup.emb M x ∈ pairB z a :=
      P.mem_B_of_mem hhL ((M.mem_fixSub_iff P.setup.pPrimeCore_eq_bot P.a_mem_norm x).1 hx)
    let hB : ↥(pairB z a) := ⟨P.setup.emb M x, hhB⟩
    have hΘh : Θ hB = c := by
      have h1 : P.permB M hB = ĉ := by
        rw [P.permB_apply]
        exact (P.setup.perm_emb M x).trans hxρ
      rw [← hĉc]
      exact pairActPerm_congr h1 (P.permB_comm M hB) hĉ
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hp
    have h2 : c * Θ w * c⁻¹ = Θ (hB * w * hB⁻¹) := by
      rw [← hΘh, map_mul, map_mul, map_inv]
    rw [h2]
    exact Subgroup.mem_map_of_mem Θ (hYn.conj_mem w hw hB)
  have hnormA : ∀ g ∈ alternatingGroup (PairSet σ), ∀ p ∈ Y.map Θ, g * p * g⁻¹ ∈ Y.map Θ := by
    have hle : Subgroup.closure {c : Perm (PairSet σ) | c.IsThreeCycle} ≤
        Subgroup.normalizer ((Y.map Θ : Subgroup (Perm (PairSet σ))) : Set (Perm (PairSet σ))) := by
      rw [Subgroup.closure_le]
      intro c hc
      rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
      intro p
      constructor
      · intro hp
        exact hnorm3 c hc p hp
      · intro hq
        have := hnorm3 c⁻¹ hc.inv _ hq
        simpa [mul_assoc] using this
    intro g hg p hp
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating] at hg
    exact ((Subgroup.mem_normalizer_iff.1 (hle hg) p).1 hp)
  have hQ : 0 < Fintype.card (PairSet σ) := by
    rw [card_pairSet hσ2]
    exact transCount_pos_of_ne_one hσ2 hσ1
  have h2 := card_eq_two_of_normalized_involution hQ (Y.map Θ) hθP hθ2 hθ hnormA hY
  rw [card_pairSet hσ2] at h2
  exact h2

end Main

end CFSG.OddStandard.Solomon75

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292NConj
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292N

open CFSG.Open Subgroup Matrix
open CFSG.RankThree.PartTwo.Sec4 hiding diagHom coe_diagHom diagHom_injective
open CFSG.SectionRank.OddCover
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankThreeUC.S15.ACore
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292
open scoped Pointwise

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem mem_normalizer_conjTorus {n : ℕ} {P x : GL (Fin 3) K} :
    x ∈ normalizer (conjTorus n P : Set (GL (Fin 3) K)) ↔
      P⁻¹ * x * P ∈ normalizer (torus3 (rootsOfUnity n K) : Set (GL (Fin 3) K)) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h t
    have h1 := h (P * t * P⁻¹)
    rw [mem_conjTorus, mem_conjTorus] at h1
    have e1 : P⁻¹ * (P * t * P⁻¹) * P = t := by group
    have e2 : P⁻¹ * (x * (P * t * P⁻¹) * x⁻¹) * P = P⁻¹ * x * P * t * (P⁻¹ * x * P)⁻¹ := by
      group
    rwa [e1, e2] at h1
  · intro h k
    have h1 := h (P⁻¹ * k * P)
    rw [mem_conjTorus, mem_conjTorus]
    have e2 : P⁻¹ * x * P * (P⁻¹ * k * P) * (P⁻¹ * x * P)⁻¹ = P⁻¹ * (x * k * x⁻¹) * P := by
      group
    rwa [e2] at h1

theorem conj_mem_normalizer_map {G : Type*} [Group G] {C : Subgroup G} {x : G}
    (hx : x ∈ normalizer (C : Set G)) (a : G) :
    a * x * a⁻¹ ∈ normalizer ((C.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) := by
  have key : ∀ k, k ∈ C.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * k * a ∈ C := by
    intro k
    constructor
    · rintro ⟨c, hc, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hc
    · intro hk
      exact ⟨a⁻¹ * k * a, hk, by simp [MulAut.conj_apply, mul_assoc]⟩
  rw [mem_normalizer_iff] at hx ⊢
  intro h
  rw [key, key]
  have e : a⁻¹ * (a * x * a⁻¹ * h * (a * x * a⁻¹)⁻¹) * a = x * (a⁻¹ * h * a) * x⁻¹ := by group
  rw [e]
  exact hx _

theorem monEmb_conj_mem_torus3 {C : Type} [CommGroup C] (e : C →* Kˣ) (M : Subgroup Kˣ)
    (x : Mon C 3) {t : GL (Fin 3) K} (ht : t ∈ torus3 M) :
    monEmb e 3 x * t * (monEmb e 3 x)⁻¹ ∈ torus3 M := by
  obtain ⟨d, hdM, hd, rfl⟩ := (mem_torus3 M).1 ht
  have hmem : diagHom 3 (d ∘ x.right.symm) ∈ torus3 M := by
    refine (mem_torus3 M).2 ⟨_, fun i => hdM _, ?_, rfl⟩
    have h := Equiv.prod_comp x.right.symm d
    rw [Fin.prod_univ_three, Fin.prod_univ_three] at h
    simpa [Function.comp] using h.trans hd
  rw [monEmb_apply]
  have h1 : diagHom 3 (fun i => e (x.left i)) * monPermGL 3 x.right * diagHom 3 d *
      (diagHom 3 (fun i => e (x.left i)) * monPermGL 3 x.right)⁻¹ =
      diagHom 3 (fun i => e (x.left i)) *
        (monPermGL 3 x.right * diagHom 3 d * (monPermGL 3 x.right)⁻¹) *
          (diagHom 3 (fun i => e (x.left i)))⁻¹ := by
    group
  rw [h1, monPermGL_conj_diagHom, diagHom_mul_comm_of_mem_torus3 _ hmem, mul_inv_cancel_right]
  exact hmem

theorem monEmb_mem_normalizer_torus3 {C : Type} [CommGroup C] (e : C →* Kˣ) (M : Subgroup Kˣ)
    (x : Mon C 3) : monEmb e 3 x ∈ normalizer (torus3 M : Set (GL (Fin 3) K)) := by
  rw [mem_normalizer_iff]
  intro t
  refine ⟨monEmb_conj_mem_torus3 e M x, fun ht => ?_⟩
  have h := monEmb_conj_mem_torus3 e M x⁻¹ ht
  have e1 : monEmb e 3 x⁻¹ * (monEmb e 3 x * t * (monEmb e 3 x)⁻¹) * (monEmb e 3 x⁻¹)⁻¹ = t := by
    rw [map_inv]
    group
  rwa [e1] at h

theorem exists_glPi_conj_monomial (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {Q : Subgroup (GL (Fin 3) K)} (hQL : Q ≤ slPi π 3 (p ^ f) K) (hQ : IsPGroup 3 Q) :
    ∃ g ∈ glPi π 3 (p ^ f) K, ∀ x ∈ Q,
      g * x * g⁻¹ ∈ (monEmb (unitsPPart K 3).subtype 3).range := by
  have := hK.finite
  have := Fintype.ofFinite K
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  cases π
  · have hU := hK.unitary
    have hF : Fintype.card K = (p ^ f) ^ 2 := by
      rw [← Nat.card_eq_fintype_card, hU.card_eq_sq]
    have hrq : 3 ∣ p ^ f + 1 := by
      change p ^ f % 3 = 2 at hq
      omega
    exact exists_conj_monomial_GU (by norm_num) hF hrq (by norm_num) Q
      (hQL.trans (slPi_le_glPi hπ)) hQ
  · have hrF : 3 ∣ Fintype.card K - 1 := by
      rw [← Nat.card_eq_fintype_card, hK.card]
      change p ^ f % 3 = 1 at hq
      change 3 ∣ p ^ f - 1
      omega
    obtain ⟨g, hg⟩ := exists_conj_monomial_GL (by norm_num) hrF (by norm_num) Q hQ
    exact ⟨g, mem_glPi_true _ _, hg⟩

theorem not_three_dvd_relIndex_normalizer (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hT : IsTypeThree π (p ^ f) K y) {v : Fin 3 → K} (hv : v ≠ 0)
    (horth : π = false → YFrameOrth (p ^ f) y v) :
    ¬ 3 ∣ (normalizer (threeFrame y v : Set (GL (Fin 3) K))).relIndex (slPi π 3 (p ^ f) K) := by
  have := hK.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥(slPi π 3 (p ^ f) K)))
  set Q : Subgroup (GL (Fin 3) K) :=
    (S : Subgroup ↥(slPi π 3 (p ^ f) K)).map (slPi π 3 (p ^ f) K).subtype
  have hQp : IsPGroup 3 Q := S.isPGroup'.map _
  have hQL : Q ≤ slPi π 3 (p ^ f) K := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  obtain ⟨g, hg, hgQ⟩ := exists_glPi_conj_monomial hK hq hQL hQp
  have hQN : ∀ x ∈ Q, x ∈ normalizer (conjTorus 3 g⁻¹ : Set (GL (Fin 3) K)) := by
    intro x hx
    obtain ⟨m, hm⟩ := hgQ x hx
    rw [mem_normalizer_conjTorus, inv_inv, ← hm]
    exact monEmb_mem_normalizer_torus3 _ _ m
  obtain ⟨P, hP, hPn⟩ := exists_glPi_frame hK hq hT hv horth
  obtain ⟨a, ha, hmap⟩ := exists_slPi_map_conjTorus hK (inv_mem hg) hP
  have h3 : threeFrame y v = conjTorus 3 P := hPn 3 (by norm_num)
  set a' : ↥(slPi π 3 (p ^ f) K) := ⟨a, ha⟩
  have hS' : ((a' • S : Sylow 3 ↥(slPi π 3 (p ^ f) K)) : Subgroup ↥(slPi π 3 (p ^ f) K)) ≤
      (normalizer (threeFrame y v : Set (GL (Fin 3) K))).subgroupOf (slPi π 3 (p ^ f) K) := by
    intro s hs
    rw [Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    rw [mem_subgroupOf]
    have e : ((MulAut.conj a' • s₀ : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
        a * (s₀ : GL (Fin 3) K) * a⁻¹ := rfl
    rw [e, h3, ← hmap]
    exact conj_mem_normalizer_map (hQN _ ⟨s₀, hs₀, rfl⟩) a
  intro h
  exact (a' • S).not_dvd_index (dvd_trans h (Subgroup.index_dvd_of_le hS'))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292N

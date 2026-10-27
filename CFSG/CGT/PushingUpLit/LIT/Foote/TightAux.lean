module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Blocks
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem QBlock.conj {K : Subgroup G} (h : QBlock K) (g : G) : QBlock (rightConjugate K g) := by
  let e : ↥K ≃* ↥(rightConjugate K g) := (MulAut.conj g⁻¹).subgroupMap K
  refine ⟨isShortGroup_of_mulEquiv e h.short, ?_⟩
  refine LocalCores.isQuasisimple_of_surjective h.quasisimple (quotTopEquiv e).toMonoidHom
    (quotTopEquiv e).surjective ?_
  rw [(MonoidHom.ker_eq_bot_iff _).2 (quotTopEquiv e).injective]
  exact bot_le

omit [Finite G] in
theorem mem_normalizer_rightConjugate {B : Subgroup G} {g x : G} :
    x ∈ Subgroup.normalizer ((rightConjugate B g : Subgroup G) : Set G) ↔
      g * x * g⁻¹ ∈ Subgroup.normalizer (B : Set G) := by
  simp only [Subgroup.mem_normalizer_iff, mem_rightConjugate_iff]
  constructor
  · intro h k
    have e1 : g * (g⁻¹ * k * g) * g⁻¹ = k := by group
    have e2 : g * (x * (g⁻¹ * k * g) * x⁻¹) * g⁻¹ = g * x * g⁻¹ * k * (g * x * g⁻¹)⁻¹ := by
      group
    have := h (g⁻¹ * k * g)
    rwa [e1, e2] at this
  · intro h y
    have e2 : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * y * x⁻¹) * g⁻¹ := by
      group
    have := h (g * y * g⁻¹)
    rwa [e2] at this

omit [Finite G] in
theorem tightlyEmbedded_conj {B : Subgroup G} (h : TightlyEmbedded B) (g : G) :
    TightlyEmbedded (rightConjugate B g) :=
  StandardSubgroupAPI.tightlyEmbedded_rightConjugate h g

omit [Finite G] in
theorem tightlyEmbedded_inf_subgroupOf {B H : Subgroup G} (hB : TightlyEmbedded B)
    (heven : Even (Nat.card ↥(B ⊓ H))) : TightlyEmbedded ((B ⊓ H).subgroupOf H) :=
  StandardSubgroupAPI.tightlyEmbedded_inf_subgroupOf hB heven

theorem mem_normalizer_of_commute {B T : Subgroup G} (hB : TightlyEmbedded B) (hT : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) (hTB : T ≤ B) {q : G} (hq : ∀ t ∈ T, q * t = t * q) :
    q ∈ Subgroup.normalizer (B : Set G) :=
  centralizer_two_subgroup_le B T hB hT hTB hT1
    (Subgroup.mem_centralizer_iff.mpr fun t ht => (hq t ht).symm)

theorem card_le_of_isSylowOf {P Q K : Subgroup G} (hP : IsSylowOf 2 P K) (hQK : Q ≤ K)
    (hQ : IsPGroup 2 Q) : Nat.card Q ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : 2 ^ k ∣ Nat.card K := hk ▸ Subgroup.card_dvd_of_le hQK
  have hle : k ≤ (Nat.card K).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  rw [hP.card_eq, hk]
  exact Nat.pow_le_pow_right (by norm_num) hle

theorem eq_of_isSylowOf_le {K N T : Subgroup G} (hperf : ⁅K, K⁆ = K) (hNK : N ≤ K)
    (hN : ∀ g ∈ K, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hT : IsSylowOf 2 T K) (hTN : T ≤ N) : N = K := by
  classical
  have hnormM : (N.subgroupOf K).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hN g g.2 n hn⟩
  set M := N.subgroupOf K with hM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hperf
  obtain ⟨B, hB⟩ := hT
  have hBM : (B : Subgroup ↥K) ≤ M := by
    intro b hb
    have hbT : (b : G) ∈ T := hB ▸ ⟨b, hb, rfl⟩
    exact hTN hbT
  have hBcard : Nat.card B = 2 ^ (Nat.card ↥K).factorization 2 := Sylow.card_eq_multiplicity B
  have hdvd : 2 ^ (Nat.card ↥K).factorization 2 ∣ Nat.card M := by
    rw [← hBcard]
    exact Subgroup.card_dvd_of_le hBM
  have hodd : Odd M.index := by
    rw [Nat.odd_iff]
    by_contra hne
    have h2i : 2 ∣ M.index := by omega
    have hK0 : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
    apply Nat.pow_succ_factorization_not_dvd hK0 Nat.prime_two
    have h3 : 2 ^ ((Nat.card ↥K).factorization 2 + 1) ∣ Nat.card M * M.index := by
      rw [pow_succ]
      exact Nat.mul_dvd_mul hdvd h2i
    rwa [Subgroup.card_mul_index] at h3
  have hQodd : Odd (Nat.card (↥K ⧸ M)) := hodd
  by_contra hne
  have hMtop : M ≠ ⊤ := by
    intro h
    apply hne
    refine le_antisymm hNK fun x hx => ?_
    have : (⟨x, hx⟩ : ↥K) ∈ M := by rw [h]; trivial
    exact this
  have : Nontrivial (↥K ⧸ M) := by
    have h1 : M.index ≠ 1 := fun h => hMtop (Subgroup.index_eq_one.1 h)
    have h2 : 1 < Nat.card (↥K ⧸ M) := by
      have := Nat.card_pos (α := ↥K ⧸ M)
      have h3 : Nat.card (↥K ⧸ M) = M.index := rfl
      omega
    exact Finite.one_lt_card_iff_nontrivial.1 h2
  exact Group.IsPerfect.not_isSolvable (↥K ⧸ M) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQodd)

omit [Finite G] in
theorem conj_mem_inf_centralizer {A N : Subgroup G} (hAN : A ≤ Subgroup.normalizer (N : Set G)) :
    ∀ g ∈ A, ∀ n ∈ A ⊓ Subgroup.centralizer (N : Set G),
      g * n * g⁻¹ ∈ A ⊓ Subgroup.centralizer (N : Set G) := by
  rintro g hg n ⟨hnA, hnC⟩
  refine ⟨A.mul_mem (A.mul_mem hg hnA) (A.inv_mem hg), ?_⟩
  change n ∈ Subgroup.centralizer (N : Set G) at hnC
  show g * n * g⁻¹ ∈ Subgroup.centralizer (N : Set G)
  rw [Subgroup.mem_centralizer_iff] at hnC ⊢
  intro b hb
  have hb' : g⁻¹ * b * g⁻¹⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.1 (hAN (A.inv_mem hg)) b).1 hb
  have hcomm := hnC _ hb'
  calc b * (g * n * g⁻¹) = g * ((g⁻¹ * b * g⁻¹⁻¹) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * b * g⁻¹⁻¹)) * g⁻¹ := by rw [hcomm]
    _ = g * n * g⁻¹ * b := by group

theorem commutator_eq_bot_of_sylow {A B T : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hT : IsSylowOf 2 T A) (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hTB : ⁅T, B⁆ = ⊥) :
    ⁅A, B⁆ = ⊥ := by
  have hTC : T ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hTB
  have heq := eq_of_isSylowOf_le hA (inf_le_left : A ⊓ Subgroup.centralizer (B : Set G) ≤ A)
    (conj_mem_inf_centralizer hAB) hT (le_inf hT.le hTC)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (heq ▸ inf_le_right)

omit [Finite G] in
theorem exists_mul_of_mem_sup {W N : Subgroup G} (hWN : W ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ W ⊔ N) : ∃ w ∈ W, ∃ n ∈ N, w * n = x := by
  have hle : W ⊔ N ≤ Subgroup.normalizer (N : Set G) := sup_le hWN Subgroup.le_normalizer
  have hNn : (N.subgroupOf (W ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hle
  have hx' : (⟨x, hx⟩ : ↥(W ⊔ N)) ∈ W.subgroupOf (W ⊔ N) ⊔ N.subgroupOf (W ⊔ N) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨w, hw, n, hn, hwn⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  exact ⟨w, hw, n, hn, congrArg Subtype.val hwn⟩

omit [Finite G] in
theorem even_card_of_isPGroup {T K : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hTK : T ≤ K) :
    Even (Nat.card K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card T := by
    rcases hT.card_eq_or_dvd with h | h
    · exact absurd ((Subgroup.eq_bot_iff_card T).2 h) hT1
    · exact h
  exact even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le hTK))

theorem ne_bot_of_isSylowOf_even {T K : Subgroup G} (hT : IsSylowOf 2 T K)
    (hK : Even (Nat.card K)) : T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  obtain ⟨-, -, hdvd⟩ := isSylowOf_iff.1 hT
  apply hdvd
  rw [hbot, Subgroup.relIndex_bot_left]
  exact even_iff_two_dvd.1 hK

end CFSG.CGT.PushingUpLit.LIT.Foote

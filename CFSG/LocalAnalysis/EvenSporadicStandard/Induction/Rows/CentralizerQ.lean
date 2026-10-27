module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

theorem vPairs_nonempty_of_centralizer_of_mem {L K : Subgroup H} {u : H} (hu2 : orderOf u = 2)
    (huL : u ∈ L) (hKL : K ≤ L) (hKeq : K = L ⊓ centralizer ({u} : Set H))
    (hZK : ∀ z ∈ (center K).map K.subtype, z * z = 1 → z = 1 ∨ z = u)
    (hlt : twoAdic K < twoAdic L) : (vPairs L K u).Nonempty := by
  have huu : u * u = 1 := by
    have : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    rwa [pow_two] at this
  have huK : u ∈ K := by
    rw [hKeq]
    exact ⟨huL, mem_centralizer_singleton_iff.2 rfl⟩
  let u' : ↥K := ⟨u, huK⟩
  have hu'2 : u' * u' = 1 := Subtype.ext huu
  obtain ⟨P, hP⟩ := (isPGroup_two_zpowers hu'2).exists_le_sylow
  have huP : u' ∈ (P : Subgroup ↥K) := hP (mem_zpowers u')
  set S : Subgroup H := (P : Subgroup ↥K).map K.subtype with hS
  have hSK : S ≤ K := Subgroup.map_subtype_le _
  have hSL : S ≤ L ⊓ centralizer ({u} : Set H) := hKeq ▸ hSK
  have hSp : IsPGroup 2 S := P.isPGroup'.map K.subtype
  have hScard : Nat.card S = 2 ^ twoAdic K := by
    rw [hS, Subgroup.card_map_of_injective K.subtype_injective, P.card_eq_multiplicity]
    rfl
  have hlt' : Nat.card S < 2 ^ (Nat.card L).factorization 2 := by
    rw [hScard]
    exact Nat.pow_lt_pow_right (by norm_num) hlt
  obtain ⟨T, hTL, hTp, hST⟩ := exists_lt_of_card_lt (hSK.trans hKL) hSp hlt'
  refine vPairs_nonempty_of_sylow (L := L) (K := K) (S := S) (T := T) hu2 ⟨u', huP, rfl⟩ hSL ?_
    hTL hTp hST (fun z hz _ => (le_sup_left : K ≤ K ⊔ zpowers u) (hSK hz)) hZK ?_
  · intro S' hS'le hS'p hSS'
    have hS'K : S' ≤ K := hKeq ▸ hS'le
    have hS'' : IsPGroup 2 (S'.subgroupOf K) := hS'p.comap_subtype
    have hPle : (P : Subgroup ↥K) ≤ S'.subgroupOf K := fun x hx =>
      mem_subgroupOf.2 (hSS' ⟨x, hx, rfl⟩)
    have hPeq : S'.subgroupOf K = (P : Subgroup ↥K) := P.is_maximal' hS'' hPle
    rw [← Subgroup.map_subgroupOf_eq_of_le hS'K, hPeq]
  · rw [inf_eq_left.2 hSK]
    unfold twoAdic
    rw [hScard, Nat.Prime.factorization_pow Nat.prime_two]
    simp [twoAdic]

theorem sol78Local39Q_of_centralizer_allInner {N L K : Subgroup H} {t u : H}
    (hset : SolomonSettingQ H N L K t u) (huL : u ∈ L)
    (hKeq : K = L ⊓ centralizer ({u} : Set H))
    (hZK : ∀ z ∈ (center K).map K.subtype, z * z = 1 → z = 1 ∨ z = u)
    (hlt : twoAdic K < twoAdic L)
    (hmax : ∀ M : Subgroup H, K ≤ M → M ≤ L → M = K ∨ M = L)
    (hinn : ∀ α : MulAut ↥K, ∃ c ∈ K, ∀ k : K, ((α k : K) : H) = c * (k : H) * c⁻¹) :
    (vPairs L K u).Nonempty ∧ Sol78Fusion39 L K u ∧ Sol78Generate L K u := by
  have hKu : ∀ k ∈ K, k * u = u * k := fun k hk =>
    mem_centralizer_iff.1 hset.u_mem_centralizer_K k hk
  refine ⟨vPairs_nonempty_of_centralizer_of_mem hset.u_order huL hset.K_le hKeq hZK hlt, ?_,
    sol78Generate_of_maximal hset.K_le hset.u_mem_centralizer_K hset.u_order hZK hmax⟩
  refine sol78Fusion39_of_induced hKu ?_
    (inducedByCentralizer_of_allInner hset.K_le hKu hinn)
  intro g hg
  obtain ⟨-, hKg⟩ := map_conj_eq_of_hyp35 hset.hyp35 hg
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => conj_mem_of_map_eq hKg hh, fun hh => ?_⟩
  have := conj_inv_mem_of_map_eq hKg hh
  simpa [mul_assoc] using this

end CFSG.EvenSporadicStandard.Induction

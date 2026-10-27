module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H

open CFSG.Open Subgroup

variable {G : Type*} [Group G]

theorem pCoreOf_le (p : ℕ) (H : Subgroup G) : pCoreOf p H ≤ H :=
  map_subtype_le _

theorem isPGroup_pCoreOf (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreOf p H) :=
  (CFSG.pCore_isPGroup (p := p) (G := H)).map H.subtype

theorem le_normalizer_map_subtype {M : Subgroup G} (C : Subgroup M) [C.Normal] :
    M ≤ normalizer (C.map M.subtype : Set G) := by
  have h : (C.map M.subtype).subgroupOf M = C :=
    comap_map_eq_self_of_injective M.subtype_injective C
  have hn : ((C.map M.subtype).subgroupOf M).Normal := by
    rw [h]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).1 hn

theorem le_normalizer_pCoreOf (p : ℕ) (H : Subgroup G) :
    H ≤ normalizer (pCoreOf p H : Set G) :=
  le_normalizer_map_subtype (CFSG.pCore p H)

theorem coprime_three_of_isPGroup_two {A : Type*} [Group A] [Finite A] (h : IsPGroup 2 A) :
    Nat.Coprime 3 (Nat.card A) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

theorem card_sup_dvd_of_le_normalizer [Finite G] {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) ∣ Nat.card A * Nat.card B := by
  have hAJ : A ≤ A ⊔ B := le_sup_left
  have hBJ : B ≤ A ⊔ B := le_sup_right
  have hJN : A ⊔ B ≤ normalizer (A : Set G) := sup_le le_normalizer hB
  haveI : (A.subgroupOf (A ⊔ B)).Normal := (normal_subgroupOf_iff_le_normalizer hAJ).2 hJN
  have htop : B.subgroupOf (A ⊔ B) ⊔ A.subgroupOf (A ⊔ B) = ⊤ := by
    rw [sup_comm (B.subgroupOf (A ⊔ B)), ← subgroupOf_sup hAJ hBJ, subgroupOf_self]
  have h1 := relIndex_sup_right (H := B.subgroupOf (A ⊔ B)) (K := A.subgroupOf (A ⊔ B))
  rw [htop, relIndex_top_right] at h1
  have h2 := card_mul_index (A.subgroupOf (A ⊔ B))
  have hcA : Nat.card (A.subgroupOf (A ⊔ B)) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv
  have hcB : Nat.card (B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hBJ).toEquiv
  have hdvd := relIndex_dvd_card (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B))
  rw [← h2, hcA, h1]
  exact Nat.mul_dvd_mul_left _ (hcB ▸ hdvd)

theorem isCyclic_of_pRank_le_one [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup p P) (hrk : CFSG.Open.pRank p P ≤ 1) : IsCyclic P := by
  by_contra hnc
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hel : IsElemAbelian p S :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p S).1 hSel
  have hel' : IsElemAbelian p (S.map P.subtype) := CFSG.SectionRank.isElemAbelian_map hel _
  have hcard : Nat.card (S.map P.subtype) = p ^ 2 := by
    rw [card_map_of_injective P.subtype_injective, hScard]
  have := CFSG.SectionRank.le_pRank hp.one_lt (map_subtype_le S) hel' hcard
  omega

theorem eq_one_of_mem_center_of_perfect {E : Type*} [Group E] [Finite E] {p : ℕ}
    [Fact p.Prime] (hperf : commutator E = ⊤) (S : Sylow p E) (hS : IsMulCommutative S)
    {z : E} (hz : z ∈ center E) (hzS : z ∈ (S : Subgroup E)) : z = 1 := by
  let : CommGroup S := IsMulCommutative.instCommGroup
  let tr : E →* S := MonoidHom.transfer (MonoidHom.id S)
  have htriv : tr z = 1 := by
    have hzc : z ∈ commutator E := by
      rw [hperf]
      trivial
    exact Abelianization.commutator_subset_ker tr hzc
  have hkey : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ (S : Subgroup E) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have h := Subgroup.mem_center_iff.mp ((center E).pow_mem hz k) g₀
    rw [mul_assoc, ← h]
    group
  have hpow : z ^ (S : Subgroup E).index = 1 := by
    have h := htriv
    rw [show tr z = _ from MonoidHom.transfer_eq_pow (MonoidHom.id S) z hkey] at h
    exact congrArg Subtype.val h
  obtain ⟨n, hn⟩ := S.isPGroup' ⟨z, hzS⟩
  have h1 : orderOf z ∣ (S : Subgroup E).index := orderOf_dvd_of_pow_eq_one hpow
  have h2 : orderOf z ∣ p ^ n :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
  have hcop : Nat.Coprime (p ^ n) (S : Subgroup E).index :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr S.not_dvd_index)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)

theorem mem_normalizer_closure {s : Set G} {g : G} (h1 : ∀ y ∈ s, g * y * g⁻¹ ∈ s)
    (h2 : ∀ y ∈ s, g⁻¹ * y * g ∈ s) : g ∈ normalizer (closure s : Set G) := by
  have key : ∀ c : G, (∀ y ∈ s, c * y * c⁻¹ ∈ s) → ∀ y ∈ closure s, c * y * c⁻¹ ∈ closure s := by
    intro c hc y hy
    have hle : closure s ≤ (closure s).comap (MulAut.conj c).toMonoidHom := by
      rw [closure_le]
      intro t ht
      exact subset_closure (hc t ht)
    simpa using hle hy
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g h1 y, fun hy => ?_⟩
  have h := key g⁻¹ (by simpa using h2) _ hy
  simpa [mul_assoc] using h

theorem exists_mul_pow_eq {O : Subgroup G} {t o : G} (ht : t ∈ normalizer (O : Set G))
    (ho : o ∈ O) (m : ℕ) : ∃ o' ∈ O, (t * o) ^ m = t ^ m * o' := by
  induction m with
  | zero => exact ⟨1, O.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨o', ho', h⟩ := ih
    refine ⟨t⁻¹ * o' * t * o, O.mul_mem ((mem_normalizer_iff''.mp ht o').mp ho') ho, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem exists_orderOf_eq_two_pow {O : Subgroup G} (hO : IsPGroup 2 O) {g : G} {n : ℕ}
    (hg : g ^ 2 ^ n ∈ O) : ∃ k : ℕ, orderOf g = 2 ^ k := by
  obtain ⟨m, hm⟩ := hO ⟨g ^ 2 ^ n, hg⟩
  have h1 : g ^ 2 ^ (n + m) = 1 := by
    rw [pow_add, pow_mul]
    exact congrArg Subtype.val hm
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨k, hk⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H

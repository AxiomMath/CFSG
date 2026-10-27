module

public import CFSG.Goldschmidt75.TheoremBa
public import CFSG.Goldschmidt75.Local
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.Goldschmidt75.TheoremBcBasic

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem mem_rcSet_subgroupOf (P : Sylow p G) {S M : Subgroup G}
    (hCM : centralizer (S : Set G) ≤ M)
    (h : Nat.card ↥((P : Subgroup G) ⊓ M) = p ^ (Nat.card M).factorization p)
    {y : G} (hy : y ∈ rcSet S P) :
    (⟨y, hCM (rcSet_le_centralizer S P hy)⟩ : M) ∈
      rcSet ((S ⊓ M).subgroupOf M) (sylowOfInf P M h) := by
  refine ⟨?_, mem_sylowOfInf.2 (rcSet_le S P hy)⟩
  have h1 := mem_commutator_subgroupOf hCM hy.1 (hCM (rcSet_le_centralizer S P hy))
  have h2 : (centralizer (S : Set G)).subgroupOf M ≤
      centralizer (((S ⊓ M).subgroupOf M : Subgroup M) : Set M) := fun z hz =>
    (mem_centralizer_subgroupOf_iff (inf_le_right : S ⊓ M ≤ M)).2
      (Subgroup.centralizer_le (fun w hw => hw.1) hz)
  exact Subgroup.commutator_mono h2 h2 h1

theorem mem_rcSet_of_subgroupOf (P : Sylow p G) {S M : Subgroup G} (hSM : S ≤ M)
    (h : Nat.card ↥((P : Subgroup G) ⊓ M) = p ^ (Nat.card M).factorization p) {z : M}
    (hz : z ∈ rcSet ((S ⊓ M).subgroupOf M) (sylowOfInf P M h)) :
    (z : G) ∈ rcSet S P := by
  refine ⟨?_, mem_sylowOfInf.1 hz.2⟩
  have h2 := map_commutator_centralizer_le (inf_le_right : S ⊓ M ≤ M) ⟨z, hz.1, rfl⟩
  rwa [inf_eq_left.mpr hSM] at h2

omit [Fact p.Prime] in
theorem normalizer_inf_le (P : Sylow p G) {S K : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) :
    normalizer (((P : Subgroup G) ⊓ K : Subgroup G) : Set G) ≤
      normalizer ((S ⊓ K : Subgroup G) : Set G) := by
  have h := normalizer_le_normalizer_inf P hS (inf_le_left : (P : Subgroup G) ⊓ K ≤ P)
  have e : S ⊓ ((P : Subgroup G) ⊓ K) = S ⊓ K := by
    rw [← inf_assoc, inf_eq_left.mpr hSP]
  rwa [e] at h

theorem rcSet_stronglyClosed_of_normalizer (P : Sylow p G) {S S₀ : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) (hS₀S : S₀ ≤ S) [S₀.Normal]
    (hA : ∀ x ∈ rcSet S P, ∀ k ∈ S ⊔ centralizer (S₀ : Set G), k⁻¹ * x * k ∈ P →
      k⁻¹ * x * k ∈ rcSet S P)
    (hM : RcFor p (normalizer ((S ⊓ centralizer (S₀ : Set G) : Subgroup G) : Set G))) :
    fusionStronglyClosed ((rcSet S P : Subgroup G) : Set G) P := by
  set K := centralizer (S₀ : Set G)
  set M := normalizer ((S ⊓ K : Subgroup G) : Set G)
  have hKn : K.Normal := inferInstance
  have hPM : (P : Subgroup G) ≤ M := fun q hq => mem_normalizer_inf
    (sylow_le_normalizer P hSP hS hq)
    (by rw [normalizer_eq_top_iff.mpr hKn]; exact mem_top q)
  have hSM : S ≤ M := hSP.trans hPM
  have hCK : centralizer (S : Set G) ≤ K := Subgroup.centralizer_le hS₀S
  have hCM : centralizer (S : Set G) ≤ M := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le (fun w hw => hw.1) hc)
  have hcard := card_inf_of_le P hPM
  have hRM := hM (sylowOfInf P M hcard) ((S ⊓ M).subgroupOf M)
    (inf_subgroupOf_le_sylowOfInf P hSP M hcard) (stronglyClosed_inf_subgroupOf P hS M hcard)
  obtain ⟨QK, hQK⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  have hfr := Sylow.normalizer_sup_eq_top QK
  have hQKG : ((QK : Subgroup K).map K.subtype) = (P : Subgroup G) ⊓ K := by
    rw [hQK, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  rw [hQKG, sup_comm] at hfr
  intro x hx g hxg
  obtain ⟨k, hk, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hfr ▸ mem_top g)
  have hxK : x ∈ K := hCK (rcSet_le_centralizer S P hx)
  have hxgK : (k * n)⁻¹ * x * (k * n) ∈ (P : Subgroup G) ⊓ K := by
    refine ⟨hxg, ?_⟩
    have := hKn.conj_mem x hxK (k * n)⁻¹
    rwa [inv_inv] at this
  have hxkP : k⁻¹ * x * k ∈ (P : Subgroup G) := by
    have := (mem_normalizer_iff.mp hn _).mp hxgK
    have e : n * ((k * n)⁻¹ * x * (k * n)) * n⁻¹ = k⁻¹ * x * k := by group
    rw [e] at this
    exact this.1
  have hxk := hA x hx k ((le_sup_right : K ≤ S ⊔ K) hk) hxkP
  have hnM : n ∈ M := normalizer_inf_le P hSP hS hn
  have hy := mem_rcSet_subgroupOf P hCM hcard hxk
  have hnconj : (⟨n, hnM⟩ : M)⁻¹ * ⟨k⁻¹ * x * k, hCM (rcSet_le_centralizer S P hxk)⟩ *
      ⟨n, hnM⟩ ∈ (sylowOfInf P M hcard : Subgroup M) :=
    mem_sylowOfInf.2 (by simpa [mul_assoc] using hxg)
  have h1 := mem_rcSet_of_subgroupOf P hSM hcard (hRM _ hy _ hnconj)
  simpa [mul_assoc] using h1

end CFSG.Goldschmidt75

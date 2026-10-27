module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitQuot0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitPGrp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitSylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X] {Z A : Subgroup X} [Z.Normal]
variable {G : Type*} [Group G] {π : X →* G}

private lemma relIndex_sup_eq_relIndex_inf {P K : Subgroup X} [P.Normal] :
    K.relIndex (K ⊔ P) = (P ⊓ K).relIndex P := by
  have h1 : K.relIndex (K ⊔ P) * Nat.card K = Nat.card (K ⊔ P : Subgroup X) := by
    have := Subgroup.relIndex_mul_card (H := K) (K := K ⊔ P)
    rwa [inf_eq_left.mpr le_sup_left] at this
  have h2 : P.relIndex (K ⊔ P) * Nat.card P = Nat.card (K ⊔ P : Subgroup X) := by
    have := Subgroup.relIndex_mul_card (H := P) (K := K ⊔ P)
    rwa [inf_eq_left.mpr le_sup_right] at this
  have h3 : P.relIndex (K ⊔ P) = P.relIndex K := Subgroup.relIndex_sup_right K P
  have h4 : P.relIndex K * Nat.card (P ⊓ K : Subgroup X) = Nat.card K :=
    Subgroup.relIndex_mul_card (H := P) (K := K)
  have h5 : (P ⊓ K).relIndex P * Nat.card (P ⊓ K : Subgroup X) = Nat.card P := by
    have := Subgroup.relIndex_mul_card (H := P ⊓ K) (K := P)
    rwa [inf_eq_left.mpr inf_le_left] at this
  have h4' : Nat.card K = P.relIndex (K ⊔ P) * Nat.card (P ⊓ K : Subgroup X) := by
    rw [← h4, h3]
  have key1 : (P ⊓ K).relIndex P * Nat.card K = Nat.card (K ⊔ P : Subgroup X) := by
    calc (P ⊓ K).relIndex P * Nat.card K
        = (P ⊓ K).relIndex P * (P.relIndex (K ⊔ P) * Nat.card (P ⊓ K : Subgroup X)) := by
          rw [h4']
      _ = P.relIndex (K ⊔ P) * ((P ⊓ K).relIndex P * Nat.card (P ⊓ K : Subgroup X)) := by ring
      _ = P.relIndex (K ⊔ P) * Nat.card P := by rw [h5]
      _ = Nat.card (K ⊔ P : Subgroup X) := h2
  exact Nat.mul_right_cancel Nat.card_pos (h1.trans key1.symm)

private lemma lit_Z_relIndex_litP (h : LitCtx Z A) :
    Z.relIndex (litP Z) = Nat.card (CFSG.oddCore X) := by
  have h1 := Subgroup.relIndex_mul_card (H := Z) (K := litP Z)
  have hinf : Z ⊓ litP Z = Z := inf_eq_left.mpr le_sup_left
  rw [hinf, h.card_Z, lit_card_litP h] at h1
  have h2 : Z.relIndex (litP Z) * 4 = Nat.card (CFSG.oddCore X) * 4 := by
    rw [h1]; ring
  exact Nat.mul_right_cancel (by norm_num : 0 < (4 : ℕ)) h2

private lemma not_two_dvd_oddCore : ¬ 2 ∣ Nat.card (CFSG.oddCore X) := by
  intro h2
  exact (Nat.not_even_iff_odd.mpr (lit_odd_card_oddCore X)) (even_iff_two_dvd.mpr h2)

private lemma lit_relIndex_sup_odd (h : LitCtx Z A) :
    ¬ 2 ∣ (litC Z A).relIndex (litC Z A ⊔ litP Z) := by
  haveI : (litP Z).Normal := Subgroup.sup_normal Z (CFSG.oddCore X)
  rw [relIndex_sup_eq_relIndex_inf (K := litC Z A) (P := litP Z)]
  have hZle : Z ≤ litP Z ⊓ litC Z A :=
    le_inf le_sup_left (le_trans h.Z_le_A (lit_A_le_litC h))
  have hdiv : (litP Z ⊓ litC Z A).relIndex (litP Z) ∣ Z.relIndex (litP Z) :=
    Subgroup.relIndex_dvd_of_le_left (L := litP Z) hZle
  rw [lit_Z_relIndex_litP h] at hdiv
  intro h2
  exact not_two_dvd_oddCore (h2.trans hdiv)

private lemma lit_relIndex_normalizer_sup_odd (h : LitCtx Z A) :
    ¬ 2 ∣ (normalizer (A : Set X)).relIndex (normalizer (A : Set X) ⊔ litP Z) := by
  haveI : (litP Z).Normal := Subgroup.sup_normal Z (CFSG.oddCore X)
  rw [relIndex_sup_eq_relIndex_inf (K := normalizer (A : Set X)) (P := litP Z)]
  have hZle : Z ≤ litP Z ⊓ normalizer (A : Set X) :=
    le_inf le_sup_left (le_trans h.Z_le_A Subgroup.le_normalizer)
  have hdiv : (litP Z ⊓ normalizer (A : Set X)).relIndex (litP Z) ∣ Z.relIndex (litP Z) :=
    Subgroup.relIndex_dvd_of_le_left (L := litP Z) hZle
  rw [lit_Z_relIndex_litP h] at hdiv
  intro h2
  exact not_two_dvd_oddCore (h2.trans hdiv)

private lemma lit_A_relIndex_litC_sup_odd (h : LitCtx Z A) :
    ¬ 2 ∣ A.relIndex (litC Z A ⊔ litP Z) := by
  have hfac : A.relIndex (litC Z A ⊔ litP Z) =
      A.relIndex (litC Z A) * (litC Z A).relIndex (litC Z A ⊔ litP Z) :=
    (Subgroup.relIndex_mul_relIndex A (litC Z A) (litC Z A ⊔ litP Z)
      (lit_A_le_litC h) le_sup_left).symm
  rw [hfac]
  exact Nat.prime_two.not_dvd_mul h.sylow (lit_relIndex_sup_odd h)

theorem lit_map_normalizer (h : LitCtx Z A) (hπ : Function.Surjective π)
    (hk : π.ker = litP Z) :
    normalizer ((A.map π : Subgroup G) : Set G) = (normalizer (A : Set X)).map π := by
  refine lit_normalizer_map (G := X) (H := G) π hπ (LitCtx.isPGroup_A h) ?_
  rw [hk]
  exact lit_A_sylow_sup h

theorem lit_mem_normalizer_map {n : X} (hn : n ∈ normalizer (A : Set X)) :
    π n ∈ normalizer ((A.map π : Subgroup G) : Set G) := by
  exact Subgroup.le_normalizer_map (H := A) π ⟨n, hn, rfl⟩

theorem lit_map_card (h : LitCtx Z A) (hk : π.ker = litP Z) : Nat.card (A.map π) = 16 := by
  have h1 := Subgroup.relIndex_mul_card (H := π.ker) (K := A)
  rw [Subgroup.relIndex_ker (K := A) π] at h1
  rw [hk, inf_comm, lit_A_inf_litP h, h.card_Z, h.card_A] at h1
  omega

theorem lit_map_comm (h : LitCtx Z A) (hk : π.ker = litP Z) :
    ∀ a ∈ A.map π, ∀ b ∈ A.map π, a * b = b * a := by
  intro a ha b hb
  rcases Subgroup.mem_map.mp ha with ⟨a', ha', rfl⟩
  rcases Subgroup.mem_map.mp hb with ⟨b', hb', rfl⟩
  have hker : ⁅a', b'⁆ ∈ π.ker := by
    rw [hk]
    exact show ⁅a', b'⁆ ∈ Z ⊔ CFSG.oddCore X from
      Subgroup.mem_sup_left (h.comm_mem a' ha' b' hb')
  have h1 : π ⁅a', b'⁆ = 1 := MonoidHom.mem_ker.mp hker
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem lit_map_sq (h : LitCtx Z A) (hk : π.ker = litP Z) : ∀ a ∈ A.map π, a ^ 2 = 1 := by
  intro a ha
  rcases Subgroup.mem_map.mp ha with ⟨a', ha', rfl⟩
  have hker : a' ^ 2 ∈ π.ker := by
    rw [hk]
    exact show a' ^ 2 ∈ Z ⊔ CFSG.oddCore X from Subgroup.mem_sup_left (h.sq_mem a' ha')
  have h1 : π (a' ^ 2) = 1 := MonoidHom.mem_ker.mp hker
  simpa using h1

theorem lit_map_centralizer (h : LitCtx Z A) (hπ : Function.Surjective π)
    (hk : π.ker = litP Z) :
    centralizer ((A.map π : Subgroup G) : Set G) = (litC Z A).map π := by
  apply le_antisymm
  · intro c hc
    have hcnorm : c ∈ normalizer ((A.map π : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ hc
    rw [lit_map_normalizer h hπ hk] at hcnorm
    rcases Subgroup.mem_map.mp hcnorm with ⟨n, hn, hnc⟩
    rw [← hnc]
    refine Subgroup.mem_map.mpr ⟨n, ?_, rfl⟩
    rw [mem_litC]
    refine ⟨hn, fun a ha => ?_⟩
    have hcomm : π a * π n = π n * π a := by
      have h1 := (Subgroup.mem_centralizer_iff.mp hc) (π a)
        (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
      rwa [← hnc] at h1
    have hker : ⁅a, n⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    rw [hk] at hker
    have hmemA : ⁅a, n⁆ ∈ A := by
      have hnA : n * a⁻¹ * n⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hn a⁻¹).mp (inv_mem ha)
      rw [commutatorElement_def]
      have heq : a * n * a⁻¹ * n⁻¹ = a * (n * a⁻¹ * n⁻¹) := by group
      rw [heq]
      exact A.mul_mem ha hnA
    have hmem : ⁅a, n⁆ ∈ A ⊓ litP Z := ⟨hmemA, hker⟩
    rwa [lit_A_inf_litP h] at hmem
  · intro c hc
    rcases Subgroup.mem_map.mp hc with ⟨n, hn, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    rw [mem_litC] at hn
    have hker : ⁅a, n⁆ ∈ π.ker := by
      rw [hk]
      exact show ⁅a, n⁆ ∈ Z ⊔ CFSG.oddCore X from Subgroup.mem_sup_left (hn.2 a ha)
    have h1 : π ⁅a, n⁆ = 1 := MonoidHom.mem_ker.mp hker
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

theorem lit_map_two_mem (h : LitCtx Z A) (hπ : Function.Surjective π) (hk : π.ker = litP Z) :
    ∀ c ∈ centralizer ((A.map π : Subgroup G) : Set G), (∃ k : ℕ, c ^ 2 ^ k = 1) →
      c ∈ A.map π := by
  intro c hc hk2
  haveI : Finite G := Finite.of_surjective π hπ
  have hcentral : centralizer ((A.map π : Subgroup G) : Set G) = (litC Z A).map π :=
    lit_map_centralizer h hπ hk
  have hAC : A.map π ≤ centralizer ((A.map π : Subgroup G) : Set G) := by
    rw [hcentral]
    exact Subgroup.map_mono (lit_A_le_litC h)
  have hcent : ∀ a ∈ A.map π, ∀ d ∈ centralizer ((A.map π : Subgroup G) : Set G),
      a * d = d * a := by
    intro a ha d hd
    exact Subgroup.mem_centralizer_iff.mp hd a ha
  have hidx : ¬ 2 ∣ (A.map π).relIndex (centralizer ((A.map π : Subgroup G) : Set G)) := by
    rw [hcentral, Subgroup.relIndex_map_map π A (litC Z A), hk]
    intro h2
    exact lit_A_relIndex_litC_sup_odd h
      (h2.trans (Subgroup.relIndex_dvd_of_le_left
        (L := litC Z A ⊔ litP Z) (le_sup_left : A ≤ A ⊔ litP Z)))
  rcases hk2 with ⟨k, hk2⟩
  exact lit_two_mem_of_central hAC hcent (LitCtx.isPGroup_A h |>.map π) hidx hc hk2

theorem lit_map_even (h : LitCtx Z A) (hπ : Function.Surjective π) (hk : π.ker = litP Z) :
    Even (normalizer ((A.map π : Subgroup G) : Set G)).index := by
  rw [lit_map_normalizer h hπ hk, Subgroup.index_map, π.range_eq_top_of_surjective hπ,
    Subgroup.index_top, mul_one, hk]
  have hodd := lit_relIndex_normalizer_sup_odd h
  have hrel := Subgroup.relIndex_mul_index
    (H := normalizer (A : Set X)) (K := normalizer (A : Set X) ⊔ litP Z) le_sup_left
  have heven : Even ((normalizer (A : Set X)).relIndex (normalizer (A : Set X) ⊔ litP Z) *
      (normalizer (A : Set X) ⊔ litP Z).index) := by
    rw [hrel]
    exact h.even
  rcases Nat.prime_two.dvd_mul.mp (even_iff_two_dvd.mp heven) with h2 | h2
  · exact absurd h2 hodd
  · exact even_iff_two_dvd.mpr h2

end CFSG.OddStandard.HigherRank.YamadaG23
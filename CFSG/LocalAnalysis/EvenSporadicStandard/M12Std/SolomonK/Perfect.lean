module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.BasicSylow

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

def oddOrderSubgroup (A : Type*) [CommGroup A] : Subgroup A where
  carrier := {a | Odd (orderOf a)}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have hlcm : Odd (Nat.lcm (orderOf a) (orderOf b)) :=
      Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨ha, hb⟩) (Nat.lcm_dvd_mul _ _)
    exact Odd.of_dvd_nat hlcm (Commute.all a b).orderOf_mul_dvd_lcm
  inv_mem' := by
    intro a ha
    simpa only [Set.mem_setOf_eq, orderOf_inv] using ha

theorem abelianization_odd_of_fusionSimple (h : FusionSimple K) (a : Abelianization K) :
    Odd (orderOf a) := by
  let Aodd : Subgroup (Abelianization K) := oddOrderSubgroup (Abelianization K)
  let M : Subgroup K := Aodd.comap (Abelianization.of (G := K))
  haveI : M.Normal := inferInstance
  have hsurj : Function.Surjective (Abelianization.of (G := K)) := by
    intro a
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (commutator K) a
    exact ⟨y, hy⟩
  haveI : Finite (Abelianization K) := Finite.of_surjective _ hsurj
  have hPgroup : IsPGroup 2 (K ⧸ M) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective M x
    have hne : orderOf (Abelianization.of (G := K) y) ≠ 0 :=
      (orderOf_pos (Abelianization.of (G := K) y)).ne'
    obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd hne
    refine ⟨k, ?_⟩
    have hmem : (Abelianization.of (G := K) y) ^ 2 ^ k ∈ Aodd := by
      have hpow : ((Abelianization.of (G := K) y) ^ 2 ^ k) ^ m = 1 := by
        rw [← pow_mul, ← hord, pow_orderOf_eq_one]
      have hdvd : orderOf ((Abelianization.of (G := K) y) ^ 2 ^ k) ∣ m :=
        orderOf_dvd_iff_pow_eq_one.mpr hpow
      exact Odd.of_dvd_nat hm hdvd
    have hyM : y ^ 2 ^ k ∈ M := by
      rw [Subgroup.mem_comap]
      simpa only [map_pow] using hmem
    rw [← map_pow (QuotientGroup.mk' M) y (2 ^ k)]
    simpa only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] using hyM
  have hMtop : M = ⊤ := h.2.2 M hPgroup
  have hAodd : Aodd = ⊤ := by
    have h1 : M.map (Abelianization.of (G := K)) = Aodd :=
      Subgroup.map_comap_eq_self_of_surjective hsurj Aodd
    rw [hMtop, Subgroup.map_top_of_surjective _ hsurj] at h1
    exact h1.symm
  change a ∈ Aodd
  rw [hAodd]
  exact Subgroup.mem_top a

theorem mem_commutator_of_two_pow_order (h : FusionSimple K) {x : K}
    (hx : ∃ k, orderOf x = 2 ^ k) : x ∈ commutator K := by
  have hodd : Odd (orderOf (Abelianization.of (G := K) x)) :=
    abelianization_odd_of_fusionSimple h (Abelianization.of x)
  obtain ⟨k, hk⟩ := hx
  have hdvd : orderOf (Abelianization.of (G := K) x) ∣ orderOf x := by
    rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, pow_orderOf_eq_one, map_one]
  rw [hk] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    by_contra hjne
    exact Nat.not_even_iff_odd.mpr (hj ▸ hodd) (even_two.pow_of_ne_zero hjne)
  have hone : orderOf (Abelianization.of (G := K) x) = 1 := by
    rw [hj, hj0, pow_zero]
  have hx1 : Abelianization.of (G := K) x = 1 := orderOf_eq_one_iff.mp hone
  have hker : x ∈ (Abelianization.of (G := K)).ker := MonoidHom.mem_ker.mpr hx1
  rwa [Abelianization.ker_of] at hker

theorem sylow_le_commutator (h : FusionSimple K) (S : Sylow 2 K) :
    (S : Subgroup K) ≤ commutator K := by
  intro x hx
  apply mem_commutator_of_two_pow_order h
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_orderOf_eq_pow (⟨x, hx⟩ : S)
  refine ⟨k, ?_⟩
  rw [← Subgroup.orderOf_mk (H := S) x hx]
  exact hk

theorem isPerfect_of_hyp (hP : P12Facts) (hK : SolomonA12HypK K) : Group.IsPerfect K := by
  obtain ⟨E, hE⟩ := hK.exists_goodE
  obtain ⟨S, hES⟩ := hE.isPGroup.exists_le_sylow
  haveI hK'normal : (commutator K).Normal := inferInstance
  have hSle : (S : Subgroup K) ≤ commutator K := sylow_le_commutator hK.fusionSimple S
  have hEK' : E ≤ commutator K := hES.trans hSle
  have hFrattini : normalizer (S : Set K) ⊔ commutator K = ⊤ :=
    Sylow.normalizer_sup_eq_top' S hSle
  have hNS : normalizer (S : Set K) ≤ normalizer (E : Set K) :=
    hE.normalizer_sylow_le hP hK hES
  let M : Subgroup K := normalizer (E : Set K) ⊓ commutator K
  have hEM : E ≤ M := fun x hx =>
    Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hx, hEK' hx⟩
  have hMN : M ≤ normalizer (E : Set K) := inf_le_left
  have hMnorm : ∀ g ∈ normalizer (E : Set K), ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    intro g hg m hm
    obtain ⟨hmN, hmK'⟩ := Subgroup.mem_inf.mp hm
    exact Subgroup.mem_inf.mpr
      ⟨(normalizer (E : Set K)).mul_mem
          ((normalizer (E : Set K)).mul_mem hg hmN) ((normalizer (E : Set K)).inv_mem hg),
        hK'normal.conj_mem m hmK' g⟩
  have hNle : normalizer (E : Set K) ≤ commutator K := by
    rcases hE.eq_or_eq hEM hMN hMnorm with hME | hMN2
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := hE.exists_commutator_not_mem
      have hxM : x * y * x⁻¹ * y⁻¹ ∈ M := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact (normalizer (E : Set K)).mul_mem
            ((normalizer (E : Set K)).mul_mem
              ((normalizer (E : Set K)).mul_mem hx hy) ((normalizer (E : Set K)).inv_mem hx))
            ((normalizer (E : Set K)).inv_mem hy)
        · have hc : ⁅x, y⁆ ∈ commutator K :=
            Subgroup.commutator_mem_commutator
              (show x ∈ (⊤ : Subgroup K) from Subgroup.mem_top x)
              (show y ∈ (⊤ : Subgroup K) from Subgroup.mem_top y)
          simpa only [commutatorElement_def] using hc
      rw [hME] at hxM
      exact hxy hxM
    · calc normalizer (E : Set K) = M := hMN2.symm
        _ ≤ commutator K := inf_le_right
  have htop : (⊤ : Subgroup K) ≤ commutator K := by
    intro k _
    have hk : k ∈ normalizer (S : Set K) ⊔ commutator K := by
      rw [hFrattini]
      exact Subgroup.mem_top k
    rw [Subgroup.mem_sup_of_normal_right] at hk
    obtain ⟨y, hy, z, hz, rfl⟩ := hk
    exact (commutator K).mul_mem (hNle (hNS hy)) hz
  exact ⟨eq_top_iff.mpr htop⟩

end CFSG.EvenSporadicStandard.M12Std.SolomonK


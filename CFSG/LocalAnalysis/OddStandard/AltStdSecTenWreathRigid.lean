module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathBasic

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup

theorem odd_card_of_fixedPointFree_involution {N : Type*} [Group N] [Finite N] (φ : N ≃* N)
    (hφ : ∀ n, φ (φ n) = n) (hfix : ∀ n, φ n = n → n = 1) : Odd (Nat.card N) := by
  let f : N → N := fun n => n⁻¹ * φ n
  have hf_inj : Function.Injective f := by
    intro m n hmn
    have h1 : m * n⁻¹ = φ m * (φ n)⁻¹ := by
      have := congrArg (fun x => m * x * (φ n)⁻¹) hmn
      simpa [f, mul_assoc] using this.symm
    have h2' : φ m * (φ n)⁻¹ = φ (m * n⁻¹) := by
      rw [← map_inv, ← map_mul]
    have h3 : m * n⁻¹ = 1 := hfix (m * n⁻¹) (h1.trans h2').symm
    exact mul_inv_eq_one.mp h3
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hf_inj
  have hinv : ∀ g : N, φ g = g⁻¹ := by
    intro g
    obtain ⟨n, hn⟩ := hsurj g
    rw [← hn]
    simp only [f, map_mul, map_inv, hφ n, mul_inv_rev, inv_inv]
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro hdvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hg2 : g * g = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    simpa [pow_two] using this
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hfixg : φ g = g := by rw [hinv g, hginv]
  have hg1 : g = 1 := hfix g hfixg
  rw [hg1, orderOf_one] at hg
  omega

variable {X : Type} [Group X] [Finite X] {t : X} {A K : Subgroup X}

theorem WreathK.centralizer_layer_eq_bot (hE : ExactShape t A 8) (hK : WreathK t A K)
    (hO : CFSG.oddCore X = ⊥) : centralizer ((CFSG.layer X : Subgroup X) : Set X) = ⊥ := by
  classical
  let N : Subgroup X := centralizer ((CFSG.layer X : Subgroup X) : Set X)
  have hNnormal : N.Normal := by
    haveI : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
    change (centralizer ((CFSG.layer X : Subgroup X) : Set X)).Normal
    infer_instance
  haveI : N.Normal := hNnormal
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [hE.order] at this
    simpa [pow_two] using this
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hA_le_layer : A ≤ CFSG.layer X := by
    intro a ha
    have hmem : a ∈ (A : Set X) := ha
    rw [hK.diag] at hmem
    obtain ⟨k, hk, rfl⟩ := hmem
    have hk' : t * k * t⁻¹ ∈ conjSub t K := by
      rw [conjSub, Subgroup.mem_map]
      exact ⟨k, hk, by simpa using MulAut.conj_apply t k⟩
    exact (CFSG.layer X).mul_mem (hK.le_layer hk) (hK.conjSub_le_layer hk')
  have htnotN : (t : X) ∉ N := by
    intro htN
    apply hK.ne
    rw [conjSub]
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have hkc : k * t = t * k := (mem_centralizer_iff.mp htN) k (hK.le_layer hk)
      have hconj : MulAut.conj t k = k := by
        rw [MulAut.conj_apply, ← hkc]
        group
      change (MulAut.conj t) k ∈ K
      rw [hconj]
      exact hk
    · intro x hx
      rw [Subgroup.mem_map]
      refine ⟨x, hx, ?_⟩
      have hxc : x * t = t * x := (mem_centralizer_iff.mp htN) x (hK.le_layer hx)
      change (MulAut.conj t) x = x
      rw [MulAut.conj_apply, ← hxc]
      group
  have hodd : Odd (Nat.card N) := by
    refine odd_card_of_fixedPointFree_involution (MulAut.conjNormal (H := N) t) ?_ ?_
    · intro n
      have h2 : MulAut.conjNormal (H := N) t * MulAut.conjNormal (H := N) t = 1 := by
        rw [← map_mul, ht2, map_one]
      have := congrArg (fun g : MulAut N => g n) h2
      simpa [MulAut.mul_apply, MulAut.one_apply] using this
    · intro n hn
      have hnval : (t : X) * (n : X) * t⁻¹ = (n : X) := by
        have := congrArg Subtype.val hn
        simpa [MulAut.conjNormal_apply] using this
      have hncomm : (n : X) * t = t * (n : X) := by
        have htn : t * (n : X) = (n : X) * t := by
          calc t * (n : X) = (t * (n : X) * t⁻¹) * t := by group
            _ = (n : X) * t := by rw [hnval]
        exact htn.symm
      have hncent : (n : X) ∈ centralizer ({t} : Set X) := by
        rw [mem_centralizer_singleton_iff]
        exact hncomm
      have hnA : (n : X) ∈ centralizer (A : Set X) := centralizer_le hA_le_layer n.2
      have hnzp : (n : X) ∈ zpowers t := by
        rw [← hE.cent_cent]
        exact ⟨hnA, hncent⟩
      have hnmem : (n : X) ∈ (Finset.range (orderOf t)).image (t ^ ·) :=
        (mem_zpowers_iff_mem_range_orderOf (x := t)).mp hnzp
      rw [hE.order] at hnmem
      simp only [Finset.mem_image, Finset.mem_range] at hnmem
      obtain ⟨a, ha, haeq⟩ := hnmem
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · exact Subtype.ext (by simpa using haeq.symm)
      · have hnt : (n : X) = t := by simpa using haeq.symm
        exact absurd (hnt ▸ n.2) htnotN
  exact le_bot_iff.mp (hO ▸ le_sSup ⟨hNnormal, hodd⟩)

end CFSG.OddStandard.AltStdSec.SwapPattern

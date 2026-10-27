module

public import CFSG.GH74.GLS.C3.Layer1.Th2P43fFrat
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt

variable {G : Type} [Group G]

@[expose] def FusesIn (x : G) (B : Subgroup G) : Prop :=
  ∀ b ∈ B, (∃ c : G, c * x * c⁻¹ = b) → ∃ g ∈ normalizer (B : Set G), g * x * g⁻¹ = b

variable {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem fuses_case_b [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {D : Subgroup G} (hD : IsFourSub (T ⊓ K) D)
    (hθ : ∀ w ∈ D, psi (a⁻¹ * w * a) = 1) : FusesIn x (D ⊔ conjugate D a) := by
  rintro b hbB ⟨c, hc⟩
  have haN : a ∈ normalizer ((D ⊔ conjugate D a : Subgroup G) : Set G) :=
    F.a_mem_normalizer_B hD
  have hb1 : b ≠ 1 := by
    intro h
    rw [h] at hc
    apply F.x_ne
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [hc]; group
  have hex : ∀ u ∈ D, u ≠ 1 →
      ∃ n ∈ normalizer ((D ⊔ conjugate D a : Subgroup G) : Set G), n * z * n⁻¹ = u := by
    intro u hu hu1
    by_cases huz : u = z
    · exact ⟨1, one_mem _, by rw [huz]; group⟩
    · exact F.frat_lift hD hθ hu hu1 huz
  have hDaP : ∀ q ∈ conjugate D a, q ∈ conjugate (T ⊓ K) a := fun q hq => by
    rw [mem_conjugate_iff'] at hq ⊢
    exact hD.1 hq
  obtain ⟨u, hu, q, hq, hbuq⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute
      (fun d hd q hq => F.core.comm_P_conj d (hD.1 hd) q (hDaP q hq)) hbB
  have hwD : a * q * a⁻¹ ∈ D := mem_conjugate_iff'.1 hq
  have hq' : q = a⁻¹ * (a * q * a⁻¹) * a := by group
  by_cases hw1 : a * q * a⁻¹ = 1
  · have hq1 : q = 1 := by rw [hq', hw1]; group
    have hbu : b = u := by rw [hbuq, hq1, mul_one]
    have hu1 : u ≠ 1 := by rw [← hbu]; exact hb1
    obtain ⟨n, hn, hnz⟩ := hex u hu hu1
    refine ⟨n * a, Subgroup.mul_mem _ hn haN, ?_⟩
    rw [hbu, ← hnz, ← F.a_x]
    group
  · by_cases hu1 : u = 1
    · have hb : b = a⁻¹ * (a * q * a⁻¹) * a := by rw [hbuq, hu1, one_mul]; exact hq'
      obtain ⟨n, hn, hnz⟩ := hex _ hwD hw1
      refine ⟨a⁻¹ * n * a, ?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ haN) hn) haN
      · rw [hb, ← hnz]
        calc (a⁻¹ * n * a) * x * (a⁻¹ * n * a)⁻¹ = a⁻¹ * (n * (a * x * a⁻¹) * n⁻¹) * a := by group
          _ = a⁻¹ * (n * z * n⁻¹) * a := by rw [F.a_x]
    · exfalso
      have huP : u ∈ T ⊓ K := hD.1 hu
      have hwP : a * q * a⁻¹ ∈ T ⊓ K := hD.1 hwD
      have hu2 : u * u = 1 := (forall_of_isElementaryAbelian hD.2.1).2 u hu
      have hw2 : (a * q * a⁻¹) * (a * q * a⁻¹) = 1 := (forall_of_isElementaryAbelian hD.2.1).2 _ hwD
      have hmixed := F.isConj_tt_v_of_right huP hwP hu2 hw2 hu1 hw1 (hθ _ hwD)
      have hbt : b = tt a u (a * q * a⁻¹) := by
        unfold tt
        rw [hbuq]
        congr 1
      rw [← hbt] at hmixed
      have hxb : IsConj x b := isConj_iff.2 ⟨c, hc⟩
      exact F.not_isConj_v_of_Q hG hs e7 hP2 hQ4 ⟨F.x_mem_T, F.x_mem_CxK⟩ F.x_sq F.x_ne
        (hxb.trans hmixed)

end Frame

end CFSG.GH74.GLS.Th2.P43f

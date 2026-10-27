module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Base
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Card
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L111Na

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem sec113_a_not_Q (hm : Sec11Model t L S z K1 K2 T Alt φ) (k : Fin 6) :
    φ (Pi.single k 1) ∉ secQ K1 K2 := by
  intro h
  have h1 := ((hm.mem_Q _).1 h).1
  rw [sec113_single_sum] at h1
  exact one_ne_zero h1

theorem sec113_a_sq (hm : Sec11Model t L S z K1 K2 T Alt φ) (k : Fin 6) :
    φ (Pi.single k 1) * φ (Pi.single k 1) = 1 :=
  hm.perm.sq _

theorem sec113_conj_mem_iff_of_comm {t : G} {H : Subgroup G} (h : ∀ y ∈ H, t * y = y * t)
    {y : G} : t * y * t⁻¹ ∈ H ↔ y ∈ H := by
  constructor
  · intro hw
    have h1 : t * (t * y * t⁻¹) = (t * y * t⁻¹) * t := h _ hw
    have h2 : y = t⁻¹ * (t * y * t⁻¹) * t := by group
    rw [h2, mul_assoc, ← h1]
    simpa using hw
  · intro hy
    rw [h y hy]
    simpa using hy

theorem sec113_swap [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hm : Sec11Model t L S z K1 K2 T Alt φ) {k : Fin 6}
    (hk : 2 ≤ k) : CFSG.conjugate K1 (φ (Pi.single k 1)) = K2 := by
  have h10 : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  have hbB : φ (Pi.single 0 1 + Pi.single k 1) ∈ secB S L :=
    (hm.mem_B _).2 (sec113_single_add_sum 0 k)
  have hbL := secB_le_L S L hbB
  have hbS := secB_le_S S L hbB
  have hbC : φ (Pi.single 0 1 + Pi.single k 1) ∈ centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central _ hbS)
  have hbQ : φ (Pi.single 0 1 + Pi.single k 1) ∉ secQ K1 K2 := fun h =>
    sec113_e0_add_ne k hk ((hm.mem_Q _).1 h).2
  have hbn : φ (Pi.single 0 1 + Pi.single k 1) ∉ K1 ⊔ K2 := by
    intro h
    have hK0 := sec11_K_le_K0 hp.r10.lK0 h10 h
    refine hbQ (sec10T_two_elem_K0 hp.r10.lK0 hp.s3.l36 hp.facts.pockets5 hp.facts.centZ5
      hp.basic h10 hK0 ⟨1, ?_⟩)
    rw [pow_one, pow_two]
    exact hm.perm.sq _
  have hbn' : φ (Pi.single 0 1 + Pi.single k 1) ∉ K2 ⊔ K1 := by rwa [sup_comm]
  have h12 := sec10A2_swap hp.facts hp.basic h10 _ ⟨hbL, hbC⟩ hbn
  have h21 := sec10A2_swap hp.facts hp.basic h10.swap _ ⟨hbL, hbC⟩ hbn'
  have hKt : ∀ y ∈ K1, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (sec11_K0_le t z (sec11_K_le_K0 hp.r10.lK0 h10 (Subgroup.mem_sup_left hy))).1).symm
  have hat : φ (Pi.single k 1) = t * φ (Pi.single 0 1 + Pi.single k 1) := by
    rw [hm.t_eq, ← hm.perm.mul, ← add_assoc, sec11_vec_add_self, zero_add]
  have hbinv : (φ (Pi.single 0 1 + Pi.single k 1))⁻¹ = φ (Pi.single 0 1 + Pi.single k 1) :=
    hm.perm.inv_eq _
  ext x
  rw [mem_conjugate_iff']
  have hconj : φ (Pi.single k 1) * x * (φ (Pi.single k 1))⁻¹ =
      t * (φ (Pi.single 0 1 + Pi.single k 1) * x * (φ (Pi.single 0 1 + Pi.single k 1))⁻¹) *
        t⁻¹ := by
    rw [hat]
    group
  rw [hconj, sec113_conj_mem_iff_of_comm hKt]
  constructor
  · intro hx
    have h3 := h12 _ hx
    have h4 : φ (Pi.single 0 1 + Pi.single k 1) *
        (φ (Pi.single 0 1 + Pi.single k 1) * x * (φ (Pi.single 0 1 + Pi.single k 1))⁻¹) *
        (φ (Pi.single 0 1 + Pi.single k 1))⁻¹ = x := by
      rw [hbinv]
      have := hm.perm.sq (Pi.single 0 1 + Pi.single k 1)
      calc _ = (φ (Pi.single 0 1 + Pi.single k 1) * φ (Pi.single 0 1 + Pi.single k 1)) * x *
            (φ (Pi.single 0 1 + Pi.single k 1) * φ (Pi.single 0 1 + Pi.single k 1)) := by group
        _ = x := by rw [this]; group
    rwa [h4] at h3
  · intro hx
    exact h21 x hx

theorem sec113_a_comm (hm : Sec11Model t L S z K1 K2 T Alt φ) {k : Fin 6} (hk : 2 ≤ k)
    {C : Subgroup G} (hC : C = zpowers t ⊔ zpowers z ∨
      ∃ r : G, (∀ v, r * φ v * r⁻¹ = φ (permVec (Equiv.swap (0 : Fin 6) 1) v)) ∧
        C = zpowers t ⊔ zpowers r) :
    ∀ c ∈ C, φ (Pi.single k 1) * c = c * φ (Pi.single k 1) := by
  have ht : φ (Pi.single k 1) * t = t * φ (Pi.single k 1) := by
    rw [hm.t_eq, ← hm.perm.mul, ← hm.perm.mul, add_comm]
  have hle : ∀ g : G, φ (Pi.single k 1) * g = g * φ (Pi.single k 1) →
      zpowers t ⊔ zpowers g ≤ centralizer ({φ (Pi.single k 1)} : Set G) := by
    intro g hg
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_) <;>
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact ht.symm
    · exact hg.symm
  intro c hc
  rcases hC with rfl | ⟨r, hr, rfl⟩
  · have hz : φ (Pi.single k 1) * z = z * φ (Pi.single k 1) := by
      rw [sec113_z_eq hm, ← hm.perm.mul, ← hm.perm.mul, add_comm]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle z hz hc)).symm
  · have hrk : φ (Pi.single k 1) * r = r * φ (Pi.single k 1) := by
      have h1 := hr (Pi.single k 1)
      rw [sec11_permVec_single] at h1
      have h2 : Equiv.swap (0 : Fin 6) 1 k = k := by
        apply Equiv.swap_apply_of_ne_of_ne <;> intro h <;> subst h <;> revert hk <;> decide
      rw [h2] at h1
      calc φ (Pi.single k 1) * r = (r * φ (Pi.single k 1) * r⁻¹) * r := by rw [h1]
        _ = r * φ (Pi.single k 1) := by group
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle r hrk hc)).symm

end CFSG.OddStandard.SmallF3.Omega

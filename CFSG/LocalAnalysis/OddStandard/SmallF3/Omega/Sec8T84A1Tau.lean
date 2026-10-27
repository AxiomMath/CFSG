module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Basic
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMHom
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}

theorem sec8t84a1_exists_tau (h8A : Asc82Lemma8A) (h8B : Asc82Lemma8B)
    (hctx : Sec8Ctx G t L S z g B) :
    ∃ τ : ↥(Nsub8 t B ⊓ centralizer (B : Set G)) →* ↥B,
      (∀ x, ((τ x : ↥B) : G) = (x : G) * t * (x : G)⁻¹ * t⁻¹) ∧
        τ.ker = (Asub8 t B ⊔ oddCoreIn (Nsub8 t B)).subgroupOf
          (Nsub8 t B ⊓ centralizer (B : Set G)) := by
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b :=
    fun b hb b' hb' => CFSG.Open.IsElemAbelian.comm hctx.B_e16.1 hb hb'
  have hMB : ∀ m ∈ Nsub8 t B ⊓ centralizer (B : Set G), ∀ b ∈ B, m * b = b * m :=
    fun m hm b hb => (Subgroup.mem_centralizer_iff.mp hm.2 b hb).symm
  have ha : ∀ m ∈ Nsub8 t B ⊓ centralizer (B : Set G), m * t * m⁻¹ * t⁻¹ ∈ B :=
    fun m hm => sec8t84a1_comm_mem h8B hctx hm.1
  obtain ⟨τ, hτ⟩ := sec9m_exists_commHom
    (M := Nsub8 t B ⊓ centralizer (B : Set G)) (B := B) (a := t) hBc hMB ha
  refine ⟨τ, hτ, ?_⟩
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    have hxt : (x : G) * t = t * (x : G) := by
      have h1 : (x : G) * t * (x : G)⁻¹ * t⁻¹ = 1 := by
        have h2 := congrArg Subtype.val hx
        rwa [hτ x, Subgroup.coe_one] at h2
      calc (x : G) * t = ((x : G) * t * (x : G)⁻¹ * t⁻¹) * (t * (x : G)) := by group
        _ = t * (x : G) := by rw [h1, one_mul]
    have hle : zpowers t ⊔ B ≤ centralizer ({(x : G)} : Set G) := by
      refine sup_le ?_ ?_
      · rw [zpowers_le, mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hxt
      · intro b hb
        rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (Subgroup.mem_centralizer_iff.mp x.2.2 b hb).symm
    have hxcent : (x : G) ∈ centralizer ((zpowers t ⊔ B : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      exact (mem_centralizer_iff.mp (hle hy) (x : G) (Set.mem_singleton (x : G))).symm
    rw [← sec8t84a1_centA h8A hctx]
    simpa [Asub8] using hxcent
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hτ x, Subgroup.coe_one]
    have hx' : (x : G) ∈ centralizer (Asub8 t B : Set G) := by
      rw [← sec8t84a1_centA h8A hctx] at hx
      exact hx
    have hcomm : t * (x : G) = (x : G) * t :=
      Subgroup.mem_centralizer_iff.mp hx' t sec8t84a1_t_mem_A
    rw [← hcomm]; group

theorem sec8t84a1_tau_conj {h c : G} (hh : h * t = t * h) :
    (h * c * h⁻¹) * t * (h * c * h⁻¹)⁻¹ * t⁻¹ = h * (c * t * c⁻¹ * t⁻¹) * h⁻¹ := by
  have ht : h * t * h⁻¹ = t := by rw [hh]; group
  have hth : h⁻¹ * t * h = t := by
    calc h⁻¹ * t * h = h⁻¹ * (h * t * h⁻¹) * h := by rw [ht]
      _ = t := by group
  have htinv : t⁻¹ * h⁻¹ = h⁻¹ * t⁻¹ := by
    have := congrArg Inv.inv hh
    simpa [mul_inv_rev] using this
  calc
    (h * c * h⁻¹) * t * (h * c * h⁻¹)⁻¹ * t⁻¹
        = h * c * (h⁻¹ * t * h) * c⁻¹ * (h⁻¹ * t⁻¹) := by group
    _ = h * c * t * c⁻¹ * (h⁻¹ * t⁻¹) := by rw [hth]
    _ = h * c * t * c⁻¹ * t⁻¹ * h⁻¹ := by rw [← htinv, ← mul_assoc]
    _ = h * (c * t * c⁻¹ * t⁻¹) * h⁻¹ := by group

end CFSG.OddStandard.SmallF3.Omega

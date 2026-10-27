module

public import Certificates.Certificate24846

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

variable {G : Type} [Group G] {L A : Subgroup G}

@[expose] def QdFixAt (L A : Subgroup G) (x : G) : Prop :=
  ∀ w ∈ A, (∀ n ∈ egNL L A, n * x * n⁻¹ = x → n * w * n⁻¹ = w) → w = 1 ∨ w = x

theorem QdFixAt.transfer {a x m : G} (hm : m ∈ egNL L A) (hma : m * a * m⁻¹ = x)
    (h : QdFixAt L A a) : QdFixAt L A x := by
  subst hma
  intro w hw hyp
  have hmN : m ∈ normalizer (A : Set G) := (mem_inf.1 hm).1
  have hw' : m⁻¹ * w * m ∈ A := by
    have := (mem_normalizer_iff.1 (inv_mem hmN) w).1 hw
    simpa using this
  have hw2 : w = m * (m⁻¹ * w * m) * m⁻¹ := by group
  refine (h (m⁻¹ * w * m) hw' ?_).imp (fun h1 => ?_) (fun h1 => ?_)
  · intro n' hn' hn'a
    have hn : m * n' * m⁻¹ ∈ egNL L A := mul_mem (mul_mem hm hn') (inv_mem hm)
    have h1 : (m * n' * m⁻¹) * (m * a * m⁻¹) * (m * n' * m⁻¹)⁻¹ = m * a * m⁻¹ := by
      calc _ = m * (n' * a * n'⁻¹) * m⁻¹ := by group
        _ = m * a * m⁻¹ := by rw [hn'a]
    have h2 := hyp _ hn h1
    calc n' * (m⁻¹ * w * m) * n'⁻¹
        = m⁻¹ * ((m * n' * m⁻¹) * w * (m * n' * m⁻¹)⁻¹) * m := by group
      _ = m⁻¹ * w * m := by rw [h2]
  · rw [hw2, h1]
    group
  · rw [hw2, h1]

section Pinned

variable (e : L ≃* S24) (hAL : A ≤ L) (hA : ∀ x : L, (x : G) ∈ A ↔ e x ∈ m24E1l)
include hAL hA

theorem qdFixAt_base {a : S24} {st : List S24} (hb : QdBase a st) : QdFixAt L A (qdIota e a) := by
  obtain ⟨-, hst, hfix⟩ := hb
  intro w hw hyp
  obtain ⟨t, ht, rfl⟩ := (qdMem_A_iff e hAL hA w).1 hw
  have key : ∀ g ∈ st, g * t * g⁻¹ = t := by
    intro g hg
    have hn := qdIota_mem_egNL e hAL hA (hst g hg).1.norm
    have h1 : qdIota e g * qdIota e a * (qdIota e g)⁻¹ = qdIota e a := by
      rw [qdIota_conj, (hst g hg).2]
    have h2 := hyp _ hn h1
    rw [qdIota_conj] at h2
    exact qdIota_injective e h2
  rcases hfix t ht key with h | h
  · left
    rw [h, map_one]
  · right
    rw [h]

end Pinned

theorem fix_of_type (h : SextetType L A) :
    ∀ x ∈ A, x ≠ 1 → ∀ w ∈ A,
      (∀ n ∈ egNL L A, n * x * n⁻¹ = x → n * w * n⁻¹ = w) → w = 1 ∨ w = x := by
  obtain ⟨hAL, e, he⟩ := h
  obtain ⟨hgs, hcov, hb1, hb2⟩ := Certificates.certificate24846
  have hnorm : ∀ g ∈ qdGens, QdNorm g := fun g hg => (hgs g hg).norm
  intro x hx hx1
  obtain ⟨s, hs, rfl⟩ := (qdMem_A_iff e hAL he x).1 hx
  have hs1 : s ≠ 1 := fun h => hx1 (by rw [h, map_one])
  rcases hcov s hs hs1 with hr | hr
  · obtain ⟨m, hm, hma⟩ := exists_norm_of_mem_qdReach hnorm hr
    exact (qdFixAt_base e hAL he hb1).transfer (qdIota_mem_egNL e hAL he hm)
      (by rw [qdIota_conj, hma])
  · obtain ⟨m, hm, hma⟩ := exists_norm_of_mem_qdReach hnorm hr
    exact (qdFixAt_base e hAL he hb2).transfer (qdIota_mem_egNL e hAL he hm)
      (by rw [qdIota_conj, hma])

end CFSG.EvenSporadicStandard.M24Std

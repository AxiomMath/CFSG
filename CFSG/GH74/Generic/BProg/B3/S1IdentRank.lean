module

public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Filter.Lie.Q8Cube

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1IdentRank

open CFSG.GH74.Generic CFSG.GH74.Filter.Lie CFSG.GH74 Subgroup

theorem rankCertified_of_quaternion_centralizer {X : Type} [Group X] [Finite X] {M : Subgroup X}
    (φ : QuaternionGroup 2 →* X) (hφ : Function.Injective φ)
    (hcent : ∀ g : QuaternionGroup 2, ∀ m ∈ M, φ g * m = m * φ g) {r : ℕ}
    (h : RankCertified (↥M ⧸ center ↥M) r) : RankCertified X (r + 2) := by
  obtain ⟨K, A, _, _, _, α, β, hβ, hc, hs, hcard, hker⟩ := h
  let π : ↥M →* ↥M ⧸ center ↥M := QuotientGroup.mk' (center ↥M)
  let P : Subgroup (K × ↥M) :=
    (α.comp (MonoidHom.fst K ↥M)).eqLocus (π.comp (MonoidHom.snd K ↥M))
  let f : ↥P →* X := M.subtype.comp ((MonoidHom.snd K ↥M).comp P.subtype)
  have hf : ∀ p : ↥P, f p = ((p.1.2 : ↥M) : X) := fun p => rfl
  have hcomm : ∀ (p : ↥P) (q : QuaternionGroup 2), Commute (f p) (φ q) := fun p q =>
    (hcent q _ p.1.2.2).symm
  let α' : ↥P × QuaternionGroup 2 →* X := f.noncommCoprod φ hcomm
  let β' : ↥P × QuaternionGroup 2 →* A × Multiplicative (ZMod 2 × ZMod 2) :=
    ((β.comp (MonoidHom.fst K ↥M)).comp P.subtype).prodMap q8Frattini
  have hα' : ∀ p q, α' (p, q) = f p * φ q := fun p q => by
    simp [α', MonoidHom.noncommCoprod_apply]
  refine ⟨↥P × QuaternionGroup 2, A × Multiplicative (ZMod 2 × ZMod 2), inferInstance,
    inferInstance, inferInstance, α', β', ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨a, v⟩
    obtain ⟨k, rfl⟩ := hβ a
    obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (center ↥M) (α k)
    obtain ⟨g, hg⟩ := q8Frattini_surjective v
    exact ⟨(⟨(k, m), hm.symm⟩, g), Prod.ext rfl hg⟩
  · intro a b
    exact Prod.ext (hc _ _) (q8Frattini_comm _ _)
  · intro a
    exact Prod.ext (hs _) (q8Frattini_sq _)
  · rw [Nat.card_prod, q8Frattini_card]
    calc 2 ^ (r + 2) = 2 ^ r * 4 := by ring
      _ < Nat.card A * 4 := by omega
  · rintro ⟨p, q⟩ hk
    rw [MonoidHom.mem_ker, hα'] at hk
    have hinv : f p = (φ q)⁻¹ := eq_inv_of_mul_eq_one_left hk
    have hz : ((p.1.2 : ↥M) : X) = φ q⁻¹ := by rw [← hf, hinv, map_inv]
    have hcen : p.1.2 ∈ center ↥M := by
      rw [Subgroup.mem_center_iff]
      intro n
      apply Subtype.ext
      have := hcent q⁻¹ (n : X) n.2
      simp only [Subgroup.coe_mul]
      rw [hz]
      exact this.symm
    have hqc : ∀ b : QuaternionGroup 2, q * b = b * q := by
      intro b
      have h1 : Commute (φ b) (φ q)⁻¹ := by
        have := hcent b (f p) p.1.2.2
        rw [hinv] at this
        exact this
      have h2 : φ b * φ q = φ q * φ b := (Commute.inv_right_iff.1 h1).eq
      apply hφ
      rw [map_mul, map_mul]
      exact h2.symm
    have hq1 : q8Frattini q = 1 := q8Frattini_center q hqc
    have hπ : α p.1.1 = 1 := by
      have h0 : α p.1.1 = π p.1.2 := p.2
      rw [h0]
      exact (QuotientGroup.eq_one_iff _).2 hcen
    have hb : β p.1.1 = 1 := MonoidHom.mem_ker.1 (hker (MonoidHom.mem_ker.2 hπ))
    refine MonoidHom.mem_ker.2 (Prod.ext ?_ hq1)
    exact hb

theorem false_of_rankCertified_quaternion_centralizer {X : Type} [Group X] [Finite X] (hX : Gen4 X)
    {M : Subgroup X} (φ : QuaternionGroup 2 →* X) (hφ : Function.Injective φ)
    (hcent : ∀ g : QuaternionGroup 2, ∀ m ∈ M, φ g * m = m * φ g) {r : ℕ} (hr : 2 ≤ r)
    (h : RankCertified (↥M ⧸ center ↥M) r) : False :=
  (rankCertified_of_quaternion_centralizer φ hφ hcent h).not_gen4 (by omega) hX

end S1IdentRank

end CFSG.GH74.Generic.BProg.B3

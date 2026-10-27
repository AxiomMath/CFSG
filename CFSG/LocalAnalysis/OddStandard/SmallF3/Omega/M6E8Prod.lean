module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma m6e8_dvd_of_card_eq (k r cA cB zA zB m : ℕ) (hk : 0 < k)
    (h1 : k * r = (cA * zA) * (cB * zB)) (h2 : zA * zB = k * m) : cA * cB ∣ r := by
  have hkr : k * r = k * (cA * cB * m) := by
    calc k * r = (cA * zA) * (cB * zB) := h1
      _ = cA * cB * (zA * zB) := by ring
      _ = cA * cB * (k * m) := by rw [h2]
      _ = k * (cA * cB * m) := by ring
  exact ⟨m, Nat.eq_of_mul_eq_mul_left hk hkr⟩

theorem m6e8_ctrQ_mul_dvd [Finite G] {A B C : Subgroup G} (hA : A ≤ C) (hB : B ≤ C)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : ctrQ A * ctrQ B ∣ ctrQ C := by
  let ψ : ↥A × ↥B →* ↥C := MonoidHom.mk'
    (fun p => ⟨(p.1 : G) * (p.2 : G), C.mul_mem (hA p.1.2) (hB p.2.2)⟩) (by
      intro p q
      apply Subtype.ext
      show ((p.1 * q.1 : ↥A) : G) * ((p.2 * q.2 : ↥B) : G) =
        ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
      push_cast
      calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
            = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
        _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
              rw [hcomm (q.1 : G) q.1.2 (p.2 : G) p.2.2]
        _ = (p.1 : G) * (p.2 : G) * ((q.1 : G) * (q.2 : G)) := by group)
  let φ : ↥A × ↥B →* ↥C ⧸ Subgroup.center ↥C :=
    (QuotientGroup.mk' (Subgroup.center ↥C)).comp ψ
  have hker : φ.ker ≤ (Subgroup.center ↥A).prod (Subgroup.center ↥B) := by
    intro p hp
    have hp1 : φ p = 1 := MonoidHom.mem_ker.mp hp
    have hz : ψ p ∈ Subgroup.center ↥C := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center ↥C), MonoidHom.mem_ker]
      simpa only [φ, MonoidHom.comp_apply] using hp1
    have hzG : ∀ g : G, g ∈ C →
        g * ((p.1 : G) * (p.2 : G)) = ((p.1 : G) * (p.2 : G)) * g := fun g hg =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
    have hpa : p.1 ∈ Subgroup.center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro a'
      apply Subtype.ext
      exact mul_right_cancel (by
        have h1 := hzG (a' : G) (hA a'.2)
        calc (a' : G) * (p.1 : G) * (p.2 : G)
              = (a' : G) * ((p.1 : G) * (p.2 : G)) := by group
          _ = ((p.1 : G) * (p.2 : G)) * (a' : G) := h1
          _ = (p.1 : G) * ((p.2 : G) * (a' : G)) := by group
          _ = (p.1 : G) * ((a' : G) * (p.2 : G)) := by
                rw [← hcomm (a' : G) a'.2 (p.2 : G) p.2.2]
          _ = (p.1 : G) * (a' : G) * (p.2 : G) := by group)
    have hpb : p.2 ∈ Subgroup.center ↥B := by
      rw [Subgroup.mem_center_iff]
      intro b'
      apply Subtype.ext
      exact mul_left_cancel (by
        have h1 := hzG (b' : G) (hB b'.2)
        calc (p.1 : G) * ((b' : G) * (p.2 : G))
              = (p.1 : G) * (b' : G) * (p.2 : G) := by group
          _ = (b' : G) * (p.1 : G) * (p.2 : G) := by
                rw [hcomm (p.1 : G) p.1.2 (b' : G) b'.2]
          _ = (b' : G) * ((p.1 : G) * (p.2 : G)) := by group
          _ = ((p.1 : G) * (p.2 : G)) * (b' : G) := h1
          _ = (p.1 : G) * ((p.2 : G) * (b' : G)) := by group)
    exact Subgroup.mem_prod.mpr ⟨hpa, hpb⟩
  let k := Nat.card φ.ker
  let r := Nat.card φ.range
  let cA := Nat.card (↥A ⧸ Subgroup.center ↥A)
  let cB := Nat.card (↥B ⧸ Subgroup.center ↥B)
  let cC := Nat.card (↥C ⧸ Subgroup.center ↥C)
  let zA := Nat.card (Subgroup.center ↥A)
  let zB := Nat.card (Subgroup.center ↥B)
  have hkpos : 0 < k := by
    show 0 < Nat.card φ.ker
    exact Nat.card_pos_iff.mpr ⟨⟨1, φ.ker.one_mem⟩, inferInstance⟩
  have hkerdvd : k ∣ zA * zB := by
    have h := Subgroup.card_dvd_of_le hker
    rwa [Nat.card_congr (Subgroup.prodEquiv (Subgroup.center ↥A)
      (Subgroup.center ↥B)).toEquiv, Nat.card_prod] at h
  obtain ⟨m, hm⟩ := hkerdvd
  have h1 : k * r = (cA * zA) * (cB * zB) := by
    show Nat.card φ.ker * Nat.card φ.range =
      (Nat.card (↥A ⧸ Subgroup.center ↥A) * Nat.card (Subgroup.center ↥A)) *
      (Nat.card (↥B ⧸ Subgroup.center ↥B) * Nat.card (Subgroup.center ↥B))
    rw [Subgroup.card_ker_mul_card_range φ, Nat.card_prod,
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥A),
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥B)]
  have hdiv : cA * cB ∣ r := m6e8_dvd_of_card_eq k r cA cB zA zB m hkpos h1 hm
  have hrange : r ∣ cC := Subgroup.card_subgroup_dvd_card φ.range
  unfold ctrQ
  change cA * cB ∣ cC
  exact dvd_trans hdiv hrange

end CFSG.OddStandard.SmallF3.Omega

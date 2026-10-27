module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedRankForm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem p34_fusion {x : G} {Q K₀ : Subgroup G}
    (hL33 : ∀ D : Subgroup G, D ≤ Q → IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
      ¬ ∃ S : Finset (Subgroup G), S.card = 3 ∧ ∀ L ∈ S, L ≤ D ∧ Nat.card L = 3 ∧
        ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom)
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hxQ : x ∈ Q) (hK₀Q : K₀ ≤ Q)
    (hK₀C : K₀ ≤ centralizer ({x} : Set G)) (hK₀el : IsElemAbelian 3 K₀)
    (hK₀card : Nat.card K₀ = 3 ^ 2) (hxK₀ : x ∉ K₀)
    (hK₀tr : ∀ a ∈ K₀, ∀ b ∈ K₀, a ≠ 1 → b ≠ 1 → ∃ n ∈ centralizer ({x} : Set G),
      n ∈ normalizer (K₀ : Set G) ∧ n * a * n⁻¹ = b) :
    ∀ y ∈ K₀ ⊔ zpowers x, (∃ g : G, g * x * g⁻¹ = y) → y ∈ zpowers x := by
  rintro y hyE ⟨g, hg⟩
  by_contra hyx
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hCz := p34_centralizer_zpowers x
  have hK₀z : ∀ k ∈ K₀, k ∈ centralizer ((zpowers x : Subgroup G) : Set G) := fun k hk => by
    rw [hCz]; exact hK₀C hk
  have hK₀N : K₀ ≤ normalizer ((zpowers x : Subgroup G) : Set G) := fun k hk =>
    Subgroup.centralizer_le_normalizer ((zpowers x : Subgroup G) : Set G) (hK₀z k hk)
  have hyE' : y ∈ ((K₀ ⊔ zpowers x : Subgroup G) : Set G) := hyE
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K₀ (zpowers x) hK₀N] at hyE'
  obtain ⟨k, hk, u, hu, rfl⟩ := hyE'
  replace hyx : k * u ∉ zpowers x := hyx
  replace hg : g * x * g⁻¹ = k * u := hg
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hyx (by simpa using hu)
  have hk3 : k ^ 3 = 1 := hK₀el.2 k hk
  have hko : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  have hkx : k ∉ zpowers x := fun hkz => by
    have := p34_zpowers_eq_of_mem hxo hkz hk1
    exact hxK₀ (zpowers_le.mpr hk (this ▸ mem_zpowers x))
  have hku : k * u = u * k := (mem_centralizer_iff.mp (hK₀z k hk) u hu).symm
  have hu3 : u ^ 3 = 1 := (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3).2 u hu
  have hconjN : ∀ k' ∈ K₀, k' ≠ 1 → ∃ h : G, h * x * h⁻¹ = k' * u := by
    intro k' hk' hk'1
    obtain ⟨n, hnC, -, hnk⟩ := hK₀tr k hk k' hk' hk1 hk'1
    refine ⟨n * g, ?_⟩
    have hnu : n * u = u * n := (mem_centralizer_iff.mp (hCz ▸ hnC) u hu).symm
    have h2 : n * u * n⁻¹ = u := mul_inv_eq_iff_eq_mul.mpr hnu
    calc n * g * x * (n * g)⁻¹ = n * (g * x * g⁻¹) * n⁻¹ := by group
      _ = n * (k * u) * n⁻¹ := by rw [hg]
      _ = (n * k * n⁻¹) * (n * u * n⁻¹) := by group
      _ = k' * u := by rw [hnk, h2]
  by_cases hu1 : u = 1
  ·
    subst hu1
    obtain ⟨k₂, hk₂, hk₂n⟩ : ∃ k₂ ∈ K₀, k₂ ∉ zpowers k := by
      by_contra hno
      push Not at hno
      have h1 : K₀ ≤ zpowers k := fun z hz => hno z hz
      have h2 := Subgroup.card_le_of_le h1
      rw [hK₀card, Nat.card_zpowers, hko] at h2
      omega
    have hk₂1 : k₂ ≠ 1 := fun h => hk₂n (h ▸ one_mem _)
    have hk₂o : orderOf k₂ = 3 := orderOf_eq_prime (hK₀el.2 k₂ hk₂) hk₂1
    have hkk₂ : k * k₂ ∈ K₀ := K₀.mul_mem hk hk₂
    have hkk₂n : k * k₂ ∉ zpowers k := fun h => hk₂n ((Subgroup.mul_mem_cancel_left _
      (mem_zpowers k)).mp h)
    have hkk₂1 : k * k₂ ≠ 1 := fun h => hk₂n (by
      rw [eq_inv_of_mul_eq_one_right h]; exact inv_mem (mem_zpowers k))
    refine p34_false_of_three_lines hL33 hK₀Q hK₀el hK₀card (y₁ := k) (y₂ := k₂)
      (y₃ := k * k₂) hk hk₂ hkk₂ hk1 hk₂1 hkk₂1 ?_ ?_ ?_ ⟨g, by simpa using hg⟩ ?_ ?_
    · exact fun h => hk₂n (by rw [h]; exact mem_zpowers k₂)
    · exact fun h => hkk₂n (by rw [h]; exact mem_zpowers _)
    · intro h
      have hmem : k * k₂ ∈ zpowers k₂ := by rw [h]; exact mem_zpowers _
      have hk' : k ∈ zpowers k₂ := (Subgroup.mul_mem_cancel_right _ (mem_zpowers k₂)).mp hmem
      have := p34_zpowers_eq_of_mem hk₂o hk' hk1
      exact hk₂n (this ▸ mem_zpowers k₂)
    · obtain ⟨h, hh⟩ := hconjN k₂ hk₂ hk₂1
      exact ⟨h, by simpa using hh⟩
    · obtain ⟨h, hh⟩ := hconjN (k * k₂) hkk₂ hkk₂1
      exact ⟨h, by simpa using hh⟩
  ·
    have huo : orderOf u = 3 := orderOf_eq_prime hu3 hu1
    have hcomm : ∀ e ∈ zpowers x, e * k = k * e := fun e he =>
      (mem_centralizer_iff.mp (hK₀z k hk) e he)
    have hxk : zpowers x ≤ centralizer ((zpowers k : Subgroup G) : Set G) := by
      refine zpowers_le.mpr ?_
      rw [p34_centralizer_zpowers k]
      exact mem_centralizer_singleton_iff.mpr (hcomm x (mem_zpowers x))
    have hDel : IsElemAbelian 3 (zpowers x ⊔ zpowers k) :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3
        (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3)
        (CFSG.AGLEmbedding.isElemAbelian_zpowers hk3) hxk
    have hDcard : Nat.card ↥(zpowers x ⊔ zpowers k) = 3 ^ 2 := by
      rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers x) hk3 hkx
        hcomm, Nat.card_zpowers, hxo]
      norm_num
    have hDQ : zpowers x ⊔ zpowers k ≤ Q :=
      sup_le (zpowers_le.mpr hxQ) (zpowers_le.mpr (hK₀Q hk))
    have hkD : k ∈ zpowers x ⊔ zpowers k := mem_sup_right (mem_zpowers k)
    have huD : u ∈ zpowers x ⊔ zpowers k := mem_sup_left hu
    have hy₂D : k * u ∈ zpowers x ⊔ zpowers k := Subgroup.mul_mem _ hkD huD
    have hy₃D : k⁻¹ * u ∈ zpowers x ⊔ zpowers k := Subgroup.mul_mem _ (inv_mem hkD) huD
    have hy₂1 : k * u ≠ 1 := fun h => hyx (h ▸ one_mem _)
    have hy₂o : orderOf (k * u) = 3 := orderOf_eq_prime (hDel.2 _ hy₂D) hy₂1
    have hkxi : k⁻¹ ∉ zpowers x := fun h => hkx (by simpa using inv_mem h)
    have hy₃x : k⁻¹ * u ∉ zpowers x := fun h =>
      hkxi ((Subgroup.mul_mem_cancel_right _ hu).mp h)
    have hy₃1 : k⁻¹ * u ≠ 1 := fun h => hy₃x (h ▸ one_mem _)
    have huu1 : u * u ≠ 1 := fun h => hu1 (by
      calc u = u ^ 3 * (u * u)⁻¹ := by group
        _ = 1 := by rw [hu3, h]; simp)
    have huu : (k * u) * (k⁻¹ * u) = u * u := by
      calc (k * u) * (k⁻¹ * u) = (u * k) * (k⁻¹ * u) := by rw [hku]
        _ = u * u := by group
    refine p34_false_of_three_lines hL33 hDQ hDel hDcard (y₁ := x) (y₂ := k * u)
      (y₃ := k⁻¹ * u) (mem_sup_left (mem_zpowers x)) hy₂D hy₃D hx1 hy₂1 hy₃1 ?_ ?_ ?_
      ⟨1, by simp⟩ ⟨g, hg⟩ (hconjN k⁻¹ (K₀.inv_mem hk) (inv_ne_one.mpr hk1))
    · exact fun h => hyx (by rw [h]; exact mem_zpowers _)
    · exact fun h => hy₃x (by rw [h]; exact mem_zpowers _)
    · intro h
      have hmem : k⁻¹ * u ∈ zpowers (k * u) := by rw [h]; exact mem_zpowers _
      have h1 : u * u ∈ zpowers (k * u) := by
        rw [← huu]; exact Subgroup.mul_mem _ (mem_zpowers _) hmem
      have h2 := p34_zpowers_eq_of_mem hy₂o h1 huu1
      have h3 := p34_zpowers_eq_of_mem hxo (Subgroup.mul_mem _ hu hu) huu1
      exact hyx (by rw [← h3, h2]; exact mem_zpowers _)

end CFSG.LocalAnalysis.RankThreeTheoremC

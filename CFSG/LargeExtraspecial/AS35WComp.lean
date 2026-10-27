module

public import CFSG.LargeExtraspecial.AS35WDefs

public section

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35W

theorem exists_noncomm_of_perfect {G : Type} [Group G] {N : Subgroup G} (hN : ⁅N, N⁆ = N)
    (hne : N ≠ ⊥) : ∃ a b : N, a * b ≠ b * a := by
  by_contra h
  push Not at h
  apply hne
  rw [← hN, eq_bot_iff, commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩)

theorem not_isPGroup_of_simple {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) : ¬ IsPGroup 2 G := by
  intro h2
  have := hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, hab⟩ := hna
  have hZ := h2.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h3 | h3
  · rw [h3] at hZ
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := hZ
    rw [Subgroup.mem_bot] at hx hy
    exact hxy (Subtype.ext (hx.trans hy.symm))
  · have : a ∈ center G := by rw [h3]; exact Subgroup.mem_top _
    exact hab ((Subgroup.mem_center_iff.1 this b).symm)

variable {X : Type} [Group X] {z : X}

theorem W2Data.false_of_component [Finite X] (h : W2Data X z) (H₀ N : Subgroup X)
    (hH₀ : H₀ ≤ centralizer ({z} : Set X))
    (hH₀n : ∀ c ∈ centralizer ({z} : Set X), ∀ g ∈ H₀, c * g * c⁻¹ ∈ H₀) (hNH : N ≤ H₀)
    (hNn : ∀ c ∈ H₀, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hs : IsSimpleGroup N)
    (hna : ∃ a b : N, a * b ≠ b * a) : False := by
  set R := oTwoCent z
  have hR2 : IsPGroup 2 R := isPGroup_oTwoCent z
  have hRn : ∀ c ∈ centralizer ({z} : Set X), ∀ r ∈ R, c * r * c⁻¹ ∈ R :=
    fun c hc r hr => conj_mem_oTwoCent hc hr
  have hNC : N ≤ centralizer ({z} : Set X) := hNH.trans hH₀
  have hnot := not_isPGroup_of_simple hs hna
  have hNR : ∀ n ∈ N, n ∈ R → n = 1 := by
    have hRN : (R.subgroupOf N).Normal := by
      refine ⟨fun r hr c => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hr ⊢
      simpa using hRn _ (hNC c.2) _ hr
    have := hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf N) with h1 | h1
    · intro n hn hnR
      have : (⟨n, hn⟩ : N) ∈ R.subgroupOf N := hnR
      rw [h1] at this
      exact congrArg Subtype.val ((Subgroup.mem_bot).1 this)
    · exfalso
      apply hnot
      refine hR2.of_injective (Subgroup.inclusion (H := N) (K := R) fun n hn => ?_)
        (Subgroup.inclusion_injective _)
      have : (⟨n, hn⟩ : N) ∈ R.subgroupOf N := by rw [h1]; exact Subgroup.mem_top _
      exact this
  have hcomm₀ : ∀ n ∈ N, ∀ r ∈ R, r ∈ H₀ → n * r = r * n := by
    intro n hn r hr hrH
    have h1 : n * (r * n⁻¹ * r⁻¹) ∈ N := N.mul_mem hn (hNn r hrH n⁻¹ (N.inv_mem hn))
    have h2 : n * r * n⁻¹ * r⁻¹ ∈ R := R.mul_mem (hRn n (hNC hn) r hr) (R.inv_mem hr)
    have e : n * (r * n⁻¹ * r⁻¹) = n * r * n⁻¹ * r⁻¹ := by group
    have h3 := hNR _ h1 (e ▸ h2)
    calc n * r = n * (r * n⁻¹ * r⁻¹) * (r * n) := by group
      _ = r * n := by rw [h3, one_mul]
  have hcomm : ∀ n ∈ N, ∀ r ∈ R, n * r = r * n := by
    intro n₀ hn₀ r hr
    have hφR : ∀ n ∈ N, n * r * n⁻¹ * r⁻¹ ∈ R := fun n hn =>
      R.mul_mem (hRn n (hNC hn) r hr) (R.inv_mem hr)
    have hφH : ∀ n ∈ N, n * r * n⁻¹ * r⁻¹ ∈ H₀ := fun n hn => by
      have e : n * r * n⁻¹ * r⁻¹ = n * (r * n⁻¹ * r⁻¹) := by group
      rw [e]
      exact H₀.mul_mem (hNH hn) (hH₀n r (oTwoCent_le_centralizer z hr) n⁻¹
        (H₀.inv_mem (hNH hn)))
    let ψ : N →* R :=
      { toFun := fun n => ⟨(n * r * n⁻¹ * r⁻¹)⁻¹, R.inv_mem (hφR n n.2)⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro a b
          apply Subtype.ext
          have hb := hcomm₀ a a.2 _ (hφR b b.2) (hφH b b.2)
          simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]
          calc (↑a * ↑b * r * (↑a * ↑b)⁻¹ * r⁻¹)⁻¹ =
              (↑a * (↑b * r * (↑b)⁻¹ * r⁻¹) * (↑a)⁻¹ * (↑a * r * (↑a)⁻¹ * r⁻¹))⁻¹ := by group
            _ = ((↑b * r * (↑b)⁻¹ * r⁻¹) * (↑a * r * (↑a)⁻¹ * r⁻¹))⁻¹ := by
                rw [hb]; group
            _ = (↑a * r * (↑a)⁻¹ * r⁻¹)⁻¹ * (↑b * r * (↑b)⁻¹ * r⁻¹)⁻¹ := by group }
    have := hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with hk | hk
    · exact absurd (hR2.of_injective ψ ((MonoidHom.ker_eq_bot_iff ψ).1 hk)) hnot
    · have hmem : (⟨n₀, hn₀⟩ : N) ∈ ψ.ker := by rw [hk]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hmem
      have h1 : (n₀ * r * n₀⁻¹ * r⁻¹)⁻¹ = 1 := congrArg Subtype.val hmem
      have h2 : n₀ * r * n₀⁻¹ * r⁻¹ = 1 := inv_eq_one.1 h1
      calc n₀ * r = n₀ * r * n₀⁻¹ * r⁻¹ * (r * n₀) := by group
        _ = r * n₀ := by rw [h2, one_mul]
  obtain ⟨a, b, hab⟩ := hna
  have hNR' : ∀ n ∈ N, n = 1 := fun n hn =>
    hNR n hn (h.selfCentralizing n (hNC hn) fun r hr => hcomm n hn r hr)
  have ha : a = 1 := Subtype.ext (hNR' _ a.2)
  have hb : b = 1 := Subtype.ext (hNR' _ b.2)
  exact hab (by rw [ha, hb])

end AS35W

end CFSG.LargeExtraspecial

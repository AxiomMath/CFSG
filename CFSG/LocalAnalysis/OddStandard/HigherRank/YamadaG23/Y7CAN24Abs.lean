module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem n24_index_two {G : Type*} [Group G] (H K : Subgroup G) (hs : IsSimpleGroup ↥H)
    (hnc : ¬ ∀ x y : ↥H, x * y = y * x)
    (h : ∀ x ∈ H, ∀ y ∈ H, x ∉ K → y ∉ K → x * y ∈ K) : H ≤ K := by
  let K' : Subgroup ↥H := K.subgroupOf H
  have hK'normal : K'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    by_cases hg : (g : G) ∈ K
    · have hmem : (g : G) * (n : G) * (g : G)⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem hg hn) (K.inv_mem hg)
      simpa using hmem
    · have hgnK : (g : G) * (n : G) ∉ K := by
        intro hmem
        apply hg
        have heq : (g : G) = (g : G) * (n : G) * (n : G)⁻¹ := by group
        rw [heq]
        exact K.mul_mem hmem (K.inv_mem hn)
      have hginvK : (g : G)⁻¹ ∉ K := by
        intro hmem
        exact hg (by simpa using K.inv_mem hmem)
      have hmem := h ((g : G) * (n : G)) (H.mul_mem g.property n.property) (g : G)⁻¹
        (H.inv_mem g.property) hgnK hginvK
      simpa using hmem
  haveI : K'.Normal := hK'normal
  rcases hs.eq_bot_or_eq_top_of_normal K' with hbot | htop
  · exfalso
    obtain ⟨x, hx⟩ := not_forall.mp hnc
    obtain ⟨y, hxy⟩ := not_forall.mp hx
    have mem_one : ∀ g : ↥H, (g : G) ∈ K → g = 1 := by
      intro g hg
      have hg' : g ∈ K' := hg
      rw [hbot] at hg'
      simpa using hg'
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hxy (by simp)
    have hy1 : y ≠ 1 := by
      rintro rfl
      exact hxy (by simp)
    have hxyK : ((x * y : ↥H) : G) ∈ K := by
      have := h (x : G) x.property (y : G) y.property
        (fun hmem => hx1 (mem_one x hmem)) (fun hmem => hy1 (mem_one y hmem))
      simpa using this
    have hyxK : ((y * x : ↥H) : G) ∈ K := by
      have := h (y : G) y.property (x : G) x.property
        (fun hmem => hy1 (mem_one y hmem)) (fun hmem => hx1 (mem_one x hmem))
      simpa using this
    exact hxy ((mem_one (x * y) hxyK).trans (mem_one (y * x) hyxK).symm)
  · intro x hx
    have : (⟨x, hx⟩ : ↥H) ∈ K' := by rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this

theorem n24_two_homs {G : Type*} [Group G] (H : Subgroup G) (hs : IsSimpleGroup ↥H)
    (ρ₁ ρ₂ : ↥H →* GL (Fin 3) (ZMod 2)) (h : ∀ x : ↥H, ρ₁ x = 1 → ρ₂ x = 1 → x = 1) :
    Nat.card ↥H ∣ 168 := by
  rcases hs.eq_bot_or_eq_top_of_normal ρ₁.ker with hbot | htop
  · have hinj : Function.Injective ρ₁ := (MonoidHom.ker_eq_bot_iff ρ₁).mp hbot
    exact CFSG.ComponentClassification.GHarris.card_GL32_gh ▸
      Subgroup.card_dvd_of_injective ρ₁ hinj
  · have hρ₁ : ∀ x : ↥H, ρ₁ x = 1 := by
      intro x
      have : x ∈ ρ₁.ker := by rw [htop]; exact Subgroup.mem_top x
      simpa using (MonoidHom.mem_ker.mp this)
    have hker : ρ₂.ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      exact h x (hρ₁ x) (MonoidHom.mem_ker.mp hx)
    have hinj : Function.Injective ρ₂ := (MonoidHom.ker_eq_bot_iff ρ₂).mp hker
    exact CFSG.ComponentClassification.GHarris.card_GL32_gh ▸
      Subgroup.card_dvd_of_injective ρ₂ hinj

theorem n24_odd_contra {G : Type*} [Group G] (H : Subgroup G) (hs : IsSimpleGroup ↥H)
    (hnc : ¬ ∀ x y : ↥H, x * y = y * x) (c : G) (hc1 : c ≠ 1) (hcH : c ∈ H)
    (hn : ∀ h ∈ H, h * c * h⁻¹ = c ∨ h * c * h⁻¹ = c⁻¹) : False := by
  let K : Subgroup G := Subgroup.centralizer {c}
  have hK : ∀ x ∈ H, ∀ y ∈ H, x ∉ K → y ∉ K → x * y ∈ K := by
    intro x hxH y hyH hxK hyK
    have hx2 : x * c * x⁻¹ = c⁻¹ := by
      rcases hn x hxH with h1 | h1
      · exact absurd (Subgroup.mem_centralizer_singleton_iff.mpr
          ((mul_inv_eq_iff_eq_mul).mp h1)) hxK
      · exact h1
    have hy2 : y * c * y⁻¹ = c⁻¹ := by
      rcases hn y hyH with h1 | h1
      · exact absurd (Subgroup.mem_centralizer_singleton_iff.mpr
          ((mul_inv_eq_iff_eq_mul).mp h1)) hyK
      · exact h1
    have hxinv : x * c⁻¹ * x⁻¹ = c := by
      have := congrArg (·⁻¹) hx2
      simpa [mul_inv_rev, mul_assoc] using this
    have hxy2 : (x * y) * c * (x * y)⁻¹ = c := by
      calc (x * y) * c * (x * y)⁻¹ = x * (y * c * y⁻¹) * x⁻¹ := by group
        _ = x * c⁻¹ * x⁻¹ := by rw [hy2]
        _ = c := hxinv
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((mul_inv_eq_iff_eq_mul).mp hxy2)
  have hHK : H ≤ K := n24_index_two H K hs hnc hK
  have hcZ : (⟨c, hcH⟩ : ↥H) ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro h
    have hcomm : (h : G) * c = c * (h : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hHK h.property)
    exact Subtype.ext (by simpa using hcomm)
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥H) with hbot | htop
  · have : (⟨c, hcH⟩ : ↥H) = 1 := by
      rw [hbot] at hcZ
      simpa using hcZ
    exact hc1 (by simpa using congrArg Subtype.val this)
  · exact hnc fun x y => by
      have hxZ : x ∈ Subgroup.center ↥H := by rw [htop]; exact Subgroup.mem_top x
      exact ((Subgroup.mem_center_iff.mp hxZ) y).symm

theorem n24_sup_elems {G : Type*} [Group G] (H : Subgroup G) (z : G) (hz : z * z = 1)
    (hzH : ∀ h ∈ H, z * h * z⁻¹ ∈ H) {x : G} (hx : x ∈ H ⊔ Subgroup.zpowers z) :
    x ∈ H ∨ ∃ h ∈ H, x = h * z := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  let S : Subgroup G :=
    { carrier := {x | x ∈ H ∨ ∃ h ∈ H, x = h * z}
      mul_mem' := by
        intro a b ha hb
        rcases ha with haH | ⟨h1, hh1, rfl⟩
        · rcases hb with hbH | ⟨h2, hh2, rfl⟩
          · exact Or.inl (H.mul_mem haH hbH)
          · exact Or.inr ⟨a * h2, H.mul_mem haH hh2, by rw [mul_assoc]⟩
        · rcases hb with hbH | ⟨h2, hh2, rfl⟩
          · exact Or.inr ⟨h1 * (z * b * z⁻¹), H.mul_mem hh1 (hzH b hbH), by group⟩
          · refine Or.inl ?_
            rw [show (h1 * z) * (h2 * z) = h1 * (z * h2 * z⁻¹) by rw [hzinv]; group]
            exact H.mul_mem hh1 (hzH h2 hh2)
      one_mem' := Or.inl H.one_mem
      inv_mem' := by
        intro a ha
        rcases ha with haH | ⟨h, hh, rfl⟩
        · exact Or.inl (H.inv_mem haH)
        · refine Or.inr ⟨z * h⁻¹ * z⁻¹, hzH h⁻¹ (H.inv_mem hh), ?_⟩
          calc (h * z)⁻¹ = z⁻¹ * h⁻¹ := by rw [mul_inv_rev]
            _ = z * h⁻¹ := by rw [hzinv]
            _ = (z * h⁻¹ * z⁻¹) * z := by group }
  have hsup : H ⊔ Subgroup.zpowers z ≤ S :=
    sup_le (fun a ha => Or.inl ha) (Subgroup.zpowers_le.mpr (Or.inr ⟨1, H.one_mem, by simp⟩))
  exact hsup hx

theorem n24_odd_mem {G : Type*} [Group G] (H : Subgroup G) (z c : G) (hz : z * z = 1)
    (hzH : ∀ h ∈ H, z * h * z⁻¹ ∈ H) (hc : c ∈ H ⊔ Subgroup.zpowers z) (hc3 : c ^ 3 = 1) :
    c ∈ H := by
  rcases n24_sup_elems H z hz hzH hc with hcH | ⟨h, hhH, hceq⟩
  · exact hcH
  · subst c
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
    have hc2H : (h * z) ^ 2 ∈ H := by
      have heq : (h * z) ^ 2 = h * (z * h * z⁻¹) := by
        rw [pow_two, hzinv]
        group
      rw [heq]
      exact H.mul_mem hhH (hzH h hhH)
    have hcz : h * z = ((h * z) ^ 2)⁻¹ := by
      have h3 : (h * z) ^ 2 * (h * z) = 1 := by rw [← pow_succ]; exact hc3
      exact (inv_eq_of_mul_eq_one_right h3).symm
    rw [hcz]
    exact H.inv_mem hc2H

end CFSG.OddStandard.HigherRank.YamadaG23

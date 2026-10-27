module

public import CFSG.LocalAnalysis.SeitzReduction.Endgame
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSylowUnique

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup

variable {G : Type*} [Group G]

theorem mem_normalizer_iff_map_conj_toMonoidHom {H : Subgroup G} {g : G} :
    g ∈ normalizer (H : Set G) ↔ H.map (MulAut.conj g).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq

theorem map_conj_map_conj_toMonoidHom (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one_toMonoidHom (H : Subgroup G) :
    H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  ext x
  simp

theorem map_conj_toMonoidHom_inj {H K : Subgroup G} {g : G} :
    H.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj g).toMonoidHom ↔ H = K :=
  (Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).eq_iff

theorem map_conj_eq_of_map_conj_inv_eq {H K : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g⁻¹).toMonoidHom = K) : K.map (MulAut.conj g).toMonoidHom = H := by
  rw [← h, map_conj_map_conj_toMonoidHom, mul_inv_cancel, map_conj_one_toMonoidHom]

variable {G₁ G₂ : Subgroup G} {t : G}

theorem map_conj_symm_of_involution (htt : t * t = 1)
    (hswap : G₁.map (MulAut.conj t).toMonoidHom = G₂) :
    G₂.map (MulAut.conj t).toMonoidHom = G₁ := by
  rw [← hswap, map_conj_map_conj_toMonoidHom, htt, map_conj_one_toMonoidHom]

theorem mem_normalizer_sup_of_map_conj_eq (htt : t * t = 1)
    (hswap : G₁.map (MulAut.conj t).toMonoidHom = G₂) :
    t ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_toMonoidHom, Subgroup.map_sup, hswap,
    map_conj_symm_of_involution htt hswap, sup_comm]

theorem notMem_normalizer_of_map_conj_eq_of_ne (hswap : G₁.map (MulAut.conj t).toMonoidHom = G₂)
    (hne : G₁ ≠ G₂) : t ∉ normalizer (G₁ : Set G) := fun h =>
  hne ((mem_normalizer_iff_map_conj_toMonoidHom.1 h).symm.trans hswap)

section Perm

variable (htt : t * t = 1) (hswap : G₁.map (MulAut.conj t).toMonoidHom = G₂) (hne : G₁ ≠ G₂)
  (hperm : ∀ g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G),
    G₁.map (MulAut.conj g).toMonoidHom = G₁ ∨ G₁.map (MulAut.conj g).toMonoidHom = G₂)
include htt hswap hne hperm

theorem mem_normalizer_or_mul_mem_normalizer_of_swap {g : G}
    (hg : g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    g ∈ normalizer (G₁ : Set G) ∨ g * t ∈ normalizer (G₁ : Set G) := by
  rcases hperm g hg with h | h
  · exact Or.inl (mem_normalizer_iff_map_conj_toMonoidHom.2 h)
  · right
    rw [mem_normalizer_iff_map_conj_toMonoidHom]
    have hgt := hperm (g * t) (mul_mem hg (mem_normalizer_sup_of_map_conj_eq htt hswap))
    rw [← map_conj_map_conj_toMonoidHom, hswap] at hgt ⊢
    rcases hgt with h' | h'
    · exact h'
    · exact absurd (map_conj_toMonoidHom_inj.1 (h.trans h'.symm)) hne

theorem mem_normalizer_right_of_swap {g : G}
    (hg : g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) (hg₁ : g ∈ normalizer (G₁ : Set G)) :
    g ∈ normalizer (G₂ : Set G) := by
  rw [mem_normalizer_iff_map_conj_toMonoidHom] at hg₁ ⊢
  have hgt := hperm (g * t) (mul_mem hg (mem_normalizer_sup_of_map_conj_eq htt hswap))
  rw [← map_conj_map_conj_toMonoidHom, hswap] at hgt
  rcases hgt with h' | h'
  · exact absurd (map_conj_toMonoidHom_inj.1 (h'.trans hg₁.symm)).symm hne
  · exact h'

theorem conj_mem_inf_normalizer_of_swap {m y : G}
    (hm : m ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))
    (hy : y ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) ⊓ normalizer (G₁ : Set G)) :
    m * y * m⁻¹ ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) ⊓ normalizer (G₁ : Set G) := by
  rw [mem_inf] at hy ⊢
  refine ⟨mul_mem (mul_mem hm hy.1) (inv_mem hm), ?_⟩
  have hy₁ := mem_normalizer_iff_map_conj_toMonoidHom.1 hy.2
  have hy₂ := mem_normalizer_iff_map_conj_toMonoidHom.1
    (mem_normalizer_right_of_swap htt hswap hne hperm hy.1 hy.2)
  rw [mem_normalizer_iff_map_conj_toMonoidHom, ← map_conj_map_conj_toMonoidHom,
    ← map_conj_map_conj_toMonoidHom]
  rcases hperm m⁻¹ (inv_mem hm) with h | h
  · rw [h, hy₁]
    exact map_conj_eq_of_map_conj_inv_eq h
  · rw [h, hy₂]
    exact map_conj_eq_of_map_conj_inv_eq h

theorem mem_normalizer_inf_normalizer_of_swap :
    t ∈ normalizer (((normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) ⊓ normalizer (G₁ : Set G) :
      Subgroup G)) : Set G) := by
  have ht₀ := mem_normalizer_sup_of_map_conj_eq htt hswap
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact conj_mem_inf_normalizer_of_swap htt hswap hne hperm ht₀
  · intro hy
    have h := conj_mem_inf_normalizer_of_swap htt hswap hne hperm (inv_mem ht₀) hy
    have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
    rwa [e] at h

theorem normalizer_sup_le_sup_zpowers_of_swap :
    normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) ≤
      (normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) ⊓ normalizer (G₁ : Set G)) ⊔ zpowers t := by
  intro g hg
  rcases mem_normalizer_or_mul_mem_normalizer_of_swap htt hswap hne hperm hg with h | h
  · exact mem_sup_left ⟨hg, h⟩
  · have e : g = g * t * t⁻¹ := by group
    rw [e]
    exact mul_mem (mem_sup_left ⟨mul_mem hg (mem_normalizer_sup_of_map_conj_eq htt hswap), h⟩)
      (mem_sup_right (inv_mem (mem_zpowers t)))

theorem relIndex_inf_normalizer_eq_two_of_swap :
    (normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) ⊓ normalizer (G₁ : Set G)).relIndex
      (normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) = 2 := by
  have h := CFSG.SeitzReduction.relIndex_inf_eq_two htt
    (mem_normalizer_inf_normalizer_of_swap htt hswap hne hperm)
    (fun h => notMem_normalizer_of_map_conj_eq_of_ne hswap hne h.2)
    (normalizer_sup_le_sup_zpowers_of_swap htt hswap hne hperm)
    (mem_normalizer_sup_of_map_conj_eq htt hswap)
  rwa [← inf_assoc, inf_idem] at h

theorem inf_normalizer_eq_of_swap :
    normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) ⊓ normalizer (G₁ : Set G) =
      normalizer (G₁ : Set G) ⊓ normalizer (G₂ : Set G) := by
  apply le_antisymm
  · intro g hg
    rw [mem_inf] at hg ⊢
    exact ⟨hg.2, mem_normalizer_right_of_swap htt hswap hne hperm hg.1 hg.2⟩
  · intro g hg
    rw [mem_inf] at hg ⊢
    obtain ⟨hg₁, hg₂⟩ := hg
    refine ⟨?_, hg₁⟩
    rw [mem_normalizer_iff_map_conj_toMonoidHom, Subgroup.map_sup,
      mem_normalizer_iff_map_conj_toMonoidHom.1 hg₁, mem_normalizer_iff_map_conj_toMonoidHom.1 hg₂]

end Perm

theorem exists_normal_index_two_of_swap [Finite G] (ht : orderOf t = 2)
    (hswap : G₁.map (MulAut.conj t).toMonoidHom = G₂) (hne : G₁ ≠ G₂)
    (hperm : ∀ g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G),
      G₁.map (MulAut.conj g).toMonoidHom = G₁ ∨ G₁.map (MulAut.conj g).toMonoidHom = G₂)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht₀ := mem_normalizer_sup_of_map_conj_eq htt hswap
  have htY : t ∉ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) ⊓ normalizer (G₁ : Set G) :=
    fun h => notMem_normalizer_of_map_conj_eq_of_ne hswap hne h.2
  obtain ⟨-, ⟨S, hS⟩, -, -⟩ := centralizer_le_and_sylow_le_of_unique ht ht₀ huniq
  refine CFSG.SeitzReduction.exists_normal_index_two_of_not_fused_of_sylow_le ht
    (mem_normalizer_inf_normalizer_of_swap htt hswap hne hperm) htY
    ⟨S, hS.trans (normalizer_sup_le_sup_zpowers_of_swap htt hswap hne hperm)⟩ (fun g hg => ?_)
  have h := conj_mem_inf_normalizer_of_swap htt hswap hne hperm (huniq g hg.1) hg
  have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
  rw [e] at h
  exact htY h

theorem false_of_simple_of_swap [Finite G] [IsSimpleGroup G] (ht : orderOf t = 2)
    (hswap : G₁.map (MulAut.conj t).toMonoidHom = G₂) (hne : G₁ ≠ G₂)
    (hperm : ∀ g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G),
      G₁.map (MulAut.conj g).toMonoidHom = G₁ ∨ G₁.map (MulAut.conj g).toMonoidHom = G₂)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) : False := by
  obtain ⟨N, hN, hidx⟩ := exists_normal_index_two_of_swap ht hswap hne hperm huniq
  rcases hN.eq_bot_or_eq_top with rfl | rfl
  · rw [index_bot] at hidx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic G := isCyclic_of_prime_card hidx
    have hcomm : ∀ a b : G, a * b = b * a := fun a b =>
      (IsCyclic.isMulCommutative (α := G)).is_comm.comm a b
    apply hne
    rw [← hswap]
    ext x
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hx
      exact ⟨x, hx, by rw [hcomm t x, mul_inv_cancel_right]⟩
    · rintro ⟨y, hy, rfl⟩
      rwa [hcomm t y, mul_inv_cancel_right]
  · rw [index_top] at hidx
    omega

theorem eq_or_le_centralizer_of_isSimpleGroup {A N : Subgroup G} (hsA : IsSimpleGroup A)
    (hsN : IsSimpleGroup N) (hAN : A ≤ normalizer (N : Set G))
    (hNA : N ≤ normalizer (A : Set G)) : N = A ∨ N ≤ centralizer (A : Set G) := by
  have hnorm : (A.subgroupOf N).Normal :=
    ⟨fun a ha n => by
      rw [mem_subgroupOf] at ha ⊢
      exact (mem_normalizer_iff.1 (hNA n.2) a).1 ha⟩
  have := hsN
  rcases hnorm.eq_bot_or_eq_top with h | h
  ·
    right
    rw [subgroupOf_eq_bot] at h
    intro n hn
    rw [mem_centralizer_iff]
    intro a ha
    have hc : n * a * n⁻¹ * a⁻¹ ∈ A ⊓ N := by
      refine mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 (hNA hn) a).1 ha) (inv_mem ha), ?_⟩
      have h1 : a * n⁻¹ * a⁻¹ ∈ N := (mem_normalizer_iff.1 (hAN ha) n⁻¹).1 (inv_mem hn)
      have e : n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) := by group
      rw [e]
      exact mul_mem hn h1
    rw [h.eq_bot] at hc
    have h1 : n * a * n⁻¹ * a⁻¹ = 1 := (mem_bot).1 hc
    have e : a * n = n * a := by
      calc a * n = (n * a * n⁻¹ * a⁻¹)⁻¹ * (n * a) := by group
        _ = n * a := by rw [h1, inv_one, one_mul]
    exact e
  ·
    left
    rw [subgroupOf_eq_top] at h
    have hnorm' : (N.subgroupOf A).Normal :=
      ⟨fun x hx a => by
        rw [mem_subgroupOf] at hx ⊢
        exact (mem_normalizer_iff.1 (hAN a.2) x).1 hx⟩
    have := hsA
    rcases hnorm'.eq_bot_or_eq_top with h' | h'
    · exfalso
      rw [subgroupOf_eq_bot] at h'
      have hbot : N = ⊥ := by
        have := h'.eq_bot
        rwa [inf_eq_left.2 h] at this
      have : Nontrivial N := hsN.toNontrivial
      exact ((nontrivial_iff_ne_bot N).1 this) hbot
    · exact le_antisymm h (subgroupOf_eq_top.1 h')

theorem sup_le_normalizer_left_of_le_centralizer (h₁₂ : G₂ ≤ centralizer (G₁ : Set G)) :
    G₁ ⊔ G₂ ≤ normalizer (G₁ : Set G) :=
  sup_le le_normalizer (h₁₂.trans (centralizer_le_normalizer _))

theorem sup_le_normalizer_right_of_le_centralizer (h₁₂ : G₂ ≤ centralizer (G₁ : Set G)) :
    G₁ ⊔ G₂ ≤ normalizer (G₂ : Set G) :=
  sup_le ((le_centralizer_iff.1 h₁₂).trans (centralizer_le_normalizer _)) le_normalizer

theorem map_conj_le_sup_of_mem_normalizer {g : G}
    (hg : g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    G₁.map (MulAut.conj g).toMonoidHom ≤ G₁ ⊔ G₂ :=
  (map_mono le_sup_left).trans (mem_normalizer_iff_map_conj_toMonoidHom.1 hg).le

theorem sup_le_normalizer_map_conj {g : G} (h : G₁ ⊔ G₂ ≤ normalizer (G₁ : Set G))
    (hg : g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    G₁ ⊔ G₂ ≤ normalizer ((G₁.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_toMonoidHom, map_conj_map_conj_toMonoidHom]
  have hx' : g⁻¹ * x * g ∈ G₁ ⊔ G₂ := (mem_normalizer_iff''.1 hg x).1 hx
  have h1 := mem_normalizer_iff_map_conj_toMonoidHom.1 (h hx')
  have e1 : x * g = g * (g⁻¹ * x * g) := by group
  rw [e1, ← map_conj_map_conj_toMonoidHom, h1]

theorem eq_or_eq_of_isSimpleGroup_of_le_sup {N : Subgroup G}
    (h₁₂ : G₂ ≤ centralizer (G₁ : Set G)) (hs₁ : IsSimpleGroup G₁) (hs₂ : IsSimpleGroup G₂)
    (hsN : IsSimpleGroup N) (hna : ∃ a b : N, a * b ≠ b * a) (hN : N ≤ G₁ ⊔ G₂)
    (hNn : G₁ ⊔ G₂ ≤ normalizer (N : Set G)) : N = G₁ ∨ N = G₂ := by
  rcases eq_or_le_centralizer_of_isSimpleGroup hs₁ hsN (le_sup_left.trans hNn)
    (hN.trans (sup_le_normalizer_left_of_le_centralizer h₁₂)) with h | hc₁
  · exact Or.inl h
  rcases eq_or_le_centralizer_of_isSimpleGroup hs₂ hsN (le_sup_right.trans hNn)
    (hN.trans (sup_le_normalizer_right_of_le_centralizer h₁₂)) with h | hc₂
  · exact Or.inr h
  exfalso
  have hNN : N ≤ centralizer (N : Set G) :=
    hN.trans (sup_le (le_centralizer_iff.1 hc₁) (le_centralizer_iff.1 hc₂))
  obtain ⟨a, b, hab⟩ := hna
  exact hab (Subtype.ext (mem_centralizer_iff.1 (hNN b.2) a a.2))

theorem map_conj_eq_or_eq_of_isSimpleGroup (h₁₂ : G₂ ≤ centralizer (G₁ : Set G))
    (hs₁ : IsSimpleGroup G₁) (hs₂ : IsSimpleGroup G₂) (hna : ∃ a b : G₁, a * b ≠ b * a) {g : G}
    (hg : g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    G₁.map (MulAut.conj g).toMonoidHom = G₁ ∨ G₁.map (MulAut.conj g).toMonoidHom = G₂ := by
  let e : G₁ ≃* G₁.map (MulAut.conj g).toMonoidHom :=
    G₁.equivMapOfInjective _ (MulAut.conj g).injective
  have hsN : IsSimpleGroup (G₁.map (MulAut.conj g).toMonoidHom) := by
    have := hs₁
    exact e.symm.isSimpleGroup
  have hnaN : ∃ a b : G₁.map (MulAut.conj g).toMonoidHom, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
    rw [map_mul, map_mul, h]
  exact eq_or_eq_of_isSimpleGroup_of_le_sup h₁₂ hs₁ hs₂ hsN hnaN
    (map_conj_le_sup_of_mem_normalizer hg)
    (sup_le_normalizer_map_conj (sup_le_normalizer_left_of_le_centralizer h₁₂) hg)

theorem ne_of_le_centralizer_of_exists_ne (h₁₂ : G₂ ≤ centralizer (G₁ : Set G))
    (hna : ∃ a b : G₁, a * b ≠ b * a) : G₁ ≠ G₂ := by
  rintro rfl
  obtain ⟨a, b, hab⟩ := hna
  exact hab (Subtype.ext (mem_centralizer_iff.1 (h₁₂ b.2) a a.2))

theorem false_of_simple_of_swap_of_isSimpleGroup [Finite G] [IsSimpleGroup G] (ht : orderOf t = 2)
    (hs₁ : IsSimpleGroup G₁) (hna : ∃ a b : G₁, a * b ≠ b * a)
    (h₁₂ : G₂ ≤ centralizer (G₁ : Set G)) (hswap : G₁.map (MulAut.conj t).toMonoidHom = G₂)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) : False := by
  have hs₂ : IsSimpleGroup G₂ := by
    have := hs₁
    subst hswap
    exact (G₁.equivMapOfInjective _ (MulAut.conj t).injective).symm.isSimpleGroup
  exact false_of_simple_of_swap ht hswap (ne_of_le_centralizer_of_exists_ne h₁₂ hna)
    (fun g hg => map_conj_eq_or_eq_of_isSimpleGroup h₁₂ hs₁ hs₂ hna hg) huniq

end CFSG.SeitzReduction.F4Pilot

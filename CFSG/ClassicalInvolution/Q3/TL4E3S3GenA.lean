module

public import CFSG.ClassicalInvolution.Q3.TL4E3C269G2A

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3Gen

variable {X P : Type} [Group X] [Group P]

theorem sup_centralizer_eq_top_of_normal {N : Subgroup X} [N.Normal] (e : ↥N ≃* P)
    (hgen : ∀ a b : P, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a ≠ b →
      Subgroup.centralizer ({a} : Set P) ⊔ Subgroup.centralizer ({b} : Set P) = ⊤)
    (hclass : ∀ a b : P, orderOf a = 2 → orderOf b = 2 → ∃ g : P, g * a * g⁻¹ = b)
    {t s : X} (htN : t ∈ N) (hsN : s ∈ N) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hts : t * s = s * t) (hne : s ≠ t) :
    Subgroup.centralizer ({t} : Set X) ⊔ Subgroup.centralizer ({s} : Set X) = ⊤ := by
  have he2 : ∀ y : ↥N, orderOf (y : X) = 2 → orderOf (e y) = 2 := fun y hy => by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, hy]
  have hN : Subgroup.centralizer ({(⟨t, htN⟩ : ↥N)} : Set ↥N) ⊔
      Subgroup.centralizer ({(⟨s, hsN⟩ : ↥N)} : Set ↥N) = ⊤ := by
    refine E3C269G.sup_centralizer_eq_top_of_equiv e
      (hgen _ _ (he2 _ ht) (he2 _ hs) ?_ fun h => hne ?_)
    · rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext hts)
    · exact (congrArg Subtype.val (e.injective h)).symm
  have hNle : N ≤ Subgroup.centralizer ({t} : Set X) ⊔ Subgroup.centralizer ({s} : Set X) := by
    intro n hn
    have hmem : (⟨n, hn⟩ : ↥N) ∈ Subgroup.centralizer ({(⟨t, htN⟩ : ↥N)} : Set ↥N) ⊔
        Subgroup.centralizer ({(⟨s, hsN⟩ : ↥N)} : Set ↥N) := by
      rw [hN]
      exact Subgroup.mem_top _
    have hmap := Subgroup.mem_map_of_mem N.subtype hmem
    rw [Subgroup.map_sup] at hmap
    have hcent : ∀ x : ↥N, (Subgroup.centralizer ({x} : Set ↥N)).map N.subtype ≤
        Subgroup.centralizer ({(x : X)} : Set X) := by
      rintro x _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hc
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc)
    exact sup_le_sup (hcent ⟨t, htN⟩) (hcent ⟨s, hsN⟩) hmap
  have hF := E3C269G2.le_sup_centralizer_of_conj htN ht fun y hyN hy => by
    obtain ⟨g, hg⟩ := hclass (e ⟨t, htN⟩) (e ⟨y, hyN⟩) (he2 _ ht) (he2 _ hy)
    refine ⟨(e.symm g : X), (e.symm g).2, ?_⟩
    have h1 : e.symm g * ⟨t, htN⟩ * (e.symm g)⁻¹ = ⟨y, hyN⟩ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]
    exact congrArg Subtype.val h1
  rw [eq_top_iff]
  exact hF.trans (sup_le hNle le_sup_left)

end CFSG.ClassicalInvolution.Q3.TL4.E3S3Gen

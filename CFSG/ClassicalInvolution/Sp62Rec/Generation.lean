module

public import CFSG.ClassicalInvolution.Sp62Rec.Pkg

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

variable {G : Type*} [Group G]

theorem normalizer_le_centralizer_of_centralizer_le {E : Subgroup G} {e : G}
    (hC : Subgroup.centralizer (E : Set G) ≤ Subgroup.zpowers e)
    (he : e ∈ Subgroup.centralizer (E : Set G)) (he2 : e * e = 1) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.centralizer ({e} : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hconj : n * e * n⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) x).mp hx
    rw [inv_inv] at hx'
    have h := Subgroup.mem_centralizer_iff.mp he _ hx'
    calc x * (n * e * n⁻¹) = n * ((n⁻¹ * x * n) * e) * n⁻¹ := by group
      _ = n * (e * (n⁻¹ * x * n)) * n⁻¹ := by rw [h]
      _ = n * e * n⁻¹ * x := by group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hC hconj)
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have hpow : ∀ k : ℤ, e ^ k = 1 ∨ e ^ k = e := by
    intro k
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, zpow_two, he2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, he2, one_zpow, one_mul, zpow_one]
  rcases hpow k with h1 | h1
  ·
    rw [h1] at hk
    have he1 : e = 1 := by
      have : n⁻¹ * (n * e * n⁻¹) * n = n⁻¹ * 1 * n := by rw [hk]
      simpa [mul_assoc] using this
    rw [he1, one_mul, mul_one]
  · rw [h1] at hk
    calc n * e = (n * e * n⁻¹) * n := by group
      _ = e * n := by rw [← hk]

theorem sup_normalizer_centralizer_eq_top {E A : Subgroup G} {e : G}
    (hgen : ∀ n : G, E.map (MulAut.conj n).toMonoidHom ≠ E →
      E ⊔ E.map (MulAut.conj n).toMonoidHom = ⊤)
    (hEe : E ≤ Subgroup.centralizer ({e} : Set G))
    (hNE : Subgroup.normalizer (E : Set G) ≤ Subgroup.centralizer ({e} : Set G))
    {n : G} (hnA : n ∈ Subgroup.normalizer (A : Set G))
    (hne : n ∉ Subgroup.centralizer ({e} : Set G)) :
    Subgroup.normalizer (A : Set G) ⊔ Subgroup.centralizer ({e} : Set G) = ⊤ := by
  have hn : E.map (MulAut.conj n).toMonoidHom ≠ E := by
    intro h
    apply hne
    apply hNE
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hm : (MulAut.conj n).toMonoidHom x ∈ E.map (MulAut.conj n).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [h] at hm
      simpa [MulAut.conj_apply] using hm
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : n * y * n⁻¹ = n * x * n⁻¹ := by simpa [MulAut.conj_apply] using hyx
      have : y = x := by simpa using hyx'
      rw [← this]
      exact hy
  rw [eq_top_iff, ← hgen n hn]
  apply sup_le
  · exact hEe.trans le_sup_right
  · rintro _ ⟨y, hy, rfl⟩
    have hn' : n ∈ Subgroup.normalizer (A : Set G) ⊔ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_sup_left hnA
    have hy' : y ∈ Subgroup.normalizer (A : Set G) ⊔ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_sup_right (hEe hy)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hn' hy') (inv_mem hn')

open CFSG.ClassicalInvolution.Solomon73.Yamaki in
theorem E8ZPkg.sup_normalizer_centralizer_eq_top
    {G : Type} [Group G] [Finite G] {z e : G} {E B : Subgroup G} {T : Sylow 2 G}
    {A X : Subgroup G} (P : E8ZPkg z e E B T A X)
    (hC : Subgroup.centralizer (E : Set G) ≤ Subgroup.zpowers e) (he2 : e * e = 1)
    {n : G} (hnA : n ∈ Subgroup.normalizer (A : Set G))
    (hne : n ∉ Subgroup.centralizer ({e} : Set G)) :
    Subgroup.normalizer (A : Set G) ⊔ Subgroup.centralizer ({e} : Set G) = ⊤ := by
  have hEe : E ≤ Subgroup.centralizer ({e} : Set G) := P.E_le_B.trans P.B_le
  have he : e ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hEe hx)
  exact CFSG.ClassicalInvolution.Sp62Rec.sup_normalizer_centralizer_eq_top P.gen hEe
    (normalizer_le_centralizer_of_centralizer_le hC he he2) hnA hne

end CFSG.ClassicalInvolution.Sp62Rec

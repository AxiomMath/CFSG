module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Layer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem l515S_conj_eq_of_comm {a x : G} (h : a * x = x * a) : a⁻¹ * x * a = x := by
  calc a⁻¹ * x * a = a⁻¹ * (x * a) := mul_assoc _ _ _
    _ = a⁻¹ * (a * x) := by rw [h]
    _ = x := inv_mul_cancel_left a x

theorem l515S_idx {i i' j j' : Fin 4} (hi : (i = 0 ∧ i' = 1) ∨ (i = 1 ∧ i' = 0))
    (hj : (j = 2 ∧ j' = 3) ∨ (j = 3 ∧ j' = 2)) :
    i ≠ j ∧ i ≠ j' ∧ i' ≠ j ∧ i' ≠ j' ∧ i ≠ i' ∧ j ≠ j' := by
  rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem l515S_exists_ne_ne : ∀ i j : Fin 4, ∃ l : Fin 4, l ≠ i ∧ l ≠ j := by
  decide

section Quad

variable {K : Fin 4 → Subgroup G} {z : G}

theorem Sec5B517Quad.mem_normalizer_pair (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j)
    {y : G} (hy : y ∈ K i ⊔ K j) : y ∈ normalizer (K i : Set G) := by
  have hKi : K i ≤ normalizer (K i : Set G) := Subgroup.le_normalizer
  have hKj : K j ≤ normalizer (K i : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (K i : Set G))
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hq.comm j i hij.symm x hx w hw).symm
  exact (sup_le hKi hKj) hy

theorem Sec5B517Quad.conjugate_eq_of_mem_pair (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j)
    {y : G} (hy : y ∈ K i ⊔ K j) (l : Fin 4) : CFSG.conjugate (K l) y = K l := by
  by_cases hli : l = i
  · subst hli
    exact sec5b513_conjugate_eq_iff.mpr (hq.mem_normalizer_pair hij hy)
  · by_cases hlj : l = j
    · subst hlj
      rw [sup_comm] at hy
      exact sec5b513_conjugate_eq_iff.mpr (hq.mem_normalizer_pair hij.symm hy)
    · exact conjugate_eq_self_of_le_centralizer (hq.le_centralizer_of_mem_pair hli hlj hy)

theorem Sec5B517Quad.conj_z_of_mem_pair (hq : Sec5B517Quad K z) {i j : Fin 4} {y : G}
    (hy : y ∈ K i ⊔ K j) : y⁻¹ * z * y = z := by
  obtain ⟨l, hli, hlj⟩ := l515S_exists_ne_ne i j
  have hmem : z ∈ centralizer ({y} : Set G) := hq.le_centralizer_of_mem_pair hli hlj hy (hq.z_mem l)
  have hzy : z * y = y * z := Subgroup.mem_centralizer_singleton_iff.mp hmem
  exact l515S_conj_eq_of_comm hzy.symm

end Quad

section Ctx

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G} {h : G}

theorem l515S_s_facts (h37 : Asc82Lemma37) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    (h⁻¹ * t * h) * (h⁻¹ * t * h) = 1 ∧ h⁻¹ * t * h ≠ 1 ∧ h⁻¹ * t * h ≠ z := by
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp c.h_z
  refine ⟨?_, ?_, ?_⟩
  · calc (h⁻¹ * t * h) * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
      _ = 1 := by rw [c.t_mul_self]; group
  · intro hs
    apply c.t_ne_one
    calc t = h * (h⁻¹ * t * h) * h⁻¹ := by group
      _ = 1 := by rw [hs]; group
  · intro hs
    apply c.t_ne_z h37
    calc t = h * (h⁻¹ * t * h) * h⁻¹ := by group
      _ = h * z * h⁻¹ := by rw [hs]
      _ = z := by rw [hhz]; group

theorem l515S_adapt (h37 : Asc82Lemma37) (h514 : Asc82Lemma514)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {i i' j j' : Fin 4}
    (hi : (i = 0 ∧ i' = 1) ∨ (i = 1 ∧ i' = 0)) (hj : (j = 2 ∧ j' = 3) ∨ (j = 3 ∧ j' = 2))
    {α β : G} (hα : α ∈ Kfam5 K₁ K₂ h i) (hβ : β ∈ Kfam5 K₁ K₂ h j) (hα2 : α * α = z)
    (hβ2 : β * β = z) :
    ∃ g : G, (g⁻¹ * t * g) * (α * β) = (α * β) * (g⁻¹ * t * g) ∧
      (g⁻¹ * (h⁻¹ * t * h) * g) * (α * β) = (α * β) * (g⁻¹ * (h⁻¹ * t * h) * g) ∧
      g⁻¹ * z * g = z ∧ (∀ l : Fin 4, CFSG.conjugate (Kfam5 K₁ K₂ h l) g = Kfam5 K₁ K₂ h l) ∧
      β * (g⁻¹ * t * g) = (g⁻¹ * t * g) * β ∧
      α * (g⁻¹ * (h⁻¹ * t * h) * g) = (g⁻¹ * (h⁻¹ * t * h) * g) * α := by
  have hq : Sec5B517Quad (Kfam5 K₁ K₂ h) z := sec5b517_quad h514 c
  obtain ⟨hij, hij', hi'j, hi'j', hii', hjj'⟩ := l515S_idx hi hj
  have hK0 : Kfam5 K₁ K₂ h 0 = K₁ := by simp [Kfam5]
  have hK1 : Kfam5 K₁ K₂ h 1 = K₂ := by simp [Kfam5]
  have hK2 : Kfam5 K₁ K₂ h 2 = CFSG.conjugate K₁ h := by simp [Kfam5]
  have hK3 : Kfam5 K₁ K₂ h 3 = CFSG.conjugate K₂ h := by simp [Kfam5]
  obtain ⟨q', hq'K, hq'2⟩ := hq.exists_sq j'
  obtain ⟨ht₁2, ht₁1, ht₁z⟩ := hq.mul_invol hjj' hβ hq'K hβ2 hq'2
  have ht₁mem : β * q' ∈ Kfam5 K₁ K₂ h 2 ⊔ Kfam5 K₁ K₂ h 3 := by
    rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Subgroup.mul_mem_sup hβ hq'K
    · rw [sup_comm]
      exact Subgroup.mul_mem_sup hβ hq'K
  have htmem : t ∈ Kfam5 K₁ K₂ h 2 ⊔ Kfam5 K₁ K₂ h 3 := by
    rw [hK2, hK3]
    exact c.t_mem_sup₃₄
  obtain ⟨y, hy, hyt⟩ := hq.pair_invol_conj (i := 2) (j := 3) (by decide) htmem c.t_mul_self
    c.t_ne_one (c.t_ne_z h37) ht₁mem ht₁2 ht₁1 ht₁z
  obtain ⟨q, hqK, hq2⟩ := hq.exists_sq i'
  obtain ⟨ht₂2, ht₂1, ht₂z⟩ := hq.mul_invol hii' hα hqK hα2 hq2
  have ht₂mem : α * q ∈ Kfam5 K₁ K₂ h 0 ⊔ Kfam5 K₁ K₂ h 1 := by
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Subgroup.mul_mem_sup hα hqK
    · rw [sup_comm]
      exact Subgroup.mul_mem_sup hα hqK
  obtain ⟨hs2, hs1, hsz⟩ := l515S_s_facts h37 c
  have hsmem : h⁻¹ * t * h ∈ Kfam5 K₁ K₂ h 0 ⊔ Kfam5 K₁ K₂ h 1 := by
    rw [hK0, hK1]
    exact c.h_t
  obtain ⟨c₀, hc₀, hc₀s⟩ := hq.pair_invol_conj (i := 0) (j := 1) (by decide) hsmem hs2 hs1 hsz
    ht₂mem ht₂2 ht₂1 ht₂z
  have hj0 : j ≠ 0 ∧ j ≠ 1 ∧ j' ≠ 0 ∧ j' ≠ 1 := by
    rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hαβ : α * β = β * α := hq.comm i j hij α hα β hβ
  have hαq' : α * q' = q' * α := hq.comm i j' hij' α hα q' hq'K
  have hβq' : β * q' = q' * β := hq.comm j j' hjj' β hβ q' hq'K
  have hqβ : q * β = β * q := hq.comm i' j hi'j q hqK β hβ
  have hαq : α * q = q * α := hq.comm i i' hii' α hα q hqK
  have hc₀β : c₀ * β = β * c₀ := by
    have hmem : β ∈ centralizer ({c₀} : Set G) :=
      hq.le_centralizer_of_mem_pair (i := 0) (j := 1) (l := j) hj0.1 hj0.2.1 hc₀ hβ
    exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm
  have hc₀q' : c₀ * q' = q' * c₀ := by
    have hmem : q' ∈ centralizer ({c₀} : Set G) :=
      hq.le_centralizer_of_mem_pair (i := 0) (j := 1) (l := j') hj0.2.2.1 hj0.2.2.2 hc₀ hq'K
    exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm
  have hc₀t₁ : c₀ * (β * q') = (β * q') * c₀ :=
    (Commute.mul_right (show Commute c₀ β from hc₀β) (show Commute c₀ q' from hc₀q')).eq
  have hys : (h⁻¹ * t * h) * y = y * (h⁻¹ * t * h) := by
    have h0 : Kfam5 K₁ K₂ h 0 ≤ centralizer ({y} : Set G) :=
      hq.le_centralizer_of_mem_pair (i := 2) (j := 3) (l := 0) (by decide) (by decide) hy
    have h1 : Kfam5 K₁ K₂ h 1 ≤ centralizer ({y} : Set G) :=
      hq.le_centralizer_of_mem_pair (i := 2) (j := 3) (l := 1) (by decide) (by decide) hy
    exact Subgroup.mem_centralizer_singleton_iff.mp ((sup_le h0 h1) hsmem)
  have hcomm₁ : Commute (β * q') (α * β) :=
    Commute.mul_right (Commute.mul_left (show Commute β α from hαβ.symm)
      (show Commute q' α from hαq'.symm))
      (Commute.mul_left (Commute.refl β) (show Commute q' β from hβq'.symm))
  have hcomm₂ : Commute (α * q) (α * β) :=
    Commute.mul_right (Commute.mul_left (Commute.refl α) (show Commute q α from hαq.symm))
      (Commute.mul_left (show Commute α β from hαβ) (show Commute q β from hqβ))
  have hgt : (y * c₀)⁻¹ * t * (y * c₀) = β * q' := by
    calc (y * c₀)⁻¹ * t * (y * c₀) = c₀⁻¹ * (y⁻¹ * t * y) * c₀ := by group
      _ = c₀⁻¹ * (β * q') * c₀ := by rw [hyt]
      _ = β * q' := l515S_conj_eq_of_comm hc₀t₁
  have hgs : (y * c₀)⁻¹ * (h⁻¹ * t * h) * (y * c₀) = α * q := by
    calc (y * c₀)⁻¹ * (h⁻¹ * t * h) * (y * c₀)
        = c₀⁻¹ * (y⁻¹ * (h⁻¹ * t * h) * y) * c₀ := by group
      _ = c₀⁻¹ * (h⁻¹ * t * h) * c₀ := by rw [l515S_conj_eq_of_comm hys.symm]
      _ = α * q := hc₀s
  refine ⟨y * c₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgt]
    exact hcomm₁.eq
  · rw [hgs]
    exact hcomm₂.eq
  · calc (y * c₀)⁻¹ * z * (y * c₀) = c₀⁻¹ * (y⁻¹ * z * y) * c₀ := by group
      _ = c₀⁻¹ * z * c₀ := by rw [hq.conj_z_of_mem_pair hy]
      _ = z := hq.conj_z_of_mem_pair hc₀
  · intro l
    rw [← sec5b517_conjugate_conjugate,
      hq.conjugate_eq_of_mem_pair (i := 2) (j := 3) (by decide) hy l,
      hq.conjugate_eq_of_mem_pair (i := 0) (j := 1) (by decide) hc₀ l]
  · rw [hgt]
    exact (Commute.mul_right (Commute.refl β) (show Commute β q' from hβq')).eq
  · rw [hgs]
    exact (Commute.mul_right (Commute.refl α) (show Commute α q from hαq)).eq

end Ctx

end CFSG.OddStandard.SmallF3.Omega

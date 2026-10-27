module

public import CFSG.LargeExtraspecial.AS35JGen
public import CFSG.LargeExtraspecial.AS35HLocal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem sup_Qa_eq_HAt_J (hS : S.SixHyp) {t h : G} (ht : t ∈ S.DSet) (hh : h * S.z * h⁻¹ = t)
    {k₁ k₂ : G} (hk₁ : k₁ * S.z * k₁⁻¹ ∈ S.zConj (S.HAt h))
    (hk₂ : k₂ * S.z * k₂⁻¹ ∈ S.zConj (S.HAt h)) (hne : k₁ * S.z * k₁⁻¹ ≠ k₂ * S.z * k₂⁻¹) :
    S.Qa k₁ ⊔ S.Qa k₂ = S.HAt h := by
  obtain ⟨h₁, hh₁, e₁⟩ := hk₁
  obtain ⟨h₂, hh₂, e₂⟩ := hk₂
  rw [← S.Qa_eq_of_conj_eq e₁, ← S.Qa_eq_of_conj_eq e₂]
  have hH := (S.isHStar_of_mem_ESet ht.1 hh).1
  have hg : h₁⁻¹ * h₂ ∈ S.HAt h := (S.HAt h).mul_mem ((S.HAt h).inv_mem hh₁) hh₂
  have hgM : h₁⁻¹ * h₂ ∉ S.M := by
    intro hM
    apply hne
    rw [← e₁, ← e₂]
    have h1 := S.conj_z_of_mem_M hM
    calc h₁ * S.z * h₁⁻¹ = h₁ * ((h₁⁻¹ * h₂) * S.z * (h₁⁻¹ * h₂)⁻¹) * h₁⁻¹ := by rw [h1]
      _ = h₂ * S.z * h₂⁻¹ := by group
  have heq := ((hS.sixFour _ hH).2 _ hg hgM).1
  have h1 := congrArg (fun K : Subgroup G => K.map (MulAut.conj h₁).toMonoidHom) heq
  rw [AS35J.map_conj_eq_self_of_mem hh₁, Subgroup.map_sup, ← Qa_eq_map, ← Qa_mul,
    mul_inv_cancel_left] at h1
  exact h1.symm

theorem conj_mem_zConj_J (hS : S.SixHyp) {t h : G} (ht : t ∈ S.DSet) (hh : h * S.z * h⁻¹ = t)
    {c p₁ p₂ : G} (hp₁ : p₁ ∈ S.zConj (S.HAt h)) (hp₂ : p₂ ∈ S.zConj (S.HAt h)) (hne : p₁ ≠ p₂)
    (hcp₁ : c * p₁ * c⁻¹ ∈ S.zConj (S.HAt h)) (hcp₂ : c * p₂ * c⁻¹ ∈ S.zConj (S.HAt h))
    {x : G} (hx : x ∈ S.zConj (S.HAt h)) : c * x * c⁻¹ ∈ S.zConj (S.HAt h) := by
  obtain ⟨k₁, -, e₁⟩ := id hp₁
  obtain ⟨k₂, -, e₂⟩ := id hp₂
  have hA := S.sup_Qa_eq_HAt_J hS ht hh (by rw [e₁]; exact hp₁) (by rw [e₂]; exact hp₂)
    (by rwa [e₁, e₂])
  have hc₁ : c * k₁ * S.z * (c * k₁)⁻¹ = c * p₁ * c⁻¹ := by rw [← e₁]; group
  have hc₂ : c * k₂ * S.z * (c * k₂)⁻¹ = c * p₂ * c⁻¹ := by rw [← e₂]; group
  have hB := S.sup_Qa_eq_HAt_J hS ht hh (k₁ := c * k₁) (k₂ := c * k₂)
    (by rw [hc₁]; exact hcp₁) (by rw [hc₂]; exact hcp₂)
    (by
      rw [hc₁, hc₂]
      intro h'
      apply hne
      calc p₁ = c⁻¹ * (c * p₁ * c⁻¹) * c := by group
        _ = p₂ := by rw [h']; group)
  have hmap : (S.HAt h).map (MulAut.conj c).toMonoidHom = S.HAt h := by
    calc (S.HAt h).map (MulAut.conj c).toMonoidHom =
        (S.Qa k₁ ⊔ S.Qa k₂).map (MulAut.conj c).toMonoidHom := by rw [hA]
      _ = S.Qa (c * k₁) ⊔ S.Qa (c * k₂) := by rw [Subgroup.map_sup, Qa_mul, Qa_mul]
      _ = S.HAt h := hB
  change x ∈ Asc77.conjIn S.z (S.HAt h) at hx
  rw [← Asc77.conjIn_eq_of_mem hp₁] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  have hcg : c * g * c⁻¹ ∈ S.HAt h := by
    rw [← hmap]
    exact ⟨g, hg, rfl⟩
  rw [show c * (g * p₁ * g⁻¹) * c⁻¹ = (c * g * c⁻¹) * (c * p₁ * c⁻¹) * (c * g * c⁻¹)⁻¹ by
    group]
  exact Asc77.conj_mem_conjIn_of_mem hcg hcp₁

theorem conj_z_eq_or_J (hS : S.SixHyp) {t h : G} (ht : t ∈ S.DSet) (hh : h * S.z * h⁻¹ = t)
    {c : G} (hc : ∀ p ∈ S.zConj (S.HAt h), p ≠ S.z → p ≠ t → c * p = p * c) :
    c * S.z * c⁻¹ = S.z ∨ c * S.z * c⁻¹ = t := by
  have htH := S.mem_zConj_of_mem_ESet ht.1 hh
  have h5 := (S.isHStar_of_mem_ESet ht.1 hh).2
  have htz := S.ne_z_of_mem_ESet ht.1
  have hsub : ({S.z, t} : Set G) ⊆ S.zConj (S.HAt h) := by
    rintro w (rfl | rfl)
    · exact Asc77.self_mem_conjIn _ _
    · exact htH
  have h3 : (S.zConj (S.HAt h) \ {S.z, t}).ncard = 3 := by
    rw [Set.ncard_sdiff hsub, h5, Set.ncard_pair htz.symm]
  obtain ⟨p, p', hp, hp', hne⟩ := (Set.one_lt_ncard_iff
    (s := S.zConj (S.HAt h) \ {S.z, t}) (Set.toFinite _)).mp (by omega)
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp hp'
  obtain ⟨hpH, hpz, hpt⟩ := hp
  obtain ⟨hp'H, hp'z, hp't⟩ := hp'
  have hcp : c * p * c⁻¹ = p := by rw [hc p hpH hpz hpt]; group
  have hcp' : c * p' * c⁻¹ = p' := by rw [hc p' hp'H hp'z hp't]; group
  have hzH := S.conj_mem_zConj_J hS ht hh hpH hp'H hne (by rw [hcp]; exact hpH)
    (by rw [hcp']; exact hp'H) (Asc77.self_mem_conjIn S.z (S.HAt h))
  by_contra hcon
  push Not at hcon
  have h1 := hc _ hzH hcon.1 hcon.2
  apply hcon.1
  calc c * S.z * c⁻¹ = c⁻¹ * (c * (c * S.z * c⁻¹)) := by group
    _ = c⁻¹ * ((c * S.z * c⁻¹) * c) := by rw [h1]
    _ = S.z := by group

theorem exists_conj_mem_QG_J (hS : S.SixHyp) {t h s : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) (hs : s ∈ S.zConj (S.HAt h)) (hsz : s ≠ S.z) (hst : s ≠ t) :
    ∃ k : G, k * S.z * k⁻¹ = s ∧ k⁻¹ * (S.z * t) * k ∈ S.QG := by
  obtain ⟨k, -, hk⟩ := id hs
  have hsD := S.zConj_diff_subset_DSet hS.sixFour ht hh hs hsz
  have hHk : S.HAt k = S.HAt h := by
    have h1 := S.sup_Qa_eq_HAt_J hS ht hh (k₁ := 1) (k₂ := k)
      (by simpa using Asc77.self_mem_conjIn S.z (S.HAt h)) (by rw [hk]; exact hs)
      (by rw [hk]; simpa using hsz.symm)
    rwa [Qa_one] at h1
  have htk : t ∈ S.zConj (S.HAt k) := by
    rw [hHk]
    exact S.mem_zConj_of_mem_ESet ht.1 hh
  have h1 := S.mul_z_mem_Qa_of_mem_zConj hS hsD hk htk (Ne.symm hst)
  refine ⟨k, hk, ?_⟩
  rw [S.mem_Qa_iff_inv_conj_mem] at h1
  rwa [← S.mem_M_iff.mp (S.mem_M_of_mem_ESet hS.sixFour ht.1)]

end Setting

end CFSG.LargeExtraspecial

module

public import CFSG.GH74.GLS.Bg.Iii2.FusionStmt
import CFSG.GH74.GLS.Bg.Iii2.FusionAux

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2.FusionKleinProof

theorem fusionKlein_of : FusionKlein := by
  intro G _ _ T hT x y hx hy hx1 _ hne hcomm _ hyT hcen hconj hcl
  have hcen' : ∀ t ∈ T, t * x * t⁻¹ = x := fun t ht => by
    rw [hcen t ht, mul_inv_cancel_right]
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  let E : Subgroup G := kleinSub x y hx hy hcomm
  have hxE : x ∈ E := mem_kleinSub.2 (Or.inr (Or.inl rfl))
  have hyE : y ∈ E := mem_kleinSub.2 (Or.inr (Or.inr (Or.inl rfl)))
  have hxyE : x * y ∈ E := mem_kleinSub.2 (Or.inr (Or.inr (Or.inr rfl)))
  have hclE : ∀ g : G, g * x * g⁻¹ ∈ T → g * x * g⁻¹ ∈ E := by
    intro g hg
    rcases hcl g hg with h | h | h
    · rw [h]; exact hxE
    · rw [h]; exact hyE
    · rw [h]; exact hxyE
  have hclyE : ∀ n : G, n * y * n⁻¹ ∈ T → n * y * n⁻¹ ∈ E := by
    intro n hn
    have h : n * y * n⁻¹ = (n * c) * x * (n * c)⁻¹ := by rw [← hc]; group
    rw [h] at hn ⊢
    exact hclE _ hn
  let N : Subgroup G := Subgroup.normalizer (E : Set G)
  have hTN : T ≤ N := by
    intro t ht
    refine mem_normalizer_kleinSub hx hy hcomm t ?_ ?_
    · rw [hcen' t ht]; exact hxE
    · exact hclyE t (T.mul_mem (T.mul_mem ht hyT) (T.inv_mem ht))
  have hTN' : IsSylowOf 2 T N := hT.of_le hTN le_top
  have hweak : ∀ n : G, (∀ e ∈ E, n * e * n⁻¹ ∈ T) → n ∈ N := fun n h =>
    mem_normalizer_kleinSub hx hy hcomm n (hclE n (h x hxE)) (hclyE n (h y hyE))
  let P : Subgroup G := E.map (MulAut.conj c⁻¹).toMonoidHom
  have hPpg : IsPGroup 2 P := (kleinSub_isPGroup hx hy hcomm).map _
  have hPC : P ≤ Subgroup.centralizer {x} := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxc : x = c⁻¹ * y * c := by rw [← hc]; group
    have he' : e * y = y * e := kleinSub_mul_comm hx hy hcomm he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hxc]
    calc c⁻¹ * e * c * (c⁻¹ * y * c) = c⁻¹ * (e * y) * c := by group
      _ = c⁻¹ * (y * e) * c := by rw [he']
      _ = c⁻¹ * y * c * (c⁻¹ * e * c) := by group
  have hTC : T ≤ Subgroup.centralizer {x} := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcen t ht)
  obtain ⟨d, hdC, hdP⟩ := exists_conj_mem_of_isSylowOf (hT.of_le hTC le_top) hPC hPpg
  have hn₀ : d * c⁻¹ ∈ N := by
    apply hweak
    intro e he
    have h := hdP (c⁻¹ * e * c) ⟨e, he, by simp⟩
    have h' : d * c⁻¹ * e * (d * c⁻¹)⁻¹ = d * (c⁻¹ * e * c) * d⁻¹ := by group
    rw [h']
    exact h
  have hn : c * d⁻¹ ∈ N := by
    have := N.inv_mem hn₀
    simpa using this
  have hdx : d⁻¹ * x * d = x := by
    have hd : d * x = x * d := Subgroup.mem_centralizer_singleton_iff.1 hdC
    calc d⁻¹ * x * d = d⁻¹ * (x * d) := by rw [mul_assoc]
      _ = d⁻¹ * (d * x) := by rw [hd]
      _ = x := inv_mul_cancel_left d x
  have hnx : c * d⁻¹ * x * (c * d⁻¹)⁻¹ = y := by
    have : c * d⁻¹ * x * (c * d⁻¹)⁻¹ = c * (d⁻¹ * x * d) * c⁻¹ := by group
    rw [this, hdx, hc]
  by_contra hcon
  refine false_of_orbit_pair hTN' hcen' hne ?_ hn hnx
  intro m hm
  have hmE : m * x * m⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hm x).1 hxE
  rcases mem_kleinSub.1 hmE with h | h | h | h
  · exfalso
    have h1 : x = 1 := by simpa using h
    exact hx1 h1
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (isConj_iff.2 ⟨m, h⟩) hcon

end CFSG.GH74.GLS.Bg.Iii2

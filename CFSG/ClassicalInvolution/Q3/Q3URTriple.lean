module

public import CFSG.ClassicalInvolution.Q3.Q3URNodes
public import CFSG.ClassicalInvolution.Q3.Q3URSU4
public import CFSG.ClassicalInvolution.Q3.Q3URFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped MatrixGroups

section Triples

variable {m : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UCtx3.triple_of_members (c : UCtx3 m Ω K z)
    (hN : NoCover.{0} (fun n => Odd n ∧ ¬ 3 ∣ n) (Su (GaloisField 3 2) 3 1 4)) (hm : 3 ≤ m)
    {L₀ L₁ L₂ : Subgroup G} (h₀ : L₀ ∈ centralizingMembers Ω {z})
    (h₁ : L₁ ∈ centralizingMembers Ω {z}) (h₂ : L₂ ∈ centralizingMembers Ω {z})
    (k₀ : L₀ ≠ K) (k₁ : L₁ ≠ K) (k₂ : L₂ ≠ K) {w₀ w₁ w₂ : G}
    (hw₀ : IsClassicalMember3 L₀ w₀) (hw₁ : IsClassicalMember3 L₁ w₁)
    (hw₂ : IsClassicalMember3 L₂ w₂) (c₀₁ : w₀ * w₁ = w₁ * w₀) (c₁₂ : w₁ * w₂ = w₂ * w₁)
    (c₀₂ : w₀ * w₂ = w₂ * w₀) (n₀₁ : L₀ ≠ L₁) (n₁₂ : L₁ ≠ L₂) (n₀₂ : L₀ ≠ L₂)
    (r₀₂ : Commutes L₀ L₂) (a₀₁ : ¬ Commutes L₀ L₁) (a₁₂ : ¬ Commutes L₁ L₂) :
    ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G, θ.range = (L₀ ⊔ L₁) ⊔ (L₁ ⊔ L₂) ∧
      θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = L₀ ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = L₁ ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = L₂ := by
  obtain ⟨R₀, i₀, hR₀, hL₀, hi₀⟩ := c.exists_rootData h₀ k₀ hw₀
  obtain ⟨R₁, i₁, hR₁, hL₁, hi₁⟩ := c.exists_rootData h₁ k₁ hw₁
  obtain ⟨R₂, i₂, hR₂, hL₂, hi₂⟩ := c.exists_rootData h₂ k₂ hw₂
  obtain ⟨cc₀₁, nn₀₁⟩ := c.commute_of_locElt h₀ h₁ n₀₁ hR₀ hR₁ hL₀ hL₁
    (le_centralizingLayer h₀ hw₀.mem) (le_centralizingLayer h₁ hw₁.mem) hi₀ hi₁ c₀₁
  obtain ⟨cc₁₂, nn₁₂⟩ := c.commute_of_locElt h₁ h₂ n₁₂ hR₁ hR₂ hL₁ hL₂
    (le_centralizingLayer h₁ hw₁.mem) (le_centralizingLayer h₂ hw₂.mem) hi₁ hi₂ c₁₂
  obtain ⟨cc₀₂, nn₀₂⟩ := c.commute_of_locElt h₀ h₂ n₀₂ hR₀ hR₂ hL₀ hL₂
    (le_centralizingLayer h₀ hw₀.mem) (le_centralizingLayer h₂ hw₂.mem) hi₀ hi₂ c₀₂
  have rr₀₂ : Commutes R₀ R₂ := (c.commutes_iff_root h₀ h₂ hR₀ hL₀ hL₂).mp r₀₂
  have aa₀₁ : ¬ Commutes R₀ R₁ := fun h => a₀₁ ((c.commutes_iff_root h₀ h₁ hR₀ hL₀ hL₁).mpr h)
  have aa₁₂ : ¬ Commutes R₁ R₂ := fun h => a₁₂ ((c.commutes_iff_root h₁ h₂ hR₁ hL₁ hL₂).mpr h)
  obtain ⟨ι, hι, b₀, b₁, b₂⟩ := exists_blocks_of_chain3 card_gf9 (by norm_num)
    (by omega : 4 ≤ m + 1) hR₀ hR₁ hR₂ cc₀₁ cc₁₂ cc₀₂ nn₀₁ nn₁₂ nn₀₂ rr₀₂ aa₀₁ aa₁₂
  have hker : (c.d.ψ.comp ι).ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : ι x ∈ c.d.ψ.ker := hx
    have h2 := Subgroup.mem_center_iff.mp (c.d.ker_le h1) (ι y)
    exact hι (by rw [map_mul, map_mul]; exact h2)
  exact tripleOfLocImg3 hN c.hΩ c.hex c.hP1 c.hO3 h₀ h₁ h₂ (c.d.ψ.comp ι)
    hker (by rw [← Subgroup.map_map, b₀, hL₀]) (by rw [← Subgroup.map_map, b₁, hL₁])
    (by rw [← Subgroup.map_map, b₂, hL₂])

theorem UCtx3.triple_of_members_conj (c : UCtx3 m Ω K z)
    (hN : NoCover.{0} (fun n => Odd n ∧ ¬ 3 ∣ n) (Su (GaloisField 3 2) 3 1 4)) (hm : 3 ≤ m)
    {g : G} {Z' : Subgroup G} (hZ : Z' = conjSub g K) {L₀ L₁ L₂ : Subgroup G} (h₀ : L₀ ∈ Ω)
    (h₁ : L₁ ∈ Ω) (h₂ : L₂ ∈ Ω) (z₀ : Commutes L₀ Z') (z₁ : Commutes L₁ Z')
    (z₂ : Commutes L₂ Z') (e₀ : L₀ ≠ Z') (e₁ : L₁ ≠ Z') (e₂ : L₂ ≠ Z') {w₀ w₁ w₂ : G}
    (hw₀ : IsClassicalMember3 L₀ w₀) (hw₁ : IsClassicalMember3 L₁ w₁)
    (hw₂ : IsClassicalMember3 L₂ w₂) (c₀₁ : w₀ * w₁ = w₁ * w₀) (c₁₂ : w₁ * w₂ = w₂ * w₁)
    (c₀₂ : w₀ * w₂ = w₂ * w₀) (n₀₁ : L₀ ≠ L₁) (n₁₂ : L₁ ≠ L₂) (n₀₂ : L₀ ≠ L₂)
    (r₀₂ : Commutes L₀ L₂) (a₀₁ : ¬ Commutes L₀ L₁) (a₁₂ : ¬ Commutes L₁ L₂) :
    ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G, θ.range = (L₀ ⊔ L₁) ⊔ (L₁ ⊔ L₂) ∧
      θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = L₀ ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = L₁ ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = L₂ := by
  obtain ⟨m₀, k₀, -⟩ := c.exists_rootData_conj hZ h₀ z₀ e₀ hw₀
  obtain ⟨m₁, k₁, -⟩ := c.exists_rootData_conj hZ h₁ z₁ e₁ hw₁
  obtain ⟨m₂, k₂, -⟩ := c.exists_rootData_conj hZ h₂ z₂ e₂ hw₂
  have hcl : ∀ {L : Subgroup G} {w : G}, IsClassicalMember3 L w →
      IsClassicalMember3 (conjSub g⁻¹ L) (g⁻¹ * w * g) := by
    intro L w h
    have := IsClassicalMember3.conj h g⁻¹
    rwa [inv_inv] at this
  have hcc : ∀ {a b : G}, a * b = b * a →
      g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * b * g * (g⁻¹ * a * g) := by
    intro a b h
    calc g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
      _ = g⁻¹ * (b * a) * g := by rw [h]
      _ = g⁻¹ * b * g * (g⁻¹ * a * g) := by group
  obtain ⟨θ', hθr, hθk, f₀, f₁, f₂⟩ := c.triple_of_members hN hm m₀ m₁ m₂ k₀ k₁ k₂ (hcl hw₀)
    (hcl hw₁)
    (hcl hw₂) (hcc c₀₁) (hcc c₁₂) (hcc c₀₂) (fun h => n₀₁ (conjSub_injective g⁻¹ h))
    (fun h => n₁₂ (conjSub_injective g⁻¹ h)) (fun h => n₀₂ (conjSub_injective g⁻¹ h))
    ((commutes_conjSub_iff g⁻¹).mpr r₀₂) (fun h => a₀₁ ((commutes_conjSub_iff g⁻¹).mp h))
    (fun h => a₁₂ ((commutes_conjSub_iff g⁻¹).mp h))
  have hconj : ∀ A B : Subgroup G, conjSub g (A ⊔ B) = conjSub g A ⊔ conjSub g B :=
    fun A B => Subgroup.map_sup _ _ _
  refine ⟨(MulAut.conj g).toMonoidHom.comp θ', ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hθr]
    show conjSub g _ = _
    rw [hconj, hconj, hconj, conjSub_conjSub_inv, conjSub_conjSub_inv, conjSub_conjSub_inv]
  · intro x hx
    apply hθk
    have h1 : g * θ' x * g⁻¹ = 1 := hx
    rw [MonoidHom.mem_ker]
    simpa using h1
  · rw [← Subgroup.map_map, f₀]
    exact conjSub_conjSub_inv g L₀
  · rw [← Subgroup.map_map, f₁]
    exact conjSub_conjSub_inv g L₁
  · rw [← Subgroup.map_map, f₂]
    exact conjSub_conjSub_inv g L₂

theorem UCtx3.node_triple (c : UCtx3 m Ω K z) (nd : UNodes3 c)
    (hN : NoCover.{0} (fun n => Odd n ∧ ¬ 3 ∣ n) (Su (GaloisField 3 2) 3 1 4)) (hm : 3 ≤ m)
    {a : ℕ} (ha : a + 2 < m) :
    ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G,
      θ.range = (nd.j a ⊔ nd.j (a + 1)) ⊔ (nd.j (a + 1) ⊔ nd.j (a + 2)) ∧
        θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
        (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = nd.j a ∧
        (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = nd.j (a + 1) ∧
        (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = nd.j (a + 2) :=
  c.triple_of_members hN hm (nd.mem a (by omega)) (nd.mem (a + 1) (by omega))
    (nd.mem (a + 2) ha) (nd.ne_K a (by omega)) (nd.ne_K (a + 1) (by omega))
    (nd.ne_K (a + 2) ha) (nd.isCl a (by omega)) (nd.isCl (a + 1) (by omega))
    (nd.isCl (a + 2) ha) (nd.wcomm a (by omega) (a + 1) (by omega))
    (nd.wcomm (a + 1) (by omega) (a + 2) ha) (nd.wcomm a (by omega) (a + 2) ha)
    (nd.inj a (by omega) (a + 1) (by omega) (by omega))
    (nd.inj (a + 1) (by omega) (a + 2) ha (by omega)) (nd.inj a (by omega) (a + 2) ha (by omega))
    (nd.far a (by omega) (a + 2) ha le_rfl) (nd.adj a (by omega)) (nd.adj (a + 1) (by omega))

end Triples

end CFSG.ClassicalInvolution.Q3.Q3W

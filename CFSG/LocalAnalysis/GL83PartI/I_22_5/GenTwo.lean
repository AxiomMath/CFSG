module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Descent

public section

namespace GL83.CompFam

open CFSG.Open

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {B : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem IsFam.commutator_mem_normJoin (hF : IsFam p B 𝒦) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦)
    {b b' : G} (hb : b ∈ B) (hb' : b' ∈ B) (hbA : b ∉ stab B K₀) (hbA' : b' ∉ stab B K₀)
    (hind : ∀ i j : ZMod p, cj (b ^ i.val) K₀ = cj (b' ^ j.val) K₀ → i = 0 ∧ j = 0)
    (x y : K₀) : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ normJoin hF K₀ := by
  have hc := hF.normComm hK₀ hb hbA
  have hc' := hF.normComm hK₀ hb' hbA'
  obtain ⟨d₁, hd₁c, hd₁s, h1⟩ := normHom_decomp' hc x
  obtain ⟨d₂, hd₂c, hd₂s, h2⟩ := normHom_decomp' hc' y
  have hxy1 : (y : G) * d₁ = d₁ * y := Subgroup.mem_centralizer_iff.1 hd₁c y y.2
  have hxy2 : (x : G) * d₂ = d₂ * x := Subgroup.mem_centralizer_iff.1 hd₂c x x.2
  have hd : d₁ * d₂ = d₂ * d₁ := by
    refine comm_of_iSup (fun i : {i : ZMod p // i ≠ 0} => cj (b ^ i.1.val) K₀)
      (fun j : {j : ZMod p // j ≠ 0} => cj (b' ^ j.1.val) K₀) ?_ d₁ hd₁s d₂ hd₂s
    intro i j u hu v hv
    refine hF.comm _ (hF.smul_mem K₀ hK₀ _ (B.pow_mem hb _)) _
      (hF.smul_mem K₀ hK₀ _ (B.pow_mem hb' _)) ?_ u hu v hv
    intro heq
    exact i.2 (hind i.1 j.1 heq).1
  have hn : normHom hc x ∈ normJoin hF K₀ :=
    le_normJoin hF ⟨b, hb, hbA, normSub_mem_normFam hF hK₀ hb hbA⟩ ⟨x, rfl⟩
  have hn' : normHom hc' y ∈ normJoin hF K₀ :=
    le_normJoin hF ⟨b', hb', hbA', normSub_mem_normFam hF hK₀ hb' hbA'⟩ ⟨y, rfl⟩
  have e1 : ((x : G) * d₁) * ((y : G) * d₂) = ((x : G) * y) * (d₁ * d₂) := by
    calc ((x : G) * d₁) * ((y : G) * d₂) = x * (d₁ * y) * d₂ := by group
      _ = x * (y * d₁) * d₂ := by rw [← hxy1]
      _ = ((x : G) * y) * (d₁ * d₂) := by group
  have e2 : ((y : G) * d₂) * ((x : G) * d₁) = ((y : G) * x) * (d₁ * d₂) := by
    calc ((y : G) * d₂) * ((x : G) * d₁) = y * (d₂ * x) * d₁ := by group
      _ = y * (x * d₂) * d₁ := by rw [← hxy2]
      _ = ((y : G) * x) * (d₂ * d₁) := by group
      _ = ((y : G) * x) * (d₁ * d₂) := by rw [hd]
  have key : normHom hc x * normHom hc' y * (normHom hc x)⁻¹ * (normHom hc' y)⁻¹ =
      (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ := by
    rw [h1, h2]
    calc ((x : G) * d₁) * ((y : G) * d₂) * ((x : G) * d₁)⁻¹ * ((y : G) * d₂)⁻¹
        = (((x : G) * d₁) * ((y : G) * d₂)) * (((y : G) * d₂) * ((x : G) * d₁))⁻¹ := by group
      _ = (((x : G) * y) * (d₁ * d₂)) * (((y : G) * x) * (d₁ * d₂))⁻¹ := by rw [e1, e2]
      _ = (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ := by group
  rw [← key]
  exact mul_mem (mul_mem (mul_mem hn hn') (inv_mem hn)) (inv_mem hn')

theorem IsFam.layer_le_normJoin_of_independent (hF : IsFam p B 𝒦) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ 𝒦) {b b' : G} (hb : b ∈ B) (hb' : b' ∈ B) (hbA : b ∉ stab B K₀)
    (hbA' : b' ∉ stab B K₀)
    (hind : ∀ i j : ZMod p, cj (b ^ i.val) K₀ = cj (b' ^ j.val) K₀ → i = 0 ∧ j = 0) :
    layer 𝒦 ≤ normJoin hF K₀ := by
  refine hF.layer_le_normJoin hK₀ ?_
  have hperf : ⁅K₀, K₀⁆ = K₀ :=
    Subgroup.isPerfect_iff.1 ((Group.isPerfect_def).2 (hF.quasi K₀ hK₀).1)
  have hcomm : ⁅K₀, K₀⁆ ≤ normJoin hF K₀ := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact hF.commutator_mem_normJoin hK₀ hb hb' hbA hbA' hind ⟨x, hx⟩ ⟨y, hy⟩
  calc K₀ = ⁅K₀, K₀⁆ := hperf.symm
    _ ≤ normJoin hF K₀ := hcomm

end GL83.CompFam

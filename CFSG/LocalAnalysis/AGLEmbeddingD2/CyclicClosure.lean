module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding

theorem exists_eq_map_conj_of_isCyclic {J : Type*} [Group J] [Finite J] {p : ℕ} [Fact p.Prime]
    (hcyc : ∀ T : Sylow p J, IsCyclic T) {Y₀ Y₁ : Subgroup J} (h₀ : Nat.card Y₀ = p)
    (h₁ : Nat.card Y₁ = p) : ∃ j : J, Y₁ = Y₀.map (MulAut.conj j).toMonoidHom := by
  have hp₀ : IsPGroup p Y₀ := IsPGroup.of_card (n := 1) (by rw [h₀, pow_one])
  have hp₁ : IsPGroup p Y₁ := IsPGroup.of_card (n := 1) (by rw [h₁, pow_one])
  obtain ⟨T₀, hT₀⟩ := hp₀.exists_le_sylow
  obtain ⟨T₁, hT₁⟩ := hp₁.exists_le_sylow
  obtain ⟨j, hj⟩ := MulAction.exists_smul_eq J T₀ T₁
  refine ⟨j, ?_⟩
  have hT : ((T₁ : Sylow p J) : Subgroup J) =
      (T₀ : Subgroup J).map (MulAut.conj j).toMonoidHom := by
    rw [← hj, Sylow.coe_subgroup_smul]
    rfl
  have hY₀T : Y₀.map (MulAut.conj j).toMonoidHom ≤ T₁ := hT ▸ Subgroup.map_mono hT₀
  have := hcyc T₁
  have hcard : Nat.card (Y₁.subgroupOf T₁) =
      Nat.card ((Y₀.map (MulAut.conj j).toMonoidHom).subgroupOf T₁) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY₀T).toEquiv, h₁,
      Subgroup.card_map_of_injective (MulAut.conj j).injective, h₀]
  have heq := (IsCyclic.subgroup_eq_iff_card_eq (G := T₁)).mpr hcard
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hT₁, inf_of_le_left hY₀T] at heq
  exact heq

variable {G : Type} [Group G] [Finite G]

theorem nclIn_le_nclIn_of_isCyclic {p : ℕ} [Fact p.Prime] {H X H' : Subgroup G} (hXH : X ≤ H)
    (hXp : Nat.card X = p)
    (hcyc : ∀ Y : Subgroup G, Y ≤ nclIn H X → IsPGroup p Y → IsCyclic Y)
    (hJH' : nclIn H X ≤ H') : nclIn H X ≤ nclIn H' X := by
  set J := nclIn H X with hJdef
  have hXJ : X ≤ J := le_nclIn hXH
  have hJH : J ≤ H := nclIn_le_self H X
  have hcycJ : ∀ T : Sylow p J, IsCyclic T := by
    intro T
    have hTp : IsPGroup p ((T : Subgroup J).map J.subtype) := T.isPGroup'.map J.subtype
    have hc := hcyc _ (Subgroup.map_subtype_le _) hTp
    let e := (Subgroup.equivMapOfInjective (T : Subgroup J) J.subtype J.subtype_injective).symm
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hconj : ∀ c ∈ H, ∀ x ∈ X, c * x * c⁻¹ ∈ nclIn J X := by
    intro c hc x hx
    set Xc : Subgroup G := X.map (MulAut.conj c).toMonoidHom with hXc
    have hXcJ : Xc ≤ J := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_nclIn H X hc) y).mp (hXJ hy)
    have hcard₀ : Nat.card (X.subgroupOf J) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXJ).toEquiv, hXp]
    have hcard₁ : Nat.card (Xc.subgroupOf J) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXcJ).toEquiv, hXc,
        Subgroup.card_map_of_injective (MulAut.conj c).injective, hXp]
    obtain ⟨j, hj⟩ := exists_eq_map_conj_of_isCyclic hcycJ hcard₀ hcard₁
    have hmem : (⟨c * x * c⁻¹, hXcJ ⟨x, hx, rfl⟩⟩ : J) ∈ Xc.subgroupOf J :=
      Subgroup.mem_subgroupOf.mpr ⟨x, hx, rfl⟩
    rw [hj] at hmem
    obtain ⟨⟨y, hyJ⟩, hy, hyeq⟩ := hmem
    have hyX : y ∈ X := Subgroup.mem_subgroupOf.mp hy
    have heq : c * x * c⁻¹ = (j : G) * y * (j : G)⁻¹ := by
      have := congrArg Subtype.val hyeq
      simpa [MulAut.conj_apply] using this.symm
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_nclIn J X j.2) y).mp
      (le_nclIn hXJ hyX)
  have hJJ : J ≤ nclIn J X := by
    rintro _ ⟨y, hy, rfl⟩
    have hcl : Subgroup.normalClosure ((X.subgroupOf H : Subgroup H) : Set H) ≤
        (nclIn J X).subgroupOf H := by
      show Subgroup.closure (Group.conjugatesOfSet _) ≤ _
      rw [Subgroup.closure_le]
      intro z hz
      obtain ⟨b, hb, hbz⟩ := Group.mem_conjugatesOfSet_iff.mp hz
      obtain ⟨c, rfl⟩ := isConj_iff.mp hbz
      exact hconj c c.2 b hb
    exact hcl hy
  exact hJJ.trans (nclIn_le_nclIn_of_le hXJ hJH')

end CFSG.AGLEmbeddingD2

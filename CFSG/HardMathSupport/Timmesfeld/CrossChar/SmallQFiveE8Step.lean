module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Torus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFiveQ2Y
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFiveQ2Char
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwo
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Classical CFSG.RankThree.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false


section Step

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

@[expose] noncomputable def stepHom (L : Type) [Field L] [CharP L 2] :
    ModGL Tag.E8 L →* ModGL Tag.E8 L :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)).toMonoidHom.comp
    (Units.map (entrywiseHom (iterateFrobenius L 2 1)))

theorem stepHom_apply (g : ModGL Tag.E8 L) :
    stepHom L g = canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl *
      Units.map (entrywiseHom (iterateFrobenius L 2 1)) g *
        (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)⁻¹ := rfl

theorem mem_twModel_iff_step {g : ModGL Tag.E8 L} :
    g ∈ twModel (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl) (iterateFrobenius L 2 1) ↔
      g ∈ adjointGroup Tag.E8 L ∧ stepHom L g = g :=
  Iff.rfl

theorem stepHom_rootSL2 {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot Tag.E8 γ) (A : SL2 L) :
    stepHom L (rootSL2 Tag.E8 L γ A) =
      rootSL2 Tag.E8 L (e8PhiFourWeyl • γ)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A) := by
  rw [stepHom_apply, entrywise_rootSL2_of_field, conj_rootSL2_two _ hγ]

theorem stepHom_rootSL2_second {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α)
    (B : SL2 L) :
    stepHom L (rootSL2 Tag.E8 L (e8PhiFourWeyl • α) B) =
      rootSL2 Tag.E8 L α (conjSL swapGL
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) B)) := by
  rw [stepHom_rootSL2 ((isRoot_smul_iff _).2 hα), e8PhiFourWeyl_sq_smul5, rootSL2_neg_two hα]

noncomputable abbrev Lsp (L : Type) [Field L] (α β : Fin Tag.E8.rank → ℤ) :
    Subgroup (ModGL Tag.E8 L) :=
  rootSpan Tag.E8 L {α, -α, β, -β}

theorem Lsp_eq {α β : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) (hβ : IsRoot Tag.E8 β) :
    Lsp L α β = (rootSL2 Tag.E8 L α).range ⊔ (rootSL2 Tag.E8 L β).range := by
  rw [range_rootSL2_of_isRoot hα, range_rootSL2_of_isRoot hβ, Lsp, rootSpan, iSup_insert,
    iSup_insert, iSup_insert, iSup_singleton, sup_assoc]

theorem rootSL2_mem_Lsp_left {α β : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α)
    (hβ : IsRoot Tag.E8 β) (A : SL2 L) : rootSL2 Tag.E8 L α A ∈ Lsp L α β := by
  rw [Lsp_eq hα hβ]
  exact Subgroup.mem_sup_left ⟨A, rfl⟩

theorem rootSL2_mem_Lsp_right {α β : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α)
    (hβ : IsRoot Tag.E8 β) (B : SL2 L) : rootSL2 Tag.E8 L β B ∈ Lsp L α β := by
  rw [Lsp_eq hα hβ]
  exact Subgroup.mem_sup_right ⟨B, rfl⟩

theorem stepHom_Lsp_le {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) :
    (Lsp L α (e8PhiFourWeyl • α)).map (stepHom L) ≤ Lsp L α (e8PhiFourWeyl • α) := by
  have hβ : IsRoot Tag.E8 (e8PhiFourWeyl • α) := (isRoot_smul_iff _).2 hα
  rw [Lsp_eq hα hβ, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    rw [stepHom_rootSL2 hα]
    exact Subgroup.mem_sup_right ⟨_, rfl⟩
  · rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
    rw [stepHom_rootSL2_second hα]
    exact Subgroup.mem_sup_left ⟨_, rfl⟩

theorem stepHom_mem_Lsp {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α)
    {l : ModGL Tag.E8 L} (hl : l ∈ Lsp L α (e8PhiFourWeyl • α)) :
    stepHom L l ∈ Lsp L α (e8PhiFourWeyl • α) :=
  stepHom_Lsp_le hα ⟨l, hl, rfl⟩

theorem exists_mul_of_mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let M : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
          _ = h₁ * (h₂ * k₁) * k₂ := by rw [← hcomm h₂ hh₂ k₁ hk₁]
          _ = h₁ * h₂ * (k₁ * k₂) := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        calc (h * k)⁻¹ = (k * h)⁻¹ := by rw [hcomm h hh k hk]
          _ = h⁻¹ * k⁻¹ := by rw [mul_inv_rev] }
  have hle : H ⊔ K ≤ M := sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩)
  exact hle hx

theorem commute_rootSL2_pair {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) (A B : SL2 L) :
    Commute (rootSL2 Tag.E8 L α A) (rootSL2 Tag.E8 L (e8PhiFourWeyl • α) B) :=
  commute_rootSL2_smul_E8 e8PhiFourWeyl_sq_smul5 hα A B

theorem exists_pair_of_mem_Lsp {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α)
    {g : ModGL Tag.E8 L} (hg : g ∈ Lsp L α (e8PhiFourWeyl • α)) :
    ∃ A B : SL2 L, g = rootSL2 Tag.E8 L α A * rootSL2 Tag.E8 L (e8PhiFourWeyl • α) B := by
  have hβ : IsRoot Tag.E8 (e8PhiFourWeyl • α) := (isRoot_smul_iff _).2 hα
  rw [Lsp_eq hα hβ] at hg
  obtain ⟨_, ⟨A, rfl⟩, _, ⟨B, rfl⟩, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun h hh k hk => by
      obtain ⟨A, rfl⟩ := hh
      obtain ⟨B, rfl⟩ := hk
      exact (commute_rootSL2_pair hα A B).eq) hg
  exact ⟨A, B, rfl⟩

theorem sl2_eq_one_of_central {X : SL2 L} (h : ∀ Z : SL2 L, X * Z = Z * X) : X = 1 :=
  sl2_eq_one_of_central_charTwo h

theorem eq_one_of_rootSL2_eq {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) {A B : SL2 L}
    (h : rootSL2 Tag.E8 L α A = rootSL2 Tag.E8 L (e8PhiFourWeyl • α) B) : A = 1 := by
  have hinj := rootSL2_injective_of_field (τ := Tag.E8) (K := L) α
  apply sl2_eq_one_of_central
  intro Z
  apply hinj
  rw [map_mul, map_mul, h]
  exact (commute_rootSL2_pair hα Z B).eq.symm

theorem entrywise_two_of_mem_torus {t : ModGL Tag.E8 L} (ht : t ∈ torusGroup Tag.E8 L) :
    Units.map (entrywiseHom (iterateFrobenius L 2 1)) t = t ^ 2 := by
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom ht
  have hta : t = rootDiagUnit Tag.E8 a := ha.symm
  rw [hta]
  exact entrywise_two_rootDiagUnit a

theorem conj_mem_torus {t : ModGL Tag.E8 L} (ht : t ∈ torusGroup Tag.E8 L) :
    canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl * t *
      (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)⁻¹ ∈ torusGroup Tag.E8 L := by
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom ht
  have hta : t = rootDiagUnit Tag.E8 a := ha.symm
  rw [hta, canonicalRep_conj_rootDiagUnit]
  exact rootDiagUnit_mem_torusGroup_E8 _

theorem conj_conj_torus {t : ModGL Tag.E8 L} (ht : t ∈ torusGroup Tag.E8 L) :
    canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl *
        (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl * t *
          (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)⁻¹) *
      (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)⁻¹ = t⁻¹ := by
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom ht
  have hta : t = rootDiagUnit Tag.E8 a := ha.symm
  have hw : ∀ u : Fin Tag.E8.rank → ℤ, (e8PhiFourWeyl * e8PhiFourWeyl) • u = -u := fun u => by
    rw [mul_smul]
    exact e8PhiFourWeyl_sq_smul5 u
  have h := SmallQ3.canonicalRep_conj_rootDiagUnit_of_neg (K := L) hw a
  rw [CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo] at h
  rw [hta]
  set n := canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl with hn
  set d := rootDiagUnit Tag.E8 a with hd
  calc n * (n * d * n⁻¹) * n⁻¹ = n * n * d * (n * n)⁻¹ := by group
    _ = d⁻¹ := h

theorem stepHom_torus {t : ModGL Tag.E8 L} (ht : t ∈ torusGroup Tag.E8 L) :
    stepHom L t = (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl * t *
      (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)⁻¹) ^ 2 := by
  rw [stepHom_apply, entrywise_two_of_mem_torus ht, conj_pow]

theorem step_step_torus {t : ModGL Tag.E8 L} (ht : t ∈ torusGroup Tag.E8 L) :
    stepHom L (stepHom L t) = (t ^ 4)⁻¹ := by
  have hu := conj_mem_torus ht
  have h2 := conj_conj_torus ht
  rw [stepHom_torus ht, stepHom_apply, map_pow, entrywise_two_of_mem_torus hu]
  set n := canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl with hn
  set u := n * t * n⁻¹ with hu'
  calc n * (u ^ 2) ^ 2 * n⁻¹ = n * u ^ 4 * n⁻¹ := by rw [← pow_mul]
    _ = (n * u * n⁻¹) ^ 4 := (conj_pow).symm
    _ = (t ^ 4)⁻¹ := by rw [h2, inv_pow]

theorem pow_five_mem_Lsp {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α)
    {g : ModGL Tag.E8 L} (hgW : stepHom L g = g)
    (hg : g ∈ torusGroup Tag.E8 L ⊔ Lsp L α (e8PhiFourWeyl • α)) :
    g ^ 5 ∈ Lsp L α (e8PhiFourWeyl • α) := by
  have hβ : IsRoot Tag.E8 (e8PhiFourWeyl • α) := (isRoot_smul_iff _).2 hα
  set 𝓛 := Lsp L α (e8PhiFourWeyl • α) with h𝓛
  have hTN : torusGroup Tag.E8 L ≤ Subgroup.normalizer (𝓛 : Set (ModGL Tag.E8 L)) := by
    refine CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan fun γ hγ => ?_
    rcases hγ with h | h | h | h
    · rw [h]; exact hα
    · rw [h]; exact isRoot_neg_iff.2 hα
    · rw [h]; exact hβ
    · rw [h]; exact isRoot_neg_iff.2 hβ
  have hnormL : ∀ s ∈ torusGroup Tag.E8 L, ∀ x ∈ 𝓛, s * x * s⁻¹ ∈ 𝓛 := fun s hs x hx =>
    (Subgroup.mem_normalizer_iff.1 (hTN hs) x).1 hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at hg
  obtain ⟨t, ht, l, hl, rfl⟩ := hg
  have hstep : stepHom L t * stepHom L l = t * l := by rw [← map_mul]; exact hgW
  have hstepl : stepHom L l ∈ 𝓛 := stepHom_mem_Lsp hα hl
  set δ := t⁻¹ * stepHom L t with hδ
  have hδL : δ ∈ 𝓛 := by
    have : δ = l * (stepHom L l)⁻¹ := by
      rw [hδ]
      calc t⁻¹ * stepHom L t = t⁻¹ * (stepHom L t * stepHom L l) * (stepHom L l)⁻¹ := by group
        _ = l * (stepHom L l)⁻¹ := by rw [hstep]; group
    rw [this]
    exact 𝓛.mul_mem hl (𝓛.inv_mem hstepl)
  have hstδ : stepHom L δ ∈ 𝓛 := stepHom_mem_Lsp hα hδL
  have e1 : stepHom L (stepHom L t) = t * δ * stepHom L δ := by
    have h1 : stepHom L t = t * δ := by rw [hδ]; group
    conv_lhs => rw [h1]
    rw [map_mul, h1]
  have e2 := step_step_torus ht
  rw [e1] at e2
  have e3 : t ^ 5 = (δ * stepHom L δ)⁻¹ := by
    have : t ^ 5 * (δ * stepHom L δ) = 1 := by
      calc t ^ 5 * (δ * stepHom L δ) = t ^ 4 * (t * δ * stepHom L δ) := by group
        _ = t ^ 4 * (t ^ 4)⁻¹ := by rw [e2]
        _ = 1 := mul_inv_cancel _
    exact eq_inv_of_mul_eq_one_left this
  have h5 : t ^ 5 ∈ 𝓛 := by
    rw [e3]
    exact 𝓛.inv_mem (𝓛.mul_mem hδL hstδ)
  have hpow : ∀ k : ℕ, ∃ l' ∈ 𝓛, (t * l) ^ k = t ^ k * l' := by
    intro k
    induction k with
    | zero => exact ⟨1, 𝓛.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨l', hl', hk⟩ := ih
      refine ⟨t⁻¹ * l' * t * l, 𝓛.mul_mem ?_ hl, ?_⟩
      · have := hnormL t⁻¹ (inv_mem ht) l' hl'
        simpa using this
      · rw [pow_succ, hk]
        group
  obtain ⟨l', hl', hk⟩ := hpow 5
  rw [hk]
  exact 𝓛.mul_mem h5 hl'

end Step

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

end

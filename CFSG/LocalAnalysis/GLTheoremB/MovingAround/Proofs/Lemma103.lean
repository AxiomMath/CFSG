module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Reduction
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma101

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped MatrixGroups

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_of_le' {p : ℕ} {E D : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E)
    (hDE : D ≤ E) : CFSG.Open.IsElemAbelian p D := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x (hDE hx)⟩
  simpa using congrArg Subtype.val (hE.1.is_comm.comm ⟨a.1, hDE a.2⟩ ⟨b.1, hDE b.2⟩)

theorem isPGroup_of_isElemAbelian' {p : ℕ} {D : Subgroup G}
    (hD : CFSG.Open.IsElemAbelian p D) : IsPGroup p ↥D := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  exact ⟨1, Subtype.ext (by simpa using hD.2 g.1 g.2)⟩

theorem le_centralizer_of_comm' {p : ℕ} {X D : Subgroup G} (hX : CFSG.Open.IsElemAbelian p X)
    (hDX : D ≤ X) : X ≤ Subgroup.centralizer (D : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact congrArg Subtype.val (hX.1.is_comm.comm ⟨d, hDX hd⟩ ⟨x, hx⟩)

theorem exists_elemAbelian_card_pow_of_le_pRank' {p : ℕ} [Fact p.Prime] {H : Subgroup G} {k : ℕ}
    (hk : k ≤ CFSG.Open.pRank p H) :
    ∃ D : Subgroup G, D ≤ H ∧ CFSG.Open.IsElemAbelian p D ∧ Nat.card D = p ^ k := by
  obtain ⟨E, hEH, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (Fact.out : p.Prime).one_lt H
  have hdvd : p ^ k ∣ Nat.card ↥E := by
    rw [hEcard]
    exact pow_dvd_pow p hk
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  have hKE : K.map E.subtype ≤ E := Subgroup.map_subtype_le K
  refine ⟨K.map E.subtype, hKE.trans hEH, isElemAbelian_of_le' hE hKE, ?_⟩
  rw [Subgroup.card_map_of_injective (f := E.subtype) Subtype.coe_injective, hK]

theorem exists_conj_le_pGroup' {p : ℕ} [Fact p.Prime] {K X Y : Subgroup G}
    (hXK : X ≤ K) (hX : IsPGroup p ↥X) (hYK : Y ≤ K) (hY : IsPGroup p ↥Y) :
    ∃ x ∈ K, ∃ S : Subgroup G, IsPGroup p ↥S ∧ S ≤ K ∧ X ≤ S ∧ GLBConj x Y ≤ S := by
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_equiv hX (Subgroup.subgroupOfEquivOfLe hXK).symm :
    IsPGroup p ↥(X.subgroupOf K)).exists_le_sylow
  obtain ⟨T, hT⟩ := (IsPGroup.of_equiv hY (Subgroup.subgroupOfEquivOfLe hYK).symm :
    IsPGroup p ↥(Y.subgroupOf K)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K T Q
  refine ⟨((g⁻¹ : K) : G), (g⁻¹).2, (Q : Subgroup K).map K.subtype, Q.isPGroup'.map K.subtype,
    Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro y hy
    exact Subgroup.mem_map.2 ⟨⟨y, hXK hy⟩, hQ (Subgroup.mem_subgroupOf.2 hy), rfl⟩
  · intro z hz
    rw [mem_gLBConj] at hz
    have hwT : (⟨((g⁻¹ : K) : G) * z * ((g⁻¹ : K) : G)⁻¹, hYK hz⟩ : K) ∈ (T : Subgroup K) :=
      hT (Subgroup.mem_subgroupOf.2 hz)
    have hmem : MulAut.conj g ⟨((g⁻¹ : K) : G) * z * ((g⁻¹ : K) : G)⁻¹, hYK hz⟩ ∈
        (Q : Subgroup K) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hwT
    refine Subgroup.mem_map.2 ⟨MulAut.conj g ⟨((g⁻¹ : K) : G) * z * ((g⁻¹ : K) : G)⁻¹, hYK hz⟩,
      hmem, ?_⟩
    simp [MulAut.conj_apply]
    group

theorem pRank_gLBConj' {p : ℕ} (hp : 1 < p) (g : G) (H : Subgroup G) :
    CFSG.Open.pRank p (GLBConj g H) = CFSG.Open.pRank p H := by
  apply le_antisymm
  · have h1 := CFSG.SectionRank.pRank_le_map hp (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective (GLBConj g H)
    have h2 : (GLBConj g H).map (MulAut.conj g).toMonoidHom = H := by
      have h3 := gLBConj_inv_gLBConj g H
      unfold GLBConj at h3 ⊢
      rw [inv_inv] at h3
      exact h3
    rw [h2] at h1
    exact h1
  · exact CFSG.SectionRank.pRank_le_map hp (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective H

end Helpers

theorem lemma103_of_inputs (hI : Input31_8) (h101i : Lemma101_iStatement) :
    Lemma103Statement := by
  intro G _ _ m p B M h
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hB : inD p M B := lemma101_ii_holds h
  obtain ⟨F, hFs, hFn⟩ := h.notStar
  have hF : inDp p M F := ⟨hFs, hFn⟩
  have hBM : B ≤ M := hB.1.1.1
  have hFM : F ≤ M := hF.1.1.1
  obtain ⟨y, hyM, S, hSp, hSM, hBS, hFS⟩ :=
    exists_conj_le_pGroup' (K := M) (X := B) (Y := F) hBM
      (isPGroup_of_isElemAbelian' hB.1.1.2.1) hFM (isPGroup_of_isElemAbelian' hF.1.1.2.1)
  have hF' : inDp p M (GLBConj y F) := (h101i h hyM hB hF).2
  obtain ⟨B3, hB3B, hB3el, hB3c⟩ := exists_elemAbelian_card_pow_of_le_pRank' (k := 3) hB.1.2
  obtain ⟨F3, hF3F, hF3el, hF3c⟩ := exists_elemAbelian_card_pow_of_le_pRank' (k := 3) hF'.1.2
  have hB3S : IsEkIn p 3 S B3 := ⟨hB3B.trans hBS, hB3el, hB3c⟩
  have hF3S : IsEkIn p 3 S F3 := ⟨hF3F.trans hFS, hF3el, hF3c⟩
  have hchain := hI G p 3 hp (by norm_num) S hSp B3 F3 hB3S hF3S
  have key : ∀ C : Subgroup G,
      Relation.ReflTransGen
        (fun U V : Subgroup G => IsEkIn p 3 S U ∧ IsEkIn p 3 S V ∧ 2 ≤ CFSG.Open.pRank p (U ⊓ V))
        B3 C →
      (∃ E A : Subgroup G, inDDp p M E A) ∨
        ∃ X : Subgroup G, IsSCstar p M X ∧ C ≤ X ∧ inD p M X := by
    intro C hC
    induction hC with
    | refl => exact Or.inr ⟨B, hB.1, hB3B, hB⟩
    | @tail D C' _ hstep ih =>
      obtain ⟨-, hC'e, hrank⟩ := hstep
      rcases ih with hdone | ⟨X, -, hDX, hXD⟩
      · exact Or.inl hdone
      · obtain ⟨Y, hYs, hC'Y⟩ :=
          exists_isSCstar_above (M := M) (hC'e.1.trans hSM) hC'e.2.1 hC'e.2.2.ge
        by_cases hYD : IsUniquenessTwoLocal p Y M
        · exact Or.inr ⟨Y, hYs, hC'Y, ⟨hYs, hYD⟩⟩
        · exact Or.inl ⟨X, Y, hXD, ⟨hYs, hYD⟩,
            le_trans hrank (CFSG.SectionRank.pRank_mono hp.one_lt (inf_le_inf hDX hC'Y))⟩
  rcases key F3 hchain with hdone | ⟨X, -, hF3X, hXD⟩
  · exact hdone
  · have h3 : 3 ≤ CFSG.Open.pRank p (X ⊓ GLBConj y F) :=
      CFSG.SectionRank.le_pRank hp.one_lt (le_inf hF3X hF3F) hF3el hF3c
    exact ⟨X, GLBConj y F, hXD, hF', by omega⟩


theorem lemma103_of_input31_8 (hI : Input31_8) (hconj : IsUniquenessTwoLocal_conjStatement) :
    Lemma103Statement :=
  lemma103_of_inputs hI (lemma101_i_of_conj hconj)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

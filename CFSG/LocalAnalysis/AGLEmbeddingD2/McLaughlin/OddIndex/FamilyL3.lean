module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyL3P1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyL2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Main
public import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves

theorem isLThreeTwo_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X' ≃* X)
    (hX : IsLThreeTwo X) : IsLThreeTwo X' := by
  obtain ⟨d, hd, ⟨f⟩⟩ := hX
  exact ⟨d, hd, ⟨e.trans f⟩⟩

theorem isLThreeTwo_map_equiv {K G : Type} [Group K] [Group G] (e : K ≃* G) (Y : Subgroup K)
    (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    IsLThreeTwo (↥(Y.map e.toMonoidHom) ⧸ CFSG.pCore 2 ↥(Y.map e.toMonoidHom)) := by
  let eY : ↥Y ≃* ↥(Y.map e.toMonoidHom) := Y.equivMapOfInjective e.toMonoidHom e.injective
  have : (CFSG.pCore 2 ↥(Y.map e.toMonoidHom)).Normal := by
    unfold CFSG.pCore
    exact Subgroup.sSup_normal _ fun _ hN => hN.1
  exact isLThreeTwo_of_mulEquiv
    (QuotientGroup.congr (CFSG.pCore 2 ↥Y) (CFSG.pCore 2 ↥(Y.map e.toMonoidHom)) eY
      (CFSG.LieType.SteinbergBR.pCore_map_equiv 2 eY)).symm hY

@[expose] def OvergroupL32Core (G : Type) [Group G] [Finite G] : Prop :=
  (∀ X : Subgroup G, IsPGroup 3 X → IsCyclic X) →
    ∀ A W Y : Subgroup G, Nat.card A = 3 → Subgroup.normalizer (A : Set G) ≤ W → Y ≤ W →
      A ≤ Y → IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) → W = ⊤ ∨ ¬ 2 ∣ W.index

theorem overgroupL32Odd_of_core {K G : Type} [Group K] [Finite K] [Group G] [Finite G]
    (e : K ≃* G) (h : OvergroupL32Core G) : OvergroupL32Odd K := by
  intro _ _ _ hcyc A W Y hA hNW hYW hAY hY
  have hcycG : ∀ X : Subgroup G, IsPGroup 3 X → IsCyclic X := by
    intro X hX
    set e' := X.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
    have h1 : IsPGroup 3 ↥(X.map e.symm.toMonoidHom) := hX.map _
    have h2 := hcyc _ h1
    exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective
  have hcard : Nat.card (A.map e.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hA]
  have hN : Subgroup.normalizer ((A.map e.toMonoidHom : Subgroup G) : Set G) ≤
      W.map e.toMonoidHom := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNW
  have hidx : (W.map e.toMonoidHom).index = W.index := Subgroup.index_map_equiv W e
  rcases h hcycG _ _ _ hcard hN (Subgroup.map_mono hYW) (Subgroup.map_mono hAY)
      (isLThreeTwo_map_equiv e Y hY) with htop | hodd
  · left
    rw [← Subgroup.index_eq_one, ← hidx, htop, Subgroup.index_top]
  · exact Or.inr (hidx ▸ hodd)

variable {F : Type} [Field F] [Finite F]

theorem overgroupL32Core_SL3 (hq : Nat.card F % 3 = 2) (h5 : 5 ≤ Nat.card F)
    (hmax : GL2NonsplitMax F) : OvergroupL32Core (SL3 F) := by
  intro hcyc A W Y hA hNW hYW hAY hY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hroot := sq_add_self_add_one_ne_zero hq
  have hcube := exists_cube hq
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_eq_three hcyc hA card_A0
  set cg := (MulAut.conj g).toMonoidHom
  have hNW' : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W.map cg := by
    rw [hg, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNW
  have hYW' : Y.map cg ≤ W.map cg := Subgroup.map_mono hYW
  have hY' := isLThreeTwo_map_equiv (MulAut.conj g) Y hY
  have hW' : ¬ Group.IsSolvable ↥(W.map cg) := by
    intro hs
    apply not_isPSolvable_of_isLThreeTwo hY'
    have hsY : Group.IsSolvable ↥(Y.map cg) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYW')
        (Subgroup.inclusion_injective hYW')
    exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5.isPSolvable_of_isSolvable Nat.prime_three hsY
  have hidx : (W.map cg).index = W.index := Subgroup.index_map_equiv W (MulAut.conj g)
  have hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) →
        lev X ∈ W.map cg :=
    fun X hX => hNW' (lev_mem_normalizer_A0 (mem_Nt_of_comm hX))
  rcases Nat.even_or_odd (Nat.card F) with he | ho
  ·
    have hF : 2 ∣ Nat.card F := even_iff_two_dvd.mp he
    left
    rw [← Subgroup.index_eq_one, ← hidx]
    have hW'top : W.map cg = ⊤ := by
      rcases le_P1_or_le_P2_or_transitive hroot hcube hlev with h | h | htr
      · exact (false_of_le_P1_of_isLThreeTwo hF (hYW'.trans h) hY').elim
      · exact (false_of_le_P2_of_isLThreeTwo hF (hYW'.trans h) hY').elim
      · have hlevY : ∀ X : GL (Fin 2) F,
            (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) →
              lev X ∈ W.map cg ⊓ P1 :=
          fun X hX => ⟨hlev X hX, lev_mem_P1 X⟩
        rcases inf_Q1_eq_bot_or_le hroot hcube hlevY with hb | hle
        · exact (false_of_transitive_of_isLThreeTwo hF hYW' htr hb hY').elim
        · exact eq_top_of_Q1_le_of_transitive htr (hle.trans inf_le_left)
    rw [hW'top, Subgroup.index_top]
  ·
    right
    rw [← hidx]
    have hodd2 : Odd (Nat.card F ^ 2 + Nat.card F + 1) := by
      have : Odd (Nat.card F ^ 2 + Nat.card F + 1) := by
        have hev : Even (Nat.card F ^ 2 + Nat.card F) := by
          rw [show Nat.card F ^ 2 + Nat.card F = Nat.card F * (Nat.card F + 1) by ring]
          exact Nat.even_mul_succ_self _
        exact hev.add_one
      exact this
    have hnd : ∀ n : ℕ, Odd n → ¬ 2 ∣ n := fun n hn => by
      rintro ⟨k, rfl⟩
      obtain ⟨m, hm⟩ := hn
      omega
    rcases index_cases_SL3 hq h5 hmax hNW' hW' with htop | h | h | h
    · rw [htop, Subgroup.index_top]
      exact hnd 1 odd_one
    · rw [h]
      exact hnd _ ho.pow
    · rw [h]
      exact hnd _ hodd2
    · rw [h]
      exact hnd _ (ho.pow.mul hodd2)

theorem overgroupL32L3_of_max
    (hmax : ∀ (F : Type) [Field F] [Finite F], Nat.card F % 3 = 2 → 5 ≤ Nat.card F →
      GL2NonsplitMax F) : OvergroupL32L3 := by
  intro K _ _ d q hq hd ⟨e⟩
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := GaloisField q.p q.exponent
  have hF : Nat.card F = q.card := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
  have hqF : Nat.card F % 3 = 2 := by rw [hF]; exact hq
  have h5 : 5 ≤ Nat.card F := by
    rw [hF]
    have hdup := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).2
    rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
    have h2 : 2 ≤ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact (Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt)
    omega
  exact overgroupL32Odd_of_core
    ((e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
      (pslEquivSL3 hqF))
    (overgroupL32Core_SL3 hqF h5 (hmax F hqF h5))

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

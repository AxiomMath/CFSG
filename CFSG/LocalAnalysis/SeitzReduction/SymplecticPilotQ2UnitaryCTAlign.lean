module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignEdge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.SeitzReduction.LinearPilot (pairEmbed pairEmbed_apply)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups commutatorElement

section Levi

variable {K F : Type} [Field K] [Field F] [CharP K 2] {N ε : ℕ} {hε : ε ≤ 1} {σ : F ≃+* F}
  {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}

omit [CharP K 2] in
theorem ctuCoord_e_ne_f (l : Fin N) :
    ctuCoord N ε (Sum.inl (Sum.inl l)) ≠ ctuCoord N ε (Sum.inl (Sum.inr l)) := fun h => by
  have := (ctuCoord N ε).injective h
  simp at this

theorem ctuToSL_ctuEmbed_nsElt (l : Fin N) :
    ctuToSL σ (2 * N + ε) (ctuEmbed ε hε σ ι hι (nsElt l)) =
      pairEmbed (ctuCoord_e_ne_f (ε := ε) l) (zThreeSL (K := F)) := by
  apply Subtype.ext
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  rw [coe_ctuToSL, ctuEmbed_apply_ctuCoord, pairEmbed_apply, nsElt, mat_longBlock]
  simp only [Finset.mem_insert, Finset.mem_singleton, (ctuCoord N ε).injective.eq_iff,
    coe_zThreeSL, zThreeMat]
  rcases w with (p | p) | i <;> rcases w' with (q | q) | j <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      map_apply, Matrix.zero_apply, Matrix.one_apply, CFSG.LieType.Steinberg.Sp.blockMat,
      of_apply, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, false_and, and_false, false_or, or_false, ite_false] <;>
    split_ifs <;> aesop

variable [Finite F] [CharP F 2] {f : ℕ}

theorem perfectCore_ctuBlock_inf_centralizer_nsTorus (hF : Nat.card F = (2 ^ f) ^ 2)
    (hε : ε ≤ 1) {ι : K →+* F} (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c) {k l : Fin N}
    (h3 : 3 ≤ 2 * ({k, l} : Finset (Fin N))ᶜ.card + ε)
    (hq : ¬(2 * ({k, l} : Finset (Fin N))ᶜ.card + ε = 3 ∧ 2 ^ f = 2)) :
    perfectCore (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)) ⊓
      centralizer (((nsTorusSp K l).map (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι) :
        Subgroup (SU (unitaryInvolution F 2 f) (2 * N + ε))) :
          Set (SU (unitaryInvolution F 2 f) (2 * N + ε)))) =
      ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) := by
  set σ := unitaryInvolution F 2 f with hσdef
  set C := ctuBlock σ ε ({k} : Finset (Fin N)) ⊓
    centralizer (((nsTorusSp K l).map (ctuEmbed ε hε σ ι hι) :
      Subgroup (SU σ (2 * N + ε))) : Set (SU σ (2 * N + ε))) with hC
  have hab : ctuCoord N ε (Sum.inl (Sum.inl l)) ≠ ctuCoord N ε (Sum.inl (Sum.inr l)) :=
    ctuCoord_e_ne_f l
  set a := ctuCoord N ε (Sum.inl (Sum.inl l)) with ha
  set b := ctuCoord N ε (Sum.inl (Sum.inr l)) with hb
  have hent : ∀ x ∈ C, (∀ r, r ≠ a → r ≠ b →
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) r a = 0 ∧
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) r b = 0 ∧
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a r = 0 ∧
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) b r = 0) ∧
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) b a =
        -((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b ∧
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) b b =
        ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a a -
          ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b := by
    intro x hx
    have hc : x * ctuEmbed ε hε σ ι hι (nsElt l) = ctuEmbed ε hε σ ι hι (nsElt l) * x :=
      (mem_centralizer_iff.1 hx.2 _ ⟨nsElt l, mem_zpowers _, rfl⟩).symm
    have hc' := congrArg (ctuToSL σ (2 * N + ε)) hc
    rw [map_mul, map_mul, ctuToSL_ctuEmbed_nsElt] at hc'
    exact entries_of_commute_pairEmbed_zThree hab hc'
  set β : SU σ (2 * N + ε) → Matrix (Fin 2) (Fin 2) F := fun x =>
    !![((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a a,
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b;
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) b a,
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) b b]
    with hβdef
  have hsum : ∀ x ∈ C, ∀ y : SU σ (2 * N + ε), ∀ i, (i = a ∨ i = b) → ∀ j,
      (((x * y : SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) i j =
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) i a *
          ((y : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a j +
        ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) i b *
          ((y : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) b j := by
    intro x hx y i hi j
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add a b hab]
    · intro t _ ht
      rcases hi with rfl | rfl
      · rw [((hent x hx).1 t ht.1 ht.2).2.2.1, zero_mul]
      · rw [((hent x hx).1 t ht.1 ht.2).2.2.2, zero_mul]
    · simp
    · simp
  have hmul : ∀ x ∈ C, ∀ y : SU σ (2 * N + ε), β (x * y) = β x * β y := by
    intro x hx y
    simp only [hβdef]
    rw [hsum x hx y a (Or.inl rfl) a, hsum x hx y a (Or.inl rfl) b,
      hsum x hx y b (Or.inr rfl) a, hsum x hx y b (Or.inr rfl) b]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hβ1 : β 1 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hβdef, hab, hab.symm]
  have hcomm : ∀ x ∈ C, ∀ y ∈ C, β x * β y = β y * β x := by
    intro x hx y hy
    obtain ⟨-, hx1, hx2⟩ := hent x hx
    obtain ⟨-, hy1, hy2⟩ := hent y hy
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hβdef, Matrix.mul_apply, Fin.sum_univ_two, hx1, hx2, hy1, hy2] <;> ring
  have hinv : ∀ x ∈ C, β x * β x⁻¹ = 1 := fun x hx => by
    rw [← hmul x hx, mul_inv_cancel, hβ1]
  apply le_antisymm
  · refine (CFSG.Quasithin.perfectCore_le_derivedSeriesOf C 1).trans ?_
    rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero,
      Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hc : ⁅g₁, g₂⁆ ∈ C := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
    have hβc : β ⁅g₁, g₂⁆ = 1 := by
      rw [commutatorElement_def, hmul _ (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)),
        hmul _ (mul_mem hg₁ hg₂), hmul _ hg₁, hcomm g₁ hg₁ g₂ hg₂, Matrix.mul_assoc (β g₂),
        hinv g₁ hg₁, Matrix.mul_one, hinv g₂ hg₂]
    have hz := hent _ hc
    have e1 := congrFun (congrFun hβc 0) 0
    have e2 := congrFun (congrFun hβc 0) 1
    have e3 := congrFun (congrFun hβc 1) 0
    have e4 := congrFun (congrFun hβc 1) 1
    simp only [hβdef, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, one_apply_eq, one_apply_ne (zero_ne_one (α := Fin 2)),
      one_apply_ne (one_ne_zero (α := Fin 2))] at e1 e2 e3 e4
    have hcl : ⁅g₁, g₂⁆ ∈ ctuBlock σ ε ({l} : Finset (Fin N)) := by
      rw [mem_ctuBlock]
      intro r t hrt
      by_cases hrt' : r = t
      · subst hrt'
        rw [one_apply_eq]
        have hr : r ∈ ctuPlanes ε ({l} : Finset (Fin N)) := hrt.elim id id
        rcases eq_or_eq_of_mem_ctuPlanes_singleton hr with h | h
        · rw [h]
          exact e1
        · rw [h]
          exact e4
      · rw [one_apply_ne hrt']
        rcases hrt with hr | ht
        · rcases eq_or_eq_of_mem_ctuPlanes_singleton hr with h | h
          · rw [h] at hrt' ⊢
            by_cases htb : t = b
            · rw [htb]
              exact e2
            · exact (hz.1 t (Ne.symm hrt') htb).2.2.1
          · rw [h] at hrt' ⊢
            by_cases hta : t = a
            · rw [hta]
              exact e3
            · exact (hz.1 t hta (Ne.symm hrt')).2.2.2
        · rcases eq_or_eq_of_mem_ctuPlanes_singleton ht with h | h
          · rw [h] at hrt' ⊢
            by_cases hrb : r = b
            · rw [hrb]
              exact e3
            · exact (hz.1 r hrt' hrb).1
          · rw [h] at hrt' ⊢
            by_cases hra : r = a
            · rw [hra]
              exact e2
            · exact (hz.1 r hra hrt').2.1
    exact mem_ctuBlock_pair hc.1 hcl
  · refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ (commutator_ctuBlock_eq hF hε h3 hq)
    intro x hx
    refine Subgroup.mem_inf.2 ⟨ctuBlock_pair_le_left _ k l hx, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hyl : y ∈ spBlock K ({l} : Finset (Fin N)) := by
      rw [spBlock_singleton]
      exact nsTorusSp_le_longRootSp2 l hy
    exact (commute_ctuBlock_ctuEmbed (ctuBlock_pair_le_right _ k l hx) hyl).symm

end Levi


section Overlap

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N ε : ℕ}
  {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1} {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}

theorem NsUniParam.injOn_ctuBlock (hF : Nat.card F = (2 ^ f) ^ 2) (hN : 3 ≤ N) {k l : Fin N}
    (hkl : k ≠ l) (P : NsUniParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    {x y : ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))}
    (hx : (x : SU (unitaryInvolution F 2 f) (2 * N + ε)) ∈
      ctuBlock (unitaryInvolution F 2 f) ε ({l} : Finset (Fin N)))
    (hy : (y : SU (unitaryInvolution F 2 f) (2 * N + ε)) ∈
      ctuBlock (unitaryInvolution F 2 f) ε ({l} : Finset (Fin N)))
    (hxy : P.Φ x = P.Φ y) : x = y := by
  have hc := card_compl_singleton_ctua k
  have hker : x * y⁻¹ ∈ P.Φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  have h1 := eq_one_of_mem_center_ctuBlock hF hε (by omega)
    (fun h => by have := (Prod.mk.inj h).1; omega) (P.ker_le hker) (k := l)
    (by simpa using Ne.symm hkl) (mul_mem hx (inv_mem hy))
  exact mul_inv_eq_one.1 h1

omit [CharP K 2] [Finite F] [CharP F 2] in
theorem nsTorusSp_le_spBlock_compl {k l : Fin N} (hkl : k ≠ l) {y : StatedSp N K}
    (hy : y ∈ nsTorusSp K l) : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ := by
  have h1 : y ∈ spBlock K ({l} : Finset (Fin N)) := by
    rw [spBlock_singleton]
    exact nsTorusSp_le_longRootSp2 l hy
  exact spBlock_mono (by simpa using hkl) h1

theorem NsUniParam.map_nsTorus_eq {k : Fin N}
    (P : NsUniParam ε hε (unitaryInvolution F 2 f) ι hι e k) {l : Fin N} (hkl : k ≠ l) :
    (((nsTorusSp K l).map (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι)).subgroupOf
      (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)))).map P.Φ =
        modelToG e (nsTorusSp K l) := by
  ext g
  constructor
  · rintro ⟨x, ⟨y, hy, hyx⟩, rfl⟩
    have hx : x = ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y,
        ctuEmbed_mem_ctuBlock_iff.2 (nsTorusSp_le_spBlock_compl hkl hy)⟩ :=
      Subtype.ext hyx.symm
    rw [hx, P.N1 y (nsTorusSp_le_spBlock_compl hkl hy)]
    exact UnitaryPilot.symm_mem_modelToG e hy
  · intro hg
    obtain ⟨y, hy, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
    exact ⟨⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y,
      ctuEmbed_mem_ctuBlock_iff.2 (nsTorusSp_le_spBlock_compl hkl hy)⟩, ⟨y, hy, rfl⟩,
      P.N1 y (nsTorusSp_le_spBlock_compl hkl hy)⟩

theorem NsUniParam.map_overlap_eq [Finite G] [Finite K] (hF : Nat.card F = (2 ^ f) ^ 2)
    (hN : 4 ≤ N) {k : Fin N} (P : NsUniParam ε hε (unitaryInvolution F 2 f) ι hι e k) {l : Fin N}
    (hkl : k ≠ l) :
    ((ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N))).subgroupOf
      (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)))).map P.Φ =
        centralizerPerfectCore (modelToG e (nsTorusSp K k) ⊔ modelToG e (nsTorusSp K l)) := by
  have hc := card_compl_pair_ctua hkl
  rw [F4Pilot.centralizerPerfectCore_sup, ← P.range_eq, ← P.map_nsTorus_eq hkl,
    perfectCore_range_inf_centralizer_map P.Φ P.ker_le]
  congr 1
  apply Subgroup.map_injective
    (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))).subtype_injective
  have hXle : (nsTorusSp K l).map (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι) ≤
      ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ctuEmbed_mem_ctuBlock_iff.2 (nsTorusSp_le_spBlock_compl hkl hy)
  have hA : (((nsTorusSp K l).map (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι)).subgroupOf
      (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)))).map
        (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))).subtype =
      (nsTorusSp K l).map (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι) := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hXle]
  have hB : ((ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N))).subgroupOf
      (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)))).map
        (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))).subtype =
      ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr (ctuBlock_pair_le_left _ k l)]
  rw [hB, CFSG.Quasithin.map_perfectCore, ← ct_inf_centralizer_map_subtype_eq, hA,
    perfectCore_ctuBlock_inf_centralizer_nsTorus hF hε hι (by omega)
      (fun h => by have := h.1; omega)]

end Overlap

section TwistBy

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N ε : ℕ}
  {F : Type} [Field F] {hε : ε ≤ 1} {σ : F ≃+* F} {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}
  {e : L ≃* StatedSp N K}

@[expose] noncomputable def NsUniParam.twistBy {k : Fin N} (P : NsUniParam ε hε σ ι hι e k)
    {T : MulAut (SU σ (2 * N + ε))} (hT : CtuaAdmissible hε σ ι hι T) :
    NsUniParam ε hε σ ι hι e k where
  Φ := P.Φ.comp (hT.restrict {k}).toMonoidHom
  ker_le := by
    intro x hx
    have hx' : hT.restrict {k} x ∈ P.Φ.ker := hx
    have h1 := P.ker_le hx'
    rw [mem_center_iff] at h1 ⊢
    intro g
    apply (hT.restrict {k}).injective
    rw [map_mul, map_mul]
    exact h1 _
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, P.range_eq]
  N1 y hy := by
    change P.Φ (hT.restrict {k} ⟨ctuEmbed ε hε σ ι hι y, _⟩) = _
    have h1 : hT.restrict {k} ⟨ctuEmbed ε hε σ ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ =
        ⟨ctuEmbed ε hε σ ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ := Subtype.ext (hT.fix y)
    rw [h1]
    exact P.N1 y hy

theorem NsUniParam.twistBy_Φ_apply {k : Fin N} (P : NsUniParam ε hε σ ι hι e k)
    {T : MulAut (SU σ (2 * N + ε))} (hT : CtuaAdmissible hε σ ι hι T) (x : ctuBlock σ ε {k}) :
    (P.twistBy hT).Φ x = P.Φ (hT.restrict {k} x) := rfl

end TwistBy

section Edge

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}

theorem NsUniParam.exists_twist_of_overlap (hKc : Nat.card K = 2 ^ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hN : 4 ≤ N) {k l : Fin N} (hkl : k ≠ l)
    (P : NsUniParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    (Q : NsUniParam ε hε (unitaryInvolution F 2 f) ι hι e l) :
    ∃ (ν : Fˣ) (hν : unitaryInvolution F 2 f ν * ν = 1) (b : Bool),
      ∀ (x : SU (unitaryInvolution F 2 f) (2 * N + ε))
        (hx : x ∈ ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N))),
        P.Φ ⟨x, ctuBlock_pair_le_left _ k l hx⟩ =
          Q.Φ ⟨ctuaTwist hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b x,
            ctuBlock_pair_le_right _ k l ((ctuaTwist_mem_ctuBlock_iff hν b _ x).2 hx)⟩ := by
  have hc := card_compl_pair_ctua hkl
  set φP : ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) →* G :=
    P.Φ.comp (Subgroup.inclusion (ctuBlock_pair_le_left _ k l)) with hφP
  set φQ : ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) →* G :=
    Q.Φ.comp (Subgroup.inclusion (ctuBlock_pair_le_right _ k l)) with hφQ
  have hPinj : Function.Injective φP := fun x y h => by
    have h' := P.injOn_ctuBlock hF (by omega) hkl (ctuBlock_pair_le_right _ k l x.2)
      (ctuBlock_pair_le_right _ k l y.2) h
    exact Subtype.ext (congrArg (fun w : ctuBlock (unitaryInvolution F 2 f) ε
      ({k} : Finset (Fin N)) => (w : SU (unitaryInvolution F 2 f) (2 * N + ε))) h')
  have hQinj : Function.Injective φQ := fun x y h => by
    have h' := Q.injOn_ctuBlock hF (by omega) (Ne.symm hkl) (ctuBlock_pair_le_left _ k l x.2)
      (ctuBlock_pair_le_left _ k l y.2) h
    exact Subtype.ext (congrArg (fun w : ctuBlock (unitaryInvolution F 2 f) ε
      ({l} : Finset (Fin N)) => (w : SU (unitaryInvolution F 2 f) (2 * N + ε))) h')
  have hrange : ∀ {m : Fin N} (Φ : ctuBlock (unitaryInvolution F 2 f) ε ({m} : Finset (Fin N)) →* G)
      (h : ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) ≤
        ctuBlock (unitaryInvolution F 2 f) ε ({m} : Finset (Fin N))),
      (Φ.comp (Subgroup.inclusion h)).range =
        ((ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N))).subgroupOf
          (ctuBlock (unitaryInvolution F 2 f) ε ({m} : Finset (Fin N)))).map Φ := by
    intro m Φ h
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion h y, mem_subgroupOf.2 y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, mem_subgroupOf.1 hy⟩, rfl⟩
  have hr : φP.range = φQ.range := by
    rw [hφP, hφQ, hrange P.Φ, hrange Q.Φ, P.map_overlap_eq hF hN hkl]
    have h3 := Q.map_overlap_eq hF hN (Ne.symm hkl)
    rw [show ({l, k} : Finset (Fin N)) = {k, l} from Finset.pair_comm l k] at h3
    rw [h3, sup_comm]
  set θ : MulAut (ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N))) :=
    ((MonoidHom.ofInjective hPinj).trans (MulEquiv.subgroupCongr hr)).trans
      (MonoidHom.ofInjective hQinj).symm with hθdef
  have hθ : ∀ y, φQ (θ y) = φP y := by
    intro y
    have h := (MonoidHom.ofInjective hQinj).apply_symm_apply
      (MulEquiv.subgroupCongr hr (MonoidHom.ofInjective hPinj y))
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hfix : ∀ (y : StatedSp N K) (hy : y ∈ spBlock K ({k, l} : Finset (Fin N))ᶜ),
      θ ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ =
        ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ := by
    intro y hy
    have hyk : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ :=
      spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hy
    have hyl : y ∈ spBlock K ({l} : Finset (Fin N))ᶜ :=
      spBlock_mono (Finset.compl_subset_compl.2 (by simp)) hy
    apply hQinj
    rw [hθ]
    exact (P.N1 y hyk).trans (Q.N1 y hyl).symm
  obtain ⟨ν, hν, b, htw⟩ := exists_ctuaTwist_of_mulAut_fix hKc hF hf hε hι
    (R := ({k, l} : Finset (Fin N))) (by omega) θ hfix
  refine ⟨ν, hν, b, fun x hx => ?_⟩
  have h1 := hθ ⟨x, hx⟩
  rw [hφP, hφQ, MonoidHom.comp_apply, MonoidHom.comp_apply] at h1
  exact h1.symm.trans (congrArg Q.Φ (Subtype.ext (htw ⟨x, hx⟩)))

end Edge

end CFSG.SeitzReduction.SymplecticPilot

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTower
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTransport
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoNode
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoBlock
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits
open scoped commutatorElement

section InnerOn

variable {G : Type*} [Group G]

@[expose] def innerActOn (S : Subgroup G) : Subgroup G where
  carrier := {g | ∃ p ∈ S, ∀ s ∈ S, g * s * g⁻¹ = p * s * p⁻¹}
  mul_mem' := by
    rintro g₁ g₂ ⟨p₁, hp₁, h₁⟩ ⟨p₂, hp₂, h₂⟩
    refine ⟨p₁ * p₂, S.mul_mem hp₁ hp₂, fun s hs => ?_⟩
    have h3 : g₁ * g₂ * s * (g₁ * g₂)⁻¹ = g₁ * (g₂ * s * g₂⁻¹) * g₁⁻¹ := by group
    rw [h3, h₂ s hs, h₁ _ (S.mul_mem (S.mul_mem hp₂ hs) (S.inv_mem hp₂))]
    group
  one_mem' := ⟨1, S.one_mem, fun s _ => by group⟩
  inv_mem' := by
    rintro g ⟨p, hp, h⟩
    refine ⟨p⁻¹, S.inv_mem hp, fun s hs => ?_⟩
    have h1 := h (p⁻¹ * s * p) (S.mul_mem (S.mul_mem (S.inv_mem hp) hs) hp)
    have h2 : g * (p⁻¹ * s * p) * g⁻¹ = s := by rw [h1]; group
    calc g⁻¹ * s * g⁻¹⁻¹ = g⁻¹ * (g * (p⁻¹ * s * p) * g⁻¹) * g⁻¹⁻¹ := by rw [h2]
      _ = p⁻¹ * s * p⁻¹⁻¹ := by group

theorem mem_innerActOn {S : Subgroup G} {g : G} :
    g ∈ innerActOn S ↔ ∃ p ∈ S, ∀ s ∈ S, g * s * g⁻¹ = p * s * p⁻¹ :=
  Iff.rfl

theorem le_innerActOn (S : Subgroup G) : S ≤ innerActOn S :=
  fun g hg => ⟨g, hg, fun _ _ => rfl⟩

theorem blockOK_innerActOn (S : Subgroup G) : BlockOK (innerActOn S) S :=
  fun _ hg _ _ _ => Or.inl hg

end InnerOn

section OneNode

variable {K Y : Type} [Group K] [Group Y] [Finite K] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem normal_posUnipotentExcept_subgroupOf (h : BorelQuotient D n H π M) {A : Subgroup K}
    (hBA : borel D H ≤ A) {i : Fin D.rank} (hI : negIndices D A = {i}) :
    ((posUnipotentExcept D i).subgroupOf A).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (posUnipotentExcept_le_of_borel_le hBA i)).mpr
    (le_normalizer_posUnipotentExcept_of_negIndices_eq h hBA hI)

theorem innerActOn_oneNode (h : BorelQuotient D n H π M) {A : Subgroup K} (hBA : borel D H ≤ A)
    {i : Fin D.rank} (hI : negIndices D A = {i})
    (hT : ∀ k, ∀ t ∈ H k, ∃ p ∈ rankOne D.rootGroup i, ∀ l ∈ rankOne D.rootGroup i,
      t * l * t⁻¹ = p * l * p⁻¹) (a : ↥A) :
    haveI := normal_posUnipotentExcept_subgroupOf h hBA hI
    QuotientGroup.mk' ((posUnipotentExcept D i).subgroupOf A) a ∈
      innerActOn (((rankOne D.rootGroup i).subgroupOf A).map
        (QuotientGroup.mk' ((posUnipotentExcept D i).subgroupOf A))) := by
  classical
  haveI := normal_posUnipotentExcept_subgroupOf h hBA hI
  set U : Subgroup ↥A := (posUnipotentExcept D i).subgroupOf A
  set S : Subgroup (↥A ⧸ U) := ((rankOne D.rootGroup i).subgroupOf A).map (QuotientGroup.mk' U)
  have hUA := posUnipotentExcept_le_of_borel_le hBA i
  have hLA : rankOne D.rootGroup i ≤ A := rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl)
  have hSmem : ∀ (l : K) (hl : l ∈ rankOne D.rootGroup i), QuotientGroup.mk' U ⟨l, hLA hl⟩ ∈ S :=
    fun l hl => ⟨⟨l, hLA hl⟩, hl, rfl⟩
  set W : Subgroup K := ((innerActOn S).comap (QuotientGroup.mk' U)).map A.subtype
  have hHk : ∀ k, H k ≤ W := by
    intro k t ht
    have htA : t ∈ A := hBA (iSup_le_borel (le_iSup H k ht))
    refine ⟨⟨t, htA⟩, ?_, rfl⟩
    obtain ⟨p, hp, hpl⟩ := hT k t ht
    refine ⟨QuotientGroup.mk' U ⟨p, hLA hp⟩, hSmem p hp, ?_⟩
    rintro _ ⟨⟨l, hlA⟩, hl, rfl⟩
    have hl' : l ∈ rankOne D.rootGroup i := hl
    rw [← map_mul, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul]
    congr 1
    exact Subtype.ext (hpl l hl')
  have hL : rankOne D.rootGroup i ≤ W := fun l hl =>
    ⟨⟨l, hLA hl⟩, le_innerActOn S (hSmem l hl), rfl⟩
  have hUW : posUnipotentExcept D i ≤ W := fun u hu => by
    refine ⟨⟨u, hUA hu⟩, ?_, rfl⟩
    have : QuotientGroup.mk' U ⟨u, hUA hu⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hu
    show QuotientGroup.mk' U ⟨u, hUA hu⟩ ∈ innerActOn S
    rw [this]
    exact (innerActOn S).one_mem
  have hAW : A ≤ W := (le_torus_sup_of_negIndices_eq h hBA hI).trans
    (sup_le (iSup_le hHk) (sup_le hL hUW))
  obtain ⟨w, hw, hwa⟩ := hAW a.2
  have : w = a := Subtype.ext hwa
  subst this
  exact hw

end OneNode

section LeviOneNode

variable {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} [L.Normal]
  {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem leviInnAt_of_oneNode (hPL : P ≤ L) (π : K →* ↥L) (h : BorelQuotient D n H π M)
    {i : Fin D.rank} (hBA : borel D H ≤ coverSub π P) (hI : negIndices D (coverSub π P) = {i})
    (hLU : rankOne D.rootGroup i ⊓ posUnipotentExcept D i = ⊥)
    (hT : ∀ k, ∀ t ∈ H k, ∃ p ∈ rankOne D.rootGroup i, ∀ l ∈ rankOne D.rootGroup i,
      t * l * t⁻¹ = p * l * p⁻¹)
    (hq : CFSG.Open.IsQuasisimple ↥(rankOne D.rootGroup i))
    (hZ : Subgroup.center ↥(rankOne D.rootGroup i) = ⊥)
    (hrk : Open.pRank 3 (perfectJoin P) ≤ 1) : LeviInnAt P := by
  classical
  set A : Subgroup K := coverSub π P
  haveI := normal_posUnipotentExcept_subgroupOf h hBA hI
  set U : Subgroup ↥A := (posUnipotentExcept D i).subgroupOf A with hU
  set Λ : Subgroup ↥A := (rankOne D.rootGroup i).subgroupOf A with hΛ
  set S : Subgroup (↥A ⧸ U) := Λ.map (QuotientGroup.mk' U)
  have hUA := posUnipotentExcept_le_of_borel_le hBA i
  have hLA : rankOne D.rootGroup i ≤ A := rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl)
  have hU2 : IsPGroup 2 U := (isPGroup_posUnipotentExcept h i).comap_subtype
  have hc : ∀ a b : ↥A, ⁅a, b⁆ ∈ Λ ⊔ U := fun a b => by
    rw [hΛ, hU, ← Subgroup.subgroupOf_sup hLA hUA, Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using commutator_mem_of_negIndices_eq h hBA hI a.2 b.2
  have hΛU : Λ ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx : (x : K) ∈ rankOne D.rootGroup i ⊓ posUnipotentExcept D i := ⟨hx1, hx2⟩
    rw [hLU, Subgroup.mem_bot] at hx
    exact (Subgroup.mem_bot).2 (Subtype.ext hx)
  obtain ⟨eΛ⟩ := nonempty_mulEquiv_oneBlock U Λ hΛU
  have e : ↥(rankOne D.rootGroup i) ≃* ↥S := (Subgroup.subgroupOfEquivOfLe hLA).symm.trans eΛ
  have hqS : CFSG.Open.IsQuasisimple ↥S := isQuasisimple_of_mulEquiv e hq
  have hZS : Subgroup.center ↥S = ⊥ := by rw [← map_center_mulEquiv e, hZ, Subgroup.map_bot]
  refine leviInnAt_of_levi_data hPL π h.surj (fun z hz => h.ker_central z hz) A rfl
    (G := fun _ : Fin 1 => ↥A ⧸ U) (fun _ => S) (fun _ => innerActOn S)
    (MonoidHom.pi fun _ => QuotientGroup.mk' U) (isPGroup_ker_oneBlock U hU2)
    (pi_le_range_oneBlock U Λ) (commutator_range_oneBlock_le U Λ hc) (fun _ => Or.inl hqS)
    (fun x j => ?_) (fun j _ => blockOK_innerActOn S) (fun j E hE _ _ x hπx hβx => ?_) hrk
  · exact innerActOn_oneNode h hBA hI hT x
  · obtain ⟨e', he', he'x⟩ := hβx
    have h1 : QuotientGroup.mk' U x = e' := by
      have := congrFun he'x j
      simpa [MonoidHom.pi_apply] using this.symm
    have hxZ : (x : K) ∈ Subgroup.center K := h.ker_central _ hπx
    have hx_comm : ∀ y : ↥A, x * y = y * x := fun y =>
      Subtype.ext ((Subgroup.mem_center_iff.1 hxZ (y : K)).symm)
    have hcent : (⟨e', hE he'⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨s, y, -, rfl⟩
      apply Subtype.ext
      show QuotientGroup.mk' U y * e' = e' * QuotientGroup.mk' U y
      rw [← h1, ← map_mul, ← map_mul, hx_comm y]
    rw [hZS, Subgroup.mem_bot] at hcent
    have hmk : QuotientGroup.mk' U x = 1 := by rw [h1]; exact congrArg Subtype.val hcent
    have hxU : (x : K) ∈ posUnipotentExcept D i :=
      Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := U) x).1 hmk)
    obtain ⟨r, hr⟩ := isPGroup_posUnipotentExcept h i ⟨(x : K), hxU⟩
    have hr' : (x : K) ^ (2 ^ r) = 1 := by simpa using congrArg Subtype.val hr
    have hM : (x : K) ^ M = 1 := h.ker_pow _ hπx
    have hcop : Nat.Coprime (2 ^ r) M := Nat.Coprime.pow_left r (Nat.coprime_two_left.2 h.odd)
    have hx1 : (x : K) = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hr') (orderOf_dvd_of_pow_eq_one hM))
    exact Subtype.ext hx1

end LeviOneNode

section TorusInner

theorem exists_sl2Diag_conj_unitriangular {F : Type} [Field F] (a : Fˣ) :
    ∃ D : SpecialLinearGroup (Fin 2) F,
      (∀ c : F, D * sl2Upper c * D⁻¹ = sl2Upper ((a : F) ^ 2 * c)) ∧
      ∀ c : F, D * sl2Lower c * D⁻¹ = sl2Lower (((a⁻¹ : Fˣ) : F) ^ 2 * c) := by
  obtain ⟨D, hD⟩ : ∃ D : SpecialLinearGroup (Fin 2) F,
      (D : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] :=
    ⟨⟨_, by simp [Matrix.det_fin_two]⟩, rfl⟩
  refine ⟨D, fun c => ?_, fun c => ?_⟩
  · rw [mul_inv_eq_iff_eq_mul]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hD]
    fin_cases i <;> fin_cases j <;> simp [sl2Upper, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  · rw [mul_inv_eq_iff_eq_mul]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hD]
    fin_cases i <;> fin_cases j <;> simp [sl2Lower, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp

theorem g2_torus_conj_rankOne_inner
    {F : Type} [Field F] [Finite F] [CharP F 2] (i k : Fin (Tag.rank .G2))
    {t : ↥(adjointGroup .G2 F)} (ht : t ∈ torus (τ := .G2) F k) :
    ∃ p ∈ rankOne (rootGroup (rootOperatorFamily .G2) F) i,
      ∀ l ∈ rankOne (rootGroup (rootOperatorFamily .G2) F) i, t * l * t⁻¹ = p * l * p⁻¹ := by
  obtain ⟨u, rfl⟩ := ht
  obtain ⟨φ, -, hx, hy⟩ := g2_exists_sl2_hom (K := F) i
  have hr := rankOne_eq_range_of_sl2
    (adjDatum_isParametrization (F := rootOperatorFamily .G2) (K := F)
      (RootSystem.ofCartan (g2Datum F).isFiniteType (g2Datum F).divisible)
      (adjDatum_roots (rootOperatorFamily .G2) F))
    (fun c => (hx c).trans (xPar_simple i c).symm)
    (fun c => (hy c).trans (xPar_neg_simple i c).symm)
  set e : ℤ := Tag.cartan .G2 k i with he
  obtain ⟨μ0, hμ0⟩ := isSquare_of_charTwo' (((u ^ e : Fˣ) : F))
  have hμ0ne : μ0 ≠ 0 := by
    intro h0
    have := (u ^ e).ne_zero
    rw [hμ0, h0, mul_zero] at this
    exact this rfl
  set μ : Fˣ := Units.mk0 μ0 hμ0ne
  have hμsq : (μ : F) ^ 2 = ((u ^ e : Fˣ) : F) := by
    rw [hμ0, Units.val_mk0, sq]
  have hμinv : ((μ⁻¹ : Fˣ) : F) ^ 2 = ((u ^ (-e) : Fˣ) : F) := by
    rw [_root_.zpow_neg, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, ← hμsq, inv_pow]
  obtain ⟨D, hDu, hDl⟩ := exists_sl2Diag_conj_unitriangular (F := F) μ
  have hsum1 : ∑ j, Tag.cartan .G2 k j *
      ((simpleRoot .G2 i : Root .G2) : Fin (Tag.rank .G2) → ℤ) j = e := by
    simp [simpleRoot, Pi.single_apply, he]
  have hsum2 : ∑ j, Tag.cartan .G2 k j *
      ((-simpleRoot .G2 i : Root .G2) : Fin (Tag.rank .G2) → ℤ) j = -e := by
    simp [simpleRoot, Pi.single_apply, he]
  have hconj : ∀ M : SpecialLinearGroup (Fin 2) F,
      torusElement .G2 F k u * φ M * (torusElement .G2 F k u)⁻¹ = φ (D * M * D⁻¹) := by
    intro M
    have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
        MonoidHom.eqLocus ((MulAut.conj (torusElement .G2 F k u)).toMonoidHom.comp φ)
          (φ.comp (MulAut.conj D).toMonoidHom) := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · show torusElement .G2 F k u * φ (sl2Upper c) * (torusElement .G2 F k u)⁻¹ =
          φ (D * sl2Upper c * D⁻¹)
        rw [hDu, hx, hx, (rootOperatorFamily .G2).torusElement_mul_eltElement_mul_inv, hsum1,
          hμsq]
      · show torusElement .G2 F k u * φ (sl2Lower c) * (torusElement .G2 F k u)⁻¹ =
          φ (D * sl2Lower c * D⁻¹)
        rw [hDl, hy, hy, (rootOperatorFamily .G2).torusElement_mul_eltElement_mul_inv, hsum2,
          hμinv]
    exact hle (Sp.mem_closure_sl2 M)
  refine ⟨φ D, ?_, fun l hl => ?_⟩
  · rw [hr]
    exact ⟨D, rfl⟩
  · rw [hr] at hl
    obtain ⟨M, rfl⟩ := hl
    exact (hconj M).trans (by rw [map_mul, map_mul, map_inv])

end TorusInner

theorem leviInnOn_g2
    (hGA : GriessAllModelsStatement) : LeviInnOn (IsLieOf IdxG2) := by
  intro Y _ _ L P hCP hG hLn _ _ hrk
  haveI := hLn
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_mulEquiv_g2 hGA hCP hG
  obtain ⟨T, hNT, hne, htop⟩ := exists_sylow_le_subgroupOf_of_compParab hCP
  obtain ⟨π', hQ, hBA, i, hI⟩ := exists_single_node_g2 e T hNT hne htop
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨eL⟩ := nonempty_sl2_mulEquiv_rankOne_g2 (F := GaloisField 2 f) i
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    sl2_isSimpleGroup h4
  have : IsSimpleGroup ↥(rankOne (g2Datum (GaloisField 2 f)).rootGroup i) :=
    eL.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(rankOne (g2Datum (GaloisField 2 f)).rootGroup i), a * b ≠ b * a :=
    ⟨eL (sl2Upper 1 * sl2Lower 1), eL (sl2Upper 1), fun h =>
      sl2_upper_lower_not_commute (eL.injective (by simpa [map_mul] using h))⟩
  obtain ⟨hqs, hZ, -⟩ := sl2Block_facts h4 eL
  exact leviInnAt_of_oneNode hCP.parab.1 π' hQ hBA hI
    (rankOne_inf_posUnipotentExcept_eq_bot hQ i hnc)
    (fun k t ht => g2_torus_conj_rankOne_inner i k ht) hqs hZ hrk

theorem fieldIndexOn_g2
    (hGA : GriessAllModelsStatement) : FieldIndexOn (IsLieOf IdxG2) :=
  fieldIndexOn_of_outPNice (fun _ _ _ _ _ _ hC _ => outPNice_three_of_idxG2 hC)
    (leviInnOn_g2 hGA)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

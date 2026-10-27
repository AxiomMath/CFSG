module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Eta
public import CFSG.ClassicalGroups.Orthogonal.ElementaryGroupIrreducible

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin

theorem isSimpleRep_comp {G : Type*} [Group G] {k W : Type*} [Field k] [AddCommGroup W]
    [Module k W] {ρ : Representation k G W} (hρ : IsSimpleRep ρ) (σ : G ≃* G) :
    IsSimpleRep (ρ.comp σ.toMonoidHom) := by
  refine ⟨hρ.1, fun W' hW => hρ.2 W' fun g w hw => ?_⟩
  have h := hW (σ.symm g) w hw
  simpa using h

private theorem perm_cover : ∀ a b : Fin 4, a ∈ ({0, 1, 3} : Finset (Fin 4)) →
    b ∈ ({0, 1, 3} : Finset (Fin 4)) →
    b = a ∨ TwistTag.D4.perm.symm b = a ∨
      TwistTag.D4.perm.symm (TwistTag.D4.perm.symm b) = a := by
  intro a b ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)

section General


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}

theorem isChevType_one_of_card_two (hK : Nat.card K = 2) {k W : Type*} [Field k]
    [AddCommGroup W] [Module k W] {ρ : Representation k (adjointGroup τ K) W} {y : W}
    {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)} (ht : IsChevType τ K 2 hw ρ y χ J) :
    IsChevType τ K 2 hw ρ y (fun _ => 1) J := by
  have hunits : Subsingleton Kˣ := by
    have h := natCard_units_lt (M₀ := K)
    rw [hK] at h
    exact Finite.card_le_one_iff_subsingleton.mp (by omega)
  have hone : ∀ t : Kˣ, t = 1 := fun t => Subsingleton.elim t 1
  have hd : ∀ (i : Fin τ.rank) (t : Kˣ), dC τ K i t = 1 := by
    intro i t
    rw [hone t, dC_one]
  have htorus : torusGroup τ K = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [torusGroup, Subgroup.closure_le]
    rintro - ⟨⟨i, t⟩, rfl⟩
    change torusElt τ K i t ∈ (⊥ : Subgroup (ModGL τ K))
    rw [hone t, torusElt_one]
    exact Subgroup.mem_bot.mpr rfl
  have hHone : ∀ h ∈ (chevDatum τ K 2 hw).H, h = 1 := by
    intro h hh
    have h1 : (h : ModGL τ K) ∈ torusGroup τ K := hh
    rw [htorus] at h1
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  have hchi : χ 1 = 1 := by
    have h1 : ρ (1 : adjointGroup τ K) y = χ 1 • y := ht.2.2.1 1 (Subgroup.one_mem _)
    rw [map_one, Module.End.one_apply] at h1
    have h2 : (1 : k) • y = χ 1 • y := by rw [one_smul, ← h1]
    exact (smul_left_injective k ht.2.1 h2).symm
  refine ⟨ht.1, ht.2.1, fun h hh => ?_, fun i => ?_⟩
  · rw [hHone h hh, map_one, Module.End.one_apply, one_smul]
  · have hiff : (∀ t : Kˣ, χ (dC τ K i t) = 1) ↔ True :=
      ⟨fun _ => trivial, fun _ t => by rw [hd i t, hchi]⟩
    rw [ht.2.2.2 i, hiff]
    simp

theorem eq_of_isChevType_univ (hK : Nat.card K = 2) {k W : Type*} [Field k] [Algebra K k]
    [CharP k 2] [AddCommGroup W] [Module k W] {ρ : Representation k (adjointGroup τ K) W}
    (hρ : IsSimpleRep ρ) {y : W} {χ : adjointGroup τ K → k}
    (ht : IsChevType τ K 2 hw ρ y χ Finset.univ) (g : adjointGroup τ K) (w : W) : ρ g w = w := by
  let ρ₀ : Representation k (adjointGroup τ K) k := Representation.trivial k (adjointGroup τ K) k
  have hρ₀ : IsSimpleRep ρ₀ := by
    refine ⟨inferInstance, fun W' _ => ?_⟩
    by_cases hbot : W' = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    refine eq_top_iff.mpr fun z _ => ?_
    have hz : z = (z / x) • x := by rw [smul_eq_mul, div_mul_cancel₀ z hx0]
    rw [hz]
    exact W'.smul_mem (z / x) hxW
  have ht₀ : IsChevType τ K 2 hw ρ₀ 1 (fun _ => 1) Finset.univ := by
    refine ⟨?_, one_ne_zero, ?_, ?_⟩
    · rw [CurtisDatum.mem_fixU]
      intro u _
      rfl
    · intro h _
      show (1 : k) = (1 : k) • (1 : k)
      rw [one_smul]
    · intro i
      have : Fintype K := Fintype.ofFinite K
      refine iff_of_true (Finset.mem_univ i) ⟨fun _ => rfl, ?_⟩
      have hterm : ∀ c : K, (ρ₀ (xC τ K i c * nC τ K i)) (1 : k) = 1 := fun c => rfl
      rw [heckeT_chevDatum]
      calc ∑ c : K, (ρ₀ (xC τ K i c * nC τ K i)) (1 : k)
          = ∑ _c : K, (1 : k) := Finset.sum_congr rfl fun c _ => hterm c
        _ = (Finset.univ : Finset K).card • (1 : k) := Finset.sum_const _
        _ = 0 := by
            rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK,
              show (2 : ℕ) • (1 : k) = (2 : k) by norm_num [nsmul_eq_mul]]
            exact CharP.cast_eq_zero k 2
  obtain ⟨β, hβ⟩ := iso_of_isChevType (p := 2) hρ hρ₀
    (isChevType_one_of_card_two hK ht) ht₀
  have hb : β (ρ g w) = β w := by
    rw [hβ g w]
    simp [ρ₀, Representation.trivial]
  exact β.injective hb

end General

section D4


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α}

variable (K) in
@[expose] noncomputable def natRep : Representation K (adjointGroup .D4 K) (Fin 4 ⊕ Fin 4 → K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((orthElementaryGroup (quadPlus 4 K)).subtype.comp (eta K).toMonoidHom)

theorem natRep_apply (g : adjointGroup .D4 K) (v : Fin 4 ⊕ Fin 4 → K) :
    natRep K g v = (eta K g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) v :=
  rfl

theorem isSimpleRep_natRep : IsSimpleRep (natRep K) := by
  refine ⟨inferInstance, fun W hW => ?_⟩
  refine CFSG.ClassicalGroups.Orthogonal.submodule_eq_bot_or_top_of_elementaryGroup_invariant
    (nondegenerate_polarBilin_quadPlus 4 K)
    ⟨fun i => CFSG.ClassicalGroups.Orthogonal.plusPair K (Fin.castLE (by norm_num : 2 ≤ 4) i),
      fun i j hij => ?_⟩ W ?_
  · refine CFSG.ClassicalGroups.Orthogonal.plusPair_orth ?_
    intro h
    exact hij (Fin.castLE_injective _ h)
  · intro g hg x hx
    have h1 := hW ((eta K).symm ⟨g, hg⟩) x hx
    simpa [natRep_apply] using h1

variable (K) in
@[expose] noncomputable def triality : adjointGroup .D4 K ≃* adjointGroup .D4 K :=
  twistEquiv TwistTag.D4 K (RingHom.id K) (surjective_ringHom_of_finite (K := K) (RingHom.id K))

private def trialityPerm : Equiv.Perm (Fin Tag.D4.rank) := TwistTag.D4.perm

omit [CharP K 2] in
private theorem triality_xC_mul_nC (i : Fin Tag.D4.rank) (c : K) :
    triality K (xC .D4 K i c * nC .D4 K i) =
      xC .D4 K (TwistTag.D4.perm i) c * nC .D4 K (TwistTag.D4.perm i) := by
  rw [map_mul]
  congr 1
  · simp only [triality]
    exact twistC_xElement (t := TwistTag.D4) (K := K) (σ := RingHom.id K) i c
  · simp only [triality]
    exact twistC_weylElement (t := TwistTag.D4) (K := K) (σ := RingHom.id K) i

private theorem heckeT_comp_triality {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    {ρ : Representation k (adjointGroup .D4 K) W} (i : Fin Tag.D4.rank) (y : W) :
    (chevDatum .D4 K 2 hw).heckeT (ρ.comp (triality K).toMonoidHom) i y
      = (chevDatum .D4 K 2 hw).heckeT ρ (TwistTag.D4.perm i) y := by
  have : Fintype K := Fintype.ofFinite K
  rw [heckeT_chevDatum (V := W) (ρ := ρ.comp (triality K).toMonoidHom) (i := i) (v := y),
    heckeT_chevDatum (V := W) (ρ := ρ) (i := TwistTag.D4.perm i) (v := y)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← triality_xC_mul_nC i c]
  rfl

theorem isChevType_comp_triality {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    {ρ : Representation k (adjointGroup .D4 K) W} {y : W} {J : Finset (Fin Tag.D4.rank)}
    (ht : IsChevType .D4 K 2 hw ρ y (fun _ => 1) J) :
    IsChevType .D4 K 2 hw (ρ.comp (triality K).toMonoidHom) y (fun _ => 1)
      (J.map TwistTag.D4.perm.symm.toEmbedding) := by
  have hσ : Function.Surjective (RingHom.id K) := fun x => ⟨x, rfl⟩
  refine ⟨?_, ht.2.1, ?_, fun i => ?_⟩
  · intro u hu
    have hFu : (triality K) u ∈ (chevDatum .D4 K 2 hw).U := by
      show (twistHom TwistTag.D4 K (RingHom.id K) (u : ModGL .D4 K)) ∈ posUnipotent .D4 K
      exact twistHom_mem_posUnipotent (t := TwistTag.D4) (K := K) (σ := RingHom.id K) hσ hu
    have h1 := ht.1 _ hFu
    simpa using h1
  · intro h hh
    have hFh : (triality K) h ∈ (chevDatum .D4 K 2 hw).H := by
      show (twistHom TwistTag.D4 K (RingHom.id K) (h : ModGL .D4 K)) ∈ torusGroup .D4 K
      exact twistHom_mem_torusGroup (t := TwistTag.D4) (K := K) (σ := RingHom.id K) hh
    have h1 := ht.2.2.1 _ hFh
    simpa using h1
  · have hmem : i ∈ J.map TwistTag.D4.perm.symm.toEmbedding ↔ TwistTag.D4.perm i ∈ J :=
      Finset.mem_map_equiv
    refine hmem.trans ?_
    refine (ht.2.2.2 (TwistTag.D4.perm i)).trans ?_
    rw [heckeT_comp_triality i y]

private theorem isChevType_comp_triality_erase {k W : Type*} [Field k] [AddCommGroup W]
    [Module k W] {ρ : Representation k (adjointGroup .D4 K) W} {y : W}
    {a b : Fin Tag.D4.rank}
    (ht : IsChevType .D4 K 2 hw ρ y (fun _ => 1) (Finset.univ.erase a))
    (h : TwistTag.D4.perm.symm a = b) :
    IsChevType .D4 K 2 hw (ρ.comp (triality K).toMonoidHom) y (fun _ => 1)
      (Finset.univ.erase b) := by
  have hbase := isChevType_comp_triality ht
  refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, fun i => ?_⟩
  have hmemiff : (i ∈ (Finset.univ : Finset (Fin Tag.D4.rank)).erase b) ↔
      (trialityPerm i ∈ (Finset.univ : Finset (Fin Tag.D4.rank)).erase a) := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hi hpi
      apply hi
      rw [← h, ← hpi]
      exact (Equiv.symm_apply_apply trialityPerm i).symm
    · intro hpi hi
      apply hpi
      rw [hi, ← h]
      exact Equiv.apply_symm_apply trialityPerm a
  have hmap : trialityPerm i ∈ (Finset.univ : Finset (Fin Tag.D4.rank)).erase a ↔
      ((∀ t : Kˣ, (fun _ => (1 : k)) (dC .D4 K i t) = 1) ∧
        (chevDatum .D4 K 2 hw).heckeT (ρ.comp (triality K).toMonoidHom) i y = 0) :=
    (Finset.mem_map_equiv).symm.trans (hbase.2.2.2 i)
  exact hmemiff.trans hmap

theorem exists_isChevType_natRep (hK : Nat.card K = 2) :
    ∃ (y : Fin 4 ⊕ Fin 4 → K) (e : Fin 4), e ∈ ({0, 1, 3} : Finset (Fin 4)) ∧
      IsChevType .D4 K 2 hw (natRep K) y (fun _ => 1) (Finset.univ.erase e) := by
  obtain ⟨y, χ, J, ht⟩ := exists_isChevType (p := 2) (k := K) (hw := hw)
    (ρ := natRep K) isSimpleRep_natRep
  have ht' : IsChevType .D4 K 2 hw (natRep K) y (fun _ => 1) J :=
    isChevType_one_of_card_two hK ht
  have hJu : J ≠ Finset.univ := by
    intro hJ
    have htriv : ∀ g : adjointGroup .D4 K, eta K g = 1 := by
      intro g
      refine Subtype.ext (LinearEquiv.ext fun w => ?_)
      have h1 := eq_of_isChevType_univ hK isSimpleRep_natRep (hJ ▸ ht') g w
      simpa [natRep_apply] using h1
    have hx : xC .D4 K (0 : Fin 4) (1 : Kˣ) = 1 := (eta K).injective (by rw [htriv, map_one])
    exact xC_ne_one (τ := .D4) (0 : Fin 4) 1 hx
  by_cases hJe : ∃ e ∈ ({0, 1, 3} : Finset (Fin 4)), J = Finset.univ.erase e
  · obtain ⟨e, he, rfl⟩ := hJe
    exact ⟨y, e, he, ht'⟩
  · push Not at hJe
    exfalso
    have h9 := nine_le_finrank_range_of_not_natural (k := K) (V := Fin 4 ⊕ Fin 4 → K)
      isSimpleRep_natRep ht' hJu hJe 0
    have hle := Submodule.finrank_le (LinearMap.range
      ((natRep K) ((chevDatum .D4 K 2 hw).nW ((coxeterSystem .D4).wordProd (invWord 0))) - 1))
    rw [Module.finrank_fintype_fun_eq_card] at hle
    simp at hle
    omega

private theorem exists_iso_of_chevType_erase {W : Type*} [AddCommGroup W] [Module K W]
    {ρ : Representation K (adjointGroup .D4 K) W} (hρ : IsSimpleRep ρ) {y : W} {e : Fin 4}
    (ht : IsChevType .D4 K 2 hw ρ y (fun _ => 1) (Finset.univ.erase e))
    (y₀ : Fin 4 ⊕ Fin 4 → K) (σ : adjointGroup .D4 K ≃* adjointGroup .D4 K)
    (hσ : IsChevType .D4 K 2 hw ((natRep K).comp σ.toMonoidHom) y₀ (fun _ => 1)
      (Finset.univ.erase e)) :
    ∃ (β : W ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)), ∀ (g : adjointGroup .D4 K) (w : W),
      β (ρ g w) = (eta K (σ g) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (β w) := by
  obtain ⟨β, hβ⟩ := iso_of_isChevType (p := 2) hρ
    (isSimpleRep_comp isSimpleRep_natRep σ) ht hσ
  exact ⟨β, fun g w => by rw [hβ g w]; rfl⟩

private theorem exists_iso_of_chevType_erase2 {W : Type*} [AddCommGroup W] [Module K W]
    {ρ : Representation K (adjointGroup .D4 K) W} (hρ : IsSimpleRep ρ) {y : W} {e : Fin 4}
    (ht : IsChevType .D4 K 2 hw ρ y (fun _ => 1) (Finset.univ.erase e))
    (y₀ : Fin 4 ⊕ Fin 4 → K)
    (hσ : IsChevType .D4 K 2 hw
      (((natRep K).comp (triality K).toMonoidHom).comp (triality K).toMonoidHom) y₀
      (fun _ => 1) (Finset.univ.erase e)) :
    ∃ (β : W ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)), ∀ (g : adjointGroup .D4 K) (w : W),
      β (ρ g w) = (eta K ((triality K).trans (triality K) g) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (β w) := by
  obtain ⟨β, hβ⟩ := iso_of_isChevType (p := 2) hρ
    (isSimpleRep_comp (isSimpleRep_comp isSimpleRep_natRep (triality K)) (triality K)) ht hσ
  exact ⟨β, fun g w => by rw [hβ g w]; rfl⟩

theorem exists_iso_natRep (hK : Nat.card K = 2) {W : Type*} [AddCommGroup W] [Module K W]
    {ρ : Representation K (adjointGroup .D4 K) W} (hρ : IsSimpleRep ρ) {y : W} {e : Fin 4}
    (he : e ∈ ({0, 1, 3} : Finset (Fin 4)))
    (ht : IsChevType .D4 K 2 hw ρ y (fun _ => 1) (Finset.univ.erase e)) :
    ∃ (σ : adjointGroup .D4 K ≃* adjointGroup .D4 K) (β : W ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)),
      ∀ (g : adjointGroup .D4 K) (w : W),
        β (ρ g w) = (eta K (σ g) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (β w) := by
  obtain ⟨y₀, e₀, he₀, ht₀⟩ := exists_isChevType_natRep (hw := hw) hK
  rcases perm_cover e e₀ he he₀ with h0 | h1 | h2
  · subst e₀
    exact ⟨MulEquiv.refl _, exists_iso_of_chevType_erase hρ ht y₀ (MulEquiv.refl _)
      (by simpa using ht₀)⟩
  · have h1' := isChevType_comp_triality_erase (a := (e₀ : Fin Tag.D4.rank))
      (b := (e : Fin Tag.D4.rank)) ht₀ h1
    exact ⟨triality K, exists_iso_of_chevType_erase hρ ht y₀ (triality K) h1'⟩
  · have h1' := isChevType_comp_triality_erase (a := (e₀ : Fin Tag.D4.rank))
      (b := (TwistTag.D4.perm.symm e₀ : Fin Tag.D4.rank)) ht₀ rfl
    have h2' := isChevType_comp_triality_erase
      (a := (TwistTag.D4.perm.symm e₀ : Fin Tag.D4.rank)) (b := (e : Fin Tag.D4.rank)) h1' h2
    exact ⟨(triality K).trans (triality K), exists_iso_of_chevType_erase2 hρ ht y₀ h2'⟩

end D4

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

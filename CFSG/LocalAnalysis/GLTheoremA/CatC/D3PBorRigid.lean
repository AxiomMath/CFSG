module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PBorSign

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three

variable {K : Type} [Field K] [Finite K]



section Rigid

open scoped Pointwise

theorem map_conj_subgroupOf (S : Subgroup (ModGL Tag.D4 K)) {g : ↥(adjointGroup Tag.D4 K)}
    (hg : (g : ModGL Tag.D4 K) ∈ Subgroup.normalizer (S : Set (ModGL Tag.D4 K))) :
    (S.subgroupOf (adjointGroup Tag.D4 K)).map (MulAut.conj g).toMonoidHom =
      S.subgroupOf (adjointGroup Tag.D4 K) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ S.subgroupOf (adjointGroup Tag.D4 K) := hx
    rw [Subgroup.mem_subgroupOf] at hx'
    show (MulAut.conj g) x ∈ S.subgroupOf (adjointGroup Tag.D4 K)
    rw [Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.1 hg (x : ModGL Tag.D4 K)).1 hx'
    simpa [MulAut.conj_apply] using this
  · intro hy
    have hy' : y ∈ S.subgroupOf (adjointGroup Tag.D4 K) := hy
    rw [Subgroup.mem_subgroupOf] at hy'
    refine ⟨(MulAut.conj g)⁻¹ y, ?_, by simp [MulAut.conj_apply, MulAut.conj_inv_apply, mul_assoc]⟩
    show (MulAut.conj g)⁻¹ y ∈ S.subgroupOf (adjointGroup Tag.D4 K)
    rw [Subgroup.mem_subgroupOf]
    have h := (Subgroup.mem_normalizer_iff.1 hg
      ((g : ModGL Tag.D4 K)⁻¹ * (y : ModGL Tag.D4 K) * (g : ModGL Tag.D4 K))).2 (by
        have e : (g : ModGL Tag.D4 K) * ((g : ModGL Tag.D4 K)⁻¹ * (y : ModGL Tag.D4 K) *
            (g : ModGL Tag.D4 K)) * (g : ModGL Tag.D4 K)⁻¹ = (y : ModGL Tag.D4 K) := by simp [mul_assoc]
        rw [e]; exact hy')
    simpa [MulAut.conj_inv_apply] using h

open scoped Classical in
theorem eq_one_of_scalars_one [CharP K 3] (t : MulAut ↥(adjointGroup Tag.D4 K)) (ht2 : t * t = 1)
    (hUt : (unitU K).map t.toMonoidHom = unitU K) (la : LayerAct Tag.D4 t (1 : K ≃+* K))
    (hr : ∀ k δ, la.r k δ = δ) (hf : ∀ k δ, la.f k δ = 1) : t = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  have hop := exceptional_ordinary_Sylow_opposition Tag.D4 K 3 w₀ hw₀
  obtain ⟨c, β, hβU, hβV, htc⟩ := hop.2.2.2.2.2 t
  have hβU' : (unitU K).map β.toMonoidHom = unitU K := hβU
  have hceq : MulAut.conj c = t * β⁻¹ := by rw [htc]; group
  have hcU : (unitU K).map (MulAut.conj c).toMonoidHom = unitU K := by
    rw [hceq, map_toMonoidHom_mul_mulAut, map_inv_toMonoidHom_of_map_eq hβU', hUt]
  have hcB : (c : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K := mem_borelGroup_of_stable c hcU
  have hst := triangular_borel_structure.{0, 0} Tag.D4 K
  have hcB' : (c : ModGL Tag.D4 K) ∈
      (SetLike.coe (posUnipotent Tag.D4 K) * SetLike.coe (torusGroup Tag.D4 K) :
        Set (ModGL Tag.D4 K)) := by
    rw [← hst.2.2.2.2.2.1]; exact hcB
  obtain ⟨u₀, hu₀, h₀, hh₀, hc'⟩ := hcB'
  have hu₀C : u₀ ∈ adjointGroup Tag.D4 K := posUnipotent_le_adjointGroup hu₀
  have hh₀C : h₀ ∈ adjointGroup Tag.D4 K := by
    have : h₀ = u₀⁻¹ * (c : ModGL Tag.D4 K) := by rw [← hc']; group
    rw [this]
    exact mul_mem (inv_mem hu₀C) c.2
  set U₀ : ↥(adjointGroup Tag.D4 K) := ⟨u₀, hu₀C⟩ with hU₀
  set H₀ : ↥(adjointGroup Tag.D4 K) := ⟨h₀, hh₀C⟩ with hH₀
  have hcUH : c = U₀ * H₀ := Subtype.ext hc'.symm
  have hh₀N : (H₀ : ModGL Tag.D4 K) ∈
      Subgroup.normalizer (posUnipotent Tag.D4 K : Set (ModGL Tag.D4 K)) := hst.2.2.1 hh₀
  have hh₀N' : (H₀ : ModGL Tag.D4 K) ∈
      Subgroup.normalizer (negUnipotent Tag.D4 K : Set (ModGL Tag.D4 K)) :=
    torusGroup_le_normalizer_negUnipotent hh₀
  set β' : MulAut ↥(adjointGroup Tag.D4 K) := MulAut.conj H₀ * β with hβ'
  have hβ'U : (unitU K).map β'.toMonoidHom = unitU K := by
    rw [hβ', map_toMonoidHom_mul_mulAut, hβU']
    exact map_conj_subgroupOf (posUnipotent Tag.D4 K) hh₀N
  have hβ'V : ((negUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K)).map β'.toMonoidHom =
      (negUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K) := by
    rw [hβ', map_toMonoidHom_mul_mulAut, hβV]
    exact map_conj_subgroupOf (negUnipotent Tag.D4 K) hh₀N'
  have hA' : β' ∈ unipotentPairAut Tag.D4 K := ⟨hβ'U, hβ'V⟩
  have htβ : t = MulAut.conj U₀ * β' := by
    rw [hβ', ← mul_assoc, ← map_mul, ← hcUH]; exact htc
  obtain ⟨π, hπ⟩ := exists_perm_map_simple hA'
  have hadj : ∀ (i : D4Idx) (c' : K), adjX Tag.D4 K i c' = rootElt (rA i) c' := fun i c' =>
    Subtype.ext (pinnedX_single Tag.D4 K i c').symm
  have hxN : ∀ (i : D4Idx) (c' : K), adjX Tag.D4 K i c' ∈ unitN Tag.D4 K 0 := fun i c' => by
    rw [hadj]; exact rootElt_rA_mem i c'
  have hδ : ∀ j : D4Idx, IsRoot Tag.D4 (rA j) ∧ height (rA j) = ((0 + 1 : ℕ) : ℤ) := fun j =>
    ⟨rA_isRoot j, by rw [height_rA]; rfl⟩
  let δ : D4Idx → UnitRoots Tag.D4 0 := fun j => ⟨rA j, hδ j⟩
  have hδinj : ∀ a b : D4Idx, δ a = δ b ↔ a = b := fun a b =>
    ⟨fun h => (rA_inj _ _).1 (congrArg Subtype.val h), fun h => by rw [h]⟩
  have hex : ∀ (i : D4Idx) (c' : K), ∃ e : K,
      ((β' (adjX Tag.D4 K i c') : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        xUnit Tag.D4 K (π i) e := by
    intro i c'
    have h1 : adjX Tag.D4 K i c' ∈ simplePosSubgroup Tag.D4 K i := ⟨c', rfl⟩
    have h2 := Subgroup.mem_map_of_mem β'.toMonoidHom h1
    rw [(hπ i).1] at h2
    exact h2
  choose e he using hex
  have hβx : ∀ i c', β' (adjX Tag.D4 K i c') = rootElt (rA (π i)) (e i c') := fun i c' =>
    Subtype.ext ((he i c').trans (pinnedX_single Tag.D4 K (π i) (e i c')).symm)
  have hcoord : ∀ (i : D4Idx) (c' : K) (j : D4Idx),
      (if π i = j then e i c' else 0) = (if i = j then c' else 0) := by
    intro i c' j
    have h1 := layerAct_coord_triv la hr 0 (δ j) (adjX Tag.D4 K i c') (hxN i c')
    rw [hf, one_mul] at h1
    have htx : ((t (adjX Tag.D4 K i c') : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        u₀ * ((rootElt (rA (π i)) (e i c') : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) * u₀⁻¹ := by
      rw [htβ, MulAut.mul_apply, MulAut.conj_apply, hβx]
      rfl
    have hmem : ((rootElt (rA (π i)) (e i c') : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈
        heightSeries Tag.D4 K (height (δ j).1) := by
      have := (mem_unitN (τ := Tag.D4)).1 (rootElt_rA_mem (K := K) (π i) (e i c'))
      rw [show height (δ j).1 = ((0 + 1 : ℕ) : ℤ) from (hδ j).2]
      exact this
    rw [htx, rootCoord_conj (UnitRoots.pos Tag.D4 (δ j)) hu₀ hmem] at h1
    have h2 := rootCoord_rootElt (K := K) (δ j) (δ (π i)) (e i c')
    have h3 := rootCoord_rootElt (K := K) (δ j) (δ i) c'
    have h4 : ((adjX Tag.D4 K i c' : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        ((rootElt (δ i).1 c' : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) := by
      rw [hadj]
    rw [h4] at h1
    change rootCoord (UnitRoots.pos Tag.D4 (δ j))
      ((rootElt (δ (π i)).1 (e i c') : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) = _ at h1
    rw [h2, h3] at h1
    simpa only [hδinj] using h1
  have hπ1 : ∀ i, π i = i := by
    intro i
    by_contra hne
    have h := hcoord i 1 i
    rw [if_neg hne, if_pos rfl] at h
    exact zero_ne_one h
  have he1 : ∀ i c', e i c' = c' := by
    intro i c'
    have h := hcoord i c' i
    rw [hπ1 i, if_pos rfl, if_pos rfl] at h
    exact h
  have key : ∀ i c', β' (adjX Tag.D4 K i c') = adjX Tag.D4 K i c' := by
    intro i c'
    have h := hβx i c'
    rw [hπ1 i, he1 i c', ← hadj] at h
    exact h
  have hε : ∀ i, (simplePosSubgroup Tag.D4 K i).map β'.toMonoidHom =
        simplePosSubgroup Tag.D4 K ((d4Rho ^ 0) i) ∧
      (simpleNegSubgroup Tag.D4 K i).map β'.toMonoidHom =
        simpleNegSubgroup Tag.D4 K ((d4Rho ^ 0) i) := by
    intro i
    have h := hπ i
    rw [hπ1 i] at h
    simpa using h
  obtain ⟨a, σ', hβ'eq⟩ := exists_normalAut_mul_graph (K := K) (β := β') (ε := 0) hε
  have hxa : ∀ (i : D4Idx) (c' : K), (a i : K) * σ' c' = c' := by
    intro i c'
    have h1 := key i c'
    rw [hβ'eq, normalGraph_apply_adjX] at h1
    have h2 : (d4Rho ^ 0) i = i := by simp
    rw [h2] at h1
    exact adjX_injective (τ := Tag.D4) (K := K) i h1
  have ha1 : ∀ i : D4Idx, (a i : K) = 1 := fun i => by
    have := hxa i 1
    rwa [map_one, mul_one] at this
  have hσ1 : ∀ c' : K, σ' c' = c' := fun c' => by
    have := hxa 0 c'
    rwa [ha1, one_mul] at this
  have hyfix : ∀ (i : D4Idx) (c' : K), β' (adjY Tag.D4 K i c') = adjY Tag.D4 K i c' := by
    intro i c'
    rw [hβ'eq, MulAut.mul_apply, d4Graph_adjY, exactNormalAut_adjY]
    have h2 : (d4Rho ^ 0) i = i := by simp
    rw [h2]
    change adjY Tag.D4 K i ((((a i)⁻¹ : Kˣ) : K) * σ' c') = adjY Tag.D4 K i c'
    rw [hσ1, Units.val_inv_eq_inv_val, ha1 i, inv_one, one_mul]
  have hβ'one : β' = 1 := mulAut_eq_one_of_fix key hyfix
  have ht_eq : t = MulAut.conj U₀ := by rw [htβ, hβ'one, mul_one]
  obtain ⟨P₀, hP₀⟩ := hop.1
  have hp : IsPGroup 3 ((posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K)) := by
    rw [← hP₀]; exact P₀.isPGroup'
  have hU₀mem : U₀ ∈ (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K) :=
    Subgroup.mem_subgroupOf.2 hu₀
  obtain ⟨k, hk⟩ := hp ⟨U₀, hU₀mem⟩
  have hk' : U₀ ^ 3 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have ht3 : t ^ 3 ^ k = 1 := by rw [ht_eq, ← map_pow, hk', map_one]
  have hord : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht2)
  have hord2 : orderOf t ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one ht3
  have h1 : orderOf t = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right _ (by norm_num)) hord hord2
  exact orderOf_eq_one_iff.1 h1

end Rigid

end CFSG.LocalAnalysis.GLTheoremA

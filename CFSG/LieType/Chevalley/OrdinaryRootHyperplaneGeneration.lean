module

public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section General

variable {G : Type*} [Group G]

theorem le_iSup_hyper_of_coprime {p : ℕ} [Fact p.Prime] {A H C : Subgroup G}
    [Finite A] [Finite H] [IsElementaryAbelian p A] [Nontrivial A]
    (hp : ¬ p ∣ Nat.card H) (hAH : A ≤ Subgroup.normalizer (H : Set G)) (hHC : H ≤ C) :
    H ≤ ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : B.relIndex A = p),
      C ⊓ Subgroup.centralizer (B : Set G) := by
  let : MulDistribMulAction A H := MulDistribMulAction.compHom H (Subgroup.inclusion hAH)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := A) (H := H) hp
  have hle : (⨆ (B : Subgroup A) (_ : B.index = p), CFSG.fixedPointSubgroup B H) ≤
      (⨆ (B : Subgroup G) (_ : B ≤ A) (_ : B.relIndex A = p),
        C ⊓ Subgroup.centralizer (B : Set G)).comap H.subtype := by
    refine iSup₂_le fun B hB => fun x hx => ?_
    have hBA : B.map A.subtype ≤ A := Subgroup.map_subtype_le B
    have hBi : (B.map A.subtype).relIndex A = p := by
      have h := Subgroup.relIndex_map_map_of_injective B ⊤ A.subtype_injective
      rw [Subgroup.relIndex_top_right, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
      rw [h, hB]
    refine Subgroup.mem_iSup_of_mem (B.map A.subtype) (Subgroup.mem_iSup_of_mem hBA
      (Subgroup.mem_iSup_of_mem hBi (Subgroup.mem_inf.2 ⟨hHC x.2, ?_⟩)))
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hc : (b : G) * x * (b : G)⁻¹ = x := congrArg Subtype.val (hx ⟨b, hb⟩)
    calc (A.subtype b : G) * x = (b : G) * x * (b : G)⁻¹ * b := by
          rw [inv_mul_cancel_right]; rfl
      _ = x * A.subtype b := by rw [hc]; rfl
  intro h hh
  have hmem : (⟨h, hh⟩ : H) ∈
      ⨆ (B : Subgroup A) (_ : B.index = p), CFSG.fixedPointSubgroup B H := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle hmem

theorem le_iSup_hyper_of_map_conj {p : ℕ} {C A : Subgroup G} {x : G} (hx : x ∈ C)
    (h : C ≤ ⨆ (B : Subgroup G) (_ : B ≤ A.map (MulAut.conj x).toMonoidHom)
      (_ : B.relIndex (A.map (MulAut.conj x).toMonoidHom) = p),
        C ⊓ Subgroup.centralizer (B : Set G)) :
    C ≤ ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : B.relIndex A = p),
      C ⊓ Subgroup.centralizer (B : Set G) := by
  set f : G →* G := (MulAut.conj x⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj x⁻¹).injective
  have hAA : (A.map (MulAut.conj x).toMonoidHom).map f = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext y
    simp only [f, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  have hle : (⨆ (B : Subgroup G) (_ : B ≤ A.map (MulAut.conj x).toMonoidHom)
      (_ : B.relIndex (A.map (MulAut.conj x).toMonoidHom) = p),
        C ⊓ Subgroup.centralizer (B : Set G)) ≤
      (⨆ (B : Subgroup G) (_ : B ≤ A) (_ : B.relIndex A = p),
        C ⊓ Subgroup.centralizer (B : Set G)).comap f := by
    refine iSup₂_le fun B hB => iSup_le fun hBi => fun y hy => ?_
    obtain ⟨hyC, hyc⟩ := Subgroup.mem_inf.1 hy
    have hB₀ : B.map f ≤ A := hAA ▸ Subgroup.map_mono hB
    have hB₀i : (B.map f).relIndex A = p := by
      rw [← hAA, Subgroup.relIndex_map_map_of_injective _ _ hf, hBi]
    rw [Subgroup.mem_comap]
    refine Subgroup.mem_iSup_of_mem (B.map f) (Subgroup.mem_iSup_of_mem hB₀
      (Subgroup.mem_iSup_of_mem hB₀i (Subgroup.mem_inf.2 ⟨?_, ?_⟩)))
    · change x⁻¹ * y * x⁻¹⁻¹ ∈ C
      exact mul_mem (mul_mem (inv_mem hx) hyC) (by rw [inv_inv]; exact hx)
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have hby := Subgroup.mem_centralizer_iff.1 hyc b hb
      change x⁻¹ * b * x⁻¹⁻¹ * (x⁻¹ * y * x⁻¹⁻¹) = x⁻¹ * y * x⁻¹⁻¹ * (x⁻¹ * b * x⁻¹⁻¹)
      simp only [inv_inv]
      calc x⁻¹ * b * x * (x⁻¹ * y * x) = x⁻¹ * (b * y) * x := by group
        _ = x⁻¹ * (y * b) * x := by rw [hby]
        _ = x⁻¹ * y * x * (x⁻¹ * b * x) := by group
  intro c hc
  have hmem := hle (h (mul_mem (mul_mem hx hc) (inv_mem hx)))
  rw [Subgroup.mem_comap] at hmem
  have e : f (x * c * x⁻¹) = c := by
    change x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c
    group
  rwa [e] at hmem

end General

section Ordinary

variable {τ : Tag} {k : Type} [Field k]

theorem exists_radicals_of_parabolicLevi
    [Finite k] {r : ℕ} [Fact r.Prime] [CharP k r] [IsSimpleGroup (adjointGroup τ k)]
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) :
    ∃ Q Q' : Subgroup (ModGL τ k), IsPGroup r Q ∧ IsPGroup r Q' ∧ Q ≤ adjointGroup τ k ∧
      Q' ≤ adjointGroup τ k ∧ parabolicLevi τ k J ≤ Subgroup.normalizer (Q : Set (ModGL τ k)) ∧
      parabolicLevi τ k J ≤ Subgroup.normalizer (Q' : Set (ModGL τ k)) ∧
      adjointGroup τ k ≤ Q ⊔ Q' := by
  have := finite_modGL (τ := τ) (K := k)
  obtain ⟨w₀, δ, hδinj, hδ⟩ := exists_longest_simple_perm τ
  obtain ⟨-, hR, -⟩ := canonical_weyl_root_transport τ k
  have hnC : canonicalRep (coxeterSystem τ) k w₀ ∈ adjointGroup τ k :=
    canonicalRep_mem_adjointGroup _ k w₀
  set n := canonicalRep (coxeterSystem τ) k w₀
  set Q := parabolicRadical τ k J
  set Q' := (parabolicRadical τ k (δ '' J)).map (MulAut.conj n⁻¹).toMonoidHom
  set C := adjointGroup τ k
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := parabolic_root_radical_Levi_factors τ k J
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin'⟩ :=
    parabolic_root_radical_Levi_factors τ k (δ '' J)
  have hQp : IsPGroup r Q := (hfin r).2.1
  have hQ'p : IsPGroup r Q' := (hfin' r).2.1.map _
  have hQ1 : Q ≠ ⊥ := (hfin r).2.2 hJ
  have hQC : Q ≤ C := rootSpan_le_adjointGroup k _
  have hQ'C : Q' ≤ C := by
    rintro _ ⟨q, hq, rfl⟩
    exact mul_mem (mul_mem (inv_mem hnC) (rootSpan_le_adjointGroup k _ hq)) (inv_inv n ▸ hnC)
  have hMQ : parabolicLevi τ k J ≤ Subgroup.normalizer (Q : Set (ModGL τ k)) :=
    (parabolicLevi_le_parabolicSubgroup J).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical J)
  have hMQ' : parabolicLevi τ k J ≤ Subgroup.normalizer (Q' : Set (ModGL τ k)) := fun m hm =>
    mem_normalizer_map_conj_inv (((parabolicLevi_le_parabolicSubgroup (δ '' J)).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical (δ '' J)))
      (map_conj_parabolicLevi_le hδ J (Subgroup.mem_map_of_mem _ hm)))
  have hgen : C ≤ Q ⊔ Q' ⊔ parabolicLevi τ k J := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, hg | hg⟩
    · have hg' : g = xUnit τ k i c := Units.ext (hg.trans (coe_xUnit i c).symm)
      rw [hg']
      by_cases hi : i ∈ J
      · exact Subgroup.mem_sup_right (xUnit_mem_parabolicLevi hi c)
      · refine Subgroup.mem_sup_left (Subgroup.mem_sup_left ?_)
        rw [← pinnedX_single]
        exact pinnedX_mem_rootSpan (mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ i,
          by rw [height_single]; exact one_pos, i, hi, by simp⟩) c
    · have hg' : g = yUnit τ k i c := Units.ext (hg.trans (coe_yUnit i c).symm)
      rw [hg']
      by_cases hi : i ∈ J
      · exact Subgroup.mem_sup_right (yUnit_mem_parabolicLevi hi c)
      · refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)
        have hmem : (MulAut.conj n).toMonoidHom (yUnit τ k i c) ∈
            (rootSubgroup τ k (-Pi.single i 1)).map (MulAut.conj n).toMonoidHom :=
          Subgroup.mem_map_of_mem _
            (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨c, pinnedX_neg_single τ k i c⟩)
        rw [hR w₀ _ (isRoot_neg_single τ i), smul_neg, hδ, neg_neg] at hmem
        have hδi : Pi.single (δ i) 1 ∈ parabolicRadicalRoots τ (δ '' J) :=
          mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ (δ i),
            by rw [height_single]; exact one_pos, δ i,
            fun ⟨j, hj, hji⟩ => hi (hδinj hji ▸ hj), by simp⟩
        have hmem' : (MulAut.conj n).toMonoidHom (yUnit τ k i c) ∈
            parabolicRadical τ k (δ '' J) :=
          (le_biSup (rootSubgroup τ k) hδi) hmem
        refine Subgroup.mem_map.2 ⟨_, hmem', ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MulAut.conj_apply]
        group
  have hXC : Q ⊔ Q' ≤ C := sup_le hQC hQ'C
  have hCX : C ≤ Q ⊔ Q' := by
    have hN : C ≤ Subgroup.normalizer ((Q ⊔ Q' : Subgroup (ModGL τ k)) : Set (ModGL τ k)) :=
      hgen.trans (sup_le Subgroup.le_normalizer fun m hm =>
        mem_normalizer_sup_of_mem (hMQ hm) (hMQ' hm))
    have : ((Q ⊔ Q').subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).2 hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q ⊔ Q').subgroupOf C) with h | h
    · exfalso
      apply hQ1
      have hdis := Subgroup.subgroupOf_eq_bot.1 h
      exact eq_bot_iff.2 fun q hq => (Subgroup.disjoint_def.1 hdis)
        (Subgroup.mem_sup_left hq) (hQC hq) ▸ Subgroup.mem_bot.2 rfl
    · exact Subgroup.subgroupOf_eq_top.1 h
  exact ⟨Q, Q', hQp, hQ'p, hQC, hQ'C, hMQ, hMQ', hCX⟩

end Ordinary

theorem ordinary_root_invariant_prime_subgroup_hyperplane_generation
    (τ : Tag) (k : Type)
    [Field k] [Finite k] (r p : ℕ) [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    [IsSimpleGroup (adjointGroup τ k)] (A : Subgroup (ModGL τ k)) (hAC : A ≤ adjointGroup τ k)
    [IsElementaryAbelian p A] (hA1 : A ≠ ⊥) (R : Subgroup (ModGL τ k))
    (hRC : R ≤ adjointGroup τ k) (hRr : IsPGroup r R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL τ k))) :
    (⨆ (B : Subgroup (ModGL τ k)) (_ : B ≤ A) (_ : B.relIndex A = p),
      adjointGroup τ k ⊓ Subgroup.centralizer (B : Set (ModGL τ k))) = adjointGroup τ k := by
  have := finite_modGL (τ := τ) (K := k)
  refine le_antisymm (iSup₂_le fun B _ => iSup_le fun _ => inf_le_left) ?_
  obtain ⟨M, -, -, -, F, -, -, ⟨g, hg, l, hl, hl1, hgl⟩, hdom, -⟩ :=
    (RootWeightDatum.ordinary τ : RootWeightDatum k).root_p_subgroup_optimal_parabolic_containment
      r R hRC hRr hR
  obtain ⟨hJ, -, hN, hset, -⟩ := hdom g hg l hl hl1 hgl
  obtain ⟨g', rfl⟩ : ∃ g' : ModGL τ k, g' = g := ⟨g, rfl⟩
  have hgC : g' ∈ adjointGroup τ k := hg
  have hJ' : ((RootWeightDatum.ordinary τ : RootWeightDatum k).face l : Set (Fin τ.rank)) ≠
      Set.univ := hJ
  set J : Set (Fin τ.rank) := (RootWeightDatum.ordinary τ : RootWeightDatum k).face l
  change {x : ModGL τ k | x ∈ adjointGroup τ k ∧
      ∀ c : ℝ, (F c).map (x : Module.End k (RootModule τ k)) = F c} =
    ((parabolicSubgroup τ k J).map (MulAut.conj g').toMonoidHom : Set (ModGL τ k)) at hset
  have hA1' : A.map (MulAut.conj g'⁻¹).toMonoidHom ≤ parabolicSubgroup τ k J := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem := (Set.ext_iff.1 hset a).1
      (And.intro (hAC ha) (hN a (Subgroup.mem_inf.2 ⟨hAC ha, hAR ha⟩)))
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hmem
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hmem
  have hindex : ¬ p ∣ ((parabolicLevi τ k J).subgroupOf (parabolicSubgroup τ k J)).index := by
    rw [parabolicLevi_index_eq]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := parabolic_root_radical_Levi_factors τ k J
    exact not_dvd_card_of_isPGroup hrp (hfin r).2.1
  have hA1p : IsPGroup p (A.map (MulAut.conj g'⁻¹).toMonoidHom) :=
    (IsElementaryAbelian.isPGroup p A).map _
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_not_dvd_index hA1' hA1p hindex
  have hyC : y ∈ adjointGroup τ k := parabolicSubgroup_le_adjointGroup τ k J hy
  have hxC : y * g'⁻¹ ∈ adjointGroup τ k := mul_mem hyC (inv_mem hgC)
  have hmap : A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom =
      (A.map (MulAut.conj g'⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map, map_mul]
    rfl
  set A' := A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom
  have hAx : A' ≤ parabolicLevi τ k J := hmap ▸ hyA
  have : IsElementaryAbelian p A' := IsElementaryAbelian.map _
  have : Nontrivial A' := (Subgroup.nontrivial_iff_ne_bot A').2 fun h =>
    hA1 ((Subgroup.map_eq_bot_iff_of_injective A (MulAut.conj (y * g'⁻¹)).injective).1 h)
  obtain ⟨Q, Q', hQp, hQ'p, hQC, hQ'C, hMQ, hMQ', hCX⟩ :=
    exists_radicals_of_parabolicLevi (k := k) (r := r) hJ'
  refine le_iSup_hyper_of_map_conj hxC (hCX.trans (sup_le ?_ ?_))
  · exact le_iSup_hyper_of_coprime (not_dvd_card_of_isPGroup hrp hQp) (hAx.trans hMQ) hQC
  · exact le_iSup_hyper_of_coprime (not_dvd_card_of_isPGroup hrp hQ'p) (hAx.trans hMQ') hQ'C

end CFSG.LieType.Chevalley

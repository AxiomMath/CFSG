module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagAssembly

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWeight CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.CTP
open scoped Pointwise

section Generic

variable {G : Type*} [Group G]

theorem le_iSup_inf_centralizer_of_map_conj_normalizer {C A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (C : Set G))
    (h : C ≤ ⨆ b ∈ A.map (MulAut.conj x).toMonoidHom, ⨆ (_ : b ≠ 1),
      C ⊓ Subgroup.centralizer ({b} : Set G)) :
    C ≤ ⨆ a ∈ A, ⨆ (_ : a ≠ 1), C ⊓ Subgroup.centralizer ({a} : Set G) := by
  have hle : (⨆ b ∈ A.map (MulAut.conj x).toMonoidHom, ⨆ (_ : b ≠ 1),
      C ⊓ Subgroup.centralizer ({b} : Set G)) ≤
        (⨆ a ∈ A, ⨆ (_ : a ≠ 1), C ⊓ Subgroup.centralizer ({a} : Set G)).comap
          (MulAut.conj x⁻¹).toMonoidHom := by
    refine iSup₂_le fun b hb => iSup_le fun hb1 => fun y hy => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
    have ha1 : a ≠ 1 := fun h => hb1 (by rw [h, map_one])
    rw [Subgroup.mem_comap]
    refine Subgroup.mem_iSup_of_mem a (Subgroup.mem_iSup_of_mem ha
      (Subgroup.mem_iSup_of_mem ha1 ?_))
    obtain ⟨hyC, hyc⟩ := Subgroup.mem_inf.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] at hyc
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hxy : x⁻¹ * y * x ∈ C := by
      have h' := (Subgroup.mem_normalizer_iff.1 (inv_mem hx) y).1 hyC
      rwa [inv_inv] at h'
    refine Subgroup.mem_inf.2 ⟨hxy, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x⁻¹ * y * x * a = x⁻¹ * (y * (x * a * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * a * x⁻¹) * y) * x := by rw [hyc]
      _ = a * (x⁻¹ * y * x) := by group
  intro c hc
  have hmem := hle (h ((Subgroup.mem_normalizer_iff.1 hx c).1 hc))
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmem
  have e : x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c := by group
  rwa [e] at hmem

end Generic

section Radicals

variable {τ : Tag} {k : Type} [Field k]

theorem le_iSup_centralizer_of_normalizes_radicals
    [Finite k] {r p : ℕ} [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    [IsSimpleGroup (adjointGroup τ k)] {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ)
    {A : Subgroup (ModGL τ k)} [IsElementaryAbelian p A] (hcard : p ^ 2 ≤ Nat.card A)
    (w₀ : WeylGroup τ) {δ : Fin τ.rank → Fin τ.rank} (hδinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    (hAQ : A ≤ Subgroup.normalizer (parabolicRadical τ k J : Set (ModGL τ k)))
    (hAQ' : A ≤ Subgroup.normalizer
      (((parabolicRadical τ k (δ '' J)).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) k w₀)⁻¹).toMonoidHom :
          Subgroup (ModGL τ k)) : Set (ModGL τ k))) :
    adjointGroup τ k ≤
      ⨆ a ∈ A, ⨆ (_ : a ≠ 1), adjointGroup τ k ⊓ Subgroup.centralizer ({a} : Set (ModGL τ k)) := by
  have := finite_modGL (τ := τ) (K := k)
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
  have hpQ := not_dvd_card_of_isPGroup hrp hQp
  have hpQ' := not_dvd_card_of_isPGroup hrp hQ'p
  have h1 := le_iSup_inf_centralizer_of_coprime hcard hpQ hAQ hQC
  have h2 := le_iSup_inf_centralizer_of_coprime hcard hpQ' hAQ' hQ'C
  exact hCX.trans (sup_le h1 h2)

end Radicals

section Index

theorem index_subgroupOf_dvd_card_of_sup {G : Type*} [Group G] [Finite G] {P L Q : Subgroup G}
    (hQP : Q ≤ P) (hLP : L ≤ P) (hQn : P ≤ Subgroup.normalizer (Q : Set G))
    (hsup : L ⊔ Q = P) :
    (L.subgroupOf P).index ∣ Nat.card Q := by
  have hLn : L ≤ Subgroup.normalizer (Q : Set G) := hLP.trans hQn
  have hQn' : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).2 hQn
  have htop : L.subgroupOf P ⊔ Q.subgroupOf P = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hx⟩ := y
    have hx' : x ∈ (↑(L ⊔ Q) : Set G) := by rw [hsup]; exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L Q hLn] at hx'
    obtain ⟨l, hl, q, hq, rfl⟩ := Set.mem_mul.1 hx'
    haveI := hQn'
    rw [Subgroup.mem_sup_of_normal_right]
    exact ⟨⟨l, hLP hl⟩, Subgroup.mem_subgroupOf.2 hl, ⟨q, hQP hq⟩,
      Subgroup.mem_subgroupOf.2 hq, rfl⟩
  have hd : (Q.subgroupOf P).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (Q.subgroupOf P).relIndex (L.subgroupOf P ⊔ Q.subgroupOf P) =
      (Q.subgroupOf P).relIndex (L.subgroupOf P) :=
    Subgroup.relIndex_sup_right (L.subgroupOf P) (Q.subgroupOf P)
  rw [htop, Subgroup.relIndex_top_right] at h1
  have h2 : ((Q.subgroupOf P) ⊓ (L.subgroupOf P)).index =
      (Q.subgroupOf P).relIndex (L.subgroupOf P) * (L.subgroupOf P).index :=
    Subgroup.index_inf
  have h3 : ((Q.subgroupOf P) ⊓ (L.subgroupOf P)).relIndex (Q.subgroupOf P) *
      (Q.subgroupOf P).index = ((Q.subgroupOf P) ⊓ (L.subgroupOf P)).index :=
    Subgroup.relIndex_mul_index inf_le_left
  have h4 : ((Q.subgroupOf P) ⊓ (L.subgroupOf P)).relIndex (Q.subgroupOf P) =
      (L.subgroupOf P).relIndex (Q.subgroupOf P) :=
    Subgroup.inf_relIndex_left _ _
  rw [h4, h1, h2] at h3
  have h5 : (L.subgroupOf P).relIndex (Q.subgroupOf P) = (L.subgroupOf P).index := by
    have hpos : 0 < (Q.subgroupOf P).relIndex (L.subgroupOf P) :=
      Nat.pos_of_ne_zero (h1 ▸ hd)
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_comm ((Q.subgroupOf P).relIndex (L.subgroupOf P))
      ((L.subgroupOf P).relIndex (Q.subgroupOf P))]
    exact h3
  rw [← h5]
  have h6 := Subgroup.index_dvd_card ((L.subgroupOf P).subgroupOf (Q.subgroupOf P))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv] at h6

end Index

section Units

theorem submodule_map_units_mul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (X : Submodule K V) (a b : LinearMap.GeneralLinearGroup K V) :
    X.map ((a * b : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
      (X.map (b : Module.End K V)).map (a : Module.End K V) := by
  rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp]

end Units

abbrev E6Tag (K : Type) [Field K] : Tag :=
  (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).tag

@[expose] def e6DiagTorus (K : Type) [Field K] : Subgroup (ModGL (E6Tag K) K) :=
  (rootDiagUnitHom (τ := E6Tag K) (K := K)).range

theorem rootDiagUnitHom_eq (K : Type) [Field K] (b : Fin (E6Tag K).rank → Kˣ) :
    rootDiagUnitHom (τ := E6Tag K) (K := K) b = rootDiagUnit (E6Tag K) b :=
  rfl

section E6


theorem e6DiagTorus_le_normalizer (K : Type) [Field K] :
    e6DiagTorus K ≤ Subgroup.normalizer (adjointGroup (E6Tag K) K : Set (ModGL (E6Tag K) K)) := by
  intro t ht
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 ht
  rw [rootDiagUnitHom_eq] at hb
  subst hb
  exact (root_diagonal_conjugation (E6Tag K) K b).2.2

theorem e6DiagTorus_le_e6InndiagGL (K : Type) [Field K] : e6DiagTorus K ≤ e6InndiagGL K :=
  le_sup_right

theorem mem_e6InndiagGL_decomp (K : Type) [Field K] {x : ModGL (E6Tag K) K}
    (hx : x ∈ e6InndiagGL K) :
    ∃ c ∈ adjointGroup (E6Tag K) K, ∃ t ∈ e6DiagTorus K, x = c * t := by
  have key : ∀ y ∈ Subgroup.closure ((adjointGroup (E6Tag K) K : Set (ModGL (E6Tag K) K)) ∪
      (e6DiagTorus K : Set (ModGL (E6Tag K) K))),
      ∃ c ∈ adjointGroup (E6Tag K) K, ∃ t ∈ e6DiagTorus K, y = c * t := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with hz | hz
      · exact ⟨z, hz, 1, one_mem _, (mul_one z).symm⟩
      · exact ⟨1, one_mem _, z, hz, (one_mul z).symm⟩
    | one => exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, hc, t, ht, rfl⟩ := ha
      obtain ⟨c', hc', t', ht', rfl⟩ := hb
      refine ⟨c * (t * c' * t⁻¹), mul_mem hc ?_, t * t', mul_mem ht ht', ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (e6DiagTorus_le_normalizer K ht) c').1 hc'
      · group
    | inv a _ ha =>
      obtain ⟨c, hc, t, ht, rfl⟩ := ha
      refine ⟨t⁻¹ * c⁻¹ * t, ?_, t⁻¹, inv_mem ht, ?_⟩
      · have h' := (Subgroup.mem_normalizer_iff.1 (e6DiagTorus_le_normalizer K (inv_mem ht))
          c⁻¹).1 (inv_mem hc)
        rwa [inv_inv] at h'
      · group
  exact key x (mem_e6InndiagGL_iff.1 hx)

@[expose] def e6Chat (K : Type) [Field K] : Subgroup (ModGL (E6Tag K) K) := e6InndiagGL K

theorem map_weightSpace_le_of_mem_e6DiagTorus (K : Type) [Field K] {t : ModGL (E6Tag K) K}
    (ht : t ∈ e6DiagTorus K)
    (χ : (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).space) :
    ((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).weightSpace χ).map
      (t : Module.End K (RootModule (E6Tag K) K)) ≤
      (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).weightSpace χ := by
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 ht
  rw [rootDiagUnitHom_eq] at hb
  subst hb
  refine Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 fun v hv => ?_)
  rw [SetLike.mem_coe, Submodule.mem_comap]
  rcases hv with ⟨α, hα, hχ, rfl⟩ | ⟨hχ0, j, rfl⟩
  · change rootDiag b (rootVec (E6Tag K) K α) ∈ _
    rw [rootDiag_rootVec b hα]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨α, hα, hχ, rfl⟩))
  · change rootDiag b (hVec (E6Tag K) K j) ∈ _
    rw [rootDiag_hVec b j]
    exact Submodule.subset_span (Or.inr ⟨hχ0, j, rfl⟩)

theorem map_weightSpace_eq_of_mem_e6DiagTorus (K : Type) [Field K] {t : ModGL (E6Tag K) K}
    (ht : t ∈ e6DiagTorus K) (χ : (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).space) :
    ((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).weightSpace χ).map
      (t : Module.End K (RootModule (E6Tag K) K)) =
      (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).weightSpace χ := by
  refine le_antisymm (map_weightSpace_le_of_mem_e6DiagTorus K ht χ) ?_
  have h := map_weightSpace_le_of_mem_e6DiagTorus K (inv_mem ht) χ
  have e : (((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).weightSpace χ).map
      ((t⁻¹ : ModGL (E6Tag K) K) : Module.End K (RootModule (E6Tag K) K))).map
      (t : Module.End K (RootModule (E6Tag K) K)) =
      (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).weightSpace χ := by
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Module.End.one_eq_id, Submodule.map_id]
  exact (le_of_eq e.symm).trans (Submodule.map_mono h)

theorem filtration_map_le_of_mem_e6DiagTorus (K : Type) [Field K] {t : ModGL (E6Tag K) K}
    (ht : t ∈ e6DiagTorus K) (l : (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).space)
    (c : ℝ) :
    ((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l c).map
      (t : Module.End K (RootModule (E6Tag K) K)) ≤
      (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l c := by
  refine Submodule.map_le_iff_le_comap.2 (weightFiltration_le_iff.2 fun χ hχ hc => ?_)
  rw [← Submodule.map_le_iff_le_comap]
  exact (map_weightSpace_le_of_mem_e6DiagTorus K ht χ).trans (le_weightFiltration hχ hc)

theorem filtration_map_eq_of_mem_e6DiagTorus (K : Type) [Field K] {t : ModGL (E6Tag K) K}
    (ht : t ∈ e6DiagTorus K) (l : (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).space)
    (c : ℝ) :
    ((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l c).map
      (t : Module.End K (RootModule (E6Tag K) K)) =
      (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l c := by
  refine le_antisymm (filtration_map_le_of_mem_e6DiagTorus K ht l c) ?_
  have h := filtration_map_le_of_mem_e6DiagTorus K (inv_mem ht) l c
  have e : ((((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l c).map
      ((t⁻¹ : ModGL (E6Tag K) K) : Module.End K (RootModule (E6Tag K) K))).map
      (t : Module.End K (RootModule (E6Tag K) K))) =
      (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l c := by
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Module.End.one_eq_id, Submodule.map_id]
  exact (le_of_eq e.symm).trans (Submodule.map_mono h)

theorem mem_parabolic_sup_torus_of_stab (K : Type) [Field K] [Finite K]
    {l : (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).space}
    (hl : l ∈ (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).dominant)
    {y : ModGL (E6Tag K) K} (hy : y ∈ e6Chat K)
    (hstab : ∀ c : ℝ, ((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l c).map
      (y : Module.End K (RootModule (E6Tag K) K)) =
      (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l c) :
    y ∈ (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).parabolic
      ((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).face l) ⊔ e6DiagTorus K := by
  obtain ⟨c', hc', t', ht', rfl⟩ := mem_e6InndiagGL_decomp K hy
  have hc'stab : ∀ c : ℝ,
      ((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l c).map
        (c' : Module.End K (RootModule (E6Tag K) K)) =
      (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l c := by
    intro c
    have h1 := hstab c
    rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp,
      filtration_map_eq_of_mem_e6DiagTorus K ht' l c] at h1
    exact h1
  have hset :=
    (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).setOf_stab_eq_map_conj_parabolic
      hl (one_mem _)
    (F := (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l)
    (fun c => by rw [Units.val_one, Module.End.one_eq_id, Submodule.map_id])
  have hmem : c' ∈ ((((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).parabolic
      ((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).face l)).map
        (MulAut.conj (1 : ModGL (E6Tag K) K)).toMonoidHom : Subgroup (ModGL (E6Tag K) K)) :
        Set (ModGL (E6Tag K) K)) := by
    rw [← hset]
    exact ⟨hc', hc'stab⟩
  obtain ⟨p, hp, hpc⟩ := Subgroup.mem_map.1 hmem
  have hpc' : p = c' := by simpa [MulAut.conj_apply] using hpc
  exact mul_mem (Subgroup.mem_sup_left (hpc' ▸ hp)) (Subgroup.mem_sup_right ht')

theorem parabolic_sup_torus_eq (K : Type) [Field K] [Finite K] (J : Set (Fin (E6Tag K).rank)) :
    parabolicSubgroup (E6Tag K) K J ⊔ e6DiagTorus K =
      parabolicRadical (E6Tag K) K J ⊔ (parabolicLevi (E6Tag K) K J ⊔ e6DiagTorus K) := by
  obtain ⟨-, -, -, -, -, hsup, -⟩ := parabolic_root_radical_Levi_factors (E6Tag K) K J
  rw [← sup_assoc, hsup]

theorem map_parabolicRadical_conj_rootDiagUnit (K : Type) [Field K]
    (b : Fin (E6Tag K).rank → Kˣ) (J : Set (Fin (E6Tag K).rank)) :
    (parabolicRadical (E6Tag K) K J).map (MulAut.conj (rootDiagUnit (E6Tag K) b)).toMonoidHom =
      parabolicRadical (E6Tag K) K J := by
  unfold parabolicRadical
  exact map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup b hα.1.1

theorem e6DiagTorus_le_normalizer_parabolicRadical (K : Type) [Field K]
    (J : Set (Fin (E6Tag K).rank)) :
    e6DiagTorus K ≤
      Subgroup.normalizer (parabolicRadical (E6Tag K) K J : Set (ModGL (E6Tag K) K)) := by
  intro t ht
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 ht
  rw [rootDiagUnitHom_eq] at hb
  subst hb
  exact mem_normalizer_of_map_eq (map_parabolicRadical_conj_rootDiagUnit K b J)

theorem levi_sup_torus_le_normalizer_parabolicRadical (K : Type) [Field K]
    (J : Set (Fin (E6Tag K).rank)) :
    parabolicLevi (E6Tag K) K J ⊔ e6DiagTorus K ≤
      Subgroup.normalizer (parabolicRadical (E6Tag K) K J : Set (ModGL (E6Tag K) K)) :=
  sup_le ((parabolicLevi_le_parabolicSubgroup J).trans
    (parabolicSubgroup_le_normalizer_parabolicRadical J))
    (e6DiagTorus_le_normalizer_parabolicRadical K J)

theorem e6DiagTorus_le_normalizer_opposite (K : Type) [Field K] (w₀ : WeylGroup (E6Tag K))
    (J' : Set (Fin (E6Tag K).rank)) :
    e6DiagTorus K ≤ Subgroup.normalizer
      (((parabolicRadical (E6Tag K) K J').map
        (MulAut.conj (canonicalRep (coxeterSystem (E6Tag K)) K w₀)⁻¹).toMonoidHom :
          Subgroup (ModGL (E6Tag K) K)) : Set (ModGL (E6Tag K) K)) := by
  intro t ht
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 ht
  rw [rootDiagUnitHom_eq] at hb
  subst hb
  refine mem_normalizer_of_map_eq ?_
  have hs : canonicalRep (coxeterSystem (E6Tag K)) K w₀ * rootDiagUnit (E6Tag K) b *
      (canonicalRep (coxeterSystem (E6Tag K)) K w₀)⁻¹ =
      rootDiagUnit (E6Tag K) (weylTuple w₀ b) :=
    canonicalRep_conj_rootDiagUnit w₀ b
  have hcomp : (MulAut.conj (rootDiagUnit (E6Tag K) b)).toMonoidHom.comp
      (MulAut.conj (canonicalRep (coxeterSystem (E6Tag K)) K w₀)⁻¹).toMonoidHom =
      (MulAut.conj (canonicalRep (coxeterSystem (E6Tag K)) K w₀)⁻¹).toMonoidHom.comp
      (MulAut.conj (rootDiagUnit (E6Tag K) (weylTuple w₀ b))).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hs]
    group
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    map_parabolicRadical_conj_rootDiagUnit K _ J']

theorem levi_sup_torus_le_normalizer_opposite (K : Type) [Field K]
    (w₀ : WeylGroup (E6Tag K)) {δ : Fin (E6Tag K).rank → Fin (E6Tag K).rank}
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin (E6Tag K).rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin (E6Tag K).rank)) :
    parabolicLevi (E6Tag K) K J ⊔ e6DiagTorus K ≤ Subgroup.normalizer
      (((parabolicRadical (E6Tag K) K (δ '' J)).map
        (MulAut.conj (canonicalRep (coxeterSystem (E6Tag K)) K w₀)⁻¹).toMonoidHom :
          Subgroup (ModGL (E6Tag K) K)) : Set (ModGL (E6Tag K) K)) :=
  sup_le (fun m hm => mem_normalizer_map_conj_inv
      (((parabolicLevi_le_parabolicSubgroup (δ '' J)).trans
        (parabolicSubgroup_le_normalizer_parabolicRadical (δ '' J)))
        (map_conj_parabolicLevi_le hδ J (Subgroup.mem_map_of_mem _ hm))))
    (e6DiagTorus_le_normalizer_opposite K w₀ (δ '' J))

theorem not_three_dvd_index_levi_sup (K : Type) [Field K] [Finite K]
    [Fact (ringChar K).Prime] [CharP K (ringChar K)] (hK3 : ringChar K ≠ 3)
    (J : Set (Fin (E6Tag K).rank)) :
    ¬ 3 ∣ ((parabolicLevi (E6Tag K) K J ⊔ e6DiagTorus K).subgroupOf
      (parabolicSubgroup (E6Tag K) K J ⊔ e6DiagTorus K)).index := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hQP, -, -, hMP, -, hsup, -, -, -, -, -, -, hfin⟩ :=
    parabolic_root_radical_Levi_factors (E6Tag K) K J
  have hQp : IsPGroup (ringChar K) (parabolicRadical (E6Tag K) K J) := (hfin (ringChar K)).2.1
  have hQPP : parabolicRadical (E6Tag K) K J ≤ parabolicSubgroup (E6Tag K) K J ⊔ e6DiagTorus K :=
    hQP.trans le_sup_left
  have hLPP : parabolicLevi (E6Tag K) K J ⊔ e6DiagTorus K ≤
      parabolicSubgroup (E6Tag K) K J ⊔ e6DiagTorus K :=
    sup_le_sup_right hMP _
  have hQn : parabolicSubgroup (E6Tag K) K J ⊔ e6DiagTorus K ≤
      Subgroup.normalizer (parabolicRadical (E6Tag K) K J : Set (ModGL (E6Tag K) K)) :=
    sup_le (parabolicSubgroup_le_normalizer_parabolicRadical J)
      (e6DiagTorus_le_normalizer_parabolicRadical K J)
  have hsup' : (parabolicLevi (E6Tag K) K J ⊔ e6DiagTorus K) ⊔ parabolicRadical (E6Tag K) K J =
      parabolicSubgroup (E6Tag K) K J ⊔ e6DiagTorus K := by
    rw [sup_comm, parabolic_sup_torus_eq]
  have hdvd := index_subgroupOf_dvd_card_of_sup hQPP hLPP hQn hsup'
  have hQ3 : ¬ 3 ∣ Nat.card (parabolicRadical (E6Tag K) K J) :=
    not_dvd_card_of_isPGroup hK3 hQp
  exact fun h => hQ3 (h.trans hdvd)

theorem e6InndiagParabolic_holds : E6InndiagParabolic := by
  intro K _ _ hK3 E hE hEab hcard hnin hnorm
  have hrp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hrp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK4 : 4 ≤ Nat.card K := four_le_card_of_not_innerAut K hK3 E hE hnin
  have hinj : Function.Injective (e6InndiagConj K) := e6InndiagConj_injective K hK4
  haveI := finite_modGL (τ := E6Tag K) (K := K)
  haveI hSimple : IsSimpleGroup (adjointGroup (E6Tag K) K) :=
    CFSG.LieType.SeitzGeneration.isSimpleGroup_adjointGroup_of_isQuasisimple
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K)
  have hEle : E ≤ (e6InndiagConj K).range := by rw [range_e6InndiagConj]; exact hE
  have hmap : (E.comap (e6InndiagConj K)).map (e6InndiagConj K) = E := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hEle]
  haveI hEcomap : IsElementaryAbelian 3 (E.comap (e6InndiagConj K)) :=
    IsElementaryAbelian.of_mulEquiv (((Subgroup.equivMapOfInjective _ _ hinj).trans
      (MulEquiv.subgroupCongr hmap)).symm) hEab
  set A : Subgroup (ModGL (E6Tag K) K) := e6PlanePre K E with hAdef
  haveI hA3 : IsElementaryAbelian 3 A := by
    rw [hAdef]
    exact @IsElementaryAbelian.map_subtype 3 _ _ _ _ _ hEcomap
  have hAcard : Nat.card A = 3 ^ 2 := (card_e6PlanePre K hK4 E hE).trans hcard
  have hA_mem : ∀ x ∈ A, ∃ g : ↥(e6Chat K), (g.1 : ModGL (E6Tag K) K) = x ∧
      e6InndiagConj K g ∈ E := fun x hx => (mem_e6PlanePre_iff K E x).1 hx
  have hA_inC : ∀ x ∈ A, x ∈ e6Chat K := by
    intro x hx
    obtain ⟨g, rfl, -⟩ := hA_mem x hx
    exact g.2
  have hnorm' : ∃ R : Subgroup (adjointGroup (E6Tag K) K), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
      ∀ ε ∈ E, R.map ε.toMonoidHom = R := hnorm
  obtain ⟨R, hR1, hRp, hRn⟩ := hnorm'
  set Q : Subgroup (ModGL (E6Tag K) K) := R.map (adjointGroup (E6Tag K) K).subtype with hQ
  have hQ1 : Q ≠ ⊥ := fun h => hR1
    ((Subgroup.map_eq_bot_iff_of_injective R (Subgroup.subtype_injective _)).1 h)
  have hQp : IsPGroup (ringChar K) Q := hRp.map _
  have hQC : Q ≤ adjointGroup (E6Tag K) K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hA_norm : ∀ x ∈ A, x ∈ Subgroup.normalizer (Q : Set (ModGL (E6Tag K) K)) := by
    intro x hx
    obtain ⟨g, rfl, hgE⟩ := hA_mem x hx
    have fwd : ∀ k : ↥(e6Chat K), e6InndiagConj K k ∈ E → ∀ r ∈ R,
        (k.1 : ModGL (E6Tag K) K) * (r : ModGL (E6Tag K) K) * (k.1 : ModGL (E6Tag K) K)⁻¹ ∈ Q := by
      intro k hkE r hr
      have hεr : e6InndiagConj K k r ∈ R := by
        rw [← hRn _ hkE]
        exact Subgroup.mem_map_of_mem _ hr
      have e : ((e6InndiagConj K k r).1 : ModGL (E6Tag K) K) =
          (k.1 : ModGL (E6Tag K) K) * (r : ModGL (E6Tag K) K) * (k.1 : ModGL (E6Tag K) K)⁻¹ :=
        e6InndiagConj_apply k r
      rw [← e]
      exact Subgroup.mem_map_of_mem _ hεr
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hh
      exact fwd g hgE r hr
    · intro hh
      obtain ⟨r, hr, hr'⟩ := Subgroup.mem_map.1 hh
      have hginv : e6InndiagConj K g⁻¹ ∈ E := by
        have e : e6InndiagConj K g⁻¹ = (e6InndiagConj K g)⁻¹ := map_inv _ g
        rw [e]
        exact E.inv_mem hgE
      have h1 := fwd g⁻¹ hginv r hr
      have hr'' : (r : ModGL (E6Tag K) K) = (g.1 : ModGL (E6Tag K) K) * h *
          (g.1 : ModGL (E6Tag K) K)⁻¹ := hr'
      have hginv_coe : ((g⁻¹ : ↥(e6Chat K)) : ModGL (E6Tag K) K) =
          (g.1 : ModGL (E6Tag K) K)⁻¹ := rfl
      have e2 : ((g⁻¹ : ↥(e6Chat K)) : ModGL (E6Tag K) K) * (r : ModGL (E6Tag K) K) *
          ((g⁻¹ : ↥(e6Chat K)) : ModGL (E6Tag K) K)⁻¹ = h := by
        rw [hginv_coe, hr'']
        group
      rw [e2] at h1
      exact h1
  have hQG : Q ≤ (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).group := hQC
  obtain ⟨M, -, ⟨g₁, hg₁, l₁, hl₁, hgl₁⟩, -, F, hF, -, ⟨g₀, hg₀, l₀, hl₀, hl₀1, hgl₀⟩, hdom,
    hsemi⟩ :=
    RootWeightDatum.root_p_subgroup_optimal_parabolic_containment
      (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K) (ringChar K) Q hQG hQp hQ1
  obtain ⟨hJ, -, -, -, -⟩ := hdom g₀ hg₀ l₀ hl₀ hl₀1 hgl₀
  set J₀ : Set (Fin (E6Tag K).rank) :=
    (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).face l₀ with hJ₀
  have hstabN : ∀ x : ModGL (E6Tag K) K, x ∈ e6Chat K →
      x ∈ Subgroup.normalizer (Q : Set (ModGL (E6Tag K) K)) →
      ∀ c : ℝ, (F c).map (x : Module.End K (RootModule (E6Tag K) K)) = F c := by
    intro x hx hxN c
    obtain ⟨c₀, hc₀, t₀, ht₀, rfl⟩ := mem_e6InndiagGL_decomp K hx
    set s : RootModule (E6Tag K) K ≃ₗ[K] RootModule (E6Tag K) K :=
      LinearMap.GeneralLinearGroup.generalLinearEquiv K (RootModule (E6Tag K) K) t₀ with hs_def
    have hs_apply : ∀ v, s v = (t₀ : Module.End K (RootModule (E6Tag K) K)) v :=
      fun v => rfl
    have hs_symm : ∀ v, s.symm v =
        ((t₀⁻¹ : ModGL (E6Tag K) K) : Module.End K (RootModule (E6Tag K) K)) v := by
      intro v
      rw [LinearEquiv.symm_apply_eq, hs_apply, ← Module.End.mul_apply, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Module.End.one_eq_id, LinearMap.id_apply]
    have hs_eq : ∀ g : ModGL (E6Tag K) K, semilinearConjUnit s g = t₀ * g * t₀⁻¹ := by
      intro g
      apply Units.ext
      apply LinearMap.ext
      intro v
      rw [coe_semilinearConjUnit, semilinearConj_apply, hs_symm, hs_apply, Units.val_mul,
        Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
    have hsC : ∀ g : ModGL (E6Tag K) K,
        semilinearConjUnit s g ∈ (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).group ↔
          g ∈ (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).group := by
      intro g
      rw [hs_eq]
      exact (Subgroup.mem_normalizer_iff.1 (e6DiagTorus_le_normalizer K ht₀) g).symm
    have hsW : ∀ χ ∈ (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).weights,
        ((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).weightSpace χ).map s.toLinearMap =
          (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).weightSpace
            ((LinearIsometryEquiv.refl ℝ
              (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).space) χ) := by
      intro χ _
      exact map_weightSpace_eq_of_mem_e6DiagTorus K ht₀ χ
    have hQ' : ∀ x' : ModGL (E6Tag K) K, x' ∈ Q ↔
        ∃ q ∈ Q, c₀ * semilinearConjUnit s q * c₀⁻¹ = x' := by
      intro x'
      simp only [hs_eq]
      constructor
      · intro hx'
        refine ⟨(c₀ * t₀)⁻¹ * x' * (c₀ * t₀), ?_, ?_⟩
        · have h' := (Subgroup.mem_normalizer_iff.1 (inv_mem hxN) x').1 hx'
          rwa [inv_inv] at h'
        · group
      · rintro ⟨q, hq, rfl⟩
        have h' := (Subgroup.mem_normalizer_iff.1 hxN q).1 hq
        have e : c₀ * (t₀ * q * t₀⁻¹) * c₀⁻¹ = c₀ * t₀ * q * (c₀ * t₀)⁻¹ := by group
        rw [e]
        exact h'
    have hcov := hsemi (RingHom.id K) (RingHom.id K) s hsC (LinearIsometryEquiv.refl ℝ _)
      (by simp) hsW c₀ hc₀ Q hQ'
    have h1 := hcov.2.2 g₁ hg₁ l₁ hl₁ hgl₁ c
    have h2 := hF g₁ hg₁ l₁ hl₁ hgl₁ c
    have e : (F c).map s.toLinearMap = (F c).map (t₀ : Module.End K (RootModule (E6Tag K) K)) :=
      rfl
    rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, ← e]
    exact h1.symm.trans h2
  set Ph : Subgroup (ModGL (E6Tag K) K) := parabolicSubgroup (E6Tag K) K J₀ ⊔ e6DiagTorus K
    with hPh
  set Lh : Subgroup (ModGL (E6Tag K) K) := parabolicLevi (E6Tag K) K J₀ ⊔ e6DiagTorus K with hLh
  have hPh_le : Ph ≤ e6Chat K :=
    sup_le ((parabolicSubgroup_le_adjointGroup (E6Tag K) K J₀).trans
      (adjointGroup_le_e6InndiagGL K)) (e6DiagTorus_le_e6InndiagGL K)
  have hg₀I : g₀ ∈ e6Chat K := adjointGroup_le_e6InndiagGL K hg₀
  have hstabG : ∀ x ∈ A, g₀⁻¹ * x * g₀ ∈ Ph := by
    intro x hx
    have hxI := hA_inC x hx
    have hxN := hA_norm x hx
    have hgI : g₀⁻¹ * x * g₀ ∈ e6Chat K :=
      mul_mem (mul_mem (inv_mem hg₀I) hxI) hg₀I
    have key : ∀ c : ℝ,
        ((RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l₀ c).map
          ((g₀⁻¹ * x * g₀ : ModGL (E6Tag K) K) : Module.End K (RootModule (E6Tag K) K)) =
        (RootWeightDatum.ordinary Tag.E6 : RootWeightDatum K).filtration l₀ c := by
      intro c
      have h1 := hF g₀ hg₀ l₀ hl₀1 hgl₀ c
      have h2 := hstabN x hxI hxN c
      rw [submodule_map_units_mul, submodule_map_units_mul, h1, h2, ← h1,
        ← submodule_map_units_mul, inv_mul_cancel, Units.val_one, Module.End.one_eq_id,
        Submodule.map_id]
    exact mem_parabolic_sup_torus_of_stab K hl₀ hgI key
  have hA0 : A.map (MulAut.conj g₀⁻¹).toMonoidHom ≤ Ph := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hstabG x hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact h
  haveI hA0e : IsElementaryAbelian 3 (A.map (MulAut.conj g₀⁻¹).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hA0p : IsPGroup 3 (A.map (MulAut.conj g₀⁻¹).toMonoidHom) :=
    IsElementaryAbelian.isPGroup 3 _
  have hindex := not_three_dvd_index_levi_sup K hK3 J₀
  obtain ⟨y, hyPh, hyA⟩ := exists_conj_le_of_not_dvd_index hA0 hA0p hindex
  obtain ⟨w₀, δ, hδinj, hδ⟩ := exists_longest_simple_perm (E6Tag K)
  set A₁ := (A.map (MulAut.conj g₀⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom with hA₁
  haveI hA₁e : IsElementaryAbelian 3 A₁ := IsElementaryAbelian.map _
  have hA₁card : Nat.card A₁ = 3 ^ 2 := by
    rw [hA₁, Subgroup.card_map_of_injective (MulAut.conj y).injective,
      Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective, hAcard]
  have hLQ : A₁ ≤ Subgroup.normalizer (parabolicRadical (E6Tag K) K J₀ : Set (ModGL (E6Tag K) K)) :=
    hyA.trans (levi_sup_torus_le_normalizer_parabolicRadical K J₀)
  have hLQ' : A₁ ≤ Subgroup.normalizer
      (((parabolicRadical (E6Tag K) K (δ '' J₀)).map
        (MulAut.conj (canonicalRep (coxeterSystem (E6Tag K)) K w₀)⁻¹).toMonoidHom :
          Subgroup (ModGL (E6Tag K) K)) : Set (ModGL (E6Tag K) K)) :=
    hyA.trans (levi_sup_torus_le_normalizer_opposite K w₀ hδ J₀)
  have hG := le_iSup_centralizer_of_normalizes_radicals hK3 hJ (le_of_eq hA₁card.symm) w₀
    hδinj hδ hLQ hLQ'
  have hyC : y * g₀⁻¹ ∈ Subgroup.normalizer (adjointGroup (E6Tag K) K : Set (ModGL (E6Tag K) K)) :=
    e6InndiagGL_le_normalizer K (mul_mem (hPh_le hyPh) (inv_mem hg₀I))
  have hconjeq : A.map (MulAut.conj (y * g₀⁻¹)).toMonoidHom = A₁ := by
    have hfun : (MulAut.conj (y * g₀⁻¹)).toMonoidHom =
        (MulAut.conj y).toMonoidHom.comp (MulAut.conj g₀⁻¹).toMonoidHom := by
      refine MonoidHom.ext fun z => ?_
      show y * g₀⁻¹ * z * (y * g₀⁻¹)⁻¹ = y * (g₀⁻¹ * z * g₀⁻¹⁻¹) * y⁻¹
      group
    rw [hA₁, Subgroup.map_map, hfun]
  have hC_sup : adjointGroup (E6Tag K) K ≤
      ⨆ a ∈ A, ⨆ (_ : a ≠ 1), adjointGroup (E6Tag K) K ⊓
        Subgroup.centralizer ({a} : Set (ModGL (E6Tag K) K)) :=
    le_iSup_inf_centralizer_of_map_conj_normalizer hyC (by rw [hconjeq]; exact hG)
  rw [eq_top_iff]
  intro c _
  have hle : (⨆ a ∈ A, ⨆ (_ : a ≠ 1), adjointGroup (E6Tag K) K ⊓
      Subgroup.centralizer ({a} : Set (ModGL (E6Tag K) K))) ≤
      (Subgroup.closure (fixUnion E)).map (adjointGroup Tag.E6 K).subtype := by
    refine iSup₂_le fun a ha => iSup_le fun ha1 => ?_
    intro y' hy'
    obtain ⟨hyC', hyc⟩ := Subgroup.mem_inf.1 hy'
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc
    obtain ⟨g, hga, hgE⟩ := hA_mem a ha
    have hε1 : e6InndiagConj K g ≠ 1 := by
      intro h
      have hg1 : g = 1 := hinj (h.trans (map_one _).symm)
      apply ha1
      rw [← hga, hg1]
      rfl
    have hzfix : (⟨y', hyC'⟩ : adjointGroup Tag.E6 K) ∈ fixedSubgroup (e6InndiagConj K g) := by
      rw [mem_fixedSubgroup]
      apply Subtype.ext
      show (g.1 : ModGL (E6Tag K) K) * y' * (g.1 : ModGL (E6Tag K) K)⁻¹ = y'
      rw [hga, ← hyc]
      group
    have hzU := fixedSubgroup_subset_fixUnion hgE hε1 hzfix
    exact Subgroup.mem_map.2 ⟨_, Subgroup.subset_closure hzU, rfl⟩
  obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.1 (hle (hC_sup c.2))
  have hzc : z = c := Subtype.ext hzeq
  subst hzc
  exact hz

end E6

end CFSG.LieType.SeitzGeneration.ExcWideThree

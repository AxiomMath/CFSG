module

public import CFSG.LieType.Chevalley.RootWeightOptimalParabolic
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section General

variable {G : Type*} [Group G]

theorem mem_normalizer_map_conj_inv {H : Subgroup G} {n m : G}
    (h : n * m * n⁻¹ ∈ Subgroup.normalizer (H : Set G)) :
    m ∈ Subgroup.normalizer ((H.map (MulAut.conj n⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    MulAut.conj_symm_apply, inv_inv, h (n * x * n⁻¹)]
  have e : n * m * n⁻¹ * (n * x * n⁻¹) * (n * m * n⁻¹)⁻¹ = n * (m * x * m⁻¹) * n⁻¹ := by group
  rw [e]

theorem mem_normalizer_sup_of_mem {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  mem_normalizer_of_map_eq (by
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hH, map_conj_eq_of_mem_normalizer hK])

theorem le_iSup_inf_centralizer_of_map_conj {C A : Subgroup G} {x : G} (hx : x ∈ C)
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
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hx) hyC) hx, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x⁻¹ * y * x * a = x⁻¹ * (y * (x * a * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * a * x⁻¹) * y) * x := by rw [hyc]
      _ = a * (x⁻¹ * y * x) := by group
  intro c hc
  have hmem := hle (h (mul_mem (mul_mem hx hc) (inv_mem hx)))
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmem
  have e : x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c := by group
  rwa [e] at hmem

theorem le_iSup_inf_centralizer_of_coprime {p : ℕ} [Fact p.Prime] {A H C : Subgroup G}
    [Finite A] [Finite H] [IsElementaryAbelian p A] (hcard : p ^ 2 ≤ Nat.card A)
    (hp : ¬ p ∣ Nat.card H) (hAH : A ≤ Subgroup.normalizer (H : Set G)) (hHC : H ≤ C) :
    H ≤ ⨆ a ∈ A, ⨆ (_ : a ≠ 1), C ⊓ Subgroup.centralizer ({a} : Set G) := by
  let : MulDistribMulAction A H := MulDistribMulAction.compHom H (Subgroup.inclusion hAH)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := A) (H := H)
    hcard hp
  have hle : (⨆ (a : A) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) H) ≤
      (⨆ a ∈ A, ⨆ (_ : a ≠ 1), C ⊓ Subgroup.centralizer ({a} : Set G)).comap H.subtype := by
    refine iSup₂_le fun a ha => fun x hx => ?_
    have hfix := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).1 hx
    have hc : (a : G) * x * (a : G)⁻¹ = x := congrArg Subtype.val hfix
    have ha1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    refine Subgroup.mem_iSup_of_mem (a : G) (Subgroup.mem_iSup_of_mem a.2
      (Subgroup.mem_iSup_of_mem ha1 (Subgroup.mem_inf.2 ⟨hHC x.2, ?_⟩)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x : G) * a = (a : G) * x * (a : G)⁻¹ * a := by rw [hc]
      _ = a * x := by rw [inv_mul_cancel_right]
  intro h hh
  have hmem : (⟨h, hh⟩ : H) ∈
      ⨆ (a : A) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) H := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle hmem

theorem exists_conj_le_of_not_dvd_index [Finite G] {p : ℕ} [Fact p.Prime] {P M A : Subgroup G}
    (hAP : A ≤ P) (hA : IsPGroup p A) (hindex : ¬ p ∣ (M.subgroupOf P).index) :
    ∃ y ∈ P, A.map (MulAut.conj y).toMonoidHom ≤ M := by
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow p (M.subgroupOf P)))
  have hS₁p : IsPGroup p ((S₀ : Subgroup (M.subgroupOf P)).map (M.subgroupOf P).subtype) :=
    S₀.isPGroup'.map _
  have hS₁i : ¬ p ∣ ((S₀ : Subgroup (M.subgroupOf P)).map (M.subgroupOf P).subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact fun h => ((Nat.Prime.dvd_mul Fact.out).1 h).elim (Sylow.not_dvd_index S₀) hindex
  have hSM : (hS₁p.toSylow hS₁i : Subgroup P) ≤ M.subgroupOf P := by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.map_subtype_le _
  obtain ⟨c, -, hc⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow ⊤ (hS₁p.toSylow hS₁i)
    le_top (A.subgroupOf P) le_top (hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAP).symm)
  refine ⟨c, c.2, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have h1 : (MulAut.conj c).toMonoidHom (⟨a, hAP ha⟩ : P) ∈
      (A.subgroupOf P).map (MulAut.conj c).toMonoidHom :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ha)
  have h2 := Subgroup.mem_subgroupOf.1 (hSM (hc h1))
  exact h2

end General

section Ordinary

variable {τ : Tag} {k : Type} [Field k]

theorem exists_longest_simple_perm
    (τ : Tag) : ∃ (w₀ : WeylGroup τ) (δ : Fin τ.rank → Fin τ.rank),
    Function.Injective δ ∧ ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1 := by
  obtain ⟨w₀, hmax, -, -, hsq, -, -⟩ := weyl_longest_element τ
  have hsq' : w₀ * w₀ = 1 := by rw [← pow_two]; exact hsq
  choose δ hδ using exists_smul_single_eq_neg (reversesSigns_of_forall_length_le hmax) hsq'
  refine ⟨w₀, δ, fun i j hij => ?_, hδ⟩
  have h : w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = w₀ • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    rw [hδ, hδ, hij]
  exact single_injective_one (smul_left_cancel w₀ h)

theorem rootSubgroup_single_le_parabolicLevi
    {J : Set (Fin τ.rank)} {i : Fin τ.rank}
    (hi : i ∈ J) : rootSubgroup τ k (Pi.single i 1) ≤ parabolicLevi τ k J :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_single]
    exact xUnit_mem_parabolicLevi hi c)

theorem rootSubgroup_neg_single_le_parabolicLevi
    {J : Set (Fin τ.rank)} {i : Fin τ.rank}
    (hi : i ∈ J) : rootSubgroup τ k (-Pi.single i 1) ≤ parabolicLevi τ k J :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_neg_single]
    exact yUnit_mem_parabolicLevi hi c)

theorem map_conj_parabolicLevi_le
    {w₀ : WeylGroup τ} {δ : Fin τ.rank → Fin τ.rank}
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin τ.rank)) :
    (parabolicLevi τ k J).map (MulAut.conj (canonicalRep (coxeterSystem τ) k w₀)).toMonoidHom ≤
      parabolicLevi τ k (δ '' J) := by
  obtain ⟨-, hR, hH⟩ := canonical_weyl_root_transport τ k
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (fun h hh => ?_) ((Subgroup.closure_le _).2 ?_)
  · exact torusGroup_le_parabolicLevi _ ((Subgroup.mem_normalizer_iff.1 (hH w₀) h).1 hh)
  · rintro _ ⟨j, hj, c, rfl | rfl⟩
    · have hx : xUnit τ k j c ∈ rootSubgroup τ k (Pi.single j 1) :=
        CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨c, pinnedX_single τ k j c⟩
      have hmem : (MulAut.conj (canonicalRep (coxeterSystem τ) k w₀)).toMonoidHom
          (xUnit τ k j c) ∈ (rootSubgroup τ k (Pi.single j 1)).map
            (MulAut.conj (canonicalRep (coxeterSystem τ) k w₀)).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hR w₀ _ (isRoot_single τ j), hδ] at hmem
      exact rootSubgroup_neg_single_le_parabolicLevi (Set.mem_image_of_mem δ hj) hmem
    · have hy : yUnit τ k j c ∈ rootSubgroup τ k (-Pi.single j 1) :=
        CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨c, pinnedX_neg_single τ k j c⟩
      have hmem : (MulAut.conj (canonicalRep (coxeterSystem τ) k w₀)).toMonoidHom
          (yUnit τ k j c) ∈ (rootSubgroup τ k (-Pi.single j 1)).map
            (MulAut.conj (canonicalRep (coxeterSystem τ) k w₀)).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy
      rw [hR w₀ _ (isRoot_neg_single τ j), smul_neg, hδ, neg_neg] at hmem
      exact rootSubgroup_single_le_parabolicLevi (Set.mem_image_of_mem δ hj) hmem

theorem card_parabolicSubgroup_eq_mul
    (J : Set (Fin τ.rank)) :
    Nat.card (parabolicSubgroup τ k J) =
      Nat.card (parabolicRadical τ k J) * Nat.card (parabolicLevi τ k J) := by
  obtain ⟨hQP, -, -, hMP, -, -, huniq, -⟩ := parabolic_root_radical_Levi_factors τ k J
  let f : parabolicRadical τ k J × parabolicLevi τ k J → parabolicSubgroup τ k J :=
    fun qm => ⟨qm.1 * qm.2, mul_mem (hQP qm.1.2) (hMP qm.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun g => ?_⟩
    · have h := congrArg Subtype.val hxy
      obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_parabolic x.1.2 y.1.2 x.2.2 y.2.2 h
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · obtain ⟨⟨q, m⟩, ⟨hq, hm, hg⟩, -⟩ := huniq g g.2
      exact ⟨(⟨q, hq⟩, ⟨m, hm⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem parabolicLevi_index_eq
    [Finite k] (J : Set (Fin τ.rank)) :
    ((parabolicLevi τ k J).subgroupOf (parabolicSubgroup τ k J)).index =
      Nat.card (parabolicRadical τ k J) := by
  have := finite_modGL (τ := τ) (K := k)
  have hMP := parabolicLevi_le_parabolicSubgroup (K := k) J
  have h := ((parabolicLevi τ k J).subgroupOf (parabolicSubgroup τ k J)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMP).toEquiv, card_parabolicSubgroup_eq_mul,
    mul_comm (Nat.card (parabolicRadical τ k J))] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

theorem not_dvd_card_of_isPGroup {G : Type*} [Group G] {H : Subgroup G} [Finite H] {r p : ℕ}
    [Fact r.Prime] [Fact p.Prime] (hrp : r ≠ p) (hH : IsPGroup r H) : ¬ p ∣ Nat.card H := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hH
  rw [hm]
  intro h
  exact hrp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1
    ((Nat.Prime.dvd_of_dvd_pow Fact.out h))).symm

theorem le_iSup_centralizer_of_le_parabolicLevi
    [Finite k] {r p : ℕ} [Fact r.Prime]
    [Fact p.Prime] [CharP k r] (hrp : r ≠ p) [IsSimpleGroup (adjointGroup τ k)]
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) {A : Subgroup (ModGL τ k)}
    [IsElementaryAbelian p A] (hcard : p ^ 2 ≤ Nat.card A) (hAM : A ≤ parabolicLevi τ k J) :
    adjointGroup τ k ≤
      ⨆ a ∈ A, ⨆ (_ : a ≠ 1), adjointGroup τ k ⊓ Subgroup.centralizer ({a} : Set (ModGL τ k)) := by
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
  have hpQ := not_dvd_card_of_isPGroup hrp hQp
  have hpQ' := not_dvd_card_of_isPGroup hrp hQ'p
  have h1 := le_iSup_inf_centralizer_of_coprime hcard hpQ (hAM.trans hMQ) hQC
  have h2 := le_iSup_inf_centralizer_of_coprime hcard hpQ' (hAM.trans hMQ') hQ'C
  exact hCX.trans (sup_le h1 h2)

end Ordinary

theorem ordinary_root_invariant_prime_subgroup_centralizer_generation
    (τ : Tag) (k : Type)
    [Field k] [Finite k] (r p : ℕ) [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    [IsSimpleGroup (adjointGroup τ k)] (A : Subgroup (ModGL τ k)) (hAC : A ≤ adjointGroup τ k)
    [IsElementaryAbelian p A] (hcard : p ^ 2 ≤ Nat.card A) (R : Subgroup (ModGL τ k))
    (hRC : R ≤ adjointGroup τ k) (hRr : IsPGroup r R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL τ k))) :
    (⨆ a ∈ A, ⨆ (_ : a ≠ 1), adjointGroup τ k ⊓ Subgroup.centralizer ({a} : Set (ModGL τ k))) =
      adjointGroup τ k := by
  have := finite_modGL (τ := τ) (K := k)
  refine le_antisymm (iSup₂_le fun a _ => iSup_le fun _ => inf_le_left) ?_
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
  have hA1 : A.map (MulAut.conj g'⁻¹).toMonoidHom ≤ parabolicSubgroup τ k J := by
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
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_not_dvd_index hA1 hA1p hindex
  have hyC : y ∈ adjointGroup τ k := parabolicSubgroup_le_adjointGroup τ k J hy
  have hxC : y * g'⁻¹ ∈ adjointGroup τ k := mul_mem hyC (inv_mem hgC)
  have hmap : A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom =
      (A.map (MulAut.conj g'⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map, map_mul]
    rfl
  have hAx : A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom ≤ parabolicLevi τ k J := hmap ▸ hyA
  have : IsElementaryAbelian p (A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hcard' : p ^ 2 ≤ Nat.card (A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (y * g'⁻¹)).injective]
    exact hcard
  exact le_iSup_inf_centralizer_of_map_conj hxC
    (le_iSup_centralizer_of_le_parabolicLevi hrp hJ' hcard' hAx)

end CFSG.LieType.Chevalley

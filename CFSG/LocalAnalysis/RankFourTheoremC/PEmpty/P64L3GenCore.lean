module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64L3GenMat
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoDefs
public import CFSG.Adapters.StatedClassicalOrders

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64L3Gen

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix Subgroup
open scoped Pointwise

theorem not_dvd_pow_sub_one' {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) : ¬ p ∣ p ^ k - 1 := by
  intro h
  have h1 : p ∣ p ^ k := dvd_pow_self p (by omega)
  have h2 : p ∣ p ^ k - (p ^ k - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

theorem scalar_injective_fin3 {F : Type} [Field F] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) (R := F)) := by
  intro u v h
  apply Units.ext
  have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this

theorem factorization_PSL3 {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p) : (Nat.card (PSL3 F)).factorization p = 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (PSL3 F) := Finite.of_surjective (phi3 F) (phi3_surjective F)
  have hSL : Nat.card (StatedSL 3 F) = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
    have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
    rw [CFSG.Open.StatedAPI.card_statedSL_eq_prod (K := F) (d := 3) (by norm_num), hF, hI,
      Finset.prod_pair (by norm_num)]
  have hGZ : Nat.card (StatedSL 3 F) =
      Nat.card (PSL3 F) * Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  set Z : Subgroup (StatedSL 3 F) := (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)
    with hZ
  have hZdvd : Nat.card Z ∣ p - 1 := by
    have hle : Z.map (StatedSL 3 F).subtype ≤ StatedScalars (Fin 3) F := by
      rintro _ ⟨z, hz, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hz
    have hcard1 : Nat.card (Z.map (StatedSL 3 F).subtype) = Nat.card Z :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    have hcard2 : Nat.card (StatedScalars (Fin 3) F) = p - 1 := by
      rw [StatedScalars, ← Nat.card_congr
        (MonoidHom.ofInjective (scalar_injective_fin3 (F := F))).toEquiv, Nat.card_units, hF]
    rw [← hcard1, ← hcard2]
    exact Subgroup.card_dvd_of_le hle
  have hcop : Nat.Coprime p (Nat.card Z) := by
    have h1 : Nat.Coprime p (p - 1) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have := Nat.le_of_dvd (by have := hp.two_le; omega) h
      have := hp.two_le
      omega
    exact Nat.Coprime.coprime_dvd_right hZdvd h1
  have hM : ¬ p ∣ (p ^ 2 - 1) * (p ^ 3 - 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact not_dvd_pow_sub_one' hp (by norm_num) h
    · exact not_dvd_pow_sub_one' hp (by norm_num) h
  have hdvd3 : p ^ 3 ∣ Nat.card (PSL3 F) := by
    have h1 : p ^ 3 ∣ Nat.card (PSL3 F) * Nat.card Z := by
      rw [← hGZ, hSL]
      exact Dvd.intro _ rfl
    exact (Nat.Coprime.pow_left 3 hcop).dvd_of_dvd_mul_right h1
  have hnd4 : ¬ p ^ 4 ∣ Nat.card (PSL3 F) := by
    intro h
    have h1 : p ^ 4 ∣ Nat.card (PSL3 F) * Nat.card Z := Dvd.dvd.mul_right h _
    rw [← hGZ, hSL] at h1
    have h2 : p ^ 3 * p ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
      rw [← pow_succ]
      exact h1
    exact hM (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 3) h2)
  have hne : Nat.card (PSL3 F) ≠ 0 := Nat.card_pos.ne'
  have h3 := (hp.pow_dvd_iff_le_factorization hne).1 hdvd3
  have h4 : ¬ 4 ≤ (Nat.card (PSL3 F)).factorization p := fun h =>
    hnd4 ((hp.pow_dvd_iff_le_factorization hne).2 h)
  omega

theorem injective_phi3_uniT (F : Type) [Field F] :
    Function.Injective ((phi3 F).comp (uniT F).subtype) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨u, hu'⟩ h
  obtain ⟨a, b, c, hu⟩ : ∃ a b c : F, (u : Matrix (Fin 3) (Fin 3) F) = utMat a b c := hu'
  have h0 : phi3 F u = 1 := h
  have ha := phi3_offdiag h0 (i := 0) (j := 1) (by decide)
  have hb := phi3_offdiag h0 (i := 0) (j := 2) (by decide)
  have hc := phi3_offdiag h0 (i := 1) (j := 2) (by decide)
  rw [hu] at ha hb hc
  simp [utMat] at ha hb hc
  subst ha hb hc
  apply Subtype.ext
  apply Subtype.ext
  rw [hu]
  simp [utMat, Matrix.one_fin_three]

@[expose] noncomputable def Ubar (F : Type) [Field F] : Subgroup (PSL3 F) :=
  ((phi3 F).comp (uniT F).subtype).range

theorem card_Ubar {F : Type} [Field F] [Finite F] : Nat.card (Ubar F) = Nat.card F ^ 3 := by
  rw [Ubar, ← Nat.card_congr (MonoidHom.ofInjective (injective_phi3_uniT F)).toEquiv,
    card_uniT]

theorem card_Ubar_eq {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p) :
    Nat.card (Ubar F) = p ^ (Nat.card (PSL3 F)).factorization p := by
  rw [card_Ubar, hF, factorization_PSL3 hp hF]

theorem e1SL_mem_uniT {F : Type} [Field F] (a c : F) : e1SL a c ∈ uniT F := by
  show ∃ a' b' c' : F, ((e1SL a c : SL3 F) : Matrix (Fin 3) (Fin 3) F) = utMat a' b' c'
  exact ⟨a, c, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp [e1SL, e1Mat, utMat]⟩

theorem e2SL_mem_uniT {F : Type} [Field F] (b c : F) : e2SL b c ∈ uniT F := by
  show ∃ a' b' c' : F, ((e2SL b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) = utMat a' b' c'
  exact ⟨0, c, b, by ext i j; fin_cases i <;> fin_cases j <;> simp [e2SL, e2Mat, utMat]⟩

theorem S1_le_Ubar {F : Type} [Field F] : S1 F ≤ Ubar F := by
  intro x hx
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.1 hx
  exact MonoidHom.mem_range.2
    ⟨⟨_, e1SL_mem_uniT (Multiplicative.toAdd t).1 (Multiplicative.toAdd t).2⟩, rfl⟩

theorem S2_le_Ubar {F : Type} [Field F] : S2 F ≤ Ubar F := by
  intro x hx
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.1 hx
  exact MonoidHom.mem_range.2
    ⟨⟨_, e2SL_mem_uniT (Multiplicative.toAdd t).1 (Multiplicative.toAdd t).2⟩, rfl⟩

theorem mem_normalizer_equiv_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) (S : Subgroup G)
    (x : G) :
    e x ∈ normalizer ((S.map e.toMonoidHom : Subgroup H) : Set H) ↔
      x ∈ normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h n
    have := h (e n)
    simpa only [Subgroup.mem_map_equiv, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
      MulEquiv.symm_apply_apply] using this
  · intro h m
    simpa only [Subgroup.mem_map_equiv, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
      MulEquiv.symm_apply_apply] using h (e.symm m)

theorem core_U {F : Type} [Field F] (Y : Subgroup (PSL3 F))
    (h1 : normalizer ((S1 F : Subgroup (PSL3 F)) : Set (PSL3 F)) ≤ Y)
    (h2 : normalizer ((S2 F : Subgroup (PSL3 F)) : Set (PSL3 F)) ≤ Y) : Y = ⊤ := by
  set H : Subgroup (SL3 F) := Y.comap (phi3 F) with hH
  have hT1 : ∀ x : SL3 F, (x : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 →
      (x : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 → x ∈ H := fun x hx1 hx2 =>
    h1 (phi3_mem_normalizer_S1 hx1 hx2)
  have hT2 : ∀ x : SL3 F, (x : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 →
      (x : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 → x ∈ H := fun x hx1 hx2 =>
    h2 (phi3_mem_normalizer_S2 hx1 hx2)
  have htr : ∀ (i j : Fin 3) (hij : i ≠ j) (c : F),
      Matrix.SpecialLinearGroup.transvection hij c ∈ H := by
    intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hT1 _ (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
        (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
    · exact hT1 _ (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
        (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
    · exact hT2 _ (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
        (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
    · exact absurd rfl hij
    · exact hT1 _ (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
        (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
    ·
      show Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c ∈ H
      have ha : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ H :=
        hT1 _ (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
          (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
      have hb : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide)
          (1 : F) ∈ H :=
        hT2 _ (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
          (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
      have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection
        (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide)
        (show (2 : Fin 3) ≠ 0 by decide) c (1 : F)
      rw [mul_one] at hcomm
      rw [← hcomm, commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    · exact hT1 _ (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
        (by simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply])
    · exact absurd rfl hij
  have hle : Subgroup.closure (Set.range
      (Matrix.TransvectionStruct.toSpecialLinearGroup :
        Matrix.TransvectionStruct (Fin 3) F → SL3 F)) ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    obtain ⟨i, j, hij, c⟩ := t
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    exact htr i j hij c
  rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 3)] at hle
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨m, rfl⟩ := phi3_surjective F g
  exact hle (Subgroup.mem_top m)

theorem core_G {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p)
    (P : Sylow p (PSL3 F)) (Y : Subgroup (PSL3 F))
    (hY : ∀ S : Subgroup (PSL3 F), S ≤ (P : Subgroup (PSL3 F)) →
      2 ≤ CFSG.Open.pRank p S → normalizer (S : Set (PSL3 F)) ≤ Y) : Y = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Q₀ : Sylow p (PSL3 F) := Sylow.ofCard (Ubar F) (card_Ubar_eq hp hF)
  haveI : Finite (Sylow p (PSL3 F)) :=
    Finite.of_injective (fun Q : Sylow p (PSL3 F) => (Q : Set (PSL3 F))) SetLike.coe_injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL3 F) Q₀ P
  have hcj : ∀ u ∈ Ubar F, MulAut.conj g u ∈ (P : Subgroup (PSL3 F)) := by
    intro u hu
    have h1 : MulAut.conj g u ∈ MulAut.conj g • (Q₀ : Subgroup (PSL3 F)) :=
      Subgroup.smul_mem_pointwise_smul u (MulAut.conj g) _ hu
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    exact h1
  have hsub : ∀ S : Subgroup (PSL3 F), S ≤ Ubar F → 2 ≤ CFSG.Open.pRank p S →
      normalizer (S : Set (PSL3 F)) ≤ Y.comap (MulAut.conj g).toMonoidHom := by
    intro S hS hS2 x hx
    have hSP : S.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup (PSL3 F)) := by
      rintro _ ⟨s, hs, rfl⟩
      exact hcj s (hS hs)
    have hS2' : 2 ≤ CFSG.Open.pRank p (S.map (MulAut.conj g).toMonoidHom) :=
      le_trans hS2 (CFSG.SectionRank.pRank_le_map hp.one_lt (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective S)
    have hx' := (mem_normalizer_equiv_iff (MulAut.conj g) S x).2 hx
    exact hY _ hSP hS2' hx'
  have hYc : Y.comap (MulAut.conj g).toMonoidHom = ⊤ :=
    core_U _ (hsub _ S1_le_Ubar (two_le_pRank_S1 hp hF))
      (hsub _ S2_le_Ubar (two_le_pRank_S2 hp hF))
  refine eq_top_iff.2 fun y _ => ?_
  have hy : (MulAut.conj g).symm y ∈ Y.comap (MulAut.conj g).toMonoidHom := by
    rw [hYc]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hy
  exact hy

end P64L3Gen

open P64L3Gen Subgroup

theorem kdi278L3_holds : KDI278L3 := by
  unfold KDI278L3
  intro p hp hp5 K _ _ hK P Y hY
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hFfield, hFfin, hF, ⟨e⟩⟩ := hK
  let P' : Sylow p (PSL3 F) := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P
  have hP' : (P' : Subgroup (PSL3 F)) = (P : Subgroup K).map e.toMonoidHom := rfl
  have hY' : ∀ S : Subgroup (PSL3 F), S ≤ (P' : Subgroup (PSL3 F)) →
      2 ≤ CFSG.Open.pRank p S → normalizer (S : Set (PSL3 F)) ≤ Y.map e.toMonoidHom := by
    intro S hS hS2 x hx
    have hS₀P : S.map e.symm.toMonoidHom ≤ (P : Subgroup K) := by
      rintro _ ⟨s, hs, rfl⟩
      have hs' : s ∈ (P : Subgroup K).map e.toMonoidHom := hS hs
      obtain ⟨p0, hp0, hp0e⟩ := Subgroup.mem_map.1 hs'
      have hsp : e.symm s = p0 := by
        rw [← hp0e]
        simp
      show e.symm s ∈ (P : Subgroup K)
      rw [hsp]
      exact hp0
    have hS₀2 : 2 ≤ CFSG.Open.pRank p (S.map e.symm.toMonoidHom) :=
      le_trans hS2 (CFSG.SectionRank.pRank_le_map hp.one_lt e.symm.toMonoidHom
        e.symm.injective S)
    have hx₀ := (mem_normalizer_equiv_iff e.symm S x).2 hx
    have hmem : e.symm x ∈ Y := hY _ hS₀P hS₀2 hx₀
    have := Subgroup.mem_map_of_mem e.toMonoidHom hmem
    simpa using this
  have hYtop : Y.map e.toMonoidHom = ⊤ := P64L3Gen.core_G hp hF P' (Y.map e.toMonoidHom) hY'
  refine eq_top_iff.2 fun k _ => ?_
  have hk : e k ∈ Y.map e.toMonoidHom := by
    rw [hYtop]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.1 hk
  rw [e.injective hyk] at hy
  exact hy

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

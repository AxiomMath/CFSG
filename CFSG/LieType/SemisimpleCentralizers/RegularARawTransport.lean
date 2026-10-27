module

public import CFSG.LieType.SemisimpleCentralizers.LinearCentralizerSolvable
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcTransport

public section

namespace CFSG.LieType.SemisimpleCentralizers

open CFSG.Assembly CFSG.StandardType

theorem isSolvable_ggFixedSubgroup_of_rawLinear
    {K : Type} [Field K] [Finite K]
    {m n p : ℕ} (hK : Nat.card K = 2 ^ n)
    (hp : p.Prime) (hpF : p ∣ Nat.card K ^ 2 - 1)
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin (m + 1)) K)))}
    (hEsub : E ≤ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin (m + 1)) K)) Set.univ)
    (hEp : IsPGroup p E)
    (hNPC : CFSG.HasNormalPComplement p
      ↥⁅ggFixedSubgroup E, ggFixedSubgroup E⁆) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    apply charP_of_card_eq_prime_pow
    simpa [Nat.card_eq_fintype_card] using hK
  let L : Subgroup (GL (Fin (m + 1)) K) := LargeEvenSLGroup (Fin (m + 1)) K
  let π : ↥L →* LargeEvenProj L := LargeEvenProjMk L
  let E' : Type := ↥E
  let φ : E' →* MulAut (LargeEvenProj L) := E.subtype
  let G : Type := LargeEvenProj L ⋊[φ] E'
  let ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) K →* G :=
    (SemidirectProduct.inl : LargeEvenProj L →* G).comp
      (π.comp (InnerDiagA.slEquiv (m := m) K).toMonoidHom)
  let A : Subgroup G := (SemidirectProduct.inr : E' →* G).range
  let F : Subgroup (LargeEvenProj L) := ggFixedSubgroup E
  let H : Subgroup G := ψ.range ⊓ Subgroup.centralizer (A : Set G)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcomp_surj : Function.Surjective
      (π.comp (InnerDiagA.slEquiv (m := m) K).toMonoidHom) :=
    hπsurj.comp (InnerDiagA.slEquiv (m := m) K).surjective
  have hψrange : ψ.range = (SemidirectProduct.inl : LargeEvenProj L →* G).range := by
    dsimp only [ψ]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hcomp_surj]
    exact Subgroup.map_top _
  have hkerπ : π.ker ≤ Subgroup.center ↥L := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    have hg' : (g : GL (Fin (m + 1)) K) ∈ LargeEvenScalars (Fin (m + 1)) K := by
      have hker : π.ker = (LargeEvenScalars (Fin (m + 1)) K).subgroupOf L := by
        dsimp only [π, L]
        exact QuotientGroup.ker_mk' _
      rw [hker] at hg
      exact Subgroup.mem_subgroupOf.mp hg
    have hgc : (g : GL (Fin (m + 1)) K) ∈ Subgroup.center (GL (Fin (m + 1)) K) := by
      rw [largeEvenScalars_def] at hg'
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hg'
    exact Subgroup.mem_center_iff.mp hgc (h : GL (Fin (m + 1)) K)
  have hkerψ : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K) := by
    intro u hu
    have h1 : (π.comp (InnerDiagA.slEquiv (m := m) K).toMonoidHom) u = 1 := by
      have hleft := congrArg SemidirectProduct.left (MonoidHom.mem_ker.mp hu)
      simpa [ψ] using hleft
    have h2 : InnerDiagA.slEquiv (m := m) K u ∈ π.ker := MonoidHom.mem_ker.mpr h1
    have h3 : ∀ y : ↥L,
        y * InnerDiagA.slEquiv (m := m) K u =
          InnerDiagA.slEquiv (m := m) K u * y :=
      Subgroup.mem_center_iff.mp (hkerπ h2)
    rw [Subgroup.mem_center_iff]
    intro v
    apply (InnerDiagA.slEquiv (m := m) K).injective
    rw [map_mul, map_mul]
    exact h3 (InnerDiagA.slEquiv (m := m) K v)
  have hEA : ∀ a ∈ A, ∃ A₀ : GL (Fin (m + 1)) K,
      (a, A₀) ∈ LinFusion.ggInducedPairs ψ := by
    rintro a ha
    obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨A₀, -, hA₀⟩ := hEsub e.2
    refine ⟨A₀, ?_⟩
    rw [LinFusion.mem_ggInducedPairs]
    intro u
    calc
      (SemidirectProduct.inr e) * ψ u * (SemidirectProduct.inr e)⁻¹
          = SemidirectProduct.inl
              ((φ e) (π (InnerDiagA.slEquiv (m := m) K u))) := by
            have hψu : ψ u = SemidirectProduct.inl
                (π (InnerDiagA.slEquiv (m := m) K u)) := rfl
            rw [hψu]
            simpa only [map_inv] using
              (SemidirectProduct.inl_aut (φ := φ) e
                (π (InnerDiagA.slEquiv (m := m) K u))).symm
      _ = SemidirectProduct.inl
            (π (MulAut.conjNormal A₀ (InnerDiagA.slEquiv (m := m) K u))) := by
            congr 1
            exact hA₀ _ _ (MulAut.conjNormal_apply A₀ _)
      _ = ψ (InnerDiagA.conjSL A₀ u) := by
            simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
            rw [InnerDiagA.slEquiv_conjSL]
  have hE_G : IsPGroup p A := by
    let eTop : E' ≃* ↥(⊤ : Subgroup E') := Subgroup.topEquiv.symm
    let eMap : ↥(⊤ : Subgroup E') ≃*
        ↥((⊤ : Subgroup E').map (SemidirectProduct.inr : E' →* G)) :=
      Subgroup.equivMapOfInjective _ _ SemidirectProduct.inr_injective
    have hmapA : (⊤ : Subgroup E').map (SemidirectProduct.inr : E' →* G) = A := by
      rw [Subgroup.map_top]
    let eA : E' ≃* A := (eTop.trans eMap).trans (MulEquiv.subgroupCongr hmapA)
    exact IsPGroup.of_equiv hEp eA
  have hHF : H = F.map (SemidirectProduct.inl : LargeEvenProj L →* G) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxψ, hxcent⟩ := hx
      rw [hψrange] at hxψ
      obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp hxψ
      refine Subgroup.mem_map.mpr ⟨r, ?_, hr⟩
      change ∀ ε ∈ E, ε r = r
      intro e he
      have hmem : SemidirectProduct.inr (⟨e, he⟩ : E') ∈ A :=
        MonoidHom.mem_range.mpr ⟨⟨e, he⟩, rfl⟩
      have hcomm := hxcent (SemidirectProduct.inr (⟨e, he⟩ : E')) hmem
      rw [← hr] at hcomm
      have hconj : (SemidirectProduct.inr (φ := φ) (⟨e, he⟩ : E') : G) *
          (SemidirectProduct.inl (φ := φ) r : G) *
            (SemidirectProduct.inr (φ := φ) (⟨e, he⟩ : E'))⁻¹ =
          (SemidirectProduct.inl (φ := φ) r : G) := by
        rw [hcomm]
        group
      have hfix : (φ (⟨e, he⟩ : E')) r = r := by
        have h := (SemidirectProduct.inl_aut (φ := φ) (⟨e, he⟩ : E') r).symm
        have h' : (SemidirectProduct.inr (φ := φ) (⟨e, he⟩ : E') : G) *
            (SemidirectProduct.inl (φ := φ) r : G) *
              (SemidirectProduct.inr (φ := φ) (⟨e, he⟩ : E'))⁻¹ =
            (SemidirectProduct.inl (φ := φ) ((φ (⟨e, he⟩ : E')) r) : G) := by
          simpa only [map_inv] using h
        rw [h'] at hconj
        exact SemidirectProduct.inl_injective hconj
      change e r = r at hfix
      exact hfix
    · rintro ⟨r, hrF, rfl⟩
      rw [Subgroup.mem_inf]
      constructor
      · rw [hψrange]
        exact MonoidHom.mem_range.mpr ⟨r, rfl⟩
      · rw [Subgroup.mem_centralizer_iff]
        rintro a ha
        obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp ha
        have hfix : (φ e) r = r := hrF e.1 e.2
        calc
          (SemidirectProduct.inr (φ := φ) e : G) *
              (SemidirectProduct.inl (φ := φ) r : G)
              = (SemidirectProduct.inl (φ := φ) ((φ e) r) : G) *
                  (SemidirectProduct.inr (φ := φ) e : G) := by
                rw [SemidirectProduct.inl_aut, map_inv]
                group
          _ = (SemidirectProduct.inl (φ := φ) r : G) *
                (SemidirectProduct.inr (φ := φ) e : G) := by
                rw [hfix]
  let eMap : ↥F ≃* ↥(F.map (SemidirectProduct.inl : LargeEvenProj L →* G)) :=
    Subgroup.equivMapOfInjective F (SemidirectProduct.inl : LargeEvenProj L →* G)
      SemidirectProduct.inl_injective
  let eHF : ↥H ≃* ↥F := (MulEquiv.subgroupCongr hHF).trans eMap.symm
  have hNPC_absF : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥F) := by
    let eF : ↥(_root_.commutator ↥F) ≃* ↥⁅F, F⁆ :=
      (Subgroup.equivMapOfInjective (_root_.commutator ↥F) F.subtype F.subtype_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator F))
    exact CFSG.hasNormalPComplement_of_equiv p eF.symm hNPC
  have hNPC_H : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥H) := by
    let eComm : ↥(_root_.commutator ↥H) ≃* ↥(_root_.commutator ↥F) :=
      (Subgroup.equivMapOfInjective (_root_.commutator ↥H) eHF.toMonoidHom eHF.injective).trans
        (MulEquiv.subgroupCongr (by
          rw [map_commutator_eq, MonoidHom.range_eq_top.mpr eHF.surjective]
          rfl))
    exact CFSG.hasNormalPComplement_of_equiv p eComm.symm hNPC_absF
  have h2card : Even (Nat.card K) := by
    rcases n with _ | n
    · exfalso
      have h1 : Nat.card K = 1 := by simpa using hK
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · rw [hK]
      exact even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.succ_ne_zero n))
  have hKgt1 : 1 < Nat.card K := Finite.one_lt_card
  have h2sq : Even (Nat.card K ^ 2) := Even.pow_of_ne_zero h2card (by norm_num : 2 ≠ 0)
  have hodd : Odd (Nat.card K ^ 2 - 1) :=
    Nat.Even.sub_odd (by nlinarith [hKgt1]) h2sq odd_one
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (by simpa using hpF))
  haveI : Finite (LargeEvenProj L) := by
    dsimp only [L]
    infer_instance
  haveI : Finite E' := by
    dsimp only [E']
    infer_instance
  haveI : Finite G := by
    dsimp only [G]
    exact Finite.of_equiv (LargeEvenProj L × E') SemidirectProduct.equivProd.symm
  let eAmb : ↥(_root_.commutator ↥H) ≃* ↥⁅H, H⁆ :=
    (Subgroup.equivMapOfInjective (_root_.commutator ↥H) H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator H))
  have hNPC_amb : CFSG.HasNormalPComplement p ↥⁅H, H⁆ :=
    CFSG.hasNormalPComplement_of_equiv p eAmb hNPC_H
  have hHsolv : Group.IsSolvable ↥H :=
    isSolvable_centralizer_of_hasNormalPComplement
      (m := m) (F := K) (G := G) hkerψ hp hp2 hpF hE_G hEA hNPC_amb
  haveI : Group.IsSolvable ↥H := hHsolv
  exact Group.isSolvable_of_surjective (f := eHF.toMonoidHom) eHF.surjective

theorem largeEvenLabelAll_A_commonFixed_isSolvable
    {m n p : ℕ} (hp : p.Prime) (hpF : p ∣ (2 ^ n) ^ 2 - 1) :
    LargeEvenLabelAll (⟨.A, m, n⟩ : LargeEvenLabel) fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), E ≤ I → IsPGroup p E →
        CFSG.HasNormalPComplement p ↥⁅ggFixedSubgroup E, ggFixedSubgroup E⁆ →
        Group.IsSolvable ↥(ggFixedSubgroup E) := by
  intro Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hKfield, hKfinite, hKcard, hQRIF⟩ := hQ
  refine ⟨K, hKfield, hKfinite, hKcard, hQRIF, ?_⟩
  intro E hEsub hEp hNPC
  exact isSolvable_ggFixedSubgroup_of_rawLinear hKcard hp (by rwa [hKcard]) hEsub hEp hNPC

end CFSG.LieType.SemisimpleCentralizers

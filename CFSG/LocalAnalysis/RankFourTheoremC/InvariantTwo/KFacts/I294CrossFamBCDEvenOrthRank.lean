module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenOrth
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenWeir

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.BCDEven

open CFSG.Open Subgroup Polynomial Module Submodule CFSG.LocalAnalysis.RankFourTheoremC
  QuadraticMap CFSG.GroupTheory.WeirSylow
open LinearMap (BilinForm)

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem odd_card_of_odd_finrank {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (hodd : Odd (finrank K V)) :
    Odd (Nat.card K) := by
  haveI := Fintype.ofFinite K
  by_contra hne
  have hmod : Fintype.card K % 2 = 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.even_iff.1 (Nat.not_odd_iff_even.1 hne)
  have hchar : ringChar K = 2 := FiniteField.even_card_iff_char_two.2 hmod
  haveI : CharP K 2 := ringChar.of_eq hchar
  have halt : (polarBilin Q).IsAlt := fun x => by
    rw [polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul]
    exact CharTwo.add_self_eq_zero _
  exact (Nat.not_even_iff_odd.2 hodd) (LinearMap.BilinForm.IsAlt.even_finrank halt hQ)

theorem le_pRank_orth (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) {e : ℕ} (he : 0 < e)
    (hee : Even e) (hpe : p ∣ Nat.card K ^ e - 1) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate) {k : ℕ}
    (hk : k * e + 2 ≤ finrank K V ∨ (Odd (finrank K V) ∧ k * e + 1 ≤ finrank K V)) :
    k ≤ CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  rcases Nat.even_or_odd' (finrank K V) with ⟨n, hn | hn⟩
  · have hk' : k * e + 2 ≤ 2 * n := by
      rcases hk with h | ⟨hodd, -⟩
      · omega
      · exfalso
        rw [hn] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) ⟨n, by ring⟩
    exact le_pRank_orthogonalGroup_even hp2 hpK he hee hpe Q hQ hn hk'
  · have hK : Odd (Nat.card K) := odd_card_of_odd_finrank hQ ⟨n, hn⟩
    have hk' : k * e ≤ 2 * n := by
      rcases hk with h | ⟨-, h⟩ <;> omega
    exact le_pRank_orthogonalGroup_odd hp2 hpK he hee hpe hK Q hQ hn hk'

theorem isMulCommutative_of_isPGroup_equiv (hp2 : Odd p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : 0 < e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) {W : Type} [AddCommGroup W]
    [Module K W] [Module.Finite K W] (G : Subgroup (W ≃ₗ[K] W))
    (hne : Module.finrank K W / e < p) {P : Subgroup G} (hP : IsPGroup p P) :
    IsMulCommutative P := by
  let ψ : G →* (Module.End K W)ˣ :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm.toMonoidHom).comp
      (Subgroup.subtype _)
  have hψ : Function.Injective ψ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm.injective.comp
      (Subgroup.subtype_injective _)
  exact isMulCommutative_of_map_injective ψ hψ
    (isMulCommutative_of_isPGroup_GL hp2 hpK he hpe hne (hP.map ψ))

theorem three_le_pRank_orthogonal (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ} (he : 0 < e)
    (hee : Even e) (hpe : p ∣ Nat.card K ^ e - 1) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 * e ≤ finrank K V) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have hee2 : 2 ≤ e := by
    obtain ⟨m, hm⟩ := hee
    omega
  exact le_pRank_orth (by omega) hpK he hee hpe Q hQ (Or.inl (by omega))

theorem three_le_pRank_centralizer_orthogonal (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : 0 < e) (hee : Even e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j)
    {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 * e ≤ finrank K V)
    (y : TauCeti.QuadraticMap.orthogonalGroup Q) (hy : y ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (TauCeti.QuadraticMap.orthogonalGroup Q))) := by
  have hp2 : p ≠ 2 := by omega
  have hp2' : Odd p := hp.out.odd_of_ne_two hp2
  have hp0 := natCast_ne_zero_of_not_dvd_card hp.out hpK
  have hpe1 : p ∣ Nat.card K ^ e - 1 := (hpe e).2 dvd_rfl
  have hee2 : 2 ≤ e := by
    obtain ⟨m, hm⟩ := hee
    omega
  have hrefl := polarBilin_isRefl Q
  set B : BilinForm K V := polarBilin Q with hB
  set yL : V ≃ₗ[K] V := (y : V ≃ₗ[K] V) with hyL
  have hyLp : yL ^ p = 1 := by
    have := congrArg (fun x : TauCeti.QuadraticMap.orthogonalGroup Q => (x : V ≃ₗ[K] V)) hy
    simpa using this
  let yE : Module.End K V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom yL
  have hyEp : yE ^ p = 1 := by rw [← map_pow, hyLp, map_one]
  have hyB : ∀ u v, polarBilin Q (yE u) (yE v) = polarBilin Q u v := fun u v =>
    polarBilin_apply_of_mem_orthogonalGroup y.2 u v
  have hdeg : ∀ f : K[X], Irreducible f → f ∣ X ^ p - 1 → f.natDegree ≤ e :=
    fun f hf hfP => natDegree_le_of_dvd_X_pow_sub_one he hpe1 hf hfP
  obtain ⟨W, hWinv, hWd, hW3, hW5⟩ :=
    exists_nondeg_window (c := 3) hyEp hp0 hp.out.pos he hdeg hrefl hQ hyB (by omega)
  have hCinv : ∀ x ∈ B.orthogonal W, yE x ∈ B.orthogonal W :=
    orthogonal_invt hp.out.pos hyEp hyB hWinv
  have hWinv' : ∀ x ∈ W, yL⁻¹ x ∈ W := inv_apply_mem_of_pow_eq_one yL hp.out.pos hyLp hWinv
  have hCinv' : ∀ x ∈ B.orthogonal W, yL⁻¹ x ∈ B.orthogonal W :=
    inv_apply_mem_of_pow_eq_one yL hp.out.pos hyLp hCinv
  have hWC : IsCompl W (B.orthogonal W) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).2 hWd
  have hperp : ∀ d ∈ W, ∀ c ∈ B.orthogonal W, polarBilin Q d c = 0 :=
    fun d hd c hc => LinearMap.BilinForm.mem_orthogonal_iff.1 hc d hd
  let yW := restrictIsoO y W hWinv hWinv'
  let yC := restrictIsoO y (B.orthogonal W) hCinv hCinv'
  have hblock := blockHomO_restrictIsoO hWC hperp y hWinv hWinv' hCinv hCinv'
  have hpow : (yW, yC) ^ p = 1 := by
    apply blockHomO_injective hWC hperp
    rw [map_pow, hblock, hy, map_one]
  have hyWp : yW ^ p = 1 := by simpa using congrArg Prod.fst hpow
  have hyCp : yC ^ p = 1 := by simpa using congrArg Prod.snd hpow
  have hres : ∀ D : Submodule K V, polarBilin (resQ Q D) = B.restrict D := by
    intro D
    ext x y
    exact polarBilin_resQ D x y
  have hWnd : (polarBilin (resQ Q W)).Nondegenerate := by
    rw [hres]
    exact B.nondegenerate_restrict_of_disjoint_orthogonal hrefl hWd
  have hCd : Disjoint (B.orthogonal W)
      (B.orthogonal (B.orthogonal W)) := by
    rw [LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl]
    exact hWd.symm
  have hCnd : (polarBilin (resQ Q (B.orthogonal W))).Nondegenerate := by
    rw [hres]
    exact B.nondegenerate_restrict_of_disjoint_orthogonal hrefl hCd
  have hne : finrank K W / e < p := by
    refine (Nat.div_lt_iff_lt_mul he).2 ?_
    have h5' : (3 + 2) * e = 5 * e := by ring
    have : 5 * e ≤ p * e := Nat.mul_le_mul_right e hp5
    omega
  have hab : ∀ P : Sylow p (TauCeti.QuadraticMap.orthogonalGroup (resQ Q W)),
      IsMulCommutative (P : Subgroup _) := fun P =>
    isMulCommutative_of_isPGroup_equiv hp2' hpK he hpe
      (TauCeti.QuadraticMap.orthogonalGroup (resQ Q W)) hne P.isPGroup'
  have hcomb := pRank_centralizer_add_le (p := p) (blockHomO hWC hperp)
    (blockHomO_injective hWC hperp) yW yC
  rw [hblock] at hcomb
  rcases lt_or_ge (3 * e) (finrank K W) with hgt | hle
  ·
    have hpar : 3 * e + 2 ≤ finrank K W ∨ (Odd (finrank K W) ∧ 3 * e + 1 ≤ finrank K W) := by
      rcases Nat.even_or_odd (finrank K W) with hev | hodd
      · left
        obtain ⟨m, hm⟩ := hev
        obtain ⟨a, ha⟩ := hee
        omega
      · right
        exact ⟨hodd, by omega⟩
    have hrank := le_pRank_orth hp2 hpK he hee hpe1 (resQ Q W) hWnd (k := 3) hpar
    have h3 := le_pRank_centralizer_of_sylow_abelian hab hrank hyWp
    omega
  ·
    have hdimW : finrank K W = 3 * e := by omega
    have hrank2 := le_pRank_orth hp2 hpK he hee hpe1 (resQ Q W) hWnd (k := 2)
      (Or.inl (by omega))
    have h2 := le_pRank_centralizer_of_sylow_abelian hab hrank2 hyWp
    have hdimC := LinearMap.BilinForm.finrank_orthogonal hQ W
    have hCdim : 2 * e ≤ finrank K (B.orthogonal W) := by omega
    have h1 : 1 ≤ CFSG.Open.pRank p (centralizer
        ({yC} : Set (TauCeti.QuadraticMap.orthogonalGroup
          (resQ Q (B.orthogonal W))))) := by
      by_cases hyC1 : yC = 1
      · have htop : centralizer ({yC} : Set (TauCeti.QuadraticMap.orthogonalGroup
            (resQ Q (B.orthogonal W)))) = ⊤ := by
          refine eq_top_iff.2 fun g _ => ?_
          rw [Subgroup.mem_centralizer_singleton_iff, hyC1, mul_one, one_mul]
        rw [htop]
        exact le_pRank_orth hp2 hpK he hee hpe1 (resQ Q (B.orthogonal W)) hCnd
          (k := 1) (Or.inl (by omega))
      · have hord : orderOf yC = p := orderOf_eq_prime hyCp hyC1
        have hmem : yC ∈ centralizer ({yC} : Set (TauCeti.QuadraticMap.orthogonalGroup
            (resQ Q (B.orthogonal W)))) :=
          Subgroup.mem_centralizer_singleton_iff.2 rfl
        rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
        refine one_le_pRank_of_orderOf hp.out.one_lt (g := (⟨yC, hmem⟩ : centralizer
          ({yC} : Set (TauCeti.QuadraticMap.orthogonalGroup
            (resQ Q (B.orthogonal W)))))) ?_
        rw [← Subgroup.orderOf_coe]
        exact hord
    omega

end CFSG.LocalAnalysis.RankFourTheoremC.BCDEven

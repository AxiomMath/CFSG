module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcAut
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcE6Mat
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotLayer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoBalance
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6Three
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc.E6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType
open scoped MatrixGroups

section Subnormal

theorem isSubnormal_inf' {G : Type*} [Group G] {H K : Subgroup G}
    (h : CFSG.Open.IsSubnormal H K) (Z : Subgroup G) :
    CFSG.Open.IsSubnormal (H ⊓ Z) (K ⊓ Z) := by
  induction h with
  | refl H => exact .refl _
  | step hHM hN hMK ih =>
    rename_i H M K
    refine .step (inf_le_inf_right _ hHM) ?_ ih
    rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right _ hHM)]
    intro h n hh hn
    obtain ⟨hhH, hhZ⟩ := hh
    obtain ⟨hnM, hnZ⟩ := hn
    exact ⟨(Subgroup.normal_subgroupOf_iff hHM).1 hN h n hhH hnM,
      Z.mul_mem (Z.mul_mem hnZ hhZ) (Z.inv_mem hnZ)⟩

theorem assembly_isSubnormal {G : Type*} [Group G] {H K : Subgroup G}
    (h : CFSG.Assembly.IsSubnormal H K) : CFSG.Open.IsSubnormal H K := by
  induction h with
  | refl H => exact .refl _
  | step hHM hN _ ih => exact .step hHM hN ih

end Subnormal

section RankTwo

variable {G : Type*} [Group G] {n : ℕ}

theorem ofAdd_smul_zmod3' (a : ZMod 3) (x : Fin n → ZMod 3) :
    Multiplicative.ofAdd (a • x) = Multiplicative.ofAdd x ^ a.val := by
  rw [← ofAdd_nsmul]
  congr 1
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  exact Nat.cast_smul_eq_nsmul (ZMod 3) a.val x

theorem exists_rank_two_subgroup_of_hom (φ : Multiplicative (Fin n → ZMod 3) →* G)
    (hφ : Function.Injective φ) (u v : Fin n → ZMod 3)
    (hind : Function.Injective fun ab : Fin 2 → ZMod 3 => ab 0 • u + ab 1 • v) :
    ∃ U : Subgroup G, U ≤ φ.range ∧ Nat.card U = 9 ∧
      ∀ x : G, x ∈ Subgroup.centralizer (U : Set G) ↔
        (x ∈ Subgroup.centralizer ({φ (Multiplicative.ofAdd u)} : Set G) ∧
          x ∈ Subgroup.centralizer ({φ (Multiplicative.ofAdd v)} : Set G)) := by
  classical
  let lin : (Fin 2 → ZMod 3) →+ (Fin n → ZMod 3) :=
    { toFun := fun ab => ab 0 • u + ab 1 • v
      map_zero' := by simp
      map_add' := fun a b => by simp only [Pi.add_apply, add_smul]; abel }
  let ψ : Multiplicative (Fin 2 → ZMod 3) →* G := φ.comp (AddMonoidHom.toMultiplicative lin)
  set du : G := φ (Multiplicative.ofAdd u) with hdu_def
  set dv : G := φ (Multiplicative.ofAdd v) with hdv_def
  have hψ : ∀ ab : Fin 2 → ZMod 3, ψ (Multiplicative.ofAdd ab) =
      du ^ (ab 0).val * dv ^ (ab 1).val := by
    intro ab
    show φ (Multiplicative.ofAdd (ab 0 • u + ab 1 • v)) = _
    rw [ofAdd_add, map_mul, ofAdd_smul_zmod3', ofAdd_smul_zmod3', map_pow, map_pow]
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h1 := hφ hxy
    have h2 : lin (Multiplicative.toAdd x) = lin (Multiplicative.toAdd y) := h1
    exact hind h2
  have hv1 : (1 : ZMod 3).val = 1 := by decide
  have hduU : du ∈ ψ.range := ⟨Multiplicative.ofAdd (Pi.single 0 1), by
    rw [hψ]; simp [hv1]⟩
  have hdvU : dv ∈ ψ.range := ⟨Multiplicative.ofAdd (Pi.single 1 1), by
    rw [hψ]; simp [hv1]⟩
  refine ⟨ψ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod 3) ≃ _)]
    simp [Nat.card_fun, ZMod.card]
  · intro x
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨h du hduU, h dv hdvU⟩
    · rintro ⟨h1, h2⟩ y ⟨z, rfl⟩
      rw [show ψ z = du ^ (Multiplicative.toAdd z 0).val * dv ^ (Multiplicative.toAdd z 1).val from
        hψ (Multiplicative.toAdd z)]
      have c1 : Commute du x := h1
      have c2 : Commute dv x := h2
      exact Commute.mul_left (c1.pow_left _) (c2.pow_left _)

end RankTwo

section GoodPair

open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6 CFSG.StandardType.TableBExc.E6Three
  CFSG.StandardType.E6ThreeEnd CFSG.RankThree.CentralCover

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem tvMatWord_zmod_two :
    (tvMatWord [(3, 5), (5, 3)] : Matrix (Fin 6) (Fin 6) (ZMod 2)) = Tm := by
  decide +kernel

theorem coe_T_eq_Tm :
    ((tvSLWord [(3, 5), (5, 3)] : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = Tm := by
  rw [coe_tvSLWord]
  have h := map_tvMatWord (ZMod.castHom (dvd_refl 2) K) [(3, 5), (5, 3)]
  rw [← h, tvMatWord_zmod_two, map_Tm]

theorem e6_good_pair (hK : Nat.card K = 2) (h2 : (2 : K) = 0) :
    ∃ U J : Subgroup (adjointGroup .E6 K), U ≤ (torusE6Two h2).range ∧ Nat.card U = 9 ∧
      CFSG.Open.IsSubnormal J (Subgroup.centralizer (U : Set (adjointGroup .E6 K))) ∧
      CFSG.Open.IsQuasisimple ↥J ∧ 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  classical
  have hv1 : (1 : ZMod 3).val = 1 := by decide
  have hu : ∀ i : Fin 4, torusE6Two h2 (Multiplicative.ofAdd (Pi.single i 1)) = uE6Two i :=
    fun i => by rw [torusE6Two_single, zmodPowHom_apply, hv1, pow_one]
  have hind : Function.Injective fun ab : Fin 2 → ZMod 3 =>
      ab 0 • (Pi.single (0 : Fin 4) (1 : ZMod 3)) + ab 1 • (Pi.single (1 : Fin 4) (1 : ZMod 3)) := by
    intro a b hab
    have h0 := congrFun hab 0
    have h1 := congrFun hab 1
    simp at h0 h1
    funext i
    fin_cases i <;> simp [h0, h1]
  obtain ⟨U, hUV, hUcard, hUcent⟩ := exists_rank_two_subgroup_of_hom (torusE6Two h2)
    (torusE6Two_injective h2) _ _ hind
  rw [hu 0, hu 1] at hUcent
  set X := Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K)) with hX
  set Y := Subgroup.centralizer ({uE6Two 1} : Set (adjointGroup .E6 K)) with hY
  obtain ⟨hLle, hLsub, -⟩ := (largeEvenLayer_centralizer_uE6Two_zero hK).2
  have hLsub' : CFSG.Open.IsSubnormal (leviB0 K) X := assembly_isSubnormal hLsub
  set L := leviB0 K with hL
  set T : SL(6, K) := tvSLWord [(3, 5), (5, 3)] with hTdef
  have hT : phi0 K T = uE6Two 1 := phi0_of_conj conj_uE6Two_one
  have hphi0 : Function.Injective (phi0 K) := phi0_injective hK
  set Jm : Subgroup SL(6, K) := (blk (K := K)).range with hJm
  set J : Subgroup (adjointGroup .E6 K) := Jm.map (phi0 K) with hJ
  have hJL : J ≤ L := by
    rw [hL, ← range_phi0]
    exact Subgroup.map_le_range _ _
  have hblkT : ∀ h : SL(4, K), blk h * T = T * blk h := fun h => Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hTdef,
      coe_T_eq_Tm]
    exact blk_commute h)
  have hJY : J ≤ Y := by
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    rw [hY, Subgroup.mem_centralizer_singleton_iff, ← hT, ← map_mul, ← map_mul, hblkT]
  have hJM : J ≤ L ⊓ Y := le_inf hJL hJY
  have hJnorm : (J.subgroupOf (L ⊓ Y)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJM]
    rintro j m ⟨_, ⟨h, rfl⟩, rfl⟩ ⟨hmL, hmY⟩
    obtain ⟨g, rfl⟩ : m ∈ (phi0 K).range := by rw [range_phi0]; exact hmL
    have hgT : g * T = T * g := by
      apply hphi0
      rw [map_mul, map_mul, hT]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hmY)
    have hgm : (g : Matrix (Fin 6) (Fin 6) K) * Tm = Tm * (g : Matrix (Fin 6) (Fin 6) K) := by
      rw [← coe_T_eq_Tm, ← hTdef, ← Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, hgT]
    obtain ⟨h', hh'⟩ := blk_conj_mem hgm h
    refine ⟨blk h', ⟨h', rfl⟩, ?_⟩
    have this : g * blk h * g⁻¹ = blk h' := by rw [hh', mul_inv_cancel_right]
    rw [← this, map_mul, map_mul, map_inv]
  have hUXY : Subgroup.centralizer (U : Set (adjointGroup .E6 K)) = X ⊓ Y := by
    ext x
    rw [Subgroup.mem_inf]
    exact hUcent x
  have hsub : CFSG.Open.IsSubnormal J (X ⊓ Y) :=
    .step hJM hJnorm (isSubnormal_inf' hLsub' Y)
  let eJ : SL(4, K) ≃* ↥J :=
    (MonoidHom.ofInjective (blk_injective (K := K))).trans
      (Subgroup.equivMapOfInjective Jm (phi0 K) hphi0)
  have hq : CFSG.Open.IsQuasisimple SL(4, K) := by
    have h := CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (n := 4) (K := K)
      (by norm_num)
    exact ⟨h.1.commutator_eq_top, h.2.1⟩
  refine ⟨U, J, hUV, hUcard, hUXY ▸ hsub, (CFSG.Open.IsQuasisimple.congr eJ).1 hq, ?_⟩
  rw [← natCard_quotCenter_eq eJ]
  have hZ := center_sl4_eq_bot hK
  have hc : Nat.card (SL(4, K) ⧸ Subgroup.center SL(4, K)) = Nat.card SL(4, K) :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv
  rw [hc]
  exact three_dvd_card_sl4

end GoodPair

section Conclusion

open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6 CFSG.StandardType.TableBExc.E6Three
  CFSG.StandardType.E6ThreeEnd CFSG.RankThree.CentralCover

theorem multiplicative_pow_three {n : ℕ} (a : Multiplicative (Fin n → ZMod 3)) : a ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  have h3 : (3 : ZMod 3) = 0 := by decide
  simp [nsmul_eq_mul, h3]

theorem mem_range_conj_of_equiv_mem {C₀ C₁ : Type*} [Group C₀] [Group C₁] (e : C₀ ≃* C₁)
    (α : MulAut C₀)
    (h : MulAut.congr e α ∈ (MulAut.conj : C₁ →* MulAut C₁).range) :
    α ∈ (MulAut.conj : C₀ →* MulAut C₀).range := by
  obtain ⟨g, hg⟩ := h
  refine ⟨e.symm g, ?_⟩
  ext y
  have h1 : (MulAut.conj g) (e y) = e (α y) := by
    have := congrArg (fun β : MulAut C₁ => β (e y)) hg
    simpa [MulAut.congr_apply] using this
  have h2 : α y = e.symm ((MulAut.conj g) (e y)) := by
    rw [h1]
    simp
  rw [h2]
  simp [MulAut.conj_apply]

theorem isElemAbelian_range_of_exp_three {A G : Type*} [CommGroup A] [Group G] (φ : A →* G)
    (h3 : ∀ a : A, a ^ 3 = 1) : IsElemAbelian 3 φ.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨_, a, rfl⟩ := x
    obtain ⟨_, b, rfl⟩ := y
    apply Subtype.ext
    show φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, h3, map_one]

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem e6_aut_cube_inner (hK : Nat.card K = 2) (β : MulAut (adjointGroup .E6 K))
    (hβ : β ^ 3 = 1) : β ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  by_contra hne
  have hmem : β ∉ e6Inndiag K := by
    rw [e6Inndiag_eq_innerAut_of_not_dvd K (by rw [hK]; norm_num)]
    exact hne
  obtain ⟨σ, -, hdvd, -⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag (ℓ := 2) (f := 1)
    Nat.prime_two le_rfl K (by rw [hK, pow_one]) Nat.prime_three (by norm_num) hβ hmem
  omega

theorem e6_conclusion {C₀ : Type} [Group C₀] [Finite C₀] (hK : Nat.card K = 2)
    (e : C₀ ≃* adjointGroup .E6 K) : X1Concl C₀ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨U, J, hUV, hUcard, hJsub, hJq, hJ3⟩ := e6_good_pair hK h2
  have hVel : IsElemAbelian 3 (torusE6Two h2).range :=
    isElemAbelian_range_of_exp_three (torusE6Two h2) multiplicative_pow_three
  have hVcard : Nat.card (torusE6Two h2).range = 3 ^ 4 := by
    rw [Nat.card_congr (MonoidHom.ofInjective (torusE6Two_injective h2)).toEquiv.symm,
      card_multiplicative_fin_zmod]
  refine exc_final (⊤ : Subgroup (adjointGroup .E6 K)) ⊤ (torusE6Two h2).range U J 4
    (e.trans Subgroup.topEquiv.symm) (fun _ _ _ _ => Subgroup.mem_top _) le_top hVel hVcard ?_
    hUV hUcard (by rwa [top_inf_eq]) hJq hJ3 ?_
    (conj_injective_of_equiv e center_adjointGroup_eq_bot)
  · intro E _ hE hcard
    obtain ⟨c, hc⟩ := E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK hE hcard
    exact ⟨c, Subgroup.mem_top _, hc⟩
  · intro A hA α hα
    have hα3 : α ^ 3 = 1 := hA.2 α hα
    refine mem_range_conj_of_equiv_mem e α (e6_aut_cube_inner hK _ ?_)
    rw [← map_pow, hα3, map_one]

end Conclusion


end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc.E6

end

module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriHolds
public import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsHolds
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Arith
import CFSG.LocalAnalysis.StandardType.GGL45FixA2UniFix
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5SU
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonL2Holds
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriAux

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open scoped commutatorElement

section Tools

variable {X Y : Type} [Group X] [Group Y]

theorem tcent_map_centralizer (ψ : X ≃* Y) (r : X) :
    (Subgroup.centralizer ({r} : Set X)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ r} : Set Y) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨ψ.symm y, ?_, ψ.apply_symm_apply y⟩
    apply ψ.injective
    rw [map_mul, map_mul, ψ.apply_symm_apply, hy]

theorem tcent_isComponentOf_map (ψ : X ≃* Y) {Q C : Subgroup X}
    (h : CFSG.Assembly.IsComponentOf Q C) :
    CFSG.Assembly.IsComponentOf (Q.map ψ.toMonoidHom) (C.map ψ.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map _,
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (Q.equivMapOfInjective _ ψ.injective).symm h.2.2⟩

theorem tcent_component_eq {Q C R : Subgroup X} (hQ : CFSG.Assembly.IsComponentOf Q C)
    (hRC : R ≤ C) (hcomm : ∀ a ∈ C, ∀ b ∈ C, a * b * a⁻¹ * b⁻¹ ∈ R)
    (hR : CFSG.IsQuasisimple ↥R) : Q = R := by
  have hQperf : ⁅Q, Q⁆ = Q := by
    have h1 : (commutator ↥Q).map Q.subtype = ⁅Q, Q⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← h1, hQ.2.2.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hQR : Q ≤ R := by
    rw [← hQperf, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact hcomm a (hQ.1 ha) b (hQ.1 hb)
  have hsub : CFSG.Assembly.IsSubnormal Q R := by
    have h := hQ.2.1.inf R
    rwa [inf_eq_left.2 hQR, inf_eq_right.2 hRC] at h
  have hRo : CFSG.Open.IsQuasisimple ↥R := ⟨hR.1.commutator_eq_top, hR.2.1⟩
  haveI : Group.IsPerfect ↥Q := ⟨hQ.2.2.1⟩
  haveI : Group.IsPerfect ↥(Q.subgroupOf R) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hQR).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQR).symm.surjective
  rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hRo
      (Q.subgroupOf R) (CFSG.Open.IsSubnormal.of_mathlib hsub.subgroupOf) with h | h
  · exact absurd ((Subgroup.subgroupOf_eq_bot.1 h).eq_bot_of_le hQR) (ggComponent_ne_bot hQ)
  · exact le_antisymm hQR (Subgroup.subgroupOf_eq_top.1 h)

private theorem tcent_center_eq {H : Type} [Group H] (N : Subgroup H) [N.Normal]
    (hN : N ≤ Subgroup.center H) (hs : IsSimpleGroup (H ⧸ N))
    (hna : ∃ a b : H ⧸ N, a * b ≠ b * a) : Subgroup.center H = N := by
  refine le_antisymm (fun z hz => ?_) hN
  by_contra hzN
  haveI := hs
  set M : Subgroup (H ⧸ N) := (Subgroup.center H).map (QuotientGroup.mk' N) with hM
  have hMn : M.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  haveI := hMn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hbot | htop
  · apply hzN
    have hz' : QuotientGroup.mk' N z ∈ M := ⟨z, hz, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz'
    exact hz'
  · obtain ⟨a, b, hab⟩ := hna
    apply hab
    have ha : a ∈ M := htop ▸ Subgroup.mem_top a
    obtain ⟨z', hz', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective N b
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz' b')]

theorem tcent_map_center (e : X ≃* Y) :
    (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ Subgroup.center X := hx
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hx' g']
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    show e.symm y ∈ Subgroup.center X
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hy (e g)]

theorem tcent_centerQuot_congr (e : X ≃* Y) :
    Nonempty (X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) :=
  ⟨QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e (tcent_map_center e)⟩

private theorem tcent_quot_equiv {H : Type} [Group H] (e : X ≃* H) (N : Subgroup H) [N.Normal]
    (hZ : Subgroup.center H = N) : Nonempty (X ⧸ Subgroup.center X ≃* H ⧸ N) :=
  ⟨QuotientGroup.congr (Subgroup.center X) N e ((tcent_map_center e).trans hZ)⟩

private theorem tcent_scalars_le_center {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (H : Subgroup (GL ι F)) : (LargeEvenScalars ι F).subgroupOf H ≤ Subgroup.center ↥H := by
  intro h hh
  rw [Subgroup.mem_subgroupOf, largeEvenScalars_def,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hh
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext ((Subgroup.mem_center_iff.mp hh) g)

private theorem tcent_labelOf_of_quot {Γ : Type} [Group Γ] {K : Subgroup Γ} {lab : GLALabel}
    (hperf : commutator ↥K = ⊤) (hlab : LargeEvenInLambda2 lab)
    (h : CFSG.Assembly.LargeEvenRawDatum lab fun R₀ _ _ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* R₀)) :
    LabelOf K lab := by
  refine ⟨hperf, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ h⟩
  rintro R _ I F ⟨hs, hna, ⟨e⟩⟩
  exact ⟨hs, hna, e, rfl⟩

theorem tcent_center_eq_bot_of_simple {R₀ : Type} [Group R₀] (hs : IsSimpleGroup R₀)
    (hna : ∃ a b : R₀, a * b ≠ b * a) : Subgroup.center R₀ = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R₀) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center R₀ := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem tcent_center_bot_of_equiv (e : X ≃* Y) (hY : Subgroup.center Y = ⊥) :
    Subgroup.center X = ⊥ := by
  have h := tcent_map_center e.symm
  rw [hY, Subgroup.map_bot] at h
  exact h.symm

private theorem tcent_commutator_eq_top_of_simple {R₀ : Type} [Group R₀] (hs : IsSimpleGroup R₀)
    (hna : ∃ a b : R₀, a * b ≠ b * a) : commutator R₀ = ⊤ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator R₀) with hbot | htop
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have h1 : ⁅a, b⁆ ∈ commutator R₀ := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hab h1
  · exact htop

private theorem tcent_labelOf_of_equiv {Γ : Type} [Group Γ] {K : Subgroup Γ} {lab : GLALabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : CFSG.Assembly.LargeEvenRawDatum lab fun R₀ _ _ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ Nonempty (↥K ≃* R₀)) :
    Subgroup.center ↥K = ⊥ ∧ LabelOf K lab := by
  obtain ⟨R₀, _, I, F, hs, hna, ⟨e⟩⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists h
  have hZ : Subgroup.center ↥K = ⊥ :=
    tcent_center_bot_of_equiv e (tcent_center_eq_bot_of_simple hs hna)
  haveI : Group.IsPerfect R₀ := ⟨tcent_commutator_eq_top_of_simple hs hna⟩
  have hcomm : commutator ↥K = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective).commutator_eq_top
  refine ⟨hZ, hcomm, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ h⟩
  rintro R _ I' F' ⟨hs', hna', ⟨e'⟩⟩
  exact ⟨hs', hna', (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e'),
    rfl⟩

end Tools

section Holds


private theorem tcent_inner_model {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n) {K₃ : Type} [Field K₃]
    [Finite K₃] (hK : Nat.card K₃ = (2 ^ n) ^ 3) {Fr : K₃ ≃+* K₃} (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {X : Type} [Group X] (ψ : X ≃* graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)
    {r : X} (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) {Q : Subgroup X}
    (hQ : CFSG.Assembly.IsComponentOf Q (Subgroup.centralizer ({r} : Set X))) :
    (CFSG.Assembly.LargeEvenRawDatum ⟨.A, 1, 3 * n⟩ fun R₀ _ _ _ =>
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ Nonempty (↥Q ≃* R₀)) ∨
      (CFSG.Assembly.LargeEvenRawDatum ⟨.twA, 2, n⟩ fun R₀ _ _ _ =>
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
          Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃* R₀)) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hq1 : 2 ^ n % 3 = 2 := by
    obtain ⟨m, rfl⟩ := hn
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hq2 : 2 < 2 ^ n := by omega
  have h3q : ¬ 3 ∣ 2 ^ n := by omega
  have hσ3 : Fr ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hFr c
    simpa [pow_succ] using this
  set z := ψ r with hzdef
  have hz3 : z ^ 3 = 1 := by rw [hzdef, ← map_pow, hr3, map_one]
  have hz1 : z ≠ 1 := fun h => hr1 (ψ.injective (h.trans (map_one ψ).symm))
  obtain ⟨g, hg | hg⟩ :=
    Sec11.KS11Lie6Proof.d4ThreeConj_holds K₃ (2 ^ n) Fr hK hFr h3q z hz3 hz1
  ·
    right
    have hy3 : (g * z * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3, mul_one, mul_inv_cancel]
    have hy1 : g * z * g⁻¹ ≠ 1 := by
      intro h1
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨c, R, -, hRc, hcomm, hRq, U, hU, eRU, -⟩ :=
      Sec21.Item219LieProof.d4_threeA_model_unitary Nat.prime_two hn1 (by norm_num) hq1 hq2 hK hFr
        hg hy3 hy1
    set ψ' : X ≃* graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom :=
      ψ.trans (MulAut.conj (c * g)) with hψ'def
    have hψ' : ψ' r = c * (g * z * g⁻¹) * c⁻¹ := by
      rw [hψ'def, MulEquiv.trans_apply, MulAut.conj_apply, ← hzdef]
      group
    have hQm := tcent_isComponentOf_map ψ' hQ
    rw [tcent_map_centralizer, hψ'] at hQm
    have hQR := tcent_component_eq hQm hRc hcomm hRq
    haveI : CharP K₃ 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (k := n * 3) (by omega) (by rw [hK, pow_mul])
    haveI : CharP (AlgebraicClosure K₃) 2 :=
      charP_of_injective_algebraMap (algebraMap K₃ (AlgebraicClosure K₃)).injective 2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨F, _, _, hF, ⟨ε⟩⟩ := CFSG.OddStandard.GH71.S55.nonempty_statedSU_mulEquiv
      (Ω := AlgebraicClosure K₃) (ℓ := 2) (f := n) hn1 hU
    let isoQ : ↥Q ≃* ↥(LargeEvenSUGroup (Fin 3) F (2 ^ n)) :=
      (Q.equivMapOfInjective ψ'.toMonoidHom ψ'.injective).trans
        ((MulEquiv.subgroupCongr hQR).trans (eRU.trans ε.symm))
    obtain ⟨hs, hnab⟩ := gffa2_unitary_simple_nonab (by omega : 2 ≤ n) hF
    have hZ : Subgroup.center ↥(LargeEvenSUGroup (Fin 3) F (2 ^ n)) =
        (LargeEvenScalars (Fin 3) F).subgroupOf (LargeEvenSUGroup (Fin 3) F (2 ^ n)) :=
      tcent_center_eq _ (tcent_scalars_le_center _) hs hnab
    dsimp only [CFSG.Assembly.LargeEvenRawDatum]
    exact ⟨F, inferInstance, inferInstance, hF, hs, hnab, tcent_quot_equiv isoQ _ hZ⟩
  ·
    left
    have hy3 : (g * z * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3, mul_one, mul_inv_cancel]
    have hy1 : g * z * g⁻¹ ≠ 1 := by
      intro h1
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨hcomm, -⟩ :=
      Sec11.KS11Lie6Proof.d4ThreeBCent_holds K₃ (2 ^ n) Fr hK hFr h3q (g * z * g⁻¹) hg hy3 hy1
    have hSC : (Sec11.KS11Lie4Proof.d4ShortSL2 K₃ Fr.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) ≤
          Subgroup.centralizer ({g * z * g⁻¹} : Set _) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hg s hs
    set ψ' : X ≃* graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom :=
      ψ.trans (MulAut.conj g) with hψ'def
    have hψ' : ψ' r = g * z * g⁻¹ := by
      rw [hψ'def, MulEquiv.trans_apply, MulAut.conj_apply, ← hzdef]
    have hQm := tcent_isComponentOf_map ψ' hQ
    rw [tcent_map_centralizer, hψ'] at hQm
    have hK4 : 4 ≤ Nat.card K₃ := by
      rw [hK]
      calc 4 ≤ 2 ^ n := by omega
        _ ≤ (2 ^ n) ^ 3 := Nat.le_self_pow (by norm_num) _
    have hSq := Sec11.KS11Lie4Proof.isQuasisimple_d4ShortSL2 hσ3 hK4
    have hQS := tcent_component_eq hQm hSC hcomm hSq
    obtain ⟨eS⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 hσ3
    set F : Subfield K₃ := orbitField TwistTag.D4 K₃ Fr.toRingHom Sec11.KS11Lie4Proof.d4Outer
      with hFdef
    haveI : Finite ↥F := Subtype.finite
    have hFcard : Nat.card ↥F = 2 ^ (3 * n) := by
      rw [hFdef, Sec11.KS11Lie4Proof.natCard_orbitField_d4Outer hσ3, hK, ← pow_mul, mul_comm]
    haveI : CharP ↥F 2 := charP_two_of_card hFcard
    have hF4 : 4 ≤ Nat.card ↥F := by
      rw [hFcard]
      calc 4 ≤ 2 ^ n := by omega
        _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨hs, hnab⟩ := ggL48TBVac_simple_linear_two hF4
    let isoQ : ↥Q ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) ↥F) :=
      (Q.equivMapOfInjective ψ'.toMonoidHom ψ'.injective).trans
        ((MulEquiv.subgroupCongr hQS).trans (eS.symm.trans (projEquiv ↥F).symm))
    dsimp only [CFSG.Assembly.LargeEvenRawDatum]
    exact ⟨↥F, inferInstance, inferInstance, hFcard, hs, hnab, ⟨isoQ⟩⟩

theorem triD4Cent3_holds : TriD4Cent3 := by
  intro Γ _ _ J K b lab hlab htag hodd hn3 hZ hbN hb3 hbC hKc
  obtain ⟨K₃, _, _, hn1, hK₃, hs, hna, ⟨θ⟩⟩ := triD4_datum hlab htag
  have hKc' : CFSG.Assembly.IsComponentOf K (J ⊓ Subgroup.centralizer ({b} : Set Γ)) :=
    CFSG.Assembly.isComponentOf_iff_open.2 hKc
  obtain ⟨Q, eKQ, hQ⟩ := exists_component_fixed_of_centerless θ hZ hbN hKc'
  set σ := ggLAut J θ ⟨b, hbN⟩ with hσdef
  have hσ3 : σ ^ 3 = 1 := ggLAut_pow_eq_one_of_pow J θ hbN hb3
  have hperfK : commutator ↥K = ⊤ := hKc.2.2.1
  set e := ggCenterlessEquiv θ hZ with he
  have hσe : ∀ j (hj : j ∈ J), σ (e ⟨j, hj⟩) = e (J.normalizerMonoidHom ⟨b, hbN⟩ ⟨j, hj⟩) := by
    intro j hj
    rw [he, ggCenterlessEquiv_apply, ggCenterlessEquiv_apply]
    exact ggLAut_apply J θ ⟨b, hbN⟩ ⟨j, hj⟩
  by_cases hin : InnerOn J b
  ·
    right
    refine ⟨hin, ?_⟩
    obtain ⟨a, haJ, haact⟩ := hin
    set r : GGTriD4R lab.n K₃ := e ⟨a, haJ⟩ with hrdef
    have hσr : σ = MulAut.conj r := by
      ext y
      obtain ⟨⟨j, hj⟩, rfl⟩ := e.surjective y
      rw [MulAut.conj_apply, hσe j hj, hrdef, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [CFSG.StandardType.normalizerMonoidHom_coe]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact haact j hj
    have hfix : ggAutFixedSubgroup σ = Subgroup.centralizer ({r} : Set (GGTriD4R lab.n K₃)) := by
      ext y
      rw [mem_ggAutFixedSubgroup, hσr, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        calc y * r = r * y * r⁻¹ * r := by rw [h]
          _ = r * y := by group
      · intro h
        rw [← h]
        group
    rw [hfix] at hQ
    have ha3 : a ^ 3 = 1 := pow_eq_one_of_act hZ haJ haact hb3
    have hr3 : r ^ 3 = 1 := by
      rw [hrdef, ← map_pow]
      have : (⟨a, haJ⟩ : ↥J) ^ 3 = 1 := Subtype.ext (by simp [ha3])
      rw [this, map_one]
    have hr1 : r ≠ 1 := by
      intro h1
      have ha1 : (⟨a, haJ⟩ : ↥J) = 1 := e.injective (h1.trans (map_one e).symm)
      have ha1' : a = 1 := congrArg Subtype.val ha1
      apply hbC
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have h2 := haact j hj
      rw [ha1'] at h2
      simp only [inv_one, mul_one, one_mul] at h2
      calc j * b = b * j * b⁻¹ * b := by rw [h2]
        _ = b * j := by group
    haveI : CharP K₃ 2 := charP_two_of_card (m := lab.n * 3) (by rw [hK₃, pow_mul])
    set σ₀ := iterateFrobeniusEquiv K₃ 2 lab.n with hσ₀def
    have hσ₀ : ∀ c, σ₀ c = c ^ 2 ^ lab.n := fun c => by
      rw [hσ₀def, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
    obtain ⟨e₀⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn1 K₃ hK₃ σ₀ hσ₀
    rcases tcent_inner_model hodd hn3 hK₃ hσ₀ e₀ hr3 hr1 hQ with hA | hU
    · left
      have hd : CFSG.Assembly.LargeEvenRawDatum ⟨.A, 1, 3 * lab.n⟩ fun R₀ _ _ _ =>
          IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ Nonempty (↥K ≃* R₀) :=
        CFSG.StandardType.Canonical.largeEvenRawDatum_mono
          (fun R₀ _ _ _ ⟨h1, h2, ⟨e'⟩⟩ => ⟨h1, h2, ⟨eKQ.trans e'⟩⟩) hA
      have hΛ : LargeEvenInLambda2 ⟨.A, 1, 3 * lab.n⟩ :=
        ⟨show 1 ≤ 3 * lab.n by omega, by norm_num, fun _ => show 2 ≤ 3 * lab.n by omega⟩
      exact (tcent_labelOf_of_equiv hΛ hd).2
    · right
      obtain ⟨eZ⟩ := tcent_centerQuot_congr eKQ
      have hd : CFSG.Assembly.LargeEvenRawDatum ⟨.twA, 2, lab.n⟩ fun R₀ _ _ _ =>
          IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
            Nonempty (↥K ⧸ Subgroup.center ↥K ≃* R₀) :=
        CFSG.StandardType.Canonical.largeEvenRawDatum_mono
          (fun R₀ _ _ _ ⟨h1, h2, ⟨e'⟩⟩ => ⟨h1, h2, ⟨eZ.trans e'⟩⟩) hU
      exact tcent_labelOf_of_quot hperfK (gffa2_label_unitary hodd hn3).1 hd
  ·
    left
    refine ⟨hin, ?_⟩
    have hσout : σ ∉ (MulAut.conj : GGTriD4R lab.n K₃ →* MulAut (GGTriD4R lab.n K₃)).range := by
      rintro ⟨r, hr⟩
      apply hin
      refine ⟨((e.symm r : ↥J) : Γ), (e.symm r).2, fun j hj => ?_⟩
      have h1 := hσe j hj
      rw [← hr, MulAut.conj_apply] at h1
      have h2 : e (J.normalizerMonoidHom ⟨b, hbN⟩ ⟨j, hj⟩) =
          e (e.symm r * ⟨j, hj⟩ * (e.symm r)⁻¹) := by
        rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      have h3 := congrArg Subtype.val (e.injective h2)
      rw [CFSG.StandardType.normalizerMonoidHom_coe] at h3
      simpa using h3
    have hn2 : 2 ≤ lab.n := by omega
    rcases ggTriD4_fixedShape hn1 K₃ hK₃ σ hσ3 hσout with
      ⟨k, _, _, hk, ⟨E⟩⟩ | ⟨hev, -⟩ | ⟨-, F, _, _, hF, ⟨E⟩⟩
    ·
      left
      have hk3 : 3 ≤ Nat.card k := by
        rw [hk]
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn2
      have hperf := ExcCopy.isPerfect_adjointGroup Tag.G2 k fun _ => hk3
      obtain ⟨hsG, -⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect Tag.G2 k hperf
      let T : ↥⁅ggAutFixedSubgroup σ, ggAutFixedSubgroup σ⁆ ≃* ↥(adjointGroup Tag.G2 k) :=
        (ggCommutatorEquiv _).trans
          ((ggCommutatorCongr E).trans
            ((MulEquiv.subgroupCongr hperf.commutator_eq_top).trans Subgroup.topEquiv))
      obtain ⟨Qe⟩ := gffa2_component_equiv T hsG hQ
      have hΛ : LargeEvenInLambda2 ⟨.G2, 0, lab.n⟩ := ⟨hn1, rfl, hn2⟩
      have hd : CFSG.Assembly.LargeEvenRawDatum ⟨.G2, 0, lab.n⟩ fun R₀ _ _ _ =>
          IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ Nonempty (↥K ≃* R₀) :=
        CFSG.Assembly.largeEvenRawDatumLegacy_to_canonical_carrier
          (ggG2_rawDatum hn2 hk (eKQ.trans Qe))
      exact (tcent_labelOf_of_equiv hΛ hd).2
    · exact absurd hodd (Nat.not_odd_iff_even.2 hev)
    ·
      right
      obtain ⟨E'⟩ := gffa2_commutator_equiv E
      obtain ⟨T₀⟩ := ggTriD4_pgu_derived_equiv hn2 hF
      obtain ⟨hsU, hnabU⟩ := gffa2_unitary_simple_nonab hn2 hF
      obtain ⟨Qe⟩ := gffa2_component_equiv (E'.trans T₀) hsU hQ
      have hd : CFSG.Assembly.LargeEvenRawDatum ⟨.twA, 2, lab.n⟩ fun R₀ _ _ _ =>
          IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ Nonempty (↥K ≃* R₀) := by
        dsimp only [CFSG.Assembly.LargeEvenRawDatum]
        exact ⟨F, inferInstance, inferInstance, hF, hsU, hnabU, ⟨eKQ.trans Qe⟩⟩
      obtain ⟨hZK, hM⟩ := tcent_labelOf_of_equiv (gffa2_label_unitary hodd hn3).1 hd
      exact ⟨hM, hZK⟩

end Holds

end CFSG.LocalAnalysis.GLTheoremA

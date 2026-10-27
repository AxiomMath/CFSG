module

public import CFSG.LieType.SeitzGeneration.ExcHigh.Classes
public import CFSG.LieType.SeitzGeneration.ExcHigh.Generic
public import CFSG.HardMathSupport.Lang.AnisoF4.B4Even
public import CFSG.HardMathSupport.Lang.AnisoF4.Closing
public import CFSG.LieType.SeitzGeneration.OrthManyMaster
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwModel
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.HardMathSupport.Lang.AnisoF4.B4Planes

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open scoped MatrixGroups
open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits
  CFSG.ComponentClassification.CatLeafProof CFSG.TauCetiBridge TauCeti CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.HardMathSupport.Lang.AnisoF4

@[expose] def f4Frame : Fin 4 → (Fin (Tag.rank .F4) → ℤ) :=
  ![![0, 1, 2, 2], ![2, 3, 4, 2], ![0, 1, 0, 0], ![0, 1, 2, 0]]

section Roots


theorem f4Frame_facts : ∀ i j : Fin 4, i ≠ j → f4Frame i ≠ f4Frame j ∧ f4Frame i ≠ -f4Frame j ∧
    iform (f4Frame i) (f4Frame j) = 0 ∧ ¬ IsRoot .F4 (f4Frame i + f4Frame j) ∧
      ¬ IsRoot .F4 (f4Frame i + -f4Frame j) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)]
  decide +kernel

theorem f4Frame_isRoot : ∀ i, IsRoot .F4 (f4Frame i) := by
  intro i
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)]
  revert i
  decide +kernel

end Roots

@[expose] def f4FrameSwap (i : Fin 4) : Fin 4 := if i = 0 then 3 else if i = 3 then 0 else i

theorem f4FrameSwap_swap (i : Fin 4) : f4FrameSwap (f4FrameSwap i) = i := by
  revert i
  decide

theorem reflect_three_f4Frame : ∀ i : Fin 4, reflect .F4 (f4Node 3) (f4Frame i) =
    f4Frame (f4FrameSwap i) := by decide

section Native


@[expose] noncomputable def f4FrameGroup (K : Type) [Field K] : Subgroup (adjointGroup .F4 K) :=
  ⨆ i, rootPairF4 K (f4Frame i)

section Frame

variable {K : Type} [Field K]

theorem f4FrameGroup_le_b4 : f4FrameGroup K ≤ ⨆ k, b4Chain K k := by
  set X : Subgroup (adjointGroup .F4 K) := ⨆ k, b4Chain K k with hX
  have hb : ∀ k, b4Chain K k ≤ X := fun k => le_iSup (b4Chain K) k
  have hn0 : Chevalley.weylElement .F4 K (f4Node 0) ∈ X :=
    hb 1 (Steinberg.Adjoint.weylElement_mem_rankOne (F := rootOperatorFamily .F4) (f4Node 0))
  have hn1 : Chevalley.weylElement .F4 K (f4Node 1) ∈ X :=
    hb 2 (Steinberg.Adjoint.weylElement_mem_rankOne (F := rootOperatorFamily .F4) (f4Node 1))
  have hn2 : Chevalley.weylElement .F4 K (f4Node 2) ∈ X :=
    hb 3 (Steinberg.Adjoint.weylElement_mem_rankOne (F := rootOperatorFamily .F4) (f4Node 2))
  have hβ0 : rootPairF4 K b4Root ≤ X := hb 0
  have hα1 : rootPairF4 K (Pi.single (f4Node 1) 1) ≤ X := hb 2
  refine iSup_le fun i => ?_
  fin_cases i
  · exact hβ0
  ·
    have e : f4Frame 1 = reflect .F4 (f4Node 0) (reflect .F4 (f4Node 1) (reflect .F4 (f4Node 2)
        (reflect .F4 (f4Node 1) (reflect .F4 (f4Node 0) b4Root)))) := by decide
    have r0 := isRoot_b4Root
    have s1 := rootPairF4_reflect_le (f4Node 0) hn0 r0 hβ0
    have s2 := rootPairF4_reflect_le (f4Node 1) hn1 (IsRoot.reflect _ r0) s1
    have s3 := rootPairF4_reflect_le (f4Node 2) hn2 (IsRoot.reflect _ (IsRoot.reflect _ r0)) s2
    have s4 := rootPairF4_reflect_le (f4Node 1) hn1
      (IsRoot.reflect _ (IsRoot.reflect _ (IsRoot.reflect _ r0))) s3
    have s5 := rootPairF4_reflect_le (f4Node 0) hn0
      (IsRoot.reflect _ (IsRoot.reflect _ (IsRoot.reflect _ (IsRoot.reflect _ r0)))) s4
    rw [← e] at s5
    exact s5
  · have e2 : f4Frame 2 = Pi.single (f4Node 1) 1 := by decide
    show rootPairF4 K (f4Frame 2) ≤ X
    rw [e2]
    exact hα1
  ·
    have e : f4Frame 3 = reflect .F4 (f4Node 2) (Pi.single (f4Node 1) 1) := by decide
    have s1 := rootPairF4_reflect_le (f4Node 2) hn2 (isRoot_single _ _) hα1
    rw [← e] at s1
    exact s1

theorem f4FrameGroup_le_conj_b4 : f4FrameGroup K ≤
    (⨆ k, b4Chain K k).map (MulAut.conj (Chevalley.weylElement .F4 K (f4Node 3))).toMonoidHom := by
  set X : Subgroup (adjointGroup .F4 K) := ⨆ k, b4Chain K k with hX
  have hP : f4FrameGroup K ≤ X := f4FrameGroup_le_b4
  refine iSup_le fun i => ?_
  have e : f4Frame i = reflect .F4 (f4Node 3) (f4Frame (f4FrameSwap i)) := by
    rw [reflect_three_f4Frame, f4FrameSwap_swap]
  calc rootPairF4 K (f4Frame i) =
        rootPairF4 K (reflect .F4 (f4Node 3) (f4Frame (f4FrameSwap i))) := by
        rw [← e]
    _ = (rootPairF4 K (f4Frame (f4FrameSwap i))).map
          (MulAut.conj (Chevalley.weylElement .F4 K (f4Node 3))).toMonoidHom :=
        (map_conj_weylElement_rootPair_F4 (f4Node 3) (f4Frame_isRoot _)).symm
    _ ≤ X.map (MulAut.conj (Chevalley.weylElement .F4 K (f4Node 3))).toMonoidHom :=
        Subgroup.map_mono ((le_iSup (fun j => rootPairF4 K (f4Frame j)) (f4FrameSwap i)).trans hP)

theorem eq_top_of_b4Chain_le_of_conj_le (M : Subgroup (adjointGroup .F4 K))
    (hX : ⨆ k, b4Chain K k ≤ M)
    (hn : (⨆ k, b4Chain K k).map
      (MulAut.conj (Chevalley.weylElement .F4 K (f4Node 3))).toMonoidHom ≤ M) : M = ⊤ := by
  have hb : ∀ k, b4Chain K k ≤ M := fun k => (le_iSup (b4Chain K) k).trans hX
  have hr0 : rankOne (f4Datum K).rootGroup (f4Node 0) ≤ M := hb 1
  have hr1 : rankOne (f4Datum K).rootGroup (f4Node 1) ≤ M := hb 2
  have hr2 : rankOne (f4Datum K).rootGroup (f4Node 2) ≤ M := hb 3
  have hn2 : Chevalley.weylElement .F4 K (f4Node 2) ∈ M :=
    hr2 (Steinberg.Adjoint.weylElement_mem_rankOne (F := rootOperatorFamily .F4) (f4Node 2))
  have h23 : rootPairF4 K (reflect .F4 (f4Node 3) (Pi.single (f4Node 2) 1)) ≤ M := by
    rw [rootPairF4, ← map_conj_weylElement_rootPair_F4 (f4Node 3) (isRoot_single _ _)]
    exact (Subgroup.map_mono (le_iSup (b4Chain K) 3)).trans hn
  have h3 : rootPairF4 K (Pi.single (f4Node 3) 1) ≤ M := by
    have := rootPairF4_reflect_le (f4Node 2) hn2 (IsRoot.reflect _ (isRoot_single _ _)) h23
    have e : reflect .F4 (f4Node 2) (reflect .F4 (f4Node 3) (Pi.single (f4Node 2) 1)) =
        Pi.single (f4Node 3) 1 := by decide
    rwa [e] at this
  have hall : ⨆ i, rankOne (f4Datum K).rootGroup i ≤ M := by
    refine iSup_le fun i => ?_
    fin_cases i
    · exact hr0
    · exact hr1
    · exact hr2
    · exact h3
  rw [CFSG.ClassicalInvolution.RouteD.iSup_rankOne_eq_top (f4_isCTGroupDatum K)] at hall
  exact eq_top_iff.2 hall

end Frame

section ClassicalB4

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut

theorem iSup_b4Chain_le_closure_centralizers_two {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .F4 K)) (hE : E ≤ ⨆ k, b4Chain K k) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hEc : Nat.card E = p ^ 2) :
    ⨆ k, b4Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hℓ2 : ringChar K ≠ 2 := by
    intro h
    apply h2
    have : CharP K 2 := h ▸ ringChar.charP K
    exact CharTwo.two_eq_zero
  obtain ⟨Ψ, hΨker, hΨrange, -, -⟩ := exists_psi_B4_F4_frame hℓ hℓ2 hK h2
  have hn3 : 3 ≤ 4 := by norm_num
  have : Nonempty (Fin 4 ⊕ Fin 4 ⊕ Unit) := ⟨Sum.inr (Sum.inr ())⟩
  have : Finite (spinGroup (quadOdd 4 K)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadOdd (n := 4) h2 hn3
  set π := spinToStatedProj (quadOdd 4 K) (range_spinMatrix_quadOdd h2 hn3) with hπdef
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadOdd 4 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadOdd 4 K) (range_spinMatrix_quadOdd h2 hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadOdd_iff h2 x).mp hx)) hp2 hpq1
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    intro hd
    apply hcen
    have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadOdd 4 K))) := by
      rw [hZ]
    exact hd.trans this
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := by
    intro hd
    apply hcen
    exact hd.trans (Subgroup.card_dvd_of_le hΨker)
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadOdd 4 K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadOdd h2 hn3).commutator_eq_top
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hEpg : IsPGroup p E := IsPGroup.of_card hEc
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ Ψ.range := hΨrange ▸ hE
  set Ψ' : spinGroup (quadOdd 4 K) →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← card_map_eq_of_disjoint_ker Ψ' hdisE', hmapE', hcardE1]
  set Ebar : Subgroup _ := E'.map π with hEbar
  have hEbarea : IsElemAbelian p Ebar :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE'ea π
  have hcardEbar : Nat.card Ebar = p ^ 2 := by
    rw [hEbar, card_map_eq_of_disjoint_ker π (disjoint_ker_of_exponent π hπcop hE'ea.2), hcardE']
  have hmodel := orthogonalOddPlanes 4 p K (by norm_num) hp hp5 hpK h2 Ebar hEbarea hcardEbar
  have hG := closure_centralizers_of_quotient π hπsurj hZ.le hπcop hperf E' hE'ea.2 hmodel
  have hdisΨ : Disjoint E' Ψ.ker := hΨ'ker ▸ hdisE'
  rw [← hΨrange, MonoidHom.range_eq_map, ← hG, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨g, ⟨x, hx, hx1, hg⟩, rfl⟩
  refine ⟨Ψ x, ?_, ?_, ?_⟩
  · have : Ψ' x ∈ E1 := hmapE' ▸ ⟨x, hx, rfl⟩
    exact this
  · intro h1
    exact hx1 (Subgroup.disjoint_def.mp hdisΨ hx (MonoidHom.mem_ker.mpr h1))
  · show Ψ g * Ψ x = Ψ x * Ψ g
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ hg

theorem iSup_b4Chain_le_closure_centralizers_of_sp_two {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (Ψ : StatedSp 4 K →* adjointGroup .F4 K) (hker : Ψ.ker ≤ Subgroup.center (StatedSp 4 K))
    (hrange : Ψ.range = ⨆ k, b4Chain K k)
    (E : Subgroup (adjointGroup .F4 K)) (hE : E ≤ ⨆ k, b4Chain K k) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hEc : Nat.card E = p ^ 2) :
    ⨆ k, b4Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : Finite (StatedSp 4 K) := inferInstance
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (StatedSp 4 K)) := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      show (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedSp 4 K) =
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 4 K from rfl,
      CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd K (by norm_num)]
    intro hd
    have h2 := (Nat.dvd_prime Nat.prime_two).1 (hd.trans (Nat.gcd_dvd_left 2 _))
    omega
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := fun hd => hcen (hd.trans (Subgroup.card_dvd_of_le hker))
  have hpℓ : p ≠ ringChar K := by
    intro h
    have hd : p ∣ Nat.card K := by rw [hK, ← h]; exact dvd_pow_self p (n.ne_zero)
    have : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ Ψ.range := hrange ▸ hE
  set Ψ' : StatedSp 4 K →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 2 := by
    rw [hE1def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv, hEc]
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← hcardE1, ← hmapE', card_map_eq_of_disjoint_ker Ψ' hdisE']
  have : CFSG.IsElementaryAbelian p E' :=
    { toIsMulCommutative := hE'ea.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hE'ea.2 x x.2) }
  have htop := CFSG.RankThree.PartOne.CTP.closure_centralizers_spPlane
    (⟨hℓ, n.pos, hK, hp, by omega, hpℓ, by norm_num, by omega, this, hcardE'⟩ :
      CFSG.RankThree.PartOne.KCSpFull.SpPlaneSetup (ringChar K) n p 4 K E')
  intro g hg
  rw [← hrange] at hg
  obtain ⟨h, rfl⟩ := hg
  have hh : h ∈ Subgroup.closure {g : StatedSp 4 K | ∃ x ∈ E', x ≠ 1 ∧ g * x = x * g} := by
    rw [htop]
    exact Subgroup.mem_top _
  have hmap : (Subgroup.closure {g : StatedSp 4 K | ∃ x ∈ E', x ≠ 1 ∧ g * x = x * g}).map Ψ ≤
      Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨k, ⟨x, hx, hx1, hkx⟩, rfl⟩
    have hxE : Ψ x ∈ E := by
      have h1 : Ψ' x ∈ E1 := hmapE' ▸ ⟨x, hx, rfl⟩
      exact h1
    have hx1' : Ψ x ≠ 1 := by
      intro h1
      apply hx1
      refine Subgroup.disjoint_def.mp hdisE' hx ?_
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1
    refine Subgroup.subset_closure ⟨Ψ x, hxE, hx1', ?_⟩
    change Ψ k * Ψ x = Ψ x * Ψ k
    rw [← map_mul, ← map_mul, hkx]
  exact hmap ⟨h, hh, rfl⟩

end ClassicalB4

section SylowFrame

variable {K : Type} [Field K]

theorem exists_sl2_hom_rootPairF4 {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    ∃ ρ : SL(2, K) →* adjointGroup .F4 K, Function.Injective ρ ∧ ρ.range = rootPairF4 K γ := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  choose ρF hρFi hρFr _ using exists_rankOne_param hE
  induction hγ with
  | basis j => exact ⟨ρF j, hρFi j, hρFr j⟩
  | reflect i hv ih =>
    obtain ⟨ρ, hρi, hρr⟩ := ih
    refine ⟨(MulAut.conj (Chevalley.weylElement .F4 K i)).toMonoidHom.comp ρ,
      (MulAut.conj _).injective.comp hρi, ?_⟩
    rw [MonoidHom.range_comp, hρr, rootPairF4, map_conj_weylElement_rootPair_F4 i hv]

theorem f4Frame_hom : ∃ ρ : Fin 4 → SL(2, K) →* adjointGroup .F4 K,
    (∀ i, Function.Injective (ρ i)) ∧ (∀ i, (ρ i).range = rootPairF4 K (f4Frame i)) ∧
      ∀ i j, i ≠ j → ∀ x y, Commute (ρ i x) (ρ j y) := by
  choose ρ hρi hρr using fun i => exists_sl2_hom_rootPairF4 (K := K) (f4Frame_isRoot i)
  refine ⟨ρ, hρi, hρr, fun i j hij x y => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := f4Frame_facts i j hij
  have hc := commutes_rootPair_F4 (K := K) (f4Frame_isRoot i) (f4Frame_isRoot j) h1 h2 h3 h4 h5
  have hx : ρ i x ∈ rootPairF4 K (f4Frame i) := by
    rw [← hρr i]
    exact ⟨x, rfl⟩
  have hy : ρ j y ∈ rootPairF4 K (f4Frame j) := by
    rw [← hρr j]
    exact ⟨y, rfl⟩
  exact hc _ hx _ hy

section Card

variable [Finite K]

theorem factorization_card_F4_of_dvd_add_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    (Nat.card (adjointGroup .F4 K)).factorization p = 4 * (Nat.card K + 1).factorization p := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.factorization_ordF4_of_dvd_add_one hp hp5
    (Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.2 inferInstance)) hpq

end Card

end SylowFrame

@[expose] def F4TwoSylow : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 5 ≤ p → p ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
      ∃ g : adjointGroup .F4 K, E₀.map (MulAut.conj g).toMonoidHom ≤ f4FrameGroup K

@[expose] def F4TwoB4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 5 ≤ p → p ∣ Nat.card K + 1 →
    ∀ E : Subgroup (adjointGroup .F4 K), E ≤ ⨆ k, b4Chain K k → (∀ x ∈ E, x ^ p = 1) →
      Nat.card E = p ^ 2 →
        ⨆ k, b4Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x}

@[expose] def F4TwoNative : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 5 ≤ p → p ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
      Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤

theorem f4TwoNative_of_interfaces (h1 : F4TwoSylow) (h2 : F4TwoB4) : F4TwoNative := by
  intro K _ _ p hpF hp5 hpq E₀ hE₀p hE₀c
  obtain ⟨g, hg⟩ := h1 K p hp5 hpq E₀ hE₀p hE₀c
  exact closure_centralizers_eq_top_of_two_conj (p := p) (⨆ k, b4Chain K k) (f4FrameGroup K)
    (Chevalley.weylElement .F4 K (f4Node 3)) f4FrameGroup_le_b4 f4FrameGroup_le_conj_b4
    (fun M hX hn => eq_top_of_b4Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => h2 K p hp5 hpq E hE hEp hEc) E₀ hE₀p hE₀c ⟨g, hg⟩

theorem f4TwoSylow : F4TwoSylow := by
  intro K _ _ p hpF hp5 hpq E₀ hE₀p hE₀c
  obtain ⟨ρ, hρi, hρr, hρc⟩ := f4Frame_hom (K := K)
  have hcomm : Pairwise fun i j => ∀ x y : SL(2, K), Commute (ρ i x) (ρ j y) := by
    intro i j hij x y
    exact hρc i j hij x y
  obtain ⟨Q, -, hQ⟩ := exists_conj_le_frame_sylow ρ hρi hcomm hp5 hpq
    (by rw [factorization_card_F4_of_dvd_add_one hpF.out hp5 hpq])
  obtain ⟨g, hg⟩ := hQ E₀ hE₀p
  refine ⟨g, hg.trans ((map_noncommPiCoprod_le ρ hcomm Q).trans ?_)⟩
  simp only [f4FrameGroup, hρr]
  exact le_rfl

theorem f4TwoB4 : F4TwoB4 := by
  intro K _ _ p hpF hp5 hpq E hE hEp hEc
  classical
  by_cases h2 : (2 : K) = 0
  · have : Fintype K := Fintype.ofFinite K
    have hc : ringChar K = 2 := by
      have hd : ringChar K ∣ 2 := ringChar.dvd (by exact_mod_cast h2)
      obtain ⟨n, hℓ, -⟩ := FiniteField.card K (ringChar K)
      exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hd
    have : CharP K 2 := ringChar.of_eq hc
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
    have hK4 : 4 ≤ Nat.card K := by
      have := Nat.le_of_dvd (by omega) hpq
      omega
    obtain ⟨Ψ, hker, hrange, -, -⟩ := exists_psi_B4_F4_frame_even hK hK4
    exact iSup_b4Chain_le_closure_centralizers_of_sp_two hpF.out hp5 hpq Ψ hker hrange E hE hEp hEc
  · exact iSup_b4Chain_le_closure_centralizers_two h2 hpF.out hp5 hpq E hE hEp hEc

theorem f4TwoNative : F4TwoNative := f4TwoNative_of_interfaces f4TwoSylow f4TwoB4

end Native

section Glue


theorem seitzExcHighF4Two_of_native (h : F4TwoNative) : SeitzExcHighF4Two := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hp5, q, hdq, -, hord⟩, -, -⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, hchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have : Fact p.Prime := ⟨hp⟩
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hKq]
    exact dvd_add_one_of_orderOf_eq_two hp hord
  exact CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.planeGen_of_native_closure e
    center_adjointGroup_eq_bot (fun E₀ hE₀p hE₀c => h K p hp5 hpq E₀ hE₀p hE₀c) hE hcard hin

theorem seitzExcHighF4Two : SeitzExcHighF4Two := seitzExcHighF4Two_of_native f4TwoNative

theorem seitzExcHighF4_geFive_of_one (h1 : SeitzExcHighF4One) :
    SeitzExcHighForAt IsF4Index PrimeRange.geFive :=
  seitzExcHighF4_geFive_of_classes h1 seitzExcHighF4Two

end Glue

end CFSG.LieType.SeitzGeneration.ExcHigh

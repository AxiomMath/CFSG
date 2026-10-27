module

public import CFSG.GH74.Generic.BProg.B3.S1ThreeLift
public import CFSG.GH74.Generic.BProg.B3.S1Split
public import CFSG.GH74.Generic.BProg.B3.S1Lemma282ANeX
public import CFSG.GH74.Generic.BProg.B1.PilotS1ThreeFacts
public import CFSG.GH74.Generic.S1.CompIdent
public import CFSG.GH74.Generic.S1.SL2Facts
public import CFSG.GH74.Generic.S1.Exo.Q3Core
public import CFSG.GH74.GLS.Balance.Bender.Final
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.CompletedOddCoreElimination
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.GH74.E2.ComponentsShape
public import CFSG.GH74.GLS.Bg.Iii2.L41Comp
public import CFSG.GH74.GLS.C3.Layer1.Th2V2Core
public import CFSG.GH74.GLS.SP.Consistency
public import CFSG.GH74.GLS.SP.Generic
public import CFSG.GH74.GLS.Stage2.Final.ModelLUMain
public import CFSG.GH74.GLS.Stage2.Local.Concl
public import CFSG.GH74.Generic.BProg.B1.Assembly2
public import CFSG.GH74.Generic.BProg.B1.PilotS3
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicQuot
public import CFSG.GH74.Generic.BProg.B2.GenLocU3
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.S1.Exo.Leaf
public import CFSG.GH74.Generic.S3.LeavesFine
public import CFSG.GH74.Generic.S3.Lem37
public import CFSG.GH74.KGroups.L3EpsInvLin
public import CFSG.GroupTheory.ElementaryAbelianBasis
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CyclicFour
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import Certificates.Certificate5007

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1Three

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS1 CFSG.GH74.L5U5
open CFSG.GH74.Generic.BProg.B3.S1SplitAux Subgroup
open CFSG.GH74.Filter.ClassicalOdd (Q8)
open scoped MatrixGroups commutatorElement

theorem q8_pow4 : ∀ g : Q8, g ^ (2 ^ 2) = 1 := by decide

theorem q8_z_sq : (QuaternionGroup.a 2 : Q8) * QuaternionGroup.a 2 = 1 := by decide

theorem q8_z_ne : (QuaternionGroup.a 2 : Q8) ≠ 1 := by decide

theorem injective_comp_of_odd {H H' : Type*} [Group H] [Group H'] (f : Q8 →* H)
    (hf : Function.Injective f) (π : H →* H') (hπ : ∀ h, π h = 1 → Odd (orderOf h)) :
    Function.Injective (π.comp f) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  have h1 := hπ (f q) hq
  have h2 : orderOf (f q) ∣ 2 ^ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, q8_pow4, map_one])
  have hcop : Nat.Coprime (orderOf (f q)) (2 ^ 2) :=
    Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 h1)
  have h3 : orderOf (f q) = 1 := Nat.Coprime.eq_one_of_dvd hcop h2
  exact hf ((orderOf_eq_one_iff.1 h3).trans (map_one f).symm)

theorem normal_of_centralizer_le {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsComponent L) {z : X} (hC : ∀ w ∈ centralizer (L : Set X), w = 1 ∨ w = z) : L.Normal := by
  refine ⟨fun n hn g => ?_⟩
  by_contra hng
  set Lc : Subgroup X := L.map (MulAut.conj g).toMonoidHom with hLc
  have hLcc : IsComponent Lc := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hL
  have hne : L ≠ Lc := by
    intro h
    exact hng (by rw [h]; exact ⟨n, hn, rfl⟩)
  have hcomm : ⁅Lc, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (CFSG.LocalCores.distinct_components_commute hL hLcc).resolve_left hne
  have hLle : Lc ≤ centralizer (L : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hab : IsMulCommutative ↥Lc := ⟨⟨fun a b => Subtype.ext (by
    rcases hC _ (hLle a.2) with h1 | h1 <;> rcases hC _ (hLle b.2) with h2 | h2 <;>
      simp only [Subgroup.coe_mul, h1, h2, one_mul, mul_one])⟩⟩
  have hperf : Group.IsPerfect ↥Lc := hLcc.1.1
  have hss : Subsingleton ↥Lc := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hLcc.1
  exact not_subsingleton _ hss

theorem exists_q8_of_sl23 {X : Type} [Group X] {J : Subgroup X} {F : Type} [Field F] [Finite F]
    (hF3 : Nat.card F = 3) (e : ↥J ≃* SL(2, F)) {u : X} (hu : u ∈ J) (hu2 : orderOf u = 2) :
    ∃ τ : Q8 →* X, Function.Injective τ ∧ (∀ q, τ q ∈ J) ∧ τ (QuaternionGroup.a 2) = u := by
  have hV : HasSL2Model ↥J (fun q' => q' = 3) :=
    ⟨F, inferInstance, inferInstance, hF3,
      ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)⟩⟩
  obtain ⟨ψ, hψi, hψm⟩ := CFSG.GH74.Generic.S1.exists_q8_of_hasSL2Model (by decide : Odd 3) hV
  obtain ⟨t, -, -, ht, -⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts (by decide : Odd 3) hV
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu2
    omega
  have huu : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  have hut : u = t := (ht u hu huu).resolve_left hu1
  refine ⟨ψ, hψi, hψm, ?_⟩
  have hsq : ψ (QuaternionGroup.a 2) * ψ (QuaternionGroup.a 2) = 1 := by
    rw [← map_mul, q8_z_sq, map_one]
  rcases ht _ (hψm _) hsq with h1 | h1
  · exact absurd (hψi (h1.trans (map_one ψ).symm)) q8_z_ne
  · rw [h1, hut]

section Hom

variable {G : Type} [Group G]

abbrev Yc (a x : G) (hxa : x ∈ centralizer ({a} : Set G)) : Subgroup ↥(centralizer ({a} : Set G)) :=
  centralizer ({(⟨x, hxa⟩ : ↥(centralizer ({a} : Set G)))} : Set ↥(centralizer ({a} : Set G)))

theorem mem_cx_of_mem_Yc {a x : G} {hxa : x ∈ centralizer ({a} : Set G)} (y : ↥(Yc a x hxa)) :
    ((y : ↥(centralizer ({a} : Set G))) : G) ∈ centralizer ({x} : Set G) := by
  have h := Subgroup.mem_centralizer_singleton_iff.1 y.2
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val h

@[expose] noncomputable def inclYc (a x : G) (hxa : x ∈ centralizer ({a} : Set G)) :
    ↥(Yc a x hxa) →* ↥(centralizer ({x} : Set G)) :=
  ((centralizer ({a} : Set G)).subtype.comp (Yc a x hxa).subtype).codRestrict _
    fun y => mem_cx_of_mem_Yc y

theorem inclYc_apply (a x : G) (hxa : x ∈ centralizer ({a} : Set G)) (y : ↥(Yc a x hxa)) :
    ((inclYc a x hxa y : ↥(centralizer ({x} : Set G))) : G) = ((y : ↥(centralizer ({a} : Set G))) : G) :=
  rfl

theorem inclYc_injective (a x : G) (hxa : x ∈ centralizer ({a} : Set G)) :
    Function.Injective (inclYc a x hxa) := fun y y' h => by
  have h1 := congrArg Subtype.val h
  rw [inclYc_apply, inclYc_apply] at h1
  exact Subtype.ext (Subtype.ext h1)

@[expose] noncomputable def gHom (a x : G) (hxa : x ∈ centralizer ({a} : Set G)) :
    ↥(Yc a x hxa) →* CentralizerBar x :=
  (proj x).comp (inclYc a x hxa)

variable [Finite G]

theorem not_two_dvd_card_ker_gHom (a x : G) (hxa : x ∈ centralizer ({a} : Set G)) :
    ¬ 2 ∣ Nat.card (gHom a x hxa).ker :=
  B1.not_two_dvd_card_ker_comp_mk (inclYc a x hxa) (inclYc_injective a x hxa)
    (pPrimeCore 2 ↥(centralizer ({x} : Set G)))
    (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card)

theorem range_gHom {a x : G} (hxa : x ∈ centralizer ({a} : Set G))
    (hax : a ∈ centralizer ({x} : Set G)) (ha2 : orderOf a = 2) :
    (gHom a x hxa).range = centralizer ({proj x ⟨a, hax⟩} : Set (CentralizerBar x)) := by
  ext c
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show proj x (inclYc a x hxa y) * proj x ⟨a, hax⟩ = proj x ⟨a, hax⟩ * proj x (inclYc a x hxa y)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (y : ↥(centralizer ({a} : Set G))).2
  · intro hc
    have hker : Odd (Nat.card (proj x).ker) := by
      have : (proj x).ker = pPrimeCore 2 ↥(centralizer ({x} : Set G)) := QuotientGroup.ker_mk' _
      rw [this]
      exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
    have hord : orderOf (⟨a, hax⟩ : ↥(centralizer ({x} : Set G))) = 2 := by
      rw [Subgroup.orderOf_mk]; exact ha2
    have hcr : c ∈ (proj x).range := by
      obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(centralizer ({x} : Set G))) c
      exact ⟨g, hg⟩
    obtain ⟨g', hg1, hg2⟩ := exists_commuting_lift (proj x) hker hord hcr
      (Subgroup.mem_centralizer_singleton_iff.1 hc)
    have ga : (g' : G) ∈ centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hg2)
    have gY : (⟨(g' : G), ga⟩ : ↥(centralizer ({a} : Set G))) ∈ Yc a x hxa := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 g'.2
    refine ⟨⟨⟨(g' : G), ga⟩, gY⟩, ?_⟩
    rw [← hg1]
    rfl

end Hom

section Bal

variable {G : Type} [Group G] [Finite G]

theorem bal_of_solvComp (hSB : Balance.SolvableL2PrimeBalance) {a x : G}
    (hxa : x ∈ centralizer ({a} : Set G)) (hx2 : orderOf x = 2) {V : Subgroup ↥(Yc a x hxa)}
    (hV : Balance.IsSolvTwoCompSL23 ↥(Yc a x hxa) V) (ψ : Q8 →* ↥(Yc a x hxa)) (hψ : ∀ q, ψ q ∈ V) :
    (∀ q, proj a ((Yc a x hxa).subtype (ψ q)) ∈ pCore 2 (CentralizerBar a)) ∨
      ∃ N : Subgroup (CentralizerBar a), IsComponent N ∧
        ∀ q, proj a ((Yc a x hxa).subtype (ψ q)) ∈ N := by
  set X := ↥(centralizer ({a} : Set G)) with hX
  set xX : X := ⟨x, hxa⟩ with hxX
  have hxX2 : orderOf xX = 2 := by rw [hxX, Subgroup.orderOf_mk]; exact hx2
  set V' : Subgroup X := V.map (Yc a x hxa).subtype with hV'def
  have hV' : Balance.IsSolvTwoCompSL23In (centralizer ({xX} : Set X)) V' := by
    refine ⟨Subgroup.map_subtype_le V, ?_⟩
    have : V'.subgroupOf (Yc a x hxa) = V :=
      Subgroup.comap_map_eq_self_of_injective (Yc a x hxa).subtype_injective V
    rw [this]
    exact hV
  have hres : ∀ q, (Yc a x hxa).subtype (ψ q) ∈ oPrimeResidualOf 2 V' := fun q =>
    ⟨⟨_, Subgroup.mem_map_of_mem _ (hψ q)⟩, Subgroup.subset_closure ⟨2, Subtype.ext (by
      rw [SubgroupClass.coe_pow]
      show ((Yc a x hxa).subtype (ψ q)) ^ (2 ^ 2) = 1
      rw [← map_pow, ← map_pow, q8_pow4, map_one, map_one])⟩, rfl⟩
  rcases hSB X xX hxX2 V' hV' with h | ⟨L, hL, -, hLle⟩
  · left
    intro q
    exact h (hres q)
  · right
    obtain ⟨N, hN, -, hLN, -⟩ := hL
    refine ⟨N, hN, fun q => ?_⟩
    rw [← hLN]
    exact ⟨_, hLle (hres q), rfl⟩

end Bal

structure S1ThreeData {G : Type} [Group G] (x a : G) (φA φB : Q8 →* CentralizerBar a) : Prop where
  injA : Function.Injective φA
  injB : Function.Injective φB
  zA : φA (QuaternionGroup.a 2) = bar a a
  zB : φB (QuaternionGroup.a 2) = bar a (x * a)
  comm : ∀ p q : Q8, φA p * φB q = φB q * φA p
  balA : (∀ q, φA q ∈ pCore 2 (CentralizerBar a)) ∨
    ∃ N : Subgroup (CentralizerBar a), IsComponent N ∧ ∀ q, φA q ∈ N
  balB : (∀ q, φB q ∈ pCore 2 (CentralizerBar a)) ∨
    ∃ N : Subgroup (CentralizerBar a), IsComponent N ∧ ∀ q, φB q ∈ N

variable {G : Type} [Group G] [Finite G]


theorem exists_s1ThreeData {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}
    (hc : Ctx21 G x K A a D J) (h3 : B1.PilotS1.QShape1Three (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∃ φA φB : Q8 →* CentralizerBar a, S1ThreeData x a φA φB := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF3, ⟨eK⟩⟩ := h3
  have h1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K) :=
    Or.inl ⟨F, inferInstance, inferInstance, by omega, ⟨eK⟩⟩
  obtain ⟨hxK, hAK, hxA, hCY⟩ := s1_basic hc h1
  have hax : a ≠ x := s1_a_ne_x hc h1
  have hx2 : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have ha2 : orderOf a = 2 := hc.obs.y_ord
  have haA : a ∈ A := hc.a_mem
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hc.src.2.1
  have hA8 : Nat.card ↥A = 8 := hc.src.2.2.1
  have hAsq : ∀ b ∈ A, b * b = 1 := fun b hb => by
    rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) b hb
  have hAcomm : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc' =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨b, hb⟩ ⟨c, hc'⟩)
  have hxa_comm : x * a = a * x := hAcomm x hxA a haA
  have hxa : x ∈ centralizer ({a} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hxa_comm
  have hax' : a ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxa_comm.symm
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  obtain ⟨z₀, hP⟩ := B1.PilotS1.grpS1_lin (F := F) (by omega)
  obtain ⟨-, -, -, hY, -, -⟩ := B1.PilotS1.shape1_data hc.hyp.gen4 hx2 hK eK hP h1
  have hKc : IsComponent (imgBar x K) := by
    obtain ⟨-, Kb, hKb, -, hmap, -⟩ := hK
    show IsComponent ((K.subgroupOf (centralizer ({x} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G)))))
    rw [hmap]
    exact hKb
  have hKn : (imgBar x K).Normal := normal_of_centralizer_le hKc hCY
  have haK : a ∈ K := hAK haA
  obtain ⟨hub, -, hub2⟩ := bar_facts hKC haK ha2
  have hubx : bar x a ≠ xbar x := by
    intro h
    apply hax
    refine B1.PilotS1.eq_of_proj_eq hax' hxC (hAcomm a haA x hxA) (hAsq a haA) (hAsq x hxA) ?_
    rw [← bar_of_mem hax']; exact h
  obtain ⟨Jb₁, Jb₂, hS⟩ := hY.split (bar x a) hub hub2 hubx
  set g := gHom a x hxa with hgdef
  have hgker : ¬ 2 ∣ Nat.card g.ker := not_two_dvd_card_ker_gHom a x hxa
  have hgrange : g.range = centralizer ({bar x a} : Set (CentralizerBar x)) := by
    rw [bar_of_mem hax']; exact range_gHom hxa hax' ha2
  have hsub : ∀ Jb : Subgroup (CentralizerBar x),
      Jb ≤ centralizer ({bar x a} : Set (CentralizerBar x)) ⊓ imgBar x K →
      (∀ c ∈ imgBar x K, c * bar x a = bar x a * c → ∀ j ∈ Jb, c * j * c⁻¹ ∈ Jb) →
      (Jb.subgroupOf g.range).IsSubnormal := by
    intro Jb hle hn
    refine CFSG.GH74.Generic.S1.Exo.isSubnormal_subgroupOf_of_two_step
      (R := centralizer ({bar x a} : Set (CentralizerBar x)) ⊓ imgBar x K) hle ?_ ?_
    · intro r hr j hj
      exact hn r hr.2 (Subgroup.mem_centralizer_singleton_iff.1 hr.1) j hj
    · intro t ht r hr
      rw [hgrange] at ht
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hr.1) (Subgroup.inv_mem _ ht),
        hKn.conj_mem r hr.2 t⟩
  obtain ⟨e₁⟩ := hS.equiv₁
  obtain ⟨e₂⟩ := hS.equiv₂
  obtain ⟨σ⟩ := B1.PilotS1.nonempty_slEquiv_zmod_three hF3
  have hJr : ∀ Jb : Subgroup (CentralizerBar x),
      Jb ≤ centralizer ({bar x a} : Set (CentralizerBar x)) ⊓ imgBar x K → Jb ≤ g.range :=
    fun Jb hle j hj => by rw [hgrange]; exact (hle hj).1
  obtain ⟨V₁, hV₁, hJV₁⟩ := isSolvTwoComp_of_map g hgker (hJr Jb₁ hS.le₁) (hsub Jb₁ hS.le₁ hS.norm₁)
    ⟨e₁.trans σ⟩
  obtain ⟨V₂, hV₂, hJV₂⟩ := isSolvTwoComp_of_map g hgker (hJr Jb₂ hS.le₂) (hsub Jb₂ hS.le₂ hS.norm₂)
    ⟨e₂.trans σ⟩
  have hxaC : x * a ∈ centralizer ({x} : Set G) := Subgroup.mul_mem _ hxC hax'
  have hbxa : bar x (x * a) = xbar x * bar x a := by
    rw [bar_of_mem hxaC, bar_of_mem hax']
    show proj x (⟨x, hxC⟩ * ⟨a, hax'⟩) = _
    rw [map_mul]
    rfl
  have hxa2 : orderOf (x * a) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · calc (x * a) ^ 2 = x * (a * x) * a := by rw [pow_two]; simp only [mul_assoc]
        _ = x * (x * a) * a := by rw [hxa_comm]
        _ = (x * x) * (a * a) := by group
        _ = 1 := by rw [hAsq x hxA, hAsq a haA, one_mul]
    · intro h
      apply hax
      have h' : x = a⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [h', inv_eq_of_mul_eq_one_left (hAsq a haA)]
  obtain ⟨-, -, hxu2⟩ := bar_facts hKC (K.mul_mem hxK haK) hxa2
  rw [hbxa] at hxu2
  obtain ⟨τ₁, hτ₁i, hτ₁m, hτ₁z⟩ := exists_q8_of_sl23 hF3 e₁ hS.u_mem hub2
  obtain ⟨τ₂, hτ₂i, hτ₂m, hτ₂z⟩ := exists_q8_of_sl23 hF3 e₂ hS.zu_mem hxu2
  have hτcomm : ∀ p q : Q8, Commute (τ₁ p) (τ₂ q) := fun p q =>
    hS.commute _ (hτ₁m p) _ (hτ₂m q)
  set E : Subgroup (CentralizerBar x) := τ₁.range ⊔ τ₂.range with hEdef
  have hE2 : IsPGroup 2 ↥E := by
    have hrange : (τ₁.noncommCoprod τ₂ hτcomm).range = E := MonoidHom.noncommCoprod_range τ₁ τ₂ hτcomm
    have hQQ : IsPGroup 2 (Q8 × Q8) := fun g => ⟨2, Prod.ext (q8_pow4 g.1) (q8_pow4 g.2)⟩
    rw [← hrange]
    exact hQQ.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hτ₁E : ∀ q, τ₁ q ∈ E := fun q => Subgroup.mem_sup_left ⟨q, rfl⟩
  have hτ₂E : ∀ q, τ₂ q ∈ E := fun q => Subgroup.mem_sup_right ⟨q, rfl⟩
  have hEr : E ≤ g.range := by
    rw [hgrange]
    refine sup_le ?_ ?_
    · rintro _ ⟨q, rfl⟩
      exact (hS.le₁ (hτ₁m q)).1
    · rintro _ ⟨q, rfl⟩
      exact (hS.le₂ (hτ₂m q)).1
  set ιY : ↥(Yc a x hxa) →* G := (centralizer ({a} : Set G)).subtype.comp (Yc a x hxa).subtype
    with hιY
  have hιYi : Function.Injective ιY :=
    (centralizer ({a} : Set G)).subtype_injective.comp (Yc a x hxa).subtype_injective
  have haC : a ∈ centralizer ({a} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have haY : (⟨a, haC⟩ : ↥(centralizer ({a} : Set G))) ∈ Yc a x hxa := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hxa_comm.symm
  have hxY : (⟨x, hxa⟩ : ↥(centralizer ({a} : Set G))) ∈ Yc a x hxa :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  set a' : ↥(Yc a x hxa) := ⟨⟨a, haC⟩, haY⟩ with ha'
  set x' : ↥(Yc a x hxa) := ⟨⟨x, hxa⟩, hxY⟩ with hx'
  have hga' : g a' = bar x a := by rw [bar_of_mem hax']; rfl
  have hgx' : g x' = xbar x := rfl
  have hua : bar x a * bar x a = 1 := by
    have h := pow_orderOf_eq_one (bar x a)
    rw [hub2, pow_two] at h
    exact h
  have hxE : xbar x ∈ E := by
    have : xbar x = τ₂ (QuaternionGroup.a 2) * τ₁ (QuaternionGroup.a 2) := by
      rw [hτ₂z, hτ₁z, mul_assoc, hua, mul_one]
    rw [this]
    exact E.mul_mem (hτ₂E _) (hτ₁E _)
  set P₀ : Subgroup ↥(Yc a x hxa) := A.comap ιY ⊓ E.comap g with hP₀
  have hA2 : IsPGroup 2 ↥A := IsPGroup.of_card (n := 3) (by rw [hA8]; norm_num)
  have hP₀2 : IsPGroup 2 ↥P₀ := (hA2.comap_of_injective ιY hιYi).to_le inf_le_left
  have hP₀E : P₀.map g ≤ E := Subgroup.map_le_iff_le_comap.2 inf_le_right
  have ha'P₀ : a' ∈ P₀ := ⟨haA, show g a' ∈ E by rw [hga', ← hτ₁z]; exact hτ₁E _⟩
  have hx'P₀ : x' ∈ P₀ := ⟨hxA, show g x' ∈ E by rw [hgx']; exact hxE⟩
  obtain ⟨S, hP₀S, hSE, hSinj⟩ := exists_lift_two_le g hgker E hEr hE2 hP₀2 hP₀E
  have huniq : ∀ s ∈ S, ∀ t ∈ S, g s = g t → s = t := fun s hs t ht h => by
    have := hSinj (s * t⁻¹) (S.mul_mem hs (S.inv_mem ht)) (by rw [map_mul, map_inv, h, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  have hgSmem : ∀ s : ↥S, g s ∈ E := fun s => hSE ▸ Subgroup.mem_map_of_mem g s.2
  set gS : ↥S →* ↥E := (g.comp S.subtype).codRestrict E hgSmem with hgS
  have hgSbij : Function.Bijective gS := by
    refine ⟨fun s t h => Subtype.ext (huniq _ s.2 _ t.2 (congrArg Subtype.val h)), fun e => ?_⟩
    have he : (e : CentralizerBar x) ∈ S.map g := hSE.symm ▸ e.2
    obtain ⟨s, hs, hse⟩ := he
    exact ⟨⟨s, hs⟩, Subtype.ext hse⟩
  set eS : ↥S ≃* ↥E := MulEquiv.ofBijective gS hgSbij with heS
  set τ₁E : Q8 →* ↥E := τ₁.codRestrict E hτ₁E with hτ₁E'
  set τ₂E : Q8 →* ↥E := τ₂.codRestrict E hτ₂E with hτ₂E'
  set ψA : Q8 →* ↥(Yc a x hxa) := S.subtype.comp (eS.symm.toMonoidHom.comp τ₁E) with hψA
  set ψB : Q8 →* ↥(Yc a x hxa) := S.subtype.comp (eS.symm.toMonoidHom.comp τ₂E) with hψB
  have hgψA : ∀ q, g (ψA q) = τ₁ q := fun q =>
    congrArg Subtype.val (eS.apply_symm_apply (τ₁E q))
  have hgψB : ∀ q, g (ψB q) = τ₂ q := fun q =>
    congrArg Subtype.val (eS.apply_symm_apply (τ₂E q))
  have hψAS : ∀ q, ψA q ∈ S := fun q => (eS.symm (τ₁E q)).2
  have hψBS : ∀ q, ψB q ∈ S := fun q => (eS.symm (τ₂E q)).2
  have hψAi : Function.Injective ψA :=
    S.subtype_injective.comp (eS.symm.injective.comp fun p q h => hτ₁i (congrArg Subtype.val h))
  have hψBi : Function.Injective ψB :=
    S.subtype_injective.comp (eS.symm.injective.comp fun p q h => hτ₂i (congrArg Subtype.val h))
  have hψAz : ψA (QuaternionGroup.a 2) = a' :=
    huniq _ (hψAS _) _ (hP₀S ha'P₀) (by rw [hgψA, hτ₁z, hga'])
  have hψBz : ψB (QuaternionGroup.a 2) = x' * a' :=
    huniq _ (hψBS _) _ (S.mul_mem (hP₀S hx'P₀) (hP₀S ha'P₀)) (by rw [hgψB, hτ₂z, map_mul, hgx', hga'])
  have hψcomm : ∀ p q, ψA p * ψB q = ψB q * ψA p := fun p q =>
    huniq _ (S.mul_mem (hψAS p) (hψBS q)) _ (S.mul_mem (hψBS q) (hψAS p)) (by
      rw [map_mul, map_mul, hgψA, hgψB]; exact hS.commute _ (hτ₁m p) _ (hτ₂m q))
  have hψAV : ∀ q, ψA q ∈ V₁ := fun q => hJV₁ (show g (ψA q) ∈ Jb₁ by rw [hgψA]; exact hτ₁m q)
  have hψBV : ∀ q, ψB q ∈ V₂ := fun q => hJV₂ (show g (ψB q) ∈ Jb₂ by rw [hgψB]; exact hτ₂m q)
  have hodd : ∀ h : ↥(centralizer ({a} : Set G)), proj a h = 1 → Odd (orderOf h) := fun h hh =>
    proj_odd a h hh
  refine ⟨(proj a).comp ((Yc a x hxa).subtype.comp ψA),
    (proj a).comp ((Yc a x hxa).subtype.comp ψB), ?_⟩
  refine
    { injA := injective_comp_of_odd _ ((Yc a x hxa).subtype_injective.comp hψAi) _ hodd
      injB := injective_comp_of_odd _ ((Yc a x hxa).subtype_injective.comp hψBi) _ hodd
      zA := ?_
      zB := ?_
      comm := fun p q => by
        simp only [MonoidHom.comp_apply]
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hψcomm]
      balA := bal_of_solvComp Balance.solvableL2PrimeBalance_proved hxa hx2 hV₁ ψA hψAV
      balB := bal_of_solvComp Balance.solvableL2PrimeBalance_proved hxa hx2 hV₂ ψB hψBV }
  · simp only [MonoidHom.comp_apply]
    rw [hψAz, bar_of_mem haC]
    rfl
  · simp only [MonoidHom.comp_apply]
    rw [hψBz, bar_of_mem (Subgroup.mul_mem _ hxa haC)]
    rfl

end S1Three

end CFSG.GH74.Generic.BProg.B3

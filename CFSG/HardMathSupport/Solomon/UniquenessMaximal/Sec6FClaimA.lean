module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FStmts
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DClaim
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem jstar_dichotomy (i183 : Input18_3_4) {N Ka J : Subgroup G} {x : G}
    (hN : CFSG.Open.IsKGroup ↥N) (hKa : GLAPComponent 3 N Ka) (hxN : x ∈ N) (hx3 : x ^ 3 = 1)
    (hxKa : GLBConj x Ka = Ka)
    (hJ : GLAPComponent 3 (N ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    J ≤ (⨆ g ∈ GLAPLayer 3 N, GLBConj g J) ∧
      ((⨆ g ∈ GLAPLayer 3 N, GLBConj g J) = Ka ∨
        (⨆ g ∈ GLAPLayer 3 N, GLBConj g J) ≤
          LocalBalance.centralizerQuot Ka (GLAPPrimeCoreOf 3 N)) := by
  have hJJ : J ≤ ⨆ g ∈ GLAPLayer 3 N, GLBConj g J := by
    have := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 N) => GLBConj g J) 1 (Subgroup.one_mem _)
    rwa [gLBConj_one] at this
  refine ⟨hJJ, ?_⟩
  have hlecq : ∀ P : Subgroup G, GLAPComponent 3 N P → P ≠ Ka →
      P ≤ LocalBalance.centralizerQuot Ka (GLAPPrimeCoreOf 3 N) := by
    intro P hP hne k hkP
    refine ⟨le_normalizer_of_ne hP hKa hne hkP,
      normalizer_core 3 (Subgroup.le_normalizer (hP.1 hkP)), fun f hf => ?_⟩
    exact commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hKa hP hne.symm
      (Subgroup.commutator_mem_commutator hf hkP)
  rcases dichotomy_of_input18_3_4 i183 hN hxN hx3 hJ with
    ⟨Lc, hLc, -, hJ0, -⟩ |
    ⟨L₁, L₂, L₃, h₁, h₂, h₃, h12, h23, h31, hx1', hx2', hx3', hu, -⟩
  · by_cases hLK : Lc = Ka
    · left; rw [hJ0, hLK]
    · right; rw [hJ0]; exact hlecq Lc hLc hLK
  · right
    rw [hu]
    have hL₁ : L₁ ≠ Ka := by
      intro h; apply h12
      calc L₁ = Ka := h
        _ = GLBConj x Ka := hxKa.symm
        _ = GLBConj x L₁ := by rw [h]
        _ = L₂ := hx1'
    have hL₂ : L₂ ≠ Ka := by
      intro h; apply h23
      calc L₂ = Ka := h
        _ = GLBConj x Ka := hxKa.symm
        _ = GLBConj x L₂ := by rw [h]
        _ = L₃ := hx2'
    have hL₃ : L₃ ≠ Ka := by
      intro h; apply h31
      calc L₃ = Ka := h
        _ = GLBConj x Ka := hxKa.symm
        _ = GLBConj x L₃ := by rw [h]
        _ = L₁ := hx3'
    exact sup_le (sup_le (hlecq L₁ h₁ hL₁) (hlecq L₂ h₂ hL₂)) (hlecq L₃ h₃ hL₃)

theorem no_slThreeFour_section (hNoSL : InputNoSLSection) {Ka J : Subgroup G}
    (hKaT : IsLThreeEps (barOf 3 Ka)) (hJ : J ≤ Ka) {S : Type} [Group S]
    (hS : IsSLThreeFour S) (θ : ↥J →* S) (hθ : Function.Surjective θ)
    (hker : ∀ y : ↥J, (y : G) ∈ GLAPPrimeCoreOf 3 Ka → θ y = 1) : False := by
  set φ : ↥J →* barOf 3 Ka :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Ka)).comp (Subgroup.inclusion hJ) with hφ
  have hle : φ.ker ≤ θ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    apply hker
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Ka)) (Subgroup.inclusion hJ y) = 1 := hy
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    exact (mem_coreOf_iff (Subgroup.inclusion hJ y)).2 h2
  let e : ↥J ⧸ φ.ker ≃* φ.range := QuotientGroup.quotientKerEquivRange φ
  let ψ : ↥φ.range →* S := (QuotientGroup.lift φ.ker θ hle).comp e.symm.toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro s
    obtain ⟨y, rfl⟩ := hθ s
    refine ⟨e (QuotientGroup.mk y), ?_⟩
    simp [ψ]
  let e2 : ↥φ.range ⧸ ψ.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  obtain ⟨K', hf, hfin, hc, ⟨iso⟩⟩ := hS
  exact hNoSL (barOf 3 Ka) hKaT φ.range ψ.ker ⟨K', hf, hfin, hc, ⟨e2.trans iso⟩⟩


omit [Finite G] in
theorem core_le_self (K : Subgroup G) : GLAPPrimeCoreOf 3 K ≤ K := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem surj_of_le_sup {K J : Subgroup G} (hJK : J ≤ K) (h : K ≤ J ⊔ GLAPPrimeCoreOf 3 K) :
    Function.Surjective
      ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hJK)) := by
  set θ := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hJK) with hθ
  set T : Subgroup ↥K := θ.range.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) with hT
  have hJT : J ≤ T.map K.subtype := fun j hj =>
    ⟨⟨j, hJK hj⟩, ⟨⟨j, hj⟩, rfl⟩, rfl⟩
  have hUT : GLAPPrimeCoreOf 3 K ≤ T.map K.subtype := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, ?_, rfl⟩
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) y ∈ θ.range
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) y = 1 := (QuotientGroup.eq_one_iff y).2 hy
    rw [h1]
    exact one_mem _
  intro s
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
  have hq : (q : G) ∈ T.map K.subtype := sup_le hJT hUT (h q.2)
  obtain ⟨t, ht, htq⟩ := hq
  have : t = q := Subtype.ext htq
  rw [this] at ht
  exact ht

theorem mem_dQ_of_comm_mod {K J : Subgroup G} {f : G} (hf : f ∈ Subgroup.normalizer (K : Set G))
    (hJK : J ≤ K) (h : K ≤ J ⊔ GLAPPrimeCoreOf 3 K)
    (hc : ∀ j ∈ J, f * j * f⁻¹ * j⁻¹ ∈ GLAPPrimeCoreOf 3 K) : f ∈ dQ K := by
  have hfU : f ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := normalizer_core 3 hf
  have hyU : ∀ y ∈ K, y ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := fun y hy =>
    normalizer_core 3 (Subgroup.le_normalizer hy)
  let S : Subgroup G :=
    { carrier := {y | y ∈ K ∧ f * y * f⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 3 K}
      one_mem' := ⟨K.one_mem, by simp⟩
      mul_mem' := by
        rintro y z ⟨hyK, hy⟩ ⟨hzK, hz⟩
        refine ⟨K.mul_mem hyK hzK, ?_⟩
        have h1 : f * (y * z) * f⁻¹ * (y * z)⁻¹ =
            (f * y * f⁻¹ * y⁻¹) * (y * (f * z * f⁻¹ * z⁻¹) * y⁻¹) := by group
        rw [h1]
        refine Subgroup.mul_mem _ hy ?_
        exact (Subgroup.mem_normalizer_iff.1 (hyU y hyK) _).1 hz
      inv_mem' := by
        rintro y ⟨hyK, hy⟩
        refine ⟨K.inv_mem hyK, ?_⟩
        have h1 : f * y⁻¹ * f⁻¹ * (y⁻¹)⁻¹ = y⁻¹ * (f * y * f⁻¹ * y⁻¹)⁻¹ * y := by group
        rw [h1]
        have h2 : (f * y * f⁻¹ * y⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 K := Subgroup.inv_mem _ hy
        have := (Subgroup.mem_normalizer_iff.1 (hyU y⁻¹ (K.inv_mem hyK)) _).1 h2
        simpa using this }
  have hJS : J ≤ S := fun j hj => ⟨hJK hj, hc j hj⟩
  have hUS : GLAPPrimeCoreOf 3 K ≤ S := fun u hu => by
    refine ⟨core_le_self K hu, ?_⟩
    have h1 : f * u * f⁻¹ * u⁻¹ = (f * u * f⁻¹) * u⁻¹ := rfl
    rw [h1]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 hfU u).1 hu) (Subgroup.inv_mem _ hu)
  have hKS : K ≤ S := h.trans (sup_le hJS hUS)
  refine ⟨hf, hfU, fun y hy => ?_⟩
  have h1 : y * f * y⁻¹ * f⁻¹ = (f * y * f⁻¹ * y⁻¹)⁻¹ := by group
  rw [h1]
  exact Subgroup.inv_mem _ (hKS hy).2


theorem claimA (hcov : CoverStmt) (iL3 : InputL3U3Facts) (i183 : Input18_3_4) (h515 : Lemma515)
    (hKT : InputKType) (hNoSL : InputNoSLSection)
    {m : ℕ} {B : Subgroup G} {b : G} {L A : Subgroup G} (e : Env m B b L A)
    {x : G} (hx : x ∈ B) (hx1 : x ≠ 1) {K : Subgroup G}
    (hcomp : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K)
    (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hSL : IsSLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K)) (hcard : Nat.card ↥(B ⊓ dQ K) = 9)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (haD : a ∈ dQ K) : False := by
  have _ := hx1
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haB : a ∈ B := e.X.AB haA
  have ha3 : a ^ 3 = 1 := e.X.Bel.2 a haB
  have hx3 : x ^ 3 = 1 := e.X.Bel.2 x hx
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set Cx := Subgroup.centralizer ({x} : Set G) with hCx
  have hKa : GLAPComponent 3 Ca (kOf L A a) := Ka_comp iL3 e.X haA ha1
  have hKaB : B ≤ Subgroup.normalizer (kOf L A a : Set G) := Ka_B h515 e haA ha1
  have hBCa : B ≤ Ca := fun c hc => by
    rw [hCa, Subgroup.mem_centralizer_singleton_iff]; exact ea_comm e.X.Bel hc haB
  have hzp : IsPGroup 3 ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]; simp)
  have hzle : Subgroup.zpowers a ≤ dQ K := (Subgroup.zpowers_le).2 haD
  obtain ⟨J0, hJ0c, hKJ0, huniq, hO⟩ := hcov G Cx K (Subgroup.zpowers a) hcomp hzp hzle
  rw [centralizer_zpowers_eq_singleton] at hJ0c huniq
  have hJ0K : J0 ≤ K := hJ0c.1.trans inf_le_left
  have hJ0Ca : J0 ≤ Ca := hJ0c.1.trans inf_le_right
  have hsn : IsSubnormal J0 (Ca ⊓ Cx) := by
    have h1 : IsSubnormal (K ⊓ Ca) (Cx ⊓ Ca) := isSubnormal_inf hcomp.2.1 Ca
    rw [inf_comm Cx Ca] at h1
    exact isSubnormal_trans' hJ0c.2.1 h1
  have hJ0c' : GLAPComponent 3 (Ca ⊓ Cx) J0 :=
    Lemma512Ns.glaPComponent_up Nat.prime_three hJ0c
      (le_inf inf_le_right (inf_le_left.trans hcomp.1)) hsn
  have hCaK : CFSG.Open.IsKGroup ↥Ca :=
    isKGroup_of_isKProper e.S.kProper (centralizer_ne_top_of_simple e.S ha1)
  have hxCa : x ∈ Ca := by
    rw [hCa, Subgroup.mem_centralizer_singleton_iff]; exact (ea_comm e.X.Bel haB hx).symm
  have hKax : GLBConj x (kOf L A a) = kOf L A a := gLBConj_eq_of_mem_normalizer (hKaB hx)
  obtain ⟨hJJ, hstar⟩ := jstar_dichotomy i183 hCaK hKa hxCa hx3 hKax hJ0c'
  rcases hstar with hEq | hcq
  ·
    have hJ0Ka : J0 ≤ kOf L A a := hEq ▸ hJJ
    refine no_slThreeFour_section hNoSL (Ka_type hKT e haA ha1) hJ0Ka hSL
      ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hJ0K))
      (surj_of_le_sup hJ0K hKJ0) ?_
    intro y hy
    have h1 : (y : G) ∈ GLAPPrimeCoreOf 3 J0 := inf_core_le 3 hJ0Ka ⟨y.2, hy⟩
    rw [hO] at h1
    have h2 : (Subgroup.inclusion hJ0K y) ∈ GLAPPrimeCore 3 ↥K :=
      (mem_coreOf_iff (Subgroup.inclusion hJ0K y)).1 h1.2
    exact (QuotientGroup.eq_one_iff _).2 h2
  ·
    have hBJ0 : ∀ f ∈ B, GLBConj f J0 = J0 := by
      intro f hf
      have hfCa : f ∈ Subgroup.normalizer (Ca : Set G) := Subgroup.le_normalizer (hBCa hf)
      have hfn : f ∈ Subgroup.normalizer ((K ⊓ Ca : Subgroup G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h1 := (Subgroup.mem_normalizer_iff.1 (hBN hf)) y
        have h2 := (Subgroup.mem_normalizer_iff.1 hfCa) y
        simp only [Subgroup.mem_inf] at h1 h2 ⊢
        rw [h1, h2]
      have h3 := glaPComponent_gLBConj hJ0c f
      rw [gLBConj_eq_of_mem_normalizer hfn] at h3
      exact huniq _ h3
    have hF : B ⊓ L ≤ dQ K := by
      intro f hf
      refine mem_dQ_of_comm_mod (hBN hf.1) hJ0K hKJ0 fun j hj => ?_
      have hjf : f * j * f⁻¹ ∈ J0 := by
        have hj' : j ∈ GLBConj f J0 := by rw [hBJ0 f hf.1]; exact hj
        exact (mem_gLBConj).1 hj'
      have hq := (hcq (hJJ hj)).2.2 f (F_le_Ka e.X a hf)
      have h4 : f * j * f⁻¹ * j⁻¹ ∈ J0 ⊓ GLAPPrimeCoreOf 3 Ca :=
        ⟨J0.mul_mem hjf (J0.inv_mem hj), hq⟩
      have h5 := inf_core_le 3 hJ0Ca h4
      rw [hO] at h5
      exact h5.2
    have hFeq : B ⊓ L = B ⊓ dQ K :=
      Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hF) (by rw [hcard, e.X.Fc])
    have haF : a ∈ B ⊓ L := by rw [hFeq]; exact ⟨haB, haD⟩
    have h6 : a ∈ A ⊓ (B ⊓ L) := ⟨haA, haF⟩
    rw [e.X.AF, Subgroup.mem_bot] at h6
    exact ha1 h6

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

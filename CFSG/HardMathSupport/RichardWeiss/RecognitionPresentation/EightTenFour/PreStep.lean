module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BarMNormalizer
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairBlocks

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.HardMathSupport.Cooperstein CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (mem_barM)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

omit [Finite G] in
theorem coe_mem_pCoreOf {M : Subgroup G} {x : ↥M} (hx : x ∈ CFSG.pCore 2 ↥M) :
    (x : G) ∈ pCoreOf 2 M := (CFSG.mem_openPCoreOf_iff x).mpr hx

omit [Finite G] in
theorem mem_pCore_of_coe_mem {M : Subgroup G} {x : ↥M} (hx : (x : G) ∈ pCoreOf 2 M) :
    x ∈ CFSG.pCore 2 ↥M := (CFSG.mem_openPCoreOf_iff x).mp hx

omit [Finite G] in
theorem normal_barM_of_le_normalizer {M Y : Subgroup G}
    (hMY : M ≤ Subgroup.normalizer (Y : Set G)) : (barM M Y).Normal := by
  refine ⟨fun c hc q => ?_⟩
  obtain ⟨⟨l, hl'⟩, hl, rfl⟩ := (mem_barM c).1 hc
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  refine (mem_barM _).2 ⟨⟨y * l * y⁻¹, ?_⟩, ?_, ?_⟩
  · exact M.mul_mem (M.mul_mem hy hl') (M.inv_mem hy)
  · exact (Subgroup.mem_normalizer_iff.1 (hMY hy) l).1 hl
  · rfl

omit [Finite G] in
theorem normal_barM_sup (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    (barM (L ⊔ S) L).Normal :=
  normal_barM_of_le_normalizer (sup_le Subgroup.le_normalizer hSL)

omit [Finite G] in
theorem commutator_self_of_isQuasisimple {Y : Type*} [Group Y] {K : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥K) : ⁅K, K⁆ = K :=
  Subgroup.isPerfect_iff.mp ⟨hq.1⟩

theorem inf_centralizer_blockV_le_sup
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) :
    (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ≤ L ⊔ pCoreOf 2 (L ⊔ S) := by
  classical
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  set M : Subgroup G := L ⊔ S with hM
  set C : Subgroup G := Subgroup.centralizer (blockV S L : Set G) with hC
  have hLs : IsTwoPrimeComponent M L :=
    Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent hA.twoRadical.1
      hA.twoRadical.isPGroup hSL
  set B := ↥M ⧸ CFSG.pCore 2 ↥M with hB
  set Lb : Subgroup B := barM M L with hLb
  have hLbn : Lb.Normal := normal_barM_sup hSL
  have hq : CFSG.Open.IsQuasisimple ↥Lb := hLs.component.2.2
  have hperf : ⁅Lb, Lb⁆ = Lb := commutator_self_of_isQuasisimple hq
  set Nb : Subgroup B := barM M C with hNb
  have hMC : M ≤ Subgroup.normalizer (C : Set G) := le_normalizer_centralizer_blockV S L
  have hNbn : Nb.Normal := normal_barM_of_le_normalizer hMC
  have hQC : pCoreOf 2 M ≤ C :=
    AscTenThree.le_centralizer_omegaOneCenterOf_self (pCoreOf 2 M)
  have hcen : barM M (L ⊓ C) ≤ (Subgroup.center ↥Lb).map Lb.subtype :=
    barM_inf_le_center_of_core_le hLs (le_sup_left.trans hMC) (inf_le_right.trans hQC)
      (not_le_centralizer_blockV hA hL hSL)
  have hNL : Nb ⊓ Lb ≤ barM M (L ⊓ C) := by
    intro x hx
    obtain ⟨m, hmC, rfl⟩ := (mem_barM x).1 hx.1
    obtain ⟨m', hm'L, hmm'⟩ := (mem_barM _).1 hx.2
    have hker : m⁻¹ * m' ∈ CFSG.pCore 2 ↥M := by
      rw [← QuotientGroup.eq]; exact hmm'.symm
    have hq1 : ((m⁻¹ * m' : ↥M) : G) ∈ pCoreOf 2 M := coe_mem_pCoreOf hker
    have hmC' : (m' : G) ∈ C := by
      have h3 : (m : G) * ((m⁻¹ * m' : ↥M) : G) ∈ C := C.mul_mem hmC (hQC hq1)
      have e : (m : G) * ((m⁻¹ * m' : ↥M) : G) = m' := by simp
      rwa [e] at h3
    exact (mem_barM _).2 ⟨m', ⟨hm'L, hmC'⟩, hmm'⟩
  have hZcen : (Subgroup.center ↥Lb).map Lb.subtype ≤ Subgroup.centralizer (Lb : Set B) := by
    rintro _ ⟨z, hz, rfl⟩ y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩)
  have hcomm : ⁅Nb, Lb⁆ ≤ (Subgroup.center ↥Lb).map Lb.subtype := by
    refine le_trans ?_ (hNL.trans hcen)
    exact le_inf (Subgroup.commutator_le_left _ _) (Subgroup.commutator_le_right _ _)
  have hcc : ⁅⁅Nb, Lb⁆, Lb⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅Nb, Lb⁆, Lb⁆ ≤ ⁅(Subgroup.center ↥Lb).map Lb.subtype, Lb⁆ :=
          Subgroup.commutator_mono hcomm le_rfl
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZcen
  have hNC : Nb ≤ Subgroup.centralizer (Lb : Set B) :=
    StarAux.le_centralizer_of_commutator_commutator_eq_bot hperf hcc
  have h2 : ∀ y : B, ∃ e : ℕ, y ^ 2 ^ e ∈ Lb := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨e, he⟩ := exists_pow_mem_sup_subgroupOf hA.twoRadical.isPGroup hSL y
    exact ⟨e, (mem_barM _).2 ⟨y ^ 2 ^ e, Subgroup.mem_subgroupOf.1 he, rfl⟩⟩
  have hodd : Odd (Nat.card (Subgroup.centralizer (Lb : Set B))) :=
    haveI := hLbn
    StarAux.odd_card_centralizer Lb h2 StarAux.pCore_quotient_pCore_eq_bot
  intro c hc
  have hcM : c ∈ M := hc.1
  have hcC : c ∈ C := hc.2
  set b : B := QuotientGroup.mk (⟨c, hcM⟩ : ↥M) with hbdef
  have hbN : b ∈ Nb := (mem_barM _).2 ⟨⟨c, hcM⟩, hcC, rfl⟩
  have hbC : b ∈ Subgroup.centralizer (Lb : Set B) := hNC hbN
  have hord : Odd (orderOf b) := by
    have h1 : orderOf (⟨b, hbC⟩ : Subgroup.centralizer (Lb : Set B)) ∣
        Nat.card (Subgroup.centralizer (Lb : Set B)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hodd.of_dvd_nat h1
  obtain ⟨e, he⟩ := h2 b
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hord) : (2 ^ e).Coprime (orderOf b))
  have hbL : b ∈ Lb := by
    rw [← hk]; exact Lb.pow_mem he k
  obtain ⟨m', hm'L, hmm'⟩ := (mem_barM _).1 hbL
  have hker : (⟨c, hcM⟩ : ↥M)⁻¹ * m' ∈ CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.eq]; exact hbdef ▸ hmm'.symm
  have hq1 := coe_mem_pCoreOf hker
  have e2 : c = (m' : G) * (((⟨c, hcM⟩ : ↥M)⁻¹ * m' : ↥M) : G)⁻¹ := by simp
  rw [e2]
  exact Subgroup.mul_mem_sup hm'L (Subgroup.inv_mem _ hq1)

theorem le_sup_pCoreOf_of_acts
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hact : ∀ s ∈ S, ∃ l ∈ L, ∀ v ∈ blockV S L, s * v * s⁻¹ = l * v * l⁻¹) :
    S ≤ L ⊔ pCoreOf 2 (L ⊔ S) := by
  intro s hs
  obtain ⟨l, hl, hsl⟩ := hact s hs
  have hsM : s ∈ L ⊔ S := Subgroup.mem_sup_right hs
  have hlM : l ∈ L ⊔ S := Subgroup.mem_sup_left hl
  have hd : l⁻¹ * s ∈ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) := by
    refine Subgroup.mem_inf.2 ⟨(L ⊔ S).mul_mem ((L ⊔ S).inv_mem hlM) hsM, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := hsl v hv
    have : v * (l⁻¹ * s) = (l⁻¹ * s) * v := by
      have e1 : (l⁻¹ * s) * v * (l⁻¹ * s)⁻¹ = l⁻¹ * (s * v * s⁻¹) * l := by group
      rw [h1] at e1
      have e2 : l⁻¹ * (l * v * l⁻¹) * l = v := by group
      rw [e2] at e1
      calc v * (l⁻¹ * s) = ((l⁻¹ * s) * v * (l⁻¹ * s)⁻¹) * (l⁻¹ * s) := by rw [e1]
        _ = (l⁻¹ * s) * v := by group
    exact this
  have hd' := inf_centralizer_blockV_le_sup hX hA hL hd
  have e : s = l * (l⁻¹ * s) := by group
  rw [e]
  exact (L ⊔ pCoreOf 2 (L ⊔ S)).mul_mem (Subgroup.mem_sup_left hl) hd'

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

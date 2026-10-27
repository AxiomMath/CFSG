module

public import CFSG.GH74.Generic.BProg.B1.Stage3aSD1
import CFSG.GH74.Generic.BProg.B1.JPrime
import CFSG.GH74.Generic.S3.PumpLift

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem bar_facts_of_involution {x y : G} (hx : orderOf x = 2) (hyC : y ∈ centralizer ({x} : Set G))
    (hy2 : orderOf y = 2) (hyx : y ≠ x) :
    bar x y ≠ 1 ∧ orderOf (bar x y) = 2 ∧ bar x y ∉ zpowers (xbar x) := by
  have h1 : bar x y = proj x ⟨y, hyC⟩ := bar_of_mem hyC
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hne : bar x y ≠ 1 := by
    intro h
    have := proj_odd x ⟨y, hyC⟩ (by rw [← h1]; exact h)
    rw [Subgroup.orderOf_mk, hy2] at this
    exact absurd this (by decide)
  have hb2 : orderOf (bar x y) = 2 := by
    refine orderOf_eq_prime ?_ hne
    rw [h1, ← map_pow]
    have : (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) ^ 2 = 1 :=
      Subtype.ext (by rw [← hy2]; exact pow_orderOf_eq_one y)
    rw [this, map_one]
  refine ⟨hne, hb2, fun hmem => ?_⟩
  rcases mem_zpowers_of_two (L5U5.orderOf_xbar hx) hmem with h | h
  · exact hne h
  · have hyy : y * y = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy2, pow_two] at this
    have hxx : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx, pow_two] at this
    exact hyx (eq_of_proj_eq_of_involutions hyC hxC hyy hxx
      (Subgroup.mem_centralizer_singleton_iff.1 hyC) (by rw [← h1]; exact h))

theorem isAdmPair_of_centralizing {F : Type} [Field F] [Finite F] {x y : G} {K A E₀ : Subgroup G}
    (hx : orderOf x = 2) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hxK : x ∉ K)
    (hY : Split3Like F (imgBar x K)) (hE₀K : E₀ ≤ K) (hAE : A = E₀ ⊔ zpowers x)
    (hE₀el : CFSG.IsElementaryAbelian 2 ↥E₀) (hE₀4 : Nat.card ↥E₀ = 4)
    (hyC : y ∈ centralizer ({x} : Set G)) (hy2 : orderOf y = 2) (hyx : y ≠ x)
    (hyK : ∀ k ∈ K, y * k = k * y) : IsAdmPair x K A y (imgBar x K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  obtain ⟨hyb1, hyb2, hybne⟩ := bar_facts_of_involution hx hyC hy2 hyx
  have hE₀nt : Nontrivial ↥E₀ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE₀4]; norm_num)
  obtain ⟨⟨e, heE⟩, he1⟩ := exists_ne (1 : ↥E₀)
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have heK : e ∈ K := hE₀K heE
  have heC : e ∈ centralizer ({x} : Set G) := hKC heK
  have he2sq : e ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E₀) e heE
  have he2 : orderOf e = 2 := orderOf_eq_prime he2sq he1'
  have hxe : x * e = e * x := (Subgroup.mem_centralizer_singleton_iff.1 heC).symm
  have hxene : x ≠ e := fun h => hxK (h ▸ heK)
  obtain ⟨hEcl, hEel, hE4⟩ := closure_pair_facts hx he2 hxe hxene
  set E : Subgroup G := closure ({x, e} : Set G) with hE
  have hEA : E ≤ A := by
    rw [hE, Subgroup.closure_le]
    intro a ha
    rcases ha with h | h
    · rw [h, hAE]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    · rw [Set.mem_singleton_iff.1 h, hAE]; exact Subgroup.mem_sup_left heE
  have hErank : 2 ≤ pRank 2 ↥E := by
    have := CFSG.pRank_eq_of_card_eq_pow (A := ↥E) Nat.one_lt_two (k := 2) (by rw [hE4]; norm_num)
    omega
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hEC : E ≤ centralizer ({x} : Set G) := by
    rw [hE, Subgroup.closure_le]
    intro a ha
    rcases ha with h | h
    · rw [h]; exact hxC
    · rw [Set.mem_singleton_iff.1 h]; exact heC
  have hKy : K ≤ centralizer ({y} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.2 (hyK k hk).symm
  have hEy : E ≤ centralizer ({y} : Set G) := by
    rw [hE, Subgroup.closure_le]
    intro a ha
    rcases ha with h | h
    · rw [h]; exact TwoThin.mem_centralizer_symm hyC
    · rw [Set.mem_singleton_iff.1 h]; exact hKy heK
  have hDE : closure ({x, y} : Set G) ≤ centralizer (E : Set G) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro g hg
    rcases ha with h | h
    · rw [h]; exact Subgroup.mem_centralizer_singleton_iff.1 (hEC hg)
    · rw [Set.mem_singleton_iff.1 h]; exact Subgroup.mem_centralizer_singleton_iff.1 (hEy hg)
  have hsetup : Setup1E x y E := by
    refine ⟨hyC, hy2, hybne, hEC, hEel, fun d hd => ?_, ?_⟩
    · exact Subgroup.centralizer_le_normalizer _ (hDE hd)
    · have : E ⊓ centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G) = E := by
        refine inf_eq_left.2 fun g hg => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        exact ((Subgroup.mem_centralizer_iff.1 (hDE hd)) g hg).symm
      rw [this]
      exact hErank
  have hKbarC : ∀ w ∈ imgBar x K, w * bar x y = bar x y * w := by
    intro w hw
    obtain ⟨g, hgK, rfl⟩ := mem_imgBar.1 hw
    rw [bar_of_mem hyC, ← map_mul, ← map_mul]
    exact congrArg (proj x) (Subtype.ext (hyK g hgK).symm)
  have hbarCent : imgBar x K ≤ centralizer ({bar x y} : Set (CentralizerBar x)) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.2 (hKbarC w hw)
  have hinfY : centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K = imgBar x K :=
    inf_eq_right.2 hbarCent
  obtain ⟨eK⟩ := hat_equiv_imgBar hK
  have hYq : IsQuasisimple ↥(imgBar x K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK (TwoThin.isQuasisimple_hat hK)
  have hYY : IsPCompIn 2 (imgBar x K) (imgBar x K) := by
    refine isPCompIn_of_subnormal_block le_rfl ?_ hYq
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.IsSubnormal.top
  have hYne : imgBar x K ≠ ⊥ := by
    intro hbot
    obtain ⟨a, b, hab⟩ := S45.exists_noncomm_of_isQuasisimple hYq
    apply hab
    have ha : a = 1 := Subtype.ext (by simpa [hbot] using a.2)
    rw [ha]; simp
  have hlayer : pLayerOf 2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) ≠ ⊥ := by
    rw [hinfY]
    intro hbot
    have h1 : imgBar x K ≤ pLayerOf 2 (imgBar x K) := le_sSup hYY
    rw [hbot, le_bot_iff] at h1
    exact hYne h1
  have hcompL : IsPCompIn 2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K)
      (imgBar x K) := by
    rw [hinfY]; exact hYY
  have hrel : SubtermRel (imgBar x K) (bar x y) (imgBar x K) := by
    refine ⟨hyb2, Subgroup.centralizer_le_normalizer _ ?_, Or.inl ⟨hcompL, fun z hz _ => Or.inr ?_⟩⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hKbarC w hw
    · have hsupC : (centralizer ((imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) ⊓
          (imgBar x K ⊔ zpowers (bar x y))) ⊔
          centralizer ((imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) ≤
          centralizer ((imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) :=
        sup_le inf_le_left le_rfl
      exact hsupC hz
  have hsubterm : IsSubtermPair x K y (imgBar x K) :=
    ⟨hyC, hy2, hybne, hrel, fun _ => ⟨hcompL, fun L' hL' _ =>
      Subgroup.card_le_of_le (hL'.1.trans inf_le_right)⟩⟩
  obtain ⟨hbmem, -, hb2⟩ := bar_facts hKC heK he2
  obtain ⟨L, hLY, hL, -⟩ := hY.exists_pair hbmem hb2
  have hbE : bar x e ∈ imgBar x E := by
    rw [bar_of_mem heC]
    exact mem_imgBar.2 ⟨⟨e, heC⟩, Subgroup.subset_closure (by simp), rfl⟩
  have hLE : L ≤ centralizer ((imgBar x E : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) := by
    set Q : Subgroup G := ((centralizer (L : Set (CentralizerBar x))).comap (proj x)).map
      (centralizer ({x} : Set G)).subtype with hQ
    have hxQ : x ∈ Q := ⟨⟨x, hxC⟩, by
      show proj x ⟨x, hxC⟩ ∈ centralizer (L : Set (CentralizerBar x))
      exact Subgroup.mem_centralizer_iff.2 fun l _ =>
        (Subgroup.mem_center_iff.1 (xbar_mem_center x)) l, rfl⟩
    have heQ : e ∈ Q := ⟨⟨e, heC⟩, by
      show proj x ⟨e, heC⟩ ∈ centralizer (L : Set (CentralizerBar x))
      rw [← bar_of_mem heC]
      exact Subgroup.mem_centralizer_iff.2 fun l hl =>
        Subgroup.mem_centralizer_singleton_iff.1 (hL.le_H hl).1, rfl⟩
    have hEQ : E ≤ Q := by
      rw [hE, Subgroup.closure_le]
      intro a ha
      rcases ha with h | h
      · rw [h]; exact hxQ
      · rw [Set.mem_singleton_iff.1 h]; exact heQ
    intro l hl
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    obtain ⟨c', hc', rfl⟩ := hg
    obtain ⟨c'', hc'', hcc⟩ := hEQ hc'
    have : c'' = c' := Subtype.ext hcc
    subst this
    exact (Subgroup.mem_centralizer_iff.1 hc'' l hl).symm
  set H : Subgroup (CentralizerBar x) :=
    centralizer ((imgBar x E : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) ⊓ imgBar x K
    with hH
  have hLH : L ≤ H := le_inf hLE hLY
  have hHC : H ≤ centralizer ({bar x e} : Set (CentralizerBar x)) ⊓ imgBar x K := by
    refine le_inf ?_ inf_le_right
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 hg.1 _ hbE).symm)
  have hLsubC : (L.subgroupOf (centralizer ({bar x e} : Set (CentralizerBar x)) ⊓ imgBar x K)).IsSubnormal :=
    hL.normal.isSubnormal
  have hLsubH : (L.subgroupOf H).IsSubnormal := TwoThin.isSubnormal_inf_subgroupOf hLsubC hHC
  have hLq : IsQuasisimple ↥L := hL.quasisimple
  have hpcLH : IsPCompIn 2 H L := isPCompIn_of_subnormal_block hLH hLsubH hLq
  have hLlay : L ≤ pLayerOf 2 H := le_sSup hpcLH
  have hlayH : pLayerOf 2 H ≤ H := sSup_le fun L' hL' => hL'.1
  have hLsubLay : (L.subgroupOf (pLayerOf 2 H)).IsSubnormal :=
    TwoThin.isSubnormal_inf_subgroupOf hLsubH hlayH
  have hcompI : IsPCompIn 2 (pLayerOf 2 H) L := isPCompIn_of_subnormal_block hLlay hLsubLay hLq
  have hyleaves : y ∈ normalizer (K : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hyK k hk).symm
  exact ⟨hsubterm, E, L, ⟨hEA, hEel, hErank⟩, Or.inl ⟨hsetup, hyleaves, hlayer, hcompL, hcompI⟩⟩

theorem S3PairData.pumpSS_of_allow {x : G} {K : Subgroup G} (h : S3PairData G x K) (hAllow : Stage2Allow)
    {y : G} (hy : y ∈ CxK x K) (hy2 : orderOf y = 2) (hyx : y ≠ x) :
    ⁅K, pPrimeCoreOf 2 (centralizer ({y} : Set G))⁆ = ⊥ := by
  have hZ := PilotS3.center_trivial_of_shape3 h.hKpc h.shape3
  have hxK : x ∉ K := not_mem_of_center_trivial h.x2 h.le hZ
  obtain ⟨A, hA⟩ := PilotS3.exists_source_of_shape3 h.x2 h.hKpc h.shape3
  rcases hA.2.2.2 with ⟨-, h1⟩ | ⟨E₀, hE₀K, hAE, -, hE₀el, hE₀4, -⟩
  · exact (not_qShape1_of_center_trivial h1 hZ).elim
  · obtain ⟨eK⟩ := hat_equiv_imgBar h.hKpc
    obtain ⟨F, _, _, P, _, ⟨e⟩, hP⟩ := exists_equiv_grpS3_of_qShape3 h.shape3
    have hY : Split3Like F (imgBar x K) :=
      Split3Like.of_equiv (eK.symm.trans e) hP (center_trivial_of_equiv eK hZ)
    have hyC : y ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.1 hy).1
    have hyK' : ∀ k ∈ K, y * k = k * y := fun k hk =>
      (Subgroup.mem_centralizer_iff.1 (h.cxk_le hy) k hk).symm
    have hAdm := isAdmPair_of_centralizing h.x2 h.hKpc hxK hY hE₀K hAE hE₀el hE₀4 hyC hy2 hyx hyK'
    have hss : NbhdSemisimple x y (imgBar x K) :=
      hAllow G h.hyp h.noAlt x K ⟨h.hJ, Or.inl h.hr⟩ A hA y (imgBar x K) hAdm
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hy2
      omega
    have hcomm := hss y (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) hy1
    have hKX : K ≤ (((imgBar x K).comap (proj x)).map (centralizer ({x} : Set G)).subtype) ⊓
        centralizer ({y} : Set G) := by
      intro k hk
      refine ⟨⟨⟨k, h.le hk⟩, mem_imgBar.2 ⟨⟨k, h.le hk⟩, hk, rfl⟩, rfl⟩, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hyK' k hk).symm
    have hKlift : K ≤ liftAt x y (imgBar x K) :=
      le_oPrimeResidualOf_of_isQuasisimple hKX h.hq
    exact le_bot_iff.1 ((Subgroup.commutator_mono hKlift le_rfl).trans hcomm.le)

end CFSG.GH74.Generic.BProg.B1

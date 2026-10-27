module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbAltFive
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
public import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive
public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocksAux
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGlue
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGroup
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideBlocksThree

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_barM_of {M X : Subgroup G} {p : ℕ} (hX : IsElemAbelian p X) :
    IsElemAbelian p (barM M X) := by
  have : IsMulCommutative X := hX.1
  refine CFSG.SectionRank.isElemAbelian_map ⟨inferInstance, fun x hx => Subtype.ext ?_⟩ _
  simpa using hX.2 x (Subgroup.mem_subgroupOf.mp hx)

theorem card_barM_of_elem {M X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXM : X ≤ M) (hX : IsElemAbelian p X) : Nat.card (barM M X) = Nat.card X :=
  card_barM_of_isPGroup hp hp2 hXM fun x => ⟨1, Subtype.ext (by simpa using hX.2 x x.2)⟩

omit [Finite G] in
theorem mem_normalizer_preimage {M : Subgroup G} {g : G} (hgM : g ∈ M)
    {Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hg : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ ∈ Subgroup.normalizer (Q : Set _)) :
    g ∈ Subgroup.normalizer
      (((Q.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype : Subgroup G) : Set G) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have key : ∀ (m : M), mk m ∈ Subgroup.normalizer (Q : Set _) →
      ∀ c ∈ (Q.comap mk).map M.subtype, (m : G) * c * (m : G)⁻¹ ∈ (Q.comap mk).map M.subtype := by
    rintro m hm _ ⟨c, hc, rfl⟩
    refine ⟨m * c * m⁻¹, ?_, by simp⟩
    show mk (m * c * m⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hm _).mp hc
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key ⟨g, hgM⟩ hg c, fun hc => ?_⟩
  have h1 := key (⟨g, hgM⟩)⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hg) _ hc
  simpa [mul_assoc] using h1

end Helpers

section Block

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G}

theorem D1PhaseThree.mem_sup_barM_of_mem_sup (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hx : x ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hxS : x ∈ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    x ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ⊔
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  set Lb := barM M L
  set Sb := barM M (pCoreOf 2 H)
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  have hLC : Lb ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Lb C hLC] at hx
  obtain ⟨l, hl, c, hc, rfl⟩ := hx
  obtain ⟨hSL, -⟩ := h.weakSBlock_asc81bHyp h86 hL
  have hSbL : Sb ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    barM_le_normalizer_barM hSL
  have hlP : l ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) := by
    refine stmtBlockInnerNormalizer_of h h84 h86 hD2 hL l hl fun s hs => ?_
    refine ⟨(l * c) * s * (l * c)⁻¹, (Subgroup.mem_normalizer_iff.mp hxS s).mp hs, fun y hy => ?_⟩
    have hy' : l⁻¹ * y * l ∈ Lb := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hl) hy) hl
    have hsy : s * (l⁻¹ * y * l) * s⁻¹ ∈ Lb := (Subgroup.mem_normalizer_iff.mp (hSbL hs) _).mp hy'
    have hc1 : c * (l⁻¹ * y * l) = (l⁻¹ * y * l) * c :=
      (Subgroup.mem_centralizer_iff.mp hc _ hy').symm
    have hc2 : c * (s * (l⁻¹ * y * l) * s⁻¹) = (s * (l⁻¹ * y * l) * s⁻¹) * c :=
      (Subgroup.mem_centralizer_iff.mp hc _ hsy).symm
    calc l * s * l⁻¹ * y * (l * s * l⁻¹)⁻¹
        = l * (s * (l⁻¹ * y * l) * s⁻¹) * l⁻¹ := by group
      _ = l * (c * (s * (l⁻¹ * y * l) * s⁻¹) * c⁻¹) * l⁻¹ := by
          rw [hc2, mul_inv_cancel_right]
      _ = l * (c * s * (c⁻¹ * (c * (l⁻¹ * y * l))) * s⁻¹ * c⁻¹) * l⁻¹ := by group
      _ = l * (c * s * (c⁻¹ * ((l⁻¹ * y * l) * c)) * s⁻¹ * c⁻¹) * l⁻¹ := by rw [hc1]
      _ = l * c * s * (l * c)⁻¹ * y * (l * c * s * (l * c)⁻¹)⁻¹ := by group
  exact Subgroup.mul_mem_sup hlP hc

theorem D1PhaseThree.barM_le_centralizer_of_irr (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hSch : KFactCatalogSchreier)
    (hKF : KFactBlockCentRankIb) (hK2 : KFactAltSixSevenAutFive)
    (hK3 : CitedBlockTransvectionCyclic) (hK4 : CitedBlockAltNormalizerSq) (hp5 : 5 ≤ p)
    (hcyc : ∀ Y' : Subgroup G, Y' ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) →
      ⁅Y', Y'⁆ = Y' → ∀ A : Subgroup G, A ≤ Y' → IsPGroup p A → IsCyclic A)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {X : Subgroup G} (hXK : X ≤ H ⊓ M) (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hXel : IsElemAbelian p X) (hXcard : Nat.card X = p ^ 2)
    {y : G} (hyK : y ∈ H ⊓ M) (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyX : y ∈ Subgroup.normalizer (X : Set G))
    (hirr : ∀ Y : Subgroup G, Y ≤ X → y ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X)
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hDp : ⁅D, D⁆ = D)
    (hDL : D ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hDS : D ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hDcyc : ∀ A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), A ≤ D → IsPGroup p A → IsCyclic A)
    (hDpart : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) → ⁅V, V⁆ = V →
      ∀ k : ℕ, p ^ k ∣ Nat.card V → p ^ k ∣ Nat.card D)
    {zb : ↥M ⧸ CFSG.pCore 2 ↥M} (hzD : zb ∈ D) (hzp : zb ^ p = 1)
    (hzC : zb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hZ : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → W = ⊥)
    (hXD : barM M X ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    barM M X ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  have hXM : X ≤ M := hXK.trans inf_le_right
  have hyM : y ∈ M := hyK.2
  have hXK' : X ≤ M ⊓ Subgroup.normalizer (S : Set G) := hKeq ▸ hXK
  have hyK' : y ∈ M ⊓ Subgroup.normalizer (S : Set G) := hKeq ▸ hyK
  have hXp : IsPGroup p X := fun x => ⟨1, Subtype.ext (by simpa using hXel.2 x x.2)⟩
  have hpp : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  set C := X ⊓ blockCentralizer M L with hC
  have hyC : y ∈ Subgroup.normalizer (C : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hyX, mem_normalizer_blockCentralizer hyM hyL⟩
  rcases hirr C inf_le_left hyC with hC0 | hCX
  swap
  · have hXC : X ≤ blockCentralizer M L := by
      rw [← hCX]
      exact inf_le_right
    exact (barM_mono hXC).trans (barM_blockCentralizer_le M L)
  exfalso
  have hbig : ¬ X ≤ C := by
    intro hXC
    rw [hC0, le_bot_iff] at hXC
    rw [hXC, Subgroup.card_bot] at hXcard
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  have hkey : ∀ U : Subgroup G, U ≤ X → y ∈ Subgroup.normalizer (U : Set G) →
      U.relIndex X ≤ p → X ≤ U := by
    intro U hUX hyU hUi
    rcases hirr U hUX hyU with hU | hU
    · rw [hU, Subgroup.relIndex_bot_left, hXcard] at hUi
      omega
    · exact hU.ge
  have hCi : C.relIndex X = p ^ 2 := by
    rw [hC0, Subgroup.relIndex_bot_left, hXcard]
  have hJ := perfectCyclicSylow_barM hL.le hp hcyc
  have hn1 := h.nineThree_not_one h85 hD2 hL
  rcases h.nineThree h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact hn1.1 h1
  ·
    have hMtop : M ≠ ⊤ := fun hM => h.not_le (hM ▸ le_top)
    have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
      (catalogSimpleSections_of_isKProper h.glob.kProper M hMtop).quotient _
    have hOut := isSolvable_outer_of_component hSch hL.component
      (hcat.isCatalogGroup_center_quotient hL.component)
    have hDsup : D ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) ⊔ Cb := fun d hd =>
      h.mem_sup_barM_of_mem_sup h84 h86 hD2 hL
        (perfect_le_sup_centralizer_of_outer hOut hDp hDL hd) (hDS hd)
    set Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := Lb ⊔ Cb with hQ
    have hyQ : mk ⟨y, hyM⟩ ∈ Subgroup.normalizer (Q : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      have hyLb : mk ⟨y, hyM⟩ ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        mem_normalizer_barM hyM hyL
      have hyCb : mk ⟨y, hyM⟩ ∈ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
          (Subgroup.normal_subgroupOf_centralizer_normalizer _) hyLb
      exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hyLb, hyCb⟩
    set XQ := X ⊓ (Q.comap mk).map M.subtype with hXQ
    have hyXQ : y ∈ Subgroup.normalizer (XQ : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hyX, mem_normalizer_preimage hyM hyQ⟩
    have hdisj : barM M X ⊓ Q = ⊥ ∨
        barM M X ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) ⊔ Cb := by
      rcases hirr XQ inf_le_left hyXQ with hXQ0 | hXQX
      · left
        rw [eq_bot_iff]
        rintro _ ⟨⟨⟨x, hxM⟩, hxX, rfl⟩, hxQ⟩
        have hxXQ : x ∈ XQ := ⟨Subgroup.mem_subgroupOf.mp hxX, ⟨x, hxM⟩, hxQ, rfl⟩
        rw [hXQ0, Subgroup.mem_bot] at hxXQ
        have : (⟨x, hxM⟩ : M) = 1 := Subtype.ext hxXQ
        rw [this, map_one]
        exact Subgroup.one_mem _
      · right
        rintro _ ⟨⟨x, hxM⟩, hxX, rfl⟩
        have hxXQ : x ∈ XQ := hXQX ▸ Subgroup.mem_subgroupOf.mp hxX
        obtain ⟨m, hm, hmx⟩ := hxXQ.2
        have hmeq : m = ⟨x, hxM⟩ := Subtype.ext hmx
        subst hmeq
        have hxS : x ∈ Subgroup.normalizer (S : Set G) :=
          (hXK' (Subgroup.mem_subgroupOf.mp hxX)).2
        exact h.mem_sup_barM_of_mem_sup h84 h86 hD2 hL hm (mem_normalizer_barM hxM hxS)
    have hEC : barM M X ⊓ Cb = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨⟨⟨x, hxM⟩, hxX, rfl⟩, hxC⟩
      have hxC' : x ∈ C := ⟨Subgroup.mem_subgroupOf.mp hxX, ⟨x, hxM⟩, hxC, rfl⟩
      rw [hC0, Subgroup.mem_bot] at hxC'
      have : (⟨x, hxM⟩ : M) = 1 := Subtype.ext hxC'
      rw [this, map_one]
      exact Subgroup.one_mem _
    exact hKF _ Lb (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) hL.component h2.1 h2.2.1
      (h.barM_ne_of_isWeakSBlock hL) (ne_inf_normalizer_of_nineThreeTwo h2 (hn1.2 h2)) p hp hp5
      D hDp hDsup hDcyc hDpart zb hzD hzp hzC
      (fun W _ hWp hWz => hZ W hWp hWz) (barM M X) (barM_le_normalizer_barM hXL) hXD
      (isElemAbelian_barM_of hXel) ((card_barM_of_elem hp hp2 hXM hXel).trans hXcard)
      hdisj hEC
  ·
    obtain ⟨u, hu, hcov⟩ := hK3 G M S L p h.isKGroup.1 h.asc81bHyp hL hn1.1
      (h.not_isSylowTwoOf_inf h85 hD2 hL) h3 hp hp2 hJ X hXK' hXL hXp
    have hZc : C ≤ Subgroup.centralizer (X : Set G) := fun c hc =>
      Subgroup.mem_centralizer_iff.mpr fun x hx => by
        have := hXel.1.is_comm.comm ⟨x, hx⟩ ⟨c, hc.1⟩
        exact congrArg Subtype.val this
    have hup : u ^ p ∈ C := by rw [hXel.2 u hu]; exact C.one_mem
    have hcov' : ∀ x ∈ X, ∃ k : ℕ, x * (u ^ k)⁻¹ ∈ C := by
      intro x hx
      obtain ⟨k, hk⟩ := hcov x hx
      exact ⟨k, ⟨X.mul_mem hx (X.inv_mem (X.pow_mem hu k)), hk⟩⟩
    have hle := relIndex_le_of_cyclic_mod_central hp.pos hu hZc hup hcov'
    omega
  ·
    have hle := hK2 _ Lb (barM M X) p hL.component (Or.inl h4.2.2.1) hp hp5
      (barM_le_normalizer_barM hXL) (isPGroup_barM hXp)
    rw [← relIndex_blockCentralizer_eq hXM, ← hC] at hle
    omega
  ·
    have hle := hK2 _ Lb (barM M X) p hL.component (Or.inr h5.2.1) hp hp5
      (barM_le_normalizer_barM hXL) (isPGroup_barM hXp)
    rw [← relIndex_blockCentralizer_eq hXM, ← hC] at hle
    omega
  all_goals
    have h678 : NineThreeSix M S L ∨ NineThreeSeven M S L ∨ NineThreeEight M S L := by
      first
      | exact Or.inl ‹_›
      | exact Or.inr (Or.inl ‹_›)
      | exact Or.inr (Or.inr ‹_›)
    obtain ⟨U₁, U₂, hU₁, hU₂, hU12, hi₁, hi₂, hnorm⟩ :=
      hK4 G M S L p h.isKGroup.1 h.asc81bHyp hL hn1.1 (h.not_isSylowTwoOf_inf h85 hD2 hL) h678
        hp hp2 hJ X hXK' hXL hXp
    obtain ⟨hyU₁, hyU₂⟩ := hnorm y hyK' hyL hyX
    exact hbig (le_inf le_rfl (le_trans (le_inf (hkey U₁ hU₁ hyU₁ hi₁) (hkey U₂ hU₂ hyU₂ hi₂))
      hU12))

end Block

end CFSG.AGLEmbedding

module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutBlocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SmallTypes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltRank
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NoOrderNine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairRankBook
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem one_le_pRank_three_of_dvd {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    (h : 3 ∣ Nat.card T) : 1 ≤ Open.pRank 3 T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h
  have hxo : orderOf (x : K) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hxp : (x : K) ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
  have hel : IsElemAbelian 3 (Subgroup.zpowers (x : K)) := by
    refine ⟨inferInstance, fun z hz => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt (Subgroup.zpowers_le.2 x.2) hel
    (by rw [Nat.card_zpowers, hxo, pow_one])

theorem barM_inf_centralizer_eq_bot_of_alt {M L : Subgroup G} {N : ℕ} (hN : 5 ≤ N)
    (e : ↥(barM M L) ≃* alternatingGroup (Fin N)) :
    barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ := by
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hperf : Group.IsPerfect (alternatingGroup (Fin N)) :=
    ⟨commutator_alternatingGroup_eq_top (by simpa using hN)⟩
  have hsimple : IsSimpleGroup (alternatingGroup (Fin N)) :=
    alternatingGroup.isSimpleGroup (by simpa using hN)
  have hnt : Nontrivial (alternatingGroup (Fin N)) := hsimple.toNontrivial
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzc : (⟨z, hz.1⟩ : ↥(barM M L)) ∈ Subgroup.center ↥(barM M L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hz.2) (g : _) g.2)
  have hz1 : e ⟨z, hz.1⟩ ∈ Subgroup.center (alternatingGroup (Fin N)) := by
    rw [Subgroup.mem_center_iff] at hzc ⊢
    intro g
    have := hzc (e.symm g)
    simpa using congrArg e this
  have hcen : Subgroup.center (alternatingGroup (Fin N)) = ⊥ := by
    rcases (Subgroup.center (alternatingGroup (Fin N))).normal_of_characteristic.eq_bot_or_eq_top
      with h | h
    · exact h
    · exfalso
      have hc : IsMulCommutative (alternatingGroup (Fin N)) := Subgroup.center_eq_top_iff.mp h
      exact Group.IsPerfect.not_isMulCommutative (G := alternatingGroup (Fin N)) hc
  rw [hcen, Subgroup.mem_bot] at hz1
  have : (⟨z, hz.1⟩ : ↥(barM M L)) = 1 := e.injective (by rw [hz1, map_one])
  exact congrArg Subtype.val this

section Cover

open CFSG.PreuniquenessRankFour.Helpers

theorem pRank_le_pRank_inf_centralizer_add_of_cover {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {A E : Subgroup X} (hEN : E ≤ Subgroup.normalizer (A : Set X))
    (hEA : E ≤ A ⊔ Subgroup.centralizer (A : Set X)) {k : ℕ}
    (hk : Open.pRank p (⊤ : Subgroup (↥A ⧸ Subgroup.center ↥A)) ≤ k) :
    Open.pRank p E ≤ Open.pRank p (E ⊓ Subgroup.centralizer (A : Set X)) + k := by
  set N := Subgroup.normalizer (A : Set X) with hNdef
  set R : Subgroup N := E.subgroupOf N with hR
  have hineq := pRank_le_pRank_inf_ker_add_pRank_map hp A.normalizerMonoidHom R
  have h₁ : Open.pRank p R = Open.pRank p E := by
    rw [← pRank_map_of_injective p hp N.subtype N.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hEN]
  have h₂ : Open.pRank p (R ⊓ A.normalizerMonoidHom.ker) ≤
      Open.pRank p (E ⊓ Subgroup.centralizer (A : Set X)) := by
    rw [Subgroup.normalizerMonoidHom_ker,
      ← pRank_map_of_injective p hp N.subtype N.subtype_injective]
    refine pRank_mono p hp ?_
    rintro _ ⟨x, ⟨hxR, hxC⟩, rfl⟩
    exact ⟨hxR, hxC⟩
  have hAN : A ≤ N := Subgroup.le_normalizer
  have hCN : Subgroup.centralizer (A : Set X) ≤ N := Subgroup.centralizer_le_normalizer _
  have hmap : R.map A.normalizerMonoidHom ≤ (MulAut.conj : A →* MulAut A).range := by
    rintro _ ⟨e, he, rfl⟩
    have heLC : (e : X) ∈ ((A ⊔ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := hEA he
    have hNC : N ≤ Subgroup.normalizer (Subgroup.centralizer (A : Set X) : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A (Subgroup.centralizer (A : Set X))
      (hAN.trans hNC)] at heLC
    obtain ⟨l, hl, c, hc, hlc⟩ := heLC
    have he' : e = ⟨l, hAN hl⟩ * ⟨c, hCN hc⟩ := Subtype.ext hlc.symm
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [he', map_mul]
    have hc1 : A.normalizerMonoidHom ⟨c, hCN hc⟩ = 1 := by
      rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
      exact hc
    rw [hc1, mul_one]
    ext a
    exact congrArg Subtype.val (show _ = _ from rfl)
  have hconj : Open.pRank p (MulAut.conj : A →* MulAut A).range ≤ k := by
    have hker : (MulAut.conj : A →* MulAut A).ker = Subgroup.center A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
      constructor
      · intro h b
        have := congrArg (fun φ : MulAut A => φ b) h
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        have h2 : a * b * a⁻¹ = b := this
        calc b * a = (a * b * a⁻¹) * a := by rw [h2]
          _ = a * b := by group
      · intro h
        apply MulEquiv.ext
        intro b
        simp only [MulAut.conj_apply, MulAut.one_apply]
        have := h b
        calc a * b * a⁻¹ = (b * a) * a⁻¹ := by rw [← this]
          _ = b := by group
    have e1 : ↥A ⧸ (MulAut.conj : A →* MulAut A).ker ≃* (MulAut.conj : A →* MulAut A).range :=
      QuotientGroup.quotientKerEquivRange _
    have e2 : ↥A ⧸ (MulAut.conj : A →* MulAut A).ker ≃* ↥A ⧸ Subgroup.center ↥A :=
      QuotientGroup.quotientMulEquivOfEq hker
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e1,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e2]
    exact hk
  have h₃ := pRank_mono p hp hmap
  omega

end Cover

omit [Finite G] in
theorem pRank_barM_le_of_alt [Finite G] {M L : Subgroup G} {N : ℕ}
    (e : ↥(barM M L) ≃* alternatingGroup (Fin N)) : Open.pRank 3 (barM M L) ≤ N / 3 := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barM M L),
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e]
  exact pRank_three_alternating_le

theorem rank_clause_nineThreeFive {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (h5 : NineThreeFive M L) (hVL : ∀ v ∈ blockV S L, ∀ l ∈ L, v * l * v⁻¹ ∈ L) {y : G}
    (hy : y ∈ blockV S L) :
    Open.pRank 3 L ≤ Open.pRank 3 (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) + 1 := by
  have h3 := three_dvd_card_inf_centralizer_of_nineThreeFive hL.le hL.perfect h5 hVL hy
  have h1 := one_le_pRank_three_of_dvd (T := (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G))
    h3
  obtain ⟨-, ⟨e⟩, -⟩ := h5
  have hr : Open.pRank 3 L = Open.pRank 3 (barM M L) :=
    (pRank_barM_eq Nat.prime_three (by norm_num) M L hL.le).symm
  have hle := pRank_barM_le_of_alt e
  omega

theorem eClause_nineThreeFour {M S L : Subgroup G} (h4 : NineThreeFour M S L)
    (E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (hEN : E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hEA : E ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    Open.pRank 3 E ≤
      Open.pRank 3 (E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) + 2 := by
  obtain ⟨-, -, ⟨e⟩, -⟩ := h4
  refine pRank_le_pRank_inf_centralizer_add_of_cover Nat.prime_three hEN hEA ?_
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e]
  have := pRank_three_alternating_le (N := 6)
  simpa using this

@[expose] def BlockRankClauses (M S L : Subgroup G) : Prop :=
  ClauseO M L ∧
    ((¬ 3 ∣ Nat.card (barM M L ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) ∧
      (∀ y ∈ Quasithin.omegaOneCenterOf S, y ≠ 1 →
        Open.pRank 3 L ≤ Open.pRank 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) + 1)) ∨
     (3 ∣ Nat.card (barM M L ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) ∧
      (∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        E ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        IsElemAbelian 3 E →
        Open.pRank 3 E ≤ Open.pRank 3 (E ⊓
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) + 2) ∧
      ∃ y ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L), y ^ 3 = 1 ∧
        y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))))

theorem blockRankClauses_nineThreeFive {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (h5 : NineThreeFive M L) (hVL : ∀ v ∈ blockV S L, ∀ l ∈ L, v * l * v⁻¹ ∈ L)
    (hV : ∀ y ∈ Quasithin.omegaOneCenterOf S, y ∈ blockV S L) : BlockRankClauses M S L := by
  refine ⟨clauseO_nineThreeFive h5, Or.inl ⟨?_, fun y hy _ => rank_clause_nineThreeFive hL h5 hVL
    (hV y hy)⟩⟩
  obtain ⟨-, ⟨e⟩, -⟩ := h5
  rw [barM_inf_centralizer_eq_bot_of_alt (by norm_num) e, Subgroup.card_bot]
  norm_num

theorem exists_order_three_noncentral_of_cover {M S L : Subgroup G} (hLM : L ≤ M)
    (h3L : BlockHasThree M S L)
    (hZ : Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) = 3)
    (hno9 : ∀ g : ↥(barM M L), orderOf g ≠ 9) :
    ∃ y ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨y, ⟨hyN, hyL⟩, hy3, l, hl, hyl⟩ := h3L
  set yb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hLM hyL⟩
  have hybP : yb ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hyN, hyL⟩)
  have hybL : yb ∈ barM M L := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL)
  have hybC : yb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun hc =>
    barM_not_commute hLM hyL hl hyl (Subgroup.mem_centralizer_iff.mp hc _
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl))).symm
  obtain ⟨e, he1, he2⟩ := exists_pow_not_mem_centralizer (isPGroup_zpowers_mk _ hy3) hybC
  set a := yb ^ 3 ^ e with ha
  refine ⟨a, Subgroup.pow_mem _ hybP _, ?_, he1⟩
  have haA : a ∈ barM M L := Subgroup.pow_mem _ hybL _
  have haZ : a ^ 3 ∈ barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    ⟨Subgroup.pow_mem _ haA _, he2⟩
  have h33 : (a ^ 3) ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := (barM M L ⊓ Subgroup.centralizer
      (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) (x := ⟨a ^ 3, haZ⟩)
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have h9 : a ^ 9 = 1 := by rw [← h33]; group
  have hdvd : orderOf a ∣ 9 := orderOf_dvd_of_pow_eq_one h9
  have hno : orderOf a ≠ 9 := by
    have := hno9 ⟨a, haA⟩
    rwa [Subgroup.orderOf_mk] at this
  have hne1 : orderOf a ≠ 1 := fun h => he1 (by
    have := orderOf_eq_one_iff.mp h
    rw [this]; exact Subgroup.one_mem _)
  have h3 : orderOf a = 3 := by
    have hd : orderOf a ∈ Nat.divisors 9 := by simp [hdvd]
    have : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [this] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h | h
    · exact absurd h hne1
    · exact h
    · exact absurd h hno
  rw [← h3]
  exact pow_orderOf_eq_one a

theorem card_inf_centralizer_eq_card_center {Q : Type*} [Group Q] (A : Subgroup Q) :
    Nat.card (A ⊓ Subgroup.centralizer (A : Set Q) : Subgroup Q) =
      Nat.card (Subgroup.center ↥A) := by
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp x.2.2) (g : Q) g.2)⟩
      invFun := fun z => ⟨z.1.1, z.1.2, Subgroup.mem_centralizer_iff.mpr fun h hh =>
        congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.2) ⟨h, hh⟩)⟩
      left_inv := fun x => rfl
      right_inv := fun z => rfl }

theorem blockRankClauses_nineThreeFour {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (h4 : NineThreeFour M S L) (h3L : BlockHasThree M S L) : BlockRankClauses M S L := by
  have hcard : Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) = 3 := by
    rw [card_inf_centralizer_eq_card_center]
    exact h4.2.1
  refine ⟨clauseO_nineThreeFour hL.le hL.perfect h4, Or.inr ⟨?_, ?_, ?_⟩⟩
  · rw [hcard]
  · intro E hEN hEA _
    exact eClause_nineThreeFour h4 E hEN hEA
  · obtain ⟨-, hZ, ⟨e⟩, -⟩ := h4
    exact exists_order_three_noncentral_of_cover hL.le h3L hcard
      (fun g => orderOf_ne_nine_tripleA6 hZ e g)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

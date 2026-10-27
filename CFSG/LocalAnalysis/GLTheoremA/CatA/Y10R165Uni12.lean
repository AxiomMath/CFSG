module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni9
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Concl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

structure SesqBlockData {n p : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) {N : ℕ}
    (A : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N))) (hp : p.Prime) where
  hpF : (p : F) ≠ 0
  hBsym : (idForm h N).IsSymm
  hBn : (idForm h N).SeparatingLeft
  A'' : Subgroup ((Fin N → F) ≃ₗ[F] (Fin N → F))
  [instFintype : Fintype A'']
  hA''le : A'' ≤ sesqSpecialUnitaryGroupLE (idForm h N)
  hA''e : IsElemAbelian p A''
  hmemA : ∀ x : ↥(sesqSpecialUnitaryGroupLE (idForm h N)),
    x ∈ A ↔ (x : (Fin N → F) ≃ₗ[F] (Fin N → F)) ∈ A''
  hB : InvariantSesq A'' (idForm h N)
  t : Hyperplane A'' p → ↥A''
  ht : ∀ D, t D ∉ D.1
  hbSU : ∀ D, blockEnd A'' hp hpF hA''e t ht D ∈ sesqSpecialUnitaryGroupLE (idForm h N)
  hblockA : ∀ D, blockEnd A'' hp hpF hA''e t ht D ∈ A''
  D₁ : Hyperplane A'' p
  D₂ : Hyperplane A'' p
  D₃ : Hyperplane A'' p
  hD12 : D₁ ≠ D₂
  hD13 : D₁ ≠ D₃
  hD23 : D₂ ≠ D₃
  hV1 : blockSpace A'' D₁.1 ≠ ⊥
  hV2 : blockSpace A'' D₂.1 ≠ ⊥
  hV3 : blockSpace A'' D₃.1 ≠ ⊥
  hdim2 : 2 ≤ Module.finrank F ↥(blockSpace A'' D₂.1)
  hdim3 : 2 ≤ Module.finrank F ↥(blockSpace A'' D₃.1)

@[reducible] instance instFintypeSubgroup {n p : ℕ} {F : Type} [Field F] [Finite F]
    {h : UnitaryFieldData 2 n F} {N : ℕ}
    {A : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N))} {hp : p.Prime}
    (S : SesqBlockData h A hp) : Fintype ↥S.A'' := S.instFintype

structure SesqTorusData {n p : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) {N : ℕ}
    (A : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N))) (hp : p.Prime) (q : ℕ)
    (S : SesqBlockData h A hp) where
  Fq : Subgroup ↥(pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
    (blockSpace S.A'' S.D₁.1))
  hFqe : IsElemAbelian q Fq
  hFq3 : 3 ≤ CFSG.Open.pRank q Fq
  x₁ : ↥(sesqSpecialUnitaryGroupLE (idForm h N))
  x₂ : ↥(sesqSpecialUnitaryGroupLE (idForm h N))
  x₃ : ↥(sesqSpecialUnitaryGroupLE (idForm h N))
  hx₁ : x₁ = ⟨blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₁, S.hbSU S.D₁⟩
  hx₂ : x₂ = ⟨blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₂, S.hbSU S.D₂⟩
  hx₃ : x₃ = ⟨blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₃, S.hbSU S.D₃⟩
  hx₁A : x₁ ∈ A
  hx₂A : x₂ ∈ A
  hord₁ : orderOf x₁ = p
  hord₃ : orderOf x₃ = p
  hx₃ne : x₃ ≠ 1
  hfour_one : n = 1 → 4 ≤ orderOf (-(2 ^ n) : ZMod p)
  hne1_two : Module.finrank F
    ↥(Submodule.orthogonalBilin (idForm h N) (blockSpace S.A'' S.D₁.1)) = 2 → n ≠ 1
  hne1_three : Module.finrank F
    ↥(Submodule.orthogonalBilin (idForm h N) (blockSpace S.A'' S.D₁.1)) = 3 → n ≠ 1
  h4perp : 4 ≤ Module.finrank F
    ↥(Submodule.orthogonalBilin (idForm h N) (blockSpace S.A'' S.D₁.1))

structure SesqJData {n p : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) {N : ℕ}
    (A : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N))) (hp : p.Prime) (q : ℕ)
    (S : SesqBlockData h A hp) (T : SesqTorusData h A hp q S) where
  hJle : pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1) ≤
    Subgroup.centralizer ({T.x₁} : Set ↥(sesqSpecialUnitaryGroupLE (idForm h N)))
  hzpow : Subgroup.centralizer (Subgroup.zpowers T.x₁ :
      Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) =
    Subgroup.centralizer ({T.x₁} : Set ↥(sesqSpecialUnitaryGroupLE (idForm h N)))
  hcompJ : GLAPComponent p
    (Subgroup.centralizer (Subgroup.zpowers T.x₁ :
      Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))))
    (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1))
  hAnormJ : A ≤ Subgroup.normalizer
    (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1) :
      Set ↥(sesqSpecialUnitaryGroupLE (idForm h N)))

structure SesqQData {n p : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) {N : ℕ}
    (A : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N))) (hp : p.Prime) (q : ℕ)
    (S : SesqBlockData h A hp) (T : SesqTorusData h A hp q S) where
  hQleH : pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1) ≤
    pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1) ⊓
      Subgroup.centralizer (Subgroup.closure ({T.x₁, T.x₂} :
        Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
        Set ↥(sesqSpecialUnitaryGroupLE (idForm h N)))
  hQn : ((pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1)).subgroupOf
      (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1) ⊓
        Subgroup.centralizer (Subgroup.closure ({T.x₁, T.x₂} :
          Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
          Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))))).Normal

section

variable {n p q : ℕ} {N : ℕ} {F : Type} [Field F] [Finite F]
  (h : UnitaryFieldData 2 n F)
  (A : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N)))

noncomputable def exists_sesqBlockData (hm0 : CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ≠ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hAe : IsElemAbelian p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N))) ≤
      CFSG.Open.pRank p A)
    (h3 : 3 ≤ CFSG.Open.pRank p A) : SesqBlockData h A hp := by
  classical
  suffices h : Nonempty (SesqBlockData h A hp) from Classical.choice h
  haveI : Fact p.Prime := ⟨hp⟩
  have hpF : (p : F) ≠ 0 := by
    intro h0
    haveI : CharP F 2 := h.charP
    have hpdiv : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hpdiv).symm
  have hpq : ¬ p ∣ 2 ^ n + 1 :=
    fun hd => hm0 ((CFSG.LocalAnalysis.GLTheoremA.rk2Ord_eq_two_iff hp hp2).2 hd)
  have hBsym : (idForm h N).IsSymm := idForm_isSymm h N
  have hBn : (idForm h N).SeparatingLeft := idForm_separatingLeft h N
  have hd2 : 2 ≤ orderOf (-(2 ^ n) : ZMod p) := two_le_orderOf_neg_two_pow hp hp2 hpq
  set A'' : Subgroup ((Fin N → F) ≃ₗ[F] (Fin N → F)) :=
    A.map (sesqSpecialUnitaryGroupLE (idForm h N)).subtype with hA''def
  have hA''le : A'' ≤ sesqSpecialUnitaryGroupLE (idForm h N) := Subgroup.map_subtype_le _
  have hA''e : IsElemAbelian p A'' := CFSG.SectionRank.isElemAbelian_map hAe _
  have hmemA : ∀ x : ↥(sesqSpecialUnitaryGroupLE (idForm h N)), x ∈ A ↔
      (x : (Fin N → F) ≃ₗ[F] (Fin N → F)) ∈ A'' := by
    intro x
    constructor
    · intro hx; exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
  have hcardA'' : Nat.card A'' = p ^ CFSG.Open.pRank p A := by
    rw [Subgroup.card_map_of_injective (f := (sesqSpecialUnitaryGroupLE (idForm h N)).subtype)
      Subtype.coe_injective,
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hAe]
  have hpRankA'' : CFSG.Open.pRank p A'' = CFSG.Open.pRank p A :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) A'').trans
      ((CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := p) hp.one_lt
        (Subgroup.equivMapOfInjective A (sesqSpecialUnitaryGroupLE (idForm h N)).subtype
          Subtype.coe_injective)).symm.trans
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) A).symm)
  have hmaxA : CFSG.Open.pRank p (sesqSpecialUnitaryGroupLE (idForm h N)) ≤ CFSG.Open.pRank p A :=
    (le_of_eq (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p)
      (sesqSpecialUnitaryGroupLE (idForm h N)))).trans hmax
  have hmax'' :
      CFSG.Open.pRank p (sesqSpecialUnitaryGroupLE (idForm h N)) ≤ CFSG.Open.pRank p A'' :=
    hmaxA.trans (le_of_eq hpRankA''.symm)
  haveI : Fintype A'' := Fintype.ofFinite _
  obtain ⟨t, ht⟩ := exists_blockRep (A := A'') hp
  have hB : InvariantSesq A'' (idForm h N) := fun a u v =>
    ((mem_sesqSpecialUnitaryGroupLE (B := idForm h N)).mp (hA''le a.2)).1 u v
  have hbSU : ∀ D, blockEnd A'' hp hpF hA''e t ht D ∈
      sesqSpecialUnitaryGroupLE (idForm h N) := fun D =>
    blockEnd_mem_sesqSpecialUnitaryGroupLE (h := h) A'' hp hpF hA''e hB hBsym hBn hpq t ht D
  have hblockA : ∀ D, blockEnd A'' hp hpF hA''e t ht D ∈ A'' := fun D =>
    blockEnd_mem_of_pRank_le A'' hp hpF hA''e t ht hA''le hmax'' hbSU D
  obtain ⟨D₁, D₂, D₃, hD12, hD13, hD23, hV1, hV2, hV3⟩ :=
    exists_three_ne_bot_blockSpace A'' hp hpF hA''e t ht hcardA'' hA''le hmaxA hbSU h3
  have hdimBlock : ∀ (D : Hyperplane A'' p), blockSpace A'' D.1 ≠ ⊥ →
      2 ≤ Module.finrank F ↥(blockSpace A'' D.1) := by
    intro D hD
    exact le_trans hd2 (orderOf_neg_le_finrank_blockSpace (h := h) A'' hp hpF hA''e hB hBsym hBn
      hp2 t ht hD)
  exact ⟨⟨hpF, hBsym, hBn, A'', hA''le, hA''e, hmemA, hB, t, ht, hbSU, hblockA,
    D₁, D₂, D₃, hD12, hD13, hD23, hV1, hV2, hV3,
    hdimBlock D₂ hV2, hdimBlock D₃ hV3⟩⟩

theorem blockSpace_le_orthogonalBilin_of_ne (hp : p.Prime) (S : SesqBlockData h A hp) :
    blockSpace S.A'' S.D₂.1 ≤
      Submodule.orthogonalBilin (idForm h N) (blockSpace S.A'' S.D₁.1) := by
  intro v hv
  rw [Submodule.mem_orthogonalBilin]
  intro u hu
  exact blockSpace_sesq_orthogonal S.A'' hp S.hpF S.hA''e (idForm h N) S.hB S.hD12 hu hv

theorem four_le_finrank_orthogonalBilin_blockSpace (hp : p.Prime)
    (S : SesqBlockData h A hp) :
    4 ≤ Module.finrank F
      ↥(Submodule.orthogonalBilin (idForm h N) (blockSpace S.A'' S.D₁.1)) := by
  classical
  have hsumBlock :=
    OmEngine.finrank_eq_finrank_fixedSpaceOf_add_sum_blockSpace S.A'' hp S.hpF S.hA''e
  have htriple : Module.finrank F ↥(blockSpace S.A'' S.D₁.1) +
      Module.finrank F ↥(blockSpace S.A'' S.D₂.1) +
      Module.finrank F ↥(blockSpace S.A'' S.D₃.1) ≤ Module.finrank F (Fin N → F) := by
    have hle : (∑ D ∈ ({S.D₁, S.D₂, S.D₃} : Finset (Hyperplane S.A'' p)),
        Module.finrank F ↥(blockSpace S.A'' D.1)) ≤
        ∑ D : Hyperplane S.A'' p, Module.finrank F ↥(blockSpace S.A'' D.1) :=
      Finset.sum_le_univ_sum_of_nonneg
        (f := fun D : Hyperplane S.A'' p => Module.finrank F ↥(blockSpace S.A'' D.1))
        (s := ({S.D₁, S.D₂, S.D₃} : Finset (Hyperplane S.A'' p))) (fun _ => Nat.zero_le _)
    have h3sum : (∑ D ∈ ({S.D₁, S.D₂, S.D₃} : Finset (Hyperplane S.A'' p)),
        Module.finrank F ↥(blockSpace S.A'' D.1)) =
        Module.finrank F ↥(blockSpace S.A'' S.D₁.1) +
          Module.finrank F ↥(blockSpace S.A'' S.D₂.1) +
          Module.finrank F ↥(blockSpace S.A'' S.D₃.1) := by
      rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
      · omega
      · simp [S.hD23]
      · simp [S.hD12, S.hD13]
    rw [← h3sum]
    exact hle.trans (by rw [hsumBlock]; omega)
  have hfinV : Module.finrank F (Fin N → F) = N := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  have hperp1 : Module.finrank F
      ↥(Submodule.orthogonalBilin (idForm h N) (blockSpace S.A'' S.D₁.1)) =
      Module.finrank F (Fin N → F) - Module.finrank F ↥(blockSpace S.A'' S.D₁.1) := by
    have hdim := finrank_ker_projBlock_add_finrank_blockSpace S.A'' hp S.hpF S.hA''e S.D₁
    rw [← orthogonalBilin_blockSpace_eq_ker S.A'' hp S.hpF S.hA''e S.hB S.hBsym.isRefl S.hBn
      S.D₁] at hdim
    omega
  have hdim2 := S.hdim2
  have hdim3 := S.hdim3
  rw [hperp1, hfinV]
  omega

noncomputable def exists_sesqTorusData (hm0 : CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ≠ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2) (hqd : q ∣ 2 ^ n + 1)
    (S : SesqBlockData h A hp)
    (hV2le : blockSpace S.A'' S.D₂.1 ≤
      Submodule.orthogonalBilin (idForm h N) (blockSpace S.A'' S.D₁.1))
    (h4perp : 4 ≤ Module.finrank F
      ↥(Submodule.orthogonalBilin (idForm h N) (blockSpace S.A'' S.D₁.1))) :
    SesqTorusData h A hp q S := by
  classical
  suffices h : Nonempty (SesqTorusData h A hp q S) from Classical.choice h
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Fq, hFqe, hFq3⟩ := exists_elemAbelian_qtorsion_pointwiseStab_blockSpace (h := h)
    S.A'' hp S.hpF S.hA''e S.hB S.hBsym S.hBn S.D₁ hq hq2 hqd h4perp
  set x₁ : ↥(sesqSpecialUnitaryGroupLE (idForm h N)) :=
    ⟨blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₁, S.hbSU S.D₁⟩ with hx₁
  set x₂ : ↥(sesqSpecialUnitaryGroupLE (idForm h N)) :=
    ⟨blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₂, S.hbSU S.D₂⟩ with hx₂
  set x₃ : ↥(sesqSpecialUnitaryGroupLE (idForm h N)) :=
    ⟨blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₃, S.hbSU S.D₃⟩ with hx₃
  have hx₁A : x₁ ∈ A := (S.hmemA x₁).mpr (by rw [hx₁]; exact S.hblockA S.D₁)
  have hx₂A : x₂ ∈ A := (S.hmemA x₂).mpr (by rw [hx₂]; exact S.hblockA S.D₂)
  have hord₁ : orderOf x₁ = p := by
    rw [hx₁, Subgroup.orderOf_mk,
      orderOf_blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.hV1]
  have hord₃ : orderOf x₃ = p := by
    rw [hx₃, Subgroup.orderOf_mk,
      orderOf_blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.hV3]
  have hx₃ne : x₃ ≠ 1 := by
    intro h₁
    rw [h₁, orderOf_one] at hord₃
    exact hp.ne_one hord₃.symm
  have hfour_one : n = 1 → 4 ≤ orderOf (-(2 ^ n) : ZMod p) := by
    intro hn1
    have hp3 : ¬ p ∣ 3 := by
      intro hd
      have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd
      refine hm0 ?_
      rw [hp3', hn1]
      exact
        (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_one_eq_two_iff (by norm_num) (by norm_num)).mpr rfl
    rw [hn1]
    simpa using four_le_orderOf_neg_two hp hp2 hp3
  have hne1_two : Module.finrank F
      ↥(Submodule.orthogonalBilin (idForm h N) (blockSpace S.A'' S.D₁.1)) = 2 → n ≠ 1 := by
    intro h2 hn1
    have h4 : 4 ≤ Module.finrank F ↥(blockSpace S.A'' S.D₂.1) :=
      le_trans (hfour_one hn1) (orderOf_neg_le_finrank_blockSpace (h := h) S.A'' hp S.hpF
        S.hA''e S.hB S.hBsym S.hBn hp2 S.t S.ht S.hV2)
    have hle := Submodule.finrank_mono hV2le
    omega
  have hne1_three : Module.finrank F
      ↥(Submodule.orthogonalBilin (idForm h N) (blockSpace S.A'' S.D₁.1)) = 3 → n ≠ 1 := by
    intro h3' hn1
    have h4 : 4 ≤ Module.finrank F ↥(blockSpace S.A'' S.D₂.1) :=
      le_trans (hfour_one hn1) (orderOf_neg_le_finrank_blockSpace (h := h) S.A'' hp S.hpF
        S.hA''e S.hB S.hBsym S.hBn hp2 S.t S.ht S.hV2)
    have hle := Submodule.finrank_mono hV2le
    omega
  exact ⟨⟨Fq, hFqe, hFq3, x₁, x₂, x₃, hx₁, hx₂, hx₃, hx₁A, hx₂A, hord₁, hord₃, hx₃ne,
    hfour_one, hne1_two, hne1_three, h4perp⟩⟩

end

end CFSG.LocalAnalysis.GLTheoremA.Y10F

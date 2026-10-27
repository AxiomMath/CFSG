module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.FlagStabPlusLink
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD.Levi
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusBase

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin Matrix
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus

variable {n : ℕ} {F : Type} [Field F]

theorem nodeCowt_root (_hn : 2 ≤ n) (k : Fin n) :
    nodeCowt n k (rootIdxD n k) = 1 ∧
      boolSign (!rootSignD n k) * nodeCowt n k (rootIdxD' n k) ≤ 0 := by
  have hk := k.isLt
  by_cases h : k.val + 1 < n
  · rw [rootIdxD_of_lt n h, rootIdxD'_of_lt n h, rootSignD_of_lt n h]
    simp only [Bool.not_false, boolSign_true, one_mul]
    unfold nodeCowt
    constructor <;> split_ifs <;> simp_all <;> omega
  · rw [rootSignD_of_not_lt n h]
    simp only [Bool.not_true, boolSign_false]
    unfold nodeCowt
    have h1 := val_rootIdxD_of_not_lt n h
    have h2 := val_rootIdxD'_of_not_lt n h
    constructor <;> split_ifs <;> simp_all <;> omega

theorem negRootD_not_stab (hn : 3 ≤ n) (k : Fin n) :
    ¬ ∀ w ∈ flagSpace F (nodeCowt n k),
      spinAction (quadPlus n F) (negRootD F hn k (.ofAdd 1)) w ∈ flagSpace F (nodeCowt n k) := by
  intro hst
  obtain ⟨hb, ha⟩ := nodeCowt_root (n := n) (by omega) k
  set b : Fin n ⊕ Fin n := flagIdx (rootIdxD n k) true with hbdef
  set a : Fin n ⊕ Fin n := flagIdx (rootIdxD' n k) (!rootSignD n k) with hadef
  have hw : (Pi.single b (1 : F) : Fin n ⊕ Fin n → F) ∈ flagSpace F (nodeCowt n k) := by
    intro u hu
    have : u = b := by
      by_contra hne
      exact hu (by simp [hne])
    subst this
    rw [hbdef, flagWt_idx, boolSign_true, hb]
    norm_num
  have h1 := hst _ hw
  have hab : a ≠ b := by
    intro h
    have := congrArg (fun u : Fin n ⊕ Fin n => flagWt (nodeCowt n k) u) h
    simp only [hadef, hbdef, flagWt_idx] at this
    rw [boolSign_true, hb] at this
    linarith
  have hentry : spinAction (quadPlus n F) (negRootD F hn k (.ofAdd 1)) (Pi.single b 1) a = 1 := by
    rw [← spinMat_apply]
    unfold negRootD
    rw [(isCoord_plusFrame_flag (K := F) hn).spinMat_longRoot
      (rootIdxD_ne n (by omega) k).symm (!rootSignD n k) false (1 : F) a b]
    have hc1 : a = flagIdx (rootIdxD' n k) (!rootSignD n k) ∧ b = flagIdx (rootIdxD n k) (!false) :=
      ⟨rfl, rfl⟩
    have hc2 : ¬ (a = flagIdx (rootIdxD n k) false ∧ b = flagIdx (rootIdxD' n k) (!(!rootSignD n k))) := by
      rintro ⟨h2, -⟩
      have := congrArg (fun u : Fin n ⊕ Fin n => u) h2
      cases hs : rootSignD n k <;> simp [hadef, flagIdx, hs] at h2 <;>
        exact absurd h2 (by
          have := rootIdxD_ne n (by omega) k
          intro h3
          exact this (by simpa using h3.symm))
    rw [ite_eq_left hc1, ite_eq_right hc2, Matrix.one_apply_ne hab]
    simp
  have h2 := h1 a (by rw [hentry]; exact one_ne_zero)
  have := ha
  rw [hadef, flagWt_idx] at h2
  omega

@[expose] def stabW (n : ℕ) (F : Type) [Field F] (k : Fin n) : Subgroup ↥(Om n F) where
  carrier := {A | ∀ w, ((A : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ w ∈
      flagSpace F (nodeCowt n k) ↔ w ∈ flagSpace F (nodeCowt n k)}
  mul_mem' := by
    intro A B hA hB w
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
  one_mem' := by
    intro w
    simp
  inv_mem' := by
    intro A hA w
    rw [← hA]
    simp only [Subgroup.coe_inv, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]

@[expose] def JK (n : ℕ) (F : Type) [Field F] (K : Set (Fin n)) : Subgroup ↥(Om n F) :=
  ⨅ k ∈ K, stabW n F k

theorem mem_JK {K : Set (Fin n)} {A : ↥(Om n F)} :
    A ∈ JK n F K ↔ ∀ k ∈ K, A ∈ stabW n F k := by
  simp [JK]

section Main

variable [Finite F] [CharP F 2]

theorem exists_flag_data (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer (T : Set Y) ≤ J) (hJ : J ≠ ⊤) :
    ∃ (θ : Y ≃* ↥(Om n F)) (K : Set (Fin n)), K.Nonempty ∧
      J.map θ.toMonoidHom = JK n F K := by
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have hB := borelQuotient_spinPlus hn3 e
  set π := e.symm.toMonoidHom.comp (spinToStatedProj (quadPlus n F)
        (range_spinMatrix_quadPlus hn3)) with hπ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (posUnipotent (plusDatum n F hn3)) :=
    isPGroup_iSup_pos hB.extras hB.pGroup
  have hidx : ¬ 2 ∣ ((posUnipotent (plusDatum n F hn3)).map π).index := fun hd =>
    hB.not_dvd_index (hd.trans (Subgroup.index_map_dvd _ hB.surj))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y ((hU2.map π).toSylow hidx) T
  set π' : spinGroup (quadPlus n F) →* Y := (MulAut.conj g).toMonoidHom.comp π with hπ'
  have hπ'surj : Function.Surjective π' := (MulAut.conj g).surjective.comp hB.surj
  have hker : π'.ker = π.ker := by
    ext z
    simp [hπ', MonoidHom.mem_ker]
  have hT : (T : Subgroup Y) = (posUnipotent (plusDatum n F hn3)).map π' := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    change Subgroup.map (MulAut.conj g).toMonoidHom ((posUnipotent _).map π) = _
    rw [Subgroup.map_map]
  have hQ : BorelQuotient (plusDatum n F hn3) (weylD F hn3) (fun k => (torusD F hn3 k).range) π'
      (Nat.card F - 1) :=
    { ct := hB.ct, extras := hB.extras, pGroup := hB.pGroup, surj := hπ'surj, odd := hB.odd
      torus_pow := hB.torus_pow
      ker_central := fun z hz => hB.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => hB.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel (plusDatum n F hn3) (fun k => (torusD F hn3 k).range)).map π' ≤ J := by
    rw [← hNπ]; exact hNJ
  have hBA : borel (plusDatum n F hn3) (fun k => (torusD F hn3 k).range) ≤ J.comap π' :=
    fun b hb => hBJ ⟨b, hb, rfl⟩
  have hJeq := eq_map_borel_sup_of_le hQ.ct hQ.extras hπ'surj hBJ
  obtain ⟨k0, hk0⟩ := CFSG.AGLEmbedding.LieOut.exists_node_not_mem_negIndices hQ hBJ hJ
  obtain ⟨Ag, hAg⟩ := QuotientGroup.mk_surjective (e g)
  have hπx : ∀ x : spinGroup (quadPlus n F), e (π' x) =
      (QuotientGroup.mk (Ag * ResidualD.genΩ hn3 x * Ag⁻¹) :
        StatedProj (StatedOmega (StatedQuadPlus n F))) := by
    intro x
    have hπk : e (π x) = (QuotientGroup.mk (ResidualD.genΩ hn3 x) :
        StatedProj (StatedOmega (StatedQuadPlus n F))) := by
      rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        spinToStatedProj_apply]
      rfl
    rw [hπ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul,
      map_inv, hπk, ← hAg, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  set I : Set (Fin n) := negIndices (plusDatum n F hn3) (J.comap π') with hI
  set K : Set (Fin n) := {k | k ∉ I} with hKdef
  have hKne : K.Nonempty := ⟨k0, hk0⟩
  set stabK : Subgroup (spinGroup (quadPlus n F)) :=
    ⨅ k ∈ K, stabSub (quadPlus n F) (flagSpace F (nodeCowt n k)) with hstabK
  have hmem_stabK : ∀ s : spinGroup (quadPlus n F), s ∈ stabK ↔
      ∀ k ∈ K, ∀ w ∈ flagSpace F (nodeCowt n k),
        spinAction (quadPlus n F) s w ∈ flagSpace F (nodeCowt n k) := by
    intro s
    simp [hstabK, mem_stabSub]
  have hbor : borel (plusDatum n F hn3) (fun k => (torusD F hn3 k).range) ≤ stabK := by
    refine le_iInf₂ fun k _ => ?_
    exact borel_le_stabSub (K := F) hn3 (nodeCowt n k) (fun i j hij => nodeCowt_dom n k i j hij)
  have hJle : J ≤ stabK.map π' := by
    refine hJeq.le.trans (sup_le (Subgroup.map_mono hbor) (iSup₂_le fun i hi =>
      Subgroup.map_mono ?_))
    refine le_iInf₂ fun k hk => ?_
    have hik : i ≠ k := fun h => hk (h ▸ hi)
    exact rankOneD_le_stabSub (K := F) hn3 (nodeCowt n k) i
      (nodeCowt_node n k i hik (by omega))
  have hPle : stabK.map π' ≤ J := by
    have hBP : (borel (plusDatum n F hn3) (fun k => (torusD F hn3 k).range)).map π' ≤
        stabK.map π' := Subgroup.map_mono hbor
    have hPeq := eq_map_borel_sup_of_le hQ.ct hQ.extras hπ'surj hBP
    rw [hPeq]
    refine sup_le hBJ (iSup₂_le fun i hi => ?_)
    have hiI : i ∈ I := by
      by_contra hiI
      have hiK : i ∈ K := hiI
      have hBP' : borel (plusDatum n F hn3) (fun k => (torusD F hn3 k).range) ≤
          (stabK.map π').comap π' := fun b hb => hBP ⟨b, hb, rfl⟩
      have hneg : negRootD F hn3 i (.ofAdd 1) ∈
          rankOne (plusDatum n F hn3).rootGroup i := by
        change _ ∈ plusRootGroup n F hn3 (Pi.single i 1) ⊔ plusRootGroup n F hn3 (-Pi.single i 1)
        refine Subgroup.mem_sup_right ?_
        have hh := plusRootGroup_neg_single (K := F) hn3 i
        exact (SetLike.ext_iff.mp hh _).mpr ⟨_, rfl⟩
      have hx : π' (negRootD F hn3 i (.ofAdd 1)) ∈ stabK.map π' :=
        rankOne_le_of_mem_negIndices hBP' hi hneg
      obtain ⟨s, hs, hsx⟩ := hx
      have hz : s⁻¹ * negRootD F hn3 i (.ofAdd 1) ∈ π'.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hsx, inv_mul_cancel]
      rw [hker, hπ, MonoidHom.mem_ker] at hz
      have hz1 : (spinMatrix (quadPlus n F) (s⁻¹ * negRootD F hn3 i (.ofAdd 1)) :
          GL (Fin n ⊕ Fin n) F) = 1 := by
        have h1 : e.symm (spinToStatedProj (quadPlus n F) (range_spinMatrix_quadPlus hn3)
            (s⁻¹ * negRootD F hn3 i (.ofAdd 1))) = 1 := hz
        have h2 := (MulEquiv.map_eq_one_iff e.symm).1 h1
        rw [spinToStatedProj_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
        exact congrArg Subtype.val (ResidualD.eq_one_of_mem_statedScalars_plus (by omega)
          (A := ⟨spinMatrix (quadPlus n F) (s⁻¹ * negRootD F hn3 i (.ofAdd 1)),
            spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadPlus hn3) _⟩) h2)
      have hx_eq : spinMatrix (quadPlus n F) (negRootD F hn3 i (.ofAdd 1)) =
          spinMatrix (quadPlus n F) s := by
        have : negRootD F hn3 i (.ofAdd 1) = s * (s⁻¹ * negRootD F hn3 i (.ofAdd 1)) := by group
        rw [this, map_mul, hz1, mul_one]
      refine negRootD_not_stab (F := F) hn3 i (fun w hw => ?_)
      rw [← spinMatrix_mulVec, hx_eq, spinMatrix_mulVec]
      exact (hmem_stabK s).1 hs i hiK w hw
    exact (Subgroup.map_mono (rankOne_le_of_mem_negIndices hBA hiI)).trans
      (Subgroup.map_comap_le _ _)
  have hJeqP : J = stabK.map π' := le_antisymm hJle hPle
  let Θ : ↥(Om n F) →* Y :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (MulAut.conj Ag).toMonoidHom)
  have hΘ : ∀ A, Θ A = e.symm (QuotientGroup.mk (Ag * A * Ag⁻¹)) := fun _ => rfl
  have hΘinj : Function.Injective Θ := by
    intro x y hxy
    rw [hΘ, hΘ] at hxy
    have h1 := e.symm.injective hxy
    have h2 := ResidualD.eq_of_mk_eq_plus (n := n) (F := F) (by omega) h1
    simpa using h2
  have hΘsurj : Function.Surjective Θ := by
    intro y
    obtain ⟨A', hA'⟩ := QuotientGroup.mk_surjective (e y)
    refine ⟨Ag⁻¹ * A' * Ag, ?_⟩
    rw [hΘ]
    have : Ag * (Ag⁻¹ * A' * Ag) * Ag⁻¹ = A' := by group
    rw [this, hA']
    simp
  have hΘπ : ∀ x : spinGroup (quadPlus n F), π' x = Θ (ResidualD.genΩ hn3 x) := by
    intro x
    rw [hΘ]
    apply e.injective
    rw [hπx x, MulEquiv.apply_symm_apply]
  let θ : Y ≃* ↥(Om n F) := (MulEquiv.ofBijective Θ ⟨hΘinj, hΘsurj⟩).symm
  have hθsymm : ∀ A, θ.symm A = Θ A := fun _ => rfl
  refine ⟨θ, K, hKne, ?_⟩
  ext A
  rw [Subgroup.mem_map_equiv, hθsymm, mem_JK]
  constructor
  · intro hA
    rw [hJeqP] at hA
    obtain ⟨s, hs, hsA⟩ := hA
    have hAs : A = ResidualD.genΩ hn3 s := hΘinj (by rw [← hsA, hΘπ])
    have hsinv := inv_mem hs
    intro k hk w
    constructor
    · intro hw
      have h1 := (hmem_stabK s⁻¹).1 hsinv k hk _ hw
      have hAw : ((A : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ w =
          spinAction (quadPlus n F) s w := by
        rw [hAs]
        exact spinMatrix_mulVec (Q := quadPlus n F) s w
      have hinv : spinAction (quadPlus n F) s⁻¹ (spinAction (quadPlus n F) s w) = w := by
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      rw [hAw, hinv] at h1
      exact h1
    · intro hw
      have h1 := (hmem_stabK s).1 hs k hk w hw
      rw [← spinMatrix_mulVec] at h1
      rw [hAs]
      exact h1
  · intro hA
    have hmemA : (A : GL (Fin n ⊕ Fin n) F) ∈ (spinMatrix (quadPlus n F)).range := by
      rw [range_spinMatrix_quadPlus hn3]; exact A.2
    obtain ⟨s, hsA⟩ := hmemA
    have hs : s ∈ stabK := by
      rw [hmem_stabK]
      intro k hk w hw
      rw [← spinMatrix_mulVec, hsA]
      exact (hA k hk w).2 hw
    rw [hJeqP]
    refine ⟨s, hs, ?_⟩
    rw [hΘπ]
    congr 1
    exact Subtype.ext hsA

end Main

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

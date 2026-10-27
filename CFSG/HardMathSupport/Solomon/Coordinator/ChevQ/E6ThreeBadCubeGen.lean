module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2Closure
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadCube
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerAbs
public import CFSG.RankThree.Chevalley.SteinbergBID4Triality

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.CatLeafProof (weylWordElt)
open CFSG.RankThree.Chevalley (wordAct wordSign wordRep wordRep_conj_pinnedX isRoot_wordAct)

theorem notMem_closure_pair_of_card {Γ : Type*} [Group Γ] {a b c : Γ} (hab : Commute a b)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hcard : Nat.card (Subgroup.closure ({a, b, c} : Set Γ)) = 3 ^ 3) :
    c ∉ Subgroup.closure ({a, b} : Set Γ) := by
  intro hc
  have e : Subgroup.closure ({a, b, c} : Set Γ) = Subgroup.closure {a, b} := by
    refine le_antisymm ((Subgroup.closure_le _).2 ?_) (Subgroup.closure_mono ?_)
    · rintro x (rfl | rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact hc
    · rintro x (rfl | rfl) <;> simp
  have h9 := card_closure_pair_le hab ha hb
  rw [← e, hcard] at h9
  norm_num at h9

@[expose] def e6BadNWord : List (Fin Tag.E6.rank) :=
  [0, 1, 2, 0, 3, 4, 5, 4, 3, 1, 2, 0, 3, 2, 1, 1, 4, 4]

theorem e6BadNWord_moves : ∃ i, ∃ γ ∈ e6LineRoots i,
    ∀ k, CFSG.ComponentClassification.CatLeafProof.wordReflect .E6 e6BadNWord γ ∉
      e6LineRoots k := by
  decide +kernel


@[expose] def e6BadN (K : Type) [Field K] (c : Kˣ) : adjointGroup Tag.E6 K :=
  weylWordElt .E6 K e6BadNWord * torusElement .E6 K 2 c * torusElement .E6 K 3 c

section Coe

variable {K : Type} [Field K]

theorem coe_weylWordElt (ν : List (Fin Tag.E6.rank)) :
    (weylWordElt .E6 K ν : ModGL .E6 K) = wordRep .E6 K ν := by
  induction ν with
  | nil => rfl
  | cons i ν ih =>
    rw [show weylWordElt .E6 K (i :: ν) = weylElement .E6 K i * weylWordElt .E6 K ν from
      List.prod_cons, Subgroup.coe_mul, ih]
    rfl

theorem coe_e6BadN (c : Kˣ) :
    (e6BadN K c : ModGL .E6 K) =
      wordRep .E6 K e6BadNWord * torusElt .E6 K 2 c * torusElt .E6 K 3 c := by
  rw [e6BadN, Subgroup.coe_mul, Subgroup.coe_mul, coe_weylWordElt]
  rfl

theorem e6BadT_eq (c : Kˣ) : (![1, 1, c, 1, 1, 1] : Fin Tag.E6.rank → Kˣ) =
    fun j => c ^ (![0, 0, 1, 0, 0, 0] : Fin Tag.E6.rank → ℤ) j := by
  funext j
  fin_cases j <;> simp

theorem e6D0Char_eq (ω : Kˣ) :
    e6D0Char ω = fun j => ω ^ (![0, 1, 0, 0, 1, 1] : Fin Tag.E6.rank → ℤ) j := by
  have h0 : ω ^ (0 : ℤ) = 1 := zpow_zero ω
  have h1 : ω ^ (1 : ℤ) = ω := zpow_one ω
  funext j
  fin_cases j
  exacts [h0.symm, h1.symm, h0.symm, h0.symm, h1.symm, h1.symm]

theorem rootChar_zpow (u : Kˣ) (e β : Fin Tag.E6.rank → ℤ) :
    rootChar (fun j => u ^ e j) β = u ^ ∑ j, e j * β j := by
  simp only [rootChar, ← zpow_mul]
  exact CFSG.LieType.Chevalley.prod_zpow_eq_zpow_sum _ _ _

@[expose] def E6ConjPinned (c ω : Kˣ) (g : ModGL .E6 K)
    (π : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ) (s N M : (Fin Tag.E6.rank → ℤ) → ℤ) :
    Prop :=
  ∀ β, IsRoot .E6 β → IsRoot .E6 (π β) ∧ ∀ x : K, g * pinnedX .E6 K β x * g⁻¹ =
    pinnedX .E6 K (π β) ((s β : K) * ((c ^ N β * ω ^ M β : Kˣ) : K) * x)

variable {c ω : Kˣ}

theorem E6ConjPinned.mul {g g' : ModGL .E6 K}
    {π π' : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ}
    {s s' N N' M M' : (Fin Tag.E6.rank → ℤ) → ℤ} (h : E6ConjPinned c ω g π s N M)
    (h' : E6ConjPinned c ω g' π' s' N' M') :
    E6ConjPinned c ω (g * g') (fun β => π (π' β)) (fun β => s (π' β) * s' β)
      (fun β => N (π' β) + N' β) (fun β => M (π' β) + M' β) := by
  intro β hβ
  obtain ⟨hπ', h'x⟩ := h' β hβ
  obtain ⟨hπ, hx⟩ := h (π' β) hπ'
  refine ⟨hπ, fun x => ?_⟩
  rw [show g * g' * pinnedX .E6 K β x * (g * g')⁻¹ =
      g * (g' * pinnedX .E6 K β x * g'⁻¹) * g⁻¹ by group, h'x, hx]
  congr 1
  simp only [zpow_add, Units.val_mul, Int.cast_mul]
  ring

end Coe

section Pinned

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] {c ω : Kˣ}

theorem e6ConjPinned_wordRep (ν : List (Fin Tag.E6.rank)) :
    E6ConjPinned c ω (wordRep .E6 K ν) (wordAct .E6 ν) (wordSign .E6 ν) 0 0 := by
  intro β hβ
  refine ⟨isRoot_wordAct ν hβ, fun x => ?_⟩
  rw [wordRep_conj_pinnedX K ν hβ x]
  simp

theorem e6ConjPinned_rootDiagUnit_left (e : Fin Tag.E6.rank → ℤ) :
    E6ConjPinned c ω (rootDiagUnit .E6 fun j => c ^ e j) id 1 (fun β => ∑ j, e j * β j) 0 := by
  intro β hβ
  refine ⟨hβ, fun x => ?_⟩
  rw [rootDiagUnit_conj_pinnedX _ hβ x, rootChar_zpow]
  simp

theorem e6ConjPinned_rootDiagUnit_right (f : Fin Tag.E6.rank → ℤ) :
    E6ConjPinned c ω (rootDiagUnit .E6 fun j => ω ^ f j) id 1 0 (fun β => ∑ j, f j * β j) := by
  intro β hβ
  refine ⟨hβ, fun x => ?_⟩
  rw [rootDiagUnit_conj_pinnedX _ hβ x, rootChar_zpow]
  simp

theorem e6ConjPinned_torusElt (i : Fin Tag.E6.rank) :
    E6ConjPinned c ω (torusElt .E6 K i c) id 1 (fun β => ∑ j, Tag.E6.cartan i j * β j) 0 := by
  rw [torusElt_eq_rootDiagUnit]
  exact e6ConjPinned_rootDiagUnit_left _

theorem rootDiagUnit_conj_mem_e6LineSpan (a : Fin Tag.E6.rank → Kˣ) {y : ModGL .E6 K}
    (hy : y ∈ rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)))) :
    rootDiagUnit .E6 a * y * (rootDiagUnit .E6 a)⁻¹ ∈
      rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) := by
  have e : (rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)))).map
      (MulAut.conj (rootDiagUnit .E6 a)).toMonoidHom =
        rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) :=
    map_rootSpan_of_forall fun α hα => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hα
      exact map_conj_rootDiagUnit_rootSubgroup a (isRoot_of_mem_e6LineRoots (Finset.mem_coe.1 hi))
  rw [← e]
  exact ⟨y, hy, rfl⟩

end Pinned

section Main

set_option linter.unusedSectionVars false


theorem eq_of_e6ConjPinned {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) {c ω : Kˣ}
    (h3 : ω ^ 3 = 1) {g₁ g₂ : ModGL .E6 K} (hg₁ : g₁ ∈ e6InndiagGL K) (hg₂ : g₂ ∈ e6InndiagGL K)
    {π₁ π₂ : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ}
    {s₁ s₂ N₁ N₂ M₁ M₂ : (Fin Tag.E6.rank → ℤ) → ℤ} (h₁ : E6ConjPinned c ω g₁ π₁ s₁ N₁ M₁)
    (h₂ : E6ConjPinned c ω g₂ π₂ s₂ N₂ M₂)
    (h : ∀ i : Fin Tag.E6.rank,
      ∀ β ∈ ([Pi.single i 1, -Pi.single i 1] : List (Fin Tag.E6.rank → ℤ)),
        π₁ β = π₂ β ∧ s₁ β = s₂ β ∧ N₁ β = N₂ β ∧ M₁ β % 3 = M₂ β % 3) :
    g₁ = g₂ := by
  have h3' : ω ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, h3]
  have key : ∀ i : Fin Tag.E6.rank,
      ∀ β ∈ ([Pi.single i 1, -Pi.single i 1] : List (Fin Tag.E6.rank → ℤ)), IsRoot .E6 β →
        ∀ x : K, g₁ * pinnedX .E6 K β x * g₁⁻¹ = g₂ * pinnedX .E6 K β x * g₂⁻¹ := by
    intro i β hβl hβ x
    obtain ⟨hπ, hs, hN, hM⟩ := h i β hβl
    rw [(h₁ β hβ).2 x, (h₂ β hβ).2 x, hπ, hs, hN, zpow_eq_zpow_emod (M₁ β) h3',
      zpow_eq_zpow_emod (M₂ β) h3', hM]
  have hle : adjointGroup .E6 K ≤
      MonoidHom.eqLocus (MulAut.conj g₁).toMonoidHom (MulAut.conj g₂).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, x, hg | hg⟩
    · rw [show g = xUnit .E6 K i x from Units.ext hg]
      have e := key i (Pi.single i 1) (by simp) (isRoot_single _ i) x
      rw [pinnedX_single] at e
      exact e
    · rw [show g = yUnit .E6 K i x from Units.ext hg]
      have e := key i (-Pi.single i 1) (by simp) (isRoot_neg_single _ i) x
      rw [pinnedX_neg_single] at e
      exact e
  have e : e6InndiagConj K ⟨g₁, hg₁⟩ = e6InndiagConj K ⟨g₂, hg₂⟩ :=
    MulEquiv.ext fun y => Subtype.ext (hle y.2)
  exact congrArg Subtype.val (e6InndiagConj_injective K hK e)

theorem e6BadN_commute_X {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) {ω : Kˣ}
    (h3 : ω ^ 3 = 1) (c : Kˣ) :
    (weylWordElt .E6 K e6BadWord : ModGL .E6 K) * rootDiagUnit .E6 ![1, 1, c, 1, 1, 1] *
        (e6BadN K c : ModGL .E6 K) =
      (e6BadN K c : ModGL .E6 K) * (weylWordElt .E6 K e6BadWord : ModGL .E6 K) *
        rootDiagUnit .E6 ![1, 1, c, 1, 1, 1] := by
  have hn := ((e6ConjPinned_wordRep (K := K) (c := c) (ω := ω) e6BadNWord).mul
    (e6ConjPinned_torusElt 2)).mul (e6ConjPinned_torusElt 3)
  rw [← coe_e6BadN] at hn
  have hw := e6ConjPinned_wordRep (K := K) (c := c) (ω := ω) e6BadWord
  rw [← coe_weylWordElt] at hw
  have ht : E6ConjPinned c ω (rootDiagUnit .E6 ![1, 1, c, 1, 1, 1]) id 1
      (fun β => ∑ j, (![0, 0, 1, 0, 0, 0] : Fin Tag.E6.rank → ℤ) j * β j) 0 := by
    rw [e6BadT_eq]
    exact e6ConjPinned_rootDiagUnit_left _
  have hm : ∀ g : adjointGroup Tag.E6 K, (g : ModGL .E6 K) ∈ e6InndiagGL K :=
    fun g => adjointGroup_le_e6InndiagGL K g.2
  refine eq_of_e6ConjPinned hK h3
    (mul_mem (mul_mem (hm _) (rootDiagUnit_mem_e6InndiagGL _)) (hm _))
    (mul_mem (mul_mem (hm _) (hm _)) (rootDiagUnit_mem_e6InndiagGL _))
    ((hw.mul ht).mul hn) ((hn.mul hw).mul ht) ?_
  decide +kernel

theorem e6BadN_commute_d0 {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) {ω : Kˣ}
    (h3 : ω ^ 3 = 1) (c : Kˣ) :
    rootDiagUnit .E6 (e6D0Char ω) * (e6BadN K c : ModGL .E6 K) =
      (e6BadN K c : ModGL .E6 K) * rootDiagUnit .E6 (e6D0Char ω) := by
  have hn := ((e6ConjPinned_wordRep (K := K) (c := c) (ω := ω) e6BadNWord).mul
    (e6ConjPinned_torusElt 2)).mul (e6ConjPinned_torusElt 3)
  rw [← coe_e6BadN] at hn
  have hd : E6ConjPinned c ω (rootDiagUnit .E6 (e6D0Char ω)) id 1 0
      (fun β => ∑ j, (![0, 1, 0, 0, 1, 1] : Fin Tag.E6.rank → ℤ) j * β j) := by
    rw [e6D0Char_eq]
    exact e6ConjPinned_rootDiagUnit_right _
  have hm : (e6BadN K c : ModGL .E6 K) ∈ e6InndiagGL K :=
    adjointGroup_le_e6InndiagGL K (e6BadN K c).2
  refine eq_of_e6ConjPinned hK h3 (mul_mem (rootDiagUnit_mem_e6InndiagGL _) hm)
    (mul_mem hm (rootDiagUnit_mem_e6InndiagGL _)) (hd.mul hn) (hn.mul hd) ?_
  decide +kernel

theorem seitzHyperGamma_e6BadCube (hLayer : E6ThreeLayerGen) {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K ≠ 3) (hK : 3 ∣ Nat.card K - 1) (hK4 : Nat.card K ≠ 4) {ω : Kˣ}
    (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (c : Kˣ) (hE : IsElemAbelian 3 (e6BadCube K ω c))
    (hEc : Nat.card (e6BadCube K ω c) = 3 ^ 3) : seitzHyperGamma 3 (e6BadCube K ω c) = ⊤ := by
  have hK4' : 4 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hh : MulAut.conj (e6LineElt ω) ∈ e6BadCube K ω c := Subgroup.subset_closure (by simp)
  have hd : rootDiagAutHom .E6 K (e6D0Char ω) ∈ e6BadCube K ω c :=
    Subgroup.subset_closure (by simp)
  have hX : e6BadX K c ∈ e6BadCube K ω c := Subgroup.subset_closure (by simp)
  have hED : e6BadCube K ω c ≤ e6Inndiag K := by
    have hD : ∀ a, rootDiagAutHom .E6 K a ∈ e6Inndiag K := fun a =>
      le_sup_right (a := CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) ⟨a, rfl⟩
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl | rfl)
    · exact innerAut_le_e6Inndiag K ⟨_, rfl⟩
    · exact hD _
    · exact mul_mem (innerAut_le_e6Inndiag K ⟨_, rfl⟩) (hD _)
  have hU : rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) ≤
      (seitzHyperGamma 3 (e6BadCube K ω c)).map (adjointGroup Tag.E6 K).subtype := by
    rw [rootSpan_iUnion_e6LineRoots]
    have hf : ∀ i, e6LineFactor K i ≤
        (seitzHyperGamma 3 (e6BadCube K ω c)).map (adjointGroup Tag.E6 K).subtype :=
      fun i x hx => ⟨⟨x, rootSpan_le_adjointGroup K _ hx⟩,
        hLayer K hK3 hK hK4 ω h3 h1 _ hE hEc hED hh i (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    exact sup_le (sup_le (hf 0) (hf 1)) (hf 2)
  have hd1 : rootDiagAutHom .E6 K (e6D0Char ω) ≠ 1 := fun h => h1 (by
    simpa [e6D0Char] using
      congrFun (rootDiagAutHom_injective (h.trans (map_one (rootDiagAutHom .E6 K)).symm)) 1)
  have hab : Commute (MulAut.conj (e6LineElt ω)) (rootDiagAutHom .E6 K (e6D0Char ω)) := by
    have := hE.1.is_comm.comm ⟨_, hh⟩ ⟨_, hd⟩
    exact congrArg Subtype.val this
  have hXd : e6BadX K c ∉ Subgroup.zpowers (rootDiagAutHom .E6 K (e6D0Char ω)) := fun hz =>
    notMem_closure_pair_of_card hab (hE.2 _ hh) (hE.2 _ hd) hEc
      (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)) hz)
  have hnd : rootDiagAutHom .E6 K (e6D0Char ω) (e6BadN K c) = e6BadN K c := by
    refine Subtype.ext ?_
    change rootDiagUnit .E6 (e6D0Char ω) * (e6BadN K c : ModGL .E6 K) *
      (rootDiagUnit .E6 (e6D0Char ω))⁻¹ = _
    rw [e6BadN_commute_d0 hK4' h3 c, mul_inv_cancel_right]
  have hnX : e6BadX K c (e6BadN K c) = e6BadN K c := by
    refine Subtype.ext ?_
    change (weylWordElt .E6 K e6BadWord : ModGL .E6 K) * (rootDiagUnit .E6 ![1, 1, c, 1, 1, 1] *
      (e6BadN K c : ModGL .E6 K) * (rootDiagUnit .E6 ![1, 1, c, 1, 1, 1])⁻¹) *
        (weylWordElt .E6 K e6BadWord : ModGL .E6 K)⁻¹ = _
    rw [show ∀ a b m : ModGL .E6 K, a * (b * m * b⁻¹) * a⁻¹ = a * b * m * (a * b)⁻¹ from
      fun a b m => by group, e6BadN_commute_X hK4' h3 c]
    group
  have hn : e6BadN K c ∈ seitzHyperGamma 3 (e6BadCube K ω c) :=
    mem_seitzHyperGamma_of_fixed hE (by rw [hEc]; norm_num) hd hX hd1 hXd hnd hnX
  refine eq_top_of_e6A2_le_of_conj_le _ hU e6BadNWord e6BadNWord_moves ?_
  rintro _ ⟨y, hy, rfl⟩
  have hb : torusElt .E6 K 2 c * torusElt .E6 K 3 c = rootDiagUnit .E6
      ((fun j => c ^ Tag.E6.cartan 2 j) * fun j => c ^ Tag.E6.cartan 3 j) := by
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, rootDiagUnit_mul]
  have hy' := rootDiagUnit_conj_mem_e6LineSpan
    ((fun j => c ^ Tag.E6.cartan 2 j) * fun j => c ^ Tag.E6.cartan 3 j)⁻¹ hy
  rw [← rootDiagUnit_inv, inv_inv, ← hb] at hy'
  obtain ⟨m, hm, hmy⟩ := hU hy'
  refine ⟨e6BadN K c * m * (e6BadN K c)⁻¹, mul_mem (mul_mem hn hm) (inv_mem hn), ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] at hmy ⊢
  rw [hmy, coe_e6BadN, coe_weylWordElt]
  group

theorem e6ThreeNotAll24Gen_of_nf (hLayer : E6ThreeLayerGen) (hNF : E6ThreeNotAll24NF) :
    E6ThreeNotAll24Gen := by
  intro K _ _ hK3 hK hK4 E hE hEc hED hEi hER hA
  obtain ⟨ω, c, φ, h3, h1, hφ⟩ := hNF K hK3 hK hK4 E hE hEc hED hEi hER hA
  have hE' : IsElemAbelian 3 (e6BadCube K ω c) := by
    rw [← hφ]
    exact hE.map _
  have hEc' : Nat.card (e6BadCube K ω c) = 3 ^ 3 := by
    rw [← hφ, Subgroup.card_map_of_injective (MulAut.congr φ).injective, hEc]
  have htop := seitzHyperGamma_e6BadCube hLayer hK3 hK hK4 h3 h1 c hE' hEc'
  refine eq_top_iff.2 fun y _ => mem_seitzHyperGamma_of_congr (c := φ) ?_
  rw [hφ, htop]
  exact Subgroup.mem_top _

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end

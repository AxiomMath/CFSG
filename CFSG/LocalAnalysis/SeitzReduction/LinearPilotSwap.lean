module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapParam
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTBlocks
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAlignImages
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuasisimpleOfCentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleField
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

theorem exists_coherent_choice {α : Type*} (A B A' B' : ℕ → α) :
    ∃ U : ℕ → α, U 0 = A 0 ∧ ∀ k, (U k = A k ∨ U k = B k) →
      (U k = A k ∧ U (k + 1) = A' k) ∨ (U k = B k ∧ U (k + 1) = B' k) := by
  classical
  let U : ℕ → α := fun k =>
    Nat.rec (motive := fun _ => α) (A 0) (fun k u => if u = A k then A' k else B' k) k
  have hU : ∀ k, U (k + 1) = if U k = A k then A' k else B' k := fun _ => rfl
  refine ⟨U, rfl, fun k hk => ?_⟩
  by_cases h : U k = A k
  · exact Or.inl ⟨h, by simp [hU, h]⟩
  · exact Or.inr ⟨hk.resolve_left h, by simp [hU, h]⟩

section Diag

variable {G : Type*} [Group G] {t : G} {G₁ : Subgroup G}

@[expose] def linearSwapDiag (h : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G)) :
    G₁ →* G where
  toFun x := x * (t * x * t⁻¹)
  map_one' := by simp
  map_mul' x y := by
    have hc : (y : G) * (t * x * t⁻¹) = (t * x * t⁻¹) * y :=
      mem_centralizer_iff.1 (h ⟨x, x.2, rfl⟩) y y.2
    simp only [Subgroup.coe_mul]
    calc (x : G) * y * (t * (x * y) * t⁻¹) = x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) := by group
      _ = x * ((t * x * t⁻¹) * y) * (t * y * t⁻¹) := by rw [hc]
      _ = x * (t * x * t⁻¹) * (y * (t * y * t⁻¹)) := by group

theorem linearSwapDiag_apply (h : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (x : G₁) : linearSwapDiag h x = x * (t * x * t⁻¹) :=
  rfl

theorem ker_linearSwapDiag_le_center
    (h : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G)) :
    (linearSwapDiag h).ker ≤ center G₁ := by
  intro x hx
  rw [MonoidHom.mem_ker, linearSwapDiag_apply] at hx
  have hx' : (x : G) = t * (x : G)⁻¹ * t⁻¹ :=
    calc (x : G) = (t * x * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hx
      _ = t * (x : G)⁻¹ * t⁻¹ := by group
  have hmem : (x : G) ∈ centralizer (G₁ : Set G) := by
    rw [hx']
    exact h ⟨(x : G)⁻¹, G₁.inv_mem x.2, rfl⟩
  rw [mem_center_iff]
  intro y
  exact Subtype.ext ((mem_centralizer_iff.1 hmem) y y.2)

theorem isQuasisimple_of_linearSwapDiag
    (h : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G)) (hperf : ⁅G₁, G₁⁆ = G₁)
    {S : Subgroup G} (hS : IsSimpleGroup S) (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ S)
    (hsurj : ∀ y ∈ S, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) : CFSG.Open.IsQuasisimple G₁ := by
  let δ : G₁ →* S := (linearSwapDiag h).codRestrict S fun x => hδ x x.2
  have hδsurj : Function.Surjective δ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : δ.ker ≤ center G₁ := by
    intro x hx
    refine ker_linearSwapDiag_le_center h ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  have hperf' : Group.IsPerfect G₁ := Subgroup.isPerfect_iff.2 hperf
  have hnt : Nontrivial G₁ := by
    have : Nontrivial S := hS.toNontrivial
    obtain ⟨y, hy⟩ := exists_ne (1 : S)
    obtain ⟨x, rfl⟩ := hδsurj y
    exact ⟨⟨x, 1, fun h' => hy (by rw [h', map_one])⟩⟩
  obtain ⟨-, h1, h2⟩ :=
    CFSG.GorensteinWalter.isQuasisimple_of_perfect_of_ker_le_center_of_surjective_simple δ
      hδsurj hnt hperf' hS hker
  exact ⟨h1, h2⟩

end Diag

section Joins

variable {G : Type*} [Group G]

theorem commutator_iSup_eq_of_forall {ι' : Sort*} (U : ι' → Subgroup G)
    (hU : ∀ i, ⁅U i, U i⁆ = U i) : ⁅⨆ i, U i, ⨆ i, U i⁆ = ⨆ i, U i := by
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (iSup_le fun i => ?_)
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · calc U i = ⁅U i, U i⁆ := (hU i).symm
      _ ≤ ⁅⨆ i, U i, ⨆ i, U i⁆ := commutator_mono (le_iSup U i) (le_iSup U i)

theorem commutator_map_eq_of_commutator_eq {H : Type*} [Group H] (f : H →* G) {A : Subgroup H}
    (hA : ⁅A, A⁆ = A) : ⁅A.map f, A.map f⁆ = A.map f := by
  rw [← map_commutator, hA]

variable {t : G}

theorem mul_conj_mem_of_mem_iSup {ι' : Sort*} {U : ι' → Subgroup G}
    (h : (⨆ i, U i).map (MulAut.conj t).toMonoidHom ≤ centralizer ((⨆ i, U i : Subgroup G) : Set G))
    {S : Subgroup G} (hU : ∀ i, ∀ x ∈ U i, x * (t * x * t⁻¹) ∈ S) :
    ∀ x ∈ ⨆ i, U i, x * (t * x * t⁻¹) ∈ S := by
  intro x hx
  refine (Subgroup.iSup_induction U (C := fun x => x ∈ ⨆ i, U i ∧ x * (t * x * t⁻¹) ∈ S) hx
    (fun i y hy => ⟨le_iSup U i hy, hU i y hy⟩) ⟨one_mem _, by simp⟩
    (fun y z hy hz => ⟨mul_mem hy.1 hz.1, ?_⟩)).2
  have hc : z * (t * y * t⁻¹) = (t * y * t⁻¹) * z :=
    mem_centralizer_iff.1 (h ⟨y, hy.1, rfl⟩) z hz.1
  have e : y * z * (t * (y * z) * t⁻¹) = (y * (t * y * t⁻¹)) * (z * (t * z * t⁻¹)) := by
    calc y * z * (t * (y * z) * t⁻¹) = y * (z * (t * y * t⁻¹)) * (t * z * t⁻¹) := by group
      _ = y * ((t * y * t⁻¹) * z) * (t * z * t⁻¹) := by rw [hc]
      _ = (y * (t * y * t⁻¹)) * (z * (t * z * t⁻¹)) := by group
  rw [e]
  exact mul_mem hy.2 hz.2

theorem exists_mul_conj_eq_of_mem_iSup {ι' κ : Sort*} {U : ι' → Subgroup G}
    (h : (⨆ i, U i).map (MulAut.conj t).toMonoidHom ≤ centralizer ((⨆ i, U i : Subgroup G) : Set G))
    {V : κ → Subgroup G} (hV : ∀ j, ∀ y ∈ V j, ∃ x ∈ ⨆ i, U i, x * (t * x * t⁻¹) = y) :
    ∀ y ∈ ⨆ j, V j, ∃ x ∈ ⨆ i, U i, x * (t * x * t⁻¹) = y := by
  intro y hy
  refine Subgroup.iSup_induction V (C := fun y => ∃ x ∈ ⨆ i, U i, x * (t * x * t⁻¹) = y) hy
    (fun j y hy => hV j y hy) ⟨1, one_mem _, by simp⟩ ?_
  rintro _ _ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, rfl⟩
  refine ⟨x₁ * x₂, mul_mem hx₁ hx₂, ?_⟩
  have hc : x₂ * (t * x₁ * t⁻¹) = (t * x₁ * t⁻¹) * x₂ :=
    mem_centralizer_iff.1 (h ⟨x₁, hx₁, rfl⟩) x₂ hx₂
  calc x₁ * x₂ * (t * (x₁ * x₂) * t⁻¹) = x₁ * (x₂ * (t * x₁ * t⁻¹)) * (t * x₂ * t⁻¹) := by group
    _ = x₁ * ((t * x₁ * t⁻¹) * x₂) * (t * x₂ * t⁻¹) := by rw [hc]
    _ = x₁ * (t * x₁ * t⁻¹) * (x₂ * (t * x₂ * t⁻¹)) := by group

theorem map_conj_iSup_le_centralizer {ι' : Sort*} {U : ι' → Subgroup G}
    (h : ∀ i j, (U j).map (MulAut.conj t).toMonoidHom ≤ centralizer (U i : Set G)) :
    (⨆ i, U i).map (MulAut.conj t).toMonoidHom ≤
      centralizer ((⨆ i, U i : Subgroup G) : Set G) := by
  rw [Subgroup.map_iSup]
  refine iSup_le fun j => ?_
  rw [le_centralizer_iff]
  exact iSup_le fun i => le_centralizer_iff.1 (h i j)

end Joins

section Cover

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]

@[expose] def SwapNeighbourCover (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (s : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card ≤ s → ∃ (X : Subgroup G) (N : Finset (Fin n)), S ⊆ N ∧
    (∃ k, k ∉ N) ∧ 3 ≤ N.card ∧ X ≤ modelToG e (blockTorus (K := K) S) ∧
      Nonempty (SwapNeighbourParam e t X N)

variable {e : L ≃* LinearFlag.projectiveSL n K} {t : G}

theorem SwapNeighbourCover.mono {s s' : ℕ} (h : SwapNeighbourCover e t s) (hs : s' ≤ s) :
    SwapNeighbourCover e t s' :=
  fun S hS => h S (hS.trans hs)

theorem swapNeighbourCover_rootTorus (hn : 5 ≤ n)
    (hparam : ∀ (a b : Fin n) (hab : a ≠ b),
      Nonempty (SwapNeighbourParam e t (modelToG e (rootTorus (K := K) hab))
        (({a, b} : Finset (Fin n))ᶜ)))
    {s : ℕ} (hs : s + 2 ≤ n) : SwapNeighbourCover e t s := by
  intro S hS
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_index_notMem (S := S) (by omega)
  refine ⟨modelToG e (rootTorus (K := K) hab), ({a, b} : Finset (Fin n))ᶜ, fun x hx => ?_,
    ⟨a, by simp⟩, ?_, modelToG_rootTorus_le e hab ha hb, hparam a b hab⟩
  · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => ha (h ▸ hx), fun h => hb (h ▸ hx)⟩
  · rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
    omega

theorem swapNeighbourCover_levTorus (hn : 4 ≤ n)
    (hparam : ∀ a : Fin n,
      Nonempty (SwapNeighbourParam e t (modelToG e (levTorus (K := K) a)) ({a}ᶜ)))
    {s : ℕ} (hs : s + 1 ≤ n) : SwapNeighbourCover e t s := by
  intro S hS
  obtain ⟨a, ha⟩ := exists_index_notMem_of_card_lt (S := S) (by omega)
  refine ⟨modelToG e (levTorus (K := K) a), {a}ᶜ, fun x hx => ?_, ⟨a, by simp⟩, ?_,
    modelToG_levTorus_le e ha, hparam a⟩
  · simp only [Finset.mem_compl, Finset.mem_singleton]
    exact fun h => ha (h ▸ hx)
  · rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
    omega

theorem SwapNeighbourParam.pieceCore_le_centralizer [Finite G] [Finite K] {X : Subgroup G}
    {N : Finset (Fin n)} (P : SwapNeighbourParam e t X N) {I J : Finset (Fin n)} (hIN : I ⊆ N)
    (hJN : J ⊆ N) (hIJ : Disjoint I J) (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) {k : Fin n}
    (hk : k ∉ N) {κ : Kˣ} (hκ : κ ≠ 1) (hK : 4 ≤ Nat.card K)
    (hXI : X ≤ modelToG e (blockTorus (K := K) I)) (hXJ : X ≤ modelToG e (blockTorus (K := K) J)) :
    pieceCore e I ≤ centralizer (pieceCore e J : Set G) := by
  rw [P.pieceCore_eq_fst_sup_snd hIN hk hκ (commutator_blockSpecialLinear_eq_of_two_le hI hK) hXI,
    P.pieceCore_eq_fst_sup_snd hJN hk hκ (commutator_blockSpecialLinear_eq_of_two_le hJ hK) hXJ,
    le_centralizer_iff]
  refine sup_le ?_ ?_
  · rw [← le_centralizer_iff]
    exact sup_le (P.fst_le_centralizer_fst_of_disjoint hIJ.symm) (P.snd_le_centralizer_fst J I)
  · rw [← le_centralizer_iff]
    exact sup_le (P.fst_le_centralizer_snd J I) (P.snd_le_centralizer_snd_of_disjoint hIJ.symm)

theorem pieceCore_le_centralizer_of_swapNeighbourCover [Finite G] [Finite K]
    (hcov : SwapNeighbourCover e t 4) {I J : Finset (Fin n)} (hIJ : Disjoint I J)
    (hI : I.card = 2) (hJ : J.card = 2) {κ : Kˣ} (hκ : κ ≠ 1) (hK : 4 ≤ Nat.card K) :
    pieceCore e I ≤ centralizer (pieceCore e J : Set G) := by
  have hc : (I ∪ J).card ≤ 4 := (Finset.card_union_le I J).trans (by omega)
  obtain ⟨X, N, hSN, ⟨k, hk⟩, -, hX, ⟨P⟩⟩ := hcov (I ∪ J) hc
  exact P.pieceCore_le_centralizer (Finset.subset_union_left.trans hSN)
    (Finset.subset_union_right.trans hSN) hIJ hI.ge hJ.ge hk hκ hK
    (hX.trans (modelToG_mono e (blockTorus_anti Finset.subset_union_left)))
    (hX.trans (modelToG_mono e (blockTorus_anti Finset.subset_union_right)))

end Cover

section Construction

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem SwapNeighbourParam.commutator_fst {n : ℕ} {e : L ≃* LinearFlag.projectiveSL n K} {t : G}
    {X : Subgroup G} {N : Finset (Fin n)} (P : SwapNeighbourParam e t X N) {I : Finset (Fin n)}
    (hIN : I ⊆ N)
    (hperf : ⁅blockSpecialLinear (K := K) I, blockSpecialLinear (K := K) I⁆ =
      blockSpecialLinear I) :
    ⁅P.fst I, P.fst I⁆ = P.fst I :=
  commutator_map_eq_of_commutator_eq _ (commutator_subgroupOf_eq_self
    (blockSpecialLinear_mono hIN) hperf)

theorem SwapNeighbourParam.commutator_snd {n : ℕ} {e : L ≃* LinearFlag.projectiveSL n K} {t : G}
    {X : Subgroup G} {N : Finset (Fin n)} (P : SwapNeighbourParam e t X N) {I : Finset (Fin n)}
    (hIN : I ⊆ N)
    (hperf : ⁅blockSpecialLinear (K := K) I, blockSpecialLinear (K := K) I⁆ =
      blockSpecialLinear I) :
    ⁅P.snd I, P.snd I⁆ = P.snd I :=
  commutator_map_eq_of_commutator_eq _ (commutator_subgroupOf_eq_self
    (blockSpecialLinear_mono hIN) hperf)

theorem exists_units_ne_one_of_three_le_card [Finite K] (hK : 3 ≤ Nat.card K) :
    ∃ κ : Kˣ, κ ≠ 1 := by
  have h2 : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have h3 : 1 < Nat.card Kˣ := by omega
  have := Finite.one_lt_card_iff_nontrivial.mp h3
  exact exists_ne 1

theorem iSup_modelToG_blockSL_pair_eq {m : ℕ} (e : L ≃* LinearFlag.projectiveSL (m + 1) K) :
    ⨆ i : Fin m, modelToG e (blockSL (K := K) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) =
      L := by
  refine Eq.trans ?_ (modelToG_top e)
  rw [← iSup_blockSL_pair_eq_top K m]
  simp only [modelToG, Subgroup.map_iSup]

theorem exists_swapFactors_of_cover [Finite G] [Finite K] [CharP K 2] {m : ℕ} (hm : 2 ≤ m)
    (hK : 4 ≤ Nat.card K) (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G}
    (hcov : SwapNeighbourCover e t 3)
    (hcomm : ∀ i j : Fin m, (i : ℕ) + 1 < j →
      pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ≤
        centralizer (pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1))) : Set G)) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  classical
  obtain ⟨κ, hκ⟩ := exists_units_ne_one_of_three_le_card (K := K) (by omega)
  have hframe : ∀ k : ℕ, ∃ (X : Subgroup G) (N : Finset (Fin (m + 1))),
      consecutiveBlock (m + 1) k 3 ⊆ N ∧ (∃ o, o ∉ N) ∧ 3 ≤ N.card ∧
        X ≤ modelToG e (blockTorus (K := K) (consecutiveBlock (m + 1) k 3)) ∧
          Nonempty (SwapNeighbourParam e t X N) :=
    fun k => hcov _ (card_consecutiveBlock_le _ _ _)
  choose X N hτN ho hN3 hXτ hP using hframe
  choose o ho using ho
  let P : ∀ k, SwapNeighbourParam e t (X k) (N k) := fun k => (hP k).some
  set α : ℕ → Finset (Fin (m + 1)) := fun k => consecutiveBlock (m + 1) k 2 with hαdef
  have hα3 : ∀ k, α k ⊆ consecutiveBlock (m + 1) k 3 := fun k x hx => by
    simp only [hαdef, mem_consecutiveBlock] at hx ⊢
    omega
  have hα3' : ∀ k, α (k + 1) ⊆ consecutiveBlock (m + 1) k 3 := fun k x hx => by
    simp only [hαdef, mem_consecutiveBlock] at hx ⊢
    omega
  have hsubN : ∀ k {S : Finset (Fin (m + 1))}, S ⊆ consecutiveBlock (m + 1) k 3 → S ⊆ N k :=
    fun k S hS => hS.trans (hτN k)
  have hX : ∀ k {S : Finset (Fin (m + 1))}, S ⊆ consecutiveBlock (m + 1) k 3 →
      X k ≤ modelToG e (blockTorus (K := K) S) :=
    fun k S hS => (hXτ k).trans (modelToG_mono e (blockTorus_anti hS))
  have hαeq : ∀ k (hk : k < m),
      α k = ({(⟨k, hk⟩ : Fin m).castSucc, (⟨k, hk⟩ : Fin m).succ} : Finset (Fin (m + 1))) :=
    fun k hk => consecutiveBlock_two ⟨k, hk⟩
  have hαcard : ∀ k, k < m → (α k).card = 2 := fun k hk => by
    rw [hαeq k hk]
    exact card_nodePair _
  have hαne : ∀ k j, k < m → α k ≠ N j := fun k j hk h => by
    have := hN3 j
    rw [← h, hαcard k hk] at this
    omega
  have hkN : ∀ k, o k ∉ N k := ho
  have hperfα : ∀ k, k < m → ⁅blockSpecialLinear (K := K) (α k), blockSpecialLinear (α k)⁆ =
      blockSpecialLinear (α k) := fun k hk =>
    commutator_blockSpecialLinear_eq_of_two_le (hαcard k hk).ge hK
  have hpiece : ∀ k, k < m →
      pieceCore e (α k) = (P k).fst (α k) ⊔ (P k).snd (α k) := fun k hk =>
    (P k).pieceCore_eq_fst_sup_snd (hsubN k (hα3 k)) (hkN k) hκ (hperfα k hk) (hX k (hα3 k))
  obtain ⟨U, hU0, hU⟩ := exists_coherent_choice (fun k => (P k).fst (α k))
    (fun k => (P k).snd (α k)) (fun k => (P k).fst (α (k + 1))) (fun k => (P k).snd (α (k + 1)))
  have hinv : ∀ k, k < m → (U k = (P k).fst (α k) ∨ U k = (P k).snd (α k)) := by
    intro k
    induction k with
    | zero => exact fun _ => Or.inl hU0
    | succ k ih =>
      intro hk
      rcases hU k (ih (by omega)) with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h]
        exact (P (k + 1)).fst_eq_or_eq hK (P k) (hαcard (k + 1) hk) (hsubN (k + 1) (hα3 (k + 1)))
          (hsubN k (hα3' k)) (hαne _ _ hk) (hαne _ _ hk) (hkN (k + 1)) (hkN k) hκ
          (hX (k + 1) (hα3 (k + 1))) (hX k (hα3' k))
      · rw [h]
        exact (P (k + 1)).snd_eq_or_eq hK (P k) (hαcard (k + 1) hk) (hsubN (k + 1) (hα3 (k + 1)))
          (hsubN k (hα3' k)) (hαne _ _ hk) (hαne _ _ hk) (hkN (k + 1)) (hkN k) hκ
          (hX (k + 1) (hα3 (k + 1))) (hX k (hα3' k))
  have hαi : ∀ i : Fin m, α i = ({i.castSucc, i.succ} : Finset (Fin (m + 1))) :=
    fun i => hαeq i i.isLt
  have hUpiece : ∀ i : Fin m, U i ≤ pieceCore e (α i) := fun i => by
    rw [hpiece i i.isLt]
    rcases hinv i i.isLt with h | h <;> rw [h]
    exacts [le_sup_left, le_sup_right]
  have hUt : ∀ i : Fin m, ((U i).map (MulAut.conj t).toMonoidHom = (P i).snd (α i) ∧
      U i = (P i).fst (α i)) ∨ ((U i).map (MulAut.conj t).toMonoidHom = (P i).fst (α i) ∧
      U i = (P i).snd (α i)) := fun i => by
    rcases hinv i i.isLt with h | h
    · exact Or.inl ⟨by rw [h, (P i).map_conj_fst], h⟩
    · exact Or.inr ⟨by rw [h, (P i).map_conj_snd], h⟩
  have hUtpiece : ∀ i : Fin m, (U i).map (MulAut.conj t).toMonoidHom ≤ pieceCore e (α i) :=
    fun i => by
      rw [hpiece i i.isLt]
      rcases hUt i with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
      exacts [le_sup_right, le_sup_left]
  have hfar : ∀ i j : Fin m, pieceCore e (α j) ≤ centralizer (pieceCore e (α i) : Set G) →
      (U j).map (MulAut.conj t).toMonoidHom ≤ centralizer (U i : Set G) := fun i j h =>
    (hUtpiece j).trans (h.trans (centralizer_le (SetLike.coe_subset_coe.2 (hUpiece i))))
  have hcommU : ∀ i j : Fin m,
      (U j).map (MulAut.conj t).toMonoidHom ≤ centralizer (U i : Set G) := by
    intro i j
    rcases lt_trichotomy (j : ℕ) (i : ℕ) with hji | hij | hij
    · rcases Nat.lt_or_ge ((j : ℕ) + 1) i with hji' | hji'
      ·
        have h := hcomm j i hji'
        rw [← hαi, ← hαi] at h
        exact hfar i j h
      ·
        have hi : (i : ℕ) = j + 1 := by omega
        rw [hi]
        rcases hU j (hinv j j.isLt) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, (P j).map_conj_fst, h2]
          exact (P j).snd_le_centralizer_fst _ _
        · rw [h1, (P j).map_conj_snd, h2]
          exact (P j).fst_le_centralizer_snd _ _
    ·
      obtain rfl : i = j := Fin.ext hij.symm
      rcases hUt i with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
        exact (P i).snd_le_centralizer_fst _ _
      · rw [h1, h2]
        exact (P i).fst_le_centralizer_snd _ _
    · rcases Nat.lt_or_ge ((i : ℕ) + 1) j with hij' | hij'
      ·
        have h := hcomm i j hij'
        rw [← hαi, ← hαi] at h
        exact hfar i j (le_centralizer_iff.1 h)
      ·
        have hj : (j : ℕ) = i + 1 := by omega
        rw [hj]
        rcases hU i (hinv i i.isLt) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2, (P i).map_conj_fst]
          exact (P i).snd_le_centralizer_fst _ _
        · rw [h1, h2, (P i).map_conj_snd]
          exact (P i).fst_le_centralizer_snd _ _
  have h₁₂ := map_conj_iSup_le_centralizer (U := fun i : Fin m => U i) hcommU
  have hsup : (⨆ i : Fin m, U i) ⊔ (⨆ i : Fin m, U i).map (MulAut.conj t).toMonoidHom =
      ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) := by
    rw [Subgroup.map_iSup, ← iSup_sup_eq]
    refine iSup_congr fun i => ?_
    rw [← hαi, hpiece i i.isLt]
    rcases hUt i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  have hδ : ∀ x ∈ ⨆ i : Fin m, U i, x * (t * x * t⁻¹) ∈ L := by
    refine mul_conj_mem_of_mem_iSup h₁₂ fun i x hx =>
      modelToG_le e (blockSL (K := K) (α i)) ?_
    rcases hinv i i.isLt with h | h
    · exact (P i).mul_conj_mem_modelToG_of_mem_fst (h ▸ hx)
    · exact (P i).mul_conj_mem_modelToG_of_mem_snd (h ▸ hx)
  have hsurj : ∀ y ∈ L, ∃ x ∈ ⨆ i : Fin m, U i, x * (t * x * t⁻¹) = y := by
    intro y hy
    rw [← iSup_modelToG_blockSL_pair_eq e] at hy
    refine exists_mul_conj_eq_of_mem_iSup h₁₂ (fun i y hy => ?_) y hy
    rw [← hαi] at hy
    rcases hinv i i.isLt with h | h
    · obtain ⟨x, hx, hxy⟩ := (P i).exists_mem_fst_mul_conj_eq (hsubN i (hα3 i)) hy
      exact ⟨x, le_iSup (fun i : Fin m => U i) i (h ▸ hx), hxy⟩
    · obtain ⟨x, hx, hxy⟩ := (P i).exists_mem_snd_mul_conj_eq (hsubN i (hα3 i)) hy
      exact ⟨x, le_iSup (fun i : Fin m => U i) i (h ▸ hx), hxy⟩
  have hperf : ⁅⨆ i : Fin m, U i, ⨆ i : Fin m, U i⁆ = ⨆ i : Fin m, U i :=
    commutator_iSup_eq_of_forall (fun i : Fin m => U i) fun i => by
      rcases hinv i i.isLt with h | h <;> rw [h]
      · exact (P i).commutator_fst (hsubN i (hα3 i)) (hperfα i i.isLt)
      · exact (P i).commutator_snd (hsubN i (hα3 i)) (hperfα i i.isLt)
  have hL : IsSimpleGroup L := by
    have : IsSimpleGroup (LinearFlag.projectiveSL (m + 1) K) :=
      CFSG.ComponentClassification.OutcomeLocal.isSimpleGroup_projectiveSL (by omega)
    exact e.isSimpleGroup
  exact ⟨⨆ i : Fin m, U i, isQuasisimple_of_linearSwapDiag h₁₂ hperf hL hδ hsurj, h₁₂, hsup, hδ,
    hsurj⟩

theorem exists_swapFactors_of_param [Finite G] [Finite K] [CharP K 2] {m : ℕ} (hm : 4 ≤ m)
    (hK : 4 ≤ Nat.card K) (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G}
    (hparam : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
      Nonempty (SwapNeighbourParam e t (modelToG e (rootTorus (K := K) hab))
        (({a, b} : Finset (Fin (m + 1)))ᶜ)))
    (hcomm : ∀ i j : Fin m, (i : ℕ) + 1 < j →
      pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ≤
        centralizer (pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1))) : Set G)) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y :=
  exists_swapFactors_of_cover (by omega) hK e
    (swapNeighbourCover_rootTorus (by omega) hparam (by omega)) hcomm

theorem exists_swapFactors_rootTorus [Finite G] [Finite K] [CharP K 2] {m : ℕ} (hm : 5 ≤ m)
    (hK : 4 ≤ Nat.card K) (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G}
    (hparam : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
      Nonempty (SwapNeighbourParam e t (modelToG e (rootTorus (K := K) hab))
        (({a, b} : Finset (Fin (m + 1)))ᶜ))) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  obtain ⟨κ, hκ⟩ := exists_units_ne_one_of_three_le_card (K := K) (by omega)
  exact exists_swapFactors_of_param (by omega) hK e hparam fun i j hij =>
    pieceCore_le_centralizer_of_swapNeighbourCover
      (swapNeighbourCover_rootTorus (by omega) hparam (by omega)) (disjoint_nodePair_of_lt i j hij)
      (card_nodePair i) (card_nodePair j) hκ hK

end Construction

end CFSG.SeitzReduction.LinearPilot

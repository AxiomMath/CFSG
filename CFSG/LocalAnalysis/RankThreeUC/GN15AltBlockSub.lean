module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeAbstract
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBlockLiftBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
open scoped commutatorElement

section LiftBlock

variable {X : Type*} [Group X]

@[expose] def liftBlockGens (K Kb : Subgroup X) : Set X :=
  {y | ∃ k ∈ K, ∃ b ∈ Kb, Odd (orderOf b) ∧ y = k * b * k⁻¹}

@[expose] def liftBlock (K Kb : Subgroup X) : Subgroup X :=
  Subgroup.closure (liftBlockGens K Kb)

private theorem orderOf_conj_eq' (g x : X) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using this

theorem liftBlock_le {K Kb : Subgroup X} (hKb : Kb ≤ K) : liftBlock K Kb ≤ K := by
  refine (Subgroup.closure_le K).2 ?_
  rintro _ ⟨k, hk, b, hb, -, rfl⟩
  exact K.mul_mem (K.mul_mem hk (hKb hb)) (K.inv_mem hk)

theorem conj_mem_liftBlock {K Kb : Subgroup X} {k : X} (hk : k ∈ K) {y : X}
    (hy : y ∈ liftBlock K Kb) : k * y * k⁻¹ ∈ liftBlock K Kb := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k', hk', b, hb, hodd, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨k * k', K.mul_mem hk hk', b, hb, hodd, ?_⟩
    group
  | one => simp
  | mul x y _ _ hx hy =>
    have e : k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
    rw [e]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ hx

theorem le_liftBlock {K Kb : Subgroup X}
    (hodd : Kb ≤ Subgroup.closure {x : X | x ∈ Kb ∧ Odd (orderOf x)}) : Kb ≤ liftBlock K Kb := by
  refine hodd.trans (Subgroup.closure_mono ?_)
  rintro x ⟨hx, hxo⟩
  exact ⟨1, K.one_mem, x, hx, hxo, by simp⟩

theorem liftBlock_le_of_normal {K Kb N : Subgroup X} [N.Normal] (hKb : Kb ≤ N) :
    liftBlock K Kb ≤ N := by
  refine (Subgroup.closure_le N).2 ?_
  rintro _ ⟨k, -, b, hb, -, rfl⟩
  exact ‹N.Normal›.conj_mem b (hKb hb) k

theorem liftBlock_le_closure_odd (K Kb : Subgroup X) :
    liftBlock K Kb ≤
      Subgroup.closure {x : X | x ∈ liftBlock K Kb ∧ Odd (orderOf x)} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, b, hb, hodd, rfl⟩
  refine Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨k, hk, b, hb, hodd, rfl⟩, ?_⟩
  rw [orderOf_conj_eq']; exact hodd

theorem normal_subgroupOf_of_forall_conj_mem {K Y : Subgroup X} (hYK : Y ≤ K)
    (hn : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) : (Y.subgroupOf K).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hYK).2 fun k hk => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hn k hk h, fun hh => ?_⟩
  have := hn k⁻¹ (K.inv_mem hk) _ hh
  simpa [mul_assoc] using this

end LiftBlock

section Lifted

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

structure IsLiftedBlock (T K Y : Subgroup X) : Prop where
  le : Y ≤ K
  norm : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y
  odd : Y ≤ Subgroup.closure {y : X | y ∈ Y ∧ Odd (orderOf y)}
  le_gnD : Y ≤ gnD T
  not_le_gnC : ¬ Y ≤ gnC T

theorem isLiftedBlock_liftBlock (hX : GNSetting X T) {K H Kb : Subgroup X} (hKb : Kb ≤ K)
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) (hblk : IsBlock2 H Kb) (hC : ¬ Kb ≤ gnC T) :
    IsLiftedBlock T K (liftBlock K Kb) := by
  have hKbD : Kb ≤ gnD T := le_gnD_iff.2 (commutator_pCoreOf_le_gnV_q hX hQH hblk hC)
  have := normal_gnD (X := X) T
  exact ⟨liftBlock_le hKb, fun k hk y hy => conj_mem_liftBlock hk hy,
    liftBlock_le_closure_odd K Kb, liftBlock_le_of_normal hKbD,
    fun h => hC ((le_liftBlock (CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.le_closure_odd_of_isShort2 hblk.1)).trans h)⟩

variable {K Y : Subgroup X}

omit [Finite X] in
theorem IsLiftedBlock.le_normalizer (hY : IsLiftedBlock T K Y) :
    K ≤ Subgroup.normalizer (Y : Set X) := fun k hk => by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hY.norm k hk h, fun hh => ?_⟩
  have := hY.norm k⁻¹ (K.inv_mem hk) _ hh
  simpa [mul_assoc] using this

omit [Finite X] in
theorem IsLiftedBlock.normal_subgroupOf (hY : IsLiftedBlock T K Y) : (Y.subgroupOf K).Normal :=
  normal_subgroupOf_of_forall_conj_mem hY.le hY.norm

theorem IsLiftedBlock.inf_le_pCoreOf_top (hX : GNSetting X T) (hY : IsLiftedBlock T K Y) :
    Y ⊓ gnC T ≤ pCoreOf 2 (⊤ : Subgroup X) :=
  (le_inf (inf_le_left.trans hY.le_gnD) inf_le_right).trans (centralizer_quot_inf_le hX)

theorem IsLiftedBlock.isPGroup_inf (hX : GNSetting X T) (hY : IsLiftedBlock T K Y) :
    IsPGroup 2 (Y ⊓ gnC T : Subgroup X) :=
  (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X)).to_le (hY.inf_le_pCoreOf_top hX)

omit [Finite X] in
theorem le_normalizer_inf_gnC (T Y : Subgroup X) :
    Y ≤ Subgroup.normalizer ((Y ⊓ gnC T : Subgroup X) : Set X) := fun g hg =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
    Subgroup.le_normalizer_of_normal (Subgroup.mem_top g)⟩

theorem IsLiftedBlock.inf_le_pCoreOf (hX : GNSetting X T) (hY : IsLiftedBlock T K Y) :
    Y ⊓ gnC T ≤ pCoreOf 2 Y :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (le_normalizer_inf_gnC T Y)
    (hY.isPGroup_inf hX)

end Lifted

section WithPhi

variable {X : Type} [Group X] [Finite X] {T K Y : Subgroup X} {n : ℕ}
  {Φ : ↥K →* alternatingGroup (Fin n)}

@[expose] def liftAlpha (hYK : Y ≤ K) (Φ : ↥K →* alternatingGroup (Fin n)) :
    ↥Y →* alternatingGroup (Fin n) :=
  Φ.comp (Subgroup.inclusion hYK)

omit [Finite X] in
theorem IsLiftedBlock.liftAlpha_surjective (hY : IsLiftedBlock T K Y) (h5 : 5 ≤ n)
    (hΦs : Function.Surjective Φ) (hΦk : ∀ k : ↥K, Φ k = 1 ↔ (k : X) ∈ gnC T) :
    Function.Surjective (liftAlpha hY.le Φ) := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact h5)
  have hN : ((Y.subgroupOf K).map Φ).Normal := hY.normal_subgroupOf.map Φ hΦs
  have hne : (Y.subgroupOf K).map Φ ≠ ⊥ := by
    intro h
    apply hY.not_le_gnC
    intro y hy
    have : Φ ⟨y, hY.le hy⟩ ∈ (Y.subgroupOf K).map Φ := Subgroup.mem_map_of_mem Φ hy
    rw [h, Subgroup.mem_bot] at this
    exact (hΦk _).1 this
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ hN with h | h
  · exact absurd h hne
  · intro σ
    have : σ ∈ (Y.subgroupOf K).map Φ := by rw [h]; trivial
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 this
    exact ⟨⟨k.1, hk⟩, rfl⟩

theorem IsLiftedBlock.pCoreOf_le_gnC (hY : IsLiftedBlock T K Y) (h5 : 5 ≤ n)
    (hΦs : Function.Surjective Φ) (hΦk : ∀ k : ↥K, Φ k = 1 ↔ (k : X) ∈ gnC T) :
    pCoreOf 2 Y ≤ gnC T := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact h5)
  have hP₂Y : pCoreOf 2 Y ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hP₂K : pCoreOf 2 Y ≤ K := hP₂Y.trans hY.le
  have hKnorm : K ≤ Subgroup.normalizer (pCoreOf 2 Y : Set X) :=
    hY.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hN : ((pCoreOf 2 Y).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP₂K).2 hKnorm
  have hNimg : (((pCoreOf 2 Y).subgroupOf K).map Φ).Normal := hN.map Φ hΦs
  have h2 : IsPGroup 2 (((pCoreOf 2 Y).subgroupOf K).map Φ) := by
    refine IsPGroup.map ?_ Φ
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).of_equiv
      (Subgroup.subgroupOfEquivOfLe hP₂K).symm
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ hNimg with h | h
  · intro y hy
    have : Φ ⟨y, hP₂K hy⟩ ∈ ((pCoreOf 2 Y).subgroupOf K).map Φ :=
      Subgroup.mem_map_of_mem Φ hy
    rw [h, Subgroup.mem_bot] at this
    exact (hΦk _).1 this
  · exfalso
    refine alt_not_two_group (by omega : 3 ≤ n) fun g => ?_
    have hg : g ∈ ((pCoreOf 2 Y).subgroupOf K).map Φ := by rw [h]; trivial
    obtain ⟨k, hk⟩ := h2 ⟨g, hg⟩
    exact ⟨k, congrArg Subtype.val hk⟩

theorem IsLiftedBlock.pCoreOf_eq (hX : GNSetting X T) (hY : IsLiftedBlock T K Y) (h5 : 5 ≤ n)
    (hΦs : Function.Surjective Φ) (hΦk : ∀ k : ↥K, Φ k = 1 ↔ (k : X) ∈ gnC T) :
    pCoreOf 2 Y = Y ⊓ gnC T :=
  le_antisymm (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) (hY.pCoreOf_le_gnC h5 hΦs hΦk))
    (hY.inf_le_pCoreOf hX)

theorem IsLiftedBlock.blockU_eq (hX : GNSetting X T) (hY : IsLiftedBlock T K Y) (h5 : 5 ≤ n)
    (hΦs : Function.Surjective Φ) (hΦk : ∀ k : ↥K, Φ k = 1 ↔ (k : X) ∈ gnC T)
    (hCK : gnC T ≤ K) : blockU Y = ⁅gnV T, Y⁆ := by
  have := normal_gnV (X := X) T
  have hVC : gnV T ≤ gnC T :=
    (gnV_le_pCoreOf hX).trans (CFSG.AGLEmbeddingD2.GN.pCoreOf_le_gnC hX)
  have hVK : gnV T ≤ K := hVC.trans hCK
  have hR2 := hY.isPGroup_inf hX
  have hV2 : IsPGroup 2 (gnV T) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X)).to_le (gnV_le_pCoreOf hX)
  have hVN : Y ≤ Subgroup.normalizer ((gnV T : Subgroup X) : Set X) :=
    Subgroup.le_normalizer_of_normal
  have hUV : ⁅Y ⊓ gnC T, Y⁆ ≤ gnV T :=
    (Subgroup.commutator_mono (hY.inf_le_pCoreOf_top hX) le_rfl).trans
      (le_gnD_iff.1 hY.le_gnD)
  have hVY : ⁅gnV T, Y⁆ ≤ Y ⊓ gnC T := by
    rw [Subgroup.commutator_le]
    intro v hv y hy
    refine ⟨?_, ?_⟩
    · have e : ⁅v, y⁆ = (v * y * v⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact Y.mul_mem (hY.norm v (hVK hv) y hy) (Y.inv_mem hy)
    · have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact (gnC T).mul_mem (hVC hv) (hVC (‹(gnV T).Normal›.conj_mem _ ((gnV T).inv_mem hv) y))
  rw [blockU, blockQ, hY.pCoreOf_eq hX h5 hΦs hΦk]
  refine le_antisymm ?_ ?_
  · exact ((commutator_le_commutator_commutator_of_odd hR2 (le_normalizer_inf_gnC T Y) hY.odd).trans
      (Subgroup.commutator_mono hUV le_rfl))
  · exact (commutator_le_commutator_commutator_of_odd hV2 hVN hY.odd).trans
      (Subgroup.commutator_mono hVY le_rfl)

end WithPhi

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

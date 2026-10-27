module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKCtx
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixTInvariant
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSevenSylow
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.HardMathSupport.Cooperstein.Proving.QuotientPCoreTransfer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

@[expose] def TwelveSixIMember : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ) (Q H L : Subgroup G) (n : ℕ),
    TwelveCtx G M p Q H → L ∈ weakBlockSet M H → Odd n → IsL3TwoPow n (modTwoCore L) →
      ∃ I : Subgroup G, cZero (H ⊓ L) = {I} ∧ IsPSLType 2 (GaloisField 2 n) (modTwoCore I)

variable {G : Type} [Group G] [Finite G]

structure TwelveSixIData (H L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ) where
  I₁ : Subgroup G
  I₂ : Subgroup G
  I₃ : Subgroup G
  V : Subgroup G
  W₁ : Subgroup G
  W₂ : Subgroup G
  W₃ : Subgroup G
  t₁ : G
  t₂ : G
  t₃ : G
  cZero₁ : cZero (H ⊓ L₁) = {I₁}
  cZero₂ : cZero (H ⊓ L₂) = {I₂}
  cZero₃ : cZero (H ⊓ L₃) = {I₃}
  type₁ : IsPSLType 2 (GaloisField 2 n₁) (modTwoCore I₁)
  type₂ : IsPSLType 2 (GaloisField 2 n₂) (modTwoCore I₂)
  type₃ : IsPSLType 2 (GaloisField 2 n₃) (modTwoCore I₃)
  le₁ : W₁ ≤ I₁
  le₂ : W₂ ≤ I₂
  le₃ : W₃ ≤ I₃
  mem₁ : t₁ ∈ I₁ ⊔ I₂ ⊔ I₃
  mem₂ : t₂ ∈ I₁ ⊔ I₂ ⊔ I₃
  mem₃ : t₃ ∈ I₁ ⊔ I₂ ⊔ I₃
  cfg : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃

namespace TwelveSixIData

private theorem isCZeroMember_map_conj_map {X I : Subgroup G} (h : IsCZeroMember X I) (g : G) :
    IsCZeroMember (X.map (MulAut.conj g).toMonoidHom)
      (I.map (MulAut.conj g).toMonoidHom) := by
  have hconj : ∀ Y : Subgroup G, pCoreOf 2 (Y.map (MulAut.conj g).toMonoidHom) =
      (pCoreOf 2 Y).map (MulAut.conj g).toMonoidHom :=
    fun Y => CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) Y
  refine ⟨Subgroup.map_mono h.le, h.subnormal.map _, ?_⟩
  rcases h.shape with ha | ⟨hp, hq⟩
  · left
    refine ⟨le_rfl, .refl _, ?_, ?_⟩
    · rw [← Subgroup.map_commutator, ha.perfect]
    · let ε := CFSG.HardMathSupport.Cooperstein.Proving.quotientPCoreMulEquiv 2
          ((MulAut.conj g).subgroupMap I)
      have hcomp := CFSG.isComponentOf_map_mulEquiv ε ha.component
      have hbar' : barM I I = ⊤ := by
        unfold barM
        rw [Subgroup.subgroupOf_self, Subgroup.map_top, QuotientGroup.range_mk']
      rw [hbar'] at hcomp
      rw [Subgroup.map_top_of_surjective ε.toMonoidHom ε.surjective] at hcomp
      have hbar : barM (I.map (MulAut.conj g).toMonoidHom)
          (I.map (MulAut.conj g).toMonoidHom) = ⊤ := by
        unfold barM
        rw [Subgroup.subgroupOf_self, Subgroup.map_top, QuotientGroup.range_mk']
      rw [hbar]
      exact hcomp
  · right
    refine ⟨?_, ?_⟩
    · rw [hconj I, hp, ← hconj X]
    · exact IsSymThreeOrSUThreeTwo.of_mulEquiv
        (CFSG.HardMathSupport.Cooperstein.Proving.quotientPCoreMulEquiv 2
          ((MulAut.conj g).subgroupMap I)) hq

private theorem mem_three_of_mem_cZero {H L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {L I : Subgroup G}
    (hL : L ∈ ({L₁, L₂, L₃} : Set (Subgroup G))) (hI : I ∈ cZero (H ⊓ L)) :
    I ∈ ({D.I₁, D.I₂, D.I₃} : Set (Subgroup G)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL
  rcases hL with rfl | rfl | rfl
  · rw [D.cZero₁, Set.mem_singleton_iff] at hI
    rw [hI]
    simp
  · rw [D.cZero₂, Set.mem_singleton_iff] at hI
    rw [hI]
    simp
  · rw [D.cZero₃, Set.mem_singleton_iff] at hI
    rw [hI]
    simp

private theorem map_conj_mem_I {H L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}
    {M : Subgroup G} {d : ℕ} (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) {g : G} (hg : g ∈ H ⊓ M)
    {I : Subgroup G} (hI : I ∈ ({D.I₁, D.I₂, D.I₃} : Set (Subgroup G))) :
    I.map (MulAut.conj g).toMonoidHom ∈ ({D.I₁, D.I₂, D.I₃} : Set (Subgroup G)) := by
  have hHg : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg.1)
  have key : ∀ (X I : Subgroup G), IsCZeroMember (H ⊓ X) I →
      X ∈ ({L₁, L₂, L₃} : Set (Subgroup G)) →
      I.map (MulAut.conj g).toMonoidHom ∈ ({D.I₁, D.I₂, D.I₃} : Set (Subgroup G)) := by
    intro X I hXI hX
    have hXmap : (H ⊓ X).map (MulAut.conj g).toMonoidHom =
        H ⊓ X.map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hHg]
    have htr := isCZeroMember_map_conj_map hXI g
    rw [hXmap] at htr
    exact mem_three_of_mem_cZero D (TwelveFiveData.map_conj_mem hd hg.2 hX) htr
  rcases hI with rfl | rfl | rfl
  · have hcz : IsCZeroMember (H ⊓ L₁) D.I₁ := by
      change D.I₁ ∈ cZero (H ⊓ L₁)
      rw [D.cZero₁]
      exact Set.mem_singleton _
    exact key L₁ D.I₁ hcz (by simp)
  · have hcz : IsCZeroMember (H ⊓ L₂) D.I₂ := by
      change D.I₂ ∈ cZero (H ⊓ L₂)
      rw [D.cZero₂]
      exact Set.mem_singleton _
    exact key L₂ D.I₂ hcz (by simp)
  · have hcz : IsCZeroMember (H ⊓ L₃) D.I₃ := by
      change D.I₃ ∈ cZero (H ⊓ L₃)
      rw [D.cZero₃]
      exact Set.mem_singleton _
    exact key L₃ D.I₃ hcz (by simp)

private theorem isSubnormal_of_le_jSub {H L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}
    {M : Subgroup G} {d : ℕ} (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    {L I : Subgroup G} (hLJ : L ≤ jSub M H)
    (hJN : jSub M H ≤ Subgroup.normalizer (L : Set G))
    (hI : CFSG.Open.IsSubnormal I (H ⊓ L)) :
    CFSG.Open.IsSubnormal I (H ⊓ M) := by
  have hle₁ : H ⊓ L ≤ H ⊓ jSub M H := inf_le_inf_left H hLJ
  have hle₂ : H ⊓ jSub M H ≤ H ⊓ M := inf_le_inf_left H (jSub_le M H)
  have hnorm₁ : H ⊓ jSub M H ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := by
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg.1, hJN hg.2⟩
  have hnorm₂ : H ⊓ M ≤ Subgroup.normalizer ((H ⊓ jSub M H : Subgroup G) : Set G) := by
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg.1, TwelveFiveData.le_normalizer_jSub hd hg.2⟩
  have hstep₁ : CFSG.Open.IsSubnormal (H ⊓ L) (H ⊓ jSub M H) :=
    .step hle₁ ((Subgroup.normal_subgroupOf_iff_le_normalizer hle₁).mpr hnorm₁) (.refl _)
  have hstep₂ : CFSG.Open.IsSubnormal (H ⊓ jSub M H) (H ⊓ M) :=
    .step hle₂ ((Subgroup.normal_subgroupOf_iff_le_normalizer hle₂).mpr hnorm₂) (.refl _)
  exact hI.trans (hstep₁.trans hstep₂)

variable {H L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ} (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)

theorem isCZeroMember₁ : IsCZeroMember (H ⊓ L₁) D.I₁ := by
  change D.I₁ ∈ cZero (H ⊓ L₁)
  rw [D.cZero₁]
  exact Set.mem_singleton _

theorem isCZeroMember₂ : IsCZeroMember (H ⊓ L₂) D.I₂ := by
  change D.I₂ ∈ cZero (H ⊓ L₂)
  rw [D.cZero₂]
  exact Set.mem_singleton _

theorem isCZeroMember₃ : IsCZeroMember (H ⊓ L₃) D.I₃ := by
  change D.I₃ ∈ cZero (H ⊓ L₃)
  rw [D.cZero₃]
  exact Set.mem_singleton _

theorem le_inf₁ : D.I₁ ≤ H ⊓ L₁ := D.isCZeroMember₁.le

theorem le_inf₂ : D.I₂ ≤ H ⊓ L₂ := D.isCZeroMember₂.le

theorem le_inf₃ : D.I₃ ≤ H ⊓ L₃ := D.isCZeroMember₃.le

theorem V_le : D.V ≤ D.I₁ ⊔ D.I₂ ⊔ D.I₃ := by
  rw [D.cfg.join]
  have h12 : D.W₁ ⊔ D.W₂ ≤ D.I₁ ⊔ D.I₂ :=
    _root_.sup_le (D.le₁.trans le_sup_left) (D.le₂.trans le_sup_right)
  exact _root_.sup_le (h12.trans le_sup_left) (D.le₃.trans le_sup_right)

variable {M : Subgroup G} {d : ℕ}

theorem sup_le (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    D.I₁ ⊔ D.I₂ ⊔ D.I₃ ≤ H ⊓ M := by
  have hH : D.I₁ ⊔ D.I₂ ⊔ D.I₃ ≤ H :=
    _root_.sup_le
      (_root_.sup_le (D.le_inf₁.trans inf_le_left) (D.le_inf₂.trans inf_le_left))
      (D.le_inf₃.trans inf_le_left)
  have hM : D.I₁ ⊔ D.I₂ ⊔ D.I₃ ≤ M :=
    _root_.sup_le
      (_root_.sup_le ((D.le_inf₁.trans inf_le_right).trans hd.mem₁.le)
        ((D.le_inf₂.trans inf_le_right).trans hd.mem₂.le))
      ((D.le_inf₃.trans inf_le_right).trans hd.mem₃.le)
  exact le_inf hH hM

theorem t₁_mem (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) : D.t₁ ∈ H ⊓ M :=
  (D.sup_le hd) D.mem₁

theorem t₂_mem (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) : D.t₂ ∈ H ⊓ M :=
  (D.sup_le hd) D.mem₂

theorem t₃_mem (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) : D.t₃ ∈ H ⊓ M :=
  (D.sup_le hd) D.mem₃

theorem isSubnormal₁ (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    CFSG.Open.IsSubnormal D.I₁ (H ⊓ M) :=
  isSubnormal_of_le_jSub hd (le_jSub hd.mem₁) (TwelveFiveData.jSub_le_normalizer_left hd)
    D.isCZeroMember₁.subnormal

theorem isSubnormal₂ (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    CFSG.Open.IsSubnormal D.I₂ (H ⊓ M) :=
  isSubnormal_of_le_jSub hd (le_jSub hd.mem₂) (TwelveFiveData.jSub_le_normalizer_middle hd)
    D.isCZeroMember₂.subnormal

theorem isSubnormal₃ (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    CFSG.Open.IsSubnormal D.I₃ (H ⊓ M) :=
  isSubnormal_of_le_jSub hd (le_jSub hd.mem₃) (TwelveFiveData.jSub_le_normalizer_right hd)
    D.isCZeroMember₃.subnormal

theorem le_normalizer (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    H ⊓ M ≤ normalizer ((D.I₁ ⊔ D.I₂ ⊔ D.I₃ : Subgroup G) : Set G) := by
  intro g hg
  have hmem : ∀ K ∈ ({D.I₁, D.I₂, D.I₃} : Set (Subgroup G)),
      K.map (MulAut.conj g).toMonoidHom ∈ ({D.I₁, D.I₂, D.I₃} : Set (Subgroup G)) :=
    fun K hK => map_conj_mem_I D hd hg hK
  have hmem' : ∀ K ∈ ({D.I₁, D.I₂, D.I₃} : Set (Subgroup G)),
      K.map (MulAut.conj g⁻¹).toMonoidHom ∈ ({D.I₁, D.I₂, D.I₃} : Set (Subgroup G)) :=
    fun K hK => map_conj_mem_I D hd (Subgroup.inv_mem _ hg) hK
  have h := CFSG.Walter.mem_normalizer_sSup_of_map_mem hmem hmem'
  have hsup : sSup ({D.I₁, D.I₂, D.I₃} : Set (Subgroup G)) = D.I₁ ⊔ D.I₂ ⊔ D.I₃ := by
    simp [sSup_insert, sSup_singleton, sup_assoc]
  simpa [hsup] using h

variable {p : ℕ} {Q : Subgroup G}

theorem centralizer_le₁ (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃) :
    centralizer (D.W₁ : Set G) ≤ M :=
  hc.hC L₁ D.W₁ hc.data.mem₁ D.cfg.card₁ (D.le₁.trans (D.le_inf₁.trans inf_le_right))

theorem centralizer_le₂ (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃) :
    centralizer (D.W₂ : Set G) ≤ M :=
  hc.hC L₂ D.W₂ hc.data.mem₂ D.cfg.card₂ (D.le₂.trans (D.le_inf₂.trans inf_le_right))

theorem centralizer_le₃ (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃) :
    centralizer (D.W₃ : Set G) ≤ M :=
  hc.hC L₃ D.W₃ hc.data.mem₃ D.cfg.card₃ (D.le₃.trans (D.le_inf₃.trans inf_le_right))

end TwelveSixIData

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end

module

public import CFSG.CGT.Foote82.ChiefBridge
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.CGT.Foote82.EF2
import CFSG.LocalAnalysis.WeakClosure81.Eleven
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTI

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19.SimsTheoremC
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_isPGroup_of_block {K : Subgroup G} (hK : IsFooteBlock K K) : ¬ IsPGroup 2 K := by
  intro h2
  have htop : CFSG.pCore 2 ↥K = ⊤ :=
    le_antisymm le_top (le_sSup ⟨inferInstance, h2.of_equiv Subgroup.topEquiv.symm⟩)
  haveI := hK.quasisimple.2.toNontrivial
  have hsub : Subsingleton (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  have : Subsingleton ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    Quotient.instSubsingletonQuotient _
  exact not_subsingleton _ this

theorem lt_inf_normalizer {P T : Subgroup G} (hPT : P < T) (hT : IsPGroup 2 T) :
    P < T ⊓ Subgroup.normalizer (P : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  have hlt : P.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hPT.ne (le_antisymm hPT.le fun t ht => by
      have : (⟨t, ht⟩ : ↥T) ∈ P.subgroupOf T := h ▸ Subgroup.mem_top _
      exact this)
  have hn := Group.normalizerCondition_of_isNilpotent (G := ↥T) _ hlt
  obtain ⟨t, htN, htP⟩ := SetLike.exists_of_lt hn
  refine lt_of_le_of_ne (le_inf hPT.le Subgroup.le_normalizer) fun he => htP ?_
  have htN' : (t : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ T
    · have := Subgroup.mem_normalizer_iff.mp htN ⟨g, hg⟩
      exact this
    · constructor
      · intro hgP; exact absurd (hPT.le hgP) hg
      · intro hgP
        exfalso
        apply hg
        have h1 : (t : G) * g * (t : G)⁻¹ ∈ T := hPT.le hgP
        have : g = (t : G)⁻¹ * ((t : G) * g * (t : G)⁻¹) * t := by group
        rw [this]
        exact T.mul_mem (T.mul_mem (T.inv_mem t.2) h1) t.2
  have : (t : G) ∈ P := he ▸ ⟨t.2, htN'⟩
  exact this

theorem mem_centralizerModTwoCore_iff {K : Subgroup G} {x : G} :
    x ∈ centralizerModTwoCore K ↔
      x ∈ Subgroup.normalizer (K : Set G) ∧ ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
  refine ⟨fun hx => ?_, fun hx => Subgroup.subset_closure hx⟩
  have hN := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.normalizer_le_normalizer_pCoreOf K
  have hx' : x ∈ Subgroup.closure {g : G | g ∈ Subgroup.normalizer (K : Set G) ∧
      ∀ y ∈ K, g * y * g⁻¹ * y⁻¹ ∈ pCoreOf 2 K} := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem g hg => exact hg
  | one => exact ⟨one_mem _, fun y _ => by simpa using (pCoreOf 2 K).one_mem⟩
  | mul a b _ _ iha ihb =>
    refine ⟨mul_mem iha.1 ihb.1, fun y hy => ?_⟩
    have e : a * b * y * (a * b)⁻¹ * y⁻¹ =
        a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ * (a * y * a⁻¹ * y⁻¹) := by group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hN iha.1) _).mp (ihb.2 y hy)) (iha.2 y hy)
  | inv a _ iha =>
    refine ⟨inv_mem iha.1, fun y hy => ?_⟩
    have hy' : a⁻¹ * y * a ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem iha.1) y).mp hy
      simpa using this
    have h := iha.2 _ hy'
    have e : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = (a * (a⁻¹ * y * a) * a⁻¹ * (a⁻¹ * y * a)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h

theorem blockU_le_core {N K : Subgroup G} (hK : IsFooteBlock K K) (hKN : K ≤ N)
    (hfaith : N ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) ≤ pCoreOf 2 N)
    (hHK : pCoreOf 2 N ≤ Subgroup.normalizer (K : Set G)) (hc : ⁅pCoreOf 2 N, K⁆ ≤ blockQ K) :
    blockU K ≤ pCoreOf 2 N := by
  set H := pCoreOf 2 N with hHdef
  have hNH : N ≤ Subgroup.normalizer (H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N
  have hA : blockU K ⊓ H ≤ K := inf_le_left.trans (blockU_le_self K)
  have hKA : K ≤ Subgroup.normalizer ((blockU K ⊓ H : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K hk) x
    have h2 := Subgroup.mem_normalizer_iff.mp (hNH (hKN hk)) x
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  rcases IsFooteBlock.le_centralizer_or_blockU_le hK hA hKA with hcen | hU
  · exfalso
    have hKH : ⁅K, H⁆ ≤ blockU K ⊓ H := by
      refine le_inf (IsFooteBlock.commutator_le_blockU hK hHK hc) ?_
      refine (Subgroup.commutator_le).mpr fun k hk h hh => ?_
      have e : ⁅k, h⁆ = (k * h * k⁻¹) * h⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact H.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNH (hKN hk)) h).mp hh) (H.inv_mem hh)
    have h1 : ⁅⁅K, H⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hKH.trans hcen
    have h2 : ⁅⁅H, K⁆, K⁆ = ⊥ := by rwa [Subgroup.commutator_comm H K]
    have h3 : ⁅⁅K, K⁆, H⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [IsFooteBlock.commutator_eq hK] at h3
    have hKC : K ≤ N ⊓ Subgroup.centralizer (H : Set G) :=
      le_inf hKN ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp h3)
    exact not_isPGroup_of_block hK
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N).to_le (hKC.trans hfaith))
  · exact hU.trans inf_le_right

theorem map_conj_eq_of_mem_normalizer {K : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (K : Set G)) : K.map (MulAut.conj c).toMonoidHom = K := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hc y).mp hy
  · intro hx
    refine ⟨c⁻¹ * x * c, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) x).mp hx
    simpa using this

theorem le_normalizer_of_commutator_le {K P : Subgroup G} (hQP : blockQ K ≤ P)
    (hc : ⁅P, K⁆ ≤ blockQ K) : K ≤ Subgroup.normalizer (P : Set G) := by
  have key : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P := by
    intro k hk p hp
    have h1 : ⁅k, p⁆ ∈ blockQ K := by
      have := Subgroup.commutator_mem_commutator hk hp
      rw [Subgroup.commutator_comm] at this
      exact hc this
    have e : k * p * k⁻¹ = ⁅k, p⁆ * p := by rw [commutatorElement_def]; group
    rw [e]
    exact P.mul_mem (hQP h1) hp
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨key k hk p, fun hp => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hp
  simpa [mul_assoc] using this

@[expose] def EF1Class (K P : Subgroup G) : Prop :=
  IsPGroup 2 P ∧ blockQ K ≤ P ∧ P ≤ centralizerModTwoCore K ∧
    ∃ N : Subgroup G, GLBIsMaxTwoLocal N ∧ K ⊔ P ≤ N ∧ ¬ IsSubnormal K N

theorem exists_maximal_ef1Class {K N : Subgroup G} (hK : IsFooteBlock K K)
    (hN : GLBIsMaxTwoLocal N) (hKN : K ≤ N) (hsub : ¬ IsSubnormal K N) :
    ∃ P, EF1Class K P ∧ ∀ P', EF1Class K P' → P ≤ P' → P' = P := by
  have hQ2 : IsPGroup 2 (blockQ K) := C1.blockQ_isPGroup K
  have hQC : blockQ K ≤ centralizerModTwoCore K := by
    intro q hq
    refine mem_centralizerModTwoCore_iff.mpr ⟨Subgroup.le_normalizer (C1.blockQ_le K hq),
      fun y hy => ?_⟩
    have hq' : q * y * q⁻¹ ∈ K := by
      have hqK := C1.blockQ_le K hq
      exact K.mul_mem (K.mul_mem hqK hy) (K.inv_mem hqK)
    have : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
    rw [this]
    exact (blockQ K).mul_mem hq ((Subgroup.mem_normalizer_iff.mp
      (C1.le_normalizer_blockQ K hy) _).mp ((blockQ K).inv_mem hq))
  have hKQ : K ⊔ blockQ K = K := sup_eq_left.mpr (C1.blockQ_le K)
  have h0 : EF1Class K (blockQ K) := ⟨hQ2, le_rfl, hQC, N, hN, by rw [hKQ]; exact hKN, hsub⟩
  obtain ⟨P, -, hPmax⟩ := Set.Finite.exists_le_maximal (Set.toFinite {P | EF1Class K P}) h0
  exact ⟨P, hPmax.1, fun P' hP' hPP' => (le_antisymm (hPmax.2 hP' hPP') hPP')⟩

theorem blockU_le_blockQ (K : Subgroup G) : blockU K ≤ blockQ K := by
  refine (Subgroup.commutator_le).mpr fun q hq k hk => ?_
  have e : ⁅q, k⁆ = q * (k * q⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact (blockQ K).mul_mem hq ((Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockQ K hk) _).mp
    ((blockQ K).inv_mem hq))

namespace EF1Class

variable {K P : Subgroup G} (hP : EF1Class K P)
include hP

theorem le_normalizer : P ≤ Subgroup.normalizer (K : Set G) := fun _ hp =>
  (mem_centralizerModTwoCore_iff.mp (hP.2.2.1 hp)).1

theorem commutator_le : ⁅P, K⁆ ≤ blockQ K :=
  (Subgroup.commutator_le).mpr fun p hp k hk => by
    rw [commutatorElement_def]
    exact (mem_centralizerModTwoCore_iff.mp (hP.2.2.1 hp)).2 k hk

theorem K_le_normalizer : K ≤ Subgroup.normalizer (P : Set G) :=
  le_normalizer_of_commutator_le hP.2.1 hP.commutator_le

theorem ne_bot (hK : IsFooteBlock K K) : P ≠ ⊥ := by
  intro hbot
  obtain ⟨u, hu, hz⟩ := SetLike.exists_of_lt hK.chief.1
  have hu1 : u = 1 := by
    have := hP.2.1 (blockU_le_blockQ K hu)
    rw [hbot] at this
    exact (Subgroup.mem_bot).mp this
  exact hz (hu1 ▸ Subgroup.one_mem _)

end EF1Class

theorem ef1_isSubnormal_normalizer {K P : Subgroup G} (hKB : InFooteB K) (hP : EF1Class K P)
    (hPmax : ∀ P', EF1Class K P' → P ≤ P' → P' = P) :
    IsSubnormal K (Subgroup.normalizer (P : Set G)) := by
  obtain ⟨S, hS, hSK⟩ := hKB
  have hK : IsFooteBlock K K := IsFooteBlock.self hSK
  obtain ⟨T, hPT, hT⟩ := exists_isSylowTwoOf_of_le hP.2.2.1 hP.1
  by_cases hPeq : P = T
  · subst hPeq
    obtain ⟨c, hcC, hPc⟩ := hS.exists_conj hT
    have hcK : c ∈ Subgroup.normalizer (K : Set G) := (mem_centralizerModTwoCore_iff.mp hcC).1
    have h1 := CFSG.Open.IsSubnormal.map (MulAut.conj c).toMonoidHom hSK.subnormal
    rwa [map_conj_eq_of_mem_normalizer hcK, Subgroup.map_equiv_normalizer_eq, ← hPc] at h1
  · have hlt : P < T := lt_of_le_of_ne hPT hPeq
    have hPstar := lt_inf_normalizer hlt hT.isPGroup
    set Pst := T ⊓ Subgroup.normalizer (P : Set G) with hPst
    have hPstC : Pst ≤ centralizerModTwoCore K := inf_le_left.trans hT.le
    have hall : ∀ N', GLBIsMaxTwoLocal N' → K ⊔ Pst ≤ N' → IsSubnormal K N' := by
      intro N' hN' hle
      by_contra hns
      have hcl : EF1Class K Pst :=
        ⟨hT.isPGroup.to_le inf_le_left, hP.2.1.trans hPstar.le, hPstC, N', hN', hle, hns⟩
      exact hPstar.ne (hPmax Pst hcl hPstar.le).symm
    have h2l : IsTwoLocal (Subgroup.normalizer (P : Set G)) := ⟨P, hP.ne_bot hK, hP.1, rfl⟩
    obtain ⟨M, hM, hPM⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_isMaxTwoLocalSubgroup_le h2l
    have hKPst : K ⊔ Pst ≤ Subgroup.normalizer (P : Set G) := sup_le hP.K_le_normalizer inf_le_right
    have hsubM := hall M hM (hKPst.trans hPM)
    have := CFSG.Open.IsSubnormal.inf_of_le hsubM hPM
    rwa [inf_eq_left.mpr hP.K_le_normalizer] at this

theorem mem_centralizerModTwoCore_of_isFooteBlock {X L N : Subgroup G} (hL : IsFooteBlock X L)
    (hLN : L ≤ N) {h : G} (hhH : h ∈ pCoreOf 2 N) (hhX : h ∈ Subgroup.normalizer (X : Set G)) :
    h ∈ centralizerModTwoCore L := by
  have hK : IsFooteBlock L L := IsFooteBlock.self hL
  have hNH : N ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N
  have hhN : h ∈ N := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 N hhH
  have hKh := isFooteBlock_map hL (MulAut.conj h)
  rw [map_conj_eq_of_mem_normalizer hhX] at hKh
  by_cases hne : L = L.map (MulAut.conj h).toMonoidHom
  ·
    have hhK : h ∈ Subgroup.normalizer (L : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [hne]
        exact ⟨y, hy, rfl⟩
      · intro hy
        rw [hne] at hy
        obtain ⟨y', hy', hyy'⟩ := hy
        have : y' = y := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyy'
          exact mul_left_cancel (mul_right_cancel hyy')
        exact this ▸ hy'
    refine mem_centralizerModTwoCore_iff.mpr ⟨hhK, fun y hy => ?_⟩
    have hKH : L ⊓ pCoreOf 2 N ≤ pCoreOf 2 L :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ L inf_le_left
        ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk => by
          rw [Subgroup.mem_normalizer_iff]
          intro x
          have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) x
          have h2 := Subgroup.mem_normalizer_iff.mp (hNH (hLN hk)) x
          exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩)
        ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N).to_le inf_le_right)
    refine hKH ⟨?_, ?_⟩
    · exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hhK y).mp hy) (L.inv_mem hy)
    · have e : h * y * h⁻¹ * y⁻¹ = h * (y * h⁻¹ * y⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 N).mul_mem hhH ((Subgroup.mem_normalizer_iff.mp (hNH (hLN hy)) _).mp
        ((pCoreOf 2 N).inv_mem hhH))
  · exfalso
    have hcomm := blocks_commute hL hKh hne
    have hab : ∀ a b : ↥(hatIn N L), a * b = b * a := by
      rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have hx' : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hx
      have hy' : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
      have hyh : h * y * h⁻¹ ∈ L.map (MulAut.conj h).toMonoidHom := ⟨y, hy', rfl⟩
      have hxy : (x : G) * (h * y * h⁻¹) = h * y * h⁻¹ * x :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx' _ hyh |>.symm
      have hyN : h * (y : G) * h⁻¹ ∈ N := N.mul_mem (N.mul_mem hhN y.2) (N.inv_mem hhN)
      have hθ : (QuotientGroup.mk ⟨h * y * h⁻¹, hyN⟩ : NHat N) = QuotientGroup.mk y := by
        rw [mk_eq_mk_iff]
        have e : (h * (y : G) * h⁻¹)⁻¹ * y = h * ((y : G)⁻¹ * h⁻¹ * (y : G)) := by group
        show (h * (y : G) * h⁻¹)⁻¹ * y ∈ pCoreOf 2 N
        rw [e]
        have h1 := (Subgroup.mem_normalizer_iff.mp (hNH (N.inv_mem y.2)) _).mp
          ((pCoreOf 2 N).inv_mem hhH)
        simp only [Subgroup.coe_inv, inv_inv] at h1
        exact (pCoreOf 2 N).mul_mem hhH h1
      show (QuotientGroup.mk x : NHat N) * QuotientGroup.mk y =
        QuotientGroup.mk y * QuotientGroup.mk x
      rw [← hθ, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hxy
    have hperf : ⁅hatIn N L, hatIn N L⁆ = hatIn N L := by
      haveI := isPerfect_of_block hK
      exact commutator_eq_of_isPerfect (Group.IsPerfect.ofSurjective (hatMap_surjective hLN))
    have hbot : hatIn N L = ⊥ := by
      rw [← hperf, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hab ⟨b, hb⟩ ⟨a, ha⟩)
    have hKH : L ≤ pCoreOf 2 N := by
      intro k hk
      have : (QuotientGroup.mk ⟨k, hLN hk⟩ : NHat N) ∈ hatIn N L :=
        ⟨⟨k, hLN hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact (mk_eq_one_iff _).mp this
    exact not_isPGroup_of_block hK
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N).to_le hKH)

theorem ef1_mem_centralizerModTwoCore {K P N : Subgroup G} (hKB : InFooteB K) (hP : EF1Class K P)
    (hPmax : ∀ P', EF1Class K P' → P ≤ P' → P' = P) (hKN : K ≤ N) {h : G}
    (hhH : h ∈ pCoreOf 2 N) (hhP : h ∈ Subgroup.normalizer (P : Set G)) :
    h ∈ centralizerModTwoCore K := by
  have hK : IsFooteBlock K K := by obtain ⟨S, -, hSK⟩ := hKB; exact IsFooteBlock.self hSK
  have hKblock : IsFooteBlock (Subgroup.normalizer (P : Set G)) K :=
    { le := hP.K_le_normalizer
      subnormal := ef1_isSubnormal_normalizer hKB hP hPmax
      residual := hK.residual
      quasisimple := hK.quasisimple
      chief := hK.chief }
  exact mem_centralizerModTwoCore_of_isFooteBlock hKblock hKN hhH (Subgroup.le_normalizer hhP)

theorem ef1_core_le {K P N : Subgroup G} (hKB : InFooteB K) (hP : EF1Class K P)
    (hPmax : ∀ P', EF1Class K P' → P ≤ P' → P' = P) (hN : GLBIsMaxTwoLocal N)
    (hKPN : K ⊔ P ≤ N) (hsub : ¬ IsSubnormal K N) : pCoreOf 2 N ≤ P := by
  have hKN : K ≤ N := le_sup_left.trans hKPN
  have hPN : P ≤ N := le_sup_right.trans hKPN
  have hH2 := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N
  have hNH : N ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N
  by_contra hHP
  have hPH2 : IsPGroup 2 ↥(P ⊔ pCoreOf 2 N) :=
    IsPGroup.to_sup_of_normal_right' hP.1 hH2 (hPN.trans hNH)
  have hlt : P < P ⊔ pCoreOf 2 N :=
    lt_of_le_of_ne le_sup_left fun he => hHP (he ▸ le_sup_right)
  have hPR := lt_inf_normalizer hlt hPH2
  set R := (P ⊔ pCoreOf 2 N) ⊓ Subgroup.normalizer (P : Set G) with hRdef
  have hRC : R ≤ centralizerModTwoCore K := by
    intro x hx
    have hx' : x ∈ ((P ⊔ pCoreOf 2 N : Subgroup G) : Set G) := hx.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P (pCoreOf 2 N) (hPN.trans hNH)] at hx'
    obtain ⟨p, hp, k, hk, rfl⟩ := hx'
    have hpN : p ∈ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer hp
    have hkP : k ∈ Subgroup.normalizer (P : Set G) := by
      have : k = p⁻¹ * (p * k) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hpN) hx.2
    exact Subgroup.mul_mem _ (hP.2.2.1 hp)
      (ef1_mem_centralizerModTwoCore hKB hP hPmax hKN hk hkP)
  have hR2 : IsPGroup 2 ↥R := hPH2.to_le inf_le_left
  have hKRN : K ⊔ R ≤ N := sup_le hKN (inf_le_left.trans (sup_le hPN
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 N)))
  have hcl : EF1Class K R := ⟨hR2, hP.2.1.trans hPR.le, hRC, N, hN, hKRN, hsub⟩
  exact hPR.ne (hPmax R hcl hPR.le).symm

theorem ef1_chiefHyp (hG : IsCharTwoType G) {K P N : Subgroup G} (hKB : InFooteB K)
    (hKF : IsFType K) (hP : EF1Class K P) (hPmax : ∀ P', EF1Class K P' → P ≤ P' → P' = P)
    (hN : GLBIsMaxTwoLocal N) (hKPN : K ⊔ P ≤ N) (hsub : ¬ IsSubnormal K N) :
    ChiefHyp N K P := by
  have hK : IsFooteBlock K K := by obtain ⟨S, -, hSK⟩ := hKB; exact IsFooteBlock.self hSK
  have hKN : K ≤ N := le_sup_left.trans hKPN
  have hPN : P ≤ N := le_sup_right.trans hKPN
  have hfaith : N ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) ≤ pCoreOf 2 N := hG N hN.1
  have hHP := ef1_core_le hKB hP hPmax hN hKPN hsub
  have hsubN : IsSubnormal K (N ⊓ Subgroup.normalizer (P : Set G)) := by
    have := CFSG.Open.IsSubnormal.inf_of_le (ef1_isSubnormal_normalizer hKB hP hPmax)
      (inf_le_right : N ⊓ Subgroup.normalizer (P : Set G) ≤ _)
    rwa [inf_eq_left.mpr (le_inf hKN hP.K_le_normalizer)] at this
  exact
    { faithful := hfaith
      block := hK
      ftype := hKF
      two := hP.1
      core_le := hHP
      le := hPN
      normalizes := hP.le_normalizer
      cent := hP.commutator_le
      blockU_le := blockU_le_core hK hKN hfaith (hHP.trans hP.le_normalizer)
        ((Subgroup.commutator_mono hHP le_rfl).trans hP.commutator_le)
      subnormal := hsubN }

end CFSG.CGT.Foote82

module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.LieType.ChevTwo.Defs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.GLTheoremB.I2810.StronglyRealAut

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LieType.ChevTwo
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

namespace SRInd

section Ind
variable {X : Type} [Group X] {W K : Subgroup X} [W.Normal]

theorem mk_mem_normalizer_bar {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X)) :
    (QuotientGroup.mk b : X ⧸ W) ∈
      Subgroup.normalizer ((bar W K : Subgroup (X ⧸ W)) : Set (X ⧸ W)) :=
  K.le_normalizer_map (QuotientGroup.mk' W) (Subgroup.mem_map_of_mem _ hb)

@[expose] noncomputable def mkN (W K : Subgroup X) [W.Normal] :
    ↥(Subgroup.normalizer (K : Set X)) →*
      ↥(Subgroup.normalizer ((bar W K : Subgroup (X ⧸ W)) : Set (X ⧸ W))) where
  toFun b := ⟨QuotientGroup.mk (b : X), mk_mem_normalizer_bar b.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[expose] noncomputable def indHom (W K : Subgroup X) [W.Normal] :
    ↥(Subgroup.normalizer (K : Set X)) →* MulAut ↥(bar W K) :=
  (bar W K).normalizerMonoidHom.comp (mkN W K)

theorem indHom_toBar (b : ↥(Subgroup.normalizer (K : Set X))) (k : ↥K)
    (hk : (b : X) * k * (b : X)⁻¹ ∈ K) :
    indHom W K b (toBar W K k) = toBar W K ⟨(b : X) * k * (b : X)⁻¹, hk⟩ := rfl

theorem mem_indAut_iff' {B : Subgroup X} (hB : B ≤ Subgroup.normalizer (K : Set X))
    (α : MulAut ↥(bar W K)) :
    α ∈ indAut W K B ↔
      ∃ b : ↥(Subgroup.normalizer (K : Set X)), (b : X) ∈ B ∧ indHom W K b = α := by
  constructor
  · intro hα
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hα
    obtain ⟨b, hb, hbg⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
    refine ⟨⟨b, hB hb⟩, hb, ?_⟩
    have : mkN W K ⟨b, hB hb⟩ = g := Subtype.ext hbg
    show (bar W K).normalizerMonoidHom (mkN W K ⟨b, hB hb⟩) = _
    rw [this]
  · rintro ⟨b, hb, rfl⟩
    exact Subgroup.mem_map.2 ⟨mkN W K b, Subgroup.mem_subgroupOf.2 ⟨b, hb, rfl⟩, rfl⟩

theorem indAut_isElemAbelian {A : Subgroup X} (hAN : A ≤ Subgroup.normalizer (K : Set X))
    (hA : IsElemAbelian 2 A) : IsElemAbelian 2 (indAut W K A) := by
  refine ⟨⟨⟨fun α β => ?_⟩⟩, fun α hα => ?_⟩
  · obtain ⟨a, haA, ha⟩ := (mem_indAut_iff' hAN α.1).1 α.2
    obtain ⟨b, hbA, hb⟩ := (mem_indAut_iff' hAN β.1).1 β.2
    apply Subtype.ext
    show (α : MulAut ↥(bar W K)) * β = β * α
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA.comm haA hbA)
  · obtain ⟨a, haA, rfl⟩ := (mem_indAut_iff' hAN α).1 hα
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hA.2 a haA)
    rw [this, map_one]

theorem indHom_eq_one_iff (b : ↥(Subgroup.normalizer (K : Set X))) :
    indHom W K b = 1 ↔ ∀ k ∈ K, ⁅(b : X), k⁆ ∈ W := by
  constructor
  · intro h k hk
    have h1 : (QuotientGroup.mk (b : X) : X ⧸ W) * QuotientGroup.mk k *
        (QuotientGroup.mk (b : X))⁻¹ = QuotientGroup.mk k := by
      have := congrArg (fun f : MulAut ↥(bar W K) =>
        ((f (toBar W K ⟨k, hk⟩) : ↥(bar W K)) : X ⧸ W)) h
      exact this
    have h2 : (QuotientGroup.mk ((b : X) * k * (b : X)⁻¹ * k⁻¹) : X ⧸ W) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [h1, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).1 h2
  · intro h
    refine MulEquiv.ext fun y => ?_
    obtain ⟨y', k, hk, rfl⟩ := y
    refine Subtype.ext ?_
    have h1 : (QuotientGroup.mk ((b : X) * k * (b : X)⁻¹ * k⁻¹) : X ⧸ W) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (h k hk)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    show (QuotientGroup.mk (b : X) : X ⧸ W) * QuotientGroup.mk' W k *
      (QuotientGroup.mk (b : X))⁻¹ = QuotientGroup.mk' W k
    exact mul_inv_eq_one.1 h1

end Ind

section CentreQuot
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem centerQuotientHom_mk {G : Type*} [Group G] (α : MulAut G) (y : G) :
    centerQuotientHom G α (QuotientGroup.mk y : G ⧸ Subgroup.center G) =
      (QuotientGroup.mk (α y) : G ⧸ Subgroup.center G) :=
  onCenterQuotient_apply_mk α y

end CentreQuot

section One
open CFSG.ComponentClassification.PerfectAutomorphisms
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem hyp1_inverts_big_aux (hInv : Chev2RankTwoInverts) (h : Setup28 W K S)
    (h1 : Hyp28One W K S) {A : Subgroup X} (hA : Off28 W K S A)
    (hc : Nat.card ↥(indAut W K A) = 4) :
    ∃ a ∈ A, a ∉ kerAct W K S ∧ Inverts W K a (fun m => 5 < m) := by
  have hAS : A ≤ S := hA.isMax.1
  have hAN : A ≤ Subgroup.normalizer (K : Set X) := hAS.trans h.hN
  obtain ⟨⟨hq, hChevQ⟩, hnAlt, hnoInner⟩ := h1
  have hperf : Group.IsPerfect ↥(bar W K) := hq.1
  have hι : Function.Injective (centerQuotientHom ↥(bar W K)) :=
    centerQuotientHom_injective _
  have hEel : IsElemAbelian 2 (indAut W K A) := indAut_isElemAbelian hAN hA.isMax.2.1
  have hE' : IsElemAbelian 2 ((indAut W K A).map (centerQuotientHom ↥(bar W K))) :=
    CFSG.Open.IsElemAbelian.map hEel _
  have hcard' : Nat.card ((indAut W K A).map (centerQuotientHom ↥(bar W K))) = 4 := by
    rw [Subgroup.card_map_of_injective hι]
    exact hc
  have hinn : (indAut W K A).map (centerQuotientHom ↥(bar W K)) ⊓
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) = ⊥ := by
    rw [eq_bot_iff]
    rintro ε ⟨hεE, hεI⟩
    obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.1 hεE
    obtain ⟨q, hqε⟩ := hεI
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hα' : α = MulAut.conj g := by
      apply hι
      rw [CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
      exact hqε.symm
    have hαS : α ∈ indAut W K S := indAut_mono hAS hα
    have hαI : α ∈ (MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range := ⟨g, hα'.symm⟩
    have hbot : α ∈ indAut W K S ⊓ (MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range :=
      ⟨hαS, hαI⟩
    rw [hnoInner] at hbot
    rw [Subgroup.mem_bot.1 hbot, map_one]
    exact Subgroup.one_mem _
  have hnotAlt : ¬ ∃ n : ℕ, 5 ≤ n ∧
      Nonempty ((↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* alternatingGroup (Fin n)) :=
    fun ⟨n, hn, hne⟩ => hnAlt ⟨hq, n, hn, hne⟩
  obtain ⟨ε, hεE, hε1, xq, hxodd, hx5, hεx⟩ := hInv _ hq.2.1 hq.2.2 hChevQ hnotAlt _ hE' hcard'
    hinn
  obtain ⟨α, hαE, rfl⟩ := Subgroup.mem_map.1 hεE
  obtain ⟨b, hbA, rfl⟩ := (mem_indAut_iff' hAN α).1 hαE
  refine ⟨(b : X), hbA, ?_, ?_⟩
  · intro hb
    apply hε1
    have : indHom W K b = 1 := (indHom_eq_one_iff b).2 hb.2
    rw [this, map_one]
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective xq
    obtain ⟨x, rfl⟩ := SRAut.toBar_surjective W K g
    refine ⟨x, hxodd, hx5, ?_⟩
    have hbxK : (b : X) * x * (b : X)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 b.2 x).1 x.2
    have hmemK : (b : X) * x * (b : X)⁻¹ * x ∈ K := K.mul_mem hbxK x.2
    refine (SRAut.mem_zPre_iff (W := W) (K := K) ⟨_, hmemK⟩).2 ?_
    have e1 : (⟨(b : X) * x * (b : X)⁻¹ * x, hmemK⟩ : ↥K) =
        ⟨(b : X) * x * (b : X)⁻¹, hbxK⟩ * x := rfl
    rw [e1, map_mul, ← indHom_toBar b x hbxK]
    apply (QuotientGroup.eq_one_iff _).1
    have hx' := hεx
    rw [centerQuotientHom_mk] at hx'
    show (QuotientGroup.mk (indHom W K b (toBar W K x)) : ↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) *
      QuotientGroup.mk (toBar W K x) = 1
    rw [hx', inv_mul_cancel]

end One

end SRInd

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

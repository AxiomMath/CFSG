module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs
public import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267CenterMultiplier
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Abs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267RankAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

section Transport

variable {S K : Subgroup Ω}

private theorem map_fixSubgroup_conj (hKN : K ≤ Subgroup.normalizer (S : Set Ω)) (x : ↥K) :
    (fixSubgroup (normalizerConjAutOfMem S K hKN x)).map S.subtype =
      S ⊓ Subgroup.centralizer ({(x : Ω)} : Set Ω) := by
  rw [show normalizerConjAutOfMem S K hKN x =
      (Subgroup.normalizerMonoidHom (H := S)) ⟨(x : Ω), hKN x.2⟩ from rfl]
  exact CFSG.map_eqLocus_normalizerMonoidHom S (hKN x.2)

private theorem subtype_ker_comm (X : Subgroup ↥S) :
    ∀ y ∈ X ⊓ S.subtype.ker, ∀ z ∈ X, z * y = y * z := fun y hy _ _ => by
  have hy1 : y = 1 := S.subtype_injective (by simpa using hy.2)
  rw [hy1, mul_one, one_mul]

theorem glaPComponent_fixSubgroup_of_inf_centralizer {p : ℕ} (hp : p.Prime)
    (hKN : K ≤ Subgroup.normalizer (S : Set Ω)) (x : ↥K) {J : Subgroup Ω}
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({(x : Ω)} : Set Ω)) J) :
    GLAPComponent p (fixSubgroup (normalizerToCenterQuotientAut S K hKN x))
      ((J.subgroupOf S).map (QuotientGroup.mk' (Subgroup.center ↥S))) := by
  rw [← map_fixSubgroup_conj hKN x] at hJ
  obtain ⟨J₀, hJ₀, hmap⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_glaPComponent_map_central hp S.subtype
      (subtype_ker_comm _) hJ
  subst hmap
  rw [show (J₀.map S.subtype).subgroupOf S = J₀ from
    Subgroup.comap_map_eq_self_of_injective S.subtype_injective J₀]
  exact CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup
    (QuotientGroup.mk' (Subgroup.center ↥S)) (by rw [QuotientGroup.ker_mk'])
    (normalizerConjAutOfMem S K hKN x) (normalizerToCenterQuotientAut S K hKN x)
    (fun k => normalizerConjAutOfMem_comp_mk S K hKN x k) (QuotientGroup.mk'_surjective _) hp hJ₀

theorem isQuasisimple_of_map_mk {J : Subgroup Ω} (hJS : J ≤ S) (hperf : ⁅J, J⁆ = J)
    (hq : CFSG.Open.IsQuasisimple
      ↥((J.subgroupOf S).map (QuotientGroup.mk' (Subgroup.center ↥S)))) :
    CFSG.Open.IsQuasisimple ↥J := by
  have hperf₀ : ⁅J.subgroupOf S, J.subgroupOf S⁆ = J.subgroupOf S := by
    rw [← subgroupOf_commutator hJS hJS, hperf]
  have hq₀ : CFSG.Open.IsQuasisimple ↥(J.subgroupOf S) := by
    refine I142.isQuasisimple_of_surj_central
      ((QuotientGroup.mk' (Subgroup.center ↥S)).subgroupMap (J.subgroupOf S))
      (MonoidHom.subgroupMap_surjective _ _) (fun y hy => ?_)
      (S267.perfect_of_commutator_self_eq hperf₀) hq
    have h1 : (QuotientGroup.mk' (Subgroup.center ↥S)) (y : ↥S) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_center_iff.2 fun z => Subtype.ext (Subgroup.mem_center_iff.1 h1 (z : ↥S))
  have e : ↥(J.subgroupOf S) ≃* ↥J :=
    ((J.subgroupOf S).equivMapOfInjective S.subtype S.subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hJS]))
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hq₀

theorem isElemAbelian_range {p : ℕ} (hKN : K ≤ Subgroup.normalizer (S : Set Ω))
    (hK : IsElemAbelian p K) : IsElemAbelian p (normalizerToCenterQuotientAut S K hKN).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : MulAut (↥S ⧸ Subgroup.center ↥S)) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (congrArg Subtype.val (hK.1.is_comm.comm x z))
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (hK.2 x x.2)
    rw [this, map_one]

end Transport

namespace GenHyp

variable {Q : TauCeti.LieTypeIndex → Prop} {p q : ℕ} {S B : Subgroup Ω}

theorem isPerfect (H : GenHyp Q p q S B) : Group.IsPerfect ↥S :=
  ⟨S267.perfect_of_commutator_self_eq H.perfect⟩

theorem le_normalizer (H : GenHyp Q p q S B) (K : Subgroup Ω) :
    K ≤ Subgroup.normalizer (S : Set Ω) := by
  rw [Subgroup.normalizer_eq_top_iff.2 H.normal]
  exact le_top

theorem centModSubgroup_eq (H : GenHyp Q p q S B) :
    centModSubgroup p S = Subgroup.centralizer (S : Set Ω) := by
  ext x
  refine ⟨fun hx => Subgroup.mem_centralizer_iff.2 fun s hs => ?_,
    fun hx => centMod_iff.1 (centMod_of_mem_centralizer hx)⟩
  have h := (mem_centModSubgroup.1 hx).2 s hs
  have hbot : GLAPPrimeCoreOf p S = ⊥ := by
    unfold GLAPPrimeCoreOf
    rw [H.core, Subgroup.map_bot]
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem exists_oddLie (H : GenHyp Q p q S B) :
    ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = q ∧ Q d.1 ∧
      OddLie p (↥S ⧸ Subgroup.center ↥S) d := by
  obtain ⟨d, hchar, hQ, ⟨e⟩⟩ := H.lie
  refine ⟨d, hchar, hQ, ⟨H.pPrime, H.pOdd,
    ⟨(BadExc.psimpleEquivCenterQuotOfCore H.core).symm.trans e⟩, ?_, ?_⟩⟩
  · rw [hchar]
    exact H.qOdd
  · rw [hchar]
    exact fun h => H.qp h.symm

theorem ne_bot (H : GenHyp Q p q S B) : S ≠ ⊥ := by
  intro hS
  have hle : B ≤ centModSubgroup p S := by
    intro x _
    refine mem_centModSubgroup.2 ⟨H.le_normalizer ⊤ (Subgroup.mem_top x), fun l hl => ?_⟩
    rw [hS, Subgroup.mem_bot] at hl
    rw [hl, commutatorElement_one_left]
    exact Subgroup.one_mem _
  have h1 := H.cent
  rw [inf_eq_left.2 hle] at h1
  have h4 := H.four
  rw [h1] at h4
  have hlt : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right H.pPrime.one_lt (by norm_num)
  rw [pow_one] at hlt
  exact absurd h4 (not_le.2 hlt)

theorem dvd_card_subgroup (H : GenHyp Q p q S B) : p ∣ Nat.card S := by
  by_contra h
  apply H.ne_bot
  have htop : (⊤ : Subgroup ↥S) ≤ GLAPPrimeCore p ↥S := by
    refine le_sSup ⟨inferInstance, ?_⟩
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd H.pPrime).2 h
  rw [H.core] at htop
  rw [eq_bot_iff]
  intro x hx
  have h1 := htop (Subgroup.mem_top ⟨x, hx⟩)
  rw [Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)

theorem dvd_card (H : GenHyp Q p q S B) : p ∣ Nat.card (↥S ⧸ Subgroup.center ↥S) := by
  have h := Subgroup.card_commutator_dvd_index_center_pow (G := ↥S)
  rw [S267.perfect_of_commutator_self_eq H.perfect, Subgroup.card_top] at h
  exact H.pPrime.dvd_of_dvd_pow (H.dvd_card_subgroup.trans h)

theorem aut_eq_one_iff (H : GenHyp Q p q S B) (K : Subgroup Ω) (x : ↥K) :
    normalizerToCenterQuotientAut S K (H.le_normalizer K) x = 1 ↔
      (x : Ω) ∈ centModSubgroup p S := by
  rw [normalizerToCenterQuotientAut_eq_one_iff H.isPerfect, H.centModSubgroup_eq]
  exact ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨x.2, h⟩⟩

theorem card_range_mul (H : GenHyp Q p q S B) (K : Subgroup Ω) :
    Nat.card (normalizerToCenterQuotientAut S K (H.le_normalizer K)).range *
      Nat.card ↥(K ⊓ centModSubgroup p S) = Nat.card K := by
  rw [card_range_normalizerToCenterQuotientAut H.isPerfect, H.centModSubgroup_eq]
  have h := Subgroup.relIndex_mul_card (H := K ⊓ Subgroup.centralizer (S : Set Ω)) (K := K)
  rwa [inf_eq_left.2 (inf_le_left : K ⊓ Subgroup.centralizer (S : Set Ω) ≤ K)] at h

theorem pow_three_le_card_range (H : GenHyp Q p q S B) :
    p ^ 3 ≤ Nat.card (normalizerToCenterQuotientAut S B (H.le_normalizer B)).range := by
  have h := H.card_range_mul B
  rw [H.cent] at h
  have h4 : p ^ 3 * p ≤
      Nat.card (normalizerToCenterQuotientAut S B (H.le_normalizer B)).range * p := by
    rw [h, ← pow_succ]
    exact H.four
  exact Nat.le_of_mul_le_mul_right h4 H.pPrime.pos

end GenHyp

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen

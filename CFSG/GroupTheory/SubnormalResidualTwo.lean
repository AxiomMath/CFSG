module

public import CFSG.RankThree.PartOne.S12.PushingUp
import CFSG.GroupTheory.OddOrderClosure
import CFSG.GroupTheory.PResidualNormalizer
import CFSG.GroupTheory.PResidualLocalFinite
import CFSG.Quasithin.Background.B2FactorizationResidual
import TauCeti.GroupTheory.Elementary
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.GroupTheory

open CFSG CFSG.RankThree.PartOne Subgroup
open scoped Pointwise commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

private theorem eq_one_of_odd_of_isPGroup_two_srt {G : Type*} [Group G] (hG : IsPGroup 2 G)
    {x : G} (hx : Odd (orderOf x)) : x = 1 := by
  have hcop : (orderOf x).Coprime (orderOf x) :=
    hG.orderOf_coprime hx.coprime_two_left x
  exact orderOf_eq_one_iff.mp ((Nat.coprime_self (orderOf x)).mp hcop)

private theorem isPGroup_two_quotient_iff_srt {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup 2 (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ 2 ^ k ∈ N := by
  constructor
  · intro h g
    obtain ⟨k, hk⟩ := h (QuotientGroup.mk' N g)
    refine ⟨k, ?_⟩
    have h1 : ((g ^ 2 ^ k : G) : G ⧸ N) = 1 := by simpa [QuotientGroup.mk_pow] using hk
    exact (QuotientGroup.eq_one_iff (N := N) (g ^ 2 ^ k)).1 h1
  · exact TauCeti.isPGroup_quotient_of_forall_exists_pow_mem

private theorem mem_oResidualTwo_of_odd_srt {X : Type*} [Group X] {x : X}
    (hx : Odd (orderOf x)) : x ∈ oResidualTwo X := by
  rw [oResidualTwo, Subgroup.mem_sInf]
  intro N hN
  obtain ⟨hNn, hNp⟩ := hN
  have := hNn
  have hodd : Odd (orderOf ((QuotientGroup.mk' N) x)) :=
    Odd.of_dvd_nat hx (orderOf_map_dvd _ x)
  have hone : (QuotientGroup.mk' N) x = 1 := eq_one_of_odd_of_isPGroup_two_srt hNp hodd
  exact (QuotientGroup.eq_one_iff (N := N) x).1 (by simpa using hone)

private theorem oddOrderClosure_top_le_oResidualTwo_srt (X : Type*) [Group X] :
    oddOrderClosure (⊤ : Subgroup X) ≤ oResidualTwo X := by
  rw [oddOrderClosure_le_iff]
  intro x hx
  exact mem_oResidualTwo_of_odd_srt hx.2

private theorem oResidualTwo_le_oddOrderClosure_top_srt (X : Type*) [Group X] [Finite X] :
    oResidualTwo X ≤ oddOrderClosure (⊤ : Subgroup X) := by
  have hnormal : (oddOrderClosure (⊤ : Subgroup X)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (⊤ : Set X) :=
      Subgroup.le_normalizer (H := (⊤ : Subgroup X)) (Subgroup.mem_top g)
    exact conj_mem_oddOrderClosure hg hn
  refine sInf_le ⟨hnormal, ?_⟩
  rw [isPGroup_two_quotient_iff_srt]
  intro g
  obtain ⟨k, hk⟩ := pow_two_pow_mem_oddOrderClosure (⊤ : Subgroup X) (Subgroup.mem_top g)
  exact ⟨k, hk⟩

private theorem pResidual_two_eq_oddOrderClosure_top_srt (X : Type*) [Group X] [Finite X] :
    CFSG.Quasithin.pResidual 2 X = oddOrderClosure (⊤ : Subgroup X) := by
  have h1 : CFSG.Quasithin.pResidualOf 2 (⊤ : Subgroup X) = CFSG.Quasithin.pResidual 2 X :=
    pResidual_map_of_surjective 2 (⊤ : Subgroup X).subtype
      fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
  have h2 : CFSG.Quasithin.pResidualOf 2 (⊤ : Subgroup X) =
      Subgroup.closure {x : X | Odd (orderOf x)} :=
    CFSG.Quasithin.B2F.pResidualOf_top_eq_closure_odd
  rw [← h1, h2, oddOrderClosure_eq_closure]
  congr 1
  ext x
  simp

private theorem oResidualTwo_eq_pResidual_srt (X : Type*) [Group X] [Finite X] :
    oResidualTwo X = CFSG.Quasithin.pResidual 2 X := by
  rw [pResidual_two_eq_oddOrderClosure_top_srt X]
  exact le_antisymm (oResidualTwo_le_oddOrderClosure_top_srt X)
    (oddOrderClosure_top_le_oResidualTwo_srt X)

private theorem oddOrderClosure_top_le_of_isSubnormal_srt {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} (hidx : ∃ n, K.index = 2 ^ n) (hsub : K.IsSubnormal) :
    oddOrderClosure (⊤ : Subgroup G) ≤ K := by
  revert hidx
  induction hsub with
  | top => intro _; exact le_top
  | step H K h_le hSubn hN ih =>
      intro hidx
      obtain ⟨n, hn⟩ := hidx
      have hKidx : ∃ m, K.index = 2 ^ m := by
        have hdvd : K.index ∣ 2 ^ n := by
          rw [← hn]
          exact Subgroup.index_dvd_of_le h_le
        obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
        exact ⟨m, hm⟩
      have hKle : oddOrderClosure (⊤ : Subgroup G) ≤ K := ih hKidx
      have hdvd : (H.subgroupOf K).index ∣ 2 ^ n := by
        change H.relIndex K ∣ 2 ^ n
        rw [← hn]
        exact Subgroup.relIndex_dvd_index_of_le h_le
      have : (H.subgroupOf K).Normal := hN
      have hcard : Nat.card (K ⧸ H.subgroupOf K) ∣ 2 ^ n := by
        rw [← Subgroup.index_eq_card]
        exact hdvd
      have hpg : IsPGroup 2 (K ⧸ H.subgroupOf K) := IsPGroup.of_card_dvd_pow hcard
      rw [oddOrderClosure_le_iff]
      intro x hx
      have hxK : x ∈ K := hKle (mem_oddOrderClosure_of_mem_of_odd (Subgroup.mem_top x) hx.2)
      have hoddK : Odd (orderOf (⟨x, hxK⟩ : K)) := by
        rw [← Subgroup.orderOf_coe (⟨x, hxK⟩ : K)]
        exact hx.2
      have hoddq : Odd (orderOf ((QuotientGroup.mk' (H.subgroupOf K)) (⟨x, hxK⟩ : K))) :=
        Odd.of_dvd_nat hoddK (orderOf_map_dvd _ _)
      have hone : (QuotientGroup.mk' (H.subgroupOf K)) (⟨x, hxK⟩ : K) = 1 :=
        eq_one_of_odd_of_isPGroup_two_srt hpg hoddq
      exact (QuotientGroup.eq_one_iff (N := H.subgroupOf K) (⟨x, hxK⟩ : K)).1
        (by simpa using hone)

theorem map_oResidualTwo_eq_of_isSubnormal {B X : Subgroup Y} (hBX : B ≤ X)
    (hsub : (B.subgroupOf X).IsSubnormal) (hidx : ∃ n : ℕ, B.relIndex X = 2 ^ n)
    (hres : oResidualTwo B = ⊤) : (oResidualTwo X).map X.subtype = B := by
  have hoddB : oddOrderClosure (⊤ : Subgroup ↥B) = ⊤ := by
    rw [← pResidual_two_eq_oddOrderClosure_top_srt ↥B, ← oResidualTwo_eq_pResidual_srt B, hres]
  have hmap := map_oddOrderClosure_le (Subgroup.inclusion hBX) (⊤ : Subgroup ↥B)
  rw [hoddB] at hmap
  have hrange : (⊤ : Subgroup ↥B).map (Subgroup.inclusion hBX) = B.subgroupOf X := by
    rw [← MonoidHom.range_eq_map, Subgroup.inclusion_range]
  rw [hrange] at hmap
  have hBle : B.subgroupOf X ≤ oResidualTwo X :=
    (hmap.trans (oddOrderClosure_mono le_top)).trans (oddOrderClosure_top_le_oResidualTwo_srt ↥X)
  have hK : oddOrderClosure (⊤ : Subgroup ↥X) ≤ B.subgroupOf X :=
    oddOrderClosure_top_le_of_isSubnormal_srt (K := B.subgroupOf X) hidx hsub
  refine le_antisymm ?_ ?_
  · calc (oResidualTwo X).map X.subtype
        ≤ (B.subgroupOf X).map X.subtype :=
          Subgroup.map_mono ((oResidualTwo_le_oddOrderClosure_top_srt ↥X).trans hK)
      _ = B := Subgroup.map_subgroupOf_eq_of_le hBX
  · calc B = (B.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hBX).symm
      _ ≤ (oResidualTwo X).map X.subtype := Subgroup.map_mono hBle

theorem le_normalizer_of_commutator_le {B Q C : Subgroup Y} (hQ : IsPGroup 2 Q)
    (hQB : Q ≤ normalizer (B : Set Y)) (hres : oResidualTwo B = ⊤)
    (hCQ : C ≤ normalizer (Q : Set Y)) (hCB : ⁅C, B⁆ ≤ Q) : C ≤ normalizer (B : Set Y) := by
  let X : Subgroup Y := B ⊔ Q
  have hBX : B ≤ X := le_sup_left
  have hsubX : (B.subgroupOf X).IsSubnormal := by
    have hnorm : (B.subgroupOf X).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBX]
      exact sup_le Subgroup.le_normalizer hQB
    exact hnorm.isSubnormal
  have hidx : ∃ n, B.relIndex X = 2 ^ n := by
    rw [show X = Q ⊔ B by simp [X, sup_comm]]
    rw [CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer hQB]
    exact CFSG.Quasithin.B6.exists_relIndex_eq_two_pow_of_isPGroup hQ B
  have hresX : (oResidualTwo ↥X).map X.subtype = B :=
    map_oResidualTwo_eq_of_isSubnormal hBX hsubX hidx hres
  have hpRes : CFSG.Quasithin.pResidualOf 2 X = B := by
    rw [CFSG.Quasithin.pResidualOf, ← oResidualTwo_eq_pResidual_srt ↥X]
    exact hresX
  have hCX : C ≤ normalizer (X : Set Y) := by
    have hconj : ∀ d ∈ C, ∀ y ∈ B ⊔ Q, d * y * d⁻¹ ∈ X := by
      intro d hd y hy
      have hyBQ : (y : Y) ∈ (B : Set Y) * (Q : Set Y) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left B Q hQB]
        exact hy
      obtain ⟨b, hb, q, hq, rfl⟩ := Set.mem_mul.1 hyBQ
      have hb' : d * b * d⁻¹ ∈ X := by
        have hcomm : ⁅d, b⁆ ∈ Q := hCB (Subgroup.commutator_mem_commutator hd hb)
        have hdb : d * b * d⁻¹ = ⁅d, b⁆ * b := by
          rw [commutatorElement_def]
          group
        rw [hdb]
        exact mul_mem (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hb)
      have hq' : d * q * d⁻¹ ∈ X :=
        Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hCQ hd) q).mp hq)
      rw [show d * (b * q) * d⁻¹ = (d * b * d⁻¹) * (d * q * d⁻¹) by group]
      exact mul_mem hb' hq'
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hconj c hc x, fun hx => by
      have := hconj c⁻¹ (C.inv_mem hc) (c * x * c⁻¹) hx
      simpa [mul_assoc] using this⟩
  calc C ≤ normalizer (X : Set Y) := hCX
    _ ≤ normalizer (CFSG.Quasithin.pResidualOf 2 X : Set Y) :=
        CFSG.Quasithin.normalizer_le_normalizer_pResidualOf 2 X
    _ = normalizer (B : Set Y) := by rw [hpRes]

end CFSG.GroupTheory
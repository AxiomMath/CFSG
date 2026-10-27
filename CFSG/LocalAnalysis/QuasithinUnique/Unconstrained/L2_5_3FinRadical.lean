module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinBasic

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open
open scoped Pointwise

section Radical

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_inf_normalizer_not_mem {X R : Subgroup G} (hX : IsPGroup 2 X) (hRX : R ≤ X)
    (hne : ¬ X ≤ R) : ∃ x ∈ X ⊓ Subgroup.normalizer (R : Set G), x ∉ R := by
  classical
  let RX : Subgroup X := R.subgroupOf X
  have hRXne : RX ≠ ⊤ := by
    intro htop
    apply hne
    intro x hxX
    have hxR : (⟨x, hxX⟩ : X) ∈ RX := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hxR
  have hRXlt : RX < ⊤ := lt_of_le_of_ne le_top hRXne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥X := hX.isNilpotent
  have hnc : NormalizerCondition ↥X := Group.normalizerCondition_of_isNilpotent (G := ↥X)
  have hlt : RX < Subgroup.normalizer (RX : Set X) := hnc RX hRXlt
  obtain ⟨x, hxN, hxnotRX⟩ := IsConcreteLE.exists_of_lt hlt
  have hxNorm : (x : G) ∈ Subgroup.normalizer (R : Set G) := by
    have hxsub : x ∈ (Subgroup.normalizer (R : Set G)).subgroupOf X := by
      rw [Subgroup.subgroupOf_normalizer_eq hRX]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  exact ⟨(x : G), ⟨x.2, hxNorm⟩, fun hxR => hxnotRX (Subgroup.mem_subgroupOf.mpr hxR)⟩

theorem pCoreOf_le_of_radical {B R : Subgroup G} (hRB : R ≤ B) (hR : IsPGroup 2 R)
    (hrad : pCoreOf 2 (B ⊓ Subgroup.normalizer (R : Set G)) = R) : pCoreOf 2 B ≤ R := by
  set P := pCoreOf 2 B with hP
  have hPB : P ≤ B := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 B
  have hP2 : IsPGroup 2 P := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 B
  have hBP : B ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 B
  obtain ⟨T, hRT, hT⟩ := exists_isSylowTwoOf_of_le hRB hR
  have hPT : P ≤ T := hT.le_of_normalizes hPB hBP hP2
  by_contra hPR
  have hX2 : IsPGroup 2 ↥(R ⊔ P) := hT.isPGroup.to_le (sup_le hRT hPT)
  have hnot : ¬ R ⊔ P ≤ R := fun h => hPR (le_sup_right.trans h)
  obtain ⟨x, ⟨hxX, hxN⟩, hxR⟩ := exists_mem_inf_normalizer_not_mem hX2 le_sup_left hnot
  have hRP : R ≤ Subgroup.normalizer (P : Set G) := hRB.trans hBP
  have hcoe : ((R ⊔ P : Subgroup G) : Set G) = (R : Set G) * (P : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right R P hRP
  have hxmem : x ∈ (R : Set G) * (P : Set G) := by
    rw [← hcoe]
    exact hxX
  obtain ⟨r, hr, p, hp, rfl⟩ := Set.mem_mul.mp hxmem
  have hrN : r ∈ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer hr
  have hpN : p ∈ Subgroup.normalizer (R : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hrN) hxN
    simpa using this
  have hpA : p ∈ B ⊓ Subgroup.normalizer (R : Set G) := ⟨hPB hp, hpN⟩
  have hPA : P ⊓ (B ⊓ Subgroup.normalizer (R : Set G)) ≤ R := by
    have hn : B ⊓ Subgroup.normalizer (R : Set G) ≤
        Subgroup.normalizer ((P ⊓ (B ⊓ Subgroup.normalizer (R : Set G)) : Subgroup G) : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ P _
        (inf_le_left.trans hBP) Subgroup.le_normalizer
    have h := le_pCoreOf_of_normal_pGroup
      (inf_le_right : P ⊓ (B ⊓ Subgroup.normalizer (R : Set G)) ≤ B ⊓ Subgroup.normalizer (R : Set G))
      hn (hP2.to_le inf_le_left)
    rwa [hrad] at h
  exact hxR (Subgroup.mul_mem _ hr (hPA ⟨hp, hpA⟩))

omit [Finite G] in
theorem exists_pow_mem_of_mem_sup {D S : Subgroup G} (hS : IsPGroup 2 S)
    (hSD : S ≤ Subgroup.normalizer (D : Set G)) {x : G} (hx : x ∈ D ⊔ S) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ D := by
  have hcoe : ((S ⊔ D : Subgroup G) : Set G) = (S : Set G) * (D : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right S D hSD
  have hx' : x ∈ ((S ⊔ D : Subgroup G) : Set G) := by
    rw [sup_comm] at hx
    exact hx
  rw [hcoe] at hx'
  obtain ⟨s, hs, d, hd, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hsk : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have key : ∀ n : ℕ, ∃ d' ∈ D, (s * d) ^ n = s ^ n * d' := by
    intro n
    induction n with
    | zero => exact ⟨1, D.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨d', hd', hn⟩ := ih
      have hs' : s⁻¹ * d' * s ∈ D := by
        have := (Subgroup.mem_normalizer_iff.mp (hSD (S.inv_mem hs)) d').mp hd'
        simpa using this
      refine ⟨(s⁻¹ * d' * s) * d, D.mul_mem hs' hd, ?_⟩
      rw [pow_succ, hn, pow_succ]
      group
  obtain ⟨d', hd', hn⟩ := key (2 ^ k)
  refine ⟨k, ?_⟩
  rw [hn, hsk, one_mul]
  exact hd'

omit [Finite G] in
theorem isPGroup_inf_sup_centralizer {D Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQD : Q ≤ Subgroup.normalizer (D : Set G)) (hD : Unc25G2.CentreTwo D) :
    IsPGroup 2 ↥(D ⊓ (Q ⊔ Subgroup.centralizer (D : Set G))) := by
  have hQC : Q ≤ Subgroup.normalizer ((Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
    hQD.trans (normalizer_le_normalizer_centralizer D)
  have hcoe : ((Q ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) =
      (Q : Set G) * (Subgroup.centralizer (D : Set G) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Q _ hQC
  rintro ⟨y, hyD, hyQC⟩
  have hy' : y ∈ ((Q ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := hyQC
  rw [hcoe] at hy'
  obtain ⟨q, hq, c, hc, rfl⟩ := Set.mem_mul.mp hy'
  obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
  have hqk : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcq : Commute c (q * c) := (Subgroup.mem_centralizer_iff.mp hc (q * c) hyD).symm
  have hcomm : Commute (q * c) c⁻¹ := hcq.inv_left.symm
  have hqeq : q = (q * c) * c⁻¹ := by group
  have h1 : (q * c) ^ 2 ^ k * (c⁻¹) ^ 2 ^ k = 1 := by
    rw [← hcomm.mul_pow, ← hqeq]
    exact hqk
  have h2 : (q * c) ^ 2 ^ k = c ^ 2 ^ k := by
    rw [inv_pow] at h1
    exact mul_inv_eq_one.mp h1
  have hu : (q * c) ^ 2 ^ k ∈ D := D.pow_mem hyD _
  have hucomm : ∀ w ∈ D, w * (q * c) ^ 2 ^ k = (q * c) ^ 2 ^ k * w := by
    intro w hw
    rw [h2]
    exact (Commute.pow_right (show Commute w c from Subgroup.mem_centralizer_iff.mp hc w hw) _).eq
  obtain ⟨j, hj⟩ := hD _ hu hucomm
  refine ⟨k + j, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [pow_add, pow_mul]
  exact hj

end Radical

section Normalizers

variable {G : Type*} [Group G]

theorem le_normalizer_sup {N X Y : Subgroup G} (hX : N ≤ Subgroup.normalizer (X : Set G))
    (hY : N ≤ Subgroup.normalizer (Y : Set G)) :
    N ≤ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  have key : ∀ n ∈ N, ∀ y ∈ X ⊔ Y, n * y * n⁻¹ ∈ X ⊔ Y := by
    intro n hn
    have hle : X ⊔ Y ≤ (X ⊔ Y).comap (MulAut.conj n).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun y hy => ?_)
      · exact (le_sup_left : X ≤ X ⊔ Y) ((Subgroup.mem_normalizer_iff.mp (hX hn) x).mp hx)
      · exact (le_sup_right : Y ≤ X ⊔ Y) ((Subgroup.mem_normalizer_iff.mp (hY hn) y).mp hy)
    intro y hy
    exact hle hy
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key n hn y, fun h => ?_⟩
  have := key n⁻¹ (N.inv_mem hn) _ h
  simpa [mul_assoc] using this

theorem false_of_centralizes {L : Subgroup G} {z : G} (hcomm : ⁅L, Subgroup.zpowers z⁆ = L)
    (hL : L ≠ ⊥) (hz : ∀ x ∈ L, z * x = x * z) : False := by
  apply hL
  calc L = ⁅L, Subgroup.zpowers z⁆ := hcomm.symm
    _ = ⊥ := by
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx => ?_
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (hz x hx) i).eq

end Normalizers

end CFSG.QuasithinUnique.Fin253

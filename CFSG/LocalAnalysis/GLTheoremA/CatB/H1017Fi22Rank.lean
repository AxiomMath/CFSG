module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017TwistFi22
public import Certificates.Certificate431010

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22Rank

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H1017
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22Twist

theorem card_lt_of_comm_le_Q2
    (A : Subgroup (Equiv.Perm (Fin 3510))) (hA : A ≤ Qk 2)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Nat.card A < 243 :=
  Certificates.certificate431010 A hA hcomm

theorem card_le_of_le_centralizer (t : fi22P) (ht : orderOf t = 2) (F : Subgroup fi22P)
    (hFt : F ≤ Subgroup.centralizer ({t} : Set fi22P)) (hF : IsElemAbelian 3 F) :
    Nat.card F ≤ 3 ^ 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, g, hg⟩ := exists_conj_ext t ht
  have htk : fi22ExtRep k ∈ fi22P := CTUC_Fi22_all_extension_involutions_covered.1 k hk
  set tk : fi22P := ⟨fi22ExtRep k, htk⟩
  have hgt : g * t * g⁻¹ = tk := Subtype.ext hg
  set F₁ := F.map (MulAut.conj g).toMonoidHom with hF₁
  have hF₁t : F₁ ≤ Subgroup.centralizer ({tk} : Set fi22P) := by
    rw [← hgt]
    exact map_conj_le_centralizer_singleton g hFt
  have hF₁e : IsElemAbelian 3 F₁ := isElemAbelian_map' _ hF
  have hQC : (Qk k).subgroupOf fi22P ≤ Subgroup.centralizer ({tk} : Set fi22P) := by
    intro q hq
    have hq' := Qk_le_centralizer hk (Subgroup.mem_subgroupOf.1 hq)
    rw [Subgroup.mem_centralizer_iff] at hq' ⊢
    rintro s rfl
    exact Subtype.ext (hq' _ rfl)
  have hF₁p : IsPGroup 3 F₁ := fun d => ⟨1, Subtype.ext (by simpa using hF₁e.2 d d.2)⟩
  obtain ⟨h, -, hh⟩ := exists_conj_into_of_card hQC (card_Qk_eq hk) hF₁t hF₁p
  set F₂ := F₁.map (MulAut.conj h).toMonoidHom with hF₂
  have hF₂c : Nat.card F₂ = Nat.card F := by
    rw [hF₂, Subgroup.card_map_of_injective (MulAut.conj h).injective, hF₁,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hF₂e : IsElemAbelian 3 F₂ := isElemAbelian_map' _ hF₁e
  rw [← hF₂c]
  set A := F₂.map fi22P.subtype with hAdef
  have hAc : Nat.card A = Nat.card F₂ := Subgroup.card_map_of_injective fi22P.subtype_injective
  have hAQ : A ≤ Qk k := by
    rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hh hw)
  rw [← hAc]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · have := Subgroup.card_le_of_le hAQ
    rw [card_Qk hk] at this
    exact this.trans (by decide)
  · have := Subgroup.card_le_of_le hAQ
    rw [card_Qk hk] at this
    exact this.trans (by decide)
  · have hlt : Nat.card A < 243 := card_lt_of_comm_le_Q2 A hAQ (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (comm_of_isElemAbelian' hF₂e ha hb))
    have hAp : IsPGroup 3 A := by
      rw [hAdef]
      exact (IsPGroup.map (fun d => ⟨1, Subtype.ext (by simpa using hF₂e.2 d d.2)⟩) _)
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hAp
    rw [hm] at hlt ⊢
    have : m < 5 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1
      (by rw [show (3 : ℕ) ^ 5 = 243 by norm_num]; exact hlt)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem twoLocalBoundPow_fi22P :
    TwoLocalBoundPow 4 fi22P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro R E hR hR2 hEN hE
  by_contra hlt
  push Not at hlt
  have hcomm := noTwist_of_invClosed (r := 4) (by norm_num) (fun E' D hE' _ hDE hDc ⟨t, ht, hDt⟩ =>
    Fi22Twist.closed_of_inv D (CFSG.Open.IsElemAbelian.mono hE' hDE) (by simpa using hDc) t ht hDt)
    E hE hlt.le R hR2 hEN
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hR2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hR (Subgroup.card_eq_one.1 hm)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 (by rw [hm]; exact dvd_pow_self 2 hm0)
  have hu2 : orderOf (u : fi22P) = 2 := by rw [Subgroup.orderOf_coe, hu]
  have hEu : E ≤ Subgroup.centralizer ({(u : fi22P)} : Set fi22P) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (by first | exact hcomm e he u u.2 | exact (hcomm e he u u.2).symm)
  exact absurd (card_le_of_le_centralizer u hu2 E hEu hE) (not_le.2 hlt)

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22Rank


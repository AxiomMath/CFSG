module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamURankBasic
public import CFSG.GroupTheory.WeirSylow.Unitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SigmaDich
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open CFSG.Quasithin (StatedGU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
  (mem_statedSU_of_mem_statedGU)

theorem heisU_exp_pos {p q : ℕ} (hp : p.Prime) (hq2 : 2 ≤ q) (hpq : ¬ p ∣ q) :
    1 ≤ padicValInt p ((-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne0 : (-(q : ZMod p)) ≠ 0 :=
    neg_ne_zero.2 (fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h))
  have hdvd : (p : ℤ) ∣ (-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hx : (-(q : ZMod p)) ^ orderOf (-(q : ZMod p)) = 1 := pow_orderOf_eq_one _
    push_cast
    exact sub_eq_zero.2 hx
  have hne : (-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1 ≠ 0 := by
    intro h
    have h1 : (-(q : ℤ)) ^ orderOf (-(q : ZMod p)) = 1 := sub_eq_zero.1 h
    have h2 := congrArg Int.natAbs h1
    rw [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_one] at h2
    have hepos : 0 < orderOf (-(q : ZMod p)) := by
      rw [orderOf_pos_iff]
      exact isOfFinOrder_iff_pow_eq_one.2
        ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one hne0⟩
    have h3 : q = 1 := (Nat.pow_eq_one.1 h2).resolve_right (by omega)
    omega
  rcases (padicValInt_dvd_iff 1 ((-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1)).1
      (by simpa using hdvd) with h | h
  · exact absurd h hne
  · exact h

theorem heisU_exists_elemAbelian_of_sigma {p e a n : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hge : p ≤ n / e) {G : Type*} [Group G] (φ : sigmaModel p e a n →* G)
    (hφ : Function.Injective φ) : ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ p := by
  have hL : 1 < (Nat.digits p (n / e)).length := by
    rw [Nat.lt_digits_length_iff hp.one_lt]
    simpa using hge
  have hne : n / e ≠ 0 := by have := hp.two_le; omega
  let i₁ : Fin (Nat.digits p (n / e)).length := ⟨(Nat.digits p (n / e)).length - 1, by omega⟩
  have hi₁ : 1 ≤ (i₁ : ℕ) := by
    show 1 ≤ (Nat.digits p (n / e)).length - 1
    omega
  have hpos : 0 < (Nat.digits p (n / e))[i₁] := by
    have hlast := Nat.getLast_digit_ne_zero p hne
    have heq : (Nat.digits p (n / e))[i₁] =
        (Nat.digits p (n / e)).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hne) := by
      rw [List.getLast_eq_getElem]
      rfl
    rw [heq]
    exact Nat.pos_of_ne_zero hlast
  let j₁ : Fin (Nat.digits p (n / e))[i₁] := ⟨0, hpos⟩
  obtain ⟨E, hE, hEcard⟩ := SigmaDich.exists_elemAbelian_wreathTower hp ha i₁ hi₁
  let Ψ : wreathTower p (Multiplicative (ZMod (p ^ a))) i₁ →* G :=
    φ.comp (SigmaDich.sigmaEmbed p e a n i₁ j₁)
  have hΨ : Function.Injective Ψ := hφ.comp (SigmaDich.sigmaEmbed_injective p e a n i₁ j₁)
  exact ⟨E.map Ψ, (isElemAbelian_map_iff_of_injective Ψ hΨ E).2 hE,
    by rw [Subgroup.card_map_of_injective hΨ]; exact hEcard⟩

theorem heisU_exists_elemAbelian_GU {K : Type} [Field K] [Fintype K] {q p n : ℕ}
    (hK : Fintype.card K = q ^ 2) (hq2 : 2 ≤ q) (hp : p.Prime) (hpq : ¬ p ∣ q)
    (hge : p ≤ n / orderOf (-(q : ZMod p))) :
    ∃ E : Subgroup (StatedGU n q K), IsElemAbelian p E ∧ Nat.card E = p ^ p := by
  have ha := heisU_exp_pos hp hq2 hpq
  obtain ⟨φ, hφ⟩ := @exists_injective_sigmaModel_GU p ⟨hp⟩ K _ _ q hK hpq n
  exact heisU_exists_elemAbelian_of_sigma hp ha hge φ hφ

theorem heisU_card_range_le {G K : Type*} [Group G] [Field K] [Finite K] {p : ℕ} (hp : 0 < p)
    (hG : ∀ x : G, x ^ p = 1) (δ : G →* Kˣ) : Nat.card δ.range ≤ p := by
  classical
  haveI := Fintype.ofFinite Kˣ
  have h1 : Nat.card δ.range ≤ Nat.card {a : Kˣ // a ^ p = 1} := by
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1, ?_⟩) ?_
    · obtain ⟨z, hz⟩ := x.2
      rw [← hz, ← map_pow, hG z, map_one]
    · intro a b hab
      exact Subtype.ext (by simpa using hab)
  have h2 : Nat.card {a : Kˣ // a ^ p = 1} =
      (Finset.univ.filter fun a : Kˣ => a ^ p = 1).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h1.trans (h2 ▸ IsCyclic.card_pow_eq_one_le hp)

theorem heisU_false_of_GU {L K : Type} [Group L] [Field K] [Finite K] (hrk : OddRankLeThree L)
    {n f p : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (ρ : StatedSU n (2 ^ f) K →* L) (hker : ¬ p ∣ Nat.card ρ.ker)
    (E : Subgroup (StatedGU n (2 ^ f) K)) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ p) : False := by
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  let δ : E →* Kˣ :=
    Matrix.GeneralLinearGroup.det.comp ((StatedGU n (2 ^ f) K).subtype.comp E.subtype)
  have hδ : ∀ x : E, ((δ x : Kˣ) : K) =
      (((x : StatedGU n (2 ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := fun _ => rfl
  have hEp : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hE.2 _ x.2)
  have hr : Nat.card δ.range ≤ p := heisU_card_range_le hp.pos hEp δ
  have hmul := Subgroup.card_ker_mul_card_range δ
  have hkcard : p ^ 4 ≤ Nat.card δ.ker := by
    have h1 : p ^ 4 * p ≤ Nat.card δ.ker * p := by
      calc p ^ 4 * p = p ^ 5 := by ring
        _ ≤ p ^ p := Nat.pow_le_pow_right hp.pos hp5
        _ = Nat.card δ.ker * Nat.card δ.range := by rw [hmul, hEcard]
        _ ≤ Nat.card δ.ker * p := Nat.mul_le_mul_left _ hr
    exact Nat.le_of_mul_le_mul_right h1 hp.pos
  let ι : δ.ker →* GL (Fin n) K :=
    (StatedGU n (2 ^ f) K).subtype.comp (E.subtype.comp δ.ker.subtype)
  have hι : Function.Injective ι := (StatedGU n (2 ^ f) K).subtype_injective.comp
    (E.subtype_injective.comp δ.ker.subtype_injective)
  have hSU : ∀ x : δ.ker, ι x ∈ StatedSU n (2 ^ f) K := fun x => by
    refine mem_statedSU_of_mem_statedGU h rfl ((x : E) : StatedGU n (2 ^ f) K).2 ?_
    show ((((x : E) : StatedGU n (2 ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1
    rw [← hδ, MonoidHom.mem_ker.1 x.2, Units.val_one]
  let κ : δ.ker →* StatedSU n (2 ^ f) K := ι.codRestrict (StatedSU n (2 ^ f) K) hSU
  have hκ : Function.Injective κ := (MonoidHom.injective_codRestrict ι _ hSU).2 hι
  have hkp : ∀ x : δ.ker, x ^ p = 1 := fun x => Subtype.ext (hEp _)
  have hψ : Function.Injective (ρ.comp κ) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : κ x = 1 :=
      heisU_eq_one_of_pow_eq_one ρ hp hker (by rw [← map_pow, hkp x, map_one]) hx
    exact hκ (h1.trans (map_one κ).symm)
  have hcomm : ∀ x y : δ.ker, x * y = y * x := fun x y =>
    Subtype.ext (hE.1.is_comm.comm (x : E) (y : E))
  exact heisU_false_of_injective hrk hp (by omega) hcomm hkp hkcard (ρ.comp κ) hψ

theorem heisU_div_lt {L K : Type} [Group L] [Field K] [Finite K] (hrk : OddRankLeThree L)
    {n f p : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (ρ : StatedSU n (2 ^ f) K →* L) (hker : ¬ p ∣ Nat.card ρ.ker) :
    n / orderOf (-((2 ^ f : ℕ) : ZMod p)) < p := by
  by_contra hge
  push Not at hge
  haveI := Fintype.ofFinite K
  have hKc : Fintype.card K = (2 ^ f) ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hK
  have hpq : ¬ p ∣ 2 ^ f := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨E, hE, hEcard⟩ := heisU_exists_elemAbelian_GU hKc hq2 hp hpq hge
  exact heisU_false_of_GU hrk hK hf hp hp5 ρ hker E hE hEcard

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

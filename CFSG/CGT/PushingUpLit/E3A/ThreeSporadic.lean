module

public import CFSG.CGT.PushingUpLit.E3A.ThreeBase
public import CFSG.CGT.Timmesfeld75.ListWCCert

public section

namespace CFSG.CGT.PushingUpLit.E3A

open CFSG CFSG.Blueprint CFSG.CGT.Timmesfeld75 CFSG.CGT.Timmesfeld75.WCCheck CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

theorem sylowCenterTwo_of_facts {D : Data} {M : Subgroup (Equiv.Perm (Fin D.n))}
    {genG : ℤ → M} (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l))
    (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (hF : Facts D)
    (hM : ∃ m : ℕ, Odd m ∧ Nat.card M = 2 ^ D.pc.length * m) : SylowCenterTwo M := by
  obtain ⟨m, hm, hcardM⟩ := hM
  have hp := isPGroup_S0 hn hgen hinv hF
  have hidx : ¬ 2 ∣ (S0 D genG).index := by
    have h := (S0 D genG).card_mul_index
    rw [card_S0 hn hgen hF hinv, hcardM] at h
    have : (S0 D genG).index = m := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) h
    rw [this]
    exact hm.not_two_dvd_nat
  let P : Sylow 2 M := hp.toSylow hidx
  refine SylowCenterTwo.of_one P fun u v hu hv hcu hcv => ?_
  have hu' : u ∈ S0 D genG := hu
  have hv' : v ∈ S0 D genG := hv
  rcases eq_one_or_eq_z_of_central hn hgen hF hinv hu' hcu with h1 | h1
  · exact Or.inl h1
  rcases eq_one_or_eq_z_of_central hn hgen hF hinv hv' hcv with h2 | h2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (h1.trans h2.symm))

theorem sylowCenterTwo_m22_of_check (h : M22WCCheck) :
    SylowCenterTwo NativeSporadic.M22 :=
  sylowCenterTwo_of_facts (D := m22Data) (M := NativeSporadic.M22) (by norm_num [m22Data])
    rep_m22gen m22gen_neg (facts_of_wcCheck h) ⟨3465, by decide, by
      rw [show 2 ^ m22Data.pc.length * 3465 = 443520 from rfl]
      exact CFSG.Sporadic.Mathieu.card_M22⟩

theorem sylowCenterTwo_m23_of_check (h : M23WCCheck) :
    SylowCenterTwo NativeSporadic.M23 :=
  sylowCenterTwo_of_facts (D := m23Data) (M := NativeSporadic.M23) (by norm_num [m23Data])
    rep_m23gen m23gen_neg (facts_of_wcCheck h) ⟨79695, by decide, by
      rw [show 2 ^ m23Data.pc.length * 79695 = 10200960 from rfl]
      exact CFSG.Sporadic.Schreier.m23_card⟩

theorem sylowCenterTwo_m24_of_check (h : M24WCCheck) :
    SylowCenterTwo NativeSporadic.M24 :=
  sylowCenterTwo_of_facts (D := m24Data) (M := NativeSporadic.M24) (by norm_num [m24Data])
    rep_m24gen m24gen_neg (facts_of_wcCheck h) ⟨239085, by decide, by
      rw [show 2 ^ m24Data.pc.length * 239085 = 244823040 from rfl]
      exact CFSG.Sporadic.Mathieu.card_M24⟩

theorem sylowCenterTwo_m22 :
    SylowCenterTwo NativeSporadic.M22 :=
  sylowCenterTwo_m22_of_check m22WCCheck_holds

theorem sylowCenterTwo_m23 :
    SylowCenterTwo NativeSporadic.M23 :=
  sylowCenterTwo_m23_of_check m23WCCheck_holds

theorem sylowCenterTwo_m24 :
    SylowCenterTwo NativeSporadic.M24 :=
  sylowCenterTwo_m24_of_check m24WCCheck_holds

end CFSG.CGT.PushingUpLit.E3A

module

public import CFSG.ClassicalInvolution.Q3.TL4ConnBendOut
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscR10E1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf29Kbar
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar

open CFSG.Open CFSG.ClassicalInvolution.Asc77.T3CII
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Out
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {G : Type} [Group G] [Finite G]

theorem le_of_index_eq_two_of_psiK_fpf {K : Subgroup G}
    (y : ↥(Subgroup.normalizer (K : Set G))) (hy : ∀ I, Idx2.act (rhoK K y) I ≠ I)
    {H : Subgroup G} (hH : H.index = 2) : K ≤ H := by
  classical
  haveI hHn : H.Normal := Subgroup.normal_of_index_eq_two hH
  by_contra hKH
  set O := classicalInvolutionOddCore ↥K with hO
  set L : Subgroup ↥K := H.subgroupOf K with hL
  have hOL : O ≤ L := by
    intro x hx
    have hodd : Odd (orderOf x) := by
      have h1 : orderOf (⟨x, hx⟩ : ↥O) ∣ Nat.card ↥O := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card ↥K) h1
    obtain ⟨m, hm⟩ := hodd
    have hx2 : ((x : G) ^ 2) ∈ H := Subgroup.sq_mem_of_index_two hH _
    have : (x : G) = ((x : G) ^ 2) ^ (m + 1) := by
      rw [← pow_mul]
      have h := pow_orderOf_eq_one (x : G)
      rw [Subgroup.orderOf_coe, hm] at h
      calc (x : G) = (x : G) ^ (2 * m + 1) * (x : G) := by rw [h, one_mul]
        _ = (x : G) ^ (2 * (m + 1)) := by
          rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ (x : G) (2 * m + 1)]
    rw [hL, Subgroup.mem_subgroupOf, this]
    exact H.pow_mem hx2 _
  have hLi : L.index = 2 := by
    have hd : L.index ∣ 2 := hH ▸ Subgroup.relIndex_dvd_index_of_normal H K
    have h1 : L.index ≠ 1 := by
      intro h
      apply hKH
      intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ L := by rw [Subgroup.index_eq_one.mp h]; exact Subgroup.mem_top _
      exact this
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd h h1
    · exact h
  set π := QuotientGroup.mk' O with hπ
  set I : Subgroup (Kbar K) := L.map π with hI
  have hIi : I.index = 2 := by
    rw [hI, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective O)
      (by rw [QuotientGroup.ker_mk']; exact hOL), hLi]
  have hIc : Nat.card (Kbar K) = 2 * Nat.card I := by
    rw [← I.index_mul_card, hIi]
  have hle : I.map (rhoK K y).toMonoidHom ≤ I := by
    rintro _ ⟨q, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨conjK K y.1 y.2 k, ?_, rfl⟩
    have hk' : (k : G) ∈ H := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hk)
    change ((conjK K y.1 y.2 k : ↥K) : G) ∈ H
    rw [conjK_apply]
    exact hHn.conj_mem _ hk' _
  have hmap : I.map (rhoK K y).toMonoidHom = I :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (rhoK K y).injective).ge
  let I2 : Idx2 (Kbar K) := ⟨I, hIc⟩
  apply hy I2
  apply Subtype.ext
  refine Subgroup.ext fun q => ?_
  rw [Idx2.act_apply]
  show (rhoK K y).symm q ∈ I ↔ q ∈ I
  rw [← Subgroup.mem_map_equiv, hmap]

theorem eq_one_or_eq_of_mem_zpowers_sq {X : Type*} [Group X] {u v : X} (hv : v * v = 1)
    (h : u ∈ Subgroup.zpowers v) : u = 1 ∨ u = v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hv, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hv, one_zpow, one_mul]

theorem two_group_cases_of_twoTot (L : Subgroup G) [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥)
    (hT : CFSG.ClassicalInvolution.Q3.TL4.Bend.TwoTot (Outer ↥L))
    (S : Subgroup G) (hS : IsPGroup 2 ↥S) :
    ∀ x ∈ S, ∀ y ∈ S, x * x ∈ L → y * y ∈ L → x ∈ L ∨ y ∈ L ∨ x * y ∈ L := by
  classical
  intro x hx y hy hx2 hy2
  let ψ : G →* Outer ↥L := (QuotientGroup.mk' (inner ↥L)).comp MulAut.conjNormal
  have hker : ∀ g : G, ψ g = 1 → g ∈ L := by
    intro g hg
    have h1 : (MulAut.conjNormal g : MulAut ↥L) ∈ inner ↥L :=
      (QuotientGroup.eq_one_iff (N := inner ↥L) _).mp hg
    obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp h1
    set f₀ : G := (f : G) with hf₀
    have hc : g⁻¹ * f₀ ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h2 := congrArg (fun α : MulAut ↥L => ((α ⟨w, hw⟩ : ↥L) : G)) hf
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h2
      calc w * (g⁻¹ * f₀) = g⁻¹ * (g * w * g⁻¹) * f₀ := by group
        _ = g⁻¹ * (f₀ * w * f₀⁻¹) * f₀ := by rw [← h2]
        _ = g⁻¹ * f₀ * w := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hc
    rw [hc]
    exact f.2
  have hker' : ∀ g ∈ L, ψ g = 1 := by
    intro g hg
    refine (QuotientGroup.eq_one_iff (N := inner ↥L) _).mpr ⟨⟨g, hg⟩, ?_⟩
    exact MulAut.conjNormal_val.symm
  have hsq : ∀ g : G, g * g ∈ L → ψ g * ψ g = 1 := fun g hg => by
    rw [← map_mul]
    exact hker' _ hg
  have hP : IsPGroup 2 ↥(S.map ψ) := hS.map ψ
  rcases hT _ hP (ψ x) ⟨x, hx, rfl⟩ (ψ y) ⟨y, hy, rfl⟩ with h | h
  · rcases eq_one_or_eq_of_mem_zpowers_sq (hsq y hy2) h with h1 | h1
    · exact Or.inl (hker x h1)
    · exact Or.inr (Or.inr (hker (x * y) (by rw [map_mul, h1]; exact hsq y hy2)))
  · rcases eq_one_or_eq_of_mem_zpowers_sq (hsq x hx2) h with h1 | h1
    · exact Or.inr (Or.inl (hker y h1))
    · exact Or.inr (Or.inr (hker (x * y) (by rw [map_mul, h1]; exact hsq x hx2)))

theorem twoTot_outer_psl2_odd {p f : ℕ} [Fact p.Prime] (hp : Odd p) (hf : Odd f) :
    CFSG.ClassicalInvolution.Q3.TL4.Bend.TwoTot
      (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f))) := by
  classical
  have hp' := (Fact.out : p.Prime)
  have hf0 : f ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hf)
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0
  haveI : Finite (GaloisField p f) :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp'.pos f).ne')
  haveI : Finite (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p f))) :=
    CFSG.ClassicalInvolution.Q3.TL4.Bend.finite_outer'
  have hdvd := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor hp'
    (GaloisField p f) hK).1
  have hg : Nat.gcd 2 (p ^ f - 1) = 2 := by
    have hodd : Odd (p ^ f) := hp.pow
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  rw [hg] at hdvd
  intro P hP a ha b hb
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hPd : Nat.card P ∣ f * 2 := (Subgroup.card_subgroup_dvd_card P).trans hdvd
  have hn1 : n ≤ 1 := by
    by_contra h
    have h4 : 4 ∣ f * 2 := by
      have : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      exact (this.trans (hn ▸ hPd))
    obtain ⟨j, hj⟩ := hf
    omega
  by_cases ha1 : a = 1
  · left; rw [ha1]; exact Subgroup.one_mem _
  · right
    have hc : Nat.card P = 2 := by
      interval_cases n
      · exfalso
        have : P = ⊥ := Subgroup.eq_bot_of_card_eq P (by simpa using hn)
        exact ha1 (by rw [this] at ha; exact Subgroup.mem_bot.mp ha)
      · simpa using hn
    have hle : Subgroup.zpowers a ≤ P := Subgroup.zpowers_le.mpr ha
    have hge : Nat.card P ≤ Nat.card (Subgroup.zpowers a) := by
      rw [Nat.card_zpowers, hc]
      have h1 : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
      have h0 : 0 < orderOf a := orderOf_pos a
      omega
    exact (Subgroup.eq_of_le_of_card_ge hle hge) ▸ hb

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar

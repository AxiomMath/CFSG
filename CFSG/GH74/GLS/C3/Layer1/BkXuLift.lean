module

public import CFSG.GH74.GLS.C3.Layer1.BkIv10
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma15a
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_sup_of_actHom_mem_range {L M : Subgroup G} (hLM : L ≤ M)
    (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) {u : G} (huM : u ∈ M)
    (h : Back.actHom hLn ⟨u, huM⟩ ∈ (MulAut.conj : kBar L →* MulAut (kBar L)).range) :
    u ∈ L ⊔ CMK M L := by
  obtain ⟨kb, hkb⟩ := h
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective kb
  have hlM : (l : G) ∈ M := hLM l.2
  have h1 : Back.actHom hLn ⟨u, huM⟩ = Back.actHom hLn ⟨(l : G), hlM⟩ := by
    rw [Back.actHom_of_mem hLn l.2 hlM]
    exact hkb.symm
  have h2 : (⟨u, huM⟩ : ↥M) * (⟨(l : G), hlM⟩ : ↥M)⁻¹ ∈ (Back.actHom hLn).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
  rw [Back.actHom_ker hLn, Subgroup.mem_subgroupOf] at h2
  have e : u = (u * (l : G)⁻¹) * l := by group
  rw [e]
  exact (L ⊔ CMK M L).mul_mem (mem_sup_right h2) (mem_sup_left l.2)

theorem not_le_centralizerSection_of_xu {x u : G} {K M : Subgroup G}
    (hCM : centralizer ({x} : Set G) ≤ M) (hLn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hKx : K ≤ centralizer ({x} : Set G))
    (huC : u ∈ centralizer ({x} : Set G)) (hu2 : orderOf u = 2)
    (hcen : ∀ a : kBar K, (∀ b : kBar K, a * b = b * a) → a = 1)
    (hodd : Odd (Nat.card ↥(IVK.xu (Back.actHom hLn ⟨u, hCM huC⟩))))
    (hne : IVK.xu (Back.actHom hLn ⟨u, hCM huC⟩) ≠ ⊥) :
    ¬ pPrimeCoreOf 2 (centralizer ({x, u} : Set G)) ≤ centralizerSection K (pPrimeCoreOf 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : MulAut (kBar K) := Back.actHom hLn ⟨u, hCM huC⟩ with hρ
  set Xb : Subgroup (kBar K) := IVK.xu ρ with hXb
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hbfix : ρ b = b :=
    (IVK.Proofs2.mem_fixedSubgroup_iff').1 (IVK.Proofs2.xu_le_fixedSubgroup ρ hb)
  obtain ⟨c, hcu, hcb⟩ := exists_lift_fixed hu2 (hCM huC) hLn b hbfix
  let D : Subgroup G :=
    (Xb.comap (QuotientGroup.mk' (pPrimeCore 2 ↥K))).map K.subtype ⊓ centralizer ({u} : Set G)
  have memD : ∀ g : G, g ∈ D ↔
      ∃ k : ↥K, (k : G) = g ∧ (QuotientGroup.mk k : kBar K) ∈ Xb ∧ g * u = u * g := by
    intro g
    simp only [D, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap, QuotientGroup.mk'_apply,
      Subgroup.coe_subtype, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, h2⟩
      exact ⟨k, rfl, hk, h2⟩
    · rintro ⟨k, rfl, hk, h2⟩
      exact ⟨⟨k, hk, rfl⟩, h2⟩
  have hcD : (c : G) ∈ D := (memD _).2 ⟨c, rfl, by rw [hcb]; exact hb, hcu⟩
  have hDK : ∀ g ∈ D, g ∈ K := by
    intro g hg
    obtain ⟨k, rfl, -⟩ := (memD g).1 hg
    exact k.2
  have hDC : D ≤ centralizer ({x, u} : Set G) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl
    · exact (mem_centralizer_singleton_iff.1 (hKx (hDK g hg))).symm
    · exact (((memD g).1 hg).choose_spec.2.2).symm
  have hnorm : ∀ z ∈ centralizer ({x, u} : Set G), ∀ d ∈ D, z * d * z⁻¹ ∈ D := by
    intro z hz d hd
    have hzx : x * z = z * x := (mem_centralizer_iff.1 hz) x (by simp)
    have hzu : u * z = z * u := (mem_centralizer_iff.1 hz) u (by simp)
    have hzC : z ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hzx.symm
    have hzM : z ∈ M := hCM hzC
    obtain ⟨k, rfl, hk, hdu⟩ := (memD d).1 hd
    refine (memD _).2 ⟨⟨z * (k : G) * z⁻¹, hLn z hzM k k.2⟩, rfl, ?_, ?_⟩
    · have h1 : (QuotientGroup.mk (⟨z * (k : G) * z⁻¹, hLn z hzM k k.2⟩ : ↥K) : kBar K) =
          Back.actHom hLn ⟨z, hzM⟩ (QuotientGroup.mk k) := (Back.actHom_mk hLn ⟨z, hzM⟩ k).symm
      rw [h1]
      refine IVK.Proofs2.apply_mem_xu ?_ hk
      rw [hρ, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hzu.symm
    · have hzu' : z⁻¹ * u = u * z⁻¹ := by
        calc z⁻¹ * u = z⁻¹ * (u * z) * z⁻¹ := by group
          _ = z⁻¹ * (z * u) * z⁻¹ := by rw [hzu]
          _ = u * z⁻¹ := by group
      calc z * (k : G) * z⁻¹ * u = z * (k : G) * (z⁻¹ * u) := by group
        _ = z * (k : G) * (u * z⁻¹) := by rw [hzu']
        _ = z * ((k : G) * u) * z⁻¹ := by group
        _ = z * (u * (k : G)) * z⁻¹ := by rw [hdu]
        _ = (z * u) * (k : G) * z⁻¹ := by group
        _ = (u * z) * (k : G) * z⁻¹ := by rw [hzu]
        _ = u * (z * (k : G) * z⁻¹) := by group
  have hDodd : Odd (Nat.card ↥D) := by
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    obtain ⟨d, hd2⟩ := exists_prime_orderOf_dvd_card' 2 hev
    have hg2 : orderOf (d : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hd2
    obtain ⟨k, hkg, hkX, -⟩ := (memD (d : G)).1 d.2
    have hsq : ((QuotientGroup.mk k : kBar K)) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : k ^ 2 = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_pow, Subgroup.coe_one, hkg]
        rw [← hg2]
        exact pow_orderOf_eq_one _
      rw [this]
      rfl
    have hord : orderOf (QuotientGroup.mk k : kBar K) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have hodd' : Odd (orderOf (QuotientGroup.mk k : kBar K)) := by
      exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard Xb hkX)
    have h1 : orderOf (QuotientGroup.mk k : kBar K) = 1 := by
      have := Nat.le_of_dvd (by norm_num) hord
      rcases Nat.lt_or_ge (orderOf (QuotientGroup.mk k : kBar K)) 2 with h | h
      · have := orderOf_pos (QuotientGroup.mk k : kBar K)
        omega
      · have h2 : orderOf (QuotientGroup.mk k : kBar K) = 2 := by omega
        rw [h2] at hodd'
        exact absurd hodd' (by decide)
    have hk1 : (QuotientGroup.mk k : kBar K) = 1 := orderOf_eq_one_iff.1 h1
    have hkO : (k : G) ∈ pPrimeCoreOf 2 K :=
      Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨k.2, (QuotientGroup.eq_one_iff _).1 hk1⟩
    have hodd2 : Odd (orderOf (k : G)) :=
      Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) (Subgroup.orderOf_dvd_natCard _ hkO)
    rw [hkg, hg2] at hodd2
    exact absurd hodd2 (by decide)
  have hDle : D ≤ pPrimeCoreOf 2 (centralizer ({x, u} : Set G)) :=
    Back.Setup91.le_pPrimeCoreOf_of_normalized hDC hnorm hDodd
  intro hle
  obtain ⟨-, -, hcomm⟩ := hle (hDle hcD)
  have hcent : ∀ y : kBar K, (QuotientGroup.mk c : kBar K) * y = y * QuotientGroup.mk c := by
    intro y
    induction y using QuotientGroup.induction_on with | H l => ?_
    obtain ⟨_, hc⟩ := Back.Setup91.mem_pPrimeCoreOf_iff.1 (hcomm l l.2)
    have h2 : (⁅(l : G), (c : G)⁆) = ((⁅l, c⁆ : ↥K) : G) := rfl
    have h4 : ⁅(QuotientGroup.mk' (pPrimeCore 2 ↥K)) l, (QuotientGroup.mk' (pPrimeCore 2 ↥K)) c⁆
        = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 hc
    have h5 := commutatorElement_eq_one_iff_mul_comm.1 h4
    exact h5.symm
  have hb0 : b = 1 := by
    rw [← hcb]
    exact hcen _ hcent
  exact hb1 (Subtype.ext hb0)

theorem not_isL34Quotient_of_card_lt {H : Type} [Group H] [Finite H] (hH : Nat.card H < 20160) :
    ¬ IsL34Quotient H := by
  intro h
  have h1 : Nat.card (H ⧸ center H) = 20160 := by
    rw [CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) h]
    decide
  have h2 : Nat.card (H ⧸ center H) ∣ Nat.card H := Subgroup.index_dvd_card (center H)
  have := Nat.le_of_dvd Nat.card_pos h2
  omega

theorem isV2Triple_of_xu {x u : G} {K M T Q : Subgroup G}
    (hh : Hyp9A x K K M T Q) (hsimple : IsSimpleGroup (kBar K))
    (hL34 : ¬ IsL34Quotient (kBar K))
    (huC : u ∈ centralizer ({x} : Set G)) (hu2 : orderOf u = 2)
    (hxu : IVK.xu (Back.actHom hh.L_normal.2 ⟨u, hh.centralizer_le huC⟩) ≠ ⊥ ∧
      Odd (Nat.card ↥(IVK.xu (Back.actHom hh.L_normal.2 ⟨u, hh.centralizer_le huC⟩)))) :
    IsV2Triple x u K := by
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hh.twoTerminal.1.2.2
  have hx2 : orderOf x = 2 := hh.twoTerminal.1.1
  obtain ⟨hcen, -⟩ := no_central_involution hKc hsimple
  have hKx : K ≤ centralizer ({x} : Set G) := hKc.1
  have huM : u ∈ M := hh.centralizer_le huC
  have hunorm : u ∈ normalizer (K : Set G) := U1a.mem_normalizer_of_norm hh.L_normal.2 huM
  have hQC : Q ≤ CxK x K := by rw [hh.hQ]; exact inf_le_right
  refine ⟨⟨⟨hx2, hKc⟩, hu2, huC, hunorm, ?_⟩, hh.twoTerminal, Or.inl ?_, fun h => absurd h hL34⟩
  · exact not_le_centralizerSection_of_xu hh.centralizer_le hh.L_normal.2 hKx huC hu2 hcen hxu.2 hxu.1
  · exact hh.rankQ.trans (Back.pRank_mono' hQC)

end CFSG.GH74.GLS.C3.Layer1.Bk

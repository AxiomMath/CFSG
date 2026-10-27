module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Config
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Involution
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

private theorem mem_u3T_iff {a : G} : a ∈ u3T P x J ↔ a ∈ u3S P x ∧ a ∈ J :=
  Subgroup.mem_inf

private theorem u3_O_eq_one (hcop : Nat.Coprime p (Nat.card (rankThreePrimeCore p J)))
    {g : G} (hg : g ∈ rankThreePrimeCore p J) (hgp : g ^ p = 1) : g = 1 := by
  have hk : orderOf (⟨g, hg⟩ : rankThreePrimeCore p J) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hgp
  have hk2 : orderOf (⟨g, hg⟩ : rankThreePrimeCore p J) ∣ Nat.card (rankThreePrimeCore p J) :=
    orderOf_dvd_natCard _
  have h1 : orderOf (⟨g, hg⟩ : rankThreePrimeCore p J) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hk hk2
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)

private theorem u3_false_of_O_sq (hodd : Odd (Nat.card (rankThreePrimeCore p J))) {g : G}
    (hg : g ∈ rankThreePrimeCore p J) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) : False := by
  have hord : orderOf (⟨g, hg⟩ : rankThreePrimeCore p J) = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      simpa using hg2
    · intro h
      exact hg1 (congrArg Subtype.val h)
  have hdvd := orderOf_dvd_natCard (⟨g, hg⟩ : rankThreePrimeCore p J)
  rw [hord] at hdvd
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨k, hk⟩ := hdvd
  omega

private theorem u3_mem_zpowers_of_orderOf_eq {Z : Subgroup G} [IsCyclic Z] {c z : G}
    (hc : c ∈ Z) (hz : z ∈ Z) (hcz : orderOf c = orderOf z) : c ∈ Subgroup.zpowers z := by
  have heq : Subgroup.zpowers (⟨c, hc⟩ : Z) = Subgroup.zpowers ⟨z, hz⟩ :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by
      rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hcz])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (heq ▸ Subgroup.mem_zpowers (⟨c, hc⟩ : Z))
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem u3_central_of_involution (hc : U3Config G p P M x J)
    (hodd : Odd (Nat.card (rankThreePrimeCore p J)))
    (hcop : Nat.Coprime p (Nat.card (rankThreePrimeCore p J)))
    (hTexp : ∀ t ∈ u3T P x J, t ^ p = 1)
    {z a : G} (hzJ : z ∈ J) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (haT : a ∈ u3T P x J) (ha1 : a ≠ 1) (hza : z * a = a * z) :
    a ∈ u3ZT P x J := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨Q, instQ, ψ, hψsurj, hker, hU3⟩ := hc.u3
  haveI : Finite Q := Finite.of_surjective ψ hψsurj
  have hOlem : ∀ g ∈ rankThreePrimeCore p J, g ^ p = 1 → g = 1 :=
    fun g hg hgp => u3_O_eq_one hcop hg hgp
  have haJ : a ∈ J := (mem_u3T_iff.mp haT).2
  obtain ⟨zJ, hzJ_eq⟩ : ∃ zJ : J, (zJ : G) = z := ⟨⟨z, hzJ⟩, rfl⟩
  obtain ⟨aJ, haJ_eq⟩ : ∃ aJ : J, (aJ : G) = a := ⟨⟨a, haJ⟩, rfl⟩
  have hψz : ψ zJ ≠ 1 := by
    intro h
    have hmem : zJ ∈ ψ.ker := MonoidHom.mem_ker.mpr h
    rw [hker, Subgroup.mem_subgroupOf, hzJ_eq] at hmem
    exact u3_false_of_O_sq hodd hmem hz2 hz1
  have hψz2 : ψ zJ ^ 2 = 1 := by
    have h2 : zJ ^ 2 = 1 := by
      apply Subtype.ext
      simpa [hzJ_eq] using hz2
    rw [← map_pow, h2, map_one]
  have hψa : ψ aJ ≠ 1 := by
    intro h
    have hmem : aJ ∈ ψ.ker := MonoidHom.mem_ker.mpr h
    rw [hker, Subgroup.mem_subgroupOf, haJ_eq] at hmem
    exact ha1 (hOlem a hmem (hTexp a haT))
  have hψza : ψ zJ * ψ aJ = ψ aJ * ψ zJ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [hzJ_eq, haJ_eq, hza]
  obtain ⟨Tq, hTq_def⟩ : ∃ Tq : Subgroup Q, Tq = ((u3T P x J).subgroupOf J).map ψ := ⟨_, rfl⟩
  have hψT : ∀ tJ : J, (tJ : G) ∈ u3T P x J → ψ tJ ∈ Tq := by
    intro tJ htJ
    rw [hTq_def]
    exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr htJ)
  have hTq : IsPGroup p Tq := by
    rw [hTq_def]
    intro g
    obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.mp g.2
    refine ⟨1, ?_⟩
    have hsp : s ^ p = 1 := by
      apply Subtype.ext
      simpa using hTexp (s : G) (Subgroup.mem_subgroupOf.mp hs)
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hsg, ← map_pow, hsp, map_one]
  obtain ⟨T', hT'⟩ := IsPGroup.exists_le_sylow hTq
  have hψaT : ψ aJ ∈ (T' : Subgroup Q) := hT' (hψT aJ (by rw [haJ_eq]; exact haT))
  have hcent := u3_involution_central hc.five hU3 T' hψz hψz2 hψaT hψa hψza
  show a ∈ u3T P x J ⊓ Subgroup.centralizer ((u3T P x J : Subgroup G) : Set G)
  refine Subgroup.mem_inf.mpr ⟨haT, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro t ht
  have htT : t ∈ u3T P x J := ht
  have htJ : t ∈ J := (mem_u3T_iff.mp htT).2
  obtain ⟨tJ, htJ_eq⟩ : ∃ tJ : J, (tJ : G) = t := ⟨⟨t, htJ⟩, rfl⟩
  have hψtT : ψ tJ ∈ (T' : Subgroup Q) := hT' (hψT tJ (by rw [htJ_eq]; exact htT))
  have hcomm_t : ψ tJ * ψ aJ = ψ aJ * ψ tJ := Subgroup.mem_centralizer_iff.mp hcent (ψ tJ) hψtT
  have hψw : ψ ((aJ * tJ)⁻¹ * (tJ * aJ)) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcomm_t, inv_mul_cancel]
  have hwG : (((aJ * tJ)⁻¹ * (tJ * aJ) : J) : G) = (a * t)⁻¹ * (t * a) := by
    simp [haJ_eq, htJ_eq]
  have hwO : (a * t)⁻¹ * (t * a) ∈ rankThreePrimeCore p J := by
    have hw : (aJ * tJ)⁻¹ * (tJ * aJ) ∈ ψ.ker := MonoidHom.mem_ker.mpr hψw
    rw [hker, Subgroup.mem_subgroupOf] at hw
    rw [← hwG]
    exact hw
  have hwT : (a * t)⁻¹ * (t * a) ∈ u3T P x J :=
    mul_mem (inv_mem (mul_mem haT htT)) (mul_mem htT haT)
  have hw1 : (a * t)⁻¹ * (t * a) = 1 := hOlem _ hwO (hTexp _ hwT)
  exact (inv_mul_eq_one.mp hw1).symm

theorem u3_plane_eq (hS : Setting G) (hD1 : TheoremD1 G) (hc : U3Config G p P M x J)
    {z : G} (hzJ : z ∈ J) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) {R : Subgroup G}
    (hRP : R ≤ (P : Subgroup G)) (hRe : IsElemAbelian p R) (hRc : Nat.card R = p ^ 2) (hxR : x ∈ R)
    (hRz : R ≤ Subgroup.centralizer ({z} : Set G)) : R = u3U0 P x J := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨-, hodd⟩ := u3main_core_facts hS hD1 hc.sigma hc.core hc.generic hc.le_cent hc.cent_le
  have hcop : Nat.Coprime p (Nat.card (rankThreePrimeCore p J)) :=
    (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p J).2.2
  obtain ⟨-, hTexp, -, hxJ⟩ := u3_T_structure hc
  obtain ⟨Z, hZcyc, hxZ, -, hZT, -, hTZsup⟩ := u3_S_decomp hc
  obtain ⟨-, hU0card, -, -, -, -, -⟩ := u3U0_facts hc
  obtain ⟨hRcomm, hRexp⟩ := hRe
  have hx1 : x ≠ 1 := fun h => hxJ (by rw [h]; exact Subgroup.one_mem _)
  have hxord : orderOf x = p := orderOf_eq_prime (hRexp x hxR) hx1
  have hcommR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    have h := hRcomm.is_comm.comm (⟨a, ha⟩ : R) ⟨b, hb⟩
    exact congrArg Subtype.val h
  have hRS : R ≤ u3S P x := by
    intro r hr
    show r ∈ (P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)
    refine Subgroup.mem_inf.mpr ⟨hRP hr, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hcommR x hxR r hr
  have hZU : u3ZT P x J ≤ u3U0 P x J := le_sup_left
  have hbU : Subgroup.zpowers x ≤ u3U0 P x J := le_sup_right
  have hRU : R ≤ u3U0 P x J := by
    intro r hr
    have hrS : r ∈ u3T P x J ⊔ Z := by
      rw [hTZsup]
      exact hRS hr
    obtain ⟨a, ha, b, hb, hab⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (A := u3T P x J) (B := Z)
        (fun a ha b hb => (hZT b hb a ha).symm) hrS
    have hcab : Commute a b := (hZT b hb a ha).symm
    have hbp : b ^ p = 1 := by
      have h1 : r ^ p = 1 := hRexp r hr
      rw [← hab, hcab.mul_pow, hTexp a ha, one_mul] at h1
      exact h1
    have hbx : b ∈ Subgroup.zpowers x := by
      rcases (Nat.dvd_prime hc.prime).mp (orderOf_dvd_of_pow_eq_one hbp) with h1 | h1
      · rw [orderOf_eq_one_iff] at h1
        rw [h1]
        exact Subgroup.one_mem _
      · exact u3_mem_zpowers_of_orderOf_eq hb hxZ (by rw [h1, hxord])
    have hbR : b ∈ R := Subgroup.zpowers_le.mpr hxR hbx
    have haR : a ∈ R := by
      have hEq : a = r * b⁻¹ := by rw [← hab, mul_inv_cancel_right]
      rw [hEq]
      exact mul_mem hr (inv_mem hbR)
    have hza : z * a = a * z := Subgroup.mem_centralizer_iff.mp (hRz haR) z (Set.mem_singleton z)
    have haZ : a ∈ u3ZT P x J := by
      by_cases ha1 : a = 1
      · rw [ha1]
        exact Subgroup.one_mem _
      · exact u3_central_of_involution hc hodd hcop hTexp hzJ hz1 hz2 ha ha1 hza
    rw [← hab]
    exact mul_mem (hZU haZ) (hbU hbx)
  exact Subgroup.eq_of_le_of_card_ge hRU (le_of_eq (by rw [hU0card, hRc]))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

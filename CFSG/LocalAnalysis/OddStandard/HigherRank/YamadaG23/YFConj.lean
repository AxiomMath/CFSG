module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJS
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem orderOf_conj_mk_eq_two (hS : HRSetting G L)
    (hZ : Odd (Nat.card ↥(center ↥L))) {w : G} (hw : w ∈ L) (hw2 : orderOf w = 2) :
    orderOf (MulAut.conj (QuotientGroup.mk (⟨w, hw⟩ : ↥L) : L ⧸ center L)) = 2 := by
  have hact : ActsAs L w
      (MulAut.conj (QuotientGroup.mk (⟨w, hw⟩ : ↥L) : L ⧸ center L)) :=
    actsAs_of_mem L hw
  apply orderOf_eq_prime
  · have hsq : w * w = 1 := by
      have h : w ^ 2 = 1 := by simpa [hw2] using pow_orderOf_eq_one w
      simpa [pow_two] using h
    have h := actsAs_mul L hact hact
    rw [hsq] at h
    have heq : MulAut.conj (QuotientGroup.mk (⟨w, hw⟩ : ↥L) : L ⧸ center L) *
        MulAut.conj (QuotientGroup.mk (⟨w, hw⟩ : ↥L) : L ⧸ center L) = 1 :=
      actsAs_unique L h (actsAs_one L)
    simpa [pow_two] using heq
  · intro hα1
    rw [hα1] at hact
    have hwC : w ∈ centralizer (L : Set G) := by
      haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
      exact (actsAs_one_iff L).mp hact
    have hwz : (⟨w, hw⟩ : ↥L) ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hwC g g.2)
    have hdvd : orderOf (⟨w, hw⟩ : ↥L) ∣ Nat.card ↥(center ↥L) :=
      (center ↥L).orderOf_dvd_natCard hwz
    have hdvd' : orderOf w ∣ Nat.card ↥(center ↥L) := by
      rwa [Subgroup.orderOf_mk w hw] at hdvd
    have hodd : Odd (orderOf w) := Odd.of_dvd_nat hZ hdvd'
    rw [hw2] at hodd
    exact hodd.not_two_dvd_nat (dvd_refl 2)

private theorem mem_invols_conj_mk (hS : HRSetting G L)
    (hZ : Odd (Nat.card ↥(center ↥L))) {w : G} (hw : w ∈ L) (hw2 : orderOf w = 2) :
    MulAut.conj (QuotientGroup.mk (⟨w, hw⟩ : ↥L) : L ⧸ center L) ∈
      invols (innerAut (L ⧸ center L)) := by
  refine ⟨?_, orderOf_conj_mk_eq_two hS hZ hw hw2⟩
  rw [innerAut, MonoidHom.mem_range]
  exact ⟨QuotientGroup.mk (⟨w, hw⟩ : ↥L), rfl⟩

theorem s3_invol_conj (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) {u v : G} (hu : u ∈ L) (hu2 : orderOf u = 2) (hv : v ∈ L)
    (hv2 : orderOf v = 2) : ∃ l ∈ L, v = l * u * l⁻¹ := by
  let αu : MulAut (L ⧸ center L) :=
    MulAut.conj (QuotientGroup.mk (⟨u, hu⟩ : ↥L) : L ⧸ center L)
  let αv : MulAut (L ⧸ center L) :=
    MulAut.conj (QuotientGroup.mk (⟨v, hv⟩ : ↥L) : L ⧸ center L)
  have hαu : αu ∈ invols (innerAut (L ⧸ center L)) :=
    mem_invols_conj_mk hS hZ hu hu2
  have hαv : αv ∈ invols (innerAut (L ⧸ center L)) :=
    mem_invols_conj_mk hS hZ hv hv2
  obtain ⟨l', hl', hconj⟩ :=
    s.facts.2.2.2.2.2.1.1.2 αu hαu αv hαv
  rw [innerAut, MonoidHom.mem_range] at hl'
  obtain ⟨q, hq⟩ := hl'
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hacts_l : ActsAs L (l : G) l' := by
    rw [← hq]
    exact actsAs_of_mem L l.2
  have hu_acts : ActsAs L u αu := actsAs_of_mem L hu
  have hv_acts : ActsAs L v αv := actsAs_of_mem L hv
  let w : G := (l : G) * u * (l : G)⁻¹
  have hwL : w ∈ L := L.mul_mem (L.mul_mem l.2 hu) (L.inv_mem l.2)
  have hw_acts : ActsAs L w (l' * αu * l'⁻¹) := by
    simpa only [w] using
      actsAs_mul L (actsAs_mul L hacts_l hu_acts) (actsAs_inv L hacts_l)
  have hw_acts' : ActsAs L w αv := by
    rw [hconj]
    exact hw_acts
  let c : G := v⁻¹ * w
  have hc_acts : ActsAs L c (1 : MulAut (L ⧸ center L)) := by
    have h := actsAs_mul L (actsAs_inv L hv_acts) hw_acts'
    simpa [c] using h
  have hcC : c ∈ centralizer (L : Set G) := by
    haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
    exact (actsAs_one_iff L).mp hc_acts
  have hcL : c ∈ L := L.mul_mem (L.inv_mem hv) hwL
  have hcz : (⟨c, hcL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcC g g.2)
  have hcvd : orderOf (⟨c, hcL⟩ : ↥L) ∣ Nat.card ↥(center ↥L) :=
    (center ↥L).orderOf_dvd_natCard hcz
  have hcvd' : orderOf c ∣ Nat.card ↥(center ↥L) := by
    rwa [Subgroup.orderOf_mk c hcL] at hcvd
  have hcodd : Odd (orderOf c) := Odd.of_dvd_nat hZ hcvd'
  have hu_sq : u ^ 2 = 1 := by simpa [hu2] using pow_orderOf_eq_one u
  have hv_sq : v ^ 2 = 1 := by simpa [hv2] using pow_orderOf_eq_one v
  have hw_sq : w ^ 2 = 1 := by
    show ((l : G) * u * (l : G)⁻¹) ^ 2 = 1
    rw [pow_two]
    calc (l : G) * u * (l : G)⁻¹ * ((l : G) * u * (l : G)⁻¹)
        = (l : G) * (u * u) * (l : G)⁻¹ := by group
      _ = 1 := by rw [← pow_two, hu_sq]; group
  have hvc : v * c = c * v := (Subgroup.mem_centralizer_iff.mp hcC) v hv
  have hw_eq : w = v * c := by
    show w = v * (v⁻¹ * w)
    group
  have hc_sq : c ^ 2 = 1 := by
    have hexp : (v * c) ^ 2 = v ^ 2 * c ^ 2 := by
      simp only [pow_two]
      calc v * c * (v * c) = v * (c * v) * c := by group
        _ = v * (v * c) * c := by rw [← hvc]
        _ = v * v * (c * c) := by group
    have h1 : (v * c) ^ 2 = 1 := by
      rw [← hw_eq]
      exact hw_sq
    rw [hexp] at h1
    simpa [hv_sq] using h1
  have hdiv : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc_sq
  have hc_one : c = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at hcodd
      exact hcodd.not_two_dvd_nat (dvd_refl 2)
  have hvw : v = w := by
    have hinv : v⁻¹ * w = 1 := by
      show c = 1
      exact hc_one
    exact eq_of_inv_mul_eq_one hinv
  exact ⟨(l : G), l.2, by simpa only [w] using hvw⟩

end CFSG.OddStandard.HigherRank.YamadaG23

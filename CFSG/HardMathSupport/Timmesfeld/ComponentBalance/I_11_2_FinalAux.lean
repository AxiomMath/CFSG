module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bonus
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FamilyFixed
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Rank

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem i112_one_le_pRank_of_dvd (hp : p.Prime) (H : Subgroup G) (hd : p ∣ Nat.card H) :
    1 ≤ CFSG.Open.pRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) p hd
  have hord : orderOf (h : G) = p := by rw [Subgroup.orderOf_coe, hh]
  have hle : Subgroup.zpowers (h : G) ≤ H := Subgroup.zpowers_le.2 h.2
  have hcard : Nat.card (Subgroup.zpowers (h : G)) = p ^ 1 := by
    rw [Nat.card_zpowers, hord, pow_one]
  refine CFSG.SectionRank.le_pRank hp.one_lt hle ?_ hcard
  refine isElemAbelian_of_forall (fun a ha b hb => ?_) (fun x hx => ?_)
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow_self (h : G) i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hord, pow_orderOf_eq_one,
      one_zpow]

theorem i112_pRank_eq_zero_of_card_le_one (hp : 1 < p) {H : Subgroup G} (h : Nat.card H ≤ 1) :
    CFSG.Open.pRank p H = 0 :=
  Nat.le_zero.1 (CFSG.SectionRank.pRank_le hp fun _ hE _ => by
    rw [pow_zero]; exact (Subgroup.card_le_of_le hE).trans h)

theorem i112_exists_two_subgroup (h2 : ∃ t : G, orderOf t = 2) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T := by
  obtain ⟨t, ht⟩ := h2
  refine ⟨Subgroup.zpowers t, fun h => ?_, ?_⟩
  · have := Subgroup.zpowers_eq_bot.1 h
    rw [this, orderOf_one] at ht
    omega
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])

theorem i112_pRank_center_le_twoLocal (hp : p.Prime) (h2 : ∃ t : G, orderOf t = 2) :
    CFSG.Open.pRank p (Subgroup.center G) ≤ GLATwoLocalRank p G := by
  obtain ⟨T, hT, hT2⟩ := i112_exists_two_subgroup h2
  obtain ⟨E, hEZ, hEa, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center G)
  exact le_glaTwoLocalRank_of_le_normalizer hp.one_lt hT hT2 hEa
    (hEZ.trans (Subgroup.center_le_normalizer _)) hEc

end Rank

section Centres

variable {X : Type} [Group X] [Finite X] {p : ℕ} {B L : Subgroup X}

theorem i112_card_centreIn_orbit {M : Subgroup X} (hM : M ∈ i112Orbit B L) :
    Nat.card ↥(centreIn M) = Nat.card ↥(Subgroup.center ↥L) := by
  obtain ⟨g, -, rfl⟩ := mem_i112Orbit.1 hM
  rw [centreIn_gLBConj]
  have h : Nat.card ↥(GLBConj g (centreIn L)) = Nat.card ↥(centreIn L) :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [h, card_centreIn]

theorem i112_centreIn_le_Z (hL : IsComponentOf L ⊤) {M : Subgroup X} (hM : M ∈ i112Orbit B L) :
    centreIn M ≤ i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X) := by
  rw [i112_centre_J_eq hL]
  exact le_iSup (fun M : ↥(i112Orbit B L) =>
    (M : Subgroup X) ⊓ Subgroup.centralizer (M : Set X)) ⟨M, hM⟩

theorem i112_isElemAbelian_Z (hL : IsComponentOf L ⊤)
    (hZc : Nat.card ↥(Subgroup.center ↥L) = 1 ∨ Nat.card ↥(Subgroup.center ↥L) = p) :
    IsElemAbelian p (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) := by
  refine i112_isElemAbelian_centre_J hL fun M hM z hz => ?_
  have hdvd : Nat.card ↥(centreIn M) ∣ p := by
    rw [i112_card_centreIn_orbit hM]
    rcases hZc with h | h
    · rw [h]; exact one_dvd _
    · rw [h]
  have hz' : z ∈ centreIn M := hz
  have h1 := orderOf_dvd_natCard (⟨z, hz'⟩ : ↥(centreIn M))
  have h2 : orderOf (⟨z, hz'⟩ : ↥(centreIn M)) ∣ p := h1.trans hdvd
  have h3 : (⟨z, hz'⟩ : ↥(centreIn M)) ^ p = 1 := orderOf_dvd_iff_pow_eq_one.1 h2
  exact congrArg Subtype.val h3

theorem i112_card_Z_eq_one (hL : IsComponentOf L ⊤) (hZ : Nat.card ↥(Subgroup.center ↥L) = 1) :
    Nat.card ↥(i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) = 1 := by
  have h : i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X) = ⊥ := by
    rw [i112_centre_J_eq hL, iSup_eq_bot]
    intro M
    exact Subgroup.eq_bot_of_card_eq _ (by
      have := i112_card_centreIn_orbit (B := B) (L := L) M.2
      rwa [hZ] at this)
  rw [h, Subgroup.card_bot]

theorem i112_conj_mem_Z {y : X} (hy : y ∈ B) {v : X}
    (hv : v ∈ i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) :
    y * v * y⁻¹ ∈ i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X) := by
  have hyN : y ∈ Subgroup.normalizer (i112J B L : Set X) := i112_B_le_normalizer_J hy
  have hyN' : y⁻¹ ∈ Subgroup.normalizer (i112J B L : Set X) :=
    (Subgroup.normalizer (i112J B L : Set X)).inv_mem hyN
  obtain ⟨hvJ, hvC⟩ := Subgroup.mem_inf.1 hv
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hyN v).1 hvJ, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hj' : y⁻¹ * j * y ∈ i112J B L := by
    have := (Subgroup.mem_normalizer_iff.1 hyN' j).1 hj
    simpa using this
  have h1 : (y⁻¹ * j * y) * v = v * (y⁻¹ * j * y) := Subgroup.mem_centralizer_iff.1 hvC _ hj'
  calc j * (y * v * y⁻¹) = y * ((y⁻¹ * j * y) * v) * y⁻¹ := by group
    _ = y * (v * (y⁻¹ * j * y)) * y⁻¹ := by rw [h1]
    _ = (y * v * y⁻¹) * j := by group

theorem i112_pRank_Z_le (hp : p.Prime) (hL : IsComponentOf L ⊤) {r : ℕ}
    (hrel : (Subgroup.normalizer (L : Set X)).relIndex B = p ^ r)
    (hZc : Nat.card ↥(Subgroup.center ↥L) = p) :
    CFSG.Open.pRank p (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ≤ p ^ r := by
  classical
  have : Fintype ↥(i112Orbit B L) := Fintype.ofFinite _
  have hE := i112_isElemAbelian_Z (B := B) hL (Or.inr hZc)
  obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian hp hE
  rw [pRank_eq_of_card hp.one_lt hE hk]
  have hle := (i112_commFam (B := B) hL).card_centreIn_iSup_le_prod
  rw [i112_iSup_fam] at hle
  have hprod : ∏ i : ↥(i112Orbit B L), Nat.card ↥(centreIn (i112Fam B L i)) = p ^ (p ^ r) := by
    have h1 : ∀ i : ↥(i112Orbit B L), Nat.card ↥(centreIn (i112Fam B L i)) = p := fun i => by
      rw [show i112Fam B L i = (i : Subgroup X) from rfl, i112_card_centreIn_orbit i.2, hZc]
    rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, i112_natCard_orbit, hrel]
  rw [hprod] at hle
  have h2 : p ^ k ≤ p ^ (p ^ r) := hk ▸ hle
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h2

theorem i112_iSupIndep_of_numbers (hp : p.Prime) (hL : IsComponentOf L ⊤) {r : ℕ}
    (hrel : (Subgroup.normalizer (L : Set X)).relIndex B = p ^ r)
    (hZc : Nat.card ↥(Subgroup.center ↥L) = 1 ∨ Nat.card ↥(Subgroup.center ↥L) = p)
    (hnum : p ^ CFSG.Open.pRank p (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) =
      Nat.card ↥(Subgroup.center ↥L) ^ (p ^ r)) :
    iSupIndep (i112Fam B L) := by
  classical
  have : Fintype ↥(i112Orbit B L) := Fintype.ofFinite _
  have hE := i112_isElemAbelian_Z (B := B) hL hZc
  obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian hp hE
  refine i112_iSupIndep_of_card_centre hL ?_
  have h1 : ∀ i : ↥(i112Orbit B L), Nat.card ↥(centreIn (i : Subgroup X)) =
      Nat.card ↥(Subgroup.center ↥L) := fun i => i112_card_centreIn_orbit i.2
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, i112_natCard_orbit, hrel, ← hnum,
    pRank_eq_of_card hp.one_lt hE hk]
  exact hk

end Centres

section Fixed

variable {X : Type} [Group X] [Finite X] {p : ℕ} {B L : Subgroup X}

theorem i112_pRank_Z_inf_B_le_one (hp : p.Prime) (hp3 : p = 3) (hO : GLAPPrimeCore p X = ⊥)
    (hB : IsElemAbelian p B) (hL : GLAPComponent p ⊤ L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X))
    (hidx : (Subgroup.normalizer (L : Set X)).relIndex B = p)
    (hZc : Nat.card ↥(Subgroup.center ↥L) = p) :
    CFSG.Open.pRank p ((i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ B) ≤ 1 := by
  have hLc : IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  obtain ⟨b, hbB, hbn⟩ : ∃ b ∈ B, b ∉ Subgroup.normalizer (L : Set X) := by
    by_contra h
    exact hnL fun b hb => by_contra fun hb' => h ⟨b, hb, hb'⟩
  have horb := i112_orbit_eq_pow hp hB hidx hbB hbn
  have hZE := i112_isElemAbelian_Z (B := B) hLc (Or.inr hZc)
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hcomm : ∀ a ∈ i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X),
      ∀ b ∈ i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb.2 a ha.1
  have hcyc : IsCyclic ↥(centreIn L) :=
    isCyclic_of_prime_card (by rw [card_centreIn, hZc])
  have e2 : centreIn (GLBConj b L) = (centreIn L).map (MulAut.conj b⁻¹).toMonoidHom :=
    centreIn_gLBConj b L
  have e3 : centreIn (GLBConj b (GLBConj b L)) =
      (centreIn (GLBConj b L)).map (MulAut.conj b⁻¹).toMonoidHom :=
    centreIn_gLBConj b (GLBConj b L)
  have key : ∀ M ∈ i112Orbit B L, centreIn M ≤
      centreIn L ⊔ centreIn (GLBConj b L) ⊔ centreIn (GLBConj b (GLBConj b L)) := by
    intro M hM
    have hM' := (Set.ext_iff.1 horb M).1 hM
    obtain ⟨i, hi, rfl⟩ := hM'
    have hi' : i < 3 := by simpa using hi
    interval_cases i
    · simp only [pow_zero, gLBConj_one]
      exact le_sup_left.trans le_sup_left
    · simp only [pow_one]
      exact le_sup_right.trans le_sup_left
    · simp only [pow_two, ← gLBConj_gLBConj]
      exact le_sup_right
  refine pRank_inf_le_one_of_conj hp _ (centreIn L) (centreIn (GLBConj b L))
    (centreIn (GLBConj b (GLBConj b L))) hcomm hZE.2 b⁻¹
    (fun v hv => i112_conj_mem_Z (B.inv_mem hbB) hv)
    (i112_centreIn_le_Z hLc i112_self_mem_orbit) hcyc e2.le e3.le ?_ B
    (fun y hy => i116pI_comm hB hy (B.inv_mem hbB))
  rw [i112_centre_J_eq hLc]
  exact iSup_le fun M => key M M.2

end Fixed

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance

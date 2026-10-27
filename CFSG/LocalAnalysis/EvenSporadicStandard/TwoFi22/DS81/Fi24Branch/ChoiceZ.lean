module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.StdBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Sylow

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t z : G}

structure ZData (E : Subgroup G) (t z : G) : Prop where
  syl : ∀ S : Sylow 2 G, Nat.card ↥S = 2 ^ 21
  notConj : ¬ IsConj t z
  conj_tz : IsConj t (t * z)
  card_CNz : Nat.card ↥(CNz E z) = 2 ^ 21 * 3 ^ 3 * 5
  sylow_CNz : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ CNz E z
  card_K : Nat.card ↥(Kg t z) = 2 ^ 19 * 3 ^ 4 * 5

theorem isConj_t_tz (h : M24Out G E t) (hz : IsZ E t z) : IsConj t (t * z) := by
  obtain ⟨n, hn, hnz⟩ := hz.2.2.2
  exact isConj_iff.mpr ⟨n, hnz⟩

theorem card_CNz (h : M24Out G E t) (hz : IsZ E t z) :
    Nat.card ↥(CNz E z) = 2 ^ 21 * 3 ^ 3 * 5 := by
  obtain ⟨y, hyE, hy1, hyn, hycard, hyall⟩ := h.rest
  have hz_mem : z ∈ normClass E y := hyall z hz.1 hz.2.1 hz.2.2.1
  have hclass : (normClass E z).ncard = 1771 := by
    have hset : normClass E z = normClass E y := by
      ext w
      constructor
      · rintro ⟨n, hn, rfl⟩
        obtain ⟨m, hm, hmz⟩ := hz_mem
        exact ⟨n * m, mul_mem hn hm, by rw [← hmz]; group⟩
      · rintro ⟨n, hn, rfl⟩
        obtain ⟨m, hm, hmz⟩ := hz_mem
        exact ⟨n * m⁻¹, mul_mem hn (inv_mem hm), by rw [← hmz]; group⟩
    rw [hset, hycard]
  letI : MulAction ↥(Nrm E) G :=
    MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp (Nrm E).subtype)
  have hsmul : ∀ (n : ↥(Nrm E)) (x : G), n • x = (n : G) * x * (n : G)⁻¹ :=
    fun n x => ConjAct.toConjAct_smul (n : G) x
  have horbit : MulAction.orbit ↥(Nrm E) z = normClass E z := by
    ext w
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨(n : G), n.2, (hsmul n z).symm⟩
    · rintro ⟨n, hn, hnz⟩
      have hnN : n ∈ Nrm E := hn
      refine ⟨⟨n, hnN⟩, ?_⟩
      change (⟨n, hnN⟩ : ↥(Nrm E)) • z = w
      rw [hsmul]
      exact hnz
  have hstab : MulAction.stabilizer ↥(Nrm E) z = (CNz E z).subgroupOf (Nrm E) := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_CNz]
    constructor
    · intro hnz
      refine ⟨n.2, ?_⟩
      rw [hsmul] at hnz
      exact mul_inv_eq_iff_eq_mul.mp hnz
    · rintro ⟨-, hc⟩
      rw [hsmul]
      exact mul_inv_eq_iff_eq_mul.mpr hc
  have hidx : ((CNz E z).subgroupOf (Nrm E)).index = 1771 := by
    rw [← hstab, MulAction.index_stabilizer, horbit]
    exact hclass
  have hcard_sub : Nat.card ↥((CNz E z).subgroupOf (Nrm E)) = Nat.card ↥(CNz E z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (CNz_le_Nrm E z)).toEquiv
  have hmain := Subgroup.card_mul_index ((CNz E z).subgroupOf (Nrm E))
  rw [hcard_sub, hidx, card_Nrm h] at hmain
  rw [show (1771 : ℕ) = 7 * 11 * 23 by norm_num] at hmain
  rw [show 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 * 23 =
      (2 ^ 21 * 3 ^ 3 * 5) * (7 * 11 * 23) by ring] at hmain
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) hmain

theorem not_isConj_t_z
    (h : Std G L E t) (hz : IsZ E t z) : ¬ IsConj t z := by
  intro hconj
  have hzt : Nat.card ↥(centralizer ({z} : Set G)) =
      Nat.card ↥(centralizer ({t} : Set G)) := by
    rw [Subgroup.nat_card_centralizer_nat_card_stabilizer z,
      Subgroup.nat_card_centralizer_nat_card_stabilizer t]
    have hor : MulAction.orbitRel (ConjAct G) G z t := by
      rw [MulAction.orbitRel_apply, ConjAct.mem_orbit_conjAct]
      exact hconj.symm
    exact Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel hor).toEquiv
  have hdvd_z : 2 ^ 21 ∣ Nat.card ↥(centralizer ({z} : Set G)) := by
    have hdvd : Nat.card ↥(CNz E z) ∣ Nat.card ↥(centralizer ({z} : Set G)) := by
      simpa only [Cz] using Subgroup.card_dvd_of_le (CNz_le_Cz E z)
    rw [card_CNz h.m24 hz] at hdvd
    exact dvd_trans (by simpa [mul_assoc] using dvd_mul_right (2 ^ 21) (3 ^ 3 * 5)) hdvd
  have hdvd_t : ¬ 2 ^ 21 ∣ Nat.card ↥(centralizer ({t} : Set G)) := by
    rw [Std.card_H h]
    intro hd
    have h2 : (2 : ℕ) ^ 21 = 2 ^ 19 * 2 ^ 2 := by ring
    rw [h2] at hd
    rw [show 2 ^ 19 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 =
        2 ^ 19 * (3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) by ring] at hd
    have hd' : 2 ^ 2 ∣ 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 :=
      (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2 ^ 19)).mp hd
    norm_num at hd'
  exact hdvd_t (hzt ▸ hdvd_z)

theorem exists_sylow_CNz (hC : CocodeFacts) (h : M24Out G E t)
    (hz : IsZ E t z) : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ CNz E z := by
  have hfac : Nat.factorization (Nat.card ↥(CNz E z)) 2 = 21 := by
    rw [card_CNz h hz, show 2 ^ 21 * 3 ^ 3 * 5 = 2 ^ 21 * (3 ^ 3 * 5) by ring,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3 ^ 3 * 5)]
  let Q : Sylow 2 ↥(CNz E z) := default
  have hQcard : Nat.card ↥(Q : Subgroup ↥(CNz E z)) = 2 ^ 21 := by
    simpa only [hfac] using Sylow.card_eq_multiplicity Q
  let P : Subgroup G := (Q : Subgroup ↥(CNz E z)).map (CNz E z).subtype
  have hPcard : Nat.card ↥P = 2 ^ 21 := by
    dsimp only [P]
    rw [Subgroup.card_map_of_injective (CNz E z).subtype_injective]
    exact hQcard
  have hPle : P ≤ CNz E z := by
    intro x hx
    change x ∈ (Q : Subgroup ↥(CNz E z)).map (CNz E z).subtype at hx
    obtain ⟨q, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact q.2
  have hP2 : IsPGroup 2 P := by
    change IsPGroup 2 ((Q : Subgroup ↥(CNz E z)).map (CNz E z).subtype)
    exact Q.isPGroup'.map (CNz E z).subtype
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  refine ⟨S, ?_⟩
  have hScard : Nat.card ↥(S : Subgroup G) = 2 ^ 21 := card_sylow hC h S
  have hSP : (S : Subgroup G) = P :=
    (Subgroup.eq_of_le_of_card_ge hPS (by rw [hScard, hPcard])).symm
  rw [hSP]
  exact hPle

theorem zData (hC : CocodeFacts)
    (hK : KFacts) (h : Std G L E t) (hz : IsZ E t z) : ZData E t z :=
  ⟨fun S => card_sylow hC h.m24 S, not_isConj_t_z h hz, isConj_t_tz h.m24 hz,
    card_CNz h.m24 hz, exists_sylow_CNz hC h.m24 hz, (hK G L E t z h hz).card_K⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

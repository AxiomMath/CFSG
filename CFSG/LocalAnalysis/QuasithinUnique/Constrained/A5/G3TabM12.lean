module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM12

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

theorem exists_conj_le_of_card_dvd {M : Type*} [Group M] [Finite M] {U H : Subgroup M} {k : ℕ}
    (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) (hUk : Nat.card U = 2 ^ k)
    (hH : 2 ^ k ∣ Nat.card H) : ∃ g : M, U.map (MulAut.conj g).toMonoidHom ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hQ₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 hH
  set Q : Subgroup M := Q₀.map H.subtype with hQ
  have hQcard : Nat.card Q = 2 ^ k := by
    rw [hQ, Subgroup.card_map_of_injective H.subtype_injective, hQ₀]
  have hQp : IsPGroup 2 Q := IsPGroup.of_card hQcard
  have hQi : ¬ 2 ∣ Q.index := by
    have h1 := Subgroup.card_mul_index U
    have h2 := Subgroup.card_mul_index Q
    rw [hUk] at h1
    rw [hQcard] at h2
    have : Q.index = U.index := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < 2) k)
      rw [h1, h2]
    rw [this]
    exact hUi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M (hU.toSylow hUi) (hQp.toSylow hQi)
  refine ⟨g, ?_⟩
  have hg' := congrArg (fun P : Sylow 2 M => (P : Subgroup M)) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at hg'
  have hmap : U.map (MulAut.conj g).toMonoidHom = Q := hg'
  rw [hmap]
  exact Subgroup.map_subtype_le Q₀

theorem card_eq_of_odd_index {M : Type*} [Group M] [Finite M] {U : Subgroup M} {k m : ℕ}
    (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) (hM : Nat.card M = 2 ^ k * m) (hm : ¬ 2 ∣ m) :
    Nat.card U = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hU.exists_card_eq
  have h1 := Subgroup.card_mul_index U
  rw [hj, hM] at h1
  have hm0 : m ≠ 0 := fun h => by simp [h] at hm
  have hi0 : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 := congrArg (padicValNat 2) h1
  rw [padicValNat.mul (by positivity) hi0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hUi, padicValNat.mul (by positivity) hm0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm] at h2
  simp only [add_zero] at h2
  rw [hj, h2]

theorem false_of_m12 {X : Type} [Group X] [Finite X]
    (e : X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M12) {H : Subgroup X} {n : ℕ} (hn : 4 ≤ n)
    (hH : Nat.card H = 60 * 2 ^ n) : False := by
  have hck := M12Lat.cert_check
  set M := Subgroup.closure {g | g ∈ M12Lat.cert.mGens} with hMdef
  have hMcard : Nat.card ↥M = 95040 :=
    M12Lat.cert.card_m (rawIsEnc 12) (LatCert.closedOK_of_check hck) (LatCert.sizesOK_of_check hck)
  let eM : X ≃* ↥M := e.trans (MulEquiv.subgroupCongr M12Lat.mGens_closure).symm
  have : Finite ↥M := Finite.of_equiv X eM.toEquiv
  set H' : Subgroup ↥M := H.map eM.toMonoidHom with hH'
  have hH'card : Nat.card H' = 60 * 2 ^ n := by
    rw [hH', Subgroup.card_map_of_injective eM.injective, hH]
  have hdvd : Nat.card H' ∣ 95040 := hMcard ▸ Subgroup.card_subgroup_dvd_card H'
  have hn4 : n = 4 := by
    by_contra hne
    have hn5 : 5 ≤ n := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn5
    rw [hH'card] at hdvd
    have h128 : 128 ∣ 60 * 2 ^ (5 + m) := ⟨15 * 2 ^ m, by rw [pow_add]; ring⟩
    have := h128.trans hdvd
    omega
  subst hn4
  have hH'960 : Nat.card H' = 960 := by rw [hH'card]; norm_num
  have hU := M12Lat.cert.isSylowTwoOf_top (rawIsEnc 12) hck (k := 6) (m := 1485) (by decide)
    (by decide) (by omega)
  set U : Subgroup ↥M := (Subgroup.closure {g | g ∈ M12Lat.cert.tGens}).subgroupOf M with hUdef
  have hUi : ¬ 2 ∣ U.index := by
    have h1 : (U.subgroupOf (⊤ : Subgroup ↥M)).index = U.index := Subgroup.relIndex_top_right U
    rw [← h1]
    exact hU.2.2
  have hUcard : Nat.card U = 2 ^ 6 :=
    card_eq_of_odd_index (m := 1485) hU.2.1 hUi (by rw [hMcard]; norm_num) (by omega)
  obtain ⟨g, hg⟩ := exists_conj_le_of_card_dvd hU.2.1 hUi hUcard
    (by rw [hH'960]; norm_num : 2 ^ 6 ∣ Nat.card H')
  set Y : Subgroup ↥M := H'.map (MulAut.conj g⁻¹).toMonoidHom with hY
  have hUY : U ≤ Y := by
    intro u hu
    have hmem : (MulAut.conj g).toMonoidHom u ∈ H' := hg ⟨u, hu, rfl⟩
    refine ⟨_, hmem, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    group
  have hYcard : Nat.card Y = 960 := by
    rw [hY, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hH'960]
  obtain ⟨L, -, hLM, hYL, hLcard⟩ := M12Lat.cert.overgroup_cases (rawIsEnc 12) hck Y hUY
  have h1 : Nat.card Y = Nat.card (Subgroup.closure {g | g ∈ L}) := by
    rw [hYL]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
  rw [h1] at hYcard
  have hmem : Nat.card (Subgroup.closure {g | g ∈ L}) ∈ [64, 95040, 192, 192] := hLcard
  rw [hYcard] at hmem
  simp at hmem

end CFSG.QuasithinUnique.A5.G3

module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalInner
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Cat
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Local

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Sporadic.Schreier.Tits
  CFSG.RankThree.PartTwo.Sec4.Item434RemTits

section Nine

variable {G : Type*} [Group G] [Finite G]

theorem nine_dvd_card_inf_centralizer_of_card_eq {R : Subgroup G} (hR : Nat.card R = 27)
    {s : G} (hsR : s ∈ R) (hs1 : s ≠ 1) :
    9 ∣ Nat.card ↥(R ⊓ Subgroup.centralizer ({s} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZC : (Subgroup.center ↥R).map R.subtype ≤ R ⊓ Subgroup.centralizer ({s} : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨s, hsR⟩)).symm
  have hsC : s ∈ R ⊓ Subgroup.centralizer ({s} : Set G) :=
    ⟨hsR, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hCdvd : Nat.card ↥(R ⊓ Subgroup.centralizer ({s} : Set G)) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hR]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hZ3 : 3 ∣ Nat.card ↥((Subgroup.center ↥R).map R.subtype) := by
    rw [Subgroup.card_map_of_injective R.subtype_injective]
    obtain ⟨j, hj0, hj⟩ := IsPGroup.card_center_eq_prime_pow (p := 3) (n := 3)
      (by rw [hR]; norm_num) (by norm_num)
    rw [hj]
    exact dvd_pow_self 3 hj0.ne'
  obtain ⟨m, hm, hmC⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hCdvd
  rw [hmC, show (9 : ℕ) = 3 ^ 2 by norm_num]
  refine pow_dvd_pow 3 ?_
  by_contra hlt
  have hZdvd := Subgroup.card_dvd_of_le hZC
  rw [hmC] at hZdvd
  obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
  ·
    rw [pow_zero] at hZdvd
    exact absurd (Nat.le_of_dvd one_pos (hZ3.trans hZdvd)) (by norm_num)
  ·
    rw [pow_one] at hZdvd hmC
    have hZC' := Subgroup.eq_of_le_of_card_ge hZC
      (by rw [hmC]; exact Nat.le_of_dvd Nat.card_pos hZ3)
    have hsZ : s ∈ (Subgroup.center ↥R).map R.subtype := by
      rw [hZC']
      exact hsC
    obtain ⟨z, hz, hzs⟩ := Subgroup.mem_map.1 hsZ
    have hRC : R ≤ R ⊓ Subgroup.centralizer ({s} : Set G) := by
      intro r hr
      refine ⟨hr, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [← hzs]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨r, hr⟩)
    have hle := Subgroup.card_le_of_le hRC
    rw [hR, hmC] at hle
    norm_num at hle

theorem exists_elemAbelian_nine_le_of_dvd {C : Subgroup G} (hC : 9 ∣ Nat.card C)
    (hCe : ∀ c ∈ C, c ^ 3 = 1) : ∃ Q ≤ C, IsElemAbelian 3 Q ∧ Nat.card Q = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 3 (n := 2)
    (by simpa using hC)
  have hQcard : Nat.card ↥(K.map C.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hK]
    norm_num
  refine ⟨K.map C.subtype, ?_, ⟨?_, ?_⟩, hQcard⟩
  · rintro _ ⟨c, -, rfl⟩
    exact c.2
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hQcard]; norm_num)
  · rintro _ ⟨c, -, rfl⟩
    exact hCe _ c.2

theorem exists_elemAbelian_nine_le_centralizer {R : Subgroup G} (hR : Nat.card R = 27)
    (hRe : ∀ r ∈ R, r ^ 3 = 1) {s : G} (hsR : s ∈ R) (hs1 : s ≠ 1) :
    ∃ Q : Subgroup G, IsElemAbelian 3 Q ∧ Nat.card Q = 9 ∧ ∀ q ∈ Q, q * s = s * q := by
  obtain ⟨Q, hQC, hQe, hQ9⟩ := exists_elemAbelian_nine_le_of_dvd
    (nine_dvd_card_inf_centralizer_of_card_eq hR hsR hs1) fun c hc => hRe c hc.1
  exact ⟨Q, hQe, hQ9, fun q hq => Subgroup.mem_centralizer_singleton_iff.1 (hQC hq).2⟩

end Nine

section Tits

theorem titsD_exists_elemAbelian_nine
    {k : titsD} (hk : orderOf k = 3) :
    ∃ Q : Subgroup titsD, IsElemAbelian 3 Q ∧ Nat.card Q = 9 ∧ ∀ q ∈ Q, q * k = k * q := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylGrp hk
  have hR : Nat.card ↥(sylD.map (MulAut.conj g⁻¹).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective, card_sylD,
      RankThree.PartTwo.Sec4.Item434RemTits.factorization_card_titsD]
    norm_num
  have hRe : ∀ r ∈ sylD.map (MulAut.conj g⁻¹).toMonoidHom, r ^ 3 = 1 := by
    rintro _ ⟨r, hr, rfl⟩
    have h3 : (r : Equiv.Perm (Fin 1755)) * r * r = 1 :=
      cube_of_mem_sylPerms (mem_sylGrp.1 (Subgroup.mem_subgroupOf.1 hr))
    have hr3 : r ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, pow_three']
      exact h3
    rw [← map_pow, hr3, map_one]
  have hkR : k ∈ sylD.map (MulAut.conj g⁻¹).toMonoidHom := by
    refine ⟨g * k * g⁻¹, Subgroup.mem_subgroupOf.2 hg, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hk
    exact absurd hk (by norm_num)
  exact exists_elemAbelian_nine_le_centralizer hR hRe hkR hk1


theorem isLocallyBalancedAbs_three_one_titsD : IsLocallyBalancedAbs 3 1 titsD := by
  intro D hD hcard H hH _
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one_of_card_eq_prime Nat.prime_three hcard
  have hd3 : d ^ 3 = 1 := hD.2 d hdD
  have hdin : d ∈ innerAut titsD :=
    mem_innerAut_of_pow_eq_one_of_hom
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner titsD))
      (fun α hα => (QuotientGroup.eq_one_iff α).1 hα) (m := 2)
      (fun y => orderOf_dvd_iff_pow_eq_one.1
        ((orderOf_dvd_natCard y).trans (dvd_of_eq card_outer_titsD)))
      (by norm_num) hd3
  obtain ⟨k, rfl⟩ := hdin
  have hk3 : orderOf k = 3 := by
    rw [← orderOf_injective _ LocalTwoBalance.Cross.TitsAux.conj_injective_titsD k]
    exact orderOf_eq_prime hd3 hd1
  obtain ⟨Q, hQe, hQ9, hQk⟩ := titsD_exists_elemAbelian_nine hk3
  refine localDeltaIn_eq_bot_of_core_eq_bot hdD hd1 ?_
  refine noSignalizer hQe hQ9 _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (coprime_card_GLAPPrimeCoreOf Nat.prime_three _)) ?_
  rintro _ ⟨q, hq, rfl⟩
  have hqC : MulAut.conj q ∈
      H ⊓ Subgroup.centralizer ({MulAut.conj k} : Set (MulAut titsD)) := by
    refine Subgroup.mem_inf.2 ⟨hH (MonoidHom.mem_range.2 ⟨q, rfl⟩),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have e1 := map_mul (MulAut.conj : titsD →* MulAut titsD) q k
    have e2 := map_mul (MulAut.conj : titsD →* MulAut titsD) k q
    rw [← e1, ← e2, hQk q hq]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨GLAPPrimeCoreOf_conj_mem _ hqC y, fun h => ?_⟩
  have h1 := GLAPPrimeCoreOf_conj_mem _ (inv_mem hqC) _ h
  have e : (MulAut.conj q)⁻¹ * (MulAut.conj q * y * (MulAut.conj q)⁻¹) * (MulAut.conj q)⁻¹⁻¹ =
      y := by group
  rwa [e] at h1


theorem isLocallyBalancedAbs_three_one_tits (hv : TauCeti.LieTypeIndex.tits.Valid) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := by
  obtain ⟨e⟩ := LocalTwoBalance.Cross.TitsAux.nonempty_mulEquiv_titsD_cat hv
  exact IsLocallyBalancedAbs.of_mulEquiv e isLocallyBalancedAbs_three_one_titsD

end Tits

end CFSG.HardMathSupport.Dickson.Bal207

module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusDickson
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem le_three_of_odd_dvd_twelve : ∀ m : ℕ, m ≤ 12 → Odd m → m ∣ 12 → m ≤ 3 := by decide

theorem le_three_of_odd_dvd_twentyfour : ∀ m : ℕ, m ≤ 24 → Odd m → m ∣ 24 → m ≤ 3 := by decide

theorem le_five_or_eq_of_odd_dvd_sixty :
    ∀ m : ℕ, m ≤ 60 → Odd m → m ∣ 60 → m ≤ 5 ∨ m = 15 := by decide

theorem le_normalizer_or_coordinateG_le
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hK : Nat.card K = p ^ f) (hq4 : Nat.card K % 4 = 1)
    (hq13 : 13 ≤ Nat.card K) (Cb Y : Subgroup (Equiv.Perm (Omega K))) (hCY : Cb ≤ Y)
    (hYD : Y ≤ coordinateD K) (hC : IsCyclic Cb) (hCcard : Nat.card Cb = (Nat.card K + 1) / 2) :
    Y ≤ Subgroup.normalizer (Cb : Set (Equiv.Perm (Omega K))) ∨ coordinateG K ≤ Y := by
  classical
  have _hCcyc : IsCyclic Cb := hC
  have : Fact p.Prime := ⟨hp⟩
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hK
    omega
  obtain ⟨m, hm⟩ : ∃ m, m = (Nat.card K + 1) / 2 := ⟨_, rfl⟩
  rw [← hm] at hCcard
  have hm2 : 2 * m = Nat.card K + 1 := by omega
  have hmodd : Odd m := ⟨(Nat.card K + 1) / 4, by omega⟩
  have hm7 : 7 ≤ m := by omega
  have hpq : p ∣ Nat.card K := hK ▸ dvd_pow_self p hf
  have hpm : Nat.Coprime p m := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_
    have h1 : p ∣ 2 * m := dvd_mul_of_dvd_right h 2
    rw [hm2] at h1
    have h2 := (Nat.dvd_add_right hpq).mp h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hcop1 : Nat.Coprime m ((Nat.card K - 1) / 2) := by
    have h1 : m = 1 + (Nat.card K - 1) / 2 := by omega
    rw [h1]
    exact Nat.coprime_add_self_left.mpr (Nat.coprime_one_left _)
  have hmq1 : ¬ m ∣ (Nat.card K - 1) / 2 := fun h => by
    have := Nat.Coprime.eq_one_of_dvd hcop1 h
    omega
  set Y₀ : Subgroup (Equiv.Perm (Omega K)) := Y ⊓ coordinateG K with hY₀def
  have hCodd : Odd (Nat.card Cb) := hCcard ▸ hmodd
  have hCG : Cb ≤ coordinateG K := le_coordinateG_of_odd hp hpodd hK (hCY.trans hYD) hCodd
  have hCY₀ : Cb ≤ Y₀ := le_inf hCY hCG
  have hmY₀ : m ∣ Nat.card Y₀ := hCcard ▸ Subgroup.card_dvd_of_le hCY₀
  have hY₀G : Y₀ ≤ coordinateG K := inf_le_right
  have hY₀n : ∀ y ∈ Y, ∀ z ∈ Y₀, y * z * y⁻¹ ∈ Y₀ := by
    intro y hy z hz
    refine ⟨Y.mul_mem (Y.mul_mem hy hz.1) (Y.inv_mem hy), ?_⟩
    have hyN := coordinateE_le_normalizer_G K (coordinateD_le_E K (hYD hy))
    exact (Subgroup.mem_normalizer_iff.mp hyN z).mp hz.2
  have hnorm : (Nat.card Y₀ = m ∨ Nat.card Y₀ = 2 * m) →
      Y ≤ Subgroup.normalizer (Cb : Set (Equiv.Perm (Omega K))) := by
    intro hcard y hy
    apply mem_normalizer_of_conj_mem
    have hZY₀ : Cb.map (MulAut.conj y).toMonoidHom ≤ Y₀ := by
      rintro _ ⟨c, hc, rfl⟩
      exact hY₀n y hy c (hCY₀ hc)
    have hZcard : Nat.card (Cb.map (MulAut.conj y).toMonoidHom) = m := by
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hCcard]
    have hZeq : Cb.map (MulAut.conj y).toMonoidHom = Cb := by
      rcases hcard with h | h
      · have h1 := Subgroup.eq_of_le_of_card_ge hZY₀ (by rw [h, hZcard])
        have h2 := Subgroup.eq_of_le_of_card_ge hCY₀ (by rw [h, hCcard])
        rw [h1, h2]
      · have hidx : ((Cb.map (MulAut.conj y).toMonoidHom).subgroupOf Y₀).index = 2 := by
          have h1 := ((Cb.map (MulAut.conj y).toMonoidHom).subgroupOf Y₀).card_mul_index
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY₀).toEquiv, hZcard, h] at h1
          have h2 : m * ((Cb.map (MulAut.conj y).toMonoidHom).subgroupOf Y₀).index = m * 2 := by
            linarith
          exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) h2
        have hCZ : Cb ≤ Cb.map (MulAut.conj y).toMonoidHom := by
          intro c hc
          have hodd : Odd (orderOf (⟨c, hCY₀ hc⟩ : Y₀)) := by
            rw [Subgroup.orderOf_mk]
            exact hCodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Cb hc)
          exact Subgroup.mem_subgroupOf.mp (mem_of_index_two_of_odd hidx hodd)
        exact (Subgroup.eq_of_le_of_card_ge hCZ (by rw [hZcard, hCcard])).symm
    intro c hc
    have h1 : y * c * y⁻¹ ∈ Cb.map (MulAut.conj y).toMonoidHom := ⟨c, hc, rfl⟩
    rw [hZeq] at h1
    exact h1
  set ψ : coordinateG K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    (pslEquivCoordinateG K).symm.toMonoidHom with hψdef
  set H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    (Y₀.subgroupOf (coordinateG K)).map ψ with hHdef
  let e : Y₀ ≃* H := (Subgroup.subgroupOfEquivOfLe hY₀G).symm.trans
    ((Y₀.subgroupOf (coordinateG K)).equivMapOfInjective ψ (pslEquivCoordinateG K).symm.injective)
  have hHcard : Nat.card H = Nat.card Y₀ := (Nat.card_congr e.toEquiv).symm
  have hmH : m ∣ Nat.card H := hHcard ▸ hmY₀
  have hqodd : Odd (Nat.card K) := hK ▸ hpodd.pow
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := by
    obtain ⟨k, hk⟩ := hqodd
    rw [show Nat.card K - 1 = 2 * k by omega]
    exact Nat.gcd_mul_right_left k 2
  have hm2' : Nat.Coprime m 2 := Nat.coprime_two_right.mpr hmodd
  have hmp : ∀ k : ℕ, Nat.Coprime m (p ^ k) := fun k => Nat.Coprime.pow_right k hpm.symm
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK H with
    hEA | ⟨z, hz, hzc, -⟩ | ⟨z, hz, hzc, -⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨k, t, -, ht, N, Cc, hNn, -, hNcard, -, hCcard', hdisj, hsup⟩ |
      ⟨k, hk0, hkf, ⟨eP⟩⟩ | ⟨k, hk0, hkf, ⟨eP⟩⟩
  ·
    exfalso
    have hPG : IsPGroup p H := IsElementaryAbelian.isPGroup p H
    obtain ⟨k, hk⟩ := hPG.exists_card_eq
    rw [hk] at hmH
    have := Nat.Coprime.eq_one_of_dvd (hmp k) hmH
    omega
  ·
    left
    apply hnorm
    rw [← hHcard, hzc]
    rw [hgcd] at hz
    rcases hz with hz | hz
    · exact absurd ((hzc ▸ hmH).trans hz) hmq1
    · left
      rw [← hm] at hz
      exact Nat.dvd_antisymm hz (hzc ▸ hmH)
  ·
    left
    apply hnorm
    rw [← hHcard, hzc]
    have hmz : m ∣ z := Nat.Coprime.dvd_of_dvd_mul_left hm2' (hzc ▸ hmH)
    rw [hgcd] at hz
    rcases hz with hz | hz
    · exact absurd (hmz.trans hz) hmq1
    · right
      rw [← hm] at hz
      rw [Nat.dvd_antisymm hz hmz]
  ·
    exfalso
    have h12 : Nat.card H = 12 := by
      rw [Nat.card_congr eA4.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [h12] at hmH
    have := le_three_of_odd_dvd_twelve m (Nat.le_of_dvd (by norm_num) hmH) hmodd hmH
    omega
  ·
    exfalso
    have h24 : Nat.card H = 24 := by
      rw [Nat.card_congr eS4.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
    rw [h24] at hmH
    have := le_three_of_odd_dvd_twentyfour m (Nat.le_of_dvd (by norm_num) hmH) hmodd hmH
    omega
  ·
    exfalso
    have h60 : Nat.card H = 60 := by
      rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [h60] at hmH
    have hm15 : m = 15 := by
      rcases le_five_or_eq_of_odd_dvd_sixty m (Nat.le_of_dvd (by norm_num) hmH) hmodd hmH with
        h | h
      · omega
      · exact h
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup Y₀ := (e.trans eA5).isSimpleGroup
    have hY₀card : Nat.card Y₀ = 60 := hHcard ▸ h60
    have hZcard : Nat.card (Cb.subgroupOf Y₀) = 15 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCY₀).toEquiv, hCcard, hm15]
    have hZidx : (Cb.subgroupOf Y₀).index = 4 := by
      have h1 := (Cb.subgroupOf Y₀).card_mul_index
      rw [hZcard, hY₀card] at h1
      omega
    have hcore := (Cb.subgroupOf Y₀).index_normalCore_dvd_factorial_index
    rcases (Subgroup.normalCore_normal (Cb.subgroupOf Y₀)).eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.index_bot, hY₀card, hZidx] at hcore
      exact absurd hcore (by decide)
    · have htop : Cb.subgroupOf Y₀ = ⊤ :=
        eq_top_iff.mpr (h ▸ Subgroup.normalCore_le (Cb.subgroupOf Y₀))
      rw [htop, Subgroup.card_top, hY₀card] at hZcard
      exact absurd hZcard (by norm_num)
  ·
    exfalso
    have hCN : Cc ≤ Subgroup.normalizer (N : Set H) := fun c _ =>
      Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => hNn.conj_mem n hn c, fun hn => by
        have h1 := hNn.conj_mem _ hn c⁻¹
        simpa [mul_assoc] using h1⟩
    have hsupcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer N Cc hCN
      hdisj
    rw [hsup, Subgroup.card_top, hNcard, hCcard'] at hsupcard
    rw [hsupcard] at hmH
    have hmt : m ∣ t := Nat.Coprime.dvd_of_dvd_mul_left (hmp k) hmH
    rw [← hK, hgcd] at ht
    exact hmq1 (hmt.trans ht)
  ·
    have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
    have hoddk : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p k)) :=
      ⟨p, k, hp, hpodd, Nat.one_le_iff_ne_zero.mpr hk0, hcardF⟩
    have hHc : Nat.card H = p ^ k * ((p ^ k) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr eP.toEquiv, CFSG.GorensteinWalter.psl2_card_formula _ hoddk, hcardF]
    by_cases hkf' : k = f
    ·
      right
      subst hkf'
      have hKodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
        ⟨p, k, hp, hpodd, Nat.one_le_iff_ne_zero.mpr hk0, hK⟩
      have hG : Nat.card (coordinateG K) = p ^ k * ((p ^ k) ^ 2 - 1) / 2 := by
        rw [← Nat.card_congr (pslEquivCoordinateG K).toEquiv,
          CFSG.GorensteinWalter.psl2_card_formula K hKodd, hK]
      have hY₀eq : Y₀ = coordinateG K :=
        Subgroup.eq_of_le_of_card_ge hY₀G (by rw [hG, ← hHcard, hHc])
      rw [← hY₀eq]
      exact inf_le_left
    · exfalso
      obtain ⟨c, hc⟩ := hkf
      have hc2 : 2 ≤ c := by
        rcases c with _ | _ | c
        · omega
        · exact absurd (by rw [hc]; ring) hkf'
        · omega
      have hpk3 : 3 ≤ p ^ k := by
        have := hp.two_le
        rcases hpodd with ⟨r, hr⟩
        have : p ≤ p ^ k := Nat.le_self_pow hk0 p
        omega
      have heven : 2 ∣ (p ^ k) ^ 2 - 1 := by
        have h1 : Odd ((p ^ k) ^ 2) := (hpodd.pow).pow
        exact (Nat.Odd.sub_odd h1 odd_one).two_dvd
      rw [hHc, Nat.mul_div_assoc _ heven] at hmH
      have hmd : m ∣ ((p ^ k) ^ 2 - 1) / 2 := Nat.Coprime.dvd_of_dvd_mul_left (hmp k) hmH
      have hle : (p ^ k) ^ 2 ≤ Nat.card K := by
        rw [hK, hc, ← pow_mul]
        exact Nat.pow_le_pow_right hp.pos (by nlinarith)
      have hpos : 0 < ((p ^ k) ^ 2 - 1) / 2 := by
        have : 9 ≤ (p ^ k) ^ 2 := by nlinarith
        omega
      have := Nat.le_of_dvd hpos hmd
      omega
  ·
    exfalso
    have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
    have hHc : Nat.card H = p ^ k * ((p ^ k) ^ 2 - 1) := by
      rw [Nat.card_congr eP.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula, hcardF]
    rw [hHc] at hmH
    have hmd : m ∣ (p ^ k) ^ 2 - 1 := Nat.Coprime.dvd_of_dvd_mul_left (hmp k) hmH
    have hpk3 : 3 ≤ p ^ k := by
      have := hp.two_le
      rcases hpodd with ⟨r, hr⟩
      have : p ≤ p ^ k := Nat.le_self_pow hk0 p
      omega
    obtain ⟨c, hc⟩ := hkf
    have hc1 : 1 ≤ c := by
      rcases c with _ | c
      · omega
      · omega
    by_cases hc1' : c = 1
    ·
      subst hc1'
      have hsq : (p ^ k) ^ 2 = Nat.card K := by rw [hK, hc, mul_one]; ring
      rw [hsq] at hmd
      have h2 : m ∣ 2 := by
        have h3 : m ∣ 2 * m := dvd_mul_left m 2
        have h4 := Nat.dvd_sub h3 hmd
        rwa [show 2 * m - (Nat.card K - 1) = 2 by omega] at h4
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    ·
      have hle : 3 * (p ^ k) ^ 2 ≤ Nat.card K := by
        rw [hK, hc]
        have h1 : 2 * k + 1 ≤ 2 * k * c := by
          have : 2 ≤ c := by omega
          have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
          nlinarith
        calc 3 * (p ^ k) ^ 2 ≤ p * (p ^ k) ^ 2 := by
              apply Nat.mul_le_mul_right
              have := hp.two_le
              rcases hpodd with ⟨r, hr⟩
              omega
          _ = p ^ (2 * k + 1) := by rw [← pow_mul, mul_comm k 2, pow_succ, mul_comm]
          _ ≤ p ^ (2 * k * c) := Nat.pow_le_pow_right hp.pos h1
      have hpos : 0 < (p ^ k) ^ 2 - 1 := by
        have : 9 ≤ (p ^ k) ^ 2 := by nlinarith
        omega
      have := Nat.le_of_dvd hpos hmd
      omega

end CFSG.Semidihedral.FixedCoreNontrivial

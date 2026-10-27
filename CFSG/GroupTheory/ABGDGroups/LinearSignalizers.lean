module

public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers

public noncomputable section

namespace CFSG.ABGDGroups

open CFSG.GorensteinWalter (PGammaL2 PSL2 PGL2 IsOddPrimePower pGammaL2PSLRange
  pGammaL2PGLRange mem_pGammaL2PSLRange_iff)
open scoped commutatorElement

section Tori

variable {F : Type} [Field F] [Finite F]

theorem mem_of_mem_sup_zpowers_of_odd {G : Type*} [Group G] {U : Subgroup G} {w : G}
    (hwU : w ∉ U) (hw : w * w = 1) (hinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) {x : G}
    (hx : x ∈ U ⊔ Subgroup.zpowers w) (hxo : Odd (orderOf x)) : x ∈ U := by
  obtain ⟨u, hu, rfl | rfl⟩ :=
    (CFSG.GorensteinWalter.mem_sup_zpowers_of_involution_inverts hwU hw hinv).mp hx
  · exact hu
  · have h2 : (u * w) ^ 2 = 1 := by
      have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
      calc (u * w) ^ 2 = u * (w * u * w⁻¹) := by rw [sq, hw']; group
        _ = 1 := by rw [hinv u hu, mul_inv_cancel]
    have h1 : orderOf (u * w) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h1' : orderOf (u * w) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · rw [h] at hxo
        exact absurd hxo (by decide)
    rw [orderOf_eq_one_iff] at h1'
    rw [h1']
    exact U.one_mem

theorem psl2_le_of_isCyclic_of_inf_ne_bot {p f : ℕ} [Fact p.Prime] (hcard : Nat.card F = p ^ f)
    (hp2 : p ≠ 2) (h3 : 3 < Nat.card F) {R Y : Subgroup (PSL2 F)} [hRc : IsCyclic R]
    (hR : Nat.card R = (Nat.card F - 1) / 2 ∨ Nat.card R = (Nat.card F + 1) / 2) [hYc : IsCyclic Y]
    (hRY : R ⊓ Y ≠ ⊥) : Y ≤ R := by
  classical
  have hp : p.Prime := Fact.out
  have hqodd : Odd (Nat.card F) := by
    rw [hcard]
    obtain ⟨f', rfl⟩ | h := Nat.even_or_odd f
    · exact (hp.odd_of_ne_two hp2).pow
    · exact (hp.odd_of_ne_two hp2).pow
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    obtain ⟨a, ha⟩ := hqodd
    rw [ha, Nat.add_sub_cancel, Nat.gcd_comm]
    simp
  obtain ⟨P⟩ : Nonempty (Sylow p (PSL2 F)) := inferInstance
  obtain ⟨U₀, S₀, -, hU₀, -, hS₀, hpart⟩ :=
    CFSG.Glauberman.Dickson.huppert_II_8_5_a_psl2_cover hcard P
  rw [hgcd] at hU₀ hS₀
  obtain ⟨⟨r, hrR⟩, hr⟩ := hRc.exists_generator
  have hRr : R = Subgroup.zpowers r := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hr ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]
      exact hrR
  have hRcard2 : 2 ≤ Nat.card R := by
    obtain ⟨a, ha⟩ := hqodd
    rcases hR with h | h <;> omega
  have hr1 : r ≠ 1 := by
    intro h
    rw [hRr, h, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hRcard2
    omega
  obtain ⟨X, ⟨hrX, hXmem⟩, -⟩ := hpart r hr1
  have hRX : R ≤ X := by
    rw [hRr, Subgroup.zpowers_le]
    exact hrX
  have hdvd := Subgroup.card_dvd_of_le hRX
  have hXR : X = R := by
    apply (Subgroup.eq_of_le_of_card_ge hRX _).symm
    rcases hXmem with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exfalso
      have hXp : IsPGroup p ((P : Subgroup (PSL2 F)).map (MulAut.conj g).toMonoidHom) :=
        P.isPGroup'.map _
      obtain ⟨n, hn⟩ := hXp.exists_card_eq
      rw [hn] at hdvd
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [hj, pow_zero] at hRcard2
        omega
      have hpR : p ∣ Nat.card R := by rw [hj]; exact dvd_pow_self p hj0
      have hpq : p ∣ Nat.card F := by
        rw [hcard]
        apply dvd_pow_self
        rintro rfl
        rw [pow_zero] at hcard
        omega
      obtain ⟨a, ha⟩ := hqodd
      rcases hR with h | h
      · rw [h] at hpR
        have h1 : p ∣ Nat.card F - 2 * ((Nat.card F - 1) / 2) :=
          Nat.dvd_sub hpq (dvd_mul_of_dvd_right hpR 2)
        rw [show Nat.card F - 2 * ((Nat.card F - 1) / 2) = 1 by omega] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
      · rw [h] at hpR
        have h1 : p ∣ 2 * ((Nat.card F + 1) / 2) - Nat.card F :=
          Nat.dvd_sub (dvd_mul_of_dvd_right hpR 2) hpq
        rw [show 2 * ((Nat.card F + 1) / 2) - Nat.card F = 1 by omega] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hU₀] at hdvd ⊢
      obtain ⟨a, ha⟩ := hqodd
      rcases hR with h | h
      · rw [h]
      · rw [h] at hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hS₀] at hdvd ⊢
      obtain ⟨a, ha⟩ := hqodd
      rcases hR with h | h
      · rw [h] at hdvd
        have h' : (Nat.card F - 1) / 2 ∣ (Nat.card F + 1) / 2 - (Nat.card F - 1) / 2 :=
          Nat.dvd_sub hdvd dvd_rfl
        rw [show (Nat.card F + 1) / 2 - (Nat.card F - 1) / 2 = 1 by omega] at h'
        have := Nat.le_of_dvd one_pos h'
        omega
      · rw [h]
  obtain ⟨⟨y, hyY⟩, hy⟩ := hYc.exists_generator
  have hYy : Y = Subgroup.zpowers y := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hy ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]
      exact hyY
  by_cases hy1 : y = 1
  · rw [hYy, hy1, Subgroup.zpowers_one_eq_bot]
    exact bot_le
  obtain ⟨Xy, ⟨hyXy, hXymem⟩, -⟩ := hpart y hy1
  have hYXy : Y ≤ Xy := by
    rw [hYy, Subgroup.zpowers_le]
    exact hyXy
  obtain ⟨a, ⟨haR, haY⟩, ha1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hRY
  have hXyR : Xy = R :=
    (hpart a ha1).unique ⟨hYXy haY, hXymem⟩ ⟨haR, hXR ▸ hXmem⟩
  rw [← hXyR]
  exact hYXy

theorem pgl2_le_centralizer_of_inf_ne_bot (hF : IsOddPrimePower (Nat.card F))
    {Y : Subgroup (PGL2 F)}
    (hYJ : Y ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    (hY : Odd (Nat.card Y)) [hYc : IsCyclic Y] {v : PGL2 F} (hv : orderOf v = 2)
    (hYv : Y ⊓ Subgroup.centralizer ({v} : Set (PGL2 F)) ≠ ⊥) :
    Y ≤ Subgroup.centralizer ({v} : Set (PGL2 F)) := by
  classical
  set toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) with htoPGL
  have hinj : Function.Injective toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  set J := toPGL.range with hJdef
  have hJindex : J.index = 2 := CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two F hF
  have hJn : J.Normal := Subgroup.normal_of_index_eq_two hJindex
  have hF' := hF
  obtain ⟨p, f, hp, hpodd, hf, hcard⟩ := hF'
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact absurd hpodd (by decide)
  have hqodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have hv1 : v ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hv
    exact absurd hv (by norm_num)
  have hvI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution v :=
    ⟨hv1, by have h := pow_orderOf_eq_one v; rwa [hv] at h⟩
  by_cases h3 : Nat.card F = 3
  ·
    have h12 : Nat.card (PSL2 F) = 12 := by
      rw [CFSG.GorensteinWalter.psl2_card_formula F hF, h3]
      norm_num
    have hYcard : Nat.card Y ∣ 3 := by
      have hdvd : Nat.card Y ∣ 3 * 4 := by
        have h := Subgroup.card_dvd_of_le hYJ
        rw [hJdef, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj,
          Subgroup.card_top, h12] at h
        exact h
      have hcop : Nat.Coprime (Nat.card Y) 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact (Nat.coprime_two_right.mpr hY).pow_right 2
      exact hcop.dvd_of_dvd_mul_right hdvd
    have hle : Y ⊓ Subgroup.centralizer ({v} : Set (PGL2 F)) ≤ Y := inf_le_left
    have hne : Nat.card ↥(Y ⊓ Subgroup.centralizer ({v} : Set (PGL2 F))) ≠ 1 := by
      rwa [Ne, Subgroup.card_eq_one]
    have hdvd := (Subgroup.card_dvd_of_le hle).trans hYcard
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · have hY3 : Nat.card Y = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hYcard with h' | h'
        · have := Subgroup.card_le_of_le hle
          omega
        · exact h'
      have := Subgroup.eq_of_le_of_card_ge hle (by rw [h, hY3])
      rw [← this]
      exact inf_le_right
  have h3' : 3 < Nat.card F := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨a, ha⟩ := hqodd
    omega
  have key : ∀ {Y' : Subgroup (PGL2 F)} [IsCyclic Y'], Y' ≤ J → Odd (Nat.card Y') →
      ∀ (R : Subgroup (PSL2 F)) [IsCyclic R],
        (Nat.card R = (Nat.card F - 1) / 2 ∨ Nat.card R = (Nat.card F + 1) / 2) →
        (∃ a ∈ Y', a ≠ 1 ∧ a ∈ R.map toPGL) → Y' ≤ R.map toPGL := by
    intro Y' _ hY'J hY'odd R _ hR ⟨a, haY, ha1, haR⟩
    set Y₀ := Y'.comap toPGL
    have hY₀ : Y₀.map toPGL = Y' := Subgroup.map_comap_eq_self hY'J
    have : IsCyclic Y₀ :=
      ((Y₀.equivMapOfInjective toPGL hinj).trans (MulEquiv.subgroupCongr hY₀)).isCyclic.mpr
        inferInstance
    obtain ⟨a', ha'R, rfl⟩ := haR
    have hle := psl2_le_of_isCyclic_of_inf_ne_bot hcard hp2 h3' hR (Y := Y₀) (by
      intro h
      apply ha1
      have : a' ∈ R ⊓ Y₀ := ⟨ha'R, haY⟩
      rw [h, Subgroup.mem_bot] at this
      rw [this, map_one])
    rw [← hY₀]
    exact Subgroup.map_mono hle
  by_cases hvJ : v ∈ J
  ·
    obtain ⟨v', rfl⟩ := hvJ
    have hv'I : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution v' :=
      ⟨fun h => hv1 (by rw [h, map_one]), hinj (by rw [map_pow, map_one]; exact hvI.2)⟩
    obtain ⟨R, s, hRcyc, -, hsI, hsR, hinv, hC, -, hRcard⟩ :=
      CFSG.GorensteinWalter.psl2_reflected_torus_card hF hv'I
    have hRC : R.map toPGL ≤ Subgroup.centralizer ({toPGL v'} : Set (PGL2 F)) := by
      rintro _ ⟨r, hr, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      have hr' : r ∈ Subgroup.centralizer ({v'} : Set (PSL2 F)) := by
        rw [hC]
        exact Subgroup.mem_sup_left hr
      rw [Subgroup.mem_centralizer_singleton_iff.mp hr']
    obtain ⟨a, ⟨haY, haC⟩, ha1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hYv
    obtain ⟨a', rfl⟩ := hYJ haY
    have ha'C : a' ∈ Subgroup.centralizer ({v'} : Set (PSL2 F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp haC
    rw [hC] at ha'C
    have ha'R : a' ∈ R := mem_of_mem_sup_zpowers_of_odd hsR (by rw [← sq]; exact hsI.2) hinv
      ha'C (by
        rw [← orderOf_injective toPGL hinj a']
        exact hY.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y haY))
    have : IsCyclic R := hRcyc
    exact (key hYJ hY R hRcard ⟨_, haY, ha1, ⟨a', ha'R, rfl⟩⟩).trans hRC
  ·
    obtain ⟨U, s, t, w, hUcyc, -, hUcard, hsU, hsJ, hs1, hss, -, -, -, -, -, hwU, hww, hwinv,
      hcent⟩ := CFSG.GorensteinWalter.pgl2_low_two_part_torus_reflection_data F hF h3'
    have hJc : commutator (PGL2 F) = J :=
      CFSG.GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three F hF h3'
    rw [hJc] at hsJ
    have hsI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s := ⟨hs1, by rw [sq]; exact hss⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp (CFSG.GorensteinWalter.pgl2_outer_involutions_conjugate F hF
      h3' hvI hsI (by rwa [hJc]) (by rwa [hJc]))
    set φ := (MulAut.conj c).toMonoidHom
    have hφ : Function.Injective φ := (MulAut.conj c).injective
    set Y' := Y.map φ
    have hY'J : Y' ≤ J := by
      rw [← map_conj_eq_of_normal hJn c]
      exact Subgroup.map_mono hYJ
    have hY'odd : Odd (Nat.card Y') := by
      rwa [Subgroup.card_map_of_injective hφ]
    have : IsCyclic Y' := (Y.equivMapOfInjective φ hφ).isCyclic.mp hYc
    set R := (U ⊓ J).comap toPGL
    have hRmap : R.map toPGL = U ⊓ J := Subgroup.map_comap_eq_self inf_le_right
    have : IsCyclic (U ⊓ J : Subgroup (PGL2 F)) :=
      Subgroup.isCyclic_of_le (H' := U) inf_le_left
    have : IsCyclic R :=
      ((R.equivMapOfInjective toPGL hinj).trans (MulEquiv.subgroupCongr hRmap)).isCyclic.mpr
        inferInstance
    have hrel : J.relIndex U = 2 := by
      have hdvd := Subgroup.relIndex_dvd_index_of_normal J U
      rw [hJindex] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (Subgroup.relIndex_eq_one.mp h hsU) hsJ
      · exact h
    have hUJ := Subgroup.relIndex_mul_card (H := J) (K := U)
    rw [hrel] at hUJ
    have hR2 : 2 * Nat.card R = Nat.card U := by
      have e1 : Nat.card R = Nat.card ↥(U ⊓ J) := by
        rw [← Subgroup.card_map_of_injective hinj, hRmap]
      rw [e1, inf_comm]
      exact hUJ
    have hRcard : Nat.card R = (Nat.card F - 1) / 2 ∨ Nat.card R = (Nat.card F + 1) / 2 := by
      obtain ⟨a, ha⟩ := hqodd
      rcases hUcard with h | h <;> omega
    obtain ⟨a, ⟨haY, haC⟩, ha1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hYv
    have haY' : φ a ∈ Y' := ⟨a, haY, rfl⟩
    have haC' : φ a ∈ Subgroup.centralizer ({s} : Set (PGL2 F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
      change c * a * c⁻¹ * (c * v * c⁻¹) = c * v * c⁻¹ * (c * a * c⁻¹)
      have := Subgroup.mem_centralizer_singleton_iff.mp haC
      calc c * a * c⁻¹ * (c * v * c⁻¹) = c * (a * v) * c⁻¹ := by group
        _ = c * (v * a) * c⁻¹ := by rw [this]
        _ = c * v * c⁻¹ * (c * a * c⁻¹) := by group
    rw [hcent] at haC'
    have haU : φ a ∈ U := mem_of_mem_sup_zpowers_of_odd hwU hww hwinv haC' (by
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      exact hY.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y haY))
    have hle := key hY'J hY'odd R hRcard
      ⟨φ a, haY', fun h => ha1 (hφ (h.trans (map_one φ).symm)), hRmap ▸ ⟨haU, hY'J haY'⟩⟩
    rw [hRmap] at hle
    intro y hy
    have hyU : φ y ∈ U := (hle ⟨y, hy, rfl⟩).1
    have hyC : φ y ∈ Subgroup.centralizer ({s} : Set (PGL2 F)) := by
      rw [hcent]
      exact Subgroup.mem_sup_left hyU
    have hys : φ y * s = s * φ y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hφ
    rw [map_mul, map_mul]
    change c * y * c⁻¹ * (c * v * c⁻¹) = c * v * c⁻¹ * (c * y * c⁻¹)
    rw [hc]
    exact hys

theorem pgl2_exists_le_centralizer_of_odd
    (hF : IsOddPrimePower (Nat.card F))
    {Y : Subgroup (PGL2 F)}
    (hYJ : Y ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    (hY : Odd (Nat.card Y)) {T : Subgroup (PGL2 F)} (hT : IsKleinFour T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set (PGL2 F))) :
    ∃ x ∈ T, x ≠ 1 ∧ Y ≤ Subgroup.centralizer ({x} : Set (PGL2 F)) := by
  classical
  have : IsCyclic Y := pgl2_isCyclic_of_odd_of_kleinFour_le_normalizer hF hYJ hY hT hTY
  have hpow : ∀ v : T, v ^ 2 = 1 := fun v => by
    have h := Monoid.pow_exponent_eq_one v
    rwa [hT.exponent_two] at h
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two T Y hpow hT.card_four
    (fun h => (Nat.not_even_iff_odd.mpr hY) (even_iff_two_dvd.mpr h)) hTY
  by_cases hne : ∃ v : T, v ≠ 1 ∧ Y ⊓ Subgroup.centralizer ({(v : PGL2 F)} : Set (PGL2 F)) ≠ ⊥
  · obtain ⟨v, hv1, hvY⟩ := hne
    have hv2 : orderOf (v : PGL2 F) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (hpow v) hv1
    exact ⟨v, v.2, fun h => hv1 (Subtype.ext h),
      pgl2_le_centralizer_of_inf_ne_bot hF hYJ hY hv2 hvY⟩
  · push Not at hne
    have hbot : Y = ⊥ := by
      rw [hgen]
      exact iSup₂_eq_bot.mpr hne
    have hT1 : 1 < Nat.card T := by rw [hT.card_four]; norm_num
    have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp hT1
    obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : T)
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h), by rw [hbot]; exact bot_le⟩

end Tori

namespace IsLinearDecomposition

variable {H : Type} [Group H] [Finite H] {F : Type} [Field F] [Finite F] {ι : H →* PGammaL2 F}
  {L E : Subgroup H} {S : Sylow 2 H}

theorem mem_linearCore_of_map_eq_pGLStar (hd : IsLinearDecomposition ι L E S)
    (hL : L.map ι = pGammaL2PGLStar F) {x : H} (hx : orderOf x = 2) : x ∈ linearCore ι := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hxL : x ∈ L := hd.sylow_le P (hP (Subgroup.mem_zpowers x))
  exact mem_pGammaL2PSLRange_of_mem_pGLStar hd.isOddPrimePower_card (hL ▸ ⟨x, hxL, rfl⟩)
    (by rw [orderOf_injective ι hd.injective, hx])

theorem inf_centralizer_kleinFour
    (hd : IsLinearDecomposition ι L E S) {T : Subgroup H}
    (hT : IsKleinFour T) : L ⊓ Subgroup.centralizer (T : Set H) = T := by
  obtain ⟨P, hTP⟩ := (isPGroup_two_of_isKleinFour hT).exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq H S P
  exact ((hd.conj g).centralizer_kleinFour hT hTP).2

theorem odd_card_of_kleinFour_le_normalizer
    (hd : IsLinearDecomposition ι L E S)
    {T : Subgroup H} (hT : IsKleinFour T) {Y : Subgroup H}
    (hY : T ≤ Subgroup.normalizer (Y : Set H)) (hYT : Y ⊓ T = ⊥) : Odd (Nat.card Y) := by
  classical
  have hCLT := hd.inf_centralizer_kleinFour hT
  by_contra heven
  rw [Nat.not_odd_iff_even] at heven
  set K := Y ⊔ T with hKdef
  have hKN : K ≤ Subgroup.normalizer (Y : Set H) := sup_le Subgroup.le_normalizer hY
  have hKcard : Nat.card K = Nat.card Y * Nat.card T :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Y T hY
      (disjoint_iff.mpr hYT)
  have hTK : T ≤ K := le_sup_right
  have hT2 : IsPGroup 2 (T.subgroupOf K) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv, hT.card_four]
    norm_num)
  obtain ⟨Q, hTQ⟩ := hT2.exists_le_sylow
  set P := (Q : Subgroup K).map K.subtype with hPdef
  have hPK : P ≤ K := Subgroup.map_subtype_le _
  have hTP : T ≤ P := fun t ht =>
    ⟨⟨t, hTK ht⟩, hTQ (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hP2 : IsPGroup 2 P := Q.isPGroup'.map _
  have h8 : 8 ∣ Nat.card P := by
    rw [hPdef, Subgroup.card_map_of_injective K.subtype_injective]
    apply Q.pow_dvd_card_of_pow_dvd_card (n := 3)
    rw [hKcard, hT.card_four]
    obtain ⟨k, hk⟩ := heven
    exact ⟨k, by rw [hk]; ring⟩
  have hYP : Y ⊓ P = ⊥ := by
    by_contra hne
    have hPL : P ≤ L := by
      obtain ⟨P', hP'⟩ := hP2.exists_le_sylow
      exact hP'.trans (hd.sylow_le P')
    have hN : ((Y ⊓ P).subgroupOf P).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨?_, P.mul_mem (P.mul_mem g.2 hn.2) (P.inv_mem g.2)⟩
      exact (Subgroup.mem_normalizer_iff.mp (hKN (hPK g.2)) _).mp hn.1
    have : Group.IsNilpotent P := hP2.isNilpotent
    have hne' : (Y ⊓ P).subgroupOf P ≠ ⊥ := by
      intro h
      apply hne
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact eq_bot_iff.mpr fun x hx => (disjoint_iff.mp h).le ⟨hx, hx.2⟩
    obtain ⟨⟨z, hzP⟩, ⟨hzYP', hzZ'⟩, hz1⟩ :=
      (Subgroup.bot_or_exists_ne_one _).resolve_left
        (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
    have hzYP : z ∈ Y ⊓ P := hzYP'
    have hzZ : (⟨z, hzP⟩ : P) ∈ Subgroup.center P := hzZ'
    have hzC : z ∈ Subgroup.centralizer (T : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have := Subgroup.mem_center_iff.mp hzZ ⟨t, hTP ht⟩
      exact congrArg Subtype.val this
    have hzT : z ∈ T := hCLT ▸ ⟨hPL hzP, hzC⟩
    have : z ∈ Y ⊓ T := ⟨hzYP.1, hzT⟩
    rw [hYT, Subgroup.mem_bot] at this
    exact hz1 (Subtype.ext this)
  have hYPcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Y P
    (hPK.trans hKN) (disjoint_iff.mpr hYP)
  have hle : Nat.card ↥(Y ⊔ P) ≤ Nat.card K :=
    Subgroup.card_le_of_le (sup_le le_sup_left hPK)
  rw [hYPcard, hKcard, hT.card_four] at hle
  have hYpos : 0 < Nat.card Y := Nat.card_pos
  have hP4 : Nat.card P ≤ 4 := Nat.le_of_mul_le_mul_left hle hYpos
  have := Nat.le_of_dvd (Nat.card_pos) h8
  omega

theorem exists_le_centralizer_of_kleinFour
    (hd : IsLinearDecomposition ι L E S)
    {T : Subgroup H} (hT : IsKleinFour T) {Y : Subgroup H}
    (hY : T ≤ Subgroup.normalizer (Y : Set H)) (hYT : Y ⊓ T = ⊥) :
    ∃ x ∈ T, x ≠ 1 ∧ Y ≤ Subgroup.centralizer ({x} : Set H) := by
  classical
  have hF := hd.isOddPrimePower_card
  have hYodd := hd.odd_card_of_kleinFour_le_normalizer hT hY hYT
  have hTsq : ∀ t ∈ T, t ^ 2 = 1 := fun t ht => by
    have h := Monoid.pow_exponent_eq_one (⟨t, ht⟩ : T)
    rw [hT.exponent_two] at h
    simpa using congrArg Subtype.val h
  have hTL : T ≤ L := by
    obtain ⟨P, hTP⟩ := (isPGroup_two_of_isKleinFour hT).exists_le_sylow
    exact hTP.trans (hd.sylow_le P)
  have hTP : T.map ι ≤ pGammaL2PGLRange F := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases ht1 : t = 1
    · rw [ht1, map_one]
      exact Subgroup.one_mem _
    exact hd.isStandardLayer.mem_pGLRange_of_orderOf_eq_two hF ⟨t, hTL ht, rfl⟩
      (by rw [orderOf_injective ι hd.injective, orderOf_eq_prime (hTsq t ht) ht1])
  set L₀ := linearCore ι
  have hL₀ : L₀.Normal := hd.linearCore_normal
  set Y₀ := Y ⊓ L₀ with hY₀def
  have hY₀odd : Odd (Nat.card Y₀) := hYodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hTY₀ : T ≤ Subgroup.normalizer (Y₀ : Set H) := fun t ht => by
    apply Subgroup.mem_normalizer_fintype
    rintro y ⟨hyY, hyL⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hY ht) y).mp hyY, hL₀.conj_mem y hyL t⟩
  have hinl : Function.Injective (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) :=
    SemidirectProduct.inl_injective
  set Y₁ := (Y₀.map ι).comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  set T₁ := (T.map ι).comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  have hY₀P : Y₀.map ι ≤ pGammaL2PSLRange F := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy.2
  have hY₁J : Y₁ ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    intro x hx
    obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff F _).mp (hY₀P hx)
    exact ⟨y, hinl hy⟩
  let eY : Y₁ ≃* Y₀ :=
    ((Y₁.equivMapOfInjective _ hinl).trans (MulEquiv.subgroupCongr
      (Subgroup.map_comap_eq_self (hY₀P.trans pGammaL2PSLRange_le_pGLRange)))).trans
      (Y₀.equivMapOfInjective ι hd.injective).symm
  let eT : T₁ ≃* T :=
    ((T₁.equivMapOfInjective _ hinl).trans (MulEquiv.subgroupCongr
      (Subgroup.map_comap_eq_self hTP))).trans (T.equivMapOfInjective ι hd.injective).symm
  have hY₁ : Odd (Nat.card Y₁) := by rwa [Nat.card_congr eY.toEquiv]
  have hT₁ : IsKleinFour T₁ :=
    ⟨by rw [Nat.card_congr eT.toEquiv]; exact hT.card_four,
      by rw [Monoid.exponent_eq_of_mulEquiv eT]; exact hT.exponent_two⟩
  have hT₁Y₁ : T₁ ≤ Subgroup.normalizer (Y₁ : Set (PGL2 F)) := by
    intro t ht
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    have hN := Subgroup.le_normalizer_map ι
      (Subgroup.map_mono hTY₀ (show SemidirectProduct.inl t ∈ T.map ι from ht))
    change SemidirectProduct.inl (t * y * t⁻¹) ∈ Y₀.map ι
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hN _).mp hy
  obtain ⟨x₁, hx₁T, hx₁1, hY₁C⟩ := pgl2_exists_le_centralizer_of_odd hF hY₁J hY₁ hT₁ hT₁Y₁
  obtain ⟨x, hxT, hxx₁⟩ := hx₁T
  have hx1 : x ≠ 1 := fun h => hx₁1 (hinl (by rw [map_one, ← hxx₁, h, map_one]))
  have hY₀C : Y₀ ≤ Subgroup.centralizer ({x} : Set H) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨y₁, hy₁⟩ := pGammaL2PSLRange_le_pGLRange (hY₀P ⟨y, hy, rfl⟩)
    have hy₁Y : y₁ ∈ Y₁ := by
      change SemidirectProduct.inl y₁ ∈ Y₀.map ι
      rw [hy₁]
      exact ⟨y, hy, rfl⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hY₁C hy₁Y)
    apply hd.injective
    rw [map_mul, map_mul, ← hy₁, hxx₁, ← map_mul, ← map_mul, hc]
  refine ⟨x, hxT, hx1, fun y hy => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxx : x * x = 1 := by rw [← sq]; exact hTsq x hxT
  have hxyx : x * y⁻¹ * x⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp (hY hxT) y⁻¹).mp (Y.inv_mem hy)
  obtain ⟨c, hcdef⟩ : ∃ c, c = y * x * y⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hcY : c ∈ Y := by
    rw [hcdef, show y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) by group]
    exact Y.mul_mem hy hxyx
  have hcL : c ∈ L₀ := by
    have h : ⁅y, x⁆ ∈ commutator H := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x)
    have h' := hd.commutator_le_linearCore h
    rwa [commutatorElement_def, ← hcdef] at h'
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp (hY₀C ⟨hcY, hcL⟩)
  have hyx : y * x * y⁻¹ = c * x := by rw [hcdef]; group
  have hc2 : c * c = 1 := by
    have h1 : (y * x * y⁻¹) * (y * x * y⁻¹) = 1 := by
      calc (y * x * y⁻¹) * (y * x * y⁻¹) = y * (x * x) * y⁻¹ := by group
        _ = 1 := by rw [hxx, mul_one, mul_inv_cancel]
    rw [hyx] at h1
    calc c * c = c * c * (x * x) := by rw [hxx, mul_one]
      _ = c * (x * c) * x := by rw [← hcx]; group
      _ = c * x * (c * x) := by group
      _ = 1 := h1
  have hc1 : c = 1 := by
    have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hc2)
    have hodd : Odd (orderOf c) := hY₀odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y₀ ⟨hcY, hcL⟩)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [hc1, one_mul] at hyx
  calc y * x = y * x * y⁻¹ * y := by group
    _ = x * y := by rw [hyx]

theorem le_centralizer_of_normalizer_kleinFour
    (hd : IsLinearDecomposition ι L E S)
    {T : Subgroup H} (hT : IsKleinFour T) (P : Sylow 2 H) (hTP : T ≤ P)
    {D : Subgroup H} (hDdef : D = (P : Subgroup H) ⊓ Subgroup.normalizer (T : Set H))
    (hDT : D ≠ T) {x₁ : H} (hx₁T : x₁ ∈ T) (hx₁ : x₁ ≠ 1)
    (hx₁D : x₁ ∈ Subgroup.centralizer (D : Set H)) {Y : Subgroup H}
    (hY : D ≤ Subgroup.normalizer (Y : Set H)) (hYD : Y ⊓ D = ⊥) :
    Y ≤ Subgroup.centralizer ({x₁} : Set H) := by
  classical
  have hTD : T ≤ D := by
    rw [hDdef]
    exact le_inf hTP Subgroup.le_normalizer
  have hYT : Y ⊓ T = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left Y hTD).trans hYD.le)
  obtain ⟨x, hxT, hx1, hYx⟩ :=
    hd.exists_le_centralizer_of_kleinFour hT (hTD.trans hY) hYT
  by_cases hxx₁ : x = x₁
  · rwa [← hxx₁]
  obtain ⟨d, hdD, hdT⟩ : ∃ d ∈ D, d ∉ T := by
    by_contra h
    push Not at h
    exact hDT (le_antisymm h hTD)
  have hdP : d ∈ (P : Subgroup H) := by rw [hDdef] at hdD; exact hdD.1
  have hdN : d ∈ Subgroup.normalizer (T : Set H) := by rw [hDdef] at hdD; exact hdD.2
  have hdx₁ : d * x₁ = x₁ * d := Subgroup.mem_centralizer_iff.mp hx₁D d hdD
  obtain ⟨x', hx'def⟩ : ∃ x', x' = d * x * d⁻¹ := ⟨_, rfl⟩
  have hx'T : x' ∈ T := hx'def ▸ (Subgroup.mem_normalizer_iff.mp hdN x).mp hxT
  have hx'1 : x' ≠ 1 := fun h => hx1 (by
    rw [show x = d⁻¹ * x' * d by rw [hx'def]; group, h]
    group)
  have hx'x : x' ≠ x := by
    intro h
    apply hdT
    have hdx : d * x = x * d := by
      rw [hx'def] at h
      calc d * x = d * x * d⁻¹ * d := by group
        _ = x * d := by rw [h]
    have hTgen : ∀ t ∈ T, t * d = d * t := by
      intro t ht
      by_cases ht1 : t = 1
      · rw [ht1, one_mul, mul_one]
      by_cases htx : t = x
      · rw [htx, hdx]
      by_cases htx₁ : t = x₁
      · rw [htx₁, hdx₁]
      have hT' : IsKleinFour T := hT
      have := hT'.eq_mul_of_ne_all (x := (⟨x, hxT⟩ : T)) (y := ⟨x₁, hx₁T⟩) (z := ⟨t, ht⟩)
        (fun h => hx1 (congrArg Subtype.val h)) (fun h => hx₁ (congrArg Subtype.val h))
        (fun h => hxx₁ (congrArg Subtype.val h)) (fun h => ht1 (congrArg Subtype.val h))
        (fun h => htx (congrArg Subtype.val h)) (fun h => htx₁ (congrArg Subtype.val h))
      have ht' : t = x * x₁ := congrArg Subtype.val this
      rw [ht']
      calc x * x₁ * d = x * (x₁ * d) := by group
        _ = x * (d * x₁) := by rw [hdx₁]
        _ = (x * d) * x₁ := by group
        _ = d * x * x₁ := by rw [hdx]
        _ = d * (x * x₁) := by group
    have hdC : d ∈ Subgroup.centralizer (T : Set H) := Subgroup.mem_centralizer_iff.mpr hTgen
    have hdL : d ∈ L := hd.sylow_le P hdP
    exact (hd.inf_centralizer_kleinFour hT) ▸ ⟨hdL, hdC⟩
  have hx'x₁ : x' ≠ x₁ := by
    intro h
    apply hxx₁
    rw [hx'def] at h
    have h' : d * x * d⁻¹ = d * x₁ * d⁻¹ := by rw [h, hdx₁]; group
    simpa using h'
  have hT' : IsKleinFour T := hT
  have hx'eq : x' = x * x₁ := congrArg Subtype.val
    (hT'.eq_mul_of_ne_all (x := (⟨x, hxT⟩ : T)) (y := ⟨x₁, hx₁T⟩) (z := ⟨x', hx'T⟩)
      (fun h => hx1 (congrArg Subtype.val h)) (fun h => hx₁ (congrArg Subtype.val h))
      (fun h => hxx₁ (congrArg Subtype.val h)) (fun h => hx'1 (congrArg Subtype.val h))
      (fun h => hx'x (congrArg Subtype.val h)) (fun h => hx'x₁ (congrArg Subtype.val h)))
  have hYx' : Y ≤ Subgroup.centralizer ({x'} : Set H) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy' : d⁻¹ * y * d ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hY hdD)) y).mp hy
      simpa using this
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hYx hy')
    rw [hx'def]
    calc y * (d * x * d⁻¹) = d * (d⁻¹ * y * d * x) * d⁻¹ := by group
      _ = d * (x * (d⁻¹ * y * d)) * d⁻¹ := by rw [hc]
      _ = d * x * d⁻¹ * y := by group
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hYx hy)
  have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hYx' hy)
  rw [hx'eq] at h2
  have hxx : x * x = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨x, hxT⟩ : T)
    rw [hT.exponent_two] at h
    simpa [sq] using congrArg Subtype.val h
  calc y * x₁ = y * (x * (x * x₁)) := by rw [← mul_assoc x x x₁, hxx, one_mul]
    _ = y * x * (x * x₁) := by group
    _ = x * (y * (x * x₁)) := by rw [h1]; group
    _ = x * (x * x₁ * y) := by rw [h2]
    _ = x₁ * y := by rw [← mul_assoc, ← mul_assoc, hxx, one_mul]

end IsLinearDecomposition



end CFSG.ABGDGroups

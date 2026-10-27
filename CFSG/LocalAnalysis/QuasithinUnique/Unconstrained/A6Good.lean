module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Endgame
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Datum

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

section CharTwoFacts

variable {G : Type*} [Group G] [Finite G]

theorem not_charTwo_of_card_ten {X : Subgroup G} (hX : Nat.card X = 10) : ¬ CharTwo X := by
  intro hc
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 5 (by rw [hX]; norm_num)
  set R := pCoreOf 2 X with hR
  have hR2 : IsPGroup 2 ↥R := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X
  have hRX : R ≤ X := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X
  have hXR : X ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  have hRdvd : Nat.card R ∣ 10 := hX ▸ Subgroup.card_dvd_of_le hRX
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hRcard : Nat.card R = 1 ∨ Nat.card R = 2 := by
    rw [hk] at hRdvd ⊢
    have hk1 : k ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hlt
      have := this.trans hRdvd
      norm_num at this
    interval_cases k
    · left; rfl
    · right; rfl
  have hxX : (x : G) ∈ X := x.2
  have hxc : (x : G) ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrx : (x : G) * r * (x : G)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hXR hxX) r).mp hr
    suffices h : (x : G) * r * (x : G)⁻¹ = r by
      calc r * (x : G) = ((x : G) * r * (x : G)⁻¹) * (x : G) := by rw [h]
        _ = (x : G) * r := by group
    have hr' : r ∈ R := hr
    rcases hRcard with h1 | h2
    · have hbot : R = ⊥ := Subgroup.eq_bot_of_card_eq R h1
      rw [hbot, Subgroup.mem_bot] at hr'
      rw [hr']; group
    · by_cases hr1 : r = 1
      · rw [hr1]; group
      ·
        have hzR : Subgroup.zpowers r ≤ R := Subgroup.zpowers_le.mpr hr'
        have hord : 2 ≤ orderOf r := by
          rcases Nat.lt_or_ge (orderOf r) 2 with hlt | hge
          · have : orderOf r = 1 := by
              have := orderOf_pos r
              omega
            exact absurd (orderOf_eq_one_iff.mp this) hr1
          · exact hge
        have hzcard : Nat.card (Subgroup.zpowers r) = orderOf r := Nat.card_zpowers r
        have hzeq : Subgroup.zpowers r = R :=
          Subgroup.eq_of_le_of_card_ge hzR (by rw [h2, hzcard]; exact hord)
        have hord2 : orderOf r = 2 := by
          have := Subgroup.card_le_of_le hzR
          rw [hzcard, h2] at this
          omega
        have hrr : r * r = 1 := by
          have := pow_orderOf_eq_one r
          rwa [hord2, sq] at this
        rw [← hzeq] at hrx
        rcases mem_zpowers_involution hrr hrx with h | h
        · exfalso
          apply hr1
          calc r = (x : G)⁻¹ * ((x : G) * r * (x : G)⁻¹) * (x : G) := by group
            _ = 1 := by rw [h]; group
        · exact h
  have hxR : (x : G) ∈ R := hc ⟨hxX, hxc⟩
  obtain ⟨n, hn⟩ := hR2 ⟨(x : G), hxR⟩
  have hxn : (x : G) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hdvd : orderOf (x : G) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hxn
  rw [Subgroup.orderOf_coe, hx] at hdvd
  have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd
  omega

omit [Finite G] in
theorem not_charTwo_of_isSimple {X : Subgroup G} (hs : IsSimpleGroup ↥X) (h1 : X ≠ ⊥)
    (h2 : ¬ IsPGroup 2 ↥X) : ¬ CharTwo X := by
  intro hc
  set R := pCoreOf 2 X with hR
  have hR2 : IsPGroup 2 ↥R := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X
  have hRX : R ≤ X := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X
  have hXR : X ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  have hnorm : (R.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRX).mpr hXR
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf X) with h | h
  · have hRbot : R = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      have : (⟨r, hRX hr⟩ : ↥X) ∈ R.subgroupOf X := hr
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    apply h1
    rw [eq_bot_iff]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hr' : r ∈ R := hr
      rw [hRbot, Subgroup.mem_bot] at hr'
      rw [hr']; simp
    have hxR : x ∈ R := hc ⟨hx, hxc⟩
    rwa [hRbot] at hxR
  · apply h2
    have hXle : X ≤ R := by
      intro x hx
      have : (⟨x, hx⟩ : ↥X) ∈ R.subgroupOf X := by rw [h]; trivial
      exact this
    exact hR2.to_le hXle

end CharTwoFacts

section Conj

variable {G : Type*} [Group G]

theorem centralizer_conj_singleton (z g : G) :
    Subgroup.centralizer ({g⁻¹ * z * g} : Set G) =
      (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨g * x * g⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by rw [hx]
        _ = z * (g * x * g⁻¹) := by group
    · show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    have hy' : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    show g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * z * g) = g⁻¹ * z * g * (g⁻¹ * y * g⁻¹⁻¹)
    calc g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * z * g) = g⁻¹ * (y * z) * g := by group
      _ = g⁻¹ * (z * y) * g := by rw [hy']
      _ = g⁻¹ * z * g * (g⁻¹ * y * g⁻¹⁻¹) := by group

theorem centralizer_zpowers_eq (a : G) :
    Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

end Conj

section Good

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs}

theorem A6Datum.good_of_conj {t zK : G} (D : A6Datum N) (h : Lv2521 N t zK) {g : G}
    (hg : g⁻¹ * N.z * g ∈ N.S) :
    D.Φ (g⁻¹ * N.z * g) ≠ 1 ∧
      (D.Φ (g⁻¹ * N.z * g) ∈ A6Models.psl29 ∨ D.Φ (g⁻¹ * N.z * g) ∈ s6) := by
  set u : G := g⁻¹ * N.z * g with hu
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← hK0]; exact N.H_le_normalizer_K0
  have hf := h.facts2511
  have h258 := h.facts258
  have hz2 : N.z * N.z = 1 := by have := N.tuple.z_sq; rwa [sq] at this
  have hz1 : N.z ≠ 1 := N.tuple.z_ne_one
  have hu2 : u * u = 1 := by
    rw [hu]
    calc g⁻¹ * N.z * g * (g⁻¹ * N.z * g) = g⁻¹ * (N.z * N.z) * g := by group
      _ = 1 := by rw [hz2]; group
  have huH : u ∈ N.H := N.S_le_H hg
  have htS : t ∈ N.S := hf.t_mem_center.1
  have htu : u * t = t * u := Subgroup.mem_centralizer_iff.mp hf.t_mem_center.2 u hg
  have hzT : N.z ∈ centerOf T := N.tuple.z_mem
  have hTz : T ≤ Subgroup.centralizer ({N.z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzT.2 w hw)
  have hzpow2 : IsPGroup 2 ↥(Subgroup.zpowers N.z) :=
    hs.setting.isPGroup.to_le (Subgroup.zpowers_le.mpr (N.tuple.center_le hzT |> fun hzS => N.S_le_T hzS))
  have hloc : IsTwoLocal (Subgroup.centralizer ({N.z} : Set G)) :=
    ⟨Subgroup.zpowers N.z, fun h1 => hz1 (Subgroup.zpowers_eq_bot.mp h1), hzpow2,
      (normalizer_zpowers_eq_centralizer hz2).symm⟩
  have hCzM : Subgroup.centralizer ({N.z} : Set G) ≤ M :=
    hs.setting.le_of_isTwoLocal_of_isSylowTwoOf_M hs.setting.isSylowTwoOf_M hloc hTz
  have hzM : Subgroup.zpowers N.z ≤ M :=
    (Subgroup.zpowers_le.mpr (N.tuple.center_le hzT |> fun hzS => hs.setting.le (N.S_le_T hzS)))
  have hCharz : CharTwo (Subgroup.centralizer ({N.z} : Set G)) := by
    have := hs.setting.charTwo.inf_centralizer hzM hzpow2
    rwa [centralizer_zpowers_eq, inf_eq_right.mpr hCzM] at this
  have hCharu : CharTwo (Subgroup.centralizer ({u} : Set G)) := by
    rw [hu, centralizer_conj_singleton]
    exact (charTwo_map_equiv_iff (MulAut.conj g⁻¹) _).mpr hCharz
  have htpow2 : IsPGroup 2 ↥(Subgroup.zpowers t) :=
    N.tuple.sylow.isPGroup.to_le (Subgroup.zpowers_le.mpr htS)
  have htC : Subgroup.zpowers t ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr htu.symm
  have hChartu : CharTwo (Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) := by
    have := hCharu.inf_centralizer htC htpow2
    rwa [centralizer_zpowers_eq] at this
  have hGt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [h.concl2518.2.1]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [hK0]; exact Subgroup.le_normalizer
    · exact N.S_le_normalizer_K hKH
    · rw [← hK0]
      exact inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hKt : N.K ≤ Subgroup.centralizer ({t} : Set G) := by
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hf.t_mem) k (hK0 ▸ hk))
  set Y : Subgroup G :=
    Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) with hY
  have hKuY : N.K ⊓ Subgroup.centralizer ({u} : Set G) ≤ Y :=
    fun k hk => ⟨hk.2, hKt hk.1⟩
  have hYnorm : Y ≤ Subgroup.normalizer ((N.K ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) :
      Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
      (inf_le_right.trans hGt) (inf_le_left.trans Subgroup.le_normalizer)
  have hCharKu : CharTwo (N.K ⊓ Subgroup.centralizer ({u} : Set G)) :=
    CharTwo.of_normal hChartu hKuY
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKuY).mpr hYnorm)
  have hα2 : D.Φ u * D.Φ u = 1 := by rw [← D.mul u huH u huH, hu2, D.Φ_one]
  have hαP : D.Φ u ∈ A6Models.autA6 := D.mem u huH
  have hKsimple : IsSimpleGroup ↥N.K := h258.simple
  have hKcard : Nat.card N.K = 360 := by
    obtain ⟨eK⟩ := h.concl2521.nonempty_K
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  by_cases hα1 : D.Φ u = 1
  ·
    exfalso
    have hcentK := (D.ker u huH).mp hα1
    have hKu : N.K ⊓ Subgroup.centralizer ({u} : Set G) = N.K := by
      apply inf_eq_left.mpr
      intro k hk
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcentK k hk).symm
    rw [hKu] at hCharKu
    refine not_charTwo_of_isSimple hKsimple ?_ ?_ hCharKu
    · intro hbot
      have : Nat.card N.K = 1 := by rw [hbot]; simp
      omega
    · intro hp
      obtain ⟨n, hn⟩ := hp.exists_card_eq
      rw [hKcard] at hn
      have h3 : (3 : ℕ) ∣ 2 ^ n := by rw [← hn]; norm_num
      have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3
      omega
  · refine ⟨hα1, ?_⟩
    by_contra hcon
    push Not at hcon
    have hc10 := card_psl29_centralizer_of_not_mem hαP hα2 hα1 hcon.1 hcon.2
    rw [← D.card_K_centralizer hKH hKsimple huH] at hc10
    exact not_charTwo_of_card_ten hc10 hCharKu

end Good

end CFSG.QuasithinUnique

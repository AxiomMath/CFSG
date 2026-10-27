module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Gl
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21AutFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinStep7

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def OutAutAll : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsL2pType X → OutAutFacts X

section Generic

variable {G : Type} [Group G] [Finite G]

theorem mem_of_odd_orderOf_of_mem_sup {K S : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) {e : G} (he : e ∈ K ⊔ S)
    (hodd : Odd (orderOf e)) : e ∈ K := by
  obtain ⟨k, hk, s, hs, rfl⟩ := mem_sup_of_le_normalizer hSK he
  obtain ⟨j, hj⟩ := hS ⟨s, hs⟩
  have hs1 : s ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  obtain ⟨k', hk', hpow⟩ := pow_mul_mem_mul_pow hSK hk hs (2 ^ j)
  rw [hs1, mul_one] at hpow
  set r := orderOf (k * s) with hr
  by_cases hr1 : r = 1
  · have : k * s = 1 := orderOf_eq_one_iff.mp hr1
    rw [this]
    exact K.one_mem
  · have hr1' : 1 < r := by
      have : r ≠ 0 := (orderOf_pos _).ne'
      omega
    have hcop : Nat.Coprime (2 ^ j) r :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr1'
    have h1 : (k * s) ^ (2 ^ j * m) = k * s := by
      rw [← pow_mod_orderOf, hm, pow_one]
    rw [← h1, pow_mul, hpow]
    exact K.pow_mem hk' m

end Generic

section Gt

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G} {R : Subgroup ↥(autOn N.S N.K)}

theorem Lv2520.centralizer_t_le_normalizer_Kx (h : Lv2520 N t zK) (hp : CaseCParams N t zK R)
    (hne : CFSG.conjugate N.K N.x ≠ N.K)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) :
    Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G) := by
  intro g hg
  have hgM : g ∈ N.Mplus := h.centralizer_t_le_Mplus hcomm hp hg
  have h1 : CFSG.conjugate N.K g = N.K :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (h.centralizer_t_le_normalizer hg)
  rcases h.conj_Kx_eq hcomm hgM with h2 | h2
  · exfalso
    apply hne
    have h3 : CFSG.conjugate (CFSG.conjugate N.K N.x) g = CFSG.conjugate N.K g := by
      rw [h2, h1]
    exact BenderBranch.conjugate_inj.mp h3
  · exact BenderBranch.conjugate_eq_iff_mem_normalizer.mp h2

@[expose] def Notation25.Yc (N : Notation25 hs) : Subgroup G :=
  Subgroup.centralizer (N.Kplus : Set G)

theorem Notation25.mem_Yc {N : Notation25 hs} {y : G} :
    y ∈ N.Yc ↔ ∀ w ∈ N.Kplus, w * y = y * w :=
  Subgroup.mem_centralizer_iff

theorem Lv2520.Yc_le_centralizer_t (h : Lv2520 N t zK) (hp : CaseCParams N t zK R) :
    N.Yc ≤ Subgroup.centralizer ({t} : Set G) := by
  intro y hy
  have htK : t ∈ N.Kplus :=
    (le_sup_right : CFSG.conjugate N.K N.x ≤ N.Kplus) (h.t_mem_Kx hp)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Notation25.mem_Yc.mp hy t htK).symm

theorem Notation25.Yc_normalized {N : Notation25 hs} {g : G} (hg : g ∈ N.Mplus) {y : G}
    (hy : y ∈ N.Yc) : g * y * g⁻¹ ∈ N.Yc := by
  rw [Notation25.mem_Yc]
  intro w hw
  have hw' : g⁻¹ * w * g ∈ N.Kplus := by
    have := (Subgroup.mem_normalizer_iff.mp (N.Mplus.inv_mem hg) w).mp hw
    simpa using this
  have h1 := Notation25.mem_Yc.mp hy _ hw'
  calc w * (g * y * g⁻¹) = g * ((g⁻¹ * w * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
    _ = (g * y * g⁻¹) * w := by group

theorem Lv2520.Yc_inf_S (h : Lv2520 N t zK) : N.Yc ⊓ N.S = ⊥ := by
  rw [eq_bot_iff]
  rintro s ⟨hsY, hsS⟩
  rw [Subgroup.mem_bot]
  have hc1 : s ∈ Subgroup.centralizer (N.K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Notation25.mem_Yc.mp hsY k (Subgroup.mem_sup_left hk)
  have hc2 : N.x * s * N.x⁻¹ ∈ Subgroup.centralizer (N.K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : N.x⁻¹ * k * N.x ∈ CFSG.conjugate N.K N.x := by
      rw [BenderBranch.mem_conjugate_iff]
      have : N.x * (N.x⁻¹ * k * N.x) * N.x⁻¹ = k := by group
      rw [this]; exact hk
    have h1 := Notation25.mem_Yc.mp hsY _ (Subgroup.mem_sup_right hk')
    calc k * (N.x * s * N.x⁻¹) = N.x * ((N.x⁻¹ * k * N.x) * s) * N.x⁻¹ := by group
      _ = N.x * (s * (N.x⁻¹ * k * N.x)) * N.x⁻¹ := by rw [h1]
      _ = (N.x * s * N.x⁻¹) * k := by group
  have hsC : s ∈ N.SC := by
    refine ⟨hsS, ?_⟩
    rw [h.hK0]
    exact hc1
  have hsCx : s ∈ N.SCx := by
    rw [Notation25.mem_SCx]
    refine ⟨(Subgroup.mem_normalizer_iff.mp N.x_mem.2 s).mp hsS, ?_⟩
    rw [h.hK0]
    exact hc2
  have : s ∈ N.SC ⊓ CFSG.conjugate N.SC N.x := ⟨hsC, hsCx⟩
  rw [h.concl255.1, Subgroup.mem_bot] at this
  exact this

theorem Lv2520.Yc_eq_bot (h : Lv2520 N t zK) (hp : CaseCParams N t zK R)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) : N.Yc = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGtM : Subgroup.centralizer ({t} : Set G) ≤ N.Mplus := h.centralizer_t_le_Mplus hcomm hp
  have hYle := h.Yc_le_centralizer_t hp
  have hnormY : ∀ g ∈ Subgroup.centralizer ({t} : Set G), ∀ y ∈ N.Yc, g * y * g⁻¹ ∈ N.Yc :=
    fun g hg y hy => Notation25.Yc_normalized (hGtM hg) hy
  have hYnorm : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.Yc : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hnormY g hg y hy, fun hy => ?_⟩
    have := hnormY g⁻¹ ((Subgroup.centralizer ({t} : Set G)).inv_mem hg) _ hy
    simpa [mul_assoc] using this
  have hodd : Odd (Nat.card ↥N.Yc) := by
    by_contra hev
    have h2 : 2 ∣ Nat.card ↥N.Yc := by
      rcases Nat.even_or_odd (Nat.card ↥N.Yc) with he | ho
      · exact even_iff_two_dvd.mp he
      · exact absurd ho hev
    obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' (G := ↥N.Yc) 2 h2
    set jj : G := (j : G) with hjj
    have hjY : jj ∈ N.Yc := j.2
    have hj2 : jj * jj = 1 := by
      have h1 : j ^ 2 = 1 := by rw [← hj]; exact pow_orderOf_eq_one j
      have := congrArg Subtype.val h1
      simpa [pow_two] using this
    have hj1 : jj ≠ 1 := by
      intro h1
      have : j = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hj
      omega
    have hzp : IsPGroup 2 ↥(Subgroup.zpowers jj) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hj2) hj1]
      norm_num
    obtain ⟨m, hm, hmS⟩ := EscapingLocal.exists_conj_mem_of_isPGroup
      (M := Subgroup.centralizer ({t} : Set G)) (T := N.S) (S := Subgroup.zpowers jj)
      h.facts2511.sylow.1 h.facts2511.sylow.2.1 h.facts2511.sylow.2.2
      ((Subgroup.zpowers_le).mpr (hYle hjY)) hzp
    have h1 : m * jj * m⁻¹ ∈ N.S := hmS jj (Subgroup.mem_zpowers jj)
    have h2 : m * jj * m⁻¹ ∈ N.Yc := hnormY m hm jj hjY
    have h3 : m * jj * m⁻¹ ∈ N.Yc ⊓ N.S := ⟨h2, h1⟩
    rw [h.Yc_inf_S, Subgroup.mem_bot] at h3
    apply hj1
    calc jj = m⁻¹ * (m * jj * m⁻¹) * m := by group
      _ = 1 := by rw [h3]; group
  have hle : N.Yc ≤ oddCoreIn (Subgroup.centralizer ({t} : Set G)) :=
    Out21.le_oddCoreIn' hYle hYnorm hodd
  rw [h.concl2518.2.2.2.2] at hle
  exact le_bot_iff.mp hle

theorem Lv2520.D_isPGroup
    (hAF : OutAutAll) (h : Lv2520 N t zK) (hp : CaseCParams N t zK R)
    (hL2p : IsL2pType ↥N.K) (hne : CFSG.conjugate N.K N.x ≠ N.K)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) :
    IsPGroup 2 ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G)) := by
  classical
  have hY := h.Yc_eq_bot hp hcomm
  have hKxType : IsL2pType ↥(CFSG.conjugate N.K N.x) := isL2pType_conjugate N.x hL2p
  have hX : OutAutFacts ↥(CFSG.conjugate N.K N.x) := hAF _ hKxType
  have hdat := l2pFacts ↥(CFSG.conjugate N.K N.x) hKxType
  have htKx : t ∈ CFSG.conjugate N.K N.x := h.t_mem_Kx hp
  have htt2 : orderOf (⟨t, htKx⟩ : ↥(CFSG.conjugate N.K N.x)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      show t ^ 2 = 1
      exact h.facts2511.t_sq
    · intro h1
      apply h.facts2511.t_ne_one
      exact congrArg Subtype.val h1
  have hcent := hdat.cent_two ⟨t, htKx⟩ htt2
  have hDN : (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G)) ≤
      Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G) :=
    fun d hd => h.centralizer_t_le_normalizer_Kx hp hne hcomm hd.1
  have hinj : ∀ d : ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G)),
      Setup.rho (CFSG.conjugate N.K N.x)
        (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G)) hDN d = 1 →
      d = 1 := by
    intro d hd1
    have hc : (d : G) ∈ Subgroup.centralizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G) :=
      (Setup.rho_eq_one_iff hDN d).mp hd1
    have hY' : (d : G) ∈ N.Yc := by
      rw [Notation25.mem_Yc]
      intro w hw
      have hle : N.Kplus ≤ Subgroup.centralizer ({(d : G)} : Set G) := by
        refine sup_le ?_ ?_
        · intro k hk
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp d.2.2 k hk
        · intro k hk
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hc k hk
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    rw [hY, Subgroup.mem_bot] at hY'
    exact Subtype.ext hY'
  intro d
  have hαt : Setup.rho (CFSG.conjugate N.K N.x)
      (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G)) hDN d
        ⟨t, htKx⟩ = ⟨t, htKx⟩ := by
    apply Subtype.ext
    rw [Setup.rho_apply_coe]
    have h1 : (d : G) * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp d.2.1
    show (d : G) * t * (d : G)⁻¹ = t
    calc (d : G) * t * (d : G)⁻¹ = (t * d) * (d : G)⁻¹ := by rw [h1]
      _ = t := by group
  obtain ⟨k, hk⟩ := hX.sq_inner (Setup.rho (CFSG.conjugate N.K N.x)
      (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G)) hDN d)
  have hkt : k ∈ Subgroup.centralizer ({(⟨t, htKx⟩ : ↥(CFSG.conjugate N.K N.x))} :
      Set ↥(CFSG.conjugate N.K N.x)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (MulAut.conj k : MulAut ↥(CFSG.conjugate N.K N.x)) ⟨t, htKx⟩ = ⟨t, htKx⟩ := by
      rw [hk, MulAut.mul_apply, hαt, hαt]
    have h2 : k * ⟨t, htKx⟩ * k⁻¹ = ⟨t, htKx⟩ := by simpa [MulAut.conj_apply] using h1
    calc k * ⟨t, htKx⟩ = (k * ⟨t, htKx⟩ * k⁻¹) * k := by group
      _ = ⟨t, htKx⟩ * k := by rw [h2]
  obtain ⟨m, hm⟩ := hcent ⟨k, hkt⟩
  have hkm : k ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hsq : (Setup.rho (CFSG.conjugate N.K N.x)
      (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G)) hDN d *
      Setup.rho (CFSG.conjugate N.K N.x)
      (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G)) hDN d) ^ 2 ^ m
      = 1 := by
    rw [← hk, ← map_pow, hkm, map_one]
  refine ⟨m + 1, hinj _ ?_⟩
  rw [map_pow, pow_succ', pow_mul, pow_two]
  exact hsq

theorem Lv2520.centralizer_t_eq
    (hAF : OutAutAll) (h : Lv2520 N t zK) (hp : CaseCParams N t zK R)
    (hL2p : IsL2pType ↥N.K) (hne : CFSG.conjugate N.K N.x ≠ N.K)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) :
    Subgroup.centralizer ({t} : Set G) = N.K ⊔ N.S := by
  have hD2 := h.D_isPGroup hAF hp hL2p hne hcomm
  have hnorm := h.centralizer_t_le_normalizer_C
  rw [h.hK0] at hnorm
  have hDS : (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G)) ≤ N.S := by
    obtain ⟨m, hm, hmS⟩ := EscapingLocal.exists_conj_mem_of_isPGroup
      (M := Subgroup.centralizer ({t} : Set G)) (T := N.S)
      (S := Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G))
      h.facts2511.sylow.1 h.facts2511.sylow.2.1 h.facts2511.sylow.2.2 inf_le_left hD2
    intro d hd
    have hd' : m⁻¹ * d * m ∈
        Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G) := by
      have := (Subgroup.mem_normalizer_iff.mp
        (hnorm ((Subgroup.centralizer ({t} : Set G)).inv_mem hm)) d).mp hd
      simpa using this
    have := hmS _ hd'
    simpa [mul_assoc] using this
  have h1 := h.concl2518.2.1
  rw [h.hK0] at h1
  exact h1.trans (sup_eq_left.mpr (hDS.trans le_sup_right))

theorem Lv2520.odd_mem_K
    (hAF : OutAutAll) (h : Lv2520 N t zK) (hp : CaseCParams N t zK R)
    (hL2p : IsL2pType ↥N.K) (hne : CFSG.conjugate N.K N.x ≠ N.K)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) {e : G}
    (he : e ∈ Subgroup.centralizer ({t} : Set G)) (hodd : Odd (orderOf e)) : e ∈ N.K :=
  mem_of_odd_orderOf_of_mem_sup N.tuple.sylow.isPGroup h.S_le_normalizer
    (by rw [← h.centralizer_t_eq hAF hp hL2p hne hcomm]; exact he) hodd

theorem Lv2520.simple_le_K
    (hAF : OutAutAll) (h : Lv2520 N t zK) (hp : CaseCParams N t zK R)
    (hL2p : IsL2pType ↥N.K) (hne : CFSG.conjugate N.K N.x ≠ N.K)
    (hcomm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k) {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({t} : Set G)) (hsimple : IsSimpleGroup ↥L)
    (hnc : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) : L ≤ N.K := by
  have hGtN := h.centralizer_t_le_normalizer
  have hGt := h.centralizer_t_eq hAF hp hL2p hne hcomm
  have hnormal : ((L ⊓ N.K).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have hlK : l ∈ Subgroup.normalizer (N.K : Set G) := hGtN (hL hl)
    constructor
    · rintro ⟨hvL, hvK⟩
      exact ⟨L.mul_mem (L.mul_mem hl hvL) (L.inv_mem hl),
        (Subgroup.mem_normalizer_iff.mp hlK v).mp hvK⟩
    · rintro ⟨hvL, hvK⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hlK v).mpr hvK⟩
      have h1 := L.mul_mem (L.mul_mem (L.inv_mem hl) hvL) hl
      have e : l⁻¹ * (l * v * l⁻¹) * l = v := by group
      rwa [e] at h1
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · exfalso
    have hdisj : L ⊓ N.K = ⊥ := by
      have h1 := Subgroup.subgroupOf_eq_bot.mp hbot
      rw [disjoint_iff] at h1
      simpa [inf_assoc] using h1
    have hL2 : IsPGroup 2 ↥L := by
      intro ℓ
      have hℓ : (ℓ : G) ∈ N.K ⊔ N.S := by rw [← hGt]; exact hL ℓ.2
      obtain ⟨k, hk, s, hs, hks⟩ := mem_sup_of_le_normalizer h.S_le_normalizer hℓ
      obtain ⟨j, hj⟩ := N.tuple.sylow.isPGroup ⟨s, hs⟩
      have hs1 : s ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      obtain ⟨k', hk', hpow⟩ := pow_mul_mem_mul_pow h.S_le_normalizer hk hs (2 ^ j)
      rw [hs1, mul_one, ← hks] at hpow
      refine ⟨j, ?_⟩
      apply Subtype.ext
      have h1 : (ℓ : G) ^ 2 ^ j ∈ L ⊓ N.K := ⟨L.pow_mem ℓ.2 _, by rw [hpow]; exact hk'⟩
      rw [hdisj, Subgroup.mem_bot] at h1
      simpa using h1
    have : Group.IsNilpotent ↥L := hL2.isNilpotent
    have hab' : ∀ a b : ↥L, a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    exact hab (congrArg Subtype.val (hab' ⟨a, ha⟩ ⟨b, hb⟩))
  · have h1 := Subgroup.subgroupOf_eq_top.mp htop
    exact fun x hx => (h1 hx).2

end Gt

end CFSG.QuasithinUnique

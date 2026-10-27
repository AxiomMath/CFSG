module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34MSideTwist
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34MSideKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {Y : Type} [Group Y] [Finite Y]

theorem L34MSide.centralizer_eq_bot {T : Subgroup Y} (S : Sylow 3 Y)
    (hcore : primeComplementCore (G := Y) 3 = ⊥)
    (hcenter : ∀ x ∈ (S : Subgroup Y), (∀ y ∈ (S : Subgroup Y), x * y = y * x) → x ∈ T)
    (htr : ∀ t ∈ T, t ≠ 1 → ∀ s ∈ T, s ≠ 1 → ∃ n : Y, n * t * n⁻¹ = s)
    (hT1 : T ≠ ⊥) {L₀ : Subgroup Y} (hnorm : L₀.Normal)
    (hTnc : ∀ t ∈ T, t ≠ 1 → ∃ l ∈ L₀, t * l ≠ l * t) :
    Subgroup.centralizer (L₀ : Set Y) = ⊥ := by
  set C := Subgroup.centralizer (L₀ : Set Y) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  by_cases h3 : 3 ∣ Nat.card C
  · exfalso
    have hTC := L34MSide.le_of_normal_of_three_dvd S hcenter htr hCn h3
    obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hT1)
    obtain ⟨l, hl, hne⟩ := hTnc t t.2 (fun h => ht1 (Subtype.ext h))
    exact hne (Subgroup.mem_centralizer_iff.mp (hTC t.2) l hl).symm
  · have hcop : Nat.Coprime 3 (Nat.card C) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have hle := normal_coprime_le_primeComplementCore 3 C hCn hcop
    rw [hcore] at hle
    exact le_bot_iff.mp hle

omit [Finite Y] in
theorem L34MSide.isSimpleGroup_of_centralizer_eq_bot {L₀ : Subgroup Y}
    (hL₀ : IsComponentOf L₀ ⊤) (hC : Subgroup.centralizer (L₀ : Set Y) = ⊥) :
    Subgroup.center L₀ = ⊥ ∧ IsSimpleGroup L₀ := by
  have hZ : Subgroup.center L₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : (x : Y) ∈ Subgroup.centralizer (L₀ : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have := Subgroup.mem_center_iff.mp hx ⟨l, hl⟩
      exact congrArg Subtype.val this
    rw [hC, Subgroup.mem_bot] at hxC
    exact Subgroup.mem_bot.mpr (Subtype.ext hxC)
  refine ⟨hZ, ?_⟩
  have hs : IsSimpleGroup (L₀ ⧸ Subgroup.center L₀) := hL₀.2.2.2
  exact MulEquiv.isSimpleGroup ((QuotientGroup.quotientBot (G := L₀)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm))

theorem L34MSide.exists_unique_component_le' {z : Y} {R T : Subgroup Y} (S : Sylow 3 Y)
    (hcore : primeComplementCore (G := Y) 3 = ⊥)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hRgen : ∀ r ∈ R, ∃ t ∈ T, ∃ i : ℕ, r = t * z ^ i)
    (hRp : IsPGroup 3 R)
    (hRsyl : ∀ Q : Subgroup Y, Q ≤ Subgroup.centralizer ({z} : Set Y) → IsPGroup 3 Q →
      Nat.card Q ≤ Nat.card R)
    (hRC : R ≤ Subgroup.centralizer ({z} : Set Y))
    (hconj : ∀ y ∈ Subgroup.centralizer ({z} : Set Y), IsPGroup 3 (Subgroup.zpowers y) →
      ∃ c ∈ Subgroup.centralizer ({z} : Set Y), c⁻¹ * y * c ∈ R)
    (hfus : ∀ r ∈ R, r ∉ T → ∃ n : Y, n * r * n⁻¹ ∈ Subgroup.zpowers z)
    (htr : ∀ t ∈ T, t ≠ 1 → ∀ s ∈ T, s ≠ 1 → ∃ n : Y, n * t * n⁻¹ = s)
    (htrz : ∀ t ∈ T, t ≠ 1 → ∀ s ∈ T, s ≠ 1 → ∃ n : Y, n * z * n⁻¹ = z ∧ n * t * n⁻¹ = s)
    (hT9 : Nat.card T = 9)
    (hcenter : ∀ x ∈ (S : Subgroup Y), (∀ y ∈ (S : Subgroup Y), x * y = y * x) → x ∈ T)
    (hzcomp : ∀ L : Subgroup Y, IsComponentOf L ⊤ → z ∉ Subgroup.centralizer (L : Set Y))
    (hfixed : ∀ L : Subgroup Y, IsComponentOf L ⊤ →
      (∃ y ∈ L, IsPGroup 3 (Subgroup.zpowers y) ∧ y * z = z * y ∧ ∃ l ∈ L, y * l ≠ l * y) ∨
      (∃ h ∈ L, h ^ 3 = 1 ∧ ∃ c ∈ L, z * h * z⁻¹ = c * h ∧ c ≠ 1 ∧ c ^ 3 = 1 ∧ c * z = z * c ∧
        ∀ x ∈ L, (∀ l ∈ L, x * l = l * x) ↔ x ∈ Subgroup.zpowers c))
    (hcomp : ∃ L : Subgroup Y, IsComponentOf L ⊤)
    (hcenT : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L.Normal → T ≤ L →
      ¬ ∀ t ∈ T, ∀ l ∈ L, t * l = l * t) :
    ∃ L₀ : Subgroup Y, IsComponentOf L₀ ⊤ ∧ L₀.Normal ∧ T ≤ L₀ ∧
      (∀ t ∈ T, t ≠ 1 → ∃ l ∈ L₀, t * l ≠ l * t) ∧
      (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₀) := by
  have hW : ∀ L : Subgroup Y, IsComponentOf L ⊤ → ∃ w ∈ L, w ≠ 1 ∧
      IsPGroup 3 (Subgroup.zpowers w) ∧ w * z = z * w := by
    intro L hL
    rcases hfixed L hL with ⟨y, hyL, hyp, hyz, hync⟩ | ⟨-, -, -, c, hcL, -, hc1, hc3, hcz, -⟩
    · exact ⟨y, hyL, L34MSide.ne_one_of_noncentral hync, hyp, hyz⟩
    · exact ⟨c, hcL, hc1, L34MSide.isPGroup_zpowers_of_pow_three hc3, hcz⟩
  by_cases hgood : ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧ ∃ y ∈ L,
      IsPGroup 3 (Subgroup.zpowers y) ∧ y * z = z * y ∧ ∃ l ∈ L, y * l ≠ l * y
  · obtain ⟨L, hL, y, hyL, hyp, hyz, hync⟩ := hgood
    exact L34MSide.exists_unique_component_le_good S hcore hz3 hz1 hRgen hRp hRsyl hRC hconj
      hfus htr hcenter hzcomp hW hL hyL hyp hyz hync hcenT
  · exfalso
    push Not at hgood
    have htwist : ∀ L : Subgroup Y, IsComponentOf L ⊤ →
        ∃ h ∈ L, h ^ 3 = 1 ∧ ∃ c ∈ L, z * h * z⁻¹ = c * h ∧ c ≠ 1 ∧ c ^ 3 = 1 ∧
          c * z = z * c ∧ ∀ x ∈ L, (∀ l ∈ L, x * l = l * x) ↔ x ∈ Subgroup.zpowers c := by
      intro L hL
      rcases hfixed L hL with ⟨y, hyL, hyp, hyz, l, hl, hne⟩ | h2
      · exact absurd (hgood L hL y hyL hyp hyz l hl) hne
      · exact h2
    exact L34MSide.false_of_bad hz3 hz1 hconj hfus htr htrz hT9 hzcomp hgood htwist hcomp

theorem L34MSide.false_of_mtilde' (hKZ : KFactMSideAlmostSimpleE27)
    (hKβ1 : KFactCompFixedThreeEltN) (hKZ9 : KFactCompCenterNine)
    (hcore : primeComplementCore (G := Y) 3 = ⊥) {z : Y} {R T : Subgroup Y}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hRel : IsElemAbelian 3 R) (hR27 : Nat.card R = 27) (hTR : T ≤ R) (hT9 : Nat.card T = 9)
    (hzR : z ∈ R) (hzT : z ∉ T)
    (hRgen : ∀ r ∈ R, ∃ t ∈ T, ∃ i : ℕ, r = t * z ^ i)
    (hfusN : ∀ r ∈ R, r ∉ T → ∃ n ∈ Subgroup.normalizer (R : Set Y),
      n * r * n⁻¹ ∈ Subgroup.zpowers z)
    (htrN : ∀ t ∈ T, t ≠ 1 → ∀ s ∈ T, s ≠ 1 → ∃ n ∈ Subgroup.normalizer (R : Set Y),
      n * z * n⁻¹ = z ∧ (∀ x ∈ T, n * x * n⁻¹ ∈ T) ∧ n * t * n⁻¹ = s)
    (hRC : R ≤ Subgroup.centralizer ({z} : Set Y))
    (hRsyl : ∀ Q : Subgroup Y, Q ≤ Subgroup.centralizer ({z} : Set Y) → IsPGroup 3 Q →
      Nat.card Q ≤ Nat.card R)
    (hperf : ∀ D : Subgroup Y, D ≤ Subgroup.centralizer ({z} : Set Y) → ⁅D, D⁆ = D →
      ¬ 3 ∣ Nat.card D)
    (hT3c : ∀ t ∈ T, t ≠ 1 →
      ∃ S : Sylow 3 Y, (S : Subgroup Y) ≤ Subgroup.centralizer ({t} : Set Y))
    (h81 : 81 ∣ Nat.card Y)
    (hcenterP : ∃ S : Sylow 3 Y,
      ∀ x ∈ (S : Subgroup Y), (∀ y ∈ (S : Subgroup Y), x * y = y * x) → x ∈ T)
    (hzcomp : ∀ L : Subgroup Y, IsComponentOf L ⊤ →
      z ∈ Subgroup.normalizer (L : Set Y) ∧ z ∉ Subgroup.centralizer (L : Set Y))
    (hcat : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCatalogGroup (L ⧸ Subgroup.center L))
    (hcomp : ∃ L : Subgroup Y, IsComponentOf L ⊤) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := hcenterP
  have hRp : IsPGroup 3 R := IsPGroup.of_card (n := 3) (by rw [hR27]; norm_num)
  obtain ⟨SZ, hSZ⟩ : ∃ S : Sylow 3 ↥(Subgroup.centralizer ({z} : Set Y)),
      (S : Subgroup _).map (Subgroup.centralizer ({z} : Set Y)).subtype = R := by
    have hRp' : IsPGroup 3 (R.subgroupOf (Subgroup.centralizer ({z} : Set Y))) :=
      hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRC).symm
    obtain ⟨S', hS'⟩ := hRp'.exists_le_sylow
    refine ⟨S', ?_⟩
    have hle : R ≤ (S' : Subgroup _).map (Subgroup.centralizer ({z} : Set Y)).subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hRC]
      exact Subgroup.map_mono hS'
    have hcard := hRsyl _ (Subgroup.map_subtype_le _) (S'.isPGroup'.map _)
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hconj : ∀ y ∈ Subgroup.centralizer ({z} : Set Y), IsPGroup 3 (Subgroup.zpowers y) →
      ∃ c ∈ Subgroup.centralizer ({z} : Set Y), c⁻¹ * y * c ∈ R := by
    intro y hy hyp
    have hyp' : IsPGroup 3 (Subgroup.zpowers
        (⟨y, hy⟩ : Subgroup.centralizer ({z} : Set Y))) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hyp
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_zpowers, ← hk, Nat.card_zpowers]
      exact (orderOf_injective (Subgroup.centralizer ({z} : Set Y)).subtype
        (Subgroup.centralizer ({z} : Set Y)).subtype_injective ⟨y, hy⟩).symm
    obtain ⟨Q, hQ⟩ := hyp'.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (Subgroup.centralizer ({z} : Set Y)) Q SZ
    refine ⟨((c⁻¹ : Subgroup.centralizer ({z} : Set Y)) : Y),
      (c⁻¹ : Subgroup.centralizer ({z} : Set Y)).2, ?_⟩
    rw [← hSZ]
    refine ⟨c * ⟨y, hy⟩ * c⁻¹, ?_, ?_⟩
    · rw [← hc, Sylow.coe_subgroup_smul]
      exact ⟨⟨y, hy⟩, hQ (Subgroup.mem_zpowers _), by simp [MulAut.conj_apply]⟩
    · simp
  have hfus : ∀ r ∈ R, r ∉ T → ∃ n : Y, n * r * n⁻¹ ∈ Subgroup.zpowers z :=
    fun r hr hrT => by
      obtain ⟨n, -, hn⟩ := hfusN r hr hrT
      exact ⟨n, hn⟩
  have htr : ∀ t ∈ T, t ≠ 1 → ∀ s ∈ T, s ≠ 1 → ∃ n : Y, n * t * n⁻¹ = s :=
    fun t ht ht1 s hs hs1 => by
      obtain ⟨n, -, -, -, hn⟩ := htrN t ht ht1 s hs hs1
      exact ⟨n, hn⟩
  have htrz : ∀ t ∈ T, t ≠ 1 → ∀ s ∈ T, s ≠ 1 → ∃ n : Y, n * z * n⁻¹ = z ∧ n * t * n⁻¹ = s :=
    fun t ht ht1 s hs hs1 => by
      obtain ⟨n, -, hnz, -, hn⟩ := htrN t ht ht1 s hs hs1
      exact ⟨n, hnz, hn⟩
  have hfixed := fun (L : Subgroup Y) (hL : IsComponentOf L ⊤) =>
    hKβ1 Y L hL (hcat L hL) (isPGroup_center_of_isComponentOf Nat.prime_three hcore hL)
      (prime_dvd_card_center_quotient_of_isComponentOf Nat.prime_three hcore hL) z hz3
      (hzcomp L hL).1 (hzcomp L hL).2 (fun Q hQ hQp => hR27 ▸ hRsyl Q hQ hQp)
  have hTel : IsElemAbelian 3 T := by
    refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => hRel.2 x (hTR hx)⟩
    have h := (isMulCommutative_iff.mp hRel.1) ⟨a, hTR a.2⟩ ⟨b, hTR b.2⟩
    have h' := congrArg Subtype.val h
    simpa using h'
  have hcenT : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L.Normal → T ≤ L →
      ¬ ∀ t ∈ T, ∀ l ∈ L, t * l = l * t := by
    intro L hL hLn hTL hc
    obtain ⟨e, he, he1, f, hf, hf1, hne⟩ :=
      hKZ9 Y L hL hLn (hcat L hL) T hTL hc hTel hT9
    obtain ⟨n, hn⟩ := htr e he he1 f hf hf1
    exact hne n hn
  obtain ⟨L₀, hL₀, hnorm, hTL₀, hTnc, -⟩ := L34MSide.exists_unique_component_le' S hcore hz3
    hz1 hRgen hRp hRsyl hRC hconj hfus htr htrz hT9 hS (fun L hL => (hzcomp L hL).2) hfixed
    hcomp hcenT
  have hT1 : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hT9
    omega
  have hC := L34MSide.centralizer_eq_bot S hcore hS htr hT1 hnorm hTnc
  obtain ⟨hZ, hsimple⟩ := L34MSide.isSimpleGroup_of_centralizer_eq_bot hL₀ hC
  have hnonab : ∃ a b : L₀, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center L₀ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact Subgroup.mem_center_iff.mpr fun g => h g x
    have : Nontrivial L₀ := hsimple.toNontrivial
    rw [hZ] at htop
    exact bot_ne_top htop
  have hcatL₀ : IsCatalogGroup L₀ :=
    IsCatalogGroup.of_mulEquiv ((QuotientGroup.quotientBot (G := L₀)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)) (hcat L₀ hL₀)
  exact hKZ Y L₀ hnorm hsimple hnonab hcatL₀ hC R T z hRel hR27 hTR hTL₀ hT9 hzR hzT hfusN htrN
    ⟨SZ, hSZ⟩ hperf hT3c h81

end CFSG.AGLEmbedding

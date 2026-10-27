module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Basic
public import CFSG.LocalAnalysis.GL83PartI.I_20_1
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def layerClosure (p : ℕ) (D' J : Subgroup G) : Subgroup G :=
  ⨆ g ∈ GLAPLayer p (Subgroup.centralizer (D' : Set G)), GLBConj g J

namespace S3

private theorem layer_top_eq_bot {p : ℕ} (hp : p.Prime) (C : Subgroup G) (h : GLAPLayer p C = ⊥) :
    GLAPLayer p (⊤ : Subgroup C) = ⊥ := by
  have hle : GLAPLayer p (⊤ : Subgroup C) ≤ (GLAPLayer p C).comap C.subtype := by
    unfold GLAPLayer
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup C) ⊓ C.subtype.ker)) := by
      have : (⊤ : Subgroup C) ⊓ C.subtype.ker = ⊥ := by simp
      rw [this, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    have h1 := glaPComponent_map hp C.subtype hker hJ
    have htop : (⊤ : Subgroup C).map C.subtype = C :=
      le_antisymm (by rintro _ ⟨y, -, rfl⟩; exact y.2) fun y hy => ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
    rw [htop] at h1
    exact le_sSup h1
  rw [h, MonoidHom.comap_bot, Subgroup.ker_subtype] at hle
  exact le_bot_iff.1 hle

private theorem primeCoreOf_top_eq (p : ℕ) (X : Type) [Group X] :
    GLAPPrimeCoreOf p (⊤ : Subgroup X) = GLAPPrimeCore p X := by
  have h := glaPPrimeCore_map_iso p (Subgroup.topEquiv (G := X))
  have hsub : (⊤ : Subgroup X).subtype = (Subgroup.topEquiv (G := X)).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  unfold GLAPPrimeCoreOf
  rw [hsub, h]

theorem bender_G {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G} {B S : Subgroup G}
    (hB : IsElemAbelian p B) (hxB : x ∈ B) (hSC : IsSC p B)
    (hlayer : GLAPLayer p (Subgroup.centralizer ({x} : Set G)) = ⊥)
    (hS2 : IsPGroup 2 S) (hSx : S ≤ Subgroup.centralizer ({x} : Set G))
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hBC : B ≤ C := fun b hb => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute hB hb hxB
  have hB'el : IsElemAbelian p (B.subgroupOf C) :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (isElemAbelian_commute hB a.2 b.2))⟩⟩,
      fun y hy => Subtype.ext (by simpa using hB.2 (y : G) hy)⟩
  have hmax : ∀ E : Subgroup C, IsElemAbelian p E → B.subgroupOf C ≤ E → E = B.subgroupOf C := by
    intro E hE hBE
    refine le_antisymm (fun e he => ?_) hBE
    rw [Subgroup.mem_subgroupOf]
    have hcomm : (e : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 := hE.1.1.comm ⟨⟨b, hBC hb⟩, hBE (Subgroup.mem_subgroupOf.2 hb)⟩ ⟨e, he⟩
      simpa using congrArg (fun z : E => ((z : C) : G)) h1
    have hpow : (e : G) ^ p = 1 := by
      have := hE.2 e he
      simpa using congrArg (fun z : C => (z : G)) this
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hpow) with h1 | h1
    · rw [orderOf_eq_one_iff.1 h1]; exact B.one_mem
    · exact hSC.2 _ hcomm h1
  have hS'cop : Nat.Coprime p (Nat.card (S.subgroupOf C)) := by
    have hcard : Nat.card (S.subgroupOf C) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSx).toEquiv
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS2
    rw [hcard, hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hBS' : B.subgroupOf C ≤ Subgroup.normalizer ((S.subgroupOf C : Subgroup C) : Set C) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 (hBS (Subgroup.mem_subgroupOf.1 hb)) (s : G)
  have key := GL83.I_20_1_proved C p hp hp2 (layer_top_eq_bot hp C hlayer) (B.subgroupOf C) hB'el hmax
  have hle : S.subgroupOf C ≤ GLAPPrimeCoreOf p (⊤ : Subgroup C) := by
    rw [← key]
    exact le_iSup_of_le (S.subgroupOf C) (le_iSup_of_le hS'cop (le_iSup_of_le hBS' le_rfl))
  intro s hs
  have h1 : (⟨s, hSx hs⟩ : C) ∈ GLAPPrimeCoreOf p (⊤ : Subgroup C) := hle (Subgroup.mem_subgroupOf.2 hs)
  rw [primeCoreOf_top_eq] at h1
  exact ⟨_, h1, rfl⟩

theorem delta_contra {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hΔ : GLADeltaZero G p)
    {B D₀ S : Subgroup G} (hB : GLAIsBmax p B) (hD₀B : D₀ ≤ B) (hD₀card : p ^ 2 ∣ Nat.card D₀)
    (hS2 : IsPGroup 2 S) (hS : S ≠ ⊥) (hSB : (⁅B, S⁆ : Subgroup G) = S)
    (hSC : ∀ x ∈ D₀, x ≠ 1 →
      S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))) : False := by
  have hDel0 : IsElemAbelian p D₀ := isElemAbelian_mono hB.1 hD₀B
  obtain ⟨D, hDD₀, hDcard⟩ := S3.exists_card_pow_le hp hDel0 hD₀card
  have hDB : D ≤ B := hDD₀.trans hD₀B
  have hDel : IsElemAbelian p D := isElemAbelian_mono hDel0 hDD₀
  obtain ⟨h5, h3⟩ := hΔ B hB D hDB hDel hDcard
  have hSΔ : S ≤ GLADelta p D := by
    refine le_iInf₂ (fun d hd => le_iInf fun hd1 => ?_)
    exact hSC d (hDD₀ hd) hd1
  have hS_even : 2 ∣ Nat.card S := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hS (Subgroup.eq_bot_of_card_eq S (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  by_cases hp3 : p = 3
  · have hle : S ≤ (⁅GLADelta p D, B⁆ : Subgroup G) := by
      calc S = ⁅B, S⁆ := hSB.symm
        _ ≤ ⁅B, GLADelta p D⁆ := Subgroup.commutator_mono le_rfl hSΔ
        _ = ⁅GLADelta p D, B⁆ := Subgroup.commutator_comm _ _
    exact (Nat.not_even_iff_odd.2 (h3 hp3))
      (even_iff_two_dvd.2 (hS_even.trans (Subgroup.card_dvd_of_le hle)))
  · have hp5 : 5 ≤ p := by
      by_contra h
      push_neg at h
      interval_cases p <;> simp_all <;> exact absurd hp (by norm_num)
    exact (Nat.not_even_iff_odd.2 (h5 hp5))
      (even_iff_two_dvd.2 (hS_even.trans (Subgroup.card_dvd_of_le hSΔ)))

theorem mem_normalizer_inf_cen {K D B : Subgroup G} {b : G} (hB : IsMulCommutative B)
    (hDB : D ≤ B) (hb : b ∈ B) (hbK : b ∈ Subgroup.normalizer (K : Set G)) :
    b ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  have hbC : b ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h := hB.1.comm ⟨d, hDB hd⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val h
  have hbN2 : b ∈ Subgroup.normalizer ((Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hbC
  rw [Subgroup.mem_normalizer_iff] at hbK hbN2 ⊢
  intro x
  simp only [Subgroup.mem_inf]
  exact and_congr (hbK x) (hbN2 x)

theorem two_core_cen_props {p : ℕ} {B D₀ N : Subgroup G} (hBN : B ≤ N) (hB : IsElemAbelian p B)
    (hD₀B : D₀ ≤ B) :
    IsPGroup 2 ↥(pCoreOf 2 N ⊓ Subgroup.centralizer (D₀ : Set G)) ∧
      B ≤ Subgroup.normalizer ((pCoreOf 2 N ⊓ Subgroup.centralizer (D₀ : Set G) : Subgroup G) :
        Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥(pCoreOf 2 N) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  refine ⟨IsPGroup.to_le hT2 inf_le_left, fun b hb => ?_⟩
  have hbN : b ∈ Subgroup.normalizer ((pCoreOf 2 N : Subgroup G) : Set G) :=
    le_normalizer_pCoreOf 2 N (hBN hb)
  exact S3.mem_normalizer_inf_cen hB.1 hD₀B hb hbN

theorem comm_two_group {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B R : Subgroup G}
    (hB : IsElemAbelian p B) (hR2 : IsPGroup 2 R) (hBR : B ≤ Subgroup.normalizer (R : Set G)) :
    (⁅B, R⁆ : Subgroup G) ≤ R ∧ B ≤ Subgroup.normalizer ((⁅B, R⁆ : Subgroup G) : Set G) ∧
      (⁅B, (⁅B, R⁆ : Subgroup G)⁆ : Subgroup G) = ⁅B, R⁆ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : (⁅B, R⁆ : Subgroup G) ≤ R := by
    rw [Subgroup.commutator_le]
    intro b hb r hr
    have := (Subgroup.mem_normalizer_iff.1 (hBR hb) r).1 hr
    exact R.mul_mem this (R.inv_mem hr)
  have h2 : B ≤ Subgroup.normalizer ((⁅B, R⁆ : Subgroup G) : Set G) := by
    intro b hb
    rw [mem_normalizer_iff_gLBConj_eq]
    have hbB : b ∈ Subgroup.normalizer (B : Set G) := Subgroup.le_normalizer hb
    have hbR := hBR hb
    rw [mem_normalizer_iff_gLBConj_eq] at hbB hbR
    have h : GLBConj b ⁅B, R⁆ = ⁅GLBConj b B, GLBConj b R⁆ := by
      unfold GLBConj
      rw [Subgroup.map_commutator]
    rw [h, hbB, hbR]
  have hcop : Nat.Coprime (Nat.card B) (Nat.card R) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 (isPGroup_of_isElemAbelian hB)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hR2
    rw [hm, hn]
    exact Nat.Coprime.pow m n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  refine ⟨h1, h2, ?_⟩
  haveI : Group.IsNilpotent R := hR2.isNilpotent
  haveI : Group.IsSolvable R := inferInstance
  have h3 := GL83.commutator_double_eq_self B R hBR hcop inferInstance
  calc (⁅B, (⁅B, R⁆ : Subgroup G)⁆ : Subgroup G) = ⁅B, ⁅R, B⁆⁆ := by rw [Subgroup.commutator_comm B R]
    _ = ⁅⁅R, B⁆, B⁆ := Subgroup.commutator_comm _ _
    _ = ⁅R, B⁆ := h3
    _ = ⁅B, R⁆ := Subgroup.commutator_comm _ _

private theorem isElemAbelian_sup_zpowers' {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    {z : G} (hzp : z ^ p = 1) (hz : ∀ e ∈ E, e * z = z * e) :
    IsElemAbelian p (E ⊔ Subgroup.zpowers z) := by
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (E : Set G) (Subgroup.mem_centralizer_iff.mpr hz)
  have hdec : ∀ x ∈ E ⊔ Subgroup.zpowers z, ∃ e ∈ E, ∃ k : ℤ, x = e * z ^ k := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left E _ hnorm] at hx
    obtain ⟨e, he, y, hy, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨e, he, k, rfl⟩
  have hcomm : ∀ e ∈ E, ∀ k : ℤ, Commute e (z ^ k) := fun e he k =>
    Commute.zpow_right (hz e he) k
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨e₁, he₁, k₁, h₁⟩ := hdec x x.2
    obtain ⟨e₂, he₂, k₂, h₂⟩ := hdec y y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [h₁, h₂]
    have h12 : e₁ * e₂ = e₂ * e₁ := isElemAbelian_commute hE he₁ he₂
    calc e₁ * z ^ k₁ * (e₂ * z ^ k₂) = e₁ * (z ^ k₁ * e₂) * z ^ k₂ := by group
      _ = e₁ * (e₂ * z ^ k₁) * z ^ k₂ := by rw [(hcomm e₂ he₂ k₁).eq]
      _ = (e₁ * e₂) * (z ^ k₁ * z ^ k₂) := by group
      _ = (e₂ * e₁) * (z ^ k₂ * z ^ k₁) := by rw [h12, ← zpow_add, ← zpow_add, add_comm]
      _ = e₂ * (e₁ * z ^ k₂) * z ^ k₁ := by group
      _ = e₂ * (z ^ k₂ * e₁) * z ^ k₁ := by rw [(hcomm e₁ he₁ k₂).eq]
      _ = e₂ * z ^ k₂ * (e₁ * z ^ k₁) := by group
  · obtain ⟨e, he, k, rfl⟩ := hdec x hx
    rw [(hcomm e he k).mul_pow, hE.2 e he, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hzp, one_zpow]

theorem isSC_iff_maximal {H : Type} [Group H] {p : ℕ} (hp : p.Prime) {B : Subgroup H} :
    IsSC p B ↔ IsElemAbelian p B ∧
      ∀ E : Subgroup H, IsElemAbelian p E → B ≤ E → E = B := by
  constructor
  · intro hSC
    refine ⟨hSC.1, ?_⟩
    intro E hE hBE
    refine le_antisymm (fun e he => ?_) hBE
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hE.2 e he)) with h1 | hpord
    · rw [orderOf_eq_one_iff.1 h1]
      exact B.one_mem
    · exact hSC.2 e (Subgroup.mem_centralizer_iff.2
        (fun b hb => isElemAbelian_commute hE (hBE hb) he)) hpord
  · rintro ⟨hB, hmax⟩
    refine ⟨hB, ?_⟩
    intro g hg hord
    have hgp : g ^ p = 1 := hord ▸ pow_orderOf_eq_one g
    have hz : ∀ e ∈ B, e * g = g * e :=
      fun e he => Subgroup.mem_centralizer_iff.1 hg e he
    have hE : IsElemAbelian p (B ⊔ Subgroup.zpowers g) :=
      IsElemAbelian.sup_of_commute hB (CFSG.Open.isElemAbelian_zpowers hgp) (by
        intro a ha b hb
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact ((show Commute a g from hz a ha).zpow_right k).eq)
    have hEB := hmax (B ⊔ Subgroup.zpowers g) hE le_sup_left
    exact hEB ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g)

theorem i326 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B D : Subgroup G} (hB : GLAIsBmax p B)
    (hDB : D ≤ B) (hD : D ≠ ⊥)
    (heven : Even (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set G))))) :
    IsSC p B := by
  refine ⟨hB.1, ?_⟩
  intro g hg hord
  by_contra hgB
  have hBel := hB.1
  have hgp : g ^ p = 1 := hord ▸ pow_orderOf_eq_one g
  have hz : ∀ e ∈ B, e * g = g * e := fun e he => Subgroup.mem_centralizer_iff.1 hg e he
  have hEel : IsElemAbelian p (B ⊔ Subgroup.zpowers g) := isElemAbelian_sup_zpowers' hBel hgp hz
  have hgE : g ∈ B ⊔ Subgroup.zpowers g :=
    (le_sup_right : Subgroup.zpowers g ≤ B ⊔ Subgroup.zpowers g) (Subgroup.mem_zpowers g)
  have hBE : B ≤ B ⊔ Subgroup.zpowers g := le_sup_left
  have hEC : B ⊔ Subgroup.zpowers g ≤ Subgroup.centralizer (D : Set G) := by
    refine sup_le ?_ ?_
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact isElemAbelian_commute hBel (hDB hd) hb
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_iff.2 (fun d hd => hz d (hDB hd))
  have hEN : B ⊔ Subgroup.zpowers g ≤
      Subgroup.normalizer ((GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set G)) : Subgroup G) :
        Set G) :=
    fun x hx => le_normalizer_glaPPrimeCoreOf p (Subgroup.centralizer (D : Set G)) (hEC hx)
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set G)))) :=
    (hp.coprime_iff_not_dvd).2 (not_dvd_card_glaPPrimeCoreOf hp _)
  obtain ⟨S, -, hS2, hS, hSN, -⟩ := S3.exists_invariant_sylow hp Nat.prime_two
    (isPGroup_of_isElemAbelian hEel) hEN hcop (even_iff_two_dvd.1 heven)
  have hle := card_le_pow_glaTwoLocalRank hp hEel hS hS2 hSN
  rw [← hB.2.1] at hle
  have hEB : B = B ⊔ Subgroup.zpowers g := Subgroup.eq_of_le_of_card_ge hBE hle
  exact hgB (hEB ▸ hgE)

theorem i326_holds {G : Type} [Group G] [Finite G] (p : ℕ) :
    p.Prime → p ≠ 2 → ∀ B D : Subgroup G, GLAIsBmax p B → D ≤ B → D ≠ ⊥ →
      Even (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set G)))) → IsSC p B :=
  fun hp hp2 _ _ hB hDB hD heven => i326 hp hp2 hB hDB hD heven

theorem iSup_eq_of_transitive {𝒞 : Set (Subgroup G)} {D B : Subgroup G} (hDB : D ≤ B)
    (hB : ∀ L ∈ 𝒞, B ≤ Subgroup.normalizer (L : Set G))
    (htr : ∀ L ∈ 𝒞, ∀ L' ∈ 𝒞, ∃ e ∈ D, GLBConj e L = L') :
    ∀ L ∈ 𝒞, (⨆ L' ∈ 𝒞, L') = L := by
  intro L hL
  apply le_antisymm
  · refine iSup₂_le fun L' hL' => ?_
    obtain ⟨e, he, heq⟩ := htr L hL L' hL'
    have : GLBConj e L = L := gLBConj_eq_of_mem_normalizer (hB L hL (hDB he))
    rw [← heq, this]
  · exact le_iSup₂ (f := fun L' (_ : L' ∈ 𝒞) => L') L hL

theorem closure_eq {p : ℕ} (hp : p.Prime) (hI18 : Input18_3_4) {B D D' J : Subgroup G}
    (hKG : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (D' : Set G)))
    (hD'D : D' ≤ D) (hDB : D ≤ B) (hB : IsElemAbelian p B)
    (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J)
    (hnorm : ∀ J' : Subgroup G, GLAPComponent p (Subgroup.centralizer (D' : Set G)) J' →
      B ≤ Subgroup.normalizer (J' : Set G)) :
    GLAPComponent p (Subgroup.centralizer (D' : Set G)) (layerClosure p D' J) ∧
      J ≤ layerClosure p D' J ∧ B ≤ Subgroup.normalizer ((layerClosure p D' J : Subgroup G) : Set G) ∧
      GLAPComponent p (layerClosure p D' J ⊓ Subgroup.centralizer (D : Set G)) J := by
  have hDel : IsElemAbelian p D := isElemAbelian_mono hB hDB
  have hDX : D ≤ Subgroup.centralizer (D' : Set G) := fun d hd => by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact isElemAbelian_commute hDel (hD'D he) hd
  have hJ' : GLAPComponent p (Subgroup.centralizer (D' : Set G) ⊓
      Subgroup.centralizer (D : Set G)) J := by
    have : Subgroup.centralizer (D' : Set G) ⊓ Subgroup.centralizer (D : Set G) =
        Subgroup.centralizer (D : Set G) :=
      inf_eq_right.2 (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hD'D))
    rw [this]
    exact hJ
  obtain ⟨𝒞, hcomp, hsup, -, htr⟩ := hI18 G (Subgroup.centralizer (D' : Set G)) hKG p hp D hDX hDel J hJ'
  have hJle : J ≤ layerClosure p D' J := by
    unfold layerClosure
    have h : GLBConj (1 : G) J ≤
        ⨆ g ∈ GLAPLayer p (Subgroup.centralizer (D' : Set G)), GLBConj g J :=
      le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) le_rfl
    rwa [gLBConj_one] at h
  have hJne : J ≠ ⊥ := glaPComponent_ne_bot' hJ
  have hne : 𝒞.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hJne
    rw [← le_bot_iff]
    calc J ≤ layerClosure p D' J := hJle
      _ = ⨆ L ∈ 𝒞, L := hsup.symm
      _ = ⊥ := by rw [h]; simp
  obtain ⟨L, hL⟩ := hne
  have hKL : layerClosure p D' J = L := by
    have := S3.iSup_eq_of_transitive (𝒞 := 𝒞) hDB (fun L' hL' => hnorm L' (hcomp L' hL')) htr L hL
    rw [← this]
    exact hsup.symm
  rw [hKL]
  refine ⟨hcomp L hL, hKL ▸ hJle, hnorm L (hcomp L hL), ?_⟩
  exact glaPComponent_of_le hp hJ (le_inf (hKL ▸ hJle) hJ.1) inf_le_right

end S3

theorem lemma34_i {p : ℕ} (hc : S3Ctx G p) {B : Subgroup G} (hB : GLAIsBmax p B)
    (hnc : ∀ (x : G) (L : Subgroup G), IsEssential p B x →
      ¬ GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L) : ¬ IsSC p B := by
  intro hSC
  have hp := hc.prime
  have hp2 := hc.odd
  obtain ⟨N, hN, hBN⟩ := GLAIsBmax.exists_maxTwoLocal hB
  have hcard : p ^ 4 ≤ Nat.card B := by
    rw [hB.2.1]
    exact Nat.pow_le_pow_right hp.pos hc.rank_ge
  have hncyc : ¬ IsCyclic B :=
    S3.not_isCyclic_of_card hp hB.1 (le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) hcard)
  obtain ⟨D₀, hD₀B, hD₀card, hD₀ess, hD₀comm⟩ := hc.lemma31 B B N hB le_rfl hncyc hN hBN
  obtain ⟨hR2, hBR⟩ := S3.two_core_cen_props hBN hB.1 hD₀B
  obtain ⟨hSR, hBS, hSS⟩ := S3.comm_two_group hp hp2 hB.1 hR2 hBR
  have hD₀dvd : p ^ 2 ∣ Nat.card D₀ := by
    have h4 := hc.rank_ge
    have h1 : Nat.card D₀ * p = p ^ (GLATwoLocalRank p G - 1) * p := by
      rw [hD₀card, hB.2.1, ← pow_succ]
      congr 1
      omega
    have h2 : Nat.card D₀ = p ^ (GLATwoLocalRank p G - 1) := Nat.eq_of_mul_eq_mul_right hp.pos h1
    rw [h2]
    exact pow_dvd_pow p (by omega)
  refine S3.delta_contra (S := ⁅B, pCoreOf 2 N ⊓ Subgroup.centralizer (D₀ : Set G)⁆) hp hp2
    hc.deltaZero hB hD₀B hD₀dvd (IsPGroup.to_le hR2 hSR) hD₀comm hSS ?_
  intro x hx hx1
  have hlayer : GLAPLayer p (Subgroup.centralizer ({x} : Set G)) = ⊥ := by
    by_contra h
    obtain ⟨L, hL⟩ := (S3.glaPLayer_ne_bot_iff hp).1 h
    exact hnc x L (hD₀ess x hx hx1) hL
  refine S3.bender_G hp hp2 hB.1 (hD₀B hx) hSC hlayer (IsPGroup.to_le hR2 hSR) ?_ hBS
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hsR := hSR hs
  exact (Subgroup.mem_centralizer_iff.1 hsR.2 x hx).symm

theorem lemma34_ii {p : ℕ} (hc : S3Ctx G p) {B : Subgroup G} (hS : Star3 G p B) {D : Subgroup G}
    (hDB : D ≤ B) (hD : D ≠ ⊥) :
    Odd (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set G)))) := by
  by_contra h
  exact hS.notSC (S3.i326 hc.prime hc.odd hS.bmax hDB hD (Nat.not_odd_iff_even.1 h))

theorem Star3.of_noComp {p : ℕ} (hc : S3Ctx G p) {B : Subgroup G} (hB : GLAIsBmax p B)
    (hnc : ∀ (x : G) (L : Subgroup G), IsEssential p B x →
      ¬ GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L) : Star3 G p B :=
  ⟨hB, lemma34_i hc hB hnc, fun x L hx hL => (hnc x L hx hL).elim⟩

theorem Star3.normalizes {p : ℕ} (hc : S3Ctx G p) {B : Subgroup G} (hS : Star3 G p B)
    (h1135 : I1135At G p) {x : G} (hx : IsEssential p B x) {L : Subgroup G}
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L) :
    B ≤ Subgroup.normalizer (L : Set G) := by
  by_contra h
  have hK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) := by
    have := S3.isKGroup_cen hc.simple hc.nonabelian hc.kProper (E := Subgroup.zpowers x)
      (by rw [Ne, Subgroup.zpowers_eq_bot]; exact hx.2.1)
    rwa [S3.centralizer_zpowers] at this
  exact hS.notSC (h1135 hc.prime hc.odd B x L hK hS.bmax hx hL h (hS.chev x L hx hL))

theorem lemma34_iii {p : ℕ} (hc : S3Ctx G p) (hI18 : Input18_3_4) (h1135 : I1135At G p)
    (hCl : ChevClosureAt G p) (hUn : ChevUniqueAt G p) {B : Subgroup G} (hS : Star3 G p B)
    {D : Subgroup G} (hDB : D ≤ B) (hess : ∃ d ∈ D, IsEssential p B d) {J : Subgroup G}
    (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J) :
    IsChevSimple p (PSimple p J) ∧ B ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨d, hdD, hd⟩ := hess
  have hp := hc.prime
  have hDabel : IsElemAbelian p D := isElemAbelian_mono hS.bmax.1 hDB
  have hD'D : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.2 hdD
  have hcen : Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) =
      Subgroup.centralizer ({d} : Set G) := S3.centralizer_zpowers d
  have hD'ne : Subgroup.zpowers d ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hd.2.1
  have hKG := S3.isKGroup_cen hc.simple hc.nonabelian hc.kProper hD'ne
  have hnorm : ∀ J' : Subgroup G,
      GLAPComponent p (Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G)) J' →
      B ≤ Subgroup.normalizer (J' : Set G) := fun J' hJ' =>
    hS.normalizes hc h1135 hd (hcen ▸ hJ')
  obtain ⟨hKcomp, -, hBK, hJK⟩ :=
    S3.closure_eq hp hI18 hKG hD'D hDB hS.bmax.1 hJ hnorm
  have hKchev := hS.chev d _ hd (hcen ▸ hKcomp)
  have hDK : D ≤ Subgroup.normalizer ((layerClosure p (Subgroup.zpowers d) J : Subgroup G) : Set G) :=
    hDB.trans hBK
  have hX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G)) :=
    hKG
  refine ⟨hCl hp hc.odd _ _ D hX hKcomp hKchev hDabel hDK J hJK, ?_⟩
  intro b hb
  have hbK := hBK hb
  have hbN := S3.mem_normalizer_inf_cen hS.bmax.1.1 hDB hb hbK
  have hfix := mem_normalizer_iff_gLBConj_eq.1 hbN
  have hconj := glaPComponent_gLBConj hJK b
  rw [hfix] at hconj
  have := hUn hp hc.odd _ _ D hX hKcomp hKchev hDabel hDK J _ hJK hconj
  rw [mem_normalizer_iff_gLBConj_eq]
  exact this.symm

end CFSG.LocalAnalysis.GLTheoremA

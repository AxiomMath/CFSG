module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Master

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Generic

theorem dvd_of_isInnerAut_zpow {L : Type*} [Group L] {p : ℕ} (hp : p.Prime) {ψ : MulAut L}
    (hψ : ¬ IsInnerAut ψ) (hpψ : ψ ^ p = 1) {n : ℤ} (hn : IsInnerAut (ψ ^ n)) : (p : ℤ) ∣ n := by
  have key : ∀ φ : MulAut L, IsInnerAut φ ↔ φ ∈ (MulAut.conj : L →* MulAut L).range := by
    intro φ
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, MulEquiv.ext fun t => by simp [MulAut.conj_apply, hg]⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, fun t => by simp [MulAut.conj_apply]⟩
  by_contra hdvd
  have hcop : IsCoprime (p : ℤ) n :=
    (Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hdvd
  obtain ⟨u, v, huv⟩ := hcop
  apply hψ
  rw [key]
  have : ψ = (ψ ^ n) ^ v := by
    calc ψ = ψ ^ ((p : ℤ) * u + n * v) := by
          rw [show (p : ℤ) * u + n * v = 1 by linarith, zpow_one]
      _ = (ψ ^ p) ^ u * (ψ ^ n) ^ v := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast]
      _ = (ψ ^ n) ^ v := by rw [hpψ, one_zpow, one_mul]
  rw [this]
  exact Subgroup.zpow_mem _ ((key _).1 hn) v

end Generic

section Main

variable {X : Type} [Group X] [Finite X] {p : ℕ} {B L : Subgroup X}

omit [Finite X] in
theorem mem_normalizer_map_subtype {T₀ : Subgroup ↥L} {e : ↥L}
    (he : e ∈ Subgroup.normalizer (T₀ : Set ↥L)) :
    (e : X) ∈ Subgroup.normalizer ((T₀.map L.subtype : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 he x).1 hx
    exact ⟨e * x * e⁻¹, this, by simp⟩
  · rintro ⟨x, hx, hxe⟩
    have h1 : e⁻¹ * x * e ∈ T₀ := by
      have := (Subgroup.mem_normalizer_iff.1 he (e⁻¹ * x * e)).2
      simpa using this (by simpa [mul_assoc] using hx)
    refine ⟨e⁻¹ * x * e, h1, ?_⟩
    have := congrArg (fun z : X => (e : X)⁻¹ * z * (e : X)) hxe
    simpa [mul_assoc] using this

omit [Finite X] in
theorem i112_mem_normalizer_map {y : ↥(i112A B L)} {T₀ : Subgroup ↥L}
    (h : T₀.map (i112Act B L y).toMonoidHom = T₀) :
    (y : X) ∈ Subgroup.normalizer ((T₀.map L.subtype : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h'
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨i112Act B L y t, ?_, rfl⟩
    rw [← h]
    exact Subgroup.mem_map_of_mem _ ht
  · rintro ⟨t₁, ht₁, hxy⟩
    have : t₁ ∈ T₀.map (i112Act B L y).toMonoidHom := by rw [h]; exact ht₁
    obtain ⟨t₀, ht₀, rfl⟩ := this
    refine ⟨t₀, ht₀, ?_⟩
    have h3 : (y : X) * (t₀ : X) * (y : X)⁻¹ = (y : X) * h' * (y : X)⁻¹ := hxy
    exact (by simpa using h3 : (t₀ : X) = h')

omit [Finite X] in
theorem exists_gLBConj_of_orbit (k : ↥(i112Orbit B L)) :
    ∃ g : X, g ∈ B ∧ (k : Subgroup X) = GLBConj g L :=
  mem_i112Orbit.1 k.2

theorem i112_inf_Bc_le (hp : p.Prime) (hB : IsElemAbelian p B) (hL : IsComponentOf L ⊤)
    {y : ↥(i112A B L)} (hy : ¬ IsInnerAut (i112Act B L y)) {F₀ : Subgroup X}
    (hF₀ : F₀ ≤ i112J B L) (hc : ∀ f ∈ F₀, f * (y : X) = (y : X) * f) :
    (F₀ ⊔ Subgroup.zpowers (y : X)) ⊓ i112Bc B L ≤ F₀ := by
  intro x hx
  obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.1 hx
  have hcz : ∀ f ∈ F₀, ∀ b ∈ Subgroup.zpowers (y : X), f * b = b * f := by
    intro f hf b hb
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hc f hf : Commute f (y : X)) z).eq
  obtain ⟨f, hf, b, hb, rfl⟩ := (mem_sup_iff_of_commute hcz).1 hxA
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have hyp : (y : X) ^ p = 1 := hB.2 y (i112A_le_B y.2)
  obtain ⟨l, hl, hlt⟩ := i112_exists_inner_of_mem_J hL (inv_mem (hF₀ hf))
  have hinner : IsInnerAut ((i112Act B L y) ^ n) := by
    refine ⟨⟨l, hl⟩, fun t => Subtype.ext ?_⟩
    have hz : (i112Act B L y) ^ n = i112Act B L (y ^ n) := (map_zpow _ y n).symm
    rw [hz, i112Act_apply]
    simp only [Subgroup.coe_zpow, InvMemClass.coe_inv]
    have hxt : (t : X) * (f * (y : X) ^ n) = (f * (y : X) ^ n) * t :=
      Subgroup.mem_centralizer_iff.1 hxC.2 t (i112_orbit_le_J (M := L) i112_self_mem_orbit t.2)
    have h1 : (f * (y : X) ^ n) * t * (f * (y : X) ^ n)⁻¹ = t := by
      rw [← hxt]; group
    have h2 : (y : X) ^ n * t * ((y : X) ^ n)⁻¹ =
        f⁻¹ * ((f * (y : X) ^ n) * t * (f * (y : X) ^ n)⁻¹) * f := by group
    rw [h2, h1]
    have := hlt t t.2
    simpa using this
  have hpψ : (i112Act B L y) ^ p = 1 := by
    rw [← map_pow]
    have : y ^ p = 1 := Subtype.ext hyp
    rw [this, map_one]
  have hdvd := dvd_of_isInnerAut_zpow hp hy hpψ hinner
  obtain ⟨k, hk⟩ := hdvd
  have : (y : X) ^ n = 1 := by
    rw [hk, zpow_mul, zpow_natCast, hyp, one_zpow]
  rw [this, mul_one]
  exact hf

omit [Finite X] in
theorem i112_commute_of_fixed {y : ↥(i112A B L)} {E₀ : Subgroup ↥L}
    (h : ∀ e ∈ E₀, i112Act B L y e = e) :
    ∀ x ∈ E₀.map L.subtype, x * (y : X) = (y : X) * x := by
  rintro _ ⟨e, he, rfl⟩
  have := congrArg (fun t : ↥L => (t : X)) (h e he)
  simp only [i112Act_apply] at this
  exact (mul_inv_eq_iff_eq_mul.1 this).symm

omit [Finite X] in
theorem i112_commute_conj {y : X} (hB : IsElemAbelian p B) (hy : y ∈ B) {E₀ : Subgroup X}
    (hE : ∀ x ∈ E₀, x * y = y * x) {g : X} (hg : g ∈ B) :
    ∀ x ∈ GLBConj g E₀, x * y = y * x := by
  intro x hx
  rw [mem_gLBConj] at hx
  have hgy : Commute g y := i116pI_comm hB hg hy
  have hx' : Commute (g * x * g⁻¹) y := hE _ hx
  have := (hgy.inv_left.mul_left hx').mul_left hgy
  have hxe : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [hxe] at this
  exact this.eq

theorem i112_iSupIndep_of_card_centre [Fintype ↥(i112Orbit B L)] (hL : IsComponentOf L ⊤)
    (h : Nat.card ↥(i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) =
      ∏ k : ↥(i112Orbit B L), Nat.card ↥(centreIn (k : Subgroup X))) :
    iSupIndep (i112Fam B L) := by
  classical
  have hc := i112_commFam (B := B) hL
  have h' : Nat.card (centreIn (⨆ i, i112Fam B L i)) =
      ∏ i, Nat.card (centreIn (i112Fam B L i)) := by
    rw [i112_iSup_fam]
    exact h
  exact (hc.card_centreIn_iSup_eq_prod_iff).1 h'

theorem i112_bonus (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥) (hB : IsElemAbelian p B)
    (hr : GLATwoLocalRank p X ≤ CFSG.Open.pRank p B) (hL : GLAPComponent p ⊤ L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X))
    (hind : iSupIndep (i112Fam B L)) (hfb : FieldBonus ↥L p (i112H B L)) :
    ∃ r a : ℕ, 1 ≤ r ∧ (Subgroup.normalizer (L : Set X)).relIndex B = p ^ r ∧
      Nat.card (i112H B L) = p ^ a ∧ CFSG.Open.pRank p (i112H B L) = a ∧
      GLATwoLocalRank p ↥L + p ^ r * CFSG.Open.pRank p (⊤ : Subgroup ↥L) + 1 ≤
      r + a + CFSG.Open.pRank p ((i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ B) +
        CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
  classical
  have : Fintype ↥(i112Orbit B L) := Fintype.ofFinite _
  have hp1 := hp.one_lt
  have hLc : IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  obtain ⟨r, a, hr1, hrel, hHa, hHr, hBrank⟩ := i112_pRank_formula hp hB hnL
  refine ⟨r, a, hr1, hrel, hHa, hHr, ?_⟩
  obtain ⟨ψ, hψH, hψn, T₀, hT₀, hT₀2, hT₀m, E₁₀, E₂₀, hE₁a, hE₂a, hE₁N, hE₁c, hE₂c, hE₁f,
    hE₂f⟩ := hfb
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hψH
  have hyB : (y : X) ∈ B := i112A_le_B y.2
  set T : Subgroup X := T₀.map L.subtype with hTdef
  set E₁ : Subgroup X := E₁₀.map L.subtype with hE₁def
  set E₂ : Subgroup X := E₂₀.map L.subtype with hE₂def
  have hT : T ≠ ⊥ := fun h =>
    hT₀ ((Subgroup.map_eq_bot_iff_of_injective T₀ L.subtype_injective).1 h)
  have hT2 : IsPGroup 2 T := hT₀2.map _
  have hE₁a' : IsElemAbelian p E₁ := CFSG.SectionRank.isElemAbelian_map hE₁a _
  have hE₂a' : IsElemAbelian p E₂ := CFSG.SectionRank.isElemAbelian_map hE₂a _
  have hE₁c' : Nat.card E₁ = p ^ GLATwoLocalRank p ↥L := by
    rw [hE₁def, Subgroup.card_map_of_injective L.subtype_injective, hE₁c]
  have hE₂c' : Nat.card E₂ = p ^ CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
    rw [hE₂def, Subgroup.card_map_of_injective L.subtype_injective, hE₂c]
  have hE₁L : E₁ ≤ L := Subgroup.map_subtype_le E₁₀
  have hE₂L : E₂ ≤ L := Subgroup.map_subtype_le E₂₀
  have hE₁N' : E₁ ≤ Subgroup.normalizer (T : Set X) := by
    rintro _ ⟨e, he, rfl⟩
    exact mem_normalizer_map_subtype (hE₁N he)
  have hyN : (y : X) ∈ Subgroup.normalizer (T : Set X) := i112_mem_normalizer_map hT₀m
  have hyE₁ : ∀ x ∈ E₁, x * (y : X) = (y : X) * x := i112_commute_of_fixed hE₁f
  have hyE₂ : ∀ x ∈ E₂, x * (y : X) = (y : X) * x := i112_commute_of_fixed hE₂f
  have hg : ∀ k : ↥(i112Orbit B L), ∃ g : X, g ∈ B ∧ (k : Subgroup X) = GLBConj g L :=
    exists_gLBConj_of_orbit
  choose g hgB hgk using hg
  let k₀ : ↥(i112Orbit B L) := ⟨L, i112_self_mem_orbit⟩
  let E : ↥(i112Orbit B L) → Subgroup X := fun k => if k = k₀ then E₁ else GLBConj (g k) E₂
  let e : ↥(i112Orbit B L) → ℕ := fun k =>
    if k = k₀ then GLATwoLocalRank p ↥L else CFSG.Open.pRank p (⊤ : Subgroup ↥L)
  have hEL : ∀ k, E k ≤ i112Fam B L k := by
    intro k
    by_cases hk : k = k₀
    · simp only [E, hk, ↓reduceIte]
      exact hE₁L
    · simp only [E, hk, ↓reduceIte]
      show _ ≤ (k : Subgroup X)
      rw [hgk k]
      exact gLBConj_mono _ hE₂L
  have hEa : ∀ k, IsElemAbelian p (E k) := by
    intro k
    by_cases hk : k = k₀
    · simp only [E, hk, ↓reduceIte]
      exact hE₁a'
    · simp only [E, hk, ↓reduceIte]
      exact CFSG.SectionRank.isElemAbelian_map hE₂a' _
  have hEc : ∀ k, Nat.card (E k) = p ^ e k := by
    intro k
    by_cases hk : k = k₀
    · simp only [E, e, hk, ↓reduceIte]
      exact hE₁c'
    · simp only [E, e, hk, ↓reduceIte]
      rw [← hE₂c']
      exact Subgroup.card_map_of_injective (MulAut.conj (g k)⁻¹).injective
  have hcomm : CommFam (i112Fam B L) := i112_commFam hLc
  have hEy : ∀ k, ∀ x ∈ E k, x * (y : X) = (y : X) * x := by
    intro k
    by_cases hk : k = k₀
    · simp only [E, hk, ↓reduceIte]
      exact hyE₁
    · simp only [E, hk, ↓reduceIte]
      exact i112_commute_conj hB hyB hyE₂ (hgB k)
  obtain ⟨hF₀a, hF₀card⟩ := hcomm.isElemAbelian_card_iSup_of_iSupIndep hind E hEL hEa hEc
  set F₀ : Subgroup X := ⨆ k, E k with hF₀def
  have hJcent_T : Subgroup.centralizer (i112J B L : Set X) ≤ Subgroup.centralizer (T : Set X) :=
    Subgroup.centralizer_le (fun x hx =>
      i112_orbit_le_J (M := L) i112_self_mem_orbit ((Subgroup.map_subtype_le T₀) hx))
  have hF₀J : F₀ ≤ i112J B L :=
    iSup_le fun k => (hEL k).trans (i112_orbit_le_J k.2)
  have hF₀N : F₀ ≤ Subgroup.normalizer (T : Set X) := by
    refine iSup_le fun k => ?_
    by_cases hk : k = k₀
    · simp only [E, hk, ↓reduceIte]
      exact hE₁N'
    · refine (hEL k).trans ?_
      have hkk : (k : Subgroup X) ≤ Subgroup.centralizer (L : Set X) :=
        hcomm.le_centralizer (i := k₀) hk
      exact hkk.trans ((Subgroup.centralizer_le (Subgroup.map_subtype_le T₀)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hF₀y : ∀ f ∈ F₀, f * (y : X) = (y : X) * f := by
    have hle : F₀ ≤ Subgroup.centralizer ({(y : X)} : Set X) := by
      refine iSup_le fun k x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hEy k x hx
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hf)
  have hyne : ¬ IsInnerAut (i112Act B L y) := hψn
  have hyp : (y : X) ^ p = 1 := hB.2 y hyB
  have hzp : IsElemAbelian p (Subgroup.zpowers (y : X)) := by
    refine isElemAbelian_of_forall (fun a ha b hb => ?_) (fun x hx => ?_)
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow_self (y : X) i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]
  have hA'a : IsElemAbelian p (F₀ ⊔ Subgroup.zpowers (y : X)) :=
    isElemAbelian_sup_of_commute hF₀a hzp (fun f hf b hb => by
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (hF₀y f hf : Commute f (y : X)) z).eq)
  have hA'card : Nat.card ↥(F₀ ⊔ Subgroup.zpowers (y : X)) = p ^ (∑ k, e k + 1) := by
    rw [i112_card_sup_zpowers hp hB hLc hyne hF₀J hF₀y, hF₀card, pow_succ, mul_comm]
  have hA'N : F₀ ⊔ Subgroup.zpowers (y : X) ≤ Subgroup.normalizer (T : Set X) :=
    sup_le hF₀N (Subgroup.zpowers_le.2 hyN)
  have hBc : IsElemAbelian p (i112Bc B L) := isElemAbelian_of_le hB i112Bc_le_B
  obtain ⟨b, hb⟩ := exists_card_eq_of_isElemAbelian hp hBc
  have hBcJ : i112Bc B L ≤ Subgroup.centralizer (i112J B L : Set X) := inf_le_right
  have hA'cent : F₀ ⊔ Subgroup.zpowers (y : X) ≤ Subgroup.centralizer (i112Bc B L : Set X) := by
    refine sup_le (fun f hf => ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_iff.1 (hBcJ hc) f (hF₀J hf)).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact i116pI_comm hB (i112Bc_le_B hc) hyB
  have hcomm' : ∀ x ∈ F₀ ⊔ Subgroup.zpowers (y : X), ∀ c ∈ i112Bc B L, x * c = c * x :=
    fun x hx c hc => (Subgroup.mem_centralizer_iff.1 (hA'cent hx) c hc).symm
  have hW : (F₀ ⊔ Subgroup.zpowers (y : X)) ⊓ i112Bc B L ≤
      (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ B := by
    intro x hx
    have hxF := i112_inf_Bc_le hp hB hLc hyne hF₀J hF₀y hx
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hF₀J hxF, hBcJ (Subgroup.mem_inf.1 hx).2⟩,
      i112Bc_le_B (Subgroup.mem_inf.1 hx).2⟩
  have hN : (F₀ ⊔ Subgroup.zpowers (y : X)) ⊔ i112Bc B L ≤ Subgroup.normalizer (T : Set X) :=
    sup_le hA'N (hBcJ.trans (hJcent_T.trans (Subgroup.centralizer_le_normalizer _)))
  have hcomb := rank_combine hp hT hT2 hA'a hBc hcomm' hW le_rfl hN hA'card hb
  have hbrank : CFSG.Open.pRank p (i112Bc B L) = b := pRank_eq_of_card hp1 hBc hb
  have hsum := sum_ite_add k₀ (GLATwoLocalRank p ↥L) (CFSG.Open.pRank p (⊤ : Subgroup ↥L))
  have hcard : Fintype.card ↥(i112Orbit B L) = p ^ r := by
    rw [← Nat.card_eq_fintype_card, i112_natCard_orbit, hrel]
  rw [hcard] at hsum
  have hsum' : ∑ k, e k + CFSG.Open.pRank p (⊤ : Subgroup ↥L) =
      GLATwoLocalRank p ↥L + p ^ r * CFSG.Open.pRank p (⊤ : Subgroup ↥L) := hsum
  omega

end Main

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance

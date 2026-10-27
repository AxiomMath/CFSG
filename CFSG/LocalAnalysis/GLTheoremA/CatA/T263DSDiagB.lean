module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSDiagA
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiCover
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal

section Y

variable {Y : Type} [Group Y] [Finite Y]

theorem t263_mem_normalizer_diagK_of {E J : Subgroup Y} {g : Y}
    (hgJ : g ∈ Subgroup.normalizer (J : Set Y)) (hgE : g ∈ Subgroup.centralizer (E : Set Y)) :
    g ∈ Subgroup.normalizer (diagK E J : Set Y) := by
  have key : ∀ g : Y, g ∈ Subgroup.normalizer (J : Set Y) → g ∈ Subgroup.centralizer (E : Set Y) →
      GLBConj g (diagK E J) ≤ diagK E J := by
    intro g hgJ hgE
    unfold diagK
    have h : GLBConj g (⨆ e ∈ E, GLBConj e J) = ⨆ e ∈ E, GLBConj g (GLBConj e J) := by
      unfold GLBConj
      simp only [Subgroup.map_iSup]
    rw [h]
    refine iSup₂_le fun e he => ?_
    have hcomm : e * g = g * e := Subgroup.mem_centralizer_iff.1 hgE e he
    have : GLBConj g (GLBConj e J) = GLBConj e J := by
      rw [t263_gLBConj_conj, hcomm, ← t263_gLBConj_conj, gLBConj_eq_of_mem_normalizer hgJ]
    rw [this]
    exact t263_conj_le_diagK he
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key g hgJ hgE) ?_
  have hgJ' : g⁻¹ ∈ Subgroup.normalizer (J : Set Y) := Subgroup.inv_mem _ hgJ
  have hgE' : g⁻¹ ∈ Subgroup.centralizer (E : Set Y) := Subgroup.inv_mem _ hgE
  have h := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono g (key g⁻¹ hgJ' hgE')
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h

theorem t263_gLBConj_layer_le {X : Subgroup Y} {g : Y} (hg : g ∈ Subgroup.normalizer (X : Set Y)) :
    GLBConj g (GLALayer X) ≤ GLALayer X := by
  unfold GLALayer
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  exact (Subgroup.map_le_iff_le_comap).1 (le_sSup (i25_isComponentOf_gLBConj hL hg))

theorem t263_mem_normalizer_layer {X : Subgroup Y} {g : Y} (hg : g ∈ Subgroup.normalizer (X : Set Y)) :
    g ∈ Subgroup.normalizer (GLALayer X : Set Y) := by
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  have h := t263_gLBConj_layer_le (X := X) (g := g⁻¹) (Subgroup.inv_mem _ hg)
  have hmem : g * n * g⁻¹ ∈ GLBConj g⁻¹ (GLALayer X) := by
    rw [mem_gLBConj]
    simpa [mul_assoc] using hn
  exact h hmem

structure T263DiagData (E J : Subgroup Y) (d : ↥J →* Y) : Prop where
  mem : ∀ x : ↥J, d x ∈ diagK E J ∧ d x ∈ Subgroup.centralizer (E : Set Y) ∧
    (x : Y)⁻¹ * d x ∈ Subgroup.centralizer (J : Set Y)
  ker : d.ker ≤ Subgroup.center ↥J
  quasi : CFSG.Open.IsQuasisimple ↥d.range
  sub : IsSubnormal d.range (Subgroup.centralizer (E : Set Y))
  layer : GLALayer (diagK E J ⊓ Subgroup.centralizer (E : Set Y)) = d.range

theorem t263_diag_data {p : ℕ} {E J : Subgroup Y} (hE : IsElemAbelian p E) (hJ : IsComponentOf J ⊤)
    (hfree : ∀ e ∈ E, e ≠ 1 → GLBConj e J ≠ J) : ∃ d : ↥J →* Y, T263DiagData E J d := by
  obtain ⟨d, h1, h2, h3, h4, h5⟩ := t263_diag_core hE hJ hfree
  exact ⟨d, ⟨h1, h2, h3, h4, h5⟩⟩

theorem T263DiagData.mem_normalizer {E J : Subgroup Y} {d : ↥J →* Y} (hd : T263DiagData E J d) {g : Y}
    (hgK : g ∈ Subgroup.normalizer (diagK E J : Set Y)) (hgE : g ∈ Subgroup.centralizer (E : Set Y)) :
    g ∈ Subgroup.normalizer (d.range : Set Y) := by
  have hX : g ∈ Subgroup.normalizer ((diagK E J ⊓ Subgroup.centralizer (E : Set Y) : Subgroup Y) : Set Y) :=
    CFSG.LocalAnalysis.GLTheoremB.mem_normalizer_inf hgK (Subgroup.le_normalizer hgE)
  have := t263_mem_normalizer_layer hX
  rwa [hd.layer] at this

theorem T263DiagData.le_normalizer {p : ℕ} {E J : Subgroup Y} {d : ↥J →* Y} (hd : T263DiagData E J d)
    (hE : IsElemAbelian p E) : E ≤ Subgroup.normalizer (d.range : Set Y) := fun g hg =>
  hd.mem_normalizer (t263_mem_normalizer_diagK hg)
    (Subgroup.mem_centralizer_iff.2 fun h hh => isElemAbelian_commute hE hh hg)

theorem t263_eq_bot_of_pGroup_coprime {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {N : Subgroup G} (hN : IsPGroup p ↥N) (hc : Nat.Coprime p (Nat.card ↥N)) : N = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  rw [hn] at hc
  have hn0 : n = 0 := by
    by_contra h
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hc (dvd_pow_self p h))
  rw [hn0, pow_zero] at hn
  exact Subgroup.eq_bot_of_card_eq N hn

theorem t263_centerQuot_nonempty {G H : Type*} [Group G] [Group H] [Group.IsPerfect G] (φ : G →* H)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G) :
    Nonempty ((G ⧸ Subgroup.center G) ≃* (H ⧸ Subgroup.center H)) := by
  have hc := CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel φ hφ hker
  refine ⟨MulEquiv.ofBijective (QuotientGroup.map (Subgroup.center G) (Subgroup.center H) φ hc.ge) ⟨?_, ?_⟩⟩
  · refine (injective_iff_map_eq_one _).2 fun a ha => ?_
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    rw [QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at ha
    rw [QuotientGroup.eq_one_iff, ← hc]
    exact ha
  · intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, rfl⟩ := hφ h
    exact ⟨QuotientGroup.mk g, by simp [QuotientGroup.map_mk]⟩

theorem T263DiagData.center_eq {E J : Subgroup Y} {d : ↥J →* Y} (hd : T263DiagData E J d)
    (hJq : CFSG.Open.IsQuasisimple ↥J) :
    Subgroup.center ↥d.range = (Subgroup.center ↥J).map d.rangeRestrict := by
  haveI : Group.IsPerfect ↥J := ⟨hJq.1⟩
  refine (CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel d.rangeRestrict
    d.rangeRestrict_surjective ?_).symm
  rw [MonoidHom.ker_rangeRestrict]
  exact hd.ker

theorem T263DiagData.centerQuot_nonempty {E J : Subgroup Y} {d : ↥J →* Y} (hd : T263DiagData E J d)
    (hJq : CFSG.Open.IsQuasisimple ↥J) :
    Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* (↥d.range ⧸ Subgroup.center ↥d.range)) := by
  haveI : Group.IsPerfect ↥J := ⟨hJq.1⟩
  refine t263_centerQuot_nonempty d.rangeRestrict d.rangeRestrict_surjective ?_
  rw [MonoidHom.ker_rangeRestrict]
  exact hd.ker

theorem T263DiagData.isPGroup_center {p : ℕ} (hp : p.Prime) {E J : Subgroup Y} {d : ↥J →* Y}
    (hd : T263DiagData E J d) (hJq : CFSG.Open.IsQuasisimple ↥J) (hcore : GLAPPrimeCore p ↥J = ⊥) :
    IsPGroup p ↥(Subgroup.center ↥d.range) := by
  have hZ := isPGroup_center_of_pPrimeCore_eq_bot hp hcore
  rw [hd.center_eq hJq]
  exact hZ.map d.rangeRestrict

theorem T263DiagData.core_eq_bot {p : ℕ} (hp : p.Prime) {E J : Subgroup Y} {d : ↥J →* Y}
    (hd : T263DiagData E J d) (hJq : CFSG.Open.IsQuasisimple ↥J) (hcore : GLAPPrimeCore p ↥J = ⊥)
    (hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) : GLAPPrimeCore p ↥d.range = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hRcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥d.range)) := CFSG.pPrimeCore_coprime_card
  have hpΔ : p ∣ Nat.card ↥d.range := by
    obtain ⟨e⟩ := hd.centerQuot_nonempty hJq
    have h1 : p ∣ Nat.card (↥d.range ⧸ Subgroup.center ↥d.range) := by
      rwa [← Nat.card_congr e.toEquiv]
    exact h1.trans (Subgroup.card_quotient_dvd_card _)
  have hne : GLAPPrimeCore p ↥d.range ≠ ⊤ := by
    intro h
    have hc : Nat.card (GLAPPrimeCore p ↥d.range) = Nat.card ↥d.range := by
      rw [h, Subgroup.card_top]
    rw [hc] at hRcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hRcop hpΔ
  have hle : GLAPPrimeCore p ↥d.range ≤ Subgroup.center ↥d.range :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hd.quasi _ hne
  exact t263_eq_bot_of_pGroup_coprime hp ((hd.isPGroup_center hp hJq hcore).to_le hle) hRcop

theorem T263DiagData.equivariant {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E J : Subgroup Y} {d : ↥J →* Y}
    (hd : T263DiagData E J d) (hcore : GLAPPrimeCore p ↥J = ⊥) {g : Y}
    (hgJ : g ∈ Subgroup.normalizer (J : Set Y)) (hgE : g ∈ Subgroup.centralizer (E : Set Y))
    (y : ↥J) (k : ℕ) (hy : y ^ (2 ^ k) = 1) :
    d ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.1 hgJ _).1 y.2⟩ = g * d y * g⁻¹ := by
  classical
  set y₁ : ↥J := ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.1 hgJ _).1 y.2⟩ with hy₁
  have hΔ : g ∈ Subgroup.normalizer (d.range : Set Y) :=
    hd.mem_normalizer (t263_mem_normalizer_diagK_of hgJ hgE) hgE
  have hδ : g * d y * g⁻¹ ∈ d.range := (Subgroup.mem_normalizer_iff.1 hΔ _).1 ⟨y, rfl⟩
  have hconjC : ∀ c ∈ Subgroup.centralizer (J : Set Y), g * c * g⁻¹ ∈ Subgroup.centralizer (J : Set Y) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro j hj
    have hj' : g⁻¹ * j * g ∈ J := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgJ) j).1 hj
      simpa using this
    have h1 := hc _ hj'
    calc j * (g * c * g⁻¹) = g * ((g⁻¹ * j * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * j * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * j := by group
  have hu1 : (y₁ : Y)⁻¹ * d y₁ ∈ Subgroup.centralizer (J : Set Y) := (hd.mem y₁).2.2
  have hu2 : (y₁ : Y)⁻¹ * (g * d y * g⁻¹) ∈ Subgroup.centralizer (J : Set Y) := by
    have h1 := hconjC _ (hd.mem y).2.2
    have e : (y₁ : Y)⁻¹ * (g * d y * g⁻¹) = g * ((y : Y)⁻¹ * d y) * g⁻¹ := by
      simp only [hy₁]
      group
    rw [e]
    exact h1
  have hu : (d y₁)⁻¹ * (g * d y * g⁻¹) ∈ Subgroup.centralizer (J : Set Y) := by
    have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hu1) hu2
    have e : ((y₁ : Y)⁻¹ * d y₁)⁻¹ * ((y₁ : Y)⁻¹ * (g * d y * g⁻¹)) = (d y₁)⁻¹ * (g * d y * g⁻¹) := by
      group
    rwa [e] at h1
  have hmem : (d y₁)⁻¹ * (g * d y * g⁻¹) ∈ d.range :=
    d.range.mul_mem (d.range.inv_mem ⟨y₁, rfl⟩) hδ
  obtain ⟨z, hz⟩ := hmem
  have hzc : z ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    have h1 := Subgroup.mem_centralizer_iff.1 (hd.mem z).2.2 (t : Y) t.2
    have h2 := Subgroup.mem_centralizer_iff.1 hu (t : Y) t.2
    rw [← hz] at h2
    have hdz : d z = (z : Y) * ((z : Y)⁻¹ * d z) := by group
    have h3 : (t : Y) * (z : Y) * ((z : Y)⁻¹ * d z) = (z : Y) * (t : Y) * ((z : Y)⁻¹ * d z) := by
      calc (t : Y) * (z : Y) * ((z : Y)⁻¹ * d z) = (t : Y) * ((z : Y) * ((z : Y)⁻¹ * d z)) := by group
        _ = (t : Y) * d z := by rw [← hdz]
        _ = d z * (t : Y) := h2
        _ = (z : Y) * ((z : Y)⁻¹ * d z) * (t : Y) := by rw [← hdz]
        _ = (z : Y) * (((z : Y)⁻¹ * d z) * (t : Y)) := by group
        _ = (z : Y) * ((t : Y) * ((z : Y)⁻¹ * d z)) := by rw [h1]
        _ = (z : Y) * (t : Y) * ((z : Y)⁻¹ * d z) := by group
    exact mul_right_cancel h3
  have hZp : IsPGroup p ↥(Subgroup.center ↥J) := isPGroup_center_of_pPrimeCore_eq_bot hp hcore
  obtain ⟨a, ha⟩ := hZp ⟨z, hzc⟩
  have hza : z ^ (p ^ a) = 1 := congrArg Subtype.val ha
  have hup : (d z) ^ (p ^ a) = 1 := by rw [← map_pow, hza, map_one]
  have hcomm : Commute (d y₁) (d z) := by
    have := Subgroup.mem_center_iff.1 hzc y₁
    change d y₁ * d z = d z * d y₁
    rw [← map_mul, ← map_mul, this]
  have hy1 : y₁ ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    show (g * (y : Y) * g⁻¹) ^ (2 ^ k) = 1
    rw [conj_pow]
    have h1 : (y : Y) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hy
      simpa using this
    rw [h1]
    simp
  have hd1 : (d y₁) ^ (2 ^ k) = 1 := by rw [← map_pow, hy1, map_one]
  have hδ1 : (g * d y * g⁻¹) ^ (2 ^ k) = 1 := by
    rw [conj_pow, ← map_pow, hy, map_one]
    simp
  have hu2k : (d z) ^ (2 ^ k) = 1 := by
    have e : g * d y * g⁻¹ = d y₁ * d z := by rw [hz]; group
    rw [e, hcomm.mul_pow, hd1, one_mul] at hδ1
    exact hδ1
  have hcop : Nat.Coprime (2 ^ k) (p ^ a) :=
    Nat.Coprime.pow k a ((Nat.coprime_primes Nat.prime_two hp).2 hp2.symm)
  have hz1 : d z = 1 := by
    have := pow_gcd_eq_one.2 ⟨hu2k, hup⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have e : g * d y * g⁻¹ = d y₁ * d z := by rw [hz]; group
  rw [e, hz1, mul_one]

end Y

end CFSG.LocalAnalysis.GLTheoremA.T263

end

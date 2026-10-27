module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.Section2.CoprimeTools
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_isPGroup_of_card_eq {p : ℕ} (hp : p.Prime) {P Z : Subgroup G}
    (hP : IsPGroup p P) (hZ : Nat.card Z = p) (hPZ : P ≤ Subgroup.normalizer (Z : Set G)) :
    P ≤ Subgroup.centralizer (Z : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulDistribMulAction P Z := Subgroup.conjMulDistribMulActionOfLeNormalizer P Z hPZ
  have hmod := hP.card_modEq_card_fixedPoints Z
  rw [hZ] at hmod
  set F := MulAction.fixedPoints P Z with hF
  have hone : (1 : Z) ∈ F := fun g => smul_one g
  have hpos : 0 < Nat.card F := Nat.card_pos_iff.2 ⟨⟨⟨1, hone⟩⟩, inferInstance⟩
  have hdvd : p ∣ Nat.card F := by
    have h := hmod.symm
    exact (Nat.modEq_zero_iff_dvd.1 (h.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)))
  have hcF : Nat.card F = Nat.card Z := by
    have h1 : Nat.card F ≤ Nat.card Z := by
      rw [← Nat.card_univ (α := Z)]
      exact Nat.card_mono Set.finite_univ (Set.subset_univ _)
    have h2 : p ≤ Nat.card F := Nat.le_of_dvd hpos hdvd
    omega
  have hall : ∀ y : Z, y ∈ F := by
    by_contra h
    push_neg at h
    obtain ⟨y, hy⟩ := h
    have hss : F ⊂ Set.univ := Set.ssubset_univ_iff.2 fun hFu => hy (hFu ▸ Set.mem_univ y)
    have := Set.ncard_lt_ncard hss
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq] at this
    omega
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hfix := hall ⟨y, hy⟩ ⟨b, hb⟩
  have h := congrArg Subtype.val hfix
  change b * y * b⁻¹ = y at h
  calc y * b = b * y * b⁻¹ * b := by rw [h]
    _ = b * y := by group

theorem exists_sylow_self_normalized {p : ℕ} (hp : p.Prime) {S W : Subgroup G}
    (hS : IsPGroup p S) (hSW : S ≤ Subgroup.normalizer (W : Set G)) :
    ∃ P : Subgroup G, P ≤ W ∧ IsPGroup p P ∧ ¬ p ∣ P.relIndex W ∧
      S ≤ Subgroup.normalizer (P : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulDistribMulAction S W := Subgroup.conjMulDistribMulActionOfLeNormalizer S W hSW
  have hnot : ¬ p ∣ Nat.card (Sylow p W) := by
    intro hdvd
    have h1 := card_sylow_modEq_one p W
    have h2 : 1 % p = 0 := by
      have := (Nat.modEq_zero_iff_dvd.2 hdvd).symm.trans h1
      exact this.symm
    rw [Nat.one_mod_eq_zero_iff] at h2
    exact hp.one_lt.ne' h2
  obtain ⟨Q, hQ⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p W) hnot
  have hfix : ∀ t : S, t • Q = Q := fun t => MulAction.mem_fixedPoints.mp hQ t
  refine ⟨(Q : Subgroup W).map W.subtype, Subgroup.map_subtype_le _,
    Q.isPGroup'.map W.subtype, ?_, ?_⟩
  · rw [Subgroup.relIndex, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective W.subtype_injective]
    exact Q.not_dvd_index
  · have key : ∀ t : S, ∀ x : G, x ∈ (Q : Subgroup W).map W.subtype →
        (t : G) * x * (t : G)⁻¹ ∈ (Q : Subgroup W).map W.subtype := by
      intro t x hx
      obtain ⟨w, hwQ, rfl⟩ := hx
      have h1 : t • w ∈ ((t • Q : Sylow p W) : Subgroup W) := by
        rw [Sylow.pointwise_smul_def]
        exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨w, hwQ, rfl⟩
      rw [hfix t] at h1
      exact ⟨t • w, h1, rfl⟩
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact key ⟨s, hs⟩ y
    · intro hy
      have := key ⟨s, hs⟩⁻¹ _ hy
      simpa [mul_assoc] using this

theorem mk_mem_center_of_mem_centModSubgroup {p : ℕ} {L : Subgroup G} {z : G} (hzL : z ∈ L)
    (hz : z ∈ centModSubgroup p L) :
    (QuotientGroup.mk (⟨z, hzL⟩ : L) : PQuot p L) ∈ Subgroup.center (PQuot p L) := by
  rw [Subgroup.mem_center_iff]
  intro g
  induction g using QuotientGroup.induction_on with
  | H l =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hl : (l : G) ∈ L := l.2
    have h1 : ⁅(l : G)⁻¹, z⁆ ∈ GLAPPrimeCoreOf p L := hz.2 _ (L.inv_mem hl)
    have hzN : z ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
      normalizer_le_normalizer_glaPPrimeCoreOf p L (Subgroup.le_normalizer hzL)
    have h2 : z⁻¹ * ⁅(l : G)⁻¹, z⁆ * z⁻¹⁻¹ ∈ GLAPPrimeCoreOf p L :=
      (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hzN) _).1 h1
    have h3 : z⁻¹ * ⁅(l : G)⁻¹, z⁆ * z⁻¹⁻¹ = (((l * ⟨z, hzL⟩)⁻¹ * (⟨z, hzL⟩ * l) : L) : G) := by
      simp [commutatorElement_def, mul_assoc]
    rw [h3] at h2
    obtain ⟨y, hy, hyeq⟩ := h2
    rwa [Subtype.ext hyeq] at hy

theorem card_inf_centModSubgroup (p : ℕ) (L : Subgroup G) :
    Nat.card ↥(L ⊓ centModSubgroup p L) =
      Nat.card (GLAPPrimeCoreOf p L) * Nat.card (Subgroup.center (PQuot p L)) := by
  set N := GLAPPrimeCore p ↥L with hN
  set f := QuotientGroup.mk' N with hf
  have hfs : Function.Surjective f := QuotientGroup.mk'_surjective N
  set Zc := Subgroup.center (PQuot p L) with hZc
  have heq : (L ⊓ centModSubgroup p L).subgroupOf L = Zc.comap f := by
    ext l
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    constructor
    · rintro ⟨-, hl⟩
      exact mk_mem_center_of_mem_centModSubgroup l.2 hl
    · intro hl
      refine ⟨l.2, Subgroup.le_normalizer l.2, fun m hm => ?_⟩
      have hc := (Subgroup.mem_center_iff.1 hl) (f ⟨m, hm⟩)
      have h1 : f ⁅(⟨m, hm⟩ : L), l⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hc
      rw [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩
  have hcard1 : Nat.card ↥(L ⊓ centModSubgroup p L) = Nat.card ↥(Zc.comap f) := by
    rw [← heq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  have h2 := (Zc.comap f).card_mul_index
  rw [Subgroup.index_comap_of_surjective Zc hfs] at h2
  have h3 := Zc.card_mul_index
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h5 : Nat.card N = Nat.card (GLAPPrimeCoreOf p L) :=
    (Subgroup.card_map_of_injective L.subtype_injective).symm
  have hidx : 0 < Zc.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [hcard1, h5.symm]
  have : Nat.card ↥(Zc.comap f) * Zc.index = Nat.card N * Nat.card Zc * Zc.index := by
    rw [h2, h4, ← h3]
    ring
  exact Nat.eq_of_mul_eq_mul_right hidx this

theorem normalizer_le_normalizer_centModSubgroup (p : ℕ) (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (centModSubgroup p L : Set G) := by
  have key : ∀ n ∈ Subgroup.normalizer (L : Set G), ∀ g ∈ centModSubgroup p L,
      n * g * n⁻¹ ∈ centModSubgroup p L := by
    intro n hn g hg
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hg.1) (Subgroup.inv_mem _ hn),
      fun l hl => ?_⟩
    have hl' : n⁻¹ * l * n⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) l).1 hl
    have h1 := hg.2 _ hl'
    have h2 := (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_glaPPrimeCoreOf p L hn) _).1 h1
    have h3 : n * ⁅n⁻¹ * l * n⁻¹⁻¹, g⁆ * n⁻¹ = ⁅l, n * g * n⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rwa [h3] at h2
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key n hn g, fun h => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ h
  simpa [mul_assoc] using this

theorem commutator_le_normalizer_of_stable {T B K : Subgroup G} (𝒦 : Set (Subgroup G))
    (hK : K ∈ 𝒦) (hT : ∀ t ∈ T, ∀ K' ∈ 𝒦, GLBConj t K' ∈ 𝒦)
    (hB : ∀ K' ∈ 𝒦, B ≤ Subgroup.normalizer (K' : Set G)) :
    ⁅T, B⁆ ≤ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.commutator_le]
  intro t ht b hb
  rw [mem_normalizer_iff_gLBConj_eq]
  have hconj : ∀ (g h : G) (H : Subgroup G), GLBConj (g * h) H = GLBConj h (GLBConj g H) := by
    intro g h H
    ext y
    simp only [mem_gLBConj, mul_inv_rev, mul_assoc]
  have hb' : ∀ K' ∈ 𝒦, GLBConj b K' = K' := fun K' hK' =>
    mem_normalizer_iff_gLBConj_eq.1 (hB K' hK' hb)
  have hbinv : ∀ K' ∈ 𝒦, GLBConj b⁻¹ K' = K' := fun K' hK' =>
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.inv_mem _ (hB K' hK' hb))
  have htK := hT t ht K hK
  have hinvt : GLBConj t⁻¹ (GLBConj t K) = K := by
    rw [← hconj, mul_inv_cancel, gLBConj_one]
  rw [commutatorElement_def, hconj, hconj, hconj, hb' _ htK, hinvt, hbinv K hK]

theorem isElemAbelian_sup_zpowers {p : ℕ} {B : Subgroup G} {z : G} (hB : IsElemAbelian p B)
    (hzB : B ≤ Subgroup.centralizer ({z} : Set G)) (hz : z ^ p = 1) :
    IsElemAbelian p (B ⊔ Subgroup.zpowers z) := by
  have hzc : ∀ b ∈ B, b * z = z * b := fun b hb =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hzB hb))
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer (B : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hzc b hb
  have hdec : ∀ x ∈ B ⊔ Subgroup.zpowers z, ∃ b ∈ B, ∃ k : ℤ, x = b * z ^ k := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left B _ hnorm] at hx
    obtain ⟨b, hb, y, hy, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨b, hb, k, rfl⟩
  have hcomm : ∀ b ∈ B, ∀ k : ℤ, Commute b (z ^ k) := fun b hb k =>
    Commute.zpow_right (hzc b hb) k
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨b₁, hb₁, k₁, hx⟩ := hdec x x.2
    obtain ⟨b₂, hb₂, k₂, hy⟩ := hdec y y.2
    change (x : G) * y = y * x
    rw [hx, hy]
    have h12 : b₁ * b₂ = b₂ * b₁ := isElemAbelian_commute hB hb₁ hb₂
    have c1 := hcomm b₂ hb₂ k₁
    have c2 := hcomm b₁ hb₁ k₂
    calc b₁ * z ^ k₁ * (b₂ * z ^ k₂) = b₁ * (z ^ k₁ * b₂) * z ^ k₂ := by group
      _ = b₁ * (b₂ * z ^ k₁) * z ^ k₂ := by rw [c1.eq]
      _ = (b₁ * b₂) * (z ^ k₁ * z ^ k₂) := by group
      _ = (b₂ * b₁) * (z ^ k₂ * z ^ k₁) := by rw [h12, ← zpow_add, ← zpow_add, add_comm]
      _ = b₂ * (b₁ * z ^ k₂) * z ^ k₁ := by group
      _ = b₂ * (z ^ k₂ * b₁) * z ^ k₁ := by rw [c2.eq]
      _ = b₂ * z ^ k₂ * (b₁ * z ^ k₁) := by group
  · obtain ⟨b, hb, k, rfl⟩ := hdec x hx
    rw [(hcomm b hb k).mul_pow, hB.2 b hb, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hz, one_zpow]


@[expose] def cosetStab (p : ℕ) (L : Subgroup G) (z : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (L : Set G) ∧ g * z * g⁻¹ * z⁻¹ ∈ GLAPPrimeCoreOf p L}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hza⟩ ⟨hb, hzb⟩
    refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_glaPPrimeCoreOf p L ha) _).1 hzb
    have h2 := Subgroup.mul_mem _ h1 hza
    have h3 : a * (b * z * b⁻¹ * z⁻¹) * a⁻¹ * (a * z * a⁻¹ * z⁻¹) =
        a * b * z * (a * b)⁻¹ * z⁻¹ := by group
    rwa [h3] at h2
  inv_mem' := by
    rintro a ⟨ha, hza⟩
    refine ⟨Subgroup.inv_mem _ ha, ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_glaPPrimeCoreOf p L (Subgroup.inv_mem _ ha)) _).1
      (Subgroup.inv_mem _ hza)
    have h3 : a⁻¹ * (a * z * a⁻¹ * z⁻¹)⁻¹ * a⁻¹⁻¹ = a⁻¹ * z * a⁻¹⁻¹ * z⁻¹ := by group
    rwa [h3] at h1

theorem mem_cosetStab {p : ℕ} {L : Subgroup G} {z g : G} :
    g ∈ cosetStab p L z ↔
      g ∈ Subgroup.normalizer (L : Set G) ∧ g * z * g⁻¹ * z⁻¹ ∈ GLAPPrimeCoreOf p L :=
  Iff.rfl

theorem mem_normalizer_sup {A C : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at *
  unfold GLBConj at *
  rw [Subgroup.map_sup, hA, hC]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G}
    (h : ∀ y ∈ H, g * y * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : GLBConj g⁻¹ H ≤ H := by
    intro y hy
    rw [mem_gLBConj] at hy
    have := h _ hy
    simpa [mul_assoc] using this
  have hcard : Nat.card (GLBConj g⁻¹ H) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹⁻¹).injective
  have heq : GLBConj g⁻¹ H = H := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have hmem : g⁻¹ ∈ Subgroup.normalizer (H : Set G) := mem_normalizer_iff_gLBConj_eq.2 heq
  simpa using Subgroup.inv_mem _ hmem

theorem lemma48 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hB : GLAIsBmax p B) (hx : IsEssential p B x)
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L)
    (hZ : Nat.card (Subgroup.center (PQuot p L)) = p)
    (hinv : ∀ K : Subgroup G, GLAPComponent p (Subgroup.centralizer ({x} : Set G)) K →
      Nonempty (PQuot p K ≃* PQuot p L) → B ≤ Subgroup.normalizer (K : Set G)) :
    ∃ z ∈ B, ∃ hzL : z ∈ L, orderOf z = p ∧
      (QuotientGroup.mk (⟨z, hzL⟩ : L) : PQuot p L) ∈ Subgroup.center (PQuot p L) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Cx := Subgroup.centralizer ({x} : Set G) with hCx
  set O := GLAPPrimeCoreOf p L with hO
  set Z₀ := L ⊓ centModSubgroup p L with hZ₀def
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := hinv L hL ⟨MulEquiv.refl _⟩
  have hBpg : IsPGroup p B := GLAIsBmax.isPGroup hB
  obtain ⟨hxB, -, T, hTCx, hT2, hBT, hTB, -⟩ := hx
  have hLCx : L ≤ Cx := hL.1
  have hNZ₀ : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Z₀ : Set G) := by
    intro n hn
    have h1 := normalizer_le_normalizer_centModSubgroup p L hn
    rw [Subgroup.mem_normalizer_iff] at hn h1 ⊢
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hn h, h1 h]
  obtain ⟨P, hPZ₀, hPp, hPidx, hBP⟩ := exists_sylow_self_normalized hp hBpg (hBL.trans hNZ₀)
  have hcardZ₀ : Nat.card Z₀ = Nat.card O * p := by
    rw [hZ₀def, card_inf_centModSubgroup, hZ]
  have hOp : ¬ p ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp L
  have hPcard : Nat.card P = p := by
    obtain ⟨a, ha⟩ := hPp.exists_card_eq
    have hmul : Nat.card P * P.relIndex Z₀ = Nat.card Z₀ := by
      have h := Subgroup.relIndex_mul_card (H := P) (K := Z₀)
      rw [inf_eq_left.mpr hPZ₀] at h
      rw [mul_comm]
      exact h
    rw [ha, hcardZ₀] at hmul
    have ha1 : 1 ≤ a := by
      by_contra h0
      push_neg at h0
      interval_cases a
      rw [pow_zero, one_mul] at hmul
      exact hPidx (hmul ▸ dvd_mul_left p _)
    have ha2 : a ≤ 1 := by
      by_contra h2
      push_neg at h2
      have h3 : p * p ∣ Nat.card O * p := by
        rw [← hmul, ← pow_two]
        exact Dvd.dvd.mul_right (pow_dvd_pow p h2) _
      exact hOp (Nat.dvd_of_mul_dvd_mul_right hp.pos h3)
    rw [ha, le_antisymm ha2 ha1, pow_one]
  obtain ⟨z, hzP, hz1⟩ : ∃ z ∈ P, z ≠ 1 := by
    by_contra h
    push_neg at h
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 h
    rw [this, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  have hzord : orderOf z = p := by
    have h1 : orderOf z ∣ p := hPcard ▸ Subgroup.orderOf_dvd_natCard P hzP
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  have hzZ₀ : z ∈ Z₀ := hPZ₀ hzP
  have hzL : z ∈ L := hzZ₀.1
  have hzC : z ∈ centModSubgroup p L := hzZ₀.2
  have hBcP := le_centralizer_of_isPGroup_of_card_eq hp hBpg hPcard hBP
  have hbz : ∀ b ∈ B, b * z = z * b := fun b hb =>
    (Subgroup.mem_centralizer_iff.1 (hBcP hb) z hzP).symm
  have hBcz : B ≤ Subgroup.centralizer ({z} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.2 (hbz b hb)
  have hOZ₀ : O ≤ Z₀ := by
    intro o ho
    have hoL : o ∈ L := Subgroup.map_subtype_le _ ho
    refine ⟨hoL, Subgroup.le_normalizer hoL, fun l hl => ?_⟩
    have hoN := (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_glaPPrimeCoreOf p L (Subgroup.le_normalizer hl)) o).1 ho
    have : ⁅l, o⁆ = (l * o * l⁻¹) * o⁻¹ := by simp [commutatorElement_def]
    rw [this]
    exact Subgroup.mul_mem _ hoN (Subgroup.inv_mem _ ho)
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.zpowers_le.2
      (normalizer_le_normalizer_glaPPrimeCoreOf p L (Subgroup.le_normalizer hzL))
  have hdisj : O ⊓ Subgroup.zpowers z = ⊥ := by
    rw [eq_bot_iff]
    intro y ⟨hyO, hyz⟩
    have h1 : Nat.card (O ⊓ Subgroup.zpowers z : Subgroup G) ∣ p := by
      rw [← hzord, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    have h2 : Nat.card (O ⊓ Subgroup.zpowers z : Subgroup G) ∣ Nat.card O :=
      Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card (O ⊓ Subgroup.zpowers z : Subgroup G) = 1 := by
      rcases (Nat.dvd_prime hp).1 h1 with h | h
      · exact h
      · exact absurd (h ▸ h2) hOp
    have := (Subgroup.card_eq_one).1 h3
    have hy : y ∈ (O ⊓ Subgroup.zpowers z : Subgroup G) := ⟨hyO, hyz⟩
    rw [this] at hy
    exact hy
  have hZ₀eq : Z₀ = O ⊔ Subgroup.zpowers z := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (sup_le hOZ₀ (Subgroup.zpowers_le.2 hzZ₀))
    have h1 := card_sup_mul_card_inf_of_le_normalizer hzN
    rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hzord] at h1
    rw [h1, hcardZ₀]
  set R := ⁅T, B⁆ with hRdef
  have hRT : R ≤ T := Subgroup.le_normalizer_iff_commutator_le_left.1 hBT
  have hR2 : IsPGroup 2 R := hT2.to_le hRT
  have hRCx : R ≤ Cx := hRT.trans hTCx
  have hBR : B ≤ Subgroup.normalizer (R : Set G) := Subgroup.normalizer_commutator_ge_right T B
  have hcop : Nat.Coprime (Nat.card B) (Nat.card T) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := hBpg.exists_card_eq
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    rw [hm, hn]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hsolv : Group.IsSolvable T := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := hT2.isNilpotent
    infer_instance
  have hRR : ⁅R, B⁆ = R := GL83.commutator_double_eq_self B T hBT hcop hsolv
  set 𝒦 : Set (Subgroup G) :=
    {K | GLAPComponent p Cx K ∧ Nonempty (PQuot p K ≃* PQuot p L)} with h𝒦
  have hT𝒦 : ∀ t ∈ T, ∀ K' ∈ 𝒦, GLBConj t K' ∈ 𝒦 := by
    rintro t ht K' ⟨hK'c, ⟨e⟩⟩
    have hCxconj : GLBConj t Cx = Cx :=
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hTCx ht))
    refine ⟨?_, ⟨(conjQuotEquiv p t K').symm.trans e⟩⟩
    have := glaPComponent_gLBConj hK'c t
    rwa [hCxconj] at this
  have hRL : R ≤ Subgroup.normalizer (L : Set G) :=
    commutator_le_normalizer_of_stable 𝒦 ⟨hL, ⟨MulEquiv.refl _⟩⟩ hT𝒦
      (fun K' hK' => hinv K' hK'.1 hK'.2)
  have hRS : R ≤ cosetStab p L z := by
    rw [← hRR, Subgroup.commutator_le]
    intro r hr b hb
    have hrN := hRL hr
    have hbN := hBL hb
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hbN)
      (Subgroup.inv_mem _ hrN)) (Subgroup.inv_mem _ hbN), ?_⟩
    set w := r⁻¹ * z * r with hw
    have hwZ₀ : w ∈ Z₀ := by
      have := (Subgroup.mem_normalizer_iff.1 (hNZ₀ (Subgroup.inv_mem _ hrN)) z).1 hzZ₀
      simpa [hw] using this
    rw [hZ₀eq, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left O _ hzN] at hwZ₀
    obtain ⟨o, ho, y, hy, hwy⟩ := Set.mem_mul.mp hwZ₀
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hbzk : b * z ^ k * b⁻¹ = z ^ k := by
      have := (Commute.zpow_right (hbz b hb) k).eq
      rw [this, mul_inv_cancel_right]
    have hbzb : b⁻¹ * z * b = z := by
      have := hbz b hb
      calc b⁻¹ * z * b = b⁻¹ * (z * b) := by group
        _ = b⁻¹ * (b * z) := by rw [this]
        _ = z := by group
    have hbo : b * o * b⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p L hbN) o).1 ho
    have hc : b * o * b⁻¹ * o⁻¹ ∈ O := Subgroup.mul_mem _ hbo (Subgroup.inv_mem _ ho)
    have hrc := (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p L hrN)
      (b * o * b⁻¹ * o⁻¹)).1 hc
    have hkey : ⁅r, b⁆ * z * ⁅r, b⁆⁻¹ * z⁻¹ = r * (b * o * b⁻¹ * o⁻¹) * r⁻¹ := by
      have hz' : z = r * (o * z ^ k) * r⁻¹ := by
        rw [hwy, hw]
        group
      have e1 : ⁅r, b⁆ * z * ⁅r, b⁆⁻¹ = r * (b * (o * z ^ k) * b⁻¹) * r⁻¹ := by
        calc ⁅r, b⁆ * z * ⁅r, b⁆⁻¹ = r * b * r⁻¹ * (b⁻¹ * z * b) * r * b⁻¹ * r⁻¹ := by
              simp only [commutatorElement_def]
              group
          _ = r * b * r⁻¹ * z * r * b⁻¹ * r⁻¹ := by rw [hbzb]
          _ = r * (b * (r⁻¹ * z * r) * b⁻¹) * r⁻¹ := by group
          _ = r * (b * (o * z ^ k) * b⁻¹) * r⁻¹ := by rw [← hw, hwy]
      have e2 : b * (o * z ^ k) * b⁻¹ = (b * o * b⁻¹ * o⁻¹) * (o * z ^ k) := by
        calc b * (o * z ^ k) * b⁻¹ = b * o * b⁻¹ * (b * z ^ k * b⁻¹) := by group
          _ = b * o * b⁻¹ * z ^ k := by rw [hbzk]
          _ = (b * o * b⁻¹ * o⁻¹) * (o * z ^ k) := by group
      rw [e1, e2]
      calc r * ((b * o * b⁻¹ * o⁻¹) * (o * z ^ k)) * r⁻¹ * z⁻¹
          = r * (b * o * b⁻¹ * o⁻¹) * r⁻¹ * (r * (o * z ^ k) * r⁻¹) * z⁻¹ := by group
        _ = r * (b * o * b⁻¹ * o⁻¹) * r⁻¹ * z * z⁻¹ := by rw [← hz']
        _ = r * (b * o * b⁻¹ * o⁻¹) * r⁻¹ := by group
    rw [hkey]
    exact hrc
  set OC := GLAPPrimeCoreOf p Cx with hOC
  have hOOC : O ≤ OC := glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1
  have hRN : R ≤ Subgroup.normalizer (OC : Set G) :=
    hRCx.trans (le_normalizer_glaPPrimeCoreOf p Cx)
  set H := OC ⊔ R with hH
  have hRp : ¬ p ∣ Nat.card R := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := hR2.exists_card_eq
    rw [hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    exact hp2 this
  have hHp : ¬ p ∣ Nat.card H :=
    not_dvd_card_sup_of_le_normalizer hp hRN (not_dvd_card_glaPPrimeCoreOf hp Cx) hRp
  set E := B ⊔ Subgroup.zpowers z with hEdef
  have hzp : z ^ p = 1 := hzord ▸ pow_orderOf_eq_one z
  have hE : IsElemAbelian p E := isElemAbelian_sup_zpowers hB.1 hBcz hzp
  have hEp : IsPGroup p E := isPGroup_of_isElemAbelian hE
  have hzCx : z ∈ Cx := hLCx hzL
  have hEH : E ≤ Subgroup.normalizer (H : Set G) := by
    apply sup_le
    · intro b hb
      exact mem_normalizer_sup (le_normalizer_glaPPrimeCoreOf p Cx (isElemAbelian_le_centralizer
        hB.1 hxB hb)) (hBR hb)
    · rw [Subgroup.zpowers_le]
      apply mem_normalizer_of_conj_mem
      have hzOC := le_normalizer_glaPPrimeCoreOf p Cx hzCx
      set K' := H.comap (MulAut.conj z).toMonoidHom with hK'
      have hmemK' : ∀ y, y ∈ K' ↔ z * y * z⁻¹ ∈ H := fun y => by
        simp [hK', MulAut.conj_apply]
      have hOCK : OC ≤ K' := fun y hy => (hmemK' y).2
        (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hzOC y).1 hy))
      have hRK : R ≤ K' := by
        intro y hy
        rw [hmemK']
        have hyS := hRS hy
        have h1 : z * y * z⁻¹ = (y * z * y⁻¹ * z⁻¹)⁻¹ * y := by group
        rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hOOC (Subgroup.inv_mem _ hyS.2)))
          (Subgroup.mem_sup_right hy)
      intro y hy
      exact (hmemK' y).1 (sup_le hOCK hRK hy)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S2, hS2⟩ := exists_sylow_normalized (r := 2) hEH hEp hHp
  set S := (S2 : Subgroup H).map H.subtype with hS
  have hSp : IsPGroup 2 S := S2.isPGroup'.map H.subtype
  have h2H : 2 ∣ Nat.card H := by
    obtain ⟨n, hn⟩ := hR2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hTB (Subgroup.card_eq_one.1 hn)
    have h1 : 2 ∣ Nat.card R := hn ▸ dvd_pow_self 2 hn0
    exact h1.trans (Subgroup.card_dvd_of_le le_sup_right)
  have hSne : S ≠ ⊥ := by
    intro h
    have h1 := S2.ne_bot_of_dvd_card h2H
    apply h1
    rw [hS] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 h
  have hEB : E = B := GLAIsBmax.eq_of_le hp hB le_sup_left hE hSne hSp hS2
  have hzB : z ∈ B := hEB ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  exact ⟨z, hzB, hzL, hzord, mk_mem_center_of_mem_centModSubgroup hzL hzC⟩

end CFSG.LocalAnalysis.GLTheoremA

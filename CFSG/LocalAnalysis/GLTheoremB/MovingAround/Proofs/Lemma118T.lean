module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118Parts

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open scoped Pointwise
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut barAut_mk)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)


namespace Lemma118T

variable {G : Type} [Group G] [Finite G]

structure TransportData (p n : ℕ) (K : Subgroup G) (a : G) (Q₁ Q₂ : Subgroup G) : Prop where
  Q₁K : Q₁ ≤ K
  Q₁ab : IsElemAbelian p Q₁
  Q₁rk : CFSG.Open.pRank p Q₁ = n / p
  Q₂ab : IsElemAbelian p Q₂
  Q₂C : Q₂ ≤ centBar p (Cg a) K
  Q₂max : ∀ R : Subgroup G, R ≤ centBar p (Cg a) K → IsElemAbelian p R →
    CFSG.Open.pRank p R ≤ CFSG.Open.pRank p Q₂
  aQ₂ : a ∈ Q₂
  comm : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x

@[expose] def Input10_5K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p n : ℕ), p.Prime → p ≠ 2 → ∀ K : Subgroup G,
    IsAltType n (barOf p K) → ∀ P : Subgroup G, IsSylowIn p K P →
      ∃! E : Subgroup G, E ≤ P ∧ IsElemAbelian p E ∧ CFSG.Open.pRank p E = n / p

@[expose] def Input24_1K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p n : ℕ), p.Prime → p ≠ 2 → ¬ p ∣ n → 2 ≤ n / p →
    ∀ K : Subgroup G, IsAltType n (barOf p K) → ∀ E : Subgroup G, E ≤ K → IsElemAbelian p E →
      CFSG.Open.pRank p E = n / p →
        (⨆ (X : Subgroup G) (_ : X ≤ E ∧ X ≠ ⊥), Subgroup.normalizer (X : Set G) ⊓ K) = K

@[expose] def Input118Local : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G) (K : Subgroup G),
    Cex117 G m p B M E A a K → ∀ (n : ℕ) (Q₁ Q₂ : Subgroup G),
      IsAltType n (barOf p K) → ¬ p ∣ n → TransportData p n K a Q₁ Q₂ →
        CFSG.Open.pRank p (Q₁ ⊔ Q₂) ≤ GLATwoLocalRank p G + 1 ∧
          (p = 3 → CFSG.Open.pRank 3 (Q₁ ⊔ Q₂) ≤ GLATwoLocalRank 3 G)

@[expose] def Lemma118Sub : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) (B M E A : Subgroup G) (a : G) (K : Subgroup G),
    Cex117 G m 3 B M E A a K → ∀ (n : ℕ) (Q₁ Q₂ : Subgroup G),
      IsAltType n (barOf 3 K) → ¬ 3 ∣ n → 3 ^ CFSG.Open.pRank 3 (E ⊓ A) < n →
        TransportData 3 n K a Q₁ Q₂ → CFSG.Open.pRank 3 (E ⊓ A) = 2 →
          CFSG.Open.pRank 3 (Q₁ ⊔ Q₂) = 4 → CFSG.Open.pRank 3 A ≤ 3


theorem pRank_eq_of_isElemAbelian_card {p : ℕ} [hp : Fact p.Prime] {R : Subgroup G}
    (hR : IsElemAbelian p R) {k : ℕ} (hk : Nat.card R = p ^ k) : CFSG.Open.pRank p R = k := by
  refine le_antisymm ?_ (CFSG.SectionRank.le_pRank hp.out.one_lt le_rfl hR hk)
  unfold CFSG.Open.pRank
  refine csSup_le ⟨k, R, le_rfl, hR, hk⟩ ?_
  rintro j ⟨E, hER, -, hEc⟩
  have hdvd : p ^ j ∣ p ^ k := by
    rw [← hEc, ← hk]
    exact Subgroup.card_dvd_of_le hER
  exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 hdvd

theorem pRank_gLBConj' {p : ℕ} (hp1 : 1 < p) (H : Subgroup G) (g : G) :
    CFSG.Open.pRank p (GLBConj g H) = CFSG.Open.pRank p H := by
  have hle : ∀ (H : Subgroup G) (g : G), CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (GLBConj g H) :=
    fun H g => CFSG.SectionRank.pRank_le_map hp1 (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective H
  refine le_antisymm ?_ (hle H g)
  have := hle (GLBConj g H) g⁻¹
  rwa [gLBConj_inv_gLBConj] at this

theorem glbCore_gLBConj_le' {p k : ℕ} (hp1 : 1 < p) (H : Subgroup G) (g : G) :
    GLBConj g (GLBCore p k H) ≤ GLBCore p k (GLBConj g H) := by
  have key : GLBCore p k H ≤ GLBConj g⁻¹ (GLBCore p k (GLBConj g H)) := by
    unfold GLBCore
    refine sSup_le fun N hN => ?_
    obtain ⟨Q, hQH, hkQ, rfl⟩ := hN
    have hQ' : GLBConj g Q ≤ GLBConj g H := gLBConj_mono g hQH
    have hrank : k ≤ CFSG.Open.pRank p (GLBConj g Q) := by
      rw [pRank_gLBConj' hp1]; exact hkQ
    have hle : Subgroup.normalizer ((GLBConj g Q : Subgroup G) : Set G) ≤
        GLBCore p k (GLBConj g H) := le_sSup ⟨GLBConj g Q, hQ', hrank, rfl⟩
    have heq : Subgroup.normalizer (Q : Set G) =
        GLBConj g⁻¹ (Subgroup.normalizer ((GLBConj g Q : Subgroup G) : Set G)) := by
      rw [gLBConj_normalizer, gLBConj_inv_gLBConj]
    rw [heq]
    exact gLBConj_mono g⁻¹ hle
  calc GLBConj g (GLBCore p k H) ≤ GLBConj g (GLBConj g⁻¹ (GLBCore p k (GLBConj g H))) :=
        gLBConj_mono g key
    _ = GLBCore p k (GLBConj g H) := gLBConj_gLBConj_inv g _

theorem centralizer_gLBConj_eq (a g : G) :
    GLBConj g (Subgroup.centralizer ({a} : Set G)) =
      Subgroup.centralizer ({g⁻¹ * a * g} : Set G) := by
  ext y
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * (g⁻¹ * a * g) = g⁻¹ * ((g * y * g⁻¹) * a) * g := by group
      _ = g⁻¹ * (a * (g * y * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * a * g * y := by group
  · intro h
    calc g * y * g⁻¹ * a = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * y) * g⁻¹ := by rw [h]
      _ = a * (g * y * g⁻¹) := by group

theorem conj_pow_eq (a g : G) (k : ℕ) : (g⁻¹ * a * g) ^ k = g⁻¹ * a ^ k * g := by
  have := (map_pow (MulAut.conj g⁻¹) a k).symm
  simpa only [MulAut.conj_apply, inv_inv] using this

theorem isAltType_barOf_gLBConj {n p : ℕ} (g : G) (K : Subgroup G)
    (hn : IsAltType n (barOf p K)) : IsAltType n (barOf p (GLBConj g K)) := by
  obtain ⟨e⟩ := hn
  exact ⟨(conjQuotEquiv p g K).symm.trans e⟩

theorem lemma118_P1_anchor_of_ranks {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {M E A : Subgroup G} (hEA : IsDDpStar p M E A)
    (hI31_6 : Input31_6) (hI31_9 : Input31_9)
    {D Q R : Subgroup G} (hD : inD p M D) (hQ : CFSG.Open.IsElemAbelian p Q) (hR : IsPGroup p R)
    (hQR : Q ≤ R) (hDR : D ≤ R)
    (hQs : p ^ (CFSG.Open.pRank p (E ⊓ A) - 1) ≤ CFSG.Open.pRank p Q)
    (hDs : p ^ (CFSG.Open.pRank p (E ⊓ A) - 1) ≤ CFSG.Open.pRank p D)
    (hcase : p = 3 → CFSG.Open.pRank p (E ⊓ A) = 2 →
      4 ≤ CFSG.Open.pRank p Q ∧ 4 ≤ CFSG.Open.pRank p D ∧
        (5 ≤ CFSG.Open.pRank p Q → 5 ≤ CFSG.Open.pRank p D) ∧
          (CFSG.Open.pRank p Q = 4 → CFSG.Open.pRank p A ≤ 3)) :
    ∃ H : Subgroup G, IsSCp p ⊤ H ∧ Q ≤ H ∧ inD p M H := by
  have hr2 : 2 ≤ CFSG.Open.pRank p (E ⊓ A) := hEA.1.2.2
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have hDab : CFSG.Open.IsElemAbelian p D := hD.1.1.2.1
  obtain ⟨HQ, hHQ, hQHQ⟩ := c104_exists_isSCp_top hQ
  refine ⟨HQ, hHQ, hQHQ, ?_⟩
  suffices hX : ∃ X : Subgroup G, X ≤ Q ∧ ∀ H : Subgroup G, IsSCp p ⊤ H → X ≤ H → inD p M H by
    obtain ⟨X, hXQ, hXP⟩ := hX
    exact hXP HQ hHQ (hXQ.trans hQHQ)
  by_cases hex : p = 3 ∧ CFSG.Open.pRank p (E ⊓ A) = 2
  ·
    obtain ⟨hp3', hr'⟩ := hex
    obtain ⟨-, -, hQ5, hQ4A⟩ := hcase hp3' hr'
    have hr3 : CFSG.Open.pRank p (E ⊓ A) + 1 = 3 := by omega
    by_cases hQ5' : 5 ≤ CFSG.Open.pRank p Q
    ·
      obtain ⟨X, hXQ, hXab, hXcard⟩ := exists_elemAb_sub_of_rank hQ (s := 5) hQ5'
      obtain ⟨Y, hYD, hYab, hYcard⟩ := exists_elemAb_sub_of_rank hDab (s := 5) (hQ5 hQ5')
      have hX5 : IsEkIn p 5 R X := ⟨hXQ.trans hQR, hXab, hXcard⟩
      have hY5 : IsEkIn p 5 R Y := ⟨hYD.trans hDR, hYab, hYcard⟩
      have kc : IsKConnectedIn p 3 ⊤ X Y :=
        kconn_mono ((hI31_6 G p hp.out hp2 R hR).1 X Y hX5 hY5)
      have kc' : IsKConnectedIn p (CFSG.Open.pRank p (E ⊓ A) + 1) ⊤ X Y := by
        rw [hr3]; exact kc
      have hYr' : 5 ≤ CFSG.Open.pRank p Y := rank_ge_of_card' hYab hYcard.ge
      exact ⟨X, hXQ, propagate_chain hEA kc' (base_of_le hEA hD hYD (by omega))⟩
    ·
      have hQ4eq : CFSG.Open.pRank p Q = 4 := by
        have := hcase hp3' hr'
        omega
      have hA3 : CFSG.Open.pRank p A ≤ 3 := hQ4A hQ4eq
      obtain ⟨X, hXQ, hXab, hXcard⟩ := exists_elemAb_sub_of_rank hQ (s := 4) (by omega)
      obtain ⟨C0, hC0D, hC0ab, hC0card⟩ := exists_elemAb_sub_of_rank hDab (s := 4)
        (by have := hcase hp3' hr'; omega)
      have hX4 : IsEkIn p 4 R X := ⟨hXQ.trans hQR, hXab, hXcard⟩
      have hC4 : IsEkIn p 4 R C0 := ⟨hC0D.trans hDR, hC0ab, hC0card⟩
      have hchain := input31_8_holds G p 4 hp.out (by norm_num) R hR C0 X hC4 hX4
      have hC0r : 4 ≤ CFSG.Open.pRank p C0 := rank_ge_of_card' hC0ab hC0card.ge
      have hP0 := base_of_le hEA hD hC0D (by omega)
      have hall : ∀ W : Subgroup G,
          Relation.ReflTransGen
            (fun U V : Subgroup G => IsEkIn p 4 R U ∧ IsEkIn p 4 R V ∧
              2 ≤ CFSG.Open.pRank p (U ⊓ V)) C0 W →
          ∀ H : Subgroup G, IsSCp p ⊤ H → W ≤ H → inD p M H := by
        intro W hW
        induction hW with
        | refl => exact hP0
        | @tail b c _ hbc ih =>
          exact chain_min_step hEA hr' hA3 hbc.1.2.1 (rank_ge_of_card' hbc.1.2.1 hbc.1.2.2.ge)
            (rank_ge_of_card' hbc.2.1.2.1 hbc.2.1.2.2.ge) hbc.2.2 ih
      exact ⟨X, hXQ, hall X hchain⟩
  ·
    have hs : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ p ^ (CFSG.Open.pRank p (E ⊓ A) - 1) :=
      succ_le_pow_pred hp3 hr2
    obtain ⟨X, hXQ, hXab, hXcard⟩ := exists_elemAb_sub_of_rank hQ (s := p ^ (CFSG.Open.pRank p (E ⊓ A) - 1)) hQs
    obtain ⟨Y, hYD, hYab, hYcard⟩ := exists_elemAb_sub_of_rank hDab (s := p ^ (CFSG.Open.pRank p (E ⊓ A) - 1)) hDs
    have hX' : IsEkIn p (p ^ (CFSG.Open.pRank p (E ⊓ A) - 1)) R X := ⟨hXQ.trans hQR, hXab, hXcard⟩
    have hY' : IsEkIn p (p ^ (CFSG.Open.pRank p (E ⊓ A) - 1)) R Y := ⟨hYD.trans hDR, hYab, hYcard⟩
    have kc := hI31_9 G p (CFSG.Open.pRank p (E ⊓ A)) hp.out hp2 hr2 hex R hR X Y hX' hY'
    have hYr : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p Y :=
      hs.trans (rank_ge_of_card' hYab hYcard.ge)
    exact ⟨X, hXQ, propagate_chain hEA (kconn_mono kc) (base_of_le hEA hD hYD hYr)⟩

theorem lemma118_P1_claim_of_ranks {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {M E A : Subgroup G} (hEA : IsDDpStar p M E A)
    (hI31_6 : Input31_6) (hI31_9 : Input31_9)
    {D Q R : Subgroup G} (hD : inD p M D) (hQ : CFSG.Open.IsElemAbelian p Q) (hR : IsPGroup p R)
    (hQR : Q ≤ R) (hDR : D ≤ R)
    (hQs : p ^ (CFSG.Open.pRank p (E ⊓ A) - 1) ≤ CFSG.Open.pRank p Q)
    (hDs : p ^ (CFSG.Open.pRank p (E ⊓ A) - 1) ≤ CFSG.Open.pRank p D)
    (hcase : p = 3 → CFSG.Open.pRank p (E ⊓ A) = 2 →
      4 ≤ CFSG.Open.pRank p Q ∧ 4 ≤ CFSG.Open.pRank p D ∧
        (5 ≤ CFSG.Open.pRank p Q → 5 ≤ CFSG.Open.pRank p D) ∧
          (CFSG.Open.pRank p Q = 4 → CFSG.Open.pRank p A ≤ 3)) :
    GLBCore p 2 Q ≤ M := by
  obtain ⟨H, -, hQH, hHD⟩ :=
    lemma118_P1_anchor_of_ranks hp2 hEA hI31_6 hI31_9 hD hQ hR hQR hDR hQs hDs hcase
  exact (glbCore_mono hQH).trans hHD.2.clause_d



variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_pPrimeCoreOf {p : ℕ} [hp : Fact p.Prime] {K : Subgroup G} {w : G}
    (hw : w ∈ GLAPPrimeCoreOf p K) (hw1 : w ^ p = 1) : w = 1 := by
  unfold GLAPPrimeCoreOf at hw
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
  have hz1 : z ^ p = 1 := by
    apply Subtype.ext
    simpa using hw1
  have hcop := CFSG.pPrimeCore_coprime_card (p := p) (G := ↥K)
  have hzN : (⟨z, hz⟩ : ↥(CFSG.pPrimeCore p ↥K)) ^ p = 1 := by
    apply Subtype.ext
    simpa using hz1
  have hord1 : orderOf (⟨z, hz⟩ : ↥(CFSG.pPrimeCore p ↥K)) ∣ p := orderOf_dvd_of_pow_eq_one hzN
  have hord2 : orderOf (⟨z, hz⟩ : ↥(CFSG.pPrimeCore p ↥K)) ∣ Nat.card (CFSG.pPrimeCore p ↥K) :=
    orderOf_dvd_natCard _
  have hcop' := Nat.Coprime.coprime_dvd_left hord1 hcop
  have h1 := Nat.Coprime.eq_one_of_dvd hcop' hord2
  have hz' : (⟨z, hz⟩ : ↥(CFSG.pPrimeCore p ↥K)) = 1 := orderOf_eq_one_iff.1 h1
  have : z = 1 := congrArg Subtype.val hz'
  simp [this]

theorem eq_one_of_central_barOf {p n : ℕ} (K : Subgroup G) (hn : IsAltType n (barOf p K))
    (hn4 : 4 ≤ n) (w : barOf p K) (hw : ∀ v : barOf p K, v * w = w * v) : w = 1 := by
  obtain ⟨e⟩ := hn
  have hc : e w ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro v
    obtain ⟨v', rfl⟩ := e.surjective v
    have := hw v'
    have h2 := congrArg e this
    simpa using h2
  have hcenter := alternatingGroup.center_eq_bot (α := Fin n) (by simpa using hn4)
  rw [hcenter, Subgroup.mem_bot] at hc
  exact e.injective (by simpa using hc)

theorem normalizerMonoidHom_val {K : Subgroup G} (γ : ↥(Subgroup.normalizer (K : Set G)))
    (k : ↥K) : ((K.normalizerMonoidHom γ k : ↥K) : G) = (γ : G) * k * (γ : G)⁻¹ := rfl

theorem mk_conj_of_barAut_one {p : ℕ} {K : Subgroup G} {γ : ↥(Subgroup.normalizer (K : Set G))}
    (hγ : barAut p K γ = 1) (k : ↥K) :
    (QuotientGroup.mk (K.normalizerMonoidHom γ k) : barOf p K) = QuotientGroup.mk k := by
  have := congrArg (fun φ : MulAut (↥K ⧸ GLAPPrimeCore p ↥K) => φ (QuotientGroup.mk k)) hγ
  rw [barAut_mk, MulAut.one_apply] at this
  exact this

theorem barAut_eq_one_of_forall {p : ℕ} {K : Subgroup G} {γ : ↥(Subgroup.normalizer (K : Set G))}
    (h : ∀ k : ↥K, (QuotientGroup.mk (K.normalizerMonoidHom γ k) : barOf p K) = QuotientGroup.mk k) :
    barAut p K γ = 1 := by
  ext q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [barAut_mk, h k, MulAut.one_apply]

theorem exists_barAut_one_of_mem_centBar {p : ℕ} {K : Subgroup G} {a x : G}
    (hx : x ∈ centBar p (Cg a) K) :
    ∃ γ : ↥(Subgroup.normalizer (K : Set G)), barAut p K γ = 1 ∧ (γ : G) = x := by
  unfold centBar at hx
  obtain ⟨hk, -⟩ := hx
  obtain ⟨γ, hγ, hxγ⟩ := Subgroup.mem_map.1 hk
  exact ⟨γ, MonoidHom.mem_ker.1 hγ, by simpa using hxγ⟩

theorem mem_pPrimeCoreOf_of_central {p n : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hn : IsAltType n (barOf p K)) (hn4 : 4 ≤ n) {z : G} (hzK : z ∈ K)
    (hz : ∀ k : ↥K, (QuotientGroup.mk (⟨z, hzK⟩ * k * (⟨z, hzK⟩ : ↥K)⁻¹ : ↥K) : barOf p K) =
      QuotientGroup.mk k) :
    z ∈ GLAPPrimeCoreOf p K := by
  have hcen : (QuotientGroup.mk ⟨z, hzK⟩ : barOf p K) = 1 := by
    apply eq_one_of_central_barOf K hn hn4
    intro v
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective v
    have h := hz k
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  rw [QuotientGroup.eq_one_iff] at hcen
  unfold GLAPPrimeCoreOf
  exact Subgroup.mem_map.2 ⟨⟨z, hzK⟩, hcen, rfl⟩

theorem exists_sylow_normalized_by {p : ℕ} [hp : Fact p.Prime] (K X : Subgroup G)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hX : IsPGroup p ↥X) :
    ∃ P : Subgroup G, IsSylowIn p K P ∧ ∀ x ∈ X, ∀ y ∈ P, x⁻¹ * y * x ∈ P := by
  let ψ : ↥X →* MulAut ↥K := (K.normalizerMonoidHom).comp (Subgroup.inclusion hXN)
  letI : MulAction ↥X (Sylow p ↥K) := MulAction.compHom (Sylow p ↥K) ψ
  have hcard1 := IsPGroup.card_modEq_card_fixedPoints (p := p) (G := ↥X) (α := Sylow p ↥K) hX
  have hcard2 := card_sylow_modEq_one p ↥K
  have hpos : Nat.card (MulAction.fixedPoints ↥X (Sylow p ↥K)) ≠ 0 := by
    intro h0
    have h01 : (0 : ℕ) ≡ 1 [MOD p] := by
      rw [← h0]
      exact hcard1.symm.trans hcard2
    unfold Nat.ModEq at h01
    rw [Nat.zero_mod, Nat.mod_eq_of_lt hp.out.one_lt] at h01
    exact absurd h01 (by norm_num)
  obtain ⟨⟨P0, hP0⟩⟩ := (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hpos)).1
  have hfix : ∀ g : ↥X, g • P0 = P0 := fun g => MulAction.mem_fixedPoints.1 hP0 g
  have hnorm : ∀ x ∈ X, ∀ y ∈ P0.toSubgroup, x⁻¹ * (y : G) * x ∈ P0.toSubgroup.map K.subtype := by
    intro x hx y hy
    have hxinv : x⁻¹ ∈ X := X.inv_mem hx
    have hg := hfix ⟨x⁻¹, hxinv⟩
    have hsub : (ψ ⟨x⁻¹, hxinv⟩) • P0.toSubgroup = P0.toSubgroup := by
      have h1 : (ψ ⟨x⁻¹, hxinv⟩) • P0 = P0 := hg
      have h2 := congrArg (fun S : Sylow p ↥K => (S : Subgroup ↥K)) h1
      simpa only [Sylow.pointwise_smul_def] using h2
    have hmem : (ψ ⟨x⁻¹, hxinv⟩) y ∈ (ψ ⟨x⁻¹, hxinv⟩) • P0.toSubgroup :=
      Subgroup.smul_mem_pointwise_smul y _ _ hy
    rw [hsub] at hmem
    refine ⟨(ψ ⟨x⁻¹, hxinv⟩) y, hmem, ?_⟩
    simp [ψ, normalizerMonoidHom_val]
  refine ⟨P0.toSubgroup.map K.subtype, ⟨Subgroup.map_subtype_le _, P0.isPGroup'.map K.subtype, ?_⟩, ?_⟩
  · intro R hRK hR hPR
    have hR' : IsPGroup p ↥(R.subgroupOf K) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm
    have hle : P0.toSubgroup ≤ R.subgroupOf K := by
      intro z hz
      have hzP : (z : G) ∈ P0.toSubgroup.map K.subtype := Subgroup.mem_map.2 ⟨z, hz, rfl⟩
      exact (Subgroup.mem_subgroupOf).2 (hPR hzP)
    have heq := P0.is_maximal' hR' hle
    have hRe : R = (R.subgroupOf K).map K.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hRK]
    rw [hRe, heq]
  · intro x hx y hy
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.1 hy
    exact hnorm x hx y0 hy0

theorem isPGroup_of_isElemAbelian {p : ℕ} {R : Subgroup G} (hR : IsElemAbelian p R) :
    IsPGroup p ↥R := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hR.2 g g.2)⟩

theorem mem_pPrimeCoreOf_of_mem_centBar {p n : ℕ} [Fact p.Prime] {K : Subgroup G} {a z : G}
    (hn : IsAltType n (barOf p K)) (hn4 : 4 ≤ n) (hzK : z ∈ K)
    (hz : z ∈ centBar p (Cg a) K) : z ∈ GLAPPrimeCoreOf p K := by
  obtain ⟨γ, hγ1, hγz⟩ := exists_barAut_one_of_mem_centBar hz
  apply mem_pPrimeCoreOf_of_central hn hn4 hzK
  intro k
  have hk := mk_conj_of_barAut_one hγ1 k
  have heq : (⟨z, hzK⟩ * k * (⟨z, hzK⟩ : ↥K)⁻¹ : ↥K) = K.normalizerMonoidHom γ k := by
    apply Subtype.ext
    rw [normalizerMonoidHom_val, hγz]
    simp
  rw [heq]
  exact hk

theorem mem_centBar_self {p : ℕ} {K : Subgroup G} {a : G} (haK : ∀ k ∈ K, k * a = a * k) :
    a ∈ centBar p (Cg a) K := by
  have hC : a ∈ Subgroup.centralizer (K : Set G) := Subgroup.mem_centralizer_iff.2 fun h hh => haK h hh
  have hnorm : a ∈ Subgroup.normalizer (K : Set G) := Subgroup.centralizer_le_normalizer _ hC
  have hbar : barAut p K ⟨a, hnorm⟩ = 1 := by
    apply barAut_eq_one_of_forall
    intro k
    have hk : (K.normalizerMonoidHom ⟨a, hnorm⟩ k : ↥K) = k := by
      apply Subtype.ext
      rw [normalizerMonoidHom_val]
      have := haK k k.2
      simp only at this ⊢
      rw [← this]
      group
    rw [hk]
  unfold centBar
  refine ⟨Subgroup.mem_map.2 ⟨⟨a, hnorm⟩, MonoidHom.mem_ker.2 hbar, rfl⟩, ?_⟩
  exact Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]

theorem pRank_le_of_elemAb_le {p : ℕ} [hp : Fact p.Prime] {C R : Subgroup G} (hRC : R ≤ C)
    (hR : IsElemAbelian p R) : CFSG.Open.pRank p R ≤ CFSG.Open.pRank p C := by
  obtain ⟨k, hk⟩ := exists_card_eq_pow (isPGroup_of_isElemAbelian hR)
  rw [pRank_eq_of_isElemAbelian_card hR hk]
  exact CFSG.SectionRank.le_pRank hp.out.one_lt hRC hR hk

theorem pRank_sup_zpowers {p : ℕ} [hp : Fact p.Prime] {E : Subgroup G} {a : G}
    (hE : IsElemAbelian p E) (ha : a ^ p = 1) (ha1 : a ≠ 1)
    (hcomm : ∀ x ∈ E, x * a = a * x) (hdisj : E ⊓ Subgroup.zpowers a = ⊥) :
    CFSG.Open.pRank p (E ⊔ Subgroup.zpowers a) = CFSG.Open.pRank p E + 1 := by
  have hA : IsElemAbelian p (Subgroup.zpowers a) := CFSG.Open.isElemAbelian_zpowers ha
  have hcz : ∀ x ∈ E, ∀ f ∈ Subgroup.zpowers a, x * f = f * x := by
    intro x hx f hf
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
    exact (Commute.zpow_right (show Commute x a from hcomm x hx) k).eq
  have hEc : IsElemAbelian p (E ⊔ Subgroup.zpowers a) := by
    apply isElemAbelian_sup_of_commute hE hA
    intro x hx
    exact Subgroup.mem_centralizer_iff.2 fun h hh => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute a x from (hcomm x hx).symm) k).eq
  obtain ⟨k, hk⟩ := exists_card_eq_pow (isPGroup_of_isElemAbelian hE)
  have hzc : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha ha1]
  have hcard : Nat.card ↥(E ⊔ Subgroup.zpowers a) = p ^ (k + 1) := by
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_eq_mul_of_commute hcz hdisj, hk, hzc,
      pow_succ]
  rw [pRank_eq_of_isElemAbelian_card hEc hcard]
  rw [pRank_eq_of_isElemAbelian_card hE hk]

theorem isElemAbelian_gLBConj' {p : ℕ} {H : Subgroup G} (hH : IsElemAbelian p H) (g : G) :
    IsElemAbelian p (GLBConj g H) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x', hx', hxe⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨y', hy', hye⟩ := Subgroup.mem_map.1 y.2
    show (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hxe, ← hye, ← map_mul, ← map_mul, elemAbelian_comm hH hx' hy']
  · obtain ⟨y, hyH, rfl⟩ := Subgroup.mem_map.1 hx
    show (MulAut.conj g⁻¹).toMonoidHom y ^ p = 1
    rw [← map_pow, hH.2 y hyH, map_one]

theorem inf_eq_bot_of_elemAb_le_centBar {p n : ℕ} [hp : Fact p.Prime] {K : Subgroup G} {a : G}
    (hn : IsAltType n (barOf p K)) (hn4 : 4 ≤ n) {X : Subgroup G}
    (hXC : X ≤ centBar p (Cg a) K) (hXab : IsElemAbelian p X) : X ⊓ K = ⊥ := by
  rw [eq_bot_iff]
  rintro z hz
  obtain ⟨hzX, hzK⟩ := Subgroup.mem_inf.1 hz
  have hzO := mem_pPrimeCoreOf_of_mem_centBar hn hn4 hzK (hXC hzX)
  have := eq_one_of_mem_pPrimeCoreOf hzO (hXab.2 z hzX)
  rw [this]
  exact Subgroup.one_mem _

theorem comm_of_normalized {p n : ℕ} [hp : Fact p.Prime] {K : Subgroup G} {a : G} {E : Subgroup G}
    (hn : IsAltType n (barOf p K)) (hn4 : 4 ≤ n) (hEK : E ≤ K) (hEab : IsElemAbelian p E)
    {x : G} (hxC : x ∈ centBar p (Cg a) K) (hxE : GLBConj x E = E) (y : G) (hy : y ∈ E) :
    x * y = y * x := by
  obtain ⟨γ, hγ1, hγx⟩ := exists_barAut_one_of_mem_centBar hxC
  have hyK : y ∈ K := hEK hy
  have hxy : x * y * x⁻¹ ∈ E := by
    have : y ∈ GLBConj x E := by rw [hxE]; exact hy
    exact (mem_gLBConj).1 this
  have hmk := mk_conj_of_barAut_one hγ1 ⟨y, hyK⟩
  have heq : (K.normalizerMonoidHom γ ⟨y, hyK⟩ : ↥K) = ⟨x * y * x⁻¹, hEK hxy⟩ := by
    apply Subtype.ext
    rw [normalizerMonoidHom_val, hγx]
  rw [heq] at hmk
  have hquot := (QuotientGroup.eq (a := (⟨x * y * x⁻¹, hEK hxy⟩ : ↥K)) (b := (⟨y, hyK⟩ : ↥K))).1 hmk
  have hw : (x * y * x⁻¹)⁻¹ * y ∈ GLAPPrimeCoreOf p K := by
    unfold GLAPPrimeCoreOf
    refine Subgroup.mem_map.2 ⟨(⟨x * y * x⁻¹, hEK hxy⟩ : ↥K)⁻¹ * ⟨y, hyK⟩, hquot, ?_⟩
    simp
  have hwE : (x * y * x⁻¹)⁻¹ * y ∈ E := E.mul_mem (E.inv_mem hxy) hy
  have hw1 : ((x * y * x⁻¹)⁻¹ * y) ^ p = 1 := hEab.2 _ hwE
  have h1 := eq_one_of_mem_pPrimeCoreOf hw hw1
  have h2 : x * y * x⁻¹ = y := inv_mul_eq_one.1 h1
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem exists_transportData {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hI105 : Input10_5K)
    (K : Subgroup G) {a : G} (hKa : ∀ k ∈ K, k * a = a * k) (ha : a ^ p = 1)
    (hn : IsAltType n (barOf p K)) (hn4 : 4 ≤ n) :
    ∃ Q₁ Q₂ : Subgroup G, TransportData p n K a Q₁ Q₂ := by
  have hp1 : 1 < p := hp.out.one_lt
  have haC : a ∈ centBar p (Cg a) K := mem_centBar_self hKa
  obtain ⟨E0, hE0C, hE0ab, hE0card⟩ := CFSG.SectionRank.exists_pRank hp1 (centBar p (Cg a) K)
  have hE0r : CFSG.Open.pRank p E0 = CFSG.Open.pRank p (centBar p (Cg a) K) :=
    pRank_eq_of_isElemAbelian_card hE0ab hE0card
  have hCg : centBar p (Cg a) K ≤ Cg a := by unfold centBar; exact inf_le_right
  have hCN : centBar p (Cg a) K ≤ Subgroup.normalizer (K : Set G) := by
    unfold centBar; exact inf_le_left.trans (Subgroup.map_subtype_le _)
  have hza : Subgroup.zpowers a ≤ centBar p (Cg a) K := Subgroup.zpowers_le.2 haC
  have hE0a : ∀ x ∈ E0, x * a = a * x := fun x hx =>
    ((Subgroup.mem_centralizer_iff.1 (hCg (hE0C hx))) a (Set.mem_singleton a)).symm
  have hAB : E0 ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute a x from (hE0a x hx).symm) k).eq
  have hA : IsElemAbelian p (Subgroup.zpowers a) := CFSG.Open.isElemAbelian_zpowers ha
  have hQ₂ab : IsElemAbelian p (E0 ⊔ Subgroup.zpowers a) := isElemAbelian_sup_of_commute hE0ab hA hAB
  have hQ₂C : E0 ⊔ Subgroup.zpowers a ≤ centBar p (Cg a) K := sup_le hE0C hza
  have hQ₂max : ∀ R : Subgroup G, R ≤ centBar p (Cg a) K → IsElemAbelian p R →
      CFSG.Open.pRank p R ≤ CFSG.Open.pRank p (E0 ⊔ Subgroup.zpowers a) := by
    intro R hRC hR
    calc CFSG.Open.pRank p R ≤ CFSG.Open.pRank p (centBar p (Cg a) K) :=
          pRank_le_of_elemAb_le hRC hR
      _ = CFSG.Open.pRank p E0 := hE0r.symm
      _ ≤ CFSG.Open.pRank p (E0 ⊔ Subgroup.zpowers a) :=
          CFSG.SectionRank.pRank_mono hp1 le_sup_left
  obtain ⟨P, hPsyl, hPnorm⟩ :=
    exists_sylow_normalized_by K (E0 ⊔ Subgroup.zpowers a) (hQ₂C.trans hCN)
      (isPGroup_of_isElemAbelian hQ₂ab)
  obtain ⟨E, ⟨hEP, hEab, hErk⟩, hEuniq⟩ := hI105 G p n hp.out hp2 K hn P hPsyl
  have hEK : E ≤ K := hEP.trans hPsyl.1
  have hEQ : ∀ x ∈ E0 ⊔ Subgroup.zpowers a, GLBConj x E = E := by
    intro x hx
    have hle : GLBConj x E ≤ P := by
      intro y hy
      have hy' := (mem_gLBConj).1 hy
      have h1 := hPnorm x hx _ (hEP hy')
      have h2 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      rw [h2] at h1
      exact h1
    have hGab := isElemAbelian_gLBConj' hEab x
    have hr : CFSG.Open.pRank p (GLBConj x E) = n / p := by
      rw [pRank_gLBConj' hp1]; exact hErk
    exact hEuniq (GLBConj x E) ⟨hle, hGab, hr⟩
  have hcomm : ∀ x ∈ E0 ⊔ Subgroup.zpowers a, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    comm_of_normalized hn hn4 hEK hEab (hQ₂C hx) (hEQ x hx) y hy
  exact ⟨E, E0 ⊔ Subgroup.zpowers a, ⟨hEK, hEab, hErk, hQ₂ab, hQ₂C, hQ₂max,
    (le_sup_right (a := E0) (b := Subgroup.zpowers a)) (Subgroup.mem_zpowers a),
    fun x hx y hy => (hcomm y hy x hx).symm⟩⟩

theorem le_centralizer_zpowers_of_comm {A : Subgroup G} {a : G} (hcomm : ∀ x ∈ A, x * a = a * x) :
    A ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) := fun x hx =>
  Subgroup.mem_centralizer_iff.2 fun h hh => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (show Commute a x from (hcomm x hx).symm) k).eq

theorem pRank_add_one_le_of_transport {p n : ℕ} [hp : Fact p.Prime] {K : Subgroup G} {a : G}
    {Q₁ Q₂ : Subgroup G} (hn : IsAltType n (barOf p K)) (hn4 : 4 ≤ n)
    (hKa : ∀ k ∈ K, k * a = a * k) (ha : a ^ p = 1) (ha1 : a ≠ 1)
    (hT : TransportData p n K a Q₁ Q₂) :
    CFSG.Open.pRank p Q₁ + 1 ≤ CFSG.Open.pRank p (Q₁ ⊔ Q₂) := by
  have hp1 : 1 < p := hp.out.one_lt
  have h2 : Q₂ ⊓ K = ⊥ := inf_eq_bot_of_elemAb_le_centBar hn hn4 hT.Q₂C hT.Q₂ab
  have hza : Subgroup.zpowers a ≤ Q₂ := Subgroup.zpowers_le.2 hT.aQ₂
  have hdisj : Q₁ ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzQ1, hzza⟩ := Subgroup.mem_inf.1 hz
    have hz2 : z ∈ Q₂ ⊓ K := Subgroup.mem_inf.2 ⟨hza hzza, hT.Q₁K hzQ1⟩
    rw [h2] at hz2
    exact hz2
  have hpr := pRank_sup_zpowers hT.Q₁ab ha ha1 (fun x hx => hKa x (hT.Q₁K hx)) hdisj
  have hmono : CFSG.Open.pRank p (Q₁ ⊔ Subgroup.zpowers a) ≤ CFSG.Open.pRank p (Q₁ ⊔ Q₂) :=
    CFSG.SectionRank.pRank_mono hp1 (sup_le_sup_left hza Q₁)
  omega

theorem one_le_pRank_of_elemAb_ne_bot {p : ℕ} [hp : Fact p.Prime] {X : Subgroup G}
    (hX : IsElemAbelian p X) (hX1 : X ≠ ⊥) : 1 ≤ CFSG.Open.pRank p X := by
  obtain ⟨k, hk⟩ := exists_card_eq_pow (isPGroup_of_isElemAbelian hX)
  rw [pRank_eq_of_isElemAbelian_card hX hk]
  by_contra hk0
  have hk0' : k = 0 := by omega
  rw [hk0', pow_zero] at hk
  exact hX1 ((Subgroup.eq_bot_iff_card _).2 hk)

theorem le_glbCore_of_generation {p n : ℕ} [hp : Fact p.Prime] {K : Subgroup G} {a : G}
    {Q₁ Q₂ : Subgroup G} (hn : IsAltType n (barOf p K)) (hn4 : 4 ≤ n)
    (hKa : ∀ k ∈ K, k * a = a * k) (ha : a ^ p = 1) (ha1 : a ≠ 1)
    (hT : TransportData p n K a Q₁ Q₂)
    (hgen : (⨆ (X : Subgroup G) (_ : X ≤ Q₁ ∧ X ≠ ⊥), Subgroup.normalizer (X : Set G) ⊓ K) = K) :
    K ≤ GLBCore p 2 (Q₁ ⊔ Q₂) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hza : Subgroup.zpowers a ≤ Q₂ := Subgroup.zpowers_le.2 hT.aQ₂
  rw [← hgen]
  refine iSup₂_le fun X hX => ?_
  have hXab : IsElemAbelian p X := isElemAbelian_mono hT.Q₁ab hX.1
  have hdisj : X ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzX, hzza⟩ := Subgroup.mem_inf.1 hz
    have hz1 : z ∈ Q₁ ⊓ Subgroup.zpowers a := Subgroup.mem_inf.2 ⟨hX.1 hzX, hzza⟩
    have hbot := pRank_add_one_le_of_transport hn hn4 hKa ha ha1 hT
    have hQ1 : Q₁ ⊓ Subgroup.zpowers a = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨hwQ1, hwza⟩ := Subgroup.mem_inf.1 hw
      have hw2 : w ∈ Q₂ ⊓ K := Subgroup.mem_inf.2 ⟨hza hwza, hT.Q₁K hwQ1⟩
      rw [inf_eq_bot_of_elemAb_le_centBar hn hn4 hT.Q₂C hT.Q₂ab] at hw2
      exact hw2
    rw [hQ1] at hz1
    exact hz1
  have hrk : 2 ≤ CFSG.Open.pRank p (X ⊔ Subgroup.zpowers a) := by
    have h1 := pRank_sup_zpowers hXab ha ha1
      (fun x hx => hKa x (hX.1 hx |> fun hxQ => hT.Q₁K hxQ)) hdisj
    have h0 := one_le_pRank_of_elemAb_ne_bot hXab hX.2
    omega
  have hYle : X ⊔ Subgroup.zpowers a ≤ Q₁ ⊔ Q₂ := sup_le_sup hX.1 hza
  have hXZ : X ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) :=
    le_centralizer_zpowers_of_comm fun x hx => hKa x (hT.Q₁K (hX.1 hx))
  have key : ∀ g' ∈ Subgroup.normalizer (X : Set G), g' ∈ K → ∀ y ∈ X ⊔ Subgroup.zpowers a,
      g' * y * g'⁻¹ ∈ X ⊔ Subgroup.zpowers a := by
    intro g' hg' hgK y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := exists_mul_of_mem_sup hXZ hy
    have hgx : g' * x * g'⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hg' x).1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hcomm' : Commute g' a := hKa g' hgK
    have hgk : g' * a ^ k * g'⁻¹ = a ^ k := by
      rw [mul_inv_eq_iff_eq_mul, (hcomm'.zpow_right k).eq]
    have e : g' * (x * a ^ k) * g'⁻¹ = (g' * x * g'⁻¹) * (g' * a ^ k * g'⁻¹) := by group
    rw [e, hgk]
    exact Subgroup.mul_mem _ (le_sup_left (a := X) (b := Subgroup.zpowers a) hgx)
      (le_sup_right (a := X) (b := Subgroup.zpowers a) (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) k))
  have hnorm : Subgroup.normalizer (X : Set G) ⊓ K ≤
      Subgroup.normalizer ((X ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
    intro g' hg'
    obtain ⟨hgX, hgK⟩ := Subgroup.mem_inf.1 hg'
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact key g' hgX hgK y hy
    · intro hy
      have h1 := key g'⁻¹ (Subgroup.inv_mem _ hgX) (K.inv_mem hgK) _ hy
      have e : g'⁻¹ * (g' * y * g'⁻¹) * g'⁻¹⁻¹ = y := by group
      rw [e] at h1
      exact h1
  unfold GLBCore
  exact hnorm.trans (le_sSup ⟨X ⊔ Subgroup.zpowers a, hYle, hrk, rfl⟩)

theorem exists_conj_sylow_contains {p : ℕ} [hp : Fact p.Prime] {Q B : Subgroup G}
    (hQ : IsPGroup p ↥Q) (hB : IsPGroup p ↥B) :
    ∃ g : G, ∃ S : Subgroup G, IsPGroup p ↥S ∧ GLBConj g Q ≤ S ∧ B ≤ S := by
  obtain ⟨S, hBS⟩ := hB.exists_le_sylow
  obtain ⟨T, hQT⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  refine ⟨g⁻¹, S.toSubgroup, S.isPGroup', ?_, hBS⟩
  intro y hy
  rw [mem_gLBConj] at hy
  have hyT : g⁻¹ * y * g⁻¹⁻¹ ∈ T.toSubgroup := hQT hy
  have hmem : MulAut.conj g (g⁻¹ * y * g⁻¹⁻¹) ∈ (MulAut.conj g) • T.toSubgroup :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hyT
  have hS : (MulAut.conj g) • T.toSubgroup = S.toSubgroup := by
    have h1 := congrArg (fun U : Sylow p G => (U : Subgroup G)) hg
    simpa only [Sylow.coe_subgroup_smul] using h1
  rw [hS] at hmem
  have e : MulAut.conj g (g⁻¹ * y * g⁻¹⁻¹) = y := by
    simp only [MulAut.conj_apply, inv_inv]
    group
  rw [e] at hmem
  exact hmem

theorem anchorRanks_of_numbers {p r n q T a' : ℕ} (hp : 3 ≤ p) (hr : 2 ≤ r) (hrn : p ^ r < n)
    (hq1 : n / p + 1 ≤ q) (hq2 : q ≤ T + 1) (hq3 : p = 3 → q ≤ T)
    (hsub : p = 3 → r = 2 → q = 4 → a' ≤ 3) :
    p ^ (r - 1) ≤ q ∧ p ^ (r - 1) ≤ T ∧
      (p = 3 → r = 2 → 4 ≤ q ∧ 4 ≤ T ∧ (5 ≤ q → 5 ≤ T) ∧ (q = 4 → a' ≤ 3)) := by
  have hpr : p ^ (r - 1) * p = p ^ r := by
    rw [← pow_succ]
    congr 1
    omega
  have hdiv : p ^ (r - 1) ≤ n / p :=
    (Nat.le_div_iff_mul_le (by omega)).2 (by rw [hpr]; exact hrn.le)
  refine ⟨by omega, by omega, fun hp3 hr2 => ?_⟩
  subst hp3 hr2
  norm_num at hrn
  have h10 : 10 ≤ n := by omega
  refine ⟨by omega, by omega, fun h5 => by omega, fun h4 => hsub rfl rfl h4⟩

theorem hasBigAltPComponent_of_conj {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (hAlt : AltBalanceInput) (h : Sec11 G m p B M E A) (g : G) {n r : ℕ}
    (ha1 : a ≠ 1) (hap : a ^ p = 1) (hacent : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K)
    (hn : IsAltType n (barOf p K)) (hn10 : 10 ≤ n) (hrn : p ^ r < n)
    (hta : g⁻¹ * a * g ∈ M) (hKM : GLBConj g K ≤ M) :
    HasBigAltPComponent p r M := by
  have hJ : GLAPComponent p (Subgroup.centralizer ({g⁻¹ * a * g} : Set G)) (GLBConj g K) := by
    have := glaPComponent_gLBConj hacent g
    rwa [centralizer_gLBConj_eq] at this
  have ht1 : g⁻¹ * a * g ≠ 1 := by
    intro h1
    apply ha1
    have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [this, h1]
    group
  have htp : (g⁻¹ * a * g) ^ p = 1 := by
    rw [conj_pow_eq, hap]
    group
  obtain ⟨L, n', hL, hn', hle⟩ :=
    hAlt G m p B M E A h (g⁻¹ * a * g) (GLBConj g K) n hta htp ht1 hKM hJ
      (isAltType_barOf_gLBConj g K hn) hn10
  exact ⟨L, n', hL, hn', lt_of_lt_of_le hrn hle⟩


end Lemma118T

open Lemma118T in
theorem lemma118Transport_of_inputs (hAlt : AltBalanceInput) (hI31_6 : Input31_6)
    (hI31_9 : Input31_9) (hI105 : Input10_5K) (hI24 : Input24_1K) (hLoc : Input118Local)
    (hSub : Lemma118Sub) : Lemma118Transport := by
  intro G _ _ m p B M E A a K h ht
  obtain ⟨n, hn, hrn, hpn⟩ := ht
  have hp : p.Prime := h.standing.prime
  have hp2 : p ≠ 2 := h.standing.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hr2 : 2 ≤ CFSG.Open.pRank p (E ⊓ A) := h.pair.1.2.2
  have hKle : K ≤ Cg a := h.hK.1
  have hKa : ∀ k ∈ K, k * a = a * k := fun k hk =>
    ((Subgroup.mem_centralizer_iff.1 (hKle hk)) a (Set.mem_singleton a)).symm
  have hap : a ^ p = 1 := h.pair.1.2.1.1.1.2.1.2 a h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have hpr2 : p ^ 2 ≤ p ^ CFSG.Open.pRank p (E ⊓ A) := Nat.pow_le_pow_right hp.pos hr2
  have h9 : 9 ≤ p ^ 2 := by nlinarith
  have hn10 : 10 ≤ n := by omega
  have hn4 : 4 ≤ n := by omega
  obtain ⟨Q₁, Q₂, hT⟩ := exists_transportData hp2 hI105 K hKa hap hn hn4
  have hrank := pRank_add_one_le_of_transport hn hn4 hKa hap ha1 hT
  have hdiv : p ^ (CFSG.Open.pRank p (E ⊓ A) - 1) ≤ n / p := by
    have hpr : p ^ (CFSG.Open.pRank p (E ⊓ A) - 1) * p = p ^ CFSG.Open.pRank p (E ⊓ A) := by
      rw [← pow_succ]
      congr 1
      omega
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by rw [hpr]; exact hrn.le)
  have hn2 : 2 ≤ n / p := by
    have : p ≤ p ^ (CFSG.Open.pRank p (E ⊓ A) - 1) := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (CFSG.Open.pRank p (E ⊓ A) - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  have hQab : IsElemAbelian p (Q₁ ⊔ Q₂) := by
    refine isElemAbelian_sup_of_commute hT.Q₁ab hT.Q₂ab ?_
    exact fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => (hT.comm x hx y hy).symm
  obtain ⟨hloc1, hloc3⟩ := hLoc G m p B M E A a K h n Q₁ Q₂ hn hpn hT
  have hKQ : K ≤ GLBCore p 2 (Q₁ ⊔ Q₂) :=
    le_glbCore_of_generation hn hn4 hKa hap ha1 hT
      (hI24 G p n hp hp2 hpn hn2 K hn Q₁ hT.Q₁K hT.Q₁ab hT.Q₁rk)
  obtain ⟨hBab, hBcard, -⟩ := h.bOne.1
  obtain ⟨g, S, hS, hgQ, hBS⟩ := exists_conj_sylow_contains (isPGroup_of_isElemAbelian hQab)
    (isPGroup_of_isElemAbelian hBab)
  have hBr : CFSG.Open.pRank p B = GLATwoLocalRank p G :=
    pRank_eq_of_isElemAbelian_card hBab hBcard
  have hD : inD p M B := lemma101_ii_holds h.toSec10Fails
  have hQ'ab : IsElemAbelian p (GLBConj g (Q₁ ⊔ Q₂)) := isElemAbelian_gLBConj' hQab g
  have hQ'r : CFSG.Open.pRank p (GLBConj g (Q₁ ⊔ Q₂)) = CFSG.Open.pRank p (Q₁ ⊔ Q₂) :=
    pRank_gLBConj' hp1 _ _
  have hQ1r : CFSG.Open.pRank p Q₁ = n / p := hT.Q₁rk
  have key := anchorRanks_of_numbers (p := p) (r := CFSG.Open.pRank p (E ⊓ A)) (n := n)
    (q := CFSG.Open.pRank p (Q₁ ⊔ Q₂)) (T := GLATwoLocalRank p G) (a' := CFSG.Open.pRank p A)
    hp3 hr2 hrn (by omega) hloc1
    (fun hp3' => by rw [hp3']; exact hloc3 hp3')
    (fun hp3' hr2' hq4 => by
      subst hp3'
      exact hSub G m B M E A a K h n Q₁ Q₂ hn hpn hrn hT hr2' hq4)
  have hP1 : GLBCore p 2 (GLBConj g (Q₁ ⊔ Q₂)) ≤ M :=
    lemma118_P1_claim_of_ranks hp2 h.pair hI31_6 hI31_9 hD hQ'ab hS hgQ hBS
      (by rw [hQ'r]; exact key.1)
      (by rw [hBr]; exact key.2.1)
      (fun hp3' hr2' => by rw [hQ'r, hBr]; exact key.2.2 hp3' hr2')
  have hKM : GLBConj g K ≤ M :=
    ((gLBConj_mono g hKQ).trans (glbCore_gLBConj_le' hp1 _ g)).trans hP1
  have hta : g⁻¹ * a * g ∈ M := by
    have hmem : g⁻¹ * a * g ∈ GLBConj g (Q₁ ⊔ Q₂) := by
      rw [mem_gLBConj]
      have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [e]
      exact (le_sup_right : Q₂ ≤ Q₁ ⊔ Q₂) hT.aQ₂
    have hrk : 2 ≤ CFSG.Open.pRank p (GLBConj g (Q₁ ⊔ Q₂)) := by
      rw [hQ'r]
      omega
    have hnorm := normalizer_le_glbCore' (p := p) (Q := GLBConj g (Q₁ ⊔ Q₂))
      (P := GLBConj g (Q₁ ⊔ Q₂)) le_rfl hrk
    exact hP1 (hnorm (Subgroup.le_normalizer hmem))
  exact hasBigAltPComponent_of_conj hAlt h.toSec11 g ha1 hap h.hK hn hn10 hrn hta hKM

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

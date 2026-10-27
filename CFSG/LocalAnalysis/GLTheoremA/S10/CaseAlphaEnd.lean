module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseAlpha
public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem AlphaCtx.ne_one {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G}
    (ac : AlphaCtx G p B x L b a) : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)

@[expose] def KyCardTy (B K : Subgroup G) (n : ℕ) : Prop :=
  (catalogIs (PSimple 3 K) (isU6n n) ∧ Nat.card B = 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 K)) ∨
    (catalogIs (PSimple 3 K) (isTE6n n) ∧ Nat.card B = 3 ^ 4 * Nat.card ↥(B ⊓ centModSubgroup 3 K))

theorem KyCardTy.type {B K : Subgroup G} {n : ℕ} (h : KyCardTy B K n) :
    catalogIs (PSimple 3 K) (isU6n n) ∨ catalogIs (PSimple 3 K) (isTE6n n) :=
  h.imp (fun h => h.1) (fun h => h.1)

theorem Ky_le_cx {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G} {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) :
    Kf p K (Subgroup.zpowers y) ≤ cx y := by
  have hyE : y ∈ E := by
    rw [hd.E_def]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hKy : K ≤ cx y := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 (hd.K_comp.1 hg).2 y hyE).symm)
  exact closureIn_le_of_le hKy ((layer_le p _).trans (S3.centralizer_zpowers y).le)

theorem alpha_158 (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K)
    (hky : AlphaKy p x a y K) :
    p = 3 ∧ (∃ n : ℕ, Odd n ∧ 1 < n ∧ KyCardTy B (Kf p K (Subgroup.zpowers y)) n) ∧
      ∀ T : Subgroup G, T ≤ cx y → IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set G) →
        (⁅T, B⁆ : Subgroup G) = ⊥ := by
  have hp := hc.ctx.prime
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian p B := B_el h
  obtain ⟨hDB, -, -⟩ := dgrp_facts hc h
  have hyB : y ∈ B := hd.E₀_B (hd.F_E₀ hd.y_F)
  have haB : a ∈ B := hDB ac.mem
  have hBy : B ≤ cx y := isElemAbelian_le_centralizer hBel hyB
  have hrk : GLATwoLocalRank p ↥(Subgroup.centralizer ({y} : Set G)) ≤ GLATwoLocalRank p G :=
    glaTwoLocalRank_subgroup_le hp.one_lt (cx y)
  have hhyp : I158HypK p (cx y) (Kf p K (Subgroup.zpowers y)) B x a
      (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) :=
    ⟨⟨S8.isKGroup_cx hc.ctx hd.y_ne, hky.Ky_comp, hBel, hBy, by
      rw [hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos hrk, hS.2.1.1, haB, hS.2.1.2.1, ac.ne_one,
      hky.Kxy_comp, hkay.chev_xy, hky.Kay_comp, hkay.chev_ay⟩, hkay.x_fg, hkay.a_fg⟩
  exact hin.i158.main p hp hc.ctx.odd _ _ _ _ _ _ _ hhyp hky.layer_ne |> fun ⟨hp3, n, hn, hn1, hty, h6⟩ =>
    ⟨hp3, ⟨n, hn, hn1, hty.imp (fun h => ⟨h.1, h.2.2.2⟩) (fun h => ⟨h.1, h.2.2.2⟩)⟩, h6⟩

theorem alpha_B_norm (hc : S10Ctx G 3) (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg 3 B x L b) {E₀ F : Subgroup G} {y : G} {E K : Subgroup G}
    (hd : AlphaData 3 B x L b a E₀ F y E K) (hky : AlphaKy 3 x a y K) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hty : catalogIs (PSimple 3 (Kf 3 K (Subgroup.zpowers y))) (isU6n n) ∨
      catalogIs (PSimple 3 (Kf 3 K (Subgroup.zpowers y))) (isTE6n n)) :
    B ≤ Subgroup.normalizer ((Kf 3 K (Subgroup.zpowers y) : Subgroup G) : Set G) := by
  have hS := sstar_triple h.star
  have hyB : y ∈ B := hd.E₀_B (hd.F_E₀ hd.y_F)
  have hBy : B ≤ cx y := isElemAbelian_le_centralizer (B_el h) hyB
  have hrk : GLATwoLocalRank 3 ↥(Subgroup.centralizer ({y} : Set G)) ≤ GLATwoLocalRank 3 G :=
    glaTwoLocalRank_subgroup_le (by norm_num : 1 < 3) (cx y)
  exact hin.i112 (cx y) _ B n (S8.isKGroup_cx hc.ctx hd.y_ne) hky.Ky_comp (B_el h) hBy (by
    rw [hS.1.2.1]
    exact Nat.pow_le_pow_right (by norm_num) hrk) hn hn1 hty

theorem not_essential_y {B : Subgroup G} {y : G}
    (h6 : ∀ T : Subgroup G, T ≤ cx y → IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set G) →
      (⁅T, B⁆ : Subgroup G) = ⊥) : ¬ IsEssential 3 B y := by
  rintro ⟨-, -, T, hTc, hT2, hTB, hne, -⟩
  exact hne (h6 T hTc hT2 hTB)

theorem normalizes_of_inYK {y : G} {K B' : Subgroup G} (hK : K ≤ cx y) (hY : InYK y K B') :
    B' ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  obtain ⟨i, k, hk, rfl⟩ := hY g hg
  have hyN : y ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun z hz =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hK hz)))
  exact Subgroup.mul_mem _ (zpow_mem hyN i) (Subgroup.le_normalizer hk)

theorem inducesInner_of_inYK {y : G} {K : Subgroup G} (hK : K ≤ cx y) {g : G} {i : ℤ} {k : G} (hk : k ∈ K)
    (hg : g = y ^ i * k) : InducesInnerMod p K g := by
  refine ⟨k, hk, fun z hz => ?_⟩
  have hcomm : Commute z (y ^ i) := (Commute.zpow_right
    (Subgroup.mem_centralizer_singleton_iff.1 (hK hz) : Commute z y) i)
  have : g⁻¹ * z * g = k⁻¹ * z * k := by
    rw [hg]
    have h1 : (y ^ i)⁻¹ * z * y ^ i = z := by
      rw [mul_assoc, hcomm.eq, inv_mul_cancel_left]
    calc (y ^ i * k)⁻¹ * z * (y ^ i * k) = k⁻¹ * ((y ^ i)⁻¹ * z * y ^ i) * k := by group
      _ = k⁻¹ * z * k := by rw [h1]
  rw [this, inv_mul_cancel]
  exact Subgroup.one_mem _

theorem caseAlphaEnd_chev2 {S : Type} [Group S] {n : ℕ}
    (h : catalogIs S (isU6n n) ∨ catalogIs S (isTE6n n)) : IsChevSimple 2 S := by
  refine Or.inl ?_
  rcases h with h | h
  · obtain ⟨i, hi, ⟨e⟩⟩ := h
    refine ⟨i, ?_, ⟨e⟩⟩
    cases i with
    | cyclic p hp => simp [isU6n, onLie] at hi
    | alternating n hn => simp [isU6n, onLie] at hi
    | sporadic s => simp [isU6n, onLie] at hi
    | lie j =>
      obtain ⟨d, hv⟩ := j
      simp only [isU6n, onLie] at hi
      simp only [onLie]
      change d.characteristic = 2
      split at hi
      · rename_i q
        rw [TauCeti.LieTypeIndex.characteristic_twistedA]
        exact hi.1
      · exact absurd hi id
  · obtain ⟨i, hi, ⟨e⟩⟩ := h
    refine ⟨i, ?_, ⟨e⟩⟩
    cases i with
    | cyclic p hp => simp [isTE6n, onLie] at hi
    | alternating n hn => simp [isTE6n, onLie] at hi
    | sporadic s => simp [isTE6n, onLie] at hi
    | lie j =>
      obtain ⟨d, hv⟩ := j
      simp only [isTE6n, onLie] at hi
      simp only [onLie]
      change d.characteristic = 2
      split at hi
      · rename_i q
        rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
        exact hi.1
      · exact absurd hi id

theorem caseAlphaEnd_card_le_three {H : Subgroup G} (hH : IsCyclic ↥H)
    (hexp : IsElemAbelian 3 H) : Nat.card H ≤ 3 := by
  haveI := hH
  have h1 : Monoid.exponent ↥H ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
    apply Subtype.ext
    simpa using hexp.2 g.1 g.2
  have h2 : Monoid.exponent ↥H = Nat.card ↥H := IsCyclic.exponent_eq_card
  rw [← h2]
  exact Nat.le_of_dvd (by norm_num) h1

theorem caseAlphaEnd_bstar_T_of_cycMod (hin : I1312At G 3) {B' K : Subgroup G} {y : G}
    (hKc : GLAPComponent 3 (cx y) K) (hchev : IsChevSimple 2 (PSimple 3 K))
    (hcm : CycModSylow 3 K) (hyB' : y ∈ B') (hY : InYK y K B') (hel : IsElemAbelian 3 B')
    (hbig : 27 ≤ Nat.card B') {T₀ : Subgroup G} (hT₀K : T₀ ≤ K) (hT₀2 : IsPGroup 2 T₀)
    (hT₀O : ¬ T₀ ≤ GLAPPrimeCoreOf 3 K) (hT₀B : B' ≤ Subgroup.normalizer (T₀ : Set G)) :
    ∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ B' ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B'⁆ : Subgroup G) ≠ ⊥ ∧ IsEmpty (T ≃* QuaternionGroup 2) ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 K := by
  classical
  have hBN : B' ≤ Subgroup.normalizer (K : Set G) := normalizes_of_inYK hKc.1 hY
  have hnc : ∀ H : Subgroup G, H ≤ B' → 9 ≤ Nat.card H → (∀ c ∈ H, CentMod 3 K c) → False := by
    intro H hHB hH9 hHc
    have hel' := isElemAbelian_mono hel hHB
    have hcyc : IsCyclic ↥H := hcm H hHc (isPGroup_of_isElemAbelian hel')
    have := caseAlphaEnd_card_le_three hcyc hel'
    omega
  obtain ⟨T, hTS, hTmax⟩ := Set.exists_max_image
    {S : Subgroup G | T₀ ≤ S ∧ S ≤ K ∧ IsPGroup 2 S ∧ B' ≤ Subgroup.normalizer (S : Set G) ∧
      ¬ S ≤ GLAPPrimeCoreOf 3 K}
    (fun S : Subgroup G => Nat.card S) (Set.toFinite _) ⟨T₀, le_rfl, hT₀K, hT₀2, hT₀B, hT₀O⟩
  obtain ⟨hT₀T, hTK, hT2, hTB, hTO⟩ := hTS
  have hmax : ∀ S' : Subgroup G, T ≤ S' → S' ≤ K → IsPGroup 2 S' →
      B' ≤ Subgroup.normalizer (S' : Set G) → ¬ S' ≤ GLAPPrimeCoreOf 3 K → S' = T := by
    intro S' hTS' hS'K hS'2 hS'B hS'O
    have hmem : S' ∈ {S : Subgroup G | T₀ ≤ S ∧ S ≤ K ∧ IsPGroup 2 S ∧
        B' ≤ Subgroup.normalizer (S : Set G) ∧ ¬ S ≤ GLAPPrimeCoreOf 3 K} :=
      ⟨hT₀T.trans hTS', hS'K, hS'2, hS'B, hS'O⟩
    exact (Subgroup.eq_of_le_of_card_ge hTS' (hTmax S' hmem)).symm
  obtain ⟨hcentr, hsmall⟩ := hin Nat.prime_three (by norm_num) (cx y) K B' T hKc hchev hel hBN hTK hT2 hTB hTO hmax
  have hcardT : 9 ≤ Nat.card T := by
    by_contra hlt
    obtain ⟨B₀, hB₀B, hB₀card, hB₀c⟩ := hsmall (by omega)
    exact hnc B₀ hB₀B (by omega) fun c hc => hcentr c (hB₀B hc) (hB₀c c hc)
  refine ⟨T, hTK, hT2, hTB, ?_, ⟨fun e => ?_⟩, hTO⟩
  · intro hbot
    apply hnc B' le_rfl (by omega)
    intro c hc
    apply hcentr c hc
    have h1 : (⁅T, Subgroup.zpowers c⁆ : Subgroup G) ≤ ⁅T, B'⁆ :=
      Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.2 hc)
    rw [hbot] at h1
    exact h1.trans bot_le
  · have h8 : Nat.card (QuaternionGroup 2) = 8 := by
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    have := Nat.card_congr e.toEquiv
    rw [h8] at this
    omega

theorem caseAlphaEnd_sup_zpowers_el {K E : Subgroup G} {y : G} (hKN : K ≤ cx y) (hy3 : y ^ 3 = 1)
    (hEK : E ≤ K) (hEel : IsElemAbelian 3 E) :
    y ∈ (Subgroup.zpowers y ⊔ E : Subgroup G) ∧ InYK y K (Subgroup.zpowers y ⊔ E) ∧
      IsElemAbelian 3 (Subgroup.zpowers y ⊔ E : Subgroup G) := by
  classical
  have hcomm : ∀ e ∈ E, Commute y e := fun e he =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hKN (hEK he))).symm
  have hcomm' : ∀ e ∈ E, Commute e y := fun e he => (hcomm e he).symm
  let P : Subgroup G :=
    { carrier := {g | ∃ i : ℤ, ∃ e ∈ E, g = y ^ i * e}
      mul_mem' := by
        rintro _ _ ⟨i, e, he, rfl⟩ ⟨j, f, hf, rfl⟩
        refine ⟨i + j, e * f, E.mul_mem he hf, ?_⟩
        have h1 : e * y ^ j = y ^ j * e := ((hcomm' e he).zpow_right j).eq
        calc y ^ i * e * (y ^ j * f) = y ^ i * (e * y ^ j) * f := by simp only [mul_assoc]
          _ = y ^ i * (y ^ j * e) * f := by rw [h1]
          _ = y ^ i * y ^ j * (e * f) := by simp only [mul_assoc]
          _ = y ^ (i + j) * (e * f) := by rw [zpow_add]
      one_mem' := ⟨0, 1, E.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, e, he, rfl⟩
        refine ⟨-i, e⁻¹, E.inv_mem he, ?_⟩
        have h2 : e⁻¹ * y ^ (-i) = y ^ (-i) * e⁻¹ := ((hcomm' e he).zpow_right (-i)).inv_left.eq
        rw [mul_inv_rev, ← zpow_neg, h2] }
  have hyP : y ∈ P := ⟨1, 1, E.one_mem, by simp⟩
  have hEP : E ≤ P := fun e he => ⟨0, e, he, by simp⟩
  have hB'P : Subgroup.zpowers y ⊔ E ≤ P := sup_le (Subgroup.zpowers_le.2 hyP) hEP
  have hInYK : InYK y K (Subgroup.zpowers y ⊔ E) := by
    intro g hg
    obtain ⟨i, e, he, rfl⟩ := hB'P hg
    exact ⟨i, e, hEK he, rfl⟩
  have hkey : ∀ (i j : ℤ) (e f : G), e ∈ E → f ∈ E →
      y ^ i * e * (y ^ j * f) = y ^ j * f * (y ^ i * e) := by
    intro i j e f he hf
    have h1 : e * y ^ j = y ^ j * e := ((hcomm' e he).zpow_right j).eq
    have h2 : f * y ^ i = y ^ i * f := ((hcomm' f hf).zpow_right i).eq
    have h3 : e * f = f * e := isElemAbelian_commute hEel he hf
    have h4 : y ^ i * y ^ j = y ^ j * y ^ i := by rw [← zpow_add, ← zpow_add, add_comm]
    calc y ^ i * e * (y ^ j * f) = y ^ i * (e * y ^ j) * f := by simp only [mul_assoc]
      _ = y ^ i * (y ^ j * e) * f := by rw [h1]
      _ = (y ^ i * y ^ j) * (e * f) := by simp only [mul_assoc]
      _ = (y ^ j * y ^ i) * (f * e) := by rw [h4, h3]
      _ = y ^ j * (y ^ i * f) * e := by simp only [mul_assoc]
      _ = y ^ j * (f * y ^ i) * e := by rw [h2]
      _ = y ^ j * f * (y ^ i * e) := by simp only [mul_assoc]
  have hPcomm : ∀ g ∈ P, ∀ h ∈ P, g * h = h * g := by
    rintro _ ⟨i, e, he, rfl⟩ _ ⟨j, f, hf, rfl⟩
    exact hkey i j e f he hf
  have hPexp : ∀ g ∈ P, g ^ 3 = 1 := by
    rintro _ ⟨i, e, he, rfl⟩
    have hc : Commute (y ^ i) e := (hcomm e he).zpow_left i
    have hyi : (y ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
    rw [hc.mul_pow, hyi, hEel.2 e he, one_mul]
  have hcomm_sub : IsMulCommutative (Subgroup.zpowers y ⊔ E : Subgroup G) :=
    ⟨⟨fun a b => Subtype.ext (hPcomm a.1 (hB'P a.2) b.1 (hB'P b.2))⟩⟩
  have hel : IsElemAbelian 3 (Subgroup.zpowers y ⊔ E : Subgroup G) :=
    ⟨hcomm_sub, fun g hg => hPexp g (hB'P hg)⟩
  exact ⟨Subgroup.mem_sup_left (Subgroup.mem_zpowers y), hInYK, hel⟩

theorem caseAlphaEnd_sup_zpowers {K E : Subgroup G} {y : G} (hKN : K ≤ cx y) (hyK : y ∉ K)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hEK : E ≤ K) (hEel : IsElemAbelian 3 E) :
    y ∈ (Subgroup.zpowers y ⊔ E : Subgroup G) ∧ InYK y K (Subgroup.zpowers y ⊔ E) ∧
      IsElemAbelian 3 (Subgroup.zpowers y ⊔ E : Subgroup G) ∧
      Nat.card (Subgroup.zpowers y ⊔ E : Subgroup G) = 3 * Nat.card E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hyB', hInYK, hel⟩ := caseAlphaEnd_sup_zpowers_el hKN hy3 hEK hEel
  have hcomm : ∀ e ∈ E, Commute y e := fun e he =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hKN (hEK he))).symm
  have hEN : E ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    intro e he
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((hcomm e he).zpow_left k).eq
  have hy_ord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hzy : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hy_ord]
  have hprod := card_sup_mul_card_inf_of_le_normalizer hEN
  rw [hzy] at hprod
  have hinf : Nat.card (Subgroup.zpowers y ⊓ E : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers y ⊓ E : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers y ⊓ E ≤ Subgroup.zpowers y)
      rwa [hzy] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact h1
    · exfalso
      have hEq : Subgroup.zpowers y ⊓ E = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hzy, h3])
      have hyin : y ∈ Subgroup.zpowers y ⊓ E := by
        rw [hEq]
        exact Subgroup.mem_zpowers y
      exact hyK (hEK (Subgroup.mem_inf.1 hyin).2)
  rw [hinf, mul_one] at hprod

  exact ⟨hyB', hInYK, hel, hprod⟩

theorem caseAlphaEnd_card_centMod {B K : Subgroup G} {y : G} (hB : IsElemAbelian 3 B) (hyB : y ∈ B)
    (hy1 : y ≠ 1) (hKN : K ≤ cx y) (hcyc : IsCyclic ↥(B ⊓ centModSubgroup 3 K)) :
    Nat.card ↥(B ⊓ centModSubgroup 3 K) = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : y ^ 3 = 1 := hB.2 y hyB
  have hyC : y ∈ B ⊓ centModSubgroup 3 K := by
    refine ⟨hyB, mem_centModSubgroup.2 ⟨?_, fun l hl => ?_⟩⟩
    · exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun k hk =>
        Subgroup.mem_centralizer_singleton_iff.1 (hKN hk))
    · have h1 : ⁅l, y⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_centralizer_singleton_iff.1 (hKN hl)
      rw [h1]
      exact Subgroup.one_mem _
  have hle : Nat.card ↥(B ⊓ centModSubgroup 3 K) ≤ 3 :=
    caseAlphaEnd_card_le_three hcyc (isElemAbelian_mono hB inf_le_left)
  have hge : 3 ≤ Nat.card ↥(B ⊓ centModSubgroup 3 K) := by
    have h1 := Subgroup.card_le_of_le
      (Subgroup.zpowers_le.2 hyC : Subgroup.zpowers y ≤ B ⊓ centModSubgroup 3 K)
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1] at h1
    exact h1
  omega

theorem caseAlphaEnd_card_ty {B K : Subgroup G} {n : ℕ} (hty : KyCardTy B K n)
    (hC : Nat.card ↥(B ⊓ centModSubgroup 3 K) = 3) :
    (catalogIs (PSimple 3 K) (isU6n n) ∧ Nat.card B = 3 ^ 3 * 3) ∨
      (catalogIs (PSimple 3 K) (isTE6n n) ∧ Nat.card B = 3 ^ 4 * 3) := by
  unfold KyCardTy at hty
  rcases hty with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, by rw [h2, hC]⟩
  · exact Or.inr ⟨h1, by rw [h2, hC]⟩

theorem alpha_center_ne_bot_of_mem {K : Subgroup G} {y : G} (hKN : K ≤ cx y) (hyK : y ∈ K) (hy1 : y ≠ 1)
    (hy3 : y ^ 3 = 1) : Subgroup.center (PQuot 3 K) ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hbot
  have hc : (QuotientGroup.mk (⟨y, hyK⟩ : ↥K) : PQuot 3 K) ∈ Subgroup.center (PQuot 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hKN k.2))
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  have hycore : y ∈ GLAPPrimeCoreOf 3 K := ⟨_, hc, rfl⟩
  have hdvd : 3 ∣ Nat.card (GLAPPrimeCoreOf 3 K) := by
    have h1 : orderOf (⟨y, hycore⟩ : ↥(GLAPPrimeCoreOf 3 K)) ∣ Nat.card (GLAPPrimeCoreOf 3 K) :=
      orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hy3 hy1] at h1
  exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three K hdvd

theorem caseAlphaEnd_bstar_of_not_mem (hin : I1015twoAt G) {B K : Subgroup G} {y : G} {n : ℕ}
    (hB : IsElemAbelian 3 B) (hyB : y ∈ B) (hy1 : y ≠ 1) (hyK : y ∉ K) (hn : Odd n)
    (hKc : GLAPComponent 3 (cx y) K) (hty : KyCardTy B K n)
    (hcyc : IsCyclic ↥(B ⊓ centModSubgroup 3 K)) :
    ∃ B' T₀ : Subgroup G, y ∈ B' ∧ InYK y K B' ∧ IsElemAbelian 3 B' ∧
      Nat.card B' = Nat.card B ∧ T₀ ≤ K ∧ IsPGroup 2 T₀ ∧
      ¬ T₀ ≤ GLAPPrimeCoreOf 3 K ∧ B' ≤ Subgroup.normalizer (T₀ : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : y ^ 3 = 1 := hB.2 y hyB
  have hKN : K ≤ cx y := hKc.1
  have hcases := caseAlphaEnd_card_ty hty (caseAlphaEnd_card_centMod hB hyB hy1 hKN hcyc)
  have hyT : ∀ T : Subgroup G, T ≤ K → y ∈ Subgroup.normalizer (T : Set G) := fun T hTK =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.1 (hKN (hTK ht)))
  rcases hcases with ⟨hU, hBcard⟩ | ⟨hTE, hBcard⟩
  · obtain ⟨E, T, hEK, hEel, hEcard, hTK, hT2, hTO, hEN⟩ := (hin (cx y) K n hKc hn).1 hU
    obtain ⟨hyB', hY, hel, hcard⟩ := caseAlphaEnd_sup_zpowers hKN hyK hy3 hy1 hEK hEel
    refine ⟨Subgroup.zpowers y ⊔ E, T, hyB', hY, hel, ?_, hTK, hT2, hTO, ?_⟩
    · rw [hcard, hEcard, hBcard]
      norm_num
    · exact sup_le (Subgroup.zpowers_le.2 (hyT T hTK)) hEN
  · obtain ⟨E, T, hEK, hEel, hEcard, hTK, hT2, hTO, hEN⟩ := (hin (cx y) K n hKc hn).2 hTE
    obtain ⟨hyB', hY, hel, hcard⟩ := caseAlphaEnd_sup_zpowers hKN hyK hy3 hy1 hEK hEel
    refine ⟨Subgroup.zpowers y ⊔ E, T, hyB', hY, hel, ?_, hTK, hT2, hTO, ?_⟩
    · rw [hcard, hEcard, hBcard]
      norm_num
    · exact sup_le (Subgroup.zpowers_le.2 (hyT T hTK)) hEN

theorem caseAlphaEnd_bstar_of_mem (hin : I1015coverAt G) {B K : Subgroup G} {y : G} {n : ℕ}
    (hB : IsElemAbelian 3 B) (hyB : y ∈ B) (hy1 : y ≠ 1) (hyK : y ∈ K) (hn : Odd n)
    (hKc : GLAPComponent 3 (cx y) K) (hty : KyCardTy B K n)
    (hcyc : IsCyclic ↥(B ⊓ centModSubgroup 3 K)) (hrk : Nat.card B = 3 ^ GLATwoLocalRank 3 G) :
    ∃ B' T₀ : Subgroup G, y ∈ B' ∧ InYK y K B' ∧ IsElemAbelian 3 B' ∧
      Nat.card B' = Nat.card B ∧ T₀ ≤ K ∧ IsPGroup 2 T₀ ∧
      ¬ T₀ ≤ GLAPPrimeCoreOf 3 K ∧ B' ≤ Subgroup.normalizer (T₀ : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : y ^ 3 = 1 := hB.2 y hyB
  have hKN : K ≤ cx y := hKc.1
  have hcases := caseAlphaEnd_card_ty hty (caseAlphaEnd_card_centMod hB hyB hy1 hKN hcyc)
  obtain ⟨-, hU, hTE⟩ := hin (cx y) K n hKc hn (hcases.imp (fun h => h.1) (fun h => h.1))
    (alpha_center_ne_bot_of_mem hKN hyK hy1 hy3)
  obtain ⟨E, T, hEK, hEel, hEcard, hTK, hT2, hTO, hEN⟩ : ∃ E T : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧
      Nat.card E = Nat.card B ∧ T ≤ K ∧ IsPGroup 2 T ∧ ¬ T ≤ GLAPPrimeCoreOf 3 K ∧
      E ≤ Subgroup.normalizer (T : Set G) := by
    rcases hcases with ⟨hU6, hBcard⟩ | ⟨hTE6, hBcard⟩
    · obtain ⟨E, T, hEK, hEel, hEcard, hTK, hT2, hTO, hEN⟩ := hU hU6
      exact ⟨E, T, hEK, hEel, by rw [hEcard, hBcard]; norm_num, hTK, hT2, hTO, hEN⟩
    · obtain ⟨E, T, hEK, hEel, hEcard, hTK, hT2, hTO, hEN⟩ := hTE hTE6
      exact ⟨E, T, hEK, hEel, by rw [hEcard, hBcard]; norm_num, hTK, hT2, hTO, hEN⟩
  obtain ⟨-, -, hel⟩ := caseAlphaEnd_sup_zpowers_el hKN hy3 hEK hEel
  have hTne : T ≠ ⊥ := fun e => hTO (e ▸ bot_le)
  have hyT : y ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.1 (hKN (hTK ht)))
  have hle := card_le_pow_glaTwoLocalRank Nat.prime_three hel hTne hT2
    (sup_le (Subgroup.zpowers_le.2 hyT) hEN)
  rw [← hrk, ← hEcard] at hle
  have heq : E = Subgroup.zpowers y ⊔ E := Subgroup.eq_of_le_of_card_ge le_sup_right hle
  have hyE : y ∈ E := by
    rw [heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  refine ⟨E, T, hyE, ?_, hEel, hEcard, hTK, hT2, hTO, hEN⟩
  intro g hg
  exact ⟨0, g, hEK hg, by simp⟩


theorem alpha_Kf_E (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G} {E₀ F : Subgroup G}
    {y : G} {E K : Subgroup G} (h : Cfg p B x L b) (hd : AlphaData p B x L b a E₀ F y E K) :
    Kf p K E = K := by
  have hp : p.Prime := hc.ctx.prime
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hxE : x ∈ E := hDE hxD
  have hcsE : cs E ≤ cx x := Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hxE))
  have hK_csE : GLAPComponent p (cs E) K := by
    refine glaPComponent_of_isSubnormal' hp ?_ hd.K_comp
    have hsn := isSubnormal_inf hLc.2.1 (cs E)
    rwa [inf_eq_right.2 hcsE] at hsn
  exact closureIn_layer_eq_of_component hp hK_csE hd.K_comp le_rfl

section CBAux

variable {G : Type} [Group G] [Finite G]

private theorem cb_conj_mem {O : Subgroup G} {g x : G} (hg : g ∈ Subgroup.normalizer (O : Set G))
    (hx : x ∈ O) : g * x * g⁻¹ ∈ O :=
  (Subgroup.mem_normalizer_iff.1 hg x).1 hx

private theorem cb_mem_sup_of_comm {P Q : Subgroup G} (hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) {x : G}
    (hx : x ∈ P ⊔ Q) : ∃ p ∈ P, ∃ q ∈ Q, x = p * q := by
  let S : Subgroup G :=
    { carrier := {x | ∃ p ∈ P, ∃ q ∈ Q, x = p * q}
      one_mem' := ⟨1, P.one_mem, 1, Q.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, q, hq, rfl⟩ ⟨p', hp', q', hq', rfl⟩
        refine ⟨p * p', P.mul_mem hp hp', q * q', Q.mul_mem hq hq', ?_⟩
        calc p * q * (p' * q') = p * (q * p') * q' := by group
          _ = p * (p' * q) * q' := by rw [hPQ p' hp' q hq]
          _ = p * p' * (q * q') := by group
      inv_mem' := by
        rintro _ ⟨p, hp, q, hq, rfl⟩
        have hc : p⁻¹ * q⁻¹ = q⁻¹ * p⁻¹ := by
          calc p⁻¹ * q⁻¹ = (q * p)⁻¹ := by group
            _ = (p * q)⁻¹ := by rw [hPQ p hp q hq]
            _ = q⁻¹ * p⁻¹ := by group
        exact ⟨p⁻¹, P.inv_mem hp, q⁻¹, Q.inv_mem hq, by rw [mul_inv_rev, hc]⟩ }
  have hP : P ≤ S := fun p hp => ⟨p, hp, 1, Q.one_mem, by simp⟩
  have hQ : Q ≤ S := fun q hq => ⟨1, P.one_mem, q, hq, by simp⟩
  obtain ⟨p, hp, q, hq, h⟩ := (sup_le hP hQ : P ⊔ Q ≤ S) hx
  exact ⟨p, hp, q, hq, h⟩

private theorem cb_closureIn_le {I H Z : Subgroup G} (hI : I ≤ Z)
    (hH : H ≤ Subgroup.normalizer (Z : Set G)) : closureIn I H ≤ Z := by
  unfold closureIn
  refine iSup₂_le fun h hh => ?_
  rintro _ ⟨i, hi, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 (hH hh) i).1 (hI hi)

private theorem cb_Kf_le_cs {K F : Subgroup G} (hK : K ≤ Subgroup.centralizer (F : Set G)) :
    closureIn K (GLAPLayer 3 (Subgroup.centralizer (F : Set G))) ≤ Subgroup.centralizer (F : Set G) :=
  cb_closureIn_le hK (fun _ hg => Subgroup.le_normalizer (layer_le 3 _ hg))

private theorem cb_le_normalizer_of_comm {H S : Subgroup G}
    (h : ∀ g ∈ H, ∀ s ∈ S, g * s = s * g) : H ≤ Subgroup.normalizer (S : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have hgk := h g hg k hk
    rw [hgk, mul_inv_cancel_right]
    exact hk
  · intro hk
    have hs := h g⁻¹ (H.inv_mem hg) _ hk
    have hkeq : k = g * k * g⁻¹ := by
      calc k = g⁻¹ * (g * k * g⁻¹) * g := by group
        _ = (g * k * g⁻¹) * g⁻¹ * g := by rw [hs]
        _ = g * k * g⁻¹ := by group
    rwa [hkeq.symm] at hk

private theorem cb_nine_le_of_not_cyclic {H : Subgroup G} (hel : IsElemAbelian 3 H)
    (hnc : ¬ IsCyclic ↥H) : 9 ≤ Nat.card H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hel
  by_contra hlt
  push Not at hlt
  have hc2 : c < 2 := by
    by_contra h2
    push Not at h2
    have h9 : 9 ≤ 3 ^ c := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ c := Nat.pow_le_pow_right (by norm_num) h2
    omega
  apply hnc
  interval_cases c
  · have h1 : Nat.card ↥H = 1 := by simpa using hc
    haveI : Subsingleton ↥H := (Nat.card_eq_one_iff_unique.1 h1).1
    exact isCyclic_of_subsingleton
  · haveI : Fact (Nat.card ↥H).Prime := ⟨by rw [hc]; norm_num⟩
    exact isCyclic_of_prime_card (by rw [hc])

private theorem cb_not_dvd_of_le {P N : Subgroup G} (hPN : P ≤ N) (hN : ¬ 3 ∣ Nat.card N) :
    ¬ 3 ∣ Nat.card P :=
  fun h => hN (h.trans (Subgroup.card_dvd_of_le hPN))

private theorem cb_le_core {L P : Subgroup G} (hPL : P ≤ L)
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) (hP : ¬ 3 ∣ Nat.card P) :
    P ≤ GLAPPrimeCoreOf 3 L :=
  le_glaPPrimeCoreOf_of_le_normalizer hPL hLP ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hP)

private theorem cb_normalizes_inf {L Y : Subgroup G} (hLY : L ≤ Y) :
    L ≤ Subgroup.normalizer ((L ⊓ GLAPPrimeCoreOf 3 Y : Subgroup G) : Set G) := by
  intro m hm
  have hmN : m ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 Y : Set G) :=
    le_normalizer_glaPPrimeCoreOf 3 Y (hLY hm)
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · rintro ⟨hkL, hkN⟩
    exact ⟨L.mul_mem (L.mul_mem hm hkL) (L.inv_mem hm), (Subgroup.mem_normalizer_iff.1 hmN k).1 hkN⟩
  · rintro ⟨hkL, hkN⟩
    have hm' : m⁻¹ ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 Y : Set G) :=
      Subgroup.inv_mem _ hmN
    have hkL' : k = m⁻¹ * (m * k * m⁻¹) * m⁻¹⁻¹ := by group
    have hkN' : m⁻¹ * (m * k * m⁻¹) * m⁻¹⁻¹ ∈ GLAPPrimeCoreOf 3 Y :=
      (Subgroup.mem_normalizer_iff.1 hm' (m * k * m⁻¹)).1 hkN
    refine ⟨?_, ?_⟩
    · rw [hkL']
      exact L.mul_mem (L.mul_mem (L.inv_mem hm) hkL) (L.inv_mem (L.inv_mem hm))
    · rw [hkL']
      exact hkN'

private theorem cb_inducesInner {L : Subgroup G} {g : G}
    (h : ∀ m ∈ L, ⁅m, g⁻¹⁆ ∈ GLAPPrimeCoreOf 3 L) : InducesInnerMod 3 L g := by
  unfold InducesInnerMod
  refine ⟨1, L.one_mem, fun y hy => ?_⟩
  have := h y⁻¹ (L.inv_mem hy)
  convert this using 1
  simp only [commutatorElement_def]
  group

private theorem cb_mem_core_iff {K : Subgroup G} (w : ↥K) :
    w ∈ GLAPPrimeCore 3 ↥K ↔ ((w : ↥K) : G) ∈ GLAPPrimeCoreOf 3 K := by
  constructor
  · intro hw
    exact ⟨w, hw, rfl⟩
  · rintro ⟨u, hu, huw⟩
    have : u = w := Subtype.ext huw
    rwa [this] at hu

private theorem cb_barX_eq_bot_of_le {X T : Subgroup G} (h : T ≤ GLAPPrimeCoreOf 3 X) :
    barX 3 X T = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨t, ht, rfl⟩
  rw [Subgroup.mem_bot]
  have htO : ((t : ↥X) : G) ∈ GLAPPrimeCoreOf 3 X := h (Subgroup.mem_subgroupOf.1 ht)
  exact (QuotientGroup.eq_one_iff _).2 ((cb_mem_core_iff t).2 htO)

private theorem cb_le_core_of_barX_eq_bot {X T : Subgroup G} (hTX : T ≤ X) (h : barX 3 X T = ⊥) :
    T ≤ GLAPPrimeCoreOf 3 X := by
  intro t ht
  have hmem : (QuotientGroup.mk (⟨t, hTX ht⟩ : ↥X) : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ barX 3 X T :=
    ⟨⟨t, hTX ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact (cb_mem_core_iff ⟨t, hTX ht⟩).1 ((QuotientGroup.eq_one_iff _).1 hmem)

private theorem cb_mem_normalizer_inf {L S : Subgroup G} {g : G}
    (h1 : g ∈ Subgroup.normalizer (L : Set G)) (h2 : g ∈ Subgroup.normalizer (S : Set G)) :
    g ∈ Subgroup.normalizer ((L ⊓ S : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
  intro k
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (h1 k) (h2 k)

private theorem cb_cover_of_centMod {p : ℕ} (hp : p.Prime) {L A : Subgroup G} (ha : IsPGroup p A)
    (hA : A ≤ centModSubgroup p L) : (L ⊓ Subgroup.centralizer (A : Set G)) ⊔ GLAPPrimeCoreOf p L = L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set O := GLAPPrimeCoreOf p L with hO
  apply le_antisymm (sup_le inf_le_left (Subgroup.map_subtype_le _))
  intro l hl
  have hmem : ∀ g ∈ A, ∀ o ∈ O, l⁻¹ * (g * (l * o) * g⁻¹) ∈ O := by
    intro g hg o ho
    have hgC := hA hg
    have h1 : ⁅l⁻¹, g⁆ ∈ O := hgC.2 _ (L.inv_mem hl)
    have h2 : g * o * g⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p L hgC.1) o).1 ho
    have h3 : l⁻¹ * (g * (l * o) * g⁻¹) = ⁅l⁻¹, g⁆ * (g * o * g⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact O.mul_mem h1 h2
  letI act : MulAction A O :=
    { smul := fun g o => ⟨l⁻¹ * ((g : G) * (l * (o : G)) * (g : G)⁻¹), hmem g g.2 o o.2 ⟩
      one_smul := fun o => Subtype.ext (show l⁻¹ * (((1 : A) : G) * (l * (o : G)) *
          ((1 : A) : G)⁻¹) = (o : G) by simp)
      mul_smul := fun g h o => Subtype.ext (show l⁻¹ * (((g * h : A) : G) * (l * (o : G)) *
          ((g * h : A) : G)⁻¹) = l⁻¹ * ((g : G) * (l * (l⁻¹ * ((h : G) * (l * (o : G)) *
          (h : G)⁻¹))) * (g : G)⁻¹) by simp only [Subgroup.coe_mul]; group) }
  have hOp : ¬ p ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp L
  obtain ⟨o, ho⟩ := ha.nonempty_fixed_point_of_prime_not_dvd_card O hOp
  have hfa : ∀ g ∈ A, l⁻¹ * (g * (l * (o : G)) * g⁻¹) = o := fun g hg =>
    congrArg Subtype.val (ho ⟨g, hg⟩)
  have hyC : l * (o : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' := hfa g hg
    have hy : g * (l * (o : G)) * g⁻¹ = l * (o : G) := by
      calc g * (l * (o : G)) * g⁻¹ = l * (l⁻¹ * (g * (l * (o : G)) * g⁻¹)) := by group
        _ = l * o := by rw [hg']
    calc g * (l * (o : G)) = g * (l * (o : G)) * g⁻¹ * g := by group
      _ = l * (o : G) * g := by rw [hy]
  have hyL : l * (o : G) ∈ L := L.mul_mem hl (Subgroup.map_subtype_le _ o.2)
  have hl' : l = (l * (o : G)) * (o : G)⁻¹ := by group
  rw [hl']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hyL, hyC⟩) (Subgroup.mem_sup_right (O.inv_mem o.2))

private theorem cb_mem_GLBConj {K : Subgroup G} {c k : G} (hk : k ∈ K) : c⁻¹ * k * c ∈ GLBConj c K :=
  Subgroup.mem_map.2 ⟨k, hk, by simp [MulAut.conj_apply]⟩

end CBAux

theorem alpha_layer_EC (hc : S10Ctx G 3) (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg 3 B x L b) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData 3 B x L b a E₀ F y E K)
    (hBN : B ≤ Subgroup.normalizer ((Kf 3 K (Subgroup.zpowers y) : Subgroup G) : Set G))
    {C : Subgroup G} (hCB : C ≤ B) (hCc : ∀ g ∈ C, CentMod 3 (Kf 3 K (Subgroup.zpowers y)) g) :
    GLAPLayer 3 (L ⊓ cs (E ⊔ C)) ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hB : IsElemAbelian 3 B := B_el h
  have hcommB : ∀ g ∈ B, ∀ g' ∈ B, g * g' = g' * g :=
    fun g hg g' hg' => isElemAbelian_commute hB hg hg'
  have hNL : B ≤ Subgroup.normalizer (L : Set G) := sstar_norm h.star
  have hEB : E ≤ B := by
    rw [hd.E_def]
    exact sup_le (hd.D_E₀.trans hd.E₀_B) (Subgroup.zpowers_le.2 (hd.E₀_B (hd.F_E₀ hd.y_F)))
  have hKc : GLAPComponent 3 (L ⊓ Subgroup.centralizer (E : Set G)) K := hd.K_comp
  set X := L ⊓ Subgroup.centralizer (E : Set G) with hXdef
  set Y := Kf 3 K (Subgroup.zpowers y) with hYdef
  have hKX : K ≤ X := hKc.1
  have hKcs : K ≤ Subgroup.centralizer (E : Set G) := hKX.trans inf_le_right
  have hKY : K ≤ Y := le_closureIn_self K _
  have hNY : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 Y) := not_dvd_card_glaPPrimeCoreOf hp Y
  have hNX : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 X) := not_dvd_card_glaPPrimeCoreOf hp X
  have hK3 : 3 ∣ Nat.card K := by
    by_contra hK3
    have hcop : Nat.Coprime 3 (Nat.card K) := (Nat.Prime.coprime_iff_not_dvd hp).2 hK3
    have hself : K ≤ GLAPPrimeCoreOf 3 K :=
      le_glaPPrimeCoreOf_of_le_normalizer le_rfl Subgroup.le_normalizer hcop
    have hinf := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hKc.2.1
    have hKO : K ≤ GLAPPrimeCoreOf 3 X := by
      intro k hk
      have hk' : k ∈ K ⊓ GLAPPrimeCoreOf 3 X := by
        rw [hinf]
        exact hself hk
      exact (Subgroup.mem_inf.1 hk').2
    have hbot := cb_barX_eq_bot_of_le hKO
    have hnt := isQuasisimple_nontrivial hKc.2.2.1.2.2
    exact ((Subgroup.nontrivial_iff_ne_bot _).1 hnt) hbot
  have hCX : ∀ c ∈ C, c ∈ Subgroup.normalizer (X : Set G) := by
    intro c hc
    have hcB : c ∈ B := hCB hc
    have hcE : c ∈ Subgroup.centralizer (E : Set G) :=
      Subgroup.mem_centralizer_iff.2 (fun e he => (hcommB c hcB e (hEB he)).symm)
    exact cb_mem_normalizer_inf (hNL hcB) (Subgroup.le_normalizer hcE)
  have hKeq : ∀ c ∈ C, GLBConj c K = K := by
    intro c hc
    have hcX := hCX c hc
    have hcY : c ∈ Subgroup.normalizer (Y : Set G) := hBN (hCB hc)
    have hKCc : GLAPComponent 3 X (GLBConj c K) := by
      have h1 := glaPComponent_gLBConj hKc c
      rwa [mem_normalizer_iff_gLBConj_eq.1 hcX] at h1
    by_contra hne
    have hKCY : GLBConj c K ≤ Y := by
      have h1 : GLBConj c K ≤ GLBConj c Y := Subgroup.map_mono hKY
      rwa [mem_normalizer_iff_gLBConj_eq.1 hcY] at h1
    have hKCX : GLBConj c K ≤ X := hKCc.1
    have hbne : barX 3 X K ≠ barX 3 X (GLBConj c K) := fun heq =>
      hne (glaPComponent_unique hKc hKCc heq).symm
    have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne
      (barX 3 X K) (barX 3 X (GLBConj c K)) hKc.2.2.1 hKCc.2.2.1 hbne
    have hTX : (⁅K, GLBConj c K⁆ : Subgroup G) ≤ X := commutator_le_of_le' hKX hKCX
    have hTY : (⁅K, GLBConj c K⁆ : Subgroup G) ≤ Y := commutator_le_of_le' hKY hKCY
    have hTbar : barX 3 X (⁅K, GLBConj c K⁆ : Subgroup G) = ⊥ := by
      rw [barX_commutator 3 hKX hKCX, hcomm]
    have hTO : (⁅K, GLBConj c K⁆ : Subgroup G) ≤ GLAPPrimeCoreOf 3 X := cb_le_core_of_barX_eq_bot hTX hTbar
    have hT3 : ¬ 3 ∣ Nat.card (⁅K, GLBConj c K⁆ : Subgroup G) := fun h3 =>
      hNX (h3.trans (Subgroup.card_dvd_of_le hTO))
    have hdecomp : ∀ k ∈ K, ∃ k' ∈ GLBConj c K, ∃ n ∈ GLAPPrimeCoreOf 3 Y, k = k' * n := by
      intro k hk
      have hn1 : ⁅k⁻¹, c⁆ ∈ GLAPPrimeCoreOf 3 Y :=
        (mem_centModSubgroup.1 (centMod_iff.1 (hCc c hc))).2 k⁻¹ (Y.inv_mem (hKY hk))
      have hcinv : c⁻¹ ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 Y : Set G) :=
        normalizer_le_normalizer_glaPPrimeCoreOf 3 Y (Subgroup.inv_mem _ hcY)
      refine ⟨c⁻¹ * k * c, cb_mem_GLBConj hk, c⁻¹ * ⁅k⁻¹, c⁆ * c⁻¹⁻¹,
        cb_conj_mem hcinv hn1, ?_⟩
      simp only [commutatorElement_def]
      group
    have hsub : ⁅K, K⁆ ≤ (⁅K, GLBConj c K⁆ : Subgroup G) ⊔ GLAPPrimeCoreOf 3 Y := by
      apply Subgroup.commutator_le.2
      intro k₁ hk₁ k₂ hk₂
      obtain ⟨k', hk', n, hn, rfl⟩ := hdecomp k₂ hk₂
      have hT : ⁅k₁, k'⁆ ∈ (⁅K, GLBConj c K⁆ : Subgroup G) := Subgroup.commutator_mem_commutator hk₁ hk'
      have hcomm1 : ⁅k₁, n⁆ ∈ GLAPPrimeCoreOf 3 Y := by
        have h2 := cb_conj_mem (le_normalizer_glaPPrimeCoreOf 3 Y (hKY hk₁)) hn
        have e : ⁅k₁, n⁆ = (k₁ * n * k₁⁻¹) * n⁻¹ := by
          simp only [commutatorElement_def]
        rw [e]
        exact (GLAPPrimeCoreOf 3 Y).mul_mem h2 ((GLAPPrimeCoreOf 3 Y).inv_mem hn)
      have hNn : k' * ⁅k₁, n⁆ * k'⁻¹ ∈ GLAPPrimeCoreOf 3 Y :=
        cb_conj_mem (le_normalizer_glaPPrimeCoreOf 3 Y (hKCY hk')) hcomm1
      have e : ⁅k₁, k' * n⁆ = ⁅k₁, k'⁆ * (k' * ⁅k₁, n⁆ * k'⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hT) (Subgroup.mem_sup_right hNn)
    have hKle : K ≤ GLAPPrimeCoreOf 3 Y ⊔ (⁅K, GLBConj c K⁆ : Subgroup G) := by
      rw [sup_comm]
      have h := hsub
      rwa [glaPComponent_perfect hKc] at h
    have hTN : (⁅K, GLBConj c K⁆ : Subgroup G) ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 Y : Set G) :=
      hTY.trans (le_normalizer_glaPPrimeCoreOf 3 Y)
    have hcard := card_sup_mul_card_inf_of_le_normalizer hTN
    have hdvd : Nat.card K ∣ Nat.card ((GLAPPrimeCoreOf 3 Y ⊔ (⁅K, GLBConj c K⁆ : Subgroup G) : Subgroup G)) :=
      Subgroup.card_dvd_of_le hKle
    have h3S : 3 ∣ Nat.card ((GLAPPrimeCoreOf 3 Y ⊔ (⁅K, GLBConj c K⁆ : Subgroup G) : Subgroup G)) := hK3.trans hdvd
    have h3P : 3 ∣ Nat.card (GLAPPrimeCoreOf 3 Y) * Nat.card (⁅K, GLBConj c K⁆ : Subgroup G) := by
      rw [← hcard]
      exact Dvd.dvd.mul_right h3S _
    rcases (Nat.Prime.dvd_mul hp).1 h3P with h4 | h4
    · exact hNY h4
    · exact hT3 h4
  have hCK : ∀ c ∈ C, c ∈ centModSubgroup 3 K := by
    intro c hc
    have hNK : c ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_gLBConj_eq.2 (hKeq c hc)
    refine mem_centModSubgroup.2 ⟨hNK, fun l hl => ?_⟩
    have hlc : ⁅l, c⁆ ∈ K ⊓ GLAPPrimeCoreOf 3 Y := by
      refine ⟨?_, (mem_centModSubgroup.1 (centMod_iff.1 (hCc c hc))).2 l (hKY hl)⟩
      rw [commutatorElement_def]
      have e : l * c * l⁻¹ * c⁻¹ = l * (c * l⁻¹ * c⁻¹) := by group
      rw [e]
      exact K.mul_mem hl ((Subgroup.mem_normalizer_iff.1 hNK l⁻¹).1 (K.inv_mem hl))
    exact le_glaPPrimeCoreOf_of_le_normalizer inf_le_left (cb_normalizes_inf hKY)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (cb_not_dvd_of_le inf_le_right hNY)) hlc
  have hEK : E ≤ centModSubgroup 3 K := by
    intro e he
    have hcomm' : ∀ g ∈ E, ∀ s ∈ K, g * s = s * g :=
      fun g hg s hs => Subgroup.mem_centralizer_iff.1 (hKcs hs) g hg
    have hNe : e ∈ Subgroup.normalizer (K : Set G) :=
      cb_le_normalizer_of_comm (H := E) (S := K) hcomm' he
    refine mem_centModSubgroup.2 ⟨hNe, fun l hl => ?_⟩
    have h1 : ⁅l, e⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hcomm' e he l hl).symm
    rw [h1]
    exact (GLAPPrimeCoreOf 3 K).one_mem
  have hAK : E ⊔ C ≤ centModSubgroup 3 K := sup_le hEK (fun c hc => hCK c hc)
  have hAel : IsElemAbelian 3 (E ⊔ C : Subgroup G) := isElemAbelian_mono hB (sup_le hEB hCB)
  have hAp : IsPGroup 3 (E ⊔ C : Subgroup G) := isPGroup_of_isElemAbelian hAel
  have hcov := cb_cover_of_centMod hp hAp hAK
  have hWK : K ⊓ Subgroup.centralizer ((E ⊔ C : Subgroup G) : Set G) ≤ K := inf_le_left
  obtain ⟨-, ⟨eW⟩⟩ := cover_facts hp hWK hcov
  have hPQK : CFSG.Open.IsQuasisimple (PQuot 3 K) := isQuasisimple_pQuot_of_glaPComponent hp hKc
  have hPQW : CFSG.Open.IsQuasisimple (PQuot 3 (K ⊓ Subgroup.centralizer ((E ⊔ C : Subgroup G) : Set G))) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eW.symm hPQK
  obtain ⟨J, hJ, hJbar⟩ := exists_glaPComponent_of_isQuasisimple hPQW
  have hcsA : Subgroup.centralizer ((E ⊔ C : Subgroup G) : Set G) ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left)
  have hsn : IsSubnormal (K ⊓ Subgroup.centralizer ((E ⊔ C : Subgroup G) : Set G))
      (L ⊓ Subgroup.centralizer ((E ⊔ C : Subgroup G) : Set G)) := by
    have h1 := isSubnormal_inf hKc.2.1 (Subgroup.centralizer ((E ⊔ C : Subgroup G) : Set G))
    have e : X ⊓ Subgroup.centralizer ((E ⊔ C : Subgroup G) : Set G) =
        L ⊓ Subgroup.centralizer ((E ⊔ C : Subgroup G) : Set G) := by
      rw [hXdef, inf_assoc, inf_eq_right.2 hcsA]
    rw [e] at h1
    exact h1
  have hJ' : GLAPComponent 3 (L ⊓ Subgroup.centralizer ((E ⊔ C : Subgroup G) : Set G)) J :=
    glaPComponent_of_isSubnormal' hp hsn hJ
  intro hLayer
  have hJle : J ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer ((E ⊔ C : Subgroup G) : Set G)) :=
    le_sSup hJ'
  rw [hLayer] at hJle
  have hJbot : J = ⊥ := le_bot_iff.1 hJle
  have hbarbot := cb_barX_eq_bot_of_le (X := K ⊓ Subgroup.centralizer ((E ⊔ C : Subgroup G) : Set G))
    (T := ⊥) bot_le
  rw [hJbot, hbarbot] at hJbar
  have hnt := isQuasisimple_nontrivial hPQW
  have hne : (⊤ : Subgroup (PQuot 3 (K ⊓ Subgroup.centralizer ((E ⊔ C : Subgroup G) : Set G)))) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  exact hne hJbar.symm


theorem alpha_CB_cyclic (hc : S10Ctx G 3) (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg 3 B x L b) (ac : AlphaCtx G 3 B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData 3 B x L b a E₀ F y E K) (hkay : AlphaKay 3 x a y K)
    (hky : AlphaKy 3 x a y K) (hnot : ¬ IsEssential 3 B y)
    (hBN : B ≤ Subgroup.normalizer ((Kf 3 K (Subgroup.zpowers y) : Subgroup G) : Set G)) :
    IsCyclic ↥(B ⊓ centModSubgroup 3 (Kf 3 K (Subgroup.zpowers y))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haut := hin.l105.l104.lemma102.aut
  have hS := sstar_triple h.star
  have hbmax : GLAIsBmax 3 B := hS.1
  have hB : IsElemAbelian 3 B := B_el h
  obtain ⟨hDB, hDel, hDc⟩ := dgrp_facts hc h
  have hyB : y ∈ B := hd.E₀_B (hd.F_E₀ hd.y_F)
  have hy1 : y ≠ 1 := hd.y_ne
  have hy3 : y ^ 3 = 1 := hB.2 y hyB
  have ha1 : a ≠ 1 := ac.ne_one
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have haD : a ∈ Dgrp b x := ac.mem
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have haB : a ∈ B := hDB haD
  have hxB : x ∈ B := hDB hxD
  have ha3 : a ^ (3 : ℤ) = 1 := by exact_mod_cast hB.2 a haB
  have hx3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hB.2 x hxB
  have hcommB : ∀ g ∈ B, ∀ g' ∈ B, g * g' = g' * g :=
    fun g hg g' hg' => isElemAbelian_commute hB hg hg'
  have hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a :=
    fun he => ac.not_x (he ▸ Subgroup.mem_zpowers a)
  have hza_B : Subgroup.zpowers a ≤ B := Subgroup.zpowers_le.2 haB
  have hzx_B : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 hxB
  have hzy_B : Subgroup.zpowers y ≤ B := Subgroup.zpowers_le.2 hyB
  have hDeq : Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers x := by
    have hza : Subgroup.zpowers a ≤ Dgrp b x := Subgroup.zpowers_le.2 haD
    have hzx : Subgroup.zpowers x ≤ Dgrp b x := Subgroup.zpowers_le.2 hxD
    have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
      cb_le_normalizer_of_comm (fun g hg s hs => hcommB g (hzx_B hg) s (hza_B hs))
    have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers x = ⊥ := by
      rw [eq_bot_iff]
      rintro g ⟨h1, h2⟩
      rw [Subgroup.mem_bot]
      by_contra hg1
      have hgo : orderOf g = 3 := by
        have hg3 : g ^ 3 = 1 := hB.2 g (hza_B h1)
        rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hg3) with h' | h'
        · exact absurd (orderOf_eq_one_iff.1 h') hg1
        · exact h'
      have e1 : Subgroup.zpowers g = Subgroup.zpowers a := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 h1)
        rw [Nat.card_zpowers, Nat.card_zpowers, hgo, orderOf_eq_prime (hB.2 a haB) ha1]
      have e2 : Subgroup.zpowers g = Subgroup.zpowers x := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 h2)
        rw [Nat.card_zpowers, Nat.card_zpowers, hgo, orderOf_eq_prime (hB.2 x hxB) hx1]
      exact hxa (e2.symm.trans e1)
    have hcardS : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers x : Subgroup G) = 3 ^ 2 := by
      have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
        orderOf_eq_prime (hB.2 a haB) ha1, orderOf_eq_prime (hB.2 x hxB) hx1] at h1
      rw [h1]
      norm_num
    exact (Subgroup.eq_of_le_of_card_ge (sup_le hza hzx) (hDc.trans hcardS.symm).le).symm
  have hDform : ∀ d ∈ Dgrp b x, ∃ i j : ℤ, d = a ^ i * x ^ j := by
    intro d hd'
    rw [hDeq] at hd'
    obtain ⟨p, hp', q, hq', rfl⟩ := cb_mem_sup_of_comm
      (fun p hp'' q hq'' => hcommB p (hza_B hp'') q (hzx_B hq'')) hd'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq'
    exact ⟨i, j, rfl⟩
  set Ky := Kf 3 K (Subgroup.zpowers y) with hKy
  set C := B ⊓ centModSubgroup 3 Ky with hC
  set N := GLAPPrimeCoreOf 3 Ky with hNdef
  set M := Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) with hMdef
  set N' := Kf 3 K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) with hN'def
  by_contra hnc
  have hNcop : ¬ 3 ∣ Nat.card N := not_dvd_card_glaPPrimeCoreOf Nat.prime_three Ky
  have hKcs : K ≤ Subgroup.centralizer (E : Set G) := hd.K_comp.1.trans inf_le_right
  have hDE : Dgrp b x ≤ E := by
    rw [hd.E_def]
    exact le_sup_left
  have hyE : y ∈ E := by
    rw [hd.E_def]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE haD
  have hxE : x ∈ E := hDE hxD
  have hEB : E ≤ B := by
    rw [hd.E_def]
    exact sup_le hDB (Subgroup.zpowers_le.2 hyB)
  have hFE : Subgroup.zpowers a ⊔ Subgroup.zpowers y ≤ E :=
    sup_le (Subgroup.zpowers_le.2 haE) (Subgroup.zpowers_le.2 hyE)
  have hFxyE : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ E :=
    sup_le (Subgroup.zpowers_le.2 hxE) (Subgroup.zpowers_le.2 hyE)
  have hMcs : M ≤ Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) :=
    cb_Kf_le_cs (hKcs.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hFE)))
  have hMKy : M ≤ Ky := (hky.Kay_comp.1).trans inf_le_left
  have hN'Ky : N' ≤ Ky := (hky.Kxy_comp.1).trans inf_le_left
  have hx_N_M : x ∈ Subgroup.normalizer (M : Set G) := hkay.x_acts.1.1
  have ha_N_N' : a ∈ Subgroup.normalizer (N' : Set G) := hkay.a_acts.1
  have hMcomm : ∀ m ∈ M, Commute a m := fun m hm =>
    Subgroup.mem_centralizer_iff.1 (hMcs hm) a (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hyN : y ∈ Subgroup.normalizer (Ky : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun z hz =>
      (Subgroup.mem_centralizer_singleton_iff.1 (Ky_le_cx hd hz)))
  have hyC : y ∈ C := by
    refine ⟨hyB, mem_centModSubgroup.2 ⟨hyN, fun l hl => ?_⟩⟩
    have hly : ⁅l, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_singleton_iff.1 (Ky_le_cx hd hl))
    rw [hly]
    exact N.one_mem
  have hCel : IsElemAbelian 3 C := isElemAbelian_mono hB inf_le_left
  have hC9 : 9 ≤ Nat.card C := cb_nine_le_of_not_cyclic hCel hnc
  have hCc : ∀ g ∈ C, CentMod 3 Ky g := fun g hg => centMod_iff.2 (Subgroup.mem_inf.1 hg).2
  have hcore_M : ∀ i j : ℤ, a ^ i * x ^ j ∈ C → ∀ m ∈ M, ⁅m, x ^ j⁆ ∈ GLAPPrimeCoreOf 3 M := by
    intro i j hdC m hm
    have hdC' := mem_centModSubgroup.1 (Subgroup.mem_inf.1 hdC).2
    have hmd : ⁅m, a ^ i * x ^ j⁆ ∈ N := hdC'.2 m (hMKy hm)
    have hma : m * a ^ i = a ^ i * m := ((hMcomm m hm).zpow_left i).symm.eq
    have hconj : ⁅m, a ^ i * x ^ j⁆ = a ^ i * ⁅m, x ^ j⁆ * (a ^ i)⁻¹ := by
      simp only [commutatorElement_def]
      rw [mul_inv_rev]
      calc m * (a ^ i * x ^ j) * m⁻¹ * ((x ^ j)⁻¹ * (a ^ i)⁻¹)
          = (m * a ^ i) * x ^ j * m⁻¹ * ((x ^ j)⁻¹ * (a ^ i)⁻¹) := by group
        _ = (a ^ i * m) * x ^ j * m⁻¹ * ((x ^ j)⁻¹ * (a ^ i)⁻¹) := by rw [hma]
        _ = a ^ i * (m * x ^ j * m⁻¹ * (x ^ j)⁻¹) * (a ^ i)⁻¹ := by group
    have hinv : (a ^ i)⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
      normalizer_le_normalizer_glaPPrimeCoreOf 3 Ky (hBN (B.inv_mem (zpow_mem haB i)))
    have hN_part : ⁅m, x ^ j⁆ ∈ N := by
      have h1 := cb_conj_mem hinv hmd
      have e : ⁅m, x ^ j⁆ = (a ^ i)⁻¹ * ⁅m, a ^ i * x ^ j⁆ * (a ^ i)⁻¹⁻¹ := by
        rw [hconj]
        group
      rw [e]
      exact h1
    have hM_part : ⁅m, x ^ j⁆ ∈ M := by
      have h2 : x ^ j * m⁻¹ * (x ^ j)⁻¹ ∈ M :=
        (Subgroup.mem_normalizer_iff.1 (zpow_mem hx_N_M j) m⁻¹).1 (M.inv_mem hm)
      have e2 : ⁅m, x ^ j⁆ = m * (x ^ j * m⁻¹ * (x ^ j)⁻¹) := by
        simp only [commutatorElement_def, mul_assoc]
      rw [e2]
      exact M.mul_mem hm h2
    exact cb_le_core (L := M) (P := M ⊓ N) inf_le_left (cb_normalizes_inf hMKy)
      (cb_not_dvd_of_le inf_le_right hNcop) ⟨hM_part, hN_part⟩ 
  have hcore_N : ∀ i : ℤ, a ^ i ∈ C → ∀ m ∈ N', ⁅m, a ^ i⁆ ∈ GLAPPrimeCoreOf 3 N' := by
    intro i hiC m hm
    have hmd : ⁅m, a ^ i⁆ ∈ N := (mem_centModSubgroup.1 (Subgroup.mem_inf.1 hiC).2).2 m (hN'Ky hm)
    have hN'part : ⁅m, a ^ i⁆ ∈ N' := by
      have e : ⁅m, a ^ i⁆ = m * (a ^ i * m⁻¹ * (a ^ i)⁻¹) := by
        simp only [commutatorElement_def, mul_assoc]
      rw [e]
      exact N'.mul_mem hm ((Subgroup.mem_normalizer_iff.1 (zpow_mem ha_N_N' i) m⁻¹).1 (N'.inv_mem hm))
    exact cb_le_core (L := N') (P := N' ⊓ N) inf_le_left (cb_normalizes_inf hN'Ky)
      (cb_not_dvd_of_le inf_le_right hNcop) ⟨hN'part, hmd⟩
  have hP4 : ∀ i j : ℤ, a ^ i * x ^ j ∈ C → (3 : ℤ) ∣ j := by
    intro i j hdC
    by_contra hj
    have hai : a ^ i ∈ B := zpow_mem haB i
    have hxj : x ^ j ∈ B := zpow_mem hxB j
    have hdinv : a ^ (-i) * x ^ (-j) ∈ C := by
      have e : a ^ (-i) * x ^ (-j) = (a ^ i * x ^ j)⁻¹ := by
        calc a ^ (-i) * x ^ (-j) = (a ^ i)⁻¹ * (x ^ j)⁻¹ := by rw [zpow_neg, zpow_neg]
          _ = (x ^ j * a ^ i)⁻¹ := by group
          _ = (a ^ i * x ^ j)⁻¹ := by rw [hcommB (a ^ i) hai (x ^ j) hxj]
      rw [e]
      exact C.inv_mem hdC
    have hinn : InducesInnerMod 3 M (x ^ j) := by
      apply cb_inducesInner
      intro m hm
      rw [← zpow_neg]
      exact hcore_M (-i) (-j) hdinv m hm
    have hJ : InnDiagOn 3 (Subgroup.zpowers (x ^ j)) M :=
      haut.inner_innDiag _ M (x ^ j) hkay.Kay_single hkay.chev_ay (zpow_mem hkay.x_acts.1.1 j) hinn
    have hmod : j % 3 = 1 ∨ j % 3 = 2 := by omega
    have hjj : (j * j) % 3 = 1 := by
      rcases hmod with h1 | h1 <;> simp [Int.mul_emod, h1]
    have hjt : ∃ t : ℤ, j * j = 1 + 3 * t := by
      generalize j * j = s at hjj ⊢
      exact ⟨s / 3, by omega⟩
    obtain ⟨t, ht⟩ := hjt
    have hzx : Subgroup.zpowers x ≤ Subgroup.zpowers (x ^ j) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
      rw [← zpow_mul, ht, zpow_add, zpow_mul, hx3]
      simp
    exact hkay.x_acts.1.2 (innDiagOn_mono hJ hzx)
  have hP5 : ∀ i : ℤ, a ^ i ∈ C → (3 : ℤ) ∣ i := by
    intro i hiC
    by_contra hi
    have hinvC : a ^ (-i) ∈ C := by
      rw [zpow_neg]
      exact C.inv_mem hiC
    have hinn : InducesInnerMod 3 N' (a ^ i) := by
      apply cb_inducesInner
      intro m hm
      rw [← zpow_neg]
      exact hcore_N (-i) hinvC m hm
    have hJ : InnDiagOn 3 (Subgroup.zpowers (a ^ i)) N' :=
      haut.inner_innDiag _ N' (a ^ i) hkay.Kxy_single hkay.chev_xy (zpow_mem ha_N_N' i) hinn
    have hmod : i % 3 = 1 ∨ i % 3 = 2 := by omega
    have hii : (i * i) % 3 = 1 := by
      rcases hmod with h1 | h1 <;> simp [Int.mul_emod, h1]
    have hit : ∃ t : ℤ, i * i = 1 + 3 * t := by
      generalize i * i = s at hii ⊢
      exact ⟨s / 3, by omega⟩
    obtain ⟨t, ht⟩ := hit
    have hza : Subgroup.zpowers a ≤ Subgroup.zpowers (a ^ i) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
      rw [← zpow_mul, ht, zpow_add, zpow_mul, ha3]
      simp
    exact hkay.a_acts.2 (innDiagOn_mono hJ hza)
  have hDC : Dgrp b x ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro d ⟨hdD, hdC⟩
    rw [Subgroup.mem_bot]
    obtain ⟨i, j, rfl⟩ := hDform d hdD
    have hj3 : (3 : ℤ) ∣ j := hP4 i j hdC
    obtain ⟨t, rfl⟩ := hj3
    have hxj : x ^ (3 * t) = 1 := by rw [zpow_mul, hx3, one_zpow]
    rw [hxj, mul_one] at hdC ⊢
    obtain ⟨s, rfl⟩ := hP5 i hdC
    rw [zpow_mul, ha3, one_zpow]
  have hzyC : Subgroup.zpowers y ≤ C := Subgroup.zpowers_le.2 hyC
  have hEC : E ⊓ C ≤ Subgroup.zpowers y := by
    intro e he
    have heE : e ∈ Dgrp b x ⊔ Subgroup.zpowers y := by
      rw [← hd.E_def]
      exact (Subgroup.mem_inf.1 he).1
    obtain ⟨d, hdD, z, hz, rfl⟩ := cb_mem_sup_of_comm
      (fun p hp'' q hq'' => hcommB p (hDB hp'') q (hzy_B hq'')) heE
    have hdC : d ∈ C := by
      have h1 : d * z ∈ C := (Subgroup.mem_inf.1 he).2
      have h2 : z ∈ C := hzyC hz
      have e3 : d = d * z * z⁻¹ := by group
      rw [e3]
      exact C.mul_mem h1 (C.inv_mem h2)
    have hd1 : d = 1 := by
      have h3 : d ∈ Dgrp b x ⊓ C := ⟨hdD, hdC⟩
      rw [hDC, Subgroup.mem_bot] at h3
      exact h3
    rw [hd1, one_mul]
    exact hz
  have hCE : C ≤ Subgroup.normalizer (E : Set G) :=
    cb_le_normalizer_of_comm (fun g hg s hs => hcommB g (Subgroup.mem_inf.1 hg).1 s (hEB hs))
  have hcardEC := card_sup_mul_card_inf_of_le_normalizer hCE
  have hyCcard : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
  have hEC_le : Nat.card (E ⊓ C : Subgroup G) ≤ 3 := by
    rw [← hyCcard]
    exact Subgroup.card_le_of_le hEC
  have hEC_pos : 0 < Nat.card (E ⊓ C : Subgroup G) := Nat.card_pos
  have hEC81 : 81 ≤ Nat.card (E ⊔ C : Subgroup G) := by
    have hE27 : Nat.card E = 3 ^ 3 := hd.E_card
    rw [hE27] at hcardEC
    have h1 : 27 * 9 ≤ 27 * Nat.card C := Nat.mul_le_mul_left 27 hC9
    have h2 : Nat.card (E ⊔ C : Subgroup G) * Nat.card (E ⊓ C : Subgroup G) ≤
        Nat.card (E ⊔ C : Subgroup G) * 3 := Nat.mul_le_mul_left _ hEC_le
    have h3 : 27 * 9 ≤ Nat.card (E ⊔ C : Subgroup G) * 3 := by
      calc 27 * 9 ≤ 27 * Nat.card C := h1
        _ = 3 ^ 3 * Nat.card C := by norm_num
        _ = Nat.card (E ⊔ C : Subgroup G) * Nat.card (E ⊓ C : Subgroup G) := hcardEC.symm
        _ ≤ Nat.card (E ⊔ C : Subgroup G) * 3 := h2
    omega
  have hEC_sub : E ⊔ C ≤ B := sup_le hEB inf_le_left
  have hEC_el : IsElemAbelian 3 (E ⊔ C : Subgroup G) := isElemAbelian_mono hB hEC_sub
  have hDsub : Dgrp b x ≤ E ⊔ C := le_trans hDE le_sup_left
  have hlayer : GLAPLayer 3 (L ⊓ cs (E ⊔ C)) ≠ ⊥ :=
    alpha_layer_EC hc hin h hd hBN (inf_le_left : C ≤ B) hCc
  have hE₀ : 81 ≤ Nat.card E₀ := le_trans hEC81 (hd.E₀_max (E ⊔ C) hEC_sub hEC_el hDsub hlayer)
  have hF_sub : F ≤ B := hd.F_E₀.trans hd.E₀_B
  have hF_el : IsElemAbelian 3 F := isElemAbelian_mono hd.E₀_el hd.F_E₀
  have hDN : Dgrp b x ≤ Subgroup.normalizer (F : Set G) :=
    cb_le_normalizer_of_comm (fun g hg s hs => hcommB g (hDB hg) s (hF_sub hs))
  have hcardFD := card_sup_mul_card_inf_of_le_normalizer hDN
  rw [hd.F_sup, hd.F_inf, Subgroup.card_bot, mul_one, hDc] at hcardFD
  have hFcard : 9 ≤ Nat.card F := by
    have h4 : Nat.card E₀ = Nat.card F * 9 := by
      rw [hcardFD]
      norm_num
    omega
  have hFnc : ¬ IsCyclic ↥F := fun hcyc => by
    have := caseAlphaEnd_card_le_three hcyc hF_el
    omega
  obtain ⟨N₂, hN₂, hBN₂⟩ := GLAIsBmax.exists_maxTwoLocal hbmax
  obtain ⟨D₀, hD₀F, hD₀card, hD₀ess, -⟩ := hc.ctx.lemma31 B F N₂ hbmax hF_sub hFnc hN₂ hBN₂
  obtain ⟨d₀, hd0, hd1⟩ : ∃ d₀ ∈ D₀, d₀ ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : D₀ = ⊥ := (Subgroup.eq_bot_iff_forall D₀).2 hne
    rw [hbot, Subgroup.card_bot] at hD₀card
    omega
  exact hnot (hd.y_ess ⟨d₀, hD₀F hd0, hd1, hD₀ess d₀ hd0 hd1⟩)

theorem alpha_Bstar_group (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg 3 B x L b) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData 3 B x L b a E₀ F y E K) (hky : AlphaKy 3 x a y K) {n : ℕ}
    (hn : Odd n) (hty : KyCardTy B (Kf 3 K (Subgroup.zpowers y)) n)
    (hcyc : IsCyclic ↥(B ⊓ centModSubgroup 3 (Kf 3 K (Subgroup.zpowers y)))) :
    ∃ B' T₀ : Subgroup G, y ∈ B' ∧ InYK y (Kf 3 K (Subgroup.zpowers y)) B' ∧ IsElemAbelian 3 B' ∧
      Nat.card B' = Nat.card B ∧ T₀ ≤ Kf 3 K (Subgroup.zpowers y) ∧ IsPGroup 2 T₀ ∧
      ¬ T₀ ≤ GLAPPrimeCoreOf 3 (Kf 3 K (Subgroup.zpowers y)) ∧ B' ≤ Subgroup.normalizer (T₀ : Set G) := by
  have hyB : y ∈ B := hd.E₀_B (hd.F_E₀ hd.y_F)
  by_cases hyK : y ∈ Kf 3 K (Subgroup.zpowers y)
  · exact caseAlphaEnd_bstar_of_mem hin.i1015cover (B_el h) hyB hd.y_ne hyK hn hky.Ky_comp hty hcyc
      (sstar_triple h.star).1.2.1
  · exact caseAlphaEnd_bstar_of_not_mem hin.i1015two (B_el h) hyB hd.y_ne hyK hn hky.Ky_comp hty hcyc

section EnlargeAux

variable {G : Type} [Group G] [Finite G]

private theorem enl_conj_mem {O : Subgroup G} {g x : G} (hg : g ∈ Subgroup.normalizer (O : Set G))
    (hx : x ∈ O) : g * x * g⁻¹ ∈ O :=
  (Subgroup.mem_normalizer_iff.1 hg x).1 hx

private def enlS (O E F : Subgroup G) (hE : ∀ e ∈ E, e ∈ Subgroup.normalizer (O : Set G))
    (hF : ∀ f ∈ F, f ∈ Subgroup.normalizer (O : Set G)) (hc : ∀ f ∈ F, ∀ e ∈ E, ⁅f, e⁆ ∈ O) :
    Subgroup G where
  carrier := {x | ∃ o ∈ O, ∃ e ∈ E, ∃ f ∈ F, x = o * e * f}
  one_mem' := ⟨1, O.one_mem, 1, E.one_mem, 1, F.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨o, ho, e, he, f, hf, rfl⟩ ⟨o', ho', e', he', f', hf', rfl⟩
    have hX : f * o' * f⁻¹ ∈ O := enl_conj_mem (hF f hf) ho'
    have hY : e * (f * o' * f⁻¹ * ⁅f, e'⁆) * e⁻¹ ∈ O :=
      enl_conj_mem (hE e he) (O.mul_mem hX (hc f hf e' he'))
    refine ⟨o * (e * (f * o' * f⁻¹ * ⁅f, e'⁆) * e⁻¹), O.mul_mem ho hY, e * e', E.mul_mem he he',
      f * f', F.mul_mem hf hf', ?_⟩
    simp only [commutatorElement_def]
    group
  inv_mem' := by
    rintro _ ⟨o, ho, e, he, f, hf, rfl⟩
    have h1 : e⁻¹ * o⁻¹ * e ∈ O := by
      have := enl_conj_mem (Subgroup.inv_mem _ (hE e he)) (O.inv_mem ho)
      rwa [inv_inv] at this
    have h2 : f⁻¹ * (e⁻¹ * o⁻¹ * e) * f ∈ O := by
      have := enl_conj_mem (Subgroup.inv_mem _ (hF f hf)) h1
      rwa [inv_inv] at this
    refine ⟨f⁻¹ * (e⁻¹ * o⁻¹ * e) * f * ⁅f⁻¹, e⁻¹⁆, O.mul_mem h2 (hc f⁻¹ (F.inv_mem hf) e⁻¹ (E.inv_mem he)),
      e⁻¹, E.inv_mem he, f⁻¹, F.inv_mem hf, ?_⟩
    simp only [commutatorElement_def]
    group

private theorem mem_enlS_iff {O E F : Subgroup G} {hE : ∀ e ∈ E, e ∈ Subgroup.normalizer (O : Set G)}
    {hF : ∀ f ∈ F, f ∈ Subgroup.normalizer (O : Set G)} {hc : ∀ f ∈ F, ∀ e ∈ E, ⁅f, e⁆ ∈ O} {x : G} :
    x ∈ enlS O E F hE hF hc ↔ ∃ o ∈ O, ∃ e ∈ E, ∃ f ∈ F, x = o * e * f :=
  Iff.rfl

private theorem enlS_mul_eq {O E F : Subgroup G} (hE : ∀ e ∈ E, e ∈ Subgroup.normalizer (O : Set G))
    (hF : ∀ f ∈ F, f ∈ Subgroup.normalizer (O : Set G)) (hc : ∀ f ∈ F, ∀ e ∈ E, ⁅f, e⁆ ∈ O)
    {o e f o' e' f' : G} (ho : o ∈ O) (he : e ∈ E) (hf : f ∈ F) (ho' : o' ∈ O) (he' : e' ∈ E)
    (hf' : f' ∈ F) : ∃ o₀ ∈ O, o * e * f * (o' * e' * f') = o₀ * (e * e') * (f * f') := by
  have hX : f * o' * f⁻¹ ∈ O := enl_conj_mem (hF f hf) ho'
  have hY : e * (f * o' * f⁻¹ * ⁅f, e'⁆) * e⁻¹ ∈ O :=
    enl_conj_mem (hE e he) (O.mul_mem hX (hc f hf e' he'))
  refine ⟨o * (e * (f * o' * f⁻¹ * ⁅f, e'⁆) * e⁻¹), O.mul_mem ho hY, ?_⟩
  simp only [commutatorElement_def]
  group

private theorem enlS_comm_mem {O E F : Subgroup G} {hE : ∀ e ∈ E, e ∈ Subgroup.normalizer (O : Set G)}
    {hF : ∀ f ∈ F, f ∈ Subgroup.normalizer (O : Set G)} {hc : ∀ f ∈ F, ∀ e ∈ E, ⁅f, e⁆ ∈ O}
    (hEel : IsElemAbelian 3 E) (hFel : IsElemAbelian 3 F) {x y : G}
    (hx : x ∈ enlS O E F hE hF hc) (hy : y ∈ enlS O E F hE hF hc) : ⁅x, y⁆ ∈ O := by
  obtain ⟨o, ho, e, he, f, hf, rfl⟩ := hx
  obtain ⟨o', ho', e', he', f', hf', rfl⟩ := hy
  obtain ⟨o₁, ho₁, h₁⟩ := enlS_mul_eq hE hF hc ho he hf ho' he' hf'
  obtain ⟨o₂, ho₂, h₂⟩ := enlS_mul_eq hE hF hc ho' he' hf' ho he hf
  have hee : e' * e = e * e' := isElemAbelian_commute hEel he' he
  have hff : f' * f = f * f' := isElemAbelian_commute hFel hf' hf
  rw [hee, hff] at h₂
  have key : ⁅o * e * f, o' * e' * f'⁆ = (o * e * f * (o' * e' * f')) * (o' * e' * f' * (o * e * f))⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [key, h₁, h₂]
  have h3 : o₁ * (e * e') * (f * f') * (o₂ * (e * e') * (f * f'))⁻¹ = o₁ * o₂⁻¹ := by group
  rw [h3]
  exact O.mul_mem ho₁ (O.inv_mem ho₂)

private theorem enlS_pow_three_mem {O E F : Subgroup G} {hE : ∀ e ∈ E, e ∈ Subgroup.normalizer (O : Set G)}
    {hF : ∀ f ∈ F, f ∈ Subgroup.normalizer (O : Set G)} {hc : ∀ f ∈ F, ∀ e ∈ E, ⁅f, e⁆ ∈ O}
    (hEel : IsElemAbelian 3 E) (hFel : IsElemAbelian 3 F) {x : G} (hx : x ∈ enlS O E F hE hF hc) :
    x ^ 3 ∈ O := by
  obtain ⟨o, ho, e, he, f, hf, rfl⟩ := hx
  obtain ⟨o₀, ho₀, h₀⟩ := enlS_mul_eq hE hF hc ho he hf ho he hf
  obtain ⟨o₁, ho₁, h₁⟩ := enlS_mul_eq hE hF hc ho₀ (E.mul_mem he he) (F.mul_mem hf hf) ho he hf
  have he3 : e * e * e = 1 := by simpa [pow_three, mul_assoc] using hEel.2 e he
  have hf3 : f * f * f = 1 := by simpa [pow_three, mul_assoc] using hFel.2 f hf
  have hx3 : (o * e * f) ^ 3 = o₁ * (e * e * e) * (f * f * f) := by
    have : (o * e * f) ^ 3 = (o * e * f) * (o * e * f) * (o * e * f) := by
      simp only [pow_three, mul_assoc]
    rw [this, h₀, h₁]
  rw [hx3, he3, hf3, mul_one, mul_one]
  exact ho₁

private theorem enl_conj_OE {O E K : Subgroup G} (hK : ∀ k ∈ K, k ∈ Subgroup.normalizer (O : Set G))
    (hcomm : ∀ l ∈ K, ∀ e ∈ E, ⁅l, e⁆ ∈ O) {g o e : G} (hg : g ∈ K) (ho : o ∈ O) (he : e ∈ E) :
    ∃ o₀ ∈ O, ∃ e₀ ∈ E, g * (o * e) * g⁻¹ = o₀ * e₀ := by
  refine ⟨g * o * g⁻¹ * ⁅g, e⁆, O.mul_mem (enl_conj_mem (hK g hg) ho) (hcomm g hg e he), e, he, ?_⟩
  simp only [commutatorElement_def]
  group

private theorem enl_le_normalizer_of_conj {M Γ : Subgroup G}
    (hΓ : ∀ g ∈ Γ, ∀ x ∈ M, g * x * g⁻¹ ∈ M) : Γ ≤ Subgroup.normalizer (M : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hΓ g hg x hx, fun hx => ?_⟩
  have h := hΓ g⁻¹ (Γ.inv_mem hg) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h

private theorem enl_inf_bot {O E : Subgroup G} (hO : ¬ 3 ∣ Nat.card O) (hE : IsElemAbelian 3 E) :
    O ⊓ E = ⊥ := by
  obtain ⟨α, hα⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hE
  have h1 : Nat.card (O ⊓ E : Subgroup G) ∣ 3 ^ α := hα ▸ Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
  have h2 : Nat.card (O ⊓ E : Subgroup G) ∣ Nat.card O := Subgroup.card_dvd_of_le inf_le_left
  have hj0 : j = 0 := by
    by_contra hne
    apply hO
    have h3 : 3 ∣ Nat.card (O ⊓ E : Subgroup G) := by
      rw [hj]
      exact dvd_pow_self 3 hne
    exact h3.trans h2
  apply Subgroup.eq_bot_of_card_eq
  rw [hj, hj0, pow_zero]

private theorem enl_mem_core_iff {K : Subgroup G} (w : ↥K) :
    w ∈ GLAPPrimeCore 3 ↥K ↔ ((w : ↥K) : G) ∈ GLAPPrimeCoreOf 3 K := by
  constructor
  · intro hw
    exact ⟨w, hw, rfl⟩
  · rintro ⟨u, hu, huw⟩
    have : u = w := Subtype.ext huw
    rwa [this] at hu

private theorem enl_card_le {K H : Subgroup G} (hHK : H ≤ K) (hOH : GLAPPrimeCoreOf 3 K ≤ H)
    (hcent : ∀ x ∈ K, ∀ h ∈ H, ⁅x, h⁆ ∈ GLAPPrimeCoreOf 3 K) :
    Nat.card H ≤ Nat.card (GLAPPrimeCoreOf 3 K) * Nat.card (Subgroup.center (PQuot 3 K)) := by
  classical
  let f : ↥(H.subgroupOf K) →* PQuot 3 K :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (H.subgroupOf K).subtype
  have hcard : Nat.card (H.subgroupOf K) = Nat.card f.ker * Nat.card f.range :=
    (Subgroup.card_ker_mul_card_range f).symm
  have hHsub : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have hrange : Nat.card f.range ≤ Nat.card (Subgroup.center (PQuot 3 K)) := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨h, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    have hh : ((h : ↥K) : G) ∈ H := Subgroup.mem_subgroupOf.1 h.2
    have hkK : ((k : ↥K) : G) ∈ K := k.2
    have hhK : ((h : ↥K) : G) ∈ K := (h : ↥K).2
    have hcm : ⁅((k : ↥K) : G), ((h : ↥K) : G)⁆ ∈ GLAPPrimeCoreOf 3 K := hcent _ hkK _ hh
    have hc1 : (k : G)⁻¹ * (⁅(k : G), (h : G)⁆)⁻¹ * (k : G)⁻¹⁻¹ ∈ GLAPPrimeCoreOf 3 K :=
      enl_conj_mem (le_normalizer_glaPPrimeCoreOf 3 K (K.inv_mem hkK)) (Subgroup.inv_mem _ hcm)
    have hc2 : (h : G)⁻¹ * ((k : G)⁻¹ * (⁅(k : G), (h : G)⁆)⁻¹ * (k : G)⁻¹⁻¹) * (h : G)⁻¹⁻¹ ∈
        GLAPPrimeCoreOf 3 K :=
      enl_conj_mem (le_normalizer_glaPPrimeCoreOf 3 K (K.inv_mem hhK)) hc1
    change QuotientGroup.mk k * QuotientGroup.mk (h : ↥K) = QuotientGroup.mk (h : ↥K) * QuotientGroup.mk k
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, enl_mem_core_iff]
    have key : (((k * (h : ↥K))⁻¹ * ((h : ↥K) * k) : ↥K) : G) =
        (h : G)⁻¹ * ((k : G)⁻¹ * (⁅(k : G), (h : G)⁆)⁻¹ * (k : G)⁻¹⁻¹) * (h : G)⁻¹⁻¹ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [key]
    exact hc2
  have hker : Nat.card f.ker ≤ Nat.card (GLAPPrimeCoreOf 3 K) := by
    have hmem : ∀ x : f.ker, (((x : ↥(H.subgroupOf K)) : ↥K) : G) ∈ GLAPPrimeCoreOf 3 K := by
      intro x
      have hx : (QuotientGroup.mk ((x : ↥(H.subgroupOf K)) : ↥K) : PQuot 3 K) = 1 := x.2
      rw [← enl_mem_core_iff]
      exact (QuotientGroup.eq_one_iff _).1 hx
    refine Nat.card_le_card_of_injective
      (fun x : f.ker => (⟨(((x : ↥(H.subgroupOf K)) : ↥K) : G), hmem x⟩ : ↥(GLAPPrimeCoreOf 3 K))) ?_
    intro x y hxy
    have hval : (((x : ↥(H.subgroupOf K)) : ↥K) : G) = (((y : ↥(H.subgroupOf K)) : ↥K) : G) :=
      congrArg (fun z : ↥(GLAPPrimeCoreOf 3 K) => (z : G)) hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hval
  rw [← hHsub, hcard]
  exact Nat.mul_le_mul hker hrange

end EnlargeAux

theorem alpha_enlarge {K E₁ T₀ E : Subgroup G} (hE₁K : E₁ ≤ K) (hE₁el : IsElemAbelian 3 E₁)
    (hT₀K : T₀ ≤ K) (hT₀2 : IsPGroup 2 T₀) (hT₀O : ¬ T₀ ≤ GLAPPrimeCoreOf 3 K)
    (hE₁T₀ : E₁ ≤ Subgroup.normalizer (T₀ : Set G)) (hEel : IsElemAbelian 3 E)
    (hEc : ∀ g ∈ E, CentMod 3 K g) :
    ∃ A U : Subgroup G, IsElemAbelian 3 A ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set G) ∧
      Nat.card E * Nat.card E₁ ≤ Nat.card A * Nat.card (Subgroup.center (PQuot 3 K)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOcop : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 K) := not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
  have hOK : GLAPPrimeCoreOf 3 K ≤ K := Subgroup.map_subtype_le _
  have hKN : ∀ k ∈ K, k ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := fun k hk =>
    le_normalizer_glaPPrimeCoreOf 3 K hk
  have hEN : ∀ e ∈ E, e ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := fun e he =>
    normalizer_le_normalizer_glaPPrimeCoreOf 3 K (And.left (hEc e he))
  have hcomm : ∀ l ∈ K, ∀ e ∈ E, ⁅l, e⁆ ∈ GLAPPrimeCoreOf 3 K := fun l hl e he =>
    And.right (hEc e he) (Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers e))
  have hE₁N : ∀ f ∈ E₁, f ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := fun f hf =>
    hKN f (hE₁K hf)
  have hT₀N : ∀ t ∈ T₀, t ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := fun t ht =>
    hKN t (hT₀K ht)
  have hcE₁ : ∀ f ∈ E₁, ∀ e ∈ E, ⁅f, e⁆ ∈ GLAPPrimeCoreOf 3 K := fun f hf e he =>
    hcomm f (hE₁K hf) e he
  have hbotN : ∀ f ∈ (⊥ : Subgroup G), f ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := by
    intro f hf
    rw [Subgroup.mem_bot] at hf
    rw [hf]
    exact Subgroup.one_mem _
  have hbotc : ∀ (E' : Subgroup G), ∀ f ∈ (⊥ : Subgroup G), ∀ e ∈ E', ⁅f, e⁆ ∈ GLAPPrimeCoreOf 3 K := by
    intro E' f hf e _
    rw [Subgroup.mem_bot] at hf
    rw [hf, commutatorElement_one_left]
    exact Subgroup.one_mem _
  have hbotc' : ∀ f ∈ E₁, ∀ e ∈ (⊥ : Subgroup G), ⁅f, e⁆ ∈ GLAPPrimeCoreOf 3 K := by
    intro f _ e he
    rw [Subgroup.mem_bot] at he
    rw [he, commutatorElement_one_right]
    exact Subgroup.one_mem _
  have hEN' : E ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := fun e he => hEN e he
  have hE₁N' : E₁ ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := fun f hf => hE₁N f hf
  have hT₀N' : T₀ ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := fun t ht => hT₀N t ht
  obtain ⟨α, hα⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hEel
  obtain ⟨β, hβ⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hE₁el
  set O := GLAPPrimeCoreOf 3 K with hO
  set PE : Subgroup G := enlS O E ⊥ hEN hbotN (hbotc E) with hPEdef
  set PF : Subgroup G := enlS O ⊥ E₁ hbotN hE₁N hbotc' with hPFdef
  set S : Subgroup G := enlS O E E₁ hEN hE₁N hcE₁ with hSdef
  set M₀ : Subgroup G := enlS O T₀ ⊥ hT₀N hbotN (hbotc T₀) with hM₀def
  have memPE : ∀ {x : G}, x ∈ PE ↔ ∃ o ∈ O, ∃ e ∈ E, x = o * e := by
    intro x
    rw [hPEdef, mem_enlS_iff]
    constructor
    · rintro ⟨o, ho, e, he, f, hf, rfl⟩
      rw [Subgroup.mem_bot] at hf
      exact ⟨o, ho, e, he, by rw [hf, mul_one]⟩
    · rintro ⟨o, ho, e, he, rfl⟩
      exact ⟨o, ho, e, he, 1, Subgroup.one_mem _, (mul_one _).symm⟩
  have memPF : ∀ {x : G}, x ∈ PF ↔ ∃ o ∈ O, ∃ f ∈ E₁, x = o * f := by
    intro x
    rw [hPFdef, mem_enlS_iff]
    constructor
    · rintro ⟨o, ho, e, he, f, hf, rfl⟩
      rw [Subgroup.mem_bot] at he
      exact ⟨o, ho, f, hf, by rw [he, mul_one]⟩
    · rintro ⟨o, ho, f, hf, rfl⟩
      exact ⟨o, ho, 1, Subgroup.one_mem _, f, hf, by rw [mul_one]⟩
  have memS : ∀ {x : G}, x ∈ S ↔ ∃ o ∈ O, ∃ e ∈ E, ∃ f ∈ E₁, x = o * e * f := by
    intro x
    rw [hSdef, mem_enlS_iff]
  have memM₀ : ∀ {x : G}, x ∈ M₀ ↔ ∃ o ∈ O, ∃ t ∈ T₀, x = o * t := by
    intro x
    rw [hM₀def, mem_enlS_iff]
    constructor
    · rintro ⟨o, ho, t, ht, f, hf, rfl⟩
      rw [Subgroup.mem_bot] at hf
      exact ⟨o, ho, t, ht, by rw [hf, mul_one]⟩
    · rintro ⟨o, ho, t, ht, rfl⟩
      exact ⟨o, ho, t, ht, 1, Subgroup.one_mem _, (mul_one _).symm⟩
  have hPE_eq : PE = O ⊔ E := by
    apply le_antisymm
    · intro x hx
      obtain ⟨o, ho, e, he, rfl⟩ := memPE.1 hx
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right he)
    · apply sup_le
      · intro o ho
        exact memPE.2 ⟨o, ho, 1, E.one_mem, (mul_one o).symm⟩
      · intro e he
        exact memPE.2 ⟨1, O.one_mem, e, he, (one_mul e).symm⟩
  have hPF_eq : PF = O ⊔ E₁ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨o, ho, f, hf, rfl⟩ := memPF.1 hx
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hf)
    · apply sup_le
      · intro o ho
        exact memPF.2 ⟨o, ho, 1, E₁.one_mem, (mul_one o).symm⟩
      · intro f hf
        exact memPF.2 ⟨1, O.one_mem, f, hf, (one_mul f).symm⟩
  have hM₀_eq : M₀ = O ⊔ T₀ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨o, ho, t, ht, rfl⟩ := memM₀.1 hx
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right ht)
    · apply sup_le
      · intro o ho
        exact memM₀.2 ⟨o, ho, 1, T₀.one_mem, (mul_one o).symm⟩
      · intro t ht
        exact memM₀.2 ⟨1, O.one_mem, t, ht, (one_mul t).symm⟩
  have hS_eq : S = PE ⊔ PF := by
    apply le_antisymm
    · intro x hx
      obtain ⟨o, ho, e, he, f, hf, rfl⟩ := memS.1 hx
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (memPE.2 ⟨o, ho, e, he, rfl⟩))
        (Subgroup.mem_sup_right (memPF.2 ⟨1, O.one_mem, f, hf, (one_mul f).symm⟩))
    · apply sup_le
      · intro x hx
        obtain ⟨o, ho, e, he, rfl⟩ := memPE.1 hx
        exact memS.2 ⟨o, ho, e, he, 1, E₁.one_mem, (mul_one _).symm⟩
      · intro x hx
        obtain ⟨o, ho, f, hf, rfl⟩ := memPF.1 hx
        exact memS.2 ⟨o, ho, 1, E.one_mem, f, hf, by rw [mul_one]⟩
  have hPE_conj : ∀ g ∈ K, ∀ x ∈ PE, g * x * g⁻¹ ∈ PE := by
    intro g hg x hx
    obtain ⟨o, ho, e, he, rfl⟩ := memPE.1 hx
    obtain ⟨o₀, ho₀, e₀, he₀, h⟩ := enl_conj_OE hKN hcomm hg ho he
    exact memPE.2 ⟨o₀, ho₀, e₀, he₀, h⟩
  have hK_N_PE : K ≤ Subgroup.normalizer (PE : Set G) := enl_le_normalizer_of_conj hPE_conj
  have hPF_le_K : PF ≤ K := by
    rw [hPF_eq]
    exact sup_le hOK hE₁K
  have hPF_N_PE : PF ≤ Subgroup.normalizer (PE : Set G) := le_trans hPF_le_K hK_N_PE
  have hcardPE : Nat.card PE = Nat.card O * Nat.card E := by
    have h := card_sup_mul_card_inf_of_le_normalizer hEN'
    rw [enl_inf_bot hOcop hEel, Subgroup.card_bot, mul_one, ← hPE_eq] at h
    exact h
  have hcardPF : Nat.card PF = Nat.card O * Nat.card E₁ := by
    have h := card_sup_mul_card_inf_of_le_normalizer hE₁N'
    rw [enl_inf_bot hOcop hE₁el, Subgroup.card_bot, mul_one, ← hPF_eq] at h
    exact h
  have hcardS : Nat.card S * Nat.card (PE ⊓ PF : Subgroup G) = Nat.card PE * Nat.card PF := by
    have h := card_sup_mul_card_inf_of_le_normalizer hPF_N_PE
    rw [← hS_eq] at h
    exact h
  have hcardM₀ : Nat.card M₀ * Nat.card (O ⊓ T₀ : Subgroup G) = Nat.card O * Nat.card T₀ := by
    have h := card_sup_mul_card_inf_of_le_normalizer hT₀N'
    rw [← hM₀_eq] at h
    exact h
  have hOPE : O ≤ PE := by
    rw [hPE_eq]
    exact le_sup_left
  have hOPF : O ≤ PF := by
    rw [hPF_eq]
    exact le_sup_left
  have hOH : O ≤ PE ⊓ PF := le_inf hOPE hOPF
  have hHK : PE ⊓ PF ≤ K := inf_le_right.trans hPF_le_K
  have hOS : O ≤ S := fun x hx => memS.2 ⟨x, hx, 1, E.one_mem, 1, E₁.one_mem, by simp⟩
  have hcentH : ∀ x ∈ K, ∀ h ∈ PE ⊓ PF, ⁅x, h⁆ ∈ O := by
    intro x hx h hh
    obtain ⟨o, ho, e, he, rfl⟩ := memPE.1 (Subgroup.mem_inf.1 hh).1
    have key : ⁅x, o * e⁆ = (x * o * x⁻¹) * ⁅x, e⁆ * o⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact O.mul_mem (O.mul_mem (enl_conj_mem (hKN x hx) ho) (hcomm x hx e he)) (O.inv_mem ho)
  have hcardH := enl_card_le hHK hOH hcentH
  obtain ⟨s, hs⟩ := Subgroup.card_dvd_of_le hOS
  obtain ⟨h', hh'⟩ := Subgroup.card_dvd_of_le hOH
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hprod : s * h' = 3 ^ α * 3 ^ β := by
    have h1 : Nat.card S * Nat.card (PE ⊓ PF : Subgroup G) = (Nat.card O * Nat.card E) * (Nat.card O * Nat.card E₁) := by
      rw [hcardS, hcardPE, hcardPF]
    rw [hs, hh', hα, hβ] at h1
    have h2 : (Nat.card O * Nat.card O) * (s * h') = (Nat.card O * Nat.card O) * (3 ^ α * 3 ^ β) := by
      calc (Nat.card O * Nat.card O) * (s * h') = Nat.card O * s * (Nat.card O * h') := by ring
        _ = Nat.card O * 3 ^ α * (Nat.card O * 3 ^ β) := h1
        _ = (Nat.card O * Nat.card O) * (3 ^ α * 3 ^ β) := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hOpos hOpos) h2
  have hh'le : h' ≤ Nat.card (Subgroup.center (PQuot 3 K)) := by
    rw [hh'] at hcardH
    exact Nat.le_of_mul_le_mul_left hcardH hOpos
  have hsdvd : s ∣ 3 ^ (α + β) := ⟨h', by rw [pow_add, hprod]⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hsdvd
  have hdvdP : 3 ^ k ∣ Nat.card S := by
    rw [hs, ← hk]
    exact dvd_mul_left s _
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvdP
  set A : Subgroup G := P.map S.subtype with hAdef
  have hAcard : Nat.card A = 3 ^ k := by
    rw [hAdef, Subgroup.card_map_of_injective S.subtype_injective, hP]
  have hAS : A ≤ S := Subgroup.map_subtype_le P
  have hAO : A ⊓ O = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h1 : Nat.card (A ⊓ O : Subgroup G) ∣ 3 ^ k := hAcard ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    have h2 : Nat.card (A ⊓ O : Subgroup G) ∣ Nat.card O := Subgroup.card_dvd_of_le inf_le_right
    have hj0 : j = 0 := by
      by_contra hne
      apply hOcop
      have h3 : 3 ∣ Nat.card (A ⊓ O : Subgroup G) := by
        rw [hj]
        exact dvd_pow_self 3 hne
      exact h3.trans h2
    rw [hj, hj0, pow_zero]
  have hcomm_A : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have haS : a ∈ enlS O E E₁ hEN hE₁N hcE₁ := hAS ha
    have hbS : b ∈ enlS O E E₁ hEN hE₁N hcE₁ := hAS hb
    have hO' : ⁅a, b⁆ ∈ O := enlS_comm_mem hEel hE₁el haS hbS
    have hcA : ⁅a, b⁆ ∈ A := by
      rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
    have h1 : ⁅a, b⁆ ∈ A ⊓ O := ⟨hcA, hO'⟩
    rw [hAO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hcube_A : ∀ x ∈ A, x ^ 3 = 1 := by
    intro x hx
    have hxS : x ∈ enlS O E E₁ hEN hE₁N hcE₁ := hAS hx
    have h3O : x ^ 3 ∈ O := enlS_pow_three_mem hEel hE₁el hxS
    have h3A : x ^ 3 ∈ A := A.pow_mem hx 3
    have h1 : x ^ 3 ∈ A ⊓ O := ⟨h3A, h3O⟩
    rw [hAO, Subgroup.mem_bot] at h1
    exact h1
  have hAel : IsElemAbelian 3 A :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm_A a.1 a.2 b.1 b.2)⟩⟩, fun x hx => hcube_A x hx⟩
  have hA3 : IsPGroup 3 A := isPGroup_of_isElemAbelian hAel
  have hM₀_ndvd : ¬ 3 ∣ Nat.card M₀ := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hT₀2
    intro h3
    have h1 : 3 ∣ Nat.card O * Nat.card T₀ := by
      rw [← hcardM₀]
      exact Dvd.dvd.mul_right h3 _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h1 with h | h
    · exact hOcop h
    · rw [hm] at h
      have h4 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      norm_num at h4
  have hON : O ≤ Subgroup.normalizer (M₀ : Set G) := by
    apply enl_le_normalizer_of_conj
    intro g hg x hx
    obtain ⟨o', ho', t, ht, rfl⟩ := memM₀.1 hx
    have hgt : g * (t * g⁻¹ * t⁻¹) ∈ O :=
      O.mul_mem hg (enl_conj_mem (hT₀N t ht) (O.inv_mem hg))
    exact memM₀.2 ⟨g * o' * g⁻¹ * (g * (t * g⁻¹ * t⁻¹)),
      O.mul_mem (enl_conj_mem (Subgroup.le_normalizer hg) ho') hgt, t, ht, by group⟩
  have hEM₀ : E ≤ Subgroup.normalizer (M₀ : Set G) := by
    apply enl_le_normalizer_of_conj
    intro g hg x hx
    obtain ⟨o', ho', t, ht, rfl⟩ := memM₀.1 hx
    have hgt : g * t * g⁻¹ * t⁻¹ ∈ O := by
      have e1 : g * t * g⁻¹ * t⁻¹ = (t * g * t⁻¹ * g⁻¹)⁻¹ := by group
      rw [e1]
      exact O.inv_mem (hcomm t (hT₀K ht) g hg)
    exact memM₀.2 ⟨g * o' * g⁻¹ * (g * t * g⁻¹ * t⁻¹),
      O.mul_mem (enl_conj_mem (hEN g hg) ho') hgt, t, ht, by group⟩
  have hE₁M₀ : E₁ ≤ Subgroup.normalizer (M₀ : Set G) := by
    apply enl_le_normalizer_of_conj
    intro g hg x hx
    obtain ⟨o', ho', t, ht, rfl⟩ := memM₀.1 hx
    have htg : g * t * g⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.1 (hE₁T₀ hg) t).1 ht
    exact memM₀.2 ⟨g * o' * g⁻¹, enl_conj_mem (hE₁N g hg) ho', g * t * g⁻¹, htg, by group⟩
  have hSM₀ : S ≤ Subgroup.normalizer (M₀ : Set G) := by
    intro x hx
    obtain ⟨o, ho, e, he, f, hf, rfl⟩ := memS.1 hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hON ho) (hEM₀ he)) (hE₁M₀ hf)
  have hAM₀ : A ≤ Subgroup.normalizer (M₀ : Set G) := hAS.trans hSM₀
  have hT₀M₀ : T₀ ≤ M₀ := by
    rw [hM₀_eq]
    exact le_sup_right
  have hbot2 : IsPGroup 2 (⊥ : Subgroup G) := fun g => ⟨0, by
    have : g = 1 := Subtype.ext (Subgroup.mem_bot.1 g.2)
    simp [this]⟩
  have hAQ : A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro a _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp
  obtain ⟨U, hUfus, -, hAU⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_three Nat.prime_two hA3
      hM₀_ndvd hAM₀ bot_le hbot2 hAQ
  obtain ⟨hUM, hU2, hUmax⟩ := hUfus
  have hUne : U ≠ ⊥ := by
    intro hUbot
    have hT : T₀ = U := hUmax T₀ hT₀M₀ hT₀2 (by rw [hUbot]; exact bot_le)
    apply hT₀O
    rw [hT, hUbot]
    exact bot_le
  refine ⟨A, U, hAel, hUne, hU2, hAU, ?_⟩
  calc Nat.card E * Nat.card E₁ = 3 ^ α * 3 ^ β := by rw [hα, hβ]
    _ = s * h' := hprod.symm
    _ ≤ s * Nat.card (Subgroup.center (PQuot 3 K)) := Nat.mul_le_mul_left s hh'le
    _ = Nat.card A * Nat.card (Subgroup.center (PQuot 3 K)) := by rw [hAcard, hk]

theorem alpha_cycMod (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G}
    (h : Cfg 3 B x L b) {E₀ F : Subgroup G} {y : G} {E K : Subgroup G}
    (hd : AlphaData 3 B x L b a E₀ F y E K) (hky : AlphaKy 3 x a y K) {n : ℕ} (hn : Odd n)
    (hty : KyCardTy B (Kf 3 K (Subgroup.zpowers y)) n)
    (hcyc : IsCyclic ↥(B ⊓ centModSubgroup 3 (Kf 3 K (Subgroup.zpowers y)))) :
    CycModSylow 3 (Kf 3 K (Subgroup.zpowers y)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := sstar_triple h.star
  have hyB : y ∈ B := hd.E₀_B (hd.F_E₀ hd.y_F)
  have hcases := caseAlphaEnd_card_ty hty (caseAlphaEnd_card_centMod (B_el h) hyB hd.y_ne hky.Ky_comp.1 hcyc)
  have hrk : Nat.card B = 3 ^ GLATwoLocalRank 3 G := hS.1.2.1
  intro S hSc hS3
  by_contra hnc
  haveI : Fact (IsPGroup 3 S) := ⟨hS3⟩
  obtain ⟨S₁, -, hS₁card, hS₁el⟩ := CFSG.lemma_4_5_a (R := ↥S) (p := 3) (by norm_num) hnc
  have hSm : CFSG.IsElementaryAbelian 3 (S₁.map S.subtype) := CFSG.IsElementaryAbelian.map_subtype
  have hcard : Nat.card (S₁.map S.subtype) = 3 ^ 2 := by
    rw [← hS₁card]
    exact (Nat.card_congr (S₁.equivMapOfInjective S.subtype S.subtype_injective).toEquiv).symm
  have hel : IsElemAbelian 3 (S₁.map S.subtype) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mp hSm
  have hS₀c : ∀ g ∈ S₁.map S.subtype, CentMod 3 (Kf 3 K (Subgroup.zpowers y)) g := by
    intro g hg
    obtain ⟨g', -, rfl⟩ := Subgroup.mem_map.1 hg
    exact hSc g' g'.2
  have key : ∀ (E₁ T : Subgroup G) (z : ℕ), E₁ ≤ Kf 3 K (Subgroup.zpowers y) → IsElemAbelian 3 E₁ →
      T ≤ Kf 3 K (Subgroup.zpowers y) → IsPGroup 2 T →
      ¬ T ≤ GLAPPrimeCoreOf 3 (Kf 3 K (Subgroup.zpowers y)) → E₁ ≤ Subgroup.normalizer (T : Set G) →
      Nat.card (Subgroup.center (PQuot 3 (Kf 3 K (Subgroup.zpowers y)))) = z →
      Nat.card B * z < 9 * Nat.card E₁ → False := by
    intro E₁ T z hE₁K hE₁el hTK hT2 hTO hE₁T hz hlt
    obtain ⟨A, U, hAel, hU, hU2, hAU, hle⟩ := alpha_enlarge hE₁K hE₁el hTK hT2 hTO hE₁T hel hS₀c
    have hA := card_le_pow_glaTwoLocalRank Nat.prime_three hAel hU hU2 hAU
    rw [← hrk] at hA
    rw [hcard, hz] at hle
    have h1 := Nat.mul_le_mul_right z hA
    omega
  rcases hcases with ⟨hU6, hBcard⟩ | ⟨hTE6, hBcard⟩
  · by_cases hZ : Subgroup.center (PQuot 3 (Kf 3 K (Subgroup.zpowers y))) = ⊥
    · obtain ⟨E₁, T, hE₁K, hE₁el, hE₁card, hTK, hT2, hTO, hE₁T⟩ :=
        (hin.i1015two (cx y) _ n hky.Ky_comp hn).1 hU6
      exact key E₁ T 1 hE₁K hE₁el hTK hT2 hTO hE₁T (by rw [hZ, Subgroup.card_bot])
        (by rw [hBcard, hE₁card]; norm_num)
    · obtain ⟨hz3, hU6c, -⟩ := hin.i1015cover (cx y) _ n hky.Ky_comp hn (Or.inl hU6) hZ
      obtain ⟨E₁, T, hE₁K, hE₁el, hE₁card, hTK, hT2, hTO, hE₁T⟩ := hU6c hU6
      exact key E₁ T 3 hE₁K hE₁el hTK hT2 hTO hE₁T hz3 (by rw [hBcard, hE₁card]; norm_num)
  · by_cases hZ : Subgroup.center (PQuot 3 (Kf 3 K (Subgroup.zpowers y))) = ⊥
    · obtain ⟨E₁, T, hE₁K, hE₁el, hE₁card, hTK, hT2, hTO, hE₁T⟩ :=
        (hin.i1015two (cx y) _ n hky.Ky_comp hn).2 hTE6
      exact key E₁ T 1 hE₁K hE₁el hTK hT2 hTO hE₁T (by rw [hZ, Subgroup.card_bot])
        (by rw [hBcard, hE₁card]; norm_num)
    · obtain ⟨hz3, -, hTE6c⟩ := hin.i1015cover (cx y) _ n hky.Ky_comp hn (Or.inr hTE6) hZ
      obtain ⟨E₁, T, hE₁K, hE₁el, hE₁card, hTK, hT2, hTO, hE₁T⟩ := hTE6c hTE6
      exact key E₁ T 3 hE₁K hE₁el hTK hT2 hTO hE₁T hz3 (by rw [hBcard, hE₁card]; norm_num)

theorem alpha_Bstar_T (hc : S10Ctx G 3) (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg 3 B x L b) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData 3 B x L b a E₀ F y E K) (hky : AlphaKy 3 x a y K)
    {B' T₀ : Subgroup G} (hyB' : y ∈ B') (hY : InYK y (Kf 3 K (Subgroup.zpowers y)) B')
    (hel : IsElemAbelian 3 B') (hcard : Nat.card B' = Nat.card B)
    (hT₀K : T₀ ≤ Kf 3 K (Subgroup.zpowers y)) (hT₀2 : IsPGroup 2 T₀)
    (hT₀O : ¬ T₀ ≤ GLAPPrimeCoreOf 3 (Kf 3 K (Subgroup.zpowers y)))
    (hT₀B : B' ≤ Subgroup.normalizer (T₀ : Set G))
    (hchev : IsChevSimple 2 (PSimple 3 (Kf 3 K (Subgroup.zpowers y))))
    (hcm : CycModSylow 3 (Kf 3 K (Subgroup.zpowers y))) :
    ∃ T : Subgroup G, T ≤ Kf 3 K (Subgroup.zpowers y) ∧ IsPGroup 2 T ∧
      B' ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B'⁆ : Subgroup G) ≠ ⊥ ∧
      IsEmpty (T ≃* QuaternionGroup 2) ∧ ¬ T ≤ GLAPPrimeCoreOf 3 (Kf 3 K (Subgroup.zpowers y)) := by
  have hS := sstar_triple h.star
  have hbig : 27 ≤ Nat.card B' := by
    rw [hcard, hS.1.2.1]
    calc 27 ≤ 3 ^ 4 := by norm_num
      _ ≤ 3 ^ GLATwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) hc.ctx.rank_ge
  exact caseAlphaEnd_bstar_T_of_cycMod hin.l105.i1312 hky.Ky_comp hchev hcm hyB' hY hel hbig hT₀K hT₀2 hT₀O hT₀B

theorem alpha_Bstar (hc : S10Ctx G 3) (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg 3 B x L b) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData 3 B x L b a E₀ F y E K) (hky : AlphaKy 3 x a y K) {n : ℕ}
    (hn : Odd n) (hty : KyCardTy B (Kf 3 K (Subgroup.zpowers y)) n)
    (hcyc : IsCyclic ↥(B ⊓ centModSubgroup 3 (Kf 3 K (Subgroup.zpowers y)))) :
    ∃ B' T : Subgroup G, y ∈ B' ∧ InYK y (Kf 3 K (Subgroup.zpowers y)) B' ∧ IsElemAbelian 3 B' ∧
      Nat.card B' = Nat.card B ∧ T ≤ Kf 3 K (Subgroup.zpowers y) ∧ IsPGroup 2 T ∧
      B' ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B'⁆ : Subgroup G) ≠ ⊥ ∧
      IsEmpty (T ≃* QuaternionGroup 2) ∧ ¬ T ≤ GLAPPrimeCoreOf 3 (Kf 3 K (Subgroup.zpowers y)) ∧
      CycModSylow 3 (Kf 3 K (Subgroup.zpowers y)) := by
  have hcm := alpha_cycMod hin h hd hky hn hty hcyc
  obtain ⟨B', T₀, hyB', hY, hel, hcard, hT₀K, hT₀2, hT₀O, hT₀B⟩ :=
    alpha_Bstar_group hin h hd hky hn hty hcyc
  obtain ⟨T, hTK, hT2, hTB, hTc, hTQ, hTO⟩ :=
    alpha_Bstar_T hc hin h hd hky hyB' hY hel hcard hT₀K hT₀2 hT₀O hT₀B (caseAlphaEnd_chev2 hty.type) hcm
  exact ⟨B', T, hyB', hY, hel, hcard, hTK, hT2, hTB, hTc, hTQ, hTO, hcm⟩


theorem caseAlpha (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hA : CaseA p B x L b) : Alt1 G p := by
  have hcase : CaseAB G p B x L b := Or.inl hA
  have c := lemma105 hc hin.l105 h hd5 hcase
  obtain ⟨a, haD, hax, hlt, hC⟩ := lemma107 hc hin.l105 h hd5 hcase c
  have ac : AlphaCtx G p B x L b a := ⟨c, haD, hax, hlt, hC, hd5, hA⟩
  obtain ⟨E₀, F, y, E, K, hd⟩ := alpha_yEK hc hin h ac
  have hkay := alpha_kay hc hin h ac hd
  have hky := alpha_ky hc hin h ac hd hkay
  obtain ⟨hp3, ⟨n, hn, hn1, hty⟩, h6⟩ := alpha_158 hc hin h ac hd hkay hky
  subst hp3
  have hS := sstar_triple h.star
  have hBN := alpha_B_norm hc hin h hd hky hn hn1 hty.type
  have hnot := not_essential_y h6
  have hcyc := alpha_CB_cyclic hc hin h ac hd hkay hky hnot hBN
  obtain ⟨B', T, hyB', hY, hB'el, hB'card, hTK, hT2, hTB, hTcomm, hTQ, hTO, hcm⟩ :=
    alpha_Bstar hc hin h hd hky hn hty hcyc
  have hKyc : Kf 3 K (Subgroup.zpowers y) ≤ cx y := Ky_le_cx hd
  have hB'N := normalizes_of_inYK hKyc hY
  have hTne : T ≠ ⊥ := fun hT => hTcomm (by rw [hT]; simp)
  have hBmax' : GLAIsBmax 3 B' := ⟨hB'el, by rw [hB'card, hS.1.2.1], ⟨T, hTne, hT2, hTB⟩⟩
  have hess' : IsEssential 3 B' y := ⟨hyB', hd.y_ne, T, hTK.trans hKyc, hT2, hTB, hTcomm, fun _ => hTQ⟩
  have hSt : IsSTriple 3 B' y (Kf 3 K (Subgroup.zpowers y)) := ⟨hBmax', hess', hky.Ky_comp⟩
  have hGB := hin.i263 hc.ctx.rank_ge y _ B' n hBmax' hyB' hky.Ky_comp hY hn hn1 hty.type ⟨T, hTK, hT2, hTB, hTO⟩
  have hG : IsGStar 3 B' (Kf 3 K (Subgroup.zpowers y)) := by
    obtain ⟨E', hE'B, hE'el, hE'card, -, hE'ne⟩ := hGB
    exact ⟨E', hE'B, hE'el, hE'card, by rwa [closureIn_eq_self hB'N]⟩
  have hS0 : IsS0 3 B' y (Kf 3 K (Subgroup.zpowers y)) := ⟨hSt, by
    unfold tripleLevel
    rw [if_pos hG, hd5]⟩
  have hSStar : IsSStarMax 3 B' y (Kf 3 K (Subgroup.zpowers y)) :=
    ⟨hc.stage4o.2.2.2.2.1 B' y _ hS0 hcm, hcm⟩
  have hq := (hc.stage9.1 B' y _ hSStar).1
  have hchev := hc.stage8.1 B' y _ hSStar
  have haut := hin.l105.l104.lemma102.aut
  have hInn : InnDiagOn 3 B' (Kf 3 K (Subgroup.zpowers y)) :=
    haut.innDiag_unif _ _ B' hky.Ky_comp hchev hB'N fun g hg => by
      obtain ⟨i, k, hk, hgk⟩ := hY g hg
      exact haut.inner_innDiag _ _ g hky.Ky_comp hchev (hB'N hg) (inducesInner_of_inYK hKyc hk hgk)
  exact ⟨B', y, _, hSStar, (innDiagOn_iff hky.Ky_comp hq).2 hInn⟩

end S10

end CFSG.LocalAnalysis.GLTheoremA

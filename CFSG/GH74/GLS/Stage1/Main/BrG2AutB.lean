module

public import CFSG.GH74.GLS.Stage1.Main.BrG2AutA
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassT
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassU

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.IVK.Lifted
  CFSG.GH74.GLS.Stage2.Local

theorem pPrimeCore_eq_bot_of_equiv_sl2 {Q : Type} [Group Q] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    pPrimeCore 2 Q = ⊥ := by
  have : Finite Q := Finite.of_equiv _ e.symm.toEquiv
  rw [pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have hN' : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map hN _ e.surjective
  have hcard : Nat.card ↥(N.map e.toMonoidHom) = Nat.card ↥N :=
    Subgroup.card_map_of_injective e.injective
  have h0 := (pPrimeCore_eq_bot_iff).1 (pPrimeCore_two_sl2_five hodd h5) (N.map e.toMonoidHom) hN'
    (by rw [hcard]; exact hcop)
  exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).1 h0

section Hat

variable {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {F : Type} [Field F] [Finite F]

@[expose] noncomputable def hatEquivSL (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) : Thm2.Recip.Hat K ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
  ((QuotientGroup.quotientMulEquivOfEq (pPrimeCore_eq_bot_of_equiv_sl2 hodd h5 e)).trans
    QuotientGroup.quotientBot).trans e

omit [Finite Y] in
theorem congr_phi_apply (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {s : Y} (hs : s ∈ normalizer (K : Set Y)) (k : ↥K) :
    MulAut.congr (hatEquivSL hodd h5 e) (phi K s hs) (e k) =
      e ⟨s * k * s⁻¹, (mem_normalizer_iff.mp hs k).mp k.2⟩ := by
  have : (hatEquivSL hodd h5 e).symm (e k) = hatMk K k := by
    rw [MulEquiv.symm_apply_eq]; rfl
  show hatEquivSL hodd h5 e (phi K s hs ((hatEquivSL hodd h5 e).symm (e k))) = _
  rw [this, phi_mk]
  rfl

omit [Finite Y] in
theorem phi_one (K : Subgroup Y) (h : (1 : Y) ∈ normalizer (K : Set Y)) : phi K 1 h = 1 := by
  ext x
  obtain ⟨k, rfl⟩ := hatMk_surjective K x
  rw [phi_mk]
  simp

omit [Finite Y] in
theorem phi_pow (K : Subgroup Y) {g : Y} (hg : g ∈ normalizer (K : Set Y)) (m : ℕ) :
    phi K (g ^ m) (pow_mem hg m) = phi K g hg ^ m := by
  induction m with
  | zero =>
    ext x
    obtain ⟨k, rfl⟩ := hatMk_surjective K x
    rw [phi_mk]
    simp
  | succ m ih =>
    have := phi_mul K (pow_mem hg m) hg
    rw [phi_congr K (pow_succ g m) (pow_mem hg (m + 1)) (mul_mem (pow_mem hg m) hg), this, ih, pow_succ]

theorem not_inducesInner_of_outer (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {u : Y} (hu2 : u * u = 1)
    {P : Subgroup Y} (hPK : P ≤ K) (hPs : CFSG.ABGLocalTools.IsSylowOf 2 P K)
    (huP : ∀ p ∈ P, u * p * u⁻¹ ∈ P)
    (hout : ∀ p ∈ P, ∃ x ∈ K, (u * p⁻¹) * x ≠ x * (u * p⁻¹)) :
    ¬ InducesInner u K := by
  rintro ⟨k, hkK, hk⟩
  have hO : pPrimeCoreOf 2 K = ⊥ := by
    unfold pPrimeCoreOf
    rw [pPrimeCore_eq_bot_of_equiv_sl2 hodd h5 e, Subgroup.map_bot]
  have hcomm : ∀ x ∈ K, (u * k⁻¹) * x = x * (u * k⁻¹) := by
    intro x hx
    have h1 := hk.2.2 x hx
    rw [hO, Subgroup.mem_bot] at h1
    have h2 : x * (u * k⁻¹) * x⁻¹ * (u * k⁻¹)⁻¹ = 1 := h1
    calc (u * k⁻¹) * x = (x * (u * k⁻¹) * x⁻¹ * (u * k⁻¹)⁻¹) * ((u * k⁻¹) * x) := by rw [h2, one_mul]
      _ = x * (u * k⁻¹) := by group
  have hconj : ∀ x ∈ K, u * x * u⁻¹ = k * x * k⁻¹ := by
    intro x hx
    have hy : k * x * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hkK hx) (K.inv_mem hkK)
    have h := hcomm _ hy
    calc u * x * u⁻¹ = (u * k⁻¹) * (k * x * k⁻¹) * (u * k⁻¹)⁻¹ := by group
      _ = (k * x * k⁻¹) * (u * k⁻¹) * (u * k⁻¹)⁻¹ := by rw [h]
      _ = k * x * k⁻¹ := by group
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hk2 : ∀ x ∈ K, k * k * x = x * (k * k) := by
    intro x hx
    have hx' : k * x * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hkK hx) (K.inv_mem hkK)
    have h1 : u * (k * x * k⁻¹) * u⁻¹ = k * (k * x * k⁻¹) * k⁻¹ := hconj _ hx'
    have h2 : u * (k * x * k⁻¹) * u⁻¹ = x := by
      rw [← hconj x hx]
      calc u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u⁻¹ * u⁻¹) := by group
        _ = x := by rw [hu2, hui, hu2]; group
    calc k * k * x = (k * (k * x * k⁻¹) * k⁻¹) * (k * k) := by group
      _ = x * (k * k) := by rw [← h1, h2]
  have hkk : (k * k) * (k * k) = 1 := by
    have hcen : (e ⟨k, hkK⟩) * (e ⟨k, hkK⟩) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := e.surjective g
      have h' : (⟨k, hkK⟩ * ⟨k, hkK⟩ : ↥K) * x = x * (⟨k, hkK⟩ * ⟨k, hkK⟩) := Subtype.ext (hk2 x.1 x.2)
      have h'' : e (x * (⟨k, hkK⟩ * ⟨k, hkK⟩)) = e ((⟨k, hkK⟩ * ⟨k, hkK⟩) * x) := by rw [h']
      simp only [map_mul] at h''
      exact h''

    have h1 := sq_eq_one_of_mem_center_sl2 hcen
    have h2 : ((⟨k, hkK⟩ : ↥K) * ⟨k, hkK⟩) * (⟨k, hkK⟩ * ⟨k, hkK⟩) = 1 := by
      apply e.injective
      simp only [map_mul, map_one]
      exact h1
    exact congrArg Subtype.val h2
  have hnorm : k ∈ normalizer (P : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      rw [← hconj p (hPK hp)]
      exact huP p hp
    · intro hp
      have hpK : p ∈ K := by
        have := K.mul_mem (K.mul_mem (K.inv_mem hkK) (hPK hp)) hkK
        simpa [mul_assoc] using this
      have h0 : u * p * u⁻¹ ∈ P := by rw [hconj p hpK]; exact hp
      have h1 := huP _ h0
      have e1 : u * (u * p * u⁻¹) * u⁻¹ = p := by
        calc u * (u * p * u⁻¹) * u⁻¹ = (u * u) * p * (u⁻¹ * u⁻¹) := by group
          _ = p := by rw [hu2, hui, hu2]; group
      rw [e1] at h1
      exact h1
  have hgrp : IsPGroup 2 ↥(Subgroup.zpowers k) := by
    have h4 : k ^ 4 = 1 := by
      have : k ^ 4 = (k * k) * (k * k) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      rw [this]; exact hkk
    have hord : orderOf k ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h4)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hsup : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers k) :=
    hPs.isPGroup.to_sup_of_normal_left' hgrp (Subgroup.zpowers_le.2 hnorm)
  have heq : P ⊔ Subgroup.zpowers k = P :=
    hPs.eq_of_le le_sup_left (sup_le hPK (Subgroup.zpowers_le.2 hkK)) hsup
  have hkP : k ∈ P := by
    rw [← heq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers k)
  obtain ⟨x, hx, hne⟩ := hout k hkP
  exact hne (hcomm x hx)

end Hat

theorem pglQuot_of_outer {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (e : ↥K ≃* StatedSL 2 F)
    {ζ u : Y} (hζK : ζ ∈ K) (hKζ : K ≤ centralizer ({ζ} : Set Y)) (hζ2 : orderOf ζ = 2)
    (huN : u ∈ normalizer (K : Set Y)) (hu2 : u * u = 1)
    {P : Subgroup Y} (hPK : P ≤ K) (hPs : CFSG.ABGLocalTools.IsSylowOf 2 P K)
    (huP : ∀ p ∈ P, u * p * u⁻¹ ∈ P)
    (hout : ∀ p ∈ P, ∃ x ∈ K, (u * p⁻¹) * x ≠ x * (u * p⁻¹))
    {g : Y} (hgN : g ∈ normalizer (K : Set Y)) (hg2 : ∃ m : ℕ, g ^ (2 ^ m) = 1)
    (hug : ∃ k ∈ K, ∀ x ∈ K, u * x * u⁻¹ = k * (g * x * g⁻¹) * k⁻¹)
    (hfix : (∃ n : ℕ, 2 ≤ n ∧ (Nat.card ↥(StatedSL 2 F)).factorization 2 = n + 1 ∧
        ∃ c ∈ K, orderOf c = 2 ^ n ∧ g * c = c * g) ∨ (Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)) :
    PGLQuot ζ u K F := by
  have h5 : 5 ≤ Nat.card F := by
    obtain ⟨m, hm⟩ := hodd
    omega
  set eS : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (specialLinearGroupEquivStatedSL 2 F).symm with heS
  set e' := hatEquivSL hodd h5 eS with he'
  have hO : pPrimeCoreOf 2 K = ⊥ := by
    unfold pPrimeCoreOf
    rw [pPrimeCore_eq_bot_of_equiv_sl2 hodd h5 eS, Subgroup.map_bot]
  have hcen : Nat.card (center (Thm2.Recip.Hat K)) = 2 := by
    refine le_antisymm (card_center_le_two (e'.trans (specialLinearGroupEquivStatedSL 2 F))) ?_
    have hzc : hatMk K ⟨ζ, hζK⟩ ∈ center (Thm2.Recip.Hat K) := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨y, rfl⟩ := hatMk_surjective K x
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 (hKζ y.2)
    have hne : center (Thm2.Recip.Hat K) ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot, hatMk_eq_one_iff, hO, Subgroup.mem_bot] at hzc
      have : ζ = 1 := hzc
      rw [this, orderOf_one] at hζ2
      exact absurd hζ2 (by norm_num)
    exact (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hwin : ¬ phi K u huN ∈ innOf (Thm2.Recip.Hat K) := fun h =>
    not_inducesInner_of_outer hodd h5 eS hu2 hPK hPs huP hout ((phi_mem_inn_iff K huN).1 h)
  have hσ : (gammaOf hodd h3 (MulAut.congr e' (phi K u huN))).right = 1 := by
    obtain ⟨k, hkK, hk⟩ := hug
    have hβγ : MulAut.congr e' (phi K u huN) =
        MulAut.conj (eS ⟨k, hkK⟩) * MulAut.congr e' (phi K g hgN) := by
      apply MulEquiv.ext
      intro s
      obtain ⟨x, rfl⟩ := eS.surjective s
      rw [MulAut.mul_apply, congr_phi_apply hodd h5 eS huN, congr_phi_apply hodd h5 eS hgN,
        MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hk x x.2
    have hγ2 : ∃ m : ℕ, MulAut.congr e' (phi K g hgN) ^ (2 ^ m) = 1 := by
      obtain ⟨m, hm⟩ := hg2
      refine ⟨m, ?_⟩
      rw [← map_pow, ← phi_pow K hgN, phi_congr K hm (pow_mem hgN _) (one_mem _), phi_one, map_one]
    have hr : (gammaOf hodd h3 (MulAut.congr e' (phi K g hgN))).right = 1 := by
      rcases hfix with ⟨n, hn, hv, c, hcK, hco, hgc⟩ | hmod
      · refine field_part_trivial_big hodd h3 hn hv (c := eS ⟨c, hcK⟩) ?_ _ ?_ hγ2
        · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
          exact hco
        · rw [congr_phi_apply hodd h5 eS hgN]
          congr 1
          apply Subtype.ext
          calc g * c * g⁻¹ = c * g * g⁻¹ := by rw [hgc]
            _ = c := by group
      · exact field_part_trivial_small hodd h3 hmod _ hγ2
    rw [hβγ, gammaOf_mul_right, hr, gammaOf_conj_right, one_mul]
  exact exists_pglQuot hodd h3 e' hζK hKζ hζ2 hcen huN hu2 hwin hσ

theorem central_of_card_le_two {Y : Type} [Group Y] [Finite Y] {N B : Subgroup Y} (hNB : N ≤ B)
    (hN : (N.subgroupOf B).Normal) (hcard : Nat.card ↥N ≤ 2) :
    ∀ n ∈ N, ∀ b ∈ B, b * n * b⁻¹ = n := by
  intro n hn b hb
  by_cases hn1 : n = 1
  · rw [hn1]; group
  have hbn : b * n * b⁻¹ ∈ N := by
    have := hN.conj_mem ⟨n, hNB hn⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨b, hb⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hb1 : b * n * b⁻¹ ≠ 1 := by
    intro h
    apply hn1
    have : n = b⁻¹ * (b * n * b⁻¹) * b := by group
    rw [this, h]; group
  have hzN : ∀ x ∈ N, x ≠ 1 → Subgroup.zpowers x = N ∧ orderOf x = 2 := by
    intro x hx hx1
    have hle : Subgroup.zpowers x ≤ N := Subgroup.zpowers_le.2 hx
    have h1 : 2 ≤ orderOf x := by
      have h0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
      have h1' : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
      omega
    have h2 : orderOf x ≤ 2 := by
      calc orderOf x = Nat.card (Subgroup.zpowers x) := (Nat.card_zpowers x).symm
        _ ≤ Nat.card N := Subgroup.card_le_of_le hle
        _ ≤ 2 := hcard
    have hox : orderOf x = 2 := le_antisymm h2 h1
    refine ⟨Subgroup.eq_of_le_of_card_ge hle ?_, hox⟩
    rw [Nat.card_zpowers, hox]
    exact hcard
  obtain ⟨hz1, ho1⟩ := hzN n hn hn1
  obtain ⟨hz2, ho2⟩ := hzN _ hbn hb1
  have hmem : n ∈ Subgroup.zpowers (b * n * b⁻¹) := by rw [hz2]; exact hn
  rcases eq_one_or_of_mem_zpowers_two ho2 hmem with h | h
  · exact absurd h hn1
  · exact h.symm

theorem inducedPGL2_of_pglQuot_abs {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {F : Type} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (e : ↥K ≃* StatedSL 2 F)
    {ζ u : Y} (hu2 : u * u = 1) (huN : u ∈ normalizer (K : Set Y)) (h : PGLQuot ζ u K F)
    {T : Subgroup Y} (hTN : T ≤ normalizer (K : Set Y)) (huT : u ∈ T)
    (hTle : T ≤ (K ⊔ zpowers u) ⊔ centralizer (K : Set Y)) : InducedPGL2 K T (Nat.card F) := by
  classical
  have h5 : 5 ≤ Nat.card F := by
    obtain ⟨m, hm⟩ := hodd
    omega
  set eS : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (specialLinearGroupEquivStatedSL 2 F).symm with heS
  obtain ⟨hZn, ⟨φ⟩⟩ := h
  set B : Subgroup Y := K ⊔ zpowers u with hB
  set Z : Subgroup Y := pPrimeCoreOf 2 K ⊔ zpowers ζ with hZ
  set N : Subgroup Y := Z ⊓ B with hN
  have hNB : N ≤ B := inf_le_right
  have hLB : K ≤ B := le_sup_left
  have hNsub : N.subgroupOf B = Z.subgroupOf B := Subgroup.inf_subgroupOf_right Z B
  have hNn : (N.subgroupOf B).Normal := by rw [hNsub]; exact hZn
  let φ' : ↥B ⧸ N.subgroupOf B ≃* CFSG.GorensteinWalter.PGL2 F :=
    (QuotientGroup.quotientMulEquivOfEq hNsub).trans φ
  have hqpos : 0 < Nat.card F * (Nat.card F ^ 2 - 1) := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) h1
    exact Nat.mul_pos (by omega) (by omega)
  have hBcard : Nat.card ↥B = Nat.card ↥N * (Nat.card F * (Nat.card F ^ 2 - 1)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf B)
    have h2 : Nat.card ↥(N.subgroupOf B) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv
    have h3' : Nat.card (↥B ⧸ N.subgroupOf B) = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [Nat.card_congr φ'.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula]
    rw [h1, h2, h3', mul_comm]
  have hKcard : Nat.card ↥K = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr eS.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hidx : K.relIndex B ≤ 2 := relIndex_le_two_of_involution hu2 huN
  have hBcard2 : Nat.card ↥B ≤ 2 * Nat.card ↥K := by
    have h1 := Subgroup.relIndex_mul_card K B
    rw [inf_eq_left.2 hLB] at h1
    calc Nat.card ↥B = K.relIndex B * Nat.card ↥K := h1.symm
      _ ≤ 2 * Nat.card ↥K := Nat.mul_le_mul_right _ hidx
  have hNle : Nat.card ↥N ≤ 2 := by
    rw [hBcard, hKcard] at hBcard2
    have := Nat.le_of_mul_le_mul_right (by linarith : Nat.card ↥N * (Nat.card F * (Nat.card F ^ 2 - 1)) ≤ 2 * (Nat.card F * (Nat.card F ^ 2 - 1))) hqpos
    exact this
  have hNc := central_of_card_le_two hNB hNn hNle
  have hNC : N ≤ centralizer (K : Set Y) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := hNc n hn k (hLB hk)
    calc k * n = (k * n * k⁻¹) * k := by group
      _ = n * k := by rw [this]
  have hOdd := CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hodd
  have hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F (by omega)
  have hperf : Group.IsPerfect ↥K :=
    Group.IsPerfect.ofSurjective (G := Matrix.SpecialLinearGroup (Fin 2) F) (G' := ↥K)
      (f := eS.symm.toMonoidHom) eS.symm.surjective
  have hBC : B ⊓ centralizer (K : Set Y) = N := by
    apply le_antisymm
    · exact inf_centralizer_le_Z hLB hperf hidx (hZn := hNn) hOdd h3 φ'
    · exact le_inf hNB hNC
  have hBN : B ≤ normalizer (K : Set Y) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 huN)
  have hBT : B ≤ K ⊔ T := sup_le le_sup_left ((Subgroup.zpowers_le.2 huT).trans le_sup_right)
  have hA : K ⊔ T ≤ B ⊔ centralizer (K : Set Y) := sup_le (hLB.trans le_sup_left) hTle
  obtain ⟨hCn, ⟨e2⟩⟩ := inducedQuot_equiv hBN hTN hBT hA hBC (hZn := hNn)
  exact ⟨hCn, F, inferInstance, inferInstance, rfl, ⟨e2.trans φ'⟩⟩

end CFSG.GH74.GLS.Stage1.Main

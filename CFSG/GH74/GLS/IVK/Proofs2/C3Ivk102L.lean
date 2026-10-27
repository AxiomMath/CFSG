module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma118
public import CFSG.GH74.GLS.IVK.Proofs2.Pgl2Three
public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.GH74.GLS.C3.Layer1.BkIvk10Stmt
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.GH74.GLS.IVK.L2.Lemma12hc

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

theorem perm4_aux : ∀ w : Equiv.Perm (Fin 4), w ≠ 1 → w ^ 3 = 1 →
    ∃ g : Equiv.Perm (Fin 4), (w * (g * w * g⁻¹)) ^ 2 = 1 ∧ w * (g * w * g⁻¹) ≠ 1 := by
  decide +kernel

theorem perm4_odd_normal (W : Subgroup (Equiv.Perm (Fin 4))) [W.Normal] (hW : Odd (Nat.card W)) :
    W = ⊥ := by
  by_contra hne
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hodd : Odd (orderOf w) := Odd.of_dvd_nat hW (Subgroup.orderOf_dvd_natCard W hw)
  have h24 : orderOf w ∣ 24 := by
    have := orderOf_dvd_natCard w
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      show Nat.factorial 4 = 24 from rfl] at this
  have h3 : orderOf w ∣ 3 := by
    have hc : Nat.Coprime (orderOf w) 8 := by
      have := Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)
      simpa using this
    exact hc.dvd_of_dvd_mul_left (by simpa using h24)
  have hw3 : w ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 h3
  obtain ⟨g, hg2, hg1⟩ := perm4_aux w hw1' hw3
  have hc : w * (g * w * g⁻¹) ∈ W := W.mul_mem hw (Subgroup.Normal.conj_mem inferInstance w hw g)
  have hord : orderOf (w * (g * w * g⁻¹)) = 2 := orderOf_eq_prime hg2 hg1
  have hdvd : 2 ∣ Nat.card W := hord ▸ Subgroup.orderOf_dvd_natCard W hc
  exact (Nat.not_even_iff_odd.2 hW) (even_iff_two_dvd.2 hdvd)

theorem eq_bot_of_normal_odd_of_equiv_perm4 {C : Type*} [Group C] (ρ : C ≃* Equiv.Perm (Fin 4))
    (W : Subgroup C) [W.Normal] (hW : Odd (Nat.card W)) : W = ⊥ := by
  have hN : (W.map ρ.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ ρ.surjective
  have hodd : Odd (Nat.card (W.map ρ.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective ρ.injective]
    exact hW
  have h := perm4_odd_normal _ hodd
  exact (Subgroup.map_eq_bot_iff_of_injective _ ρ.injective).mp h

section Arith

theorem exists_two_pow_of_isFM9 {q : ℕ} (h : IsFM9 q) : ∃ a : ℕ, q = 2 ^ a + 1 ∨ q + 1 = 2 ^ a := by
  rcases h with rfl | ⟨-, ⟨k, hk⟩ | ⟨n, hn⟩⟩
  · exact ⟨3, Or.inl (by norm_num)⟩
  · exact ⟨2 ^ k, Or.inl hk⟩
  · exact ⟨n, Or.inr hn⟩

theorem exists_two_pow_of_isFM9_mod {q : ℕ} (hq3 : 3 < q) (h : IsFM9 q) {ε : ℤ}
    (hε1 : ε = 1 ∨ ε = -1) (hε : (q : ℤ) ≡ ε [ZMOD 4]) {d : ℕ} (hd : (d : ℤ) = q - ε) :
    ∃ a : ℕ, d = 2 ^ a := by
  obtain ⟨a, ha | ha⟩ := exists_two_pow_of_isFM9 h
  · rcases hε1 with rfl | rfl
    · exact ⟨a, by omega⟩
    · exfalso
      unfold Int.ModEq at hε
      rcases Nat.lt_or_ge a 2 with h2 | h2
      · interval_cases a <;> omega
      · have : 2 ^ 2 ∣ 2 ^ a := pow_dvd_pow 2 h2
        omega
  · rcases hε1 with rfl | rfl
    · exfalso
      unfold Int.ModEq at hε
      rcases Nat.lt_or_ge a 2 with h2 | h2
      · interval_cases a <;> omega
      · have : 2 ^ 2 ∣ 2 ^ a := pow_dvd_pow 2 h2
        omega
    · exact ⟨a, by omega⟩

end Arith

section L2

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem card_fieldAutSub_of_isFM9 (hF : L2Field F) (hfm : IsFM9 (Nat.card F)) (e : K ≃* L2 F) :
    Nat.card ↥(fieldAutSub e) = 1 ∨ Nat.card ↥(fieldAutSub e) = 2 := by
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := isOddPrimePower_of_L2Field hF
  rw [(ivk_1_2e F hF K e).2.2 p n hp hq]
  rcases hfm with h9 | ⟨hprime, -⟩
  · rw [hq] at h9
    have hp3 : p = 3 := by
      have h1 : p ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
        exact dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h1)
    subst hp3
    right
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h9.trans (by norm_num : 9 = 3 ^ 2))
  · left
    rw [hq] at hprime
    exact ((Nat.Prime.pow_eq_iff hprime).1 rfl).2

theorem mem_innAut_of_odd_orderOf (hF : L2Field F) (hfm : IsFM9 (Nat.card F)) (e : K ≃* L2 F)
    {w : MulAut K} (hw : Odd (orderOf w)) : w ∈ innAut K := by
  have hidx : (innAut K).index * Nat.card K = (2 * Nat.card ↥(fieldAutSub e)) * Nat.card K := by
    rw [← card_innAut e, Subgroup.index_mul_card, card_mulAut_eq e, card_innDiagSub e hF,
      card_innAut e]
    ring
  have hidx' : (innAut K).index = 2 * Nat.card ↥(fieldAutSub e) :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos hidx
  have h4 : (innAut K).index ∣ 2 ^ 2 := by
    rcases card_fieldAutSub_of_isFM9 hF hfm e with h | h <;> rw [hidx', h] <;> norm_num
  have h1 : orderOf (QuotientGroup.mk' (innAut K) w) ∣ orderOf w := orderOf_map_dvd _ _
  have h2 : orderOf (QuotientGroup.mk' (innAut K) w) ∣ (innAut K).index := orderOf_dvd_natCard _
  have hodd : Odd (orderOf (QuotientGroup.mk' (innAut K) w)) := Odd.of_dvd_nat hw h1
  have h5 : orderOf (QuotientGroup.mk' (innAut K) w) = 1 :=
    Lemma118.odd_dvd_two_pow hodd (h2.trans h4)
  exact (QuotientGroup.eq_one_iff w).1 (orderOf_eq_one_iff.1 h5)

theorem exists_two_pow_card_centralizer (hF : L2Field F) (hfm : IsFM9 (Nat.card F))
    (e : K ≃* L2 F) {u : K} (hu : orderOf u = 2) :
    ∃ a : ℕ, Nat.card ↥(centralizer ({u} : Set K)) = 2 ^ a := by
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    obtain ⟨t, ht⟩ := hF.1
    by_cases h : t % 2 = 0
    · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
    · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
    ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by have := hF.2; omega)⟩
  obtain ⟨k, hkd, hk2, ⟨ψ⟩⟩ := (ivk_1_3a F hF K e ε hε1 hε d hd u hu).2.1
  have : NeZero k := ⟨by omega⟩
  have hcard : Nat.card ↥(centralizer ({u} : Set K)) = d := by
    rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card, hkd]
  obtain ⟨a, ha⟩ := exists_two_pow_of_isFM9_mod hF.2 hfm hε1 hε hd
  exact ⟨a, hcard.trans ha⟩

end L2

section Fixed

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem mul_conj_mul_inv (φ : MulAut K) (k : K) : φ * MulAut.conj k * φ⁻¹ = MulAut.conj (φ k) := by
  ext a
  simp [MulAut.conj_apply]

theorem exists_normal_odd_fixed (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (hodd : ∀ w : MulAut K, Odd (orderOf w) → w ∈ innAut K)
    {y : MulAut K} {H : Subgroup (MulAut K)} (hH : innAut K ≤ H)
    (hW : pPrimeCoreOf 2 (H ⊓ centralizer ({y} : Set (MulAut K))) ≠ ⊥) :
    ∃ W' : Subgroup K, W' ≠ ⊥ ∧ W' ≤ fixedSubgroup K y ∧ Odd (Nat.card ↥W') ∧
      ∀ c ∈ fixedSubgroup K y, ∀ k ∈ W', c * k * c⁻¹ ∈ W' := by
  set C : Subgroup (MulAut K) := H ⊓ centralizer ({y} : Set (MulAut K)) with hCdef
  set W : Subgroup (MulAut K) := pPrimeCoreOf 2 C with hWdef
  have hWodd : Odd (Nat.card ↥W) := TwoThin.card_pPrimeCoreOf_odd C
  have hWC : W ≤ C := TwoThin.pPrimeCoreOf_le C
  have hWinn : W ≤ innAut K := fun w hw =>
    hodd w (Odd.of_dvd_nat hWodd (Subgroup.orderOf_dvd_natCard W hw))
  have hmap : (W.comap (MulAut.conj : K →* MulAut K)).map (MulAut.conj : K →* MulAut K) = W :=
    Subgroup.map_comap_eq_self hWinn
  have hyc : ∀ k : K, MulAut.conj k ∈ C → y k = k := by
    intro k hk
    have h1 : MulAut.conj k * y = y * MulAut.conj k :=
      mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hk).2
    have h2 : MulAut.conj (y k) = MulAut.conj k := by
      rw [← mul_conj_mul_inv, ← h1]
      group
    exact hinj h2
  refine ⟨W.comap (MulAut.conj : K →* MulAut K), ?_, ?_, ?_, ?_⟩
  · intro hbot
    apply hW
    rw [← hmap, hbot, Subgroup.map_bot]
  · intro k hk
    exact hyc k (hWC hk)
  · rw [← Subgroup.card_map_of_injective hinj, hmap]
    exact hWodd
  · intro c hc k hk
    have hcc : MulAut.conj c ∈ C := by
      refine Subgroup.mem_inf.2 ⟨hH ⟨c, rfl⟩, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have h2 : MulAut.conj (y c) = MulAut.conj c := by rw [show y c = c from hc]
      have h3 : y * MulAut.conj c * y⁻¹ = MulAut.conj c := by rw [mul_conj_mul_inv, h2]
      calc MulAut.conj c * y = (y * MulAut.conj c * y⁻¹) * y := by rw [h3]
        _ = y * MulAut.conj c := by group
    have := TwoThin.pPrimeCoreOf_normalized C hcc hk
    simpa using this

end Fixed

section Model

theorem exists_l2Field_of_hasL2Model {K : Type} [Group K] {q : ℕ} (hq : IsFM9 q)
    (h : HasL2Model K (fun r => r = q)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : K ≃* L2 F), L2Field F ∧ Nat.card F = q := by
  obtain ⟨p, f, hp, hf, hqe, hL⟩ := h
  rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hodd : Odd q := isFM9_odd hq
    refine ⟨F, hF, hFin, e, ⟨by rw [hcard, hqe]; exact hodd, ?_⟩, by rw [hcard, hqe]⟩
    have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    have h2 : (2, p ^ f) ≠ (2, 3) := hadm.2.2.2.2
    have h3 : p ^ f ≠ 3 := fun h => h2 (by rw [h])
    have h4 : q % 2 = 1 := Nat.odd_iff.1 hodd
    rw [hcard]
    omega
  all_goals exact absurd h0 (by norm_num)

theorem isSimpleGroup_of_l2 {F : Type} [Field F] [Finite F] {K : Type} [Group K] (hF : L2Field F)
    (e : K ≃* L2 F) : IsSimpleGroup K := by
  have h4 : 4 ≤ Nat.card F := by
    obtain ⟨⟨t, ht⟩, h3⟩ := hF
    omega
  have : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (toPSL e).isSimpleGroup

theorem even_card_of_l2 {F : Type} [Field F] [Finite F] {K : Type} [Group K] (hF : L2Field F)
    (e : K ≃* L2 F) : Even (Nat.card K) := by
  rw [card_eq_of_L2Field e hF]
  obtain ⟨m, hm⟩ := Nat.eight_dvd_sq_sub_one_of_odd hF.1
  rw [hm, show Nat.card F * (8 * m) = 8 * (Nat.card F * m) by ring]
  exact ⟨2 * (Nat.card F * m), by omega⟩

end Model

section Conj

variable {K : Type} [Group K]

theorem map_fixedSubgroup_eq {y f a : MulAut K} (h : a * y * a⁻¹ = f) :
    (fixedSubgroup K y).map (a : K ≃* K).toMonoidHom = fixedSubgroup K f := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : y k = k := hk
    show f (a k) = a k
    rw [← h]
    simp [hk']
  · intro hx
    have hx' : f x = x := hx
    refine ⟨a⁻¹ x, ?_, by simp⟩
    show y (a⁻¹ x) = a⁻¹ x
    have h1 : a * y = f * a := by rw [← h]; group
    have h2 : y = a⁻¹ * f * a := by
      calc y = a⁻¹ * (a * y) := by group
        _ = a⁻¹ * (f * a) := by rw [h1]
        _ = a⁻¹ * f * a := by group
    rw [h2]
    show a⁻¹ (f (a (a⁻¹ x))) = a⁻¹ x
    simp [hx']

noncomputable def fixedSubgroupEquivOfConj {y f a : MulAut K} (h : a * y * a⁻¹ = f) :
    ↥(fixedSubgroup K y) ≃* ↥(fixedSubgroup K f) :=
  ((a : K ≃* K).subgroupMap (fixedSubgroup K y)).trans
    (MulEquiv.subgroupCongr (map_fixedSubgroup_eq h))

end Conj

section Outer

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem exists_equiv_perm4_fixedSubgroup (hF : L2Field F) (hfm : IsFM9 (Nat.card F)) (e : K ≃* L2 F)
    (N : L2Notation e) {y : MulAut K} (hy2 : y ^ 2 = 1) (hyD : y ∉ innDiagSub e) :
    Nat.card F = 9 ∧ Nonempty (↥(fixedSubgroup K y) ≃* Equiv.Perm (Fin 4)) := by
  have hyInn : y ∉ innAut K := fun h => hyD (innAut_le_innDiagSub e h)
  obtain ⟨g, hg, hyg⟩ := fieldAutHom_fieldProj_mul e y
  have hσ1 : fieldProj e y ≠ 1 := fun h => hyD ((mem_innDiagSub_iff e y).2 h)
  have hσ2 : fieldProj e y ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  have hσo : orderOf (fieldProj e y) = 2 := orderOf_eq_prime hσ2 hσ1
  have hf1 : fieldAutHom e (fieldProj e y) ≠ 1 := fun h =>
    hσ1 (fieldAutHom_injective e (h.trans (map_one _).symm))
  have hf2 : fieldAutHom e (fieldProj e y) ^ 2 = 1 := by rw [← map_pow, hσ2, map_one]
  have hfo : orderOf (fieldAutHom e (fieldProj e y)) = 2 := orderOf_eq_prime hf2 hf1
  have hfF : fieldAutHom e (fieldProj e y) ∈ fieldAutSub e := ⟨_, rfl⟩
  have hfT : fieldAutHom e (fieldProj e y) ∈ (N.T : Subgroup (MulAut K)) := by
    have hP : IsPGroup 2 ↥(zpowers (fieldAutHom e (fieldProj e y))) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hfo]; norm_num)
    have h1 := hP.inf_normalizer_sylow N.T
    have h2 : fieldAutHom e (fieldProj e y) ∈
        zpowers (fieldAutHom e (fieldProj e y)) ⊓ normalizer (N.T : Set (MulAut K)) :=
      ⟨mem_zpowers _, N.T_inv hfF⟩
    rw [h1] at h2
    exact h2.2
  have hyo : orderOf (g * fieldAutHom e (fieldProj e y)) = 2 := by
    rw [← hyg]
    exact orderOf_eq_prime hy2 (fun h => hyInn (by rw [h]; exact one_mem _))
  obtain ⟨a, -, hay⟩ := ivk_1_2h_c F hF K e N _ ⟨hfT, hfF⟩ hfo g hg hyo
  rw [← hyg] at hay
  obtain ⟨F₀, _, _, hF₀, ⟨φ⟩⟩ :=
    (ivk_1_4a F hF K e (fieldProj e y)).2.2 (by rw [hσo]; exact even_two)
  rw [hσo] at hF₀
  have hF03 : Nat.card F₀ = 3 := by
    rcases hfm with h9 | ⟨hprime, -⟩
    · rw [← hF₀] at h9
      exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) (h9.trans (by norm_num : 9 = 3 ^ 2))
    · rw [← hF₀] at hprime
      exact absurd ((Nat.Prime.pow_eq_iff hprime).1 rfl).2 (by norm_num)
  obtain ⟨π⟩ := exists_pgl2_equiv_perm hF03
  refine ⟨?_, ⟨((fixedSubgroupEquivOfConj hay).trans φ).trans π⟩⟩
  rw [← hF₀, hF03]
  norm_num

end Outer

section Main

theorem b_ivk_10_2L : CFSG.GH74.GLS.C3.Layer1.Bk.B_ivk_10_2L := by
  intro K _ _ q hq hmodel y H hH hy2 hW
  obtain ⟨F, _, _, e0, hF, hFq⟩ := exists_l2Field_of_hasL2Model hq hmodel
  have hfm : IsFM9 (Nat.card F) := hFq ▸ hq
  obtain ⟨e, N, -⟩ := ivk_1_2a_exists F hF K e0 (inferInstance : Nonempty (Sylow 2 (MulAut K))).some
  have hinj := conj_injective_of_L2 e
  have hH' : innAut K ≤ H := hH
  obtain ⟨W', hne, hle, hodd, hnorm⟩ :=
    exists_normal_odd_fixed hinj (fun w hw => mem_innAut_of_odd_orderOf hF hfm e hw) hH' hW
  by_cases hyInn : y ∈ innAut K
  ·
    exfalso
    obtain ⟨u, rfl⟩ := hyInn
    have hu2 : u ^ 2 = 1 := by
      apply hinj
      rw [map_pow, hy2, map_one]
    by_cases hu1 : u = 1
    · subst hu1
      have hs : IsSimpleGroup K := isSimpleGroup_of_l2 hF e
      have hN : W'.Normal := ⟨fun k hk c => hnorm c (by simp [fixedSubgroup]) k hk⟩
      rcases hs.eq_bot_or_eq_top_of_normal W' with h | h
      · exact hne h
      · rw [h, Subgroup.card_top] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) (even_card_of_l2 hF e)
    · have hu : orderOf u = 2 := orderOf_eq_prime hu2 hu1
      obtain ⟨a, ha⟩ := exists_two_pow_card_centralizer hF hfm e hu
      have hle' : W' ≤ centralizer ({u} : Set K) := by
        rw [← Lemma118.fixedSubgroup_conj]
        exact hle
      have hdvd : Nat.card ↥W' ∣ 2 ^ a := ha ▸ Subgroup.card_dvd_of_le hle'
      exact hne (Subgroup.card_eq_one.1 (Lemma118.odd_dvd_two_pow hodd hdvd))
  · refine ⟨hyInn, ?_⟩
    by_cases hyD : y ∈ innDiagSub e
    ·
      have hsup := innAut_sup_zpowers_eq e hF hyD hyInn
      exact ⟨F, inferInstance, inferInstance, hFq,
        ⟨(MulEquiv.subgroupCongr hsup).trans (MonoidHom.ofInjective (innDiagHom_injective e)).symm⟩⟩
    ·
      exfalso
      obtain ⟨-, ⟨ρ⟩⟩ := exists_equiv_perm4_fixedSubgroup hF hfm e N hy2 hyD
      have hWn : (W'.subgroupOf (fixedSubgroup K y)).Normal := ⟨fun n hn c => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact hnorm c c.2 n hn⟩
      have hWodd : Odd (Nat.card ↥(W'.subgroupOf (fixedSubgroup K y))) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
        exact hodd
      have hbot := eq_bot_of_normal_odd_of_equiv_perm4 ρ _ hWodd
      apply hne
      rw [Subgroup.eq_bot_iff_forall]
      intro k hk
      have hk' : (⟨k, hle hk⟩ : ↥(fixedSubgroup K y)) ∈ W'.subgroupOf (fixedSubgroup K y) := hk
      rw [hbot, Subgroup.mem_bot] at hk'
      exact congrArg Subtype.val hk'

end Main

end CFSG.GH74.GLS.IVK.Proofs2

module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48NSV
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48CenFact

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin KFactProofs.Sp48 CFSG.PreuniquenessRankFour.Helpers

namespace KFactProofs.Sp48

section A

variable {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal] {e : K ≃* Sp8} {T : Subgroup Y} {y : Y}

omit [K.Normal] in
theorem Sp48Setup.y_pow_comm_E (S : Sp48Setup e T y) {s : Sp8} (hs : s ∈ spE) (j : ℕ) :
    y ^ j * emb e s = emb e s * y ^ j := by
  have h := S.y_pow_act j s
  rw [fr_pow_spE hs] at h
  calc y ^ j * emb e s = (y ^ j * emb e s * (y ^ j)⁻¹) * y ^ j := by group
    _ = emb e s * y ^ j := by rw [h]

omit [K.Normal] in
theorem Sp48Setup.A_mul (S : Sp48Setup e T y) {s s' : Sp8} (hs' : s' ∈ spE) (j j' : ℕ) :
    (emb e s * y ^ j) * (emb e s' * y ^ j') = emb e (s * s') * y ^ (j + j') := by
  have := S.y_pow_comm_E hs' j
  rw [map_mul, pow_add]
  calc emb e s * y ^ j * (emb e s' * y ^ j') = emb e s * (y ^ j * emb e s') * y ^ j' := by group
    _ = emb e s * (emb e s' * y ^ j) * y ^ j' := by rw [this]
    _ = _ := by group

omit [K.Normal] in
theorem Sp48Setup.A_pow_three (S : Sp48Setup e T y) {s : Sp8} (hs : s ∈ spE) (j : ℕ) :
    (emb e s * y ^ j) ^ 3 = 1 := by
  have hc : Commute (emb e s) (y ^ j) := (S.y_pow_comm_E hs j).symm
  rw [hc.mul_pow, ← map_pow, ((mem_spE_iff_cube s).1 hs).2, map_one, ← pow_mul,
    mul_comm, pow_mul, S.cube, one_pow, one_mul]

omit [K.Normal] in
theorem Sp48Setup.exists_A0 (S : Sp48Setup e T y) :
    ∃ A₀ : Subgroup Y, ∀ a, a ∈ A₀ ↔ ∃ s ∈ spE, ∃ j : ℕ, a = emb e s * y ^ j := by
  refine ⟨{ carrier := {a | ∃ s ∈ spE, ∃ j : ℕ, a = emb e s * y ^ j}
            one_mem' := ⟨1, spE.one_mem, 0, by simp⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun a => Iff.rfl⟩
  · rintro a b ⟨s, hs, j, rfl⟩ ⟨s', hs', j', rfl⟩
    exact ⟨s * s', spE.mul_mem hs hs', j + j', S.A_mul hs' j j'⟩
  · rintro a ⟨s, hs, j, rfl⟩
    refine ⟨s⁻¹, spE.inv_mem hs, 2 * j, ?_⟩
    have h1 : (y ^ j)⁻¹ = y ^ (2 * j) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, S.cube, one_pow]
    have hc := S.y_pow_comm_E (spE.inv_mem hs) (2 * j)
    rw [map_inv] at hc ⊢
    rw [mul_inv_rev, h1, hc]

omit [K.Normal] in
theorem Sp48Setup.card_of_mem_iff (S : Sp48Setup e T y) {E' : Subgroup Sp8} {A : Subgroup Y}
    (hA : ∀ a, a ∈ A ↔ ∃ s ∈ E', ∃ j : ℕ, a = emb e s * y ^ j) :
    Nat.card A = Nat.card E' * 3 := by
  let f : E' × Fin 3 → A := fun p =>
    ⟨emb e p.1 * y ^ (p.2 : ℕ), (hA _).2 ⟨p.1, p.1.2, p.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨k, j⟩ ⟨k', j'⟩ h
      have h' : emb e k * y ^ (j : ℕ) = emb e k' * y ^ (j' : ℕ) := congrArg Subtype.val h
      have hK : y ^ ((j : ℕ) + 2 * (j' : ℕ)) ∈ K := by
        have h1 : (y ^ (j' : ℕ))⁻¹ = y ^ (2 * (j' : ℕ)) := by
          apply inv_eq_of_mul_eq_one_right
          rw [← pow_add, show (j' : ℕ) + 2 * (j' : ℕ) = 3 * (j' : ℕ) by ring, pow_mul, S.cube,
            one_pow]
        have : y ^ ((j : ℕ) + 2 * (j' : ℕ)) = (emb e k)⁻¹ * emb e k' := by
          rw [pow_add, ← h1]
          calc y ^ (j : ℕ) * (y ^ (j' : ℕ))⁻¹ =
              (emb e k)⁻¹ * (emb e k * y ^ (j : ℕ)) * (y ^ (j' : ℕ))⁻¹ := by group
            _ = (emb e k)⁻¹ * emb e k' := by rw [h']; group
        rw [this]
        exact K.mul_mem (K.inv_mem (emb_mem e k)) (emb_mem e k')
      have hdvd := (y_pow_mem_iff S.cube S.not_mem _).1 hK
      have hj : (j : ℕ) = j' := by
        have := j.2
        have := j'.2
        omega
      have hjj : j = j' := Fin.ext hj
      subst hjj
      have : emb e k = emb e k' := mul_right_cancel h'
      exact Prod.ext (Subtype.ext (emb_injective e this)) rfl
    · rintro ⟨t, ht⟩
      obtain ⟨k, hk, j, rfl⟩ := (hA t).1 ht
      refine ⟨(⟨k, hk⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      apply Subtype.ext
      show emb e k * y ^ (j % 3) = emb e k * y ^ j
      rw [y_pow_eq S.cube j]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

omit [K.Normal] in
theorem Sp48Setup.conj_formula (S : Sp48Setup e T y) {k s : Sp8} (j : ℕ) :
    emb e k * (emb e s * y ^ j) * (emb e k)⁻¹ = emb e (k * s * ((fr ^ j) k)⁻¹) * y ^ j := by
  have h := S.y_pow_act j k⁻¹
  rw [map_inv] at h
  have h2 : y ^ j * (emb e k)⁻¹ * (y ^ j)⁻¹ = emb e (((fr ^ j) k)⁻¹) := by
    rw [h, map_inv]
  calc emb e k * (emb e s * y ^ j) * (emb e k)⁻¹ =
        emb e k * emb e s * (y ^ j * (emb e k)⁻¹ * (y ^ j)⁻¹) * y ^ j := by group
    _ = emb e k * emb e s * emb e (((fr ^ j) k)⁻¹) * y ^ j := by rw [h2]
    _ = _ := by simp only [map_mul]

omit [K.Normal] in
theorem Sp48Setup.mem_E_of_conj_mem (S : Sp48Setup e T y) {k s : Sp8} (hk : k ∈ spT0)
    (hs : s ∈ spE) {j : ℕ} (hj : ¬ 3 ∣ j)
    (h : emb e k * (emb e s * y ^ j) * (emb e k)⁻¹ ∈ Subgroup.zpowers (emb e s * y ^ j)) :
    k ∈ spE := by
  have hcomm := S.y_pow_comm_E hs j
  have ha3 : (emb e s * y ^ j) ^ 3 = 1 := S.A_pow_three hs j
  have hyK : ∀ X : Sp8, emb e X * y ^ j = 1 → False := fun X hX => by
    have : y ^ j ∈ K := by
      have h1 : y ^ j = (emb e X)⁻¹ := by
        calc y ^ j = (emb e X)⁻¹ * (emb e X * y ^ j) := by group
          _ = (emb e X)⁻¹ := by rw [hX, mul_one]
      rw [h1]
      exact K.inv_mem (emb_mem e X)
    exact hj ((y_pow_mem_iff S.cube S.not_mem j).1 this)
  rw [S.conj_formula j] at h
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
  obtain ⟨r, hr3, hnr⟩ : ∃ r : ℕ, r < 3 ∧ (emb e s * y ^ j) ^ n = (emb e s * y ^ j) ^ r := by
    refine ⟨(n % 3).toNat, by omega, ?_⟩
    conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
    rw [zpow_add, zpow_mul]
    have h3 : (emb e s * y ^ j) ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
    rw [h3, one_zpow, mul_one, ← zpow_natCast (emb e s * y ^ j) (n % 3).toNat,
      Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num))]
  rw [hnr] at hn
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
  · exact (hyK _ (by rw [← hn]; simp)).elim
  ·
    have hX : emb e (k * s * ((fr ^ j) k)⁻¹) = emb e s := by
      rw [pow_one] at hn
      exact mul_right_cancel hn.symm
    have hX' : k * s * ((fr ^ j) k)⁻¹ = s := emb_injective e hX
    have hfrk : (fr ^ j) k ∈ spT0 := fr_pow_mem_spT0 j hk
    have hss : s ∈ spT0 := spE_le_spT0 hs
    have hkeq : (fr ^ j) k = k := by
      have h1 : k * ((fr ^ j) k)⁻¹ * s = s := by
        calc k * ((fr ^ j) k)⁻¹ * s = k * (((fr ^ j) k)⁻¹ * s) := by group
          _ = k * (s * ((fr ^ j) k)⁻¹) := by
              rw [show ((fr ^ j) k)⁻¹ * s = s * ((fr ^ j) k)⁻¹ from
                (comm_spT0 _ (spT0.inv_mem hfrk) _ hss)]
          _ = k * s * ((fr ^ j) k)⁻¹ := by group
          _ = s := hX'
      have h2 : k * ((fr ^ j) k)⁻¹ = 1 := by
        calc k * ((fr ^ j) k)⁻¹ = k * ((fr ^ j) k)⁻¹ * s * s⁻¹ := by group
          _ = 1 := by rw [h1]; group
      exact (mul_inv_eq_one.1 h2).symm
    by_contra hkE
    have hk3 : k ^ 3 ≠ 1 := fun h3 => hkE ((mem_spE_iff_cube k).2 ⟨hk, h3⟩)
    have hmod : (fr ^ j) k = (fr ^ (j % 3)) k := by rw [pow_eq_pow_mod j fr_pow_three]
    have hj3 : j % 3 = 1 ∨ j % 3 = 2 := by omega
    exact fr_pow_ne hj3 hk hk3 (hmod ▸ hkeq)
  ·
    exfalso
    have ha2 : (emb e s * y ^ j) ^ 2 = emb e (s * s) * y ^ (j + j) := by
      have hc : Commute (emb e s) (y ^ j) := hcomm.symm
      rw [pow_two, map_mul, pow_add]
      calc emb e s * y ^ j * (emb e s * y ^ j) = emb e s * (y ^ j * emb e s) * y ^ j := by group
        _ = emb e s * (emb e s * y ^ j) * y ^ j := by rw [hcomm]
        _ = _ := by group
    rw [ha2] at hn
    have hy2 : y ^ j ∈ K := by
      have h1 : emb e (s * s) * y ^ (j + j) = emb e (k * s * ((fr ^ j) k)⁻¹) * y ^ j := hn
      have hX : emb e (k * s * ((fr ^ j) k)⁻¹) = emb e (s * s) * y ^ j := by
        calc emb e (k * s * ((fr ^ j) k)⁻¹) =
              (emb e (k * s * ((fr ^ j) k)⁻¹) * y ^ j) * (y ^ j)⁻¹ := by group
          _ = (emb e (s * s) * y ^ (j + j)) * (y ^ j)⁻¹ := by rw [← h1]
          _ = emb e (s * s) * y ^ j := by rw [pow_add]; group
      have h2 : y ^ j = (emb e (s * s))⁻¹ * emb e (k * s * ((fr ^ j) k)⁻¹) := by
        rw [hX]
        group
      rw [h2]
      exact K.mul_mem (K.inv_mem (emb_mem e _)) (emb_mem e _)
    exact hj ((y_pow_mem_iff S.cube S.not_mem j).1 hy2)

end A

@[expose] noncomputable def kk (p : Fin 2 × Fin 2) : Sp8 :=
  blk0 (slA ^ (p.1 : ℕ)) * blk1 (slA ^ (p.2 : ℕ))

theorem kk_mem_spT0 (p : Fin 2 × Fin 2) : kk p ∈ spT0 :=
  (mem_spT0_iff _).2 ⟨slA ^ (p.1 : ℕ), slT.pow_mem (Subgroup.mem_zpowers slA) _, slA ^ (p.2 : ℕ),
    slT.pow_mem (Subgroup.mem_zpowers slA) _, rfl⟩

theorem blk_cube_of_mem_spE {x y : Sl28} (h : blk0 x * blk1 y ∈ spE) : x ^ 3 = 1 ∧ y ^ 3 = 1 := by
  have h3 := ((mem_spE_iff_cube _).1 h).2
  have : (blk0 x * blk1 y) ^ 3 = blk0 (x ^ 3) * blk1 (y ^ 3) := by
    have e1 : (blk0 x * blk1 y) ^ 3 = blkHom (x, y) ^ 3 := rfl
    rw [e1, ← map_pow, Prod.pow_mk]
    rfl
  rw [this] at h3
  have h4 : blk0 (x ^ 3) * blk1 (y ^ 3) = blk0 1 * blk1 1 := by rw [h3]; simp
  exact blk_inj h4

theorem kk_quot_not_mem {p q : Fin 2 × Fin 2} (h : p ≠ q) : (kk p)⁻¹ * kk q ∉ spE := by
  intro hmem
  have e1 : (kk p)⁻¹ * kk q = blk0 ((slA ^ (p.1 : ℕ))⁻¹ * slA ^ (q.1 : ℕ)) *
      blk1 ((slA ^ (p.2 : ℕ))⁻¹ * slA ^ (q.2 : ℕ)) := by
    rw [kk, kk, blk_inv, blk_mul]
  rw [e1] at hmem
  have key : ∀ p q : Fin 2 × Fin 2, p ≠ q → ¬ (((slA ^ (p.1 : ℕ))⁻¹ * slA ^ (q.1 : ℕ)) ^ 3 = 1 ∧
      ((slA ^ (p.2 : ℕ))⁻¹ * slA ^ (q.2 : ℕ)) ^ 3 = 1) := by decide +kernel
  exact key p q h (blk_cube_of_mem_spE hmem)

section B

variable {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal] {e : K ≃* Sp8} {T : Subgroup Y} {y : Y}

omit [K.Normal] in
theorem Sp48Setup.orbit_nine_aux (S : Sp48Setup e T y) {A₀ : Subgroup Y}
    (hA : ∀ a, a ∈ A₀ ↔ ∃ s ∈ spE, ∃ j : ℕ, a = emb e s * y ^ j) {a : Y} (ha : a ∈ A₀)
    (haZ : a ∉ centerOf T) (W : Fin 3 → Subgroup Y) :
    ∃ u ∈ T ⊓ K, ∀ i, (Subgroup.zpowers a).map (MulAut.conj u).toMonoidHom ≠ W i := by
  obtain ⟨s, hs, j, rfl⟩ := (hA a).1 ha
  have hj : ¬ 3 ∣ j := by
    intro hdvd
    apply haZ
    have : y ^ j = 1 := by rw [y_pow_eq S.cube, Nat.mod_eq_zero_of_dvd hdvd, pow_zero]
    rw [this, mul_one, S.center_T]
    exact ⟨s, hs, rfl⟩
  by_contra hcon
  push Not at hcon
  have hu : ∀ p, emb e (kk p) ∈ T ⊓ K := fun p =>
    ⟨S.emb_mem_T (kk_mem_spT0 p), emb_mem e _⟩
  choose g hg using fun p => hcon (emb e (kk p)) (hu p)
  obtain ⟨p, q, hpq, hgpq⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by simp)
  have heq : (Subgroup.zpowers (emb e s * y ^ j)).map (MulAut.conj (emb e (kk p))).toMonoidHom =
      (Subgroup.zpowers (emb e s * y ^ j)).map (MulAut.conj (emb e (kk q))).toMonoidHom := by
    rw [hg p, hg q, hgpq]
  have hmem : emb e (kk q) * (emb e s * y ^ j) * (emb e (kk q))⁻¹ ∈
      (Subgroup.zpowers (emb e s * y ^ j)).map (MulAut.conj (emb e (kk q))).toMonoidHom :=
    ⟨emb e s * y ^ j, Subgroup.mem_zpowers _, rfl⟩
  rw [← heq] at hmem
  obtain ⟨b, hb, hbq⟩ := hmem
  have hbq' : emb e (kk p) * b * (emb e (kk p))⁻¹ =
      emb e (kk q) * (emb e s * y ^ j) * (emb e (kk q))⁻¹ := hbq
  have hconj : emb e ((kk p)⁻¹ * kk q) * (emb e s * y ^ j) * (emb e ((kk p)⁻¹ * kk q))⁻¹ = b := by
    have : b = (emb e (kk p))⁻¹ * (emb e (kk q) * (emb e s * y ^ j) * (emb e (kk q))⁻¹) *
        emb e (kk p) := by
      rw [← hbq']
      group
    rw [this, map_mul, map_inv]
    group
  have hmem2 : emb e ((kk p)⁻¹ * kk q) * (emb e s * y ^ j) * (emb e ((kk p)⁻¹ * kk q))⁻¹ ∈
      Subgroup.zpowers (emb e s * y ^ j) := hconj ▸ hb
  have hk0 : (kk p)⁻¹ * kk q ∈ spT0 :=
    spT0.mul_mem (spT0.inv_mem (kk_mem_spT0 p)) (kk_mem_spT0 q)
  exact kk_quot_not_mem hpq (S.mem_E_of_conj_mem hk0 hs hj hmem2)

omit [K.Normal] in
theorem Sp48Setup.A_comm (S : Sp48Setup e T y) {s s' : Sp8} (hs : s ∈ spE) (hs' : s' ∈ spE)
    (j j' : ℕ) :
    (emb e s * y ^ j) * (emb e s' * y ^ j') = (emb e s' * y ^ j') * (emb e s * y ^ j) := by
  rw [S.A_mul hs' j j', S.A_mul hs j' j, comm_spT0 _ (spE_le_spT0 hs) _ (spE_le_spT0 hs'),
    add_comm]

omit [K.Normal] in
theorem blk1_slA_mem : blk1 slA ∈ spT0 :=
  (mem_spT0_iff _).2 ⟨1, slT.one_mem, slA, Subgroup.mem_zpowers slA, by simp⟩

omit [K.Normal] in
theorem Sp48Setup.homocyclic_aux (S : Sp48Setup e T y) :
    ∃ u v : Y, u ∈ T ⊓ K ∧ v ∈ T ⊓ K ∧ orderOf u = 9 ∧ orderOf v = 9 ∧ u * v = v * u ∧
      Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥ := by
  refine ⟨emb e (blk0 slA), emb e (blk1 slA), ⟨S.emb_mem_T blk0_slA_mem, emb_mem e _⟩,
    ⟨S.emb_mem_T blk1_slA_mem, emb_mem e _⟩, ?_, ?_, ?_, ?_⟩
  · rw [orderOf_injective (emb e) (emb_injective e), orderOf_injective blk0 blk0_injective,
      orderOf_slA]
  · rw [orderOf_injective (emb e) (emb_injective e), orderOf_injective blk1 blk1_injective,
      orderOf_slA]
  · rw [← map_mul, ← map_mul, (blk_commute _ _).eq]
  · rw [eq_bot_iff]
    rintro t ⟨ht1, ht2⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 ht2
    rw [Subgroup.mem_bot]
    have h1 : emb e (blk0 (slA ^ m)) = emb e (blk1 (slA ^ n)) := by
      rw [map_zpow, map_zpow, map_zpow, map_zpow]
      exact hn.symm
    have h2 := emb_injective e h1
    have h3 : blk0 (slA ^ m) * blk1 1 = blk0 1 * blk1 (slA ^ n) := by simpa using h2
    have h4 := (blk_inj h3).1
    rw [← map_zpow, ← map_zpow, h4]
    simp

section C

variable {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal] {e : K ≃* Sp8}
  {T : Subgroup Y} {y : Y} {Y₀ : Subgroup Y}

omit [K.Normal] in
theorem Sp48Setup.normalizer_E_le (S : Sp48Setup e T y) (h3 : 3 ≤ Open.pRank 3 T)
    (hW : GLBWeakCore 3 T ≤ Y₀) :
    Subgroup.normalizer ((spE.map (emb e) : Subgroup Y) : Set Y) ≤ Y₀ := by
  have hEel : IsElemAbelian 3 spE := by
    refine ⟨IsMulCommutative.of_comm ?_, fun x hx => ((mem_spE_iff_cube x).1 hx).2⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact Subtype.ext (comm_spT0 a (spE_le_spT0 ha) b (spE_le_spT0 hb))
  have hcardE : Nat.card (centerOf T) = 3 ^ 2 := by
    rw [S.center_T, Subgroup.card_map_of_injective (emb_injective e), card_spE]
    norm_num
  have hQN : Subgroup.normalizer (centerOf T : Set Y) ≤ GLBWeakCore 3 T := by
    refine normalizer_le_weakCore 3 inf_le_left ?_ ?_
    · rw [S.center_T]
      exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hEel (emb e)) (k := 2)
        (by rw [← S.center_T]; exact hcardE)
    · refine h3.trans (pRank_mono 3 Nat.prime_three ?_)
      intro x hx
      refine Subgroup.mem_sup_right ⟨hx, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 hq.2 x hx).symm
  rw [← S.center_T]
  exact hQN.trans hW

end C

end B

end KFactProofs.Sp48

theorem kFactSp48NonsolvLocal : KFactSp48NonsolvLocal := by
  intro Y _ _ K d hd hKn he hC T Y₀ h3 hW hY₀ hns
  obtain ⟨e⟩ := he
  obtain ⟨⟨eK⟩, hcardK⟩ := exists_equiv_sp8 hd e
  have hcardS : Nat.card Sp8 = 3 ^ 4 * 13045760 := by
    rw [← hcardK]
    exact Nat.card_congr eK.symm.toEquiv
  have hsimple : IsSimpleGroup Sp8 := isSimple_sp8_of_index hd e eK
  have : K.Normal := hKn
  obtain ⟨e', y, S⟩ := exists_setup K eK hC hcardS T h3
  have hNE := S.normalizer_E_le h3 hW
  obtain ⟨θ, ψ, hθT, hθz, hψ, hcl⟩ := nonsolv_classify S hC hcardS hsimple hNE hY₀ hns
  have hTY : (T : Subgroup Y) ≤ Y₀ := S.T_le_Y₀ hNE
  obtain ⟨A₀, hA⟩ := S.exists_A0
  refine ⟨A₀, Vzero e' ψ, ?_⟩
  refine
  { card_T := S.card_T
    center_pow := fun z hz => by
      rw [S.center_T] at hz
      obtain ⟨s, hs, rfl⟩ := hz
      rw [← map_pow, ((mem_spE_iff_cube s).1 hs).2, map_one]
    card_center := by
      rw [S.center_T, Subgroup.card_map_of_injective (emb_injective e'), card_spE]
      norm_num
    card_TK := S.card_inf_K
    A_le := fun a ha => by
      obtain ⟨s, hs, j, rfl⟩ := (hA a).1 ha
      exact (S.mem_iff _).2 ⟨s, spE_le_spT0 hs, j, rfl⟩
    A_pow := fun a ha => by
      obtain ⟨s, hs, j, rfl⟩ := (hA a).1 ha
      exact S.A_pow_three hs j
    A_comm := fun a ha b hb => by
      obtain ⟨s, hs, j, rfl⟩ := (hA a).1 ha
      obtain ⟨s', hs', j', rfl⟩ := (hA b).1 hb
      exact S.A_comm hs hs' j j'
    card_A := by
      rw [S.card_of_mem_iff hA, card_spE]
      norm_num
    center_le_A := fun z hz => by
      rw [S.center_T] at hz
      obtain ⟨s, hs, rfl⟩ := hz
      exact (hA _).2 ⟨s, hs, 0, by simp⟩
    homocyclic := S.homocyclic_aux
    orbit_nine := fun a ha haZ W => S.orbit_nine_aux hA ha haZ W
    V_le := Vzero_le_Y₀ hcl
    V_le_K := Vzero_le_K
    V_perfect := Vzero_perfect
    V_normal := fun g hg => Vzero_mem_normalizer hcl hg
    TK_le_V := S.TK_le_Vzero hψ
    minimal := fun W hWY hn => S.minimal_V hC hNE hcl hWY hn
    V_centralizer := S.V_centralizer hC hψ
    sylow_normal := fun W _ _ hVW => S.sylow_normal_V hψ hVW
    factors := ⟨Vone e' ψ, Vtwo e' ψ, Vzero_eq_sup.symm, commutator_Vone_Vtwo, Vone_perfect,
      Vtwo_perfect, Vone_caseTwo, Vtwo_caseTwo, S.T_le_normalizer_Vone hcl hψ hTY,
      S.T_le_normalizer_Vtwo hcl hψ hTY, fpsi e' ψ swp, fpsi_mem_Y₀ hcl swp_mem_wrp_top,
      Vone_conj_swap, Vtwo_conj_swap⟩ }

end CFSG.AGLEmbedding

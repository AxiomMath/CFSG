module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Frob
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups Matrix

section Emb

variable {Y : Type} [Group Y] {K : Subgroup Y}

@[expose] def emb (e : K ≃* Sp8) : Sp8 →* Y := K.subtype.comp e.symm.toMonoidHom

theorem emb_apply (e : K ≃* Sp8) (k : Sp8) : emb e k = ((e.symm k : K) : Y) := rfl

theorem emb_injective (e : K ≃* Sp8) : Function.Injective (emb e) := fun _ _ h =>
  e.symm.injective (Subtype.val_injective h)

theorem emb_mem (e : K ≃* Sp8) (k : Sp8) : emb e k ∈ K := (e.symm k).2

theorem exists_emb (e : K ≃* Sp8) {t : Y} (ht : t ∈ K) : ∃ k, emb e k = t :=
  ⟨e ⟨t, ht⟩, by simp [emb_apply]⟩

structure Sp48Setup (e : K ≃* Sp8) (T : Subgroup Y) (y : Y) : Prop where
  cube : y ^ 3 = 1
  act : ∀ k : Sp8, y * emb e k * y⁻¹ = emb e (fr k)
  not_mem : y ∉ K
  mem_iff : ∀ t : Y, t ∈ T ↔ ∃ k ∈ spT0, ∃ j : ℕ, t = emb e k * y ^ j

theorem pow_act {e : K ≃* Sp8} {y : Y} (hact : ∀ k : Sp8, y * emb e k * y⁻¹ = emb e (fr k))
    (j : ℕ) (k : Sp8) : y ^ j * emb e k * (y ^ j)⁻¹ = emb e ((fr ^ j) k) := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_succ', MulAut.mul_apply]
    calc y * y ^ j * emb e k * (y * y ^ j)⁻¹ = y * (y ^ j * emb e k * (y ^ j)⁻¹) * y⁻¹ := by group
      _ = emb e (fr ((fr ^ j) k)) := by rw [ih, hact]

theorem y_pow_eq {y : Y} (hy : y ^ 3 = 1) (j : ℕ) : y ^ j = y ^ (j % 3) :=
  pow_eq_pow_mod j hy

theorem y_pow_mem_iff {y : Y} (hy : y ^ 3 = 1) (hyK : y ∉ K) (j : ℕ) : y ^ j ∈ K ↔ 3 ∣ j := by
  rw [y_pow_eq hy j]
  have h3 : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hy4 : y ^ 4 = y := by
    calc y ^ 4 = y ^ 3 * y := by group
      _ = y := by rw [hy]; group
  constructor
  · intro h
    by_contra hdvd
    have : j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases this with h1 | h1
    · rw [h1, pow_one] at h
      exact hyK h
    · rw [h1] at h
      apply hyK
      rw [← hy4, show 4 = 2 * 2 by norm_num, pow_mul]
      exact K.pow_mem h 2
  · intro h
    rw [Nat.mod_eq_zero_of_dvd h, pow_zero]
    exact K.one_mem

theorem exists_tSub (e : K ≃* Sp8) (y : Y) (hcube : y ^ 3 = 1)
    (hact : ∀ k : Sp8, y * emb e k * y⁻¹ = emb e (fr k)) (hnot : y ∉ K) :
    ∃ T : Subgroup Y, Sp48Setup e T y := by
  let T : Subgroup Y :=
    { carrier := {t | ∃ k ∈ spT0, ∃ j : ℕ, t = emb e k * y ^ j}
      one_mem' := ⟨1, spT0.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨k, hk, j, rfl⟩ ⟨k', hk', j', rfl⟩
        refine ⟨k * (fr ^ j) k', spT0.mul_mem hk (fr_pow_mem_spT0 j hk'), j + j', ?_⟩
        have := pow_act hact j k'
        rw [map_mul, ← this, pow_add]
        group
      inv_mem' := by
        rintro a ⟨k, hk, j, rfl⟩
        refine ⟨(fr ^ (2 * j)) k⁻¹, ?_, 2 * j, ?_⟩
        · rw [map_inv]
          exact spT0.inv_mem (fr_pow_mem_spT0 _ hk)
        · have h1 : (y ^ j)⁻¹ = y ^ (2 * j) := by
            apply inv_eq_of_mul_eq_one_right
            rw [← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hcube, one_pow]
          have := pow_act hact (2 * j) k⁻¹
          calc (emb e k * y ^ j)⁻¹ = (y ^ j)⁻¹ * (emb e k)⁻¹ := mul_inv_rev _ _
            _ = y ^ (2 * j) * (emb e k)⁻¹ := by rw [h1]
            _ = (y ^ (2 * j) * emb e k⁻¹ * (y ^ (2 * j))⁻¹) * y ^ (2 * j) := by
                rw [map_inv]; group
            _ = emb e ((fr ^ (2 * j)) k⁻¹) * y ^ (2 * j) := by rw [this] }
  exact ⟨T, hcube, hact, hnot, fun t => Iff.rfl⟩

end Emb

section Conj

variable {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal]

@[expose] def econj (e : K ≃* Sp8) (g : Y) : K ≃* Sp8 :=
  (e.symm.trans (MulAut.conjNormal g)).symm

theorem emb_econj (e : K ≃* Sp8) (g : Y) (k : Sp8) :
    emb (econj e g) k = g * emb e k * g⁻¹ := by
  show (((econj e g).symm k : K) : Y) = _
  simp [econj, MulAut.conjNormal_apply, emb_apply]

theorem Sp48Setup.conj {e : K ≃* Sp8} {T : Subgroup Y} {y : Y} (S : Sp48Setup e T y) (g : Y) :
    Sp48Setup (econj e g) (T.map (MulAut.conj g).toMonoidHom) (g * y * g⁻¹) where
  cube := by
    rw [conj_pow, S.cube]
    group
  act k := by
    rw [emb_econj, emb_econj]
    calc g * y * g⁻¹ * (g * emb e k * g⁻¹) * (g * y * g⁻¹)⁻¹ =
          g * (y * emb e k * y⁻¹) * g⁻¹ := by group
      _ = g * emb e (fr k) * g⁻¹ := by rw [S.act]
  not_mem h := S.not_mem (by
    have := Subgroup.Normal.conj_mem (inferInstance : K.Normal) _ h g⁻¹
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at this)
  mem_iff t := by
    constructor
    · rintro ⟨t', ht', rfl⟩
      obtain ⟨k, hk, j, rfl⟩ := (S.mem_iff t').1 ht'
      refine ⟨k, hk, j, ?_⟩
      rw [emb_econj, conj_pow]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul]
    · rintro ⟨k, hk, j, rfl⟩
      refine ⟨emb e k * y ^ j, (S.mem_iff _).2 ⟨k, hk, j, rfl⟩, ?_⟩
      rw [emb_econj, conj_pow]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul]

end Conj

section Facts

variable {Y : Type} [Group Y] {K : Subgroup Y} {e : K ≃* Sp8} {T : Subgroup Y} {y : Y}

namespace Sp48Setup

theorem emb_mem_T (S : Sp48Setup e T y) {k : Sp8} (hk : k ∈ spT0) : emb e k ∈ T :=
  (S.mem_iff _).2 ⟨k, hk, 0, by simp⟩

theorem y_mem (S : Sp48Setup e T y) : y ∈ T :=
  (S.mem_iff _).2 ⟨1, spT0.one_mem, 1, by simp⟩

theorem y_pow_act (S : Sp48Setup e T y) (j : ℕ) (k : Sp8) :
    y ^ j * emb e k * (y ^ j)⁻¹ = emb e ((fr ^ j) k) := pow_act S.act j k

theorem inf_K (S : Sp48Setup e T y) {t : Y} (ht : t ∈ T) (htK : t ∈ K) :
    ∃ k ∈ spT0, t = emb e k := by
  obtain ⟨k, hk, j, rfl⟩ := (S.mem_iff t).1 ht
  have h1 : y ^ j ∈ K := by
    have := K.mul_mem (K.inv_mem (emb_mem e k)) htK
    simpa using this
  have h2 : y ^ j = 1 := by
    rw [y_pow_eq S.cube, Nat.mod_eq_zero_of_dvd ((y_pow_mem_iff S.cube S.not_mem j).1 h1), pow_zero]
  exact ⟨k, hk, by rw [h2, mul_one]⟩

theorem card_T (S : Sp48Setup e T y) : Nat.card T = 3 ^ 5 := by
  let f : spT0 × Fin 3 → T := fun p =>
    ⟨emb e p.1 * y ^ (p.2 : ℕ), (S.mem_iff _).2 ⟨p.1, p.1.2, p.2, rfl⟩⟩
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
      obtain ⟨k, hk, j, rfl⟩ := (S.mem_iff t).1 ht
      refine ⟨(⟨k, hk⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      apply Subtype.ext
      show emb e k * y ^ (j % 3) = emb e k * y ^ j
      rw [y_pow_eq S.cube j]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, card_spT0,
    Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
  norm_num

theorem blk0_slA_mem : blk0 slA ∈ spT0 :=
  (mem_spT0_iff _).2 ⟨slA, Subgroup.mem_zpowers slA, 1, slT.one_mem, by simp⟩

theorem blk0_slA_cube : (blk0 slA) ^ 3 ≠ 1 := by
  intro h
  rw [← map_pow] at h
  have := longBlock_injective (K := GF8) (n := 2) 0 (h.trans (map_one _).symm)
  exact slA_pow3 this

theorem cent_T0 (S : Sp48Setup e T y) {t : Y} (ht : t ∈ T)
    (hc : ∀ s ∈ spT0, t * emb e s = emb e s * t) : ∃ k ∈ spT0, t = emb e k := by
  obtain ⟨k, hk, j, rfl⟩ := (S.mem_iff t).1 ht
  have h3 : 3 ∣ j := by
    by_contra hj
    have hc' := hc _ blk0_slA_mem
    have hkc : emb e k * emb e (blk0 slA) = emb e (blk0 slA) * emb e k := by
      rw [← map_mul, ← map_mul, comm_spT0 _ hk _ blk0_slA_mem]
    have h1 : y ^ j * emb e (blk0 slA) * (y ^ j)⁻¹ = emb e (blk0 slA) := by
      have : emb e k * (emb e (blk0 slA) * y ^ j) = emb e k * (y ^ j * emb e (blk0 slA)) := by
        calc emb e k * (emb e (blk0 slA) * y ^ j) = (emb e k * emb e (blk0 slA)) * y ^ j := by
              group
          _ = (emb e (blk0 slA) * emb e k) * y ^ j := by rw [hkc]
          _ = emb e (blk0 slA) * (emb e k * y ^ j) := by group
          _ = emb e k * y ^ j * emb e (blk0 slA) := hc'.symm
          _ = emb e k * (y ^ j * emb e (blk0 slA)) := by group
      have := mul_left_cancel this
      rw [← this]
      group
    rw [S.y_pow_act j] at h1
    have h2 : (fr ^ j) (blk0 slA) = blk0 slA := emb_injective e h1
    rw [pow_eq_pow_mod j fr_pow_three] at h2
    have hmod : j % 3 = 1 ∨ j % 3 = 2 := by omega
    exact fr_pow_ne hmod blk0_slA_mem blk0_slA_cube h2
  have hy : y ^ j = 1 := by
    rw [y_pow_eq S.cube, Nat.mod_eq_zero_of_dvd h3, pow_zero]
  exact ⟨k, hk, by rw [hy, mul_one]⟩

theorem fr_pow_spE {k : Sp8} (hk : k ∈ spE) (j : ℕ) : (fr ^ j) k = k := by
  have h : fr k = k := (fr_eq_self_iff_mem_spE (spE_le_spT0 hk)).2 hk
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', MulAut.mul_apply, ih, h]

theorem center_T (S : Sp48Setup e T y) : centerOf T = spE.map (emb e) := by
  ext z
  constructor
  · rintro ⟨hzT, hzC⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 hzC
    obtain ⟨k, hk, rfl⟩ := S.cent_T0 hzT fun s hs =>
      (hcomm (emb e s) (S.emb_mem_T hs)).symm
    refine ⟨k, ?_, rfl⟩
    have hy := hcomm y S.y_mem
    have h1 : emb e (fr k) = emb e k := by
      rw [← S.act]
      calc y * emb e k * y⁻¹ = (y * emb e k) * y⁻¹ := rfl
        _ = (emb e k * y) * y⁻¹ := by rw [hy]
        _ = emb e k := by group
    exact (fr_eq_self_iff_mem_spE hk).1 (emb_injective e h1)
  · rintro ⟨k, hk, rfl⟩
    refine ⟨S.emb_mem_T (spE_le_spT0 hk), Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
    obtain ⟨k', hk', j, rfl⟩ := (S.mem_iff t).1 ht
    have h1 : y ^ j * emb e k * (y ^ j)⁻¹ = emb e k := by
      rw [S.y_pow_act, fr_pow_spE hk]
    have h2 : emb e k' * emb e k = emb e k * emb e k' := by
      rw [← map_mul, ← map_mul, comm_spT0 _ hk' _ (spE_le_spT0 hk)]
    calc emb e k' * y ^ j * emb e k = emb e k' * (y ^ j * emb e k * (y ^ j)⁻¹) * y ^ j := by group
      _ = emb e k' * emb e k * y ^ j := by rw [h1]
      _ = emb e k * (emb e k' * y ^ j) := by rw [h2]; group

theorem fr_pow_normalizer {n : Sp8} (hn : n ∈ wrp slD) (j : ℕ) : n⁻¹ * (fr ^ j) n ∈ spT0 := by
  induction j with
  | zero => simp [spT0.one_mem]
  | succ j ih =>
    have h1 := fr_normalizer hn
    rw [pow_succ', MulAut.mul_apply]
    have hs : (fr ^ j) n = n * (n⁻¹ * (fr ^ j) n) := by group
    rw [hs, map_mul]
    have e : n⁻¹ * (fr n * fr (n⁻¹ * (fr ^ j) n)) = (n⁻¹ * fr n) * fr (n⁻¹ * (fr ^ j) n) := by
      group
    rw [e]
    exact spT0.mul_mem h1 (fr_mem_spT0 ih)

theorem emb_conj_mem_T (S : Sp48Setup e T y) {n : Sp8} (hn : n ∈ wrp slD) {t : Y} (ht : t ∈ T) :
    emb e n * t * (emb e n)⁻¹ ∈ T := by
  obtain ⟨k, hk, j, rfl⟩ := (S.mem_iff t).1 ht
  have hN : n ∈ Subgroup.normalizer (spT0 : Set Sp8) := wrp_eq_normalizer ▸ hn
  have hsT : n⁻¹ * (fr ^ j) n ∈ spT0 := fr_pow_normalizer hn j
  have hfr : (fr ^ j) n = n * (n⁻¹ * (fr ^ j) n) := by group
  have hinv : (fr ^ j) n⁻¹ = (n⁻¹ * (fr ^ j) n)⁻¹ * n⁻¹ := by
    rw [map_inv]
    conv_lhs => rw [hfr]
    rw [mul_inv_rev]
  have h1 : y ^ j * emb e n⁻¹ * (y ^ j)⁻¹ = emb e ((n⁻¹ * (fr ^ j) n)⁻¹ * n⁻¹) := by
    rw [S.y_pow_act, hinv]
  refine (S.mem_iff _).2 ⟨n * (k * (n⁻¹ * (fr ^ j) n)⁻¹) * n⁻¹, ?_, j, ?_⟩
  · have hmem : k * (n⁻¹ * (fr ^ j) n)⁻¹ ∈ spT0 := spT0.mul_mem hk (spT0.inv_mem hsT)
    have := (Subgroup.mem_normalizer_iff.1 hN _).1 hmem
    exact this
  · calc emb e n * (emb e k * y ^ j) * (emb e n)⁻¹ =
          emb e n * emb e k * (y ^ j * emb e n⁻¹ * (y ^ j)⁻¹) * y ^ j := by
          rw [map_inv]; group
      _ = _ := by rw [h1]; simp only [map_mul]; group

theorem emb_mem_normalizer_T (S : Sp48Setup e T y) {n : Sp8} (hn : n ∈ wrp slD) :
    emb e n ∈ Subgroup.normalizer (T : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨fun ht => S.emb_conj_mem_T hn ht, fun ht => ?_⟩
  have hn' : n⁻¹ ∈ wrp slD := Subgroup.inv_mem _ hn
  have := S.emb_conj_mem_T hn' ht
  simpa [map_inv, mul_assoc] using this

end Sp48Setup

end Facts

end CFSG.AGLEmbedding.KFactProofs.Sp48

module

public import CFSG.LocalAnalysis.GLTheoremA.S9.L94Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4T

open CFSG.Open

@[expose] def innerAut (K : Type) [Group K] : Subgroup (MulAut K) :=
  (MulAut.conj : K →* MulAut K).range

structure D4TwoFacts (K : Type) [Group K] [Finite K] : Prop where
  rank3 : ∃ E W : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ IsPGroup 2 W ∧ W ≠ ⊥ ∧
    E ≤ Subgroup.normalizer (W : Set K)
  rank4 : ∃ E : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4
  aut_le : ∀ P : Subgroup (MulAut K), IsElemAbelian 3 P → ¬ P ≤ innerAut K → Nat.card P ≤ 3 ^ 3
  aut_norm : ∀ P S : Subgroup (MulAut K), IsElemAbelian 3 P → ¬ P ≤ innerAut K →
    Nat.card P = 3 ^ 3 → IsPGroup 2 S → S ≠ ⊥ → P ≤ Subgroup.normalizer (S : Set (MulAut K)) → False

section Core

variable {H : Type} [Group H]

@[expose] def conjAut (K : Subgroup H) (b : H) (hb : b ∈ Subgroup.normalizer (K : Set H)) : MulAut ↥K where
  toFun k := ⟨b * k * b⁻¹, (Subgroup.mem_normalizer_iff.1 hb k).1 k.2⟩
  invFun k := ⟨b⁻¹ * k * b, by simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem hb) k).1 k.2⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' k l := Subtype.ext (by simp [mul_assoc])

@[expose] def conjHom (K : Subgroup H) : ↥(Subgroup.normalizer (K : Set H)) →* MulAut ↥K where
  toFun b := conjAut K b b.2
  map_one' := by ext k; simp [conjAut]
  map_mul' a b := by ext k; simp [conjAut, mul_assoc]

end Core

section Main

variable {H : Type} [Group H] [Finite H]

theorem mem_normalizer_of_centralizes {W : Subgroup H} {s : H} (hs : ∀ w ∈ W, s * w = w * s) :
    s ∈ Subgroup.normalizer (W : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : s * h * s⁻¹ = h := by rw [hs h hh]; group
    rw [e]
    exact hh
  · intro hh
    have h1 := hs _ hh
    have e : s * h * s⁻¹ = h := by
      apply mul_left_cancel (a := s)
      calc s * (s * h * s⁻¹) = s * h * s⁻¹ * s := h1
        _ = s * h := by group
    rw [e] at hh
    exact hh

theorem card_subgroupOf_of_le {N Y : Subgroup H} (hY : Y ≤ N) :
    Nat.card (Y.subgroupOf N) = Nat.card Y :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv

theorem noTriality_core {K B : Subgroup H} (hF : D4TwoFacts ↥K)
    (hKc : ∀ k ∈ K, (∀ y ∈ K, y * k = k * y) → k = 1)
    (hB : IsElemAbelian 3 B) (hBK : B ≤ Subgroup.normalizer (K : Set H))
    (hout : ∃ b ∈ B, ∀ k ∈ K, ¬ ∀ y ∈ K, b * y * b⁻¹ = k * y * k⁻¹)
    (hcase : (∀ P : Subgroup H, IsElemAbelian 3 P → Nat.card P ≤ Nat.card B) ∨
      ((∀ P W : Subgroup H, IsElemAbelian 3 P → IsPGroup 2 W → W ≠ ⊥ →
          P ≤ Subgroup.normalizer (W : Set H) → Nat.card P ≤ Nat.card B) ∧
        ∃ T : Subgroup H, IsPGroup 2 T ∧ T ≠ ⊥ ∧ B ≤ Subgroup.normalizer (T : Set H) ∧
          T ≤ Subgroup.normalizer (K : Set H))) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup H := Subgroup.normalizer (K : Set H) with hN
  set ρ : ↥N →* MulAut ↥K := conjHom K with hρ
  set B' : Subgroup ↥N := B.subgroupOf N with hB'
  set Bh : Subgroup (MulAut ↥K) := B'.map ρ with hBh
  set Bo : Subgroup H := B ⊓ Subgroup.centralizer (K : Set H) with hBo
  have hBo_le : Bo ≤ B := inf_le_left
  have hBo_cent : ∀ s ∈ Bo, ∀ k ∈ K, s * k = k * s := fun s hs k hk =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hs).2 k hk).symm
  have hBoel : IsElemAbelian 3 Bo := isElemAbelian_mono hB hBo_le
  have hρcoe : ∀ (b : ↥N) (k : ↥K), ((ρ b k : ↥K) : H) = (b : H) * k * (b : H)⁻¹ := fun b k => rfl
  have hker : ρ.ker ⊓ B' = Bo.subgroupOf N := by
    ext b
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, hB', hBo, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, fun k hk => ?_⟩
      have h3 := congrArg (fun σ : MulAut ↥K => ((σ ⟨k, hk⟩ : ↥K) : H)) h1
      simp only [hρcoe, MulAut.one_apply] at h3
      calc k * (b : H) = (b : H) * k * (b : H)⁻¹ * (b : H) := by rw [h3]
        _ = (b : H) * k := by group
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      ext ⟨k, hk⟩
      simp only [hρcoe, MulAut.one_apply]
      have := h1 k hk
      calc (b : H) * k * (b : H)⁻¹ = (k * (b : H)) * (b : H)⁻¹ := by rw [← this]
        _ = k := by group
  have hcardB : Nat.card B = Nat.card Bo * Nat.card Bh := by
    have h1 := Subgroup.relIndex_mul_card (H := ρ.ker) (K := B')
    rw [Subgroup.relIndex_ker, hker, card_subgroupOf_of_le (hBo_le.trans hBK),
      card_subgroupOf_of_le hBK] at h1
    rw [← h1, mul_comm]
  have hB'el : IsElemAbelian 3 B' := hB.comap N.subtype_injective
  have hBhel : IsElemAbelian 3 Bh := CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map ρ hB'el
  have hBhni : ¬ Bh ≤ innerAut ↥K := by
    intro hle
    obtain ⟨b, hb, hbn⟩ := hout
    have hmem : ρ ⟨b, hBK hb⟩ ∈ Bh := Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 hb)
    obtain ⟨k, hk⟩ := hle hmem
    refine hbn k k.2 fun y hy => ?_
    have h3 := congrArg (fun σ : MulAut ↥K => ((σ ⟨y, hy⟩ : ↥K) : H)) hk
    simp only [hρcoe, MulAut.conj_apply] at h3
    exact h3.symm
  have hBh_le : Nat.card Bh ≤ 3 ^ 3 := hF.aut_le Bh hBhel hBhni
  have hbig : ∀ E : Subgroup ↥K, IsElemAbelian 3 E →
      IsElemAbelian 3 (E.map K.subtype ⊔ Bo) ∧
        Nat.card (E.map K.subtype ⊔ Bo : Subgroup H) = Nat.card E * Nat.card Bo := by
    intro E hE
    have hEel : IsElemAbelian 3 (E.map K.subtype) :=
      CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map K.subtype hE
    have hEK : ∀ e ∈ E.map K.subtype, e ∈ K := by
      rintro _ ⟨e, -, rfl⟩
      exact e.2
    refine ⟨hEel.sup_of_commute hBoel fun e he s hs => (hBo_cent s hs e (hEK e he)).symm, ?_⟩
    have hnorm : Bo ≤ Subgroup.normalizer ((E.map K.subtype : Subgroup H) : Set H) :=
      fun s hs => mem_normalizer_of_centralizes fun w hw => hBo_cent s hs w (hEK w hw)
    have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
    have hinf : (E.map K.subtype : Subgroup H) ⊓ Bo = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
      rw [Subgroup.mem_bot]
      exact hKc z (hEK z hz1) fun y hy => (hBo_cent z hz2 y hy).symm
    rw [hinf, Subgroup.card_bot, mul_one] at h1
    rw [h1, Subgroup.card_map_of_injective K.subtype_injective]
  have hBopos : 0 < Nat.card Bo := Nat.card_pos
  rcases hcase with hall | ⟨hmax, T, hT2, hTne, hBT, hTK⟩
  ·
    obtain ⟨E4, hE4el, hE4c⟩ := hF.rank4
    obtain ⟨hPel, hPc⟩ := hbig E4 hE4el
    have h1 := hall _ hPel
    rw [hPc, hE4c, hcardB] at h1
    nlinarith
  ·
    obtain ⟨E3, W, hE3el, hE3c, hW2, hWne, hE3W⟩ := hF.rank3
    have hWH2 : IsPGroup 2 (W.map K.subtype) := hW2.map K.subtype
    have hWHne : W.map K.subtype ≠ ⊥ := fun h =>
      hWne ((Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h)
    obtain ⟨hP3el, hP3c⟩ := hbig E3 hE3el
    have hP3norm : E3.map K.subtype ⊔ Bo ≤
        Subgroup.normalizer ((W.map K.subtype : Subgroup H) : Set H) := by
      refine sup_le ?_ ?_
      · intro e he
        obtain ⟨e0, he0, rfl⟩ := he
        exact Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem _ (hE3W he0))
      · intro s hs
        refine mem_normalizer_of_centralizes fun w hw => ?_
        obtain ⟨w0, -, rfl⟩ := hw
        exact hBo_cent s hs w0 w0.2
    have h27 := hmax _ _ hP3el hWH2 hWHne hP3norm
    rw [hP3c, hE3c, hcardB] at h27
    have hBh27 : Nat.card Bh = 3 ^ 3 := by
      have : 3 ^ 3 ≤ Nat.card Bh := by nlinarith
      omega
    by_cases hTc : ∀ t ∈ T, ∀ k ∈ K, t * k = k * t
    ·
      obtain ⟨E4, hE4el, hE4c⟩ := hF.rank4
      obtain ⟨hPel, hPc⟩ := hbig E4 hE4el
      have hPnorm : E4.map K.subtype ⊔ Bo ≤ Subgroup.normalizer (T : Set H) := by
        refine sup_le ?_ (hBo_le.trans hBT)
        intro e he
        obtain ⟨e0, -, rfl⟩ := he
        exact mem_normalizer_of_centralizes fun t ht => (hTc t ht e0 e0.2).symm
      have h1 := hmax _ _ hPel hT2 hTne hPnorm
      rw [hPc, hE4c, hcardB, hBh27] at h1
      nlinarith
    ·
      push Not at hTc
      obtain ⟨t, ht, k, hk, htk⟩ := hTc
      set T' : Subgroup ↥N := T.subgroupOf N with hT'
      set Th : Subgroup (MulAut ↥K) := T'.map ρ with hTh
      have hT'2 : IsPGroup 2 T' := hT2.comap_subtype
      have hTh2 : IsPGroup 2 Th := hT'2.map ρ
      have hThne : Th ≠ ⊥ := by
        intro h
        have hmem : ρ ⟨t, hTK ht⟩ ∈ Th := Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 ht)
        rw [h, Subgroup.mem_bot] at hmem
        apply htk
        have h3 := congrArg (fun σ : MulAut ↥K => ((σ ⟨k, hk⟩ : ↥K) : H)) hmem
        simp only [hρcoe, MulAut.one_apply] at h3
        calc t * k = t * k * t⁻¹ * t := by group
          _ = k * t := by rw [h3]
      have hBT' : B' ≤ Subgroup.normalizer (T' : Set ↥N) := by
        intro b hb
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h1 := Subgroup.mem_normalizer_iff.1 (hBT (Subgroup.mem_subgroupOf.1 hb)) (y : H)
        simp only [hT', Subgroup.mem_subgroupOf, SetLike.mem_coe, Subgroup.coe_mul,
          Subgroup.coe_inv] at h1 ⊢
        exact h1
      have hnorm : Bh ≤ Subgroup.normalizer (Th : Set (MulAut ↥K)) := fun σ hσ => by
        obtain ⟨b, hb, rfl⟩ := hσ
        exact Subgroup.le_normalizer_map ρ (Subgroup.mem_map_of_mem _ (hBT' hb))
      exact hF.aut_norm Bh Th hBhel hBhni hBh27 hTh2 hThne hnorm

end Main

end CFSG.LocalAnalysis.GLTheoremA.D4T

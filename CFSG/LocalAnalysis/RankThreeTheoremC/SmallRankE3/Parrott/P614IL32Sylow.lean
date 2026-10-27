module

public import CFSG.Open.FusionDefs
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_map_conj {T : Subgroup G} {g y : G} :
    y ∈ T.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ T := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨g⁻¹ * y * g, hy, by simp [mul_assoc]⟩

omit [Finite G] in
theorem fusionIsSylowIn_map_conj {p : ℕ} {T N : Subgroup G} {g : G}
    (hT : fusionIsSylowIn p T N) (hg : g ∈ normalizer (N : Set G)) :
    fusionIsSylowIn p (T.map (MulAut.conj g).toMonoidHom) N := by
  obtain ⟨hTN, hT2, hmax⟩ := hT
  have hNg : ∀ y, y ∈ N ↔ g⁻¹ * y * g ∈ N := fun y => by
    have := mem_normalizer_iff.1 (inv_mem hg) y
    simpa using this
  refine ⟨fun y hy => (hNg y).2 (hTN (mem_map_conj.1 hy)), hT2.map _, fun P hPN hP hTP => ?_⟩
  have h1 : T ≤ P.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro x hx
    rw [mem_map_conj, inv_inv]
    exact hTP (mem_map_conj.2 (by simpa [mul_assoc] using hx))
  have h2 : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ N := by
    intro y hy
    rw [mem_map_conj, inv_inv] at hy
    have := (hNg (g * y * g⁻¹)).1 (hPN hy)
    simpa [mul_assoc] using this
  have h3 := hmax _ h2 (hP.map _) h1
  ext y
  rw [mem_map_conj]
  constructor
  · intro hy
    rw [← h3, mem_map_conj, inv_inv]
    simpa [mul_assoc] using hy
  · intro hy
    rw [← h3, mem_map_conj, inv_inv] at hy
    simpa [mul_assoc] using hy

omit [Finite G] in
theorem le_normalizer_map_conj {B T : Subgroup G} {g : G} (hgB : g ∈ normalizer (B : Set G))
    (hBT : B ≤ normalizer (T : Set G)) :
    B ≤ normalizer ((T.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro β hβ
  have hβ' : g⁻¹ * β * g ∈ B := by
    have := (mem_normalizer_iff.1 (inv_mem hgB) β).1 hβ
    simpa using this
  rw [mem_normalizer_iff]
  intro y
  simp only [SetLike.mem_coe, mem_map_conj]
  have key := mem_normalizer_iff.1 (hBT hβ') (g⁻¹ * y * g)
  have e : g⁻¹ * β * g * (g⁻¹ * y * g) * (g⁻¹ * β * g)⁻¹ = g⁻¹ * (β * y * β⁻¹) * g := by group
  rw [e] at key
  exact key

omit [Finite G] in
theorem map_conj_eq_iff {T : Subgroup G} {g g' : G} :
    T.map (MulAut.conj g).toMonoidHom = T.map (MulAut.conj g').toMonoidHom ↔
      g⁻¹ * g' ∈ normalizer (T : Set G) := by
  constructor
  · intro h
    refine inv_mem_iff.1 ?_
    rw [mem_normalizer_iff]
    intro x
    have h1 : g * x * g⁻¹ ∈ T.map (MulAut.conj g).toMonoidHom ↔ x ∈ T := by
      rw [mem_map_conj]
      simp [mul_assoc]
    rw [h, mem_map_conj] at h1
    rw [← h1]
    have e : g'⁻¹ * (g * x * g⁻¹) * g' = (g⁻¹ * g')⁻¹ * x * (g⁻¹ * g')⁻¹⁻¹ := by group
    rw [e]
  · intro h
    ext y
    rw [mem_map_conj, mem_map_conj]
    have key := mem_normalizer_iff.1 (inv_mem h) (g⁻¹ * y * g)
    have e : (g⁻¹ * g')⁻¹ * (g⁻¹ * y * g) * (g⁻¹ * g')⁻¹⁻¹ = g'⁻¹ * y * g' := by group
    rw [e] at key
    exact key

theorem exists_sylow_two_invariant {N₀ B : Subgroup G} {t : G} {n : ℕ} (hB : IsPGroup 3 B)
    (hN₀ : ¬ 3 ∣ Nat.card N₀) (hBN : B ≤ normalizer (N₀ : Set G))
    (htN : t ∈ normalizer (N₀ : Set G)) (htB : t ∈ normalizer (B : Set G)) (ht : t ^ 2 ^ n = 1) :
    ∃ T : Subgroup G, fusionIsSylowIn 2 T N₀ ∧ B ≤ normalizer (T : Set G) ∧
      t ∈ normalizer (T : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  set C : Subgroup G := N₀ ⊓ centralizer (B : Set G)
  obtain ⟨W₀⟩ := (inferInstance : Nonempty (Sylow 2 ↥C))
  set W : Subgroup G := (W₀ : Subgroup ↥C).map C.subtype
  have hWC : W ≤ C := map_subtype_le _
  have hW2 : IsPGroup 2 W := W₀.isPGroup'.map _
  have hBW : B ≤ normalizer (W : Set G) :=
    (le_centralizer_iff.1 (hWC.trans inf_le_right)).trans (centralizer_le_normalizer _)
  obtain ⟨T₀, hT₀, hWT₀, hBT₀⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hB hN₀ hBN (hWC.trans inf_le_left) hW2 hBW
  let 𝒮 := {T : Subgroup G // fusionIsSylowIn 2 T N₀ ∧ B ≤ normalizer (T : Set G)}
  have hmemS : ∀ c : ↥C, fusionIsSylowIn 2 (T₀.map (MulAut.conj (c : G)).toMonoidHom) N₀ ∧
      B ≤ normalizer ((T₀.map (MulAut.conj (c : G)).toMonoidHom : Subgroup G) : Set G) := by
    intro c
    refine ⟨fusionIsSylowIn_map_conj hT₀ (le_normalizer (mem_inf.1 c.2).1),
      le_normalizer_map_conj ?_ hBT₀⟩
    exact centralizer_le_normalizer _ (mem_inf.1 c.2).2
  let ψ : ↥C ⧸ (normalizer (T₀ : Set G)).subgroupOf C → 𝒮 :=
    Quotient.lift (fun c : ↥C => (⟨T₀.map (MulAut.conj (c : G)).toMonoidHom, hmemS c⟩ : 𝒮))
      (by
        intro a b hab
        have hab := QuotientGroup.leftRel_apply.mp hab
        rw [mem_subgroupOf] at hab
        apply Subtype.ext
        exact map_conj_eq_iff.2 (by simpa using hab))
  have hψ : Function.Bijective ψ := by
    constructor
    · intro a b hab
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      have h := congrArg Subtype.val hab
      change T₀.map (MulAut.conj (a : G)).toMonoidHom =
        T₀.map (MulAut.conj (b : G)).toMonoidHom at h
      rw [QuotientGroup.eq, mem_subgroupOf]
      simpa using map_conj_eq_iff.1 h
    · rintro ⟨T', hT'syl, hBT'⟩
      obtain ⟨c, hc, hT'c⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
        Nat.prime_three Nat.prime_two hB hN₀ hBN hT₀ hT'syl hBT₀ hBT'
      exact ⟨((⟨c, hc⟩ : ↥C) : ↥C ⧸ (normalizer (T₀ : Set G)).subgroupOf C),
        Subtype.ext hT'c.symm⟩
  have hcardS : Nat.card 𝒮 = ((normalizer (T₀ : Set G)).subgroupOf C).index :=
    (Nat.card_congr (Equiv.ofBijective ψ hψ)).symm
  have hodd : ¬ 2 ∣ Nat.card 𝒮 := by
    rw [hcardS]
    have hle : (W₀ : Subgroup ↥C) ≤ (normalizer (T₀ : Set G)).subgroupOf C := by
      intro w hw
      rw [mem_subgroupOf]
      exact le_normalizer (hWT₀ ⟨w, hw, rfl⟩)
    exact fun hd => W₀.not_dvd_index (hd.trans (index_dvd_of_le hle))
  have hσmem : ∀ T : 𝒮, fusionIsSylowIn 2 (T.1.map (MulAut.conj t).toMonoidHom) N₀ ∧
      B ≤ normalizer ((T.1.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := fun T =>
    ⟨fusionIsSylowIn_map_conj T.2.1 htN, le_normalizer_map_conj htB T.2.2⟩
  let σ : Function.End 𝒮 := fun T => ⟨T.1.map (MulAut.conj t).toMonoidHom, hσmem T⟩
  have hσpow : ∀ (k : ℕ) (T : 𝒮), ((σ ^ k) T).1 = T.1.map (MulAut.conj (t ^ k)).toMonoidHom := by
    intro k
    induction k with
    | zero =>
      intro T
      change T.1 = T.1.map (MulAut.conj (t ^ 0)).toMonoidHom
      ext x
      rw [mem_map_conj, pow_zero]
      simp
    | succ k ih =>
      intro T
      rw [pow_succ]
      change ((σ ^ k) (σ T)).1 = _
      rw [ih]
      change (T.1.map (MulAut.conj t).toMonoidHom).map _ = _
      rw [map_map]
      congr 1
      ext x
      simp [pow_succ, mul_assoc]
  have hσ : σ ^ 2 ^ n = 1 := by
    funext T
    apply Subtype.ext
    rw [hσpow, ht]
    ext x
    rw [mem_map_conj]
    simp only [inv_one, one_mul, mul_one]
    rfl
  have : Fintype 𝒮 := Fintype.ofFinite 𝒮
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := σ) (p := 2) (n := n) hσ
  have hfix : Nonempty (Function.fixedPoints σ) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h0 : Fintype.card (Function.fixedPoints σ) = 0 := Fintype.card_eq_zero
    rw [h0, Nat.modEq_zero_iff_dvd, ← Nat.card_eq_fintype_card] at hmod
    exact hodd hmod
  obtain ⟨⟨⟨T, hTsyl, hBT⟩, hTfix⟩⟩ := hfix
  refine ⟨T, hTsyl, hBT, ?_⟩
  have h := congrArg Subtype.val hTfix
  exact mem_normalizer_iff_map_conj_eq.2 h

theorem exists_sylow_two_invariant_containing {D B S₀ : Subgroup G} {t : G} {n : ℕ}
    (hB : IsPGroup 3 B) (hD : ¬ 3 ∣ Nat.card D) (hBD : B ≤ normalizer (D : Set G))
    (htD : t ∈ normalizer (D : Set G)) (htB : t ∈ normalizer (B : Set G)) (ht : t ^ 2 ^ n = 1)
    (hS₀D : S₀ ≤ D) (hS₀ : IsPGroup 2 S₀) (hBS₀ : B ≤ normalizer (S₀ : Set G))
    (htS₀ : t ∈ normalizer (S₀ : Set G)) :
    ∃ T : Subgroup G, fusionIsSylowIn 2 T D ∧ S₀ ≤ T ∧ B ≤ normalizer (T : Set G) ∧
      t ∈ normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  let 𝒞 : Subgroup G → Prop := fun T => T ≤ D ∧ IsPGroup 2 T ∧ S₀ ≤ T ∧
    B ≤ normalizer (T : Set G) ∧ t ∈ normalizer (T : Set G)
  obtain ⟨T, -, hTmax⟩ := Finite.exists_le_maximal (p := 𝒞) ⟨hS₀D, hS₀, le_rfl, hBS₀, htS₀⟩
  obtain ⟨hTD, hT2, hS₀T, hBT, htT⟩ := hTmax.1
  refine ⟨T, ⟨hTD, hT2, fun P hPD hP hTP => ?_⟩, hS₀T, hBT, htT⟩
  by_contra hne
  set N₀ := D ⊓ normalizer (T : Set G)
  have hBN₀ : B ≤ normalizer (N₀ : Set G) :=
    CFSG.Goldschmidt.G310.le_normalizer_inf hBD (hBT.trans le_normalizer)
  have htN₀ : t ∈ normalizer (N₀ : Set G) :=
    CFSG.Goldschmidt.G310.le_normalizer_inf (zpowers_le.2 htD) (zpowers_le.2 (le_normalizer htT))
      (mem_zpowers t)
  have hN₀3 : ¬ 3 ∣ Nat.card N₀ := fun hd => hD (hd.trans (card_dvd_of_le inf_le_left))
  obtain ⟨T', ⟨hT'N, hT'2, hT'max⟩, hBT', htT'⟩ :=
    exists_sylow_two_invariant hB hN₀3 hBN₀ htN₀ htB ht
  have hTN₀ : T ≤ N₀ := le_inf hTD le_normalizer
  have hTT' : T ≤ T' := by
    have hsup : IsPGroup 2 ↥(T' ⊔ T) :=
      IsPGroup.to_sup_of_normal_right' hT'2 hT2 (hT'N.trans inf_le_right)
    have := hT'max (T' ⊔ T) (sup_le hT'N hTN₀) hsup le_sup_left
    exact this ▸ le_sup_right
  have hT'T : T' = T :=
    (hTmax.2 ⟨hT'N.trans inf_le_left, hT'2, hS₀T.trans hTT', hBT', htT'⟩ hTT').antisymm hTT'
  have hlt := CFSG.Goldschmidt.G310.lt_inf_normalizer hP hTP (Ne.symm hne)
  have hle : P ⊓ normalizer (T : Set G) ≤ N₀ := inf_le_inf_right _ hPD
  have := hT'max (P ⊓ normalizer (T : Set G)) hle (hP.to_le inf_le_left)
    (hT'T ▸ hlt.le)
  exact hlt.ne (this.trans hT'T).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

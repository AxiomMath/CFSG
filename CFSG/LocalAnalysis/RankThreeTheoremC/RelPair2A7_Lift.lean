module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Coprime
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {Y X : Type} [Group Y] [Finite Y] [Group X]

theorem card_comap_eq_card_ker_mul (π : Y →* X) (hπ : Function.Surjective π) (W : Subgroup X) :
    Nat.card (W.comap π) = Nat.card π.ker * Nat.card W := by
  have hfin : Finite X := Finite.of_surjective π hπ
  have h1 := Subgroup.card_mul_index (W.comap π)
  have h2 := Subgroup.card_mul_index W
  have h3 := Subgroup.card_ker_mul_card_of_surjective hπ
  rw [Subgroup.index_comap_of_surjective W hπ] at h1
  have hpos : 0 < W.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card (W.comap π) * W.index = Nat.card Y := h1
    _ = Nat.card π.ker * Nat.card X := h3.symm
    _ = Nat.card π.ker * (Nat.card W * W.index) := by rw [h2]
    _ = (Nat.card π.ker * Nat.card W) * W.index := by ring

theorem isSylowOf_map_hom {A B : Type} [Group A] [Finite A] [Group B] {p : ℕ} [Fact p.Prime]
    (f : A →* B) {P K : Subgroup A} (h : IsSylowOf p P K) :
    IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

omit [Finite Y] in
theorem card_eq_card_map_mul_card_inf_ker (π : Y →* X) (V : Subgroup Y) :
    Nat.card V = Nat.card (V.map π) * Nat.card (V ⊓ π.ker : Subgroup Y) := by
  have h := Subgroup.card_ker_mul_card_range (π.domRestrict V)
  rw [MonoidHom.domRestrict_range] at h
  have hker : Nat.card (π.domRestrict V).ker = Nat.card (V ⊓ π.ker : Subgroup Y) := by
    rw [MonoidHom.ker_domRestrict]
    have h1 : (V ⊓ π.ker).subgroupOf V = π.ker.subgroupOf V := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [← h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← h, hker, mul_comm]

omit [Finite Y] in
theorem inf_eq_bot_of_isPGroup_of_coprime {q : ℕ} (hq : q.Prime) {P N : Subgroup Y}
    (hP : IsPGroup q P) (hN : q.Coprime (Nat.card N)) : P ⊓ N = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxP, hxN⟩ := hx
  have h1 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxN
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hxP⟩
  have h2 : orderOf x = q ^ k := by simpa using hk
  have h3 : (q ^ k).Coprime (Nat.card N) := Nat.Coprime.pow_left k hN
  have : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd (h2 ▸ h3) h1
  exact orderOf_eq_one_iff.mp this

theorem rankTwoMaximalInvariantTwoSubgroup_map_of_ker {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (π : Y →* X) (hπ : Function.Surjective π) (hker : q.Coprime (Nat.card π.ker))
    {Dy Vy : Subgroup Y} (hD : IsPGroup q Dy) (hV : rankTwoMaximalInvariantTwoSubgroup Dy Vy) :
    rankTwoMaximalInvariantTwoSubgroup (Dy.map π) (Vy.map π) := by
  classical
  have hfin : Finite X := Finite.of_surjective π hπ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hV.1.map π, (Subgroup.map_mono hV.2.1).trans (Subgroup.le_normalizer_map π), ?_⟩
  intro W hW2 hDW hVW
  set Wt : Subgroup Y := W.comap π with hWt
  have hDWt : Dy ≤ normalizer (Wt : Set Y) := by
    intro d hd
    rw [mem_normalizer_iff]
    intro w
    have hπd : π d ∈ normalizer (W : Set X) := hDW ⟨d, hd, rfl⟩
    have := mem_normalizer_iff.mp hπd (π w)
    simpa [hWt, mem_comap, map_mul, map_inv] using this
  have hcop : q.Coprime (Nat.card Wt) := by
    rw [hWt, card_comap_eq_card_ker_mul π hπ W]
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    rw [hk]
    exact hker.mul_right (Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2))
  have hVWt : Vy ≤ Wt := (Subgroup.le_comap_map π Vy).trans (Subgroup.comap_mono hVW)
  obtain ⟨B, hVB, hBS, hDB⟩ :=
    exists_isSylowOf_normalized_containing hq hD hDWt hcop hVWt hV.1 hV.2.1
  have hBV : B = Vy := hV.2.2 B hBS.isPGroup hDB hVB
  have hS : IsSylowOf 2 (Vy.map π) (Wt.map π) := by
    have := isSylowOf_map_hom (p := 2) π hBS
    rwa [hBV] at this
  rw [hWt, Subgroup.map_comap_eq_self_of_surjective hπ] at hS
  exact hS.eq_of_le hVW le_rfl hW2

omit [Finite Y] in
theorem mem_map_conj_iff_implicit {K : Subgroup Y} {g x : Y} :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem exists_mem_normalizer_map_eq_mul {q : ℕ} (hq : q.Prime) (π : Y →* X)
    (hπ : Function.Surjective π) (hker : q.Coprime (Nat.card π.ker)) {Dy : Subgroup Y}
    (hD : IsPGroup q Dy) {n : X} (hn : n ∈ normalizer ((Dy.map π : Subgroup X) : Set X)) :
    ∃ m ∈ normalizer (Dy : Set Y), ∃ d ∈ Dy.map π, π m = n * d := by
  classical
  have hfact : Fact q.Prime := ⟨hq⟩
  obtain ⟨h, rfl⟩ := hπ n
  set Dt : Subgroup Y := (Dy.map π).comap π with hDt
  have hDyDt : Dy ≤ Dt := Subgroup.le_comap_map π Dy
  have hinf : Dy ⊓ π.ker = ⊥ := inf_eq_bot_of_isPGroup_of_coprime hq hD hker
  have hcardmap : Nat.card (Dy.map π) = Nat.card Dy := by
    have := card_eq_card_map_mul_card_inf_ker π Dy
    rw [hinf, Subgroup.card_bot, mul_one] at this
    exact this.symm
  have hDtcard : Nat.card Dt = Nat.card π.ker * Nat.card Dy := by
    rw [hDt, card_comap_eq_card_ker_mul π hπ, hcardmap]
  have hsyl : ∀ D₁ : Subgroup Y, D₁ ≤ Dt → IsPGroup q D₁ → Nat.card D₁ = Nat.card Dy →
      IsSylowOf q D₁ Dt := by
    intro D₁ hle hpg hc
    rw [isSylowOf_iff]
    refine ⟨hle, hpg, ?_⟩
    have h1 := Subgroup.relIndex_mul_card D₁ Dt
    rw [inf_eq_left.mpr hle, hDtcard, hc] at h1
    have hpos : 0 < Nat.card Dy := Nat.card_pos
    have h2 : D₁.relIndex Dt = Nat.card π.ker := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      exact h1
    rw [h2]
    exact (Nat.Prime.coprime_iff_not_dvd hq).mp hker
  set D' : Subgroup Y := Dy.map (MulAut.conj h⁻¹).toMonoidHom with hD'
  have hD'mem : ∀ x : Y, x ∈ D' ↔ h * x * h⁻¹ ∈ Dy := by
    intro x
    rw [hD', mem_map_conj_iff_implicit]
    simp
  have hD'le : D' ≤ Dt := by
    intro x hx
    have hx' := (hD'mem x).mp hx
    have h1 : π (h * x * h⁻¹) ∈ Dy.map π := ⟨_, hx', rfl⟩
    rw [map_mul, map_mul, map_inv] at h1
    have := (mem_normalizer_iff.mp hn (π x)).mpr h1
    exact this
  have hD'card : Nat.card D' = Nat.card Dy :=
    Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective
  obtain ⟨t, ht, hconj⟩ := IsSylowOf.exists_mem_conj (hsyl Dy hDyDt hD rfl)
    (hsyl D' hD'le (hD.map _) hD'card)
  refine ⟨h * t, ?_, π t, ?_, by rw [map_mul]⟩
  · rw [mem_normalizer_iff]
    intro y
    have h1 : h * (t * y * t⁻¹) * h⁻¹ = h * t * y * (h * t)⁻¹ := by group
    rw [← h1]
    constructor
    · intro hy
      have : t * y * t⁻¹ ∈ D' := (hconj _).mpr (by simpa [mul_assoc] using hy)
      exact (hD'mem _).mp this
    · intro hy
      have := (hD'mem _).mpr hy
      have := (hconj _).mp this
      simpa [mul_assoc] using this
  · exact Subgroup.mem_comap.mp ht

theorem exists_isElemAbelian_card_eq_of_map {q : ℕ} (hq : q.Prime) (π : Y →* X)
    (hπ : Function.Surjective π) (hker : q.Coprime (Nat.card π.ker)) {E : Subgroup X}
    (hE : IsElemAbelian q E) :
    ∃ E' : Subgroup Y, IsElemAbelian q E' ∧ Nat.card E' = Nat.card E := by
  classical
  have hfact : Fact q.Prime := ⟨hq⟩
  have hEp : IsPGroup q E := fun x => ⟨1, by
    have := hE.2 x x.2
    exact Subtype.ext (by simpa using this)⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf q (E.comap π)
  have hfin : Finite X := Finite.of_surjective π hπ
  have hPE : P.map π = E := by
    have h1 := isSylowOf_map_hom (p := q) π hP
    rw [Subgroup.map_comap_eq_self_of_surjective hπ E] at h1
    exact (h1.eq_of_le h1.le le_rfl hEp).symm
  have hinf : P ⊓ π.ker = ⊥ := inf_eq_bot_of_isPGroup_of_coprime hq hP.isPGroup hker
  have hcard : Nat.card P = Nat.card E := by
    have := card_eq_card_map_mul_card_inf_ker π P
    rw [hinf, Subgroup.card_bot, mul_one, hPE] at this
    exact this
  have hmem : ∀ x ∈ P, π x ∈ E := fun x hx => hPE ▸ ⟨x, hx, rfl⟩
  have hker0 : ∀ z ∈ P, π z = 1 → z = 1 := by
    intro z hz h1
    have : z ∈ P ⊓ π.ker := ⟨hz, h1⟩
    rw [hinf] at this
    exact Subgroup.mem_bot.mp this
  refine ⟨P, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, hcard⟩
  · apply Subtype.ext
    have hc : x.1 * y.1 * x.1⁻¹ * y.1⁻¹ = 1 := by
      apply hker0 _ (P.mul_mem (P.mul_mem (P.mul_mem x.2 y.2) (P.inv_mem x.2)) (P.inv_mem y.2))
      have hxy : π x.1 * π y.1 = π y.1 * π x.1 := by
        have := hE.1.is_comm.comm ⟨π x.1, hmem _ x.2⟩ ⟨π y.1, hmem _ y.2⟩
        exact congrArg Subtype.val this
      simp only [map_mul, map_inv]
      calc π x.1 * π y.1 * (π x.1)⁻¹ * (π y.1)⁻¹ = (π y.1 * π x.1) * (π x.1)⁻¹ * (π y.1)⁻¹ := by
            rw [hxy]
        _ = 1 := by group
    have : x.1 * y.1 = y.1 * x.1 := by
      calc x.1 * y.1 = (x.1 * y.1 * x.1⁻¹ * y.1⁻¹) * (y.1 * x.1) := by group
        _ = y.1 * x.1 := by rw [hc, one_mul]
    simpa using this
  · apply hker0 _ (P.pow_mem hx q)
    rw [map_pow]
    exact hE.2 _ (hmem x hx)

end CFSG.LocalAnalysis.RankThreeTheoremC

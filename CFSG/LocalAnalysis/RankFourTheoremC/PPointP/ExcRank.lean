module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTypes

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open CFSG.Open CFSG.AGLEmbedding Subgroup

@[expose] def ExcludedAltSpor (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  (∃ h : 5 ≤ 2 * p, 7 ≤ p ∧ i = .alternating (2 * p) h) ∨ (p = 5 ∧ i = .sporadic .Fi22) ∨
    ((p = 11 ∨ p = 13) ∧ i = .sporadic .M)

@[expose] def ExcludedSpor (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  (p = 5 ∧ i = .sporadic .Fi22) ∨ ((p = 11 ∨ p = 13) ∧ i = .sporadic .M)

@[expose] def KFactExcludedRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ) (i : TauCeti.CFSGIndex), p.Prime →
    ExcludedSpor p i → Nonempty (K ≃* i.Group) →
    ∀ B : Subgroup K, IsElemAbelian p B → Nat.card B ≤ p ^ 2

@[expose] def KFactExcludedInner : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ) (i : TauCeti.CFSGIndex), p.Prime →
    ExcludedAltSpor p i → Nonempty (K ≃* i.Group) →
    ∀ A : Subgroup (MulAut K), IsPGroup p A → A ≤ (MulAut.conj : K →* MulAut K).range

theorem pow_dvd_two_mul_factorial {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) {k : ℕ}
    (h : p ^ k ∣ Nat.factorial (2 * p)) : k ≤ 2 := by
  have hlog : Nat.log p (2 * p) < 2 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    nlinarith [hp.out.two_le]
  have hv := padicValNat_factorial (p := p) (n := 2 * p) (b := 2) hlog
  have h2 : ∑ i ∈ Finset.Ico 1 2, 2 * p / p ^ i = 2 := by
    simp [Nat.mul_div_cancel _ hp.out.pos]
  rw [h2] at hv
  rw [← hv]
  exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).mp h

theorem card_le_sq_of_alt {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) {K : Type} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin (2 * p))) {B : Subgroup K} (hBp : IsPGroup p B) :
    Nat.card B ≤ p ^ 2 := by
  obtain ⟨k, hk⟩ := hBp.exists_card_eq
  have hdvd : Nat.card B ∣ Nat.card K := Subgroup.card_subgroup_dvd_card B
  have hK : Nat.card K = Nat.factorial (2 * p) / 2 := by
    have : Nontrivial (Fin (2 * p)) :=
      Fin.nontrivial_iff_two_le.mpr (by have := hp.out.two_le; omega)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
  rw [hK, hk] at hdvd
  have h2 : p ^ k ∣ Nat.factorial (2 * p) := hdvd.trans (Nat.div_dvd_of_dvd (Nat.dvd_factorial
    (by norm_num) (by have := hp.out.two_le; omega)))
  rw [hk]
  exact Nat.pow_le_pow_right hp.out.pos (pow_dvd_two_mul_factorial hp3 h2)

theorem card_le_sq_of_excluded {p : ℕ} [Fact p.Prime] {i : TauCeti.CFSGIndex}
    (hKR : KFactExcludedRank) (hi : ExcludedAltSpor p i) {K : Type} [Group K] [Finite K]
    (e : Nonempty (K ≃* i.Group)) {B : Subgroup K} (hB : IsElemAbelian p B) :
    Nat.card B ≤ p ^ 2 := by
  rcases hi with ⟨h, hp7, rfl⟩ | h | h
  · obtain ⟨e'⟩ := e
    exact card_le_sq_of_alt (by omega) e' (fun g => ⟨1, by simpa using Subtype.ext (hB.2 g g.2)⟩)
  · exact hKR K p _ Fact.out (Or.inl h) e B hB
  · exact hKR K p _ Fact.out (Or.inr h) e B hB

theorem card_le_cube_of_isElemAbelian {p : ℕ} [Fact p.Prime] {i : TauCeti.CFSGIndex}
    (hi : ExcludedAltSpor p i) (hKR : KFactExcludedRank) (hKI : KFactExcludedInner)
    {X : Type} [Group X] [Finite X] {K : Subgroup X} (hKn : K.Normal)
    (e : Nonempty (K ≃* i.Group)) (hZ : center K = ⊥)
    (hC : IsCyclic (centralizer (K : Set X))) {B : Subgroup X} (hB : IsElemAbelian p B) :
    Nat.card B ≤ p ^ 3 := by
  classical
  have hp : p.Prime := Fact.out
  have _ := hKn
  let ψ : B →* MulAut K := (MulAut.conjNormal : X →* MulAut K).comp B.subtype
  have hker : Nat.card ψ.ker ≤ p := by
    let j : ψ.ker → {c : centralizer (K : Set X) // c ^ p = 1} := fun b => ⟨⟨(b.1 : X), by
      rw [mem_centralizer_iff]
      intro k hk
      have h := (congrArg (fun a : MulAut K => ((a ⟨k, hk⟩ : K) : X)) b.2).symm
      simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulAut.conjNormal_apply, MulAut.one_apply] at h
      exact (eq_mul_inv_iff_mul_eq.mp h)⟩, by
        apply Subtype.ext
        simpa using hB.2 (b.1 : X) b.1.2⟩
    have hj : Function.Injective j := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun c : {c : centralizer (K : Set X) // c ^ p = 1} => (c.1 : X)) hab
    have h1 := Nat.card_le_card_of_injective j hj
    have h2 : Nat.card {c : centralizer (K : Set X) // c ^ p = 1} ≤ p := by
      have := Fintype.ofFinite (centralizer (K : Set X))
      have := IsCyclic.card_pow_eq_one_le (α := centralizer (K : Set X)) (n := p) hp.pos
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact this
    exact h1.trans h2
  have hrange_p : IsPGroup p ψ.range := by
    intro g
    obtain ⟨g, b, rfl⟩ := g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, show b ^ p = 1 from Subtype.ext (hB.2 b b.2), map_one]
  have hle : ψ.range ≤ (MulAut.conj : K →* MulAut K).range :=
    hKI K p i hp hi e ψ.range hrange_p
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    intro a b hab
    have hc : b⁻¹ * a ∈ center K := by
      rw [mem_center_iff]
      intro k
      have h : a * k * a⁻¹ = b * k * b⁻¹ := by
        have := congrArg (fun f : MulAut K => f k) hab
        simpa [MulAut.conj_apply] using this
      calc k * (b⁻¹ * a) = b⁻¹ * (b * k * b⁻¹) * a := by group
        _ = b⁻¹ * (a * k * a⁻¹) * a := by rw [h]
        _ = b⁻¹ * a * k := by group
    rw [hZ, mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  set F : Subgroup K := ψ.range.comap (MulAut.conj : K →* MulAut K) with hF
  have hFmap : F.map (MulAut.conj : K →* MulAut K) = ψ.range := by
    rw [hF, Subgroup.map_comap_eq]
    exact inf_of_le_right hle
  have hFcard : Nat.card F = Nat.card ψ.range := by
    rw [← hFmap, Subgroup.card_map_of_injective hinj]
  have hFel : IsElemAbelian p F := by
    have hmem : ∀ k : K, k ∈ F → ∃ u : B, MulAut.conj k = ψ u := fun k hk => by
      obtain ⟨u, hu⟩ := hk
      exact ⟨u, hu.symm⟩
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun k hk => ?_⟩
    · obtain ⟨u, hu⟩ := hmem a a.2
      obtain ⟨v, hv⟩ := hmem b b.2
      apply Subtype.ext
      apply hinj
      have huv : u * v = v * u := hB.1.is_comm.comm u v
      show MulAut.conj ((a : K) * b) = MulAut.conj ((b : K) * a)
      rw [map_mul, map_mul, hu, hv, ← map_mul, ← map_mul, huv]
    · obtain ⟨u, hu⟩ := hmem k hk
      apply hinj
      rw [map_pow, hu, ← map_pow, show u ^ p = 1 from Subtype.ext (hB.2 u u.2), map_one, map_one]
  have hF2 : Nat.card F ≤ p ^ 2 := card_le_sq_of_excluded hKR hi e hFel
  have hmul := Subgroup.card_ker_mul_card_range ψ
  rw [← hmul, ← hFcard]
  calc Nat.card ψ.ker * Nat.card F ≤ p * p ^ 2 := Nat.mul_le_mul hker hF2
    _ = p ^ 3 := by ring


theorem altSpor_or_of_excluded {p : ℕ} {i : TauCeti.CFSGIndex} (h : PPointExcluded p i) :
    ExcludedAltSpor p i ∨ (∃ d, i = .lie d ∧ IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨
      (∃ d, i = .lie d ∧ IsReeGTwoIndex p d) := by
  cases h with
  | altTwoP h hp => exact Or.inl (Or.inl ⟨h, hp, rfl⟩)
  | fiTwentyTwo hp => exact Or.inl (Or.inr (Or.inl ⟨hp, rfl⟩))
  | monster hp => exact Or.inl (Or.inr (Or.inr ⟨hp, rfl⟩))
  | unitary hd hn => exact Or.inr (Or.inl ⟨_, rfl, hd, hn⟩)
  | ree hd => exact Or.inr (Or.inr ⟨_, rfl, hd⟩)

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP

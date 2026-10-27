module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableCrit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableTransport

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def K32ZBound (N : Type) [Group N] (m : ℕ) : Prop :=
  ∀ ω : MulAut N, orderOf ω = 3 → ∀ W : Subgroup (MulAut N), W ≤ innAut N → IsPGroup 2 ↥W →
    W ≤ Subgroup.centralizer ({ω} : Set (MulAut N)) → Nat.card ↥W ≤ m

theorem k32AutQuot_conj {K : Type} [Group K] (k : K) :
    k32AutQuot K (MulAut.conj k) = MulAut.conj (k : K ⧸ Subgroup.center K) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H z => rfl

theorem k32_noDatum_of_quot {K N : Type} [Group K] [Finite K] [Group N] [Finite N]
    (hperf : Group.IsPerfect K) (e : K ⧸ Subgroup.center K ≃* N) {m : ℕ} (hN : K32ZBound N m)
    (hlt : 16 * m < 2 ^ (Nat.card N).factorization 2) : K32NoDatum K := by
  intro X P R A V hd
  obtain ⟨ω, -, hω3, W, hWJ, hW2, hWC, hcard⟩ := k32_crit hd
  have : Group.IsPerfect K := hperf
  let Φ : MulAut K →* MulAut N := (MulAut.congr e).toMonoidHom.comp (k32AutQuot K)
  have hΦinj : Function.Injective Φ :=
    (MulAut.congr e).injective.comp k32AutQuot_injective
  have hω3' : orderOf (Φ ω) = 3 := (orderOf_injective Φ hΦinj ω).trans hω3
  have hWΦ2 : IsPGroup 2 ↥(W.map Φ) := hW2.of_equiv (Subgroup.equivMapOfInjective W Φ hΦinj)
  have hWΦJ : W.map Φ ≤ innAut N := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, rfl⟩ := hWJ hw
    refine ⟨e (k : K ⧸ Subgroup.center K), ?_⟩
    show MulAut.conj (e (k : K ⧸ Subgroup.center K)) =
      MulAut.congr e (k32AutQuot K (MulAut.conj k))
    rw [k32AutQuot_conj, k32_congr_conj]
  have hWΦC : W.map Φ ≤ Subgroup.centralizer ({Φ ω} : Set (MulAut N)) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hWC hw)
    rw [← map_mul, ← map_mul, h1]
  have hbound := hN (Φ ω) hω3' (W.map Φ) hWΦJ hWΦ2 hWΦC
  rw [Subgroup.card_map_of_injective hΦinj] at hbound
  have h2 : twoPart (innAut K) = 2 ^ (Nat.card N).factorization 2 := by
    unfold twoPart
    rw [k32_card_innAut, Nat.card_congr e.toEquiv]
  have h3 := hcard.trans (Nat.mul_le_mul_left 16 hbound)
  rw [h2] at h3
  exact absurd (lt_of_le_of_lt h3 hlt) (lt_irrefl _)

theorem k32ZBound_of_centralizer {N : Type} [Group N] [Finite N] (hZ : Subgroup.center N = ⊥)
    (hout : ∀ ω : MulAut N, orderOf ω = 3 → ω ∈ innAut N) {m : ℕ}
    (hcent : ∀ g : N, orderOf g = 3 → ∀ W : Subgroup N, IsPGroup 2 ↥W →
      W ≤ Subgroup.centralizer ({g} : Set N) → Nat.card ↥W ≤ m) : K32ZBound N m := by
  intro ω hω3 W hWJ hW2 hWC
  have hinj : Function.Injective (MulAut.conj : N →* MulAut N) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : a ∈ (MulAut.conj : N →* MulAut N).ker := ha
    rw [k32_conj_ker, hZ, Subgroup.mem_bot] at h1
    exact h1
  obtain ⟨g, rfl⟩ := hout ω hω3
  have hg3 : orderOf g = 3 := (orderOf_injective _ hinj g).symm.trans hω3
  set W' := W.comap (MulAut.conj : N →* MulAut N) with hW'
  have hmap : W'.map (MulAut.conj : N →* MulAut N) = W := by
    rw [hW', Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hWJ
  have hcard : Nat.card ↥W' = Nat.card ↥W := by
    have h1 := Subgroup.card_map_of_injective (K := W') hinj
    rw [hmap] at h1
    exact h1.symm
  have hW'2 : IsPGroup 2 ↥W' := by
    refine hW2.of_injective (((MulAut.conj : N →* MulAut N).comp W'.subtype).codRestrict W
      (fun a => a.2)) ?_
    intro a b hab
    exact Subtype.ext (hinj (congrArg Subtype.val hab))
  have hW'C : W' ≤ Subgroup.centralizer ({g} : Set N) := by
    intro a ha
    have h1 : (MulAut.conj : N →* MulAut N) a ∈ W := ha
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hWC h1)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hinj
    rw [map_mul, map_mul]
    exact h2
  rw [← hcard]
  exact hcent g hg3 W' hW'2 hW'C

theorem k32_inner_of_orderThree {N : Type} [Group N] [Finite N] (hZ : Subgroup.center N = ⊥)
    (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N) (ω : MulAut N) (hω3 : orderOf ω = 3) :
    ω ∈ innAut N := by
  have hJn : (innAut N).Normal := innAut_normal N
  have hJcard : Nat.card ↥(innAut N) = Nat.card N := by
    rw [k32_card_innAut]
    have e1 := QuotientGroup.quotientMulEquivOfEq hZ
    have e2 := QuotientGroup.quotientBot (G := N)
    exact (Nat.card_congr e1.toEquiv).trans (Nat.card_congr e2.toEquiv)
  have hidx : (innAut N).index ≤ 2 := by
    have h1 := Subgroup.card_mul_index (innAut N)
    rw [hJcard] at h1
    have hpos : 0 < Nat.card N := Nat.card_pos
    by_contra hcon
    push Not at hcon
    have h3 : Nat.card N * 3 ≤ Nat.card N * (innAut N).index := Nat.mul_le_mul_left _ hcon
    omega
  have hidx0 : (innAut N).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hq3 : ((ω : MulAut N) : MulAut N ⧸ innAut N) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : ω ^ 3 = 1 := by rw [← hω3]; exact pow_orderOf_eq_one ω
    rw [this]
    rfl
  have hqi : ((ω : MulAut N) : MulAut N ⧸ innAut N) ^ (innAut N).index = 1 :=
    pow_card_eq_one' (G := MulAut N ⧸ innAut N) (x := (ω : MulAut N ⧸ innAut N))
  have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq3) (orderOf_dvd_of_pow_eq_one hqi)
  have hg : Nat.gcd 3 (innAut N).index = 1 := by
    have : (innAut N).index = 1 ∨ (innAut N).index = 2 := by omega
    rcases this with h | h <;> rw [h] <;> norm_num
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  exact (QuotientGroup.eq_one_iff ω).mp hdvd

theorem k32_card_le_four_of_dvd {W : Type} [Group W] [Finite W] (hW : IsPGroup 2 W) {c : ℕ}
    (hodd : c % 2 = 1) (hdvd : Nat.card W ∣ 4 * c) : Nat.card W ≤ 4 := by
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  rw [hk] at hdvd ⊢
  by_contra hcon
  have hk3 : 3 ≤ k := by
    by_contra h
    have : k ≤ 2 := by omega
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h8 : 8 ∣ 2 ^ k := by
    have : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 hk3
    simpa using this
  have := h8.trans hdvd
  omega

end CFSG.QuasithinUnique.DoubleA3

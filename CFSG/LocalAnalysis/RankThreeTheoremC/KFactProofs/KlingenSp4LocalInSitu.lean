module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalTransport
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {K U : Subgroup Y} [K.Normal]

namespace SiegelRadicalData

theorem dichotomy (T : Sylow p Y) (h : SiegelRadicalData p K (T : Subgroup Y) U)
    (m : SiegelModuleData K U) {Y₀ : Subgroup Y}
    (hY₀ : GLBWeakCore p (T : Subgroup Y) ≤ Y₀) (hne : Y₀ ≠ ⊤) {W : Subgroup Y} (hW : W ≤ Y₀)
    (hWn : Y₀ ≤ Subgroup.normalizer (W : Set Y)) : W = ⊥ ∨ U ≤ W := by
  have hY := h.eq_normalizer T hY₀ hne
  have hUY : U ≤ Y₀ := hY ▸ Subgroup.le_normalizer
  have hN : Subgroup.normalizer (U : Set Y) ⊓ K ≤
      Subgroup.normalizer ((W ⊓ U : Subgroup Y) : Set Y) := by
    intro y hy
    have hy1 : y ∈ Y₀ := hY ▸ hy.1
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (hWn hy1) x
    have h2 := Subgroup.mem_normalizer_iff.mp hy.1 x
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  rcases m.irred (W ⊓ U) inf_le_right hN with h1 | h1
  · left
    rw [eq_bot_iff]
    intro w hw
    have hcomm : ∀ u ∈ U, u * w = w * u := by
      intro u hu
      have hwU : w * u * w⁻¹ ∈ U := by
        have := Subgroup.mem_normalizer_iff.mp (hY ▸ hW hw : w ∈ Subgroup.normalizer (U : Set Y))
          u
        exact this.mp hu
      have hwW : u * w⁻¹ * u⁻¹ ∈ W := by
        have := Subgroup.mem_normalizer_iff.mp (hWn (hUY hu)) w⁻¹
        exact this.mp (W.inv_mem hw)
      have hc : w * u * w⁻¹ * u⁻¹ ∈ W ⊓ U := by
        refine ⟨?_, U.mul_mem hwU (U.inv_mem hu)⟩
        have := W.mul_mem hw hwW
        simpa [mul_assoc] using this
      rw [h1, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
      exact hc.symm
    have hwU : w ∈ U := m.centralizer_le (Subgroup.mem_centralizer_iff.mpr hcomm)
    have : w ∈ W ⊓ U := ⟨hw, hwU⟩
    rwa [h1, Subgroup.mem_bot] at this
  · right
    exact inf_eq_right.mp h1

theorem a3pInSitu (T : Sylow p Y) (h : SiegelRadicalData p K (T : Subgroup Y) U)
    (m : SiegelModuleData K U) {B Y₀ : Subgroup Y} (hBT : B ≤ (T : Subgroup Y))
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 3)
    (hY₀ : GLBWeakCore p (T : Subgroup Y) ≤ Y₀) (hne : Y₀ ≠ ⊤) :
    A3pInSitu p (T : Subgroup Y) B Y₀ := by
  have hp : p.Prime := Fact.out
  have hBU : B = U := h.unique B hBT hB hBc
  subst hBU
  refine ⟨fun W hW hWn hcop => ?_, fun W hW hWn => h.dichotomy T m hY₀ hne hW hWn, ?_⟩
  · rcases h.dichotomy T m hY₀ hne hW hWn with h1 | h1
    · exact h1
    · exfalso
      have hdvd : p ∣ Nat.card W := by
        refine (dvd_pow_self p (by norm_num : 3 ≠ 0)).trans ?_
        rw [← hBc]
        exact Subgroup.card_dvd_of_le h1
      have := Nat.dvd_gcd (dvd_refl p) hdvd
      rw [hcop] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · exact fun y hy => h.U_le (m.centralizer_le hy.2)

theorem a9InSitu (T : Sylow 3 Y) (hp3 : p = 3) (h : SiegelRadicalData 3 K (T : Subgroup Y) U)
    (m : SiegelModuleData K U)
    (hnn : ¬ Subgroup.normalizer (U : Set Y) ⊓ K ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hsol : Group.IsSolvable ↥(Subgroup.normalizer (U : Set Y) ⊓ K))
    (hq : Group.IsSolvable (Y ⧸ K)) {B Y₀ : Subgroup Y} (hBT : B ≤ (T : Subgroup Y))
    (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 3 ^ 3)
    (hY₀ : GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀) (hne : Y₀ ≠ ⊤) :
    A9InSitu (T : Subgroup Y) B Y₀ := by
  subst hp3
  have hBU : B = U := h.unique B hBT hB hBc
  rw [hBU]
  have hY := h.eq_normalizer T hY₀ hne
  have hTY : (T : Subgroup Y) ≤ Y₀ := hY ▸ h.T_le_normalizer
  refine ⟨hY.le, fun W hW hWn hcop => ?_, fun W hW hWn => h.dichotomy T m hY₀ hne hW hWn,
    fun y hy => m.centralizer_le hy.2, fun W hW hWn hWp => ?_, ?_, ?_⟩
  · rcases h.dichotomy T m hY₀ hne hW hWn with h1 | h1
    · exact h1
    · exfalso
      have hdvd : 3 ∣ Nat.card W := by
        refine (dvd_pow_self 3 (by norm_num : 3 ≠ 0)).trans ?_
        rw [← h.card_U]
        exact Subgroup.card_dvd_of_le h1
      have := Nat.dvd_gcd (dvd_refl 3) hdvd
      rw [hcop] at this
      exact absurd (Nat.dvd_one.mp this) (by norm_num)
  ·
    rcases h.dichotomy T m hY₀ hne hW hWn with h1 | h1
    · rw [h1]
      exact bot_le
    ·
      have hsup : IsPGroup 3 (W ⊔ (T : Subgroup Y) : Subgroup Y) :=
        hWp.to_sup_of_normal_left' T.isPGroup' (fun t ht => hWn (hTY ht))
      have hWT : W ≤ (T : Subgroup Y) := by
        have := T.is_maximal' hsup le_sup_right
        exact le_sup_left.trans this.le
      have hdvd : Nat.card W ∣ 3 ^ 4 := h.card_T ▸ Subgroup.card_dvd_of_le hWT
      obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
      have hdvd3 : 3 ^ 3 ∣ Nat.card W := h.card_U ▸ Subgroup.card_dvd_of_le h1
      rw [hjc] at hdvd3
      have hj3 : 3 ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd3
      have hj34 : j = 3 ∨ j = 4 := by omega
      rcases hj34 with rfl | rfl
      · exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hjc, h.card_U])).ge
      · exfalso
        have hWTeq : W = (T : Subgroup Y) :=
          Subgroup.eq_of_le_of_card_ge hWT (by rw [hjc, h.card_T])
        apply hnn
        intro y hy
        have hy1 : y ∈ Y₀ := hY ▸ hy.1
        have := hWn hy1
        rwa [hWTeq] at this
  ·
    rw [hY]
    let G₀ := Subgroup.normalizer (U : Set Y)
    let Q := Subgroup.normalizer (U : Set Y) ⊓ K
    have hQ : Group.IsSolvable ↥(Q.subgroupOf G₀) :=
      Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Q ≤ G₀)).symm.toMonoidHom) (MulEquiv.surjective _)
    refine Group.isSolvable_of_ker_le_range (Q.subgroupOf G₀).subtype
      ((QuotientGroup.mk' K).comp G₀.subtype) ?_
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hy
    exact ⟨⟨y, ⟨y.2, hy⟩⟩, rfl⟩
  · exact h.pRank_top_le T

end SiegelRadicalData

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

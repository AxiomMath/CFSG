module

public import CFSG.Open.GLBDefs
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Malle.OvergroupTransport

open CFSG.Open

variable {Y : Type} [Group Y] [Finite Y]

theorem le_pRank_of_elemAbelian {p : ℕ} (hp : 1 < p) {H E : Subgroup Y} {k : ℕ}
    (hEH : E ≤ H) (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ k) : k ≤ pRank p H :=
  CFSG.SectionRank.le_pRank hp hEH hE hcard

omit [Finite Y] in
theorem normalizer_le_normalizer_center (T : Subgroup Y) :
    Subgroup.normalizer (T : Set Y) ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (T : Set Y) : Subgroup Y) : Set Y) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro z
  constructor
  · rintro ⟨hzT, hzC⟩
    refine ⟨(hg z).1 hzT, ?_⟩
    replace hzC := Subgroup.mem_centralizer_iff.mp hzC
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    have hh' : g⁻¹ * h * g ∈ T := by
      refine (hg (g⁻¹ * h * g)).2 ?_
      simpa [mul_assoc] using hh
    have h1 := hzC _ hh'
    calc h * (g * z * g⁻¹) = g * ((g⁻¹ * h * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * h := by group
  · rintro ⟨hzT, hzC⟩
    refine ⟨(hg z).2 hzT, ?_⟩
    replace hzC := Subgroup.mem_centralizer_iff.mp hzC
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    have h1 := hzC (g * h * g⁻¹) ((hg h).1 hh)
    calc h * z = g⁻¹ * ((g * h * g⁻¹) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (g * h * g⁻¹)) * g := by rw [h1]
      _ = z * h := by group

theorem normalizer_center_le_weakCore {p : ℕ} {T : Subgroup Y}
    (h2 : 2 ≤ pRank p (T ⊓ Subgroup.centralizer (T : Set Y)))
    (h3 : 3 ≤ pRank p T) :
    Subgroup.normalizer ((T ⊓ Subgroup.centralizer (T : Set Y) : Subgroup Y) : Set Y) ≤
      GLBWeakCore p T := by
  refine le_sSup ⟨T ⊓ Subgroup.centralizer (T : Set Y), inf_le_left, h2, ?_, rfl⟩
  have hT : T ≤ Subgroup.centralizer ((T ⊓ Subgroup.centralizer (T : Set Y) : Subgroup Y) :
      Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.mp hz.2) x hx).symm
  rw [inf_eq_left.mpr hT, sup_eq_right.mpr inf_le_left]
  exact h3

theorem normalizer_le_of_weakCore_le {p : ℕ} {T Y₀ : Subgroup Y}
    (h2 : 2 ≤ pRank p (T ⊓ Subgroup.centralizer (T : Set Y))) (h3 : 3 ≤ pRank p T)
    (hY₀ : GLBWeakCore p T ≤ Y₀) : Subgroup.normalizer (T : Set Y) ≤ Y₀ :=
  (normalizer_le_normalizer_center T).trans
    ((normalizer_center_le_weakCore h2 h3).trans hY₀)

theorem conj_mem_of_normalizes_overgroup {p : ℕ} [Fact p.Prime] {T₀ M K : Subgroup Y}
    (hTM : T₀ ≤ M) (hMK : M ≤ K) (hp : IsPGroup p T₀) (hidx : ¬ p ∣ T₀.relIndex K)
    (hnorm : M ≤ Subgroup.normalizer (T₀ : Set Y)) {g : Y}
    (hg : g ∈ Subgroup.normalizer (M : Set Y)) {x : Y} (hx : x ∈ T₀) : g * x * g⁻¹ ∈ T₀ := by
  have hidx' : ¬ p ∣ (T₀.subgroupOf M).index := by
    intro h
    exact hidx (by
      rw [← Subgroup.relIndex_mul_relIndex T₀ M K hTM hMK]
      exact Dvd.dvd.mul_right h _)
  let P : Sylow p M := (hp.comap_subtype (K := M)).toSylow hidx'
  have hPn : (P : Subgroup M).Normal := by
    change (T₀.subgroupOf M).Normal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hTM).mpr hnorm
  let Q : Subgroup Y := T₀.map (MulAut.conj g).toMonoidHom
  have hQM : Q ≤ M := by
    rintro _ ⟨y, hy, rfl⟩
    have hyM : y ∈ M := hTM hy
    exact ((Subgroup.mem_normalizer_iff.mp hg) y).1 hyM
  have hQp : IsPGroup p Q :=
    hp.of_equiv (Subgroup.equivMapOfInjective T₀ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)
  obtain ⟨S, hS⟩ := (hQp.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M P S
  have hSP : S = P := by
    rw [← hc]
    exact Sylow.smul_eq_of_normal (g := c) (P := P) (h := hPn)
  have hxQ : g * x * g⁻¹ ∈ Q := ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hmem : (⟨g * x * g⁻¹, hQM hxQ⟩ : M) ∈ (S : Subgroup M) :=
    hS (Subgroup.mem_comap.mpr hxQ)
  rw [hSP] at hmem
  exact hmem

theorem ambient_sup_eq_top {K : Subgroup Y} [K.Normal]
    (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (hAut : Nat.card (MulAut K) ∣ 5 * Nat.card K)
    (hrk : ∀ P : Subgroup Y, P ≤ K → IsPGroup 5 ↥P → pRank 5 P ≤ 2)
    (T : Sylow 5 Y) (h3 : 3 ≤ pRank 5 (T : Subgroup Y)) :
    K ⊔ (T : Subgroup Y) = ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hinj : Function.Injective (MulAut.conjNormal : Y →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgC : g ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : Y)) hg
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc k * g = (g * k * g⁻¹) * g := by rw [h1]
        _ = g * k := by group
    rw [hC] at hgC
    exact Subgroup.mem_bot.mp hgC
  have hdvd : K.index ∣ 5 := by
    have h1 : Nat.card Y ∣ 5 * Nat.card K :=
      (Subgroup.card_dvd_of_injective _ hinj).trans hAut
    rw [← Subgroup.card_mul_index K, mul_comm 5] at h1
    exact (Nat.mul_dvd_mul_iff_left Nat.card_pos).mp h1
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
  · exfalso
    have hK : K = ⊤ := Subgroup.index_eq_one.mp h1
    have := hrk (T : Subgroup Y) (hK ▸ le_top) T.isPGroup'
    omega
  · have hT : ¬ (T : Subgroup Y) ≤ K := by
      intro hle
      have := Subgroup.index_dvd_of_le hle
      rw [h5] at this
      exact T.not_dvd_index this
    have hlt : K < K ⊔ (T : Subgroup Y) :=
      lt_of_le_of_ne le_sup_left (fun h => hT (h ▸ le_sup_right))
    have hidx : (K ⊔ (T : Subgroup Y)).index ∣ 5 := by
      have := Subgroup.index_dvd_of_le (le_sup_left : K ≤ K ⊔ (T : Subgroup Y))
      rwa [h5] at this
    rcases (Nat.dvd_prime Nat.prime_five).mp hidx with h | h
    · exact Subgroup.index_eq_one.mp h
    · exfalso
      have := Subgroup.relIndex_mul_index (le_sup_left : K ≤ K ⊔ (T : Subgroup Y))
      rw [h, h5] at this
      have h1 : K.relIndex (K ⊔ (T : Subgroup Y)) = 1 := by omega
      exact hlt.ne (le_antisymm le_sup_left (Subgroup.relIndex_eq_one.mp h1))

end CFSG.HardMathSupport.Malle.OvergroupTransport

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XFusion
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Count
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Qz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gzNo_centralize {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    {x y ρ : G} (hxz : x ∈ Gx z) (hyz : y ∈ Gx z) (hρz : ρ ∈ Gx z) (hyx : y * x = x * y)
    (hy2 : y ^ 2 = 1) (hρx : ρ * x = x * ρ) (hρy : ρ * y = y * ρ) (hρ5 : orderOf ρ = 5)
    (hρQ : ∀ q ∈ Qz z, q * ρ = ρ * q → q = 1 ∨ q = z) (hD : Nat.card ↥(Qz z ⊓ Gx x) = 2 ^ 5)
    (hS : Nat.card ↥(Qz z ⊓ Qz x) = 2 ^ 4) (hS2 : ∀ t ∈ Qz z ⊓ Qz x, t ^ 2 = 1) :
    Qz z ⊓ Gx x ≤ Gx y := by
  let D : Subgroup G := Qz z ⊓ Gx x
  let S : Subgroup G := Qz z ⊓ Qz x
  let E : Subgroup G := D ⊓ Gx y
  have hDE : ∀ e : G, e ∈ E ↔ e ∈ D ∧ e ∈ Gx y := by
    intro e
    show e ∈ D ⊓ Gx y ↔ e ∈ D ∧ e ∈ Gx y
    exact Subgroup.mem_inf
  have hDD : ∀ e : G, e ∈ D ↔ e ∈ Qz z ∧ e ∈ Gx x := by
    intro e
    show e ∈ Qz z ⊓ Gx x ↔ e ∈ Qz z ∧ e ∈ Gx x
    exact Subgroup.mem_inf
  have hSS : ∀ e : G, e ∈ S ↔ e ∈ Qz z ∧ e ∈ Qz x := by
    intro e
    show e ∈ Qz z ⊓ Qz x ↔ e ∈ Qz z ∧ e ∈ Qz x
    exact Subgroup.mem_inf
  have hDval : Nat.card ↥D = 2 ^ 5 := hD
  have hSval : Nat.card ↥S = 2 ^ 4 := hS
  have hS2S : ∀ t ∈ S, t ^ 2 = 1 := fun t ht => hS2 t ht
  have hz2 : z ^ 2 = 1 := by
    rw [← h.orderOf_z]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro hz
    have h2 : orderOf (1 : G) = 2 := by rw [← hz]; exact h.orderOf_z
    rw [orderOf_one] at h2
    norm_num at h2
  have hxz' : z * x = x * z := hxz z (by simp)
  have hyz' : z * y = y * z := hyz z (by simp)
  have hzx : z ∈ Gx x := mem_Gx.2 hxz'.symm
  have hzy : z ∈ Gx y := mem_Gx.2 hyz'.symm
  have hzQz : z ∈ Qz z := self_mem_Qz hz2
  have hzρ : z * ρ = ρ * z := mem_Gx.1 hρz
  have hzE : z ∈ E := (hDE z).2 ⟨(hDD z).2 ⟨hzQz, hzx⟩, hzy⟩
  have hρGx : ρ ∈ Gx x := mem_Gx.2 hρx.symm
  have hρGy : ρ ∈ Gx y := mem_Gx.2 hρy.symm
  have hρE : ∀ s ∈ (E : Set G), ρ * s * ρ⁻¹ ∈ (E : Set G) := by
    intro s hs
    have hsE : s ∈ E := hs
    have hsD : s ∈ D := ((hDE s).1 hsE).1
    have hsGy : s ∈ Gx y := ((hDE s).1 hsE).2
    have hsQz : s ∈ Qz z := ((hDD s).1 hsD).1
    have hsGx : s ∈ Gx x := ((hDD s).1 hsD).2
    refine (hDE (ρ * s * ρ⁻¹)).2 ⟨(hDD (ρ * s * ρ⁻¹)).2 ⟨?_, ?_⟩, ?_⟩
    · exact gzNo_conj_mem_Qz hρz hsQz
    · exact mul_mem (mul_mem hρGx hsGx) (inv_mem hρGx)
    · exact mul_mem (mul_mem hρGy hsGy) (inv_mem hρGy)
  have hiff : ∀ e : G, (e ∈ (E : Set G) ∧ e * ρ = ρ * e) ↔ (e = 1 ∨ e = z) := by
    intro e
    constructor
    · rintro ⟨heE, heρ⟩
      have heD : e ∈ D := ((hDE e).1 heE).1
      have heQz : e ∈ Qz z := ((hDD e).1 heD).1
      exact hρQ e heQz heρ
    · rintro (rfl | rfl)
      · exact ⟨(hDE 1).2 ⟨(hDD 1).2 ⟨(Qz z).one_mem, (Gx x).one_mem⟩, (Gx y).one_mem⟩,
          by rw [one_mul, mul_one]⟩
      · exact ⟨hzE, hzρ⟩
  have hcard_fixed : Nat.card {s : G // s ∈ (E : Set G) ∧ s * ρ = ρ * s} = 2 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    refine (Nat.card_eq_two_iff' (⟨1, Or.inl rfl⟩ : {e : G // e = 1 ∨ e = z})).mpr ?_
    refine ⟨⟨z, Or.inr rfl⟩, ?_, ?_⟩
    · intro hh
      exact hz1 (congrArg Subtype.val hh)
    · intro w hw
      apply Subtype.ext
      rcases w.2 with hh | hh
      · exact absurd (Subtype.ext hh) hw
      · exact hh
  have hmodE : Nat.card ↥E ≡ 2 [MOD 5] := by
    have hc := gzNo_card_modEq_five (K := G) hρ5 (E : Set G) hρE
    rw [hcard_fixed] at hc
    exact hc
  have hmod5 : Nat.card ↥E % 5 = 2 := by
    simpa [Nat.ModEq] using hmodE
  have hyGx : y ∈ Gx x := mem_Gx.2 hyx.symm
  have hyS : ∀ d ∈ S, y * d * y⁻¹ ∈ S := by
    intro d hd
    have hd' : d ∈ Qz z ∧ d ∈ Qz x := (hSS d).1 hd
    exact (hSS (y * d * y⁻¹)).2
      ⟨gzNo_conj_mem_Qz hyz hd'.1, gzNo_conj_mem_Qz hyGx hd'.2⟩
  let c : ℕ := Nat.card {d : G // d ∈ S ∧ d * y = y * d}
  have hSsq : 2 ^ 4 ≤ c ^ 2 := by
    have hle := gzNo_card_le_sq (K := G) S hS2S hy2 hyS
    rw [hSval] at hle
    exact hle
  have hc4 : 4 ≤ c := by
    have h16 : (4 : ℕ) ^ 2 ≤ c ^ 2 := by simpa using hSsq
    by_contra hlt
    push_neg at hlt
    have hc3 : c ≤ 3 := by omega
    have hle : c ^ 2 ≤ 3 ^ 2 := pow_le_pow_left' hc3 2
    norm_num at h16 hle
    linarith
  have hmemE : ∀ d : G, d ∈ S → d * y = y * d → d ∈ E := by
    intro d hdS hcomm
    have hd' : d ∈ Qz z ∧ d ∈ Qz x := (hSS d).1 hdS
    have hdD : d ∈ D := (hDD d).2 ⟨hd'.1, gzNo_Qz_le x hd'.2⟩
    exact (hDE d).2 ⟨hdD, mem_Gx.2 hcomm.symm⟩
  have hinj : c ≤ Nat.card ↥E := by
    show Nat.card {d : G // d ∈ S ∧ d * y = y * d} ≤ Nat.card ↥E
    let f : {d : G // d ∈ S ∧ d * y = y * d} → ↥E :=
      fun d => ⟨d.1, hmemE d.1 d.2.1 d.2.2⟩
    have hf : Function.Injective f := by
      intro u v huv
      exact Subtype.ext (congrArg (fun w : ↥E => (w : G)) huv)
    exact Nat.card_le_card_of_injective f hf
  have hE4 : 4 ≤ Nat.card ↥E := le_trans hc4 hinj
  have hEle : E ≤ D := inf_le_left
  have hEdvd : Nat.card ↥E ∣ 2 ^ 5 := by
    have hdvd := Subgroup.card_dvd_of_le hEle
    rwa [hDval] at hdvd
  obtain ⟨i, hi5, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hEdvd
  have hi_eq : i = 5 := by
    interval_cases i
    · rw [hi] at hmod5
      norm_num at hmod5
    · rw [hi] at hE4
      norm_num at hE4
    · rw [hi] at hmod5
      norm_num at hmod5
    · rw [hi] at hmod5
      norm_num at hmod5
    · rw [hi] at hmod5
      norm_num at hmod5
    · rfl
  have hEcard : Nat.card ↥E = 2 ^ 5 := by
    rw [hi, hi_eq]
  have hED : E = D := by
    refine Subgroup.eq_of_le_of_card_ge hEle ?_
    rw [hDval, hEcard]
  show D ≤ Gx y
  rw [← hED]
  exact inf_le_right

end CFSG.EvenSporadicStandard.HNRecog.Section3

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6P6a
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Basic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem y6_a6_no_order6 : ∀ σ ∈ alternatingGroup (Fin 6), orderOf σ ≠ 6 := fun σ hσ => by
  simpa using CFSG.ComponentClassification.CatFC.alt6_no_order_six ⟨σ, hσ⟩

theorem y6_count {G : Type} [Group G] [Finite G] (X C Y K C1 : Subgroup G)
    (ψ : ↥X →* Equiv.Perm (Fin 6)) (hker : ψ.ker = K.subgroupOf X)
    (hCX : C ≤ X) (hYC : Y ≤ C) (hKC : K ≤ C) (hC1K : C1 ≤ K) (hC1Y : C1 ≤ Y)
    (hKY : K ⊓ Y = C1) (hXC : Nat.card ↥X = 10 * Nat.card ↥C)
    (hCY : Nat.card ↥C ≤ 2 * Nat.card ↥Y) {m : ℕ} (hm : m = 18 ∨ m = 36)
    (hY : Nat.card ↥Y = m * Nat.card ↥C1)
    (h6 : m = 36 → ∃ y : ↥X, (y : G) ∈ Y ∧ orderOf (ψ y) = 6) :
    Nat.card ↥C = 2 * Nat.card ↥Y ∧ K = C1 ∧ alternatingGroup (Fin 6) ≤ ψ.range ∧
      Nat.card ↥ψ.range = 20 * m := by
  classical
  have hKxcard : Nat.card ↥(K.subgroupOf X) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hKC.trans hCX)).toEquiv
  have hXR : Nat.card ↥K * Nat.card ↥ψ.range = 10 * Nat.card ↥C := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hker, hKxcard, hXC] at h
    exact h
  set Kx : Subgroup ↥X := K.subgroupOf X with hKx
  set Yx : Subgroup ↥X := Y.subgroupOf X with hYx
  set Cx : Subgroup ↥X := C.subgroupOf X with hCx
  set C1x : Subgroup ↥X := C1.subgroupOf X with hC1x
  haveI hKxNormal : Kx.Normal := by rw [← hker]; infer_instance
  have hKxcard' : Nat.card ↥Kx = Nat.card ↥K := by rw [hKx]; exact hKxcard
  have hYxcard : Nat.card ↥Yx = Nat.card ↥Y := by
    rw [hYx]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hYC.trans hCX)).toEquiv
  have hC1xcard : Nat.card ↥C1x = Nat.card ↥C1 := by
    rw [hC1x]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (hC1Y.trans (hYC.trans hCX))).toEquiv
  have hCxcard : Nat.card ↥Cx = Nat.card ↥C := by
    rw [hCx]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv
  have hsup_le : Kx ⊔ Yx ≤ Cx := by
    rw [hKx, hYx, hCx]
    exact sup_le (Subgroup.subgroupOf_mono X hKC) (Subgroup.subgroupOf_mono X hYC)
  have hJdvdA : Nat.card ↥(Kx ⊔ Yx) ∣ Nat.card ↥C := by
    have h := Subgroup.card_dvd_of_le hsup_le
    rwa [hCxcard] at h
  have hinf2 : Kx ⊓ Yx = C1x := by
    rw [hKx, hYx, hC1x]
    change K.comap X.subtype ⊓ Y.comap X.subtype = C1.comap X.subtype
    rw [← Subgroup.comap_inf K Y X.subtype, hKY]
  have hrel1 : Kx.relIndex (Kx ⊔ Yx) * Nat.card ↥(Kx ⊓ (Kx ⊔ Yx)) =
      Nat.card ↥(Kx ⊔ Yx) := Subgroup.relIndex_mul_card Kx (Kx ⊔ Yx)
  have hinf1 : Kx ⊓ (Kx ⊔ Yx) = Kx := inf_eq_left.mpr le_sup_left
  have hrel3 : Kx.relIndex (Kx ⊔ Yx) = Kx.relIndex Yx := by
    rw [sup_comm]
    exact Subgroup.relIndex_sup_right (H := Yx) (K := Kx)
  have hJcard : Nat.card ↥(Kx ⊔ Yx) = Kx.relIndex Yx * Nat.card ↥Kx := by
    rw [← hrel1, hinf1, hrel3]
  have hrel2 : Kx.relIndex Yx * Nat.card ↥(Kx ⊓ Yx) = Nat.card ↥Yx :=
    Subgroup.relIndex_mul_card Kx Yx
  have hYcard : Nat.card ↥Yx = Kx.relIndex Yx * Nat.card ↥C1x := by
    rw [← hrel2, hinf2]
  have hJmul' : Nat.card ↥(Kx ⊔ Yx) * Nat.card ↥C1x =
      Nat.card ↥Kx * Nat.card ↥Yx := by
    rw [hJcard, hYcard]; ring
  have hJmul : Nat.card ↥(Kx ⊔ Yx) * Nat.card ↥C1 = Nat.card ↥K * Nat.card ↥Y := by
    rw [← hC1xcard, ← hKxcard', ← hYxcard]
    exact hJmul'
  have hJeq : Nat.card ↥(Kx ⊔ Yx) = m * Nat.card ↥K := by
    have h := hJmul
    rw [hY] at h
    have h' : Nat.card ↥(Kx ⊔ Yx) * Nat.card ↥C1 =
        (m * Nat.card ↥K) * Nat.card ↥C1 := by
      rw [h]; ring
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥C1)) h'
  obtain ⟨r, hr⟩ := Subgroup.card_dvd_of_le hYC
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hC1K
  have hrpos : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h, mul_zero] at hr
      have := Nat.card_pos (α := ↥C)
      omega
    · exact h
  have hrle : r ≤ 2 := by
    have h : Nat.card ↥Y * r ≤ Nat.card ↥Y * 2 := by
      rw [← hr]
      calc Nat.card ↥C ≤ 2 * Nat.card ↥Y := hCY
        _ = Nat.card ↥Y * 2 := by ring
    exact Nat.le_of_mul_le_mul_left h (Nat.card_pos (α := ↥Y))
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      have := Nat.card_pos (α := ↥K)
      omega
    · exact h
  have hmpos : 0 < m := by rcases hm with h | h <;> omega
  have hkpos0 : 0 < k := by omega
  have hkdvd : k ∣ r := by
    have h1 : m * Nat.card ↥K ∣ Nat.card ↥Y * r := by
      rw [← hJeq, ← hr]
      exact hJdvdA
    refine Nat.dvd_of_mul_dvd_mul_left
      (Nat.mul_pos hmpos (Nat.card_pos (α := ↥C1))) ?_
    have h2 := h1
    rw [hk, hY, ← mul_assoc] at h2
    exact h2
  obtain ⟨s, hs⟩ := hkdvd
  have hspos : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, mul_zero] at hs
      omega
    · exact h
  have hsle : s ≤ 2 := by
    have h1 : s ≤ k * s := by simpa using Nat.mul_le_mul_right s hkpos
    omega
  have hR : Nat.card ↥ψ.range = 10 * m * s := by
    have h := hXR
    rw [hk, hr, hs, hY] at h
    have h' : (Nat.card ↥C1 * k) * Nat.card ↥ψ.range =
        (Nat.card ↥C1 * k) * (10 * m * s) := by
      rw [h]; ring
    exact Nat.mul_left_cancel
      (Nat.mul_pos (Nat.card_pos (α := ↥C1)) hkpos0) h'
  have hmge : 18 ≤ m := by rcases hm with h | h <;> omega
  have hRge : 180 ≤ Nat.card ↥ψ.range := by
    rw [hR]
    nlinarith [hmge, hspos]
  have hA6le : alternatingGroup (Fin 6) ≤ ψ.range := y6_index_le_four hRge
  have hA6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have h360dvd : 360 ∣ Nat.card ↥ψ.range := by
    have h := Subgroup.card_dvd_of_le hA6le
    rwa [hA6card] at h
  have hs2 : s = 2 := by
    rcases hm with hm18 | hm36
    · have h360 : 360 ∣ 180 * s := by
        have h := h360dvd
        rw [hR, hm18] at h
        have h10 : (10 : ℕ) * 18 * s = 180 * s := by ring
        rwa [h10] at h
      have h2s : 2 ∣ s :=
        Nat.dvd_of_mul_dvd_mul_left (show 0 < 180 by norm_num) (by simpa using h360)
      obtain ⟨t, ht⟩ := h2s
      omega
    · have hR36 : Nat.card ↥ψ.range = 360 * s := by rw [hR, hm36]; try ring
      rcases (show s = 1 ∨ s = 2 by omega) with hs1 | hs2
      · exfalso
        have hR360 : Nat.card ↥ψ.range = 360 := by rw [hR36, hs1]; try ring
        have hAeq : alternatingGroup (Fin 6) = ψ.range := by
          refine Subgroup.eq_of_le_of_card_ge hA6le ?_
          rw [hR360, hA6card]
        obtain ⟨y, _hyY, hyord⟩ := h6 hm36
        have hmem : ψ y ∈ alternatingGroup (Fin 6) := by
          rw [hAeq]
          exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
        exact y6_a6_no_order6 (ψ y) hmem hyord
      · exact hs2
  have hk1 : k = 1 := by
    have hks : k * s ≤ 2 := by rw [← hs]; exact hrle
    rw [hs2] at hks
    omega
  have hr2 : r = 2 := by rw [hs, hs2, hk1]; try ring
  refine ⟨?_, ?_, hA6le, ?_⟩
  · rw [hr, hr2]; ring
  · have hKeq : Nat.card ↥K = Nat.card ↥C1 := by rw [hk, hk1, mul_one]
    exact (Subgroup.eq_of_le_of_card_ge hC1K (le_of_eq hKeq)).symm
  · rw [hR, hs2]; ring

theorem y6_orbit_le {G : Type} [Group G] [Finite G] {N H0 : Subgroup G} {t : G} {S : Set G}
    (hH0 : H0 = N ⊓ centralizer ({t} : Set G)) (hS : ∀ n ∈ N, n * t * n⁻¹ ∈ S) :
    Nat.card ↥N ≤ Nat.card ↥S * Nat.card ↥H0 := by
  classical
  have hmem : ∀ n : ↥N, (n : G) * t * (n : G)⁻¹ ∈ S := fun n => hS n n.2
  let f : ↥N → ↥S := fun n => ⟨(n : G) * t * (n : G)⁻¹, hmem n⟩
  let sec : ↥S → ↥N := fun s => if h : ∃ n : ↥N, f n = s then Classical.choose h else 1
  have hsec : ∀ s : ↥S, (∃ n : ↥N, f n = s) → f (sec s) = s := by
    intro s h
    have h1 : sec s = Classical.choose h := by
      simp only [sec]
      rw [dif_pos h]
    rw [h1]
    exact Classical.choose_spec h
  have hkey : ∀ n : ↥N, ((sec (f n) : ↥N) : G)⁻¹ * (n : G) ∈ H0 := by
    intro n
    have h1 : f (sec (f n)) = f n := hsec (f n) ⟨n, rfl⟩
    have h2 : ((sec (f n) : ↥N) : G) * t * ((sec (f n) : ↥N) : G)⁻¹ =
        (n : G) * t * (n : G)⁻¹ := by
      have := congrArg (fun x : ↥S => (x : G)) h1
      simpa [f] using this
    rw [hH0]
    refine ⟨?_, ?_⟩
    · exact N.mul_mem (N.inv_mem (sec (f n)).2) n.2
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst h
      have h3 : t * (((sec (f n) : ↥N) : G)⁻¹ * (n : G)) =
          (((sec (f n) : ↥N) : G)⁻¹ * (n : G)) * t := by
        have h4 := congrArg (fun x => ((sec (f n) : ↥N) : G)⁻¹ * x * (n : G)) h2
        simpa [mul_assoc] using h4
      exact h3
  let φ : ↥N → ↥S × ↥H0 := fun n =>
    (f n, ⟨((sec (f n) : ↥N) : G)⁻¹ * (n : G), hkey n⟩)
  have hφinj : Function.Injective φ := by
    intro n n' h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨hf, hg⟩ := h
    have hsec_eq : sec (f n) = sec (f n') := by rw [hf]
    have hg' : ((sec (f n) : ↥N) : G)⁻¹ * (n : G) =
        ((sec (f n') : ↥N) : G)⁻¹ * (n' : G) := by
      have := congrArg (fun x : ↥H0 => (x : G)) hg
      simpa using this
    have hAB : ((sec (f n) : ↥N) : G) = ((sec (f n') : ↥N) : G) :=
      congrArg (fun x : ↥N => (x : G)) hsec_eq
    have hg'' : ((sec (f n') : ↥N) : G)⁻¹ * (n : G) =
        ((sec (f n') : ↥N) : G)⁻¹ * (n' : G) := by
      have := hg'
      rw [hAB] at this
      exact this
    apply Subtype.ext
    calc (n : G) = ((sec (f n) : ↥N) : G) *
          (((sec (f n) : ↥N) : G)⁻¹ * (n : G)) := by group
      _ = ((sec (f n') : ↥N) : G) *
          (((sec (f n') : ↥N) : G)⁻¹ * (n' : G)) := by rw [hsec_eq, hg'']
      _ = (n' : G) := by group
  have hle : Nat.card ↥N ≤ Nat.card (↥S × ↥H0) :=
    Nat.card_le_card_of_injective φ hφinj
  simpa only [Nat.card_prod] using hle

theorem y6_normal_eq {G : Type} [Group G] [Finite G] {N X H0 : Subgroup G} {t : G} {S : Set G}
    (hXN : X ≤ N) (hH0X : H0 ≤ X) (hH0 : H0 = N ⊓ centralizer ({t} : Set G))
    (hX : Nat.card ↥X = 40 * Nat.card ↥H0) (hS : ∀ n ∈ N, n * t * n⁻¹ ∈ S)
    (hSc : Nat.card ↥S ≤ 52) : X = N := by
  have hNle : Nat.card ↥N ≤ Nat.card ↥S * Nat.card ↥H0 := y6_orbit_le hH0 hS
  have hNle52 : Nat.card ↥N ≤ 52 * Nat.card ↥H0 :=
    hNle.trans (Nat.mul_le_mul_right _ hSc)
  have hdvd : Nat.card ↥X ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hXN
  obtain ⟨q, hq⟩ := hdvd
  have hH0pos : 0 < Nat.card ↥H0 := Nat.card_pos
  have hqle : q ≤ 1 := by
    rw [hq, hX] at hNle52
    have h : 40 * q * Nat.card ↥H0 ≤ 52 * Nat.card ↥H0 := by nlinarith [hNle52]
    have := Nat.le_of_mul_le_mul_right h hH0pos
    omega
  have hqge : 1 ≤ q := by
    have hXleN : Nat.card ↥X ≤ Nat.card ↥N :=
      Nat.le_of_dvd (Nat.card_pos (α := ↥N)) (Subgroup.card_dvd_of_le hXN)
    have h' : Nat.card ↥X * 1 ≤ Nat.card ↥X * q := by
      rw [hq] at hXleN
      simpa using hXleN
    exact Nat.le_of_mul_le_mul_left h' (Nat.card_pos (α := ↥X))
  have hq1 : q = 1 := le_antisymm hqle hqge
  have hNX : Nat.card ↥N = Nat.card ↥X := by rw [hq, hq1, mul_one]
  exact Subgroup.eq_of_le_of_card_ge hXN (le_of_eq hNX)

end CFSG.OddStandard.HigherRank.YamadaG23

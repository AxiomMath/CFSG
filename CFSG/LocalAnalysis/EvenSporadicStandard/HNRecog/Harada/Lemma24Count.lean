module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24CountAlt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24CountPSp

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

private lemma map_centralizer_singleton {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (e : G →* H) =
      Subgroup.centralizer ({e x} : Set H) := by
  refine le_antisymm ?_ ?_
  · simpa [Set.image_singleton] using
      Subgroup.map_centralizer_le_centralizer_image ({x} : Set G) (e : G →* H)
  · intro y hy
    rw [Subgroup.mem_map]
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    have h := congrArg (⇑e.symm) hy
    simpa using h

private lemma card_centralizer_singleton_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({e x} : Set H)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  rw [← map_centralizer_singleton e x]
  exact Subgroup.card_map_of_injective e.injective

theorem no_X0_of_conclusion {X : Type} [Group X] [Finite X]
    (hconc : Nonempty (X ≃* alternatingGroup (Fin 8)) ∨ Nonempty (X ≃* alternatingGroup (Fin 9)) ∨
      Nat.card X = 960 ∨ Nat.card X = 1344 ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧
        CFSG.Blueprint.LieModel X .PSp 2 p f)
    (hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    {x : X} (hx : x ^ 2 = 1) (hx1 : x ≠ 1) (hC : Nat.card (centralizer ({x} : Set X)) = 480)
    {M : Subgroup X} (hMC : M ≤ centralizer ({x} : Set X)) (hMp : ⁅M, M⁆ = M)
    (hM : Nat.card M = 60) {I : Set X} (hIcard : I.ncard = 46)
    (hI : ∀ c ∈ I, c ∈ centralizer ({x} : Set X) ∧ c ^ 2 = 1 ∧ c ≠ 1 ∧
      Nat.card (centralizer ({c} : Set X)) = 480)
    (hJ : ∀ c ∈ centralizer ({x} : Set X), c ^ 2 = 1 → c ≠ 1 → IsConj x c → c ∈ I) : False := by
  classical
  rcases hconc with hA8 | hA9 | h960 | h1344 | hPSp
  ·
    obtain ⟨e⟩ := hA8
    have hx8 : (e x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
    have hx81 : e x ≠ 1 := fun h => hx1 (e.injective (by rw [h, map_one]))
    have hC8 : Nat.card (Subgroup.centralizer ({e x} : Set (alternatingGroup (Fin 8)))) = 480 := by
      rw [card_centralizer_singleton_mulEquiv e x, hC]
    exact not_card_centralizer_A8 (e x) hx8 hx81 hC8
  ·
    obtain ⟨e⟩ := hA9
    set y : alternatingGroup (Fin 9) := e x with hy
    have hy2 : y ^ 2 = 1 := by rw [hy, ← map_pow, hx, map_one]
    have hy1 : y ≠ 1 := by
      rw [hy]
      intro h
      exact hx1 (e.injective (by rw [h, map_one]))
    have hyC : Nat.card (Subgroup.centralizer ({y} : Set (alternatingGroup (Fin 9)))) = 480 := by
      rw [hy, card_centralizer_singleton_mulEquiv e x, hC]
    set S : Set (alternatingGroup (Fin 9)) :=
      {c : alternatingGroup (Fin 9) |
        c ∈ Subgroup.centralizer ({y} : Set (alternatingGroup (Fin 9))) ∧ c ^ 2 = 1 ∧ c ≠ 1 ∧
          Nat.card (Subgroup.centralizer ({c} : Set (alternatingGroup (Fin 9)))) = 480} with hS
    have himage : e '' I ⊆ S := by
      rw [hS]
      rintro c ⟨d, hdI, rfl⟩
      obtain ⟨hdC, hd2, hd1, hdK⟩ := hI d hdI
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hdC ⊢
        rw [hy]
        calc e d * e x = e (d * x) := by rw [map_mul]
          _ = e (x * d) := by rw [hdC]
          _ = e x * e d := by rw [map_mul]
      · rw [← map_pow, hd2, map_one]
      · intro h
        exact hd1 (e.injective (by rw [h, map_one]))
      · rw [card_centralizer_singleton_mulEquiv e d, hdK]
    have himgcard : (e '' I).ncard = 46 := by
      rw [Set.ncard_image_of_injective I e.injective, hIcard]
    have hle : (e '' I).ncard ≤ S.ncard := Set.ncard_le_ncard himage (Set.toFinite S)
    have h38 : S.ncard ≤ 38 := by
      rw [hS]
      exact card_involutions_A9_le y hy2 hy1 hyC
    omega
  ·
    set C : Subgroup X := Subgroup.centralizer ({x} : Set X) with hCdef
    have hCcard : Nat.card C = 480 := by rw [hCdef]; exact hC
    have hidx : C.index = 2 := by
      have h := C.index_mul_card
      rw [hCcard, h960] at h
      omega
    haveI : C.Normal := Subgroup.normal_of_index_eq_two hidx
    have hcard : Nat.card (X ⧸ C) = 2 := by
      rw [← Subgroup.index_eq_card, hidx]
    haveI : IsCyclic (X ⧸ C) := isCyclic_of_prime_card (p := 2) hcard
    have hcomm : IsMulCommutative (X ⧸ C) := inferInstance
    have hle : _root_.commutator X ≤ C :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
    have htop : (⊤ : Subgroup X) ≤ C := by
      rw [← hperf]
      simpa [_root_.commutator_def] using hle
    have hCtop : C = ⊤ := top_le_iff.mp htop
    rw [hCtop, Subgroup.card_top, h960] at hCcard
    omega
  ·
    have hdvd : Nat.card (Subgroup.centralizer ({x} : Set X)) ∣ Nat.card X :=
      Subgroup.card_subgroup_dvd_card _
    rw [hC, h1344] at hdvd
    exact absurd hdvd (by norm_num)
  ·
    obtain ⟨p, f, hp, hp2, hf, hmod, hX⟩ := hPSp
    have h47 : 47 ≤ Set.ncard {c : X | c ∈ Subgroup.centralizer ({x} : Set X) ∧
        c ^ 2 = 1 ∧ c ≠ 1 ∧ IsConj x c} :=
      psp_conj_count hp hp2 hf hX hx hx1 hC hMC hMp hM
    have hsub : {c : X | c ∈ Subgroup.centralizer ({x} : Set X) ∧
        c ^ 2 = 1 ∧ c ≠ 1 ∧ IsConj x c} ⊆ I := by
      intro c hc
      exact hJ c hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    have hle : Set.ncard {c : X | c ∈ Subgroup.centralizer ({x} : Set X) ∧
        c ^ 2 = 1 ∧ c ≠ 1 ∧ IsConj x c} ≤ I.ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite I)
    rw [hIcard] at hle
    omega

end CFSG.EvenSporadicStandard.HNRecog.Harada

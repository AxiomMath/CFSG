module

public import CFSG.HardMathSupport.Dickson.I271.Support.AmbBase
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAltDiv
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAlt
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MCover

public section

namespace CFSG.HardMathSupport.Dickson.I271.Amb

open Equiv Equiv.Perm MulAction CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Dickson.I271 GL83 GL83.CompFam GL83.PiGen

section AltCore

variable {X : Type} [Group X] [Finite X]

theorem altCore {p : ℕ} {K B : Subgroup X} {n : ℕ} (hp : p.Prime)
    (hpodd : p ≠ 2) (hcore : GLAPPrimeCore p X = ⊥) (hcomp : GLAPComponent p ⊤ K)
    (hscp : IsSCp p ⊤ B) (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (hpn : p ∣ n) (h73 : ¬ (p = 3 ∧ n = 7))
    (e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n)) : IsStronglyBalancedIn p B K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hcore hcomp
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  have hOK : GLAPPrimeCore p ↥K = ⊥ := i271h_primeCore_eq_bot hcore hcomp
  have hZ : Subgroup.center ↥K = ⊥ := i271h_center_eq_bot_of_ne_six hp hpodd hOK hn e hn6 h73
  have hAsc := i271h_map_permHom_isSCp hp hpodd hscp hBN hZ hn hn6 e
  set N := Subgroup.normalizer (K : Set X) with hN
  set π := permHom (le_refl N) hn hn6 e with hπ
  have hdvdn : p ∣ Fintype.card (Fin n) := by simpa using hpn
  intro S hSN hcop hBS
  have hBNB : B ⊓ N = B := inf_of_le_left hBN
  rw [hBNB] at hBS
  set T : Subgroup (Perm (Fin n)) := (S.subgroupOf N).map π with hT
  set A : Subgroup (Perm (Fin n)) := (B.subgroupOf N).map π with hA
  have hTcop : Nat.Coprime p (Nat.card T) := by
    have hcard : Nat.card (S.subgroupOf N) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
    refine Nat.Coprime.coprime_dvd_right ?_ (hcard ▸ hcop)
    exact Subgroup.card_map_dvd _ _
  have hAT : A ≤ Subgroup.normalizer (T : Set (Perm (Fin n))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxn : x ∈ Subgroup.normalizer ((S.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have := Subgroup.mem_normalizer_iff.1 (hBS (Subgroup.mem_subgroupOf.1 hx)) (h : X)
      simpa [Subgroup.mem_subgroupOf] using this
    exact Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hxn)
  have hTbot : T = ⊥ := i271h_perm_coprime_normalized_eq_bot hAsc hdvdn hTcop hAT
  intro s hs
  have hsN : s ∈ N := hSN hs
  have h1 : π ⟨s, hsN⟩ ∈ T := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hs)
  rw [hTbot, Subgroup.mem_bot] at h1
  have h2 := (permHom_eq_one_iff (le_refl N) hn hn6 e ⟨s, hsN⟩).1 h1
  exact Subgroup.mem_centralizer_iff.2 fun x hx => (h2 ⟨x, hx⟩).symm

end AltCore

section A6

variable {X : Type} [Group X] [Finite X]

theorem alt6_pow_nine : ∀ g : alternatingGroup (Fin 6), g ^ 9 = 1 → g ^ 3 = 1 := by decide +kernel

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem exists_sylow_alt6 :
    ∃ P : Sylow 3 (alternatingGroup (Fin 6)),
      IsElemAbelian 3 (P : Subgroup (alternatingGroup (Fin 6))) ∧
        Nat.card (P : Subgroup (alternatingGroup (Fin 6))) = 9 := by
  haveI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 (alternatingGroup (Fin 6))) := inferInstance
  have hcard : Nat.card (P : Subgroup (alternatingGroup (Fin 6))) = 9 := by
    rw [Sylow.card_eq_multiplicity, card_alt6, show (360 : ℕ).factorization 3 = 2 by decide +kernel]
    norm_num
  refine ⟨P, ⟨?_, ?_⟩, hcard⟩
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hcard]; norm_num)
  · intro g hg
    have h9 : g ^ 9 = 1 := by
      have hd : orderOf g ∣ 9 := by
        have := Subgroup.orderOf_dvd_natCard (P : Subgroup (alternatingGroup (Fin 6))) hg
        rwa [hcard] at this
      exact orderOf_dvd_iff_pow_eq_one.1 hd
    exact alt6_pow_nine g h9

theorem alt6_center_cases {K : Type} [Group K] [Finite K]
    [Group.IsPerfect K] (hZp : IsPGroup 3 (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) :
    Subgroup.center K = ⊥ ∨ Nat.card (Subgroup.center K) = 3 := by
  haveI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  by_cases hZ : Subgroup.center K = ⊥
  · exact Or.inl hZ
  · right
    have h := CFSG.AGLEmbedding.card_center_dvd_card_hopfMultiplier e
    rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput 6 (by norm_num)).2] at h
    have h6 : Nat.card (Subgroup.center K) ∣ 6 := by simpa using h
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hZ (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
    have hk1 : k ≤ 1 := by
      by_contra hlt
      have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      rw [← hk] at h9
      have := h9.trans h6
      norm_num at this
    obtain rfl : k = 1 := by omega
    simpa using hk

theorem a6Case {K B : Subgroup X}
    (hcore : GLAPPrimeCore 3 X = ⊥) (hcomp : GLAPComponent 3 ⊤ K) (hscp : IsSCp 3 ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 6)) :
    IsStronglyBalancedIn 3 B K ∨
      ((commutator ↥K = ⊤ ∧ Nat.card (Subgroup.center ↥K) = 3 ∧
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 6))) ∧
          autOrderIn B K = 3) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hBel : IsElemAbelian 3 B := hscp.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hcore hcomp
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  have hOK : GLAPPrimeCore 3 ↥K = ⊥ := i271h_primeCore_eq_bot hcore hcomp
  have hZp : IsPGroup 3 (Subgroup.center ↥K) := isPGroup_center hp hOK
  have h3K : 3 ∣ Nat.card K := i116e_dvd_card hp hcore hcomp
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn hp hBel hBN
  have hdvd : autOrderIn B K ∣ 1440 := by
    have := i271h_autOrderIn_dvd_card_mulAut hBN hq.1
    rwa [Nat.card_congr (MulAut.congr e).toEquiv,
      CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6] at this
  have hr2 : r ≤ 2 := by
    by_contra hlt
    have h27 : 3 ^ 3 ∣ 3 ^ r := pow_dvd_pow 3 (by omega)
    rw [← hr] at h27
    have := h27.trans hdvd
    norm_num at this
  have hone : autOrderIn B K = 1 ↔ B ≤ Subgroup.centralizer (K : Set X) := by
    unfold autOrderIn
    rw [inf_of_le_left hBN, Subgroup.relIndex_eq_one]
  by_cases hr' : r = 2
  · left
    subst hr'
    exact isStronglyBalancedIn_of_autBalanced hBel hq.1 e (by rw [hr]) i271AutBalanceAltSix_holds
  · have hr1 : r ≤ 1 := by omega
    rcases alt6_center_cases hZp e with hZ | hZ3
    ·
      exfalso
      obtain ⟨x, hxB, hxK, hx1, hxp⟩ := exists_mem_inf_of_isSCp hp hscp hBN h3K
      have hxC : x ∉ Subgroup.centralizer (K : Set X) := fun h =>
        hx1 (eq_one_of_mem_centralizer hZ hxK h)
      have hne1 : autOrderIn B K ≠ 1 := fun h => hxC ((hone.1 h) hxB)
      have hcard : autOrderIn B K = 3 := by
        rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
        · exact (hne1 (by simpa using hr)).elim
        · simpa using hr
      let eK : ↥K ≃* alternatingGroup (Fin 6) := mulEquivOfCenterBot hZ e
      obtain ⟨P₀, hE, hP9⟩ := exists_sylow_alt6
      have hx₁p : eK ⟨x, hxK⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨x, hxK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hxp)
        rw [this, map_one]
      have hx₁1 : eK ⟨x, hxK⟩ ≠ 1 := by
        intro h
        apply hx1
        have := eK.injective (h.trans (map_one eK).symm)
        exact congrArg Subtype.val this
      obtain ⟨y₁, hy₁p, hy₁n, hy₁c⟩ := exists_comm_outside_zpowers hp hE (by rw [hP9]; norm_num)
        (le_refl _) (Subgroup.le_normalizer) hx₁p hx₁1
      set y₀ : ↥K := eK.symm y₁ with hy₀
      refine cyclic_contra hp hscp hBN hZ hcard hxB hxK hx1 (y := (y₀ : X)) y₀.2 ?_ ?_ ?_
      · have : y₀ ^ 3 = 1 := by
          apply eK.injective
          rw [map_pow, hy₀, MulEquiv.apply_symm_apply, map_one]
          exact hy₁p
        simpa using congrArg Subtype.val this
      · have : y₀ * ⟨x, hxK⟩ = ⟨x, hxK⟩ * y₀ := by
          apply eK.injective
          rw [map_mul, map_mul, hy₀, MulEquiv.apply_symm_apply]
          exact hy₁c
        exact congrArg Subtype.val this
      · intro hmem
        apply hy₁n
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
        refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
        have : y₀ = ⟨x, hxK⟩ ^ n := Subtype.ext (by simpa using hn.symm)
        rw [← map_zpow, ← this, hy₀, MulEquiv.apply_symm_apply]
    ·
      have hHat : commutator ↥K = ⊤ ∧ Nat.card (Subgroup.center ↥K) = 3 ∧
          Nonempty (↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 6)) := ⟨hq.1, hZ3, ⟨e⟩⟩
      rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
      · exfalso
        have hBC : B ≤ Subgroup.centralizer (K : Set X) := hone.1 (by simpa using hr)
        obtain ⟨R⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
        obtain ⟨hR27, -, hR3⟩ := t112m_sylow_hatSix hHat R
        have hZR : Subgroup.center ↥K ≤ (R : Subgroup ↥K) := hZp.le_sylow_of_normal R
        have hnle : ¬ (R : Subgroup ↥K) ≤ Subgroup.center ↥K := by
          intro hle
          have := Subgroup.card_le_of_le hle
          rw [hR27, hZ3] at this
          omega
        obtain ⟨y₀, hy₀R, hy₀Z⟩ := Set.not_subset.1 hnle
        have hyK : (y₀ : X) ∈ K := y₀.2
        have hyp : (y₀ : X) ^ 3 = 1 := by simpa using congrArg Subtype.val (hR3 y₀ hy₀R)
        have hyB : (y₀ : X) ∈ B := mem_of_comm_of_isSCp hscp hyp fun b hb =>
          (Subgroup.mem_centralizer_iff.1 (hBC hb) (y₀ : X) hyK).symm
        apply hy₀Z
        rw [SetLike.mem_coe, Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hBC hyB) (g : X) g.2)
      · right
        exact ⟨hHat, by simpa using hr⟩

end A6

end CFSG.HardMathSupport.Dickson.I271.Amb

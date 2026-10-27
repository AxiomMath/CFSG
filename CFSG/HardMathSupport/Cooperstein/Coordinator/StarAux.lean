module

public import Mathlib.GroupTheory.IsPerfect
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux

open Subgroup
open scoped commutatorElement

section Commutators

variable {Y : Type*} [Group Y]

theorem le_centralizer_of_commutator_commutator_eq_bot {K W : Subgroup Y}
    (hK : ⁅K, K⁆ = K) (hW : ⁅⁅W, K⁆, K⁆ = ⊥) : W ≤ Subgroup.centralizer (K : Set Y) := by
  have h1 : ⁅⁅K, W⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm K W]; exact hW
  have h3 : ⁅⁅K, K⁆, W⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 hW
  rw [hK, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
  exact Subgroup.le_centralizer_iff.mpr h3

theorem normal_le_center_or_eq_top {Q : Type*} [Group Q] (hperf : commutator Q = ⊤)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (N : Subgroup Q) (hN : N.Normal) :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  let qt := QuotientGroup.mk' (Subgroup.center Q)
  have hnormal : (N.map qt).Normal := Subgroup.Normal.map hN qt (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hkernel : N ≤ qt.ker := N.map_eq_bot_iff.mp hbot
    change N ≤ (QuotientGroup.mk' (Subgroup.center Q)).ker at hkernel
    simpa only [QuotientGroup.ker_mk'] using hkernel
  · right
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq qt N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hperf] at hderived
    exact top_unique hderived

end Commutators

section CentralQuotient

variable {A B C : Type*} [Group A] [Group B] [Group C]

theorem exists_factor (π : A →* B) (hπ : Function.Surjective π) (φ : A →* C)
    (hk : π.ker ≤ φ.ker) : ∃ h : B →* C, ∀ a, h (π a) = φ a :=
  ⟨π.liftOfSurjective hπ ⟨φ, hk⟩, fun a => π.liftOfRightInverse_comp_apply _ _ ⟨φ, hk⟩ a⟩

theorem map_center_eq_center (h : B →* C) (hs : Function.Surjective h)
    (hker : h.ker ≤ Subgroup.center B) (hperf : ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = ⊤) :
    (Subgroup.center B).map h = Subgroup.center C := by
  apply le_antisymm
  · rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨b', rfl⟩ := hs c
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hb b']
  · intro c hc
    obtain ⟨b, rfl⟩ := hs c
    refine ⟨b, ?_, rfl⟩
    have hW : ⁅⁅(Subgroup.center C).comap h, (⊤ : Subgroup B)⁆, (⊤ : Subgroup B)⁆ = ⊥ := by
      have h1 : ⁅(Subgroup.center C).comap h, (⊤ : Subgroup B)⁆ ≤ h.ker := by
        rw [Subgroup.commutator_le]
        intro x hx y _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hx (h y)).symm
      refine le_bot_iff.mp ?_
      calc ⁅⁅(Subgroup.center C).comap h, (⊤ : Subgroup B)⁆, (⊤ : Subgroup B)⁆
          ≤ ⁅Subgroup.center B, (⊤ : Subgroup B)⁆ := Subgroup.commutator_mono (h1.trans hker) le_rfl
        _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (by
            intro z hz g _
            exact (Subgroup.mem_center_iff.mp hz g))
    have hle := le_centralizer_of_commutator_commutator_eq_bot hperf hW
    have hb : b ∈ (Subgroup.center C).comap h := hc
    have := hle hb
    show b ∈ Subgroup.center B
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_iff.mp this g (Subgroup.mem_top g)

theorem exists_central_factor (π : A →* B) (hπ : Function.Surjective π) (φ : A →* C)
    (hφ : Function.Surjective φ) (hk : π.ker ≤ φ.ker)
    (hcen : ∀ a ∈ φ.ker, π a ∈ Subgroup.center B) :
    ∃ h : B →* C, Function.Surjective h ∧ h.ker ≤ Subgroup.center B ∧ ∀ a, h (π a) = φ a := by
  obtain ⟨h, hh⟩ := exists_factor π hπ φ hk
  refine ⟨h, ?_, ?_, hh⟩
  · intro c
    obtain ⟨a, rfl⟩ := hφ c
    exact ⟨π a, hh a⟩
  · intro b hb
    obtain ⟨a, rfl⟩ := hπ b
    rw [MonoidHom.mem_ker, hh] at hb
    exact hcen a hb

theorem nonempty_quotientCenterEquiv_of_central_ker (h : B →* C) (hs : Function.Surjective h)
    (hker : h.ker ≤ Subgroup.center B) (hperf : ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = ⊤) :
    Nonempty (B ⧸ Subgroup.center B ≃* C ⧸ Subgroup.center C) := by
  let f : B →* C ⧸ Subgroup.center C := (QuotientGroup.mk' (Subgroup.center C)).comp h
  have hfs : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp hs
  have hfk : f.ker = Subgroup.center B := by
    ext b
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← map_center_eq_center h hs hker hperf]
    constructor
    · rintro ⟨z, hz, hzb⟩
      have hb : b * z⁻¹ ∈ h.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ← hzb, mul_inv_cancel]
      have : b = (b * z⁻¹) * z := by group
      rw [this]
      exact Subgroup.mul_mem _ (hker hb) hz
    · intro hb
      exact ⟨b, hb, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hfk).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs)⟩

theorem commutator_eq_top_of_surjective (h : B →* C) (hs : Function.Surjective h)
    (hB : commutator B = ⊤) : commutator C = ⊤ := by
  rw [commutator_def] at hB ⊢
  have := congrArg (Subgroup.map h) hB
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective h hs] at this
  exact this

end CentralQuotient

section PCore

variable {Y : Type*} [Group Y]

theorem pCore_quotient_pCore_eq_bot : CFSG.pCore 2 (Y ⧸ CFSG.pCore 2 Y) = ⊥ := by
  set P := CFSG.pCore 2 (Y ⧸ CFSG.pCore 2 Y)
  set f := QuotientGroup.mk' (CFSG.pCore 2 Y)
  have hker : IsPGroup 2 f.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hle : P.comap f ≤ CFSG.pCore 2 Y :=
    le_sSup ⟨CFSG.pCore_normal.comap f, CFSG.pCore_isPGroup.comap_of_ker_isPGroup f hker⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  exact hle hx

variable [Finite Y]

theorem odd_card_centralizer (K : Subgroup Y) [hKn : K.Normal]
    (h2 : ∀ y : Y, ∃ e : ℕ, y ^ 2 ^ e ∈ K) (hO : CFSG.pCore 2 Y = ⊥) :
    Odd (Nat.card (Subgroup.centralizer (K : Set Y))) := by
  set C := Subgroup.centralizer (K : Set Y) with hC
  have hCn : C.Normal := ⟨fun n hn g => by
    rw [hC, Subgroup.mem_centralizer_iff] at hn ⊢
    intro k hk
    have hk' : g⁻¹ * k * g ∈ K := by simpa using hKn.conj_mem k hk g⁻¹
    have h1 := hn (g⁻¹ * k * g) hk'
    calc k * (g * n * g⁻¹) = g * ((g⁻¹ * k * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * n * g⁻¹ * k := by group⟩
  let f : ↥C →* Y ⧸ K := (QuotientGroup.mk' K).comp C.subtype
  have hf : f.ker ≤ Subgroup.center ↥C := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp c.2 (x : Y) hx
    exact this.symm
  have hP : IsPGroup 2 (Y ⧸ K) := fun g => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨e, he⟩ := h2 y
    exact ⟨e, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).mpr he⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (Y ⧸ K) := hP.isNilpotent
  have hnil : Group.IsNilpotent ↥C := Subgroup.isNilpotent_of_ker_le_center f hf
  by_contra hodd
  have h2d : 2 ∣ Nat.card ↥C := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2d
  have hxP : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx]
    simp
  obtain ⟨P, hxP'⟩ := hxP.exists_le_sylow
  have hle := Sylow.map_le_pCore hCn hnil 2 P
  rw [hO] at hle
  have hxmem : (x : Y) ∈ P.map C.subtype := ⟨x, hxP' (Subgroup.mem_zpowers x), rfl⟩
  have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.mp (hle hxmem))
  rw [hx1, orderOf_one] at hx
  exact Nat.not_prime_one (hx ▸ Nat.prime_two)

end PCore

section Main

variable {Y H : Type*} [Group Y] [Finite Y] [Group H]

theorem pCore_eq_bot_of_surjective (ψ : Y →* H) (hψ : Function.Surjective ψ)
    (K : Subgroup Y) [hKn : K.Normal]
    (hperf : commutator ↥K = ⊤) (hs : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K))
    (h2 : ∀ y : Y, ∃ e : ℕ, y ^ 2 ^ e ∈ K) (hO : CFSG.pCore 2 Y = ⊥)
    (hD : ∀ d ∈ K, ψ d = 1 → d ∈ Subgroup.centralizer (K : Set Y)) :
    CFSG.pCore 2 H = ⊥ := by
  have : Finite H := Finite.of_surjective ψ hψ
  have hKK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp ⟨hperf⟩
  set C := Subgroup.centralizer (K : Set Y) with hC
  have hodd := odd_card_centralizer K h2 hO
  set K' := K.map ψ with hK'
  have hK'n : K'.Normal := hKn.map ψ hψ
  have hK'K' : ⁅K', K'⁆ = K' := by rw [hK', ← Subgroup.map_commutator, hKK]
  have step1 : Subgroup.centralizer (K' : Set H) ≤ C.map ψ := by
    intro x hx
    obtain ⟨w, rfl⟩ := hψ x
    refine ⟨w, ?_, rfl⟩
    set W := (Subgroup.centralizer (K' : Set H)).comap ψ with hW
    have hWK : ⁅W, K⁆ ≤ ψ.ker ⊓ K := by
      rw [Subgroup.commutator_le]
      intro a ha k hk
      refine ⟨?_, ?_⟩
      · change ψ ⁅a, k⁆ = 1
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp ha (ψ k) ⟨k, hk, rfl⟩).symm
      · rw [commutatorElement_def]
        have : a * k * a⁻¹ ∈ K := by simpa using hKn.conj_mem k hk a
        exact K.mul_mem this (K.inv_mem hk)
    have hKz : ψ.ker ⊓ K ≤ C := fun d hd => hD d hd.2 hd.1
    have hbot : ⁅⁅W, K⁆, K⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      calc ⁅⁅W, K⁆, K⁆ ≤ ⁅C, K⁆ := Subgroup.commutator_mono (hWK.trans hKz) le_rfl
        _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
    exact le_centralizer_of_commutator_commutator_eq_bot hKK hbot hx
  set R := CFSG.pCore 2 H with hR
  have hRn : R.Normal := CFSG.pCore_normal
  have hRp : IsPGroup 2 R := CFSG.pCore_isPGroup
  have step2 : R ⊓ K' ≤ Subgroup.centralizer (K' : Set H) := by
    let ψK : ↥K →* H := ψ.comp K.subtype
    let N : Subgroup ↥K := (R ⊓ K').comap ψK
    have hN : N.Normal := ⟨fun n hn k => by
      have hn' : ψ (n : Y) ∈ R ⊓ K' := hn
      show ψ ((k * n * k⁻¹ : ↥K) : Y) ∈ R ⊓ K'
      have e : ψ ((k * n * k⁻¹ : ↥K) : Y) = ψ k * ψ (n : Y) * (ψ k)⁻¹ := by simp
      rw [e]
      exact ⟨hRn.conj_mem _ hn'.1 _, K'.mul_mem (K'.mul_mem ⟨k, k.2, rfl⟩ hn'.2)
        (K'.inv_mem ⟨k, k.2, rfl⟩)⟩⟩
    rcases normal_le_center_or_eq_top hperf hs N hN with hc | htop
    · rintro t ⟨htR, k, hk, rfl⟩
      have hkN : (⟨k, hk⟩ : ↥K) ∈ N := ⟨htR, k, hk, rfl⟩
      have hkc := Subgroup.mem_center_iff.mp (hc hkN)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k', hk', rfl⟩
      have h' := congrArg (fun z : ↥K => ψ (z : Y)) (hkc ⟨k', hk'⟩)
      simpa using h'
    · exfalso
      have hKR : K' ≤ R := by
        rintro _ ⟨k, hk, rfl⟩
        have : (⟨k, hk⟩ : ↥K) ∈ N := htop ▸ Subgroup.mem_top _
        exact this.1
      have : Group.IsPerfect ↥K' := Subgroup.isPerfect_iff.mpr hK'K'
      have : Finite ↥K' := inferInstance
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hK'p : IsPGroup 2 ↥K' := hRp.to_le hKR
      have : Group.IsNilpotent ↥K' := hK'p.isNilpotent
      have hsub : Subsingleton ↥K' := by
        obtain ⟨n, hn⟩ := (Group.IsSolvable.solvable : ∃ n, derivedSeries ↥K' n = ⊥)
        rw [Group.IsPerfect.derivedSeries_eq_top] at hn
        exact (Subgroup.subsingleton_iff).mp (subsingleton_of_top_eq_bot hn)
      have hall : ∀ k ∈ K, ψ k = 1 := fun k hk => by
        have : ψ k ∈ K' := ⟨k, hk, rfl⟩
        exact congrArg Subtype.val (Subsingleton.elim (⟨ψ k, this⟩ : ↥K') 1)
      have hcen : Subgroup.center ↥K = ⊤ := by
        rw [eq_top_iff]
        intro k _
        rw [Subgroup.mem_center_iff]
        intro k'
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp (hD k k.2 (hall k k.2)) k' k'.2
      have : Subsingleton (↥K ⧸ Subgroup.center ↥K) := by
        rw [hcen]; exact QuotientGroup.subsingleton_quotient_top
      exact not_subsingleton _ ‹Subsingleton (↥K ⧸ Subgroup.center ↥K)›
  have step3 : R ≤ Subgroup.centralizer (K' : Set H) := by
    have hRK : ⁅R, K'⁆ ≤ R ⊓ K' := Subgroup.commutator_le_inf R K'
    have hbot : ⁅⁅R, K'⁆, K'⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      calc ⁅⁅R, K'⁆, K'⁆ ≤ ⁅Subgroup.centralizer (K' : Set H), K'⁆ :=
            Subgroup.commutator_mono (hRK.trans step2) le_rfl
        _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
    exact le_centralizer_of_commutator_commutator_eq_bot hK'K' hbot
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨c, hc, rfl⟩ := step1 (step3 hr)
  have h1 : orderOf (ψ c) ∣ Nat.card ↥C :=
    (orderOf_map_dvd ψ c).trans (by
      rw [← Subgroup.orderOf_mk c hc]
      exact orderOf_dvd_natCard _)
  obtain ⟨e, he⟩ := hRp ⟨ψ c, hr⟩
  have he' : (ψ c) ^ 2 ^ e = 1 := congrArg Subtype.val he
  have h2' : orderOf (ψ c) ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one he'
  have hcop : Nat.Coprime (orderOf (ψ c)) (2 ^ e) := by
    refine Nat.Coprime.pow_right e ?_
    exact (Nat.coprime_two_right.mpr (Odd.of_dvd_nat hodd h1))
  have := Nat.Coprime.eq_one_of_dvd hcop h2'
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp this)

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux

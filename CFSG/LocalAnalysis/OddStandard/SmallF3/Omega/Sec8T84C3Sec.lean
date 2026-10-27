module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Aut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Per
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218a

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup
open CFSG.GH74.GLS.Bg.TwoGroups

theorem card_comm_sections {V : Type} [CommGroup V] [Finite V] (hsq : ∀ v : V, v * v = 1)
    (hcard : Nat.card V = 2 ^ 8) (ζ x : MulAut V) (hζ : ζ ^ 3 = 1)
    (hfix : ∀ v : V, ζ v = v → v = 1) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hcomm : ζ * x = x * ζ) :
    ∃ T R : Subgroup V, R ≤ T ∧ (∀ v : V, v ∈ T ↔ x v = v) ∧
      (∀ r : V, r ∈ R ↔ ∃ v : V, r = x v * v⁻¹) ∧
      Nat.card R * Nat.card T = 256 ∧ (Nat.card R = 4 ∨ Nat.card R = 16) := by
  classical
  let δ : V →* V := MonoidHom.mk' (fun v => x v * v⁻¹) (by
    intro a b
    simp only [map_mul, mul_inv_rev]
    ac_rfl)
  have hδ : ∀ v : V, δ v = x v * v⁻¹ := fun v => rfl
  let T : Subgroup V := L218.fixE x
  let R : Subgroup V := δ.range
  have hx2' : ∀ v : V, x (x v) = v := by
    intro v
    have := congrArg (fun m : MulAut V => m v) hx2
    simpa using this
  have hinv : ∀ a : V, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hsq a)
  have hT : ∀ v : V, v ∈ T ↔ x v = v := fun v => L218.mem_fixE x v
  have hRmem : ∀ r : V, r ∈ R ↔ ∃ v : V, r = x v * v⁻¹ := by
    intro r
    show r ∈ δ.range ↔ _
    rw [MonoidHom.mem_range]
    simp only [hδ]
    exact exists_congr (fun v => eq_comm)
  have hker : δ.ker = T := by
    ext v
    rw [MonoidHom.mem_ker, hδ v, hT v]
    exact mul_inv_eq_one
  have hRT : R ≤ T := by
    intro r hr
    rw [hT]
    obtain ⟨v, rfl⟩ := (hRmem r).mp hr
    rw [map_mul, map_inv, hx2' v, hinv (x v), hinv v, mul_comm v (x v)]
  have hcard_eq : Nat.card R * Nat.card T = 256 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker
    have h2 : Nat.card (V ⧸ δ.ker) = Nat.card δ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv
    rw [h2, hker] at h1
    have hRdef : R = δ.range := rfl
    rw [hRdef]
    rw [← h1, hcard]
    norm_num
  have hcomm_apply : ∀ v : V, ζ (x v) = x (ζ v) := by
    intro v
    have := congrArg (fun m : MulAut V => m v) hcomm
    simpa using this
  have hRinv : ∀ r : V, r ∈ R → ζ r ∈ R := by
    intro r hr
    obtain ⟨v, hv⟩ := (hRmem r).mp hr
    rw [hv, hRmem]
    refine ⟨ζ v, ?_⟩
    rw [map_mul, map_inv, hcomm_apply v]
  have hfix1 : Nat.card {d : R // ζ d = d} = 1 := by
    haveI : Unique {d : R // ζ d = d} :=
      { default := ⟨1, by simp⟩
        uniq := fun d => by
          apply Subtype.ext
          apply Subtype.ext
          exact hfix (d : V) d.2 }
    exact Nat.card_unique
  have hmod : Nat.card R ≡ 1 [MOD 3] := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := L218.card_fix_modEq ζ R hRinv 3 1 (by simpa using hζ)
    rwa [hfix1] at h
  have hxne : ∃ v : V, x v ≠ v := by
    by_contra h
    push Not at h
    exact hx1 (by ext v; exact h v)
  have hne : R ≠ ⊥ := by
    obtain ⟨v, hv⟩ := hxne
    intro hbot
    have hmem : δ v ∈ R := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rw [hbot] at hmem
    have hδv : δ v = 1 := Subgroup.mem_bot.mp hmem
    apply hv
    have hx : x v * v⁻¹ = 1 := by rw [← hδ v]; exact hδv
    exact mul_inv_eq_one.mp hx
  have hne1 : Nat.card R ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  have hdvd : Nat.card R ∣ 2 ^ 8 := by
    have := Subgroup.card_subgroup_dvd_card R
    rwa [hcard] at this
  have hsq_le : Nat.card R * Nat.card R ≤ 256 := by
    have hle : Nat.card R ≤ Nat.card T := Subgroup.card_le_of_le hRT
    calc Nat.card R * Nat.card R ≤ Nat.card R * Nat.card T := Nat.mul_le_mul_left _ hle
      _ = 256 := hcard_eq
  have hRle16 : Nat.card R ≤ 16 := by
    nlinarith [hsq_le]
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hval : Nat.card R = 4 ∨ Nat.card R = 16 := by
    have hj04 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by
      omega
    rcases hj04 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso; rw [hj] at hne1; revert hne1; decide
    · exfalso; rw [hj] at hmod; revert hmod; decide
    · left; rw [hj]; norm_num
    · exfalso; rw [hj] at hmod; revert hmod; decide
    · right; rw [hj]; norm_num
    · exfalso; rw [hj] at hmod; revert hmod; decide
    · exfalso; rw [hj] at hRle16
      exact (by norm_num : ¬ ((2 : ℕ) ^ 6 ≤ 16)) hRle16
    · exfalso; rw [hj] at hmod; revert hmod; decide
    · exfalso; rw [hj] at hRle16
      exact (by norm_num : ¬ ((2 : ℕ) ^ 8 ≤ 16)) hRle16
  exact ⟨T, R, hRT, hT, hRmem, hcard_eq, hval⟩

theorem sec_comm_trivial {V : Type} [CommGroup V] [Finite V] (hsq : ∀ v : V, v * v = 1)
    (ζ : MulAut V) (hζ : ζ ^ 3 = 1) (hfix : ∀ v : V, ζ v = v → v = 1)
    (M N : Subgroup (MulAut V)) (hζM : ζ ∈ M) (hMζ : ∀ m ∈ M, m * ζ = ζ * m)
    (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hq : QuotEquivTo M N (alternatingGroup (Fin 6)))
    (Rr Tt : Subgroup V) (hRT : Rr ≤ Tt) (hT : ∀ m ∈ M, ∀ t ∈ Tt, m t ∈ Tt)
    (hR : ∀ m ∈ M, ∀ r ∈ Rr, m r ∈ Rr)
    (hS : Nat.card (↥Tt ⧸ Rr.subgroupOf Tt) ≤ 16) :
    ∀ a b : ↥M, ∀ t ∈ Tt, ((a * b * a⁻¹ * b⁻¹ : ↥M) : MulAut V) t * t⁻¹ ∈ Rr := by
  classical
  let S := ↥Tt ⧸ Rr.subgroupOf Tt
  obtain ⟨ρ, hρ⟩ := exists_sectionAct Rr Tt hRT M hT hR
  let ζS : MulAut S := ρ ⟨ζ, hζM⟩
  haveI : Finite S := inferInstance
  have hsqS : ∀ s : S, s * s = 1 := by
    intro s
    refine QuotientGroup.induction_on s ?_
    intro t
    rw [← QuotientGroup.mk_mul]
    rw [show (t : ↥Tt) * t = 1 from Subtype.ext (hsq (t : V))]
    rfl
  have hζ3v : ∀ v : V, ζ (ζ (ζ v)) = v := by
    intro v
    have := congrArg (fun m : MulAut V => m v) hζ
    simpa [pow_succ, MulAut.mul_apply] using this
  have htriple : ∀ v : V, v * ζ v * ζ (ζ v) = 1 := by
    intro v
    have h : ζ (v * ζ v * ζ (ζ v)) = v * ζ v * ζ (ζ v) := by
      rw [map_mul, map_mul, hζ3v v]
      ac_rfl
    exact hfix _ h
  have hζS3 : ζS ^ 3 = 1 := by
    have h3 : (⟨ζ, hζM⟩ : ↥M) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hζ
    have h := map_pow ρ (⟨ζ, hζM⟩ : ↥M) 3
    rw [h3, map_one] at h
    exact h.symm
  have hfixS : ∀ s : S, ζS s = s → s = 1 := by
    intro s
    refine QuotientGroup.induction_on s (fun t ht => ?_)
    have hζt_mem : ζ (t : V) ∈ Tt := hT ζ hζM t t.2
    have hζζt_mem : ζ (ζ (t : V)) ∈ Tt :=
      hT ζ hζM (ζ t) hζt_mem
    have hζS_mk : ζS (QuotientGroup.mk t) = QuotientGroup.mk (⟨ζ t, hζt_mem⟩ : ↥Tt) :=
      hρ ⟨ζ, hζM⟩ t
    have hζS_mk2 : ζS (QuotientGroup.mk (⟨ζ t, hζt_mem⟩ : ↥Tt)) =
        QuotientGroup.mk (⟨ζ (ζ t), hζζt_mem⟩ : ↥Tt) :=
      hρ ⟨ζ, hζM⟩ ⟨ζ t, hζt_mem⟩
    have hprod : (QuotientGroup.mk t : S) * ζS (QuotientGroup.mk t) *
        ζS (ζS (QuotientGroup.mk t)) = 1 := by
      rw [hζS_mk, hζS_mk2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rw [show (t * (⟨ζ t, hζt_mem⟩ : ↥Tt) * ⟨ζ (ζ t), hζζt_mem⟩ : ↥Tt) = 1 from by
        apply Subtype.ext
        simpa using htriple (t : V)]
      rw [QuotientGroup.mk_one]
    have hprod' : (QuotientGroup.mk t : S) * QuotientGroup.mk t *
        QuotientGroup.mk t = 1 := by
      simpa only [ht] using hprod
    calc (QuotientGroup.mk t : S)
        = QuotientGroup.mk t * 1 := (mul_one _).symm
      _ = QuotientGroup.mk t * (QuotientGroup.mk t * QuotientGroup.mk t) := by
          rw [hsqS (QuotientGroup.mk t)]
      _ = QuotientGroup.mk t * QuotientGroup.mk t * QuotientGroup.mk t :=
          (mul_assoc _ _ _).symm
      _ = 1 := hprod'
  haveI : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S))
      (fun f g h => MulEquiv.ext (fun x => congrFun h x))
  haveI : Finite ↥(Subgroup.centralizer ({ζS} : Set (MulAut S))) := inferInstance
  have hcent := card_centralizer_zeta_le hsqS ζS hζS3 hfixS hS
  have hL : Nat.card ↥(Subgroup.centralizer ({ζS} : Set (MulAut S))) < 360 := by
    omega
  have hmem_cent : ∀ m : ↥M, ρ m ∈ Subgroup.centralizer ({ζS} : Set (MulAut S)) := by
    intro m
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hm : (m * ⟨ζ, hζM⟩ : ↥M) = ⟨ζ, hζM⟩ * m := by
      apply Subtype.ext
      exact hMζ m m.2
    have h := congrArg ρ hm
    simpa [map_mul, ζS] using h
  let ρ' : ↥M →* ↥(Subgroup.centralizer ({ζS} : Set (MulAut S))) :=
    ρ.codRestrict (Subgroup.centralizer ({ζS} : Set (MulAut S))) hmem_cent
  have hchoose : ∀ m : ↥M, ∃ n : ↥M, (n : MulAut V) ∈ N ∧ ρ m = ρ n := by
    intro m
    obtain ⟨n, hnN, heq⟩ := exists_eq_of_quotEquivTo_card_lt hq ρ' hL m
    refine ⟨n, hnN, ?_⟩
    have h := congrArg Subtype.val heq
    simpa [ρ'] using h
  intro a b t ht
  obtain ⟨na, hnaN, hna⟩ := hchoose a
  obtain ⟨nb, hnbN, hnb⟩ := hchoose b
  have hcomm_n : na * nb = nb * na := by
    apply Subtype.ext
    exact hNc na hnaN nb hnbN
  have hcomm_ρ : ρ na * ρ nb = ρ nb * ρ na := by
    rw [← map_mul, ← map_mul, hcomm_n]
  let c : ↥M := a * b * a⁻¹ * b⁻¹
  have hρc : ρ c = 1 := by
    show ρ (a * b * a⁻¹ * b⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hna, hnb, hcomm_ρ]
    group
  have heq : (QuotientGroup.mk ⟨t, ht⟩ : S) =
      QuotientGroup.mk ⟨(c : MulAut V) t, hT c c.2 t ht⟩ := by
    have h := hρ c ⟨t, ht⟩
    rw [hρc] at h
    simpa using h
  have hmem : (⟨t, ht⟩ : ↥Tt)⁻¹ * ⟨(c : MulAut V) t, hT c c.2 t ht⟩ ∈
      Rr.subgroupOf Tt := QuotientGroup.eq.mp heq
  have hmem' : (t : V)⁻¹ * (c : MulAut V) t ∈ Rr := by
    have h := Subgroup.mem_subgroupOf.mp hmem
    simpa using h
  rw [mul_comm]
  exact hmem'

end C10

end CFSG.OddStandard.SmallF3.Omega

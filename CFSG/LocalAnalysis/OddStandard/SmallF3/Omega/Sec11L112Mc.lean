module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Cls
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112QA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11_T_set {t z : G} {T A M : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 6))}
    {φ : (Fin 6 → ZMod 2) → G} (hm : Sec11Perm A M Alt φ) (hTM : T ≤ M)
    (ht : t = φ (Pi.single 0 1)) (htz : t * z = φ (Pi.single 1 1))
    (hcl : conjClassIn T t = {t, t * z}) (x : G) (hx : x ∈ T) :
    (hm.rho x 0 = 0 ∧ hm.rho x 1 = 1) ∨ (hm.rho x 0 = 1 ∧ hm.rho x 1 = 0) := by
  have hxM : x ∈ M := hTM hx
  have key : ∀ y ∈ conjClassIn T t, ∀ k : Fin 6, φ (Pi.single k 1) = y → k = 0 ∨ k = 1 := by
    intro y hy k hk
    rw [hcl] at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Or.inl (hm.single_inj (hk.trans ht))
    · exact Or.inr (hm.single_inj (hk.trans htz))
  obtain ⟨m, hmT, hm'⟩ : t * z ∈ conjClassIn T t := by
    rw [hcl]
    simp
  have h0 : hm.rho x 0 = 0 ∨ hm.rho x 0 = 1 := by
    refine key (x * t * x⁻¹) ⟨x, hx, rfl⟩ _ ?_
    rw [ht]
    exact (hm.conj_single hxM 0).symm
  have h1 : hm.rho x 1 = 0 ∨ hm.rho x 1 = 1 := by
    refine key (x * (t * z) * x⁻¹) ⟨x * m, T.mul_mem hx hmT, ?_⟩ _ ?_
    · rw [hm']
      group
    · rw [htz]
      exact (hm.conj_single hxM 1).symm
  have hinj := (hm.rho x).injective
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact absurd (hinj (h0.trans h1.symm)) (by decide)
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exact absurd (hinj (h0.trans h1.symm)) (by decide)

namespace Sec11Perm

variable {A M : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem card_A (hm : Sec11Perm A M Alt φ) : Nat.card A = 32 := by
  let f : {v : Fin 6 → ZMod 2 // v 5 = 0} → A := fun v => ⟨φ v.1, hm.mem _⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro v w h
      have h' : φ v.1 = φ w.1 := congrArg Subtype.val h
      rcases (hm.eq_iff _ _).mp h' with h1 | h1
      · exact Subtype.ext (sec11_vec_eq_of_add_eq_zero h1)
      · exfalso
        have := congrFun h1 5
        simp only [Pi.add_apply, v.2, w.2] at this
        exact absurd this (by decide)
    · rintro ⟨a, ha⟩
      obtain ⟨v, hv⟩ := hm.surj a ha
      obtain ⟨v', hv', h5⟩ := sec11_exists_rep v
      refine ⟨⟨v', h5⟩, Subtype.ext ?_⟩
      show φ v' = a
      rcases hv' with rfl | rfl
      · exact hv
      · rw [hm.map_add_one, hv]
  rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end Sec11Perm

theorem sec11_sylow_card_of {H : Type} [Group H] [Finite H] (P : Sylow 2 H) {k m : ℕ}
    (hm : ¬ 2 ∣ m) (h : Nat.card H = 2 ^ k * m) : Nat.card P = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [Sylow.card_eq_multiplicity, h, Nat.factorization_mul (by positivity) hm0,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd hm]

theorem sec11_card_T [Finite G] {A M T : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 6))}
    {φ : (Fin 6 → ZMod 2) → G} (hm : Sec11Perm A M Alt φ)
    (hAlt : Alt = alternatingGroup (Fin 6) ∨ Alt = ⊤) (hT : IsSylow2Of T M) (hAT : A ≤ T)
    (hcen : ∀ c ∈ T, (∀ a ∈ A, c * a = a * c) → c ∈ A) :
    (Alt = ⊤ → Nat.card ↥T = 512) ∧ (Alt ≠ ⊤ → Nat.card ↥T = 256) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hT.exists_sylow
  have hPT : ∀ p : ↥P, ((p : ↥M) : G) ∈ T := fun p => hP ▸ ⟨(p : ↥M), p.2, rfl⟩
  let F : ↥M →* ↥hm.rhoHom.range := hm.rhoHom.rangeRestrict
  have hF : Function.Surjective F := hm.rhoHom.rangeRestrict_surjective
  let g2 : ↥(P : Subgroup ↥M) →* ↥hm.rhoHom.range := F.comp (P : Subgroup ↥M).subtype
  have hker : Nat.card ↥g2.ker = 32 := by
    rw [← hm.card_A]
    have hcomm : ∀ (p : ↥P) (a : G), a ∈ A → (g2 p = 1) → ((p : ↥M) : G) * a = a * (p : ↥M) := by
      intro p a ha hp
      have h0 : hm.rhoHom (p : ↥M) = 1 := by
        have := congrArg Subtype.val hp
        exact this
      have h1 : hm.rho ((p : ↥M) : G) = 1 := by
        rw [← hm.rhoHom_apply]
        exact h0
      have h2 := (hm.rho_eq_one_iff (p : ↥M).2).mp h1 a ha
      exact (mul_inv_eq_iff_eq_mul.mp h2)
    let e : ↥g2.ker → ↥A := fun k =>
      ⟨((k.1 : ↥M) : G), hcen _ (hPT k.1) fun a ha => hcomm k.1 a ha k.2⟩
    have hbij : Function.Bijective e := by
      constructor
      · intro k k' h
        have h' : ((k.1 : ↥M) : G) = ((k'.1 : ↥M) : G) := by
          have := congrArg Subtype.val h
          exact this
        exact Subtype.ext (Subtype.ext (Subtype.ext h'))
      · rintro ⟨a, ha⟩
        have haT : a ∈ T := hAT ha
        have haM : a ∈ M := hT.1 haT
        have haP : (⟨a, haM⟩ : ↥M) ∈ P := by
          rw [← hP] at haT
          obtain ⟨y, hy, hya⟩ := haT
          have : y = ⟨a, haM⟩ := Subtype.ext hya
          rw [← this]
          exact hy
        refine ⟨⟨⟨⟨a, haM⟩, haP⟩, ?_⟩, rfl⟩
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        show hm.rhoHom ⟨a, haM⟩ = 1
        rw [hm.rhoHom_apply, hm.rho_eq_one_iff haM]
        intro b hb
        obtain ⟨v, rfl⟩ := hm.surj b hb
        obtain ⟨w, rfl⟩ := hm.surj a ha
        rw [hm.comm w v]
        group
    exact Nat.card_congr (Equiv.ofBijective e hbij)
  have hr2 : g2.range = (P : Subgroup ↥M).map F := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hprod : Nat.card ↥g2.ker * Nat.card ↥g2.range = Nat.card ↥P :=
    Subgroup.card_ker_mul_card_range g2
  have hTP : Nat.card ↥T = Nat.card ↥P := by
    rw [← hP]
    exact Subgroup.card_map_of_injective M.subtype_injective
  have hP2 : Nat.card ↥(P.mapSurjective hF) = Nat.card ↥g2.range := by
    rw [hr2]
    rfl
  have hrange : Nat.card ↥hm.rhoHom.range = Nat.card ↥Alt := by rw [hm.range_rhoHom]
  rw [hker, ← hP2] at hprod
  refine ⟨fun htop => ?_, fun hne => ?_⟩
  · have h720 : Nat.card ↥hm.rhoHom.range = 2 ^ 4 * 45 := by
      rw [hrange, htop, Subgroup.card_top, Nat.card_perm]
      simp [Nat.factorial]
    have h16 : Nat.card ↥(P.mapSurjective hF) = 2 ^ 4 :=
      sec11_sylow_card_of (P.mapSurjective hF) (k := 4) (m := 45) (by norm_num) h720
    calc Nat.card ↥T = Nat.card ↥P := hTP
      _ = 32 * Nat.card ↥(P.mapSurjective hF) := hprod.symm
      _ = 512 := by rw [h16]; norm_num
  · have hA6 : Alt = alternatingGroup (Fin 6) := hAlt.resolve_right hne
    have h360 : Nat.card ↥hm.rhoHom.range = 2 ^ 3 * 45 := by
      rw [hrange, hA6, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have h8 : Nat.card ↥(P.mapSurjective hF) = 2 ^ 3 :=
      sec11_sylow_card_of (P.mapSurjective hF) (k := 3) (m := 45) (by norm_num) h360
    calc Nat.card ↥T = Nat.card ↥P := hTP
      _ = 32 * Nat.card ↥(P.mapSurjective hF) := hprod.symm
      _ = 256 := by rw [h8]; norm_num

end CFSG.OddStandard.SmallF3.Omega

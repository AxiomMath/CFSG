module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P33c

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1

section S

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

omit [Finite G] in
theorem normalizer_conj_mem {V : Subgroup G} {g : G} (hg : g ∈ normalizer (V : Set G)) :
    (∀ v ∈ V, g * v * g⁻¹ ∈ V) ∧ (∀ v ∈ V, g⁻¹ * v * g ∈ V) := by
  refine ⟨fun v hv => (Subgroup.mem_normalizer_iff.1 hg v).1 hv, fun v hv => ?_⟩
  have := (Subgroup.mem_normalizer_iff.1 ((normalizer (V : Set G)).inv_mem hg) v).1 hv
  simpa using this

theorem Env33.hPker (E : Env33 x y K T V W f z) :
    ∀ p ∈ T ⊓ K, ∀ hp : p ∈ centralizer ({x} : Set G), Back.actHom E.hKN ⟨p, hp⟩ = 1 → p = 1 := by
  intro p hpP hpC hφ
  have hpK : p ∈ K := hpP.2
  have h1 := Back.actHom_of_mem E.hKN hpK hpC
  have h2 : MulAut.conj (QuotientGroup.mk (⟨p, hpK⟩ : ↥K) : kBar K) = MulAut.conj 1 := by
    rw [map_one, ← h1]
    exact hφ
  have h3 := E.hcen h2
  have h4 : (⟨p, hpK⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h3
  have h5 : p ∈ pPrimeCoreOf 2 K := Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hpK, h4⟩
  have h6 := Back.Setup91.inf_pPrimeCoreOf_eq_bot K E.hPK.isPGroup
  have h7 : p ∈ (T ⊓ K) ⊓ pPrimeCoreOf 2 K := ⟨hpP, h5⟩
  rw [h6, Subgroup.mem_bot] at h7
  exact h7

theorem Env33.hxker (E : Env33 x y K T V W f z) :
    Back.actHom E.hKN ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ = 1 := by
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hxmem : x ∈ CMK (centralizer ({x} : Set G)) K := E.hxS.le (mem_zpowers x)
  have hker : (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom E.hKN).ker := by
    rw [Back.actHom_ker E.hKN]
    exact hxmem
  exact hker

theorem Env33.exists_mem_P_of_inn (E : Env33 x y K T V W f z) {N : Subgroup G}
    (hN2 : IsPGroup 2 ↥N) (hNC : N ≤ centralizer ({x} : Set G)) (hPN : T ⊓ K ≤ N) :
    ∀ n (hn : n ∈ N), Back.actHom E.hKN ⟨n, hNC hn⟩ ∈ innAut (kBar K) →
      n ∈ (T ⊓ K) ⊔ zpowers x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : ↥N →* MulAut (kBar K) := (Back.actHom E.hKN).comp (Subgroup.inclusion hNC)
  set P' : Subgroup ↥N := (T ⊓ K).subgroupOf N with hP'
  have hker : ∀ p ∈ P', ρ p = 1 → p = 1 := by
    intro p hp hρp
    have hpP : (p : G) ∈ T ⊓ K := hp
    exact Subtype.ext (E.hPker (p : G) hpP (hNC p.2) hρp)
  have hPE : ∀ p ∈ P', ρ p ∈ innAut (kBar K) := by
    intro p hp
    have hpP : (p : G) ∈ T ⊓ K := hp
    show Back.actHom E.hKN ⟨(p : G), hNC p.2⟩ ∈ innAut (kBar K)
    rw [Back.actHom_of_mem E.hKN hpP.2 (hNC p.2)]
    exact ⟨_, rfl⟩
  have hE : Nat.card ↥(innAut (kBar K)) = Nat.card (kBar K) :=
    (Nat.card_congr (MonoidHom.ofInjective E.hcen).toEquiv).symm
  have hcard : ∀ j : ℕ, 2 ^ j ∣ Nat.card ↥(innAut (kBar K)) → 2 ^ j ≤ Nat.card ↥P' := by
    intro j hj
    rw [hE] at hj
    have h2 : 2 ^ j ∣ Nat.card ↥K := hj.trans (Subgroup.card_quotient_dvd_card _)
    have hK0 : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
    have h3 : j ≤ (Nat.card ↥K).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hK0).1 h2
    have h4 : Nat.card ↥P' = Nat.card ↥(T ⊓ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
    rw [h4, E.hPK.card_eq]
    exact Nat.pow_le_pow_right (by norm_num) h3
  have himg := image_inf_eq_image hN2 ρ (innAut (kBar K)) P' hker hPE hcard
  intro n hn hinn
  obtain ⟨p, hp, hpn⟩ := himg ⟨n, hn⟩ hinn
  have hpP : (p : G) ∈ T ⊓ K := hp
  have hcN : (p : G)⁻¹ * n ∈ N := N.mul_mem (N.inv_mem p.2) hn
  have hcC : (p : G)⁻¹ * n ∈ centralizer ({x} : Set G) := hNC hcN
  have hφc : Back.actHom E.hKN ⟨(p : G)⁻¹ * n, hcC⟩ = 1 := by
    have h1 : (⟨(p : G)⁻¹ * n, hcC⟩ : ↥(centralizer ({x} : Set G))) =
        (⟨(p : G), hNC p.2⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * ⟨n, hNC hn⟩ := rfl
    rw [h1, map_mul, map_inv]
    have h' : Back.actHom E.hKN ⟨(p : G), hNC p.2⟩ = Back.actHom E.hKN ⟨n, hNC hn⟩ := hpn
    rw [h']
    group
  have hcmk : (p : G)⁻¹ * n ∈ CMK (centralizer ({x} : Set G)) K := by
    have hkerc : (⟨(p : G)⁻¹ * n, hcC⟩ : ↥(centralizer ({x} : Set G))) ∈
        (Back.actHom E.hKN).ker := hφc
    rw [Back.actHom_ker E.hKN] at hkerc
    exact hkerc
  have hc2 : ∃ k : ℕ, ((p : G)⁻¹ * n) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hN2 ⟨(p : G)⁻¹ * n, hcN⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hcx : (p : G)⁻¹ * n ∈ zpowers x :=
    mem_zpowers_of_two_element E.hxS (fun k hk => mem_centralizer_singleton_iff.1 hk.1) hcmk hc2
  have hn' : n = (p : G) * ((p : G)⁻¹ * n) := by group
  rw [hn']
  exact Subgroup.mul_mem_sup hpP hcx

theorem hom_cyclic_involutions_eq {M C : Type} [Group M] [Finite M] [Group C] [IsCyclic C]
    (ω : M →* C) {a b : M} (ha : ω a ≠ 1) (hb : ω b ≠ 1) (ha2 : ω a * ω a = 1)
    (hb2 : ω b * ω b = 1) : ω a = ω b := by
  have : Finite ↥ω.range := Finite.of_surjective ω.rangeRestrict ω.rangeRestrict_surjective
  have hc : IsCyclic ↥ω.range := inferInstance
  have h := IVK.DihedralAux.cyclic_unique_involution (G := ↥ω.range)
    (a := ⟨ω a, a, rfl⟩) (b := ⟨ω b, b, rfl⟩)
    (fun h => ha (congrArg Subtype.val h)) (fun h => hb (congrArg Subtype.val h))
    (Subtype.ext ha2) (Subtype.ext hb2)
  exact congrArg Subtype.val h

theorem Env33.hOmega1S (E : Env33 x y K T V W f z) :
    ∀ u ∈ V, u * x = x * u → u * u = 1 → u ∈ (T ⊓ K) ⊔ (zpowers x ⊔ zpowers f) := by
  intro u hu hux huu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC : V ⊓ centralizer ({x} : Set G) ≤ centralizer ({x} : Set G) := inf_le_right
  have hS2 : IsPGroup 2 ↥(V ⊓ centralizer ({x} : Set G)) := E.hV2.to_le inf_le_left
  have hPS : T ⊓ K ≤ V ⊓ centralizer ({x} : Set G) :=
    le_inf E.hPV (fun p hp => mem_centralizer_singleton_iff.2 (E.hxcommK p hp.2))
  have huS : u ∈ V ⊓ centralizer ({x} : Set G) :=
    ⟨hu, mem_centralizer_singleton_iff.2 hux⟩
  have hfuS : u * f ∈ V ⊓ centralizer ({x} : Set G) :=
    (V ⊓ centralizer ({x} : Set G)).mul_mem huS E.hS_f
  have hσσ : Back.actHom E.hKN ⟨f, E.hfC⟩ * Back.actHom E.hKN ⟨f, E.hfC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f, E.hfC⟩ : ↥(centralizer ({x} : Set G))) * ⟨f, E.hfC⟩ = 1 := Subtype.ext E.hf2'
    rw [this, map_one]
  have hσ1 : Back.actHom E.hKN ⟨f, E.hfC⟩ ≠ 1 := fun h => E.hfout (h ▸ (innAut _).one_mem)
  have hσ2 : orderOf (Back.actHom E.hKN ⟨f, E.hfC⟩) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  obtain ⟨C, hC, hCc, ω, hω1, hωσ, hω3⟩ := omegaData_of_isFAut hσ2 E.hfFaut
  set σ := Back.actHom E.hKN ⟨f, E.hfC⟩ with hσdef
  set ū := Back.actHom E.hKN ⟨u, hSC huS⟩ with hūdef
  have hūū : ū * ū = 1 := by
    rw [hūdef, ← map_mul]
    have : (⟨u, hSC huS⟩ : ↥(centralizer ({x} : Set G))) * ⟨u, hSC huS⟩ = 1 := Subtype.ext huu
    rw [this, map_one]
  have hσū : σ * ū = ū * σ := by
    rw [hσdef, hūdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (E.hVf u hu).symm
  have hωσσ : ω σ * ω σ = 1 := by rw [← map_mul, hσσ, map_one]
  by_cases hωu : ω ū = 1
  · have hinn := hω3 ū hσū hωu
    have := E.exists_mem_P_of_inn hS2 hSC hPS u huS hinn
    exact (sup_le_sup_left (le_sup_left : zpowers x ≤ zpowers x ⊔ zpowers f) (T ⊓ K)) this
  · have hωuu : ω ū * ω ū = 1 := by rw [← map_mul, hūū, map_one]
    have hωeq : ω ū = ω σ := hom_cyclic_involutions_eq ω hωu hωσ hωuu hωσσ
    set w := Back.actHom E.hKN ⟨u * f, hSC hfuS⟩ with hwdef
    have hwuσ : w = ū * σ := by
      rw [hwdef, hūdef, hσdef, ← map_mul]
      rfl
    have hωw : ω w = 1 := by
      rw [hwuσ, map_mul, hωeq, hωσσ]
    have hσw : σ * w = w * σ := by
      rw [hwuσ]
      calc σ * (ū * σ) = (σ * ū) * σ := by group
        _ = (ū * σ) * σ := by rw [hσū]
    have hwinn := hω3 w hσw hωw
    have hmem := E.exists_mem_P_of_inn hS2 hSC hPS (u * f) hfuS hwinn
    have hu' : u = (u * f) * f⁻¹ := by group
    rw [hu']
    refine Subgroup.mul_mem _ ?_ ?_
    · exact (sup_le_sup_left (le_sup_left : zpowers x ≤ zpowers x ⊔ zpowers f) (T ⊓ K)) hmem
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right ((zpowers f).inv_mem (mem_zpowers f)))

end S

end CFSG.GH74.GLS.C3.Layer1.Thm1G33

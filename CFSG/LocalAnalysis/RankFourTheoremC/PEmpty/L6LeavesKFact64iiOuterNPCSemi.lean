module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiOuterNPCBurn
public import Mathlib.GroupTheory.SemidirectProduct
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiOuterNPCCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64iiNPC

open SemidirectProduct
open scoped Pointwise

theorem exists_fixed_normalizing {K : Type*} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K) (hcyc : ∀ P : Sylow p K, IsCyclic (P : Subgroup K))
    (φ : MulAut K) (hφ : orderOf φ = p)
    (hmov : ∀ P : Sylow p K, ∃ g ∈ (P : Subgroup K), φ g ≠ g) :
    ∃ w r : K, φ w = w ∧ φ r = r ∧ orderOf r = p ∧ w * r * w⁻¹ ∈ Subgroup.zpowers r ∧
      w * r * w⁻¹ ≠ r := by
  classical
  set N : Subgroup (MulAut K) := Subgroup.zpowers φ with hN
  have hNcard : Nat.card N = p := by rw [hN, Nat.card_zpowers, hφ]
  have hNp : IsPGroup p N := IsPGroup.of_card (n := 1) (by rw [hNcard, pow_one])
  obtain ⟨PK, hPK⟩ := hNp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p K)
    (not_dvd_card_sylow p K)
  have hPKmem : ∀ g : N, ∀ x ∈ (PK : Subgroup K), (g : MulAut K) x ∈ (PK : Subgroup K) := by
    intro g x hx
    have hfix : g • PK = PK := hPK g
    have h1 : g • x ∈ (g • (PK : Subgroup K)) := Subgroup.smul_mem_pointwise_smul _ _ _ hx
    have h2 : g • x ∈ ((g • PK : Sylow p K) : Subgroup K) := h1
    rw [hfix] at h2
    exact h2
  have hPKiff : ∀ x : K, x ∈ (PK : Subgroup K) ↔ φ x ∈ (PK : Subgroup K) := by
    intro x
    constructor
    · intro hx
      exact hPKmem ⟨φ, Subgroup.mem_zpowers φ⟩ x hx
    · intro hx
      have := hPKmem ⟨φ⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers φ)⟩ (φ x) hx
      simpa using this
  haveI : Finite (K ⋊[N.subtype] N) := Finite.of_equiv (K × N) SemidirectProduct.equivProd.symm
  set f : K ⋊[N.subtype] N := inr ⟨φ, Subgroup.mem_zpowers φ⟩ with hf
  set Kn : Subgroup (K ⋊[N.subtype] N) := (inl : K →* K ⋊[N.subtype] N).range with hKn
  haveI hKnN : Kn.Normal := by
    rw [hKn, range_inl_eq_ker_rightHom]
    exact MonoidHom.normal_ker _
  have hfconj : ∀ x : K, f * inl x * f⁻¹ = inl (φ x) := by
    intro x
    have h := inl_aut (φ := N.subtype) (⟨φ, Subgroup.mem_zpowers φ⟩ : N) x
    rw [map_inv] at h
    exact h.symm
  have hfp : f ^ p = 1 := by
    rw [hf, ← map_pow]
    have : (⟨φ, Subgroup.mem_zpowers φ⟩ : N) ^ p = 1 := by
      apply Subtype.ext
      have h1 : φ ^ p = 1 := by
        have := pow_orderOf_eq_one φ
        rwa [hφ] at this
      simpa using h1
    rw [this, map_one]
  have hf1 : f ≠ 1 := by
    intro h
    have h1 := congrArg (rightHom : K ⋊[N.subtype] N →* N) h
    rw [hf, rightHom_inr, map_one] at h1
    have h2 : φ = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at hφ
    exact hp.out.one_lt.ne hφ
  have hforder : orderOf f = p := orderOf_eq_prime hfp hf1
  have hG : ∀ g : K ⋊[N.subtype] N, ∃ k ∈ Kn, ∃ j : ℕ, g = k * f ^ j := by
    intro g
    obtain ⟨n, z⟩ := g
    refine ⟨inl n, ⟨n, rfl⟩, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (⟨φ, Subgroup.mem_zpowers φ⟩ : N) ^ j = z := by
      obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 z.2)
      exact ⟨j, Subtype.ext (by simpa using hj)⟩
    refine ⟨j, ?_⟩
    rw [hf, ← map_pow, hj, ← mk_eq_inl_mul_inr]
  set PhK : Subgroup (K ⋊[N.subtype] N) := (PK : Subgroup K).map inl with hPhK
  have hPhKp : IsPGroup p PhK := PK.isPGroup'.map inl
  have hfconj' : ∀ x : K, f⁻¹ * inl x * f = inl (φ⁻¹ x) := by
    intro x
    have h := hfconj (φ⁻¹ x)
    rw [MulAut.apply_inv_self] at h
    rw [← h]
    group
  have hfnorm : f ∈ Subgroup.normalizer (PhK : Set (K ⋊[N.subtype] N)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨φ x, (hPKiff x).1 hx, (hfconj x).symm⟩
    · rintro ⟨x, hx, hxh⟩
      have h1 : h = f⁻¹ * inl x * f := by rw [hxh]; group
      rw [h1, hfconj']
      refine ⟨φ⁻¹ x, ?_, rfl⟩
      refine (hPKiff _).2 ?_
      rw [MulAut.apply_inv_self]
      exact hx
  have hKp : IsPGroup p (Subgroup.zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hforder, pow_one])
  have hsupp : IsPGroup p ↥(PhK ⊔ Subgroup.zpowers f) :=
    hPhKp.to_sup_of_normal_left' hKp (Subgroup.zpowers_le.2 hfnorm)
  obtain ⟨S, hS⟩ := hsupp.exists_le_sylow
  have hPhKS : PhK ≤ (S : Subgroup (K ⋊[N.subtype] N)) := le_trans le_sup_left hS
  have hfS : f ∈ (S : Subgroup (K ⋊[N.subtype] N)) :=
    hS (Subgroup.mem_sup_right (Subgroup.mem_zpowers f))
  have hPeq : ∀ x : K ⋊[N.subtype] N, x ∈ (S : Subgroup (K ⋊[N.subtype] N)) ⊓ Kn ↔ x ∈ PhK := by
    intro x
    constructor
    · rintro ⟨hxS, k, rfl⟩
      have hQp : IsPGroup p ((S : Subgroup (K ⋊[N.subtype] N)).comap
          (inl : K →* K ⋊[N.subtype] N)) :=
        S.isPGroup'.comap_of_injective inl inl_injective
      have hle : (PK : Subgroup K) ≤ (S : Subgroup (K ⋊[N.subtype] N)).comap
          (inl : K →* K ⋊[N.subtype] N) := fun y hy => hPhKS ⟨y, hy, rfl⟩
      have hEq := PK.is_maximal' hQp hle
      have hk : k ∈ (PK : Subgroup K) := by
        rw [← hEq]
        exact hxS
      exact ⟨k, hk, rfl⟩
    · intro hx
      exact ⟨hPhKS hx, by obtain ⟨y, -, rfl⟩ := hx; exact ⟨y, rfl⟩⟩
  obtain ⟨γ, hγ⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (PK : Subgroup K)).1 (hcyc PK)
  have hγP : γ ∈ (PK : Subgroup K) := by
    rw [← hγ]
    exact Subgroup.mem_zpowers γ
  have hgenK : ∀ x ∈ (PK : Subgroup K), x ∈ Subgroup.zpowers γ := by
    intro x hx
    rw [hγ]
    exact hx
  have hPKne : (PK : Subgroup K) ≠ ⊥ := PK.ne_bot_of_dvd_card hpK
  obtain ⟨a, hγord⟩ := exists_orderOf_eq_pow_of_mem_sylow PK hγP
  obtain ⟨y, hyN, x, hxP, hxp, hyx⟩ :=
    exists_normalizer_not_centralize_torsion hnab PK hPKne hγord hγP hgenK
  have hg₀ : (inl γ : K ⋊[N.subtype] N) ∈ (S : Subgroup (K ⋊[N.subtype] N)) ⊓ Kn :=
    ⟨hPhKS ⟨γ, hγP, rfl⟩, ⟨γ, rfl⟩⟩
  have hgen : ∀ z ∈ (S : Subgroup (K ⋊[N.subtype] N)) ⊓ Kn,
      z ∈ Subgroup.zpowers (inl γ : K ⋊[N.subtype] N) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := (hPeq z).1 hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgenK u hu)
    exact Subgroup.mem_zpowers_iff.2 ⟨i, (map_zpow inl γ i).symm⟩
  have hmovG : f * inl γ * f⁻¹ ≠ inl γ := by
    rw [hfconj]
    intro h
    have h1 : φ γ = γ := inl_injective h
    obtain ⟨g, hg, hne⟩ := hmov PK
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgenK g hg)
    apply hne
    rw [map_zpow, h1]
  have hy₀N : ∀ z ∈ (S : Subgroup (K ⋊[N.subtype] N)) ⊓ Kn,
      (inl y : K ⋊[N.subtype] N) * z * (inl y)⁻¹ ∈ (S : Subgroup (K ⋊[N.subtype] N)) ⊓ Kn := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := (hPeq z).1 hz
    have h1 : y * u * y⁻¹ ∈ (PK : Subgroup K) := (Subgroup.mem_normalizer_iff.1 hyN u).1 hu
    have h2 := (hPeq (inl (y * u * y⁻¹))).2 ⟨_, h1, rfl⟩
    simpa using h2
  have hy₀N' : ∀ z ∈ (S : Subgroup (K ⋊[N.subtype] N)) ⊓ Kn,
      (inl y : K ⋊[N.subtype] N)⁻¹ * z * inl y ∈ (S : Subgroup (K ⋊[N.subtype] N)) ⊓ Kn := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := (hPeq z).1 hz
    have h1 : y⁻¹ * u * y ∈ (PK : Subgroup K) := by
      refine (Subgroup.mem_normalizer_iff.1 hyN _).2 ?_
      have : y * (y⁻¹ * u * y) * y⁻¹ = u := by group
      rw [this]
      exact hu
    have h2 := (hPeq (inl (y⁻¹ * u * y))).2 ⟨_, h1, rfl⟩
    simpa using h2
  have hxhat : (inl x : K ⋊[N.subtype] N) ∈ (S : Subgroup (K ⋊[N.subtype] N)) ⊓ Kn :=
    (hPeq _).2 ⟨x, hxP, rfl⟩
  obtain ⟨k, r, hkK, hrK, hrord, hfk, hfr, hkr, hkrne⟩ :=
    exists_centralizing_normalizing hp2 Kn f hfp hG S hfS hg₀ hgen hmovG
      (y₀ := inl y) hy₀N hy₀N' (x := inl x) hxhat (by rw [← map_pow, hxp, map_one])
      (by
        intro h
        apply hyx
        refine inl_injective (φ := N.subtype) ?_
        simpa using h)
  obtain ⟨w, rfl⟩ := hkK
  obtain ⟨r', rfl⟩ := hrK
  have hfixed : ∀ u : K, f * inl u = inl u * f → φ u = u := by
    intro u h
    refine inl_injective (φ := N.subtype) ?_
    rw [← hfconj u, h, mul_inv_cancel_right]
  refine ⟨w, r', hfixed w hfk, hfixed r' hfr, ?_, ?_, ?_⟩
  · exact (orderOf_injective (inl : K →* K ⋊[N.subtype] N) inl_injective r').symm.trans hrord
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hkr
    refine Subgroup.mem_zpowers_iff.2 ⟨i, inl_injective (φ := N.subtype) ?_⟩
    rw [map_zpow, hi]
    simp
  · intro h
    apply hkrne
    rw [← map_inv, ← map_mul, ← map_mul, h]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64iiNPC

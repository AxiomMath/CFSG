module

public import CFSG.GH74.KGroups.Generic9
public import CFSG.GH74.KGroups.Generic10

public section

namespace CFSG.GH74.KGroups

open scoped Pointwise

theorem exists_conj_stabilizes {K : Type*} [Group K] [Finite K] (P : Sylow 2 K) (φ : MulAut K) :
    ∃ k : K, ∀ y : K, y ∈ (P : Subgroup K) ↔ (k * φ y * k⁻¹) ∈ (P : Subgroup K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K (φ • P) P
  refine ⟨k, fun y => ?_⟩
  have h := congrArg (fun Q : Sylow 2 K => (Q : Subgroup K)) hk
  simp only [Sylow.coe_subgroup_smul, Sylow.pointwise_smul_def] at h
  have h2 := congrArg (fun H : Subgroup K => (k * φ y * k⁻¹) ∈ H) h
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
  have h3 : φ⁻¹ • (MulAut.conj k)⁻¹ • (k * φ y * k⁻¹) = y := by
    simp [MulAut.smul_def]
    group
  rw [h3] at h2
  exact (iff_of_eq h2)

theorem conj_mem_inv {G : Type*} [Group G] (S : Subgroup G) [Finite S] (σ : G)
    (h : ∀ s ∈ S, σ * s * σ⁻¹ ∈ S) : ∀ s ∈ S, σ⁻¹ * s * σ ∈ S := by
  let f : S → S := fun s => ⟨σ * s * σ⁻¹, h s s.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    have h2 : (a : G) = b := by simpa [f] using this
    exact Subtype.ext h2
  have hs := Finite.injective_iff_surjective.1 hf
  intro s hs'
  obtain ⟨a, ha⟩ := hs ⟨s, hs'⟩
  have h3 : σ * (a : G) * σ⁻¹ = s := congrArg Subtype.val ha
  have h4 : σ⁻¹ * s * σ = a := by rw [← h3]; group
  rw [h4]
  exact a.2

theorem aut_inner_of_pairing {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    (hZcard : Nat.card (Subgroup.center K) = 2)
    (hMF1 : ∀ P : Sylow 2 K, ∀ b ∈ (P : Subgroup K), ∀ c ∈ (P : Subgroup K),
      (∀ x ∈ (P : Subgroup K), b * x * b⁻¹ * x⁻¹ ∈ Subgroup.center K) →
      (∀ x ∈ (P : Subgroup K), c * x * c⁻¹ * x⁻¹ ∈ Subgroup.center K) → b * c = c * b)
    (hMF2 : ∀ P : Sylow 2 K, ∀ b ∈ (P : Subgroup K),
      (∀ x ∈ (P : Subgroup K), b * x * b⁻¹ * x⁻¹ ∈ Subgroup.center K) →
      b ∉ Subgroup.center K → ∀ z ∈ Subgroup.center K,
        ∃ x ∈ (P : Subgroup K), x * b * x⁻¹ * b⁻¹ = z)
    {G : Type*} [Group G] (M : AutModel (K ⧸ Subgroup.center K) G) (S E : Subgroup G)
    (hSP : S ≤ M.P) {v m : ℕ} (hS : Nat.card S = 2 ^ v)
    (hK : Nat.card (K ⧸ Subgroup.center K) = 2 ^ v * m) (hm : Odd m)
    (hES : E ≤ S) (hEz : ∀ w ∈ E, ∀ s ∈ S, w * s = s * w)
    (Fx : G → Prop)
    (hfix : ∀ σ : G, (∀ s ∈ S, σ * s * σ⁻¹ ∈ S) → (∀ s ∈ S, σ⁻¹ * s * σ ∈ S) → Fx σ)
    (tt : G) (htt : tt ∈ M.P) (y0 : G) (hy0 : y0 ∈ E) (hy01 : y0 ≠ 1)
    (hfin : ∀ κ : G → G → ZMod 2,
      (∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ E, κ (x * x') y = κ x y + κ x' y) →
      (∀ x ∈ S, ∀ y ∈ E, ∀ y' ∈ E, κ x (y * y') = κ x y + κ x y') →
      (∀ w ∈ E, ∀ y ∈ E, κ w y = 0) →
      (∀ x ∈ S, κ x (x ^ 2) = 0) →
      (∀ s ∈ S, ∀ t ∈ E, κ (tt * s * tt⁻¹) (tt * t * tt⁻¹) = κ s t) →
      ∀ σ ∈ M.A, Fx σ → σ ∉ M.P →
        (∀ s ∈ S, ∀ t ∈ E, κ (σ * s * σ⁻¹) (σ * t * σ⁻¹) = κ s t) →
        ∀ s ∈ S, ∀ t ∈ E, κ s t = 0)
    (P : Sylow 2 K) (φ : MulAut K)
    (hφP : ∀ x : K, x ∈ (P : Subgroup K) ↔ φ x ∈ (P : Subgroup K)) :
    ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSfin : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; positivity)
  set Z : Subgroup K := Subgroup.center K with hZdef
  have hZc : ∀ z ∈ Z, ∀ g : K, g * z = z * g := fun z hz g => Subgroup.mem_center_iff.1 hz g
  have hZ2 : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)
  have hZP : Z ≤ (P : Subgroup K) := hZ2.le_sylow_of_normal P
  let π : K →* K ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hT2 : IsPGroup 2 ((P : Subgroup K).map π) := P.isPGroup'.map π
  have hTi : ¬ 2 ∣ ((P : Subgroup K).map π).index := fun h =>
    P.not_dvd_index (h.trans (Subgroup.index_map_dvd (P : Subgroup K) hπ))
  let T : Sylow 2 (K ⧸ Z) := hT2.toSylow hTi
  obtain ⟨g, hg⟩ := exists_conj_of_sylow M.P M.e S hSP hS hK hm T
  set M' : AutModel (K ⧸ Z) G := M.twist (MulAut.conj g⁻¹) with hM'
  have hmem : ∀ k : K ⧸ Z, k ∈ (T : Subgroup (K ⧸ Z)) ↔ ((M'.e k : M'.P) : G) ∈ S := by
    intro k
    rw [hg k, hM', AutModel.twist_e, MulAut.conj_apply, inv_inv]
  let φb : MulAut (K ⧸ Z) := QuotientGroup.congr Z Z φ (Subgroup.map_center_eq φ)
  have hφb : ∀ x : K, φb (π x) = π (φ x) := fun x => rfl
  let σ : G := (M'.Φ φb : G)
  have hσA : σ ∈ M.A := (M'.Φ φb).2
  by_cases hσP : σ ∈ M.P
  ·
    obtain ⟨kb, hkb⟩ := M'.inner_of_mem φb hσP
    obtain ⟨k, rfl⟩ := hπ kb
    refine ⟨k, fun x => ?_⟩
    have hconj : (φ : K →* K) = (MulAut.conj k : K →* K) := by
      apply eq_of_central_diff hperf Z hZc
      intro x
      rw [← hker, MonoidHom.mem_ker]
      have h1 := hkb (π x)
      rw [hφb] at h1
      change π (φ x) * (π (k * x * k⁻¹))⁻¹ = 1
      rw [map_mul, map_mul, map_inv, ← h1]
      group
    have := congrArg (fun f : K →* K => f x) hconj
    simpa using this
  · exfalso
    let ε : K →* G := M'.P.subtype.comp (M'.e.toMonoidHom.comp π)
    have hεapp : ∀ k, ε k = ((M'.e (π k) : M'.P) : G) := fun k => rfl
    have hεker : ε.ker = Z := by
      ext k
      rw [MonoidHom.mem_ker, hεapp]
      constructor
      · intro h
        have h1 : M'.e (π k) = 1 := Subtype.ext h
        have h2 : π k = 1 := M'.e.map_eq_one_iff.1 h1
        rw [← hker]
        exact h2
      · intro h
        have h2 : π k = 1 := by rw [← MonoidHom.mem_ker, hker]; exact h
        rw [h2, map_one]
        rfl
    have hεsurj : ∀ s ∈ M.P, ∃ k, ε k = s := by
      intro s hs
      obtain ⟨kb, hkb⟩ := M'.e.surjective ⟨s, hs⟩
      obtain ⟨k, rfl⟩ := hπ kb
      exact ⟨k, congrArg Subtype.val hkb⟩
    have hPε : ∀ k : K, k ∈ (P : Subgroup K) ↔ ε k ∈ S := by
      intro k
      rw [hεapp, ← hmem]
      constructor
      · intro hk
        exact Subgroup.mem_map_of_mem π hk
      · intro hk
        obtain ⟨p, hp, hpk⟩ := (Subgroup.mem_map).1 hk
        have h1 : p⁻¹ * k ∈ Z := by
          rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hpk, inv_mul_cancel]
        have h2 : k = p * (p⁻¹ * k) := by group
        rw [h2]
        exact (P : Subgroup K).mul_mem hp (hZP h1)
    have hcommE : ∀ a : K, ε a ∈ E → ∀ x ∈ (P : Subgroup K), a * x * a⁻¹ * x⁻¹ ∈ Z := by
      intro a ha x hx
      rw [← hεker, MonoidHom.mem_ker]
      have h1 := hEz _ ha (ε x) ((hPε x).1 hx)
      simp only [map_mul, map_inv]
      calc ε a * ε x * (ε a)⁻¹ * (ε x)⁻¹ = (ε x * ε a) * (ε a)⁻¹ * (ε x)⁻¹ := by rw [h1]
        _ = 1 := by group
    have hAab : ∀ a b : K, ε a ∈ E → ε b ∈ E → a * b = b * a := by
      intro a b ha hb
      exact hMF1 P a ((hPε a).2 (hES ha)) b ((hPε b).2 (hES hb)) (hcommE a ha) (hcommE b hb)
    have hnd : ∀ a : K, ε a ∈ E → ε a ≠ 1 → ∃ p : K, ε p ∈ S ∧ p * a * p⁻¹ * a⁻¹ ≠ 1 := by
      intro a ha ha1
      have haP : a ∈ (P : Subgroup K) := (hPε a).2 (hES ha)
      have haZ : a ∉ Z := fun h => ha1 (by
        have : a ∈ ε.ker := by rw [hεker]; exact h
        exact this)
      obtain ⟨z0, hz0, hz01, -⟩ := exists_unique_ne_one_of_card_two Z hZcard
      obtain ⟨x, hxP, hx⟩ := hMF2 P a haP (hcommE a ha) haZ z0 hz0
      refine ⟨x, (hPε x).1 hxP, ?_⟩
      rw [hx]
      exact hz01
    obtain ⟨κ, h1, h2, h3, h4, h5, h7⟩ := exists_kappa ε Z hZc hZcard hεker S E hES hEz
      (fun s hs => hεsurj s (hSP hs)) hAab hnd
    obtain ⟨tk, htk⟩ := hεsurj tt htt
    have hψt : ∀ k, ε (MulAut.conj tk k) = tt * ε k * tt⁻¹ := by
      intro k
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, htk]
    have h4t := h4 (MulAut.conj tk) tt hψt
    have hψσ : ∀ k, ε (φ k) = σ * ε k * σ⁻¹ := by
      intro k
      have := M'.spec φb (π k)
      rw [hφb] at this
      exact this
    have h4σ := h4 φ σ hψσ
    have hσnorm : ∀ s ∈ S, σ * s * σ⁻¹ ∈ S := by
      intro s hs
      obtain ⟨t, ht⟩ := M'.e.surjective ⟨s, hSP hs⟩
      have hst : ((M'.e t : M'.P) : G) = s := congrArg Subtype.val ht
      have htT : t ∈ (T : Subgroup (K ⧸ Z)) := (hmem t).2 (by rw [hst]; exact hs)
      obtain ⟨p, hp, rfl⟩ := (Subgroup.mem_map).1 htT
      have hφp : φ p ∈ (P : Subgroup K) := (hφP p).1 hp
      have h6 := M'.spec φb (π p)
      rw [hφb, hst] at h6
      rw [← h6]
      exact (hmem _).1 (Subgroup.mem_map_of_mem π hφp)
    have hσfix : Fx σ := hfix σ hσnorm (conj_mem_inv S σ hσnorm)
    have hzero := hfin κ h1 h2 h3 h5 h4t σ hσA hσfix hσP h4σ
    obtain ⟨x, hxS, hx⟩ := h7 y0 hy0 hy01
    exact hx (hzero x hxS y0 hy0)

end CFSG.GH74.KGroups

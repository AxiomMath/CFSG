module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.AGLEmbedding.BlockCyc

open Equiv

section Perm

theorem perm_five_centralizer (c r : Perm (Fin 5)) (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1)
    (h : c * r = r * c) : ∃ k : Fin 5, r = c ^ (k : ℕ) := by
  revert c r
  decide +kernel

theorem card_inf_centralizer_modEq_of_pow {G : Type*} [Group G] [Finite G] {R : Subgroup G}
    {y : G} (hy : y ∈ Subgroup.normalizer (R : Set G)) {p a : ℕ} [Fact p.Prime]
    (hya : y ^ p ^ a = 1) :
    Nat.card R ≡ Nat.card (R ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) [MOD p] := by
  classical
  have : Fintype R := Fintype.ofFinite R
  let f : Function.End R := fun u => ⟨y * u * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy u).1 u.2⟩
  have hfpow : ∀ k : ℕ, ∀ u : R, ((f ^ k) u : G) = y ^ k * u * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u; simp; rfl
    | succ k ih =>
      intro u
      rw [pow_succ]
      change ((f ^ k) (f u) : G) = _
      rw [ih]
      change y ^ k * (y * u * y⁻¹) * (y ^ k)⁻¹ = _
      group
  have hf1 : f ^ p ^ a = 1 := by
    funext u
    apply Subtype.ext
    rw [hfpow, hya]
    simp; rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := R) hf1
  set C : Subgroup G := R ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hfix : Fintype.card f.fixedPoints = Nat.card C := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ⟨fun u => ⟨(u.1 : G), u.1.2, ?_⟩, fun c => ⟨⟨c.1, c.2.1⟩, ?_⟩, ?_, ?_⟩
    · have hu : f u.1 = u.1 := u.2
      have h1 : y * (u.1 : G) * y⁻¹ = u.1 := congrArg Subtype.val hu
      show (u.1 : G) ∈ Subgroup.centralizer ({y} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact (mul_inv_eq_iff_eq_mul.1 h1)
    · have h1 : y * (c.1 : G) = c.1 * y :=
        Subgroup.mem_centralizer_iff.1 c.2.2 y rfl
      show f ⟨c.1, c.2.1⟩ = ⟨c.1, c.2.1⟩
      apply Subtype.ext
      show y * (c.1 : G) * y⁻¹ = c.1
      rw [h1]; group
    · intro u; rfl
    · intro c; rfl
  rw [← Nat.card_eq_fintype_card, hfix] at hmod
  exact hmod

theorem eq_bot_of_perm_five_normalizes {R : Subgroup (Perm (Fin 5))} (hR : IsPGroup 2 R)
    {c : Perm (Fin 5)} (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1)
    (hc : c ∈ Subgroup.normalizer (R : Set (Perm (Fin 5)))) : R = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := card_inf_centralizer_modEq_of_pow hc (p := 5) (a := 1) (by simpa using hc5)
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hk3 : k ≤ 3 := by
    by_contra hk3
    have h16 : 2 ^ 4 ∣ Nat.card R := by
      rw [hk]
      exact pow_dvd_pow 2 (by omega)
    have h120 : Nat.card R ∣ Nat.card (Perm (Fin 5)) := Subgroup.card_subgroup_dvd_card R
    have hcard : Nat.card (Perm (Fin 5)) = 120 := by
      rw [Nat.card_perm]
      simp [Nat.factorial]
    rw [hcard] at h120
    have := h16.trans h120
    norm_num at this
  set C : Subgroup (Perm (Fin 5)) := R ⊓ Subgroup.centralizer ({c} : Set (Perm (Fin 5))) with hC
  have hCR : C ≤ R := inf_le_left
  have hCp : IsPGroup 2 C := hR.to_le hCR
  obtain ⟨j, hj⟩ := hCp.exists_card_eq
  have hjk : j ≤ k := by
    have hd : Nat.card C ∣ Nat.card R := Subgroup.card_dvd_of_le hCR
    rw [hj, hk] at hd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd
  have hjk' : j = k := by
    rw [hj, hk] at hmod
    interval_cases k <;> interval_cases j <;> first | rfl | (exfalso; revert hmod; decide)
  have hCeq : C = R := Subgroup.eq_of_le_of_card_ge hCR (by rw [hj, hk, hjk'])
  have hcomm : ∀ r ∈ R, c * r = r * c := fun r hr => by
    have : r ∈ C := hCeq ▸ hr
    exact Subgroup.mem_centralizer_iff.1 this.2 c rfl
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨i, hi⟩ := perm_five_centralizer c r hc5 hc1 (hcomm r hr)
  obtain ⟨m, hm⟩ := hR ⟨r, hr⟩
  have hrm : r ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hord : orderOf c = 5 := orderOf_eq_prime hc5 hc1
  have hdvd : 5 ∣ (i : ℕ) * 2 ^ m := by
    have hrm' : c ^ ((i : ℕ) * 2 ^ m) = 1 := by rw [pow_mul, ← hi]; exact hrm
    have := orderOf_dvd_of_pow_eq_one hrm'
    rwa [hord] at this
  have hi0 : (i : ℕ) = 0 := by
    have h5 : ¬ 5 ∣ 2 ^ m := by
      intro h
      have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h : 5 ∣ 2)
      omega
    have : 5 ∣ (i : ℕ) :=
      ((Nat.Prime.dvd_mul (by norm_num)).1 hdvd).resolve_right h5
    have := i.2
    omega
  rw [hi, hi0, pow_zero]
  exact Subgroup.one_mem _

end Perm

section Core

variable {A : Type*} [Group A]

theorem eq_one_of_five_normalizes_two_group {Q R : Subgroup A} [Group.IsPerfect Q]
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 5))
    (hZ : ¬ 5 ∣ Nat.card (Subgroup.center Q))
    (hRQ : R ≤ Subgroup.normalizer (Q : Set A)) (hR : IsPGroup 2 R)
    (hRc : ¬ R ≤ Subgroup.centralizer (Q : Set A)) {x : A} (hxQ : x ∈ Q)
    (hxR : x ∈ Subgroup.normalizer (R : Set A)) (hx5 : x ^ 5 = 1) : x = 1 := by
  classical
  let E5 : Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)) :
      Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
        (by norm_num))
  let ι : MulAut Q →* Perm (Fin 5) :=
    E5.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Q))
  have hι : Function.Injective ι := fun a b hab =>
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Q
      ((MulAut.congr e).injective (E5.symm.injective hab))
  let ρ : (Subgroup.normalizer (Q : Set A)) →* MulAut Q := Subgroup.normalizerMonoidHom Q
  let χ : (Subgroup.normalizer (Q : Set A)) →* Perm (Fin 5) := ι.comp ρ
  have hρ : ∀ (g : Subgroup.normalizer (Q : Set A)) (q : Q), ((ρ g q : Q) : A) = g * q * g⁻¹ :=
    fun g q => rfl
  have hχ : ∀ g : Subgroup.normalizer (Q : Set A), χ g = 1 → ∀ q ∈ Q, (g : A) * q = q * g := by
    intro g hg q hq
    have h1 : ρ g = 1 := hι (by rw [map_one]; exact hg)
    have h2 := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : A)) h1
    simp only [hρ, MulAut.one_apply, Subgroup.coe_inv] at h2
    exact mul_inv_eq_iff_eq_mul.1 h2
  let R' : Subgroup (Perm (Fin 5)) :=
    (R.subgroupOf (Subgroup.normalizer (Q : Set A))).map χ
  have hR' : IsPGroup 2 R' := hR.comap_subtype.map χ
  have hxN : x ∈ Subgroup.normalizer (Q : Set A) := Subgroup.le_normalizer hxQ
  set c : Perm (Fin 5) := χ ⟨x, hxN⟩ with hcdef
  have hc5 : c ^ 5 = 1 := by
    rw [hcdef, ← map_pow]
    have : (⟨x, hxN⟩ : Subgroup.normalizer (Q : Set A)) ^ 5 = 1 := Subtype.ext hx5
    rw [this, map_one]
  have hcR' : c ∈ Subgroup.normalizer (R' : Set (Perm (Fin 5))) := by
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨r, hr, rfl⟩
    have hrR : ((r : Subgroup.normalizer (Q : Set A)) : A) ∈ R := hr
    have hxr : x * (r : A) * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hxR (r : A)).1 hrR
    have hmem : (⟨x, hxN⟩ : Subgroup.normalizer (Q : Set A)) * r * ⟨x, hxN⟩⁻¹ ∈
        R.subgroupOf (Subgroup.normalizer (Q : Set A)) := hxr
    have : c * χ r * c⁻¹ = χ (⟨x, hxN⟩ * r * ⟨x, hxN⟩⁻¹) := by
      rw [hcdef, map_mul, map_mul, map_inv]
    rw [this]
    exact Subgroup.mem_map_of_mem χ hmem
  have hc1 : c = 1 := by
    by_contra hc1
    have hbot : R' = ⊥ := eq_bot_of_perm_five_normalizes hR' hc5 hc1 hcR'
    obtain ⟨r, hrR, hrc⟩ := Set.not_subset.1 hRc
    have hrN : r ∈ Subgroup.normalizer (Q : Set A) := hRQ hrR
    have hχr : χ ⟨r, hrN⟩ = 1 := by
      have hmem : χ ⟨r, hrN⟩ ∈ R' := Subgroup.mem_map_of_mem χ
        (show (⟨r, hrN⟩ : Subgroup.normalizer (Q : Set A)) ∈
          R.subgroupOf (Subgroup.normalizer (Q : Set A)) from hrR)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    apply hrc
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hχ ⟨r, hrN⟩ hχr q hq).symm
  have hxz : (⟨x, hxQ⟩ : Q) ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (hχ ⟨x, hxN⟩ hc1 q q.2).symm
  have hz5 : (⟨⟨x, hxQ⟩, hxz⟩ : Subgroup.center Q) ^ 5 = 1 := Subtype.ext (Subtype.ext hx5)
  have hord : orderOf (⟨⟨x, hxQ⟩, hxz⟩ : Subgroup.center Q) ∣ 5 := orderOf_dvd_of_pow_eq_one hz5
  have hdvd := orderOf_dvd_natCard (⟨⟨x, hxQ⟩, hxz⟩ : Subgroup.center Q)
  have h1 : orderOf (⟨⟨x, hxQ⟩, hxz⟩ : Subgroup.center Q) = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hord with h | h
    · exact h
    · exact absurd (h ▸ hdvd) hZ
  have h0 := orderOf_eq_one_iff.1 h1
  exact congrArg Subtype.val (congrArg Subtype.val h0)

end Core

end CFSG.AGLEmbedding.BlockCyc

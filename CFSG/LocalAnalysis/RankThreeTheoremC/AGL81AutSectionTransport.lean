module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionDefs
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTorus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open CFSG.Open

@[expose] def AutomizerBound (p q : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W],
    Module.finrank (ZMod q) W ≤ 4 → ∀ P : Subgroup (Module.End (ZMod q) W)ˣ, IsPGroup p P →
    IsMulCommutative P → ∀ g ∈ Subgroup.normalizer (P : Set (Module.End (ZMod q) W)ˣ),
      (∀ x ∈ P, g ^ 3 * x * (g ^ 3)⁻¹ = x) ∨ (∀ x ∈ P, g ^ 4 * x * (g ^ 4)⁻¹ = x)

theorem eq_one_of_coprime_prime_pows {G : Type*} [Group G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) {x : G} {m n : ℕ} (hm : x ^ (p ^ m) = 1) (hn : x ^ (q ^ n) = 1) :
    x = 1 := by
  have h1 : orderOf x ∣ p ^ m := orderOf_dvd_of_pow_eq_one hm
  have h2 : orderOf x ∣ q ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime (p ^ m) (q ^ n) :=
    Nat.Coprime.pow m n ((Nat.coprime_primes hp hq).mpr hpq)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem dvd_pow_sub_one_iff_orderOf_dvd {p q : ℕ} [hp : Fact p.Prime] (hq : q.Prime)
    (hpq : p ≠ q) (j : ℕ) : p ∣ q ^ j - 1 ↔ orderOf (q : ZMod p) ∣ j := by
  have h1 : 1 ≤ q ^ j := Nat.one_le_pow _ _ hq.pos
  rw [orderOf_dvd_iff_pow_eq_one, ← Nat.cast_pow, ← (Nat.cast_one (R := ZMod p)),
    ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm, Nat.modEq_iff_dvd' h1]

theorem smallAutomizer_of_surjective {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hp5 : 5 ≤ p) (hpq : p ≠ q) (hauto : AutomizerBound p q) {V : Type} [Group V] [Finite V]
    (hM : HasSmallLinearModel q V) (A : Subgroup (MulAut V)) {K : Type} [Group K] [Finite K]
    (φ : ↥A →* K) (hφ : Function.Surjective φ) : SmallAutomizer p K := by
  obtain ⟨W, _, _, _, hW, ρ, hker⟩ := hM
  haveI : Finite (MulAut V) := MulEquiv.finite_left
  set ρ' : ↥A →* (Module.End (ZMod q) W)ˣ := ρ.comp A.subtype with hρ'
  have hinj : ∀ {P : Subgroup ↥A}, IsPGroup p P → ∀ x ∈ P, ∀ y ∈ P, ρ' x = ρ' y → x = y := by
    intro P hP x hx y hy hxy
    have h1 : ρ (x * y⁻¹ : ↥A) = 1 := by
      have : ρ' (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
      exact this
    obtain ⟨k, hk⟩ := hker _ h1
    obtain ⟨m, hm⟩ := hP ⟨x * y⁻¹, P.mul_mem hx (P.inv_mem hy)⟩
    have hm' : (x * y⁻¹) ^ (p ^ m) = 1 := by
      simpa using congrArg Subtype.val hm
    have hk' : (x * y⁻¹) ^ (q ^ k) = 1 := by
      apply Subtype.ext
      simpa using hk
    exact mul_inv_eq_one.mp (eq_one_of_coprime_prime_pows hp.out hq.out hpq hm' hk')
  have hcard : ¬ p ∣ Nat.card (ZMod q) := by
    rw [Nat.card_zmod]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp h)
  have hcop : Nat.Coprime q p := (Nat.coprime_primes hq.out hp.out).mpr hpq.symm
  have hord : 0 < orderOf (q : ZMod p) := by
    have := orderOf_pos (ZMod.unitOfCoprime q hcop)
    rwa [← orderOf_units, ZMod.coe_unitOfCoprime] at this
  have habGL : ∀ {P : Subgroup ↥A}, IsPGroup p P → IsMulCommutative (P.map ρ') := by
    intro P hP
    refine CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_of_isPGroup_GL
      (Nat.Prime.odd_of_ne_two hp.out (by omega)) hcard hord ?_ ?_ (hP.map ρ')
    · intro j
      rw [Nat.card_zmod]
      exact dvd_pow_sub_one_iff_orderOf_dvd hq.out hpq j
    · calc Module.finrank (ZMod q) W / orderOf (q : ZMod p) ≤ Module.finrank (ZMod q) W :=
            Nat.div_le_self _ _
        _ ≤ 4 := hW
        _ < p := by omega
  have hab : ∀ {P : Subgroup ↥A}, IsPGroup p P → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro P hP x hx y hy
    have h := (habGL hP).is_comm.comm ⟨ρ' x, x, hx, rfl⟩ ⟨ρ' y, y, hy, rfl⟩
    refine hinj hP _ (P.mul_mem hx hy) _ (P.mul_mem hy hx) ?_
    rw [map_mul, map_mul]
    exact congrArg Subtype.val h
  intro T
  obtain ⟨P, hPT⟩ := Sylow.mapSurjective_surjective hφ p T
  have hTP : (T : Subgroup K) = (P : Subgroup ↥A).map φ := by
    rw [← hPT]
    rfl
  have hPp : IsPGroup p (P : Subgroup ↥A) := P.isPGroup'
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun k hk => ?_⟩
  ·
    obtain ⟨x, hx, hxa⟩ := (Subgroup.mem_map.mp (hTP ▸ a.2 : (a : K) ∈ (P : Subgroup ↥A).map φ))
    obtain ⟨y, hy, hyb⟩ := (Subgroup.mem_map.mp (hTP ▸ b.2 : (b : K) ∈ (P : Subgroup ↥A).map φ))
    apply Subtype.ext
    change (a : K) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, hab hPp x hx y hy]
  ·
    obtain ⟨a, rfl⟩ := hφ k
    set H : Subgroup ↥A := (T : Subgroup K).comap φ with hH
    have hPH : (P : Subgroup ↥A) ≤ H := fun x hx => by
      rw [hH, Subgroup.mem_comap, hTP]
      exact ⟨x, hx, rfl⟩
    have haPH : ((a • P : Sylow p ↥A) : Subgroup ↥A) ≤ H := by
      intro x hx
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      rw [hH, Subgroup.mem_comap]
      have hx' : a⁻¹ * x * a ∈ (P : Subgroup ↥A) := by
        simpa [MulAut.smul_def, MulAut.conj_apply] using hx
      have h1 : φ (a⁻¹ * x * a) ∈ (T : Subgroup K) := by
        rw [hTP]
        exact ⟨_, hx', rfl⟩
      have h2 : φ x = φ a * φ (a⁻¹ * x * a) * (φ a)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        group
      rw [h2]
      exact (Subgroup.mem_normalizer_iff.mp hk _).mp h1
    haveI : Finite ↥H := inferInstance
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥H ((a • P).subtype haPH) (P.subtype hPH)
    have hhP : ((h : ↥A) * a) • P = P := by
      have h1 := hh
      rw [Sylow.smul_subtype] at h1
      have h2 : ((h • (a • P) : Sylow p ↥A) : Subgroup ↥A) = (P : Subgroup ↥A) := by
        have h3 := congrArg (fun S : Sylow p ↥H => (S : Subgroup ↥H)) h1
        simp only [Sylow.coe_subtype] at h3
        rw [Subgroup.subgroupOf_inj, inf_of_le_left (Sylow.smul_le haPH h),
          inf_of_le_left hPH] at h3
        exact h3
      rw [mul_smul]
      exact Sylow.ext h2
    set n : ↥A := (h : ↥A) * a with hn
    have hnP : n ∈ Subgroup.normalizer ((P : Subgroup ↥A) : Set ↥A) :=
      Sylow.smul_eq_iff_mem_normalizer.mp hhP
    have hnφ : φ n = φ h * φ a := map_mul _ _ _
    have hφh : φ h ∈ (T : Subgroup K) := h.2
    have hnorm : ρ' n ∈ Subgroup.normalizer ((P.map ρ' : Subgroup _) : Set _) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨n * x * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnP x).mp hx, by
          rw [map_mul, map_mul, map_inv]⟩
      · rintro ⟨x, hx, hxy⟩
        refine ⟨n⁻¹ * x * n, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnP) x).mp hx
          rwa [inv_inv] at this
        · rw [map_mul, map_mul, map_inv, hxy]
          group
    have hbound := hauto W hW (P.map ρ') (hPp.map ρ') (habGL hPp) (ρ' n) hnorm
    have hpow : ∀ e : ℕ, (∀ x ∈ P.map ρ', ρ' n ^ e * x * (ρ' n ^ e)⁻¹ = x) →
        ∀ x ∈ (P : Subgroup ↥A), n ^ e * x * (n ^ e)⁻¹ = x := by
      intro e he x hx
      have hmem : n ^ e * x * (n ^ e)⁻¹ ∈ (P : Subgroup ↥A) :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hnP e) x).mp hx
      refine hinj hPp _ hmem _ hx ?_
      rw [map_mul, map_mul, map_inv, map_pow]
      exact he _ ⟨x, hx, rfl⟩
    have hT : ∀ e : ℕ, (∀ x ∈ (P : Subgroup ↥A), n ^ e * x * (n ^ e)⁻¹ = x) →
        ∀ t ∈ (T : Subgroup K), φ a ^ e * t * (φ a ^ e)⁻¹ = t := by
      intro e he t ht
      have hcomm : ∀ s ∈ (T : Subgroup K), ∀ u ∈ (T : Subgroup K), s * u = u * s := by
        intro s hs u hu
        rw [hTP] at hs hu
        obtain ⟨x, hx, rfl⟩ := hs
        obtain ⟨y, hy, rfl⟩ := hu
        rw [← map_mul, ← map_mul, hab hPp x hx y hy]
      have hconj : ∀ e' : ℕ, ∀ t ∈ (T : Subgroup K),
          φ n ^ e' * t * (φ n ^ e')⁻¹ = φ a ^ e' * t * (φ a ^ e')⁻¹ := by
        intro e'
        induction e' with
        | zero => intro t _; simp
        | succ m ih =>
          intro t ht
          have hk' : ∀ s ∈ (T : Subgroup K), φ a * s * (φ a)⁻¹ ∈ (T : Subgroup K) :=
            fun s hs => (Subgroup.mem_normalizer_iff.mp hk s).mp hs
          have hnt : φ n ^ m * t * (φ n ^ m)⁻¹ ∈ (T : Subgroup K) := by
            rw [ih t ht]
            have : ∀ r : ℕ, ∀ s ∈ (T : Subgroup K),
                φ a ^ r * s * (φ a ^ r)⁻¹ ∈ (T : Subgroup K) := by
              intro r
              induction r with
              | zero => intro s hs; simpa using hs
              | succ r ihr =>
                intro s hs
                have := hk' _ (ihr s hs)
                simpa [pow_succ', mul_assoc] using this
            exact this m t ht
          calc φ n ^ (m + 1) * t * (φ n ^ (m + 1))⁻¹
              = φ n * (φ n ^ m * t * (φ n ^ m)⁻¹) * (φ n)⁻¹ := by group
            _ = φ h * (φ a * (φ a ^ m * t * (φ a ^ m)⁻¹) * (φ a)⁻¹) * (φ h)⁻¹ := by
                rw [ih t ht, hnφ]
                group
            _ = φ a * (φ a ^ m * t * (φ a ^ m)⁻¹) * (φ a)⁻¹ := by
                have hmem : φ a * (φ a ^ m * t * (φ a ^ m)⁻¹) * (φ a)⁻¹ ∈ (T : Subgroup K) := by
                  rw [← ih t ht]
                  exact hk' _ hnt
                rw [hcomm _ hφh _ hmem, mul_assoc, mul_inv_cancel, mul_one]
            _ = φ a ^ (m + 1) * t * (φ a ^ (m + 1))⁻¹ := by group
      rw [← hconj e t ht]
      rw [hTP] at ht
      obtain ⟨x, hx, rfl⟩ := ht
      rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, he x hx]
    rcases hbound with h3 | h4
    · exact Or.inl (hT 3 (hpow 3 h3))
    · exact Or.inr (hT 4 (hpow 4 h4))

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

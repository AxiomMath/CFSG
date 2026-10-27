module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement

theorem conj_commutatorElement_eq_zpow {T : Type*} [Group T] {x y z₀ : T} {K : ℤ}
    (hz : ∀ g, g * z₀ = z₀ * g) (hK : y * x * y⁻¹ = x ^ K * z₀) :
    y * ⁅x, y⁆ * y⁻¹ = ⁅x, y⁆ ^ K := by
  have hxz : Commute x z₀ := hz x
  have hconj : ∀ n : ℤ, y * x ^ n * y⁻¹ = x ^ (K * n) * z₀ ^ n := fun n => by
    have h1 : y * x ^ n * y⁻¹ = (y * x * y⁻¹) ^ n := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [h1, hK, (hxz.zpow_left K).mul_zpow, zpow_mul]
  have hc : ⁅x, y⁆ = x ^ (1 - K) * z₀⁻¹ := by
    have h2 : ⁅x, y⁆ = x * (y * x ^ (-1 : ℤ) * y⁻¹) := by
      rw [commutatorElement_def, zpow_neg_one]; group
    rw [h2, hconj, ← mul_assoc, ← zpow_one_add, zpow_neg_one, mul_neg_one]
    ring_nf
  have hy : Commute y z₀⁻¹ := (show Commute y z₀ from hz y).inv_right
  have hsplit : y * (x ^ (1 - K) * z₀⁻¹) * y⁻¹ =
      (y * x ^ (1 - K) * y⁻¹) * (y * z₀⁻¹ * y⁻¹) := by group
  have hyz : y * z₀⁻¹ * y⁻¹ = z₀⁻¹ := by rw [hy.eq, mul_inv_cancel_right]
  have hcomm : Commute (x ^ (1 - K)) z₀⁻¹ := (hxz.inv_right).zpow_left _
  rw [hc, hsplit, hyz, hconj, hcomm.mul_zpow, ← zpow_mul, inv_zpow', mul_assoc,
    ← zpow_sub_one]
  congr 2 <;> ring

theorem isCyclic_commutator_of_metacyclic_quotient {T S : Type*} [Group T] [Group S] [Finite T]
    {f : T →* S} (hf : Function.Surjective f) (hZ : f.ker ≤ center T) {N : Subgroup S}
    [hNn : N.Normal] (hN : IsCyclic N) (hSN : IsCyclic (S ⧸ N)) : IsCyclic (commutator T) := by
  obtain ⟨n₀, hn₀⟩ := hN.exists_generator
  obtain ⟨s₀, hs₀⟩ := hSN.exists_generator
  obtain ⟨x, hx⟩ := hf (n₀ : S)
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective s₀
  obtain ⟨y, rfl⟩ := hf s
  have hM : ∀ m, f m ∈ N → ∃ k : ℤ, ∃ z ∈ f.ker, m = x ^ k * z := fun m hm => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hn₀ ⟨f m, hm⟩)
    refine ⟨k, (x ^ k)⁻¹ * m, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hx]
    have := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_zpow] at this
    rw [this, inv_mul_cancel]
  have hT : ∀ t, ∃ k : ℕ, f ((y ^ k)⁻¹ * t) ∈ N := fun t => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hs₀ (f t : S ⧸ N))
    have hy : y ^ k ∈ Submonoid.powers y :=
      (mem_powers_iff_mem_zpowers).2 (zpow_mem_zpowers y k)
    obtain ⟨k', hk'⟩ := hy
    have hk'' : y ^ k' = y ^ k := hk'
    refine ⟨k', ?_⟩
    rw [hk'', map_mul, map_inv, map_zpow, ← QuotientGroup.eq, ← hk]
    simp
  have hcen : ∀ z ∈ f.ker, ∀ g : T, g * z = z * g := fun z hz g =>
    mem_center_iff.1 (hZ hz) g
  have hMcomm : ∀ m m', f m ∈ N → f m' ∈ N → Commute m m' := fun m m' hm hm' => by
    obtain ⟨a, z, hz, rfl⟩ := hM m hm
    obtain ⟨b, z', hz', rfl⟩ := hM m' hm'
    refine Commute.mul_left (Commute.mul_right ((Commute.refl x).zpow_zpow a b) ?_) ?_
    · exact (hcen z' hz' _)
    · exact Commute.mul_right (hcen z hz _).symm (hcen z' hz' z)
  set c := ⁅x, y⁆ with hc
  have hcN : f c ∈ N := by
    have : f c = n₀ * (f y * (n₀ : S)⁻¹ * (f y)⁻¹) := by
      rw [hc, map_commutatorElement, commutatorElement_def, hx]; group
    rw [this]
    exact N.mul_mem n₀.2 (hNn.conj_mem _ (N.inv_mem n₀.2) _)
  have hxN : f x ∈ N := by rw [hx]; exact n₀.2
  have hyx : f (y * x * y⁻¹) ∈ N := by
    rw [map_mul, map_mul, map_inv]; exact hNn.conj_mem _ hxN _
  obtain ⟨K, z₀, hz₀, hK⟩ := hM _ hyx
  have hyc : y * c * y⁻¹ = c ^ K := conj_commutatorElement_eq_zpow (hcen z₀ hz₀) hK
  set D := zpowers c
  have hyD : ∀ k : ℕ, y ^ k * c * (y ^ k)⁻¹ ∈ D := fun k => by
    induction k with
    | zero => simp [D]
    | succ k ih =>
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 ih
      have : y ^ (k + 1) * c * (y ^ (k + 1))⁻¹ = y * (y ^ k * c * (y ^ k)⁻¹) * y⁻¹ := by
        rw [pow_succ']; group
      rw [this, ← hj, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hyc, ← zpow_mul]
      exact zpow_mem_zpowers _ _
  have hDn : D.Normal := by
    refine ⟨fun d hd g => ?_⟩
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hd
    obtain ⟨k, hk⟩ := hT g
    have hgc : g * c * g⁻¹ ∈ D := by
      have hm' : (y ^ k)⁻¹ * g * c * ((y ^ k)⁻¹ * g)⁻¹ = c := by
        rw [(hMcomm _ _ hk hcN).eq, mul_inv_cancel_right]
      have : g * c * g⁻¹ = y ^ k * ((y ^ k)⁻¹ * g * c * ((y ^ k)⁻¹ * g)⁻¹) * (y ^ k)⁻¹ := by
        group
      rw [this, hm']
      exact hyD k
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    exact D.zpow_mem hgc j
  have hdecomp : ∀ t : T, ∃ i : ℕ, ∃ p : ℤ, ∃ z ∈ f.ker, t = y ^ i * x ^ p * z := fun t => by
    obtain ⟨i, hi⟩ := hT t
    obtain ⟨p, z, hz, hpz⟩ := hM _ hi
    exact ⟨i, p, z, hz, by rw [mul_assoc, ← hpz]; group⟩
  have hxy : Commute (x : T ⧸ D) (y : T ⧸ D) := by
    rw [← commutatorElement_eq_one_iff_commute]
    change ⁅QuotientGroup.mk' D x, QuotientGroup.mk' D y⁆ = 1
    rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact mem_zpowers c
  have hzc : ∀ z ∈ f.ker, ∀ u : T ⧸ D, Commute (z : T ⧸ D) u := fun z hz u => by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective u
    change ((z * w : T) : T ⧸ D) = ((w * z : T) : T ⧸ D)
    rw [← hcen z hz w]
  have hcomm : ∀ a b : T, ⁅a, b⁆ ∈ D := fun a b => by
    obtain ⟨i, p, z, hz, rfl⟩ := hdecomp a
    obtain ⟨j, q, z', hz', rfl⟩ := hdecomp b
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    simp only [map_mul, map_pow, map_zpow, QuotientGroup.mk'_apply]
    have hYX : Commute (y : T ⧸ D) (x : T ⧸ D) := hxy.symm
    refine Commute.mul_left (Commute.mul_left ?_ ?_) (hzc z hz _)
    · exact Commute.mul_right (Commute.mul_right ((Commute.refl _).pow_pow i j)
        ((hYX.pow_left i).zpow_right q)) (hzc z' hz' _).symm
    · exact Commute.mul_right (Commute.mul_right ((hxy.zpow_left p).pow_right j)
        ((Commute.refl _).zpow_zpow p q)) (hzc z' hz' _).symm
  have hle : commutator T ≤ D := by
    rw [commutator_def]
    exact (Subgroup.commutator_le).2 fun a _ b _ => hcomm a b
  exact Subgroup.isCyclic_of_le hle

theorem exists_sylow_map_eq {E Q : Type*} [Group E] [Group Q] [Finite E] {ℓ : ℕ}
    [Fact ℓ.Prime] {η : E →* Q} (hη : Function.Surjective η) (S : Sylow ℓ Q) :
    ∃ T : Sylow ℓ E, (T : Subgroup E).map η = S := by
  obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hη ℓ S
  exact ⟨T, by rw [← hT, Sylow.coe_mapSurjective]⟩

theorem perfect_central_cover_metacyclic_sylow_prime_kernel_cyclic {E Q : Type*} [Group E]
    [Group Q] [Finite E] [Finite Q] [Group.IsPerfect E] {η : E →* Q}
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) {ℓ : ℕ} [Fact ℓ.Prime]
    (Cℓ : Sylow ℓ η.ker) (S : Sylow ℓ Q)
    (hS : ∃ N : Subgroup S, ∃ _ : N.Normal, IsCyclic N ∧ IsCyclic (S ⧸ N)) :
    IsCyclic Cℓ := by
  obtain ⟨N, hNn, hN, hSN⟩ := hS
  obtain ⟨T, hT⟩ := exists_sylow_map_eq hη S
  let f : (T : Subgroup E) →* S :=
    (η.comp (T : Subgroup E).subtype).codRestrict (S : Subgroup Q) fun t => by
      rw [← hT]; exact Subgroup.mem_map_of_mem _ t.2
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    have hs' := hs
    rw [← hT] at hs'
    obtain ⟨t, ht, rfl⟩ := hs'
    exact ⟨⟨t, ht⟩, rfl⟩
  have hfZ : f.ker ≤ center (T : Subgroup E) := fun t ht => by
    have ht' : (t : E) ∈ η.ker := by
      rw [MonoidHom.mem_ker]
      simpa [f] using congrArg Subtype.val ht
    refine mem_center_iff.2 fun u => Subtype.ext ?_
    exact mem_center_iff.1 (hC ht') u
  have := hNn
  have hcyc : IsCyclic (commutator (T : Subgroup E)) :=
    isCyclic_commutator_of_metacyclic_quotient hf hfZ hN hSN
  set A : Subgroup E := (Cℓ : Subgroup η.ker).map η.ker.subtype
  have hAc : A ≤ center E := by
    rintro _ ⟨c, -, rfl⟩
    exact hC c.2
  have hAp : IsPGroup ℓ A :=
    Cℓ.isPGroup'.map η.ker.subtype
  have hA := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived T A hAc hAp
  let φ : (Cℓ : Subgroup η.ker) →* ((commutator (T : Subgroup E)).map (T : Subgroup E).subtype) :=
    ((η.ker.subtype).comp (Cℓ : Subgroup η.ker).subtype).codRestrict _ fun c =>
      hA ⟨c, c.2, rfl⟩
  have hφ : Function.Injective φ := fun a b h => by
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  have : IsCyclic ((commutator (T : Subgroup E)).map (T : Subgroup E).subtype) :=
    isCyclic_of_surjective _ ((T : Subgroup E).subtype.subgroupMap_surjective _)
  exact isCyclic_of_injective φ hφ

end CFSG.LocalAnalysis.ComponentInitial

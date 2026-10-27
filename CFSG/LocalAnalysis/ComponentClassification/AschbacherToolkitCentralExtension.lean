module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open scoped commutatorElement

section Transfer

variable {E : Type*} [Group E] [Finite E]

theorem central_sylow_commutator {p : ℕ} [Fact p.Prime] (P : Sylow p E)
    {Z : Subgroup E} (hZc : Z ≤ Subgroup.center E) (hZp : IsPGroup p Z) :
    Z ⊓ commutator E =
      Z ⊓ (commutator (P : Subgroup E)).map (P : Subgroup E).subtype := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hzZ, hzD⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨hzZ, ?_⟩
    let τ : E →* Abelianization (P : Subgroup E) :=
      MonoidHom.transfer (Abelianization.of : (P : Subgroup E) →* _)
    have hτ1 : τ z = 1 := Abelianization.commutator_subset_ker τ hzD
    have hzc : z ∈ Subgroup.center E := hZc hzZ
    have hkey : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup E) →
        g₀⁻¹ * z ^ k * g₀ = z ^ k := fun k g₀ _ => by
      have hk : z ^ k ∈ Subgroup.center E := Subgroup.pow_mem _ hzc k
      rw [Subgroup.mem_center_iff] at hk
      rw [mul_assoc, ← hk g₀, ← mul_assoc, inv_mul_cancel, one_mul]
    have hτ2 := MonoidHom.transfer_eq_pow
      (Abelianization.of : (P : Subgroup E) →* Abelianization (P : Subgroup E)) z hkey
    have hmem : (⟨z ^ (P : Subgroup E).index, MonoidHom.transfer_eq_pow_aux z hkey⟩ :
        (P : Subgroup E)) ∈ commutator (P : Subgroup E) := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      exact hτ2.symm.trans hτ1
    have hpow : z ^ (P : Subgroup E).index ∈
        (commutator (P : Subgroup E)).map (P : Subgroup E).subtype := ⟨_, hmem, rfl⟩
    obtain ⟨k, hk⟩ := hZp ⟨z, hzZ⟩
    have hdvd : orderOf z ∣ p ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    have hcop : Nat.Coprime (P : Subgroup E).index (orderOf z) :=
      Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.pow_right k
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr P.not_dvd_index).symm)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem _ hpow m
  · intro z hz
    obtain ⟨hzZ, hzD⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨hzZ, ?_⟩
    have hle : (commutator (P : Subgroup E)).map (P : Subgroup E).subtype ≤ commutator E := by
      rw [map_commutator_eq, _root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact hle hzD

theorem central_sylow_commutator_eq_bot {p : ℕ} [Fact p.Prime] (P : Sylow p E)
    {Z : Subgroup E} (hZc : Z ≤ Subgroup.center E) (hZp : IsPGroup p Z)
    (hP : Z.subgroupOf (P : Subgroup E) ⊓ commutator (P : Subgroup E) = ⊥) :
    Z ⊓ commutator E = ⊥ := by
  rw [central_sylow_commutator P hZc hZp, eq_bot_iff]
  intro z hz
  obtain ⟨hzZ, u, hu, rfl⟩ := Subgroup.mem_inf.mp hz
  have hu' : u ∈ Z.subgroupOf (P : Subgroup E) ⊓ commutator (P : Subgroup E) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hzZ, hu⟩
  rw [hP, Subgroup.mem_bot] at hu'
  rw [hu']
  exact Subgroup.one_mem _

end Transfer

section Generators

variable {P : Type*} [Group P]

theorem commutator_le_of_closure_eq_top (N : Subgroup P) [N.Normal] {S : Set P}
    (hS : Subgroup.closure S = ⊤) (hc : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ N) :
    commutator P ≤ N := by
  let π := QuotientGroup.mk' N
  have hcomm : ∀ g h : P, ⁅g, h⁆ ∈ N ↔ π g * π h = π h * π g := fun g h => by
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).symm
  have hgen : ∀ s ∈ S, ∀ g : P, π s * π g = π g * π s := by
    intro s hs g
    have hle : Subgroup.closure S ≤ (Subgroup.centralizer {π s}).comap π := by
      rw [Subgroup.closure_le]
      intro t ht
      simp only [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm t s).mp (hc t ht s hs)
    have hg := hle (hS ▸ Subgroup.mem_top g)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hg
    exact hg.symm
  have hall : ∀ g h : P, π g * π h = π h * π g := by
    intro g h
    have hle : Subgroup.closure S ≤ (Subgroup.centralizer {π h}).comap π := by
      rw [Subgroup.closure_le]
      intro t ht
      simp only [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact hgen t ht h
    have hg := hle (hS ▸ Subgroup.mem_top g)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hg
    exact hg
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro g _ h _
  exact (hcomm g h).mpr (hall g h)

theorem mem_normalizer_zpowers_of_conj {g w : P}
    (h : g * w * g⁻¹ = w ∨ g * w * g⁻¹ = w⁻¹) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers w : Set P) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  rcases h with h | h
  · simp only [MonoidHom.coe_ofClass, MulAut.conj_apply, h]
  · simp only [MonoidHom.coe_ofClass, MulAut.conj_apply, h, Subgroup.zpowers_inv]

end Generators

section Quaternion

variable {P : Type*} [Group P] {n : ℕ}

theorem quaternion_closure_generators [NeZero n] :
    Subgroup.closure ({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
      Set (QuaternionGroup n)) = ⊤ := by
  rw [eq_top_iff]
  have ha : QuaternionGroup.a 1 ∈ Subgroup.closure ({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
      Set (QuaternionGroup n)) := Subgroup.subset_closure (by simp)
  have hx : QuaternionGroup.xa 0 ∈ Subgroup.closure ({QuaternionGroup.a 1,
      QuaternionGroup.xa 0} : Set (QuaternionGroup n)) := Subgroup.subset_closure (by simp)
  rintro (i | i) -
  · have : QuaternionGroup.a i = (QuaternionGroup.a 1 : QuaternionGroup n) ^ i.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [this]
    exact Subgroup.pow_mem _ ha _
  · have : QuaternionGroup.xa i =
        (QuaternionGroup.a 1 : QuaternionGroup n) ^ (-i).val * QuaternionGroup.xa 0 := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val, QuaternionGroup.a_mul_xa, zero_sub,
        neg_neg]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ ha _) hx

theorem quaternion_central_extension_of_surjective [NeZero n]
    (f : P →* QuaternionGroup n) (hf : Function.Surjective f)
    (hK : f.ker ≤ Subgroup.center P) : f.ker ⊓ commutator P = ⊥ := by
  classical
  obtain ⟨x, hx⟩ := hf (QuaternionGroup.a 1)
  obtain ⟨y, hy⟩ := hf (QuaternionGroup.xa 0)
  have h2n : ((n : ZMod (2 * n)) + n) = 0 := by
    rw [← two_mul]
    exact_mod_cast ZMod.natCast_self (2 * n)
  have hyinv : f y⁻¹ = QuaternionGroup.xa n := by
    rw [map_inv, hy, inv_eq_iff_mul_eq_one, QuaternionGroup.xa_mul_xa, sub_zero, h2n]
    rfl
  set c := y * x * y⁻¹ * x with hc
  have hcK : c ∈ f.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, hyinv, hx, hy,
      QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa, QuaternionGroup.a_mul_a, zero_add,
      sub_add_cancel, h2n]
    rfl
  have hcz : ∀ g : P, g * c = c * g := Subgroup.mem_center_iff.mp (hK hcK)
  have hcz' : ∀ g : P, g * c⁻¹ = c⁻¹ * g :=
    Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ (hK hcK))
  have hyx : y * x * y⁻¹ = c * x⁻¹ := by rw [hc]; group
  set w := x * x * c⁻¹ with hw
  have hxw : x * w * x⁻¹ = w := by
    calc x * w * x⁻¹ = x * x * (x * c⁻¹) * x⁻¹ := by rw [hw]; group
      _ = x * x * (c⁻¹ * x) * x⁻¹ := by rw [hcz' x]
      _ = w := by rw [hw]; group
  have hyw : y * w * y⁻¹ = w⁻¹ := by
    calc y * w * y⁻¹ = (y * x * y⁻¹) * (y * x * y⁻¹) * (y * c⁻¹ * y⁻¹) := by rw [hw]; group
      _ = c * x⁻¹ * (c * x⁻¹) * (c⁻¹ * y * y⁻¹) := by rw [hyx, hcz' y]
      _ = c * (x⁻¹ * c) * x⁻¹ * c⁻¹ := by group
      _ = c * (c * x⁻¹) * x⁻¹ * c⁻¹ := by rw [hcz x⁻¹]
      _ = c * c * (x⁻¹ * x⁻¹ * c⁻¹) := by group
      _ = c * c * (c⁻¹ * (x⁻¹ * x⁻¹)) := by rw [hcz' (x⁻¹ * x⁻¹)]
      _ = w⁻¹ := by rw [hw]; group
  have hxy : ⁅x, y⁆ = w := by
    calc ⁅x, y⁆ = x * (y * x * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      _ = x * (c * x⁻¹)⁻¹ := by rw [hyx]
      _ = x * (x * c⁻¹) := by group
      _ = w := by rw [hw]; group
  let S : Set P := insert x (insert y (f.ker : Set P))
  have hS : Subgroup.closure S = ⊤ := by
    have hmap : (Subgroup.closure S).map f = ⊤ := by
      rw [eq_top_iff, ← quaternion_closure_generators, Subgroup.closure_le]
      rintro q (rfl | rfl)
      · exact ⟨x, Subgroup.subset_closure (by simp [S]), hx⟩
      · exact ⟨y, Subgroup.subset_closure (by simp [S]), hy⟩
    have hker : f.ker ≤ Subgroup.closure S := fun k hk =>
      Subgroup.subset_closure (by simp [S, hk])
    have h := Subgroup.comap_map_eq f (Subgroup.closure S)
    rw [hmap, Subgroup.comap_top, sup_eq_left.mpr hker] at h
    exact h.symm
  have hnorm : (Subgroup.zpowers w).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hS, Subgroup.closure_le]
    rintro s (rfl | rfl | hs)
    · exact mem_normalizer_zpowers_of_conj (Or.inl hxw)
    · exact mem_normalizer_zpowers_of_conj (Or.inr hyw)
    · refine mem_normalizer_zpowers_of_conj (Or.inl ?_)
      have := Subgroup.mem_center_iff.mp (hK hs) w
      rw [← this]
      group
  have hcentral : ∀ s t : P, s ∈ f.ker → ⁅s, t⁆ = 1 ∧ ⁅t, s⁆ = 1 := by
    intro s t hs
    have := Subgroup.mem_center_iff.mp (hK hs) t
    exact ⟨commutatorElement_eq_one_iff_mul_comm.mpr this.symm,
      commutatorElement_eq_one_iff_mul_comm.mpr this⟩
  have hD : commutator P ≤ Subgroup.zpowers w := by
    refine commutator_le_of_closure_eq_top _ hS ?_
    intro s hs t ht
    rcases hs with rfl | rfl | hs
    · rcases ht with rfl | rfl | ht
      · rw [commutatorElement_self]; exact Subgroup.one_mem _
      · rw [hxy]; exact Subgroup.mem_zpowers _
      · rw [(hcentral t s ht).2]; exact Subgroup.one_mem _
    · rcases ht with rfl | rfl | ht
      · rw [← commutatorElement_inv, hxy]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      · rw [commutatorElement_self]; exact Subgroup.one_mem _
      · rw [(hcentral t s ht).2]; exact Subgroup.one_mem _
    · rw [(hcentral s t hs).1]; exact Subgroup.one_mem _
  set d := (x ^ n)⁻¹ * y ^ 2 with hd
  have hdK : d ∈ f.ker := by
    rw [MonoidHom.mem_ker, hd, map_mul, map_inv, map_pow, map_pow, hx, hy,
      QuaternionGroup.a_one_pow, QuaternionGroup.xa_sq, inv_mul_cancel]
  have hdz' : ∀ g : P, g * d⁻¹ = d⁻¹ * g :=
    Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ (hK hdK))
  have hxn : x ^ n = y ^ 2 * d⁻¹ := by rw [hd]; group
  have hkey : (c * x⁻¹) ^ n = x ^ n := by
    rw [← hyx, conj_pow, hxn]
    calc y * (y ^ 2 * d⁻¹) * y⁻¹ = y ^ 2 * (y * d⁻¹) * y⁻¹ := by group
      _ = y ^ 2 * (d⁻¹ * y) * y⁻¹ := by rw [hdz' y]
      _ = y ^ 2 * d⁻¹ := by group
  have hcomm1 : Commute c x⁻¹ := (hcz x⁻¹).symm
  have hcomm2 : Commute (x * x) c⁻¹ := hcz' (x * x)
  have hcn : c ^ n = x ^ n * x ^ n := by
    rw [hcomm1.mul_pow, inv_pow] at hkey
    calc c ^ n = c ^ n * (x ^ n)⁻¹ * x ^ n := by group
      _ = x ^ n * x ^ n := by rw [hkey]
  have hwn : w ^ n = 1 := by
    rw [hw, hcomm2.mul_pow, (Commute.refl x).mul_pow, inv_pow, ← hcn, mul_inv_cancel]
  have hfw : f w = (QuaternionGroup.a 1 : QuaternionGroup n) ^ 2 := by
    rw [hw, map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hcK, hx, inv_one, mul_one, sq]
  have hord : orderOf (f w) = n := by
    rw [hfw, orderOf_pow' _ two_ne_zero, QuaternionGroup.orderOf_a_one,
      Nat.gcd_eq_right (dvd_mul_right 2 n), Nat.mul_div_cancel_left n two_pos]
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzK, hzD⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hD hzD)
  rw [MonoidHom.mem_ker, map_zpow] at hzK
  have h1 : (n : ℤ) ∣ m := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hzK
  have h2 : (orderOf w : ℤ) ∣ m :=
    (Int.natCast_dvd_natCast.mpr (orderOf_dvd_of_pow_eq_one hwn)).trans h1
  exact Subgroup.mem_bot.mpr (orderOf_dvd_iff_zpow_eq_one.mp h2)

theorem quaternion_central_extension [NeZero n] (K : Subgroup P) [K.Normal]
    (hK : K ≤ Subgroup.center P) (e : P ⧸ K ≃* QuaternionGroup n) :
    K ⊓ commutator P = ⊥ := by
  let f : P →* QuaternionGroup n := e.toMonoidHom.comp (QuotientGroup.mk' K)
  have hker : f.ker = K := by
    ext g
    simp [f]
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective K)
  rw [← hker] at hK ⊢
  exact quaternion_central_extension_of_surjective f hf hK

theorem cyclic_central_extension {Q : Type*} [Group Q] [IsCyclic Q] (f : P →* Q)
    (hK : f.ker ≤ Subgroup.center P) : commutator P = ⊥ := by
  rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
  intro g _ h _
  exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
    ((MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hK).is_comm.comm g h))

end Quaternion

end CFSG.ComponentClassification.AschbacherToolkit

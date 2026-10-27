module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialCore
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterGeneric

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_dvd_mul_of_le_normalizer {H N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (H ⊔ N : Subgroup G) ∣ Nat.card H * Nat.card N := by
  have hN : (N.subgroupOf (H ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have htop : H.subgroupOf (H ⊔ N) ⊔ N.subgroupOf (H ⊔ N) = ⊤ :=
    codisjoint_iff.mp (Subgroup.codisjoint_subgroupOf_sup H N)
  have h1 : (N.subgroupOf (H ⊔ N)).index =
      (N.subgroupOf (H ⊔ N)).relIndex (H.subgroupOf (H ⊔ N)) := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
  have h2 := Subgroup.relIndex_dvd_card (N.subgroupOf (H ⊔ N)) (H.subgroupOf (H ⊔ N))
  rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv] at h2
  have h3 := Subgroup.card_mul_index (N.subgroupOf (H ⊔ N))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at h3
  rw [← h3, mul_comm (Nat.card H)]
  exact Nat.mul_dvd_mul_left _ h2

theorem mem_of_odd_of_mem_sup {R V : Subgroup G} (hVR : V ≤ Subgroup.normalizer (R : Set G))
    (hV : IsPGroup 2 V) {x : G} (hx : x ∈ R ⊔ V) (hodd : Odd (orderOf x)) : x ∈ R := by
  classical
  have hcomm : R ⊔ V = V ⊔ R := sup_comm R V
  have hN : (R.subgroupOf (V ⊔ R)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hVR
  have htop : V.subgroupOf (V ⊔ R) ⊔ R.subgroupOf (V ⊔ R) = ⊤ :=
    codisjoint_iff.mp (Subgroup.codisjoint_subgroupOf_sup V R)
  have h1 : (R.subgroupOf (V ⊔ R)).index =
      (R.subgroupOf (V ⊔ R)).relIndex (V.subgroupOf (V ⊔ R)) := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
  have h2 := Subgroup.relIndex_dvd_card (R.subgroupOf (V ⊔ R)) (V.subgroupOf (V ⊔ R))
  rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv] at h2
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  rw [hk] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hx' : x ∈ V ⊔ R := hcomm ▸ hx
  have hmem : (⟨x, hx'⟩ : ↥(V ⊔ R)) ∈ R.subgroupOf (V ⊔ R) := by
    rw [← QuotientGroup.eq_one_iff]
    have hdvd₁ : orderOf (QuotientGroup.mk' (R.subgroupOf (V ⊔ R)) ⟨x, hx'⟩) ∣ orderOf x := by
      have := orderOf_map_dvd (QuotientGroup.mk' (R.subgroupOf (V ⊔ R))) ⟨x, hx'⟩
      rwa [Subgroup.orderOf_mk] at this
    have hdvd₂ : orderOf (QuotientGroup.mk' (R.subgroupOf (V ⊔ R)) ⟨x, hx'⟩) ∣ 2 ^ j := by
      rw [← hj, Subgroup.index_eq_card]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (orderOf x) (2 ^ j) :=
      Nat.Coprime.pow_right j hodd.coprime_two_right
    have h3 := Nat.eq_one_of_dvd_coprimes hcop hdvd₁ hdvd₂
    exact orderOf_eq_one_iff.mp h3
  exact Subgroup.mem_subgroupOf.mp hmem

theorem exists_mul_mem_centralizer_of_card_sylow_two {C : Subgroup G} {t : G} (htC : t ∈ C)
    (ht : orderOf t = 2) (hS : ∀ S : Sylow 2 C, Nat.card S = 2) {f : G}
    (hf : f ∈ Subgroup.normalizer (C : Set G)) :
    ∃ c ∈ C, c * f ∈ Subgroup.centralizer {t} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hftC : f * t * f⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hf t).mp htC
  have hft : orderOf (f * t * f⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  have hfac : (Nat.card C).factorization 2 = 1 := by
    have h1 := Sylow.card_eq_multiplicity (default : Sylow 2 C)
    rw [hS default] at h1
    have h2 : (2 : ℕ) ^ 1 = 2 ^ (Nat.card C).factorization 2 := by rw [pow_one]; exact h1
    exact (Nat.pow_right_injective le_rfl h2).symm
  have hcard : ∀ x : C, orderOf x = 2 →
      Nat.card (Subgroup.zpowers x) = 2 ^ (Nat.card C).factorization 2 := by
    intro x hx
    rw [Nat.card_zpowers, hx, hfac, pow_one]
  let S₀ : Sylow 2 C := Sylow.ofCard (Subgroup.zpowers ⟨t, htC⟩)
    (hcard ⟨t, htC⟩ (by rw [Subgroup.orderOf_mk, ht]))
  let S₁ : Sylow 2 C := Sylow.ofCard (Subgroup.zpowers ⟨f * t * f⁻¹, hftC⟩)
    (hcard ⟨f * t * f⁻¹, hftC⟩ (by rw [Subgroup.orderOf_mk, hft]))
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C S₁ S₀
  have hmem : (⟨f * t * f⁻¹, hftC⟩ : C) ∈ (S₁ : Subgroup C) := Subgroup.mem_zpowers _
  have hmem' : c * ⟨f * t * f⁻¹, hftC⟩ * c⁻¹ ∈ (S₀ : Subgroup C) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact ⟨_, hmem, rfl⟩
  have hS₀ : (S₀ : Subgroup C) = Subgroup.zpowers ⟨t, htC⟩ := Sylow.coe_ofCard _ _
  rw [hS₀] at hmem'
  have ht2 : (⟨t, htC⟩ : C) * ⟨t, htC⟩ = 1 := by
    apply Subtype.ext
    change t * t = 1
    rw [← pow_two, ← ht, pow_orderOf_eq_one]
  rcases zpowers_cases_of_mul_self ht2 _ hmem' with h1 | h1
  · exfalso
    have h2 : t = 1 := by
      have := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at this
      exact conj_eq_one_iff.mp (conj_eq_one_iff.mp this)
    rw [h2, orderOf_one] at ht
    exact absurd ht (by decide)
  · refine ⟨c, c.2, ?_⟩
    have h2 : (c : G) * (f * t * f⁻¹) * (c : G)⁻¹ = t := by
      have := congrArg Subtype.val h1
      simpa using this
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c : G) * f * t = (c : G) * (f * t * f⁻¹) * (c : G)⁻¹ * ((c : G) * f) := by group
      _ = t * ((c : G) * f) := by rw [h2]

theorem sup_mem_normalizer {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := by
    apply sup_le
    · intro a ha
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha)
    · intro b hb
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB b).mp hb)
  apply mem_normalizer_of_conj_mem
  intro x hx
  have := hle hx
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

omit [Finite G] in
theorem conj_mem_centralizer {Q : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    {c : G} (hc : c ∈ Subgroup.centralizer (Q : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro y hy
  have hy' : g⁻¹ * y * g ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) y).mp hy
    rwa [inv_inv] at this
  have h1 := hc _ hy'
  calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * y := by group

theorem mem_normalizer_centralizer_of_mem {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem fun _ hc => conj_mem_centralizer hg hc

omit [Finite G] in
theorem centralizer_conj_eq_map (g x : G) :
    Subgroup.centralizer {g * x * g⁻¹} =
      (Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by simp [mul_assoc]⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
      _ = x * (g⁻¹ * y * g) := by group
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hz]
      _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group

omit [Finite G] in
theorem card_centralizer_conj (g x : G) :
    Nat.card (Subgroup.centralizer {g * x * g⁻¹}) = Nat.card (Subgroup.centralizer {x}) := by
  rw [centralizer_conj_eq_map, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem exists_mem_normalizer_not_mem {p n : ℕ} [hp : Fact p.Prime] {H : Subgroup G}
    (hH : Nat.card H = p ^ n) (hdvd : p ^ (n + 1) ∣ Nat.card G) :
    ∃ g ∈ Subgroup.normalizer (H : Set G), g ∉ H ∧ g ^ p ^ (n + 1) = 1 := by
  have hq : p ∣ Nat.card (Subgroup.normalizer (H : Set G) ⧸
      H.subgroupOf (Subgroup.normalizer (H : Set G))) :=
    Sylow.prime_dvd_card_quotient_normalizer hdvd hH
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨g, g.2, fun hg => ?_, ?_⟩
  · have h1 : (QuotientGroup.mk g : Subgroup.normalizer (H : Set G) ⧸
        H.subgroupOf (Subgroup.normalizer (H : Set G))) = 1 :=
      (QuotientGroup.eq_one_iff g).mpr (Subgroup.mem_subgroupOf.mpr hg)
    rw [h1, orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  · have h1 : (QuotientGroup.mk g : Subgroup.normalizer (H : Set G) ⧸
        H.subgroupOf (Subgroup.normalizer (H : Set G))) ^ p = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow] at h1
    have h2 := orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ h1)
    rw [hH, ← pow_mul] at h2
    rw [pow_succ']
    exact h2

theorem le_centralizer_of_inf_centralizer_eq_bot {U B : Subgroup G} {u : G}
    (hU : Odd (Nat.card U)) (hu2 : u * u = 1) (huU : u ∈ Subgroup.normalizer (U : Set G))
    (hfree : U ⊓ Subgroup.centralizer {u} = ⊥) (huB : ∀ b ∈ B, u * b * u⁻¹ = b⁻¹)
    (hBodd : ∀ b ∈ B, Odd (orderOf b)) (hBU : B ≤ Subgroup.normalizer (U : Set G))
    {b : G} (hb : b ∈ B) : U ≤ Subgroup.centralizer {b} := by
  obtain ⟨hinv, -⟩ := conj_eq_inv_of_inf_centralizer_eq_bot hU hu2 huU hfree
  intro x hx
  have hbx : b * x * b⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hBU hb) x).mp hx
  have h1 := hinv _ hbx
  have h4 : u * (b * x * b⁻¹) * u⁻¹ = b⁻¹ * x⁻¹ * b := by
    calc u * (b * x * b⁻¹) * u⁻¹ = (u * b * u⁻¹) * (u * x * u⁻¹) * (u * b * u⁻¹)⁻¹ := by group
      _ = b⁻¹ * x⁻¹ * b := by rw [huB b hb, hinv x hx, inv_inv]
  rw [h4, show (b * x * b⁻¹)⁻¹ = b * x⁻¹ * b⁻¹ by group] at h1
  have h6 : x⁻¹ * (b * b) = (b * b) * x⁻¹ := by
    calc x⁻¹ * (b * b) = b * (b⁻¹ * x⁻¹ * b) * b := by group
      _ = b * (b * x⁻¹ * b⁻¹) * b := by rw [h1]
      _ = (b * b) * x⁻¹ := by group
  have h5 : Commute (b * b) x := by
    calc (b * b) * x = x * (x⁻¹ * (b * b)) * x := by group
      _ = x * ((b * b) * x⁻¹) * x := by rw [h6]
      _ = x * (b * b) := by group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_sq_of_odd (hBodd b hb))
  have h7 := h5.zpow_left k
  rw [hk] at h7
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact h7.eq.symm

omit [Finite G] in
theorem map_conj_le_centralizer {X : Subgroup G} {g x : G}
    (hX : X ≤ Subgroup.centralizer {x}) :
    X.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer {g * x * g⁻¹} := by
  rw [centralizer_conj_eq_map]
  exact Subgroup.map_mono hX

theorem le_normalizer_map_conj {X W : Subgroup G} {g : G}
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) (hWX : W ≤ Subgroup.normalizer (X : Set G)) :
    W ≤ Subgroup.normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro w hw
  apply mem_normalizer_of_conj_mem
  rintro _ ⟨z, hz, rfl⟩
  have hw' : g⁻¹ * w * g ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgW) w).mp hw
    rwa [inv_inv] at this
  have hz' := (Subgroup.mem_normalizer_iff.mp (hWX hw') z).mp hz
  refine ⟨(g⁻¹ * w * g) * z * (g⁻¹ * w * g)⁻¹, hz', ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end CFSG.Semidihedral.FixedCoreNontrivial

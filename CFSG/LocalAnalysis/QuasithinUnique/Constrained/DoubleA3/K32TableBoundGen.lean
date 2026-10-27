module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableBound2

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def K32InnerBound (N : Type) [Group N] (m : ℕ) : Prop :=
  ∀ g : N, g ^ 3 = 1 → g ≠ 1 → ∀ W : Subgroup N, IsPGroup 2 ↥W → (∀ w ∈ W, w * g = g * w) →
    Nat.card ↥W ≤ m

@[expose] def K32OuterBound (N : Type) [Group N] (m : ℕ) : Prop :=
  ∀ α : MulAut N, α ^ 3 = 1 → α ∉ innAut N → ∀ W : Subgroup N, IsPGroup 2 ↥W →
    (∀ w ∈ W, α w = w) → Nat.card ↥W ≤ m

theorem k32_mulAut_conj_conj {N : Type} [Group N] (α : MulAut N) (y : N) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext m
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem k32ZBound2_of_inner_outer {N : Type} [Group N] (hZ : Subgroup.center N = ⊥) {m₁ m₂ : ℕ}
    (hin : K32InnerBound N m₁) (hout : K32OuterBound N m₂) : K32ZBound2 N m₁ m₂ := by
  have hinj : Function.Injective (MulAut.conj : N →* MulAut N) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : a ∈ (MulAut.conj : N →* MulAut N).ker := ha
    rw [k32_conj_ker, hZ, Subgroup.mem_bot] at h1
    exact h1
  have key : ∀ W : Subgroup (MulAut N), W ≤ innAut N → IsPGroup 2 ↥W →
      ∃ W' : Subgroup N, Nat.card ↥W' = Nat.card ↥W ∧ IsPGroup 2 ↥W' ∧
        W'.map (MulAut.conj : N →* MulAut N) = W := by
    intro W hWJ hW2
    set W' := W.comap (MulAut.conj : N →* MulAut N) with hW'
    have hmap : W'.map (MulAut.conj : N →* MulAut N) = W := by
      rw [hW', Subgroup.map_comap_eq]
      exact inf_eq_right.mpr hWJ
    have hcard : Nat.card ↥W' = Nat.card ↥W := by
      have h1 := Subgroup.card_map_of_injective (K := W') hinj
      rw [hmap] at h1
      exact h1.symm
    refine ⟨W', hcard, ?_, hmap⟩
    refine hW2.of_injective (((MulAut.conj : N →* MulAut N).comp W'.subtype).codRestrict W
      (fun a => a.2)) ?_
    intro a b hab
    exact Subtype.ext (hinj (congrArg Subtype.val hab))
  refine ⟨?_, ?_⟩
  · intro ω hωin hω3 W hWJ hW2 hWC
    obtain ⟨g, rfl⟩ := hωin
    obtain ⟨W', hcard, hW'2, hmap⟩ := key W hWJ hW2
    have hg3 : g ^ 3 = 1 := by
      apply hinj
      rw [map_pow, map_one]
      rw [← hω3]
      exact pow_orderOf_eq_one _
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [map_one, orderOf_one] at hω3
      omega
    rw [← hcard]
    refine hin g hg3 hg1 W' hW'2 fun w hw => ?_
    have hmem : (MulAut.conj : N →* MulAut N) w ∈ W := by
      rw [← hmap]
      exact ⟨w, hw, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hWC hmem)
    apply hinj
    rw [map_mul, map_mul]
    exact h1
  · intro ω hωout hω3 W hWJ hW2 hWC
    have hω3' : ω ^ 3 = 1 := by
      rw [← hω3]
      exact pow_orderOf_eq_one ω
    obtain ⟨W', hcard, hW'2, hmap⟩ := key W hWJ hW2
    rw [← hcard]
    refine hout ω hω3' hωout W' hW'2 fun w hw => ?_
    have hmem : (MulAut.conj : N →* MulAut N) w ∈ W := by
      rw [← hmap]
      exact ⟨w, hw, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hWC hmem)
    have h2 : MulAut.conj (ω w) = MulAut.conj w := by
      rw [← k32_mulAut_conj_conj ω w, mul_inv_eq_iff_eq_mul]
      exact h1.symm
    exact hinj h2

theorem k32InnerBound_of_equiv {N N' : Type} [Group N] [Group N'] (e : N ≃* N') {m : ℕ}
    (h : K32InnerBound N m) : K32InnerBound N' m := by
  intro g' hg3 hg1 W' hW2 hC
  set g : N := e.symm g' with hg
  set W : Subgroup N := W'.map (e.symm : N' →* N) with hW
  have hinj : Function.Injective (e.symm : N' →* N) := e.symm.injective
  have hcard : Nat.card ↥W = Nat.card ↥W' := Subgroup.card_map_of_injective hinj
  have hWpg : IsPGroup 2 ↥W := by
    exact hW2.of_equiv (Subgroup.equivMapOfInjective W' (e.symm : N' →* N) hinj)
  rw [← hcard]
  refine h g ?_ ?_ W hWpg ?_
  · rw [hg, ← map_pow, hg3, map_one]
  · intro h1
    apply hg1
    have := congrArg e h1
    rwa [hg, MulEquiv.apply_symm_apply, map_one] at this
  · rintro _ ⟨w', hw', rfl⟩
    change e.symm w' * e.symm g' = e.symm g' * e.symm w'
    rw [← map_mul, ← map_mul, hC w' hw']

theorem k32_two_pow_factorization {N k i : ℕ} (h : N = 2 ^ k * i) (hi : Odd i) :
    2 ^ N.factorization 2 = 2 ^ k := by
  have hi0 : i ≠ 0 := hi.pos.ne'
  have hnd : ¬ 2 ∣ i := by
    have := Nat.odd_iff.mp hi
    omega
  rw [h, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hi0]
  simp [Nat.factorization_eq_zero_of_not_dvd hnd, Nat.Prime.factorization_pow Nat.prime_two]

theorem k32_exists_conj_le_sylow {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    {W : Subgroup G} (hW : IsPGroup 2 ↥W) : ∃ g : G, ∀ w ∈ W, g * w * g⁻¹ ∈ (P : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hW.exists_le_sylow
  obtain ⟨y, rfl⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨y⁻¹, fun w hw => ?_⟩
  have hwQ : w ∈ ((y • P : Sylow 2 G) : Subgroup G) := hQ hw
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hwQ
  obtain ⟨p, hpP, hpw⟩ := hwQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hpw
  have : y⁻¹ * w * y⁻¹⁻¹ = p := by rw [← hpw]; group
  rw [this]
  exact hpP

theorem k32_exists_conj_le {G : Type*} [Group G] [Finite G] {U W : Subgroup G}
    (hU : IsSylowTwoOf U ⊤) (hW : IsPGroup 2 ↥W) : ∃ g : G, ∀ w ∈ W, g * w * g⁻¹ ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hU2, hUidx⟩ := hU
  have hidx : ¬ 2 ∣ U.index := by
    rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right _] at hUidx
  exact k32_exists_conj_le_sylow (hU2.toSylow hidx) hW

theorem k32_lift_two_group {G P : Type*} [Group G] [Group P] [Finite G] (π : G →* P)
    (hπ : Function.Surjective π) (hodd : ¬ 2 ∣ Nat.card π.ker) {W : Subgroup P}
    (hW : IsPGroup 2 ↥W) :
    ∃ V : Subgroup G, IsPGroup 2 ↥V ∧ V.map π = W ∧ Nat.card ↥V = Nat.card ↥W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite P := Finite.of_surjective π hπ
  obtain ⟨P₂, hWP₂⟩ := hW.exists_le_sylow
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective hπ 2 P₂
  have hQmap : (Q : Subgroup G).map π = P₂ := by
    rw [← hQ]
    rfl
  set V : Subgroup G := (Q : Subgroup G) ⊓ W.comap π with hV
  have hV2 : IsPGroup 2 ↥V := Q.isPGroup'.to_le inf_le_left
  have hVmap : V.map π = W := by
    ext w
    constructor
    · rintro ⟨x, ⟨-, hxW⟩, rfl⟩
      exact hxW
    · intro hw
      have h1 : w ∈ (Q : Subgroup G).map π := by
        rw [hQmap]
        exact hWP₂ hw
      obtain ⟨x, hxQ, hxw⟩ := h1
      exact ⟨x, ⟨hxQ, Subgroup.mem_comap.mpr (by rw [hxw]; exact hw)⟩, hxw⟩
  refine ⟨V, hV2, hVmap, ?_⟩
  have hker : ∀ x ∈ V, π x = 1 → x = 1 := by
    intro x hxV hx1
    have hxker : x ∈ π.ker := hx1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hV2) ⟨x, hxV⟩
    have hdvd : orderOf x ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hxker
    have hord : orderOf x = 2 ^ k := by
      have := hk
      rwa [Subgroup.orderOf_mk] at this
    rw [hord] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact hodd ((dvd_pow_self 2 hk0).trans hdvd)
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hord
    exact hord
  let f : V → W := fun x => ⟨π x, hVmap ▸ Subgroup.mem_map_of_mem π x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h1 : π x = π y := congrArg Subtype.val hxy
      have h2 : π ((x : G)⁻¹ * y) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
      have h3 := hker _ (V.mul_mem (V.inv_mem x.2) y.2) h2
      exact Subtype.ext (inv_mul_eq_one.mp h3)
    · rintro ⟨w, hw⟩
      rw [← hVmap] at hw
      obtain ⟨x, hxV, hxw⟩ := hw
      exact ⟨⟨x, hxV⟩, Subtype.ext hxw⟩
  exact Nat.card_congr (Equiv.ofBijective f hf)

end CFSG.QuasithinUnique.DoubleA3

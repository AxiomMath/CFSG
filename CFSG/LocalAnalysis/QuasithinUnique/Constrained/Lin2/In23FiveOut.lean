module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel

public section

namespace CFSG.QuasithinUnique.Lin2.Five

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBSymplecticTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

section Cyclic

theorem card_two_subgroup_of_cyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {A X : Subgroup C} (hA : A.index = 2) (hX : IsPGroup 2 X) (hXA : ¬ X ≤ A) :
    Nat.card X = 2 ^ (Nat.card C).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCA : Nat.card A * 2 = Nat.card C := by
    rw [← hA]; exact Subgroup.card_mul_index A
  obtain ⟨a, ha⟩ := hX.exists_card_eq
  have hXC : Nat.card X ∣ Nat.card C := Subgroup.card_subgroup_dvd_card X
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hle : a ≤ (Nat.card C).factorization 2 := by
    rw [ha] at hXC
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hC0).mp hXC
  have hnd : ¬ Nat.card X ∣ Nat.card A := fun hd =>
    hXA (IsCyclic.subgroup_le_iff_card_dvd.mpr hd)
  have hge : (Nat.card C).factorization 2 ≤ a := by
    by_contra hlt
    push Not at hlt
    have h2 : 2 ^ (a + 1) ∣ Nat.card C :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hC0).mpr hlt
    rw [← hCA] at h2
    have h3 : 2 ^ a * 2 ∣ Nat.card A * 2 := by simpa [pow_succ] using h2
    have h4 : 2 ^ a ∣ Nat.card A := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3
    exact hnd (ha ▸ h4)
  rw [ha, le_antisymm hle hge]

end Cyclic

section Act

variable {G : Type*} [Group G]

@[expose] noncomputable def act (K : Subgroup G) {T' : Subgroup G}
    (h : T' ≤ Subgroup.normalizer (K : Set G)) : T' →* MulAut ↥K :=
  (conjAct K).comp (Subgroup.inclusion h)

theorem act_apply (K : Subgroup G) {T' : Subgroup G} (h : T' ≤ Subgroup.normalizer (K : Set G))
    (t : T') (k : ↥K) : ((act K h t k : ↥K) : G) = (t : G) * (k : G) * (t : G)⁻¹ := rfl

@[expose] noncomputable def outAct (K : Subgroup G) {T' : Subgroup G}
    (h : T' ≤ Subgroup.normalizer (K : Set G)) : T' →* Outer ↥K :=
  (QuotientGroup.mk' (inner ↥K)).comp (act K h)

theorem conj_injective_of_center_eq_bot {Q : Type*} [Group Q] (hZ : Subgroup.center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  intro g h hgh
  have : h⁻¹ * g ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun φ : MulAut Q => φ z) hgh
    simp only [MulAut.conj_apply] at h1
    have h2 : g * z = h * z * h⁻¹ * g := by
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = (h * z * h⁻¹) * g := by rw [h1]
    calc z * (h⁻¹ * g) = h⁻¹ * (h * z * h⁻¹ * g) := by group
      _ = h⁻¹ * (g * z) := by rw [h2]
      _ = h⁻¹ * g * z := by group
  rw [hZ, Subgroup.mem_bot] at this
  exact (inv_mul_eq_one.mp this).symm

theorem mem_ker_outAct_iff [Finite G] {K T' R₀ : Subgroup G} (hZ : Subgroup.center ↥K = ⊥)
    (h : T' ≤ Subgroup.normalizer (K : Set G)) (hT2 : IsPGroup 2 T') (hR₀K : R₀ ≤ K)
    (hR₀T : R₀ ≤ T') (hsyl : IsSylowTwoOf R₀ K) (t : T') :
    outAct K h t = 1 ↔ (t : G) ∈ R₀ ⊔ (T' ⊓ Subgroup.centralizer (K : Set G)) := by
  have hinj := conj_injective_of_center_eq_bot hZ
  constructor
  · intro ht
    have h1 : act K h t ∈ inner ↥K := (QuotientGroup.eq_one_iff _).mp ht
    obtain ⟨k, hk⟩ := h1
    set B : Subgroup ↥K := (act K h).range.comap (MulAut.conj : ↥K →* MulAut ↥K) with hB
    have hkB : k ∈ B := ⟨t, hk.symm⟩
    have hBp : IsPGroup 2 B := by
      intro b
      obtain ⟨u, hu⟩ : ∃ u : T', act K h u = MulAut.conj (b : ↥K) := b.2
      obtain ⟨j, hj⟩ := hT2 u
      refine ⟨j, ?_⟩
      apply Subtype.ext
      apply hinj
      rw [Subgroup.coe_pow, map_pow, ← hu, ← map_pow, hj, map_one]
      simp
    have hB2p : IsPGroup 2 (B.map K.subtype) := hBp.map K.subtype
    have hR₀B : R₀ ≤ B.map K.subtype := by
      intro r hr
      refine ⟨⟨r, hR₀K hr⟩, ⟨⟨r, hR₀T hr⟩, ?_⟩, rfl⟩
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      simp [act_apply, MulAut.conj_apply]
    have hB2K : B.map K.subtype ≤ K := Subgroup.map_subtype_le B
    have hR₀eq : R₀ = B.map K.subtype := (hsyl.eq_of_le hR₀B hB2K hB2p).symm
    have hkR : (k : G) ∈ R₀ := by
      rw [hR₀eq]
      exact ⟨k, hkB, rfl⟩
    have hmem : (k : G)⁻¹ * (t : G) ∈ T' ⊓ Subgroup.centralizer (K : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨T'.mul_mem (T'.inv_mem (hR₀T hkR)) t.2, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
      have hy1 := congrArg (fun α : MulAut ↥K => ((α ⟨y, hy⟩ : ↥K) : G)) hk
      simp only [MulAut.conj_apply, act_apply] at hy1
      have hy2 : (k : G) * y * (k : G)⁻¹ = (t : G) * y * (t : G)⁻¹ := hy1
      calc y * ((k : G)⁻¹ * (t : G)) = (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) * (t : G) := by group
        _ = (k : G)⁻¹ * ((t : G) * y * (t : G)⁻¹) * (t : G) := by rw [hy2]
        _ = ((k : G)⁻¹ * (t : G)) * y := by group
    have : (t : G) = (k : G) * ((k : G)⁻¹ * (t : G)) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hkR hmem
  · intro ht
    have hN : R₀ ⊔ (T' ⊓ Subgroup.centralizer (K : Set G)) ≤ (outAct K h).ker.map T'.subtype := by
      refine sup_le ?_ ?_
      · intro r hr
        refine ⟨⟨r, hR₀T hr⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
        rw [outAct, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        refine ⟨⟨r, hR₀K hr⟩, ?_⟩
        apply MulEquiv.ext
        intro y
        apply Subtype.ext
        simp [act_apply, MulAut.conj_apply]
      · intro y hy
        have hyT : y ∈ T' := (Subgroup.mem_inf.mp hy).1
        have hyC := (Subgroup.mem_inf.mp hy).2
        refine ⟨⟨y, hyT⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
        rw [outAct, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        refine ⟨1, ?_⟩
        apply MulEquiv.ext
        intro z
        apply Subtype.ext
        have hz := Subgroup.mem_centralizer_iff.mp hyC (z : G) z.2
        have hz' : (y : G) * (z : G) * (y : G)⁻¹ = (z : G) := by
          calc (y : G) * (z : G) * (y : G)⁻¹ = ((y : G) * (z : G)) * (y : G)⁻¹ := rfl
            _ = ((z : G) * (y : G)) * (y : G)⁻¹ := by rw [← hz]
            _ = (z : G) := by group
        simp [act_apply, hz']
    obtain ⟨t₀, ht₀, hteq⟩ := hN ht
    have : t₀ = t := Subtype.ext hteq
    rw [← this]
    exact ht₀

end Act

theorem outer_two_part {G : Type} [Group G] [Finite G] {K T' R₀ : Subgroup G} {F : Type}
    [Field F] [Fintype F] {e : ℕ} (hF : Fintype.card F = 2 ^ e) (he : 0 < e)
    (hout : Sp4OutCyclic) (φ : ↥K ≃* StatedProj (StatedSp 2 F))
    (h : T' ≤ Subgroup.normalizer (K : Set G)) (hT2 : IsPGroup 2 T') (hR₀K : R₀ ≤ K)
    (hR₀T : R₀ ≤ T') (hR₀2 : IsPGroup 2 R₀) (hR₀card : Nat.card R₀ = 2 ^ (4 * e)) {x : G}
    (hx : x ∈ T')
    (hxout : ∀ β : MulAut ↥K, (∀ k : ↥K, ((β k : ↥K) : G) = x * (k : G) * x⁻¹) →
      MulAut.congr φ β ∉ typeKernel F) :
    (∃ t ∈ T', T' = (R₀ ⊔ (T' ⊓ Subgroup.centralizer (K : Set G))) ⊔ Subgroup.zpowers t) ∧
      (R₀ ⊔ (T' ⊓ Subgroup.centralizer (K : Set G))).relIndex T' =
        2 ^ ((2 * e).factorization 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have : Finite F := Finite.of_fintype F
  obtain ⟨hcyc, hcard⟩ := hout F e hF he
  have := hcyc
  have : Finite (Outer (StatedProj (StatedSp 2 F))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hZ : Subgroup.center ↥K = ⊥ := center_eq_bot_of_equiv φ
  have hsyl : IsSylowTwoOf R₀ K := isSylowTwoOf_of_card hF he φ hR₀K hR₀2 hR₀card
  set N := R₀ ⊔ (T' ⊓ Subgroup.centralizer (K : Set G)) with hN
  have hNT : N ≤ T' := sup_le hR₀T inf_le_left
  let Ψ : T' →* Outer (StatedProj (StatedSp 2 F)) :=
    (equivalence φ).toMonoidHom.comp (outAct K h)
  have hker : ∀ t : T', Ψ t = 1 ↔ (t : G) ∈ N := fun t => by
    show equivalence φ (outAct K h t) = 1 ↔ _
    rw [map_eq_one_iff _ (equivalence φ).injective]
    exact mem_ker_outAct_iff hZ h hT2 hR₀K hR₀T hsyl t
  have hkerEq : Ψ.ker = N.subgroupOf T' := by
    ext t
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hrel : N.relIndex T' = Nat.card Ψ.range := by
    rw [Subgroup.relIndex, ← hkerEq]
    exact Subgroup.index_ker Ψ
  set X := Ψ.range with hX
  have hX2 : IsPGroup 2 X := hT2.of_surjective Ψ.rangeRestrict Ψ.rangeRestrict_surjective
  set A := (typeKernel F).map (QuotientGroup.mk' (inner (StatedProj (StatedSp 2 F)))) with hA
  obtain ⟨-, -, hidx, hinner⟩ := type_kernel (K := F) 2
  have hAidx : A.index ≤ 2 := by
    rw [hA, Subgroup.index_map_eq (typeKernel F) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact hinner)]
    exact hidx
  have hxA : Ψ ⟨x, hx⟩ ∉ A := by
    intro hmem
    obtain ⟨γ, hγ, hγeq⟩ := Subgroup.mem_map.mp hmem
    have hΨ : Ψ ⟨x, hx⟩ = QuotientGroup.mk (MulAut.congr φ (act K h ⟨x, hx⟩)) := rfl
    have h1 : γ⁻¹ * MulAut.congr φ (act K h ⟨x, hx⟩) ∈ inner (StatedProj (StatedSp 2 F)) := by
      have := hγeq.trans hΨ
      exact QuotientGroup.eq.mp this
    have h2 : γ⁻¹ * MulAut.congr φ (act K h ⟨x, hx⟩) ∈ typeKernel F := hinner h1
    have h3 : MulAut.congr φ (act K h ⟨x, hx⟩) ∈ typeKernel F := by
      have := (typeKernel F).mul_mem hγ h2
      simpa using this
    exact hxout (act K h ⟨x, hx⟩) (fun k => act_apply K h ⟨x, hx⟩ k) h3
  have hAne : A ≠ ⊤ := fun htop => hxA (htop ▸ Subgroup.mem_top _)
  have hAidx2 : A.index = 2 := by
    have h1 : A.index ≠ 1 := fun h1 => hAne (Subgroup.index_eq_one.mp h1)
    have h0 : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hXnle : ¬ X ≤ A := fun hle => hxA (hle ⟨⟨x, hx⟩, rfl⟩)
  have hXcard : Nat.card X = 2 ^ (2 * e).factorization 2 := by
    rw [card_two_subgroup_of_cyclic hAidx2 hX2 hXnle, hcard]
  refine ⟨?_, by rw [hrel]; exact hXcard⟩
  have : IsCyclic X := inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
  obtain ⟨t, ht⟩ := g.2
  refine ⟨(t : G), t.2, le_antisymm ?_ (sup_le hNT (Subgroup.zpowers_le.mpr t.2))⟩
  intro u hu
  have hΨu : Ψ ⟨u, hu⟩ ∈ X := ⟨⟨u, hu⟩, rfl⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨Ψ ⟨u, hu⟩, hΨu⟩)
  have hj' : (Ψ t) ^ j = Ψ ⟨u, hu⟩ := by rw [ht]; exact congrArg Subtype.val hj
  have hw : Ψ (⟨u, hu⟩ * t ^ (-j)) = 1 := by
    rw [map_mul, map_zpow, ← hj', ← zpow_add, add_neg_cancel, zpow_zero]
  have hwN : (⟨u, hu⟩ * t ^ (-j) : T').1 ∈ N := (hker _).mp hw
  have hu' : u = (⟨u, hu⟩ * t ^ (-j) : T').1 * (t : G) ^ j := by
    have hcoe : ((t ^ (-j) : T') : G) = ((t : G) ^ j)⁻¹ := by rw [Subgroup.coe_zpow, zpow_neg]
    show u = (u * ((t ^ (-j) : T') : G)) * (t : G) ^ j
    rw [hcoe]
    group
  rw [hu']
  exact Subgroup.mul_mem_sup hwN (Subgroup.zpow_mem_zpowers _ _)

end CFSG.QuasithinUnique.Lin2.Five

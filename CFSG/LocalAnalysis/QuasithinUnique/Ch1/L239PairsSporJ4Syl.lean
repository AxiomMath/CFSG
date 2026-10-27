module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporWit

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

section Assembly

variable {X : Type*} [Group X]

theorem le_pCoreOf_of_normal_pGroup (Y Q : Subgroup X) (hQY : Q ≤ Y)
    (hQn : ∀ y ∈ Y, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) (hQ2 : IsPGroup 2 ↥Q) : Q ≤ pCoreOf 2 Y := by
  have hnorm : (Q.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff hQY).2 fun h g hh hg => hQn g hg h hh
  have hQ2' : IsPGroup 2 (Q.subgroupOf Y) := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQY).symm
  have hle : Q.subgroupOf Y ≤ CFSG.pCore 2 ↥Y := le_pCore_of_normal hQ2'
  intro q hq
  rw [pCoreOf_eq_map]
  exact ⟨⟨q, hQY hq⟩, hle (show (⟨q, hQY hq⟩ : ↥Y) ∈ Q.subgroupOf Y from hq), rfl⟩

theorem goodLocal_of_sylow3_witnesses (Y : Subgroup X) [Finite ↥Y] (N M : Subgroup X)
    (hNY : N ≤ Y) (hNn : ∀ y ∈ Y, ∀ q ∈ N, y * q * y⁻¹ ∈ N) (hN2 : IsPGroup 2 ↥N)
    (hC : ∀ y ∈ Y, (∀ q ∈ N, y * q = q * y) → y ∈ N) (hMY : M ≤ Y)
    (hMn : ∀ y ∈ Y, ∀ q ∈ M, y * q * y⁻¹ ∈ M) (hM2 : IsPGroup 2 ↥M) (P : Subgroup X)
    (hPY : P ≤ Y) (hP3 : IsPGroup 3 ↥P) (hPi : ¬ 3 ∣ (P.subgroupOf Y).index)
    (hw : ∀ b ∈ P, orderOf b = 3 → ∃ x ∈ ⁅M, Subgroup.zpowers b⁆,
      ∃ y ∈ ⁅M, Subgroup.zpowers b⁆, x * y ≠ y * x) : GoodLocal Y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ↥N :=
    Finite.of_injective (Subgroup.inclusion hNY) (Subgroup.inclusion_injective hNY)
  have hnorm : (N.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff hNY).2 fun h g hh hg => hNn g hg h hh
  have hN2' : IsPGroup 2 (N.subgroupOf Y) := hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNY).symm
  have hle : N.subgroupOf Y ≤ CFSG.pCore 2 ↥Y := le_pCore_of_normal hN2'
  have hMpc : M ≤ pCoreOf 2 Y := le_pCoreOf_of_normal_pGroup Y M hMY hMn hM2
  obtain ⟨k, hk⟩ := hN2.exists_card_eq
  have hord2 : ∀ c : ↥Y, (∀ q ∈ N, (c : X) * q = q * (c : X)) → ∃ n, orderOf c = 2 ^ n := by
    intro c hc
    have hcN : (c : X) ∈ N := hC c c.2 hc
    have h1 : orderOf (⟨(c : X), hcN⟩ : ↥N) ∣ Nat.card ↥N := orderOf_dvd_natCard _
    rw [hk, ← Subgroup.orderOf_coe] at h1
    have h2 : orderOf c ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe c]
      exact h1
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    exact ⟨n, hn⟩
  refine goodLocal_of_noncentral Y ?_ ?_
  · intro b hb3
    have hZ : IsPGroup 3 (Subgroup.zpowers b) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb3, pow_one])
    obtain ⟨T, hT⟩ := hZ.exists_le_sylow
    have hPb3 : IsPGroup 3 ↥(P.subgroupOf Y) :=
      hP3.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y T (hPb3.toSylow hPi)
    have hb' : g * b * g⁻¹ ∈ P.subgroupOf Y := by
      have hbT : b ∈ (T : Subgroup ↥Y) := hT (Subgroup.mem_zpowers b)
      have h1 : g * b * g⁻¹ ∈ ((g • T : Sylow 3 ↥Y) : Subgroup ↥Y) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ hbT
      rw [hg] at h1
      exact h1
    have hb'P : (g : X) * (b : X) * (g : X)⁻¹ ∈ P := Subgroup.mem_subgroupOf.1 hb'
    have hord' : orderOf ((g : X) * (b : X) * (g : X)⁻¹) = 3 := by
      have h1 : orderOf (((g * b * g⁻¹ : ↥Y)) : X) = 3 := by
        rw [Subgroup.orderOf_coe]
        have := (MulAut.conj g).orderOf_eq b
        rw [MulAut.conj_apply] at this
        rw [this, hb3]
      simpa using h1
    obtain ⟨x', hx', y', hy', hxy'⟩ := hw _ hb'P hord'
    set f : X →* X := (MulAut.conj ((g : X)⁻¹)).toMonoidHom with hf
    have hfinj : Function.Injective f := (MulAut.conj ((g : X)⁻¹)).injective
    have hfapp : ∀ t : X, f t = (g : X)⁻¹ * t * (g : X) := fun t => by
      simp [hf]
    have hmap : ⁅M, Subgroup.zpowers ((g : X) * (b : X) * (g : X)⁻¹)⁆.map f ≤
        ⁅pCoreOf 2 Y, Subgroup.zpowers (b : X)⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨q, hq, rfl⟩
        rw [hfapp]
        have := hMn ((g : X)⁻¹) (Y.inv_mem g.2) q hq
        rw [inv_inv] at this
        exact hMpc this
      · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
        rw [hfapp]
        have : (g : X)⁻¹ * ((g : X) * (b : X) * (g : X)⁻¹) * (g : X) = (b : X) := by group
        rw [this]
        exact Subgroup.mem_zpowers _
    have hx'' : f x' ∈ ⁅pCoreOf 2 Y, Subgroup.zpowers (b : X)⁆ := hmap ⟨x', hx', rfl⟩
    have hy'' : f y' ∈ ⁅pCoreOf 2 Y, Subgroup.zpowers (b : X)⁆ := hmap ⟨y', hy', rfl⟩
    obtain ⟨x, hx, hxe⟩ := exists_lift_commutator Y b hx''
    obtain ⟨y, hy, hye⟩ := exists_lift_commutator Y b hy''
    refine ⟨x, hx, y, hy, Or.inl fun h => hxy' ?_⟩
    apply hfinj
    rw [map_mul, map_mul, ← hxe, ← hye]
    exact congrArg Subtype.val h
  · intro r hr hr2 hr3 c hc
    by_contra hcon
    have hcon' : ∀ q ∈ N, (c : X) * q = q * (c : X) := fun q hq => by
      by_contra h
      refine hcon ⟨⟨q, hNY hq⟩, hle (show (⟨q, hNY hq⟩ : ↥Y) ∈ N.subgroupOf Y from hq), ?_⟩
      intro h'
      exact h (congrArg Subtype.val h').symm
    obtain ⟨n, hn⟩ := hord2 c hcon'
    rw [hc] at hn
    have := hr.dvd_of_dvd_pow (show r ∣ 2 ^ n from ⟨1, by omega⟩)
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)

end Assembly

end CFSG.QuasithinUnique.Vol2Native.L239

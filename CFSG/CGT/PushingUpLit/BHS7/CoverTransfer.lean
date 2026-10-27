module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open scoped commutatorElement

theorem eq_bot_of_central_of_commutative_sylow
    {E G : Type*} [Group E] [Group G] [Finite G]
    (hE : ∀ (N : Subgroup E) [N.Normal], IsPGroup 2 (E ⧸ N) → N = ⊤)
    {φ : E →* G} (hφ : Function.Surjective φ)
    {S Z : Subgroup G} (hS : IsPGroup 2 S) (hind : ¬ 2 ∣ S.index)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hZS : Z ≤ S) (hZc : Z ≤ Subgroup.center G) : Z = ⊥ := by
  classical
  by_contra hZ
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzS : z ∈ S := hZS hzZ
  let _ : CommGroup S := { (inferInstance : Group S) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let V : G →* S := MonoidHom.transfer (MonoidHom.id S)
  have hz : z ∈ Subgroup.center G := hZc hzZ
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ S →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center G := Subgroup.pow_mem _ hz k
    rw [Subgroup.mem_center_iff] at hzk
    rw [mul_assoc, ← hzk g₀, inv_mul_cancel_left]
  have hVz := MonoidHom.transfer_eq_pow (MonoidHom.id S) z key
  have hne : V z ≠ 1 := by
    intro h1
    have h2 := hVz.symm.trans h1
    have h3 : z ^ S.index = 1 := congrArg Subtype.val h2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨z, hzS⟩
    have hk' : orderOf z = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hz1' (orderOf_eq_one_iff.mp (by simpa using hk'))
    have h4 : orderOf z ∣ S.index := orderOf_dvd_of_pow_eq_one h3
    rw [hk'] at h4
    exact hind ((dvd_pow_self 2 hk0).trans h4)
  let f : E →* S := V.comp φ
  have hf : f.ker = ⊤ := by
    refine hE f.ker ?_
    have e := QuotientGroup.quotientKerEquivRange f
    exact (hS.to_subgroup f.range).of_equiv e.symm
  obtain ⟨x, hx⟩ := hφ z
  have h5 : f x = 1 := by
    have : x ∈ f.ker := by rw [hf]; trivial
    exact this
  apply hne
  have : f x = V z := by simp [f, hx]
  rw [← this]
  exact h5

theorem le_of_central_mod_of_commutative_mod_sylow
    {Γ : Type*} [Group Γ] [Finite Γ] {E U QE SE : Subgroup Γ}
    (hE : ∀ (N : Subgroup E) [N.Normal], IsPGroup 2 (E ⧸ N) → N = ⊤)
    (hUn : ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U)
    (hUS : U ≤ SE) (hSE : SE ≤ E) (hQS : QE ≤ SE)
    (hp : IsPGroup 2 SE) (hodd : ¬ 2 ∣ (SE.subgroupOf E).index)
    (hQc : ∀ q ∈ QE, ∀ e ∈ E, ⁅q, e⁆ ∈ U)
    (hSc : ∀ a ∈ SE, ∀ b ∈ SE, ⁅a, b⁆ ∈ U) : QE ≤ U := by
  classical
  have hNn : (U.subgroupOf E).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hUn g g.2 n hn⟩
  let φ : E →* E ⧸ U.subgroupOf E := QuotientGroup.mk' (U.subgroupOf E)
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hker : φ.ker = U.subgroupOf E := QuotientGroup.ker_mk' _
  have hcommU : ∀ a b : E, ((⁅a, b⁆ : E) : Γ) ∈ U → φ a * φ b = φ b * φ a := by
    intro a b hab
    have h1 : φ ⁅a, b⁆ = 1 := by
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      exact hab
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm).mp h1
  let Z : Subgroup (E ⧸ U.subgroupOf E) := (QE.subgroupOf E).map φ
  let S' : Subgroup (E ⧸ U.subgroupOf E) := (SE.subgroupOf E).map φ
  have hS'p : IsPGroup 2 S' := by
    have h1 : IsPGroup 2 (SE.subgroupOf E) :=
      hp.of_equiv (Subgroup.subgroupOfEquivOfLe hSE).symm
    exact h1.of_surjective (φ.subgroupMap (SE.subgroupOf E)) (φ.subgroupMap_surjective _)
  have hS'ind : ¬ 2 ∣ S'.index := by
    have h1 : S'.index = (SE.subgroupOf E).index :=
      Subgroup.index_map_eq (SE.subgroupOf E) hφ (by
        rw [hker]
        exact fun n hn => Subgroup.mem_subgroupOf.mpr (hUS (Subgroup.mem_subgroupOf.mp hn)))
    rw [h1]
    exact hodd
  have hS'comm : ∀ a ∈ S', ∀ b ∈ S', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact hcommU a b (hSc a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb))
  have hZS' : Z ≤ S' := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hQS (Subgroup.mem_subgroupOf.mp hx))
  have hZc : Z ≤ Subgroup.center _ := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨e, rfl⟩ := hφ g
    exact (hcommU q e (hQc q (Subgroup.mem_subgroupOf.mp hq) e e.2)).symm
  have hZbot := eq_bot_of_central_of_commutative_sylow hE hφ hS'p hS'ind hS'comm hZS' hZc
  intro q hq
  have hqE : q ∈ E := hSE (hQS hq)
  have h2 : φ ⟨q, hqE⟩ ∈ Z := ⟨⟨q, hqE⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  rw [hZbot, Subgroup.mem_bot] at h2
  have h3 : (⟨q, hqE⟩ : E) ∈ φ.ker := h2
  rw [hker, Subgroup.mem_subgroupOf] at h3
  exact h3

end CFSG.CGT.PushingUpLit.BHS7

module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnAPI
public import CFSG.GroupTheory.PCore.PrimeCoreImages

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

section CentralCover

variable {M S : Type} [Group M] [Group S] (π : M →* S) (α : MulAut M) (β : MulAut S)

@[expose] def coverX : Subgroup M := (u4Fix β).comap π

theorem mem_coverX {π : M →* S} {β : MulAut S} {u : M} : u ∈ coverX π β ↔ β (π u) = π u := Iff.rfl

variable {π α β}

theorem fix_le_coverX (hαβ : ∀ u, π (α u) = β (π u)) : u4Fix α ≤ coverX π β := by
  intro u hu
  rw [mem_coverX, ← hαβ]
  have : α u = u := hu
  rw [this]

theorem alpha_mul_inv_mem_ker (hαβ : ∀ u, π (α u) = β (π u)) {u : M} (hu : u ∈ coverX π β) :
    α u * u⁻¹ ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ, mem_coverX.1 hu, mul_inv_cancel]

@[expose] noncomputable def coverZeta (hZc : π.ker ≤ Subgroup.center M)
    (hαβ : ∀ u, π (α u) = β (π u)) : ↥(coverX π β) →* M where
  toFun x := α x.1 * x.1⁻¹
  map_one' := by simp
  map_mul' x y := by
    have hc : α y.1 * y.1⁻¹ ∈ Subgroup.center M := hZc (alpha_mul_inv_mem_ker hαβ y.2)
    have h2 := Subgroup.mem_center_iff.1 hc (α x.1)
    show α (x.1 * y.1) * (x.1 * y.1)⁻¹ = (α x.1 * x.1⁻¹) * (α y.1 * y.1⁻¹)
    calc α (x.1 * y.1) * (x.1 * y.1)⁻¹ = α x.1 * (α y.1 * y.1⁻¹) * x.1⁻¹ := by
          rw [map_mul, mul_inv_rev]; group
      _ = α x.1 * ((α y.1 * y.1⁻¹) * x.1⁻¹) := by rw [mul_assoc]
      _ = α x.1 * (x.1⁻¹ * (α y.1 * y.1⁻¹)) := by
          rw [← Subgroup.mem_center_iff.1 hc x.1⁻¹]
      _ = (α x.1 * x.1⁻¹) * (α y.1 * y.1⁻¹) := by rw [mul_assoc]

theorem coverZeta_mem_ker (hZc : π.ker ≤ Subgroup.center M) (hαβ : ∀ u, π (α u) = β (π u))
    (x : ↥(coverX π β)) : coverZeta hZc hαβ x ∈ π.ker := alpha_mul_inv_mem_ker hαβ x.2

theorem map_ker_coverZeta (hZc : π.ker ≤ Subgroup.center M) (hαβ : ∀ u, π (α u) = β (π u)) :
    (coverZeta hZc hαβ).ker.map (coverX π β).subtype = u4Fix α := by
  ext u
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : α x.1 * x.1⁻¹ = 1 := hx
    exact mul_inv_eq_one.1 h1
  · intro hu
    refine ⟨⟨u, fix_le_coverX hαβ hu⟩, ?_, rfl⟩
    show α u * u⁻¹ = 1
    have : α u = u := hu
    rw [this, mul_inv_cancel]

end CentralCover

section CentralCover2

variable {M S : Type} [Group M] [Finite M] [Group S] [Finite S]
  {π : M →* S} {α : MulAut M} {β : MulAut S}

theorem pPrimeCore_coverX_eq_bot (hZc : π.ker ≤ Subgroup.center M)
    (hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1) (hαβ : ∀ u, π (α u) = β (π u))
    (h : CFSG.pPrimeCore 3 ↥(u4Fix α) = ⊥) : CFSG.pPrimeCore 3 ↥(coverX π β) = ⊥ := by
  apply pPrimeCore_eq_bot_of_ker_range (coverZeta hZc hαβ)
  · let e : ↥(coverZeta hZc hαβ).ker ≃* ↥(u4Fix α) :=
      (Subgroup.equivMapOfInjective (coverZeta hZc hαβ).ker (coverX π β).subtype
        (coverX π β).subtype_injective).trans
        (MulEquiv.subgroupCongr (map_ker_coverZeta hZc hαβ))
    exact pPrimeCore_eq_bot_of_mulEquiv e h
  · apply pPrimeCore_eq_bot_of_exponent
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨x, hx⟩ := g.2
    apply Subtype.ext
    show (g : M) ^ 3 = 1
    rw [← hx]
    exact hZ3 _ (coverZeta_mem_ker hZc hαβ x)

theorem pPrimeCore_fix_of_central_cover (hπ : Function.Surjective π)
    (hZc : π.ker ≤ Subgroup.center M) (hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1)
    (hαβ : ∀ u, π (α u) = β (π u)) (h : CFSG.pPrimeCore 3 ↥(u4Fix α) = ⊥) :
    CFSG.pPrimeCore 3 ↥(u4Fix β) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hX := pPrimeCore_coverX_eq_bot hZc hZ3 hαβ h
  let f : ↥(coverX π β) →* ↥(u4Fix β) :=
    (π.comp (coverX π β).subtype).codRestrict (u4Fix β) (fun x => x.2)
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨u, hu⟩ := hπ c.1
    exact ⟨⟨u, by show π u ∈ u4Fix β; rw [hu]; exact c.2⟩, Subtype.ext hu⟩
  have hxk : ∀ x ∈ f.ker, (x : M) ∈ π.ker := by
    intro x hx
    have h1 : f x = 1 := hx
    exact congrArg Subtype.val h1
  have hcent : f.ker ≤ Subgroup.center ↥(coverX π β) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZc (hxk x hx)) y.1)
  have hp : IsPGroup 3 f.ker := fun x => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    show (x.1.1 : M) ^ 3 = 1
    exact hZ3 _ (hxk x.1 x.2)⟩
  have := CFSG.central_p_kernel_prime_core_image f hf hcent hp
  show CFSG.pPrimeCore 3 ↥(u4Fix β) = ⊥
  rw [this, hX, Subgroup.map_bot]

theorem exists_perfect_of_central_cover (hπ : Function.Surjective π)
    (hZc : π.ker ≤ Subgroup.center M) (hαβ : ∀ u, π (α u) = β (π u))
    (hq : HasU4Quot (u4Fix β)) :
    ∃ L : Subgroup M, L ≤ u4Fix α ∧ Group.IsPerfect ↥L ∧ 25920 ∣ Nat.card L := by
  obtain ⟨A, T, _, _, _, hAC, hT, fA, hfA⟩ := hq
  let A' : Subgroup M := A.comap π
  have hA'X : A' ≤ coverX π β := fun u hu => hAC hu
  let g : ↥A' →* ↥A := (π.comp A'.subtype).codRestrict A (fun x => x.2)
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨u, hu⟩ := hπ a.1
    exact ⟨⟨u, by show π u ∈ A; rw [hu]; exact a.2⟩, Subtype.ext hu⟩
  have hq' : HasU4Quot (coverX π β) := HasU4Quot.of_surj hA'X hT (fA.comp g) (hfA.comp hg)
  have hcomm : ∀ x ∈ coverX π β, ∀ y ∈ coverX π β, ⁅x, y⁆ ∈ u4Fix α := by
    intro x hx y hy
    let x' : ↥(coverX π β) := ⟨x, hx⟩
    let y' : ↥(coverX π β) := ⟨y, hy⟩
    have h1 : coverZeta hZc hαβ ⁅x', y'⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.1 (hZc (coverZeta_mem_ker hZc hαβ y')) _
    have h2 : α ⁅x, y⁆ * ⁅x, y⁆⁻¹ = 1 := h1
    exact mul_inv_eq_one.1 h2
  have hq'' := hq'.of_comm_le (fix_le_coverX hαβ) hcomm
  obtain ⟨L, hL, hperf, hdvd⟩ := hq''.exists_perfect
  exact ⟨L, hL, hperf, hdvd⟩

end CentralCover2

end CFSG.LocalAnalysis.GLTheoremA.CatB

end

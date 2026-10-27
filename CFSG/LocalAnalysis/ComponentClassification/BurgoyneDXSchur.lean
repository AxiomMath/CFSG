module

public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG Subgroup
open scoped commutatorElement MatrixGroups

variable {G L : Type} [Group G] [Group L] [Finite G] [Finite L]

omit [Finite G] in
theorem commutatorElement_mul_mul_center {a b z z' : G} (hz : z ∈ center G)
    (hz' : z' ∈ center G) : ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
  have hzc : ∀ w : G, w * z = z * w := Subgroup.mem_center_iff.mp hz
  have hz'c : ∀ w : G, w * z' = z' * w := Subgroup.mem_center_iff.mp hz'
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * z') * (a * z)⁻¹ * (b * z')⁻¹
      = a * (z * b) * z' * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z' * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by rw [← hzc b]
    _ = a * b * (z * z') * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by group
    _ = a * b * (z' * z) * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by rw [← hzc z']
    _ = a * b * (z' * a⁻¹) * z'⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z') * z'⁻¹ * b⁻¹ := by rw [← hz'c a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem perfectLift_spec (α : G →* L) (hα : Function.Surjective α) (hker : α.ker ≤ center G)
    (hker2 : IsPGroup 2 α.ker) {Q : Subgroup L} (hQ : ⁅Q, Q⁆ = Q) {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (e : Q ⧸ pPrimeCore 2 Q ≃* SL(2, F)) :
    ⁅Q.comap α, Q.comap α⁆.map α = Q ∧
      ⁅⁅Q.comap α, Q.comap α⁆, ⁅Q.comap α, Q.comap α⁆⁆ = ⁅Q.comap α, Q.comap α⁆ ∧
      ∀ x ∈ ⁅Q.comap α, Q.comap α⁆, α x = 1 → x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₁ := Q.comap α with hT₁
  set T := ⁅T₁, T₁⁆ with hT
  have hT₁Q : T₁.map α = Q := map_comap_eq_self_of_surjective hα Q
  have hTQ : T.map α = Q := by rw [hT, map_commutator, hT₁Q, hQ]
  have hdec : ∀ x ∈ T₁, ∃ t ∈ T, ∃ z ∈ center G, x = t * z := by
    intro x hx
    have hx' : α x ∈ T.map α := by
      rw [hTQ]
      exact hx
    obtain ⟨t, ht, htx⟩ := hx'
    refine ⟨t, ht, t⁻¹ * x, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, htx, inv_mul_cancel]
  have hTT : ⁅T, T⁆ = T := by
    refine le_antisymm (Subgroup.commutator_le_self T) ?_
    change ⁅T₁, T₁⁆ ≤ ⁅T, T⁆
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨t, ht, z, hz, rfl⟩ := hdec x hx
    obtain ⟨t', ht', z', hz', rfl⟩ := hdec y hy
    rw [commutatorElement_mul_mul_center hz hz']
    exact commutator_mem_commutator ht ht'
  refine ⟨hTQ, hTT, ?_⟩
  have hTp : Group.IsPerfect T := Subgroup.isPerfect_iff.mpr hTT
  have hmem : ∀ x : T, α x ∈ Q := fun x => by
    rw [← hTQ]
    exact mem_map_of_mem α x.2
  let ρ : T →* Q := (α.comp T.subtype).codRestrict Q hmem
  have hρone : ∀ x : T, ρ x = 1 ↔ α x = 1 := fun x =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hρ : Function.Surjective ρ := by
    rintro ⟨q, hq⟩
    rw [← hTQ] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, hx⟩, rfl⟩
  have hρker : ρ.ker ≤ center T := by
    intro x hx
    have h2 : (x : G) ∈ center G := hker (MonoidHom.mem_ker.mpr ((hρone x).mp hx))
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp h2 g)
  have hρ2 : IsPGroup 2 ρ.ker := by
    intro x
    obtain ⟨k, hk⟩ := hker2 ⟨(x : T), MonoidHom.mem_ker.mpr ((hρone x).mp x.2)⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : α.ker => ((y : G))) hk
    simpa using this
  have hcore : pPrimeCore 2 Q = (pPrimeCore 2 T).map ρ :=
    central_p_kernel_prime_core_image ρ hρ hρker hρ2
  have hle : pPrimeCore 2 T ≤ (pPrimeCore 2 Q).comap ρ := by
    rw [hcore]
    exact le_comap_map ρ _
  let π : T ⧸ pPrimeCore 2 T →* SL(2, F) :=
    e.toMonoidHom.comp (QuotientGroup.map _ _ ρ hle)
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨x, rfl⟩ := hρ q
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hπker : ∀ x : T, π (QuotientGroup.mk x) = 1 →
      ∃ n ∈ ρ.ker, (QuotientGroup.mk x : T ⧸ pPrimeCore 2 T) = QuotientGroup.mk n := by
    intro x hx
    change e (QuotientGroup.mk (ρ x)) = 1 at hx
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, hcore] at hx
    obtain ⟨o, ho, hox⟩ := hx
    refine ⟨o⁻¹ * x, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hox, inv_mul_cancel]
    · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        (QuotientGroup.eq_one_iff o).mpr ho, inv_one, one_mul]
  have hπcen : π.ker ≤ center (T ⧸ pPrimeCore 2 T) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨n, hn, hxn⟩ := hπker x hy
    rw [hxn, mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp (hρker hn) g']
  have hπ2 : IsPGroup 2 π.ker := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (y : T ⧸ pPrimeCore 2 T)
    obtain ⟨n, hn, hxn⟩ := hπker x (by rw [hx]; exact y.2)
    obtain ⟨k, hk⟩ := hρ2 ⟨n, hn⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : n ^ 2 ^ k = 1 := congrArg Subtype.val hk
    change (y : T ⧸ pPrimeCore 2 T) ^ 2 ^ k = 1
    rw [← hx, hxn, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  obtain ⟨τ, -, -, e', he'⟩ :=
    CFSG.LieType.Steinberg.sl_central_two_extension_splitting 1 hF hπ hπcen hπ2
  have hEp : Group.IsPerfect (T ⧸ pPrimeCore 2 T) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 T))
      (QuotientGroup.mk'_surjective _)
  have hkerbot : ∀ a : π.ker, a = 1 := by
    have hcomm : ∀ a b : π.ker, a * b = b * a := fun a b =>
      Subtype.ext (mem_center_iff.mp (hπcen a.2) b).symm
    let f : T ⧸ pPrimeCore 2 T →* π.ker :=
      (MonoidHom.fst π.ker τ.range).comp e'.symm.toMonoidHom
    have hk : ⁅(⊤ : Subgroup (T ⧸ pPrimeCore 2 T)), ⊤⁆ ≤ f.ker := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    have htop : ⁅(⊤ : Subgroup (T ⧸ pPrimeCore 2 T)), ⊤⁆ = ⊤ := hEp.commutator_eq_top
    intro a
    have h1 : e'.symm (a : T ⧸ pPrimeCore 2 T) = (a, 1) := by
      apply e'.injective
      rw [MulEquiv.apply_symm_apply, he']
      simp
    have h2 : f (a : T ⧸ pPrimeCore 2 T) = 1 :=
      MonoidHom.mem_ker.mp (hk (by rw [htop]; exact mem_top _))
    change (e'.symm (a : T ⧸ pPrimeCore 2 T)).1 = 1 at h2
    rw [h1] at h2
    exact h2
  intro x hx h1
  have hn : (⟨x, hx⟩ : T) ∈ ρ.ker := MonoidHom.mem_ker.mpr ((hρone ⟨x, hx⟩).mpr h1)
  have hπn : π (QuotientGroup.mk ⟨x, hx⟩) = 1 := by
    change e (QuotientGroup.mk (ρ ⟨x, hx⟩)) = 1
    rw [MonoidHom.mem_ker.mp hn, QuotientGroup.mk_one, map_one]
  have h3 := hkerbot ⟨_, hπn⟩
  have h4 : (⟨x, hx⟩ : T) ∈ pPrimeCore 2 T := by
    rw [← QuotientGroup.eq_one_iff]
    exact congrArg Subtype.val h3
  have hodd : Nat.Coprime 2 (orderOf (⟨x, hx⟩ : T)) := by
    have hdvd : orderOf (⟨⟨x, hx⟩, h4⟩ : pPrimeCore 2 T) ∣ Nat.card (pPrimeCore 2 T) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card
  obtain ⟨k, hk⟩ := hρ2 ⟨_, hn⟩
  have hk' : (⟨x, hx⟩ : T) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hord : orderOf (⟨x, hx⟩ : T) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h1' : orderOf (⟨x, hx⟩ : T) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm (Nat.Coprime.pow_right k hodd.symm).symm) hord
  have := orderOf_eq_one_iff.mp h1'
  exact congrArg Subtype.val this

end CFSG.ComponentClassification.Burgoyne.DX

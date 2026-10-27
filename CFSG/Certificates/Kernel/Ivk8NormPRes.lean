module

public import CFSG.Certificates.Kernel.Ivk8NormPGlue

public section

namespace CFSG.KS.Ivk8NormP

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.PK Subgroup

variable {N k : ℕ} (o : Fin k ↪ Fin N)

@[expose] def resStab : Subgroup (Equiv.Perm (Fin N)) where
  carrier := {g | ∀ i, g (o i) ∈ Set.range o ∧ g⁻¹ (o i) ∈ Set.range o}
  one_mem' := fun i => ⟨⟨i, rfl⟩, ⟨i, rfl⟩⟩
  mul_mem' := by
    intro g h hg hh i
    refine ⟨?_, ?_⟩
    · obtain ⟨j, hj⟩ := (hh i).1
      rw [Equiv.Perm.mul_apply, ← hj]
      exact (hg j).1
    · obtain ⟨j, hj⟩ := (hg i).2
      rw [mul_inv_rev, Equiv.Perm.mul_apply, ← hj]
      exact (hh j).2
  inv_mem' := by
    intro g hg i
    rw [inv_inv]
    exact ⟨(hg i).2, (hg i).1⟩

variable {o}

noncomputable def resF (g : resStab o) (i : Fin k) : Fin k := Classical.choose (g.2 i).1

theorem o_resF (g : resStab o) (i : Fin k) : o (resF g i) = (g : Equiv.Perm (Fin N)) (o i) :=
  Classical.choose_spec (g.2 i).1

theorem resF_inv (g : resStab o) (i : Fin k) : resF g⁻¹ (resF g i) = i := by
  apply o.injective
  rw [o_resF, o_resF, Subgroup.coe_inv]
  simp

variable (o)

noncomputable def resHom : resStab o →* Equiv.Perm (Fin k) where
  toFun g :=
    { toFun := resF g
      invFun := resF g⁻¹
      left_inv := resF_inv g
      right_inv := fun i => by simpa using resF_inv g⁻¹ i }
  map_one' := by
    ext i
    congr 1
    apply o.injective
    rw [Equiv.coe_fn_mk, o_resF]
    rfl
  map_mul' := by
    intro g h
    ext i
    congr 1
    apply o.injective
    simp only [Equiv.coe_fn_mk, Equiv.Perm.mul_apply]
    rw [o_resF, o_resF, o_resF]
    rfl

variable {o}

theorem o_resHom (g : resStab o) (i : Fin k) : o (resHom o g i) = (g : Equiv.Perm (Fin N)) (o i) :=
  o_resF g i

theorem mem_resStab_of {g : Equiv.Perm (Fin N)} {σ : Equiv.Perm (Fin k)}
    (h : ∀ i, g (o i) = o (σ i)) : g ∈ resStab o := by
  intro i
  refine ⟨⟨σ i, (h i).symm⟩, ⟨σ⁻¹ i, ?_⟩⟩
  rw [Equiv.Perm.eq_inv_iff_eq, h]
  simp

theorem resHom_eq {g : Equiv.Perm (Fin N)} (hg : g ∈ resStab o) {σ : Equiv.Perm (Fin k)}
    (h : ∀ i, g (o i) = o (σ i)) : resHom o ⟨g, hg⟩ = σ := by
  ext i
  congr 1
  apply o.injective
  rw [o_resHom, h]

theorem res_injOn {K : Subgroup (Equiv.Perm (Fin N))} (hK : K ≤ resStab o)
    {L : Subgroup (Equiv.Perm (Fin k))}
    (hL : ∀ l ∈ L, ∃ x, ∃ hx : x ∈ K, resHom o ⟨x, hK hx⟩ = l)
    (hcard : Nat.card K ≤ Nat.card L) :
    (∀ x (hx : x ∈ K), resHom o ⟨x, hK hx⟩ ∈ L) ∧
      ∀ x (hx : x ∈ K) y (hy : y ∈ K), resHom o ⟨x, hK hx⟩ = resHom o ⟨y, hK hy⟩ → x = y := by
  classical
  let φ : K →* Equiv.Perm (Fin k) := (resHom o).comp (Subgroup.inclusion hK)
  have hφ : ∀ x : K, φ x = resHom o ⟨x, hK x.2⟩ := fun _ => rfl
  have hLr : L ≤ φ.range := by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := hL l hl
    exact ⟨⟨x, hx⟩, rfl⟩
  have hr : Nat.card φ.range ≤ Nat.card K := by
    exact Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  have hLeq : L = φ.range :=
    Subgroup.eq_of_le_of_card_ge hLr (hr.trans hcard)
  have hcardEq : Nat.card K = Nat.card φ.range :=
    le_antisymm (hcard.trans (Subgroup.card_le_of_le hLr)) hr
  have hinj : Function.Injective φ.rangeRestrict :=
    ((Nat.bijective_iff_surjective_and_card _).2 ⟨φ.rangeRestrict_surjective, hcardEq⟩).1
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · rw [hLeq]
    exact ⟨⟨x, hx⟩, rfl⟩
  · have : φ.rangeRestrict ⟨x, hx⟩ = φ.rangeRestrict ⟨y, hy⟩ := Subtype.ext hxy
    exact congrArg Subtype.val (hinj this)

theorem mem_zpowers_sub {G : Type*} [Group G] {S : Subgroup G} (y u : S) :
    u ∈ zpowers y ↔ (u : G) ∈ zpowers (y : G) := by
  simp only [mem_zpowers_iff, Subtype.ext_iff, coe_zpow]

theorem hN_of_res (hk : k < 16777216) (hw : k + 1 < 2 ^ wd k) {p : ℕ} (hp : p.Prime) {K H : Subgroup (Equiv.Perm (Fin N))}
    (hK : K ≤ resStab o)
    (hinj : ∀ x (hx : x ∈ K) y (hy : y ∈ K), resHom o ⟨x, hK hx⟩ = resHom o ⟨y, hK hy⟩ → x = y)
    (c : Equiv.Perm (Fin N)) {F L : List (VP k)}
    (hF : ∀ f ∈ F, ∃ x ∈ H, ∃ hx : c⁻¹ * x * c ∈ resStab o, resHom o ⟨_, hx⟩ = pkp f)
    (hL : ∀ y (hy : y ∈ K), ∃ y' ∈ L, resHom o ⟨y, hK hy⟩ = pkp y')
    (h : chkP k (wd k) p ((subprodsV F).tail.map Subtype.val) (L.map fun y => y.1.1) = true) :
    ∀ y ∈ K, orderOf y = p →
      ∃ g ∈ H, g ∉ normalizer (zpowers (c * y * c⁻¹) : Set (Equiv.Perm (Fin N))) := by
  classical
  intro y hy hyo
  obtain ⟨y', hy'L, hyy'⟩ := hL y hy
  let φ : K →* Equiv.Perm (Fin k) := (resHom o).comp (Subgroup.inclusion hK)
  have hφ : Function.Injective φ := fun a b hab => Subtype.ext (hinj a a.2 b b.2 hab)
  have hyo' : orderOf (pkp y') = p := by
    have e : φ ⟨y, hy⟩ = pkp y' := hyy'
    rw [← e, orderOf_injective φ hφ, Subgroup.orderOf_mk, hyo]
  obtain ⟨g, hg, hgN⟩ := chkP_spec (by omega) hk hw hp h y' hy'L hyo'
  have hgS := pkp_mem_closure_of_subprods F g (List.mem_of_mem_tail hg)
  have hcl : closure {x | x ∈ F.map pkp} ≤
      (((H.map (MulAut.conj c⁻¹).toMonoidHom).subgroupOf (resStab o)).map (resHom o)) := by
    rw [closure_le]
    rintro _ hz
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hz
    obtain ⟨x, hxH, hx, e⟩ := hF f hf
    refine ⟨⟨_, hx⟩, ?_, e⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact ⟨x, hxH, by simp⟩
  obtain ⟨z, hzH, hz⟩ := hcl hgS
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hzH
  obtain ⟨h0, h0H, hh0⟩ := hzH
  have hh0' : (z : Equiv.Perm (Fin N)) = c⁻¹ * h0 * c := by
    rw [← hh0]
    simp
  refine ⟨h0, h0H, fun hN => hgN ?_⟩
  have hconj : ∀ u, c * u * c⁻¹ ∈ zpowers (c * y * c⁻¹) ↔ u ∈ zpowers y := by
    intro u
    have hmap : (zpowers y).map (MulAut.conj c).toMonoidHom = zpowers (c * y * c⁻¹) := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [← hmap]
    exact mem_map_iff_mem (MulAut.conj c).injective
  have hzN : (z : Equiv.Perm (Fin N)) ∈ normalizer (zpowers y : Set (Equiv.Perm (Fin N))) := by
    rw [mem_normalizer_iff] at hN ⊢
    intro u
    have e2 := hN (c * u * c⁻¹)
    have e3 : h0 * (c * u * c⁻¹) * h0⁻¹ = c * ((z : Equiv.Perm (Fin N)) * u * (z : Equiv.Perm (Fin N))⁻¹) * c⁻¹ := by
      rw [hh0']
      group
    rw [e3, hconj, hconj] at e2
    exact e2
  have hzN' : z ∈ normalizer (zpowers (⟨y, hK hy⟩ : resStab o) : Set (resStab o)) := by
    rw [mem_normalizer_iff] at hzN ⊢
    intro u
    rw [mem_zpowers_sub, mem_zpowers_sub]
    simpa using hzN u
  have hm := Subgroup.le_normalizer_map (resHom o) ⟨z, hzN', rfl⟩
  rw [MonoidHom.map_zpowers] at hm
  rw [← hz]
  change resHom o z ∈ normalizer (zpowers (pkp y') : Set (Equiv.Perm (Fin k)))
  rw [← hyy']
  exact hm

end CFSG.KS.Ivk8NormP

end

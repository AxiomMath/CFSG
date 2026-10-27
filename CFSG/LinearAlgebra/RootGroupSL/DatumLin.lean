module

public import CFSG.LinearAlgebra.RootGroupSL.Datum

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E V : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup V] [Module k V]

variable (k E) in
@[expose] def stdIota (X : Type) [AddCommGroup X] [Module k X] : E →ₗ[k] DSpace E X :=
  LinearMap.inl k E (X × E)

variable (k E) in
@[expose] def stdPi (X : Type) [AddCommGroup X] [Module k X] : DSpace E X →ₗ[k] E :=
  LinearMap.snd k X E ∘ₗ LinearMap.snd k E (X × E)

theorem stdIota_apply {X : Type} [AddCommGroup X] [Module k X] (t : E) :
    stdIota k E X t = (t, 0, 0) :=
  rfl

theorem stdPi_stdIota {X : Type} [AddCommGroup X] [Module k X] (t : E) :
    stdPi k E X (stdIota k E X t) = 0 :=
  rfl

theorem exists_datumLin [Module.Finite k V] (ι : E →ₗ[k] V) (π : V →ₗ[k] E)
    (h : ∀ t, π (ι t) = 0) (hι : Function.Injective ι) (hπ : Function.Surjective π) :
    ∃ (X' : Type) (_ : AddCommGroup X') (_ : Module k X') (_ : Module.Finite k X')
      (L : V ≃ₗ[k] DSpace E X'), (∀ t, L (ι t) = (t, 0, 0)) ∧ (∀ v, (L v).2.2 = π v) := by
  classical
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hs_apply : ∀ e, π (s e) = e := fun e => by
    have := LinearMap.ext_iff.1 hs e
    simpa using this
  let iota' : E →ₗ[k] LinearMap.ker π :=
    ι.codRestrict (LinearMap.ker π) (fun t => LinearMap.mem_ker.mpr (h t))
  have hiota' : Function.Injective iota' := fun a b hab => hι (Subtype.ext_iff.mp hab)
  obtain ⟨q, hq⟩ := iota'.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hiota')
  have hq_apply : ∀ t, q (iota' t) = t := fun t => by
    have := LinearMap.ext_iff.1 hq t
    simpa using this
  let r : V →ₗ[k] LinearMap.ker π :=
    LinearMap.codRestrict (LinearMap.ker π) (LinearMap.id - s.comp π) (fun v =>
      LinearMap.mem_ker.mpr (by
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
        rw [map_sub, hs_apply (π v), sub_self]))
  let p : V →ₗ[k] E := q.comp r
  have hr_iota : ∀ t, r (ι t) = iota' t := fun t => by
    apply Subtype.ext
    simp only [r, iota', LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, h t, map_zero, sub_zero]
  have hp_iota : ∀ t, p (ι t) = t := fun t => by
    simp only [p, LinearMap.comp_apply, hr_iota t, hq_apply t]
  have hr_s : ∀ e, r (s e) = 0 := fun e => by
    apply Subtype.ext
    simp only [r, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, hs_apply e]
    simp
  have hp_s : ∀ e, p (s e) = 0 := fun e => by
    simp only [p, LinearMap.comp_apply, hr_s e, map_zero]
  let S : Submodule k V := LinearMap.ker p ⊓ LinearMap.ker π
  have hx_kerp : ∀ x : ↥S, p (x : V) = 0 := fun x =>
    LinearMap.mem_ker.mp (Submodule.mem_inf.mp x.2).1
  have hx_kerPi : ∀ x : ↥S, π (x : V) = 0 := fun x =>
    LinearMap.mem_ker.mp (Submodule.mem_inf.mp x.2).2
  let g : V →ₗ[k] ↥S :=
    LinearMap.codRestrict S (LinearMap.id - ι.comp p - s.comp π) (fun v => by
      refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr ?_, LinearMap.mem_ker.mpr ?_⟩
      · simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
        rw [map_sub, map_sub, hp_iota (p v), hp_s (π v)]
        simp
      · simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
        rw [map_sub, map_sub, h (p v), hs_apply (π v)]
        simp)
  let L : V ≃ₗ[k] DSpace E ↥S :=
    { toFun := fun v => (p v, g v, π v)
      invFun := fun w => ι w.1 + (w.2.1 : V) + s w.2.2
      map_add' := fun u v => by
        ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
      map_smul' := fun c v => by
        ext <;> simp [smul_add]
      left_inv := fun v => by
        change ι (p v) + ((g v : ↥S) : V) + s (π v) = v
        have hg : ((g v : ↥S) : V) = v - ι (p v) - s (π v) := by
          simp only [g, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
            LinearMap.comp_apply]
        rw [hg]
        abel
      right_inv := fun w => by
        obtain ⟨a, x, b⟩ := w
        have h1 : p (ι a + (x : V) + s b) = a := by
          rw [map_add, map_add, hp_iota a, hx_kerp x, hp_s b]
          abel
        have h3 : π (ι a + (x : V) + s b) = b := by
          rw [map_add, map_add, h a, hx_kerPi x, hs_apply b]
          abel
        have h2 : g (ι a + (x : V) + s b) = x := by
          apply Subtype.ext
          have hg' : ((g (ι a + (x : V) + s b) : ↥S) : V) =
              (ι a + (x : V) + s b) - ι (p (ι a + (x : V) + s b))
                - s (π (ι a + (x : V) + s b)) := by
            simp only [g, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
              LinearMap.comp_apply]
          rw [hg', h1, h3]
          abel
        exact Prod.ext h1 (Prod.ext h2 h3) }
  refine ⟨↥S, inferInstance, inferInstance, inferInstance, L, ?_, ?_⟩
  · intro t
    have hg0 : g (ι t) = 0 := by
      apply Subtype.ext
      simp only [g, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.comp_apply, hp_iota t, h t, map_zero]
      simp
    show (p (ι t), g (ι t), π (ι t)) = ((t, 0, 0) : E × ↥S × E)
    simp only [hp_iota t, h t, hg0]
  · intro v
    rfl

end CFSG.LinearAlgebra.RootGroupSL

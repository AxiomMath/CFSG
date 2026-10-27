module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Fam
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a : G} {α : G → G'}

private lemma mem_Gx_conj_iff {G' : Type} [Group G'] {c u v : G'} (hcu : Commute c u) :
    u ∈ Gx (c * v * c⁻¹) ↔ u ∈ Gx v := by
  have hcu' : c * u * c⁻¹ = u := by
    rw [hcu.eq, mul_assoc, mul_inv_cancel, mul_one]
  have h1 : Commute (c * v * c⁻¹) (c * u * c⁻¹) ↔ Commute (c * v * c⁻¹) u := by
    rw [hcu']
  rw [mem_Gx, mem_Gx]
  exact h1.symm.trans (Commute.conj_iff c)

private lemma conj_conj_comm {G' : Type} [Group G'] {b c v : G'} (h : Commute b c) :
    c * (b * v * b⁻¹) * c⁻¹ = b * (c * v * c⁻¹) * b⁻¹ := by
  calc c * (b * v * b⁻¹) * c⁻¹ = (c * b) * v * (c * b)⁻¹ := by group
    _ = (b * c) * v * (b * c)⁻¹ := by rw [h.eq.symm]
    _ = b * (c * v * c⁻¹) * b⁻¹ := by group

theorem cp_conj_mem_Gxy {x y s g : G} (hs : s ∈ Gx a) (hsx : s * x * s⁻¹ = y)
    (hg : g ∈ Gxy a y) : s⁻¹ * g * s ∈ Gxy a x := by
  have hga : s⁻¹ * g * s ∈ Gx a :=
    (Gx a).mul_mem ((Gx a).mul_mem ((Gx a).inv_mem hs) (mem_Gxy.1 hg).1) hs
  refine mem_Gxy.2 ⟨hga, ?_⟩
  rw [mem_Gx]
  have hgy : y * g = g * y := mem_Gx.mp (mem_Gxy.1 hg).2
  have hxs : x = s⁻¹ * y * s := by
    rw [← hsx]
    group
  rw [hxs]
  calc (s⁻¹ * y * s) * (s⁻¹ * g * s) = s⁻¹ * (y * g) * s := by group
    _ = s⁻¹ * (g * y) * s := by rw [hgy]
    _ = (s⁻¹ * g * s) * (s⁻¹ * y * s) := by group

theorem cp_alpha_iso (F : Fam a α) (ha : orderOf a = 2) : IsIsoOn (Gx a) (Gx (α a)) α := by
  have h1 := F.iso a ⟨self_mem_Gx a, ha⟩
  exact h1.congr fun x hx => F.restrict a ⟨self_mem_Gx a, ha⟩ x (mem_Gxy.2 ⟨hx, hx⟩)

theorem cp_alpha_cent_gen (F : Fam a α) {r x g : G} (hr : r ∈ InvIn (Gx a)) (hx : x ∈ Gx r)
    (hg : g ∈ Gxyz a r x) : α g ∈ Gx (F.app r x) := by
  have hz := mem_Gxyz.1 hg
  have hgr : g ∈ Gxy a r := mem_Gxy.2 ⟨hz.1, hz.2.1⟩
  have hxg : x * g = g * x := mem_Gx.mp hz.2.2
  have hrestrict : F.app r g = α g := F.restrict r hr g hgr
  have key : F.app r (x * g) = F.app r (g * x) := by rw [hxg]
  rw [(F.iso r hr).map_mul x hx g hz.2.1,
    (F.iso r hr).map_mul g hz.2.1 x hx, hrestrict] at key
  exact mem_Gx.mpr key

theorem cp_alpha_cent_conj (F : Fam a α) (ha : orderOf a = 2) {s g : G} (hs : s ∈ Gx a)
    (hg : g ∈ Gx a) {v : G'} (h : α (s⁻¹ * g * s) ∈ Gx v) : α g ∈ Gx (α s * v * (α s)⁻¹) := by
  have hxK : s⁻¹ * g * s ∈ Gx a :=
    (Gx a).mul_mem ((Gx a).mul_mem ((Gx a).inv_mem hs) hg) hs
  have hconj := IsIsoOn.map_conj (cp_alpha_iso F ha) hs hxK
  have e : s * (s⁻¹ * g * s) * s⁻¹ = g := by group
  rw [e] at hconj
  have hvw : Commute v (α (s⁻¹ * g * s)) := mem_Gx.mp h
  have hC : Commute (α s * v * (α s)⁻¹) (α s * α (s⁻¹ * g * s) * (α s)⁻¹) :=
    (Commute.conj_iff (α s)).mpr hvw
  rw [hconj]
  exact mem_Gx.mpr hC

theorem cp_cent_transfer (F : Fam a α) (ha : orderOf a = 2) {x g r r' : G}
    (hr' : r' ∈ InvIn (Gx a)) (hx : x ∈ Gx r') (hg : g ∈ Gx a)
    (h : F.app r x = F.app r' x ∨ F.app r x = F.app r' (a * x * a⁻¹)) :
    α g ∈ Gx (F.app r x) ↔ α g ∈ Gx (F.app r' x) := by
  have hcomm : Commute (α a) (α g) := by
    have h1 : α (a * g) = α a * α g := (cp_alpha_iso F ha).map_mul a (self_mem_Gx a) g hg
    have h2 : α (g * a) = α g * α a := (cp_alpha_iso F ha).map_mul g hg a (self_mem_Gx a)
    rw [mem_Gx.mp hg] at h1
    exact h1.symm.trans h2
  have hra : a * r' * a⁻¹ = r' := by
    rw [mem_Gx.mp hr'.1, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : F.app r' (a * x * a⁻¹) = α a * F.app r' x * (α a)⁻¹ := by
    have he := F.equivariant r' hr' a (self_mem_Gx a) x hx
    rwa [hra] at he
  rcases h with h | h
  · rw [h]
  · rw [h, hconj]
    exact mem_Gx_conj_iff hcomm

theorem cp_star (F : Fam a α) (ha : orderOf a = 2) {x : G} {R : Set G} (hR : IsInvReps a x R)
    (hagree : ∀ r ∈ R, ∀ r' ∈ R,
      F.app r x = F.app r' x ∨ F.app r x = F.app r' (a * x * a⁻¹)) :
    ∀ r ∈ R, ∀ g ∈ Gxy a x, α g ∈ Gx (F.app r x) := by
  intro r hr g hg
  have hmain : ∀ g ∈ Subgroup.closure (⋃ r ∈ R, (Gxyz a r x : Set G)),
      g ∈ Gx a ∧ α g ∈ Gx (F.app r x) := by
    intro g hgcl
    refine Subgroup.closure_induction (p := fun z _ => z ∈ Gx a ∧ α z ∈ Gx (F.app r x))
      ?_ ?_ ?_ ?_ hgcl
    · intro z hz
      rcases Set.mem_iUnion.mp hz with ⟨r', hz⟩
      rcases Set.mem_iUnion.mp hz with ⟨hr', hz'⟩
      have hsub := hR.subset hr'
      have hrinv : r' ∈ InvIn (Gx a) := ⟨(mem_Gxy.1 hsub.1).1, hsub.2⟩
      have hxr' : x ∈ Gx r' := mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 hsub.1).2).symm
      have hcent : α z ∈ Gx (F.app r' x) := cp_alpha_cent_gen F hrinv hxr' hz'
      refine ⟨(mem_Gxyz.1 hz').1, ?_⟩
      exact (cp_cent_transfer F ha hrinv hxr' (mem_Gxyz.1 hz').1
        (hagree r hr r' hr')).mpr hcent
    · exact ⟨(Gx a).one_mem, by
        rw [(cp_alpha_iso F ha).map_one]
        exact (Gx (F.app r x)).one_mem⟩
    · intro u v hu hv ihu ihv
      refine ⟨(Gx a).mul_mem ihu.1 ihv.1, ?_⟩
      rw [(cp_alpha_iso F ha).map_mul u ihu.1 v ihv.1, mem_Gx]
      have hu' : F.app r x * α u = α u * F.app r x := mem_Gx.mp ihu.2
      have hv' : F.app r x * α v = α v * F.app r x := mem_Gx.mp ihv.2
      calc F.app r x * (α u * α v) = (F.app r x * α u) * α v := by group
        _ = (α u * F.app r x) * α v := by rw [hu']
        _ = α u * (F.app r x * α v) := by group
        _ = α u * (α v * F.app r x) := by rw [hv']
        _ = (α u * α v) * F.app r x := by group
    · intro u hu ihu
      refine ⟨(Gx a).inv_mem ihu.1, ?_⟩
      rw [(cp_alpha_iso F ha).map_inv ihu.1, mem_Gx]
      exact (show Commute (F.app r x) (α u) from mem_Gx.mp ihu.2).inv_right.eq
  exact (hmain g (by rw [hR.generate]; exact hg)).2

theorem cp_transport (F : Fam a α) {x y : G} (hxy : ConjIn (Gx a) x y) {R : Set G}
    (hR : IsInvReps a x R) {t : G} (ht : t ∈ InvIn (Gxy a y)) :
    ∃ r ∈ R, ∃ s ∈ Gx a, s * x * s⁻¹ = y ∧ F.app t y = α s * F.app r x * (α s)⁻¹ := by
  obtain ⟨s₀, hs₀, hs₀x⟩ := hxy
  let t₀ := s₀⁻¹ * t * s₀
  have ht0 : t₀ ∈ InvIn (Gxy a x) := by
    refine ⟨cp_conj_mem_Gxy (a := a) hs₀ hs₀x ht.1, ?_⟩
    have horder : orderOf ((MulAut.conj s₀⁻¹) t) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact ht.2
    simpa [t₀, MulAut.conj_apply] using horder
  obtain ⟨r, hr, hc⟩ := hR.cover t₀ ht0
  obtain ⟨m, hm, hmr⟩ := hc
  let s := s₀ * m
  have hmGx : m ∈ Gx a := (mem_Gxy.1 hm).1
  have hmx : m * x = x * m := (mem_Gx.mp (mem_Gxy.1 hm).2).symm
  have hs : s ∈ Gx a := (Gx a).mul_mem hs₀ hmGx
  have hsx : s * x * s⁻¹ = y := by
    calc s * x * s⁻¹ = s₀ * (m * x) * (s₀ * m)⁻¹ := by
          rw [show s = s₀ * m from rfl]
          group
      _ = s₀ * (x * m) * (s₀ * m)⁻¹ := by rw [hmx]
      _ = s₀ * x * s₀⁻¹ := by group
      _ = y := hs₀x
  have hsr : s * r * s⁻¹ = t := by
    calc s * r * s⁻¹ = s₀ * (m * r * m⁻¹) * s₀⁻¹ := by
          rw [show s = s₀ * m from rfl]
          group
      _ = s₀ * t₀ * s₀⁻¹ := by rw [hmr]
      _ = t := by
        rw [show t₀ = s₀⁻¹ * t * s₀ from rfl]
        group
  have hsub := hR.subset hr
  have hrinv : r ∈ InvIn (Gx a) := ⟨(mem_Gxy.1 hsub.1).1, hsub.2⟩
  have hxr : x ∈ Gx r := mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 hsub.1).2).symm
  refine ⟨r, hr, s, hs, hsx, ?_⟩
  have he := F.equivariant r hrinv s hs x hxr
  rw [hsr, hsx] at he
  exact he

theorem cp_cmp (F : Fam a α) (ha : orderOf a = 2) {x y : G} {R : Set G}
    (hstar : ∀ r ∈ R, ∀ g ∈ Gxy a x, α g ∈ Gx (F.app r x)) {r r' : G} (hr : r ∈ R)
    (hr' : r' ∈ R) {s s' : G} (hs : s ∈ Gx a) (hs' : s' ∈ Gx a) (hsx : s * x * s⁻¹ = y)
    (hsx' : s' * x * s'⁻¹ = y) :
    (F.app r x = F.app r' x →
      α s * F.app r x * (α s)⁻¹ = α s' * F.app r' x * (α s')⁻¹) ∧
    (F.app r x = α a * F.app r' x * (α a)⁻¹ →
      α s * F.app r x * (α s)⁻¹ = α a * (α s' * F.app r' x * (α s')⁻¹) * (α a)⁻¹) := by
  let m := s⁻¹ * s'
  have hmGxa : m ∈ Gx a := (Gx a).mul_mem ((Gx a).inv_mem hs) hs'
  have hmx : m * x * m⁻¹ = x := by
    calc m * x * m⁻¹ = s⁻¹ * (s' * x * s'⁻¹) * s := by
          rw [show m = s⁻¹ * s' from rfl]
          group
      _ = s⁻¹ * y * s := by rw [hsx']
      _ = s⁻¹ * (s * x * s⁻¹) * s := by rw [hsx]
      _ = x := by group
  have hmGx : m ∈ Gx x := by
    rw [mem_Gx]
    calc x * m = (m * x * m⁻¹) * m := by rw [hmx]
      _ = m * x := by group
  have hmGxy : m ∈ Gxy a x := mem_Gxy.2 ⟨hmGxa, hmGx⟩
  have hsm : s * m = s' := by
    rw [show m = s⁻¹ * s' from rfl]
    group
  have halpham : α s' = α s * α m := by
    rw [← hsm, (cp_alpha_iso F ha).map_mul s hs m hmGxa]
  have hcomm : Commute (α s) (α a) := by
    have h1 : α (a * s) = α a * α s := (cp_alpha_iso F ha).map_mul a (self_mem_Gx a) s hs
    have h2 : α (s * a) = α s * α a := (cp_alpha_iso F ha).map_mul s hs a (self_mem_Gx a)
    rw [mem_Gx.mp hs] at h1
    exact h2.symm.trans h1
  have hmV : α m ∈ Gx (F.app r x) := hstar r hr m hmGxy
  have hmW : α m ∈ Gx (F.app r' x) := hstar r' hr' m hmGxy
  constructor
  · intro hV
    have key : α s * α m * F.app r x * (α s * α m)⁻¹
        = α s * F.app r x * (α s)⁻¹ := by
      calc α s * α m * F.app r x * (α s * α m)⁻¹
          = α s * (α m * F.app r x * (α m)⁻¹) * (α s)⁻¹ := by group
        _ = α s * F.app r x * (α s)⁻¹ := by
          rw [show α m * F.app r x * (α m)⁻¹ = F.app r x by
            rw [← mem_Gx.mp hmV]
            group]
    rw [halpham, ← hV, key]
  · intro hV
    have hmcW : α m * F.app r' x * (α m)⁻¹ = F.app r' x := by
      rw [← mem_Gx.mp hmW]
      group
    have keyW : α s * α m * F.app r' x * (α s * α m)⁻¹
        = α s * F.app r' x * (α s)⁻¹ := by
      calc α s * α m * F.app r' x * (α s * α m)⁻¹
          = α s * (α m * F.app r' x * (α m)⁻¹) * (α s)⁻¹ := by group
        _ = α s * F.app r' x * (α s)⁻¹ := by rw [hmcW]
    rw [halpham, keyW, hV]
    exact (conj_conj_comm hcomm).symm

theorem cp_app_conj_a (F : Fam a α) {y t' : G} (ht' : t' ∈ InvIn (Gxy a y)) :
    F.app t' (a * y * a⁻¹) = α a * F.app t' y * (α a)⁻¹ := by
  have hsub := mem_Gxy.1 ht'.1
  have hta : a * t' * a⁻¹ = t' := by
    rw [mem_Gx.mp hsub.1, mul_assoc, mul_inv_cancel, mul_one]
  have hy : y ∈ Gx t' := mem_Gx.2 (mem_Gx.1 hsub.2).symm
  have he := F.equivariant t' ⟨hsub.1, ht'.2⟩ a (self_mem_Gx a) y hy
  rwa [hta] at he

end CFSG.EvenSporadicStandard.HNRecog.Section4

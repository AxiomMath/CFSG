module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

universe u

theorem eq_top_of_sup_le_center_of_isPerfect {G : Type u} [Group G] [Group.IsPerfect G]
    {L Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) (h : L ⊔ Z = ⊤) : L = ⊤ := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := G), _root_.commutator_def,
    Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨l₁, hl₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  obtain ⟨l₂, hl₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top y)
  have hz₁' : z₁ ∈ Subgroup.center G := hZ hz₁
  have hz₂' : z₂ ∈ Subgroup.center G := hZ hz₂
  rw [show l₁ * z₁ = z₁ * l₁ from Subgroup.mem_center_iff.mp hz₁' l₁,
    show l₂ * z₂ = z₂ * l₂ from Subgroup.mem_center_iff.mp hz₂' l₂,
    CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hz₁' hz₂' l₁ l₂]
  exact Subgroup.commutator_le_self L (Subgroup.commutator_mem_commutator hl₁ hl₂)

theorem exists_mulEquiv_comp_eq_of_card_ker_eq_two {C C' P : Type u} [Group C] [Group C']
    [Group P] [Finite C] [Finite C']
    (hC : Group.IsPerfect C) (hC' : Group.IsPerfect C') (π : C →* P) (π' : C' →* P)
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π')
    (hker : π.ker ≤ Subgroup.center C) (hker' : π'.ker ≤ Subgroup.center C')
    (hcard : Nat.card π.ker = 2) (hcard' : Nat.card π'.ker = 2)
    (hcyc : ∀ (D : Type u) [Group D] [Finite D], Group.IsPerfect D →
      ∀ f : D →* P, Function.Surjective f → f.ker ≤ Subgroup.center D → IsCyclic f.ker) :
    ∃ θ : C ≃* C', ∀ c, π' (θ c) = π c := by
  classical
  have hP : Group.IsPerfect P := by
    haveI : Group.IsPerfect C := hC
    exact Group.IsPerfect.ofSurjective hπ
  let F : Subgroup (C × C') := CFSG.LieType.Steinberg.pullback π π'
  let H := ↥F
  let p : H →* C := CFSG.LieType.Steinberg.pullbackFst π π'
  let q : H →* C' := (MonoidHom.snd C C').comp F.subtype
  let f : H →* P := π.comp p
  let D : Subgroup H := commutator H
  let fD : ↥D →* P := f.comp D.subtype
  have hp : Function.Surjective p := CFSG.LieType.Steinberg.pullbackFst_surjective hπ'
  have hq : Function.Surjective q := by
    intro c'
    obtain ⟨c, hc⟩ := hπ (π' c')
    exact ⟨⟨(c, c'), CFSG.LieType.Steinberg.mem_pullback.mpr hc⟩, rfl⟩
  have hf : Function.Surjective f := hπ.comp hp
  have hfq : f = π'.comp q := by
    ext y
    exact CFSG.LieType.Steinberg.mem_pullback.1 y.2
  have hker_f : f.ker ≤ Subgroup.center H := by
    intro y hy
    have hy1' : π (y : C × C').1 = 1 := by
      change π (p y) = 1
      exact MonoidHom.mem_ker.mp hy
    have hy2' : π' (y : C × C').2 = 1 := by
      rw [← CFSG.LieType.Steinberg.mem_pullback.1 y.2]
      exact hy1'
    have hc1 : (y : C × C').1 ∈ Subgroup.center C := hker (MonoidHom.mem_ker.mpr hy1')
    have hc2 : (y : C × C').2 ∈ Subgroup.center C' := hker' (MonoidHom.mem_ker.mpr hy2')
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    apply Prod.ext
    · exact Subgroup.mem_center_iff.mp hc1 (z : C × C').1
    · exact Subgroup.mem_center_iff.mp hc2 (z : C × C').2
  obtain ⟨hsup, hDperf, hfDsurj⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective f hf hker_f hP
  have hpDsurj : Function.Surjective (p.comp D.subtype) := by
    have hmap : D.map p = ⊤ := by
      have h := congrArg (Subgroup.map p) hsup
      rw [Subgroup.map_sup, Subgroup.map_top_of_surjective p hp] at h
      have hkermap : (f.ker).map p ≤ π.ker := by
        rintro c ⟨y, hy, rfl⟩
        exact MonoidHom.mem_ker.mpr (by
          simpa only [f, MonoidHom.comp_apply] using MonoidHom.mem_ker.mp hy)
      apply eq_top_of_sup_le_center_of_isPerfect hker
      apply top_le_iff.mp
      rw [← h]
      exact sup_le le_sup_left (hkermap.trans le_sup_right)
    intro c
    have hc : c ∈ D.map p := hmap.symm ▸ Subgroup.mem_top c
    obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.mp hc
    exact ⟨⟨d, hd⟩, hdc⟩
  have hqDsurj : Function.Surjective (q.comp D.subtype) := by
    have hmap : D.map q = ⊤ := by
      have h := congrArg (Subgroup.map q) hsup
      rw [Subgroup.map_sup, Subgroup.map_top_of_surjective q hq] at h
      have hkermap : (f.ker).map q ≤ π'.ker := by
        rintro c ⟨y, hy, rfl⟩
        have hy' : π' (q y) = 1 := by
          have := MonoidHom.mem_ker.mp hy
          rwa [hfq, MonoidHom.comp_apply] at this
        exact MonoidHom.mem_ker.mpr hy'
      apply eq_top_of_sup_le_center_of_isPerfect hker'
      apply top_le_iff.mp
      rw [← h]
      exact sup_le le_sup_left (hkermap.trans le_sup_right)
    intro c
    have hc : c ∈ D.map q := hmap.symm ▸ Subgroup.mem_top c
    obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.mp hc
    exact ⟨⟨d, hd⟩, hdc⟩
  have hkerD : fD.ker ≤ Subgroup.center ↥D := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker_f hy) (z : H)
  haveI : IsCyclic ↥(fD.ker) := hcyc ↥D hDperf fD hfDsurj hkerD
  have hsq : ∀ y : ↥(fD.ker), y ^ 2 = 1 := by
    intro y
    have hy : f (y.1 : H) = 1 := y.2
    have hy1' : π ((y.1 : H) : C × C').1 = 1 := by
      change π (p (y.1 : H)) = 1
      simpa only [f, MonoidHom.comp_apply] using hy
    have hy2' : π' ((y.1 : H) : C × C').2 = 1 := by
      rw [← CFSG.LieType.Steinberg.mem_pullback.1 (y.1 : H).2]
      exact hy1'
    have h1 : (((y.1 : H) : C × C').1) ^ 2 = 1 := by
      have h := pow_card_eq_one' (G := π.ker) (x := ⟨_, MonoidHom.mem_ker.mpr hy1'⟩)
      rw [hcard] at h
      exact congrArg Subtype.val h
    have h2 : (((y.1 : H) : C × C').2) ^ 2 = 1 := by
      have h := pow_card_eq_one' (G := π'.ker) (x := ⟨_, MonoidHom.mem_ker.mpr hy2'⟩)
      rw [hcard'] at h
      exact congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact h1
    · exact h2
  have hcardDvd : Nat.card ↥(fD.ker) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card (α := ↥(fD.ker))]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hsq
  have hcard_le : Nat.card ↥(fD.ker) ≤ 2 := Nat.le_of_dvd (by norm_num) hcardDvd
  let Φ : ↥(fD.ker) →* π.ker :=
    { toFun := fun y =>
        ⟨p (y.1 : H),
          MonoidHom.mem_ker.mpr (by
            have hy : f (y.1 : H) = 1 := y.2
            change π (p (y.1 : H)) = 1
            simpa only [f, MonoidHom.comp_apply] using hy)⟩
      map_one' := Subtype.ext (map_one p)
      map_mul' := fun a b => Subtype.ext (map_mul p (a.1 : H) (b.1 : H)) }
  have hΦsurj : Function.Surjective Φ := by
    intro c
    obtain ⟨d, hd⟩ := hpDsurj c.1
    have hdmem : d ∈ fD.ker := by
      change f (d : H) = 1
      dsimp only [f]
      rw [MonoidHom.comp_apply]
      have hd' : p (D.subtype d) = (c : C) := by
        change (p.comp D.subtype) d = (c : C)
        exact hd
      change π (p (D.subtype d)) = 1
      rw [hd']
      exact MonoidHom.mem_ker.mp c.2
    refine ⟨⟨d, hdmem⟩, ?_⟩
    apply Subtype.ext
    exact hd
  have hcard_ge : 2 ≤ Nat.card ↥(fD.ker) := by
    rw [← hcard]
    exact Nat.card_le_card_of_surjective Φ hΦsurj
  have hcardD : Nat.card ↥(fD.ker) = 2 := le_antisymm hcard_le hcard_ge
  have hΦker : Φ.ker = ⊥ := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := Φ) hΦsurj
    rw [hcard, hcardD] at h
    have h1 : Nat.card ↥(Φ.ker) = 1 := by omega
    exact Subgroup.card_eq_one.mp h1
  have hKbot : (p.comp D.subtype).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxmem : x ∈ fD.ker := by
      rw [MonoidHom.mem_ker]
      change f (x : H) = 1
      dsimp only [f]
      rw [MonoidHom.comp_apply]
      have hx' : p (D.subtype x) = 1 := by
        change (p.comp D.subtype) x = 1
        exact MonoidHom.mem_ker.mp hx
      change π (p (D.subtype x)) = 1
      rw [hx', map_one]
    have hxΦ : (⟨x, hxmem⟩ : ↥(fD.ker)) ∈ Φ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change p (D.subtype x) = 1
      exact MonoidHom.mem_ker.mp hx
    rw [hΦker] at hxΦ
    exact congrArg Subtype.val hxΦ
  have hinjC : Function.Injective (p.comp D.subtype) :=
    (MonoidHom.ker_eq_bot_iff _).mp hKbot
  let eC : ↥D ≃* C := MulEquiv.ofBijective (p.comp D.subtype) ⟨hinjC, hpDsurj⟩
  let Ψ : ↥(fD.ker) →* π'.ker :=
    { toFun := fun y =>
        ⟨q (y.1 : H),
          MonoidHom.mem_ker.mpr (by
            have hy : f (y.1 : H) = 1 := y.2
            have hy' : π ((y.1 : H) : C × C').1 = 1 := by
              change π (p (y.1 : H)) = 1
              simpa only [f, MonoidHom.comp_apply] using hy
            dsimp only [q]
            change π' ((y.1 : H) : C × C').2 = 1
            rw [← CFSG.LieType.Steinberg.mem_pullback.1 (y.1 : H).2]
            exact hy')⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun a b => Subtype.ext (map_mul q (a.1 : H) (b.1 : H)) }
  have hΨsurj : Function.Surjective Ψ := by
    intro c
    obtain ⟨d, hd⟩ := hqDsurj c.1
    have hdmem : d ∈ fD.ker := by
      change f (d : H) = 1
      rw [hfq, MonoidHom.comp_apply]
      have hd' : q (D.subtype d) = (c : C') := by
        change (q.comp D.subtype) d = (c : C')
        exact hd
      change π' (q (D.subtype d)) = 1
      rw [hd']
      exact MonoidHom.mem_ker.mp c.2
    refine ⟨⟨d, hdmem⟩, ?_⟩
    apply Subtype.ext
    exact hd
  have hΨker : Ψ.ker = ⊥ := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := Ψ) hΨsurj
    rw [hcard', hcardD] at h
    have h1 : Nat.card ↥(Ψ.ker) = 1 := by omega
    exact Subgroup.card_eq_one.mp h1
  have hKbot' : (q.comp D.subtype).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxmem : x ∈ fD.ker := by
      rw [MonoidHom.mem_ker]
      change f (x : H) = 1
      rw [hfq, MonoidHom.comp_apply]
      have hx' : q (D.subtype x) = 1 := by
        change (q.comp D.subtype) x = 1
        exact MonoidHom.mem_ker.mp hx
      change π' (q (D.subtype x)) = 1
      rw [hx', map_one]
    have hxΨ : (⟨x, hxmem⟩ : ↥(fD.ker)) ∈ Ψ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change q (D.subtype x) = 1
      have hx' : (q.comp D.subtype) x = 1 := MonoidHom.mem_ker.mp hx
      exact hx'
    rw [hΨker] at hxΨ
    exact congrArg Subtype.val hxΨ
  have hinjC' : Function.Injective (q.comp D.subtype) :=
    (MonoidHom.ker_eq_bot_iff _).mp hKbot'
  let eC' : ↥D ≃* C' := MulEquiv.ofBijective (q.comp D.subtype) ⟨hinjC', hqDsurj⟩
  let θ : C ≃* C' := eC.symm.trans eC'
  refine ⟨θ, fun c => ?_⟩
  change π' (eC' (eC.symm c)) = π c
  set d : ↥D := eC.symm c
  have hd : eC d = c := by simp [d]
  have h1 : (eC d : C) = ((d : H) : C × C').1 := rfl
  have h2 : (eC' d : C') = ((d : H) : C × C').2 := rfl
  change π' (eC' d) = π c
  rw [← hd, h2, h1]
  exact (CFSG.LieType.Steinberg.mem_pullback.1 (d : H).2).symm

end CFSG.GroupTheory

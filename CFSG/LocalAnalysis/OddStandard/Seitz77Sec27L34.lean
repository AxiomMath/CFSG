module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L34Core
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L34Ord3
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.KGroups

theorem exists_perfect_preimage {H N : Type*} [Group H] [Finite H] [Group N] (π : H →* N)
    (hπ : Function.Surjective π) (L : Subgroup N) (hL : ⁅L, L⁆ = L) (Xh : Subgroup H)
    (hX : ⁅Xh, Xh⁆ = Xh) (hXL : Xh.map π ≤ L) :
    ∃ K : Subgroup H, Xh ≤ K ∧ K.map π = L ∧ ⁅K, K⁆ = K := by
  have h0 : Xh ≤ L.comap π ∧ (L.comap π).map π = L :=
    ⟨Subgroup.map_le_iff_le_comap.1 hXL, Subgroup.map_comap_eq_self_of_surjective hπ L⟩
  obtain ⟨K, hKle, hmin⟩ := Finite.exists_le_minimal
    (p := fun M : Subgroup H => Xh ≤ M ∧ M.map π = L) (a := L.comap π) h0
  refine ⟨K, hmin.1.1, hmin.1.2, ?_⟩
  have hc : ⁅K, K⁆ ≤ K := Subgroup.commutator_le_self K
  have hXc : Xh ≤ ⁅K, K⁆ :=
    calc Xh = ⁅Xh, Xh⁆ := hX.symm
      _ ≤ ⁅K, K⁆ := Subgroup.commutator_mono hmin.1.1 hmin.1.1
  have hmapc : (⁅K, K⁆).map π = L := by
    rw [Subgroup.map_commutator, hmin.1.2, hL]
  exact le_antisymm hc (hmin.2 ⟨hXc, hmapc⟩ hc)

theorem xh_equiv {N H : Type} [Group N] [Finite N] [Group H]
    {X : Subgroup N} {t : N} (c : Local27 N X t) (π : H →* N) (Xh : Subgroup H)
    (hXh : Xh.map π = X) (hdisj : Disjoint Xh π.ker) :
    Nonempty (↥Xh ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨eX⟩ := c.nonempty_equiv
  let f : Xh →* N := π.comp Xh.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxk : (x : H) ∈ Xh ⊓ π.ker :=
      ⟨x.2, by simpa [f] using hx⟩
    rw [disjoint_iff.1 hdisj, Subgroup.mem_bot] at hxk
    exact Subtype.ext hxk
  have hr : f.range = X := by
    rw [← hXh, MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)).trans eX⟩

theorem notL34
    (hord3 : Certificates.Seitz77Sec27.l34Ord3Check = true) :
    NotL34 := by
  intro N _ _ X t o m h
  obtain ⟨e⟩ := L34.equiv_of_lieModel h
  obtain ⟨H, _, _, ρ, π, hρ, hπ, hker, Xh, hXh, hdisj, hdims, hfpf⟩ := m.exists_module
  obtain ⟨eXh⟩ := xh_equiv o.loc π Xh hXh hdisj
  have hXsimple : IsSimpleGroup Xh :=
    (MulEquiv.isSimpleGroup_congr eXh).2 (alternatingGroup.isSimpleGroup (α := Fin 5) (by simp))
  have hXcard : Nat.card Xh = 60 := by
    rw [Nat.card_congr eXh.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin, Nat.factorial]
  have hXperf : ⁅Xh, Xh⁆ = Xh := by
    have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)⟩
    have hperf : Group.IsPerfect Xh :=
      Group.IsPerfect.ofSurjective (f := eXh.symm.toMonoidHom) eXh.symm.surjective
    exact Subgroup.isPerfect_iff.1 hperf
  have hLperf : ⁅layer N, layer N⁆ = layer N := LocalCores.layer_perfect
  have hXL : Xh.map π ≤ layer N := hXh ▸ o.X_le
  obtain ⟨K, hXK, hKmap, hKperf⟩ := exists_perfect_preimage π hπ (layer N) hLperf Xh hXperf hXL
  have hKmem : ∀ k : K, π k ∈ layer N := fun k => by
    have : π k ∈ K.map π := ⟨k, k.2, rfl⟩
    rwa [hKmap] at this
  have hLcard : Nat.card ↥(layer N) = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_group L34.QP L34.QP_ok, L34.QP_valid.2]
  have hord_e : ∀ z : ↥(layer N), orderOf ((e z : L34.QP.originalSubgroup) : Equiv.Perm (Fin 42)) =
      orderOf z := fun z => by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have hinv2 : ∀ x y : ↥(layer N), x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 →
      ∃ g : ↥(layer N), g * x * g⁻¹ = y := by
    have key : ∀ z : ↥(layer N), z * z = 1 → z ≠ 1 →
        ∃ g : ↥(layer N), e (g * e.symm ⟨L34.x0, L34.x0_mem⟩ * g⁻¹) = e z := by
      intro z hz hz1
      have hz2 : ((e z : L34.QP.originalSubgroup) : Equiv.Perm (Fin 42)) ^ 2 = 1 := by
        have := congrArg (fun a => ((e a : L34.QP.originalSubgroup) : Equiv.Perm (Fin 42))) hz
        simpa [pow_two] using this
      have hz1' : ((e z : L34.QP.originalSubgroup) : Equiv.Perm (Fin 42)) ≠ 1 := by
        intro h1
        apply hz1
        apply e.injective
        exact Subtype.ext (by simpa using h1)
      obtain ⟨g, hg, hgz⟩ := L34.one_class_P _ (e z).2 hz2 hz1'
      refine ⟨e.symm ⟨g, hg⟩, ?_⟩
      apply Subtype.ext
      simpa using hgz
    intro x y hx hy hx1 hy1
    obtain ⟨g₁, h₁⟩ := key x hx hx1
    obtain ⟨g₂, h₂⟩ := key y hy hy1
    refine ⟨g₂ * g₁⁻¹, ?_⟩
    have h1 : g₁ * e.symm ⟨L34.x0, L34.x0_mem⟩ * g₁⁻¹ = x := e.injective h₁
    have h2 : g₂ * e.symm ⟨L34.x0, L34.x0_mem⟩ * g₂⁻¹ = y := e.injective h₂
    rw [← h2, ← h1]
    group
  have hinv3 : ∀ x y : ↥(layer N), orderOf x = 3 → orderOf y = 3 →
      ∃ g : ↥(layer N), g * x * g⁻¹ = y := by
    intro x y hx hy
    obtain ⟨g, hg, hgxy⟩ := l34Ord3Check_sound hord3 _ (e x).2 _ (e y).2
      (by rw [hord_e, hx]) (by rw [hord_e, hy])
    refine ⟨e.symm ⟨g, hg⟩, e.injective ?_⟩
    apply Subtype.ext
    simpa using hgxy
  let ρ₁ : K →* GL (Fin 8) (ZMod 2) := ρ.comp K.subtype
  let π₁ : K →* ↥(layer N) := (π.comp K.subtype).codRestrict (layer N) hKmem
  have hπ₁_apply : ∀ k : K, ((π₁ k : ↥(layer N)) : N) = π k := fun k => rfl
  have hK1 : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
    have : Group.IsPerfect K := Subgroup.isPerfect_iff.2 hKperf
    have h2 := Group.isPerfect_def.1 this
    rwa [commutator_def] at h2
  have hπ₁ : Function.Surjective π₁ := by
    intro s
    have hs : (s : N) ∈ K.map π := by rw [hKmap]; exact s.2
    obtain ⟨k, hk, hks⟩ := hs
    exact ⟨⟨k, hk⟩, Subtype.ext hks⟩
  have hodd : Odd (Nat.card π₁.ker) := by
    let f : π₁.ker →* ↥(oddCore H) :=
      ((K.subtype.comp π₁.ker.subtype).codRestrict (oddCore H) (fun x => by
        rw [← hker, MonoidHom.mem_ker]
        have := congrArg Subtype.val x.2
        rw [hπ₁_apply] at this
        simpa using this))
    have hf : Function.Injective f := by
      intro a b hab
      have := congrArg (fun y => ((y : ↥(oddCore H)) : H)) hab
      exact Subtype.ext (Subtype.ext this)
    exact Odd.of_dvd_nat (CFSG.ABGLocalTools.odd_card_oddCore (H := H))
      (Subgroup.card_dvd_of_injective f hf)
  have hXK' : ∀ x : K, x ∈ Xh.subgroupOf K ↔ (x : H) ∈ Xh := fun x => Subgroup.mem_subgroupOf
  have eXh1 : ↥(Xh.subgroupOf K) ≃* ↥Xh := Subgroup.subgroupOfEquivOfLe hXK
  have hX1simple : IsSimpleGroup ↥(Xh.subgroupOf K) :=
    (MulEquiv.isSimpleGroup_congr eXh1).2 hXsimple
  have hX1card : Nat.card ↥(Xh.subgroupOf K) = 60 := by
    rw [Nat.card_congr eXh1.toEquiv, hXcard]
  have hX1ker : ∀ x ∈ Xh.subgroupOf K, π₁ x = 1 → x = 1 := by
    intro x hx hπx
    have hxk : (x : H) ∈ Xh ⊓ π.ker :=
      ⟨(hXK' x).1 hx, by
        have := congrArg Subtype.val hπx
        rw [hπ₁_apply] at this
        simpa using this⟩
    rw [disjoint_iff.1 hdisj, Subgroup.mem_bot] at hxk
    exact Subtype.ext hxk
  let c : L34Conf K ↥(layer N) :=
    { ρ := ρ₁
      π := π₁
      Xh := Xh.subgroupOf K
      ρ_inj := hρ.comp K.subtype_injective
      π_surj := hπ₁
      perf := hK1
      odd := hodd
      S_simple := o.simple
      S_card := hLcard
      inv2 := hinv2
      inv3 := hinv3
      X_simple := hX1simple
      X_card := hX1card
      X_ker := hX1ker
      dims := fun U hU => hdims U (fun x hx w hw => hU ⟨x, hXK hx⟩ w hw)
      fpf := fun x hx hx3 w hw =>
        hfpf (x : H) ((hXK' x).1 hx) (by rw [Subgroup.orderOf_coe]; exact hx3) w hw }
  exact c.false

end CFSG.OddStandard.Seitz77

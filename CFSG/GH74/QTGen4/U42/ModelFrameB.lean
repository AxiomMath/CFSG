module

public import CFSG.GH74.QTGen4.U42.ModelFrame
public import CFSG.GH74.QTGen4.U42.U0Core

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5 CFSG.Quasithin.H13.F431.U42 U42F431

theorem Vsub_le_P2 :
    Vsub ≤ P2 :=
  Vsub_le_T.trans (T_le_B0.trans B0_le_P2)

theorem T_le_P2' :
    T ≤ P2 :=
  T_le_B0.trans B0_le_P2

theorem mem_L0S_of_P2 {g : Y} (hg : g ∈ P2) {p : Fin 45} (hp : p ∈ L0S) :
    (g : P45) p ∈ L0S := by
  have h := (mem_P2_iff g).1 hg
  rw [← h]
  exact ⟨p, hp, rfl⟩

theorem ptL_invFun {p : Fin 45} (hp : p ∈ L0S) : ptL (Function.invFun ptL p) = p :=
  Function.invFun_eq ((mem_L0S_ptL p).1 hp)

@[expose] noncomputable def permFun (g : ↥P2) (j : Fin 5) : Fin 5 :=
  Function.invFun ptL (((g : Y) : P45) (ptL j))

theorem permFun_mem (g : ↥P2) (j : Fin 5) : ((g : Y) : P45) (ptL j) ∈ L0S :=
  mem_L0S_of_P2 g.2 ((mem_L0S_ptL _).2 ⟨j, rfl⟩)

theorem ptL_permFun (g : ↥P2) (j : Fin 5) :
    ptL (permFun g j) = ((g : Y) : P45) (ptL j) :=
  ptL_invFun (permFun_mem g j)

theorem permFun_injective (g : ↥P2) : Function.Injective (permFun g) := by
  intro j k h
  apply ptL_inj
  have h1 := ptL_permFun g j
  have h2 := ptL_permFun g k
  rw [h] at h1
  exact ((g : Y) : P45).injective (h1.symm.trans h2)

@[expose] noncomputable def permOf (g : ↥P2) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (permFun g) (Finite.injective_iff_bijective.1 (permFun_injective g))

theorem ptL_permOf (g : ↥P2) (j : Fin 5) :
    ptL (permOf g j) = ((g : Y) : P45) (ptL j) :=
  ptL_permFun g j

theorem permOf_mul (g h : ↥P2) : permOf (g * h) = permOf g * permOf h := by
  apply Equiv.ext
  intro j
  apply ptL_inj
  simp only [ptL_permOf, Equiv.Perm.mul_apply, Subgroup.coe_mul]

theorem permOf_one : permOf (1 : ↥P2) = 1 := by
  apply Equiv.ext
  intro j
  apply ptL_inj
  simp [ptL_permOf]

@[expose] noncomputable def permHom : ↥P2 →* Equiv.Perm (Fin 5) where
  toFun := permOf
  map_one' := permOf_one
  map_mul' := permOf_mul

theorem permOf_eq_one_iff
    (g : ↥P2) : permOf g = 1 ↔ (g : Y) ∈ Vsub := by
  constructor
  · intro h
    apply fix_mem_Vsub
    intro p hp
    obtain ⟨j, rfl⟩ := (mem_L0S_ptL p).1 hp
    have := ptL_permOf g j
    rw [h, Equiv.Perm.one_apply] at this
    exact this.symm
  · intro h
    apply Equiv.ext
    intro j
    apply ptL_inj
    rw [ptL_permOf, Equiv.Perm.one_apply]
    exact Vsub_fix h (ptL j) ((mem_L0S_ptL (ptL j)).2 ⟨j, rfl⟩)

theorem card_ker_permHom :
    Nat.card permHom.ker = 16 := by
  rw [← card_Vsub_eq]
  apply Nat.card_congr
  exact
    { toFun := fun g => ⟨(g.1 : Y), (permOf_eq_one_iff g.1).1 (MonoidHom.mem_ker.1 g.2)⟩
      invFun := fun v => ⟨⟨v.1, Vsub_le_P2 v.2⟩,
        (MonoidHom.mem_ker.2 ((permOf_eq_one_iff _).2 v.2) : _)⟩
      left_inv := fun g => Subtype.ext (Subtype.ext rfl)
      right_inv := fun v => Subtype.ext rfl }

theorem card_range_permHom :
    Nat.card permHom.range = 60 := by
  have h1 := Subgroup.index_mul_card (H := permHom.ker)
  rw [card_P2, card_ker_permHom, Subgroup.index_ker] at h1
  omega

theorem sign_permOf_eq_one
    (g : ↥P2) : Equiv.Perm.sign (permOf g) = 1 := by
  by_contra hne
  let R := permHom.range
  let f : ↥R →* ℤˣ := (Equiv.Perm.sign : Equiv.Perm (Fin 5) →* ℤˣ).comp R.subtype
  have hgR : permOf g ∈ R := MonoidHom.mem_range.2 ⟨g, rfl⟩
  have hsurj : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one f⟩
    · have hm1 : Equiv.Perm.sign (permOf g) = -1 := (Int.units_eq_one_or _).resolve_left hne
      exact ⟨⟨permOf g, hgR⟩, hm1⟩
  have hr : f.range = ⊤ := MonoidHom.range_eq_top.2 hsurj
  have hidx : f.ker.index = 2 := by
    rw [Subgroup.index_ker, hr, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have hR60 : Nat.card R = 60 := card_range_permHom
  have hK : Nat.card f.ker = 30 := by
    have h := Subgroup.index_mul_card (H := f.ker)
    rw [hidx, hR60] at h
    omega
  let K' : Subgroup (Equiv.Perm (Fin 5)) := f.ker.map R.subtype
  have hK'le : K' ≤ alternatingGroup (Fin 5) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [Equiv.Perm.mem_alternatingGroup]
    exact MonoidHom.mem_ker.1 hy
  have hK'card : Nat.card K' = 30 := by
    rw [← hK]
    exact Subgroup.card_map_of_injective Subtype.val_injective
  let M : Subgroup (alternatingGroup (Fin 5)) := K'.subgroupOf (alternatingGroup (Fin 5))
  have hMcard : Nat.card M = 30 := by
    rw [← hK'card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'le).toEquiv
  have hMi : M.index = 2 := by
    have h := Subgroup.index_mul_card (H := M)
    rw [hMcard, card_alt5] at h
    omega
  have := Subgroup.normal_of_index_eq_two hMi
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
  · have h1 : Nat.card M = 1 := by rw [h, Subgroup.card_bot]
    omega
  · have h1 : Nat.card M = 60 := by rw [h, Subgroup.card_top, card_alt5]
    omega

@[expose] noncomputable def thetaF :
    ↥P2 →* alternatingGroup (Fin 5) where
  toFun g := ⟨permOf g, Equiv.Perm.mem_alternatingGroup.2 (sign_permOf_eq_one g)⟩
  map_one' := Subtype.ext permOf_one
  map_mul' g h := Subtype.ext (permOf_mul g h)

theorem mem_ker_thetaF
    (g : ↥P2) : g ∈ thetaF.ker ↔ permOf g = 1 := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  exact Iff.rfl

theorem mem_ker_thetaF_iff
    (g : ↥P2) : g ∈ thetaF.ker ↔ (g : Y) ∈ Vsub :=
  (mem_ker_thetaF g).trans (permOf_eq_one_iff g)

theorem card_ker_thetaF :
    Nat.card thetaF.ker = 16 := by
  rw [← card_Vsub_eq]
  apply Nat.card_congr
  exact
    { toFun := fun g => ⟨(g.1 : Y), (mem_ker_thetaF_iff g.1).1 g.2⟩
      invFun := fun v => ⟨⟨v.1, Vsub_le_P2 v.2⟩, (mem_ker_thetaF_iff _).2 v.2⟩
      left_inv := fun g => Subtype.ext (Subtype.ext rfl)
      right_inv := fun v => Subtype.ext rfl }

theorem card_range_thetaF :
    Nat.card thetaF.range = 60 := by
  have h1 := Subgroup.index_mul_card (H := thetaF.ker)
  rw [card_P2, card_ker_thetaF, Subgroup.index_ker] at h1
  omega

theorem thetaF_surjective :
    Function.Surjective thetaF := by
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  rw [card_range_thetaF, card_alt5]

end CFSG.GH74.QTGen4.U42

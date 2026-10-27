module

public import CFSG.CharacterTheory.Wreathed.InvertedOddCyclingLiftSupport
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.Walter.Cited.FourGroupCentralizer
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueSetup

public section

open scoped Classical

namespace CFSG.Semidihedral.UnitaryDValue.GW

open CFSG.Semidihedral.UnitaryDValue CFSG.Semidihedral.UnitaryDValue.DValueData

theorem eq_one_or_eq_of_mem_zpowers {M : Type*} [Group M] {a g : M} (ha : orderOf a = 2)
    (hg : g ∈ Subgroup.zpowers a) : g = 1 ∨ g = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, ha]
  have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases this with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem sylowU_hyp {w : G} (hw : w ∈ D.W) (hw1 : w ≠ 1) (htw : D.t * w = w * D.t) :
    ∀ g ∈ ({1, D.t⁻¹, D.t⁻¹ * D.t⁻¹} : Set G),
      D.N ⊓ Subgroup.centralizer {g * w * g⁻¹} ≤ D.C := by
  have htw' : Commute D.t⁻¹ w := Commute.inv_left htw
  have hconj : ∀ g ∈ ({1, D.t⁻¹, D.t⁻¹ * D.t⁻¹} : Set G), g * w * g⁻¹ = w := by
    intro g hg
    apply conj_eq_of_comm
    rcases hg with rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact htw'.eq
    · exact (htw'.mul_left htw').eq
  intro g hg c hc
  obtain ⟨hcx, hcw⟩ := Subgroup.mem_inf.mp hc
  rw [hconj g hg] at hcw
  exact Subgroup.mem_inf.mpr ⟨hcx, D.W_centralizer w hw hw1 (Subgroup.mem_inf.mpr ⟨hcx, hcw⟩)⟩

theorem mem_C_of_commute_T {w : G}
    (hw : ∀ g ∈ ({1, D.t⁻¹, D.t⁻¹ * D.t⁻¹} : Set G),
      D.N ⊓ Subgroup.centralizer {g * w * g⁻¹} ≤ D.C)
    {c v : G} (hcw : c ∈ Subgroup.centralizer {w}) (hv : v ∈ D.T) (hv1 : v ≠ 1)
    (hcv : c * v = v * c) : c ∈ D.C := by
  have key : ∀ g ∈ ({1, D.t⁻¹, D.t⁻¹ * D.t⁻¹} : Set G),
      g ∈ Subgroup.normalizer (D.T : Set G) → g * v * g⁻¹ = D.x → c ∈ D.C := by
    intro g hg hgT hgv
    have h1 : g * c * g⁻¹ ∈ D.N := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hgv]
      calc g * c * g⁻¹ * (g * v * g⁻¹) = g * (c * v) * g⁻¹ := by group
        _ = g * (v * c) * g⁻¹ := by rw [hcv]
        _ = g * v * g⁻¹ * (g * c * g⁻¹) := by group
    have h2 : g * c * g⁻¹ ∈ Subgroup.centralizer {g * w * g⁻¹} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hcw ⊢
      calc g * c * g⁻¹ * (g * w * g⁻¹) = g * (c * w) * g⁻¹ := by group
        _ = g * (w * c) * g⁻¹ := by rw [hcw]
        _ = g * w * g⁻¹ * (g * c * g⁻¹) := by group
    have h3 : g * c * g⁻¹ ∈ D.C := hw g hg ⟨h1, h2⟩
    have h4 := D.conj_mem_C (Subgroup.inv_mem _ hgT) h3
    convert h4 using 1
    group
  have htN := D.t_mem_normalizer_T
  rcases D.mem_T_iff.mp hv with rfl | rfl | rfl | rfl
  · exact absurd rfl hv1
  · exact key 1 (by simp) (Subgroup.one_mem _) (by group)
  · exact key D.t⁻¹ (by simp) (Subgroup.inv_mem _ htN) (by rw [inv_inv]; exact D.t_inv_z)
  · refine key (D.t⁻¹ * D.t⁻¹) (by simp)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ htN) (Subgroup.inv_mem _ htN)) ?_
    rw [conj_mul_eq, inv_inv, D.t_inv_xz, D.t_inv_z]

theorem mem_normalizer_T_of_mem_C {c : G} (hc : c ∈ D.C) :
    c ∈ Subgroup.normalizer (D.T : Set G) := by
  obtain ⟨hx, hz⟩ := D.mem_C_iff_conj.mp hc
  exact D.mem_normalizer_T_of (by rw [hx]; exact D.x_mem_T) (by rw [hz]; exact D.z_mem_T)

theorem x_mem_centralizer {w : G} (hwC : w ∈ D.C) : D.x ∈ Subgroup.centralizer {w} :=
  Subgroup.mem_centralizer_singleton_iff.mpr (D.mem_C_iff.mp hwC).1.symm

theorem z_mem_centralizer {w : G} (hwC : w ∈ D.C) : D.z ∈ Subgroup.centralizer {w} :=
  Subgroup.mem_centralizer_singleton_iff.mpr (D.mem_C_iff.mp hwC).2.symm

theorem isKleinFour_closure {w : G} (hwC : w ∈ D.C) :
    IsKleinFour (Subgroup.closure ({⟨D.x, x_mem_centralizer D hwC⟩,
      ⟨D.z, z_mem_centralizer D hwC⟩} : Set (Subgroup.centralizer ({w} : Set G)))) := by
  have hxo : orderOf (⟨D.x, x_mem_centralizer D hwC⟩ : Subgroup.centralizer ({w} : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact D.x_order
  have hzo : orderOf (⟨D.z, z_mem_centralizer D hwC⟩ : Subgroup.centralizer ({w} : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact D.z_order
  refine CFSG.Wreathed.isKleinFour_closure_pair hxo hzo (Subtype.ext D.z_comm) ?_
  rw [Subgroup.disjoint_def]
  intro g hg1 hg2
  rcases eq_one_or_eq_of_mem_zpowers hxo hg1 with h | h
  · exact h
  · rcases eq_one_or_eq_of_mem_zpowers hzo hg2 with h' | h'
    · exact h'
    · exact absurd (congrArg Subtype.val (h'.symm.trans h)) D.z_ne

theorem oddCore_le_C {w : G} (hw : w ∈ D.W) (hw1 : w ≠ 1) (htw : D.t * w = w * D.t) :
    ∀ o ∈ CFSG.oddCore (Subgroup.centralizer ({w} : Set G)), (o : G) ∈ D.C := by
  have hwC : w ∈ D.C := D.W_le hw
  have hyp := sylowU_hyp D hw hw1 htw
  set K := Subgroup.centralizer ({w} : Set G) with hK
  set x' : K := ⟨D.x, x_mem_centralizer D hwC⟩ with hx'
  set z' : K := ⟨D.z, z_mem_centralizer D hwC⟩ with hz'
  have hclT : ∀ s ∈ Subgroup.closure ({x', z'} : Set K), (s : G) ∈ D.T := by
    intro s hs
    have hle : Subgroup.closure ({x', z'} : Set K) ≤ D.T.comap K.subtype := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact D.x_mem_T
      · exact D.z_mem_T
    exact hle hs
  have hab : ∀ s ∈ Subgroup.closure ({x', z'} : Set K), s ≠ 1 →
      IsMulCommutative (Subgroup.centralizer ({s} : Set K)) := by
    intro s hs hs1
    have hsT := hclT s hs
    have hs1' : (s : G) ≠ 1 := fun h => hs1 (Subtype.ext h)
    have hmem : ∀ c : Subgroup.centralizer ({s} : Set K), ((c : K) : G) ∈ D.C := by
      intro c
      have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
      exact mem_C_of_commute_T D hyp (c : K).2 hsT hs1' (congrArg Subtype.val hc)
    exact ⟨⟨fun a b => Subtype.ext (Subtype.ext (D.C_comm _ (hmem a) _ (hmem b)))⟩⟩
  have hTO := CFSG.Walter.Suzuki.le_centralizer_of_isKleinFour (N := CFSG.oddCore K)
    (isKleinFour_closure D hwC) CFSG.ABGLocalTools.odd_card_oddCore hab
  intro o ho
  have h1 := Subgroup.mem_centralizer_iff.mp
    (hTO (Subgroup.subset_closure (Set.mem_insert _ _))) o ho
  have h2 := Subgroup.mem_centralizer_iff.mp
    (hTO (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))) o ho
  exact D.mem_C_iff.mpr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩

theorem centralizer_le_normalizer_T_of_normal {w : G} (hw : w ∈ D.W) (hw1 : w ≠ 1)
    (htw : D.t * w = w * D.t)
    (hM : (CFSG.oddCore (Subgroup.centralizer ({w} : Set G)) ⊔
      (D.sylowU (D.W_le hw) (sylowU_hyp D hw hw1 htw) :
        Subgroup (Subgroup.centralizer ({w} : Set G)))).Normal) :
    Subgroup.centralizer {w} ≤ Subgroup.normalizer (D.T : Set G) := by
  have hwC : w ∈ D.C := D.W_le hw
  have hyp := sylowU_hyp D hw hw1 htw
  set K := Subgroup.centralizer ({w} : Set G) with hK
  have hUK : D.U ≤ K := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (D.C_comm u hu.1 w hwC)
  set P : Sylow 2 K := D.sylowU hwC hyp with hP
  have hOC := oddCore_le_C D hw hw1 htw
  have := hM
  have hfr := Sylow.normalizer_sup_eq_top' (N := CFSG.oddCore K ⊔ (P : Subgroup K)) P
    le_sup_right
  intro g hg
  have hk : (⟨g, hg⟩ : K) ∈ (⊤ : Subgroup K) := Subgroup.mem_top _
  rw [← hfr] at hk
  obtain ⟨a, ha, b, hb, hab'⟩ := Subgroup.mem_sup_of_normal_right.mp hk
  obtain ⟨o, ho, u, hu, hou⟩ := Subgroup.mem_sup_of_normal_left.mp hb
  have hg' : g = (a : G) * ((o : G) * (u : G)) := by
    have h := congrArg Subtype.val hab'
    rw [← hou] at h
    exact h.symm
  rw [hg']
  refine Subgroup.mul_mem _ ?_ (Subgroup.mul_mem _ ?_ ?_)
  · apply D.normalizer_U_le
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have ha' : a ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) := ha
    rw [Subgroup.mem_normalizer_iff] at ha'
    constructor
    · intro hv
      exact (ha' ⟨v, hUK hv⟩).mp hv
    · intro hv
      have hvK : v ∈ K := by
        have : v = (a : G)⁻¹ * ((a : G) * v * (a : G)⁻¹) * a := by group
        rw [this]
        exact K.mul_mem (K.mul_mem (K.inv_mem a.2) (hUK hv)) a.2
      exact (ha' ⟨v, hvK⟩).mpr hv
  · exact mem_normalizer_T_of_mem_C D (hOC o ho)
  · exact mem_normalizer_T_of_mem_C D (Subgroup.mem_subgroupOf.mp hu).1

end CFSG.Semidihedral.UnitaryDValue.GW

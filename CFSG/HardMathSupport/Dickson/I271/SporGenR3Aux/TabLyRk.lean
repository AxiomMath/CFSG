module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyA
public import CFSG.Sporadic.Recognition.LyonsAS44Delta
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInner
public import Certificates.Certificate6109

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Yardstones.Md0ec50421ce4
  CFSG.Sporadic.Recognition.LyonsSims CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Subgroup Equiv

section Rk

variable {G : Type} [Group G] [Finite G] {t : G} {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

@[expose] def tabLyX₁ (x₁ : ↥(centralizer ({t} : Set G))) : ↥(centralizer ({(x₁ : G)} : Set G)) :=
  ⟨(x₁ : G), self_mem_centralizer_singleton _⟩

@[expose] def tabLyA3 (x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))) :
    Subgroup ↥(centralizer ({(x₁ : G)} : Set G)) :=
  (Subgroup.closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G)).subgroupOf
    (centralizer ({(x₁ : G)} : Set G))

theorem tabLy_closure_le (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Subgroup.closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G) ≤
      centralizer ({(x₁ : G)} : Set G) := by
  rw [Subgroup.closure_le]
  rintro y (rfl | rfl | rfl)
  · exact self_mem_centralizer_singleton _
  · exact mem_centralizer_singleton_iff.2 (D.comm₂₁ S)
  · exact mem_centralizer_singleton_iff.2 (D.comm₃₁ S)

theorem tabLy_closure_comm (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {a b : G}
    (ha : a ∈ Subgroup.closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G))
    (hb : b ∈ Subgroup.closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G)) : a * b = b * a := by
  have hpw : ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G).Pairwise Commute := by
    have h12 : Commute (x₁ : G) (x₂ : G) := (D.comm₂₁ S).symm
    have h13 : Commute (x₁ : G) (x₃ : G) := (D.comm₃₁ S).symm
    have h23 : Commute (x₂ : G) (x₃ : G) := (D.comm₃₂ S).symm
    rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl) _
    all_goals first
      | exact Commute.refl _
      | exact h12 | exact h13 | exact h23 | exact h12.symm | exact h13.symm | exact h23.symm
  have h := (Subgroup.isMulCommutative_closure hpw).is_comm.comm
    (⟨a, ha⟩ : ↥(Subgroup.closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G))) ⟨b, hb⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_mk] using congrArg Subtype.val h

theorem tabLyA3_facts (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    IsElemAbelian 3 (tabLyA3 x₁ x₂ x₃) ∧ Nat.card ↥(tabLyA3 x₁ x₂ x₃) = 27 := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact tabLy_closure_comm D S (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2)
  · obtain ⟨i, j, k, hijk⟩ := D.exists_zpow_of_mem_closure_three S (Subgroup.mem_subgroupOf.1 ha)
    apply Subtype.ext
    have h := congrArg Subtype.val (D.pow_three_torus S i j k)
    simp only [SubgroupClass.coe_pow, Subgroup.coe_mul, SubgroupClass.coe_zpow,
      OneMemClass.coe_one] at h
    rw [SubgroupClass.coe_pow, hijk, OneMemClass.coe_one]
    exact h
  · unfold tabLyA3
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (tabLy_closure_le D S)).toEquiv]
    exact D.card_closure_three S

theorem tabLyA3_comm (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    {a b : ↥(centralizer ({(x₁ : G)} : Set G))}
    (ha : a ∈ tabLyA3 x₁ x₂ x₃) (hb : b ∈ tabLyA3 x₁ x₂ x₃) : a * b = b * a :=
  Subtype.ext (tabLy_closure_comm D S (Subgroup.mem_subgroupOf.1 ha) (Subgroup.mem_subgroupOf.1 hb))


theorem tabLy_eq_conj (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hO : Nat.Coprime 3 (Nat.card (Outer (↥(centralizer ({(x₁ : G)} : Set G)) ⧸
      Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G))))))
    {β : MulAut ↥(centralizer ({(x₁ : G)} : Set G))} (hβ : β ^ 3 = 1) :
    ∃ g : ↥(centralizer ({(x₁ : G)} : Set G)), β = MulAut.conj g := by
  have hq := tabLy_quasisimple D S
  have hβ' : centerDescend ↥(centralizer ({(x₁ : G)} : Set G)) β ^ 3 = 1 := by
    rw [← map_pow, hβ, map_one]
  obtain ⟨gq, hgq⟩ := mem_innerAut_of_pow_eq_one' hO hβ'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gq
  refine ⟨g, ?_⟩
  have h1 : centerDescend ↥(centralizer ({(x₁ : G)} : Set G)) (β * (MulAut.conj g)⁻¹) = 1 := by
    rw [map_mul, map_inv, CFSG.HardMathSupport.Solomon.Coordinator.centerDescend_conj, ← hgq,
      mul_inv_cancel]
  exact mul_inv_eq_one.1 (eq_one_of_centerDescend_eq_one hq h1)


theorem tabLy_conj_A3 (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    {g : ↥(centralizer ({(x₁ : G)} : Set G))} (hg : orderOf (projQ (x₁ : G) g) = 3) :
    ∃ m a : ↥(centralizer ({(x₁ : G)} : Set G)), a ∈ tabLyA3 x₁ x₂ x₃ ∧ g = m * a * m⁻¹ := by
  obtain ⟨R, T, A, Y, F⟩ := D.exists_lyAFacts Certificates.certificate6109 S
  have hx₁mem : ∀ k : ℤ, (x₁ : G) ^ k ∈ Subgroup.closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G) :=
    fun k => Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) k
  have hx₂mem : (x₂ : G) ∈ Subgroup.closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hx₃mem : (x₃ : G) ∈ Subgroup.closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G) :=
    Subgroup.subset_closure (by simp)
  rcases F.classes _ hg with h | h
  · have h' : IsConj (projQ (x₁ : G) (D.x₂M S)) (projQ (x₁ : G) g) := h.symm
    obtain ⟨m, k, hmk⟩ := LyData.exists_lift_conj h'
    refine ⟨m, D.x₂M S * tabLyX₁ x₁ ^ k, ?_, Subtype.ext ?_⟩
    · rw [tabLyA3, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      exact Subgroup.mul_mem _ hx₂mem (hx₁mem k)
    · rw [hmk]
      simp [tabLyX₁, LyData.x₂M]
  · have h' : IsConj (projQ (x₁ : G) (D.x₂M S * D.x₃M S)) (projQ (x₁ : G) g) := by
      rw [map_mul]
      exact h.symm
    obtain ⟨m, k, hmk⟩ := LyData.exists_lift_conj h'
    refine ⟨m, D.x₂M S * D.x₃M S * tabLyX₁ x₁ ^ k, ?_, Subtype.ext ?_⟩
    · rw [tabLyA3, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx₂mem hx₃mem) (hx₁mem k)
    · rw [hmk]
      simp [tabLyX₁, LyData.x₂M, LyData.x₃M]

theorem tabLy_rkAut (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hO : Nat.Coprime 3 (Nat.card (Outer (↥(centralizer ({(x₁ : G)} : Set G)) ⧸
      Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G)))))) :
    RkAut 3 ↥(centralizer ({(x₁ : G)} : Set G)) := by
  intro β hβ
  obtain ⟨g, rfl⟩ := tabLy_eq_conj D S hO hβ
  have hZ : Nat.card ↥(Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G))) = 3 :=
    D.card_center_centralizer S
  obtain ⟨hEl, hcard⟩ := tabLyA3_facts D S
  by_cases hg1 : projQ (x₁ : G) g = 1
  ·
    have hgZ : g ∈ Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G)) := by
      have hk : g ∈ (projQ (x₁ : G)).ker := hg1
      rw [ker_projQ] at hk
      exact LyData.zpowers_le_center_centralizer _ hk
    refine ⟨tabLyA3 x₁ x₂ x₃, hEl, by rw [hZ, hcard]; norm_num, fun e _ => ?_⟩
    rw [MulAut.conj_apply, (Subgroup.mem_center_iff.1 hgZ e).symm, mul_inv_cancel_right]
  · have h3 : projQ (x₁ : G) g ^ 3 = 1 := by
      have hc : MulAut.conj (g ^ 3) = 1 := by rw [map_pow]; exact hβ
      have hgZ : g ^ 3 ∈ Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G)) := by
        rw [Subgroup.mem_center_iff]
        intro h
        have := congrArg (fun φ : MulAut ↥(centralizer ({(x₁ : G)} : Set G)) => φ h) hc
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc h * g ^ 3 = (g ^ 3 * h * (g ^ 3)⁻¹) * g ^ 3 := by rw [this]
          _ = g ^ 3 * h := by group
      rw [D.center_centralizer S] at hgZ
      rw [← map_pow]
      have hk : g ^ 3 ∈ (projQ (x₁ : G)).ker := by rw [ker_projQ]; exact hgZ
      exact hk
    have hord : orderOf (projQ (x₁ : G) g) = 3 := orderOf_eq_prime h3 hg1
    obtain ⟨m, a, ha, rfl⟩ := tabLy_conj_A3 D S hord
    refine ⟨(tabLyA3 x₁ x₂ x₃).map (MulAut.conj m).toMonoidHom, hEl.map _, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj m).injective, hZ, hcard]
      norm_num
    · rintro _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hab := tabLyA3_comm D S ha hb
      calc m * a * m⁻¹ * (m * b * m⁻¹) * (m * a * m⁻¹)⁻¹ = m * (a * b) * a⁻¹ * m⁻¹ := by group
        _ = m * (b * a) * a⁻¹ * m⁻¹ := by rw [hab]
        _ = m * b * m⁻¹ := by group

end Rk

end CFSG.HardMathSupport.Dickson.I271

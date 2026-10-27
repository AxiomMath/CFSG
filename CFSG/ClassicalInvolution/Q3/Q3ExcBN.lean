module

public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootQuasisimple
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped Pointwise commutatorElement

section BN

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem exc3_mem_orbitTorus_of_mem_normalCore :
    ∀ y : D.orbitGroup, y ∈ (D.orbitBorel.subgroupOf D.orbitGroup).normalCore →
      (y : ModGL τ k) ∈ D.orbitTorus := by
  set C := D.orbitGroup
  set R := (D.orbitBorel.subgroupOf C).normalCore
  obtain ⟨w₀, hw₀, himg⟩ := D.exists_longest
  obtain ⟨x₀, hx₀, -⟩ := D.exists_fixed_lift hw₀
  obtain ⟨hn₀C, hn₀N, hn₀w⟩ := D.isCLift_of_isOrbitLift hx₀
  set n₀ : ModGL τ k := (x₀ : ModGL τ k) with hn₀def
  have hmaps : MapsRootLines n₀ w₀ := by
    have := mapsRootLines_weylQuotientHom (⟨n₀, hn₀N⟩ : monomialSubgroup τ k)
    rwa [hn₀w] at this
  have hnegroot : ∀ α ∈ negRoots D.roots, IsRoot τ α ∧ height α < 0 := fun α hα => by
    have hαΨ : α ∈ D.roots := by
      have := neg_mem_unionRoots hα.1
      rwa [neg_neg] at this
    exact ⟨isRoot_of_mem_unionRoots hαΨ, (mem_negRoots_iff_height_neg hαΨ).1 hα⟩
  have hconjU : ∀ u ∈ D.unipotentJ, n₀ * u * n₀⁻¹ ∈ negUnipotent τ k := fun u hu => by
    have h := conj_mem_rootSpan_of_mapsRootLines hn₀N hmaps (S := D.posRootsJ)
      (fun α hα => isRoot_of_mem_unionRoots hα.1) hu
    rw [himg] at h
    exact rootSpan_le_negUnipotent hnegroot h
  have hRT : ∀ x ∈ R, (x : ModGL τ k) ∈ D.orbitTorus := by
    intro x hx
    have hxB : (x : ModGL τ k) ∈ D.orbitBorel :=
      Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hx)
    have hx' : n₀⁻¹ * (x : ModGL τ k) * n₀ ∈ unionBorel k D.χ D.J := by
      have h := hx (⟨n₀, hn₀C⟩ : C)⁻¹
      rw [Subgroup.mem_subgroupOf] at h
      exact D.orbitBorel_le_unionBorel (by simpa using h)
    have hxopp : (x : ModGL τ k) ∈ torusGroup τ k ⊔ negUnipotent τ k := by
      obtain ⟨t, ht, u, hu, htu⟩ := D.exists_torus_mul_unipotent hx'
      have e : (x : ModGL τ k) = (n₀ * t * n₀⁻¹) * (n₀ * u * n₀⁻¹) := by
        calc (x : ModGL τ k) = n₀ * (n₀⁻¹ * (x : ModGL τ k) * n₀) * n₀⁻¹ := by group
          _ = _ := by rw [← htu]; group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1
        (mem_normalizer_torusGroup_of_mem_monomialSubgroup hn₀N) _).1
          (unionTorus_le_torusGroup ht)))
        (Subgroup.mem_sup_right (hconjU _ hu))
    obtain ⟨w₁, hw₁, -⟩ := weyl_longest_element τ
    have hH : (x : ModGL τ k) ∈ torusGroup τ k := by
      rw [← (opposite_Borel_intersection τ k w₁ hw₁).2.2.1]
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxB).2, hxopp⟩
    exact Subgroup.mem_inf.2 ⟨x.2, hH⟩
  exact hRT

theorem exc3_sup_orbitBorel_eq_top_of_not_le {M : Subgroup D.orbitGroup} (hM : M.Normal)
    (hMB : ¬ M ≤ D.orbitBorel.subgroupOf D.orbitGroup) :
    M ⊔ D.orbitBorel.subgroupOf D.orbitGroup = ⊤ := by
  set B := D.orbitBorel with hB
  set M₀ := M.map D.orbitGroup.subtype with hM₀
  have hM₀C : M₀ ≤ D.orbitGroup := by
    rintro _ ⟨m, -, rfl⟩
    exact m.2
  have hconj : ∀ s ∈ D.orbitGroup, ∀ m ∈ M₀, s * m * s⁻¹ ∈ M₀ := by
    rintro s hs _ ⟨m, hm, rfl⟩
    exact ⟨⟨s, hs⟩ * m * ⟨s, hs⟩⁻¹, hM.conj_mem m hm ⟨s, hs⟩, rfl⟩
  obtain ⟨m, hmM, hmB⟩ : ∃ m ∈ M₀, m ∉ B := by
    by_contra! h
    apply hMB
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact h _ ⟨x, hx, rfl⟩
  set E := M₀ ⊔ B with hE
  have hBE : B ≤ E := le_sup_right
  have hME : M₀ ≤ E := le_sup_left
  have hBnorm : B ≤ Subgroup.normalizer (M₀ : Set (ModGL τ k)) :=
    fun b hb => Subgroup.mem_normalizer_iff.2 fun y =>
      ⟨fun hy => hconj b (D.orbitBorel_le_orbitGroup hb) y hy, fun hy => by
        have h := hconj b⁻¹ (inv_mem (D.orbitBorel_le_orbitGroup hb)) _ hy
        rwa [show b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y by group] at h⟩
  have hEset : (E : Set (ModGL τ k)) = (M₀ : Set (ModGL τ k)) * (B : Set (ModGL τ k)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBnorm
  have hlift : ∀ w ∈ D.fixedWeyl, ∃ x : adjointGroup τ k,
      D.IsOrbitLift (x : ModGL τ k) w ∧ D.F x = x := fun w hw => D.exists_fixed_lift hw
  choose! xw hxw hxwF using hlift
  have hmU : m ∈ ⋃ w ∈ D.fixedWeyl, D.fixedCell (xw w) := by
    rw [← D.coe_orbitGroup_eq_iUnion (nw := xw) fun w hw => ⟨hxw w hw, hxwF w hw⟩]
    exact hM₀C hmM
  obtain ⟨w, hw, hmw⟩ := Set.mem_iUnion₂.1 hmU
  obtain ⟨b, hb, b', hb', hbgb⟩ := D.mem_fixedCell.1 hmw
  have hxE : ((xw w : adjointGroup τ k) : ModGL τ k) ∈ E := by
    have e : ((xw w : adjointGroup τ k) : ModGL τ k) = b⁻¹ * m * b'⁻¹ := by
      rw [← hbgb]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hBE hb)) (hME hmM)) (inv_mem (hBE hb'))
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hmB
    have h1 : D.IsOrbitLift 1 1 := ⟨[], fun _ h => absurd h List.not_mem_nil, rfl, rfl⟩
    have hT := D.inv_mul_mem_orbitTorus h1 (hxw 1 hw)
    rw [inv_one, one_mul] at hT
    rw [← hbgb]
    exact mul_mem (mul_mem hb (D.orbitTorus_le_orbitBorel hT)) hb'
  obtain ⟨O₀, hO₀, hneg₀⟩ :=
    D.exists_orbits_image_subset_negRoots (inv_mem hw) (inv_ne_one.2 hw1)
  have hO₀E := D.orbitN_mem_of_lift_mem hBE (hxw w hw) (hxwF w hw) hxE hO₀ hneg₀
  have hall : ∀ O ∈ D.orbits, D.orbitN O ∈ E := by
    by_contra! hnot
    obtain ⟨P₀, hP₀, hP₀E⟩ := hnot
    obtain ⟨O, P, ⟨hO, hP, hOP, hadj⟩, hOE, hPE⟩ :=
      exists_edge_of_reflTransGen (P := fun X => D.orbitN X ∈ E)
        (D.orbits_connected hO₀ hP₀) hO₀E hP₀E
    apply hPE
    have hOE' : D.orbitN O ∈ (M₀ : Set (ModGL τ k)) * (B : Set (ModGL τ k)) := by
      rw [← hEset]
      exact hOE
    obtain ⟨m₁, hm₁, b₁, hb₁, hmb⟩ := hOE'
    have hrO := D.setReflection_mem_fixedWeyl hO
    have hrP := D.setReflection_mem_fixedWeyl hP
    have hNOC := D.orbitMap_mem_orbitGroup hO WSL
    have hNPC := D.orbitMap_mem_orbitGroup hP WSL
    have hlO := D.isOrbitLift_orbitN hO
    have hlP := D.isOrbitLift_orbitN hP
    have l1 := D.foldedLength_setReflection hO
    have l2 := D.foldedLength_setReflection_mul_setReflection hO hP hOP
    have l2' := D.foldedLength_setReflection_mul_setReflection hP hO hOP.symm
    have l3 := D.foldedLength_braid hO hP hOP hadj
    have hm₁cell : m₁⁻¹ ∈ D.fixedCell (D.orbitN O) := by
      have hsq : D.orbitN O * D.orbitN O ∈ B :=
        D.orbitTorus_le_orbitBorel ⟨mul_mem hNOC hNOC, D.orbitN_mul_self_mem_torusGroup hO⟩
      refine D.mem_fixedCell.2 ⟨b₁, hb₁, (D.orbitN O * D.orbitN O)⁻¹, inv_mem hsq, ?_⟩
      have e : m₁ = D.orbitN O * b₁⁻¹ := by
        rw [← hmb]
        group
      rw [e]
      group
    have h1 : D.orbitN P * m₁⁻¹ ∈ D.fixedCell (D.orbitN P * D.orbitN O) := by
      rw [← (D.fixedCell_orbitN_mul_fixedCell hP hrO hlO).1 (by rw [l2, l1])]
      exact Set.mul_mem_mul (D.self_mem_fixedCell _) hm₁cell
    have h2 : m₁ * (D.orbitN P)⁻¹ ∈ D.fixedCell (D.orbitN O * D.orbitN P) := by
      have h := D.inv_mem_fixedCell h1
      have e1 : (D.orbitN P * m₁⁻¹)⁻¹ = m₁ * (D.orbitN P)⁻¹ := by group
      rw [e1] at h
      rwa [D.fixedCell_eq_of_isCLift
        (D.isCLift_inv (D.isCLift_mul (D.isCLift_of_isOrbitLift hlP)
          (D.isCLift_of_isOrbitLift hlO)))
        (by
          have h' := D.isCLift_mul (D.isCLift_of_isOrbitLift hlO) (D.isCLift_of_isOrbitLift hlP)
          rwa [show setReflection O * setReflection P =
            (setReflection P * setReflection O)⁻¹ by
              rw [mul_inv_rev, D.setReflection_inv hO, D.setReflection_inv hP]] at h')] at h
    have hlOP := D.isOrbitLift_orbitN_mul hO hlP
    have h3 : D.orbitN P * m₁ * (D.orbitN P)⁻¹ ∈
        D.fixedCell (D.orbitN P * (D.orbitN O * D.orbitN P)) := by
      rw [← (D.fixedCell_orbitN_mul_fixedCell hP (mul_mem hrO hrP) hlOP).1
        (by rw [← mul_assoc, l3, l2']), mul_assoc]
      exact Set.mul_mem_mul (D.self_mem_fixedCell _) h2
    have hl3 := D.isOrbitLift_orbitN_mul hP hlOP
    obtain ⟨-, -, x₃, hx₃, hx₃F⟩ := D.isOrbitLift_spec hl3
    obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ := D.mem_fixedCell.1 h3
    have hx₃E : ((x₃ : adjointGroup τ k) : ModGL τ k) ∈ E := by
      rw [hx₃]
      have e : D.orbitN P * (D.orbitN O * D.orbitN P) =
          c₁⁻¹ * (D.orbitN P * m₁ * (D.orbitN P)⁻¹) * c₂⁻¹ := by
        rw [← hc]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hBE hc₁)) (hME (hconj _ hNPC m₁ hm₁)))
        (inv_mem (hBE hc₂))
    have hw' := mul_mem hrP (mul_mem hrO hrP)
    have hdesc : (fun γ => (setReflection P * (setReflection O * setReflection P))⁻¹ • γ) '' P ⊆
        negRoots D.roots := by
      refine (D.foldedLength_setReflection_mul hP hw').1.1 ?_
      rw [← mul_assoc (setReflection P) (setReflection P), D.setReflection_mul_self hP, one_mul,
        ← mul_assoc, l3, l2']
    exact D.orbitN_mem_of_lift_mem hBE (hx₃ ▸ hl3) hx₃F hx₃E hP hdesc
  have hCE : D.orbitGroup ≤ E := by
    rw [D.orbitGroup_eq_closure, Subgroup.closure_le]
    rintro _ (hb | ⟨O, hO, rfl⟩)
    · exact hBE hb
    · exact hall O hO
  rw [eq_top_iff]
  intro s _
  have hs : (s : ModGL τ k) ∈ (M₀ : Set (ModGL τ k)) * (B : Set (ModGL τ k)) := by
    rw [← hEset]
    exact hCE s.2
  obtain ⟨m', hm', b₀, hb₀, hmb⟩ := hs
  obtain ⟨m'', hm'', rfl⟩ := hm'
  simp only [Subgroup.coe_subtype] at hmb
  have hb₀C : b₀ ∈ D.orbitGroup := by
    have e : b₀ = (m'' : ModGL τ k)⁻¹ * s := by
      rw [← hmb]
      group
    rw [e]
    exact mul_mem (inv_mem m''.2) s.2
  have hs' : s = m'' * ⟨b₀, hb₀C⟩ := Subtype.ext hmb.symm
  rw [hs']
  exact mul_mem (Subgroup.mem_sup_left hm'')
    (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hb₀))

omit [Fact p₀.Prime] in
theorem exc3_commutator_mul_central {G : Type*} [Group G] {m₁ m₂ : G}
    (h₁ : m₁ ∈ Subgroup.center G) (h₂ : m₂ ∈ Subgroup.center G) (b₁ b₂ : G) :
    ⁅m₁ * b₁, m₂ * b₂⁆ = ⁅b₁, b₂⁆ := by
  have c1 : ∀ x : G, m₁ * x = x * m₁ := fun x => (Subgroup.mem_center_iff.mp h₁ x).symm
  have c2 : ∀ x : G, m₂ * x = x * m₂ := fun x => (Subgroup.mem_center_iff.mp h₂ x).symm
  have c1' : ∀ x : G, m₁⁻¹ * x = x * m₁⁻¹ := fun x =>
    (Subgroup.mem_center_iff.mp (inv_mem h₁) x).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc m₁ * b₁ * (m₂ * b₂) * (m₁ * b₁)⁻¹ * (m₂ * b₂)⁻¹
      = m₁ * (b₁ * m₂ * b₂ * b₁⁻¹ * m₁⁻¹ * b₂⁻¹) * m₂⁻¹ := by group
    _ = m₁ * (m₂ * (b₁ * b₂ * b₁⁻¹ * m₁⁻¹ * b₂⁻¹)) * m₂⁻¹ := by
        rw [show b₁ * m₂ * b₂ * b₁⁻¹ * m₁⁻¹ * b₂⁻¹ = m₂ * (b₁ * b₂ * b₁⁻¹ * m₁⁻¹ * b₂⁻¹) by
          rw [← c2 b₁]; group]
    _ = m₁ * (b₁ * b₂ * b₁⁻¹ * m₁⁻¹ * b₂⁻¹) := by
        rw [c2 (b₁ * b₂ * b₁⁻¹ * m₁⁻¹ * b₂⁻¹)]
        group
    _ = b₁ * b₂ * b₁⁻¹ * b₂⁻¹ := by
        rw [show b₁ * b₂ * b₁⁻¹ * m₁⁻¹ * b₂⁻¹ = m₁⁻¹ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) by
          rw [← c1' (b₁ * b₂ * b₁⁻¹)]; group]
        group

theorem exc3_center_orbitGroup_le_torus (hperf : Group.IsPerfect D.orbitGroup) :
    ∀ z ∈ D.orbitGroup, (∀ g ∈ D.orbitGroup, g * z = z * g) → z ∈ torusGroup τ k := by
  intro z hz hzc
  have hZB : Subgroup.center D.orbitGroup ≤ D.orbitBorel.subgroupOf D.orbitGroup := by
    by_contra hnot
    have htop := exc3_sup_orbitBorel_eq_top_of_not_le D
      (M := Subgroup.center D.orbitGroup) inferInstance hnot
    have hmul : (⊤ : Subgroup D.orbitGroup) =
        (Subgroup.center D.orbitGroup : Set D.orbitGroup) *
          (D.orbitBorel.subgroupOf D.orbitGroup : Set D.orbitGroup) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ Subgroup.le_normalizer_of_normal,
        htop]
    have hcomm : commutator D.orbitGroup ≤ D.orbitBorel.subgroupOf D.orbitGroup := by
      rw [commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      have ha : a ∈ (Subgroup.center D.orbitGroup : Set D.orbitGroup) *
          (D.orbitBorel.subgroupOf D.orbitGroup : Set D.orbitGroup) := by
        rw [← hmul]; trivial
      have hb : b ∈ (Subgroup.center D.orbitGroup : Set D.orbitGroup) *
          (D.orbitBorel.subgroupOf D.orbitGroup : Set D.orbitGroup) := by
        rw [← hmul]; trivial
      obtain ⟨m₁, hm₁, b₁, hb₁, rfl⟩ := ha
      obtain ⟨m₂, hm₂, b₂, hb₂, rfl⟩ := hb
      change ⁅m₁ * b₁, m₂ * b₂⁆ ∈ D.orbitBorel.subgroupOf D.orbitGroup
      rw [exc3_commutator_mul_central hm₁ hm₂, commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hb₁ hb₂) (inv_mem hb₁)) (inv_mem hb₂)
    have hall : D.orbitBorel.subgroupOf D.orbitGroup = ⊤ := by
      rw [Group.isPerfect_def.1 hperf] at hcomm
      exact top_le_iff.mp hcomm
    exact hnot (hall ▸ le_top)
  have hcore : Subgroup.center D.orbitGroup ≤ (D.orbitBorel.subgroupOf D.orbitGroup).normalCore :=
    Subgroup.normal_le_normalCore.2 hZB
  have hzC : (⟨z, hz⟩ : D.orbitGroup) ∈ Subgroup.center D.orbitGroup := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using hzc g g.2)
  exact (exc3_mem_orbitTorus_of_mem_normalCore D ⟨z, hz⟩ (hcore hzC)).2

end BN

end CFSG.ClassicalInvolution.Q3

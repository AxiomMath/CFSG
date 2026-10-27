module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem y7a_sq_subgroup {M V : Subgroup G} (hVM : V ≤ M)
    (hVc : ∀ m ∈ M, ∀ v ∈ V, m * v = v * m) (hcomm : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ V) :
    ∃ K : Subgroup G, K ≤ M ∧ ∀ m, m ∈ K ↔ m ∈ M ∧ m ^ 2 ∈ V := by
  refine ⟨{ carrier := {m | m ∈ M ∧ m ^ 2 ∈ V}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, ?_, ?_⟩
  · rintro x y ⟨hxM, hxV⟩ ⟨hyM, hyV⟩
    refine ⟨M.mul_mem hxM hyM, ?_⟩
    have hxy : ⁅y, x⁆ ∈ V := hcomm y hyM x hxM
    have hc : x * ⁅y, x⁆ = ⁅y, x⁆ * x := hVc x hxM ⁅y, x⁆ hxy
    have h1 : y * x = ⁅y, x⁆ * (x * y) := by rw [commutatorElement_def]; group
    have h2 : (x * y) ^ 2 = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
      calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
        _ = x * (⁅y, x⁆ * (x * y)) * y := by rw [h1]
        _ = (x * ⁅y, x⁆) * (x * y) * y := by group
        _ = (⁅y, x⁆ * x) * (x * y) * y := by rw [hc]
        _ = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by simp only [pow_two]; group
    rw [h2]
    exact V.mul_mem hxy (V.mul_mem hxV hyV)
  · exact ⟨M.one_mem, by simp⟩
  · rintro x ⟨hxM, hxV⟩
    exact ⟨M.inv_mem hxM, by simpa [inv_pow] using V.inv_mem hxV⟩
  · intro m hm
    exact hm.1
  · intro m
    exact Iff.rfl

theorem y7a_secProp_of_sq {M V : Subgroup G} (hVM : V ≤ M)
    (hVn : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V) (hcomm : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ V)
    (hsq : ∀ m ∈ M, m ^ 2 ∈ V) :
    SecProp M V (fun Y _ _ _ => IsElemAbelian 2 (⊤ : Subgroup Y)) := by
  have hN : (V.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hVM).mpr (fun v m hv hm => hVn m hm v hv)
  haveI := hN
  have hQ : ∀ g h : (↥M ⧸ V.subgroupOf M), g * h = h * g := by
    intro g h
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf M) g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf M) h
    rw [← commutatorElement_eq_one_iff_mul_comm]
    rw [← map_commutatorElement (QuotientGroup.mk' (V.subgroupOf M)) x y]
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
    have hcoe : ((⁅x, y⁆ : ↥M) : G) = ⁅(x : G), (y : G)⁆ :=
      map_commutatorElement M.subtype x y
    rw [hcoe]
    exact hcomm (x : G) x.2 (y : G) y.2
  refine ⟨hN, IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    exact Subtype.ext (hQ a.1 b.1)
  · intro g _
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf M) g
    rw [← map_pow]
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
    simpa using hsq (m : G) m.2

theorem y7a_sq_of_secProp {M V : Subgroup G}
    (h : SecProp M V (fun Y _ _ _ => IsElemAbelian 2 (⊤ : Subgroup Y))) :
    ∀ m ∈ M, m ^ 2 ∈ V := by
  obtain ⟨hN, hEA⟩ := h
  haveI := hN
  intro m hm
  have hsq : (QuotientGroup.mk' (V.subgroupOf M) (⟨m, hm⟩ : ↥M)) ^ 2 = 1 :=
    hEA.2 (QuotientGroup.mk' (V.subgroupOf M) (⟨m, hm⟩ : ↥M)) (Subgroup.mem_top _)
  have hmem : (⟨m, hm⟩ : ↥M) ^ 2 ∈ V.subgroupOf M := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    change QuotientGroup.mk' (V.subgroupOf M) ((⟨m, hm⟩ : ↥M) ^ 2) = 1
    rw [map_pow]
    exact hsq
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

theorem y7a_comm_le_of_gen {C M N : Subgroup G} {t : G} (hC : C = M ⊔ zpowers t)
    (hN : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hMM : ∀ m ∈ M, ∀ m' ∈ M, ⁅m, m'⁆ ∈ N) (hMt : ∀ m ∈ M, ⁅m, t⁆ ∈ N) :
    ⁅C, C⁆ ≤ N := by
  have hCcl : closure ((M : Set G) ∪ {t}) = C := by
    rw [hC, Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
  have key : ∀ x ∈ closure ((M : Set G) ∪ {t}), ∀ y ∈ closure ((M : Set G) ∪ {t}),
      ⁅x, y⁆ ∈ N := by
    intro x hx y hy
    refine Subgroup.closure_induction₂ (k := (M : Set G) ∪ {t})
      (p := fun x y _ _ => ⁅x, y⁆ ∈ N) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · intro a b ha hb
      simp only [Set.mem_union, Set.mem_singleton_iff] at ha hb
      rcases ha with haM | rfl <;> rcases hb with hbM | rfl
      · exact hMM a haM b hbM
      · exact hMt a haM
      · have h1 := N.inv_mem (hMt b hbM)
        simpa [commutatorElement_inv] using h1
      · simpa using N.one_mem
    · intro a ha
      simpa using N.one_mem
    · intro a ha
      simpa using N.one_mem
    · intro a b c ha hb hc hac hbc
      have ha' : a ∈ C := hCcl ▸ ha
      have h1 : a * ⁅b, c⁆ * a⁻¹ ∈ N := hN a ha' ⁅b, c⁆ hbc
      have h2 : a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ ∈ N := N.mul_mem h1 hac
      simpa [commutatorElement_mul_left_eq_conj_mul] using h2
    · intro b c a hb hc ha hab hac
      have hb' : b ∈ C := hCcl ▸ hb
      have h1 : b * ⁅a, c⁆ * b⁻¹ ∈ N := hN b hb' ⁅a, c⁆ hac
      have h2 : ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) ∈ N := N.mul_mem hab h1
      have heq : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
        rw [commutatorElement_mul_right_eq_mul_conj]; group
      rw [heq]; exact h2
    · intro a b ha hb hab
      have ha' : a⁻¹ ∈ C := C.inv_mem (hCcl ▸ ha)
      have hba : ⁅b, a⁆ ∈ N := by simpa [commutatorElement_inv] using N.inv_mem hab
      have h1 : a⁻¹ * ⁅b, a⁆ * a ∈ N := by simpa using hN a⁻¹ ha' ⁅b, a⁆ hba
      have heq : ⁅a⁻¹, b⁆ = a⁻¹ * ⁅b, a⁆ * a := commutatorElement_inv_left a b
      rw [heq]; exact h1
    · intro a b ha hb hab
      have hb' : b⁻¹ ∈ C := C.inv_mem (hCcl ▸ hb)
      have hba : ⁅b, a⁆ ∈ N := by simpa [commutatorElement_inv] using N.inv_mem hab
      have h1 : b⁻¹ * ⁅b, a⁆ * b ∈ N := by simpa using hN b⁻¹ hb' ⁅b, a⁆ hba
      have heq : ⁅a, b⁻¹⁆ = b⁻¹ * ⁅b, a⁆ * b := commutatorElement_inv_right a b
      rw [heq]; exact h1
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← hCcl] at hx hy
  exact key x hx y hy

end CFSG.OddStandard.HigherRank.YamadaG23

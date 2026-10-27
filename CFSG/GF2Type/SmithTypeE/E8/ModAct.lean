module

public import CFSG.GF2Type.SmithTypeE.E8.ModFacts
public import CFSG.GF2Type.SmithTypeE.E8.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.LargeExtraspecial
open CFSG.LieType.Steinberg.Minuscule (e7Data)
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7Rep56 e7Y56 e7n6)
open CFSG.SeitzReduction (highRoot)
open CFSG.SeitzReduction.EPilot (pinnedElt)

theorem rep_mul_apply (a b : ↥(adjointGroup .E7 (ZMod 2))) (v : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) (a * b) v = e7Rep56 (ZMod 2) a (e7Rep56 (ZMod 2) b v) := by
  rw [map_mul, Module.End.mul_apply]

theorem rep_one_apply (v : Fin e7Data.d →₀ ZMod 2) : e7Rep56 (ZMod 2) 1 v = v := by
  rw [map_one]
  rfl

theorem rep_comm_apply {a b : ↥(adjointGroup .E7 (ZMod 2))} (h : a * b = b * a)
    (v : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) a (e7Rep56 (ZMod 2) b v) = e7Rep56 (ZMod 2) b (e7Rep56 (ZMod 2) a v) := by
  rw [← rep_mul_apply, ← rep_mul_apply, h]

theorem rep_braid_apply {a b : ↥(adjointGroup .E7 (ZMod 2))} (h : a * b * a = b * a * b)
    (v : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) a (e7Rep56 (ZMod 2) b (e7Rep56 (ZMod 2) a v)) =
      e7Rep56 (ZMod 2) b (e7Rep56 (ZMod 2) a (e7Rep56 (ZMod 2) b v)) := by
  have := congrArg (fun g => e7Rep56 (ZMod 2) g v) h
  simpa only [rep_mul_apply] using this

theorem rep_dihedral_apply {a b : ↥(adjointGroup .E7 (ZMod 2))}
    (h : a * b * a * b = b * a * b * a) (v : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) a (e7Rep56 (ZMod 2) b (e7Rep56 (ZMod 2) a (e7Rep56 (ZMod 2) b v))) =
      e7Rep56 (ZMod 2) b (e7Rep56 (ZMod 2) a (e7Rep56 (ZMod 2) b (e7Rep56 (ZMod 2) a v))) := by
  have := congrArg (fun g => e7Rep56 (ZMod 2) g v) h
  simpa only [rep_mul_apply] using this

section Action

variable {G : Type} [Group G] (S : Setting G)
  (φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2))

theorem exists_cl_eq_vec (v : Fin e7Data.d →₀ ZMod 2) : ∃ u ∈ S.QG, φ (S.cl u) = v := by
  obtain ⟨u, hu, huv⟩ := S.exists_cl (φ.symm v)
  exact ⟨u, hu, by rw [huv, φ.apply_symm_apply]⟩

theorem mul_self_eq_one_of_isConj' {x : G} (hx : IsConj S.z x) : x * x = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hx
  calc g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ := by group
    _ = 1 := by rw [S.z_mul_z]; group

@[expose] def Acts (g : G) (T : ↥(adjointGroup .E7 (ZMod 2))) : Prop :=
  ∀ u ∈ S.QG, φ (S.cl (g * u * g⁻¹)) = e7Rep56 (ZMod 2) T (φ (S.cl u))

variable {S φ}

theorem Acts.mul {g h : G} {T T' : ↥(adjointGroup .E7 (ZMod 2))} (hh : h ∈ S.M)
    (hg : Acts S φ g T) (hH : Acts S φ h T') : Acts S φ (g * h) (T * T') := by
  intro u hu
  have e : g * h * u * (g * h)⁻¹ = g * (h * u * h⁻¹) * g⁻¹ := by group
  rw [e, hg _ (S.conj_mem_QG hh hu), hH u hu, rep_mul_apply]

theorem mem_QG_of_acts [Finite G] {g : G} {T : ↥(adjointGroup .E7 (ZMod 2))} (hgM : g ∈ S.M)
    (hg : Acts S φ g T) (hT : ∀ v, e7Rep56 (ZMod 2) T v = v) : g ∈ S.QG :=
  S.mem_QG_of_cl_conj hgM fun u hu => φ.injective (by rw [hg u hu, hT])

theorem cl_conj_of_mem_QG' {g u : G} (hg : g ∈ S.QG) (hu : u ∈ S.QG) :
    S.cl (g * u * g⁻¹) = S.cl u := by
  rcases S.commutator_eq_one_or_z hg hu with h | h
  · have e : g * u * g⁻¹ = u := by
      calc g * u * g⁻¹ = g * u * g⁻¹ * u⁻¹ * u := by group
        _ = u := by rw [h, one_mul]
    rw [e]
  · have e : g * u * g⁻¹ = S.z * u := by
      calc g * u * g⁻¹ = g * u * g⁻¹ * u⁻¹ * u := by group
        _ = S.z * u := by rw [h]
    rw [e, S.cl_mul S.z_mem_QG hu, S.cl_z, zero_add]

theorem acts_of_mem_QG {g : G} {T : ↥(adjointGroup .E7 (ZMod 2))} (hgQ : g ∈ S.QG)
    (hg : Acts S φ g T) : ∀ v, e7Rep56 (ZMod 2) T v = v := by
  intro v
  obtain ⟨u, hu, rfl⟩ := exists_cl_eq_vec S φ v
  rw [← hg u hu, cl_conj_of_mem_QG' hgQ hu]

theorem acts_of_equiv [Finite G] {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))}
    (hE : SmithE8Equiv S φ ψ) {x : G} (hxM : x ∈ S.M) :
    Acts S φ x (ψ ⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩) := by
  intro u hu
  rw [← hE ⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩ (S.cl u)]
  exact congrArg φ (S.ρ_cl ⟨x, hxM⟩ hu).symm

theorem exists_acts_of_equiv [Finite G] {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))}
    (hE : SmithE8Equiv S φ ψ) (s : ↥(adjointGroup .E7 (ZMod 2))) : ∃ m ∈ S.M, Acts S φ m s := by
  obtain ⟨m, hm⟩ := (ψ.symm s).2
  refine ⟨(m : G), m.2, fun u hu => ?_⟩
  have e := hE (ψ.symm s) (S.cl u)
  rw [ψ.apply_symm_apply] at e
  rw [← e, ← hm]
  exact congrArg φ (S.ρ_cl m hu).symm

theorem Acts.invol {x : G} {T : ↥(adjointGroup .E7 (ZMod 2))} (hx : IsConj S.z x) (hxM : x ∈ S.M)
    (hT : Acts S φ x T) : ∀ v, e7Rep56 (ZMod 2) T (e7Rep56 (ZMod 2) T v) = v := by
  intro v
  have h1 : x * x = 1 := mul_self_eq_one_of_isConj' S hx
  have := acts_of_mem_QG (g := x * x) (by rw [h1]; exact S.QG.one_mem) (hT.mul hxM hT) v
  rwa [rep_mul_apply] at this

end Action

section Pair

variable {G : Type} [Group G] [Finite G] {S : Setting G}
  {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)} {x y : G}
  {A B : ↥(adjointGroup .E7 (ZMod 2))}

theorem sq_mem_of_comm (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hA : Acts S φ x A) (hB : Acts S φ y B)
    (hAA : ∀ v, e7Rep56 (ZMod 2) A (e7Rep56 (ZMod 2) A v) = v)
    (hBB : ∀ v, e7Rep56 (ZMod 2) B (e7Rep56 (ZMod 2) B v) = v) (hc : A * B = B * A) :
    (x * y) ^ 2 ∈ S.QG := by
  have hm : x * y ∈ S.M := S.M.mul_mem hxM hyM
  have hxy : Acts S φ (x * y) (A * B) := hA.mul hyM hB
  rw [sq]
  refine mem_QG_of_acts (S.M.mul_mem hm hm) (hxy.mul hm hxy) fun v => ?_
  simp only [rep_mul_apply]
  rw [rep_comm_apply hc, hAA, hBB]

theorem cube_mem_of_braid (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hA : Acts S φ x A)
    (hB : Acts S φ y B) (hAA : ∀ v, e7Rep56 (ZMod 2) A (e7Rep56 (ZMod 2) A v) = v)
    (hBB : ∀ v, e7Rep56 (ZMod 2) B (e7Rep56 (ZMod 2) B v) = v) (hbr : A * B * A = B * A * B) :
    (x * y) ^ 3 ∈ S.QG := by
  have hm : x * y ∈ S.M := S.M.mul_mem hxM hyM
  have hxy : Acts S φ (x * y) (A * B) := hA.mul hyM hB
  rw [show (x * y) ^ 3 = x * y * (x * y * (x * y)) by rw [pow_succ, sq, mul_assoc]]
  refine mem_QG_of_acts (S.M.mul_mem hm (S.M.mul_mem hm hm))
    (hxy.mul (S.M.mul_mem hm hm) (hxy.mul hm hxy)) fun v => ?_
  simp only [rep_mul_apply]
  rw [rep_braid_apply hbr, hBB, hAA, hBB]

theorem fourth_mem_of_dihedral (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hA : Acts S φ x A)
    (hB : Acts S φ y B) (hAA : ∀ v, e7Rep56 (ZMod 2) A (e7Rep56 (ZMod 2) A v) = v)
    (hBB : ∀ v, e7Rep56 (ZMod 2) B (e7Rep56 (ZMod 2) B v) = v)
    (hd8 : A * B * A * B = B * A * B * A) : (x * y) ^ 4 ∈ S.QG := by
  have hm : x * y ∈ S.M := S.M.mul_mem hxM hyM
  have hxy : Acts S φ (x * y) (A * B) := hA.mul hyM hB
  have hxy2 := hxy.mul hm hxy
  have hxy3 := hxy.mul (S.M.mul_mem hm hm) hxy2
  have hxy4 := hxy.mul (S.M.mul_mem hm (S.M.mul_mem hm hm)) hxy3
  rw [show (x * y) ^ 4 = x * y * (x * y * (x * y * (x * y))) by
    rw [pow_succ, pow_succ, sq, mul_assoc, mul_assoc]]
  refine mem_QG_of_acts (S.M.mul_mem hm (S.M.mul_mem hm (S.M.mul_mem hm hm))) hxy4
    fun v => ?_
  simp only [rep_mul_apply]
  rw [rep_dihedral_apply hd8, hAA, hBB, hAA, hBB]

theorem exists_eq_of_mem_commQt {w : G} {T : ↥(adjointGroup .E7 (ZMod 2))} (hwM : w ∈ S.M)
    (hT : Acts S φ w T) {v : S.Qt} (hv : v ∈ S.commQt w) :
    ∃ c, φ v = e7Rep56 (ZMod 2) T c - c := by
  obtain ⟨u, hu, rfl⟩ := (S.mem_commQt_iff hwM).mp hv
  refine ⟨φ (S.cl u), ?_⟩
  rw [S.cl_mul (S.conj_mem_QG hwM hu) (S.QG.inv_mem hu), S.cl_inv hu, map_add, hT u hu,
    sub_eq_add_neg, ZModModule.neg_eq_self]

end Pair

theorem smithE8E23_of (hF : E8ModelFacts) (hM : SmithE8Module) : SmithE8E23 := by
  intro G _ _ _ S hw hU x y hx hy hxM hyM hxQ hyQ
  obtain ⟨φ, -, -, -, h4⟩ := hM G S hw hU
  obtain ⟨r, hr, hA⟩ := h4 x hx hxM hxQ
  obtain ⟨r', hr', hB⟩ := h4 y hy hyM hyQ
  change Acts S φ x r at hA
  change Acts S φ y r' at hB
  have hAA := hA.invol hx hxM
  have hBB := hB.invol hy hyM
  by_cases hrr : r = r'
  · subst hrr
    exact Or.inl (mem_QG_of_acts (S.M.mul_mem hxM hyM) (hA.mul hyM hB) fun v => by
      rw [rep_mul_apply, hAA])
  rcases hF.pair_rel_sym r r' hr hr' hrr with hc | hbr | hd8
  · exact Or.inr (Or.inl (sq_mem_of_comm hxM hyM hA hB hAA hBB hc))
  · exact Or.inr (Or.inr (Or.inl (cube_mem_of_braid hxM hyM hA hB hAA hBB hbr)))
  · exact Or.inr (Or.inr (Or.inr (fourth_mem_of_dihedral hxM hyM hA hB hAA hBB hd8)))

theorem smithE8E25_of (hF : E8ModelFacts) (hM : SmithE8Module) : SmithE8E25 := by
  intro G _ _ _ S hw hU x y hx hy hxM hyM hxQ hyQ hxyQ
  obtain ⟨φ, -, h2b, -, h4⟩ := hM G S hw hU
  obtain ⟨r, hr, hA⟩ := h4 x hx hxM hxQ
  obtain ⟨r', hr', hB⟩ := h4 y hy hyM hyQ
  change Acts S φ x r at hA
  change Acts S φ y r' at hB
  have hAA := hA.invol hx hxM
  have hBB := hB.invol hy hyM
  have hrr : r ≠ r' := by
    rintro rfl
    exact hxyQ (mem_QG_of_acts (S.M.mul_mem hxM hyM) (hA.mul hyM hB) fun v => by
      rw [rep_mul_apply, hAA])
  have hint : ∀ v ∈ S.commQt x ⊓ S.commQt y, φ v = 0 ∨
      (r * r' = r' * r ∧ φ v ∈ weightVec) := by
    intro v hv
    obtain ⟨c, hcv⟩ := exists_eq_of_mem_commQt hxM hA hv.1
    obtain ⟨c', hcv'⟩ := exists_eq_of_mem_commQt hyM hB hv.2
    rw [hcv]
    exact hF.int_rel_sym r r' hr hr' hrr c c' (hcv.symm.trans hcv')
  have hzero : ∀ {v : S.Qt}, φ v = 0 → v = 0 := fun h => φ.injective (h.trans (map_zero φ).symm)
  refine ⟨fun _ v hv => ?_, fun hcu => ?_, fun hn2 _ => ?_⟩
  · rcases hint v hv with h0 | ⟨-, hw'⟩
    · exact ⟨S.z, IsConj.refl _, S.z_mem_QG, by rw [hzero h0, S.cl_z]⟩
    · obtain ⟨c, hc, hcQ, hcj⟩ := h2b _ hw'
      exact ⟨c, hc, hcQ, φ.injective hcj⟩
  · rw [eq_bot_iff]
    intro v hv
    rcases hint v hv with h0 | ⟨hc, -⟩
    · exact (Submodule.mem_bot _).mpr (hzero h0)
    · exfalso
      apply hxyQ
      have hm : x * y ∈ S.M := S.M.mul_mem hxM hyM
      have hxy : Acts S φ (x * y) (r * r') := hA.mul hyM hB
      rw [show (x * y) ^ 3 = x * y * (x * y) * (x * y) by rw [pow_succ, sq]] at hcu
      have hF3 := acts_of_mem_QG hcu ((hxy.mul hm hxy).mul hm hxy)
      have h2 : ∀ u, e7Rep56 (ZMod 2) (r * r' * (r * r')) u = u := by
        intro u
        simp only [rep_mul_apply]
        rw [rep_comm_apply hc, hAA, hBB]
      refine mem_QG_of_acts hm hxy fun v' => ?_
      have := hF3 v'
      rwa [rep_mul_apply, h2] at this
  · rw [eq_bot_iff]
    intro v hv
    rcases hint v hv with h0 | ⟨hc, -⟩
    · exact (Submodule.mem_bot _).mpr (hzero h0)
    · exact absurd (sq_mem_of_comm hxM hyM hA hB hAA hBB hc) hn2

end CFSG.GF2Type.SmithTypeE.E8

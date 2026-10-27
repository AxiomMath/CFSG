module

public import CFSG.LargeExtraspecial.S14C8Cases
public import CFSG.LargeExtraspecial.S14C13Conj
public import CFSG.LargeExtraspecial.S14C8Norm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem FCt_le_Ct (t : S.O) : FCt S t ≤ Ct S t := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem conj_mem_FCt_of_mem_Ct {t c f : S.O} (hc : c ∈ Ct S t) (hf : f ∈ FCt S t) :
    c * f * c⁻¹ ∈ FCt S t := by
  obtain ⟨x, hx, rfl⟩ := hf
  have := (timmesfeldFStar_normal (Ct S t)).conj_mem x hx ⟨c, hc⟩
  exact ⟨_, this, rfl⟩

theorem isPGroup_FCt {t : S.O} (h7 : Concl14_7 S g t) : IsPGroup 2 (FCt S t) :=
  h7.2.map (Ct S t).subtype

theorem FCt_inf_Rbar_le_Nbar (hCE : CentralExtInput.{0}) [IsSimpleGroup G] {t : S.O}
    {c : Config} (hSt : Stage S g t) (hocc : c.Occurs S g t)
    (hext : IsExtraspecialPGroup 2 (Nbar S g t)) (h7 : Concl14_7 S g t) :
    FCt S t ⊓ Rbar S g t ≤ Nbar S g t := by
  have haQ := hSt.hyp4.conj_mem
  have hRp := rbarPerfectStmt_of hCE G S g t c hSt hocc hext
  rcases le_Nbar_or_le_of_normal (K := FCt S t ⊓ Rbar S g t) haQ
      (isSimpleGroup_RmodN_of_occurs hocc) hRp hext.1 inf_le_right
      (fun r hr k hk => Subgroup.mem_inf.mpr
        ⟨conj_mem_FCt_of_mem_Ct
          (Subgroup.mem_inf.mpr ⟨Rbar_le_Mbar hr, Rbar_le_centralizer haQ hr⟩)
          (Subgroup.mem_inf.mp hk).1,
          mul_mem (mul_mem hr (Subgroup.mem_inf.mp hk).2) (inv_mem hr)⟩) with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : IsPGroup 2 (Rbar S g t) :=
      (isPGroup_FCt h7).to_le (h.trans inf_le_left)
    have : Group.IsPerfect (Rbar S g t) := (Subgroup.isPerfect_iff).mpr hRp
    have : Nontrivial (Rbar S g t) := ⟨⟨⟨t, Lbar_le_Rbar hSt.mem hSt.mem⟩, 1, fun e =>
      hSt.ne_one (congrArg Subtype.val e)⟩⟩
    exact Group.IsPerfect.not_isNilpotent (G := Rbar S g t) h2.isNilpotent

theorem comm_mem_Nbar_of_mem_FCt (hCE : CentralExtInput.{0}) [IsSimpleGroup G] {t : S.O}
    {c : Config} (hSt : Stage S g t) (hocc : c.Occurs S g t)
    (hext : IsExtraspecialPGroup 2 (Nbar S g t)) (h7 : Concl14_7 S g t) {β : S.O}
    (hβ : β ∈ FCt S t) : ∀ r ∈ Rbar S g t, β * r * β⁻¹ * r⁻¹ ∈ Nbar S g t := by
  intro r hr
  have haQ := hSt.hyp4.conj_mem
  have hrC : r ∈ Ct S t := Subgroup.mem_inf.mpr ⟨Rbar_le_Mbar hr, Rbar_le_centralizer haQ hr⟩
  refine FCt_inf_Rbar_le_Nbar hCE hSt hocc hext h7 (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [show β * r * β⁻¹ * r⁻¹ = β * (r * β⁻¹ * r⁻¹) by group]
    exact mul_mem hβ (conj_mem_FCt_of_mem_Ct hrC (inv_mem hβ))
  · exact mul_mem (conj_Rbar_of_mem_Ct (FCt_le_Ct t hβ) hr) (inv_mem hr)

section Lin

variable {t : S.O} [NQHyp S g t]

theorem cLin_mul {x y : S.O} (hx : x ∈ Ct S t) (hy : y ∈ Ct S t) :
    cLin (g := g) (mul_mem hx hy) = cLin (g := g) hx * cLin (g := g) hy := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨n, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) m
  rw [Module.End.mul_apply, cLin_mk, cLin_mk, cLin_mk]
  exact congrArg nqMk (Subtype.ext (by simp [coe_cConj, mul_assoc]))

theorem cLin_one : cLin (g := g) (one_mem (Ct S t)) = 1 := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨n, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) m
  rw [cLin_mk, Module.End.one_apply]
  exact congrArg nqMk (Subtype.ext (by simp [coe_cConj]))

theorem cLin_pow_apply {x : S.O} (hx : x ∈ Ct S t) (k : ℕ) (n : Nbar S g t) :
    (cLin (g := g) hx ^ k) (nqMk n) = nqMk (cConj (pow_mem hx k) n) := by
  induction k with
  | zero =>
    rw [pow_zero, Module.End.one_apply]
    exact congrArg nqMk (Subtype.ext (by simp [coe_cConj]))
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, cLin_mk]
    exact congrArg nqMk (Subtype.ext (by rw [coe_cConj, coe_cConj, coe_cConj]; group))

theorem cLin_pow_eq_one {x : S.O} (hx : x ∈ Ct S t) {k : ℕ} (hk : x ^ k = 1) :
    cLin (g := g) hx ^ k = 1 := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨n, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) m
  rw [cLin_pow_apply, Module.End.one_apply]
  exact congrArg nqMk (Subtype.ext (by rw [coe_cConj, hk]; group))

theorem cLin_eq_one_of_mem_Nbar {z : S.O} (hz : z ∈ Ct S t) (hzN : z ∈ Nbar S g t) :
    cLin (g := g) hz = 1 := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨n, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) m
  rw [cLin_mk, Module.End.one_apply, nqMk_eq_iff]
  have hc := (inferInstance : NQHyp S g t).comm _ hzN _ (inv_mem n.2)
  convert hc using 1
  rw [coe_cConj]
  group

end Lin

theorem sub_one_pow_two_pow {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (d : Module.End (ZMod 2) M) (k : ℕ) : (d - 1) ^ (2 ^ k) = d ^ (2 ^ k) - 1 := by
  have h2 : ∀ f : Module.End (ZMod 2) M, f + f = 0 := fun f => by
    rw [← two_smul (ZMod 2) f, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hsq : ∀ e : Module.End (ZMod 2) M, (e - 1) * (e - 1) = e * e - 1 := by
    intro e
    have h : (e - 1) * (e - 1) = e * e - 1 - (e + e) + (1 + 1) := by noncomm_ring
    rw [h, h2, h2, sub_zero, add_zero]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih, pow_two, hsq, ← pow_two, ← pow_mul, ← pow_succ]

end CFSG.LargeExtraspecial.S14

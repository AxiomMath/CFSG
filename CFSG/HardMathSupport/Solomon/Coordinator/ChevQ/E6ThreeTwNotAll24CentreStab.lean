module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
public import CFSG.LieType.AlgebraicGroups.ToralRootCover

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint.Chevalley.RootCertificate
  CFSG.LieType.AlgebraicGroups

set_option maxRecDepth 100000

section Count


def triKerCount (b : Fin Tag.E6.rank → ZMod 3) : ℕ :=
  ((rootFinset .E6).filter fun α => triPairing b α = 0).card

theorem triKerCount_reps : ∀ ρ < 8, triKerCount (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) =
    [72, 40, 40, 30, 22, 22, 24, 18].getD ρ 0 := by
  decide +kernel

theorem rep_index_of_conn {ρ : ℕ} (hρ : ρ < 8)
    (h : triKerCount (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) ∈ ({22, 30, 40} : Set ℕ)) :
    ρ = 1 ∨ ρ = 2 ∨ ρ = 3 ∨ ρ = 4 ∨ ρ = 5 := by
  rw [triKerCount_reps ρ hρ] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  interval_cases ρ <;> simp_all

theorem triKerCount_eq_of_isCharConj {b b' : Fin Tag.E6.rank → ZMod 3} {t : WeylGroup .E6}
    (ht : IsCharConj (triChar b') (triChar b) t) : triKerCount b = triKerCount b' := by
  have hpair : ∀ v, triPairing b v = triPairing b' (t⁻¹ • v) := fun v => by
    have h := ht v
    rw [triChar_apply, triChar_apply] at h
    exact Z3.ofAdd_eq_ofAdd_iff.1 h
  unfold triKerCount
  refine Finset.card_bij (fun α _ => t⁻¹ • α) (fun α hα => ?_) (fun α _ β _ h => ?_)
    (fun β hβ => ?_)
  · rw [Finset.mem_filter, mem_rootFinset] at hα ⊢
    exact ⟨IsRoot.smul hα.1 t⁻¹, by rw [← hpair]; exact hα.2⟩
  · exact MulAction.injective t⁻¹ h
  · rw [Finset.mem_filter, mem_rootFinset] at hβ
    refine ⟨t • β, ?_, inv_smul_smul t β⟩
    rw [Finset.mem_filter, mem_rootFinset]
    refine ⟨IsRoot.smul hβ.1 t, ?_⟩
    rw [hpair, inv_smul_smul]
    exact hβ.2

end Count

section Conn


theorem passing_conn_reps : ∀ ρ ∈ [1, 2, 3, 4, 5],
    (e6ThreeStabs.getD ρ e6ThreeStab0).passing e6Certificate = [List.range 6] := by
  decide +kernel

theorem mem_kernelWeylGroup_of_stabCert_one {S : StabCert3} (hS : S.check e6Certificate = true)
    (hpass : S.passing e6Certificate = [List.range Tag.E6.rank])
    {w : WeylGroup .E6} (hw : w ∈ charStabilizer (triChar (vec3 (τ := .E6) S.vec))) :
    w ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) S.vec)) := by
  obtain ⟨u, hu, hwu⟩ := exists_mul_mem_kernelPosStabilizer hw
  obtain ⟨t, ht, hrep⟩ := StabCert3.exists_passing_of_mem e6Certificate_check hS hwu
  rw [hpass] at ht
  have htr : t = List.range Tag.E6.rank := by simpa using ht
  subst htr
  have h1 : w * u = 1 := represents_unique hrep (represents_one e6Certificate_check)
  rw [eq_inv_of_mul_eq_one_left h1]
  exact inv_mem hu

theorem mem_kernelWeylGroup_of_conn
    (b : Fin Tag.E6.rank → ZMod 3) (hb : triKerCount b ∈ ({22, 30, 40} : Set ℕ))
    {w : WeylGroup .E6} (hw : w ∈ charStabilizer (triChar b)) :
    w ∈ kernelWeylGroup (triChar b) := by
  obtain ⟨horbit, hstab⟩ := e6ThreeScCheck_spec
  have hvec := e6ThreeStabs_vec
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 horbit (triChar b)
  have hlen : ρ < e6ThreeStabs.length := by
    rw [← List.length_map StabCert3.vec, hvec]
    exact hρ
  have hρ8 : ρ < 8 := hρ
  set S := e6ThreeStabs[ρ] with hSdef
  have hSv : S.vec = e6ThreeReps.getD ρ [] := by
    rw [List.getD_eq_getElem _ _ hρ, hSdef]
    have := congrArg (fun l => l[ρ]?) hvec
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlen, List.getElem?_eq_getElem hρ,
      Option.map_some, Option.some.injEq] at this
    exact this
  obtain ⟨hScheck, -⟩ := hstab S (List.getElem_mem hlen)
  rw [← hSv] at ht
  set bρ := vec3 (τ := .E6) S.vec with hbρ
  have hcnt : triKerCount bρ ∈ ({22, 30, 40} : Set ℕ) := by
    rw [← triKerCount_eq_of_isCharConj ht]
    exact hb
  have hρ' : ρ = 1 ∨ ρ = 2 ∨ ρ = 3 ∨ ρ = 4 ∨ ρ = 5 := by
    refine rep_index_of_conn hρ8 ?_
    rw [← hSv]
    exact hcnt
  have hpass : S.passing e6Certificate = [List.range 6] := by
    have h := passing_conn_reps ρ (by rcases hρ' with h | h | h | h | h <;> simp [h])
    rw [List.getD_eq_getElem _ _ hlen] at h
    exact h
  have hw₀ : t⁻¹ * w * t ∈ charStabilizer (triChar bρ) :=
    (charStabilizer_iff_of_isCharConj ht).1 hw
  have hk := mem_kernelWeylGroup_of_stabCert_one hScheck hpass hw₀
  rw [kernelWeylGroup_eq_map ht]
  exact ⟨t⁻¹ * w * t, hk, by simp [mul_assoc]⟩

theorem e6_stab_le_kernelReflectionGroup_of_conn {K : Type}
    [Field K] (a : Fin Tag.E6.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1)
    (hk : (kernelRoots (rootCharHom a)).ncard ∈ ({22, 30, 40} : Set ℕ)) :
    rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
  classical
  obtain ⟨χ', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a h3)
  have hS : rootCharStabilizerSubgroup a = charStabilizer (rootCharHom3 a) :=
    Subgroup.ext fun w => Iff.rfl
  have hW : kernelReflectionGroup a = kernelWeylGroup (rootCharHom3 a) := rfl
  rw [hS, hW, charStabilizer_congr_ker hker, kernelWeylGroup_congr_ker hker]
  obtain ⟨b, rfl⟩ : ∃ b, χ' = triChar b := ⟨_, eq_triChar χ'⟩
  intro w hw
  refine mem_kernelWeylGroup_of_conn b ?_ hw
  have hker' : kernelRoots (rootCharHom3 a) = kernelRoots (triChar b) := kernelRoots_congr_ker hker
  have : triKerCount b = (kernelRoots (triChar b)).ncard := by
    unfold triKerCount
    rw [← Set.ncard_coe_finset]
    congr 1
    ext α
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_rootFinset]
    exact mem_kernelRoots_triChar.symm
  rw [this, ← hker']
  exact hk

end Conn

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

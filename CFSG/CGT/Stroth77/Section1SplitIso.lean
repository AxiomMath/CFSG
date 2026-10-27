module

public import CFSG.CGT.Stroth77.Section1SplitModel
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.SectionExtension

public section

namespace CFSG.CGT.Stroth77

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
  CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster (exists_section_of_compl)

namespace Msp

@[expose] def cl (m : Msp) : altHeart 6 := ((⟨m.vec, m.par_vec⟩ : evenWeight 6) : altHeart 6)

theorem mk_nrm (x : Vec6) (hx : par x = 0) (hnx : par (nrm x) = 0) :
    (((⟨nrm x, hnx⟩ : evenWeight 6)) : altHeart 6) = ((⟨x, hx⟩ : evenWeight 6) : altHeart 6) := by
  refine QuotientAddGroup.eq.2 (mem_evenWeightOnes_of_forall_eq (c := x 5) fun i => ?_)
  show -(x i + x 5) + x i = x 5
  generalize x i = a; generalize x 5 = b
  revert a b; decide

theorem cl_mul (a b : Msp) : (a * b).cl = a.cl + altAct a.perm b.cl := by
  have h1 : par (a.vec + pact a.perm b.vec) = 0 := by
    rw [par_add, par_pact, a.par_vec, b.par_vec, add_zero]
  have e1 : (a * b).cl = ((⟨a.vec + pact a.perm b.vec, h1⟩ : evenWeight 6) : altHeart 6) := by
    have hv : (a * b).vec = nrm (a.vec + pact a.perm b.vec) := vec_mul a b
    have := mk_nrm (a.vec + pact a.perm b.vec) h1 (by rw [← hv]; exact (a * b).par_vec)
    rw [← this]
    unfold cl
    congr 2
  rw [e1]
  unfold cl
  rw [altAct_mk, ← QuotientAddGroup.mk_add]
  rfl

theorem cl_ofPerm (σ : Perm (Fin 6)) : (ofPerm σ).cl = 0 := by
  unfold cl
  rw [QuotientAddGroup.eq_zero_iff]
  exact mem_evenWeightOnes_of_forall_eq (c := 0) fun _ => rfl

theorem cl_heartToMsp (x : altHeart 6) : (heartToMsp x).cl = x := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [heartToMsp_mk]
  unfold cl
  have hv : (evToMsp y).vec = nrm (y : Vec6) := evToMsp_vec y
  have := mk_nrm (y : Vec6) y.2 (by rw [← hv]; exact (evToMsp y).par_vec)
  rw [← this]
  congr 2

theorem eq_one_of_cl {m : Msp} (hp : m.perm = 1) (hc : m.cl = 0) : m = 1 := by
  refine ext ?_ hp
  obtain ⟨c, hc'⟩ := exists_forall_eq_of_mem_evenWeightOnes ((QuotientAddGroup.eq_zero_iff _).1 hc)
  have h5 : m.vec 5 = c := hc' 5
  rw [vec_five] at h5
  funext i
  have := hc' i
  rw [← h5] at this
  exact this

end Msp

theorem exists_mulEquiv_Msp_of_section {Γ : Type*} [Group Γ] (θ : Γ →* Perm (Fin 6))
    (ψ : Multiplicative (altHeart 6) ≃* θ.ker)
    (hconj : ∀ (g : Γ) (v : Multiplicative (altHeart 6)), g * (ψ v : Γ) * g⁻¹ =
      (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : Γ))
    (s : Perm (Fin 6) →* Γ) (hs : ∀ σ, θ (s σ) = σ) :
    ∃ e : Msp ≃* Γ, (∀ v, e (ψsp v : Msp) = (ψ v : Γ)) ∧ ∀ m, θ (e m) = θsp m := by
  have hψθ : ∀ v, θ (ψ v : Γ) = 1 := fun v => (ψ v).2
  let f : Msp →* Γ :=
    { toFun := fun m => (ψ (Multiplicative.ofAdd m.cl) : Γ) * s m.perm
      map_one' := by
        have h0 : (1 : Msp).cl = 0 := by
          unfold Msp.cl
          rw [QuotientAddGroup.eq_zero_iff]
          exact mem_evenWeightOnes_of_forall_eq (c := 0) fun _ => rfl
        show (ψ (Multiplicative.ofAdd (1 : Msp).cl) : Γ) * s (1 : Msp).perm = 1
        rw [h0, Msp.perm_one, map_one, ofAdd_zero, map_one, Subgroup.coe_one, one_mul]
      map_mul' := fun a b => by
        show (ψ (Multiplicative.ofAdd (a * b).cl) : Γ) * s (a * b).perm =
          (ψ (Multiplicative.ofAdd a.cl) : Γ) * s a.perm *
            ((ψ (Multiplicative.ofAdd b.cl) : Γ) * s b.perm)
        have hc := hconj (s a.perm) (Multiplicative.ofAdd b.cl)
        rw [hs, toAdd_ofAdd] at hc
        have hc' : (ψ (Multiplicative.ofAdd (altAct a.perm b.cl)) : Γ) * s a.perm =
            s a.perm * (ψ (Multiplicative.ofAdd b.cl) : Γ) := by
          rw [← hc, inv_mul_cancel_right]
        rw [Msp.cl_mul, Msp.perm_mul, ofAdd_add, map_mul, Subgroup.coe_mul, map_mul, mul_assoc,
          ← mul_assoc _ (s a.perm), hc']
        group }
  have hfθ : ∀ m, θ (f m) = θsp m := by
    intro m
    show θ ((ψ (Multiplicative.ofAdd m.cl) : Γ) * s m.perm) = m.perm
    rw [map_mul, hψθ, one_mul, hs]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have hp : m.perm = 1 := by
      have := hfθ m
      rw [hm, map_one] at this
      exact this.symm
    have hm' : (ψ (Multiplicative.ofAdd m.cl) : Γ) * s m.perm = 1 := hm
    rw [hp, map_one, mul_one] at hm'
    have hψ1 : ψ (Multiplicative.ofAdd m.cl) = 1 := Subtype.ext hm'
    have hc : m.cl = 0 := by
      have := ψ.injective (hψ1.trans (map_one ψ).symm)
      exact this
    exact Msp.eq_one_of_cl hp hc
  have hsurj : Function.Surjective f := by
    intro γ
    have hk : γ * (s (θ γ))⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]
    set v := ψ.symm ⟨_, hk⟩ with hv
    refine ⟨heartToMsp v.toAdd * Msp.ofPerm (θ γ), ?_⟩
    show (ψ (Multiplicative.ofAdd (heartToMsp v.toAdd * Msp.ofPerm (θ γ)).cl) : Γ) *
      s (heartToMsp v.toAdd * Msp.ofPerm (θ γ)).perm = γ
    rw [Msp.cl_mul, Msp.cl_ofPerm, map_zero, add_zero, Msp.cl_heartToMsp, Msp.perm_mul,
      heartToMsp_perm, one_mul, Msp.perm_ofPerm, ofAdd_toAdd, hv, MulEquiv.apply_symm_apply]
    simp
  refine ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun v => ?_, hfθ⟩
  show (ψ (Multiplicative.ofAdd (heartHomSp v).cl) : Γ) * s (heartHomSp v).perm = (ψ v : Γ)
  have hp : (heartHomSp v).perm = 1 := heartToMsp_perm _
  have hc : (heartHomSp v).cl = v.toAdd := Msp.cl_heartToMsp _
  rw [hp, hc, map_one, mul_one, ofAdd_toAdd]

theorem exists_mulEquiv_Msp_of_compl {Γ : Type} [Group Γ] (θ : Γ →* Perm (Fin 6))
    (hθ : Function.Surjective θ) (ψ : Multiplicative (altHeart 6) ≃* θ.ker)
    (hconj : ∀ (g : Γ) (v : Multiplicative (altHeart 6)), g * (ψ v : Γ) * g⁻¹ =
      (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : Γ))
    {K : Subgroup Γ} (h1 : θ.ker ⊓ K = ⊥) (h2 : θ.ker ⊔ K = ⊤) :
    ∃ e : Msp ≃* Γ, (∀ v, e (ψsp v : Msp) = (ψ v : Γ)) ∧ ∀ m, θ (e m) = θsp m := by
  obtain ⟨s, hs, -⟩ := exists_section_of_compl θ hθ h1 h2
  exact exists_mulEquiv_Msp_of_section θ ψ hconj s hs

end CFSG.CGT.Stroth77

module

public import CFSG.CGT.T75M23.P7Check
public import CFSG.CGT.T75M23.P7Struct
public import CFSG.CGT.T75M23.Interfaces
public import Certificates.Certificate271033

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable CFSG.CGT.Timmesfeld75 CFSG.CGT.T75I
open CFSG.CGT.T75JM (evalWord7 evalWord7_liftWord OntoEmb evalWord3)

theorem pFacts7_of_certificate :
    PFacts7 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h7', h8, h9, h10, h11⟩ :=
    Certificates.certificate271033
  exact pFacts7_of_checks h1 h2 h3 h4 h5 h6 h7 h7' h8 h9 h10 h11

theorem evalWord7_append7 {H : Type*} [Group H] (e : Fin 7 → H) (a b : M23Word) :
    evalWord7 e (a ++ b) = evalWord7 e a * evalWord7 e b := by
  simp only [evalWord7, ← map_mul, FreeGroup.mul_mk]

theorem evalWord7_nil7 {H : Type*} [Group H] (e : Fin 7 → H) : evalWord7 e [] = 1 := by
  rw [evalWord7]
  exact map_one _

theorem evalWord7_single7 {H : Type*} [Group H] (e : Fin 7 → H) (i : Fin 7) :
    evalWord7 e [(i, true)] = e i := by
  show FreeGroup.lift e (FreeGroup.of i) = e i
  exact FreeGroup.lift_apply_of

theorem evalWord7_invWord7 {H : Type*} [Group H] (e : Fin 7 → H) (w : M23Word) :
    evalWord7 e (invWord7 w) = (evalWord7 e w)⁻¹ := by
  rw [evalWord7, evalWord7, ← map_inv, FreeGroup.inv_mk, FreeGroup.invRev, invWord7,
    List.map_reverse]

theorem evalWord7_genTuple7_liftWord {G : Type} [Group G] {T : Subgroup G}
    (ψ : PG 6 rels7 ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G) (w : List (Fin 6 × Bool)) :
    evalWord7 (genTuple7 ψ g) (liftWord7 w) =
      ((ψ (n7 w) : ↥(Subgroup.normalizer (T : Set G))) : G) := by
  rw [liftWord7_eq, evalWord7_liftWord]
  have h2 : (FreeGroup.lift (fun i : Fin 6 => genTuple7 ψ g (Fin.castSucc i)) :
      FreeGroup (Fin 6) →* G) =
      (Subgroup.normalizer (T : Set G)).subtype.comp
        (ψ.toMonoidHom.comp (PresentedGroup.mk {r : FreeGroup (Fin 6) |
          r ∈ rels7.map FreeGroup.mk})) := by
    apply FreeGroup.ext_hom
    intro i
    simp [genTuple7, PresentedGroup.mk]
    rfl
  rw [h2]
  rfl

theorem genTuple7_six {G : Type} [Group G] {T : Subgroup G}
    (ψ : PG 6 rels7 ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G) : genTuple7 ψ g 6 = g := by
  simp [genTuple7]

theorem pStatement7_of_certificate :
    PStatement7 := by
  intro G _ _ _ T T₁ hyp c r hr
  have hf := pFacts7_of_certificate
  have hg6 := genTuple7_six c.ψ c.g
  have hgg : c.g * c.g = 1 := by
    have h := c.rel [(6, true), (6, true)] (by simp [thetaRels7])
    rw [show ([(6, true), (6, true)] : M23Word) = [(6, true)] ++ [(6, true)] from rfl,
      evalWord7_append7, evalWord7_single7, hg6] at h
    exact h
  let E : OntoEmb N7 (Subgroup.normalizer (T : Set G)) := OntoEmb.ofEquiv c.ψ
  have hT : ∀ x, x ∈ n7T ↔ E.Φ x ∈ T := by
    intro x
    have h1 : x ∈ Subgroup.closure (Set.range tGen7) ↔
        c.ψ x ∈ Subgroup.map c.ψ.toMonoidHom (Subgroup.closure (Set.range tGen7)) := by
      rw [Subgroup.mem_map_equiv]
      simp
    rw [c.map_t, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hconj : ∀ i : Fin 3, c.g * E.Φ (n7 (dGen7 i)) * c.g⁻¹ = E.Φ (n7 (dTheta7 i)) := by
    intro i
    have hmem : ([(6, true)] ++ liftWord7 (dGen7 i) ++ [(6, true)] ++
        liftWord7 (invWord7 (dTheta7 i)) : M23Word) ∈ thetaRels7 := by
      unfold thetaRels7
      refine List.mem_cons_of_mem _ ?_
      rw [List.mem_ofFn]
      exact ⟨i, rfl⟩
    have h := c.rel _ hmem
    change evalWord7 (genTuple7 c.ψ c.g) _ = 1 at h
    rw [evalWord7_append7, evalWord7_append7, evalWord7_append7, evalWord7_single7, hg6,
      evalWord7_genTuple7_liftWord, evalWord7_genTuple7_liftWord, n7_invWord, map_inv] at h
    have hg' : c.g⁻¹ = c.g := inv_eq_of_mul_eq_one_right hgg
    rw [hg']
    exact mul_inv_eq_one.1 h
  let pc : PCfg7 T T₁ 0 :=
    { E := E
      hT := hT
      g := c.g
      hgg := by
        show c.g * c.g = E.Φ (n7 [])
        rw [n7_nil, map_one]
        exact hgg
      hconj := hconj }
  have hbase : ∀ i : Fin 3, evalWord7 (genTuple7 c.ψ c.g) (base3Z i) = pc.aG i := by
    intro i
    fin_cases i
    · show evalWord7 _ (liftWord7 (vGen7 0)) = E.Φ (n7 (vGen7 0))
      rw [evalWord7_genTuple7_liftWord]
      rfl
    · show evalWord7 _ (liftWord7 (vGen7 1)) = E.Φ (n7 (vGen7 1))
      rw [evalWord7_genTuple7_liftWord]
      rfl
    · show evalWord7 _ [(6, true)] = c.g
      rw [evalWord7_single7]
      exact hg6
  have hexp : ∀ w : List (Fin 3 × Bool),
      evalWord7 (genTuple7 c.ψ c.g) (expand3Z w) = evalWord3 pc.aG w := by
    intro w
    induction w with
    | nil =>
      show evalWord7 _ [] = evalWord3 pc.aG []
      rw [evalWord7_nil7, evalWord3_nil7]
    | cons p w ih =>
      have h1 : expand3Z (p :: w) =
          (if p.2 then base3Z p.1 else invWord7 (base3Z p.1)) ++ expand3Z w := rfl
      rw [h1, evalWord7_append7, ih, evalWord3_cons7]
      congr 1
      rcases p with ⟨i, b⟩
      cases b
      · simp [evalWord7_invWord7, hbase]
      · simp [hbase]
  rw [pRels7, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  change evalWord7 (genTuple7 c.ψ c.g) (expand3Z w) = 1
  rw [hexp w]
  exact pc.rels_of_zero hf hyp.cent_le w hw

end CFSG.CGT.T75M23

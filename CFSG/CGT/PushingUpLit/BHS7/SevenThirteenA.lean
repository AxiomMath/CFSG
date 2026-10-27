module

public import CFSG.CGT.PushingUpLit.BHS7.OffenderConj
public import CFSG.CGT.PushingUpLit.BHS7.SevenSeven

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

omit [Finite Γ] in
theorem tZero_le : tZero G T ≤ T := by
  unfold tZero
  split_ifs
  · exact qSub_le
  · exact (C1GN.omegaOneCenterOf_le_self (baum T)).trans (C1GN.baum_le T)

omit [Finite Γ] in
theorem conjSub_sup_eq (g : Γ) (A B : Subgroup Γ) :
    A1b.conjSub g (A ⊔ B) = A1b.conjSub g A ⊔ A1b.conjSub g B := by
  unfold A1b.conjSub
  exact Subgroup.map_sup _ _ _

theorem le_normalizer_tZero_sup (h : MinCex G T) {g : Γ} (hgG : g ∈ G)
    (hgT : A1b.conjSub g T = T) :
    g ∈ Subgroup.normalizer ((tZero G T ⊔ (G ⊓ Subgroup.centralizer (vSub G T : Set Γ)) :
      Subgroup Γ) : Set Γ) := by
  refine BHS.mem_normalizer_of_conjSub_eq ?_
  have hVn : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
  have hT0 : A1b.conjSub g (tZero G T) = tZero G T := by
    have := conjSub_tZero h.charTwo h.sylow hgG
    rw [hgT] at this
    exact this.symm
  have hCn : g ∈ Subgroup.normalizer ((G ⊓ Subgroup.centralizer (vSub G T : Set Γ) :
      Subgroup Γ) : Set Γ) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hgG,
      B6.le_normalizer_centralizer hVn hgG⟩
  rw [conjSub_sup_eq, hT0, conjSub_eq_of_mem_normalizer hCn]

omit [Finite Γ] in
theorem le_normalizer_tZero_sup_of_comm {E : Subgroup Γ} (hEG : E ≤ G) (hT0 : tZero G T ≤ G)
    (hcomm : ∀ x ∈ tZero G T, ∀ e ∈ E, ⁅x, e⁆ ∈ Subgroup.centralizer (vSub G T : Set Γ)) :
    E ≤ Subgroup.normalizer ((tZero G T ⊔ (G ⊓ Subgroup.centralizer (vSub G T : Set Γ)) :
      Subgroup Γ) : Set Γ) := by
  have hVn : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
  have key : ∀ e ∈ E, ∀ y ∈ tZero G T ⊔ (G ⊓ Subgroup.centralizer (vSub G T : Set Γ)),
      e * y * e⁻¹ ∈ tZero G T ⊔ (G ⊓ Subgroup.centralizer (vSub G T : Set Γ)) := by
    intro e he
    have hCn : e ∈ Subgroup.normalizer ((G ⊓ Subgroup.centralizer (vSub G T : Set Γ) :
        Subgroup Γ) : Set Γ) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hEG he),
        B6.le_normalizer_centralizer hVn (hEG he)⟩
    have hle : tZero G T ⊔ (G ⊓ Subgroup.centralizer (vSub G T : Set Γ)) ≤
        (tZero G T ⊔ (G ⊓ Subgroup.centralizer (vSub G T : Set Γ))).comap
          (MulAut.conj e).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · have hc : ⁅e, y⁆ ∈ G ⊓ Subgroup.centralizer (vSub G T : Set Γ) := by
          refine ⟨?_, ?_⟩
          · simp only [commutatorElement_def]
            exact G.mul_mem (G.mul_mem (G.mul_mem (hEG he) (hT0 hy)) (G.inv_mem (hEG he)))
              (G.inv_mem (hT0 hy))
          · have := (Subgroup.centralizer (vSub G T : Set Γ)).inv_mem (hcomm y hy e he)
            rwa [commutatorElement_inv] at this
        show e * y * e⁻¹ ∈ tZero G T ⊔ (G ⊓ Subgroup.centralizer (vSub G T : Set Γ))
        have h2 : e * y * e⁻¹ = ⁅e, y⁆ * y := by simp only [commutatorElement_def]; group
        rw [h2]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hy)
      · show e * y * e⁻¹ ∈ tZero G T ⊔ (G ⊓ Subgroup.centralizer (vSub G T : Set Γ))
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hCn y).mp hy)
    exact fun y hy => hle hy
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key e he y, fun hy => ?_⟩
  have := key e⁻¹ (E.inv_mem he) _ hy
  simpa [mul_assoc] using this

theorem normalizer_tZero_lt (h : MinCex G T)
    (hne : ¬ tZero G T ≤ Subgroup.centralizer (vSub G T : Set Γ)) :
    G ⊓ Subgroup.normalizer ((tZero G T ⊔ (G ⊓ Subgroup.centralizer (vSub G T : Set Γ)) :
      Subgroup Γ) : Set Γ) < G := by
  have hT : IsSylowTwoOf T G := h.sylow
  have hVn : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
  refine lt_of_le_of_ne inf_le_left fun heq => hne ?_
  set R : Subgroup Γ := tZero G T ⊔ (G ⊓ Subgroup.centralizer (vSub G T : Set Γ)) with hR
  have hT0G : tZero G T ≤ G := tZero_le.trans hT.1
  have hRG : R ≤ G := sup_le hT0G inf_le_left
  have hGn : G ≤ Subgroup.normalizer (R : Set Γ) := fun g hg => by
    have : g ∈ G ⊓ Subgroup.normalizer (R : Set Γ) := by rw [heq]; exact hg
    exact this.2
  have hR2 : IsPGroup 2 ↥(autOn R (vSub G T)) := by
    have hT0V : tZero G T ≤ Subgroup.normalizer (vSub G T : Set Γ) := hT0G.trans hVn
    refine IsPGroup.to_le (isPGroup_autOn (hT.2.1.to_le tZero_le) hT0V) ?_
    intro y hy
    obtain ⟨a, haR, rfl⟩ := mem_autOn_iff.mp hy
    have hCn : tZero G T ≤ Subgroup.normalizer ((G ⊓ Subgroup.centralizer (vSub G T : Set Γ) :
        Subgroup Γ) : Set Γ) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hT0G ht),
        B6.le_normalizer_centralizer hVn (hT0G ht)⟩
    have haR' : (a : Γ) ∈ ((R : Subgroup Γ) : Set Γ) := haR
    rw [hR, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCn] at haR'
    obtain ⟨t, ht, c, hc, hac⟩ := haR'
    refine mem_autOn_iff.mpr ⟨⟨t, hT0V ht⟩, ht, ?_⟩
    have hca : conjAct (vSub G T) ⟨c, (hVn (hc.1))⟩ = 1 := (conjAct_eq_one_iff _ _).mpr hc.2
    have hmul : a = ⟨t, hT0V ht⟩ * ⟨c, hVn hc.1⟩ := Subtype.ext hac.symm
    rw [hmul, map_mul, hca, mul_one]
  have := le_centralizer_vSub_of_isPGroup_autOn hT hRG hGn hR2
  exact (le_sup_left : tZero G T ≤ R).trans this

theorem seven_thirteen_one (h : MinCex G T) {E H : Subgroup Γ} (hE : E ∈ bStarT G T)
    (hcomm : ∀ x ∈ tZero G T, ∀ e ∈ E, ⁅x, e⁆ ∈ Subgroup.centralizer (vSub G T : Set Γ))
    (hne : ¬ tZero G T ≤ Subgroup.centralizer (vSub G T : Set Γ))
    (huniq : ∀ H' : Subgroup Γ, IsMaximalSubgroup G H' → E ⊔ baum T ≤ H' → H' = H) :
    G ⊓ Subgroup.normalizer ((tZero G T ⊔ (G ⊓ Subgroup.centralizer (vSub G T : Set Γ)) :
      Subgroup Γ) : Set Γ) ≤ H ∧ T ≤ H ∧ G ⊓ Subgroup.normalizer (T : Set Γ) ≤ H ∧
      G ⊓ Subgroup.centralizer (vSub G T : Set Γ) ≤ H := by
  have hT : IsSylowTwoOf T G := h.sylow
  set R : Subgroup Γ := tZero G T ⊔ (G ⊓ Subgroup.centralizer (vSub G T : Set Γ)) with hR
  set K : Subgroup Γ := G ⊓ Subgroup.normalizer (R : Set Γ) with hK
  have hKG : K < G := normalizer_tZero_lt h hne
  have hEG : E ≤ G := hE.1.2.le
  have hT0G : tZero G T ≤ G := tZero_le.trans hT.1
  have hEK : E ≤ K := le_inf hEG (le_normalizer_tZero_sup_of_comm hEG hT0G hcomm)
  have hTK : T ≤ K := fun g hg =>
    ⟨hT.1 hg, le_normalizer_tZero_sup h (hT.1 hg) (conjSub_eq_of_mem_normalizer
      (Subgroup.le_normalizer hg))⟩
  have hNK : G ⊓ Subgroup.normalizer (T : Set Γ) ≤ K := fun g hg =>
    ⟨hg.1, le_normalizer_tZero_sup h hg.1 (conjSub_eq_of_mem_normalizer hg.2)⟩
  have hCK : G ⊓ Subgroup.centralizer (vSub G T : Set Γ) ≤ K := fun g hg =>
    ⟨hg.1, Subgroup.le_normalizer (le_sup_right (a := tZero G T) hg)⟩
  obtain ⟨M, hM, hKM⟩ := exists_maximalSubgroup_ge hKG
  have hMH : M = H := huniq M hM (sup_le (hEK.trans hKM) ((C1GN.baum_le T).trans (hTK.trans hKM)))
  subst hMH
  exact ⟨hKM, hTK.trans hKM, hNK.trans hKM, hCK.trans hKM⟩

end CFSG.CGT.PushingUpLit.BHS7

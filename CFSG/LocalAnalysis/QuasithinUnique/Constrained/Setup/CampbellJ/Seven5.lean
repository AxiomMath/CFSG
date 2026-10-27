module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellExclusion
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellUtil
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocalAimg
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six4a
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Seven1
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Seven2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Seven34
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellLocal
import CFSG.Quasithin.Background.C118PartnerB

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}
  {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))}
  {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} {A : Subgroup G} {g : G}

private def DsubJ_Seven5 (S : Sylow 2 G)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : Subgroup G :=
  CFSG.pCore 2 G ⊓ Subgroup.centralizer
    ((Fcore G ⊔ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G) :
      Subgroup G) : Set G)

private def XsubJ_Seven5 (S : Sylow 2 G)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : Subgroup G :=
  CFSG.Quasithin.thompsonJ (DsubJ_Seven5 S α)

private theorem aimg_symm_B0_max_Seven5 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G)
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (B0J S α A)) := by
  classical
  let T : Subgroup G := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  have hFJ : Fcore G ≤ T := Fcore_le_JS c.seed
  have hB0Q : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (B0J S α A) :=
    c.facts71.2.1
  have hB0S : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) (B0J S α A) :=
    c.seed.max_core_facts.1 _ hB0Q
  have hB0T : B0J S α A ≤ T := maxElem_le_thompsonJ hB0S
  have hFaB0 : aimg T α (Fcore G) ≤ B0J S α A :=
    (le_sup_right : aimg T α (Fcore G) ≤ Fcore G ⊔ aimg T α (Fcore G)).trans le_sup_left
  have hB0aQ : B0J S α A ≤ aimg T α (CFSG.pCore 2 G) := by
    intro x hx
    have hxT : x ∈ T := hB0T hx
    have hxc : x ∈ Subgroup.centralizer ((aimg T α (Fcore G) : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun w hw =>
        (isElemAbelian_iff.mp hB0S.2.1).1 w (hFaB0 hw) x hx
    have h1 : aimg T α (T ⊓ Subgroup.centralizer ((Fcore G : Subgroup G) : Set G)) =
        T ⊓ Subgroup.centralizer ((aimg T α (Fcore G) : Subgroup G) : Set G) := by
      rw [aimg_centralizer (S := T) (α := α) (Y := T) (Y' := Fcore G) hFJ, aimg_self]
    have h2 : x ∈ aimg T α (T ⊓ Subgroup.centralizer
        ((Fcore G : Subgroup G) : Set G)) := by
      rw [h1]; exact ⟨hxT, hxc⟩
    exact aimg_mono c.seed.sylow_inf_centralizer_Fcore_le
      (aimg_mono (inf_le_inf (thompsonJ_le_self' (S : Subgroup G)) le_rfl) h2)
  have hB0'Q : aimg T α.symm (B0J S α A) ≤ CFSG.pCore 2 G := by
    have h1 : aimg T α.symm (B0J S α A) ≤ aimg T α.symm (aimg T α (CFSG.pCore 2 G)) :=
      aimg_mono hB0aQ
    have hQe : aimg T α.symm (aimg T α (CFSG.pCore 2 G)) = CFSG.pCore 2 G ⊓ T := by
      rw [← aimg_inf_self (S := T) (α := α) (Y := CFSG.pCore 2 G),
        aimg_symm_aimg (S := T) (α := α) (Y := CFSG.pCore 2 G ⊓ T) inf_le_right]
    rw [hQe] at h1
    exact h1.trans inf_le_left
  exact ⟨hB0'Q, isElemAbelian_aimg α.symm hB0S.2.1, fun B hBQ hBe => by
    have := maxElem_card_le hB0S (hBQ.trans hQS) hBe
    rwa [← card_aimg (S := T) (α := α.symm) hB0T] at this⟩

private theorem X_core_max_Seven5 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    CFSG.Quasithin.IsMaxElemAbelian (DsubJ_Seven5 S α)
        (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (B0J S α A)) ∧
      (∀ A', CFSG.Quasithin.IsMaxElemAbelian (DsubJ_Seven5 S α) A' →
        CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) A') := by
  classical
  let T : Subgroup G := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  have hB0'max := aimg_symm_B0_max_Seven5 c
  have hFB0 : Fcore G ≤ B0J S α A := le_sup_left.trans le_sup_left
  have hFB0' : Fcore G ≤ aimg T α.symm (B0J S α A) := fun f hf =>
    (mem_Fcore_iff.mp hf).2 _ hB0'max
  have hFiB0' : aimg T α.symm (Fcore G) ≤ aimg T α.symm (B0J S α A) := aimg_mono hFB0
  have hB0'D : aimg T α.symm (B0J S α A) ≤ DsubJ_Seven5 S α :=
    le_inf hB0'max.1 fun x hx => mem_centralizer_sup
      (fun y hy => (isElemAbelian_iff.mp hB0'max.2.1).1 y (hFB0' hy) x hx)
      (fun y hy => (isElemAbelian_iff.mp hB0'max.2.1).1 y (hFiB0' hy) x hx)
  exact ⟨⟨hB0'D, hB0'max.2.1, fun B hBD hBe =>
      hB0'max.2.2 B (hBD.trans inf_le_left) hBe⟩,
    fun A' hA' => ⟨hA'.1.trans inf_le_left, hA'.2.1, fun B hBQ hBe =>
      (hB0'max.2.2 B hBQ hBe).trans (maxElem_card_le hA' hB0'D hB0'max.2.1)⟩⟩

private theorem X_factsJ_Seven5 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (B0J S α A) ≤ XsubJ_Seven5 S α ∧
      XsubJ_Seven5 S α ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) ∧
      XsubJ_Seven5 S α ≤ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)) := by
  classical
  let T : Subgroup G := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let JQ : Subgroup G := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)
  obtain ⟨hB0'DAe, hAe⟩ := X_core_max_Seven5 c
  refine ⟨maxElem_le_thompsonJ hB0'DAe, ?_, ?_⟩
  · exact thompsonJ_le_of_forall fun A' hA' => maxElem_le_thompsonJ (hAe A' hA')
  · refine thompsonJ_le_of_forall fun A' hA' => ?_
    have hA'D : A' ≤ DsubJ_Seven5 S α := hA'.1
    have hA'Q : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) A' := hAe A' hA'
    have hA'J : A' ≤ T := maxElem_le_thompsonJ (c.seed.max_core_facts.1 A' hA'Q)
    have hA'C : A' ≤ Subgroup.centralizer
        ((aimg T α.symm (Fcore G) : Subgroup G) : Set G) :=
      hA'D.trans (inf_le_right.trans (Subgroup.centralizer_le
        (le_sup_right : aimg T α.symm (Fcore G) ≤ Fcore G ⊔ aimg T α.symm (Fcore G))))
    have hαA'Qle : aimg T α A' ≤ CFSG.pCore 2 G := by
      calc aimg T α A' ≤ aimg T α (T ⊓ Subgroup.centralizer
            ((aimg T α.symm (Fcore G) : Subgroup G) : Set G)) :=
            aimg_mono (le_inf hA'J hA'C)
        _ = T ⊓ Subgroup.centralizer ((Fcore G : Subgroup G) : Set G) := by
            rw [aimg_centralizer (S := T) (α := α) (Y := T)
                (Y' := aimg T α.symm (Fcore G))
                (aimg_le (S := T) (α := α.symm) (Y := Fcore G)), aimg_self,
              aimg_aimg_symm (S := T) (α := α) (Y := Fcore G) (Fcore_le_JS c.seed)]
        _ ≤ CFSG.pCore 2 G :=
            (inf_le_inf (thompsonJ_le_self' (S : Subgroup G)) le_rfl).trans
              c.seed.sylow_inf_centralizer_Fcore_le
    have hαA'Q : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (aimg T α A') :=
      ⟨hαA'Qle, isElemAbelian_aimg α hA'.2.1, fun B hBQ hBe => by
        have := hA'Q.2.2 B hBQ hBe
        rwa [← card_aimg (S := T) (α := α) hA'J] at this⟩
    have hαA'R : aimg T α A' ≤ JQ := maxElem_le_thompsonJ hαA'Q
    have := aimg_mono (S := T) (α := α.symm) hαA'R
    rwa [aimg_symm_aimg (S := T) (α := α) hA'J] at this

private theorem AgU_Seven5 (c : DoubleSetupJ S ρ ψ Λ α A g)
    (hYB : YsubJ S α g ≤ BbJ S α A g) :
    ⁅cj A g, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆ ≤
      Fcore G := by
  classical
  let T : Subgroup G := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  have hAZZ : ⁅A, B0J S α A⁆ ≤ Zfix S ⊔ aimg T α (Zfix S) := c.facts71.2.2.2
  have hYB0 : YsubJ S α g ≤ B0J S α A := (c.lemma73 hYB).2 ▸ hYB
  have hAY : ⁅A, YsubJ S α g⁆ ≤ Fcore G :=
    (Subgroup.commutator_mono le_rfl hYB0).trans
      (hAZZ.trans (sup_le c.seed.Zfix_le_Fcore (aimgJ_Zfix_le_Fcore c.seed α)))
  have e : ⁅cj A g, aimg T α.symm (cj (aimg T α (Fcore G)) g)⁆ =
      cj ⁅A, cj (aimg T α.symm (cj (aimg T α (Fcore G)) g)) g⁻¹⁆ g := by
    rw [cj_commutator, cj_cj_inv]
  rw [e, inv_eq_of_mul_eq_one_right c.hg2]
  calc cj ⁅A, cj (aimg T α.symm (cj (aimg T α (Fcore G)) g)) g⁆ g ≤
        cj (Fcore G) g := cj_mono hAY
    _ = Fcore G := cj_eq_self_of_normal

private theorem commutator_X_Seven5 (c : DoubleSetupJ S ρ ψ Λ α A g)
    (hYB : YsubJ S α g ≤ BbJ S α A g) :
    ⁅XsubJ_Seven5 S α, Fcore G ⊔ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)⁆ =
      Zfix S := by
  classical
  let T : Subgroup G := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let U : Subgroup G := aimg T α.symm (cj (aimg T α (Fcore G)) g)
  let JQ : Subgroup G := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)
  obtain ⟨hX1, hX2, hX3⟩ := X_factsJ_Seven5 c
  obtain ⟨-, -, -, -, hUAdm⟩ := U_factsJ c.seed c.lam c.hαΛ c.hgH c.hg2
  have hPJ : cj (aimg T α (Fcore G)) g ≤ T := by
    simpa only [tr] using tr_Fcore_le_thompsonJ_sylowJ c.seed α g (c.lam.vmod α c.hαΛ)
  have hUR : U ≤ JQ := by
    obtain ⟨A', hA', hle⟩ := hUAdm
    exact hle.trans (maxElem_le_thompsonJ hA')
  have hB0S : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) (B0J S α A) :=
    c.seed.max_core_facts.1 _ c.facts71.2.1
  have hB0T : B0J S α A ≤ T := maxElem_le_thompsonJ hB0S
  apply le_antisymm
  · have h1 : ⁅XsubJ_Seven5 S α, Fcore G ⊔ U⁆ ≤ ⁅XsubJ_Seven5 S α, U⁆ := by
      rw [Subgroup.commutator_comm, sup_comm, Subgroup.commutator_comm (XsubJ_Seven5 S α)]
      exact commutator_sup_of_commute
        (fun x hx y hy => Fcore_commute_thompsonJ_core hy (hUR hx))
        (fun y hy w hw => (Fcore_commute_thompsonJ_core hy (hX2 hw)).symm)
    have h2 : ⁅XsubJ_Seven5 S α, U⁆ ≤ ⁅aimg T α.symm (JQ), U⁆ :=
      Subgroup.commutator_mono hX3 le_rfl
    have h3 : ⁅aimg T α.symm (JQ), U⁆ = Zfix S := by
      have := aimg_commutator (S := T) (α := α.symm)
        c.seed.thompsonJ_core_le_thompsonJ_sylow hPJ
      rw [c.commutator_R0_Pg, aimg_symm_aimg (S := T) (Zfix_le_JS c.seed)] at this
      exact this.symm
    exact h1.trans (h2.trans h3.le)
  · have h1 : ⁅aimg T α.symm (B0J S α A), U⁆ = Zfix S := by
      have := aimg_commutator (S := T) (α := α.symm) hB0T hPJ
      rw [c.commutator_B0_Pg, aimg_symm_aimg (S := T) (Zfix_le_JS c.seed)] at this
      exact this.symm
    calc Zfix S = ⁅aimg T α.symm (B0J S α A), U⁆ := h1.symm
      _ ≤ ⁅XsubJ_Seven5 S α, U⁆ := Subgroup.commutator_mono hX1 le_rfl
      _ ≤ _ := Subgroup.commutator_mono le_rfl le_sup_right

private theorem cj_Zfix_Seven5 (c : DoubleSetupJ S ρ ψ Λ α A g)
    (hYB : YsubJ S α g ≤ BbJ S α A g) :
    ∀ a ∈ cj A g, cj (Zfix S) a = Zfix S := by
  classical
  let T : Subgroup G := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  have hZX := commutator_X_Seven5 c hYB
  have hR := c.lemma74 hYB
  have hAgU := AgU_Seven5 c hYB
  intro a ha
  have haH : a ∈ Hone S := by rw [c.Hone_eq_sup]; exact Subgroup.mem_sup_right ha
  have e1 : cj (Fcore G ⊔ aimg T α.symm (Fcore G)) a =
      Fcore G ⊔ aimg T α.symm (Fcore G) :=
    cj_sup_eq_of_commutator_le fun w hw => hR (Subgroup.commutator_mem_commutator haH hw)
  have e2 : cj (Fcore G ⊔ aimg T α.symm (cj (aimg T α (Fcore G)) g)) a =
      Fcore G ⊔ aimg T α.symm (cj (aimg T α (Fcore G)) g) :=
    cj_sup_eq_of_commutator_le fun u hu => hAgU (Subgroup.commutator_mem_commutator ha hu)
  have hD : cj (DsubJ_Seven5 S α) a = DsubJ_Seven5 S α := by
    change cj (CFSG.pCore 2 G ⊓ Subgroup.centralizer
      ((Fcore G ⊔ aimg T α.symm (Fcore G) : Subgroup G) : Set G)) a =
      CFSG.pCore 2 G ⊓ Subgroup.centralizer
        ((Fcore G ⊔ aimg T α.symm (Fcore G) : Subgroup G) : Set G)
    rw [cj_inf, cj_eq_self_of_normal (Y := CFSG.pCore 2 G), ← centralizer_cj, e1]
  have hX : cj (XsubJ_Seven5 S α) a = XsubJ_Seven5 S α := by
    change cj (CFSG.Quasithin.thompsonJ (DsubJ_Seven5 S α)) a =
      CFSG.Quasithin.thompsonJ (DsubJ_Seven5 S α)
    exact cj_thompsonJ_eq hD
  calc cj (Zfix S) a = cj ⁅XsubJ_Seven5 S α, Fcore G ⊔ aimg T α.symm
        (cj (aimg T α (Fcore G)) g)⁆ a := by rw [hZX]
    _ = ⁅cj (XsubJ_Seven5 S α) a, cj (Fcore G ⊔ aimg T α.symm
        (cj (aimg T α (Fcore G)) g)) a⁆ := cj_commutator
    _ = ⁅XsubJ_Seven5 S α, Fcore G ⊔ aimg T α.symm
        (cj (aimg T α (Fcore G)) g)⁆ := by rw [hX, e2]
    _ = Zfix S := hZX

theorem DoubleSetupJ.Y_not_le_B (c : DoubleSetupJ S ρ ψ Λ α A g) :
    ¬ YsubJ S α g ≤ BbJ S α A g := by
  classical
  intro hYB
  have hZa := cj_Zfix_Seven5 c hYB
  obtain ⟨a₀, ha₀, ha₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp c.hAQ
  have ha : g * a₀ * g⁻¹ ∈ cj A g := by
    rw [mem_cj]
    have h1 : g * (g * a₀ * g⁻¹) * g⁻¹ = a₀ := by
      calc g * (g * a₀ * g⁻¹) * g⁻¹ = (g * g) * a₀ * (g⁻¹ * g⁻¹) := by group
        _ = a₀ := by rw [c.hg2, inv_eq_of_mul_eq_one_right c.hg2, c.hg2]; group
    rw [h1]; exact ha₀
  have hmemN : g * a₀ * g⁻¹ ∈ Subgroup.normalizer (Zfix S : Set G) :=
    mem_normalizer_of_le_cj (hZa _ ha).symm.le
  have hM := c.seed.normalizer_Zfix_le_Mnorm hmemN
  exact c.hgM (c.seed.mem_Mnorm_of_conj_mem (c.hA.1 ha₀) ha₀Q hM)

end CFSG.QuasithinUnique.Setup.CampbellJ

end

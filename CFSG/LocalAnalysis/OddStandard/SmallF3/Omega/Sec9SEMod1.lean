module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def phiSim (Q : QuadraticForm (ZMod 3) V) : OGroup Q →* ProjSim Q :=
  (projOrthToProjSim Q).comp (toProj Q)

theorem phiSim_eq_one_iff {g : OGroup Q} : phiSim Q g = 1 ↔ g = 1 ∨ g = piOrth Q := by
  rw [phiSim, MonoidHom.comp_apply,
    map_eq_one_iff (projOrthToProjSim Q) projOrthToProjSim_injective]
  exact Iff.trans (QuotientGroup.eq_one_iff g) mem_piGroup_iff

private lemma ker_phiSim (Q : QuadraticForm (ZMod 3) V) : (phiSim Q).ker = piGroup Q := by
  ext g
  rw [MonoidHom.mem_ker, phiSim_eq_one_iff, mem_piGroup_iff]

private noncomputable def kerSubgroupComapEquiv {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (H : Subgroup G') : (f.subgroupComap H).ker ≃ f.ker where
  toFun x := ⟨((x.1 : H.comap f) : G), by
    show f ((x.1 : H.comap f) : G) = 1
    have h : (((f.subgroupComap H) x.1 : H) : G') = 1 :=
      congrArg (fun z : H => (z : G')) x.2
    exact h⟩
  invFun y := ⟨⟨(y.1 : G), by
    show f (y.1 : G) ∈ H
    rw [y.2]
    exact H.one_mem⟩, by
    apply Subtype.ext
    show f (y.1 : G) = (1 : G')
    exact y.2⟩
  left_inv x := rfl
  right_inv y := rfl

private lemma card_ker_subgroupComap {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (H : Subgroup G') :
    Nat.card (f.subgroupComap H).ker = Nat.card f.ker :=
  Nat.card_congr (kerSubgroupComapEquiv f H)

private lemma card_comap_eq_card_ker_mul_card_of_le_range {G G' : Type*} [Group G] [Group G']
    (f : G →* G') {H : Subgroup G'} (hH : H ≤ f.range) :
    Nat.card (H.comap f) = Nat.card f.ker * Nat.card H := by
  have hsurj : Function.Surjective (f.subgroupComap H) := by
    intro y
    obtain ⟨x, hx⟩ := hH y.2
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    show f x ∈ H
    rw [hx]
    exact y.2
  have hcard : Nat.card (f.subgroupComap H).ker * Nat.card H = Nat.card (H.comap f) :=
    Subgroup.card_ker_mul_card_of_surjective (f := f.subgroupComap H) hsurj
  rw [← hcard, card_ker_subgroupComap]

theorem sec9e_card_comap (h : 0 < Module.finrank (ZMod 3) V) (F : Subgroup (ProjSim Q))
    (hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f) :
    Nat.card (F.comap (phiSim Q)) = Nat.card F * 2 := by
  have hFle : F ≤ (phiSim Q).range := by
    intro f hf
    by_cases hf1 : f = 1
    · subst hf1
      exact ⟨1, map_one _⟩
    · obtain ⟨t, -, ht⟩ := hlift f hf hf1
      exact ⟨t, ht⟩
  rw [card_comap_eq_card_ker_mul_card_of_le_range (phiSim Q) hFle, ker_phiSim, card_piGroup h]
  exact Nat.mul_comm _ _

theorem sec9e_comap_sq (F : Subgroup (ProjSim Q))
    (hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f) :
    ∀ g ∈ F.comap (phiSim Q), g * g = 1 := by
  intro g hg
  rw [Subgroup.mem_comap] at hg
  by_cases hfg : phiSim Q g = 1
  · rcases (phiSim_eq_one_iff.mp hfg) with rfl | hpi
    · rw [one_mul]
    · rw [hpi]
      exact piOrth_mul_self
  · obtain ⟨t, htt, ht⟩ := hlift (phiSim Q g) hg hfg
    have hker : phiSim Q (g * t⁻¹) = 1 := by
      rw [map_mul, map_inv, ht, mul_inv_cancel]
    rcases (phiSim_eq_one_iff.mp hker) with h1 | h1
    · have hgt : g = t := by
        have := congrArg (fun z => z * t) h1
        simpa [mul_assoc] using this
      rw [hgt, htt]
    · have hgt : g = piOrth Q * t := by
        have := congrArg (fun z => z * t) h1
        simpa [mul_assoc] using this
      rw [hgt, piOrth_mul_mul_self htt]

theorem sec9e_comap_invDim_ne_one (hQ : Q.Nondegenerate) (h6 : Module.finrank (ZMod 3) V = 6)
    (F : Subgroup (ProjSim Q))
    (hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f ∧ 2 ≤ invDim t ∧
      invDim t ≤ 4) :
    ∀ g ∈ F.comap (phiSim Q), g ≠ 1 → invDim g ≠ 1 := by
  intro g hg hgne
  rw [Subgroup.mem_comap] at hg
  by_cases hfg : phiSim Q g = 1
  · rcases (phiSim_eq_one_iff.mp hfg) with h1 | hpi
    · exact absurd h1 hgne
    · have hdimpi : invDim (piOrth Q) = Module.finrank (ZMod 3) V := by
        have := congrArg Prod.fst (invType_piOrth hQ)
        simpa only [invType] using this
      rw [hpi, hdimpi, h6]
      decide
  · obtain ⟨t, htt, ht, htlo, hthi⟩ := hlift (phiSim Q g) hg hfg
    have hker : phiSim Q (g * t⁻¹) = 1 := by
      rw [map_mul, map_inv, ht, mul_inv_cancel]
    rcases (phiSim_eq_one_iff.mp hker) with h1 | h1
    · have hgt : g = t := by
        have := congrArg (fun z => z * t) h1
        simpa [mul_assoc] using this
      rw [hgt]
      omega
    · have hgt : g = piOrth Q * t := by
        have := congrArg (fun z => z * t) h1
        simpa [mul_assoc] using this
      rw [hgt]
      have hdim : invDim (piOrth Q * t) = Module.finrank (ZMod 3) V - invDim t := by
        have := congrArg Prod.fst (invType_piOrth_mul hQ htt)
        simpa only [invType] using this
      rw [hdim, h6]
      omega

end CFSG.OddStandard.SmallF3.Omega

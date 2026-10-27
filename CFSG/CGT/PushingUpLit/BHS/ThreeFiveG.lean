module

public import CFSG.CGT.PushingUpLit.BHS.ThreeFiveF
public import CFSG.CGT.PushingUpLit.BHS.GlaubMain
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS.Glauberman CFSG.RankThree.PartOne CFSG.Open
  CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ]

@[expose] def secProj (ρ : Γ →* MulAut V) (T : Subgroup Γ) (hW : ∀ v : V, v ∈ wMod ρ T) :
    V →* Sec (wMod ρ T) (fixV ρ.range) :=
  (QuotientGroup.mk' ((fixV ρ.range).subgroupOf (wMod ρ T))).comp
    { toFun := fun v => ⟨v, hW v⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem secProj_apply (ρ : Γ →* MulAut V) (T : Subgroup Γ) (hW : ∀ v : V, v ∈ wMod ρ T) (v : V) :
    secProj ρ T hW v = QuotientGroup.mk ⟨v, hW v⟩ := rfl

theorem secProj_surjective (ρ : Γ →* MulAut V) (T : Subgroup Γ) (hW : ∀ v : V, v ∈ wMod ρ T) :
    Function.Surjective (secProj ρ T hW) := by
  intro s
  induction s using QuotientGroup.induction_on with
  | H w => exact ⟨w.1, rfl⟩

theorem secProj_eq_one_iff (ρ : Γ →* MulAut V) (T : Subgroup Γ) (hW : ∀ v : V, v ∈ wMod ρ T)
    (v : V) : secProj ρ T hW v = 1 ↔ v ∈ fixV ρ.range := by
  rw [secProj_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem secProj_act (ρ : Γ →* MulAut V) (T : Subgroup Γ) (hW : ∀ v : V, v ∈ wMod ρ T) (g : Γ)
    (v : V) : secProj ρ T hW (ρ g v) = secF ρ T g (secProj ρ T hW v) := rfl

namespace ThreeFiveHyp

variable {ρ : Γ →* MulAut V} {T M A : Subgroup Γ} (h : ThreeFiveHyp ρ T M A)

include h

variable [Finite V] [Finite Γ]

theorem three_five_abs :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card A = 2 ^ n ∧ wMod ρ T = ⊤ ∧
      Nat.card V = Nat.card A * Nat.card (fixV (A.map ρ)) ∧
      fixV (A.map ρ) = commV (A.map ρ) ⊔ fixV ρ.range ∧
      (∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers (ρ a)) = fixV (A.map ρ)) ∧
      ∃ (θ : Γ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
        (β : V →* Multiplicative (Fin 2 → GaloisField 2 n)),
        Function.Surjective β ∧ β.ker = fixV ρ.range ∧
        ∀ (x : Γ) (v : V), β (ρ x v) = Multiplicative.ofAdd
          ((θ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
            (Multiplicative.toAdd (β v))) := by
  obtain ⟨n, hn1, hAn, hVn, hSL, hcomm, hfixc, hzp⟩ := glauberman_natural h.glHyp_secF
  have hcard : Nat.card (Sec (wMod ρ T) (fixV ρ.range)) =
      Nat.card (A.map (secF ρ T)) * Nat.card (fixV (A.map (secF ρ T))) := by
    rw [hVn, hfixc, hAn, ← mul_pow]
    norm_num
  obtain ⟨-, hsup, hVcard⟩ := h.ker_eq_bot_of_card_eq hcard
  have hW : wMod ρ T = ⊤ := h.wMod_eq_top hsup
  have hker : (secF ρ T).ker = ⊥ := h.ker_secF_eq_bot hW
  have hinj : Function.Injective (secF ρ T) := (MonoidHom.ker_eq_bot_iff _).1 hker
  have hmem : ∀ v : V, v ∈ wMod ρ T := fun v => hW ▸ Subgroup.mem_top v
  have hAcard : Nat.card A = 2 ^ n := by
    rw [← hAn]
    exact (Subgroup.card_map_of_injective hinj).symm
  obtain ⟨x, hx⟩ := h.exists_not_mem
  have hD1 : ∀ v : V, secProj ρ T hmem v ∈ fixV (A.map (secF ρ T)) → v ∈ fixV (A.map ρ) := by
    intro v hv
    refine h.mem_fixV_A_of_mod hx (hmem v) (fun a ha => ?_)
    have h1 := mem_fixV.1 hv (secF ρ T a) (Subgroup.mem_map_of_mem _ ha)
    have h2 : secProj ρ T hmem (ρ a v * v⁻¹) = 1 := by
      rw [map_mul, map_inv, secProj_act, h1, mul_inv_cancel]
    exact (secProj_eq_one_iff ρ T hmem _).1 h2
  have hD2 : ∀ v ∈ fixV (A.map ρ), secProj ρ T hmem v ∈ fixV (A.map (secF ρ T)) := by
    intro v hv
    rw [mem_fixV]
    rintro _ ⟨a, ha, rfl⟩
    rw [← secProj_act, mem_fixV.1 hv (ρ a) (Subgroup.mem_map_of_mem ρ ha)]
  have hcommeq : fixV (A.map ρ) = commV (A.map ρ) ⊔ fixV ρ.range := by
    refine le_antisymm ?_ (sup_le h.quadratic (fixV_range_le_fixV_map ρ A))
    intro v hv
    have hv1 : secProj ρ T hmem v ∈ commV (A.map (secF ρ T)) := by
      rw [hcomm]
      exact hD2 v hv
    have hle : commV (A.map (secF ρ T)) ≤
        (commV (A.map ρ) ⊔ fixV ρ.range).map (secProj ρ T hmem) := by
      rw [G6.commV_le_iff]
      rintro _ ⟨a, ha, rfl⟩ s
      obtain ⟨w, rfl⟩ := secProj_surjective ρ T hmem s
      refine ⟨ρ a w * w⁻¹, Subgroup.mem_sup_left
        (G6.mem_commV_of_mem (Subgroup.mem_map_of_mem ρ ha) w), ?_⟩
      rw [map_mul, map_inv, secProj_act]
    obtain ⟨k, hkK, hke⟩ := hle hv1
    have hvk : v * k⁻¹ ∈ fixV ρ.range := by
      rw [← secProj_eq_one_iff ρ T hmem, map_mul, map_inv, hke, mul_inv_cancel]
    have : v = (v * k⁻¹) * k := by rw [inv_mul_cancel_right]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hvk) hkK
  have hzpow : ∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers (ρ a)) = fixV (A.map ρ) := by
    intro a ha ha1
    refine le_antisymm ?_ (fixV_anti (Subgroup.zpowers_le.2 (Subgroup.mem_map_of_mem ρ ha)))
    intro v hv
    have hva : ρ a v = v := mem_fixV_zpowers.1 hv
    have h1 : secProj ρ T hmem v ∈ fixV (Subgroup.zpowers (secF ρ T a)) := by
      rw [mem_fixV_zpowers, ← secProj_act, hva]
    have hne : secF ρ T a ≠ 1 := fun h0 => ha1 (hinj (by rw [h0, map_one]))
    rw [hzp (secF ρ T a) (Subgroup.mem_map_of_mem _ ha) hne] at h1
    exact hD1 v h1
  obtain ⟨-, θ, β, hsurj, hkerβ, hequiv⟩ := hSL
  let θe : Γ ≃* ↥((⊤ : Subgroup Γ).map (secF ρ T)) :=
    Subgroup.topEquiv.symm.trans (Subgroup.equivMapOfInjective ⊤ (secF ρ T) hinj)
  refine ⟨n, hn1, hAcard, hW, hVcard, hcommeq, hzpow, θe.trans θ,
    β.comp ((Subgroup.topEquiv.symm : Sec (wMod ρ T) (fixV ρ.range) ≃*
      ↥(⊤ : Subgroup (Sec (wMod ρ T) (fixV ρ.range)))).toMonoidHom.comp
        (secProj ρ T hmem)), ?_, ?_, ?_⟩
  · exact hsurj.comp (Subgroup.topEquiv.symm.surjective.comp (secProj_surjective ρ T hmem))
  · ext v
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      hkerβ, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    exact secProj_eq_one_iff ρ T hmem v
  · intro g v
    exact hequiv (θe g) (Subgroup.topEquiv.symm (secProj ρ T hmem v)) trivial

end ThreeFiveHyp

end CFSG.CGT.PushingUpLit.BHS

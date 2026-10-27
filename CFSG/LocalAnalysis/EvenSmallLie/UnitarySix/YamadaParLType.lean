module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParGamma
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParImage

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix Subgroup CFSG.Fischer

section Factor

variable {Γ X M : Type*} [Group Γ] [Group X] [Monoid M]

noncomputable def factorHom (F : Γ →* M) (ρ : X →* M) (hρ : Function.Injective ρ)
    (hF : ∀ γ, ∃ x, ρ x = F γ) : Γ →* X where
  toFun γ := Classical.choose (hF γ)
  map_one' := hρ (by rw [Classical.choose_spec (hF 1), map_one, map_one])
  map_mul' γ γ' := hρ (by
    rw [Classical.choose_spec (hF (γ * γ')), map_mul, map_mul, Classical.choose_spec (hF γ),
      Classical.choose_spec (hF γ')])

theorem factorHom_spec (F : Γ →* M) (ρ : X →* M) (hρ : Function.Injective ρ)
    (hF : ∀ γ, ∃ x, ρ x = F γ) (γ : Γ) : ρ (factorHom F ρ hρ hF γ) = F γ :=
  Classical.choose_spec (hF γ)

theorem factorHom_surjective (F : Γ →* M) (ρ : X →* M) (hρ : Function.Injective ρ)
    (hF : ∀ γ, ∃ x, ρ x = F γ) (hρF : ∀ x, ∃ γ, F γ = ρ x) :
    Function.Surjective (factorHom F ρ hρ hF) := fun x => by
  obtain ⟨γ, hγ⟩ := hρF x
  exact ⟨γ, hρ (by rw [factorHom_spec, hγ])⟩

theorem factorHom_ker (F : Γ →* M) (ρ : X →* M) (hρ : Function.Injective ρ)
    (hF : ∀ γ, ∃ x, ρ x = F γ) : (factorHom F ρ hρ hF).ker = F.ker := by
  ext γ
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← factorHom_spec F ρ hρ hF γ]
  constructor
  · intro h; rw [h, map_one]
  · intro h; exact hρ (by rw [h, map_one])

theorem map_inv_eq_of_eq {G : Type*} [Group G] (F : G →* M) (ρ : X →* M) {γ : G} {x : X}
    (h : F γ = ρ x) : F γ⁻¹ = ρ x⁻¹ := by
  calc F γ⁻¹ = F γ⁻¹ * (ρ x * ρ x⁻¹) := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = (F γ⁻¹ * F γ) * ρ x⁻¹ := by rw [h, mul_assoc]
    _ = ρ x⁻¹ := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]

end Factor

section Section

variable {Γ X : Type*} [Group Γ] [Group X]

theorem mem_range_of_mul_self_eq_one (lam : Γ →* X) (ψ : X →* Γ) (hψ : lam.comp ψ = MonoidHom.id X)
    (hZc : lam.ker ≤ center Γ) (hZo : Odd (Nat.card lam.ker)) {γ : Γ} (hγ : γ * γ = 1) :
    γ ∈ ψ.range := by
  have hlp : ∀ x, lam (ψ x) = x := fun x => DFunLike.congr_fun hψ x
  set a := ψ (lam γ) with ha_def
  set k := a⁻¹ * γ with hk_def
  have hk : k ∈ lam.ker := by
    rw [MonoidHom.mem_ker, hk_def, map_mul, map_inv, ha_def, hlp, inv_mul_cancel]
  have ha : a * a = 1 := by rw [ha_def, ← map_mul, ← map_mul, hγ, map_one, map_one]
  have hγ' : γ = a * k := (mul_inv_cancel_left a γ).symm
  have hka : k * a = a * k := (Subgroup.mem_center_iff.mp (hZc hk) a).symm
  have hkk : k * k = 1 := by
    calc k * k = (a * a) * (k * k) := by rw [ha, one_mul]
      _ = a * (k * a) * k := by rw [hka]; group
      _ = γ * γ := by rw [hγ']; group
      _ = 1 := hγ
  have hk1 : k = 1 := eq_of_pow_two_pow hZo hk lam.ker.one_mem 1 (by rw [pow_one, sq, hkk, one_pow])
  rw [hγ', hk1, mul_one]
  exact ⟨_, rfl⟩

theorem range_normal_of_section (lam : Γ →* X) (ψ : X →* Γ) (hψ : lam.comp ψ = MonoidHom.id X)
    (hZc : lam.ker ≤ center Γ) : ψ.range.Normal := by
  have hlp : ∀ x, lam (ψ x) = x := fun x => DFunLike.congr_fun hψ x
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨x, rfl⟩ := hn
  set b := ψ (lam g)
  set c := b⁻¹ * g with hc_def
  have hc : c ∈ lam.ker := by rw [MonoidHom.mem_ker, hc_def, map_mul, map_inv, hlp, inv_mul_cancel]
  have hg : g = b * c := (mul_inv_cancel_left b g).symm
  have hcx : c * ψ x = ψ x * c := (Subgroup.mem_center_iff.mp (hZc hc) (ψ x)).symm
  have h1 : g * ψ x * g⁻¹ = b * ψ x * b⁻¹ := by
    conv_lhs => rw [hg]
    rw [_root_.mul_inv_rev]
    calc b * c * ψ x * (c⁻¹ * b⁻¹) = b * (c * ψ x) * c⁻¹ * b⁻¹ := by group
      _ = b * ψ x * b⁻¹ := by rw [hcx]; group
  have h2 : b * ψ x * b⁻¹ = ψ (lam g * x * (lam g)⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [h1, h2]
  exact ⟨_, rfl⟩

end Section

section Rep

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def matRep (π : Γ →* (W →ₗ[ZMod 2] W)) (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) :
    Γ →* Mat16 :=
  (matHom e).comp π

theorem matRep_apply (π : Γ →* (W →ₗ[ZMod 2] W)) (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) (γ : Γ) :
    matRep π e γ = matOf e (π γ) := rfl

theorem matRep_ker (π : Γ →* (W →ₗ[ZMod 2] W)) (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) :
    (matRep π e).ker = π.ker := by
  ext γ
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, matRep_apply, ← matOf_one e]
  exact ⟨fun h => matOf_injective e h, fun h => by rw [h]⟩

end Rep

section Linear

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable {π : Γ →* (W →ₗ[ZMod 2] W)} {K : Subgroup Γ} {θ : K ≃* SU42b}
  {D : Subgroup Γ} {e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)} {z : ℕ}

@[expose] noncomputable def rhoMHom : SU42b →* Mat16 where
  toFun x := rhoM ((x : GL (Fin 8) (ZMod 2)) : Mat8)
  map_one' := by rw [OneMemClass.coe_one, Units.val_one, rhoM_one]
  map_mul' x y := by rw [Subgroup.coe_mul, Units.val_mul, rhoM_mul]

theorem toMat_dGen (z k : ℕ) (hk : k < 8) :
    toMat 16 16 (dGen z k) = 1 + embedM (candBlock z ⟨k, hk⟩) := by
  rw [dGen, toMat_bxor, toMat_id16, toMat_embed16]
  simp only [candBlock]
  split_ifs <;> rfl

theorem gens16M_lt3 (z : ℕ) (s : Fin 3) : gens16M z s = rhoM (genMat s) := by
  rw [gens16M, gens16Bits, ite_eq_left_of_eq_true _ _ (by simp [s.isLt]), Fin.ofNat_val_eq_self,
    toMat_rho16]
  rfl

theorem gens16M_ge3 (z l : ℕ) (hl : 3 ≤ l) (hl' : l < 11) :
    gens16M z l = 1 + embedM (candBlock z ⟨l - 3, by omega⟩) := by
  rw [gens16M, gens16Bits, ite_eq_right_of_eq_false _ _ (by simp; omega), toMat_dGen]

theorem exists_rhoL_eq_matRep (hz : z = 1 ∨ z = 2) (hgen : K ⊔ D = ⊤)
    (hK : ∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8))
    (hDe : ∀ d ∈ D, ∃ ψ ∈ psiZ z, matOf e (π d) = 1 + embedM ψ) (γ : Γ) :
    ∃ g, rhoL z g = matRep π e γ := by
  let S : Subgroup Γ :=
    { carrier := {γ | ∃ g, rhoL z g = matRep π e γ}
      mul_mem' := by
        rintro a b ⟨g, hg⟩ ⟨g', hg'⟩
        exact ⟨g * g', by rw [map_mul, map_mul, hg, hg']⟩
      one_mem' := ⟨1, by rw [map_one, map_one]⟩
      inv_mem' := by
        rintro a ⟨g, hg⟩
        exact ⟨g⁻¹, (map_inv_eq_of_eq (matRep π e) (rhoL z) hg.symm).symm⟩ }
  have hSU : ∀ x : SU42b, ∃ g, rhoL z g = rhoMHom x := by
    intro x
    have hx : x ∈ Subgroup.closure {genSU 0, genSU 1} := SU42b_eq_closure ▸ Subgroup.mem_top x
    refine Subgroup.closure_induction (p := fun x _ => ∃ g, rhoL z g = rhoMHom x) ?_ ?_ ?_ ?_ hx
    · rintro x (rfl | rfl)
      · exact ⟨trProdSL (lKW ((0 : Fin 3) : ℕ)), by
          rw [rhoL_lKW hz 0]; simp [rhoMHom, genSU, coe_genGL]⟩
      · exact ⟨trProdSL (lKW ((1 : Fin 3) : ℕ)), by
          rw [rhoL_lKW hz 1]; simp [rhoMHom, genSU, coe_genGL]⟩
    · exact ⟨1, by rw [map_one, map_one]⟩
    · rintro a b _ _ ⟨g, hg⟩ ⟨g', hg'⟩
      exact ⟨g * g', by rw [map_mul, map_mul, hg, hg']⟩
    · rintro a _ ⟨g, hg⟩
      exact ⟨g⁻¹, (map_inv_eq_of_eq rhoMHom (rhoL z) hg.symm).symm⟩
  have hpsi : ∀ ψ ∈ psiZ z, ∃ g, rhoL z g = 1 + embedM ψ := by
    intro ψ hψ
    refine Submodule.span_induction (p := fun ψ _ => ∃ g, rhoL z g = 1 + embedM ψ) ?_ ?_ ?_ ?_ hψ
    · rintro _ ⟨c, rfl⟩
      exact ⟨trProdSL (lDW z c), by rw [rhoL_lDW hz c.isLt, toMat_dGen z c c.isLt]⟩
    · exact ⟨1, by rw [map_one, embedM_zero, add_zero]⟩
    · rintro x y _ _ ⟨g, hg⟩ ⟨g', hg'⟩
      exact ⟨g * g', by rw [map_mul, hg, hg', one_add_embedM_mul]⟩
    · intro a x _ hx
      rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a with rfl | rfl
      · exact ⟨1, by rw [map_one, zero_smul, embedM_zero, add_zero]⟩
      · rwa [one_smul]
  have hKS : K ≤ S := by
    intro k hk
    obtain ⟨g, hg⟩ := hSU (θ ⟨k, hk⟩)
    refine ⟨g, ?_⟩
    rw [hg, matRep_apply]
    exact (hK ⟨k, hk⟩).symm
  have hDS : D ≤ S := by
    intro d hd
    obtain ⟨ψ, hψ, hdψ⟩ := hDe d hd
    obtain ⟨g, hg⟩ := hpsi ψ hψ
    exact ⟨g, by rw [hg, matRep_apply, hdψ]⟩
  have : S = ⊤ := eq_top_iff.mpr (hgen ▸ sup_le hKS hDS)
  exact (this ▸ Subgroup.mem_top γ : γ ∈ S)

theorem exists_matRep_eq_gens16M
    (hK : ∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8))
    (hDe' : ∀ ψ ∈ psiZ z, ∃ d ∈ D, matOf e (π d) = 1 + embedM ψ) {l : ℕ} (hl : l < 11) :
    ∃ γ, matRep π e γ = gens16M z l := by
  by_cases h3 : l < 3
  · refine ⟨θ.symm (genSU ⟨l, h3⟩), ?_⟩
    have h1 := gens16M_lt3 z ⟨l, h3⟩
    rw [show (((⟨l, h3⟩ : Fin 3) : ℕ)) = l from rfl] at h1
    rw [matRep_apply, hK, MulEquiv.apply_symm_apply, h1]
    simp [genSU, coe_genGL]
  · obtain ⟨d, -, hd⟩ := hDe' (candBlock z ⟨l - 3, by omega⟩) (Submodule.subset_span ⟨_, rfl⟩)
    exact ⟨d, by rw [matRep_apply, hd, gens16M_ge3 z l (by omega) hl]⟩

theorem exists_matRep_eq_rhoL (hz : z = 1 ∨ z = 2)
    (hK : ∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8))
    (hDe' : ∀ ψ ∈ psiZ z, ∃ d ∈ D, matOf e (π d) = 1 + embedM ψ) (g : SL4) :
    ∃ γ, matRep π e γ = rhoL z g := by
  have hg : g ∈ Subgroup.closure (Set.range fun p : Fin 4 × Fin 4 × F4 => st4 p.1 p.2.1 p.2.2) :=
    closure_stT (F := F4) (m := 3) (by norm_num) ▸ Subgroup.mem_top g
  refine Subgroup.closure_induction (p := fun g _ => ∃ γ, matRep π e γ = rhoL z g) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨⟨a, b, c⟩, rfl⟩
    obtain ⟨w, hwl, hw⟩ := exists_word_rhoL_st4 hz a b c
    have hgen : ∀ l ∈ w, ∃ γ, matRep π e γ = gens16M z l := fun l hl =>
      exists_matRep_eq_gens16M hK hDe' (hwl l hl)
    change ∃ γ, matRep π e γ = rhoL z (st4 a b c)
    rw [hw]
    clear hw hwl
    induction w with
    | nil => exact ⟨1, by rw [map_one]; rfl⟩
    | cons l w ih =>
      obtain ⟨γ, hγ⟩ := hgen l (by simp)
      obtain ⟨γ', hγ'⟩ := ih fun l' hl' => hgen l' (by simp [hl'])
      exact ⟨γ * γ', by rw [map_mul, hγ, hγ', List.map_cons, List.prod_cons]⟩
  · exact ⟨1, by rw [map_one, map_one]⟩
  · rintro x y _ _ ⟨γ, hγ⟩ ⟨γ', hγ'⟩
    exact ⟨γ * γ', by rw [map_mul, map_mul, hγ, hγ']⟩
  · rintro x _ ⟨γ, hγ⟩
    exact ⟨γ⁻¹, map_inv_eq_of_eq (matRep π e) (rhoL z) hγ⟩

end Linear

section Main

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable {π : Γ →* (W →ₗ[ZMod 2] W)} {K : Subgroup Γ} {θ : K ≃* SU42b} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 8 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2}
  {τ : Γ →* Γ} {e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)} {z : ℕ}

theorem K_le_of_normal (N : Subgroup Γ) [N.Normal]
    (hE : ∀ m < 4, ((θ.symm (eSU m) : K) : Γ) ∈ N) : K ≤ N := by
  set N' : Subgroup SU42b := (N.subgroupOf K).map θ.toMonoidHom
  have hN : N'.Normal := (Subgroup.normal_subgroupOf).map _ θ.surjective
  have hE' : E16 ≤ N' := by
    rw [E16, Subgroup.closure_le]
    rintro _ ⟨m, rfl⟩
    exact ⟨θ.symm (eSU m), Subgroup.mem_subgroupOf.mpr (hE m m.isLt), by simp⟩
  have htop := SU42b_eq_top_of_normal N' hE'
  intro k hk
  have hmem : θ ⟨k, hk⟩ ∈ N' := htop ▸ Subgroup.mem_top _
  obtain ⟨k', hk', hkk'⟩ := hmem
  have : k' = ⟨k, hk⟩ := θ.injective hkk'
  subst this
  exact Subgroup.mem_subgroupOf.mp hk'

theorem matOf_π_τ (h : R3Hyp π K θ τW ι D B τ) (he : matOf e τW = tM16) (γ : Γ) :
    matOf e (π (τ γ)) = tM16 * matOf e (π γ) * tM16 := by
  rw [h.πτ, matOf_comp, matOf_comp, he, mul_assoc]

theorem R3Hyp.exists_equiv_SL4 [Finite Γ]
    (h : R3Hyp π K θ τW ι D B τ) (he : matOf e τW = tM16) (hz : z = 1 ∨ z = 2)
    (hK : ∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8))
    (hDe : ∀ d ∈ D, ∃ ψ ∈ psiZ z, matOf e (π d) = 1 + embedM ψ)
    (hDe' : ∀ ψ ∈ psiZ z, ∃ d ∈ D, matOf e (π d) = 1 + embedM ψ) :
    ∃ ψ : SL4 ≃* Γ, (∀ g, matOf e (π (ψ g)) = rhoL z g) ∧ ∀ g, τ (ψ g) = ψ (sigmaSL g) := by
  have hz4 : z < 4 := by rcases hz with rfl | rfl <;> norm_num
  have hF := exists_rhoL_eq_matRep (K := K) (θ := θ) (D := D) hz h.gen hK hDe
  set lam := factorHom (matRep π e) (rhoL z) (rhoL_injective z) hF with hlam
  have hsurj : Function.Surjective lam :=
    factorHom_surjective _ _ _ hF (exists_matRep_eq_rhoL hz hK hDe')
  have hker : lam.ker = π.ker := (factorHom_ker _ _ _ hF).trans (matRep_ker π e)
  have hZc : lam.ker ≤ center Γ := hker ▸ h.ker_le_center he hz4 hK hDe hDe'
  have hZo : Odd (Nat.card lam.ker) := hker ▸ h.odd_card_ker he
  obtain ⟨ψ, hψ⟩ := exists_hom_comp_eq_of_odd_center (F := F4) (m := 3) (by norm_num) lam hZc hZo
    (MonoidHom.id SL4) (fun _ _ _ _ => hsurj _)
  have hlp : ∀ g, lam (ψ g) = g := fun g => DFunLike.congr_fun hψ g
  have hinj : Function.Injective ψ := fun g g' hgg' => by rw [← hlp g, hgg', hlp]
  have hnorm := range_normal_of_section lam ψ hψ hZc
  have hinv : ∀ γ, γ * γ = 1 → γ ∈ ψ.range := fun γ hγ =>
    mem_range_of_mul_self_eq_one lam ψ hψ hZc hZo hγ
  have hDr : D ≤ ψ.range := fun d hd => hinv d (h.D_mul_self hDe hd)
  have hKr : K ≤ ψ.range := K_le_of_normal ψ.range fun m hm => hDr (h.E_le m hm)
  have htop : ψ.range = ⊤ := eq_top_iff.mpr (h.gen ▸ sup_le hKr hDr)
  have hsurjψ : Function.Surjective ψ := MonoidHom.range_eq_top.mp htop
  refine ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurjψ⟩, fun g => ?_, fun g => ?_⟩
  · show matOf e (π (ψ g)) = rhoL z g
    rw [← matRep_apply, ← factorHom_spec (matRep π e) (rhoL z) (rhoL_injective z) hF, ← hlam, hlp]
  · show τ (ψ g) = ψ (sigmaSL g)
    have hτ : lam (τ (ψ g)) = sigmaSL g := by
      apply rhoL_injective z
      rw [hlam, factorHom_spec, matRep_apply, matOf_π_τ h he, ← matRep_apply, ← factorHom_spec
        (matRep π e) (rhoL z) (rhoL_injective z) hF, ← hlam, hlp, tM16_rhoL hz]
    obtain ⟨g', hg'⟩ := hsurjψ (τ (ψ g))
    rw [← hg', hlp] at hτ
    rw [← hg', hτ]

end Main

end CFSG.EvenSmallLie.UnitarySix.YamadaPar

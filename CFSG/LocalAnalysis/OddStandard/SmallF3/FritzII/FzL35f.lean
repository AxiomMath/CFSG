module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL21bC

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private abbrev fzlPt (t x₁ x₂ : G) : Type :=
  {w : G // ∃ z ∈ fourGrp x₁ x₂, w = t * z}

private lemma fzlPt_val_mem_W (h : Ctx t L S x₁ x₂ lam rho tau) (y : fzlPt t x₁ x₂) :
    y.1 ∈ ctxW t x₁ x₂ := by
  obtain ⟨z, hz, hw⟩ := y.2
  rw [hw]
  exact (ctxW t x₁ x₂).mul_mem (fzl_t_facts h).1 (fzl_Z_le_W h hz)

private lemma fzl_W_comm (h : Ctx t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ ctxW t x₁ x₂) (hb : b ∈ ctxW t x₁ x₂) : a * b = b * a := by
  have hc := h.abelian_W.is_comm.comm (⟨a, ha⟩ : ↥(ctxW t x₁ x₂)) ⟨b, hb⟩
  simpa using congrArg Subtype.val hc

private lemma fzlPt_conj_mem (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {n : G} (hn : n ∈ fzN2 t x₁ x₂) {w : G} (hw : ∃ z ∈ fourGrp x₁ x₂, w = t * z) :
    ∃ z ∈ fourGrp x₁ x₂, n * w * n⁻¹ = t * z := by
  obtain ⟨z, hz, hw'⟩ := hw
  obtain ⟨z₀, hz₀, hz₀'⟩ := fzl_conj_t h hK hn
  have hzn : n * z * n⁻¹ ∈ fourGrp x₁ x₂ := fzl_conj_Z h hK hn hz
  refine ⟨z₀ * (n * z * n⁻¹), (fourGrp x₁ x₂).mul_mem hz₀ hzn, ?_⟩
  have hconj : n * (t * z) * n⁻¹ = (n * t * n⁻¹) * (n * z * n⁻¹) := by group
  rw [hw', hconj, hz₀']
  group

@[instance_reducible]
private noncomputable def fzlPtMulAction (h : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 2) :
    MulAction ↥(fzN2 t x₁ x₂) (fzlPt t x₁ x₂) where
  smul n w := ⟨(n : G) * w.1 * (n : G)⁻¹, fzlPt_conj_mem h hK n.2 w.2⟩
  one_smul w := by
    apply Subtype.ext
    change (1 : G) * w.1 * (1 : G)⁻¹ = w.1
    simp
  mul_smul n m w := by
    apply Subtype.ext
    change ((n * m : ↥(fzN2 t x₁ x₂)) : G) * w.1 * ((n * m : ↥(fzN2 t x₁ x₂)) : G)⁻¹ =
      (n : G) * ((m : G) * w.1 * (m : G)⁻¹) * (n : G)⁻¹
    rw [Subgroup.coe_mul]
    group

private noncomputable def fzlPtEquiv (h : Ctx t L S x₁ x₂ lam rho tau) :
    fzlPt t x₁ x₂ ≃ ↥(fourGrp x₁ x₂) where
  toFun w := ⟨t * w.1, by
    obtain ⟨z, hz, hw⟩ := w.2
    have ht2 : t * t = 1 := by rw [← pow_two]; exact (fzl_t_facts h).2.1
    rw [hw, ← mul_assoc, ht2, one_mul]
    exact hz⟩
  invFun z := ⟨t * z.1, ⟨z.1, z.2, rfl⟩⟩
  left_inv w := by
    apply Subtype.ext
    obtain ⟨z, hz, hw⟩ := w.2
    have ht2 : t * t = 1 := by rw [← pow_two]; exact (fzl_t_facts h).2.1
    change t * (t * w.1) = w.1
    rw [hw]
    change t * (t * (t * z)) = t * z
    rw [← mul_assoc, ht2, one_mul]
  right_inv z := by
    apply Subtype.ext
    have ht2 : t * t = 1 := by rw [← pow_two]; exact (fzl_t_facts h).2.1
    change t * (t * z.1) = z.1
    rw [← mul_assoc, ht2, one_mul]

theorem fzl_35b :
    Fz35b := by
  classical
  intro G _ _ _ t L S x₁ x₂ lam rho tau hr4 hctx hK
  letI : CommGroup ↥(ctxW t x₁ x₂) :=
    { (inferInstance : Group ↥(ctxW t x₁ x₂)) with
      mul_comm := fun a b => hctx.abelian_W.is_comm.comm a b }
  let φ : ↥(fzN2 t x₁ x₂) →* MulAut ↥(ctxW t x₁ x₂) :=
    Subgroup.normalizerMonoidHom (H := ctxW t x₁ x₂)
  have hφker : φ.ker = (ctxW t x₁ x₂).subgroupOf (fzN2 t x₁ x₂) := by
    show (Subgroup.normalizerMonoidHom (H := ctxW t x₁ x₂)).ker =
      (ctxW t x₁ x₂).subgroupOf (fzN2 t x₁ x₂)
    rw [Subgroup.normalizerMonoidHom_ker, hctx.cent_W]
    rfl
  letI : MulAction ↥(fzN2 t x₁ x₂) (fzlPt t x₁ x₂) := fzlPtMulAction hctx hK
  let pt0 : fzlPt t x₁ x₂ := ⟨t, ⟨1, one_mem _, by rw [mul_one]⟩⟩
  letI : Fintype (fzlPt t x₁ x₂) := Fintype.ofFinite _
  have hcardPt : Fintype.card (fzlPt t x₁ x₂) = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (fzlPtEquiv hctx), fzl_card_Z hctx]
  let e0 : fzlPt t x₁ x₂ ≃ Fin 4 := Fintype.equivFinOfCardEq hcardPt
  let e : fzlPt t x₁ x₂ ≃ Fin 4 := e0.trans (Equiv.swap (e0 pt0) 0)
  have he0 : e pt0 = 0 := by
    dsimp [e]
    exact Equiv.swap_apply_left _ _
  have he_symm0 : e.symm 0 = pt0 := by rw [← he0, Equiv.symm_apply_apply]
  let ψ : ↥(fzN2 t x₁ x₂) →* Equiv.Perm (Fin 4) :=
    e.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom ↥(fzN2 t x₁ x₂) (fzlPt t x₁ x₂))
  have hψ_apply : ∀ (n : ↥(fzN2 t x₁ x₂)) (x : Fin 4), ψ n x = e (n • e.symm x) :=
    fun _ _ => rfl
  have hz1mem : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hz1ne : x₁ ^ 2 ≠ 1 := (fzl_z1_ne_z2 hctx).2.1
  let ptz₁ : fzlPt t x₁ x₂ := ⟨t * x₁ ^ 2, ⟨x₁ ^ 2, hz1mem, rfl⟩⟩
  let ρN : ↥(fzN2 t x₁ x₂) := ⟨rho, (fzl_rho_Z hctx).1⟩
  let lamN : ↥(fzN2 t x₁ x₂) := ⟨lam, (fzl_lam_Z hctx).1⟩
  let tauN : ↥(fzN2 t x₁ x₂) := ⟨tau, (fzl_tau_facts hctx hK).1⟩
  have hker_of_fixes : ∀ {n : G} (hn : n ∈ fzN2 t x₁ x₂), n * t * n⁻¹ = t →
      (∀ z ∈ fourGrp x₁ x₂, n * z * n⁻¹ = z) →
      (⟨n, hn⟩ : ↥(fzN2 t x₁ x₂)) ∈ ψ.ker := by
    intro n hn htn hz
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro x
    rw [hψ_apply]
    have hy : (⟨n, hn⟩ : ↥(fzN2 t x₁ x₂)) • e.symm x = e.symm x := by
      apply Subtype.ext
      obtain ⟨z, hz', hwz⟩ := (e.symm x).2
      show n * (e.symm x).1 * n⁻¹ = (e.symm x).1
      rw [hwz]
      have hconj : n * (t * z) * n⁻¹ = (n * t * n⁻¹) * (n * z * n⁻¹) := by group
      rw [hconj, htn, hz z hz']
    rw [hy, Equiv.apply_symm_apply]
    rfl
  have hφψ : φ.ker ≤ ψ.ker := by
    intro k hk
    rw [hφker] at hk
    have hkW : (k : G) ∈ ctxW t x₁ x₂ := by
      have := Subgroup.mem_subgroupOf.mp hk
      simpa using this
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro x
    rw [hψ_apply]
    have hy : k • e.symm x = e.symm x := by
      apply Subtype.ext
      show (k : G) * (e.symm x).1 * (k : G)⁻¹ = (e.symm x).1
      rw [fzl_W_comm hctx hkW (fzlPt_val_mem_W hctx (e.symm x))]
      group
    rw [hy, Equiv.apply_symm_apply]
    rfl
  have htrans : ∀ i : Fin 4, ∃ h ∈ ψ.range, h 0 = i := by
    intro i
    let w : fzlPt t x₁ x₂ := e.symm i
    obtain ⟨z, hz, hwz⟩ := w.2
    obtain ⟨n, hn, hnt⟩ := fzl_exists_swap hctx hK hz
    refine ⟨ψ ⟨n, hn⟩, MonoidHom.mem_range.mpr ⟨⟨n, hn⟩, rfl⟩, ?_⟩
    rw [hψ_apply, he_symm0]
    have hpt : (⟨n, hn⟩ : ↥(fzN2 t x₁ x₂)) • pt0 = w := by
      apply Subtype.ext
      show n * t * n⁻¹ = w.1
      rw [hnt, hwz]
    rw [hpt]
    exact Equiv.apply_symm_apply e i
  have hψtop : ψ.range = ⊤ := by
    refine fzl_perm4_eq_top ψ.range htrans (a := ψ ρN) (b := ψ lamN)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact MonoidHom.mem_range.mpr ⟨ρN, rfl⟩
    · exact MonoidHom.mem_range.mpr ⟨lamN, rfl⟩
    · rw [hψ_apply, he_symm0]
      have hpt : ρN • pt0 = pt0 := by
        apply Subtype.ext
        show rho * t * rho⁻¹ = t
        exact (fzl_rho_Z hctx).2.1
      rw [hpt, he0]
    · rw [hψ_apply, he_symm0]
      have hpt : lamN • pt0 = pt0 := by
        apply Subtype.ext
        show lam * t * lam⁻¹ = t
        exact (fzl_lam_Z hctx).2.1
      rw [hpt, he0]
    · rw [← map_pow]
      have h3 : ρN ^ 3 = 1 := by
        apply Subtype.ext
        show rho ^ 3 = ((1 : ↥(fzN2 t x₁ x₂)) : G)
        rw [(fzl_rho_Z hctx).2.2.1]
        rfl
      rw [h3, map_one]
    · intro h1
      have hfix : ρN • ptz₁ = ptz₁ := by
        have h' : ψ ρN (e ptz₁) = e ptz₁ := by rw [h1]; rfl
        rw [hψ_apply, Equiv.symm_apply_apply] at h'
        exact e.injective h'
      have hval : rho * (t * x₁ ^ 2) * rho⁻¹ = t * x₁ ^ 2 := by
        have h := congrArg Subtype.val hfix
        change rho * (t * x₁ ^ 2) * rho⁻¹ = t * x₁ ^ 2 at h
        exact h
      have h2 : rho * (t * x₁ ^ 2) * rho⁻¹ =
          (rho * t * rho⁻¹) * (rho * x₁ ^ 2 * rho⁻¹) := by group
      rw [h2, (fzl_rho_Z hctx).2.1] at hval
      have hzx : rho * x₁ ^ 2 * rho⁻¹ = x₁ ^ 2 := mul_left_cancel hval
      exact (fzl_rho_Z hctx).2.2.2 (x₁ ^ 2) hz1mem hz1ne hzx
    · rw [← map_pow]
      have h2 : lamN ^ 2 = 1 := by
        apply Subtype.ext
        show lam ^ 2 = ((1 : ↥(fzN2 t x₁ x₂)) : G)
        rw [(fzl_lam_Z hctx).2.2.1]
        rfl
      rw [h2, map_one]
    · intro h1
      have hfix : lamN • ptz₁ = ptz₁ := by
        have h' : ψ lamN (e ptz₁) = e ptz₁ := by rw [h1]; rfl
        rw [hψ_apply, Equiv.symm_apply_apply] at h'
        exact e.injective h'
      have hval : lam * (t * x₁ ^ 2) * lam⁻¹ = t * x₁ ^ 2 := by
        have h := congrArg Subtype.val hfix
        change lam * (t * x₁ ^ 2) * lam⁻¹ = t * x₁ ^ 2 at h
        exact h
      have h2 : lam * (t * x₁ ^ 2) * lam⁻¹ =
          (lam * t * lam⁻¹) * (lam * x₁ ^ 2 * lam⁻¹) := by group
      rw [h2, (fzl_lam_Z hctx).2.1] at hval
      have hzx : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := mul_left_cancel hval
      rw [(fzl_lam_Z hctx).2.2.2.1] at hzx
      exact (fzl_z1_ne_z2 hctx).1 hzx.symm
    · rw [← map_mul, ← map_inv, ← map_mul, ← map_inv]
      congr 1
      apply Subtype.ext
      simpa using (fzl_lam_rho hctx).1
  have hψ : Function.Surjective ψ := by
    intro y
    have hy : y ∈ ψ.range := by rw [hψtop]; exact Subgroup.mem_top y
    exact MonoidHom.mem_range.mp hy
  have hK_act : ∀ k ∈ ψ.ker, (∀ x : ↥(ctxW t x₁ x₂), φ k x = x) ∨
      (∀ x : ↥(ctxW t x₁ x₂), φ k x = x⁻¹) := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hkt : (k : G) * t * (k : G)⁻¹ = t := by
      have h0 : ψ k 0 = 0 := by rw [hk]; rfl
      rw [hψ_apply, he_symm0, ← he0] at h0
      have h1 := congrArg Subtype.val (e.injective h0)
      change (k : G) * t * (k : G)⁻¹ = t at h1
      exact h1
    have hkZ : ∀ z ∈ fourGrp x₁ x₂, (k : G) * z * (k : G)⁻¹ = z := by
      intro z hz
      let ptz : fzlPt t x₁ x₂ := ⟨t * z, ⟨z, hz, rfl⟩⟩
      have hptz : k • ptz = ptz := by
        have h' : ψ k (e ptz) = e ptz := by rw [hk]; rfl
        rw [hψ_apply, Equiv.symm_apply_apply] at h'
        exact e.injective h'
      have hval : (k : G) * (t * z) * (k : G)⁻¹ = t * z := by
        have h := congrArg Subtype.val hptz
        change (k : G) * (t * z) * (k : G)⁻¹ = t * z at h
        exact h
      have h2 : (k : G) * (t * z) * (k : G)⁻¹ =
          ((k : G) * t * (k : G)⁻¹) * ((k : G) * z * (k : G)⁻¹) := by group
      rw [h2, hkt] at hval
      exact mul_left_cancel hval
    have hact := (fzl_Wtau_act hctx hK (fzl_ker_le hctx hK k.2 hkt hkZ)).2.2.2
    rcases hact with ha | ha
    · left; intro x; apply Subtype.ext; exact ha x.1 x.2
    · right; intro x; apply Subtype.ext; exact ha x.1 x.2
  have hι : ∃ k ∈ ψ.ker, ∀ x : ↥(ctxW t x₁ x₂), φ k x = x⁻¹ := by
    refine ⟨tauN, ?_, ?_⟩
    · exact hker_of_fixes tauN.2 (fzl_tau_facts hctx hK).2.1 (fzl_tau_facts hctx hK).2.2.1
    · intro x
      apply Subtype.ext
      exact (fzl_tau_facts hctx hK).2.2.2 x.1 x.2
  have hρ3 : ρN ^ 3 ∈ φ.ker := by
    have h3 : ρN ^ 3 = 1 := by
      apply Subtype.ext
      show rho ^ 3 = ((1 : ↥(fzN2 t x₁ x₂)) : G)
      rw [(fzl_rho_Z hctx).2.2.1]
      rfl
    rw [h3]; exact φ.ker.one_mem
  have hρ1 : ρN ∉ φ.ker := by
    rw [hφker]
    intro hmem
    have hrhoW : (rho : G) ∈ ctxW t x₁ x₂ := by
      have := Subgroup.mem_subgroupOf.mp hmem
      simpa using this
    have hcomm := fzl_W_comm hctx hrhoW (fzl_Z_le_W hctx hz1mem)
    have hz : rho * x₁ ^ 2 * rho⁻¹ = x₁ ^ 2 := by rw [hcomm]; group
    exact (fzl_rho_Z hctx).2.2.2 (x₁ ^ 2) hz1mem hz1ne hz
  have hlam2 : lamN ^ 2 ∈ φ.ker := by
    have h2 : lamN ^ 2 = 1 := by
      apply Subtype.ext
      show lam ^ 2 = ((1 : ↥(fzN2 t x₁ x₂)) : G)
      rw [(fzl_lam_Z hctx).2.2.1]
      rfl
    rw [h2]; exact φ.ker.one_mem
  have hlam1 : lamN ∉ φ.ker := by
    rw [hφker]
    intro hmem
    have hlamW : (lam : G) ∈ ctxW t x₁ x₂ := by
      have := Subgroup.mem_subgroupOf.mp hmem
      simpa using this
    have hcomm := fzl_W_comm hctx hlamW (fzl_Z_le_W hctx hz1mem)
    have hz : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by rw [hcomm]; group
    rw [(fzl_lam_Z hctx).2.2.2.1] at hz
    exact (fzl_z1_ne_z2 hctx).1 hz.symm
  have hlr : lamN * ρN * lamN⁻¹ * ρN ∈ φ.ker := by
    have h1 : lamN * ρN * lamN⁻¹ * ρN = 1 := by
      apply Subtype.ext
      show lam * rho * lam⁻¹ * rho = ((1 : ↥(fzN2 t x₁ x₂)) : G)
      rw [(fzl_lam_rho hctx).1]
      rw [inv_mul_cancel, Subgroup.coe_one]
    rw [h1]; exact φ.ker.one_mem
  obtain ⟨f, hf, hfker⟩ :=
    fzl_assemble fzl_21b φ (fzl_W_equiv hctx hK) ψ hψ hφψ hK_act hι
      (ρ := ρN) (lam := lamN) hρ3 hρ1 hlam2 hlam1 hlr
  exact ⟨f, hf, by rw [hfker, hφker]⟩

end CFSG.OddStandard.SmallF3.FritzII

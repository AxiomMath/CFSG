module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL21bC

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma fzbs_mem_normalizer_of_conj_mem_aux {H : Subgroup G} {g : G}
    (h : ∀ y ∈ H, g * y * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    show g * y * g⁻¹ ∈ H
    exact h y hy
  · exact le_of_eq (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).symm

private abbrev fzbsPt (t x₁ x₂ : G) : Type :=
  {w : G // ∃ z ∈ fourGrp x₁ x₂, w = t * z}

private lemma fzbsPt_val_mem_X (h : Ctx t L S x₁ x₂ lam rho tau) (y : fzbsPt t x₁ x₂) :
    y.1 ∈ fzbsX t x₁ x₂ := by
  obtain ⟨z, hz, hw⟩ := y.2
  rw [hw]
  exact (fzbsX t x₁ x₂).mul_mem (fzbs_X_le h).1
    ((fzbs_X_le h).2.2.1 (S4A.pt_four_le_base x₁ x₂ hz))

private lemma fzbs_W_comm (h : Ctx t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ ctxW t x₁ x₂) (hb : b ∈ ctxW t x₁ x₂) : a * b = b * a := by
  have hc := h.abelian_W.is_comm.comm (⟨a, ha⟩ : ↥(ctxW t x₁ x₂)) ⟨b, hb⟩
  simpa using congrArg Subtype.val hc

private lemma fzbsPt_conj_mem (h : Ctx t L S x₁ x₂ lam rho tau)
    [IsSimpleGroup G]
    {n : G} (hn : n ∈ fzN2 t x₁ x₂) {w : G} (hw : ∃ z ∈ fourGrp x₁ x₂, w = t * z) :
    ∃ z ∈ fourGrp x₁ x₂, n * w * n⁻¹ = t * z := by
  obtain ⟨z, hz, hw'⟩ := hw
  obtain ⟨z₀, hz₀, hz₀'⟩ := fzbs_conj_t h hn
  have hzn : n * z * n⁻¹ ∈ fourGrp x₁ x₂ := fzbs_conj_Z h hn hz
  refine ⟨z₀ * (n * z * n⁻¹), (fourGrp x₁ x₂).mul_mem hz₀ hzn, ?_⟩
  have hconj : n * (t * z) * n⁻¹ = (n * t * n⁻¹) * (n * z * n⁻¹) := by group
  rw [hw', hconj, hz₀']
  group

@[instance_reducible]
private noncomputable def fzbsPtMulAction (h : Ctx t L S x₁ x₂ lam rho tau)
    [IsSimpleGroup G] :
    MulAction ↥(fzN2 t x₁ x₂) (fzbsPt t x₁ x₂) where
  smul n w := ⟨(n : G) * w.1 * (n : G)⁻¹, fzbsPt_conj_mem h n.2 w.2⟩
  one_smul w := Subtype.ext (by
    change (1 : G) * w.1 * (1 : G)⁻¹ = w.1
    simp)
  mul_smul n m w := Subtype.ext (by
    change ((n * m : ↥(fzN2 t x₁ x₂)) : G) * w.1 *
      ((n * m : ↥(fzN2 t x₁ x₂)) : G)⁻¹ =
      (n : G) * ((m : G) * w.1 * (m : G)⁻¹) * (n : G)⁻¹
    rw [Subgroup.coe_mul]
    group)

private noncomputable def fzbsPtEquiv (h : Ctx t L S x₁ x₂ lam rho tau) :
    fzbsPt t x₁ x₂ ≃ ↥(fourGrp x₁ x₂) :=
  let ht2 : t * t = 1 := by rw [← pow_two]; exact (fzl_t_facts h).2.1
  { toFun := fun w => ⟨t * w.1, by
      obtain ⟨z, hz, hw⟩ := w.2
      rw [hw, ← mul_assoc, ht2, one_mul]
      exact hz⟩
    invFun := fun z => ⟨t * z.1, ⟨z.1, z.2, rfl⟩⟩
    left_inv := fun w => Subtype.ext (by
      obtain ⟨z, hz, hw⟩ := w.2
      change t * (t * w.1) = w.1
      rw [hw]
      change t * (t * (t * z)) = t * z
      rw [← mul_assoc, ht2, one_mul])
    right_inv := fun z => Subtype.ext (by
      change t * (t * z.1) = z.1
      rw [← mul_assoc, ht2, one_mul]) }

theorem fzbs_N2
    [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∃ f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4, FzF t x₁ x₂ f := by
  classical
  letI : CommGroup ↥(fzbsX t x₁ x₂) :=
    { (inferInstance : Group ↥(fzbsX t x₁ x₂)) with
      mul_comm := fun a b => Subtype.ext (fzbs_X_comm h a.2 b.2) }
  have hle : fzN2 t x₁ x₂ ≤ Subgroup.normalizer ((fzbsX t x₁ x₂ : Subgroup G) : Set G) :=
    fun n hn => fzbs_mem_normalizer_of_conj_mem_aux (fun y hy => fzbs_conj_X h hn hy)
  let φ : ↥(fzN2 t x₁ x₂) →* MulAut ↥(fzbsX t x₁ x₂) :=
    (Subgroup.normalizerMonoidHom (H := fzbsX t x₁ x₂)).comp (Subgroup.inclusion hle)
  have hφ_apply : ∀ (k : ↥(fzN2 t x₁ x₂)) (x : ↥(fzbsX t x₁ x₂)),
      ((φ k x : ↥(fzbsX t x₁ x₂)) : G) = (k : G) * x * (k : G)⁻¹ := fun k x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe (fzbsX t x₁ x₂)
      (Subgroup.inclusion hle k) x
  have hφker : φ.ker = (ctxW t x₁ x₂).subgroupOf (fzN2 t x₁ x₂) := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      apply fzbs_cent_X h
      intro x hx
      have h2 := congrArg (fun y : ↥(fzbsX t x₁ x₂) => (y : G))
        (congrArg (fun f : MulAut ↥(fzbsX t x₁ x₂) => f ⟨x, hx⟩) hk)
      rw [hφ_apply k ⟨x, hx⟩] at h2
      simpa using h2
    · intro hk
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [hφ_apply k x]
      have hxW : (x : G) ∈ ctxW t x₁ x₂ := (fzbs_X_le h).2.2.2 x.2
      have hcomm : (k : G) * (x : G) = (x : G) * (k : G) :=
        congrArg Subtype.val (isMulCommutative_iff.mp h.abelian_W ⟨k, hk⟩ ⟨x, hxW⟩)
      rw [hcomm]
      group
      simp
  letI : MulAction ↥(fzN2 t x₁ x₂) (fzbsPt t x₁ x₂) := fzbsPtMulAction h
  let pt0 : fzbsPt t x₁ x₂ := ⟨t, ⟨1, one_mem _, by rw [mul_one]⟩⟩
  letI : Fintype (fzbsPt t x₁ x₂) := Fintype.ofFinite _
  have hcardPt : Fintype.card (fzbsPt t x₁ x₂) = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (fzbsPtEquiv h), fzl_card_Z h]
  let e0 : fzbsPt t x₁ x₂ ≃ Fin 4 := Fintype.equivFinOfCardEq hcardPt
  let e : fzbsPt t x₁ x₂ ≃ Fin 4 := e0.trans (Equiv.swap (e0 pt0) 0)
  have he0 : e pt0 = 0 := Equiv.swap_apply_left _ _
  have he_symm0 : e.symm 0 = pt0 := by rw [← he0, Equiv.symm_apply_apply]
  let ψ : ↥(fzN2 t x₁ x₂) →* Equiv.Perm (Fin 4) :=
    e.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom ↥(fzN2 t x₁ x₂) (fzbsPt t x₁ x₂))
  have hψ_apply : ∀ (n : ↥(fzN2 t x₁ x₂)) (x : Fin 4), ψ n x = e (n • e.symm x) :=
    fun _ _ => rfl
  have hz1mem : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hz1ne : x₁ ^ 2 ≠ 1 := (fzl_z1_ne_z2 h).2.1
  let ptz₁ : fzbsPt t x₁ x₂ := ⟨t * x₁ ^ 2, ⟨x₁ ^ 2, hz1mem, rfl⟩⟩
  let ρN : ↥(fzN2 t x₁ x₂) := ⟨rho, (fzl_rho_Z h).1⟩
  let lamN : ↥(fzN2 t x₁ x₂) := ⟨lam, (fzl_lam_Z h).1⟩
  let tauN : ↥(fzN2 t x₁ x₂) := ⟨tau, (fzbs_tau_facts h).1⟩
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
    have hkW : (k : G) ∈ ctxW t x₁ x₂ := Subgroup.mem_subgroupOf.mp hk
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro x
    rw [hψ_apply]
    have hy : k • e.symm x = e.symm x := by
      apply Subtype.ext
      show (k : G) * (e.symm x).1 * (k : G)⁻¹ = (e.symm x).1
      rw [fzbs_W_comm h hkW ((fzbs_X_le h).2.2.2 (fzbsPt_val_mem_X h (e.symm x)))]
      group
    rw [hy, Equiv.apply_symm_apply]
    rfl
  have htrans : ∀ i : Fin 4, ∃ h ∈ ψ.range, h 0 = i := by
    intro i
    let w : fzbsPt t x₁ x₂ := e.symm i
    obtain ⟨z, hz, hwz⟩ := w.2
    obtain ⟨n, hn, hnt⟩ := fzbs_exists_swap h hz
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
        exact (fzl_rho_Z h).2.1
      rw [hpt, he0]
    · rw [hψ_apply, he_symm0]
      have hpt : lamN • pt0 = pt0 := by
        apply Subtype.ext
        show lam * t * lam⁻¹ = t
        exact (fzl_lam_Z h).2.1
      rw [hpt, he0]
    · rw [← map_pow]
      have h3 : ρN ^ 3 = 1 := by
        apply Subtype.ext
        show rho ^ 3 = ((1 : ↥(fzN2 t x₁ x₂)) : G)
        rw [(fzl_rho_Z h).2.2.1]
        rfl
      rw [h3, map_one]
    · intro h1
      have hfix : ρN • ptz₁ = ptz₁ := by
        have h' : ψ ρN (e ptz₁) = e ptz₁ := by rw [h1]; rfl
        rw [hψ_apply, Equiv.symm_apply_apply] at h'
        exact e.injective h'
      have hval : rho * (t * x₁ ^ 2) * rho⁻¹ = t * x₁ ^ 2 :=
        congrArg Subtype.val hfix
      have h2 : rho * (t * x₁ ^ 2) * rho⁻¹ =
          (rho * t * rho⁻¹) * (rho * x₁ ^ 2 * rho⁻¹) := by group
      rw [h2, (fzl_rho_Z h).2.1] at hval
      have hzx : rho * x₁ ^ 2 * rho⁻¹ = x₁ ^ 2 := mul_left_cancel hval
      exact (fzl_rho_Z h).2.2.2 (x₁ ^ 2) hz1mem hz1ne hzx
    · rw [← map_pow]
      have h2 : lamN ^ 2 = 1 := by
        apply Subtype.ext
        show lam ^ 2 = ((1 : ↥(fzN2 t x₁ x₂)) : G)
        rw [(fzl_lam_Z h).2.2.1]
        rfl
      rw [h2, map_one]
    · intro h1
      have hfix : lamN • ptz₁ = ptz₁ := by
        have h' : ψ lamN (e ptz₁) = e ptz₁ := by rw [h1]; rfl
        rw [hψ_apply, Equiv.symm_apply_apply] at h'
        exact e.injective h'
      have hval : lam * (t * x₁ ^ 2) * lam⁻¹ = t * x₁ ^ 2 :=
        congrArg Subtype.val hfix
      have h2 : lam * (t * x₁ ^ 2) * lam⁻¹ =
          (lam * t * lam⁻¹) * (lam * x₁ ^ 2 * lam⁻¹) := by group
      rw [h2, (fzl_lam_Z h).2.1] at hval
      have hzx : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := mul_left_cancel hval
      rw [(fzl_lam_Z h).2.2.2.1] at hzx
      exact (fzl_z1_ne_z2 h).1 hzx.symm
    · rw [← map_mul, ← map_inv, ← map_mul, ← map_inv]
      congr 1
      apply Subtype.ext
      simpa using (fzl_lam_rho h).1
  have hψ : Function.Surjective ψ := fun y =>
    MonoidHom.mem_range.mp (by rw [hψtop]; exact Subgroup.mem_top y)
  have hK_act : ∀ k ∈ ψ.ker, (∀ x : ↥(fzbsX t x₁ x₂), φ k x = x) ∨
      (∀ x : ↥(fzbsX t x₁ x₂), φ k x = x⁻¹) := by
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
      let ptz : fzbsPt t x₁ x₂ := ⟨t * z, ⟨z, hz, rfl⟩⟩
      have hptz : k • ptz = ptz := by
        have h' : ψ k (e ptz) = e ptz := by rw [hk]; rfl
        rw [hψ_apply, Equiv.symm_apply_apply] at h'
        exact e.injective h'
      have hval : (k : G) * (t * z) * (k : G)⁻¹ = t * z := congrArg Subtype.val hptz
      have h2 : (k : G) * (t * z) * (k : G)⁻¹ =
          ((k : G) * t * (k : G)⁻¹) * ((k : G) * z * (k : G)⁻¹) := by group
      rw [h2, hkt] at hval
      exact mul_left_cancel hval
    have hact := (fzbs_Wtau_act h (fzbs_ker_le h k.2 hkt hkZ)).2.2.2
    rcases hact with ha | ha
    · left; intro x; exact Subtype.ext (by rw [hφ_apply k x]; exact ha x.1 x.2)
    · right; intro x; exact Subtype.ext (by rw [hφ_apply k x]; exact ha x.1 x.2)
  have hι : ∃ k ∈ ψ.ker, ∀ x : ↥(fzbsX t x₁ x₂), φ k x = x⁻¹ :=
    ⟨tauN, hker_of_fixes tauN.2 (fzbs_tau_facts h).2.1 (fzbs_tau_facts h).2.2.1,
      fun x => Subtype.ext (by
        rw [hφ_apply tauN x]
        exact (fzbs_tau_facts h).2.2.2.1 x.1 x.2)⟩
  have hρ3 : ρN ^ 3 ∈ φ.ker := by
    have h3 : ρN ^ 3 = 1 := Subtype.ext (by simpa using (fzl_rho_Z h).2.2.1)
    rw [h3]; exact φ.ker.one_mem
  have hρ1 : ρN ∉ φ.ker := by
    rw [hφker]
    intro hmem
    have hrhoW : (rho : G) ∈ ctxW t x₁ x₂ := by
      have := Subgroup.mem_subgroupOf.mp hmem
      simpa using this
    have hcomm := fzbs_W_comm h hrhoW (fzl_Z_le_W h hz1mem)
    have hz : rho * x₁ ^ 2 * rho⁻¹ = x₁ ^ 2 := by rw [hcomm]; group
    exact (fzl_rho_Z h).2.2.2 (x₁ ^ 2) hz1mem hz1ne hz
  have hlam2 : lamN ^ 2 ∈ φ.ker := by
    have h2 : lamN ^ 2 = 1 := Subtype.ext (by simpa using (fzl_lam_Z h).2.2.1)
    rw [h2]; exact φ.ker.one_mem
  have hlam1 : lamN ∉ φ.ker := by
    rw [hφker]
    intro hmem
    have hlamW : (lam : G) ∈ ctxW t x₁ x₂ := by
      have := Subgroup.mem_subgroupOf.mp hmem
      simpa using this
    have hcomm := fzbs_W_comm h hlamW (fzl_Z_le_W h hz1mem)
    have hz : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by rw [hcomm]; group
    rw [(fzl_lam_Z h).2.2.2.1] at hz
    exact (fzl_z1_ne_z2 h).1 hz.symm
  have hlr : lamN * ρN * lamN⁻¹ * ρN ∈ φ.ker := by
    have h1 : lamN * ρN * lamN⁻¹ * ρN = 1 := by
      apply Subtype.ext
      show lam * rho * lam⁻¹ * rho = 1
      rw [(fzl_lam_rho h).1, inv_mul_cancel]
    rw [h1]; exact φ.ker.one_mem
  obtain ⟨f, hf, hfker⟩ :=
    fzl_assemble fzl_21b φ (fzbs_X_equiv h) ψ hψ hφψ hK_act hι
      (ρ := ρN) (lam := lamN) hρ3 hρ1 hlam2 hlam1 hlr
  exact ⟨f, ⟨hf, by rw [hfker, hφker]⟩⟩

end CFSG.OddStandard.SmallF3.FritzII

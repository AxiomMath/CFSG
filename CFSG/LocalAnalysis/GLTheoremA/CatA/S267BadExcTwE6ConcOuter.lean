module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcOuterNat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenB
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRConcB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.E6A5Cube CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.LieType.Universal.Unitary (SU SUid antidiag conjTr conjEquiv)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary (coordBlockSU mem_coordBlockSU_iff)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen (ModelBGen)
open scoped commutatorElement

theorem ringEquiv_pow_apply_eq {K : Type} [Field K] {δ : K ≃+* K} {x : K} (h : δ x = x) (k : ℕ) :
    (δ ^ k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    show (δ ^ k) (δ x) = x
    rw [h, ih]

section Model

variable {K : Type} [Field K] [Finite K]

theorem fieldActor_pow (σ δ : K ≃+* K) (k : ℕ) :
    fieldActor (t := TwistTag.E6) σ δ ^ k = fieldActor σ (δ ^ k) := by
  rw [← fieldActorHom_apply, ← fieldActorHom_apply, map_pow]

variable {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)
  (P : GL (Fin 6) K) (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)

theorem entrywise_leviSU {δ : K ≃+* K} (hδζ : δ ζ = ζ)
    (hPδ : ∀ i j, δ ((P : Matrix (Fin 6) (Fin 6) K) i j) = (P : Matrix (Fin 6) (Fin 6) K) i j)
    (y : Su K ℓ f 6) :
    fieldActor (unitaryInvolution K ℓ f) δ (leviSU hK hf hζ hσζ P hP y) =
      leviSU hK hf hζ hσζ P hP
        (suidMap (unitaryInvolution K ℓ f) 6 (ringEquiv_comm_of_finite _ δ) y) := by
  apply Subtype.ext
  rw [coe_fieldActor, coe_leviSU, coe_leviSU]
  change Units.map (entrywiseHom δ.toRingHom)
      ((leviHomA (unitaryInvolution K ℓ f) hζ ((conjEquiv P hP).symm y) : groupA K) :
        ModGL Tag.E6 K) =
    ((leviHomA (unitaryInvolution K ℓ f) hζ ((conjEquiv P hP).symm
      (suidMap (unitaryInvolution K ℓ f) 6 (ringEquiv_comm_of_finite _ δ) y)) : groupA K) :
        ModGL Tag.E6 K)
  rw [entrywise_leviHomA (ringEquiv_comm_of_finite _ δ) hζ hδζ,
    conjEquiv_symm_suidMap _ (ringEquiv_comm_of_finite _ δ) P hP hPδ]

theorem fieldActor_twE6R0 {δ : K ≃+* K} (c : Kˣ)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    (hδc : δ ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K)) :
    fieldActor (unitaryInvolution K ℓ f) δ (twE6R0 c hct) = twE6R0 c hct := by
  have hA : Matrix.SpecialLinearGroup.map δ.toRingHom (compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K))) =
      compSL2 ((c : K) + ((c⁻¹ : Kˣ) : K)) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [compSL2] <;> simpa using hδc
  apply Subtype.ext
  rw [coe_fieldActor, coe_twE6R0, CFSG.RankThree.Chevalley.entrywise_rootSL2_of_field, hA]

theorem fieldActor_twE6T (δ : K ≃+* K) :
    fieldActor (unitaryInvolution K ℓ f) δ (twE6T K ℓ f) = twE6T K ℓ f := by
  have hA : Matrix.SpecialLinearGroup.map δ.toRingHom (-1 : SL2 K) = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  apply Subtype.ext
  rw [coe_fieldActor, coe_twE6T, CFSG.RankThree.Chevalley.entrywise_rootSL2_of_field, hA]

@[expose] def yTuple (u : Kˣ) : Fin 6 → Kˣ := ![u, u, u⁻¹, u⁻¹, 1, 1]

include hK in
theorem yTuple_mem (u : Kˣ) (hu : u ^ (ℓ ^ f + 1) = 1) :
    diagGL K 6 (yTuple u) ∈ SUid (unitaryInvolution K ℓ f) 6 := by
  have hσv : ∀ v : Kˣ, v ^ (ℓ ^ f + 1) = 1 → unitaryInvolution K ℓ f (v : K) * v = 1 := by
    intro v hv
    rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hv, Units.val_one]
  refine diagGL_mem_SUid (fun i => hσv _ ?_) ?_
  · fin_cases i <;> simp [yTuple, hu, inv_pow]
  · simp [yTuple, Fin.prod_univ_succ]

@[expose] noncomputable def yLam (u : Kˣ) (hu : u ^ (ℓ ^ f + 1) = 1) : Su K ℓ f 6 :=
  ⟨diagGL K 6 (yTuple u), yTuple_mem hK u hu⟩

theorem coe_yLam (u : Kˣ) (hu : u ^ (ℓ ^ f + 1) = 1) :
    (((yLam hK u hu : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      diagonal fun i => (yTuple u i : K) :=
  rfl

theorem suidMap_yLam {δ : K ≃+* K} (u : Kˣ) (hu : u ^ (ℓ ^ f + 1) = 1)
    (hu' : Units.map δ.toRingHom.toMonoidHom u ^ (ℓ ^ f + 1) = 1) :
    suidMap (unitaryInvolution K ℓ f) 6 (ringEquiv_comm_of_finite _ δ) (yLam hK u hu) =
      yLam hK (Units.map δ.toRingHom.toMonoidHom u) hu' := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_suidMap, coe_yLam, coe_yLam, diagonal_map (map_zero δ)]
  congr 1
  funext i
  fin_cases i <;> simp [yTuple]

theorem map_pow_eq_one {δ : K ≃+* K} {u : Kˣ} (hu : u ^ (ℓ ^ f + 1) = 1) :
    Units.map δ.toRingHom.toMonoidHom u ^ (ℓ ^ f + 1) = 1 := by
  rw [← map_pow, hu, map_one]

theorem coe_yLam_mul_inv (u u' : Kˣ) (hu : u ^ (ℓ ^ f + 1) = 1) (hu' : u' ^ (ℓ ^ f + 1) = 1) :
    (((yLam hK u' hu' * (yLam hK u hu)⁻¹ : Su K ℓ f 6) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal fun i => ((yTuple u' i * (yTuple u i)⁻¹ : Kˣ) : K) := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv]
  change ((diagGL K 6 (yTuple u') * (diagGL K 6 (yTuple u))⁻¹ : GL (Fin 6) K) :
    Matrix (Fin 6) (Fin 6) K) = _
  rw [← map_inv, ← map_mul, coe_diagGL]
  rfl

theorem commute_of_leviSU_commute_of_mem_blk01 {y h : Su K ℓ f 6}
    (hy : y ∈ coordBlockSU K ℓ f blk01) (hh : h ∈ coordBlockSU K ℓ f blk01)
    (hc : leviSU hK hf hζ hσζ P hP y * leviSU hK hf hζ hσζ P hP h =
      leviSU hK hf hζ hσζ P hP h * leviSU hK hf hζ hσζ P hP y) : y * h = h * y := by
  have h1 : leviSU hK hf hζ hσζ P hP (y * h * y⁻¹ * h⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  obtain ⟨μ, hμ⟩ := exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP h1
  have hmem : y * h * y⁻¹ * h⁻¹ ∈ coordBlockSU K ℓ f blk01 :=
    mul_mem (mul_mem (mul_mem hy hh) (inv_mem hy)) (inv_mem hh)
  rw [mem_coordBlockSU_iff] at hmem
  have e55 := hmem 5 5 (Or.inl (by decide))
  rw [hμ] at e55
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, if_true] at e55
  have h2 : y * h * y⁻¹ * h⁻¹ = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hμ, e55, one_smul]
    rfl
  calc y * h = y * h * y⁻¹ * h⁻¹ * (h * y) := by group
    _ = h * y := by rw [h2, one_mul]

include hf hζ hσζ hP in
theorem modelBGen_twistedE6_spec_of_inj (hℓ2 : ℓ ≠ 2) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {d : ℕ} (hfd : f = p * d)
    {δ : K ≃+* K} (hδ : orderOf δ = p)
    (hout : fieldActor (unitaryInvolution K ℓ f) δ ∉
      (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
        MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range)
    (hδζ : δ ζ = ζ)
    (hPδ : ∀ i j, δ ((P : Matrix (Fin 6) (Fin 6) K) i j) = (P : Matrix (Fin 6) (Fin 6) K) i j)
    {c : Kˣ} (hc : orderOf c = p)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    (hδc : δ ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} (hm : 0 < m) {φ : (Fin m → Multiplicative (ZMod p)) →* Su K ℓ f 6}
    (hιφ : Function.Injective ((leviSU hK hf hζ hσζ P hP).comp φ))
    (hφδ : ∀ x, suidMap (unitaryInvolution K ℓ f) 6 (ringEquiv_comm_of_finite _ δ) (φ x) = φ x)
    (hφy : ∀ x (u : Kˣ) (hu : u ^ (ℓ ^ f + 1) = 1), φ x * yLam hK u hu = yLam hK u hu * φ x)
    {z₀ w₀ : Su K ℓ f 6}
    (hz₀δ : ∀ i j, δ (((z₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j) =
      ((z₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j)
    (hw₀δ : ∀ i j, δ (((w₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j) =
      ((w₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j) (hz₀ : z₀ ^ p = 1)
    (hzw : leviSU hK hf hζ hσζ P hP z₀ * leviSU hK hf hζ hσζ P hP w₀ ≠
      leviSU hK hf hζ hσζ P hP w₀ * leviSU hK hf hζ hσζ P hP z₀) :
    fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) δ ^ p = 1 ∧
      fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) δ ∉
        (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
          MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range ∧
      IsElemAbelian p (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range ∧
      Nat.card (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range = p ^ (m + 1) ∧
      (∀ a ∈ (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range,
        fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) δ a = a) ∧
      Subgroup.zpowers (twE6R0 c hct) ≤ (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range ∧
      Nat.card (Subgroup.zpowers (twE6R0 c hct)) = p ∧
      GLAPComponent p (Subgroup.centralizer
          ((Subgroup.zpowers (twE6R0 c hct) : Subgroup _) :
            Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))))
        ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f))) ∧
      (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range ≤
        Subgroup.normalizer (((leviJ K ℓ f).subgroupOf
          (twistedE6RootGroup K (unitaryInvolution K ℓ f)) : Subgroup _) :
            Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) ∧
      ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f))).map
          (fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) δ).toMonoidHom =
        (leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) ∧
      (∀ a ∈ (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range, ∀ k : ℕ, k < p →
        (∀ j ∈ (leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)),
          j * (a * (fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) δ ^ k) j * a⁻¹)⁻¹ ∈
            GLAPPrimeCoreOf p
              ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)))) →
          k = 0 ∧ a ∈ Subgroup.zpowers (twE6R0 c hct)) ∧
      GLAPLayer p ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) ⊓
        fixSubgroup (fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) δ)) ≠ ⊥ ∧
      twE6T K ℓ f ≠ 1 ∧ twE6T K ℓ f ^ 2 = 1 ∧
      (leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) ≤
        Subgroup.centralizer
          ({twE6T K ℓ f} : Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) ∧
      (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range ≤
        Subgroup.centralizer
          ({twE6T K ℓ f} : Set ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) ∧
      fieldActor (t := TwistTag.E6) (unitaryInvolution K ℓ f) δ (twE6T K ℓ f) = twE6T K ℓ f := by
  classical
  subst hfd
  have hp : p.Prime := Fact.out
  set σ := unitaryInvolution K ℓ (p * d) with hσdef
  set C₀ := twistedE6RootGroup K σ with hC₀
  set ψ := fieldActor σ δ with hψ
  set ι := leviSU hK hf hζ hσζ P hP with hιdef
  set r₀ := twE6R0 c hct with hr₀
  set Φ := twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ with hΦ
  set J : Subgroup C₀ := (leviJ K ℓ (p * d)).subgroupOf C₀ with hJ
  obtain ⟨hA, hAc, hA₁A, hA₁c, hJcomp, hAN, hcm, ht1, ht2, hJt, hAt⟩ :=
    modelAGen_twistedE6_spec_of_inj hK hf hζ hσζ P hP hℓ2 hp2 hc hct hm hιφ
  have hδσ : ∀ e : K ≃+* K, ∀ x, e (σ x) = σ (e x) := fun e => ringEquiv_comm_of_finite σ e
  have hnat : ∀ y, ψ (ι y) = ι (suidMap σ 6 (hδσ δ) y) :=
    entrywise_leviSU hK hf hζ hσζ P hP hδζ hPδ
  have hnatk : ∀ (k : ℕ) y, (ψ ^ k) (ι y) = ι (suidMap σ 6 (hδσ (δ ^ k)) y) := by
    intro k y
    rw [hψ, fieldActor_pow]
    exact entrywise_leviSU hK hf hζ hσζ P hP (ringEquiv_pow_apply_eq hδζ k)
      (fun i j => ringEquiv_pow_apply_eq (hPδ i j) k) y
  have hψr₀ : ψ r₀ = r₀ := fieldActor_twE6R0 c hct hδc
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe (twE6LeviSA_le_twistedE6RootGroup hK hf)).symm
      (isQuasisimple_twE6LeviSA hζ hσζ hK).1
  have hφp : ∀ x, φ x ^ p = 1 := fun x => by rw [← map_pow, pow_eq_one_of_fin, map_one]
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : Fin m → Multiplicative (ZMod p), x₁ ≠ 1 :=
    ⟨Pi.mulSingle ⟨0, hm⟩ (Multiplicative.ofAdd 1), fun h => by
      have h1 := congrFun h ⟨0, hm⟩
      rw [Pi.mulSingle_eq_same, Pi.one_apply] at h1
      exact one_ne_zero (Multiplicative.ofAdd.injective h1)⟩
  have hιφ1 : ι (φ x₁) ≠ 1 := fun h => hx₁ (hιφ (h.trans (map_one _).symm))
  have hpJ : p ∣ Nat.card ↥J := by
    have hmem : ι (φ x₁) ∈ J := leviSU_mem_leviJ hK hf hζ hσζ P hP _
    have ho : orderOf (⟨ι (φ x₁), hmem⟩ : J) = p := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [← map_pow, hφp, map_one]) hιφ1
    rw [← ho]
    exact orderOf_dvd_natCard _
  refine ⟨?_, hout, hA, hAc, ?_, hA₁A, hA₁c, hJcomp, hAN, ?_, ?_, ?_, ht1, ht2, hJt, hAt,
    fieldActor_twE6T δ⟩
  ·
    have hδp : δ ^ p = 1 := hδ ▸ pow_orderOf_eq_one δ
    rw [fieldActor_pow, hδp, ← fieldActorHom_apply, map_one]
  ·
    rintro _ ⟨x, rfl⟩
    rw [twE6Phi_apply, map_mul, map_pow, hψr₀, hnat, hφδ]
  ·
    have hle : J.map ψ.toMonoidHom ≤ J := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, rfl⟩ := exists_leviSU_eq hK hf hζ hσζ P hP hx
      show ψ (ι y) ∈ J
      rw [hnat]
      exact leviSU_mem_leviJ hK hf hζ hσζ P hP _
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective ψ.injective])
  ·
    rintro _ ⟨x, rfl⟩ k hk hcore
    set a := Φ x with ha
    have hfix : ∀ j ∈ J, a * (ψ ^ k) j * a⁻¹ = j :=
      CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf hp hJq hpJ
        (MulAut.conj a * ψ ^ k).toMonoidHom fun j hj => by
          have h1 := (GLAPPrimeCoreOf p J).inv_mem (hcore j hj)
          rw [_root_.mul_inv_rev, inv_inv] at h1
          exact h1
    have hufix : ∀ u : Kˣ, u ^ (ℓ ^ (p * d) + 1) = 1 → (δ ^ k) (u : K) = u := by
      intro u hu
      set u' := Units.map (δ ^ k).toRingHom.toMonoidHom u with hu'def
      have hu' : u' ^ (ℓ ^ (p * d) + 1) = 1 := map_pow_eq_one hu
      have h1 := hfix (ι (yLam hK u hu)) (leviSU_mem_leviJ hK hf hζ hσζ P hP _)
      rw [hnatk, suidMap_yLam hK u hu hu', ha, twE6Phi_apply] at h1
      set g := φ (fun i : Fin m => x i.succ) with hg
      set n := (Multiplicative.toAdd (x 0)).val with hn
      have h2 : ι g * ι (yLam hK u' hu') * (ι g)⁻¹ = ι (yLam hK u' hu') := by
        rw [← map_mul, hφy, map_mul, mul_inv_cancel_right]
      have hcomm := twE6R0_pow_commute c hct n (leviSU_mem_leviJ hK hf hζ hσζ P hP (yLam hK u' hu'))
      have e : r₀ ^ n * ι g * ι (yLam hK u' hu') * (r₀ ^ n * ι g)⁻¹ = ι (yLam hK u' hu') := by
        calc r₀ ^ n * ι g * ι (yLam hK u' hu') * (r₀ ^ n * ι g)⁻¹
            = r₀ ^ n * (ι g * ι (yLam hK u' hu') * (ι g)⁻¹) * (r₀ ^ n)⁻¹ := by group
          _ = r₀ ^ n * ι (yLam hK u' hu') * (r₀ ^ n)⁻¹ := by rw [h2]
          _ = ι (yLam hK u' hu') := by rw [hcomm, mul_inv_cancel_right]
      rw [e] at h1
      have h4 : ι (yLam hK u' hu' * (yLam hK u hu)⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      obtain ⟨μ, hμ⟩ := exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP h4
      rw [coe_yLam_mul_inv] at hμ
      have e44 := congrFun (congrFun hμ 4) 4
      have e00 := congrFun (congrFun hμ 0) 0
      simp [yTuple] at e44 e00
      rw [← e44] at e00
      have h5 : (u' : K) = u := by
        have hu0 : (u : K) ≠ 0 := u.ne_zero
        field_simp at e00
        exact e00
      rw [hu'def, Units.coe_map] at h5
      exact h5
    have hQ2 : 2 ≤ ℓ ^ (p * d) :=
      (Fact.out : ℓ.Prime).two_le.trans (Nat.le_self_pow (by omega) ℓ)
    have hδk : δ ^ k = 1 := by
      refine eq_one_of_forall_fixed hK hQ2 hp ?_ hufix
      rw [← pow_mul, mul_comm, pow_mul, ← hδ, pow_orderOf_eq_one, one_pow]
    have hk0 : k = 0 := by
      have h1 := orderOf_dvd_of_pow_eq_one hδk
      rw [hδ] at h1
      exact Nat.eq_zero_of_dvd_of_lt h1 hk
    subst hk0
    refine ⟨rfl, hcm a ⟨x, rfl⟩ ⟨hAN ⟨x, rfl⟩, ?_⟩⟩
    have hcomm : ∀ j ∈ J, a * j = j * a := fun j hj => by
      have h1 := hfix j hj
      rw [pow_zero, MulAut.one_apply] at h1
      calc a * j = a * j * a⁻¹ * a := by group
        _ = j * a := by rw [h1]
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₂
    have h1 : ⁅g₁, a ^ n⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact ((Commute.zpow_left (show Commute a g₁ from hcomm g₁ hg₁) n).symm).eq
    rw [h1]
    exact one_mem _
  ·
    have hcard := card_fixSubfield_of_orderOf hp hK hδ
    set S₀ := suidSub hp hp2 hK hδ 6 with hS₀
    set ιF : Su (fixSubfield δ) ℓ d 6 →* C₀ := ι.comp S₀ with hιF
    set L : Subgroup C₀ := ιF.range with hL
    set H : Subgroup C₀ := J ⊓ fixSubgroup ψ with hH
    have hLH : L ≤ H := by
      rintro _ ⟨y, rfl⟩
      refine Subgroup.mem_inf.2 ⟨leviSU_mem_leviJ hK hf hζ hσζ P hP _, ?_⟩
      rw [mem_fixSubgroup]
      show ψ (ι (S₀ y)) = ι (S₀ y)
      rw [hnat, hS₀, suidMap_suidSub]
    have hLn : (L.subgroupOf H).Normal := by
      refine ⟨fun l hl g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hl ⊢
      obtain ⟨y, hy⟩ := hl
      obtain ⟨hgJ, hgψ⟩ := Subgroup.mem_inf.1 g.2
      obtain ⟨h, hh⟩ := exists_leviSU_eq hK hf hζ hσζ P hP hgJ
      have hψh : ι (suidMap σ 6 (hδσ δ) h) = ι h := by
        rw [← hnat, hh]
        exact mem_fixSubgroup.1 hgψ
      obtain ⟨μ, hμ⟩ := exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP
        (show ι (suidMap σ 6 (hδσ δ) h * h⁻¹) = 1 by rw [map_mul, map_inv, hψh, mul_inv_cancel])
      set z := suidMap σ 6 (hδσ δ) h * h⁻¹ with hz
      have hzc : ∀ w, z * w = w * z := commute_of_coe_eq_smul _ hμ
      have hδh : suidMap σ 6 (hδσ δ) h = z * h := by rw [hz, inv_mul_cancel_right]
      have e1 : suidMap σ 6 (hδσ δ) (h * S₀ y * h⁻¹) = h * S₀ y * h⁻¹ := by
        rw [map_mul, map_mul, map_inv, hS₀, suidMap_suidSub, ← hS₀, hδh]
        calc z * h * S₀ y * (z * h)⁻¹ = z * (h * S₀ y * h⁻¹) * z⁻¹ := by group
          _ = h * S₀ y * h⁻¹ * z * z⁻¹ := by rw [hzc]
          _ = h * S₀ y * h⁻¹ := by rw [mul_inv_cancel_right]
      have hfixed : ∀ i j, δ ((((h * S₀ y * h⁻¹ : Su K ℓ (p * d) 6) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) i j) = (((h * S₀ y * h⁻¹ : Su K ℓ (p * d) 6) : GL (Fin 6) K) :
            Matrix (Fin 6) (Fin 6) K) i j := by
        intro i j
        have h1 := congrArg (fun w : Su K ℓ (p * d) 6 =>
          ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j) e1
        simpa only [coe_suidMap, Matrix.map_apply] using h1
      obtain ⟨y', hy'⟩ := mem_range_suidSub hp hp2 hK hδ hfixed
      refine ⟨y', ?_⟩
      show ι (S₀ y') = (g : C₀) * (l : C₀) * (g : C₀)⁻¹
      rw [hy', map_mul, map_mul, map_inv, hh, show ι (S₀ y) = (l : C₀) from hy]
    have hQF : CFSG.IsQuasisimple (Su (fixSubfield δ) ℓ d 6) := by
      obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hcard 6
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (conjEquiv P₀ hP₀)
        (CFSG.LieType.Universal.Unitary.isQuasisimple_SU hcard (by norm_num) (by simp))
    have hker : ιF.rangeRestrict.ker ≤ Subgroup.center (Su (fixSubfield δ) ℓ d 6) := by
      intro y hy
      have h1 : ι (S₀ y) = 1 := congrArg Subtype.val hy
      obtain ⟨μ, hμ⟩ := exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP h1
      rw [Subgroup.mem_center_iff]
      intro w
      apply suidSub_injective hp hp2 hK hδ 6
      rw [map_mul, map_mul]
      exact (commute_of_coe_eq_smul _ hμ _).symm
    have hLq : CFSG.Open.IsQuasisimple ↥L :=
      CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin.isQuasisimple_of_surjective_of_ker_le_center
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hQF)
        ιF.rangeRestrict (MonoidHom.rangeRestrict_surjective _) hker
    obtain ⟨y₀, hy₀⟩ := mem_range_suidSub hp hp2 hK hδ hz₀δ
    obtain ⟨y₁, hy₁⟩ := mem_range_suidSub hp hp2 hK hδ hw₀δ
    have hzL : ι z₀ ∈ L := ⟨y₀, by rw [hιF, MonoidHom.comp_apply, hy₀]⟩
    have hwL : ι w₀ ∈ L := ⟨y₁, by rw [hιF, MonoidHom.comp_apply, hy₁]⟩
    have hzp : ι z₀ ^ p = 1 := by rw [← map_pow, hz₀, map_one]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_normal_quasisimple hp hLH hLn hLq
      (CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute hp hzL hwL
        hzp hzw)

include hf hζ hσζ hP in
theorem modelBGen_twistedE6_of_inj (hℓ2 : ℓ ≠ 2) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {d : ℕ} (hfd : f = p * d)
    {δ : K ≃+* K} (hδ : orderOf δ = p)
    (hout : fieldActor (unitaryInvolution K ℓ f) δ ∉
      (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
        MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range)
    (hδζ : δ ζ = ζ)
    (hPδ : ∀ i j, δ ((P : Matrix (Fin 6) (Fin 6) K) i j) = (P : Matrix (Fin 6) (Fin 6) K) i j)
    {c : Kˣ} (hc : orderOf c = p)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    (hδc : δ ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} (hm : 0 < m) {φ : (Fin m → Multiplicative (ZMod p)) →* Su K ℓ f 6}
    (hιφ : Function.Injective ((leviSU hK hf hζ hσζ P hP).comp φ))
    (hφδ : ∀ x, suidMap (unitaryInvolution K ℓ f) 6 (ringEquiv_comm_of_finite _ δ) (φ x) = φ x)
    (hφy : ∀ x (u : Kˣ) (hu : u ^ (ℓ ^ f + 1) = 1), φ x * yLam hK u hu = yLam hK u hu * φ x)
    {z₀ w₀ : Su K ℓ f 6}
    (hz₀δ : ∀ i j, δ (((z₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j) =
      ((z₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j)
    (hw₀δ : ∀ i j, δ (((w₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j) =
      ((w₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j) (hz₀ : z₀ ^ p = 1)
    (hzw : leviSU hK hf hζ hσζ P hP z₀ * leviSU hK hf hζ hσζ P hP w₀ ≠
      leviSU hK hf hζ hσζ P hP w₀ * leviSU hK hf hζ hσζ P hP z₀) :
    ModelBGen p (m + 1) ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))
      (fieldActor (unitaryInvolution K ℓ f) δ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ :=
    modelBGen_twistedE6_spec_of_inj hK hf hζ hσζ P hP hℓ2 hp2 hfd hδ hout hδζ hPδ hc hct hδc hm hιφ
      hφδ hφy hz₀δ hw₀δ hz₀ hzw
  exact ⟨h1, h2, _, _, _, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

include hf hζ hσζ hP in
theorem modelBGen_twistedE6 (hℓ2 : ℓ ≠ 2) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p (Nat.gcd 6 (ℓ ^ f + 1))) {d : ℕ} (hfd : f = p * d)
    {δ : K ≃+* K} (hδ : orderOf δ = p)
    (hout : fieldActor (unitaryInvolution K ℓ f) δ ∉
      (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
        MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range)
    (hδζ : δ ζ = ζ)
    (hPδ : ∀ i j, δ ((P : Matrix (Fin 6) (Fin 6) K) i j) = (P : Matrix (Fin 6) (Fin 6) K) i j)
    {c : Kˣ} (hc : orderOf c = p)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    (hδc : δ ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} (hm : 0 < m) {φ : (Fin m → Multiplicative (ZMod p)) →* Su K ℓ f 6}
    (hφ : Function.Injective φ)
    (hφδ : ∀ x, suidMap (unitaryInvolution K ℓ f) 6 (ringEquiv_comm_of_finite _ δ) (φ x) = φ x)
    (hφy : ∀ x (u : Kˣ) (hu : u ^ (ℓ ^ f + 1) = 1), φ x * yLam hK u hu = yLam hK u hu * φ x)
    {z₀ w₀ : Su (fixSubfield δ) ℓ d 6} (hz₀ : z₀ ^ p = 1) (hzw : z₀ * w₀ ≠ w₀ * z₀) :
    ModelBGen p (m + 1) ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))
      (fieldActor (unitaryInvolution K ℓ f) δ) := by
  subst hfd
  have hp : p.Prime := Fact.out
  refine modelBGen_twistedE6_of_inj hK hf hζ hσζ P hP hℓ2 hp2 rfl hδ hout hδζ hPδ hc hct hδc hm
    (leviSU_comp_injective hK hf hζ hσζ P hP hcop hφ) hφδ hφy
    (suidSub_fixed hp hp2 hK hδ z₀) (suidSub_fixed hp hp2 hK hδ w₀)
    (by rw [← map_pow, hz₀, map_one]) fun h => hzw ?_
  apply suidSub_injective hp hp2 hK hδ 6
  rw [map_mul, map_mul]
  exact (commute_of_leviSU_commute hK hf hζ hσζ P hP hcop (y := suidSub hp hp2 hK hδ 6 w₀)
    (h := suidSub hp hp2 hK hδ 6 z₀) (by rw [← map_pow, hz₀, map_one]) h.symm).symm

end Model

section Wrappers

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem exists_eq_mul_of_orderOf (hK : Nat.card K = (ℓ ^ f) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ε : K ≃+* K} (hε : orderOf ε = p) : ∃ d, f = p * d := by
  have hc := CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_pow ε
  rw [hε, hK] at hc
  haveI : Fintype (fixSubfield ε) := Fintype.ofFinite _
  obtain ⟨k, -, hk⟩ := FiniteField.card (fixSubfield ε) ℓ
  rw [Nat.card_eq_fintype_card, hk, ← pow_mul, ← pow_mul] at hc
  have h := Nat.pow_right_injective (Fact.out : ℓ.Prime).two_le hc
  have hdvd : p ∣ f * 2 := ⟨k, by rw [← h, mul_comm]⟩
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
  · exact h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1) hp2

theorem dvd_sub_one_of_dvd_pow_sub_one {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (h : p ∣ a ^ p - 1) : p ∣ a - 1 := by
  haveI := Fact.mk hp
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  rw [Nat.cast_sub (Nat.one_le_pow _ _ ha), Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at h
  rw [Nat.cast_sub ha, Nat.cast_one]
  exact h

theorem dvd_add_one_of_dvd_pow_add_one {p a : ℕ} (hp : p.Prime) (h : p ∣ a ^ p + 1) :
    p ∣ a + 1 := by
  haveI := Fact.mk hp
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  rw [Nat.cast_add, Nat.cast_pow, ZMod.pow_card] at h
  rw [Nat.cast_add]
  exact h

theorem commute_yLam_of_mem_coordBlockSU (hK : Nat.card K = (ℓ ^ f) ^ 2) {J : Finset (Fin 6)}
    {g : Su K ℓ f 6} (hg : g ∈ coordBlockSU K ℓ f J) {u : Kˣ} (hu : u ^ (ℓ ^ f + 1) = 1)
    (hv : ∀ i ∈ J, ∀ j ∈ J, (yTuple u i : K) = yTuple u j) :
    g * yLam hK u hu = yLam hK u hu * g := by
  apply Subtype.ext
  apply Units.ext
  show ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * diagonal (fun i => (yTuple u i : K)) =
    diagonal (fun i => (yTuple u i : K)) * ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  exact (CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary.diagonal_mul_comm_of_mem_coordBlockSU
    hg hv).symm

theorem exists_layer_pair {d p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ε : K ≃+* K}
    (hF : Nat.card (fixSubfield ε) = (ℓ ^ d) ^ 2) (hpF : p ∣ (ℓ ^ d) ^ 2 - 1) :
    ∃ z₀ w₀ : Su (fixSubfield ε) ℓ d 6, z₀ ^ p = 1 ∧ z₀ * w₀ ≠ w₀ * z₀ := by
  obtain ⟨M₂, W₂, hM₂, hMW⟩ := exists_su_two_orderOf_not_commute hF Fact.out hp2 hpF
  refine ⟨pairBlock blk01 card_blk01 M₂, pairBlock blk01 card_blk01 W₂, ?_, fun h => hMW ?_⟩
  · rw [← map_pow, ← hM₂, pow_orderOf_eq_one, map_one]
  · apply pairBlock_injective blk01 card_blk01
    rw [map_mul, map_mul]
    exact h

theorem modelBGen_twistedE6_of_dvd_sub_one (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) (hℓ2 : ℓ ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpQ : p ∣ ℓ ^ f - 1) {ε : K ≃+* K} (hε : orderOf ε = p)
    (hout : fieldActor (unitaryInvolution K ℓ f) ε ∉
      (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
        MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range) :
    ModelBGen p 4 ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))
      (fieldActor (unitaryInvolution K ℓ f) ε) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, rfl⟩ := exists_eq_mul_of_orderOf hK hp hp2 hε
  have hQ1 : 1 ≤ ℓ ^ (p * d) := Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos
  have hpQ2 : p ∣ (ℓ ^ (p * d)) ^ 2 - 1 := hpQ.trans (Nat.sub_one_dvd_pow_sub_one _ 2)
  have hcop : Nat.Coprime p (Nat.gcd 6 (ℓ ^ (p * d) + 1)) := by
    refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 6 _) ?_
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hp2 ?_
    have h2 : p ∣ 2 := by
      have := Nat.dvd_sub h hpQ
      rwa [show ℓ ^ (p * d) + 1 - (ℓ ^ (p * d) - 1) = 2 by omega] at this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
  have hF := card_fixSubfield_of_orderOf hp hK hε
  have hpF : p ∣ (ℓ ^ d) ^ 2 - 1 := by
    refine dvd_sub_one_of_dvd_pow_sub_one hp (Nat.one_le_pow _ _ (pow_pos (Fact.out : ℓ.Prime).pos _)) ?_
    rw [show ((ℓ ^ d) ^ 2) ^ p = (ℓ ^ (p * d)) ^ 2 by ring]
    exact hpQ2
  obtain ⟨ζ, hζ, hσζ, hεζ⟩ := exists_unitaryInvolution_eq_neg_fixed hp hp2 hK hε
  obtain ⟨P, hP, hPε⟩ := exists_wittMatrix_fixed hp hp2 hK hε 6
  obtain ⟨c, hc, hεc⟩ := exists_orderOf_eq_fixSubfield hp hε (by rw [hK]; exact hpQ2)
  have hcQ : (c : K) ^ (ℓ ^ (p * d)) = c := by
    obtain ⟨k, hk⟩ := hpQ
    have h1 : c ^ (ℓ ^ (p * d) - 1) = 1 := by rw [hk, pow_mul, ← hc, pow_orderOf_eq_one, one_pow]
    have h2 : c ^ (ℓ ^ (p * d)) = c := by
      calc c ^ (ℓ ^ (p * d)) = c ^ (ℓ ^ (p * d) - 1) * c := by rw [← pow_succ, Nat.sub_add_cancel hQ1]
        _ = c := by rw [h1, one_mul]
    rw [← Units.val_pow_eq_pow_val, h2]
  have hct : unitaryInvolution K ℓ (p * d) ((c : K) + ((c⁻¹ : Kˣ) : K)) =
      (c : K) + ((c⁻¹ : Kˣ) : K) := by
    rw [map_add, unitaryInvolution_apply, unitaryInvolution_apply, hcQ, Units.val_inv_eq_inv_val,
      inv_pow, hcQ]
  have hεct : ε ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K) := by
    rw [map_add, Units.val_inv_eq_inv_val, map_inv₀, hεc]
  obtain ⟨M₂, -, hM₂, -⟩ := exists_su_two_orderOf_not_commute hF hp hp2 hpF
  set S₀ := suidSub hp hp2 hK hε 6 with hS₀
  set φ := S₀.comp (blockTripleHom M₂ hM₂) with hφ
  have hφinj : Function.Injective φ :=
    (suidSub_injective hp hp2 hK hε 6).comp (blockTripleHom_injective M₂ hM₂)
  have hφε : ∀ x, suidMap (unitaryInvolution K ℓ (p * d)) 6 (ringEquiv_comm_of_finite _ ε)
      (φ x) = φ x := fun x => suidMap_suidSub hp hp2 hK hε _
  have hφy : ∀ x (u : Kˣ) (hu : u ^ (ℓ ^ (p * d) + 1) = 1),
      φ x * yLam hK u hu = yLam hK u hu * φ x := by
    intro x u hu
    rw [hφ, MonoidHom.comp_apply, blockTripleHom_apply, map_mul, map_mul]
    have h01 := commute_yLam_of_mem_coordBlockSU hK
      (suidSub_mem_coordBlockSU hp hp2 hK hε (pairBlock_mem blk01 card_blk01
        (powHom M₂ hM₂ (x 0)))) hu (by
          intro i hi j hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
          rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rfl)
    have h23 := commute_yLam_of_mem_coordBlockSU hK
      (suidSub_mem_coordBlockSU hp hp2 hK hε (pairBlock_mem blk23 card_blk23
        (powHom M₂ hM₂ (x 1)))) hu (by
          intro i hi j hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
          rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rfl)
    have h45 := commute_yLam_of_mem_coordBlockSU hK
      (suidSub_mem_coordBlockSU hp hp2 hK hε (pairBlock_mem blk45 card_blk45
        (powHom M₂ hM₂ (x 2)))) hu (by
          intro i hi j hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
          rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rfl)
    exact ((Commute.mul_left (Commute.mul_left h01 h23) h45)).eq
  obtain ⟨z₀, w₀, hz₀, hzw⟩ := exists_layer_pair hp2 hF hpF
  exact modelBGen_twistedE6 hK hf hζ hσζ P hP hℓ2 hp2 hcop rfl hε hout hεζ hPε hc hct hεct
    (by norm_num : 0 < 3) hφinj hφε hφy hz₀ hzw

theorem modelBGen_twistedE6_of_dvd_add_one (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) (hℓ2 : ℓ ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpQ : p ∣ ℓ ^ f + 1) {ε : K ≃+* K} (hε : orderOf ε = p)
    (hout : fieldActor (unitaryInvolution K ℓ f) ε ∉
      (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
        MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range) :
    ModelBGen p 6 ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))
      (fieldActor (unitaryInvolution K ℓ f) ε) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨d, rfl⟩ := exists_eq_mul_of_orderOf hK hp hp2 hε
  have hQ1 : 1 ≤ ℓ ^ (p * d) := Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos
  have hpQ2 : p ∣ (ℓ ^ (p * d)) ^ 2 - 1 := by
    have h : (ℓ ^ (p * d)) ^ 2 - 1 = (ℓ ^ (p * d) + 1) * (ℓ ^ (p * d) - 1) := by
      have h2 : 1 ≤ (ℓ ^ (p * d)) ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [hQ1, h2]
      ring
    rw [h]
    exact hpQ.mul_right _
  have hcop : Nat.Coprime p (Nat.gcd 6 (ℓ ^ (p * d) + 1)) := by
    refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 6 _) ?_
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
    have h6 := Nat.le_of_dvd (by norm_num) h
    have h56 : p = 5 ∨ p = 6 := by omega
    rcases h56 with rfl | rfl
    · norm_num at h
    · exact absurd hp (by norm_num)
  have hF := card_fixSubfield_of_orderOf hp hK hε
  have hpF : p ∣ (ℓ ^ d) ^ 2 - 1 := by
    refine dvd_sub_one_of_dvd_pow_sub_one hp (Nat.one_le_pow _ _ (pow_pos (Fact.out : ℓ.Prime).pos _)) ?_
    rw [show ((ℓ ^ d) ^ 2) ^ p = (ℓ ^ (p * d)) ^ 2 by ring]
    exact hpQ2
  have hpF1 : p ∣ ℓ ^ d + 1 := by
    refine dvd_add_one_of_dvd_pow_add_one hp ?_
    rw [show (ℓ ^ d) ^ p = ℓ ^ (p * d) by ring]
    exact hpQ
  obtain ⟨ζ, hζ, hσζ, hεζ⟩ := exists_unitaryInvolution_eq_neg_fixed hp hp2 hK hε
  obtain ⟨P, hP, hPε⟩ := exists_wittMatrix_fixed hp hp2 hK hε 6
  obtain ⟨c, hc, hεc⟩ := exists_orderOf_eq_fixSubfield hp hε (by rw [hK]; exact hpQ2)
  have h2u : c ^ (ℓ ^ (p * d)) = c⁻¹ := by
    obtain ⟨k, hk⟩ := hpQ
    have h1 : c ^ (ℓ ^ (p * d) + 1) = 1 := by rw [hk, pow_mul, ← hc, pow_orderOf_eq_one, one_pow]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h1])
  have hct : unitaryInvolution K ℓ (p * d) ((c : K) + ((c⁻¹ : Kˣ) : K)) =
      (c : K) + ((c⁻¹ : Kˣ) : K) := by
    have hcQ : (c : K) ^ (ℓ ^ (p * d)) = ((c⁻¹ : Kˣ) : K) := by rw [← Units.val_pow_eq_pow_val, h2u]
    have hcQ' : ((c⁻¹ : Kˣ) : K) ^ (ℓ ^ (p * d)) = (c : K) := by
      rw [← Units.val_pow_eq_pow_val, inv_pow, h2u, inv_inv]
    rw [map_add, unitaryInvolution_apply, unitaryInvolution_apply, hcQ, hcQ', add_comm]
  have hεct : ε ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K) := by
    rw [map_add, Units.val_inv_eq_inv_val, map_inv₀, hεc]
  haveI : Finite (fixSubfield ε) := Subtype.finite
  obtain ⟨c₀, hc₀⟩ := CFSG.StandardType.TableBSymp.exists_orderOf_eq_of_dvd (K := fixSubfield ε)
    (p := p) (by rw [hF]; exact hpF)
  set S₀ := suidSub hp hp2 hK hε 6 with hS₀
  set φ := S₀.comp (diagSUHom c₀ hc₀ hpF1) with hφ
  have hφinj : Function.Injective φ :=
    (suidSub_injective hp hp2 hK hε 6).comp (diagSUHom_injective c₀ hc₀ hpF1)
  have hφε : ∀ x, suidMap (unitaryInvolution K ℓ (p * d)) 6 (ringEquiv_comm_of_finite _ ε)
      (φ x) = φ x := fun x => suidMap_suidSub hp hp2 hK hε _
  have hφy : ∀ x (u : Kˣ) (hu : u ^ (ℓ ^ (p * d) + 1) = 1),
      φ x * yLam hK u hu = yLam hK u hu * φ x := by
    intro x u hu
    apply Subtype.ext
    apply Units.ext
    show (((S₀ (diagSUHom c₀ hc₀ hpF1 x) : Su K ℓ (p * d) 6) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) * diagonal (fun i => (yTuple u i : K)) =
      diagonal (fun i => (yTuple u i : K)) *
        (((S₀ (diagSUHom c₀ hc₀ hpF1 x) : Su K ℓ (p * d) 6) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)
    rw [hS₀, coe_suidSub, coe_diagSUHom, diagonal_map (map_zero _), diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  obtain ⟨z₀, w₀, hz₀, hzw⟩ := exists_layer_pair hp2 hF hpF
  exact modelBGen_twistedE6 hK hf hζ hσζ P hP hℓ2 hp2 hcop rfl hε hout hεζ hPε hc hct hεct
    (by norm_num : 0 < 5) hφinj hφε hφy hz₀ hzw

end Wrappers

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer

end

module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Assemble
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Beta
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2IdCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Units

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem code_one3 (i j : Fin 3) : (((1 : M3) i j).code : ℕ) = idCode i j := by
  revert i j; decide

theorem coe_st3 {a b : Fin 3} (hab : a ≠ b) (c : F4) :
    ((st3 a b c : SL3) : M3) = Matrix.transvection a b c := by
  rw [st3, stT_eq_transvection _ hab]; rfl

theorem toMat_kBits (A B : M3) :
    toMat 18 18 (kBits (fun i j => (A i j).code) (fun i j => (B i j).code)) =
      conjP (reF9 (kr A B)) := by
  have hc : krCode (fun i j => ((A i j).code : ℕ)) (fun i j => ((B i j).code : ℕ)) =
      fun r s => ((kr A B r s).code : ℕ) := by
    funext r s; exact (code_kr A B r s).symm
  rw [kBits, hc, toMat_bmul, toMat_bmul, toMat_reBits9, conjP_apply, pcM, pciM]

theorem lft_st3 {a b : Fin 3} (hab : a ≠ b) (c : F4) :
    lft (st3 a b c) = toMat 18 18 (kBits (trCode3 a b c.code) idCode) := by
  rw [lft_apply, coe_st3 hab, ← toMat_kBits]
  congr 2
  · funext i j; exact code_transvection3 hab c i j
  · funext i j; exact code_one3 i j

theorem transvection_transpose3 {a b : Fin 3} (hab : a ≠ b) (c : F4) :
    (Matrix.transvection a b c)ᵀ = Matrix.transvection b a c := by
  refine f3mat_ext fun i j => ?_
  rw [transpose_apply]
  have key : ∀ (a b : Fin 3) (c : F4) (i j : Fin 3), decide (a ≠ b →
      (Matrix.transvection a b c j i).code = (Matrix.transvection b a c i j).code) = true := by
    decide
  exact of_decide_eq_true (key a b c i j) hab

theorem rgt_st3 {a b : Fin 3} (hab : a ≠ b) (c : F4) :
    rgt (st3 a b c) = toMat 18 18 (kBits idCode (trCode3 b a c.code)) := by
  rw [rgt_apply, st3_inv, coe_st3 hab, transvection_transpose3 hab, ← toMat_kBits]
  congr 2
  · funext i j; exact code_one3 i j
  · funext i j; exact code_transvection3 (Ne.symm hab) c i j

theorem sigma3_st3 {a b : Fin 3} (hab : a ≠ b) (c : F4) :
    sigma3 (st3 a b c) = st3 b a (frobF4 c) := by
  apply Subtype.ext
  rw [coe_sigma3, st3_inv, coe_st3 hab, coe_st3 (Ne.symm hab), star3]
  refine f3mat_ext fun i j => ?_
  rw [transpose_apply, frob3_apply]
  have key : ∀ (a b : Fin 3) (c : F4) (i j : Fin 3), decide (a ≠ b →
      (frobF4 (Matrix.transvection a b c j i)).code =
        (Matrix.transvection b a (frobF4 c) i j).code) = true := by
    decide
  exact of_decide_eq_true (key a b c i j) hab

theorem sigma3_sigma3 (g : SL3) : sigma3 (sigma3 g) = g := by
  apply Subtype.ext
  rw [coe_sigma3, ← map_inv, coe_sigma3, inv_inv, star3_star3]

section TL


@[expose] noncomputable def tlftHom : SL3 →* Mat18 where
  toFun g := tauM * lft g * tauM
  map_one' := by rw [map_one, Matrix.mul_one, tauM_mul_self]
  map_mul' a b := by
    rw [map_mul]
    calc tauM * (lft a * lft b) * tauM = tauM * lft a * (tauM * tauM) * lft b * tauM := by
          rw [tauM_mul_self, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = tauM * lft a * tauM * (tauM * lft b * tauM) := by simp only [Matrix.mul_assoc]

theorem tau_lft (g : SL3) : tauM * lft g * tauM = rgt (sigma3 g) := by
  let φ₂ : SL3 →* Mat18 := rgt.comp sigma3
  have h : tlftHom = φ₂ := hom_ext_gen3 fun s => by
    have hne := pairOf_ne s
    have hg : gen3 s = st3 (pairOf s).1 (pairOf s).2 (coefOf s) := rfl
    change tauM * lft (gen3 s) * tauM = rgt (sigma3 (gen3 s))
    rw [hg, lft_st3 hne, sigma3_st3 hne, rgt_st3 (Ne.symm hne), code_frobF4, code_coefOf, tauM,
      ← toMat_bmul, ← toMat_bmul]
    have := tlCheck_eq_true
    simp only [tlCheck, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at this
    rw [toMat_bmul, toMat_bmul, Matrix.mul_assoc, ← toMat_bmul, ← toMat_bmul, this s]
  exact DFunLike.congr_fun h g

end TL

@[expose] noncomputable def cL (m : ℕ) : SL3 :=
  st3 (lTr m).1 (lTr m).2.1 ⟨Fin.ofNat 4 (lTr m).2.2⟩

@[expose] noncomputable def gL (m : ℕ) : SL3 :=
  if m = 0 then gen3 1 else if m = 1 then gen3 0 * gen3 1 else if m = 2 then gen3 3
  else gen3 2 * gen3 3

theorem lTr_ne {m : ℕ} : (lTr m).1 ≠ (lTr m).2.1 := by
  unfold lTr; split_ifs <;> decide

theorem rhoA_gL {m : ℕ} (hm : m < 4) :
    rhoA (gL m) = toMat 9 9 (lGen m) := by
  interval_cases m
  · have e1 : gL 0 = gen3 1 := rfl
    have e2 : lGen 0 = genABits 1 := rfl
    rw [e1, e2, rhoA_gen3]; rfl
  · have e1 : gL 1 = gen3 0 * gen3 1 := rfl
    have e2 : lGen 1 = bmul 9 9 (genABits 0) (genABits 1) := rfl
    rw [e1, e2, map_mul, rhoA_gen3, rhoA_gen3, toMat_bmul]; rfl
  · have e1 : gL 2 = gen3 3 := rfl
    have e2 : lGen 2 = genABits 3 := rfl
    rw [e1, e2, rhoA_gen3]; rfl
  · have e1 : gL 3 = gen3 2 * gen3 3 := rfl
    have e2 : lGen 3 = bmul 9 9 (genABits 2) (genABits 3) := rfl
    rw [e1, e2, map_mul, rhoA_gen3, rhoA_gen3, toMat_bmul]; rfl

theorem candX1_eq {m : ℕ}
    (hm : m < 4) : toMat 18 18 (candXBits 1 m) = rgt (cL m) * kact (gL m) := by
  have h := lIdCheck_eq_true
  simp only [lIdCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [h m hm, toMat_bmul, toMat_bd9_self, kact_eq_rhoN, rhoA_gL hm, cL, rgt_st3 lTr_ne]
  congr 3
  interval_cases m <;> rfl

theorem st3_mem_of_gen' {N : Subgroup SL3} {a b : Fin 3} (hab : a ≠ b)
    (h1 : st3 a b 1 ∈ N) (h3 : st3 a b ⟨3⟩ ∈ N) (c : F4) : st3 a b c ∈ N := by
  have hω : st3 a b F4.ω ∈ N := by
    have := mul_mem h1 h3
    rw [st3_mul_st3 hab] at this
    have e : (1 : F4) + ⟨3⟩ = F4.ω := f4_ext rfl
    rwa [e] at this
  exact st3_mem_of_gen hab h1 hω c

section LiftL

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable {π : Γ →* (W →ₗ[ZMod 2] W)} {θ : SL3 →* Γ} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 9 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {W₀ V : Submodule (ZMod 2) W}
  {τ : Γ →* Γ} {e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)}

theorem kact_eq_lft_rgt (g : SL3) : kact g = lft g * rgt (sigma3 g) := kact_apply g

theorem conj_rgt (x y b : SL3) :
    lft x * rgt y * rgt b * (lft x⁻¹ * rgt y⁻¹) = rgt (y * b * y⁻¹) := by
  calc lft x * rgt y * rgt b * (lft x⁻¹ * rgt y⁻¹)
      = lft x * (rgt y * (rgt b * (rgt y⁻¹ * lft x⁻¹))) := by
        rw [lft_rgt_comm x⁻¹ y⁻¹]; simp only [Matrix.mul_assoc]
    _ = lft x * rgt (y * b * y⁻¹) * lft x⁻¹ := by
        rw [map_mul, map_mul]; simp only [Matrix.mul_assoc]
    _ = rgt (y * b * y⁻¹) * (lft x * lft x⁻¹) := by
        rw [lft_rgt_comm]; simp only [Matrix.mul_assoc]
    _ = rgt (y * b * y⁻¹) := by rw [← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]

theorem exists_liftL (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {d : ℕ → Γ}
    (hX : ∀ n < 4, matOfN e (π (d n)) = toMat 18 18 (candXBits 1 n))
    (hKc : π.ker ≤ Subgroup.center Γ) (hKo : Odd (Nat.card π.ker)) :
    ∃ ψ : SL3 →* Γ, ∀ g, matOfN e (π (ψ g)) = lft g := by
  set f := fU e π with hfdef
  have hfk := fU_ker e π
  have hKθ : ∀ g, matOfN e (π (θ g)) = kact g := fun g => by rw [hK, kact_eq_rhoN]
  set ρR := rgt.toHomUnits with hρRdef
  have hρR : ∀ b, ((ρR b : (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
      Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2)) = rgt b := fun b => rfl
  set N := f.range.comap ρR with hNdef
  have hNn : N.Normal := by
    constructor
    intro b hb y
    obtain ⟨γ, hγ⟩ := hb
    have hγ' : matOfN e (π γ) = rgt b := by
      have := congrArg Units.val hγ
      rwa [coe_fU, hρR] at this
    refine ⟨θ (sigma3 y) * γ * θ (sigma3 y)⁻¹, Units.ext ?_⟩
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, coe_fU, coe_fU, coe_fU, hKθ, hKθ, hγ', hρR,
      kact_eq_lft_rgt, kact_eq_lft_rgt, sigma3_sigma3]
    rw [show sigma3 (sigma3 y)⁻¹ = y⁻¹ by rw [map_inv, sigma3_sigma3], conj_rgt]
  have hc : ∀ m < 4, cL m ∈ N := fun m hm => by
    refine ⟨d m * (θ (gL m))⁻¹, Units.ext ?_⟩
    rw [map_mul, map_inv, Units.val_mul, coe_fU, hX m hm, hρR, candX1_eq hm]
    have h1 : ((f (θ (gL m)))⁻¹ : (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ).val =
        kact (gL m)⁻¹ := by
      have e1 : (f (θ (gL m)))⁻¹ = f (θ (gL m)⁻¹) := by rw [map_inv, map_inv]
      rw [e1, coe_fU, hKθ]
    rw [h1, Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  have h10 : ∀ c, st3 1 0 c ∈ N := st3_mem_of_gen' (by decide) (hc 0 (by norm_num))
    (hc 1 (by norm_num))
  have h20 : ∀ c, st3 2 0 c ∈ N := st3_mem_of_gen' (by decide) (hc 2 (by norm_num))
    (hc 3 (by norm_num))
  have htop := eq_top_of_ET h10 h20
  have hallR : ∀ b, rgt.toHomUnits b ∈ f.range := fun b => by
    have : b ∈ N := by rw [htop]; exact Subgroup.mem_top b
    exact this
  set ρ := lft.toHomUnits with hρdef
  have hall : ∀ g, ρ g ∈ f.range := fun g => by
    obtain ⟨γ, hγ⟩ := hallR (sigma3 g)
    refine ⟨θ g * γ⁻¹, Units.ext ?_⟩
    have hγ' : (f γ⁻¹).val = rgt (sigma3 g)⁻¹ := by
      rw [map_inv, hγ, ← map_inv]; rfl
    rw [map_mul, Units.val_mul, hγ', coe_fU, hKθ, kact_eq_lft_rgt, Matrix.mul_assoc, ← map_mul,
      mul_inv_cancel, map_one, Matrix.mul_one]
    rfl
  obtain ⟨ψ, hψ⟩ := exists_hom_comp_eq_of_odd_center (F := CFSG.Fischer.F4) (m := 2)
    (by norm_num) f (by rw [hfk]; exact hKc) (by rw [hfk]; exact hKo) ρ
    (fun i j _ c => hall _)
  refine ⟨ψ, fun g => ?_⟩
  have h1 := congrArg Units.val (DFunLike.congr_fun hψ g)
  rw [MonoidHom.comp_apply, coe_fU] at h1
  exact h1

theorem R3bHyp.concl_L [Finite Γ] (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {d : ℕ → Γ}
    (hX : ∀ n < 4, matOfN e (π (d n)) = toMat 18 18 (candXBits 1 n))
    (hspan : ∀ x ∈ D, ∃ μ < 16, ∃ ν < 16, x = dProd d ν * eProdG θ μ)
    (hKc : π.ker ≤ Subgroup.center Γ) (hKo : Odd (Nat.card π.ker)) :
    (∀ γ, τ γ = γ → γ ∈ θ.range) ∧ ∃ X : Subgroup Γ, X ⊔ X.map τ = ⊤ ∧ ⁅X, X.map τ⁆ = ⊥ ∧
      Nat.card (X ⊓ X.map τ : Subgroup Γ) ∣ 3 ∧ ∃ ψ' : SL3 →* X, Function.Surjective ψ' ∧
        ψ'.ker ≤ Subgroup.center SL3 ∧ ∀ g, θ g = (ψ' g : Γ) * τ (ψ' g) := by
  obtain ⟨ψ, hψ⟩ := exists_liftL hK hX hKc hKo
  have hfk := fU_ker e π
  have hKθ : ∀ g, matOfN e (π (θ g)) = kact g := fun g => by rw [hK, kact_eq_rhoN]
  have hfψ : ∀ g, ((fU e π (ψ g) : (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
      Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2)) = lft g := fun g => by rw [coe_fU, hψ]
  have hconj : ∀ g, ((TU * fU e π (ψ g) * TU⁻¹ : (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
      Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2)) = rgt (sigma3 g) := fun g => by
    simp only [Units.val_mul, hfψ, coe_TU, coe_TU_inv]; exact tau_lft g
  have hcomm : ∀ a b, fU e π (ψ a) * (TU * fU e π (ψ b) * TU⁻¹) =
      (TU * fU e π (ψ b) * TU⁻¹) * fU e π (ψ a) := fun a b => by
    ext1
    have e1 : ((fU e π (ψ a) * (TU * fU e π (ψ b) * TU⁻¹) :
        (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
          Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))
        = lft a * rgt (sigma3 b) := by rw [Units.val_mul, hfψ, hconj]
    have e2 : (((TU * fU e π (ψ b) * TU⁻¹) * fU e π (ψ a) :
        (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
          Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))
        = rgt (sigma3 b) * lft a := by rw [Units.val_mul, hfψ, hconj]
    rw [e1, e2]; exact lft_rgt_comm a (sigma3 b)
  have hsc : ∀ a b, fU e π (ψ a) = TU * fU e π (ψ b) * TU⁻¹ → a ∈ Subgroup.zpowers omegaI :=
    fun a b hab => mem_zpowers_of_lft_eq_rgt (b := sigma3 b)
      (by have := congrArg Units.val hab; rwa [hfψ, hconj] at this)
  have hθ : ∀ g, fU e π (θ g) = fU e π (ψ g) * (TU * fU e π (ψ g) * TU⁻¹) := fun g => by
    ext1
    have e1 : ((fU e π (ψ g) * (TU * fU e π (ψ g) * TU⁻¹) :
        (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
          Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))
        = lft g * rgt (sigma3 g) := by rw [Units.val_mul, hfψ, hconj]
    rw [e1, coe_fU, hKθ, kact_eq_lft_rgt]
  have hd' : ∀ n < 4, fU e π (d n) = fU e π (ψ (gL n)) *
      (TU * fU e π (ψ (sigma3 (cL n * sigma3 (gL n)))) * TU⁻¹) := fun n hn => by
    ext1
    have e1 : ((fU e π (ψ (gL n)) * (TU * fU e π (ψ (sigma3 (cL n * sigma3 (gL n)))) * TU⁻¹) :
        (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
          Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))
        = lft (gL n) * rgt (cL n * sigma3 (gL n)) := by
      rw [Units.val_mul, hfψ, hconj, sigma3_sigma3]
    rw [e1, coe_fU, hX n hn, candX1_eq hn, kact_eq_lft_rgt, map_mul, ← Matrix.mul_assoc,
      ← lft_rgt_comm, Matrix.mul_assoc]
  refine concl_of_assemble τ (fU e π) TU ψ θ h.ττ (by rw [hfk]; exact hKc) (by rw [hfk]; exact hKo)
    (fun g hg hτ => h.Kr g (by rw [hfk] at hg; exact hg) hτ) (h.fU_τ he) hcomm hsc hθ h.τK
    (closure_range_union θ D h.gen) ?_
  rintro s (⟨g, rfl⟩ | hsD)
  · exact Or.inl ⟨g, rfl⟩
  · refine Or.inr ⟨h.D_sq s hsD, ?_⟩
    set S₀ : Set Γ := {x | (∃ n < 4, x = d n) ∨ x ∈ Set.range θ} with hS₀
    refine exists_Q_of_mem_closure (fU e π) TU ψ hcomm (S₀ := S₀) ?_ ?_
    · rintro x (⟨n, hn, rfl⟩ | ⟨g, rfl⟩)
      · exact ⟨_, _, hd' n hn⟩
      · exact ⟨g, g, hθ g⟩
    · obtain ⟨μ, -, ν, -, rfl⟩ := hspan s hsD
      refine mul_mem (Subgroup.list_prod_mem _ fun y hy => ?_)
        (Subgroup.list_prod_mem _ fun y hy => ?_)
      · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hy
        exact Subgroup.subset_closure (Or.inl ⟨n, bitList_lt hn, rfl⟩)
      · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hy
        exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)

end LiftL

end CFSG.EvenSmallLie.UnitarySix.YamadaN2

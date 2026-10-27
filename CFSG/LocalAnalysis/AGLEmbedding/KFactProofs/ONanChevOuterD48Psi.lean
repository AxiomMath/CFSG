module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Steinberg.TwistedD4.Defs
public import CFSG.Quasithin.Recognition.CertD4BridgeTheta

public section

namespace CFSG.AGLEmbedding.ChevOuterD48

open CFSG.Quasithin CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Ree

section Unique

variable (k : Type) [Field k] [CharP k 2]

theorem eq_one_of_pow_eight_eq_one {c : k} (h : c ^ 8 = 1) : c = 1 := by
  have h8 : (c - 1) ^ 8 = c ^ 8 - 1 ^ 8 := by
    have := sub_pow_char_pow (R := k) (p := 2) (n := 3) c 1
    simpa using this
  have h0 : (c - 1) ^ 8 = 0 := by rw [h8, h]; ring
  exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h0)

theorem d48b_rel_unique
    {A : ModGL Tag.D4 k}
    {B B' : GL (Fin 8) k} (hB : B ∈ d4bΩ k) (hB' : B' ∈ d4bΩ k) (h : D4bRel k A B)
    (h' : D4bRel k A B') : B = B' := by
  have hBB : ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
      (B : Matrix (Fin 8) (Fin 8) k) = 1 := Units.inv_mul B
  have hBB' : (B : Matrix (Fin 8) (Fin 8) k) *
      ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) = 1 := Units.mul_inv B
  have hcomm : ∀ v : RootModule Tag.D4 k,
      ((B⁻¹ * B' : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * d4bθ k v =
        d4bθ k v * ((B⁻¹ * B' : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) := by
    intro v
    set T := d4bθ k v with hT
    set S := d4bθ k ((A : Module.End k (RootModule Tag.D4 k)) v) with hS
    have e1 : T = ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
        (S * (B : Matrix (Fin 8) (Fin 8) k)) := by
      rw [hS, h v, ← mul_assoc, hBB, one_mul]
    have e2 : S * (B' : Matrix (Fin 8) (Fin 8) k) = (B' : Matrix (Fin 8) (Fin 8) k) * T := h' v
    rw [Units.val_mul]
    have L : ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
        (B' : Matrix (Fin 8) (Fin 8) k) * T =
        ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * S *
          (B' : Matrix (Fin 8) (Fin 8) k) := by
      rw [mul_assoc, ← e2, ← mul_assoc]
    have R : T * (((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
        (B' : Matrix (Fin 8) (Fin 8) k)) =
        ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * S *
          (B' : Matrix (Fin 8) (Fin 8) k) := by
      calc T * (((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
              (B' : Matrix (Fin 8) (Fin 8) k))
          = ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
              (S * (B : Matrix (Fin 8) (Fin 8) k)) *
            (((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *
              (B' : Matrix (Fin 8) (Fin 8) k)) := by
            rw [← e1]
        _ = ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) * S *
            ((B : Matrix (Fin 8) (Fin 8) k) *
              ((B⁻¹ : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k)) *
            (B' : Matrix (Fin 8) (Fin 8) k) := by simp only [mul_assoc]
        _ = _ := by rw [hBB', mul_one]
    exact L.trans R.symm
  obtain ⟨c, hc⟩ := d4b_scalar k ((B⁻¹ * B' : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k)
    (fun i s => by
      have hm : d4bSimple i s < d4Certificate.roots.length := by
        cases s <;> fin_cases i <;> decide
      have := hcomm (Finsupp.single (toLabel d4Certificate_check (.inr ⟨d4bSimple i s, hm⟩)) 1)
      rwa [d4bθ_simple k i s hm] at this)
  have hdet := d4b_det_Ω k (B⁻¹ * B') (Subgroup.mul_mem _ (Subgroup.inv_mem _ hB) hB')
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc1 : c = 1 := eq_one_of_pow_eight_eq_one k hdet
  have hD1 : B⁻¹ * B' = 1 := Units.ext (by rw [hc, hc1, one_smul]; rfl)
  exact inv_mul_eq_one.1 hD1

noncomputable def d48bΨ :
    ↥(adjointGroup Tag.D4 k) →* GL (Fin 8) k :=
  MonoidHom.mk' (fun A => Classical.choose (d4b_exists_partner k A.1 A.2)) (by
    intro A A'
    obtain ⟨hB, hr⟩ := Classical.choose_spec (d4b_exists_partner k A.1 A.2)
    obtain ⟨hB', hr'⟩ := Classical.choose_spec (d4b_exists_partner k A'.1 A'.2)
    obtain ⟨hB'', hr''⟩ := Classical.choose_spec (d4b_exists_partner k (A * A').1 (A * A').2)
    exact d48b_rel_unique k hB'' (Subgroup.mul_mem _ hB hB') hr'' (d4b_rel_mul k hr hr'))

theorem d48bΨ_mem
    (A : ↥(adjointGroup Tag.D4 k)) : d48bΨ k A ∈ d4bΩ k :=
  (Classical.choose_spec (d4b_exists_partner k A.1 A.2)).1

theorem d48bΨ_rel
    (A : ↥(adjointGroup Tag.D4 k)) : D4bRel k A.1 (d48bΨ k A) :=
  (Classical.choose_spec (d4b_exists_partner k A.1 A.2)).2

theorem d48bΨ_eq
    (A : ↥(adjointGroup Tag.D4 k)) {B : GL (Fin 8) k}
    (hB : B ∈ d4bΩ k) (h : D4bRel k A.1 B) : d48bΨ k A = B :=
  d48b_rel_unique k (d48bΨ_mem k A) hB (d48bΨ_rel k A) h

theorem d48bΨ_of_xOp
    (A : ↥(adjointGroup Tag.D4 k))
    (i : Fin Tag.D4.rank) (c : k)
    (h : (A.1 : Module.End k (RootModule Tag.D4 k)) = xOp Tag.D4 k i c) :
    d48bΨ k A = d4bNat k i true c :=
  d48bΨ_eq k A (d4bNat_mem k i true c) (d4b_rel_of_xOp k i c A.1 h)

theorem d48bΨ_of_yOp
    (A : ↥(adjointGroup Tag.D4 k))
    (i : Fin Tag.D4.rank) (c : k)
    (h : (A.1 : Module.End k (RootModule Tag.D4 k)) = yOp Tag.D4 k i c) :
    d48bΨ k A = d4bNat k i false c :=
  d48bΨ_eq k A (d4bNat_mem k i false c) (d4b_rel_of_yOp k i c A.1 h)

end Unique

section Values

variable {k : Type} [Field k] [CharP k 2]

@[expose] noncomputable def d48bΨ' :
    ↥(adjointGroup d4 k) →* GL (Fin 8) k := d48bΨ k

theorem d48bΨ_xPar_pos
    (i : Fin d4.rank) (c : k) :
    d48bΨ' (k := k) (xPar (rootOperatorFamily d4) (Pi.single i 1) c) = d4bNat k i true c := by
  rw [xPar_simple, eltElement_simpleRoot]
  exact d48bΨ_of_xOp k _ i c rfl

theorem d48bΨ_xPar_neg
    (i : Fin d4.rank) (c : k) :
    d48bΨ' (k := k) (xPar (rootOperatorFamily d4) (-Pi.single i 1) c) = d4bNat k i false c := by
  have e : xPar (rootOperatorFamily d4) (-Pi.single i 1) c = yElement i c :=
    (xPar_neg_simple i c).trans (Subtype.ext ((rootOperatorFamily d4).eltUnit_neg_simple i c))
  rw [e]
  exact d48bΨ_of_yOp k _ i c rfl

end Values

end CFSG.AGLEmbedding.ChevOuterD48

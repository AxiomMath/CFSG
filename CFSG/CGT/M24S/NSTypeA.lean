module

public import CFSG.CGT.M24S.NSOrbit5

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {G : Type} [Group G] {T H : Subgroup G} {t : G} (c : NatCoord T H t)

theorem blk_inv_of_sq {l : G} (hl : l ∈ H ⊓ Subgroup.centralizer ({t} : Set G))
    (h : blk (c.mat l) * blk (c.mat l) = 1) : blk (c.mat l⁻¹) = blk (c.mat l) := by
  calc blk (c.mat l⁻¹) = blk (c.mat l⁻¹) * (blk (c.mat l) * blk (c.mat l)) := by
        rw [h, mul_one]
    _ = blk (c.mat l) := by rw [← mul_assoc, blk_inv_mul c hl, one_mul]

theorem sq_commutator_eq_t [Finite G] (hN : NaturalSL T H 4 1) (hns : ¬ HasComplement T H)
    {l e : G} {k f : Fin 3 → ZMod 2} (hk : k ≠ 0) (hf : f ≠ 0) (hfk : f ⬝ᵥ k = 0)
    (hl : l ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) (hlB : blk (c.mat l) = lv k f)
    (he : e ∈ c.E) (hek : top (c.mat e) ⬝ᵥ k = 1) : (e * l * e⁻¹ * l⁻¹) ^ 2 = t := by
  have hl2 : blk (c.mat l) * blk (c.mat l) = 1 := by rw [hlB]; exact lv_mul_self hfk
  have hx : l * e⁻¹ * l⁻¹ ∈ c.E := c.conj_mem_E hl (c.E.inv_mem he)
  have hyE : e * l * e⁻¹ * l⁻¹ ∈ c.E := by
    rw [show e * l * e⁻¹ * l⁻¹ = e * (l * e⁻¹ * l⁻¹) by group]
    exact c.E.mul_mem he hx
  have hyv : top (c.mat (e * l * e⁻¹ * l⁻¹)) = f := by
    rw [show e * l * e⁻¹ * l⁻¹ = e * (l * e⁻¹ * l⁻¹) by group, top_mul_of_mem_E c he hx,
      top_conj c hl (c.E.inv_mem he), top_inv_of_mem_E c he, blk_inv_of_sq c hl hl2, hlB,
      vecMul_lv, hek, one_smul, ← add_assoc, vec_add_self, zero_add]
  rcases c.sq_eq_one_or_eq_z hyE with h | h
  swap
  · exact h
  exfalso
  set y := e * l * e⁻¹ * l⁻¹ with hy
  have hover : Over c f y := ⟨hyE, hyv, h⟩
  have hd := moves_of_ne_zero c hN hns hf l hl k hfk hlB y hover
  have hT := mem_T_of_fix c hl hyE (by rw [hyv, hlB]; exact vecMul_lv_self hfk)
  have hm : l * l ∈ c.E := mem_E_of_blk_eq_one c (mul_mem hl hl)
    (by rw [blk_mul_of_mem c hl hl.1, hl2])
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h)
  have e1 : l * y * l⁻¹ = (l * e * l⁻¹) * ((l * l) * e⁻¹ * (l * l)⁻¹) := by rw [hy]; group
  have e2 : (l * e * l⁻¹) * e⁻¹ = y⁻¹ := by rw [hy]; group
  have hfix : l * y * l⁻¹ = y ∨ l * y * l⁻¹ = y * t := by
    rcases conj_mem_E_eq c hm (c.E.inv_mem he) with h1 | h1 <;> rw [e1, h1]
    · left
      rw [e2, hyi]
    · right
      rw [← mul_assoc, e2, hyi]
  rw [(disp_eq_zero_iff c hT).2 hfix] at hd
  exact hk hd.symm

theorem mk4_mul (a b : Fin 3 → ZMod 2) (B C : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    mk4 a B * mk4 b C = mk4 (b + vecMul a C) (B * C) := by
  refine eq_of_mulVec_e0 _ _ ?_ (mk4_mulVec_e0 _ _) ?_ ?_
  · rw [← mulVec_mulVec, mk4_mulVec_e0, mk4_mulVec_e0]
  · rw [blk_mul _ _ (mk4_mulVec_e0 _ _), blk_mk4, blk_mk4, blk_mk4]
  · rw [top_mul _ _ (mk4_mulVec_e0 _ _), top_mk4, top_mk4, blk_mk4, top_mk4]

theorem det_eq_one_of_mul_eq_one {P Q : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : P * Q = 1) :
    P.det = 1 := by
  rcases zmod_two_eq_zero_or_one P.det with h0 | h0
  · have h1 := congrArg Matrix.det h
    rw [det_mul, h0, zero_mul, det_one] at h1
    exact absurd h1 zero_ne_one
  · exact h0

theorem mk4_mul_mk4_eq_one {P Q : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : P * Q = 1) :
    mk4 0 P * mk4 0 Q = 1 := by
  rw [mk4_mul, zero_vecMul, add_zero, h, mk4_zero_one]

noncomputable def conjCoord (P Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hPQ : P * Q = 1) :
    NatCoord T H t :=
  let A' : SL(4, ZMod 2) := ⟨mk4 0 P, by rw [det_mk4, det_eq_one_of_mul_eq_one hPQ]⟩
  have hQP : Q * P = 1 := mul_eq_one_comm.mp hPQ
  have hinv : ((A'⁻¹ : SL(4, ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) * mk4 0 P = 1 :=
    congrArg (fun g : SL(4, ZMod 2) => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
      (inv_mul_cancel A')
  let σ : (Fin 4 → ZMod 2) ≃+ (Fin 4 → ZMod 2) :=
    { toFun := fun w => mk4 0 P *ᵥ w
      invFun := fun w => mk4 0 Q *ᵥ w
      left_inv := fun w => by
        simp only [mulVec_mulVec, mk4_mul_mk4_eq_one hQP, one_mulVec]
      right_inv := fun w => by
        simp only [mulVec_mulVec, mk4_mul_mk4_eq_one hPQ, one_mulVec]
      map_add' := fun w w' => mulVec_add _ w w' }
  { le := c.le
    ρ := (MulAut.conj A').toMonoidHom.comp c.ρ
    ψ := c.ψ.trans (AddEquiv.toMultiplicative σ)
    ker_iff := fun h => by
      change MulAut.conj A' (c.ρ h) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff]
      exact c.ker_iff h
    surj := fun g => by
      obtain ⟨h, hh⟩ := c.surj ((MulAut.conj A').symm g)
      exact ⟨h, by change MulAut.conj A' (c.ρ h) = g; rw [hh, MulEquiv.apply_symm_apply]⟩
    compat := fun h t' hm => by
      change mk4 0 P *ᵥ (Multiplicative.toAdd (c.ψ ⟨_, hm⟩)) =
        (mk4 0 P * (c.ρ h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
          ((A'⁻¹ : SL(4, ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) *ᵥ
            (mk4 0 P *ᵥ Multiplicative.toAdd (c.ψ t'))
      rw [c.compat h t' hm, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc _ _ (mk4 0 P), hinv,
        Matrix.mul_one]
    mem := c.mem
    ψ_z := by
      change mk4 0 P *ᵥ Multiplicative.toAdd (c.ψ ⟨t, c.mem⟩) = e0
      rw [c.ψ_z, mk4_mulVec_e0] }

theorem conjCoord_vec {P Q : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hPQ : P * Q = 1) {s : G}
    (hs : s ∈ T) : (conjCoord c P Q hPQ).vec s = mk4 0 P *ᵥ c.vec s := by
  rw [NatCoord.vec_of_mem _ hs, c.vec_of_mem hs]
  rfl

theorem eq_of_forall_mulVec {M M' : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : ∀ w, M *ᵥ w = M' *ᵥ w) : M = M' := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  rwa [mulVec_single_one, mulVec_single_one] at h1

theorem conjCoord_mat {P Q : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hPQ : P * Q = 1) {x : G}
    (hx : x ∈ H) : (conjCoord c P Q hPQ).mat x = mk4 0 P * c.mat x * mk4 0 Q := by
  have hQP : Q * P = 1 := mul_eq_one_comm.mp hPQ
  apply eq_of_forall_mulVec
  intro w
  obtain ⟨s, hs, rfl⟩ := (conjCoord c P Q hPQ).exists_vec_eq w
  rw [← NatCoord.vec_conj _ hx hs, conjCoord_vec c hPQ (c.conj_mem hx hs), conjCoord_vec c hPQ hs,
    c.vec_conj hx hs, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (mk4 0 P * c.mat x),
    mk4_mul_mk4_eq_one hQP, Matrix.mul_one, ← mulVec_mulVec]

theorem conjCoord_mat_of_mem {P Q : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hPQ : P * Q = 1) {x : G}
    (hx : x ∈ H ⊓ Subgroup.centralizer ({t} : Set G)) :
    (conjCoord c P Q hPQ).mat x = mk4 (vecMul (top (c.mat x)) Q) (P * blk (c.mat x) * Q) := by
  rw [conjCoord_mat c hPQ hx.1, eq_mk4 _ (c.mat_mulVec_e0 hx), mk4_mul, mk4_mul, zero_vecMul,
    add_zero, zero_add, top_mk4, blk_mk4]

theorem exists_coord_top {x : G} (hx : x ∈ c.E) (ha : top (c.mat x) ≠ 0) :
    ∃ c' : NatCoord T H t, x ∈ c'.E ∧ top (c'.mat x) = v₀ := by
  obtain ⟨B, hB1, hBv⟩ := exists_vecMul_eq_v₀ _ ha
  have hPQ : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B (by rw [hB1]; exact isUnit_one)
  have hxK := c.E_le hx
  have hm := conjCoord_mat_of_mem c hPQ hxK
  rw [c.blk_of_mem_E hx, Matrix.mul_one, hPQ] at hm
  refine ⟨conjCoord c B⁻¹ B hPQ, (NatCoord.mem_E_iff _).2 ⟨hxK.1, ?_, ?_⟩, ?_⟩
  · rw [hm, mk4_mulVec_e0]
  · rw [hm, blk_mk4]
  · rw [hm, top_mk4, hBv]

theorem exists_coord_blk {x : G} (hx : x ∈ H ⊓ Subgroup.centralizer ({t} : Set G))
    (h2 : blk (c.mat x) * blk (c.mat x) = 1) (h1 : blk (c.mat x) ≠ 1) :
    ∃ c' : NatCoord T H t, blk (c'.mat x) = ℓ₀ := by
  obtain ⟨P, hP1, hPB⟩ := conjToℓ₀_of_involution _ h2 h1
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (by rw [hP1]; exact isUnit_one)
  refine ⟨conjCoord c P P⁻¹ hPQ, ?_⟩
  rw [conjCoord_mat_of_mem c hPQ hx, blk_mk4, hPB, Matrix.mul_assoc, hPQ, Matrix.mul_one]

end CFSG.CGT.M24S.NSB

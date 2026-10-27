module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModBlock

@[expose] public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod

open Matrix Equiv CFSG.QuasithinUnique

def d5fun (c : Fin 4 → ZMod 2) : Fin 5 → ZMod 2 :=
  fun i => if h : (i : ℕ) < 4 then c ⟨i, h⟩ else ∑ t, c t

theorem d5fun_sum : ∀ c : Fin 4 → ZMod 2, ∑ i, d5fun c i = 0 := by decide +kernel

theorem d5fun_add : ∀ c c' : Fin 4 → ZMod 2, d5fun (c + c') = d5fun c + d5fun c' := by
  decide +kernel

theorem d5fun_inv : ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → d5fun (fun t => x t.castSucc) = x := by
  decide +kernel

theorem d5fun_equivariant : ∀ (g : A5) (c : Fin 4 → ZMod 2) (i : Fin 5),
    d5fun (fun s => ∑ t, Dm g s t * c t) i = d5fun c (((g : Perm (Fin 5))⁻¹) i) := by
  decide +kernel

theorem mem_evenWeight_iff {m : ℕ} (x : Fin m → ZMod 2) : x ∈ evenWeight m ↔ ∑ i, x i = 0 := by
  simp [evenWeight]

def d5 : (Fin 4 → ZMod 2) ≃+ ↥(evenWeight 5) where
  toFun c := ⟨d5fun c, (mem_evenWeight_iff _).mpr (d5fun_sum c)⟩
  invFun x := fun t => (x : Fin 5 → ZMod 2) t.castSucc
  left_inv c := by
    funext t
    simp [d5fun]
  right_inv x := by
    apply Subtype.ext
    exact d5fun_inv x ((mem_evenWeight_iff _).mp x.2)
  map_add' c c' := by
    apply Subtype.ext
    exact d5fun_add c c'

section Class

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [DistribMulAction A5 W]
  [SMulCommClass A5 (ZMod 2) W]

theorem triv_block_false (b : Fin 6) (y : Fin 15 → W) (hR1 : ∀ g k, g • y k = ∑ l, Mt g l k • y l)
    (hy0 : ∀ k, blk k < b → y k = 0)
    (hspan : Submodule.span (ZMod 2) {z | ∃ k : Fin 15, blk k = b ∧ z = y k} = ⊤)
    (k0 : Fin 15) (hk : ∀ k, blk k = b ↔ k = k0) (hd : ∀ g, Mt g k0 k0 = 1)
    (hact : ∃ (g : A5) (w : W), g • w ≠ w) : False := by
  have hfix : ∀ g : A5, g • y k0 = y k0 := by
    intro g
    rw [hR1, Finset.sum_eq_single k0]
    · rw [hd, one_smul]
    · intro l _ hl
      have hlb : blk l ≠ b := fun h => hl ((hk l).mp h)
      rcases lt_or_gt_of_ne hlb with h | h
      · rw [hy0 l h, smul_zero]
      · rw [Mt_tri g l k0 (by rw [(hk k0).mpr rfl]; exact h), zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  obtain ⟨g, w, hgw⟩ := hact
  have hall : ∀ w ∈ Submodule.span (ZMod 2) {z | ∃ k : Fin 15, blk k = b ∧ z = y k}, g • w = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, hkb, rfl⟩ := hz
      rw [(hk k).mp hkb]
      exact hfix g
    | zero => exact smul_zero g
    | add a b _ _ ha hb => rw [smul_add, ha, hb]
    | smul c a _ ha => rw [smul_comm, ha]
  exact hgw (hall w (by rw [hspan]; exact Submodule.mem_top))

theorem mat_assoc4 (A B : Fin 4 → Fin 4 → ZMod 2) (c : Fin 4 → ZMod 2) (s : Fin 4) :
    ∑ t, A s t * ∑ u, B t u * c u = ∑ u, (∑ t, A s t * B t u) * c u := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun t _ => ?_
  ring

theorem nat_case (ψ : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] W) (o : ℕ) (om : Fin 4 → Fin 4 → ZMod 2)
    (hψ : ∀ g c, ψ (fun s => ∑ t, bm o g s t * c t) = g • ψ c)
    (hcomm : ∀ (g : A5) (l k : Fin 4), ∑ t, om l t * bm o g t k = ∑ t, bm o g l t * om t k)
    (hsq : ∀ l k : Fin 4, ∑ t, om l t * om t k + om l k + (if l = k then 1 else 0) = 0) :
    ∃ ω : W →ₗ[ZMod 2] W, (∀ (g : A5) (w : W), ω (g • w) = g • ω w) ∧
      (∀ w : W, ω (ω w) + ω w + w = 0) ∧ Nat.card W = 16 := by
  classical
  let M : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) := Matrix.mulVecLin (Matrix.of om)
  have hMapp : ∀ c s, M c s = ∑ t, om s t * c t := fun c s => by
    simp [M, Matrix.mulVec, dotProduct]
  have hM : ∀ c, M c = fun s => ∑ t, om s t * c t := fun c => funext (hMapp c)
  have hMρ : ∀ (g : A5) c, M (fun s => ∑ t, bm o g s t * c t) =
      fun s => ∑ t, bm o g s t * (M c) t := by
    intro g c
    funext s
    rw [hMapp]
    simp only [hMapp]
    rw [mat_assoc4, mat_assoc4]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hcomm g s u]
  refine ⟨ψ.toLinearMap ∘ₗ M ∘ₗ ψ.symm.toLinearMap, ?_, ?_, ?_⟩
  · intro g w
    obtain ⟨c, rfl⟩ := ψ.surjective w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← hψ, LinearEquiv.symm_apply_apply, hMρ, hψ]
  · intro w
    obtain ⟨c, rfl⟩ := ψ.surjective w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← map_add, ← map_add]
    have : M (M c) + M c + c = 0 := by
      funext s
      simp only [Pi.add_apply, Pi.zero_apply, hMapp]
      have e : c s = ∑ u, (if s = u then (1 : ZMod 2) else 0) * c u := by simp
      rw [e]
      simp only [mat_assoc4]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [← add_mul, ← add_mul, hsq s u, zero_mul]
    rw [this, map_zero]
  · rw [Nat.card_congr ψ.symm.toEquiv]
    simp

theorem delta_case (ψ : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] W)
    (hψ : ∀ g c, ψ (fun s => ∑ t, bm 11 g s t * c t) = g • ψ c) :
    ∃ φ : W ≃+ ↥(evenWeight 5), ∀ (g : A5) (w : W) (i : Fin 5),
      ((φ (g • w) : ↥(evenWeight 5)) : Fin 5 → ZMod 2) i =
        ((φ w : ↥(evenWeight 5)) : Fin 5 → ZMod 2) (((g : Perm (Fin 5))⁻¹) i) := by
  refine ⟨ψ.symm.toAddEquiv.trans d5, ?_⟩
  intro g w i
  obtain ⟨c, rfl⟩ := ψ.surjective w
  have h1 : ψ.symm (g • ψ c) = fun s => ∑ t, bm 11 g s t * c t := by
    rw [← hψ, LinearEquiv.symm_apply_apply]
  have h2 : ψ.symm (ψ c) = c := LinearEquiv.symm_apply_apply _ _
  show d5fun (ψ.symm (g • ψ c)) i = d5fun (ψ.symm (ψ c)) _
  rw [h1, h2]
  simp_rw [bm5_eq_Dm]
  exact d5fun_equivariant g c i

theorem classify [Finite W] (hs : IsSimpleMod W) [Nontrivial W]
    (hact : ∃ (g : A5) (w : W), g • w ≠ w) :
    (∃ φ : W ≃+ ↥(evenWeight 5), ∀ (g : A5) (w : W) (i : Fin 5),
      ((φ (g • w) : ↥(evenWeight 5)) : Fin 5 → ZMod 2) i =
        ((φ w : ↥(evenWeight 5)) : Fin 5 → ZMod 2) (((g : Perm (Fin 5))⁻¹) i)) ∨
    (∃ ω : W →ₗ[ZMod 2] W, (∀ (g : A5) (w : W), ω (g • w) = g • ω w) ∧
      (∀ w : W, ω (ω w) + ω w + w = 0) ∧ Nat.card W = 16) := by
  obtain ⟨y, hR1, hR2⟩ := exists_y hs
  obtain ⟨b, hy0, hspan⟩ := exists_block hs y hR1 hR2
  fin_cases b
  · exact (triv_block_false _ y hR1 hy0 hspan 0 (by decide) Mt_triv0 hact).elim
  · obtain ⟨ψ, hψ⟩ := block4_equiv hs 1 (by norm_num) _ (by decide) simple1 y hR1 hy0 hspan
    exact Or.inr (nat_case ψ 1 om1 hψ om1_comm om1_sq)
  · exact (triv_block_false _ y hR1 hy0 hspan 5 (by decide) Mt_triv2 hact).elim
  · exact (triv_block_false _ y hR1 hy0 hspan 6 (by decide) Mt_triv3 hact).elim
  · obtain ⟨ψ, hψ⟩ := block4_equiv hs 7 (by norm_num) _ (by decide) simple4 y hR1 hy0 hspan
    exact Or.inr (nat_case ψ 7 om4 hψ om4_comm om4_sq)
  · obtain ⟨ψ, hψ⟩ := block4_equiv hs 11 (by norm_num) _ (by decide) simple5 y hR1 hy0 hspan
    exact Or.inl (delta_case ψ hψ)

end Class

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod

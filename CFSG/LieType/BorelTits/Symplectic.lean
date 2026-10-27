module

public import CFSG.LieType.BorelTits.IsotropicKernel
public import CFSG.LieType.BorelTits.Matrix
public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LieType.BorelTits

universe u v w

section Alternating

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

namespace ReflForm

variable (F : ReflForm K V)

theorem β_swap_of_alt (halt : ∀ v, F.β v v = 0) (u v : V) : F.β v u = -F.β u v := by
  have h := halt (u + v)
  rw [F.add_left, F.add_right, F.add_right, halt u, halt v] at h
  linear_combination h

theorem β_transvection (hσ : F.σ = RingEquiv.refl K) (halt : ∀ v, F.β v v = 0) (x u v : V) :
    F.β (u + F.β x u • x) (v + F.β x v • x) = F.β u v := by
  have hs : ∀ (a : K) (w w' : V), F.β (a • w) w' = a * F.β w w' := fun a w w' => by
    rw [F.smul_left, hσ]
    rfl
  simp only [F.add_left, F.add_right, hs, F.smul_right, halt, F.β_swap_of_alt halt x u]
  ring

theorem β_siegel (hσ : F.σ = RingEquiv.refl K) (halt : ∀ v, F.β v v = 0) {x y : V}
    (hxy : F.β x y = 0) (u v : V) :
    F.β (u + F.β x u • y + F.β y u • x) (v + F.β x v • y + F.β y v • x) = F.β u v := by
  have hs : ∀ (a : K) (w w' : V), F.β (a • w) w' = a * F.β w w' := fun a w w' => by
    rw [F.smul_left, hσ]
    rfl
  have hyx : F.β y x = 0 := F.refl _ _ hxy
  simp only [F.add_left, F.add_right, hs, F.smul_right, halt, hxy, hyx,
    F.β_swap_of_alt halt y u, F.β_swap_of_alt halt x u]
  ring

end ReflForm

variable {H : Type w} [Group H]

theorem holds_of_alternating [Finite H] [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (F : ReflForm K V) (halt : ∀ v, F.β v v = 0)
    (ρ : H →* Module.End K V) (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ)
    (htrans : ∀ x : V, ∃ h : H, ∀ v, ρ h v = v + F.β x v • x)
    (hsiegel : ∀ x y : V, F.β x y = 0 → ∃ h : H, ∀ v, ρ h v = v + F.β x v • y + F.β y v • x) :
    Holds H p := by
  refine holds_of_isoFlags F ρ p hρ hinj (fun W hW hWiso => ?_) (fun R _ _ => ?_)
  ·
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    obtain ⟨u, hu⟩ : ∃ u, F.β w u ≠ 0 := by
      by_contra! h
      exact hw0 (F.nondeg w h)
    have hu' : F.β u w ≠ 0 := fun h => hu (F.refl _ _ h)
    obtain ⟨h, hh⟩ := htrans u
    refine ⟨h, w, hwW, fun hmem => hu' (hWiso hwW u ?_)⟩
    have := sub_mem hmem hwW
    rwa [hh, add_sub_cancel_left, Submodule.smul_mem_iff _ hu'] at this
  ·
    obtain ⟨X, m, hX0, hXmono, hXiso, hXrank, hXstable, hrefine, hmax⟩ :=
      exists_isotropicChain_refining F (isoSeq F ρ R) (isoSeq_zero F ρ R) (isoSeq_mono F ρ R)
        (isoSeq_isTotallyIsotropic F ρ R)
    refine exists_sylow_normalizer_le_of_isotropicChain F ρ p hρ R X m m le_rfl hX0 hXmono hXiso
      hXrank hXstable hrefine (flagKernel ρ (isoCompletion F X m))
      (isPGroup_flagKernel ρ p hinj (isoCompletion_zero hX0 m) (isoCompletion_top hX0 m))
      ((flagKernel_le_flagStab ρ _).trans (flagStab_le_flagStab ρ fun k => ⟨min k m, ?_⟩))
      (fun k hk v hv hfix => ?_) (fun S _ hS g hg v hv => ?_)
      (fun S _ k hk hk' => absurd hk' (Nat.not_le.mpr hk))
    ·
      rw [isoCompletion_of_le (min_le_right k m)]
      rcases le_total k m with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, hXstable k h]
    ·
      by_contra hv'
      have hlt : X k < X (k + 1) := lt_of_le_of_ne (hXmono k.le_succ) fun h => by
        have h1 := hXrank k hk.le
        have h2 := hXrank (k + 1) hk
        rw [h] at h1
        omega
      obtain ⟨x, hx, hxk⟩ := IsConcreteLE.exists_of_lt hlt
      have hxx : x ∈ F.perp (X (k + 1)) := hXiso (k + 1) hx
      have hxspan : X k ⊔ K ∙ x = X (k + 1) :=
        Submodule.eq_of_le_of_finrank_eq
          (sup_le (hXmono k.le_succ) ((Submodule.span_singleton_le_iff_mem _ _).mpr hx))
          (by rw [Submodule.finrank_sup_span_singleton hxk, hXrank k hk.le, hXrank (k + 1) hk])
      by_cases hxv : F.β x v = 0
      ·
        have hv1 : v ∈ F.perp (X (k + 1)) := by
          rw [← hxspan, F.perp_sup]
          exact ⟨hv, F.mem_perp_span_singleton.mpr hxv⟩
        obtain ⟨y, hy, hyv⟩ : ∃ y ∈ F.perp (X (k + 1)), F.β y v ≠ 0 := by
          by_contra! h
          exact hv' (F.perp_perp (X (k + 1)) ▸ h)
        obtain ⟨s, hs⟩ := hsiegel x y (hy x hx)
        have := hfix s (mem_flagKernel_isoCompletion ρ hXmono hXiso hk hx hy hy 1 fun w => by
          rw [hs, one_mul])
        rw [hs, hxv, zero_smul, add_zero, add_sub_cancel_left, Submodule.smul_mem_iff _ hyv] at this
        exact hxk this
      ·
        obtain ⟨t, ht⟩ := htrans x
        have := hfix t (mem_flagKernel_isoCompletion ρ hXmono hXiso hk hx hxx hxx 0 fun w => by
          rw [ht, zero_mul, zero_smul, add_zero])
        rw [ht, add_sub_cancel_left, Submodule.smul_mem_iff _ hxv] at this
        exact hxk this
    ·
      rw [le_antisymm (fun v hv => hmax v hv (halt v)) (hXiso m)] at hv
      exact sub_mem (flagStab_apply_mem ρ (F := fun _ => X m) (hS hg) (k := 0) hv) hv

end Alternating

section Symplectic

open Matrix CFSG.Assembly.LowTwoRank

variable (n : ℕ) (K : Type) [Field K]

abbrev spJ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks 0 1 (-1) 0

theorem spJ_mul_spJ : spJ n K * spJ n K = -1 := by
  simp [spJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem dotProduct_spJ_mulVec (u v : Fin n ⊕ Fin n → K) :
    u ⬝ᵥ (spJ n K *ᵥ v) = (u ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) - (u ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inl) := by
  simp [spJ, dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec, neg_mulVec, sub_eq_add_neg]

@[expose] def spForm : ReflForm K (Fin n ⊕ Fin n → K) where
  σ := RingEquiv.refl K
  β u v := u ⬝ᵥ (spJ n K *ᵥ v)
  add_left u u' v := add_dotProduct u u' _
  smul_left c u v := smul_dotProduct c u _
  add_right u v v' := by rw [mulVec_add, dotProduct_add]
  smul_right c u v := by rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
  refl u v h := by
    rw [dotProduct_spJ_mulVec] at h ⊢
    rw [dotProduct_comm (v ∘ Sum.inl), dotProduct_comm (v ∘ Sum.inr), ← neg_sub, h, neg_zero]
  nondeg u h := by
    have hJ : u ᵥ* spJ n K = 0 := by
      ext i
      have := h (Pi.single i 1)
      rwa [dotProduct_mulVec, dotProduct_single, mul_one] at this
    have := congrArg (· ᵥ* -spJ n K) hJ
    rwa [vecMul_vecMul, Matrix.mul_neg, spJ_mul_spJ, neg_neg, vecMul_one, zero_vecMul] at this

theorem spForm_β (u v : Fin n ⊕ Fin n → K) : (spForm n K).β u v = u ⬝ᵥ (spJ n K *ᵥ v) :=
  rfl

theorem spForm_self (v : Fin n ⊕ Fin n → K) : (spForm n K).β v v = 0 := by
  rw [spForm_β, dotProduct_spJ_mulVec, dotProduct_comm, sub_self]

variable {n K} in
theorem transpose_mul_mul_of_mem_statedSp {A : GL (Fin n ⊕ Fin n) K} (hA : A ∈ StatedSp n K) :
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * spJ n K *
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = spJ n K := by
  have hassoc : ∀ a b c d e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K,
      a * b * c * (d * e) = a * (b * c * d) * e := fun _ _ _ _ _ => by
    simp only [Matrix.mul_assoc]
  induction hA using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => simp
  | mul x y _ _ hx hy => rw [Units.val_mul, transpose_mul, hassoc, hx, hy]
  | inv x _ hx =>
    set a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := ↑x
    set b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := ↑x⁻¹
    have hab : a * b = 1 := Units.mul_inv x
    calc bᵀ * spJ n K * b = bᵀ * (aᵀ * spJ n K * a) * b := by rw [hx]
      _ = (a * b)ᵀ * spJ n K * (a * b) := by rw [transpose_mul, hassoc]
      _ = spJ n K := by rw [hab, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem isIsometric_natRep_statedSp : IsIsometric (spForm n K) (natRep (StatedSp n K)) := by
  intro h u v
  rw [spForm_β, spForm_β, natRep_apply, natRep_apply, mulVec_mulVec, dotProduct_mulVec,
    ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc,
    transpose_mul_mul_of_mem_statedSp h.2, ← dotProduct_mulVec]

theorem exists_natRep_eq_of_isometry (f : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))
    (hf : ∀ u v, (spForm n K).β (f u) (f v) = (spForm n K).β u v) :
    ∃ g : StatedSp n K, ∀ v, natRep (StatedSp n K) g v = f v := by
  set M := LinearMap.toMatrix' f
  have hMv : ∀ v, M *ᵥ v = f v := LinearMap.toMatrix'_mulVec f
  have hM : Mᵀ * spJ n K * M = spJ n K := by
    refine ext_iff_mulVec.mpr fun v => dotProduct_eq_iff.mp fun u => ?_
    rw [dotProduct_comm _ u, dotProduct_comm _ u, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec, vecMul_transpose, hMv, hMv]
    exact hf u v
  have hinv : -(spJ n K * Mᵀ * spJ n K) * M = 1 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, hM,
      spJ_mul_spJ, neg_neg]
  let g : GL (Fin n ⊕ Fin n) K := ⟨M, _, mul_eq_one_comm.mp hinv, hinv⟩
  exact ⟨⟨g, Subgroup.subset_closure hM⟩, fun v => by rw [natRep_apply]; exact hMv v⟩

theorem holds_statedSp [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    Holds (StatedSp n K) p := by
  have hσ : (spForm n K).σ = RingEquiv.refl K := rfl
  refine holds_of_alternating p (spForm n K) (spForm_self n K) (natRep _)
    (isIsometric_natRep_statedSp n K) (natRep_injective _) (fun x => ?_) (fun x y hxy => ?_)
  · exact exists_natRep_eq_of_isometry n K
      { toFun := fun v => v + (spForm n K).β x v • x
        map_add' := fun u v => by
          simp only [(spForm n K).add_right, add_smul]
          abel
        map_smul' := fun a v => by
          simp only [(spForm n K).smul_right, RingHom.id_apply, smul_add, smul_smul] }
      ((spForm n K).β_transvection hσ (spForm_self n K) x)
  · exact exists_natRep_eq_of_isometry n K
      { toFun := fun v => v + (spForm n K).β x v • y + (spForm n K).β y v • x
        map_add' := fun u v => by
          simp only [(spForm n K).add_right, add_smul]
          abel
        map_smul' := fun a v => by
          simp only [(spForm n K).smul_right, RingHom.id_apply, smul_add, smul_smul] }
      ((spForm n K).β_siegel hσ (spForm_self n K) hxy)

theorem holds_statedProj_statedSp [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    Holds (StatedProj (StatedSp n K)) p :=
  Holds.statedProj _ (holds_statedSp n K p)

end Symplectic

end CFSG.LieType.BorelTits

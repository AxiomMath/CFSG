module

public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Nodes
public import CFSG.ClassicalInvolution.WeakCT.TwistedAssembly
public import CFSG.ClassicalInvolution.WeakCT.Standard

public noncomputable section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.LieType.Universal CFSG.LieType.CurtisTits MinData.Valid
open CFSG.ClassicalInvolution.Models.TwistedPairs
  (fixedField liftSL liftSL_injective map_liftSL liftSL_torusHom)
open scoped MatrixGroups

section SL3

variable {K : Type} [Field K] {H : Type*} [Group H]

theorem hom_ext_sl3 {f g : SL(3, K) →* H} (h0 : f.comp (blk K 0) = g.comp (blk K 0))
    (h1 : f.comp (blk K 1) = g.comp (blk K 1)) : f = g := by
  have hle : B12 K ⊔ B23 K ≤ MonoidHom.eqLocus f g := by
    refine sup_le ?_ ?_
    · rintro _ ⟨A, rfl⟩
      exact DFunLike.congr_fun h0 A
    · rintro _ ⟨A, rfl⟩
      exact DFunLike.congr_fun h1 A
  refine MonoidHom.ext fun x => hle ?_
  rw [B12_sup_B23 (K := K)]
  exact Subgroup.mem_top x

theorem commute_of_blk (f g : SL(3, K) →* H)
    (h : ∀ (s t : Fin 2) (A B : SL(2, K)), Commute (f (blk K s A)) (g (blk K t B))) :
    ∀ A B, Commute (f A) (g B) := by
  have step1 : ∀ (s : Fin 2) (A : SL(2, K)) (B : SL(3, K)), Commute (f (blk K s A)) (g B) := by
    intro s A B
    have hle : B12 K ⊔ B23 K ≤
        (Subgroup.centralizer ({f (blk K s A)} : Set H)).comap g := by
      refine sup_le ?_ ?_
      · rintro _ ⟨C, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.2 (h s 0 A C).symm.eq
      · rintro _ ⟨C, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.2 (h s 1 A C).symm.eq
    have hB : B ∈ (Subgroup.centralizer ({f (blk K s A)} : Set H)).comap g := by
      refine hle ?_
      rw [B12_sup_B23 (K := K)]
      exact Subgroup.mem_top B
    exact (Subgroup.mem_centralizer_singleton_iff.1 hB).symm
  intro A B
  have hle : B12 K ⊔ B23 K ≤ (Subgroup.centralizer (g.range : Set H)).comap f := by
    refine sup_le ?_ ?_
    · rintro _ ⟨C, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ ⟨D, rfl⟩
      exact (step1 0 C D).symm.eq
    · rintro _ ⟨C, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ ⟨D, rfl⟩
      exact (step1 1 C D).symm.eq
  have hA : A ∈ (Subgroup.centralizer (g.range : Set H)).comap f := by
    refine hle ?_
    rw [B12_sup_B23 (K := K)]
    exact Subgroup.mem_top A
  exact (Subgroup.mem_centralizer_iff.1 hA (g B) ⟨B, rfl⟩).symm

end SL3

section E6

variable {k : Type} [Field k]

theorem e6Rank1_hm (a : Fin (Tag.rank .E6)) (t : kˣ) :
    e6Rank1 k a (torusHom k t) = e6Data_valid.hm k a t := by
  refine e6Data_valid.endo_injective k ?_
  change e6Data_valid.blockOp k a ((torusHom k t : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
    e6Data_valid.endo k (e6Data_valid.hm k a t)
  rw [coe_torusHom, e6Data_valid.blockOp_diag, e6Data_valid.endo_hm]

theorem commute_xm_orth {a b : Fin (Tag.rank .E6)} (hne : a ≠ b) (hc : Tag.cartan .E6 a b = 0)
    {s s' : ℤ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (c d : k) :
    Commute (e6Data_valid.xm k (s • Pi.single a 1) c)
      (e6Data_valid.xm k (s' • Pi.single b 1) d) := by
  have hroot : ∀ (x : Fin (Tag.rank .E6)) (t : ℤ), (t = 1 ∨ t = -1) →
      IsRoot .E6 (t • Pi.single x 1) := fun x t ht => by
    rcases ht with rfl | rfl
    · rw [one_smul]; exact .basis x
    · rw [neg_one_smul]; exact isRoot_neg_single _ x
  have key : ∀ a b : Fin (Tag.rank .E6), a ≠ b → Tag.cartan .E6 a b = 0 →
      ∀ ε ε' : ℤ, (ε = 1 ∨ ε = -1) → (ε' = 1 ∨ ε' = -1) →
        ε • (Pi.single a 1 : Fin (Tag.rank .E6) → ℤ) + ε' • Pi.single b 1 ≠ 0 ∧
          MinData.toWeight (ε • (Pi.single a 1 : Fin (Tag.rank .E6) → ℤ) + ε' • Pi.single b 1) ⬝ᵥ
            (ε • (Pi.single a 1 : Fin (Tag.rank .E6) → ℤ) + ε' • Pi.single b 1) ≠ 2 := by
    intro a b hne hc ε ε' hε hε'
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> fin_cases a <;> fin_cases b <;>
      first | exact absurd rfl hne | (revert hne hc; decide)
  obtain ⟨h1, h2⟩ := key a b hne hc s s' hs hs'
  exact commute_xm (hroot a s hs) (hroot b s' hs') h1 (not_isRoot_of_form h2) c d

theorem commute_e6Rank1 {a b : Fin (Tag.rank .E6)} (hne : a ≠ b) (hc : Tag.cartan .E6 a b = 0)
    (A B : SL(2, k)) : Commute (e6Rank1 k a A) (e6Rank1 k b B) := by
  refine commute_of_tv₂ (e6Rank1 k a) (e6Rank1 k b) (fun c d => ?_) A B
  have h : ∀ s s' : ℤ, (s = 1 ∨ s = -1) → (s' = 1 ∨ s' = -1) →
      Commute (e6Data_valid.xm k (s • Pi.single a 1) c)
        (e6Data_valid.xm k (s' • Pi.single b 1) d) :=
    fun s s' hs hs' => commute_xm_orth hne hc hs hs' c d
  simp only [e6Rank1_tv01, e6Rank1_tv10]
  have pp := h 1 1 (Or.inl rfl) (Or.inl rfl)
  have pn := h 1 (-1) (Or.inl rfl) (Or.inr rfl)
  have np := h (-1) 1 (Or.inr rfl) (Or.inl rfl)
  have nn := h (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  simp only [one_smul, neg_one_smul] at pp pn np nn
  exact ⟨pp, pn, np, nn⟩

theorem exists_node_not_dvd : ∀ a b : Fin (Tag.rank .E6), Tag.cartan .E6 a b = -1 →
    ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E6 a l + 2 * Tag.cartan .E6 b l := by
  intro a b hc
  fin_cases a <;> fin_cases b <;> first | (exfalso; revert hc; decide) | (revert hc; decide)

theorem exists_e6Sl3 [Finite k] {a b : Fin (Tag.rank .E6)} (hab : a ≠ b)
    (hc1 : Tag.cartan .E6 a b = -1) (hc2 : Tag.cartan .E6 b a = -1) :
    ∃ Ψ : SL(3, k) →* e6Data_valid.minGroup k, Function.Injective Ψ ∧
      Ψ.comp (blk k 0) = e6Rank1 k a ∧ Ψ.comp (blk k 1) = e6Rank1 k b := by
  obtain ⟨O⟩ := e6_nonempty_commOrder k
  have hE := e6_chevalleyExtras k O _ (e6Data_valid.commutatorFormula_commC k posDef_cartan_E6 _
    (roots_eq isFiniteType_cartan_E6) O)
  obtain ⟨l, hl⟩ := exists_node_not_dvd a b hc1
  obtain ⟨Ψ, hinj, -, hv⟩ := exists_sl3Levi hE rfl hab hc1 hc2 hl
  refine ⟨Ψ, hinj, hom_ext_sl2 (fun c => ?_) (fun c => ?_), hom_ext_sl2 (fun c => ?_) (fun c => ?_)⟩
  · rw [MonoidHom.comp_apply, blk_zero_tv01, (hv c).1, e6Rank1_tv01]
  · rw [MonoidHom.comp_apply, blk_zero_tv10, (hv c).2.1, e6Rank1_tv10]
  · rw [MonoidHom.comp_apply, blk_one_tv01, (hv c).2.2.1, e6Rank1_tv01]
  · rw [MonoidHom.comp_apply, blk_one_tv10, (hv c).2.2.2, e6Rank1_tv10]

theorem sigma_comp_sl3 (θ : k →+* k) {Ψ Ψ' : SL(3, k) →* e6Data_valid.minGroup k}
    {a b a' b' : Fin (Tag.rank .E6)} (h0 : Ψ.comp (blk k 0) = e6Rank1 k a)
    (h1 : Ψ.comp (blk k 1) = e6Rank1 k b) (h0' : Ψ'.comp (blk k 0) = e6Rank1 k a')
    (h1' : Ψ'.comp (blk k 1) = e6Rank1 k b') (ha : rhoPerm a = a') (hb : rhoPerm b = b') :
    (sigma k θ).comp Ψ = Ψ'.comp (Matrix.SpecialLinearGroup.map θ) := by
  refine hom_ext_sl3 (MonoidHom.ext fun A => ?_) (MonoidHom.ext fun A => ?_)
  · have e1 : Matrix.SpecialLinearGroup.map θ (blk k 0 A) =
        blk k 0 (Matrix.SpecialLinearGroup.map θ A) := map_blk (θ : k →+* k) 0 A
    simp only [MonoidHom.comp_apply]
    rw [e1, show Ψ (blk k 0 A) = e6Rank1 k a A from DFunLike.congr_fun h0 A, sigma_e6Rank1, ha]
    exact (DFunLike.congr_fun h0' _).symm
  · have e1 : Matrix.SpecialLinearGroup.map θ (blk k 1 A) =
        blk k 1 (Matrix.SpecialLinearGroup.map θ A) := map_blk (θ : k →+* k) 1 A
    simp only [MonoidHom.comp_apply]
    rw [e1, show Ψ (blk k 1 A) = e6Rank1 k b A from DFunLike.congr_fun h1 A, sigma_e6Rank1, hb]
    exact (DFunLike.congr_fun h1' _).symm

end E6

section Twisted

variable {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

theorem wS_one_sq {K : Type} [Field K] :
    (wS (1 : Kˣ) * wS (1 : Kˣ) : SL(2, K)) = torusHom K (-1) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, wS, coe_sl2Upper, coe_sl2Lower,
    Matrix.mul_fin_two, coe_torusHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem slOrbitHom_apply {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (A : SL(2, k)) :
    (slOrbitHom θ hθ hab A : e6Data_valid.minGroup k) =
      e6Rank1 k a A * e6Rank1 k b (Matrix.SpecialLinearGroup.map θ A) := by
  change phiOrbit θ hab (slRankOne k a A) = _
  rw [phiOrbit_apply]
  change e6Rank1 k a A * sigma k θ (e6Rank1 k a A) = _
  rw [sigma_e6Rank1, rhoPerm_of_orbit hab]

theorem slOrbitHom_wS_sq {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) :
    (slOrbitHom θ hθ hab (wS (1 : kˣ) * wS (1 : kˣ)) : e6Data_valid.minGroup k) =
      e6Data_valid.hm k a (-1) * e6Data_valid.hm k b (-1) := by
  rw [slOrbitHom_apply, wS_one_sq, e6Rank1_hm]
  have : Matrix.SpecialLinearGroup.map θ (torusHom k (-1)) = torusHom k (-1) := by
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [coe_torusHom]
  rw [this, e6Rank1_hm]

theorem slOrbitHom_injective {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) :
    Function.Injective (slOrbitHom θ hθ hab) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 : e6Rank1 k a A * e6Rank1 k b (Matrix.SpecialLinearGroup.map θ A) = 1 := by
    rw [← slOrbitHom_apply θ hθ hab]
    exact congrArg Subtype.val hA
  have hcent : A ∈ Subgroup.center SL(2, k) := by
    rw [Subgroup.mem_center_iff]
    intro C
    have hy : e6Rank1 k a A = (e6Rank1 k b (Matrix.SpecialLinearGroup.map θ A))⁻¹ :=
      eq_inv_of_mul_eq_one_left h1
    have hmem : e6Rank1 k a A ∈ rankOne (e6Data_valid.rootGroup k) b := by
      rw [hy]
      exact inv_mem (slRankOne k b _).2
    have hc : Commute (e6Rank1 k a C) (e6Rank1 k a A) :=
      commute_rankOne_orbit hab (slRankOne k a C).2 hmem
    refine e6Rank1_injective a ?_
    simp only [map_mul]
    exact hc.eq
  rcases eq_one_or_eq_sq_of_mem_center hcent with h | h
  · exact h
  · have hv := slOrbitHom_wS_sq θ hθ hab
    rw [← h] at hv
    have hv1 : e6Data_valid.hm k a (-1) * e6Data_valid.hm k b (-1) = 1 := by
      rw [← hv]
      exact congrArg Subtype.val hA
    have hne : a ≠ b := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    have hu : TwistedE6.torusHom k ((Pi.mulSingle a (-1 : kˣ) : Fin (Tag.rank .E6) → kˣ) *
        (Pi.mulSingle b (-1 : kˣ) : Fin (Tag.rank .E6) → kˣ)) = 1 := by
      rw [map_mul, torusHom_mulSingle, torusHom_mulSingle]
      exact hv1
    have h2 := eq_one_of_torusHom_mem (k := k)
      (u := (Pi.mulSingle a (-1 : kˣ) : Fin (Tag.rank .E6) → kˣ) *
        (Pi.mulSingle b (-1 : kˣ) : Fin (Tag.rank .E6) → kˣ)) (a := a)
      (by rw [hu]; exact one_mem _)
    rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne, mul_one] at h2
    rw [h, wS_one_sq, h2, map_one]

theorem eq_one_of_torusHom_eq_one {u : Fin (Tag.rank .E6) → kˣ}
    (h : TwistedE6.torusHom k u = 1) (a : Fin (Tag.rank .E6)) : u a = 1 :=
  eq_one_of_torusHom_mem (by rw [h]; exact one_mem _)

theorem map_torusHom_hom (s : kˣ) :
    Matrix.SpecialLinearGroup.map θ (torusHom k s) = torusHom k (Units.map (θ : k →* k) s) := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [coe_torusHom]

theorem slOrbitHom_torusHom {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (t : kˣ) :
    (slOrbitHom θ hθ hab (torusHom k t) : e6Data_valid.minGroup k) =
      e6Data_valid.hm k a t * e6Data_valid.hm k b (Units.map (θ : k →* k) t) := by
  rw [slOrbitHom_apply, map_torusHom_hom, e6Rank1_hm, e6Rank1_hm]

theorem eq_blk_torus_of_scalar3 (ω η : kˣ) (hη : (η : k) = (ω : k) ^ 2) (h3 : (ω : k) ^ 3 = 1)
    (g : SL(3, k)) (hg : Matrix.scalar (Fin 3) (ω : k) = (g : Matrix (Fin 3) (Fin 3) k)) :
    g = blk k 0 (torusHom k ω) * blk k 1 (torusHom k η) := by
  have hω : (ω : k) ≠ 0 := ω.ne_zero
  refine Subtype.ext ?_
  rw [← hg, Matrix.SpecialLinearGroup.coe_mul]
  change _ = ((blockSL k 3 2 0 (by omega) (torusHom k ω) : SL(3, k)) : Matrix (Fin 3) (Fin 3) k) *
    ((blockSL k 3 2 1 (by omega) (torusHom k η) : SL(3, k)) : Matrix (Fin 3) (Fin 3) k)
  rw [coe_blockSL_three_zero, coe_blockSL_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, coe_torusHom, Matrix.scalar_apply,
      Units.val_inv_eq_inv_val, hη]
  all_goals field_simp
  all_goals first | ring1 | linear_combination h3

theorem commute_rFixed_slOrbitHom {a c d : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    (hcd : (c = nd 2 ∧ d = nd 4) ∨ (c = nd 0 ∧ d = nd 5)) (hac : a ≠ c) (had : a ≠ d)
    (hc : Tag.cartan .E6 a c = 0) (hd : Tag.cartan .E6 a d = 0) (A : SL(2, fixedField θ))
    (B : SL(2, k)) : Commute (rFixed θ a ha A) (slOrbitHom θ hθ hcd B) := by
  have h1 : Commute (e6Rank1 k a (liftSL θ 2 A)) (e6Rank1 k c B) := commute_e6Rank1 hac hc _ _
  have h2 : Commute (e6Rank1 k a (liftSL θ 2 A))
      (e6Rank1 k d (Matrix.SpecialLinearGroup.map θ B)) := commute_e6Rank1 had hd _ _
  refine Subtype.ext ?_
  change e6Rank1 k a (liftSL θ 2 A) * (slOrbitHom θ hθ hcd B : e6Data_valid.minGroup k) =
    (slOrbitHom θ hθ hcd B : e6Data_valid.minGroup k) * e6Rank1 k a (liftSL θ 2 A)
  rw [slOrbitHom_apply]
  exact (h1.mul_right h2).eq

theorem rFixed_wS_sq {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) :
    ((rFixed θ a ha (wS (1 : (fixedField θ)ˣ) * wS (1 : (fixedField θ)ˣ)) : fixedGroup k θ) :
      e6Data_valid.minGroup k) = e6Data_valid.hm k a (-1) := by
  rw [wS_one_sq]
  change e6Rank1 k a (liftSL θ 2 (torusHom (fixedField θ) (-1))) = _
  rw [liftSL_torusHom, e6Rank1_hm]
  congr 1

theorem rFixed_wS_sq_mem_hHat {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    {i : Fin (Tag.rank .F4)} (hi : hHatE k θ i = (hFixE θ a).range) :
    rFixed θ a ha (wS (1 : (fixedField θ)ˣ) * wS (1 : (fixedField θ)ˣ)) ∈ hHat k θ i := by
  rw [hHat, Subgroup.mem_subgroupOf, rFixed_wS_sq, hi]
  exact ⟨⟨-1, (mem_fixedUnits θ).2 (by simp)⟩, rfl⟩

theorem slOrbitHom_wS_sq_mem_hHat {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hi : hHatE k θ i = (hPairE θ a b).range) :
    slOrbitHom θ hθ hab (wS (1 : kˣ) * wS (1 : kˣ)) ∈ hHat k θ i := by
  rw [hHat, Subgroup.mem_subgroupOf, slOrbitHom_wS_sq, hi]
  refine ⟨-1, ?_⟩
  change e6Data_valid.hm k a (-1) * e6Data_valid.hm k b (Units.map (θ : k →* k) (-1)) = _
  congr 2
  exact Units.ext (by simp)

section NodeDatum

variable {X : Type} [Group X] {U : Subgroup X}

def nodeDataFixed (a : Fin (Tag.rank .E6)) (ha : rhoPerm a = a) {i : Fin (Tag.rank .F4)}
    (hai : orbitMap a = i) (ρ : SL(2, fixedField θ) →* X) (hU : ρ.range = U) :
    NodeData (twistedDatum k θ) X i U :=
  NodeData.ofParam (D := twistedDatum k θ) (k := i) (rFixed θ a ha) ρ hU (rFixed_injective θ a ha)
    (rFixed_upper θ a ha hai) (rFixed_lower θ a ha hai) (rFixed_param_upper θ a ha hai)
    (rFixed_param_lower θ a ha hai)

theorem nodeDataFixed_isParam (a : Fin (Tag.rank .E6)) (ha : rhoPerm a = a)
    {i : Fin (Tag.rank .F4)} (hai : orbitMap a = i) (ρ : SL(2, fixedField θ) →* X)
    (hU : ρ.range = U) : (nodeDataFixed θ a ha hai ρ hU).IsParam (rFixed θ a ha) ρ :=
  NodeData.ofParam_isParam (D := twistedDatum k θ) (k := i) hU (rFixed_injective θ a ha)
    (rFixed_upper θ a ha hai) (rFixed_lower θ a ha hai) (rFixed_param_upper θ a ha hai)
    (rFixed_param_lower θ a ha hai)

def nodeDataOrbit (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hai : orbitMap a = i) (ρ : SL(2, k) →* X) (hU : ρ.range = U) :
    NodeData (twistedDatum k θ) X i U :=
  NodeData.ofParam (D := twistedDatum k θ) (k := i) (slOrbitHom θ hθ hab) ρ hU
    (slOrbitHom_injective θ hθ hab) (slOrbitHom_upper_mem θ hθ hab hai)
    (slOrbitHom_lower_mem θ hθ hab hai) (slOrbitHom_param_upper θ hθ hab hai)
    (slOrbitHom_param_lower θ hθ hab hai)

theorem nodeDataOrbit_isParam (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hai : orbitMap a = i) (ρ : SL(2, k) →* X) (hU : ρ.range = U) :
    (nodeDataOrbit θ hθ hab hai ρ hU).IsParam (slOrbitHom θ hθ hab) ρ :=
  NodeData.ofParam_isParam (D := twistedDatum k θ) (k := i) hU (slOrbitHom_injective θ hθ hab)
    (slOrbitHom_upper_mem θ hθ hab hai) (slOrbitHom_lower_mem θ hθ hab hai)
    (slOrbitHom_param_upper θ hθ hab hai) (slOrbitHom_param_lower θ hθ hab hai)

end NodeDatum

theorem map_map_involution (hθ : ∀ c, θ (θ c) = c) {d : ℕ} (A : SL(d, k)) :
    Matrix.SpecialLinearGroup.map θ (Matrix.SpecialLinearGroup.map θ A) = A :=
  Subtype.ext (Matrix.ext fun _ _ => hθ _)

variable [Finite k]

theorem exists_levi01 : ∃ emb : SL(3, fixedField θ) →* fixedGroup k θ, Function.Injective emb ∧
    emb.comp (blk (fixedField θ) 0) = nodeHom0 θ ∧
      emb.comp (blk (fixedField θ) 1) = nodeHom1 θ := by
  obtain ⟨Ψ, hΨ, h0, h1⟩ := exists_e6Sl3 (k := k) (a := nd 1) (b := nd 3) (by decide)
    (by decide) (by decide)
  have hσ : (sigma k θ).comp Ψ = Ψ.comp (Matrix.SpecialLinearGroup.map θ) :=
    sigma_comp_sl3 θ h0 h1 h0 h1 rfl rfl
  have hfix : ∀ A : SL(3, fixedField θ), Ψ (liftSL θ 3 A) ∈ fixedGroup k θ := fun A => by
    rw [mem_fixedGroup]
    have := DFunLike.congr_fun hσ (liftSL θ 3 A)
    simp only [MonoidHom.comp_apply] at this
    rw [this, map_liftSL]
  refine ⟨(Ψ.comp (liftSL θ 3)).codRestrict (fixedGroup k θ) hfix, ?_, ?_, ?_⟩
  · intro A B h
    have h' : Ψ (liftSL θ 3 A) = Ψ (liftSL θ 3 B) := congrArg Subtype.val h
    exact liftSL_injective θ 3 (hΨ h')
  · refine MonoidHom.ext fun A => Subtype.ext ?_
    change Ψ (liftSL θ 3 (blk (fixedField θ) 0 A)) = e6Rank1 k (nd 1) (liftSL θ 2 A)
    rw [show liftSL θ 3 (blk (fixedField θ) 0 A) = blk k 0 (liftSL θ 2 A) from
      map_blk (fixedField θ).subtype 0 A]
    exact DFunLike.congr_fun h0 _
  · refine MonoidHom.ext fun A => Subtype.ext ?_
    change Ψ (liftSL θ 3 (blk (fixedField θ) 1 A)) = e6Rank1 k (nd 3) (liftSL θ 2 A)
    rw [show liftSL θ 3 (blk (fixedField θ) 1 A) = blk k 1 (liftSL θ 2 A) from
      map_blk (fixedField θ).subtype 1 A]
    exact DFunLike.congr_fun h1 _

theorem exists_levi23 (hθ : ∀ c, θ (θ c) = c) :
    ∃ emb : SL(3, k) →* fixedGroup k θ, Function.Injective emb ∧
      emb.comp (blk k 0) = nodeHom2 θ hθ ∧ emb.comp (blk k 1) = nodeHom3 θ hθ := by
  obtain ⟨Ψ₁, hΨ₁, h10, h11⟩ := exists_e6Sl3 (k := k) (a := nd 2) (b := nd 0) (by decide)
    (by decide) (by decide)
  obtain ⟨Ψ₂, hΨ₂, h20, h21⟩ := exists_e6Sl3 (k := k) (a := nd 4) (b := nd 5) (by decide)
    (by decide) (by decide)
  have hσ₁ : (sigma k θ).comp Ψ₁ = Ψ₂.comp (Matrix.SpecialLinearGroup.map θ) :=
    sigma_comp_sl3 θ h10 h11 h20 h21 rfl rfl
  have hσ₂ : (sigma k θ).comp Ψ₂ = Ψ₁.comp (Matrix.SpecialLinearGroup.map θ) :=
    sigma_comp_sl3 θ h20 h21 h10 h11 rfl rfl
  have hc : ∀ A B, Commute (Ψ₁ A) (Ψ₂ B) := by
    refine commute_of_blk Ψ₁ Ψ₂ (fun s t A B => ?_)
    fin_cases s <;> fin_cases t
    · show Commute (Ψ₁ (blk k 0 A)) (Ψ₂ (blk k 0 B))
      rw [show Ψ₁ (blk k 0 A) = e6Rank1 k (nd 2) A from DFunLike.congr_fun h10 A,
        show Ψ₂ (blk k 0 B) = e6Rank1 k (nd 4) B from DFunLike.congr_fun h20 B]
      exact commute_e6Rank1 (by decide) (by decide) A B
    · show Commute (Ψ₁ (blk k 0 A)) (Ψ₂ (blk k 1 B))
      rw [show Ψ₁ (blk k 0 A) = e6Rank1 k (nd 2) A from DFunLike.congr_fun h10 A,
        show Ψ₂ (blk k 1 B) = e6Rank1 k (nd 5) B from DFunLike.congr_fun h21 B]
      exact commute_e6Rank1 (by decide) (by decide) A B
    · show Commute (Ψ₁ (blk k 1 A)) (Ψ₂ (blk k 0 B))
      rw [show Ψ₁ (blk k 1 A) = e6Rank1 k (nd 0) A from DFunLike.congr_fun h11 A,
        show Ψ₂ (blk k 0 B) = e6Rank1 k (nd 4) B from DFunLike.congr_fun h20 B]
      exact commute_e6Rank1 (by decide) (by decide) A B
    · show Commute (Ψ₁ (blk k 1 A)) (Ψ₂ (blk k 1 B))
      rw [show Ψ₁ (blk k 1 A) = e6Rank1 k (nd 0) A from DFunLike.congr_fun h11 A,
        show Ψ₂ (blk k 1 B) = e6Rank1 k (nd 5) B from DFunLike.congr_fun h21 B]
      exact commute_e6Rank1 (by decide) (by decide) A B
  let emb₀ : SL(3, k) →* e6Data_valid.minGroup k :=
    (Ψ₁.noncommCoprod Ψ₂ hc).comp ((MonoidHom.id _).prod (Matrix.SpecialLinearGroup.map θ))
  have hemb₀ : ∀ A, emb₀ A = Ψ₁ A * Ψ₂ (Matrix.SpecialLinearGroup.map θ A) := fun A => rfl
  have hfix : ∀ A, emb₀ A ∈ fixedGroup k θ := fun A => by
    rw [mem_fixedGroup, hemb₀, map_mul]
    have e1 : sigma k θ (Ψ₁ A) = Ψ₂ (Matrix.SpecialLinearGroup.map θ A) :=
      DFunLike.congr_fun hσ₁ A
    have e2 : sigma k θ (Ψ₂ (Matrix.SpecialLinearGroup.map θ A)) = Ψ₁ A := by
      have := DFunLike.congr_fun hσ₂ (Matrix.SpecialLinearGroup.map θ A)
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, map_map_involution θ hθ] at this
      exact this
    rw [e1, e2]
    exact (hc A _).symm.eq
  let emb : SL(3, k) →* fixedGroup k θ := emb₀.codRestrict (fixedGroup k θ) hfix
  have hemb0 : emb.comp (blk k 0) = nodeHom2 θ hθ := by
    refine MonoidHom.ext fun A => Subtype.ext ?_
    change emb₀ (blk k 0 A) = _
    rw [hemb₀, show Ψ₁ (blk k 0 A) = e6Rank1 k (nd 2) A from DFunLike.congr_fun h10 A,
      map_blk (θ : k →+* k) 0 A, show Ψ₂ (blk k 0 (Matrix.SpecialLinearGroup.map θ A)) =
        e6Rank1 k (nd 4) (Matrix.SpecialLinearGroup.map θ A) from DFunLike.congr_fun h20 _,
      slOrbitHom_apply]
  have hemb1 : emb.comp (blk k 1) = nodeHom3 θ hθ := by
    refine MonoidHom.ext fun A => Subtype.ext ?_
    change emb₀ (blk k 1 A) = _
    rw [hemb₀, show Ψ₁ (blk k 1 A) = e6Rank1 k (nd 0) A from DFunLike.congr_fun h11 A,
      map_blk (θ : k →+* k) 1 A, show Ψ₂ (blk k 1 (Matrix.SpecialLinearGroup.map θ A)) =
        e6Rank1 k (nd 5) (Matrix.SpecialLinearGroup.map θ A) from DFunLike.congr_fun h21 _,
      slOrbitHom_apply]
  refine ⟨emb, ?_, hemb0, hemb1⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have hne : emb (blk k 0 (tv 0 1 1)) ≠ 1 := by
    rw [show emb (blk k 0 (tv 0 1 1)) = nodeHom2 θ hθ (tv 0 1 1) from
      DFunLike.congr_fun hemb0 _]
    intro h
    exact tv_zero_one_one_ne_one (slOrbitHom_injective θ hθ _ (h.trans (map_one _).symm))
  have hker : g ∈ Subgroup.center SL(3, k) :=
    ker_le_center_of_isQuasisimple (SpecialLinear.isQuasisimple 2 k le_rfl)
      ⟨_, hne⟩ hg
  obtain ⟨ω, hω3, hωg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hker
  rw [Fintype.card_fin] at hω3
  have hω0 : ω ≠ 0 := fun h => by simp [h] at hω3
  let ωu : kˣ := Units.mk0 ω hω0
  have hg' : g = blk k 0 (torusHom k ωu) * blk k 1 (torusHom k (ωu ^ 2)) :=
    eq_blk_torus_of_scalar3 ωu (ωu ^ 2) (by simp [ωu]) hω3 g hωg
  have hemb : emb g = nodeHom2 θ hθ (torusHom k ωu) * nodeHom3 θ hθ (torusHom k (ωu ^ 2)) := by
    rw [hg', map_mul]
    exact congrArg₂ (· * ·) (DFunLike.congr_fun hemb0 _) (DFunLike.congr_fun hemb1 _)
  rw [hemb] at hg
  have hv : (nodeHom2 θ hθ (torusHom k ωu) : e6Data_valid.minGroup k) *
      (nodeHom3 θ hθ (torusHom k (ωu ^ 2)) : e6Data_valid.minGroup k) = 1 :=
    congrArg Subtype.val hg
  rw [slOrbitHom_torusHom, slOrbitHom_torusHom] at hv
  have hu : TwistedE6.torusHom k
      ((Pi.mulSingle (nd 2) ωu * Pi.mulSingle (nd 4) (Units.map (θ : k →* k) ωu) :
          Fin (Tag.rank .E6) → kˣ) *
        (Pi.mulSingle (nd 0) (ωu ^ 2) * Pi.mulSingle (nd 5) (Units.map (θ : k →* k) (ωu ^ 2)) :
          Fin (Tag.rank .E6) → kˣ)) = 1 := by
    rw [map_mul, map_mul, map_mul, torusHom_mulSingle, torusHom_mulSingle, torusHom_mulSingle,
      torusHom_mulSingle]
    exact hv
  have h2 := eq_one_of_torusHom_eq_one hu (nd 2)
  have e1 : (nd 2 : Fin (Tag.rank .E6)) ≠ nd 4 := by decide
  have e2 : (nd 2 : Fin (Tag.rank .E6)) ≠ nd 0 := by decide
  have e3 : (nd 2 : Fin (Tag.rank .E6)) ≠ nd 5 := by decide
  simp [Pi.mul_apply, e1, e2, e3] at h2
  have hω1 : ω = 1 := by
    have := congrArg Units.val h2
    simpa [ωu] using this
  refine Subtype.ext ?_
  rw [← hωg, hω1]
  simp

end Twisted

end CFSG.ClassicalInvolution.WeakCT

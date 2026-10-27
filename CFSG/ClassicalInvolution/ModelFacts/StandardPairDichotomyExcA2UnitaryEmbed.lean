module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryBasic
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Data
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Universal CFSG.LieType
  CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups

section SL2Values

variable {τ : Tag} {F : Type} [Field F]

theorem tv01_eq_uSL (c : F) : (tv 0 1 c : SL(2, F)) = uSL c := by
  rw [tv01_eq_sl2Upper]
  rfl

theorem tv10_eq_vSL (c : F) : (tv 1 0 c : SL(2, F)) = vSL c := by
  rw [tv10_eq_sl2Lower]
  rfl

theorem uvu_sq (a b : F) (h : a * b = -1) :
    (uSL a * vSL b * uSL a) * (uSL a * vSL b * uSL a) = HSL (-1 : Fˣ) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp only [Matrix.SpecialLinearGroup.coe_mul] <;>
    simp [coe_HSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (2 * (a * b + 1)) * h
  · linear_combination (2 * a * (a * b + 2)) * h
  · linear_combination (2 * b) * h
  · linear_combination (2 * (a * b + 1)) * h

theorem exists_pinned_signs {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ s ε : F, s * s = 1 ∧ ε * ε = 1 ∧ ∀ z : F,
      rootSL2 τ F β (uSL z) = pinnedX τ F β (s * z) ∧
        rootSL2 τ F β (vSL z) = pinnedX τ F (-β) (ε * z) := by
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := F) hβ
  refine ⟨(((pinnedData τ β).2.2 : ℤ) : F), ε, ?_, hε, fun z => ⟨?_, hv z⟩⟩
  · rcases pinnedSign_eq τ β with h | h <;> simp [h]
  · rw [rootSL2_uSL_eq, zsmul_eq_mul]

end SL2Values

section Braid

variable {τ : Tag} {F : Type} [Field F]

theorem pinned_braid (hF : ringChar F ≠ 2) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {a b : F}
    (ha : a ≠ 0)
    (h : pinnedX τ F β a * pinnedX τ F (-β) b * pinnedX τ F β a =
      pinnedX τ F (-β) b * pinnedX τ F β a * pinnedX τ F (-β) b) :
    ∃ s ε : F, s * s = 1 ∧ ε * ε = 1 ∧ (s * a) * (ε * b) = -1 ∧ ∀ z : F,
      rootSL2 τ F β (uSL z) = pinnedX τ F β (s * z) ∧
        rootSL2 τ F β (vSL z) = pinnedX τ F (-β) (ε * z) := by
  obtain ⟨s, ε, hs, hε, hsig⟩ := exists_pinned_signs (F := F) hβ
  set ρ := rootSL2 τ F β with hρ
  have hinj : Function.Injective ρ :=
    ((exceptional_Lang_root_rank_one_data τ F β).2.2.2.2.2.2.2.1 hF).1
  have hX : ∀ c : F, pinnedX τ F β c = ρ (uSL (s * c)) := fun c => by
    rw [(hsig _).1, ← mul_assoc, hs, one_mul]
  have hY : ∀ c : F, pinnedX τ F (-β) c = ρ (vSL (ε * c)) := fun c => by
    rw [(hsig _).2, ← mul_assoc, hε, one_mul]
  rw [hX a, hY b, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h
  have hm := hinj h
  have h12 := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) hm
  simp only [uvu_apply_zero_one, vuv_apply_zero_one] at h12
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have h3 : (s * a) * (1 + (s * a) * (ε * b)) = 0 := by linear_combination h12
  have h4 := (mul_eq_zero.1 h3).resolve_left (mul_ne_zero hs0 ha)
  exact ⟨s, ε, hs, hε, by linear_combination h4, hsig⟩

theorem sl2Hom_neg_one (hF : ringChar F ≠ 2) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    {f : SL2 F →* ModGL τ F} {a b : F} (ha : a ≠ 0)
    (hu : ∀ c, f (uSL c) = pinnedX τ F β (a * c))
    (hv : ∀ c, f (vSL c) = pinnedX τ F (-β) (b * c)) :
    f (HSL (-1 : Fˣ)) = rootSL2 τ F β (HSL (-1 : Fˣ)) := by
  have hbr := congrArg f (uSL_one_mul_vSL_neg_one_mul_uSL_one (F := F))
  rw [map_mul, map_mul, map_mul, map_mul, hu, hv] at hbr
  obtain ⟨s, ε, hs, hε, hsab, hsig⟩ := pinned_braid hF hβ (a := a * 1) (b := b * -1)
    (by simpa using ha) hbr
  have hsq := uvu_sq (F := F) (s * (a * 1)) (ε * (b * -1)) hsab
  have hX : pinnedX τ F β a = rootSL2 τ F β (uSL (s * (a * 1))) := by
    rw [(hsig _).1, ← mul_assoc, hs, one_mul, mul_one]
  have hY : pinnedX τ F (-β) (-b) = rootSL2 τ F β (vSL (ε * (b * -1))) := by
    rw [(hsig _).2, ← mul_assoc, hε, one_mul, mul_neg_one]
  have hW : (uSL (1 : F) * vSL (-1) * uSL 1) * (uSL 1 * vSL (-1) * uSL 1) = HSL (-1 : Fˣ) := by
    simpa using uvu_sq (F := F) 1 (-1) (by simp)
  have h1 : f (HSL (-1 : Fˣ)) = (pinnedX τ F β (a * 1) * pinnedX τ F (-β) (b * -1) *
      pinnedX τ F β (a * 1)) * (pinnedX τ F β (a * 1) * pinnedX τ F (-β) (b * -1) *
      pinnedX τ F β (a * 1)) := by
    rw [← hW]
    simp only [map_mul, hu, hv]
  have h2 : rootSL2 τ F β (HSL (-1 : Fˣ)) = (pinnedX τ F β a * pinnedX τ F (-β) (-b) *
      pinnedX τ F β a) * (pinnedX τ F β a * pinnedX τ F (-β) (-b) * pinnedX τ F β a) := by
    rw [← hsq]
    simp only [map_mul]
    rw [← hX, ← hY]
  rw [h1, h2]
  simp only [mul_one, mul_neg]

theorem sl2Hom_mem {β : Fin τ.rank → ℤ} {f : SL2 F →* ModGL τ F} {a b : F}
    (hu : ∀ c, f (uSL c) = pinnedX τ F β (a * c))
    (hv : ∀ c, f (vSL c) = pinnedX τ F (-β) (b * c)) (hβ : IsRoot τ β) (A : SL2 F) :
    f A ∈ rootRankOneGroup τ F β := by
  rw [(exceptional_Lang_root_rank_one_torus_transport τ F hβ).1]
  have hA : A ∈ Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper F) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower F)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
    trivial
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact Subgroup.mem_sup_left (mem_rootSubgroup.2 ⟨a * c, (hu c).symm⟩)
    · exact Subgroup.mem_sup_right (mem_rootSubgroup.2 ⟨b * c, (hv c).symm⟩)
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

end Braid

section Embedding

variable {τ : Tag} {θ δ : Fin τ.rank → ℤ} {F : Type} [Field F]

variable (τ θ δ F) in
structure A2Embedding where
  ι : SL(3, F) →* ModGL τ F
  inj : Function.Injective ι
  mem : ∀ y, ι y ∈ adjointGroup τ F
  m₀ : F
  m₁ : F
  m₂ : F
  m₃ : F
  sq₀ : m₀ * m₀ = 1
  sq₁ : m₁ * m₁ = 1
  sq₂ : m₂ * m₂ = 1
  sq₃ : m₃ * m₃ = 1
  h01 : ∀ c, ι (tv 0 1 c) = pinnedX τ F θ (m₀ * c)
  h10 : ∀ c, ι (tv 1 0 c) = pinnedX τ F (-θ) (m₁ * c)
  h12 : ∀ c, ι (tv 1 2 c) = pinnedX τ F δ (m₂ * c)
  h21 : ∀ c, ι (tv 2 1 c) = pinnedX τ F (-δ) (m₃ * c)

namespace A2Embedding

variable (E : A2Embedding τ θ δ F)

theorem m₀_ne_zero : E.m₀ ≠ 0 := fun h => by
  have := E.sq₀
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem m₂_ne_zero : E.m₂ ≠ 0 := fun h => by
  have := E.sq₂
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem blk_zero_mem (hθ : IsRoot τ θ) (A : SL2 F) :
    E.ι (blk F 0 A) ∈ rootRankOneGroup τ F θ :=
  sl2Hom_mem (f := E.ι.comp (blk F 0)) (a := E.m₀) (b := E.m₁)
    (fun c => by
      change E.ι (blk F 0 (uSL c)) = _
      rw [← tv01_eq_uSL, blk_zero_tv01, E.h01])
    (fun c => by
      change E.ι (blk F 0 (vSL c)) = _
      rw [← tv10_eq_vSL, blk_zero_tv10, E.h10]) hθ A

theorem blk_zero_neg_one (hF : ringChar F ≠ 2) (hθ : IsRoot τ θ) :
    E.ι (blk F 0 (HSL (-1 : Fˣ))) = rootSL2 τ F θ (HSL (-1 : Fˣ)) :=
  sl2Hom_neg_one hF hθ (f := E.ι.comp (blk F 0)) (a := E.m₀) (b := E.m₁) E.m₀_ne_zero
    (fun c => by
      change E.ι (blk F 0 (uSL c)) = _
      rw [← tv01_eq_uSL, blk_zero_tv01, E.h01])
    (fun c => by
      change E.ι (blk F 0 (vSL c)) = _
      rw [← tv10_eq_vSL, blk_zero_tv10, E.h10])

theorem blk_one_neg_one (hF : ringChar F ≠ 2) (hδ : IsRoot τ δ) :
    E.ι (blk F 1 (HSL (-1 : Fˣ))) = rootSL2 τ F δ (HSL (-1 : Fˣ)) :=
  sl2Hom_neg_one hF hδ (f := E.ι.comp (blk F 1)) (a := E.m₂) (b := E.m₃) E.m₂_ne_zero
    (fun c => by
      change E.ι (blk F 1 (uSL c)) = _
      rw [← tv01_eq_uSL, blk_one_tv01, E.h12])
    (fun c => by
      change E.ι (blk F 1 (vSL c)) = _
      rw [← tv10_eq_vSL, blk_one_tv10, E.h21])

end A2Embedding

end Embedding

section Levi

variable {τ : Tag} {θ δ : Fin τ.rank → ℤ} {F : Type} [Field F]

theorem simpleWordAct_neg {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    simpleWordAct τ l (-v) = -simpleWordAct τ l v := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [simpleWordAct_cons, simpleWordAct_cons, ih]
    funext i
    simp only [reflect, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp [Finset.sum_neg_distrib]
    ring

theorem nonempty_a2Embedding_of_levi (w : List (Fin τ.rank)) {i j : Fin τ.rank}
    (hθ : simpleWordAct τ w (Pi.single i 1) = θ) (hδ : simpleWordAct τ w (Pi.single j 1) = δ)
    (ι₀ : SL(3, F) →* ModGL τ F) (hinj : Function.Injective ι₀)
    (hmem : ∀ y, ι₀ y ∈ adjointGroup τ F) {s₀ s₁ s₂ s₃ : F} (hs₀ : s₀ * s₀ = 1)
    (hs₁ : s₁ * s₁ = 1) (hs₂ : s₂ * s₂ = 1) (hs₃ : s₃ * s₃ = 1)
    (h01 : ∀ c, ι₀ (tv 0 1 c) = pinnedX τ F (Pi.single i 1) (s₀ * c))
    (h10 : ∀ c, ι₀ (tv 1 0 c) = pinnedX τ F (-Pi.single i 1) (s₁ * c))
    (h12 : ∀ c, ι₀ (tv 1 2 c) = pinnedX τ F (Pi.single j 1) (s₂ * c))
    (h21 : ∀ c, ι₀ (tv 2 1 c) = pinnedX τ F (-Pi.single j 1) (s₃ * c)) :
    Nonempty (A2Embedding τ θ δ F) := by
  have hr0 : IsRoot τ (Pi.single i 1 : Fin τ.rank → ℤ) := isRoot_single τ _
  have hr0' : IsRoot τ (-(Pi.single i 1 : Fin τ.rank → ℤ)) := isRoot_neg_single τ _
  have hr1 : IsRoot τ (Pi.single j 1 : Fin τ.rank → ℤ) := isRoot_single τ _
  have hr1' : IsRoot τ (-(Pi.single j 1 : Fin τ.rank → ℤ)) := isRoot_neg_single τ _
  obtain ⟨ε₀, hε₀, k₀⟩ := simpleWordElt_conj_pinnedX (F := F) w hr0
  obtain ⟨ε₁, hε₁, k₁⟩ := simpleWordElt_conj_pinnedX (F := F) w hr0'
  obtain ⟨ε₂, hε₂, k₂⟩ := simpleWordElt_conj_pinnedX (F := F) w hr1
  obtain ⟨ε₃, hε₃, k₃⟩ := simpleWordElt_conj_pinnedX (F := F) w hr1'
  rw [hθ] at k₀
  rw [simpleWordAct_neg, hθ] at k₁
  rw [hδ] at k₂
  rw [simpleWordAct_neg, hδ] at k₃
  set n := simpleWordElt τ F w with hn
  have key : ∀ {γ γ' : Fin τ.rank → ℤ} {ε s : F}, ε * ε = 1 → s * s = 1 →
      (∀ c : F, n * pinnedX τ F γ c * n⁻¹ = pinnedX τ F γ' (ε * c)) →
      ∃ m : F, m * m = 1 ∧ ∀ c : F, n * pinnedX τ F γ (s * c) * n⁻¹ = pinnedX τ F γ' (m * c) := by
    intro γ γ' ε s hε hs h
    refine ⟨ε * s, by linear_combination (ε * ε) * hs + hε, fun c => ?_⟩
    rw [h, mul_assoc]
  obtain ⟨m₀, hm₀, l₀⟩ := key hε₀ hs₀ k₀
  obtain ⟨m₁, hm₁, l₁⟩ := key hε₁ hs₁ k₁
  obtain ⟨m₂, hm₂, l₂⟩ := key hε₂ hs₂ k₂
  obtain ⟨m₃, hm₃, l₃⟩ := key hε₃ hs₃ k₃
  refine ⟨{
    ι := (MulAut.conj n).toMonoidHom.comp ι₀
    inj := fun x y hxy => hinj ((MulAut.conj n).injective hxy)
    mem := fun y => mul_mem (mul_mem (simpleWordElt_mem_adjointGroup _) (hmem y))
      (inv_mem (simpleWordElt_mem_adjointGroup _))
    m₀ := m₀, m₁ := m₁, m₂ := m₂, m₃ := m₃
    sq₀ := hm₀, sq₁ := hm₁, sq₂ := hm₂, sq₃ := hm₃
    h01 := fun c => ?_
    h10 := fun c => ?_
    h12 := fun c => ?_
    h21 := fun c => ?_ }⟩
  · change n * ι₀ (tv 0 1 c) * n⁻¹ = _
    rw [h01, l₀]
  · change n * ι₀ (tv 1 0 c) * n⁻¹ = _
    rw [h10, l₁]
  · change n * ι₀ (tv 1 2 c) * n⁻¹ = _
    rw [h12, l₂]
  · change n * ι₀ (tv 2 1 c) * n⁻¹ = _
    rw [h21, l₃]

end Levi

section F4

@[expose] def transportWordF4 : List (Fin (Tag.rank .F4)) :=
  [idxF4 1, idxF4 2, idxF4 0, idxF4 1, idxF4 2, idxF4 3, idxF4 2, idxF4 1, idxF4 2, idxF4 1]

theorem simpleWordAct_transport_zero :
    simpleWordAct .F4 transportWordF4 (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .F4)) 1) =
      thetaF4' := by
  unfold transportWordF4 simpleWordAct idxF4
  decide +kernel

theorem simpleWordAct_transport_one :
    simpleWordAct .F4 transportWordF4 (Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .F4)) 1) =
      deltaF4 := by
  unfold transportWordF4 simpleWordAct idxF4
  decide +kernel

theorem exists_sl3_simple_F4 (F : Type) [Field F] [Finite F] :
    ∃ emb : SL(3, F) →* ↥(adjointGroup .F4 F), Function.Injective emb ∧
      ∀ c, emb (tv 0 1 c) = f4Par F (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .F4)) 1) c ∧
        emb (tv 1 0 c) = f4Par F (-Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .F4)) 1) c ∧
        emb (tv 1 2 c) = f4Par F (Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .F4)) 1) c ∧
        emb (tv 2 1 c) = f4Par F (-Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .F4)) 1) c := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Steinberg.Adjoint.f4Datum F).isFiniteType
    (Dv := (Steinberg.Adjoint.f4Datum F).divisible) rfl
  obtain ⟨C, -, hC⟩ := Steinberg.Adjoint.f4_commutatorFormula F O
  have hE := Steinberg.Adjoint.f4_chevalleyExtras F O C hC
  have hdiv : (Steinberg.Adjoint.f4Datum F).divisible = ∅ := rfl
  obtain ⟨emb, hinj, -, hx⟩ := exists_sl3Levi hE hdiv (i := ⟨0, by show 0 < 4; decide⟩)
    (j := ⟨1, by show 1 < 4; decide⟩) (k := ⟨2, by show 2 < 4; decide⟩)
    (by intro h; have := congrArg Fin.val h; simp at this)
    (by show Blueprint.Chevalley.Tag.cartan .F4 ⟨0, by decide⟩ ⟨1, by decide⟩ = -1; decide)
    (by show Blueprint.Chevalley.Tag.cartan .F4 ⟨1, by decide⟩ ⟨0, by decide⟩ = -1; decide)
    (by show ¬ (3 : ℤ) ∣ Blueprint.Chevalley.Tag.cartan .F4 ⟨0, by decide⟩ ⟨2, by decide⟩ +
      2 * Blueprint.Chevalley.Tag.cartan .F4 ⟨1, by decide⟩ ⟨2, by decide⟩; decide)
  exact ⟨emb, hinj, hx⟩

theorem nonempty_a2Embedding_F4 (F : Type) [Field F] [Finite F] :
    Nonempty (A2Embedding .F4 thetaF4 deltaF4 F) := by
  obtain ⟨emb, hinj, hx⟩ := exists_sl3_simple_F4 F
  have hcoe : ∀ {γ : Fin (Tag.rank .F4) → ℤ}, IsRoot .F4 γ → ∀ c : F,
      ((f4Par F γ c : ↥(adjointGroup .F4 F)) : ModGL .F4 F) =
        pinnedX .F4 F γ ((((rootOperatorFamily .F4).pinnedFamilySign γ : ℤ) : F) * c) :=
    fun hγ c => CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hγ c
  have hsg : ∀ γ : Fin (Tag.rank .F4) → ℤ,
      (((rootOperatorFamily .F4).pinnedFamilySign γ : ℤ) : F) *
        (((rootOperatorFamily .F4).pinnedFamilySign γ : ℤ) : F) = 1 := fun γ =>
    (rootOperatorFamily .F4).pinnedFamilySign_mul_self F γ
  refine nonempty_a2Embedding_of_levi (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) transportWordF4
    (by rw [simpleWordAct_transport_zero, thetaF4_eq]) simpleWordAct_transport_one
    ((adjointGroup .F4 F).subtype.comp emb) (fun x y h => hinj (Subtype.ext h))
    (fun y => (emb y).2) (hsg (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .F4)) 1))
    (hsg (-Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .F4)) 1))
    (hsg (Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .F4)) 1))
    (hsg (-Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .F4)) 1)) (fun c => ?_) (fun c => ?_)
    (fun c => ?_) (fun c => ?_)
  · change ((emb (tv 0 1 c) : ↥(adjointGroup .F4 F)) : ModGL .F4 F) = _
    rw [(hx c).1, hcoe (isRoot_single _ _)]
  · change ((emb (tv 1 0 c) : ↥(adjointGroup .F4 F)) : ModGL .F4 F) = _
    rw [(hx c).2.1, hcoe (isRoot_neg_single _ _)]
  · change ((emb (tv 1 2 c) : ↥(adjointGroup .F4 F)) : ModGL .F4 F) = _
    rw [(hx c).2.2.1, hcoe (isRoot_single _ _)]
  · change ((emb (tv 2 1 c) : ↥(adjointGroup .F4 F)) : ModGL .F4 F) = _
    rw [(hx c).2.2.2, hcoe (isRoot_neg_single _ _)]

end F4

end CFSG.ClassicalInvolution.ModelFacts.Levi

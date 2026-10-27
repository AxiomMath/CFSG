module

public import CFSG.HardMathSupport.Lang.AnisoE6.TwPlane

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.Open

set_option linter.unusedSectionVars false

theorem exists_eq_algebraMap_add_mul {k K : Type} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] (h2 : Module.finrank k K = 2) {u : K}
    (hu : u ∉ Set.range (algebraMap k K)) (x : K) :
    ∃ α β : k, x = algebraMap k K α + u * algebraMap k K β := by
  have hli : LinearIndependent k ![(1 : K), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      refine ⟨?_, rfl⟩
      simpa using hst
    · exfalso
      apply hu
      refine ⟨-(s / t), ?_⟩
      have e : t • u = -(s • (1 : K)) := eq_neg_of_add_eq_zero_right hst
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at e
      have htK : algebraMap k K t ≠ 0 := (map_ne_zero _).2 ht
      rw [map_neg, map_div₀]
      field_simp
      rw [mul_comm] at e
      linear_combination -e
  have hspan : Submodule.span k (Set.range ![(1 : K), u]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, h2])
  have hx : x ∈ Submodule.span k (Set.range ![(1 : K), u]) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Algebra.smul_def, mul_one]
  ring

theorem finrank_eq_two_of_card {k K : Type} [Field k] [Finite k] [Field K] [Finite K]
    [Algebra k K] (hK : Nat.card K = Nat.card k ^ 2) : Module.finrank k K = 2 := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype K := Fintype.ofFinite K
  have h : Fintype.card K = Fintype.card k ^ Module.finrank k K := Module.card_eq_pow_finrank
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK] at h
  have hk : 1 < Nat.card k := Finite.one_lt_card
  exact (Nat.pow_right_injective hk h).symm


section KPoints

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem ringHom_pow_apply_algebraMap (σ : K ≃+* K)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c) (n : ℕ) (c : k) :
    (σ.toRingHom ^ n) (algebraMap k K c) = algebraMap k K c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih]; exact hfix c

theorem ringHom_id_pow_apply (n : ℕ) (c : k) : (RingHom.id k ^ n) c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih]; rfl

theorem algebraMap_mem_orbitField (σ : K ≃+* K)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (a : Fin TwistTag.E6.foldedTag.rank) (c : k) :
    algebraMap k K c ∈ orbitField TwistTag.E6 K σ.toRingHom a := by
  rw [mem_orbitField]
  exact ringHom_pow_apply_algebraMap σ hfix _ c

theorem orbitX_algebraMap_eq_baseChange (σ : K ≃+* K)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (a : Fin TwistTag.E6.foldedTag.rank) (c : k) :
    (orbitX TwistTag.E6 K σ.toRingHom a ⟨algebraMap k K c, algebraMap_mem_orbitField σ hfix a c⟩ :
        ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap k K)
        (orbitX TwistTag.E6 k (RingHom.id k) a ⟨c, mem_orbitField_id a c⟩ :
          ModGL TwistTag.E6.tag k) := by
  rw [coe_orbitX, coe_orbitX, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun n _ => ?_)
  rw [Function.comp_apply, baseChangeGL_xUnit]
  congr 1
  exact (ringHom_pow_apply_algebraMap σ hfix n c).trans
    (congrArg (algebraMap k K) (ringHom_id_pow_apply n c)).symm

theorem orbitY_algebraMap_eq_baseChange (σ : K ≃+* K)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (a : Fin TwistTag.E6.foldedTag.rank) (c : k) :
    (orbitY TwistTag.E6 K σ.toRingHom a ⟨algebraMap k K c, algebraMap_mem_orbitField σ hfix a c⟩ :
        ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap k K)
        (orbitY TwistTag.E6 k (RingHom.id k) a ⟨c, mem_orbitField_id a c⟩ :
          ModGL TwistTag.E6.tag k) := by
  rw [coe_orbitY, coe_orbitY, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun n _ => ?_)
  rw [Function.comp_apply, baseChangeGL_yUnit]
  congr 1
  exact (ringHom_pow_apply_algebraMap σ hfix n c).trans
    (congrArg (algebraMap k K) (ringHom_id_pow_apply n c)).symm

end KPoints

section OrbitY

variable {t : TwistTag} {K : Type} [Field K] (σ : K →+* K)

theorem orbitYProd_add_of {a : Fin t.foldedTag.rank} {γ γ' : Fin t.tag.rank → K} :
    orbitYProd t a (γ + γ') = orbitYProd t a γ * orbitYProd t a γ' := by
  unfold orbitYProd
  rw [← list_prod_map_mul_of_commute]
  · congr 1
    exact List.map_congr_left fun j _ => by rw [Pi.add_apply, yUnit_add]
  · intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      change yUnit t.tag K x _ * yUnit t.tag K x _ = yUnit t.tag K x _ * yUnit t.tag K x _
      rw [← yUnit_add, ← yUnit_add, add_comm]
    · exact commute_yUnit_yUnit K ((t.mem_orbitWord).1 hx) ((t.mem_orbitWord).1 hy) hxy _ _

theorem orbitY_add_of {a : Fin t.foldedTag.rank} (c c' : orbitField t K σ a) :
    orbitY t K σ a (c + c') = orbitY t K σ a c * orbitY t K σ a c' := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_orbitY_eq_orbitYProd, coe_orbitY_eq_orbitYProd,
    coe_orbitY_eq_orbitYProd, ← orbitYProd_add_of]
  unfold orbitYProd
  congr 1
  exact List.map_congr_left fun j hj => by
    rw [Pi.add_apply, Subfield.coe_add, orbitParam_add t σ _ _ ((t.mem_orbitWord).1 hj)]

end OrbitY

section Closing

variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]

theorem orbitX_mem_twistedE6RootGroup (σ : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ :=
  graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (orbitX_mem_graphFixedPosUnipotent _ _ _ _)

theorem orbitY_mem_twistedE6RootGroup (σ : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ :=
  graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ (orbitY_mem_graphFixedNegUnipotent _ _ _ _)

theorem mem_orbitField_short (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) {a : Fin TwistTag.E6.foldedTag.rank}
    (ha : a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩) (x : K) :
    x ∈ orbitField TwistTag.E6 K σ.toRingHom a := by
  have hcard : (TwistTag.E6.orbit a).card = 2 := by rcases ha with rfl | rfl <;> rfl
  rw [mem_orbitField, hcard, pow_two, RingHom.coe_mul, Function.comp_apply]
  change σ (σ x) = x
  rw [hσ, hσ, ← pow_mul, ← sq, ← hK]
  classical
  letI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem closure_top_of_torus (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hK : Nat.card K = Nat.card k ^ 2)
    (H : Subgroup (twistedE6RootGroup K σ)) (hF : (phiG σ hfix).range ≤ H)
    (d : twistedE6RootGroup K σ) (hd : d ∈ H)
    (v : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (hX : ∀ a c, (d : ModGL TwistTag.E6.tag K) *
        (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) *
        (d : ModGL TwistTag.E6.tag K)⁻¹ =
      orbitX TwistTag.E6 K σ.toRingHom a ((v a : orbitField TwistTag.E6 K σ.toRingHom a) * c))
    (hY : ∀ a c, (d : ModGL TwistTag.E6.tag K) *
        (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) *
        (d : ModGL TwistTag.E6.tag K)⁻¹ =
      orbitY TwistTag.E6 K σ.toRingHom a
        (((v a)⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) * c))
    (hv : ∀ a : Fin TwistTag.E6.foldedTag.rank, (a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩) →
      ((v a : orbitField TwistTag.E6 K σ.toRingHom a) : K) ∉ Set.range (algebraMap k K)) :
    H = ⊤ := by
  classical
  haveI : FiniteDimensional k K := Module.Finite.of_finite
  have h2 : Module.finrank k K = 2 := finrank_eq_two_of_card hK
  set XG : (a : Fin TwistTag.E6.foldedTag.rank) → orbitField TwistTag.E6 K σ.toRingHom a →
      twistedE6RootGroup K σ := fun a c => ⟨_, orbitX_mem_twistedE6RootGroup σ a c⟩ with hXGdef
  set YG : (a : Fin TwistTag.E6.foldedTag.rank) → orbitField TwistTag.E6 K σ.toRingHom a →
      twistedE6RootGroup K σ := fun a c => ⟨_, orbitY_mem_twistedE6RootGroup σ a c⟩ with hYGdef
  have hkX : ∀ a (c : k), XG a ⟨algebraMap k K c, algebraMap_mem_orbitField σ hfix a c⟩ ∈ H := by
    intro a c
    apply hF
    refine ⟨⟨(orbitX TwistTag.E6 k (RingHom.id k) a ⟨c, mem_orbitField_id a c⟩ :
        ModGL TwistTag.E6.tag k),
      graphFixedPosUnipotent_le _ _ _ (orbitX_mem_graphFixedPosUnipotent _ _ _ _)⟩, ?_⟩
    apply Subtype.ext
    rw [coe_phiG]
    exact (orbitX_algebraMap_eq_baseChange σ hfix a c).symm
  have hkY : ∀ a (c : k), YG a ⟨algebraMap k K c, algebraMap_mem_orbitField σ hfix a c⟩ ∈ H := by
    intro a c
    apply hF
    refine ⟨⟨(orbitY TwistTag.E6 k (RingHom.id k) a ⟨c, mem_orbitField_id a c⟩ :
        ModGL TwistTag.E6.tag k),
      graphFixedNegUnipotent_le _ _ _ (orbitY_mem_graphFixedNegUnipotent _ _ _ _)⟩, ?_⟩
    apply Subtype.ext
    rw [coe_phiG]
    exact (orbitY_algebraMap_eq_baseChange σ hfix a c).symm
  have hconjX : ∀ a c, XG a c ∈ H →
      XG a ((v a : orbitField TwistTag.E6 K σ.toRingHom a) * c) ∈ H := by
    intro a c hc
    have e : XG a ((v a : orbitField TwistTag.E6 K σ.toRingHom a) * c) = d * XG a c * d⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (hX a c).symm
    rw [e]
    exact H.mul_mem (H.mul_mem hd hc) (H.inv_mem hd)
  have hconjY : ∀ a c, YG a c ∈ H →
      YG a (((v a)⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) * c) ∈ H := by
    intro a c hc
    have e : YG a (((v a)⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) * c) =
        d * YG a c * d⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (hY a c).symm
    rw [e]
    exact H.mul_mem (H.mul_mem hd hc) (H.inv_mem hd)
  have hall : ∀ a c, XG a c ∈ H ∧ YG a c ∈ H := by
    intro a c
    by_cases hs : a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩
    · have hfull := mem_orbitField_short σ hσ hK hs
      set u : K := ((v a : orbitField TwistTag.E6 K σ.toRingHom a) : K) with hudef
      have hu : u ∉ Set.range (algebraMap k K) := hv a hs
      have hu' : u⁻¹ ∉ Set.range (algebraMap k K) := by
        rintro ⟨w, hw⟩
        apply hu
        refine ⟨w⁻¹, ?_⟩
        rw [map_inv₀, hw, inv_inv]
      obtain ⟨α, β, hαβ⟩ := exists_eq_algebraMap_add_mul h2 hu (c : K)
      obtain ⟨α', β', hαβ'⟩ := exists_eq_algebraMap_add_mul h2 hu' (c : K)
      constructor
      · have hsplit : c = ⟨algebraMap k K α, algebraMap_mem_orbitField σ hfix a α⟩ +
            (v a : orbitField TwistTag.E6 K σ.toRingHom a) *
              ⟨algebraMap k K β, algebraMap_mem_orbitField σ hfix a β⟩ := by
          apply Subtype.ext
          rw [Subfield.coe_add, Subfield.coe_mul]
          exact hαβ
        have e : XG a c = XG a ⟨algebraMap k K α, algebraMap_mem_orbitField σ hfix a α⟩ *
            XG a ((v a : orbitField TwistTag.E6 K σ.toRingHom a) *
              ⟨algebraMap k K β, algebraMap_mem_orbitField σ hfix a β⟩) := by
          apply Subtype.ext
          rw [Subgroup.coe_mul]
          change (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) = _
          rw [hsplit, orbitX_add σ.toRingHom]
          rfl
        rw [e]
        exact H.mul_mem (hkX a α) (hconjX a _ (hkX a β))
      · have hsplit : c = ⟨algebraMap k K α', algebraMap_mem_orbitField σ hfix a α'⟩ +
            (((v a)⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
              orbitField TwistTag.E6 K σ.toRingHom a) *
              ⟨algebraMap k K β', algebraMap_mem_orbitField σ hfix a β'⟩ := by
          apply Subtype.ext
          rw [Subfield.coe_add, Subfield.coe_mul]
          have hinv : ((((v a)⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
              orbitField TwistTag.E6 K σ.toRingHom a) : K) = u⁻¹ := by
            rw [hudef, ← Subfield.coe_inv, Units.val_inv_eq_inv_val]
          rw [hinv]
          exact hαβ'
        have e : YG a c = YG a ⟨algebraMap k K α', algebraMap_mem_orbitField σ hfix a α'⟩ *
            YG a ((((v a)⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
              orbitField TwistTag.E6 K σ.toRingHom a) *
              ⟨algebraMap k K β', algebraMap_mem_orbitField σ hfix a β'⟩) := by
          apply Subtype.ext
          rw [Subgroup.coe_mul]
          change (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) = _
          rw [hsplit, orbitY_add_of σ.toRingHom]
          rfl
        rw [e]
        exact H.mul_mem (hkY a α') (hconjY a _ (hkY a β'))
    · have hcard : (TwistTag.E6.orbit a).card = 1 := by
        obtain ⟨n, hn⟩ := a
        have hn4 : n < 4 := hn
        interval_cases n
        · exact (hs (Or.inl rfl)).elim
        · exact (hs (Or.inr rfl)).elim
        · rfl
        · rfl
      have hc : (c : K) ^ Nat.card k = c := by
        rw [← hσ]
        have := mem_orbitField.1 c.2
        rwa [hcard, pow_one] at this
      obtain ⟨c', hc'⟩ := mem_range_algebraMap_of_pow_card_eq (k := k) hc
      have e : c = ⟨algebraMap k K c', algebraMap_mem_orbitField σ hfix a c'⟩ :=
        Subtype.ext hc'.symm
      rw [e]
      exact ⟨hkX a c', hkY a c'⟩
  have hG : twistedE6RootGroup K σ ≤ H.map (twistedE6RootGroup K σ).subtype := by
    have hgen' := graphFixedRootGroup_eq_iSup_orbitRankOneGroup (t := TwistTag.E6)
      (σ := σ.toRingHom) σ.surjective
    refine (le_of_eq hgen').trans (iSup_le fun a => (Subgroup.closure_le _).2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨_, (hall a c).1, rfl⟩
    · exact ⟨_, (hall a c).2, rfl⟩
  refine (Subgroup.eq_top_iff' _).2 fun x => ?_
  obtain ⟨y, hy, hyx⟩ := hG x.2
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

end Closing

section TorusWord

variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]

abbrev aSixteen : Fin TwistTag.E6.foldedTag.rank := ⟨0, by decide⟩

@[expose] def torusUnit (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) (t : Kˣ) :
    (orbitField TwistTag.E6 K σ.toRingHom aSixteen)ˣ :=
  Units.mk0 ⟨t, mem_orbitField_short σ hσ hK (Or.inl rfl) t⟩
    (fun h => t.ne_zero (congrArg Subtype.val h))

@[expose] def torusW (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) (t : Kˣ) :
    (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ :=
  Pi.mulSingle aSixteen (torusUnit σ hσ hK t)

theorem compatDiag_torusW (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) (t : Kˣ) :
    compatDiag TwistTag.E6 σ.toRingHom (torusW σ hσ hK t) =
      ![t, 1, 1, 1, 1, Units.map σ.toRingHom.toMonoidHom t] := by
  have hpow : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (n : ℕ) (j : Fin TwistTag.E6.tag.rank),
      n < (TwistTag.E6.orbit a).card → (TwistTag.E6.perm ^ n) (TwistTag.E6.orbitMin a) = j →
      compatDiag TwistTag.E6 σ.toRingHom (torusW σ hσ hK t) j =
        Units.map (σ.toRingHom ^ n).toMonoidHom
          (orbitFieldUnit TwistTag.E6 σ.toRingHom (torusW σ hσ hK t a)) := by
    intro a n j hn hj
    rw [← hj]
    exact compatDiag_pow _ a hn
  have hone : ∀ (a : Fin TwistTag.E6.foldedTag.rank), a ≠ aSixteen →
      orbitFieldUnit TwistTag.E6 σ.toRingHom (torusW σ hσ hK t a) = 1 := by
    intro a ha
    rw [torusW, Pi.mulSingle_eq_of_ne ha]
    exact Units.ext rfl
  have hsame : orbitFieldUnit TwistTag.E6 σ.toRingHom (torusW σ hσ hK t aSixteen) = t := by
    rw [torusW, Pi.mulSingle_eq_same]
    exact Units.ext rfl
  funext j
  fin_cases j
  · rw [hpow aSixteen 0 _ (by decide) (by decide +kernel), hsame]
    exact Units.ext rfl
  · rw [hpow ⟨3, by decide⟩ 0 _ (by decide) (by decide +kernel), hone _ (by decide), map_one]
    rfl
  · rw [hpow ⟨1, by decide⟩ 0 _ (by decide) (by decide +kernel), hone _ (by decide), map_one]
    rfl
  · rw [hpow ⟨2, by decide⟩ 0 _ (by decide) (by decide +kernel), hone _ (by decide), map_one]
    rfl
  · rw [hpow ⟨1, by decide⟩ 1 _ (by decide) (by decide +kernel), hone _ (by decide), map_one]
    rfl
  · rw [hpow aSixteen 1 _ (by decide) (by decide +kernel), hsame]
    exact Units.ext rfl


@[expose] def torusChar (σ : K ≃+* K) (t : Kˣ) : Fin TwistTag.E6.tag.rank → Kˣ :=
  fun l => t ^ TwistTag.E6.tag.cartan ⟨0, by decide⟩ l *
    (Units.map σ.toRingHom.toMonoidHom t) ^ TwistTag.E6.tag.cartan ⟨5, by decide⟩ l

theorem cartanChar_torus (σ : K ≃+* K) (t : Kˣ) :
    cartanChar (τ := TwistTag.E6.tag) ![t, 1, 1, 1, 1, Units.map σ.toRingHom.toMonoidHom t] =
      torusChar σ t := by
  funext l
  unfold cartanChar torusChar
  rw [Finset.prod_eq_mul (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) ⟨5, by decide⟩ (by decide)]
  · rfl
  · intro j _ hj
    have hj' : j ≠ ⟨0, by decide⟩ ∧ j ≠ ⟨5, by decide⟩ := hj
    have hv : (![t, 1, 1, 1, 1, Units.map σ.toRingHom.toMonoidHom t] : Fin 6 → Kˣ) j = 1 := by
      fin_cases j
      · exact (hj'.1 rfl).elim
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (hj'.2 rfl).elim
    change (![t, 1, 1, 1, 1, Units.map σ.toRingHom.toMonoidHom t] : Fin 6 → Kˣ) j ^ _ = 1
    rw [hv, one_zpow]
  · intro h
    exact (h (Finset.mem_univ _)).elim
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem torusChar_zero (σ : K ≃+* K) (t : Kˣ) : torusChar σ t ⟨0, by decide⟩ = t ^ 2 := by
  unfold torusChar
  rw [show TwistTag.E6.tag.cartan ⟨0, by decide⟩ ⟨0, by decide⟩ = 2 from by decide +kernel,
    show TwistTag.E6.tag.cartan ⟨5, by decide⟩ ⟨0, by decide⟩ = 0 from by decide +kernel]
  simp

theorem torusChar_two (σ : K ≃+* K) (t : Kˣ) : torusChar σ t ⟨2, by decide⟩ = t⁻¹ := by
  unfold torusChar
  rw [show TwistTag.E6.tag.cartan ⟨0, by decide⟩ ⟨2, by decide⟩ = -1 from by decide +kernel,
    show TwistTag.E6.tag.cartan ⟨5, by decide⟩ ⟨2, by decide⟩ = 0 from by decide +kernel]
  simp

theorem orbitH_mem_twistedE6RootGroup (σ : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (u : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    (orbitH TwistTag.E6 K σ.toRingHom a u : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ := by
  have hN : ∀ u' : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ,
      (orbitN TwistTag.E6 K σ.toRingHom a u' : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ := by
    intro u'
    rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
    exact mul_mem (mul_mem (orbitX_mem_twistedE6RootGroup σ a _)
      (orbitY_mem_twistedE6RootGroup σ a _)) (orbitX_mem_twistedE6RootGroup σ a _)
  rw [orbitH, Subgroup.coe_mul, Subgroup.coe_inv]
  exact mul_mem (hN u) (inv_mem (hN 1))

@[expose] def torusWord (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) (t : Kˣ) : twistedE6RootGroup K σ :=
  ⟨((List.finRange TwistTag.E6.foldedTag.rank).map fun a =>
      (orbitH TwistTag.E6 K σ.toRingHom a (torusW σ hσ hK t a) : ModGL TwistTag.E6.tag K)).prod,
    list_prod_mem fun x hx => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      exact orbitH_mem_twistedE6RootGroup σ a _⟩

theorem coe_torusWord (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) (t : Kˣ) :
    (torusWord σ hσ hK t : ModGL TwistTag.E6.tag K) =
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag
        (torusChar σ t) := by
  change ((List.finRange TwistTag.E6.foldedTag.rank).map fun a =>
      (orbitH TwistTag.E6 K σ.toRingHom a (torusW σ hσ hK t a) : ModGL TwistTag.E6.tag K)).prod = _
  rw [list_prod_orbitH_eq_rootDiagUnit, compatDiag_torusW, cartanChar_torus]

theorem closure_top_of_torusWord (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hK : Nat.card K = Nat.card k ^ 2)
    (H : Subgroup (twistedE6RootGroup K σ)) (hF : (phiG σ hfix).range ≤ H) (t : Kˣ)
    (ht : (t : K) ^ (Nat.card k + 1) = 1) (ht4 : (t : K) ^ 4 ≠ 1)
    (hd : torusWord σ hσ hK t ∈ H) : H = ⊤ := by
  obtain ⟨v, -, hv, hX, hY⟩ := exists_list_prod_orbitH_conj (torusW σ hσ hK t)
  have hval : ∀ a, ((v a : orbitField TwistTag.E6 K σ.toRingHom a) : K) =
      (torusChar σ t (TwistTag.E6.orbitMin a) : K) := by
    intro a
    have h := hv a
    rw [compatDiag_torusW, cartanChar_torus] at h
    exact congrArg Units.val h
  refine closure_top_of_torus σ hσ hfix hK H hF (torusWord σ hσ hK t) hd v hX hY ?_
  have hfixK : ∀ x : K, x ∈ Set.range (algebraMap k K) → x ^ Nat.card k = x := by
    rintro x ⟨c, rfl⟩
    rw [← hσ]
    exact hfix c
  rintro a (rfl | rfl)
  · rw [hval]
    have hm : TwistTag.E6.orbitMin (⟨0, by decide⟩ : Fin TwistTag.E6.foldedTag.rank) =
        (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) := by decide +kernel
    rw [hm, torusChar_zero]
    intro hmem
    apply ht4
    have h1 := hfixK _ hmem
    rw [Units.val_pow_eq_pow_val] at h1
    calc (t : K) ^ 4 = ((t : K) ^ 2) ^ Nat.card k * (t : K) ^ 2 := by rw [h1]; ring
      _ = ((t : K) ^ (Nat.card k + 1)) ^ 2 := by ring
      _ = 1 := by rw [ht, one_pow]
  · rw [hval]
    have hm : TwistTag.E6.orbitMin (⟨1, by decide⟩ : Fin TwistTag.E6.foldedTag.rank) =
        (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) := by decide +kernel
    rw [hm, torusChar_two]
    intro hmem
    apply ht4
    have h1 := hfixK _ hmem
    rw [Units.val_inv_eq_inv_val, inv_pow] at h1
    have h2 : (t : K) ^ Nat.card k = t := inv_injective h1
    calc (t : K) ^ 4 = ((t : K) ^ (Nat.card k) * (t : K)) ^ 2 := by rw [h2]; ring
      _ = ((t : K) ^ (Nat.card k + 1)) ^ 2 := by ring
      _ = 1 := by rw [ht, one_pow]

end TorusWord

end CFSG.LieType.SeitzGeneration.ExcHighThree

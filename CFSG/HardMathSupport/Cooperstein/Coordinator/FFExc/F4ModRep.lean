module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitIso
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4ModTables
public import CFSG.Quasithin.Background.SmithCurtisChev

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.FieldFour
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev Matrix

variable (K : Type) [Field K] [Finite K] [CharP K 2]

abbrev idF4 : adjointGroup Tag.F4 K ≃* adjointGroup Tag.F4 K := MulEquiv.refl _

theorem f4in27Equiv_sX_eq (j : Fin Tag.F4.rank) (c : K) :
    f4in27Equiv K ⟨sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c,
      sX_mem_F4in27 _ (orbitWord_mem j) c⟩ = xC Tag.F4 K j c :=
  Subtype.ext (f4in27Equiv_sX K j c)

theorem f4in27Equiv_sY_eq (j : Fin Tag.F4.rank) (c : K) :
    f4in27Equiv K ⟨sY e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c,
      sY_mem_F4in27 _ (orbitWord_mem j) c⟩ = yC Tag.F4 K j c :=
  Subtype.ext (f4in27Equiv_sY K j c)

theorem f4Embed_xC (j : Fin Tag.F4.rank) (c : K) :
    f4Embed K (idF4 K) (xC Tag.F4 K j c) =
      sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c := by
  have := (f4in27Equiv K).symm_apply_apply
    (⟨sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c,
      sX_mem_F4in27 _ (orbitWord_mem j) c⟩ : F4in27 e6Data_valid K)
  rw [f4in27Equiv_sX_eq] at this
  change ((f4in27Equiv K).symm (xC Tag.F4 K j c)).1 = _
  rw [this]

theorem f4Embed_yC (j : Fin Tag.F4.rank) (c : K) :
    f4Embed K (idF4 K) (yC Tag.F4 K j c) =
      sY e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c := by
  have := (f4in27Equiv K).symm_apply_apply
    (⟨sY e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c,
      sY_mem_F4in27 _ (orbitWord_mem j) c⟩ : F4in27 e6Data_valid K)
  rw [f4in27Equiv_sY_eq] at this
  change ((f4in27Equiv K).symm (yC Tag.F4 K j c)).1 = _
  rw [this]

theorem sX_orbit_eq_gen (k : ℕ) (hk : k < 4) :
    ∃ j : Fin Tag.F4.rank, ∀ c : K,
      sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c =
        gen e6Data_valid K (e6root k) c := by
  match k, hk with
  | 0, _ =>
    refine ⟨⟨3, by decide⟩, fun c => ?_⟩
    have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨3, by decide⟩) = [nd0, nd5] := rfl
    rw [h, sX_pair, e6root_simple nd0, gen_pair_gen _ _ _ gam_single_zero (by decide)]
  | 1, _ =>
    refine ⟨⟨0, by decide⟩, fun c => ?_⟩
    have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨0, by decide⟩) = [nd1] := rfl
    rw [h, sX_single, e6root_simple nd1, gen_fix_gen _ _ gam_single_one]
  | 2, _ =>
    refine ⟨⟨2, by decide⟩, fun c => ?_⟩
    have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨2, by decide⟩) = [nd2, nd4] := rfl
    rw [h, sX_pair, e6root_simple nd2, gen_pair_gen _ _ _ gam_single_two (by decide)]
  | 3, _ =>
    refine ⟨⟨1, by decide⟩, fun c => ?_⟩
    have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨1, by decide⟩) = [nd3] := rfl
    rw [h, sX_single, e6root_simple nd3, gen_fix_gen _ _ gam_single_three]

theorem fixed_conds (x : Fin e6Data.d →₀ K)
    (hx : ∀ (j : Fin Tag.F4.rank) (c : K), e6Data_valid.endo K (f4Embed K (idF4 K) (xC Tag.F4 K j c)) x = x) :
    ∀ k < 4, (Gm2 k - 1).map (cast2 K) *ᵥ ⇑x = 0 := by
  intro k hk
  obtain ⟨j, hj⟩ := sX_orbit_eq_gen (K := K) k hk
  have h1 := hx j 1
  simp only [f4Embed_xC, hj] at h1
  have h2 := congrArg (fun v : Fin e6Data.d →₀ K => ⇑v) h1
  simp only [coe_endo, rho_gen_one e6Data_valid k (by omega)] at h2
  have : (Gm2 k - 1).map (cast2 K) = (cast2 K).mapMatrix (Gm2 k) - 1 := by
    rw [← RingHom.mapMatrix_apply, map_sub, map_one]
  rw [this, sub_mulVec, h2, one_mulVec, sub_self]

abbrev i0 : Ix := ⟨0, by decide⟩

theorem fT_single_i0 : fT K (Finsupp.single i0 (1 : K)) = 0 := by
  rw [fT_eq]
  simp [Finsupp.single_apply, i12, i13, i14, i0, Fin.ext_iff]

theorem fixed_coords (x : Ix → K)
    (hx : ∀ k < 4, (Gm2 k - 1).map (cast2 K) *ᵥ x = 0) :
    (∀ i : Ix, ¬ (i.val = 0 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14) → x i = 0) ∧
      x ⟨12, by decide⟩ + x ⟨13, by decide⟩ = 0 ∧ x ⟨13, by decide⟩ + x ⟨14, by decide⟩ = 0 := by
  have key : ∀ p ∈ fixCert, dotK (bvec p.1) x = 0 := by
    intro p hp
    have h1 := (fixCert_check p hp)
    rw [← h1, dotK_list_sum, List.map_map]
    refine List.sum_eq_zero fun a ha => ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
    exact dotK_Nrow q.1 _ x (hx q.1 (fixCert_rows p hp q hq))
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · obtain ⟨p, hp, hp1⟩ := fixCert_single i hi
    have := key p hp
    rwa [hp1, bvec_single, dotK_single] at this
  · obtain ⟨p, hp, hp1⟩ := fixCert_mem_12_13
    have := key p hp
    rwa [hp1, bvec_12_13, dotK_add, dotK_single, dotK_single] at this
  · obtain ⟨p, hp, hp1⟩ := fixCert_mem_13_14
    have := key p hp
    rwa [hp1, bvec_13_14, dotK_add, dotK_single, dotK_single] at this

theorem eq_smul_i0_of_fixed (x : Fin e6Data.d →₀ K) (hxf : fT K x = 0)
    (hx : ∀ (j : Fin Tag.F4.rank) (c : K),
      e6Data_valid.endo K (f4Embed K (idF4 K) (xC Tag.F4 K j c)) x = x) :
    ∃ c : K, x = c • Finsupp.single i0 (1 : K) := by
  obtain ⟨h0, h1, h2⟩ := fixed_coords K (x := ⇑x) (fixed_conds K x hx)
  have hf := hxf
  rw [fT_eq] at hf
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  have e13 : x ⟨13, by decide⟩ = x ⟨12, by decide⟩ := by
    linear_combination h1 - x ⟨12, by decide⟩ * h2'
  have e14 : x ⟨14, by decide⟩ = x ⟨13, by decide⟩ := by
    linear_combination h2 - x ⟨13, by decide⟩ * h2'
  have z12 : x ⟨12, by decide⟩ = 0 := by
    have : x i12 + x i13 + x i14 = 0 := hf
    have e13' : x i13 = x i12 := e13
    have e14' : x i14 = x i12 := e14.trans e13
    rw [e13', e14'] at this
    linear_combination this - x i12 * h2'
  refine ⟨x i0, Finsupp.ext fun i => ?_⟩
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases hi0 : i0 = i
  · subst hi0; simp
  · rw [if_neg hi0, mul_zero]
    by_cases hi : i.val = 0 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14
    · rcases hi with h | h | h | h
      · exact absurd (Fin.ext h.symm) hi0
      · have : i = ⟨12, by decide⟩ := Fin.ext h
        rw [this]; exact z12
      · have : i = ⟨13, by decide⟩ := Fin.ext h
        rw [this, e13, z12]
      · have : i = ⟨14, by decide⟩ := Fin.ext h
        rw [this, e14, e13, z12]
    · exact h0 i hi

@[expose] def vecOf (v : Ix → ZMod 2) : Fin e6Data.d →₀ K := Finsupp.equivFunOnFinite.symm (cast2 K ∘ v)

theorem coe_vecOf (v : Ix → ZMod 2) : ⇑(vecOf K v) = cast2 K ∘ v := rfl

theorem vecOf_add (v w : Ix → ZMod 2) : vecOf K (v + w) = vecOf K v + vecOf K w :=
  Finsupp.ext fun j => map_add (cast2 K) (v j) (w j)

theorem vecOf_zero : vecOf K (0 : Ix → ZMod 2) = 0 := Finsupp.ext fun j => map_zero (cast2 K)

@[expose] def vecOfHom : (Ix → ZMod 2) →+ (Fin e6Data.d →₀ K) where
  toFun := vecOf K
  map_zero' := vecOf_zero K
  map_add' := vecOf_add K

theorem vecOf_list_sum (L : List (Ix → ZMod 2)) : vecOf K L.sum = (L.map (vecOf K)).sum :=
  map_list_sum (vecOfHom K) L

theorem vecOf_single (i : Ix) : vecOf K (Pi.single i 1) = Finsupp.single i (1 : K) := by
  refine Finsupp.ext fun j => ?_
  rw [coe_vecOf, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_apply, h, Ne.symm h]

theorem vecOf_Nact (k : ℕ) (hk : k < 72) (v : Ix → ZMod 2) :
    e6Data_valid.endo K (gen e6Data_valid K (e6root k) 1) (vecOf K v) - vecOf K v =
      vecOf K (Nact k v) := by
  refine Finsupp.ext fun j => ?_
  have h := congrFun (coe_endo e6Data_valid (gen e6Data_valid K (e6root k) 1) (vecOf K v)) j
  rw [Finsupp.sub_apply, h, rho_gen_one e6Data_valid k hk, coe_vecOf, coe_vecOf]
  have e : (Gm2 k - 1).map (cast2 K) = (cast2 K).mapMatrix (Gm2 k) - 1 := by
    rw [← RingHom.mapMatrix_apply, map_sub, map_one]
  have : (cast2 K).mapMatrix (Gm2 k) *ᵥ (cast2 K ∘ v) - cast2 K ∘ v =
      cast2 K ∘ ((Gm2 k - 1) *ᵥ v) := by
    rw [← map_mulVec', e, sub_mulVec, one_mulVec]
  have h' := congrFun this j
  rw [Gm2_sub_one_mulVec] at h'
  exact h'

theorem ker_le_of_closed (Wv : Submodule K (Fin e6Data.d →₀ K))
    (h0 : Finsupp.single i0 (1 : K) ∈ Wv)
    (hstep : ∀ k < 72, ∀ u ∈ Wv,
      e6Data_valid.endo K (gen e6Data_valid K (e6root k) 1) u - u ∈ Wv) :
    LinearMap.ker (fT K) ≤ Wv := by
  have hchain : ∀ i < genChain.length, vecOf K (bvec (genChain.getD i (0, 0, 0)).1) ∈ Wv := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [genChain_zero]
        have : vecOf K (bvec 1) = Finsupp.single i0 (1 : K) := by
          have := bvec_single i0
          have h1 : (1 <<< (i0 : Ix).val : ℕ) = 1 := rfl
          rw [h1] at this
          rw [this, vecOf_single]
        rw [this]
        exact h0
      · obtain ⟨hc, hp, hk⟩ := genChain_check i hi hpos
        have hp' := ih _ hp (by omega)
        have := hstep _ hk _ hp'
        rw [vecOf_Nact K _ hk] at this
        rwa [hc]
  have htarget : ∀ p ∈ genCert, vecOf K (bvec p.1) ∈ Wv := by
    intro p hp
    obtain ⟨hsum, hlt⟩ := genCert_check p hp
    rw [← hsum, vecOf_list_sum, List.map_map]
    refine list_sum_mem fun a ha => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    exact hchain i (hlt i hi)
  refine ker_le_of_targets _ (fun b hb => ?_) ?_ ?_
  · obtain ⟨p, hp, hp1⟩ := genCert_single b hb
    have := htarget p hp
    rwa [hp1, bvec_single, vecOf_single] at this
  · obtain ⟨p, hp, hp1⟩ := genCert_mem_12_13
    have := htarget p hp
    rwa [hp1, bvec_12_13, vecOf_add, vecOf_single, vecOf_single] at this
  · obtain ⟨p, hp, hp1⟩ := genCert_mem_13_14
    have := htarget p hp
    rwa [hp1, bvec_13_14, vecOf_add, vecOf_single, vecOf_single] at this

theorem f4Embed_symm_apply (g : F4in27 e6Data_valid K) :
    f4Embed K (idF4 K) (f4in27Equiv K g) = g.1 := by
  have := (f4in27Equiv K).symm_apply_apply g
  exact congrArg Subtype.val this

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

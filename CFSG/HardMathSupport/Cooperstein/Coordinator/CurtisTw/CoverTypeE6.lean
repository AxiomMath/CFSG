module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverE6
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverType
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.ChevTypeLD

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Quasithin.SmithCurtis.Chev CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

section Matrices

variable {K : Type} [Field K]

theorem mat_phi (u : Kˣ) :
    (!![1, (u : K); 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; -1, 0] =
      !![1, 0; ((u⁻¹ : Kˣ) : K), 1] * !![((-u : Kˣ) : K), 0; 0, (((-u)⁻¹ : Kˣ) : K)] *
        !![1, -((u⁻¹ : Kˣ) : K); 0, 1] := by
  have hu : (u : K) ≠ 0 := u.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hu]

theorem mat_psi (u : Kˣ) :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) * !![1, (u : K); 0, 1] * !![0, 1; -1, 0] =
      !![1, -((u⁻¹ : Kˣ) : K); 0, 1] * !![0, 1; -1, 0] *
        !![((-u : Kˣ) : K), 0; 0, (((-u)⁻¹ : Kˣ) : K)] * !![1, -((u⁻¹ : Kˣ) : K); 0, 1] := by
  have hu : (u : K) ≠ 0 := u.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hu]

end Matrices

section E6

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e6_endo_x (i : Fin (Tag.rank .E6)) (c : K) :
    e6Data_valid.endo K (e6Data_valid.xm K (Pi.single i 1) c) =
      e6Data_valid.blockOp K i !![1, c; 0, 1] := by
  rw [e6Data_valid.endo_xm, e6Data_valid.blockOp_upper]

theorem e6_endo_y (i : Fin (Tag.rank .E6)) (c : K) :
    e6Data_valid.endo K (e6Data_valid.xm K (-Pi.single i 1) c) =
      e6Data_valid.blockOp K i !![1, 0; c, 1] := by
  rw [e6Data_valid.endo_xm, e6Data_valid.blockOp_lower]

theorem e6_endo_n (i : Fin (Tag.rank .E6)) :
    e6Data_valid.endo K (e6Data_valid.nm K i) = e6Data_valid.blockOp K i !![0, 1; -1, 0] := by
  rw [e6Data_valid.endo_nm, e6Data_valid.blockOp_weyl]

theorem e6_endo_h (i : Fin (Tag.rank .E6)) (t : Kˣ) :
    e6Data_valid.endo K (e6Data_valid.hm K i t) =
      e6Data_valid.blockOp K i !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] := by
  rw [e6Data_valid.endo_hm, e6Data_valid.blockOp_diag]

theorem e6_phi_id (i : Fin (Tag.rank .E6)) (u : Kˣ) :
    e6Data_valid.xm K (Pi.single i 1) (u : K) * e6Data_valid.nm K i =
      e6Data_valid.xm K (-Pi.single i 1) ((u⁻¹ : Kˣ) : K) * e6Data_valid.hm K i (-u) *
        e6Data_valid.xm K (Pi.single i 1) (-((u⁻¹ : Kˣ) : K)) := by
  refine e6Data_valid.endo_injective K ?_
  rw [e6Data_valid.endo_mul, e6Data_valid.endo_mul, e6Data_valid.endo_mul, e6_endo_x, e6_endo_n,
    e6_endo_y, e6_endo_h, e6_endo_x, ← e6Data_valid.blockOp_mul, ← e6Data_valid.blockOp_mul,
    ← e6Data_valid.blockOp_mul, mat_phi]

theorem e6_psi_id (i : Fin (Tag.rank .E6)) (u : Kˣ) :
    e6Data_valid.nm K i * e6Data_valid.xm K (Pi.single i 1) (u : K) * e6Data_valid.nm K i =
      e6Data_valid.xm K (Pi.single i 1) (-((u⁻¹ : Kˣ) : K)) * e6Data_valid.nm K i *
        e6Data_valid.hm K i (-u) * e6Data_valid.xm K (Pi.single i 1) (-((u⁻¹ : Kˣ) : K)) := by
  refine e6Data_valid.endo_injective K ?_
  rw [e6Data_valid.endo_mul, e6Data_valid.endo_mul, e6Data_valid.endo_mul, e6Data_valid.endo_mul,
    e6Data_valid.endo_mul, e6_endo_x, e6_endo_n, e6_endo_h, e6_endo_x, ← e6Data_valid.blockOp_mul,
    ← e6Data_valid.blockOp_mul, ← e6Data_valid.blockOp_mul, ← e6Data_valid.blockOp_mul,
    ← e6Data_valid.blockOp_mul, mat_psi]

theorem isPElt_xm (γ : Fin (Tag.rank .E6) → ℤ) (c : K) : IsPElt 2 (e6Data_valid.xm K γ c) :=
  ⟨1, by
    rw [pow_one, pow_two, ← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]⟩

theorem coe_e6IsogenyT_xm_single (i : Fin (Tag.rank .E6)) (c : K) :
    ((Isogeny.e6IsogenyT K (e6Data_valid.xm K (Pi.single i 1) c) :
      ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K i c := by
  show ((Isogeny.e6Isogeny K (e6Data_valid.xm K (Pi.single i 1) c) :
      ↥(adjointGroup .E6 K)) : ModGL .E6 K) = _
  rw [Isogeny.e6Isogeny_xm_single, Isogeny.eltElement_simpleRoot_E6]
  rfl

theorem coe_e6IsogenyT_xm_neg_single (i : Fin (Tag.rank .E6)) (c : K) :
    ((Isogeny.e6IsogenyT K (e6Data_valid.xm K (-Pi.single i 1) c) :
      ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) =
      yUnit TwistTag.E6.tag K i c := by
  show ((Isogeny.e6Isogeny K (e6Data_valid.xm K (-Pi.single i 1) c) :
      ↥(adjointGroup .E6 K)) : ModGL .E6 K) = _
  rw [Isogeny.e6Isogeny_xm_neg_single, Isogeny.eltElement_neg_simpleRoot_E6]
  rfl

theorem canonMin_simple (s : Fin (Tag.rank .E6)) :
    canonMin K ((coxeterSystem Tag.E6).simple s) = e6Data_valid.nm K s := by
  have h := canonMin_wordProd (k := K) (ω := [s])
    (by rw [CoxeterSystem.IsReduced, CoxeterSystem.wordProd_singleton,
      CoxeterSystem.length_simple, List.length_singleton])
  rwa [CoxeterSystem.wordProd_singleton, List.map_singleton, List.prod_singleton] at h

theorem nhat_e6 (s : Fin (Tag.rank .E6)) : (e6CoverData K).nhat s = e6Data_valid.nm K s :=
  canonMin_simple s

theorem pow_card_sub_one_of_isogeny_mem_torusGroup {a : ↥(e6Data_valid.minGroup K)}
    (ha : ((Isogeny.e6IsogenyT K a : ↥(adjointGroup TwistTag.E6.tag K)) :
      ModGL TwistTag.E6.tag K) ∈ torusGroup TwistTag.E6.tag K) :
    a ^ (Nat.card K - 1) = 1 := by
  obtain ⟨t, ht, e⟩ := exists_lift_torusGroup ha
  have hz : t⁻¹ * a ∈ Subgroup.center ↥(e6Data_valid.minGroup K) := by
    refine Isogeny.ker_e6IsogenyT_le_center K ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    exact inv_mul_eq_one.2 (Subtype.ext e)
  have htN : t ^ (Nat.card K - 1) = 1 := by
    have := Subgroup.iSup_induction (fun i => e6Data_valid.torus K i)
      (C := fun x => x ∈ ⨆ i, e6Data_valid.torus K i ∧ x ^ (Nat.card K - 1) = 1) ht
      (fun i x hx => by
        obtain ⟨u, rfl⟩ := (e6Data_valid.mem_torus K).1 hx
        refine ⟨Subgroup.mem_iSup_of_mem i hx, ?_⟩
        have h1 : (e6Data_valid.hm K i u) ^ (Nat.card K - 1) =
            e6Data_valid.hm K i (u ^ (Nat.card K - 1)) :=
          ((e6Data_valid.hHom K i).map_pow u (Nat.card K - 1)).symm
        rw [h1, ← Nat.card_units K, pow_card_eq_one', e6Data_valid.hm_one])
      ⟨one_mem _, one_pow _⟩ (fun x y hx hy => by
        refine ⟨mul_mem hx.1 hy.1, ?_⟩
        rw [Commute.mul_pow (commute_of_mem_iSup_torus hx.1 hy.1), hx.2, hy.2, mul_one])
    exact this.2
  have hzN : (t⁻¹ * a) ^ (Nat.card K - 1) = 1 := by
    have h1 := pow_card_eq_one' (G := ↥(Subgroup.center ↥(e6Data_valid.minGroup K)))
      (x := ⟨_, hz⟩)
    have h2 : (t⁻¹ * a) ^ Nat.card ↥(Subgroup.center ↥(e6Data_valid.minGroup K)) = 1 :=
      congrArg Subtype.val h1
    rw [(CentralExt.MinusculeClosed.card_center_e6 (k := K)).1] at h2
    obtain ⟨m, hm⟩ := Nat.gcd_dvd_right 3 (Nat.card K - 1)
    rw [hm, pow_mul, h2, one_pow]
  have hcomm : Commute t (t⁻¹ * a) := by
    exact Subgroup.mem_center_iff.1 hz t
  calc a ^ (Nat.card K - 1) = (t * (t⁻¹ * a)) ^ (Nat.card K - 1) := by group
    _ = t ^ (Nat.card K - 1) * (t⁻¹ * a) ^ (Nat.card K - 1) := hcomm.mul_pow _
    _ = 1 := by rw [htN, hzN, one_mul]

theorem coe_e6IsogenyT_hm (i : Fin (Tag.rank .E6)) (u : Kˣ) :
    ((Isogeny.e6IsogenyT K (e6Data_valid.hm K i u) : ↥(adjointGroup TwistTag.E6.tag K)) :
      ModGL TwistTag.E6.tag K) = torusElt TwistTag.E6.tag K i u :=
  e6Isogeny_hm' i u

instance e6Cover_finite : Finite ↥(e6Data_valid.minGroup K) := by
  have : Finite (Module.End K (Fin e6Data.d →₀ K)) := Module.finite_of_finite K
  infer_instance

theorem e6_xm_mem_lX (i : Fin TwistTag.E6.tag.rank) (c : K) :
    e6Data_valid.xm K (Pi.single i 1) c ∈ (e6CoverData K).lX i := by
  refine (e6CoverData K).mem_lX.2 ⟨?_, isPElt_xm _ _⟩
  refine (mem_X_chevDatumLD (T := TwistTag.E6)).2 ⟨c, Subtype.ext ?_⟩
  exact (coe_e6IsogenyT_xm_single i c).symm

theorem e6_ym_mem_lL (i : Fin TwistTag.E6.tag.rank) (c : K) :
    e6Data_valid.xm K (-Pi.single i 1) c ∈ (e6CoverData K).lL := by
  refine (e6CoverData K).mem_lL.2 ⟨?_, isPElt_xm _ _⟩
  refine Subgroup.mem_subgroupOf.2 ?_
  have e : ((Isogeny.e6IsogenyT K (e6Data_valid.xm K (-Pi.single i 1) c) :
      ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) =
        yUnit TwistTag.E6.tag K i c := coe_e6IsogenyT_xm_neg_single i c
  rw [e]
  exact rootSubgroup_neg_single_le i (Chev.yUnit_mem_rootSubgroup i c)

theorem e6_hm_mem_H (i : Fin TwistTag.E6.tag.rank) (u : Kˣ) :
    e6Data_valid.hm K i u ∈
      (chevDatumLD TwistTag.E6 K 2 e6LongestData).H.comap (Isogeny.e6IsogenyT K) := by
  refine Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 ?_)
  rw [coe_e6IsogenyT_hm i u]
  exact torusElt_mem_torusGroup i u

variable (K) in
@[expose] noncomputable def e6CoverRankOne :
    CoverRankOne (e6CoverData K) (fun _ : Fin TwistTag.E6.tag.rank => K) where
  x s c := e6Data_valid.xm K (Pi.single s 1) c
  y s c := e6Data_valid.xm K (-Pi.single s 1) c
  hh s u := e6Data_valid.hm K s u
  x_mem s c := e6_xm_mem_lX s c
  x_surj s g hg := by
    obtain ⟨c, hc⟩ := mem_X_chevDatumLD.1 hg.1
    refine ⟨c, pLift_inj (h := (e6CoverData K).cover) (e6_xm_mem_lX s c) hg ?_⟩
    exact Subtype.ext ((coe_e6IsogenyT_xm_single s c).trans (congrArg Subtype.val hc))
  x_zero s := e6Data_valid.xm_zero K _
  x_inj s c d h := by
    have h1 := congrArg (fun g => ((Isogeny.e6IsogenyT K g : ↥(adjointGroup TwistTag.E6.tag K)) :
      ModGL TwistTag.E6.tag K)) h
    exact xUnit_injective s ((coe_e6IsogenyT_xm_single s c).symm.trans
      (h1.trans (coe_e6IsogenyT_xm_single s d)))
  y_mem s c := e6_ym_mem_lL s c
  hh_mem s u := e6_hm_mem_H s u
  hh_mul s u v := e6Data_valid.hm_mul K s u v
  hh_one s := e6Data_valid.hm_one K s
  phi_id s u := by
    have h := e6_phi_id (K := K) s u
    rw [← nhat_e6 s] at h
    exact h
  psi_id s u := by
    have h := e6_psi_id (K := K) s u
    rw [← nhat_e6 s] at h
    exact h

theorem e6Cover_pow (h : ↥(e6Data_valid.minGroup K))
    (hh : h ∈ (chevDatumLD TwistTag.E6 K 2 e6LongestData).H.comap (Isogeny.e6IsogenyT K)) :
    h ^ (Nat.card K - 1) = 1 :=
  pow_card_sub_one_of_isogeny_mem_torusGroup hh

theorem e6Cover_hodd : ∀ h ∈ (chevDatumLD TwistTag.E6 K 2 e6LongestData).H.comap
    (Isogeny.e6IsogenyT K), IsPElt 2 h → h = 1 := by
  intro h hh ⟨k, hk⟩
  have hN := e6Cover_pow h hh
  have hlt : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hev : Even (Nat.card K) := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Nat.even_iff.2 ((FiniteField.even_card_iff_char_two (F := K)).1 (ringChar.eq K 2))
  obtain ⟨r, hr⟩ := hev
  have hodd : Nat.Coprime (2 ^ k) (Nat.card K - 1) := by
    refine Nat.Coprime.pow_left k ?_
    rw [Nat.coprime_two_left]
    exact ⟨r - 1, by omega⟩
  have h1 : orderOf h ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf h ∣ Nat.card K - 1 := orderOf_dvd_of_pow_eq_one hN
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hodd h1 h2)

theorem e6Cover_split (k : Type*) [Field k] [Algebra K k] :
    SplitOver k ((chevDatumLD TwistTag.E6 K 2 e6LongestData).H.comap (Isogeny.e6IsogenyT K)) :=
  splitOver_of_pow_card_sub_one k e6Cover_pow

theorem e6_exists_isCoverType {k V : Type*} [Field k] [Algebra K k] [AddCommGroup V] [Module k V]
    [CharP k 2] {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) :
    ∃ y : V, ∃ χ : ↥(e6Data_valid.minGroup K) → k, ∃ J : Finset (Fin TwistTag.E6.tag.rank),
      IsCoverType (e6CoverRankOne K) ρ y χ J :=
  exists_isCoverType hρ (e6Cover_split k)

theorem e6_isCoverType_unique {k V : Type*} [Field k] [Algebra K k] [AddCommGroup V] [Module k V]
    [CharP k 2] {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ)
    {y y' : V} {χ χ' : ↥(e6Data_valid.minGroup K) → k} {J J' : Finset (Fin TwistTag.E6.tag.rank)}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (ht' : IsCoverType (e6CoverRankOne K) ρ y' χ' J') :
    (∀ h ∈ (chevDatumLD TwistTag.E6 K 2 e6LongestData).H.comap (Isogeny.e6IsogenyT K),
      χ h = χ' h) ∧ J = J' :=
  IsCoverType.unique hρ (e6Cover_split k) ht ht'

theorem e6_iso_of_isCoverType {k V V' : Type*} [Field k] [Algebra K k] [AddCommGroup V]
    [Module k V] [AddCommGroup V'] [Module k V'] [CharP k 2]
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V}
    {ρ' : Representation k ↥(e6Data_valid.minGroup K) V'} (hρ : IsSimpleRep ρ)
    (hρ' : IsSimpleRep ρ') {y : V} {y' : V'} {χ : ↥(e6Data_valid.minGroup K) → k}
    {J : Finset (Fin TwistTag.E6.tag.rank)} (ht : IsCoverType (e6CoverRankOne K) ρ y χ J)
    (ht' : IsCoverType (e6CoverRankOne K) ρ' y' χ J) :
    ∃ β : V ≃ₗ[k] V', ∀ (g : ↥(e6Data_valid.minGroup K)) (v : V), β (ρ g v) = ρ' g (β v) :=
  iso_of_isCoverType e6Cover_hodd hρ hρ' (e6Cover_split k) ht ht'

end E6

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

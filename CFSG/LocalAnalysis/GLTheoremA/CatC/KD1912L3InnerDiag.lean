module

public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.GroupTheory.PCore.SelfCentralizing
public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424SL2
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeGLTwoCent
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeCoverPsl
public import CFSG.LieType.SeitzGeneration.UnitaryHeisGU2
public import CFSG.RankThree.PartTwo.Sec15.Item15Res5ProofBlock
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsNilp
public import CFSG.Walter.W67.W2Cor32A
public import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofTypeOne

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec14
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.Open
open Matrix

variable {K : Type} [Field K] {n : ℕ} {π : Bool}

theorem modThree_two_pow_odd {n : ℕ} (hn : Odd n) : ModThree false (2 ^ n) := by
  simpa [ModThree] using CFSG.two_pow_mod_three_of_odd hn

theorem modThree_two_pow_even {F : Type} [Field F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : Even n) : ModThree true (2 ^ n) := by
  simpa [ModThree] using CFSG.two_pow_mod_three_of_even hn

theorem odd_qSubPi_two_pow {ε : Bool} {n : ℕ} (hn0 : n ≠ 0) : Odd (qSubPi ε (2 ^ n)) := by
  have hEven : Even (2 ^ n) :=
    Even.pow_of_ne_zero (show Even (2 : ℕ) from ⟨1, by norm_num⟩) hn0
  obtain ⟨k, hk⟩ := hEven
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hn0)
  have hk1 : 1 ≤ k := by omega
  cases ε <;> simp [qSubPi, hk, Nat.odd_iff] <;> omega

theorem eqLocus_conjM'_eq_map_centMod (hK : PiField π 2 n K)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (2 ^ n) K) :
    (((Res8Hess.conjM' (p := 2) (f := n) (fun h => by subst h; exact hK.unitary) hg :
        MulAut (projImage (slPi π 3 (2 ^ n) K))) :
      projImage (slPi π 3 (2 ^ n) K) →*
        projImage (slPi π 3 (2 ^ n) K)).eqLocus (MonoidHom.id _)) =
      ((centMod (slPi π 3 (2 ^ n) K) g).subgroupOf (slPi π 3 (2 ^ n) K)).map (projOf (slPi π 3 (2 ^ n) K)) := by
  have hπ : π = false → UnitaryFieldData 2 n K := fun h => by subst h; exact hK.unitary
  ext m
  rw [Subgroup.mem_map]
  constructor
  · intro hm
    obtain ⟨s, rfl⟩ := projOf_surjective (slPi π 3 (2 ^ n) K) m
    refine ⟨s, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hm2 : Res8Hess.conjM' (p := 2) (f := n)
        (fun h => by subst h; exact hK.unitary) hg
        ((projOf (slPi π 3 (2 ^ n) K)) s) = (projOf (slPi π 3 (2 ^ n) K)) s := hm
    have hm' := congrArg (fun x : projImage (slPi π 3 (2 ^ n) K) =>
      (x : ProjGenLinGroup (Fin 3) K)) hm2
    simp only [Res8Hess.coe_conjM', coe_projOf] at hm'
    have hw : g * (s : GL (Fin 3) K) * g⁻¹ * (s : GL (Fin 3) K)⁻¹ ∈ CFSG.Open.StatedScalars (Fin 3) K := by
      rw [← mk_eq_one_iff_mem_statedScalars]
      have h := congrArg (fun x : ProjGenLinGroup (Fin 3) K =>
        x * (ProjGenLinGroup.mk (s : GL (Fin 3) K))⁻¹) hm'
      simpa [map_mul, map_inv, mul_assoc] using h
    rw [mem_centMod_iff_scalar]
    refine ⟨s.2, (g * (s : GL (Fin 3) K) * g⁻¹ * (s : GL (Fin 3) K)⁻¹)⁻¹, inv_mem hw, ?_⟩
    group
  · intro hmaps
    obtain ⟨s, hs, rfl⟩ := hmaps
    rw [Subgroup.mem_subgroupOf] at hs
    obtain ⟨-, z, hz, hzy⟩ := mem_centMod_iff_scalar.1 hs
    have hinv : (s : GL (Fin 3) K) * g⁻¹ * (s : GL (Fin 3) K)⁻¹ = g⁻¹ * z⁻¹ := by
      calc (s : GL (Fin 3) K) * g⁻¹ * (s : GL (Fin 3) K)⁻¹
          = ((s : GL (Fin 3) K) * g * (s : GL (Fin 3) K)⁻¹)⁻¹ := by group
        _ = (z * g)⁻¹ := by rw [hzy]
        _ = g⁻¹ * z⁻¹ := by group
    have hgz : g * (s : GL (Fin 3) K) * g⁻¹ = z⁻¹ * (s : GL (Fin 3) K) := by
      calc g * (s : GL (Fin 3) K) * g⁻¹
          = g * ((s : GL (Fin 3) K) * g⁻¹ * (s : GL (Fin 3) K)⁻¹) * (s : GL (Fin 3) K) := by
            group
        _ = g * (g⁻¹ * z⁻¹) * (s : GL (Fin 3) K) := by rw [hinv]
        _ = z⁻¹ * (s : GL (Fin 3) K) := by group
    change Res8Hess.conjM' (p := 2) (f := n) (fun h => by subst h; exact hK.unitary) hg
      (projOf (slPi π 3 (2 ^ n) K) s) = projOf (slPi π 3 (2 ^ n) K) s
    apply Subtype.ext
    simp only [Res8Hess.coe_conjM', coe_projOf]
    rw [← map_inv, ← map_mul, ← map_mul, hgz, map_mul,
      show ProjGenLinGroup.mk (z⁻¹) = 1 from
        mk_eq_one_iff_mem_statedScalars.2 (inv_mem hz), one_mul]

theorem center_slPi_le_centMod (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n))
    (y : GL (Fin 3) K) :
    Subgroup.center (slPi π 3 (2 ^ n) K) ≤
      (centMod (slPi π 3 (2 ^ n) K) y).subgroupOf (slPi π 3 (2 ^ n) K) := by
  intro z hz
  rw [Subgroup.mem_subgroupOf, mem_centMod_iff_scalar]
  have hzS : (z : GL (Fin 3) K) ∈ CFSG.Open.StatedScalars (Fin 3) K := by
    have h := CFSG.HardMathSupport.Solomon.Coordinator.center_slPi_eq hK hq
    rw [h] at hz
    exact hz
  refine ⟨z.2, 1, one_mem _, ?_⟩
  rw [← commute_of_mem_statedScalars hzS y]
  group

theorem card_map_centMod_mul_three (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n))
    (y : GL (Fin 3) K) :
    Nat.card (((centMod (slPi π 3 (2 ^ n) K) y).subgroupOf
        (slPi π 3 (2 ^ n) K)).map (projOf (slPi π 3 (2 ^ n) K))) * 3 =
      Nat.card (centMod (slPi π 3 (2 ^ n) K) y) := by
  let L := slPi π 3 (2 ^ n) K
  let C := (centMod L y).subgroupOf L
  let f : C →* projImage L := (projOf L).comp C.subtype
  have hrange : f.range = C.map (projOf L) := by
    dsimp only [f]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card f.ker = 3 := by
    have hkereq : f.ker = (Subgroup.center L).subgroupOf C := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change (projOf L) (x : L) = 1 ↔ (x : L) ∈ Subgroup.center L
      rw [← MonoidHom.mem_ker, CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree.ker_projOf_eq_center hK hq]
    rw [hkereq]
    have hZle : Subgroup.center L ≤ C := center_slPi_le_centMod hK hq y
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv]
    exact card_center_slPi hK hq
  have hCcard : Nat.card C = Nat.card (centMod L y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show centMod L y ≤ L from inf_le_left)).toEquiv
  have h := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, hCcard, mul_comm] at h
  exact h

theorem odd_card_core_map_centMod_of_regular (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n)) (hn : 2 ≤ n)
    {y : GL (Fin 3) K}
    (hCL : Nonempty (↥(slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) ≃*
      Multiplicative (ZMod (qSubPi π (2 ^ n))) × Multiplicative (ZMod (qSubPi π (2 ^ n)))))
    (hrel : (slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))).relIndex
      (centMod (slPi π 3 (2 ^ n) K) y) = 3) :
    Odd (Nat.card (GLAPPrimeCoreOf 3
      (((centMod (slPi π 3 (2 ^ n) K) y).subgroupOf (slPi π 3 (2 ^ n) K)).map
        (projOf (slPi π 3 (2 ^ n) K))))) := by
  let L := slPi π 3 (2 ^ n) K
  let CL := L ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))
  let C := centMod L y
  change Odd (Nat.card (GLAPPrimeCoreOf 3 ((C.subgroupOf L).map (projOf L))))
  have hCLle : CL ≤ C := centralizer_le_centMod L y
  have hoddCL : Odd (Nat.card CL) := by
    obtain ⟨e⟩ := hCL
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have hc : Nat.card (Multiplicative (ZMod (qSubPi π (2 ^ n)))) = qSubPi π (2 ^ n) := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [hc]
    have hn0 : n ≠ 0 := by omega
    exact (CFSG.LocalAnalysis.GLTheoremA.KD1912.odd_qSubPi_two_pow (ε := π) (n := n) hn0).mul
      (CFSG.LocalAnalysis.GLTheoremA.KD1912.odd_qSubPi_two_pow (ε := π) (n := n) hn0)
  have hcardC : Nat.card C = 3 * Nat.card CL := by
    have h := Subgroup.relIndex_mul_card CL C
    rw [hrel, inf_eq_left.mpr hCLle] at h
    exact h.symm
  have hcardCbar := card_map_centMod_mul_three (π := π) (n := n) hK hq y
  have hCbar : Nat.card ((C.subgroupOf L).map (projOf L)) = Nat.card CL := by
    rw [hcardC, mul_comm (3 : ℕ) (Nat.card CL)] at hcardCbar
    exact Nat.mul_right_cancel (by norm_num : 0 < 3) hcardCbar
  have hdvd : Nat.card (GLAPPrimeCoreOf 3 ((C.subgroupOf L).map (projOf L))) ∣ Nat.card CL := by
    rw [← hCbar]
    exact Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)
  exact hoddCL.of_dvd_nat hdvd

theorem odd_card_core_map_centMod_of_glTwo (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n)) (hn : 2 ≤ n)
    {y : GL (Fin 3) K}
    (hcen : centMod (slPi π 3 (2 ^ n) K) y =
      slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)))
    (hCL : Nonempty (↥(slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) ≃*
      ↥(glPi π 2 (2 ^ n) K))) :
    Odd (Nat.card (GLAPPrimeCoreOf 3
      (((centMod (slPi π 3 (2 ^ n) K) y).subgroupOf (slPi π 3 (2 ^ n) K)).map
        (projOf (slPi π 3 (2 ^ n) K))))) := by
  classical
  haveI hKfin : Finite K := hK.finite
  let L := slPi π 3 (2 ^ n) K
  let C := centMod L y
  let G2 := glPi π 2 (2 ^ n) K
  let S2 := slPi π 2 (2 ^ n) K
  let C' : Subgroup ↥L := C.subgroupOf L
  let ZL : Subgroup ↥L := Subgroup.center L
  change Odd (Nat.card (GLAPPrimeCoreOf 3 (C'.map (projOf L))))
  have hπ : π = false → UnitaryFieldData 2 n K := fun h => by subst h; exact hK.unitary
  haveI : CharP K 2 := hK.charP
  have hn0 : n ≠ 0 := by omega
  have hq3 : 3 < 2 ^ n := by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hCle : C ≤ L := inf_le_left
  obtain ⟨eCL⟩ := hCL
  let eC : ↥C ≃* ↥G2 := (MulEquiv.subgroupCongr hcen).trans eCL
  let eC' : ↥C' ≃* ↥G2 := (Subgroup.subgroupOfEquivOfLe hCle).trans eC
  let N : Subgroup ↥C' := (S2.subgroupOf G2).comap eC'.toMonoidHom
  have hS2normal : (S2.subgroupOf G2).Normal := by
    have hker : S2.subgroupOf G2 = (GeneralLinearGroup.det.comp G2.subtype).ker := by
      ext A
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, mem_slPi_iff hπ]
      constructor
      · rintro ⟨-, h⟩
        exact Units.ext h
      · intro h
        exact ⟨A.2, Units.ext_iff.mp h⟩
    rw [hker]
    infer_instance
  have hNnormal : N.Normal := by
    have h : N = (S2.subgroupOf G2).comap eC'.toMonoidHom := rfl
    rw [h]
    infer_instance
  have hS2data := CFSG.RankThree.PartTwo.Sec15.KS1424.sl2_data (π := π) hK hn
  have hS2simple : IsSimpleGroup ↥S2 := hS2data.1
  have hS2card : Nat.card ↥S2 = 2 ^ n * ((2 ^ n) ^ 2 - 1) := hS2data.2
  have hS2leG2 : S2 ≤ G2 := slPi_le_glPi hπ
  have hmapN : N.map eC'.toMonoidHom = S2.subgroupOf G2 := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hn
    · intro hx
      refine ⟨eC'.symm x, ?_, ?_⟩
      · change eC' (eC'.symm x) ∈ S2.subgroupOf G2
        simpa using hx
      · simp
  let eN : ↥N ≃* ↥S2 :=
    (MulEquiv.subgroupMap eC' N).trans
      ((MulEquiv.subgroupCongr hmapN).trans (Subgroup.subgroupOfEquivOfLe hS2leG2))
  have hNsimple : IsSimpleGroup ↥N := MulEquiv.isSimpleGroup eN
  have hZle : ZL ≤ C' := center_slPi_le_centMod hK hq y
  have hNZ : N ⊓ ZL.subgroupOf C' = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    have hnN : n ∈ N := (Subgroup.mem_inf.1 hn).1
    have hnZ : (n : ↥C') ∈ ZL.subgroupOf C' := (Subgroup.mem_inf.1 hn).2
    rw [Subgroup.mem_subgroupOf] at hnZ
    have hS2 : ((eC' n : ↥G2) : GL (Fin 2) K) ∈ S2 := Subgroup.mem_subgroupOf.1 hnN
    have hcenterC : (n : ↥C') ∈ Subgroup.center ↥C' := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 hnZ (c : ↥L)
    have hcenterG : eC' n ∈ Subgroup.center ↥G2 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨c, rfl⟩ := eC'.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hcenterC c]
    have hscalar : (eC' n : GL (Fin 2) K) ∈ StatedScalars (Fin 2) K := by
      rw [← CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree.centralizer_slPi_two hK hq3]
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hcenterG ⟨s, hS2leG2 hs⟩)
    obtain ⟨μ, hμ⟩ := hscalar
    have hdet : ((μ : K)) ^ 2 = 1 := by
      have hd := (mem_slPi_iff hπ).1 hS2 |>.2
      rw [← hμ] at hd
      have hd' : (Matrix.scalar (Fin 2) (μ : K)).det = 1 := by
        simpa only [GeneralLinearGroup.coe_scalar] using hd
      rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hd'
      simpa [pow_two] using hd' 
    have hμ1 : μ = 1 := by
      rcases sq_eq_one_iff.mp hdet with h | h
      · exact Units.ext h
      · apply Units.ext
        rw [h]
        exact CharTwo.neg_eq 1
    have he1 : eC' n = 1 := by
      apply Subtype.ext
      rw [← hμ, hμ1, map_one]
      rfl
    exact eC'.injective (by simpa using he1)
  let f : ↥C' →* projImage L := (projOf L).comp C'.subtype
  have hfker : f.ker = ZL.subgroupOf C' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (projOf L) (x : ↥L) = 1 ↔ (x : ↥L) ∈ Subgroup.center L
    rw [← MonoidHom.mem_ker,
      CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree.ker_projOf_eq_center hK hq]
  let Cbar : Subgroup (projImage L) := f.range
  have hCbar_eq : Cbar = C'.map (projOf L) := by
    dsimp only [Cbar, f]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let Nbar : Subgroup (projImage L) := N.map f
  have hNbar_le : Nbar ≤ Cbar := by
    dsimp only [Nbar, Cbar]
    exact Subgroup.map_le_range f N
  have hNbar_normal : (Nbar.subgroupOf Cbar).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNbar_le]
    intro h k hh hk
    dsimp only [Nbar] at hh
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hh
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hk
    refine Subgroup.mem_map.2 ⟨c * n * c⁻¹, hNnormal.conj_mem n hn c, ?_⟩
    simp only [map_mul, map_inv]
  let fN : ↥N →* ↥Nbar :=
    { toFun := fun n => ⟨f n, ⟨n, n.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f (a : ↥C') (b : ↥C')) }
  have hfN_inj : Function.Injective fN := by
    intro a b hab
    have hf : f a = f b := congrArg Subtype.val hab
    have hmem : (a * b⁻¹ : ↥C') ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      change f ((a : ↥C') * (b : ↥C')⁻¹) = 1
      rw [map_mul, map_inv, hf, mul_inv_cancel]
    rw [hfker, Subgroup.mem_subgroupOf] at hmem
    have hbot : (a * b⁻¹ : ↥C') ∈ (⊥ : Subgroup ↥C') := by
      rw [← hNZ]
      exact Subgroup.mem_inf.2 ⟨N.mul_mem a.2 (N.inv_mem b.2), hmem⟩
    rw [Subgroup.mem_bot] at hbot
    exact Subtype.ext (mul_inv_eq_one.mp hbot)
  have hfN_surj : Function.Surjective fN := by
    rintro z
    obtain ⟨n, hn, hfn⟩ := Subgroup.mem_map.1 z.2
    exact ⟨⟨n, hn⟩, Subtype.ext hfn⟩
  let eNbar : ↥N ≃* ↥Nbar := MulEquiv.ofBijective fN ⟨hfN_inj, hfN_surj⟩
  have hNbar_simple : IsSimpleGroup ↥Nbar :=
    MulEquiv.isSimpleGroup (eNbar.symm.trans eN)
  have h3Nbar : 3 ∣ Nat.card ↥Nbar := by
    rw [Nat.card_congr (eNbar.symm.trans eN).toEquiv, hS2card]
    have hqmod : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
      cases π
      · exact Or.inr hq
      · exact Or.inl hq
    have h3dvd : 3 ∣ (2 ^ n) ^ 2 - 1 := by
      have hsq : (2 ^ n) ^ 2 % 3 = 1 := by
        rcases hqmod with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
      omega
    exact dvd_mul_of_dvd_right h3dvd _
  let δ : ↥C' →* Kˣ := GeneralLinearGroup.det.comp (G2.subtype.comp eC'.toMonoidHom)
  have hδker : δ.ker = N := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_slPi_iff hπ]
    constructor
    · intro h
      exact ⟨(eC' c).2, Units.ext_iff.mp h⟩
    · rintro ⟨-, h⟩
      exact Units.ext h
  have hCNcard : Nat.card (↥C' ⧸ N) = Nat.card δ.range := by
    rw [← hδker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv
  have hδodd : Odd (Nat.card δ.range) := by
    have hforall : ∀ u : Kˣ, u ∈ δ.range → Odd (orderOf u) := by
      rintro u ⟨c, rfl⟩
      have hqodd : Odd (qSubPi π (2 ^ n)) :=
        CFSG.LocalAnalysis.GLTheoremA.KD1912.odd_qSubPi_two_pow (ε := π) (n := n) hn0
      have hdvd : orderOf (δ c) ∣ qSubPi π (2 ^ n) := by
        cases π with
        | true =>
          have hcardK : Nat.card K = 2 ^ n := by simpa [piCard] using hK.card
          rw [show qSubPi true (2 ^ n) = 2 ^ n - 1 from rfl, ← hcardK, ← Nat.card_units]
          exact orderOf_dvd_natCard _
        | false =>
          have hU : UnitaryFieldData 2 n K := hπ rfl
          have hgu : ((eC' c : ↥G2) : GL (Fin 2) K) ∈
              CFSG.LieType.SeitzGeneration.gu2 hU := by
            rw [CFSG.LieType.SeitzGeneration.mem_gu2 hU]
            exact (mem_glPi_false hU).1 (eC' c).2
          have hnorm := CFSG.LieType.SeitzGeneration.norm_det_of_mem_gu2 hU hgu
          have hpow : (δ c) ^ (2 ^ n + 1) = 1 := by
            apply Units.ext
            have hbar : hU.bar ((eC' c : ↥G2) : GL (Fin 2) K).det =
                ((eC' c : ↥G2) : GL (Fin 2) K).det ^ (2 ^ n) := by
              rw [UnitaryFieldData.bar_apply]
            rw [Units.val_pow_eq_pow_val, Units.val_one]
            change hU.bar ((eC' c : ↥G2) : GL (Fin 2) K).det *
              ((eC' c : ↥G2) : GL (Fin 2) K).det = 1 at hnorm
            rw [hbar, ← pow_succ] at hnorm
            exact hnorm
          rw [show qSubPi false (2 ^ n) = 2 ^ n + 1 from rfl]
          exact orderOf_dvd_of_pow_eq_one hpow
      exact hqodd.of_dvd_nat hdvd
    rw [Nat.odd_iff]
    by_contra h
    have h2 : 2 ∣ Nat.card δ.range := by omega
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := δ.range) 2 h2
    have hodd := hforall (u : Kˣ) u.2
    rw [Subgroup.orderOf_coe, hu] at hodd
    norm_num at hodd
  have hCNodd : Odd (Nat.card (↥C' ⧸ N)) := by
    rw [hCNcard]
    exact hδodd
  have hcardCbar : Nat.card Cbar * 3 = Nat.card ↥C' := by
    calc Nat.card Cbar * 3 = Nat.card (centMod L y) := by
          rw [hCbar_eq]
          exact card_map_centMod_mul_three (π := π) (n := n) hK hq y
      _ = Nat.card ↥C' :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCle).toEquiv).symm
  have hrel_mul : Nbar.relIndex Cbar * Nat.card ↥Nbar = Nat.card Cbar := by
    have h := Subgroup.relIndex_mul_card Nbar Cbar
    rw [inf_eq_left.mpr hNbar_le] at h
    exact h
  have hcardNbar : Nat.card ↥Nbar = Nat.card ↥N :=
    (Nat.card_congr eNbar.toEquiv).symm
  have hcardC : Nat.card ↥C' = Nat.card (↥C' ⧸ N) * Nat.card ↥N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hrel3 : Nbar.relIndex Cbar * 3 = Nat.card (↥C' ⧸ N) := by
    have h : Nbar.relIndex Cbar * Nat.card ↥Nbar * 3 =
        Nat.card (↥C' ⧸ N) * Nat.card ↥N := by
      rw [hrel_mul, hcardCbar, hcardC]
    rw [hcardNbar] at h
    have h' : (Nbar.relIndex Cbar * 3) * Nat.card ↥N =
        Nat.card (↥C' ⧸ N) * Nat.card ↥N := by
      rw [mul_assoc, mul_comm 3 (Nat.card ↥N), ← mul_assoc, h]
    exact Nat.mul_right_cancel (Nat.card_pos) h'
  have hrelOdd : Odd (Nbar.relIndex Cbar) := by
    refine hCNodd.of_dvd_nat ⟨3, ?_⟩
    exact hrel3.symm
  have hL : Odd (Nat.card (GLAPPrimeCoreOf 3 Nbar)) := by
    have hcore : GLAPPrimeCoreOf 3 Nbar = ⊥ := by
      change (GLAPPrimeCore 3 ↥Nbar).map Nbar.subtype = ⊥
      rw [CFSG.gLAPPrimeCore_eq_bot_of_isSimpleGroup_of_dvd_card Nat.prime_three
        hNbar_simple h3Nbar, Subgroup.map_bot]
    rw [hcore, Subgroup.card_bot]
    exact odd_one
  have hmain := CFSG.odd_card_gLAPPrimeCoreOf_of_odd_relIndex (p := 3) hNbar_le
    hNbar_normal hrelOdd hL
  rw [← hCbar_eq]
  exact hmain

theorem odd_card_core_map_centMod_of_singer (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n)) (hn : 2 ≤ n)
    {y w : GL (Fin 3) K}
    (hcyc : IsCyclic ↥(slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))))
    (hcardCL : Nat.card ↥(slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) =
      qSubPi π ((2 ^ n) ^ 3) / qSubPi π (2 ^ n))
    (hcent : centMod (slPi π 3 (2 ^ n) K) y =
      (slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) ⊔ Subgroup.zpowers w)
    (hwL : w ∈ slPi π 3 (2 ^ n) K) (hwo : orderOf w = 3)
    (hwC : w ∉ slPi π 3 (2 ^ n) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) :
    Odd (Nat.card (GLAPPrimeCoreOf 3
      (((centMod (slPi π 3 (2 ^ n) K) y).subgroupOf (slPi π 3 (2 ^ n) K)).map
        (projOf (slPi π 3 (2 ^ n) K))))) := by
  classical
  haveI hKfin : Finite K := hK.finite
  let L := slPi π 3 (2 ^ n) K
  let CL := L ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))
  let Cbar := (centMod L y).subgroupOf L |>.map (projOf L)
  change Odd (Nat.card (GLAPPrimeCoreOf 3 Cbar))
  have hn0 : n ≠ 0 := by omega
  have hoddCL : Odd (Nat.card CL) := by
    rw [hcardCL, Nat.odd_iff]
    have hnot : ¬ 2 ∣ qSubPi π ((2 ^ n) ^ 3) / qSubPi π (2 ^ n) :=
      CFSG.RankThree.PartTwo.Sec15.Proof15Res5.not_two_dvd_qSubPi_div (π := π) (m := n) (by omega)
    omega
  have hwmem : w ∈ centMod L y := by
    rw [hcent]
    exact (show Subgroup.zpowers w ≤ CL ⊔ Subgroup.zpowers w from le_sup_right)
      (Subgroup.mem_zpowers w)
  have hwN : w ∈ Subgroup.normalizer (CL : Set (GL (Fin 3) K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      rw [Subgroup.mem_inf]
      refine ⟨mul_mem (mul_mem hwL hs.1) (inv_mem hwL), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.conj_commute_of_mem_centMod
        hwmem (Subgroup.mem_centralizer_singleton_iff.mp hs.2)
    · intro hs
      rw [Subgroup.mem_inf] at hs
      have hs' : w * s * w⁻¹ ∈ CL := hs
      have h := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.conj_commute_of_mem_centMod
        (inv_mem hwmem) (Subgroup.mem_centralizer_singleton_iff.mp hs'.2)
      rw [Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · have hs_eq : s = w⁻¹ * (w * s * w⁻¹) * w := by group
        rw [hs_eq]
        exact mul_mem (mul_mem (inv_mem hwL) hs'.1) hwL
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hs_eq : s = w⁻¹ * (w * s * w⁻¹) * w := by group
        rw [hs_eq]
        simpa [mul_assoc] using h
  have hwPow : Subgroup.zpowers w ≤ Subgroup.normalizer (CL : Set (GL (Fin 3) K)) :=
    Subgroup.zpowers_le.mpr hwN
  have hprod := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hwPow
  have hprod' : Nat.card ↥(CL ⊔ Subgroup.zpowers w) * Nat.card ↥(CL ⊓ Subgroup.zpowers w) =
      Nat.card ↥CL * 3 := by
    simpa [Nat.card_zpowers, hwo] using hprod
  have hcardCbar := card_map_centMod_mul_three (π := π) (n := n) hK hq y
  have hcardC : Nat.card (centMod L y) = Nat.card ↥(CL ⊔ Subgroup.zpowers w) := by rw [hcent]
  have h1 : (Nat.card Cbar * 3) * Nat.card ↥(CL ⊓ Subgroup.zpowers w) = Nat.card ↥CL * 3 := by
    rw [hcardCbar, hcardC, hprod']
  have h2 : (Nat.card Cbar * Nat.card ↥(CL ⊓ Subgroup.zpowers w)) * 3 = Nat.card ↥CL * 3 := by
    rw [mul_assoc, mul_comm (Nat.card ↥(CL ⊓ Subgroup.zpowers w)) 3, ← mul_assoc]
    exact h1
  have hCbar_div : Nat.card Cbar * Nat.card ↥(CL ⊓ Subgroup.zpowers w) = Nat.card ↥CL :=
    Nat.mul_right_cancel (by norm_num : 0 < 3) h2
  have hoddCbar : Odd (Nat.card Cbar) := by
    refine hoddCL.of_dvd_nat ⟨Nat.card ↥(CL ⊓ Subgroup.zpowers w), ?_⟩
    exact hCbar_div.symm
  exact hoddCbar.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))


end CFSG.LocalAnalysis.GLTheoremA.KD1912

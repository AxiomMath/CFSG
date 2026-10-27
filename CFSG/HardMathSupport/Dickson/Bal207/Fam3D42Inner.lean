module

public import CFSG.HardMathSupport.Dickson.Bal207.Fam3D42Outer
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Link
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.L28Leaf
public import Certificates.Certificate17525

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Fam3D42

open Subgroup CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.RankThree.PartTwo.KFacts.K426 CFSG.RankThree.PartTwo.Sec4.Item434D42
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.L28Presentation
  CFSG.HardMathSupport.Solomon.Coordinator

@[expose] noncomputable def d4L : Subgroup (Equiv.Perm (Fin 2457)) :=
  closure (permsA 2457 (lGens ()))

theorem caseA3_spec :
    d4L ≤ closure (permsA 2457 d4CAGens) ∧
      ⁅closure (permsA 2457 d4CAGens), closure (permsA 2457 d4CAGens)⁆ ≤ d4L ∧
      Nat.card d4L = 504 ∧
      ∀ w ∈ l28Words, CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW
        (fun i : Fin 2 => permOfArr 2457 (lGens ())[i.val]!) w = 1 := by
  have h := Certificates.certificate17525
  simp only [caseA3Check, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h5⟩ := h
  have hCe : enumOK 2457 d4CAGens d4Keys d4CACert = true := centOKP_enum d4_caseA_check
  have hval : ∀ k < d4CAGens.size, validA 2457 d4CAGens[k]! = true :=
    fun k hk => enumOK_gens_valid hCe hk
  obtain ⟨hder, hLcard⟩ := commutator_le_of_derivedLeOK d4Keys_lt hval h1
  have hLe : enumOK 2457 (lGens ()) d4Keys (lCert ()) = true := by
    simp only [derivedLeOK, Bool.and_eq_true] at h1
    exact h1.1.1.1
  have hLC := le_of_gens_mem d4Keys_lt hCe hLe h2
  have hl2 : (lGens ()).size = 2 := by simp [lGens]
  refine ⟨hLC, hder, hLcard, fun w hw => ?_⟩
  simp only [wordsOneOK, Bool.and_eq_true, List.all_eq_true] at h5
  have hv := rep_evalWA (m := 2) (gs := lGens ()) (fun k hk => enumOK_gens_valid hLe hk)
    (by rw [hl2]) w
  exact (eqA_iff hv rep_idA).1 (h5.2 w hw)

theorem nonempty_mulEquiv_d4L :
    Nonempty (↥d4L ≃* ↥(CFSG.GH74.KGroups.L28.QP.originalSubgroup)) := by
  obtain ⟨-, -, hLcard, hrels⟩ := caseA3_spec
  have hl2 : (lGens ()).size = 2 := by simp [lGens]
  have hr : Set.range (fun i : Fin 2 => permOfArr 2457 (lGens ())[i.val]!) =
      permsA 2457 (lGens ()) := by
    ext σ
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, by rw [Set.mem_setOf_eq, hl2]; exact i.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have hk2 : k < 2 := by rw [Set.mem_setOf_eq, hl2] at hk; exact hk
      exact ⟨⟨k, hk2⟩, rfl⟩
  have hcard : Nat.card ↥(closure (Set.range
      (fun i : Fin 2 => permOfArr 2457 (lGens ())[i.val]!))) = 504 := by
    rw [hr]
    exact hLcard
  obtain ⟨e⟩ := nonempty_mulEquiv_P9_of_rels _ hrels hcard
  exact ⟨(MulEquiv.subgroupCongr (by rw [hr]; rfl)).trans e⟩

theorem coe_mem_of_mem_fix {X : Equiv.Perm (Fin 2457)} (hX : X ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) {z : ↥d4P} (hz : (z : Equiv.Perm (Fin 2457)) = X ^ e) {c : ↥d4P}
    (hc : c ∈ fixSubgroup (MulAut.conj z)) :
    (c : Equiv.Perm (Fin 2457)) ∈ centralizer {X} ⊓ d4P := by
  rw [b3Lie_fixSubgroup_conj, mem_centralizer_singleton_iff] at hc
  have h1 : (c : Equiv.Perm (Fin 2457)) * X ^ e = X ^ e * c := by
    rw [← hz]
    exact congrArg Subtype.val hc
  refine Subgroup.mem_inf.2 ⟨?_, c.2⟩
  rcases he with rfl | rfl
  · rw [mem_centralizer_singleton_iff]
    simpa using h1
  · exact centralizer_pow_two_le hX (mem_centralizer_singleton_iff.2 h1)

theorem mem_fix_of_coe_mem {X : Equiv.Perm (Fin 2457)} {e : ℕ} {z : ↥d4P}
    (hz : (z : Equiv.Perm (Fin 2457)) = X ^ e) {c : ↥d4P}
    (hc : (c : Equiv.Perm (Fin 2457)) ∈ centralizer {X}) : c ∈ fixSubgroup (MulAut.conj z) := by
  rw [b3Lie_fixSubgroup_conj, mem_centralizer_singleton_iff]
  rw [mem_centralizer_singleton_iff] at hc
  apply Subtype.ext
  show (c : Equiv.Perm (Fin 2457)) * z = z * c
  rw [hz]
  exact (Commute.pow_right (show Commute (c : Equiv.Perm (Fin 2457)) X from hc) e).eq

theorem compShape_x0
    {e : ℕ} (he : e = 1 ∨ e = 2)
    (z : ↥d4P) (hz : (z : Equiv.Perm (Fin 2457)) = d4X 0 ^ e) :
    CompShape G28CompType (MulAut.conj z) := by
  obtain ⟨hLC, hder, -, -⟩ := caseA3_spec
  obtain ⟨hCx, -⟩ := d4_caseA
  have hX3 : d4X 0 ^ 3 = 1 := d4X_cube (by norm_num)
  have hLP : d4L ≤ d4P := hLC.trans (hCx ▸ inf_le_right)
  obtain ⟨eQ⟩ := nonempty_mulEquiv_d4L
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.L28.equiv_psl_P
  let eN : ↥(d4L.subgroupOf d4P) ≃* ↥d4L := subgroupOfEquivOfLe hLP
  haveI hs : IsSimpleGroup ↥(d4L.subgroupOf d4P) := isSimpleGroup_of_equiv_P9 (eN.trans eQ)
  have hnab := nonabelian_of_equiv_P9 (eN.trans eQ)
  have hZ : center ↥(d4L.subgroupOf d4P) = ⊥ := b3Lie_center_eq_bot hnab
  have hq : CFSG.Open.IsQuasisimple ↥(d4L.subgroupOf d4P) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
      (LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnab)
  have hT : G28CompType (↥(d4L.subgroupOf d4P) ⧸ center ↥(d4L.subgroupOf d4P)) :=
    isoInvariant_g28CompType _ _ (((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).trans ((eN.trans eQ).trans e1.symm)).symm
      (g28CompType_psl2 (CFSG.GH74.KGroups.L28.card_GF8.trans (by norm_num)))
  refine excRee_compShape_of_comm_mem (MulAut.conj z) (N := d4L.subgroupOf d4P)
    (fun n hn => mem_fix_of_coe_mem hz ((hCx ▸ hLC (mem_subgroupOf.1 hn)).1))
    (fun c₁ hc₁ c₂ hc₂ => ?_) hq hT
  rw [mem_subgroupOf]
  have h1 := hCx.symm ▸ coe_mem_of_mem_fix hX3 he hz hc₁
  have h2 := hCx.symm ▸ coe_mem_of_mem_fix hX3 he hz hc₂
  exact hder (commutator_mem_commutator h1 h2)

theorem compShape_x1
    {T : ∀ (Q : Type) [Group Q], Prop} {e : ℕ} (he : e = 1 ∨ e = 2) (z : ↥d4P)
    (hz : (z : Equiv.Perm (Fin 2457)) = d4X 1 ^ e) : CompShape T (MulAut.conj z) := by
  obtain ⟨hCx, hcard⟩ := d4_caseB
  have hX3 : d4X 1 ^ 3 = 1 := d4X_cube (by norm_num)
  have hle : ∀ c ∈ fixSubgroup (MulAut.conj z),
      (c : Equiv.Perm (Fin 2457)) ∈ closure (permsA 2457 d4CBGens) := fun c hc =>
    hCx ▸ coe_mem_of_mem_fix hX3 he hz hc
  let ι : ↥(fixSubgroup (MulAut.conj z)) →* ↥(closure (permsA 2457 d4CBGens)) :=
    { toFun := fun c => ⟨((c : ↥d4P) : Equiv.Perm (Fin 2457)), hle c c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b h => by
    have h' : ((ι a : ↥(closure (permsA 2457 d4CBGens))) : Equiv.Perm (Fin 2457)) = ι b := by
      rw [h]
    exact Subtype.ext (Subtype.ext h')
  haveI : Group.IsSolvable ↥(closure (permsA 2457 d4CBGens)) := by
    haveI : Fintype ↥(closure (permsA 2457 d4CBGens)) := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 4)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  exact compShape_of_isSolvable _ (solvable_of_solvable_injective hι)

theorem compShape_conj_d4P
    (y : ↥d4P) (hy : orderOf y = 3) : CompShape G28CompType (MulAut.conj y) := by
  have hyo : orderOf (y : Equiv.Perm (Fin 2457)) = 3 := by rw [orderOf_coe]; exact hy
  obtain ⟨k, hk, j, hj, e, he, hyk⟩ := exists_conj_rep d4Q_le card_d4Q
    (fun j => permOfArr 2457 d4Lines[j]!) (fun c => permOfArr 2457 d4Lines[c]!)
    (fun j => permOfArr 2457 d4Trans[j]!) (fun j => d4Rec.getD j 0) (r := 31)
    (fun g hg hg3 => d4_lines hg hg3) (fun j hj => d4_trans hj) y.2 hyo
  have hrec : d4Rec.getD j 0 < 2 := of_decide_eq_true (allLt_spec d4_lines_check.2.2.2 hj)
  let κ : ↥d4P := ⟨k, hk⟩
  have hz : ((κ⁻¹ * y * κ : ↥d4P) : Equiv.Perm (Fin 2457)) = d4X (d4Rec.getD j 0) ^ e := by
    show k⁻¹ * (y : Equiv.Perm (Fin 2457)) * k = _
    rw [hyk]
    simp only [d4X]
    group
  refine CompShape.of_congr isoInvariant_g28CompType
    ((MulAut.conj κ⁻¹ : MulAut ↥d4P) : ↥d4P ≃* ↥d4P) ?_
  rw [excRee_congr_self, ← map_inv MulAut.conj, ← map_mul MulAut.conj, ← map_mul MulAut.conj,
    inv_inv]
  rcases (by omega : d4Rec.getD j 0 = 0 ∨ d4Rec.getD j 0 = 1) with h | h
  · rw [h] at hz
    exact compShape_x0 he _ hz
  · rw [h] at hz
    exact compShape_x1 he _ hz

theorem nonempty_mulEquiv_d4P
    {Y : Type*} [Group Y] (φ : Y ≃* CFSG.Quasithin.trialityGroup8)
    (hcard : Nat.card CFSG.Quasithin.trialityGroup8 = 211341312) : Nonempty (Y ≃* ↥d4P) := by
  let e : Y ≃* lineGroup := φ.trans (MulEquiv.subgroupCongr lineGroup_eq.symm)
  have hX : Nat.card lineGroup = 211341312 := by
    rw [← Nat.card_congr (MulEquiv.subgroupCongr lineGroup_eq.symm).toEquiv, hcard]
  exact ⟨(e.trans (MonoidHom.ofInjective (d4Rho_injective hX))).trans
    (MulEquiv.subgroupCongr d4Rho_range)⟩

end CFSG.HardMathSupport.Dickson.Bal207.Fam3D42

end

module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.WeylE6Data
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter

public noncomputable section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6

section Abstract

variable {G : Type*} [Group G]

theorem exists_three_subgroup_centralizer (E : Subgroup G) [Finite E]
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    {s : G} (hs3 : s ^ 3 = 1) :
    ∃ B : Subgroup G, B ≤ E ⊔ Subgroup.zpowers s ∧
      B ≤ Subgroup.centralizer ({s} : Set G) ∧ Finite B ∧ (∀ x ∈ B, x ^ 3 = 1) ∧
      ((s ∈ E ∧ B = E) ∨
        (s ∉ E ∧ Nat.card B = 3 * Nat.card ↥(E ⊓ Subgroup.centralizer ({s} : Set G)))) := by
  by_cases hsE : s ∈ E
  · refine ⟨E, le_sup_left, fun a ha => ?_, inferInstance, hE3, Or.inl ⟨hsE, rfl⟩⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hE a ha s hsE)
  · set A : Subgroup G := E ⊓ Subgroup.centralizer ({s} : Set G) with hA
    have hAfin : Finite A := Finite.of_injective (Subgroup.inclusion (inf_le_left : A ≤ E))
      (Subgroup.inclusion_injective _)
    have hsC : ∀ a ∈ A, a * s = s * a := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ha).2
    have hcomm : ∀ (a : A) (t : Subgroup.zpowers s), Commute (A.subtype a) ((Subgroup.zpowers s).subtype t) := by
      intro a t
      obtain ⟨t, k, rfl⟩ := t
      have h : Commute (a : G) s := hsC a a.2
      exact h.zpow_right k
    let φ : A × Subgroup.zpowers s →* G := (A.subtype).noncommCoprod ((Subgroup.zpowers s).subtype) hcomm
    have hφ : ∀ a t, φ (a, t) = (a : G) * (t : G) := fun a t => by simp [φ]
    have hs1 : s ≠ 1 := fun h => hsE (h ▸ one_mem E)
    have hord : orderOf s = 3 := orderOf_eq_prime hs3 hs1
    have hzfin : Finite (Subgroup.zpowers s) :=
      finite_zpowers.2 (orderOf_pos_iff.1 (by rw [hord]; norm_num))
    have hinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      rintro ⟨a, t⟩ ha
      rw [MonoidHom.mem_ker, hφ] at ha
      have hat : (a : G) = ((t : G))⁻¹ := eq_inv_of_mul_eq_one_left ha
      have ht1 : (t : G) = 1 := by
        by_contra ht1
        have htA : (t : G) ∈ A := by
          have : ((t : G))⁻¹ ∈ A := hat ▸ a.2
          simpa using this
        have hle : Subgroup.zpowers (t : G) ≤ Subgroup.zpowers s :=
          (Subgroup.zpowers_le).2 t.2
        have hto : orderOf (t : G) = 3 := by
          have : (t : G) ^ 3 = 1 := by
            obtain ⟨t, k, rfl⟩ := t
            show (s ^ k) ^ 3 = 1
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs3, one_zpow]
          exact orderOf_eq_prime this ht1
        have hcard : Nat.card (Subgroup.zpowers s) ≤ Nat.card (Subgroup.zpowers (t : G)) := by
          rw [Nat.card_zpowers, Nat.card_zpowers, hord, hto]
        have heq := Subgroup.eq_of_le_of_card_ge hle hcard
        have hsz : s ∈ Subgroup.zpowers (t : G) := by rw [heq]; exact Subgroup.mem_zpowers s
        have hsA : s ∈ A := (Subgroup.zpowers_le).2 htA hsz
        exact hsE (Subgroup.mem_inf.1 hsA).1
      have ha1 : (a : G) = 1 := by rw [hat, ht1, inv_one]
      exact Prod.ext (Subtype.ext ha1) (Subtype.ext ht1)
    refine ⟨φ.range, ?_, ?_, ?_, ?_, Or.inr ⟨hsE, ?_⟩⟩
    · rintro _ ⟨⟨a, t⟩, rfl⟩
      rw [hφ]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.1 a.2).1)
        (Subgroup.mem_sup_right t.2)
    · rintro _ ⟨⟨a, t⟩, rfl⟩
      rw [hφ]
      refine mul_mem (Subgroup.mem_inf.1 a.2).2 ?_
      exact (Subgroup.zpowers_le (g := s) (H := Subgroup.centralizer ({s} : Set G))).2
        (Subgroup.mem_centralizer_singleton_iff.2 rfl) t.2
    · have : Finite (A × Subgroup.zpowers s) := inferInstance
      exact Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    · rintro _ ⟨⟨a, t⟩, rfl⟩
      have hc : Commute (a : G) (t : G) := hcomm a t
      rw [hφ, hc.mul_pow]
      have ha3 : (a : G) ^ 3 = 1 := hE3 a (Subgroup.mem_inf.1 a.2).1
      have ht3 : (t : G) ^ 3 = 1 := by
        obtain ⟨t, k, rfl⟩ := t
        show (s ^ k) ^ 3 = 1
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs3, one_zpow]
      rw [ha3, ht3, one_mul]
    · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
        hord, mul_comm]

end Abstract

section Torsion

set_option linter.unusedSectionVars false

variable {τ : Tag} {L : Type} [Field L]

variable (τ L) in
@[expose] def psi3 : (Fin τ.rank → rootsOfUnity 3 L) →* ModGL τ L :=
  (rootDiagUnitHom τ L).comp (MonoidHom.pi fun i =>
    (rootsOfUnity 3 L).subtype.comp (Pi.evalMonoidHom _ i))

variable (τ L) in
@[expose] def E3 : Subgroup (ModGL τ L) := (psi3 τ L).range

theorem psi3_apply (f : Fin τ.rank → rootsOfUnity 3 L) :
    psi3 τ L f = rootDiagUnit τ (fun i => ((f i : rootsOfUnity 3 L) : Lˣ)) := rfl

theorem psi3_injective : Function.Injective (psi3 τ L) := by
  intro f g h
  have := rootDiagUnit_injective (τ := τ) (K := L) h
  funext i
  exact Subtype.ext (congrFun this i)

theorem card_E3 (h3 : Nat.card (rootsOfUnity 3 L) = 3) : Nat.card (E3 τ L) = 3 ^ τ.rank := by
  rw [E3, Nat.card_congr (MonoidHom.ofInjective psi3_injective).toEquiv.symm, Nat.card_fun, h3,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem finite_E3 (h3 : Nat.card (rootsOfUnity 3 L) = 3) : Finite (E3 τ L) :=
  Nat.finite_of_card_ne_zero (by rw [card_E3 h3]; positivity)

theorem E3_cube {x : ModGL τ L} (hx : x ∈ E3 τ L) : x ^ 3 = 1 := by
  obtain ⟨f, rfl⟩ := hx
  rw [← map_pow]
  convert map_one (psi3 τ L)
  funext i
  exact Subtype.ext (by simpa using (mem_rootsOfUnity 3 _).1 (f i).2)

theorem psi3_commute {s : ModGL τ L} (hs : s ∈ monomialSubgroup τ L)
    (f : Fin τ.rank → rootsOfUnity 3 L)
    (hf : ∀ v, rootChar (fun i => ((f i : rootsOfUnity 3 L) : Lˣ))
        (weylQuotientHom τ L ⟨s, hs⟩ • v) = rootChar (fun i => ((f i : rootsOfUnity 3 L) : Lˣ)) v) :
    s * psi3 τ L f = psi3 τ L f * s := by
  obtain ⟨w, h, hh, rfl⟩ := monomialSubgroup_le_torusWeylCosets hs
  have hπ : weylQuotientHom τ L ⟨h * canonicalRep (coxeterSystem τ) L w, hs⟩ = w :=
    weylQuotientHom_eq (by
      simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w))
  rw [hπ] at hf
  have hn := (rootDiagUnit_eq_conj_canonicalRep_iff
    (fun i => ((f i : rootsOfUnity 3 L) : Lˣ)) (fun i => ((f i : rootsOfUnity 3 L) : Lˣ)) w).2 hf
  have hc := rootDiagUnit_mul_comm_of_mem_torusGroup
    (fun i => ((f i : rootsOfUnity 3 L) : Lˣ)) hh
  rw [psi3_apply]
  calc h * canonicalRep (coxeterSystem τ) L w *
        rootDiagUnit τ (fun i => ((f i : rootsOfUnity 3 L) : Lˣ))
      = h * (canonicalRep (coxeterSystem τ) L w *
        rootDiagUnit τ (fun i => ((f i : rootsOfUnity 3 L) : Lˣ)) *
          (canonicalRep (coxeterSystem τ) L w)⁻¹) * canonicalRep (coxeterSystem τ) L w := by group
    _ = h * rootDiagUnit τ (fun i => ((f i : rootsOfUnity 3 L) : Lˣ)) *
          canonicalRep (coxeterSystem τ) L w := by rw [← hn]
    _ = rootDiagUnit τ (fun i => ((f i : rootsOfUnity 3 L) : Lˣ)) * h *
          canonicalRep (coxeterSystem τ) L w := by rw [hc]
    _ = _ := by group

theorem prodZpowSum {G ι : Type*} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, zpow_add, ih]

variable (τ) in
@[expose] def fz (ζ : rootsOfUnity 3 L) (z : Fin τ.rank → ZMod 3) : Fin τ.rank → rootsOfUnity 3 L :=
  fun i => ζ ^ (z i).val

theorem fz_injective {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3) :
    Function.Injective (fz τ ζ) := by
  intro z z' h
  funext i
  have h1 := congrFun h i
  simp only [fz] at h1
  rw [pow_eq_pow_iff_modEq, hζ] at h1
  have h2 : (z i).val = (z' i).val :=
    Nat.ModEq.eq_of_lt_of_lt h1 (ZMod.val_lt _) (ZMod.val_lt _)
  exact ZMod.val_injective 3 h2

theorem rootChar_fz {ζ : rootsOfUnity 3 L} (z : Fin τ.rank → ZMod 3) (v : Fin τ.rank → ℤ) :
    rootChar (fun i => ((fz τ ζ z i : rootsOfUnity 3 L) : Lˣ)) v =
      ((ζ : Lˣ)) ^ (∑ i, ((z i).val : ℤ) * v i) := by
  rw [rootChar, ← prodZpowSum]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [fz, Subgroup.coe_pow]
  rw [← zpow_natCast, ← zpow_mul]

theorem psi3_fz_commute {ζ : rootsOfUnity 3 L} (hζ : orderOf ζ = 3) {s : ModGL τ L}
    (hs : s ∈ monomialSubgroup τ L) {z : Fin τ.rank → ZMod 3}
    (hz : z ∈ fixed3 (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
      (weylMatrix (weylQuotientHom τ L ⟨s, hs⟩))) :
    s * psi3 τ L (fz τ ζ z) = psi3 τ L (fz τ ζ z) * s := by
  refine psi3_commute hs _ fun v => ?_
  rw [rootChar_fz, rootChar_fz, zpow_eq_zpow_iff_modEq, Subgroup.orderOf_coe ζ, hζ]
  set w := weylQuotientHom τ L ⟨s, hs⟩ with hw
  rw [← ZMod.intCast_eq_intCast_iff]
  have hz' := (Finset.mem_filter.1 hz).2
  have key : ∑ j, (v j : ZMod 3) * ∑ k, z k * ((((1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) * (weylMatrix w - 1)) k j : ℤ) : ZMod 3) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hz' j, mul_zero]
  have hcast : ∀ i, (((z i).val : ℤ) : ZMod 3) = z i := fun i => by simp
  push_cast
  simp only [ZMod.natCast_zmod_val]
  rw [← weylMatrix_mulVec]
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
  simp only [one_mul, Matrix.sub_apply, Matrix.one_apply, Int.cast_sub, Int.cast_ite, Int.cast_one,
    Int.cast_zero, mul_sub, Finset.mul_sum] at key
  obtain ⟨Mc, hMc⟩ : ∃ Mc : Fin τ.rank → Fin τ.rank → ℤ, ∀ x y, weylMatrix w x y = Mc x y :=
    ⟨fun x y => weylMatrix w x y, fun _ _ => rfl⟩
  simp only [hMc] at key ⊢
  have h1 : ∑ x, ∑ y, (v x : ZMod 3) * (z y * ((Mc y x : ℤ) : ZMod 3)) =
      ∑ x, z x * ∑ y, ((Mc x y : ℤ) : ZMod 3) * (v y : ZMod 3) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have h2 : ∑ x, ∑ y, (v x : ZMod 3) * (z y * if y = x then 1 else 0) =
      ∑ x, z x * (v x : ZMod 3) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [mul_comm]
  have key2 : ∑ x, ∑ y, (v x : ZMod 3) * (z y * ((Mc y x : ℤ) : ZMod 3)) -
      ∑ x, ∑ y, (v x : ZMod 3) * (z y * if y = x then 1 else 0) = 0 :=
    Eq.trans ((Finset.sum_congr rfl fun x _ => Finset.sum_sub_distrib _ _).trans
      (Finset.sum_sub_distrib _ _)).symm key
  rw [h1, h2] at key2
  exact sub_eq_zero.1 key2

end Torsion

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross

module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNFix

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Timmesfeld.ExceptionalOrders (zpowMatrix zpowMatrix_apply zpowMatrix_zpowMatrix)
open scoped Matrix

section MatrixPart

variable {τ : Tag}

@[expose] def weylMat (v : WeylGroup τ) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  Matrix.of fun i j => (v • (Pi.single j 1 : Fin τ.rank → ℤ)) i

theorem weylMat_mulVec (v : WeylGroup τ) (u : Fin τ.rank → ℤ) : weylMat v *ᵥ u = v • u := by
  have hv : u = ∑ j, u j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : v • u = ∑ j, u j • (v • (Pi.single j 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm v (u j) _
  ext i
  rw [hw, Finset.sum_apply]
  simp [Matrix.mulVec, dotProduct, weylMat, mul_comm]

variable {L : Type} [Field L]

theorem weylTuple_eq_zpowMatrix (v : WeylGroup τ) (b : Fin τ.rank → Lˣ) :
    weylTuple v b = zpowMatrix (weylMat v⁻¹) b := by
  funext j
  simp only [weylTuple, rootChar, zpowMatrix_apply, weylMat, Matrix.of_apply]

theorem zpowMatrix_sub (M N : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (t : Fin τ.rank → Lˣ) :
    zpowMatrix (M - N) t = zpowMatrix M t * (zpowMatrix N t)⁻¹ := by
  funext j
  simp only [zpowMatrix_apply, Matrix.sub_apply, zpow_sub,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib, Pi.mul_apply, Pi.inv_apply]

theorem mul_inv_weylTuple_pow (w : WeylGroup τ) (q : ℕ) (c : Fin τ.rank → Lˣ) :
    c * (weylTuple w fun i => c i ^ q)⁻¹ = zpowMatrix (1 - (q : ℤ) • weylMat w⁻¹) c := by
  rw [zpowMatrix_sub, show zpowMatrix (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) c = c from
    CFSG.Timmesfeld.ExceptionalOrders.zpowMatrix_one c]
  congr 2
  funext j
  rw [weylTuple_eq_zpowMatrix]
  simp only [zpowMatrix_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul]

theorem det_one_sub_smul_weylMat_ne_zero (w : WeylGroup τ) {q : ℕ} (hq : 2 ≤ q) :
    (1 - (q : ℤ) • weylMat w⁻¹).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, weylMat_mulVec, sub_eq_zero] at hv
  have iter : ∀ j : ℕ, v = ((q : ℤ) ^ j) • ((w⁻¹ ^ j) • v) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc v = ((q : ℤ) ^ j) • ((w⁻¹ ^ j) • v) := ih
        _ = ((q : ℤ) ^ j) • ((w⁻¹ ^ j) • ((q : ℤ) • (w⁻¹ • v))) := by rw [← hv]
        _ = ((q : ℤ) ^ (j + 1)) • ((w⁻¹ ^ (j + 1)) • v) := by
          rw [pow_succ, pow_succ, mul_smul (w⁻¹ ^ j) w⁻¹ v,
            smul_comm (w⁻¹ ^ j) (q : ℤ) (w⁻¹ • v), smul_smul ((q : ℤ) ^ j) (q : ℤ)]
  have hk : 0 < orderOf w⁻¹ := orderOf_pos _
  have h1 := iter (orderOf w⁻¹)
  rw [pow_orderOf_eq_one, one_smul] at h1
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.1 hv0
  have h2 : v i = ((q : ℤ) ^ orderOf w⁻¹) * v i := by
    conv_lhs => rw [h1]
    rfl
  have h3 : ((q : ℤ) ^ orderOf w⁻¹) = 1 := by
    have : ((q : ℤ) ^ orderOf w⁻¹ - 1) * v i = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hi
  have h4 : (1 : ℤ) < (q : ℤ) ^ orderOf w⁻¹ :=
    one_lt_pow₀ (by omega) hk.ne'
  omega

end MatrixPart

section Surj

variable {L : Type} [Field L] [IsAlgClosed L]

theorem exists_zpow_eq (c : Lˣ) {d : ℤ} (hd : d ≠ 0) : ∃ x : Lˣ, x ^ d = c := by
  have hroot : ∀ (c : Lˣ) (m : ℕ), m ≠ 0 → ∃ z : Lˣ, z ^ m = c := fun c m hm => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((c : Lˣ) : L) (Nat.pos_of_ne_zero hm)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hm] at hz
      exact c.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · obtain ⟨z, hz⟩ := hroot c m (fun h => hd (by simp [h]))
    exact ⟨z, by rw [zpow_natCast, hz]⟩
  · obtain ⟨z, hz⟩ := hroot c⁻¹ m (fun h => hd (by simp [h]))
    exact ⟨z, by rw [zpow_neg, zpow_natCast, hz, inv_inv]⟩

theorem exists_zpowMatrix_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) (hB : B.det ≠ 0)
    (h : Fin r → Lˣ) : ∃ a : Fin r → Lˣ, zpowMatrix B a = h := by
  choose t ht using fun i => exists_zpow_eq (h i) hB
  refine ⟨zpowMatrix (Matrix.adjugate B) t, ?_⟩
  rw [zpowMatrix_zpowMatrix, Matrix.adjugate_mul]
  funext j
  rw [zpowMatrix_apply, Finset.prod_eq_single j (fun i _ hij => by
      simp [Matrix.smul_apply, hij])
    (fun hj => absurd (Finset.mem_univ j) hj)]
  simpa [Matrix.smul_apply, Matrix.one_apply] using ht j

end Surj

section Torus

variable {τ : Tag} {L : Type} [Field L]

theorem negPhi_rootDiagUnit_gen (Fr : L →+* L) (w : WeylGroup τ) (a : Fin τ.rank → Lˣ) :
    negPhi Fr (canonicalRep (coxeterSystem τ) L w) (rootDiagUnit τ a) =
      rootDiagUnit τ (weylTuple w fun i => Units.map Fr.toMonoidHom (a i)) := by
  rw [negPhi_apply, show Units.map (entrywiseHom Fr) (rootDiagUnit τ a) =
      rootDiagUnit τ fun i => Units.map Fr.toMonoidHom (a i) from
    Units.ext (entrywise_rootDiag Fr a), canonicalRep_conj_rootDiagUnit]

theorem negPhi_rootDiagUnit_gen_pow (Fr : L →+* L) (w : WeylGroup τ) {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (a : Fin τ.rank → Lˣ) :
    negPhi Fr (canonicalRep (coxeterSystem τ) L w) (rootDiagUnit τ a) =
      rootDiagUnit τ (weylTuple w fun i => a i ^ q) := by
  rw [negPhi_rootDiagUnit_gen]
  congr 2
  funext i
  exact Units.ext (by simp [hFr])

theorem exists_mul_negPhi_inv_eq_gen [IsAlgClosed L] (Fr : L →+* L) (w : WeylGroup τ) {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) {h : ModGL τ L} (hh : h ∈ torusGroup τ L) :
    ∃ t ∈ torusGroup τ L,
      t * (negPhi Fr (canonicalRep (coxeterSystem τ) L w) t)⁻¹ = h := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  obtain ⟨c, hc⟩ := exists_zpowMatrix_eq _ (det_one_sub_smul_weylMat_ne_zero w hq) a
  refine ⟨rootDiagUnit τ c, rootDiagUnit_mem_torusGroup c, ?_⟩
  rw [negPhi_rootDiagUnit_gen_pow Fr w hFr]
  have key : ∀ b b' : Fin τ.rank → Lˣ,
      rootDiagUnit τ b * (rootDiagUnit τ b')⁻¹ = rootDiagUnit τ (b * b'⁻¹) := fun b b' => by
    change rootDiagUnitHom τ L b * (rootDiagUnitHom τ L b')⁻¹ = rootDiagUnitHom τ L (b * b'⁻¹)
    rw [map_mul, map_inv]
  rw [key, mul_inv_weylTuple_pow, hc]

end Torus

section Weyl

variable {τ : Tag} {L : Type} [Field L]

theorem exists_mapsRootLines_frobenius (Fr : L →+* L) {x : ModGL τ L}
    (hx : x ∈ monomialSubgroup τ L) :
    ∃ u : WeylGroup τ, MapsRootLines x u ∧
      MapsRootLines (Units.map (entrywiseHom Fr) x) u := by
  obtain ⟨u, k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets hx
  refine ⟨u, ?_, ?_⟩
  · rw [hxk]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep u)
  · have hk' : Units.map (entrywiseHom Fr) k ∈ torusGroup τ L := by
      rw [entrywise_eq_baseChangeGL]
      exact CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup Fr hk
    rw [hxk, map_mul, frobenius_canonicalRep]
    simpa using (mapsRootLines_of_mem_torusGroup hk').mul (mapsRootLines_canonicalRep u)

theorem NFixToWeyl_mem_centralizer (Fr : L →+* L) (w : WeylGroup τ)
    (x : NFix (canonicalRep (coxeterSystem τ) L w) Fr) :
    NFixToWeyl (canonicalRep (coxeterSystem τ) L w) Fr x ∈
      Subgroup.centralizer ({w} : Set (WeylGroup τ)) := by
  obtain ⟨u, h1, h2⟩ := exists_mapsRootLines_frobenius Fr x.2.1
  rw [NFixToWeyl_eq h1, Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff.1 hg]
  have h3 : MapsRootLines
      (canonicalRep (coxeterSystem τ) L w * Units.map (entrywiseHom Fr) (x : ModGL τ L) *
        (canonicalRep (coxeterSystem τ) L w)⁻¹) (w * u * w⁻¹) :=
    ((mapsRootLines_canonicalRep (R := L) w).mul h2).mul (mapsRootLines_canonicalRep (R := L) w).inv
  have hxf : negPhi Fr (canonicalRep (coxeterSystem τ) L w) (x : ModGL τ L) = x := x.2.2
  rw [negPhi_apply] at hxf
  rw [hxf] at h3
  have h4 : w * u * w⁻¹ = u := h3.unique h1
  rwa [mul_inv_eq_iff_eq_mul] at h4

theorem NFixToWeyl_surjective_centralizer [IsAlgClosed L] (Fr : L →+* L) (w : WeylGroup τ)
    {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) {u : WeylGroup τ}
    (hu : u ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ))) :
    ∃ x : NFix (canonicalRep (coxeterSystem τ) L w) Fr,
      NFixToWeyl (canonicalRep (coxeterSystem τ) L w) Fr x = u := by
  set n := canonicalRep (coxeterSystem τ) L w with hn
  set nw := canonicalRep (coxeterSystem τ) L u with hnw
  have hcomm : w * u = u * w := Subgroup.mem_centralizer_iff.1 hu w (Set.mem_singleton w)
  set s : ModGL τ L := n * nw * n⁻¹ * nw⁻¹ with hs
  have hsm : s ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup L w)
      (canonicalRep_mem_monomialSubgroup L u))
      (inv_mem (canonicalRep_mem_monomialSubgroup L w)))
      (inv_mem (canonicalRep_mem_monomialSubgroup L u))
  have hs1 : MapsRootLines s 1 := by
    have h := (((mapsRootLines_canonicalRep (R := L) w).mul
      (mapsRootLines_canonicalRep (R := L) u)).mul
        (mapsRootLines_canonicalRep (R := L) w).inv).mul
      (mapsRootLines_canonicalRep (R := L) u).inv
    have e : w * u * w⁻¹ * u⁻¹ = 1 := by
      rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]
    rwa [e] at h
  have hstor : s ∈ torusGroup τ L := mem_torusGroup_of_mapsRootLines_one hsm hs1
  obtain ⟨t, ht, hts⟩ := exists_mul_negPhi_inv_eq_gen Fr w hq hFr hstor
  have hnegt : negPhi Fr n t ∈ torusGroup τ L := negPhi_mem_torus Fr w ht
  have hts' : negPhi Fr n t * s = t := by
    rw [← hts, torusGroup_mul_comm ht (inv_mem hnegt), mul_inv_cancel_left]
  have hnu : negPhi Fr n nw = s * nw := by
    have hF : Units.map (entrywiseHom Fr) nw = nw := frobenius_canonicalRep Fr u
    rw [negPhi_apply, hF, hs]
    group
  have hxm : t * nw ∈ monomialSubgroup τ L :=
    mul_mem (torusGroup_le_monomialSubgroup' ht) (canonicalRep_mem_monomialSubgroup L u)
  have hxf : negPhi Fr n (t * nw) = t * nw := by
    rw [map_mul, hnu, ← mul_assoc, hts']
  have hmaps : MapsRootLines (t * nw) u := by
    simpa using (mapsRootLines_of_mem_torusGroup ht).mul (mapsRootLines_canonicalRep (R := L) u)
  exact ⟨⟨t * nw, hxm, hxf⟩, NFixToWeyl_eq hmaps⟩

theorem NFixToWeyl_range_eq_centralizer [IsAlgClosed L] (Fr : L →+* L) (w : WeylGroup τ)
    {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) :
    (NFixToWeyl (canonicalRep (coxeterSystem τ) L w) Fr).range =
      Subgroup.centralizer ({w} : Set (WeylGroup τ)) := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    exact NFixToWeyl_mem_centralizer Fr w x
  · intro hu
    exact NFixToWeyl_surjective_centralizer Fr w hq hFr hu

theorem card_NFix_gen [IsAlgClosed L] (Fr : L →+* L) (w : WeylGroup τ) {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) :
    Nat.card (NFix (canonicalRep (coxeterSystem τ) L w) Fr) =
      Nat.card (twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
        (Units.map (entrywiseHom Fr))) *
      Nat.card (Subgroup.centralizer ({w} : Set (WeylGroup τ))) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (NFixToWeyl _ Fr).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (NFixToWeyl _ Fr)).toEquiv,
    NFixToWeyl_range_eq_centralizer Fr w hq hFr, NFixToWeyl_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (twistedTorusOf_le_NFix (canonicalRep (coxeterSystem τ) L w) Fr)).toEquiv, mul_comm]

end Weyl

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end

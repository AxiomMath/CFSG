module

public import CFSG.RankThree.PartOne.KE.CTLangData
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
public import CFSG.RankThree.PartOne.KE.CTLang

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (baseChangeGL_mem_torusGroup)

section Basic

variable {τ : Tag} {L : Type} [Field L]

@[expose] def negPhi (Fr : L →+* L) (n : ModGL τ L) : ModGL τ L →* ModGL τ L :=
  (MulAut.conj n).toMonoidHom.comp (Units.map (entrywiseHom Fr))

@[expose] def NFix (n : ModGL τ L) (Fr : L →+* L) : Subgroup (ModGL τ L) :=
  monomialSubgroup τ L ⊓ (negPhi Fr n).eqLocus (MonoidHom.id _)

theorem negPhi_apply (Fr : L →+* L) (n x : ModGL τ L) :
    negPhi Fr n x = n * Units.map (entrywiseHom Fr) x * n⁻¹ := rfl

theorem mem_NFix {n : ModGL τ L} {Fr : L →+* L} {x : ModGL τ L} :
    x ∈ NFix n Fr ↔ x ∈ monomialSubgroup τ L ∧ negPhi Fr n x = x := Iff.rfl

theorem NFix_le_monomialSubgroup (n : ModGL τ L) (Fr : L →+* L) :
    NFix n Fr ≤ monomialSubgroup τ L := inf_le_left

theorem torusGroup_le_monomialSubgroup' : torusGroup τ L ≤ monomialSubgroup τ L := le_sup_left

theorem twistedTorusOf_le_NFix (n : ModGL τ L) (Fr : L →+* L) :
    twistedTorusOf n (Units.map (entrywiseHom Fr)) ≤ NFix n Fr := fun _ hx =>
  ⟨torusGroup_le_monomialSubgroup' hx.1, hx.2⟩

theorem mem_twistedTorusOf_iff_negPhi {n : ModGL τ L} {Fr : L →+* L} {x : ModGL τ L} :
    x ∈ twistedTorusOf n (Units.map (entrywiseHom Fr)) ↔
      x ∈ torusGroup τ L ∧ negPhi Fr n x = x := Iff.rfl

theorem entrywise_eq_baseChangeGL (Fr : L →+* L) (x : ModGL τ L) :
    Units.map (entrywiseHom Fr) x = baseChangeGL Fr x := Units.ext rfl

theorem torusGroup_mul_comm [IsAlgClosed L] {x y : ModGL τ L} (hx : x ∈ torusGroup τ L)
    (hy : y ∈ torusGroup τ L) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

end Basic

section Torus

variable {τ : Tag} {L : Type} [Field L]

theorem weylTuple_eq_inv {w0 : WeylGroup τ} (hw0 : ∀ u : Fin τ.rank → ℤ, w0 • u = -u) (b : Fin τ.rank → Lˣ) :
    weylTuple w0 b = fun i => (b i)⁻¹ := by
  funext i
  have h1 : w0⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ) = -(Pi.single i 1 : Fin τ.rank → ℤ) := by
    have h := hw0 (w0⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))
    rw [smul_inv_smul] at h
    exact neg_eq_iff_eq_neg.1 h.symm
  rw [weylTuple, h1]
  have h2 : -(Pi.single i 1 : Fin τ.rank → ℤ) = (-1 : ℤ) • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    rw [neg_smul, one_smul]
  rw [h2, rootChar_zsmul, zpow_neg_one]
  congr 1
  simpa using rootChar_nsmul_single b i 1

theorem negPhi_rootDiagUnit (Fr : L →+* L) {w0 : WeylGroup τ} (hw0 : ∀ u : Fin τ.rank → ℤ, w0 • u = -u)
    (a : Fin τ.rank → Lˣ) :
    negPhi Fr (canonicalRep (coxeterSystem τ) L w0) (rootDiagUnit τ a) =
      rootDiagUnit τ (fun i => (Units.map Fr.toMonoidHom (a i))⁻¹) := by
  rw [negPhi_apply, show Units.map (entrywiseHom Fr) (rootDiagUnit τ a) =
      rootDiagUnit τ fun i => Units.map Fr.toMonoidHom (a i) from
    Units.ext (entrywise_rootDiag Fr a), canonicalRep_conj_rootDiagUnit,
    weylTuple_eq_inv hw0]

theorem exists_mul_negPhi_inv_eq [IsAlgClosed L] (Fr : L →+* L) {w0 : WeylGroup τ}
    (hw0 : ∀ u : Fin τ.rank → ℤ, w0 • u = -u) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {h : ModGL τ L}
    (hh : h ∈ torusGroup τ L) :
    ∃ t ∈ torusGroup τ L,
      t * (negPhi Fr (canonicalRep (coxeterSystem τ) L w0) t)⁻¹ = h := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hroot : ∀ i, ∃ z : Lˣ, z ^ (q + 1) = a i := fun i => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((a i : Lˣ) : L) (Nat.succ_pos q)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.succ_ne_zero q)] at hz
      exact (a i).ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose c hc using hroot
  refine ⟨rootDiagUnit τ c, rootDiagUnit_mem_torusGroup c, ?_⟩
  rw [negPhi_rootDiagUnit Fr hw0]
  have key : ∀ b b' : Fin τ.rank → Lˣ,
      rootDiagUnit τ b * (rootDiagUnit τ b')⁻¹ = rootDiagUnit τ (b * b'⁻¹) := fun b b' => by
    change rootDiagUnitHom τ L b * (rootDiagUnitHom τ L b')⁻¹ = rootDiagUnitHom τ L (b * b'⁻¹)
    rw [map_mul, map_inv]
  rw [key]
  congr 1
  funext i
  have hq : Units.map Fr.toMonoidHom (c i) = c i ^ q := Units.ext (by simp [hFr])
  simp only [Pi.mul_apply, Pi.inv_apply, inv_inv, hq]
  rw [← hc i, pow_succ']

end Torus

section WeylCentral

variable {τ : Tag}

theorem weylGroup_mul_comm_of_neg {w0 : WeylGroup τ} (hw0 : ∀ u : Fin τ.rank → ℤ, w0 • u = -u)
    (w : WeylGroup τ) : w0 * w = w * w0 :=
  FaithfulSMul.eq_of_smul_eq_smul (α := Fin τ.rank → ℤ) fun u => by
    rw [mul_smul, mul_smul, hw0, hw0, smul_neg]

end WeylCentral

section Weyl

variable {τ : Tag} {L : Type} [Field L]

theorem negPhi_mem_torus (Fr : L →+* L) (w0 : WeylGroup τ) {x : ModGL τ L}
    (hx : x ∈ torusGroup τ L) :
    negPhi Fr (canonicalRep (coxeterSystem τ) L w0) x ∈ torusGroup τ L := by
  rw [negPhi_apply, entrywise_eq_baseChangeGL]
  exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer w0) _).1
    (baseChangeGL_mem_torusGroup Fr hx)

theorem mem_torusGroup_of_mapsRootLines_one {g : ModGL τ L} (hg : g ∈ monomialSubgroup τ L)
    (h : MapsRootLines g 1) : g ∈ torusGroup τ L := by
  obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets hg
  have hmaps : MapsRootLines g w := by
    rw [hgk]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
  have hw : w = 1 := hmaps.unique h
  rw [hgk, hw, canonicalRep_one, mul_one]
  exact hk

@[expose] def NFixToWeyl (n : ModGL τ L) (Fr : L →+* L) : NFix n Fr →* WeylGroup τ :=
  (weylQuotientHom τ L).comp (Subgroup.inclusion (NFix_le_monomialSubgroup n Fr))

theorem NFixToWeyl_eq {n : ModGL τ L} {Fr : L →+* L} {x : NFix n Fr} {w : WeylGroup τ}
    (h : MapsRootLines (x : ModGL τ L) w) : NFixToWeyl n Fr x = w :=
  by
  have := weylQuotientHom_eq (g := (⟨x, NFix_le_monomialSubgroup n Fr x.2⟩ : monomialSubgroup τ L))
    h
  exact this

theorem NFix_conj_mem_twistedTorusOf {n : ModGL τ L} {Fr : L →+* L} {x t : ModGL τ L}
    (hx : x ∈ NFix n Fr) (ht : t ∈ twistedTorusOf n (Units.map (entrywiseHom Fr))) :
    x * t * x⁻¹ ∈ twistedTorusOf n (Units.map (entrywiseHom Fr)) := by
  refine ⟨?_, ?_⟩
  · have hxm : x ∈ monomialSubgroup τ L := hx.1
    have htm : t ∈ monomialSubgroup τ L := torusGroup_le_monomialSubgroup' ht.1
    have h := (inferInstance :
      ((torusGroup τ L).subgroupOf (monomialSubgroup τ L)).Normal).conj_mem
      ⟨t, htm⟩ (Subgroup.mem_subgroupOf.2 ht.1) ⟨x, hxm⟩
    exact Subgroup.mem_subgroupOf.1 h
  · have hxf : negPhi Fr n x = x := hx.2
    have htf : negPhi Fr n t = t := ht.2
    change negPhi Fr n (x * t * x⁻¹) = x * t * x⁻¹
    rw [map_mul, map_mul, map_inv, hxf, htf]

theorem NFixToWeyl_ker (n : ModGL τ L) (Fr : L →+* L) :
    (NFixToWeyl n Fr).ker =
      (twistedTorusOf n (Units.map (entrywiseHom Fr))).subgroupOf (NFix n Fr) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hmaps : MapsRootLines (x : ModGL τ L) 1 := by
      have := mapsRootLines_weylQuotientHom
        (⟨x, NFix_le_monomialSubgroup n Fr x.2⟩ : monomialSubgroup τ L)
      rwa [show weylQuotientHom τ L ⟨x, NFix_le_monomialSubgroup n Fr x.2⟩ = 1 from hx] at this
    exact ⟨mem_torusGroup_of_mapsRootLines_one (NFix_le_monomialSubgroup n Fr x.2) hmaps, x.2.2⟩
  · intro hx
    exact NFixToWeyl_eq (mapsRootLines_of_mem_torusGroup hx.1)

theorem NFixToWeyl_surjective [IsAlgClosed L] (Fr : L →+* L) {w0 : WeylGroup τ}
    (hw0 : ∀ u : Fin τ.rank → ℤ, w0 • u = -u) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) :
    Function.Surjective (NFixToWeyl (canonicalRep (coxeterSystem τ) L w0) Fr) := by
  intro w
  set n := canonicalRep (coxeterSystem τ) L w0 with hn
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  set s : ModGL τ L := n * nw * n⁻¹ * nw⁻¹ with hs
  have hsm : s ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup L w0)
      (canonicalRep_mem_monomialSubgroup L w))
      (inv_mem (canonicalRep_mem_monomialSubgroup L w0)))
      (inv_mem (canonicalRep_mem_monomialSubgroup L w))
  have hs1 : MapsRootLines s 1 := by
    have h := (((mapsRootLines_canonicalRep (R := L) w0).mul
      (mapsRootLines_canonicalRep (R := L) w)).mul
        (mapsRootLines_canonicalRep (R := L) w0).inv).mul
      (mapsRootLines_canonicalRep (R := L) w).inv
    have e : w0 * w * w0⁻¹ * w⁻¹ = 1 := by
      rw [weylGroup_mul_comm_of_neg hw0 w, mul_inv_cancel_right, mul_inv_cancel]
    rwa [e] at h
  have hstor : s ∈ torusGroup τ L := mem_torusGroup_of_mapsRootLines_one hsm hs1
  obtain ⟨t, ht, hts⟩ := exists_mul_negPhi_inv_eq Fr hw0 hFr hstor
  have hnegt : negPhi Fr n t ∈ torusGroup τ L := negPhi_mem_torus Fr w0 ht
  have hts' : negPhi Fr n t * s = t := by
    rw [← hts, torusGroup_mul_comm ht (inv_mem hnegt), mul_inv_cancel_left]
  have hnw : negPhi Fr n nw = s * nw := by
    have hF : Units.map (entrywiseHom Fr) nw = nw := frobenius_canonicalRep Fr w
    rw [negPhi_apply, hF, hs]
    group
  have hxm : t * nw ∈ monomialSubgroup τ L :=
    mul_mem (torusGroup_le_monomialSubgroup' ht) (canonicalRep_mem_monomialSubgroup L w)
  have hxf : negPhi Fr n (t * nw) = t * nw := by
    rw [map_mul, hnw, ← mul_assoc, hts']
  have hmaps : MapsRootLines (t * nw) w := by
    simpa using (mapsRootLines_of_mem_torusGroup ht).mul (mapsRootLines_canonicalRep (R := L) w)
  exact ⟨⟨t * nw, hxm, hxf⟩, NFixToWeyl_eq hmaps⟩

theorem card_NFix [IsAlgClosed L] (Fr : L →+* L) {w0 : WeylGroup τ}
    (hw0 : ∀ u : Fin τ.rank → ℤ, w0 • u = -u) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) :
    Nat.card (NFix (canonicalRep (coxeterSystem τ) L w0) Fr) =
      Nat.card (twistedTorusOf (canonicalRep (coxeterSystem τ) L w0)
        (Units.map (entrywiseHom Fr))) * Nat.card (WeylGroup τ) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (NFixToWeyl _ Fr).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (NFixToWeyl_surjective Fr hw0 hFr)).toEquiv, NFixToWeyl_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (twistedTorusOf_le_NFix (canonicalRep (coxeterSystem τ) L w0) Fr)).toEquiv, mul_comm]

end Weyl

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end

module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcCentTwAbstract
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenFix
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcWeylWords
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Timmesfeld.ExceptionalOrders (zpowMatrix zpowMatrix_apply)
open CFSG.HardMathSupport.Curtis.UnitaryLevi (Smat wordW wordW_append wordW_smul)
open scoped Matrix

section Roots

variable (F L : Type) [Field F] [Finite F] [Field L] [Algebra F L] [IsAlgClosure F L]

@[expose] def μC : Subgroup Lˣ := rootsOfUnity (Nat.card F + 1) L

variable {F L}

theorem mem_μC {ζ : Lˣ} : ζ ∈ μC F L ↔ ζ ^ (Nat.card F + 1) = 1 := mem_rootsOfUnity _ _

theorem exists_char_dvd_card (F : Type) [Field F] [Finite F] (L : Type) [Field L] [Algebra F L] :
    ∃ ℓ : ℕ, ℓ.Prime ∧ CharP L ℓ ∧ ℓ ∣ Nat.card F := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hℓ⟩
  have hq : Nat.card F = ringChar F ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP F (ringChar F) := ringChar.charP F
  refine ⟨ringChar F, hℓ, charP_of_injective_algebraMap (algebraMap F L).injective _, ?_⟩
  rw [hq]
  exact dvd_pow_self _ f.ne_zero

theorem neZero_card_succ (F L : Type) [Field F] [Finite F] [Field L] [Algebra F L] :
    NeZero (((Nat.card F + 1 : ℕ)) : L) := by
  refine ⟨fun h => ?_⟩
  obtain ⟨ℓ, hℓ, hcharL, hℓq⟩ := exists_char_dvd_card F L
  have h1 : ℓ ∣ Nat.card F + 1 := (CharP.cast_eq_zero_iff L ℓ _).1 h
  have h2 : ℓ ∣ 1 := (Nat.dvd_add_right hℓq).1 h1
  exact hℓ.one_lt.ne' (Nat.dvd_one.1 h2)

theorem natCard_μC : Nat.card (μC F L) = Nat.card F + 1 := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have := neZero_card_succ F L
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (Nat.card F + 1)
  exact hζ.card_rootsOfUnity

instance isCyclic_μC : IsCyclic (μC F L) := inferInstanceAs (IsCyclic (rootsOfUnity _ L))

theorem finite_μC : Finite (μC F L) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_μC]; exact Nat.succ_ne_zero _)

theorem exists_orderOf_three_μC (h3 : 3 ∣ Nat.card F + 1) : ∃ ω : μC F L, orderOf ω = 3 := by
  have := finite_μC (F := F) (L := L)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_prime_orderOf_dvd_card' 3 (by rw [natCard_μC]; exact h3)

end Roots

section MatrixPart

variable {τ : Tag}

theorem weylMat_eq_of_smul {v : WeylGroup τ} {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (h : ∀ u : Fin τ.rank → ℤ, v • u = M *ᵥ u) : weylMat v = M := by
  ext i j
  simp [weylMat, h, Matrix.mulVec_single]

theorem weylMat_wordW (l : List (Fin τ.rank)) :
    weylMat (wordW τ l) = (l.map (Smat τ)).prod :=
  weylMat_eq_of_smul fun u => wordW_smul τ l u

theorem wordW_inv (l : List (Fin τ.rank)) : (wordW τ l)⁻¹ = wordW τ l.reverse := by
  induction l with
  | nil => simp [wordW]
  | cons a l ih =>
    have e1 : wordW τ (a :: l) = simple τ a * wordW τ l := by simp [wordW]
    have e2 : wordW τ [a] = simple τ a := by simp [wordW]
    rw [e1, mul_inv_rev, ih, simple_inv, List.reverse_cons, wordW_append, e2]

@[expose] def Atw (w : WeylGroup τ) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ := (weylMat w⁻¹)ᵀ

theorem Atw_wordW (l : List (Fin τ.rank)) :
    Atw (wordW τ l) = ((l.reverse.map (Smat τ)).prod)ᵀ := by
  rw [Atw, wordW_inv, weylMat_wordW]

end MatrixPart

section NFixSetting

variable {τ : Tag} {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L] [IsAlgClosure F L]
  (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F)
  (w0 : WeylGroup τ) (hw0 : ∀ u : Fin τ.rank → ℤ, w0 • u = -u)

include hFr hw0 in
theorem negPhi_rootDiagUnit_eq_iff (a : Fin τ.rank → Lˣ) :
    negPhi Fr (canonicalRep (coxeterSystem τ) L w0) (rootDiagUnit τ a) = rootDiagUnit τ a ↔
      ∀ i, a i ^ (Nat.card F + 1) = 1 := by
  rw [negPhi_rootDiagUnit Fr hw0]
  have hq : ∀ i, Units.map Fr.toMonoidHom (a i) = a i ^ Nat.card F := fun i =>
    Units.ext (by simp [hFr])
  have key : ∀ i, (Units.map Fr.toMonoidHom (a i))⁻¹ = a i ↔ a i ^ (Nat.card F + 1) = 1 := by
    intro i
    rw [hq, inv_eq_iff_mul_eq_one, ← pow_succ]
  constructor
  · intro h i
    exact (key i).1 (congrFun (rootDiagUnit_injective h) i)
  · intro h
    exact congrArg (rootDiagUnit τ) (funext fun i => (key i).2 (h i))

include hFr hw0 in
theorem rootDiagUnit_mem_NFix (b : Fin τ.rank → Lˣ) (hb : ∀ i, b i ^ (Nat.card F + 1) = 1) :
    rootDiagUnit τ b ∈ NFix (canonicalRep (coxeterSystem τ) L w0) Fr := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  exact ⟨torusGroup_le_monomialSubgroup' (rootDiagUnit_mem_torusGroup b),
    (negPhi_rootDiagUnit_eq_iff Fr hFr w0 hw0 b).2 hb⟩

include hFr hw0 in
@[expose] def ιT : (Fin τ.rank → μC F L) →* NFix (canonicalRep (coxeterSystem τ) L w0) Fr where
  toFun b := ⟨rootDiagUnit τ (fun i => (b i : Lˣ)),
    rootDiagUnit_mem_NFix Fr hFr w0 hw0 _ (fun i => mem_μC.1 (b i).2)⟩
  map_one' := Subtype.ext (by
    show rootDiagUnit τ (fun _ => ((1 : μC F L) : Lˣ)) = 1
    exact rootDiagUnit_one)
  map_mul' b b' := Subtype.ext (by
    show rootDiagUnit τ (fun i => ((b i * b' i : μC F L) : Lˣ)) =
      rootDiagUnit τ (fun i => (b i : Lˣ)) * rootDiagUnit τ (fun i => (b' i : Lˣ))
    rw [← rootDiagUnit_mul]
    rfl)

include hFr hw0 in
theorem ιT_injective : Function.Injective (ιT Fr hFr w0 hw0) := by
  intro b b' h
  have h1 := rootDiagUnit_injective (congrArg Subtype.val h)
  funext i
  exact Subtype.ext (congrFun h1 i)

include hFr hw0 in
theorem NFixToWeyl_ιT (b : Fin τ.rank → μC F L) :
    NFixToWeyl (canonicalRep (coxeterSystem τ) L w0) Fr (ιT Fr hFr w0 hw0 b) = 1 := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  rw [← MonoidHom.mem_ker, NFixToWeyl_ker, Subgroup.mem_subgroupOf]
  exact ⟨rootDiagUnit_mem_torusGroup _,
    ((negPhi_rootDiagUnit_eq_iff Fr hFr w0 hw0 _).2 fun i => mem_μC.1 (b i).2)⟩

include hFr hw0 in
theorem NFixToWeyl_eq_one_mem_range (g : NFix (canonicalRep (coxeterSystem τ) L w0) Fr)
    (hg : NFixToWeyl (canonicalRep (coxeterSystem τ) L w0) Fr g = 1) :
    g ∈ (ιT Fr hFr w0 hw0).range := by
  have h1 : g ∈ (NFixToWeyl (canonicalRep (coxeterSystem τ) L w0) Fr).ker := hg
  rw [NFixToWeyl_ker, Subgroup.mem_subgroupOf] at h1
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (mem_twistedTorusOf_iff_negPhi.1 h1).1
  have hfix := (negPhi_rootDiagUnit_eq_iff Fr hFr w0 hw0 a).1 (by
    rw [← ha]; exact (mem_twistedTorusOf_iff_negPhi.1 h1).2)
  exact ⟨fun i => ⟨a i, mem_μC.2 (hfix i)⟩, Subtype.ext ha.symm⟩

include hFr hw0 in
theorem NFix_conj_ιT (g : NFix (canonicalRep (coxeterSystem τ) L w0) Fr)
    (t : Fin τ.rank → μC F L) :
    g * ιT Fr hFr w0 hw0 t * g⁻¹ = ιT Fr hFr w0 hw0
      (mactC (Atw (NFixToWeyl (canonicalRep (coxeterSystem τ) L w0) Fr g)) t) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  apply Subtype.ext
  obtain ⟨u, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets g.2.1
  have hmaps : MapsRootLines (g : ModGL τ L) u := by
    rw [hgk]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep (R := L) u)
  rw [NFixToWeyl_eq hmaps]
  change (g : ModGL τ L) * rootDiagUnit τ (fun i => (t i : Lˣ)) * (g : ModGL τ L)⁻¹ =
    rootDiagUnit τ (fun i => ((mactC (Atw u) t i : μC F L) : Lˣ))
  have e : (fun i => ((mactC (Atw u) t i : μC F L) : Lˣ)) =
      weylTuple u (fun i => (t i : Lˣ)) := by
    rw [weylTuple_eq_zpowMatrix]
    funext i
    rw [zpowMatrix_apply]
    simp [mactC, Atw]
  rw [e, ← canonicalRep_conj_rootDiagUnit, hgk]
  have e2 : k * canonicalRep (coxeterSystem τ) L u * rootDiagUnit τ (fun i => (t i : Lˣ)) *
      (k * canonicalRep (coxeterSystem τ) L u)⁻¹ =
      k * (canonicalRep (coxeterSystem τ) L u * rootDiagUnit τ (fun i => (t i : Lˣ)) *
        (canonicalRep (coxeterSystem τ) L u)⁻¹) * k⁻¹ := by group
  rw [e2]
  set D := canonicalRep (coxeterSystem τ) L u * rootDiagUnit τ (fun i => (t i : Lˣ)) *
    (canonicalRep (coxeterSystem τ) L u)⁻¹ with hD
  have hDt : D ∈ torusGroup τ L := by
    rw [hD, canonicalRep_conj_rootDiagUnit]
    exact rootDiagUnit_mem_torusGroup _
  exact (mul_inv_eq_iff_eq_mul).2 (torusGroup_mul_comm hk hDt)

end NFixSetting

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end

module

public import CFSG.ClassicalInvolution.Phan.Presentation
public import CFSG.LocalAnalysis.StandardType.PhanEBridgeTitsPhi

public noncomputable section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F : Type} [Field F] [Finite F] {f n : ℕ} [CharP F 2]
  {M : CoxeterMatrix (Fin n)} {G : Type} [Group G]
  {S : PhanFamilyE F 2 f M G}

theorem PhanFamilyE.Good.nodeTor_range_ne_bot (hF : Nat.card F = (2 ^ f) ^ 2)
    (hS : S.Good) (i : Fin n) : (S.nodeTor i).range ≠ ⊥ := by
  obtain ⟨u, hu⟩ := exists_normOne_ne_one hF
  have hu₁ : u ≠ 1 := by
    intro h
    exact hu (congrArg Subtype.val h)
  intro hbot
  have hmem : S.nodeTor i u ∈ (S.nodeTor i).range := ⟨u, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  apply hu₁
  apply torusTwo_injective (unitaryInvolution F 2 f)
  apply hS.inj i
  change S.nodeTor i u = S.nodeTor i 1
  rw [hmem, map_one]

theorem PhanFamilyE.Good.node_le_sup_iff (hF : Nat.card F = (2 ^ f) ^ 2) (hS : S.Good)
    (i j k : Fin n) :
    (S.ι i).range ≤ (S.ι j).range ⊔ (S.ι k).range ↔ i = j ∨ i = k := by
  constructor
  · intro hle
    by_contra hne
    have hij : i ≠ j := fun h => hne (Or.inl h)
    have hik : i ≠ k := fun h => hne (Or.inr h)
    let T : Fin n → Subgroup G := fun l => (S.nodeTor l).range
    have hpair : ((S.ι j).range ⊔ (S.ι k).range) ⊓ S.torus = T j ⊔ T k := by
      simpa only [iSup_pair] using hS.torus_inf {j, k} (by
        simpa only [Set.encard_singleton, one_add_one_eq_two] using
          Set.encard_insert_le ({k} : Set (Fin n)) j)
    have hTi : T i ≤ (S.ι i).range := by
      rintro x ⟨u, rfl⟩
      exact ⟨torusTwo (unitaryInvolution F 2 f) u, rfl⟩
    have hTiT : T i ≤ S.torus := le_iSup T i
    have hTiPair : T i ≤ T j ⊔ T k := by
      rw [← hpair]
      exact le_inf (hTi.trans hle) hTiT
    have hrest : T j ⊔ T k ≤ ⨆ l, ⨆ (_ : l ≠ i), T l :=
      sup_le (le_iSup₂_of_le j hij.symm le_rfl) (le_iSup₂_of_le k hik.symm le_rfl)
    have hdis : Disjoint (T i) (⨆ l, ⨆ (_ : l ≠ i), T l) :=
      iSupIndep_def.mp hS.indep i
    exact PhanFamilyE.Good.nodeTor_range_ne_bot hF hS i
      ((inf_eq_left.mpr (hTiPair.trans hrest)).symm.trans (disjoint_iff.mp hdis))
  · rintro (rfl | rfl)
    · exact le_sup_left
    · exact le_sup_right


open CFSG.LieType.CurtisTits

private noncomputable def firstNode
    (P : PhanPresentation.PartIndex (fun i => (S.ι i).range)) : Fin n :=
  P.property.choose

private noncomputable def secondNode
    (P : PhanPresentation.PartIndex (fun i => (S.ι i).range)) : Fin n :=
  P.property.choose_spec.choose

private theorem part_eq
    (P : PhanPresentation.PartIndex (fun i => (S.ι i).range)) :
    P.val = (S.ι (firstNode P)).range ⊔ (S.ι (secondNode P)).range :=
  P.property.choose_spec.choose_spec

private noncomputable def nodeSet
    (P : PhanPresentation.PartIndex (fun i => (S.ι i).range)) : Set (Fin n) :=
  {firstNode P, secondNode P}

private theorem nodeSet_small
    (P : PhanPresentation.PartIndex (fun i => (S.ι i).range)) : (nodeSet P).encard ≤ 2 := by
  simpa only [nodeSet, Set.encard_singleton, one_add_one_eq_two] using
    Set.encard_insert_le ({secondNode P} : Set (Fin n)) (firstNode P)

private theorem node_le_part_iff (hF : Nat.card F = (2 ^ f) ^ 2) (hS : S.Good)
    (P : PhanPresentation.PartIndex (fun i => (S.ι i).range)) (i : Fin n) :
    (S.ι i).range ≤ P.val ↔ i ∈ nodeSet P := by
  rw [part_eq]
  simpa only [nodeSet, Set.mem_insert_iff, Set.mem_singleton_iff] using
    PhanFamilyE.Good.node_le_sup_iff hF hS i (firstNode P) (secondNode P)

private theorem nodeSet_mono (hF : Nat.card F = (2 ^ f) ^ 2) (hS : S.Good)
    {P Q : PhanPresentation.PartIndex (fun i => (S.ι i).range)} (hPQ : P ≤ Q) :
    nodeSet P ⊆ nodeSet Q := by
  intro i hi
  exact (node_le_part_iff hF hS Q i).mp (((node_le_part_iff hF hS P i).mpr hi).trans hPQ)

private theorem part_le_parab
    (P : PhanPresentation.PartIndex (fun i => (S.ι i).range)) : P.val ≤ S.parab (nodeSet P) := by
  rw [part_eq, PhanFamilyE.parab, nodeSet, iSup_pair]
  exact le_sup_right

variable {Y : Type} [Group Y]

private noncomputable def partMap
    (φ : ∀ J : Set (Fin n), J.encard ≤ 2 → S.parab J →* Y)
    (P : PhanPresentation.PartIndex (fun i => (S.ι i).range)) : P.val →* Y :=
  (φ (nodeSet P) (nodeSet_small P)).comp (Subgroup.inclusion (part_le_parab P))

theorem PhanFamilyE.Good.exists_amalgam_maps (hF : Nat.card F = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) (hS : S.Good) (T : PhanFamilyE F 2 f M Y) :
    ∃ Ψ : ∀ P, PhanPresentation.family (fun i => (S.ι i).range) P →* Y,
      IsCompatible (PhanPresentation.family (fun i => (S.ι i).range)) Ψ ∧
        ∀ P (i : Fin n) (hi : (S.ι i).range ≤ P.val) (a : Su F 2 f 2),
          Ψ P ⟨S.ι i a, hi ⟨a, rfl⟩⟩ = T.ι i a := by
  obtain ⟨φ, hφ, hcompat⟩ := hS.exists_phi_family hF hq T
  refine ⟨partMap φ, ?_, ?_⟩
  · intro P Q hPQ x y hxy
    change φ (nodeSet P) (nodeSet_small P) _ = φ (nodeSet Q) (nodeSet_small Q) _
    have hxP : (x : G) ∈ S.parab (nodeSet P) := part_le_parab P x.property
    have hxQ : (x : G) ∈ S.parab (nodeSet Q) := part_le_parab Q (hPQ x.property)
    exact (hcompat (nodeSet Q) (nodeSet P) (nodeSet_small Q) (nodeSet_small P)
      (nodeSet_mono hF hS hPQ) x hxP hxQ).trans
        (congrArg (φ (nodeSet Q) (nodeSet_small Q)) (Subtype.ext hxy))
  · intro P i hi a
    have hiJ : i ∈ nodeSet P := (node_le_part_iff hF hS P i).mp hi
    exact (hφ (nodeSet P) (nodeSet_small P)).2 i hiJ a

private theorem hom_ext_blocks (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (φ ψ : Su F 2 f 3 →* Y)
    (hleft : ∀ a, φ (embSUid (unitaryInvolution F 2 f) 2 a) =
      ψ (embSUid (unitaryInvolution F 2 f) 2 a))
    (hright : ∀ a, φ (embSUid (unitaryInvolution F 2 f) 0 a) =
      ψ (embSUid (unitaryInvolution F 2 f) 0 a)) : φ = ψ := by
  let E : Subgroup (Su F 2 f 3) := φ.eqLocus ψ
  have h12 : B12 F 2 f ≤ E := by
    rintro x ⟨a, rfl⟩
    exact hleft a
  have h23 : B23 F 2 f ≤ E := by
    rintro x ⟨a, rfl⟩
    exact hright a
  have htop : (⊤ : Subgroup (Su F 2 f 3)) ≤ E := by
    rw [← B12_sup_B23 hF (show 2 ^ f ≠ 2 by omega)]
    exact sup_le h12 h23
  ext x
  exact htop (Subgroup.mem_top x)

theorem PhanFamilyE.Good.isUniversal_of_isUniversalCompletion
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (hS : S.Good)
    (hU : IsUniversalCompletion.{0, 0, 0} (PhanPresentation.family (fun i => (S.ι i).range))) :
    S.IsUniversal := by
  intro Y _ T
  obtain ⟨φ, hcompat, hmaps⟩ := hS.exists_amalgam_maps hF hq T
  obtain ⟨ψ, hψ, _⟩ := hU Y φ hcompat
  have hi : ∀ i, ψ.comp (S.ι i) = T.ι i := by
    intro i
    ext a
    let P := PhanPresentation.nodeIndex (fun k => (S.ι k).range) i
    exact (hψ P ⟨S.ι i a, ⟨a, rfl⟩⟩).trans (hmaps P i le_rfl a)
  refine ⟨ψ, hi, ?_⟩
  intro i j hij h3
  apply hom_ext_blocks hF hq
  · intro a
    change ψ (S.θ i j (embSUid (unitaryInvolution F 2 f) 2 a)) = _
    exact (congrArg ψ (DFunLike.congr_fun (S.left i j hij h3) a)).trans
      ((DFunLike.congr_fun (hi i) a).trans (DFunLike.congr_fun (T.left i j hij h3) a).symm)
  · intro a
    change ψ (S.θ i j (embSUid (unitaryInvolution F 2 f) 0 a)) = _
    exact (congrArg ψ (DFunLike.congr_fun (S.right i j hij h3) a)).trans
      ((DFunLike.congr_fun (hi j) a).trans (DFunLike.congr_fun (T.right i j hij h3) a).symm)

end CFSG.ClassicalInvolution.Phan.PhanE

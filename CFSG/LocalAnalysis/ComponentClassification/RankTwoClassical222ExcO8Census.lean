module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8Defs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcHyp
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Large
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalReduce
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ExcO8

open Subgroup CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th.Native

variable {n : ℕ}

theorem fixNum_eq_ncard (g : Equiv.Perm (Fin n)) :
    fixNum g = {p : Fin n | g p = p}.ncard := by
  rw [fixNum, List.countP_eq_length_filter]
  set l := (List.finRange n).filter fun p => decide (g p = p) with hl
  have hnd : l.Nodup := (List.nodup_finRange n).filter _
  have hset : {p : Fin n | g p = p} = ↑l.toFinset := by
    ext p
    simp [hl]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem fixNum_conj (c g : Equiv.Perm (Fin n)) : fixNum (c * g * c⁻¹) = fixNum g := by
  rw [fixNum_eq_ncard, fixNum_eq_ncard]
  have h : {p : Fin n | (c * g * c⁻¹) p = p} = c '' {p | g p = p} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_image, Equiv.Perm.mul_apply]
    constructor
    · intro h
      refine ⟨c⁻¹ p, ?_, by simp⟩
      have h' := congrArg (fun x => c⁻¹ x) h
      simpa using h'
    · rintro ⟨q, hq, rfl⟩
      simp [hq]
  rw [h, Set.ncard_image_of_injective _ c.injective]

theorem maskProd_mem {X : Subgroup (Equiv.Perm (Fin n))} :
    ∀ (cur : List (Equiv.Perm (Fin n))) (m : ℕ), (∀ g ∈ cur, g ∈ X) → maskProd cur m ∈ X
  | [], _, _ => X.one_mem
  | g :: gs, m, h => by
    rw [maskProd]
    refine X.mul_mem ?_ (maskProd_mem gs (m / 2) fun x hx => h x (List.mem_cons_of_mem _ hx))
    split_ifs
    · exact h g List.mem_cons_self
    · exact X.one_mem

theorem badState_eq_false {G X : Subgroup (Equiv.Perm (Fin n))} {zs : List (Equiv.Perm (Fin n))}
    (hX : Hyp212In G {z | z ∈ zs} X) {forbid : List ℕ}
    (hf : ∀ y ∈ X, y ≠ 1 → fixNum y ∉ forbid) {cur : List (Equiv.Perm (Fin n))}
    (hcur : ∀ g ∈ cur, g ∈ X) : badState zs forbid cur = false := by
  have h1 : ∀ g ∈ cur, schreierPermEq (g * g) 1 = true := fun g hg => by
    rw [schreierPermEq_eq_true_iff, ← sq]
    exact hX.sq_eq_one g (hcur g hg)
  have h2 : ∀ g ∈ cur, ∀ h ∈ cur, schreierPermEq (g * h) (h * g) = true := fun g hg h hh => by
    rw [schreierPermEq_eq_true_iff]
    exact hX.mul_comm (hcur g hg) (hcur h hh)
  have h3 : ∀ m, (!schreierPermEq (tab (maskProd cur m)) 1 &&
      (zs.any (schreierPermEq (tab (maskProd cur m))) ||
        forbid.contains (fixNum (tab (maskProd cur m))))) = false := fun m => by
    rw [tab_eq]
    by_cases hp1 : maskProd cur m = 1
    · rw [hp1]
      have : schreierPermEq (1 : Equiv.Perm (Fin n)) 1 = true :=
        (schreierPermEq_eq_true_iff _ _).2 rfl
      rw [this]
      rfl
    · have hp := maskProd_mem cur m hcur
      have hz : zs.any (schreierPermEq (maskProd cur m)) = false := by
        rw [List.any_eq_false]
        intro z hz h
        rw [schreierPermEq_eq_true_iff] at h
        exact hX.not_mem z hz (h ▸ hp)
      have := hf _ hp hp1
      simp [hz, this]
  unfold badState
  rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.any_eq_false]
    intro g hg
    simp [h1 g hg]
  · rw [List.any_eq_false]
    intro g hg
    rw [Bool.not_eq_true, List.any_eq_false]
    intro h hh
    simp [h2 g hg h hh]
  · rw [List.any_eq_false]
    intro m _
    rw [h3 m]
    exact Bool.false_ne_true

theorem derivCheck_eq_false {G X : Subgroup (Equiv.Perm (Fin n))}
    {al : List (Equiv.Perm (Fin n))} {okW : List ℤ → Bool}
    (hal : ∀ w, okW w = true → evalCodes al w ∈ G) {zs : List (Equiv.Perm (Fin n))}
    (hX : Hyp212In G {z | z ∈ zs} X) {forbid : List ℕ}
    (hf : ∀ y ∈ X, y ≠ 1 → fixNum y ∉ forbid) :
    ∀ (steps : List (ℕ × List ℤ × ℕ)) (cur : List (Equiv.Perm (Fin n))),
      (∀ g ∈ cur, g ∈ X) → derivCheck al okW zs forbid cur steps = false
  | [], cur, hcur => by
    rw [derivCheck]
    exact badState_eq_false hX hf hcur
  | (m, w, i) :: rest, cur, hcur => by
    rw [derivCheck, badState_eq_false hX hf hcur, Bool.false_or]
    dsimp only
    simp only [Bool.and_eq_false_iff]
    by_cases h1 : schreierPermEq (tab (maskProd cur m)) 1 = true
    · exact Or.inl (Or.inl (Or.inl (Or.inl (by simp [h1]))))
    by_cases hw : okW w = true
    · by_cases h2 : schreierPermEq (tab (evalCodes al w) * tab (maskProd cur m))
          (tab (maskProd cur m) * tab (evalCodes al w)) = true
      · by_cases h3 : i < cur.length
        · refine Or.inr (derivCheck_eq_false hal hX hf rest _ fun g hg => ?_)
          rcases List.mem_append.1 hg with hg | hg
          · exact hcur g hg
          · rw [List.mem_singleton] at hg
            rw [hg]
            simp only [tab_eq] at h1 h2 ⊢
            have hp := maskProd_mem cur m hcur
            have hp1 : maskProd cur m ≠ 1 := fun h => h1 (by rw [h, schreierPermEq_eq_true_iff])
            have hcw := (schreierPermEq_eq_true_iff _ _).1 h2
            have hb : cur.getD i 1 ∈ X := by
              rw [List.getD_eq_getElem _ _ h3]
              exact hcur _ (List.getElem_mem h3)
            exact hX.conj_mem _ hp hp1 _ (hal w hw) hcw _ hb
        · exact Or.inl (Or.inr (by simpa using h3))
      · exact Or.inl (Or.inl (Or.inr (by simpa using h2)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (by simpa using hw))))

theorem exists_deriv_of_zip {al : List (Equiv.Perm (Fin n))} {okW : List ℤ → Bool}
    {zs : List (Equiv.Perm (Fin n))} {reps : List (Equiv.Perm (Fin n))}
    {ds : List (List (ℕ × List ℤ × ℕ))} {x : Equiv.Perm (Fin n)} {forbid : List ℕ}
    (hlen : ds.length = reps.length)
    (hall : (reps.zip ds).all
      (fun p => schreierPermEq p.1 x || derivCheck al okW zs forbid [x, p.1] p.2) = true) :
    ∀ r ∈ reps, r ≠ x → ∃ st, derivCheck al okW zs forbid [x, r] st = true := by
  intro r hr hrx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hi' : i < (reps.zip ds).length := by simp [hlen, hi]
  have h := List.all_eq_true.1 hall _ (List.getElem_mem hi')
  rw [List.getElem_zip] at h
  have hne : schreierPermEq reps[i] x = false := by
    rw [Bool.eq_false_iff, ne_eq, schreierPermEq_eq_true_iff]
    exact hrx
  rw [hne, Bool.false_or] at h
  exact ⟨_, h⟩

theorem zip_map_self {α β : Type*} (f : α → β) :
    ∀ l : List α, l.zip (l.map f) = l.map fun a => (a, f a)
  | [] => rfl
  | a :: l => by simp [zip_map_self f l]

theorem all_zip_repSizes {gens gensInv : Array Table} {cap : ℕ} {L : List (Equiv.Perm (Fin n))}
    {P : Equiv.Perm (Fin n) × ℕ → Bool}
    (h : (L.zip (repSizes n gens gensInv (L.map toTable) cap)).all P = true) :
    ∀ r ∈ L, P (r, (conjClosure n gens gensInv (toTable r) cap).1.size) = true := by
  intro r hr
  have e : L.zip (repSizes n gens gensInv (L.map toTable) cap) =
      L.map fun r => (r, (conjClosure n gens gensInv (toTable r) cap).1.size) := by
    rw [repSizes, List.map_map, zip_map_self]
    rfl
  rw [e, List.all_map, List.all_eq_true] at h
  exact h r hr

theorem exists_conj_le_of_card_le {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS : IsPGroup 2 S) (hmax : ∀ R : Subgroup G, IsPGroup 2 R → Nat.card R ≤ Nat.card S)
    {X : Subgroup G} (hX : IsPGroup 2 X) : ∃ c : G, ∀ x ∈ X, c * x * c⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hXR⟩ := hX.exists_le_sylow
  obtain ⟨R₂, hSR⟩ := hS.exists_le_sylow
  have hR₂ : (R₂ : Subgroup G) = S :=
    (Subgroup.eq_of_le_of_card_ge hSR (hmax R₂ R₂.isPGroup')).symm
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G R R₂
  refine ⟨c, fun x hx => ?_⟩
  have h2 : c * x * c⁻¹ ∈ ((c • R : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨x, hXR hx, rfl⟩
  rw [hc, hR₂] at h2
  exact h2

theorem exists_conj_le_of_card_le' {K S X : Subgroup (Equiv.Perm (Fin n))} (hSK : S ≤ K)
    (hS : IsPGroup 2 S)
    (hmax : ∀ R : Subgroup (Equiv.Perm (Fin n)), R ≤ K → IsPGroup 2 R → Nat.card R ≤ Nat.card S)
    (hXK : X ≤ K) (hX : IsPGroup 2 X) : ∃ c ∈ K, ∀ x ∈ X, c * x * c⁻¹ ∈ S := by
  have hS' : IsPGroup 2 (S.subgroupOf K) := hS.comap_of_injective K.subtype K.subtype_injective
  have hX' : IsPGroup 2 (X.subgroupOf K) := hX.comap_of_injective K.subtype K.subtype_injective
  have hcardS : Nat.card (S.subgroupOf K) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv
  have hmax' : ∀ R : Subgroup K, IsPGroup 2 R → Nat.card R ≤ Nat.card (S.subgroupOf K) := by
    intro R hR
    rw [hcardS, ← Subgroup.card_map_of_injective K.subtype_injective]
    exact hmax _ (by rintro _ ⟨y, -, rfl⟩; exact y.2) (hR.map K.subtype)
  obtain ⟨c, hc⟩ := exists_conj_le_of_card_le hS' hmax' hX'
  refine ⟨c, c.2, fun x hx => ?_⟩
  have := hc ⟨x, hXK hx⟩ (Subgroup.mem_subgroupOf.2 hx)
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

theorem exists_conj_le_of_odd_index {G T Q : Subgroup (Equiv.Perm (Fin n))}
    (hT : IsPGroup 2 T) (hidx : ¬ 2 ∣ (T.subgroupOf G).index) (hQG : Q ≤ G)
    (hQ : IsPGroup 2 Q) : ∃ g ∈ G, ∀ q ∈ Q, g * q * g⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 (T.subgroupOf G) := hT.comap_of_injective G.subtype G.subtype_injective
  let S' : Sylow 2 G := hT2.toSylow hidx
  have hQ' : IsPGroup 2 (Q.subgroupOf G) :=
    hQ.comap_of_injective G.subtype G.subtype_injective
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R S'
  refine ⟨g, g.2, fun q hq => ?_⟩
  have h2 : g * ⟨q, hQG hq⟩ * g⁻¹ ∈ ((g • R : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨_, hR (Subgroup.mem_subgroupOf.2 hq), rfl⟩
  rw [hg] at h2
  have h3 : g * ⟨q, hQG hq⟩ * g⁻¹ ∈ T.subgroupOf G := by simpa [S'] using h2
  rw [Subgroup.mem_subgroupOf] at h3
  simpa using h3

theorem isPGroup_of_sq {X : Subgroup (Equiv.Perm (Fin n))} (h : ∀ p ∈ X, p ^ 2 = 1) :
    IsPGroup 2 X := by
  refine IsPGroup.of_exponent_dvd_pow (n := 1) (Monoid.exponent_dvd_of_forall_pow_eq_one ?_)
  intro g
  rw [pow_one]
  exact Subtype.ext (h g g.2)

theorem conjClass_conj' (K : Subgroup (Equiv.Perm (Fin n))) {c : Equiv.Perm (Fin n)}
    (hc : c ∈ K) (r : Equiv.Perm (Fin n)) : conjClass K (c * r * c⁻¹) = conjClass K r := by
  ext v
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c, K.mul_mem hd hc, by group⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c⁻¹, K.mul_mem hd (K.inv_mem hc), by group⟩

theorem conj_classes {G T : Subgroup (Equiv.Perm (Fin n))} {zs : List (Equiv.Perm (Fin n))}
    (hZ : ∀ g ∈ G, ∀ z ∈ zs, g * z = z * g) (hTG : T ≤ G)
    (hconj : ∀ Q : Subgroup (Equiv.Perm (Fin n)), Q ≤ G → IsPGroup 2 Q →
      ∃ g ∈ G, ∀ q ∈ Q, g * q * g⁻¹ ∈ T)
    {tReps : List (Equiv.Perm (Fin n))}
    (hcov : ∀ u ∈ T, orderOf u = 2 → ∃ r ∈ tReps, ∃ c ∈ T, u = c * r * c⁻¹)
    {xs : List (Equiv.Perm (Fin n))}
    (hfus : ∀ r ∈ tReps, r ∈ zs ∨ ∃ x ∈ xs, ∃ g ∈ G, g * r * g⁻¹ = x)
    {y : Equiv.Perm (Fin n)} (hy : y ∈ G) (ho : orderOf y = 2) (hyz : y ∉ zs) :
    ∃ x ∈ xs, fixNum y = fixNum x ∧ ∃ g ∈ G, g * y * g⁻¹ = x := by
  have hz : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho]; norm_num)
  obtain ⟨g, hg, hgT⟩ := hconj _ ((Subgroup.zpowers_le).2 hy) hz
  have hgy : g * y * g⁻¹ ∈ T := hgT y (Subgroup.mem_zpowers y)
  have hgo : orderOf (g * y * g⁻¹) = 2 := (MulEquiv.orderOf_eq (MulAut.conj g) y).trans ho
  obtain ⟨r, hr, s, hs, hsr⟩ := hcov _ hgy hgo
  have hsG : s ∈ G := hTG hs
  have hfy : fixNum y = fixNum r := by
    rw [← fixNum_conj g y, hsr, fixNum_conj]
  rcases hfus r hr with h | ⟨x, hx, u, hu, hur⟩
  · exfalso
    apply hyz
    have e1 : g * y * g⁻¹ = r := by
      rw [hsr, hZ s hsG r h, mul_inv_cancel_right]
    have e2 : y = g⁻¹ * r * g := by rw [← e1]; group
    rw [e2, mul_assoc, ← hZ g hg r h, ← mul_assoc, inv_mul_cancel, one_mul]
    exact h
  · refine ⟨x, hx, by rw [hfy, ← fixNum_conj u r, hur], u * s⁻¹ * g,
      G.mul_mem (G.mul_mem hu (G.inv_mem hsG)) hg, ?_⟩
    rw [← hur]
    have : r = s⁻¹ * (g * y * g⁻¹) * s := by rw [hsr]; group
    rw [this]
    group

theorem card_le_of_commute {G T : Subgroup (Equiv.Perm (Fin n))} [Finite T]
    {zs : List (Equiv.Perm (Fin n))} (hZ : ∀ g ∈ G, ∀ z ∈ zs, g * z = z * g) (hTG : T ≤ G)
    (hconj : ∀ Q : Subgroup (Equiv.Perm (Fin n)), Q ≤ G → IsPGroup 2 Q →
      ∃ g ∈ G, ∀ q ∈ Q, g * q * g⁻¹ ∈ T)
    {tReps : List (Equiv.Perm (Fin n))}
    (hcov : ∀ u ∈ T, orderOf u = 2 → ∃ r ∈ tReps, ∃ c ∈ T, u = c * r * c⁻¹)
    {x : Equiv.Perm (Fin n)} (hx : x ∈ G) (hxo : orderOf x = 2) (hxz : x ∉ zs)
    {R : Subgroup (Equiv.Perm (Fin n))} (hRG : R ≤ G) (hRx : ∀ r ∈ R, r * x = x * r)
    (hR : IsPGroup 2 R) {m : ℕ}
    (hm : ∀ r ∈ tReps, fixNum r = fixNum x → r ∉ zs → m ≤ (conjClass T r).ncard) :
    Nat.card R * m ≤ Nat.card T := by
  have hz : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo]; norm_num)
  have hcomm : ∀ r ∈ R, ∀ k : ℤ, r * x ^ k * r⁻¹ = x ^ k := fun r hr k => by
    have hc : Commute r x := hRx r hr
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  have hnorm : R ≤ Subgroup.normalizer (Subgroup.zpowers x : Set (Equiv.Perm (Fin n))) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact Subgroup.mem_zpowers_iff.2 ⟨k, (hcomm r hr k).symm⟩
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      calc x ^ k = r⁻¹ * (r * x ^ k * r⁻¹) * r := by group
        _ = r⁻¹ * x ^ k * r := by rw [hcomm r hr k]
        _ = r⁻¹ * (r * y * r⁻¹) * r := by rw [hk]
        _ = y := by group
  have hQ := IsPGroup.to_sup_of_normal_right' hR hz hnorm
  have hQG : R ⊔ Subgroup.zpowers x ≤ G := sup_le hRG ((Subgroup.zpowers_le).2 hx)
  obtain ⟨g, hg, hgQ⟩ := hconj _ hQG hQ
  set y := g * x * g⁻¹ with hy
  have hyT : y ∈ T := hgQ x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hyo : orderOf y = 2 := (MulEquiv.orderOf_eq (MulAut.conj g) x).trans hxo
  obtain ⟨r, hr, c, hc, hyr⟩ := hcov y hyT hyo
  have hcG : c ∈ G := hTG hc
  have hrz : r ∉ zs := by
    intro h
    apply hxz
    have e1 : y = r := by rw [hyr, hZ c hcG r h, mul_inv_cancel_right]
    have e2 : x = g⁻¹ * r * g := by rw [← e1, hy]; group
    rw [e2, mul_assoc, ← hZ g hg r h, ← mul_assoc, inv_mul_cancel, one_mul]
    exact h
  have hfr : fixNum r = fixNum x := by
    rw [← fixNum_conj c r, ← hyr, hy, fixNum_conj]
  have hmr := hm r hr hfr hrz
  have hcls : conjClass T y = conjClass T r := by
    rw [hyr]
    exact conjClass_conj' T hc r
  have hcard := ncard_conjClass_mul_card T y
  rw [hcls] at hcard
  have hle : Nat.card R ≤ Nat.card (centralizerIn T y) := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizerIn]
    refine ⟨hgQ q (Subgroup.mem_sup_left hq), ?_⟩
    change g * q * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * q * g⁻¹)
    have := hRx q hq
    calc g * q * g⁻¹ * (g * x * g⁻¹) = g * (q * x) * g⁻¹ := by group
      _ = g * (x * q) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * (g * q * g⁻¹) := by group
  calc Nat.card R * m ≤ Nat.card (centralizerIn T y) * (conjClass T r).ncard :=
        Nat.mul_le_mul hle hmr
    _ = Nat.card T := by rw [mul_comm]; exact hcard

theorem false_of_pair {G : Subgroup (Equiv.Perm (Fin n))} {zs : List (Equiv.Perm (Fin n))}
    (hZ : ∀ g ∈ G, ∀ z ∈ zs, g * z = z * g) {al : List (Equiv.Perm (Fin n))}
    {okW : List ℤ → Bool} (hal : ∀ w, okW w = true → evalCodes al w ∈ G)
    {x : Equiv.Perm (Fin n)} {S : Subgroup (Equiv.Perm (Fin n))}
    {reps : List (Equiv.Perm (Fin n))} {forbid : List ℕ}
    (hS : S ≤ G ⊓ Subgroup.centralizer {x}) (hS2 : IsPGroup 2 S)
    (hmax : ∀ R : Subgroup (Equiv.Perm (Fin n)), R ≤ G ⊓ Subgroup.centralizer {x} →
      IsPGroup 2 R → Nat.card R ≤ Nat.card S)
    (hcov : ∀ u ∈ S, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ S, u = c * r * c⁻¹)
    (hder : ∀ r ∈ reps, r ≠ x → ∃ st, derivCheck al okW zs forbid [x, r] st = true)
    {X : Subgroup (Equiv.Perm (Fin n))} (hX : Hyp212In G {z | z ∈ zs} X) (hx : x ∈ X)
    (hf : ∀ y ∈ X, y ≠ 1 → fixNum y ∉ forbid) : False := by
  have hZc : ∀ g ∈ G, ∀ z ∈ {z | z ∈ zs}, g * z * g⁻¹ = z := fun g hg z hz => by
    rw [hZ g hg z hz, mul_inv_cancel_right]
  have hXC : X ≤ G ⊓ Subgroup.centralizer {x} := fun y hy =>
    ⟨hX.le hy, Subgroup.mem_centralizer_singleton_iff.2 (hX.mul_comm hy hx)⟩
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_card_le' hS hS2 hmax hXC (isPGroup_of_sq hX.sq_eq_one)
  have hcx : c * x * c⁻¹ = x := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hcC.2, mul_inv_cancel_right]
  have hX₂ := hX.conj hcC.1 (hZc c hcC.1)
  have hx₂ : x ∈ X.map (MulAut.conj c).toMonoidHom := ⟨x, hx, hcx⟩
  have hX₂S : X.map (MulAut.conj c).toMonoidHom ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  have hf₂ : ∀ y ∈ X.map (MulAut.conj c).toMonoidHom, y ≠ 1 → fixNum y ∉ forbid := by
    rintro _ ⟨y, hy, rfl⟩ hy1
    change fixNum (c * y * c⁻¹) ∉ forbid
    rw [fixNum_conj]
    exact hf y hy fun h => hy1 (by rw [h, map_one])
  obtain ⟨y, hy, hy1, hyx⟩ : ∃ y ∈ X.map (MulAut.conj c).toMonoidHom, y ≠ 1 ∧ y ≠ x := by
    by_contra hcon
    push Not at hcon
    have hsub : ((X.map (MulAut.conj c).toMonoidHom : Subgroup (Equiv.Perm (Fin n))) :
        Set (Equiv.Perm (Fin n))) ⊆ {1, x} := fun y hy => by
      by_cases h1 : y = 1
      · exact Or.inl h1
      · exact Or.inr (hcon y hy h1)
    have h4 := hX₂.four_le
    have h2 : ({1, x} : Set (Equiv.Perm (Fin n))).ncard ≤ 2 := by
      calc ({1, x} : Set (Equiv.Perm (Fin n))).ncard
          ≤ ({x} : Set (Equiv.Perm (Fin n))).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq] at h3
    change Nat.card (X.map (MulAut.conj c).toMonoidHom) ≤ _ at h3
    omega
  have hyo : orderOf y = 2 := orderOf_eq_prime (hX₂.sq_eq_one y hy) hy1
  obtain ⟨r, hr, s, hs, hysr⟩ := hcov y (hX₂S hy) hyo
  have hsG : s ∈ G := (hS hs).1
  have hsx : s⁻¹ * x * s⁻¹⁻¹ = x := by
    have e := Subgroup.mem_centralizer_singleton_iff.1 (hS hs).2
    calc s⁻¹ * x * s⁻¹⁻¹ = s⁻¹ * (x * s) := by group
      _ = s⁻¹ * (s * x) := by rw [e]
      _ = x := by group
  have hsx' : s * x * s⁻¹ = x := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 (hS hs).2, mul_inv_cancel_right]
  have hX₃ := hX₂.conj (G.inv_mem hsG) (hZc _ (G.inv_mem hsG))
  have hx₃ : x ∈ (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom :=
    ⟨x, hx₂, hsx⟩
  have hr₃ : r ∈ (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom := by
    refine ⟨y, hy, ?_⟩
    change s⁻¹ * y * s⁻¹⁻¹ = r
    rw [hysr]
    group
  have hf₃ : ∀ z ∈ (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom,
      z ≠ 1 → fixNum z ∉ forbid := by
    rintro _ ⟨z, hz, rfl⟩ hz1
    change fixNum (s⁻¹ * z * s⁻¹⁻¹) ∉ forbid
    rw [fixNum_conj]
    exact hf₂ z hz fun h => hz1 (by rw [h, map_one])
  have hrx : r ≠ x := fun h => hyx (by rw [hysr, h, hsx'])
  obtain ⟨st, hst⟩ := hder r hr hrx
  have hfalse := derivCheck_eq_false hal hX₃ hf₃ st [x, r] (by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hx₃
    · exact hr₃)
  rw [hst] at hfalse
  exact Bool.noConfusion hfalse

theorem not_hyp212In_of_classes {G : Subgroup (Equiv.Perm (Fin n))}
    {zs : List (Equiv.Perm (Fin n))} (hZ : ∀ g ∈ G, ∀ z ∈ zs, g * z = z * g)
    {xs : List (Equiv.Perm (Fin n))} (hnd : (xs.map fixNum).Nodup)
    (hcl : ∀ y ∈ G, orderOf y = 2 → y ∉ zs →
      ∃ x ∈ xs, fixNum y = fixNum x ∧ ∃ g ∈ G, g * y * g⁻¹ = x)
    (hk : ∀ k < xs.length, ∀ X : Subgroup (Equiv.Perm (Fin n)), Hyp212In G {z | z ∈ zs} X →
      xs.getD k 1 ∈ X → (∀ y ∈ X, y ≠ 1 → fixNum y ∉ (xs.take k).map fixNum) → False)
    (X : Subgroup (Equiv.Perm (Fin n))) : ¬ Hyp212In G {z | z ∈ zs} X := by
  intro hX
  have hZc : ∀ g ∈ G, ∀ z ∈ {z | z ∈ zs}, g * z * g⁻¹ = z := fun g hg z hz => by
    rw [hZ g hg z hz, mul_inv_cancel_right]
  have hmeet : ∃ k, k < xs.length ∧ ∃ y ∈ X, y ≠ 1 ∧ fixNum y = fixNum (xs.getD k 1) := by
    have hne : X ≠ ⊥ := by
      intro h
      have h4 := hX.four_le
      rw [h, Subgroup.card_bot] at h4
      omega
    obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨x, hx, hfx, -⟩ := hcl y (hX.le hy) (orderOf_eq_prime (hX.sq_eq_one y hy) hy1')
      (fun h => hX.not_mem y h hy)
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact ⟨k, hk, y, hy, hy1', by rw [List.getD_eq_getElem _ _ hk]; exact hfx⟩
  classical
  let k := Nat.find hmeet
  obtain ⟨hklt, y, hy, hy1, hfy⟩ := Nat.find_spec hmeet
  have hmin : ∀ j < k, ¬ (j < xs.length ∧ ∃ y ∈ X, y ≠ 1 ∧
      fixNum y = fixNum (xs.getD j 1)) := fun j hj => Nat.find_min hmeet hj
  obtain ⟨x, hx, hfx, g, hg, hgy⟩ := hcl y (hX.le hy) (orderOf_eq_prime (hX.sq_eq_one y hy) hy1)
    (fun h => hX.not_mem y h hy)
  have hxk : x = xs.getD k 1 := by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj' : xs.getD j 1 = xs[j] := List.getD_eq_getElem _ _ hj
    have hfj : fixNum xs[j] = fixNum (xs.getD k 1) := by rw [← hfx, hfy]
    have hkk : xs.getD k 1 = xs[k] := List.getD_eq_getElem _ _ hklt
    rw [hkk] at hfj ⊢
    have h1 : (xs.map fixNum)[j]'(by rw [List.length_map]; exact hj) =
        (xs.map fixNum)[k]'(by rw [List.length_map]; exact hklt) := by
      simp [hfj]
    have := (List.Nodup.getElem_inj_iff hnd).1 h1
    simp [this]
  refine hk k hklt _ (hX.conj hg (hZc g hg)) ⟨y, hy, by rw [← hxk]; exact hgy⟩ ?_
  rintro _ ⟨z, hz, rfl⟩ hz1
  have hz1' : z ≠ 1 := fun h => hz1 (by rw [h, map_one])
  change fixNum (g * z * g⁻¹) ∉ _
  rw [fixNum_conj]
  intro hmem
  obtain ⟨f, hf, hfz⟩ := List.mem_map.1 hmem
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
  have hjk : j < k := by
    have := hj
    simp only [List.length_take] at this
    omega
  have hjl : j < xs.length := by
    have := hj
    simp only [List.length_take] at this
    omega
  apply hmin j hjk
  refine ⟨hjl, z, hz, hz1', ?_⟩
  rw [← hfz, List.getElem_take, List.getD_eq_getElem _ _ hjl]

end CFSG.ComponentClassification.RankTwoClassical.ExcO8

module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Rho
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Omega
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzCert
public import CFSG.Sporadic.SuzOddCore.InvCentralizers
public import CFSG.Sporadic.SuzOddCore.SylowFusion
public import CFSG.Sporadic.SuzOddCore.InvGraphCheck
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.SuzB0

open Subgroup CFSG.Open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore
open scoped commutatorElement

@[expose] noncomputable def qGen (i : ℕ) : Equiv.Perm (Fin 1782) := permC 1782 (qArr i)

@[expose] noncomputable def qVec (v : ℕ) : Equiv.Perm (Fin 1782) :=
  (List.range 6).foldl (fun r i => if v.testBit i then r * qGen i else r) 1

@[expose] noncomputable def bitEquiv : Fin 64 ≃ (Fin 6 → ZMod 2) :=
  Equiv.ofBijective (fun v => bitVec v) ⟨fun v w h => Fin.ext (bitVec_inj v v.2 w w.2 h),
    fun u => by
      obtain ⟨v, hv, hvu⟩ := exists_bitVec u
      exact ⟨⟨v, hv⟩, hvu⟩⟩

@[expose] noncomputable def kappa :
    ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) →* Equiv.Perm (Fin 64) where
  toFun g := (bitEquiv.trans g.toEquiv).trans bitEquiv.symm
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

theorem kappa_apply (g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) (x : Fin 64) :
    kappa g x = bitEquiv.symm (g (bitVec x)) :=
  rfl

theorem kappa_injective : Function.Injective kappa := by
  intro g h hgh
  refine LinearEquiv.ext fun u => ?_
  obtain ⟨x, rfl⟩ := bitEquiv.surjective u
  have := congrArg (fun σ : Equiv.Perm (Fin 64) => bitEquiv (σ x)) hgh
  simp only [kappa_apply, Equiv.apply_symm_apply] at this
  exact this

theorem bitEquiv_symm_bitVec {m : ℕ} (hm : m < 64) : (bitEquiv.symm (bitVec m) : ℕ) = m := by
  rw [show bitVec m = bitEquiv ⟨m, hm⟩ from rfl, Equiv.symm_apply_apply]

theorem b0_parts :
    (∀ i < 6, permOK 1782 (qArr i) = true ∧ inM (qArr i) = true ∧
      commutesA (qArr i) tTab = true) ∧
    (∀ v < 64, ∀ w < 64, eqA 1782 (compA 1782 qProds[v]! qProds[w]!)
      (compA 1782 qProds[v ^^^ w]! (tPow (gammaBit v w))) = true) ∧
    (∀ j < 128, ∀ j' < 128, (j == j' || !(eqA 1782 qElts[j]! qElts[j']!)) = true) ∧
    (∀ k < 10, permOK 1782 (cTab k) = true ∧ ∀ i < 6,
      eqA 1782 (compA 1782 (compA 1782 (cTab k) (qArr i)) (invCand 1782 (cTab k)))
        (compA 1782 qProds[(act k i).1]! (tPow (act k i).2)) = true) ∧
    enumOK 64 matTabs matEnum = true ∧ matEnum.tabs.size = 25920 ∧ noTS3 = true := by
  have h := b0Suz_check
  rw [b0SuzCheck] at h
  simp only [Bool.and_eq_true, allBelow_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨fun i hi => ⟨(h4 i hi).1.1, (h4 i hi).1.2, (h4 i hi).2⟩, h5, h6, h7, h8, h9, h10⟩

theorem act_lt : ∀ k < 10, ∀ i < 6, (act k i).1 < 64 ∧ (act k i).2 < 2 := by
  decide

theorem colFold_act_lt : ∀ k < 10, ∀ v < 64, colFold (fun i => (act k i).1) v < 64 := by
  decide

theorem getElem!_ofFn' {α : Type} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem rep_tTab :
    Rep 1782 tTab (suzInv 1) := by
  have h := rep_suzInv (i := 1) (by norm_num)
  rwa [invGraph_check.2.2.2.1 1 (by norm_num)] at h

theorem rep_permOK {a : Array ℕ} (h : permOK 1782 a = true) : Rep 1782 a (permC 1782 a) :=
  (tabRep_of_permOK h).2

theorem rep_invCand {a : Array ℕ} {g : Equiv.Perm (Fin 1782)} (ha : Rep 1782 a g)
    (h : permOK 1782 a = true) : Rep 1782 (invCand 1782 a) g⁻¹ := by
  simp only [permOK, Bool.and_eq_true] at h
  exact rep_inv_of_isInvA ha h.2

theorem rep_qArr {i : ℕ} (hi : i < 6) :
    Rep 1782 (qArr i) (qGen i) :=
  rep_permOK (b0_parts.1 i hi).1

theorem rep_idTab : Rep 1782 (idTab 1782) 1 := TabRep.idTab.2

theorem rep_qProd_foldl (v : ℕ) : ∀ l : List ℕ, (∀ i ∈ l, i < 6) →
    ∀ (a : Array ℕ) (g : Equiv.Perm (Fin 1782)), Rep 1782 a g →
      Rep 1782 (l.foldl (fun r i => if v.testBit i then compA 1782 r (qArr i) else r) a)
        (l.foldl (fun r i => if v.testBit i then r * qGen i else r) g)
  | [], _, _, _, h => h
  | i :: l, hl, a, g, h => by
    simp only [List.foldl_cons]
    refine rep_qProd_foldl v l (fun j hj => hl j (List.mem_cons_of_mem i hj)) _ _ ?_
    split_ifs
    · exact rep_compA h (rep_qArr (hl i List.mem_cons_self))
    · exact h

theorem rep_qProd (v : ℕ) : Rep 1782 (qProd v) (qVec v) :=
  rep_qProd_foldl v _ (fun _ hi => List.mem_range.mp hi) _ _ rep_idTab

theorem qProds_get {v : ℕ} (hv : v < 64) : qProds[v]! = qProd v := by
  unfold qProds
  exact getElem!_ofFn' _ hv

theorem rep_qProds {v : ℕ} (hv : v < 64) :
    Rep 1782 qProds[v]! (qVec v) := by
  rw [qProds_get hv]
  exact rep_qProd v

theorem rep_tPow {b : ℕ}
    (hb : b < 2) : Rep 1782 (tPow b) (suzInv 1 ^ b) := by
  interval_cases b
  · rw [pow_zero, show tPow 0 = idTab 1782 by simp [tPow]]
    exact rep_idTab
  · rw [pow_one, show tPow 1 = tTab by simp [tPow]]
    exact rep_tTab

theorem qElts_get {j : ℕ} (hj : j < 128) :
    qElts[j]! = compA 1782 qProds[j / 2]! (tPow (j % 2)) := by
  unfold qElts
  exact getElem!_ofFn' _ hj

theorem qGen_comm
    {i : ℕ} (hi : i < 6) :
    qGen i * suzInv 1 = suzInv 1 * qGen i :=
  (commutesA_iff (rep_qArr hi) rep_tTab).mp (b0_parts.1 i hi).2.2

theorem qVec_comm_foldl
    (v : ℕ) : ∀ l : List ℕ, (∀ i ∈ l, i < 6) →
    ∀ g : Equiv.Perm (Fin 1782), Commute g (suzInv 1) →
      Commute (l.foldl (fun r i => if v.testBit i then r * qGen i else r) g) (suzInv 1)
  | [], _, _, h => h
  | i :: l, hl, g, h => by
    simp only [List.foldl_cons]
    refine qVec_comm_foldl v l (fun j hj => hl j (List.mem_cons_of_mem i hj)) _ ?_
    split_ifs
    · exact h.mul_left (qGen_comm (hl i List.mem_cons_self))
    · exact h

theorem coord_qVec :
    Coord (suzInv 1) qVec where
  t_sq := suzInv_sq (by norm_num)
  t_ne := suzInv_ne_one (by norm_num)
  comm v _ := (qVec_comm_foldl v _ (fun _ hi => List.mem_range.mp hi) 1 (Commute.one_left _)).eq
  mul v hv w hw := eq_of_eqA (rep_compA (rep_qProds hv) (rep_qProds hw))
    (rep_compA (rep_qProds (xor_lt hv hw)) (rep_tPow (gammaBit_lt v w))) (b0_parts.2.1 v hv w hw)
  inj v hv w hw a ha b hb h := by
    have hj : 2 * v + a < 128 := by omega
    have hj' : 2 * w + b < 128 := by omega
    have h6 := b0_parts.2.2.1 _ hj _ hj'
    have e1 : (2 * v + a) / 2 = v := by omega
    have e2 : (2 * v + a) % 2 = a := by omega
    have e3 : (2 * w + b) / 2 = w := by omega
    have e4 : (2 * w + b) % 2 = b := by omega
    have r1 : Rep 1782 qElts[2 * v + a]! (qVec v * suzInv 1 ^ a) := by
      rw [qElts_get hj, e1, e2]
      exact rep_compA (rep_qProds hv) (rep_tPow ha)
    have r2 : Rep 1782 qElts[2 * w + b]! (qVec w * suzInv 1 ^ b) := by
      rw [qElts_get hj', e3, e4]
      exact rep_compA (rep_qProds hw) (rep_tPow hb)
    have heq := (eqA_iff r1 r2).mpr h
    simp only [Bool.or_eq_true, beq_iff_eq, heq, Bool.not_true, Bool.false_eq_true,
      or_false] at h6
    omega

theorem invInnerGenArrs_one_size : (invInnerGenArrs 1).size = 10 := by
  simp [invInnerGenArrs, invInnerGenCounts]

theorem qGen_mem_invE
    {i : ℕ} (hi : i < 6) : qGen i ∈ invE 1 := by
  rw [invE_eq_centM (by norm_num)]
  exact ⟨mem_centralizer_singleton_iff.mpr (qGen_comm hi),
    (inM_iff (rep_qArr hi)).mp (b0_parts.1 i hi).2.1⟩

theorem qVec_mem_invE
    (v : ℕ) : qVec v ∈ invE 1 := by
  have key : ∀ l : List ℕ, (∀ i ∈ l, i < 6) → ∀ g ∈ invE 1,
      l.foldl (fun r i => if v.testBit i then r * qGen i else r) g ∈ invE 1 := by
    intro l
    induction l with
    | nil => exact fun _ g hg => hg
    | cons i l ih =>
      intro hl g hg
      simp only [List.foldl_cons]
      refine ih (fun j hj => hl j (List.mem_cons_of_mem i hj)) _ ?_
      split_ifs
      · exact mul_mem hg (qGen_mem_invE (hl i List.mem_cons_self))
      · exact hg
  exact key _ (fun _ hi => List.mem_range.mp hi) 1 (one_mem _)

theorem suzInv_mem_invE
    : suzInv 1 ∈ invE 1 := by
  have h := coord_qVec.mul_self_eq (v := 16) (by norm_num) 0
  rw [show qMinusBit 16 = 1 by decide, pow_one, pow_zero, mul_one] at h
  rw [← h]
  exact mul_mem (qVec_mem_invE 16) (qVec_mem_invE 16)

theorem Q_le_invE
    : coord_qVec.Q ≤ invE 1 := by
  intro g hg
  obtain ⟨v, -, a, -, rfl⟩ := coord_qVec.mem_Q_iff.mp hg
  exact mul_mem (qVec_mem_invE v) (pow_mem suzInv_mem_invE a)

theorem qVec_two_pow {i : ℕ} (hi : i < 6) : qVec (2 ^ i) = qGen i := by
  simp only [qVec, Nat.testBit_two_pow]
  interval_cases i <;> simp [List.range_succ]

theorem gen_rep {g : Equiv.Perm (Fin 1782)}
    (hg : g ∈ (invInnerChain 1).original.toList) : ∃ k < 10, Rep 1782 (cTab k) g := by
  obtain ⟨k, rfl⟩ := (schreier_vector_mem_toList_iff_get _ g).1 hg
  refine ⟨k, ?_, (invInnerChain_arrays (by norm_num)).orig k⟩
  have := k.2
  change (k : ℕ) < (invInnerGenArrs 1).size at this
  rwa [invInnerGenArrs_one_size] at this

theorem rep_gen {k : ℕ} (hk : k < 10) :
    ∃ g ∈ (invInnerChain 1).original.toList, Rep 1782 (cTab k) g := by
  have hk' : k < (invInnerChain 1).originalCount := by
    change k < (invInnerGenArrs 1).size
    rw [invInnerGenArrs_one_size]
    exact hk
  exact ⟨_, schreier_vector_get_mem_toList _ ⟨k, hk'⟩,
    (invInnerChain_arrays (by norm_num)).orig ⟨k, hk'⟩⟩

theorem gen_conj
    {k : ℕ} (hk : k < 10) {g : Equiv.Perm (Fin 1782)}
    (hg : Rep 1782 (cTab k) g) {i : ℕ} (hi : i < 6) :
    g * qVec (2 ^ i) * g⁻¹ = qVec (act k i).1 * suzInv 1 ^ (act k i).2 := by
  rw [qVec_two_pow hi]
  have h7 := b0_parts.2.2.2.1 k hk
  exact eq_of_eqA (rep_compA (rep_compA hg (rep_qArr hi)) (rep_invCand hg h7.1))
    (rep_compA (rep_qProds (act_lt k hk i hi).1) (rep_tPow (act_lt k hk i hi).2)) (h7.2 i hi)

theorem invE_le
    : invE 1 ≤ normalizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782))) ⊓
      centralizer ({suzInv 1} : Set (Equiv.Perm (Fin 1782))) := by
  rw [invE, RawSchreierDatum.originalSubgroup, closure_le]
  intro g hg
  obtain ⟨k, hk, hrep⟩ := gen_rep hg
  have hgE : g ∈ invE 1 := subset_closure hg
  have hct : g * suzInv 1 = suzInv 1 * g :=
    mem_centralizer_singleton_iff.mp (invE_le_centM (by norm_num) hgE).1
  refine ⟨coord_qVec.mem_normalizer hct fun i hi => ?_, mem_centralizer_singleton_iff.mpr hct⟩
  rw [gen_conj hk hrep hi]
  exact coord_qVec.mem_Q_iff.mpr ⟨_, (act_lt k hk i hi).1, _, (act_lt k hk i hi).2, rfl⟩

@[expose] noncomputable def rho1
    : ↥(invE 1) →* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :=
  coord_qVec.rho invE_le

theorem matTab_get {k v : ℕ} (hv : v < 64) :
    (matTab k)[v]! = colFold (fun i => (act k i).1) v := by
  unfold matTab
  exact getElem!_ofFn' _ hv

theorem matTabs_get {k : ℕ} (hk : k < 10) : matTabs[k]! = matTab k := by
  unfold matTabs
  exact getElem!_ofFn' _ hk

theorem matTab_size (k : ℕ) : (matTab k).size = 64 := by
  unfold matTab
  exact Array.size_ofFn

theorem matTabs_size : matTabs.size = 10 := by
  unfold matTabs
  exact Array.size_ofFn

theorem tabRep_gen
    {k : ℕ} (hk : k < 10) (c : ↥(invE 1)) (hc : Rep 1782 (cTab k) (c : Equiv.Perm (Fin 1782))) :
    TabRep matTabs[k]! (kappa (rho1 c)) := by
  refine ⟨by rw [matTabs_get hk, matTab_size], fun x => ?_⟩
  rw [matTabs_get hk, matTab_get x.2, kappa_apply]
  change _ = ((bitEquiv.symm (coord_qVec.rho invE_le c (bitVec x)) : Fin 64) : ℕ)
  rw [coord_qVec.rho_bitVec invE_le c (w := fun i => (act k i).1) (b := fun i => (act k i).2)
    (fun i hi => (act_lt k hk i hi).1) (fun i hi => (act_lt k hk i hi).2)
    (fun i hi => gen_conj hk hc hi) x.2, bitEquiv_symm_bitVec (colFold_act_lt k hk x x.2)]

theorem kappa_rho1_enumerates
    : Enumerates (rho1.range.map kappa) matEnum.tabs.toList := by
  set S₀ : Set (Equiv.Perm (Fin 1782)) := {g | g ∈ (invInnerChain 1).original.toList} with hS₀
  have htop : closure (((↑) : ↥(invE 1) → Equiv.Perm (Fin 1782)) ⁻¹' S₀) = ⊤ :=
    closure_closure_coe_preimage
  have hrange : rho1.range.map kappa = closure ((kappa.comp rho1) '' ((↑) ⁻¹' S₀)) := by
    rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_map, MonoidHom.map_closure]
  rw [hrange]
  refine enumerates_closure ?_ ?_ b0_parts.2.2.2.2.1
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨k, hk, hrep⟩ := gen_rep hc
    exact ⟨k, by rw [matTabs_size]; exact hk, tabRep_gen hk c hrep⟩
  · intro j hj
    have hj10 : j < 10 := by rwa [matTabs_size] at hj
    obtain ⟨g, hg, hrep⟩ := rep_gen hj10
    exact ⟨kappa (rho1 ⟨g, subset_closure hg⟩), ⟨⟨g, subset_closure hg⟩, hg, rfl⟩,
      tabRep_gen hj10 _ hrep⟩

theorem card_range_rho1
    : Nat.card rho1.range = 25920 := by
  rw [← card_map_of_injective kappa_injective, kappa_rho1_enumerates.card, Array.length_toList,
    b0_parts.2.2.2.2.2.1]

theorem range_rho1
    : rho1.range = timmesfeldOmega qMinus := by
  obtain ⟨hcardΩ, hidx, -, -⟩ := omega_facts b0_parts.2.2.2.2.2.2
  set O := TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm with hOdef
  have hle : rho1.range ≤ O := by
    rintro _ ⟨c, rfl⟩
    exact coord_qVec.rho_mem_orthogonalGroup invE_le c
  have hΩO : timmesfeldOmega qMinus ≤ O := by
    rw [Sec2Omega.timmesfeldOmega_qMinus, commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact O.mul_mem (O.mul_mem (O.mul_mem ha hb) (O.inv_mem ha)) (O.inv_mem hb)
  have hO : Nat.card O = 51840 := by
    have h := ((timmesfeldOmega qMinus).subgroupOf O).card_mul_index
    rw [hidx, Nat.card_congr (subgroupOfEquivOfLe hΩO).toEquiv, hcardΩ] at h
    omega
  have hidx' : (rho1.range.subgroupOf O).index = 2 := by
    have h := (rho1.range.subgroupOf O).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, card_range_rho1, hO] at h
    omega
  have key : ∀ x y : ↥O, ⁅x, y⁆ ∈ rho1.range.subgroupOf O := by
    intro x y
    have e : ⁅x, y⁆ = (x * y) * (x⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e, mul_mem_iff_of_index_two hidx', mul_mem_iff_of_index_two hidx',
      mul_mem_iff_of_index_two hidx', inv_mem_iff, inv_mem_iff]
  have hcomm : ⁅O, O⁆ ≤ rho1.range := by
    rw [commutator_le]
    intro a ha b hb
    exact mem_subgroupOf.mp (key ⟨a, ha⟩ ⟨b, hb⟩)
  have : Finite rho1.range := Finite.of_surjective _ rho1.rangeRestrict_surjective
  rw [Sec2Omega.timmesfeldOmega_qMinus]
  refine (eq_of_le_of_card_ge hcomm ?_).symm
  rw [card_range_rho1, ← Sec2Omega.timmesfeldOmega_qMinus, hcardΩ]

theorem ker_rho1
    : rho1.ker = coord_qVec.Q.subgroupOf (invE 1) := by
  refine (eq_of_le_of_card_ge (show coord_qVec.Q.subgroupOf (invE 1) ≤ rho1.ker from
    coord_qVec.le_ker_rho invE_le) ?_).symm
  have h1 := Subgroup.card_ker_mul_card_range rho1
  have h3 : Nat.card ↥(invE 1) = 3317760 := by
    rw [card_invE (by norm_num)]
    rfl
  rw [card_range_rho1, h3] at h1
  have h2 : Nat.card (coord_qVec.Q.subgroupOf (invE 1)) = 128 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe Q_le_invE).toEquiv, coord_qVec.card_Q]
  rw [h2]
  omega

theorem invE_one_perfect
    : commutator ↥(invE 1) = ⊤ := by
  have hts := b0_parts.2.2.2.2.2.2
  refine coord_qVec.commutator_eq_top invE_le Q_le_invE range_rho1 ker_rho1 (omega_commutator hts)
    fun h => ?_
  have hc := (omega_facts hts).1
  rw [h, card_bot] at hc
  norm_num at hc

theorem suzB0_model
    : ∃ (Q₁ : Subgroup (Equiv.Perm (Fin 1782)))
      (ρ : ↥(invE 1) →* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))),
      IsQ8Cube Q₁ ∧ Q₁ ≤ invE 1 ∧ invE 1 ≤ normalizer (Q₁ : Set (Equiv.Perm (Fin 1782))) ∧
      ρ.range = timmesfeldOmega qMinus ∧ ρ.ker = Q₁.subgroupOf (invE 1) ∧
      commutator ↥(invE 1) = ⊤ :=
  ⟨coord_qVec.Q, rho1, coord_qVec.isQ8Cube b0_parts.2.2.2.2.2.2, Q_le_invE,
    fun _ h => (invE_le h).1, range_rho1, ker_rho1, invE_one_perfect⟩

end CFSG.ComponentClassification.AS81.SuzB0

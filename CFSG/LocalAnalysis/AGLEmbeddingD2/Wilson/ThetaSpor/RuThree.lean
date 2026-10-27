
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.RuThreeBase

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.ConjSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Facts
public import CFSG.Sporadic.Schreier.RuIso
public import Certificates.Certificate12614
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.PreprimitiveSolvableBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.PreprimitiveSolvableSmall
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.Sporadic.RuSchreier CFSG.Certificates.Native CFSG.Certificates

section Stage1

theorem ruThree_parts :
    ruCentOK () = true ∧ ruSylowOK () = true ∧ ruActionOK () = true := by
  have h := Certificates.certificate12614
  simp only [ruThreeOK, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem ruCent_parts :
    validA 4060 ruX = true ∧ siftA 4060 (rawLevels 4060 ruS ruBase) ruBase 0 ruX = true ∧
      eqA 4060 (powArr 4060 ruX 3) (idA 4060) = true ∧ eqA 4060 ruX (idA 4060) = false ∧
      relsOK 4060 ruBase ruX ruRels = true ∧ enumOK 4060 ruGs ruKeys (ruCCert ()) = true ∧
      (ruCCert ()).pts.size = 2160 ∧
      allLt ruGs.size (fun k => commA 4060 ruGs[k]! ruX) = true ∧
      allLt ruGs.size (fun k => siftA 4060 (rawLevels 4060 ruS ruBase) ruBase 0 ruGs[k]!) = true ∧
      ptailOK 4060 (rawLevels 4060 ruS ruBase) ruBase ruX (pow5A 4060 ruX) ruRels
        (ruCCert ()).pts.toList ruBase.size 0 (idA 4060) = true := by
  have h := ruThree_parts.1
  simp only [ruCentOK, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf⟩, hg⟩, hh⟩, hi⟩, hj⟩ := h
  exact ⟨ha, hb, hc, hd, he, hf, hg, hh, hi, hj⟩

theorem rep_ruX : Rep 4060 ruX ruXperm :=
  rep_of_validA ruCent_parts.1

theorem ruXperm_pow_three : ruXperm ^ 3 = 1 :=
  (eqA_iff (rep_powArr rep_ruX 3) rep_idA).1 ruCent_parts.2.2.1

theorem ruXperm_ne_one : ruXperm ≠ 1 := by
  intro h
  have : eqA 4060 ruX (idA 4060) = true := (eqA_iff rep_ruX rep_idA).2 h
  rw [ruCent_parts.2.2.2.1] at this
  exact Bool.false_ne_true this

theorem ruXperm_mem :
    ruXperm ∈ ruP :=
  mem_ruP_of_sift rep_ruX ruCent_parts.2.1

@[expose] noncomputable def ruXp :
    ruP := ⟨ruXperm, ruXperm_mem⟩

theorem closure_ruGs_eq :
    Subgroup.closure (permsA 4060 ruGs) = Subgroup.centralizer {ruXperm} ⊓ ruP := by
  obtain ⟨-, -, -, -, hrels, hC, -, hcomm, hsift, htail⟩ := ruCent_parts
  have hps : ∀ p ∈ ruKeys, p < 4060 := by decide
  rw [← ruChainJoin_sub_ruP]
  have hA := ruChainJoin_arrays
  have hc := ruChainJoin_check.1
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hrep := rep_of_validA (enumOK_gens_valid hC hk)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · exact (commA_iff hrep rep_ruX).1 (allLt_spec hcomm hk)
    · exact (ruChain_sift hc hrep).1 (allLt_spec hsift hk)
  · intro g hg
    have htail' : ptailOK 4060 (rawLevels 4060 ruS ruBase) ruBase ruX (pow5A 4060 ruX) ruRels
        (ruCCert ()).pts.toList ruChainJoin.baseCount 0 (idA 4060) = true := by
      rw [← hA.base_size]
      exact htail
    obtain ⟨e, he, hre⟩ := centralizer_subset_of_ptailOK hA (chainCheckFacts hc)
      (validSchreier_of_chainOK hA (by norm_num) hc).1 rep_ruX (rep_pow5A rep_ruX)
      (relsOK_spec hrels) htail' hg
    exact enumOK_mem_of_mem hps hC hre he

theorem ruCent_enum :
    (∀ x, x ∈ Subgroup.closure (permsA 4060 ruGs) ↔
        ∃ i < (ruCCert ()).pts.size, permOfArr 4060 (ruCCert ()).pts[i]! = x) ∧
      Nat.card (Subgroup.closure (permsA 4060 ruGs)) = 2160 ∧
      ∀ i < (ruCCert ()).pts.size, validA 4060 (ruCCert ()).pts[i]! = true := by
  obtain ⟨-, -, -, -, -, hC, hsize, -⟩ := ruCent_parts
  have hps : ∀ p ∈ ruKeys, p < 4060 := by decide
  obtain ⟨h1, h2, h3⟩ := enumOK_spec hps hC
  exact ⟨h1, h2.trans hsize, h3⟩

end Stage1

section Stage2

theorem ruSylow_parts :
    enumOK 4060 ruSylGs ruKeys (ruSylCert ()) = true ∧ (ruSylCert ()).pts.size = 27 ∧
      allLt ruSylGs.size (fun k => siftA 4060 (rawLevels 4060 ruS ruBase) ruBase 0 ruSylGs[k]!) =
        true ∧
      ∀ k < (ruSylCert ()).pts.size, eqA 4060 (ruSylCert ()).pts[k]! (idA 4060) = true ∨
        ∃ g ∈ ruConjs, validA 4060 g = true ∧
          siftA 4060 (rawLevels 4060 ruS ruBase) ruBase 0 g = true ∧
          eqA 4060 (conjA 4060 g (ruSylCert ()).pts[k]!) ruX = true := by
  have h := ruThree_parts.2.1
  simp only [ruSylowOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨he, hsz⟩, hs⟩, hall⟩ := h
  refine ⟨he, hsz, hs, fun k hk => ?_⟩
  have := allLt_spec hall hk
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at this
  rcases this with h | ⟨x, hx, ⟨h1, h2⟩, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, hx, h1, h2, h3⟩

theorem ruSylGs_valid {k : ℕ} (hk : k < 2) :
    validA 4060 ruSylGs[k]! = true := by
  have := ruSylow_parts.1
  have hps : ∀ p ∈ ruKeys, p < 4060 := by decide
  simp only [enumOK, Bool.and_eq_true] at this
  exact allLt_spec this.1 (by simpa [ruSylGs] using hk)

theorem ruSylGs_mem
    {k : ℕ} (hk : k < 2) :
    permOfArr 4060 ruSylGs[k]! ∈ ruP :=
  mem_ruP_of_sift (rep_of_validA (ruSylGs_valid hk)) (allLt_spec ruSylow_parts.2.2.1
    (by simpa [ruSylGs] using hk))

theorem ruSylowSub_le :
    ruSylowSub ≤ ruP := by
  rw [ruSylowSub, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact ruSylGs_mem (by simpa [ruSylGs] using hk)

theorem card_ruSylowSub : Nat.card ruSylowSub = 27 := by
  obtain ⟨he, hsz, -, -⟩ := ruSylow_parts
  have hps : ∀ p ∈ ruKeys, p < 4060 := by decide
  rw [ruSylowSub, (enumOK_spec hps he).2.1, hsz]

theorem exists_conj_ruXp
    (b : ruP) (hb : b ^ 3 = 1) (hb1 : b ≠ 1) :
    ∃ g : ruP, g * b * g⁻¹ = ruXp := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hQ : Nat.card (ruSylowSub.subgroupOf ruP) = 3 ^ 3 := by
    have e := Nat.card_congr (Subgroup.subgroupOfEquivOfLe ruSylowSub_le).toEquiv
    rw [e, card_ruSylowSub]
    norm_num
  have hfin : Finite ruP := Nat.finite_of_card_ne_zero (by rw [card_ruP]; norm_num)
  obtain ⟨h, hh⟩ := exists_conj_mem_of_orderOf_prime_sylow 3 3 (ruSylowSub.subgroupOf ruP) hQ
    (by rw [card_ruP]; norm_num) hord
  rw [Subgroup.mem_subgroupOf] at hh
  have hq1 : h⁻¹ * b * h ≠ 1 := by
    intro h1
    apply hb1
    have : b = h * (h⁻¹ * b * h) * h⁻¹ := by group
    rw [this, h1]; group
  have hps : ∀ p ∈ ruKeys, p < 4060 := by decide
  obtain ⟨he, hsz, -, hall⟩ := ruSylow_parts
  obtain ⟨i, hi, hiq⟩ := ((enumOK_spec hps he).1 _).1 hh
  have hvalid := (enumOK_spec hps he).2.2 i hi
  have hrep : Rep 4060 (ruSylCert ()).pts[i]! (permOfArr 4060 (ruSylCert ()).pts[i]!) :=
    rep_of_validA hvalid
  rcases hall i hi with hid | ⟨g, hg, hgv, hgs, hgc⟩
  · exfalso
    apply hq1
    apply Subtype.ext
    have := (eqA_iff hrep rep_idA).1 hid
    rw [← hiq] at *
    simpa using this
  · have hgrep := rep_of_validA hgv
    have hc := eq_of_eqA (rep_conjA hgv hrep) rep_ruX hgc
    have hgmem : permOfArr 4060 g ∈ ruP := mem_ruP_of_sift hgrep hgs
    refine ⟨⟨permOfArr 4060 g, hgmem⟩ * h⁻¹, ?_⟩
    apply Subtype.ext
    have e : (⟨permOfArr 4060 g, hgmem⟩ * h⁻¹ * b * (⟨permOfArr 4060 g, hgmem⟩ * h⁻¹)⁻¹ : ruP) =
        ⟨permOfArr 4060 g, hgmem⟩ * (h⁻¹ * b * h) * (⟨permOfArr 4060 g, hgmem⟩)⁻¹ := by group
    rw [e]
    change permOfArr 4060 g * (h⁻¹ * b * h : ruP).1 * (permOfArr 4060 g)⁻¹ = ruXperm
    rw [← hiq, ← hc]

end Stage2

section Stage3

theorem ruAction_parts :
    (∀ i < 4060, ((ruX[i]! == i) == ruF.contains i) = true) ∧
    (∀ k < (ruCCert ()).pts.size, (!(ruF.all fun p => (ruEl k)[p]! == p) ||
        eqA 4060 (powArr 4060 (ruEl k) 3) (idA 4060)) = true) ∧
    (∀ i < 10, (ruF.idxOf ((ruGs[0]!)[ruF[i]!]!) == ruR0[i]!) = true) ∧
    (∀ i < 10, (ruF.idxOf ((ruGs[1]!)[ruF[i]!]!) == ruR1[i]!) = true) ∧
    enumOK 10 #[ruR0, ruR1] [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] (ruTenCert ()) = true ∧
    (ruTenCert ()).pts.size = 720 ∧
    (∀ a < 10, ∀ b < 10, a ≠ b → ∃ k < (ruTenCert ()).pts.size,
      ((ruTenCert ()).pts[k]!)[0]! = a ∧ ((ruTenCert ()).pts[k]!)[1]! = b) := by
  have h := ruThree_parts.2.2
  simp only [ruActionOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨allLt_iff.1 h1, allLt_iff.1 h2, allLt_iff.1 h3, allLt_iff.1 h4, h5, h6,
    fun a ha b hb hab => ?_⟩
  have h7a := allLt_iff.1 (allLt_iff.1 h7 a ha) b hb
  have hne : (a == b) = false := by simpa using hab
  rw [hne, Bool.false_or, beq_iff_eq] at h7a
  by_contra hno
  refine absurd h7a ?_
  rw [Bool.not_eq_false, allLt_iff]
  intro k hk
  by_contra hk'
  apply hno
  refine ⟨k, hk, ?_, ?_⟩ <;>
  · simp only [Bool.not_eq_false, Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq] at hk'
    simp [hk']

end Stage3

section Stage4

theorem ruX_fixed_iff {p : ℕ} (hp : p < 4060) :
    ruCAct ruXperm p = p ↔ p ∈ ruF := by
  have h := ruAction_parts.1 p hp
  rw [← rep_ruCAct rep_ruX hp]
  generalize ruX[p]! = y at h ⊢
  rw [beq_iff_eq] at h
  constructor
  · intro hy
    apply List.contains_iff_mem.1
    rw [← h]
    exact beq_iff_eq.2 hy
  · intro hm
    have := List.contains_iff_mem.2 hm
    rw [← h] at this
    exact beq_iff_eq.1 this

theorem ruCAct_mem_F {σ : Equiv.Perm (Fin 4060)} (hσ : RuComm σ)
    {p : ℕ} (hp : p ∈ ruF) : ruCAct σ p ∈ ruF := by
  have hp' := ruF_lt p hp
  rw [← ruX_fixed_iff (ruCAct_lt σ hp')]
  exact ruCAct_comm_fixed hσ hp' ((ruX_fixed_iff hp').2 hp)

theorem ruActNat_lt {σ : Equiv.Perm (Fin 4060)} (hσ : RuComm σ)
    {k : ℕ} (hk : k < 10) : ruActNat σ k < 10 :=
  ruF_idx_lt (ruCAct_mem_F hσ (ruF_getElem_mem hk))

theorem ruActNat_mul {σ τ : Equiv.Perm (Fin 4060)}
    (hτ : RuComm τ) {k : ℕ} (hk : k < 10) :
    ruActNat (σ * τ) k = ruActNat σ (ruActNat τ k) := by
  have hmem := ruCAct_mem_F hτ (ruF_getElem_mem hk)
  unfold ruActNat
  rw [ruCAct_mul σ τ (ruF_lt _ (ruF_getElem_mem hk)), ruF_getElem_idx _ hmem]

abbrev RuC :
    Type :=
  ↥(Subgroup.centralizer ({ruXp} : Set ruP))

theorem ruComm_of_mem
    {c : ruP}
    (hc : c ∈ Subgroup.centralizer ({ruXp} : Set ruP)) : RuComm c.1 := by
  have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)
  exact this.symm

theorem mem_closure_of_mem_RuC
    {c : ruP}
    (hc : c ∈ Subgroup.centralizer ({ruXp} : Set ruP)) :
    c.1 ∈ Subgroup.closure (permsA 4060 ruGs) := by
  rw [closure_ruGs_eq]
  refine ⟨?_, c.2⟩
  have hc' := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)
  exact Subgroup.mem_centralizer_singleton_iff.2 hc'

theorem mem_RuC_of_mem_closure
    {c : ruP}
    (hc : c.1 ∈ Subgroup.closure (permsA 4060 ruGs)) :
    c ∈ Subgroup.centralizer ({ruXp} : Set ruP) := by
  rw [closure_ruGs_eq] at hc
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.1 hc.1

set_option warn.classDefReducibility false in
@[expose] noncomputable def ruMulAction :
    MulAction RuC (Fin 10) where
  smul c k := ⟨ruActNat c.1.1 k.1, ruActNat_lt (ruComm_of_mem c.2) k.2⟩
  one_smul k := Fin.ext (ruActNat_one k.2)
  mul_smul _ d k := Fin.ext (ruActNat_mul (ruComm_of_mem d.2) k.2)

@[expose] noncomputable def ruPhi :
    RuC →* Equiv.Perm (Fin 10) :=
  @MulAction.toPermHom RuC (Fin 10) _ ruMulAction

theorem ruPhi_apply
    (c : RuC) (k : Fin 10) :
    ((ruPhi c k : Fin 10) : ℕ) = ruActNat c.1.1 k.1 := rfl

end Stage4

section Stage5

theorem ruGs_valid {k : ℕ} (hk : k < 2) : validA 4060 ruGs[k]! = true := by
  obtain ⟨-, -, -, -, -, hC, -⟩ := ruCent_parts
  simp only [enumOK, Bool.and_eq_true] at hC
  exact allLt_spec hC.1 (by simpa [ruGs] using hk)

theorem ruGs_mem_ruP {k : ℕ} (hk : k < 2) : permOfArr 4060 ruGs[k]! ∈ ruP := by
  have h := ruGs_mem_closure hk
  rw [closure_ruGs_eq] at h
  exact h.2

@[expose] noncomputable def gRuC (k : ℕ) (hk : k < 2) : RuC :=
  ⟨⟨permOfArr 4060 ruGs[k]!, ruGs_mem_ruP hk⟩, mem_RuC_of_mem_closure (ruGs_mem_closure hk)⟩

theorem ruTen_spec :
    validA 10 ruR0 = true ∧ validA 10 ruR1 = true ∧
      Nat.card (Subgroup.closure (permsA 10 #[ruR0, ruR1])) = 720 := by
  obtain ⟨-, -, -, -, he, hsz, -⟩ := ruAction_parts
  have hps : ∀ p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List ℕ), p < 10 := by decide
  obtain ⟨-, h2, -⟩ := enumOK_spec hps he
  refine ⟨enumOK_gens_valid he (k := 0) (by simp), enumOK_gens_valid he (k := 1) (by simp), ?_⟩
  rw [h2, hsz]

theorem ruPhi_gRuC_zero : ruPhi (gRuC 0 (by norm_num)) = permOfArr 10 ruR0 := by
  have hrep := rep_of_validA ruTen_spec.1
  apply Equiv.ext
  intro j
  apply Fin.ext
  rw [ruPhi_apply, ← hrep j]
  have hj := j.2
  have h5 := ruAction_parts.2.2.1 j hj
  simp only [beq_iff_eq] at h5
  rw [← h5]
  change ruF.idxOf (ruCAct (permOfArr 4060 ruGs[0]!) ruF[(j : ℕ)]!) =
    ruF.idxOf ((ruGs[0]!)[ruF[(j : ℕ)]!]!)
  rw [← rep_ruCAct (rep_of_validA (ruGs_valid (k := 0) (by norm_num)))
    (ruF_lt _ (ruF_getElem_mem hj))]

theorem ruPhi_gRuC_one : ruPhi (gRuC 1 (by norm_num)) = permOfArr 10 ruR1 := by
  have hrep := rep_of_validA ruTen_spec.2.1
  apply Equiv.ext
  intro j
  apply Fin.ext
  rw [ruPhi_apply, ← hrep j]
  have hj := j.2
  have h5 := ruAction_parts.2.2.2.1 j hj
  simp only [beq_iff_eq] at h5
  rw [← h5]
  change ruF.idxOf (ruCAct (permOfArr 4060 ruGs[1]!) ruF[(j : ℕ)]!) =
    ruF.idxOf ((ruGs[1]!)[ruF[(j : ℕ)]!]!)
  rw [← rep_ruCAct (rep_of_validA (ruGs_valid (k := 1) (by norm_num)))
    (ruF_lt _ (ruF_getElem_mem hj))]

theorem closure_le_range_ruPhi : Subgroup.closure (permsA 10 #[ruR0, ruR1]) ≤ ruPhi.range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk2 : k < 2 := by simpa using hk
  interval_cases k
  · exact ⟨gRuC 0 (by norm_num), ruPhi_gRuC_zero⟩
  · exact ⟨gRuC 1 (by norm_num), ruPhi_gRuC_one⟩

theorem card_range_ruPhi_ge : 720 ≤ Nat.card ruPhi.range := by
  rw [← ruTen_spec.2.2]
  exact Subgroup.card_le_of_le closure_le_range_ruPhi

theorem ruTen_two (a b : Fin 10) (hab : a ≠ b) :
    ∃ g ∈ Subgroup.closure (permsA 10 #[ruR0, ruR1]), g 0 = a ∧ g 1 = b := by
  obtain ⟨-, -, -, -, he, hsz, h2⟩ := ruAction_parts
  have hps : ∀ p ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List ℕ), p < 10 := by decide
  obtain ⟨k, hk, hk0, hk1⟩ := h2 a a.2 b b.2 (fun h => hab (Fin.ext h))
  have hrep := rep_of_validA ((enumOK_spec hps he).2.2 k hk)
  refine ⟨_, ((enumOK_spec hps he).1 _).2 ⟨k, hk, rfl⟩, Fin.ext ?_, Fin.ext ?_⟩
  · have := hrep.apply (show 0 < 10 by norm_num)
    exact this.symm.trans hk0
  · have := hrep.apply (show 1 < 10 by norm_num)
    exact this.symm.trans hk1

theorem ruPhi_two_pretransitive :
    MulAction.IsMultiplyPretransitive ruPhi.range (Fin 10) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨g1, hg1, hg10, hg11⟩ := ruTen_two a b hab
  obtain ⟨g2, hg2, hg20, hg21⟩ := ruTen_two c d hcd
  refine ⟨⟨g2 * g1⁻¹, ruPhi.range.mul_mem (closure_le_range_ruPhi hg2)
    (ruPhi.range.inv_mem (closure_le_range_ruPhi hg1))⟩, ?_, ?_⟩
  · change (g2 * g1⁻¹) a = c
    rw [← hg10]; simp [hg20]
  · change (g2 * g1⁻¹) b = d
    rw [← hg11]; simp [hg21]

theorem ruCube_of_ker (c : RuC) (hker : ruPhi c = 1) : c ^ 3 = 1 := by
  obtain ⟨i, hi, hiq⟩ := (ruCent_enum.1 c.1.1).1 (mem_closure_of_mem_RuC c.2)
  have hrep : Rep 4060 (ruEl i) c.1.1 := by
    have := rep_of_validA (ruCent_enum.2.2 i hi)
    rw [hiq] at this
    exact this
  have hcomm := ruComm_of_mem c.2
  have hfix : ∀ k < 10, ruActNat c.1.1 k = k := by
    intro k hk
    have := congrArg (fun f : Equiv.Perm (Fin 10) => ((f ⟨k, hk⟩ : Fin 10) : ℕ)) hker
    simpa [ruPhi_apply] using this
  have hall : (ruF.all fun p => (ruEl i)[p]! == p) = true := by
    rw [List.all_eq_true]
    intro p hp
    have hp' := ruF_lt p hp
    rw [beq_iff_eq, rep_ruCAct hrep hp']
    have hk := ruF_idx_lt hp
    have h1 := hfix _ hk
    have hq := ruCAct_mem_F hcomm (ruF_getElem_mem hk)
    unfold ruActNat at h1
    rw [ruF_getElem_idx p hp] at h1 hq
    have this : ruF[ruF.idxOf (ruCAct c.1.1 p)]! = ruF[ruF.idxOf p]! := by rw [h1]
    rwa [ruF_getElem_idx _ hq, ruF_getElem_idx p hp] at this
  have h2 := ruAction_parts.2.1 i hi
  rw [hall] at h2
  simp only [Bool.not_true, Bool.false_or] at h2
  have h3 := (eqA_iff (rep_powArr hrep 3) rep_idA).1 h2
  apply Subtype.ext
  apply Subtype.ext
  simpa using h3

theorem isPGroup_ker_ruPhi : IsPGroup 3 ruPhi.ker := by
  intro g
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    simpa using ruCube_of_ker g.1 g.2
  exact ⟨1, by simpa using hg3⟩

theorem aschbacherSolvableCore_ruXp :
    CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 RuC = ⊥ := by
  have : Finite ruP := inferInstance
  have : Finite RuC := inferInstance
  have : MulAction.IsPreprimitive ruPhi.range (Fin 10) :=
    MulAction.isPreprimitive_of_is_two_pretransitive ruPhi_two_pretransitive
  refine CFSG.AGLEmbeddingD2.Wilson.Proving.aschbacherSolvableCore_eq_bot_of_hom ruPhi ?_
    isPGroup_ker_ruPhi
  intro A hcomm htrans
  rw [CFSG.AGLEmbeddingD2.Wilson.Proving.card_mul_card_mulAut_eq_forty_of_abelian_transitive_ten
    A hcomm htrans]
  have := card_range_ruPhi_ge
  omega

end Stage5

section Final

theorem thetaCent_ru
    (b : ruP) (hb : b ^ 3 = 1) (hb1 : b ≠ 1) :
    CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
      (Subgroup.centralizer ({b} : Set ruP)) = ⊥ := by
  have : Finite ruP := inferInstance
  obtain ⟨g, hg⟩ := exists_conj_ruXp b hb hb1
  exact aschbacherSolvableCore_three_centralizer_eq_bot_of_conj g b ruXp hg
    aschbacherSolvableCore_ruXp

end Final

section Transport

open CFSG.Blueprint

theorem thetaCent_of_ru
    {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.Carrier .Ru) (b : X)
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
      (Subgroup.centralizer ({b} : Set X)) = ⊥ := by
  let e' : X ≃* ruP := e.trans ruEquivP
  rw [ThreeCore.aschbacherSolvableCore_three_centralizer_eq_bot_iff e' b]
  refine thetaCent_ru (e' b) (by rw [← map_pow, hb3, map_one]) fun h => hb1 ?_
  exact e'.injective (by rw [h, map_one])

end Transport

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCriterion
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

section Defs

variable {W : Type*} [Group W]

@[expose] def FWitness (X E : Subgroup W) : Prop := X ≤ nE X E

@[expose] def YCensusF (X : Subgroup W) (Exc : Subgroup W → Prop) : Prop :=
  ∀ E : Subgroup W, IsElemAbelian 2 E → 4 ≤ Nat.card E → ¬ Exc E → YWitness X E ∨ FWitness X E

theorem fWitness_of_le {X E₀ E : Subgroup W} (h : E₀ ≤ E) (hF : FWitness X E₀) :
    FWitness X E :=
  hF.trans (nE_mono X h)

end Defs

theorem fWitness_map_iff {W U : Type*} [Group W] [Group U] (ι : W →* U)
    (hι : Function.Injective ι) (X E : Subgroup W) :
    FWitness (X.map ι) (E.map ι) ↔ FWitness X E := by
  rw [FWitness, FWitness, ← map_nE ι hι, map_le_map_iff_of_injective hι]

theorem yCensusF_of_le_sylow {W : Type*} [Group W] [Finite W] {X S : Subgroup W}
    (hX : X.Normal) (hS : IsSylowOf 2 S ⊤) {Exc : Subgroup W → Prop}
    (hExc : ∀ (E : Subgroup W) (w : W), Exc (E.map (MulAut.conj w).toMonoidHom) → Exc E)
    (h : ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E → ¬ Exc E →
      YWitness X E ∨ FWitness X E) :
    YCensusF X Exc := by
  intro E hE hE4 hExcE
  obtain ⟨m, -, hm⟩ := exists_conj_le_of_isSylowOf hS (isPGroup_of_isElemAbelian hE) le_top
  set σ := MulAut.conj m⁻¹
  have hle : E.map σ.toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [σ, MulAut.conj_apply] using hm x hx
  have hw := h _ hle (isElemAbelian_map hE _)
    (by rwa [card_map_of_injective σ.injective])
    (fun hc => hExcE (hExc E m⁻¹ hc))
  rwa [← map_conj_eq_of_normal hX m⁻¹, yWitness_map_iff σ.toMonoidHom σ.injective,
    fWitness_map_iff σ.toMonoidHom σ.injective] at hw

section GSide

variable {G W : Type*} [Group G] [Group W]

theorem nE_map_le {A Q T : Subgroup G} {X : Subgroup W} {ψ : normalizer (A : Set G) →* W}
    (hψ : IsActionHom A X ψ) (hTQ : T ≤ Q) (hTN : T ≤ normalizer (A : Set G))
    (hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c → c ∈ normalizer (Q : Set G)) :
    nE X ((T.subgroupOf (normalizer (A : Set G))).map ψ) ≤
      ((A ⊓ Q).subgroupOf (normalizer (A : Set G))).map ψ := by
  have hΓ : gammaE X ((T.subgroupOf (normalizer (A : Set G))).map ψ) ≤
      ((A ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (A : Set G))).map ψ := by
    refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    obtain ⟨t, ht, rfl⟩ := he
    have ht1 : (t : G) ≠ 1 := fun h => he1 (by rw [show t = 1 from Subtype.ext h, map_one])
    refine (centDer_le_map hψ t).trans (Subgroup.map_mono fun c hc => ?_)
    refine ⟨hc.1, hQ (t : G) ht ht1 (c : G) hc.1 ?_⟩
    exact (mem_centralizer_iff.mp hc.2 (t : G) rfl).symm
  have hcomm : ⁅T.subgroupOf (normalizer (A : Set G)),
      (A ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (A : Set G))⁆ ≤
      (A ⊓ Q).subgroupOf (normalizer (A : Set G)) := by
    rw [commutator_le]
    intro v hv c hc
    have h := commutator_le_inf hTQ hTN
    rw [commutator_le] at h
    have hvc := h (v : G) hv (c : G) hc
    change ((⁅v, c⁆ : normalizer (A : Set G)) : G) ∈ A ⊓ Q
    simpa [commutatorElement_def] using hvc
  calc nE X ((T.subgroupOf (normalizer (A : Set G))).map ψ)
      ≤ ⁅(T.subgroupOf (normalizer (A : Set G))).map ψ,
          ((A ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (A : Set G))).map ψ⁆ :=
        commutator_mono le_rfl hΓ
    _ = (⁅T.subgroupOf (normalizer (A : Set G)),
          (A ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (A : Set G))⁆).map ψ :=
        (Subgroup.map_commutator _ _ ψ).symm
    _ ≤ _ := Subgroup.map_mono hcomm

theorem le_of_le_map {A Q : Subgroup G} {X : Subgroup W} {ψ : normalizer (A : Set G) →* W}
    (hψ : IsActionHom A X ψ) (hA : commutator ↥A = ⊤)
    (h : X ≤ ((A ⊓ Q).subgroupOf (normalizer (A : Set G))).map ψ) : A ≤ Q := by
  have hdec : ∀ a ∈ A, ∃ y ∈ A ⊓ Q, ∃ z ∈ centralizer (A : Set G), a = z * y := by
    intro a ha
    obtain ⟨y, hy, hyx⟩ := h (hψ.map_mem a ha)
    refine ⟨y, hy, a * (y : G)⁻¹, ?_, by group⟩
    have h1 : ψ (⟨a, le_normalizer ha⟩ * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hyx, mul_inv_cancel]
    simpa using (hψ.eq_one_iff _).mp h1
  have hcomm : ∀ {u v : G}, u ∈ centralizer (A : Set G) → v ∈ A → Commute u v :=
    fun hu hv => (mem_centralizer_iff.mp hu _ hv).symm
  have hle : ⁅(⊤ : Subgroup ↥A), ⊤⁆ ≤ Q.subgroupOf A := by
    rw [commutator_le]
    rintro ⟨b, hb⟩ - ⟨c, hc⟩ -
    obtain ⟨y, hy, z, hz, rfl⟩ := hdec b hb
    obtain ⟨y', hy', z', hz', rfl⟩ := hdec c hc
    have hz'A : z' ∈ A := by
      have := A.mul_mem hc (A.inv_mem hy'.1)
      simpa using this
    have e : ⁅z * y, z' * y'⁆ = ⁅y, y'⁆ :=
      commutatorElement_mul_left_central (hcomm hz hy.1) (hcomm hz hy'.1) (hcomm hz' hy.1)
        (hcomm hz' hy'.1) (hcomm hz hz'A)
    rw [mem_subgroupOf]
    have hcoe : ((⁅(⟨z * y, hb⟩ : ↥A), ⟨z' * y', hc⟩⁆ : ↥A) : G) = ⁅z * y, z' * y'⁆ := by
      simp [commutatorElement_def]
    rw [hcoe, e, commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hy.2 hy'.2) (Q.inv_mem hy.2)) (Q.inv_mem hy'.2)
  intro a ha
  have hmem : (⟨a, ha⟩ : ↥A) ∈ commutator ↥A := hA ▸ mem_top _
  rw [commutator_def] at hmem
  exact hle hmem

theorem not_fWitness_map {A T : Subgroup G} (hA : standardComponentIsStandard A) {g : G}
    {X : Subgroup W} {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    (hTQ : T ≤ rightConjugate (centralizer (A : Set G)) g) (hTN : T ≤ normalizer (A : Set G))
    (hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c →
      c ∈ normalizer (rightConjugate (centralizer (A : Set G)) g : Set G)) :
    ¬ FWitness X ((T.subgroupOf (normalizer (A : Set G))).map ψ) := by
  intro hF
  have hAQ := le_of_le_map hψ hA.1.1 (hF.trans (nE_map_le hψ hTQ hTN hQ))
  apply hA.2.2.2.2 g
  rw [commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  have hbK := (mem_rightConjugate_iff _ g b).mp (hAQ hb)
  have := mem_centralizer_iff.mp hbK a ha
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact this.symm

end GSide

theorem exc_of_yCensusF (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) {G : Type} [Group G]
    [Finite G] {A : Subgroup G} (hA : AS76b.Hyp31 A) {X₀ W : Type*} [Group X₀] [Group W]
    [Finite W] {X : Subgroup W} (hW : AutModel X₀ W X) (e : ↥A ⧸ center ↥A ≃* X₀) :
    ∃ ψ : normalizer (A : Set G) →* W, IsActionHom A X ψ ∧
      ∃ g : G, g ∉ normalizer (A : Set G) ∧ ∃ T : Subgroup G,
        IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)) ∧
        IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) ∧
        ∀ Exc : Subgroup W → Prop, YCensusF X Exc →
          Exc ((T.subgroupOf (normalizer (A : Set G))).map ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ, g, hg, T, hT1, hT2, hY⟩ := exc_of_yCensus h32 h33 hA hW e
  refine ⟨ψ, hψ, g, hg, T, hT1, hT2, fun Exc hc => ?_⟩
  have hYc : YCensus X (fun E => Exc E ∨ FWitness X E) := fun E h1 h2 h3 =>
    (hc E h1 h2 (fun h => h3 (Or.inl h))).resolve_right (fun h => h3 (Or.inr h))
  rcases hY _ hYc with hExc | hF
  · exact hExc
  exfalso
  have hR := h32 G A hA
  have hK := tightlyEmbedded_centralizer_of_standard hA.standard
  have hTab : ∀ x ∈ T, x ^ 2 = 1 := by
    intro x hx
    have hxK : g * x * g⁻¹ ∈ centralizer (A : Set G) :=
      (mem_rightConjugate_iff _ g x).mp (hT2.le hx)
    have h2 : IsPGroup 2 (zpowers (g * x * g⁻¹)) := by
      have hx2 : IsPGroup 2 (zpowers x) := hT2.isPGroup.to_le (zpowers_le.mpr hx)
      have := hx2.map (MulAut.conj g).toMonoidHom
      rwa [MonoidHom.map_zpowers] at this
    have hsq := sq_eq_one_of_isPGroup_zpowers hR hxK h2
    have hc' : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := conj_pow
    rw [hc'] at hsq
    have := congrArg (fun y => g⁻¹ * y * g) hsq
    simpa [mul_assoc] using this
  have hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c →
      c ∈ normalizer (rightConjugate (centralizer (A : Set G)) g : Set G) :=
    fun t ht ht1 c _ hct => mem_normalizer_of_commute_of_tightlyEmbedded
      (tightlyEmbedded_rightConjugate' hK g) (hT2.le ht) ht1 (hTab t ht) hct
  exact not_fWitness_map hA.standard hψ hT2.le (hT1.le.trans inf_le_right) hQ hF

theorem sporadicCaseOdd_of_yCensusF (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three)
    {s : TauCeti.SporadicName} {W : Type*} [Group W] [Finite W] {X : Subgroup W}
    (hW : AutModel (Blueprint.NativeSporadic.Carrier s) W X) (hcII : YCensus X (· ≤ X))
    (hc : YCensusF X (fun _ => False)) : SporadicCaseOdd s := by
  intro G _ _ A hH hodd ⟨e⟩
  have hyp : AS76b.Hyp31 A :=
    ⟨hH.standard, hypII_of_yCensus hW hcII hH.standard.1.1 e, hodd,
      by have := hH.rank; omega, hH.not_normal⟩
  obtain ⟨ψ, -, g, -, T, -, -, hExc⟩ := exc_of_yCensusF h32 h33 hyp hW e
  exact hExc _ hc

end CFSG.ComponentClassification.RankTwoSporadic

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

structure FNode where
  basis : Array (Array ℕ)
  facs : List NFac
  prog : List (ℕ × ℕ)
  gIdx : List ℕ
deriving Inhabited

@[expose] def fullOK (n : ℕ) (inX : Array ℕ → Bool) (xGens : Array (Array ℕ)) (nd : FNode) :
    Bool :=
  let ys := (nd.facs.map (NFac.val n nd.basis)).toArray
  let regs := slpRegs n ys nd.prog
  (allLt nd.basis.size fun k => validA n nd.basis[k]!) && nd.facs.all (NFac.ok n inX nd.basis) &&
    slpOK n ys nd.prog && allLt xGens.size fun k =>
      decide (nd.gIdx.getD k 0 < regs.size) && eqA n xGens[k]! regs[nd.gIdx.getD k 0]!

@[expose] def pairOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (nodes : Array FNode) (x y : Array ℕ) :
    Bool :=
  let c := enumBfs n #[x, y] ps fuel
  enumOK n #[x, y] ps c && (List.range nodes.size).any fun k =>
    allLt nodes[k]!.basis.size fun j => memA n c nodes[k]!.basis[j]!

@[expose] def fCensusOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (inX : Array ℕ → Bool)
    (xGens sGens : Array (Array ℕ)) (nodes : Array FNode) : Bool :=
  let cS := enumBfs n sGens ps fuel
  enumOK n sGens ps cS && (allLt xGens.size fun k => validA n xGens[k]!) &&
    (allLt nodes.size fun k => fullOK n inX xGens nodes[k]!) &&
    allLt cS.pts.size fun i => allLt cS.pts.size fun j =>
      !(eqA n (compA n cS.pts[i]! cS.pts[i]!) (idA n)) || eqA n cS.pts[i]! (idA n) ||
        eqA n cS.pts[j]! (idA n) || eqA n cS.pts[i]! cS.pts[j]! ||
        !(commA n cS.pts[i]! cS.pts[j]!) || pairOK n ps fuel nodes cS.pts[i]! cS.pts[j]!

section Soundness

variable {n : ℕ} {X : Subgroup (Equiv.Perm (Fin n))} {inX : Array ℕ → Bool}

theorem le_nE_of_fullOK (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    {xGens : Array (Array ℕ)} (hxv : ∀ k < xGens.size, validA n xGens[k]! = true) {nd : FNode}
    (h : fullOK n inX xGens nd = true) :
    closure (permsA n xGens) ≤ nE X (closure (permsA n nd.basis)) := by
  simp only [fullOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hb, hf⟩, hslp⟩, hx⟩ := h
  have hb' : ∀ k < nd.basis.size, validA n nd.basis[k]! = true := fun k hk => allLt_spec hb hk
  have hys : closure (permsA n (nd.facs.map (NFac.val n nd.basis)).toArray) ≤
      nE X (closure (permsA n nd.basis)) :=
    closure_le_of_rep fun f hf' => NFac.mem_nE hin hb' (List.all_eq_true.mp hf f hf')
  rw [closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hxk := allLt_spec hx hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hxk
  obtain ⟨hlt, heq⟩ := hxk
  obtain ⟨g, hg, hr⟩ := rep_slpRegs hslp _ hlt
  have hkg : permOfArr n xGens[k]! = g := eq_of_eqA (rep_of_validA (hxv k hk)) hr heq
  show permOfArr n xGens[k]! ∈ _
  rw [hkg]
  exact hys hg

theorem exists_pair_of_four_le {E : Subgroup (Equiv.Perm (Fin n))} (hE : IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) : ∃ x ∈ E, ∃ y ∈ E, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (hcon x hx)
    rw [hbot, card_bot] at hE4
    omega
  obtain ⟨y, hyE, hy⟩ : ∃ y ∈ E, y ≠ 1 ∧ x ≠ y := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ zpowers x := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]
        exact one_mem _
      · rw [← hcon y hy hy1]
        exact mem_zpowers x
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (hE.2 x hxE)
    have hcard := card_le_of_le hle
    rw [Nat.card_zpowers] at hcard
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  exact ⟨x, hxE, y, hyE, hx1, hy.1, hy.2⟩

theorem fWitness_of_fCensusOK {ps : List ℕ} {fuel : ℕ} {xGens sGens : Array (Array ℕ)}
    {nodes : Array FNode} (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hX : X ≤ closure (permsA n xGens))
    (h : fCensusOK n ps fuel inX xGens sGens nodes = true)
    {E : Subgroup (Equiv.Perm (Fin n))} (hES : E ≤ closure (permsA n sGens))
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) : FWitness X E := by
  simp only [fCensusOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hS, hxv⟩, hnodes⟩, hpairs⟩ := h
  set cS := enumBfs n sGens ps fuel
  obtain ⟨hSmem, -, hSval⟩ := enumOK_spec hps hS
  have hxv' : ∀ k < xGens.size, validA n xGens[k]! = true := fun k hk => allLt_spec hxv hk
  obtain ⟨x, hxE, y, hyE, hx1, hy1, hxy⟩ := exists_pair_of_four_le hE hE4
  obtain ⟨i, hi, rfl⟩ := (hSmem _).1 (hES hxE)
  obtain ⟨j, hj, rfl⟩ := (hSmem _).1 (hES hyE)
  have hri := rep_of_validA (hSval i hi)
  have hrj := rep_of_validA (hSval j hj)
  have hfalse : ∀ {a b : Array ℕ} {g h : Equiv.Perm (Fin n)}, Rep n a g → Rep n b h → g ≠ h →
      eqA n a b = false := by
    intro a b g h ha hb hgh
    by_contra hc
    exact hgh (eq_of_eqA ha hb (by simpa using hc))
  have h1 : eqA n (compA n cS.pts[i]! cS.pts[i]!) (idA n) = true := by
    rw [eqA_iff (rep_compA hri hri) rep_idA, ← sq]
    exact hE.2 _ hxE
  have h2 : commA n cS.pts[i]! cS.pts[j]! = true :=
    (commA_iff hri hrj).2 (congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hxE⟩ ⟨_, hyE⟩))
  have hp : pairOK n ps fuel nodes cS.pts[i]! cS.pts[j]! = true := by
    have hp := allLt_spec (allLt_spec hpairs hi) hj
    rw [h1, hfalse hri rep_idA hx1, hfalse hrj rep_idA hy1, hfalse hri hrj hxy, h2] at hp
    simpa using hp
  simp only [pairOK, Bool.and_eq_true, List.any_eq_true, List.mem_range] at hp
  obtain ⟨hc, k, hk, hkb⟩ := hp
  have hnk := allLt_spec hnodes hk
  have hbv : ∀ l < nodes[k]!.basis.size, validA n nodes[k]!.basis[l]! = true := by
    have := hnk
    simp only [fullOK, Bool.and_eq_true] at this
    exact fun l hl => allLt_spec this.1.1.1 hl
  have hxyE : closure (permsA n #[cS.pts[i]!, cS.pts[j]!]) ≤ E := by
    rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl2 : l < 2 := hl
    interval_cases l
    · exact hxE
    · exact hyE
  have hkE : closure (permsA n nodes[k]!.basis) ≤ E := by
    refine le_trans ?_ hxyE
    rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact enumOK_mem_of_any hps hc (rep_of_validA (hbv l hl)) (allLt_spec hkb hl)
  exact hX.trans ((le_nE_of_fullOK hin hxv' hnk).trans (nE_mono X hkE))

end Soundness

section DecodeF

variable (tk : Array ℕ) (regs : Array (Array ℕ))

@[expose] def rdFNodeR (p : ℕ) : FNode × ℕ :=
  let b := rdListC tk (rdReg tk regs) p
  let f := rdListC tk (rdNFacR tk regs) b.2
  let pr := rdListC tk (rdPair tk) f.2
  let g := rdListC tk (fun p => (tk[p]!, p + 1)) pr.2
  (⟨b.1.toArray, f.1, pr.1, g.1⟩, g.2)

structure FCensusData where
  sGens : Array (Array ℕ)
  nodes : Array FNode

@[expose] def rdFCensusR : FCensusData :=
  let s := rdListC tk (rdReg tk regs) 0
  let d := rdListC tk (rdFNodeR tk regs) s.2
  ⟨s.1.toArray, d.1.toArray⟩

end DecodeF

@[expose] def decodeFCertR (regs : Array (Array ℕ)) (s : String) : FCensusData :=
  rdFCensusR (decodeNats s) regs

end CFSG.ComponentClassification.RankTwoSporadic.Cert

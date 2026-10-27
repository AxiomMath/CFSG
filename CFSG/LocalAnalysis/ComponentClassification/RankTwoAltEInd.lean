module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEL
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalQuot
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSol
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoClassical

@[expose] def AltStandardAt (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    standardComponentOddCore G = ⊥ → Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin m)) →
      Nonempty (rankTwoX A ≃* alternatingGroup (Fin (m + 4)))

section Lift

variable {Q : Type} [Group Q]

theorem map_rankTwoX_of_surjective {Q' : Type} [Group Q'] (f : Q →* Q')
    (hf : Function.Surjective f) (M : Subgroup Q) : (rankTwoX M).map f = rankTwoX (M.map f) := by
  simp only [rankTwoX, Subgroup.map_normalClosure _ f hf, Subgroup.coe_map]

theorem le_centralizer_rankTwoX_of_le {M N : Subgroup Q} [N.Normal]
    (h : N ≤ centralizer (M : Set Q)) : N ≤ centralizer (rankTwoX M : Set Q) := by
  rw [le_centralizer_iff] at h ⊢
  exact normalClosure_le_normal h

theorem commutator_rankTwoX_of_commutator {M : Subgroup Q} (hM : commutator M = ⊤) :
    commutator (rankTwoX M) = ⊤ := by
  have : Group.IsPerfect ↥M := (Group.isPerfect_def).2 hM
  have hle : M ≤ rankTwoX M := le_normalClosure
  have hN : (rankTwoX M).Normal := normalClosure_normal
  have hder : M ≤ ⁅rankTwoX M, rankTwoX M⁆ := by
    calc M = ⁅M, M⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅rankTwoX M, rankTwoX M⁆ := Subgroup.commutator_mono hle hle
  have heq : ⁅rankTwoX M, rankTwoX M⁆ = rankTwoX M :=
    le_antisymm (Subgroup.commutator_le_self _) (normalClosure_le_normal hder)
  exact (Group.isPerfect_def).1 (Subgroup.isPerfect_iff.mpr heq)

variable [Finite Q]

theorem nonempty_rankTwoX_equiv_of_map {M : Subgroup Q} (hM : RankTwoHyp Q M) {m : ℕ}
    (hm : 6 ≤ m) (e : rankTwoX (M.map (QuotientGroup.mk' (standardComponentOddCore Q))) ≃*
      alternatingGroup (Fin (m + 2))) :
    Nonempty (rankTwoX M ≃* alternatingGroup (Fin (m + 2))) := by
  set O := standardComponentOddCore Q with hOdef
  set π := QuotientGroup.mk' O with hπdef
  set X := rankTwoX M with hXdef
  have hOM : O ≤ centralizer (M : Set Q) := oddCore_le_of_rankTwoHyp hM
  have hOX : O ≤ centralizer (X : Set Q) := le_centralizer_rankTwoX_of_le hOM
  have : Group.IsPerfect ↥X :=
    (Group.isPerfect_def).2 (commutator_rankTwoX_of_commutator hM.standard.1.1)
  have hmap : X.map π = rankTwoX (M.map π) :=
    map_rankTwoX_of_surjective π (QuotientGroup.mk'_surjective O) M
  set η : ↥X →* alternatingGroup (Fin (m + 2)) :=
    e.toMonoidHom.comp ((MulEquiv.subgroupCongr hmap).toMonoidHom.comp (π.subgroupMap X))
    with hηdef
  have hη : Function.Surjective η :=
    e.surjective.comp ((MulEquiv.subgroupCongr hmap).surjective.comp (π.subgroupMap_surjective X))
  have hmemker : ∀ x : ↥X, x ∈ η.ker ↔ (x : Q) ∈ O := fun x => by
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : π.subgroupMap X x = 1 := by
        have h2 : (MulEquiv.subgroupCongr hmap) (π.subgroupMap X x) = 1 :=
          (MulEquiv.map_eq_one_iff e).mp hx
        exact (MulEquiv.map_eq_one_iff _).mp h2
      have h3 : π (x : Q) = 1 := congrArg Subtype.val h1
      rwa [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    · intro hx
      have h1 : π.subgroupMap X x = 1 := by
        apply Subtype.ext
        change π (x : Q) = 1
        rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hx
      simp only [hηdef, MonoidHom.coe_comp, Function.comp_apply, h1, map_one]
  have hK : η.ker ≤ center ↥X := fun x hx => by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hOX ((hmemker x).mp hx)) y y.2)
  have hodd : Odd (Nat.card η.ker) := by
    refine (RankTwoSporadic.odd_card_standardComponentOddCore (G := Q)).of_dvd_nat ?_
    let φ : ↥η.ker →* ↥O :=
      { toFun := fun x => ⟨(x : ↥X), (hmemker _).mp x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective φ := fun a b hab => by
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
    exact Subgroup.card_dvd_of_injective φ hinj
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd hm η hη hK hodd
  have hinj : Function.Injective η := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.card_eq_one.mp h1
  exact ⟨MulEquiv.ofBijective η ⟨hinj, hη⟩⟩

end Lift

theorem card_le_of_isSylowOf_two {G : Type} [Group G] [Finite G] {R X P : Subgroup G}
    (hR : IsSylowOf 2 R X) (hPX : P ≤ X) (hP : IsPGroup 2 P) : Nat.card P ≤ Nat.card R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hPS⟩ := (hP.comap_subtype (K := X)).exists_le_sylow
  set S' : Subgroup G := (S : Subgroup X).map X.subtype with hS'def
  have hS' : IsSylowOf 2 S' X := ⟨S, rfl⟩
  have hPS' : P ≤ S' := fun x hx => ⟨⟨x, hPX hx⟩, hPS hx, rfl⟩
  rw [hR.card_eq, ← hS'.card_eq]
  exact Subgroup.card_le_of_le hPS'

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}

namespace NormPair

variable (np : NormPair A R T g n) (hn : 8 ≤ n)

@[expose] noncomputable def DW : Subgroup G :=
  (rankTwoX (np.LE.subgroupOf (centralizer (zpowers (np.wE hn) : Set G)))).map
    (centralizer (zpowers (np.wE hn) : Set G)).subtype

omit [Finite G] in
theorem DW_le : np.DW hn ≤ centralizer (zpowers (np.wE hn) : Set G) := map_subtype_le _

omit [Finite G] in
theorem LE_le_DW : np.LE ≤ np.DW hn := by
  intro x hx
  exact ⟨⟨x, np.LE_le_centralizer hn hx⟩, le_normalClosure hx, rfl⟩

theorem le_normalizer_DW :
    centralizer (zpowers (np.wE hn) : Set G) ≤ normalizer (np.DW hn : Set G) := by
  intro x hx
  apply mem_normalizer_of_conj_mem
  rintro _ ⟨d, hd, rfl⟩
  have hN : (rankTwoX (np.LE.subgroupOf (centralizer (zpowers (np.wE hn) : Set G)))).Normal :=
    normalClosure_normal
  exact ⟨⟨x, hx⟩ * d * ⟨x, hx⟩⁻¹, hN.conj_mem d hd ⟨x, hx⟩, rfl⟩

theorem nonempty_DW_equiv_of
    (hM : RankTwoHyp (centralizer (zpowers (np.wE hn) : Set G))
      (np.LE.subgroupOf (centralizer (zpowers (np.wE hn) : Set G))))
    (e : rankTwoX ((np.LE.subgroupOf (centralizer (zpowers (np.wE hn) : Set G))).map
      (QuotientGroup.mk' (standardComponentOddCore (centralizer (zpowers (np.wE hn) : Set G))))) ≃*
        alternatingGroup (Fin (n + 1))) :
    Nonempty (np.DW hn ≃* alternatingGroup (Fin (n + 1))) := by
  set C := centralizer (zpowers (np.wE hn) : Set G) with hCdef
  set M := np.LE.subgroupOf C with hMdef
  obtain ⟨e'⟩ := nonempty_rankTwoX_equiv_of_map hM (m := n - 1) (by omega)
    (e.trans (altCongrHom (finCongr (by omega))))
  exact ⟨(((rankTwoX M).equivMapOfInjective C.subtype C.subtype_injective).symm.trans e').trans
    (altCongrHom (finCongr (by omega)))⟩

variable (hc : Sec3 A R T g)
include hc

theorem nonempty_DW_equiv
    (hn9 : 9 ≤ n) (hK : Assembly.KProper Blueprint.Catalog G) (h4 : Asc75Theorem4)
    (h32 : Lemma32) (h34 : Asc08Lemma34) (IH : AltStandardAt (n - 3)) :
    Nonempty (np.DW hn ≃* alternatingGroup (Fin (n + 1))) := by
  set C := centralizer (zpowers (np.wE hn) : Set G) with hCdef
  set M := np.LE.subgroupOf C with hMdef
  have hM : RankTwoHyp C M := np.rankTwoHyp_LE hn hc hn9 hK h4 h32 h34
  let eM : M ≃* alternatingGroup (Fin (n - 3)) :=
    (subgroupOfEquivOfLe (np.LE_le_centralizer hn)).trans (np.LEEquiv hn)
  have hZ : center ↥M = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : eM z ∈ center (alternatingGroup (Fin (n - 3))) := by
      rw [mem_center_iff] at hz ⊢
      intro y
      obtain ⟨y', rfl⟩ := eM.surjective y
      rw [← map_mul, ← map_mul, hz y']
    rw [alternatingGroup.center_eq_bot (by simp; omega), mem_bot, MulEquiv.map_eq_one_iff] at hz'
    rw [mem_bot]
    exact hz'
  let eQ : rankTwoQuot M ≃* alternatingGroup (Fin (n - 3)) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans eM)
  obtain ⟨e⟩ := IH _ _ (rankTwoHyp_map hM) RankTwoSporadic.standardComponentOddCore_quotient_eq_bot
    ⟨(quotCenterMap hM).symm.trans eQ⟩
  exact np.nonempty_DW_equiv_of hn hM (e.trans (altCongrHom (finCongr (by omega))))

theorem isSylowOf_R_WL :
    IsSylowOf 2 R (centralizer (zpowers (np.wE hn) : Set G) ⊓ centralizer (np.LE : Set G)) :=
  Lemma37.isSylowOf_of_isSylowOf_inf_normalizer (np.isSylowOf_R_LE hn hc)

theorem B_le_DW (ψD : np.DW hn ≃* alternatingGroup (Fin (n + 1))) :
    rightConjugate A g ≤ np.DW hn := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := rightConjugate A g with hBdef
  set C := centralizer (zpowers (np.wE hn) : Set G) with hCdef
  set D := np.DW hn with hDdef
  have hBC : B ≤ C := np.B_le_centralizer_W hn hc
  have hBN : B ≤ normalizer (D : Set G) := hBC.trans (np.le_normalizer_DW hn)
  have hn' : n + 1 = 5 ∨ 7 ≤ n + 1 := Or.inr (by omega)
  set α : B →* Perm (Fin (n + 1)) := (actPerm ψD hn').comp (inclusion hBN) with hαdef
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simp; omega)
  have : IsSimpleGroup B := np.equivB.isSimpleGroup
  have hcardB : Nat.card B = n.factorial / 2 := by
    rw [Nat.card_congr np.equivB.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hαA : ∀ b, α b ∈ alternatingGroup (Fin (n + 1)) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (sign.comp α).ker with h | h
    · exfalso
      have hinj : Function.Injective (sign.comp α) := (MonoidHom.ker_eq_bot_iff _).mp h
      have h1 := Nat.card_le_card_of_injective _ hinj
      rw [hcardB, Nat.card_eq_fintype_card, Fintype.card_units_int] at h1
      have h2 : (5 : ℕ).factorial ≤ n.factorial := Nat.factorial_le (by omega)
      have h3 : (5 : ℕ).factorial = 120 := rfl
      omega
    · intro b
      have hb : b ∈ (sign.comp α).ker := h ▸ mem_top b
      exact hb
  set α' : B →* alternatingGroup (Fin (n + 1)) := α.codRestrict _ hαA with hα'def
  set d : B →* D := ψD.symm.toMonoidHom.comp α' with hddef
  have hψd : ∀ b, (ψD (d b) : Perm (Fin (n + 1))) = α b := fun b => by
    simp [hddef, hα'def]
  have hd : ∀ (b : B) (x : D), (b : G) * x * (b : G)⁻¹ = (d b : G) * x * (d b : G)⁻¹ := by
    intro b x
    have h1 := actPerm_spec ψD hn' (inclusion hBN b) x
    have hmem : (b : G) * x * (b : G)⁻¹ ∈ D := (mem_normalizer_iff.mp (hBN b.2) x).mp x.2
    have h2 : ψD ⟨(b : G) * x * (b : G)⁻¹, hmem⟩ = ψD (d b * x * (d b)⁻¹) := by
      apply Subtype.ext
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hψd]
      exact h1
    exact congrArg Subtype.val (ψD.injective h2)
  have hcD : ∀ b : B, (d b : G)⁻¹ * b ∈ centralizer (D : Set G) := by
    intro b
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := hd b ⟨x, hx⟩
    calc x * ((d b : G)⁻¹ * b) = (d b : G)⁻¹ * ((d b : G) * x * (d b : G)⁻¹) * b := by group
      _ = (d b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * b := by rw [h1]
      _ = ((d b : G)⁻¹ * b) * x := by group
  let c : B →* G :=
    { toFun := fun b => (d b : G)⁻¹ * b
      map_one' := by simp
      map_mul' := fun b₁ b₂ => by
        have h := mem_centralizer_iff.mp (hcD b₁) _ (inv_mem (d b₂).2)
        simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
        calc (d b₂ : G)⁻¹ * (d b₁ : G)⁻¹ * ((b₁ : G) * b₂) =
            ((d b₂ : G)⁻¹ * ((d b₁ : G)⁻¹ * b₁)) * b₂ := by group
          _ = ((d b₁ : G)⁻¹ * b₁) * ((d b₂ : G)⁻¹ * b₂) := by rw [h]; group }
  have hc_apply : ∀ b, c b = (d b : G)⁻¹ * b := fun _ => rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal c.ker with h | h
  ·
    exfalso
    have hinj : Function.Injective c := (MonoidHom.ker_eq_bot_iff c).mp h
    have h8 : 2 ^ 3 ∣ Nat.card B := by
      obtain ⟨k, hk⟩ : 16 ∣ n.factorial :=
        (by decide : 16 ∣ (6 : ℕ).factorial).trans (Nat.factorial_dvd_factorial (by omega))
      exact ⟨k, by rw [hcardB]; omega⟩
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 2 h8
    have hP'card : Nat.card (P.map c) = 2 ^ 3 := by rw [card_map_of_injective hinj, hP]
    have hP'2 : IsPGroup 2 (P.map c) := IsPGroup.of_card hP'card
    have hP'X : P.map c ≤ C ⊓ centralizer (np.LE : Set G) := by
      rintro _ ⟨b, -, rfl⟩
      rw [hc_apply]
      refine mem_inf.mpr ⟨mul_mem (inv_mem (np.DW_le hn (d b).2)) (hBC b.2), ?_⟩
      exact centralizer_le (fun x hx => np.LE_le_DW hn hx) (hcD b)
    have hle := card_le_of_isSylowOf_two (np.isSylowOf_R_WL hn hc) hP'X hP'2
    rw [hP'card, np.card_R (by omega)] at hle
    omega
  · intro b hb
    have hb' : (⟨b, hb⟩ : B) ∈ c.ker := h ▸ mem_top _
    rw [MonoidHom.mem_ker, hc_apply] at hb'
    have hbd : b = (d ⟨b, hb⟩ : G) := (inv_mul_eq_one.mp hb').symm
    rw [hbd]
    exact (d _).2

end NormPair

end CFSG.ComponentClassification.RankTwoAlt

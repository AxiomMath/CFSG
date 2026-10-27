module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110e
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1314
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SplitExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD26e
import CFSG.Models.Transport
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeOut
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1245b
import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110f

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut Fi22Facts IsFiTwentyTwo)

section Gamma

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem comm_of_card_sq {p : ℕ} [Fact p.Prime] {P : Subgroup X} (hPc : Nat.card P = p ^ 2) :
    ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (IsPGroup.commutative_of_card_eq_prime_sq hPc ⟨a, ha⟩ ⟨b, hb⟩)

omit [Finite X] in
theorem gLBConj_zpowers_eq_of_mem_centralizer {x c : X} (hc : c ∈ Subgroup.centralizer ({x} : Set X)) :
    GLBConj c (Subgroup.zpowers x) = Subgroup.zpowers x := by
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  have hck : ∀ k : ℤ, c * x ^ k = x ^ k * c := fun k =>
    ((Commute.zpow_right (show Commute c x from hcx) k)).eq
  apply le_antisymm
  · intro y hy
    rw [mem_gLBConj] at hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
    have : y = c⁻¹ * (c * y * c⁻¹) * c := by group
    rw [this, ← hk]
    have e : c⁻¹ * x ^ k * c = x ^ k := by
      calc c⁻¹ * x ^ k * c = c⁻¹ * (x ^ k * c) := by group
        _ = c⁻¹ * (c * x ^ k) := by rw [hck k]
        _ = x ^ k := by group
    rw [e]
    exact Subgroup.zpow_mem_zpowers x k
  · intro y hy
    rw [mem_gLBConj]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have e : c * x ^ k * c⁻¹ = x ^ k := by rw [hck k]; group
    rw [e]
    exact Subgroup.zpow_mem_zpowers x k

theorem centralizer_le_layer_sup {P : Subgroup X} (hPc : Nat.card P = 5 ^ 2) (hP : IsSylowIn 5 ⊤ P)
    {x : X} (hxP : x ∈ P) (hx5 : orderOf x = 5)
    (hZ : Subgroup.center ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set X))) = ⊥)
    (h5 : 5 ∣ Nat.card ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set X)))) :
    Subgroup.centralizer ({x} : Set X) ≤
      GLAPLayer 5 (Subgroup.centralizer ({x} : Set X)) ⊔ Subgroup.normalizer (P : Set X) := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  set C := Subgroup.centralizer ({x} : Set X) with hC
  set L := GLAPLayer 5 C with hL
  have hPab := comm_of_card_sq hPc
  have hPC : P ≤ C := fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hPab y hy x hxP)
  have hPCs : IsSylowIn 5 C P := Claims1110d.isSylowIn_of_top hP hPC
  have hLC : L ≤ C := Claims1110b.glaPLayer_le'' 5 C
  have hCN : C ≤ Subgroup.normalizer (L : Set X) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPLayer 5 Subgroup.le_normalizer
  have hPL : IsSylowIn 5 L (P ⊓ L) := Claims1110d.isSylowIn_inf' hPCs hLC hCN
  have hPLc : Nat.card ↥(P ⊓ L) = 5 ^ (Nat.card L).factorization 5 := Claims1110.card_of_isSylowIn hPL
  have hfac : 1 ≤ (Nat.card L).factorization 5 :=
    Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' h5
  have hxL : x ∉ L := by
    intro hxL
    have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 (hLC l.2)
    rw [hZ, Subgroup.mem_bot] at hxZ
    have hx1 : x = 1 := congrArg Subtype.val hxZ
    rw [hx1, orderOf_one] at hx5
    norm_num at hx5
  have hPeq : Subgroup.zpowers x ⊔ P ⊓ L = P := by
    have hle : Subgroup.zpowers x ⊔ P ⊓ L ≤ P := sup_le ((Subgroup.zpowers_le).2 hxP) inf_le_left
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ P ⊓ L, a * b = b * a := fun a ha b hb =>
      hPab a ((Subgroup.zpowers_le).2 hxP ha) b (Subgroup.mem_inf.1 hb).1
    have hT := Claims1110e.card_sup_mul_card_inf_of_commute' (Subgroup.zpowers x) (P ⊓ L) hcomm
    have hI : Nat.card ↥(Subgroup.zpowers x ⊓ P ⊓ L) = 1 := by
      have hd : Nat.card ↥(Subgroup.zpowers x ⊓ P ⊓ L) ∣ 5 := by
        have := Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left :
          Subgroup.zpowers x ⊓ P ⊓ L ≤ Subgroup.zpowers x)
        rwa [Nat.card_zpowers, hx5] at this
      rcases (Nat.dvd_prime hp).1 hd with h1 | h1
      · exact h1
      · exfalso
        have heq : Subgroup.zpowers x ⊓ P ⊓ L = Subgroup.zpowers x :=
          Subgroup.eq_of_le_of_card_ge (inf_le_left.trans inf_le_left) (by rw [Nat.card_zpowers, hx5, h1])
        have : x ∈ Subgroup.zpowers x ⊓ P ⊓ L := by rw [heq]; exact Subgroup.mem_zpowers x
        exact hxL (Subgroup.mem_inf.1 this).2
    rw [inf_assoc] at hI
    rw [hI, mul_one, Nat.card_zpowers, hx5, hPLc] at hT
    rw [hT, hPc]
    calc 5 ^ 2 = 5 * 5 ^ 1 := by norm_num
      _ ≤ 5 * 5 ^ (Nat.card ↥L).factorization 5 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hfac)
  have hNPL : ∀ d ∈ C, d ∈ Subgroup.normalizer ((P ⊓ L : Subgroup X) : Set X) →
      d ∈ Subgroup.normalizer (P : Set X) := by
    intro d hdC hdN
    rw [mem_normalizer_iff_gLBConj_eq] at hdN ⊢
    rw [← hPeq]
    unfold GLBConj at hdN ⊢
    rw [Subgroup.map_sup]
    have hz := gLBConj_zpowers_eq_of_mem_centralizer hdC
    unfold GLBConj at hz
    rw [hz, hdN]
  intro c hc
  have hcN : c⁻¹ ∈ Subgroup.normalizer (L : Set X) := hCN (C.inv_mem hc)
  have hQL : GLBConj c⁻¹ (P ⊓ L) ≤ L := by
    have h1 := gLBConj_mono c⁻¹ (inf_le_right : P ⊓ L ≤ L)
    rwa [gLBConj_eq_of_mem_normalizer hcN] at h1
  obtain ⟨l, hlL, hl⟩ := Claims1110.exists_conj_eq_of_card inf_le_right hQL hPL.2.1
    (Claims1110.isPGroup_conj c⁻¹ hPL.2.1) hPLc (by rw [Claims1110.card_conj, hPLc])
  rw [gLBConj_gLBConj] at hl
  have hmem : c⁻¹ * l ∈ Subgroup.normalizer ((P ⊓ L : Subgroup X) : Set X) :=
    mem_normalizer_iff_gLBConj_eq.2 hl
  have hcl : c⁻¹ * l ∈ C := C.mul_mem (C.inv_mem hc) (hLC hlL)
  have hNP := hNPL _ hcl hmem
  have e : c = l * (c⁻¹ * l)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right (Subgroup.inv_mem _ hNP))

theorem normalizer_zpowers_le_layer_sup {P : Subgroup X} (hPc : Nat.card P = 5 ^ 2) (hP : IsSylowIn 5 ⊤ P)
    {x : X} (hxP : x ∈ P) (hx5 : orderOf x = 5)
    (hZ : Subgroup.center ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set X))) = ⊥)
    (h5 : 5 ∣ Nat.card ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set X)))) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup X) : Set X) ≤
      GLAPLayer 5 (Subgroup.centralizer ({x} : Set X)) ⊔ Subgroup.normalizer (P : Set X) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C := Subgroup.centralizer ({x} : Set X) with hC
  have hPab := comm_of_card_sq hPc
  have hPC : P ≤ C := fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hPab y hy x hxP)
  have hPCs : IsSylowIn 5 C P := Claims1110d.isSylowIn_of_top hP hPC
  have hCle := centralizer_le_layer_sup hPc hP hxP hx5 hZ h5
  intro n hn
  have hnx : n * x * n⁻¹ ∈ P :=
    (Subgroup.zpowers_le).2 hxP ((Subgroup.mem_normalizer_iff.1 hn x).1 (Subgroup.mem_zpowers x))
  have hQC : GLBConj n P ≤ C := by
    intro y hy
    rw [mem_gLBConj] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hPab _ hy _ hnx
    have h2 : n * (y * x) * n⁻¹ = n * (x * y) * n⁻¹ := by
      calc n * (y * x) * n⁻¹ = (n * y * n⁻¹) * (n * x * n⁻¹) := by group
        _ = (n * x * n⁻¹) * (n * y * n⁻¹) := h1
        _ = n * (x * y) * n⁻¹ := by group
    simpa using h2
  have hPCc : Nat.card P = 5 ^ (Nat.card C).factorization 5 := Claims1110.card_of_isSylowIn hPCs
  obtain ⟨c, hcC, hc⟩ := Claims1110.exists_conj_eq_of_card hPC hQC hPCs.2.1
    (Claims1110.isPGroup_conj n hPCs.2.1) hPCc (by rw [Claims1110.card_conj, hPCc])
  rw [gLBConj_gLBConj] at hc
  have hmem : n * c ∈ Subgroup.normalizer (P : Set X) := mem_normalizer_iff_gLBConj_eq.2 hc
  have e : n = (n * c) * c⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmem) (hCle (C.inv_mem hcC))

theorem normalizer_zpowers_le_glbCore {P : Subgroup X} {x : X} (hxP : x ∈ P) (hx5 : orderOf x = 5) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup X) : Set X) ≤ GLBCore 5 1 P := by
  refine le_sSup ⟨Subgroup.zpowers x, (Subgroup.zpowers_le).2 hxP, ?_, rfl⟩
  have hx5' : x ^ 5 = 1 := by rw [← hx5]; exact pow_orderOf_eq_one x
  exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl (Claims1116.isElemAbelian_zpowers hx5')
    (by rw [Nat.card_zpowers, hx5, pow_one])

theorem gammaK0_eq_glbCore {P : Subgroup X} (hPc : Nat.card P = 5 ^ 2) (hP : IsSylowIn 5 ⊤ P)
    (hord : ∀ x ∈ P, x ≠ 1 → orderOf x = 5)
    (hlay : ∀ x ∈ P, x ≠ 1 →
      Subgroup.center ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set X))) = ⊥ ∧
        5 ∣ Nat.card ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set X)))) :
    Claims1110b.gammaK0 P = GLBCore 5 1 P := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hne : ∃ y ∈ P, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hPb : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 hcon
    rw [hPb, Subgroup.card_bot] at hPc
    norm_num at hPc
  obtain ⟨y₀, hy₀P, hy₀1⟩ := hne
  unfold Claims1110b.gammaK0
  apply le_antisymm
  · refine sup_le ?_ (iSup_le fun x => iSup_le fun hxP => iSup_le fun hx1 => ?_)
    · refine le_sSup ⟨P, le_rfl, ?_, rfl⟩
      have hy5 := hord y₀ hy₀P hy₀1
      have hy5' : y₀ ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y₀
      exact CFSG.SectionRank.le_pRank (by norm_num) ((Subgroup.zpowers_le).2 hy₀P)
        (Claims1116.isElemAbelian_zpowers hy5') (by rw [Nat.card_zpowers, hy5, pow_one])
    · refine (Claims1110b.glaPLayer_le'' 5 _).trans ?_
      intro c hc
      refine normalizer_zpowers_le_glbCore hxP (hord x hxP hx1) ?_
      exact mem_normalizer_iff_gLBConj_eq.2 (gLBConj_zpowers_eq_of_mem_centralizer hc)
  · refine sSup_le ?_
    rintro N ⟨Q, hQP, hQk, rfl⟩
    obtain ⟨E, hEQ, -, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 5) Q
    have hQp : IsPGroup 5 ↥Q := hP.2.1.to_le hQP
    obtain ⟨i, hi⟩ := hQp.exists_card_eq
    have hdvd : Nat.card Q ∣ 5 ^ 2 := hPc ▸ Subgroup.card_dvd_of_le hQP
    have hi2 : i ≤ 2 := by
      rw [hi] at hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
    have hi1 : 1 ≤ i := by
      have h1 : 5 ^ 1 ≤ Nat.card Q := by
        calc 5 ^ 1 ≤ 5 ^ CFSG.Open.pRank 5 Q := Nat.pow_le_pow_right (by norm_num) hQk
          _ = Nat.card E := hEc.symm
          _ ≤ Nat.card Q := Subgroup.card_le_of_le hEQ
      rw [hi] at h1
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    interval_cases i
    ·
      obtain ⟨x, hxQ, hx1⟩ : ∃ x ∈ Q, x ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hQb : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).2 hcon
        rw [hQb, Subgroup.card_bot] at hi
        norm_num at hi
      have hx5 := hord x (hQP hxQ) hx1
      have hQx : Q = Subgroup.zpowers x :=
        (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hxQ)
          (by rw [hi, Nat.card_zpowers, hx5, pow_one])).symm
      rw [hQx]
      obtain ⟨hZ, h5⟩ := hlay x (hQP hxQ) hx1
      refine (normalizer_zpowers_le_layer_sup hPc hP (hQP hxQ) hx5 hZ h5).trans (sup_le ?_ le_sup_left)
      have h1 : GLAPLayer 5 (Subgroup.centralizer ({x} : Set X)) ≤
          ⨆ (y : X) (_ : y ∈ P) (_ : y ≠ 1), GLAPLayer 5 (Subgroup.centralizer ({y} : Set X)) := by
        apply le_iSup_of_le x
        apply le_iSup_of_le (hQP hxQ)
        apply le_iSup_of_le hx1
        exact le_rfl
      exact h1.trans le_sup_right
    ·
      have hQP' : Q = P := Subgroup.eq_of_le_of_card_ge hQP (by rw [hi, hPc])
      rw [hQP']
      exact le_sup_left

theorem input24_2K0_of (hF : Fi22Facts) (hI : Input14_21) (hK : CFSG.AGLEmbedding.KFactUPrimeExcFi22) :
    Claims1110b.Input24_2K0 := by
  intro X _ _ hX P hPp hPc Y hY
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, hf5, h25, -⟩ := hF X hX
  have hPc' : Nat.card P = 5 ^ (Nat.card X).factorization 5 := by rw [hPc, hf5]
  have hPsyl : IsSylowIn 5 ⊤ P :=
    Claims1110.isSylowIn_of_card le_top hPp (by rw [Subgroup.card_top]; exact hPc')
  have hord : ∀ x ∈ P, x ≠ 1 → orderOf x = 5 := by
    intro x hxP hx1
    have hd : orderOf x ∣ 5 ^ 2 := hPc ▸ Subgroup.orderOf_dvd_natCard P hxP
    obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hd
    interval_cases j
    · rw [pow_zero, orderOf_eq_one_iff] at hjx
      exact absurd hjx hx1
    · rw [hjx, pow_one]
    · exact absurd hjx (h25 x)
  have hlay : ∀ x ∈ P, x ≠ 1 →
      Subgroup.center ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set X))) = ⊥ ∧
        5 ∣ Nat.card ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set X))) := by
    intro x hxP hx1
    obtain ⟨ψ⟩ := hI X hX x (hord x hxP hx1)
    refine ⟨Claims1110e.center_eq_bot_of_isAltType_five ⟨ψ⟩, ?_⟩
    rw [Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hγ := gammaK0_eq_glbCore hPc hPsyl hord hlay
  let T : Sylow 5 X := Sylow.ofCard P hPc'
  have hTP : (T : Subgroup X) = P := Sylow.coe_ofCard P hPc'
  by_cases htop : GLBCore 5 1 P = ⊤
  · right
    rw [eq_top_iff, ← htop, ← hγ]
    exact hY
  · have h := (hK X 5 ⟨rfl, hX⟩ T (by rw [hTP]; exact htop)).1 Y (by rw [hTP, ← hγ]; exact hY)
    rw [hTP, ← hγ] at h
    exact h

end Gamma

section A5Up

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.LocalAnalysis.GLTheoremA (IsKHat IsLnEps qEps)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

theorem qEps_true_card' (q : TauCeti.PrimePower) : qEps true q.card = q.p ^ q.exponent - 1 := by
  simp [qEps, TauCeti.PrimePower.card_def]

theorem qEps_false_card' (q : TauCeti.PrimePower) : qEps false q.card = q.p ^ q.exponent + 1 := by
  simp [qEps, TauCeti.PrimePower.card_def]

theorem lieModel_twistedA' {G : Type} [Group G] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    CFSG.Models.LieModel G .PSU (r + 1) q.p q.exponent := by
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA r q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA r q
  have h := CFSG.Models.lieModel_twistedA r q hv e
  rwa [hc, hf] at h

theorem lnEps_of_five_dvd_center (hGA : CFSG.Open.GriessAllModelsStatement)
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (hZ : IsPGroup 5 (Subgroup.center K)) (hpZ : 5 ∣ Nat.card (Subgroup.center K))
    (d : TauCeti.ValidLieTypeIndex) (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (n q : ℕ) (lin : Bool), IsLnEps (K ⧸ Subgroup.center K) n q lin ∧ 5 ∣ Nat.gcd n (qEps lin q) := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK
  have key : ∀ {t : StatedLieTag} {n P f : ℕ},
      CFSG.Models.LieModel (K ⧸ Subgroup.center K) t n P f →
      (t = .PSL ∧ Nat.card (Subgroup.center K) ∣ Nat.gcd n (P ^ f - 1)) ∨
      (t = .PSU ∧ Nat.card (Subgroup.center K) ∣ Nat.gcd n (P ^ f + 1)) := fun {t n P f} hmod => by
    rcases CFSG.LocalAnalysis.GLTheoremA.kd26e_tag hp (by norm_num) ⟨k, hk⟩ hpZ t n P f
      (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_table hGA hQ' hmod
        (CFSG.LocalAnalysis.GLTheoremA.kd26e_table_ne_zero hmod.1)) with
      h | h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have h3 := (hpZ.trans h).trans (Nat.gcd_dvd_left 3 _)
      norm_num at h3
    · exfalso
      have h3 := (hpZ.trans h).trans (Nat.gcd_dvd_left 3 _)
      norm_num at h3
    all_goals norm_num at h
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    rcases key (CFSG.Models.lieModel_A r q hv e) with ⟨-, hd⟩ | ⟨h, -⟩
    · refine ⟨r + 1, q.card, true, ⟨.lie ⟨.A r q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩, ?_⟩
      rw [qEps_true_card']
      exact hpZ.trans hd
    · cases h
  | twistedA r q =>
    rcases key (lieModel_twistedA' r q hv e) with ⟨h, -⟩ | ⟨-, hd⟩
    · cases h
    · refine ⟨r + 1, q.card, false, ⟨.lie ⟨.twistedA r q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩, ?_⟩
      rw [qEps_false_card']
      exact hpZ.trans hd
  | B r q =>
    rcases CFSG.Models.lieModel_B r q hv e with hmod | hmod
    · exact absurd (key hmod) (by simp)
    · exact absurd (key hmod) (by simp)
  | C r q => exact absurd (key (CFSG.Models.lieModel_C r q hv e)) (by simp)
  | D r q => exact absurd (key (CFSG.Models.lieModel_D r q hv e)) (by simp)
  | twistedD r q => exact absurd (key (CFSG.Models.lieModel_twistedD r q hv e)) (by simp)
  | E6 q =>
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .E6) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩ e)) (by simp)
  | E7 q =>
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .E7) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E7 q, hv⟩ ⟨rfl, rfl⟩ e)) (by simp)
  | E8 q =>
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .E8) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E8 q, hv⟩ ⟨rfl, rfl⟩ e)) (by simp)
  | F4 q =>
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .F4) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩ ⟨rfl, rfl⟩ e)) (by simp)
  | G2 q =>
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .G2) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl, by rw [← TauCeti.PrimePower.card_def]; exact hq3⟩
      ⟨.G2 q, hv⟩ ⟨rfl, rfl⟩ e)) (by simp)
  | twistedE6 q =>
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .twistedE6) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩ e)) (by simp)
  | trialityD4 q =>
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .trialityD4) (p := q.p)
      (f := q.exponent) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩ e)) (by simp)
  | suzuki m =>
    have hm1 : 1 ≤ m :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .twistedB2) (p := 2)
      (f := 2 * m + 1) ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.suzuki m, hv⟩
      ⟨rfl, rfl⟩ e)) (by simp)
  | reeG2 m =>
    have hm1 : 1 ≤ m :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .twistedG2) (p := 3)
      (f := 2 * m + 1) ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeG2 m, hv⟩
      ⟨rfl, rfl⟩ e)) (by simp)
  | reeF4 m =>
    have hm1 : 1 ≤ m :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .twistedF4) (p := 2)
      (f := 2 * m + 1) ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeF4 m, hv⟩
      ⟨rfl, rfl⟩ e)) (by simp)
  | tits =>
    exact absurd (key (CFSG.Models.lieModel_of_namesTag (t := .Tits) (p := 2) (f := 1)
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, hv⟩ ⟨rfl, rfl⟩ e)) (by simp)

theorem pRank_outer_le_one_of_not_dvd {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    (h : ¬ 5 ∣ Nat.card (Outer (K ⧸ Subgroup.center K))) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (Outer K)) ≤ 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h' : ¬ 5 ∣ Nat.card (Outer K) := CFSG.AGLEmbedding.not_dvd_card_outer_of_centerQuotient h
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  obtain ⟨j, hj⟩ := (Claims1110.isPGroup_of_elemAb hE).exists_card_eq
  have hdvd : Nat.card E ∣ Nat.card (Outer K) := Subgroup.card_subgroup_dvd_card E
  rcases j with _ | j
  · rw [hj]
    norm_num
  · exact absurd ((dvd_pow_self 5 (Nat.succ_ne_zero j)).trans (hj ▸ hdvd)) h'

theorem pRank_outer_le_centerQuotient {K : Type} [Group K] [Finite K] [Group.IsPerfect K] :
    CFSG.Open.pRank 5 (⊤ : Subgroup (Outer K)) ≤
      CFSG.Open.pRank 5 (⊤ : Subgroup (Outer (K ⧸ Subgroup.center K))) :=
  (CFSG.SectionRank.pRank_le_map (by norm_num)
    (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom K)
    (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective K) ⊤).trans
    (CFSG.SectionRank.pRank_mono (by norm_num) le_top)

@[expose] def InputA5UpLn : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsKHat K → GLAPPrimeCore 5 K = ⊥ →
    ∀ (n q : ℕ) (lin : Bool), IsLnEps (K ⧸ Subgroup.center K) n q lin → 5 ∣ Nat.gcd n (qEps lin q) →
      ∀ x : MulAut K, Lemma1314.PumpupVia 5 ↥(alternatingGroup (Fin 5)) K x →
        ∃ k : ℕ, 1 ≤ k ∧ IsUpType (5 * k) 4 (K ⧸ Subgroup.center K)

@[expose] def InputOut5Lie : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (Outer S)) →
        ∃ (n q : ℕ) (lin : Bool), IsLnEps S n q lin ∧ 5 ∣ Nat.gcd n (qEps lin q)

@[expose] def InputU5kCat : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (k : ℕ), 1 ≤ k → IsUpType (5 * k) 4 S →
    IsChevSimple 2 S ∧ ¬ Claims1116.Exc5 S

@[expose] def Input30_5 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsKHat K → GLAPPrimeCore 5 K = ⊥ →
    ∀ x : MulAut K, Lemma1314.PumpupVia 5 ↥(alternatingGroup (Fin 5)) K x →
      ∀ k : ℕ, 1 ≤ k → IsUpType (5 * k) 4 (K ⧸ Subgroup.center K) →
        ∃ F : Subgroup K, F ≤ Lemma1314.fixSub x ∧ IsElemAbelian 5 F ∧
          omegaOne 5 (Subgroup.center K) ≤ F ∧
          Nat.card F = 5 ^ (5 * k - 2) * Nat.card (omegaOne 5 (Subgroup.center K))

@[expose] def InputU5Sylow : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsKHat K → GLAPPrimeCore 5 K = ⊥ →
    IsUpType 5 4 (K ⧸ Subgroup.center K) →
      ∀ P : Subgroup (MulAut K), IsPGroup 5 P →
        ∀ E : Subgroup (MulAut K), E ≤ P → IsElemAbelian 5 E → 5 ^ 3 ≤ Nat.card E →
        ∀ F : Subgroup K, IsElemAbelian 5 F → F.map (MulAut.conj : K →* MulAut K) ≤ P →
          5 ^ 3 ≤ Nat.card (F.map (MulAut.conj : K →* MulAut K)) →
          ∀ β ∈ E, ∀ f ∈ F, β f = f

theorem two_pow_dvd_ordTwistedA_four (r : ℕ) (hr : 1 ≤ r) : 2 ^ (r * (r + 1)) ∣ ordTwistedA r 4 := by
  unfold ordTwistedA
  have hg : Nat.gcd (r + 1) (4 + 1) ∣
      ∏ i ∈ Finset.Icc 2 (r + 1), ((((4 : ℕ) : ℤ)) ^ i - (-1 : ℤ) ^ i).toNat := by
    have h15 : 5 ∣ ((((4 : ℕ) : ℤ)) ^ 2 - (-1 : ℤ) ^ 2).toNat := by norm_num
    have hmem : 2 ∈ Finset.Icc 2 (r + 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
    exact (Nat.gcd_dvd_right _ _).trans (h15.trans (Finset.dvd_prod_of_mem _ hmem))
  rw [Nat.mul_div_assoc _ hg]
  have h4 : (4 : ℕ) ^ (r * (r + 1) / 2) = 2 ^ (r * (r + 1)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul,
      Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self r)]
  rw [h4]
  exact Dvd.intro _ rfl

theorem inputU5kCat_of (hO : Claims1314.Exc5Orders) : InputU5kCat := by
  intro S _ _ k hk hU
  obtain ⟨r, hr⟩ : ∃ r, 5 * k = r + 1 := ⟨5 * k - 1, by omega⟩
  rw [hr] at hU
  obtain ⟨F, _, _, hF, ⟨eS⟩⟩ := hU
  let q : TauCeti.PrimePower := ⟨2, 2, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.twistedA r q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨by omega, fun h => by omega⟩, fun h => h⟩
  obtain ⟨-, K', _, _, hK', ⟨eK⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
  have : Fintype F := Fintype.ofFinite F
  have : Fintype K' := Fintype.ofFinite K'
  have hcard : Fintype.card F = Fintype.card K' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hK']
    rfl
  let σ : F ≃+* K' := FiniteField.ringEquivOfCardEq hcard
  let e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group :=
    (eS.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv σ (r + 1) 4)).trans eK.symm
  have hchar : CFSG.Yardstones.Md0ec50421ce4.onLie (fun d => d.characteristic = 2)
      (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩) := by
    show (TauCeti.LieTypeIndex.twistedA r q).characteristic = 2
    rw [TauCeti.LieTypeIndex.characteristic_twistedA]
  refine ⟨Or.inl ⟨.lie ⟨.twistedA r q, hv⟩, hchar, ⟨e⟩⟩, ?_⟩
  rintro ⟨idx, hidx, ⟨e'⟩⟩
  have hSc : Nat.card S = ordTwistedA r 4 := by
    have h1 : Nat.card S = ordTwistedA (r + 1 - 1) (2 ^ 2) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two (n := r + 1) (f := 2)
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)).2.1 rfl
    simpa using h1
  have hS : Nat.card S = Nat.card (TauCeti.CFSGIndex.lie idx).Group := Nat.card_congr e'.toEquiv
  have h2 : 2 ^ (r * (r + 1)) ∣ Nat.card S := hSc ▸ two_pow_dvd_ordTwistedA_four r (by omega)
  have h20 : 2 ^ 20 ∣ Nat.card S :=
    (Nat.pow_dvd_pow 2 (Nat.mul_le_mul (by omega : 4 ≤ r) (by omega : 5 ≤ r + 1))).trans h2
  rcases hidx with h | h | h
  · rw [hS, (hO idx).1 h] at h20
    unfold ordTits at h20
    norm_num at h20
  · rw [hS, (hO idx).2.2 h] at h20
    unfold ordSuzuki at h20
    norm_num at h20
  · have hF4 := (hO idx).2.1 h
    rcases Nat.lt_or_ge r 9 with hr9 | hr9
    ·
      have hr4 : r = 4 := by omega
      subst hr4
      rw [hS, hF4] at hSc
      revert hSc
      rw [ordTwistedA, show Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} from rfl]
      unfold ordTwistedF4
      simp [Finset.prod_insert]
    · have h90 : 2 ^ 90 ∣ Nat.card S :=
        (Nat.pow_dvd_pow 2 (Nat.mul_le_mul hr9 (by omega : 10 ≤ r + 1))).trans h2
      rw [hS, hF4] at h90
      unfold ordTwistedF4 at h90
      norm_num at h90

theorem inputA5Up_of (hSchur : Lemma123.InputSchurAlt')
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hLn : InputA5UpLn) (hO5 : InputOut5Lie)
    (hCat : InputU5kCat) (h305 : Input30_5) (hSyl : InputU5Sylow) : Claims1110e.InputA5Up := by
  intro K _ _ hK hO x hx
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hZp : IsPGroup 5 (Subgroup.center K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i271h_center_isPGroup hp hO
  haveI hperf : Group.IsPerfect K := ⟨hK.1.1⟩
  haveI hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.1.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
  have hZbot : ∀ m : ℕ, ¬ 5 ∣ m → Nat.card (Subgroup.center K) ∣ m → Subgroup.center K = ⊥ := by
    intro m hm hd
    obtain ⟨j, hj⟩ := hZp.exists_card_eq
    rcases j with _ | j
    · exact Subgroup.eq_bot_of_card_eq _ (by rw [hj, pow_zero])
    · exact absurd ((dvd_pow_self 5 (Nat.succ_ne_zero j)).trans (hj ▸ hd)) hm
  have hZ5 : Subgroup.center K ≠ ⊥ → 5 ∣ Nat.card (Subgroup.center K) := by
    intro hne
    obtain ⟨j, hj⟩ := hZp.exists_card_eq
    rcases j with _ | j
    · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hj, pow_zero])) hne
    · rw [hj]
      exact dvd_pow_self 5 (Nat.succ_ne_zero j)
  refine ⟨fun hnU => ?_, fun k hk hU => ?_⟩
  · obtain ⟨i, ⟨e⟩⟩ := hK.2
    cases i with
    | cyclic r hr =>
      exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      apply e.injective
      rw [map_mul, map_mul]
      exact mul_comm _ _
    | alternating n hn =>
      refine ⟨?_, ?_⟩
      · rcases hSchur 5 n hp (by norm_num) K hK.1 hO ⟨e⟩ with h | ⟨h, -⟩
        · exact h
        · norm_num at h
      · refine pRank_outer_le_one_of_not_dvd fun h5 => ?_
        have h1 : 5 ∣ Nat.card (Outer (alternatingGroup (Fin n))) := by
          rw [← Nat.card_congr
            (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
          exact h5
        exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn 5 hp (by norm_num) h1
    | sporadic s =>
      refine ⟨hZbot 12 (by norm_num)
        (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.card_center_dvd_twelve hSpM hK.1 s e), ?_⟩
      refine pRank_outer_le_one_of_not_dvd fun h5 => ?_
      have h2 := hOut (K ⧸ Subgroup.center K) hsimple hnab s ⟨e⟩
      have hpos : 0 < Nat.card (Outer (K ⧸ Subgroup.center K)) := Nat.card_pos
      have h5le := Nat.le_of_dvd hpos h5
      omega
    | lie d =>
      have hU : ∀ (n q : ℕ) (lin : Bool), IsLnEps (K ⧸ Subgroup.center K) n q lin →
          5 ∣ Nat.gcd n (qEps lin q) → False := by
        intro n q lin hL hd
        obtain ⟨k, hk, hUk⟩ := hLn K hK hO n q lin hL hd x hx
        exact hnU k hk hUk
      refine ⟨?_, ?_⟩
      · by_contra hne
        obtain ⟨n, q, lin, hL, hd⟩ := lnEps_of_five_dvd_center hGA hK.1 hZp (hZ5 hne) d e
        exact hU n q lin hL hd
      · by_contra hlt
        have h2 : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (Outer (K ⧸ Subgroup.center K))) :=
          (by omega : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (Outer K))).trans pRank_outer_le_centerQuotient
        obtain ⟨n, q, lin, hL, hd⟩ := hO5 (K ⧸ Subgroup.center K) hsimple hnab d ⟨e⟩ h2
        exact hU n q lin hL hd
  · obtain ⟨hchev, hexc⟩ := hCat (K ⧸ Subgroup.center K) k hk hU
    refine ⟨hchev, hexc, h305 K hK hO x hx k hk hU, fun hk1 => ?_⟩
    rw [hk1, mul_one] at hU
    exact hSyl K hK hO hU

end A5Up

section Step6

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  (barXHom barXHom_surjective barXHom_ker_le_core mem_gLAPPrimeCoreOf_iff gLAPPrimeCoreOf_le)
open scoped commutatorElement

omit [Finite G] in
theorem isQuasisimple_of_simple_nonab {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hnab : ∃ a b : Q, a * b ≠ b * a) : CFSG.Open.IsQuasisimple Q := by
  haveI := hs
  have hZ : Subgroup.center Q = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  refine ⟨?_, ?_⟩
  · rcases hs.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hc : ⁅a, b⁆ ∈ commutator Q := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at hc
      exact commutatorElement_eq_one_iff_mul_comm.1 hc
    · exact h
  · have e : Q ⧸ Subgroup.center Q ≃* Q :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact @MulEquiv.isSimpleGroup _ _ _ _ hs e

theorem pow_card_core_eq_one {X : Subgroup G} {o : G} (ho : o ∈ GLAPPrimeCoreOf 5 X) :
    o ^ Nat.card ↥(GLAPPrimeCore 5 ↥X) = 1 := by
  obtain ⟨hoX, ho'⟩ := (mem_gLAPPrimeCoreOf_iff 5 X o).1 ho
  have hy : (⟨⟨o, hoX⟩, ho'⟩ : ↥(GLAPPrimeCore 5 ↥X)) ^ Nat.card ↥(GLAPPrimeCore 5 ↥X) = 1 :=
    pow_card_eq_one'
  have h2 := congrArg (fun z : ↥(GLAPPrimeCore 5 ↥X) => ((z : ↥X) : G)) hy
  simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h2
  exact h2

omit [Finite G] in
theorem mul_mem_of_coprime {H : Subgroup G} {k o : G} (hk : k ∈ H)
    (ho : o ∈ Subgroup.normalizer (H : Set G)) {e : ℕ} (hoe : o ^ e = 1) (hcop : Nat.Coprime 5 e)
    (hx5 : (k * o) ^ 5 = 1) : k * o ∈ H := by
  have hpow : ∀ n : ℕ, ∃ κ ∈ H, (k * o) ^ n = κ * o ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, H.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨κ, hκ, hxn⟩ := ih
      have hon : o ^ n ∈ Subgroup.normalizer (H : Set G) := Subgroup.pow_mem _ ho n
      have hconj : o ^ n * k * (o ^ n)⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hon k).1 hk
      refine ⟨κ * (o ^ n * k * (o ^ n)⁻¹), H.mul_mem hκ hconj, ?_⟩
      rw [pow_succ, hxn]
      group
  obtain ⟨κ, hκ, hxe⟩ := hpow e
  have hxe' : (k * o) ^ e ∈ H := by rw [hxe, hoe, mul_one]; exact hκ
  exact Sec13d.mem_of_pow_eq_one_of_pow_mem hcop hx5 hxe'

theorem nonempty_barOf_equiv_barX {K L : Subgroup G} (hLK : L ≤ K) (hs : IsSimpleGroup ↥(barX 5 K L))
    (h5 : 5 ∣ Nat.card ↥(barX 5 K L)) : Nonempty (barOf 5 L ≃* ↥(barX 5 K L)) := by
  set f := barXHom 5 hLK with hf
  have hker : f.ker = GLAPPrimeCore 5 ↥L := by
    refine le_antisymm (barXHom_ker_le_core 5 hLK) ?_
    haveI hn : ((GLAPPrimeCore 5 ↥L).map f).Normal :=
      (GLAPPrimeCore.normal 5 ↥L).map f (barXHom_surjective 5 hLK)
    have hcop : Nat.Coprime 5 (Nat.card ↥((GLAPPrimeCore 5 ↥L).map f)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _)
        (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥L)
    rcases hs.eq_bot_or_eq_top_of_normal ((GLAPPrimeCore 5 ↥L).map f) with hbot | htop
    · exact (Subgroup.map_eq_bot_iff _).1 hbot
    · exfalso
      rw [htop, Subgroup.card_top] at hcop
      exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).1 hcop h5
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (barXHom_surjective 5 hLK))⟩

theorem barX_derivedInf {K K₀ : Subgroup G} (hK₀ : K₀ ≤ K) :
    barX 5 K (derivedInf K₀) = derivedInf (barX 5 K K₀) := by
  apply le_antisymm
  · refine Sec12a2.le_derivedInf_of_perfect (Claims1116.bar_mono (Sec13d.derivedInf_le K₀)) ?_
    rw [← barX_commutator 5 ((Sec13d.derivedInf_le K₀).trans hK₀) ((Sec13d.derivedInf_le K₀).trans hK₀),
      Claims1245b.derivedInf_perfect]
  · classical
    set D := derivedInf (barX 5 K K₀) with hD
    have hDle : D ≤ barX 5 K K₀ := Sec13d.derivedInf_le _
    have hex : ∃ n, ∃ H : Subgroup G, H ≤ K₀ ∧ barX 5 K H = D ∧ Nat.card H = n := by
      refine ⟨_, K₀ ⊓ (D.comap (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K))).map K.subtype, inf_le_left, ?_, rfl⟩
      apply le_antisymm
      · rintro _ ⟨k, hk, rfl⟩
        obtain ⟨k', hk', hkk'⟩ := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2
        have : k' = k := Subtype.ext hkk'
        rw [← this]
        exact hk'
      · intro d hd
        obtain ⟨k, hk, rfl⟩ := hDle hd
        exact ⟨k, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hk, ⟨k, hd, rfl⟩⟩), rfl⟩
    obtain ⟨H, hHK₀, hHD, hHc⟩ := Nat.find_spec hex
    have hHperf : ⁅H, H⁆ = H := by
      have h1 : ⁅H, H⁆ ≤ H := commutator_le_of_le' le_rfl le_rfl
      have h2 : barX 5 K ⁅H, H⁆ = D := by
        rw [barX_commutator 5 (hHK₀.trans hK₀) (hHK₀.trans hK₀), hHD]
        exact Claims1245b.derivedInf_perfect _
      have h3 : Nat.find hex ≤ Nat.card ↥⁅H, H⁆ := Nat.find_min' hex ⟨⁅H, H⁆, h1.trans hHK₀, h2, rfl⟩
      exact Subgroup.eq_of_le_of_card_ge h1 (hHc ▸ h3)
    rw [← hHD]
    exact Claims1116.bar_mono (Sec12a2.le_derivedInf_of_perfect hHK₀ hHperf)

theorem exists_k1 {K Y K₀ A₀ : Subgroup G} (hK₀K : K₀ ≤ K) (hK₀Y : K₀ ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (K₀ : Set G)) (hOK₀ : GLAPPrimeCoreOf 5 K ≤ K₀) (hA₀K₀ : A₀ ≤ K₀)
    (hA₀el : IsElemAbelian 5 A₀) (hs : IsSimpleGroup ↥(derivedInf (barX 5 K K₀)))
    (hnab : ∃ x y : ↥(derivedInf (barX 5 K K₀)), x * y ≠ y * x)
    (h5 : 5 ∣ Nat.card ↥(derivedInf (barX 5 K K₀)))
    (hPD : barX 5 K A₀ ≤ derivedInf (barX 5 K K₀)) :
    ∃ K₁ : Subgroup G, GLAPComponent 5 Y K₁ ∧ K₁ ≤ K₀ ∧ A₀ ≤ K₁ ∧
      Nonempty (barOf 5 K₁ ≃* ↥(derivedInf (barX 5 K K₀))) := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  classical
  set D := derivedInf (barX 5 K K₀) with hD
  set L := derivedInf K₀ with hL
  have hLK₀ : L ≤ K₀ := Sec13d.derivedInf_le K₀
  have hLK : L ≤ K := hLK₀.trans hK₀K
  have hLY : L ≤ Y := hLK₀.trans hK₀Y
  have hLD : barX 5 K L = D := barX_derivedInf hK₀K
  have hYL : Y ≤ Subgroup.normalizer (L : Set G) := fun y hy => Sec13d.mem_normalizer_derivedInf (hYN hy)
  have hLn : (L.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).2 hYL
  have hLsn : IsSubnormal L Y := IsSubnormal.step hLY hLn (IsSubnormal.refl Y)
  have hsL : IsSimpleGroup ↥(barX 5 K L) := by rw [hLD]; exact hs
  have h5L : 5 ∣ Nat.card ↥(barX 5 K L) := by rw [hLD]; exact h5
  obtain ⟨eL⟩ := nonempty_barOf_equiv_barX hLK hsL h5L
  have eLD : barOf 5 L ≃* ↥D := eL.trans (MulEquiv.subgroupCongr hLD)
  have eY : barOf 5 L ≃* ↥(barX 5 Y L) := quotEquivBarX hp hLY hLsn
  have hqD : CFSG.Open.IsQuasisimple ↥D := isQuasisimple_of_simple_nonab hs hnab
  have hqL : CFSG.Open.IsQuasisimple ↥(barX 5 Y L) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv (eLD.symm.trans eY) hqD
  have hex : ∃ n, ∃ J : Subgroup G, IsSubnormal J Y ∧ J ≤ L ∧ barX 5 Y J = barX 5 Y L ∧ Nat.card J = n :=
    ⟨_, L, hLsn, le_rfl, rfl, rfl⟩
  obtain ⟨K₁, hK₁sn, hK₁L, hK₁b, hK₁c⟩ := Nat.find_spec hex
  have hK₁Y : K₁ ≤ Y := hK₁L.trans hLY
  have hcomp : GLAPComponent 5 Y K₁ := by
    refine ⟨hK₁Y, hK₁sn, ⟨le_top, ?_, ?_⟩, ?_⟩
    · have := isSubnormal_barX (C := Y) 5 hK₁sn
      rwa [barX_self] at this
    · show CFSG.Open.IsQuasisimple ↥(barX 5 Y K₁)
      rw [hK₁b]
      exact hqL
    · intro J hJ hJsn heq
      have hJL : J ≤ L := hJ.le.trans hK₁L
      have h1 : Nat.find hex ≤ Nat.card J := Nat.find_min' hex ⟨J, hJsn, hJL, heq.trans hK₁b, rfl⟩
      have h2 : Nat.card J < Nat.card K₁ := card_lt_of_lt' hJ
      omega
  have hA₀L : A₀ ≤ L := by
    intro x hx
    have hxK : x ∈ K := hK₀K (hA₀K₀ hx)
    obtain ⟨l, hl, hlo⟩ := exists_of_barX_le (hPD.trans hLD.ge) hx hxK
    have hoK₀ : l⁻¹ * x ∈ K₀ := hOK₀ hlo
    have hoN : l⁻¹ * x ∈ Subgroup.normalizer (L : Set G) := hYL (hK₀Y hoK₀)
    have hcop : Nat.Coprime 5 (Nat.card ↥(GLAPPrimeCore 5 ↥K)) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥K
    have e : x = l * (l⁻¹ * x) := by group
    have hx5 : (l * (l⁻¹ * x)) ^ 5 = 1 := by rw [← e]; exact hA₀el.2 x hx
    rw [e]
    exact mul_mem_of_coprime hl hoN (pow_card_core_eq_one hlo) hcop hx5
  have hA₀K₁ : A₀ ≤ K₁ := by
    intro x hx
    have hxL : x ∈ L := hA₀L hx
    obtain ⟨k, hk, hko⟩ := exists_of_barX_le (le_of_eq hK₁b.symm) hxL (hLY hxL)
    have hoN : k⁻¹ * x ∈ Subgroup.normalizer (K₁ : Set G) :=
      CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPPrimeCoreOf_le_normalizer hcomp hko
    have hcop : Nat.Coprime 5 (Nat.card ↥(GLAPPrimeCore 5 ↥Y)) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥Y
    have e : x = k * (k⁻¹ * x) := by group
    have hx5 : (k * (k⁻¹ * x)) ^ 5 = 1 := by rw [← e]; exact hA₀el.2 x hx
    rw [e]
    exact mul_mem_of_coprime hk hoN (pow_card_core_eq_one hko) hcop hx5
  have eK₁ : barOf 5 K₁ ≃* ↥D :=
    (((quotEquivBarX hp hK₁Y hK₁sn).trans (MulEquiv.subgroupCongr hK₁b)).trans eY.symm).trans eLD
  exact ⟨K₁, hcomp, hK₁L.trans hLK₀, hA₀K₁, ⟨eK₁⟩⟩

@[expose] def InputGammaD4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsFiTwentyTwo X → ∀ P : Subgroup X, IsPGroup 5 ↥P →
    Nat.card ↥P = 5 ^ 2 →
      IsSimpleGroup ↥(derivedInf (Claims1110b.gammaK0 P)) ∧
      (∃ x y : ↥(derivedInf (Claims1110b.gammaK0 P)), x * y ≠ y * x) ∧
      CFSG.Models.LieModel ↥(derivedInf (Claims1110b.gammaK0 P)) .POmegaPlus 4 2 1 ∧
      P ≤ derivedInf (Claims1110b.gammaK0 P)

@[expose] def Step6K1Claim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m p B M E A a K → Type117b p K →
    ∀ R : Subgroup G, IsSylowIn 5 M R → E ⊔ A ≤ R → IsSylowIn 5 ⊤ R →
      omegaOne 5 (centerOf R) = E ⊓ A → A = (E ⊓ A) ⊔ Subgroup.zpowers a → E ⊓ A = A ⊓ K →
      IsSylowIn 5 (Cg a) A → Cg a ≤ Subgroup.normalizer (K : Set G) →
      Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M →
      (∀ e ∈ E ⊓ A, e ≠ 1 → GLAPLayer 5 (K ⊓ Cg e) ≤ M) → GLAPPrimeCoreOf 5 K ≤ M →
      ((K ⊓ M).subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K)) =
        Claims1110b.gammaK0 (((E ⊓ A).subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K))) →
      ∀ K₁ : Subgroup G, GLAPComponent 5 (M ⊓ Cg a) K₁ → K₁ ≤ K ⊓ M → E ⊓ A ≤ K₁ →
        IsSimpleGroup (barOf 5 K₁) → (∃ x y : barOf 5 K₁, x * y ≠ y * x) →
        CFSG.Models.LieModel (barOf 5 K₁) .POmegaPlus 4 2 1 → False

theorem step6Claim_of_k1 (h119 : Lemma119Statement) (hD4 : InputGammaD4) (h6 : Step6K1Claim) :
    Claims1110b.Step6Claim := by
  intro G _ _ m p B M E A a K h hb R hR hEAR hRG hZ hAeq hA2 hASyl hCaN hN0 hKe hOK hY
  obtain ⟨rfl, hfi⟩ := hb
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  obtain ⟨hrk, -, -, -⟩ := h119 h
  have hA0el : IsElemAbelian 5 (E ⊓ A) := l1110_isElemAbelian_of_le hsc.1.2.1 inf_le_left
  have hA0c : Nat.card ↥(E ⊓ A) = 5 ^ 2 := by rw [l1110_card_eq_pow_pRank hA0el, hrk]
  have hA0K : E ⊓ A ≤ K := by rw [hA2]; exact inf_le_right
  have hEM : E ≤ M := h.pair.1.1.1.1.1
  set π : ↥K →* ↥K ⧸ GLAPPrimeCore 5 ↥K := QuotientGroup.mk' (GLAPPrimeCore 5 ↥K) with hπ
  set A₀' : Subgroup ↥K := (E ⊓ A).subgroupOf K with hA₀'
  have hOcop : Nat.Coprime 5 (Nat.card ↥(GLAPPrimeCore 5 ↥K)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥K
  have hA₀'c : Nat.card ↥A₀' = 5 ^ 2 := by
    rw [hA₀', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0K).toEquiv, hA0c]
  have hA0O : ∀ x : ↥K, x ∈ A₀' → x ∈ GLAPPrimeCore 5 ↥K → x = 1 := by
    intro x hxA hxO
    have hx5 : x ^ 5 = 1 :=
      Subtype.ext (by simpa using hA0el.2 _ (Subgroup.mem_subgroupOf.1 hxA))
    exact Claims1110.eq_one_of_dvd_coprime hOcop (orderOf_dvd_of_pow_eq_one hx5)
      (Subgroup.orderOf_dvd_natCard _ hxO)
  have hPc : Nat.card ↥(A₀'.map π) = 5 ^ 2 := by
    have hinj : Function.Injective (π.comp A₀'.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      exact Subgroup.mem_bot.2 (Subtype.ext (hA0O _ x.2 hx))
    have h1 : (π.comp A₀'.subtype).range = A₀'.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hA₀'c]
  have hPp : IsPGroup 5 ↥(A₀'.map π) := IsPGroup.of_card hPc
  obtain ⟨hs, hnab, hlie, hPD⟩ := hD4 (barOf 5 K) hfi (A₀'.map π) hPp hPc
  have hΓ : barX 5 K (K ⊓ M) = Claims1110b.gammaK0 (A₀'.map π) := hY
  rw [← hΓ] at hs hnab hlie hPD
  have h5 : 5 ∣ Nat.card ↥(derivedInf (barX 5 K (K ⊓ M))) := by
    have h1 := Subgroup.card_dvd_of_le hPD
    rw [hPc] at h1
    exact (dvd_pow_self 5 (by norm_num)).trans h1
  have hK₀Y : K ⊓ M ≤ M ⊓ Cg a := le_inf inf_le_right (inf_le_left.trans h.hK.1)
  have hYN : M ⊓ Cg a ≤ Subgroup.normalizer ((K ⊓ M : Subgroup G) : Set G) := fun y hy =>
    Sec13d.mem_normalizer_inf_of (hCaN (Subgroup.mem_inf.1 hy).2)
      (Subgroup.le_normalizer (Subgroup.mem_inf.1 hy).1)
  obtain ⟨K₁, hK₁, hK₁le, hA0K₁, ⟨e⟩⟩ := exists_k1 inf_le_left hK₀Y hYN
    (le_inf (gLAPPrimeCoreOf_le 5 K) hOK) (le_inf hA0K (inf_le_left.trans hEM)) hA0el hs hnab h5 hPD
  haveI := hs
  have hnab₁ : ∃ x y : barOf 5 K₁, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnab
    refine ⟨e.symm x, e.symm y, fun h' => hxy ?_⟩
    have h1 := congrArg e h'
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  exact h6 h ⟨rfl, hfi⟩ R hR hEAR hRG hZ hAeq hA2 hASyl hCaN hN0 hKe hOK hY K₁ hK₁ hK₁le hA0K₁
    (MulEquiv.isSimpleGroup e) hnab₁ (CFSG.Models.LieModel.of_mulEquiv e.symm hlie)

end Step6

section Main

theorem lemma1110CaseB_of_pieces (h119 : Lemma119Statement) (h111 : Prop111Statement)
    (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2) (h183 : Prop115.Input18_3Gen)
    (hSeitz : Claims1116.Input23_10) (hF : Fi22Facts) (hI : Claims1110.InputFi22OneClassFive)
    (hK : CFSG.AGLEmbedding.KFactUPrimeExcFi22) (hSchur : Lemma123.InputSchurAlt')
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hLn : InputA5UpLn) (hO5 : InputOut5Lie)
    (hCat : InputU5kCat) (h305 : Input30_5) (hSyl : InputU5Sylow) (h6 : Claims1110b.Step6Claim) :
    Lemma1110CaseB := by
  intro G _ _ m p B M E A a K h hb h1 h2 h3 hI1421
  exact Claims1110e.lemma1110CaseB_of_A5Up' h119 h111 h112 h183 hSeitz
    (inputA5Up_of hSchur hSpM hOut hGA hLn hO5 hCat h305 hSyl) hF hI (input24_2K0_of hF hI1421 hK) h6
    h hb h1 h2 h3 hI1421

theorem lemma1110CaseB_of_pieces' (h119 : Lemma119Statement) (h111 : Prop111Statement)
    (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2) (h183 : Prop115.Input18_3Gen)
    (hSeitz : Claims1116.Input23_10) (hF : Fi22Facts) (hI : Claims1110.InputFi22OneClassFive)
    (hK : CFSG.AGLEmbedding.KFactUPrimeExcFi22) (hSchur : Lemma123.InputSchurAlt')
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hO : Claims1314.Exc5Orders) (hLn : InputA5UpLn)
    (hO5 : InputOut5Lie) (h305 : Input30_5) (hSyl : InputU5Sylow) (hD4 : InputGammaD4)
    (h6 : Step6K1Claim) : Lemma1110CaseB :=
  lemma1110CaseB_of_pieces h119 h111 h112 h183 hSeitz hF hI hK hSchur hSpM hOut hGA hLn hO5
    (inputU5kCat_of hO) h305 hSyl (step6Claim_of_k1 h119 hD4 h6)

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110f

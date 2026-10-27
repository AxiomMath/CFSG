module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackage
public import CFSG.Quasithin.Background.A1bKrullSchmidt
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageFactors
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient
import CFSG.GroupTheory.IndecomposableCriteria
import CFSG.Mathlib.GroupTheory.PermCenter
import CFSG.RankThree.PartOne.FIS.CenterQuotient
import CFSG.GroupTheory.SylowInfNormal
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Sigma3Dec
import TauCeti.Algebra.Group.Subgroup.ModularLaw

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup
open CFSG.Quasithin CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Sigma3

variable {G : Type} [Group G] {L U P M : Subgroup G} {ℳ : Set (Subgroup G)}

private theorem mem_of_isSylowOf_le_normal {p : ℕ} [Fact p.Prime] {H U K : Subgroup G}
    [Finite ↥H] (hU : IsSylowOf p U H) (hUK : U ≤ K) (hKH : K ≤ H)
    (hHn : H ≤ Subgroup.normalizer (K : Set G)) {x : G} (hxH : x ∈ H)
    (hx : ∃ k : ℕ, orderOf x = p ^ k) : x ∈ K := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨Q₀, hQ₀⟩ := hU.exists_sylow_eq_subgroupOf
  let x' : ↥H := ⟨x, hxH⟩
  have hx'val : (x' : G) = x := rfl
  have hK' : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHn
  have hcard : Nat.card (Subgroup.zpowers x') ∣ p ^ k := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe x', hx'val, hk]
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card_dvd_pow hcard).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) Q₀ Q
  have hQ₀K : (Q₀ : Subgroup ↥H) ≤ K.subgroupOf H := by
    rw [hQ₀, Subgroup.subgroupOf, Subgroup.subgroupOf]
    exact Subgroup.comap_mono hUK
  have hQK : Q ≤ K.subgroupOf H := by
    rw [← hg]
    exact (Subgroup.map_mono hQ₀K).trans_eq (Subgroup.Normal.map_conj_eq (K.subgroupOf H) g)
  exact Subgroup.mem_subgroupOf.mp (hQK (hQ (Subgroup.mem_zpowers x')))

private theorem le_normalizer_pCoreOf_sup_sSup (h : IsGomiLeviPackage L U P ℳ) :
    P ≤ Subgroup.normalizer ((pCoreOf 2 P ⊔ sSup ℳ : Subgroup G) : Set G) := by
  refine Subgroup.le_normalizer_iff.mpr fun p hp n hn => ?_
  have hRmap : (pCoreOf 2 P).map (MulAut.conj p) = pCoreOf 2 P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hp)
  have hle : (pCoreOf 2 P ⊔ sSup ℳ).map (MulAut.conj p) ≤ pCoreOf 2 P ⊔ sSup ℳ := by
    rw [Subgroup.map_sup, hRmap]
    refine sup_le le_sup_left ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    calc N.map (MulAut.conj p) ≤ pCoreOf 2 P ⊔ N.map (MulAut.conj p) := le_sup_right
      _ = (pCoreOf 2 P ⊔ N).map (MulAut.conj p) := by rw [Subgroup.map_sup, hRmap]
      _ = pCoreOf 2 P ⊔ N := Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.normal N hN hp)
      _ ≤ pCoreOf 2 P ⊔ sSup ℳ := sup_le le_sup_left ((le_sSup hN).trans le_sup_right)
  exact hle (Subgroup.mem_map_of_mem (MulAut.conj p).toMonoidHom hn)

theorem IsGomiLeviPackage.sup_sSup_eq_pElementSubgroup [Finite G] (hU : IsSylowOf 2 U L)
    (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P ≤ L) (h : IsGomiLeviPackage L U P ℳ) :
    pCoreOf 2 P ⊔ sSup ℳ = pElementSubgroup 2 P := by
  have hUP : U ≤ P := (le_inf hU.le Subgroup.le_normalizer).trans hBP.le
  have hrel : U.relIndex P ∣ U.relIndex L :=
    ⟨P.relIndex L, (Subgroup.relIndex_mul_relIndex U P L hUP hPL).symm⟩
  have hUPsyl : IsSylowOf 2 U P :=
    isSylowOf_iff.mpr ⟨hUP, hU.isPGroup,
      fun hdvd => (isSylowOf_iff.mp hU).2.2 (hdvd.trans hrel)⟩
  have hKle : pCoreOf 2 P ⊔ sSup ℳ ≤ P :=
    sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 P) (sSup_le fun N hN => h.le_parabolic N hN)
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · rw [pElementSubgroup]
      intro x hx
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).exists_orderOf_eq_pow ⟨x, hx⟩
      exact Subgroup.subset_closure ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 P hx, k,
        (Subgroup.orderOf_coe ⟨x, hx⟩).trans hk⟩
    · refine sSup_le fun N hN => ?_
      have hgen := (h.pElementSubgroup_eq N hN).symm
      rw [pElementSubgroup] at hgen ⊢
      intro x hx
      refine Subgroup.closure_mono ?_ (hgen ▸ hx)
      rintro y ⟨hyN, k, hk⟩
      exact ⟨h.le_parabolic N hN hyN, k, hk⟩
  · rw [pElementSubgroup]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨hxP, k, hk⟩ := hx
    exact mem_of_isSylowOf_le_normal hUPsyl h.sylow_le hKle
      (le_normalizer_pCoreOf_sup_sSup h) hxP ⟨k, hk⟩

private theorem IsGomiLeviPackage.relIndex_inf_eq_relIndex_sup [Finite G]
    (h : IsGomiLeviPackage L U P ℳ) (hM : M ∈ ℳ) :
    (U ⊓ M).relIndex M = (pCoreOf 2 P ⊔ (U ⊓ M)).relIndex (pCoreOf 2 P ⊔ M) := by
  have hMN : M ≤ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) :=
    (h.le_parabolic M hM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hcardN : Nat.card (pCoreOf 2 P ⊔ M : Subgroup G) = Nat.card M * Nat.card (pCoreOf 2 P) := by
    have hc := CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf (H := M)
      (K := pCoreOf 2 P) hMN
    rw [inf_comm, h.inf_eq_bot M hM, Subgroup.card_bot, mul_one, sup_comm] at hc
    exact hc
  have hbotT : (U ⊓ M) ⊓ pCoreOf 2 P = ⊥ :=
    bot_unique ((inf_le_inf_right _ inf_le_right).trans (by rw [inf_comm, h.inf_eq_bot M hM]))
  have hcardT : Nat.card (pCoreOf 2 P ⊔ (U ⊓ M) : Subgroup G) =
      Nat.card (U ⊓ M : Subgroup G) * Nat.card (pCoreOf 2 P) := by
    have hc := CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := U ⊓ M) (K := pCoreOf 2 P) (inf_le_right.trans hMN)
    rw [hbotT, Subgroup.card_bot, mul_one, sup_comm] at hc
    exact hc
  have e1 : (U ⊓ M).relIndex M * Nat.card (U ⊓ M : Subgroup G) = Nat.card M := by
    simpa [inf_eq_left.mpr inf_le_right] using Subgroup.relIndex_mul_card (H := U ⊓ M) (K := M)
  have e2 : (pCoreOf 2 P ⊔ (U ⊓ M)).relIndex (pCoreOf 2 P ⊔ M) *
      Nat.card (pCoreOf 2 P ⊔ (U ⊓ M) : Subgroup G) = Nat.card (pCoreOf 2 P ⊔ M : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card (H := pCoreOf 2 P ⊔ (U ⊓ M)) (K := pCoreOf 2 P ⊔ M)
    have hle : pCoreOf 2 P ⊔ (U ⊓ M) ≤ pCoreOf 2 P ⊔ M :=
      sup_le le_sup_left (inf_le_right.trans le_sup_right)
    rwa [inf_eq_left.mpr hle] at h
  have hpos : 0 < Nat.card (U ⊓ M : Subgroup G) * Nat.card (pCoreOf 2 P) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (U ⊓ M).relIndex M * (Nat.card (U ⊓ M : Subgroup G) * Nat.card (pCoreOf 2 P))
      = ((U ⊓ M).relIndex M * Nat.card (U ⊓ M : Subgroup G)) * Nat.card (pCoreOf 2 P) := by ring
    _ = Nat.card (M : Subgroup G) * Nat.card (pCoreOf 2 P) := by rw [e1]
    _ = Nat.card (pCoreOf 2 P ⊔ M : Subgroup G) := hcardN.symm
    _ = (pCoreOf 2 P ⊔ (U ⊓ M)).relIndex (pCoreOf 2 P ⊔ M) *
          Nat.card (pCoreOf 2 P ⊔ (U ⊓ M) : Subgroup G) := e2.symm
    _ = (pCoreOf 2 P ⊔ (U ⊓ M)).relIndex (pCoreOf 2 P ⊔ M) *
          (Nat.card (U ⊓ M : Subgroup G) * Nat.card (pCoreOf 2 P)) := by rw [hcardT]

theorem IsGomiLeviPackage.isSylowOf_inf [Finite G] (hU : IsSylowOf 2 U L)
    (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P ≤ L) (h : IsGomiLeviPackage L U P ℳ)
    (hM : M ∈ ℳ) : IsSylowOf 2 (U ⊓ M) M := by
  have hUP : U ≤ P := (le_inf hU.le Subgroup.le_normalizer).trans hBP.le
  have hrel : U.relIndex P ∣ U.relIndex L :=
    ⟨P.relIndex L, (Subgroup.relIndex_mul_relIndex U P L hUP hPL).symm⟩
  have hUPsyl : IsSylowOf 2 U P :=
    isSylowOf_iff.mpr ⟨hUP, hU.isPGroup,
      fun hdvd => (isSylowOf_iff.mp hU).2.2 (hdvd.trans hrel)⟩
  have hRU : pCoreOf 2 P ≤ U := pCoreOf_le_of_isSylowOf_of_le hU hUP hPL
  have hNX : pCoreOf 2 P ⊔ M ≤ P :=
    sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 P) (h.le_parabolic M hM)
  have hTsyl : IsSylowOf 2 ((pCoreOf 2 P ⊔ M) ⊓ U) (pCoreOf 2 P ⊔ M) :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp
      (isSylowTwoOf_inf_of_normal
        (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hUPsyl) hNX
        (h.normal M hM))
  have hMN : M ≤ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) :=
    (h.le_parabolic M hM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hded : (pCoreOf 2 P ⊔ M) ⊓ U = pCoreOf 2 P ⊔ (U ⊓ M) := by
    rw [sup_comm (pCoreOf 2 P) (U ⊓ M), inf_comm (pCoreOf 2 P ⊔ M) U,
      sup_comm (pCoreOf 2 P) M]
    exact (Subgroup.inf_sup_assoc_of_le (H := M) (K := U) (N := pCoreOf 2 P) hMN hRU).symm
  rw [hded] at hTsyl
  refine isSylowOf_iff.mpr ⟨inf_le_right, hU.isPGroup.to_inf_left, ?_⟩
  rw [h.relIndex_inf_eq_relIndex_sup hM]
  exact (isSylowOf_iff.mp hTsyl).2.2

private theorem IsGomiLeviPackage.closure_pow_eq_top (h : IsGomiLeviPackage L U P ℳ) (hM : M ∈ ℳ) :
    Subgroup.closure {y : ↥M | ∃ k : ℕ, orderOf y = 2 ^ k} = ⊤ := by
  have hmap : (Subgroup.closure {y : ↥M | ∃ k : ℕ, orderOf y = 2 ^ k}).map M.subtype
      = pElementSubgroup 2 M := by
    rw [pElementSubgroup, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      exact ⟨y.2, k, (Subgroup.orderOf_coe y).trans hk⟩
    · rintro ⟨hxM, k, hk⟩
      exact ⟨⟨x, hxM⟩, ⟨k, by rwa [← Subgroup.orderOf_coe]⟩, rfl⟩
  apply Subgroup.map_injective M.subtype_injective
  rw [hmap, h.pElementSubgroup_eq M hM]
  refine le_antisymm ?_ (Subgroup.map_subtype_le _)
  intro x hx
  simpa using Subgroup.mem_map_of_mem M.subtype
    (show (⟨x, hx⟩ : ↥M) ∈ (⊤ : Subgroup ↥M) from trivial)

theorem IsGomiLeviPackage.center_quotient_center_eq_bot [Finite G]
    (h : IsGomiLeviPackage L U P ℳ) (hM : M ∈ ℳ) : center (↥M ⧸ center ↥M) = ⊥ :=
  center_quotient_center_eq_bot_of_coprime (p := 2) (h.coprime_card_center hM)
    (h.closure_pow_eq_top hM)

private theorem IsGomiLeviPackage.closure_pow_quotient_center_eq_top [Finite G]
    (h : IsGomiLeviPackage L U P ℳ) (hM : M ∈ ℳ) :
    Subgroup.closure {y : ↥M ⧸ center ↥M | ∃ k : ℕ, orderOf y = 2 ^ k} = ⊤ := by
  let π : ↥M →* (↥M ⧸ center ↥M) := QuotientGroup.mk' (center ↥M)
  have htop : Subgroup.closure (π '' {y : ↥M | ∃ k : ℕ, orderOf y = 2 ^ k}) = ⊤ := by
    rw [← MonoidHom.map_closure, h.closure_pow_eq_top hM,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
  refine le_antisymm le_top (htop ▸ Subgroup.closure_mono ?_)
  rintro z ⟨y, ⟨k, hk⟩, rfl⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hk ▸ orderOf_map_dvd π y)
  exact ⟨j, hj⟩

private theorem isCoatom_subgroupOf_of_covBy {C M : Subgroup G} (h : C ⋖ M) :
    IsCoatom (C.subgroupOf M) := by
  have htop : (⊤ : Subgroup ↥M).map M.subtype = M := by
    refine le_antisymm (Subgroup.map_subtype_le _) ?_
    intro x hx
    simpa using Subgroup.mem_map_of_mem M.subtype
      (show (⟨x, hx⟩ : ↥M) ∈ (⊤ : Subgroup ↥M) from trivial)
  refine SetLike.isCoatom_iff.mpr ⟨?_, ?_⟩
  · intro hEq
    apply h.ne
    have hcon := congrArg (Subgroup.map M.subtype) hEq
    rwa [Subgroup.map_subgroupOf_eq_of_le h.le, htop] at hcon
  · intro H g hCH hgK hgH
    have h1 : C ≤ H.map M.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.le]
      exact Subgroup.map_mono hCH
    have h2 : H.map M.subtype ≤ M := Subgroup.map_subtype_le H
    rcases h.eq_or_eq h1 h2 with hE | hE
    · exact absurd (by
        rw [Subgroup.mem_subgroupOf]
        exact hE ▸ Subgroup.mem_map_of_mem M.subtype hgH) hgK
    · apply Subgroup.map_injective M.subtype_injective
      rw [hE, htop]

private theorem IsGomiLeviPackage.not_le_normalizer_inf [Finite G]
    (h : IsGomiLeviPackage L U P ℳ) (hU : IsSylowOf 2 U L)
    (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P ≤ L) (hM : M ∈ ℳ) :
    ¬ M ≤ Subgroup.normalizer ((U ⊓ M : Subgroup G) : Set G) := by
  intro hMle
  have hSinf : IsSylowOf 2 (U ⊓ M) M := IsGomiLeviPackage.isSylowOf_inf hU hBP hPL h hM
  have hnorm : ((U ⊓ M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hMle
  have hbot : pCoreOf 2 M = ⊥ := by
    show (pCore 2 ↥M).map M.subtype = ⊥
    rw [h.pCore_eq_bot hM, Subgroup.map_bot]
  have hle : U ⊓ M ≤ pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right hnorm hSinf.isPGroup
  rw [hbot, le_bot_iff] at hle
  have hodd : ¬ 2 ∣ Nat.card ↥M := by
    have h2 := (isSylowOf_iff.mp hSinf).2.2
    rwa [hle, Subgroup.relIndex_bot_left] at h2
  have hMb : M = ⊥ := by
    rw [← h.pElementSubgroup_eq M hM, pElementSubgroup]
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) bot_le
    intro y hy
    obtain ⟨hyM, k, hk⟩ := hy
    have hndvd : ¬ 2 ∣ orderOf y := fun h2 => hodd (h2.trans (Subgroup.orderOf_dvd_natCard M hyM))
    have hk0 : k = 0 := by
      by_contra hk0
      exact hndvd (hk ▸ dvd_pow_self 2 hk0)
    change y ∈ (⊥ : Subgroup G)
    rw [Subgroup.mem_bot, ← orderOf_eq_one_iff, hk, hk0, pow_zero]
  exact h.ne_bot hM hMb

private theorem IsGomiLeviPackage.normalizer_subgroupOf_inf_eq [Finite G]
    (h : IsGomiLeviPackage L U P ℳ) (hU : IsSylowOf 2 U L)
    (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P ≤ L) (hM : M ∈ ℳ)
    (hCov : L ⊓ normalizer (U : Set G) ⊓ M ⋖ M) :
    normalizer (((U ⊓ M).subgroupOf M) : Set ↥M) =
      (L ⊓ normalizer (U : Set G) ⊓ M).subgroupOf M := by
  rw [← Subgroup.subgroupOf_normalizer_eq (H := U ⊓ M) (N := M) inf_le_right]
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hCov.le]
  have hCN : L ⊓ normalizer (U : Set G) ⊓ M ≤ normalizer (U ⊓ M) ⊓ M := by
    refine le_inf ?_ inf_le_right
    exact (le_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hNM : normalizer (U ⊓ M) ⊓ M ≠ M := by
    intro hEq
    have hMle : M ≤ normalizer (U ⊓ M) := hEq.symm.le.trans inf_le_left
    exact IsGomiLeviPackage.not_le_normalizer_inf h hU hBP hPL hM hMle
  exact (hCov.eq_or_eq hCN inf_le_right).resolve_right hNM

private theorem IsGomiLeviPackage.isIndecomposableGroup_of_covBy [Finite G]
    (h : IsGomiLeviPackage L U P ℳ) (hU : IsSylowOf 2 U L)
    (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P ≤ L) (hM : M ∈ ℳ)
    (hCov : L ⊓ normalizer (U : Set G) ⊓ M ⋖ M) :
    IsIndecomposableGroup (↥M ⧸ center ↥M) := by
  have hSinf : IsSylowOf 2 (U ⊓ M) M := IsGomiLeviPackage.isSylowOf_inf hU hBP hPL h hM
  have hnorm := h.normalizer_subgroupOf_inf_eq hU hBP hPL hM hCov
  have hcoatS : IsCoatom (normalizer (((U ⊓ M).subgroupOf M) : Set ↥M)) :=
    hnorm.symm ▸ isCoatom_subgroupOf_of_covBy hCov
  obtain ⟨Q₀, hQ₀⟩ := hSinf.exists_sylow_eq_subgroupOf
  let π : ↥M →* (↥M ⧸ center ↥M) := QuotientGroup.mk' (center ↥M)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hS : IsPGroup 2 ((U ⊓ M).subgroupOf M) := hSinf.isPGroup.comap_subtype (K := M)
  have hmapn := map_mk'_normalizer_eq (center ↥M) le_rfl (h.coprime_card_center hM) hS
  set T : Sylow 2 (↥M ⧸ center ↥M) := Q₀.mapSurjective (f := π) hπ with hT
  have hTcoe : (T : Subgroup (↥M ⧸ center ↥M)) = ((U ⊓ M).subgroupOf M).map π := by
    rw [hT, Sylow.coe_mapSurjective, hQ₀]
  have hker : π.ker ≤ normalizer (((U ⊓ M).subgroupOf M) : Set ↥M) := by
    rw [show π.ker = center ↥M from QuotientGroup.ker_mk' _]
    exact Subgroup.center_le_normalizer _
  have hcomap : (normalizer ((T : Subgroup (↥M ⧸ center ↥M)))).comap π
      = normalizer (((U ⊓ M).subgroupOf M) : Set ↥M) := by
    rw [hTcoe, ← hmapn]
    exact Subgroup.comap_map_eq_self hker
  have gi : GaloisInsertion (Subgroup.map π) (Subgroup.comap π) :=
    { choice := fun H _ => Subgroup.map π H
      gc := Subgroup.gc_map_comap π
      le_l_u := fun H => (Subgroup.map_comap_eq_self_of_surjective hπ H).ge
      choice_eq := fun _ _ => rfl }
  have hcoatT : IsCoatom (normalizer ((T : Subgroup (↥M ⧸ center ↥M)) : Set _)) :=
    gi.isCoatom_of_image (hcomap ▸ hcoatS)
  refine isIndecomposableGroup_of_isCoatom_normalizer ?_ ?_ T hcoatT
  · exact CFSG.RankThree.PartOne.FIS.pCore_quotient_center_eq_bot 2
      (by rw [h.pCore_eq_bot hM]; exact bot_le)
  · exact h.closure_pow_quotient_center_eq_top hM

theorem IsGomiLeviPackage.isIndecomposableGroup [Finite G] (hU : IsSylowOf 2 U L)
    (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P ≤ L) (h : IsGomiLeviPackage L U P ℳ)
    (hM : M ∈ ℳ) : IsIndecomposableGroup (↥M ⧸ center ↥M) := by
  rcases h.factor M hM with hChev | hS6 | hCov
  · exact @isIndecomposableGroup_of_isSimpleGroup (↥M ⧸ center ↥M) _ hChev.isSimpleGroup
  · obtain ⟨e⟩ := hS6
    have hZmap : (center ↥M).map e.toMonoidHom = center (Equiv.Perm (Fin 6)) :=
      Subgroup.map_center_eq e
    have hZ : center ↥M = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := center ↥M) (f := e.toMonoidHom)
        e.injective).mp
        (by rw [hZmap, center_perm_eq_bot_of_three_le_card (α := Fin 6) (by norm_num)])
    exact Sigma3Dec.isIndecomposableGroup_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e))
      (isIndecomposableGroup_perm (α := Fin 6) (by norm_num))
  · exact h.isIndecomposableGroup_of_covBy hU hBP hPL hM hCov

end CFSG.GroupTheory

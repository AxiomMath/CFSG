module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs27
public import CFSG.HardMathSupport.Dickson.I271.Support.ChevInner
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

@[expose] def InputI2711ChevPOuter : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ (L B : Subgroup X),
    CFSG.IsKGroup ↥L → CFSG.Open.IsQuasisimple ↥L → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (L : Set X) →
    (∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B) →
    4 ≤ CFSG.Open.pRank p B →
    (¬ ∃ n : ℕ, IsAltType n (↥L ⧸ Subgroup.center ↥L)) →
    (¬ ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (↥L ⧸ Subgroup.center ↥L)) →
    (∃ A : Subgroup (MulAut ↥L), IsElemAbelian p A ∧ 3 ≤ CFSG.Open.pRank p A) →
    CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X)) ≤ 1 →
    (∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧
        idx.1.characteristic = p) →
    ∀ J0 : Subgroup X,
      CFSG.Open.IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)) →
      ((∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) J0) ∨ (∃ k : ℕ, IsAltType (k * p + 2) J0) ∨
        (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
          Nonempty (↥J0 ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup
            (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
        (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) J0 ∧
          HasFixedPointFreeOrder ε n p)) →
      ¬ (p = 3 ∧ IsAltType 5 J0) →
    ∀ E : Subgroup X, E ≤ B → B ⊓ Subgroup.centralizer (L : Set X) ≤ E →
      Nat.card B ≤ p ^ 2 * Nat.card E →
      GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ →
      2 ≤ CFSG.Open.pRank p E →
      GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ →
      (∀ e ∈ E, GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥) →
      (∀ e ∈ E, ∀ k ∈ L, k⁻¹ * e ∈ Subgroup.centralizer (L : Set X) →
        e ∈ Subgroup.centralizer (L : Set X)) →
      Nat.card E ≤ p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) →
      L = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)

@[expose] def InputI2711SporInner : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ (L B : Subgroup X),
    CFSG.IsKGroup ↥L → CFSG.Open.IsQuasisimple ↥L → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (L : Set X) →
    (∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B) →
    4 ≤ CFSG.Open.pRank p B →
    (¬ ∃ n : ℕ, IsAltType n (↥L ⧸ Subgroup.center ↥L)) →
    (¬ ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (↥L ⧸ Subgroup.center ↥L)) →
    (∃ A : Subgroup (MulAut ↥L), IsElemAbelian p A ∧ 3 ≤ CFSG.Open.pRank p A) →
    CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X)) ≤ 1 →
    (∃ name : TauCeti.SporadicName, IsSporType name (↥L ⧸ Subgroup.center ↥L)) →
    (∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) →
    ∀ J0 : Subgroup X,
      CFSG.Open.IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)) →
      ((∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) J0) ∨ (∃ k : ℕ, IsAltType (k * p + 2) J0) ∨
        (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
          Nonempty (↥J0 ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup
            (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
        (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) J0 ∧
          HasFixedPointFreeOrder ε n p)) →
      ¬ (p = 3 ∧ IsAltType 5 J0) →
    ∀ E : Subgroup X, E ≤ B → B ⊓ Subgroup.centralizer (L : Set X) ≤ E →
      Nat.card B ≤ p ^ 2 * Nat.card E →
      GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ →
      2 ≤ CFSG.Open.pRank p E →
      GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ →
      (∀ e ∈ E, GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥) →
      L = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)

section Catalogue

theorem isChevSimple_of_lie {S : Type} [Group S] {p : ℕ}
    (h : ∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧ idx.1.characteristic = p) :
    IsChevSimple p S := by
  obtain ⟨idx, ⟨e⟩, hch⟩ := h
  exact Or.inl ⟨TauCeti.CFSGIndex.lie idx, hch, ⟨e⟩⟩

theorem lie_or_spor {L : Type} [Group L] {p : ℕ} (hLK : CFSG.IsKGroup L)
    (hLq : CFSG.Open.IsQuasisimple L)
    (hnA : ¬ ∃ n : ℕ, IsAltType n (L ⧸ Subgroup.center L))
    (hnC : ¬ ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (L ⧸ Subgroup.center L)) :
    (∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty ((L ⧸ Subgroup.center L) ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧
        idx.1.characteristic = p) ∨
      ∃ name : TauCeti.SporadicName, IsSporType name (L ⧸ Subgroup.center L) := by
  have hK : CFSG.Open.IsKGroup L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hLq.2
  have hnab := CFSG.HardMathSupport.Solomon.Coordinator.exists_noncomm_of_isQuasisimple hLq
  have hcat : CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L) :=
    CFSG.Open.IsKGroup.isCatalogGroup_of_surjective hK ⊤ hnab
      ((QuotientGroup.mk' (Subgroup.center L)).comp (⊤ : Subgroup L).subtype)
      (fun y => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) y
        exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  rcases Lemma1315b.catalog_cases hnab hcat with hA | ⟨idx, ⟨e⟩⟩ | hS
  · exact absurd hA hnA
  · left
    refine ⟨idx, ⟨e⟩, ?_⟩
    have hq : idx.1.characteristic.Prime := TauCeti.LieTypeIndex.characteristic_prime idx.1
    by_contra hqp
    exact hnC ⟨_, hq, hqp, isChevSimple_of_lie ⟨idx, ⟨e⟩, rfl⟩⟩
  · exact Or.inr hS

end Catalogue

section FirstParagraph

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem exists_glaPComponent_of_ne_bot {Y : Subgroup X} (h : GLAPLayer p Y ≠ ⊥) :
    ∃ J : Subgroup X, GLAPComponent p Y J := by
  by_contra hne
  push Not at hne
  exact h (sSup_eq_bot.2 fun J hJ => absurd hJ (hne J))

theorem glaPLayer_ne_bot_of_glaPComponent {Y J : Subgroup X} (hJ : GLAPComponent p Y J) :
    GLAPLayer p Y ≠ ⊥ := by
  intro h
  have hle : J ≤ GLAPLayer p Y := le_sSup hJ
  rw [h, le_bot_iff] at hle
  exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hJ hle

theorem two_le_pRank_of_card_le (hp : p.Prime) {B E : Subgroup X} (hB : IsElemAbelian p B)
    (hEB : E ≤ B) (hB4 : 4 ≤ CFSG.Open.pRank p B) (hcard : Nat.card B ≤ p ^ 2 * Nat.card E) :
    2 ≤ CFSG.Open.pRank p E := by
  have hEel : IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hB hEB
  have h1 := Inputs27.card_eq_pow_pRank hp hB
  have h2 := Inputs27.card_eq_pow_pRank hp hEel
  rw [h1, h2, ← pow_add] at hcard
  have h3 := (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  omega

theorem inf_centralizer_le_gammaTwoIn {B E L : Subgroup X} (hEB : E ≤ B)
    (hE2 : 2 ≤ CFSG.Open.pRank p E) :
    L ⊓ Subgroup.centralizer (E : Set X) ≤ Lemma138.gammaTwoIn p B L := by
  intro x hx
  unfold Lemma138.gammaTwoIn
  exact Subgroup.mem_iSup_of_mem E (Subgroup.mem_iSup_of_mem hEB (Subgroup.mem_iSup_of_mem hE2
    ⟨(Subgroup.mem_inf.1 hx).1,
      Subgroup.centralizer_le_normalizer (E : Set X) (Subgroup.mem_inf.1 hx).2⟩))

theorem glaPComponent_of_J0 (hp : p.Prime) {B E L J0 I : Subgroup X} (hEB : E ≤ B)
    (hE2 : 2 ≤ CFSG.Open.pRank p E)
    (hJ0 : CFSG.Open.IsComponentOf J0 (Lemma138.gammaTwoIn p B L))
    (hI : GLAPComponent p (J0 ⊓ Subgroup.centralizer (E : Set X)) I) :
    GLAPComponent p (L ⊓ Subgroup.centralizer (E : Set X)) I := by
  have hsn : CFSG.Open.IsSubnormal (J0 ⊓ Subgroup.centralizer (E : Set X))
      (Lemma138.gammaTwoIn p B L ⊓ Subgroup.centralizer (E : Set X)) :=
    hJ0.2.1.inf (Subgroup.centralizer (E : Set X))
  have heq : Lemma138.gammaTwoIn p B L ⊓ Subgroup.centralizer (E : Set X) =
      L ⊓ Subgroup.centralizer (E : Set X) :=
    le_antisymm (inf_le_inf_right _ (Inputs27.gammaTwoIn_le B L))
      (le_inf (inf_centralizer_le_gammaTwoIn hEB hE2) inf_le_right)
  rw [heq] at hsn
  exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_of_isSubnormal' hp hsn hI

theorem glaPLayer_ne_bot_of_J0 (hp : p.Prime) {B E L J0 : Subgroup X} (hEB : E ≤ B)
    (hE2 : 2 ≤ CFSG.Open.pRank p E)
    (hJ0 : CFSG.Open.IsComponentOf J0 (Lemma138.gammaTwoIn p B L))
    (hl : GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥) :
    GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ := by
  obtain ⟨I, hI⟩ := exists_glaPComponent_of_ne_bot hl
  exact glaPLayer_ne_bot_of_glaPComponent (glaPComponent_of_J0 hp hEB hE2 hJ0 hI)

theorem glaPLayer_singleton_ne_bot (hp : p.Prime) (hLB : CFSG.LocalAnalysis.GLTheoremA.LBalanceAt X p)
    {E L : Subgroup X} (hLK : CFSG.Open.IsKGroup ↥L) (hE : IsElemAbelian p E)
    (hEN : E ≤ Subgroup.normalizer (L : Set X))
    (hl : GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥) {e : X} (he : e ∈ E) :
    GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥ := by
  obtain ⟨I, hI⟩ := exists_glaPComponent_of_ne_bot hl
  have hle := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_le_glaPLayer_centralizer_singleton hp hLB
    hLK hE hEN he hI
  intro h
  rw [h, le_bot_iff] at hle
  exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hI hle

end FirstParagraph

section Chev

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem conj_eq_of_inner {L : Subgroup X} {e k : X}
    (hc : k⁻¹ * e ∈ Subgroup.centralizer (L : Set X)) {y : X} (hy : y ∈ L) :
    e * y * e⁻¹ = k * y * k⁻¹ := by
  have hcy : (k⁻¹ * e) * y = y * (k⁻¹ * e) :=
    (Subgroup.mem_centralizer_iff.1 hc y hy).symm
  calc e * y * e⁻¹ = k * ((k⁻¹ * e) * y) * (k⁻¹ * e)⁻¹ * k⁻¹ := by group
    _ = k * (y * (k⁻¹ * e)) * (k⁻¹ * e)⁻¹ * k⁻¹ := by rw [hcy]
    _ = k * y * k⁻¹ := by group

theorem not_mem_center_of_inner {L : Subgroup X} {e k : X} (hk : k ∈ L)
    (hc : k⁻¹ * e ∈ Subgroup.centralizer (L : Set X)) (he : e ∉ Subgroup.centralizer (L : Set X)) :
    (⟨k, hk⟩ : ↥L) ∉ Subgroup.center ↥L := by
  intro hz
  apply he
  have hkC : k ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := Subgroup.mem_center_iff.1 hz ⟨y, hy⟩
    exact congrArg Subtype.val h1
  have e1 : e = k * (k⁻¹ * e) := by group
  rw [e1]
  exact Subgroup.mul_mem _ hkC hc

theorem pow_mem_center_of_inner {L : Subgroup X} {e k : X} (hep : e ^ p = 1) (hk : k ∈ L)
    (hc : k⁻¹ * e ∈ Subgroup.centralizer (L : Set X)) :
    (⟨k, hk⟩ : ↥L) ^ p ∈ Subgroup.center ↥L := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hconj : ∀ n : ℕ, e ^ n * (y : X) * (e ^ n)⁻¹ = k ^ n * (y : X) * (k ^ n)⁻¹ := by
    intro n
    induction n generalizing y with
    | zero => simp
    | succ n ih =>
      have hyn : e ^ n * (y : X) * (e ^ n)⁻¹ ∈ L := by
        rw [ih y]
        exact L.mul_mem (L.mul_mem (L.pow_mem hk n) y.2) (L.inv_mem (L.pow_mem hk n))
      calc e ^ (n + 1) * (y : X) * (e ^ (n + 1))⁻¹
          = e * (e ^ n * (y : X) * (e ^ n)⁻¹) * e⁻¹ := by group
        _ = k * (e ^ n * (y : X) * (e ^ n)⁻¹) * k⁻¹ := conj_eq_of_inner hc hyn
        _ = k * (k ^ n * (y : X) * (k ^ n)⁻¹) * k⁻¹ := by rw [ih y]
        _ = k ^ (n + 1) * (y : X) * (k ^ (n + 1))⁻¹ := by group
  have h1 := hconj p
  rw [hep] at h1
  simp only [one_mul, inv_one, mul_one] at h1
  show (y : X) * (k ^ p) = (k ^ p) * (y : X)
  exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm

theorem mem_centralizer_of_inner (hp : p.Prime) (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner p)
    {L : Subgroup X} (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hChev : IsChevSimple p (↥L ⧸ Subgroup.center ↥L)) {e k : X} (hep : e ^ p = 1) (hk : k ∈ L)
    (hc : k⁻¹ * e ∈ Subgroup.centralizer (L : Set X))
    (hl : GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥) :
    e ∈ Subgroup.centralizer (L : Set X) := by
  by_contra he
  obtain ⟨J, hJ⟩ := exists_glaPComponent_of_ne_bot hl
  exact CFSG.HardMathSupport.Dickson.I271.not_glaPComponent_of_inner hp hKD hLq hChev hk hc
    (not_mem_center_of_inner hk hc he) (pow_mem_center_of_inner hep hk hc) hJ

end Chev

section Inner

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem exists_inner_of_quot {L : Subgroup X} (hLq : CFSG.Open.IsQuasisimple ↥L) {b : X}
    (hbN : b ∈ Subgroup.normalizer (L : Set X))
    (h : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L
      (L.normalizerMonoidHom ⟨b, hbN⟩) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (↥L ⧸ Subgroup.center ↥L)) :
    ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X) := by
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLq.1
  set x : MulAut ↥L := L.normalizerMonoidHom ⟨b, hbN⟩ with hx
  have hin : x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
    refine CFSG.LocalAnalysis.GLTheoremA.chev_mem_inner_of_central_surjective
      (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _).le (fun q => ?_) h
    exact (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk x q).symm
  obtain ⟨l, hl⟩ := hin
  refine ⟨(l : X), l.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨y, hy⟩ : ↥L) : X)) hl
  simp only [MulAut.conj_apply] at h1
  have h2 : ((x ⟨y, hy⟩ : ↥L) : X) = b * y * b⁻¹ := rfl
  rw [h2] at h1
  push_cast at h1
  calc y * ((l : X)⁻¹ * b) = (l : X)⁻¹ * ((l : X) * y * (l : X)⁻¹) * b := by group
    _ = (l : X)⁻¹ * (b * y * b⁻¹) * b := by rw [h1]
    _ = (l : X)⁻¹ * b * y := by group

theorem normalizerMonoidHom_pow_eq_one {L : Subgroup X} {b : X}
    (hbN : b ∈ Subgroup.normalizer (L : Set X)) (hbp : b ^ p = 1) :
    L.normalizerMonoidHom ⟨b, hbN⟩ ^ p = 1 := by
  rw [← map_pow]
  have : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set X))) ^ p = 1 :=
    Subtype.ext (by simpa using hbp)
  rw [this, map_one]

theorem exists_inner_of_spor (hp : p.Prime) (hp2 : p ≠ 2)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    {L : Subgroup X} (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hS : ∃ name : TauCeti.SporadicName, IsSporType name (↥L ⧸ Subgroup.center ↥L))
    {b : X} (hbN : b ∈ Subgroup.normalizer (L : Set X)) (hbp : b ^ p = 1) :
    ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X) := by
  obtain ⟨name, ⟨f⟩⟩ := hS
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2
  have hnab := CFSG.HardMathSupport.Solomon.Coordinator.exists_noncomm_of_isQuasisimple hLq
  have hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout := hOut (↥L ⧸ Subgroup.center ↥L) inferInstance hnab name ⟨f⟩
  set ψ := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L
    (L.normalizerMonoidHom ⟨b, hbN⟩) with hψ
  have hψp : ψ ^ p = 1 := by rw [hψ, ← map_pow, normalizerMonoidHom_pow_eq_one hbN hbp, map_one]
  obtain ⟨s, hs, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hcen hout ψ hψp
  exact exists_inner_of_quot hLq hbN ⟨s, hs⟩

theorem card_le_of_outer (hp : p.Prime) (hp2 : p ≠ 2)
    (hLO : CFSG.HardMathSupport.Timmesfeld.Coordinator.LieOuterRank)
    {L B E : Subgroup X} (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hLie : ∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧
        idx.1.characteristic = p)
    (hE : IsElemAbelian p E) (hEN : E ≤ Subgroup.normalizer (L : Set X)) (hEB : E ≤ B)
    (hBC : B ⊓ Subgroup.centralizer (L : Set X) ≤ E)
    (hout : ∀ e ∈ E, ∀ k ∈ L, k⁻¹ * e ∈ Subgroup.centralizer (L : Set X) →
      e ∈ Subgroup.centralizer (L : Set X)) :
    Nat.card E ≤ p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨idx, ⟨f⟩, -⟩ := hLie
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLq.1
  have hnab := CFSG.HardMathSupport.Solomon.Coordinator.exists_noncomm_of_isQuasisimple hLq
  let ψ : ↥E →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L).comp
      (L.normalizerMonoidHom.comp (Subgroup.inclusion hEN))
  have hψe : ∀ e : ↥E, ψ e = CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L
      (L.normalizerMonoidHom ⟨(e : X), hEN e.2⟩) := fun e => rfl
  have hker : ∀ e : ↥E, ψ e = 1 ↔ (e : X) ∈ Subgroup.centralizer (L : Set X) := by
    intro e
    rw [hψe]
    constructor
    · intro h1
      have h2 : L.normalizerMonoidHom ⟨(e : X), hEN e.2⟩ = 1 :=
        CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥L
          (h1.trans (map_one _).symm)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h3 := congrArg (fun φ : MulAut ↥L => ((φ ⟨y, hy⟩ : ↥L) : X)) h2
      have h4 : ((L.normalizerMonoidHom ⟨(e : X), hEN e.2⟩ ⟨y, hy⟩ : ↥L) : X) =
          (e : X) * y * (e : X)⁻¹ := rfl
      rw [h4] at h3
      have h5 : (e : X) * y * (e : X)⁻¹ = y := h3
      exact (mul_inv_eq_iff_eq_mul.1 h5).symm
    · intro hc
      have h2 : L.normalizerMonoidHom ⟨(e : X), hEN e.2⟩ = 1 := by
        ext y
        show (e : X) * (y : X) * (e : X)⁻¹ = (y : X)
        rw [(Subgroup.mem_centralizer_iff.1 hc y y.2).symm]
        group
      rw [h2, map_one]
  have hkerEq : ψ.ker = (B ⊓ Subgroup.centralizer (L : Set X)).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨hEB e.2, h⟩, fun h => h.2⟩
  have hcardker : Nat.card ψ.ker = Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) := by
    rw [hkerEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
  have hcardE : Nat.card E = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have hinn : ∀ x ∈ ψ.range, x ∈ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut
      (↥L ⧸ Subgroup.center ↥L) → x = 1 := by
    rintro x ⟨e, rfl⟩ hx
    obtain ⟨k, hk, hc⟩ := exists_inner_of_quot hLq (hEN e.2) hx
    exact (hker e).2 (hout (e : X) e.2 k hk hc)
  have hel : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨a', ha'⟩ := a.2
      obtain ⟨b', hb'⟩ := b.2
      show (a : MulAut (↥L ⧸ Subgroup.center ↥L)) * b = b * a
      rw [← ha', ← hb', ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Inputs27.elem_mul_comm hE a'.2 b'.2)
    · obtain ⟨e, rfl⟩ := hz
      rw [← map_pow]
      have : e ^ p = 1 := Subtype.ext (by simpa using hE.2 (e : X) e.2)
      rw [this, map_one]
  haveI : Finite ↥ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hrange : Nat.card ψ.range ≤ p ^ 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨m, hm⟩ := (CFSG.Open.IsElemAbelian.isPGroup hel).exists_card_eq
    have hm3 : 3 ≤ m := by
      rw [hm] at hlt
      have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
      omega
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p (G := ↥ψ.range) (n := 3)
      (by rw [hm]; exact pow_dvd_pow p hm3)
    set D : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L)) := H.map ψ.range.subtype with hD
    have hDle : D ≤ ψ.range := Subgroup.map_subtype_le H
    have hDcard : Nat.card D = p ^ 3 := by
      rw [hD, Subgroup.card_map_of_injective ψ.range.subtype_injective, hH]
    have hDel : IsElemAbelian p D := CFSG.Open.IsElemAbelian.mono hel hDle
    obtain ⟨x, hx, hx1⟩ := hLO (↥L ⧸ Subgroup.center ↥L) inferInstance hnab idx ⟨f⟩ p hp hp2 D hDel
      hDcard
    exact hx1 (hinn x (hDle (Subgroup.mem_inf.1 hx).1) (Subgroup.mem_inf.1 hx).2)
  rw [hcardE, ← hcardker]
  exact Nat.mul_le_mul_right _ hrange

end Inner

section Reduction

theorem inputI2711ChevPSpor_of_residuals
    (hLB : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime →
      CFSG.LocalAnalysis.GLTheoremA.LBalanceAt G p)
    (hKD : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.LocalAnalysis.GLTheoremA.KDChevInner p)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hLO : CFSG.HardMathSupport.Timmesfeld.Coordinator.LieOuterRank)
    (hC : InputI2711ChevPOuter) (hS : InputI2711SporInner) : Inputs27.InputI2711ChevPSpor := by
  intro X _ _ p hp hp2 L B hLK hLq hB hBN hmax hB4 hnA hnC hA hC1 J0 hJ0 hJt hJ5 hE
  obtain ⟨E, hEB, hEC, hEi, hEl⟩ := hE
  have hE2 : 2 ≤ CFSG.Open.pRank p E := two_le_pRank_of_card_le hp hB hEB hB4 hEi
  have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  have hEel : IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hB hEB
  have hEN : E ≤ Subgroup.normalizer (L : Set X) := hEB.trans hBN
  have hlE : GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ :=
    glaPLayer_ne_bot_of_J0 hp hEB hE2 hJ0 hEl
  have hle : ∀ e ∈ E, GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥ :=
    fun e he => glaPLayer_singleton_ne_bot hp (hLB X p hp) hLK' hEel hEN hlE he
  rcases lie_or_spor hLK hLq hnA hnC with hLie | hSpor
  · have hout : ∀ e ∈ E, ∀ k ∈ L, k⁻¹ * e ∈ Subgroup.centralizer (L : Set X) →
        e ∈ Subgroup.centralizer (L : Set X) := fun e he k hk hc =>
      mem_centralizer_of_inner hp (hKD p hp hp2) hLq (isChevSimple_of_lie hLie) (hEel.2 e he) hk hc
        (hle e he)
    exact hC X p hp hp2 L B hLK hLq hB hBN hmax hB4 hnA hnC hA hC1 hLie J0 hJ0 hJt hJ5 E hEB hEC hEi hEl
      hE2 hlE hle hout (card_le_of_outer hp hp2 hLO hLq hLie hEel hEN hEB hEC hout)
  · refine hS X p hp hp2 L B hLK hLq hB hBN hmax hB4 hnA hnC hA hC1 hSpor ?_ J0 hJ0 hJt hJ5 E hEB hEC hEi hEl
      hE2 hlE hle
    intro b hb
    exact exists_inner_of_spor hp hp2 hOut hLq hSpor (hBN hb) (hB.2 b hb)

end Reduction

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711

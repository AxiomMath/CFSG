module

public import CFSG.HardMathSupport.Solomon.Proving.LBCentralizerZpowers
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAComponentSelf
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Tools
public import CFSG.LocalAnalysis.GLTheoremB.LayerTools

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.Proving

variable {Y : Type} [Group Y]

theorem val_mem_GLAPPrimeCoreOf_iff {p : ℕ} {N : Subgroup Y} (y : N) :
    (y : Y) ∈ GLAPPrimeCoreOf p N ↔ y ∈ GLAPPrimeCore p N := by
  unfold GLAPPrimeCoreOf
  constructor
  · intro h
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 h
    have hzy' : z = y := Subtype.ext (by simpa using hzy)
    exact hzy' ▸ hz
  · intro h
    exact Subgroup.mem_map_of_mem _ h

theorem inf_glaPrimeCore_le [Finite Y] {p : ℕ} (hp : p.Prime) {X N : Subgroup Y}
    (hXN : X ≤ N) :
    X ⊓ GLAPPrimeCoreOf p N ≤ GLAPPrimeCoreOf p X := by
  have hS : ∀ g ∈ X, ∀ s ∈ X ⊓ GLAPPrimeCoreOf p N,
      g * s * g⁻¹ ∈ X ⊓ GLAPPrimeCoreOf p N := by
    intro g hg s hs
    exact ⟨X.mul_mem (X.mul_mem hg hs.1) (X.inv_mem hg),
      GLAPPrimeCoreOf_conj_mem (C := N) g (hXN hg) s hs.2⟩
  have hcop : Nat.Coprime p (Nat.card ↥(X ⊓ GLAPPrimeCoreOf p N)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (coprime_card_GLAPPrimeCoreOf hp N)
  exact le_GLAPPrimeCoreOf_of_normal inf_le_left hS hcop

@[expose] noncomputable def glaQuotMap [Finite Y] {p : ℕ} (hp : p.Prime) {X N : Subgroup Y}
    (hXN : X ≤ N) (hn : (X.subgroupOf N).Normal) :
    ↥X ⧸ GLAPPrimeCore p ↥X →* ↥N ⧸ GLAPPrimeCore p ↥N :=
  QuotientGroup.map (GLAPPrimeCore p ↥X) (GLAPPrimeCore p ↥N) (Subgroup.inclusion hXN)
    (fun a ha => by
      rw [Subgroup.mem_comap]
      have hY : ((Subgroup.inclusion hXN a : ↥N) : Y) ∈ GLAPPrimeCoreOf p N := by
        have haX : (a : Y) ∈ GLAPPrimeCoreOf p X := (val_mem_GLAPPrimeCoreOf_iff a).2 ha
        exact GLAPPrimeCoreOf_le_of_normal_sub hp hXN hn haX
      exact (val_mem_GLAPPrimeCoreOf_iff _).1 hY)

theorem glaQuotMap_mk [Finite Y] {p : ℕ} (hp : p.Prime) {X N : Subgroup Y} (hXN : X ≤ N)
    (hn : (X.subgroupOf N).Normal) (a : ↥X) :
    glaQuotMap hp hXN hn (QuotientGroup.mk a) =
      (QuotientGroup.mk (Subgroup.inclusion hXN a) : ↥N ⧸ GLAPPrimeCore p ↥N) :=
  rfl

theorem glaQuotMap_injective [Finite Y] {p : ℕ} (hp : p.Prime) {X N : Subgroup Y}
    (hXN : X ≤ N) (hn : (X.subgroupOf N).Normal) :
    Function.Injective (glaQuotMap hp hXN hn) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  rw [glaQuotMap_mk] at hq
  rw [QuotientGroup.eq_one_iff] at hq ⊢
  have hY : (a : Y) ∈ GLAPPrimeCoreOf p N := (val_mem_GLAPPrimeCoreOf_iff _).2 hq
  exact (val_mem_GLAPPrimeCoreOf_iff a).1 (inf_glaPrimeCore_le hp hXN ⟨a.2, hY⟩)

theorem glaQuotMap_map_barX [Finite Y] {p : ℕ} (hp : p.Prime) {X N : Subgroup Y}
    (hXN : X ≤ N) (hn : (X.subgroupOf N).Normal) {K : Subgroup Y} (hKX : K ≤ X) :
    (barX p X K).map (glaQuotMap hp hXN hn) = barX p N K := by
  ext q
  constructor
  · intro hq
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hq
    unfold barX at hz ⊢
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hz
    exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hXN a, Subgroup.mem_subgroupOf.2
      (Subgroup.mem_subgroupOf.1 ha), rfl⟩
  · intro hq
    unfold barX at hq
    obtain ⟨n, hn', rfl⟩ := Subgroup.mem_map.1 hq
    have haK : (n : Y) ∈ K := Subgroup.mem_subgroupOf.1 hn'
    refine Subgroup.mem_map.2 ⟨(⟨(n : Y), hKX haK⟩ : ↥X), ?_, ?_⟩
    · unfold barX
      exact Subgroup.mem_map.2 ⟨⟨(n : Y), hKX haK⟩, Subgroup.mem_subgroupOf.2 haK, rfl⟩
    · rfl

theorem barX_self_eq_top (p : ℕ) (N : Subgroup Y) : barX p N N = ⊤ := by
  unfold barX
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem isQuasisimple_barX_overgroup [Finite Y] {p : ℕ} (hp : p.Prime) {X N : Subgroup Y}
    (hXN : X ≤ N) (hn : (X.subgroupOf N).Normal) {L : Subgroup Y} (hLX : L ≤ X)
    (hq : CFSG.Open.IsQuasisimple ↥(barX p X L)) :
    CFSG.Open.IsQuasisimple ↥(barX p N L) := by
  have hinj := glaQuotMap_injective hp hXN hn
  have e1 : ↥(barX p X L) ≃* ↥((barX p X L).map (glaQuotMap hp hXN hn)) :=
    Subgroup.equivMapOfInjective _ _ hinj
  have e2 : ↥((barX p X L).map (glaQuotMap hp hXN hn)) ≃* ↥(barX p N L) :=
    MulEquiv.subgroupCongr (glaQuotMap_map_barX hp hXN hn hLX)
  exact isQuasisimple_of_mulEquiv' (e1.trans e2) hq

theorem glaPComponent_of_normal_overgroup [Finite Y] {p : ℕ} (hp : p.Prime)
    {X N L : Subgroup Y} (hXN : X ≤ N) (hn : (X.subgroupOf N).Normal)
    (hL : GLAPComponent p X L) : GLAPComponent p N L := by
  obtain ⟨hLX, hsn, hcomp, hmin⟩ := hL
  have hLN : L ≤ N := hLX.trans hXN
  have hXsn : IsSubnormal X N := IsSubnormal.step hXN hn (IsSubnormal.refl N)
  have hLsn : IsSubnormal L N := isSubnormal_trans' hsn hXsn
  refine ⟨hLN, hLsn, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have h1 := isSubnormal_barX (C := N) p hLsn
    rw [barX_self_eq_top] at h1
    exact h1
  · exact isQuasisimple_barX_overgroup hp hXN hn hLX hcomp.2.2
  · intro J hJL hJN heq
    have hJX : IsSubnormal J X := by
      have h := isSubnormal_inf hJN X
      rwa [inf_eq_left.2 (hJL.le.trans hLX), inf_eq_right.2 hXN] at h
    apply hmin J hJL hJX
    change barX p X J = barX p X L
    apply Subgroup.map_injective (glaQuotMap_injective hp hXN hn)
    rw [glaQuotMap_map_barX hp hXN hn (hJL.le.trans hLX),
      glaQuotMap_map_barX hp hXN hn hLX]
    exact heq

theorem glaPLayer_le_of_normal_overgroup [Finite Y] {p : ℕ} (hp : p.Prime)
    {X N : Subgroup Y} (hXN : X ≤ N) (hn : (X.subgroupOf N).Normal) :
    GLAPLayer p X ≤ GLAPLayer p N :=
  sSup_le fun _ hL => le_sSup (glaPComponent_of_normal_overgroup hp hXN hn hL)

theorem glaPLayer_centralizer_le_normalizer [Finite Y] {p : ℕ} (hp : p.Prime) {x : Y}
    (hx3 : x ^ 3 = 1) :
    GLAPLayer p (Subgroup.centralizer ({x} : Set Y)) ≤
      GLAPLayer p (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup Y) : Set Y)) :=
  glaPLayer_le_of_normal_overgroup hp (centralizer_le_normalizer_zpowers (x := x))
    (centralizer_subgroupOf_normalizer_normal hx3)

end CFSG.HardMathSupport.Solomon.Proving

end

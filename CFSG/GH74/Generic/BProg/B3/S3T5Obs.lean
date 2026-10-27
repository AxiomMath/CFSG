module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29E1
public import CFSG.GH74.Generic.BProg.B3.S3KG31eDesc

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.Obs CFSG.GH74.GLS.Th2.Bal CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

namespace S3T5

namespace W

section Transport

theorem isLocallyKBalanced_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] {k : ℕ}
    (e : X ≃* Y) (h : IsLocallyKBalanced k Y) : IsLocallyKBalanced k X :=
  S3KG.isLocallyKBalanced_of_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
    (fun y => ⟨e.symm y, by ext x; simp [MulAut.conj_apply]⟩) h

theorem isLocallyKBalanced_of_center_quotient {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] {k : ℕ} (h : IsLocallyKBalanced k (X ⧸ center X)) :
    IsLocallyKBalanced k X :=
  S3KG.isLocallyKBalanced_of_injective
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X)
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective X)
    (fun q => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨g, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj (G := X) g⟩) h

end Transport

variable {G : Type} [Group G] [Finite G] {B : Subgroup G} {b : G} {D J : Subgroup G}

omit [Finite G] in
theorem D_le_centralizer (h : Obs52 B b D J) : D ≤ centralizer ({b} : Set G) := fun d hd => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp h.b_cent d (h.D_le.1 hd)

omit [Finite G] in
theorem B_le_centralizer (h : Obs52 B b D J) : B ≤ centralizer ({b} : Set G) := fun e he => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp h.b_cent e he

theorem AG_inf_le_normalizer (h : Obs52 B b D J) :
    AG D ⊓ centralizer ({b} : Set G) ≤ normalizer (J : Set G) := by
  obtain ⟨-, hDel, hDr⟩ := h.D_le
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  obtain ⟨d₀, hd₀D, hd₀1⟩ := Th2Sig6.exists_ne_one_of_card (k := pRank 2 ↥D) (by omega)
    (C3.Layer1.Back.card_eq_two_pow_pRank hDel)
  exact CFSG.GH74.Generic.BProg.B3.Obs.inf_AG_le_normalizer (D_le_centralizer h) hDsq h.comp
    h.D_norm hd₀D hd₀1

omit [Finite G] in
theorem commutator_mem (h : Obs52 B b D J) (hBel : CFSG.IsElementaryAbelian 2 ↥B) {c e : G}
    (hc : c ∈ AG D ⊓ centralizer ({b} : Set G)) (he : e ∈ B) :
    ⁅c, e⁆ ∈ AG D ⊓ centralizer ({b} : Set G) := by
  obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hBH := B_le_centralizer h
  have hcomm : ⁅c, e⁆ = c * (e * c⁻¹ * e⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hcomm]
  refine (AG D ⊓ centralizer ({b} : Set G)).mul_mem hc ⟨?_, ?_⟩
  · exact conj_mem_AG (fun d hd => hBc _ he d (h.D_le.1 hd)) ((AG D).inv_mem hc.1)
  · exact (centralizer ({b} : Set G)).mul_mem
      ((centralizer ({b} : Set G)).mul_mem (hBH he) ((centralizer ({b} : Set G)).inv_mem hc.2))
      ((centralizer ({b} : Set G)).inv_mem (hBH he))

omit [Finite G] in
theorem exists_move (h : Obs52 B b D J) (hBel : CFSG.IsElementaryAbelian 2 ↥B) :
    ∃ c ∈ AG D ⊓ centralizer ({b} : Set G), c ∉ centralizerSection J (pPrimeCoreOf 2 J) := by
  rcases h.unbal with ⟨-, hnot⟩ | ⟨-, c, hc, e, he, hce⟩
  · exact IsConcreteLE.not_le_iff_exists.mp hnot
  · exact ⟨⁅c, e⁆, commutator_mem h hBel hc he, hce⟩

theorem barAct_mem_deltaCore (h : Obs52 B b D J) {c : G}
    (hc : c ∈ AG D ⊓ centralizer ({b} : Set G)) (hcM : c ∈ normalizer (J : Set G)) :
    (barAct J).rangeRestrict ⟨c, hcM⟩ ∈
      deltaCore ((D.subgroupOf (normalizer (J : Set G))).map (barAct J).rangeRestrict) := by
  obtain ⟨-, hDel, -⟩ := h.D_le
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  rw [mem_deltaCore_iff]
  rintro _ ⟨m, hm, rfl⟩ hf1
  have hmD : (m : G) ∈ D := Subgroup.mem_subgroupOf.mp hm
  have hm1 : (m : G) ≠ 1 := by
    intro h1
    apply hf1
    have : m = 1 := Subtype.ext h1
    rw [this, map_one]
  exact map_mem_involutionOddCore _ (MonoidHom.rangeRestrict_surjective _) m.2 (hDsq _ hmD) hcM
    (AG_le_pPrimeCoreOf hmD hm1 hc.1)

theorem centralizes_of_locBal2 (h : Obs52 B b D J) (hloc : IsLocallyKBalanced 2 (kBar J)) :
    AG D ⊓ centralizer ({b} : Set G) ≤ centralizerSection J (pPrimeCoreOf 2 J) := by
  classical
  obtain ⟨-, hDel, hDr⟩ := h.D_le
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  have hYN := AG_inf_le_normalizer h
  intro c hc
  by_contra hcs
  set M : Subgroup G := normalizer (J : Set G) with hM
  set ρ : ↥M →* MulAut (kBar J) := barAct J with hρ
  set Z : Subgroup (MulAut (kBar J)) := ρ.range with hZ
  have hInn : innAut (kBar J) ≤ Z := innAut_le_range_barAct J
  have hcM : c ∈ M := hYN hc
  set F : Subgroup ↥Z := (D.subgroupOf M).map ρ.rangeRestrict with hF
  have hFeq : (D.subgroupOf M).map ρ = F.map Z.subtype := by
    rw [hF, Subgroup.map_map]
    rfl
  have hFcard : Nat.card F = Nat.card D := by
    rw [← S3Sec29E1.card_map_barAct_of_faith h.D_norm h.D_faith, hFeq,
      Subgroup.card_map_of_injective Z.subtype_injective]
  have hF2 : ∀ f ∈ F, f * f = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (hDsq m (Subgroup.mem_subgroupOf.mp hm))
    rw [this, map_one]
  have hmem : ρ.rangeRestrict ⟨c, hcM⟩ ∈ deltaCore F := barAct_mem_deltaCore h hc hcM
  have h4 : 2 ^ 2 ≤ Nat.card F := by
    rw [hFcard, C3.Layer1.Back.card_eq_two_pow_pRank hDel]
    exact Nat.pow_le_pow_right (by norm_num) hDr
  have hbot : deltaCore F = ⊥ := hloc Z hInn F h4 hF2
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hcs ((barAct_eq_one_iff ⟨c, hcM⟩).1 (congrArg Subtype.val hmem))

theorem not_isLocallyKBalanced_two (h : Obs52 B b D J) (hBel : CFSG.IsElementaryAbelian 2 ↥B) :
    ¬ IsLocallyKBalanced 2 (kBar J) := fun hloc => by
  obtain ⟨c, hc, hcs⟩ := exists_move h hBel
  exact hcs (centralizes_of_locBal2 h hloc hc)

end W

end S3T5

end CFSG.GH74.Generic.BProg.B3

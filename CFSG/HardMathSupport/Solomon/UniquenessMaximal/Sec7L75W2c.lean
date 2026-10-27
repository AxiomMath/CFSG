module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75Z1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75X2
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barX_normal_of_normal {N U C : Subgroup G} (hUC : U ≤ C) (_hCN : C ≤ N)
    (hn : (U.subgroupOf C).Normal) :
    ((barX 3 N U).subgroupOf (barX 3 N C)).Normal := by
  refine ⟨fun n hn' g => ?_⟩
  have hn'' : (n : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∈ barX 3 N U := Subgroup.mem_subgroupOf.1 hn'
  obtain ⟨cn, hcnN, hcnU, hcn⟩ := exists_mem_of_mem_barX hn''
  obtain ⟨cg, hcgN, hcgC, hcg⟩ := exists_mem_of_mem_barX g.2
  rw [Subgroup.mem_subgroupOf]
  have hconj : ((g * n * g⁻¹ : ↥(barX 3 N C)) : ↥N ⧸ GLAPPrimeCore 3 ↥N) =
      mkN N (cg * cn * cg⁻¹) (N.mul_mem (N.mul_mem hcgN hcnN) (N.inv_mem hcgN)) := by
    change (g : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (n : ↥N ⧸ GLAPPrimeCore 3 ↥N) *
      (g : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹ = _
    rw [hcn, hcg]
    rfl
  rw [hconj]
  exact mkN_mem_barX _ (conj_mem_of_normal_subgroupOf hUC hn hcgC hcnU)

omit [Finite G] in
theorem not_dvd_card_barX {N S : Subgroup G} (hSN : S ≤ N) (h : ¬ 3 ∣ Nat.card S) :
    ¬ 3 ∣ Nat.card (barX 3 N S) := by
  intro hd
  refine h (hd.trans ?_)
  have h1 : Nat.card (S.subgroupOf N) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  rw [← h1]
  exact Subgroup.card_map_dvd _ _

theorem pt_G {N J₁ Ia : Subgroup G} {a : G}
    (hJ1N : J₁ ≤ N) (hJ1a : J₁ ≤ Subgroup.centralizer ({a} : Set G))
    (hIaC : GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) Ia)
    (hIan : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Ia : Set G))
    (hJ1Ia : J₁ ≤ Ia) (hcov : Ia ≤ J₁ ⊔ GLAPPrimeCoreOf 3 Ia) :
    ((J₁ ⊔ (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊓ N)).subgroupOf
      (N ⊓ Subgroup.centralizer ({a} : Set G))).Normal := by
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set O := GLAPPrimeCoreOf 3 Ca with hO
  have hIaCa : Ia ≤ Ca := hIaC.1
  have hOCa : O ≤ Ca := Sec7.glaPPrimeCoreOf_le_self' 3 Ca
  have hIanorm : (Ia.subgroupOf Ca).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIaCa).2 hIan
  have hOiO : GLAPPrimeCoreOf 3 Ia ≤ O :=
    glaPPrimeCoreOf_le_of_normal Nat.prime_three hIaCa hIanorm
  have hOn : Ca ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 Ca
  have hWn : Ca ≤ Subgroup.normalizer ((Ia ⊔ O : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_sup Ia O ⟨hIan hg, hOn hg⟩
  have hWeq : Ia ⊔ O = J₁ ⊔ O := by
    refine le_antisymm (sup_le ?_ le_sup_right) (sup_le_sup_right hJ1Ia O)
    exact hcov.trans (sup_le_sup_left hOiO J₁)
  have hJO : J₁ ≤ Subgroup.normalizer (O : Set G) := fun j hj => hOn (hJ1a hj)
  have hEq : J₁ ⊔ (O ⊓ N) = (J₁ ⊔ O) ⊓ N := by
    refine le_antisymm (sup_le (le_inf le_sup_left hJ1N)
      (inf_le_inf_right _ le_sup_right)) ?_
    rintro x ⟨hxW, hxN⟩
    obtain ⟨j, hj, o, ho, rfl⟩ := exists_mul_of_mem_sup hJO hxW
    have hoN : o ∈ N := by
      have := mul_mem (inv_mem (hJ1N hj)) hxN
      simpa using this
    exact mul_mem (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right ⟨ho, hoN⟩)
  have hle : J₁ ⊔ (O ⊓ N) ≤ N ⊓ Ca :=
    sup_le (le_inf hJ1N hJ1a) (inf_le_inf_right _ hOCa |>.trans (by rw [inf_comm]))
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_
  refine le_normalizer_of_conj_mem fun g hg x hx => ?_
  rw [hEq] at hx ⊢
  rw [← hWeq] at hx ⊢
  exact ⟨(Subgroup.mem_normalizer_iff.1 (hWn hg.2) x).1 hx.1,
    N.mul_mem (N.mul_mem hg.1 hx.2) (N.inv_mem hg.1)⟩

theorem barX_eq_of_covers {N J₁ K0 : Subgroup G} (hJ1N : J₁ ≤ N) (hJ1K0 : J₁ ≤ K0)
    (hK0N : K0 ≤ N) (hK0J1 : K0 ≤ J₁ ⊔ GLAPPrimeCoreOf 3 K0)
    (hq : CFSG.Open.IsQuasisimple ↥(barX 3 N K0))
    (hL34 : IsLThreeFour (↥(barX 3 N K0) ⧸ GLAPPrimeCore 3 ↥(barX 3 N K0))) :
    barX 3 N J₁ = barX 3 N K0 := by
  set K0b := barX 3 N K0 with hK0b
  set O0 := GLAPPrimeCoreOf 3 K0 with hO0
  have hO0K : O0 ≤ K0 := Sec7.glaPPrimeCoreOf_le_self' 3 K0
  have hO0N : O0 ≤ N := hO0K.trans hK0N
  have hK0eq : K0 = J₁ ⊔ O0 := le_antisymm hK0J1 (sup_le hJ1K0 hO0K)
  have hbK : K0b = barX 3 N J₁ ⊔ barX 3 N O0 := by
    rw [hK0b, ← barX_sup hJ1N hO0N, ← hK0eq]
  have hO0n : (O0.subgroupOf K0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO0K).2 (le_normalizer_glaPPrimeCoreOf 3 K0)
  have hbn : ((barX 3 N O0).subgroupOf K0b).Normal := barX_normal_of_normal hO0K hK0N hO0n
  have hbOK : barX 3 N O0 ≤ K0b := barX_mono 3 hO0K
  have hb3 : ¬ 3 ∣ Nat.card (barX 3 N O0) :=
    not_dvd_card_barX hO0N (not_dvd_card_glaPPrimeCoreOf Nat.prime_three K0)
  have hbO : barX 3 N O0 ≤ GLAPPrimeCoreOf 3 K0b :=
    Lemma85Aux.le_glaPPrimeCoreOf_of_normalizes Nat.prime_three hbOK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hbOK).1 hbn) hb3
  have hprop : GLAPPrimeCore 3 ↥K0b ≠ ⊤ := by
    intro htop
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥K0b)
    have h2 : Nat.card (GLAPPrimeCore 3 ↥K0b) = Nat.card ↥K0b := by
      rw [htop, Subgroup.card_top]
    have h3 := card_eq_of_isLThreeFour hL34
    rw [h2, h3] at h1
    have h4 : 0 < Nat.card ↥K0b := Nat.card_pos
    omega
  have hcenP := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq
    (GLAPPrimeCore 3 ↥K0b) hprop
  have hZ : ∀ z ∈ GLAPPrimeCoreOf 3 K0b, ∀ m ∈ K0b, z * m = m * z := by
    rintro _ ⟨z', hz', rfl⟩ m hm
    have h := Subgroup.mem_center_iff.1 (hcenP hz') ⟨m, hm⟩
    exact (congrArg Subtype.val h).symm
  have hMJ : K0b = barX 3 N J₁ ⊔ GLAPPrimeCoreOf 3 K0b := by
    refine le_antisymm ?_ (sup_le (barX_mono 3 hJ1K0) (Sec7.glaPPrimeCoreOf_le_self' 3 K0b))
    exact hbK.le.trans (sup_le_sup_left hbO _)
  have hperf : ⁅K0b, K0b⁆ = K0b := by
    refine le_antisymm ?_ (Sec7.le_commutator_of_isQuasisimple hq)
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  exact eq_of_perfect_sup_central (barX_mono 3 hJ1K0) hMJ hZ hperf

private theorem pt_aux {N J₁ K0 Ia : Subgroup G} {a : G}
    (hJ1N : J₁ ≤ N) (hJ1K0 : J₁ ≤ K0) (hK0N : K0 ≤ N)
    (hK0J1 : K0 ≤ J₁ ⊔ GLAPPrimeCoreOf 3 K0)
    (hq : CFSG.Open.IsQuasisimple ↥(barX 3 N K0))
    (hL34 : IsLThreeFour (↥(barX 3 N K0) ⧸ GLAPPrimeCore 3 ↥(barX 3 N K0)))
    (hJ1a : J₁ ≤ Subgroup.centralizer ({a} : Set G))
    (hIaC : GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) Ia)
    (hIan : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Ia : Set G))
    (hJ1Ia : J₁ ≤ Ia) (hcov : Ia ≤ J₁ ⊔ GLAPPrimeCoreOf 3 Ia) :
    barX 3 N (J₁ ⊔ (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊓ N)) ≤
        barX 3 N (N ⊓ Subgroup.centralizer ({a} : Set G)) ∧
      ((barX 3 N (J₁ ⊔ (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊓ N))).subgroupOf
        (barX 3 N (N ⊓ Subgroup.centralizer ({a} : Set G)))).Normal ∧
      barX 3 N (J₁ ⊔ (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊓ N)) =
        barX 3 N K0 ⊔ barX 3 N (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊓ N) ∧
      barX 3 N (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊓ N) ≤
        barX 3 N (N ⊓ Subgroup.centralizer ({a} : Set G)) ∧
      ((barX 3 N (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊓ N)).subgroupOf
        (barX 3 N (N ⊓ Subgroup.centralizer ({a} : Set G)))).Normal ∧
      ¬ 3 ∣ Nat.card (barX 3 N (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊓ N)) := by
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set O := GLAPPrimeCoreOf 3 Ca with hO
  have hOCa : O ≤ Ca := Sec7.glaPPrimeCoreOf_le_self' 3 Ca
  have hOn : Ca ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 Ca
  have hOnN : O ⊓ N ≤ N ⊓ Ca := le_inf inf_le_right (inf_le_left.trans hOCa)
  have hUle : J₁ ⊔ (O ⊓ N) ≤ N ⊓ Ca := sup_le (le_inf hJ1N hJ1a) hOnN
  have hCN : N ⊓ Ca ≤ N := inf_le_left
  have hUn := barX_normal_of_normal hUle hCN
    (pt_G hJ1N hJ1a hIaC hIan hJ1Ia hcov)
  have hRn : (((O ⊓ N).subgroupOf (N ⊓ Ca)).Normal) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hOnN).2 ?_
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxO, hxN⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 (hOn hg.2) x).1 hxO,
        N.mul_mem (N.mul_mem hg.1 hxN) (N.inv_mem hg.1)⟩
    · rintro ⟨hxO, hxN⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hOn hg.2) x).2 hxO, ?_⟩
      have := N.mul_mem (N.mul_mem (N.inv_mem hg.1) hxN) hg.1
      simpa [mul_assoc] using this
  have hR3 : ¬ 3 ∣ Nat.card (O ⊓ N : Subgroup G) :=
    fun h => not_dvd_card_glaPPrimeCoreOf Nat.prime_three Ca
      (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  refine ⟨barX_mono 3 hUle, hUn, ?_, barX_mono 3 hOnN, barX_normal_of_normal hOnN hCN hRn,
    not_dvd_card_barX inf_le_right hR3⟩
  rw [barX_sup hJ1N inf_le_right, barX_eq_of_covers hJ1N hJ1K0 hK0N hK0J1 hq hL34]

namespace Ctx75

variable {B N K : Subgroup G} {x : G}

private theorem aK_pow_three (c : Ctx75 B N K x) {a : G} (ha : a ∈ centralizerQuot B K) :
    a ^ 3 = 1 :=
  c.bone.1.1.2 a ((Subgroup.closure_le B).2 (fun _ hb => hb.1) ha)

omit [Finite G] in
private theorem le_centralizer_of_le_centralizerQuot {J₁ : Subgroup G}
    (hJ1C : J₁ ≤ Subgroup.centralizer (centralizerQuot B K : Set G)) {a : G}
    (ha : a ∈ centralizerQuot B K) : J₁ ≤ Subgroup.centralizer ({a} : Set G) := by
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.1 hh]
  exact Subgroup.mem_centralizer_iff.1 (hJ1C hj) a ha

theorem pt_D1_of_J1 (c : Ctx75 B N K x)
    {J₁ : Subgroup G} (hJ1N : J₁ ≤ N) (hJ1K0 : J₁ ≤ GLAPLayer 3 (K ⊓ N))
    (hJ1C : J₁ ≤ Subgroup.centralizer (centralizerQuot B K : Set G))
    (hK0J1 : GLAPLayer 3 (K ⊓ N) ≤ J₁ ⊔ GLAPPrimeCoreOf 3 (GLAPLayer 3 (K ⊓ N)))
    (hIa : ∀ a ∈ centralizerQuot B K, a ≠ 1 →
      J₁ ≤ bClosureIa K a ∧ bClosureIa K a ≤ J₁ ⊔ GLAPPrimeCoreOf 3 (bClosureIa K a))
    (hAc : barX 3 N (centralizerQuot B K) ≤
      Subgroup.centralizer (barX 3 N (GLAPLayer 3 (K ⊓ N)) : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)))
    (hq : CFSG.Open.IsQuasisimple ↥(barX 3 N (GLAPLayer 3 (K ⊓ N))))
    (hL34 : IsLThreeFour (↥(barX 3 N (GLAPLayer 3 (K ⊓ N))) ⧸
      GLAPPrimeCore 3 ↥(barX 3 N (GLAPLayer 3 (K ⊓ N)))))
    {I : Subgroup G} (hIN : I ≤ N) (hK0I : GLAPLayer 3 (K ⊓ N) ≤ I)
    {a : G} (ha : a ∈ centralizerQuot B K) (ha1 : a ≠ 1) :
    ((barX 3 N (GLAPLayer 3 (K ⊓ N)) ⊔ GLAPPrimeCoreOf 3 (barX 3 N I ⊓
        Subgroup.centralizer ({mkN N a (c.AN ha)} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)))).subgroupOf
      (barX 3 N I ⊓ Subgroup.centralizer ({mkN N a (c.AN ha)} :
        Set (↥N ⧸ GLAPPrimeCore 3 ↥N)))).Normal := by
  have _ := hIN
  have hK0N : GLAPLayer 3 (K ⊓ N) ≤ N := (glaPLayer_le 3 _).trans inf_le_right
  have hCb := centralizer_mkN_singleton (c.AN ha) (c.aK_pow_three ha)
  obtain ⟨hUC, hUn, hU, hRC, hRn, hR3⟩ :=
    pt_aux hJ1N hJ1K0 hK0N hK0J1 hq hL34 (le_centralizer_of_le_centralizerQuot hJ1C ha)
      (c.hf.ia a ha ha1).component (c.hf.ia a ha ha1).normal (hIa a ha ha1).1 (hIa a ha ha1).2
  have hRO := Lemma85Aux.le_glaPPrimeCoreOf_of_normalizes Nat.prime_three hRC
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hRC).1 hRn) hR3
  have hān : mkN N a (c.AN ha) ∈ barX 3 N (centralizerQuot B K) := mkN_mem_barX _ ha
  have hcomm := Subgroup.mem_centralizer_iff.1 (hAc hān)
  have hK0c : barX 3 N (GLAPLayer 3 (K ⊓ N)) ≤
      Subgroup.centralizer ({mkN N a (c.AN ha)} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (hcomm j hj).symm
  refine pt_abs hUC hUn hU hRO ?_ ?_
  · rw [← hCb]; exact inf_le_right
  · exact le_inf (barX_mono 3 hK0I) hK0c

theorem pt_D3_of_J1 (c : Ctx75 B N K x)
    {J₁ : Subgroup G} (hJ1N : J₁ ≤ N) (hJ1K0 : J₁ ≤ GLAPLayer 3 (K ⊓ N))
    (hJ1C : J₁ ≤ Subgroup.centralizer (centralizerQuot B K : Set G))
    (hK0J1 : GLAPLayer 3 (K ⊓ N) ≤ J₁ ⊔ GLAPPrimeCoreOf 3 (GLAPLayer 3 (K ⊓ N)))
    (hIa : ∀ a ∈ centralizerQuot B K, a ≠ 1 →
      J₁ ≤ bClosureIa K a ∧ bClosureIa K a ≤ J₁ ⊔ GLAPPrimeCoreOf 3 (bClosureIa K a))
    (hq : CFSG.Open.IsQuasisimple ↥(barX 3 N (GLAPLayer 3 (K ⊓ N))))
    (hL34 : IsLThreeFour (↥(barX 3 N (GLAPLayer 3 (K ⊓ N))) ⧸
      GLAPPrimeCore 3 ↥(barX 3 N (GLAPLayer 3 (K ⊓ N)))))
    {I : Subgroup G} (hIN : I ≤ N) (hK0I : GLAPLayer 3 (K ⊓ N) ≤ I)
    {a : G} (ha : a ∈ centralizerQuot B K) (ha1 : a ≠ 1)
    (hcent : barX 3 N I ≤ Subgroup.centralizer ({mkN N a (c.AN ha)} :
        Set (↥N ⧸ GLAPPrimeCore 3 ↥N)))
    (hOI : GLAPPrimeCoreOf 3 (barX 3 N I) = ⊥) :
    ((barX 3 N (GLAPLayer 3 (K ⊓ N))).subgroupOf (barX 3 N I)).Normal := by
  have _ := hIN
  have hK0N : GLAPLayer 3 (K ⊓ N) ≤ N := (glaPLayer_le 3 _).trans inf_le_right
  have hCb := centralizer_mkN_singleton (c.AN ha) (c.aK_pow_three ha)
  obtain ⟨hUC, hUn, hU, hRC, hRn, hR3⟩ :=
    pt_aux hJ1N hJ1K0 hK0N hK0J1 hq hL34 (le_centralizer_of_le_centralizerQuot hJ1C ha)
      (c.hf.ia a ha ha1).component (c.hf.ia a ha ha1).normal (hIa a ha ha1).1 (hIa a ha ha1).2
  refine pt_abs2 hUC hUn hU hRC hRn hR3 ?_ (barX_mono 3 hK0I) hOI
  rw [← hCb]; exact hcent

end Ctx75

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

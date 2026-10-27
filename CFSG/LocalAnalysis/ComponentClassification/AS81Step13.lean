module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS81Cover
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourE16
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec3Config

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS76b

section Inner

variable {G : Type} [Group G] [Finite G]

theorem le_sup_centralizer_of_sixteen_le {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) {B Q E : Subgroup G}
    (hB : commutator ↥B = ⊤) (e : ↥B ⧸ center ↥B ≃* ↥PSL3Four.S)
    (hQ : IsSylowOf 2 Q (centralizer (B : Set G))) (hEN : E ≤ normalizer (B : Set G))
    (hE : IsElemAbelian 2 E) (hcard : 16 * Nat.card Q ≤ Nat.card E) :
    E ≤ B ⊔ centralizer (B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom RankTwoL3Four.HypII.l34AutModel hB e
  obtain ⟨E', hE'⟩ : ∃ E' : Subgroup (normalizer (B : Set G)),
      E' = E.subgroupOf (normalizer (B : Set G)) := ⟨_, rfl⟩
  have hE'mem : ∀ n : normalizer (B : Set G), n ∈ E' ↔ (n : G) ∈ E := fun n => by
    rw [hE', mem_subgroupOf]
  have hE'card : Nat.card E' = Nat.card E := by
    rw [hE']
    exact Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv
  have hE'e : IsElemAbelian 2 E' := hE' ▸ isElemAbelian_subgroupOf hE _
  have hker : Nat.card (ψ.comp E'.subtype).ker ≤ Nat.card Q := by
    have hι : Function.Injective ((normalizer (B : Set G)).subtype.comp E'.subtype) :=
      (normalizer (B : Set G)).subtype_injective.comp E'.subtype_injective
    have hle : (ψ.comp E'.subtype).ker.map ((normalizer (B : Set G)).subtype.comp E'.subtype) ≤
        E ⊓ centralizer (B : Set G) := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨(hE'mem _).mp z.2, (hψ.eq_one_iff _).mp (MonoidHom.mem_ker.mp hz)⟩
    rw [← card_map_of_injective hι]
    exact AschbacherTheorem3.card_le_of_isSylowOf hQ
      ((isPGroup_two_of_isElemAbelian hE).to_le (hle.trans inf_le_left)) (hle.trans inf_le_right)
  have h1 := Subgroup.card_ker_mul_card_range (ψ.comp E'.subtype)
  rw [MonoidHom.range_comp, range_subtype, hE'card] at h1
  have hV : IsElemAbelian 2 (E'.map ψ) := RankTwoSporadic.isElemAbelian_map hE'e ψ
  have hV16 : 16 ≤ Nat.card (E'.map ψ) := by
    by_contra hlt
    push Not at hlt
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have h3 : Nat.card (ψ.comp E'.subtype).ker * Nat.card (E'.map ψ) ≤
        Nat.card Q * Nat.card (E'.map ψ) := Nat.mul_le_mul_right _ hker
    have h4 : Nat.card Q * Nat.card (E'.map ψ) < Nat.card Q * 16 :=
      Nat.mul_lt_mul_of_pos_left hlt hQpos
    rw [h1] at h3
    omega
  have hVS := RankTwoL3Four.HypII.l34_le_of_sixteen_le hE16 hV hV16
  intro x hx
  obtain ⟨b, hb, hbx⟩ := hψ.exists_eq _ (hVS ⟨⟨x, hEN hx⟩, (hE'mem _).mpr hx, rfl⟩)
  have h2 : ψ ((⟨b, le_normalizer hb⟩ : normalizer (B : Set G))⁻¹ * ⟨x, hEN hx⟩) = 1 := by
    rw [map_mul, map_inv, hbx, inv_mul_cancel]
  have hC := (hψ.eq_one_iff _).mp h2
  simp only [coe_mul, coe_inv] at hC
  rw [show x = b * (b⁻¹ * x) by group]
  exact mul_mem_sup hb hC

end Inner

section Core

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_centralizer_of_isPGroup {A R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) {z : G} (hzA : z ∈ A)
    (hzK : z ∈ centralizer (A : Set G)) (h2 : IsPGroup 2 (zpowers z)) : z ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzN : zpowers z ≤ normalizer (R : Set G) := by
    rw [zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hR.le hzA)
  have hsup : R ⊔ zpowers z = R :=
    hR.eq_of_le le_sup_left (sup_le hR.le (zpowers_le.mpr hzK))
      (hR.isPGroup.to_sup_of_normal_left' h2 hzN)
  exact hsup ▸ mem_sup_right (mem_zpowers _)

omit [Finite G] in
theorem centerIn_map_subtype_le {A : Subgroup G} (T : Subgroup ↥A) :
    centerIn (T.map A.subtype) ≤ (centerIn T).map A.subtype := by
  rintro _ ⟨⟨t, ht, rfl⟩, htC⟩
  have htC' : A.subtype t ∈ centralizer ((T.map A.subtype : Subgroup G) : Set G) := htC
  refine ⟨t, ⟨ht, ?_⟩, rfl⟩
  show t ∈ centralizer (T : Set ↥A)
  rw [mem_centralizer_iff]
  intro s hs
  exact Subtype.ext (mem_centralizer_iff.mp htC' (A.subtype s) ⟨s, hs, rfl⟩)

omit [Finite G] in
theorem map_inf_center_le_centerIn {A : Subgroup G} (T : Subgroup ↥A) :
    (T ⊓ center ↥A).map A.subtype ≤ centerIn (T.map A.subtype) := by
  rintro _ ⟨z, ⟨hzT, hzZ⟩, rfl⟩
  refine ⟨⟨z, hzT, rfl⟩, ?_⟩
  show A.subtype z ∈ centralizer ((T.map A.subtype : Subgroup G) : Set G)
  rw [mem_centralizer_iff]
  rintro _ ⟨s, -, rfl⟩
  exact congrArg Subtype.val (mem_center_iff.mp hzZ s)

theorem l34Cover_of_base (h11 : Step11) {A : Subgroup G} (hB : Base G A)
    (hL : TypeL34 (rankTwoQuot A)) : Nonempty (L34Cover ↥A) := by
  have hstd := hB.hyp.standard
  refine exists_l34Cover hstd.1.1 hL hstd.1.2 fun z hz h2 => ?_
  have hzK : (z : G) ∈ centralizer (A : Set G) := mem_centralizer_iff.mpr fun a ha =>
    congrArg Subtype.val (mem_center_iff.mp hz ⟨a, ha⟩)
  have h2' : IsPGroup 2 (zpowers (z : G)) := by
    have := h2.map A.subtype
    rwa [MonoidHom.map_zpowers] at this
  have := RankTwoSporadic.sq_eq_one_of_isPGroup_zpowers
    (fun R' hR' => (h11 G A hB R' hR').1) hzK h2'
  exact Subtype.ext (by simpa using this)

theorem exists_sylow_centerIn_eq (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) {A : Subgroup G} (hB : Base G A)
    (hL : TypeL34 (rankTwoQuot A)) {R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) {g : G} (hg : g ∉ normalizer (A : Set G))
    (hgc : rightConjugate R g ≤ centralizer (R : Set G)) :
    Nat.card R = 4 ∧ ∃ D : Subgroup G, IsSylowOf 2 D (A ⊔ R) ∧ rightConjugate R g ≤ D ∧
      D ≤ rightConjugate A g ⊔ rightConjugate R g ∧ centerIn D = R ⊔ rightConjugate R g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRe, -, hle⟩ := h11 G A hB R hR
  have hRgAR : rightConjugate R g ≤ A ⊔ R := hle g hg hgc
  have hstd := hB.hyp.standard
  have hAperf : commutator ↥A = ⊤ := hstd.1.1
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := hNK ▸ hg
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hR2 : IsPGroup 2 R := hR.isPGroup
  have hAR : A ≤ centralizer (R : Set G) := le_centralizer_iff.mp hRA
  have hRR : R ≤ centralizer (R : Set G) := fun y hy => mem_centralizer_iff.mpr fun z hz =>
    congrArg Subtype.val (hRe.1.is_comm.comm ⟨z, hz⟩ ⟨y, hy⟩)
  have hKg : rightConjugate (centralizer (A : Set G)) g =
      centralizer (rightConjugate A g : Set G) := AschbacherTheorem3.rightConjugate_centralizer A g
  have hRg : IsSylowOf 2 (rightConjugate R g) (centralizer (rightConjugate A g : Set G)) :=
    hKg ▸ AschbacherTheorem3.isSylowOf_rightConjugate hR g
  have hRge : IsElemAbelian 2 (rightConjugate R g) := isElemAbelian_rightConjugate hRe g
  have hRgcard : Nat.card (rightConjugate R g) = Nat.card R := rightConjugate_card R g
  have hRRg : R ⊓ rightConjugate R g = ⊥ := by
    have h := two_subgroup_inf_conjugate_eq_bot _ (R ⊓ rightConjugate R g) hKte
      (hR2.to_le inf_le_left) g hgK
      (inf_le_right.trans (AschbacherTheorem3.rightConjugate_le_rightConjugate hRA g))
    rwa [inf_eq_left.mpr (inf_le_left.trans hRA)] at h
  let fA : ↥(rightConjugate A g) ≃* ↥A :=
    (A.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm
  have hAgperf : commutator ↥(rightConjugate A g) = ⊤ := by
    have : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hAperf
    exact (Group.isPerfect_def).1
      (Group.IsPerfect.ofSurjective (f := fA.symm.toMonoidHom) fA.symm.surjective)
  obtain ⟨e₀⟩ := PSL3Four.nonempty_equiv_of_stated (↥A ⧸ center ↥A) hL
  let eAg : ↥(rightConjugate A g) ⧸ center ↥(rightConjugate A g) ≃* ↥PSL3Four.S :=
    (QuotientGroup.congr (center ↥(rightConjugate A g)) (center ↥A) fA
      (map_center_eq fA)).trans e₀
  obtain ⟨c⟩ := l34Cover_of_base h11 hB hL
  have hcent : ∀ a ∈ A, a ^ 2 = 1 → ∃ T : Subgroup G, IsSylowOf 2 T A ∧
      T ≤ centralizer ({a} : Set G) := by
    intro a ha ha2
    by_cases ha1 : a = 1
    · obtain ⟨P, hP, -⟩ :=
        AschbacherTheorem3.exists_isSylowOf_le (L := A) IsPGroup.of_bot bot_le
      refine ⟨P, hP, fun t _ => ?_⟩
      rw [mem_centralizer_singleton_iff, ha1, mul_one, one_mul]
    · have ha2' : (⟨a, ha⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using ha2)
      have ha1' : (⟨a, ha⟩ : ↥A) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
      obtain ⟨T, -, hTC⟩ := exists_sylow_le_centralizer c ha2' ha1'
      refine ⟨(T : Subgroup ↥A).map A.subtype, ⟨T, rfl⟩, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hTC ht))
  have hR1 : R ≠ ⊥ := isSylowOf_ne_bot_of_even hR hKte.1
  have hRg1 : rightConjugate R g ≠ ⊥ := by
    intro h
    apply hR1
    rw [← Subgroup.card_eq_one, ← rightConjugate_card R g, h, Subgroup.card_bot]
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hRg1
  have hxRg : (x : G) ∈ rightConjugate R g := x.2
  have hx2 : (x : G) ^ 2 = 1 := hRge.2 _ hxRg
  have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨D₁, hD₁, hD₁x⟩ :=
    exists_isSylowOf_sup_le_centralizer hRA hRe hcent (hRgAR hxRg) hx2
  have hRgx : rightConjugate R g ≤ centralizer ({(x : G)} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hRge.1.is_comm.comm ⟨y, hy⟩ x))
  obtain ⟨D, hD, hRgD, hDx⟩ :=
    exists_isSylowOf_le_centralizer_of_le hD₁ hD₁x hRg.isPGroup hRgAR hRgx
  have hKgte : TightlyEmbedded (centralizer (rightConjugate A g : Set G)) :=
    hKg ▸ RankTwoSporadic.tightlyEmbedded_rightConjugate' hKte g
  have hNKg : normalizer (centralizer (rightConjugate A g : Set G) : Set G) =
      normalizer (rightConjugate A g : Set G) := by
    rw [← hKg, ← AschbacherTheorem3.rightConjugate_normalizer, hNK,
      AschbacherTheorem3.rightConjugate_normalizer]
  have hDN : D ≤ normalizer (rightConjugate A g : Set G) := by
    intro d hd
    rw [← hNKg]
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hKgte (hRg.le hxRg) hx1'
      hx2 (mem_centralizer_singleton_iff.mp (hDx hd))
  obtain ⟨hRD, ⟨T, hT⟩, hDeq⟩ := sylow_sup_structure hRA hR2 hD
  obtain ⟨H₁, H₂, hH₁T, hH₂T, hH₁e, hH₂e, hH₁c, hH₂c, hsupH, -, hZc, hcomm⟩ :=
    sylow_structure c T
  have hkerc := card_ker_eq c T
  have hTD : (T : Subgroup ↥A).map A.subtype ≤ D := hT ▸ inf_le_left
  have hTZR : ((T : Subgroup ↥A) ⊓ center ↥A).map A.subtype ≤ R := by
    rintro _ ⟨z, ⟨hzT, hzZ⟩, rfl⟩
    have h2 : IsPGroup 2 (zpowers (z : G)) := by
      have := (T.2.to_le (zpowers_le.mpr hzT)).map A.subtype
      rwa [MonoidHom.map_zpowers] at this
    refine mem_of_mem_centralizer_of_isPGroup hR z.2 (mem_centralizer_iff.mpr fun a ha =>
      congrArg Subtype.val (mem_center_iff.mp hzZ ⟨a, ha⟩)) h2
  have hE : ∀ H : Subgroup ↥A, H ≤ T → IsElemAbelian 2 H →
      Nat.card H = 16 * Nat.card c.π.ker →
      H.map A.subtype ⊔ R ≤ rightConjugate A g ⊔ centralizer (rightConjugate A g : Set G) := by
    intro H hHT hHe hHc
    have hH'R : H.map A.subtype ≤ centralizer (R : Set G) := (map_subtype_le H).trans hAR
    have hEe : IsElemAbelian 2 (H.map A.subtype ⊔ R) := isElemAbelian_sup_of_le_centralizer
      (RankTwoSporadic.isElemAbelian_map hHe A.subtype) hRe hH'R
    have hED : H.map A.subtype ⊔ R ≤ D := sup_le ((map_mono hHT).trans hTD) hRD
    have hinf : Nat.card (H.map A.subtype ⊓ R : Subgroup G) ≤ Nat.card c.π.ker := by
      rw [hkerc, ← card_map_of_injective A.subtype_injective]
      refine Subgroup.card_le_of_le fun y hy => ?_
      obtain ⟨⟨h, hh, rfl⟩, hhR⟩ := hy
      refine ⟨h, ⟨hHT hh, mem_center_iff.mpr fun a => ?_⟩, rfl⟩
      exact Subtype.ext (mem_centralizer_iff.mp (hRA hhR) a a.2)
    have hprod := card_sup_mul_card_inf (H := H.map A.subtype) (R := R)
      ((le_centralizer_iff.mp hH'R).trans (Subgroup.centralizer_le_normalizer _))
    rw [card_map_of_injective A.subtype_injective, hHc] at hprod
    have hpos : 0 < Nat.card c.π.ker := Nat.card_pos
    have hcard : 16 * Nat.card (rightConjugate R g) ≤ Nat.card (H.map A.subtype ⊔ R :
        Subgroup G) := by
      rw [hRgcard]
      have h1 : 16 * Nat.card c.π.ker * Nat.card R ≤
          Nat.card (H.map A.subtype ⊔ R : Subgroup G) * Nat.card c.π.ker := by
        rw [← hprod]
        exact Nat.mul_le_mul_left _ hinf
      have h2 : 16 * Nat.card R * Nat.card c.π.ker ≤
          Nat.card (H.map A.subtype ⊔ R : Subgroup G) * Nat.card c.π.ker := by
        calc 16 * Nat.card R * Nat.card c.π.ker = 16 * Nat.card c.π.ker * Nat.card R := by ring
          _ ≤ _ := h1
      exact Nat.le_of_mul_le_mul_right h2 hpos
    exact le_sup_centralizer_of_sixteen_le hE16 hAgperf eAg hRg (hED.trans hDN) hEe hcard
  have hDle : D ≤ rightConjugate A g ⊔ centralizer (rightConjugate A g : Set G) := by
    rw [hDeq, ← hT, ← hsupH, Subgroup.map_sup]
    exact sup_le (sup_le (le_sup_left.trans (hE H₁ hH₁T hH₁e hH₁c))
      (le_sup_left.trans (hE H₂ hH₂T hH₂e hH₂c))) (le_sup_right.trans (hE H₁ hH₁T hH₁e hH₁c))
  obtain ⟨P, hP, hDP⟩ := AschbacherTheorem3.exists_isSylowOf_le hD.isPGroup hDle
  have hCN : rightConjugate A g ⊔ centralizer (rightConjugate A g : Set G) ≤
      normalizer (centralizer (rightConjugate A g : Set G) : Set G) :=
    sup_le ((le_centralizer_iff.mp le_rfl).trans (Subgroup.centralizer_le_normalizer _))
      le_normalizer
  have hPC : P ⊓ centralizer (rightConjugate A g : Set G) = rightConjugate R g :=
    hRg.eq_of_le (le_inf (hRgD.trans hDP) hRg.le) inf_le_right (hP.isPGroup.to_le inf_le_left)
  have hDNR : D ≤ normalizer (rightConjugate R g : Set G) := by
    intro p hp
    have hpP := hDP hp
    have hpC := hCN (hP.le hpP)
    rw [← hPC, mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyP, hyC⟩
      exact ⟨P.mul_mem (P.mul_mem hpP hyP) (P.inv_mem hpP), (mem_normalizer_iff.mp hpC y).mp hyC⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, (mem_normalizer_iff.mp hpC y).mpr h2⟩
      have := P.mul_mem (P.mul_mem (P.inv_mem hpP) h1) hpP
      simpa [mul_assoc] using this
  have hDAR : D ≤ rightConjugate A g ⊔ rightConjugate R g :=
    le_sup_of_le_sup_normalizer hRg hD.isPGroup hDNR hDle
  have hRgc : ∀ u ∈ rightConjugate R g, ∀ v ∈ rightConjugate R g, u * v = v * u :=
    fun u hu v hv => congrArg Subtype.val (hRge.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hDC : D ≤ centralizer (rightConjugate R g : Set G) := by
    refine hDAR.trans (sup_le (le_centralizer_iff.mp hRg.le) fun y hy => ?_)
    exact mem_centralizer_iff.mpr fun z hz => hRgc z hz y hy
  have hRgZ : rightConjugate R g ≤ centerIn D := le_inf hRgD (le_centralizer_iff.mp hDC)
  have hRZ : R ≤ centerIn D :=
    le_inf hRD (le_centralizer_iff.mp (hD.le.trans (sup_le hAR hRR)))
  have hRRgcard : Nat.card (R ⊔ rightConjugate R g : Subgroup G) = Nat.card R * Nat.card R := by
    rw [AschbacherTheorem3.card_sup_of_le_normalizer
      (hgc.trans (Subgroup.centralizer_le_normalizer _)) hRRg, hRgcard]
  have hZTA := centerIn_map_subtype_le (T : Subgroup ↥A)
  have hZD : centerIn D ≤ centerIn ((T : Subgroup ↥A).map A.subtype) ⊔ R := by
    rw [hT]
    exact centerIn_le_sup_of_le_sup hRA hRD hD.le
  have hZTAcard : Nat.card (centerIn ((T : Subgroup ↥A).map A.subtype)) ≤
      4 * Nat.card c.π.ker := by
    rw [← hZc, ← card_map_of_injective A.subtype_injective]
    exact Subgroup.card_le_of_le hZTA
  have hker_le : Nat.card c.π.ker ≤
      Nat.card (centerIn ((T : Subgroup ↥A).map A.subtype) ⊓ R : Subgroup G) := by
    rw [hkerc, ← card_map_of_injective A.subtype_injective]
    exact Subgroup.card_le_of_le (le_inf (map_inf_center_le_centerIn _) hTZR)
  have hZDcard : Nat.card (centerIn D) ≤ 4 * Nat.card R := by
    have hZR : R ≤ normalizer (centerIn ((T : Subgroup ↥A).map A.subtype) : Set G) :=
      (le_centralizer_iff.mp
        (((inf_le_left : centerIn ((T : Subgroup ↥A).map A.subtype) ≤ _).trans
          (map_subtype_le _)).trans hAR)).trans (Subgroup.centralizer_le_normalizer _)
    have hprod := card_sup_mul_card_inf hZR
    have hpos : 0 < Nat.card (centerIn ((T : Subgroup ↥A).map A.subtype) ⊓ R :
        Subgroup G) := Nat.card_pos
    have h1 : Nat.card (centerIn ((T : Subgroup ↥A).map A.subtype) ⊔ R : Subgroup G) *
        Nat.card (centerIn ((T : Subgroup ↥A).map A.subtype) ⊓ R : Subgroup G) ≤
        4 * Nat.card R *
          Nat.card (centerIn ((T : Subgroup ↥A).map A.subtype) ⊓ R : Subgroup G) := by
      rw [hprod]
      calc Nat.card (centerIn ((T : Subgroup ↥A).map A.subtype)) * Nat.card R
          ≤ 4 * Nat.card c.π.ker * Nat.card R := Nat.mul_le_mul_right _ hZTAcard
        _ ≤ 4 * Nat.card (centerIn ((T : Subgroup ↥A).map A.subtype) ⊓ R : Subgroup G) *
            Nat.card R :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hker_le)
        _ = 4 * Nat.card R *
            Nat.card (centerIn ((T : Subgroup ↥A).map A.subtype) ⊓ R : Subgroup G) := by ring
    exact (Subgroup.card_le_of_le hZD).trans (Nat.le_of_mul_le_mul_right h1 hpos)
  have hR4 : Nat.card R = 4 := by
    have h1 : Nat.card R * Nat.card R ≤ 4 * Nat.card R := by
      rw [← hRRgcard]
      exact (Subgroup.card_le_of_le (sup_le hRZ hRgZ)).trans hZDcard
    have h2 : Nat.card R ≤ 4 := Nat.le_of_mul_le_mul_right h1 Nat.card_pos
    have h3 : 4 ∣ Nat.card R := by
      have h4 := RankTwoSporadic.four_dvd_card_of_one_lt_pRank
        (K := centralizer (A : Set G)) (by have := hB.hyp.rank; omega)
      rw [hR.card_eq]
      have h5 : 2 ≤ (Nat.card (centralizer (A : Set G))).factorization 2 :=
        (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp (by simpa using h4)
      have h6 : 2 ^ 2 ∣ 2 ^ (Nat.card (centralizer (A : Set G))).factorization 2 :=
        pow_dvd_pow 2 h5
      simpa using h6
    have h7 : 0 < Nat.card R := Nat.card_pos
    omega
  have hZeq : R ⊔ rightConjugate R g = centerIn D := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hRZ hRgZ)
    rw [hRRgcard, hR4]
    have := hZDcard
    rw [hR4] at this
    omega
  exact ⟨hR4, D, hD, hRgD, hDAR, hZeq.symm⟩

theorem step13L34_of (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Base G A → TypeL34 (rankTwoQuot A) →
      ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
      ∀ g : G, g ∉ normalizer (A : Set G) → rightConjugate R g ≤ centralizer (R : Set G) →
        Nat.card R = 4 ∧
          (∃ D : Subgroup G, IsSylowOf 2 D (A ⊔ R) ∧ rightConjugate R g ≤ centerIn D ∧
            centerIn D ≤ rightConjugate R g ⊔ R ⊔ centerIn A) ∧
          (Odd (Nat.card (center A)) → rightConjugate R g ⊓ A = ⊥) := by
  intro G _ _ A hB hL R hR g hg hgc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hR4, D, hD, hRgD, hDAR, hZeq⟩ := exists_sylow_centerIn_eq h11 hE16 hB hL hR hg hgc
  refine ⟨hR4, ⟨D, hD, hZeq ▸ le_sup_right, ?_⟩, fun hodd => ?_⟩
  · rw [hZeq]
    exact sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)
  obtain ⟨hRe, -, -⟩ := h11 G A hB R hR
  obtain ⟨c⟩ := l34Cover_of_base h11 hB hL
  have hKg : rightConjugate (centralizer (A : Set G)) g =
      centralizer (rightConjugate A g : Set G) := AschbacherTheorem3.rightConjugate_centralizer A g
  have hRg : IsSylowOf 2 (rightConjugate R g) (centralizer (rightConjugate A g : Set G)) :=
    hKg ▸ AschbacherTheorem3.isSylowOf_rightConjugate hR g
  have hRge : IsElemAbelian 2 (rightConjugate R g) := isElemAbelian_rightConjugate hRe g
  have hRgc : ∀ u ∈ rightConjugate R g, ∀ v ∈ rightConjugate R g, u * v = v * u :=
    fun u hu v hv => congrArg Subtype.val (hRge.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hDC : D ≤ centralizer (rightConjugate R g : Set G) := by
    refine hDAR.trans (sup_le (le_centralizer_iff.mp hRg.le) fun y hy => ?_)
    exact mem_centralizer_iff.mpr fun z hz => hRgc z hz y hy
  obtain ⟨-, ⟨T, hT⟩, -⟩ := sylow_sup_structure hR.le hR.isPGroup hD
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcomm⟩ := sylow_structure c T
  have hTD : (T : Subgroup ↥A).map A.subtype ≤ D := hT ▸ inf_le_left
  rw [eq_bot_iff]
  rintro y ⟨hyRg, hyA⟩
  rw [mem_bot]
  by_contra hy1
  have hyT : y ∈ (T : Subgroup ↥A).map A.subtype := hT ▸ ⟨hRgD hyRg, hyA⟩
  have hyZ : y ∈ centerIn ((T : Subgroup ↥A).map A.subtype) := by
    refine ⟨hyT, ?_⟩
    show y ∈ centralizer (((T : Subgroup ↥A).map A.subtype : Subgroup G) : Set G)
    rw [mem_centralizer_iff]
    intro s hs
    exact mem_centralizer_iff.mp ((le_centralizer_iff.mp hDC) hyRg) s (hTD hs)
  have hyAg : y ∈ rightConjugate A g := by
    have h1 := centerIn_map_subtype_le (T : Subgroup ↥A) hyZ
    rw [← hcomm hB.hyp.standard.1.1, map_commutator] at h1
    exact commutator_le_of_le_sup hRg.le hRgc hDAR (commutator_mono hTD hTD h1)
  have hyK : g * y * g⁻¹ ∈ centralizer (A : Set G) := by
    have : y ∈ rightConjugate (centralizer (A : Set G)) g := hKg ▸ hRg.le hyRg
    exact (mem_rightConjugate_iff _ _ _).mp this
  have hyA' : g * y * g⁻¹ ∈ A := (mem_rightConjugate_iff _ _ _).mp hyAg
  have hy2 : (g * y * g⁻¹) ^ 2 = 1 := by
    have h := hRge.2 y hyRg
    rw [sq] at h ⊢
    calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  let z : ↥(center ↥A) := ⟨⟨g * y * g⁻¹, hyA'⟩,
    mem_center_iff.mpr fun a => Subtype.ext (mem_centralizer_iff.mp hyK a a.2)⟩
  have hz1 : z ≠ 1 := by
    intro h
    apply hy1
    have h' : g * y * g⁻¹ = 1 := congrArg (fun w : ↥(center ↥A) => ((w : ↥A) : G)) h
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group
  have hz2 : z ^ 2 = 1 := Subtype.ext (Subtype.ext hy2)
  have hdvd := orderOf_dvd_natCard z
  rw [orderOf_eq_prime hz2 hz1] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end Core

end CFSG.ComponentClassification.AS81

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer b3Lie_center_eq_bot)

private theorem nontrivial_of_tyF_three {X : Type} [Group X] (h : catalogIs X (tyF 3)) :
    Nontrivial X := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases i with _ | _ | ⟨⟨l, hv⟩⟩ | _ <;> try exact (hi : False).elim
  cases l
  case A r q => exact T123C.nontrivial_of_lie_A r q hv e
  case twistedA r q => exact T123C.nontrivial_of_lie_twistedA r q hv e
  all_goals exact (hi : False).elim

private theorem inj_conj_of_center_eq_bot {R : Type} [Group R] (hZ : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro a ha
  refine Subgroup.mem_center_iff.2 fun g => ?_
  have h := congrArg (fun α : MulAut R => α g) (MonoidHom.mem_ker.1 ha)
  simp only [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at h
  exact h.symm

private theorem map_fixSubgroup_congr_eq {P R : Type} [Group P] [Group R] (Φ : P ≃* R)
    {β : MulAut P} {r : R} (hr : MulAut.conj r = MulAut.congr Φ β) :
    (fixSubgroup β).map Φ.toMonoidHom = Subgroup.centralizer ({r} : Set R) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff]
  change β (Φ.symm y) = Φ.symm y ↔ _
  have hy : Φ (β (Φ.symm y)) = r * y * r⁻¹ := (congrArg (fun α : MulAut R => α y) hr).symm
  rw [← Φ.injective.eq_iff, MulEquiv.apply_symm_apply, hy, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem SG.exists_component_tyF_conj {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hcat : catalogIs (PSimple 3 K) (tyF 3))
    {R : Type} [Group R] (Φ : PSimple 3 S ≃* R) {d : Ω} (hdD : d ∈ D)
    (hdx : d ∉ Subgroup.zpowers x) (hdN : d ∈ Subgroup.normalizer (S : Set Ω)) {r : R}
    (hr : MulAut.conj r = MulAut.congr Φ (chevAut 3 S ⟨d, hdN⟩)) :
    ∃ J : Subgroup R, IsComponentOf J (Subgroup.centralizer ({r} : Set R)) ∧
      catalogIs (↥J ⧸ Subgroup.center ↥J) (tyF 3) := by
  have hc := h.cfg
  obtain ⟨-, -, -, -, -, hKc, -⟩ := hc.std
  have hKS : K ≤ S := hKc.1.trans inf_le_left
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKc.2.2
  haveI : Group.IsPerfect ↥K := ⟨hKq.1⟩
  set g : ↥K →* R := Φ.toMonoidHom.comp ((chevQuotHom 3 S).comp (Subgroup.inclusion hKS))
    with hg
  have hJ : ((K.subgroupOf S).map (chevQuotHom 3 S)).map Φ.toMonoidHom = g.range := by
    rw [hg, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.inclusion_range]
  obtain ⟨-, hJc⟩ := SG.isComponentOf_fixSubgroup_chevAut h hdD hdx hdN
  refine ⟨g.range, ?_, ?_⟩
  · rw [← hJ, ← map_fixSubgroup_congr_eq Φ hr]
    exact ⟨Subgroup.map_mono hJc.1, hJc.2.1.map _,
      hJc.2.2.of_mulEquiv (Subgroup.equivMapOfInjective _ Φ.toMonoidHom Φ.injective).symm⟩
  have hker : g.rangeRestrict.ker ≤ Subgroup.center ↥K := fun k hk => by
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hk
    have hk' : Subgroup.inclusion hKS k ∈ Subgroup.center ↥S := by
      rw [← S171.ker_chevQuotHom_eq_center' hc.prime hc.comp hc.quasi, MonoidHom.mem_ker]
      exact Φ.map_eq_one_iff.1 hk
    refine Subgroup.mem_center_iff.2 fun k' => Subtype.ext ?_
    exact congrArg (fun s : ↥S => (s : Ω))
      (Subgroup.mem_center_iff.1 hk' (Subgroup.inclusion hKS k'))
  haveI := nontrivial_of_tyF_three hcat
  have hne : GLAPPrimeCore 3 ↥K ≠ ⊤ := fun htop => by
    have h1 : ∀ y : PQuot 3 K, y = 1 := fun y => by
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
      exact (QuotientGroup.eq_one_iff k).2 (by rw [htop]; exact Subgroup.mem_top k)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PSimple 3 K)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [h1 a, h1 b])
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat
  exact ⟨i, hi, ⟨(CFSG.ComponentClassification.PerfectCentralQuotient.equivalence
    g.rangeRestrict g.rangeRestrict_surjective hker).symm.trans ((S172A.pSimpleEquivCenterQuot 3
      (le_center_of_normal_of_isQuasisimple hKq inferInstance hne)).trans f)⟩⟩

theorem SG.false_of_conj_centralizer {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hcat : catalogIs (PSimple 3 K) (tyF 3))
    (hB : Nat.card B = 3 ^ 4) {R : Type} [Group R] [IsSimpleGroup R]
    (hnc : ∃ a b : R, a * b ≠ b * a) (Φ : PSimple 3 S ≃* R)
    (hΦ : ∀ (b : Ω) (hbN : b ∈ Subgroup.normalizer (S : Set Ω)), b ∈ B →
      MulAut.congr Φ (chevAut 3 S ⟨b, hbN⟩) ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hpl : ∀ r : R, r ^ 3 = 1 → PerfectInLayer (MulAut.conj r))
    (hY : ∀ X : Subgroup R, IsElemAbelian 3 X → Nat.card X = 3 ^ 3 → ∀ r ∈ X, r ≠ 1 →
      (∃ J : Subgroup R, IsComponentOf J (Subgroup.centralizer ({r} : Set R)) ∧
        catalogIs (↥J ⧸ Subgroup.center ↥J) (tyF 3)) →
      ∃ Y ≤ X, r ∈ Y ∧ Nat.card Y = 3 ^ 2 ∧ ∃ A : Subgroup R,
        A ≤ Subgroup.centralizer (Y : Set R) ∧ IsSimpleGroup A ∧ (∃ a b : A, a * b ≠ b * a) ∧
        3 ∣ Nat.card A) : False := by
  have hc := h.cfg
  have hSN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 hc.normal) ▸ Subgroup.mem_top g
  have hinj := inj_conj_of_center_eq_bot (b3Lie_center_eq_bot hnc)
  obtain ⟨hel, hcard⟩ := SG.card_map_chevAut h hB
  set XA := ((B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S)).map
    (MulAut.congr Φ).toMonoidHom with hXA
  have hXAc : Nat.card XA = 3 ^ 3 := by
    rw [hXA, Subgroup.card_map_of_injective (MulAut.congr Φ).injective, hcard]
  have hXAr : XA ≤ (MulAut.conj : R →* MulAut R).range := by
    rintro _ ⟨_, ⟨⟨b, hbN⟩, hb, rfl⟩, rfl⟩
    obtain ⟨r, hr⟩ := hΦ b hbN hb
    exact ⟨r, hr⟩
  have hXe : IsElemAbelian 3 (XA.comap MulAut.conj) :=
    (hel.map (MulAut.congr Φ).toMonoidHom).comap hinj
  have hXc : Nat.card (XA.comap MulAut.conj) = 3 ^ 3 := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hXAr, hXAc]
  obtain ⟨d, hdD, hdx⟩ := SG.exists_mem_D_not_zpowers h
  obtain ⟨hDB, -⟩ := hc.std
  have hdN := hSN (hDB hdD)
  obtain ⟨r, hr⟩ := hΦ d hdN (hDB hdD)
  have hrX : r ∈ XA.comap MulAut.conj := by
    rw [Subgroup.mem_comap, hr]
    exact ⟨_, ⟨⟨d, hdN⟩, hDB hdD, rfl⟩, rfl⟩
  have hr1 : r ≠ 1 := by
    rintro rfl
    refine hdx ((SG.chevAut_eq_one_iff_mem_zpowers h (hDB hdD) hdN).1
      ((MulAut.congr Φ).injective ?_))
    rw [← hr, map_one, map_one]
  obtain ⟨Y, hYX, hrY, hYc, A, hAY, hAs, hAnc, hA3⟩ := hY _ hXe hXc r hrX hr1
    (SG.exists_component_tyF_conj h hcat Φ hdD hdx hdN hr)
  have hfix : ∀ y ∈ Y, A ≤ fixSubgroup (MulAut.conj y) := fun y hy a ha => by
    change (MulAut.conj y) a = a
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_iff.1 (hAY ha) y hy
  have hYXA : Y.map MulAut.conj ≤ XA := (Subgroup.map_mono hYX).trans (Subgroup.map_comap_le _ _)
  have hidx := Subgroup.relIndex_mul_card (Y.map MulAut.conj) XA
  rw [inf_of_le_left hYXA, Subgroup.card_map_of_injective hinj, hYc, hXAc] at hidx
  have hY3 : (Y.map MulAut.conj).relIndex XA ≤ 3 := by omega
  haveI := hAs
  refine SG.false_of_simple_fix_congr h hcat hB Φ hdD hdx hdN (hr ▸ hpl r (hXe.2 r hrX)) hAnc
    hA3 (hr ▸ hfix r hrY) (Y := Y.map MulAut.conj) hY3 ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hfix y hy

end CFSG.LocalAnalysis.GLTheoremA.S265

end

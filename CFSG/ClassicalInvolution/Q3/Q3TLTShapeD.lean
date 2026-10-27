module

public import CFSG.ClassicalInvolution.Q3.Q3TLTInner
public import CFSG.ClassicalInvolution.Q3.Q3TLTShapeAb

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

namespace TightDatum

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
  (d : TightDatum R S t)

@[expose] noncomputable def oddKer : Subgroup d.act.ker :=
  (oddCore (Subgroup.centralizer ({t} : Set G))).subgroupOf d.act.ker

noncomputable instance oddKer_normal : d.oddKer.Normal := by
  unfold oddKer
  infer_instance

noncomputable abbrev Dbar : Type _ := ↥d.act.ker ⧸ d.oddKer

noncomputable abbrev toDbar : ↥d.act.ker →* d.Dbar := QuotientGroup.mk' d.oddKer

theorem mem_oddKer_iff (y : ↥d.act.ker) :
    y ∈ d.oddKer ↔ (y : Subgroup.centralizer ({t} : Set G)) ∈
      oddCore (Subgroup.centralizer ({t} : Set G)) :=
  Iff.rfl

theorem map_conjNormal_oddKer (c : Subgroup.centralizer ({t} : Set G)) :
    d.oddKer.map (MulAut.conjNormal (H := d.act.ker) c).toMonoidHom = d.oddKer := by
  have hn : (oddCore (Subgroup.centralizer ({t} : Set G))).Normal := inferInstance
  ext y
  constructor
  · rintro ⟨n, hn', rfl⟩
    have h1 := (d.mem_oddKer_iff n).mp hn'
    rw [mem_oddKer_iff]
    have := hn.conj_mem _ h1 c
    simpa [MulAut.conjNormal_apply] using this
  · intro hy
    have hy' := (d.mem_oddKer_iff y).mp hy
    refine ⟨(MulAut.conjNormal c).symm y, ?_, by simp⟩
    change (MulAut.conjNormal c).symm y ∈ d.oddKer
    rw [mem_oddKer_iff]
    have := hn.conj_mem _ hy' c⁻¹
    simpa [MulAut.conjNormal_symm_apply] using this

@[expose] noncomputable def dbarAct : Subgroup.centralizer ({t} : Set G) →* MulAut d.Dbar where
  toFun c := QuotientGroup.congr d.oddKer d.oddKer (MulAut.conjNormal (H := d.act.ker) c)
    (d.map_conjNormal_oddKer c)
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H y => simp [QuotientGroup.congr_mk]
  map_mul' c c' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [MulAut.mul_apply]
      erw [QuotientGroup.congr_mk, QuotientGroup.congr_mk]
      simp

theorem dbarAct_mk (c : Subgroup.centralizer ({t} : Set G)) (y : ↥d.act.ker) :
    d.dbarAct c (QuotientGroup.mk y) =
      QuotientGroup.mk (MulAut.conjNormal (H := d.act.ker) c y) :=
  QuotientGroup.congr_mk d.oddKer d.oddKer (MulAut.conjNormal (H := d.act.ker) c)
    (d.map_conjNormal_oddKer c) y

omit [Finite G] in
theorem le_normalizer_oddCoreImg' [Finite G] (C : Subgroup G) :
    C ≤ Subgroup.normalizer (oddCoreImg C : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun ho => conj_mem_oddCoreImg (Subgroup.le_normalizer hg) ho, fun ho => ?_⟩
  have := conj_mem_oddCoreImg (Subgroup.le_normalizer (C.inv_mem hg)) ho
  simpa [mul_assoc] using this

theorem oddCore_le_ker_act : oddCore (Subgroup.centralizer ({t} : Set G)) ≤ d.act.ker := by
  intro y hy
  rw [MonoidHom.mem_ker]
  refine (d.act_eq_one_iff y.2).mpr ?_
  intro r hr
  have hyC : (y : G) ∈ oddCoreImg (Subgroup.centralizer ({t} : Set G)) :=
    (mem_oddCore_iff_coe_mem_oddCoreImg _ y).mp hy
  have hrC : r ∈ Subgroup.centralizer ({t} : Set G) := d.cent hr
  have h1 : ⁅(y : G), r⁆ ∈ R := by
    have : (y : G) * r * (y : G)⁻¹ ∈ R := d.conj_mem y.2 hr
    rw [commutatorElement_def]
    exact R.mul_mem this (R.inv_mem hr)
  have h2 : ⁅(y : G), r⁆ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set G)) := by
    have h3 : r * (y : G)⁻¹ * r⁻¹ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set G)) :=
      conj_mem_oddCoreImg (Subgroup.le_normalizer hrC) ((oddCoreImg _).inv_mem hyC)
    have h4 := (oddCoreImg (Subgroup.centralizer ({t} : Set G))).mul_mem hyC h3
    have h5 : ⁅(y : G), r⁆ = (y : G) * (r * (y : G)⁻¹ * r⁻¹) := by
      rw [commutatorElement_def]; group
    rw [h5]
    exact h4
  have hTR : oddCoreImg (Subgroup.centralizer ({t} : Set G)) ⊓ R ≤ R := inf_le_right
  have hnorm : ((oddCoreImg (Subgroup.centralizer ({t} : Set G)) ⊓ R).subgroupOf R).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hTR).mpr fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hgC : g ∈ Subgroup.normalizer
        (oddCoreImg (Subgroup.centralizer ({t} : Set G)) : Set G) :=
      le_normalizer_oddCoreImg' _ (d.cent hg)
    have hA := Subgroup.mem_normalizer_iff.mp hgC h
    have hB := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) h
    exact ⟨fun hh => ⟨hA.mp hh.1, hB.mp hh.2⟩, fun hh => ⟨hA.mpr hh.1, hB.mpr hh.2⟩⟩
  have hodd : Odd (Nat.card
      ((oddCoreImg (Subgroup.centralizer ({t} : Set G)) ⊓ R).subgroupOf R)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv]
    exact (odd_natCard_oddCoreImg _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hle : (oddCoreImg (Subgroup.centralizer ({t} : Set G)) ⊓ R).subgroupOf R ≤ oddCore ↥R :=
    le_sSup ⟨hnorm, hodd⟩
  have hmem : (⟨⁅(y : G), r⁆, h1⟩ : R) ∈
      (oddCoreImg (Subgroup.centralizer ({t} : Set G)) ⊓ R).subgroupOf R := ⟨h2, h1⟩
  exact (mem_oddCore_iff_coe_mem_oddCoreImg R _).mp (hle hmem)

theorem map_oddKer_eq :
    d.oddKer.map d.act.ker.subtype = oddCore (Subgroup.centralizer ({t} : Set G)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hy
    exact ⟨⟨y, d.oddCore_le_ker_act hy⟩, hy, rfl⟩

omit [Finite G] in
theorem t_mem_centralizer : t ∈ Subgroup.centralizer ({t} : Set G) :=
  Subgroup.mem_centralizer_iff.mpr (by simp)

theorem t_mem_ker : (⟨t, t_mem_centralizer⟩ : Subgroup.centralizer ({t} : Set G)) ∈
    d.act.ker := by
  rw [d.mem_ker_act_iff]
  intro r hr
  have h := Subgroup.mem_centralizer_iff.mp (d.cent hr) t (Set.mem_singleton t)
  have h1 : ⁅t, r⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h
  show ⁅t, r⁆ ∈ oddCoreImg R
  rw [h1]
  exact (oddCoreImg R).one_mem

@[expose] noncomputable def tbar : d.Dbar :=
  QuotientGroup.mk ⟨⟨t, t_mem_centralizer⟩, d.t_mem_ker⟩

theorem dbarAct_tbar (c : Subgroup.centralizer ({t} : Set G)) : d.dbarAct c d.tbar = d.tbar := by
  rw [tbar, dbarAct_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  have h := Subgroup.mem_centralizer_iff.mp c.2 t (Set.mem_singleton t)
  show (c : G) * t * (c : G)⁻¹ = t
  rw [mul_inv_eq_iff_eq_mul]
  exact h.symm

theorem tbar_pow_two : d.tbar ^ 2 = 1 := by
  rw [tbar, ← QuotientGroup.mk_pow]
  have h1 : (⟨⟨t, t_mem_centralizer⟩, d.t_mem_ker⟩ : ↥d.act.ker) ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have h2 : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [d.order] at this
    simpa using h2
  rw [h1]
  exact QuotientGroup.mk_one _

theorem oddCore_dbar_eq_bot : oddCore d.Dbar = ⊥ := by
  have hKchar : (oddCore d.Dbar).Characteristic := oddCore_characteristic_of_finite d.Dbar
  set K := oddCore d.Dbar with hK
  set Kt : Subgroup ↥d.act.ker := K.comap d.toDbar with hKt
  set Kc : Subgroup (Subgroup.centralizer ({t} : Set G)) := Kt.map d.act.ker.subtype with hKc
  have hKcn : Kc.Normal := by
    refine ⟨fun y hy c => ?_⟩
    obtain ⟨y', hy', rfl⟩ := hy
    refine ⟨MulAut.conjNormal (H := d.act.ker) c y', ?_, by simp [MulAut.conjNormal_apply]⟩
    change d.toDbar (MulAut.conjNormal (H := d.act.ker) c y') ∈ K
    have h1 : d.toDbar (MulAut.conjNormal (H := d.act.ker) c y') = d.dbarAct c (d.toDbar y') :=
      (d.dbarAct_mk c y').symm
    rw [h1]
    have h2 : d.dbarAct c (d.toDbar y') ∈ K.map (d.dbarAct c).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hy'
    rwa [Subgroup.characteristic_iff_map_eq.mp hKchar (d.dbarAct c)] at h2
  have hOddKer : Odd (Nat.card d.toDbar.ker) := by
    rw [QuotientGroup.ker_mk']
    have hle : d.oddKer.map d.act.ker.subtype ≤ oddCore (Subgroup.centralizer ({t} : Set G)) := by
      rintro x ⟨y, hy, rfl⟩
      exact hy
    have hcard : Nat.card d.oddKer = Nat.card (d.oddKer.map d.act.ker.subtype) :=
      (Subgroup.card_map_of_injective d.act.ker.subtype_injective).symm
    rw [hcard]
    exact (QuaternionStructure.odd_natCard_oddCore _).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hOddKt : Odd (Nat.card Kt) :=
    odd_natCard_comap_of_odd_ker d.toDbar hOddKer K (QuaternionStructure.odd_natCard_oddCore _)
  have hOddKc : Odd (Nat.card Kc) := by
    rw [hKc, Subgroup.card_map_of_injective d.act.ker.subtype_injective]
    exact hOddKt
  have hKcle : Kc ≤ oddCore (Subgroup.centralizer ({t} : Set G)) := le_sSup ⟨hKcn, hOddKc⟩
  refine eq_bot_iff.mpr fun k hk => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective k
  have hyKt : y ∈ Kt := hk
  have hyKc : (y : Subgroup.centralizer ({t} : Set G)) ∈ Kc := ⟨y, hyKt, rfl⟩
  have hyN : y ∈ d.oddKer := (d.mem_oddKer_iff y).mpr (hKcle hyKc)
  exact (QuotientGroup.eq_one_iff y).mpr hyN

theorem isPGroup_two_fitting_dbar : IsPGroup 2 (genFittingFitting d.Dbar) :=
  isPGroup_two_genFittingFitting d.oddCore_dbar_eq_bot

theorem innerAt_iff_dbar_inner (c : Subgroup.centralizer ({t} : Set G)) :
    (∃ dd ∈ d.act.ker, ∀ y ∈ d.act.ker, c * y * c⁻¹ * (dd * y * dd⁻¹)⁻¹ ∈
        oddCore (Subgroup.centralizer ({t} : Set G))) ↔
      ∃ g : d.Dbar, ∀ q : d.Dbar, d.dbarAct c q = g * q * g⁻¹ := by
  constructor
  · rintro ⟨dd, hdd, h⟩
    refine ⟨QuotientGroup.mk ⟨dd, hdd⟩, fun q => ?_⟩
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [d.dbarAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq_iff_div_mem, d.mem_oddKer_iff]
      have := h y y.2
      simpa [MulAut.conjNormal_apply, div_eq_mul_inv] using this
  · rintro ⟨g, hg⟩
    obtain ⟨dd, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨(dd : Subgroup.centralizer ({t} : Set G)), dd.2, fun y hy => ?_⟩
    have h1 := hg (QuotientGroup.mk ⟨y, hy⟩)
    rw [d.dbarAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq_iff_div_mem, d.mem_oddKer_iff] at h1
    simpa [MulAut.conjNormal_apply, div_eq_mul_inv] using h1

end TightDatum

end CFSG.ClassicalInvolution.Q3

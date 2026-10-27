module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTGen
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

@[expose] def fixSub {T : Type} [Group T] (α : MulAut T) : Subgroup T where
  carrier := {t | α t = t}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv, ha]

theorem mem_fixSub {T : Type} [Group T] {α : MulAut T} {t : T} : t ∈ fixSub α ↔ α t = t :=
  Iff.rfl

theorem fixSub_conj {T : Type} [Group T] (s : T) :
    fixSub (MulAut.conj s) = Subgroup.centralizer ({s} : Set T) := by
  ext t
  rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    have : s * t = t * s := by
      calc s * t = s * t * s⁻¹ * s := by group
        _ = t * s := by rw [h]
    exact this.symm
  · intro h
    rw [← h]
    group

@[expose] def piJ {H : Type} [Group H] (J : Subgroup H) : ↥J →* PSimple 3 J :=
  (QuotientGroup.mk' (Subgroup.center (PQuot 3 J))).comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))

theorem exists_conj_equiv {H : Type} [Group H] {J : Subgroup H} {d : H}
    (hdN : d ∈ Subgroup.normalizer (J : Set H)) :
    ∃ c : ↥J ≃* ↥J, ∀ x : ↥J, (c x : H) = d * x * d⁻¹ := by
  have hdmem : ∀ x : H, x ∈ J ↔ d * x * d⁻¹ ∈ J := fun x => Subgroup.mem_normalizer_iff.mp hdN x
  let cH : H ≃* H := MulAut.conj d
  have hJmap : J.map (cH : H →* H) = J := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hdmem x).mp hx
    · intro hy
      refine ⟨d⁻¹ * y * d, (hdmem _).mpr ?_, ?_⟩
      · have : d * (d⁻¹ * y * d) * d⁻¹ = y := by group
        rw [this]
        exact hy
      · show d * (d⁻¹ * y * d) * d⁻¹ = y
        group
  exact ⟨(MulEquiv.subgroupMap cH J).trans (MulEquiv.subgroupCongr hJmap), fun x => rfl⟩

theorem eq_of_central_valued {H : Type} [Group H] {J : Subgroup H} (hJq : CFSG.Open.IsQuasisimple ↥J)
    (c : ↥J ≃* ↥J) (hz : ∀ x : ↥J, c x * x⁻¹ ∈ Subgroup.center ↥J) : ∀ x : ↥J, c x = x := by
  let ζ : ↥J →* ↥(Subgroup.center ↥J) :=
    MonoidHom.mk' (fun x => ⟨c x * x⁻¹, hz x⟩) (by
      intro x y
      apply Subtype.ext
      have hcen : ∀ g : ↥J, g * (c y * y⁻¹) = (c y * y⁻¹) * g :=
        fun g => Subgroup.mem_center_iff.mp (hz y) g
      calc c (x * y) * (x * y)⁻¹ = c x * (c y * y⁻¹) * x⁻¹ := by rw [map_mul]; group
        _ = c x * ((c y * y⁻¹) * x⁻¹) := by group
        _ = c x * (x⁻¹ * (c y * y⁻¹)) := by rw [hcen x⁻¹]
        _ = (c x * x⁻¹) * (c y * y⁻¹) := by group)
  have hker : commutator ↥J ≤ ζ.ker := by
    show ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ ≤ ζ.ker
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hz a) (c b * b⁻¹)).symm
  rw [hJq.1] at hker
  intro x
  have hx : ζ x = 1 := hker (Subgroup.mem_top x)
  have hx' : c x * x⁻¹ = 1 := congrArg Subtype.val hx
  exact mul_inv_eq_one.mp hx'

theorem comp_fix {H : Type} [Group H] {J : Subgroup H} {d : H} {Q : TauCeti.CFSGIndex → Prop}
    {T : Type} [Group T] [Nontrivial T]
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hdN : d ∈ Subgroup.normalizer (J : Set H)) (hd3 : d ^ 3 = 1)
    (hdJ : d ∉ Subgroup.centralizer (J : Set H)) (e0 : PSimple 3 J ≃* T)
    (c : ↥J ≃* ↥J) (hc : ∀ x : ↥J, (c x : H) = d * x * d⁻¹)
    (hfix : ∀ α : MulAut T, (∀ x : ↥J, e0 (piJ J (c x)) = α (e0 (piJ J x))) → α ^ 3 = 1 → α ≠ 1 →
      ∀ L : Subgroup T, CFSG.Open.IsComponentOf L (fixSub α) →
        catalogIs (↥L ⧸ Subgroup.center ↥L) Q)
    (K : Subgroup H) (hK : CFSG.Open.IsComponentOf K (J ⊓ Subgroup.centralizer ({d} : Set H))) :
    catalogIs (↥K ⧸ Subgroup.center ↥K) Q := by
  haveI : Nontrivial (PSimple 3 J) := e0.symm.injective.nontrivial
  have hπs : Function.Surjective (piJ J) :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hNtop : GLAPPrimeCore 3 ↥J ≠ ⊤ := by
    intro hN
    have hπ1 : ∀ x : ↥J, piJ J x = 1 := by
      intro x
      have hx : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) x : ↥J ⧸ GLAPPrimeCore 3 ↥J) = 1 :=
        (QuotientGroup.eq_one_iff x).mpr (by rw [hN]; exact Subgroup.mem_top x)
      show (QuotientGroup.mk' (Subgroup.center (PQuot 3 J)))
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) x) = 1
      rw [hx, map_one]
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PSimple 3 J)
    obtain ⟨x, hx⟩ := hπs a
    obtain ⟨y, hy⟩ := hπs b
    exact hab (by rw [← hx, ← hy, hπ1 x, hπ1 y])
  have hπcenter : ∀ z ∈ Subgroup.center ↥J, piJ J z = 1 := by
    intro z hz
    have hzc : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) z : PQuot 3 J) ∈
        Subgroup.center (PQuot 3 J) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]
    show (QuotientGroup.mk' (Subgroup.center (PQuot 3 J)))
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) z) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hzc
  have hker : ∀ x : ↥J, piJ J x = 1 ↔ x ∈ Subgroup.center ↥J := fun x =>
    ⟨fun h => mem_center_of_quotQuot_eq_one hJq (GLAPPrimeCore 3 ↥J) hNtop x h, hπcenter x⟩
  let φ : ↥J →* T := e0.toMonoidHom.comp (piJ J)
  have hφs : Function.Surjective φ := e0.surjective.comp hπs
  have hφ1 : ∀ x : ↥J, φ x = 1 ↔ piJ J x = 1 := fun x => by
    show e0 (piJ J x) = 1 ↔ piJ J x = 1
    exact e0.map_eq_one_iff
  have hφk : ∀ x : ↥J, φ x = 1 → x ∈ Subgroup.center ↥J := fun x h => (hker x).mp ((hφ1 x).mp h)
  have hkerZ : φ.ker = Subgroup.center ↥J := by
    ext x
    rw [MonoidHom.mem_ker, hφ1, hker]
  let ε : (↥J ⧸ Subgroup.center ↥J) ≃* T :=
    (QuotientGroup.quotientMulEquivOfEq hkerZ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hε : ∀ x : ↥J, ε (QuotientGroup.mk x) = φ x := fun x => rfl
  let qJ : (↥J ⧸ Subgroup.center ↥J) ≃* (↥J ⧸ Subgroup.center ↥J) :=
    QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J) c (Subgroup.map_center_eq c)
  let α : MulAut T := ε.symm.trans (qJ.trans ε)
  have hα : ∀ x : ↥J, α (φ x) = φ (c x) := by
    intro x
    have h1 : ε.symm (φ x) = QuotientGroup.mk x := by
      rw [← hε x, MulEquiv.symm_apply_apply]
    show ε (qJ (ε.symm (φ x))) = φ (c x)
    rw [h1]
    show ε (QuotientGroup.mk (c x)) = φ (c x)
    exact hε _
  have hcube_all : ∀ y : ↥J, c (c (c y)) = y := by
    intro y
    apply Subtype.ext
    rw [hc, hc, hc]
    have : d * (d * (d * y * d⁻¹) * d⁻¹) * d⁻¹ = (d * d * d) * y * (d * d * d)⁻¹ := by group
    have hd3' : d * d * d = 1 := by simpa [pow_three, mul_assoc] using hd3
    rw [this, hd3']
    group
  have hα3 : α ^ 3 = 1 := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := hφs y
    have h3 : (α ^ 3) (φ x) = α (α (α (φ x))) := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
    rw [h3]
    calc α (α (α (φ x))) = α (α (φ (c x))) := by rw [hα x]
      _ = α (φ (c (c x))) := by rw [hα (c x)]
      _ = φ (c (c (c x))) := by rw [hα (c (c x))]
      _ = φ x := by rw [hcube_all x]
      _ = (1 : MulAut T) (φ x) := rfl
  have hα1 : α ≠ 1 := by
    intro h1
    apply hdJ
    have hz : ∀ x : ↥J, c x * x⁻¹ ∈ Subgroup.center ↥J := by
      intro x
      apply hφk
      rw [map_mul, map_inv, ← hα x, h1]
      have : (1 : MulAut T) (φ x) = φ x := rfl
      rw [this, mul_inv_cancel]
    have hcx := eq_of_central_valued hJq c hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 : d * x * d⁻¹ = x := by
      have := congrArg Subtype.val (hcx ⟨x, hx⟩)
      rw [hc] at this
      exact this
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hKJ : K ≤ J := hK.1.trans inf_le_left
  let X : Subgroup ↥J := (fixSub α).comap φ
  let C' : Subgroup ↥J := (J ⊓ Subgroup.centralizer ({d} : Set H)).subgroupOf J
  have hcfix : ∀ y : ↥J, y ∈ C' ↔ c y = y := by
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨_, h⟩
      apply Subtype.ext
      rw [hc]
      exact (mul_inv_eq_iff_eq_mul.mpr h.symm)
    · intro h
      refine ⟨y.2, ?_⟩
      have := congrArg Subtype.val h
      rw [hc] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
  have hC'X : C' ≤ X := by
    intro y hy
    have hcy := (hcfix y).mp hy
    rw [Subgroup.mem_comap, mem_fixSub, hα y, hcy]
  have hC'norm : (C'.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hC'X]
    intro y x hy hx
    have hcy : c y = y := (hcfix y).mp hy
    have hfx : α (φ x) = φ x := by
      have h := hx
      rw [Subgroup.mem_comap, mem_fixSub] at h
      exact h
    have hzc : c x * x⁻¹ ∈ Subgroup.center ↥J := by
      apply hφk
      rw [map_mul, map_inv, ← hα x, hfx, mul_inv_cancel]
    have hcen : ∀ g : ↥J, (c x * x⁻¹) * g = g * (c x * x⁻¹) :=
      fun g => (Subgroup.mem_center_iff.mp hzc g).symm
    have hcx : c x = (c x * x⁻¹) * x := by group
    apply (hcfix _).mpr
    rw [map_mul, map_mul, map_inv]
    rw [hcx, hcy]
    calc (c x * x⁻¹) * x * y * ((c x * x⁻¹) * x)⁻¹
        = (c x * x⁻¹) * (x * y * x⁻¹) * (c x * x⁻¹)⁻¹ := by group
      _ = (x * y * x⁻¹) * (c x * x⁻¹) * (c x * x⁻¹)⁻¹ := by rw [hcen (x * y * x⁻¹)]
      _ = x * y * x⁻¹ := by group
  have hK'C' : CFSG.Open.IsComponentOf (K.subgroupOf J) C' := isComponentOf_subgroupOf hKJ hK
  have hK'X : CFSG.Open.IsSubnormal (K.subgroupOf J) X :=
    CFSG.Open.IsSubnormal.trans hK'C'.2.1
      (CFSG.Open.IsSubnormal.step hC'X hC'norm (CFSG.Open.IsSubnormal.refl X))
  have hXmap : X.map φ = fixSub α := Subgroup.map_comap_eq_self_of_surjective hφs _
  let L : Subgroup T := (K.subgroupOf J).map φ
  have hLsub : CFSG.Open.IsSubnormal L (fixSub α) := by
    rw [← hXmap]
    exact CFSG.Open.IsSubnormal.map φ hK'X
  have hLle : L ≤ fixSub α := hLsub.le
  let ψK : ↥(K.subgroupOf J) →* ↥L :=
    (φ.comp (K.subgroupOf J).subtype).codRestrict L (fun x => Subgroup.mem_map_of_mem φ x.2)
  have hψs : Function.Surjective ψK := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hψk : ∀ x : ↥(K.subgroupOf J), ψK x = 1 → x ∈ Subgroup.center ↥(K.subgroupOf J) := by
    intro x hx
    have hx1 : φ (x : ↥J) = 1 := congrArg Subtype.val hx
    have hxc := hφk _ hx1
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxc (g : ↥J)
  have hLq : CFSG.Open.IsQuasisimple ↥L := isQuasisimple_of_surj hK'C'.2.2 ψK hψs hψk
  have hLcomp : CFSG.Open.IsComponentOf L (fixSub α) := ⟨hLle, hLsub, hLq⟩
  have hres := hfix α (fun x => (hα x).symm) hα3 hα1 L hLcomp
  obtain ⟨eQ2⟩ := quotCenter_mulEquiv_of_surj hK'C'.2.2 ψK hψs hψk
  let eKK' : ↥K ≃* ↥(K.subgroupOf J) := (Subgroup.subgroupOfEquivOfLe hKJ).symm
  let eQ1 : (↥K ⧸ Subgroup.center ↥K) ≃* (↥(K.subgroupOf J) ⧸ Subgroup.center ↥(K.subgroupOf J)) :=
    QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥(K.subgroupOf J)) eKK'
      (Subgroup.map_center_eq eKK')
  exact catalogIs_of_mulEquiv (eQ1.trans eQ2).symm hres

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTJ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTQuot
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

theorem catalogIs_of_mulEquiv {S S' : Type} [Group S] [Group S'] {Q : TauCeti.CFSGIndex → Prop}
    (e : S ≃* S') (h : catalogIs S Q) : catalogIs S' Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem comp_of_inner {H : Type} [Group H] {J : Subgroup H} {d : H} {Q : TauCeti.CFSGIndex → Prop}
    {T : Type} [Group T] [Nontrivial T]
    (hJq : IsQuasisimple ↥J) (hdN : d ∈ Subgroup.normalizer (J : Set H)) (hd3 : d ^ 3 = 1)
    (hdJ : d ∉ Subgroup.centralizer (J : Set H)) (e0 : PSimple 3 J ≃* T)
    (hinner : ∀ α : MulAut T, α ^ 3 = 1 → ∃ s : T, α = MulAut.conj s)
    (hcomp : ∀ s : T, s ^ 3 = 1 → s ≠ 1 → ∀ L : Subgroup T,
      IsComponentOf L (Subgroup.centralizer ({s} : Set T)) → catalogIs (↥L ⧸ Subgroup.center ↥L) Q)
    (K : Subgroup H) (hK : IsComponentOf K (J ⊓ Subgroup.centralizer ({d} : Set H))) :
    catalogIs (↥K ⧸ Subgroup.center ↥K) Q := by
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
  let cJ : ↥J ≃* ↥J := (MulEquiv.subgroupMap cH J).trans (MulEquiv.subgroupCongr hJmap)
  have hc : ∀ x : ↥J, (cJ x : H) = d * x * d⁻¹ := fun x => rfl
  let π : ↥J →* PSimple 3 J :=
    (QuotientGroup.mk' (Subgroup.center (PQuot 3 J))).comp
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))
  have hπs : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hNtop : GLAPPrimeCore 3 ↥J ≠ ⊤ := by
    intro hN
    have hπ1 : ∀ x : ↥J, π x = 1 := by
      intro x
      have hx : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) x : ↥J ⧸ GLAPPrimeCore 3 ↥J) = 1 :=
        (QuotientGroup.eq_one_iff x).mpr (by rw [hN]; exact Subgroup.mem_top x)
      show (QuotientGroup.mk' (Subgroup.center (PQuot 3 J)))
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) x) = 1
      rw [hx, map_one]
    obtain ⟨a, b, hab⟩ := exists_pair_ne T
    have h1 : e0.symm a = 1 := by
      obtain ⟨x, hx⟩ := hπs (e0.symm a)
      rw [← hx, hπ1]
    have h2 : e0.symm b = 1 := by
      obtain ⟨x, hx⟩ := hπs (e0.symm b)
      rw [← hx, hπ1]
    exact hab (e0.symm.injective (h1.trans h2.symm))
  have hπcenter : ∀ z ∈ Subgroup.center ↥J, π z = 1 := by
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
  have hker : ∀ x : ↥J, π x = 1 ↔ x ∈ Subgroup.center ↥J := fun x =>
    ⟨fun h => mem_center_of_quotQuot_eq_one hJq (GLAPPrimeCore 3 ↥J) hNtop x h, hπcenter x⟩
  let φ : ↥J →* T := (e0.toMonoidHom).comp π
  have hφs : Function.Surjective φ := e0.surjective.comp hπs
  have hφ1 : ∀ x : ↥J, φ x = 1 ↔ π x = 1 := fun x => by
    show e0 (π x) = 1 ↔ π x = 1
    exact e0.map_eq_one_iff
  have hφk : ∀ x : ↥J, φ x = 1 → x ∈ Subgroup.center ↥J := fun x h =>
    (hker x).mp ((hφ1 x).mp h)
  have hkerZ : φ.ker = Subgroup.center ↥J := by
    ext x
    rw [MonoidHom.mem_ker, hφ1, hker]
  let ε : (↥J ⧸ Subgroup.center ↥J) ≃* T :=
    (QuotientGroup.quotientMulEquivOfEq hkerZ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hε : ∀ x : ↥J, ε (QuotientGroup.mk x) = φ x := fun x => rfl
  let qJ : (↥J ⧸ Subgroup.center ↥J) ≃* (↥J ⧸ Subgroup.center ↥J) :=
    QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J) cJ (Subgroup.map_center_eq cJ)
  let α : T ≃* T := ε.symm.trans (qJ.trans ε)
  have hα : ∀ x : ↥J, α (φ x) = φ (cJ x) := by
    intro x
    have h1 : ε.symm (φ x) = QuotientGroup.mk x := by
      rw [← hε x, MulEquiv.symm_apply_apply]
    show ε (qJ (ε.symm (φ x))) = φ (cJ x)
    rw [h1]
    show ε (QuotientGroup.mk (cJ x)) = φ (cJ x)
    exact hε _
  have hd3' : d * d * d = 1 := by simpa [pow_three, mul_assoc] using hd3
  have hcube_all : ∀ y : ↥J, cJ (cJ (cJ y)) = y := by
    intro y
    apply Subtype.ext
    rw [hc, hc, hc]
    have : d * (d * (d * y * d⁻¹) * d⁻¹) * d⁻¹ = (d * d * d) * y * (d * d * d)⁻¹ := by group
    rw [this, hd3']
    group
  have hα3 : α ^ 3 = 1 := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := hφs y
    have h3 : (α ^ 3) (φ x) = α (α (α (φ x))) := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
    rw [h3]
    calc α (α (α (φ x))) = α (α (φ (cJ x))) := by rw [hα x]
      _ = α (φ (cJ (cJ x))) := by rw [hα (cJ x)]
      _ = φ (cJ (cJ (cJ x))) := by rw [hα (cJ (cJ x))]
      _ = φ x := by rw [hcube_all x]
      _ = (1 : MulAut T) (φ x) := rfl
  obtain ⟨s0, hs0⟩ := hinner α hα3
  have hs : ∀ x : ↥J, φ (cJ x) = s0 * φ x * s0⁻¹ := fun x => by
    rw [← hα x, hs0]
    rfl
  obtain ⟨j, hj⟩ := lift_of_inner hJq φ hφs hφk cJ hc hs
  have hjH : ∀ x ∈ J, d * x * d⁻¹ = (j : H) * x * (j : H)⁻¹ := by
    intro x hx
    have h := congrArg Subtype.val (hj ⟨x, hx⟩)
    rw [hc] at h
    exact h
  have hJC : J ⊓ Subgroup.centralizer ({d} : Set H) =
      J ⊓ Subgroup.centralizer ({(j : H)} : Set H) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, (mem_centralizer_iff_of_conj hjH hx).mp h⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, (mem_centralizer_iff_of_conj hjH hx).mpr h⟩
  rw [hJC] at hK
  have hKJ : K ≤ J := hK.1.trans inf_le_left
  have hK1 : CFSG.Open.IsComponentOf (K.subgroupOf J) (Subgroup.centralizer ({j} : Set ↥J)) := by
    have h := isComponentOf_subgroupOf hKJ hK
    have hX : (J ⊓ Subgroup.centralizer ({(j : H)} : Set H)).subgroupOf J =
        Subgroup.centralizer ({j} : Set ↥J) := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨_, h2⟩
        exact Subtype.ext h2
      · intro h2
        exact ⟨y.2, congrArg Subtype.val h2⟩
    rw [hX] at h
    exact h
  have himg := isComponentOf_image_centralizer φ hφs hφk hK1
  have hs1 : φ j ≠ 1 := by
    intro h
    have hjc := hφk j h
    apply hdJ
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxc : (⟨x, hx⟩ : ↥J) * j = j * ⟨x, hx⟩ := Subgroup.mem_center_iff.mp hjc _
    have hjx : (j : H) * x = x * j := (congrArg Subtype.val hxc).symm
    have h2 : (j : H) * x * (j : H)⁻¹ = x := by rw [hjx]; group
    have h1 : d * x * d⁻¹ = x := (hjH x hx).trans h2
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hs3 : φ j ^ 3 = 1 := by
    have hj3c : j * j * j ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hcg' : j * j * j * g * (j * j * j)⁻¹ = g := by
        have e : cJ (cJ (cJ g)) = j * j * j * g * (j * j * j)⁻¹ := by
          rw [hj, hj, hj]
          group
        rw [← e]
        exact hcube_all g
      exact (mul_inv_eq_iff_eq_mul.mp hcg').symm
    rw [pow_three, ← map_mul, ← map_mul]
    exact (hφ1 _).mpr (hπcenter _ (by simpa [mul_assoc] using hj3c))
  have hcomp2 := hcomp _ hs3 hs1 _ himg
  let ψK : ↥(K.subgroupOf J) →* ↥((K.subgroupOf J).map φ) :=
    (φ.comp (K.subgroupOf J).subtype).codRestrict ((K.subgroupOf J).map φ)
      (fun x => Subgroup.mem_map_of_mem φ x.2)
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
  obtain ⟨eQ⟩ := quotCenter_mulEquiv_of_surj hK1.2.2 ψK hψs hψk
  have hcat1 : catalogIs (↥(K.subgroupOf J) ⧸ Subgroup.center ↥(K.subgroupOf J))
      Q :=
    catalogIs_of_mulEquiv eQ.symm hcomp2
  have hKeq : ↥(K.subgroupOf J) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKJ
  let hQK : (↥(K.subgroupOf J) ⧸ Subgroup.center ↥(K.subgroupOf J)) ≃*
      (↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.congr (Subgroup.center ↥(K.subgroupOf J)) (Subgroup.center ↥K) hKeq
      (Subgroup.map_center_eq hKeq)
  exact catalogIs_of_mulEquiv hQK hcat1

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTSp8
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015Four
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs273d2
public import CFSG.LieType.SeitzGeneration.OuterSpData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

@[expose] def SchurSp8 : Prop :=
  ∀ (J : Type) [Group J], CFSG.Open.IsQuasisimple J →
    catalogIs (J ⧸ Subgroup.center J) S9.isSp8two → Subgroup.center J = ⊥

theorem sp8_model {S : Type} [Group S] (h : catalogIs S S9.isSp8two) :
    Nonempty (S ≃* StatedSp 4 (ZMod 2)) := by
  obtain ⟨K₀, _, _, hK, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.I1015.stated_sp8_of_catalog h
  obtain ⟨φ⟩ := exists_ringEquiv_zmod_two hK
  exact ⟨e.trans (statedProjEquivZMod2 φ
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 4))⟩

theorem nontrivial_statedSp_four : Nontrivial ↥(StatedSp 4 (ZMod 2)) := by
  have hs : IsSimpleGroup (StatedProj (StatedSp 4 (ZMod 2))) :=
    CFSG.LieType.SeitzGeneration.isSimpleGroup_statedProj_statedSp_of_two_le (by norm_num) (by
      rintro ⟨h4, -⟩
      exact absurd h4 (by norm_num))
  exact (QuotientGroup.mk'_surjective ((StatedScalars (Fin 4 ⊕ Fin 4) (ZMod 2)).subgroupOf
    (StatedSp 4 (ZMod 2)))).nontrivial

theorem sp8_iso_of_schur (hS : SchurSp8) {H : Type} [Group H] (J : Subgroup H)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hcat : catalogIs (PSimple 3 J) S9.isSp8two) :
    Nonempty (↥J ≃* StatedSp 4 (ZMod 2)) ∧ Subgroup.center ↥J = ⊥ := by
  obtain ⟨e8⟩ := sp8_model hcat
  haveI := nontrivial_statedSp_four
  haveI : Nontrivial (PSimple 3 J) := e8.symm.injective.nontrivial
  let π : ↥J →* PSimple 3 J :=
    (QuotientGroup.mk' (Subgroup.center (PQuot 3 J))).comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))
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
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PSimple 3 J)
    obtain ⟨x, hx⟩ := hπs a
    obtain ⟨y, hy⟩ := hπs b
    exact hab (by rw [← hx, ← hy, hπ1 x, hπ1 y])
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
  have hkerEq : π.ker = Subgroup.center ↥J := by
    ext x
    rw [MonoidHom.mem_ker, hker]
  let eQ : (↥J ⧸ Subgroup.center ↥J) ≃* PSimple 3 J :=
    (QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπs)
  have hcatJ : catalogIs (↥J ⧸ Subgroup.center ↥J) S9.isSp8two :=
    catalogIs_of_mulEquiv eQ.symm hcat
  have hZ : Subgroup.center ↥J = ⊥ := hS ↥J hJq hcatJ
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.center ↥J := (hker x).mp hx
    rw [hZ, Subgroup.mem_bot] at hxc
    exact hxc
  let eJ0 : ↥J ≃* PSimple 3 J := MulEquiv.ofBijective π ⟨hπinj, hπs⟩
  exact ⟨⟨eJ0.trans e8⟩, hZ⟩

theorem sp8_holds_of (hS : SchurSp8) (GU : GUBlockFacts) : KSubT.CompFactSp8 := by
  intro H _ _ J B d hJq hcat hdB hI hd3 hdJ K hK
  obtain ⟨⟨eJ0⟩, hZ⟩ := sp8_iso_of_schur hS J hJq hcat
  have hdN : d ∈ Subgroup.normalizer (J : Set H) := hI.1 hdB
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
  let αT : MulAut ↥(StatedSp 4 (ZMod 2)) := eJ0.symm.trans (cJ.trans eJ0)
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273d.all_inner_spTwo
    (n := 4) (by norm_num) αT
  let j : ↥J := eJ0.symm g
  have hjg : eJ0 j = g := MulEquiv.apply_symm_apply eJ0 g
  have hjconj : ∀ x : ↥J, cJ x = j * x * j⁻¹ := by
    intro x
    apply eJ0.injective
    have h1 : eJ0 (cJ x) = MulAut.conj g (eJ0 x) := by
      rw [← hg]
      simp [αT, MulEquiv.symm_apply_apply]
    rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, hjg]
  have hjH : ∀ x ∈ J, d * x * d⁻¹ = (j : H) * x * (j : H)⁻¹ := by
    intro x hx
    have h := congrArg Subtype.val (hjconj ⟨x, hx⟩)
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
  have hL : CFSG.Open.IsComponentOf ((K.subgroupOf J).map (eJ0 : ↥J →* ↥(StatedSp 4 (ZMod 2))))
      (Subgroup.centralizer ({eJ0 j} : Set ↥(StatedSp 4 (ZMod 2)))) := by
    have h := isComponentOf_map_mulEquiv hK1 eJ0
    rwa [map_centralizer_singleton] at h
  have hcube : ∀ y : ↥J, cJ (cJ (cJ y)) = y := by
    intro y
    apply Subtype.ext
    rw [hc, hc, hc]
    have : d * (d * (d * y * d⁻¹) * d⁻¹) * d⁻¹ = (d * d * d) * y * (d * d * d)⁻¹ := by group
    have hd3' : d * d * d = 1 := by simpa [pow_three, mul_assoc] using hd3
    rw [this, hd3']
    group
  have hj1 : j ≠ 1 := by
    intro h
    apply hdJ
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : cJ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [hjconj, h]
      group
    have h2 : d * x * d⁻¹ = x := by
      have := congrArg Subtype.val h1
      rw [hc] at this
      exact this
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hj3 : j * (j * j) = 1 := by
    have hcen : j * (j * j) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro y
      have e : cJ (cJ (cJ y)) = j * (j * j) * y * (j * (j * j))⁻¹ := by
        rw [hjconj, hjconj, hjconj]
        group
      have hcy := hcube y
      rw [e] at hcy
      exact (mul_inv_eq_iff_eq_mul.mp hcy).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hcen
  have hs1 : eJ0 j ≠ 1 := by
    intro h
    apply hj1
    exact eJ0.injective (by rw [h, map_one])
  have hs3 : eJ0 j ^ 3 = 1 := by
    rw [pow_three, ← map_mul, ← map_mul, hj3, map_one]
  have hsp := sp8_comp GU hs3 hs1 hL
  let eKL : ↥K ≃* ↥((K.subgroupOf J).map (eJ0 : ↥J →* ↥(StatedSp 4 (ZMod 2)))) :=
    (Subgroup.subgroupOfEquivOfLe hKJ).symm.trans
      (Subgroup.equivMapOfInjective (K.subgroupOf J) (eJ0 : ↥J →* ↥(StatedSp 4 (ZMod 2)))
        eJ0.injective)
  let eQ : (↥K ⧸ Subgroup.center ↥K) ≃*
      (↥((K.subgroupOf J).map (eJ0 : ↥J →* ↥(StatedSp 4 (ZMod 2)))) ⧸
        Subgroup.center ↥((K.subgroupOf J).map (eJ0 : ↥J →* ↥(StatedSp 4 (ZMod 2))))) :=
    QuotientGroup.congr (Subgroup.center ↥K)
      (Subgroup.center ↥((K.subgroupOf J).map (eJ0 : ↥J →* ↥(StatedSp 4 (ZMod 2)))))
      eKL (Subgroup.map_center_eq eKL)
  refine ⟨catalogIs_of_mulEquiv eQ.symm hsp.1, fun hA6 => ?_⟩
  obtain ⟨eLA6⟩ := hsp.2 (catalogIs_of_mulEquiv eQ hA6)
  exact catalogIs_alt6_of_equiv (eKL.trans eLA6)

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end

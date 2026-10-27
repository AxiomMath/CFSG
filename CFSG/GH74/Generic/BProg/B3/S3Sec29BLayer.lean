module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs
public import CFSG.GH74.Generic.BProg.B3.S3L3Facts

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3.S3Fusion CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup
open scoped MatrixGroups commutatorElement Pointwise

namespace S3Sec29BLayer

variable {G : Type} [Group G] [Finite G]

theorem piC_eq_one_of_mem {x : G} {K : Subgroup G}
    (hK : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) K) {z : G} (hz : z ∈ pPrimeCoreOf 2 K) :
    piC x z = 1 := by
  have hzK : z ∈ K := TwoThin.pPrimeCoreOf_le K hz
  have hzC : z ∈ centralizer ({x} : Set G) := hK.1 hzK
  obtain ⟨o, ho, hoz⟩ := CFSG.GH74.GLS.Th2.Bal.pPrimeCoreOf_le_of_pCompIn hK hz
  rw [piC_of_mem x hzC]
  have : (⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) = o := Subtype.ext hoz.symm
  rw [this]
  exact (QuotientGroup.eq_one_iff o).2 ho

theorem mem_pPrimeCoreOf_of_piC_eq_one {x : G} {K : Subgroup G}
    (hK : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) K) {z : G} (hzK : z ∈ K)
    (hz : piC x z = 1) : z ∈ pPrimeCoreOf 2 K := by
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  set θ : ↥K →* CentralizerBar x := (proj x).comp (Subgroup.inclusion hKC) with hθ
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer ({x} : Set G)))) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hker : Odd (Nat.card θ.ker) := by
    have h : ¬ 2 ∣ Nat.card θ.ker := B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hKC)
      (Subgroup.inclusion_injective hKC) (pPrimeCore 2 ↥(centralizer ({x} : Set G))) hodd
    exact Nat.odd_iff.2 (by omega)
  have hle : θ.ker ≤ pPrimeCore 2 ↥K :=
    le_sSup ⟨inferInstance, Nat.coprime_two_left.2 hker⟩
  have hmem : (⟨z, hzK⟩ : ↥K) ∈ θ.ker := by
    rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply]
    have := piC_of_mem x (hKC hzK)
    rw [hz] at this
    exact this.symm
  exact ⟨⟨z, hzK⟩, hle hmem, rfl⟩

omit [Finite G] in
theorem card_subgroupOf_of_le {A Y : Subgroup G} (h : A ≤ Y) :
    Nat.card (A.subgroupOf Y) = Nat.card A := by
  have h1 := Subgroup.card_map_of_injective (K := A.subgroupOf Y) (f := Y.subtype)
    Y.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h] at h1
  exact h1.symm

theorem phiY_range_mul {x : G} {K : Subgroup G}
    (hK : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) K)
    {e u b : G} (heK : e ∈ K) (hbeu : b = e * u) (hb : orderOf b = 2) (hu : u ∈ cSec K) :
    (S3L3Lift.phiY x b hK.1).range =
      centralizer ({S3L3Lift.yK x hK.1 heK} : Set ↥(S3.imgBar x K)) := by
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have huK : u ∈ normalizer (K : Set G) := hu.1
  have hbN : b ∈ normalizer (K : Set G) := by
    rw [hbeu]
    exact mul_mem (Subgroup.le_normalizer heK) huK
  have heC : e ∈ centralizer ({x} : Set G) := hKC heK
  have hcu : ∀ k ∈ K, ⁅u, k⁆ ∈ pPrimeCoreOf 2 K := fun k hk => by
    have h1 : ⁅k, u⁆ ∈ pPrimeCoreOf 2 K := hu.2.2 k hk
    have h2 : ⁅u, k⁆ = ⁅k, u⁆⁻¹ := (commutatorElement_inv k u).symm
    rw [h2]
    exact inv_mem h1
  ext c
  constructor
  · rintro ⟨w, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, S3L3Lift.phiY_coe, S3L3Lift.yK_coe]
    obtain ⟨hwK, hwb⟩ := Subgroup.mem_inf.1 w.2
    have hw : (w : G) * b = b * (w : G) := Subgroup.mem_centralizer_singleton_iff.1 hwb
    have hwC : (w : G) ∈ centralizer ({x} : Set G) := hKC hwK
    have key : (w : G) * e = e * (⁅u, (w : G)⁆ * w) := by
      have h1 : (w : G) * (e * u) = (e * u) * w := by rw [← hbeu]; exact hw
      calc (w : G) * e = ((w : G) * (e * u)) * u⁻¹ := by group
        _ = ((e * u) * w) * u⁻¹ := by rw [h1]
        _ = e * (⁅u, (w : G)⁆ * w) := by simp only [commutatorElement_def]; group
    have hcw : piC x ⁅u, (w : G)⁆ = 1 := piC_eq_one_of_mem hK (hcu w hwK)
    have hcwC : ⁅u, (w : G)⁆ ∈ centralizer ({x} : Set G) :=
      hKC (TwoThin.pPrimeCoreOf_le K (hcu w hwK))
    rw [← piC_mul x hwC heC, key, piC_mul x heC (mul_mem hcwC hwC), piC_mul x hcwC hwC, hcw,
      one_mul]
  · intro hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    obtain ⟨g, hgK, hg⟩ := S3.mem_imgBar.1 c.2
    have hgC : (g : G) ∈ centralizer ({x} : Set G) := g.2
    have hπg : piC x (g : G) = (c : CentralizerBar x) := by
      rw [piC_of_mem x hgC]
      exact hg
    have hcomm1 : piC x (g : G) * piC x e = piC x e * piC x (g : G) := by
      have := congrArg Subtype.val hc
      rw [Subgroup.coe_mul, Subgroup.coe_mul, S3L3Lift.yK_coe] at this
      rw [hπg]
      exact this
    have hegO : ⁅e, (g : G)⁆ ∈ pPrimeCoreOf 2 K := by
      have h1 : piC x ⁅e, (g : G)⁆ = 1 := by
        rw [S3L3Facts.piC_commutator x heC hgC]
        exact commutatorElement_eq_one_iff_mul_comm.2 hcomm1.symm
      refine mem_pPrimeCoreOf_of_piC_eq_one hK ?_ h1
      simp only [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem heK hgK) (K.inv_mem heK)) (K.inv_mem hgK)
    have hbgO : ⁅b, (g : G)⁆ ∈ pPrimeCoreOf 2 K := by
      have hid : ⁅b, (g : G)⁆ = (e * ⁅u, (g : G)⁆ * e⁻¹) * ⁅e, (g : G)⁆ := by
        rw [hbeu]
        simp only [commutatorElement_def]
        group
      rw [hid]
      exact mul_mem (TwoThin.pPrimeCoreOf_normalized K heK (hcu g hgK)) hegO
    set H : Subgroup G := K ⊔ zpowers b with hH
    have hKH : K ≤ H := le_sup_left
    have hbH : b ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    have hOK : pPrimeCoreOf 2 K ≤ K := TwoThin.pPrimeCoreOf_le K
    have hHN : H ≤ normalizer (pPrimeCoreOf 2 K : Set G) :=
      sup_le (fun k hk => TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hk))
        (Subgroup.zpowers_le.2 (TwoThin.mem_normalizer_pPrimeCoreOf hbN))
    set N : Subgroup ↥H := (pPrimeCoreOf 2 K).subgroupOf H with hN
    have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer (hOK.trans hKH)).2 hHN
    have hNodd : Odd (Nat.card N) := by
      rw [hN, card_subgroupOf_of_le (hOK.trans hKH)]
      exact TwoThin.card_pPrimeCoreOf_odd K
    set kH : ↥H := ⟨(g : G), hKH hgK⟩ with hkH
    set bH : ↥H := ⟨b, hbH⟩ with hbHdef
    have hbH2 : orderOf bH = 2 := by rw [hbHdef, Subgroup.orderOf_mk]; exact hb
    have hcommbk : QuotientGroup.mk' N bH * QuotientGroup.mk' N kH =
        QuotientGroup.mk' N kH * QuotientGroup.mk' N bH := by
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 hbgO
    have hc' : ∀ a ∈ zpowers bH, QuotientGroup.mk' N a * (QuotientGroup.mk' N kH) =
        (QuotientGroup.mk' N kH) * QuotientGroup.mk' N a := by
      intro a ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [map_zpow]
      exact (Commute.zpow_left (show Commute (QuotientGroup.mk' N bH) (QuotientGroup.mk' N kH)
        from hcommbk) n).eq
    obtain ⟨g', hg'1, hg'2⟩ := B1.centralizer_quotient_of_pGroup N hNodd
      (B1.isPGroup_two_zpowers_of_orderOf hbH2) (c := QuotientGroup.mk' N kH) hc'
    have hg'b : (g' : G) * b = b * (g' : G) :=
      (congrArg Subtype.val (hg'2 bH (Subgroup.mem_zpowers bH))).symm
    have hzO : (g' : G)⁻¹ * (g : G) ∈ pPrimeCoreOf 2 K := by
      have h1 : g'⁻¹ * kH ∈ N := QuotientGroup.eq.1 hg'1
      exact Subgroup.mem_subgroupOf.1 h1
    have hg'eq : (g' : G) = (g : G) * ((g' : G)⁻¹ * (g : G))⁻¹ := by group
    have hg'K : (g' : G) ∈ K := by
      rw [hg'eq]
      exact K.mul_mem hgK (K.inv_mem (hOK hzO))
    refine ⟨⟨(g' : G), Subgroup.mem_inf.2 ⟨hg'K, Subgroup.mem_centralizer_singleton_iff.2 hg'b⟩⟩,
      ?_⟩
    apply Subtype.ext
    rw [S3L3Lift.phiY_coe, ← hπg, hg'eq,
      piC_mul x hgC (inv_mem (hKC (hOK hzO))), piC_inv x (hKC (hOK hzO)),
      piC_eq_one_of_mem hK hzO]
    simp

section Lift

variable {x e b : G} {K : Subgroup G} {hKC : K ≤ centralizer ({x} : Set G)} {heK : e ∈ K}
  {S : Subgroup ↥(S3.imgBar x K)} {F : Type} [Field F] [Finite F]

theorem exists_comp (hS : S3L3Lift.LayerHyp x hKC heK S F)
    (hrange : (S3L3Lift.phiY x b hKC).range =
      centralizer ({S3L3Lift.yK x hKC heK} : Set ↥(S3.imgBar x K))) :
    ∃ L : Subgroup G, IsPCompIn 2 (K ⊓ centralizer ({b} : Set G)) L ∧
      ((L.subgroupOf (K ⊓ centralizer ({b} : Set G))).map (S3L3Lift.phiY x b hKC)) = S := by
  have hker : ¬ 2 ∣ Nat.card (S3L3Lift.phiY x b hKC).ker :=
    Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 (S3L3Lift.phiY_ker_odd x b hKC))
  obtain ⟨h1, h2⟩ := B1.exists_isPCompIn_lift_of_odd_ker (S3L3Lift.phiY x b hKC) hker (Jb := S)
    (by rw [hrange]; exact hS.comp)
  exact ⟨_, h1, h2⟩

theorem image_eq (hS : S3L3Lift.LayerHyp x hKC heK S F)
    (hrange : (S3L3Lift.phiY x b hKC).range =
      centralizer ({S3L3Lift.yK x hKC heK} : Set ↥(S3.imgBar x K))) {L : Subgroup G}
    (hL : IsPCompIn 2 (K ⊓ centralizer ({b} : Set G)) L) :
    (L.subgroupOf (K ⊓ centralizer ({b} : Set G))).map (S3L3Lift.phiY x b hKC) = S := by
  set W : Subgroup G := K ⊓ centralizer ({b} : Set G) with hW
  set φ : ↥W →* ↥(S3.imgBar x K) := S3L3Lift.phiY x b hKC with hφ
  have hfs : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hfk : Odd (Nat.card φ.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact S3L3Lift.phiY_ker_odd x b hKC
  have hL2 := (TwoThin.isPCompIn_two_iff.mp hL).2
  have himg :=
    CFSG.ComponentClassification.OddKernelTwoComponents.image φ.rangeRestrict hfs hfk _ hL2
  set M : Subgroup ↥(S3.imgBar x K) := (L.subgroupOf W).map φ with hM
  have hMeq : M = ((L.subgroupOf W).map φ.rangeRestrict).map φ.range.subtype := by
    rw [Subgroup.map_map]
    rfl
  have hMsub : M.subgroupOf φ.range = (L.subgroupOf W).map φ.rangeRestrict := by
    rw [hMeq]
    exact Subgroup.comap_map_eq_self_of_injective φ.range.subtype_injective _
  have hMle : M ≤ φ.range := by
    rintro _ ⟨l, _, rfl⟩
    exact ⟨l, rfl⟩
  have hMc : IsPCompIn 2 (centralizer ({S3L3Lift.yK x hKC heK} : Set ↥(S3.imgBar x K))) M := by
    rw [← hrange]
    exact TwoThin.isPCompIn_two_iff.mpr ⟨hMle, by rw [hMsub]; exact himg⟩
  exact hS.uniq M hMc

theorem unique_comp (hS : S3L3Lift.LayerHyp x hKC heK S F)
    (hrange : (S3L3Lift.phiY x b hKC).range =
      centralizer ({S3L3Lift.yK x hKC heK} : Set ↥(S3.imgBar x K))) {L₁ L₂ : Subgroup G}
    (h₁ : IsPCompIn 2 (K ⊓ centralizer ({b} : Set G)) L₁)
    (h₂ : IsPCompIn 2 (K ⊓ centralizer ({b} : Set G)) L₂) : L₁ = L₂ := by
  set W : Subgroup G := K ⊓ centralizer ({b} : Set G) with hW
  set φ : ↥W →* ↥(S3.imgBar x K) := S3L3Lift.phiY x b hKC with hφ
  have hfs : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hfk : Odd (Nat.card φ.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact S3L3Lift.phiY_ker_odd x b hKC
  have e1 := image_eq hS hrange h₁
  have e2 := image_eq hS hrange h₂
  have hmap : ∀ L : Subgroup G, ((L.subgroupOf W).map φ.rangeRestrict).map φ.range.subtype =
      (L.subgroupOf W).map φ := fun L => by
    rw [Subgroup.map_map]
    rfl
  have hmaps : (L₁.subgroupOf W).map φ.rangeRestrict = (L₂.subgroupOf W).map φ.rangeRestrict := by
    apply Subgroup.map_injective φ.range.subtype_injective
    rw [hmap, hmap, e1, e2]
  have := CFSG.ComponentClassification.OddKernelTwoComponents.lift_unique φ.rangeRestrict hfs hfk
    (L₁.subgroupOf W) (L₂.subgroupOf W) (TwoThin.isPCompIn_two_iff.mp h₁).2
    (TwoThin.isPCompIn_two_iff.mp h₂).2 hmaps
  have h3 := Subgroup.subgroupOf_inj.1 this
  rwa [inf_of_le_left h₁.1, inf_of_le_left h₂.1] at h3

theorem pLayerOf_eq (hS : S3L3Lift.LayerHyp x hKC heK S F)
    (hrange : (S3L3Lift.phiY x b hKC).range =
      centralizer ({S3L3Lift.yK x hKC heK} : Set ↥(S3.imgBar x K))) {L : Subgroup G}
    (hL : IsPCompIn 2 (K ⊓ centralizer ({b} : Set G)) L) :
    pLayerOf 2 (K ⊓ centralizer ({b} : Set G)) = L :=
  le_antisymm (sSup_le fun _ hL' => (unique_comp hS hrange hL' hL).le) (le_sSup hL)

theorem mem_layer (hS : S3L3Lift.LayerHyp x hKC heK S F)
    (hrange : (S3L3Lift.phiY x b hKC).range =
      centralizer ({S3L3Lift.yK x hKC heK} : Set ↥(S3.imgBar x K)))
    (he : orderOf e = 2) (heb : e * b = b * e) :
    e ∈ pLayerOf 2 (K ⊓ centralizer ({b} : Set G)) := by
  set W : Subgroup G := K ⊓ centralizer ({b} : Set G) with hW
  set φ : ↥W →* ↥(S3.imgBar x K) := S3L3Lift.phiY x b hKC with hφ
  have hfs : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hfk : Odd (Nat.card φ.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact S3L3Lift.phiY_ker_odd x b hKC
  have he2 : e * e = 1 := by
    have := pow_orderOf_eq_one e
    rwa [he, pow_two] at this
  have heW : e ∈ W := Subgroup.mem_inf.2 ⟨heK, Subgroup.mem_centralizer_singleton_iff.2 heb⟩
  set eW : ↥W := ⟨e, heW⟩ with heWdef
  have heW2 : eW * eW = 1 := Subtype.ext he2
  have hSle : S ≤ pLayerOf 2 (centralizer ({S3L3Lift.yK x hKC heK} : Set ↥(S3.imgBar x K))) :=
    le_sSup hS.comp
  have hmem : S3L3Lift.yK x hKC heK ∈ pLayerOf 2 φ.range := by
    rw [hφ, hrange]
    exact hSle hS.mem
  rw [TwoThin.pLayerOf_two_eq_map] at hmem
  obtain ⟨t, ht, htv⟩ := hmem
  have hφy : φ eW = S3L3Lift.yK x hKC heK := by
    apply Subtype.ext
    rw [hφ, S3L3Lift.phiY_coe]
    rfl
  have hft : φ.rangeRestrict eW = t := Subtype.ext (hφy.trans htv.symm)
  have h1 : φ.rangeRestrict eW ∈ CFSG.ComponentClassification.TwoLayer.subgroup ↥φ.range :=
    hft ▸ ht
  have h2 := Lemma212Aux.mem_twoLayer_of_map_mem φ.rangeRestrict hfs hfk heW2 h1
  rw [TwoThin.pLayerOf_two_eq_map]
  exact ⟨eW, h2, rfl⟩

theorem psi_data (hS : S3L3Lift.LayerHyp x hKC heK S F)
    (hrange : (S3L3Lift.phiY x b hKC).range =
      centralizer ({S3L3Lift.yK x hKC heK} : Set ↥(S3.imgBar x K))) {L : Subgroup G}
    (hL : IsPCompIn 2 (K ⊓ centralizer ({b} : Set G)) L) :
    ∃ ψ : ↥L →* ↥S, Function.Surjective ψ ∧ ψ.ker = pPrimeCore 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := K ⊓ centralizer ({b} : Set G) with hW
  set φ : ↥W →* ↥(S3.imgBar x K) := S3L3Lift.phiY x b hKC with hφ
  have himg := image_eq hS hrange hL
  have hLW : L ≤ W := hL.1
  have hmem : ∀ z : ↥L, φ (Subgroup.inclusion hLW z) ∈ S := fun z => by
    rw [← himg]
    exact ⟨Subgroup.inclusion hLW z, z.2, rfl⟩
  set ψ : ↥L →* ↥S := (φ.comp (Subgroup.inclusion hLW)).codRestrict S hmem with hψ
  have hψc : ∀ z : ↥L, (ψ z : ↥(S3.imgBar x K)) = φ (Subgroup.inclusion hLW z) := fun z => rfl
  have hsurj : Function.Surjective ψ := by
    rintro ⟨s, hs⟩
    rw [← himg] at hs
    obtain ⟨w, hw, hws⟩ := hs
    refine ⟨⟨(w : G), hw⟩, Subtype.ext ?_⟩
    rw [hψc]
    exact hws
  have hker : ¬ 2 ∣ Nat.card ψ.ker := by
    have h1 : ψ.ker = φ.ker.comap (Subgroup.inclusion hLW) := by
      rw [hψ, MonoidHom.ker_codRestrict, MonoidHom.comap_ker]
    rw [h1]
    intro h2
    have h3 := Subgroup.card_comap_dvd_of_injective φ.ker (Subgroup.inclusion hLW)
      (Subgroup.inclusion_injective hLW)
    have h4 := S3L3Lift.phiY_ker_odd x b hKC
    exact (Nat.not_even_iff_odd.2 h4) (even_iff_two_dvd.2 (h2.trans h3))
  obtain ⟨ee⟩ := hS.equiv
  have hbot : pPrimeCore 2 ↥S = ⊥ := S3L3Lift.pPrimeCore_eq_bot_of_sl2 hS.odd hS.big ee
  have hcore := (prime_complement_kernel_core_preimage ψ hsurj hker).1
  rw [hbot, MonoidHom.comap_bot] at hcore
  exact ⟨ψ, hsurj, hcore⟩

end Lift

end S3Sec29BLayer

end CFSG.GH74.Generic.BProg.B3

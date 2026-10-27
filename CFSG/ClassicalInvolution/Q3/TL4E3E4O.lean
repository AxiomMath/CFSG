module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Main
public import CFSG.ClassicalInvolution.Q3.TL4E3S3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint

section Cit3


@[expose] def TightE3E4Sec (n : ℕ) : Prop :=
  TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR 3 n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) →
      ∀ J : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J →
      ∀ u : Y, IsUniqueInvolution J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
        (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u),
        TightE4 (SecQ R u) → ¬ TightInO2 (E3.secT htu ht) →
          Twin1711.QuasiE4 (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R))

variable {n : ℕ}

theorem tightE3E4O_of (hT1 : Fin1711Sandwich) (hT2 : Fin1711Pairing) (hSec : TightE3E4Sec n)
    (hP : TightBelowRPlus 3 n) : TightE3E4O n := by
  intro Y _ _ R S t hL hO hcn hsp J hJ u hu htu ht hE4
  by_contra hE2
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set π := orbOf (TC.nbrAdj Ω) J (tightCore R) with hπdef
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have h2 : ∀ J' ∈ Ω, IsPGroup 2 J' := hd.isPGroup_member hO
  have htr : ∀ J' ∈ Ω, ∃ g : Y, conjSub g (tightCore R) = J' := fun J' hJ' => hJ'
  have hgen : (⨆ J' ∈ Ω, J') = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hL.cls.2.1
  have hF := TC.graphFam hΩ h2 hsp htr hgen hcn
  have hstd : OrbitStd Ω := ⟨hΩ, h2, hF⟩
  have hJΩ : J ∈ Ω := hJ.1.2.1
  have hmax : π ∈ maxOrbs (TC.nbrAdj Ω) J := orbOf_mem_maxOrbs hF hJ.1 hJ.2
  obtain ⟨g₀, hg₀⟩ := hJΩ
  have hK₀π : tightCore R ∈ π := ⟨1, Subgroup.one_mem _, by ext x; simp [conjSub]⟩
  have hconj : conjSub g₀⁻¹ J ∈ π := by
    rw [← hg₀, conjSub_inv_conjSub]
    exact hK₀π
  have hR2 : IsPGroup 2 R := hd.isPGroup_of_oddCent hO
  have hq8 : Nonempty (↥J ≃* QuaternionGroup 2) := by
    obtain ⟨eS⟩ := hL.cls.1
    have hS : (S : Subgroup R) = ⊤ := (S.is_maximal' (hR2.to_subgroup ⊤) le_top).symm
    let e₁ : ↥(conjSub g₀ (tightCore R)) ≃* ↥(tightCore R) :=
      ((tightCore R).equivMapOfInjective (MulAut.conj g₀).toMonoidHom
        (MulAut.conj g₀).injective).symm
    let e₂ : ↥(tightCore R) ≃* ↥R := MulEquiv.subgroupCongr (tightCore_eq_self_of_isPGroup hR2)
    let e₃ : ↥R ≃* ↥(S : Subgroup R) :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hS.symm)
    exact ⟨(MulEquiv.subgroupCongr hg₀.symm).trans (((e₁.trans e₂).trans e₃).trans eS)⟩
  have hJN : Subgroup.centralizer ({u} : Set Y) ≤ Subgroup.normalizer ((J : Subgroup Y) : Set Y) :=
    (TightLargeHypR.typeRFam hL).tight J hJ.1.2.1 u hu
  have hXC : piGen π ≤ Subgroup.centralizer ({u} : Set Y) := hstd.piGen_le_centralizer hmax hu
  have hXn : ∀ c ∈ Subgroup.centralizer ({u} : Set Y), conjSub c (piGen π) = piGen π := by
    intro c hc
    have hcJ : conjSub c J = J := conjSub_eq_of_mem_normalizer (hJN hc)
    have h1 := isMaxOrb_conj hF hmax c
    rw [hcJ] at h1
    have h2' := maxOrb_unique hF hJ.1.2.1 h1 hmax
    rw [← piGen_conj, h2']
  set C := Subgroup.centralizer ({u} : Set Y) with hCdef
  have hX'n : ((piGen π).subgroupOf C).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hm : (c : Y) * x * (c : Y)⁻¹ ∈ conjSub (c : Y) (piGen π) := by
      rw [mem_conjSub_iff]
      have he : (c : Y)⁻¹ * ((c : Y) * x * (c : Y)⁻¹) * (c : Y) = x := by group
      rw [he]
      exact hx
    rw [hXn c c.2] at hm
    simpa using hm
  have hK' : tightCore (R.subgroupOf C) ≤ (piGen π).subgroupOf C := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxR, hx2⟩
    show (x : Y) ∈ piGen π
    apply le_piGen hK₀π
    refine Subgroup.subset_closure ⟨hxR, ?_⟩
    have h := hx2.map C.subtype
    rwa [MonoidHom.map_zpowers] at h
  have hHX : secH R u ≤ (piGen π).subgroupOf C :=
    subnormalClosure_le hK' (IsSubnormal.step le_top Subgroup.normal_subgroupOf
      (IsSubnormal.refl ⊤))
  have hnbrC : nbrGen (TC.nbrAdj Ω) J ≤ C := iSup₂_le fun M hM => fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((hstd.commutes_of_nbrAdj hM) u hu.mem b hb).symm
  have hnci : NoCentralInv π := by
    intro J' hJ' v hv hc
    obtain ⟨l, hl, rfl⟩ := hJ'
    have hlC : l ∈ C := hnbrC hl
    have hv' : v = l * t * l⁻¹ := hv.eq (hd.isUniqueInvolution_core.conj l)
    subst hv'
    have htX : ∀ x ∈ piGen π, x * t = t * x := by
      intro x hx
      have hy : l * x * l⁻¹ ∈ piGen π := by
        have h1 : l * x * l⁻¹ ∈ conjSub l (piGen π) := by
          rw [mem_conjSub_iff]
          have he : l⁻¹ * (l * x * l⁻¹) * l = x := by group
          rw [he]
          exact hx
        rwa [hXn l hlC] at h1
      have h2 := hc _ hy
      have h3 : l * (x * t) * l⁻¹ = l * (t * x) * l⁻¹ := by
        calc l * (x * t) * l⁻¹ = (l * x * l⁻¹) * (l * t * l⁻¹) := by group
          _ = (l * t * l⁻¹) * (l * x * l⁻¹) := h2
          _ = l * (t * x) * l⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h3)
    apply hE2
    have hcen : ∀ y : SecQ R u, y * E3.secT htu ht = E3.secT htu ht * y := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ y
      have hhX : ((h : C) : Y) ∈ piGen π := hHX h.2
      have hc' : (h : C) * (⟨t, htu⟩ : C) = (⟨t, htu⟩ : C) * (h : C) :=
        Subtype.ext (htX _ hhX)
      have hc'' : h * (⟨⟨t, htu⟩, ht⟩ : ↥(secH R u)) = (⟨⟨t, htu⟩, ht⟩ : ↥(secH R u)) * h :=
        Subtype.ext hc'
      show QuotientGroup.mk' _ h * QuotientGroup.mk' _ (⟨⟨t, htu⟩, ht⟩ : ↥(secH R u)) =
        QuotientGroup.mk' _ (⟨⟨t, htu⟩, ht⟩ : ↥(secH R u)) * QuotientGroup.mk' _ h
      rw [← map_mul, ← map_mul, hc'']
    have ht2 : E3.secT htu ht * E3.secT htu ht = 1 := by
      have h1 : t * t = 1 := by
        have h2 := pow_orderOf_eq_one t
        rw [hd.order, pow_two] at h2
        exact h2
      show QuotientGroup.mk' _ (⟨⟨t, htu⟩, ht⟩ : ↥(secH R u)) *
        QuotientGroup.mk' _ (⟨⟨t, htu⟩, ht⟩ : ↥(secH R u)) = 1
      rw [← map_mul]
      have h3 : (⟨⟨t, htu⟩, ht⟩ : ↥(secH R u)) * ⟨⟨t, htu⟩, ht⟩ = 1 :=
        Subtype.ext (Subtype.ext h1)
      rw [h3, map_one]
    refine ⟨Subgroup.zpowers (E3.secT htu ht), ⟨fun x hx g => ?_⟩,
      Balance.isPGroup_zpowers_of_mul_self_eq_one ht2, Subgroup.mem_zpowers _⟩
    have h1 : g * x * g⁻¹ = x := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have h2 : g * E3.secT htu ht ^ k = E3.secT htu ht ^ k * g :=
        ((Commute.zpow_left (hcen g).symm k)).symm.eq
      rw [h2, mul_inv_cancel_right]
    rw [h1]
    exact hx
  have hcfg : Twin1711.Cfg' Ω J π u g₀⁻¹ := by
    refine ⟨⟨hstd, ?_, hgen, hL.center, hJ.1.2.1, hmax, hnci, hu, hq8⟩, hconj⟩
    rintro _ ⟨a, rfl⟩
    exact ⟨a * g₀⁻¹, by rw [← hg₀, conjSub_mul, conjSub_inv_conjSub]⟩
  exact Twin1711.not_quasiE4 hT1 hT2 hcfg (hSec hP Y R S t hL hO hcn hsp J hJ u hu htu ht hE4 hE2)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

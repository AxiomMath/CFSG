module

public import CFSG.ClassicalInvolution.Q3.TL4E3Odd
public import CFSG.ClassicalInvolution.Q3.TL4VtxFam

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open scoped commutatorElement

theorem E3.tightInO2_of_hom {A B C : Type} [Group A] [Group B] [Group C] [Finite A] [Finite C]
    (f : A →* B) (g : A →* C) (hg : Function.Surjective g) (hf : Odd (Nat.card f.ker))
    (hC : classicalInvolutionOddCore C = ⊥) {a : A} (h : TightInO2 (f a)) : TightInO2 (g a) := by
  obtain ⟨P, hPn, hP2, hfa⟩ := h
  have hkn : (f.ker.map g).Normal := f.normal_ker.map g hg
  have hko : Odd (Nat.card (f.ker.map g)) := Odd.of_dvd_nat hf (f.ker.card_map_dvd g)
  have hkO : f.ker.map g ≤ classicalInvolutionOddCore C := le_sSup ⟨hkn, hko⟩
  rw [hC, le_bot_iff] at hkO
  refine ⟨(P.comap f).map g, (hPn.comap f).map g hg, ?_, ⟨a, hfa, rfl⟩⟩
  rintro ⟨_, x, hx, rfl⟩
  obtain ⟨k, hk⟩ := hP2 ⟨f x, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : x ^ 2 ^ k ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : g (x ^ 2 ^ k) ∈ f.ker.map g := ⟨_, h1, rfl⟩
  rw [hkO, Subgroup.mem_bot, map_pow] at h2
  simpa using h2

theorem E3.le_coreAt_sup {G : Type} [Group G] [Finite G] {R' M N : Subgroup G}
    (hM : tightCore R' = M) (hNodd : Odd (Nat.card N))
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) {w : G} (hw2 : IsPGroup 2 (Subgroup.zpowers w))
    (hwM : ∀ x ∈ M, w * x * w⁻¹ ∈ M) (hwN : ∀ x ∈ N, w * x * w⁻¹ ∈ N)
    (htriv : ∀ x ∈ M, w * x * w⁻¹ * x⁻¹ ∈ N) : M ≤ coreAt w M ⊔ N := by
  set NM := M ⊓ N with hNMdef
  have hNModd : Odd (Nat.card NM) := Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le inf_le_right)
  have hMNM : M ≤ Subgroup.normalizer (NM : Set G) := by
    intro m hm
    have hmN := hMN hm
    rw [Subgroup.mem_normalizer_iff] at hmN ⊢
    intro x
    constructor
    · rintro ⟨hxM, hxN⟩
      exact ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm), (hmN x).mp hxN⟩
    · rintro ⟨hxM, hxN⟩
      refine ⟨?_, (hmN x).mpr hxN⟩
      have e : x = m⁻¹ * (m * x * m⁻¹) * m := by group
      rw [e]
      exact M.mul_mem (M.mul_mem (M.inv_mem hm) hxM) hm
  have key : ∀ y ∈ M, IsPGroup 2 (Subgroup.zpowers y) → y ∈ coreAt w M ⊔ N := by
    intro y hyM hy2
    set B := NM ⊔ Subgroup.zpowers y with hBdef
    have hyB : Subgroup.zpowers y ≤ Subgroup.normalizer (NM : Set G) :=
      (Subgroup.zpowers_le.mpr hyM).trans hMNM
    have hBM : B ≤ M := sup_le inf_le_left (Subgroup.zpowers_le.mpr hyM)
    obtain ⟨P, hP, hPw⟩ := E3.exists_sylow_le_centralizer_of_modOdd (M := B) (N := NM) hNModd
      (le_sup_left.trans Subgroup.le_normalizer) hw2
      (fun x hx => ⟨hwM x hx.1, hwN x hx.2⟩)
      (fun x hx => ⟨M.mul_mem (hwM x (hBM hx)) (M.inv_mem (hBM hx)), htriv x (hBM hx)⟩)
    have hPc : P ≤ coreAt w M := le_coreAt w hP.2.1 (hP.1.trans hBM) hPw
    obtain ⟨b, hb, hyb⟩ := Sec7.exists_conj_le_of_isSylow2In hP hy2 le_sup_right
    obtain ⟨m, hm, r, hr, rfl⟩ := T7L.mem_sup_normalForm hyB hb
    have hp : (m * r)⁻¹ * y * (m * r) ∈ P := mem_conjSub_iff.mp (hyb (Subgroup.mem_zpowers y))
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
    have hyM' : y⁻¹ ∈ Subgroup.normalizer (NM : Set G) := hMNM (M.inv_mem hyM)
    have hrM : (y ^ k)⁻¹ ∈ Subgroup.normalizer (NM : Set G) :=
      hMNM (M.inv_mem (M.zpow_mem hyM k))
    have h1 : y⁻¹ * m⁻¹ * y ∈ NM := by
      have := (Subgroup.mem_normalizer_iff.mp hyM' m⁻¹).mp (NM.inv_mem hm)
      simpa using this
    have h2 : (y ^ k)⁻¹ * ((y⁻¹ * m⁻¹ * y) * m) * ((y ^ k)⁻¹)⁻¹ ∈ NM :=
      (Subgroup.mem_normalizer_iff.mp hrM _).mp (NM.mul_mem h1 hm)
    have hq : y⁻¹ * ((m * y ^ k)⁻¹ * y * (m * y ^ k)) ∈ NM := by
      have e : y⁻¹ * ((m * y ^ k)⁻¹ * y * (m * y ^ k)) =
          (y ^ k)⁻¹ * ((y⁻¹ * m⁻¹ * y) * m) * ((y ^ k)⁻¹)⁻¹ := by group
      rw [e]
      exact h2
    have e : y = ((m * y ^ k)⁻¹ * y * (m * y ^ k)) *
        (y⁻¹ * ((m * y ^ k)⁻¹ * y * (m * y ^ k)))⁻¹ := by group
    rw [e]
    exact (coreAt w M ⊔ N).mul_mem (Subgroup.mem_sup_left (hPc hp))
      (Subgroup.mem_sup_right (N.inv_mem hq.2))
  calc M = tightCore R' := hM.symm
    _ ≤ coreAt w M ⊔ N := (Subgroup.closure_le _).mpr fun y hy =>
        key y (by rw [← hM]; exact Subgroup.subset_closure hy) hy.2

theorem E3.conjSub_oddCoreOf {G : Type} [Group G] {H : Subgroup G} {l : G} (hl : l ∈ H) :
    conjSub l (oddCoreOf H) = oddCoreOf H := by
  have h := Vtx.oddCoreOf_map_of_inj (MulAut.conj l).toMonoidHom (MulAut.conj l).injective H
  have hH : H.map (MulAut.conj l).toMonoidHom = H := conjSub_eq_self_of_mem hl
  rw [hH] at h
  exact h.symm

theorem E3.orbOf_conj {G : Type} [Group G] {Ω : Set (Subgroup G)} (hc : ConjInvariant Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (J : Subgroup G) (g : G) :
    orbOf (TC.nbrAdj Ω) (conjSub g K) (conjSub g J) = conjSub g '' orbOf (TC.nbrAdj Ω) K J := by
  have hKg : conjSub g K ∈ Ω := hc g K hK
  have hgen : nbrGen (TC.nbrAdj Ω) (conjSub g K) = conjSub g (nbrGen (TC.nbrAdj Ω) K) := by
    rw [E3.nbrGen_eq_omegaNbrGen hKg, E3.nbrGen_eq_omegaNbrGen hK, E3.omegaNbrGen_conj hc]
  ext M
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [hgen, mem_conjSub_iff] at hl
    refine ⟨conjSub (g⁻¹ * l * g) J, ⟨_, hl, rfl⟩, ?_⟩
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨g * l * g⁻¹, ?_, ?_⟩
    · rw [hgen]
      exact conj_mem_conjSub hl
    · rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group

theorem E3.tightInO2_of_secInO2 {G : Type} [Group G] [Finite G] {r : ℕ}
    {Ω : Set (Subgroup G)} (h : TypeRFam r Ω) {a u : G} (ha : a * a = 1) {X : Subgroup G}
    {π : Set (Subgroup G)} (hX : X = ⨆ M ∈ π, M) {J RJ : Subgroup G} (hJcore : tightCore RJ = J)
    (hJΩ : J ∈ Ω) (hJπ : J ∈ π) (hu : IsUniqueInvolution J u)
    (hπ : ∀ M ∈ π, ∃ l ∈ X, conjSub l J = M) (hc : ∀ y ∈ X, ⁅a, y⁆ ∈ oddCoreOf X)
    (hOu : oddCoreOf X ≤ Subgroup.centralizer ({u} : Set G)) (hS : SecInO2 Ω J a u)
    (huX : u ∈ X) :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (⟨u, huX⟩ : ↥X)) := by
  classical
  set O := oddCoreOf X with hOdef
  have hcl := h.hyp.conjInvariant
  have hOodd : Odd (Nat.card O) := oddCoreOf_odd_natCard X
  have hOX : O ≤ X := oddCoreOf_le_self X
  have hXO : X ≤ Subgroup.normalizer (O : Set G) := fun l hl =>
    mem_normalizer_of_conjSub_eq (E3.conjSub_oddCoreOf hl)
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) := Balance.isPGroup_zpowers_of_mul_self_eq_one ha
  have hcomm : ∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ O := fun x hx => by
    have := hc x hx
    rwa [commutatorElement_def] at this
  have haO : ∀ x ∈ O, a * x * a⁻¹ ∈ O := fun x hx => by
    have e : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact O.mul_mem (hcomm x (hOX hx)) hx
  have hMX : ∀ M ∈ π, M ≤ X := fun M hM => by
    rw [hX]
    exact le_iSup₂ (f := fun M (_ : M ∈ π) => M) M hM
  have hmem : ∀ M ∈ π, XMem Ω a M := by
    intro M hM
    obtain ⟨l, hl, hlM⟩ := hπ M hM
    have hMΩ : M ∈ Ω := by
      rw [← hlM]
      exact hcl l J hJΩ
    have hz : IsUniqueInvolution M (l * u * l⁻¹) := by
      rw [← hlM]
      exact hu.conj l
    have hON : O ≤ Subgroup.normalizer (M : Set G) := by
      intro o ho
      apply h.tight M hMΩ _ hz
      have ho' : l⁻¹ * o * l ∈ O := by
        have := (Subgroup.mem_normalizer_iff.mp (hXO (X.inv_mem hl)) o).mp ho
        simpa using this
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hOu ho')
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc o * (l * u * l⁻¹) = l * ((l⁻¹ * o * l) * u) * l⁻¹ := by group
        _ = l * (u * (l⁻¹ * o * l)) * l⁻¹ := by rw [h1]
        _ = l * u * l⁻¹ * o := by group
    obtain ⟨P, hP, hPa⟩ := E3.exists_sylow_le_centralizer_of_modOdd hOodd hON ha2 haO
      (fun x hx => hcomm x (hMX M hM hx))
    have hzP := Sec6Gen.mem_of_isSylow2In hz hP
    have haN : a ∈ Subgroup.normalizer (M : Set G) := by
      apply h.tight M hMΩ _ hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hPa hzP)).symm
    exact ⟨hMΩ, haN, P, hP, fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hPa hx)⟩
  have hcov : ∀ M ∈ π, M ≤ coreAt a M ⊔ O := by
    intro M hM
    obtain ⟨l, hl, hlM⟩ := hπ M hM
    have hMcore : tightCore (conjSub l RJ) = M := by rw [← conjSub_tightCore, hJcore, hlM]
    exact E3.le_coreAt_sup hMcore hOodd ((hMX M hM).trans hXO) ha2
      (fun x hx => (Subgroup.mem_normalizer_iff.mp (hmem M hM).2.1 x).mp hx) haO
      (fun x hx => hcomm x (hMX M hM hx))
  set Xa : Subgroup G := ⨆ M ∈ π, coreAt a M with hXadef
  have hXXa : X ≤ Xa ⊔ O := by
    calc X = ⨆ M ∈ π, M := hX
      _ ≤ Xa ⊔ O := iSup₂_le fun M hM => (hcov M hM).trans (sup_le_sup_right
          (le_iSup₂ (f := fun M (_ : M ∈ π) => coreAt a M) M hM) O)
  have hXaY : Xa ≤ layerY Ω a := iSup₂_le fun M hM => coreAt_le_layerY (hmem M hM)
  have hXaX : Xa ≤ X := iSup₂_le fun M hM => (coreAt_le a M).trans (hMX M hM)
  have hXaO : Xa ≤ Subgroup.normalizer (O : Set G) := hXaX.trans hXO
  have hdec : ∀ x ∈ X, ∃ y ∈ Xa, y⁻¹ * x ∈ O := by
    intro x hx
    have hx' : x ∈ O ⊔ Xa := by
      rw [sup_comm]
      exact hXXa hx
    obtain ⟨o, ho, y, hy, rfl⟩ := T7L.mem_sup_normalForm hXaO hx'
    refine ⟨y, hy, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (hXaO (Xa.inv_mem hy)) o).mp ho
    have e : y⁻¹ * (o * y) = y⁻¹ * o * y⁻¹⁻¹ := by group
    rw [e]
    exact this
  have hconj : ∀ M ∈ π, ∃ y ∈ Xa, conjSub y J = M := by
    intro M hM
    obtain ⟨l, hl, rfl⟩ := hπ M hM
    obtain ⟨y, hy, hyl⟩ := hdec l hl
    refine ⟨y, hy, ?_⟩
    have hJ' : conjSub (y⁻¹ * l) J = J :=
      mem_normalizer_iff_conjSub_eq.mp (h.tight J hJΩ u hu (hOu hyl))
    calc conjSub y J = conjSub y (conjSub (y⁻¹ * l) J) := by rw [hJ']
      _ = conjSub l J := by rw [← conjSub_mul]; congr 1; group
  set q := QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω a)) with hqdef
  have himg : ∀ M ∈ π, secImg Ω a M ≤ secOrb Ω J a := by
    intro M hM
    obtain ⟨y, hy, rfl⟩ := hconj M hM
    have e : secImg Ω a (conjSub y J) = conjSub (q ⟨y, hXaY hy⟩) (secImg Ω a J) :=
      (conjSub_secImg ⟨y, hXaY hy⟩ J).symm
    rw [e]
    refine Vtx.conjSub_le_orbGrp _ ⟨q ⟨y, hXaY hy⟩, ?_⟩
    rw [omegaGen_secFam]
    exact Subgroup.mem_top _
  have hXaW : ∀ x (hx : x ∈ Xa), q ⟨x, hXaY hx⟩ ∈ secOrb Ω J a := by
    have hle : Xa ≤ ((secOrb Ω J a).comap q).map (layerY Ω a).subtype := by
      refine iSup₂_le fun M hM c hcM => ?_
      have hcY : c ∈ layerY Ω a := coreAt_le_layerY (hmem M hM) hcM
      exact ⟨⟨c, hcY⟩, himg M hM ⟨⟨c, hcY⟩, Subgroup.mem_subgroupOf.mpr hcM, rfl⟩, rfl⟩
    intro x hx
    obtain ⟨x', hx', hxe⟩ := hle hx
    have e : x' = ⟨x, hXaY hx⟩ := Subtype.ext hxe
    rw [← e]
    exact hx'
  let φ : ↥Xa →* SecQuot Ω a := q.comp (Subgroup.inclusion hXaY)
  let f₁ : ↥Xa →* ↥(secOrb Ω J a) := φ.codRestrict (secOrb Ω J a) fun x => hXaW x x.2
  let g₁ : ↥Xa →* ↥X ⧸ classicalInvolutionOddCore ↥X :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)).comp (Subgroup.inclusion hXaX)
  have hg₁ : Function.Surjective g₁ := by
    intro ξ
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ ξ
    obtain ⟨y, hy, hyx⟩ := hdec x x.2
    obtain ⟨hmX, hmO⟩ := mem_oddCoreOf_iff.mp hyx
    refine ⟨⟨y, hy⟩, ?_⟩
    show QuotientGroup.mk' _ (Subgroup.inclusion hXaX ⟨y, hy⟩) = QuotientGroup.mk' _ x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e : (Subgroup.inclusion hXaX ⟨y, hy⟩)⁻¹ * x = ⟨y⁻¹ * x, hmX⟩ := Subtype.ext (by simp)
    rw [e]
    exact hmO
  have hker : Odd (Nat.card f₁.ker) := by
    have e : f₁.ker = φ.ker := MonoidHom.ker_codRestrict _ _ _
    rw [e]
    have hinj : Function.Injective (Subgroup.inclusion hXaY) := Subgroup.inclusion_injective hXaY
    have hle : φ.ker.map (Subgroup.inclusion hXaY) ≤
        classicalInvolutionOddCore ↥(layerY Ω a) := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective hinj] at h1
    exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card _) h1
  have hC : classicalInvolutionOddCore (↥X ⧸ classicalInvolutionOddCore ↥X) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree _
  have huJ : u ∈ coreAt a J := (isUniqueInvolution_coreAt h (hmem J hJπ) hu).mem
  have huXa : u ∈ Xa := le_iSup₂ (f := fun M (_ : M ∈ π) => coreAt a M) J hJπ huJ
  have h₁ : TightInO2 (f₁ ⟨u, huXa⟩) := by
    obtain ⟨P, hPn, hP2, hP⟩ := hS
    exact ⟨P, hPn, hP2, hP _
      ⟨⟨u, hXaY huXa⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers u), rfl⟩⟩
  exact E3.tightInO2_of_hom f₁ g₁ hg₁ hker hC h₁

end CFSG.ClassicalInvolution.Q3.TL4

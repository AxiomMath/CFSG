module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264X
public import CFSG.ClassicalInvolution.Q3.TL4SecIdAE5D
public import CFSG.ClassicalInvolution.Q3.TL4Conn264B

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan ThmDHyp AEIdent)
open CFSG.ClassicalInvolution.Q3.AE (memBar)
open scoped commutatorElement

namespace AE5

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem fix_twin_of_sq (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L')
    (I : AEIdent Φ 5) {A B : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ Φ) {α : Finset (Fin 5)}
    {hα : α.card = 4} {b : Bool} (hlA : (A.subgroupOf (pSpan Φ)).map I.φ = memBar α hα b)
    (hlB : (B.subgroupOf (pSpan Φ)).map I.φ = memBar α hα (!b)) {σ : MulAut X}
    (hσσ : σ * σ = 1) (hσA : ∀ k ∈ A, σ k = k) (hσB : ∀ k ∈ B, σ k ∈ B) :
    ∀ k ∈ B, σ k = k := by
  obtain ⟨y, hy⟩ := exists_conj_of_map_mem hgen I σ
    (map_mem_of_fix h.hyp.conjInvariant htr hA hσA)
  have hcA := comm_of_fix hgen I hy hA hσA
  rw [hlA] at hcA
  have hnB : ∀ a ∈ memBar α hα (!b), y * a * y⁻¹ ∈ memBar α hα (!b) := by
    intro a ha
    rw [← hlB] at ha ⊢
    obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hB ha
    show y * I.φ ⟨l, mem_pSpan hgen l⟩ * y⁻¹ ∈ _
    rw [← hy l]
    exact I.mem_map hB (hσB l hl)
  have hyy : y * y = 1 := by
    refine eq_one_of_comm_aeBar fun g hg => ?_
    rw [← I.range_eq] at hg
    obtain ⟨⟨w, hwP⟩, rfl⟩ := hg
    show y * y * I.φ ⟨w, mem_pSpan hgen w⟩ = I.φ ⟨w, mem_pSpan hgen w⟩ * (y * y)
    have e1 : σ (σ w) = w := congrArg (fun τ : MulAut X => τ w) hσσ
    have e2 : y * (y * I.φ ⟨w, mem_pSpan hgen w⟩ * y⁻¹) * y⁻¹ =
        I.φ ⟨w, mem_pSpan hgen w⟩ := by
      rw [← hy w, ← hy (σ w)]
      exact congrArg (fun v => I.φ ⟨v, mem_pSpan hgen v⟩) e1
    calc y * y * I.φ ⟨w, mem_pSpan hgen w⟩ =
        (y * (y * I.φ ⟨w, mem_pSpan hgen w⟩ * y⁻¹) * y⁻¹) * (y * y) := by group
      _ = I.φ ⟨w, mem_pSpan hgen w⟩ * (y * y) := by rw [e2]
  have hcB := comm_of_twin_of_sq α hα b hyy hcA hnB
  intro k hk
  have e1 : I.φ ⟨σ k, mem_pSpan hgen _⟩ = I.φ ⟨k, mem_pSpan hgen k⟩ := by
    have hkM : I.φ ⟨k, mem_pSpan hgen k⟩ ∈ memBar α hα (!b) := by
      rw [← hlB]
      exact I.mem_map hB hk
    rw [hy k, hcB _ hkM, mul_inv_cancel_right]
  exact I.injOn (by norm_num) hB (natCard_mem h hO hgen I hB) hlB (hσB k hk) hk e1

end AE5

theorem orbGrp_map_eq_of_top {Q : Type} [Group Q] {Φ : Set (Subgroup Q)}
    (htop : omegaGen Φ = ⊤) {K : Subgroup Q} (σ : MulAut Q)
    (hσK : K.map σ.toMonoidHom = K) :
    (Vtx.orbGrp Φ K).map σ.toMonoidHom = Vtx.orbGrp Φ K := by
  have hmem : ∀ g : Q, g ∈ omegaGen Φ := fun g => by
    rw [htop]
    exact Subgroup.mem_top g
  apply le_antisymm
  · rw [Vtx.orbGrp, Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [← conjSub_map σ.toMonoidHom (g : Q) K, hσK]
    exact Vtx.conjSub_le_orbGrp K ⟨_, hmem _⟩
  · refine iSup_le fun g => ?_
    have e : conjSub (g : Q) K = (conjSub (σ.symm g) K).map σ.toMonoidHom := by
      rw [← conjSub_map σ.toMonoidHom (σ.symm g) K, hσK, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]
    rw [e]
    exact Subgroup.map_mono (Vtx.conjSub_le_orbGrp K ⟨_, hmem _⟩)

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.false_of_ae5_secOrb (hLC : TightLambdaCommR 3 n)
    (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hΛp : tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))
    (I : AEIdent (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) 5) : False := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hcl := hΩ.conjInvariant
  have hK : K ∈ Ω := hs.mem
  have hXK : XMem Ω (z * t) K := hs.xMem_K
  have hXJ : XMem Ω (z * t) J := hs.xMem_J
  obtain ⟨t₁, ht1sq, -, hne, htt1, hzt1, hcommR, hnJ, -, -, J₁, hJ₁, hJ₁X, hJ₁t⟩ :=
    hs.exists_good_involution_E4_of_ne_top hLC hΛp hE
  have hKX := hs.not_le_omegaNbrGen_of_ne_top (tightSecNbrGenR_of_comm hLC)
    (ne_top_of_le_ne_top hΛp le_sup_right)
  have ht1C : t₁ ∈ Subgroup.centralizer ({z * t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t₁ * (z * t) = (t₁ * z) * t := by group
      _ = (z * t₁) * t := by rw [hzt1]
      _ = z * (t₁ * t) := by group
      _ = z * (t * t₁) := by rw [htt1]
      _ = z * t * t₁ := by group
  have hnt := hs.not_trivial_on_secImg_J_of_not_le hKX hE ht1C ht1sq hne htt1 hnJ hJ₁ hJ₁X hJ₁t
  have hyY1 := mem_normalizer_layerY hcl ht1C
  set σ : MulAut (SecQuot Ω (z * t)) := s26Act (layerY Ω (z * t)) ⟨t₁, hyY1⟩ with hσ
  have hσsq : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have : (⟨t₁, hyY1⟩ * ⟨t₁, hyY1⟩ : ↥(Subgroup.normalizer
        ((layerY Ω (z * t) : Subgroup Y) : Set Y))) = 1 := Subtype.ext ht1sq
    rw [this, map_one]
  have hσσx : ∀ x, σ (σ x) = x := fun x =>
    congrArg (fun τ : MulAut (SecQuot Ω (z * t)) => τ x) hσsq
  have hyNK : t₁ ∈ Subgroup.normalizer (K : Set Y) :=
    hs.large.datum.le_normalizer_core (Subgroup.mem_centralizer_singleton_iff.mpr hzt1.symm)
  have hσK : (secImg Ω (z * t) K).map σ.toMonoidHom = secImg Ω (z * t) K := by
    have e := secImg_conjSub_eq_map hcl ht1C K
    rw [mem_normalizer_iff_conjSub_eq.mp hyNK] at e
    exact e.symm
  have hσJ : (secImg Ω (z * t) J).map σ.toMonoidHom = secImg Ω (z * t) J := by
    have e := secImg_conjSub_eq_map hcl ht1C J
    rw [hnJ] at e
    exact e.symm
  set Xb := secOrb Ω K (z * t) with hXbdef
  have hσX : Xb.map σ.toMonoidHom = Xb := orbGrp_map_eq_of_top omegaGen_secFam σ hσK
  have hσmem : ∀ x ∈ Xb, σ x ∈ Xb := fun x hx => by
    rw [← hσX]
    exact ⟨x, hx, rfl⟩
  let σ' : MulAut ↥Xb :=
    { toFun := fun x => ⟨σ x, hσmem x x.2⟩
      invFun := fun x => ⟨σ x, hσmem x x.2⟩
      left_inv := fun x => Subtype.ext (hσσx x)
      right_inv := fun x => Subtype.ext (hσσx x)
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : SecQuot Ω (z * t)) y) }
  have hσ'σ' : σ' * σ' = 1 := MulEquiv.ext fun x => Subtype.ext (hσσx x)
  have hKXb : secImg Ω (z * t) K ≤ Xb := Vtx.le_orbGrp _
  obtain ⟨g₀, hg₀⟩ := hcj
  have hJXb : secImg Ω (z * t) J ≤ Xb := by
    rw [← hg₀]
    exact Vtx.conjSub_le_orbGrp _ ⟨g₀, by rw [omegaGen_secFam]; exact Subgroup.mem_top _⟩
  have hA : (secImg Ω (z * t) K).subgroupOf Xb ∈ restrictFamily (secFam Ω (z * t)) Xb :=
    ⟨_, secImg_mem hXK, hKXb, rfl⟩
  have hB : (secImg Ω (z * t) J).subgroupOf Xb ∈ restrictFamily (secFam Ω (z * t)) Xb :=
    ⟨_, secImg_mem hXJ, hJXb, rfl⟩
  have hTR : TypeRFam 3 (restrictFamily (secFam Ω (z * t)) Xb) :=
    (h.secFam (x := z * t)).restrict Xb
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1 hs.hR.2.1
  have hcommK : ∀ k ∈ K, ⁅t₁, k⁆ ∈ oddCoreOf K := fun k hk =>
    comm_mem_oddCoreOf_of_twoGroup (h.twoGroup K hK) hRsyl hyNK (fun p hp => (hcommR p hp).symm)
      hk
  have hσA0 := secAct_mul_inv_mem hcl ht1C hXK hyNK hcommK
  have h2K : IsPGroup 2 ↥(secImg Ω (z * t) K) :=
    (hD.two _ hA).of_equiv (Subgroup.subgroupOfEquivOfLe hKXb)
  have hσA : ∀ k ∈ (secImg Ω (z * t) K).subgroupOf Xb, σ' k = k := by
    intro k hk
    have hk' : (k : SecQuot Ω (z * t)) ∈ secImg Ω (z * t) K := Subgroup.mem_subgroupOf.mp hk
    have h1 : σ k * (k : SecQuot Ω (z * t))⁻¹ ∈ oddCoreOf (secImg Ω (z * t) K) := hσA0 _ hk'
    have h1K : σ k * (k : SecQuot Ω (z * t))⁻¹ ∈ secImg Ω (z * t) K :=
      oddCoreOf_le_self _ h1
    have h2 : σ k * (k : SecQuot Ω (z * t))⁻¹ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h1
        (h2K.to_le (Subgroup.zpowers_le.mpr h1K))
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have hσB : ∀ k ∈ (secImg Ω (z * t) J).subgroupOf Xb,
      σ' k ∈ (secImg Ω (z * t) J).subgroupOf Xb := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    show σ k ∈ secImg Ω (z * t) J
    rw [← hσJ]
    exact ⟨k, hk, rfl⟩
  have hKJ : secImg Ω (z * t) K ≠ secImg Ω (z * t) J := hs.secImg_J_mem_omegaNbr.2.1.symm
  obtain ⟨γ₁, h₁, b₁, hlA⟩ := I.label _ hA
  obtain ⟨γ₂, h₂, b₂, hlB⟩ := I.label _ hB
  have hγ : γ₁ = γ₂ := by
    rcases hs.labels_eq_or_disjoint hD (m := 5) (by norm_num) I.φ hKXb hJXb hlA hlB with e | hd
    · exact e
    · exfalso
      have hc := Finset.card_union_of_disjoint hd
      have hle := Finset.card_le_univ (γ₂ ∪ γ₁)
      rw [Fintype.card_fin, hc, h₁, h₂] at hle
      omega
  subst hγ
  have hb : b₂ = !b₁ := by
    by_contra hb
    have hbb : b₂ = b₁ := by cases b₁ <;> cases b₂ <;> simp_all
    subst hbb
    apply hKJ
    have e := AE5.eq_of_map_eq hTR hD.odd hD.gen I hA hB (hlA.trans hlB.symm)
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hKXb, inf_eq_left.mpr hJXb] at e
    exact e
  subst hb
  have hfix := AE5.fix_twin_of_sq hTR hD.odd hD.gen hD.trans I hA hB hlA hlB hσ'σ' hσA hσB
  refine hnt fun kb hkb => ?_
  have hk : (⟨kb, hJXb hkb⟩ : ↥Xb) ∈ (secImg Ω (z * t) J).subgroupOf Xb :=
    Subgroup.mem_subgroupOf.mpr hkb
  have e : σ kb = kb := congrArg Subtype.val (hfix _ hk)
  show σ kb * kb⁻¹ ∈ _
  rw [e, mul_inv_cancel]
  exact Subgroup.one_mem _

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

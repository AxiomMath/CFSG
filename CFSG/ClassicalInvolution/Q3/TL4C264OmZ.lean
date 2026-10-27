module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264T
public import CFSG.ClassicalInvolution.Q3.TL4Conn26YS

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame (CentOmega3)

theorem card_eq_eight_of_isSylow2In {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (h : TypeRFam 3 Φ) {L Q : Subgroup X} (hL : L ∈ Φ) (hQ : IsSylow2In Q L) :
    Nat.card ↥Q = 8 := by
  obtain ⟨e⟩ : Nonempty (↥Q ≃* QuaternionGroup 2) := h.quat L hL Q hQ
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem centOmega3_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CentOmega3 A) : CentOmega3 B := by
  have e' : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  unfold CentOmega3 at h ⊢
  rcases h with h | h | h | ⟨k, hk, h⟩ | ⟨k, hk, h⟩ | ⟨k, hk, h⟩
  · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e' h)
  · exact Or.inr (Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e' h))
  · exact Or.inr (Or.inr (Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e' h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, hk, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e' h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, hk, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e' h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨k, hk, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e' h⟩))))

section Section

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem secCyc_eq_zpowers {x w : G} (hw : w ∈ layerY Ω x) :
    secCyc Ω x w = Subgroup.zpowers
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨w, hw⟩) := by
  have e : (Subgroup.zpowers w).subgroupOf (layerY Ω x) = Subgroup.zpowers ⟨w, hw⟩ := by
    ext c
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm)⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, by rw [Subgroup.coe_zpow]⟩
  rw [secCyc, e, MonoidHom.map_zpowers]

omit [Finite G] in
theorem exists_centOmega3_secCyc {K : Subgroup G} {x : G} (htop : secOrb Ω K x = ⊤)
    (hω : SecTwinOmega Ω K x) :
    ∃ (N : Subgroup (SecQuot Ω x)) (_ : N.Normal), N = secCyc Ω x x ∧
      CentOmega3 (SecQuot Ω x ⧸ N) := by
  obtain ⟨N, hNn, -, -, hN, hcent⟩ := hω
  set e : ↥(secOrb Ω K x) ≃* SecQuot Ω x :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv with hedef
  have he : N.map (e : ↥(secOrb Ω K x) →* SecQuot Ω x) = secCyc Ω x x := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
      exact (hN c).mp hc
    · intro hy
      have hyX : y ∈ secOrb Ω K x := by
        rw [htop]
        exact Subgroup.mem_top y
      exact Subgroup.mem_map.mpr ⟨⟨y, hyX⟩, (hN _).mpr hy, rfl⟩
  have hn : (secCyc Ω x x).Normal := he ▸ hNn.map _ e.surjective
  exact ⟨_, hn, rfl, centOmega3_of_mulEquiv (QuotientGroup.congr N _ e he) hcent⟩

end Section

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.secOrb_eq_top_of_E4 (h4 : Thm4RBelow 3 n)
    (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t)) :
    secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) = ⊤ := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΦ := h.secFam (x := z * t)
  have hO := secQuot_oddCore_eq_bot (Ω := Ω) (x := z * t)
  have hn := hs.natCard_secQuot_lt
  have hKΦ := secImg_mem hs.xMem_K
  have hJΦ := secImg_mem hs.xMem_J
  obtain ⟨g₀, hg₀⟩ := hcj
  have hg₀G : g₀ ∈ omegaGen (secFam Ω (z * t)) := by
    rw [omegaGen_secFam]
    exact Subgroup.mem_top _
  rw [eq_top_iff, ← omegaGen_secFam (Ω := Ω) (x := z * t)]
  refine iSup₂_le fun M hM => ?_
  by_contra hMX
  have hnc : ¬ ∃ g ∈ omegaGen (secFam Ω (z * t)), conjSub g M = secImg Ω (z * t) K := by
    rintro ⟨g, hg, e⟩
    apply hMX
    have e' : M = conjSub g⁻¹ (secImg Ω (z * t) K) := by rw [← e, conjSub_inv_conjSub]
    rw [e']
    exact Vtx.conjSub_le_orbGrp _ ⟨g⁻¹, (omegaGen _).inv_mem hg⟩
  have hncJ : ¬ ∃ g ∈ omegaGen (secFam Ω (z * t)), conjSub g M = secImg Ω (z * t) J := by
    rintro ⟨g, hg, e⟩
    refine hnc ⟨g₀⁻¹ * g, (omegaGen _).mul_mem ((omegaGen _).inv_mem hg₀G) hg, ?_⟩
    rw [conjSub_mul, e, ← hg₀, conjSub_inv_conjSub]
  have hcK := Vtx.commutes_of_not_conj h4 hΦ hO hn hM hKΦ hnc
  have hcJ := Vtx.commutes_of_not_conj h4 hΦ hO hn hM hJΦ hncJ
  obtain ⟨-, hne, T', hT', hT'J, hT'N⟩ := hs.secImg_J_mem_omegaNbr
  have hT'syl : IsSylow2In T' (secImg Ω (z * t) J) :=
    Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΦ.hyp hJΦ hT' hT'J
  have hHN : secImg Ω (z * t) K ⊔ T' ≤
      Subgroup.normalizer ((secImg Ω (z * t) K : Subgroup _) : Set _) :=
    sup_le Subgroup.le_normalizer hT'N
  obtain ⟨V, hV, hT'V⟩ := IsSylow2In.exists_ge hT'syl.2.1 (le_sup_right : T' ≤ _ ⊔ T')
  have hVK : IsSylow2In (V ⊓ secImg Ω (z * t) K) (secImg Ω (z * t) K) :=
    AscP1Nine3.isSylow2In_inf_of_le_normalizer' hV le_sup_left hHN
  obtain ⟨QM, hQM, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := M) IsPGroup.of_bot bot_le
  have hcent : secImg Ω (z * t) K ⊔ secImg Ω (z * t) J ≤ Subgroup.centralizer (M : Set _) := by
    refine sup_le (fun b hb => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun a ha => hcK a ha b hb
    · exact Subgroup.mem_centralizer_iff.mpr fun a ha => hcJ a ha b hb
  have hQN : QM ≤ Subgroup.normalizer (V : Set _) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.le_centralizer_iff]
    exact (hV.1.trans (sup_le_sup_left hT'J _)).trans
      (hcent.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQM.1)))
  have hD2 : IsPGroup 2 ↥(QM ⊔ V) := hQM.2.1.to_sup_of_normal_right' hV.2.1 hQN
  have hlt : ∀ {B Q : Subgroup (SecQuot Ω (z * t))}, B ∈ secFam Ω (z * t) → IsSylow2In Q B →
      Q ≤ QM ⊔ V → 2 < Nat.card ↥(B ⊓ (QM ⊔ V)) := by
    intro B Q hB hQ hQD
    have h1 : Nat.card ↥Q = 8 := card_eq_eight_of_isSylow2In hΦ hB hQ
    have h2 : Nat.card ↥Q ≤ Nat.card ↥(B ⊓ (QM ⊔ V)) := Subgroup.card_le_of_le (le_inf hQ.1 hQD)
    omega
  have hKM : secImg Ω (z * t) K ≠ M := fun e => hMX (e ▸ Vtx.le_orbGrp _)
  have hJM : secImg Ω (z * t) J ≠ M := by
    intro e
    apply hMX
    rw [← e, ← hg₀]
    exact Vtx.conjSub_le_orbGrp _ ⟨g₀, hg₀G⟩
  have hcM := hlt hM hQM le_sup_left
  obtain ⟨L, hL, rfl⟩ := mem_secFam_iff.mp hM
  exact false_of_three_secImg_E4 hs.partIHypG hs.hW.1 hE hs.xMem_K hs.xMem_J hL hne.symm hKM hJM
    hD2 (hlt hKΦ hVK (inf_le_left.trans le_sup_right)) (hlt hJΦ hT'syl (hT'V.trans le_sup_right))
    hcM

theorem TightStd8R.exists_centOmega3_of_E4 (h4 : Thm4RBelow 3 n)
    (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (hω : SecTwinOmega (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)) :
    ∃ (N : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t))) (_ : N.Normal),
      N = secCyc (CoreAssembly.conjClass (tightCore Rd)) (z * t) (z * t) ∧
        CentOmega3 (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t) ⧸ N) :=
  exists_centOmega3_secCyc (hs.secOrb_eq_top_of_E4 h4 hE hcj) hω

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

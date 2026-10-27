module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W4
public import CFSG.ClassicalInvolution.Q3.TL4Conn264F

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem ne_of_mem_omegaNbr)
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan ThmDHyp AEIdent AEIdentOn E8Struct)
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ W : Subgroup Y} {P : Sylow 2 Y}

theorem std8_pair_of_three (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hthree : NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R)))
    (hKN : (secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R)).Normal)
    (hJN : (secImg (CoreAssembly.conjClass (tightCore R)) (t * u) J).Normal) :
    ∀ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) (t * u), M.Normal →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) ∨
        M = secImg (CoreAssembly.conjClass (tightCore R)) (t * u) J := by
  intro M hM hMN
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have h := TightLargeHypR.typeRFam hs.large
  obtain ⟨L, hL, rfl⟩ := mem_secFam_iff.mp hM
  have hKJ : secImg Ω (t * u) (tightCore R) ≠ secImg Ω (t * u) J :=
    secImg_ne h hs.xMem_K hs.xMem_J hs.hz hs.ht
      (Q3CL.T8.mul_comm_of_mem_omegaNbr hs.hyp hs.hz hs.hJ hs.ht)
      (ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht)
  by_contra hne
  rw [not_or] at hne
  set H : Subgroup (SecQuot Ω (t * u)) := secImg Ω (t * u) (tightCore R) ⊔
    secImg Ω (t * u) J ⊔ secImg Ω (t * u) L with hHdef
  obtain ⟨Pb, hPb, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := H) IsPGroup.of_bot bot_le
  have hcard : ∀ B ∈ secFam Ω (t * u), B.Normal → B ≤ H → 2 < Nat.card ↥(B ⊓ Pb) := by
    intro B hB hBN hBH
    have hsyl : IsSylow2In (Pb ⊓ B) B :=
      AscP1Nine3.isSylow2In_inf_of_le_normalizer' hPb hBH fun y _ => by
        rw [Subgroup.normalizer_eq_top_iff.mpr hBN]
        exact Subgroup.mem_top y
    obtain ⟨e⟩ : Nonempty (↥(Pb ⊓ B) ≃* QuaternionGroup 2) := h.secFam.quat B hB _ hsyl
    rw [inf_comm, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  exact false_of_three_secImg_of hs.partIHypG hthree hs.xMem_K hs.xMem_J hL
    hKJ (Ne.symm hne.1) (Ne.symm hne.2) hPb.2.1
    (hcard _ (secImg_mem hs.xMem_K) hKN (le_sup_left.trans le_sup_left))
    (hcard _ (secImg_mem hs.xMem_J) hJN (le_sup_right.trans le_sup_left))
    (hcard _ hM hMN le_sup_right)

open CFSG.ClassicalInvolution.Q3.TC.Thin (le_pSpan)
open CFSG.ClassicalInvolution.Q3.AE (AEQ memBar)

private theorem c264One_of_orb_of_three (h4 : Thm4RBelow 3 n)
    (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hthree : NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R)))
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore R)) (tightCore R) J (t * u))
    (h2K : IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R)))
    (h2J : IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore R)) (t * u) J))
    (honly : ∀ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) (t * u),
      M ≤ secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) →
        M = secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) ∨
          M = secImg (CoreAssembly.conjClass (tightCore R)) (t * u) J) :
    C264One (CoreAssembly.conjClass (tightCore R)) t u := by
  refine hs.c264One_of_conj fun c hc => ?_
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΦ := h.secFam (x := t * u)
  have hcl := hs.hyp.conjInvariant
  have hKc : XMem Ω (t * u) (conjSub c (tightCore R)) := XMem.conj' hcl hs.xMem_K hc
  have hMΦ := secImg_mem hKc
  by_cases hMX : secImg Ω (t * u) (conjSub c (tightCore R)) ≤ secOrb Ω (tightCore R) (t * u)
  · exact honly _ hMΦ hMX
  exfalso
  have hKΦ := secImg_mem hs.xMem_K
  have hJΦ := secImg_mem hs.xMem_J
  have hO := secQuot_oddCore_eq_bot (Ω := Ω) (x := t * u)
  have hn := hs.natCard_secQuot_lt
  have hnc : ¬ ∃ g ∈ omegaGen (secFam Ω (t * u)),
      conjSub g (secImg Ω (t * u) (conjSub c (tightCore R))) =
        secImg Ω (t * u) (tightCore R) := by
    rintro ⟨g, hg, e⟩
    apply hMX
    have e' : secImg Ω (t * u) (conjSub c (tightCore R)) =
        conjSub g⁻¹ (secImg Ω (t * u) (tightCore R)) := by
      rw [← e, conjSub_inv_conjSub]
    rw [e']
    exact Vtx.conjSub_le_orbGrp _ ⟨g⁻¹, (omegaGen _).inv_mem hg⟩
  obtain ⟨g₀, hg₀⟩ := hcj
  have hg₀G : g₀ ∈ omegaGen (secFam Ω (t * u)) := by
    rw [omegaGen_secFam]
    exact Subgroup.mem_top _
  have hncJ : ¬ ∃ g ∈ omegaGen (secFam Ω (t * u)),
      conjSub g (secImg Ω (t * u) (conjSub c (tightCore R))) = secImg Ω (t * u) J := by
    rintro ⟨g, hg, e⟩
    refine hnc ⟨g₀⁻¹ * g, (omegaGen _).mul_mem ((omegaGen _).inv_mem hg₀G) hg, ?_⟩
    rw [conjSub_mul, e, ← hg₀, conjSub_inv_conjSub]
  have hcK := Vtx.commutes_of_not_conj h4 hΦ hO hn hMΦ hKΦ hnc
  have hcJ := Vtx.commutes_of_not_conj h4 hΦ hO hn hMΦ hJΦ hncJ
  have hM2 : IsPGroup 2 ↥(secImg Ω (t * u) (conjSub c (tightCore R))) := by
    rw [secImg_conjSub_eq_map hcl hc]
    exact h2K.map _
  have hJN : secImg Ω (t * u) J ≤
      Subgroup.normalizer ((secImg Ω (t * u) (tightCore R) : Subgroup _) : Set _) := by
    obtain ⟨-, -, T', hT', hT'J, hT'N⟩ := hs.secImg_J_mem_omegaNbr
    have hT'syl : IsSylow2In T' (secImg Ω (t * u) J) :=
      Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΦ.hyp hJΦ hT' hT'J
    have hTJ : T' = secImg Ω (t * u) J :=
      (hT'syl.2.2 _ le_rfl h2J hT'syl.1).symm
    rw [← hTJ]
    exact hT'N
  have hJK2 : IsPGroup 2 ↥(secImg Ω (t * u) J ⊔ secImg Ω (t * u) (tightCore R)) :=
    h2J.to_sup_of_normal_right' h2K hJN
  have hMN : secImg Ω (t * u) (conjSub c (tightCore R)) ≤
      Subgroup.normalizer (((secImg Ω (t * u) J ⊔ secImg Ω (t * u) (tightCore R) :
        Subgroup _)) : Set _) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcJ a ha b hb
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcK a ha b hb
  have hP2 := hM2.to_sup_of_normal_right' hJK2 hMN
  have hcard : ∀ {B : Subgroup (SecQuot Ω (t * u))}, B ∈ secFam Ω (t * u) → IsPGroup 2 ↥B →
      B ≤ secImg Ω (t * u) (conjSub c (tightCore R)) ⊔
        (secImg Ω (t * u) J ⊔ secImg Ω (t * u) (tightCore R)) →
      2 < Nat.card ↥(B ⊓ (secImg Ω (t * u) (conjSub c (tightCore R)) ⊔
        (secImg Ω (t * u) J ⊔ secImg Ω (t * u) (tightCore R)))) := by
    intro B hB hB2 hBP
    rw [inf_eq_left.mpr hBP, LinkE2.card_of_isPGroup_typeR hΦ hB hB2]
    norm_num
  have hKM : secImg Ω (t * u) (tightCore R) ≠ secImg Ω (t * u) (conjSub c (tightCore R)) :=
    fun e => hMX (e ▸ Vtx.le_orbGrp _)
  have hJM : secImg Ω (t * u) J ≠ secImg Ω (t * u) (conjSub c (tightCore R)) := by
    intro e
    apply hMX
    rw [← e, ← hg₀]
    exact Vtx.conjSub_le_orbGrp _ ⟨g₀, hg₀G⟩
  have hKJ : secImg Ω (t * u) (tightCore R) ≠ secImg Ω (t * u) J :=
    hs.secImg_J_mem_omegaNbr.2.1.symm
  exact false_of_three_secImg_of hs.partIHypG hthree hs.xMem_K hs.xMem_J hKc hKJ hKM hJM hP2
    (hcard hKΦ h2K (le_sup_right.trans le_sup_right))
    (hcard hJΦ h2J (le_sup_left.trans le_sup_right)) (hcard hMΦ hM2 le_sup_left)

private theorem false_of_three_labels_of_three (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hthree : NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R)))
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))
    {m : ℕ} (hm : 5 ≤ m)
    (φ : ↥(pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))) →* AEQ m)
    (hker : φ.ker ≤ Subgroup.center _)
    (hKX : secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) ≤
      secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))
    (hJX : secImg (CoreAssembly.conjClass (tightCore R)) (t * u) J ≤
      secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))
    {L : Subgroup Y} (hL : XMem (CoreAssembly.conjClass (tightCore R)) (t * u) L)
    {γ₁ γ₂ β : Finset (Fin m)} {h₁ : γ₁.card = 4} {h₂ : γ₂.card = 4} {hβ : β.card = 4}
    {b₁ b₂ : Bool}
    (hlK : (((secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R)).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))).subgroupOf
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))).map φ =
      memBar γ₁ h₁ b₁)
    (hlJ : (((secImg (CoreAssembly.conjClass (tightCore R)) (t * u) J).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))).subgroupOf
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))).map φ =
      memBar γ₂ h₂ b₂)
    (hlL : (((secImg (CoreAssembly.conjClass (tightCore R)) (t * u) L).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))).subgroupOf
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))).map φ =
      memBar β hβ true)
    {v : AEQ m} (hvβ : v ∈ memBar β hβ true) (hv2 : v * v ≠ 1)
    (hv₁ : ∀ a ∈ memBar γ₁ h₁ b₁, v * a * v⁻¹ ∈ memBar γ₁ h₁ b₁)
    (hv₂ : ∀ a ∈ memBar γ₂ h₂ b₂, v * a * v⁻¹ ∈ memBar γ₂ h₂ b₂)
    (h12 : memBar γ₁ h₁ b₁ ≤ Subgroup.normalizer (memBar γ₂ h₂ b₂ : Set (AEQ m)))
    (hvK : v ∉ memBar γ₁ h₁ b₁) (hvJ : v ∉ memBar γ₂ h₂ b₂) : False := by
  have h := TightLargeHypR.typeRFam hs.large
  have hΦ := h.secFam (x := t * u)
  have hKΦ := secImg_mem hs.xMem_K
  have hJΦ := secImg_mem hs.xMem_J
  have hLΦ := secImg_mem hL
  have hmem2 : ∀ (γ : Finset (Fin m)) (hγ : γ.card = 4) (c : Bool),
      IsPGroup 2 ↥(memBar γ hγ c) := fun γ hγ c =>
    IsPGroup.of_card (n := 3) (by rw [AE.natCard_memBar hm]; norm_num)
  have hQ₀ : IsPGroup 2 ↥(memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂) :=
    (hmem2 γ₁ h₁ b₁).to_sup_of_normal_right' (hmem2 γ₂ h₂ b₂) h12
  have hvN : Subgroup.zpowers v ≤
      Subgroup.normalizer ((memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂ : Subgroup (AEQ m)) :
        Set (AEQ m)) := by
    rw [Subgroup.zpowers_le]
    have e₁ := mem_normalizer_iff_conjSub_eq.mp (mem_normalizer_of_conj_mem hv₁)
    have e₂ := mem_normalizer_iff_conjSub_eq.mp (mem_normalizer_of_conj_mem hv₂)
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    show (memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂).map (MulAut.conj v).toMonoidHom = _
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) e₁ e₂
  have hv2g : IsPGroup 2 ↥(Subgroup.zpowers v) :=
    (hmem2 β hβ true).to_le (Subgroup.zpowers_le.mpr hvβ)
  have hQ : IsPGroup 2 ↥(Subgroup.zpowers v ⊔ (memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂)) :=
    hv2g.to_sup_of_normal_right' hQ₀ hvN
  have hP2 := ((hQ.comap_of_ker_isPGroup φ (LinkE2.isPGroup_ker hD hker)).map
    (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))).subtype).map
    (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)).subtype
  have hin : ∀ {M : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))},
      M ∈ secFam (CoreAssembly.conjClass (tightCore R)) (t * u) →
      ∀ hMX : M ≤ secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u),
      ∀ {γ : Finset (Fin m)} {hγ : γ.card = 4} {c : Bool},
      ((M.subgroupOf (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R)
        (t * u))).subgroupOf (pSpan (restrictFamily
          (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))).map φ =
        memBar γ hγ c →
      memBar γ hγ c ≤ Subgroup.zpowers v ⊔ (memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂) →
      M ≤ (((Subgroup.zpowers v ⊔ (memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂)).comap φ).map
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))).subtype).map
        (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)).subtype := by
    intro M hM hMX γ hγ c hlab hle x hx
    have hxS : (⟨x, hMX hx⟩ : ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R)
        (t * u))) ∈ pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) :=
      le_pSpan (P := restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
        (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))
        (L := M.subgroupOf (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))
        ⟨M, hM, hMX, rfl⟩ (Subgroup.mem_subgroupOf.mpr hx)
    refine Subgroup.mem_map.mpr ⟨⟨x, hMX hx⟩,
      Subgroup.mem_map.mpr ⟨⟨⟨x, hMX hx⟩, hxS⟩, ?_, rfl⟩, rfl⟩
    rw [Subgroup.mem_comap]
    apply hle
    rw [← hlab]
    exact ⟨⟨⟨x, hMX hx⟩, hxS⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hKP := hin hKΦ hKX hlK (le_sup_left.trans le_sup_right)
  have hJP := hin hJΦ hJX hlJ (le_sup_right.trans le_sup_right)
  have hvβ' := hvβ
  rw [← hlL] at hvβ'
  obtain ⟨y, hy, hyv⟩ := hvβ'
  have hyL : ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) :
      SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) ∈
      secImg (CoreAssembly.conjClass (tightCore R)) (t * u) L :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy)
  have hzp : Subgroup.zpowers ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore R))
      (tightCore R) (t * u))) : SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) ≤
      secImg (CoreAssembly.conjClass (tightCore R)) (t * u) L ⊓
        (((Subgroup.zpowers v ⊔ (memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂)).comap φ).map
          (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
            (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))).subtype).map
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)).subtype := by
    rintro _ ⟨k, rfl⟩
    refine ⟨Subgroup.zpow_mem _ hyL k, Subgroup.mem_map.mpr ⟨(y : ↥(secOrb
      (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) ^ k,
      Subgroup.mem_map.mpr ⟨y ^ k, ?_, rfl⟩, ?_⟩⟩
    · rw [Subgroup.mem_comap, map_zpow, hyv]
      exact Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers v k)
    · simp
  have hy2 : ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) :
      SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) ^ 2 ≠ 1 := by
    intro e
    apply hv2
    have e' : y ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using e
    rw [← hyv, ← map_mul, ← pow_two, e', map_one]
  have hord : 2 < orderOf ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore R))
      (tightCore R) (t * u))) : SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) := by
    have hnd : ¬ orderOf ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore R))
        (tightCore R) (t * u))) : SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) ∣ 2 :=
      fun hd => hy2 (orderOf_dvd_iff_pow_eq_one.mp hd)
    have h0 := orderOf_pos ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore R))
      (tightCore R) (t * u))) : SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))
    have h1 : orderOf ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore R))
        (tightCore R) (t * u))) : SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) ≠ 1 :=
      fun e => hy2 (by rw [orderOf_eq_one_iff.mp e, one_pow])
    have h2 : orderOf ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore R))
        (tightCore R) (t * u))) : SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) ≠ 2 :=
      fun e => hy2 (by rw [← e]; exact pow_orderOf_eq_one _)
    omega
  have hcL : 2 < Nat.card ↥(secImg (CoreAssembly.conjClass (tightCore R)) (t * u) L ⊓
      (((Subgroup.zpowers v ⊔ (memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂)).comap φ).map
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))).subtype).map
        (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)).subtype) := by
    refine lt_of_lt_of_le ?_ (Subgroup.card_le_of_le hzp)
    rw [Nat.card_zpowers]
    exact hord
  have hcard : ∀ {M : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))},
      M ∈ secFam (CoreAssembly.conjClass (tightCore R)) (t * u) →
      M ≤ secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) →
      ∀ {P : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))}, M ≤ P →
        2 < Nat.card ↥(M ⊓ P) := by
    intro M hM hMX P hMP
    rw [inf_eq_left.mpr hMP, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMX).toEquiv,
      hD.card _ ⟨M, hM, hMX, rfl⟩]
    norm_num
  have hKL : secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (t * u) L := by
    intro e
    apply hvK
    rw [← hlK, e, hlL]
    exact hvβ
  have hJL : secImg (CoreAssembly.conjClass (tightCore R)) (t * u) J ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (t * u) L := by
    intro e
    apply hvJ
    rw [← hlJ, e, hlL]
    exact hvβ
  exact false_of_three_secImg_of hs.partIHypG hthree hs.xMem_K hs.xMem_J hL
    hs.secImg_J_mem_omegaNbr.2.1.symm hKL hJL hP2 (hcard hKΦ hKX hKP)
    (hcard hJΦ hJX hJP) hcL

private theorem false_of_meet_labels_of_three (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hthree : NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R)))
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))
    {m : ℕ} (hm : 5 ≤ m)
    (φ : ↥(pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))) →* AEQ m)
    (hker : φ.ker ≤ Subgroup.center _)
    (hKX : secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) ≤
      secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))
    (hJX : secImg (CoreAssembly.conjClass (tightCore R)) (t * u) J ≤
      secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))
    {γ₁ γ₂ β : Finset (Fin m)} {h₁ : γ₁.card = 4} {h₂ : γ₂.card = 4} (hβ : β.card = 4)
    {b₁ b₂ : Bool}
    (hlK : (((secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R)).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))).subgroupOf
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))).map φ =
      memBar γ₁ h₁ b₁)
    (hlJ : (((secImg (CoreAssembly.conjClass (tightCore R)) (t * u) J).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))).subgroupOf
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))).map φ =
      memBar γ₂ h₂ b₂)
    (hc : (γ₁ ∩ β).card = 2) (hc₂ : γ₂ ∩ β = γ₁ ∩ β ∨ γ₂ ∩ β = β \ (γ₁ ∩ β))
    (h12 : memBar γ₁ h₁ b₁ ≤ Subgroup.normalizer (memBar γ₂ h₂ b₂ : Set (AEQ m)))
    (hlab : ∃ L ∈ restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)),
        (L.subgroupOf (pSpan (restrictFamily
          (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))).map φ =
          memBar β hβ true) : False := by
  classical
  obtain ⟨p, q, hpq, hpqe⟩ := Finset.card_eq_two.mp hc
  have hpm : p ∈ γ₁ ∩ β := by rw [hpqe]; simp
  have hqm : q ∈ γ₁ ∩ β := by rw [hpqe]; simp
  have hp : p ∈ β := (Finset.mem_inter.mp hpm).2
  have hq : q ∈ β := (Finset.mem_inter.mp hqm).2
  have hsub : ({p, q} : Finset (Fin m)) ⊆ β := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hq
  have hcard2 : (β \ {p, q}).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hβ, Finset.card_pair hpq]
  have hn : ∀ γ : Finset (Fin m), (γ ∩ β).card = 2 → ¬ β ⊆ γ := fun γ hγ hsub' => by
    rw [Finset.inter_eq_right.mpr hsub', hβ] at hγ
    omega
  have hc₂' : γ₂ ∩ β = {p, q} ∨ γ₂ ∩ β = β \ {p, q} := by
    rcases hc₂ with e | e
    · exact Or.inl (e.trans hpqe)
    · exact Or.inr (by rw [e, hpqe])
  have hn₂ : ¬ β ⊆ γ₂ := by
    refine hn γ₂ ?_
    rcases hc₂' with e | e
    · rw [e, Finset.card_pair hpq]
    · rw [e, hcard2]
  obtain ⟨v, hvβ, hv2, hvout, hvn⟩ := SecIdE2.exists_normalizing_memBar_pair hm hβ hp hq hpq
  obtain ⟨L', hL', hlL'⟩ := hlab
  obtain ⟨L, hL, hLX, rfl⟩ := exists_xMem_of_mem_restrictFamily hL'
  exact false_of_three_labels_of_three hs hthree hD hm φ hker hKX hJX hL hlK hlJ hlL' hvβ hv2
    (hvn γ₁ h₁ (Or.inl hpqe) b₁) (hvn γ₂ h₂ hc₂' b₂) h12 (hvout γ₁ h₁ b₁ (hn γ₁ hc))
    (hvout γ₂ h₂ b₂ hn₂)

theorem std8_c264One_of_wSet_of_three (h4 : Thm4RBelow 3 n)
    (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hthree : NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R)))
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore R)) (tightCore R) J (t * u))
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))
    {V : Subgroup ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))}
    (hW1 : WSet (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) = {V}) :
    C264One (CoreAssembly.conjClass (tightCore R)) t u := by
  have hKX : secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) ≤
      secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) := Vtx.le_orbGrp _
  obtain ⟨g₀, hg₀⟩ := hcj
  have hJX : secImg (CoreAssembly.conjClass (tightCore R)) (t * u) J ≤
      secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) := by
    rw [← hg₀]
    exact Vtx.conjSub_le_orbGrp _ ⟨g₀, by rw [omegaGen_secFam]; exact Subgroup.mem_top _⟩
  have hKΦ := secImg_mem hs.xMem_K
  have hJΦ := secImg_mem hs.xMem_J
  have h2 : ∀ {B : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))},
      B ∈ secFam (CoreAssembly.conjClass (tightCore R)) (t * u) →
      B ≤ secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) →
      IsPGroup 2 ↥B := fun hB hBX =>
    (hD.two _ ⟨_, hB, hBX, rfl⟩).of_equiv (Subgroup.subgroupOfEquivOfLe hBX)
  have hW : V ∈ WSet (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) := by
    rw [hW1]; rfl
  have hV2 : IsPGroup 2 ↥(V.map
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)).subtype) :=
    (Thompson.isPGroup_of_mem_WSet hW).map _
  have hc4 : ∀ {B : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))},
      B ∈ secFam (CoreAssembly.conjClass (tightCore R)) (t * u) →
      B ≤ secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) →
      2 < Nat.card ↥(B ⊓ V.map
        (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)).subtype) := by
    intro B hB hBX
    have h1 := card_inf_of_wSet_eq hD hW1 _ ⟨_, hB, hBX, rfl⟩
    have h2 := card_inf_subgroupOf_le (A := B) V
    omega
  refine c264One_of_orb_of_three h4 hs hthree ⟨g₀, hg₀⟩ (h2 hKΦ hKX) (h2 hJΦ hJX) fun M hM hMX => ?_
  by_contra hne
  rw [not_or] at hne
  obtain ⟨L, hL, rfl⟩ := mem_secFam_iff.mp hM
  exact false_of_three_secImg_of hs.partIHypG hthree hs.xMem_K hs.xMem_J hL
    hs.secImg_J_mem_omegaNbr.2.1.symm (Ne.symm hne.1) (Ne.symm hne.2) hV2 (hc4 hKΦ hKX)
    (hc4 hJΦ hJX) (hc4 hM hMX)

theorem std8_false_of_e64_of_three (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hthree : NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R)))
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore R)) (tightCore R) J (t * u))
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))
    (I : AEIdentOn (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) 7 AE.e64Sets
        AE.e64Sub) : False := by
  classical
  have hKX : secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) ≤
      secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) := Vtx.le_orbGrp _
  have hJX := secImg_J_le_secOrb hcj
  obtain ⟨γ₁, hγ₁, h₁, b₁, hlK⟩ := I.label _ ⟨_, secImg_mem hs.xMem_K, hKX, rfl⟩
  obtain ⟨γ₂, -, h₂, b₂, hlJ⟩ := I.label _ ⟨_, secImg_mem hs.xMem_J, hJX, rfl⟩
  rcases hs.labels_eq_or_disjoint hD (by norm_num) I.φ hKX hJX hlK hlJ with e | hd
  · subst e
    obtain ⟨ℓ, hℓ, rfl⟩ := hγ₁
    obtain ⟨ℓ', hℓ', hc⟩ := fanoLines_exists_meet ℓ hℓ
    have hβm : ℓ'ᶜ ∈ AE.e64Sets := ⟨ℓ', hℓ', rfl⟩
    have hβ := SecIdE2.card_of_mem_e64Sets hβm
    exact false_of_meet_labels_of_three hs hthree hD (by norm_num) I.φ I.ker_le hKX hJX hβ hlK hlJ
      hc (Or.inl rfl) (memBar_le_normalizer_twin h₁ h₂ b₁ b₂) (I.label_surj _ hβm hβ true)
  · exact false_of_disjoint_four (by norm_num) h₂ h₁ hd

theorem std8_false_of_aeIdent_of_three (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hthree : NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R)))
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore R)) (tightCore R) J (t * u))
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))
    {m : ℕ} (hm : 6 ≤ m)
    (I : AEIdent (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) m) : False := by
  classical
  have hKX : secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) ≤
      secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) := Vtx.le_orbGrp _
  have hJX := secImg_J_le_secOrb hcj
  obtain ⟨γ₁, h₁, b₁, hlK⟩ := I.label _ ⟨_, secImg_mem hs.xMem_K, hKX, rfl⟩
  obtain ⟨γ₂, h₂, b₂, hlJ⟩ := I.label _ ⟨_, secImg_mem hs.xMem_J, hJX, rfl⟩
  rcases hs.labels_eq_or_disjoint hD (by omega) I.φ hKX hJX hlK hlJ with e | hd
  · subst e
    have hcard : 2 ≤ (γ₁ᶜ).card := by
      rw [Finset.card_compl, Fintype.card_fin, h₁]
      omega
    obtain ⟨p, q, β, hβ, -, -, hpq, hγβ, -, -, -⟩ :=
      exists_quad (by omega : 2 ≤ γ₁.card) hcard disjoint_compl_right
    exact false_of_meet_labels_of_three hs hthree hD (by omega) I.φ I.ker_le hKX hJX hβ hlK hlJ
      (by rw [hγβ, Finset.card_pair hpq]) (Or.inl rfl) (memBar_le_normalizer_twin h₁ h₂ b₁ b₂)
      (I.label_surj β hβ true)
  · obtain ⟨p, q, β, hβ, -, -, hpq, h1, h2, -, -⟩ :=
      exists_quad (by omega : 2 ≤ γ₁.card) (by omega : 2 ≤ γ₂.card) hd.symm
    exact false_of_meet_labels_of_three hs hthree hD (by omega) I.φ I.ker_le hKX hJX hβ hlK hlJ
      (by rw [h1, Finset.card_pair hpq]) (Or.inr (by rw [h2, h1]))
      (le_normalizer_of_comm (AE.comm_memBar_of_disjoint hd.symm b₁ b₂))
      (I.label_surj β hβ true)

theorem std8_false_of_e29_of_three (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hthree : NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R)))
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore R)) (tightCore R) J (t * u))
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))
    (I : AEIdentOn (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) 8 AE.e29Sets
        AE.e29Sub) : False := by
  classical
  have hKX : secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) ≤
      secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) := Vtx.le_orbGrp _
  have hJX := secImg_J_le_secOrb hcj
  obtain ⟨γ₁, hγ₁, h₁, b₁, hlK⟩ := I.label _ ⟨_, secImg_mem hs.xMem_K, hKX, rfl⟩
  obtain ⟨γ₂, hγ₂, h₂, b₂, hlJ⟩ := I.label _ ⟨_, secImg_mem hs.xMem_J, hJX, rfl⟩
  rcases hs.labels_eq_or_disjoint hD (by norm_num) I.φ hKX hJX hlK hlJ with e | hd
  · subst e
    obtain ⟨β, hβm, hc⟩ := affinePlanes_exists_meet γ₁ hγ₁
    have hβ := SecIdE2.card_of_mem_e29Sets hβm
    exact false_of_meet_labels_of_three hs hthree hD (by norm_num) I.φ I.ker_le hKX hJX hβ hlK hlJ
      hc (Or.inl rfl) (memBar_le_normalizer_twin h₁ h₂ b₁ b₂) (I.label_surj β hβm hβ true)
  · obtain ⟨β, hβm, hc, hc₂⟩ := affinePlanes_exists_meet_compl γ₁ hγ₁ γ₂ hγ₂ hd.symm
    have hβ := SecIdE2.card_of_mem_e29Sets hβm
    exact false_of_meet_labels_of_three hs hthree hD (by norm_num) I.φ I.ker_le hKX hJX hβ hlK hlJ
      hc (Or.inr hc₂) (le_normalizer_of_comm (AE.comm_memBar_of_disjoint hd.symm b₁ b₂))
      (I.label_surj β hβm hβ true)

theorem std8_false_of_ae5_of_sigma (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore R)) (tightCore R) J (t * u))
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))))
    (I : AEIdent (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) 5)
    {σ : MulAut (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))}
    (hσ : SPropSec (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) J σ) :
    False := by
  classical
  revert σ
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set K := tightCore R with hKdef
  intro σ hσ
  have h := TightLargeHypR.typeRFam hs.large
  have hXK : XMem Ω (t * u) K := hs.xMem_K
  have hXJ : XMem Ω (t * u) J := hs.xMem_J
  have hσσx : ∀ x, σ (σ x) = x := fun x =>
    congrArg (fun τ : MulAut (SecQuot Ω (t * u)) => τ x) hσ.sq
  set Xb := secOrb Ω K (t * u) with hXbdef
  have hKXb : secImg Ω (t * u) K ≤ Xb := Vtx.le_orbGrp _
  have hJXb : secImg Ω (t * u) J ≤ Xb := secImg_J_le_secOrb hcj
  have hA : (secImg Ω (t * u) K).subgroupOf Xb ∈ restrictFamily (secFam Ω (t * u)) Xb :=
    ⟨_, secImg_mem hXK, hKXb, rfl⟩
  have hB : (secImg Ω (t * u) J).subgroupOf Xb ∈ restrictFamily (secFam Ω (t * u)) Xb :=
    ⟨_, secImg_mem hXJ, hJXb, rfl⟩
  have hTR : TypeRFam 3 (restrictFamily (secFam Ω (t * u)) Xb) :=
    (h.secFam (x := t * u)).restrict Xb
  have h2K : IsPGroup 2 ↥(secImg Ω (t * u) K) :=
    (hD.two _ hA).of_equiv (Subgroup.subgroupOfEquivOfLe hKXb)
  obtain ⟨QK, hQK, hσQK⟩ := hσ.fixK
  have hQKeq : secImg Ω (t * u) K = QK := hQK.2.2 _ le_rfl h2K hQK.1
  have hσKfix : ∀ k ∈ secImg Ω (t * u) K, σ k = k := fun k hk => hσQK k (hQKeq ▸ hk)
  have hσK : (secImg Ω (t * u) K).map σ.toMonoidHom = secImg Ω (t * u) K := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      show σ k ∈ _
      rw [hσKfix k hk]
      exact hk
    · intro k hk
      exact ⟨k, hk, hσKfix k hk⟩
  have hσX : Xb.map σ.toMonoidHom = Xb := orbGrp_map_eq_of_top omegaGen_secFam σ hσK
  have hσmem : ∀ x ∈ Xb, σ x ∈ Xb := fun x hx => by
    rw [← hσX]
    exact ⟨x, hx, rfl⟩
  let σ' : MulAut ↥Xb :=
    { toFun := fun x => ⟨σ x, hσmem x x.2⟩
      invFun := fun x => ⟨σ x, hσmem x x.2⟩
      left_inv := fun x => Subtype.ext (hσσx x)
      right_inv := fun x => Subtype.ext (hσσx x)
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : SecQuot Ω (t * u)) y) }
  have hσ'σ' : σ' * σ' = 1 := MulEquiv.ext fun x => Subtype.ext (hσσx x)
  have hσA : ∀ k ∈ (secImg Ω (t * u) K).subgroupOf Xb, σ' k = k := fun k hk =>
    Subtype.ext (hσKfix _ (Subgroup.mem_subgroupOf.mp hk))
  have hσB : ∀ k ∈ (secImg Ω (t * u) J).subgroupOf Xb,
      σ' k ∈ (secImg Ω (t * u) J).subgroupOf Xb := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hσ.normJ _ hk
  have hKJ : secImg Ω (t * u) K ≠ secImg Ω (t * u) J := hs.secImg_J_mem_omegaNbr.2.1.symm
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
  obtain ⟨QJ, hQJ, -, hσQJ⟩ := hσ.onJ
  obtain ⟨e⟩ : Nonempty (↥QJ ≃* QuaternionGroup 2) := h.secFam.quat _ (secImg_mem hXJ) QJ hQJ
  have hyJ : ((e.symm (QuaternionGroup.xa 0) : ↥QJ) : SecQuot Ω (t * u)) ∈ secImg Ω (t * u) J :=
    hQJ.1 (e.symm (QuaternionGroup.xa 0)).2
  have hσy : σ ((e.symm (QuaternionGroup.xa 0) : ↥QJ) : SecQuot Ω (t * u)) =
      ((e.symm (QuaternionGroup.xa 0) : ↥QJ) : SecQuot Ω (t * u)) :=
    congrArg Subtype.val (hfix ⟨_, hJXb hyJ⟩ (Subgroup.mem_subgroupOf.mpr hyJ))
  have hyy : e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.xa 0) = 1 :=
    Subtype.ext (hσQJ _ (e.symm (QuaternionGroup.xa 0)).2 hσy)
  have hx : (QuaternionGroup.xa 0 * QuaternionGroup.xa 0 : QuaternionGroup 2) = 1 := by
    simpa using congrArg e hyy
  exact absurd hx (by decide)

theorem std8_c264One_of_E2 (hP : TightBelowRPlus 3 n) (h4 : Thm4RBelow 3 n)
    (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hthree : NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R)))
    {σ : MulAut (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))}
    (hσ : SPropSec (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) J σ)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore R)) (tightCore R) J (t * u))
    (hO2 : SecInO2 (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) t) :
    C264One (CoreAssembly.conjClass (tightCore R)) t u := by
  have hD := hs.thmDHyp_secOrb h4 hO2
  rcases hs.thmDConcl_secOrb hP h4 hO2 with h1 | ⟨V, hW1⟩ | ⟨E, hE8⟩ | hI | ⟨m, hm, hI⟩ | hI
  · exact (hs.false_of_subsingleton_secOrb hcj h1).elim
  · exact std8_c264One_of_wSet_of_three h4 hs hthree hcj hD hW1
  · exact (hs.false_of_e8_secOrb hcj hE8).elim
  · obtain ⟨I⟩ := hI
    exact (std8_false_of_e64_of_three hs hthree hcj hD I).elim
  · obtain ⟨I⟩ := hI
    rcases (by omega : m = 5 ∨ 6 ≤ m) with rfl | hm6
    · exact (std8_false_of_ae5_of_sigma hs hcj hD I hσ).elim
    · exact (std8_false_of_aeIdent_of_three hs hthree hcj hD hm6 I).elim
  · obtain ⟨I⟩ := hI
    exact (std8_false_of_e29_of_three hs hthree hcj hD I).elim

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.Z2W

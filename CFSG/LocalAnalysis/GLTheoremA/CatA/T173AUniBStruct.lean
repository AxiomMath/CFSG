module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open scoped MatrixGroups

private theorem eq_one_of_mulAut_conj_eq_one {Q : Type*} [Group Q]
    (hZ : Subgroup.center Q = ⊥) {σ : Q} (h : MulAut.conj σ = 1) : σ = 1 := by
  have hmem : σ ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := congrArg (fun f : MulAut Q => f g) h
    rw [MulAut.conj_apply, MulAut.one_apply] at hg
    calc g * σ = (σ * g * σ⁻¹) * σ := by rw [hg]
      _ = σ * g := by group
  simpa [hZ] using hmem

theorem uni_B_structure {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} (hcfg : Cfg173 p S B N D K x) {n d : ℕ} {F : Type} [Field F] [Finite F]
    {θ : ↥S ⧸ Subgroup.center ↥S ≃* UniPSU n d F} (hM : UniMarking p S B n d F θ)
    (hd : ¬ p ∣ d) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) :
    B = Subgroup.zpowers x ⊔ B ⊓ S ∧ IsElemAbelian p (modCentreImage S B) := by
  classical
  have hp : p.Prime := hcfg.prime
  haveI hPerf : Group.IsPerfect ↥S := ⟨hcfg.qs.1⟩
  have hBN : B ≤ Subgroup.normalizer (S : Set Ω) := hM.2.2.2.2.2.1
  have hArith : UniArith p n d F :=
    ⟨hp, hM.2.2.2.2.1, hd, hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1⟩
  let β : ↥B →* MulAut (UniPSU n d F) := CFSG.StandardType.ggBeta S θ hBN
  let Φ : ↥B →* MulAut (↥S ⧸ Subgroup.center ↥S) :=
    (MulAut.congr θ.symm).toMonoidHom.comp β
  have hBpow : ∀ b : ↥B, (b : ↥B) ^ p = 1 :=
    fun b => Subtype.ext (by simpa using hcfg.elem.2 (b : Ω) b.2)
  have hBcomm' : ∀ b₁ b₂ : ↥B, b₁ * b₂ = b₂ * b₁ :=
    fun b₁ b₂ => Subtype.ext (by simpa using IsElemAbelian.comm hcfg.elem b₁.2 b₂.2)
  have hinner : ∀ b : ↥B, ∃ r : UniPSU n d F, β b = MulAut.conj r := by
    intro b
    have hmem : β b ∈ LargeEvenMatConjImage (UniMk n d F)
        (LargeEvenGUSet (Fin d) F (2 ^ n)) := by
      have h := CFSG.StandardType.ggBeta_mem (L := S) (θ := θ) (B := B) hBN
        (I := LargeEvenMatConjImage (UniMk n d F) (LargeEvenGUSet (Fin d) F (2 ^ n)))
        hM.2.2.2.2.2.2 b
      simpa [β] using h
    have hpβ : (β b) ^ p = 1 := by
      rw [← map_pow, hBpow b, map_one]
    obtain ⟨r, hr⟩ := uni_conjImage_pPower_inner hArith hmem hpβ
    exact ⟨r, MulEquiv.ext (fun y => by rw [hr y, MulAut.conj_apply])⟩
  choose r hr using hinner
  let Sig : Subgroup (↥S ⧸ Subgroup.center ↥S) :=
    Subgroup.comap (MulAut.conj : (↥S ⧸ Subgroup.center ↥S) →*
      MulAut (↥S ⧸ Subgroup.center ↥S)) Φ.range
  have hZQ : Subgroup.center (↥S ⧸ Subgroup.center ↥S) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot ↥S
  have hconj_congr : ∀ b : ↥B,
      MulAut.congr θ.symm (MulAut.conj (r b)) = MulAut.conj (θ.symm (r b)) := by
    intro b
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply, map_mul]
  have hΦb : ∀ b : ↥B, Φ b = MulAut.conj (θ.symm (r b)) := by
    intro b
    change MulAut.congr θ.symm (β b) = MulAut.conj (θ.symm (r b))
    rw [hr b, hconj_congr b]
  have hSigPow : ∀ σ ∈ Sig, σ ^ p = 1 := by
    intro σ hσ
    have hσr : MulAut.conj σ ∈ Φ.range := Subgroup.mem_comap.mp hσ
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hσr
    apply eq_one_of_mulAut_conj_eq_one hZQ
    rw [show MulAut.conj (σ ^ p) = (MulAut.conj σ) ^ p from map_pow _ _ _, ← hb,
      ← map_pow Φ, hBpow b, map_one]
  have hSigComm' : ∀ σ τ : ↥Sig, σ * τ = τ * σ := by
    intro σ τ
    obtain ⟨b₁, hb₁⟩ := MonoidHom.mem_range.mp (Subgroup.mem_comap.mp σ.2)
    obtain ⟨b₂, hb₂⟩ := MonoidHom.mem_range.mp (Subgroup.mem_comap.mp τ.2)
    apply Subtype.ext
    have hΦcomm : Φ b₁ * Φ b₂ = Φ b₂ * Φ b₁ := by
      rw [← map_mul, ← map_mul, hBcomm' b₁ b₂]
    have hconj : MulAut.conj ((σ : ↥S ⧸ Subgroup.center ↥S) * τ *
        (σ : ↥S ⧸ Subgroup.center ↥S)⁻¹ * (τ : ↥S ⧸ Subgroup.center ↥S)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hb₁.symm, hb₂.symm, hΦcomm]
      group
    have hprod : (σ : ↥S ⧸ Subgroup.center ↥S) * τ *
        (σ : ↥S ⧸ Subgroup.center ↥S)⁻¹ * (τ : ↥S ⧸ Subgroup.center ↥S)⁻¹ = 1 :=
      eq_one_of_mulAut_conj_eq_one hZQ hconj
    have h1 : (σ : ↥S ⧸ Subgroup.center ↥S) * τ *
        ((τ : ↥S ⧸ Subgroup.center ↥S) * (σ : ↥S ⧸ Subgroup.center ↥S))⁻¹ = 1 := by
      rw [mul_inv_rev]
      simpa only [mul_assoc] using hprod
    exact mul_inv_eq_one.mp h1
  have hSigEa : IsElemAbelian p Sig :=
    ⟨IsMulCommutative.of_comm hSigComm', hSigPow⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Slift, hSlift_ea, hSlift_map, -⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.exists_elemAbelian_lift (Subgroup.center ↥S) hZ
      (Eb := Sig) hSigEa
  have hσmem : ∀ b : ↥B, θ.symm (r b) ∈ Sig := by
    intro b
    rw [Subgroup.mem_comap, ← hΦb b]
    exact MonoidHom.mem_range.mpr ⟨b, rfl⟩
  have hsb : ∀ b : ↥B, ∃ s : ↥S, s ∈ Slift ∧
      QuotientGroup.mk' (Subgroup.center ↥S) s = θ.symm (r b) := by
    intro b
    have h : θ.symm (r b) ∈ Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥S)) Slift := by
      rw [hSlift_map]
      exact hσmem b
    obtain ⟨s, hs, hsmk⟩ := Subgroup.mem_map.mp h
    exact ⟨s, hs, hsmk⟩
  choose s hsS hs_mk using hsb
  have hΦapply : ∀ (b : ↥B) (l : ↥S),
      Φ b (QuotientGroup.mk l) =
        QuotientGroup.mk ((S.normalizerMonoidHom ⟨(b : Ω), hBN b.2⟩) l) := by
    intro b l
    change (MulAut.congr θ.symm ((CFSG.StandardType.ggBeta S θ hBN) b))
      (QuotientGroup.mk l) = _
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_symm]
    change θ.symm ((CFSG.StandardType.ggLAut S θ ⟨(b : Ω), hBN b.2⟩)
      (θ (QuotientGroup.mk l))) = _
    rw [CFSG.StandardType.ggLAut_apply, MulEquiv.symm_apply_apply]
  have hrel : ∀ (b : ↥B) (l : ↥S),
      (QuotientGroup.mk' (Subgroup.center ↥S)) ((S.normalizerMonoidHom ⟨(b : Ω), hBN b.2⟩) l) =
        (QuotientGroup.mk' (Subgroup.center ↥S)) ((s b) * l * (s b)⁻¹) := by
    intro b l
    have h1 := hΦapply b l
    rw [hΦb b, MulAut.conj_apply, ← hs_mk b] at h1
    simp only [QuotientGroup.mk'_apply] at h1
    have h3 : (QuotientGroup.mk' (Subgroup.center ↥S)) ((s b) * l * (s b)⁻¹) =
        (QuotientGroup.mk' (Subgroup.center ↥S)) (s b) *
          (QuotientGroup.mk' (Subgroup.center ↥S)) l *
          ((QuotientGroup.mk' (Subgroup.center ↥S)) (s b))⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    simp only [QuotientGroup.mk'_apply] at h3
    exact h1.symm.trans h3.symm
  have hcC : ∀ b : ↥B, (b : Ω) * (s b : Ω)⁻¹ ∈ Subgroup.centralizer (S : Set Ω) := by
    intro b
    have hbN : (b : Ω) ∈ Subgroup.normalizer (S : Set Ω) := hBN b.2
    have hsN : (s b : Ω) ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.le_normalizer (s b).2
    have hcN : (b : Ω) * (s b : Ω)⁻¹ ∈ Subgroup.normalizer (S : Set Ω) :=
      Subgroup.mul_mem _ hbN (Subgroup.inv_mem _ hsN)
    have hgg : CFSG.StandardType.ggLAut S θ ⟨(b : Ω) * (s b : Ω)⁻¹, hcN⟩ = 1 := by
      ext y
      obtain ⟨q, rfl⟩ := θ.surjective y
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥S) q
      rw [QuotientGroup.mk'_apply, CFSG.StandardType.ggLAut_apply, MulAut.one_apply]
      congr 1
      have hceq : (S.normalizerMonoidHom ⟨(b : Ω) * (s b : Ω)⁻¹, hcN⟩) l =
          (S.normalizerMonoidHom ⟨(b : Ω), hBN b.2⟩) ((s b)⁻¹ * l * (s b)) := by
        apply Subtype.ext
        rw [CFSG.StandardType.normalizerMonoidHom_coe, CFSG.StandardType.normalizerMonoidHom_coe]
        show ((b : Ω) * (s b : Ω)⁻¹) * (l : Ω) * ((b : Ω) * (s b : Ω)⁻¹)⁻¹ =
          (b : Ω) * ((s b : Ω)⁻¹ * (l : Ω) * (s b : Ω)) * (b : Ω)⁻¹
        group
      rw [hceq]
      have hgoal := hrel b ((s b)⁻¹ * l * (s b))
      simp only [QuotientGroup.mk'_apply] at hgoal
      rw [hgoal]
      have hthis : (s b) * ((s b)⁻¹ * l * (s b)) * (s b)⁻¹ = l := by group
      rw [hthis]
    simpa using CFSG.StandardType.mem_centralizer_of_ggLAut_eq_one S θ hcfg.qs.1 hgg
  have hsB : ∀ b : ↥B, (s b : Ω) ∈ B := by
    intro b
    obtain ⟨T, hTS, hT2, hBT, hTne'⟩ := hcfg.hb
    have hTne : T ≠ ⊥ := by
      intro hbot
      apply hTne'
      rw [hbot, Subgroup.commutator_bot_left]
    have hcomm_all : ∀ a : ↥B, (a : Ω) * (s b : Ω) = (s b : Ω) * (a : Ω) := by
      intro a
      have hca := hcC a
      have h2 : (s a : ↥S) * (s b : ↥S) = (s b : ↥S) * (s a : ↥S) :=
        IsElemAbelian.comm hSlift_ea (hsS a) (hsS b)
      have h2Ω : (s a : Ω) * (s b : Ω) = (s b : Ω) * (s a : Ω) := by
        simpa using congrArg Subtype.val h2
      have h1 : ((a : Ω) * (s a : Ω)⁻¹) * (s b : Ω) =
          (s b : Ω) * ((a : Ω) * (s a : Ω)⁻¹) :=
        ((Subgroup.mem_centralizer_iff.mp hca) (s b : Ω) (s b).2).symm
      have ha_eq : (a : Ω) = ((a : Ω) * (s a : Ω)⁻¹) * (s a : Ω) := by group
      have h1' : Commute ((a : Ω) * (s a : Ω)⁻¹) (s b : Ω) := h1
      have h2' : Commute ((s a : Ω)) (s b : Ω) := h2Ω
      have hc := Commute.mul_left h1' h2'
      rwa [← ha_eq] at hc
    have hs_pow : (s b : Ω) ^ p = 1 := by
      have h := hSlift_ea.2 (s b) (hsS b)
      simpa using congrArg Subtype.val h
    have hcommB : ∀ a ∈ B, ∀ f ∈ Subgroup.zpowers (s b : Ω), a * f = f * a := by
      intro a ha f hf
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
      exact Commute.zpow_right (hcomm_all ⟨a, ha⟩) m
    have hEea : IsElemAbelian p (B ⊔ Subgroup.zpowers (s b : Ω)) :=
      IsElemAbelian.sup_of_commute hcfg.elem (isElemAbelian_zpowers hs_pow) hcommB
    have hsN : (s b : Ω) ∈ Subgroup.normalizer (T : Set Ω) := by
      have hcT : (b : Ω) * (s b : Ω)⁻¹ ∈ Subgroup.centralizer (T : Set Ω) :=
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTS)) (hcC b)
      have h1 : ((b : Ω) * (s b : Ω)⁻¹)⁻¹ ∈ Subgroup.normalizer (T : Set Ω) :=
        Subgroup.centralizer_le_normalizer (T : Set Ω) (Subgroup.inv_mem _ hcT)
      have h2 : ((b : Ω) * (s b : Ω)⁻¹)⁻¹ * (b : Ω) ∈ Subgroup.normalizer (T : Set Ω) :=
        Subgroup.mul_mem _ h1 (hBT b.2)
      convert h2 using 1
      group
    have hEN : B ⊔ Subgroup.zpowers (s b : Ω) ≤ Subgroup.normalizer (T : Set Ω) :=
      sup_le hBT (Subgroup.zpowers_le.mpr hsN)
    have hEq := GLAIsBmax.eq_of_le hp hcfg.bmax le_sup_left hEea hTne hT2 hEN
    have : (s b : Ω) ∈ B ⊔ Subgroup.zpowers (s b : Ω) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rwa [hEq] at this
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · intro b hb
    let bb : ↥B := ⟨b, hb⟩
    have hcB : b * (s bb : Ω)⁻¹ ∈ B :=
      Subgroup.mul_mem _ hb (Subgroup.inv_mem _ (hsB bb))
    have hcX : b * (s bb : Ω)⁻¹ ∈ Subgroup.zpowers x :=
      (hcfg.cent _ hcB).1 (hcC bb)
    have hb_eq : b = (b * (s bb : Ω)⁻¹) * (s bb : Ω) := by group
    rw [hb_eq]
    exact Subgroup.mul_mem_sup hcX ⟨hsB bb, (s bb).2⟩
  · exact sup_le (Subgroup.zpowers_le.mpr hcfg.mem) inf_le_left
  · simpa [modCentreImage] using
      (IsElemAbelian.map (IsElemAbelian.subgroupOf hcfg.elem S)
        (QuotientGroup.mk' (Subgroup.center ↥S)))

end CFSG.LocalAnalysis.GLTheoremA.T173A

end

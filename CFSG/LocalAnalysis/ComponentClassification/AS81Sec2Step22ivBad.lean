module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem exists_conj_eq_mul {t u : G} (ht : t ∈ E) (htA : t ∉ E ⊓ A) (hu : u ∈ E ⊓ A) :
    ∃ p ∈ sec2P E, p⁻¹ * t * p = t * u := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have htr := exists_mem_sec2P_rightConjugate_eq h11 hE16 hF hL hodd
  have htu : t * u ∈ E := E.mul_mem ht hu.1
  have htuA : t * u ∉ E ⊓ A := fun h => htA (by simpa using (E ⊓ A).mul_mem h ((E ⊓ A).inv_mem hu))
  obtain ⟨Q, hQ, htQ⟩ := hD.cover t ht htA
  obtain ⟨Q', hQ', htuQ'⟩ := hD.cover _ htu htuA
  obtain ⟨p₁, hp₁, hp₁Q⟩ := htr Q hQ
  obtain ⟨p₂, hp₂, hp₂Q⟩ := htr Q' hQ'
  set p := p₁⁻¹ * p₂
  have hp : p ∈ sec2P E := (sec2P E).mul_mem ((sec2P E).inv_mem hp₁) hp₂
  have hQp : rightConjugate Q p = Q' := by
    rw [← hp₁Q, rightConjugate_mul, show p₁ * p = p₂ by simp [p], hp₂Q]
  refine ⟨p, hp, ?_⟩
  have h1 : p⁻¹ * t * p ∈ Q' := by
    rw [← hQp, mem_rightConjugate_iff]
    simpa [mul_assoc] using htQ
  have hk : t⁻¹ * p⁻¹ * t * p ∈ E ⊓ A := hD.commutator_mem hT hCE hF.elemE ht hp
  have h2 : (t * u)⁻¹ * (p⁻¹ * t * p) ∈ Q' ⊓ (E ⊓ A) := by
    refine ⟨Q'.mul_mem (Q'.inv_mem htuQ') h1, ?_⟩
    have := (E ⊓ A).mul_mem ((E ⊓ A).inv_mem hu) hk
    simpa [mul_assoc] using this
  rw [hD.inf_H Q' hQ', mem_bot, inv_mul_eq_one] at h2
  exact h2.symm

omit h11 hE16 in
theorem conjClosure_inf_inf_eq (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E)) :
    conjClosure (F ⊓ A) (sec2P E) ⊓ (E ⊓ A) = sec2Z A E F := by
  obtain ⟨y, hyA, hyE, hyF, hyEF, hyfix⟩ := exists_torus_sec2 hF hL hodd
  obtain ⟨hyZ, -, -⟩ := mem_normalizer_sec2S_of_mem hF hyA hyE hyF
  set T := conjClosure (F ⊓ A) (sec2P E)
  have hZ := hF.sec2Z_eq
  have hZT : sec2Z A E F ≤ T := hZ ▸ fun z hz => le_conjClosure_self _ _ ⟨hz.1.2, hz.2⟩
  have hZU : sec2Z A E F ≤ E ⊓ A := hZ ▸ fun z hz => ⟨hz.1.1, hz.2⟩
  have hyP := Sec2.normalizer_le_normalizer_sec2P E hyE
  have hyT : y ∈ normalizer (T : Set G) :=
    mem_normalizer_conjClosure (inf_normalizer_le_normalizer_inf ⟨hyF, le_normalizer hyA⟩) hyP
  have hyU : y ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hyE, le_normalizer hyA⟩
  have hidx : (sec2Z A E F).relIndex (E ⊓ A) = 4 := by
    have h := relIndex_mul_card (H := sec2Z A E F) (K := E ⊓ A)
    rw [inf_eq_left.mpr hZU, hF.card_sec2Z hodd, card_inf_left hF hodd] at h
    omega
  rcases eq_or_eq_of_index_four hidx (le_inf hZT hZU) inf_le_right hyZ
      (inf_normalizer_le_normalizer_inf ⟨hyT, hyU⟩)
      (fun a ha h => mem_sec2Z_of_conj_mul_inv_mem hF hL hodd hyA hyZ
        (fun w hw => hyfix w (hZ ▸ hw)) ha h) with h | h
  · exact h
  · exact absurd (h ▸ inf_le_left) hT

theorem conjClosure_inf_eq (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E)) :
    conjClosure (F ⊓ A) (sec2P E) ⊓ E = sec2Z A E F := by
  obtain ⟨hD, T₀, hT₀⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have htr := exists_mem_sec2P_rightConjugate_eq h11 hE16 hF hL hodd
  have hTU := conjClosure_inf_inf_eq hF hL hodd hT
  set T := conjClosure (F ⊓ A) (sec2P E)
  have hZ := hF.sec2Z_eq
  have hZT : sec2Z A E F ≤ T := hZ ▸ fun z hz => le_conjClosure_self _ _ ⟨hz.1.2, hz.2⟩
  have hZE : sec2Z A E F ≤ E := hZ ▸ fun z hz => hz.1.1
  refine le_antisymm (fun t ht => ?_) (le_inf hZT hZE)
  by_contra htZ
  have htA : t ∉ E ⊓ A := fun h => htZ (hTU ▸ ⟨ht.1, h⟩)
  obtain ⟨Q, hQ, htQ⟩ := hD.cover t ht.2 htA
  obtain ⟨p₀, hp₀, hp₀Q⟩ := htr Q hQ
  have hPT := le_normalizer_conjClosure (F ⊓ A) (sec2P E)
  have hpt : ∀ Q' : ↥(pointsIn R E), ∃ p ∈ sec2P E, rightConjugate Q p = (Q' : Subgroup G) :=
    fun Q' => by
      obtain ⟨p₁, hp₁, hp₁Q⟩ := htr Q' Q'.2
      refine ⟨p₀⁻¹ * p₁, (sec2P E).mul_mem ((sec2P E).inv_mem hp₀) hp₁, ?_⟩
      rw [← hp₀Q, rightConjugate_mul, mul_inv_cancel_left, hp₁Q]
  choose p hp hpQ using hpt
  have hk : ∀ Q', t⁻¹ * (p Q')⁻¹ * t * p Q' ∈ sec2Z A E F := fun Q' => by
    rw [← hTU]
    refine ⟨?_, hD.commutator_mem hT₀ hCE hF.elemE ht.2 (hp Q')⟩
    have h1 : (p Q')⁻¹ * t * p Q' ∈ T := by
      have := (mem_normalizer_iff.mp (inv_mem (hPT (hp Q'))) t).mp ht.1
      simpa [mul_assoc] using this
    simpa [mul_assoc] using T.mul_mem (T.inv_mem ht.1) h1
  let ι : ↥(pointsIn R E) → ↥(sec2Z A E F) := fun Q' => ⟨_, hk Q'⟩
  have hι : Function.Injective ι := fun Q₁ Q₂ h => by
    have h' : t⁻¹ * (p Q₁)⁻¹ * t * p Q₁ = t⁻¹ * (p Q₂)⁻¹ * t * p Q₂ := congrArg Subtype.val h
    have he : (p Q₁)⁻¹ * t * p Q₁ = (p Q₂)⁻¹ * t * p Q₂ := by
      have := congrArg (fun x => t * x) h'
      simpa [mul_assoc] using this
    have hm : ∀ Q' : ↥(pointsIn R E), (p Q')⁻¹ * t * p Q' ∈ (Q' : Subgroup G) := fun Q' => by
      rw [← hpQ Q', mem_rightConjugate_iff]
      simpa [mul_assoc] using htQ
    have hne : (p Q₁)⁻¹ * t * p Q₁ ≠ 1 := fun h1 => htZ (by
      have : t = 1 := by
        have := congrArg (fun x => p Q₁ * x * (p Q₁)⁻¹) h1
        simpa [mul_assoc] using this
      rw [this]
      exact (sec2Z A E F).one_mem)
    by_contra hQne
    have hmem : (p Q₁)⁻¹ * t * p Q₁ ∈ (Q₁ : Subgroup G) ⊓ Q₂ := ⟨hm Q₁, he ▸ hm Q₂⟩
    rw [hD.disj _ Q₁.2 _ Q₂.2 (fun h => hQne (Subtype.ext h)), mem_bot] at hmem
    exact hne hmem
  have hle := Nat.card_le_card_of_injective ι hι
  rw [hT₀.card_points, hF.card_sec2Z hodd] at hle
  omega

theorem card_conjClosure_inf_sec2P (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E)) :
    Nat.card (conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E : Subgroup G) = 16 := by
  obtain ⟨hEC, hCidx, -⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  have hEP : E ≤ sec2P E := Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemE) le_normalizer
    le_rfl
  have hprod := card_sup_mul_card_inf_of_le_normalizer_left
    (X := conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E) (N := E)
    (inf_le_right.trans (Sec2.sec2P_le E))
  rw [sup_inf_sec2P_eq h11 hE16 hF hL hodd, inf_assoc, inf_eq_right.mpr hEP,
    conjClosure_inf_eq h11 hE16 hF hL hodd hT, hF.card_sec2Z hodd, hF.cardE] at hprod
  have hC : Nat.card (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) = 4 * 64 := by
    have h := relIndex_mul_card (H := E)
      (K := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F))
    rw [inf_eq_left.mpr hEC, hCidx, hF.cardE] at h
    exact h.symm
  rw [hC] at hprod
  omega

omit h11 hE16 in
theorem commutator_mem_conjClosure_inf_sec2P {f p : G} (hf : f ∈ F ⊓ A) (hp : p ∈ sec2P E) :
    f⁻¹ * p⁻¹ * f * p ∈ conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E := by
  refine ⟨?_, ?_⟩
  · have h1 : f⁻¹ ∈ conjClosure (F ⊓ A) (sec2P E) :=
      le_conjClosure_self _ _ ((F ⊓ A).inv_mem hf)
    have h2 : p⁻¹ * f * p ∈ conjClosure (F ⊓ A) (sec2P E) :=
      rightConjugate_le_conjClosure _ hp (by
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using hf)
    simpa [mul_assoc] using (conjClosure (F ⊓ A) (sec2P E)).mul_mem h1 h2
  · have hfN := Sec2.normalizer_le_normalizer_sec2P E (hF.F_le_normalizer hL hodd hf.1)
    have := (sec2P E).mul_mem ((mem_normalizer_iff.mp (inv_mem hfN) _).mp
      ((sec2P E).inv_mem hp)) hp
    simpa [mul_assoc] using this

theorem conj_eq_inv_of_mem_conjClosure_inf_sec2P (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E))
    {f : G} (hf : f ∈ F ⊓ A) (hfE : f ∉ E) {w : G}
    (hw : w ∈ conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E) : f * w * f⁻¹ = w⁻¹ := by
  have hSP := sec2S_inf_sec2P h11 hE16 hF hL hodd
  have hTS := conjClosure_le_sec2S h11 hE16 hF hL hodd
  have hPU := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hFc : ∀ x ∈ F, ∀ x' ∈ F, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hwC : w ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) :=
    hSP ▸ ⟨hTS hw.1, hw.2⟩
  obtain ⟨p, hp, hpw⟩ := exists_commutator_mul_mem h11 hE16 hF hL hodd hf.1 hfE hwC
  set d := f⁻¹ * p⁻¹ * f * p
  have hd := commutator_mem_conjClosure_inf_sec2P hF hL hodd hf hp
  have hz : d⁻¹ * w ∈ sec2Z A E F := by
    rw [← conjClosure_inf_eq h11 hE16 hF hL hodd hT]
    exact ⟨(conjClosure (F ⊓ A) (sec2P E)).mul_mem
      ((conjClosure (F ⊓ A) (sec2P E)).inv_mem hd.1) hw.1, hpw⟩
  have hZ := hF.sec2Z_eq
  set z := d⁻¹ * w
  have hwdz : w = d * z := by simp [z]
  have hf2 : f * f = 1 := by rw [← sq]; exact hF.elemF.2 f hf.1
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_left hf2
  have hzF : z ∈ F := (hZ ▸ hz).1.2
  have hzE : z ∈ E := (hZ ▸ hz).1.1
  have hz2 : z * z = 1 := by rw [← sq]; exact hF.elemE.2 z hzE
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hz2
  have hfz : f * z = z * f := hFc f hf.1 z hzF
  have hdz : d * z = z * d :=
    (mem_centralizer_iff.mp (hPU hd.2) z ⟨hzE, (hZ ▸ hz).2⟩).symm
  have hfd : f * d * f⁻¹ = d⁻¹ := by
    have hp2 : (p⁻¹ * f * p) * (p⁻¹ * f * p) = 1 := by
      calc (p⁻¹ * f * p) * (p⁻¹ * f * p) = p⁻¹ * (f * f) * p := by group
        _ = 1 := by rw [hf2]; group
    have h1 : f * d = p⁻¹ * f * p := by simp only [d]; rw [← hfinv]; group
    calc f * d * f⁻¹ = (f * d) * (f * d) * d⁻¹ * f⁻¹ * f⁻¹ := by group
      _ = d⁻¹ * (f * f)⁻¹ := by rw [h1, hp2]; group
      _ = d⁻¹ := by rw [hf2, inv_one, mul_one]
  rw [hwdz]
  calc f * (d * z) * f⁻¹ = (f * d * f⁻¹) * (f * z * f⁻¹) := by group
    _ = d⁻¹ * z := by rw [hfd, hfz, mul_inv_cancel_right]
    _ = (d * z)⁻¹ := by rw [hdz, mul_inv_rev z d, hzinv]

theorem isElemAbelian_conjClosure_inf_sec2P (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E)) :
    IsElemAbelian 2 (conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E) := by
  obtain ⟨y, hyA, hyE, hyF, hyEF, hyfix⟩ := exists_torus_sec2 hF hL hodd
  have hZ := hF.sec2Z_eq
  have hFc : ∀ x ∈ F, ∀ x' ∈ F, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  obtain ⟨f, hf, hfE⟩ : ∃ f ∈ F ⊓ A, f ∉ E := by
    by_contra h
    push Not at h
    have hle : F ⊓ A ≤ sec2Z A E F := fun x hx => hZ ▸ ⟨⟨h x hx, hx.1⟩, hx.2⟩
    have := card_le_of_le hle
    rw [card_inf_left hF.symm hodd, hF.card_sec2Z hodd] at this
    omega
  have hyFA : y ∈ normalizer ((F ⊓ A : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hyF, le_normalizer hyA⟩
  set f' := y * f * y⁻¹
  have hf' : f' ∈ F ⊓ A := (mem_normalizer_iff.mp hyFA f).mp hf
  have hf'E : f' ∉ E := fun h => hfE (by
    have := (mem_normalizer_iff.mp (inv_mem hyE) _).mp h
    simpa [f', mul_assoc] using this)
  have hff' : f * f' ∈ F ⊓ A := (F ⊓ A).mul_mem hf hf'
  have hff'E : f * f' ∉ E := by
    intro h
    have hZ' : sec2Z A F E = F ⊓ E ⊓ A := hF.symm.sec2Z_eq
    have hmem : y * f * y⁻¹ * f⁻¹ ∈ sec2Z A F E := by
      rw [hZ']
      have hf2 : f * f = 1 := by rw [← sq]; exact hF.elemF.2 f hf.1
      have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_left hf2
      refine ⟨⟨F.mul_mem hf'.1 (F.inv_mem hf.1), ?_⟩, A.mul_mem hf'.2 (A.inv_mem hf.2)⟩
      rw [hfinv, ← hFc f hf.1 f' hf'.1]
      exact h
    have hyZ' : y ∈ normalizer (sec2Z A F E : Set G) := by
      rw [sec2Z_comm]
      exact (mem_normalizer_sec2S_of_mem hF hyA hyE hyF).1
    have := mem_sec2Z_of_conj_mul_inv_mem hF.symm hL hodd hyA hyZ'
      (fun w hw h => hyfix w (by rw [sec2Z_comm, hZ] at hw; exact hw) h) hf hmem
    rw [sec2Z_comm, hZ] at this
    exact hfE this.1.1
  have hsq : ∀ w ∈ conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E, w * w = 1 := fun w hw => by
    have h1 := conj_eq_inv_of_mem_conjClosure_inf_sec2P h11 hE16 hF hL hodd hT hf hfE hw
    have h2 := conj_eq_inv_of_mem_conjClosure_inf_sec2P h11 hE16 hF hL hodd hT hf' hf'E hw
    have h3 := conj_eq_inv_of_mem_conjClosure_inf_sec2P h11 hE16 hF hL hodd hT hff' hff'E hw
    have h4 : (f * f') * w * (f * f')⁻¹ = w := by
      calc (f * f') * w * (f * f')⁻¹ = f * (f' * w * f'⁻¹) * f⁻¹ := by group
        _ = (f * w * f⁻¹)⁻¹ := by rw [h2]; group
        _ = w := by rw [h1, inv_inv]
    rw [h3] at h4
    have h5 : w * w⁻¹ = 1 := mul_inv_cancel w
    rwa [h4] at h5
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun w hw => by rw [sq]; exact hsq w hw⟩
  have ha := hsq a a.2
  have hb := hsq b b.2
  have hab := hsq _ (mul_mem a.2 b.2)
  show (a : G) * b = b * a
  calc (a : G) * b = ((a : G) * b)⁻¹ := (inv_eq_of_mul_eq_one_left hab).symm
    _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev (a : G) (b : G)
    _ = b * a := by rw [inv_eq_of_mul_eq_one_left hb, inv_eq_of_mul_eq_one_left ha]

end Frame

end CFSG.ComponentClassification.AS81

module

public import CFSG.ClassicalInvolution.Asc77.AscT7DMu
public import CFSG.ClassicalInvolution.Asc77.AscT7DFrame
public import CFSG.ClassicalInvolution.Asc77.AscT7DPerm

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7D

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_stab_split (c : Thompson.Ctx p f Ω W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) {ρ ρ' ρ₃ : Thompson.Rep Ω W}
    (hab : imgQ ρ ≠ imgQ ρ') (hcomm : imgQ ρ * imgQ ρ' = imgQ ρ' * imgQ ρ)
    (hac : imgQ ρ * imgQ ρ₃ ≠ imgQ ρ₃ * imgQ ρ) {ε : G} (hε : ε ∈ W)
    (h₁ : ρ.r * ε * ρ.r⁻¹ = ε) (h₂ : ρ'.r * ε * ρ'.r⁻¹ = ε) (h₃ : ρ₃.r * ε * ρ₃.r⁻¹ = ε)
    {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G)) :
    ∃ m ∈ Subgroup.normalizer (W : Set G), m * ε * m⁻¹ = ε ∧
      Thompson.piG W (m⁻¹ * n) * ρ.img * (Thompson.piG W (m⁻¹ * n))⁻¹ = ρ.img ∧
      Thompson.piG W (m⁻¹ * n) * ρ'.img * (Thompson.piG W (m⁻¹ * n))⁻¹ = ρ'.img ∧
      Thompson.piG W (m⁻¹ * n) * ρ₃.img * (Thompson.piG W (m⁻¹ * n))⁻¹ = ρ₃.img := by
  have ha := imgQ_mem ρ
  have ha' := imgQ_mem ρ'
  have ha₃ := imgQ_mem ρ₃
  have hmem : ∀ σ : Thompson.Rep Ω W, σ.r * ε * σ.r⁻¹ = ε →
      imgQ σ ∈ Thompson.muStab Ω W ε := fun σ h =>
    (c.mem_muStab_iff hε σ.hR σ.hr (q := imgQ σ) rfl).mpr h
  have hΔ : ∀ x ∈ Thompson.muDelta Ω W, x ∈ Thompson.muStab Ω W ε := fun x hx => by
    have hx' := S4.mem_closure_frame he ha ha' ha₃ hab hcomm hac hx
    refine (Subgroup.closure_le (Thompson.muStab Ω W ε)).mpr ?_ hx'
    rintro y (rfl | rfl | rfl)
    · exact hmem ρ h₁
    · exact hmem ρ' h₂
    · exact hmem ρ₃ h₃
  have hall : ∀ y : ↥(muGroup Ω W), y ∈ Thompson.muStab Ω W ε := fun y => by
    have : y ∈ Subgroup.closure (Thompson.muDelta Ω W) := by
      rw [Thompson.closure_muDelta_eq_top]
      trivial
    exact (Subgroup.closure_le (Thompson.muStab Ω W ε)).mpr hΔ this
  have hb₁ := Thompson.conjQ_mem_muDelta c.hΩ hn ha
  have hb₂ := Thompson.conjQ_mem_muDelta c.hΩ hn ha'
  have hb₃ := Thompson.conjQ_mem_muDelta c.hΩ hn ha₃
  obtain ⟨y, hy1, hy2, hy3⟩ := S4.exists_frame_conj he ha ha' ha₃ hb₁ hb₂ hb₃ hab hcomm hac
    (fun h => hab ((Thompson.conjQ c.hΩ hn).injective h))
    (by rw [← map_mul, ← map_mul, hcomm])
    (fun h => hac ((Thompson.conjQ c.hΩ hn).injective (by rw [map_mul, map_mul]; exact h)))
  obtain ⟨m, hm, hym, hmε⟩ := hall y
  have key : ∀ σ : Thompson.Rep Ω W,
      y * imgQ σ * y⁻¹ = Thompson.conjQ c.hΩ hn (imgQ σ) →
      Thompson.piG W (m⁻¹ * n) * σ.img * (Thompson.piG W (m⁻¹ * n))⁻¹ = σ.img := by
    intro σ hσ
    have h1 : (y : NQuot (W ⊔ OCW W)) * σ.img * (y : NQuot (W ⊔ OCW W))⁻¹ =
        Thompson.piG W n * σ.img * (Thompson.piG W n)⁻¹ := by
      have := congrArg Subtype.val hσ
      rw [Thompson.conjQ_apply] at this
      exact this
    rw [Thompson.piG_mul (Subgroup.inv_mem _ hm) hn, Thompson.piG_inv hm, ← hym]
    calc (y : NQuot (W ⊔ OCW W))⁻¹ * Thompson.piG W n * σ.img *
          ((y : NQuot (W ⊔ OCW W))⁻¹ * Thompson.piG W n)⁻¹
        = (y : NQuot (W ⊔ OCW W))⁻¹ * (Thompson.piG W n * σ.img * (Thompson.piG W n)⁻¹) *
            (y : NQuot (W ⊔ OCW W)) := by group
      _ = (y : NQuot (W ⊔ OCW W))⁻¹ * ((y : NQuot (W ⊔ OCW W)) * σ.img *
            (y : NQuot (W ⊔ OCW W))⁻¹) * (y : NQuot (W ⊔ OCW W)) := by rw [h1]
      _ = σ.img := by group
  exact ⟨m, hm, hmε, key ρ hy1, key ρ' hy2, key ρ₃ hy3⟩

theorem c24_2_of_frame [IsSimpleGroup G] {K K' : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u b b' : G} (hs : Hyp23Setting p f Ω K K' z)
    (hyp : Hyp24Data Ω K K' W S R R' z u) (hb : b ∈ K ⊓ W) (hb' : b' ∈ K' ⊓ W)
    (ob : orderOf b = 4) (ob' : orderOf b' = 4) (hu : u = b * b') :
    ∃ g ∈ Subgroup.normalizer (W : Set G), g⁻¹ * z * g = u := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hW : W ∈ WSet Ω := hyp.hW
  have hWab := Thompson.commutes_of_mem_WSet hp hq hΩ hW
  have c : Thompson.Ctx p f Ω W := ctx_of_stand hst hW
  obtain ⟨e, he⟩ := exists_swap_equiv hs hW hyp.hS4
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have hRD : R ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hyp.hWS hyp.hR.1 hyp.hR.2.2
  have hR'D : R' ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hyp.hWS hyp.hR'.1 hyp.hR'.2.2
  obtain ⟨ρ, hρK, -⟩ := exists_rep hp hq hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, -⟩ := exists_rep hp hq hΩ hW hK' hR'syl hR'D
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
  have hne : ρ.K ≠ ρ'.K := by
    rw [hρK, hρ'K]
    exact hs.hne.symm
  have hρnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
    have hperp : K' ∈ KPerp Ω K := by rw [hs.perp]; exact Or.inr rfl
    rw [hρK, hρ'K]
    rcases hperp with e | e
    · exact absurd e hs.hne
    · exact e
  have hcomm : ρ.img * ρ'.img = ρ'.img * ρ.img := c.comm_of_omega ρ ρ' hρnbr
  have hρnbr' : ρ.K ∈ omegaNbr Ω ρ'.K := c.omega_of_comm ρ' ρ hne.symm hcomm.symm
  have hab : imgQ ρ ≠ imgQ ρ' := fun h => hne (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h))
  have hcommQ : imgQ ρ * imgQ ρ' = imgQ ρ' * imgQ ρ := Subtype.ext hcomm
  obtain ⟨c₃, hc₃Δ, hac, hbc⟩ := S4.exists_third he (imgQ_mem ρ) (imgQ_mem ρ') hab hcommQ
  obtain ⟨ρ₃, hρ₃⟩ := Thompson.exists_rep_of_mem_muDelta hc₃Δ
  have hc₃ : imgQ ρ₃ = c₃ := Subtype.ext hρ₃
  have hac' : imgQ ρ * imgQ ρ₃ ≠ imgQ ρ₃ * imgQ ρ := by rw [hc₃]; exact hac
  have hbc' : imgQ ρ' * imgQ ρ₃ ≠ imgQ ρ₃ * imgQ ρ' := by rw [hc₃]; exact hbc
  have hne₁ : ρ.K ≠ ρ₃.K := fun h => hac' (by
    have h1 : imgQ ρ = imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ ρ₃ h)
    rw [← h1])
  have hne₂ : ρ'.K ≠ ρ₃.K := fun h => hbc' (by
    have h1 : imgQ ρ' = imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ' ρ₃ h)
    rw [← h1])
  have hn₁ : ρ₃.K ∉ omegaNbr Ω ρ.K := fun h => hac' (Subtype.ext (c.comm_of_omega ρ ρ₃ h))
  have hn₂ : ρ₃.K ∉ omegaNbr Ω ρ'.K := fun h => hbc' (Subtype.ext (c.comm_of_omega ρ' ρ₃ h))
  have hn₁' : ρ.K ∉ omegaNbr Ω ρ₃.K := fun h =>
    hac' (Subtype.ext (c.comm_of_omega ρ₃ ρ h).symm)
  have hn₂' : ρ'.K ∉ omegaNbr Ω ρ₃.K := fun h =>
    hbc' (Subtype.ext (c.comm_of_omega ρ₃ ρ' h).symm)
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution hp hq ρ₃.hK
  have hjW : j ∈ W :=
    (Thompson.uniqueInvolution_mem_W hp hq hΩ hW ρ₃.hK ρ₃.hR ρ₃.hRK hj).2
  have hbρ : b ∈ ρ.K ⊓ W := by rw [hρK]; exact hb
  have hb'ρ : b' ∈ ρ'.K ⊓ W := by rw [hρ'K]; exact hb'
  obtain ⟨u₁, hu₁, hr₃, hr₁, hr₂, hr₃'⟩ := frame_fixed c ρ ρ' ρ₃ hρnbr hρnbr' hne₁ hne₂ hn₁ hn₂
    hn₁' hn₂' hzρ hzρ' hj hbρ hb'ρ ob ob'
  have hu₁W : u₁ ∈ W := by
    rcases hu₁ with rfl | rfl
    · exact W.mul_mem hb.2 hb'.2
    · exact W.mul_mem (W.inv_mem hb.2) hb'.2
  have hεW : u₁ * j ∈ W := W.mul_mem hu₁W hjW
  have hsz : ρ₃.r * z * ρ₃.r⁻¹ ≠ z := by
    rw [c.conj_involution ρ₃ ρ hne₁.symm hn₁' hj hzρ]
    intro h
    exact hj.ne_one (mul_right_cancel (h.trans (one_mul z).symm))
  have hF : FrameEps W K K' ρ₃.r j (u₁ * j) := by
    rcases hu₁ with rfl | rfl
    · exact ⟨b, b', hb, hb', ob, ob', hr₃, rfl⟩
    · exact ⟨b⁻¹, b', ⟨K.inv_mem hb.1, W.inv_mem hb.2⟩, hb', by rw [orderOf_inv]; exact ob, ob',
        hr₃, rfl⟩
  have hεinv : ∀ n ∈ Subgroup.normalizer (W : Set G), n * (u₁ * j) * n⁻¹ = u₁ * j := by
    intro n hn
    obtain ⟨m, hm, hmε, k₁, k₂, k₃⟩ := exists_stab_split c he hab hcommQ hac' hεW hr₁ hr₂ hr₃' hn
    have hn' : m⁻¹ * n ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hn
    obtain ⟨hKn, -⟩ := conj_stable c hn' ρ k₁
    obtain ⟨hK'n, -⟩ := conj_stable c hn' ρ' k₂
    obtain ⟨hJn, hact⟩ := conj_stable c hn' ρ₃ k₃
    have hKn' : conjSub (m⁻¹ * n) K = K := by rw [← hρK]; exact hKn
    have hK'n' : conjSub (m⁻¹ * n) K' = K' := by rw [← hρ'K]; exact hK'n
    have hjn : (m⁻¹ * n) * j * (m⁻¹ * n)⁻¹ = j := by
      have := hj.conj (m⁻¹ * n)
      rw [hJn] at this
      exact (hj.eq this).symm
    have hF' := FrameEps.conj hn' hF
    rw [hKn', hK'n', hjn] at hF'
    have huniq := FrameEps.unique hz hz' hWab hsz (fun w hw => (hact w hw).symm) hF hF'
    calc n * (u₁ * j) * n⁻¹
        = m * ((m⁻¹ * n) * (u₁ * j) * (m⁻¹ * n)⁻¹) * m⁻¹ := by group
      _ = m * (u₁ * j) * m⁻¹ := by rw [← huniq]
      _ = u₁ * j := hmε
  have hε1 : u₁ * j = 1 := by
    have hmemC : u₁ * j ∈ centerIn (Subgroup.normalizer (W : Set G)) := by
      refine ⟨⟨u₁ * j, Subgroup.le_normalizer hεW⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := hεinv g g.2
      show (g : G) * (u₁ * j) = (u₁ * j) * g
      calc (g : G) * (u₁ * j) = ((g : G) * (u₁ * j) * (g : G)⁻¹) * g := by group
        _ = (u₁ * j) * g := by rw [h1]
    have hmem : u₁ * j ∈ W ⊓ centerIn (Subgroup.normalizer (W : Set G)) := ⟨hεW, hmemC⟩
    rw [hyp.hZ] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hu₁j : u₁ = j := by
    rw [eq_inv_of_mul_eq_one_left hε1]
    exact inv_eq_of_mul_eq_one_left hj.sq
  obtain ⟨y, hy⟩ := S4.exists_conj_of_mem he (imgQ_mem ρ) (imgQ_mem ρ₃)
  obtain ⟨m, hm, hym⟩ := exists_normalizer_of_mem_muGroup y
  have himg : Thompson.piG W m * ρ.img * (Thompson.piG W m)⁻¹ = ρ₃.img := by
    rw [← hym]
    exact congrArg Subtype.val hy
  have hKm : conjSub m ρ.K = ρ₃.K :=
    c.K_eq_of_img_eq (conjRep c.hΩ hm ρ) ρ₃ (by rw [conjRep_img, himg])
  have hzm : m * z * m⁻¹ = j := by
    have := hzρ.conj m
    rw [hKm] at this
    exact (hj.eq this).symm
  have hbinv : b⁻¹ = z * b := by
    have hbb : b * b = z := T7A.sq_eq_of_orderOf_four hz hb.1 ob
    exact (eq_inv_of_mul_eq_one_left (by rw [mul_assoc, hbb, hz.sq])).symm
  rcases hu₁ with hu₁ | hu₁
  · refine ⟨m⁻¹, Subgroup.inv_mem _ hm, ?_⟩
    rw [inv_inv, hzm, hu, ← hu₁, hu₁j]
  · refine ⟨(ρ.r * m)⁻¹, Subgroup.inv_mem _ (Subgroup.mul_mem _ ρ.r_mem_normalizer hm), ?_⟩
    have e2 : ρ.r * j * ρ.r⁻¹ = z * j := c.conj_involution ρ ρ₃ hne₁ hn₁ hzρ hj
    have hu2 : u = z * j := by
      rw [hu, ← hu₁j, hu₁, hbinv, ← mul_assoc, ← mul_assoc, hz.sq, one_mul]
    calc (ρ.r * m)⁻¹⁻¹ * z * (ρ.r * m)⁻¹ = ρ.r * (m * z * m⁻¹) * ρ.r⁻¹ := by group
      _ = ρ.r * j * ρ.r⁻¹ := by rw [hzm]
      _ = z * j := e2
      _ = u := hu2.symm

end T7D

end CFSG.ClassicalInvolution.Asc77

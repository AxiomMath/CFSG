module

public import CFSG.ClassicalInvolution.Asc77.AscT7EInv

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7C2

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_g0 [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
    {z u : G} (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp24Data Ω K K' W S R R' z u) :
    ∃ g₀ ∈ Subgroup.normalizer (W : Set G), g₀⁻¹ * z * g₀ = u := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hWab := Thompson.commutes_of_mem_WSet hp hq hΩ hd.hW
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hd.hR.1 hd.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hd.hR'.1 hd.hR'.2.1
  obtain ⟨b, hbKW, ob⟩ := T7C.exists_orderOf_four_mem_inf hp hq hΩ hd.hW hd.hWS hK hRsyl
    hd.hR.2.2 hz
  obtain ⟨b', hb'KW, ob'⟩ := T7C.exists_orderOf_four_mem_inf hp hq hΩ hd.hW hd.hWS hK' hR'syl
    hd.hR'.2.2 hz'
  have hbR : b ∈ R := by
    have : K ⊓ (S : Subgroup G) = R :=
      hRsyl.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hd.hR.2.1 hd.hR.2.2)
    rw [← this]
    exact ⟨hbKW.1, hd.hWS hbKW.2⟩
  have hb'R' : b' ∈ R' := by
    have : K' ⊓ (S : Subgroup G) = R' :=
      hR'syl.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hd.hR'.2.1 hd.hR'.2.2)
    rw [← this]
    exact ⟨hb'KW.1, hd.hWS hb'KW.2⟩
  obtain ⟨huK, huW, hu2, hu1, huz⟩ := hd.hu
  rcases T7E.involution_cases hs hRsyl hR'syl hd.hR.2.2 hd.hR'.2.2 hbR hb'R' ob ob' huK
    (hd.hWS huW) hu2 hu1 huz (hWab u huW b hbKW.2) (hWab u huW b' hb'KW.2) with h | h
  · exact T7D.c24_2_of_frame hs hd hbKW hb'KW ob ob' h
  · have hbb : b * b = z := T7A.sq_eq_of_orderOf_four hz hbKW.1 ob
    have hbinv : b⁻¹ = z * b :=
      (eq_inv_of_mul_eq_one_left (by rw [mul_assoc, hbb, hz.sq])).symm
    refine T7D.c24_2_of_frame hs hd (b := b⁻¹) ⟨K.inv_mem hbKW.1, W.inv_mem hbKW.2⟩ hb'KW
      (by rw [orderOf_inv]; exact ob) ob' ?_
    rw [h, hbinv, mul_assoc]

theorem exists_comm_swap_perm :
    ∀ a ∈ S4.swaps4, ∃ b ∈ S4.swaps4, a ≠ b ∧ a * b = b * a := by decide

theorem exists_comm_of_mem {Q : Type*} [Group Q] {Δ : Set Q} {e : Q ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Δ ↔ (e x).IsSwap) {a : Q} (ha : a ∈ Δ) :
    ∃ b ∈ Δ, a ≠ b ∧ a * b = b * a := by
  obtain ⟨τ, hτ, h1, h2⟩ := exists_comm_swap_perm (e a) (S4.mem_swaps4_of_mem he ha)
  refine ⟨e.symm τ, S4.symm_mem_of_mem_swaps4 he hτ, fun h => h1 ?_, ?_⟩
  · have := congrArg e h
    simpa using this
  · apply e.injective
    rw [map_mul, map_mul]
    simpa using h2

theorem exists_chain_conj [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u g : G} (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (hg : g⁻¹ * z * g = u) :
    ∃ h : G, conjSub h K = conjSub g⁻¹ K ∧ conjSub h (conjSub g⁻¹ K) = K' := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hW : W ∈ WSet Ω := hd.hW
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  obtain ⟨e, he⟩ := T7D.exists_swap_equiv hs hW hd.hS4
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hd.hR.1 hd.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hd.hR'.1 hd.hR'.2.1
  have hRD : R ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hd.hWS hd.hR.1 hd.hR.2.2
  have hR'D : R' ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hd.hWS hd.hR'.1 hd.hR'.2.2
  obtain ⟨ρ, hρK, -⟩ := T7D.exists_rep hp hq hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, -⟩ := T7D.exists_rep hp hq hΩ hW hK' hR'syl hR'D
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
  have hab : T7D.imgQ ρ ≠ T7D.imgQ ρ' := fun h =>
    hne (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h))
  have hcommQ : T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ := Subtype.ext hcomm
  obtain ⟨g₀, hg₀, hg₀u⟩ := exists_g0 hs hd
  have hn : g₀⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hg₀
  have hu : IsUniqueInvolution (conjSub g⁻¹ K) u := by
    have := hz.conj g⁻¹
    rwa [inv_inv, hg] at this
  have hJ' : conjSub (g₀ * g⁻¹) K ∈ twinSet Ω K := by
    refine ⟨hΩ.conjInvariant _ K hK, z, hz, ?_⟩
    have h1 := hz.conj (g₀ * g⁻¹)
    have h2 : (g₀ * g⁻¹) * z * (g₀ * g⁻¹)⁻¹ = z := by
      calc (g₀ * g⁻¹) * z * (g₀ * g⁻¹)⁻¹ = g₀ * (g⁻¹ * z * g) * g₀⁻¹ := by group
        _ = g₀ * u * g₀⁻¹ := by rw [hg]
        _ = z := by rw [← hg₀u]; group
    rwa [h2] at h1
  have hKg : conjSub g⁻¹ K = conjSub g₀⁻¹ (conjSub (g₀ * g⁻¹) K) := by
    rw [← conjSub_mul, inv_mul_cancel_left]
  rw [hs.twinSet_eq] at hJ'
  obtain ⟨ρ₃, hρ₃K⟩ : ∃ ρ₃ : Thompson.Rep Ω W, ρ₃.K = conjSub g⁻¹ K := by
    rcases hJ' with h | h
    · exact ⟨T7D.conjRep hΩ hn ρ, by rw [hKg, h, ← hρK]; rfl⟩
    · exact ⟨T7D.conjRep hΩ hn ρ', by rw [hKg, h, ← hρ'K]; rfl⟩
  have hKgK : conjSub g⁻¹ K ≠ K := fun h => hd.hu.2.2.2.2 (by
    rw [h] at hu
    exact (hz.eq hu).symm)
  have hKgK' : conjSub g⁻¹ K ≠ K' := fun h => hd.hu.2.2.2.2 (by
    rw [h] at hu
    exact (hz'.eq hu).symm)
  have hne₁ : ρ.K ≠ ρ₃.K := by
    rw [hρK, hρ₃K]
    exact hKgK.symm
  have hne₂ : ρ'.K ≠ ρ₃.K := by
    rw [hρ'K, hρ₃K]
    exact hKgK'.symm
  have hn₁ : ρ₃.K ∉ omegaNbr Ω ρ.K := fun h => by
    have h1 : ρ₃.K ∈ KPerp Ω K := by rw [← hρK]; exact Or.inr h
    rw [hs.perp, hρ₃K] at h1
    rcases h1 with h2 | h2
    · exact hKgK h2
    · exact hKgK' h2
  have hn₂ : ρ₃.K ∉ omegaNbr Ω ρ'.K := fun h => by
    have h1 : ρ₃.K ∈ KPerp Ω K' := by rw [← hρ'K]; exact Or.inr h
    rw [hs.perp_of_twin hs.hK', hρ₃K] at h1
    rcases h1 with h2 | h2
    · exact hKgK h2
    · exact hKgK' h2
  have hac : T7D.imgQ ρ * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ := fun h =>
    hn₁ (c.omega_of_comm ρ ρ₃ hne₁ (congrArg Subtype.val h))
  have hbc : T7D.imgQ ρ' * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ' := fun h =>
    hn₂ (c.omega_of_comm ρ' ρ₃ hne₂ (congrArg Subtype.val h))
  obtain ⟨b₂, hb₂Δ, hb₂ne, hb₂comm⟩ := exists_comm_of_mem he (T7D.imgQ_mem ρ₃)
  obtain ⟨y, hy1, hy2, hy3⟩ := S4.exists_frame_conj he (T7D.imgQ_mem ρ) (T7D.imgQ_mem ρ')
    (T7D.imgQ_mem ρ₃) (T7D.imgQ_mem ρ₃) hb₂Δ (T7D.imgQ_mem ρ') hab hcommQ hac hb₂ne hb₂comm
    (fun h => hbc h.symm)
  obtain ⟨m, hm, hym⟩ := T7D.exists_normalizer_of_mem_muGroup y
  have himg₁ : (T7D.conjRep hΩ hm ρ).img = ρ₃.img := by
    rw [T7D.conjRep_img, ← hym]
    have := congrArg Subtype.val hy1
    simpa [T7D.imgQ] using this
  have himg₂ : (T7D.conjRep hΩ hm ρ₃).img = ρ'.img := by
    rw [T7D.conjRep_img, ← hym]
    have := congrArg Subtype.val hy3
    simpa [T7D.imgQ] using this
  refine ⟨m, ?_, ?_⟩
  · have := c.K_eq_of_img_eq _ _ himg₁
    rw [← hρ₃K, ← this, ← hρK]
    rfl
  · have := c.K_eq_of_img_eq _ _ himg₂
    rw [← hρ₃K, ← hρ'K, ← this]
    rfl

end T7C2

end CFSG.ClassicalInvolution.Asc77

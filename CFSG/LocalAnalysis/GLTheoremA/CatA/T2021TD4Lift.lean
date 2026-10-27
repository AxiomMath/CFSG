module

import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I2015

theorem t2021TD4Lift_map_fixSub {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (β : MulAut H) (βQ : MulAut (ppQuot p H))
    (hβQ : ∀ l : H, βQ (QuotientGroup.mk l) = QuotientGroup.mk (β l)) (hβp : β ^ p = 1) :
    (fixSub β).map (QuotientGroup.mk' (GLAPPrimeCore p H)) = fixSub βQ := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : β x = x := hx
    show βQ (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [hβQ, hx']
  · intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hq' : βQ (QuotientGroup.mk x) = QuotientGroup.mk x := hq
    have h1 : (QuotientGroup.mk (β x) : ppQuot p H) = QuotientGroup.mk x :=
      (hβQ x).symm.trans hq'
    have hx : β x * x⁻¹ ∈ GLAPPrimeCore p H := by
      have h2 := QuotientGroup.eq_iff_div_mem.1 h1
      rwa [div_eq_mul_inv] at h2
    have hN : ∀ n ∈ GLAPPrimeCore p H, β n ∈ GLAPPrimeCore p H := by
      intro n hn
      have hmem : β n ∈ (CFSG.pPrimeCore p H).map β.toMonoidHom := ⟨n, hn, rfl⟩
      rwa [CFSG.pPrimeCore_map_iso p β] at hmem
    have hN3 : ¬ p ∣ Nat.card (GLAPPrimeCore p H) :=
      (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
    obtain ⟨y, hyx, hy⟩ :=
      CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.fixed_lift β hβp
        (GLAPPrimeCore p H) inferInstance hN hN3 x hx
    refine ⟨y, hy, ?_⟩
    show (QuotientGroup.mk y : ppQuot p H) = QuotientGroup.mk x
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    exact hyx

theorem t2021TD4Lift_layer_mem {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (φ : MulAut H) {X : Subgroup H} (hX : ∀ x ∈ X, φ x ∈ X) {t : H} (ht : t ∈ GLAPLayer p X) :
    φ t ∈ GLAPLayer p X := by
  have hXmap : X.map φ.toMonoidHom = X :=
    Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨x, hx, rfl⟩; exact hX x hx)
      (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).ge
  have hker : Nat.Coprime p (Nat.card ↥(X ⊓ φ.toMonoidHom.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff φ.toMonoidHom).2 φ.injective, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  unfold GLAPLayer at ht ⊢
  have hle : sSup {L | GLAPComponent p X L} ≤
      (sSup {L | GLAPComponent p X L}).comap φ.toMonoidHom := by
    refine sSup_le fun J hJ => ?_
    have hJ' : GLAPComponent p X J := hJ
    rw [← Subgroup.map_le_iff_le_comap]
    have hc := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp φ.toMonoidHom hker hJ'
    rw [hXmap] at hc
    exact le_sSup hc
  exact hle ht

theorem t2021TD4Lift_exists_sylow {H : Type} [Group H] [Finite H] {𝔅 : Type} [Group 𝔅]
    (ψ : 𝔅 →* MulAut H) {r q : ℕ} [Fact r.Prime] [Fact q.Prime] (h𝔅 : IsPGroup r 𝔅)
    {W : Subgroup H} (hWinv : ∀ g : 𝔅, ∀ w ∈ W, ψ g w ∈ W) (hW : ¬ r ∣ Nat.card W) :
    ∃ P : Sylow q ↥W, ∀ g : 𝔅, ∀ x ∈ (P : Subgroup ↥W),
      ψ g (x : H) ∈ (P : Subgroup ↥W).map W.subtype := by
  letI : MulDistribMulAction 𝔅 ↥W :=
    { smul := fun g w => ⟨ψ g w, hWinv g w w.2⟩
      one_smul := fun w => Subtype.ext (by show ψ 1 (w : H) = w; rw [map_one]; rfl)
      mul_smul := fun g h w => Subtype.ext (by
        show ψ (g * h) (w : H) = ψ g (ψ h w)
        rw [map_mul]
        rfl)
      smul_mul := fun g w w' => Subtype.ext (by
        show ψ g ((w : H) * w') = ψ g w * ψ g w'
        exact map_mul _ _ _)
      smul_one := fun g => Subtype.ext (by
        show ψ g (1 : H) = 1
        exact map_one _) }
  have hcard : ¬ r ∣ Nat.card (Sylow q ↥W) := by
    obtain ⟨P⟩ : Nonempty (Sylow q ↥W) := inferInstance
    exact fun h => hW (h.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)))
  obtain ⟨P, hP⟩ := h𝔅.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q ↥W) hcard
  refine ⟨P, fun g x hx => ?_⟩
  have hmem : g • x ∈ ((g • P : Sylow q ↥W) : Subgroup ↥W) := by
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    exact ⟨x, hx, rfl⟩
  rw [hP g] at hmem
  exact ⟨g • x, hmem, rfl⟩

theorem t2021TD4_lift {H : Type} [Group H] [Finite H] {𝔅 : Type} [Group 𝔅] [Finite 𝔅]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ψ : 𝔅 →* MulAut H) (ψQ : 𝔅 → MulAut (ppQuot p H))
    (hψQ : ∀ (g : 𝔅) (l : H), ψQ g (QuotientGroup.mk l) = QuotientGroup.mk (ψ g l))
    (b : 𝔅) (hexp : ∀ g : 𝔅, g ^ p = 1) (hcomm : ∀ g h : 𝔅, g * h = h * g)
    {K U : Subgroup (ppQuot p H)} (hK : GLAPComponent p (fixSub (ψQ b)) K)
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hKZ : Odd (Nat.card ↥(Subgroup.center ↥K)))
    (hK3 : p ∣ Nat.card ↥K) (hUK : U ≤ K) (hU2 : IsPGroup 2 U)
    (hU1 : U ≠ ⊥) (hUinv : ∀ g : 𝔅, ∀ u ∈ U, ψQ g u ∈ U) :
    ∃ T' : Subgroup H, T' ≤ GLAPLayer p (fixSub (ψ b)) ∧ IsPGroup 2 T' ∧
      (∀ g : 𝔅, ∀ t ∈ T', ψ g t ∈ T') ∧
        ¬ T' ≤ GLAPPrimeCoreOf p (GLAPLayer p (fixSub (ψ b))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  set π : H →* ppQuot p H := QuotientGroup.mk' (GLAPPrimeCore p H) with hπ
  set X : Subgroup H := fixSub (ψ b) with hX
  set E : Subgroup H := GLAPLayer p X with hE
  have hπker : π.ker = GLAPPrimeCore p H := QuotientGroup.ker_mk' _
  have hN3 : ¬ p ∣ Nat.card (GLAPPrimeCore p H) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hXmap : X.map π = fixSub (ψQ b) :=
    t2021TD4Lift_map_fixSub hp (ψ b) (ψQ b) (hψQ b) (by rw [← map_pow, hexp, map_one])
  have hker : Nat.Coprime p (Nat.card ↥(X ⊓ π.ker)) := by
    rw [hπker]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card
  obtain ⟨J, hJ, hJK⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_glaPComponent_map_eq
    hp π hker (show GLAPComponent p (X.map π) K by rw [hXmap]; exact hK)
  have hJE : J ≤ E := by
    show J ≤ sSup {L | GLAPComponent p X L}
    exact le_sSup hJ
  have hKE : K ≤ E.map π := by
    rw [← hJK]
    exact Subgroup.map_mono hJE
  have hEinv : ∀ g : 𝔅, ∀ t ∈ E, ψ g t ∈ E := by
    intro g t ht
    refine t2021TD4Lift_layer_mem (X := X) hp (ψ g) (fun x hx => ?_) ht
    have hx' : ψ b x = x := hx
    show ψ b (ψ g x) = ψ g x
    rw [← MulAut.mul_apply, ← map_mul, hcomm b g, map_mul, MulAut.mul_apply, hx']
  set W : Subgroup H := E ⊓ U.comap π with hW
  have hWinv : ∀ g : 𝔅, ∀ w ∈ W, ψ g w ∈ W := by
    intro g w hw
    refine Subgroup.mem_inf.2 ⟨hEinv g w (Subgroup.mem_inf.1 hw).1, ?_⟩
    have hwU : π w ∈ U := (Subgroup.mem_inf.1 hw).2
    have hπψ : π (ψ g w) = ψQ g (π w) := (hψQ g w).symm
    show π (ψ g w) ∈ U
    rw [hπψ]
    exact hUinv g _ hwU
  have hWmap : W.map π = U := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact (Subgroup.mem_inf.1 hw).2
    · intro u hu
      obtain ⟨e, he, rfl⟩ := hKE (hUK hu)
      exact ⟨e, Subgroup.mem_inf.2 ⟨he, hu⟩, rfl⟩
  have hW3 : ¬ p ∣ Nat.card ↥W := by
    have hfr : (π.comp W.subtype).range = U := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hWmap]
    have h1 : Nat.card ↥W =
        Nat.card (π.comp W.subtype).range * Nat.card (π.comp W.subtype).ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (π.comp W.subtype)).toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hkdvd : Nat.card (π.comp W.subtype).ker ∣ Nat.card (GLAPPrimeCore p H) := by
      have hle : (π.comp W.subtype).ker.map W.subtype ≤ GLAPPrimeCore p H := by
        rintro _ ⟨k, hk, rfl⟩
        have hk' : W.subtype k ∈ π.ker := MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hk)
        rwa [hπker] at hk'
      have h2 := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective W.subtype_injective] at h2
    rw [h1, hfr, Nat.Prime.dvd_mul hp]
    rintro (h | h)
    · obtain ⟨n, hn⟩ := hU2.exists_card_eq
      rw [hn] at h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact hN3 (h.trans hkdvd)
  obtain ⟨P, hP⟩ := t2021TD4Lift_exists_sylow ψ (r := p) (q := 2)
    (fun g => ⟨1, by rw [pow_one]; exact hexp g⟩) hWinv hW3
  have hfU : ∀ w : ↥W, π (w : H) ∈ U := fun w => (Subgroup.mem_inf.1 w.2).2
  set fU : ↥W →* ↥U := (π.comp W.subtype).codRestrict U hfU with hfUdef
  have hfUs : Function.Surjective fU := by
    intro u
    obtain ⟨w, hw, hwu⟩ : (u : ppQuot p H) ∈ W.map π := hWmap.symm ▸ u.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwu⟩
  have htop : IsPGroup 2 (⊤ : Subgroup ↥U) := hU2.of_equiv Subgroup.topEquiv.symm
  have hSU : (P : Subgroup ↥W).map fU = ⊤ := ((P.mapSurjective hfUs).3 htop le_top).symm
  have hT'U : ((P : Subgroup ↥W).map W.subtype).map π = U := by
    have h : ((P : Subgroup ↥W).map W.subtype).map π =
        ((P : Subgroup ↥W).map fU).map U.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h, hSU, Subgroup.map_top, Subgroup.range_subtype]
  refine ⟨(P : Subgroup ↥W).map W.subtype, (Subgroup.map_subtype_le _).trans inf_le_left,
    P.isPGroup'.map W.subtype, ?_, ?_⟩
  · rintro g _ ⟨x, hx, rfl⟩
    exact hP g x hx
  intro hle
  set M : Subgroup H := GLAPPrimeCoreOf p E with hM
  have hMdef : M = (GLAPPrimeCore p ↥E).map E.subtype := rfl
  have hM3 : ¬ p ∣ Nat.card ↥M := by
    rw [hMdef, Subgroup.card_map_of_injective E.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hMn : ∀ e ∈ E, ∀ m ∈ M, e * m * e⁻¹ ∈ M := by
    intro e he m hm
    rw [hMdef] at hm ⊢
    obtain ⟨m', hm', rfl⟩ := hm
    exact ⟨⟨e, he⟩ * m' * ⟨e, he⟩⁻¹,
      (inferInstance : (GLAPPrimeCore p ↥E).Normal).conj_mem m' hm' ⟨e, he⟩, rfl⟩
  have hUM : U ≤ M.map π := by
    rw [← hT'U]
    exact Subgroup.map_mono hle
  have hVn : ((M.map π).subgroupOf K).Normal := by
    refine ⟨fun v hv k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    obtain ⟨m, hm, hmv⟩ := hv
    obtain ⟨e, he, hek⟩ := hKE k.2
    refine ⟨e * m * e⁻¹, hMn e he m hm, ?_⟩
    rw [map_mul, map_mul, map_inv, hmv, hek]
    rfl
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hKq
    ((M.map π).subgroupOf K) with hc | ht
  · have hUc : U.subgroupOf K ≤ Subgroup.center ↥K := fun u hu =>
      hc (Subgroup.mem_subgroupOf.2 (hUM (Subgroup.mem_subgroupOf.1 hu)))
    have hdvd : Nat.card ↥U ∣ Nat.card ↥(Subgroup.center ↥K) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv]
      exact Subgroup.card_dvd_of_le hUc
    have hodd : Odd (Nat.card ↥U) := hKZ.of_dvd_nat hdvd
    obtain ⟨n, hn⟩ := hU2.exists_card_eq
    rw [hn] at hodd
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact hU1 (Subgroup.card_eq_one.1 (by rw [hn, pow_zero]))
    · exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hpos.ne'⟩)
  · have hKM : K ≤ M.map π := Subgroup.subgroupOf_eq_top.1 ht
    exact hM3 (hK3.trans ((Subgroup.card_dvd_of_le hKM).trans (Subgroup.card_map_dvd M π)))

end CFSG.LocalAnalysis.GLTheoremA.T2021

end

module

public import CFSG.ClassicalInvolution.Asc77.AscE186CentB
public import CFSG.ClassicalInvolution.Asc77.AscE186QuotOdd

public section

namespace CFSG.ClassicalInvolution.Asc77.AscE186

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G} {N : Subgroup G} [N.Normal]

omit [Finite G] in
theorem isPGroup_of_mem_RSet {G' : Type} [Group G'] {Ω' : Set (Subgroup G')} {R : Subgroup G'}
    (hR : R ∈ RSet Ω') : IsPGroup 2 ↥R := by
  obtain ⟨J, -, hJ⟩ := exists_isSylow2In_of_mem_RSet hR
  exact hJ.2.1

theorem exists_involution_of_ne_bot {A : Subgroup G} (hA : IsPGroup 2 ↥A) (hne : A ≠ ⊥) :
    ∃ a ∈ A, a ≠ 1 ∧ a * a = 1 := by
  have h2 : 2 ≤ Nat.card A := by
    have := (Subgroup.one_lt_card_iff_ne_bot A).mpr hne
    omega
  have h2dvd : 2 ∣ Nat.card ↥A := by
    rcases hA.card_eq_or_dvd with h | h
    · omega
    · exact h
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have htG : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htsq : (t : G) * (t : G) = 1 := by
    have := pow_orderOf_eq_one (t : G)
    rwa [htG, pow_two] at this
  refine ⟨t, t.2, ?_, htsq⟩
  intro h
  rw [h, orderOf_one] at htG
  omega

omit [N.Normal] in
theorem inf_sup_central_eq_bot (hH : H ≠ ⊤) (hcent : E186Cent2 Ω K H)
    (hNc : N ≤ Subgroup.center G) (hN2 : IsPGroup 2 ↥N) {L J R₁ R₂ : Subgroup G}
    (hL : L ∈ twinSet Ω K) (hJ : J ∈ KPerp Ω L) (hR₁ : R₁ ∈ RSet Ω) (hR₁L : R₁ ≤ L)
    (hR₂ : R₂ ∈ RSet Ω) (hR₂J : R₂ ≤ J) (hc : Commutes R₁ R₂ ∨ R₂ = R₁) :
    (R₁ ⊔ R₂) ⊓ N = ⊥ := by
  by_contra hne
  obtain ⟨a, ha, ha1, ha2⟩ := exists_involution_of_ne_bot (hN2.to_inf_right) hne
  apply hH
  rw [eq_top_iff]
  intro g _
  apply hcent L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hc a ha.1 ha1 ha2
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_center_iff.mp (hNc ha.2) g

omit [Finite G] in
theorem isPGroup_of_map_isPGroup {P : Subgroup G} (hN : IsPGroup 2 ↥N)
    (hP : IsPGroup 2 ↥(P.map (QuotientGroup.mk' N))) : IsPGroup 2 ↥P := by
  intro x
  obtain ⟨k, hk⟩ := hP ⟨QuotientGroup.mk' N (x : G), Subgroup.mem_map_of_mem _ x.2⟩
  have h1 : QuotientGroup.mk' N ((x : G) ^ 2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : (x : G) ^ 2 ^ k ∈ N := (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨m, hm⟩ := hN ⟨(x : G) ^ 2 ^ k, h2⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have h3 := congrArg Subtype.val hm
  simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h3 ⊢
  rw [pow_add, pow_mul]
  exact h3

theorem exists_lift_twin (hH : H ≠ ⊤) (hcent : E186Cent2 Ω K H) (hN2 : IsPGroup 2 ↥N)
    (c : CentQuot p f Ω N) (hK : K ∈ Ω) {Lb : Subgroup (G ⧸ N)}
    (hLb : Lb ∈ twinSet (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ L ∈ twinSet Ω K, L.map (QuotientGroup.mk' N) = Lb := by
  obtain ⟨hLbΩ, zb, hzbK, hzbL⟩ := hLb
  obtain ⟨L₀, hL₀, rfl⟩ := hLbΩ
  obtain ⟨z, hz⟩ := c.hyp.exists_uniqueInvolution c.odd c.five hK
  obtain ⟨z₀, hz₀⟩ := c.hyp.exists_uniqueInvolution c.odd c.five hL₀
  have e1 : QuotientGroup.mk' N z = zb :=
    (AscQuot.isUniqueInvolution_map_mk (c.meet K hK) hz).eq hzbK
  have e2 : QuotientGroup.mk' N z₀ = zb :=
    (AscQuot.isUniqueInvolution_map_mk (c.meet L₀ hL₀) hz₀).eq hzbL
  have hzz : z₀ = z := by
    by_cases hLK : L₀ = K
    · subst hLK
      exact (hz.eq hz₀).symm
    have hn : z₀⁻¹ * z ∈ N := by
      have : QuotientGroup.mk' N (z₀⁻¹ * z) = 1 := by
        rw [map_mul, map_inv, e1, e2, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp this
    have hzn : z = z₀ * (z₀⁻¹ * z) := by group
    have hLc : L₀ ≤ Subgroup.centralizer ({z} : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : z₀ * w = w * z₀ := hz₀.commute_of_mem hw
      have h2 : w * (z₀⁻¹ * z) = (z₀⁻¹ * z) * w :=
        Subgroup.mem_center_iff.mp (c.central hn) w
      calc w * z = w * (z₀ * (z₀⁻¹ * z)) := by rw [← hzn]
        _ = (w * z₀) * (z₀⁻¹ * z) := by group
        _ = (z₀ * w) * (z₀⁻¹ * z) := by rw [h1]
        _ = z₀ * (w * (z₀⁻¹ * z)) := by group
        _ = z₀ * ((z₀⁻¹ * z) * w) := by rw [h2]
        _ = z * w := by group
    have hnbr : L₀ ∈ omegaNbr Ω K :=
      mem_omegaNbr_of_le_centralizer c.odd c.five c.hyp hK hL₀ hLK hz hLc
    obtain ⟨R₁, R₂, hR₁, hR₂, -, hcomm⟩ := exists_commuting_sylow_pair c.odd c.five c.hyp hK hnbr
    have hR₁Ω : R₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR₁
    have hR₂Ω : R₂ ∈ RSet Ω := mem_RSet_of_isSylow2In hL₀ hR₂
    have hzR₁ : z ∈ R₁ := AscL62.mem_of_uniqueInvolution_of_pGroup hz hR₁.1 hR₁.2.1
      (by have := c.hyp.eight_le_of_mem_RSet c.odd hR₁Ω; omega)
    have hzR₂ : z₀ ∈ R₂ := AscL62.mem_of_uniqueInvolution_of_pGroup hz₀ hR₂.1 hR₂.2.1
      (by have := c.hyp.eight_le_of_mem_RSet c.odd hR₂Ω; omega)
    have hKtw : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
    have hbot := inf_sup_central_eq_bot hH hcent c.central hN2 hKtw (Set.mem_insert_of_mem _ hnbr)
      hR₁Ω hR₁.1 hR₂Ω hR₂.1 (Or.inl hcomm)
    have hmem : z₀⁻¹ * z ∈ (R₁ ⊔ R₂) ⊓ N := by
      refine ⟨?_, hn⟩
      have hz₀inv : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right hz₀.sq
      rw [hz₀inv]
      exact (R₁ ⊔ R₂).mul_mem (Subgroup.mem_sup_right hzR₂) (Subgroup.mem_sup_left hzR₁)
    rw [hbot, Subgroup.mem_bot] at hmem
    have : z = z₀ := by
      have := congrArg (fun w => z₀ * w) hmem
      simpa using this
    exact this.symm
  refine ⟨L₀, ⟨hL₀, z, hz, hzz ▸ hz₀⟩, rfl⟩

theorem exists_lift_kperp (c : CentQuot p f Ω N) {L : Subgroup G} (hL : L ∈ Ω)
    {Jb : Subgroup (G ⧸ N)}
    (hJb : Jb ∈ KPerp (quotFamily Ω N) (L.map (QuotientGroup.mk' N))) :
    ∃ J ∈ KPerp Ω L, J.map (QuotientGroup.mk' N) = Jb := by
  rcases hJb with rfl | hJbn
  · exact ⟨L, Set.mem_insert _ _, rfl⟩
  · obtain ⟨J₀, hJ₀, rfl⟩ := hJbn.1
    exact ⟨J₀, Set.mem_insert_of_mem _ (c.omegaNbr_of_map hL hJ₀ hJbn), rfl⟩

theorem exists_lift_sylow_pair (hN2 : IsPGroup 2 ↥N) (c : CentQuot p f Ω N) {L J : Subgroup G}
    (hL : L ∈ Ω) (hJ : J ∈ KPerp Ω L) {Rb₁ Rb₂ : Subgroup (G ⧸ N)}
    (hRb₁ : Rb₁ ∈ RSet (quotFamily Ω N)) (hRb₁L : Rb₁ ≤ L.map (QuotientGroup.mk' N))
    (hRb₂ : Rb₂ ∈ RSet (quotFamily Ω N)) (hRb₂J : Rb₂ ≤ J.map (QuotientGroup.mk' N))
    (hc : Commutes Rb₁ Rb₂ ∨ Rb₂ = Rb₁) :
    ∃ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω ∧ R₁ ≤ L ∧ R₂ ∈ RSet Ω ∧ R₂ ≤ J ∧
      R₁.map (QuotientGroup.mk' N) = Rb₁ ∧ R₂.map (QuotientGroup.mk' N) = Rb₂ ∧
      (Commutes R₁ R₂ ∨ R₂ = R₁) := by
  have hJΩ : J ∈ Ω := by
    rcases hJ with rfl | hJn
    · exact hL
    · exact hJn.1
  obtain ⟨R₁, hR₁, hR₁L, hR₁map⟩ := c.exists_lift_RSet hL hRb₁ hRb₁L
  rcases hc with hcomm | heq
  · obtain ⟨R₂, hR₂, hR₂J, hR₂map⟩ := c.exists_lift_RSet hJΩ hRb₂ hRb₂J
    refine ⟨R₁, R₂, hR₁, hR₁L, hR₂, hR₂J, hR₁map, hR₂map, ?_⟩
    by_cases hR₁₂ : R₂ = R₁
    · exact Or.inr hR₁₂
    refine Or.inl ?_
    have hR₁₂' : IsPGroup 2 ↥(R₁ ⊔ R₂) := by
      refine isPGroup_of_map_isPGroup hN2 ?_
      rw [Subgroup.map_sup, hR₁map, hR₂map]
      have hb₁ : IsPGroup 2 ↥Rb₁ := by
        rw [← hR₁map]
        exact (isPGroup_of_mem_RSet hR₁).map _
      have hb₂ : IsPGroup 2 ↥Rb₂ := by
        rw [← hR₂map]
        exact (isPGroup_of_mem_RSet hR₂).map _
      exact hb₁.to_sup_of_normal_right' hb₂ fun x hx =>
        mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hx hcomm)
    obtain ⟨S, hS⟩ := hR₁₂'.exists_le_sylow
    exact l6_7_proved p f c.odd c.five G Ω c.hyp S R₁ hR₁ R₂ hR₂ (le_sup_left.trans hS)
      (le_sup_right.trans hS) (Ne.symm hR₁₂)
  · have hJL : J = L := by
      by_contra hne
      have hJn : J ∈ omegaNbr Ω L := hJ.resolve_left hne
      have hLJ : L.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N) :=
        fun h => hne (c.eq_of_map_eq hL hJΩ h).symm
      have h2 := c.hyp'.card_le_two_of_le_inf (map_mem_quotFamily hL) (map_mem_quotFamily hJΩ) hLJ
        (isPGroup_of_mem_RSet hRb₁) hRb₁L (heq ▸ hRb₂J)
      have h8 := c.hyp'.eight_le_of_mem_RSet c.odd hRb₁
      omega
    subst hJL
    exact ⟨R₁, R₁, hR₁, hR₁L, hR₁, hR₁L, hR₁map, heq.symm ▸ hR₁map, Or.inr rfl⟩

theorem exists_involution_lift (hH : H ≠ ⊤) (hcent : E186Cent2 Ω K H)
    (hN2 : IsPGroup 2 ↥N) (hNc : N ≤ Subgroup.center G) {L J R₁ R₂ : Subgroup G}
    (hL : L ∈ twinSet Ω K) (hJ : J ∈ KPerp Ω L) (hR₁ : R₁ ∈ RSet Ω) (hR₁L : R₁ ≤ L)
    (hR₂ : R₂ ∈ RSet Ω) (hR₂J : R₂ ≤ J) (hc : Commutes R₁ R₂ ∨ R₂ = R₁) {a : G ⧸ N}
    (ha : a ∈ R₁.map (QuotientGroup.mk' N) ⊔ R₂.map (QuotientGroup.mk' N)) (ha1 : a ≠ 1)
    (ha2 : a * a = 1) :
    ∃ b ∈ R₁ ⊔ R₂, b ≠ 1 ∧ b * b = 1 ∧ QuotientGroup.mk' N b = a := by
  rw [← Subgroup.map_sup] at ha
  obtain ⟨b₁, hb₁, rfl⟩ := ha
  have hsq : b₁ * b₁ ∈ N := by
    have : QuotientGroup.mk' N (b₁ * b₁) = 1 := by rw [map_mul]; exact ha2
    exact (QuotientGroup.eq_one_iff _).mp this
  have hbot := inf_sup_central_eq_bot hH hcent hNc hN2 hL hJ hR₁ hR₁L hR₂ hR₂J hc
  have hmem : b₁ * b₁ ∈ (R₁ ⊔ R₂) ⊓ N := ⟨(R₁ ⊔ R₂).mul_mem hb₁ hb₁, hsq⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  refine ⟨b₁, hb₁, fun h => ha1 (by rw [h, map_one]), hmem, rfl⟩

theorem MinCex.mem_of_conj_mem (c : MinCex p f Ω K S R W H) (h182 : E18_2 p f)
    {M : Subgroup G} (hM : M ∈ dstarComp Ω K) {u : G} (hu : u ∈ M) (hu4 : orderOf u = 4)
    {g : G} (hg : g * u * g⁻¹ ∈ H) : g ∈ H := by
  obtain ⟨h, hhH, hh⟩ := c.hyp.trans M hM
  rw [← hh, mem_conjSub_iff] at hu
  have hu4' : orderOf (h⁻¹ * u * h) = 4 := by
    have := orderOf_injective (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective u
    rw [← hu4]
    simpa [inv_inv] using this
  have hgh : (g * h) * (h⁻¹ * u * h) * (g * h)⁻¹ ∈ H := by
    have : (g * h) * (h⁻¹ * u * h) * (g * h)⁻¹ = g * u * g⁻¹ := by group
    rw [this]
    exact hg
  have := h182 G Ω K S R W H c (h⁻¹ * u * h) hu hu4' (g * h) hgh
  exact (Subgroup.mul_mem_cancel_right H hhH).mp this

theorem E186Cent2.quot_cent (hH : H ≠ ⊤) (hN2 : IsPGroup 2 ↥N)
    (c : CentQuot p f Ω N) (hK : K ∈ Ω) (hcent : E186Cent2 Ω K H)
    (h18 : ∀ M ∈ dstarComp Ω K, ∀ u ∈ M, orderOf u = 4 → ∀ g : G, g * u * g⁻¹ ∈ H → g ∈ H) :
    E186Cent2 (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) (H.map (QuotientGroup.mk' N)) := by
  intro Lb hLb Jb hJb Rb₁ Rb₂ hRb₁ hRb₁L hRb₂ hRb₂J hcb ab hab hab1 hab2
  obtain ⟨L, hL, rfl⟩ := exists_lift_twin hH hcent hN2 c hK hLb
  obtain ⟨J, hJ, rfl⟩ := exists_lift_kperp c hL.1 hJb
  obtain ⟨R₁, R₂, hR₁, hR₁L, hR₂, hR₂J, rfl, rfl, hc⟩ :=
    exists_lift_sylow_pair hN2 c hL.1 hJ hRb₁ hRb₁L hRb₂ hRb₂J hcb
  obtain ⟨b, hb, hb1, hb2, rfl⟩ :=
    exists_involution_lift hH hcent hN2 c.central hL hJ hR₁ hR₁L hR₂ hR₂J hc hab hab1 hab2
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hn : b⁻¹ * (g * b * g⁻¹) ∈ N := by
    have : QuotientGroup.mk' N (b⁻¹ * (g * b * g⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      have h1 : QuotientGroup.mk' N g * QuotientGroup.mk' N b * (QuotientGroup.mk' N g)⁻¹ =
          QuotientGroup.mk' N b := by
        rw [hx]
        group
      rw [h1, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hQ : IsQuatSub R₁ := c.hyp.isQuatSub_of_mem_RSet c.odd hR₁
  obtain ⟨u, huR₁, hu4, hub⟩ : ∃ u ∈ R₁, orderOf u = 4 ∧ u * b = b * u := by
    rcases hc with hcomm | rfl
    · obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := exists_mul_of_mem_sup_of_commutes hcomm hb
      obtain ⟨u, huR₁, hu4, huy₁⟩ := exists_orderOf_four_commute_of_isQuatSub hQ hy₁
      refine ⟨u, huR₁, hu4, ?_⟩
      calc u * (y₁ * y₂) = (u * y₁) * y₂ := by group
        _ = (y₁ * u) * y₂ := by rw [huy₁]
        _ = y₁ * (u * y₂) := by group
        _ = y₁ * (y₂ * u) := by rw [hcomm u huR₁ y₂ hy₂]
        _ = (y₁ * y₂) * u := by group
    · rw [sup_idem] at hb
      exact exists_orderOf_four_commute_of_isQuatSub hQ hb
  have hgu : g * u * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : (g * u * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * u * g⁻¹) := by
      calc (g * u * g⁻¹) * (g * b * g⁻¹) = g * (u * b) * g⁻¹ := by group
        _ = g * (b * u) * g⁻¹ := by rw [hub]
        _ = (g * b * g⁻¹) * (g * u * g⁻¹) := by group
    set n : G := b⁻¹ * (g * b * g⁻¹) with hndef
    have hgb : g * b * g⁻¹ = b * n := by rw [hndef]; group
    rw [hgb] at e
    have hcn : ∀ y : G, y * n = n * y := fun y => Subgroup.mem_center_iff.mp (c.central hn) y
    have e2 : ((g * u * g⁻¹) * b) * n = (b * (g * u * g⁻¹)) * n := by
      calc ((g * u * g⁻¹) * b) * n = (g * u * g⁻¹) * (b * n) := by group
        _ = (b * n) * (g * u * g⁻¹) := e
        _ = b * (n * (g * u * g⁻¹)) := by group
        _ = b * ((g * u * g⁻¹) * n) := by rw [hcn]
        _ = (b * (g * u * g⁻¹)) * n := by group
    exact mul_right_cancel e2
  have hgH : g * u * g⁻¹ ∈ H := hcent L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hc b hb hb1 hb2 hgu
  have hg : g ∈ H :=
    h18 L (mem_dstarComp_of_twin c.odd c.hyp hK hL) u (hR₁L huR₁) hu4 g hgH
  exact Subgroup.mem_map_of_mem _ hg

theorem MinCex.cent_quot_stand (c : MinCex p f Ω K S R W H) (hc : CentQuot p f Ω N) :
    ∃ (Sb : Sylow 2 (G ⧸ N)) (Rb Wb : Subgroup (G ⧸ N)),
      EStand p f (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) Sb Rb Wb := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  have h3 : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3 p f (l6_7_proved p f) G Ω K S R W H c
  have hAΩ : ∀ J ∈ Ω, AEmpty Ω J :=
    aEmpty_forall_of_transitive hΩ.conjInvariant h3 c.stand.aEmpty
  set Sb : Sylow 2 (G ⧸ N) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S with hSbdef
  have hSb : (Sb : Subgroup (G ⧸ N)) = (S : Subgroup G).map (QuotientGroup.mk' N) :=
    Sylow.coe_mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S
  obtain ⟨Wb, hWb, hWbS, hWbn⟩ := exists_W_of_hypOmega hp hq hc.hyp' Sb
  have hRsyl : IsSylow2In R K := hΩ.isSylow2In_of_mem_RSet_of_le hp hK hRR hRK
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'tw
  have hR'syl : IsSylow2In R' K' := hΩ.isSylow2In_of_mem_RSet_of_le hp hK'Ω hR' hR'K'
  refine ⟨Sb, R.map (QuotientGroup.mk' N), Wb, ?_⟩
  exact
    { odd := hp
      five := hq
      hyp := hc.hyp'
      below := CITBelowU.mono p f (natCard_quotient_le N) c.stand.below
      mem := map_mem_quotFamily hK
      aEmpty := hc.aEmpty_quotFamily hAΩ _ (map_mem_quotFamily hK)
      twin := ⟨K'.map (QuotientGroup.mk' N),
        ⟨map_mem_quotFamily hK'Ω, QuotientGroup.mk' N z,
          AscQuot.isUniqueInvolution_map_mk (hc.meet K hK) hzK,
          AscQuot.isUniqueInvolution_map_mk (hc.meet K' hK'Ω) hzK'⟩,
        hc.map_ne_of_ne hK hK'Ω hK'ne,
        R'.map (QuotientGroup.mk' N),
        mem_RSet_of_isSylow2In (map_mem_quotFamily hK'Ω) (hc.isSylow2In_map hK'Ω hR'syl),
        Subgroup.map_mono hR'K', hSb ▸ Subgroup.map_mono hR'S⟩
      hR := ⟨mem_RSet_of_isSylow2In (map_mem_quotFamily hK) (hc.isSylow2In_map hK hRsyl),
        Subgroup.map_mono hRK, hSb ▸ Subgroup.map_mono hRS⟩
      hW := ⟨hWb, hWbS, hWbn⟩ }

theorem MinCex.cent_quot_trans (c : MinCex p f Ω K S R W H) (hc : CentQuot p f Ω N) :
    ∀ Jb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N)),
      ∃ hb ∈ H.map (QuotientGroup.mk' N),
        conjSub hb (K.map (QuotientGroup.mk' N)) = Jb := by
  intro Jb hJb
  obtain ⟨M, hM, hMeq⟩ := hc.exists_lift_dstarComp c.stand.mem hJb
  obtain ⟨h, hhH, hh⟩ := c.hyp.trans M hM
  refine ⟨QuotientGroup.mk' N h, Subgroup.mem_map_of_mem _ hhH, ?_⟩
  rw [← hMeq, ← hh, AscQuot.map_conjSub]

end CFSG.ClassicalInvolution.Asc77.AscE186

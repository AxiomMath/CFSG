module

public import CFSG.ClassicalInvolution.Asc77.AscT7BConst

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7B

variable {G : Type} [Group G]

theorem mem_centralizer_closure_pair {a b c : G} (ha : a * c = c * a) (hb : b * c = c * b) :
    c ∈ Subgroup.centralizer ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr ha
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hb
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)

theorem eq_one_of_central [IsSimpleGroup G] {c : G} (hnc : ∃ x y : G, x * y ≠ y * x)
    (hc : ∀ g : G, g * c = c * g) : c = 1 := by
  by_contra hc1
  have : (Subgroup.zpowers c).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := hn
    have h1 : g * c ^ k = c ^ k * g := (Commute.zpow_right (show Commute g c from hc g) k).eq
    show g * c ^ k * g⁻¹ ∈ Subgroup.zpowers c
    rw [h1, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers c) with h | h
  · exact hc1 (Subgroup.zpowers_eq_bot.mp h)
  · obtain ⟨x, y, hxy⟩ := hnc
    have hx : x ∈ Subgroup.zpowers c := h ▸ Subgroup.mem_top x
    have hy : y ∈ Subgroup.zpowers c := h ▸ Subgroup.mem_top y
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact hxy (Commute.zpow_zpow_self c m n).eq

theorem eq_bot_of_normalizer_eq_top [IsSimpleGroup G] {A : Subgroup G} (hodd : Odd (Nat.card A))
    (hN : Subgroup.normalizer (A : Set G) = ⊤) (hev : 2 ∣ Nat.card G) : A = ⊥ := by
  have hnormal : A.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  rcases hnormal.eq_bot_or_eq_top with h | h
  · exact h
  · rw [h, Subgroup.card_top] at hodd
    exact absurd (even_iff_two_dvd.mpr hev) (Nat.not_even_iff_odd.mpr hodd)

variable [Finite G]

omit [Finite G] in
theorem two_dvd_natCard {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) :
    2 ∣ Nat.card G := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have := orderOf_dvd_natCard (x := z)
  rwa [hz2] at this

end T7B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

namespace Hyp22

theorem exists_centralizer_conj (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) {J : Subgroup G}
    (hJ : J ∈ twinSet Ω K) : ∃ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c K = J := by
  obtain ⟨g, hg⟩ := h.std.stand.trans J hJ.1
  have hzJ : IsUniqueInvolution J z := isUniqueInvolution_of_mem_twinSet h.std.hz hJ
  have h1 : IsUniqueInvolution J (g * z * g⁻¹) := hg ▸ h.std.hz.conj g
  have h2 : g * z * g⁻¹ = z := h1.eq hzJ
  refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, hg⟩
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [h2]

theorem stdCent_of_twin (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) {H : Subgroup G}
    (hz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (htwin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 → Subgroup.centralizer ({x * y} : Set G) ≤ H) :
    StdCent Ω K H z where
  z_le := hz
  nonTwin := by
    intro L hL J hJ z' hz' hzz
    exfalso
    have hJperp : J ∈ KPerp Ω L := Set.mem_insert_of_mem _ hJ
    have hJt : J ∈ twinSet Ω K := by
      have := T7B.perp_of_twin h.std h.perp hL
      rw [this, twinSet_eq_of_mem_twinSet h.std.hz hL] at hJperp
      exact hJperp
    have hJz : IsUniqueInvolution J z := isUniqueInvolution_of_mem_twinSet h.std.hz hJt
    exact hzz (hz'.eq hJz)
  twin := htwin

theorem exists_datum_of_pair (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) {L L' : Subgroup G}
    (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K) (hne : L' ≠ L) {R₁ R₂ : Subgroup G}
    (hR₁ : IsSylow2In R₁ L) (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) {x y : G}
    (hx : x ∈ R₁) (hy : y ∈ R₂) (ox : orderOf x = 4) (oy : orderOf y = 4) :
    ∃ (L₃ : Subgroup G) (w : G), Hyp22 p f Ω L L' L₃ z x y w := by
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self h.std.stand.mem h.std.hz
  obtain ⟨L₃, hL₃, hL₃L, hL₃L'⟩ : ∃ L₃ ∈ twinSet Ω K, L₃ ≠ L ∧ L₃ ≠ L' := by
    rcases T7B.exists_ne_of_three (a := L) (b := L') h.std.hne h.hK₃K h.hK₃K' with hh | hh | hh
    · exact ⟨K, hKV, hh.1, hh.2⟩
    · exact ⟨K', h.std.hK', hh.1, hh.2⟩
    · exact ⟨K₃, h.hK₃, hh.1, hh.2⟩
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet h.std.hz hL
  have hzL' : IsUniqueInvolution L' z := isUniqueInvolution_of_mem_twinSet h.std.hz hL'
  have hzL₃ : IsUniqueInvolution L₃ z := isUniqueInvolution_of_mem_twinSet h.std.hz hL₃
  obtain ⟨R₃, hR₃, c₁, c₂⟩ := T7B.exists_third_sylow hp hq hΩ hL.1 hL'.1 hL₃.1 hzL hzL' hzL₃
    hL₃L hL₃L' hR₁ hR₂ hc
  obtain ⟨w, hw, ow⟩ :=
    hΩ.exists_orderOf_eq_four_of_mem_RSet hp (mem_RSet_of_isSylow2In hL₃.1 hR₃)
  have hs : Std7 p f Ω L L' z := Std7.of_twin h.std hL hL' hne
  have hperp : KPerp Ω L = twinSet Ω L := T7B.perp_of_twin h.std h.perp hL
  have hL₃' : L₃ ∈ twinSet Ω L := by rw [twinSet_eq_of_mem_twinSet h.std.hz hL]; exact hL₃
  exact ⟨L₃, w, T7B.hyp22_of_sylows hs hperp hL₃' hL₃L hL₃L' hR₁ hR₂ hR₃ hc c₁ c₂ hx hy hw
    ox oy ow⟩

end Hyp22

section C224

variable (p f)

@[expose] def C22_4_sigma : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ W ∈ WSet Ω, ¬ MuIsoWylD4 Ω W → ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K

@[expose] def C22_4_cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ W ∈ WSet Ω, ¬ MuIsoWylD4 Ω W →
        Subgroup.centralizer ({u₁ * u₂} : Set G) ≤
          alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) ⊔
            (Subgroup.centralizer ({u₁ * u₂} : Set G) ⊓ Subgroup.centralizer ({z} : Set G))

variable {p f}

theorem c22_4_of (hE : ThmEWithSylow p f) (h2 : C22_2 p f) (hsig : C22_4_sigma p f)
    (hcent : C22_4_cent p f) : C22_4 p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h W hW
  by_contra hμ
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hcentD : ∀ {L L' L₃ : Subgroup G} {x y w : G}, Hyp22 p f Ω L L' L₃ z x y w →
      Subgroup.centralizer ({x * y} : Set G) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥ →
        Subgroup.centralizer ({x * y} : Set G) ≤ Subgroup.centralizer ({z} : Set G)) := by
    intro L L' L₃ x y w hd
    have hc := hcent G Ω L L' L₃ z x y w hd W hW hμ
    have heq := Hyp22.alpha_eq_of_datum h2 hd h
    refine ⟨fun c hcC => ?_, fun hα => ?_⟩
    · have hinf : Subgroup.centralizer ({x * y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({x * y, z} : Set G)) : Set G) := by
        intro c' hc'
        have ha : c' * (x * y) = (x * y) * c' :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').1
        have hb : c' * z = z * c' :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').2
        exact T7B.centralizer_le_normalizer_alphaOf _
          (T7B.mem_centralizer_closure_pair ha.symm hb.symm)
      have h1 : c ∈ Subgroup.normalizer
          (alphaOf (Subgroup.closure ({x * y, z} : Set G)) : Set G) :=
        (sup_le Subgroup.le_normalizer hinf) (hc hcC)
      rwa [heq] at h1
    · rw [← heq] at hα
      rw [hα, bot_sup_eq] at hc
      exact hc.trans inf_le_right
  have htwin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 → ∃ (L₃ : Subgroup G) (w : G), Hyp22 p f Ω L L' L₃ z x y w :=
    fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy =>
      h.exists_datum_of_pair hL hL' hne hR₁ hR₂ hc hx hy ox oy
  have hstd1 : StdCent Ω K (Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G)) z :=
    h.stdCent_of_twin (h.centralizer_le_normalizer_alpha h2) fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc
      x hx y hy ox oy => by
      obtain ⟨L₃, w, hd⟩ := htwin L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
      exact (hcentD hd).1
  have htrans1 : ∀ J ∈ dstarComp Ω K, ∃ c ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G), conjSub c K = J := by
    intro J hJ
    obtain ⟨c, hc, hcJ⟩ := h.exists_centralizer_conj (hsig G Ω K K' K₃ z u₁ u₂ u₃ h W hW hμ J hJ)
    exact ⟨c, h.centralizer_le_normalizer_alpha h2 hc, hcJ⟩
  have htop1 := thmE_apply hE h.std.stand h.std.hz h.std.hK' h.std.hne hstd1 htrans1
  have hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥ :=
    T7B.eq_bot_of_normalizer_eq_top (h2 G Ω K K' K₃ z u₁ u₂ u₃ h).1 htop1
      (T7B.two_dvd_natCard h.std.hz)
  have hstd2 : StdCent Ω K (Subgroup.centralizer ({z} : Set G)) z :=
    h.stdCent_of_twin le_rfl fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
      obtain ⟨L₃, w, hd⟩ := htwin L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
      exact (hcentD hd).2 hα
  have htrans2 : ∀ J ∈ dstarComp Ω K, ∃ c ∈ Subgroup.centralizer ({z} : Set G),
      conjSub c K = J := fun J hJ =>
    h.exists_centralizer_conj (hsig G Ω K K' K₃ z u₁ u₂ u₃ h W hW hμ J hJ)
  have htop2 := thmE_apply hE h.std.stand h.std.hz h.std.hK' h.std.hne hstd2 htrans2
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  obtain ⟨x, -, y, -, hxy⟩ :=
    (hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hV)).exists_not_commute
  have hz1 : z = 1 := T7B.eq_one_of_central ⟨x, y, hxy⟩ fun g => by
    have : g ∈ Subgroup.centralizer ({z} : Set G) := by rw [htop2]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  exact h.std.hz.ne_one hz1

end C224

section C227

variable (p f)

@[expose] def C22_7_trans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) → ∀ J ∈ dstarComp Ω K, ∃ x ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G), conjSub x K = J

@[expose] def C22_7_cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) → Subgroup.centralizer ({u₁ * u₂} : Set G) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G)

variable {p f}

theorem c22_7_of (hE : ThmEWithSylow p f) (h2 : C22_2 p f) (h4 : C22_4 p f)
    (htr : C22_7_trans p f) (hc : C22_7_cent p f) : C22_7 p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  have hμ := h4 G Ω K K' K₃ z u₁ u₂ u₃ h
  have hstd : StdCent Ω K (Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G)) z :=
    h.stdCent_of_twin (h.centralizer_le_normalizer_alpha h2) fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hcm
      x hx y hy ox oy => by
      obtain ⟨L₃, w, hd⟩ := h.exists_datum_of_pair hL hL' hne hR₁ hR₂ hcm hx hy ox oy
      have hc' := hc G Ω L L' L₃ z x y w hd (h4 G Ω L L' L₃ z x y w hd)
      have heq := Hyp22.alpha_eq_of_datum h2 hd h
      rw [heq] at hc'
      exact hc'
  have htop := thmE_apply hE h.std.stand h.std.hz h.std.hK' h.std.hne hstd
    (htr G Ω K K' K₃ z u₁ u₂ u₃ h hμ)
  exact T7B.eq_bot_of_normalizer_eq_top (h2 G Ω K K' K₃ z u₁ u₂ u₃ h).1 htop
    (T7B.two_dvd_natCard h.std.hz)

end C227

end CFSG.ClassicalInvolution.Asc77

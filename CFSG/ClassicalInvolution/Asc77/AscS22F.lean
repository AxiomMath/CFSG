module

public import CFSG.ClassicalInvolution.Asc77.AscS22E
public import CFSG.ClassicalInvolution.Asc77.AscT7JCent

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S22

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section ThmE

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem exists_centralizer_conj (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {J : Subgroup G}
    (hJ : J ∈ twinSet Ω K) : ∃ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c K = J := by
  obtain ⟨g, hg⟩ := h.stand.trans J hJ.1
  have hzJ : IsUniqueInvolution J z := isUniqueInvolution_of_mem_twinSet h.hz hJ
  have h1 : IsUniqueInvolution J (g * z * g⁻¹) := hg ▸ h.hz.conj g
  have h2 : g * z * g⁻¹ = z := h1.eq hzJ
  refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, hg⟩
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [h2]

theorem stdCent_of_twin (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {H : Subgroup G}
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
      have := T7S22.perp_of_twin h hL
      rw [this, twinSet_eq_of_mem_twinSet h.hz hL] at hJperp
      exact hJperp
    have hJz : IsUniqueInvolution J z := isUniqueInvolution_of_mem_twinSet h.hz hJt
    exact hzz (hz'.eq hJz)
  twin := htwin

theorem exists_datum_of_pair (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {L L' : Subgroup G}
    (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K) (hne : L' ≠ L) {R₁ R₂ : Subgroup G}
    (hR₁ : IsSylow2In R₁ L) (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) {x y : G}
    (hx : x ∈ R₁) (hy : y ∈ R₂) (ox : orderOf x = 4) (oy : orderOf y = 4) :
    ∃ (L₃ : Subgroup G) (w : G), Hyp22Setting p f Ω L L' L₃ z x y w := by
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hp : p ≠ 2 := h.stand.odd
  have hq : 5 ≤ p ^ f := h.stand.five
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self h.stand.mem h.hz
  obtain ⟨L₃, hL₃, hL₃L, hL₃L'⟩ : ∃ L₃ ∈ twinSet Ω K, L₃ ≠ L ∧ L₃ ≠ L' := by
    rcases T7B.exists_ne_of_three (a := L) (b := L') h.hne h.hK₃K h.hK₃K' with hh | hh | hh
    · exact ⟨K, hKV, hh.1, hh.2⟩
    · exact ⟨K', h.hK', hh.1, hh.2⟩
    · exact ⟨K₃, h.hK₃, hh.1, hh.2⟩
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet h.hz hL
  have hzL' : IsUniqueInvolution L' z := isUniqueInvolution_of_mem_twinSet h.hz hL'
  have hzL₃ : IsUniqueInvolution L₃ z := isUniqueInvolution_of_mem_twinSet h.hz hL₃
  obtain ⟨R₃, hR₃, c₁, c₂⟩ := T7B.exists_third_sylow hp hq hΩ hL.1 hL'.1 hL₃.1 hzL hzL' hzL₃
    hL₃L hL₃L' hR₁ hR₂ hc
  obtain ⟨w, hw, ow⟩ :=
    hΩ.exists_orderOf_eq_four_of_mem_RSet hp (mem_RSet_of_isSylow2In hL₃.1 hR₃)
  have hperp : KPerp Ω L = twinSet Ω L := T7S22.perp_of_twin h hL
  have hL₃' : L₃ ∈ twinSet Ω L := by rw [twinSet_eq_of_mem_twinSet h.hz hL]; exact hL₃
  have hL'' : L' ∈ twinSet Ω L := by rw [twinSet_eq_of_mem_twinSet h.hz hL]; exact hL'
  exact ⟨L₃, w, hyp22Setting_of_sylows (h.stand.of_mem hL.1) hzL hL'' hne hperp hL₃' hL₃L hL₃L'
    hR₁ hR₂ hR₃ hc c₁ c₂ hx hy hw ox oy ow⟩

end ThmE

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem false_of_abelian (hE : ThmEWithSylow p f) (h2 : C22_2S p f)
    (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hb : Big Ω K)
    (hsig : ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K)
    (hcent : ∀ {L L' L₃ : Subgroup G} {x y w : G}, Hyp22Setting p f Ω L L' L₃ z x y w →
      Subgroup.centralizer ({x * y} : Set G) ≤
        alphaOf (Subgroup.closure ({x * y, z} : Set G)) ⊔
          (Subgroup.centralizer ({x * y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G))) :
    False := by
  have hp : p ≠ 2 := h.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hK : K ∈ Ω := h.stand.mem
  have hcentD : ∀ {L L' L₃ : Subgroup G} {x y w : G}, Hyp22Setting p f Ω L L' L₃ z x y w →
      Subgroup.centralizer ({x * y} : Set G) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥ →
        Subgroup.centralizer ({x * y} : Set G) ≤ Subgroup.centralizer ({z} : Set G)) := by
    intro L L' L₃ x y w hd
    have hc := hcent hd
    have heq := (alpha_eq_of_datum h2 h hd hb).symm
    refine ⟨fun c hcC => ?_, fun hα => ?_⟩
    · have hinf : Subgroup.centralizer ({x * y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({x * y, z} : Set G)) : Set G) := by
        intro c' hc'
        have ha : c' * (x * y) = (x * y) * c' :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').1
        have hb' : c' * z = z * c' :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').2
        exact T7B.centralizer_le_normalizer_alphaOf _
          (T7B.mem_centralizer_closure_pair ha.symm hb'.symm)
      have h1 : c ∈ Subgroup.normalizer
          (alphaOf (Subgroup.closure ({x * y, z} : Set G)) : Set G) :=
        (sup_le Subgroup.le_normalizer hinf) (hc hcC)
      rwa [heq] at h1
    · rw [← heq] at hα
      rw [hα, bot_sup_eq] at hc
      exact hc.trans inf_le_right
  have htwin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 →
          ∃ (L₃ : Subgroup G) (w : G), Hyp22Setting p f Ω L L' L₃ z x y w :=
    fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy =>
      exists_datum_of_pair h hL hL' hne hR₁ hR₂ hc hx hy ox oy
  have hstd1 : StdCent Ω K (Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G)) z :=
    stdCent_of_twin h (centralizer_le_normalizer_alpha h2 h hb)
      fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
        obtain ⟨L₃, w, hd⟩ := htwin L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
        exact (hcentD hd).1
  have htrans1 : ∀ J ∈ dstarComp Ω K, ∃ c ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G), conjSub c K = J := by
    intro J hJ
    obtain ⟨c, hc, hcJ⟩ := exists_centralizer_conj h (hsig J hJ)
    exact ⟨c, centralizer_le_normalizer_alpha h2 h hb hc, hcJ⟩
  have htop1 := thmE_apply hE h.stand h.hz h.hK' h.hne hstd1 htrans1
  have hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥ :=
    T7B.eq_bot_of_normalizer_eq_top (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).1 htop1
      (T7B.two_dvd_natCard h.hz)
  have hstd2 : StdCent Ω K (Subgroup.centralizer ({z} : Set G)) z :=
    stdCent_of_twin h le_rfl fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
      obtain ⟨L₃, w, hd⟩ := htwin L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
      exact (hcentD hd).2 hα
  have htrans2 : ∀ J ∈ dstarComp Ω K, ∃ c ∈ Subgroup.centralizer ({z} : Set G),
      conjSub c K = J := fun J hJ => exists_centralizer_conj h (hsig J hJ)
  have htop2 := thmE_apply hE h.stand h.hz h.hK' h.hne hstd2 htrans2
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  obtain ⟨x, -, y, -, hxy⟩ :=
    (hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hV)).exists_not_commute
  have hz1 : z = 1 := T7B.eq_one_of_central ⟨x, y, hxy⟩ fun g => by
    have : g ∈ Subgroup.centralizer ({z} : Set G) := by rw [htop2]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  exact h.hz.ne_one hz1

end Main

section Frattini

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem cent_of_zstar (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hzs : z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set G))) :
    Subgroup.centralizer ({u₁ * u₂} : Set G) ≤
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) ⊔
        (Subgroup.centralizer ({u₁ * u₂} : Set G) ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have hu1 : u₁ * u₂ ≠ 1 :=
    (T7S22.mul_ne_one_of_twins h.stand.hyp h.stand.mem h.hK'.1 h.hne.symm h.hz h.hu₁.1
      h.hu₂.1 h.hu₂.2).1
  have hz2 : z * z = 1 := h.hz.sq
  obtain ⟨zh, hzh, hzhz⟩ := Subgroup.mem_map.mp hzs
  rw [Subgroup.mem_comap] at hzh
  have hzH : z ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) := by
    rw [← hzhz]
    exact zh.2
  refine T7J.le_sup_of_zstar hz2 hzH (CFSG.ClassicalInvolution.Balance.oddCoreIn_le _)
    (oddCoreOf_odd_natCard _)
    (fun h' hh' n hn =>
      CFSG.ClassicalInvolution.Balance.Bootstrap.conj_mem_oddCoreIn_of_mem_normalizer
        (Subgroup.le_normalizer hh') hn)
    (fun g hg => ?_) ?_
  ·
    have hc := Subgroup.mem_center_iff.mp hzh (QuotientGroup.mk' _ ⟨g, hg⟩)
    have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer
        ({u₁ * u₂} : Set G))) (⟨g, hg⟩ * zh * ⟨g, hg⟩⁻¹ * zh⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    refine ⟨_, h1, ?_⟩
    simp [commutatorElement_def, ← hzhz]
  ·
    have hu_mem : u₁ * u₂ ∈ Subgroup.closure ({u₁ * u₂, z} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hz_mem : z ∈ Subgroup.closure ({u₁ * u₂, z} : Set G) :=
      Subgroup.subset_closure (by simp)
    refine le_trans (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hz_mem)) ?_
    unfold alphaOf
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le (u₁ * u₂) hu_mem
      (le_iSup (fun _ : u₁ * u₂ ≠ 1 => ⁅oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set G)),
        Subgroup.closure ({u₁ * u₂, z} : Set G)⁆) hu1)

end Frattini

end S22

end CFSG.ClassicalInvolution.Asc77

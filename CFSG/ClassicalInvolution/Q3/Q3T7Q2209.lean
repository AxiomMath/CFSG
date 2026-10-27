module

public import CFSG.ClassicalInvolution.Q3.Q3T8C262A
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2208
public import CFSG.ClassicalInvolution.Asc77.AscC22G2

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S22
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section ThmE
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem exists_centralizer_conj
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {J : Subgroup G}
    (hJ : J ∈ twinSet Ω K) : ∃ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c K = J := by
  obtain ⟨g, hg⟩ := h.stand.trans J hJ.1
  have hzJ : IsUniqueInvolution J z := isUniqueInvolution_of_mem_twinSet h.hz hJ
  have h1 : IsUniqueInvolution J (g * z * g⁻¹) := hg ▸ h.hz.conj g
  have h2 : g * z * g⁻¹ = z := h1.eq hzJ
  refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, hg⟩
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [h2]

theorem stdCent_of_twin
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {H : Subgroup G}
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
      have := Q3T8.Asc77.T7S22.perp_of_twin h hL
      rw [this, twinSet_eq_of_mem_twinSet h.hz hL] at hJperp
      exact hJperp
    have hJz : IsUniqueInvolution J z := isUniqueInvolution_of_mem_twinSet h.hz hJt
    exact hzz (hz'.eq hJz)
  twin := htwin

theorem exists_datum_of_pair
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {L L' : Subgroup G}
    (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K) (hne : L' ≠ L) {R₁ R₂ : Subgroup G}
    (hR₁ : IsSylow2In R₁ L) (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) {x y : G}
    (hx : x ∈ R₁) (hy : y ∈ R₂) (ox : orderOf x = 4) (oy : orderOf y = 4) :
    ∃ (L₃ : Subgroup G) (w : G), Q3T8.Asc77.Hyp22Setting Ω L L' L₃ z x y w := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self h.stand.mem h.hz
  obtain ⟨L₃, hL₃, hL₃L, hL₃L'⟩ : ∃ L₃ ∈ twinSet Ω K, L₃ ≠ L ∧ L₃ ≠ L' := by
    rcases T7B.exists_ne_of_three (a := L) (b := L') h.hne h.hK₃K h.hK₃K' with hh | hh | hh
    · exact ⟨K, hKV, hh.1, hh.2⟩
    · exact ⟨K', h.hK', hh.1, hh.2⟩
    · exact ⟨K₃, h.hK₃, hh.1, hh.2⟩
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet h.hz hL
  have hzL' : IsUniqueInvolution L' z := isUniqueInvolution_of_mem_twinSet h.hz hL'
  have hzL₃ : IsUniqueInvolution L₃ z := isUniqueInvolution_of_mem_twinSet h.hz hL₃
  obtain ⟨R₃, hR₃, c₁, c₂⟩ := Q3T8.Asc77.T7B.exists_third_sylow hΩ hL.1 hL'.1 hL₃.1 hzL hzL' hzL₃
    hL₃L hL₃L' hR₁ hR₂ hc
  obtain ⟨w, hw, ow⟩ :=
    hΩ.exists_orderOf_eq_four_of_mem_RSet (mem_RSet_of_isSylow2In hL₃.1 hR₃)
  have hperp : KPerp Ω L = twinSet Ω L := Q3T8.Asc77.T7S22.perp_of_twin h hL
  have hL₃' : L₃ ∈ twinSet Ω L := by rw [twinSet_eq_of_mem_twinSet h.hz hL]; exact hL₃
  have hL'' : L' ∈ twinSet Ω L := by rw [twinSet_eq_of_mem_twinSet h.hz hL]; exact hL'
  exact ⟨L₃, w, Q3T8.Asc77.S22.hyp22Setting_of_sylows (h.stand.of_mem hL.1) hzL hL'' hne hperp hL₃'
      hL₃L hL₃L'
    hR₁ hR₂ hR₃ hc c₁ c₂ hx hy hw ox oy ow⟩
end ThmE
section Main
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem false_of_abelian
    (hE : Q3T7E.ThmEWithSylow3) (h2 : Q3T8.Asc77.S22.C22_2S)
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hb : Big Ω K)
    (hsig : ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K)
    (hcent : ∀ {L L' L₃ : Subgroup G} {x y w : G}, Q3T8.Asc77.Hyp22Setting Ω L L' L₃ z x y w →
      Subgroup.centralizer ({x * y} : Set G) ≤
        alphaOf (Subgroup.closure ({x * y, z} : Set G)) ⊔
          (Subgroup.centralizer ({x * y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G))) :
    False := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hK : K ∈ Ω := h.stand.mem
  
  have hcentD : ∀ {L L' L₃ : Subgroup G} {x y w : G}, Q3T8.Asc77.Hyp22Setting Ω L L' L₃ z x y w →
      Subgroup.centralizer ({x * y} : Set G) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥ →
        Subgroup.centralizer ({x * y} : Set G) ≤ Subgroup.centralizer ({z} : Set G)) := by
    intro L L' L₃ x y w hd
    have hc := hcent hd
    have heq := (Q3T8.Asc77.S22.alpha_eq_of_datum h2 h hd hb).symm
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
          ∃ (L₃ : Subgroup G) (w : G), Q3T8.Asc77.Hyp22Setting Ω L L' L₃ z x y w :=
    fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy =>
      Q3T8.Asc77.S22.exists_datum_of_pair h hL hL' hne hR₁ hR₂ hc hx hy ox oy
  
  have hstd1 : StdCent Ω K (Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G)) z :=
    Q3T8.Asc77.S22.stdCent_of_twin h (Q3T8.Asc77.S22.centralizer_le_normalizer_alpha h2 h hb)
      fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
        obtain ⟨L₃, w, hd⟩ := htwin L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
        exact (hcentD hd).1
  have htrans1 : ∀ J ∈ dstarComp Ω K, ∃ c ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G), conjSub c K = J := by
    intro J hJ
    obtain ⟨c, hc, hcJ⟩ := Q3T8.Asc77.S22.exists_centralizer_conj h (hsig J hJ)
    exact ⟨c, Q3T8.Asc77.S22.centralizer_le_normalizer_alpha h2 h hb hc, hcJ⟩
  have htop1 := Q3T8.Asc77.thmE_apply hE h.stand h.hz h.hK' h.hne hstd1 htrans1
  have hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥ :=
    T7B.eq_bot_of_normalizer_eq_top (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).1 htop1
      (T7B.two_dvd_natCard h.hz)
  
  have hstd2 : StdCent Ω K (Subgroup.centralizer ({z} : Set G)) z :=
    Q3T8.Asc77.S22.stdCent_of_twin h le_rfl fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy =>
        by
      obtain ⟨L₃, w, hd⟩ := htwin L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
      exact (hcentD hd).2 hα
  have htrans2 : ∀ J ∈ dstarComp Ω K, ∃ c ∈ Subgroup.centralizer ({z} : Set G),
      conjSub c K = J := fun J hJ => Q3T8.Asc77.S22.exists_centralizer_conj h (hsig J hJ)
  have htop2 := Q3T8.Asc77.thmE_apply hE h.stand h.hz h.hK' h.hne hstd2 htrans2
  
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  obtain ⟨x, -, y, -, hxy⟩ :=
    (hΩ.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In hK hV)).exists_not_commute
  have hz1 : z = 1 := T7B.eq_one_of_central ⟨x, y, hxy⟩ fun g => by
    have : g ∈ Subgroup.centralizer ({z} : Set G) := by rw [htop2]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  exact h.hz.ne_one hz1
end Main
section Frattini
variable {G : Type} [Group G] [Finite G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem cent_of_zstar
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hzs : z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set G))) :
    Subgroup.centralizer ({u₁ * u₂} : Set G) ≤
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) ⊔
        (Subgroup.centralizer ({u₁ * u₂} : Set G) ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have hu1 : u₁ * u₂ ≠ 1 :=
    (Q3T8.Asc77.T7S22.mul_ne_one_of_twins h.stand.modU h.stand.mem h.hK'.1 h.hne.symm h.hz h.hu₁.1
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
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T7V
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7V
section Frame
variable {G : Type} [Group G]

@[expose] def FuseFrame
    (K₃ K₄ : Subgroup G) (z u : G) : Prop :=
  ∃ (R R' : Subgroup G) (b b' y : G),
    IsSylow2In R (Q3T8.Asc77.ExactLayer.exactCore u K₃) ∧ IsSylow2In R'
        (Q3T8.Asc77.ExactLayer.exactCore u K₄) ∧
    Commutes R R' ∧ b ∈ Q3T8.Asc77.ExactLayer.exactCore u K₃ ∧ b' ∈ Q3T8.Asc77.ExactLayer.exactCore
        u K₄ ∧
    b * b = z ∧ b' * b' = z ∧ y ∈ Subgroup.centralizer ({u} : Set G) ∧
    y * z * y⁻¹ = b * b' * u ∧ b * b' * u ≠ z ∧ z * (b * b' * u) = (b * b' * u) * z
variable [Finite G]

theorem FuseFrame.conj
    {K₃ K₄ : Subgroup G} {z u : G} (hF : Q3T8.Asc77.T7V.FuseFrame K₃ K₄ z u) {c
    : G}
    (hc₃ : conjSub c K₃ = K₃) (hc₄ : conjSub c K₄ = K₄) (hcz : c * z * c⁻¹ = z) :
    Q3T8.Asc77.T7V.FuseFrame K₃ K₄ z (c * u * c⁻¹) := by
  obtain ⟨R, R', b, b', y, hR, hR', hRR', hb, hb', hbz, hb'z, hy, hyz, hne, hcomm⟩ := hF
  have hcz' : c⁻¹ * z * c = z := by
    have := congrArg (fun x => c⁻¹ * x * c) hcz
    simpa [mul_assoc] using this.symm
  have e₃ : Q3T8.Asc77.ExactLayer.exactCore (c * u * c⁻¹) K₃ = conjSub c
      (Q3T8.Asc77.ExactLayer.exactCore u K₃) := by
    rw [← Q3T8.Asc77.ExactLayer.exactCore_conjSub, hc₃]
  have e₄ : Q3T8.Asc77.ExactLayer.exactCore (c * u * c⁻¹) K₄ = conjSub c
      (Q3T8.Asc77.ExactLayer.exactCore u K₄) := by
    rw [← Q3T8.Asc77.ExactLayer.exactCore_conjSub, hc₄]
  refine ⟨conjSub c R, conjSub c R', c * b * c⁻¹, c * b' * c⁻¹, c * y * c⁻¹, ?_, ?_,
    hRR'.conjSub c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₃]; exact hR.conj c
  · rw [e₄]; exact hR'.conj c
  · rw [e₃]; exact conj_mem_conjSub hb
  · rw [e₄]; exact conj_mem_conjSub hb'
  · calc c * b * c⁻¹ * (c * b * c⁻¹) = c * (b * b) * c⁻¹ := by group
      _ = z := by rw [hbz, hcz]
  · calc c * b' * c⁻¹ * (c * b' * c⁻¹) = c * (b' * b') * c⁻¹ := by group
      _ = z := by rw [hb'z, hcz]
  · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    calc c * y * c⁻¹ * (c * u * c⁻¹) = c * (y * u) * c⁻¹ := by group
      _ = c * (u * y) * c⁻¹ := by rw [hy]
      _ = c * u * c⁻¹ * (c * y * c⁻¹) := by group
  · calc c * y * c⁻¹ * z * (c * y * c⁻¹)⁻¹ = c * y * (c⁻¹ * z * c) * y⁻¹ * c⁻¹ := by group
      _ = c * (y * z * y⁻¹) * c⁻¹ := by rw [hcz']; group
      _ = c * (b * b' * u) * c⁻¹ := by rw [hyz]
      _ = c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹) := by group
  · intro h
    apply hne
    have h2 : b * b' * u = c⁻¹ * (c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹)) * c := by group
    rw [h2, h, hcz']
  · calc z * (c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹)) =
        c * (z * (b * b' * u)) * c⁻¹ := by
          calc z * (c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹))
              = (c * z * c⁻¹) * (c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹)) := by rw [hcz]
            _ = c * (z * (b * b' * u)) * c⁻¹ := by group
      _ = c * ((b * b' * u) * z) * c⁻¹ := by rw [hcomm]
      _ = (c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹)) * z := by
          calc c * ((b * b' * u) * z) * c⁻¹
              = (c * b * c⁻¹ * (c * b' * c⁻¹) * (c * u * c⁻¹)) * (c * z * c⁻¹) := by group
            _ = _ := by rw [hcz]
end Frame
section Setting
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem adj_of_twins
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {J J' : Subgroup G}
    (hJ : J ∈ twinSet Ω K) (hJ' : J' ∈ twinSet Ω K) (hne : J' ≠ J) : J' ∈ omegaNbr Ω J := by
  have h1 : KPerp Ω J = twinSet Ω J := Q3T8.Asc77.T7S22.perp_of_twin h hJ
  have h2 : twinSet Ω J = twinSet Ω K := twinSet_eq_of_mem_twinSet h.hz hJ
  have h3 : J' ∈ KPerp Ω J := by rw [h1, h2]; exact hJ'
  rcases h3 with rfl | h3
  · exact absurd rfl hne
  · exact h3

theorem exists_sylow_quad
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃) :
    ∃ R₁ R₂ R₃ R₄ : Subgroup G, IsSylow2In R₁ K ∧ IsSylow2In R₂ K' ∧ IsSylow2In R₃ K₃ ∧
      IsSylow2In R₄ K₄ ∧ u₁ ∈ R₁ ∧ u₂ ∈ R₂ ∧ Commutes R₁ R₂ ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ ∧
      Commutes R₁ R₄ ∧ Commutes R₂ R₄ ∧ Commutes R₃ R₄ := by
  obtain ⟨R₁, R₂, R₃, h1, h2, h3, hu₁, hu₂, -, c12, c13, c23⟩ := Q3T8.Asc77.T7B.exists_sylow_triple
      h
  have hΩ : Q3T8.Asc77.HypOmegaMod Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hK' : K' ∈ Ω := h.std.hK'.1
  have hK₃ : K₃ ∈ Ω := h.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz := h.std.hz
  have hz' := h.hzK'
  have hz₃ := h.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have nK : K ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₄Ω h41.symm hz hz₄
  have nK' : K' ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₄Ω h42.symm hz' hz₄
  have nK₃ : K₃ ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK₃ hK₄Ω h43.symm hz₃ hz₄
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes c12.symm)
  have hP : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) :=
    hP12.to_sup_of_normal_right' h3.2.1 (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  have hPN : (R₁ ⊔ R₂) ⊔ R₃ ≤ Subgroup.normalizer (K₄ : Set G) :=
    sup_le (sup_le (h1.1.trans nK) (h2.1.trans nK')) (h3.1.trans nK₃)
  obtain ⟨R₄, h4, hQ⟩ := exists_isPGroup_sup_sylow hP hPN
  have hR₁Q : R₁ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hR₂Q : R₂ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hR₃Q : R₃ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_right.trans le_sup_left
  have hR₄Q : R₄ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_right
  refine ⟨R₁, R₂, R₃, R₄, h1, h2, h3, h4, hu₁, hu₂, c12, c13, c23, ?_, ?_, ?_⟩
  · exact hΩ.commutes_of_twin_of_isPGroup hK hK₄Ω h41.symm hz hz₄ h1.1 h4.1
      (hQ.to_le (sup_le hR₁Q hR₄Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK' hK₄Ω h42.symm hz' hz₄ h2.1 h4.1
      (hQ.to_le (sup_le hR₂Q hR₄Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK₃ hK₄Ω h43.symm hz₃ hz₄ h3.1 h4.1
      (hQ.to_le (sup_le hR₃Q hR₄Q))

theorem not_dbarConnected_of_wyl
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (ρ₀ : Rep Ω W) (hρ₀ : ρ₀.K = K) (hμ : MuIsoWylD4 Ω W) :
    ¬ DbarConnected Ω W := by
  intro hconn
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand h.stand hW
  have hover : ∀ ρ : Rep Ω W, ρ.K ∈ twinSet Ω K := by
    intro ρ
    have := c.mem_dComp_of_connected hconn h.stand.mem ρ.hK ρ₀.hR ρ.hR (hρ₀ ▸ ρ₀.hRK) ρ.hRK
    exact Q3T8.Asc77.T7S22.dComp_subset_twinSet h this
  have hcomm : ∀ x ∈ muDelta Ω W, ∀ y ∈ muDelta Ω W, x * y = y * x := by
    intro x hx y hy
    obtain ⟨ρ, hρ⟩ := exists_rep_of_mem_muDelta hx
    obtain ⟨σ, hσ⟩ := exists_rep_of_mem_muDelta hy
    apply Subtype.ext
    show (x : NQuot (W ⊔ OCW W)) * y = y * x
    rw [← hρ, ← hσ]
    by_cases hK : σ.K = ρ.K
    · rw [c.img_eq_of_K_eq σ ρ hK]
    · exact c.comm_of_omega ρ σ (Q3T8.Asc77.T7V.adj_of_twins h (hover ρ) (hover σ) hK)
  have hcenter : ∀ y ∈ muDelta Ω W, ∀ x : ↥(muGroup Ω W), x * y = y * x := by
    intro y hy x
    have hx : x ∈ Subgroup.closure (muDelta Ω W) := by
      rw [closure_muDelta_eq_top]; trivial
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hcomm x hx y hy
    | one => simp
    | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    | inv a _ ha =>
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [ha]
        _ = y * a⁻¹ := by group
  have habel : ∀ x y : ↥(muGroup Ω W), x * y = y * x := by
    intro x y
    have hy : y ∈ Subgroup.closure (muDelta Ω W) := by
      rw [closure_muDelta_eq_top]; trivial
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hcenter y hy x
    | one => simp
    | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
    | inv a _ ha =>
      calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
        _ = a⁻¹ * (x * a) * a⁻¹ := by rw [ha]
        _ = a⁻¹ * x := by group
  obtain ⟨e⟩ := hμ
  apply s26_coxeterD4_not_comm
  intro u v
  have h1 := habel (e.symm u) (e.symm v)
  calc u * v = e (e.symm u * e.symm v) := by simp
    _ = e (e.symm v * e.symm u) := by rw [h1]
    _ = v * u := by simp

theorem fuseFrame_w
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃)
    (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) :
    ∃ a a' : G, a ∈ K ∧ a' ∈ K' ∧ orderOf a = 4 ∧ orderOf a' = 4 ∧ a * a' = a' * a ∧
      Q3T8.Asc77.T7V.FuseFrame K₃ K₄ z (a * a') := by
  classical
  have hs := h.setting
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃ : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := hs.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  obtain ⟨R₁, R₂, R₃, R₄, h1, h2, h3, h4, hu₁, hu₂, c12, c13, c23, c14, c24, c34⟩ :=
    Q3T8.Asc77.T7V.exists_sylow_quad h hK₄ h41 h42 h43
  
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes c12.symm)
  have hP123 : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) :=
    hP12.to_sup_of_normal_right' h3.2.1 (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  have hP : IsPGroup 2 ↥(((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄) :=
    hP123.to_sup_of_normal_right' h4.2.1 (sup_le (sup_le
      (T7A.le_normalizer_of_commutes c14.symm) (T7A.le_normalizer_of_commutes c24.symm))
      (T7A.le_normalizer_of_commutes c34.symm))
  obtain ⟨W, hW, hWD⟩ := Q3T8.Asc77.exists_W_of_isPGroup (Q3T7.modU_toGen3 hΩ) hP
  have hD₁ : R₁ ∈ DSet Ω W := hWD R₁ (mem_RSet_of_isSylow2In hK h1)
    (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hD₂ : R₂ ∈ DSet Ω W := hWD R₂ (mem_RSet_of_isSylow2In hK' h2)
    (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hD₃ : R₃ ∈ DSet Ω W := hWD R₃ (mem_RSet_of_isSylow2In hK₃ h3)
    (le_sup_right.trans le_sup_left)
  have hD₄ : R₄ ∈ DSet Ω W := hWD R₄ (mem_RSet_of_isSylow2In hK₄Ω h4) le_sup_right
  obtain ⟨ρ₀, hρ₀K, hρ₀R⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK h1 hD₁
  obtain ⟨ρ₁, hρ₁K, hρ₁R⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK' h2 hD₂
  obtain ⟨ρ₂, hρ₂K, hρ₂R⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK₃ h3 hD₃
  obtain ⟨ρ₃, hρ₃K, hρ₃R⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK₄Ω h4
      hD₄
  let ρ : Fin 4 → Rep Ω W := ![ρ₀, ρ₁, ρ₂, ρ₃]
  have hρK : ∀ i, (ρ i).K = ![K, K', K₃, K₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀K, hρ₁K, hρ₂K, hρ₃K]
  have hρR : ∀ i, (ρ i).R = ![R₁, R₂, R₃, R₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀R, hρ₁R, hρ₂R, hρ₃R]
  have hTw : ∀ i, ![K, K', K₃, K₄] i ∈ twinSet Ω K := by
    intro i
    fin_cases i
    · exact mem_twinSet_self hK hz
    · exact hs.hK'
    · exact hs.hK₃
    · exact hK₄
  have hzρ : ∀ i, IsUniqueInvolution (ρ i).K z := by
    intro i
    rw [hρK i]
    fin_cases i
    · exact hz
    · exact hz'
    · exact hz₃
    · exact hz₄
  have hKK' : K ≠ K' := hs.hne.symm
  have hKK₃ : K ≠ K₃ := hs.hK₃K.symm
  have hKK₄ : K ≠ K₄ := h41.symm
  have hK'K₃ : K' ≠ K₃ := hs.hK₃K'.symm
  have hK'K₄ : K' ≠ K₄ := h42.symm
  have hK₃K₄ : K₃ ≠ K₄ := h43.symm
  have hneK : ∀ i j : Fin 4, i ≠ j → ![K, K', K₃, K₄] i ≠ ![K, K', K₃, K₄] j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hKK', hKK'.symm, hKK₃, hKK₃.symm, hKK₄, hKK₄.symm,
      hK'K₃, hK'K₃.symm, hK'K₄, hK'K₄.symm, hK₃K₄, hK₃K₄.symm] at hij ⊢
  have hneρ : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact hneK i j hij
  have hnbrρ : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact Q3T8.Asc77.T7V.adj_of_twins hs (hTw i) (hTw j) (hneK j i (Ne.symm hij))
  have hnc : ¬ DbarConnected Ω W :=
    Q3T8.Asc77.T7V.not_dbarConnected_of_wyl hs hW ρ₀ hρ₀K (hμ W hW)
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hs.stand hW
  obtain ⟨σ, t, g, ht, hfar, hg, hrel, hR⟩ := c.fuse_frame hs.stand.cls hnc ρ hzρ hneρ hnbrρ
  have hρ0K : (ρ 0).K = K := hρ₀K
  have hρ1K : (ρ 1).K = K' := hρ₁K
  have hρ2K : (ρ 2).K = K₃ := hρ₂K
  have hρ3K : (ρ 3).K = K₄ := hρ₃K
  have hρ0R : (ρ 0).R = R₁ := hρ₀R
  have hρ1R : (ρ 1).R = R₂ := hρ₁R
  have hρ2R : (ρ 2).R = R₃ := hρ₂R
  have hρ3R : (ρ 3).R = R₄ := hρ₃R
  have hgW : ∀ i, g i ∈ W := fun i => (hg i).1.2
  have hgR : ∀ i, g i ∈ (ρ i).R := by
    intro i
    have h1 := (Q3CL.Thompson.inf_W_of_mem_D hΩ hW (ρ i).hR (ρ i).hK (ρ i).hRK).1
    have hmem : g i ∈ (ρ i).R ⊓ W := by rw [h1]; exact (hg i).1
    exact hmem.1
  have hgsq : ∀ i, g i * g i = z := fun i =>
    sq_eq_involution_of_orderOf_four (hzρ i) (hg i).1.1 (hg i).2
  have hzW : z ∈ W := c.mem_W_of_isUniqueInvolution (ρ 0) (hzρ 0)
  have htW : t ∈ W := c.mem_W_of_isUniqueInvolution σ ht
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  have hu0W : g 0 * g 1 ∈ W := W.mul_mem (hgW 0) (hgW 1)
  have hu2 : (g 0 * g 1) * (g 0 * g 1) = 1 := by
    calc (g 0 * g 1) * (g 0 * g 1) = (g 0 * g 0) * (g 1 * g 1) := by
          rw [mul_assoc, ← mul_assoc (g 1), ← hcomm _ (hgW 0) _ (hgW 1)]; group
      _ = 1 := by rw [hgsq 0, hgsq 1]; exact (hzρ 0).sq
  have hc2 : IsPGroup 2 (Subgroup.zpowers (g 0 * g 1)) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2
  have hg0R₁ : g 0 ∈ R₁ := by simpa [hρ0R] using hgR 0
  have hg1R₂ : g 1 ∈ R₂ := by simpa [hρ1R] using hgR 1
  have hR₃C : R₃ ≤ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g 0 * g 1) = (x * g 0) * g 1 := by group
      _ = (g 0 * x) * g 1 := by rw [c13 (g 0) hg0R₁ x hx]
      _ = g 0 * (x * g 1) := by group
      _ = g 0 * (g 1 * x) := by rw [c23 (g 1) hg1R₂ x hx]
      _ = (g 0 * g 1) * x := by group
  have hR₄C : R₄ ≤ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g 0 * g 1) = (x * g 0) * g 1 := by group
      _ = (g 0 * x) * g 1 := by rw [c14 (g 0) hg0R₁ x hx]
      _ = g 0 * (x * g 1) := by group
      _ = g 0 * (g 1 * x) := by rw [c24 (g 1) hg1R₂ x hx]
      _ = (g 0 * g 1) * x := by group
  have hcK₃ : g 0 * g 1 ∈ trivialOnQuot K₃ :=
    (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hc2 hK₃).mpr ⟨R₃, h3, hR₃C⟩
  have hcK₄ : g 0 * g 1 ∈ trivialOnQuot K₄ :=
    (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hc2 hK₄Ω).mpr ⟨R₄, h4, hR₄C⟩
  have hex₃ : IsSylow2In R₃ (Q3T8.Asc77.ExactLayer.exactCore (g 0 * g 1) K₃) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2 hK₃ hcK₃).mpr ⟨h3, hR₃C⟩
  have hex₄ : IsSylow2In R₄ (Q3T8.Asc77.ExactLayer.exactCore (g 0 * g 1) K₄) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2 hK₄Ω hcK₄).mpr ⟨h4, hR₄C⟩
  have hg2R₃ : g 2 ∈ R₃ := by simpa [hρ2R] using hgR 2
  have hg3R₄ : g 3 ∈ R₄ := by simpa [hρ3R] using hgR 3
  
  obtain ⟨y, hy⟩ : ∃ y : G, y = (ρ 2).r * σ.r * (ρ 2).r⁻¹ := ⟨_, rfl⟩
  have hr₂R : (ρ 2).r ∈ R₃ := by simpa [hρ2R] using (ρ 2).hr
  have hyC : y ∈ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hR₃C hr₂R) (hR σ.hr))
      (Subgroup.inv_mem _ (hR₃C hr₂R))
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ρ 2).r_mem_normalizer σ.r_mem_normalizer)
      (Subgroup.inv_mem _ (ρ 2).r_mem_normalizer)
  have hbr := c.conjRep_braid hs.stand.cls (ρ 2) σ (Ne.symm (hfar 2)) (hy ▸ hyN)
  have hKy : conjSub y K₃ = σ.K := by
    have h1 := c.K_eq_of_img_eq (Q3T8.Asc77.T7D.conjRep c.hΩ (hy ▸ hyN) (ρ 2)) σ hbr
    rw [hy, ← hρ2K]
    exact h1
  have hyz : y * z * y⁻¹ = t := by
    have h1 : IsUniqueInvolution (conjSub y K₃) (y * z * y⁻¹) := hz₃.conj y
    rw [hKy] at h1
    exact h1.eq ht
  have htz : t ≠ z := by
    intro h'
    have hσK : σ.K ∈ twinSet Ω K := ⟨σ.hK, z, hz, h' ▸ ht⟩
    have hperp : σ.K ∈ KPerp Ω K := by rw [hs.perp]; exact hσK
    rcases hperp with h'' | h''
    · exact hfar 0 (by rw [c.img_eq_of_K_eq σ (ρ 0) (h''.trans hρ0K.symm)])
    · exact hfar 0 (c.comm_of_omega (ρ 0) σ (by rw [hρ0K]; exact h'')).symm
  have hperm : g 0 * g 1 * g 2 * g 3 = g 2 * g 3 * (g 0 * g 1) := by
    calc g 0 * g 1 * g 2 * g 3 = (g 0 * g 1) * (g 2 * g 3) := by group
      _ = (g 2 * g 3) * (g 0 * g 1) := hcomm _ hu0W _ (W.mul_mem (hgW 2) (hgW 3))
  refine ⟨g 0, g 1, by simpa [hρ0K] using (hg 0).1.1, by simpa [hρ1K] using (hg 1).1.1,
    (hg 0).2, (hg 1).2, hcomm _ (hgW 0) _ (hgW 1), ?_⟩
  refine ⟨R₃, R₄, g 2, g 3, y, hex₃, hex₄, c34, hex₃.1 hg2R₃, hex₄.1 hg3R₄, hgsq 2, hgsq 3,
    hyC, ?_, ?_, ?_⟩
  · rw [hyz, hrel, hperm]
  · rw [← hperm, ← hrel]
    exact htz
  · exact hcomm _ hzW _ (W.mul_mem (W.mul_mem (hgW 2) (hgW 3)) hu0W)

theorem hyp22Fuse_of_c22_4
    (hμ : Q3T8.Asc77.C22_4) : Q3T8.Asc77.Hyp22Fuse := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h K₄ hK₄ h41 h42 h43
  have hs := h.setting
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃ : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := hs.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  obtain ⟨a, a', ha, ha', ha4, ha'4, haa', hF⟩ :=
    Q3T8.Asc77.T7V.fuseFrame_w h hK₄ h41 h42 h43 (hμ G Ω K K' K₃ z u₁ u₂ u₃ h)
  have hKK' : K ≤ trivialOnQuot K' := Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK hK' hs.hne.symm hz
      hz'
  have hK'K : K' ≤ trivialOnQuot K := Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK' hK hs.hne hz' hz
  obtain ⟨c, hc, hconj⟩ := Q3T8.Asc77.T7V.exists_conj_pair hΩ hK hK' hs.hne.symm hz hz' hKK' hK'K
      ha ha'
    hs.hu₁.1 hs.hu₂.1 ha4 ha'4 hs.hu₁.2 hs.hu₂.2 haa' hs.comm₁₂
  have nK₃ : K ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₃ hs.hK₃K.symm hz hz₃
  have nK₃' : K' ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₃ hs.hK₃K'.symm hz' hz₃
  have nK₄ : K ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₄Ω h41.symm hz hz₄
  have nK₄' : K' ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₄Ω h42.symm hz' hz₄
  have hc₃ : conjSub c K₃ = K₃ := mem_normalizer_iff_conjSub_eq.mp (sup_le nK₃ nK₃' hc)
  have hc₄ : conjSub c K₄ = K₄ := mem_normalizer_iff_conjSub_eq.mp (sup_le nK₄ nK₄' hc)
  have hcz : c * z * c⁻¹ = z := by
    have hle : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz.commute_of_mem hx).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz'.commute_of_mem hx).symm
    have h1 : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp (hle hc)
    rw [h1]
    group
  have := hF.conj hc₃ hc₄ hcz
  rw [hconj] at this
  exact this
end Setting
end T7V
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G
set_option linter.unusedSectionVars false
section Setting
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem exists_conj_of_far
    (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hzW : z ∈ W) {J : Subgroup G} (hJ : J ∈ Ω) (hJt : J ∉ twinSet Ω K)
    {w : G} (hw : IsUniqueInvolution J w) (hwW : w ∈ W) :
    ∃ y ∈ genGroup Ω K (u₁ * u₂), y * z * y⁻¹ = w := by
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := hs.hzK'
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hs.stand hW
  obtain ⟨ρ₀, hρ₀⟩ := c.exists_rep_of_involution_mem hs.stand.cls hK hz hzW
  obtain ⟨ρ₁, hρ₁⟩ := c.exists_rep_of_involution_mem hs.stand.cls hK' hz' hzW
  obtain ⟨σ, hσ⟩ := c.exists_rep_of_involution_mem hs.stand.cls hJ hw hwW
  have hKtw : K ∈ twinSet Ω K := mem_twinSet_self hK hz
  have hJK : J ≠ K := fun h => hJt (h ▸ hKtw)
  have hJK' : J ≠ K' := fun h => hJt (h ▸ hs.hK')
  have hJnot : J ∉ omegaNbr Ω K := by
    intro h
    have h1 : J ∈ KPerp Ω K := Set.mem_insert_of_mem _ h
    rw [hs.perp] at h1
    exact hJt h1
  have hKnot : K ∉ omegaNbr Ω J := fun h =>
    hJnot (Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΩ hJ hK h)
  have hz₀ : IsUniqueInvolution ρ₀.K z := hρ₀ ▸ hz
  have hz₁ : IsUniqueInvolution ρ₁.K z := hρ₁ ▸ hz'
  have hw' : IsUniqueInvolution σ.K w := hσ ▸ hw
  have hσ₀ : σ.K ≠ ρ₀.K := by rw [hσ, hρ₀]; exact hJK
  have hσ₁ : σ.K ≠ ρ₁.K := by rw [hσ, hρ₁]; exact hJK'
  have hn₀ : ρ₀.K ∉ omegaNbr Ω σ.K := by rw [hσ, hρ₀]; exact hKnot
  have hn₀' : σ.K ∉ omegaNbr Ω ρ₀.K := by rw [hσ, hρ₀]; exact hJnot
  obtain ⟨g₀, hg₀, ho₀⟩ := Q3T8.Asc77.C22G.exists_orderOf_four_mem_inf_W c ρ₀
  obtain ⟨g₁, hg₁, ho₁⟩ := Q3T8.Asc77.C22G.exists_orderOf_four_mem_inf_W c ρ₁
  obtain ⟨g₁', hg₁', ho₁', hRC⟩ :=
    Q3T8.Asc77.C22G.exists_centralized_pair c ρ₀ ρ₁ σ hz₀ hz₁ hw' hσ₀ hσ₁ hn₀ hg₀ ho₀ hg₁ ho₁
  
  have hg₀K : g₀ ∈ K := hρ₀ ▸ hg₀.1
  have hg₁K' : g₁' ∈ K' := hρ₁ ▸ hg₁'.1
  have hcomm : g₀ * g₁' = g₁' * g₀ := c.comm_W g₀ hg₀.2 g₁' hg₁'.2
  have hKK' : K ≤ trivialOnQuot K' := Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK hK' hs.hne.symm hz
      hz'
  have hK'K : K' ≤ trivialOnQuot K := Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK' hK hs.hne hz' hz
  obtain ⟨c₁, hc₁, hconj⟩ := Q3T8.Asc77.T7V.exists_conj_pair hΩ hK hK' hs.hne.symm hz hz' hKK' hK'K
    hg₀K hg₁K' hs.hu₁.1 hs.hu₂.1 ho₀ ho₁' hs.hu₁.2 hs.hu₂.2 hcomm hs.comm₁₂
  have hKA : K ≤ genGroup Ω K (u₁ * u₂) := le_genGroup_of_mem_twinSet hKtw
  have hK'A : K' ≤ genGroup Ω K (u₁ * u₂) := le_genGroup_of_mem_twinSet hs.hK'
  have hc₁A : c₁ ∈ genGroup Ω K (u₁ * u₂) := (sup_le hKA hK'A) hc₁
  have hLayer : rLayer Ω (g₀ * g₁') ≤ genGroup Ω K (u₁ * u₂) :=
    rLayer_le_of_conj hΩ.conjInvariant hc₁A hconj (rLayer_le_genGroup K (u₁ * u₂))
  have hσR : σ.R ≤ rLayer Ω (g₀ * g₁') :=
    le_rLayer_of_le_centralizer (mem_RSet_of_isSylow2In σ.hK σ.hRK) hRC
  have hσrA : σ.r ∈ genGroup Ω K (u₁ * u₂) := hLayer (hσR σ.hr)
  have hρrA : ρ₀.r ∈ genGroup Ω K (u₁ * u₂) := by
    have : ρ₀.r ∈ K := hρ₀ ▸ ρ₀.hRK.1 ρ₀.hr
    exact hKA this
  refine ⟨ρ₀.r * σ.r, (genGroup Ω K (u₁ * u₂)).mul_mem hρrA hσrA, ?_⟩
  
  have hτz : σ.r * z * σ.r⁻¹ = w * z := c.conj_involution σ ρ₀ hσ₀ hn₀ hw' hz₀
  have hτ' : ρ₀.r * w * ρ₀.r⁻¹ = z * w :=
    c.conj_involution ρ₀ σ (Ne.symm hσ₀) hn₀' hz₀ hw'
  have hr₀z : ρ₀.r * z * ρ₀.r⁻¹ = z := by
    have hn : conjSub ρ₀.r ρ₀.K = ρ₀.K := conjSub_eq_self_of_mem (ρ₀.hRK.1 ρ₀.hr)
    exact hz₀.conj_eq hn
  have hzw : z * w = w * z := c.comm_W z hzW w hwW
  have e : (ρ₀.r * σ.r) * z * (ρ₀.r * σ.r)⁻¹ = ρ₀.r * (σ.r * z * σ.r⁻¹) * ρ₀.r⁻¹ := by group
  rw [e, hτz]
  calc ρ₀.r * (w * z) * ρ₀.r⁻¹ = (ρ₀.r * w * ρ₀.r⁻¹) * (ρ₀.r * z * ρ₀.r⁻¹) := by group
    _ = (z * w) * z := by rw [hτ', hr₀z]
    _ = w := by rw [hzw, mul_assoc, hz.sq, mul_one]
end Setting
end C22G
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S22
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
section Lift
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exactImg_star_lift
    (hΩ : Q3T7M.HM Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K J : Subgroup G}
    (hK : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c) (hJ : J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c)
    (h : Q3T8.Asc77.T7H.exactImg Ω c J ∈
      omegaStarNbr (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c))
          (Q3T8.Asc77.T7H.exactImg Ω c K)) :
    ∃ n : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c), n ∈ classicalInvolutionOddCore
        ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c) ∧
      J ∈ omegaStarNbr Ω (conjSub (n : G) K) := by
  set Y := Q3T8.Asc77.ExactLayer.exactLayer Ω c with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : Q3T7M.HM (Q3T8.Asc77.ExactLayer.exactPair Ω c) :=
    Q3T8.Asc77.ExactLayer.hypOmegaMod_exactPair hΩ hc2
  have hΛ' : Q3T7M.HM (quotFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c) N₀) :=
    Q3T8.Asc77.oddQuotHyp ↥Y (Q3T8.Asc77.ExactLayer.exactPair Ω c) hΛ N₀ hN₀odd
  have hKY : (Q3T8.Asc77.ExactLayer.exactCore c K).subgroupOf Y ∈
      Q3T8.Asc77.ExactLayer.exactPair Ω c :=
    ⟨Q3T8.Asc77.ExactLayer.exactCore c K, Q3T8.Asc77.ExactLayer.exactCore_mem_exactFamily hK,
      Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK, rfl⟩
  have hJY : (Q3T8.Asc77.ExactLayer.exactCore c J).subgroupOf Y ∈
      Q3T8.Asc77.ExactLayer.exactPair Ω c :=
    ⟨Q3T8.Asc77.ExactLayer.exactCore c J, Q3T8.Asc77.ExactLayer.exactCore_mem_exactFamily hJ,
      Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hJ, rfl⟩
  obtain ⟨n, hn, hnb⟩ := Q3T8.Asc77.exists_conj_omegaStarNbr hΛ hΛ' hN₀odd hKY hJY h
  refine ⟨n, hn, ?_⟩
  have hnc : (n : G) * c * (n : G)⁻¹ = c := Q3T8.Asc77.T7H.mem_centralizer_of_mem_exactLayer
  have hncent : (n : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω c n.2
  rw [conjSub_subgroupOf] at hnb
  have hK'Y : conjSub (n : G) (Q3T8.Asc77.ExactLayer.exactCore c K) ≤ Y := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : (n : G)⁻¹ * x * (n : G) ∈ Y := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK hx
    have h2 := Y.mul_mem (Y.mul_mem n.2 h1) (Y.inv_mem n.2)
    simpa [mul_assoc] using h2
  have hJ'Y : Q3T8.Asc77.ExactLayer.exactCore c J ≤ Y :=
    Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hJ
  have h3 : Q3T8.Asc77.ExactLayer.exactCore c J ∈
      omegaStarNbr (Q3T8.Asc77.ExactLayer.exactFamily Ω c)
      (conjSub (n : G) (Q3T8.Asc77.ExactLayer.exactCore c K)) :=
    omegaStarNbr_of_restrict hK'Y hJ'Y hnb
  have hK'' : conjSub (n : G) K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hncent hK
  have h4 : Q3T8.Asc77.ExactLayer.exactCore c (conjSub (n : G) K) =
      conjSub (n : G) (Q3T8.Asc77.ExactLayer.exactCore c K) := by
    have := Q3T8.Asc77.ExactLayer.exactCore_conjSub (n : G) c K
    rwa [hnc] at this
  exact Q3T7.mem_omegaStarNbr_of_exactFamily3 hΩ hc2 hK'' hJ
    (by
      rw [show Q3NL.exactCore3 c (conjSub (n : G) K) =
        conjSub (n : G) (Q3NL.exactCore3 c K) from h4]
      exact h3)

theorem hstar_layer
    (hΩ : Q3T7M.HM Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hA : ∀ M ∈ Ω, ∀ J ∈ omegaStarNbr Ω M, ∃ w, IsUniqueInvolution M w ∧ IsUniqueInvolution J w) :
    ∀ B ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c), ∀ J ∈ oddQuotientFamily
        (Q3T8.Asc77.ExactLayer.exactPair Ω c),
      J ∈ omegaStarNbr (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)) B →
        ∃ w, IsUniqueInvolution B w ∧ IsUniqueInvolution J w := by
  intro B hB J hJ hnb
  obtain ⟨B₀, hB₀, rfl⟩ := Q3T8.Asc77.T7H.exists_exactImg_of_mem hB
  obtain ⟨J₀, hJ₀, rfl⟩ := Q3T8.Asc77.T7H.exists_exactImg_of_mem hJ
  obtain ⟨n, hn, hnb'⟩ := Q3T8.Asc77.S22.exactImg_star_lift hΩ hc2 hB₀ hJ₀ hnb
  have hncent : (n : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω c n.2
  have hnc : (n : G) * c * (n : G)⁻¹ = c := Q3T8.Asc77.T7H.mem_centralizer_of_mem_exactLayer
  have hBn : conjSub (n : G) B₀ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hncent hB₀
  obtain ⟨w, hw1, hw2⟩ := hA _ (hΩ.conjInvariant (n : G) B₀ hB₀.1) J₀ hnb'
  have hwc : w ∈ Q3T8.Asc77.ExactLayer.exactCore c (conjSub (n : G) B₀) :=
    (Q3T8.Asc77.T7H.isUniqueInvolution_exactCore hΩ hc2 hBn hw1).mem
  have hwY : w ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω c :=
      Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hBn hwc
  refine ⟨Q3T8.Asc77.T7H.toBar Ω c w hwY, ?_, Q3T8.Asc77.T7H.exactImg_isUnique hΩ hc2 hJ₀ hw2 hwY⟩
  rw [← Q3T8.Asc77.T7H.exactImg_conjSub_odd hn hnc (K := B₀)]
  exact Q3T8.Asc77.T7H.exactImg_isUnique hΩ hc2 hBn hw1 hwY
end Lift
section Section
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem layer_section (hΩ : Q3T7M.HM Ω)
    (hAΩ : ∀ M ∈ Ω, AEmpty Ω M) {u : G} (hu2 : u * u = 1)
    (hnc : ¬ ({u} : Set G) ⊆ Subgroup.center G) :
    Q3T8.Asc77.GenSection (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u)) ∧
      Nat.card (↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) ⧸ classicalInvolutionOddCore
          ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u)) <
        Nat.card G := by
  classical
  have hcpg : IsPGroup 2 (Subgroup.zpowers u) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2
  set Y := Q3T8.Asc77.ExactLayer.exactLayer Ω u with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : Q3T7M.HM (Q3T8.Asc77.ExactLayer.exactPair Ω u) :=
      Q3T8.Asc77.ExactLayer.hypOmegaMod_exactPair hΩ hcpg
  have hΦ : Q3T7M.HM (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u)) :=
    Q3T8.Asc77.oddQuotHyp ↥Y (Q3T8.Asc77.ExactLayer.exactPair Ω u) hΛ N₀ hN₀odd
  have hgen : omegaGen (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u)) = ⊤ :=
    omegaGen_quotFamily_eq_top (Q3T8.Asc77.ExactLayer.exactPair Ω u) N₀
      (omegaGen_restrictFamily_eq_top (Q3T8.Asc77.ExactLayer.exactFamily Ω u) Y
          (Q3T8.Asc77.ExactLayer.exactLayer_eq_iSup Ω u).symm)
  have hAΛ : ∀ L ∈ Q3T8.Asc77.ExactLayer.exactPair Ω u, AEmpty (Q3T8.Asc77.ExactLayer.exactPair Ω
      u) L := by
    have h0 := Q3T8.Asc77.aEmpty_exactPair hΩ hAΩ hcpg
    have e0 : centralizingMembers (Q3T8.Asc77.ExactLayer.exactFamily Ω u) {u} =
        Q3T8.Asc77.ExactLayer.exactFamily Ω u :=
      Q3T8.Asc77.ExactLayer.centMembers_exactFamily Ω u
    rw [e0] at h0
    exact h0
  have hAΦ : ∀ L ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u),
      AEmpty (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u)) L :=
    Q3T8.Asc77.aEmpty_quotFamily hΛ hΦ hN₀odd hAΛ
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    have h2 : Nat.card ↥Y < Nat.card G := Q3T8.Asc77.ExactLayer.card_exactLayer_lt hnc
    omega
  exact ⟨⟨hΦ, CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y, hgen, hAΦ⟩, hlt⟩
end Section
end S22
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8

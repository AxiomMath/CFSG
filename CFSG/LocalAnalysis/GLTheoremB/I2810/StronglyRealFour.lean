module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.StronglyRealAut
import CFSG.LocalAnalysis.GLTheoremB.I2810.StronglyRealInd
import CFSG.LocalAnalysis.GLTheoremB.I2810.StronglyRealPGL

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

namespace SRFour

open SRInd

section Generic
variable {G : Type*} [Group G]

theorem ker_conj_eq_center : (MulAut.conj : G →* MulAut G).ker = Subgroup.center G := by
  ext z
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun σ : MulAut G => σ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * z = (z * g * z⁻¹) * z := by rw [this]
      _ = z * g := by group
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h g]
    group

theorem card_range_conj : Nat.card (MulAut.conj : G →* MulAut G).range =
    Nat.card (G ⧸ Subgroup.center G) := by
  have e : (G ⧸ Subgroup.center G) ≃* (MulAut.conj : G →* MulAut G).range :=
    (QuotientGroup.quotientMulEquivOfEq ker_conj_eq_center.symm).trans
      (QuotientGroup.quotientKerEquivRange _)
  exact (Nat.card_congr e.toEquiv).symm

theorem conj_conj_aut (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  simp

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_perm] at h
  have h6 : Nat.card (Fin 6) = 6 := by simp
  have h720 : Nat.factorial 6 = 720 := by decide
  rw [h6, h720] at h
  omega

theorem card_centerQuot_of_hyp4 [Finite G]
    (h : Nonempty (G ≃* alternatingGroup (Fin 6)) ∨ IsHatSix G) :
    Nat.card (G ⧸ Subgroup.center G) = 360 := by
  rcases h with h | ⟨-, -, he⟩
  · obtain ⟨e⟩ := h
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    haveI : IsSimpleGroup G := MulEquiv.isSimpleGroup e
    have hcard : Nat.card G = 360 := (Nat.card_congr e.toEquiv).trans card_alt_six
    have hcen : Subgroup.center G = ⊥ := by
      rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        haveI : IsMulCommutative G :=
          ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm⟩⟩
        have := IsSimpleGroup.prime_card (α := G)
        rw [hcard] at this
        norm_num at this
    exact (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hcen).trans
      QuotientGroup.quotientBot).toEquiv).trans hcard
  · obtain ⟨e⟩ := he
    exact (Nat.card_congr e.toEquiv).trans card_alt_six

end Generic

section Setting
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem inn_le_P (W K S : Subgroup X) [W.Normal] :
    (MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range ≤
      inducedAutGroup (bar W K ⊔ bar W S) (bar W K) := by
  rintro _ ⟨g, rfl⟩
  have hgN : ((g : ↥(bar W K)) : X ⧸ W) ∈
      Subgroup.normalizer ((bar W K : Subgroup (X ⧸ W)) : Set (X ⧸ W)) :=
    Subgroup.le_normalizer g.2
  refine Subgroup.mem_map.2 ⟨⟨(g : X ⧸ W), hgN⟩,
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left g.2), ?_⟩
  exact MulEquiv.ext fun y => Subtype.ext rfl

theorem indAut_le_P (W K S : Subgroup X) [W.Normal] :
    indAut W K S ≤ inducedAutGroup (bar W K ⊔ bar W S) (bar W K) :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ le_sup_right)

theorem P_le_sup (hSN : S ≤ Subgroup.normalizer (K : Set X)) :
    inducedAutGroup (bar W K ⊔ bar W S) (bar W K) ≤
      (MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range ⊔ indAut W K S := by
  have hKN : bar W K ≤ Subgroup.normalizer ((bar W K : Subgroup (X ⧸ W)) : Set (X ⧸ W)) :=
    Subgroup.le_normalizer
  have hSN' : bar W S ≤ Subgroup.normalizer ((bar W K : Subgroup (X ⧸ W)) : Set (X ⧸ W)) := by
    rintro _ ⟨s, hs, rfl⟩
    exact mk_mem_normalizer_bar (hSN hs)
  have hle : (bar W K ⊔ bar W S).subgroupOf
      (Subgroup.normalizer ((bar W K : Subgroup (X ⧸ W)) : Set (X ⧸ W))) ≤
      ((MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range ⊔ indAut W K S).comap
        (bar W K).normalizerMonoidHom := by
    rw [Subgroup.subgroupOf_sup hKN hSN']
    refine sup_le ?_ ?_
    · rintro ⟨z, hz⟩ hzK
      have hzK' : z ∈ bar W K := Subgroup.mem_subgroupOf.1 hzK
      refine Subgroup.mem_sup_left ?_
      exact ⟨⟨z, hzK'⟩, MulEquiv.ext fun y => Subtype.ext rfl⟩
    · rintro ⟨z, hz⟩ hzS
      obtain ⟨s, hs, hsz⟩ := Subgroup.mem_subgroupOf.1 hzS
      refine Subgroup.mem_sup_right ?_
      refine (mem_indAut_iff' hSN _).2 ⟨⟨s, hSN hs⟩, hs, ?_⟩
      have : mkN W K ⟨s, hSN hs⟩ = ⟨z, hz⟩ := Subtype.ext hsz
      show (bar W K).normalizerMonoidHom (mkN W K ⟨s, hSN hs⟩) = _
      rw [this]
  intro p hp
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hp
  exact hle hy

theorem hyp4_inverts_five_aux (h : Setup28 W K S) (h4 : Hyp28Four W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) : Inverts W K a (fun m => m = 5) := by
  obtain ⟨hG, hindS, ⟨φP⟩⟩ := h4
  haveI : Finite (MulAut ↥(bar W K)) := SRAut.finite_mulAut _
  have haN : a ∈ Subgroup.normalizer (K : Set X) := h.hN haS
  let aN : ↥(Subgroup.normalizer (K : Set X)) := ⟨a, haN⟩
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut ↥(bar W K), α = indHom W K aN := ⟨_, rfl⟩
  have hαS : α ∈ indAut W K S := (mem_indAut_iff' h.hN α).2 ⟨aN, haS, hαdef.symm⟩
  have hα1 : α ≠ 1 := fun h1 => hna ⟨haS, (indHom_eq_one_iff aN).1 (hαdef ▸ h1)⟩
  have hαsq : α ^ 2 = 1 := by
    have := pow_card_eq_one' (G := ↥(indAut W K S)) (x := ⟨α, hαS⟩)
    rw [hindS] at this
    exact congrArg Subtype.val this
  have hQ : Nat.card (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) = 360 :=
    card_centerQuot_of_hyp4 hG
  have hInn : Nat.card (MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range = 360 :=
    card_range_conj.trans hQ
  have hP720 : Nat.card ↥(inducedAutGroup (bar W K ⊔ bar W S) (bar W K)) = 720 :=
    (Nat.card_congr φP.toEquiv).trans CFSG.QuasithinUnique.Out21.A6.card_pgl29
  have hInnP := inn_le_P W K S
  have hPle := P_le_sup (W := W) h.hN
  have hαP : α ∈ inducedAutGroup (bar W K ⊔ bar W S) (bar W K) := indAut_le_P W K S hαS
  have hnotInn : α ∉ (MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range := by
    intro hαI
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hindle : indAut W K S ≤ (MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range := by
      have hord : orderOf α = 2 := orderOf_eq_prime hαsq hα1
      have hz : Subgroup.zpowers α = indAut W K S := by
        refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hαS) ?_
        rw [hindS, Nat.card_zpowers, hord]
      rw [← hz]
      exact (Subgroup.zpowers_le).2 hαI
    have hle := Subgroup.card_le_of_le (hPle.trans (sup_le le_rfl hindle))
    omega
  have hHscard : Nat.card ↥((MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range.subgroupOf
      (inducedAutGroup (bar W K ⊔ bar W S) (bar W K))) = 360 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hInnP).toEquiv, hInn]
  have hHsidx : ((MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range.subgroupOf
      (inducedAutGroup (bar W K ⊔ bar W S) (bar W K))).index = 2 := by
    have := Subgroup.card_mul_index ((MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range.subgroupOf
      (inducedAutGroup (bar W K ⊔ bar W S) (bar W K)))
    rw [hHscard, hP720] at this
    omega
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup ↥CFSG.QuasithinUnique.A6Models.pgl29,
      H = ((MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range.subgroupOf
        (inducedAutGroup (bar W K ⊔ bar W S) (bar W K))).comap φP.symm.toMonoidHom :=
    ⟨_, rfl⟩
  have hHidx : H.index = 2 := by
    rw [hHdef]
    exact (Subgroup.index_comap_of_surjective _ (f := φP.symm.toMonoidHom)
      φP.symm.surjective).trans hHsidx
  have hF1a := PGLCheck.pgl29_index_two_eq_psl29_aux H hHidx
  have hmemH : ∀ g : ↥CFSG.QuasithinUnique.A6Models.pgl29, g ∈ H ↔
      ((φP.symm g : ↥(inducedAutGroup (bar W K ⊔ bar W S) (bar W K))) :
        MulAut ↥(bar W K)) ∈ (MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range := by
    intro g
    rw [hHdef, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rfl
  obtain ⟨y, hydef⟩ : ∃ y : ↥CFSG.QuasithinUnique.A6Models.pgl29, y = φP ⟨α, hαP⟩ := ⟨_, rfl⟩
  have hy2 : y * y = 1 := by
    rw [hydef, ← map_mul, ← map_one φP]
    congr 1
    exact Subtype.ext (by simpa [pow_two] using hαsq)
  have hyn : (y : Equiv.Perm (Fin 10)) ∉ CFSG.QuasithinUnique.A6Models.psl29 := by
    intro hy'
    have h1 := (hmemH y).1 ((hF1a y).2 hy')
    rw [hydef, MulEquiv.symm_apply_apply] at h1
    exact hnotInn h1
  obtain ⟨x, hx, hx5, hyx⟩ := PGLCheck.pgl29_outer_inverts_five_aux y.2
    (congrArg Subtype.val hy2) hyn
  have hxpgl : x ∈ CFSG.QuasithinUnique.A6Models.pgl29 :=
    CFSG.QuasithinUnique.Out21.A6.psl29_le_pgl29 hx
  obtain ⟨β, hβdef⟩ : ∃ β : ↥(inducedAutGroup (bar W K ⊔ bar W S) (bar W K)),
      β = φP.symm ⟨x, hxpgl⟩ := ⟨_, rfl⟩
  have hφβ : φP β = ⟨x, hxpgl⟩ := by rw [hβdef, MulEquiv.apply_symm_apply]
  have hβI : (β : MulAut ↥(bar W K)) ∈ (MulAut.conj : ↥(bar W K) →* MulAut ↥(bar W K)).range := by
    have := (hmemH ⟨x, hxpgl⟩).1 ((hF1a ⟨x, hxpgl⟩).2 hx)
    rwa [← hβdef] at this
  have hβord : orderOf (β : MulAut ↥(bar W K)) = 5 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective φP.toMonoidHom φP.injective β]
    show orderOf (φP β) = 5
    rw [hφβ, Subgroup.orderOf_mk x hxpgl]
    exact hx5
  have hrel : α * (β : MulAut ↥(bar W K)) * α⁻¹ = (β : MulAut ↥(bar W K))⁻¹ := by
    have h1 : (⟨α, hαP⟩ : ↥(inducedAutGroup (bar W K ⊔ bar W S) (bar W K))) * β *
        ⟨α, hαP⟩⁻¹ = β⁻¹ := by
      apply φP.injective
      rw [map_mul, map_mul, map_inv, map_inv, hφβ, ← hydef]
      exact Subtype.ext hyx
    exact congrArg Subtype.val h1
  obtain ⟨g, hg⟩ := hβI
  rw [← hg] at hrel hβord
  rw [conj_conj_aut] at hrel
  have hz : α g * g ∈ Subgroup.center ↥(bar W K) := by
    rw [← ker_conj_eq_center, MonoidHom.mem_ker, map_mul, hrel, inv_mul_cancel]
  have hq5 : orderOf (QuotientGroup.mk g : ↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) = 5 := by
    rw [← hβord, orderOf_eq_orderOf_iff]
    intro n
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← ker_conj_eq_center,
      MonoidHom.mem_ker, map_pow]
  obtain ⟨x₀, rfl⟩ := SRAut.toBar_surjective W K g
  refine ⟨x₀, ?_, hq5, ?_⟩
  · show Odd (orderOf (QuotientGroup.mk (toBar W K x₀) :
      ↥(bar W K) ⧸ Subgroup.center ↥(bar W K)))
    rw [hq5]
    decide
  · have hbxK : a * x₀ * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 haN x₀).1 x₀.2
    have hmemK : a * x₀ * a⁻¹ * x₀ ∈ K := K.mul_mem hbxK x₀.2
    refine (SRAut.mem_zPre_iff (W := W) (K := K) ⟨_, hmemK⟩).2 ?_
    have e1 : (⟨a * x₀ * a⁻¹ * x₀, hmemK⟩ : ↥K) = ⟨a * x₀ * a⁻¹, hbxK⟩ * x₀ := rfl
    rw [e1, map_mul]
    have e2 : toBar W K ⟨a * x₀ * a⁻¹, hbxK⟩ = α (toBar W K x₀) := by
      rw [hαdef]; rfl
    rw [e2]
    exact hz

end Setting

end SRFour

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

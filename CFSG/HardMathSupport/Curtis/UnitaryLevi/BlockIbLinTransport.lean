module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbGeneric
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeLinear

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open scoped commutatorElement

section Void

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

@[expose] def centralQuotientHom {X : Type} [Group X] (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) :
    ↥Lb →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Lb))

omit [Finite Y] in
theorem centralQuotientHom_surjective {X : Type} [Group X]
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) : Function.Surjective (centralQuotientHom e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite Y] in
theorem centralQuotientHom_ker {X : Type} [Group X] (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) :
    (centralQuotientHom e).ker = Subgroup.center ↥Lb := by
  ext g
  rw [MonoidHom.mem_ker, ← QuotientGroup.ker_mk' (Subgroup.center ↥Lb), MonoidHom.mem_ker]
  simp only [centralQuotientHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  exact ⟨fun h => e.injective (h.trans (map_one e).symm), fun h => by rw [h, map_one]⟩

theorem blockIb_false_of_perfect_centralizer (hP : BlockIbParab Lb Pb)
    (hD : BlockIbData Lb Pb D x) {X : Type} [Group X] (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X)
    (h : ∀ v : X, v ^ 3 = 1 → v ≠ 1 → ∃ W : Subgroup X, ⁅W, W⁆ = W ∧ W ≠ ⊥ ∧
      W ≤ Subgroup.centralizer ({v} : Set X)) : False := by
  obtain ⟨u, huP, hu3, huC, -, hfree⟩ := exists_inner_three hP hD
  have hPL : Pb ≤ Lb := hP.parab.1
  set l : ↥Lb := ⟨u, hPL huP⟩ with hl
  set ψ := centralQuotientHom e with hψ
  have hv3 : ψ l ^ 3 = 1 := by
    rw [← map_pow]
    have : l ^ 3 = 1 := Subtype.ext (by simpa [hl] using hu3)
    rw [this, map_one]
  have hv1 : ψ l ≠ 1 := by
    intro h1
    apply huC
    have hl' : l ∈ Subgroup.center ↥Lb := by
      rw [← centralQuotientHom_ker e]; exact h1
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.1 hl' ⟨g, hg⟩
    exact congrArg Subtype.val this
  obtain ⟨W, hW, hWne, hWc⟩ := h (ψ l) hv3 hv1
  obtain ⟨W', hW', hW'c, hdvd⟩ := Coordinator.exists_perfect_centralizer_dvd_of_central_quotient
    ψ (centralQuotientHom_surjective e) (centralQuotientHom_ker e).le hW hWc
  have hbot := hfree (W'.map Lb.subtype) (by rintro _ ⟨w, -, rfl⟩; exact w.2)
    (by rw [← Subgroup.map_commutator, hW'])
    (by
      rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.1 (hW'c hw)
      exact congrArg Subtype.val this)
  have hW'bot : W' = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have : (w : Y) ∈ W'.map Lb.subtype := ⟨w, hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  rw [hW'bot] at hdvd
  have h1 : Nat.card W = 1 := by
    have : Nat.card (⊥ : Subgroup ↥Lb) = 1 := Subgroup.card_bot
    rw [this] at hdvd
    exact Nat.dvd_one.1 hdvd
  exact hWne (Subgroup.eq_bot_of_card_eq W h1)

end Void

section Parab

theorem exists_sylow_normalizer_map {G X : Type*} [Group G] [Group X] [Finite G] (ψ : G →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center G)
    (hodd : Odd (Nat.card ψ.ker)) {J : Subgroup G}
    (hpar : ∃ T : Subgroup G, IsSylowTwoOf T ⊤ ∧ Subgroup.normalizer (T : Set G) ≤ J ∧
      J ≠ Subgroup.normalizer (T : Set G)) (htop : J ≠ ⊤) :
    ∃ S : Sylow 2 X, Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ J.map ψ ∧
      J.map ψ ≠ Subgroup.normalizer ((S : Subgroup X) : Set X) ∧ J.map ψ ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hNJ, hneB⟩ := hpar
  have hkJ : ψ.ker ≤ J :=
    hker.trans ((Subgroup.center_le_normalizer ((T : Subgroup G) : Set G)).trans hNJ)
  have hcomap : (J.map ψ).comap ψ = J := Subgroup.comap_map_eq_self hkJ
  have hidx : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
  let T' : Sylow 2 G := hT.2.1.toSylow hidx
  refine ⟨T'.mapSurjective hψ, ?_, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    exact ToralCensus.normalizer_map_le_map ψ hψ hker hodd hT.2.1 hNJ
  · rw [Sylow.coe_mapSurjective]
    intro hJe
    have hJe : J.map ψ = Subgroup.normalizer ((T.map ψ : Subgroup X) : Set X) := hJe
    apply hneB
    refine le_antisymm (fun x hx => ?_) hNJ
    have hmem : ψ x ∈ Subgroup.normalizer ((T.map ψ : Subgroup X) : Set X) := by
      rw [← hJe]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hyN, hyx⟩ := ToralCensus.normalizer_map_le_map ψ hψ hker hodd hT.2.1
      (le_refl (Subgroup.normalizer (T : Set G))) hmem
    have hxy : y⁻¹ * x ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have hzN : y⁻¹ * x ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.center_le_normalizer ((T : Subgroup G) : Set G)) (hker hxy)
    simpa using Subgroup.mul_mem _ hyN hzN
  · intro h
    apply htop
    rw [← hcomap, h, Subgroup.comap_top]

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

theorem exists_parab_X (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x)
    (hT : IsClassicalTwoOrG2 (↥Lb ⧸ Subgroup.center ↥Lb)) {X : Type} [Group X]
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) :
    ∃ S : Sylow 2 X, Subgroup.normalizer ((S : Subgroup X) : Set X) ≤
        (Pb.subgroupOf Lb).map (centralQuotientHom e) ∧
      (Pb.subgroupOf Lb).map (centralQuotientHom e) ≠
        Subgroup.normalizer ((S : Subgroup X) : Set X) ∧
      (Pb.subgroupOf Lb).map (centralQuotientHom e) ≠ ⊤ := by
  have hCP := compParab_of_blockIb hP hD hT
  obtain ⟨T, hT2, hNJ, hne⟩ := Coordinator.exists_sylow_normalizer_subgroupOf_of_compParab hCP
  refine exists_sylow_normalizer_map (centralQuotientHom e) (centralQuotientHom_surjective e)
    (centralQuotientHom_ker e).le (by rw [centralQuotientHom_ker e]; exact hP.odd)
    ⟨T, hT2, hNJ, hne⟩ ?_
  intro htop
  apply hP.ne
  refine le_antisymm hP.parab.1 fun y hy => ?_
  have := (Subgroup.eq_top_iff' _).1 htop ⟨y, hy⟩
  exact Subgroup.mem_subgroupOf.1 this

end Parab

end CFSG.HardMathSupport.Curtis.UnitaryLevi

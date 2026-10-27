module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Plane
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Bridge
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Dim

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

@[expose] def KD309LieOrderW : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (P : Sylow 5 Y) (x z : Y), Plane63 5 Y P x z →
    ∀ L : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf L ⊤ →
      (∀ K : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf K ⊤ → K = L) →
      I291P65.Is29a ↥L → (∃ ψ : (P : Subgroup Y) →* Wr, Function.Injective ψ) →
        Nat.card (P : Subgroup Y) ≤ 5 ^ 5

theorem kd309_of_lieW (hO : KD309LieOrderW) (hM : KD309LieMono) : I291P65.KD309 := by
  intro Y _ _ P x z hpl L hL hLu h29 V _ _ _ ρ hker
  by_contra hlt
  push Not at hlt
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  set Pg : Subgroup Y := (P : Subgroup Y) with hPg
  have hpP5 : IsPGroup 5 Pg := P.isPGroup'
  obtain ⟨hxP, hzP, hx5, hz5, hx1, hz1⟩ := I291P65.plane_facts hpl.prime hpl.plane
  have hzo : orderOf z = 5 := orderOf_eq_prime hz5 hz1
  have hzc : ∀ g ∈ Pg, g * z = z * g := fun g hg =>
    Subgroup.mem_centralizer_iff.mp hpl.z_central g hg
  have hZ : ∀ w ∈ Pg, (∀ g ∈ Pg, g * w = w * g) → w ^ 5 = 1 → w ∈ zpowers z :=
    fun w hw hc h5 => hpl.plane.center w hw (Subgroup.mem_centralizer_iff.mpr hc) h5
  set V₀ : Submodule (ZMod 2) V := LinearMap.range (ρ z - 1) with hV₀
  have hV₀inv : ∀ g ∈ Pg, ∀ v ∈ V₀, ρ g v ∈ V₀ := fun g hg v hv => range_invariant (hzc g hg) hv
  let ρ₀ : Representation (ZMod 2) ↥Pg ↥V₀ := restrictRep ρ Pg V₀ hV₀inv
  let σ : ↥Pg →* (↥V₀ ≃ₗ[ZMod 2] ↥V₀) := repEquiv ρ₀
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    refine Subtype.ext (faithful_on_range hker hpP5 hzP hzo hzc hZ a.2 fun v hv => ?_)
    have := LinearEquiv.congr_fun ha ⟨v, hv⟩
    exact congrArg Subtype.val this
  have hQnc : ∃ a b : ↥Pg, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hPC : Pg ≤ centralizer ({x} : Set Y) := by
      intro g hg
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hcon ⟨g, hg⟩ ⟨x, hxP⟩)
    have h1 := pRank_mono 5 (by norm_num) hPC
    have h2 : 4 ≤ Open.pRank 5 Pg := hpl.four_le
    have h3 := hpl.rank_centralizer
    omega
  have hdim20 : Module.finrank (ZMod 2) V₀ = 20 := by
    by_contra hne
    have hlt20 : Module.finrank (ZMod 2) V₀ < 20 := lt_of_le_of_ne hlt hne
    obtain ⟨a, b, hab⟩ := hQnc
    exact hab (commutative_of_finrank_lt hpP5 σ hσinj hlt20 a b)
  obtain ⟨τ, ψ, hψ, -⟩ := exists_model_embedding hpP5 σ hσinj hdim20
  have hcard5 : Nat.card Pg ≤ 5 ^ 5 := hO Y P x z hpl L hL hLu h29 ⟨ψ, hψ⟩
  have hcard5ge : 5 ^ 5 ≤ Nat.card Pg := by
    have h4Pg : 4 ≤ Open.pRank 5 Pg := hpl.four_le
    obtain ⟨E, hEP, hE, hEc⟩ := pRank_attained 5 Pg (by omega)
    have hElt : Nat.card E < Nat.card Pg := by
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hEP) fun h => ?_
      have hEeq : E = Pg := Subgroup.eq_of_le_of_card_ge hEP (le_of_eq h.symm)
      obtain ⟨a, b, hab⟩ := hQnc
      apply hab
      have hc := hE.1.is_comm.comm (⟨a, hEeq ▸ a.2⟩ : E) ⟨b, hEeq ▸ b.2⟩
      exact Subtype.ext (congrArg (fun t : ↥E => (t : Y)) hc)
    obtain ⟨k, hk⟩ := hpP5.exists_card_eq
    have h4 : 5 ^ 4 ≤ Nat.card E := by
      rw [hEc]
      exact Nat.pow_le_pow_right (by norm_num) h4Pg
    rw [hk] at hElt ⊢
    have hk5 : 5 ≤ k := by
      by_contra hcon
      have : 5 ^ k ≤ 5 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Nat.pow_le_pow_right (by norm_num) hk5
  have hPcard : Nat.card Pg = 5 ^ 5 := le_antisymm hcard5 hcard5ge
  obtain ⟨J, n, g, h, cfg⟩ := hM Y P x z hpl L hL hLu h29 hPcard
  have hρz : ρ z ≠ 1 := by
    intro h1
    have h2 : V₀ = ⊥ := by rw [hV₀, h1, sub_self, LinearMap.range_zero]
    rw [h2, finrank_bot] at hdim20
    omega
  have hJP : J ≤ Pg := cfg.J_le
  let JQ : Subgroup ↥Pg := J.subgroupOf Pg
  have hJQcard : Nat.card JQ = 5 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJP).toEquiv, cfg.J_card]
  have hJQc : ∀ a ∈ JQ, ∀ b ∈ JQ, a * b = b * a := by
    intro a ha b hb
    refine Subtype.ext ?_
    exact congrArg (fun t : ↥J => (t : Y))
      (cfg.J_abel.1.is_comm.comm (⟨((a : ↥Pg) : Y), ha⟩ : J) ⟨((b : ↥Pg) : Y), hb⟩)
  obtain ⟨rb1, rbn, rb2⟩ := rank_bounds hpP5 σ hσinj hdim20 JQ hJQc hJQcard hcard5 hQnc
  have hJn : ∀ p ∈ Pg, ∀ j ∈ J, p * j * p⁻¹ ∈ J := by
    intro p hp j hj
    exact Subgroup.mem_subgroupOf.mp
      (rbn ⟨p, hp⟩ ⟨j, hJP hj⟩ (Subgroup.mem_subgroupOf.mpr hj))
  have hR1 : ∀ (p : Y) (hp : p ∈ Pg), Module.finrank (ZMod 2) (V₀.map (ρ p - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range ((σ ⟨p, hp⟩ : ↥V₀ →ₗ[ZMod 2] ↥V₀) - 1)) := by
    intro p hp
    have : V₀.map (ρ p - 1) =
        (LinearMap.range ((σ ⟨p, hp⟩ : ↥V₀ →ₗ[ZMod 2] ↥V₀) - 1)).map V₀.subtype := by
      ext w
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨((σ ⟨p, hp⟩ : ↥V₀ →ₗ[ZMod 2] ↥V₀) - 1) ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
        exact ⟨(u : V), u.2, rfl⟩
    rw [this]
    exact Submodule.finrank_map_subtype_eq V₀ _
  have hD2 : ∀ p ∈ Pg, V₀.map (ρ p - 1) ≤ V₀ ⊓ LinearMap.range (ρ p - 1) := by
    rintro p hp _ ⟨v, hv, rfl⟩
    refine ⟨?_, ⟨v, rfl⟩⟩
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact V₀.sub_mem (hV₀inv p hp v hv) hv
  have hI1 : ∀ g' ∈ Pg, g' ∉ J →
      16 ≤ Module.finrank (ZMod 2) (V₀ ⊓ LinearMap.range (ρ g' - 1) : Submodule (ZMod 2) V) := by
    intro g' hg' hg'J
    have h1 := rb1 ⟨g', hg'⟩ (fun hmem => hg'J (Subgroup.mem_subgroupOf.mp hmem))
    rw [← hR1 g' hg'] at h1
    exact h1.trans (Submodule.finrank_mono (hD2 g' hg'))
  have hcommP : ⁅J, Pg⁆ ≤ Pg := by
    rw [Subgroup.commutator_le]
    intro j hj p hp
    rw [commutatorElement_def]
    exact Pg.mul_mem (Pg.mul_mem (Pg.mul_mem (hJP hj) hp) (Pg.inv_mem (hJP hj))) (Pg.inv_mem hp)
  have hI2 : ∀ e ∈ ⁅J, Pg⁆, e ≠ 1 →
      12 ≤ Module.finrank (ZMod 2) (V₀ ⊓ LinearMap.range (ρ e - 1) : Submodule (ZMod 2) V) := by
    intro e he he1
    have hmap : (⁅JQ, (⊤ : Subgroup ↥Pg)⁆).map Pg.subtype = ⁅J, Pg⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJP, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [← hmap] at he
    obtain ⟨e', he', hee'⟩ := he
    have hePg : e ∈ Pg := hee' ▸ e'.2
    have h1 := rb2 e' he' (fun h1 => he1 (by rw [← hee', h1]; rfl))
    have e'eq : e' = ⟨e, hePg⟩ := Subtype.ext hee'
    rw [e'eq, ← hR1 e hePg] at h1
    exact h1.trans (Submodule.finrank_mono (hD2 e hePg))
  have hz'E : n * z * n⁻¹ ∈ ⁅J, Pg⁆ := ((Subgroup.mem_normalizer_iff.mp cfg.n_E) z).mp cfg.z_mem
  have hz'1 : n * z * n⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    have := congrArg (fun t => n⁻¹ * t * n) h1
    simpa [mul_assoc] using this
  obtain ⟨c₁, hc₁⟩ := isConj_iff.mp cfg.conj_g
  obtain ⟨c₂, hc₂⟩ := isConj_iff.mp cfg.conj_h
  obtain ⟨p0, hp0, hhp0⟩ := mem_conjSub.mp cfg.h_mem
  have hp0J : p0 ∉ J := fun hp0J =>
    cfg.h_not (hhp0 ▸ ((Subgroup.mem_normalizer_iff.mp cfg.n_J) p0).mp hp0J)
  have hA : Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) = 20 := hdim20
  have hA' : Module.finrank (ZMod 2) (LinearMap.range (ρ (n * z * n⁻¹) - 1)) = 20 := by
    rw [finrank_range_conj]
    exact hA
  have hB : Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) = 20 := by
    rw [← hc₁, finrank_range_conj]
    exact hA
  have hB' : Module.finrank (ZMod 2) (LinearMap.range (ρ h - 1)) = 20 := by
    rw [← hc₂, finrank_range_conj]
    exact hA
  have hAB := hI1 g cfg.g_mem cfg.g_not
  have hAA' := hI2 _ hz'E hz'1
  have hA'B' : 16 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ (n * z * n⁻¹) - 1) ⊓
      LinearMap.range (ρ h - 1) : Submodule (ZMod 2) V) := by
    rw [← hhp0, finrank_inf_conj]
    exact hI1 p0 hp0 hp0J
  have hdimN : Module.finrank (ZMod 2) (commSub ρ (Subgroup.closure
      ({z, n * z * n⁻¹, g, h} : Set Y))) ≤ 36 := by
    have hle : (⨆ s ∈ ({z, n * z * n⁻¹, g, h} : Set Y), LinearMap.range (ρ s - 1)) ≤
        LinearMap.range (ρ z - 1) ⊔ (LinearMap.range (ρ (n * z * n⁻¹) - 1) ⊔
          (LinearMap.range (ρ g - 1) ⊔ LinearMap.range (ρ h - 1))) := by
      refine iSup₂_le fun s hs => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact le_sup_left
      · exact le_sup_of_le_right le_sup_left
      · exact le_sup_of_le_right (le_sup_of_le_right le_sup_left)
      · exact le_sup_of_le_right (le_sup_of_le_right le_sup_right)
    exact le_trans (Submodule.finrank_mono ((commSub_closure_le ρ _).trans hle))
      (finrank_sup_four_le hA hA' hB hB' hAB hA'B' hAA')
  exact endgame_cfg ρ hpP5 hPcard hJn cfg hρz hdimN

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

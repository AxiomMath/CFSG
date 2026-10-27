module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotTransfer

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect map_perfectCore
  perfectCore_eq_self_of_perfect)

section Defs

variable (n : ℕ) (K : Type) [Field K] {X : Type*} [Group X]

@[expose] def SpPartnerShapeOn (θ α : MulAut X) : Prop :=
  ∃ (x₀ : X) (η : MulAut X) (p : Fin n),
    α = MulAut.conj x₀ * η ∧ η x₀ = x₀ ∧ x₀ * x₀ = 1 ∧
    (∃ β : MulAut X, β * θ = η * β) ∧
    fixedSubgroup α ≤ centralizer ({x₀} : Set X) ∧
    ⁅fixedSubgroup α, fixedSubgroup α⁆ = fixedSubgroup α ∧
    Nat.card (fixedSubgroup α) = Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp n K))) ∧
    ∀ T : Subgroup X, T ≤ fixedSubgroup α → Odd (Nat.card T) →
      ∃ P : Subgroup X, P ≤ centralizer (T : Set X) ∧ ⁅P, P⁆ = P ∧
        ¬ P ≤ centralizer ({x₀} : Set X)

@[expose] def SpCosetCardOn (θ : MulAut X) : Prop :=
  ∀ y : X, (MulAut.conj y * θ) * (MulAut.conj y * θ) = 1 →
    (∃ β : MulAut X, β * θ = (MulAut.conj y * θ) * β) ∨
      ∃ p : Fin n, Nat.card (fixedSubgroup (MulAut.conj y * θ)) ≤
        Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp n K)))

end Defs

section Lift

variable {G : Type} [Group G]

theorem exists_sq_eq_one_mem_of_map_mk {M : Subgroup G} (hZ : Odd (Nat.card (center M)))
    {H : Subgroup M} {xb : M ⧸ center M} (hx : xb ∈ H.map (QuotientGroup.mk' (center M)))
    (hx2 : xb * xb = 1) :
    ∃ x ∈ H, x * x = 1 ∧ QuotientGroup.mk' (center M) x = xb := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hy2 : y ^ 2 ∈ center M := by
    rw [← QuotientGroup.ker_mk' (center M), MonoidHom.mem_ker, map_pow, _root_.sq, hx2]
  obtain ⟨j, hj⟩ := E6Pilot.odd_orderOf_of_mem_center hZ hy2
  refine ⟨y ^ (2 * j + 1), pow_mem hy _, ?_, ?_⟩
  · rw [← pow_add, show 2 * j + 1 + (2 * j + 1) = 2 * (2 * j + 1) by ring, pow_mul, ← hj,
      pow_orderOf_eq_one]
  · rw [map_pow, pow_succ, pow_mul, _root_.sq, hx2, one_pow, one_mul]

theorem map_mk_fixedSubgroup_le (M : Subgroup G) {w : G} (hw : w ∈ normalizer (M : Set G)) :
    (fixedSubgroup (M.normalizerMonoidHom ⟨w, hw⟩)).map (QuotientGroup.mk' (center M)) ≤
      fixedSubgroup (centerQuotAction M ⟨w, hw⟩) := by
  rintro _ ⟨y, hy, rfl⟩
  change centerQuotAction M ⟨w, hw⟩ (QuotientGroup.mk' (center M) y) = _
  rw [centerQuotAction_apply_mk]
  have hy' : M.normalizerMonoidHom ⟨w, hw⟩ y = y := hy
  rw [hy']
  rfl

theorem centerQuotAction_mul_self' {M : Subgroup G} {w : G} (hw2 : w * w = 1)
    (hw : w ∈ normalizer (M : Set G)) :
    centerQuotAction M ⟨w, hw⟩ * centerQuotAction M ⟨w, hw⟩ = 1 := by
  rw [← map_mul, show (⟨w, hw⟩ : normalizer (M : Set G)) * ⟨w, hw⟩ = 1 from Subtype.ext hw2,
    map_one]

theorem centerQuotAction_of_mem (M : Subgroup G) {z : G} (hz : z ∈ M) :
    centerQuotAction M ⟨z, le_normalizer hz⟩ =
      MulAut.conj (QuotientGroup.mk' (center M) ⟨z, hz⟩) :=
  EPilot.normalizerQuotMulAut_of_mem (MulEquiv.refl _) hz

theorem normalizerMonoidHom_eq_of_centerQuotAction_eq {M : Subgroup G} [Group.IsPerfect M]
    {u v : G} (hu : u ∈ normalizer (M : Set G)) (hv : v ∈ normalizer (M : Set G))
    (h : centerQuotAction M ⟨u, hu⟩ = centerQuotAction M ⟨v, hv⟩) :
    M.normalizerMonoidHom ⟨u, hu⟩ = M.normalizerMonoidHom ⟨v, hv⟩ := by
  apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective M
  exact MulEquiv.ext fun x => by
    have := congrArg (fun γ : MulAut (M ⧸ center M) => γ x) h
    exact this

theorem card_le_card_fixedSubgroup_quot_of_mem_normalizer [Finite G] {G₀ L : Subgroup G}
    (hLG : L ≤ G₀)
    {t g : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hZ : Odd (Nat.card (center G₀))) (hgN : g ∈ normalizer (G₀ : Set G))
    (hg : g⁻¹ * t * g ∈ normalizer (G₀ : Set G)) :
    Nat.card L ≤ Nat.card (fixedSubgroup (centerQuotAction G₀ ⟨g⁻¹ * t * g, hg⟩)) := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  set β := G₀.normalizerMonoidHom ⟨g⁻¹, inv_mem hgN⟩ with hβ
  have hβapp : ∀ y : G₀, ((β y : G₀) : G) = g⁻¹ * y * g := fun y => by
    rw [hβ, Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  set φ : L →* G₀ ⧸ center G₀ :=
    (QuotientGroup.mk' (center G₀)).comp (β.toMonoidHom.comp (Subgroup.inclusion hLG)) with hφ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    have ha : β (Subgroup.inclusion hLG l) ∈ center G₀ := by
      rw [← QuotientGroup.ker_mk' (center G₀), MonoidHom.mem_ker]
      exact hl
    have hlZ : Subgroup.inclusion hLG l ∈ center G₀ := by
      rw [mem_center_iff]
      intro y
      apply β.injective
      rw [map_mul, map_mul]
      exact mem_center_iff.1 ha (β y)
    have h1 := eq_one_of_mem_center_of_commute hLG ht hKt hZ hlZ
      (mem_centralizer_iff.1 htC (l : G) l.2)
    have h2 : ((Subgroup.inclusion hLG l : G₀) : G) = ((1 : G₀) : G) := by rw [h1]
    exact (mem_bot).2 (Subtype.ext h2)
  have hrange : φ.range ≤ fixedSubgroup (centerQuotAction G₀ ⟨g⁻¹ * t * g, hg⟩) := by
    rintro _ ⟨l, rfl⟩
    refine map_mk_fixedSubgroup_le G₀ hg ⟨β (Subgroup.inclusion hLG l), ?_, rfl⟩
    change G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ (β (Subgroup.inclusion hLG l)) =
      β (Subgroup.inclusion hLG l)
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hβapp]
    have hlt : (l : G) * t = t * l := mem_centralizer_iff.1 htC (l : G) l.2
    change g⁻¹ * t * g * (g⁻¹ * (l : G) * g) * (g⁻¹ * t * g)⁻¹ = g⁻¹ * (l : G) * g
    calc g⁻¹ * t * g * (g⁻¹ * (l : G) * g) * (g⁻¹ * t * g)⁻¹ =
        g⁻¹ * (t * (l : G)) * t⁻¹ * g := by group
      _ = g⁻¹ * (l : G) * g := by rw [← hlt]; group
  calc Nat.card L = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    _ ≤ _ := Subgroup.card_le_of_le hrange

end Lift

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem false_of_spPartnerShapeQuot (hset : SeitzSetting G L) {m f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* StatedSp (m + 3) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    (hLS : L ≤ G₀) [Group.IsPerfect G₀] (hZ : Odd (Nat.card (center G₀)))
    (htN : t ∈ normalizer (G₀ : Set G)) (hodd : Odd (Nat.card (centralizer (G₀ : Set G))))
    (htransfer : ∀ (h : G) (hh : h⁻¹ * t * h ∈ normalizer (G₀ : Set G))
      (γ : MulAut (G₀ ⧸ center G₀)),
      γ * centerQuotAction G₀ ⟨t, htN⟩ = centerQuotAction G₀ ⟨h⁻¹ * t * h, hh⟩ * γ →
        h ∈ normalizer (G₀ : Set G))
    (hInn : CosetInnConjInput (centerQuotAction G₀ ⟨t, htN⟩))
    (hDich : SpCosetCardOn (m + 3) K (centerQuotAction G₀ ⟨t, htN⟩))
    (hTor : pieceCore e ({Fin.last (m + 2)} : Finset (Fin (m + 3))) ≤
      centralizer ({t} : Set G))
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (G₀ : Set G))
    (hsh : SpPartnerShapeOn (m + 3) K (centerQuotAction G₀ ⟨t, htN⟩)
      (centerQuotAction G₀ ⟨g⁻¹ * t * g, hg⟩)) : False := by
  set θt := centerQuotAction G₀ ⟨t, htN⟩ with hθt
  set θs := centerQuotAction G₀ ⟨g⁻¹ * t * g, hg⟩ with hθs
  obtain ⟨xb0, η, p, hα, hηx, hxx, ⟨β₀, hβ₀⟩, hFle, hFperf, hFcard, hFtor⟩ := hsh
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega) e)
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
  have hact : ∀ y : G₀, ((G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ y : G₀) : G) =
      (g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  set Cs := fixedSubgroup (G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) with hCs
  have hCsmap : Cs.map (QuotientGroup.mk' (center G₀)) = fixedSubgroup θs :=
    map_mk_fixedSubgroup_eq_centerQuot hZ hs2 hg
  set C₀ := perfectCore Cs with hC₀
  have hC₀map : C₀.map (QuotientGroup.mk' (center G₀)) = fixedSubgroup θs := by
    rw [hC₀, map_perfectCore, hCsmap, perfectCore_eq_self_of_perfect hFperf]
  have hC₀perf : ⁅C₀, C₀⁆ = C₀ := perfectCore_perfect _
  have hC₀s : C₀ ≤ Cs := perfectCore_le _
  have hθx : θs xb0 = xb0 := by
    rw [hα, MulAut.mul_apply, hηx, MulAut.conj_apply, mul_inv_cancel_right]
  obtain ⟨x₀, hx₀C, hx₀2, hx₀π⟩ := exists_sq_eq_one_mem_of_map_mk hZ
    (show xb0 ∈ C₀.map (QuotientGroup.mk' (center G₀)) by rw [hC₀map]; exact hθx) hxx
  have hC₀x : ∀ y ∈ C₀, y * x₀ = x₀ * y := by
    refine commute_of_perfect_of_mk_commute hC₀perf fun y hy => ?_
    have h1 : QuotientGroup.mk' (center G₀) y ∈ fixedSubgroup θs := by
      rw [← hC₀map]
      exact ⟨y, hy, rfl⟩
    have h2 := mem_centralizer_singleton_iff.1 (hFle h1)
    rw [← hx₀π] at h2
    change QuotientGroup.mk' (center G₀) (y * x₀) = QuotientGroup.mk' (center G₀) (x₀ * y)
    rw [map_mul, map_mul, h2]
  set x : G := g * x₀ * g⁻¹ with hx
  have hsx : (g⁻¹ * t * g) * (x₀ : G) = x₀ * (g⁻¹ * t * g) := by
    have h1 := hact x₀
    rw [show G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ x₀ = x₀ from hC₀s hx₀C] at h1
    calc (g⁻¹ * t * g) * (x₀ : G) =
        ((g⁻¹ * t * g) * x₀ * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g) := by group
      _ = x₀ * (g⁻¹ * t * g) := by rw [← h1]
  have htx : t * x = x * t := by
    calc t * x = g * ((g⁻¹ * t * g) * x₀) * g⁻¹ := by rw [hx]; group
      _ = g * (x₀ * (g⁻¹ * t * g)) * g⁻¹ := by rw [hsx]
      _ = x * t := by rw [hx]; group
  have hx0 : (x₀ : G) * x₀ = 1 := by
    have h1 := congrArg Subtype.val hx₀2
    simpa using h1
  have hx2 : x * x = 1 := by
    calc x * x = g * ((x₀ : G) * x₀) * g⁻¹ := by rw [hx]; group
      _ = 1 := by rw [hx0]; group
  set c : G₀ →* G := (MulAut.conj g).toMonoidHom.comp G₀.subtype with hc
  have hcinj : Function.Injective c := (MulAut.conj g).injective.comp G₀.subtype_injective
  set Λ : Subgroup G := C₀.map c with hΛ
  have hΛcard : Nat.card Λ = Nat.card C₀ := Subgroup.card_map_of_injective hcinj
  have hΛperf : ⁅Λ, Λ⁆ = Λ := by rw [hΛ, ← Subgroup.map_commutator, hC₀perf]
  have hΛt : Λ ≤ centralizer ({t} : Set G) :=
    (Subgroup.map_mono hC₀s).trans (map_fixedSubgroup_conj_le_centralizer hg)
  have hΛL : Λ ≤ L := std_perfect_le hset.standardSetting hOut htC ht hΛperf hΛt
  have hxΛ : x ∈ Λ := ⟨x₀, hx₀C, rfl⟩
  have hxL : x ∈ L := hΛL hxΛ
  have hxG : x ∈ G₀ := hLS hxL
  have hΛx : Λ ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have h2 : (y : G) * x₀ = x₀ * y := congrArg Subtype.val (hC₀x y hy)
    rw [mem_centralizer_singleton_iff]
    simp only [hc, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * (y : G) * g⁻¹ * x = g * ((y : G) * x₀) * g⁻¹ := by rw [hx]; group
      _ = g * (x₀ * y) * g⁻¹ := by rw [h2]
      _ = x * (g * y * g⁻¹) := by rw [hx]; group
  have hFΛ : Nat.card (fixedSubgroup θs) ≤ Nat.card Λ := by
    rw [hΛcard, ← hC₀map]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
  have hxN : x ∈ normalizer (G₀ : Set G) := le_normalizer hxG
  have ht'N : t * x ∈ normalizer (G₀ : Set G) := mul_mem htN hxN
  have hθ' : centerQuotAction G₀ ⟨t * x, ht'N⟩ =
      MulAut.conj (QuotientGroup.mk' (center G₀) ⟨x, hxG⟩) * θt := by
    have e1 : (⟨t * x, ht'N⟩ : normalizer (G₀ : Set G)) = ⟨x, hxN⟩ * ⟨t, htN⟩ := Subtype.ext htx
    rw [e1, map_mul, show (⟨x, hxN⟩ : normalizer (G₀ : Set G)) = ⟨x, le_normalizer hxG⟩ from rfl,
      centerQuotAction_of_mem G₀ hxG]
  have ht'2 : (t * x) * (t * x) = 1 := by
    calc (t * x) * (t * x) = t * (x * t) * x := by group
      _ = t * (t * x) * x := by rw [htx]
      _ = (t * t) * (x * x) := by group
      _ = 1 := by rw [htt, hx2, one_mul]
  have hθ'2 : (MulAut.conj (QuotientGroup.mk' (center G₀) ⟨x, hxG⟩) * θt) *
      (MulAut.conj (QuotientGroup.mk' (center G₀) ⟨x, hxG⟩) * θt) = 1 := by
    rw [← hθ']
    exact centerQuotAction_mul_self' ht'2 ht'N
  have hfixLt : Nat.card (fixedSubgroup θs) < Nat.card L := by
    rw [hFcard, Nat.card_congr e.toEquiv]
    exact card_centralizer_siegDiag_lt p
  rcases hDich (QuotientGroup.mk' (center G₀) ⟨x, hxG⟩) hθ'2 with hstd | ⟨p₁, hp₁⟩
  ·
    obtain ⟨zb, hz⟩ := hInn _ hθ'2 hstd
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (center G₀) zb
    have hzN : (z : G) ∈ normalizer (G₀ : Set G) := le_normalizer z.2
    have hztN : (z : G) * t * (z : G)⁻¹ ∈ normalizer (G₀ : Set G) :=
      mul_mem (mul_mem hzN htN) (inv_mem hzN)
    have hθz : centerQuotAction G₀ ⟨(z : G) * t * (z : G)⁻¹, hztN⟩ =
        MulAut.conj (QuotientGroup.mk' (center G₀) z) * θt *
          (MulAut.conj (QuotientGroup.mk' (center G₀) z))⁻¹ := by
      have e1 : (⟨(z : G) * t * (z : G)⁻¹, hztN⟩ : normalizer (G₀ : Set G)) =
          ⟨z, hzN⟩ * ⟨t, htN⟩ * ⟨z, hzN⟩⁻¹ := Subtype.ext rfl
      rw [e1, map_mul, map_mul, map_inv,
        show (⟨(z : G), hzN⟩ : normalizer (G₀ : Set G)) = ⟨z, le_normalizer z.2⟩ from rfl,
        centerQuotAction_of_mem G₀ z.2]
    have hzt2 : ((z : G) * t * (z : G)⁻¹) * ((z : G) * t * (z : G)⁻¹) = 1 := by
      calc ((z : G) * t * (z : G)⁻¹) * ((z : G) * t * (z : G)⁻¹) =
          (z : G) * (t * t) * (z : G)⁻¹ := by group
        _ = 1 := by rw [htt]; group
    have hacteq : G₀.normalizerMonoidHom ⟨(z : G) * t * (z : G)⁻¹, hztN⟩ =
        G₀.normalizerMonoidHom ⟨t * x, ht'N⟩ :=
      normalizerMonoidHom_eq_of_centerQuotAction_eq hztN ht'N (by rw [hθz, hθ', hz])
    obtain ⟨c', hcC, hc'⟩ := exists_conj_eq_of_normalizerMonoidHom_eq hodd hzt2 ht'2 hztN ht'N
      hacteq
    have hcN : c' ∈ normalizer (G₀ : Set G) := centralizer_le_normalizer _ hcC
    set nn : G := c' * z with hnn
    have hnnN : nn ∈ normalizer (G₀ : Set G) := mul_mem hcN hzN
    have hnt : nn * t * nn⁻¹ = t * x := by
      rw [hc', hnn]
      group
    set h : G := nn⁻¹ * g with hh
    have hht : h⁻¹ * t * h = (g⁻¹ * t * g) * x₀ := by
      calc h⁻¹ * t * h = g⁻¹ * (nn * t * nn⁻¹) * g := by rw [hh]; group
        _ = g⁻¹ * (t * x) * g := by rw [hnt]
        _ = (g⁻¹ * t * g) * x₀ := by rw [hx]; group
    have hx₀N : (x₀ : G) ∈ normalizer (G₀ : Set G) := le_normalizer x₀.2
    have hsxN : (g⁻¹ * t * g) * x₀ ∈ normalizer (G₀ : Set G) := mul_mem hg hx₀N
    have hhN : h⁻¹ * t * h ∈ normalizer (G₀ : Set G) := hht ▸ hsxN
    have hθh : centerQuotAction G₀ ⟨h⁻¹ * t * h, hhN⟩ = η := by
      have e1 : (⟨h⁻¹ * t * h, hhN⟩ : normalizer (G₀ : Set G)) =
          ⟨g⁻¹ * t * g, hg⟩ * ⟨x₀, hx₀N⟩ := Subtype.ext hht
      rw [e1, map_mul, show (⟨(x₀ : G), hx₀N⟩ : normalizer (G₀ : Set G)) =
        ⟨x₀, le_normalizer x₀.2⟩ from rfl, centerQuotAction_of_mem G₀ x₀.2, Subtype.coe_eta,
        hx₀π]
      change θs * MulAut.conj xb0 = η
      rw [hα, mul_assoc, mulAut_mul_conj_eq_of_apply_eq hηx, ← mul_assoc, ← map_mul, hxx,
        map_one, one_mul]
    have hhG : h ∈ normalizer (G₀ : Set G) := htransfer h hhN β₀ (by rw [hθh]; exact hβ₀)
    have hgG : g ∈ normalizer (G₀ : Set G) := by
      have : g = nn * h := by rw [hh]; group
      rw [this]
      exact mul_mem hnnN hhG
    exact absurd (card_le_card_fixedSubgroup_quot_of_mem_normalizer hLS ht hKt hZ hgG hg)
      (not_le.2 hfixLt)
  ·
    rw [← hθ'] at hp₁
    set Ct' := fixedSubgroup (G₀.normalizerMonoidHom ⟨t * x, ht'N⟩) with hCt'
    have hCL : L ⊓ centralizer ({x} : Set G) ≤ Ct'.map G₀.subtype := by
      rintro l ⟨hl, hlx⟩
      refine ⟨⟨l, hLS hl⟩, ?_, rfl⟩
      show G₀.normalizerMonoidHom ⟨t * x, ht'N⟩ ⟨l, hLS hl⟩ = ⟨l, hLS hl⟩
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hlx' : l * x = x * l := mem_centralizer_singleton_iff.1 hlx
      have hlt' : l * t = t * l := mem_centralizer_iff.1 htC l hl
      change t * x * l * (t * x)⁻¹ = l
      calc t * x * l * (t * x)⁻¹ = t * (x * l) * x⁻¹ * t⁻¹ := by group
        _ = t * (l * x) * x⁻¹ * t⁻¹ := by rw [hlx']
        _ = (t * l) * t⁻¹ := by group
        _ = l := by rw [← hlt']; group
    have hπinj : Function.Injective ((QuotientGroup.mk' (center G₀)).comp Ct'.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro z hz
      have hzZ : (z : G₀) ∈ center G₀ := by
        rw [← QuotientGroup.ker_mk' (center G₀), MonoidHom.mem_ker]
        exact hz
      have hz1 : ((z : G₀) : G) * (t * x) = (t * x) * (z : G₀) := by
        have h1 := (Subgroup.ext_iff.1 (fixedSubgroup_normalizerMonoidHom_eq ht'N) z).1 z.2
        rw [mem_subgroupOf, mem_centralizer_singleton_iff] at h1
        exact h1
      have hz2 : x * ((z : G₀) : G) = ((z : G₀) : G) * x :=
        congrArg Subtype.val (mem_center_iff.1 hzZ ⟨x, hxG⟩)
      have hzt : ((z : G₀) : G) * t = t * (z : G₀) := by
        calc ((z : G₀) : G) * t = (((z : G₀) : G) * (t * x)) * x⁻¹ := by group
          _ = ((t * x) * (z : G₀)) * x⁻¹ := by rw [hz1]
          _ = t * (x * ((z : G₀) : G)) * x⁻¹ := by group
          _ = t * (((z : G₀) : G) * x) * x⁻¹ := by rw [hz2]
          _ = t * (z : G₀) := by group
      have h1 := eq_one_of_mem_center_of_commute hLS ht hKt hZ hzZ hzt
      have h2 : (((z : G₀)) : G) = (((1 : Ct') : G₀) : G) := by rw [h1]; rfl
      exact (mem_bot).2 (Subtype.ext (Subtype.ext h2))
    have hcardCt' : Nat.card Ct' ≤
        Nat.card (fixedSubgroup (centerQuotAction G₀ ⟨t * x, ht'N⟩)) := by
      calc Nat.card Ct' = Nat.card ((QuotientGroup.mk' (center G₀)).comp Ct'.subtype).range :=
            Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv
        _ ≤ _ := Subgroup.card_le_of_le (by
            rw [MonoidHom.range_comp, Subgroup.range_subtype]
            exact map_mk_fixedSubgroup_le G₀ ht'N)
    have hchain : Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G) ≤
        Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 3) K))) := by
      calc Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G) ≤
          Nat.card (Ct'.map G₀.subtype) := Subgroup.card_le_of_le hCL
        _ = Nat.card Ct' := Subgroup.card_map_of_injective G₀.subtype_injective
        _ ≤ Nat.card (fixedSubgroup (centerQuotAction G₀ ⟨t * x, ht'N⟩)) := hcardCt'
        _ ≤ Nat.card (centralizer ({siegDiag K p₁ 1} : Set (StatedSp (m + 3) K))) := hp₁
        _ = Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 3) K))) :=
          card_centralizer_siegDiag_eq p₁ p 1
    have hΛge : Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 3) K))) ≤
        Nat.card Λ := hFcard ▸ hFΛ
    have hΛeq : Λ = L ⊓ centralizer ({x} : Set G) :=
      Subgroup.eq_of_le_of_card_ge (le_inf hΛL hΛx) (hchain.trans hΛge)
    have hΛcard' : Nat.card Λ =
        Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 3) K))) :=
      le_antisymm (hΛeq ▸ hchain) hΛge
    set x' : L := ⟨x, hxL⟩ with hx'
    have hmapC : (centralizer ({x'} : Set L)).map L.subtype = L ⊓ centralizer ({x} : Set G) := by
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        refine ⟨y'.2, ?_⟩
        show (y' : G) ∈ centralizer ({x} : Set G)
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy')
      · rintro ⟨hyL, hyx⟩
        refine ⟨⟨y, hyL⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        exact Subtype.ext (mem_centralizer_singleton_iff.1 hyx)
    have hCperf : ⁅centralizer ({x'} : Set L), centralizer ({x'} : Set L)⁆ =
        centralizer ({x'} : Set L) := by
      apply Subgroup.map_injective L.subtype_injective
      rw [Subgroup.map_commutator, hmapC, ← hΛeq, hΛperf]
    have hCcard : Nat.card (centralizer ({x'} : Set L)) =
        Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 3) K))) := by
      rw [← Subgroup.card_map_of_injective L.subtype_injective, hmapC, ← hΛeq, hΛcard']
    obtain ⟨P₀, -, -, hP₀⟩ := hFtor ⊥ bot_le (by rw [Subgroup.card_bot]; exact odd_one)
    have hx₀1 : xb0 ≠ 1 := by
      intro h0
      apply hP₀
      intro y _
      rw [mem_centralizer_singleton_iff, h0, one_mul, mul_one]
    have hx'1 : x' ≠ 1 := by
      intro h1
      have h2 : x = 1 := congrArg Subtype.val h1
      apply hx₀1
      have h3 : (x₀ : G) = g⁻¹ * x * g := by rw [hx]; group
      have h4 : x₀ = 1 := Subtype.ext (by rw [h3, h2]; simp)
      rw [← hx₀π, h4, map_one]
    obtain ⟨c₁, hc₁⟩ := exists_conj_eq_siegDiag_last hK4 e hx'1 hCperf hCcard
    set l : G := ((c₁⁻¹ : L) : G) with hl
    have hlL : l ∈ L := (c₁⁻¹ : L).2
    have hxl : x = l * ((e.symm (siegDiag K (Fin.last (m + 2)) 1) : L) : G) * l⁻¹ := by
      have h1 := congrArg (fun y : L => (y : G)) hc₁
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [hl, ← h1, hx']
      simp only [Subgroup.coe_inv, inv_inv]
      group
    set T₀ : Subgroup G := modelToG e (leviTorusSp K ({Fin.last (m + 2)} : Finset (Fin (m + 3))))
      with hT₀
    set T : Subgroup G := T₀.map (MulAut.conj l).toMonoidHom with hT
    have hTΛ : T ≤ Λ := by
      rw [hΛeq]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨d, hd, rfl⟩ := (mem_modelToG e).1 hy
      have hdz := mem_centralizer_singleton_iff.1
        (leviTorusSp_last_le_centralizer_siegDiag (K := K) (m + 2) hd)
      have hmemL : l * ((e.symm d : L) : G) * l⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem hlL (e.symm d).2) (L.inv_mem hlL)
      refine ⟨hmemL, ?_⟩
      show l * ((e.symm d : L) : G) * l⁻¹ ∈ centralizer ({x} : Set G)
      rw [mem_centralizer_singleton_iff, hxl]
      have h2 : ((e.symm d : L) : G) * ((e.symm (siegDiag K (Fin.last (m + 2)) 1) : L) : G) =
          ((e.symm (siegDiag K (Fin.last (m + 2)) 1) : L) : G) * ((e.symm d : L) : G) := by
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hdz]
      calc l * ((e.symm d : L) : G) * l⁻¹ *
            (l * ((e.symm (siegDiag K (Fin.last (m + 2)) 1) : L) : G) * l⁻¹) =
          l * (((e.symm d : L) : G) * ((e.symm (siegDiag K (Fin.last (m + 2)) 1) : L) : G)) *
            l⁻¹ := by group
        _ = l * (((e.symm (siegDiag K (Fin.last (m + 2)) 1) : L) : G) * ((e.symm d : L) : G)) *
            l⁻¹ := by rw [h2]
        _ = l * ((e.symm (siegDiag K (Fin.last (m + 2)) 1) : L) : G) * l⁻¹ *
            (l * ((e.symm d : L) : G) * l⁻¹) := by group
    have hT₀odd : Odd (Nat.card T₀) := by
      rw [hT₀, UnitaryPilot.modelToG_def, Subgroup.card_map_of_injective L.subtype_injective,
        Subgroup.card_map_of_injective e.symm.injective]
      exact odd_card_leviTorusSp hKc (by omega) _
    have hTodd : Odd (Nat.card T) := by
      rw [hT, Subgroup.card_map_of_injective (MulAut.conj l).injective]
      exact hT₀odd
    set Tu : Subgroup G₀ := T.comap c with hTu
    have hTuC : Tu ≤ C₀ := by
      intro y hy
      obtain ⟨y', hy', hyy'⟩ := hTΛ hy
      have : y' = y := hcinj hyy'
      rw [← this]
      exact hy'
    have hTuodd : Odd (Nat.card Tu) := by
      have h1 : Nat.card (Tu.map c) = Nat.card Tu := Subgroup.card_map_of_injective hcinj
      have h2 : Tu.map c ≤ T := Subgroup.map_comap_le _ _
      rw [← h1]
      exact Odd.of_dvd_nat hTodd (Subgroup.card_dvd_of_le h2)
    set Tub : Subgroup (G₀ ⧸ center G₀) := Tu.map (QuotientGroup.mk' (center G₀)) with hTub
    have hTubF : Tub ≤ fixedSubgroup θs := by
      rw [← hC₀map]
      exact Subgroup.map_mono hTuC
    have hTubodd : Odd (Nat.card Tub) := Odd.of_dvd_nat hTuodd (Subgroup.card_map_dvd _ _)
    obtain ⟨Pb, hPc, hPperf, hPx⟩ := hFtor Tub hTubF hTubodd
    set P : Subgroup G₀ := perfectCore (Pb.comap (QuotientGroup.mk' (center G₀))) with hP
    have hPmap : P.map (QuotientGroup.mk' (center G₀)) = Pb := by
      rw [hP, map_perfectCore, Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective _), perfectCore_eq_self_of_perfect hPperf]
    have hPperf' : ⁅P, P⁆ = P := perfectCore_perfect _
    have hPTu : ∀ τ ∈ Tu, ∀ y ∈ P, y * τ = τ * y := by
      intro τ hτ
      refine commute_of_perfect_of_mk_commute hPperf' fun y hy => ?_
      have hy' : QuotientGroup.mk' (center G₀) y ∈ Pb := by
        rw [← hPmap]
        exact ⟨y, hy, rfl⟩
      have hτ' : QuotientGroup.mk' (center G₀) τ ∈ Tub := ⟨τ, hτ, rfl⟩
      have h1 := mem_centralizer_iff.1 (hPc hy') _ hτ'
      change QuotientGroup.mk' (center G₀) (y * τ) = QuotientGroup.mk' (center G₀) (τ * y)
      rw [map_mul, map_mul, h1]
    set P'' : Subgroup G := (P.map c).map (MulAut.conj l⁻¹).toMonoidHom with hP''
    have hP''perf : ⁅P'', P''⁆ = P'' := by
      rw [hP'', ← Subgroup.map_commutator, ← Subgroup.map_commutator, hPperf']
    have hP''T₀ : P'' ≤ centralizer (T₀ : Set G) := by
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rw [mem_centralizer_iff]
      intro τ hτ
      have hτT : l * τ * l⁻¹ ∈ T := ⟨τ, hτ, rfl⟩
      obtain ⟨τ', -, hττ'⟩ := hTΛ hτT
      have hτ'u : τ' ∈ Tu := by
        show c τ' ∈ T
        rw [hττ']
        exact hτT
      have h1 : y * τ' = τ' * y := hPTu τ' hτ'u y hy
      have h2 : c y * (l * τ * l⁻¹) = (l * τ * l⁻¹) * c y := by
        rw [← hττ', ← map_mul, ← map_mul, h1]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc τ * (l⁻¹ * c y * l) = l⁻¹ * ((l * τ * l⁻¹) * c y) * l := by group
        _ = l⁻¹ * (c y * (l * τ * l⁻¹)) * l := by rw [h2]
        _ = l⁻¹ * c y * l * τ := by group
    have hP''t : P'' ≤ centralizer ({t} : Set G) :=
      (F4Pilot.le_centralizerPerfectCore hP''perf hP''T₀).trans hTor
    have hlt : l * t = t * l := mem_centralizer_iff.1 htC l hlL
    have hPF : P ≤ Cs := by
      intro y hy
      have h1 : l⁻¹ * c y * l ∈ P'' := by
        refine ⟨c y, ⟨y, hy, rfl⟩, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have h2 : (l⁻¹ * c y * l) * t = t * (l⁻¹ * c y * l) :=
        mem_centralizer_singleton_iff.1 (hP''t h1)
      have h3 : c y * t = t * c y := by
        calc c y * t = l * ((l⁻¹ * c y * l) * t) * l⁻¹ := by
              rw [show l * ((l⁻¹ * c y * l) * t) * l⁻¹ = c y * (l * t * l⁻¹) by group, hlt]
              group
          _ = l * (t * (l⁻¹ * c y * l)) * l⁻¹ := by rw [h2]
          _ = t * c y := by
              rw [show l * (t * (l⁻¹ * c y * l)) * l⁻¹ = (l * t * l⁻¹) * c y by group, hlt]
              group
      show G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ y = y
      apply Subtype.ext
      rw [hact]
      have h4 : (g * (y : G) * g⁻¹) * t = t * (g * y * g⁻¹) := h3
      calc (g⁻¹ * t * g) * (y : G) * (g⁻¹ * t * g)⁻¹ =
          g⁻¹ * (t * (g * y * g⁻¹)) * t⁻¹ * g := by group
        _ = g⁻¹ * ((g * (y : G) * g⁻¹) * t) * t⁻¹ * g := by rw [h4]
        _ = y := by group
    apply hPx
    rw [← hPmap]
    exact ((Subgroup.map_mono hPF).trans (hCsmap.le)).trans hFle

end Main

end CFSG.SeitzReduction.SymplecticPilot

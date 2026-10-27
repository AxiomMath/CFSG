module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SecondClassPartner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotPartner

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.Quasithin (perfectCore map_perfectCore perfectCore_le perfectCore_perfect
  perfectCore_eq_self_of_perfect)

section Defs

variable (n : ℕ) (K : Type) [Field K] {X : Type*} [Group X]

@[expose] def NsPartnerShapeOn (θ α : MulAut X) : Prop :=
  ∃ (ρ : StatedSp n K →* X) (η : MulAut X) (p : Fin n),
    Function.Injective ρ ∧ α = MulAut.conj (ρ (siegDiag K p 1)) * η ∧
    (∀ y : StatedSp n K, η (ρ y) = ρ y) ∧ (∃ β : MulAut X, β * θ = η * β) ∧
    fixedSubgroup α = (centralizer ({siegDiag K p 1} : Set (StatedSp n K))).map ρ

end Defs

section Aut

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem exists_conj_map_nsTorusSp_eq_of_range_eq (hK : Nat.card K = 2) (hm : 3 ≤ m)
    {p k : Fin (m + 1)} (hkp : k ≠ p) {H : Type*} [Group H]
    {φ₁ φ₂ : centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) →* H}
    (h₁ : Function.Injective φ₁) (h₂ : Function.Injective φ₂) (hr : φ₁.range = φ₂.range) :
    ∃ c ∈ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
      ∀ x ∈ nsTorusSp K k, ∃ x₂ ∈ nsTorusSp K k,
        ∃ hx₂ : c * x₂ * c⁻¹ ∈ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
          ∃ hx : x ∈ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
            φ₁ ⟨x, hx⟩ = φ₂ ⟨c * x₂ * c⁻¹, hx₂⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (StatedSp (m + 1) K) := by
    have : Finite (GL (Fin (m + 1) ⊕ Fin (m + 1)) K) := inferInstance
    exact Subtype.finite
  let φ := (MonoidHom.ofInjective h₁).trans
    ((MulEquiv.subgroupCongr hr).trans (MonoidHom.ofInjective h₂).symm)
  have hφ : ∀ y : centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
      φ₂ (φ y) = φ₁ y := by
    intro y
    have h1 : ((MonoidHom.ofInjective h₂ (φ y) : φ₂.range) : H) = φ₂ (φ y) :=
      MonoidHom.ofInjective_apply h₂
    have h2 : MonoidHom.ofInjective h₂ (φ y) =
        MulEquiv.subgroupCongr hr (MonoidHom.ofInjective h₁ y) :=
      (MonoidHom.ofInjective h₂).apply_symm_apply _
    rw [← h1, h2]
    exact MonoidHom.ofInjective_apply h₁
  obtain ⟨δ, hδD, hδ⟩ := exists_mem_complSp_conj_of_mulEquiv hK hm φ
  have hXD : nsTorusSp K k ≤ complSp K p := nsTorusSp_le_complSp hkp
  have hXC : nsTorusSp K k ≤ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) :=
    hXD.trans complSp_le_centralizer_siegDiag
  set T : Subgroup (StatedSp (m + 1) K) := (nsTorusSp K k).map (MulAut.conj δ).toMonoidHom
    with hT
  set Tφ : Subgroup (StatedSp (m + 1) K) :=
    ((nsTorusSp K k).subgroupOf (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)))).map
      ((centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))).subtype.comp
        φ.toMonoidHom) with hTφ
  have hTD : T ≤ complSp K p := by
    rintro _ ⟨x, hx, rfl⟩
    exact (complSp K p).mul_mem ((complSp K p).mul_mem hδD (hXD hx)) ((complSp K p).inv_mem hδD)
  have hTN : T ≤ normalizer (transvRadical K p : Set (StatedSp (m + 1) K)) :=
    hTD.trans complSp_le_normalizer_transvRadical
  have hQT : transvRadical K p ⊓ T = ⊥ :=
    disjoint_iff.1 (disjoint_transvRadical_complSp.mono_right hTD)
  have hS : Tφ ≤ T ⊔ transvRadical K p := by
    rintro _ ⟨⟨x, hxC⟩, hx, rfl⟩
    have hxX : x ∈ nsTorusSp K k := hx
    have h1 := hδ x (hXD hxX)
    change (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) ∈ T ⊔ transvRadical K p
    have e : (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) =
        ((φ ⟨x, hxC⟩ : StatedSp (m + 1) K) * (δ * x * δ⁻¹)⁻¹) * (δ * x * δ⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_right h1) (mem_sup_left ⟨x, hxX, rfl⟩)
  have hinjφ : Function.Injective
      ((centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))).subtype.comp
        φ.toMonoidHom) := fun a b hab => φ.injective (Subtype.ext hab)
  have hcardX : Nat.card (nsTorusSp K k) = 3 := card_nsTorusSp k
  have hcardTφ : Nat.card Tφ = 3 := by
    rw [hTφ, Subgroup.card_map_of_injective hinjφ,
      CFSG.LieType.Chevalley.card_subgroupOf_of_le hXC, hcardX]
  have hcardT : Nat.card T = 3 := by
    rw [hT, Subgroup.card_map_of_injective (MulAut.conj δ).injective, hcardX]
  obtain ⟨u, hu, hle⟩ := F4Pilot.exists_mem_map_conj_le_of_le_sup isPGroup_transvRadical hTN hQT
    hS (by rw [hcardTφ]; decide)
  have heqT : Tφ.map (MulAut.conj u).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hcardT, Subgroup.card_map_of_injective (MulAut.conj u).injective, hcardTφ])
  have huC := transvRadical_le_centralizer (K := K) (p := p) hu
  have hδC := complSp_le_centralizer_siegDiag (K := K) (p := p) hδD
  refine ⟨u⁻¹ * δ, mul_mem (inv_mem huC) hδC, fun x hx => ?_⟩
  have hxC := hXC hx
  have hmem : (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) ∈ Tφ := ⟨⟨x, hxC⟩, hx, rfl⟩
  have h2 : u * (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) * u⁻¹ ∈ T := by
    rw [← heqT]
    exact ⟨_, hmem, rfl⟩
  obtain ⟨x₂, hx₂, hx₂eq⟩ := h2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx₂eq
  have hval : (u⁻¹ * δ) * x₂ * (u⁻¹ * δ)⁻¹ = (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) := by
    calc (u⁻¹ * δ) * x₂ * (u⁻¹ * δ)⁻¹ = u⁻¹ * (δ * x₂ * δ⁻¹) * u := by group
      _ = u⁻¹ * (u * (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) * u⁻¹) * u := by rw [hx₂eq]
      _ = (φ ⟨x, hxC⟩ : StatedSp (m + 1) K) := by group
  refine ⟨x₂, hx₂, hval ▸ (φ ⟨x, hxC⟩).2, hxC, ?_⟩
  rw [← hφ ⟨x, hxC⟩]
  congr 1
  exact Subtype.ext hval.symm

end Aut

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

set_option maxHeartbeats 400000 in
theorem false_of_nsPartnerShapeQuot (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    (hLS : L ≤ G₀) [Group.IsPerfect G₀] (hZ : Odd (Nat.card (center G₀)))
    (htN : t ∈ normalizer (G₀ : Set G)) (hodd : Odd (Nat.card (centralizer (G₀ : Set G))))
    (htransfer : ∀ (h : G) (hh : h⁻¹ * t * h ∈ normalizer (G₀ : Set G))
      (γ : MulAut (G₀ ⧸ center G₀)),
      γ * centerQuotAction G₀ ⟨t, htN⟩ = centerQuotAction G₀ ⟨h⁻¹ * t * h, hh⟩ * γ →
        h ∈ normalizer (G₀ : Set G))
    (htorus : ∀ (k : Fin (m + 1)) (P : Subgroup G), ⁅P, P⁆ = P →
      P ≤ centralizer (modelToG e (nsTorusSp K k) : Set G) → P ≤ G₀)
    (hInn : CosetInnConjInput (centerQuotAction G₀ ⟨t, htN⟩))
    (hDich : SpCosetCardOn (m + 1) K (centerQuotAction G₀ ⟨t, htN⟩))
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (G₀ : Set G))
    (hsh : NsPartnerShapeOn (m + 1) K (centerQuotAction G₀ ⟨t, htN⟩)
      (centerQuotAction G₀ ⟨g⁻¹ * t * g, hg⟩)) : False := by
  set θt := centerQuotAction G₀ ⟨t, htN⟩ with hθt
  set θs := centerQuotAction G₀ ⟨g⁻¹ * t * g, hg⟩ with hθs
  obtain ⟨ρ, η, p, hρ, hα, hηρ, ⟨β₀, hβ₀⟩, hfix⟩ := hsh
  set xb0 := ρ (siegDiag K p 1) with hxb0
  have hηx : η xb0 = xb0 := hηρ _
  have hxx : xb0 * xb0 = 1 := by rw [hxb0, ← map_mul, siegDiag_one_mul_self, map_one]
  have hFle : fixedSubgroup θs ≤ centralizer ({xb0} : Set (G₀ ⧸ center G₀)) := by
    rw [hfix]
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_singleton_iff, hxb0, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 hc]
  have hFperf : ⁅fixedSubgroup θs, fixedSubgroup θs⁆ = fixedSubgroup θs := by
    rw [hfix, ← Subgroup.map_commutator, commutator_centralizer_siegDiag_two hK hm p]
  have hFcard : Nat.card (fixedSubgroup θs) =
      Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))) := by
    rw [hfix, Subgroup.card_map_of_injective hρ]
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
  have hx₀N : (x₀ : G) ∈ normalizer (G₀ : Set G) := le_normalizer x₀.2
  have hsxN : (g⁻¹ * t * g) * x₀ ∈ normalizer (G₀ : Set G) := mul_mem hg hx₀N
  have hθη : centerQuotAction G₀ ⟨(g⁻¹ * t * g) * x₀, hsxN⟩ = η := by
    have e1 : (⟨(g⁻¹ * t * g) * x₀, hsxN⟩ : normalizer (G₀ : Set G)) =
        ⟨g⁻¹ * t * g, hg⟩ * ⟨x₀, hx₀N⟩ := rfl
    rw [e1, map_mul, show (⟨(x₀ : G), hx₀N⟩ : normalizer (G₀ : Set G)) =
      ⟨x₀, le_normalizer x₀.2⟩ from rfl, centerQuotAction_of_mem G₀ x₀.2, Subtype.coe_eta,
      hx₀π]
    change θs * MulAut.conj xb0 = η
    rw [hα, mul_assoc, mulAut_mul_conj_eq_of_apply_eq hηx, ← mul_assoc, ← map_mul, hxx,
      map_one, one_mul]
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
    have hhN : h⁻¹ * t * h ∈ normalizer (G₀ : Set G) := hht ▸ hsxN
    have hθh : centerQuotAction G₀ ⟨h⁻¹ * t * h, hhN⟩ = η := by
      have e1 : (⟨h⁻¹ * t * h, hhN⟩ : normalizer (G₀ : Set G)) = ⟨_, hsxN⟩ := Subtype.ext hht
      rw [e1, hθη]
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
    have hcardCt'2 : Nat.card (Ct'.map G₀.subtype) ≤
        Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))) := by
      rw [Subgroup.card_map_of_injective G₀.subtype_injective]
      exact (hcardCt'.trans hp₁).trans (card_centralizer_siegDiag_eq p₁ p 1).le
    have hchain : Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G) ≤
        Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))) :=
      (Subgroup.card_le_of_le hCL).trans hcardCt'2
    have hΛge : Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))) ≤
        Nat.card Λ := hFcard ▸ hFΛ
    have hΛeq : Λ = L ⊓ centralizer ({x} : Set G) :=
      Subgroup.eq_of_le_of_card_ge (le_inf hΛL hΛx) (hchain.trans hΛge)
    have hΛcard' : Nat.card Λ =
        Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))) :=
      le_antisymm (hΛeq ▸ hchain) hΛge
    have hΛθ' : Λ = Ct'.map G₀.subtype :=
      Subgroup.eq_of_le_of_card_ge (hΛeq ▸ hCL) (hcardCt'2.trans hΛge)
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
        Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))) := by
      rw [← Subgroup.card_map_of_injective L.subtype_injective, hmapC, ← hΛeq, hΛcard']
    have hxb01 : xb0 ≠ 1 := by
      intro h0
      apply siegDiag_one_ne_one (K := K) p
      apply hρ
      rw [map_one, ← hxb0, h0]
    have hx'1 : x' ≠ 1 := by
      intro h1
      have h2 : x = 1 := congrArg Subtype.val h1
      apply hxb01
      have h3 : (x₀ : G) = g⁻¹ * x * g := by rw [hx]; group
      have h4 : x₀ = 1 := Subtype.ext (by rw [h3, h2]; simp)
      rw [← hx₀π, h4, map_one]
    obtain ⟨c₁, hc₁⟩ := exists_conj_eq_siegDiag_two' hK (by omega) e hx'1 hCperf hCcard p
    set cG : G := (c₁ : G) with hcG
    have hcL : cG ∈ L := c₁.2
    have hxc : x = cG⁻¹ * ((e.symm (siegDiag K p 1) : L) : G) * cG := by
      have h1 := congrArg (fun y : L => (y : G)) hc₁
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [← h1, hcG]
      change x = (c₁ : G)⁻¹ * ((c₁ : G) * x * (c₁ : G)⁻¹) * (c₁ : G)
      group
    obtain ⟨k, hkp⟩ : ∃ k : Fin (m + 1), k ≠ p := by
      by_cases hp : (p : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hp; simp at hp⟩
      · exact ⟨⟨0, by omega⟩, fun h => hp (by rw [← h])⟩
    set ψL : StatedSp (m + 1) K →* G :=
      (MulAut.conj cG⁻¹).toMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom) with hψL
    have hψL_apply : ∀ y, ψL y = cG⁻¹ * ((e.symm y : L) : G) * cG := by
      intro y
      simp [hψL]
    have hψLinj : Function.Injective ψL := by
      intro a b hab
      rw [hψL_apply, hψL_apply] at hab
      have h1 : ((e.symm a : L) : G) = ((e.symm b : L) : G) := by
        have := congrArg (fun z => cG * z * cG⁻¹) hab
        simpa [mul_assoc] using this
      exact e.symm.injective (Subtype.ext h1)
    have hz : siegDiag K p 1 = e (c₁ * x' * c₁⁻¹) := by rw [hc₁, MulEquiv.apply_symm_apply]
    have hψLΛ : ∀ y ∈ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)), ψL y ∈ Λ := by
      intro y hy
      rw [hΛeq]
      refine ⟨?_, ?_⟩
      · rw [hψL_apply]
        exact L.mul_mem (L.mul_mem (L.inv_mem hcL) (e.symm y).2) hcL
      · show ψL y ∈ centralizer ({x} : Set G)
        rw [mem_centralizer_singleton_iff, hψL_apply, hxc]
        have hyz := mem_centralizer_singleton_iff.1 hy
        have h2 : ((e.symm y : L) : G) * ((e.symm (siegDiag K p 1) : L) : G) =
            ((e.symm (siegDiag K p 1) : L) : G) * ((e.symm y : L) : G) := by
          rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hyz]
        calc cG⁻¹ * ((e.symm y : L) : G) * cG *
              (cG⁻¹ * ((e.symm (siegDiag K p 1) : L) : G) * cG) =
            cG⁻¹ * (((e.symm y : L) : G) * ((e.symm (siegDiag K p 1) : L) : G)) * cG := by group
          _ = cG⁻¹ * (((e.symm (siegDiag K p 1) : L) : G) * ((e.symm y : L) : G)) * cG := by
              rw [h2]
          _ = cG⁻¹ * ((e.symm (siegDiag K p 1) : L) : G) * cG *
              (cG⁻¹ * ((e.symm y : L) : G) * cG) := by group
    have hf₁ : ∀ y : centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
        ∃ c₀ ∈ C₀, ((c₀ : G₀) : G) = g⁻¹ * ψL y * g := by
      intro y
      obtain ⟨c₀, hc₀, hc₀y⟩ := hψLΛ y y.2
      refine ⟨c₀, hc₀, ?_⟩
      have h1 : g * ((c₀ : G₀) : G) * g⁻¹ = ψL y := hc₀y
      rw [← h1]
      group
    have hf₁G : ∀ y : centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
        (MulAut.conj g⁻¹).toMonoidHom (ψL y) ∈ G₀ := by
      intro y
      obtain ⟨c₀, -, hc₀⟩ := hf₁ y
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [← hc₀]
      exact c₀.2
    set f₂ : centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) →* G₀ :=
      ((MulAut.conj g⁻¹).toMonoidHom.comp (ψL.comp
        (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))).subtype)).codRestrict G₀
          (fun y => hf₁G y) with hf₂
    have hf₂val : ∀ y, ((f₂ y : G₀) : G) = g⁻¹ * ψL y * g := by
      intro y
      simp [hf₂]
    have hf₂C : ∀ y, f₂ y ∈ C₀ := by
      intro y
      obtain ⟨c₀, hc₀, hc₀v⟩ := hf₁ y
      have : f₂ y = c₀ := Subtype.ext (by rw [hf₂val, hc₀v])
      rw [this]
      exact hc₀
    set ψb : centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) →* G₀ ⧸ center G₀ :=
      (QuotientGroup.mk' (center G₀)).comp f₂ with hψb
    set ρC : centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) →* G₀ ⧸ center G₀ :=
      ρ.comp (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))).subtype with hρC
    have hρCinj : Function.Injective ρC := hρ.comp Subtype.val_injective
    have hπC₀ : Function.Injective ((QuotientGroup.mk' (center G₀)).comp C₀.subtype) := by
      set πC : C₀ →* fixedSubgroup θs :=
        ((QuotientGroup.mk' (center G₀)).comp C₀.subtype).codRestrict (fixedSubgroup θs)
          (fun y => by rw [← hC₀map]; exact ⟨y, y.2, rfl⟩) with hπCdef
      have hsurj : Function.Surjective πC := by
        rintro ⟨w, hw⟩
        rw [← hC₀map] at hw
        obtain ⟨y, hy, rfl⟩ := hw
        exact ⟨⟨y, hy⟩, rfl⟩
      have hcard : Nat.card C₀ ≤ Nat.card (fixedSubgroup θs) := by
        rw [hFcard, ← hΛcard', hΛcard]
      have hbij := hsurj.bijective_of_nat_card_le hcard
      intro a b hab
      exact hbij.1 (Subtype.ext hab)
    have hψbinj : Function.Injective ψb := by
      intro a b hab
      have h1 : ((QuotientGroup.mk' (center G₀)).comp C₀.subtype) ⟨f₂ a, hf₂C a⟩ =
          ((QuotientGroup.mk' (center G₀)).comp C₀.subtype) ⟨f₂ b, hf₂C b⟩ := hab
      have h2 := congrArg (fun z : C₀ => ((z : G₀) : G)) (hπC₀ h1)
      simp only [hf₂val] at h2
      have h3 : ψL a = ψL b := by
        have := congrArg (fun z => g * z * g⁻¹) h2
        simpa [mul_assoc] using this
      exact Subtype.ext (hψLinj h3)
    have hψbC : ψb.range ≤ fixedSubgroup θs := by
      rintro _ ⟨y, rfl⟩
      rw [← hC₀map]
      exact ⟨f₂ y, hf₂C y, rfl⟩
    have hρCr : ρC.range = fixedSubgroup θs := by
      rw [hfix, hρC, MonoidHom.range_comp, Subgroup.range_subtype]
    have hrange : ψb.range = ρC.range := by
      refine Subgroup.eq_of_le_of_card_ge (hψbC.trans hρCr.ge) ?_
      rw [← Nat.card_congr (MonoidHom.ofInjective hρCinj).toEquiv,
        ← Nat.card_congr (MonoidHom.ofInjective hψbinj).toEquiv]
    obtain ⟨c', hc'C, hXmap⟩ :=
      exists_conj_map_nsTorusSp_eq_of_range_eq hK hm hkp hψbinj hρCinj hrange
    set Qb : Subgroup (G₀ ⧸ center G₀) :=
      ((complSp K k).map (MulAut.conj c').toMonoidHom).map ρ with hQb
    have hQbperf : ⁅Qb, Qb⁆ = Qb := by
      rw [hQb, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
        commutator_complSp_two hK hm k]
    have hQbη : Qb ≤ fixedSubgroup η := by
      rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact hηρ _
    have hQbX : ∀ q ∈ Qb, ∀ τ ∈ nsTorusSp K k,
        ∀ hτ : τ ∈ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
          q * ψb ⟨τ, hτ⟩ = ψb ⟨τ, hτ⟩ * q := by
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩ τ hτ hτC
      obtain ⟨x₂, hx₂, hx₂C, hτC', heq⟩ := hXmap τ hτ
      have heq' : ψb ⟨τ, hτC⟩ = ρC ⟨c' * x₂ * c'⁻¹, hx₂C⟩ := heq
      rw [heq']
      have hyx : x₂ * y = y * x₂ :=
        mem_centralizer_iff.1 (complSp_le_centralizer_nsTorusSp k hy) x₂ hx₂
      change ρ ((MulAut.conj c').toMonoidHom y) * ρ (c' * x₂ * c'⁻¹) =
        ρ (c' * x₂ * c'⁻¹) * ρ ((MulAut.conj c').toMonoidHom y)
      rw [← map_mul, ← map_mul]
      congr 1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc c' * y * c'⁻¹ * (c' * x₂ * c'⁻¹) = c' * (y * x₂) * c'⁻¹ := by group
        _ = c' * (x₂ * y) * c'⁻¹ := by rw [hyx]
        _ = c' * x₂ * c'⁻¹ * (c' * y * c'⁻¹) := by group
    obtain ⟨F, hF⟩ : ∃ F, F = fixedSubgroup (G₀.normalizerMonoidHom ⟨(g⁻¹ * t * g) * x₀, hsxN⟩) :=
      ⟨_, rfl⟩
    have hsx2 : ((g⁻¹ * t * g) * (x₀ : G)) * ((g⁻¹ * t * g) * x₀) = 1 := by
      have hs1 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := mul_self_inv_conj_eq_one htt g
      calc ((g⁻¹ * t * g) * (x₀ : G)) * ((g⁻¹ * t * g) * x₀) =
          (g⁻¹ * t * g) * ((x₀ : G) * (g⁻¹ * t * g)) * x₀ := by group
        _ = (g⁻¹ * t * g) * ((g⁻¹ * t * g) * x₀) * x₀ := by rw [hsx]
        _ = ((g⁻¹ * t * g) * (g⁻¹ * t * g)) * ((x₀ : G) * x₀) := by group
        _ = 1 := by rw [hs1, hx0, one_mul]
    have hFmap : Qb ≤ F.map (QuotientGroup.mk' (center G₀)) := by
      by_cases hw1 : (g⁻¹ * t * g) * (x₀ : G) = 1
      · intro q _
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center G₀) q
        refine ⟨y, ?_, rfl⟩
        rw [hF]
        show G₀.normalizerMonoidHom ⟨(g⁻¹ * t * g) * x₀, hsxN⟩ y = y
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        change (g⁻¹ * t * g) * (x₀ : G) * (y : G) * ((g⁻¹ * t * g) * (x₀ : G))⁻¹ = y
        rw [hw1, one_mul, inv_one, mul_one]
      · have hw2 : orderOf ((g⁻¹ * t * g) * (x₀ : G)) = 2 :=
          orderOf_eq_prime (by rw [_root_.sq]; exact hsx2) hw1
        rw [hF, map_mk_fixedSubgroup_eq_centerQuot hZ hw2 hsxN, hθη]
        exact hQbη
    obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : Subgroup G₀,
        Q₀ = perfectCore (Qb.comap (QuotientGroup.mk' (center G₀)) ⊓ F) := ⟨_, rfl⟩
    have hQ₀map : Q₀.map (QuotientGroup.mk' (center G₀)) = Qb := by
      have h1 : (Qb.comap (QuotientGroup.mk' (center G₀)) ⊓ F).map
          (QuotientGroup.mk' (center G₀)) = Qb := by
        refine le_antisymm ?_ ?_
        · rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
          exact hy
        · intro q hq
          obtain ⟨y, hyF, rfl⟩ := hFmap hq
          exact ⟨y, ⟨hq, hyF⟩, rfl⟩
      rw [hQ₀, map_perfectCore, h1, perfectCore_eq_self_of_perfect hQbperf]
    have hQ₀perf : ⁅Q₀, Q₀⁆ = Q₀ := by rw [hQ₀]; exact perfectCore_perfect _
    have hQ₀F : Q₀ ≤ F := by rw [hQ₀]; exact (perfectCore_le _).trans inf_le_right
    have hQ₀τ : ∀ τ ∈ nsTorusSp K k,
        ∀ hτ : τ ∈ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
          ∀ q ∈ Q₀, q * f₂ ⟨τ, hτ⟩ = f₂ ⟨τ, hτ⟩ * q := by
      intro τ hτ hτC
      refine commute_of_perfect_of_mk_commute hQ₀perf fun q hq => ?_
      have hqb : QuotientGroup.mk' (center G₀) q ∈ Qb := by
        rw [← hQ₀map]
        exact ⟨q, hq, rfl⟩
      have h1 := hQbX _ hqb τ hτ hτC
      change QuotientGroup.mk' (center G₀) (q * f₂ ⟨τ, hτC⟩) =
        QuotientGroup.mk' (center G₀) (f₂ ⟨τ, hτC⟩ * q)
      rw [map_mul, map_mul]
      exact h1
    obtain ⟨P, hP⟩ : ∃ P : Subgroup G, P = Q₀.map c := ⟨_, rfl⟩
    have hPperf : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hQ₀perf]
    have hPX : ∀ y ∈ P, ∀ τ ∈ nsTorusSp K k, y * ψL τ = ψL τ * y := by
      rw [hP]
      rintro _ ⟨q, hq, rfl⟩ τ hτ
      have hτC : τ ∈ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) :=
        (nsTorusSp_le_complSp hkp).trans complSp_le_centralizer_siegDiag hτ
      have h1 := congrArg Subtype.val (hQ₀τ τ hτ hτC q hq)
      simp only [Subgroup.coe_mul] at h1
      rw [hf₂val] at h1
      simp only [hc, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * (q : G) * g⁻¹ * ψL τ = g * ((q : G) * (g⁻¹ * ψL τ * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * ψL τ * g) * (q : G)) * g⁻¹ := by rw [h1]
        _ = ψL τ * (g * (q : G) * g⁻¹) := by group
    have hPG : P ≤ G₀ := by
      set P' : Subgroup G := P.map (MulAut.conj cG).toMonoidHom with hP'
      have hP'perf : ⁅P', P'⁆ = P' := by rw [hP', ← Subgroup.map_commutator, hPperf]
      have hP'c : P' ≤ centralizer (modelToG e (nsTorusSp K k) : Set G) := by
        rintro _ ⟨y, hy, rfl⟩
        rw [mem_centralizer_iff]
        intro w hw
        obtain ⟨τ, hτ, rfl⟩ := (mem_modelToG e).1 hw
        have h1 := hPX y hy τ hτ
        rw [hψL_apply] at h1
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc ((e.symm τ : L) : G) * (cG * y * cG⁻¹) =
            cG * ((cG⁻¹ * ((e.symm τ : L) : G) * cG) * y) * cG⁻¹ := by group
          _ = cG * (y * (cG⁻¹ * ((e.symm τ : L) : G) * cG)) * cG⁻¹ := by rw [h1]
          _ = cG * y * cG⁻¹ * ((e.symm τ : L) : G) := by group
      have hP'le := htorus k P' hP'perf hP'c
      intro y hy
      have h1 : cG * y * cG⁻¹ ∈ G₀ := hP'le ⟨y, hy, rfl⟩
      have hcG0 : cG ∈ G₀ := hLS hcL
      have e1 : y = cG⁻¹ * (cG * y * cG⁻¹) * cG := by group
      rw [e1]
      exact G₀.mul_mem (G₀.mul_mem (G₀.inv_mem hcG0) h1) hcG0
    have hPt' : ∀ y ∈ P, y * (t * x) = (t * x) * y := by
      rw [hP]
      rintro _ ⟨q, hq, rfl⟩
      have hqF := hQ₀F hq
      rw [hF] at hqF
      have hqF' : G₀.normalizerMonoidHom ⟨(g⁻¹ * t * g) * x₀, hsxN⟩ q = q := hqF
      have h1 := congrArg Subtype.val hqF'
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
      change (g⁻¹ * t * g) * (x₀ : G) * (q : G) * ((g⁻¹ * t * g) * (x₀ : G))⁻¹ = q at h1
      have htx' : t * x = g * ((g⁻¹ * t * g) * x₀) * g⁻¹ := by rw [hx]; group
      have h2 : (q : G) * ((g⁻¹ * t * g) * x₀) = ((g⁻¹ * t * g) * x₀) * q := by
        calc (q : G) * ((g⁻¹ * t * g) * x₀) =
            ((g⁻¹ * t * g) * x₀ * (q : G) * ((g⁻¹ * t * g) * x₀)⁻¹) *
              ((g⁻¹ * t * g) * x₀) := by rw [h1]
          _ = ((g⁻¹ * t * g) * x₀) * q := by group
      simp only [hc, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [htx']
      calc g * (q : G) * g⁻¹ * (g * ((g⁻¹ * t * g) * x₀) * g⁻¹) =
          g * ((q : G) * ((g⁻¹ * t * g) * x₀)) * g⁻¹ := by group
        _ = g * (((g⁻¹ * t * g) * x₀) * q) * g⁻¹ := by rw [h2]
        _ = g * ((g⁻¹ * t * g) * x₀) * g⁻¹ * (g * (q : G) * g⁻¹) := by group
    have hPΛ : P ≤ Λ := by
      rw [hΛθ']
      intro y hy
      refine ⟨⟨y, hPG hy⟩, ?_, rfl⟩
      show G₀.normalizerMonoidHom ⟨t * x, ht'N⟩ ⟨y, hPG hy⟩ = ⟨y, hPG hy⟩
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change t * x * y * (t * x)⁻¹ = y
      rw [← hPt' y hy]
      group
    have hPx : P ≤ centralizer ({x} : Set G) := hPΛ.trans hΛx
    have hQbx : Qb ≤ centralizer ({xb0} : Set (G₀ ⧸ center G₀)) := by
      rw [← hQ₀map]
      rintro _ ⟨q, hq, rfl⟩
      have hqP : c q ∈ P := by rw [hP]; exact ⟨q, hq, rfl⟩
      have h1 := mem_centralizer_singleton_iff.1 (hPx hqP)
      simp only [hc, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      have h2 : (q : G) * x₀ = x₀ * q := by
        have := congrArg (fun z => g⁻¹ * z * g) h1
        simp only [hx] at this
        calc (q : G) * x₀ = g⁻¹ * (g * (q : G) * g⁻¹ * (g * x₀ * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * x₀ * g⁻¹ * (g * (q : G) * g⁻¹)) * g := this
          _ = x₀ * q := by group
      rw [mem_centralizer_singleton_iff, ← hx₀π, ← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext h2)
    apply not_complSp_le_centralizer_siegDiag (K := K) hkp
    intro y hy
    have h1 := mem_centralizer_singleton_iff.1 (hQbx ⟨_, ⟨y, hy, rfl⟩, rfl⟩)
    rw [hxb0, ← map_mul, ← map_mul] at h1
    have h2 := hρ h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2
    have hc'z : c' * siegDiag K p 1 = siegDiag K p 1 * c' := mem_centralizer_singleton_iff.1 hc'C
    have hz1 : c' * siegDiag K p 1 * c'⁻¹ = siegDiag K p 1 := by rw [hc'z]; group
    have hz2 : c'⁻¹ * siegDiag K p 1 * c' = siegDiag K p 1 := by
      calc c'⁻¹ * siegDiag K p 1 * c' = c'⁻¹ * (siegDiag K p 1 * c') := by group
        _ = c'⁻¹ * (c' * siegDiag K p 1) := by rw [hc'z]
        _ = siegDiag K p 1 := by group
    rw [mem_centralizer_singleton_iff]
    calc y * siegDiag K p 1 =
        c'⁻¹ * ((c' * y * c'⁻¹) * (c' * siegDiag K p 1 * c'⁻¹)) * c' := by group
      _ = c'⁻¹ * ((c' * y * c'⁻¹) * siegDiag K p 1) * c' := by rw [hz1]
      _ = c'⁻¹ * (siegDiag K p 1 * (c' * y * c'⁻¹)) * c' := by rw [h2]
      _ = (c'⁻¹ * siegDiag K p 1 * c') * y := by group
      _ = siegDiag K p 1 * y := by rw [hz2]

end Main

end CFSG.SeitzReduction.SymplecticPilot

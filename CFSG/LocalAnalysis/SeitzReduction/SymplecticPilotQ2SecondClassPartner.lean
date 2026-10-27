module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SecondClassAut
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)

section Defs

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] def NsPartnerShape {n : ℕ} (e : L ≃* StatedSp n K) (θ α : MulAut (nsGlobal e)) :
    Prop :=
  ∃ (ρ : StatedSp n K →* nsGlobal e) (η : MulAut (nsGlobal e)) (p : Fin n),
    Function.Injective ρ ∧ α = MulAut.conj (ρ (siegDiag K p 1)) * η ∧
    (∀ y : StatedSp n K, η (ρ y) = ρ y) ∧ (∃ β : MulAut (nsGlobal e), β * θ = η * β) ∧
    fixedSubgroup α = (centralizer ({siegDiag K p 1} : Set (StatedSp n K))).map ρ

@[expose] def NsCosetCardInput {n : ℕ} (e : L ≃* StatedSp n K) (θ : MulAut (nsGlobal e)) :
    Prop :=
  ∀ y : nsGlobal e, (MulAut.conj y * θ) * (MulAut.conj y * θ) = 1 →
    (∃ β : MulAut (nsGlobal e), β * θ = (MulAut.conj y * θ) * β) ∨
      ∃ p : Fin n, Nat.card (fixedSubgroup (MulAut.conj y * θ)) ≤
        Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp n K)))

end Defs

section Helpers

variable {K : Type} [Field K] [CharP K 2]

theorem not_complSp_le_centralizer_siegDiag {m : ℕ} {p k : Fin (m + 1)} (hkp : k ≠ p) :
    ¬ complSp K k ≤ centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) := by
  intro h
  have hz : siegDiag K p 1 ∈ complSp K k :=
    longRootSp2_le_complSp hkp (siegDiag_mem_longRootSp2 p 1)
  set z' : complSp K k := ⟨siegDiag K p 1, hz⟩ with hz'
  have hzc : (complSpEquiv (K := K) k).symm z' ∈ center (StatedSp m K) := by
    rw [mem_center_iff]
    intro w
    apply (complSpEquiv (K := K) k).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    have h1 := mem_centralizer_singleton_iff.1 (h (complSpEquiv (K := K) k w).2)
    simpa [z'] using h1
  rw [center_statedSp_eq_bot, mem_bot] at hzc
  apply siegDiag_one_ne_one (K := K) p
  have h2 := congrArg (fun y => ((complSpEquiv (K := K) k y : complSp K k) : StatedSp (m + 1) K))
    hzc
  simpa [z'] using h2

theorem exists_conj_eq_siegDiag_two' [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : 2 ≤ m)
    {X : Type*} [Group X] [Finite X] (e : X ≃* StatedSp (m + 1) K) {x : X} (hx : x ≠ 1)
    (hperf : ⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆ = centralizer ({x} : Set X))
    {p : Fin (m + 1)}
    (hcard : Nat.card (centralizer ({x} : Set X)) =
      Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))))
    (p' : Fin (m + 1)) :
    ∃ c : X, c * x * c⁻¹ = e.symm (siegDiag K p' 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  exact exists_conj_eq_siegDiag_two hK e hx hperf hcard p'

end Helpers

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem false_of_nsPartnerShape (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (htN : t ∈ normalizer (nsGlobal e : Set G))
    (hodd : Odd (Nat.card (centralizer (nsGlobal e : Set G))))
    (hInn : CosetInnConjInput ((nsGlobal e).normalizerMonoidHom ⟨t, htN⟩))
    (hDich : NsCosetCardInput e ((nsGlobal e).normalizerMonoidHom ⟨t, htN⟩))
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G))
    (hsh : NsPartnerShape e ((nsGlobal e).normalizerMonoidHom ⟨t, htN⟩)
      ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩)) : False := by
  set G₀ := nsGlobal e with hG₀
  set θt := G₀.normalizerMonoidHom ⟨t, htN⟩ with hθt
  set θs := G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ with hθs
  obtain ⟨ρ, η, p, hρ, hα, hηρ, ⟨β₀, hβ₀⟩, hfix⟩ := hsh
  set x₀ : G₀ := ρ (siegDiag K p 1) with hx₀def
  have hηx : η x₀ = x₀ := hηρ _
  have hxx : x₀ * x₀ = 1 := by rw [hx₀def, ← map_mul, siegDiag_one_mul_self, map_one]
  have hFle : fixedSubgroup θs ≤ centralizer ({x₀} : Set G₀) := by
    rw [hfix]
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_singleton_iff, hx₀def, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 hc]
  have hFperf : ⁅fixedSubgroup θs, fixedSubgroup θs⁆ = fixedSubgroup θs := by
    rw [hfix, ← Subgroup.map_commutator, commutator_centralizer_siegDiag_two hK hm p]
  have hFcard : Nat.card (fixedSubgroup θs) =
      Nat.card (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))) := by
    rw [hfix, Subgroup.card_map_of_injective hρ]
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hLS : L ≤ G₀ := le_nsGlobal hK hm e
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega) e)
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)
  have hact : ∀ y : G₀, ((θs y : G₀) : G) = (g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hθx : θs x₀ = x₀ := by
    rw [hα, MulAut.mul_apply, hηx, MulAut.conj_apply, mul_inv_cancel_right]
  set x : G := g * x₀ * g⁻¹ with hx
  have hsx : (g⁻¹ * t * g) * (x₀ : G) = x₀ * (g⁻¹ * t * g) := by
    have h1 := hact x₀
    rw [hθx] at h1
    calc (g⁻¹ * t * g) * (x₀ : G) =
        ((g⁻¹ * t * g) * x₀ * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g) := by group
      _ = x₀ * (g⁻¹ * t * g) := by rw [← h1]
  have htx : t * x = x * t := by
    calc t * x = g * ((g⁻¹ * t * g) * x₀) * g⁻¹ := by rw [hx]; group
      _ = g * (x₀ * (g⁻¹ * t * g)) * g⁻¹ := by rw [hsx]
      _ = x * t := by rw [hx]; group
  have hx0 : (x₀ : G) * x₀ = 1 := by
    have h1 := congrArg Subtype.val hxx
    simpa using h1
  have hx2 : x * x = 1 := by
    calc x * x = g * ((x₀ : G) * x₀) * g⁻¹ := by rw [hx]; group
      _ = 1 := by rw [hx0]; group
  set Λ : Subgroup G := (fixedSubgroup θs).map ((MulAut.conj g).toMonoidHom.comp G₀.subtype)
    with hΛ
  have hinj : Function.Injective ((MulAut.conj g).toMonoidHom.comp G₀.subtype) :=
    (MulAut.conj g).injective.comp G₀.subtype_injective
  have hΛcard : Nat.card Λ = Nat.card (fixedSubgroup θs) := Subgroup.card_map_of_injective hinj
  have hΛperf : ⁅Λ, Λ⁆ = Λ := by rw [hΛ, ← Subgroup.map_commutator, hFperf]
  have hΛt : Λ ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := hact y
    have hy' : θs y = y := hy
    rw [hy'] at h1
    have hys : (y : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y := by
      calc (y : G) * (g⁻¹ * t * g) =
          ((g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g) := by rw [← h1]
        _ = (g⁻¹ * t * g) * y := by group
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * (y : G) * g⁻¹ * t = g * ((y : G) * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * y) * g⁻¹ := by rw [hys]
      _ = t * (g * y * g⁻¹) := by group
  have hΛL : Λ ≤ L := std_perfect_le hset.standardSetting hOut htC ht hΛperf hΛt
  have hxΛ : x ∈ Λ := ⟨x₀, hθx, rfl⟩
  have hxL : x ∈ L := hΛL hxΛ
  have hxG : x ∈ G₀ := hLS hxL
  have hΛx : Λ ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : y * x₀ = x₀ * y := mem_centralizer_singleton_iff.1 (hFle hy)
    have h2 : (y : G) * x₀ = x₀ * y := congrArg Subtype.val h1
    rw [mem_centralizer_singleton_iff]
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * (y : G) * g⁻¹ * x = g * ((y : G) * x₀) * g⁻¹ := by rw [hx]; group
      _ = g * (x₀ * y) * g⁻¹ := by rw [h2]
      _ = x * (g * y * g⁻¹) := by rw [hx]; group
  have hxN : x ∈ normalizer (G₀ : Set G) := le_normalizer hxG
  have ht'N : t * x ∈ normalizer (G₀ : Set G) := mul_mem htN hxN
  have hθ' : G₀.normalizerMonoidHom ⟨t * x, ht'N⟩ = MulAut.conj (⟨x, hxG⟩ : G₀) * θt := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.mul_apply, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hθt,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    change t * x * (y : G) * (t * x)⁻¹ = x * (t * y * t⁻¹) * x⁻¹
    rw [htx]
    group
  have ht'2 : (t * x) * (t * x) = 1 := by
    calc (t * x) * (t * x) = t * (x * t) * x := by group
      _ = t * (t * x) * x := by rw [htx]
      _ = (t * t) * (x * x) := by group
      _ = 1 := by rw [htt, hx2, one_mul]
  have hθ'2 : (MulAut.conj (⟨x, hxG⟩ : G₀) * θt) * (MulAut.conj (⟨x, hxG⟩ : G₀) * θt) = 1 := by
    rw [← hθ', ← map_mul,
      show (⟨t * x, ht'N⟩ : normalizer (G₀ : Set G)) * ⟨t * x, ht'N⟩ = 1 from Subtype.ext ht'2,
      map_one]
  have hfixLt : Nat.card (fixedSubgroup θs) < Nat.card L := by
    rw [hFcard, Nat.card_congr e.toEquiv]
    exact card_centralizer_siegDiag_lt p
  have hx₀N : (x₀ : G) ∈ normalizer (G₀ : Set G) := le_normalizer x₀.2
  have hsxN : (g⁻¹ * t * g) * x₀ ∈ normalizer (G₀ : Set G) := mul_mem hg hx₀N
  have hθη : G₀.normalizerMonoidHom ⟨(g⁻¹ * t * g) * x₀, hsxN⟩ = η := by
    rw [normalizerMonoidHom_mul' hg hx₀N hsxN, normalizerMonoidHom_eq_conj_of_mem x₀.2 hx₀N]
    change θs * MulAut.conj x₀ = η
    rw [hα, mul_assoc, mulAut_mul_conj_eq_of_apply_eq hηx, ← mul_assoc, ← map_mul, hxx,
      map_one, one_mul]
  rcases hDich ⟨x, hxG⟩ hθ'2 with hstd | ⟨p₁, hp₁⟩
  ·
    obtain ⟨z, hz⟩ := hInn ⟨x, hxG⟩ hθ'2 hstd
    have hzN : (z : G) ∈ normalizer (G₀ : Set G) := le_normalizer z.2
    have hztN : (z : G) * t * (z : G)⁻¹ ∈ normalizer (G₀ : Set G) :=
      mul_mem (mul_mem hzN htN) (inv_mem hzN)
    have hθz : G₀.normalizerMonoidHom ⟨(z : G) * t * (z : G)⁻¹, hztN⟩ =
        MulAut.conj z * θt * (MulAut.conj z)⁻¹ := by
      rw [normalizerMonoidHom_mul' (mul_mem hzN htN) (inv_mem hzN) hztN,
        normalizerMonoidHom_mul' hzN htN (mul_mem hzN htN),
        normalizerMonoidHom_eq_conj_of_mem z.2 hzN,
        normalizerMonoidHom_eq_conj_of_mem (inv_mem z.2) (inv_mem hzN),
        ← map_inv]
      rfl
    have hzt2 : ((z : G) * t * (z : G)⁻¹) * ((z : G) * t * (z : G)⁻¹) = 1 := by
      calc ((z : G) * t * (z : G)⁻¹) * ((z : G) * t * (z : G)⁻¹) =
          (z : G) * (t * t) * (z : G)⁻¹ := by group
        _ = 1 := by rw [htt]; group
    obtain ⟨c, hcC, hc⟩ := exists_conj_eq_of_normalizerMonoidHom_eq hodd hzt2 ht'2 hztN ht'N
      (by rw [hθz, hθ', hz])
    have hcN : c ∈ normalizer (G₀ : Set G) := centralizer_le_normalizer _ hcC
    set nn : G := c * z with hnn
    have hnnN : nn ∈ normalizer (G₀ : Set G) := mul_mem hcN hzN
    have hnt : nn * t * nn⁻¹ = t * x := by
      rw [hc, hnn]
      group
    set h : G := nn⁻¹ * g with hh
    have hht : h⁻¹ * t * h = (g⁻¹ * t * g) * x₀ := by
      calc h⁻¹ * t * h = g⁻¹ * (nn * t * nn⁻¹) * g := by rw [hh]; group
        _ = g⁻¹ * (t * x) * g := by rw [hnt]
        _ = (g⁻¹ * t * g) * x₀ := by rw [hx]; group
    have hhN : h⁻¹ * t * h ∈ normalizer (G₀ : Set G) := hht ▸ hsxN
    have hθh : G₀.normalizerMonoidHom ⟨h⁻¹ * t * h, hhN⟩ = η := by
      have e1 : (⟨h⁻¹ * t * h, hhN⟩ : normalizer (G₀ : Set G)) = ⟨_, hsxN⟩ := Subtype.ext hht
      rw [e1, hθη]
    have hhG : h ∈ normalizer (G₀ : Set G) :=
      mem_normalizer_nsGlobal_of_conj_mulAut hset hK hm e ht hKt htN hhN β₀
        (by rw [hθh]; exact hβ₀)
    have hgG : g ∈ normalizer (G₀ : Set G) := by
      have : g = nn * h := by rw [hh]; group
      rw [this]
      exact mul_mem hnnN hhG
    exact absurd (card_le_card_fixedSubgroup_of_mem_normalizer hLS hLt hgG hg) (not_le.2 hfixLt)
  ·
    rw [← hθ'] at hp₁
    set θ' := G₀.normalizerMonoidHom ⟨t * x, ht'N⟩ with hθ'def
    have hCL : L ⊓ centralizer ({x} : Set G) ≤ (fixedSubgroup θ').map G₀.subtype := by
      rintro l ⟨hl, hlx⟩
      refine ⟨⟨l, hLS hl⟩, ?_, rfl⟩
      show θ' ⟨l, hLS hl⟩ = ⟨l, hLS hl⟩
      apply Subtype.ext
      rw [hθ'def, Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hlx' : l * x = x * l := mem_centralizer_singleton_iff.1 hlx
      have hlt' : l * t = t * l := mem_centralizer_iff.1 htC l hl
      change t * x * l * (t * x)⁻¹ = l
      calc t * x * l * (t * x)⁻¹ = t * (x * l) * x⁻¹ * t⁻¹ := by group
        _ = t * (l * x) * x⁻¹ * t⁻¹ := by rw [hlx']
        _ = (t * l) * t⁻¹ := by group
        _ = l := by rw [← hlt']; group
    have hcardθ' : Nat.card ((fixedSubgroup θ').map G₀.subtype) ≤ Nat.card Λ := by
      rw [Subgroup.card_map_of_injective G₀.subtype_injective, hΛcard, hFcard]
      exact hp₁.trans (card_centralizer_siegDiag_eq p₁ p 1).le
    have hcardCL : Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ Nat.card Λ :=
      (Subgroup.card_le_of_le hCL).trans hcardθ'
    have hΛeq : Λ = L ⊓ centralizer ({x} : Set G) :=
      Subgroup.eq_of_le_of_card_ge (le_inf hΛL hΛx) hcardCL
    have hΛθ' : Λ = (fixedSubgroup θ').map G₀.subtype :=
      Subgroup.eq_of_le_of_card_ge (hΛeq ▸ hCL) hcardθ'
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
      rw [← Subgroup.card_map_of_injective L.subtype_injective, hmapC, ← hΛeq, hΛcard, hFcard]
    have hx₀1 : (x₀ : G) ≠ 1 := by
      intro h0
      apply siegDiag_one_ne_one (K := K) p
      apply hρ
      rw [map_one]
      exact Subtype.ext h0
    have hx'1 : x' ≠ 1 := by
      intro h1
      have h2 : x = 1 := congrArg Subtype.val h1
      apply hx₀1
      have h3 : (x₀ : G) = g⁻¹ * x * g := by rw [hx]; group
      rw [h3, h2]
      group
    obtain ⟨c, hc⟩ := exists_conj_eq_siegDiag_two' hK (by omega) e hx'1 hCperf hCcard p
    set cG : G := (c : G) with hcG
    have hcL : cG ∈ L := c.2
    have hxc : x = cG⁻¹ * ((e.symm (siegDiag K p 1) : L) : G) * cG := by
      have h1 := congrArg (fun y : L => (y : G)) hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [← h1, hcG]
      change x = (c : G)⁻¹ * ((c : G) * x * (c : G)⁻¹) * (c : G)
      group
    obtain ⟨k, hkp⟩ : ∃ k : Fin (m + 1), k ≠ p := by
      by_cases hp : (p : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hp; simp at hp⟩
      · exact ⟨⟨0, by omega⟩, fun h => hp (by rw [← h])⟩
    set ψL : StatedSp (m + 1) K →* G :=
      (MulAut.conj cG⁻¹).toMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom) with hψL
    set ψJ : StatedSp (m + 1) K →* G :=
      (MulAut.conj g).toMonoidHom.comp (G₀.subtype.comp ρ) with hψJ
    have hψL_apply : ∀ y, ψL y = cG⁻¹ * ((e.symm y : L) : G) * cG := by
      intro y
      simp [hψL]
    have hψJ_apply : ∀ y, ψJ y = g * ((ρ y : G₀) : G) * g⁻¹ := by
      intro y
      simp [hψJ]
    have hψLinj : Function.Injective ψL := by
      intro a b hab
      rw [hψL_apply, hψL_apply] at hab
      have h1 : ((e.symm a : L) : G) = ((e.symm b : L) : G) := by
        have := congrArg (fun z => cG * z * cG⁻¹) hab
        simpa [mul_assoc] using this
      exact e.symm.injective (Subtype.ext h1)
    have hψJinj : Function.Injective ψJ := by
      intro a b hab
      rw [hψJ_apply, hψJ_apply] at hab
      have h1 : ((ρ a : G₀) : G) = ((ρ b : G₀) : G) := by
        have := congrArg (fun z => g⁻¹ * z * g) hab
        simpa [mul_assoc] using this
      exact hρ (Subtype.ext h1)
    have hψJC : (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))).map ψJ = Λ := by
      rw [hΛ, hfix, Subgroup.map_map]
      rfl
    have hz : siegDiag K p 1 = e (c * x' * c⁻¹) := by rw [hc, MulEquiv.apply_symm_apply]
    have hψLC : (centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))).map ψL = Λ := by
      rw [hΛeq]
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
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
      · rintro w ⟨hwL, hwx⟩
        set w' : L := ⟨w, hwL⟩ with hw'
        have hw'x : w' * x' = x' * w' := Subtype.ext (mem_centralizer_singleton_iff.1 hwx)
        refine ⟨e (c * w' * c⁻¹), ?_, ?_⟩
        · rw [SetLike.mem_coe, mem_centralizer_singleton_iff, hz, ← map_mul, ← map_mul]
          congr 1
          calc c * w' * c⁻¹ * (c * x' * c⁻¹) = c * (w' * x') * c⁻¹ := by group
            _ = c * (x' * w') * c⁻¹ := by rw [hw'x]
            _ = c * x' * c⁻¹ * (c * w' * c⁻¹) := by group
        · rw [hψL_apply, MulEquiv.symm_apply_apply]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcG]
          change (c : G)⁻¹ * ((c : G) * w * (c : G)⁻¹) * (c : G) = w
          group
    obtain ⟨c', hc'C, hXeq⟩ := exists_conj_map_nsTorusSp_eq hK hm hkp hψLinj hψJinj
      (hψLC.trans hψJC.symm)
    set Q₀ : Subgroup G := ((complSp K k).map (MulAut.conj c').toMonoidHom).map ψJ with hQ₀
    have hQ₀perf : ⁅Q₀, Q₀⁆ = Q₀ := by
      rw [hQ₀, ← Subgroup.map_commutator, ← Subgroup.map_commutator, commutator_complSp_two hK hm k]
    have hQ₀X : Q₀ ≤ centralizer (((nsTorusSp K k).map ψL : Subgroup G) : Set G) := by
      rw [hXeq]
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
      have hyτ : τ * y = y * τ := mem_centralizer_iff.1 (complSp_le_centralizer_nsTorusSp k hy) τ hτ
      have key : (MulAut.conj c').toMonoidHom τ * (MulAut.conj c').toMonoidHom y =
          (MulAut.conj c').toMonoidHom y * (MulAut.conj c').toMonoidHom τ := by
        rw [← map_mul, hyτ, map_mul]
      rw [← map_mul, key, map_mul]
    have hQ₀G : Q₀ ≤ G₀ := by
      intro q hq
      set P' : Subgroup G := Q₀.map (MulAut.conj cG).toMonoidHom with hP'
      have hP'perf : ⁅P', P'⁆ = P' := by rw [hP', ← Subgroup.map_commutator, hQ₀perf]
      have hP'c : P' ≤ centralizer (modelToG e (nsTorusSp K k) : Set G) := by
        rintro _ ⟨q', hq', rfl⟩
        rw [mem_centralizer_iff]
        intro w hw
        obtain ⟨τ, hτ, rfl⟩ := (mem_modelToG e).1 hw
        have hτX : cG⁻¹ * ((e.symm τ : L) : G) * cG ∈ (nsTorusSp K k).map ψL :=
          ⟨τ, hτ, hψL_apply τ⟩
        have h1 := mem_centralizer_iff.1 (hQ₀X hq') _ hτX
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc ((e.symm τ : L) : G) * (cG * q' * cG⁻¹) =
            cG * ((cG⁻¹ * ((e.symm τ : L) : G) * cG) * q') * cG⁻¹ := by group
          _ = cG * (q' * (cG⁻¹ * ((e.symm τ : L) : G) * cG)) * cG⁻¹ := by rw [h1]
          _ = cG * q' * cG⁻¹ * ((e.symm τ : L) : G) := by group
      have hP'le : P' ≤ G₀ := (F4Pilot.le_centralizerPerfectCore hP'perf hP'c).trans (by
        rw [hG₀, nsGlobal_def]
        exact le_iSup (fun i : Fin (m + 1) =>
          centralizerPerfectCore (modelToG e (nsTorusSp K i))) k)
      have h1 : cG * q * cG⁻¹ ∈ G₀ := hP'le ⟨q, hq, rfl⟩
      have hcG0 : cG ∈ G₀ := hLS hcL
      have e1 : q = cG⁻¹ * (cG * q * cG⁻¹) * cG := by group
      rw [e1]
      exact G₀.mul_mem (G₀.mul_mem (G₀.inv_mem hcG0) h1) hcG0
    have hQ₀t' : ∀ q ∈ Q₀, q * (t * x) = (t * x) * q := by
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      set w := (MulAut.conj c').toMonoidHom y with hw
      have hfixz : G₀.normalizerMonoidHom ⟨(g⁻¹ * t * g) * x₀, hsxN⟩ (ρ w) = ρ w := by
        rw [hθη]
        exact hηρ w
      have h1 := congrArg Subtype.val hfixz
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
      have htx' : t * x = g * ((g⁻¹ * t * g) * x₀) * g⁻¹ := by rw [hx]; group
      have h2 : ((ρ w : G₀) : G) * ((g⁻¹ * t * g) * x₀) =
          ((g⁻¹ * t * g) * x₀) * ((ρ w : G₀) : G) := by
        calc ((ρ w : G₀) : G) * ((g⁻¹ * t * g) * x₀) =
            ((g⁻¹ * t * g) * x₀ * ((ρ w : G₀) : G) * ((g⁻¹ * t * g) * x₀)⁻¹) *
              ((g⁻¹ * t * g) * x₀) := by rw [h1]
          _ = ((g⁻¹ * t * g) * x₀) * ((ρ w : G₀) : G) := by group
      rw [hψJ_apply, htx']
      calc g * ((ρ w : G₀) : G) * g⁻¹ * (g * ((g⁻¹ * t * g) * x₀) * g⁻¹) =
          g * (((ρ w : G₀) : G) * ((g⁻¹ * t * g) * x₀)) * g⁻¹ := by group
        _ = g * (((g⁻¹ * t * g) * x₀) * ((ρ w : G₀) : G)) * g⁻¹ := by rw [h2]
        _ = g * ((g⁻¹ * t * g) * x₀) * g⁻¹ * (g * ((ρ w : G₀) : G) * g⁻¹) := by group
    have hQ₀Λ : Q₀ ≤ Λ := by
      rw [hΛθ']
      intro q hq
      refine ⟨⟨q, hQ₀G hq⟩, ?_, rfl⟩
      show θ' ⟨q, hQ₀G hq⟩ = ⟨q, hQ₀G hq⟩
      apply Subtype.ext
      rw [hθ'def, Subgroup.normalizerMonoidHom_apply_apply_coe]
      change t * x * q * (t * x)⁻¹ = q
      rw [← hQ₀t' q hq]
      group
    have hQ₀x : Q₀ ≤ centralizer ({x} : Set G) := hQ₀Λ.trans hΛx
    apply not_complSp_le_centralizer_siegDiag (K := K) hkp
    intro y hy
    have h1 := mem_centralizer_singleton_iff.1 (hQ₀x ⟨_, ⟨y, hy, rfl⟩, rfl⟩)
    have hxψ : x = ψJ (siegDiag K p 1) := by rw [hψJ_apply, hx, hx₀def]
    rw [hxψ, ← map_mul, ← map_mul] at h1
    have h2 := hψJinj h1
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

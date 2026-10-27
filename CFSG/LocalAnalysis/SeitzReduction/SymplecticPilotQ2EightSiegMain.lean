module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightSiegInputs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (coords)

section Conj

variable {G : Type} [Group G]

theorem conj_mem_commutator_of_mem_normalizer {G₀ M : Subgroup G} {s h : G}
    (hM : ∀ l : G, l ∈ M ↔ l ∈ G₀ ∧ l * s = s * l) (hh : h ∈ normalizer (G₀ : Set G))
    (hhs : h * s = s * h) {p : G} (hp : p ∈ ⁅M, M⁆) : h * p * h⁻¹ ∈ ⁅M, M⁆ := by
  have h3 : Commute h s := hhs
  have h3' : Commute h⁻¹ s := h3.inv_left
  have hMc : M.map (MulAut.conj h).toMonoidHom ≤ M := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨hlG, hls⟩ := (hM l).1 hl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine (hM _).2 ⟨(mem_normalizer_iff.1 hh l).1 hlG, ?_⟩
    calc h * l * h⁻¹ * s = h * l * (h⁻¹ * s) := by group
      _ = h * l * (s * h⁻¹) := by rw [h3'.eq]
      _ = h * (l * s) * h⁻¹ := by group
      _ = h * (s * l) * h⁻¹ := by rw [hls]
      _ = (h * s) * l * h⁻¹ := by group
      _ = (s * h) * l * h⁻¹ := by rw [h3.eq]
      _ = s * (h * l * h⁻¹) := by group
  have hcomm : ⁅M, M⁆.map (MulAut.conj h).toMonoidHom ≤ ⁅M, M⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hMc hMc
  exact hcomm ⟨p, hp, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

end Conj

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem false_of_q2OmegaBType_derived (hset : SeitzSetting G L) (hK : Nat.card K = 2) {N : ℕ}
    (hN : 3 ≤ N) (e : L ≃* StatedSp N K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {G₀ : Subgroup G} (hLG : L ≤ G₀) (htN : t ∈ normalizer (G₀ : Set G))
    (hout : G₀.normalizerMonoidHom ⟨t, htN⟩ ∉ (MulAut.conj : G₀ →* MulAut G₀).range)
    (hZ : G₀ ⊓ centralizer (G₀ : Set G) = ⊥)
    (hodd : Odd (Nat.card (centralizer (G₀ : Set G))))
    (hPCT : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (G₀ : Set G)) (β : MulAut G₀),
      β * G₀.normalizerMonoidHom ⟨t, htN⟩ = G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ * β →
        g ∈ normalizer (G₀ : Set G))
    (hnotL : ∀ y : G, y * t * y⁻¹ ∉ L)
    (htorus : ∀ j : ℕ, 1 ≤ j → 2 * j < N → ∀ (t' c' : G), c' ∈ L →
      ∀ Φ₂ : StatedSp N K →* G, Function.Injective Φ₂ → (∀ y, Φ₂ y * t' = t' * Φ₂ y) →
      c'⁻¹ * ((e.symm (spARep N j) : L) : G) * c' = Φ₂ (spARep N j) →
      (∀ y ∈ centralizer ({spARep N j} : Set (StatedSp N K)), Odd (orderOf y) →
        ∃ y' ∈ centralizer ({spARep N j} : Set (StatedSp N K)),
          Φ₂ y' = c'⁻¹ * ((e.symm y : L) : G) * c') →
      (∀ y ∈ centralizer ({spARep N j} : Set (StatedSp N K)), Odd (orderOf y) →
        ∃ y' ∈ centralizer ({spARep N j} : Set (StatedSp N K)),
          c'⁻¹ * ((e.symm y' : L) : G) * c' = Φ₂ y) →
      (∀ z ∈ G₀, z * t' = t' * z → z * Φ₂ (spARep N j) = Φ₂ (spARep N j) * z) → False)
    (hclos : ∀ j : ℕ, 2 * j = N → SpTwoLagDerivedClosureAt N j)
    (B : MulAut G₀ → ℕ → Prop)
    (hshape : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (G₀ : Set G)) (j : ℕ), 1 ≤ j →
      B (G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) j →
        OmegaBShapeOn G₀ N K (G₀.normalizerMonoidHom ⟨t, htN⟩)
          (G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) j)
    (hcoset : ∀ y : G₀,
      (MulAut.conj y * G₀.normalizerMonoidHom ⟨t, htN⟩) *
          (MulAut.conj y * G₀.normalizerMonoidHom ⟨t, htN⟩) = 1 →
        (∃ β : MulAut G₀, β * G₀.normalizerMonoidHom ⟨t, htN⟩ =
          (MulAut.conj y * G₀.normalizerMonoidHom ⟨t, htN⟩) * β) ∨
        ∃ j, 1 ≤ j ∧ B (MulAut.conj y * G₀.normalizerMonoidHom ⟨t, htN⟩) j) :
    ∀ (j : ℕ), 1 ≤ j → ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (G₀ : Set G)),
      ¬ B (G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj g hg hB
  obtain ⟨-, hjn, ψ, η, hψ, hα, hη, hfix, ⟨z, hz⟩, -⟩ := hshape g hg j hj hB
  set θt := G₀.normalizerMonoidHom ⟨t, htN⟩ with hθt
  set θs := G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ with hθs
  set a : StatedSp N K := spARep N j with ha
  set x₀ : G₀ := ψ a with hx₀def
  have hηx : η x₀ = x₀ := by
    have h1 : x₀ ∈ fixedSubgroup η := by rw [hη]; exact ⟨a, rfl⟩
    exact h1
  have hxx : x₀ * x₀ = 1 := by rw [hx₀def, ← map_mul, ha, spARep_mul_self, map_one]
  have hFle : fixedSubgroup θs ≤ centralizer ({x₀} : Set G₀) := by
    rw [hfix]
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hc]
  have hFcard : Nat.card (fixedSubgroup θs) =
      Nat.card (centralizer ({a} : Set (StatedSp N K))) := by
    rw [hfix, Subgroup.card_map_of_injective hψ]
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
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
  have hx₀N : (x₀ : G) ∈ normalizer (G₀ : Set G) := le_normalizer x₀.2
  have hsxN : (g⁻¹ * t * g) * x₀ ∈ normalizer (G₀ : Set G) := mul_mem hg hx₀N
  have hθη : G₀.normalizerMonoidHom ⟨(g⁻¹ * t * g) * x₀, hsxN⟩ = η := by
    rw [normalizerMonoidHom_mul' hg hx₀N hsxN, normalizerMonoidHom_eq_conj_of_mem x₀.2 hx₀N]
    change θs * MulAut.conj x₀ = η
    rw [hα, mul_assoc, mulAut_mul_conj_eq_of_apply_eq hηx, ← mul_assoc, ← map_mul, hxx,
      map_one, one_mul]
  have hzN : (z : G) ∈ normalizer (G₀ : Set G) := le_normalizer z.2
  have hztN : (z : G) * t * (z : G)⁻¹ ∈ normalizer (G₀ : Set G) :=
    mul_mem (mul_mem hzN htN) (inv_mem hzN)
  have hθz : G₀.normalizerMonoidHom ⟨(z : G) * t * (z : G)⁻¹, hztN⟩ =
      MulAut.conj z * θt * (MulAut.conj z)⁻¹ := by
    rw [normalizerMonoidHom_mul' (mul_mem hzN htN) (inv_mem hzN) hztN,
      normalizerMonoidHom_mul' hzN htN (mul_mem hzN htN),
      normalizerMonoidHom_eq_conj_of_mem z.2 hzN,
      normalizerMonoidHom_eq_conj_of_mem (inv_mem z.2) (inv_mem hzN), ← map_inv]
    rfl
  have hzt2 : ((z : G) * t * (z : G)⁻¹) * ((z : G) * t * (z : G)⁻¹) = 1 := by
    calc ((z : G) * t * (z : G)⁻¹) * ((z : G) * t * (z : G)⁻¹) = (z : G) * (t * t) * (z : G)⁻¹ :=
        by group
      _ = 1 := by rw [htt]; group
  have hsx2 : ((g⁻¹ * t * g) * x₀) * ((g⁻¹ * t * g) * x₀) = 1 := by
    calc ((g⁻¹ * t * g) * x₀) * ((g⁻¹ * t * g) * x₀) =
        (g⁻¹ * t * g) * ((x₀ : G) * (g⁻¹ * t * g)) * x₀ := by group
      _ = (g⁻¹ * t * g) * ((g⁻¹ * t * g) * x₀) * x₀ := by rw [hsx]
      _ = g⁻¹ * (t * t) * g * ((x₀ : G) * x₀) := by group
      _ = 1 := by rw [htt, hx0]; group
  obtain ⟨c, hcC, hc⟩ := exists_conj_eq_of_normalizerMonoidHom_eq hodd hzt2 hsx2 hztN hsxN
    (by rw [hθz, hθη, hz])
  set y : G := g * c * z with hy
  have hty : t * x = y * t * y⁻¹ := by
    calc t * x = g * ((g⁻¹ * t * g) * x₀) * g⁻¹ := by rw [hx]; group
      _ = g * (c * ((z : G) * t * (z : G)⁻¹) * c⁻¹) * g⁻¹ := by rw [hc]
      _ = y * t * y⁻¹ := by rw [hy]; group
  have hxL : x ∈ L := by
    rcases mem_or_mul_mem_of_mem_centralizer_two hset hK (by omega) e ht hKt
      (mem_centralizer_singleton_iff.2 htx.symm) with h | h
    · exact h
    · exact absurd (hty ▸ h) (hnotL y)
  have hxG : x ∈ G₀ := hLG hxL
  set Λ : Subgroup G := (fixedSubgroup θs).map ((MulAut.conj g).toMonoidHom.comp G₀.subtype)
    with hΛ
  have hinj : Function.Injective ((MulAut.conj g).toMonoidHom.comp G₀.subtype) :=
    (MulAut.conj g).injective.comp G₀.subtype_injective
  have hΛcard : Nat.card Λ = Nat.card (fixedSubgroup θs) := Subgroup.card_map_of_injective hinj
  have hΛt : Λ ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨y', hy', rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := hact y'
    have hy'' : θs y' = y' := hy'
    rw [hy''] at h1
    have hys : (y' : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y' := by
      calc (y' : G) * (g⁻¹ * t * g) =
          ((g⁻¹ * t * g) * y' * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g) := by rw [← h1]
        _ = (g⁻¹ * t * g) * y' := by group
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * (y' : G) * g⁻¹ * t = g * ((y' : G) * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * y') * g⁻¹ := by rw [hys]
      _ = t * (g * y' * g⁻¹) := by group
  have hΛx : Λ ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨y', hy', rfl⟩
    have h1 : y' * x₀ = x₀ * y' := mem_centralizer_singleton_iff.1 (hFle hy')
    have h2 : (y' : G) * x₀ = x₀ * y' := congrArg Subtype.val h1
    rw [mem_centralizer_singleton_iff]
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * (y' : G) * g⁻¹ * x = g * ((y' : G) * x₀) * g⁻¹ := by rw [hx]; group
      _ = g * (x₀ * y') * g⁻¹ := by rw [h2]
      _ = x * (g * y' * g⁻¹) := by rw [hx]; group
  have htΛ : t ∉ Λ := by
    rintro ⟨y', -, hyt⟩
    have hyt' : g * (y' : G) * g⁻¹ = t := hyt
    have hmem : g⁻¹ * t * g ∈ G₀ := by
      have : g⁻¹ * t * g = (y' : G) := by rw [← hyt']; group
      rw [this]
      exact y'.2
    have hθin : θs = MulAut.conj ⟨_, hmem⟩ := normalizerMonoidHom_eq_conj_of_mem hmem hg
    apply hout
    refine ⟨z⁻¹ * x₀⁻¹ * ⟨_, hmem⟩ * z, ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hθin, hα, hz]
    group
  have hfixLt : Nat.card (fixedSubgroup θs) < Nat.card L := by
    rw [hFcard, Nat.card_congr e.toEquiv]
    exact card_centralizer_spARep_lt hj hjn
  have hxN : x ∈ normalizer (G₀ : Set G) := le_normalizer hxG
  have ht'N : t * x ∈ normalizer (G₀ : Set G) := mul_mem htN hxN
  have hθ' : G₀.normalizerMonoidHom ⟨t * x, ht'N⟩ = MulAut.conj (⟨x, hxG⟩ : G₀) * θt := by
    refine MulEquiv.ext fun y' => Subtype.ext ?_
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.mul_apply, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hθt,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    change t * x * (y' : G) * (t * x)⁻¹ = x * (t * y' * t⁻¹) * x⁻¹
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
  have hg'eq : y⁻¹⁻¹ * t * y⁻¹ = t * x := by rw [inv_inv, hty]
  have hg' : y⁻¹⁻¹ * t * y⁻¹ ∈ normalizer (G₀ : Set G) := hg'eq ▸ ht'N
  have he1 : (⟨y⁻¹⁻¹ * t * y⁻¹, hg'⟩ : normalizer (G₀ : Set G)) = ⟨t * x, ht'N⟩ :=
    Subtype.ext hg'eq
  have hθg' : G₀.normalizerMonoidHom ⟨y⁻¹⁻¹ * t * y⁻¹, hg'⟩ =
      MulAut.conj (⟨x, hxG⟩ : G₀) * θt := by
    rw [he1, hθ']
  rcases hcoset ⟨x, hxG⟩ hθ'2 with ⟨β, hβ⟩ | ⟨j', hj', hB'⟩
  ·
    have hyN : y⁻¹ ∈ normalizer (G₀ : Set G) := hPCT y⁻¹ hg' β (by rw [hθg']; exact hβ)
    have hcN : c ∈ normalizer (G₀ : Set G) := centralizer_le_normalizer _ hcC
    have hgG : g ∈ normalizer (G₀ : Set G) := by
      have : g = y⁻¹⁻¹ * (z : G)⁻¹ * c⁻¹ := by rw [inv_inv, hy]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hyN) (inv_mem hzN)) (inv_mem hcN)
    exact absurd (card_le_card_fixedSubgroup_of_mem_normalizer hLG hLt hgG hg) (not_le.2 hfixLt)
  ·
    set θ' := G₀.normalizerMonoidHom ⟨t * x, ht'N⟩ with hθ'def
    have hB'' : B (G₀.normalizerMonoidHom ⟨y⁻¹⁻¹ * t * y⁻¹, hg'⟩) j' := by
      rw [he1]
      change B θ' j'
      rw [hθ']
      exact hB'
    have hjj' : j ≤ j' := by
      by_contra hlt
      exact ih j' (by omega) hj' y⁻¹ hg' hB''
    have hsh' : OmegaBShapeOn G₀ N K θt θ' j' := by
      have h1 := hshape y⁻¹ hg' j' hj' hB''
      rw [he1] at h1
      exact h1
    obtain ⟨-, hj'n, ψ', η', hψ', hα', hη', hfix', -, huniq'⟩ := hsh'
    have hCL : L ⊓ centralizer ({x} : Set G) ≤ (fixedSubgroup θ').map G₀.subtype := by
      rintro l ⟨hl, hlx⟩
      refine ⟨⟨l, hLG hl⟩, ?_, rfl⟩
      show θ' ⟨l, hLG hl⟩ = ⟨l, hLG hl⟩
      apply Subtype.ext
      rw [hθ'def, Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hlx' : l * x = x * l := mem_centralizer_singleton_iff.1 hlx
      have hlt' : l * t = t * l := mem_centralizer_iff.1 htC l hl
      change t * x * l * (t * x)⁻¹ = l
      calc t * x * l * (t * x)⁻¹ = t * (x * l) * x⁻¹ * t⁻¹ := by group
        _ = t * (l * x) * x⁻¹ * t⁻¹ := by rw [hlx']
        _ = (t * l) * t⁻¹ := by group
        _ = l := by rw [← hlt']; group
    have hcard' : Nat.card (fixedSubgroup θ') =
        Nat.card (centralizer ({spARep N j'} : Set (StatedSp N K))) := by
      rw [hfix', Subgroup.card_map_of_injective hψ']
    set A : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) with hA
    have hAcard : Nat.card A = 2 * Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G) :=
      card_inf_centralizer_eq_two_mul hset hK (by omega) e ht hKt hxL
    have hΛA : Λ ≤ A := le_inf hΛt hΛx
    have htA : t ∈ A := ⟨mem_centralizer_singleton_iff.2 rfl,
      mem_centralizer_singleton_iff.2 htx⟩
    have hΛsub : Nat.card (Λ.subgroupOf A) = Nat.card Λ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛA).toEquiv
    have hidx1 : (Λ.subgroupOf A).index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      intro htop
      have : (⟨t, htA⟩ : A) ∈ Λ.subgroupOf A := htop ▸ Subgroup.mem_top _
      exact htΛ this
    have hidx0 : (Λ.subgroupOf A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hΛA2 : 2 * Nat.card Λ ≤ Nat.card A := by
      have h1 := Subgroup.card_mul_index (Λ.subgroupOf A)
      rw [hΛsub] at h1
      rw [← h1]
      have h2 : 2 ≤ (Λ.subgroupOf A).index := by omega
      calc 2 * Nat.card Λ = Nat.card Λ * 2 := mul_comm _ _
        _ ≤ Nat.card Λ * (Λ.subgroupOf A).index := Nat.mul_le_mul_left _ h2
    have hCLle : Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G) ≤
        Nat.card (fixedSubgroup θ') := by
      have h1 := Subgroup.card_le_of_le hCL
      rwa [Subgroup.card_map_of_injective G₀.subtype_injective] at h1
    have hCLdvd : Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G) ∣
        Nat.card (fixedSubgroup θ') := by
      have h1 := Subgroup.card_dvd_of_le hCL
      rwa [Subgroup.card_map_of_injective G₀.subtype_injective] at h1
    have h2a := spACentralizerTwoPartInput_holds N j 1 K (by rw [hK, pow_one]) hjn
    have h2b := spACentralizerTwoPartInput_holds N j' 1 K (by rw [hK, pow_one]) hj'n
    have hv1 : (Nat.card Λ).factorization 2 ≤ (Nat.card A).factorization 2 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (Subgroup.card_dvd_of_le hΛA) 2
    have hv2 : (Nat.card A).factorization 2 =
        (Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G)).factorization 2 + 1 := by
      rw [hAcard, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_two, add_comm]
    have hv3 : (Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G)).factorization 2 ≤
        (Nat.card (fixedSubgroup θ')).factorization 2 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hCLdvd 2
    rw [hΛcard, hFcard, h2a] at hv1
    rw [hcard', h2b] at hv3
    have hj'eq : j' = j := by
      by_contra hne
      have hlt : j < j' := lt_of_le_of_ne hjj' (Ne.symm hne)
      have hs1 := spAExp_succ_add (n := N) (j := j) (by omega)
      have hs2 : spAExp N j' ≤ spAExp N (j + 1) := by
        rcases eq_or_lt_of_le (show j + 1 ≤ j' by omega) with h | h
        · rw [h]
        · exact (spAExp_lt_of_lt (by omega) h (by omega)).le
      omega
    subst j'
    have hcardCL : Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G) =
        Nat.card (fixedSubgroup θ') := by
      have h1 : Nat.card Λ = Nat.card (fixedSubgroup θ') := by rw [hΛcard, hFcard, hcard']
      omega
    have hCLeq : L ⊓ centralizer ({x} : Set G) = (fixedSubgroup θ').map G₀.subtype := by
      refine Subgroup.eq_of_le_of_card_ge hCL ?_
      rw [Subgroup.card_map_of_injective G₀.subtype_injective, hcardCL]
    have hΛidx : (Λ.subgroupOf A).index = 2 := by
      have h1 := Subgroup.card_mul_index (Λ.subgroupOf A)
      rw [hΛsub] at h1
      have h2 : Nat.card Λ = Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G) := by
        rw [hΛcard, hFcard, hcardCL, hcard']
      rw [hAcard, h2] at h1
      have hpos : 0 < Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G) := Nat.card_pos
      nlinarith
    have hθtx : θt ⟨x, hxG⟩ = ⟨x, hxG⟩ := by
      apply Subtype.ext
      rw [hθt, Subgroup.normalizerMonoidHom_apply_apply_coe]
      change t * x * t⁻¹ = x
      rw [htx, mul_inv_cancel_right]
    have hcomm : θt * θ' = θ' * θt := by
      rw [hθ', ← mul_assoc, mulAut_mul_conj_eq_of_apply_eq hθtx]
    have hfixle : fixedSubgroup θ' ≤ fixedSubgroup θt := by
      intro u hu
      have hu1 : (u : G) ∈ (fixedSubgroup θ').map G₀.subtype := ⟨u, hu, rfl⟩
      rw [← hCLeq] at hu1
      show θt u = u
      apply Subtype.ext
      rw [hθt, Subgroup.normalizerMonoidHom_apply_apply_coe,
        ← mem_centralizer_iff.1 htC _ hu1.1, mul_inv_cancel_right]
    have hθη' : θt = η' := huniq' hcomm hfixle
    have hxψ : ((ψ' a : G₀) : G) = x := by
      have h1 : MulAut.conj (⟨x, hxG⟩ : G₀) * θt = MulAut.conj (ψ' a) * θt := by
        rw [← hθ', hα', ← hθη']
      have h2 : MulAut.conj (⟨x, hxG⟩ : G₀) = MulAut.conj (ψ' a) := mul_right_cancel h1
      set p : G₀ := ψ' a with hp
      have hmem : (p : G)⁻¹ * x ∈ G₀ ⊓ centralizer (G₀ : Set G) := by
        refine ⟨G₀.mul_mem (G₀.inv_mem p.2) hxG, mem_centralizer_iff.2 fun u hu => ?_⟩
        have h4 := congrArg Subtype.val (DFunLike.congr_fun h2 ⟨u, hu⟩)
        change x * u * x⁻¹ = (p : G) * u * (p : G)⁻¹ at h4
        calc u * ((p : G)⁻¹ * x) = (p : G)⁻¹ * ((p : G) * u * (p : G)⁻¹) * x := by group
          _ = (p : G)⁻¹ * (x * u * x⁻¹) * x := by rw [← h4]
          _ = (p : G)⁻¹ * x * u := by group
      rw [hZ, mem_bot] at hmem
      calc (p : G) = (p : G) * ((p : G)⁻¹ * x) := by rw [hmem, mul_one]
        _ = x := by group
    have hfixθ : fixedSubgroup θt = ψ'.range := by rw [hθη']; exact hη'
    have hLfix : L ≤ (fixedSubgroup θt).map G₀.subtype := by
      intro l hl
      refine ⟨⟨l, hLG hl⟩, ?_, rfl⟩
      show θt ⟨l, hLG hl⟩ = ⟨l, hLG hl⟩
      apply Subtype.ext
      rw [hθt, Subgroup.normalizerMonoidHom_apply_apply_coe]
      change t * l * t⁻¹ = l
      rw [← mem_centralizer_iff.1 htC l hl, mul_inv_cancel_right]
    have hLeq : L = (fixedSubgroup θt).map G₀.subtype := by
      refine Subgroup.eq_of_le_of_card_ge hLfix ?_
      rw [Subgroup.card_map_of_injective G₀.subtype_injective, hfixθ,
        MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψ', Subgroup.card_top,
        Nat.card_congr e.toEquiv]
    have hψL : ∀ y' : StatedSp N K, (G₀.subtype.comp ψ') y' ∈ L := by
      intro y'
      refine hLeq.symm.le ⟨ψ' y', ?_, rfl⟩
      rw [hfixθ]
      exact ⟨y', rfl⟩
    obtain ⟨c', hc'L, hc'⟩ := exists_conj_eq_spARep_of_injective (by omega) e
      (G₀.subtype.comp ψ') (G₀.subtype_injective.comp hψ') hψL j
    have hc'x : c' * x * c'⁻¹ = ((e.symm a : L) : G) := by
      rw [← hc', ← hxψ]
      rfl
    have hxl : c'⁻¹ * ((e.symm a : L) : G) * c' = x := by rw [← hc'x]; group
    have hc't : c' * t = t * c' := mem_centralizer_iff.1 htC c' hc'L
    set Φ₂ : StatedSp N K →* G := (MulAut.conj g).toMonoidHom.comp (G₀.subtype.comp ψ)
      with hΦ₂
    have hΦ₂apply : ∀ y', Φ₂ y' = g * ((ψ y' : G₀) : G) * g⁻¹ := fun y' => by simp [hΦ₂]
    have hΦ₂inj : Function.Injective Φ₂ :=
      (MulAut.conj g).injective.comp (G₀.subtype_injective.comp hψ)
    have hΦ₂a : Φ₂ a = x := by rw [hΦ₂apply]
    have hΦ₂t : ∀ y', Φ₂ y' * (t * x) = (t * x) * Φ₂ y' := by
      intro y'
      have hmem : ψ y' ∈ fixedSubgroup η := by rw [hη]; exact ⟨y', rfl⟩
      have h1 : G₀.normalizerMonoidHom ⟨(g⁻¹ * t * g) * x₀, hsxN⟩ (ψ y') = ψ y' := by
        rw [hθη]
        exact hmem
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
      have h3 : (g⁻¹ * t * g * (x₀ : G)) * ((ψ y' : G₀) : G) =
          ((ψ y' : G₀) : G) * (g⁻¹ * t * g * x₀) := by
        calc (g⁻¹ * t * g * (x₀ : G)) * ((ψ y' : G₀) : G) =
            ((g⁻¹ * t * g * (x₀ : G)) * ((ψ y' : G₀) : G) * (g⁻¹ * t * g * (x₀ : G))⁻¹) *
              (g⁻¹ * t * g * x₀) := by group
          _ = ((ψ y' : G₀) : G) * (g⁻¹ * t * g * x₀) := by rw [h2]
      rw [hΦ₂apply, hx]
      calc g * ((ψ y' : G₀) : G) * g⁻¹ * (t * (g * x₀ * g⁻¹)) =
          g * (((ψ y' : G₀) : G) * (g⁻¹ * t * g * x₀)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g * (x₀ : G)) * ((ψ y' : G₀) : G)) * g⁻¹ := by rw [h3]
        _ = t * (g * x₀ * g⁻¹) * (g * ((ψ y' : G₀) : G) * g⁻¹) := by group
    rcases lt_or_eq_of_le hjn with hlt | heq
    ·
      have hΦ₂Λ : ∀ y' ∈ centralizer ({a} : Set (StatedSp N K)), Φ₂ y' ∈ Λ := by
        intro y' hy'
        refine ⟨ψ y', ?_, by rw [hΦ₂apply]; rfl⟩
        rw [hfix]
        exact ⟨y', hy', rfl⟩
      have hxa : c'⁻¹ * ((e.symm a : L) : G) * c' = Φ₂ a := by rw [hxl, hΦ₂a]
      have hodd₁ : ∀ y' ∈ centralizer ({a} : Set (StatedSp N K)), Odd (orderOf y') →
          ∃ y'' ∈ centralizer ({a} : Set (StatedSp N K)),
            Φ₂ y'' = c'⁻¹ * ((e.symm y' : L) : G) * c' := by
        intro y' hy' hyo
        set w : G := c'⁻¹ * ((e.symm y' : L) : G) * c' with hw
        have hwL : w ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hc'L) (e.symm y').2) hc'L
        have hya : y' * a = a * y' := mem_centralizer_singleton_iff.1 hy'
        have hwx : w * x = x * w := by
          have h1 : ((e.symm y' : L) : G) * ((e.symm a : L) : G) =
              ((e.symm a : L) : G) * ((e.symm y' : L) : G) := by
            rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hya]
          rw [hw, ← hxl]
          calc c'⁻¹ * ((e.symm y' : L) : G) * c' * (c'⁻¹ * ((e.symm a : L) : G) * c') =
              c'⁻¹ * (((e.symm y' : L) : G) * ((e.symm a : L) : G)) * c' := by group
            _ = c'⁻¹ * (((e.symm a : L) : G) * ((e.symm y' : L) : G)) * c' := by rw [h1]
            _ = c'⁻¹ * ((e.symm a : L) : G) * c' * (c'⁻¹ * ((e.symm y' : L) : G) * c') := by
                group
        have hwA : w ∈ A := ⟨mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC w hwL),
          mem_centralizer_singleton_iff.2 hwx⟩
        have hwo : Odd (orderOf w) := by
          have h1 : orderOf w = orderOf ((e.symm y' : L) : G) := by
            rw [hw, show c'⁻¹ * ((e.symm y' : L) : G) * c' =
              MulAut.conj c'⁻¹ ((e.symm y' : L) : G) by simp]
            exact orderOf_injective (MulAut.conj c'⁻¹).toMonoidHom (MulAut.conj c'⁻¹).injective _
          rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
          exact hyo
        have hwΛ : (⟨w, hwA⟩ : A) ∈ Λ.subgroupOf A := by
          refine mem_of_odd_of_index_eq_two hΛidx ?_
          rw [Subgroup.orderOf_mk]
          exact hwo
        obtain ⟨u, hu, hu'⟩ := (Subgroup.mem_subgroupOf.1 hwΛ : w ∈ Λ)
        rw [hfix] at hu
        obtain ⟨y'', hy'', rfl⟩ := hu
        refine ⟨y'', hy'', ?_⟩
        rw [hΦ₂apply]
        exact hu'
      have hodd₂ : ∀ y' ∈ centralizer ({a} : Set (StatedSp N K)), Odd (orderOf y') →
          ∃ y'' ∈ centralizer ({a} : Set (StatedSp N K)),
            c'⁻¹ * ((e.symm y'' : L) : G) * c' = Φ₂ y' := by
        intro y' hy' hyo
        have hΛy := hΦ₂Λ y' hy'
        have hyo' : Odd (orderOf (Φ₂ y')) := by rw [orderOf_injective Φ₂ hΦ₂inj]; exact hyo
        have hyL : Φ₂ y' ∈ L :=
          mem_of_odd_of_mem_centralizer_two hset hK (by omega) e ht hKt (hΛt hΛy) hyo'
        have hyx : Φ₂ y' * x = x * Φ₂ y' := mem_centralizer_singleton_iff.1 (hΛx hΛy)
        set l : G := c' * Φ₂ y' * c'⁻¹ with hl
        have hlL : l ∈ L := L.mul_mem (L.mul_mem hc'L hyL) (L.inv_mem hc'L)
        refine ⟨e ⟨l, hlL⟩, mem_centralizer_singleton_iff.2 ?_, ?_⟩
        · apply e.symm.injective
          apply Subtype.ext
          rw [map_mul, map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul, Subgroup.coe_mul]
          change l * ((e.symm a : L) : G) = ((e.symm a : L) : G) * l
          rw [hl, ← hc'x]
          calc c' * Φ₂ y' * c'⁻¹ * (c' * x * c'⁻¹) = c' * (Φ₂ y' * x) * c'⁻¹ := by group
            _ = c' * (x * Φ₂ y') * c'⁻¹ := by rw [hyx]
            _ = c' * x * c'⁻¹ * (c' * Φ₂ y' * c'⁻¹) := by group
        · rw [MulEquiv.symm_apply_apply]
          change c'⁻¹ * l * c' = Φ₂ y'
          rw [hl]
          group
      have hfin : ∀ z' ∈ G₀, z' * (t * x) = (t * x) * z' → z' * Φ₂ a = Φ₂ a * z' := by
        intro z' hz' hzt
        have hfz : (⟨z', hz'⟩ : G₀) ∈ fixedSubgroup θ' := by
          show θ' ⟨z', hz'⟩ = ⟨z', hz'⟩
          apply Subtype.ext
          rw [hθ'def, Subgroup.normalizerMonoidHom_apply_apply_coe]
          change t * x * z' * (t * x)⁻¹ = z'
          rw [← hzt, mul_inv_cancel_right]
        have hz1 : z' ∈ (fixedSubgroup θ').map G₀.subtype := ⟨⟨z', hz'⟩, hfz, rfl⟩
        rw [← hCLeq] at hz1
        rw [hΦ₂a]
        exact mem_centralizer_singleton_iff.1 hz1.2
      exact htorus j hj hlt (t * x) c' hc'L Φ₂ hΦ₂inj hΦ₂t hxa
        hodd₁ hodd₂ hfin
    ·
      have hΦ₂C : (centralizer ({a} : Set (StatedSp N K))).map Φ₂ = Λ := by
        ext z'
        constructor
        · rintro ⟨y', hy', rfl⟩
          exact ⟨ψ y', by rw [hfix]; exact ⟨y', hy', rfl⟩, by rw [hΦ₂apply]; rfl⟩
        · rintro ⟨u, hu, rfl⟩
          rw [hfix] at hu
          obtain ⟨y', hy', rfl⟩ := hu
          exact ⟨y', hy', by rw [hΦ₂apply]; rfl⟩
      have hΦ₁a : conjEmbed e c' a = x := by rw [conjEmbed_apply, hxl]
      have hΦ₁C : (centralizer ({a} : Set (StatedSp N K))).map (conjEmbed e c') =
          L ⊓ centralizer ({x} : Set G) := by
        rw [map_centralizer_conjEmbed e hc'L, hΦ₁a]
      set M : Subgroup G := L ⊓ centralizer ({x} : Set G) with hM
      set C₀ : Subgroup (StatedSp N K) := ⁅centralizer ({a} : Set (StatedSp N K)),
        centralizer ({a} : Set (StatedSp N K))⁆ with hC₀
      have hC₀₁ : C₀.map (conjEmbed e c') = ⁅M, M⁆ := by
        rw [hC₀, Subgroup.map_commutator, hΦ₁C]
      have hC₀₂ : C₀.map Φ₂ = ⁅Λ, Λ⁆ := by
        rw [hC₀, Subgroup.map_commutator, hΦ₂C]
      have hC₀le : C₀.map Φ₂ ≤ C₀.map (conjEmbed e c') := by
        rw [hC₀₂, hC₀₁]
        exact commutator_le_commutator_inf_centralizer_two hset hK (by omega) e ht hKt htx hΛt hΛx
      have hC₀eq : C₀.map (conjEmbed e c') = C₀.map Φ₂ := by
        refine (Subgroup.eq_of_le_of_card_ge hC₀le ?_).symm
        rw [Subgroup.card_map_of_injective hΦ₂inj,
          Subgroup.card_map_of_injective (conjEmbed_injective e c')]
      obtain ⟨c₀, d, ⟨y₀, hy₀, hy₀c⟩, hcd⟩ := hclos j heq K hK G (conjEmbed e c') Φ₂
        (conjEmbed_injective e c') hΦ₂inj (by show conjEmbed e c' a = Φ₂ a; rw [hΦ₁a, hΦ₂a])
        hC₀eq
      obtain ⟨w, hw⟩ : ∃ w : G, w = conjEmbed e c' (d * spARep N 1 * d⁻¹) := ⟨_, rfl⟩
      have hwL : w ∈ L := hw ▸ conjEmbed_mem e hc'L _
      have hwG : w ∈ G₀ := hLG hwL
      have hwx : x * Φ₂ (c₀ * a * c₀⁻¹) = w := by
        rw [hw, ← hΦ₁a]
        exact hcd
      have htw : t * w = Φ₂ c₀ * t * (Φ₂ c₀)⁻¹ := by
        have h1 : Φ₂ (c₀ * a * c₀⁻¹) = Φ₂ c₀ * x * (Φ₂ c₀)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hΦ₂a]
        have h3 := hΦ₂t c₀
        calc t * w = (t * x) * Φ₂ (c₀ * a * c₀⁻¹) := by rw [← hwx]; group
          _ = (t * x) * Φ₂ c₀ * x * (Φ₂ c₀)⁻¹ := by rw [h1]; group
          _ = Φ₂ c₀ * (t * x) * x * (Φ₂ c₀)⁻¹ := by rw [← h3]
          _ = Φ₂ c₀ * t * (x * x) * (Φ₂ c₀)⁻¹ := by group
          _ = Φ₂ c₀ * t * (Φ₂ c₀)⁻¹ := by rw [hx2, mul_one]
      obtain ⟨g'', hg''⟩ : ∃ g'' : G, g'' = (Φ₂ c₀)⁻¹ := ⟨_, rfl⟩
      have hg''eq : g''⁻¹ * t * g'' = t * w := by rw [hg'', inv_inv, htw]
      have htwN : t * w ∈ normalizer (G₀ : Set G) := mul_mem htN (le_normalizer hwG)
      have hg''N : g''⁻¹ * t * g'' ∈ normalizer (G₀ : Set G) := hg''eq ▸ htwN
      have he'' : (⟨g''⁻¹ * t * g'', hg''N⟩ : normalizer (G₀ : Set G)) = ⟨t * w, htwN⟩ :=
        Subtype.ext hg''eq
      have hwt : t * w = w * t := (mem_centralizer_iff.1 htC w hwL).symm
      have hθw : G₀.normalizerMonoidHom ⟨t * w, htwN⟩ = MulAut.conj (⟨w, hwG⟩ : G₀) * θt := by
        refine MulEquiv.ext fun y' => Subtype.ext ?_
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.mul_apply, MulAut.conj_apply,
          Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hθt,
          Subgroup.normalizerMonoidHom_apply_apply_coe]
        change t * w * (y' : G) * (t * w)⁻¹ = w * (t * y' * t⁻¹) * w⁻¹
        rw [hwt]
        group
      have hw2 : w * w = 1 := by
        have h1 : d * spARep N 1 * d⁻¹ * (d * spARep N 1 * d⁻¹) = (1 : StatedSp N K) := by
          calc d * spARep N 1 * d⁻¹ * (d * spARep N 1 * d⁻¹) =
              d * (spARep N 1 * spARep N 1) * d⁻¹ := by group
            _ = 1 := by rw [spARep_mul_self]; group
        rw [hw, ← map_mul, h1, map_one]
      have htw2 : (t * w) * (t * w) = 1 := by
        calc (t * w) * (t * w) = t * (w * t) * w := by group
          _ = t * (t * w) * w := by rw [← hwt]
          _ = (t * t) * (w * w) := by group
          _ = 1 := by rw [htt, hw2, one_mul]
      have hθw2 : (MulAut.conj (⟨w, hwG⟩ : G₀) * θt) * (MulAut.conj (⟨w, hwG⟩ : G₀) * θt) = 1 := by
        rw [← hθw, ← map_mul,
          show (⟨t * w, htwN⟩ : normalizer (G₀ : Set G)) * ⟨t * w, htwN⟩ = 1 from Subtype.ext htw2,
          map_one]
      rcases hcoset ⟨w, hwG⟩ hθw2 with ⟨β, hβ⟩ | ⟨j'', hj'', hB''⟩
      ·
        have hg''G : g'' ∈ normalizer (G₀ : Set G) :=
          hPCT g'' hg''N β (by rw [he'', hθw]; exact hβ)
        have hcN : Φ₂ c₀ ∈ normalizer (G₀ : Set G) := by
          have h1 := inv_mem hg''G
          rwa [hg'', inv_inv] at h1
        have hMiff : ∀ l : G, l ∈ M ↔ l ∈ G₀ ∧ l * (t * x) = (t * x) * l := by
          intro l
          constructor
          · rintro ⟨hl, hlx⟩
            refine ⟨hLG hl, ?_⟩
            have h1 : l * t = t * l := mem_centralizer_iff.1 htC l hl
            have h2 : l * x = x * l := mem_centralizer_singleton_iff.1 hlx
            calc l * (t * x) = (l * t) * x := by group
              _ = (t * l) * x := by rw [h1]
              _ = t * (l * x) := by group
              _ = t * (x * l) := by rw [h2]
              _ = (t * x) * l := by group
          · rintro ⟨hlG, hlt⟩
            have hfz : (⟨l, hlG⟩ : G₀) ∈ fixedSubgroup θ' := by
              show θ' ⟨l, hlG⟩ = ⟨l, hlG⟩
              apply Subtype.ext
              rw [hθ'def, Subgroup.normalizerMonoidHom_apply_apply_coe]
              change t * x * l * (t * x)⁻¹ = l
              rw [← hlt, mul_inv_cancel_right]
            have h4 : l ∈ (fixedSubgroup θ').map G₀.subtype := ⟨_, hfz, rfl⟩
            rwa [← hCLeq] at h4
        apply hy₀c
        have h1 : Φ₂ y₀ ∈ ⁅M, M⁆ := by
          rw [← hC₀₁, hC₀eq]
          exact ⟨y₀, hy₀, rfl⟩
        have h2 : Φ₂ (c₀ * y₀ * c₀⁻¹) ∈ C₀.map Φ₂ := by
          rw [← hC₀eq, hC₀₁, map_mul, map_mul, map_inv]
          exact conj_mem_commutator_of_mem_normalizer hMiff hcN (hΦ₂t c₀) h1
        obtain ⟨y₁, hy₁, hy₁eq⟩ := h2
        rw [hΦ₂inj hy₁eq] at hy₁
        exact hy₁
      ·
        have hB3 : B (G₀.normalizerMonoidHom ⟨g''⁻¹ * t * g'', hg''N⟩) j'' := by
          rw [he'', hθw]
          exact hB''
        rcases lt_or_ge j'' j with hlt'' | hge''
        · exact ih j'' hlt'' hj'' g'' hg''N hB3
        · obtain ⟨-, hj''n, ψ'', η'', hψ'', -, -, hfix'', -, -⟩ := hshape g'' hg''N j'' hj'' hB3
          have hCLw : L ⊓ centralizer ({w} : Set G) ≤
              (fixedSubgroup (G₀.normalizerMonoidHom ⟨g''⁻¹ * t * g'', hg''N⟩)).map
                G₀.subtype := by
            rintro l ⟨hl, hlw⟩
            refine ⟨⟨l, hLG hl⟩, ?_, rfl⟩
            show G₀.normalizerMonoidHom ⟨g''⁻¹ * t * g'', hg''N⟩ ⟨l, hLG hl⟩ = ⟨l, hLG hl⟩
            apply Subtype.ext
            rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
            have hlw' : l * w = w * l := mem_centralizer_singleton_iff.1 hlw
            have hlt' : l * t = t * l := mem_centralizer_iff.1 htC l hl
            change g''⁻¹ * t * g'' * l * (g''⁻¹ * t * g'')⁻¹ = l
            rw [hg''eq]
            calc t * w * l * (t * w)⁻¹ = t * (w * l) * w⁻¹ * t⁻¹ := by group
              _ = t * (l * w) * w⁻¹ * t⁻¹ := by rw [hlw']
              _ = (t * l) * t⁻¹ := by group
              _ = l := by rw [← hlt']; group
          have hdvd : Nat.card (L ⊓ centralizer ({w} : Set G) : Subgroup G) ∣
              Nat.card (centralizer ({spARep N j''} : Set (StatedSp N K))) := by
            have h1 := Subgroup.card_dvd_of_le hCLw
            rwa [Subgroup.card_map_of_injective G₀.subtype_injective, hfix'',
              Subgroup.card_map_of_injective hψ''] at h1
          have hcardw : Nat.card (L ⊓ centralizer ({w} : Set G) : Subgroup G) =
              Nat.card (centralizer ({spARep N 1} : Set (StatedSp N K))) := by
            rw [hw, ← map_centralizer_conjEmbed e hc'L,
              Subgroup.card_map_of_injective (conjEmbed_injective e c'),
              card_centralizer_conj_two]
          have h2a' := spACentralizerTwoPartInput_holds N 1 1 K (by rw [hK, pow_one]) (by omega)
          have h2b' := spACentralizerTwoPartInput_holds N j'' 1 K (by rw [hK, pow_one]) hj''n
          have hv : (Nat.card (centralizer ({spARep N 1} : Set (StatedSp N K)))).factorization 2 ≤
              (Nat.card (centralizer ({spARep N j''} : Set (StatedSp N K)))).factorization 2 := by
            rw [← hcardw]
            exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd 2
          rw [h2a', h2b'] at hv
          have hlt3 := spAExp_lt_of_lt (n := N) (j := 1) (j' := j'') le_rfl (by omega) (by omega)
          omega

end Main

end CFSG.SeitzReduction.SymplecticPilot

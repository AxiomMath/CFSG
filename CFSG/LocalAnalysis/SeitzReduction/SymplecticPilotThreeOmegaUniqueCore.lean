module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Defs

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] def SpOmegaBShapeAut {n : ℕ} (e : L ≃* StatedSp n K) (θ α : MulAut (spGlobal e))
    (j : ℕ) : Prop :=
  1 ≤ j ∧ 2 * j ≤ n ∧ ∃ (ψ : StatedSp n K →* spGlobal e) (η : MulAut (spGlobal e)),
    Function.Injective ψ ∧ α = MulAut.conj (ψ (spARep n j)) * η ∧
    fixedSubgroup η = ψ.range ∧
    fixedSubgroup α = (centralizer ({spARep n j} : Set (StatedSp n K))).map ψ ∧
    ∃ β : MulAut (spGlobal e), β * θ = η * β

end Defs

section Properties

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem spOmegaBShapeAut_properties (hperf : SpACentralizerPerfectInput) (htor : SpAToralInput)
    (hK : 4 ≤ Nat.card K) {n j : ℕ} (e : L ≃* StatedSp n K) {θ α : MulAut (spGlobal e)}
    (h : SpOmegaBShapeAut e θ α j) :
    ∃ (x₀ : spGlobal e) (η : MulAut (spGlobal e)), α = MulAut.conj x₀ * η ∧ η x₀ = x₀ ∧
      x₀ * x₀ = 1 ∧ (∃ β : MulAut (spGlobal e), β * θ = η * β) ∧
      fixedSubgroup α ≤ centralizer ({x₀} : Set (spGlobal e)) ∧
      ⁅fixedSubgroup α, fixedSubgroup α⁆ = fixedSubgroup α ∧
      Nat.card (fixedSubgroup α) = Nat.card (centralizer ({spARep n j} : Set (StatedSp n K))) ∧
      ∀ T : Subgroup (spGlobal e), T ≤ fixedSubgroup α → Odd (Nat.card T) →
        ∃ P : Subgroup (spGlobal e), P ≤ centralizer (T : Set (spGlobal e)) ∧ ⁅P, P⁆ = P ∧
          ¬ P ≤ centralizer ({x₀} : Set (spGlobal e)) := by
  obtain ⟨hj, hjn, ψ, η, hψ, hα, hη, hfix, hβ⟩ := h
  set a : StatedSp n K := spARep n j with ha
  set C := centralizer ({a} : Set (StatedSp n K)) with hC
  have hCle : C.map ψ ≤ centralizer ({ψ a} : Set (spGlobal e)) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hc]
  have haa : ψ a * ψ a = 1 := by rw [← map_mul, ha, spARep_mul_self, map_one]
  have hηa : η (ψ a) = ψ a := by
    have h1 : ψ a ∈ fixedSubgroup η := by
      rw [hη]
      exact ⟨a, rfl⟩
    exact h1
  refine ⟨ψ a, η, hα, hηa, haa, hβ, hfix ▸ hCle, ?_, ?_, ?_⟩
  · rw [hfix, ← Subgroup.map_commutator, hC, hperf n j K hK hj hjn]
  · rw [hfix, Subgroup.card_map_of_injective hψ]
  · intro T hT hTodd
    rw [hfix] at hT
    set T' : Subgroup (StatedSp n K) := T.comap ψ with hT'
    have hT'map : T'.map ψ = T := by
      refine le_antisymm (Subgroup.map_comap_le _ _) fun y hy => ?_
      obtain ⟨c, -, rfl⟩ := hT hy
      exact ⟨c, hy, rfl⟩
    have hT'C : T' ≤ C := by
      intro c hc
      obtain ⟨c', hc', hcc'⟩ := hT hc
      rw [← hψ hcc']
      exact hc'
    have hT'odd : Odd (Nat.card T') := by
      rw [← Subgroup.card_map_of_injective hψ, hT'map]
      exact hTodd
    obtain ⟨P, hPT, hPperf, hPa⟩ := htor n j K hK hj hjn T' hT'C hT'odd
    refine ⟨P.map ψ, ?_, by rw [← Subgroup.map_commutator, hPperf], fun h => hPa ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_iff]
      intro τ hτ
      obtain ⟨τ', hτ', rfl⟩ : ∃ τ' ∈ T', ψ τ' = τ := by
        rw [← hT'map] at hτ
        exact hτ
      rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (hPT hy) τ' hτ']
    · intro y hy
      have h1 := mem_centralizer_singleton_iff.1 (h ⟨y, hy, rfl⟩)
      rw [← map_mul, ← map_mul] at h1
      exact mem_centralizer_singleton_iff.2 (hψ h1)

end Properties

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem false_of_spOmegaBShapeAut (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (htN : t ∈ normalizer (spGlobal e : Set G))
    (hZ : spGlobal e ⊓ centralizer (spGlobal e : Set G) = ⊥)
    (hodd : Odd (Nat.card (centralizer (spGlobal e : Set G))))
    (hperf : SpACentralizerPerfectInput) (htoral : SpAToralInput) {j : ℕ}
    (hcoset : ∀ y : spGlobal e,
      (MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩) *
          (MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩) = 1 →
        (∃ z : spGlobal e, MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ =
          MulAut.conj z * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ * (MulAut.conj z)⁻¹) ∨
        SpOmegaBShape e ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩)
          (MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩) j)
    (htor : centralizerPerfectCore (modelToG e (spATorus K n j)) ≤ centralizer ({t} : Set G))
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G))
    (hsh : SpOmegaBShapeAut e ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩)
      ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) j) : False := by
  set G₀ := spGlobal e with hG₀
  set θt := G₀.normalizerMonoidHom ⟨t, htN⟩ with hθt
  set θs := G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ with hθs
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hj : 1 ≤ j := hsh.1
  have hjn : 2 * j ≤ n := hsh.2.1
  obtain ⟨x₀, η, hα, hηx, hxx, ⟨β₀, hβ₀⟩, hFle, hFperf, hFcard, hFtor⟩ :=
    spOmegaBShapeAut_properties hperf htoral hK4 e hsh
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hLS : L ≤ G₀ := le_spGlobal hK4 (by omega) e
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
    exact card_centralizer_spARep_lt hj hjn
  have hx₀N : (x₀ : G) ∈ normalizer (G₀ : Set G) := le_normalizer x₀.2
  have hsxN : (g⁻¹ * t * g) * x₀ ∈ normalizer (G₀ : Set G) := mul_mem hg hx₀N
  rcases hcoset ⟨x, hxG⟩ hθ'2 with ⟨z, hz⟩ | hsh'
  ·
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
      rw [e1, normalizerMonoidHom_mul' hg hx₀N hsxN, normalizerMonoidHom_eq_conj_of_mem x₀.2 hx₀N]
      change θs * MulAut.conj x₀ = η
      rw [hα, mul_assoc, mulAut_mul_conj_eq_of_apply_eq hηx, ← mul_assoc, ← map_mul, hxx,
        map_one, one_mul]
    have hhG : h ∈ normalizer (G₀ : Set G) :=
      mem_normalizer_of_conj_mulAut hset hn hKc hf e ht hKt htN hhN β₀
        (by rw [hθh]; exact hβ₀)
    have hgG : g ∈ normalizer (G₀ : Set G) := by
      have : g = nn * h := by rw [hh]; group
      rw [this]
      exact mul_mem hnnN hhG
    exact absurd (card_le_card_fixedSubgroup_of_mem_normalizer hLS hLt hgG hg) (not_le.2 hfixLt)
  ·
    rw [← hθ'] at hsh'
    set θ' := G₀.normalizerMonoidHom ⟨t * x, ht'N⟩ with hθ'def
    obtain ⟨-, -, ψ', η', hψ', hα', hη', hfix', -, huniq'⟩ := hsh'
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
    have hcard' : Nat.card (fixedSubgroup θ') =
        Nat.card (centralizer ({spARep n j} : Set (StatedSp n K))) := by
      rw [hfix', Subgroup.card_map_of_injective hψ']
    have hΛle : Λ ≤ (fixedSubgroup θ').map G₀.subtype := (le_inf hΛL hΛx).trans hCL
    have hcardle : Nat.card ((fixedSubgroup θ').map G₀.subtype) ≤ Nat.card Λ := by
      rw [Subgroup.card_map_of_injective G₀.subtype_injective, hcard', hΛcard, hFcard]
    have hΛeq' : Λ = (fixedSubgroup θ').map G₀.subtype :=
      Subgroup.eq_of_le_of_card_ge hΛle hcardle
    have hΛeq : L ⊓ centralizer ({x} : Set G) ≤ Λ := hCL.trans hΛeq'.symm.le
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
      rw [← hΛeq'] at hu1
      have huL : (u : G) ∈ L := hΛL hu1
      show θt u = u
      apply Subtype.ext
      rw [hθt, Subgroup.normalizerMonoidHom_apply_apply_coe,
        ← mem_centralizer_iff.1 htC _ huL, mul_inv_cancel_right]
    have hθη : θt = η' := huniq' hcomm hfixle
    have hxψ : ((ψ' (spARep n j) : G₀) : G) = x := by
      have h1 : MulAut.conj (⟨x, hxG⟩ : G₀) * θt = MulAut.conj (ψ' (spARep n j)) * θt := by
        rw [← hθ', hα', ← hθη]
      have h2 : MulAut.conj (⟨x, hxG⟩ : G₀) = MulAut.conj (ψ' (spARep n j)) :=
        mul_right_cancel h1
      set p : G₀ := ψ' (spARep n j) with hp
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
    have hfixθ : fixedSubgroup θt = ψ'.range := by rw [hθη]; exact hη'
    have hLfix : L ≤ (fixedSubgroup θt).map G₀.subtype := by
      intro l hl
      refine ⟨⟨l, hLS hl⟩, ?_, rfl⟩
      show θt ⟨l, hLS hl⟩ = ⟨l, hLS hl⟩
      apply Subtype.ext
      rw [hθt, Subgroup.normalizerMonoidHom_apply_apply_coe]
      change t * l * t⁻¹ = l
      rw [← mem_centralizer_iff.1 htC l hl, mul_inv_cancel_right]
    have hLeq : L = (fixedSubgroup θt).map G₀.subtype := by
      refine Subgroup.eq_of_le_of_card_ge hLfix ?_
      rw [Subgroup.card_map_of_injective G₀.subtype_injective, hfixθ,
        MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψ', Subgroup.card_top,
        Nat.card_congr e.toEquiv]
    have hψL : ∀ y : StatedSp n K, (G₀.subtype.comp ψ') y ∈ L := by
      intro y
      refine hLeq.symm.le ⟨ψ' y, ?_, rfl⟩
      rw [hfixθ]
      exact ⟨y, rfl⟩
    obtain ⟨c', hc'L, hc'⟩ := exists_conj_eq_spARep_of_injective hn e
      (G₀.subtype.comp ψ') (G₀.subtype_injective.comp hψ') hψL j
    have hxl : x = c'⁻¹ * ((e.symm (spARep n j) : L) : G) * c'⁻¹⁻¹ := by
      rw [← hc', inv_inv]
      change x = c'⁻¹ * (c' * ((ψ' (spARep n j) : G₀) : G) * c'⁻¹) * c'
      rw [hxψ]
      group
    exact false_of_conj_spARep_of_toral e htC θs hact hFle hFtor hΛeq
      (spATorus_le_centralizer n j) (odd_card_spATorus hKc (by omega) n j) (inv_mem hc'L) hxl
      htor

end Main

end CFSG.SeitzReduction.SymplecticPilot

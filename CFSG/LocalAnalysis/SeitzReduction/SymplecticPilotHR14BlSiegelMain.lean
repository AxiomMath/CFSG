module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlSiegelCentral
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem false_of_spOmegaBType_central (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (htN : t ∈ normalizer (spGlobal e : Set G))
    (hZ : spGlobal e ⊓ centralizer (spGlobal e : Set G) = ⊥)
    (hodd : Odd (Nat.card (centralizer (spGlobal e : Set G))))
    (hperf : SpACentralizerPerfectInput) (htoral : SpAToralInput)
    (h2part : SpACentralizerTwoPartInput) (B : MulAut (spGlobal e) → ℕ → Prop)
    (hshape : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) (j : ℕ), 1 ≤ j →
      B ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) j →
        SpOmegaBShape e ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩)
          ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) j)
    (hcoset : ∀ y : spGlobal e,
      (MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩) *
          (MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩) = 1 →
        (∃ β : MulAut (spGlobal e), β * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ =
          (MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩) * β) ∨
        ∃ j, 1 ≤ j ∧ B (MulAut.conj y * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩) j)
    (htor : ∀ j, 1 ≤ j → 2 * j ≤ n →
      centralizerPerfectCore (modelToG e (spATorus K n j)) ≤ centralizer ({t} : Set G) ∨
        ∃ Z : Subgroup (StatedSp n K), Z ≤ spATorus K n j ∧
          ∀ h ∈ centralizer (modelToG e Z : Set G), orderOf (t * h * t⁻¹ * h⁻¹) ≠ 2) :
    ∀ (j : ℕ), 1 ≤ j → ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)),
      ¬ B ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj g hg hB
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  set θt := (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ with hθt
  set θs := (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ with hθs
  have hsh : SpOmegaBShape e θt θs j := hshape g hg j hj hB
  have hjn : 2 * j ≤ n := hsh.2.1
  obtain ⟨x₀, η, hα, hηx, hxx, ⟨z, hz⟩, hFle, hFperf, hFcard, hFtor, hFel⟩ :=
    spOmegaBShape_properties_central hperf htoral hK4 e hsh
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hLS : L ≤ (spGlobal e) := le_spGlobal hK4 (by omega) e
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega) e)
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)
  have hact : ∀ y : (spGlobal e),
      ((θs y : (spGlobal e)) : G) = (g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹ := fun y =>
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
  set Λ : Subgroup G :=
    (fixedSubgroup θs).map ((MulAut.conj g).toMonoidHom.comp (spGlobal e).subtype)
    with hΛ
  have hinj : Function.Injective ((MulAut.conj g).toMonoidHom.comp (spGlobal e).subtype) :=
    (MulAut.conj g).injective.comp (spGlobal e).subtype_injective
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
  have hxG : x ∈ (spGlobal e) := hLS hxL
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
  have hxN : x ∈ normalizer (spGlobal e : Set G) := le_normalizer hxG
  have ht'N : t * x ∈ normalizer (spGlobal e : Set G) := mul_mem htN hxN
  have hθ' : (spGlobal e).normalizerMonoidHom ⟨t * x, ht'N⟩ =
      MulAut.conj (⟨x, hxG⟩ : (spGlobal e)) * θt := by
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
  have hθ'2 : (MulAut.conj (⟨x, hxG⟩ : (spGlobal e)) * θt) *
      (MulAut.conj (⟨x, hxG⟩ : (spGlobal e)) * θt) = 1 := by
    rw [← hθ', ← map_mul,
      show (⟨t * x, ht'N⟩ : normalizer (spGlobal e : Set G)) * ⟨t * x, ht'N⟩ = 1 from
        Subtype.ext ht'2,
      map_one]
  have hx₀N : (x₀ : G) ∈ normalizer (spGlobal e : Set G) := le_normalizer x₀.2
  have hsxN : (g⁻¹ * t * g) * x₀ ∈ normalizer (spGlobal e : Set G) := mul_mem hg hx₀N
  have hθη : (spGlobal e).normalizerMonoidHom ⟨(g⁻¹ * t * g) * x₀, hsxN⟩ = η := by
    rw [normalizerMonoidHom_mul' hg hx₀N hsxN, normalizerMonoidHom_eq_conj_of_mem x₀.2 hx₀N]
    change θs * MulAut.conj x₀ = η
    rw [hα, mul_assoc, mulAut_mul_conj_eq_of_apply_eq hηx, ← mul_assoc, ← map_mul, hxx,
      map_one, one_mul]
  have hzN : (z : G) ∈ normalizer (spGlobal e : Set G) := le_normalizer z.2
  have hztN : (z : G) * t * (z : G)⁻¹ ∈ normalizer (spGlobal e : Set G) :=
    mul_mem (mul_mem hzN htN) (inv_mem hzN)
  have hθz : (spGlobal e).normalizerMonoidHom ⟨(z : G) * t * (z : G)⁻¹, hztN⟩ =
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
  have hg'eq : y⁻¹⁻¹ * t * y⁻¹ = t * x := by rw [inv_inv, hty]
  have hg' : y⁻¹⁻¹ * t * y⁻¹ ∈ normalizer (spGlobal e : Set G) := hg'eq ▸ ht'N
  have hθg' : (spGlobal e).normalizerMonoidHom ⟨y⁻¹⁻¹ * t * y⁻¹, hg'⟩ =
      MulAut.conj (⟨x, hxG⟩ : (spGlobal e)) * θt := by
    have e1 : (⟨y⁻¹⁻¹ * t * y⁻¹, hg'⟩ : normalizer (spGlobal e : Set G)) = ⟨t * x, ht'N⟩ :=
      Subtype.ext hg'eq
    rw [e1, hθ']
  have hfixLt : Nat.card (fixedSubgroup θs) < Nat.card L := by
    rw [hFcard, Nat.card_congr e.toEquiv]
    exact card_centralizer_spARep_lt hj hjn
  rcases hcoset ⟨x, hxG⟩ hθ'2 with ⟨β, hβ⟩ | ⟨j', hj', hB'⟩
  ·
    have hyN : y⁻¹ ∈ normalizer (spGlobal e : Set G) :=
      mem_normalizer_of_conj_mulAut hset (by omega) hKc hf e ht hKt htN hg' β
        (by rw [hθg']; exact hβ)
    have hcN : c ∈ normalizer (spGlobal e : Set G) := centralizer_le_normalizer _ hcC
    have hgG : g ∈ normalizer (spGlobal e : Set G) := by
      have : g = y⁻¹⁻¹ * (z : G)⁻¹ * c⁻¹ := by rw [inv_inv, hy]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hyN) (inv_mem hzN)) (inv_mem hcN)
    exact absurd (card_le_card_fixedSubgroup_of_mem_normalizer hLS hLt hgG hg) (not_le.2 hfixLt)
  ·
    set θ' := (spGlobal e).normalizerMonoidHom ⟨t * x, ht'N⟩ with hθ'def
    have he1 : (⟨y⁻¹⁻¹ * t * y⁻¹, hg'⟩ : normalizer (spGlobal e : Set G)) = ⟨t * x, ht'N⟩ :=
      Subtype.ext hg'eq
    have hB'' : B ((spGlobal e).normalizerMonoidHom ⟨y⁻¹⁻¹ * t * y⁻¹, hg'⟩) j' := by
      rw [he1]
      change B θ' j'
      rw [hθ']
      exact hB'
    have hjj' : j ≤ j' := by
      by_contra hlt
      exact ih j' (by omega) hj' y⁻¹ hg' hB''
    have hsh' : SpOmegaBShape e θt θ' j' := by
      have h1 := hshape y⁻¹ hg' j' hj' hB''
      rw [he1] at h1
      exact h1
    obtain ⟨-, hj'n, ψ', η', hψ', hα', hη', hfix', -, huniq'⟩ := hsh'
    have hCL : L ⊓ centralizer ({x} : Set G) ≤ (fixedSubgroup θ').map (spGlobal e).subtype := by
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
        Nat.card (centralizer ({spARep n j'} : Set (StatedSp n K))) := by
      rw [hfix', Subgroup.card_map_of_injective hψ']
    have hΛle : Λ ≤ (fixedSubgroup θ').map (spGlobal e).subtype := (le_inf hΛL hΛx).trans hCL
    have hdvd : Nat.card (centralizer ({spARep n j} : Set (StatedSp n K))) ∣
        Nat.card (centralizer ({spARep n j'} : Set (StatedSp n K))) := by
      have h1 := Subgroup.card_dvd_of_le hΛle
      rwa [hΛcard, hFcard, Subgroup.card_map_of_injective (spGlobal e).subtype_injective,
        hcard'] at h1
    have hj'eq : j' = j := by
      by_contra hne
      have hlt : j < j' := lt_of_le_of_ne hjj' (Ne.symm hne)
      have h1 := h2part n j f K hKc hjn
      have h2 := h2part n j' f K hKc hj'n
      have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd 2
      rw [h1, h2] at hle
      have h3 := spAExp_lt_of_lt (n := n) hj hlt (by omega)
      have h4 : f * spAExp n j' < f * spAExp n j := Nat.mul_lt_mul_of_pos_left h3 (by omega)
      omega
    rw [hj'eq] at hcard' hα' hfix'
    have hcardle : Nat.card ((fixedSubgroup θ').map (spGlobal e).subtype) ≤ Nat.card Λ := by
      rw [Subgroup.card_map_of_injective (spGlobal e).subtype_injective, hcard', hΛcard, hFcard]
    have hΛeq' : Λ = (fixedSubgroup θ').map (spGlobal e).subtype :=
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
      have hu1 : (u : G) ∈ (fixedSubgroup θ').map (spGlobal e).subtype := ⟨u, hu, rfl⟩
      rw [← hΛeq'] at hu1
      have huL : (u : G) ∈ L := hΛL hu1
      show θt u = u
      apply Subtype.ext
      rw [hθt, Subgroup.normalizerMonoidHom_apply_apply_coe,
        ← mem_centralizer_iff.1 htC _ huL, mul_inv_cancel_right]
    have hθη : θt = η' := huniq' hcomm hfixle
    have hxψ : ((ψ' (spARep n j) : spGlobal e) : G) = x := by
      have h1 : MulAut.conj (⟨x, hxG⟩ : spGlobal e) * θt =
          MulAut.conj (ψ' (spARep n j)) * θt := by
        rw [← hθ', hα', ← hθη]
      have h2 : MulAut.conj (⟨x, hxG⟩ : spGlobal e) = MulAut.conj (ψ' (spARep n j)) :=
        mul_right_cancel h1
      set p : spGlobal e := ψ' (spARep n j) with hp
      have hmem : (p : G)⁻¹ * x ∈ spGlobal e ⊓ centralizer (spGlobal e : Set G) := by
        refine ⟨(spGlobal e).mul_mem ((spGlobal e).inv_mem p.2) hxG,
          mem_centralizer_iff.2 fun u hu => ?_⟩
        have h4 := congrArg Subtype.val (DFunLike.congr_fun h2 ⟨u, hu⟩)
        change x * u * x⁻¹ = (p : G) * u * (p : G)⁻¹ at h4
        calc u * ((p : G)⁻¹ * x) = (p : G)⁻¹ * ((p : G) * u * (p : G)⁻¹) * x := by group
          _ = (p : G)⁻¹ * (x * u * x⁻¹) * x := by rw [← h4]
          _ = (p : G)⁻¹ * x * u := by group
      rw [hZ, mem_bot] at hmem
      calc (p : G) = (p : G) * ((p : G)⁻¹ * x) := by rw [hmem, mul_one]
        _ = x := by group
    have hfixθ : fixedSubgroup θt = ψ'.range := by rw [hθη]; exact hη'
    have hLfix : L ≤ (fixedSubgroup θt).map (spGlobal e).subtype := by
      intro l hl
      refine ⟨⟨l, hLS hl⟩, ?_, rfl⟩
      show θt ⟨l, hLS hl⟩ = ⟨l, hLS hl⟩
      apply Subtype.ext
      rw [hθt, Subgroup.normalizerMonoidHom_apply_apply_coe]
      change t * l * t⁻¹ = l
      rw [← mem_centralizer_iff.1 htC l hl, mul_inv_cancel_right]
    have hLeq : L = (fixedSubgroup θt).map (spGlobal e).subtype := by
      refine Subgroup.eq_of_le_of_card_ge hLfix ?_
      rw [Subgroup.card_map_of_injective (spGlobal e).subtype_injective, hfixθ,
        MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψ', Subgroup.card_top,
        Nat.card_congr e.toEquiv]
    have hψL : ∀ y : StatedSp n K, ((spGlobal e).subtype.comp ψ') y ∈ L := by
      intro y
      refine hLeq.symm.le ⟨ψ' y, ?_, rfl⟩
      rw [hfixθ]
      exact ⟨y, rfl⟩
    obtain ⟨c', hc'L, hc'⟩ := exists_conj_eq_spARep_of_injective (by omega) e
      ((spGlobal e).subtype.comp ψ') ((spGlobal e).subtype_injective.comp hψ') hψL j
    have hxl : x = c'⁻¹ * ((e.symm (spARep n j) : L) : G) * c'⁻¹⁻¹ := by
      rw [← hc', inv_inv]
      change x = c'⁻¹ * (c' * ((ψ' (spARep n j) : spGlobal e) : G) * c'⁻¹) * c'
      rw [hxψ]
      group
    rcases htor j hj hjn with hT | ⟨Z, hZ, hcen⟩
    · exact false_of_conj_spARep_of_toral e htC θs hact hFle hFtor hΛeq
        (spATorus_le_centralizer n j) (odd_card_spATorus hKc (by omega) n j) (inv_mem hc'L) hxl hT
    · exact false_of_conj_spARep_of_central e htC θs hact hα hFel hΛeq hZ
        (spATorus_le_centralizer n j) (odd_card_spATorus hKc (by omega) n j) (inv_mem hc'L) hxl
        hcen

end Main

end CFSG.SeitzReduction.SymplecticPilot

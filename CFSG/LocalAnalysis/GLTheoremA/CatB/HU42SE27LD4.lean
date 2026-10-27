module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27LDefs
import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
import CFSG.LocalAnalysis.SteinbergBVA7BinaryIsometryTwoParts
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.AGLEmbedding CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open QuadraticMap

private noncomputable abbrev Q : QuadraticForm (ZMod 2) V8 := quadPlus 4 (ZMod 2)

private theorem ncard_quad_one : {v : V8 | Q v = 1}.ncard = 120 := by
  have h := CFSG.LocalAnalysis.SteinbergBV.BinaryTwoParts.two_mul_ncard_quadPlus 3
  have h' : 2 * {v : V8 | Q v = 1}.ncard + 2 ^ 4 = 4 ^ 4 := by
    simpa [Q] using h
  norm_num at h'
  omega

private theorem ncard_polar_eq_one (r : V8) (hr : r ≠ 0) :
    {a : V8 | polar Q a r = 1}.ncard = 128 := by
  classical
  let φ : Module.Dual (ZMod 2) V8 :=
    { toFun := fun a => polar Q a r
      map_add' := by
        intro a b
        rw [polar_add_left]
      map_smul' := by
        intro c a
        rw [polar_smul_left]
        simp }
  have hφ : φ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero
      (Q := Q) (nondegenerate_polarBilin_quadPlus 4 (ZMod 2)) hr
    exact hv (by
      have := congrArg (fun f : Module.Dual (ZMod 2) V8 => f v) h0
      have hvr : polar Q r v = 0 := by
        rw [polar_comm]
        simpa [φ] using this
      exact hvr)
  have hdim : Module.finrank (ZMod 2) V8 = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [ι8]
  have hkerdim : Module.finrank (ZMod 2) (LinearMap.ker φ) = 7 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := φ) hφ
    omega
  have hkercard : Nat.card (LinearMap.ker φ) = 128 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker φ), hkerdim,
      Nat.card_zmod]
    norm_num
  have hVcard : Nat.card V8 = 256 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V8), hdim, Nat.card_zmod]
    norm_num
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hcompl_eq : (LinearMap.ker φ : Set V8)ᶜ = {a : V8 | polar Q a r = 1} := by
    ext a
    simp only [Set.mem_compl_iff, LinearMap.mem_ker, Set.mem_setOf_eq]
    constructor
    · intro h
      rcases h01 (φ a) with h0 | h1
      · exact absurd h0 h
      · exact h1
    · intro h h0
      have hz : φ a = 0 := h0
      change polar Q a r = 0 at hz
      rw [h] at hz
      exact one_ne_zero hz
  have hsplit := Set.ncard_add_ncard_compl (LinearMap.ker φ : Set V8)
  have hkerncard : (LinearMap.ker φ : Set V8).ncard = 128 := by
    rw [← Nat.card_coe_set_eq]
    exact hkercard
  rw [hkerncard, hVcard, hcompl_eq] at hsplit
  omega

private theorem ncard_quad_one_polar_eq_one (r : V8) (hrQ : Q r = 0) (hr : r ≠ 0) :
    {a : V8 | Q a = 1 ∧ polar Q a r = 1}.ncard = 64 := by
  classical
  let Z : Set V8 := {a | Q a = 1 ∧ polar Q a r = 1}
  let W : Set V8 := {a | Q a = 0 ∧ polar Q a r = 1}
  have hrr : polar Q r r = 0 := CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hrQ
  have hZW : Z.ncard = W.ncard := by
    refine Set.ncard_congr (fun a _ => a + r) ?_ ?_ ?_
    · intro a ha
      exact ⟨by
          rw [QuadraticMap.map_add Q a r, ha.1, hrQ, ha.2]
          decide,
        by
          rw [polar_add_left, ha.2, hrr]
          decide⟩
    · intro a b _ _ hab
      exact add_right_cancel hab
    · intro b hb
      refine ⟨b + r, ⟨?_, ?_⟩, ?_⟩
      · rw [QuadraticMap.map_add Q b r, hb.1, hrQ, hb.2]
        decide
      · rw [polar_add_left, hb.2, hrr]
        decide
      · show b + r + r = b
        rw [add_assoc, ZModModule.add_self, add_zero]
  have hF : ({a : V8 | polar Q a r = 1} : Set V8).ncard = 128 :=
    ncard_polar_eq_one r hr
  have hunion : ({a : V8 | polar Q a r = 1} : Set V8) = Z ∪ W := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_union, Z, W]
    constructor
    · intro h
      have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      rcases h01 (Q a) with h0 | h1 <;> tauto
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact h2
  have hdisj : Disjoint Z W := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact one_ne_zero (ha.1.symm.trans hb.1)
  rw [hunion, Set.ncard_union_eq hdisj, hZW] at hF
  change Z.ncard = 64
  omega

private theorem ncard_quad_one_polar_eq_zero (r : V8) (hrQ : Q r = 0) (hr : r ≠ 0) :
    {a : V8 | Q a = 1 ∧ polar Q a r = 0}.ncard = 56 := by
  have h120 : ({a : V8 | Q a = 1} : Set V8).ncard = 120 := ncard_quad_one
  have hZ := ncard_quad_one_polar_eq_one r hrQ hr
  have hsplit : ({a : V8 | Q a = 1} : Set V8) =
      {a : V8 | Q a = 1 ∧ polar Q a r = 0} ∪
        {a : V8 | Q a = 1 ∧ polar Q a r = 1} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro h
      have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      rcases h01 (polar Q a r) with hp | hp <;> tauto
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact h1
  have hdisj : Disjoint {a : V8 | Q a = 1 ∧ polar Q a r = 0}
      {a : V8 | Q a = 1 ∧ polar Q a r = 1} := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact zero_ne_one (ha.2.symm.trans hb.2)
  rw [hsplit, Set.ncard_union_eq hdisj, hZ] at h120
  omega

private theorem sum_norm_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (M : Submodule (ZMod 2) V) (U G : Module.End (ZMod 2) V) (x : V)
    (hGx : G x ∈ M) (hG2x : G (G x) ∈ M)
    (hU3 : U ^ 3 = 1)
    (hU2M : ∀ y ∈ M, ((1 + U + U ^ 2 : Module.End (ZMod 2) V)) y = 0)
    (hUG : U * G = G * U) :
    (((1 + G + G ^ 2) + (1 + U * G + (U * G) ^ 2) +
      (1 + U ^ 2 * G + (U ^ 2 * G) ^ 2) : Module.End (ZMod 2) V)) x = x := by
  have h4 : U ^ 4 = U := by
    calc U ^ 4 = U ^ 3 * U := by rw [pow_succ]
      _ = 1 * U := by rw [hU3]
      _ = U := by rw [one_mul]
  have hUG2 : (U * G) ^ 2 = U ^ 2 * G ^ 2 := by
    rw [pow_two, pow_two]
    calc (U * G) * (U * G) = U * (G * U) * G := by noncomm_ring
      _ = U * (U * G) * G := by rw [hUG]
      _ = U * U * (G * G) := by noncomm_ring
  have hUG' : U ^ 2 * G = G * U ^ 2 := by
    rw [pow_two]
    calc (U * U) * G = U * (U * G) := by noncomm_ring
      _ = U * (G * U) := by rw [hUG]
      _ = U * G * U := by noncomm_ring
      _ = G * U * U := by rw [hUG]
      _ = G * (U * U) := by noncomm_ring
  have hU2G2 : (U ^ 2 * G) ^ 2 = U ^ 4 * G ^ 2 := by
    rw [pow_two, pow_two]
    calc (U ^ 2 * G) * (U ^ 2 * G) = U ^ 2 * (G * U ^ 2) * G := by noncomm_ring
      _ = U ^ 2 * (U ^ 2 * G) * G := by rw [hUG']
      _ = U ^ 4 * G ^ 2 := by noncomm_ring
  have h3 : ((1 : Module.End (ZMod 2) V) + 1 + 1) = 1 := by
    have h2 : ((1 : Module.End (ZMod 2) V) + 1) = 0 := by
      ext v
      simp only [LinearMap.add_apply, Module.End.one_apply]
      exact ZModModule.add_self v
    rw [h2, zero_add]
  have hop : ((1 + G + G ^ 2) + (1 + U * G + (U * G) ^ 2) +
      (1 + U ^ 2 * G + (U ^ 2 * G) ^ 2) : Module.End (ZMod 2) V) =
      (1 + 1 + 1) + (1 + U + U ^ 2) * G + (1 + U ^ 2 + U ^ 4) * G ^ 2 := by
    rw [hUG2, hU2G2]
    noncomm_ring
  have hcoef : (1 + U ^ 2 + U ^ 4 : Module.End (ZMod 2) V) = 1 + U + U ^ 2 := by
    rw [h4]
    abel
  have hG : ((1 + U + U ^ 2 : Module.End (ZMod 2) V) * G) x = 0 := by
    rw [Module.End.mul_apply]
    exact hU2M (G x) hGx
  have hG2 : ((1 + U ^ 2 + U ^ 4 : Module.End (ZMod 2) V) * G ^ 2) x = 0 := by
    rw [hcoef]
    rw [Module.End.mul_apply]
    exact hU2M (G (G x)) hG2x
  calc
    (((1 + G + G ^ 2) + (1 + U * G + (U * G) ^ 2) +
        (1 + U ^ 2 * G + (U ^ 2 * G) ^ 2) : Module.End (ZMod 2) V)) x
        = (((1 + 1 + 1) + (1 + U + U ^ 2) * G + (1 + U ^ 2 + U ^ 4) * G ^ 2 :
          Module.End (ZMod 2) V)) x := by rw [hop]
    _ = (((1 + (1 + U + U ^ 2) * G + (1 + U ^ 2 + U ^ 4) * G ^ 2 :
          Module.End (ZMod 2) V))) x := by rw [h3]
    _ = x := by
      rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, hG, hG2, add_zero,
        add_zero]

private theorem plane_lemma {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (G : Subgroup (V ≃ₗ[ZMod 2] V)) (M : Submodule (ZMod 2) V)
    (hM : M ≠ ⊥)
    (hMinv : ∀ g ∈ G, ∀ x ∈ M, g x ∈ M)
    (hcomm : ∀ g ∈ G, ∀ h ∈ G, g * h = h * g)
    (hexp : ∀ g ∈ G, g ^ 3 = 1)
    (hfix : ∀ x ∈ M, (∀ g ∈ G, g x = x) → x = 0) :
    ∃ (x : V) (e : V ≃ₗ[ZMod 2] V), x ∈ M ∧ x ≠ 0 ∧ e ∈ G ∧ e x ≠ x ∧
      e (e x) = x + e x ∧ ∀ g ∈ G, g x = x ∨ g x = e x ∨ g x = x + e x := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ N : Submodule (ZMod 2) V, N ≤ M ∧ N ≠ ⊥ ∧
      (∀ g ∈ G, ∀ x ∈ N, g x ∈ N) ∧ Module.finrank (ZMod 2) N = n
  have hP : ∃ n, P n := ⟨_, M, le_rfl, hM, hMinv, rfl⟩
  obtain ⟨M', hM'M, hM'ne, hM'inv, hM'dim⟩ := Nat.find_spec hP
  have hmin : ∀ N : Submodule (ZMod 2) V, N ≤ M → N ≠ ⊥ →
      (∀ g ∈ G, ∀ x ∈ N, g x ∈ N) →
      Module.finrank (ZMod 2) M' ≤ Module.finrank (ZMod 2) N := by
    intro N hNM hNne hNinv
    have hle := Nat.find_le (p := P) (h := hP) ⟨N, hNM, hNne, hNinv, rfl⟩
    simpa [hM'dim] using hle
  haveI : FiniteDimensional (ZMod 2) ↥M' := Submodule.finiteDimensional_of_le (le_top)
  let K : (V ≃ₗ[ZMod 2] V) → Submodule (ZMod 2) V := fun g =>
    M' ⊓ LinearMap.ker ((g : V →ₗ[ZMod 2] V) - 1)
  have hKinv : ∀ g ∈ G, ∀ h ∈ G, ∀ x ∈ K g, h x ∈ K g := by
    intro g hg h hh x hx
    obtain ⟨hxM', hxker⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨hM'inv h hh x hxM', ?_⟩
    rw [LinearMap.mem_ker] at hxker ⊢
    have hgx : (g : V →ₗ[ZMod 2] V) x = x := by
      simpa [LinearMap.sub_apply, sub_eq_zero] using hxker
    have hgh : (g : V →ₗ[ZMod 2] V) (h x) = h ((g : V →ₗ[ZMod 2] V) x) := by
      have hc := congrArg (fun e : V ≃ₗ[ZMod 2] V => e x) (hcomm g hg h hh)
      simpa [LinearEquiv.mul_apply] using hc
    simpa [LinearMap.sub_apply, hgh, hgx] using sub_self ((h : V ≃ₗ[ZMod 2] V) x)
  have hK : ∀ g ∈ G, K g = ⊥ ∨ K g = M' := by
    intro g hg
    by_cases hbot : K g = ⊥
    · exact Or.inl hbot
    · right
      haveI : FiniteDimensional (ZMod 2) ↥(K g) :=
        Submodule.finiteDimensional_of_le (le_top)
      have hleM : K g ≤ M := inf_le_left.trans hM'M
      have hfin : Module.finrank (ZMod 2) M' ≤ Module.finrank (ZMod 2) (K g) :=
        hmin (K g) hleM hbot (hKinv g hg)
      exact Submodule.eq_of_le_of_finrank_le inf_le_left hfin
  have hnotall : ∃ g ∈ G, K g ≠ M' := by
    by_contra h
    push Not at h
    have hfixall : ∀ x ∈ M', ∀ g ∈ G, g x = x := by
      intro x hx g hg
      have hxK : x ∈ K g := by rw [h g hg]; exact hx
      obtain ⟨-, hxker⟩ := Submodule.mem_inf.mp hxK
      rw [LinearMap.mem_ker] at hxker
      simpa [LinearMap.sub_apply, sub_eq_zero] using hxker
    obtain ⟨x, hxM', hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM'ne
    exact hx0 (hfix x (hM'M hxM') (fun g hg => hfixall x hxM' g hg))
  obtain ⟨e, heG, heK⟩ := hnotall
  have hKe : K e = ⊥ := (hK e heG).resolve_right heK
  have hefree : ∀ y ∈ M', e y = y → y = 0 := by
    intro y hyM' hy
    have hyK : y ∈ K e := Submodule.mem_inf.mpr ⟨hyM', by
      rw [LinearMap.mem_ker]
      simpa [LinearMap.sub_apply, sub_eq_zero] using hy⟩
    rw [hKe] at hyK
    simpa using hyK
  have he3 : e ^ 3 = 1 := hexp e heG
  let u : V ≃ₗ[ZMod 2] V := e⁻¹
  have huG : u ∈ G := by simpa [u] using G.inv_mem heG
  have hu3 : u ^ 3 = 1 := by
    change (e⁻¹) ^ 3 = 1
    rw [inv_pow, he3, inv_one]
  have hufree : ∀ y ∈ M', u y = y → y = 0 := by
    intro y hyM' hy
    have h := congrArg e hy
    have h' : y = e y := by simpa [u] using h
    exact hefree y hyM' (h'.symm)
  have hucomm : ∀ g ∈ G, u * g = g * u := by
    intro g hg
    have hc : Commute e g := hcomm e heG g hg
    change u * g = g * u
    exact hc.inv_left
  let U : Module.End (ZMod 2) V := u
  let Elin : Module.End (ZMod 2) V := e
  have hU3 : U ^ 3 = 1 := by
    ext y
    change u (u (u y)) = y
    have h := congrArg (fun f : V ≃ₗ[ZMod 2] V => f y) hu3
    simpa [pow_three, LinearEquiv.mul_apply] using h
  have hsum_u : ∀ y ∈ M', ((1 + U + U ^ 2 : Module.End (ZMod 2) V)) y = 0 := by
    intro y hy
    let w := ((1 + U + U ^ 2 : Module.End (ZMod 2) V)) y
    have hwM' : w ∈ M' := by
      have hy1 : U y ∈ M' := hM'inv u huG y hy
      have hy2 : (U ^ 2) y ∈ M' := by
        have h := hM'inv u huG (U y) hy1
        simpa [U, pow_two, Module.End.mul_apply] using h
      have h1 : y + U y ∈ M' := M'.add_mem hy hy1
      have h2 : (1 + U + U ^ 2 : Module.End (ZMod 2) V) y ∈ M' := by
        simpa [LinearMap.add_apply, Module.End.one_apply] using M'.add_mem h1 hy2
      exact h2
    have hwfix : U w = w := by
      have hop : U * (1 + U + U ^ 2) = 1 + U + U ^ 2 := by
        calc U * (1 + U + U ^ 2) = U + U ^ 2 + U ^ 3 := by noncomm_ring
          _ = U + U ^ 2 + 1 := by rw [hU3]
          _ = 1 + U + U ^ 2 := by abel
      calc U w = U (((1 + U + U ^ 2 : Module.End (ZMod 2) V)) y) := rfl
        _ = (U * (1 + U + U ^ 2 : Module.End (ZMod 2) V)) y := by
              rw [Module.End.mul_apply]
        _ = ((1 + U + U ^ 2) : Module.End (ZMod 2) V) y := by rw [hop]
        _ = w := rfl
    exact hufree w hwM' (by simpa [U] using hwfix)
  have hsum_e : ∀ y ∈ M', ((1 + Elin + Elin ^ 2 : Module.End (ZMod 2) V)) y = 0 := by
    intro y hy
    let w := ((1 + Elin + Elin ^ 2 : Module.End (ZMod 2) V)) y
    have hwM' : w ∈ M' := by
      have hy1 : Elin y ∈ M' := hM'inv e heG y hy
      have hy2 : (Elin ^ 2) y ∈ M' := by
        have h := hM'inv e heG (Elin y) hy1
        simpa [Elin, pow_two, Module.End.mul_apply] using h
      have h1 : y + Elin y ∈ M' := M'.add_mem hy hy1
      have h2 : (1 + Elin + Elin ^ 2 : Module.End (ZMod 2) V) y ∈ M' := by
        simpa [LinearMap.add_apply, Module.End.one_apply] using M'.add_mem h1 hy2
      exact h2
    have hwfix : Elin w = w := by
      have hop : Elin * (1 + Elin + Elin ^ 2) = 1 + Elin + Elin ^ 2 := by
        calc Elin * (1 + Elin + Elin ^ 2) = Elin + Elin ^ 2 + Elin ^ 3 := by noncomm_ring
          _ = Elin + Elin ^ 2 + 1 := by
              have h : Elin ^ 3 = 1 := by
                ext z
                change e (e (e z)) = z
                have h := congrArg (fun f : V ≃ₗ[ZMod 2] V => f z) he3
                simpa [pow_three, LinearEquiv.mul_apply] using h
              rw [h]
          _ = 1 + Elin + Elin ^ 2 := by abel
      calc Elin w = Elin (((1 + Elin + Elin ^ 2 : Module.End (ZMod 2) V)) y) := rfl
        _ = (Elin * (1 + Elin + Elin ^ 2 : Module.End (ZMod 2) V)) y := by
              rw [Module.End.mul_apply]
        _ = ((1 + Elin + Elin ^ 2) : Module.End (ZMod 2) V) y := by rw [hop]
        _ = w := rfl
    exact hefree w hwM' (by simpa [Elin] using hwfix)
  obtain ⟨x, hxM', hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM'ne
  have he_sq : e (e x) = x + e x := by
    have h := hsum_e x hxM'
    have h' : (x + e x) + e (e x) = 0 := by
      simpa [Elin, pow_two, LinearMap.add_apply, Module.End.one_apply, add_assoc] using h
    have hneg : -(x + e x) = x + e x := by
      rw [neg_eq_iff_add_eq_zero]
      exact ZModModule.add_self (x + e x)
    have h2 : x + e x = -(e (e x)) := eq_neg_of_add_eq_zero_left h'
    have hneg2 : -(e (e x)) = e (e x) := by
      rw [neg_eq_iff_add_eq_zero]
      exact ZModModule.add_self (e (e x))
    calc e (e x) = -(e (e x)) := hneg2.symm
      _ = x + e x := h2.symm
  have hmain : ∀ g ∈ G, g x = x ∨ g x = e x ∨ g x = x + e x := by
    intro g hg
    let Glin : Module.End (ZMod 2) V := g
    have hGx : Glin x ∈ M' := hM'inv g hg x hxM'
    have hG2x : Glin (Glin x) ∈ M' := hM'inv g hg (Glin x) hGx
    have hUG : U * Glin = Glin * U := by
      ext y
      change u (g y) = g (u y)
      have h := congrArg (fun f : V ≃ₗ[ZMod 2] V => f y) (hucomm g hg)
      simpa [LinearEquiv.mul_apply] using h
    have hsum := sum_norm_apply M' U Glin x hGx hG2x hU3 hsum_u hUG
    let P0 := ((1 + Glin + Glin ^ 2 : Module.End (ZMod 2) V)) x
    let P1 := ((1 + U * Glin + (U * Glin) ^ 2 : Module.End (ZMod 2) V)) x
    let P2 := ((1 + U ^ 2 * Glin + (U ^ 2 * Glin) ^ 2 : Module.End (ZMod 2) V)) x
    have hsum' : P0 + P1 + P2 = x := by
      simpa [P0, P1, P2, LinearMap.add_apply] using hsum
    have hsome : P0 ≠ 0 ∨ P1 ≠ 0 ∨ P2 ≠ 0 := by
      by_contra h
      push Not at h
      obtain ⟨h0, h1, h2⟩ := h
      rw [h0, h1, h2] at hsum'
      have hxzero : x = 0 := by simpa using hsum'.symm
      exact hx0 hxzero
    have hP0M' : P0 ∈ M' := by
      have h2 : (Glin ^ 2) x ∈ M' := by
        have h := hM'inv g hg (Glin x) hGx
        simpa [Glin, pow_two, Module.End.mul_apply] using h
      have h := M'.add_mem (M'.add_mem hxM' hGx) h2
      simpa [P0, LinearMap.add_apply, Module.End.one_apply] using h
    have hP1M' : P1 ∈ M' := by
      have hy : (U * Glin) x ∈ M' := by
        simpa [U, Glin, Module.End.mul_apply] using hM'inv u huG (Glin x) hGx
      have h2 : ((U * Glin) ^ 2) x ∈ M' := by
        have hg' : Glin ((U * Glin) x) ∈ M' := hM'inv g hg ((U * Glin) x) hy
        have h := hM'inv u huG (Glin ((U * Glin) x)) hg'
        simpa [pow_two, Module.End.mul_apply, U, Glin] using h
      have h := M'.add_mem (M'.add_mem hxM' hy) h2
      simpa [P1, LinearMap.add_apply, Module.End.one_apply] using h
    have hP2M' : P2 ∈ M' := by
      have hu2x : (U ^ 2 * Glin) x ∈ M' := by
        have h1 : U (Glin x) ∈ M' := by
          simpa [U, Glin, Module.End.mul_apply] using hM'inv u huG (Glin x) hGx
        have h := hM'inv u huG (U (Glin x)) h1
        simpa [pow_two, Module.End.mul_apply, U, Glin] using h
      have h2 : ((U ^ 2 * Glin) ^ 2) x ∈ M' := by
        have hg' : Glin ((U ^ 2 * Glin) x) ∈ M' := hM'inv g hg ((U ^ 2 * Glin) x) hu2x
        have h1 : U (Glin ((U ^ 2 * Glin) x)) ∈ M' := by
          simpa [U, Glin, Module.End.mul_apply] using hM'inv u huG (Glin ((U ^ 2 * Glin) x)) hg'
        have h := hM'inv u huG (U (Glin ((U ^ 2 * Glin) x))) h1
        simpa [pow_two, Module.End.mul_apply, U, Glin] using h
      have h := M'.add_mem (M'.add_mem hxM' hu2x) h2
      simpa [P2, LinearMap.add_apply, Module.End.one_apply] using h
    have fix_all_of_K : ∀ h : V ≃ₗ[ZMod 2] V, h ∈ G → K h = M' → ∀ y ∈ M', h y = y := by
      intro h hh hK y hy
      have hyK : y ∈ K h := by rw [hK]; exact hy
      obtain ⟨-, hyker⟩ := Submodule.mem_inf.mp hyK
      rw [LinearMap.mem_ker] at hyker
      simpa [LinearMap.sub_apply, sub_eq_zero] using hyker
    rcases hsome with hP0 | hP1 | hP2
    · left
      have hfixP0 : Glin P0 = P0 := by
        have hop : Glin * (1 + Glin + Glin ^ 2) = 1 + Glin + Glin ^ 2 := by
          calc Glin * (1 + Glin + Glin ^ 2) = Glin + Glin ^ 2 + Glin ^ 3 := by noncomm_ring
            _ = Glin + Glin ^ 2 + 1 := by
                have h : Glin ^ 3 = 1 := by
                  have h := hexp g hg
                  ext z
                  change g (g (g z)) = z
                  have hz := congrArg (fun f : V ≃ₗ[ZMod 2] V => f z) h
                  simpa [pow_three, LinearEquiv.mul_apply] using hz
                rw [h]
            _ = 1 + Glin + Glin ^ 2 := by abel
        calc Glin P0 = Glin (((1 + Glin + Glin ^ 2 : Module.End (ZMod 2) V)) x) := rfl
          _ = (Glin * (1 + Glin + Glin ^ 2 : Module.End (ZMod 2) V)) x := by
                rw [Module.End.mul_apply]
          _ = ((1 + Glin + Glin ^ 2) : Module.End (ZMod 2) V) x := by rw [hop]
          _ = P0 := rfl
      have hP0K : P0 ∈ K g := Submodule.mem_inf.mpr ⟨hP0M', by
        rw [LinearMap.mem_ker]
        have h : ((g : V →ₗ[ZMod 2] V) - 1) P0 = 0 := by
          change Glin P0 - P0 = 0
          rw [hfixP0, sub_self]
        exact h⟩
      have hKg : K g = M' := (hK g hg).resolve_left (fun hbot => hP0 (by
        rw [hbot] at hP0K
        simpa using hP0K))
      exact fix_all_of_K g hg hKg x hxM'
    · right; left
      have hfixP1 : (u * g) P1 = P1 := by
        have hG3 : Glin ^ 3 = 1 := by
          have h := hexp g hg
          ext z
          change g (g (g z)) = z
          have hz := congrArg (fun f : V ≃ₗ[ZMod 2] V => f z) h
          simpa [pow_three, LinearEquiv.mul_apply] using hz
        have hUG3 : (U * Glin) ^ 3 = 1 := by
          rw [Commute.mul_pow (show Commute U Glin from hUG), hU3, hG3, one_mul]
        have hop : (U * Glin) * (1 + U * Glin + (U * Glin) ^ 2) =
            1 + U * Glin + (U * Glin) ^ 2 := by
          calc (U * Glin) * (1 + U * Glin + (U * Glin) ^ 2) =
              (U * Glin) + (U * Glin) ^ 2 + (U * Glin) ^ 3 := by noncomm_ring
            _ = (U * Glin) + (U * Glin) ^ 2 + 1 := by rw [hUG3]
            _ = 1 + U * Glin + (U * Glin) ^ 2 := by abel
        calc (u * g) P1 = (u * g) (((1 + U * Glin + (U * Glin) ^ 2 :
              Module.End (ZMod 2) V)) x) := rfl
          _ = ((U * Glin) * (1 + U * Glin + (U * Glin) ^ 2 :
                Module.End (ZMod 2) V)) x := by
              rw [Module.End.mul_apply]; rfl
          _ = ((1 + U * Glin + (U * Glin) ^ 2 : Module.End (ZMod 2) V)) x := by rw [hop]
          _ = P1 := rfl
      have hP1K : P1 ∈ K (u * g) := Submodule.mem_inf.mpr ⟨hP1M', by
        rw [LinearMap.mem_ker]
        change (u * g) P1 - P1 = 0
        rw [hfixP1, sub_self]⟩
      have hKu : K (u * g) = M' := (hK (u * g) (G.mul_mem huG hg)).resolve_left (fun hbot => hP1 (by
        rw [hbot] at hP1K
        simpa using hP1K))
      have hu_fix : (u * g) x = x := fix_all_of_K (u * g) (G.mul_mem huG hg) hKu x hxM'
      have h := congrArg e hu_fix
      simpa [u, LinearEquiv.mul_apply] using h
    · right; right
      have hfixP2 : (u ^ 2 * g) P2 = P2 := by
        have hU2G : (U ^ 2 * Glin) = (U ^ 2) * Glin := rfl
        have hG3 : Glin ^ 3 = 1 := by
          have h := hexp g hg
          ext z
          change g (g (g z)) = z
          have hz := congrArg (fun f : V ≃ₗ[ZMod 2] V => f z) h
          simpa [pow_three, LinearEquiv.mul_apply] using hz
        have hU2G : Commute (U ^ 2) Glin := (show Commute U Glin from hUG).pow_left 2
        have hU2G3 : (U ^ 2 * Glin) ^ 3 = 1 := by
          rw [Commute.mul_pow hU2G, hG3]
          have h : (U ^ 2) ^ 3 = 1 := by
            calc (U ^ 2) ^ 3 = U ^ (2 * 3) := by rw [← pow_mul]
              _ = U ^ 6 := by norm_num
              _ = (U ^ 3) ^ 2 := by rw [← pow_mul]
              _ = 1 := by rw [hU3, one_pow]
          rw [h, one_mul]
        have hop : (U ^ 2 * Glin) * (1 + U ^ 2 * Glin + (U ^ 2 * Glin) ^ 2) =
            1 + U ^ 2 * Glin + (U ^ 2 * Glin) ^ 2 := by
          calc (U ^ 2 * Glin) * (1 + U ^ 2 * Glin + (U ^ 2 * Glin) ^ 2) =
              (U ^ 2 * Glin) + (U ^ 2 * Glin) ^ 2 + (U ^ 2 * Glin) ^ 3 := by noncomm_ring
            _ = (U ^ 2 * Glin) + (U ^ 2 * Glin) ^ 2 + 1 := by rw [hU2G3]
            _ = 1 + U ^ 2 * Glin + (U ^ 2 * Glin) ^ 2 := by abel
        calc (u ^ 2 * g) P2 = (u ^ 2 * g) (((1 + U ^ 2 * Glin + (U ^ 2 * Glin) ^ 2 :
              Module.End (ZMod 2) V)) x) := rfl
          _ = ((U ^ 2 * Glin) * (1 + U ^ 2 * Glin + (U ^ 2 * Glin) ^ 2 :
                Module.End (ZMod 2) V)) x := by
              rw [Module.End.mul_apply]; rfl
          _ = ((1 + U ^ 2 * Glin + (U ^ 2 * Glin) ^ 2 : Module.End (ZMod 2) V)) x := by rw [hop]
          _ = P2 := rfl
      have hP2K : P2 ∈ K (u ^ 2 * g) := Submodule.mem_inf.mpr ⟨hP2M', by
        rw [LinearMap.mem_ker]
        change (u ^ 2 * g) P2 - P2 = 0
        rw [hfixP2, sub_self]⟩
      have hu2G : u ^ 2 ∈ G := by simpa [pow_two] using G.mul_mem huG huG
      have hKu : K (u ^ 2 * g) = M' :=
        (hK (u ^ 2 * g) (G.mul_mem hu2G hg)).resolve_left (fun hbot => hP2 (by
          rw [hbot] at hP2K
          simpa using hP2K))
      have hu_fix : (u ^ 2 * g) x = x := fix_all_of_K (u ^ 2 * g) (G.mul_mem hu2G hg) hKu x hxM'
      have hgx : g x = e (e x) := by
        have h := congrArg (fun y => e (e y)) hu_fix
        simpa [u, pow_two, LinearEquiv.mul_apply] using h
      rw [hgx, he_sq]
  exact ⟨x, e, hM'M hxM', hx0, heG, by
    intro h
    exact hx0 (hefree x hxM' h), he_sq, hmain⟩

private theorem isometry_of_mem_Om8 {g : GL ι8 (ZMod 2)} (hg : g ∈ Om8) :
    toLinEquiv ι8 (ZMod 2) g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  elementaryGroup_le_orthogonalGroup Q ((mem_Om8_iff g).1 hg)

private theorem eichler_comm {x y : V8} (hx : Q x = 0) (hy : Q y = 0)
    (hxy : polar Q x y = 0) : eichler Q x y = eichler Q y x := by
  ext v
  rw [eichler_apply hx hxy, eichler_apply hy (by rwa [polar_comm])]
  simp only [hx, hy, mul_zero, zero_add]
  rw [sub_eq_add_V8, sub_eq_add_V8]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem eichler_ne_one_of_not_mem_span {u w : V8} (hu : Q u = 0) (hu0 : u ≠ 0)
    (huw : polar Q u w = 0) (hw : w ∉ Submodule.span (ZMod 2) {u}) :
    eichler Q u w ≠ 1 := by
  intro h
  have h' : eichler Q u w = eichler Q u 0 := by rw [h, eichler_zero_right]
  rw [eichler_eq_eichler_iff (nondegenerate_polarBilin_quadPlus 4 (ZMod 2)) hu hu0 huw
    (polar_zero_right Q u)] at h'
  obtain ⟨c, hc⟩ := h'
  have hw_eq : w = -(c • u) := eq_neg_of_add_eq_zero_left hc.symm
  apply hw
  rw [hw_eq]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ c (Submodule.subset_span (by simp)))

theorem invCentOn_Om8_of (hT : OmTSFact) : InvCentOn ↥CFSG.AGLEmbedding.Om8 := by
  intro E U₀ s hEab hEcard hU2 hUne hNorm hs hsne hsect
  obtain ⟨R₀, hRne, hRsing, hRinv⟩ := hT E U₀ hU2 hUne hNorm
  let L : ↥CFSG.AGLEmbedding.Om8 →* (V8 ≃ₗ[ZMod 2] V8) :=
    (toLinEquiv ι8 (ZMod 2)).toMonoidHom.comp (Subgroup.subtype CFSG.AGLEmbedding.Om8)
  by_cases hA : ∃ r : V8, r ∈ R₀ ∧ r ≠ 0 ∧
      ∀ e ∈ E, toLinEquiv ι8 (ZMod 2) (e : GL ι8 (ZMod 2)) r = r
  · obtain ⟨r, hrR, hr0, hrfix⟩ := hA
    have hrQ : Q r = 0 := hRsing r hrR
    let Y : Set V8 := {a | Q a = 1 ∧ polar Q a r = 0}
    have hYcard : Y.ncard = 56 := ncard_quad_one_polar_eq_zero r hrQ hr0
    letI : MulAction ↥E V8 := MulAction.compHom V8 (L.comp E.subtype)
    have hsmul : ∀ (e : ↥E) (a : V8), e • a = L ((e : ↥E) : ↥CFSG.AGLEmbedding.Om8) a :=
      fun _ _ => rfl
    have hYinv : ∀ (e : ↥E) (a : V8), a ∈ Y → e • a ∈ Y := by
      intro e a ha
      have hLeO : L ((e : ↥E) : ↥CFSG.AGLEmbedding.Om8) ∈
          TauCeti.QuadraticMap.orthogonalGroup Q :=
        isometry_of_mem_Om8 ((e : ↥E) : ↥CFSG.AGLEmbedding.Om8).2
      constructor
      · change Q (e • a) = 1
        rw [hsmul, map_of_mem hLeO, ha.1]
      · change polar Q (e • a) r = 0
        have hp := polar_map_of_mem (Q := Q) hLeO a r
        have hLr : L ((e : ↥E) : ↥CFSG.AGLEmbedding.Om8) r = r :=
          hrfix ((e : ↥E) : ↥CFSG.AGLEmbedding.Om8) (e : ↥E).2
        rw [hLr] at hp
        rw [hsmul, hp, ha.2]
    letI : MulAction ↥E ↥Y :=
      { smul := fun e a => ⟨e • (a : V8), hYinv e (a : V8) a.2⟩
        one_smul := fun a => Subtype.ext (one_smul _ _)
        mul_smul := fun e f a => Subtype.ext (mul_smul _ _ _) }
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hE3 : IsPGroup 3 ↥E := IsPGroup.of_card (p := 3) (n := 3) hEcard
    have hYnotdvd : ¬ 3 ∣ Nat.card ↥Y := by
      have hcard : Nat.card ↥Y = 56 := by
        rw [Nat.card_coe_set_eq]
        exact hYcard
      rw [hcard]
      norm_num
    obtain ⟨a, ha⟩ := hE3.nonempty_fixed_point_of_prime_not_dvd_card ↥Y hYnotdvd
    have haQ : Q (a : V8) = 1 := a.2.1
    have hap : polar Q (a : V8) r = 0 := a.2.2
    have hfixE : ∀ e ∈ E, L e (a : V8) = (a : V8) := by
      intro e he
      have h := congrArg Subtype.val (MulAction.mem_fixedPoints.mp ha ⟨e, he⟩)
      change (⟨e, he⟩ : ↥E) • (a : V8) = (a : V8) at h
      simpa [hsmul, L] using h
    let z : ↥CFSG.AGLEmbedding.Om8 :=
      ⟨eichGL r (a : V8), eichGL_mem r (a : V8)⟩
    have hz2 : z ^ 2 = 1 := by
      apply Subtype.ext
      change eichGL r (a : V8) ^ 2 = 1
      apply (toLinEquiv ι8 (ZMod 2)).injective
      rw [map_pow, map_one]
      have hL : toLinEquiv ι8 (ZMod 2) (eichGL r (a : V8)) = eichler Q r (a : V8) := by
        simp [eichGL]
      rw [hL]
      have hpr : polar Q r (a : V8) = 0 := by rwa [polar_comm]
      rw [pow_two, eichler_mul hpr hpr, ZModModule.add_self, eichler_zero_right]
    have hz1 : z ≠ 1 := by
      intro h
      have hE : eichGL r (a : V8) = 1 := by
        exact Subtype.ext_iff.mp h
      have hne : eichler Q r (a : V8) ≠ 1 := by
        refine eichler_ne_one_of_not_mem_span hrQ hr0 (by rwa [polar_comm]) ?_
        intro hspan
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
        have hQa0 : Q (a : V8) = 0 := by
          rw [← hc, map_smul_eq_sq, hrQ, mul_zero]
        rw [hQa0] at haQ
        exact zero_ne_one haQ
      apply hne
      have hL : toLinEquiv ι8 (ZMod 2) (eichGL r (a : V8)) = eichler Q r (a : V8) := by
        simp [eichGL]
      rw [← hL, hE, map_one]
    have hzcomm : ∀ e ∈ E, z * e = e * z := by
      intro e he
      apply Subtype.ext
      change eichGL r (a : V8) * (e : GL ι8 (ZMod 2)) =
        (e : GL ι8 (ZMod 2)) * eichGL r (a : V8)
      apply (toLinEquiv ι8 (ZMod 2)).injective
      rw [map_mul, map_mul]
      have hL : toLinEquiv ι8 (ZMod 2) (eichGL r (a : V8)) = eichler Q r (a : V8) := by
        simp [eichGL]
      have heL : toLinEquiv ι8 (ZMod 2) (e : GL ι8 (ZMod 2)) = L e := rfl
      rw [hL, heL]
      have hLeO : L e ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
        simpa [L] using isometry_of_mem_Om8 (g := (e : GL ι8 (ZMod 2))) e.2
      have hLr : L e r = r := hrfix e he
      have hLa : L e (a : V8) = (a : V8) := hfixE e he
      have hconj := eichler_conj (Q := Q) hLeO r (a : V8)
      rw [hLr, hLa] at hconj
      have hEL : eichler Q r (a : V8) * L e = L e * eichler Q r (a : V8) := by
        calc eichler Q r (a : V8) * L e =
            (L e * eichler Q r (a : V8) * (L e)⁻¹) * L e := by rw [hconj]
          _ = L e * eichler Q r (a : V8) := by group
      exact hEL
    exact ⟨z, hz2, hz1, hzcomm⟩
  · have hB : ∀ r ∈ R₀, r ≠ 0 → ∃ e ∈ E, L e r ≠ r := by
      intro r hrR hr0
      by_contra h
      push Not at h
      exact hA ⟨r, hrR, hr0, fun e he => by simpa [L] using h e he⟩
    let G : Subgroup (V8 ≃ₗ[ZMod 2] V8) := E.map L
    have hMinv : ∀ g ∈ G, ∀ x ∈ R₀, g x ∈ R₀ := by
      intro g hg x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hg
      simpa [L] using hRinv e he x hx
    have hcommG : ∀ g ∈ G, ∀ h ∈ G, g * h = h * g := by
      intro g hg h hh
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hg
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hh
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hEab.1.is_comm.comm ⟨e, he⟩ ⟨f, hf⟩)
    have hexpG : ∀ g ∈ G, g ^ 3 = 1 := by
      intro g hg
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hg
      rw [← map_pow, hEab.2 e he, map_one]
    have hfixG : ∀ x ∈ R₀, (∀ g ∈ G, g x = x) → x = 0 := by
      intro x hx hfixx
      by_contra hx0
      obtain ⟨e, he, hex⟩ := hB x hx hx0
      exact hex (hfixx (L e) (Subgroup.mem_map_of_mem L he))
    obtain ⟨x, e, hxR, hx0, heG, hexne, heex, hplane⟩ :=
      plane_lemma G R₀ hRne hMinv hcommG hexpG hfixG
    have hxQ : Q x = 0 := hRsing x hxR
    let y : V8 := e x
    have hyR : y ∈ R₀ := by
      have := hMinv e heG x hxR
      simpa [y] using this
    have hyQ : Q y = 0 := hRsing y hyR
    have hxyQ : Q (x + y) = 0 := hRsing (x + y) (R₀.add_mem hxR hyR)
    have hxy : polar Q x y = 0 := by
      have h := hxyQ
      rw [QuadraticMap.map_add Q x y, hxQ, hyQ] at h
      simpa using h
    have hyx : y ≠ x := by simpa [y] using hexne
    have hy0 : y ≠ 0 := by
      intro hy
      apply hx0
      have h := congrArg e.symm hy
      simpa [y] using h
    have hy_span : y ∉ Submodule.span (ZMod 2) {x} := by
      intro hy
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
      have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases h01 c with rfl | rfl
      · rw [zero_smul] at hc
        exact hy0 hc.symm
      · rw [one_smul] at hc
        exact hyx hc.symm
    let z : ↥CFSG.AGLEmbedding.Om8 := ⟨eichGL x y, eichGL_mem x y⟩
    have hz2 : z ^ 2 = 1 := by
      apply Subtype.ext
      change eichGL x y ^ 2 = 1
      apply (toLinEquiv ι8 (ZMod 2)).injective
      rw [map_pow, map_one]
      have hL : toLinEquiv ι8 (ZMod 2) (eichGL x y) = eichler Q x y := by
        simp [eichGL]
      rw [hL, pow_two, eichler_mul hxy hxy, ZModModule.add_self, eichler_zero_right]
    have hz1 : z ≠ 1 := by
      intro h
      have hE : eichGL x y = 1 := Subtype.ext_iff.mp h
      have hne : eichler Q x y ≠ 1 := eichler_ne_one_of_not_mem_span hxQ hx0 hxy hy_span
      apply hne
      have hL : toLinEquiv ι8 (ZMod 2) (eichGL x y) = eichler Q x y := by
        simp [eichGL]
      rw [← hL, hE, map_one]
    have hE1 : eichler Q y (x + y) = eichler Q x y := by
      have h := eichler_add_smul_self (Q := Q) (u := y) (w := x) (c := 1) hyQ
      rw [one_smul] at h
      rw [h]
      exact eichler_comm (x := y) (y := x) hyQ hxQ (by rwa [polar_comm])
    have hpxyx : polar Q (x + y) x = 0 := by
      rw [polar_add_left, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hxQ]
      rw [polar_comm, hxy]
      simp
    have hE2 : eichler Q (x + y) x = eichler Q x y := by
      rw [eichler_comm hxyQ hxQ hpxyx]
      have h := eichler_add_smul_self (Q := Q) (u := x) (w := y) (c := 1) hxQ
      rw [one_smul] at h
      rw [show x + y = y + x from add_comm x y]
      exact h
    have hzcomm : ∀ e' ∈ E, z * e' = e' * z := by
      intro e' he'
      apply Subtype.ext
      change eichGL x y * (e' : GL ι8 (ZMod 2)) =
        (e' : GL ι8 (ZMod 2)) * eichGL x y
      apply (toLinEquiv ι8 (ZMod 2)).injective
      rw [map_mul, map_mul]
      have hL : toLinEquiv ι8 (ZMod 2) (eichGL x y) = eichler Q x y := by
        simp [eichGL]
      have heL : toLinEquiv ι8 (ZMod 2) (e' : GL ι8 (ZMod 2)) = L e' := rfl
      rw [hL, heL]
      have hLeO : L e' ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
        simpa [L] using isometry_of_mem_Om8 (g := (e' : GL ι8 (ZMod 2))) e'.2
      have hLeG : L e' ∈ G := Subgroup.mem_map_of_mem L he'
      have hcomm_e : L e' * e = e * L e' := hcommG (L e') hLeG e heG
      have hLey : L e' y = e (L e' x) := by
        change (L e') (e x) = e ((L e') x)
        have h := congrArg (fun f : V8 ≃ₗ[ZMod 2] V8 => f x) hcomm_e
        simpa [LinearEquiv.mul_apply] using h
      have hconj := eichler_conj (Q := Q) hLeO x y
      rw [hLey] at hconj
      have hcase := hplane (L e') hLeG
      have htarget : eichler Q (L e' x) (e (L e' x)) = eichler Q x y := by
        rcases hcase with h | h | h
        · rw [h]
        · rw [h, heex]
          simpa [y] using hE1
        · rw [h]
          have hey : e (x + e x) = x := by
            rw [map_add, heex]
            rw [← add_assoc, add_comm (e x) x, add_assoc, ZModModule.add_self, add_zero]
          rw [hey]
          simpa [y] using hE2
      rw [htarget] at hconj
      have hEL : eichler Q x y * L e' = L e' * eichler Q x y := by
        calc eichler Q x y * L e' =
            (L e' * eichler Q x y * (L e')⁻¹) * L e' := by rw [hconj]
          _ = L e' * eichler Q x y := by group
      exact hEL
    exact ⟨z, hz2, hz1, hzcomm⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end

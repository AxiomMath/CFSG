
module

public import CFSG.GF2Type.Smith1979.GammaU.StepATD
public import CFSG.GF2Type.Smith1979.GammaU.StepAOrbitFacts
public import CFSG.GF2Type.Smith1979.GammaU.StepAFacts

@[expose] public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU Module

instance : Finite (V12 ≃ₗ[ZMod 2] V12) :=
  Finite.of_injective (fun e : V12 ≃ₗ[ZMod 2] V12 => (e : V12 → V12)) fun _ _ h =>
    LinearEquiv.ext (congrFun h)

theorem inv_apply_apply (h : V12 ≃ₗ[ZMod 2] V12) (y : V12) : h⁻¹ (h y) = y :=
  h.symm_apply_apply y

theorem f0_gammaU {h : V12 ≃ₗ[ZMod 2] V12} (hh : h ∈ gammaU) (x y : V12) :
    f0 (h x) (h y) = f0 x y :=
  f0_isometry hh.1 x y

theorem mem_map_conj {h l' : V12 ≃ₗ[ZMod 2] V12} {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)} :
    l' ∈ L.map (MulAut.conj h).toMonoidHom ↔ ∃ l ∈ L, h * l * h⁻¹ = l' := by
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem conj_apply_apply (h l : V12 ≃ₗ[ZMod 2] V12) (y : V12) : (h * l * h⁻¹) (h y) = h (l y) := by
  simp only [LinearEquiv.mul_apply]
  rw [inv_apply_apply]

theorem Hyp.conj {a : V12} {D : Submodule (ZMod 2) V12} {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (H : Hyp a D L) {h : V12 ≃ₗ[ZMod 2] V12} (hh : h ∈ gammaU) :
    Hyp (h a) (D.map (h : V12 →ₗ[ZMod 2] V12)) (L.map (MulAut.conj h).toMonoidHom) where
  ne_zero := fun h0 => H.ne_zero (h.injective (h0.trans (map_zero h).symm))
  q_eq := by rw [hh.1, H.q_eq]
  sing := by
    rintro _ ⟨y, hy, rfl⟩
    change q0 (h y) = 0
    rw [hh.1, H.sing y hy]
  finrank_eq := by rw [LinearEquiv.finrank_map_eq, H.finrank_eq]
  mem := ⟨a, H.mem, rfl⟩
  le := by
    rintro _ hl'
    obtain ⟨l, hl, rfl⟩ := mem_map_conj.1 hl'
    exact mul_mem (mul_mem hh (H.le hl)) (inv_mem hh)
  card := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, H.card]
  fix := by
    intro _ hl'
    obtain ⟨l, hl, rfl⟩ := mem_map_conj.1 hl'
    rw [conj_apply_apply, H.fix l hl]
  perp := by
    intro _ hl' x hx
    obtain ⟨l, hl, rfl⟩ := mem_map_conj.1 hl'
    obtain ⟨y, rfl⟩ := h.surjective x
    have hy : f0 y a = 0 := by rw [← f0_gammaU hh]; exact hx
    rw [conj_apply_apply, ← map_sub]
    exact ⟨_, H.perp l hl y hy, rfl⟩
  comm := by
    rintro _ hl' _ ⟨d, hd, rfl⟩
    obtain ⟨l, hl, rfl⟩ := mem_map_conj.1 hl'
    change (h * l * h⁻¹) (h d) - h d = 0 ∨ (h * l * h⁻¹) (h d) - h d = h a
    rw [conj_apply_apply, ← map_sub]
    rcases H.comm l hl d hd with h0 | h0
    · left; rw [h0, map_zero]
    · right; rw [h0]
  faithful := by
    intro _ hl' hfix
    obtain ⟨l, hl, rfl⟩ := mem_map_conj.1 hl'
    have hl1 : l = 1 := H.faithful l hl fun d hd => h.injective (by
      rw [← conj_apply_apply]
      exact hfix _ ⟨d, hd, rfl⟩)
    rw [hl1, mul_one, mul_inv_cancel]

theorem dReps_lt : ∀ rep ∈ dReps, ∀ d ∈ rep, d < 4096 := by decide

theorem eqOn_spanOf {f g : V12 →ₗ[ZMod 2] V12} {s : List ℕ}
    (h : ∀ d ∈ s, f (vecOf d) = g (vecOf d)) : ∀ y ∈ spanOf s, f y = g y := by
  intro y hy
  refine LinearMap.eqOn_span' (s := {x | ∃ v ∈ s, vecOf v = x}) ?_ hy
  rintro _ ⟨d, hd, rfl⟩
  exact h d hd

theorem false_of_bad (h16964 : StepATFacts) {rep : List ℕ} (hrep : rep ∈ dReps)
    (hne : rep ≠ d0) {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (H : Hyp (vecOf a0) (spanOf rep) L) :
    False :=
  h16964.t1 rep hrep hne L H

theorem getElem!_map_appN (g h : Array ℕ) (j : ℕ) : (h.map (appN g))[j]! = appN g h[j]! := by
  by_cases hj : j < h.size
  · rw [getElem!_pos (h.map (appN g)) j (by simpa using hj), getElem!_pos h j hj,
      Array.getElem_map]
  · rw [getElem!_neg (h.map (appN g)) j (by simpa using hj), getElem!_neg h j hj]
    simp [appN]

theorem linOfRows_mulR (g h : Array ℕ) (x : V12) :
    linOfRows (mulR g h) x = linOfRows g (linOfRows h x) := by
  have hf : linOfRows (mulR g h) = (linOfRows g).comp (linOfRows h) :=
    linMap_ext fun j => by
      rw [LinearMap.comp_apply, linOfRows_unit, linOfRows_unit, mulR, getElem!_map_appN,
        vecOf_appN]
  exact LinearMap.congr_fun hf x

theorem linOfRows_idR (x : V12) : linOfRows idR x = x := by
  have hf : linOfRows idR = LinearMap.id :=
    linMap_ext fun j => by
      rw [linOfRows_unit, LinearMap.id_apply]
      congr 1
      fin_cases j <;> rfl
  exact LinearMap.congr_fun hf x

theorem rows_eq {r r' : Array ℕ} (hr : r.size = 12) (hr' : r'.size = 12)
    (hlt : ∀ x ∈ r, x < 4096) (hlt' : ∀ x ∈ r', x < 4096)
    (h : ∀ x, linOfRows r x = linOfRows r' x) : r = r' := by
  refine Array.ext (hr.trans hr'.symm) fun j hj hj' => ?_
  have hv := h (vecOf (2 ^ j))
  rw [show j = ((⟨j, hr ▸ hj⟩ : Fin 12) : ℕ) from rfl, linOfRows_unit, linOfRows_unit,
    getElem!_pos r j hj, getElem!_pos r' j hj'] at hv
  exact vecOf_inj (hlt _ (Array.getElem_mem hj)) (hlt' _ (Array.getElem_mem hj')) hv

theorem bits_five : ∀ f : Fin 5 → Bool, ∃ c < 32, ∀ i : Fin 5, c.testBit i = f i := by decide

theorem subsetProducts_mem {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {gens : List (Array ℕ)}
    (hg : ∀ g ∈ gens, ∃ l ∈ L, ∀ x, l x = linOfRows g x) :
    ∀ r ∈ subsetProducts gens, ∃ l ∈ L, ∀ x, l x = linOfRows r x := by
  unfold subsetProducts
  suffices h : ∀ acc : List (Array ℕ), (∀ r ∈ acc, ∃ l ∈ L, ∀ x, l x = linOfRows r x) →
      ∀ r ∈ gens.foldl (fun acc g => acc ++ acc.map (mulR g)) acc,
        ∃ l ∈ L, ∀ x, l x = linOfRows r x by
    refine h [idR] fun r hr => ?_
    rw [List.mem_singleton] at hr
    exact ⟨1, one_mem _, fun x => by rw [hr, linOfRows_idR]; rfl⟩
  induction gens with
  | nil => exact fun acc hacc => hacc
  | cons g gens ih =>
    intro acc hacc
    rw [List.foldl_cons]
    refine ih (fun g' hg' => hg g' (List.mem_cons_of_mem g hg')) _ fun r hr => ?_
    rcases List.mem_append.1 hr with hr | hr
    · exact hacc r hr
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      obtain ⟨l, hl, hlx⟩ := hacc r' hr'
      obtain ⟨m, hm, hmx⟩ := hg g List.mem_cons_self
      exact ⟨m * l, mul_mem hm hl, fun x => by
        rw [LinearEquiv.mul_apply, hlx, hmx, linOfRows_mulR]⟩

theorem d0_lt : ∀ d ∈ d0, d < 4096 := by decide

theorem comp_of_d0 (h16964 : StepATFacts) {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (H : Hyp (vecOf a0) (spanOf d0) L) :
    ∃ c < 32, ∀ l : V12 ≃ₗ[ZMod 2] V12, l ∈ L ↔ ∃ r ∈ compOf c, ∀ x, l x = linOfRows r x :=
  h16964.t2 L H

theorem saMonoid_spec (h16963 : StepAOrbitFacts) {h : V12 ≃ₗ[ZMod 2] V12}
    (hh : h ∈ Submonoid.closure saSet) : h ∈ gammaU ∧ h (vecOf a0) = vecOf a0 := by
  induction hh using Submonoid.closure_induction with
  | mem x hx => exact h16963.saSet_spec x hx
  | one => exact ⟨one_mem _, rfl⟩
  | mul x y _ _ hx hy => exact ⟨mul_mem hx.1 hy.1, by rw [LinearEquiv.mul_apply, hy.2, hx.2]⟩

theorem map_inv_map (h : V12 ≃ₗ[ZMod 2] V12) (S : Submodule (ZMod 2) V12) :
    (S.map (h : V12 →ₗ[ZMod 2] V12)).map ((h⁻¹ : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) = S := by
  rw [← Submodule.map_comp]
  have e : ((h⁻¹ : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12).comp (h : V12 →ₗ[ZMod 2] V12) =
      LinearMap.id := LinearMap.ext fun x => inv_apply_apply h x
  rw [e, Submodule.map_id]

theorem exists_rep (h16963 : StepAOrbitFacts) {D : Submodule (ZMod 2) V12}
    {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (H : Hyp (vecOf a0) D L) :
    ∃ rep ∈ dReps, ∃ h ∈ gammaU, h (vecOf a0) = vecOf a0 ∧
      D.map (h : V12 →ₗ[ZMod 2] V12) = spanOf rep := by
  obtain ⟨rep, hrep, h, hh, hD⟩ := h16963.exists_rep D H.sing H.finrank_eq H.mem
  obtain ⟨hhg, hha⟩ := saMonoid_spec h16963 hh
  refine ⟨rep, hrep, h⁻¹, inv_mem hhg, ?_, ?_⟩
  · conv_lhs => rw [← hha]
    exact inv_apply_apply h _
  · rw [hD, map_inv_map]

end CFSG.GF2Type.Smith1979.GammaU.StepA

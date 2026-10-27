module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Coord

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

open CFSG CFSG.LocalCores Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_normalizer_of_conj_mem {S : Subgroup Y} {g : Y} (h : ∀ s ∈ S, g * s * g⁻¹ ∈ S) :
    g ∈ normalizer (S : Set Y) := by
  have hsurj : Function.Surjective (fun s : S => (⟨g * s * g⁻¹, h s s.2⟩ : S)) := by
    apply Finite.surjective_of_injective
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using this)
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  obtain ⟨s, hs⟩ := hsurj ⟨g * y * g⁻¹, hy⟩
  have h1 : g * (s : Y) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hs
  have hsy : (s : Y) = y := by simpa using h1
  exact hsy ▸ s.2

theorem cjComp_eq_iff (g : Y) (C : ComponentIndex Y) :
    cjComp g C = C ↔ g ∈ normalizer (C.1 : Set Y) := by
  constructor
  · intro h
    rw [mem_normalizer_iff]
    intro c
    have h1 : (g * c * g⁻¹) ∈ (cjComp g C).1 ↔ g⁻¹ * (g * c * g⁻¹) * g ∈ C.1 :=
      mem_cjComp_iff g C
    rw [h, show g⁻¹ * (g * c * g⁻¹) * g = c by group] at h1
    exact h1.symm
  · intro hg
    apply Subtype.ext
    ext c
    rw [mem_cjComp_iff]
    have := mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) c
    simpa using this.symm

theorem cjComp_ne_self {x : Y}
    (htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C')
    (hcard : 1 < Nat.card (ComponentIndex Y)) (C : ComponentIndex Y) : cjComp x C ≠ C := by
  intro h
  have hpow : ∀ k : ℕ, cjComp (x ^ k) C = C := by
    intro k
    induction k with
    | zero => simpa using cjComp_one C
    | succ k ih => rw [pow_succ, cjComp_mul, h, ih]
  have hsub : Subsingleton (ComponentIndex Y) := ⟨fun C₁ C₂ => by
    obtain ⟨k₁, hk₁⟩ := htrans C C₁
    obtain ⟨k₂, hk₂⟩ := htrans C C₂
    rw [← hk₁, ← hk₂, hpow, hpow]⟩
  have := Nat.card_of_subsingleton C
  omega

theorem exists_cjComp_pow_eq {x a : Y} (hxa : a * x = x * a)
    (htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C') (C₀ : ComponentIndex Y) :
    ∃ k : ℕ, ∀ C : ComponentIndex Y, cjComp a C = cjComp (x ^ k) C := by
  obtain ⟨k, hk⟩ := htrans C₀ (cjComp a C₀)
  refine ⟨k, fun C => ?_⟩
  obtain ⟨m, hm⟩ := htrans C₀ C
  have hcomm : ∀ n : ℕ, a * x ^ n = x ^ n * a := fun n =>
    (Commute.pow_right (show Commute a x from hxa) n).eq
  rw [← hm]
  calc cjComp a (cjComp (x ^ m) C₀) = cjComp (a * x ^ m) C₀ := (cjComp_mul _ _ _).symm
    _ = cjComp (x ^ m * a) C₀ := by rw [hcomm]
    _ = cjComp (x ^ m) (cjComp a C₀) := cjComp_mul _ _ _
    _ = cjComp (x ^ m) (cjComp (x ^ k) C₀) := by rw [hk]
    _ = cjComp (x ^ (m + k)) C₀ := by rw [← cjComp_mul, ← pow_add]
    _ = cjComp (x ^ (k + m)) C₀ := by rw [add_comm]
    _ = cjComp (x ^ k) (cjComp (x ^ m) C₀) := by rw [pow_add, cjComp_mul]

theorem commutator_mem_normalizer {x a b : Y} (hxa : a * x = x * a) (hxb : b * x = x * b)
    (htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C') (C₀ : ComponentIndex Y) :
    a * b * a⁻¹ * b⁻¹ ∈ normalizer (C₀.1 : Set Y) := by
  obtain ⟨k, hk⟩ := exists_cjComp_pow_eq hxa htrans C₀
  obtain ⟨l, hl⟩ := exists_cjComp_pow_eq hxb htrans C₀
  have hab : ∀ C : ComponentIndex Y, cjComp (a * b) C = cjComp (b * a) C := fun C => by
    rw [cjComp_mul, cjComp_mul, hl, hk, hk, hl, ← cjComp_mul, ← cjComp_mul, ← pow_add,
      ← pow_add, add_comm]
  rw [← cjComp_eq_iff, show a * b * a⁻¹ * b⁻¹ = (a * b) * (b * a)⁻¹ by group, cjComp_mul,
    hab, ← cjComp_mul, mul_inv_cancel, cjComp_one]

theorem mem_normalizer_of_mem_layer (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥)
    (C : ComponentIndex Y) {l : Y} (hl : l ∈ layer Y) : l ∈ normalizer (C.1 : Set Y) := by
  refine mem_normalizer_of_conj_mem fun c hc => ?_
  rw [conj_eq_π (hZ := hZ) C hl hc]
  exact C.1.mul_mem (C.1.mul_mem (π_mem C l hl) hc) (C.1.inv_mem (π_mem C l hl))

theorem mem_centralizer_of_centralizes_component {x c : Y} (hcx : c * x = x * c)
    (htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C') {C₀ : ComponentIndex Y}
    (hc : c ∈ centralizer (C₀.1 : Set Y)) (C : ComponentIndex Y) :
    c ∈ centralizer (C.1 : Set Y) := by
  obtain ⟨k, hk⟩ := htrans C₀ C
  rw [mem_centralizer_iff]
  intro d hd
  have hd' : (x ^ k)⁻¹ * d * x ^ k ∈ C₀.1 := by
    rw [← hk] at hd
    exact (mem_cjComp_iff _ _).mp hd
  have h1 : Commute c (x ^ k) := Commute.pow_right (show Commute c x from hcx) k
  have h2 : Commute c ((x ^ k)⁻¹ * d * x ^ k) := (mem_centralizer_iff.mp hc _ hd').symm
  have h3 : Commute c (x ^ k * ((x ^ k)⁻¹ * d * x ^ k) * (x ^ k)⁻¹) :=
    (h1.mul_right h2).mul_right h1.inv_right
  have e : d = x ^ k * ((x ^ k)⁻¹ * d * x ^ k) * (x ^ k)⁻¹ := by group
  rw [e]
  exact h3.eq.symm

theorem eq_one_of_mem_layer_of_centralizes (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) {c : Y}
    (hc : c ∈ layer Y) (h : ∀ C : ComponentIndex Y, c ∈ centralizer (C.1 : Set Y)) : c = 1 :=
  eq_one_of_π_eq_one (hZ := hZ) hc fun C => (π_eq_one_iff C hc).2 (h C)

theorem isSimpleGroup_of_component {K : Subgroup Y} (hK : IsComponent K)
    (hc : Subgroup.center ↥K = ⊥) : IsSimpleGroup ↥K := by
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.1.2.1
  let e : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot (G := ↥K))
  haveI : Nontrivial ↥K := e.symm.surjective.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective

theorem exists_noncomm_of_component {K : Subgroup Y} (hK : IsComponent K)
    (hc : Subgroup.center ↥K = ⊥) : ∃ a b : ↥K, a * b ≠ b * a := by
  let e : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot (G := ↥K))
  obtain ⟨a, b, hab⟩ := hK.1.2.2
  refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

noncomputable def conjIso (g : Y) (C₀ C : ComponentIndex Y) (h : cjComp g C₀ = C) :
    ↥C₀.1 ≃* ↥C.1 :=
  (C₀.1.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr (congrArg Subtype.val h))

noncomputable def layerPiEquiv (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) {x : Y}
    (htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C') {n : ℕ}
    (hcard : Nat.card (ComponentIndex Y) = n) (C₀ : ComponentIndex Y) :
    ↥(layer Y) ≃* (Fin n → ↥C₀.1) :=
  (layerEquiv hZ).symm.trans <|
    (MulEquiv.piCongrRight fun C : ComponentIndex Y =>
        (conjIso (x ^ Classical.choose (htrans C₀ C)) C₀ C
          (Classical.choose_spec (htrans C₀ C))).symm).trans
      { Equiv.arrowCongr (Finite.equivFinOfCardEq hcard) (Equiv.refl ↥C₀.1) with
        map_mul' := fun _ _ => rfl }

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

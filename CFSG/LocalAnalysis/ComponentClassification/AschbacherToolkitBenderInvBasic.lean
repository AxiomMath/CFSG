module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def InvDichotomyAt (S : Subgroup G) : Prop :=
  ∀ α : MulAut G, α * α = 1 → (∀ s ∈ S, α s ∈ S) →
    (∃ y : G, α = MulAut.conj y) ∨
      ∃ x : G, x ∉ Subgroup.normalizer (S : Set G) ∧ ∀ s ∈ S, x⁻¹ * α (x * s * x⁻¹) * x ∈ S

open AutTransport in
theorem InvDichotomyAt.map_mulEquiv {G' : Type*} [Group G'] {S : Subgroup G}
    (h : InvDichotomyAt S) (e : G ≃* G') : InvDichotomyAt (S.map e.toMonoidHom) := by
  intro α' hα' hn
  set α := (MulAut.congr e).symm α' with hαdef
  have hα'eq : α' = MulAut.congr e α := by rw [hαdef, MulEquiv.apply_symm_apply]
  have happ : ∀ g, α g = e.symm (α' (e g)) := fun g => congr_symm_apply' e α' g
  have hαα : α * α = 1 := by
    rw [hαdef, ← map_mul, hα', map_one]
  have hn' : ∀ s ∈ S, α s ∈ S := by
    intro s hs
    rw [happ, ← mem_map_iff' e]
    exact hn _ ((mem_map_iff e).mpr hs)
  rcases h α hαα hn' with ⟨y, hy⟩ | ⟨x, hx, hxn⟩
  · left
    refine ⟨e y, ?_⟩
    rw [hα'eq, hy, congr_conj]
  · right
    refine ⟨e x, fun hex => hx ?_, fun s' hs' => ?_⟩
    · have h1 := mem_normalizer_map e.symm hex
      rw [MulEquiv.symm_apply_apply, Subgroup.map_map] at h1
      convert h1
      ext g
      simp
    · have hs : e.symm s' ∈ S := (mem_map_iff' e).mp hs'
      have h1 := hxn _ hs
      rw [mem_map_iff' e]
      have h2 : e.symm ((e x)⁻¹ * α' (e x * s' * (e x)⁻¹) * e x) =
          x⁻¹ * α (x * e.symm s' * x⁻¹) * x := by
        rw [happ]
        simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
      rw [h2]
      exact h1

theorem invDichotomyAt_of_one_sylow [Finite G] (R : Sylow 2 G)
    (h : InvDichotomyAt (R : Subgroup G)) (T : Sylow 2 G) : InvDichotomyAt (T : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R T
  have hT : (T : Subgroup G) = (R : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [hT]
  exact h.map_mulEquiv (MulAut.conj g)

theorem invDichotomyAt_of_mulEquiv [Finite G] {G' : Type*} [Group G'] (e : G ≃* G')
    (hG' : ∀ T : Sylow 2 G', InvDichotomyAt (T : Subgroup G')) (T : Sylow 2 G) :
    InvDichotomyAt (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (hG' (T.mapSurjective (f := e.toMonoidHom) e.surjective)).map_mulEquiv e.symm
  have h' : InvDichotomyAt (((T : Subgroup G).map e.toMonoidHom).map e.symm.toMonoidHom) := h
  rw [Subgroup.map_map] at h'
  convert h'
  ext x
  simp

theorem card_sylow_eq_of_mulEquiv [Finite G] {G' : Type*} [Group G'] (e : G ≃* G') (p : ℕ)
    [Fact p.Prime] : Nat.card (Sylow p G) = Nat.card (Sylow p G') := by
  have : Finite G' := Finite.of_equiv G e.toEquiv
  refine Nat.card_congr
    { toFun := fun P => P.mapSurjective (f := e.toMonoidHom) e.surjective
      invFun := fun P => P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
      left_inv := fun P => ?_
      right_inv := fun P => ?_ }
  · apply Sylow.ext
    change ((P : Subgroup G).map e.toMonoidHom).map e.symm.toMonoidHom = P
    rw [Subgroup.map_map]
    ext x
    simp
  · apply Sylow.ext
    change ((P : Subgroup G').map e.symm.toMonoidHom).map e.toMonoidHom = P
    rw [Subgroup.map_map]
    ext x
    simp

namespace InvInner

variable [Finite G]

theorem exists_smul_eq_self_of_sq_eq_one (α : MulAut G) (hα : α * α = 1)
    (hodd : Odd (Nat.card (Sylow 2 G))) : ∃ S : Sylow 2 G, α • S = S := by
  classical
  let : Fintype (Sylow 2 G) := Fintype.ofFinite _
  let σ : Equiv.Perm (Sylow 2 G) := MulAction.toPerm α
  have hσ : σ ^ 2 = 1 := by
    rw [sq]
    refine Equiv.ext fun S => ?_
    change α • (α • S) = S
    rw [smul_smul, hα, one_smul]
  by_contra hcon
  push Not at hcon
  have hsupp : σ.support = Finset.univ := by
    ext S
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    exact hcon S
  have h2 := Equiv.Perm.two_dvd_card_support hσ
  rw [hsupp, Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem exists_fixed_of_sq_eq_one (α : MulAut G) (hα : α * α = 1) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hαS : ∀ s ∈ S, α s ∈ S) :
    ∃ s ∈ S, s ≠ 1 ∧ α s = s := by
  let φ : S →* S :=
    { toFun := fun s => ⟨α (s : G), hαS (s : G) s.2⟩
      map_one' := Subtype.ext (map_one α)
      map_mul' := fun a b => Subtype.ext (map_mul α (a : G) (b : G)) }
  have hinv : Function.Involutive φ := by
    intro s
    apply Subtype.ext
    change α (α (s : G)) = (s : G)
    rw [← MulAut.mul_apply, hα, MulAut.one_apply]
  by_contra hcon
  push Not at hcon
  have hfree : MonoidHom.FixedPointFree φ := by
    intro s hs
    by_contra hs1
    exact hcon s s.2 (fun h => hs1 (Subtype.ext h)) (congrArg Subtype.val hs)
  have hodd := hfree.odd_card_of_involutive hinv
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hS1 (Subgroup.card_eq_one.mp hn)
  rw [hn] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hn0⟩)

omit [Finite G] in
theorem mem_of_mem_normalizer {T : Sylow 2 G} {s : G}
    (hs : s ∈ Subgroup.normalizer ((T : Subgroup G) : Set G)) {S : Sylow 2 G}
    (hsS : s ∈ (S : Subgroup G)) : s ∈ (T : Subgroup G) := by
  have hp : IsPGroup 2 (Subgroup.zpowers s) :=
    S.isPGroup'.to_le ((Subgroup.zpowers_le).mpr hsS)
  have h := hp.inf_normalizer_sylow T
  have hmem : s ∈ Subgroup.zpowers s ⊓ Subgroup.normalizer (T : Set G) :=
    ⟨Subgroup.mem_zpowers s, hs⟩
  rw [h] at hmem
  exact hmem.2

omit [Finite G] in
theorem apply_mem_of_smul_eq {α : MulAut G} {S : Sylow 2 G} (hS : α • S = S) {s : G}
    (hs : s ∈ (S : Subgroup G)) : α s ∈ (S : Subgroup G) := by
  have h : α s ∈ ((α • S : Sylow 2 G) : Subgroup G) := by
    rw [Omega.mem_smul_iff, MulAut.inv_apply_self]
    exact hs
  rwa [hS] at h

theorem eq_of_smul_eq_self (hSE : ∀ S : Sylow 2 G,
      fusionStronglyEmbedded (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (α : MulAut G) (hα : α * α = 1) {T : Sylow 2 G}
    (hT : ∀ x : G, α x = x → x ∈ Subgroup.normalizer ((T : Subgroup G) : Set G))
    {S : Sylow 2 G} (hS : α • S = S) (hS1 : (S : Subgroup G) ≠ ⊥) : S = T := by
  obtain ⟨s, hsS, hs1, hαs⟩ :=
    exists_fixed_of_sq_eq_one α hα S.isPGroup' hS1 fun s hs => apply_mem_of_smul_eq hS hs
  have hsT : s ∈ (T : Subgroup G) := mem_of_mem_normalizer (hT s hαs) hsS
  by_contra hne
  exact hs1 (Omega.eq_one_of_mem_of_mem (hSE S) (Ne.symm hne) hsS hsT)

end InvInner

open InvInner in
theorem exists_eq_conj_of_dichotomy [Finite G] (hSE : ∀ S : Sylow 2 G,
      fusionStronglyEmbedded (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (hodd : Odd (Nat.card (Sylow 2 G))) (hnt : ∀ S : Sylow 2 G, (S : Subgroup G) ≠ ⊥)
    (hdich : ∀ S : Sylow 2 G, InvDichotomyAt (S : Subgroup G)) (α : MulAut G)
    (hα : α * α = 1) (T : Sylow 2 G)
    (hT : ∀ x : G, α x = x → x ∈ Subgroup.normalizer ((T : Subgroup G) : Set G)) :
    ∃ y : G, α = MulAut.conj y := by
  obtain ⟨S, hS⟩ := exists_smul_eq_self_of_sq_eq_one α hα hodd
  have hST := eq_of_smul_eq_self hSE α hα hT hS (hnt S)
  subst hST
  rcases hdich S α hα (fun s hs => apply_mem_of_smul_eq hS hs) with h | ⟨x, hx, hxn⟩
  · exact h
  · exfalso
    have hfix : α • (x • S) = x • S := by
      apply Omega.smul_eq_of_mapsTo
      intro g hg
      show α g ∈ ((x • S : Sylow 2 G) : Subgroup G)
      rw [Omega.mem_conj_smul_iff] at hg ⊢
      have h1 := hxn _ hg
      have h2 : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
      rw [h2] at h1
      exact h1
    have heq := eq_of_smul_eq_self hSE α hα hT hfix (hnt _)
    exact hx ((Sylow.smul_eq_iff_mem_normalizer).mp heq)

theorem invDichotomyAt_of_twisted [Finite G] [IsSimpleGroup G] {R R₀ : Sylow 2 G}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((R : Subgroup G) : Set G)))
    (hcard : Nat.card (Sylow 2 G) = Nat.card (R : Subgroup G) + 1) (hR₀ : R₀ ≠ R)
    (h : ∀ α' : MulAut G, (∀ g, α' (α' g) = g) → α' • R = R → α' • R₀ = R₀ →
      ∀ r ∈ (R : Subgroup G), α' r = r⁻¹ →
        (∀ s ∈ (R : Subgroup G), α' s = s) ∨ ∃ x ∈ (R : Subgroup G), r = x * (α' x)⁻¹) :
    InvDichotomyAt (R : Subgroup G) := by
  intro α hα hαR
  have hαR' : α • R = R := Omega.smul_eq_of_mapsTo hαR
  obtain ⟨r, hr, hrS⟩ := Omega.exists_conj_adjust hSE hcard hR₀ α hαR'
  set α' := (MulAut.conj r)⁻¹ * α with hα'def
  have hαeq : α = MulAut.conj r * α' := by rw [hα'def, mul_inv_cancel_left]
  have happ : ∀ g, α g = r * α' g * r⁻¹ := fun g => by
    rw [hαeq, MulAut.mul_apply, MulAut.conj_apply]
  have hα'R : α' • R = R := by
    rw [hα'def, mul_smul, hαR', inv_smul_eq_iff, Omega.conj_smul_self hr]
  have hαα : ∀ g, α (α g) = g := fun g => by
    rw [← MulAut.mul_apply, hα, MulAut.one_apply]
  have hα'sq : ∀ g, α' (α' g) = (r⁻¹ * (α r)⁻¹) * g * (r⁻¹ * (α r)⁻¹)⁻¹ := by
    intro g
    have e1 : ∀ y, α' y = r⁻¹ * α y * r := fun y => by
      rw [hα'def, MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
    rw [e1, e1, map_mul, map_mul, map_inv, hαα]
    group
  have hcR : r⁻¹ * (α r)⁻¹ ∈ (R : Subgroup G) :=
    (R : Subgroup G).mul_mem ((R : Subgroup G).inv_mem hr) ((R : Subgroup G).inv_mem (hαR r hr))
  have hc1 : r⁻¹ * (α r)⁻¹ = 1 := by
    apply Omega.eq_one_of_mem_normalizer hSE hR₀ hcR
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    rw [Sylow.smul_def]
    apply Omega.smul_eq_of_mapsTo
    intro s hs
    have h1 : α' (α' s) ∈ (R₀ : Subgroup G) :=
      InvInner.apply_mem_of_smul_eq hrS (InvInner.apply_mem_of_smul_eq hrS hs)
    rw [hα'sq] at h1
    rw [MulAut.conj_apply]
    exact h1
  have hα'α' : ∀ g, α' (α' g) = g := fun g => by
    rw [hα'sq, hc1, one_mul, inv_one, mul_one]
  have hα'r : α' r = r⁻¹ := by
    have hcen : ∀ g, (r * α' r) * g * (r * α' r)⁻¹ = g := by
      intro g
      have h1 := hαα g
      rw [happ, happ, map_mul, map_mul, map_inv, hα'α'] at h1
      calc (r * α' r) * g * (r * α' r)⁻¹ = r * (α' r * g * (α' r)⁻¹) * r⁻¹ := by group
        _ = g := h1
    have hdR : r * α' r ∈ (R : Subgroup G) :=
      (R : Subgroup G).mul_mem hr (InvInner.apply_mem_of_smul_eq hα'R hr)
    have hdN : r * α' r ∈ Subgroup.normalizer ((R₀ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      rw [hcen g]
    have hd1 := Omega.eq_one_of_mem_normalizer hSE hR₀ hdR hdN
    exact eq_inv_of_mul_eq_one_right hd1
  rcases h α' hα'α' hα'R hrS r hr hα'r with hc | ⟨x, hx, hrx⟩
  ·
    left
    have hone := Omega.eq_one_of_centralizes hSE hcard hR₀ α' hα'R hrS hc
    exact ⟨r, by rw [hαeq, hone, mul_one]⟩
  ·
    right
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R R₀
    have hαx : ∀ y, α y = x * α' (x⁻¹ * y * x) * x⁻¹ := by
      intro y
      rw [happ, hrx]
      simp only [map_mul, map_inv]
      group
    refine ⟨x * g, fun hxg => ?_, fun s hs => ?_⟩
    · apply hR₀
      have h1 : (x * g) • R = R := Sylow.smul_eq_iff_mem_normalizer.mpr hxg
      rw [mul_smul, hg] at h1
      have hxR : x • R = R := Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hx)
      calc R₀ = x⁻¹ • (x • R₀) := (inv_smul_smul x R₀).symm
        _ = x⁻¹ • R := by rw [h1]
        _ = x⁻¹ • (x • R) := by rw [hxR]
        _ = R := inv_smul_smul x R
    · rw [hαx]
      have e : (x * g)⁻¹ * (x * α' (x⁻¹ * (x * g * s * (x * g)⁻¹) * x) * x⁻¹) * (x * g) =
          g⁻¹ * α' (g * s * g⁻¹) * g := by
        have e' : x⁻¹ * (x * g * s * (x * g)⁻¹) * x = g * s * g⁻¹ := by group
        rw [e']
        group
      rw [e]
      have hgs : g * s * g⁻¹ ∈ (R₀ : Subgroup G) := by
        rw [← hg, Omega.mem_conj_smul_iff]
        have e' : g⁻¹ * (g * s * g⁻¹) * g = s := by group
        rw [e']
        exact hs
      have h2 := InvInner.apply_mem_of_smul_eq hrS hgs
      rw [← hg, Omega.mem_conj_smul_iff] at h2
      exact h2

end Bender

end CFSG.ComponentClassification.AschbacherToolkit

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYDAut

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem exists_restrict_aut {G : Type} [Group G] [Finite G] {W K : Subgroup G} (hKW : K ≤ W)
    (α : MulAut ↥W) (hα : ∀ x : ↥W, (x : G) ∈ K → ((α x : ↥W) : G) ∈ K) :
    ∃ αK : MulAut ↥K, ∀ k : ↥K, ((αK k : ↥K) : G) = ((α ⟨k, hKW k.2⟩ : ↥W) : G) := by
  let f : ↥K →* ↥K :=
    { toFun := fun k => ⟨((α ⟨k, hKW k.2⟩ : ↥W) : G), hα _ k.2⟩
      map_one' := by
        apply Subtype.ext
        show ((α ⟨(1 : ↥K), hKW (1 : ↥K).2⟩ : ↥W) : G) = 1
        have : (⟨((1 : ↥K) : G), hKW (1 : ↥K).2⟩ : ↥W) = 1 := rfl
        rw [this, map_one]; rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        show ((α ⟨((a * b : ↥K) : G), hKW (a * b).2⟩ : ↥W) : G) =
          ((α ⟨a, hKW a.2⟩ : ↥W) : G) * ((α ⟨b, hKW b.2⟩ : ↥W) : G)
        have : (⟨((a * b : ↥K) : G), hKW (a * b).2⟩ : ↥W) = ⟨a, hKW a.2⟩ * ⟨b, hKW b.2⟩ := rfl
        rw [this, map_mul]; rfl }
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : ((α ⟨a, hKW a.2⟩ : ↥W) : G) = ((α ⟨b, hKW b.2⟩ : ↥W) : G) :=
      congrArg (fun x : ↥K => (x : G)) hab
    have h2 : α ⟨a, hKW a.2⟩ = α ⟨b, hKW b.2⟩ := Subtype.ext h1
    have h3 := α.injective h2
    exact Subtype.ext (congrArg (fun x : ↥W => (x : G)) h3)
  have hbij : Function.Bijective f := ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  exact ⟨MulEquiv.ofBijective f hbij, fun k => rfl⟩

namespace OuterS16Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (c : OuterS16Ctx G L z t T E Q x B β S)

include c

theorem induced_stab {s : G} (hS : S16Gen S s z t) (α : MulAut ↥(Dsub s z ⊔ E))
    (hD : ∀ x : ↥(Dsub s z ⊔ E), (x : G) ∈ Dsub s z → ((α x : ↥(Dsub s z ⊔ E)) : G) ∈ Dsub s z)
    (hE : ∀ x : ↥(Dsub s z ⊔ E), (x : G) ∈ E → ((α x : ↥(Dsub s z ⊔ E)) : G) ∈ E) :
    ∃ m ∈ normalizer ((Dsub s z ⊔ E : Subgroup G) : Set G),
      ∀ w : ↥(Dsub s z ⊔ E), ((α w : ↥(Dsub s z ⊔ E)) : G) = m * w * m⁻¹ := by
  classical
  have hDS : Dsub s z ≤ S := Dsub_le hS.hs hS.hzS
  have hDW : Dsub s z ≤ Dsub s z ⊔ E := le_sup_left
  have hEW : E ≤ Dsub s z ⊔ E := le_sup_right
  obtain ⟨αD, hαD⟩ := exists_restrict_aut hDW α hD
  obtain ⟨αE, hαE⟩ := exists_restrict_aut hEW α hE
  have hzt : ∃ y : G, y * z * y⁻¹ = z * t := ⟨x, c.hyp.x_z⟩
  obtain ⟨n, hnz, hn⟩ := c.hyp.outerE.exists_cover hzt c.hyp.wFacts c.hyp.autE c.hyp.cardT αE
  have hnz' : (n : G) * z = z * n := mem_centralizer_singleton_iff.1 hnz
  have hnact : ∀ e : ↥E, (n : G) * e * (n : G)⁻¹ = ((αE e : ↥E) : G) := by
    intro e
    rw [← hn]
    simp
  have hnS : ∀ y ∈ S, (n : G) * y * (n : G)⁻¹ ∈ S := fun y hy => c.normHE_norm_S n.2 hnz' hy
  have hnSn : (n : G) ∈ normalizer (S : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hnS y hy, fun hy => ?_⟩
    have hn' : (n : G)⁻¹ ∈ normalizer (E : Set G) := inv_mem n.2
    have hnz'' : (n : G)⁻¹ * z = z * (n : G)⁻¹ := by
      calc (n : G)⁻¹ * z = (n : G)⁻¹ * (z * n) * (n : G)⁻¹ := by group
        _ = (n : G)⁻¹ * (n * z) * (n : G)⁻¹ := by rw [hnz']
        _ = z * (n : G)⁻¹ := by group
    have := c.normHE_norm_S hn' hnz'' hy
    simpa [mul_assoc] using this
  have hnzc : (n : G) * z * (n : G)⁻¹ = z := by
    calc (n : G) * z * (n : G)⁻¹ = (z * n) * (n : G)⁻¹ := by rw [hnz']
      _ = z := by group
  have hnD : ∀ d ∈ Dsub s z, (n : G) * d * (n : G)⁻¹ ∈ Dsub s z :=
    normalizes_Dsub hS hnSn hnzc
  let βn : MulAut ↥(Dsub s z) :=
    { toFun := fun d => ⟨(n : G) * d * (n : G)⁻¹, hnD d d.2⟩
      invFun := fun d => ⟨(n : G)⁻¹ * d * (n : G), by
        have hD' : ∀ d ∈ Dsub s z, (n : G)⁻¹ * d * (n : G) ∈ Dsub s z := by
          intro d hd
          have hn' : (n : G)⁻¹ ∈ normalizer (E : Set G) := inv_mem n.2
          have hnz'' : (n : G)⁻¹ * z = z * (n : G)⁻¹ := by
            calc (n : G)⁻¹ * z = (n : G)⁻¹ * (z * n) * (n : G)⁻¹ := by group
              _ = (n : G)⁻¹ * (n * z) * (n : G)⁻¹ := by rw [hnz']
              _ = z * (n : G)⁻¹ := by group
          have hn'S : (n : G)⁻¹ ∈ normalizer (S : Set G) := inv_mem hnSn
          have hnzc' : (n : G)⁻¹ * z * ((n : G)⁻¹)⁻¹ = z := by
            calc (n : G)⁻¹ * z * ((n : G)⁻¹)⁻¹ = (z * (n : G)⁻¹) * ((n : G)⁻¹)⁻¹ := by rw [hnz'']
              _ = z := by group
          have := normalizes_Dsub hS hn'S hnzc' d hd
          simpa using this
        exact hD' d d.2⟩
      left_inv := fun d => Subtype.ext (by group)
      right_inv := fun d => Subtype.ext (by group)
      map_mul' := fun a b => Subtype.ext (by
        show (n : G) * ((a : G) * b) * (n : G)⁻¹ =
          ((n : G) * a * (n : G)⁻¹) * ((n : G) * b * (n : G)⁻¹)
        group) }
  obtain ⟨s', hs'S, hs'⟩ := exists_induced_dauts hS (αD * βn⁻¹)
  set m : G := s' * (n : G) with hm
  have hs'E : ∀ e ∈ E, s' * e = e * s' := fun e he =>
    (mem_centralizer_iff.1 (c.SC hs'S) e he).symm
  have hmD : ∀ d : ↥(Dsub s z), m * (d : G) * m⁻¹ = ((α ⟨d, hDW d.2⟩ : ↥(Dsub s z ⊔ E)) : G) := by
    intro d
    have h1 := hs' (βn d)
    have h2 : (αD * βn⁻¹) (βn d) = αD d := by
      show αD (βn⁻¹ (βn d)) = αD d
      rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rw [h2, hαD d] at h1
    calc m * (d : G) * m⁻¹ = s' * ((n : G) * d * (n : G)⁻¹) * s'⁻¹ := by rw [hm]; group
      _ = s' * ((βn d : ↥(Dsub s z)) : G) * s'⁻¹ := rfl
      _ = ((α ⟨d, hDW d.2⟩ : ↥(Dsub s z ⊔ E)) : G) := h1.symm
  have hmE : ∀ e : ↥E, m * (e : G) * m⁻¹ = ((α ⟨e, hEW e.2⟩ : ↥(Dsub s z ⊔ E)) : G) := by
    intro e
    have h1 : (n : G) * e * (n : G)⁻¹ = ((αE e : ↥E) : G) := hnact e
    calc m * (e : G) * m⁻¹ = s' * ((n : G) * e * (n : G)⁻¹) * s'⁻¹ := by rw [hm]; group
      _ = s' * ((αE e : ↥E) : G) * s'⁻¹ := by rw [h1]
      _ = ((αE e : ↥E) : G) := by
        rw [hs'E _ (αE e).2]; group
      _ = ((α ⟨e, hEW e.2⟩ : ↥(Dsub s z ⊔ E)) : G) := hαE e
  have hED : E ≤ centralizer ((Dsub s z : Subgroup G) : Set G) := fun e he =>
    mem_centralizer_iff.2 fun d hd => (mem_centralizer_iff.1 (c.SC (hDS hd)) e he).symm
  have hmW : ∀ w : ↥(Dsub s z ⊔ E), ((α w : ↥(Dsub s z ⊔ E)) : G) = m * w * m⁻¹ := by
    intro w
    obtain ⟨d, hd, e, he, hwde⟩ := exists_mul_of_mem_sup_comm' hED w.2
    have hw' : w = (⟨d, hDW hd⟩ : ↥(Dsub s z ⊔ E)) * ⟨e, hEW he⟩ := Subtype.ext hwde
    rw [hw', map_mul]
    have h1 := hmD ⟨d, hd⟩
    have h2 := hmE ⟨e, he⟩
    show ((α ⟨d, hDW hd⟩ : ↥(Dsub s z ⊔ E)) : G) * ((α ⟨e, hEW he⟩ : ↥(Dsub s z ⊔ E)) : G) =
      m * (d * e) * m⁻¹
    rw [← h1, ← h2]
    group
  refine ⟨m, ?_, hmW⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have := (α ⟨h, hh⟩).2
    rw [hmW ⟨h, hh⟩] at this
    exact this
  · intro hh
    obtain ⟨w', hw'⟩ := α.surjective ⟨m * h * m⁻¹, hh⟩
    have h1 : ((α w' : ↥(Dsub s z ⊔ E)) : G) = m * h * m⁻¹ := congrArg Subtype.val hw'
    rw [hmW w'] at h1
    have h2 : (w' : G) = h := by
      calc (w' : G) = m⁻¹ * (m * w' * m⁻¹) * m := by group
        _ = m⁻¹ * (m * h * m⁻¹) * m := by rw [h1]
        _ = h := by group
    rw [← h2]
    exact w'.2

end OuterS16Ctx

end CFSG.EvenSporadicStandard.Fin76b

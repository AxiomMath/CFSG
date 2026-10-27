module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23.Inspect

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G G' : Type} [Group G] [Group G']

theorem map_conjSub_mulEquiv (e : G ≃* G') (a : G) (K : Subgroup G) :
    (conjSub a K).map e.toMonoidHom = conjSub (e a) (K.map e.toMonoidHom) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_conjSub_iff, mem_conjSub_iff, Subgroup.mem_map_equiv]
  simp [mul_assoc]

theorem map_comap_mulEquiv (e : G ≃* G') (T : Subgroup G') :
    (T.comap e.toMonoidHom).map e.toMonoidHom = T :=
  Subgroup.map_comap_eq_self_of_surjective e.surjective T

theorem map_mem_q8Fam (e : G ≃* G') {T : Subgroup G} (hT : T ∈ q8Fam G) :
    T.map e.toMonoidHom ∈ q8Fam G' := by
  obtain ⟨f⟩ := hT
  exact ⟨(T.equivMapOfInjective e.toMonoidHom e.injective).symm.trans f⟩

theorem comap_mem_q8Fam (e : G ≃* G') {T : Subgroup G'} (hT : T ∈ q8Fam G') :
    T.comap e.toMonoidHom ∈ q8Fam G := by
  obtain ⟨f⟩ := hT
  exact ⟨((T.comap e.toMonoidHom).equivMapOfInjective e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr (map_comap_mulEquiv e T)).trans f)⟩

theorem centralizer_map_mulEquiv (e : G ≃* G') (t : G) :
    Subgroup.centralizer {e t} = (Subgroup.centralizer {t}).map e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply e.injective
    simp [h]
  · intro h
    apply e.symm.injective
    simp [h]

theorem isUniqueInvolution_map_mulEquiv (e : G ≃* G') {K : Subgroup G} {t : G}
    (h : IsUniqueInvolution K t) : IsUniqueInvolution (K.map e.toMonoidHom) (e t) where
  mem := Subgroup.mem_map_of_mem _ h.mem
  ne_one := by
    intro h1
    exact h.ne_one (e.injective (h1.trans e.map_one.symm))
  sq := by rw [← map_mul, h.sq, map_one]
  unique := by
    intro y hy hy2
    rw [Subgroup.mem_map_equiv] at hy
    have h2 : e.symm y * e.symm y = 1 := by rw [← map_mul, hy2, map_one]
    rcases h.unique _ hy h2 with h3 | h3
    · left
      simpa using congrArg e h3
    · right
      simpa using congrArg e h3

noncomputable def G23Data.map (D : G23Data G) (e : G ≃* G') : G23Data G' where
  t := e D.t
  X := D.X.map e.toMonoidHom
  K₁ := D.K₁.map e.toMonoidHom
  K₂ := D.K₂.map e.toMonoidHom
  g := e D.g
  cent := by rw [centralizer_map_mulEquiv, D.cent]
  census := by
    intro T hT
    obtain ⟨a, ha⟩ := D.census _ (comap_mem_q8Fam e hT)
    refine ⟨e a, ?_⟩
    rcases ha with ha | ha
    · left
      rw [← map_conjSub_mulEquiv, ha, map_comap_mulEquiv]
    · right
      rw [← map_conjSub_mulEquiv, ha, map_comap_mulEquiv]
  censusX := by
    intro T hT hTX
    have hle : T.comap e.toMonoidHom ≤ D.X := by
      intro x hx
      have hx' : e x ∈ D.X.map e.toMonoidHom := hTX hx
      rw [Subgroup.mem_map_equiv] at hx'
      simpa using hx'
    rcases D.censusX _ (comap_mem_q8Fam e hT) hle with h | h
    · left
      rw [← map_comap_mulEquiv e T, h]
    · right
      rw [← map_comap_mulEquiv e T, h]
  mem₁ := map_mem_q8Fam e D.mem₁
  mem₂ := map_mem_q8Fam e D.mem₂
  inv₁ := isUniqueInvolution_map_mulEquiv e D.inv₁
  inv₂ := isUniqueInvolution_map_mulEquiv e D.inv₂
  nor₁ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxn := Subgroup.mem_normalizer_iff.mp (D.nor₁ hx) (e.symm y)
    simp only [SetLike.mem_coe, Subgroup.mem_map_equiv] at hxn ⊢
    rw [hxn]
    simp
  ne := fun h => D.ne (Subgroup.map_injective e.injective h)
  edgeIn := by
    obtain ⟨c, hc, hc4, hcX⟩ := D.edgeIn
    refine ⟨e c, Subgroup.mem_map_of_mem _ hc, by rw [MulEquiv.orderOf_eq, hc4], ?_⟩
    have : e (D.g * c * D.g⁻¹) ∈ D.X.map e.toMonoidHom := Subgroup.mem_map_of_mem _ hcX
    simpa using this
  edgeOut := by
    obtain ⟨k, hk, hkX⟩ := D.edgeOut
    refine ⟨e k, Subgroup.mem_map_of_mem _ hk, ?_⟩
    rw [Subgroup.mem_map_equiv]
    simpa using hkX
  gen := by
    intro N hXN hgN
    have hX : D.X ≤ N.comap e.toMonoidHom := fun x hx => hXN (Subgroup.mem_map_of_mem _ hx)
    have htop := D.gen _ hX hgN
    rw [eq_top_iff]
    intro y _
    have hy : e.symm y ∈ N.comap e.toMonoidHom := by rw [htop]; trivial
    simpa using hy

theorem conjSub_mem_of_conjSub_mem {Φ : Set (Subgroup G)} (hinv : ConjInvariant Φ)
    {X : Subgroup G} {c : G} (hc : conjSub c X ∈ Φ) (d : G) : conjSub d X ∈ Φ := by
  have h := hinv (d * c⁻¹) _ hc
  rwa [← conjSub_mul, inv_mul_cancel_right] at h

theorem G23Data.eq_q8Fam (D : G23Data G) {Φ : Set (Subgroup G)} (hsub : Φ ⊆ q8Fam G)
    (hinv : ConjInvariant Φ) {K J : Subgroup G} (hK : K ∈ Φ) (hJ : J ∈ Φ)
    (hJK : ∀ a : G, conjSub a K ≠ J) : Φ = q8Fam G := by
  refine Set.Subset.antisymm hsub fun T hT => ?_
  obtain ⟨a, ha⟩ := D.census K (hsub hK)
  obtain ⟨b, hb⟩ := D.census J (hsub hJ)
  have hcross : ∀ X : Subgroup G, conjSub a X = K → conjSub b X = J → False := by
    intro X hX hY
    apply hJK (b * a⁻¹)
    rw [← hX, ← conjSub_mul, inv_mul_cancel_right, hY]
  have h12 : (∃ c, conjSub c D.K₁ ∈ Φ) ∧ ∃ c, conjSub c D.K₂ ∈ Φ := by
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact (hcross _ ha hb).elim
    · exact ⟨⟨a, ha ▸ hK⟩, ⟨b, hb ▸ hJ⟩⟩
    · exact ⟨⟨b, hb ▸ hJ⟩, ⟨a, ha ▸ hK⟩⟩
    · exact (hcross _ ha hb).elim
  obtain ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ := h12
  obtain ⟨d, hd | hd⟩ := D.census T hT
  · exact hd ▸ conjSub_mem_of_conjSub_mem hinv hc₁ d
  · exact hd ▸ conjSub_mem_of_conjSub_mem hinv hc₂ d

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Inner

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Family

section Out2

variable {W : Type} [CommGroup W]

theorem normal_sup_of_le_normalizer {L E : Subgroup (MulAut W)}
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) : (L.subgroupOf (L ⊔ E)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact sup_le L.le_normalizer hE

@[expose] noncomputable def actS {L E : Subgroup (MulAut W)}
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) {S : Type} [Group S] (e : CQ L ≃* S) :
    ↥(L ⊔ E) →* MulAut S :=
  (MulAut.congr e).toMonoidHom.comp
    (actionOnCQ (le_sup_left : L ≤ L ⊔ E) (normal_sup_of_le_normalizer hE))

theorem actS_apply {L E : Subgroup (MulAut W)}
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) {S : Type} [Group S] (e : CQ L ≃* S)
    (h : ↥(L ⊔ E)) : actS hE e h =
      MulAut.congr e (actionOnCQ (le_sup_left : L ≤ L ⊔ E) (normal_sup_of_le_normalizer hE) h) :=
  rfl

theorem congr_conj {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) (q : G) :
    MulAut.congr ψ (MulAut.conj q) = MulAut.conj (ψ q) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem actS_of_mem {L E : Subgroup (MulAut W)}
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) {S : Type} [Group S] (e : CQ L ≃* S)
    (l : ↥L) : actS hE e ⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩ = MulAut.conj (redHom L e l) := by
  rw [actS_apply]
  have : actionOnCQ (le_sup_left : L ≤ L ⊔ E) (normal_sup_of_le_normalizer hE)
      ⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩ = MulAut.conj (QuotientGroup.mk l : CQ L) := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [actionOnCQ_mk, MulAut.conj_apply]
      show _ = (QuotientGroup.mk l * QuotientGroup.mk y * (QuotientGroup.mk l)⁻¹ : CQ L)
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
  rw [this, congr_conj, redHom_apply]

theorem conj_mem_range_actS {L E : Subgroup (MulAut W)}
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) {S : Type} [Group S] (e : CQ L ≃* S)
    (s : S) : MulAut.conj s ∈ (actS hE e).range := by
  obtain ⟨l, rfl⟩ := redHom_surjective L e s
  exact ⟨⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩, actS_of_mem hE e l⟩

variable [Finite W]

theorem mem_of_actS_inner (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S) {b : MulAut W} (hbE : b ∈ E)
    (hin : actS hE e ⟨b, Subgroup.mem_sup_right hbE⟩ ∈ (MulAut.conj : S →* MulAut S).range) : b ∈ L := by
  obtain ⟨s, hs⟩ := hin
  obtain ⟨l, rfl⟩ := redHom_surjective L e s
  have h1 := actS_of_mem hE e l
  set l' : ↥(L ⊔ E) := ⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩ with hl'
  set b' : ↥(L ⊔ E) := ⟨b, Subgroup.mem_sup_right hbE⟩ with hb'
  have h2 : actS hE e (l'⁻¹ * b') = 1 := by
    rw [map_mul, map_inv, h1, ← hs]
    simp
  have h3 : actionOnCQ (le_sup_left : L ≤ L ⊔ E) (normal_sup_of_le_normalizer hE) (l'⁻¹ * b') = 1 := by
    have := h2
    rw [actS_apply] at this
    exact (MulAut.congr e).injective (by rw [this, map_one])
  have h4 := (actionOnCQ_eq_one_iff (le_sup_left : L ≤ L ⊔ E) (normal_sup_of_le_normalizer hE)
    hperf (l'⁻¹ * b')).1 h3
  have h5 : ((l'⁻¹ * b' : ↥(L ⊔ E)) : MulAut W) ∈ L :=
    centralizer_inf_le hW hirr hE hEel ⟨(l'⁻¹ * b').2, h4⟩
  have h6 : b = (l : MulAut W) * ((l'⁻¹ * b' : ↥(L ⊔ E)) : MulAut W) := by
    simp [hl', hb']
  rw [h6]
  exact L.mul_mem l.2 h5

theorem inv_mul_mem_of_not_mem (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] [Finite S] (e : CQ L ≃* S) (hcent : Subgroup.center S = ⊥)
    (hcard2 : Nat.card (MulAut S) ≤ 2 * Nat.card S) {x y : MulAut W} (hx : x ∈ E) (hy : y ∈ E)
    (hxL : x ∉ L) (hyL : y ∉ L) : x⁻¹ * y ∈ L := by
  set x' : ↥(L ⊔ E) := ⟨x, Subgroup.mem_sup_right hx⟩ with hx'
  set y' : ↥(L ⊔ E) := ⟨y, Subgroup.mem_sup_right hy⟩ with hy'
  have hxo : actS hE e x' ∉ (MulAut.conj : S →* MulAut S).range := fun h =>
    hxL (mem_of_actS_inner hW hperf hirr hE hEel e hx h)
  have hyo : actS hE e y' ∉ (MulAut.conj : S →* MulAut S).range := fun h =>
    hyL (mem_of_actS_inner hW hperf hirr hE hEel e hy h)
  have h1 := inner_of_outer_mul hcent hcard2 hxo hyo
  have hmem : x⁻¹ * y ∈ E := E.mul_mem (E.inv_mem hx) hy
  refine mem_of_actS_inner hW hperf hirr hE hEel e hmem ?_
  have : (⟨x⁻¹ * y, Subgroup.mem_sup_right hmem⟩ : ↥(L ⊔ E)) = x'⁻¹ * y' := rfl
  rw [this, map_mul, map_inv]
  exact h1

theorem card_le_two_mul_inf (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] [Finite S] (e : CQ L ≃* S) (hcent : Subgroup.center S = ⊥)
    (hcard2 : Nat.card (MulAut S) ≤ 2 * Nat.card S) :
    Nat.card E ≤ 2 * Nat.card ↥(E ⊓ L) := by
  set E0 : Subgroup ↥E := (E ⊓ L).subgroupOf E with hE0
  have hcard0 : Nat.card E0 = Nat.card ↥(E ⊓ L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul := Subgroup.card_mul_index E0
  have hmemE0 : ∀ x : ↥E, x ∈ E0 ↔ (x : MulAut W) ∈ L := fun x => by
    rw [hE0, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hidx : E0.index ≤ 2 := by
    by_cases htop : E0 = ⊤
    · rw [htop, Subgroup.index_top]; norm_num
    · obtain ⟨a, ha⟩ : ∃ a : ↥E, a ∉ E0 := by
        by_contra h
        push Not at h
        exact htop (eq_top_iff.2 fun x _ => h x)
      have hnot : ∀ x : ↥E, x ∉ E0 → x⁻¹ * a ∈ E0 := fun x hx =>
        (hmemE0 _).2 (inv_mul_mem_of_not_mem hW hperf hirr hE hEel e hcent hcard2 x.2 a.2
          (fun h => hx ((hmemE0 x).2 h)) (fun h => ha ((hmemE0 a).2 h)))
      have h2 : E0.index = 2 := by
        rw [Subgroup.index_eq_two_iff]
        refine ⟨a, fun x => ?_⟩
        by_cases hx : x ∈ E0
        · refine Or.inr ⟨hx, fun h => ha ?_⟩
          have := E0.mul_mem (E0.inv_mem hx) h
          simpa using this
        · refine Or.inl ⟨?_, hx⟩
          have := hnot x⁻¹ (fun h => hx (by simpa using E0.inv_mem h))
          simpa using this
      rw [h2]
  rw [hcard0] at hmul
  calc Nat.card E = Nat.card ↥(E ⊓ L) * E0.index := hmul.symm
    _ ≤ Nat.card ↥(E ⊓ L) * 2 := Nat.mul_le_mul le_rfl hidx
    _ = 2 * Nat.card ↥(E ⊓ L) := by ring

theorem out2_dichotomy (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] [Finite S] (e : CQ L ≃* S) (hcent : Subgroup.center S = ⊥)
    (hcard2 : Nat.card (MulAut S) ≤ 2 * Nat.card S) {r p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    (hD : ∀ ψ : MulAut S, ψ ∉ (MulAut.conj : S →* MulAut S).range → ψ * ψ = 1 →
      ∃ α : MulAut S, orderOf (ψ * (α * ψ * α⁻¹)) = p) :
    E ≤ L ∨ (2 ^ orderOf (2 : ZMod p) ≤ (fixV E).index ^ 2 ∧ Nat.card E ≤ 2 ^ (r + 1)) := by
  by_cases hEL : E ≤ L
  · exact Or.inl hEL
  right
  obtain ⟨b, hbE, hbL⟩ : ∃ b ∈ E, b ∉ L := by
    by_contra h
    push Not at h
    exact hEL h
  set b' : ↥(L ⊔ E) := ⟨b, Subgroup.mem_sup_right hbE⟩ with hb'
  have hbo : actS hE e b' ∉ (MulAut.conj : S →* MulAut S).range := fun h =>
    hbL (mem_of_actS_inner hW hperf hirr hE hEel e hbE h)
  have hb2 : actS hE e b' * actS hE e b' = 1 := by
    rw [← map_mul]
    have : b' * b' = 1 := Subtype.ext (by simpa [sq] using hEel.2 b hbE)
    rw [this, map_one]
  obtain ⟨α, hα⟩ := hD _ hbo hb2
  have hαr : α ∈ (actS hE e).range := by
    by_cases hαi : α ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨s, rfl⟩ := hαi
      exact conj_mem_range_actS hE e s
    · have h1 := inner_of_outer_mul hcent hcard2 hbo hαi
      have h2 : (actS hE e b')⁻¹ * α ∈ (actS hE e).range := by
        obtain ⟨s, hs⟩ := h1
        rw [← hs]
        exact conj_mem_range_actS hE e s
      have : α = actS hE e b' * ((actS hE e b')⁻¹ * α) := by group
      rw [this]
      exact (actS hE e).range.mul_mem ⟨b', rfl⟩ h2
  have hdisp := two_pow_le_index_pow_of_mem hW (G := L ⊔ E) (actS hE e) (B := E) [1, α]
    (by
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact (actS hE e).range.one_mem
      · simp only [List.mem_singleton] at hc
        rw [hc]
        exact hαr) hp2 hα (by
      refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨1, by simp, b', hbE, by simp⟩)
        (Subgroup.subset_closure ⟨α, by simp, b', hbE, rfl⟩))
  have hEel' : IsElemAbelian2 (E ⊓ L) :=
    ⟨fun a ha b hb => hEel.1 a ha.1 b hb.1, fun a ha => hEel.2 a ha.1⟩
  have hE0 : Nat.card ↥(E ⊓ L) ≤ 2 ^ r := card_le_two_pow_of_le hW hirr inf_le_right hEel' e hr
  have hEcard := card_le_two_mul_inf hW hperf hirr hE hEel e hcent hcard2
  refine ⟨by simpa using hdisp, ?_⟩
  calc Nat.card E ≤ 2 * Nat.card ↥(E ⊓ L) := hEcard
    _ ≤ 2 * 2 ^ r := Nat.mul_le_mul le_rfl hE0
    _ = 2 ^ (r + 1) := by ring

theorem out2_dichotomy_gen (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] [Finite S] (e : CQ L ≃* S) (hcent : Subgroup.center S = ⊥)
    (hcard2 : Nat.card (MulAut S) ≤ 2 * Nat.card S) {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hD : ∀ ψ : MulAut S, ψ ∉ (MulAut.conj : S →* MulAut S).range → ψ * ψ = 1 →
      ∃ cs : List (MulAut S), cs.length = k ∧
        (∀ c ∈ cs, c ∈ (MulAut.conj : S →* MulAut S).range) ∧
        ∃ x ∈ Subgroup.closure (conjSet cs {ψ}), orderOf x = p) :
    E ≤ L ∨ (2 ^ orderOf (2 : ZMod p) ≤ (fixV E).index ^ k ∧
      Nat.card E ≤ 2 * Nat.card ↥(E ⊓ L)) := by
  by_cases hEL : E ≤ L
  · exact Or.inl hEL
  right
  obtain ⟨b, hbE, hbL⟩ : ∃ b ∈ E, b ∉ L := by
    by_contra h
    push Not at h
    exact hEL h
  set b' : ↥(L ⊔ E) := ⟨b, Subgroup.mem_sup_right hbE⟩ with hb'
  have hbo : actS hE e b' ∉ (MulAut.conj : S →* MulAut S).range := fun h =>
    hbL (mem_of_actS_inner hW hperf hirr hE hEel e hbE h)
  have hb2 : actS hE e b' * actS hE e b' = 1 := by
    rw [← map_mul]
    have : b' * b' = 1 := Subtype.ext (by simpa [sq] using hEel.2 b hbE)
    rw [this, map_one]
  obtain ⟨cs, hlen, hcsin, x, hx, hxp⟩ := hD _ hbo hb2
  have hdisp := two_pow_le_index_pow_of_mem hW (G := L ⊔ E) (actS hE e) (B := E) cs
    (by
      intro c hc
      obtain ⟨s, rfl⟩ := hcsin c hc
      exact conj_mem_range_actS hE e s) hp2 hxp (by
      refine Subgroup.closure_mono ?_ hx
      rintro _ ⟨c, hc, t, ht, rfl⟩
      have : t = actS hE e b' := by simpa using ht
      subst this
      exact ⟨c, hc, b', hbE, rfl⟩)
  have hEcard := card_le_two_mul_inf hW hperf hirr hE hEel e hcent hcard2
  exact ⟨by rw [← hlen]; exact hdisp, hEcard⟩

end Out2

end CFSG.QuasithinUnique.Setup.X1

module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartOne.S15K.CentralCover
public import CFSG.LieType.Steinberg.CentralExt.CoprimeSplit

public section

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.LinkPSUAux

section Conj

variable {G : Type} [Group G] (L : Subgroup G)

@[expose] def conjL (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) : ↥L ≃* ↥L where
  toFun l := ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg l).1 l.2⟩
  invFun l := ⟨g⁻¹ * l * g, (Subgroup.mem_normalizer_iff''.1 hg l).1 l.2⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[expose] def conjHom : ↥(Subgroup.normalizer (L : Set G)) →* MulAut ↥L where
  toFun g := conjL L g.1 g.2
  map_one' := MulEquiv.ext fun l => Subtype.ext (by simp [conjL])
  map_mul' g h := MulEquiv.ext fun l => Subtype.ext (by simp [conjL, mul_assoc])

variable {L}

theorem map_conjHom_eq (W : Subgroup ↥L)
    (hW : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (w : ↥L), w ∈ W → conjHom L g w ∈ W)
    (g : ↥(Subgroup.normalizer (L : Set G))) : W.map (conjHom L g : ↥L →* ↥L) = W := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hW g w hw
  · intro hx
    refine ⟨conjHom L g⁻¹ x, hW g⁻¹ x hx, ?_⟩
    change conjHom L g (conjHom L g⁻¹ x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

@[expose] def quotHom (W : Subgroup ↥L) [W.Normal]
    (hW : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (w : ↥L), w ∈ W → conjHom L g w ∈ W) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (↥L ⧸ W) where
  toFun g := QuotientGroup.congr W W (conjHom L g) (map_conjHom_eq W hW g)
  map_one' := MulEquiv.ext fun x => QuotientGroup.induction_on x fun l => by
    rw [QuotientGroup.congr_mk]
    simp
  map_mul' g h := MulEquiv.ext fun x => QuotientGroup.induction_on x fun l => by
    simp only [MulAut.mul_apply, QuotientGroup.congr_mk, map_mul]

theorem quotHom_mk (W : Subgroup ↥L) [W.Normal]
    (hW : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (w : ↥L), w ∈ W → conjHom L g w ∈ W)
    (g : ↥(Subgroup.normalizer (L : Set G))) (l : ↥L) :
    quotHom W hW g (QuotientGroup.mk l) = QuotientGroup.mk (conjHom L g l) :=
  QuotientGroup.congr_mk W W (conjHom L g) (map_conjHom_eq W hW g) l

theorem quotHom_of_mem (W : Subgroup ↥L) [W.Normal]
    (hW : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (w : ↥L), w ∈ W → conjHom L g w ∈ W)
    (l : ↥L) :
    quotHom W hW ⟨(l : G), Subgroup.le_normalizer l.2⟩ =
      MulAut.conj (QuotientGroup.mk l : ↥L ⧸ W) := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun u => ?_
  rw [quotHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem quotHom_of_centralizer (W : Subgroup ↥L) [W.Normal]
    (hW : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (w : ↥L), w ∈ W → conjHom L g w ∈ W)
    {c : G} (hc : c ∈ Subgroup.centralizer (L : Set G)) :
    quotHom W hW ⟨c, Subgroup.centralizer_le_normalizer _ hc⟩ = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun u => ?_
  rw [quotHom_mk]
  change QuotientGroup.mk _ = QuotientGroup.mk u
  congr 1
  apply Subtype.ext
  change c * (u : G) * c⁻¹ = u
  rw [← Subgroup.mem_centralizer_iff.1 hc u u.2, mul_assoc, mul_inv_cancel, mul_one]

end Conj

section Inn

variable {G : Type} [Group G] {L : Subgroup G}

theorem quotHom_mem_inner_iff [Group.IsPerfect ↥L] (Z : Subgroup ↥L) [Z.Normal]
    (hZc : Z ≤ Subgroup.center ↥L)
    (hZ : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (w : ↥L), w ∈ Z → conjHom L g w ∈ Z)
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    quotHom Z hZ ⟨g, hg⟩ ∈ inner (↥L ⧸ Z) ↔ g ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := (MonoidHom.mem_range).1 h
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    have key : ∀ u : ↥L, (conjHom L ⟨g, hg⟩).toMonoidHom u = (MulAut.conj l).toMonoidHom u := by
      refine CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq (QuotientGroup.mk' Z)
        (by rw [QuotientGroup.ker_mk']; exact hZc) inferInstance _ _ fun u => ?_
      have := congrArg (fun m : MulAut (↥L ⧸ Z) => m (QuotientGroup.mk u)) hx
      simp only [quotHom_mk, MulAut.conj_apply] at this
      simpa [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv] using this.symm
    have hc : (l : G)⁻¹ * g ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 := congrArg Subtype.val (key ⟨u, hu⟩)
      change g * u * g⁻¹ = (l : G) * u * (l : G)⁻¹ at h1
      have h2 : g * u = (l : G) * u * (l : G)⁻¹ * g := by
        rw [← h1]; group
      calc u * ((l : G)⁻¹ * g) = (l : G)⁻¹ * ((l : G) * u * (l : G)⁻¹ * g) := by group
        _ = (l : G)⁻¹ * (g * u) := by rw [h2]
        _ = (l : G)⁻¹ * g * u := by group
    have := Subgroup.mul_mem_sup l.2 hc
    rwa [mul_inv_cancel_left] at this
  · intro h
    set S : Subgroup G :=
      Subgroup.map (Subgroup.normalizer (L : Set G)).subtype
        ((inner (↥L ⧸ Z)).comap (quotHom Z hZ)) with hS
    have hLS : L ≤ S := fun l hl => by
      refine ⟨⟨l, Subgroup.le_normalizer hl⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      exact ⟨QuotientGroup.mk ⟨l, hl⟩, (quotHom_of_mem Z hZ ⟨l, hl⟩).symm⟩
    have hCS : Subgroup.centralizer (L : Set G) ≤ S := fun c hc => by
      refine ⟨⟨c, Subgroup.centralizer_le_normalizer _ hc⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, quotHom_of_centralizer Z hZ hc]
      exact one_mem _
    obtain ⟨⟨g', hg'⟩, hmem, hgg⟩ := sup_le hLS hCS h
    have : (⟨g', hg'⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨g, hg⟩ := Subtype.ext hgg
    rw [← this]
    exact hmem

end Inn

theorem congr_apply_apply {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (α : MulAut X) (x : X) :
    MulAut.congr e α (e x) = e (α x) := by
  simp [MulAut.congr_apply]

theorem congr_mem_inner_iff {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (α : MulAut X) :
    MulAut.congr e α ∈ inner Y ↔ α ∈ inner X := by
  constructor
  · intro h
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at h
    obtain ⟨β, hβ, hβα⟩ := h
    have : β = α := (MulAut.congr e).injective hβα
    exact this ▸ hβ
  · intro h
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e]
    exact ⟨α, h, rfl⟩

section Central

open CFSG.LieType.Steinberg.CentralExt.CoprimeSplit

variable {G : Type} [Group G] {L : Subgroup G}

theorem conjHom_mem_center (g : ↥(Subgroup.normalizer (L : Set G))) {w : ↥L}
    (hw : w ∈ Subgroup.center ↥L) : conjHom L g w ∈ Subgroup.center ↥L := by
  rw [← Subgroup.map_center_eq (conjHom L g)]
  exact ⟨w, hw, rfl⟩

theorem conjHom_mem_copPart (r : ℕ) (g : ↥(Subgroup.normalizer (L : Set G))) {w : ↥L}
    (hw : w ∈ copPart r (Subgroup.center ↥L) le_rfl) :
    conjHom L g w ∈ copPart r (Subgroup.center ↥L) le_rfl :=
  ⟨conjHom_mem_center g hw.1, by rw [MulEquiv.orderOf_eq]; exact hw.2⟩

theorem eq_one_of_mem_copPart_of_pow_eq_one {E : Type*} [Group E] {C : Subgroup E}
    {hC : C ≤ Subgroup.center E} {r : ℕ} {x : E} (hx : x ∈ copPart r C hC) (hxr : x ^ r = 1) :
    x = 1 := by
  have h1 : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one hxr
  have h2 : (orderOf x).Coprime r := hx.2.symm
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h2 h1)

@[expose] def projHom (N Z : Subgroup ↥L) [N.Normal] [Z.Normal] (h : N ≤ Z) :
    ↥L ⧸ N →* ↥L ⧸ Z :=
  QuotientGroup.map N Z (MonoidHom.id _) h

theorem eq_of_mk_eq_of_pow {E : Type*} [Group E] {r : ℕ} {w v : E}
    (hv : v ∈ Subgroup.center E) (hwr : w ^ r = 1) (hvr : v ^ r = 1)
    (h : (QuotientGroup.mk w : E ⧸ copPart r (Subgroup.center E) le_rfl) = QuotientGroup.mk v) :
    w = v := by
  have hmem : w⁻¹ * v ∈ copPart r (Subgroup.center E) le_rfl := QuotientGroup.eq.1 h
  have hcomm : Commute w⁻¹ v := Subgroup.mem_center_iff.1 hv w⁻¹
  have hpow : (w⁻¹ * v) ^ r = 1 := by
    rw [hcomm.mul_pow, inv_pow, hwr, hvr, inv_one, one_mul]
  exact inv_mul_eq_one.1 (eq_one_of_mem_copPart_of_pow_eq_one hmem hpow)

theorem mem_zpowers_of_pow_eq_one {C : Type*} [Group C] [IsCyclic C] [Finite C] {r : ℕ}
    {z x : C} (hz : orderOf z = r) (hx : x ^ r = 1) : x ∈ Subgroup.zpowers z := by
  have h1 : Subgroup.zpowers x ≤ Subgroup.zpowers z := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hz]
    exact orderOf_dvd_of_pow_eq_one hx
  exact h1 (Subgroup.mem_zpowers x)

end Central

section Abstract

theorem lift_comm {S Lb Q : Type*} [Group S] [Group Lb] [Group Q] [Group.IsPerfect S]
    (θ : S →* Q) (π₀ : Lb →* Q) (hc : π₀.ker ≤ Subgroup.center Lb)
    (φ : S →* Lb) (hφ : ∀ g, π₀ (φ g) = θ g)
    (α : S →* S) (β : Lb →* Lb) (σ : Q →* Q)
    (hα : ∀ g, θ (α g) = σ (θ g)) (hβ : ∀ x, π₀ (β x) = σ (π₀ x)) :
    ∀ g, φ (α g) = β (φ g) :=
  CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq π₀ hc inferInstance (φ.comp α) (β.comp φ)
    fun g => by simp only [MonoidHom.comp_apply, hφ, hα, hβ]

theorem pow_of_mem_ker {S Lb Q : Type*} [Group S] [Group Lb] [Group Q] [Group.IsPerfect S]
    (θ : S →* Q) (π₀ : Lb →* Q) (hc : π₀.ker ≤ Subgroup.center Lb)
    (φ : S →* Lb) (hφ : ∀ g, π₀ (φ g) = θ g) (hsurj : Function.Surjective φ)
    (α : S →* S) (β : Lb →* Lb) (σ : Q →* Q)
    (hα : ∀ g, θ (α g) = σ (θ g)) (hβ : ∀ x, π₀ (β x) = σ (π₀ x))
    (u : ℕ) (hu : ∀ g ∈ θ.ker, α g = g ^ u) : ∀ x ∈ π₀.ker, β x = x ^ u := by
  intro x hx
  obtain ⟨g, rfl⟩ := hsurj x
  have hg : g ∈ θ.ker := by
    rw [MonoidHom.mem_ker, ← hφ]
    exact hx
  rw [← lift_comm θ π₀ hc φ hφ α β σ hα hβ, hu g hg, map_pow]

end Abstract

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.LinkPSUAux

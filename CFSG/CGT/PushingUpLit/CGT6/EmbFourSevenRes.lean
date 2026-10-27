module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenAbel

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

section Res

variable {V : Type} [CommGroup V]

@[expose] def stabW (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ w : V, w ∈ W ↔ g w ∈ W}
  one_mem' := fun w => Iff.rfl
  mul_mem' := fun {a b} ha hb w => (hb w).trans (ha (b w))
  inv_mem' := fun {g} hg w => by
    have h := hg (g⁻¹ w)
    rw [MulAut.apply_inv_self] at h
    exact h.symm

theorem mem_stabW {W : Subgroup V} {g : MulAut V} :
    g ∈ stabW W ↔ ∀ w : V, w ∈ W ↔ g w ∈ W := Iff.rfl

@[expose] def restrictW (W : Subgroup V) : ↥(stabW W) →* MulAut ↥W where
  toFun g :=
    { toFun := fun w => ⟨(g : MulAut V) w, (g.2 (w : V)).mp w.2⟩
      invFun := fun w => ⟨(g : MulAut V)⁻¹ w, ((inv_mem g.2 : (g : MulAut V)⁻¹ ∈ stabW W)
        (w : V)).mp w.2⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  map_one' := by ext; rfl
  map_mul' := fun a b => by ext; rfl

theorem coe_restrictW (W : Subgroup V) (g : ↥(stabW W)) (w : ↥W) :
    ((restrictW W g w : ↥W) : V) = (g : MulAut V) w := rfl

@[expose] def resRange (W : Subgroup V) (H : Subgroup (MulAut V)) (hH : H ≤ stabW W) :
    Subgroup (MulAut ↥W) :=
  ((restrictW W).comp (Subgroup.inclusion hH)).range

theorem mem_resRange {W : Subgroup V} {H : Subgroup (MulAut V)} {hH : H ≤ stabW W}
    {a : MulAut ↥W} :
    a ∈ resRange W H hH ↔ ∃ (g : MulAut V) (hg : g ∈ H), a = restrictW W ⟨g, hH hg⟩ := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem restrictW_mem_resRange {W : Subgroup V} {H : Subgroup (MulAut V)} {hH : H ≤ stabW W}
    {g : MulAut V} (hg : g ∈ H) : restrictW W ⟨g, hH hg⟩ ∈ resRange W H hH :=
  mem_resRange.mpr ⟨g, hg, rfl⟩

theorem card_resRange_dvd (W : Subgroup V) (H : Subgroup (MulAut V)) (hH : H ≤ stabW W) :
    Nat.card (resRange W H hH) ∣ Nat.card H :=
  Subgroup.card_range_dvd _

theorem resRange_le_normalizer {W : Subgroup V} {H₁ H₂ : Subgroup (MulAut V)}
    (h₁ : H₁ ≤ stabW W) (h₂ : H₂ ≤ stabW W)
    (h : H₁ ≤ Subgroup.normalizer (H₂ : Set (MulAut V))) :
    resRange W H₁ h₁ ≤ Subgroup.normalizer (resRange W H₂ h₂ : Set (MulAut ↥W)) := by
  intro a ha
  obtain ⟨g, hg, rfl⟩ := mem_resRange.mp ha
  have hgn := h hg
  have key : ∀ k : MulAut V, k ∈ H₂ → g * k * g⁻¹ ∈ H₂ := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp hgn k).mp hk
  have key' : ∀ k : MulAut V, k ∈ H₂ → g⁻¹ * k * g ∈ H₂ := fun k hk => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgn) k).mp hk
    simpa using this
  refine normalizer_mem_of_conj (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨k, hk, rfl⟩ := mem_resRange.mp hz
    refine mem_resRange.mpr ⟨g * k * g⁻¹, key k hk, ?_⟩
    ext w
    rfl
  · obtain ⟨k, hk, rfl⟩ := mem_resRange.mp hz
    refine mem_resRange.mpr ⟨g⁻¹ * k * g, key' k hk, ?_⟩
    ext w
    rfl

theorem apply_comm_of_resRange {W : Subgroup V} {Y P : Subgroup (MulAut V)}
    (hY : Y ≤ stabW W) (hP : P ≤ stabW W)
    (h : resRange W P hP ≤ Subgroup.centralizer (resRange W Y hY : Set (MulAut ↥W)))
    {x y : MulAut V} (hx : x ∈ P) (hy : y ∈ Y) (w : V) (hw : w ∈ W) :
    (x * y * x⁻¹ * y⁻¹) w = w := by
  have h1 := Subgroup.mem_centralizer_iff.mp (h (restrictW_mem_resRange hx)) _
    (restrictW_mem_resRange hy)
  have h2 : ∀ w' : ↥W, (y : MulAut V) ((x : MulAut V) w') = (x : MulAut V) ((y : MulAut V) w') :=
    fun w' => congrArg (fun f : MulAut ↥W => ((f w' : ↥W) : V)) h1
  have hxs : x ∈ stabW W := hP hx
  have hys : y ∈ stabW W := hY hy
  have hu : (x⁻¹ * y⁻¹ : MulAut V) w ∈ W :=
    ((mem_stabW.mp (mul_mem (inv_mem hxs) (inv_mem hys))) w).mp hw
  have h3 := h2 ⟨(x⁻¹ * y⁻¹) w, hu⟩
  have h4 : y (x ((x⁻¹ * y⁻¹) w)) = w := by simp [MulAut.mul_apply]
  show x (y (x⁻¹ (y⁻¹ w))) = w
  exact h3.symm.trans h4

theorem card_commV_zpowers_res_le [Finite V] (W : Subgroup V) (g : ↥(stabW W)) :
    Nat.card (commV (Subgroup.zpowers (restrictW W g))) ≤
      Nat.card (commV (Subgroup.zpowers (g : MulAut V))) := by
  have hle : (commV (Subgroup.zpowers (restrictW W g))).map W.subtype ≤
      commV (Subgroup.zpowers (g : MulAut V)) := by
    rw [Subgroup.map_le_iff_le_comap]
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, v, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    rw [← map_zpow]
    exact Subgroup.subset_closure ⟨(g : MulAut V) ^ n, Subgroup.zpow_mem_zpowers _ n, v, rfl⟩
  calc Nat.card (commV (Subgroup.zpowers (restrictW W g)))
      = Nat.card ((commV (Subgroup.zpowers (restrictW W g))).map W.subtype) :=
        (Subgroup.card_map_of_injective W.subtype_injective).symm
    _ ≤ _ := Subgroup.card_le_of_le hle

theorem small16_res [Finite V] {Y : Subgroup (MulAut V)} (hY : Small16 Y) (W : Subgroup V)
    (hYW : Y ≤ stabW W) : Small16 (resRange W Y hYW) := by
  obtain ⟨hperf, S, hSY, hSg, hS⟩ := hY
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  let f : ↥Y →* MulAut ↥W := (restrictW W).comp (Subgroup.inclusion hYW)
  have hf : resRange W Y hYW = f.range := rfl
  let SY : Set ↥Y := {y | (y : MulAut V) ∈ S}
  have hSYtop : Subgroup.closure SY = ⊤ := by
    subst hSg
    exact Subgroup.closure_closure_coe_preimage
  refine ⟨?_, f '' SY, ?_, ?_, ?_⟩
  · have htop : ⁅(⊤ : Subgroup ↥Y), (⊤ : Subgroup ↥Y)⁆ = ⊤ :=
      Group.IsPerfect.commutator_eq_top
    rw [hf, MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  · rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  · rw [hf, ← MonoidHom.map_closure, hSYtop, MonoidHom.range_eq_map]
  · rintro _ ⟨y, hy, rfl⟩
    have h5 : (y : MulAut V) ^ 5 = 1 := (hS _ hy).1
    refine ⟨?_, ?_⟩
    · rw [← map_pow]
      have : y ^ 5 = 1 := Subtype.ext h5
      rw [this, map_one]
    · exact (card_commV_zpowers_res_le W (Subgroup.inclusion hYW y)).trans (hS _ hy).2

end Res

end CFSG.CGT.PushingUpLit.CGT6

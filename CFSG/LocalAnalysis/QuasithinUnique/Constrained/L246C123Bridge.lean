module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7B

public section

namespace CFSG.QuasithinUnique.L246.C123

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

variable {G : Type} [Group G] [Finite G] {T Y L : Subgroup G}

section Module

abbrev V₀ (m : Main T Y L) : Type := IntMod (VZ T Y) m.hyp.elem

abbrev U' (m : Main T Y L) : Subgroup (V₀ m) := intSub m.hyp.elem (blockU L)

abbrev Z' (m : Main T Y L) : Subgroup (V₀ m) := intSub m.hyp.elem (blockZ L)

abbrev Msec (m : Main T Y L) : Type := Sec (U' m) (Z' m)

variable (m : Main T Y L)

theorem Z'_eq_bot : Z' m = ⊥ := by
  ext v
  rw [mem_intSub, m.zl, Subgroup.mem_bot, Subgroup.mem_bot]
  exact ⟨fun h => IntMod.val_injective (h.trans IntMod.val_one.symm),
    fun h => by rw [h]; exact IntMod.val_one⟩

noncomputable def ι : ↥(blockU L) →* ↥(U' m) where
  toFun u := ⟨IntMod.mk m.hyp.elem ⟨u, m.uV u.2⟩, u.2⟩
  map_one' := Subtype.ext (IntMod.val_injective rfl)
  map_mul' _ _ := Subtype.ext (IntMod.val_injective rfl)

noncomputable def φ₀ : ↥(blockU L) →* Msec m :=
  (QuotientGroup.mk' ((Z' m).subgroupOf (U' m))).comp (ι m)

theorem φ₀_injective : Function.Injective (φ₀ m) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h1 : ι m u ∈ (Z' m).subgroupOf (U' m) := by
    have : QuotientGroup.mk' ((Z' m).subgroupOf (U' m)) (ι m u) = 1 := hu
    exact (QuotientGroup.eq_one_iff _).1 this
  have h2 : (ι m u : V₀ m) ∈ Z' m := Subgroup.mem_subgroupOf.1 h1
  rw [Z'_eq_bot, Subgroup.mem_bot] at h2
  apply Subtype.ext
  have := congrArg IntMod.val h2
  exact this

theorem φ₀_surjective : Function.Surjective (φ₀ m) := by
  intro s
  induction s using QuotientGroup.induction_on with
  | H x =>
    refine ⟨⟨x.1.val, x.2⟩, ?_⟩
    show QuotientGroup.mk (ι m ⟨x.1.val, x.2⟩) = QuotientGroup.mk x
    congr 1

noncomputable def φeq : ↥(blockU L) ≃* Msec m :=
  MulEquiv.ofBijective (φ₀ m) ⟨φ₀_injective m, φ₀_surjective m⟩

theorem card_Msec : Nat.card (Msec m) = 16 := by
  rw [← m.card_U]
  exact (Nat.card_congr (φeq m).toEquiv).symm

theorem exp_Msec : ∀ x : Msec m, x ^ 2 = 1 := sec_sq_eq_one (fun v => IntMod.sq_eq_one v) _ _

end Module

section Action

variable (m : Main T Y L)

theorem mem_stab (y : ↥Y) :
    convI m.hyp.elem (Subgroup.inclusion m.hyp.YN y) ∈ stabSub (U' m) ⊓ stabSub (Z' m) :=
  ⟨convI_mem_stabSub_intSub m.hyp.elem _ (C1.mem_normalizer_blockU (m.hyp.normal y.2)),
    convI_mem_stabSub_intSub m.hyp.elem _ (C1.mem_normalizer_blockZ (m.hyp.normal y.2))⟩

noncomputable def actY : ↥Y →* MulAut (Msec m) :=
  (secHom (U' m) (Z' m)).comp
    (((convI m.hyp.elem).comp (Subgroup.inclusion m.hyp.YN)).codRestrict
      (stabSub (U' m) ⊓ stabSub (Z' m)) (mem_stab m))

theorem actY_φeq (y : ↥Y) (u u' : ↥(blockU L)) (h : (u' : G) = y * u * (y : G)⁻¹) :
    actY m y (φeq m u) = φeq m u' := by
  show secHom (U' m) (Z' m) ⟨_, mem_stab m y⟩ (QuotientGroup.mk (ι m u)) =
    QuotientGroup.mk (ι m u')
  rw [secHom_apply]
  congr 1
  apply Subtype.ext
  apply IntMod.val_injective
  show (convI m.hyp.elem (Subgroup.inclusion m.hyp.YN y) (IntMod.mk _ ⟨u, _⟩)).val = u'
  rw [convI_apply_val, h]
  rfl

theorem centralizes_of_actY_eq_one {y : ↥Y} (h : actY m y = 1) :
    ∀ u ∈ blockU L, (y : G) * u * (y : G)⁻¹ = u := by
  intro u hu
  have hmem : (y : G) * u * (y : G)⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.1 (m.YU y.2) u).1 hu
  have h1 := actY_φeq m y ⟨u, hu⟩ ⟨_, hmem⟩ rfl
  rw [h, MulAut.one_apply] at h1
  exact (congrArg Subtype.val ((φeq m).injective h1)).symm

end Action

section L2

noncomputable abbrev L₂ (m : Main T Y L) : Subgroup (MulAut (Msec m)) :=
  autSec (autI m.hyp.elem L) (U' m) (Z' m)

variable {m : Main T Y L}

theorem actY_mem_L₂ (hX : autI m.hyp.elem L ≤ stabSub (U' m) ⊓ stabSub (Z' m)) {y : ↥Y}
    (hy : (y : G) ∈ L) : actY m y ∈ L₂ m :=
  (mem_autSec_iff_secHom hX).2
    ⟨⟨convI m.hyp.elem (Subgroup.inclusion m.hyp.YN y), mem_stab m y⟩,
      convI_mem_autI m.hyp.elem hy (m.hyp.YN y.2), rfl⟩

theorem exists_actY_of_mem_L₂ (hX : autI m.hyp.elem L ≤ stabSub (U' m) ⊓ stabSub (Z' m))
    {ψ : MulAut (Msec m)} (hψ : ψ ∈ L₂ m) : ∃ y : ↥Y, (y : G) ∈ L ∧ actY m y = ψ := by
  obtain ⟨g, hgX, rfl⟩ := (mem_autSec_iff_secHom hX).1 hψ
  obtain ⟨l, hl, hlg⟩ := (mem_autI m.hyp.elem).1 hgX
  refine ⟨⟨l, m.hyp.LY hl⟩, hl, ?_⟩
  show secHom (U' m) (Z' m) ⟨_, mem_stab m ⟨l, m.hyp.LY hl⟩⟩ = secHom (U' m) (Z' m) g
  congr 1
  exact Subtype.ext hlg

theorem actY_conj_mem_L₂ (hX : autI m.hyp.elem L ≤ stabSub (U' m) ⊓ stabSub (Z' m)) (y : ↥Y)
    {x : MulAut (Msec m)} (hx : x ∈ L₂ m) : actY m y * x * (actY m y)⁻¹ ∈ L₂ m := by
  obtain ⟨l, hl, rfl⟩ := exists_actY_of_mem_L₂ hX hx
  have hyl : (y : G) * l * (y : G)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (m.hyp.normal y.2) l).1 hl
  have := actY_mem_L₂ hX (y := y * l * y⁻¹) hyl
  rwa [map_mul, map_mul, map_inv] at this

theorem actY_mem_L₂' (hX : autI m.hyp.elem L ≤ stabSub (U' m) ⊓ stabSub (Z' m))
    (hcard : Nat.card (L₂ m) = 2520) (y : ↥Y) : actY m y ∈ L₂ m := by
  have hnorm := normalizer_eq_of_card_2520 (exp_Msec m) (card_Msec m) hcard
  have hy : actY m y ∈ Subgroup.normalizer (L₂ m : Set (MulAut (Msec m))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => actY_conj_mem_L₂ hX y hx, fun hx => ?_⟩
    have := actY_conj_mem_L₂ hX y⁻¹ hx
    simpa [map_inv, mul_assoc] using this
  rw [hnorm] at hy
  exact hy

end L2

section B42

theorem mem_Abar_iff {m : Main T Y L} {A : Subgroup G} (hAY : A ≤ Y)
    (hAs : autI m.hyp.elem A ≤ stabSub (U' m) ⊓ stabSub (Z' m)) {ψ : MulAut (Msec m)} :
    ψ ∈ autSec (autI m.hyp.elem A) (U' m) (Z' m) ↔ ∃ a : ↥Y, (a : G) ∈ A ∧ actY m a = ψ := by
  rw [mem_autSec_iff_secHom hAs]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, haA, hag⟩ := (mem_autI _).1 hg
    refine ⟨⟨a, hAY haA⟩, haA, ?_⟩
    show secHom (U' m) (Z' m) ⟨_, mem_stab m ⟨a, hAY haA⟩⟩ = secHom (U' m) (Z' m) g
    congr 1
    exact Subtype.ext hag
  · rintro ⟨a, haA, rfl⟩
    exact ⟨⟨_, mem_stab m a⟩, convI_mem_autI _ haA (m.hyp.YN a.2), rfl⟩

variable {m : Main T Y L} {KP : ∀ (Y : Type) [Group Y], Prop}

end B42

section PiRho

variable {m : Main T Y L}

noncomputable def πmap (hrange : ∀ y : ↥Y, actY m y ∈ L₂ m) (e : ↥(L₂ m) ≃* A7) : ↥Y →* A7 :=
  e.toMonoidHom.comp ((actY m).codRestrict (L₂ m) hrange)

noncomputable def ρmap (e : ↥(L₂ m) ≃* A7) : A7 →* MulAut (Msec m) :=
  (L₂ m).subtype.comp e.symm.toMonoidHom

theorem ρmap_πmap (hrange : ∀ y : ↥Y, actY m y ∈ L₂ m) (e : ↥(L₂ m) ≃* A7) (y : ↥Y) :
    ρmap e (πmap hrange e y) = actY m y := by
  show ((e.symm (e ⟨actY m y, hrange y⟩) : ↥(L₂ m)) : MulAut (Msec m)) = actY m y
  rw [MulEquiv.symm_apply_apply]

theorem ρmap_injective (e : ↥(L₂ m) ≃* A7) : Function.Injective (ρmap e) :=
  Subtype.val_injective.comp e.symm.injective

theorem πmap_surjective (hX : autI m.hyp.elem L ≤ stabSub (U' m) ⊓ stabSub (Z' m))
    (hrange : ∀ y : ↥Y, actY m y ∈ L₂ m) (e : ↥(L₂ m) ≃* A7) :
    Function.Surjective (πmap hrange e) := by
  intro a
  obtain ⟨y, -, hy⟩ := exists_actY_of_mem_L₂ hX (e.symm a).2
  refine ⟨y, ?_⟩
  show e ⟨actY m y, hrange y⟩ = a
  have : (⟨actY m y, hrange y⟩ : ↥(L₂ m)) = e.symm a := Subtype.ext hy
  rw [this, MulEquiv.apply_symm_apply]

theorem πmap_equiv (hrange : ∀ y : ↥Y, actY m y ∈ L₂ m) (e : ↥(L₂ m) ≃* A7) (y : ↥Y)
    (u u' : ↥(blockU L)) (h : (u' : G) = y * u * (y : G)⁻¹) :
    ρmap e (πmap hrange e y) (φeq m u) = φeq m u' := by
  rw [ρmap_πmap]
  exact actY_φeq m y u u' h

theorem πmap_ker (hrange : ∀ y : ↥Y, actY m y ∈ L₂ m) (e : ↥(L₂ m) ≃* A7) (y : ↥Y)
    (h : πmap hrange e y = 1) : (y : G) ∈ Subgroup.centralizer (VZ T Y : Set G) := by
  have h1 : actY m y = 1 := by rw [← ρmap_πmap hrange e y, h, map_one]
  exact m.centralizerU_le y.2 (centralizes_of_actY_eq_one m h1)

end PiRho

section Offender

theorem kleinRegular7_eq : kleinRegular7 = kleinP := by
  apply le_antisymm
  · rw [kleinRegular7, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact x7_mem
    · exact y7_mem
  · intro g hg
    have hg' : g ∈ kleinSet := hg
    simp only [kleinSet, Finset.mem_insert, Finset.mem_singleton] at hg'
    rcases hg' with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact Subgroup.subset_closure (Or.inl rfl)
    · exact Subgroup.subset_closure (Or.inr rfl)
    · exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))

theorem isKleinConj_of_altConjTo
    {P : Subgroup A7} (h : AltConjTo 7 P kleinRegular7) :
    IsKleinConj P := by
  obtain ⟨c, hc, hP⟩ := h
  refine ⟨⟨c, hc⟩, ?_⟩
  ext x
  rw [mem_conjSub]
  have h1 : (x : Equiv.Perm (Fin 7)) ∈ P.map (alternatingGroup (Fin 7)).subtype ↔ x ∈ P := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hconj : ∀ k : Equiv.Perm (Fin 7), (MulAut.conj c).toMonoidHom k = c * k * c⁻¹ :=
    fun k => rfl
  have h2 : (x : Equiv.Perm (Fin 7)) ∈ kleinRegular7.map (MulAut.conj c).toMonoidHom ↔
      c⁻¹ * (x : Equiv.Perm (Fin 7)) * c ∈ kleinRegular7 := by
    constructor
    · rintro ⟨k, hk, hkx⟩
      rw [hconj] at hkx
      have : c⁻¹ * (x : Equiv.Perm (Fin 7)) * c = k := by rw [← hkx]; group
      rwa [this]
    · intro hx
      refine ⟨c⁻¹ * x * c, hx, ?_⟩
      rw [hconj]
      group
  rw [← h1, hP, h2, kleinRegular7_eq]
  exact Iff.rfl

variable {m : Main T Y L}

theorem autI_le_stab {A : Subgroup G} (hAY : A ≤ Y) :
    autI m.hyp.elem A ≤ stabSub (U' m) ⊓ stabSub (Z' m) := by
  intro φ hφ
  obtain ⟨a, haA, rfl⟩ := (mem_autI _).1 hφ
  exact mem_stab m ⟨a, hAY haA⟩

omit [Finite G] in
theorem img_elem_abelian {π : ↥Y →* A7} {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    (∀ x ∈ img π A, ∀ y ∈ img π A, x * y = y * x) ∧ ∀ x ∈ img π A, x ^ 2 = 1 := by
  have := hA.1
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, haA, rfl⟩ := mem_img.1 hx
    obtain ⟨b, hbA, rfl⟩ := mem_img.1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (setLike_mul_comm haA hbA)
  · intro x hx
    obtain ⟨a, haA, rfl⟩ := mem_img.1 hx
    rw [← map_pow]
    have h1 : a ^ 2 = 1 := Subtype.ext (by simpa using hA.2 a haA)
    rw [h1, map_one]

variable (hrange : ∀ y : ↥Y, actY m y ∈ L₂ m) (e : ↥(L₂ m) ≃* A7)

include hrange

theorem img_eq_map {A : Subgroup G} (hAY : A ≤ Y) :
    img (πmap hrange e) A =
      ((autSec (autI m.hyp.elem A) (U' m) (Z' m)).subgroupOf (L₂ m)).map e.toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, haA, rfl⟩ := mem_img.1 hx
    refine ⟨⟨actY m a, hrange a⟩, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 ((mem_Abar_iff hAY (autI_le_stab hAY)).2 ⟨a, haA, rfl⟩)
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨a, haA, ha⟩ := (mem_Abar_iff hAY (autI_le_stab hAY)).1 (Subgroup.mem_subgroupOf.1 hψ)
    refine mem_img.2 ⟨a, haA, ?_⟩
    show e ⟨actY m a, hrange a⟩ = e ψ
    congr 1
    exact Subtype.ext ha

theorem card_Abar {A : Subgroup G} (hAY : A ≤ Y) :
    Nat.card ↥(autSec (autI m.hyp.elem A) (U' m) (Z' m)) = Nat.card ↥(img (πmap hrange e) A) := by
  rw [img_eq_map hrange e hAY, Subgroup.card_map_of_injective e.injective]
  have hle : autSec (autI m.hyp.elem A) (U' m) (Z' m) ≤ L₂ m := by
    intro ψ hψ
    obtain ⟨a, -, rfl⟩ := (mem_Abar_iff hAY (autI_le_stab hAY)).1 hψ
    exact hrange a
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm

theorem fixU_eq_fixV {A : Subgroup G} (hAY : A ≤ Y) :
    fixU (ρmap e) (img (πmap hrange e) A) = fixV (autSec (autI m.hyp.elem A) (U' m) (Z' m)) := by
  ext u
  rw [mem_fixU, mem_fixV]
  constructor
  · intro h ψ hψ
    obtain ⟨a, haA, rfl⟩ := (mem_Abar_iff hAY (autI_le_stab hAY)).1 hψ
    have := h (πmap hrange e a) (mem_img_of_mem a.2 haA)
    rwa [ρmap_πmap] at this
  · intro h g hg
    obtain ⟨a, haA, rfl⟩ := mem_img.1 hg
    rw [ρmap_πmap]
    exact h _ ((mem_Abar_iff hAY (autI_le_stab hAY)).2 ⟨a, haA, rfl⟩)

omit hrange in
theorem autI_inf_centSec_eq_bot {A : Subgroup G} (hAY : A ≤ Y) :
    autI m.hyp.elem A ⊓ centSec (U' m) (Z' m) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  obtain ⟨a, haA, rfl⟩ := (mem_autI _).1 hφ.1
  have hc := hφ.2
  have hcent : (a : G) ∈ Subgroup.centralizer (VZ T Y : Set G) := by
    apply m.centralizerU_le (hAY haA)
    intro u hu
    have hw : (IntMod.mk m.hyp.elem ⟨u, m.uV hu⟩ : V₀ m) ∈ U' m := hu
    have h1 := hc.2 _ hw
    rw [Z'_eq_bot, Subgroup.mem_bot, mul_inv_eq_one] at h1
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    exact h2
  rw [Subgroup.mem_bot]
  exact (convI_eq_one_iff _ a).2 hcent

end Offender

end CFSG.QuasithinUnique.L246.C123

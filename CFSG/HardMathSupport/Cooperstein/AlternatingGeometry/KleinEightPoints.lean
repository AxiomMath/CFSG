module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairFlipNormalizer
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFourModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.HardMathSupport.Cooperstein.Coordinator

namespace PairFlip

theorem wStab_flip {κ : Type*} [Fintype κ] [DecidableEq κ] {g : Perm (κ × Bool)} (hg : g ∈ wStab κ Bool) (z : κ × Bool) :
    g (z.1, !z.2) = ((g z).1, !(g z).2) := by
  have h1 : (g (z.1, !z.2)).1 = (g z).1 := (mem_wStab.1 hg _ _).2 rfl
  have h2 : g (z.1, !z.2) ≠ g z := by
    intro h
    have h3 : (!z.2) = z.2 := congrArg Prod.snd (g.injective h)
    revert h3
    cases z.2 <;> decide
  generalize g z = A at h1 h2 ⊢
  generalize g (z.1, !z.2) = B at h1 h2 ⊢
  obtain ⟨c, d⟩ := A
  obtain ⟨c', d'⟩ := B
  simp only at h1
  subst h1
  have : d' ≠ d := fun h => h2 (by rw [h])
  ext
  · rfl
  · cases d <;> cases d' <;> simp_all

theorem eq_or_flip {κ : Type*} {X Y : κ × Bool} (h : X.1 = Y.1) :
    Y = X ∨ Y = (X.1, !X.2) := by
  obtain ⟨a, b⟩ := X
  obtain ⟨c, d⟩ := Y
  simp only at h
  subst h
  cases b <;> cases d <;> simp

variable {κ : Type*}

theorem fst_eq_iff_of_flip {g : Perm (κ × Bool)}
    (hg : ∀ z, g (z.1, !z.2) = ((g z).1, !(g z).2)) (X Y : κ × Bool) :
    (g X).1 = (g Y).1 ↔ X.1 = Y.1 := by
  constructor
  · intro h
    rcases eq_or_flip h with e | e
    · have := g.injective e
      rw [this]
    · have e' : g Y = g (X.1, !X.2) := by rw [e, hg]
      have := g.injective e'
      rw [this]
  · intro h
    rcases eq_or_flip h with e | e
    · rw [e]
    · rw [e, hg]

end PairFlip

namespace KleinEight

open PairFlip

@[expose] noncomputable def E4 : Subgroup (Perm (Fin 4 × Bool)) :=
  (kleinFin4.comap (wStabAction (Fin 4))).map (wStab (Fin 4) Bool).subtype

theorem mem_E4 {e : Perm (Fin 4 × Bool)} :
    e ∈ E4 ↔ ∃ h : e ∈ wStab (Fin 4) Bool, wStabAction (Fin 4) ⟨e, h⟩ ∈ kleinFin4 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hk⟩
    exact ⟨⟨e, h⟩, hk, rfl⟩

theorem E4_le_wStab : E4 ≤ wStab (Fin 4) Bool := fun _ he => (mem_E4.1 he).1

theorem conj_mem_E4 {a e : Perm (Fin 4 × Bool)} (ha : a ∈ wStab (Fin 4) Bool) (he : e ∈ E4) :
    a * e * a⁻¹ ∈ E4 := by
  obtain ⟨h, hk⟩ := mem_E4.1 he
  refine mem_E4.2 ⟨mul_mem (mul_mem ha h) (inv_mem ha), ?_⟩
  have : (⟨a * e * a⁻¹, mul_mem (mul_mem ha h) (inv_mem ha)⟩ : ↥(wStab (Fin 4) Bool)) =
      ⟨a, ha⟩ * ⟨e, h⟩ * ⟨a, ha⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]
  exact (kleinFin4_normal.conj_mem _ hk _)

theorem isPGroup_E4 : IsPGroup 2 E4 := by
  have hK : IsPGroup 2 kleinFin4 := fun x => ⟨1, Subtype.ext (by
    simpa [pow_two] using kleinFin4_mul_self x.2)⟩
  have hker : IsPGroup 2 (wStabAction (Fin 4)).ker := by
    intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hg := g.2
    rw [MonoidHom.mem_ker] at hg
    have hfst : ∀ z : Fin 4 × Bool, (g.1.1 z).1 = z.1 := by
      intro z
      have := wStabAction_apply g.1 z
      rw [hg] at this
      exact this.symm
    have hflip := wStab_flip g.1.2
    have hmul : g.1.1 * g.1.1 = 1 := by
      apply Equiv.ext
      intro z
      rcases eq_or_flip (X := z) (Y := g.1.1 z) (hfst z).symm with e | e
      · have e' : (g.1.1) (g.1.1 z) = z := by rw [e]; exact e
        simpa [Perm.mul_apply] using e'
      · rw [Perm.mul_apply, Perm.one_apply, e, hflip, e]
        simp
    simpa [pow_two] using hmul
  exact ((hK.comap_of_ker_isPGroup (wStabAction (Fin 4)) hker).map (wStab (Fin 4) Bool).subtype)

theorem exists_E4_apply (x y : Fin 4 × Bool) : ∃ e ∈ E4, sign e = 1 ∧ e x = y := by
  obtain ⟨p, hp, hpxy⟩ := exists_mem_pTildeKlein_apply (Γ := Fin 0) x y
  refine ⟨p.1.1, mem_E4.2 ⟨p.2.1, ?_⟩, ?_, hpxy⟩
  · have := (mem_pTildeKlein_iff p).1 hp
    exact this.1
  · have h := p.2.2
    have hsub : p.1.2 = 1 := Subsingleton.elim _ _
    rw [hsub, map_one, mul_one] at h
    exact h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def embF (B : Finset ι) (hB : B.card = 4) :
    Fin 4 × Bool ≃ {z : ι × Bool // z.1 ∈ B} :=
  (Equiv.prodCongr (Fintype.equivFinOfCardEq (by simpa using hB) : {i // i ∈ B} ≃ Fin 4).symm
    (Equiv.refl Bool)).trans Equiv.prodSubtypeFstEquivSubtypeProd.symm

theorem embF_fst (B : Finset ι) (hB : B.card = 4) (y : Fin 4 × Bool) :
    ((embF B hB y) : ι × Bool) =
      (((Fintype.equivFinOfCardEq (by simpa using hB) : {i // i ∈ B} ≃ Fin 4).symm y.1 : ι), y.2) :=
  rfl

@[expose] noncomputable def ext (B : Finset ι) (hB : B.card = 4) : Perm (Fin 4 × Bool) →* Perm (ι × Bool) :=
  Equiv.Perm.extendDomainHom (embF B hB)

theorem ext_apply_embF (B : Finset ι) (hB : B.card = 4) (e : Perm (Fin 4 × Bool))
    (y : Fin 4 × Bool) : ext B hB e (embF B hB y : ι × Bool) = (embF B hB (e y) : ι × Bool) :=
  Equiv.Perm.extendDomain_apply_image e (embF B hB) y

theorem ext_apply_of_not_mem (B : Finset ι) (hB : B.card = 4) (e : Perm (Fin 4 × Bool))
    {z : ι × Bool} (hz : z.1 ∉ B) : ext B hB e z = z :=
  Equiv.Perm.extendDomain_apply_not_subtype e (embF B hB) (p := fun z : ι × Bool => z.1 ∈ B) hz

theorem sign_ext (B : Finset ι) (hB : B.card = 4) (e : Perm (Fin 4 × Bool)) :
    sign (ext B hB e) = sign e :=
  Equiv.Perm.sign_extendDomain e (embF B hB)

theorem exists_embF (B : Finset ι) (hB : B.card = 4) {z : ι × Bool} (hz : z.1 ∈ B) :
    ∃ y, (embF B hB y : ι × Bool) = z := by
  obtain ⟨y, hy⟩ := (embF B hB).surjective ⟨z, hz⟩
  exact ⟨y, congrArg Subtype.val hy⟩

theorem embF_flip (B : Finset ι) (hB : B.card = 4) (y : Fin 4 × Bool) :
    (embF B hB (y.1, !y.2) : ι × Bool) =
      ((embF B hB y : ι × Bool).1, !(embF B hB y : ι × Bool).2) := rfl

@[expose] noncomputable def U (B : Finset ι) (hB : B.card = 4) : Subgroup (Perm (ι × Bool)) :=
  (E4 ⊓ alternatingGroup (Fin 4 × Bool)).map (ext B hB)

theorem mem_U {B : Finset ι} {hB : B.card = 4} {u : Perm (ι × Bool)} :
    u ∈ U B hB ↔ ∃ e ∈ E4, sign e = 1 ∧ ext B hB e = u := by
  constructor
  · rintro ⟨e, ⟨he, he2⟩, rfl⟩
    exact ⟨e, he, mem_alternatingGroup.1 he2, rfl⟩
  · rintro ⟨e, he, hs, rfl⟩
    exact ⟨e, ⟨he, mem_alternatingGroup.2 hs⟩, rfl⟩

theorem isPGroup_U (B : Finset ι) (hB : B.card = 4) : IsPGroup 2 (U B hB) :=
  (isPGroup_E4.to_le inf_le_left).map _

theorem U_fix (B : Finset ι) (hB : B.card = 4) {u : Perm (ι × Bool)} (hu : u ∈ U B hB)
    {z : ι × Bool} (hz : z.1 ∉ B) : u z = z := by
  obtain ⟨e, -, -, rfl⟩ := mem_U.1 hu
  exact ext_apply_of_not_mem B hB e hz

theorem U_sign (B : Finset ι) (hB : B.card = 4) {u : Perm (ι × Bool)} (hu : u ∈ U B hB) :
    sign u = 1 := by
  obtain ⟨e, -, hs, rfl⟩ := mem_U.1 hu
  rw [sign_ext, hs]

theorem U_transitive (B : Finset ι) (hB : B.card = 4) {x y : ι × Bool} (hx : x.1 ∈ B)
    (hy : y.1 ∈ B) : ∃ u ∈ U B hB, u x = y := by
  obtain ⟨a, rfl⟩ := exists_embF B hB hx
  obtain ⟨b, rfl⟩ := exists_embF B hB hy
  obtain ⟨e, he, hs, heab⟩ := exists_E4_apply a b
  exact ⟨ext B hB e, mem_U.2 ⟨e, he, hs, rfl⟩, by rw [ext_apply_embF, heab]⟩

theorem U_flip (B : Finset ι) (hB : B.card = 4) {u : Perm (ι × Bool)} (hu : u ∈ U B hB)
    (z : ι × Bool) : u (z.1, !z.2) = ((u z).1, !(u z).2) := by
  obtain ⟨e, he, -, rfl⟩ := mem_U.1 hu
  by_cases hz : z.1 ∈ B
  · obtain ⟨y, rfl⟩ := exists_embF B hB hz
    rw [← embF_flip, ext_apply_embF, ext_apply_embF, wStab_flip (E4_le_wStab he) y, embF_flip]
  · rw [ext_apply_of_not_mem B hB e hz, ext_apply_of_not_mem B hB e (z := (z.1, !z.2)) hz]

theorem U_inv_mem (B : Finset ι) (hB : B.card = 4) {u : Perm (ι × Bool)} (hu : u ∈ U B hB) :
    u⁻¹ ∈ U B hB := inv_mem hu


theorem embF_fst_eq_iff (B : Finset ι) (hB : B.card = 4) (x y : Fin 4 × Bool) :
    (embF B hB x : ι × Bool).1 = (embF B hB y : ι × Bool).1 ↔ x.1 = y.1 := by
  rw [embF_fst, embF_fst]
  simp only [Subtype.val_inj]
  exact (Equiv.injective _).eq_iff

section Normalizer

variable {W : Subgroup (Perm (ι × Bool))}

theorem U_le_normalizer (hle : W ≤ J0 ι)
    (hD : ∀ i j, i ≠ j → tp i ∉ W → tp j ∉ W → tp i * tp j ∈ W)
    {B : Finset ι} (hB : B.card = 4) (hBT : B = outSet W ∨ B = (outSet W)ᶜ)
    {u : Perm (ι × Bool)} (hu : u ∈ U B hB) : u ∈ Subgroup.normalizer (W : Set _) := by
  have key : ∀ {v : Perm (ι × Bool)}, v ∈ U B hB → ∀ w ∈ W, v * w * v⁻¹ ∈ W := by
    intro v hv w hw
    have hwJ : w ∈ J0 ι := hle hw
    have hvflip := U_flip B hB hv
    have hcJ : (v * w * v⁻¹) * w⁻¹ ∈ J0 ι :=
      mul_mem (conj_mem_J0 hvflip hwJ) (inv_mem hwJ)
    set c := (v * w * v⁻¹) * w⁻¹ with hc
    have hsub : flipSet c ⊆ B := by
      intro i hi
      by_contra hiB
      rw [mem_flipSet] at hi
      apply hi
      have hy1 : (w⁻¹ (i, true)).1 = i := by
        rcases mem_J0.1 (inv_mem hwJ) (i, true) with e | e <;> simp [e]
      have hvy : v⁻¹ (w⁻¹ (i, true)) = w⁻¹ (i, true) :=
        U_fix B hB (U_inv_mem B hB hv) (by rw [hy1]; exact hiB)
      have h2 : w (w⁻¹ (i, true)) = (i, true) := by simp
      have h3 : v (i, true) = (i, true) := U_fix B hB hv hiB
      show v (w (v⁻¹ (w⁻¹ (i, true)))) = (i, true)
      rw [hvy, h2, h3]
    have hsign : sign c = 1 := by
      rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, U_sign B hB hv]
      simp
    have hev : Even (flipSet c ∩ outSet W).card := by
      rcases hBT with h | h
      · have : flipSet c ∩ outSet W = flipSet c := Finset.inter_eq_left.2 (h ▸ hsub)
        rw [this]; exact even_card_flipSet_of_sign hcJ hsign
      · have : flipSet c ∩ outSet W = ∅ := by
          ext i
          simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
          intro hi hi'
          have := hsub hi
          rw [h] at this
          exact (Finset.mem_compl.1 this) hi'
        rw [this]; simp
    have hcW : c ∈ W :=
      mem_of_even_flipSet (fun i hi => by_contra fun h => hi (mem_outSet.2 h))
        (fun i hi j hj hij => hD i j hij (mem_outSet.1 hi) (mem_outSet.1 hj)) _ c hcJ rfl hev
    have : v * w * v⁻¹ = c * w := by rw [hc]; group
    rw [this]
    exact W.mul_mem hcW hw
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw; exact key hu w hw
  · intro hw'
    have := key (U_inv_mem B hB hu) _ hw'
    simpa [mul_assoc] using this

theorem conj_mem_U (hle : W ≤ J0 ι)
    (hD : ∀ i j, i ≠ j → tp i ∉ W → tp j ∉ W → tp i * tp j ∈ W)
    (hT1 : (outSet W).card ≠ 1) {B : Finset ι} (hB : B.card = 4)
    (hBT : B = outSet W ∨ B = (outSet W)ᶜ) {g : Perm (ι × Bool)}
    (hg : g ∈ Subgroup.normalizer (W : Set _)) {u : Perm (ι × Bool)} (hu : u ∈ U B hB) :
    g * u * g⁻¹ ∈ U B hB := by
  have hflip := normalizer_flip hle hD hT1 hg
  have hmem : ∀ z : ι × Bool, z.1 ∈ B ↔ (g z).1 ∈ B := by
    intro z
    have h := normalizer_mem_outSet hle hD hT1 hg z
    rcases hBT with hB' | hB'
    · rw [hB']; exact h
    · rw [hB']; simp only [Finset.mem_compl]; exact not_congr h
  let p : ι × Bool → Prop := fun z => z.1 ∈ B
  have hp : ∀ z, p (g z) ↔ p z := fun z => (hmem z).symm
  let gsub : Perm {z : ι × Bool // p z} := g.subtypePerm hp
  let a : Perm (Fin 4 × Bool) := (embF B hB).permCongr.symm gsub
  have ha : ∀ y, (embF B hB (a y) : ι × Bool) = g (embF B hB y : ι × Bool) := by
    intro y
    have h1 : (embF B hB).permCongr a = gsub := Equiv.apply_symm_apply _ _
    have h2 := congrArg (fun f : Perm {z : ι × Bool // p z} => (f (embF B hB y) : ι × Bool)) h1
    simpa [Equiv.permCongr_apply, gsub] using h2
  have haw : a ∈ wStab (Fin 4) Bool := by
    refine mem_wStab.2 fun x y => ?_
    have e1 := fst_eq_iff_of_flip hflip (embF B hB x : ι × Bool) (embF B hB y : ι × Bool)
    rw [← ha x, ← ha y, embF_fst_eq_iff, embF_fst_eq_iff] at e1
    exact e1
  have hconj : ∀ e : Perm (Fin 4 × Bool),
      g * ext B hB e * g⁻¹ = ext B hB (a * e * a⁻¹) := by
    intro e
    apply Equiv.ext
    intro z
    by_cases hz : z.1 ∈ B
    · obtain ⟨y, rfl⟩ := exists_embF B hB hz
      have hginv : g⁻¹ (embF B hB y : ι × Bool) = (embF B hB (a⁻¹ y) : ι × Bool) := by
        have := ha (a⁻¹ y)
        rw [show a (a⁻¹ y) = y by simp] at this
        exact (Perm.inv_eq_iff_eq).2 this
      show g (ext B hB e (g⁻¹ (embF B hB y : ι × Bool))) = _
      rw [hginv, ext_apply_embF, ← ha, ext_apply_embF]
      rfl
    · rw [ext_apply_of_not_mem B hB _ hz]
      show g (ext B hB e (g⁻¹ z)) = z
      have hn : (g⁻¹ z).1 ∉ B := by
        intro h
        have := (hmem (g⁻¹ z)).1 h
        rw [show g (g⁻¹ z) = z by simp] at this
        exact hz this
      rw [ext_apply_of_not_mem B hB _ hn]
      simp
  obtain ⟨e0, he0, hs0, rfl⟩ := mem_U.1 hu
  rw [hconj]
  refine mem_U.2 ⟨a * e0 * a⁻¹, conj_mem_E4 haw he0, ?_, rfl⟩
  rw [map_mul, map_mul, map_inv, hs0]
  simp

end Normalizer

end KleinEight

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

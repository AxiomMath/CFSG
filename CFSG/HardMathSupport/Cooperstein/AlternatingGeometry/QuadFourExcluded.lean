module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTwoExcluded
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSplit
public import CFSG.HardMathSupport.Cooperstein.Proving.TwoPrimeSup

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm Subgroup

abbrev QΩ : Type := Fin 4 × Fin 4

@[expose] def V4 : Subgroup (Perm (Fin 4)) :=
  (alternatingGroup.kleinFour (Fin 4)).map (alternatingGroup (Fin 4)).subtype

theorem V4_eq_closure : V4 = Subgroup.closure
    {σ : Perm (Fin 4) | σ ∈ alternatingGroup (Fin 4) ∧ σ.cycleType = {2, 2}} := by
  unfold V4 alternatingGroup.kleinFour
  rw [MonoidHom.map_closure]
  congr 1
  ext σ
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨σ, h1⟩, h2, rfl⟩

theorem V4_le_alt : V4 ≤ alternatingGroup (Fin 4) := by
  rintro _ ⟨g, -, rfl⟩; exact g.2

theorem V4_conj (g : Perm (Fin 4)) {x : Perm (Fin 4)} (hx : x ∈ V4) : g * x * g⁻¹ ∈ V4 := by
  rw [V4_eq_closure] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨hy1, hy2⟩ := hy
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · have := mem_alternatingGroup.1 hy1
      rw [mem_alternatingGroup]
      simp [map_mul, map_inv, this]
    · rw [Equiv.Perm.cycleType_conj]
      exact hy2
  | one => simp
  | mul y z _ _ hy hz =>
    have := Subgroup.mul_mem _ hy hz
    simpa [mul_assoc] using this
  | inv y _ hy =>
    have := Subgroup.inv_mem _ hy
    convert this using 1
    group

theorem V4_sq (x : Perm (Fin 4)) (hx : x ∈ V4) : x ^ 2 = 1 := by
  obtain ⟨g, hg, rfl⟩ := hx
  have hK := alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
  have h2 := hK.exponent_two
  have : (⟨g, hg⟩ : ↥(alternatingGroup.kleinFour (Fin 4))) ^ 2 = 1 := by
    have h3 := Monoid.pow_exponent_eq_one (⟨g, hg⟩ : ↥(alternatingGroup.kleinFour (Fin 4)))
    rwa [h2] at h3
  have := congrArg (fun y : ↥(alternatingGroup.kleinFour (Fin 4)) =>
    ((y : alternatingGroup (Fin 4)) : Perm (Fin 4))) this
  simpa using this

@[expose] noncomputable def qBlk : ↥(wStab (Fin 4) (Fin 4)) →* Perm (Fin 4) where
  toFun σ := wBlockMap σ.1 σ.2
  map_one' := by refine Equiv.ext fun a => ?_; rfl
  map_mul' x y := by
    refine Equiv.ext fun a => ?_
    have h3 : wBlockMap (y.1 : Perm QΩ) y.2 a = (y.1 (a, 0)).1 := wBlockMap_apply y.2 (a, 0)
    have h1 : wBlockMap (x.1 : Perm QΩ) x.2 (y.1 (a, 0)).1 = (x.1 (y.1 (a, 0))).1 :=
      wBlockMap_apply x.2 _
    have hL : wBlockMap ((x * y).1 : Perm QΩ) (x * y).2 a = (x.1 (y.1 (a, 0))).1 :=
      wBlockMap_apply (x * y).2 (a, 0)
    show wBlockMap ((x * y).1 : Perm QΩ) (x * y).2 a =
      wBlockMap (x.1 : Perm QΩ) x.2 (wBlockMap (y.1 : Perm QΩ) y.2 a)
    rw [hL, h3, h1]

theorem qBlk_apply (σ : ↥(wStab (Fin 4) (Fin 4))) (p : QΩ) : qBlk σ p.1 = (σ.1 p).1 :=
  wBlockMap_apply σ.2 p

@[expose] noncomputable def TQ : Subgroup (Perm QΩ) :=
  ((V4.comap qBlk).map (wStab (Fin 4) (Fin 4)).subtype) ⊓ alternatingGroup QΩ

theorem mem_TQ {x : Perm QΩ} : x ∈ TQ ↔ ∃ hx : x ∈ wStab (Fin 4) (Fin 4),
    qBlk ⟨x, hx⟩ ∈ V4 ∧ x ∈ alternatingGroup QΩ := by
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, ha⟩
    exact ⟨y.2, hy, ha⟩
  · rintro ⟨hx, hv, ha⟩
    exact ⟨⟨⟨x, hx⟩, hv, rfl⟩, ha⟩

theorem conj_mem_TQ {σ x : Perm QΩ} (hσ : σ ∈ wStab (Fin 4) (Fin 4)) (hx : x ∈ TQ) :
    σ * x * σ⁻¹ ∈ TQ := by
  obtain ⟨hxs, hxv, hxa⟩ := mem_TQ.1 hx
  refine mem_TQ.2 ⟨mul_mem (mul_mem hσ hxs) (inv_mem hσ), ?_, ?_⟩
  · have : (⟨σ * x * σ⁻¹, mul_mem (mul_mem hσ hxs) (inv_mem hσ)⟩ : ↥(wStab (Fin 4) (Fin 4))) =
        ⟨σ, hσ⟩ * ⟨x, hxs⟩ * ⟨σ, hσ⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    exact V4_conj _ hxv
  · rw [mem_alternatingGroup] at hxa ⊢
    simp [map_mul, map_inv, hxa]

section QuadW

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]

theorem exists_wStab_form {n : Perm (ι × κ)} (hn : n ∈ wStab ι κ) :
    ∃ (π : Perm ι) (h : ι → Perm κ), ∀ i k, n (i, k) = (π i, h i k) := by
  refine ⟨wBlockMap n hn, fun i => Equiv.ofBijective (fun k => (n (i, k)).2)
    (Finite.injective_iff_bijective.1 ?_), fun i k => ?_⟩
  · intro k k' hkk
    have h1 : (n (i, k)).1 = (n (i, k')).1 := (hn (i, k) (i, k')).2 rfl
    exact congrArg Prod.snd (n.injective (Prod.ext h1 hkk))
  · exact Prod.ext (wBlockMap_apply hn (i, k)).symm rfl

theorem wStab_conj_wPermHom {n : Perm (ι × κ)} (hn : n ∈ wStab ι κ) (g : ι → Perm κ) :
    ∃ g' : ι → Perm κ, n * wPermHom ι κ g * n⁻¹ = wPermHom ι κ g' ∧
      ∃ (π : Perm ι) (h : ι → Perm κ), ∀ i, g' (π i) = h i * g i * (h i)⁻¹ := by
  obtain ⟨π, h, hform⟩ := exists_wStab_form hn
  refine ⟨fun j => h (π.symm j) * g (π.symm j) * (h (π.symm j))⁻¹, ?_, π, h, fun i => by simp⟩
  have hinv : ∀ (j : ι) (k' : κ), n⁻¹ (j, k') = (π.symm j, (h (π.symm j))⁻¹ k') := by
    intro j k'
    rw [Perm.inv_def, Equiv.symm_apply_eq, hform]
    simp
  ext ⟨j, k'⟩
  · simp [Perm.mul_apply, hinv, wPermHom_apply, hform]
  · simp [Perm.mul_apply, hinv, wPermHom_apply, hform]

end QuadW

section KW

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]

theorem conj_wFix_of_wStab {D : Subgroup (Perm κ)} (hD : D.Normal) {n x : Perm (ι × κ)}
    (hn : n ∈ wStab ι κ) (hx : x ∈ wFix D ι) : n * x * n⁻¹ ∈ wFix D ι := by
  obtain ⟨g, hgD, rfl⟩ := mem_wFix.1 hx
  obtain ⟨g', hg', π, h, hπ⟩ := wStab_conj_wPermHom hn g
  refine mem_wFix.2 ⟨g', fun j => ?_, hg'.symm⟩
  have hj := hπ (π.symm j)
  rw [Equiv.apply_symm_apply] at hj
  rw [hj]
  exact hD.conj_mem _ (hgD _) _

end KW

theorem hι4 : 2 ≤ Fintype.card (Fin 4) := by simp

@[expose] noncomputable def KQ : Subgroup (AltW (Fin 4) (Fin 4)) :=
  (wFix (alternatingGroup (Fin 4)) (Fin 4)).subgroupOf (alternatingGroup QΩ)

@[expose] noncomputable def WQ : Subgroup (AltW (Fin 4) (Fin 4)) :=
  (V4.comap (wAction wreathHyp_d8 hι4)).map (wN d8 (Fin 4)).subtype

@[expose] noncomputable def TQA : Subgroup (AltW (Fin 4) (Fin 4)) := TQ.subgroupOf (alternatingGroup QΩ)

theorem mem_KQ {x : AltW (Fin 4) (Fin 4)} :
    x ∈ KQ ↔ (x : Perm QΩ) ∈ wFix (alternatingGroup (Fin 4)) (Fin 4) := Iff.rfl

theorem mem_TQA {x : AltW (Fin 4) (Fin 4)} : x ∈ TQA ↔ (x : Perm QΩ) ∈ TQ := Iff.rfl

theorem wFix_le_wStab (D : Subgroup (Perm (Fin 4))) : wFix D (Fin 4) ≤ wStab (Fin 4) (Fin 4) := by
  intro σ hσ
  rw [mem_wStab]
  intro x y
  rw [wFix_apply_fst hσ, wFix_apply_fst hσ]

theorem qBlk_wFix {σ : Perm QΩ} (hσ : σ ∈ wFix (alternatingGroup (Fin 4)) (Fin 4)) :
    qBlk ⟨σ, wFix_le_wStab _ hσ⟩ = 1 := by
  refine Equiv.ext fun a => ?_
  have := qBlk_apply ⟨σ, wFix_le_wStab _ hσ⟩ (a, 0)
  rw [wFix_apply_fst hσ] at this
  exact this

theorem KQ_le_TQA : KQ ≤ TQA := by
  intro x hx
  have hx' : (x : Perm QΩ) ∈ wFix (alternatingGroup (Fin 4)) (Fin 4) := hx
  have hs : (x : Perm QΩ) ∈ wStab (Fin 4) (Fin 4) := wFix_le_wStab _ hx'
  refine mem_TQA.2 (mem_TQ.2 ⟨hs, ?_, x.2⟩)
  have := qBlk_wFix hx'
  rw [this]; exact V4.one_mem

theorem qBlk_eq_wAction (n : ↥(wN d8 (Fin 4))) :
    qBlk ⟨n.1.1, mem_wStab_of_mem_wN wreathHyp_d8 hι4 n.2⟩ = wAction wreathHyp_d8 hι4 n := by
  refine Equiv.ext fun a => ?_
  have h1 := qBlk_apply ⟨n.1.1, mem_wStab_of_mem_wN wreathHyp_d8 hι4 n.2⟩ (a, 0)
  have h2 := wAction_apply wreathHyp_d8 hι4 n (a, 0)
  exact h1.trans h2.symm

theorem WQ_le_TQA : WQ ≤ TQA := by
  rintro _ ⟨n, hn, rfl⟩
  have hs : ((n.1 : AltW (Fin 4) (Fin 4)) : Perm QΩ) ∈ wStab (Fin 4) (Fin 4) :=
    mem_wStab_of_mem_wN wreathHyp_d8 hι4 n.2
  refine mem_TQA.2 (mem_TQ.2 ⟨hs, ?_, n.1.2⟩)
  have := qBlk_eq_wAction n
  show qBlk ⟨((n.1 : AltW (Fin 4) (Fin 4)) : Perm QΩ), hs⟩ ∈ V4
  rw [this]; exact hn

theorem alt4_normal : (alternatingGroup (Fin 4)).Normal := inferInstance

theorem conj_KQ {x : AltW (Fin 4) (Fin 4)} (hx : (x : Perm QΩ) ∈ wStab (Fin 4) (Fin 4)) :
    ∀ k : AltW (Fin 4) (Fin 4), k ∈ KQ → x * k * x⁻¹ ∈ KQ := by
  intro k hk
  exact conj_wFix_of_wStab alt4_normal hx hk

theorem wStab_le_normalizer_KQ {x : AltW (Fin 4) (Fin 4)}
    (hx : (x : Perm QΩ) ∈ wStab (Fin 4) (Fin 4)) : x ∈ normalizer (KQ : Set (AltW (Fin 4) (Fin 4))) := by
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => conj_KQ hx k hk, fun hk => ?_⟩
  have hx' : ((x⁻¹ : AltW (Fin 4) (Fin 4)) : Perm QΩ) ∈ wStab (Fin 4) (Fin 4) := by
    have : ((x⁻¹ : AltW (Fin 4) (Fin 4)) : Perm QΩ) = (x : Perm QΩ)⁻¹ := rfl
    rw [this]; exact inv_mem hx
  have := conj_KQ hx' _ hk
  simpa [mul_assoc] using this

theorem exists_decomp_of_fix (y : AltW (Fin 4) (Fin 4)) (hy : ∀ p : QΩ, ((y : Perm QΩ) p).1 = p.1) :
    ∃ k ∈ KQ, ∃ w ∈ WQ, y = k * w := by
  obtain ⟨g, hg⟩ := (mem_range_wPermHom (ι := Fin 4) (κ := Fin 4)).2 hy
  set s : Perm (Fin 4) := swap 0 1 with hs
  have hsd : s ∈ d8 := by
    show ∀ x y : Fin 4, (s x).val / 2 = (s y).val / 2 ↔ x.val / 2 = y.val / 2
    decide
  have hsign : sign s = -1 := sign_swap (by decide)
  set c : Fin 4 → Perm (Fin 4) := fun i => if sign (g i) = -1 then s else 1 with hc
  have hcsign : ∀ i, sign (c i) = sign (g i) := by
    intro i
    by_cases h : sign (g i) = -1
    · simp [hc, h, hsign]
    · have h1 : sign (g i) = 1 := by
        rcases Int.units_eq_one_or (sign (g i)) with h' | h'
        · exact h'
        · exact absurd h' h
      simp [hc, h, h1]
  have hcd : ∀ i, c i ∈ d8 := by
    intro i; by_cases h : sign (g i) = -1
    · simp [hc, h, hsd]
    · simp [hc, h]
  have hyalt : sign (wPermHom (Fin 4) (Fin 4) g) = 1 := by
    have := mem_alternatingGroup.1 y.2
    rw [← hg] at this; exact this
  have hcalt : sign (wPermHom (Fin 4) (Fin 4) c) = 1 := by
    rw [sign_wPermHom] at hyalt ⊢
    simpa [hcsign] using hyalt
  let w₀ : AltW (Fin 4) (Fin 4) := ⟨wPermHom (Fin 4) (Fin 4) c, mem_alternatingGroup.2 hcalt⟩
  have hw₀R : w₀ ∈ wR d8 (Fin 4) := mem_wR.2 (mem_wFix.2 ⟨c, hcd, rfl⟩)
  have hw₀N : w₀ ∈ wN d8 (Fin 4) := Subgroup.le_normalizer hw₀R
  have hw₀A : wAction wreathHyp_d8 hι4 ⟨w₀, hw₀N⟩ = 1 := by
    refine Equiv.ext fun a => ?_
    have := wAction_apply wreathHyp_d8 hι4 ⟨w₀, hw₀N⟩ (a, 0)
    exact this.trans (by simp [w₀, wPermHom_apply])
  refine ⟨y * w₀⁻¹, ?_, w₀, ⟨⟨w₀, hw₀N⟩, by show wAction wreathHyp_d8 hι4 ⟨w₀, hw₀N⟩ ∈ V4; rw [hw₀A]; exact V4.one_mem, rfl⟩, by simp⟩
  show ((y * w₀⁻¹ : AltW (Fin 4) (Fin 4)) : Perm QΩ) ∈ wFix (alternatingGroup (Fin 4)) (Fin 4)
  refine mem_wFix.2 ⟨fun i => g i * (c i)⁻¹, fun i => ?_, ?_⟩
  · rw [mem_alternatingGroup]; simp [hcsign]
  · have : ((y * w₀⁻¹ : AltW (Fin 4) (Fin 4)) : Perm QΩ) =
        wPermHom (Fin 4) (Fin 4) g * (wPermHom (Fin 4) (Fin 4) c)⁻¹ := by
      show (y : Perm QΩ) * (w₀ : Perm QΩ)⁻¹ = _
      rw [← hg]
    rw [this, ← map_inv, ← map_mul]; rfl

theorem even_card_fin4 : Even (Fintype.card (Fin 4)) := by simp; decide

theorem TQA_le_sup : TQA ≤ KQ ⊔ WQ := by
  intro u hu
  obtain ⟨hus, huv, hua⟩ := mem_TQ.1 (mem_TQA.1 hu)
  set τ : Perm (Fin 4) := qBlk ⟨(u : Perm QΩ), hus⟩ with hτ
  let ℓ : AltW (Fin 4) (Fin 4) := ⟨wLift τ, mem_alternatingGroup.2 (wLift_sign even_card_fin4 τ)⟩
  have hℓN : ℓ ∈ wN d8 (Fin 4) := wLift_mem_wN even_card_fin4 τ
  have hℓs : (ℓ : Perm QΩ) ∈ wStab (Fin 4) (Fin 4) := wLift_mem_wStab τ
  have hℓA : wAction wreathHyp_d8 hι4 ⟨ℓ, hℓN⟩ = τ := by
    refine Equiv.ext fun a => ?_
    have := wAction_apply wreathHyp_d8 hι4 ⟨ℓ, hℓN⟩ (a, 0)
    exact this.trans rfl
  have hℓW : ℓ ∈ WQ := ⟨⟨ℓ, hℓN⟩, by show wAction wreathHyp_d8 hι4 ⟨ℓ, hℓN⟩ ∈ V4; rw [hℓA]; exact huv, rfl⟩
  set y : AltW (Fin 4) (Fin 4) := ℓ⁻¹ * u with hy
  have hyfix : ∀ p : QΩ, ((y : Perm QΩ) p).1 = p.1 := by
    intro p
    have h1 : ((u : Perm QΩ) p).1 = τ p.1 := by
      have := qBlk_apply ⟨(u : Perm QΩ), hus⟩ p
      exact this.symm
    have h2 : ((ℓ⁻¹ : AltW (Fin 4) (Fin 4)) : Perm QΩ) = wLift τ⁻¹ := by
      show ((ℓ : Perm QΩ))⁻¹ = _
      exact wLift_inv τ
    show (((ℓ⁻¹ : AltW (Fin 4) (Fin 4)) : Perm QΩ) ((u : Perm QΩ) p)).1 = p.1
    rw [h2]
    show (τ⁻¹ ((u : Perm QΩ) p).1) = p.1
    rw [h1]; simp
  obtain ⟨k, hk, w, hw, hkw⟩ := exists_decomp_of_fix y hyfix
  have hu' : u = ℓ * (k * w) := by
    rw [← hkw, hy]; simp
  have : u = (ℓ * k * ℓ⁻¹) * (ℓ * w) := by
    rw [hu']; group
  rw [this]
  exact Subgroup.mul_mem_sup (conj_KQ hℓs k hk) (WQ.mul_mem hℓW hw)

theorem KQ_sup_WQ_eq : KQ ⊔ WQ = TQA := le_antisymm (sup_le KQ_le_TQA WQ_le_TQA) TQA_le_sup

theorem isSolvable_pi_const' {ι T : Type*} [Group T] (hT : Group.IsSolvable T) :
    Group.IsSolvable (ι → T) := by
  obtain ⟨n, hn⟩ := hT.solvable
  refine ⟨n, ?_⟩
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  funext i
  have := map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom (fun _ : ι => T) i) n
    (Subgroup.mem_map_of_mem _ hg)
  rw [hn, Subgroup.mem_bot] at this
  exact this

theorem wFix_alt_le_alt : wFix (alternatingGroup (Fin 4)) (Fin 4) ≤ alternatingGroup QΩ := by
  rintro σ hσ
  obtain ⟨g, hg, rfl⟩ := mem_wFix.1 hσ
  rw [mem_alternatingGroup, sign_wPermHom]
  exact Finset.prod_eq_one fun i _ => mem_alternatingGroup.1 (hg i)

theorem solvable_KQ : Group.IsSolvable ↥KQ := by
  have h1 : Group.IsSolvable (Fin 4 → alternatingGroup (Fin 4)) := isSolvable_pi_const' a4_solvable
  let f : (Fin 4 → alternatingGroup (Fin 4)) →* Perm QΩ :=
    (wPermHom (Fin 4) (Fin 4)).comp
      (MonoidHom.pi fun i => (alternatingGroup (Fin 4)).subtype.comp (Pi.evalMonoidHom _ i))
  have hf : ∀ g, f g ∈ wFix (alternatingGroup (Fin 4)) (Fin 4) := fun g =>
    mem_wFix.2 ⟨fun i => (g i : Perm (Fin 4)), fun i => (g i).2, rfl⟩
  let f' : (Fin 4 → alternatingGroup (Fin 4)) →* ↥(wFix (alternatingGroup (Fin 4)) (Fin 4)) :=
    f.codRestrict _ hf
  have hs : Function.Surjective f' := by
    rintro ⟨σ, hσ⟩
    obtain ⟨g, hg, rfl⟩ := mem_wFix.1 hσ
    exact ⟨fun i => ⟨g i, hg i⟩, Subtype.ext rfl⟩
  have h2 : Group.IsSolvable ↥(wFix (alternatingGroup (Fin 4)) (Fin 4)) :=
    Group.isSolvable_of_surjective hs
  have e := Subgroup.subgroupOfEquivOfLe wFix_alt_le_alt
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem isPGroup_comap_of_ker {G H : Type*} [Group G] [Group H] (f : G →* H) (V : Subgroup H)
    (hV : IsPGroup 2 V) (hk : IsPGroup 2 f.ker) : IsPGroup 2 (V.comap f) := by
  intro g
  obtain ⟨a, ha⟩ := hV ⟨f g, g.2⟩
  have h1 : f ((g : G) ^ (2 ^ a)) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val ha
  obtain ⟨b, hb⟩ := hk ⟨(g : G) ^ (2 ^ a), h1⟩
  refine ⟨a + b, ?_⟩
  apply Subtype.ext
  have := congrArg Subtype.val hb
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
  rw [pow_add, pow_mul]
  exact this

theorem isPGroup_V4 : IsPGroup 2 V4 := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa [pow_two] using V4_sq g.1 g.2

theorem isPGroup_WQ : IsPGroup 2 WQ :=
  (isPGroup_comap_of_ker _ V4 isPGroup_V4 (isPGroup_ker_wAction wreathHyp_d8 hι4)).map _

theorem WQ_le_normalizer_KQ : WQ ≤ normalizer (KQ : Set (AltW (Fin 4) (Fin 4))) := by
  rintro _ ⟨n, hn, rfl⟩
  exact wStab_le_normalizer_KQ (mem_wStab_of_mem_wN wreathHyp_d8 hι4 n.2)

theorem solvable_TQA : Group.IsSolvable ↥TQA := by
  rw [← KQ_sup_WQ_eq]
  exact solvable_sup_of_normalizes WQ_le_normalizer_KQ solvable_KQ isPGroup_WQ

set_option maxRecDepth 100000 in
theorem even_sq_mem_d8 : ∀ σ : Perm (Fin 4), sign σ = 1 → σ ^ 2 = 1 →
    ∀ x y : Fin 4, (σ x).val / 2 = (σ y).val / 2 ↔ x.val / 2 = y.val / 2 := by
  decide

theorem V4_le_d8 : V4 ≤ d8 := fun x hx =>
  mem_d8.2 (even_sq_mem_d8 x (mem_alternatingGroup.1 (V4_le_alt hx)) (V4_sq x hx))

@[expose] noncomputable def KQ2 : Subgroup (AltW (Fin 4) (Fin 4)) :=
  (wFix V4 (Fin 4)).subgroupOf (alternatingGroup QΩ)

theorem wFix_mono {D D' : Subgroup (Perm (Fin 4))} (h : D ≤ D') :
    wFix D (Fin 4) ≤ wFix D' (Fin 4) := Subgroup.map_mono (fun g hg i _ => h (hg i trivial))

theorem KQ2_le_WQ : KQ2 ≤ WQ := by
  intro x hx
  have h1 : (x : Perm QΩ) ∈ wFix d8 (Fin 4) := wFix_mono V4_le_d8 hx
  have hR : x ∈ wR d8 (Fin 4) := mem_wR.2 h1
  have hN : x ∈ wN d8 (Fin 4) := Subgroup.le_normalizer hR
  refine ⟨⟨x, hN⟩, ?_, rfl⟩
  show wAction wreathHyp_d8 hι4 ⟨x, hN⟩ ∈ V4
  have : wAction wreathHyp_d8 hι4 ⟨x, hN⟩ = 1 := by
    refine Equiv.ext fun a => ?_
    have := wAction_apply wreathHyp_d8 hι4 ⟨x, hN⟩ (a, 0)
    exact this.trans (wFix_apply_fst h1 _)
  rw [this]; exact V4.one_mem

theorem index_KQ2_KQ : (KQ2.subgroupOf KQ).index = 81 := by
  let f : (Fin 4 → alternatingGroup (Fin 4)) →* Perm QΩ :=
    (wPermHom (Fin 4) (Fin 4)).comp
      (MonoidHom.pi fun i => (alternatingGroup (Fin 4)).subtype.comp (Pi.evalMonoidHom _ i))
  have hfK : ∀ g, f g ∈ wFix (alternatingGroup (Fin 4)) (Fin 4) := fun g =>
    mem_wFix.2 ⟨fun i => (g i : Perm (Fin 4)), fun i => (g i).2, rfl⟩
  let f₂ : (Fin 4 → alternatingGroup (Fin 4)) →* ↥KQ :=
    ((f.codRestrict (alternatingGroup QΩ) (fun g => wFix_alt_le_alt (hfK g))).codRestrict KQ
      (fun g => hfK g))
  have hs : Function.Surjective f₂ := by
    rintro ⟨⟨σ, hσa⟩, hσ⟩
    obtain ⟨g, hg, hgσ⟩ := mem_wFix.1 (show σ ∈ wFix (alternatingGroup (Fin 4)) (Fin 4) from hσ)
    refine ⟨fun i => ⟨g i, hg i⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    exact hgσ
  have hc : (KQ2.subgroupOf KQ).comap f₂ =
      Subgroup.pi Set.univ (fun _ : Fin 4 => alternatingGroup.kleinFour (Fin 4)) := by
    ext g
    simp only [mem_comap, mem_subgroupOf, Subgroup.mem_pi, Set.mem_univ, true_implies]
    show (f g) ∈ wFix V4 (Fin 4) ↔ _
    constructor
    · intro h i
      obtain ⟨g', hg', hgg⟩ := mem_wFix.1 h
      have : g' = fun i => (g i : Perm (Fin 4)) := wPermHom_injective hgg
      have hi := hg' i
      rw [this] at hi
      obtain ⟨y, hy, hyg⟩ := hi
      have : y = g i := Subtype.ext hyg
      rw [← this]; exact hy
    · intro h
      exact mem_wFix.2 ⟨fun i => (g i : Perm (Fin 4)), fun i => ⟨g i, h i, rfl⟩, rfl⟩
  rw [← index_comap_of_surjective _ hs, hc, index_pi]
  have hK := alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
  have h12 := alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hmul := Subgroup.card_mul_index (alternatingGroup.kleinFour (Fin 4))
  rw [hK.card_four, h12] at hmul
  have h3 : (alternatingGroup.kleinFour (Fin 4)).index = 3 := by omega
  simp [h3]

theorem odd_index_WQ : ¬ 2 ∣ (WQ.subgroupOf TQA).index := by
  have h1 : (WQ.subgroupOf (KQ ⊔ WQ)).index = ((WQ ⊓ KQ).subgroupOf KQ).index :=
    index_sup_eq WQ_le_normalizer_KQ
  rw [← KQ_sup_WQ_eq, h1]
  have hle : KQ2.subgroupOf KQ ≤ (WQ ⊓ KQ).subgroupOf KQ := fun x hx =>
    ⟨KQ2_le_WQ hx, x.2⟩
  have hd := Subgroup.index_dvd_of_le hle
  rw [index_KQ2_KQ] at hd
  intro h2
  have := Nat.dvd_trans h2 hd
  omega

theorem eq_one_of_pow_two_three {H : Type*} [Group H] {x : H} (h2 : x ^ 2 = 1) (h3 : x ^ 3 = 1) :
    x = 1 := by
  have : x = x ^ 3 * (x ^ 2)⁻¹ := by group
  rw [this, h3, h2]; simp

theorem eq_one_of_sq_pow_three {H : Type*} [Group H] {x : H} (h2 : x ^ 2 = 1) {m : ℕ}
    (hm : x ^ (3 ^ m) = 1) : x = 1 := by
  have hmod : 3 ^ m % 2 = 1 := by rw [Nat.pow_mod]; simp
  have hpos : 0 < 3 ^ m := by positivity
  obtain ⟨t, ht⟩ : ∃ t, 3 ^ m = 2 * t + 1 := ⟨(3 ^ m - 1) / 2, by omega⟩
  rw [ht, pow_succ, pow_mul, h2, one_pow, one_mul] at hm
  exact hm

theorem noNormalThree_TQA : ∀ R : Subgroup (AltW (Fin 4) (Fin 4)), R ≤ TQA →
    (∀ b ∈ TQA, ∀ r ∈ R, b * r * b⁻¹ ∈ R) → (∀ r ∈ R, ∃ m : ℕ, r ^ (3 ^ m) = 1) → R = ⊥ := by
  intro R hRT hn h3
  by_contra hne
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  obtain ⟨j, hc3, hc1⟩ := exists_order_three hr1' (h3 r hr)
  set c : AltW (Fin 4) (Fin 4) := r ^ (3 ^ j) with hc
  have hcR : c ∈ R := R.pow_mem hr _
  obtain ⟨hcs, hcv, -⟩ := mem_TQ.1 (mem_TQA.1 (hRT hcR))
  have hblk : qBlk ⟨(c : Perm QΩ), hcs⟩ = 1 := by
    have h2 := V4_sq _ hcv
    have h3' : (qBlk ⟨(c : Perm QΩ), hcs⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨(c : Perm QΩ), hcs⟩ : ↥(wStab (Fin 4) (Fin 4))) ^ 3 = 1 := by
        apply Subtype.ext
        have := congrArg (fun y : AltW (Fin 4) (Fin 4) => (y : Perm QΩ)) hc3
        simpa using this
      rw [this, map_one]
    exact eq_one_of_pow_two_three h2 h3'
  have hfix : ∀ p : QΩ, ((c : Perm QΩ) p).1 = p.1 := by
    intro p
    have := qBlk_apply ⟨(c : Perm QΩ), hcs⟩ p
    rw [hblk] at this
    exact this.symm
  obtain ⟨g, hg⟩ := (mem_range_wPermHom (ι := Fin 4) (κ := Fin 4)).2 hfix
  have hg3 : g ^ 3 = 1 := by
    apply wPermHom_injective (ι := Fin 4) (κ := Fin 4)
    rw [map_pow, hg, map_one]
    have := congrArg (fun y : AltW (Fin 4) (Fin 4) => (y : Perm QΩ)) hc3
    simpa using this
  have hg1 : g ≠ 1 := by
    intro h
    apply hc1
    apply Subtype.ext
    rw [← hg, h, map_one]; rfl
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hg1
  have hgi3 : g i ^ 3 = 1 := by
    have := congrFun hg3 i
    simpa using this
  obtain ⟨a, ha, h2, h1⟩ := perm4_three_witness (g i) hi hgi3
  set x₀' : Fin 4 → Perm (Fin 4) := Pi.mulSingle i a with hx₀'
  have hx₀'sign : ∀ j, sign (x₀' j) = 1 := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa [hx₀'] using ha
    · simp [hx₀', Pi.mulSingle_eq_of_ne hj]
  have hx₀alt : sign (wPermHom (Fin 4) (Fin 4) x₀') = 1 := by
    rw [sign_wPermHom]; exact Finset.prod_eq_one fun j _ => hx₀'sign j
  let x₀ : AltW (Fin 4) (Fin 4) := ⟨wPermHom (Fin 4) (Fin 4) x₀', mem_alternatingGroup.2 hx₀alt⟩
  have hx₀K : x₀ ∈ KQ :=
    mem_KQ.2 (mem_wFix.2 ⟨x₀', fun j => mem_alternatingGroup.2 (hx₀'sign j), rfl⟩)
  have hx₀T : x₀ ∈ TQA := KQ_le_TQA hx₀K
  have hw : c * (x₀ * c * x₀⁻¹)⁻¹ ∈ R := R.mul_mem hcR (R.inv_mem (hn x₀ hx₀T c hcR))
  set v : Fin 4 → Perm (Fin 4) := g * (x₀' * g * x₀'⁻¹)⁻¹ with hv
  have hwv : (((c * (x₀ * c * x₀⁻¹)⁻¹ : AltW (Fin 4) (Fin 4)) : Perm QΩ)) =
      wPermHom (Fin 4) (Fin 4) v := by
    show (c : Perm QΩ) * ((x₀ : Perm QΩ) * (c : Perm QΩ) * (x₀ : Perm QΩ)⁻¹)⁻¹ = _
    rw [← hg, hv]
    show _ = wPermHom (Fin 4) (Fin 4) (g * (x₀' * g * x₀'⁻¹)⁻¹)
    simp only [map_mul, map_inv]
    rfl
  have hvi : v i = g i * (a * g i * a⁻¹)⁻¹ := by
    simp [hv, hx₀']
  have hvj : ∀ j, j ≠ i → v j = 1 := by
    intro j hj
    simp [hv, hx₀', Pi.mulSingle_eq_of_ne hj]
  have hv2 : v ^ 2 = 1 := by
    funext j
    by_cases hj : j = i
    · subst hj; simpa [hvi] using h2
    · simp [hvj j hj]
  have hv1 : v ≠ 1 := by
    intro h
    have := congrFun h i
    rw [hvi] at this
    exact h1 (by simpa using this)
  have hw2 : (c * (x₀ * c * x₀⁻¹)⁻¹) ^ 2 = 1 := by
    apply Subtype.ext
    have : ((((c * (x₀ * c * x₀⁻¹)⁻¹) ^ 2 : AltW (Fin 4) (Fin 4)) : Perm QΩ)) =
        wPermHom (Fin 4) (Fin 4) (v ^ 2) := by
      rw [map_pow, ← hwv]; simp
    rw [this, hv2, map_one]; rfl
  obtain ⟨m, hm⟩ := h3 _ hw
  have hw1 := eq_one_of_sq_pow_three hw2 hm
  apply hv1
  apply wPermHom_injective (ι := Fin 4) (κ := Fin 4)
  rw [← hwv, hw1, map_one]; rfl

theorem exists_TQA_not_wN : ∃ t ∈ TQA, t ∉ wN d8 (Fin 4) := by
  set c3 : Perm (Fin 4) := swap 0 1 * swap 1 2 with hc3
  have hc3alt : sign c3 = 1 := by
    rw [hc3, map_mul, sign_swap (by decide), sign_swap (by decide)]; decide
  have hc3d8 : c3 ∉ d8 := by
    intro h
    have := mem_d8.1 h 0 1
    revert this
    simp [hc3, swap_apply_def]
  set x' : Fin 4 → Perm (Fin 4) := Pi.mulSingle 0 c3 with hx'
  have hx'sign : ∀ j, sign (x' j) = 1 := by
    intro j
    by_cases hj : j = 0
    · subst hj; simpa [hx'] using hc3alt
    · simp [hx', Pi.mulSingle_eq_of_ne hj]
  have hxalt : sign (wPermHom (Fin 4) (Fin 4) x') = 1 := by
    rw [sign_wPermHom]; exact Finset.prod_eq_one fun j _ => hx'sign j
  let t : AltW (Fin 4) (Fin 4) := ⟨wPermHom (Fin 4) (Fin 4) x', mem_alternatingGroup.2 hxalt⟩
  have htK : t ∈ KQ := mem_KQ.2 (mem_wFix.2 ⟨x', fun j => mem_alternatingGroup.2 (hx'sign j), rfl⟩)
  refine ⟨t, KQ_le_TQA htK, fun htN => ?_⟩
  have hker : (⟨t, htN⟩ : ↥(wN d8 (Fin 4))) ∈ (wAction wreathHyp_d8 hι4).ker := by
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun a => ?_
    have := wAction_apply wreathHyp_d8 hι4 ⟨t, htN⟩ (a, 0)
    exact this.trans (by simp [t, wPermHom_apply, hx'])
  obtain ⟨g', hg'd, hg'⟩ := mem_wFix.1 (mem_wFix_of_mem_ker wreathHyp_d8 hι4 hker)
  have : g' = x' := wPermHom_injective hg'
  apply hc3d8
  have := hg'd 0
  rw [‹g' = x'›] at this
  simpa [hx'] using this

theorem WQ_conj_wN {n : AltW (Fin 4) (Fin 4)} (hn : n ∈ wN d8 (Fin 4)) {w : AltW (Fin 4) (Fin 4)}
    (hw : w ∈ WQ) : n * w * n⁻¹ ∈ WQ := by
  obtain ⟨m, hm, rfl⟩ := hw
  let n' : ↥(wN d8 (Fin 4)) := ⟨n, hn⟩
  refine ⟨n' * m * n'⁻¹, ?_, rfl⟩
  show wAction wreathHyp_d8 hι4 (n' * m * n'⁻¹) ∈ V4
  rw [map_mul, map_mul, map_inv]
  exact V4_conj _ hm

open CFSG.AGLEmbedding (Asc81bHyp IsTwoPrimeComponent barM)

@[expose] noncomputable def comapEquiv {M A : Type*} [Group M] [Group A] (ψ : M ≃* A)
    (T : Subgroup A) : ↥(T.comap ψ.toMonoidHom) ≃* ↥T :=
  (ψ.subgroupMap (T.comap ψ.toMonoidHom)).trans (MulEquiv.subgroupCongr
    (Subgroup.map_comap_eq_self_of_surjective ψ.surjective _))

theorem quadFour_false {G : Type} [Group G] [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsTwoPrimeComponent X L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hLB : SolvableSylowNormalizer X S) (D : QuadBlockDataAct X S L 4) : False := by
  obtain ⟨ψ, hψN, hact⟩ := D
  set T : Subgroup ↥(barM X L) := TQA.comap ψ.toMonoidHom with hT
  set eT := comapEquiv ψ TQA with heT
  have hNL : barM X (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM X L := barM_mono inf_le_right
  have hSbar : ∀ y ∈ barM X S, y ∈ barM X (Subgroup.normalizer (S : Set G) ⊓
      Subgroup.normalizer (L : Set G)) := by
    intro y hy
    obtain ⟨x, hxX, hxS, rfl⟩ := mem_barM_iff.1 hy
    exact mem_barM_iff.2 ⟨x, hxX, ⟨Subgroup.le_normalizer hxS, hSL hxS⟩, rfl⟩
  have hnorm : ∀ y ∈ barM X S, ∀ l l' : ↥(barM X L),
      (l' : ↥X ⧸ CFSG.pCore 2 ↥X) = y * l * y⁻¹ → l ∈ T → l' ∈ T := by
    intro y hy l l' hll' hl
    obtain ⟨σ, hσ, hσl⟩ := hact y (hSbar y hy)
    have h1 := hσl l l' hll'
    have h2 : ((ψ l' : AltW (Fin 4) (Fin 4)) : Perm QΩ) ∈ TQ := by
      rw [h1]; exact conj_mem_TQ hσ hl
    exact h2
  have hsolv : Group.IsSolvable ↥T := by
    have := solvable_TQA
    exact Group.isSolvable_of_isSolvable_injective (f := eT.toMonoidHom) eT.injective
  have hodd : ¬ 2 ∣ (((barM X (S ⊓ L)).subgroupOf (barM X L)).subgroupOf T).index := by
    set VT : Subgroup ↥(barM X L) := WQ.comap ψ.toMonoidHom with hVT
    have hVT_T : VT ≤ T := fun v hv => WQ_le_TQA hv
    have hpc := Proving.barM_inf_eq_pCoreOf_barM hA hL
    have hVN : ∀ v' ∈ VT, v' ∈ ((barM X (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
        (barM X L)) := by
      intro v' hv'
      obtain ⟨n, -, hn⟩ := (show ψ v' ∈ WQ from hv')
      have h1 : ψ v' ∈ wN d8 (Fin 4) := by rw [← hn]; exact n.2
      rw [← hψN] at h1
      obtain ⟨n', hn', hnv⟩ := h1
      have : n' = v' := ψ.injective hnv
      rw [← this]; exact hn'
    have hVT_P : VT ≤ (barM X (S ⊓ L)).subgroupOf (barM X L) := by
      intro v hv
      show (v : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ barM X (S ⊓ L)
      rw [hpc]
      have hApG : IsPGroup 2 (VT.map (barM X L).subtype) :=
        (isPGroup_WQ.comap_of_injective ψ.toMonoidHom ψ.injective).map _
      refine le_pCoreOf_of_normalized (A := VT.map (barM X L).subtype) ?_ ?_ hApG ⟨v, hv, rfl⟩
      · rintro _ ⟨v', hv', rfl⟩
        exact hVN v' hv'
      · rintro k hk _ ⟨v', hv', rfl⟩
        have hkL : k ∈ barM X L := hNL hk
        have hk' : (⟨k, hkL⟩ : ↥(barM X L)) ∈ ((barM X (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
            (barM X L)) := hk
        have h1 : ψ ⟨k, hkL⟩ ∈ wN d8 (Fin 4) := by
          rw [← hψN]; exact ⟨_, hk', rfl⟩
        refine ⟨⟨k, hkL⟩ * v' * ⟨k, hkL⟩⁻¹, ?_, rfl⟩
        show ψ (⟨k, hkL⟩ * v' * ⟨k, hkL⟩⁻¹) ∈ WQ
        rw [map_mul, map_mul, map_inv]
        exact WQ_conj_wN h1 hv'
    have hsub : VT.subgroupOf T ≤ ((barM X (S ⊓ L)).subgroupOf (barM X L)).subgroupOf T :=
      fun t ht => hVT_P ht
    have hdvd := Subgroup.index_dvd_of_le hsub
    have hc : (WQ.subgroupOf TQA).comap eT.toMonoidHom = VT.subgroupOf T := by
      ext t
      simp only [mem_comap, mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      exact Iff.rfl
    have h3 : (VT.subgroupOf T).index = (WQ.subgroupOf TQA).index := by
      rw [← hc, index_comap_of_surjective _ (by exact eT.surjective)]
    rw [h3] at hdvd
    intro h2
    exact odd_index_WQ (Nat.dvd_trans h2 hdvd)
  have hT3 : ∀ R : Subgroup ↥(barM X L), R ≤ T → (∀ b ∈ T, ∀ r ∈ R, b * r * b⁻¹ ∈ R) →
      (∀ r ∈ R, ∃ m : ℕ, r ^ (3 ^ m) = 1) → R = ⊥ := by
    intro R hRT hn h3
    have h := noNormalThree_TQA (R.map ψ.toMonoidHom) (by
      rintro _ ⟨r, hr, rfl⟩; exact hRT hr) (by
      rintro b hb _ ⟨r, hr, rfl⟩
      have hb' : ψ.symm b ∈ T := by
        show ψ (ψ.symm b) ∈ TQA
        simpa using hb
      refine ⟨ψ.symm b * r * (ψ.symm b)⁻¹, hn _ hb' r hr, ?_⟩
      simp) (by
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨m, hm⟩ := h3 r hr
      exact ⟨m, by rw [← map_pow]; simp [hm]⟩)
    rw [eq_bot_iff]
    intro r hr
    have : ψ r ∈ R.map ψ.toMonoidHom := ⟨r, hr, rfl⟩
    rw [h] at this
    have h1 : ψ r = 1 := Subgroup.mem_bot.1 this
    have : r = 1 := ψ.injective (by rw [h1, map_one])
    rw [this]; exact Subgroup.one_mem _
  have hres := blockTransfer_iso hA hSL T hnorm hsolv hodd hT3 hLB
  obtain ⟨t, htT, htN⟩ := exists_TQA_not_wN
  have htT' : ψ.symm t ∈ T := by
    show ψ (ψ.symm t) ∈ TQA
    simpa using htT
  have hmem := hres _ htT'
  apply htN
  rw [← hψN]
  refine ⟨ψ.symm t, ?_, by simp⟩
  exact hmem

open CFSG CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.AGLEmbedding (IsWeakSBlock)

theorem quadFourExcluded_of_lemmaB (hB : SolvableSylowNormalizerAll) :
    QuadFourExcluded := by
  intro G _ _ X S L hX hA hL hSL h
  have hA' := CFSG.HardMathSupport.Cooperstein.Coordinator.asc81bHyp_sup hA
    hL.toIsTwoPrimeComponent hSL
  have hLc := CFSG.HardMathSupport.Cooperstein.Proving.isTwoPrimeComponent_sup
    hL.toIsTwoPrimeComponent hA.twoRadical.1 hA.twoRadical.isPGroup hSL
  have hXk := CFSG.HardMathSupport.Cooperstein.Coordinator.isKGroup_sup hX hA
    hL.toIsTwoPrimeComponent
  exact quadFour_false hA' hLc hSL (hB G (L ⊔ S) S hXk hA') h.1

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

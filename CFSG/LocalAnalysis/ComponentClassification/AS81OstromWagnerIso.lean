module

public import CFSG.LocalAnalysis.ComponentClassification.AS81OstromWagnerCoord
public import CFSG.LocalAnalysis.ComponentClassification.AS81OstromWagnerModel
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquares
import all CFSG.Fischer.F4

public section

namespace CFSG.ComponentClassification.AS81.OstromWagner

open CFSG.Fischer CFSG.ComponentClassification.WittDesign Equiv

theorem val_some_zero_mk : ∀ x y : Fin 4, val (some 0) ((⟨x⟩ : F4), (⟨y⟩ : F4)) = ⟨y⟩ := by
  decide

theorem val_rA : ∀ x y : Fin 4,
    val (some 1) ((⟨x⟩ : F4), (⟨y⟩ : F4)) = ⟨latinSq rA x y⟩ := by
  decide

theorem val_rB : ∀ x y : Fin 4,
    val (some F4.ω) ((⟨x⟩ : F4), (⟨y⟩ : F4)) = ⟨latinSq rB x y⟩ := by
  decide

theorem val_rC : ∀ x y : Fin 4,
    val (some (F4.ω * F4.ω)) ((⟨x⟩ : F4), (⟨y⟩ : F4)) = ⟨latinSq rC x y⟩ := by
  decide

theorem latinSq_succ (r : Fin 3 → Perm (Fin 4)) (i : Fin 3) (y : Fin 4) :
    latinSq r i.succ y = r i y := by
  have h : ((i.succ : Fin 4) : ℕ) ≠ 0 := by
    rw [Fin.val_succ]
    exact Nat.succ_ne_zero _
  rw [latinSq, dite_eq_right h]
  congr 2

theorem exists_other_two : ∀ yc : Fin 4, yc ≠ 0 → ∃ y₃ y₄ : Fin 4, y₃ ≠ 0 ∧ y₄ ≠ 0 ∧ y₃ ≠ yc ∧
    y₄ ≠ yc ∧ y₃ ≠ y₄ ∧ ∀ y, y = 0 ∨ y = yc ∨ y = y₃ ∨ y = y₄ := by
  decide

theorem iff_mem_agLines {P : Type} {lines : Set (Set P)} (hA : IsAffinePlane P lines)
    (hne : ∀ ℓ ∈ lines, ℓ.Nonempty) (e : P ≃ F4 × F4) (cls : Option F4 → Set P)
    (crd : Option F4 → P → Fin 4)
    (hT1 : ∀ s p q, crd s p = crd s q ↔ par lines (cls s) p = par lines (cls s) q)
    (hT2 : ∀ s p, val s (e p) = ⟨crd s p⟩) (hT3 : ∀ s, cls s ∈ lines)
    (hT4 : ∀ ℓ ∈ lines, ∃ s, Par (cls s) ℓ) (ℓ : Set P) :
    ℓ ∈ lines ↔ (e : P → F4 × F4) '' ℓ ∈ agLines := by
  have hlevel : ∀ s p, par lines (cls s) p = {q | crd s q = crd s p} := by
    intro s p
    ext q
    rw [Set.mem_ofPred_eq, hT1, eq_comm, hA.par_eq_par_iff (hT3 s)]
  have himage : ∀ s p, (e : P → F4 × F4) '' par lines (cls s) p = lineSet (s, ⟨crd s p⟩) := by
    intro s p
    ext z
    rw [hlevel, mem_lineSet]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [hT2, show crd s q = crd s p from hq]
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      have h := hT2 s (e.symm z)
      rw [e.apply_symm_apply] at h
      exact F4.mk.inj (h.symm.trans hz)
  constructor
  · intro hℓ
    obtain ⟨s, hs⟩ := hT4 ℓ hℓ
    obtain ⟨p, hp⟩ := hne ℓ hℓ
    rw [hA.eq_par (hT3 s) hℓ hp hs, himage]
    exact ⟨_, rfl⟩
  · rintro ⟨⟨s, k⟩, hk⟩
    obtain ⟨z, hz⟩ := exists_val_eq s k
    have h := himage s (e.symm z)
    have hk' : (⟨crd s (e.symm z)⟩ : F4) = k := by rw [← hT2, e.apply_symm_apply, hz]
    rw [hk'] at h
    have hℓ : ℓ = par lines (cls s) (e.symm z) :=
      (Set.image_injective.2 e.injective) (hk.symm.trans h.symm)
    rw [hℓ]
    exact hA.par_mem (hT3 s) _

section Squares

variable {P : Type} [Nonempty P] {lines : Set (Set P)} {o : P} {a b c : Set P}
  {lab : P → Fin 4} (hA : IsAffinePlane P lines) (hF : AffFrame lines o a b c)
  (hL : Labelling a o lab) {pt : Fin 4 → Fin 4 → P}
  (hptX : ∀ x y, cX lines a b c lab (pt x y) = x) (hptY : ∀ x y, cZ lines a lab b (pt x y) = y)
include hA hF hL hptX hptY

theorem cZ_pt_zero {d : Set P} (hd : d ∈ lines) (hda : ¬Par d a) (y : Fin 4) :
    cZ lines a lab d (pt 0 y) = y := by
  have hmem : pt 0 y ∈ a := (cX_eq_zero_iff hA hF hL).1 (hptX 0 y)
  rw [cZ_of_mem_a hA hF hd hda hmem, ← cZ_of_mem_a (lab := lab) hA hF hF.hb hF.hba hmem]
  exact hptY 0 y

theorem cZ_c_pt_zero (x : Fin 4) : cZ lines a lab c (pt x 0) = x := by
  have hmem : pt x 0 ∈ b := (cZ_eq_zero_iff hA hF hL hF.hb hF.hba hF.ob).1 (hptY x 0)
  rw [← cX_of_mem_b hA hF hmem]
  exact hptX x 0

theorem exists_latinSq {d : Set P} (hd : d ∈ lines) (hda : ¬Par d a) :
    ∃ r : Fin 3 → Perm (Fin 4), latinSq r = fun x y => cZ lines a lab d (pt x y) := by
  have hrow : ∀ x : Fin 4, Function.Injective fun y => cZ lines a lab d (pt x y) := by
    intro x y y' h
    have h1 := eq_of_cX_eq_of_cZ_eq hA hF hL hd hda ((hptX x y).trans (hptX x y').symm) h
    rw [← hptY x y, ← hptY x y', h1]
  refine ⟨fun i => Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (hrow i.succ)), ?_⟩
  funext x y
  by_cases hx : x = 0
  · subst hx
    rw [cZ_pt_zero hA hF hL hptX hptY hd hda]
    simp [latinSq]
  · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hx
    rw [latinSq_succ]
    rfl

theorem columnsInj_cZ {d : Set P} (hd : d ∈ lines) (hda : ¬Par d a) (hdb : ¬Par d b) :
    ColumnsInj fun x y => cZ lines a lab d (pt x y) := by
  intro y x x' h
  have h1 := eq_of_cZ_eq_of_cZ_eq hA hF hL hF.hb hF.hba hd hda (fun h => hdb h.symm)
    ((hptY x y).trans (hptY x' y).symm) h
  rw [← hptX x y, ← hptX x' y, h1]

theorem orth_cZ {d d' : Set P} (hd : d ∈ lines) (hda : ¬Par d a) (hd' : d' ∈ lines)
    (hda' : ¬Par d' a) (hdd' : ¬Par d d') :
    Orth (fun x y => cZ lines a lab d (pt x y)) (fun x y => cZ lines a lab d' (pt x y)) := by
  intro x y x' y' h h'
  have h1 := eq_of_cZ_eq_of_cZ_eq hA hF hL hd hda hd' hda' hdd' h h'
  exact ⟨by rw [← hptX x y, ← hptX x' y', h1], by rw [← hptY x y, ← hptY x' y', h1]⟩

omit hptY in
theorem pt_one_ne (y : Fin 4) : pt 1 y ≠ o := by
  intro h
  have h1 := hptX 1 y
  rw [h, (cX_eq_zero_iff hA hF hL).2 hF.oa] at h1
  exact absurd h1 (by decide)

theorem ln_pt_one_injective {y y' : Fin 4} (h : ln lines o (pt 1 y) = ln lines o (pt 1 y')) :
    y = y' := by
  by_contra hne
  have hpt : pt 1 y ≠ pt 1 y' := fun h' => hne (by rw [← hptY 1 y, ← hptY 1 y', h'])
  obtain ⟨hℓ, hoℓ, hyℓ⟩ := hA.ln_spec (pt_one_ne hA hF hL hptX y).symm
  obtain ⟨-, -, hy'ℓ⟩ := hA.ln_spec (pt_one_ne hA hF hL hptX y').symm
  rw [← h] at hy'ℓ
  have hpar : par lines a (pt 1 y) = par lines a (pt 1 y') :=
    (cX_eq_cX_iff hA hF hL).1 ((hptX 1 y).trans (hptX 1 y').symm)
  have hy'm : pt 1 y' ∈ par lines a (pt 1 y) := (hA.par_eq_par_iff hF.ha).1 hpar
  have hm := hA.eq_of_mem hℓ (hA.par_mem hF.ha (pt 1 y)) hpt hyℓ hy'ℓ (hA.mem_par hF.ha _) hy'm
  rw [hm] at hoℓ
  have h1 := (cX_eq_cX_iff hA hF hL).2 ((hA.par_eq_par_iff hF.ha).2 hoℓ)
  rw [hptX, (cX_eq_zero_iff hA hF hL).2 hF.oa] at h1
  exact absurd h1 (by decide)

omit hptY in
theorem not_par_ln_pt_one (y : Fin 4) : ¬Par (ln lines o (pt 1 y)) a := by
  obtain ⟨-, hoℓ, hyℓ⟩ := hA.ln_spec (pt_one_ne hA hF hL hptX y).symm
  refine not_par_of_mem (fun h => ?_) hoℓ hF.oa
  have h1 := (cX_eq_zero_iff hA hF hL).2 (h ▸ hyℓ)
  rw [hptX] at h1
  exact absurd h1 (by decide)

theorem exists_eq_ln_pt_one {D : Set P} (hD : D ∈ lines) (hoD : o ∈ D) (hDa : D ≠ a) :
    ∃ y, D = ln lines o (pt 1 y) := by
  have hDa' : ¬Par D a := not_par_of_mem hDa hoD hF.oa
  have hm : ¬Par D (par lines a (pt 1 0)) := fun h =>
    hDa' (hA.par_trans hD (hA.par_mem hF.ha _) hF.ha h (hA.par_par hF.ha _).symm)
  obtain ⟨x, hxD, hxm⟩ := exists_mem_of_not_par hm
  have hx1 : cX lines a b c lab x = 1 := by
    rw [← hptX 1 0]
    exact (cX_eq_cX_iff hA hF hL).2 ((hA.par_eq_par_iff hF.ha).2 hxm).symm
  have hxpt : pt 1 (cZ lines a lab b x) = x := by
    by_contra hne
    apply hne
    refine eq_of_cX_eq_of_cZ_eq hA hF hL hF.hb hF.hba ?_ (hptY _ _)
    rw [hptX, hx1]
  refine ⟨cZ lines a lab b x, ?_⟩
  rw [hxpt]
  refine hA.eq_ln (fun h => ?_) hD hoD hxD
  rw [← h, (cX_eq_zero_iff hA hF hL).2 hF.oa] at hx1
  exact absurd hx1 (by decide)

end Squares

theorem exists_equiv_agLines {P : Type} [Finite P]
    {lines : Set (Set P)} (hA : IsAffinePlane P lines) (h16 : Nat.card P = 16) :
    ∃ e : P ≃ F4 × F4, ∀ ℓ : Set P, ℓ ∈ lines ↔ (e : P → F4 × F4) '' ℓ ∈ agLines := by
  classical
  obtain ⟨x₀, y₀, hxy₀⟩ :=
    (Finite.one_lt_card_iff_nontrivial.1 (by omega : 1 < Nat.card P)).exists_pair_ne
  have : Nonempty P := ⟨x₀⟩
  obtain ⟨o, a, b, c, hF⟩ := exists_affFrame hA ⟨x₀, y₀, hxy₀⟩
  obtain ⟨lab, hL⟩ := exists_labelling hA hF h16
  set X := cX lines a b c lab with hX
  set Z := cZ lines a lab with hZ
  have hinj : Function.Injective fun p => (X p, Z b p) := fun p q h =>
    eq_of_cX_eq_of_cZ_eq hA hF hL hF.hb hF.hba (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hbij : Function.Bijective fun p => (X p, Z b p) := hinj.bijective_of_nat_card_le (by
    rw [h16, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin])
  set E := Equiv.ofBijective _ hbij with hE
  set pt : Fin 4 → Fin 4 → P := fun x y => E.symm (x, y) with hpt
  have hptX : ∀ x y, X (pt x y) = x := fun x y => congrArg Prod.fst (E.apply_symm_apply (x, y))
  have hptY : ∀ x y, Z b (pt x y) = y := fun x y =>
    congrArg Prod.snd (E.apply_symm_apply (x, y))
  have hpt_eq : ∀ p, pt (X p) (Z b p) = p := fun p => E.symm_apply_apply p
  set ℓ : Fin 4 → Set P := fun y => ln lines o (pt 1 y) with hℓdef
  have hℓ : ∀ y, ℓ y ∈ lines ∧ o ∈ ℓ y ∧ pt 1 y ∈ ℓ y := fun y =>
    hA.ln_spec (pt_one_ne hA hF hL hptX y).symm
  have hℓa : ∀ y, ¬Par (ℓ y) a := not_par_ln_pt_one hA hF hL hptX
  have hℓpar : ∀ y y', y ≠ y' → ¬Par (ℓ y) (ℓ y') := fun y y' h =>
    not_par_of_mem (fun h' => h (ln_pt_one_injective hA hF hL hptX hptY h')) (hℓ y).2.1
      (hℓ y').2.1
  have hℓ0 : ℓ 0 = b := by
    have hmem : pt 1 0 ∈ b := (cZ_eq_zero_iff hA hF hL hF.hb hF.hba hF.ob).1 (hptY 1 0)
    exact (hA.eq_ln (pt_one_ne hA hF hL hptX 0).symm hF.hb hF.ob hmem).symm
  obtain ⟨yc, hyc⟩ : ∃ yc, Z c (pt 1 yc) = 0 := by
    have hinj1 : Function.Injective fun y => Z c (pt 1 y) := fun y y' h => by
      have h1 := eq_of_cX_eq_of_cZ_eq hA hF hL hF.hc hF.hca
        ((hptX 1 y).trans (hptX 1 y').symm) h
      rw [← hptY 1 y, ← hptY 1 y', h1]
    exact (Finite.injective_iff_surjective.1 hinj1) 0
  have hℓc : ℓ yc = c := by
    have hmem : pt 1 yc ∈ c := (cZ_eq_zero_iff hA hF hL hF.hc hF.hca hF.oc).1 hyc
    exact (hA.eq_ln (pt_one_ne hA hF hL hptX yc).symm hF.hc hF.oc hmem).symm
  have hyc0 : yc ≠ 0 := by
    rintro rfl
    have h : Z c (pt 1 0) = 1 := cZ_c_pt_zero hA hF hL hptX hptY 1
    rw [hyc] at h
    exact absurd h (by decide)
  obtain ⟨y₃, y₄, h30, h40, h3c, h4c, h34, hall⟩ := exists_other_two yc hyc0
  obtain ⟨r₂, hr₂⟩ := exists_latinSq hA hF hL hptX hptY hF.hc hF.hca
  obtain ⟨r₃, hr₃⟩ := exists_latinSq hA hF hL hptX hptY (hℓ y₃).1 (hℓa y₃)
  obtain ⟨r₄, hr₄⟩ := exists_latinSq hA hF hL hptX hptY (hℓ y₄).1 (hℓa y₄)
  have h₂ : ∀ x : Fin 3, r₂ x 0 = x.succ := by
    intro x
    rw [← latinSq_succ, hr₂]
    exact cZ_c_pt_zero hA hF hL hptX hptY x.succ
  have h3b : ¬Par (ℓ y₃) b := hℓ0 ▸ hℓpar y₃ 0 h30
  have h4b : ¬Par (ℓ y₄) b := hℓ0 ▸ hℓpar y₄ 0 h40
  have hc3 : ¬Par c (ℓ y₃) := hℓc ▸ hℓpar yc y₃ (Ne.symm h3c)
  have hc4 : ¬Par c (ℓ y₄) := hℓc ▸ hℓpar yc y₄ (Ne.symm h4c)
  have hcol₂ : ColumnsInj (latinSq r₂) := by
    rw [hr₂]
    exact columnsInj_cZ hA hF hL hptX hptY hF.hc hF.hca hF.hcb
  have hcol₃ : ColumnsInj (latinSq r₃) := by
    rw [hr₃]
    exact columnsInj_cZ hA hF hL hptX hptY (hℓ y₃).1 (hℓa y₃) h3b
  have hcol₄ : ColumnsInj (latinSq r₄) := by
    rw [hr₄]
    exact columnsInj_cZ hA hF hL hptX hptY (hℓ y₄).1 (hℓa y₄) h4b
  have h₂₃ : Orth (latinSq r₂) (latinSq r₃) := by
    rw [hr₂, hr₃]
    exact orth_cZ hA hF hL hptX hptY hF.hc hF.hca (hℓ y₃).1 (hℓa y₃) hc3
  have h₂₄ : Orth (latinSq r₂) (latinSq r₄) := by
    rw [hr₂, hr₄]
    exact orth_cZ hA hF hL hptX hptY hF.hc hF.hca (hℓ y₄).1 (hℓa y₄) hc4
  have h₃₄ : Orth (latinSq r₃) (latinSq r₄) := by
    rw [hr₃, hr₄]
    exact orth_cZ hA hF hL hptX hptY (hℓ y₃).1 (hℓa y₃) (hℓ y₄).1 (hℓa y₄) (hℓpar y₃ y₄ h34)
  have hmols := mols_classification r₂ r₃ r₄ h₂ hcol₂ hcol₃ hcol₄ h₂₃ h₂₄ h₃₄
  have hrA : ∀ x y, Z c (pt x y) = latinSq rA x y := by
    intro x y
    rcases hmols with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [← h2, hr₂]
  obtain ⟨yω, yω2, hyω, hrB, hrC⟩ : ∃ yω yω2 : Fin 4,
      ((yω = y₃ ∧ yω2 = y₄) ∨ (yω = y₄ ∧ yω2 = y₃)) ∧
      (∀ x y, Z (ℓ yω) (pt x y) = latinSq rB x y) ∧
      (∀ x y, Z (ℓ yω2) (pt x y) = latinSq rC x y) := by
    rcases hmols with ⟨-, h3, h4⟩ | ⟨-, h3, h4⟩
    · exact ⟨y₃, y₄, Or.inl ⟨rfl, rfl⟩, fun x y => by rw [← h3, hr₃],
        fun x y => by rw [← h4, hr₄]⟩
    · exact ⟨y₄, y₃, Or.inr ⟨rfl, rfl⟩, fun x y => by rw [← h4, hr₄],
        fun x y => by rw [← h3, hr₃]⟩
  set yOf : F4 → Fin 4 := fun l =>
    if l = 0 then 0 else if l = 1 then yc else if l = F4.ω then yω else yω2 with hyOf
  have hy0 : yOf 0 = 0 := ite_eq_left rfl
  have hy1 : yOf 1 = yc := (ite_eq_right (by decide)).trans (ite_eq_left rfl)
  have hyω' : yOf F4.ω = yω :=
    (ite_eq_right (by decide)).trans ((ite_eq_right (by decide)).trans (ite_eq_left rfl))
  have hyω2' : yOf (F4.ω * F4.ω) = yω2 :=
    (ite_eq_right (by decide)).trans ((ite_eq_right (by decide)).trans
      (ite_eq_right (by decide)))
  set cls : Option F4 → Set P := fun s => s.elim a fun l => ℓ (yOf l) with hcls
  set crd : Option F4 → P → Fin 4 := fun s => s.elim X fun l => Z (ℓ (yOf l)) with hcrd
  set fin4 : Fin 4 ≃ F4 := ⟨F4.mk, F4.code, fun _ => rfl, fun _ => rfl⟩ with hfin4
  set e : P ≃ F4 × F4 := E.trans (Equiv.prodCongr fin4 fin4) with he
  have hT1 : ∀ s p q, crd s p = crd s q ↔ par lines (cls s) p = par lines (cls s) q := by
    rintro (_ | l) p q
    · exact cX_eq_cX_iff hA hF hL
    · exact cZ_eq_cZ_iff hA hF hL (hℓ _).1 (hℓa _)
  have hT3 : ∀ s, cls s ∈ lines := by
    rintro (_ | l)
    · exact hF.ha
    · exact (hℓ _).1
  have hT2 : ∀ s p, val s (e p) = ⟨crd s p⟩ := by
    rintro (_ | l) p
    · rfl
    · show val (some l) ((⟨X p⟩ : F4), (⟨Z b p⟩ : F4)) = ⟨Z (ℓ (yOf l)) p⟩
      conv_rhs => rw [← hpt_eq p]
      generalize X p = x
      generalize Z b p = y
      rcases F4_cases l with rfl | rfl | rfl | rfl
      · rw [hy0, hℓ0, hptY, val_some_zero_mk]
      · rw [hy1, hℓc, hrA, val_rA]
      · rw [hyω', hrB, val_rB]
      · rw [hyω2', hrC, val_rC]
  have hT4 : ∀ m ∈ lines, ∃ s, Par (cls s) m := by
    intro m hm
    have hD := hA.par_mem hm o
    have hoD := hA.mem_par hm o
    have hpar : Par (par lines m o) m := (hA.par_par hm o).symm
    by_cases hDa : par lines m o = a
    · refine ⟨none, ?_⟩
      show Par a m
      rw [← hDa]
      exact hpar
    obtain ⟨y, hy⟩ := exists_eq_ln_pt_one hA hF hL hptX hptY hD hoD hDa
    obtain ⟨l, hl⟩ : ∃ l, yOf l = y := by
      rcases hall y with rfl | rfl | rfl | rfl
      · exact ⟨0, hy0⟩
      · exact ⟨1, hy1⟩
      · rcases hyω with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact ⟨F4.ω, hyω'.trans h1⟩
        · exact ⟨F4.ω * F4.ω, hyω2'.trans h2⟩
      · rcases hyω with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact ⟨F4.ω * F4.ω, hyω2'.trans h2⟩
        · exact ⟨F4.ω, hyω'.trans h1⟩
    refine ⟨some l, ?_⟩
    show Par (ℓ (yOf l)) m
    rw [hl, ← show ln lines o (pt 1 y) = ℓ y from rfl, ← hy]
    exact hpar
  have hne : ∀ m ∈ lines, Set.Nonempty m := by
    intro m hm
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    subst hemp
    obtain ⟨n, -, hu⟩ := hA.parallel ∅ hm o (Set.notMem_empty o)
    have h1 := hu a ⟨hF.ha, hF.oa, Set.empty_disjoint _⟩
    have h2 := hu b ⟨hF.hb, hF.ob, Set.empty_disjoint _⟩
    exact hF.hab (Or.inl (h1.trans h2.symm))
  exact ⟨e, iff_mem_agLines hA hne e cls crd hT1 hT2 hT3 hT4⟩

end CFSG.ComponentClassification.AS81.OstromWagner

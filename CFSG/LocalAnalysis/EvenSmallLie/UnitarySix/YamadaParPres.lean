module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParPresCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParGamma
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSU

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Subgroup

theorem pow_mul_eq_one_of_involutions {Γ : Type*} [Group Γ] {Z : Subgroup Γ}
    (hZc : Z ≤ center Γ) (hZo : Odd (Nat.card Z)) {p q : Γ} (hp : p * p = 1) (hq : q * q = 1)
    {m : ℕ} (hm : (p * q) ^ m ∈ Z) : (p * q) ^ m = 1 := by
  set w := p * q
  have hinv : p * w * p⁻¹ = w⁻¹ := by
    have hp' : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
    have hq' : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
    rw [hp', mul_inv_rev, hp', hq']
    calc p * (p * q) * p = (p * p) * q * p := by group
      _ = q * p := by rw [hp, one_mul]
  have h1 : p * w ^ m * p⁻¹ = (w ^ m)⁻¹ := by
    rw [← conj_pow, hinv, inv_pow]
  have h2 : p * w ^ m * p⁻¹ = w ^ m := by
    rw [Subgroup.mem_center_iff.mp (hZc hm) p, mul_inv_cancel_right]
  have h4 : w ^ m = (w ^ m)⁻¹ := h2.symm.trans h1
  have h3 : w ^ m * w ^ m = 1 := by
    calc w ^ m * w ^ m = w ^ m * (w ^ m)⁻¹ := by rw [← h4]
      _ = 1 := mul_inv_cancel _
  exact eq_of_pow_two_pow hZo hm Z.one_mem 1 (by rw [pow_one, sq, h3, one_pow])

section Pres


@[expose] noncomputable def tSU (a : ℕ) : SU42b := ⟨wordGL (uPresGenW a), wordGL_mem _⟩

theorem coe_tSU (a : ℕ) : ((tSU a : GL (Fin 8) (ZMod 2)) : Mat8) = toMat 8 8 (tBitsOf a) :=
  coe_wordGL _

end Pres

@[expose] def prodWord {G : Type*} [Monoid G] (g : ℕ → G) (w : List ℕ) : G := (w.map g).prod

theorem lift_mk_uRelWord {G : Type*} [Group G] (g : Fin 5 → G) (r : List ℕ × List ℕ × ℕ) :
    FreeGroup.lift g (FreeGroup.mk (uRelWord r)) =
      (prodWord (fun a => g (Fin.ofNat 5 a)) r.1 * prodWord (fun a => g (Fin.ofNat 5 a)) r.2.1) ^
        r.2.2 := by
  rw [FreeGroup.lift_mk, uRelWord, List.map_map]
  simp only [Function.comp_def, Bool.cond_true]
  rw [List.map_flatten, List.map_replicate, List.prod_flatten, List.map_replicate,
    List.prod_replicate, List.map_append, List.prod_append]
  rfl

@[expose] def IsConjWord (w : List ℕ) : Prop :=
  (∃ a < 5, w = [a]) ∨ ∃ a < 5, ∃ b < 5, w = [a, b, a]

@[expose] def isConjWordB : List ℕ → Bool
  | [a] => a < 5
  | [a, b, c] => a < 5 && b < 5 && a == c
  | _ => false

theorem isConjWord_of_B {w : List ℕ} (h : isConjWordB w = true) : IsConjWord w := by
  match w, h with
  | [a], h => exact Or.inl ⟨a, by simpa [isConjWordB] using h, rfl⟩
  | [a, b, c], h =>
    simp only [isConjWordB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨ha, hb⟩, rfl⟩ := h
    exact Or.inr ⟨a, ha, b, hb, rfl⟩

theorem specs_shapeB : uPresSpecs.all (fun r => isConjWordB r.1 && isConjWordB r.2.1) = true := by
  decide

theorem isConjWord_specs : ∀ r ∈ uPresSpecs, IsConjWord r.1 ∧ IsConjWord r.2.1 := by
  intro r hr
  have h := List.all_eq_true.mp specs_shapeB r hr
  simp only [Bool.and_eq_true] at h
  exact ⟨isConjWord_of_B h.1, isConjWord_of_B h.2⟩

theorem prodWord_mul_self_of_isConjWord {G : Type*} [Group G] {g : ℕ → G}
    (hg : ∀ a < 5, g a * g a = 1) {w : List ℕ} (hw : IsConjWord w) :
    prodWord g w * prodWord g w = 1 := by
  rcases hw with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl⟩
  · simp [prodWord, hg a ha]
  · simp only [prodWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    calc g a * (g b * g a) * (g a * (g b * g a)) = g a * (g b * (g a * g a) * g b) * g a := by group
      _ = 1 := by rw [hg a ha, mul_one, hg b hb, mul_one, hg a ha]

section Section


abbrev PresG : Type := CFSG.CosetTable.PG 5 uWS

theorem presG_card : Finite PresG ∧ Nat.card PresG ≤ 51840 :=
  uPres_card

theorem tProdBits_eq (w : List ℕ) :
    toMat 8 8 (tProdBits w) = ((prodWord tSU w : SU42b) : GL (Fin 8) (ZMod 2)) := by
  rw [tProdBits, prodWord]
  suffices ∀ acc : Array ℕ, toMat 8 8 (w.foldl (fun acc a => bmul 8 8 acc (tBitsOf a)) acc) =
      toMat 8 8 acc * (((w.map tSU).prod : SU42b) : GL (Fin 8) (ZMod 2)) by
    rw [this, toMat_id8', one_mul]
  induction w with
  | nil => intro acc; simp
  | cons a w ih =>
    intro acc
    rw [List.foldl_cons, ih, toMat_bmul, List.map_cons, List.prod_cons, Subgroup.coe_mul,
      Units.val_mul, coe_tSU, mul_assoc]

theorem bpow8_eq (A : Array ℕ) (m : ℕ) : toMat 8 8 (bpow8 A m) = toMat 8 8 A ^ m := by
  rw [bpow8]
  suffices ∀ (acc : Array ℕ) (l : List ℕ), toMat 8 8 (l.foldl (fun acc _ => bmul 8 8 acc A) acc) =
      toMat 8 8 acc * toMat 8 8 A ^ l.length by
    rw [this, toMat_id8', one_mul, List.length_range]
  intro acc l
  induction l generalizing acc with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, toMat_bmul, List.length_cons, pow_succ', mul_assoc]

theorem rel_tSU {r : List ℕ × List ℕ × ℕ} (hr : r ∈ uPresSpecs) :
    (prodWord tSU r.1 * prodWord tSU r.2.1) ^ r.2.2 = 1 := by
  have h := List.all_eq_true.mp uRelCheck_eq_true r hr
  have h1 := toMat_eq_one_of_bIsId h
  rw [bpow8_eq, toMat_bmul, tProdBits_eq, tProdBits_eq, ← Units.val_mul, ← Subgroup.coe_mul,
    ← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow] at h1
  exact Subtype.ext (Units.ext h1)

theorem lift_uWS {G : Type*} [Group G] (g : Fin 5 → G)
    (hrel : ∀ r ∈ uPresSpecs, FreeGroup.lift g (FreeGroup.mk (uRelWord r)) = 1) :
    ∀ r ∈ {r : FreeGroup (Fin 5) | r ∈ uWS.map FreeGroup.mk}, FreeGroup.lift g r = 1 := by
  intro r hr
  change r ∈ uWS.map FreeGroup.mk at hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  change w ∈ uPresSpecs.map uRelWord at hw
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hw
  exact hrel s hs

theorem prodWord_ofNat {G : Type*} [Monoid G] (g : ℕ → G) {w : List ℕ} (hw : IsConjWord w) :
    prodWord (fun a => g ((Fin.ofNat 5 a : Fin 5) : ℕ)) w = prodWord g w := by
  rcases hw with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl⟩
  · simp [prodWord, Fin.ofNat, Nat.mod_eq_of_lt ha]
  · simp [prodWord, Fin.ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

noncomputable def presHom : PresG →* SU42b :=
  PresentedGroup.toGroup (lift_uWS (fun a : Fin 5 => tSU a) fun r hr => by
    rw [lift_mk_uRelWord, prodWord_ofNat _ (isConjWord_specs r hr).1,
      prodWord_ofNat _ (isConjWord_specs r hr).2]
    exact rel_tSU hr)

theorem presHom_of (a : Fin 5) : presHom (PresentedGroup.of a) = tSU a :=
  PresentedGroup.toGroup.of _

theorem prodWord_presHom {w : List ℕ} (hw : ∀ a ∈ w, a < 5) :
    presHom (prodWord (fun a => PresentedGroup.of (Fin.ofNat 5 a)) w) = prodWord tSU w := by
  rw [prodWord, prodWord, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  simp only [Function.comp_apply, presHom_of, Fin.ofNat, Nat.mod_eq_of_lt (hw a ha)]

theorem presHom_surjective : Function.Surjective presHom := by
  have hx := uGenCheck_eq_true
  simp only [uGenCheck, Bool.and_eq_true, beq_iff_eq] at hx
  have hmem : ∀ w : List ℕ, (∀ a ∈ w, a < 5) → prodWord tSU w ∈ presHom.range := fun w hw =>
    ⟨_, prodWord_presHom hw⟩
  have h0 : genSU 0 ∈ presHom.range := by
    have : genSU 0 = prodWord tSU uPresX := by
      apply SU42b_ext
      rw [← tProdBits_eq, hx.1, coe_genSU']
    rw [this]; exact hmem _ (by decide)
  have h1 : genSU 1 ∈ presHom.range := by
    have : genSU 1 = prodWord tSU uPresY := by
      apply SU42b_ext
      rw [← tProdBits_eq, hx.2, coe_genSU']
    rw [this]; exact hmem _ (by decide)
  rw [← MonoidHom.range_eq_top, eq_top_iff, SU42b_eq_closure, Subgroup.closure_le]
  rintro g (rfl | rfl)
  exacts [h0, h1]

theorem tSU_mul_self {a : ℕ} (ha : a < 5) : tSU a * tSU a = 1 := by
  have hmem : ∀ a < 5, ([a], [a], 1) ∈ uPresSpecs := by decide
  have := rel_tSU (hmem a ha)
  simpa [prodWord] using this

theorem presHom_ker_mul_self {p : PresG} (hp : p ∈ presHom.ker) : p * p = 1 := by
  obtain ⟨hfin, hcard⟩ := presG_card
  have hindex : Nat.card PresG = Nat.card presHom.ker * Nat.card SU42b := by
    rw [mul_comm, ← Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective presHom presHom_surjective).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [card_SU42b] at hindex
  have hk : Nat.card presHom.ker ≤ 2 := by omega
  have hk0 : 0 < Nat.card presHom.ker := Nat.card_pos
  have hpow := pow_card_eq_one' (G := presHom.ker) (x := ⟨p, hp⟩)
  interval_cases h : Nat.card presHom.ker
  · have : (⟨p, hp⟩ : presHom.ker) = 1 := by simpa using hpow
    have hp1 : p = 1 := congrArg Subtype.val this
    rw [hp1, one_mul]
  · have : (⟨p, hp⟩ : presHom.ker) ^ 2 = 1 := hpow
    have h2 := congrArg Subtype.val this
    simpa [sq] using h2

theorem exists_section_SU42b {Γ : Type*} [Group Γ] (f : Γ →* SU42b) (hf : Function.Surjective f)
    (hZc : f.ker ≤ center Γ) (hZo : Odd (Nat.card f.ker)) :
    ∃ ψ : SU42b →* Γ, f.comp ψ = MonoidHom.id SU42b := by
  choose T₀ hT₀ using fun a : Fin 5 => hf (tSU a)
  have hsq : ∀ a : Fin 5, T₀ a ^ 2 ^ 1 ∈ f.ker := fun a => by
    rw [MonoidHom.mem_ker, map_pow, hT₀, pow_one, sq, tSU_mul_self a.isLt]
  choose w hwZ hw using fun a => exists_isTwoElt_mul hZc hZo (hsq a)
  set T : Fin 5 → Γ := fun a => T₀ a * w a with hT
  have hfT : ∀ a, f (T a) = tSU a := fun a => by
    rw [hT, map_mul, hT₀, (MonoidHom.mem_ker).mp (hwZ a), mul_one]
  have hTT : ∀ a, T a * T a = 1 := fun a => by
    have := hw a; rwa [pow_one, sq] at this
  set T' : ℕ → Γ := fun a => T (Fin.ofNat 5 a)
  have hT'T' : ∀ a < 5, T' a * T' a = 1 := fun a _ => hTT _
  have hfT' : ∀ w : List ℕ, IsConjWord w → f (prodWord T' w) = prodWord tSU w := by
    intro w hw
    rw [prodWord, map_list_prod, List.map_map, ← prodWord_ofNat tSU hw, prodWord]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    simp only [Function.comp_apply, T', hfT]
  have hrel : ∀ r ∈ uPresSpecs, FreeGroup.lift T (FreeGroup.mk (uRelWord r)) = 1 := by
    intro r hr
    rw [lift_mk_uRelWord]
    have h1 := isConjWord_specs r hr
    refine pow_mul_eq_one_of_involutions hZc hZo (prodWord_mul_self_of_isConjWord hT'T' h1.1)
      (prodWord_mul_self_of_isConjWord hT'T' h1.2) ?_
    rw [MonoidHom.mem_ker, map_pow, map_mul]
    rw [hfT' _ h1.1, hfT' _ h1.2]
    exact rel_tSU hr
  set σ := PresentedGroup.toGroup (lift_uWS T hrel)
  have hfσ : f.comp σ = presHom := by
    refine PresentedGroup.ext fun a => ?_
    rw [MonoidHom.comp_apply, PresentedGroup.toGroup.of, hfT, presHom_of]
  have hle : presHom.ker ≤ σ.ker := by
    intro p hp
    rw [MonoidHom.mem_ker]
    have hpp := presHom_ker_mul_self hp
    have hσk : σ p ∈ f.ker := by
      rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hfσ]
      exact hp
    refine eq_of_pow_two_pow hZo hσk f.ker.one_mem 1 ?_
    rw [pow_one, sq, ← map_mul, hpp, map_one, one_pow]
  set e := QuotientGroup.quotientKerEquivOfSurjective presHom presHom_surjective
  refine ⟨(QuotientGroup.lift presHom.ker σ hle).comp e.symm.toMonoidHom, ?_⟩
  ext1 x
  obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (e.symm x)
  have hx : x = presHom p := by
    rw [← e.apply_symm_apply x, ← hp]
    rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
  rw [← hp, QuotientGroup.lift_mk, ← MonoidHom.comp_apply, hfσ, ← hx]

end Section

end CFSG.EvenSmallLie.UnitarySix.YamadaPar

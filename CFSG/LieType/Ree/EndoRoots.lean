module

public import CFSG.LieType.Ree.Endo
public import CFSG.LieType.Chevalley.FixedBruhat
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits

namespace ReeTag

variable {t : ReeTag}

theorem cartan_mul_cartan_perm (t : ReeTag) (i j : Fin t.tag.rank) :
    t.tag.cartan (t.perm i) (t.perm j) * t.tag.cartan (t.perm j) (t.perm i) =
      t.tag.cartan i j * t.tag.cartan j i := by
  revert i j
  cases t <;> decide

theorem coxeterMatrix_perm (i j : Fin t.tag.rank) :
    (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan t.tag)).M (t.perm i)
        (t.perm j) =
      (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan t.tag)).M i j := by
  simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
    cartan_mul_cartan_perm]

variable (t) in
@[expose] def weylPermHom : WeylGroup t.tag →* WeylGroup t.tag :=
  (coxeterSystem t.tag).lift ⟨fun i => simple t.tag (t.perm i), fun i i' => by
    rw [← coxeterMatrix_perm]
    exact (coxeterSystem t.tag).simple_mul_simple_pow _ _⟩

theorem weylPermHom_simple (i : Fin t.tag.rank) :
    t.weylPermHom (simple t.tag i) = simple t.tag (t.perm i) :=
  (coxeterSystem t.tag).lift_apply_simple _ i

theorem weylPermHom_comp_self : t.weylPermHom.comp t.weylPermHom = MonoidHom.id _ :=
  (coxeterSystem t.tag).ext_simple fun i => by
    rw [MonoidHom.comp_apply, weylPermHom_simple, weylPermHom_simple, perm_perm,
      MonoidHom.id_apply]

variable (t) in
@[expose] def weylPerm : WeylGroup t.tag ≃* WeylGroup t.tag :=
  MonoidHom.toMulEquiv t.weylPermHom t.weylPermHom weylPermHom_comp_self weylPermHom_comp_self

theorem weylPerm_simple (i : Fin t.tag.rank) :
    t.weylPerm (simple t.tag i) = simple t.tag (t.perm i) :=
  weylPermHom_simple i

theorem weylPerm_weylPerm (w : WeylGroup t.tag) : t.weylPerm (t.weylPerm w) = w :=
  DFunLike.congr_fun weylPermHom_comp_self w

theorem weylPerm_wordProd (ω : List (Fin t.tag.rank)) :
    t.weylPerm ((coxeterSystem t.tag).wordProd ω) =
      (coxeterSystem t.tag).wordProd (ω.map t.perm) := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, map_one, List.map_nil, CoxeterSystem.wordProd_nil]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, weylPerm_simple, ih, List.map_cons,
      CoxeterSystem.wordProd_cons]

theorem length_weylPerm_le (w : WeylGroup t.tag) :
    (coxeterSystem t.tag).length (t.weylPerm w) ≤ (coxeterSystem t.tag).length w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem t.tag).exists_isReduced w
  rw [weylPerm_wordProd]
  refine ((coxeterSystem t.tag).length_wordProd_le _).trans ?_
  rw [List.length_map]
  exact hω.ge

theorem length_weylPerm (w : WeylGroup t.tag) :
    (coxeterSystem t.tag).length (t.weylPerm w) = (coxeterSystem t.tag).length w := by
  refine le_antisymm (length_weylPerm_le w) ?_
  have := length_weylPerm_le (t := t) (t.weylPerm w)
  rwa [weylPerm_weylPerm] at this

theorem isReduced_map_perm {ω : List (Fin t.tag.rank)} (hω : (coxeterSystem t.tag).IsReduced ω) :
    (coxeterSystem t.tag).IsReduced (ω.map t.perm) := by
  unfold CoxeterSystem.IsReduced at hω ⊢
  rw [← weylPerm_wordProd, length_weylPerm, hω, List.length_map]

theorem dualRoot_smul (w : WeylGroup t.tag) {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) :
    t.dualRoot (w • α) = t.weylPerm w • t.dualRoot α := by
  induction w using (coxeterSystem t.tag).simple_induction_left with
  | one => rw [one_smul, map_one, one_smul]
  | mul_simple_left w i ih =>
    rw [mul_smul, simple_smul, dualRoot_reflect (IsRoot.smul hα w), ih, map_mul,
      weylPerm_simple, mul_smul, simple_smul]

theorem height_dualRoot_neg_iff {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) :
    height (t.dualRoot α) < 0 ↔ height α < 0 := by
  have h1 := height_dualRoot_pos_iff hα
  have h2 := (isRoot_dualRoot hα).height_ne_zero
  have h3 := hα.height_ne_zero
  omega

variable (t) in
@[expose] def dualRootOf (α : Root t.tag) : Root t.tag :=
  ⟨t.dualRoot α.1, isRoot_dualRoot α.2⟩

theorem dualRootOf_smul (w : WeylGroup t.tag) (α : Root t.tag) :
    t.dualRootOf (w • α) = t.weylPerm w • t.dualRootOf α :=
  Subtype.ext (dualRoot_smul w α.2)

variable {K : Type} [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

theorem reeAut_xElement (i : Fin t.tag.rank) (c : K) :
    t.reeAut K a (xElement i c) = xElement (t.perm i) (c ^ t.relationExponent a i) :=
  reeEndo_xElement (shortFaithful (CharP.cast_eq_zero K t.prime)) a i c

theorem reeAut_yElement (i : Fin t.tag.rank) (c : K) :
    t.reeAut K a (yElement i c) = yElement (t.perm i) (c ^ t.relationExponent a i) :=
  reeEndo_yElement (shortFaithful (CharP.cast_eq_zero K t.prime)) a i c

omit [Finite K] in
theorem neg_one_pow_relationExponent (i : Fin t.tag.rank) :
    (-1 : K) ^ t.relationExponent a i = -1 := by
  cases t with
  | G2 =>
    have h3 : Odd ReeTag.G2.prime := by decide
    refine Odd.neg_one_pow ?_
    unfold relationExponent
    split_ifs
    · exact h3.pow
    · exact h3.pow
  | F4 =>
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    rw [CharTwo.neg_eq, one_pow]

variable (K) in
@[expose] def weylElementOf (i : Fin t.tag.rank) (u : Kˣ) : adjointGroup t.tag K :=
  ⟨weylElt t.tag K i u, weylElt_mem_adjointGroup i u⟩

omit [Finite K] [CharP K t.prime] in
theorem weylElementOf_eq (i : Fin t.tag.rank) (u : Kˣ) :
    weylElementOf K i u =
      xElement i (u : K) * yElement i (-((u⁻¹ : Kˣ) : K)) * xElement i (u : K) :=
  Subtype.ext (weylElt_eq_xUnit_mul i u)

theorem reeAut_weylElementOf (i : Fin t.tag.rank) (u : Kˣ) :
    t.reeAut K a (weylElementOf K i u) =
      weylElementOf K (t.perm i) (u ^ t.relationExponent a i) := by
  have hx : (u : K) ^ t.relationExponent a i = ((u ^ t.relationExponent a i : Kˣ) : K) :=
    (Units.val_pow_eq_pow_val _ _).symm
  have hy : (-((u⁻¹ : Kˣ) : K)) ^ t.relationExponent a i =
      -(((u ^ t.relationExponent a i)⁻¹ : Kˣ) : K) := by
    rw [neg_pow, neg_one_pow_relationExponent (K := K), neg_one_mul, ← inv_pow,
      Units.val_pow_eq_pow_val]
  rw [weylElementOf_eq, weylElementOf_eq, map_mul, map_mul, reeAut_xElement, reeAut_yElement, hx,
    hy]

theorem reeAut_weylElement (i : Fin t.tag.rank) :
    t.reeAut K a (weylElement t.tag K i) = weylElement t.tag K (t.perm i) := by
  have := reeAut_weylElementOf (K := K) a i 1
  rwa [one_pow] at this

theorem reeAut_torusElement (i : Fin t.tag.rank) (u : Kˣ) :
    t.reeAut K a (torusElement t.tag K i u) =
      torusElement t.tag K (t.perm i) (u ^ t.relationExponent a i) := by
  have h : ∀ (j : Fin t.tag.rank) (v : Kˣ),
      torusElement t.tag K j v = weylElementOf K j v * weylElementOf K j (-1) :=
    fun _ _ => rfl
  have hneg : ((-1 : Kˣ) ^ t.relationExponent a i) = -1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      neg_one_pow_relationExponent (K := K)])
  rw [h, h, map_mul, reeAut_weylElementOf, reeAut_weylElementOf, hneg]

theorem reeAut_mem_monomialGroup {m : adjointGroup t.tag K} (hm : m ∈ monomialGroup t.tag K) :
    t.reeAut K a m ∈ monomialGroup t.tag K := by
  have hle : (monomialGroup t.tag K).map (t.reeAut K a).toMonoidHom ≤ monomialGroup t.tag K := by
    rw [monomialGroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rcases hg with ⟨i, rfl⟩ | ⟨⟨i, u⟩, rfl⟩
    · change t.reeAut K a (weylElement t.tag K i) ∈ _
      rw [reeAut_weylElement]
      exact weylElement_mem_monomialGroup _
    · change t.reeAut K a (torusElement t.tag K i u) ∈ _
      rw [reeAut_torusElement]
      exact torusElement_mem_monomialGroup _ _
  exact hle ⟨m, hm, rfl⟩

variable (t K) in
@[expose] def reeAutN : monomialGroup t.tag K →* monomialGroup t.tag K :=
  (((t.reeAut K a).toMonoidHom).comp (monomialGroup t.tag K).subtype).codRestrict _
    fun m => reeAut_mem_monomialGroup a m.2

theorem weylHom_reeAut (m : monomialGroup t.tag K) :
    weylHom t.tag K ⟨t.reeAut K a m, reeAut_mem_monomialGroup a m.2⟩ =
      t.weylPerm (weylHom t.tag K m) := by
  have hcl : Subgroup.closure (((↑) : monomialGroup t.tag K → adjointGroup t.tag K) ⁻¹'
      (Set.range (weylElement t.tag K) ∪
        Set.range fun x : Fin t.tag.rank × Kˣ => torusElement t.tag K x.1 x.2)) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have key : (weylHom t.tag K).comp (t.reeAutN K a) =
      (t.weylPerm.toMonoidHom).comp (weylHom t.tag K) := by
    refine MonoidHom.eq_of_eqOn_dense hcl fun g hg => ?_
    rcases hg with ⟨i, hi⟩ | ⟨⟨i, u⟩, hi⟩
    · have h1 : t.reeAutN K a g =
          ⟨weylElement t.tag K (t.perm i), weylElement_mem_monomialGroup _⟩ :=
        Subtype.ext (by
          change t.reeAut K a (g : adjointGroup t.tag K) = _
          rw [← hi, reeAut_weylElement])
      have h2 : g = ⟨weylElement t.tag K i, weylElement_mem_monomialGroup _⟩ :=
        Subtype.ext hi.symm
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, weylHom_weylElement]
      rw [h2, weylHom_weylElement, weylPerm_simple]
    · have h1 : t.reeAutN K a g = ⟨torusElement t.tag K (t.perm i) (u ^ t.relationExponent a i),
          torusElement_mem_monomialGroup _ _⟩ :=
        Subtype.ext (by
          change t.reeAut K a (g : adjointGroup t.tag K) = _
          rw [← hi, reeAut_torusElement])
      have h2 : g = ⟨torusElement t.tag K i u, torusElement_mem_monomialGroup _ _⟩ :=
        Subtype.ext hi.symm
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, weylHom_torusElement]
      rw [h2, weylHom_torusElement, map_one]
  exact DFunLike.congr_fun key m

theorem reeAut_nrep (w : WeylGroup t.tag) :
    t.reeAut K a (nrep t.tag K w) = nrep t.tag K (t.weylPerm w) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem t.tag).exists_isReduced w
  rw [nrep_eq_prod _ _ hω, weylPerm_wordProd, nrep_eq_prod _ _ (isReduced_map_perm hω),
    map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact reeAut_weylElement a i

theorem X_dualRootOf_smul_simple (m : monomialGroup t.tag K) (j : Fin t.tag.rank) :
    (nativeRootSubgroups t.tag K).X (t.dualRootOf (weylHom t.tag K m • simpleRoot t.tag j)) =
      ((nativeRootSubgroups t.tag K).X (simpleRoot t.tag (t.perm j))).map
        (MulAut.conj (t.reeAut K a m)).toMonoidHom := by
  set m' : monomialGroup t.tag K := ⟨t.reeAut K a m, reeAut_mem_monomialGroup a m.2⟩ with hm'
  change _ = ((nativeRootSubgroups t.tag K).X (simpleRoot t.tag (t.perm j))).map
    (MulAut.conj (m' : adjointGroup t.tag K)).toMonoidHom
  rw [RootSubgroups.map_conj, hm', weylHom_reeAut, dualRootOf_smul]
  congr 2
  exact Subtype.ext (dualRoot_single t j)

theorem reeAut_conj_xElement (m : adjointGroup t.tag K) (j : Fin t.tag.rank) (c : K) :
    t.reeAut K a ((MulAut.conj m).toMonoidHom (xElement j c)) =
      (MulAut.conj (t.reeAut K a m)).toMonoidHom
        (xElement (t.perm j) (c ^ t.relationExponent a j)) := by
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, reeAut_xElement]

theorem reeAut_mem_X {α : Root t.tag} {x : adjointGroup t.tag K}
    (hx : x ∈ (nativeRootSubgroups t.tag K).X α) :
    t.reeAut K a x ∈ (nativeRootSubgroups t.tag K).X (t.dualRootOf α) := by
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 α.2
  obtain ⟨m, rfl⟩ := weylHom_surjective (τ := t.tag) (K := K) w
  have hα : α = weylHom t.tag K m • simpleRoot t.tag j := Subtype.ext hwj.symm
  subst hα
  rw [← (nativeRootSubgroups t.tag K).map_conj m] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨c, hc⟩ := ((nativeRootSubgroups t.tag K).mem_simple j y).1 hy
  have hy' : y = xElement j c := Subtype.ext hc
  subst hy'
  rw [X_dualRootOf_smul_simple, reeAut_conj_xElement]
  exact ⟨_, ((nativeRootSubgroups t.tag K).mem_simple _ _).2 ⟨_, rfl⟩, rfl⟩

theorem map_reeAut_X_le (α : Root t.tag) :
    ((nativeRootSubgroups t.tag K).X α).map (t.reeAut K a).toMonoidHom ≤
      (nativeRootSubgroups t.tag K).X (t.dualRootOf α) := by
  rintro _ ⟨x, hx, rfl⟩
  exact reeAut_mem_X a hx

omit [CharP K t.prime] in
theorem pow_relationExponent_surjective [CharP K t.prime] (i : Fin t.tag.rank) :
    Function.Surjective fun c : K => c ^ t.relationExponent a i := by
  have h : ∀ n, Function.Surjective fun c : K => c ^ t.prime ^ n := fun n => by
    have := Finite.injective_iff_surjective.1 (iterateFrobenius K t.prime n).injective
    intro d
    obtain ⟨c, hc⟩ := this d
    exact ⟨c, by rw [iterateFrobenius_def] at hc; exact hc⟩
  unfold relationExponent
  split_ifs
  · exact h a
  · exact h (a + 1)

theorem map_reeAut_X (α : Root t.tag) :
    ((nativeRootSubgroups t.tag K).X α).map (t.reeAut K a).toMonoidHom =
      (nativeRootSubgroups t.tag K).X (t.dualRootOf α) := by
  refine le_antisymm (map_reeAut_X_le a α) ?_
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 α.2
  obtain ⟨m, rfl⟩ := weylHom_surjective (τ := t.tag) (K := K) w
  have hα : α = weylHom t.tag K m • simpleRoot t.tag j := Subtype.ext hwj.symm
  subst hα
  rw [X_dualRootOf_smul_simple]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨d, hd⟩ := ((nativeRootSubgroups t.tag K).mem_simple _ y).1 hy
  have hy' : y = xElement (t.perm j) d := Subtype.ext hd
  subst hy'
  obtain ⟨c, rfl⟩ := pow_relationExponent_surjective (K := K) a j d
  refine ⟨(MulAut.conj (m : adjointGroup t.tag K)).toMonoidHom (xElement j c), ?_,
    reeAut_conj_xElement a _ j c⟩
  rw [← (nativeRootSubgroups t.tag K).map_conj m]
  exact ⟨xElement j c, ((nativeRootSubgroups t.tag K).mem_simple _ _).2 ⟨c, rfl⟩, rfl⟩

theorem reeAut_mem_H {h : adjointGroup t.tag K} (hh : h ∈ (nativeData t.tag K).H) :
    t.reeAut K a h ∈ (nativeData t.tag K).H := by
  obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := RootGroupData.mem_H_iff.1 hh
  have hkN' : k ∈ monomialGroup t.tag K := hkN
  have hk' : weylHom t.tag K ⟨k, hkN'⟩ = 1 := hk
  refine RootGroupData.mem_H_iff.2 ⟨⟨t.reeAut K a k, reeAut_mem_monomialGroup a hkN'⟩, ?_, rfl⟩
  have h1 := weylHom_reeAut a ⟨k, hkN'⟩
  rw [hk', map_one] at h1
  exact h1

theorem reeAut_mem_U {u : adjointGroup t.tag K} (hu : u ∈ (nativeData t.tag K).U) :
    t.reeAut K a u ∈ (nativeData t.tag K).U := by
  have hle : (nativeData t.tag K).U ≤
      (nativeData t.tag K).U.comap (t.reeAut K a).toMonoidHom :=
    iSup₂_le fun α hα _ hx => (nativeData t.tag K).X_le_U
      (show 0 < height (t.dualRootOf α).1 from (height_dualRoot_pos_iff α.2).2 hα)
      (reeAut_mem_X a hx)
  exact hle hu

theorem reeAut_mem_B {b : adjointGroup t.tag K} (hb : b ∈ (nativeData t.tag K).B) :
    t.reeAut K a b ∈ (nativeData t.tag K).B := by
  have hle : (nativeData t.tag K).B ≤
      (nativeData t.tag K).B.comap (t.reeAut K a).toMonoidHom :=
    sup_le (fun _ hh => (nativeData t.tag K).H_le_B (reeAut_mem_H a hh))
      (fun _ hu => (nativeData t.tag K).U_le_B (reeAut_mem_U a hu))
  exact hle hb

theorem reeAut_mem_Uminus (w : WeylGroup t.tag) {u : adjointGroup t.tag K}
    (hu : u ∈ Uminus t.tag K w) : t.reeAut K a u ∈ Uminus t.tag K (t.weylPerm w) := by
  have hle : Uminus t.tag K w ≤ (Uminus t.tag K (t.weylPerm w)).comap (t.reeAut K a).toMonoidHom :=
    iSup₂_le fun α hα _ hx => by
      refine le_iSup₂_of_le (f := fun (β : Root t.tag)
        (_ : 0 < height β.1 ∧ height (t.weylPerm w • β).1 < 0) =>
          (nativeRootSubgroups t.tag K).X β) (t.dualRootOf α) ⟨?_, ?_⟩ le_rfl
        (reeAut_mem_X a hx)
      · exact (height_dualRoot_pos_iff α.2).2 hα.1
      · rw [← dualRootOf_smul]
        exact (height_dualRoot_neg_iff (w • α).2).2 hα.2
  exact hle hu

theorem exists_reeFixed_mul
    (hdisj : ∀ m m' : monomialGroup t.tag K, ∀ b₁ ∈ (nativeData t.tag K).B,
      ∀ b₂ ∈ (nativeData t.tag K).B, ∀ b₃ ∈ (nativeData t.tag K).B,
      ∀ b₄ ∈ (nativeData t.tag K).B,
      b₁ * (m : adjointGroup t.tag K) * b₂ = b₃ * (m' : adjointGroup t.tag K) * b₄ →
        weylHom t.tag K m = weylHom t.tag K m')
    (hexists : ∀ m : monomialGroup t.tag K, ∀ b₁ ∈ (nativeData t.tag K).B,
      ∀ b₂ ∈ (nativeData t.tag K).B, ∃ b ∈ (nativeData t.tag K).B,
      ∃ u ∈ Uminus t.tag K (weylHom t.tag K m),
        b₁ * (m : adjointGroup t.tag K) * b₂ = b * nrep t.tag K (weylHom t.tag K m) * u)
    (hunique : ∀ w, ∀ b ∈ (nativeData t.tag K).B, ∀ b' ∈ (nativeData t.tag K).B,
      ∀ u ∈ Uminus t.tag K w, ∀ u' ∈ Uminus t.tag K w,
      b * nrep t.tag K w * u = b' * nrep t.tag K w * u' → b = b' ∧ u = u')
    {g : adjointGroup t.tag K} (hg : t.reeAut K a g = g) :
    ∃ w, t.weylPerm w = w ∧ ∃ b ∈ (nativeData t.tag K).B, t.reeAut K a b = b ∧
      ∃ u ∈ Uminus t.tag K w, t.reeAut K a u = u ∧ g = b * nrep t.tag K w * u :=
  exists_fixed_mul_of_fixed (nativeData t.tag K).B (monomialGroup t.tag K) (weylHom t.tag K)
    (nrep t.tag K) (fun w => (Uminus t.tag K w : Set (adjointGroup t.tag K))) (t.reeAut K a)
    t.weylPerm
    (RootGroupData.exists_mem_doubleCoset (D := nativeData t.tag K)
      (nativeRootSubgroups t.tag K).simple_le_normalizer_Ui (nativeRootSubgroups t.tag K).rankOne
      (nativeRootSubgroups t.tag K).closure_B_union_n)
    hdisj hexists hunique (fun _ hb => reeAut_mem_B a hb)
    (fun m => reeAut_mem_monomialGroup a m.2) (weylHom_reeAut a)
    (fun w _ hu => reeAut_mem_Uminus a w hu)
    (fun w hw => by rw [reeAut_nrep, hw]) hg

end ReeTag

end CFSG.LieType.Ree

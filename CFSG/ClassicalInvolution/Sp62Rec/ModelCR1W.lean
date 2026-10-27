module

public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1CE
public import CFSG.ClassicalInvolution.Q3.AE.Models
public import Certificates.Certificate550851

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open
  CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open scoped commutatorElement

@[expose] def W6 : Subgroup (Wr 6) where
  carrier := {a | wsum a = 0}
  mul_mem' {a b} ha hb := by
    have ha' : wsum a = 0 := ha
    have hb' : wsum b = 0 := hb
    show wsum (a * b) = 0
    rw [wsum_mul, ha', hb', add_zero]
  one_mem' := wsum_one
  inv_mem' {a} ha := by
    have ha' : wsum a = 0 := ha
    show wsum a⁻¹ = 0
    rw [wsum_inv, ha']

theorem mem_W6 {a : Wr 6} : a ∈ W6 ↔ wsum a = 0 := Iff.rfl

theorem allOnes_mem_W6 : allOnes 6 ∈ W6 := by
  show wsum (allOnes 6) = 0
  decide

theorem aeSub_six_le_W6 : aeSub 6 ≤ W6 := fun _ ha => ha.1

@[expose] def wsumHom : Wr 6 →* Multiplicative (ZMod 2) where
  toFun a := Multiplicative.ofAdd (wsum a)
  map_one' := by rw [wsum_one]; rfl
  map_mul' a b := by rw [wsum_mul]; rfl

theorem W6_eq_ker : W6 = wsumHom.ker := by
  ext a
  rw [MonoidHom.mem_ker, mem_W6]
  exact ofAdd_eq_one.symm

theorem card_wr_six : Nat.card (Wr 6) = 46080 := by
  have e : Wr 6 ≃ (Fin 6 → ZMod 2) × Equiv.Perm (Fin 6) :=
    { toFun := fun a => (a.vec, a.perm)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_perm, Nat.card_zmod,
    Nat.card_fin]
  decide

theorem card_W6 : Nat.card W6 = 23040 := by
  have hsurj : Function.Surjective wsumHom := by
    intro y
    obtain ⟨x, rfl⟩ : ∃ x : ZMod 2, Multiplicative.ofAdd x = y := ⟨Multiplicative.toAdd y, rfl⟩
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) x with rfl | rfl
    · exact ⟨1, map_one wsumHom⟩
    · refine ⟨Wr.ofVec (Pi.single 0 1), ?_⟩
      show Multiplicative.ofAdd (wsum (Wr.ofVec (Pi.single 0 1))) = Multiplicative.ofAdd 1
      congr 1
  have hidx : W6.index = 2 := by
    rw [W6_eq_ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    rfl
  have h := Subgroup.card_mul_index W6
  rw [hidx, card_wr_six] at h
  omega

@[expose] def signW6 : ↥W6 →* ℤˣ := Equiv.Perm.sign.comp ((permHom 6).comp W6.subtype)

theorem card_aeSub_six : Nat.card (aeSub 6) = 11520 := by
  have hker : signW6.ker = (aeSub 6).subgroupOf W6 := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_aeSub]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  have hsurj : Function.Surjective signW6 := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one signW6⟩
    · refine ⟨⟨Wr.ofPerm (Equiv.swap 0 1), ?_⟩, ?_⟩
      · show wsum (Wr.ofPerm (Equiv.swap 0 1)) = 0
        decide
      · show Equiv.Perm.sign (Equiv.swap (0 : Fin 6) 1) = -1
        exact Equiv.Perm.sign_swap (by decide)
  have hidx : ((aeSub 6).subgroupOf W6).index = 2 := by
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h := Subgroup.card_mul_index ((aeSub 6).subgroupOf W6)
  rw [hidx, card_W6, Nat.card_congr (Subgroup.subgroupOfEquivOfLe aeSub_six_le_W6).toEquiv] at h
  omega

theorem commutator_W6_le : ⁅W6, W6⁆ ≤ aeSub 6 := by
  rw [Subgroup.commutator_le]
  intro g _ h _
  rw [mem_aeSub, commutatorElement_def]
  refine ⟨?_, ?_⟩
  · rw [wsum_mul, wsum_mul, wsum_mul, wsum_inv, wsum_inv,
      show wsum g + wsum h + wsum g + wsum h = (wsum g + wsum g) + (wsum h + wsum h) by ring,
      zmod_two_add_self, zmod_two_add_self, add_zero]
  · rw [mul_perm, mul_perm, mul_perm, inv_perm, inv_perm, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Equiv.Perm.sign_inv]
    rw [mul_right_comm (Equiv.Perm.sign g.perm), Int.units_mul_self, one_mul,
      Int.units_mul_self]

theorem size_w6code (a : Wr 6) : (w6code a).size = 64 := Array.size_ofFn

theorem w6code_get (a : Wr 6) {p : ℕ} (hp : p < 64) :
    (w6code a)[p]! = if p < 12 then w6Pt a p else p :=
  getElem!_ofFn_nat _ hp

theorem w6Pt_eq (a : Wr 6) (i : Fin 6) {c : ℕ} (hc : c < 2) :
    w6Pt a (i.val + 6 * c) = (a.perm i).val + 6 * ((c + (a.vec (a.perm i)).val) % 2) := by
  have h1 : (⟨(i.val + 6 * c) % 6, Nat.mod_lt _ (by decide)⟩ : Fin 6) = i :=
    Fin.ext (by show (i.val + 6 * c) % 6 = i.val; omega)
  have h2 : (i.val + 6 * c) / 6 = c := by omega
  unfold w6Pt
  rw [h1, h2]

theorem exists_pt6 {p : ℕ} (hp : p < 12) : ∃ i : Fin 6, ∃ c < 2, p = i.val + 6 * c :=
  ⟨⟨p % 6, Nat.mod_lt _ (by decide)⟩, p / 6, by omega, by simp only; omega⟩

theorem w6Pt_lt (a : Wr 6) {p : ℕ} (hp : p < 12) : w6Pt a p < 12 := by
  obtain ⟨i, c, hc, rfl⟩ := exists_pt6 hp
  rw [w6Pt_eq a i hc]
  have h1 := (a.perm i).isLt
  have h2 : (c + (a.vec (a.perm i)).val) % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

theorem w6Pt_mul (a b : Wr 6) {p : ℕ} (hp : p < 12) : w6Pt (a * b) p = w6Pt a (w6Pt b p) := by
  obtain ⟨i, c, hc, rfl⟩ := exists_pt6 hp
  have hc' : (c + (b.vec (b.perm i)).val) % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [w6Pt_eq _ i hc, w6Pt_eq b i hc, w6Pt_eq a (b.perm i) hc']
  have hperm : (a * b).perm i = a.perm (b.perm i) := rfl
  have hvec : (a * b).vec (a.perm (b.perm i)) = a.vec (a.perm (b.perm i)) + b.vec (b.perm i) := by
    rw [mul_vec, Equiv.symm_apply_apply]
  rw [hperm, hvec, ZMod.val_add]
  have h1 := ZMod.val_lt (a.vec (a.perm (b.perm i)))
  have h2 := ZMod.val_lt (b.vec (b.perm i))
  omega

theorem w6code_mul (a b : Wr 6) : w6code (a * b) = compA (w6code a) (w6code b) := by
  refine ext64 (size_w6code _) (size_compA _ _) fun p hp => ?_
  rw [compA_get _ _ hp, w6code_get _ hp, w6code_get b hp]
  by_cases h12 : p < 12
  · have h := w6Pt_lt b h12
    rw [if_pos h12, if_pos h12, w6code_get a (by omega), if_pos h, w6Pt_mul a b h12]
  · rw [if_neg h12, if_neg h12, w6code_get a hp, if_neg h12]

theorem w6code_one : w6code 1 = idA () := by
  refine ext64 (size_w6code _) size_idA fun p hp => ?_
  rw [w6code_get _ hp, idA_get hp]
  by_cases h12 : p < 12
  · rw [if_pos h12]
    obtain ⟨i, c, hc, rfl⟩ := exists_pt6 h12
    rw [w6Pt_eq _ i hc]
    show i.val + 6 * ((c + (0 : ZMod 2).val) % 2) = i.val + 6 * c
    rw [ZMod.val_zero, add_zero, Nat.mod_eq_of_lt hc]
  · rw [if_neg h12]

theorem w6code_injective : Function.Injective w6code := by
  intro a b h
  have hpt : ∀ i : Fin 6, w6Pt a i.val = w6Pt b i.val := by
    intro i
    have := congrArg (fun t => t[i.val]!) h
    rwa [w6code_get _ (by omega), w6code_get _ (by omega), if_pos (by omega),
      if_pos (by omega)] at this
  have hpt0 : ∀ i : Fin 6, (a.perm i).val + 6 * ((a.vec (a.perm i)).val % 2) =
      (b.perm i).val + 6 * ((b.vec (b.perm i)).val % 2) := by
    intro i
    have := hpt i
    rw [show i.val = i.val + 6 * 0 from rfl, w6Pt_eq a i (by norm_num),
      w6Pt_eq b i (by norm_num), zero_add, zero_add] at this
    exact this
  have hperm : a.perm = b.perm := by
    ext i
    have := hpt0 i
    have h1 := (a.perm i).isLt
    have h2 := (b.perm i).isLt
    omega
  have hvec : a.vec = b.vec := by
    funext j
    have := hpt0 (a.perm.symm j)
    rw [Equiv.apply_symm_apply, hperm, Equiv.apply_symm_apply] at this
    have h1 := ZMod.val_lt (a.vec j)
    have h2 := ZMod.val_lt (b.vec j)
    exact ZMod.val_injective _ (by omega)
  exact Wr.ext hvec hperm

theorem exists_w6_of_autOK {E : Enum} {gs hs F : Array (Array ℕ)} {h : ℕ → Wr 6}
    (hhs : ∀ j < gs.size, hs[j]! = w6code (h j)) (htree : treeOK E gs = true)
    (haut : autOK E gs hs F = true) :
    ∀ i < E.elems.size, ∃ m ∈ Subgroup.closure (h '' Set.Iio gs.size), w6code m = F[i]! := by
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at htree
  simp only [autOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at haut
  obtain ⟨-, hall⟩ := htree
  obtain ⟨⟨⟨⟨-, hF0⟩, hFt⟩, -⟩, -⟩ := haut
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases hall i hi with rfl | ⟨⟨hp, hg⟩, -⟩
    · exact ⟨1, one_mem _, by rw [w6code_one, getElem!_eq_of_getElem? hF0]⟩
    · rcases hFt i hi with hi0 | hFi
      · subst hi0
        exact ⟨1, one_mem _, by rw [w6code_one, getElem!_eq_of_getElem? hF0]⟩
      · obtain ⟨m, hm, hme⟩ := ih _ hp (hp.trans hi)
        refine ⟨m * h E.gen[i]!, mul_mem hm (Subgroup.subset_closure ⟨_, hg, rfl⟩), ?_⟩
        rw [w6code_mul, hme, ← hhs _ hg, hFi]

theorem exists_w6Hom_of_autOK {E : Enum} {gs hs F : Array (Array ℕ)}
    {s : ℕ → StatedSp 3 (ZMod 2)} {h : ℕ → Wr 6}
    (hgs : ∀ j < gs.size, gs[j]! = code (s j)) (hhs : ∀ j < gs.size, hs[j]! = w6code (h j))
    (henum : enumOK E gs = true) (haut : autOK E gs hs F = true) :
    ∃ φ : ↥(Subgroup.closure (s '' Set.Iio gs.size)) →* Wr 6, Function.Injective φ ∧
      (∀ x, φ x ∈ Subgroup.closure (h '' Set.Iio gs.size)) ∧
      ∀ x, w6code (φ x) = appF E F (code (x : StatedSp 3 (ZMod 2))) := by
  set L := Subgroup.closure (s '' Set.Iio gs.size)
  have htree : treeOK E gs = true := by
    simp only [enumOK, Bool.and_eq_true] at henum
    exact henum.1.1
  have hnodup : nodupOK E = true := by
    simp only [enumOK, Bool.and_eq_true] at henum
    exact henum.2
  have hFw := exists_w6_of_autOK hhs htree haut
  have haut' := haut
  simp only [autOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at haut'
  obtain ⟨⟨⟨⟨hsize, hF0⟩, -⟩, hcrit⟩, hinj⟩ := haut'
  have hpos : ∀ x ∈ L, ∃ k, E.lookup (code x) = some k :=
    fun x hx => Option.isSome_iff_exists.mp (lookup_isSome_of_mem_closure hgs henum hx)
  have hex : ∀ x ∈ L, ∃ m ∈ Subgroup.closure (h '' Set.Iio gs.size),
      w6code m = appF E F (code x) := by
    intro x hx
    obtain ⟨k, hk⟩ := hpos x hx
    obtain ⟨m, hm, hme⟩ := hFw k (Enum.lookup_spec hk).1
    exact ⟨m, hm, by rw [hme, appF, hk, Option.getD_some]⟩
  obtain ⟨f, hf, hfm⟩ : ∃ f : StatedSp 3 (ZMod 2) → Wr 6,
      (∀ x ∈ L, w6code (f x) = appF E F (code x)) ∧
        ∀ x ∈ L, f x ∈ Subgroup.closure (h '' Set.Iio gs.size) := by
    classical
    refine ⟨fun x => if hx : ∃ m, w6code m = appF E F (code x) then hx.choose else 1, ?_, ?_⟩
    · intro x hx
      obtain ⟨m, -, hme⟩ := hex x hx
      have hx' : ∃ m, w6code m = appF E F (code x) := ⟨m, hme⟩
      simp only [dif_pos hx']
      exact hx'.choose_spec
    · intro x hx
      obtain ⟨m, hm, hme⟩ := hex x hx
      have hx' : ∃ m, w6code m = appF E F (code x) := ⟨m, hme⟩
      simp only [dif_pos hx']
      rw [w6code_injective (hx'.choose_spec.trans hme.symm)]
      exact hm
  have hf1 : f 1 = 1 := by
    apply w6code_injective
    rw [hf 1 (one_mem _), w6code_one, appF]
    have h0 : E.elems[0]? = some (idA ()) := by
      simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
      exact htree.1
    have := (allLt_iff.mp hnodup) 0 (size_pos_of_getElem? h0)
    rw [decide_eq_true_eq, getElem!_eq_of_getElem? h0] at this
    rw [code_one, this, Option.getD_some, getElem!_eq_of_getElem? hF0]
  have hstep : ∀ x ∈ L, ∀ j < gs.size, f (x * s j) = f x * h j := by
    intro x hx j hj
    obtain ⟨k, hk⟩ := hpos x hx
    obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
    have hc := hcrit k hks j hj
    rw [hke, hgs j hj, ← code_mul] at hc
    apply w6code_injective
    rw [hf _ (mul_mem hx (Subgroup.subset_closure ⟨j, hj, rfl⟩)), w6code_mul (f x) (h j),
      hf x hx, appF, appF, hk, Option.getD_some, ← hhs j hj]
    split at hc
    · rename_i k' hk'
      rw [hk', Option.getD_some]
      exact of_decide_eq_true hc
    · cases hc
  have hgen : ∀ j < gs.size, f (s j) = h j := by
    intro j hj
    have := hstep 1 (one_mem _) j hj
    rwa [one_mul, hf1, one_mul] at this
  have hmulf := map_mul_of_forall_mem hf1 (S := s '' Set.Iio gs.size) (by
    rintro x hx _ ⟨j, hj, rfl⟩
    rw [hstep x hx j hj, hgen j hj])
  have hinj' : ∀ i < F.size, (firstIndex F)[F[i]!]? = some i := by
    unfold injOK at hinj
    simpa only [allLt_iff, decide_eq_true_eq] using hinj
  let φ : L →* Wr 6 :=
    { toFun := fun x => f x
      map_one' := hf1
      map_mul' := fun x y => hmulf y y.2 x x.2 }
  refine ⟨φ, fun x y hxy => ?_, fun x => hfm x x.2, fun x => hf x x.2⟩
  have hxy' : f x = f y := hxy
  obtain ⟨k, hk⟩ := hpos x x.2
  obtain ⟨k', hk'⟩ := hpos y y.2
  have e := congrArg w6code hxy'
  rw [hf x x.2, hf y y.2, appF, appF, hk, hk', Option.getD_some, Option.getD_some] at e
  have hks := (Enum.lookup_spec hk).1
  have hks' := (Enum.lookup_spec hk').1
  have i1 := hinj' k (by rw [hsize]; exact hks)
  have i2 := hinj' k' (by rw [hsize]; exact hks')
  rw [e] at i1
  have hkk : k = k' := Option.some.inj (i1.symm.trans i2)
  subst hkk
  exact Subtype.ext (code_injective ((Enum.lookup_spec hk).2.symm.trans (Enum.lookup_spec hk').2))

@[expose] def w6Img (j : ℕ) : Wr 6 := if j = 0 then w6Img0 else w6Img1

theorem w6Hs_get {j : ℕ} (hj : j < 2) : (w6Hs ())[j]! = w6code (w6Img j) := by
  interval_cases j <;> rfl

theorem closure_w6Img_le : Subgroup.closure (w6Img '' Set.Iio 2) ≤ W6 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  unfold w6Img
  split_ifs
  · show wsum w6Img0 = 0
    decide
  · show wsum w6Img1 = 0
    decide

section Hom


theorem w6IsoCheck_holds : w6IsoCheck () = true := Certificates.certificate550851

theorem exists_hom_Hhat_W6 : ∃ φ : ↥Hhat →* Wr 6, Function.Injective φ ∧ (∀ x, φ x ∈ W6) ∧
    φ ⟨alpha, alpha_mem_Hhat⟩ = allOnes 6 := by
  have h := w6IsoCheck_holds
  simp only [w6IsoCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨haut, hα⟩ := h
  have hgs : ∀ j < (gH ()).size, (gH ())[j]! = code (hfam j) :=
    fun j hj => gH_get (size_gH ▸ hj)
  have hhs : ∀ j < (gH ()).size, (w6Hs ())[j]! = w6code (w6Img j) :=
    fun j hj => w6Hs_get (size_gH ▸ hj)
  obtain ⟨φ, hφ, hmem, hcode⟩ := exists_w6Hom_of_autOK hgs hhs enumCheck_spec.2.2 haut
  have hH : Hhat = Subgroup.closure (hfam '' Set.Iio (gH ()).size) := by
    rw [size_gH]
    exact Hhat_eq_closure
  have hle : Subgroup.closure (w6Img '' Set.Iio (gH ()).size) ≤ W6 := by
    rw [size_gH]
    exact closure_w6Img_le
  refine ⟨φ.comp (MulEquiv.subgroupCongr hH).toMonoidHom,
    hφ.comp (MulEquiv.subgroupCongr hH).injective,
    fun x => hle (hmem ((MulEquiv.subgroupCongr hH) x)), ?_⟩
  apply w6code_injective
  rw [MonoidHom.comp_apply, hcode]
  exact (congrArg (appF (enumH ()) (buildF (enumH ()) (w6Hs ()))) (code_alpha)).trans hα

end Hom

theorem commutator_eq_map {G : Type*} [Group G] (H : Subgroup G) :
    ⁅H, H⁆ = (commutator ↥H).map H.subtype := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem mem_commutator_self_iff {G : Type*} [Group G] (H : Subgroup G) (x : ↥H) :
    (x : G) ∈ ⁅H, H⁆ ↔ x ∈ commutator ↥H := by
  rw [commutator_eq_map H]
  exact Subgroup.mem_map_iff_mem H.subtype_injective

theorem map_commutator_top_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (commutator A).map e.toMonoidHom = commutator B := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem mem_commutator_iff_of_mulEquiv {G G' : Type*} [Group G] [Group G'] {H : Subgroup G}
    {K : Subgroup G'} (e : ↥H ≃* ↥K) (x : ↥H) :
    (x : G) ∈ ⁅H, H⁆ ↔ ((e x : ↥K) : G') ∈ ⁅K, K⁆ := by
  rw [mem_commutator_self_iff, mem_commutator_self_iff, ← map_commutator_top_of_mulEquiv e]
  exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm

section Iso


theorem exists_Hhat_mulEquiv_W6 :
    ∃ e : ↥Hhat ≃* ↥W6, (e ⟨alpha, alpha_mem_Hhat⟩ : Wr 6) = allOnes 6 := by
  obtain ⟨φ, hφ, hW, hα⟩ := exists_hom_Hhat_W6
  let ψ : ↥Hhat →* ↥W6 := φ.codRestrict W6 hW
  have hψ : Function.Injective ψ := fun x y h => hφ (congrArg Subtype.val h)
  have hbij : Function.Bijective ψ :=
    hψ.bijective_of_nat_card_le (by rw [card_W6, card_Hhat])
  exact ⟨MulEquiv.ofBijective ψ hbij, hα⟩

theorem commutator_W6 : ⁅W6, W6⁆ = aeSub 6 := by
  obtain ⟨e, -⟩ := exists_Hhat_mulEquiv_W6
  refine Subgroup.eq_of_le_of_card_ge commutator_W6_le ?_
  rw [card_aeSub_six]
  have hcard : Nat.card ↥(⁅W6, W6⁆) = Nat.card ↥E0 := by
    rw [E0, commutator_eq_map W6, commutator_eq_map Hhat,
      Subgroup.card_map_of_injective W6.subtype_injective,
      Subgroup.card_map_of_injective Hhat.subtype_injective,
      ← map_commutator_top_of_mulEquiv e, Subgroup.card_map_of_injective e.injective]
  rw [hcard, card_E0]

theorem exists_W6_mulEquiv_Hhat : ∃ f : ↥W6 ≃* ↥Hhat,
    (f ⟨allOnes 6, allOnes_mem_W6⟩ : StatedSp 3 (ZMod 2)) = alpha ∧
      ((aeSub 6).subgroupOf W6).map f.toMonoidHom = E0.subgroupOf Hhat := by
  obtain ⟨e, he⟩ := exists_Hhat_mulEquiv_W6
  refine ⟨e.symm, ?_, ?_⟩
  · have h1 : e.symm ⟨allOnes 6, allOnes_mem_W6⟩ = ⟨alpha, alpha_mem_Hhat⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext he.symm
    rw [h1]
  · ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      MulEquiv.symm_symm, ← commutator_W6]
    exact (mem_commutator_iff_of_mulEquiv e y).symm

end Iso

end CFSG.ClassicalInvolution.Sp62Rec

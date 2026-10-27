module

public import CFSG.ClassicalInvolution.Solomon73.YamakiTables
public import CFSG.ClassicalInvolution.Q3.E64Ker.Model
public import Certificates.Certificate550831

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open
  CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem size_wcode (a : Wr 7) : (wcode a).size = 64 := Array.size_ofFn

theorem wcode_get (a : Wr 7) {p : ℕ} (hp : p < 64) :
    (wcode a)[p]! = if p < 14 then wPt a p else p :=
  getElem!_ofFn_nat _ hp

theorem wPt_eq (a : Wr 7) (i : Fin 7) {c : ℕ} (hc : c < 2) :
    wPt a (i.val + 7 * c) = (a.perm i).val + 7 * ((c + (a.vec (a.perm i)).val) % 2) := by
  have h1 : (⟨(i.val + 7 * c) % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7) = i :=
    Fin.ext (by show (i.val + 7 * c) % 7 = i.val; omega)
  have h2 : (i.val + 7 * c) / 7 = c := by omega
  unfold wPt
  rw [h1, h2]

theorem exists_pt {p : ℕ} (hp : p < 14) : ∃ i : Fin 7, ∃ c < 2, p = i.val + 7 * c :=
  ⟨⟨p % 7, Nat.mod_lt _ (by decide)⟩, p / 7, by omega, by simp only; omega⟩

theorem wPt_lt (a : Wr 7) {p : ℕ} (hp : p < 14) : wPt a p < 14 := by
  obtain ⟨i, c, hc, rfl⟩ := exists_pt hp
  rw [wPt_eq a i hc]
  have h1 := (a.perm i).isLt
  have h2 : (c + (a.vec (a.perm i)).val) % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

theorem wPt_mul (a b : Wr 7) {p : ℕ} (hp : p < 14) : wPt (a * b) p = wPt a (wPt b p) := by
  obtain ⟨i, c, hc, rfl⟩ := exists_pt hp
  have hc' : (c + (b.vec (b.perm i)).val) % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [wPt_eq _ i hc, wPt_eq b i hc, wPt_eq a (b.perm i) hc']
  have hperm : (a * b).perm i = a.perm (b.perm i) := rfl
  have hvec : (a * b).vec (a.perm (b.perm i)) = a.vec (a.perm (b.perm i)) + b.vec (b.perm i) := by
    rw [mul_vec, Equiv.symm_apply_apply]
  rw [hperm, hvec, ZMod.val_add]
  have h1 := ZMod.val_lt (a.vec (a.perm (b.perm i)))
  have h2 := ZMod.val_lt (b.vec (b.perm i))
  omega

theorem wcode_mul (a b : Wr 7) : wcode (a * b) = compA (wcode a) (wcode b) := by
  refine ext64 (size_wcode _) (size_compA _ _) fun p hp => ?_
  rw [compA_get _ _ hp, wcode_get _ hp, wcode_get b hp]
  by_cases h14 : p < 14
  · have h := wPt_lt b h14
    rw [if_pos h14, if_pos h14, wcode_get a (by omega), if_pos h, wPt_mul a b h14]
  · rw [if_neg h14, if_neg h14, wcode_get a hp, if_neg h14]

theorem wcode_one : wcode 1 = idA () := by
  refine ext64 (size_wcode _) size_idA fun p hp => ?_
  rw [wcode_get _ hp, idA_get hp]
  by_cases h14 : p < 14
  · rw [if_pos h14]
    obtain ⟨i, c, hc, rfl⟩ := exists_pt h14
    rw [wPt_eq _ i hc]
    show i.val + 7 * ((c + (0 : ZMod 2).val) % 2) = i.val + 7 * c
    rw [ZMod.val_zero, add_zero, Nat.mod_eq_of_lt hc]
  · rw [if_neg h14]

theorem wcode_injective : Function.Injective wcode := by
  intro a b h
  have hpt : ∀ i : Fin 7, wPt a i.val = wPt b i.val := by
    intro i
    have := congrArg (fun t => t[i.val]!) h
    rwa [wcode_get _ (by omega), wcode_get _ (by omega), if_pos (by omega),
      if_pos (by omega)] at this
  have hpt0 : ∀ i : Fin 7, (a.perm i).val + 7 * ((a.vec (a.perm i)).val % 2) =
      (b.perm i).val + 7 * ((b.vec (b.perm i)).val % 2) := by
    intro i
    have := hpt i
    rw [show i.val = i.val + 7 * 0 from rfl, wPt_eq a i (by norm_num),
      wPt_eq b i (by norm_num), zero_add, zero_add] at this
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

theorem exists_wr_of_autOK {E : Enum} {gs hs F : Array (Array ℕ)} {h : ℕ → Wr 7}
    (hhs : ∀ j < gs.size, hs[j]! = wcode (h j)) (htree : treeOK E gs = true)
    (haut : autOK E gs hs F = true) :
    ∀ i < E.elems.size, ∃ m ∈ Subgroup.closure (h '' Set.Iio gs.size), wcode m = F[i]! := by
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at htree
  simp only [autOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at haut
  obtain ⟨-, hall⟩ := htree
  obtain ⟨⟨⟨⟨-, hF0⟩, hFt⟩, -⟩, -⟩ := haut
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases hall i hi with rfl | ⟨⟨hp, hg⟩, -⟩
    · exact ⟨1, one_mem _, by rw [wcode_one, getElem!_eq_of_getElem? hF0]⟩
    · rcases hFt i hi with hi0 | hFi
      · subst hi0
        exact ⟨1, one_mem _, by rw [wcode_one, getElem!_eq_of_getElem? hF0]⟩
      · obtain ⟨m, hm, hme⟩ := ih _ hp (hp.trans hi)
        refine ⟨m * h E.gen[i]!, mul_mem hm (Subgroup.subset_closure ⟨_, hg, rfl⟩), ?_⟩
        rw [wcode_mul, hme, ← hhs _ hg, hFi]

def e64Img (j : ℕ) : Wr 7 := if j = 0 then e64H0 else e64H1

theorem e64Hs_get {j : ℕ} (hj : j < 2) : (e64Hs ())[j]! = wcode (e64Img j) := by
  interval_cases j <;> rfl

theorem e64H0_mem : e64H0 ∈ aeSubOver l32 := by
  refine Subgroup.mem_inf.mpr ⟨mem_aeSub.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  show ∀ s ∈ fanoLines, s.map e64H0.perm.toEmbedding ∈ fanoLines ∧
    s.map e64H0.perm⁻¹.toEmbedding ∈ fanoLines
  decide +kernel

theorem e64H1_mem : e64H1 ∈ aeSubOver l32 := by
  refine Subgroup.mem_inf.mpr ⟨mem_aeSub.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  show ∀ s ∈ fanoLines, s.map e64H1.perm.toEmbedding ∈ fanoLines ∧
    s.map e64H1.perm⁻¹.toEmbedding ∈ fanoLines
  decide +kernel

theorem closure_e64Img_le : Subgroup.closure (e64Img '' Set.Iio 2) ≤ aeSubOver l32 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  unfold e64Img
  split_ifs
  · exact e64H0_mem
  · exact e64H1_mem

section Card


theorem card_aeSubOver_l32_le : Nat.card (aeSubOver l32) ≤ 10752 := by
  obtain ⟨-, -, -, -, -, -, h168, h64⟩ := Q3.E64Ker.model_check
  have hv : ∀ a : ↥(aeSubOver l32), (a : Wr 7).vec ∈ Q3.E64Data.evenFin () := by
    intro a
    simp only [Q3.E64Data.evenFin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact a.2.1.1
  have hp : ∀ a : ↥(aeSubOver l32), (a : Wr 7).perm ∈ Q3.E64Data.l32Fin () := by
    intro a
    simp only [Q3.E64Data.l32Fin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a.2.2, a.2.1.2⟩
  have hinj : Function.Injective fun a : ↥(aeSubOver l32) =>
      ((⟨(a : Wr 7).vec, hv a⟩ : ↥(Q3.E64Data.evenFin ())),
        (⟨(a : Wr 7).perm, hp a⟩ : ↥(Q3.E64Data.l32Fin ()))) := by
    intro a b hab
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hab
    exact Subtype.ext (Wr.ext hab.1 hab.2)
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_eq_finsetCard, Nat.card_eq_finsetCard, h64, h168] at h

theorem card_e64Sub_le : Nat.card e64Sub ≤ 10752 := by
  refine le_trans (Nat.card_le_card_of_surjective
    (fun a : ↥(aeSubOver l32) => (⟨mkQ 7 a, Subgroup.mem_map_of_mem _ a.2⟩ : ↥e64Sub)) ?_)
    card_aeSubOver_l32_le
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  exact ⟨⟨a, ha⟩, rfl⟩

end Card

theorem exists_wrHom_of_autOK {E : Enum} {gs hs F : Array (Array ℕ)}
    {s : ℕ → StatedSp 3 (ZMod 2)} {h : ℕ → Wr 7}
    (hgs : ∀ j < gs.size, gs[j]! = code (s j)) (hhs : ∀ j < gs.size, hs[j]! = wcode (h j))
    (henum : enumOK E gs = true) (haut : autOK E gs hs F = true) :
    ∃ φ : ↥(Subgroup.closure (s '' Set.Iio gs.size)) →* Wr 7, Function.Injective φ ∧
      ∀ x, φ x ∈ Subgroup.closure (h '' Set.Iio gs.size) := by
  set L := Subgroup.closure (s '' Set.Iio gs.size)
  have htree : treeOK E gs = true := by
    simp only [enumOK, Bool.and_eq_true] at henum
    exact henum.1.1
  have hnodup : nodupOK E = true := by
    simp only [enumOK, Bool.and_eq_true] at henum
    exact henum.2
  have hFw := exists_wr_of_autOK hhs htree haut
  have haut' := haut
  simp only [autOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at haut'
  obtain ⟨⟨⟨⟨hsize, hF0⟩, -⟩, hcrit⟩, hinj⟩ := haut'
  have hpos : ∀ x ∈ L, ∃ k, E.lookup (code x) = some k :=
    fun x hx => Option.isSome_iff_exists.mp (lookup_isSome_of_mem_closure hgs henum hx)
  have hex : ∀ x ∈ L, ∃ m ∈ Subgroup.closure (h '' Set.Iio gs.size),
      wcode m = appF E F (code x) := by
    intro x hx
    obtain ⟨k, hk⟩ := hpos x hx
    obtain ⟨m, hm, hme⟩ := hFw k (Enum.lookup_spec hk).1
    exact ⟨m, hm, by rw [hme, appF, hk, Option.getD_some]⟩
  obtain ⟨f, hf, hfm⟩ : ∃ f : StatedSp 3 (ZMod 2) → Wr 7,
      (∀ x ∈ L, wcode (f x) = appF E F (code x)) ∧
        ∀ x ∈ L, f x ∈ Subgroup.closure (h '' Set.Iio gs.size) := by
    classical
    refine ⟨fun x => if hx : ∃ m, wcode m = appF E F (code x) then hx.choose else 1, ?_, ?_⟩
    · intro x hx
      obtain ⟨m, -, hme⟩ := hex x hx
      have hx' : ∃ m, wcode m = appF E F (code x) := ⟨m, hme⟩
      simp only [dif_pos hx']
      exact hx'.choose_spec
    · intro x hx
      obtain ⟨m, hm, hme⟩ := hex x hx
      have hx' : ∃ m, wcode m = appF E F (code x) := ⟨m, hme⟩
      simp only [dif_pos hx']
      rw [wcode_injective (hx'.choose_spec.trans hme.symm)]
      exact hm
  have hf1 : f 1 = 1 := by
    apply wcode_injective
    rw [hf 1 (one_mem _), wcode_one, appF]
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
    apply wcode_injective
    rw [hf _ (mul_mem hx (Subgroup.subset_closure ⟨j, hj, rfl⟩)), wcode_mul (f x) (h j),
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
  let φ : L →* Wr 7 :=
    { toFun := fun x => f x
      map_one' := hf1
      map_mul' := fun x y => hmulf y y.2 x x.2 }
  refine ⟨φ, fun x y hxy => ?_, fun x => hfm x x.2⟩
  have hxy' : f x = f y := hxy
  obtain ⟨k, hk⟩ := hpos x x.2
  obtain ⟨k', hk'⟩ := hpos y y.2
  have e := congrArg wcode hxy'
  rw [hf x x.2, hf y y.2, appF, appF, hk, hk', Option.getD_some, Option.getD_some] at e
  have hks := (Enum.lookup_spec hk).1
  have hks' := (Enum.lookup_spec hk').1
  have i1 := hinj' k (by rw [hsize]; exact hks)
  have i2 := hinj' k' (by rw [hsize]; exact hks')
  rw [e] at i1
  have hkk : k = k' := Option.some.inj (i1.symm.trans i2)
  subst hkk
  exact Subtype.ext (code_injective ((Enum.lookup_spec hk).2.symm.trans (Enum.lookup_spec hk').2))

section Hom


theorem e64IsoCheck_holds :
    autOK (enumN ()) (gN ()) (e64Hs ()) (buildF (enumN ()) (e64Hs ())) = true :=
  Certificates.certificate550831

theorem exists_hom_N0 :
    ∃ φ : ↥N0 →* Wr 7, Function.Injective φ ∧ ∀ x, φ x ∈ aeSubOver l32 := by
  have hgs : ∀ j < (gN ()).size, (gN ())[j]! = code (nfam j) :=
    fun j hj => gN_get (size_gN ▸ hj)
  have hhs : ∀ j < (gN ()).size, (e64Hs ())[j]! = wcode (e64Img j) :=
    fun j hj => e64Hs_get (size_gN ▸ hj)
  obtain ⟨φ, hφ, hmem⟩ := exists_wrHom_of_autOK hgs hhs enumCheck_spec.2.1 e64IsoCheck_holds
  have hN0 : N0 = Subgroup.closure (nfam '' Set.Iio (gN ()).size) := by
    rw [size_gN]
    exact N0_eq_closure
  refine ⟨φ.comp (MulEquiv.subgroupCongr hN0).toMonoidHom,
    hφ.comp (MulEquiv.subgroupCongr hN0).injective, fun x => ?_⟩
  have hle : Subgroup.closure (e64Img '' Set.Iio (gN ()).size) ≤ aeSubOver l32 := by
    rw [size_gN]
    exact closure_e64Img_le
  exact hle (hmem ((MulEquiv.subgroupCongr hN0) x))

theorem nonempty_e64Sub_mulEquiv_N0 : Nonempty (↥CFSG.ClassicalInvolution.Q3.AE.e64Sub ≃* ↥N0) := by
  obtain ⟨φ, hφ, hmem⟩ := exists_hom_N0
  let ψ : ↥N0 →* ↥e64Sub :=
    ((mkQ 7).comp φ).codRestrict e64Sub fun x => Subgroup.mem_map_of_mem (mkQ 7) (hmem x)
  have hψ : Function.Injective ψ := by
    intro x y h
    have h' : mkQ 7 (φ x) = mkQ 7 (φ y) := congrArg Subtype.val h
    exact hφ (Q3.E64Ker.mkQ7_inj (hmem x).1 (hmem y).1 h')
  have hbij : Function.Bijective ψ :=
    hψ.bijective_of_nat_card_le (card_e64Sub_le.trans card_N0.ge)
  exact ⟨(MulEquiv.ofBijective ψ hbij).symm⟩

theorem card_e64Sub : Nat.card ↥CFSG.ClassicalInvolution.Q3.AE.e64Sub = 10752 := by
  obtain ⟨e⟩ := nonempty_e64Sub_mulEquiv_N0
  rw [Nat.card_congr e.toEquiv, card_N0]

end Hom

end CFSG.ClassicalInvolution.Sp62Rec

module

public import CFSG.ClassicalInvolution.Sp62Rec.NACountZ6Enum
public import CFSG.CGT.Foote82.T66.FoxH1
public import Certificates.Data.Foote82OmegaSixCent

public section

namespace CFSG.CGT.Foote82.OmegaSix

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec.Z6NA

@[expose] def vec6 (x₀ x₁ x₂ x₃ x₄ x₅ : ZMod 2) : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2 :=
  Sum.elim ![x₀, x₁] (Sum.elim ![x₂, x₃] ![x₄, x₅])

theorem eq_vec6 (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) :
    v = vec6 (v (.inl 0)) (v (.inl 1)) (v (.inr (.inl 0))) (v (.inr (.inl 1)))
      (v (.inr (.inr 0))) (v (.inr (.inr 1))) := by
  funext a
  rcases a with k | k | k <;> fin_cases k <;> rfl

theorem vcode_vec6_lt : ∀ x₀ x₁ x₂ x₃ x₄ x₅ : ZMod 2, vcode (vec6 x₀ x₁ x₂ x₃ x₄ x₅) < 64 := by
  decide

theorem cvec_vcode_vec6 : ∀ x₀ x₁ x₂ x₃ x₄ x₅ : ZMod 2,
    cvec (vcode (vec6 x₀ x₁ x₂ x₃ x₄ x₅)) = vec6 x₀ x₁ x₂ x₃ x₄ x₅ := by
  decide

theorem vcode_lt (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) : vcode v < 64 := by
  rw [eq_vec6 v]
  exact vcode_vec6_lt _ _ _ _ _ _

theorem cvec_vcode (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) : cvec (vcode v) = v := by
  rw [eq_vec6 v]
  exact cvec_vcode_vec6 _ _ _ _ _ _

theorem vcode_cvec : ∀ n < 64, vcode (cvec n) = n := by
  decide

theorem cvec_xor (n m : ℕ) : cvec (n ^^^ m) = cvec n + cvec m := by
  funext a
  simp only [cvec, Nat.testBit_xor, Pi.add_apply]
  cases n.testBit (bit6 a).val <;> cases m.testBit (bit6 a).val <;> decide

theorem isVecCode : FoxH1.IsVecCode 64 cvec vcode where
  code_lt := vcode_lt
  vec_code := cvec_vcode
  code_vec := vcode_cvec
  vec_xor := cvec_xor
  xor_lt _ hn _ hm := Nat.xor_lt_two_pow (n := 6) hn hm

theorem size_marr (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
    (marr A).size = 64 := Array.size_ofFn

theorem marr_get (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) {n : ℕ}
    (hn : n < 64) : (marr A)[n]! = vcode (A *ᵥ cvec n) :=
  getElem!_ofFn_nat _ hn

theorem mulVec_cvec (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2))
    {n : ℕ} (hn : n < 64) : A *ᵥ cvec n = cvec (marr A)[n]! := by
  rw [marr_get A hn, cvec_vcode]

theorem marr_mul (A B : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
    marr (A * B) = compA (marr A) (marr B) := by
  refine ext64 (size_marr _) (size_compA _ _) fun i hi => ?_
  rw [compA_get _ _ hi, marr_get B hi, marr_get A (vcode_lt _), cvec_vcode, marr_get _ hi,
    ← mulVec_mulVec]

theorem marr_one : marr 1 = idA () := by
  refine ext64 (size_marr _) size_idA fun i hi => ?_
  rw [marr_get _ hi, one_mulVec, vcode_cvec i hi, idA_get hi]

theorem marr_injective : Function.Injective marr := by
  intro A B h
  rw [ext_iff_mulVec]
  intro v
  rw [← cvec_vcode v, mulVec_cvec A (vcode_lt v), mulVec_cvec B (vcode_lt v), h]

theorem isActArr_marr {X : Type*} {act : X → (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) →
    Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2} {x : X}
    {A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (h : ∀ v, act x v = A *ᵥ v) : FoxH1.IsActArr act 64 cvec x (marr A) := fun k hk =>
  ⟨by rw [marr_get A hk]; exact vcode_lt _, by rw [h, mulVec_cvec A hk]⟩

@[expose] def glArr {H : Subgroup (GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2))} (x : H) : Array ℕ :=
  marr ((x : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
    Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2))

theorem isArrCode_glArr (H : Subgroup (GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2))) :
    IsArrCode (glArr (H := H)) where
  mul x y := by
    rw [glArr, glArr, glArr, Subgroup.coe_mul, Units.val_mul, marr_mul]
  one := by
    rw [glArr, Subgroup.coe_one, Units.val_one, marr_one]
  injective _ _ h := Subtype.ext (Units.ext (marr_injective h))

@[expose] def glCode (g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) : Array ℕ :=
  marr (g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2))

theorem isArrCode_glCode : IsArrCode glCode where
  mul x y := by rw [glCode, glCode, glCode, Units.val_mul, marr_mul]
  one := by rw [glCode, Units.val_one, marr_one]
  injective _ _ h := Units.ext (marr_injective h)

section Enum

variable {H : Type*} [Group H] {cd : H → Array ℕ}

theorem arr_prod_map (hc : IsArrCode cd) {s : ℕ → H} {gs : Array (Array ℕ)} :
    ∀ w : List ℕ, (∀ i ∈ w, gs[i]! = cd (s i)) → cd (w.map s).prod = wordA gs w
  | [], _ => by rw [List.map_nil, List.prod_nil, hc.one, wordA]
  | i :: w, hw => by
    rw [List.map_cons, List.prod_cons, hc.mul, wordA, hw i List.mem_cons_self,
      arr_prod_map hc w fun j hj => hw j (List.mem_cons_of_mem i hj)]

theorem card_closure_eq_of_enumOK [Finite H] (hc : IsArrCode cd) {E : Enum}
    {gs : Array (Array ℕ)} {s : ℕ → H} (hgs : ∀ j < gs.size, gs[j]! = cd (s j))
    (h : enumOK E gs = true) :
    Nat.card (Subgroup.closure (s '' Set.Iio gs.size)) = E.elems.size := by
  have htree : treeOK E gs = true := by
    simp only [enumOK, Bool.and_eq_true] at h
    exact h.1.1
  have hnodup : ∀ i < E.elems.size, E.lookup E.elems[i]! = some i := by
    simp only [enumOK, Bool.and_eq_true] at h
    simpa only [nodupOK, allLt_iff, decide_eq_true_eq] using h.2
  have hex := exists_mem_closure_of_treeOK hc hgs htree
  choose e he hec using hex
  have hbij : Function.Bijective fun i : Fin E.elems.size =>
      (⟨e i i.2, he i i.2⟩ : Subgroup.closure (s '' Set.Iio gs.size)) := by
    constructor
    · intro i j hij
      have hv : e i i.2 = e j j.2 := congrArg Subtype.val hij
      have hc' : E.elems[i.val]! = E.elems[j.val]! := by
        rw [← hec i i.2, ← hec j j.2, hv]
      have h1 := hnodup i i.2
      rw [hc', hnodup j j.2] at h1
      exact Fin.ext (Option.some.inj h1).symm
    · intro x
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (lookup_isSome_of_mem_closure hc hgs h x.2)
      obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
      exact ⟨⟨k, hks⟩, Subtype.ext (hc.injective ((hec k hks).trans hke))⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem exists_conj_of_conjTreeOK (hc : IsArrCode cd) {E : Enum} {gs gsInv : Array (Array ℕ)}
    {s : ℕ → H} (hgs : ∀ j < gs.size, gs[j]! = cd (s j))
    (hgsInv : ∀ j < gs.size, gsInv[j]! = cd (s j)⁻¹) {x : H}
    (h : conjTreeOK E gs gsInv (cd x) = true) :
    ∀ i < E.elems.size, ∃ g ∈ Subgroup.closure (s '' Set.Iio gs.size),
      cd (g * x * g⁻¹) = E.elems[i]! := by
  simp only [conjTreeOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at h
  obtain ⟨h0, hall⟩ := h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases hall i hi with rfl | ⟨⟨hp, hg⟩, he⟩
    · exact ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one, getElem!_eq_of_getElem? h0]⟩
    · obtain ⟨g, hg', hge⟩ := ih _ hp (hp.trans hi)
      refine ⟨s E.gen[i]! * g, mul_mem (Subgroup.subset_closure ⟨_, hg, rfl⟩) hg', ?_⟩
      rw [he, ← hge, hgs _ hg, hgsInv _ hg, ← hc.mul, ← hc.mul]
      congr 1
      group

end Enum

end CFSG.CGT.Foote82.OmegaSix

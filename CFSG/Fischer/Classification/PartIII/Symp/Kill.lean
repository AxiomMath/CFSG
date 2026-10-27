module

public import CFSG.Fischer.Classification.PartIII.Symp.Count
public import CFSG.Fischer.Classification.PartIII.Symp.Sym
public import CFSG.Fischer.Classification.Symplectic.Recognition

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open Symplectic LocalSymp Matrix

variable {X : Type} [Group X] {E : Set X}

namespace LocalSymp

theorem commute_iff_map {Y : Type} [Group Y] (φ : X ≃* Y) (a b : X) :
    φ a * φ b = φ b * φ a ↔ a * b = b * a := by
  rw [← map_mul, ← map_mul, φ.injective.eq_iff]

section Transport

variable {Y : Type} [Group Y] (φ : X ≃* Y) {F : Set Y} (hEF : ∀ g, g ∈ E ↔ φ g ∈ F)
include hEF

theorem localClass_eq_preimage (a : X) : LocalClass E a = φ ⁻¹' LocalClass F (φ a) := by
  ext g
  simp only [Set.mem_preimage, mem_localClass, hEF, φ.injective.ne_iff, commute_iff_map]

theorem ncard_muSet_of_mulEquiv (a b : X) :
    (muSet E a b).ncard = (muSet F (φ a) (φ b)).ncard := by
  rw [show muSet E a b = φ ⁻¹' muSet F (φ a) (φ b) by
    rw [muSet, muSet, localClass_eq_preimage φ hEF, localClass_eq_preimage φ hEF,
      Set.preimage_inter]]
  exact Set.ncard_preimage_of_injective_subset_range φ.injective (by simp)

theorem ncard_of_mulEquiv : E.ncard = F.ncard := by
  rw [show E = φ ⁻¹' F from Set.ext hEF]
  exact Set.ncard_preimage_of_injective_subset_range φ.injective (by simp)

theorem isSymplecticType_of_mulEquiv (hF : IsSymplecticType F) : IsSymplecticType E := by
  intro d hd e he z hz hde
  have hded : φ d * φ e * φ d = φ (d * e * d) := by rw [map_mul, map_mul]
  have h := hF (φ d) ((hEF d).1 hd) (φ e) ((hEF e).1 he) (φ z) ((hEF z).1 hz)
    (by rwa [Ne, commute_iff_map])
  rwa [commute_iff_map, commute_iff_map, hded, commute_iff_map] at h

end Transport

section LinearModel

variable {H : Type} [Group H] {k : ℕ} {M : Subgroup (GL (Fin k) (ZMod 2))}

@[expose] def modelAct (φ : H ≃* M) (h : H) (x : Fin k → ZMod 2) : Fin k → ZMod 2 :=
  ((φ h : GL (Fin k) (ZMod 2)) : Matrix (Fin k) (Fin k) (ZMod 2)) *ᵥ x

theorem modelAct_mul (φ : H ≃* M) (a b : H) :
    modelAct φ (a * b) = modelAct φ a ∘ modelAct φ b := by
  funext x
  simp only [modelAct, Function.comp_apply, map_mul, Subgroup.coe_mul, Units.val_mul,
    Matrix.mulVec_mulVec]

theorem modelAct_injective (φ : H ≃* M) : Function.Injective (modelAct φ) := fun _ _ h =>
  φ.injective (Subtype.ext (gl_ext fun x => congrFun h x))

theorem modelAct_symm (φ : H ≃* M) {g : GL (Fin k) (ZMod 2)} (hg : g ∈ M) :
    modelAct φ (φ.symm ⟨g, hg⟩) = fun x => (g : Matrix (Fin k) (Fin k) (ZMod 2)) *ᵥ x := by
  funext x
  simp only [modelAct, MulEquiv.apply_symm_apply]

end LinearModel

theorem ncard_ne_zero_add_one {V : Type*} [Zero V] [Finite V] {S : Set V} (h0 : (0 : V) ∈ S) :
    {w | w ≠ 0 ∧ w ∈ S}.ncard + 1 = S.ncard := by
  rw [← Set.ncard_insert_of_notMem (fun h => h.1 rfl)]
  congr 1
  ext w
  by_cases hw : w = 0 <;> simp [hw, h0]

end LocalSymp

section ModelSymp

variable {H : Type} [Group H] {F : Set H}

theorem isSymplecticType_of_fischerLinearModel {k : ℕ} {M : Subgroup (GL (Fin k) (ZMod 2))}
    (B : LinearMap.BilinForm (ZMod 2) (Fin k → ZMod 2)) (hsymm : ∀ x y, B x y = B y x)
    {β : (Fin k → ZMod 2) → (Fin k → ZMod 2) → ZMod 2} (hβ : ∀ x y, β x y = B x y)
    {P : (Fin k → ZMod 2) → Prop} (hPB : ∀ v, P v → B v v = 0)
    (hmod : fischerLinearModel F M (fischerTransvections β P)) : IsSymplecticType F := by
  obtain ⟨φ, hφ⟩ := hmod
  refine isSymplecticType_of_tv B (modelAct φ) hsymm (modelAct_mul φ) (modelAct_injective φ)
    fun f hf => ?_
  obtain ⟨v, hv, h⟩ := (hφ f).1 hf
  refine ⟨v, hPB v hv, funext fun x => ?_⟩
  rw [tv_apply, ← hβ]
  exact h x

theorem isSymplecticType_of_o {k : ℕ} {Q : QuadraticForm (ZMod 2) (Fin k → ZMod 2)}
    (hmod : fischerLinearModel F (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) : IsSymplecticType F :=
  isSymplecticType_of_fischerLinearModel (QuadraticMap.polarBilin Q)
    (fun x y => by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
        QuadraticMap.polar_comm])
    (fun x y => (QuadraticMap.polarBilin_apply_apply Q x y).symm)
    (fun v _ => by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul,
        zmod2_add_self])
    hmod

theorem isSymplecticType_of_perm {n : ℕ} (φ : H ≃* Equiv.Perm (Fin n))
    (hφ : ∀ g, g ∈ F ↔ (φ g).IsSwap) : IsSymplecticType F :=
  isSymplecticType_of_mulEquiv φ (F := {σ | σ.IsSwap}) hφ isSymplecticType_isSwap

end ModelSymp

theorem Pair.exists_four_mul_le_of_tv (hH : Hyp X E) (hna : NonabelianCommutator X)
    (hnot : ¬ IsSymplecticType E) {d : X} (hd : d ∈ E) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (B : LinearMap.BilinForm (ZMod 2) V)
    (hsymm : ∀ x y, B x y = B y x) (hnd : ∀ x, (∀ y, B y x = 0) → x = 0)
    (act : LocalQuotient E d → V → V) (hmul : ∀ a b, act (a * b) = act a ∘ act b)
    (hinj : Function.Injective act) {P : V → Prop} (hP0 : ∀ v, P v → v ≠ 0)
    (hPB : ∀ v, P v → B v v = 0) (hF : ∀ f ∈ LocalImages E d, ∃ v, P v ∧ act f = tv B v)
    (hsurj : ∀ w, P w → ∃ f ∈ LocalImages E d, act f = tv B w) :
    ∃ s s', P s ∧ P s' ∧ B s s' = 1 ∧
      4 * (1 + {w | P w ∧ B w s = 0 ∧ B w s' = 0}.ncard) ≤ {v | P v}.ncard := by
  obtain ⟨hP, hZ, hS⟩ := hH
  have := Pair.finite hP
  have hsymp : IsSymplecticType (LocalImages E d) :=
    isSymplecticType_of_tv B act hsymm hmul hinj fun f hf => by
      obtain ⟨v, hv, h⟩ := hF f hf
      exact ⟨v, hPB v hv, h⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := Pair.exists_not_commute (Pair.pair_localQuotient hP hZ hS hna hd)
    (Pair.center_localQuotient hP hZ hS hd)
  obtain ⟨s, hs, h₀⟩ := hF x hx
  obtain ⟨s', hs', h₁⟩ := hF y hy
  have hss' := bilin_eq_one_of_not_commute B act hsymm hmul hinj h₀ h₁ hxy
  have h4 := Pair.four_mul_le_ncard_localImages ⟨hP, hZ, hS⟩ hna hnot hd hsymp hx hy hxy
  have hμ := ncard_le_ncard_muSet_of_tv B act hsymm hnd hmul hinj hP0 hsurj h₀ h₁ hss'
  have hD := ncard_le_of_tv B act hinj hF
  exact ⟨s, s', hs, hs', hss', by omega⟩

variable {G : Type} [Group G] {D : Set G}

theorem false_of_localSym (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hnot : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D) {n : ℕ} (hn : n = 3 ∨ 6 ≤ n)
    (φ : LocalQuotient D d ≃* Equiv.Perm (Fin n)) (hφ : ∀ g, g ∈ LocalImages D d ↔ (φ g).IsSwap) :
    False := by
  have h3 : 3 ≤ n := by omega
  have hφ' : ∀ g, g ∈ LocalImages D d ↔ φ g ∈ {σ : Equiv.Perm (Fin n) | σ.IsSwap} := hφ
  have hsymp := isSymplecticType_of_mulEquiv φ hφ' isSymplecticType_isSwap
  have hx : φ.symm (Equiv.swap (i0 h3) (i1 h3)) ∈ LocalImages D d := by
    rw [hφ', MulEquiv.apply_symm_apply]
    exact ⟨_, _, i0_ne_i1 h3, rfl⟩
  have hy : φ.symm (Equiv.swap (i1 h3) (i2 h3)) ∈ LocalImages D d := by
    rw [hφ', MulEquiv.apply_symm_apply]
    exact ⟨_, _, i1_ne_i2 h3, rfl⟩
  have hxy : φ.symm (Equiv.swap (i0 h3) (i1 h3)) * φ.symm (Equiv.swap (i1 h3) (i2 h3)) ≠
      φ.symm (Equiv.swap (i1 h3) (i2 h3)) * φ.symm (Equiv.swap (i0 h3) (i1 h3)) := by
    rw [Ne, ← commute_iff_map φ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact swap_mul_swap_ne h3
  have h4 := Pair.four_mul_le_ncard_localImages hH hna hnot hd hsymp hx hy hxy
  rw [ncard_muSet_of_mulEquiv φ hφ', ncard_of_mulEquiv φ hφ', MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply] at h4
  have h5 := choose_le_ncard_muSet_isSwap h3
  have h6 := ncard_isSwap_le (n := n)
  have h7 := choose_two_lt hn
  omega

theorem false_of_localSp (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hnot : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D) {m : ℕ}
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)} (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hmod : fischerLinearModel (LocalImages D d)
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) : False := by
  obtain ⟨φ, hφ⟩ := hmod
  have hsymm : ∀ x y, b x y = b y x := fun x y => by
    rw [← LinearMap.IsAlt.neg halt x y, ZMod.neg_eq_self_mod_two]
  have hnd' : ∀ x, (∀ y, b y x = 0) → x = 0 := fun x hx =>
    hnd x fun y => by rw [hsymm]; exact hx y
  have hF : ∀ f ∈ LocalImages D d, ∃ v, v ≠ 0 ∧ modelAct φ f = tv b v := by
    intro f hf
    obtain ⟨v, hv, h⟩ := (hφ f).1 hf
    exact ⟨v, hv, funext h⟩
  have hsurj : ∀ w, w ≠ 0 → ∃ f ∈ LocalImages D d, modelAct φ f = tv b w := by
    intro w hw
    refine ⟨φ.symm ⟨_, sympTransvectionGL_mem_fischerMatrixGroup (halt := halt) w⟩, ?_, ?_⟩
    · rw [hφ, MulEquiv.apply_symm_apply]
      exact sympTransvectionGL_mem_fischerTransvections hw
    · rw [modelAct_symm]
      funext x
      exact sympTransvectionGL_mulVec w x
  obtain ⟨s, s', -, -, hss', h⟩ := Pair.exists_four_mul_le_of_tv hH hna hnot hd b hsymm hnd'
    (modelAct φ) (modelAct_mul φ) (modelAct_injective φ) (fun v hv => hv) (fun v _ => halt v)
    hF hsurj
  have hV := card_eq_four_mul b (halt s) (halt s') hss' (by rw [hsymm]; exact hss')
  have h1 := ncard_ne_zero_add_one (S := {w | b w s = 0 ∧ b w s' = 0})
    (by simp only [Set.mem_ofPred_eq, map_zero, LinearMap.zero_apply, and_self])
  have h2 := ncard_ne_zero_add_one (S := (Set.univ : Set (Fin (2 * m) → ZMod 2))) trivial
  simp only [Set.mem_ofPred_eq, Set.mem_univ, and_true, Set.ncard_univ] at h1 h2
  omega

theorem false_of_localO (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hnot : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D) {m : ℕ} (hm : 1 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hQ : {v | Q v = 1}.ncard ≤ 2 ^ (2 * m - 1))
    (hmod : fischerLinearModel (LocalImages D d)
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) : False := by
  obtain ⟨φ, hφ⟩ := hmod
  set B := QuadraticMap.polarBilin Q
  have hpol : ∀ x y, QuadraticMap.polar Q x y = B x y := fun x y =>
    (QuadraticMap.polarBilin_apply_apply Q x y).symm
  have hsymm : ∀ x y, B x y = B y x := fun x y => by
    rw [← hpol, ← hpol, QuadraticMap.polar_comm]
  have halt : ∀ x, B x x = 0 := fun x => by
    rw [← hpol, QuadraticMap.polar_self, two_nsmul, zmod2_add_self]
  have hnd' : ∀ x, (∀ y, B y x = 0) → x = 0 := fun x hx =>
    hnd x fun y => by rw [hpol, hsymm]; exact hx y
  have hP0 : ∀ v, Q v = 1 → v ≠ 0 := by
    rintro v hv rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have hF : ∀ f ∈ LocalImages D d, ∃ v, Q v = 1 ∧ modelAct φ f = tv B v := by
    intro f hf
    obtain ⟨v, hv, h⟩ := (hφ f).1 hf
    refine ⟨v, hv, funext fun x => ?_⟩
    rw [tv_apply, ← hpol]
    exact h x
  have hsurj : ∀ w, Q w = 1 → ∃ f ∈ LocalImages D d, modelAct φ f = tv B w := by
    intro w hw
    refine ⟨φ.symm ⟨_, fischerTransvections_polar_subset
      (orthTransvectionGL_mem_fischerTransvections hw)⟩, ?_, ?_⟩
    · rw [hφ, MulEquiv.apply_symm_apply]
      exact orthTransvectionGL_mem_fischerTransvections hw
    · rw [modelAct_symm]
      funext x
      rw [tv_apply, ← hpol]
      exact orthTransvectionGL_mulVec hw x
  obtain ⟨s, s', hs, hs', hss', h⟩ := Pair.exists_four_mul_le_of_tv hH hna hnot hd B hsymm hnd'
    (modelAct φ) (modelAct_mul φ) (modelAct_injective φ) hP0 (fun v _ => halt v) hF hsurj
  have hV := card_eq_four_mul B (halt s) (halt s') hss' (by rw [hsymm]; exact hss')
  have hcount := ncard_quadratic_add B Q hpol hs hs' hss'
  have hcard : Nat.card (Fin (2 * m) → ZMod 2) = 2 * 2 ^ (2 * m - 1) := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_succ']
    congr 1
    omega
  omega

end CFSG.Fischer.Classification

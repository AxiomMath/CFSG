module

public import CFSG.Quasithin.SteinbergCBG2TwoBits
public import CFSG.ClassicalGroups.Orthogonal.ReflectPairs
public import CFSG.LocalAnalysis.StandardType.SpEightSymplecticGeneration
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.OrthPlanes

open CFSG.Quasithin.SteinbergCB.G2Two Matrix CFSG.Open

variable {ι : Type} [Fintype ι] [DecidableEq ι]

section Codes

variable {n : ℕ}

@[expose] def pt (e : ι ≃ Fin n) (x : ℕ) : ι → ZMod 2 := toV n x ∘ e

@[expose] def code (e : ι ≃ Fin n) (w : ι → ZMod 2) : ℕ := ofV (w ∘ e.symm)

theorem pt_code (e : ι ≃ Fin n) (w : ι → ZMod 2) : pt e (code e w) = w := by
  funext i
  simp only [pt, code, Function.comp_apply, toV_ofV, Equiv.symm_apply_apply]

theorem code_lt (e : ι ≃ Fin n) (w : ι → ZMod 2) : code e w < 2 ^ n :=
  ofV_lt _

theorem exists_mem_of_certOK (e : ι ≃ Fin n) (H : Subgroup (GL ι (ZMod 2)))
    (gens : List (List ℕ))
    (hgens : ∀ k < gens.length, ∃ h ∈ H, ∀ x < 2 ^ n,
      (h : Matrix ι ι (ZMod 2)) *ᵥ pt e x = pt e (mApp (gens.getD k []) x))
    (v₀ : ℕ) : ∀ (cert : List (ℕ × ℕ × ℕ)) (seen : List ℕ),
      (∀ s ∈ seen, s < 2 ^ n ∧ ∃ h ∈ H, (h : Matrix ι ι (ZMod 2)) *ᵥ pt e v₀ = pt e s) →
      certOK n gens seen cert = true →
      ∀ t ∈ cert, t.1 < 2 ^ n ∧ ∃ h ∈ H, (h : Matrix ι ι (ZMod 2)) *ᵥ pt e v₀ = pt e t.1
  | [], _, _, _ => by simp
  | (y, k, x) :: rest, seen, hseen, hc => by
    simp only [certOK, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq,
      beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨hx, hk⟩, hy⟩, hyx⟩, hrest⟩ := hc
    obtain ⟨g, hg, hgx⟩ := hgens k hk
    obtain ⟨hxlt, h, hh, hhx⟩ := hseen x hx
    have hyo : ∃ h ∈ H, (h : Matrix ι ι (ZMod 2)) *ᵥ pt e v₀ = pt e y :=
      ⟨g * h, H.mul_mem hg hh, by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hhx, hgx x hxlt, hyx]⟩
    have hseen' : ∀ s ∈ y :: seen, s < 2 ^ n ∧
        ∃ h ∈ H, (h : Matrix ι ι (ZMod 2)) *ᵥ pt e v₀ = pt e s := by
      intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact ⟨hy, hyo⟩
      · exact hseen s hs
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨hy, hyo⟩
    · exact exists_mem_of_certOK e H gens hgens v₀ rest (y :: seen) hseen' hrest t ht

theorem exists_mem_mulVec_of_certOK (e : ι ≃ Fin n) {H : Subgroup (GL ι (ZMod 2))}
    {gens : List (List ℕ)}
    (hgens : ∀ k < gens.length, ∃ h ∈ H, ∀ x < 2 ^ n,
      (h : Matrix ι ι (ZMod 2)) *ᵥ pt e x = pt e (mApp (gens.getD k []) x))
    {v₀ : ℕ} (hv₀ : v₀ < 2 ^ n) {cert : List (ℕ × ℕ × ℕ)}
    (hcert : certOK n gens [v₀] cert = true) {P : (ι → ZMod 2) → Prop}
    (hcover : ∀ x < 2 ^ n, P (pt e x) → x = v₀ ∨ x ∈ cert.map Prod.fst) (w : ι → ZMod 2)
    (hw : P w) : ∃ h ∈ H, (h : Matrix ι ι (ZMod 2)) *ᵥ pt e v₀ = w := by
  rw [← pt_code e w] at hw ⊢
  rcases hcover _ (code_lt e w) hw with h0 | hmem
  · exact ⟨1, H.one_mem, by rw [Units.val_one, Matrix.one_mulVec, h0]⟩
  · obtain ⟨t, ht, htw⟩ := List.mem_map.1 hmem
    have hsound := exists_mem_of_certOK e H gens hgens v₀ cert [v₀] (by
      intro s hs
      rw [List.mem_singleton.1 hs]
      exact ⟨hv₀, 1, H.one_mem, by rw [Units.val_one, Matrix.one_mulVec]⟩) hcert t ht
    rw [← htw]
    exact hsound.2

end Codes

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {X : Subgroup G} [Finite X]
    {g : G} (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  have hinj : Function.Injective (fun x : X => (⟨g * x * g⁻¹, h x x.2⟩ : X)) := fun a b hab =>
    Subtype.ext (by simpa using congrArg Subtype.val hab)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hinj ⟨_, hx⟩
  have hyx : (y : G) = x := by simpa using congrArg Subtype.val hy
  exact hyx ▸ y.2

theorem le_comap_sup_zpowers {G : Type*} [Group G] (φ : G →* G) {a b : G}
    (ha : φ a ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hb : φ b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤
      (Subgroup.zpowers a ⊔ Subgroup.zpowers b).comap φ :=
  sup_le (Subgroup.zpowers_le.2 ha) (Subgroup.zpowers_le.2 hb)

theorem mem_normalizer_sup_zpowers {G : Type*} [Group G] [Finite G] {a b g : G}
    (ha : g * a * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hb : g * b * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
  have hle := le_comap_sup_zpowers (MulAut.conj g).toMonoidHom (a := a) (b := b) ha hb
  exact mem_normalizer_of_conj_mem fun x hx => hle hx

section Symplectic

open CFSG.StandardType.SpEight

theorem sup_normalizer_eq_top_of_tvGL {X₁ X₂ : Subgroup ↥(StatedSp 4 (ZMod 2))} {w₀ : Vec}
    (h₀ : tvGL w₀ ∈ (Subgroup.normalizer (X₁ : Set ↥(StatedSp 4 (ZMod 2))) ⊔
      Subgroup.normalizer (X₂ : Set ↥(StatedSp 4 (ZMod 2)))).map (StatedSp 4 (ZMod 2)).subtype)
    (htr : ∀ w : Vec, w ≠ 0 → ∃ h ∈ (Subgroup.normalizer (X₁ : Set ↥(StatedSp 4 (ZMod 2))) ⊔
      Subgroup.normalizer (X₂ : Set ↥(StatedSp 4 (ZMod 2)))).map (StatedSp 4 (ZMod 2)).subtype,
      (h : Matrix Idx Idx (ZMod 2)) *ᵥ w₀ = w) :
    Subgroup.normalizer (X₁ : Set ↥(StatedSp 4 (ZMod 2))) ⊔
      Subgroup.normalizer (X₂ : Set ↥(StatedSp 4 (ZMod 2))) = ⊤ := by
  have hle : StatedSp 4 (ZMod 2) ≤ (Subgroup.normalizer (X₁ : Set ↥(StatedSp 4 (ZMod 2))) ⊔
      Subgroup.normalizer (X₂ : Set ↥(StatedSp 4 (ZMod 2)))).map (StatedSp 4 (ZMod 2)).subtype := by
    have hcl : Subgroup.closure {g | ∃ w : Vec, w ≠ 0 ∧ g = tvGL w} ≤
        (Subgroup.normalizer (X₁ : Set ↥(StatedSp 4 (ZMod 2))) ⊔
          Subgroup.normalizer (X₂ : Set ↥(StatedSp 4 (ZMod 2)))).map
            (StatedSp 4 (ZMod 2)).subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨h, hh, hhw⟩ := htr w hw
      rw [← hhw, ← mul_tvGL_mul_inv (Subgroup.map_subtype_le _ hh) w₀]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hh h₀) (Subgroup.inv_mem _ hh)
    rwa [← statedSp_eq_closure_tvGL] at hcl
  rw [eq_top_iff]
  intro g _
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 (hle g.2)
  rwa [Subtype.ext hyg] at hy

end Symplectic

section Reflections

variable {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} {Q₀ : (ι → ZMod 2) → ZMod 2}

@[expose] def reflM (Q₀ : (ι → ZMod 2) → ZMod 2) (v : ι → ZMod 2) : Matrix ι ι (ZMod 2) :=
  Matrix.of fun i j => (1 : Matrix ι ι (ZMod 2)) i j +
    v i * (Q₀ (Pi.single j 1 + v) - Q₀ (Pi.single j 1) - Q₀ v)

theorem reflM_mulVec (hQ : ⇑Q = Q₀) (v x : ι → ZMod 2) :
    reflM Q₀ v *ᵥ x = x + QuadraticMap.polar Q x v • v := by
  have hp : ∀ j, Q₀ (Pi.single j 1 + v) - Q₀ (Pi.single j 1) - Q₀ v =
      QuadraticMap.polar Q (Pi.single j 1) v := by
    intro j
    rw [← hQ]
    rfl
  have hsum : ∑ j, x j * QuadraticMap.polar Q (Pi.single j 1) v =
      QuadraticMap.polar Q x v := by
    have hx : x = ∑ j, x j • (Pi.single j 1 : ι → ZMod 2) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    calc ∑ j, x j * QuadraticMap.polar Q (Pi.single j 1) v
        = QuadraticMap.polarBilin Q (∑ j, x j • (Pi.single j 1 : ι → ZMod 2)) v := by
          rw [map_sum, LinearMap.sum_apply]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [LinearMap.map_smul, LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply,
            smul_eq_mul]
      _ = QuadraticMap.polar Q x v := by
          rw [← hx, QuadraticMap.polarBilin_apply_apply]
  funext i
  simp only [Matrix.mulVec, dotProduct, reflM, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp]
  rw [← hsum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem reflM_mul_self (hQ : ⇑Q = Q₀) (v : ι → ZMod 2) : reflM Q₀ v * reflM Q₀ v = 1 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, reflM_mulVec hQ, reflM_mulVec hQ, Matrix.one_mulVec,
    QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_self]
  have h2 : (2 : ℕ) • Q v = 0 := by
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero _
  rw [h2, smul_zero, add_zero, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul,
    add_zero]

@[expose] def reflGL (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) (Q₀ : (ι → ZMod 2) → ZMod 2)
    (hQ : ⇑Q = Q₀) (v : ι → ZMod 2) : GL ι (ZMod 2) :=
  ⟨reflM Q₀ v, reflM Q₀ v, reflM_mul_self hQ v, reflM_mul_self hQ v⟩

theorem coe_reflGL (hQ : ⇑Q = Q₀) (v : ι → ZMod 2) :
    (reflGL Q Q₀ hQ v : Matrix ι ι (ZMod 2)) = reflM Q₀ v :=
  rfl

theorem reflGL_mul_self (hQ : ⇑Q = Q₀) (v : ι → ZMod 2) :
    reflGL Q Q₀ hQ v * reflGL Q Q₀ hQ v = 1 :=
  Units.ext (reflM_mul_self hQ v)

theorem reflGL_mem_isometryCore (hQ : ⇑Q = Q₀) {v : ι → ZMod 2} (hv : Q₀ v = 1) :
    reflGL Q Q₀ hQ v ∈ CFSG.MatrixModel.isometryCore Q₀ := by
  unfold CFSG.MatrixModel.isometryCore
  apply Subgroup.subset_closure
  intro x
  change Q₀ (reflM Q₀ v *ᵥ x) = Q₀ x
  rw [reflM_mulVec hQ, ← hQ]
  have hv' : Q v = 1 := by rw [hQ]; exact hv
  have hpol : QuadraticMap.polar Q x (QuadraticMap.polar Q x v • v) =
      QuadraticMap.polar Q x v * QuadraticMap.polar Q x v := by
    rw [QuadraticMap.polar_smul_right, smul_eq_mul, mul_comm]
  have hadd : ∀ y, Q (x + y) = Q x + Q y + QuadraticMap.polar Q x y := fun y => by
    unfold QuadraticMap.polar
    ring
  rw [hadd, QuadraticMap.map_smul, hv', hpol, smul_eq_mul, mul_one, add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

end Reflections

section Omega

open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply reflect reflect_conj
  reflect_apply_of_map_eq_one zmod_two_eq_one_of_ne_zero closure_isometries_eq_comap
  statedOmega_eq_comap commutator_orthogonalGroup_le_closure_reflect_mul)

variable {Q₀ : (ι → ZMod 2) → ZMod 2}

theorem statedOmega_eq_commutator (Q₀ : (ι → ZMod 2) → ZMod 2) :
    StatedOmega Q₀ =
      ⁅CFSG.MatrixModel.isometryCore Q₀, CFSG.MatrixModel.isometryCore Q₀⁆ :=
  rfl

theorem statedOmega_le_isometryCore (Q₀ : (ι → ZMod 2) → ZMod 2) :
    StatedOmega Q₀ ≤ CFSG.MatrixModel.isometryCore Q₀ := by
  rw [statedOmega_eq_commutator, Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

theorem conj_mem_statedOmega {r : GL ι (ZMod 2)} (hr : r ∈ CFSG.MatrixModel.isometryCore Q₀)
    {x : GL ι (ZMod 2)} (hx : x ∈ StatedOmega Q₀) : r * x * r⁻¹ ∈ StatedOmega Q₀ := by
  have hO : (CFSG.MatrixModel.isometryCore Q₀).map (MulAut.conj r).toMonoidHom ≤
      CFSG.MatrixModel.isometryCore Q₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hr hy) (Subgroup.inv_mem _ hr)
  have hmap : (StatedOmega Q₀).map (MulAut.conj r).toMonoidHom ≤ StatedOmega Q₀ := by
    rw [statedOmega_eq_commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hO hO
  exact hmap ⟨x, hx, rfl⟩

@[expose] def conjOmega (r : GL ι (ZMod 2)) (hr : r ∈ CFSG.MatrixModel.isometryCore Q₀) :
    StatedOmega Q₀ →* StatedOmega Q₀ :=
  ((MulAut.conj r).toMonoidHom.comp (StatedOmega Q₀).subtype).codRestrict (StatedOmega Q₀)
    fun x => conj_mem_statedOmega hr x.2

theorem coe_conjOmega {r : GL ι (ZMod 2)} (hr : r ∈ CFSG.MatrixModel.isometryCore Q₀)
    (x : StatedOmega Q₀) : (conjOmega r hr x : GL ι (ZMod 2)) = r * x * r⁻¹ :=
  rfl

theorem conj_mem_map_sup_normalizer {r : GL ι (ZMod 2)}
    (hr : r ∈ CFSG.MatrixModel.isometryCore Q₀) (hrr : r * r = 1)
    {X₁ X₂ : Subgroup (StatedOmega Q₀)} (h₁ : X₁ ≤ X₁.comap (conjOmega r hr))
    (h₂ : X₂ ≤ X₂.comap (conjOmega r hr)) {h : GL ι (ZMod 2)} (hh : h ∈ (Subgroup.normalizer (X₁ : Set (StatedOmega Q₀)) ⊔
      Subgroup.normalizer (X₂ : Set (StatedOmega Q₀))).map (StatedOmega Q₀).subtype) :
    r * h * r ∈ (Subgroup.normalizer (X₁ : Set (StatedOmega Q₀)) ⊔
      Subgroup.normalizer (X₂ : Set (StatedOmega Q₀))).map (StatedOmega Q₀).subtype := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  have hφφ : ∀ x, conjOmega r hr (conjOmega r hr x) = x := by
    intro x
    apply Subtype.ext
    rw [coe_conjOmega, coe_conjOmega, hri]
    calc r * (r * (x : GL ι (ZMod 2)) * r) * r = (r * r) * x * (r * r) := by group
      _ = x := by rw [hrr, one_mul, mul_one]
  have hN : ∀ X : Subgroup (StatedOmega Q₀), X ≤ X.comap (conjOmega r hr) →
      Subgroup.normalizer (X : Set (StatedOmega Q₀)) ≤
        (Subgroup.normalizer (X : Set (StatedOmega Q₀))).comap (conjOmega r hr) := by
    intro X hX y hy
    rw [Subgroup.mem_comap]
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have hφx : conjOmega r hr x ∈ X := hX hx
    have hyx : y * conjOmega r hr x * y⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.1 hy (conjOmega r hr x)).1 hφx
    have key : conjOmega r hr y * x * (conjOmega r hr y)⁻¹ =
        conjOmega r hr (y * conjOmega r hr x * y⁻¹) := by
      rw [map_mul, map_mul, map_inv, hφφ]
    rw [key]
    exact hX hyx
  have hsup : Subgroup.normalizer (X₁ : Set (StatedOmega Q₀)) ⊔
      Subgroup.normalizer (X₂ : Set (StatedOmega Q₀)) ≤
      (Subgroup.normalizer (X₁ : Set (StatedOmega Q₀)) ⊔
        Subgroup.normalizer (X₂ : Set (StatedOmega Q₀))).comap (conjOmega r hr) :=
    sup_le ((hN X₁ h₁).trans (Subgroup.comap_mono le_sup_left))
      ((hN X₂ h₂).trans (Subgroup.comap_mono le_sup_right))
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hh
  refine Subgroup.mem_map.2 ⟨conjOmega r hr y, hsup hy, ?_⟩
  change ((conjOmega r hr y : StatedOmega Q₀) : GL ι (ZMod 2)) = r * y * r
  rw [coe_conjOmega, hri]

theorem statedOmega_le_of_reflect {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} (hQ : ⇑Q = Q₀)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (h5 : 5 ≤ Fintype.card ι)
    {H : Subgroup (GL ι (ZMod 2))} (hHO : H ≤ CFSG.MatrixModel.isometryCore Q₀)
    {v₀ : ι → ZMod 2} (hv₀ : Q₀ v₀ = 1)
    (hrH : ∀ h ∈ H, reflGL Q Q₀ hQ v₀ * h * reflGL Q Q₀ hQ v₀ ∈ H)
    (htr : ∀ w, Q₀ w = 1 → ∃ h ∈ H, (h : Matrix ι ι (ZMod 2)) *ᵥ v₀ = w) :
    StatedOmega Q₀ ≤ H := by
  have hfin : 5 ≤ Module.finrank (ZMod 2) (ι → ZMod 2) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact h5
  have hv₀Q : Q v₀ = 1 := by rw [hQ]; exact hv₀
  have hcomm := commutator_orthogonalGroup_le_closure_reflect_mul hnd hfin (v₀ := v₀)
    (by rw [hv₀Q]; exact one_ne_zero)
  have hLr : toLinEquiv ι (ZMod 2) (reflGL Q Q₀ hQ v₀) = reflect Q v₀ := by
    refine LinearEquiv.ext fun x => ?_
    rw [toLinEquiv_apply, coe_reflGL, reflM_mulVec hQ, reflect_apply_of_map_eq_one hv₀Q]
  have hO : ∀ h ∈ H, toLinEquiv ι (ZMod 2) h ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro h hh
    have hmem := hHO hh
    rw [CFSG.MatrixModel.isometryCore, closure_isometries_eq_comap hQ] at hmem
    exact hmem
  have hpairs : Subgroup.closure {g | ∃ v, Q v ≠ 0 ∧ g = reflect Q v * reflect Q v₀} ≤
      H.map (toLinEquiv ι (ZMod 2)).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv1 : Q₀ v = 1 := by
      rw [← hQ]
      exact zmod_two_eq_one_of_ne_zero hv
    obtain ⟨h, hh, hhv⟩ := htr v hv1
    refine ⟨h * (reflGL Q Q₀ hQ v₀ * h⁻¹ * reflGL Q Q₀ hQ v₀),
      H.mul_mem hh (hrH _ (H.inv_mem hh)), ?_⟩
    have hc := reflect_conj (hO h hh) v₀
    have hLhv : toLinEquiv ι (ZMod 2) h v₀ = v := by
      rw [toLinEquiv_apply, hhv]
    rw [hLhv] at hc
    rw [← hc, ← hLr]
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    group
  intro g hg
  rw [statedOmega_eq_comap hQ, Subgroup.mem_comap] at hg
  obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.1 (hpairs (hcomm hg))
  rwa [(toLinEquiv ι (ZMod 2)).injective hke] at hk

theorem sup_normalizer_eq_top_of_reflect {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)}
    (hQ : ⇑Q = Q₀) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (h5 : 5 ≤ Fintype.card ι)
    {v₀ : ι → ZMod 2} (hv₀ : Q₀ v₀ = 1) {X₁ X₂ : Subgroup (StatedOmega Q₀)}
    (h₁ : X₁ ≤ X₁.comap (conjOmega (reflGL Q Q₀ hQ v₀) (reflGL_mem_isometryCore hQ hv₀)))
    (h₂ : X₂ ≤ X₂.comap (conjOmega (reflGL Q Q₀ hQ v₀) (reflGL_mem_isometryCore hQ hv₀)))
    (htr : ∀ w, Q₀ w = 1 → ∃ h ∈ (Subgroup.normalizer (X₁ : Set (StatedOmega Q₀)) ⊔
      Subgroup.normalizer (X₂ : Set (StatedOmega Q₀))).map (StatedOmega Q₀).subtype,
      (h : Matrix ι ι (ZMod 2)) *ᵥ v₀ = w) :
    Subgroup.normalizer (X₁ : Set (StatedOmega Q₀)) ⊔
      Subgroup.normalizer (X₂ : Set (StatedOmega Q₀)) = ⊤ := by
  have hle := statedOmega_le_of_reflect hQ hnd h5
    ((Subgroup.map_subtype_le _).trans (statedOmega_le_isometryCore Q₀)) hv₀
    (fun h hh => conj_mem_map_sup_normalizer (reflGL_mem_isometryCore hQ hv₀)
      (reflGL_mul_self hQ v₀) h₁ h₂ hh) htr
  rw [eq_top_iff]
  intro g _
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 (hle g.2)
  rwa [Subtype.ext hyg] at hy

end Omega

end CFSG.LocalAnalysis.RankThreeTheoremC.OrthPlanes

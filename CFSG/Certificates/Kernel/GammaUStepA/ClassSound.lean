
module

public import Certificates.Data.Kernel.GammaUStepA.Class
public import CFSG.Certificates.Kernel.GammaUStepA.Sound
public import CFSG.Certificates.Kernel.GammaUCensusSound

public section

namespace CFSG.KC.GUA

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.KC.GUC CFSG.GF2Type.Smith1979.GammaU
  CFSG.GF2Type.Smith1979.GammaU.StepA

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

@[expose] def RowsIn (acc : List (Array ℕ)) (f : V12 → V12) : Prop :=
  ∃ r ∈ acc, ∀ x, f x = linOfRows r x

theorem mem_fold_of_mem : ∀ (gs acc : List (Array ℕ)) {r : Array ℕ}, r ∈ acc →
    r ∈ gs.foldl (fun acc g => acc ++ acc.map (mulR g)) acc
  | [], _, _, h => h
  | _ :: gs, _, _, h => mem_fold_of_mem gs _ (List.mem_append_left _ h)

theorem rowsIn_fold_mul {t : V12 → V12} : ∀ (gs acc : List (Array ℕ)),
    (∀ g ∈ gs, ∀ x, t (linOfRows g x) = linOfRows g (t x)) →
    (∀ f, RowsIn acc f → RowsIn acc (fun x => t (f x))) →
    ∀ f, RowsIn (gs.foldl (fun acc g => acc ++ acc.map (mulR g)) acc) f →
      RowsIn (gs.foldl (fun acc g => acc ++ acc.map (mulR g)) acc) (fun x => t (f x))
  | [], _, _, h => h
  | g :: gs, acc, hg, h => by
    refine rowsIn_fold_mul gs (acc ++ acc.map (mulR g))
      (fun g' hg' => hg g' (List.mem_cons_of_mem g hg')) ?_
    rintro f ⟨r, hr, hfr⟩
    rcases List.mem_append.1 hr with hr | hr
    · obtain ⟨r', hr', hr'x⟩ := h f ⟨r, hr, hfr⟩
      exact ⟨r', List.mem_append_left _ hr', hr'x⟩
    · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr
      obtain ⟨r', hr', hr'x⟩ := h (fun x => linOfRows r₀ x) ⟨r₀, hr₀, fun x => rfl⟩
      refine ⟨mulR g r', List.mem_append_right _ (List.mem_map_of_mem hr'), fun x => ?_⟩
      beta_reduce
      rw [hfr, linOfRows_mulR, linOfRows_mulR, hg g List.mem_cons_self]
      exact congrArg (linOfRows g) (hr'x x)

theorem rowsIn_inv {g : Array ℕ} (hinv : ∀ x, linOfRows g (linOfRows g x) = x)
    (acc : List (Array ℕ)) : ∀ f, RowsIn (acc ++ acc.map (mulR g)) f →
      RowsIn (acc ++ acc.map (mulR g)) (fun x => linOfRows g (f x)) := by
  rintro f ⟨r, hr, hfr⟩
  rcases List.mem_append.1 hr with hr | hr
  · refine ⟨mulR g r, List.mem_append_right _ (List.mem_map_of_mem hr), fun x => ?_⟩
    beta_reduce
    rw [hfr, linOfRows_mulR]
  · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr
    refine ⟨r₀, List.mem_append_left _ hr₀, fun x => ?_⟩
    beta_reduce
    rw [hfr, linOfRows_mulR, hinv]

theorem rowsIn_gen {gs : List (Array ℕ)}
    (hc : ∀ g ∈ gs, ∀ h ∈ gs, ∀ x, linOfRows g (linOfRows h x) = linOfRows h (linOfRows g x))
    {g : Array ℕ} (hg : g ∈ gs) (hinv : ∀ x, linOfRows g (linOfRows g x) = x)
    (acc : List (Array ℕ)) (f : V12 → V12)
    (hf : RowsIn (gs.foldl (fun acc g => acc ++ acc.map (mulR g)) acc) f) :
    RowsIn (gs.foldl (fun acc g => acc ++ acc.map (mulR g)) acc) (fun x => linOfRows g (f x)) := by
  obtain ⟨s, u, rfl⟩ := List.append_of_mem hg
  rw [List.foldl_append, List.foldl_cons] at hf ⊢
  exact rowsIn_fold_mul (t := ⇑(linOfRows g)) u _
    (fun h hh x => hc g hg h (List.mem_append_right s (List.mem_cons_of_mem g hh)) x)
    (rowsIn_inv hinv _) f hf

theorem twAt_eq (c j : ℕ) :
    twAt c j = if c.testBit j then mulP K0P (nthD 0 CBP j) else nthD 0 CBP j := by
  unfold twAt
  rw [land_shr_one]
  split_ifs <;> rfl

theorem mem_twG {g c : ℕ} (hg : g ∈ twG c) : ∃ j < 5, g = twAt c j := by
  simp only [twG, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩,
    ⟨3, by norm_num, rfl⟩, ⟨4, by norm_num, rfl⟩]

theorem twAt_mem (c : ℕ) {j : ℕ} (hj : j < 5) : twAt c j ∈ twG c := by
  interval_cases j <;> simp [twG]

section Gens

variable {K : GL} {C : ℕ → GL} (hK : IsP K K0P) (hC : ∀ j < 5, IsP (C j) (nthD 0 CBP j))
include hK hC

theorem twAt_isP (c : ℕ) {j : ℕ} (hj : j < 5) :
    IsP (if c.testBit j then K * C j else C j) (twAt c j) := by
  rw [twAt_eq]
  split_ifs
  · exact hK.mul (hC j hj)
  · exact hC j hj

theorem twG_isP (c : ℕ) : ∀ g ∈ twG c, ∃ U, IsP U g := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := mem_twG hg
  exact ⟨_, twAt_isP hK hC c hj⟩

theorem rowsIn_iff (hKr : ∀ v, K v = linOfRows k0 v)
    (hCr : ∀ j < 5, ∀ v, C j v = linOfRows cBasis[j]! v) (hKK : K * K = 1)
    (hCC : ∀ j < 5, C j * C j = 1) (hKC : ∀ j < 5, Commute K (C j))
    (hCC' : ∀ j < 5, ∀ j' < 5, Commute (C j) (C j')) (c : ℕ) (f : GL) :
    (∃ r ∈ compOf c, ∀ x, f x = linOfRows r x) ↔ f ∈ pGrp (twG c) := by
  let U : ℕ → GL := fun j => if c.testBit j then K * C j else C j
  have hU : ∀ j < 5, IsP (U j) (twAt c j) := fun j hj => twAt_isP hK hC c hj
  have hUr : ∀ j < 5, ∀ v,
      U j v = linOfRows (if c.testBit j then mulR k0 cBasis[j]! else cBasis[j]!) v := by
    intro j hj v
    dsimp only [U]
    split_ifs
    · rw [LinearEquiv.mul_apply, hCr j hj, hKr, linOfRows_mulR]
    · exact hCr j hj v
  have hUU : ∀ j < 5, U j * U j = 1 := by
    intro j hj
    dsimp only [U]
    split_ifs
    · calc K * C j * (K * C j) = K * (C j * K) * C j := by group
        _ = K * (K * C j) * C j := by rw [(hKC j hj).eq]
        _ = (K * K) * (C j * C j) := by group
        _ = 1 := by rw [hKK, hCC j hj, one_mul]
    · exact hCC j hj
  have hUc : ∀ j < 5, ∀ j' < 5, Commute (U j) (U j') := by
    intro j hj j' hj'
    dsimp only [U]
    split_ifs
    · exact ((Commute.refl K).mul_right (hKC j' hj')).mul_left
        ((hKC j hj).symm.mul_right (hCC' j hj j' hj'))
    · exact (hKC j' hj').mul_left (hCC' j hj j' hj')
    · exact (hKC j hj).symm.mul_right (hCC' j hj j' hj')
    · exact hCC' j hj j' hj'
  have hgR : ∀ g ∈ (List.range 5).map fun i => if c.testBit i then mulR k0 cBasis[i]! else
      cBasis[i]!, ∃ j < 5, ∀ v, U j v = linOfRows g v := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    exact ⟨j, List.mem_range.1 hj, hUr j (List.mem_range.1 hj)⟩
  constructor
  · rintro ⟨r, hr, hfr⟩
    obtain ⟨l, hl, hlx⟩ := subsetProducts_mem (L := pGrp (twG c)) (fun g hg => by
      obtain ⟨j, hj, hjg⟩ := hgR g hg
      exact ⟨U j, Subgroup.subset_closure ⟨twAt c j, twAt_mem c hj, hU j hj⟩, hjg⟩) r hr
    have e : f = l := LinearEquiv.ext fun x => (hfr x).trans (hlx x).symm
    rw [e]
    exact hl
  · intro hf
    refine mem_of_closure (S := {W | ∃ g ∈ twG c, IsP W g})
      (K := {W : GL | RowsIn (compOf c) ⇑W}) ?_ ?_ hf
    · refine ⟨idR, mem_fold_of_mem _ _ (List.mem_singleton_self _), fun x => ?_⟩
      rw [linOfRows_idR]
      rfl
    · rintro s ⟨g, hg, hsg⟩ y hy
      obtain ⟨j, hj, rfl⟩ := mem_twG hg
      have hs : s = U j := IsP.inj hsg (hU j hj)
      have hgm : (if c.testBit j then mulR k0 cBasis[j]! else cBasis[j]!) ∈
          (List.range 5).map fun i => if c.testBit i then mulR k0 cBasis[i]! else cBasis[i]! :=
        List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
      have hcR : ∀ g ∈ (List.range 5).map fun i => if c.testBit i then mulR k0 cBasis[i]! else
          cBasis[i]!, ∀ h ∈ (List.range 5).map fun i => if c.testBit i then mulR k0 cBasis[i]!
          else cBasis[i]!, ∀ x, linOfRows g (linOfRows h x) = linOfRows h (linOfRows g x) := by
        intro g hg h hh x
        obtain ⟨a, ha, hag⟩ := hgR g hg
        obtain ⟨b, hb, hbh⟩ := hgR h hh
        rw [← hag, ← hbh, ← hag, ← hbh, ← LinearEquiv.mul_apply, (hUc a ha b hb).eq,
          LinearEquiv.mul_apply]
      have hinv : ∀ x, linOfRows (if c.testBit j then mulR k0 cBasis[j]! else cBasis[j]!)
          (linOfRows (if c.testBit j then mulR k0 cBasis[j]! else cBasis[j]!) x) = x := by
        intro x
        rw [← hUr j hj, ← hUr j hj, ← LinearEquiv.mul_apply, hUU j hj]
        rfl
      obtain ⟨r, hr, hrx⟩ := rowsIn_gen hcR hgm hinv [idR] ⇑y hy
      exact ⟨r, hr, fun x => by rw [hs, LinearEquiv.mul_apply, hUr j hj]; exact hrx x⟩

end Gens

theorem commute_of {A B : GL} {a b : ℕ} (hA : IsP A a) (hB : IsP B b) (h : mulP a b = mulP b a) :
    Commute A B := by
  have h1 := hA.mul hB
  rw [h] at h1
  exact IsP.inj h1 (hB.mul hA)

theorem mapD_spec (hspan : spanOK = true) {g : ℕ} (h : mapD g = true) {U : GL} (hU : IsP U g) :
    ∀ y, y ∈ spanOf d0 → U y ∈ spanOf d0 := by
  have hSD : SD0 = spanList d0 := beq_iff_eq.1 hspan
  have hle : spanOf d0 ≤ (spanOf d0).comap (U : V12 →ₗ[ZMod 2] V12) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    have hd' := (recAll_iff (fun d => memN (ap12 g d) SD0) d0).1 h d hd
    rw [memN_iff, hSD] at hd'
    change U (vecOf d) ∈ spanOf d0
    rw [hU.apply_code]
    exact (mem_spanList_iff d0_lt (ap12_lt _ _)).1 hd'
  exact fun y hy => hle hy

theorem cls_spec (hpin : pinOK = true) (hspan : spanOK = true) (hcomm : commOK = true)
    (hb0 : clsBlk THP CLS 0 = true) (hb1 : clsBlk THP CLS 1 = true)
    (hb2 : clsBlk THP CLS 2 = true) (hb3 : clsBlk THP CLS 3 = true) :
    ∀ c < 32, ∃ i, (i = 0 ∨ i = 1) ∧ ∃ g ∈ gammaU, g (vecOf a0) = vecOf a0 ∧
      (∀ y, y ∈ spanOf d0 ↔ g y ∈ spanOf d0) ∧
      ∀ l : GL, (∃ r ∈ compOf c, ∀ x, l x = linOfRows r x) ↔
        ∃ r ∈ compOf i, ∀ x, (g⁻¹ * l * g) x = linOfRows r x := by
  intro c hc
  obtain ⟨hK0eq, -, hTHeq, hk0r, hcbr, hthr⟩ := pinOK_spec hpin
  have hTH : ∀ v, linP THP v = theta0 v := fun v => by
    rw [hTHeq, linP_eq_of_rowsP (GUS.rowsP_packR hthr), GUS.linOfRows_thetaRows]
  have hca : ∀ g ∈ K0P :: CBP, mulP g g = idP ∧ ∀ h ∈ K0P :: CBP, mulP g h = mulP h g := by
    intro g hg
    have hg' := (recAll_iff (fun g => commAt (K0P :: CBP) g) (K0P :: CBP)).1 hcomm g hg
    unfold commAt at hg'
    rw [Bool.and_eq_true, Nat.beq_eq] at hg'
    refine ⟨hg'.1, fun h hh => ?_⟩
    exact Nat.eq_of_beq_eq_true
      ((recAll_iff (fun h => Nat.beq (mulP g h) (mulP h g)) _).1 hg'.2 h hh)
  obtain ⟨K, hK⟩ := IsP.exists_of_mul (hca K0P List.mem_cons_self).1
  have hKK : K * K = 1 := by
    have h2 := hK.mul hK
    rw [(hca K0P List.mem_cons_self).1] at h2
    exact IsP.inj h2 IsP.one
  have hKr : ∀ v, K v = linOfRows k0 v := (GUS.isP_packR hk0r K).1 (hK0eq ▸ hK)
  have hCBi : ∀ i < 5, nthD 0 CBP i = CFSG.KC.IF4R.packR cBasis[i]! := by decide +kernel
  have hmem : ∀ j < 5, nthD 0 CBP j ∈ K0P :: CBP := fun j hj =>
    List.mem_cons_of_mem _ (GUS.nthD_mem 0 (lt_of_lt_of_eq hj rfl))
  have hCex : ∀ j, ∃ C : GL, j < 5 → IsP C (nthD 0 CBP j) := fun j => by
    by_cases hj : j < 5
    · obtain ⟨C, hC⟩ := IsP.exists_of_mul (hca _ (hmem j hj)).1
      exact ⟨C, fun _ => hC⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose C hC using hCex
  have hCr : ∀ j < 5, ∀ v, C j v = linOfRows cBasis[j]! v := fun j hj =>
    (GUS.isP_packR (hcbr _ (cBasis_mem hj)) (C j)).1 (by rw [← hCBi j hj]; exact hC j hj)
  have hCC : ∀ j < 5, C j * C j = 1 := fun j hj => by
    have h2 := (hC j hj).mul (hC j hj)
    rw [(hca _ (hmem j hj)).1] at h2
    exact IsP.inj h2 IsP.one
  have hKC : ∀ j < 5, Commute K (C j) := fun j hj =>
    commute_of hK (hC j hj) ((hca K0P List.mem_cons_self).2 _ (hmem j hj))
  have hCC' : ∀ j < 5, ∀ j' < 5, Commute (C j) (C j') := fun j hj j' hj' =>
    commute_of (hC j hj) (hC j' hj') ((hca _ (hmem j hj)).2 _ (hmem j' hj'))
  have hiff := rowsIn_iff hK hC hKr hCr hKK hCC hKC hCC'
  have hrec : clsRec THP c (nthD [] CLS c) = true := by
    have hb : ∀ b < 4, clsBlk THP CLS b = true := by
      intro b hb
      interval_cases b
      exacts [hb0, hb1, hb2, hb3]
    have h8 := (allBelow_iff _ _).1 (hb (c / 8) (by omega)) (c % 8) (Nat.mod_lt _ (by norm_num))
    beta_reduce at h8
    have e : Nat.add (Nat.mul 8 (c / 8)) (c % 8) = c := Nat.div_add_mod c 8
    rwa [e] at h8
  unfold clsRec clsAt at hrec
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hrec
  obtain ⟨⟨⟨⟨⟨⟨⟨hi, hinv⟩, hgu⟩, hfix⟩, hmv⟩, hmvi⟩, hc1⟩, hc2⟩ := hrec
  obtain ⟨V, hV⟩ := IsP.exists_of_mul hinv
  have hVi : IsP V⁻¹ (nthD 0 (nthD [] CLS c) 2) := hV.inv hinv
  have hVii : IsP V⁻¹⁻¹ (nthD 0 (nthD [] CLS c) 1) := by
    rw [inv_inv]
    exact hV
  have h1 := map_conj_le_of_cjOK hc1 (twG_isP hK hC c) hV hVi
  have h2 := map_conj_le_of_cjOK hc2 (twG_isP hK hC _) hVi hVii
  refine ⟨nthD 0 (nthD [] CLS c) 0, by omega, V, guOK_spec hTH hgu hV, ?_,
    fun y => ⟨mapD_spec hspan hmv hV y, fun h => ?_⟩, fun l => ?_⟩
  · change V (vecOf 3072) = vecOf 3072
    rw [hV.apply_code, hfix]
  · have h' := mapD_spec hspan hmvi hVi (V y) h
    rwa [inv_apply_apply] at h'
  · rw [hiff c l, hiff _ (V⁻¹ * l * V)]
    constructor
    · intro hl
      have h' := h2 (Subgroup.mem_map_of_mem _ hl)
      simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h'
      exact h'
    · intro hl
      have h' := h1 (Subgroup.mem_map_of_mem _ hl)
      simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h'
      have e : V * (V⁻¹ * l * V) * V⁻¹ = l := by group
      rwa [e] at h'

end CFSG.KC.GUA

end

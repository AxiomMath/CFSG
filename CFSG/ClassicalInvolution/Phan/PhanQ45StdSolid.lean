module

public import CFSG.ClassicalInvolution.Phan.PhanQ44Dict
public import CFSG.ClassicalInvolution.Phan.PhanQ41Inj

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Monster.B.Geometry
  CFSG.Monster.B.Geometry.ChamberSystem CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

section Count

theorem surjective_and_reflect_of_injective {Ω X : Type*} [Finite Ω] [Finite X]
    (Col : Ω → Ω → Prop) (Adj : X → X → Prop) (β : Ω → X) (hβ : Function.Bijective β)
    (hcol : ∀ a b, Col a b ↔ Adj (β a) (β b)) (π : Ω → X) (hπ : Function.Injective π)
    (hπc : ∀ a b, Col a b → Adj (π a) (π b)) :
    Function.Surjective π ∧ ∀ a b, Adj (π a) (π b) → Col a b := by
  have hcard : Nat.card X = Nat.card Ω := (Nat.card_congr (Equiv.ofBijective β hβ)).symm
  have hπb : Function.Bijective π := hπ.bijective_of_nat_card_le hcard.le
  refine ⟨hπb.2, ?_⟩
  let E₁ := {p : Ω × Ω // Col p.1 p.2}
  let E₂ := {p : X × X // Adj p.1 p.2}
  let φ : E₁ → E₂ := fun p => ⟨(π p.1.1, π p.1.2), hπc _ _ p.2⟩
  let ψ : E₁ → E₂ := fun p => ⟨(β p.1.1, β p.1.2), (hcol _ _).1 p.2⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · intro p q h
      have h1 := congrArg (fun r : E₂ => r.1) h
      simp only [ψ, Prod.mk.injEq] at h1
      exact Subtype.ext (Prod.ext (hβ.1 h1.1) (hβ.1 h1.2))
    · rintro ⟨⟨x, y⟩, hxy⟩
      obtain ⟨a, rfl⟩ := hβ.2 x
      obtain ⟨b, rfl⟩ := hβ.2 y
      exact ⟨⟨(a, b), (hcol a b).2 hxy⟩, rfl⟩
  have hφ : Function.Injective φ := by
    intro p q h
    have h1 := congrArg (fun r : E₂ => r.1) h
    simp only [φ, Prod.mk.injEq] at h1
    exact Subtype.ext (Prod.ext (hπ h1.1) (hπ h1.2))
  have hcardE : Nat.card E₂ = Nat.card E₁ := (Nat.card_congr (Equiv.ofBijective ψ hψ)).symm
  have hφb : Function.Bijective φ := hφ.bijective_of_nat_card_le hcardE.le
  intro a b hab
  obtain ⟨q, hq⟩ := hφb.2 ⟨(π a, π b), hab⟩
  have h1 := congrArg (fun r : E₂ => r.1) hq
  simp only [φ, Prod.mk.injEq] at h1
  have e1 := hπ h1.1
  have e2 := hπ h1.2
  have := q.2
  rw [e1, e2] at this
  exact this

end Count

section StdSolid

variable {p e : ℕ} [Fact p.Prime] (M : StdModel p e)
  [Algebra (GaloisField p e) (GaloisField p (2 * e))]
  (D : KData (GaloisField p e) (GaloisField p (2 * e)) M.ε)

structure StdSolid (e' : Fin 3 → Fin 4)
    (ψ : Su (GaloisField p (2 * e)) p e 4 →* spinGroup (quadPlus 4 (GaloisField p e)))
    (k : Fin 4)
    (J : V8 (GaloisField p (2 * e)) →ₗ[GaloisField p (2 * e)] V8 (GaloisField p (2 * e)))
    (JF : V8 (GaloisField p e) → V8 (GaloisField p e)) : Prop where
  chain : ChainCtx M.S e' ψ
  hcov : ∀ i : Fin 4, i = k ∨ ∃ j, e' j = i
  hc0 : ∀ A B, M.S.ι k A * M.S.ι (e' 0) B = M.S.ι (e' 0) B * M.S.ι k A
  hc2 : ∀ A B, M.S.ι k A * M.S.ι (e' 2) B = M.S.ι (e' 2) B * M.S.ι k A
  hpair : ({e' 2} : Set (Fin 4)) ∪ {k} = {2, 3}
  hcomm : CommuteTypes (phanSystem M.S) k (e' 2)
  hrange : Set.range e' = {0, 1, 2} ∨ Set.range e' = {0, 1, 3}
  hJ : PhanJK D J
  hext : ∀ x, J (extV (GaloisField p (2 * e)) x) = extV (GaloisField p (2 * e)) (JF x)
  hsq : ∀ x, JF (JF x) = (-M.ε) • x
  hψJ : ∀ (h : Su (GaloisField p (2 * e)) p e 4) (v : V8 (GaloisField p e)),
    JF (spinAction (quadPlus 4 (GaloisField p e)) (ψ h) v) =
      spinAction (quadPlus 4 (GaloisField p e)) (ψ h) (JF v)
  hz0 : JF (z0 M.ε).x = (z0 M.ε).y

end StdSolid

section Points

variable {p e : ℕ} [Fact p.Prime] {M : StdModel p e}
  [Algebra (GaloisField p e) (GaloisField p (2 * e))]
  {D : KData (GaloisField p e) (GaloisField p (2 * e)) M.ε}
  {e' : Fin 3 → Fin 4}
  {ψ : Su (GaloisField p (2 * e)) p e 4 →* spinGroup (quadPlus 4 (GaloisField p e))}
  {k : Fin 4} {J : V8 (GaloisField p (2 * e)) →ₗ[GaloisField p (2 * e)] V8 (GaloisField p (2 * e))}
  {JF : V8 (GaloisField p e) → V8 (GaloisField p e)}

theorem StdSolid.ptVec_mem (hS : StdSolid M D e' ψ k J JF) (hp2 : p ≠ 2)
    (h : Su (GaloisField p (2 * e)) p e 4) : ptVec M D (ψ h) ∈ solidOf D J := by
  have h2K := two_ne_zero_gf hp2 (2 * e)
  unfold ptVec
  rw [(vecK_mem_solidOf_iff h2K M.hε JF hS.hext hS.hsq ((ψ h) • z0 M.ε))]
  rw [NPair.smul_x, NPair.smul_y, hS.hψJ, hS.hz0]

end Points

section Main

variable {p e : ℕ} [Fact p.Prime] {M : StdModel p e}
  [Algebra (GaloisField p e) (GaloisField p (2 * e))]
  {D : KData (GaloisField p e) (GaloisField p (2 * e)) M.ε}
  {e' : Fin 3 → Fin 4}
  {ψ : Su (GaloisField p (2 * e)) p e 4 →* spinGroup (quadPlus 4 (GaloisField p e))}
  {k : Fin 4} {J : V8 (GaloisField p (2 * e)) →ₗ[GaloisField p (2 * e)] V8 (GaloisField p (2 * e))}
  {JF : V8 (GaloisField p e) → V8 (GaloisField p e)}

theorem StdSolid.hσ (_hS : StdSolid M D e' ψ k J JF) (hq : 5 ≤ p ^ e) (x : GaloisField p (2 * e)) :
    unitaryInvolution (GaloisField p (2 * e)) p e x = D.τ x := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  rw [unitaryInvolution_apply, D.tau_pow, hF]

set_option linter.unusedSectionVars false

theorem StdSolid.points_complete (hS : StdSolid M D e' ψ k J JF) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (h0 : PtStep0 M.S) (he : PtEdge M.S) :
    (∀ y : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3},
      lineOfPt M D hp2 hq y ≤ solidOf D J →
        ∃ f : Frame (unitaryInvolution (GaloisField p (2 * e)) p e) 4,
          ptMap M.S (hS.chain.Phi f) = y) ∧
    (∀ f f' : Frame (unitaryInvolution (GaloisField p (2 * e)) p e) 4,
      (ptGraph M.S).Adj (ptMap M.S (hS.chain.Phi f)) (ptMap M.S (hS.chain.Phi f')) →
        IsCollinear (unitaryInvolution (GaloisField p (2 * e)) p e) (f.line 0) (f'.line 0)) := by
  have C := hS.chain
  have h2K := two_ne_zero_gf hp2 (2 * e)
  have hW := hS.hJ.phanSolid h2K M.hε
  obtain ⟨β, hβ⟩ := PhanSolid.exists_pointEquiv D hW h2K M.hε (hS.hσ hq) C.hσ
  have : Finite (Submodule (GaloisField p (2 * e)) (Fin 4 → GaloisField p (2 * e))) :=
    Finite.of_injective (SetLike.coe) SetLike.coe_injective
  have : Finite (Submodule (GaloisField p (2 * e)) (V8 (GaloisField p (2 * e)))) :=
    Finite.of_injective (SetLike.coe) SetLike.coe_injective
  choose fr hfr using fun a : ↥(nsPts (unitaryInvolution (GaloisField p (2 * e)) p e)
      (⊤ : Submodule (GaloisField p (2 * e)) (Fin 4 → GaloisField p (2 * e)))) =>
    C.exists_frame_line a.2
  have hpi : ∀ a, C.piPt a = ptMap M.S (C.Phi (fr a)) := fun a => C.piPt_eq (hfr a)
  have hmemW : ∀ a, lineOfPt M D hp2 hq (C.piPt a) ≤ solidOf D J := by
    intro a
    rw [hpi]
    obtain ⟨h, hh⟩ := exists_smul_stdFrame C.hσ (fr a)
    rw [← hh, C.Phi_smul, ptMap_mk, lineOfPt_mk]
    exact (Submodule.span_singleton_le_iff_mem _ _).2 (hS.ptVec_mem hp2 h)
  have hffa : ∀ a, lineOfPt M D hp2 hq (C.piPt a) ∈ ffLines D (solidOf D J) := by
    intro a
    obtain ⟨v, hv0, hvff, hv⟩ := lineOfPt_ff (D := D) hp2 hq h2K (C.piPt a)
    exact ⟨hmemW a, v, hv0, hvff, hv⟩
  let π' : ↥(nsPts (unitaryInvolution (GaloisField p (2 * e)) p e)
      (⊤ : Submodule (GaloisField p (2 * e)) (Fin 4 → GaloisField p (2 * e)))) →
      ↥(ffLines D (solidOf D J)) := fun a => ⟨lineOfPt M D hp2 hq (C.piPt a), hffa a⟩
  have hπ'inj : Function.Injective π' := by
    intro a b hab
    have h1 := lineOfPt_injective hp2 hq (congrArg Subtype.val hab)
    rw [hpi, hpi] at h1
    have h2 := C.line_eq_of_ptMap_eq hS.hcov hS.hc0 hS.hc2 hS.hpair hS.hcomm h0 he h1
    rw [hfr a, hfr b] at h2
    exact Subtype.ext h2
  have hπ'col : ∀ a b, IsCollinear (unitaryInvolution (GaloisField p (2 * e)) p e) a.1 b.1 →
      AdjL D (π' a).1 (π' b).1 := by
    intro a b hab
    have h1 := C.adj_ptMap_of_collinear h0 (c := fr a) (d := fr b) (by rw [hfr a, hfr b]; exact hab)
    rw [← hpi, ← hpi] at h1
    exact (adj_iff_adjL hp2 hq _ _).1 h1
  obtain ⟨hsurj, hrefl⟩ := surjective_and_reflect_of_injective _ (fun ℓ ℓ' => AdjL D ℓ.1 ℓ'.1) β
    β.bijective hβ π' hπ'inj hπ'col
  refine ⟨fun y hy => ?_, fun f f' hadj => ?_⟩
  · obtain ⟨v, hv0, hvff, hyv⟩ := lineOfPt_ff (D := D) hp2 hq h2K y
    obtain ⟨a, ha⟩ := hsurj ⟨lineOfPt M D hp2 hq y, hy, v, hv0, hvff, hyv⟩
    have h1 := lineOfPt_injective hp2 hq (congrArg Subtype.val ha)
    exact ⟨fr a, by rw [← hpi, h1]⟩
  · let a : ↥(nsPts (unitaryInvolution (GaloisField p (2 * e)) p e)
        (⊤ : Submodule (GaloisField p (2 * e)) (Fin 4 → GaloisField p (2 * e)))) :=
      ⟨f.line 0, le_top, f.finrank_line _, f.nondeg_line _⟩
    let b : ↥(nsPts (unitaryInvolution (GaloisField p (2 * e)) p e)
        (⊤ : Submodule (GaloisField p (2 * e)) (Fin 4 → GaloisField p (2 * e)))) :=
      ⟨f'.line 0, le_top, f'.finrank_line _, f'.nondeg_line _⟩
    have h1 : (ptGraph M.S).Adj (C.piPt a) (C.piPt b) := by
      rw [C.piPt_eq (c := f) rfl, C.piPt_eq (c := f') rfl]
      exact hadj
    exact hrefl a b ((adj_iff_adjL hp2 hq _ _).1 h1)

theorem StdSolid.conditions (hS : StdSolid M D e' ψ k J JF) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (h0 : PtStep0 M.S) (he : PtEdge M.S) :
    (∀ {i : Fin 4} {c g : (spinGroup (quadPlus 4 (GaloisField p e))) ⧸ torusSub M.S},
      i ∈ Set.range e' → (phanSystem M.S).adj i c g → c ∈ Set.range hS.chain.Phi →
        g ∈ Set.range hS.chain.Phi) ∧
    (∀ c ∈ Set.range hS.chain.Phi, ∀ c' ∈ Set.range hS.chain.Phi,
      ptMap M.S c = ptMap M.S c' →
        ∃ τ, IsJGallery (phanSystem M.S) {i | i ∈ Set.range e' ∧ i ≠ 0} c τ ∧
          galleryEnd c τ = c') ∧
    (∀ c ∈ Set.range hS.chain.Phi, ∀ y ∈ ptMap M.S '' Set.range hS.chain.Phi,
      (ptGraph M.S).Adj (ptMap M.S c) y →
        ∃ c₁ ∈ Set.range hS.chain.Phi, ∃ g ∈ Set.range hS.chain.Phi,
          ptMap M.S c₁ = ptMap M.S c ∧ ptMap M.S g = y ∧ (phanSystem M.S).adj 0 c₁ g) ∧
    (∀ y : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3},
      lineOfPt M D hp2 hq y ≤ solidOf D J → y ∈ ptMap M.S '' Set.range hS.chain.Phi) := by
  obtain ⟨hsurj, hrefl⟩ := hS.points_complete hp2 hq h0 he
  have C := hS.chain
  have hq3 : 3 ≤ p ^ e := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro i g g' ⟨j, rfl⟩ hadj ⟨c, rfl⟩
    obtain ⟨c', -, hc'⟩ := C.exists_adj_Phi c hadj
    exact ⟨c', hc'⟩
  · rintro _ ⟨f, rfl⟩ _ ⟨f', rfl⟩ hp
    have hline := C.line_eq_of_ptMap_eq hS.hcov hS.hc0 hS.hc2 hS.hpair hS.hcomm h0 he hp
    have hres : f' ∈ (frameSystem (unitaryInvolution (GaloisField p (2 * e)) p e) 3).residue
        (typeInt 3 1 3) f := by
      refine (mem_residue_typeInt_iff C.hσ C.hK hq3 (a := 1) (b := 3) (by omega) (by omega)).2 ?_
      intro k hk
      have hk0 : k = 0 := by
        rw [mem_posInt] at hk
        ext
        simp only [Fin.val_zero]
        omega
      subst hk0
      exact hline.symm
    obtain ⟨τ, hτ, hτe⟩ := mem_residue_iff_exists_isJGallery.1 (C.mem_residue_Phi hres)
    refine ⟨τ, hτ.mono ?_, hτe⟩
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨⟨j, rfl⟩, fun h0' => ?_⟩
    have hj0 : j = 0 := C.hch.inj (h0'.trans C.he0.symm)
    rw [mem_typeInt] at hj
    rw [hj0] at hj
    simp at hj
  · rintro _ ⟨f, rfl⟩ y ⟨_, ⟨f', rfl⟩, rfl⟩ hadj
    have hcol := hrefl f f' hadj
    obtain ⟨c₁, c₂, h1, h2, hadj0⟩ :=
      C.exists_adj_zero (f₀ := f) ⟨le_top, f'.finrank_line _, f'.nondeg_line _⟩ hcol
    exact ⟨C.Phi c₁, ⟨c₁, rfl⟩, C.Phi c₂, ⟨c₂, rfl⟩, C.ptMap_Phi_eq h1, C.ptMap_Phi_eq h2,
      C.he0 ▸ C.Phi_adj hadj0⟩
  · intro v hv
    obtain ⟨f, hf⟩ := hsurj v hv
    exact ⟨C.Phi f, ⟨f, rfl⟩, hf⟩

end Main

end CFSG.ClassicalInvolution.PhanQ

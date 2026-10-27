module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzWords
public import Certificates.Certificate27120
public import CFSG.LieType.Multipliers.Sz8Bridge
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.EvenSporadicStandard.Induction.RuSz

open Subgroup CFSG.Blueprint CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Sz8
open CFSG.Sporadic.Th (Rep)
open CFSG.EvenSporadicStandard.TwoRu.HypOne (lGens)

section Tables

theorem eq_of_rep_tblEq {n : ℕ} {S T : Table} {g h : Equiv.Perm (Fin n)} (hg : Rep n S g)
    (hh : Rep n T h) (e : tblEq n S T = true) : g = h := by
  unfold tblEq at e
  rw [CFSG.Sporadic.Th.allIn_eq_true] at e
  ext x
  have e1 := hg x.1 x.2
  have e2 := hh x.1 x.2
  rw [CFSG.Sporadic.Th.idx_of_lt _ x.2] at e1 e2
  have := e x.1 (Nat.zero_le _) x.2
  simp only [beq_iff_eq] at this
  exact e1.symm.trans (this.trans e2)

theorem eq_one_of_rep_tblEq {n : ℕ} (hn : n < 2 ^ 32) {S : Table} {g : Equiv.Perm (Fin n)}
    (hg : Rep n S g) (e : tblEq n S (idT n) = true) : g = 1 :=
  eq_of_rep_tblEq hg (CFSG.Sporadic.Th.Rep.idT hn) e

theorem tblEq_of_rep {n : ℕ} {S T : Table} {g : Equiv.Perm (Fin n)} (hg : Rep n S g)
    (hh : Rep n T g) : tblEq n S T = true := by
  unfold tblEq
  rw [CFSG.Sporadic.Th.allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hg i hi, hh i hi]

theorem ne_one_of_tblEq_false {n : ℕ} (hn : n < 2 ^ 32) {S : Table} {g : Equiv.Perm (Fin n)}
    (hg : Rep n S g) (e : tblEq n S (idT n) = false) : g ≠ 1 := by
  rintro rfl
  have := tblEq_of_rep hg (CFSG.Sporadic.Th.Rep.idT (G := Equiv.Perm (Fin n)) hn)
  rw [e] at this
  cases this

end Tables

section Checks


theorem szChecks :
    ruSzInvOK = true ∧ ruSzRelsOK = true ∧ ruSzNontriv = true ∧ ruSzNormOK = true ∧
      ruSzCentOK = true ∧ ruSzFixOK = true ∧ ruSzPtsOK = true := by
  have h := Certificates.certificate27120
  simp only [ruSzCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end Checks

section Elements


theorem sWord_ok : ∀ z ∈ sWord, z ≠ 0 ∧ z.natAbs ≤ lGens.size := by
  rw [lGens_size]
  decide

theorem tWord_ok : ∀ z ∈ tWord, z ≠ 0 ∧ z.natAbs ≤ lGens.size := by
  rw [lGens_size]
  decide

theorem bWord_ok : ∀ z ∈ bWord, z ≠ 0 ∧ z.natAbs ≤ lGens.size := by
  rw [lGens_size]
  decide

theorem rep_s : Rep 4060 sTab sG ∧ sG ∈ ruL := rep_lTab sWord_ok

theorem rep_t : Rep 4060 tTab tG ∧ tG ∈ ruL := rep_lTab tWord_ok

theorem rep_b : Rep 4060 bTab bG ∧ bG ∈ ruL := rep_lTab bWord_ok


theorem rep_sInv : Rep 4060 sInv sG⁻¹ := by
  have h := szChecks.1
  simp only [ruSzInvOK, Bool.and_eq_true] at h
  exact CFSG.Sporadic.Th.Rep.inv_of_invOK rep_s.1 h.1

theorem rep_tInv : Rep 4060 tInv tG⁻¹ := by
  have h := szChecks.1
  simp only [ruSzInvOK, Bool.and_eq_true] at h
  exact CFSG.Sporadic.Th.Rep.inv_of_invOK rep_t.1 h.2

theorem rep_kTab (w : String) : Rep 4060 (kTab w) (kG w) :=
  rep_wordTab (by norm_num) rep_s.1 rep_sInv rep_t.1 rep_tInv (parseW w)

theorem szRels_eq : szRels = rels.map (List.map fun l => ((l.1 : Fin 2).val, l.2)) := rfl

theorem wordProd_rels : ∀ v ∈ szRels, wordProd (img2 sG tG) v = 1 := by
  intro v hv
  have h := szChecks.2.1
  simp only [ruSzRelsOK, List.all_eq_true] at h
  exact eq_one_of_rep_tblEq (by norm_num)
    (rep_wordTab (by norm_num) rep_s.1 rep_sInv rep_t.1 rep_tInv v) (h v hv)

theorem lift_eq_one :
    ∀ r ∈ wordSet rels, FreeGroup.lift (fun i : Fin 2 => img2 sG tG i.val) r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [lift_mk_eq_wordProd]
  exact wordProd_rels _ (by rw [szRels_eq]; exact List.mem_map_of_mem hw)

theorem sG_ne_one : sG ≠ 1 :=
  ne_one_of_tblEq_false (by norm_num) rep_s.1 (by
    have h := szChecks.2.2.1
    simpa [ruSzNontriv] using h)

end Elements

section Hom

abbrev SzB : Type := suzukiGroup 1 (GaloisField 2 3)

theorem card_GF : Nat.card (GaloisField 2 3) = 2 ^ (2 * 1 + 1) :=
  GaloisField.card 2 3 (by norm_num)

theorem suzukiModel_SzB : SuzukiModel SzB 2 3 :=
  ⟨rfl, 1, le_rfl, GaloisField 2 3, inferInstance, inferInstance, rfl, card_GF,
    ⟨MulEquiv.refl _⟩⟩

theorem suzukiModel_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p f : ℕ}
    (h : SuzukiModel Y p f) : SuzukiModel X p f := by
  obtain ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e.trans e'⟩⟩

theorem exists_equiv_tauCeti : Nonempty (SzB ≃* TauCeti.suzukiGroup 1) :=
  nonempty_mulEquiv_suzukiGroup_of_blueprint
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, suzukiModel_SzB⟩)))


theorem szB_simple : IsSimpleGroup SzB :=
  (CFSG.LieType.Ree.suzuki_simple (a := 1) (K := GaloisField 2 3) le_rfl card_GF).2.2

theorem card_SzB : Nat.card SzB = 29120 := by
  obtain ⟨e⟩ := exists_equiv_tauCeti
  rw [Nat.card_congr e.toEquiv]
  exact card_suzukiGroup


theorem exists_presentation : ∃ g : Fin 2 → SzB, IsPresentation g (wordSet rels) := by
  obtain ⟨e⟩ := exists_equiv_tauCeti
  exact ⟨_, isPresentation e.symm⟩

end Hom

@[expose] def K0 : Subgroup (Equiv.Perm (Fin 4060)) := closure {sG, tG}

section Iso


theorem exists_hom :
    ∃ φ : SzB →* Equiv.Perm (Fin 4060), φ.ker = ⊥ ∧ φ.range = K0 := by
  obtain ⟨g, hP⟩ := exists_presentation
  set f : FreeGroup (Fin 2) →* SzB := FreeGroup.lift g with hf
  set ψ : FreeGroup (Fin 2) →* Equiv.Perm (Fin 4060) :=
    FreeGroup.lift (fun i : Fin 2 => img2 sG tG i.val) with hψ
  have hsurj : Function.Surjective f := hP.lift_surjective
  have hle : f.ker ≤ ψ.ker := by
    rw [hP.ker_lift]
    exact Subgroup.normalClosure_le_normal fun r hr => MonoidHom.mem_ker.2 (lift_eq_one r hr)
  let φ : SzB →* Equiv.Perm (Fin 4060) := MonoidHom.liftOfSurjective f hsurj ⟨ψ, hle⟩
  have hcomp : ∀ x, φ (f x) = ψ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨ψ, hle⟩ x
  have hg : ∀ i : Fin 2, φ (g i) = img2 sG tG i.val := by
    intro i
    have := hcomp (FreeGroup.of i)
    simpa [hf, hψ] using this
  have hg0 : φ (g 0) = sG := by simpa [img2] using hg 0
  have hg1 : φ (g 1) = tG := by simpa [img2] using hg 1
  have hker : φ.ker = ⊥ := by
    have := szB_simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      apply sG_ne_one
      rw [← hg0]
      exact MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top _)
  refine ⟨φ, hker, ?_⟩
  have hclos : closure (Set.range g) = ⊤ := by
    rw [← FreeGroup.range_lift_eq_closure]
    exact MonoidHom.range_eq_top.2 hsurj
  rw [MonoidHom.range_eq_map, ← hclos, MonoidHom.map_closure, K0]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · left; exact hg0
    · right; exact hg1
  · rintro (rfl | rfl)
    · exact ⟨_, ⟨0, rfl⟩, hg0⟩
    · exact ⟨_, ⟨1, rfl⟩, hg1⟩

theorem exists_mulEquiv_K0 : Nonempty (SzB ≃* K0) := by
  obtain ⟨φ, hker, hrange⟩ := exists_hom
  exact ⟨(MonoidHom.ofInjective (MonoidHom.ker_eq_bot_iff φ |>.1 hker)).trans
    (MulEquiv.subgroupCongr hrange)⟩

theorem card_K0 : Nat.card K0 = 29120 := by
  obtain ⟨e⟩ := exists_mulEquiv_K0
  rw [← Nat.card_congr e.toEquiv]
  exact card_SzB

theorem K0_simple : IsSimpleGroup K0 := by
  obtain ⟨e⟩ := exists_mulEquiv_K0
  exact (MulEquiv.isSimpleGroup_congr e).1 szB_simple

theorem K0_suzukiModel : SuzukiModel K0 2 3 := by
  obtain ⟨e⟩ := exists_mulEquiv_K0
  exact suzukiModel_of_equiv e.symm suzukiModel_SzB

theorem K0_le_L : K0 ≤ ruL := by
  rw [K0, closure_le]
  rintro x (rfl | rfl)
  · exact rep_s.2
  · exact rep_t.2

end Iso

end CFSG.EvenSporadicStandard.Induction.RuSz

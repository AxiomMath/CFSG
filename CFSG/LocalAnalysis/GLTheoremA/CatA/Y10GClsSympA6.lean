module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsSympB
public import CFSG.Milestones.ASVolI.I2Natural

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem zmod_two_ringEquiv {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nonempty (ZMod 2 ≃+* K) := by
  have := Fintype.ofFinite K
  haveI : CharP K 2 := charP_two_of_card_pow (m := 1) (by rw [hK]; norm_num)
  let f : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨f.injective, ?_⟩
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK]
  exact ⟨RingEquiv.ofBijective f hbij⟩

theorem largeEvenScalars_two_subgroupOf_eq_bot {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {ι : Type} [Fintype ι] [DecidableEq ι] (H : Subgroup (GL ι K)) :
    (LargeEvenScalars ι K).subgroupOf H = ⊥ := by
  obtain ⟨c⟩ := zmod_two_ringEquiv hK
  have key : ∀ x : K, x ≠ 0 → x = 1 := by
    intro x hx
    obtain ⟨a, rfl⟩ := c.surjective x
    fin_cases a
    · exact absurd (map_zero c) hx
    · exact map_one c
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨u, hu⟩ := hg
  have hu1 : u = 1 := Units.ext (key _ u.ne_zero)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hu, hu1]
  simp

theorem commutator_statedSp_le (K : Type) [Field K] :
    ⁅StatedSp 2 K, StatedSp 2 K⁆ ≤ StatedSp 2 K := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

theorem conj_mem_derived_I (K : Type) [Field K] (g : ↥⁅StatedSp 2 K, StatedSp 2 K⁆) :
    MulAut.conj (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ g) ∈
      LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenGSpSet K 2) := by
  have hg : ((g : GL (Fin 2 ⊕ Fin 2) K)) ∈ StatedSp 2 K := commutator_statedSp_le K g.2
  refine ⟨(g : GL (Fin 2 ⊕ Fin 2) K), ⟨1, one_ne_zero, ?_⟩, fun h h' hh' => ?_⟩
  · rw [one_smul]
    exact StatedAPI.mem_statedSp_iff.1 hg
  · have hkey : h' = g * h * g⁻¹ := Subtype.ext (by rw [hh']; simp)
    change MulAut.conj (LargeEvenProjMk _ g) (LargeEvenProjMk _ h) = LargeEvenProjMk _ h'
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hkey]

theorem innDiag_B2der (S : Type) [Group S] (p : ℕ) (α : MulAut S) (labK : GLALabel)
    (htag : labK.tag = .B2der) (hp : p.Prime) (hp2 : p ≠ 2)
    (hlab : HasLabel S (fun l : GLALabel => l = labK)) (hα : α ^ p = 1) :
    InnDiagKind S labK α := by
  have hlab' : LargeEvenMarking S (fun lab _ _ _ _ _ => lab = labK) := hlab
  obtain ⟨hcomm, lab, hΛ, hraw⟩ := hlab'
  obtain ⟨_, _, _, _, hQ0⟩ := rawDatum_exists hraw
  obtain ⟨_, _, θ0, hlabEq⟩ := hQ0
  subst hlabEq
  have hrec : ∀ Q : LargeEvenRawCont, LargeEvenRawDatum lab Q ↔
      LargeEvenRecipeSymplectic 2 2 true Q := by
    intro Q
    obtain ⟨tag, rank, n⟩ := lab
    dsimp only at htag
    subst htag
    exact Iff.rfl
  obtain ⟨K, instF, instFin, hK, hQ⟩ := (hrec _).1 hraw
  obtain ⟨hsimple, hnonab, θ, -⟩ := hQ
  have hS := largeEvenScalars_two_subgroupOf_eq_bot hK ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆
  obtain ⟨c⟩ := zmod_two_ringEquiv hK
  let e1 : LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ ≃*
      ↥⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ :=
    (QuotientGroup.quotientMulEquivOfEq hS).trans QuotientGroup.quotientBot
  let e2 : ↥(alternatingGroup (Fin 6)) ≃* ↥⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ :=
    MulEquiv.ofBijective (CFSG.ASVolI.burnsideI23x_a6ι c) (CFSG.ASVolI.burnsideI23x_a6ι_bijective c)
  let eR : LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ ≃* ↥(alternatingGroup (Fin 6)) :=
    e1.trans e2.symm
  let θD : S ⧸ Subgroup.center S ≃* LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ := θ
  set φ : MulAut (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆) :=
    MulAut.congr θD (centerQuotAut S α) with hφdef
  have hφp : φ ^ p = 1 := by
    rw [hφdef, ← map_pow, ← map_pow, hα, map_one, map_one]
  have hind : LargeEvenInduces θD (fun s s' => s' = α s) φ := by
    intro l l' hll'
    subst hll'
    simp [hφdef, MulAut.congr_apply, centerQuotAut_mk]
  set ψ : MulAut (alternatingGroup (Fin 6)) := MulAut.congr eR φ with hψdef
  have hψp : ψ ^ p = 1 := by
    rw [hψdef, ← map_pow, hφp, map_one]
  have hodd : Odd (orderOf ψ) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hψp)
  obtain ⟨l, hl⟩ := CFSG.ASVolI.burnsideA315x_alt6_odd_inner hodd
  have hφconj : φ = MulAut.conj (eR.symm l) := by
    have h1 : φ = MulAut.congr eR.symm ψ := by
      rw [hψdef]
      ext y
      simp [MulAut.congr_apply]
    rw [h1, hl]
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (eR.symm l)
  have hI : φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆) (LargeEvenGSpSet K 2) := by
    rw [hφconj, ← hg]
    exact conj_mem_derived_I K g
  unfold InnDiagKind CFSG.Assembly.LargeEvenMarking
  refine ⟨hcomm, lab, hΛ, (hrec _).2 ?_⟩
  unfold LargeEvenRecipeSymplectic
  exact ⟨K, instF, instFin, hK, hsimple, hnonab, θD, rfl, φ, hI, hind⟩

theorem ClsSymp_holds : ClsSymp := by
  intro S _ _ p α labK hfam hp hp2 _ hlab hα
  rcases hfam with h | h | h
  · exact clsSympBC p α labK (Or.inl h) hp hp2 hlab hα
  · exact clsSympBC p α labK (Or.inr h) hp hp2 hlab hα
  · exact Or.inl (innDiag_B2der S p α labK h hp hp2 hlab hα)

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

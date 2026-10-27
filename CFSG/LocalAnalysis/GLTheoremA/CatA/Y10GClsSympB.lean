module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsLin
public import CFSG.Milestones.ASVolI.A3Aut.C5Sp4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {K : Type} [Field K] {m : ℕ}

theorem conj_mem_symp_I (g : StatedSp m K) :
    MulAut.conj (proj m K g) ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) := by
  refine ⟨(g : GL (Fin m ⊕ Fin m) K), ⟨1, one_ne_zero, ?_⟩, fun h h' hh' => ?_⟩
  · rw [one_smul]
    exact StatedAPI.mem_statedSp_iff.1 g.2
  · have hkey : h' = g * h * g⁻¹ := Subtype.ext (by rw [hh']; simp)
    change MulAut.conj (proj m K g) (proj m K h) = proj m K h'
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hkey]

theorem fieldAut_mem_symp_F (σ : K ≃+* K) :
    fieldAut m K σ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m)) := by
  refine ⟨σ, fun h h' hh' => ?_⟩
  have hkey : h' = fieldSp m K σ h := Subtype.ext (by
    apply Units.ext
    rw [coe_fieldSp]
    exact hh')
  change fieldAut m K σ (proj m K h) = proj m K h'
  rw [fieldAut_proj, hkey]

theorem symp_odd_aut_mem_mul_field [Finite K] [CharP K 2] (hm : 2 ≤ m)
    (α : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) (hα : Odd (orderOf α)) :
    ∃ i ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m),
      ∃ f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m)), α = i * f := by
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · obtain rfl : m = 2 := by omega
    have hmem := CFSG.ASVolI.burnsideAut_c5Sp4_odd_mem (K := K) hα
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hmem
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨σ, rfl⟩ := hz
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨_, conj_mem_symp_I g, _, fieldAut_mem_symp_F σ, rfl⟩
  · obtain ⟨i, hi, c, hc, rfl⟩ := CFSG.StandardType.AutPSp.exists_mul_compl (n := m) (K := K) h3 α
    obtain ⟨x, rfl⟩ := hi
    obtain ⟨σ, rfl⟩ := hc
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨_, conj_mem_symp_I g, _, fieldAut_mem_symp_F σ, rfl⟩

theorem famSympBC_recipe {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hfam : lab.tag = .B ∨ lab.tag = .C) :
    ∃ (m n : ℕ), 2 ≤ m ∧ 1 ≤ n ∧
      ∀ Q : LargeEvenRawCont, LargeEvenRawDatum lab Q ↔ LargeEvenRecipeSymplectic m (2 ^ n) false Q := by
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hn, hT⟩ := hΛ
  dsimp only at hn hT
  rcases hfam with h | h
  · subst h
    exact ⟨rank, n, by omega, hn, fun Q => Iff.rfl⟩
  · subst h
    exact ⟨rank, n, by omega, hn, fun Q => Iff.rfl⟩

theorem clsSympBC {S : Type} [Group S] (p : ℕ) (α : MulAut S) (labK : GLALabel)
    (hfam : labK.tag = .B ∨ labK.tag = .C) (hp : p.Prime) (hp2 : p ≠ 2)
    (hlab : HasLabel S (fun l : GLALabel => l = labK)) (hα : α ^ p = 1) :
    InnDiagKind S labK α ∨ FieldKind S labK α := by
  have hlab' : LargeEvenMarking S (fun lab _ _ _ _ _ => lab = labK) := hlab
  obtain ⟨hcomm, lab, hΛ, hraw⟩ := hlab'
  obtain ⟨_, _, _, _, hQ0⟩ := rawDatum_exists hraw
  obtain ⟨_, _, θ0, hlabEq⟩ := hQ0
  subst hlabEq
  have hfam' : lab.tag = .B ∨ lab.tag = .C := hfam
  obtain ⟨m, n, hm, hn, hiff⟩ := famSympBC_recipe hΛ hfam'
  obtain ⟨K, instF, instFin, hK, hQ⟩ := (hiff _).1 hraw
  obtain ⟨hsimple, hnonab, θ, -⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card_pow hK
  set φ : MulAut (LargeEvenProj (LargeEvenSpGroup K m)) :=
    MulAut.congr θ (centerQuotAut S α) with hφdef
  have hφp : φ ^ p = 1 := by
    rw [hφdef, ← map_pow, ← map_pow, hα, map_one, map_one]
  have hodd : Odd (orderOf φ) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hφp)
  have hind : LargeEvenInduces θ (fun s s' => s' = α s) φ := by
    intro l l' hll'
    subst hll'
    simp [hφdef, MulAut.congr_apply, centerQuotAut_mk]
  have hrec : ∀ Q : LargeEvenRawCont,
      Q (LargeEvenProj (LargeEvenSpGroup K m))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) →
      LargeEvenRecipeSymplectic m (2 ^ n) false Q := by
    intro Q hQK
    unfold LargeEvenRecipeSymplectic
    exact ⟨K, instF, instFin, hK, hQK⟩
  by_cases hI : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)
  · left
    unfold InnDiagKind CFSG.Assembly.LargeEvenMarking
    exact ⟨hcomm, lab, hΛ, (hiff _).2 (hrec _ ⟨hsimple, hnonab, θ, rfl, φ, hI, hind⟩)⟩
  · right
    obtain ⟨i, hi, f, hf, hφif⟩ := symp_odd_aut_mem_mul_field hm φ hodd
    have hnotI : ¬ ∃ i' ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m),
        LargeEvenInduces θ (fun s s' => s' = α s) i' := by
      rintro ⟨i', hi', hind'⟩
      apply hI
      rw [← induces_unique hind' hind]
      exact hi'
    have hindif : LargeEvenInduces θ (fun s s' => s' = α s) (i * f) := by
      rw [← hφif]
      exact hind
    unfold FieldKind CFSG.Assembly.LargeEvenMarking
    exact ⟨hcomm, lab, hΛ, (hiff _).2 (hrec _
      ⟨hsimple, hnonab, θ, rfl, ⟨i, hi, f, hf, hindif⟩, hnotI⟩)⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

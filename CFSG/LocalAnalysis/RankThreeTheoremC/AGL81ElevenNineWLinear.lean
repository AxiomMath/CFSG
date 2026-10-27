module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveLinear
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveBlockOK
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexLinearDiag
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Index

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)
open CFSG.RankThree.PartOne.OutStructure
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus (IsWBlock)
open scoped commutatorElement

section LinData

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {I : Set ℕ}

theorem odd_relIndex_linLeviHom :
    Odd ((Subgroup.pi Set.univ (linBlockSL K n I)).relIndex (linLeviHom K n I).range) := by
  have h : ¬ 2 ∣ (Subgroup.pi Set.univ (linBlockSL K n I)).relIndex (linLeviHom K n I).range :=
    ParabCensus.not_two_dvd_relIndex_pi (S := linBlockSL K n I) (T := fun _ => ⊤)
      (fun _ => le_top) pi_le_range_linLeviHom (by rw [Subgroup.pi_top]; exact le_top)
      fun a => by
        rw [Subgroup.relIndex_top_right]
        exact ParabCensus.not_two_dvd_index_range_toGL (K := K) (linBlockLen n I a)
  exact Nat.not_even_iff_odd.mp fun he => h (even_iff_two_dvd.mp he)

theorem linBlockSL_bot_or_wBlock (a : Fin n) :
    linBlockSL K n I a = ⊥ ∨ IsWBlock ↥(linBlockSL K n I a) := by
  rcases ParabCensus.range_toGL_cases (K := K) (linBlockLen n I a) with h | ⟨-, -, h⟩ | ⟨hq, ho⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl ⟨hq, ho⟩)

theorem blockOKP_linBlockSL {p : ℕ} [OddPrime p] (a : Fin n) (h : linBlockSL K n I a ≠ ⊥) :
    BlockOKP p ⊤ (linBlockSL K n I a) := by
  rcases ParabCensus.range_toGL_cases (K := K) (linBlockLen n I a) with h' | ⟨-, hm, -⟩ |
      ⟨hq, -⟩
  · exact absurd h' h
  · exact blockOK_gl_slP _ (by omega)
  · exact blockOK_gl_slP _ (two_le_of_isQuasisimple_specialLinear
      (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) (linBlockLen n I a)).symm hq))

theorem conj_mem_linBlockSL (a : Fin n) (g : GL (Fin (linBlockLen n I a)) K)
    {s : GL (Fin (linBlockLen n I a)) K} (hs : s ∈ linBlockSL K n I a) :
    g * s * g⁻¹ ∈ linBlockSL K n I a := by
  have hN : (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin (linBlockLen n I a)) K →* GL _ K).range.Normal := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    infer_instance
  exact hN.conj_mem s hs g

theorem eq_one_of_mem_map_mulSingle (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hIne : I.Nonempty)
    (x : ↥(flagStabilizer n K I))
    (hx : (x : SpecialLinearGroup (Fin n) K) ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    {j : Fin n} {E : Subgroup (GL (Fin (linBlockLen n I j)) K)}
    (h : linLeviHom K n I x ∈
      E.map (MonoidHom.mulSingle (fun a : Fin n => GL (Fin (linBlockLen n I a)) K) j)) :
    x = 1 := by
  refine eq_one_of_scalar_of_single_block (j := j) hI hIne x hx fun a haj => ?_
  obtain ⟨y, -, hyx⟩ := h
  rw [← hyx]
  exact Pi.mulSingle_eq_of_ne (M := fun a : Fin n => GL (Fin (linBlockLen n I a)) K) haj y

theorem odd_card_ker_of_le_center {M : Type*} [Group M] (hn : 1 ≤ n)
    (ρ : SpecialLinearGroup (Fin n) K →* M)
    (hker : ρ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K)) :
    Odd (Nat.card ρ.ker) := by
  refine Odd.of_dvd_nat ?_ (Subgroup.card_dvd_of_le hker)
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
    (CFSG.RankThree.PartTwo.Census.coprime_card_center_SL hn).symm

end LinData

theorem actsInnerlyW_linear_of_compatP (p : ℕ) [OddPrime p] {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} [L.Normal] (hCP : CompParab L P) {n : ℕ} (hn : 3 ≤ n) {F : Type}
    [Field F] [Finite F] [CharP F 2]
    (ρ : SpecialLinearGroup (Fin n) F →* ↥L) (hρs : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F)) {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hIne : I.Nonempty)
    (hcomap : (P.subgroupOf L).comap ρ = flagStabilizer n F I) (A : GL (Fin n) F) {a : Y}
    (haN : a ∈ Subgroup.normalizer (P : Set Y))
    (hcm : ∀ x : SpecialLinearGroup (Fin n) F, (MulAut.conjNormal a : MulAut ↥L) (ρ x) *
      (ρ (slConjugation n F A x))⁻¹ ∈ Subgroup.center ↥L)
    (hpow : ∃ m : ℕ, ∀ w ∈ wPre P, a ^ (p ^ m) * w = w * a ^ (p ^ m))
    (hrk : Open.pRank p (wPre P) ≤ 1) :
    ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅a * v, w⁆ ∈ pCoreOf 2 P := by
  classical
  have hmemQ : ∀ x : SpecialLinearGroup (Fin n) F,
      x ∈ flagStabilizer n F I ↔ ((ρ x : ↥L) : Y) ∈ P := fun x => by
    rw [← hcomap]; rfl
  have hQA : ∀ x ∈ flagStabilizer n F I, slConjugation n F A x ∈ flagStabilizer n F I := by
    intro x hx
    rw [hmemQ] at hx ⊢
    have h1 := hcm x
    have h2 : ρ (slConjugation n F A x) =
        ((MulAut.conjNormal a : MulAut ↥L) (ρ x) * (ρ (slConjugation n F A x))⁻¹)⁻¹ *
          (MulAut.conjNormal a : MulAut ↥L) (ρ x) := by group
    rw [h2]
    exact P.mul_mem (center_le_of_compParab hCP (Subgroup.inv_mem _ h1))
      ((Subgroup.mem_normalizer_iff.1 haN _).1 hx)
  have hn0 : 0 < n := by omega
  set δ := GeneralLinearGroup.det A with hδ
  set d : Fin n → Fˣ := Function.update (1 : Fin n → Fˣ) ⟨0, hn0⟩ δ with hd
  have hdet : GeneralLinearGroup.det (diagGL d : GL (Fin n) F) = δ := by
    rw [det_diagGL, hd, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have hker1 : A * (diagGL d : GL (Fin n) F)⁻¹ ∈
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, map_mul, map_inv, hdet,
      mul_inv_cancel]
  obtain ⟨s, hs⟩ := hker1
  have hAs : A = SpecialLinearGroup.toGL s * diagGL d := by
    rw [hs]; group
  have hconjA : ∀ x, slConjugation n F A x =
      s * slConjugation n F (diagGL d) x * s⁻¹ := by
    intro x
    rw [hAs, map_mul, MulAut.mul_apply, slConjugation_toGL_apply]
  have hsQ : s ∈ flagStabilizer n F I := by
    refine mem_of_normalizes_coverSub hCP ρ hρs hcomap.symm fun x hx => ?_
    have h1 : slConjugation n F (diagGL (d⁻¹)) x ∈ flagStabilizer n F I :=
      slConjugation_diagGL_mem _ hx
    have h2 := hQA _ h1
    rw [hconjA] at h2
    have h3 : slConjugation n F (diagGL d) (slConjugation n F (diagGL (d⁻¹)) x) = x := by
      rw [← MulAut.mul_apply, ← map_mul, ← diagGL_inv, mul_inv_cancel, map_one, MulAut.one_apply]
    rwa [h3] at h2
  set Q := flagStabilizer n F I with hQdef
  let φ₀ : ↥Q →* ↥Q := ((slConjugation n F A).toMonoidHom.comp Q.subtype).codRestrict Q
    fun x => hQA x x.2
  have hφinj : Function.Injective φ₀ := fun x y h =>
    Subtype.ext ((slConjugation n F A).injective (congrArg Subtype.val h))
  have hφsurj : Function.Surjective φ₀ := Finite.injective_iff_surjective.1 hφinj
  let φ : MulAut ↥Q := MulEquiv.ofBijective φ₀ ⟨hφinj, hφsurj⟩
  have hφval : ∀ x : ↥Q, ((φ x : ↥Q) : SpecialLinearGroup (Fin n) F) =
      slConjugation n F A (x : SpecialLinearGroup (Fin n) F) := fun x => rfl
  let ĥ : ∀ a : Fin n, GL (Fin (linBlockLen n I a)) F := fun a => diagBlk I d a
  let g : ∀ a : Fin n, GL (Fin (linBlockLen n I a)) F :=
    linLeviHom F n I ⟨s, hsQ⟩ * ĥ
  have hφ : ∀ x : ↥Q, linLeviHom F n I (φ x) = g * linLeviHom F n I x * g⁻¹ := by
    intro x
    have hxh := slConjugation_diagGL_mem d x.2
    have e1 : φ x = ⟨s, hsQ⟩ * ⟨slConjugation n F (diagGL d) (x : SpecialLinearGroup (Fin n) F),
        hxh⟩ * ⟨s, hsQ⟩⁻¹ := Subtype.ext (hconjA _)
    rw [e1, map_mul, map_mul, map_inv, linLeviHom_slConjugation_diagGL d x hxh]
    simp only [g, ĥ]
    group
  refine ParabCensus.actsInnerlyW_of_levi_dataP (OddPrime.ne_two p)
    (K := SpecialLinearGroup (Fin n) F) (G := fun a : Fin n => GL (Fin (linBlockLen n I a)) F)
    hCP.parab.1 hCP.odd ρ hρs hker (odd_card_ker_of_le_center (by omega) ρ hker) Q
    hcomap.symm (linBlockSL F n I) (fun _ => ⊤) (linLeviHom F n I)
    (isPGroup_ker_linLeviHom (by omega)) pi_le_range_linLeviHom commutator_range_linLeviHom_le
    odd_relIndex_linLeviHom linBlockSL_bot_or_wBlock (fun a ha => blockOKP_linBlockSL a ha)
    (fun j E _ _ _ x hρx hβx => eq_one_of_mem_map_mulSingle hI hIne x (hker hρx) hβx)
    (fun j _ x hρx hβx => by rw [eq_one_of_mem_map_mulSingle hI hIne x (hker hρx) hβx, map_one])
    φ g (fun _ => Subgroup.mem_top _) hφ (fun a s hs => conj_mem_linBlockSL a (g a) hs) haN
    (fun x => ?_) hpow hrk
  rw [hφval]
  exact hcm _

theorem fieldIndexOnPW_linear (p : ℕ) [OddPrime p]
    (hGA : GriessAllModelsStatement) :
    FieldIndexOnPW p (IsLieOf IdxA) := by
  intro Y _ _ L P hCP hA hLn hrank h3 hrk a ha3 haN hout
  haveI := hLn
  obtain ⟨n, f, ρ, e, I, hn, hf, hρs, hker, hcompat, hI, hIne, -, hcomap⟩ :=
    ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP hA
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  have hD : PCentral p
      ((linearAutGroup n (GaloisField 2 f)).comap (MulAut.congr e).toMonoidHom) :=
    pCentral_comap_of_mulEquiv (MulAut.congr e) (linear_pCentralP p hn)
  refine fieldIndexW_coreP hD ha3 hout fun hmem => ?_
  obtain ⟨A, hA'⟩ := mem_linearAutGroup_iff.1 (Subgroup.mem_comap.1 hmem)
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine actsInnerlyW_linear_of_compatP p hCP hn ρ hρs hker hI hIne hcomap A haN (fun x => ?_)
    ⟨k, fun w _ => by rw [hak, one_mul, mul_one]⟩ hrk
  have h1 : conjAut n (GaloisField 2 f) A (proj n (GaloisField 2 f) x) =
      MulAut.congr e (convAut L a) (proj n (GaloisField 2 f) x) := by
    rw [hA']; rfl
  rw [conjAut_proj] at h1
  have hx : e.symm (proj n (GaloisField 2 f) x) = QuotientGroup.mk (ρ x) := by
    rw [← hcompat x]; exact e.symm_apply_apply _
  have h1' : MulAut.congr e (convAut L a) (proj n (GaloisField 2 f) x) =
      e (convAut L a (e.symm (proj n (GaloisField 2 f) x))) := rfl
  rw [h1', hx] at h1
  have h2 : (QuotientGroup.mk (ρ (slConjugation n (GaloisField 2 f) A x)) :
      ↥L ⧸ Subgroup.center ↥L) = convAut L a (QuotientGroup.mk (ρ x)) := by
    apply e.injective
    rw [hcompat]
    exact h1
  have h3' : convAut L a (QuotientGroup.mk (ρ x)) =
      (QuotientGroup.mk ((MulAut.conjNormal a : MulAut ↥L) (ρ x)) : ↥L ⧸ Subgroup.center ↥L) :=
    rfl
  rw [h3'] at h2
  simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.1 h2.symm

end CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW

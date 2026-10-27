module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexLinear
public import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexBlockOK
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTransport
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)
open CFSG.RankThree.PartOne.OutStructure
open scoped commutatorElement

section Tower

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem linear_pCentral (hn : 3 ≤ n) : PCentral 3 (linearAutGroup n K) := by
  obtain ⟨hgenTop, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, hDn, -, -, ⟨g, -, hg⟩, -, hidx, -, -⟩ :=
    standard_outer_quotients (n := n) (K := K)
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have : Finite (MulAut (projectiveSL n K)) := inferInstance
  have hDnorm : (linearAutGroup n K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hpE : ∀ α : MulAut (projectiveSL n K), (∃ k : ℕ, α ^ (3 ^ k) ∈ linearAutGroup n K) →
      α ∈ semilinearAutGroup n K := by
    rintro α ⟨k, hk⟩
    have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
      have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2
    have hpodd : Odd (3 ^ k) := (Nat.Prime.odd_of_ne_two Nat.prime_three (by norm_num)).pow
    exact mem_of_pow_mem_of_index_le_two _ hidx' hpodd (linearAutGroup_le_semilinearAutGroup hk)
  have hD3 : ∀ γ α : MulAut (projectiveSL n K), α ∈ semilinearAutGroup n K →
      ⁅γ, α⁆ ∈ linearAutGroup n K := by
    intro γ α hα
    obtain ⟨B, τ, rfl⟩ := mem_semilinearAutGroup_iff.mp hα
    obtain ⟨A, σ, ε, hε, rfl⟩ := hgen γ
    set π := QuotientGroup.mk' (linearAutGroup n K) with hπ
    have hπc : ∀ C : GL (Fin n) K, π (conjAut n K C) = 1 := fun C =>
      (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup C)
    have hfσ : Commute (π (fieldAut n K σ)) (π (fieldAut n K τ)) := by
      have h1 : fieldAut n K σ * fieldAut n K τ = fieldAut n K τ * fieldAut n K σ := by
        rw [htrans.2.1, htrans.2.1, ringAut_comm K σ τ]
      have h3 := congrArg π h1
      rw [map_mul π, map_mul π] at h3
      exact h3
    have hδf : Commute (π (dualAut n K)) (π (fieldAut n K τ)) := by
      have h1 : dualAut n K * fieldAut n K τ = fieldAut n K τ * dualAut n K := by
        have h2 := htrans.2.2.2.2.2.1 τ
        calc dualAut n K * fieldAut n K τ
            = (dualAut n K * fieldAut n K τ * dualAut n K) * dualAut n K := by
              rw [mul_assoc (dualAut n K * fieldAut n K τ), htrans.2.2.2.1, mul_one]
          _ = fieldAut n K τ * dualAut n K := by rw [h2]
      have h3 := congrArg π h1
      rw [map_mul π, map_mul π] at h3
      exact h3
    have hc : Commute (π (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε))
        (π (conjAut n K B * fieldAut n K τ)) := by
      rw [map_mul, map_mul, map_mul, hπc, hπc, one_mul, one_mul, map_pow]
      exact (hfσ.mul_left (hδf.pow_left ε))
    have h1 : π ⁅conjAut n K A * fieldAut n K σ * dualAut n K ^ ε,
        conjAut n K B * fieldAut n K τ⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hc
    exact (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨hDnorm, fun α hα γ => hD3 γ α (hpE α hα)⟩

end Tower

theorem pCentral_comap_of_mulEquiv {p : ℕ} {Γ Γ' : Type*} [Group Γ] [Group Γ'] (ψ : Γ ≃* Γ')
    {D : Subgroup Γ'} (hD : PCentral p D) : PCentral p (D.comap ψ.toMonoidHom) := by
  haveI := hD.1
  refine ⟨inferInstance, fun α ⟨k, hk⟩ γ => ?_⟩
  have h1 : ψ α ^ (p ^ k) ∈ D := by
    rw [← map_pow]
    exact hk
  have h2 := hD.2 (ψ α) ⟨k, h1⟩ (ψ γ)
  rw [Subgroup.mem_comap]
  simpa only [MulEquiv.coe_toMonoidHom, map_commutatorElement] using h2

section Diag

variable {F : Type} [Field F] {n : ℕ} {I : Set ℕ}

@[expose] def diagGL (d : Fin n → Fˣ) : GL (Fin n) F where
  val := diagonal fun i => (d i : F)
  inv := diagonal fun i => (((d i)⁻¹ : Fˣ) : F)
  val_inv := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  inv_val := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem diagGL_val (d : Fin n → Fˣ) :
    ((diagGL d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal fun i => (d i : F) :=
  rfl

theorem diagGL_inv_val (d : Fin n → Fˣ) :
    (((diagGL d : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun i => (((d i)⁻¹ : Fˣ) : F) :=
  rfl

theorem slConjugation_diagGL_mem (d : Fin n → Fˣ) {x : SpecialLinearGroup (Fin n) F}
    (hx : x ∈ flagStabilizer n F I) :
    slConjugation n F (diagGL d) x ∈ flagStabilizer n F I := by
  refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
  have h0 := CFSG.AGLEmbedding.ToralCensus.apply_eq_zero_of_mem_flagStabilizer (Or.inr hc) hx hl
    hk
  rw [slConjugation_entry, diagGL_val, diagGL_inv_val]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, h0]
  simp

@[expose] noncomputable def diagBlk (I : Set ℕ) (d : Fin n → Fˣ) (a : Fin n) :
    GL (Fin (linBlockLen n I a)) F :=
  diagGL fun i => d ⟨(a : ℕ) + i, by have := linBlockLen_le (I := I) a; have := i.isLt; omega⟩

theorem linLeviHom_slConjugation_diagGL (d : Fin n → Fˣ) (x : ↥(flagStabilizer n F I))
    (hy : slConjugation n F (diagGL d) (x : SpecialLinearGroup (Fin n) F) ∈
      flagStabilizer n F I) :
    linLeviHom F n I ⟨slConjugation n F (diagGL d) (x : SpecialLinearGroup (Fin n) F), hy⟩ =
      (fun a => diagBlk I d a) * linLeviHom F n I x * (fun a => diagBlk I d a)⁻¹ := by
  funext a
  apply Units.ext
  ext i j
  rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, Units.val_mul, Units.val_mul]
  simp only [coe_linLeviHom_apply, blkAt_apply, slConjugation_entry, diagBlk, diagGL_val,
    diagGL_inv_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem slConjugation_toGL_apply (s x : SpecialLinearGroup (Fin n) F) :
    slConjugation n F (SpecialLinearGroup.toGL s) x = s * x * s⁻¹ := by
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation, map_mul, map_mul, map_inv]

theorem diagGL_inv (d : Fin n → Fˣ) : (diagGL d : GL (Fin n) F)⁻¹ = diagGL (d⁻¹) :=
  Units.ext rfl

theorem det_diagGL (d : Fin n → Fˣ) :
    GeneralLinearGroup.det (diagGL d : GL (Fin n) F) = ∏ i, d i := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, diagGL_val, Matrix.det_diagonal, Units.coe_prod]

theorem mem_of_normalizes_coverSub {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hCP : CompParab L P) {K : Type} [Group K] (ρ : K →* ↥L) (hρs : Function.Surjective ρ)
    {Q : Subgroup K} (hQ : Q = (P.subgroupOf L).comap ρ) {s : K}
    (hs : ∀ x ∈ Q, s * x * s⁻¹ ∈ Q) : s ∈ Q := by
  have hmemQ : ∀ x : K, x ∈ Q ↔ ((ρ x : ↥L) : Y) ∈ P := fun x => by
    rw [hQ]; rfl
  have hN : ((ρ s : ↥L) : Y) ∈ Subgroup.normalizer (P : Set Y) := by
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    obtain ⟨x, hx⟩ := hρs ⟨p, hCP.parab.1 hp⟩
    have hxQ : x ∈ Q := (hmemQ x).2 (by rw [hx]; exact hp)
    have h1 := (hmemQ _).1 (hs x hxQ)
    simpa [map_mul, map_inv, hx] using h1
  exact (hmemQ s).2 (CFSG.HardMathSupport.Curtis.UnitaryLevi.mem_of_mem_normalizer_of_isParabolicTwo
    hCP.parab (ρ s).2 hN)

theorem center_le_of_compParab {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hCP : CompParab L P) {z : ↥L} (hz : z ∈ Subgroup.center ↥L) : (z : Y) ∈ P := by
  obtain ⟨-, T, ⟨hTL, -, -⟩, hN⟩ := hCP.parab
  refine hN ⟨z.2, ?_⟩
  show (z : Y) ∈ Subgroup.normalizer (T : Set Y)
  rw [Subgroup.mem_normalizer_iff]
  intro t
  have hc : ∀ t' ∈ L, (z : Y) * t' = t' * z := fun t' ht' =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨t', ht'⟩).symm
  constructor
  · intro ht
    have := hc t (hTL ht)
    rw [this, mul_inv_cancel_right]
    exact ht
  · intro ht
    have htL : t ∈ L := by
      have := L.mul_mem (L.mul_mem (L.inv_mem z.2) (hTL ht)) z.2
      simpa [mul_assoc] using this
    have := hc t htL
    rwa [this, mul_inv_cancel_right] at ht

end Diag

theorem actsInnerly_linear_of_compat {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    [L.Normal] (hCP : CompParab L P) {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2]
    (ρ : SpecialLinearGroup (Fin n) F →* ↥L) (hρs : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F)) {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hIne : I.Nonempty)
    (hcomap : (P.subgroupOf L).comap ρ = flagStabilizer n F I) (A : GL (Fin n) F) {a : Y}
    (haN : a ∈ Subgroup.normalizer (P : Set Y))
    (hcm : ∀ x : SpecialLinearGroup (Fin n) F, (MulAut.conjNormal a : MulAut ↥L) (ρ x) *
      (ρ (slConjugation n F A x))⁻¹ ∈ Subgroup.center ↥L)
    (hpow : ∃ m : ℕ, ∀ w ∈ perfectJoin P, a ^ (3 ^ m) * w = w * a ^ (3 ^ m))
    (hrk : Open.pRank 3 (perfectJoin P) ≤ 1) :
    ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P) := by
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
  refine actsInnerly_of_levi_data (K := SpecialLinearGroup (Fin n) F)
    (G := fun a : Fin n => GL (Fin (linBlockLen n I a)) F) hCP.parab.1 ρ hρs hker Q
    hcomap.symm (linBlockSL F n I) (fun _ => ⊤) (linLeviHom F n I)
    (isPGroup_ker_linLeviHom (by omega)) pi_le_range_linLeviHom commutator_range_linLeviHom_le
    (isQuasisimple_or_isSolvable_linBlockSL I) (fun a hq => ?_)
    (fun j E _ _ _ x hρx hβx => ?_) φ g (fun _ => Subgroup.mem_top _) hφ (a := a)
    (fun x => ?_) hpow hrk
  · have hm := two_le_of_isQuasisimple_specialLinear
      (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := F) (linBlockLen n I a)).symm hq)
    exact blockOK_gl_sl (linBlockLen n I a) hm
  · refine eq_one_of_scalar_of_single_block (j := j) hI hIne x (hker hρx) fun a haj => ?_
    obtain ⟨y, hy, hyx⟩ := hβx
    rw [← hyx]
    exact Pi.mulSingle_eq_of_ne (M := fun a : Fin n => GL (Fin (linBlockLen n I a)) F) haj y
  · rw [hφval]
    exact hcm _

theorem fieldIndexOn_linear
    (hGA : GriessAllModelsStatement) : FieldIndexOn (IsLieOf IdxA) := by
  intro Y _ _ L P hCP hA hLn hrank h3 hrk a ha3 haN hout
  haveI := hLn
  obtain ⟨n, f, ρ, e, I, hn, hf, hρs, hker, hcompat, hI, hIne, -, hcomap⟩ :=
    ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP hA
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  have hD : PCentral 3
      ((linearAutGroup n (GaloisField 2 f)).comap (MulAut.congr e).toMonoidHom) :=
    pCentral_comap_of_mulEquiv (MulAut.congr e) (linear_pCentral hn)
  refine fieldIndex_core hD ha3 hout fun hmem => ?_
  obtain ⟨A, hA'⟩ := mem_linearAutGroup_iff.1 (Subgroup.mem_comap.1 hmem)
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine actsInnerly_linear_of_compat hCP hn ρ hρs hker hI hIne hcomap A haN (fun x => ?_)
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

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

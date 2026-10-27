module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Open.StatedAPI CFSG.LieType.SemisimpleCentralizers
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.StandardType.LinNonsplit
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.PComp
open scoped commutatorElement MatrixGroups

@[expose] def factorSL' {r : ℕ} (D : Fin r → Type) [∀ i, Field (D i)] (d : Fin r → ℕ) (i : Fin r) :
    Subgroup (∀ j, GL (Fin (d j)) (D j)) :=
  (StatedSL (d i) (D i)).map (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)

instance factorSL'_normal {r : ℕ} (D : Fin r → Type) [∀ i, Field (D i)] (d : Fin r → ℕ) (i : Fin r) :
    (factorSL' D d i).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
  rw [mulSingle_conj']
  exact Subgroup.mem_map.mpr ⟨_, (statedSL_normal' (d i) (D i)).conj_mem w hw (g i), rfl⟩

theorem l154_not_isSolvable_of_isQuasisimple {G : Type*} [Group G] (hq : CFSG.Open.IsQuasisimple G) :
    ¬ Group.IsSolvable G := by
  intro hs
  haveI : Group.IsPerfect G := ⟨hq.1⟩
  haveI : Nontrivial G := by
    haveI := hq.2
    obtain ⟨a, b, hab⟩ := exists_pair_ne (G ⧸ Subgroup.center G)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [h])⟩
  exact Group.IsPerfect.not_isSolvable G hs

theorem linear_pcomp_core' {F : Type} [Field F] [Finite F] {n r : ℕ}
    {D : Fin r → Type} [∀ i, Field (D i)] [∀ i, Finite (D i)] {d : Fin r → ℕ}
    (θ : (∀ j, GL (Fin (d j)) (D j)) →* GL (Fin n) F) (hθ : Function.Injective θ)
    (p : ℕ) (M : Subgroup (GL (Fin n) F))
    (hM : GLAPComponent p (((StatedSL n F).comap θ).map θ) M) :
    ∃ i : Fin r, 2 ≤ d i ∧ (d i ≠ 2 ∨ Nat.card (D i) ≠ 2) ∧ (d i ≠ 2 ∨ Nat.card (D i) ≠ 3) ∧
      M = (factorSL' D d i).map θ := by
  classical
  obtain ⟨KP, hKP⟩ : ∃ KP : Subgroup (∀ j, GL (Fin (d j)) (D j)),
      KP = (StatedSL n F).comap θ := ⟨_, rfl⟩
  have memKP : ∀ x, x ∈ KP ↔ θ x ∈ StatedSL n F := fun x => by rw [hKP]; rfl
  haveI hKPn : KP.Normal := by rw [hKP]; infer_instance
  obtain ⟨T, hT⟩ : ∃ T : Fin r → Subgroup (∀ j, GL (Fin (d j)) (D j)),
      ∀ i, T i = factorSL' D d i ⊓ KP := ⟨fun i => factorSL' D d i ⊓ KP, fun i => rfl⟩
  haveI hTn : ∀ i, (T i).Normal := fun i => by rw [hT i]; infer_instance
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup (∀ j, GL (Fin (d j)) (D j)), Q = ⨆ i, T i := ⟨_, rfl⟩
  haveI hQn : Q.Normal := by rw [hQ]; infer_instance
  have hQKP : Q ≤ KP := by
    rw [hQ]
    exact iSup_le fun i => by rw [hT i]; exact inf_le_right
  obtain ⟨E, hE⟩ : ∃ E : Subgroup (GL (Fin n) F), E = Q.map θ := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Fin r → Subgroup (GL (Fin n) F),
      ∀ i, L i = (T i).map θ := ⟨fun i => (T i).map θ, fun i => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Subgroup (GL (Fin n) F), X = KP.map θ := ⟨_, rfl⟩
  rw [← hKP, ← hX] at hM
  have memX : ∀ y, y ∈ X ↔ ∃ k ∈ KP, θ k = y := by
    intro y
    rw [hX, Subgroup.mem_map]
  have hEX : E ≤ X := by
    rw [hE, hX]
    exact Subgroup.map_mono hQKP
  have hcommQ : ∀ k l : (∀ j, GL (Fin (d j)) (D j)), ⁅k, l⁆ ∈ Q := by
    intro k l
    rw [hQ]
    apply mem_iSup_of_mulSingle_mem T
    intro i
    have hmul : MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i (⁅k, l⁆ i) =
        ⁅MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i (k i),
          MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i (l i)⁆ := by
      rw [← map_commutatorElement]
      congr 1
    rw [hmul, hT i, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_map.mpr ⟨⁅k i, l i⁆, commutatorElement_mem_statedSL _ _, ?_⟩, ?_⟩
    · rw [map_commutatorElement]
    · rw [memKP, map_commutatorElement]
      exact commutatorElement_mem_statedSL _ _
  have hEn : (E.subgroupOf X).Normal := by
    refine ⟨fun e he g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at he ⊢
    obtain ⟨k, -, hkg⟩ := (memX _).mp g.2
    rw [hE] at he ⊢
    obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp he
    refine Subgroup.mem_map.mpr ⟨k * q * k⁻¹, hQn.conj_mem q hq k, ?_⟩
    simp [map_mul, map_inv, hkg, hqe]
  haveI hEn' : (E.subgroupOf X).Normal := hEn
  have hsolv : Group.IsSolvable (X ⧸ E.subgroupOf X) := by
    apply Group.isSolvable_of_comm
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    obtain ⟨k, -, hkx⟩ := (memX _).mp x.2
    obtain ⟨l, -, hly⟩ := (memX _).mp y.2
    have hc : ((x : GL (Fin n) F) * (y : GL (Fin n) F))⁻¹ *
        ((y : GL (Fin n) F) * (x : GL (Fin n) F)) = θ ⁅l⁻¹, k⁻¹⁆ := by
      rw [← hkx, ← hly]
      simp only [map_commutatorElement, map_inv, map_mul, commutatorElement_def]
      group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc, hE]
    exact Subgroup.mem_map.mpr ⟨_, hcommQ l⁻¹ k⁻¹, rfl⟩
  have hE_eq : E = ⨆ i, L i := by
    rw [hE, hQ, Subgroup.map_iSup]
    simp only [hL]
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, Commute x y := by
    intro i j hij x hx y hy
    rw [hL i] at hx
    rw [hL j] at hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hT i] at ha
    rw [hT j] at hb
    obtain ⟨hfa, -⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨hfb, -⟩ := Subgroup.mem_inf.mp hb
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hfa
    obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.mp hfb
    exact (commute_mulSingle_of_ne hij u v).map θ
  have hLq : ∀ i, (2 ≤ d i ∧ (d i ≠ 2 ∨ Nat.card (D i) ≠ 2) ∧ (d i ≠ 2 ∨ Nat.card (D i) ≠ 3) ∧
      L i = (factorSL' D d i).map θ ∧ CFSG.Open.IsQuasisimple ↥(L i)) ∨ Group.IsSolvable ↥(L i) := by
    intro i
    by_cases hperf : 2 ≤ d i ∧ (d i ≠ 2 ∨ Nat.card (D i) ≠ 2) ∧ (d i ≠ 2 ∨ Nat.card (D i) ≠ 3)
    · left
      obtain ⟨h2, h22, h23⟩ := hperf
      have hcommKP : ∀ x y : GL (Fin (d i)) (D i),
          MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i ⁅x, y⁆ ∈ KP := by
        intro x y
        rw [memKP]
        have hxy : MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i ⁅x, y⁆ =
            ⁅MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i x,
              MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i y⁆ :=
          map_commutatorElement _ _ _
        rw [hxy, map_commutatorElement]
        exact commutatorElement_mem_statedSL _ _
      have hle : factorSL' D d i ≤ KP := by
        intro w hw
        obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hw
        have hperfH := Group.isPerfect_def.mp (hct_isPerfect_statedSL (D i) h2 h22 h23)
        have hle' : (⊤ : Subgroup ↥(StatedSL (d i) (D i))) ≤
            ((KP.comap (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)).subgroupOf
              (StatedSL (d i) (D i))) := by
          rw [← hperfH]
          refine Subgroup.commutator_le.mpr (fun x _ y _ => ?_)
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
          have e : ((⁅x, y⁆ : ↥(StatedSL (d i) (D i))) : GL (Fin (d i)) (D i)) =
              ⁅(x : GL (Fin (d i)) (D i)), (y : GL (Fin (d i)) (D i))⁆ := by
            simp [commutatorElement_def]
          rw [e]
          exact hcommKP _ _
        have := Subgroup.mem_subgroupOf.mp (hle' (Subgroup.mem_top ⟨g, hg⟩))
        exact Subgroup.mem_comap.mp this
      have hTi : T i = factorSL' D d i := by rw [hT i, inf_eq_left.mpr hle]
      have hLi : L i = (factorSL' D d i).map θ := by rw [hL i, hTi]
      have e1 : ↥(StatedSL (d i) (D i)) ≃* ↥(factorSL' D d i) :=
        Subgroup.equivMapOfInjective (StatedSL (d i) (D i))
          (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)
          (mulSingle_injective' i)
      have e2 : ↥(factorSL' D d i) ≃* ↥(L i) :=
        (Subgroup.equivMapOfInjective _ θ hθ).trans (MulEquiv.subgroupCongr hLi).symm
      exact ⟨h2, h22, h23, hLi, CFSG.Open.IsQuasisimple.of_mulEquiv (e1.trans e2).symm
        (hct_isQuasisimple_statedSL (D i) h2 h22 h23)⟩
    · right
      have hsolvS : Group.IsSolvable ↥(StatedSL (d i) (D i)) := by
        rcases Nat.lt_or_ge (d i) 2 with hlt | hge
        · haveI := hct_subsingleton_statedSL_of_le_one (K := D i) (by omega : d i ≤ 1)
          infer_instance
        · have hd2 : d i = 2 := by
            by_contra hne
            exact hperf ⟨hge, Or.inl hne, Or.inl hne⟩
          have hcard : Nat.card (D i) = 2 ∨ Nat.card (D i) = 3 := by
            by_contra hne
            push Not at hne
            exact hperf ⟨hge, Or.inr hne.1, Or.inr hne.2⟩
          rw [hd2]
          have hcs := card_statedSL_two (D i)
          rcases hcard with hc | hc
          · rw [hc] at hcs
            exact hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 1) (b := 1)
              Nat.prime_two Nat.prime_three (by norm_num) (by rw [hcs]; norm_num)
          · rw [hc] at hcs
            exact hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 1)
              Nat.prime_two Nat.prime_three (by norm_num) (by rw [hcs]; norm_num)
      have eF : ↥(StatedSL (d i) (D i)) ≃* ↥(factorSL' D d i) :=
        Subgroup.equivMapOfInjective (StatedSL (d i) (D i))
          (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)
          (mulSingle_injective' i)
      have hF : Group.IsSolvable ↥(factorSL' D d i) :=
        Group.isSolvable_of_isSolvable_injective (f := eF.symm.toMonoidHom) eF.symm.injective
      have hTle : T i ≤ factorSL' D d i := by rw [hT i]; exact inf_le_left
      have hLle : L i ≤ (factorSL' D d i).map θ := by
        rw [hL i]
        exact Subgroup.map_mono hTle
      haveI hFmap : Group.IsSolvable ↥((factorSL' D d i).map θ) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.equivMapOfInjective (factorSL' D d i) θ hθ).symm.toMonoidHom)
          (Subgroup.equivMapOfInjective (factorSL' D d i) θ hθ).symm.injective
      exact isSolvable_of_le' hLle
  obtain ⟨i, hMi, hqi⟩ := largeEvenPComponent_eq_of_commuting_product (p := p) L hEX hEn'
    hsolv hE_eq hcomm (fun j => (hLq j).elim (fun h => Or.inl h.2.2.2.2) (fun h => Or.inr h))
    ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent p X M).mpr hM)
  rcases hLq i with ⟨h2, h22, h23, hLi, -⟩ | hsolv'
  · exact ⟨i, h2, h22, h23, by rw [hMi, hLi]⟩
  · exfalso
    exact l154_not_isSolvable_of_isQuasisimple hqi hsolv'


@[expose] noncomputable def l154TransvecGL {m : ℕ} {D : Type} [Field D] (a0 a1 : Fin m) (ha : a0 ≠ a1) (c : D) :
    GL (Fin m) D :=
  ⟨Matrix.transvection a0 a1 c, Matrix.transvection a0 a1 (-c),
    by rw [Matrix.transvection_mul_transvection_same _ _ ha, add_neg_cancel, Matrix.transvection_zero],
    by rw [Matrix.transvection_mul_transvection_same _ _ ha, neg_add_cancel, Matrix.transvection_zero]⟩

theorem l154TransvecGL_mem {m : ℕ} {D : Type} [Field D] (a0 a1 : Fin m) (ha : a0 ≠ a1) (c : D) :
    l154TransvecGL a0 a1 ha c ∈ StatedSL m D := by
  rw [statedSL_eq_ker_det]
  show Matrix.GeneralLinearGroup.det (l154TransvecGL a0 a1 ha c) = 1
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, l154TransvecGL, Matrix.det_transvection_of_ne _ _ ha]

theorem exists_linComp {F : Type} [Field F] [Finite F] (h2 : (2 : F) = 0) {d : ℕ}
    (A : GL (Fin d) F) (hA : (orderOf A : F) ≠ 0) {p : ℕ} {M : Subgroup (GL (Fin d) F)}
    (hM : GLAPComponent p (Subgroup.centralizer ({A} : Set (GL (Fin d) F)) ⊓ StatedSL d F) M) :
    ∃ (d₁ : ℕ) (D₁ : Type) (_ : Field D₁) (_ : Finite D₁) (ι : GL (Fin d₁) D₁ →* GL (Fin d) F),
      (2 : D₁) = 0 ∧ 2 ≤ d₁ ∧ (d₁ ≠ 2 ∨ Nat.card D₁ ≠ 2) ∧ (d₁ ≠ 2 ∨ Nat.card D₁ ≠ 3) ∧
      Function.Injective ι ∧ M = (StatedSL d₁ D₁).map ι ∧
      ∃ E : Matrix (Fin d) (Fin d) F, E ≠ 0 ∧ ∀ c : F, ∃ t ∈ StatedSL d₁ D₁,
        ((ι t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 + c • E := by
  classical
  have hA' : (Nat.card (Subgroup.zpowers A) : F) ≠ 0 := by
    rw [Nat.card_zpowers]
    exact hA
  obtain ⟨r, D, dd, hFld, hFin, hAlg, Φ, θ, _hNZ, hΦinj, _hΦrange, hθinj, hθrange, hθapply⟩ :=
    exists_piMat_commutant (Subgroup.zpowers A) hA'
  letI : ∀ i, Field (D i) := hFld
  haveI : ∀ i, Finite (D i) := hFin
  letI : ∀ i, Algebra F (D i) := hAlg
  have hcent : Subgroup.centralizer ((Subgroup.zpowers A : Subgroup (GL (Fin d) F)) :
      Set (GL (Fin d) F)) = Subgroup.centralizer ({A} : Set (GL (Fin d) F)) := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hg _ (Subgroup.mem_zpowers _)
    · intro hg h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hc : Commute A g := hg A (Set.mem_singleton A)
      exact (hc.zpow_left k).eq
  have hCeq : Subgroup.centralizer ({A} : Set (GL (Fin d) F)) ⊓ StatedSL d F =
      ((StatedSL d F).comap θ).map θ := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hxr : x ∈ θ.range := by
        rw [hθrange, hcent]
        exact hx1
      obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hxr
      exact Subgroup.mem_map.mpr ⟨w, hx2, rfl⟩
    · intro hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      refine ⟨?_, hw⟩
      rw [← hcent, ← hθrange]
      exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
  rw [hCeq] at hM
  obtain ⟨i, h2d, h22, h23, hMi⟩ := linear_pcomp_core' θ hθinj p M hM
  have hd0 : 0 < dd i := by omega
  have hd1 : 1 < dd i := by omega
  set a0 : Fin (dd i) := ⟨0, hd0⟩ with ha0
  set a1 : Fin (dd i) := ⟨1, hd1⟩ with ha1
  have ha : a0 ≠ a1 := by simp [ha0, ha1, Fin.ext_iff]
  refine ⟨dd i, D i, hFld i, hFin i, θ.comp (MonoidHom.mulSingle (fun j => GL (Fin (dd j)) (D j)) i),
    ?_, h2d, h22, h23, hθinj.comp (mulSingle_injective' i), ?_, ?_⟩
  · have := map_ofNat (algebraMap F (D i)) 2
    rw [h2, map_zero] at this
    exact this.symm
  · rw [hMi, factorSL', Subgroup.map_map]
  · let e01 : Matrix (Fin (dd i)) (Fin (dd i)) (D i) := Matrix.single a0 a1 1
    refine ⟨Φ (Pi.single i e01), ?_, fun c => ?_⟩
    · intro h0
      have h1 : (Pi.single i e01 : ∀ j, Matrix (Fin (dd j)) (Fin (dd j)) (D j)) = 0 :=
        hΦinj (by rw [h0, map_zero])
      have h3 := congrFun h1 i
      have h4 := congrFun (congrFun h3 a0) a1
      simp [e01] at h4
    · refine ⟨l154TransvecGL a0 a1 ha (algebraMap F (D i) c), l154TransvecGL_mem a0 a1 ha _, ?_⟩
      show ((θ (MonoidHom.mulSingle (fun j => GL (Fin (dd j)) (D j)) i
        (l154TransvecGL a0 a1 ha (algebraMap F (D i) c))) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = _
      rw [hθapply]
      have hce : c • e01 = Matrix.single a0 a1 (algebraMap F (D i) c) := by
        ext x y
        rw [Matrix.smul_apply]
        simp [e01, Matrix.single_apply, Algebra.smul_def]
      have hfun : (fun j => (((MonoidHom.mulSingle (fun j => GL (Fin (dd j)) (D j)) i
          (l154TransvecGL a0 a1 ha (algebraMap F (D i) c))) j : GL (Fin (dd j)) (D j)) :
            Matrix (Fin (dd j)) (Fin (dd j)) (D j))) =
          1 + c • (Pi.single i e01 : ∀ j, Matrix (Fin (dd j)) (Fin (dd j)) (D j)) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same, Pi.add_apply, Pi.one_apply,
            Pi.smul_apply, Pi.single_eq_same]
          show Matrix.transvection a0 a1 (algebraMap F (D j) c) = 1 + c • e01
          rw [hce]
          rfl
        · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj, Pi.single_eq_of_ne hj]
      rw [hfun, map_add, map_one, map_smul]

end CFSG.LocalAnalysis.GLTheoremA.K155X

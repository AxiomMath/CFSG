module

public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
public import CFSG.LieType.SemisimpleCentralizers.PComponentProduct
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

open CFSG.Open CFSG.Open.StatedAPI CFSG.LieType.SemisimpleCentralizers
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.StandardType.LinNonsplit Matrix
open scoped commutatorElement

namespace PComp

section Pi

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type} [∀ i, Group (M i)]

theorem mem_iSup_of_mulSingle_mem (S : ι → Subgroup (∀ j, M j)) (z : ∀ j, M j)
    (h : ∀ i, MonoidHom.mulSingle M i (z i) ∈ S i) : z ∈ ⨆ i, S i := by
  rw [← Finset.noncommProd_mulSingle z]
  exact Subgroup.noncommProd_mem _ _ (fun i _ => Subgroup.mem_iSup_of_mem i (h i))

end Pi

theorem commute_mulSingle_of_ne {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, Group (M i)]
    {i j : ι} (hij : i ≠ j) (u : M i) (v : M j) :
    Commute (MonoidHom.mulSingle M i u) (MonoidHom.mulSingle M j v) := by
  show MonoidHom.mulSingle M i u * MonoidHom.mulSingle M j v =
    MonoidHom.mulSingle M j v * MonoidHom.mulSingle M i u
  ext k
  by_cases hki : k = i
  · subst hki
    simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hki]
    · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hki, Pi.mulSingle_eq_of_ne hkj]

instance statedSL_normal' (d : ℕ) (K : Type) [Field K] : (StatedSL d K).Normal := by
  rw [statedSL_eq_ker_det]
  infer_instance

theorem mulSingle_conj' {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ} (i : Fin r)
    (g : ∀ j, GL (Fin (d j)) (D j)) (w : GL (Fin (d i)) (D i)) :
    g * MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i w * g⁻¹ =
      MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i (g i * w * (g i)⁻¹) := by
  ext j
  by_cases h : j = i
  · subst h
    simp [MonoidHom.mulSingle_apply]
  · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]

def factorSL {r : ℕ} (D : Fin r → Type) [∀ i, Field (D i)] (d : Fin r → ℕ) (i : Fin r) :
    Subgroup (∀ j, GL (Fin (d j)) (D j)) :=
  (StatedSL (d i) (D i)).map (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)

instance factorSL_normal' {r : ℕ} (D : Fin r → Type) [∀ i, Field (D i)] (d : Fin r → ℕ)
    (i : Fin r) : (factorSL D d i).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
  rw [mulSingle_conj']
  exact Subgroup.mem_map.mpr ⟨_, (statedSL_normal' (d i) (D i)).conj_mem w hw (g i), rfl⟩

instance finite_GL' (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] [Finite K] :
    Finite (GL ι K) :=
  Finite.of_injective (fun g : GL ι K => (g : Matrix ι ι K)) (fun _ _ h => Units.ext h)

theorem mulSingle_injective' {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ}
    (i : Fin r) :
    Function.Injective (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i) := by
  intro a b hab
  have := congrFun hab i
  simpa [MonoidHom.mulSingle_apply] using this

theorem isSolvable_of_le' {G : Type} [Group G] {A B : Subgroup G} (hAB : A ≤ B)
    [Group.IsSolvable ↥B] : Group.IsSolvable ↥A :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAB)
    (Subgroup.inclusion_injective hAB)

theorem linear_pcomp_core {F : Type} [Field F] [Finite F] {n r : ℕ}
    {D : Fin r → Type} [∀ i, Field (D i)] [∀ i, Finite (D i)] {d : Fin r → ℕ}
    (θ : (∀ j, GL (Fin (d j)) (D j)) →* GL (Fin n) F) (hθ : Function.Injective θ)
    (p : ℕ) (M : Subgroup (GL (Fin n) F))
    (hM : GLAPComponent p (((StatedSL n F).comap θ).map θ) M) :
    IsComponentOf M (((StatedSL n F).comap θ).map θ) := by
  classical
  obtain ⟨KP, hKP⟩ : ∃ KP : Subgroup (∀ j, GL (Fin (d j)) (D j)),
      KP = (StatedSL n F).comap θ := ⟨_, rfl⟩
  have memKP : ∀ x, x ∈ KP ↔ θ x ∈ StatedSL n F := fun x => by rw [hKP]; rfl
  haveI hKPn : KP.Normal := by rw [hKP]; infer_instance
  obtain ⟨T, hT⟩ : ∃ T : Fin r → Subgroup (∀ j, GL (Fin (d j)) (D j)),
      ∀ i, T i = factorSL D d i ⊓ KP := ⟨fun i => factorSL D d i ⊓ KP, fun i => rfl⟩
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
  rw [← hKP, ← hX] at hM ⊢
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
  have hLq : ∀ i, CFSG.Open.IsQuasisimple ↥(L i) ∨ Group.IsSolvable ↥(L i) := by
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
      have hle : factorSL D d i ≤ KP := by
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
      have hTi : T i = factorSL D d i := by rw [hT i, inf_eq_left.mpr hle]
      have hLi : L i = (factorSL D d i).map θ := by rw [hL i, hTi]
      have e1 : ↥(StatedSL (d i) (D i)) ≃* ↥(factorSL D d i) :=
        Subgroup.equivMapOfInjective (StatedSL (d i) (D i))
          (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)
          (mulSingle_injective' i)
      have e2 : ↥(factorSL D d i) ≃* ↥(L i) :=
        (Subgroup.equivMapOfInjective _ θ hθ).trans (MulEquiv.subgroupCongr hLi).symm
      exact CFSG.Open.IsQuasisimple.of_mulEquiv (e1.trans e2).symm
        (hct_isQuasisimple_statedSL (D i) h2 h22 h23)
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
      have eF : ↥(StatedSL (d i) (D i)) ≃* ↥(factorSL D d i) :=
        Subgroup.equivMapOfInjective (StatedSL (d i) (D i))
          (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)
          (mulSingle_injective' i)
      have hF : Group.IsSolvable ↥(factorSL D d i) :=
        Group.isSolvable_of_isSolvable_injective (f := eF.symm.toMonoidHom) eF.symm.injective
      have hTle : T i ≤ factorSL D d i := by rw [hT i]; exact inf_le_left
      have hLle : L i ≤ (factorSL D d i).map θ := by
        rw [hL i]
        exact Subgroup.map_mono hTle
      haveI hFmap : Group.IsSolvable ↥((factorSL D d i).map θ) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.equivMapOfInjective (factorSL D d i) θ hθ).symm.toMonoidHom)
          (Subgroup.equivMapOfInjective (factorSL D d i) θ hθ).symm.injective
      exact isSolvable_of_le' hLle
  have hLX : ∀ i, L i ≤ X := by
    intro i y hy
    rw [hL i] at hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hT i] at ht
    obtain ⟨-, htK⟩ := Subgroup.mem_inf.mp ht
    exact (memX _).mpr ⟨t, htK, rfl⟩
  obtain ⟨i, hMi, hqi⟩ := largeEvenPComponent_eq_of_commuting_product (p := p) L hEX hEn'
    hsolv hE_eq hcomm (fun j => (hLq j).elim (fun h => Or.inl h) (fun h => Or.inr h))
    ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent p X M).mpr hM)
  rw [hMi]
  have hsub : CFSG.Open.IsSubnormal (L i) X := by
    refine CFSG.Open.IsSubnormal.step (hLX i) ?_ (CFSG.Open.IsSubnormal.refl X)
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, -, hkg⟩ := (memX _).mp g.2
    rw [hL i] at hn ⊢
    obtain ⟨t, ht, htn⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨k * t * k⁻¹, (hTn i).conj_mem t ht k, ?_⟩
    simp [map_mul, map_inv, hkg, htn]
  unfold CFSG.Open.IsComponentOf
  exact ⟨hLX i, hsub, hqi⟩

end PComp

theorem LinPCompIsComp_holds : LinPCompIsComp := by
  intro F _ _ n p _ s hs M hM
  have hA : (Nat.card (Subgroup.zpowers s) : F) ≠ 0 := by
    rw [Nat.card_zpowers]
    exact hs
  obtain ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, _hNZ, _hΦinj, _hΦrange, hθinj, hθrange,
    _hθapply⟩ := exists_piMat_commutant (Subgroup.zpowers s) hA
  letI : ∀ i, Field (D i) := hFld
  haveI : ∀ i, Finite (D i) := hFin
  have hcent : Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (GL (Fin n) F)) :
      Set (GL (Fin n) F)) = Subgroup.centralizer ({s} : Set (GL (Fin n) F)) := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hg _ (Subgroup.mem_zpowers _)
    · intro hg h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hc : Commute s g := hg s (Set.mem_singleton s)
      exact (hc.zpow_left k).eq
  have hCeq : Subgroup.centralizer ({s} : Set (GL (Fin n) F)) ⊓ StatedSL n F =
      ((StatedSL n F).comap θ).map θ := by
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
  rw [hCeq] at hM ⊢
  exact PComp.linear_pcomp_core θ hθinj p M hM

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

end

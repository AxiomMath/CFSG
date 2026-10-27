module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvT1

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

section Generic

theorem t2_mulAut_map_mem_center {A : Type*} [Group A] (ψ : MulAut A) {z : A}
    (hz : z ∈ Subgroup.center A) : ψ z ∈ Subgroup.center A := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : ψ (ψ.symm g) = g := ψ.apply_symm_apply g
  calc g * ψ z = ψ (ψ.symm g) * ψ z := by rw [h1]
    _ = ψ (ψ.symm g * z) := (map_mul ψ _ _).symm
    _ = ψ (z * ψ.symm g) := by rw [Subgroup.mem_center_iff.1 hz (ψ.symm g)]
    _ = ψ z * g := by rw [map_mul, h1]

theorem t2_conj_central_left {A : Type*} [Group A] {z : A} (hz : z ∈ Subgroup.center A) (g : A) :
    z * g * z⁻¹ = g := by
  rw [← Subgroup.mem_center_iff.1 hz g]
  group

theorem t2_conj_central_right {A : Type*} [Group A] {z : A} (hz : z ∈ Subgroup.center A) (g : A) :
    g * z * g⁻¹ = z := by
  rw [Subgroup.mem_center_iff.1 hz g]
  group

theorem t2_commutatorElement_mul_central {A : Type*} [Group A] {c d : A}
    (hc : c ∈ Subgroup.center A) (hd : d ∈ Subgroup.center A) (x y : A) :
    ⁅c * x, d * y⁆ = ⁅x, y⁆ := by
  have hdx : x * d = d * x := Subgroup.mem_center_iff.1 hd x
  rw [commutatorElement_def, commutatorElement_def]
  calc c * x * (d * y) * (c * x)⁻¹ * (d * y)⁻¹
      = c * (x * d * y * x⁻¹) * c⁻¹ * (d * y)⁻¹ := by group
    _ = (x * d * y * x⁻¹) * (d * y)⁻¹ := by rw [t2_conj_central_left hc]
    _ = d * (x * y * x⁻¹ * y⁻¹) * d⁻¹ := by rw [hdx]; group
    _ = x * y * x⁻¹ * y⁻¹ := t2_conj_central_left hd _

theorem t2_perfect_aut_apply_eq {A : Type*} [Group A] (hperf : commutator A = ⊤) (θ : MulAut A)
    (hθ : ∀ a : A, θ a * a⁻¹ ∈ Subgroup.center A) (a : A) : θ a = a := by
  let F : Subgroup A :=
    { carrier := {x | θ x = x}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, hx, hy]
      one_mem' := by
        simp only [Set.mem_setOf_eq, map_one]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_inv, hx] }
  have key : ∀ x y : A, ⁅x, y⁆ ∈ F := by
    intro x y
    show θ ⁅x, y⁆ = ⁅x, y⁆
    have hx : θ x = θ x * x⁻¹ * x := (inv_mul_cancel_right _ _).symm
    have hy : θ y = θ y * y⁻¹ * y := (inv_mul_cancel_right _ _).symm
    rw [map_commutatorElement, hx, hy, t2_commutatorElement_mul_central (hθ x) (hθ y)]
  have htop : (⊤ : Subgroup A) ≤ F := by
    rw [← hperf]
    exact Subgroup.commutator_le.2 fun x _ y _ => key x y
  exact htop (Subgroup.mem_top a)

theorem t2_perfect_aut_eq_of_mk_eq {A : Type*} [Group A] (hperf : commutator A = ⊤)
    (φ φ' : MulAut A)
    (h : ∀ a : A, (QuotientGroup.mk (φ a) : A ⧸ Subgroup.center A) = QuotientGroup.mk (φ' a)) :
    φ = φ' := by
  have hθ : ∀ a : A, (φ.trans φ'.symm) a * a⁻¹ ∈ Subgroup.center A := by
    intro a
    obtain ⟨z, hzdef⟩ : ∃ z : A, z = (φ a)⁻¹ * φ' a := ⟨_, rfl⟩
    have hz : z ∈ Subgroup.center A := by
      rw [hzdef]
      exact QuotientGroup.eq.1 (h a)
    have hφa : φ a = φ' a * z⁻¹ := by
      rw [hzdef]
      group
    have hw : φ'.symm z⁻¹ ∈ Subgroup.center A :=
      t2_mulAut_map_mem_center φ'.symm ((Subgroup.center A).inv_mem hz)
    have hcalc : (φ.trans φ'.symm) a = a * φ'.symm z⁻¹ := by
      rw [MulEquiv.trans_apply, hφa, map_mul, MulEquiv.symm_apply_apply]
    rw [hcalc, t2_conj_central_right hw a]
    exact hw
  have hθa := t2_perfect_aut_apply_eq hperf (φ.trans φ'.symm) hθ
  ext a
  have h2 := congrArg φ' (hθa a)
  rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h2
  exact h2

theorem t2_mem_inducedAutGroup_iff {Y : Type*} [Group Y] (W A : Subgroup Y) (φ : MulAut ↥A) :
    φ ∈ inducedAutGroup W A ↔
      ∃ n ∈ W, ∃ hn : n ∈ Subgroup.normalizer (A : Set Y),
        A.normalizerMonoidHom ⟨n, hn⟩ = φ := by
  unfold inducedAutGroup
  constructor
  · intro hφ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hφ
    exact ⟨x.1, Subgroup.mem_subgroupOf.1 hx, x.2, rfl⟩
  · rintro ⟨n, hnW, hn, rfl⟩
    exact Subgroup.mem_map.2 ⟨⟨n, hn⟩, Subgroup.mem_subgroupOf.2 hnW, rfl⟩

theorem t2_inducesOn_iff_congr {A K : Type*} [Group A] [Group K]
    (eCQ : (A ⧸ Subgroup.center A) ≃* K) (e : A ≃* K)
    (hmk : ∀ x : A, eCQ (QuotientGroup.mk x) = e x) (φ : MulAut A) (σ : MulAut K) :
    InducesOn eCQ φ σ ↔ MulAut.congr e φ = σ := by
  constructor
  · intro H
    apply MulEquiv.ext
    intro k
    have hk := H (e.symm k)
    rw [hmk, hmk, MulEquiv.apply_symm_apply] at hk
    exact hk
  · intro H a
    rw [hmk, hmk, ← H]
    show e (φ a) = e (φ (e.symm (e a)))
    rw [MulEquiv.symm_apply_apply]

end Generic

section Setting

variable {G : Type} [Group G] [Finite G]
variable {m p : ℕ} {M D L : Subgroup G}

theorem t2_tl_perfect (h : IvSetting m p M D L) : commutator ↥(tl M L) = ⊤ :=
  (isComponentOf_tl (prime_of_standing h.standing) (ne_two_of_standing h.standing) h.hyp h.hL h.hn
    h.hnc h.hQ).2.2.1

theorem t2_tl_le_normalizer {W : Subgroup G} (hWM : W ≤ M)
    (hWN : W ≤ Subgroup.normalizer (L : Set G)) :
    tl M W ≤ Subgroup.normalizer ((tl M L : Subgroup (Mt M)) : Set (Mt M)) := by
  have h1 : W.subgroupOf M ≤ Subgroup.normalizer ((L.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    intro w hw
    have hwW : (w : G) ∈ W := Subgroup.mem_subgroupOf.1 hw
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.1 (hWN hwW) (x : G)
  calc tl M W = (W.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := rfl
    _ ≤ (Subgroup.normalizer ((L.subgroupOf M : Subgroup ↥M) : Set ↥M)).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := Subgroup.map_mono h1
    _ ≤ Subgroup.normalizer ((tl M L : Subgroup (Mt M)) : Set (Mt M)) :=
          (L.subgroupOf M).le_normalizer_map _

theorem t2_projQ_mem_normalizer (h : IvSetting m p M D L) {n : Mt M}
    (hn : n ∈ Subgroup.normalizer ((tl M L : Subgroup (Mt M)) : Set (Mt M))) :
    projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M) n ∈
      Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have hle := (tl M L).le_normalizer_map
    (projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M))
  rw [map_projQ_tl h L] at hle
  exact hle (Subgroup.mem_map_of_mem _ hn)

theorem t2_psiL_ind_apply (h : IvSetting m p M D L) {n : Mt M}
    (hn : n ∈ Subgroup.normalizer ((tl M L : Subgroup (Mt M)) : Set (Mt M)))
    (a : ↥(tl M L)) :
    psiL h ((tl M L).normalizerMonoidHom ⟨n, hn⟩ a) =
      (barX p M L).normalizerMonoidHom
        ⟨projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M) n,
          t2_projQ_mem_normalizer h hn⟩ (psiL h a) := by
  have hle := pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M
  apply Subtype.ext
  show projQ p M hle (n * (a : Mt M) * n⁻¹) =
    projQ p M hle n * projQ p M hle (a : Mt M) * (projQ p M hle n)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem t2_inducesOn_psiHat_iff (h : IvSetting m p M D L) {K : Type*} [Group K]
    (e : (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) ≃* K) (σ : MulAut K)
    (φ : MulAut ↥(tl M L)) (φB : MulAut ↥(barX p M L))
    (hcomp : ∀ a : ↥(tl M L), psiL h (φ a) = φB (psiL h a)) :
    InducesOn ((psiHat h).trans e) φ σ ↔ InducesOn e φB σ := by
  have hmk : ∀ x : ↥(tl M L), ((psiHat h).trans e) (QuotientGroup.mk x) =
      e (QuotientGroup.mk (psiL h x)) := fun x => rfl
  unfold InducesOn
  constructor
  · intro H b
    obtain ⟨a, rfl⟩ := psiL_surjective h b
    have hH := H a
    rw [hmk, hmk, hcomp] at hH
    exact hH
  · intro H a
    rw [hmk, hmk, hcomp]
    exact H (psiL h a)

theorem t2_ind_equiv_bar (h : IvSetting m p M D L) (P : Subgroup (Mt M))
    (P' : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M))
    (hPP : P.map (projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M)) =
      P')
    (hP : P ≤ Subgroup.normalizer ((tl M L : Subgroup (Mt M)) : Set (Mt M))) :
    Nonempty (↥(inducedAutGroup P (tl M L)) ≃* ↥(inducedAutGroup P' (barX p M L))) := by
  have hperf := t2_tl_perfect h
  have hle := pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M
  let N := Subgroup.normalizer ((tl M L : Subgroup (Mt M)) : Set (Mt M))
  let ρ : N →* ↥(Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M))) :=
    ((projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M)).comp
      N.subtype).codRestrict _ (fun n => t2_projQ_mem_normalizer h n.2)
  let Φ : ↥(P.subgroupOf N) →* MulAut ↥(tl M L) :=
    (tl M L).normalizerMonoidHom.comp (P.subgroupOf N).subtype
  let Ψ : ↥(P.subgroupOf N) →* MulAut ↥(barX p M L) :=
    (barX p M L).normalizerMonoidHom.comp (ρ.comp (P.subgroupOf N).subtype)
  have hI1 : inducedAutGroup P (tl M L) = Φ.range := by
    ext φ
    rw [t2_mem_inducedAutGroup_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨n, hnP, hn, rfl⟩
      exact ⟨⟨⟨n, hn⟩, Subgroup.mem_subgroupOf.2 hnP⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2, x.1.2, rfl⟩
  have hI2 : inducedAutGroup P' (barX p M L) = Ψ.range := by
    ext φ
    rw [t2_mem_inducedAutGroup_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨ν, hνP', hν, rfl⟩
      rw [← hPP] at hνP'
      obtain ⟨n, hnP, rfl⟩ := Subgroup.mem_map.1 hνP'
      exact ⟨⟨⟨n, hP hnP⟩, Subgroup.mem_subgroupOf.2 hnP⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M) x.1.1,
        ?_, t2_projQ_mem_normalizer h x.1.2, rfl⟩
      rw [← hPP]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.1 x.2)
  have hker : Φ.ker = Ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      apply MulEquiv.ext
      intro b
      obtain ⟨a, rfl⟩ := psiL_surjective h b
      have ha : (tl M L).normalizerMonoidHom ⟨x.1.1, x.1.2⟩ a = a := by
        have h1 := congrArg (fun g : MulAut ↥(tl M L) => g a) hx
        exact h1
      have hna : x.1.1 * (a : Mt M) * x.1.1⁻¹ = (a : Mt M) := by
        have h2 := congrArg Subtype.val ha
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
        exact h2
      apply Subtype.ext
      show projQ p M hle x.1.1 * projQ p M hle (a : Mt M) * (projQ p M hle x.1.1)⁻¹ =
        projQ p M hle (a : Mt M)
      have hfa := congrArg (projQ p M hle) hna
      rw [map_mul, map_mul, map_inv] at hfa
      exact hfa
    · intro hx
      have hΨ : ∀ a : ↥(tl M L),
          psiL h ((tl M L).normalizerMonoidHom ⟨x.1.1, x.1.2⟩ a) = psiL h a := by
        intro a
        rw [t2_psiL_ind_apply h x.1.2 a]
        exact congrArg (fun g : MulAut ↥(barX p M L) => g (psiL h a)) hx
      have hθ : ∀ a : ↥(tl M L), (tl M L).normalizerMonoidHom ⟨x.1.1, x.1.2⟩ a * a⁻¹ ∈
          Subgroup.center ↥(tl M L) := by
        intro a
        apply ker_psiL_le_center h
        rw [MonoidHom.mem_ker, map_mul, map_inv, hΨ a, mul_inv_cancel]
      apply MulEquiv.ext
      intro a
      rw [MulAut.one_apply]
      exact t2_perfect_aut_apply_eq hperf ((tl M L).normalizerMonoidHom ⟨x.1.1, x.1.2⟩) hθ a
  refine ⟨?_⟩
  rw [hI1, hI2]
  exact (QuotientGroup.quotientKerEquivRange Φ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange Ψ))

theorem t2_indCA_mem {W : Subgroup G} {n : Mt M} (hnW : n ∈ tl M W)
    (hn : n ∈ Subgroup.normalizer ((tl M L : Subgroup (Mt M)) : Set (Mt M))) :
    (tl M L).normalizerMonoidHom ⟨n, hn⟩ ∈ inducedAutGroup (tl M W) (tl M L) :=
  (t2_mem_inducedAutGroup_iff _ _ _).2 ⟨n, hnW, hn, rfl⟩

theorem t2_indCB_mem (h : IvSetting m p M D L) {W : Subgroup G} {n : Mt M} (hnW : n ∈ tl M W)
    (hn : n ∈ Subgroup.normalizer ((tl M L : Subgroup (Mt M)) : Set (Mt M))) :
    (barX p M L).normalizerMonoidHom
        ⟨projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M) n,
          t2_projQ_mem_normalizer h hn⟩ ∈ inducedAutGroup (barX p M W) (barX p M L) := by
  refine (t2_mem_inducedAutGroup_iff _ _ _).2
    ⟨projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M) n, ?_,
      t2_projQ_mem_normalizer h hn, rfl⟩
  rw [← map_projQ_tl h W]
  exact Subgroup.mem_map_of_mem _ hnW

theorem t2_ind_bar_rep (h : IvSetting m p M D L) {W : Subgroup G} (hWM : W ≤ M)
    (hWN : W ≤ Subgroup.normalizer (L : Set G)) {φB : MulAut ↥(barX p M L)}
    (hφB : φB ∈ inducedAutGroup (barX p M W) (barX p M L)) :
    ∃ n ∈ tl M W, ∃ hn : n ∈ Subgroup.normalizer ((tl M L : Subgroup (Mt M)) : Set (Mt M)),
      (barX p M L).normalizerMonoidHom
        ⟨projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M) n,
          t2_projQ_mem_normalizer h hn⟩ = φB := by
  obtain ⟨ν, hνW, hν, rfl⟩ := (t2_mem_inducedAutGroup_iff _ _ _).1 hφB
  rw [← map_projQ_tl h W] at hνW
  obtain ⟨n, hnW, rfl⟩ := Subgroup.mem_map.1 hνW
  exact ⟨n, hnW, t2_tl_le_normalizer hWM hWN hnW, rfl⟩

theorem t2_congr_ind_eq (h : IvSetting m p M D L) (hψ : Function.Bijective (psiL h))
    {n : Mt M} (hn : n ∈ Subgroup.normalizer ((tl M L : Subgroup (Mt M)) : Set (Mt M))) :
    (MulAut.congr (MulEquiv.ofBijective (psiL h) hψ)).toMonoidHom
        ((tl M L).normalizerMonoidHom ⟨n, hn⟩) =
      (barX p M L).normalizerMonoidHom
        ⟨projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M) n,
          t2_projQ_mem_normalizer h hn⟩ := by
  apply MulEquiv.ext
  intro b
  have hb : psiL h ((MulEquiv.ofBijective (psiL h) hψ).symm b) = b :=
    (MulEquiv.ofBijective (psiL h) hψ).apply_symm_apply b
  show psiL h ((tl M L).normalizerMonoidHom ⟨n, hn⟩
    ((MulEquiv.ofBijective (psiL h) hψ).symm b)) = _
  rw [t2_psiL_ind_apply h hn, hb]

theorem t2_map_congr_ind (h : IvSetting m p M D L) (hψ : Function.Bijective (psiL h))
    {W : Subgroup G} (hWM : W ≤ M) (hWN : W ≤ Subgroup.normalizer (L : Set G)) :
    (inducedAutGroup (tl M W) (tl M L)).map
        (MulAut.congr (MulEquiv.ofBijective (psiL h) hψ)).toMonoidHom =
      inducedAutGroup (barX p M W) (barX p M L) := by
  ext φB
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨n, hnW, hn, rfl⟩ := (t2_mem_inducedAutGroup_iff _ _ _).1 hφ
    rw [t2_congr_ind_eq h hψ hn]
    exact t2_indCB_mem h hnW hn
  · intro hφB
    obtain ⟨n, hnW, hn, rfl⟩ := t2_ind_bar_rep h hWM hWN hφB
    exact ⟨_, t2_indCA_mem hnW hn, t2_congr_ind_eq h hψ hn⟩

theorem actsLikeCQ_tl_iff_bar (h : IvSetting m p M D L) {K : Type*} [Group K]
    (e : (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) ≃* K) (S : Subgroup (MulAut K))
    {W : Subgroup G} (hWM : W ≤ M) (hWN : W ≤ Subgroup.normalizer (L : Set G)) :
    ActsLikeCQ (tl M W) (tl M L) ((psiHat h).trans e) S ↔
      ActsLikeCQ (barX p M W) (barX p M L) e S := by
  have hT : ∀ (n : Mt M) (hn : n ∈ Subgroup.normalizer ((tl M L : Subgroup (Mt M)) :
      Set (Mt M))) (σ : MulAut K),
      InducesOn ((psiHat h).trans e) ((tl M L).normalizerMonoidHom ⟨n, hn⟩) σ ↔
        InducesOn e ((barX p M L).normalizerMonoidHom
          ⟨projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M) n,
            t2_projQ_mem_normalizer h hn⟩) σ :=
    fun n hn σ => t2_inducesOn_psiHat_iff h e σ _ _ (t2_psiL_ind_apply h hn)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun φB hφB => ?_, fun σ hσ => ?_⟩
    · obtain ⟨n, hnW, hn, rfl⟩ := t2_ind_bar_rep h hWM hWN hφB
      obtain ⟨σ', hσ', hI⟩ := h1 _ (t2_indCA_mem hnW hn)
      exact ⟨σ', hσ', (hT n hn σ').1 hI⟩
    · obtain ⟨φ, hφ, hI⟩ := h2 σ hσ
      obtain ⟨n, hnW, hn, rfl⟩ := (t2_mem_inducedAutGroup_iff _ _ _).1 hφ
      exact ⟨_, t2_indCB_mem h hnW hn, (hT n hn σ).1 hI⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun φ hφ => ?_, fun σ hσ => ?_⟩
    · obtain ⟨n, hnW, hn, rfl⟩ := (t2_mem_inducedAutGroup_iff _ _ _).1 hφ
      obtain ⟨σ', hσ', hI⟩ := h1 _ (t2_indCB_mem h hnW hn)
      exact ⟨σ', hσ', (hT n hn σ').2 hI⟩
    · obtain ⟨φB, hφB, hI⟩ := h2 σ hσ
      obtain ⟨n, hnW, hn, rfl⟩ := t2_ind_bar_rep h hWM hWN hφB
      exact ⟨_, t2_indCA_mem hnW hn, (hT n hn σ).2 hI⟩

theorem card_inducedAutGroup_tl_eq_bar (h : IvSetting m p M D L) {W : Subgroup G}
    (hWM : W ≤ M) (hWN : W ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (inducedAutGroup (tl M W) (tl M L)) =
      Nat.card (inducedAutGroup (barX p M W) (barX p M L)) := by
  obtain ⟨e⟩ :=
    t2_ind_equiv_bar h (tl M W) (barX p M W) (map_projQ_tl h W) (t2_tl_le_normalizer hWM hWN)
  exact Nat.card_congr e.toEquiv

theorem inducedAutGroupSup_nonempty (h : IvSetting m p M D L) {W : Subgroup G}
    (hWM : W ≤ M) (hWN : W ≤ Subgroup.normalizer (L : Set G)) :
    Nonempty (↥(inducedAutGroup (tl M L ⊔ tl M W) (tl M L)) ≃*
      ↥(inducedAutGroup (barX p M L ⊔ barX p M W) (barX p M L))) := by
  refine t2_ind_equiv_bar h (tl M L ⊔ tl M W) (barX p M L ⊔ barX p M W) ?_
    (sup_le Subgroup.le_normalizer (t2_tl_le_normalizer hWM hWN))
  rw [Subgroup.map_sup, map_projQ_tl h L, map_projQ_tl h W]

theorem actsLike_tl_iff_bar (h : IvSetting m p M D L) (hψ : Function.Bijective (psiL h))
    {K : Type*} [Group K] (e : ↥(barX p M L) ≃* K) (S : Subgroup (MulAut K))
    {W : Subgroup G} (hWM : W ≤ M) (hWN : W ≤ Subgroup.normalizer (L : Set G)) :
    ActsLike (barX p M W) (barX p M L) e S ↔
      ActsLike (tl M W) (tl M L) ((MulEquiv.ofBijective (psiL h) hψ).trans e) S := by
  have hcomp : (MulAut.congr ((MulEquiv.ofBijective (psiL h) hψ).trans e)).toMonoidHom =
      (MulAut.congr e).toMonoidHom.comp
        (MulAut.congr (MulEquiv.ofBijective (psiL h) hψ)).toMonoidHom :=
    MonoidHom.ext fun f => MulEquiv.ext fun k => rfl
  unfold ActsLike
  rw [hcomp, ← Subgroup.map_map, t2_map_congr_ind h hψ hWM hWN]

theorem actsLike_iff_actsLikeCQ {Y : Type*} [Group Y] {K : Type*} [Group K] (W A : Subgroup Y)
    (hZ : Subgroup.center ↥A = ⊥) (e : ↥A ≃* K) (S : Subgroup (MulAut K)) :
    ActsLike W A e S ↔ ActsLikeCQ W A
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans ((QuotientGroup.quotientBot).trans e)) S := by
  have hmk : ∀ x : ↥A, ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      ((QuotientGroup.quotientBot).trans e)) (QuotientGroup.mk x) = e x := fun x => rfl
  constructor
  · intro H
    refine ⟨fun φ hφ => ⟨MulAut.congr e φ, ?_, (t2_inducesOn_iff_congr _ e hmk φ _).2 rfl⟩,
      fun σ hσ => ?_⟩
    · rw [← H]
      exact Subgroup.mem_map_of_mem _ hφ
    · rw [← H] at hσ
      obtain ⟨φ, hφ, hφσ⟩ := Subgroup.mem_map.1 hσ
      exact ⟨φ, hφ, (t2_inducesOn_iff_congr _ e hmk φ σ).2 hφσ⟩
  · rintro ⟨h1, h2⟩
    ext σ
    constructor
    · intro hσ
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.1 hσ
      obtain ⟨σ', hσ', hI⟩ := h1 φ hφ
      have hEq := (t2_inducesOn_iff_congr _ e hmk φ σ').1 hI
      show MulAut.congr e φ ∈ S
      rw [hEq]
      exact hσ'
    · intro hσ
      obtain ⟨φ, hφ, hI⟩ := h2 σ hσ
      exact Subgroup.mem_map.2 ⟨φ, hφ, (t2_inducesOn_iff_congr _ e hmk φ σ).1 hI⟩

theorem card_induced_of_actsLikeCQ {Y : Type*} [Group Y] {K : Type*} [Group K] (W A : Subgroup Y)
    (hperf : commutator ↥A = ⊤) (e : (↥A ⧸ Subgroup.center ↥A) ≃* K) (S : Subgroup (MulAut K))
    (h : ActsLikeCQ W A e S) : Nat.card (inducedAutGroup W A) = Nat.card S := by
  obtain ⟨h1, h2⟩ := h
  choose! σf hσS hσI using h1
  refine Nat.card_eq_of_bijective
    (fun φ : ↥(inducedAutGroup W A) => (⟨σf φ.1, hσS φ.1 φ.2⟩ : ↥S)) ⟨?_, ?_⟩
  · intro φ φ' hgg
    have hσ : σf φ.1 = σf φ'.1 := congrArg Subtype.val hgg
    apply Subtype.ext
    apply t2_perfect_aut_eq_of_mk_eq hperf
    intro a
    apply e.injective
    rw [hσI φ.1 φ.2 a, hσI φ'.1 φ'.2 a, hσ]
  · rintro ⟨σ, hσ⟩
    obtain ⟨φ, hφ, hI⟩ := h2 σ hσ
    refine ⟨⟨φ, hφ⟩, ?_⟩
    apply Subtype.ext
    show σf φ = σ
    apply MulEquiv.ext
    intro k
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm k)
    have hk : k = e (QuotientGroup.mk a) := by
      rw [ha, MulEquiv.apply_symm_apply]
    rw [hk]
    exact (hσI φ hφ a).symm.trans (hI a)

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

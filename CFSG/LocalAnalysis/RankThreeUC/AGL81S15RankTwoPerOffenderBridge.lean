module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderNat
public import CFSG.RankThree.FFModules.ChiefFactors
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Matrix

private theorem brg_monoidHom_eq_one {L : Type*} [Group L] {A : Type*} [CommGroup A]
    (hperf : commutator L = ⊤) (f : L →* A) : f = 1 := by
  have hle : commutator L ≤ f.ker :=
    Subgroup.commutator_le.mpr (fun a _ b _ => by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _))
  have htop : (⊤ : Subgroup L) ≤ f.ker := hperf ▸ hle
  ext g
  simpa using MonoidHom.mem_ker.mp (htop (Subgroup.mem_top g))

private theorem brg_factor_mem {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (L : Subgroup G) {r : ℕ}
    (Vs : Fin (r + 1) → Subrepresentation (ρ.comp L.subtype)) (i₀ : Fin r)
    (htriv : ∀ i : Fin r, i ≠ i₀ → ∀ l : ↥L,
      factorRep (Vs i.castSucc) (Vs i.succ) l = 1)
    {i : Fin r} (hi : i ≠ i₀) (l : ↥L) (x : (Vs i.succ).toSubmodule) :
    ρ (l : G) (x : V) - x ∈ (Vs i.castSucc).toSubmodule := by
  have h : factorRep (Vs i.castSucc) (Vs i.succ) l
      (Submodule.Quotient.mk (p := factorSub (Vs i.castSucc) (Vs i.succ)) x) =
      Submodule.Quotient.mk (p := factorSub (Vs i.castSucc) (Vs i.succ)) x := by
    rw [htriv i hi l]
    rfl
  rw [factorRep_mk] at h
  have hmem := (Submodule.Quotient.eq (p := factorSub (Vs i.castSucc) (Vs i.succ))).mp h
  have hcoe : (((Vs i.succ).toRepresentation l x - x : (Vs i.succ).toSubmodule) : V) =
      ρ (l : G) (x : V) - x := rfl
  rw [← hcoe]
  exact hmem

private theorem brg_fixes_below {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    (hperf : commutator ↥L = ⊤) {r : ℕ}
    (Vs : Fin (r + 1) → Subrepresentation (ρ.comp L.subtype))
    (hVs : IsCompositionSeries r Vs) (i₀ : Fin r)
    (htriv : ∀ i : Fin r, i ≠ i₀ → ∀ l : ↥L,
      factorRep (Vs i.castSucc) (Vs i.succ) l = 1) :
    ∀ (j : Fin (r + 1)), j ≤ i₀.castSucc → ∀ (l : ↥L) (x : (Vs j).toSubmodule),
      ρ (l : G) (x : V) = x := by
  intro j
  induction j using Fin.induction with
  | zero =>
    intro _ l x
    have hx : (x : V) = 0 := by
      have : Subsingleton ↥(Vs 0).toSubmodule := by
        rw [show (Vs 0).toSubmodule = (⊥ : Submodule (ZMod 2) V) from by rw [hVs.zero]; rfl]
        infer_instance
      simpa using congrArg Subtype.val (Subsingleton.elim x 0)
    rw [hx, map_zero]
  | succ i ih =>
    intro hle l x
    have hcast : i.castSucc ≤ i₀.castSucc := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hle ⊢
      omega
    have hi : i ≠ i₀ := by
      intro h
      have hle' : (i.succ : Fin (r + 1)).val ≤ (i₀.castSucc).val := Fin.le_def.mp hle
      rw [h] at hle'
      simp only [Fin.val_succ, Fin.val_castSucc] at hle'
      omega
    have hfixi : ∀ (a : ↥L) (y : (Vs i.castSucc).toSubmodule), ρ (a : G) (y : V) = y :=
      ih hcast
    let θ : ↥L →* Multiplicative ↥(Vs i.castSucc).toSubmodule :=
      { toFun := fun a => Multiplicative.ofAdd
            ⟨ρ (a : G) (x : V) - x, brg_factor_mem ρ L Vs i₀ htriv hi a x⟩
        map_one' := by
          rw [ofAdd_eq_one]
          apply Subtype.ext
          simp
        map_mul' := by
          intro a b
          rw [← ofAdd_add]
          apply congrArg Multiplicative.ofAdd
          apply Subtype.ext
          have hfixab : ρ (a : G) (ρ (b : G) (x : V) - x) = ρ (b : G) (x : V) - x := by
            have := hfixi a ⟨ρ (b : G) (x : V) - x, brg_factor_mem ρ L Vs i₀ htriv hi b x⟩
            simpa using this
          show ρ ((a * b : ↥L) : G) (x : V) - x =
            (ρ (a : G) (x : V) - x) + (ρ (b : G) (x : V) - x)
          rw [show ((a * b : ↥L) : G) = (a : G) * (b : G) from rfl, map_mul,
            Module.End.mul_apply]
          calc ρ (a : G) (ρ (b : G) (x : V)) - x
              = ρ (a : G) ((ρ (b : G) (x : V) - x) + x) - x := by rw [sub_add_cancel]
            _ = (ρ (a : G) (ρ (b : G) (x : V) - x) + ρ (a : G) x) - x := by rw [map_add]
            _ = ((ρ (b : G) (x : V) - x) + ρ (a : G) x) - x := by rw [hfixab]
            _ = (ρ (a : G) (x : V) - x) + (ρ (b : G) (x : V) - x) := by abel }
    have hθ : θ = 1 := brg_monoidHom_eq_one hperf θ
    have hθl : θ l = 1 := by rw [hθ]; rfl
    have hof : Multiplicative.ofAdd
        (⟨ρ (l : G) (x : V) - x, brg_factor_mem ρ L Vs i₀ htriv hi l x⟩ :
          ↥(Vs i.castSucc).toSubmodule) = 1 := by
      simpa [θ] using hθl
    have hsub : ρ (l : G) (x : V) - x = 0 := by
      have := ofAdd_eq_one.mp hof
      simpa using congrArg Subtype.val this
    exact sub_eq_zero.mp hsub

private theorem brg_commOn_le_succ {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    (hperf : commutator ↥L = ⊤) {r : ℕ}
    (Vs : Fin (r + 1) → Subrepresentation (ρ.comp L.subtype))
    (hVs : IsCompositionSeries r Vs) (i₀ : Fin r)
    (htriv : ∀ i : Fin r, i ≠ i₀ → ∀ l : ↥L,
      factorRep (Vs i.castSucc) (Vs i.succ) l = 1) :
    commOn ρ L ⊤ ≤ (Vs i₀.succ).toSubmodule := by
  have hP : ∀ j : Fin (r + 1), i₀.succ ≤ j →
      ∀ (l : ↥L) (x : (Vs j).toSubmodule),
        ρ (l : G) (x : V) - x ∈ (Vs i₀.succ).toSubmodule := by
    intro j
    induction j using Fin.induction with
    | zero =>
      intro hle
      exact absurd hle (not_le_of_gt (Fin.succ_pos i₀))
    | succ i ih =>
      intro hle l x
      have hi₀i : i₀ ≤ i := Fin.succ_le_succ_iff.mp hle
      rcases lt_or_eq_of_le hi₀i with hlt | heq
      · have hi : i ≠ i₀ := ne_of_gt hlt
        have hcast : i₀.succ ≤ i.castSucc := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hlt ⊢
          omega
        have hmemq : ∀ q : ↥L, ρ (q : G) (x : V) - x ∈ (Vs i.castSucc).toSubmodule :=
          fun q => brg_factor_mem ρ L Vs i₀ htriv hi q x
        let W : Submodule (ZMod 2) V := (Vs i₀.succ).toSubmodule
        let θ : ↥L →* Multiplicative (V ⧸ W) :=
          { toFun := fun a => Multiplicative.ofAdd
                (Submodule.Quotient.mk (ρ (a : G) (x : V) - x))
            map_one' := by
              rw [ofAdd_eq_one]
              simp
            map_mul' := by
              intro p q
              rw [← ofAdd_add]
              apply congrArg Multiplicative.ofAdd
              rw [← Submodule.Quotient.mk_add]
              rw [Submodule.Quotient.eq]
              have h := ih hcast p ⟨ρ (q : G) (x : V) - x, hmemq q⟩
              convert h using 1
              rw [show ((p * q : ↥L) : G) = (p : G) * (q : G) from rfl, map_mul,
                Module.End.mul_apply, map_sub]
              simp only
              abel }
        have hθ : θ = 1 := brg_monoidHom_eq_one hperf θ
        have hθl : θ l = 1 := by rw [hθ]; rfl
        have hof : Multiplicative.ofAdd
            (Submodule.Quotient.mk (p := W) (ρ (l : G) (x : V) - x)) = 1 := by
          simpa [θ] using hθl
        have hzero : Submodule.Quotient.mk (ρ (l : G) (x : V) - x) = (0 : V ⧸ W) :=
          ofAdd_eq_one.mp hof
        have := (Submodule.Quotient.mk_eq_zero (p := W)).mp hzero
        simpa [W] using this
      · have hx' : (x : V) ∈ (Vs i₀.succ).toSubmodule := by rw [heq]; exact x.2
        exact Submodule.sub_mem _
          ((Vs i₀.succ).apply_mem_toSubmodule l hx') hx'
  intro v hv
  rw [commOn] at hv
  refine Submodule.span_induction (p := fun w _ => w ∈ (Vs i₀.succ).toSubmodule)
    ?_ ?_ ?_ ?_ hv
  · rintro w ⟨a, ha, u, -, rfl⟩
    have hlast : i₀.succ ≤ (Fin.last r : Fin (r + 1)) := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_last]
      omega
    exact hP (Fin.last r) hlast ⟨a, ha⟩
      ⟨u, by rw [hVs.last]; exact Submodule.mem_top⟩
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    exact Submodule.smul_mem _ c hx

private theorem brg_commOn_le_commOn {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    (hperf : commutator ↥L = ⊤) :
    commOn ρ L ⊤ ≤ Submodule.span (ZMod 2)
      {w | ∃ l ∈ L, ∃ x ∈ commOn ρ L ⊤, w = ρ l x - x} := by
  set W : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2) {w | ∃ l ∈ L, ∃ x ∈ commOn ρ L ⊤, w = ρ l x - x} with hW
  rw [commOn]
  refine Submodule.span_le.mpr ?_
  rintro w ⟨a, ha, u, -, rfl⟩
  have hchoice : ∀ q : ↥L, ρ (q : G) u - u ∈ commOn ρ L ⊤ := by
    intro q
    rw [commOn]
    exact Submodule.subset_span ⟨(q : G), q.2, u, Submodule.mem_top, rfl⟩
  let θ : ↥L →* Multiplicative (V ⧸ W) :=
    { toFun := fun l => Multiplicative.ofAdd (Submodule.Quotient.mk (ρ (l : G) u - u))
      map_one' := by
        rw [ofAdd_eq_one]
        simp
      map_mul' := by
        intro p q
        rw [← ofAdd_add]
        apply congrArg Multiplicative.ofAdd
        rw [← Submodule.Quotient.mk_add]
        rw [Submodule.Quotient.eq]
        have hgen : ρ (p : G) (ρ (q : G) u - u) - (ρ (q : G) u - u) ∈ W := by
          rw [hW]
          exact Submodule.subset_span ⟨(p : G), p.2, ρ (q : G) u - u, hchoice q, rfl⟩
        convert hgen using 1
        rw [show ((p * q : ↥L) : G) = (p : G) * (q : G) from rfl, map_mul,
          Module.End.mul_apply, map_sub]
        abel }
  have hθ : θ = 1 := brg_monoidHom_eq_one hperf θ
  have hθa : θ ⟨a, ha⟩ = 1 := by rw [hθ]; rfl
  have hof : Multiplicative.ofAdd (Submodule.Quotient.mk (p := W) (ρ a u - u)) = 1 := by
    simpa [θ] using hθa
  exact (Submodule.Quotient.mk_eq_zero (p := W)).mp (ofAdd_eq_one.mp hof)

private theorem brg_fixSub_factor_eq_zero {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [Nontrivial ↥L]
    {F : Type*} [Field F] {m : ℕ}
    (Mat : ↥L →* Matrix.GeneralLinearGroup (Fin m) F) (hMat : Function.Injective Mat)
    {r : ℕ} (Vs : Fin (r + 1) → Subrepresentation (ρ.comp L.subtype))
    (hVs : IsCompositionSeries r Vs) (i₀ : Fin r)
    (φ : ((Vs i₀.succ).toSubmodule ⧸ factorSub (Vs i₀.castSucc) (Vs i₀.succ)) ≃+ (Fin m → F))
    (hφ : ∀ (l : ↥L) (x : (Vs i₀.succ).toSubmodule ⧸
        factorSub (Vs i₀.castSucc) (Vs i₀.succ)),
      φ (factorRep (Vs i₀.castSucc) (Vs i₀.succ) l x) =
        (Mat l : Matrix (Fin m) (Fin m) F) *ᵥ φ x)
    (x : (Vs i₀.succ).toSubmodule ⧸ factorSub (Vs i₀.castSucc) (Vs i₀.succ))
    (hx : ∀ l : ↥L, factorRep (Vs i₀.castSucc) (Vs i₀.succ) l x = x) : x = 0 := by
  let X : Submodule (ZMod 2) ((Vs i₀.succ).toSubmodule ⧸
      factorSub (Vs i₀.castSucc) (Vs i₀.succ)) :=
    { carrier := {y | ∀ l : ↥L, factorRep (Vs i₀.castSucc) (Vs i₀.succ) l y = y}
      zero_mem' := fun l => by rw [map_zero]
      add_mem' := fun {y z} hy hz l => by rw [map_add, hy l, hz l]
      smul_mem' := fun c y hy l => by rw [map_smul, hy l] }
  have hX : ∀ k, ∀ y ∈ X, factorRep (Vs i₀.castSucc) (Vs i₀.succ) k y ∈ X := by
    intro k y hy l
    have hkey := hy (k⁻¹ * l * k)
    calc factorRep (Vs i₀.castSucc) (Vs i₀.succ) l
          (factorRep (Vs i₀.castSucc) (Vs i₀.succ) k y)
        = factorRep (Vs i₀.castSucc) (Vs i₀.succ) (l * k) y := by rw [map_mul]; rfl
      _ = factorRep (Vs i₀.castSucc) (Vs i₀.succ) (k * (k⁻¹ * l * k)) y := by
            rw [show l * k = k * (k⁻¹ * l * k) by group]
      _ = factorRep (Vs i₀.castSucc) (Vs i₀.succ) k
            (factorRep (Vs i₀.castSucc) (Vs i₀.succ) (k⁻¹ * l * k) y) := by rw [map_mul]; rfl
      _ = factorRep (Vs i₀.castSucc) (Vs i₀.succ) k y := by rw [hkey]
  rcases factor_invariant_eq_bot_or_top (hVs.covBy i₀) X hX with hbot | htop
  · have : x ∈ (⊥ : Submodule (ZMod 2) ((Vs i₀.succ).toSubmodule ⧸
        factorSub (Vs i₀.castSucc) (Vs i₀.succ))) := by rw [← hbot]; exact hx
    simpa using this
  · exfalso
    have hfix : ∀ l : ↥L,
        ∀ y : (Vs i₀.succ).toSubmodule ⧸ factorSub (Vs i₀.castSucc) (Vs i₀.succ),
          factorRep (Vs i₀.castSucc) (Vs i₀.succ) l y = y := by
      intro l y
      have hy : y ∈ X := by rw [htop]; exact Submodule.mem_top
      exact hy l
    have hMat1 : ∀ l : ↥L, Mat l = 1 := by
      intro l
      have hmat : (Mat l : Matrix (Fin m) (Fin m) F) = 1 := by
        apply Matrix.ext_of_mulVec_single
        intro j
        have h1 := hφ l (φ.symm (Pi.single j (1 : F)))
        rw [hfix l (φ.symm (Pi.single j (1 : F))), AddEquiv.apply_symm_apply] at h1
        rw [Matrix.one_mulVec]
        exact h1.symm
      exact Units.ext hmat
    obtain ⟨l, hl⟩ := exists_ne (1 : ↥L)
    exact hl (hMat (by rw [hMat1 l, map_one]))

theorem NatQuot.exists_of_series_natural_factor
    {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [Nontrivial ↥L]
    (hperf : commutator ↥L = ⊤) {F : Type} [Field F] {m : ℕ}
    (Mat : ↥L →* Matrix.GeneralLinearGroup (Fin m) F) (hMat : Function.Injective Mat) {r : ℕ}
    (Vs : Fin (r + 1) → Subrepresentation (ρ.comp L.subtype)) (hVs : IsCompositionSeries r Vs)
    (i₀ : Fin r)
    (htriv : ∀ i : Fin r, i ≠ i₀ → ∀ l : ↥L, factorRep (Vs i.castSucc) (Vs i.succ) l = 1)
    (φ : ((Vs i₀.succ).toSubmodule ⧸ factorSub (Vs i₀.castSucc) (Vs i₀.succ)) ≃+ (Fin m → F))
    (hφ : ∀ (l : ↥L) (x : (Vs i₀.succ).toSubmodule ⧸ factorSub (Vs i₀.castSucc) (Vs i₀.succ)),
      φ (factorRep (Vs i₀.castSucc) (Vs i₀.succ) l x) =
        (Mat l : Matrix (Fin m) (Fin m) F) *ᵥ φ x) :
    ∃ N : NatQuot ρ L F m, N.Mat = Mat ∧ N.I = commOn ρ L ⊤ ∧
      ∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2) {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x} := by
  classical
  let I : Submodule (ZMod 2) V := commOn ρ L ⊤
  have hIle : I ≤ (Vs i₀.succ).toSubmodule :=
    brg_commOn_le_succ ρ L hperf Vs hVs i₀ htriv
  let toV : ↥I →ₗ[ZMod 2] (Vs i₀.succ).toSubmodule :=
    { toFun := fun v => ⟨(v : V), hIle v.2⟩
      map_add' := by intro a b; ext; rfl
      map_smul' := by intro c x; ext; rfl }
  let q : (Vs i₀.succ).toSubmodule →ₗ[ZMod 2]
      ((Vs i₀.succ).toSubmodule ⧸ factorSub (Vs i₀.castSucc) (Vs i₀.succ)) :=
    Submodule.mkQ _
  let π : ↥I →+ (Fin m → F) := φ.toAddMonoidHom.comp (q.comp toV).toAddMonoidHom
  have hinv : ∀ l ∈ L, ∀ v ∈ I, ρ l v ∈ I := by
    intro l hl v hv
    exact isInvariant_commOn_top (K := L) (H := L) Subgroup.le_normalizer l hl v hv
  have hkey : ∀ (l : ↥L) (w : ↥I),
      q (toV ⟨ρ (l : G) (w : V), hinv l l.2 w w.2⟩) =
        factorRep (Vs i₀.castSucc) (Vs i₀.succ) l (q (toV w)) := by
    intro l w
    show Submodule.Quotient.mk (toV ⟨ρ (l : G) (w : V), hinv l l.2 w w.2⟩) =
      factorRep (Vs i₀.castSucc) (Vs i₀.succ) l (Submodule.Quotient.mk (toV w))
    rw [factorRep_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    rfl
  have hequiv : ∀ (l : ↥L) (v : ↥I),
      π ⟨ρ (l : G) (v : V), hinv l l.2 v v.2⟩ =
        (Mat l : Matrix (Fin m) (Fin m) F) *ᵥ π v := by
    intro l v
    show φ (q (toV ⟨ρ (l : G) (v : V), hinv l l.2 v v.2⟩)) =
      (Mat l : Matrix (Fin m) (Fin m) F) *ᵥ φ (q (toV v))
    rw [hkey l v, hφ]
  have hker : ∀ v : ↥I, π v = 0 ↔ ∀ l ∈ L, ρ l v = v := by
    intro v
    constructor
    · intro hpi l hl
      have h0 : Submodule.Quotient.mk (p := factorSub (Vs i₀.castSucc) (Vs i₀.succ))
          (toV v) = 0 := by
        apply φ.injective
        rw [map_zero]
        exact hpi
      have hmem : (v : V) ∈ (Vs i₀.castSucc).toSubmodule := by
        have := (Submodule.Quotient.mk_eq_zero
          (p := factorSub (Vs i₀.castSucc) (Vs i₀.succ))).mp h0
        simpa [factorSub, toV] using this
      have := brg_fixes_below ρ L hperf Vs hVs i₀ htriv i₀.castSucc le_rfl
        ⟨l, hl⟩ ⟨(v : V), hmem⟩
      simpa using this
    · intro hv
      have hxfix : ∀ l : ↥L, factorRep (Vs i₀.castSucc) (Vs i₀.succ) l
          (Submodule.Quotient.mk (toV v)) = Submodule.Quotient.mk (toV v) := by
        intro l
        rw [factorRep_mk]
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        exact hv (l : G) l.2
      have hzero := brg_fixSub_factor_eq_zero ρ L Mat hMat Vs hVs i₀ φ hφ
        (Submodule.Quotient.mk (toV v)) hxfix
      show φ (Submodule.Quotient.mk (toV v)) = 0
      rw [hzero, map_zero]
  let S : Submodule (ZMod 2) ((Vs i₀.succ).toSubmodule ⧸
      factorSub (Vs i₀.castSucc) (Vs i₀.succ)) := Submodule.map (q.comp toV) ⊤
  have hSinv : ∀ k, ∀ y ∈ S,
      factorRep (Vs i₀.castSucc) (Vs i₀.succ) k y ∈ S := by
    intro k y hy
    obtain ⟨v, -, hvx⟩ := Submodule.mem_map.mp hy
    rw [← hvx]
    refine Submodule.mem_map.mpr
      ⟨⟨ρ (k : G) (v : V), hinv k k.2 v v.2⟩, Submodule.mem_top, ?_⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hkey k v]
  have hsurj : Function.Surjective π := by
    rcases factor_invariant_eq_bot_or_top (hVs.covBy i₀) S hSinv with hSbot | hStop
    · exfalso
      have htrivI : ∀ v : ↥I, ∀ l : ↥L, ρ (l : G) (v : V) = (v : V) := by
        intro v l
        have hπ0 : π v = 0 := by
          have hmemS : (q.comp toV) v ∈ S :=
            Submodule.mem_map.mpr ⟨v, Submodule.mem_top, rfl⟩
          rw [hSbot, Submodule.mem_bot] at hmemS
          show φ (Submodule.Quotient.mk (toV v)) = 0
          rw [show Submodule.Quotient.mk (toV v) = (q.comp toV) v from rfl, hmemS, map_zero]
        exact (hker v).mp hπ0 l l.2
      have hI0 : I = ⊥ := by
        have hle := brg_commOn_le_commOn (ρ := ρ) L hperf
        have hspan0 : Submodule.span (ZMod 2)
            {w | ∃ l ∈ L, ∃ x ∈ commOn ρ L ⊤, w = ρ l x - x} = ⊥ := by
          rw [Submodule.span_eq_bot]
          rintro w ⟨l, hl, x, hx, rfl⟩
          have : ρ l x = x := htrivI ⟨x, hx⟩ ⟨l, hl⟩
          rw [this, sub_self]
        rw [eq_bot_iff]
        intro v hv
        have := hle hv
        rw [hspan0, Submodule.mem_bot] at this
        exact this
      have htrivV : ∀ l ∈ L, ∀ v : V, ρ l v = v := by
        intro l hl v
        exact (commOn_eq_bot_iff (ρ := ρ) (A := L) (U := (⊤ : Submodule (ZMod 2) V))).mp
          (show commOn ρ L ⊤ = ⊥ from hI0) l hl v (Submodule.mem_top)
      have : Nontrivial ((Vs i₀.succ).toSubmodule ⧸
          factorSub (Vs i₀.castSucc) (Vs i₀.succ)) :=
        factor_nontrivial (hVs.covBy i₀)
      obtain ⟨x₀, hx₀⟩ := exists_ne (0 : (Vs i₀.succ).toSubmodule ⧸
        factorSub (Vs i₀.castSucc) (Vs i₀.succ))
      have hxfix : ∀ l : ↥L,
          factorRep (Vs i₀.castSucc) (Vs i₀.succ) l x₀ = x₀ := by
        intro l
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x₀
        rw [factorRep_mk]
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        exact htrivV (l : G) l.2 (y : V)
      exact hx₀ (brg_fixSub_factor_eq_zero ρ L Mat hMat Vs hVs i₀ φ hφ x₀ hxfix)
    · intro u
      have hu : φ.symm u ∈ S := by rw [hStop]; exact Submodule.mem_top
      obtain ⟨v, -, hvx⟩ := Submodule.mem_map.mp hu
      refine ⟨v, ?_⟩
      show φ (Submodule.Quotient.mk (toV v)) = u
      rw [show Submodule.Quotient.mk (toV v) = (q.comp toV) v from rfl, hvx,
        AddEquiv.apply_symm_apply]
  refine ⟨{ Mat := Mat
            mat_inj := hMat
            I := commOn ρ L ⊤
            inv := hinv
            π := π
            surj := hsurj
            equiv := hequiv
            ker_iff := hker }, rfl, rfl, ?_⟩
  intro v hv
  exact brg_commOn_le_commOn (ρ := ρ) L hperf hv

end CFSG.LocalAnalysis.RankThreeUC.S15

end

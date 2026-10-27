module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMCfg
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XHyp
import CFSG.GroupTheory.OddKernelImage

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped commutatorElement MatrixGroups Pointwise

private theorem mem_normalizer_conj {G : Type*} [Group G] {U : Subgroup G} {A : G}
    (hA : A ∈ Subgroup.normalizer (U : Set G)) {u : G} (hu : u ∈ U) :
    A * u * A⁻¹ ∈ U :=
  (Subgroup.mem_normalizer_iff.mp hA u).mp hu

private theorem gInduced_one {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type}
    [Field F] {U : Subgroup (GL (Fin d) F)}
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj U) :
    GInduced θ (1 : Ω) (1 : GL (Fin d) F) := by
  refine ⟨1, ?_, ?_⟩
  · intro h h' hh
    rw [MulAut.one_apply]
    rw [show h = h' by
      exact Subtype.ext (by simpa using hh.symm)]
  · intro l l' hl
    rw [MulAut.one_apply]
    rw [show l = l' by
      exact Subtype.ext (by simpa using hl.symm)]

private theorem gInduced_mul {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type}
    [Field F] {U : Subgroup (GL (Fin d) F)}
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj U) {b b' : Ω}
    {A A' : GL (Fin d) F} (hAN : A ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)))
    (hA'N : A' ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)))
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω))
    (hb'N : b' ∈ Subgroup.normalizer (S : Set Ω))
    (hA : GInduced θ b A) (hA' : GInduced θ b' A') :
    GInduced θ (b' * b) (A * A') := by
  obtain ⟨φ, hφg, hφi⟩ := hA
  obtain ⟨ψ, hψg, hψi⟩ := hA'
  refine ⟨φ * ψ, ?_, ?_⟩
  · intro h h' hh
    have h₁ : A' * (h : GL (Fin d) F) * A'⁻¹ ∈ U := mem_normalizer_conj hA'N h.2
    have hh' : (h' : GL (Fin d) F) =
        A * (⟨A' * (h : GL (Fin d) F) * A'⁻¹, h₁⟩ : ↥U) * A⁻¹ := by
      rw [hh]
      group
    have hg₁ := hφg ⟨A' * (h : GL (Fin d) F) * A'⁻¹, h₁⟩ h' hh'
    have hg₂ := hψg h ⟨A' * (h : GL (Fin d) F) * A'⁻¹, h₁⟩ rfl
    change (φ * ψ) (LargeEvenProjMk U h) = LargeEvenProjMk U h'
    rw [MulAut.mul_apply, hg₂]
    exact hg₁
  · intro l l' hl
    have h₁ : b'⁻¹ * (l : Ω) * b' ∈ S := by
      simpa only [inv_inv] using
        mem_normalizer_conj ((Subgroup.normalizer (S : Set Ω)).inv_mem hb'N) l.2
    have hl' : (l' : Ω) = b⁻¹ * (⟨b'⁻¹ * (l : Ω) * b', h₁⟩ : ↥S) * b := by
      show (l' : Ω) = b⁻¹ * (b'⁻¹ * (l : Ω) * b') * b
      rw [hl]
      group
    have hg₁ := hφi ⟨b'⁻¹ * (l : Ω) * b', h₁⟩ l' hl'
    have hg₂ := hψi l ⟨b'⁻¹ * (l : Ω) * b', h₁⟩ rfl
    change (φ * ψ) (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l')
    rw [MulAut.mul_apply, hg₂]
    exact hg₁

private theorem gInduced_inv {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type}
    [Field F] {U : Subgroup (GL (Fin d) F)}
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj U) {b : Ω} {A : GL (Fin d) F}
    (hAN : A ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)))
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω)) (hA : GInduced θ b A) :
    GInduced θ b⁻¹ A⁻¹ := by
  obtain ⟨φ, hφg, hφi⟩ := hA
  refine ⟨φ⁻¹, ?_, ?_⟩
  · intro h h' hh
    have hh' : (h : GL (Fin d) F) = A * (h' : GL (Fin d) F) * A⁻¹ := by
      rw [hh]
      group
    have hg := hφg h' h hh'
    change φ⁻¹ (LargeEvenProjMk U h) = LargeEvenProjMk U h'
    rw [← hg, MulAut.inv_apply]
    simp
  · intro l l' hl
    have h₁ : b * (l : Ω) * b⁻¹ ∈ S :=
      mem_normalizer_conj hbN l.2
    have hl' : (l : Ω) = b⁻¹ * (⟨b * (l : Ω) * b⁻¹, h₁⟩ : ↥S) * b := by
      show (l : Ω) = b⁻¹ * (b * (l : Ω) * b⁻¹) * b
      group
    have hg := hφi ⟨b * (l : Ω) * b⁻¹, h₁⟩ l hl'
    have hl'_eq : (⟨b * (l : Ω) * b⁻¹, h₁⟩ : ↥S) = l' :=
      Subtype.ext (by simpa using hl.symm)
    rw [← hl'_eq]
    change φ⁻¹ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk _)
    rw [← hg, MulAut.inv_apply]
    simp

private theorem gInduced_pow {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type}
    [Field F] {U : Subgroup (GL (Fin d) F)}
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj U) {b : Ω} {A : GL (Fin d) F}
    (hAN : A ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)))
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω)) (hA : GInduced θ b A) :
    ∀ n : ℕ, GInduced θ (b ^ n) (A ^ n) := by
  intro n
  induction n with
  | zero => simpa using gInduced_one (Ω := Ω) θ
  | succ n ih =>
      have hANn : A ^ n ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)) :=
        Subgroup.pow_mem _ hAN n
      have hbNn : b ^ n ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.pow_mem _ hbN n
      have h := gInduced_mul θ hANn hAN hbNn hbN ih hA
      rw [show b * b ^ n = b ^ n * b from (Commute.self_pow b n).eq] at h
      simpa [pow_succ, pow_succ'] using h

private theorem scalar_of_same_induced {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ}
    {F : Type} [Field F] {U : Subgroup (GL (Fin d) F)}
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj U) {b : Ω} {A A' : GL (Fin d) F}
    (hcen : ∀ C : GL (Fin d) F, (∀ u ∈ U, ⁅C, u⁆ ∈ LargeEvenScalars (Fin d) F) →
      C ∈ LargeEvenScalars (Fin d) F)
    (hAN : A ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)))
    (hA'N : A' ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)))
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω))
    (hA : GInduced θ b A) (hA' : GInduced θ b A') :
    A' * A⁻¹ ∈ LargeEvenScalars (Fin d) F := by
  obtain ⟨φ, hφg, hφi⟩ := hA
  obtain ⟨ψ, hψg, hψi⟩ := hA'
  have hφψ : φ = ψ := by
    ext x
    obtain ⟨q, rfl⟩ := θ.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hmem : b⁻¹ * (l : Ω) * b ∈ S := by
      simpa only [inv_inv] using
        mem_normalizer_conj ((Subgroup.normalizer (S : Set Ω)).inv_mem hbN) l.2
    rw [hφi l ⟨b⁻¹ * (l : Ω) * b, hmem⟩ rfl,
      hψi l ⟨b⁻¹ * (l : Ω) * b, hmem⟩ rfl]
  apply hcen (A' * A⁻¹)
  intro u hu
  have hAuinv : A⁻¹ * (u : GL (Fin d) F) * A ∈ U :=
    mem_normalizer_conj ((Subgroup.normalizer (U : Set (GL (Fin d) F))).inv_mem hAN) hu
  let h : ↥U := ⟨A⁻¹ * (u : GL (Fin d) F) * A, hAuinv⟩
  have hAh : (u : GL (Fin d) F) = A * (h : GL (Fin d) F) * A⁻¹ := by
    show (u : GL (Fin d) F) = A * (A⁻¹ * (u : GL (Fin d) F) * A) * A⁻¹
    group
  have hCN : A' * A⁻¹ ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)) :=
    (Subgroup.normalizer (U : Set (GL (Fin d) F))).mul_mem hA'N
      ((Subgroup.normalizer (U : Set (GL (Fin d) F))).inv_mem hAN)
  have hCu : (A' * A⁻¹) * (u : GL (Fin d) F) * (A' * A⁻¹)⁻¹ ∈ U :=
    mem_normalizer_conj hCN hu
  have hh' : (⟨A' * (h : GL (Fin d) F) * A'⁻¹,
        mem_normalizer_conj hA'N h.2⟩ : ↥U) =
      (⟨(A' * A⁻¹) * (u : GL (Fin d) F) * (A' * A⁻¹)⁻¹, hCu⟩ : ↥U) := by
    apply Subtype.ext
    show A' * (A⁻¹ * (u : GL (Fin d) F) * A) * A'⁻¹ =
      (A' * A⁻¹) * (u : GL (Fin d) F) * (A' * A⁻¹)⁻¹
    group
  have hqu : LargeEvenProjMk U (⟨(A' * A⁻¹) * (u : GL (Fin d) F) * (A' * A⁻¹)⁻¹,
      hCu⟩ : ↥U) = LargeEvenProjMk U ⟨u, hu⟩ := by
    have h1 := hφg h ⟨u, hu⟩ hAh
    rw [hφψ] at h1
    have h2 := hψg h ⟨A' * (h : GL (Fin d) F) * A'⁻¹, mem_normalizer_conj hA'N h.2⟩ rfl
    rw [hh'] at h2
    exact h2.symm.trans h1
  have hdiv := (QuotientGroup.eq_iff_div_mem.mp hqu)
  have hsc : (A' * A⁻¹) * (u : GL (Fin d) F) * (A' * A⁻¹)⁻¹ * (u : GL (Fin d) F)⁻¹ ∈
      LargeEvenScalars (Fin d) F := by
    simpa only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv] using
      (Subgroup.mem_subgroupOf.mp hdiv)
  simpa only [commutatorElement_def, mul_assoc] using hsc

private theorem hom_eq_of_inv_mul_mem_center {H X : Type*} [Group H] [Group X]
    (hH : Group.IsPerfect H) {f₁ f₂ : H →* X}
    (h : ∀ g : H, (f₁ g)⁻¹ * f₂ g ∈ Subgroup.center X) : f₁ = f₂ := by
  let χ : H →* Subgroup.center X :=
    { toFun := fun g => ⟨(f₁ g)⁻¹ * f₂ g, h g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (h a)
        change (f₁ (a * b))⁻¹ * f₂ (a * b) =
          ((f₁ a)⁻¹ * f₂ a) * ((f₁ b)⁻¹ * f₂ b)
        rw [map_mul, map_mul, mul_inv_rev]
        calc (f₁ b)⁻¹ * (f₁ a)⁻¹ * (f₂ a * f₂ b)
            = (f₁ b)⁻¹ * ((f₁ a)⁻¹ * f₂ a) * f₂ b := by group
          _ = ((f₁ a)⁻¹ * f₂ a) * (f₁ b)⁻¹ * f₂ b := by rw [hc ((f₁ b)⁻¹)]
          _ = ((f₁ a)⁻¹ * f₂ a) * ((f₁ b)⁻¹ * f₂ b) := by group }
  have hker : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ χ.ker := Abelianization.commutator_subset_ker χ
  have htop : ⁅(⊤ : Subgroup H), ⊤⁆ = ⊤ := hH.commutator_eq_top
  rw [htop] at hker
  refine MonoidHom.ext fun g => ?_
  have hg : g ∈ χ.ker := hker (Subgroup.mem_top g)
  have h1 : (f₁ g)⁻¹ * f₂ g = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hg)
  exact inv_mul_eq_one.1 h1

private theorem commutatorElement_mul_center_eq {G : Type*} [Group G] (x y : G)
    {c d : G} (hc : c ∈ Subgroup.center G) (hd : d ∈ Subgroup.center G) :
    ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  have hc' : ∀ g : G, c * g * c⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hc g, mul_inv_cancel_right]
  have hd' : ∀ g : G, d * g * d⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hd g, mul_inv_cancel_right]
  calc ⁅x * c, y * d⁆ = x * (c * (y * d) * c⁻¹) * x⁻¹ * d⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = x * y * (d * x⁻¹ * d⁻¹) * y⁻¹ := by rw [hc']; group
    _ = ⁅x, y⁆ := by rw [hd', commutatorElement_def]

private theorem commutator_sup_center_le {G : Type*} [Group G] {A Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) : ⁅A ⊔ Z, A ⊔ Z⁆ ≤ A := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, c, hc, rfl⟩ := (Subgroup.mem_sup_of_normal_right).mp hx
  obtain ⟨b, hb, d, hd, rfl⟩ := (Subgroup.mem_sup_of_normal_right).mp hy
  rw [commutatorElement_mul_center_eq a b (hZ hc) (hZ hd)]
  simpa only [commutatorElement_def] using
    A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)

theorem gen_ghat {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : MCfg p S B N D K x) {d : ℕ} {F : Type} [Field F] [Finite F]
    {U : Subgroup (GL (Fin d) F)} (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj U)
    (V : Subgroup (GL (Fin d) F)) (hVs : LargeEvenScalars (Fin d) F ≤ V)
    (hVN : V ≤ Subgroup.normalizer (U : Set (GL (Fin d) F)))
    (hcen : ∀ A : GL (Fin d) F, (∀ u ∈ U, ⁅A, u⁆ ∈ LargeEvenScalars (Fin d) F) →
      A ∈ LargeEvenScalars (Fin d) F)
    (hact : ∀ b ∈ B, ∃ A ∈ V, GInduced θ b A) :
    ∃ Gh : Subgroup (GL (Fin d) F), Gh ≤ V ∧
      (∀ A, A ∈ Gh ↔ A ∈ V ∧ ∃ b ∈ B, GInduced θ b A) ∧
      LargeEvenScalars (Fin d) F ≤ Gh ∧ MElemMod p d F Gh ∧
      p * (LargeEvenScalars (Fin d) F).relIndex Gh = Nat.card B := by
  classical
  let H := LargeEvenScalars (Fin d) F
  have hBN : B ≤ Subgroup.normalizer (S : Set Ω) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking
      (CFSG.LocalAnalysis.GLTheoremA.innerDiagMarking_of_split16 hcfg.split)
  have hperfS : Group.IsPerfect ↥S := ⟨hcfg.qs.1⟩
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  let Gh : Subgroup (GL (Fin d) F) :=
    { carrier := {A | A ∈ V ∧ ∃ b ∈ B, GInduced θ b A}
      one_mem' := ⟨V.one_mem, 1, B.one_mem, gInduced_one θ⟩
      mul_mem' := by
        intro A A' hA hA'
        obtain ⟨b, hb, hind⟩ := hA.2
        obtain ⟨b', hb', hind'⟩ := hA'.2
        exact ⟨V.mul_mem hA.1 hA'.1, b' * b, B.mul_mem hb' hb,
          gInduced_mul θ (hVN hA.1) (hVN hA'.1) (hBN hb) (hBN hb') hind hind'⟩
      inv_mem' := by
        intro A hA
        obtain ⟨b, hb, hind⟩ := hA.2
        exact ⟨V.inv_mem hA.1, b⁻¹, B.inv_mem hb,
          gInduced_inv θ (hVN hA.1) (hBN hb) hind⟩ }
  have hGh : ∀ A, A ∈ Gh ↔ A ∈ V ∧ ∃ b ∈ B, GInduced θ b A := fun A => Iff.rfl
  have hGhV : Gh ≤ V := fun A hA => (hGh A).1 hA |>.1
  have hsc_le : H ≤ Gh := by
    intro c hc
    have hcenter : c ∈ Subgroup.center (GL (Fin d) F) := by
      rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
      exact hc
    refine (hGh c).2 ⟨hVs hc, 1, B.one_mem, ?_⟩
    refine ⟨1, ?_, ?_⟩
    · intro h h' hh
      rw [MulAut.one_apply]
      have hh' : h' = h := by
        apply Subtype.ext
        show (h' : GL (Fin d) F) = (h : GL (Fin d) F)
        rw [show (h' : GL (Fin d) F) = c * h * c⁻¹ from hh,
          ← Subgroup.mem_center_iff.mp hcenter h]
        group
      first
        | exact hh'
        | exact congrArg (LargeEvenProjMk U) hh'.symm
    · intro l l' hl
      rw [MulAut.one_apply]
      rw [show l = l' by exact Subtype.ext (by simpa using hl.symm)]
  let Ab : ↥B → GL (Fin d) F := fun b => Classical.choose (hact b b.2)
  have hAbV : ∀ b : ↥B, Ab b ∈ V := fun b =>
    (Classical.choose_spec (hact b b.2)).1
  have hAbInd : ∀ b : ↥B, GInduced θ (b : Ω) (Ab b) := fun b =>
    (Classical.choose_spec (hact b b.2)).2
  have hAbGh : ∀ b : ↥B, Ab b ∈ Gh := fun b =>
    (hGh (Ab b)).2 ⟨hAbV b, b, b.2, hAbInd b⟩
  let Hsub : Subgroup ↥Gh := H.subgroupOf Gh
  let f : ↥B →* (↥Gh ⧸ Hsub) :=
    { toFun := fun b => QuotientGroup.mk' Hsub ⟨Ab b, hAbGh b⟩
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).mpr
        apply Subgroup.mem_subgroupOf.mpr
        have hsc := scalar_of_same_induced θ hcen
          (Subgroup.one_mem (Subgroup.normalizer (U : Set (GL (Fin d) F))))
          (hVN (hAbV 1)) (Subgroup.one_mem (Subgroup.normalizer (S : Set Ω)))
          (gInduced_one θ) (by simpa using hAbInd (1 : ↥B))
        simpa using hsc
      map_mul' := fun a b => by
        change QuotientGroup.mk' Hsub ⟨Ab (a * b), hAbGh (a * b)⟩ =
          QuotientGroup.mk' Hsub ⟨Ab a, hAbGh a⟩ *
            QuotientGroup.mk' Hsub ⟨Ab b, hAbGh b⟩
        rw [← map_mul]
        apply (QuotientGroup.eq_iff_div_mem).mpr
        rw [Subgroup.mem_subgroupOf]
        have hcomm : (b : Ω) * (a : Ω) = (a : Ω) * (b : Ω) :=
          IsElemAbelian.comm hcfg.elem b.2 a.2
        have hprod : GInduced θ ((a : Ω) * (b : Ω)) (Ab a * Ab b) := by
          have h := gInduced_mul θ (hVN (hAbV a)) (hVN (hAbV b))
            (hBN a.2) (hBN b.2) (hAbInd a) (hAbInd b)
          rwa [hcomm] at h
        have hsc := scalar_of_same_induced θ hcen (hVN (hAbV (a * b)))
          (hVN (V.mul_mem (hAbV a) (hAbV b))) (hBN (B.mul_mem a.2 b.2))
          (hAbInd (a * b)) hprod
        have hsc' : Ab (a * b) * (Ab a * Ab b)⁻¹ ∈ H := by
          have := H.inv_mem hsc
          simpa [mul_inv_rev, inv_inv] using this
        simpa only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv]
          using hsc' }
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective Hsub q
    obtain ⟨b, hb, hind⟩ := ((hGh (A : GL (Fin d) F)).1 A.2).2
    refine ⟨⟨b, hb⟩, ?_⟩
    change QuotientGroup.mk' Hsub ⟨Ab ⟨b, hb⟩, hAbGh _⟩ =
      QuotientGroup.mk' Hsub A
    apply (QuotientGroup.eq_iff_div_mem).mpr
    rw [Subgroup.mem_subgroupOf]
    have hsc := scalar_of_same_induced θ hcen (hVN (hAbV ⟨b, hb⟩))
      (hVN ((hGh (A : GL (Fin d) F)).1 A.2).1) (hBN hb)
      (hAbInd ⟨b, hb⟩) hind
    have hsc' : Ab ⟨b, hb⟩ * (A : GL (Fin d) F)⁻¹ ∈ H := by
      have := H.inv_mem hsc
      simpa [mul_inv_rev, inv_inv] using this
    simpa only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv]
      using hsc'
  have hker_iff : ∀ b : ↥B, f b = 1 ↔ (b : Ω) ∈ Subgroup.zpowers x := by
    intro b
    constructor
    · intro hb1
      have hmem : (⟨Ab b, hAbGh b⟩ : ↥Gh) ∈ Hsub :=
        (QuotientGroup.eq_one_iff _).mp hb1
      have hsc : Ab b ∈ H := Subgroup.mem_subgroupOf.mp hmem
      have hcenter : Ab b ∈ Subgroup.center (GL (Fin d) F) := by
        rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
        exact hsc
      obtain ⟨φ, hφg, hφi⟩ := hAbInd b
      have hφ1 : φ = 1 := by
        ext q
        obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
        have hrel : (h : GL (Fin d) F) = Ab b * h * (Ab b)⁻¹ := by
          rw [← Subgroup.mem_center_iff.mp hcenter h]
          group
        exact hφg h h hrel
      have hind1 : LargeEvenInduces θ (fun l l' : ↥S => (l' : Ω) = b⁻¹ * l * b) 1 := by
        rw [← hφ1]
        exact hφi
      have hcenter' := CFSG.LocalAnalysis.GLTheoremA.T171Sh.exists_center_of_largeEvenInduces_one
        (L := S) (θ := θ) (a := (b : Ω)) (hBN b.2) hind1
      have hcentS : (b : Ω) ∈ Subgroup.centralizer (S : Set Ω) :=
        CFSG.LocalAnalysis.GLTheoremA.T171Sh.centralizes_of_conjRel_center
          (L := S) (a := (b : Ω)) (hBN b.2) hcenter' hperfS
      exact (hcfg.cent (b : Ω) b.2).mp hcentS
    · intro hbzp
      have hxC : x ∈ Subgroup.centralizer (S : Set Ω) :=
        (hcfg.cent x hcfg.mem).mpr (Subgroup.mem_zpowers x)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbzp
      have hbC : (b : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
        rw [← hk]
        exact (Subgroup.centralizer (S : Set Ω)).zpow_mem hxC k
      have hrelid : ∀ l l' : ↥S, (l' : Ω) = (b : Ω)⁻¹ * l * b → l = l' := by
        intro l l' hl
        apply Subtype.ext
        have hcomm : (l : Ω) * (b : Ω) = (b : Ω) * (l : Ω) :=
          Subgroup.mem_centralizer_iff.mp hbC (l : Ω) l.2
        have hb_eq : (b : Ω)⁻¹ * (l : Ω) * (b : Ω) = (l : Ω) := by
          calc (b : Ω)⁻¹ * (l : Ω) * (b : Ω) = (b : Ω)⁻¹ * ((l : Ω) * (b : Ω)) := by
                group
            _ = (b : Ω)⁻¹ * ((b : Ω) * (l : Ω)) := by rw [hcomm]
            _ = (l : Ω) := by group
        exact hb_eq.symm.trans hl.symm
      have hind1 : LargeEvenInduces θ (fun l l' : ↥S => (l' : Ω) = b⁻¹ * l * b) 1 :=
        CFSG.LocalAnalysis.GLTheoremA.T171Sh.largeEvenInduces_one hrelid
      have h1ind : GInduced θ (b : Ω) (1 : GL (Fin d) F) := by
        refine ⟨1, ?_, hind1⟩
        intro h h' hh
        rw [MulAut.one_apply]
        have hh' : h = h' := by simpa using hh.symm
        rw [hh']
      have hsc := scalar_of_same_induced θ hcen
        (Subgroup.one_mem (Subgroup.normalizer (U : Set (GL (Fin d) F))))
        (hVN (hAbV b)) (hBN b.2) h1ind (hAbInd b)
      apply (QuotientGroup.eq_one_iff _).mpr
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hsc)
  have hker_eq : f.ker = (Subgroup.zpowers x).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, hker_iff b, Subgroup.mem_subgroupOf]
  have hcardker : Nat.card f.ker = p := by
    rw [hker_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hcfg.mem)).toEquiv,
      Nat.card_zpowers]
    exact orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one
  have hel : MElemMod p d F Gh := by
    constructor
    · intro g hg
      obtain ⟨b, hb, hind⟩ := ((hGh g).1 hg).2
      have hgV : g ∈ V := ((hGh g).1 hg).1
      have hgp : GInduced θ (b ^ p) (g ^ p) :=
        gInduced_pow θ (hVN hgV) (hBN hb) hind p
      rw [hcfg.elem.2 b hb] at hgp
      have hsc := scalar_of_same_induced θ hcen
        (Subgroup.one_mem (Subgroup.normalizer (U : Set (GL (Fin d) F))))
        (hVN (V.pow_mem hgV p)) (Subgroup.one_mem (Subgroup.normalizer (S : Set Ω)))
        (gInduced_one θ) (by simpa using hgp)
      simpa using hsc
    · intro g hg g' hg'
      obtain ⟨b, hb, hind⟩ := ((hGh g).1 hg).2
      obtain ⟨b', hb', hind'⟩ := ((hGh g').1 hg').2
      have hgV : g ∈ V := ((hGh g).1 hg).1
      have hg'V : g' ∈ V := ((hGh g').1 hg').1
      have hgg' : GInduced θ (b' * b) (g * g') :=
        gInduced_mul θ (hVN hgV) (hVN hg'V) (hBN hb) (hBN hb') hind hind'
      have hinvg : GInduced θ b⁻¹ g⁻¹ :=
        gInduced_inv θ (hVN hgV) (hBN hb) hind
      have hinvg' : GInduced θ b'⁻¹ g'⁻¹ :=
        gInduced_inv θ (hVN hg'V) (hBN hb') hind'
      have hstep := gInduced_mul θ (hVN (V.mul_mem hgV hg'V))
        (hVN (V.inv_mem hgV))
        (hBN (B.mul_mem hb' hb)) (hBN (B.inv_mem hb)) hgg' hinvg
      have hall := gInduced_mul θ
        (hVN (V.mul_mem (V.mul_mem hgV hg'V) (V.inv_mem hgV)))
        (hVN (V.inv_mem hg'V))
        (hBN (B.mul_mem (B.inv_mem hb) (B.mul_mem hb' hb))) (hBN (B.inv_mem hb'))
        hstep hinvg'
      have hone : b'⁻¹ * (b⁻¹ * (b' * b)) = 1 := by
        rw [IsElemAbelian.comm hcfg.elem hb' hb]
        group
      rw [hone] at hall
      have hsc := scalar_of_same_induced θ hcen
        (Subgroup.one_mem (Subgroup.normalizer (U : Set (GL (Fin d) F))))
        (hVN (V.mul_mem (V.mul_mem (V.mul_mem hgV hg'V) (V.inv_mem hgV))
          (V.inv_mem hg'V)))
        (Subgroup.one_mem (Subgroup.normalizer (S : Set Ω)))
        (gInduced_one θ) (by simpa [mul_assoc] using hall)
      simpa [commutatorElement_def, mul_assoc] using hsc
  have hcard : p * H.relIndex Gh = Nat.card B := by
    have hcardB := Subgroup.card_ker_mul_card_of_surjective (f := f) hsurj
    rw [hcardker] at hcardB
    change p * (H.subgroupOf Gh).index = Nat.card ↥B
    change p * Nat.card (↥Gh ⧸ Hsub) = Nat.card ↥B
    exact hcardB
  exact ⟨Gh, hGhV, hGh, hsc_le, hel, hcard⟩

theorem gen_two_subgroup {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : MCfg p S B N D K x) {d : ℕ} {F : Type} [Field F] [Finite F]
    {U : Subgroup (GL (Fin d) F)} (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj U)
    (hodd : Odd (Nat.card (LargeEvenProjMk U).ker)) {Gh : Subgroup (GL (Fin d) F)}
    (hGhN : Gh ≤ Subgroup.normalizer (U : Set (GL (Fin d) F)))
    (hGh : ∀ A ∈ Gh, ∃ b ∈ B, GInduced θ b A) :
    ∃ T : Subgroup (GL (Fin d) F), IsPGroup 2 T ∧ T ≠ ⊥ ∧ T ≤ U ∧
      ∀ A ∈ Gh, A ∈ Subgroup.normalizer (T : Set (GL (Fin d) F)) := by
  classical
  obtain ⟨T1, hT1S, hT1_2, hT1N, hT1comm⟩ := hcfg.hc
  have hBT : B ≤ Subgroup.normalizer (T1 : Set Ω) :=
    le_trans le_sup_right hT1N
  have hKS : K ≤ S := hcfg.K_le
  have hIS : closureIn K N ≤ S :=
    CFSG.LocalAnalysis.GLTheoremA.T173X.closureIn_le_of_normal hcfg.normal hKS
  let ZS : Subgroup Ω := (Subgroup.center ↥S).map S.subtype
  have hT1_notZ : ¬ T1 ≤ ZS := by
    intro hZ
    apply hT1comm
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp (hZ ht)
    have hs' : (⟨t, hT1S ht⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rwa [show (⟨t, hT1S ht⟩ : ↥S) = s by exact Subtype.ext hst.symm]
    have hxS : (⟨x, hIS hx⟩ : ↥S) ∈ (⊤ : Subgroup ↥S) := Subgroup.mem_top _
    have hcomm := Subgroup.mem_center_iff.mp hs' ⟨x, hIS hx⟩
    exact congrArg Subtype.val hcomm.symm
  let ψS : ↥S →* LargeEvenProj U :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))
  let Ebar : Subgroup (LargeEvenProj U) := (T1.subgroupOf S).map ψS
  have hEbar_2 : IsPGroup 2 Ebar := hT1_2.comap_subtype.map ψS
  have hEbar_ne : Ebar ≠ ⊥ := by
    intro hbot
    apply hT1_notZ
    intro t ht
    have hmem : ψS ⟨t, hT1S ht⟩ ∈ Ebar :=
      Subgroup.mem_map.mpr ⟨⟨t, hT1S ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    rw [hbot] at hmem
    have hzero : QuotientGroup.mk (⟨t, hT1S ht⟩ : ↥S) =
        (1 : ↥S ⧸ Subgroup.center ↥S) := by
      apply θ.injective
      simpa [ψS] using hmem
    have hcenter : (⟨t, hT1S ht⟩ : ↥S) ∈ Subgroup.center ↥S :=
      (QuotientGroup.eq_one_iff (⟨t, hT1S ht⟩ : ↥S)).mp hzero
    exact Subgroup.mem_map.mpr ⟨⟨t, hT1S ht⟩, hcenter, rfl⟩
  let W : Subgroup ↥U := Ebar.comap (LargeEvenProjMk U)
  have hEbar_le : Ebar ≤ (LargeEvenProjMk U).range := by
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact le_top
  obtain ⟨P0, hP0_2, hP0_map, hP0_inj⟩ :=
    CFSG.GroupTheory.exists_isPGroup_map_eq_of_odd hodd hEbar_le hEbar_2
  have hK0_le_W : (LargeEvenProjMk U).ker ≤ W := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mpr hx]
    exact Ebar.one_mem
  have hP0_le_W : P0 ≤ W := by
    intro p hp
    rw [Subgroup.mem_comap]
    rw [← hP0_map]
    exact Subgroup.mem_map_of_mem (LargeEvenProjMk U) hp
  let A : Subgroup ↥W := (LargeEvenProjMk U).ker.subgroupOf W
  have hAcenter : A ≤ Subgroup.center ↥W := by
    have hker_center : (LargeEvenProjMk U).ker ≤ Subgroup.center ↥U := by
      rw [show (LargeEvenProjMk U).ker =
        (LargeEvenScalars (Fin d) F).subgroupOf U from QuotientGroup.ker_mk' _]
      exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center U
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker_center (Subgroup.mem_subgroupOf.mp ha))
      ((w : ↥W) : ↥U)
  have hAodd : Odd (Nat.card A) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0_le_W).toEquiv]
    exact hodd
  have hW_eq : W = P0 ⊔ (LargeEvenProjMk U).ker := by
    change Ebar.comap (LargeEvenProjMk U) = P0 ⊔ (LargeEvenProjMk U).ker
    rw [← hP0_map, Subgroup.comap_map_eq]
  have hsup : P0.subgroupOf W ⊔ A = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hP0_le_W hK0_le_W]
    rw [← hW_eq, Subgroup.subgroupOf_self]
  have hdisj0 : Disjoint P0 (LargeEvenProjMk U).ker := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP0_2
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  have hdisj : Disjoint (P0.subgroupOf W) A := by
    rw [Subgroup.disjoint_def]
    intro x hxP hxA
    have hxP' : ((x : ↥W) : ↥U) ∈ P0 := Subgroup.mem_subgroupOf.mp hxP
    have hxA' : ((x : ↥W) : ↥U) ∈ (LargeEvenProjMk U).ker :=
      Subgroup.mem_subgroupOf.mp hxA
    have hx1 : ((x : ↥W) : ↥U) = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hdisj0.eq_bot]
      exact ⟨hxP', hxA'⟩
    exact Subtype.ext hx1
  have hA_normal : A.Normal := by
    change ((LargeEvenProjMk U).ker.subgroupOf W).Normal
    infer_instance
  have hprod : (↑(P0.subgroupOf W) : Set ↥W) * (A : Set ↥W) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro w
    have hw : w ∈ P0.subgroupOf W ⊔ A := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨p, hp, a, ha, hpa⟩ := (Subgroup.mem_sup_of_normal_right).mp hw
    exact ⟨p, hp, a, ha, hpa⟩
  have hcomp : (P0.subgroupOf W).IsComplement' A :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hprod
  have hAindex : A.index = Nat.card P0 := by
    rw [hcomp.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0_le_W).toEquiv]
  have hAindex_pow : ∃ n : ℕ, A.index = 2 ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP0_2
    exact ⟨n, hAindex.trans hn⟩
  have hcop : Nat.Coprime (Nat.card A) A.index := by
    obtain ⟨n, hn⟩ := hAindex_pow
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hAodd)
  obtain ⟨K, hKchar, hKcard, hKcomp, hKsup, hKinf, hKcomm, hKcommut, hKuniq, hKmem,
    hKequiv⟩ := CFSG.Semidihedral.central_hall_subgroup_direct_complement A hAcenter hcop
  have hK2 : IsPGroup 2 K := by
    obtain ⟨n, hn⟩ := hAindex_pow
    exact IsPGroup.of_card (hKcard.trans hn)
  have hKne : K ≠ ⊥ := by
    intro hbot
    have hcomp' : A.IsComplement' (⊥ : Subgroup ↥W) := by simpa [hbot] using hKcomp
    have hAtop : A = ⊤ := Subgroup.isComplement'_bot_right.mp hcomp'
    have hP0ker : P0 ≤ (LargeEvenProjMk U).ker := by
      intro p hp
      have hpW : p ∈ W := hP0_le_W hp
      have hpA : (⟨p, hpW⟩ : ↥W) ∈ A := by
        rw [hAtop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hpA
    have hP0bot : P0 = ⊥ := by
      rw [eq_bot_iff]
      intro p hp
      have hpker : p ∈ (LargeEvenProjMk U).ker := hP0ker hp
      have hmem : p ∈ (⊥ : Subgroup ↥U) := by
        rw [← hdisj0.eq_bot]
        exact ⟨hp, hpker⟩
      exact Subgroup.mem_bot.mp hmem
    have hEbarBot : Ebar = ⊥ := by
      rw [← hP0_map, hP0bot, Subgroup.map_bot]
    exact hEbar_ne hEbarBot
  let T : Subgroup (GL (Fin d) F) := K.map (U.subtype.comp W.subtype)
  have hTU : T ≤ U := by
    rintro _ ⟨k, hk, rfl⟩
    exact ((k : ↥W) : ↥U).2
  have hT2 : IsPGroup 2 T := hK2.map (U.subtype.comp W.subtype)
  have hTne : T ≠ ⊥ := by
    intro hbot
    apply hKne
    have hinj : Function.Injective ((U.subtype.comp W.subtype)) :=
      U.subtype_injective.comp W.subtype_injective
    have hcardT : Nat.card T = Nat.card K := Subgroup.card_map_of_injective hinj
    rw [hbot, Subgroup.card_bot] at hcardT
    exact Subgroup.eq_bot_of_card_eq K hcardT.symm
  have hEbar_phi : ∀ (M : GL (Fin d) F) (hM : M ∈ Gh),
      ∃ b ∈ B, GInduced θ b M := fun M hM => hGh M hM
  have hAWmem : ∀ (M : GL (Fin d) F) (hM : M ∈ Gh) (u : ↥U), u ∈ W →
      (⟨M * (u : GL (Fin d) F) * M⁻¹,
        mem_normalizer_conj (hGhN hM) u.2⟩ : ↥U) ∈ W := by
    intro M hM u hu
    obtain ⟨b, hb, hind⟩ := hEbar_phi M hM
    obtain ⟨φ, hφg, hφi⟩ := hind
    have hBT' : b ∈ Subgroup.normalizer (T1 : Set Ω) := hBT hb
    have hphi_mem : ∀ y ∈ Ebar, φ y ∈ Ebar := by
      rintro y ⟨t, ht, rfl⟩
      have htT : (t : Ω) ∈ T1 := Subgroup.mem_subgroupOf.mp ht
      have hmemT : b⁻¹ * (t : Ω) * b ∈ T1 := by
        simpa only [inv_inv] using mem_normalizer_conj (inv_mem hBT') htT
      let t' : ↥S := ⟨b⁻¹ * (t : Ω) * b, hT1S hmemT⟩
      have h' : φ (ψS t) = ψS t' := hφi t t' rfl
      rw [h']
      exact Subgroup.mem_map.mpr ⟨t', Subgroup.mem_subgroupOf.mpr hmemT, rfl⟩
    have hmem : LargeEvenProjMk U u ∈ Ebar := hu
    have h1 : φ (LargeEvenProjMk U u) ∈ Ebar := hphi_mem _ hmem
    have h2 : φ (LargeEvenProjMk U u) =
        LargeEvenProjMk U ⟨M * (u : GL (Fin d) F) * M⁻¹,
          mem_normalizer_conj (hGhN hM) u.2⟩ :=
      hφg u ⟨M * (u : GL (Fin d) F) * M⁻¹, mem_normalizer_conj (hGhN hM) u.2⟩ rfl
    rwa [h2] at h1
  have hTinv : ∀ M ∈ Gh, ∀ t ∈ T, M * t * M⁻¹ ∈ T := by
    intro M hM t ht
    let conjM : ↥U →* ↥U :=
      { toFun := fun u => ⟨M * (u : GL (Fin d) F) * M⁻¹,
          mem_normalizer_conj (hGhN hM) u.2⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun u v => by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          group }
    have hconjM_inj : Function.Injective conjM := by
      intro u v huv
      apply Subtype.ext
      have h := congrArg (fun x : ↥U => (x : GL (Fin d) F)) huv
      simpa only [conjM, MonoidHom.coe_mk, OneHom.coe_mk] using
        (mul_left_cancel (a := M) (mul_right_cancel (b := M⁻¹) h))
    have hmap_le : K.map (conjM.comp W.subtype) ≤ W := by
      rintro _ ⟨k, hk, rfl⟩
      exact hAWmem M hM (k : ↥U) k.2
    have hcard_map : Nat.card ((K.map (conjM.comp W.subtype)).subgroupOf W) = A.index := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmap_le).toEquiv,
        Subgroup.card_map_of_injective (by
          intro a b hab
          apply W.subtype_injective
          exact hconjM_inj hab), hKcard]
    have huniq := hKuniq _ hcard_map
    have hmap_eq : K.map (conjM.comp W.subtype) = K.map W.subtype := by
      conv_rhs => rw [← huniq]
      rw [Subgroup.map_subgroupOf_eq_of_le hmap_le]
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp ht
    have hmemU : conjM (k : ↥U) ∈ K.map W.subtype := by
      rw [← hmap_eq]
      exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    have hT_eq : (K.map W.subtype).map U.subtype = T := by
      rw [Subgroup.map_map]
    have hmemT : ((conjM (k : ↥U) : ↥U) : GL (Fin d) F) ∈ T := by
      rw [← hT_eq]
      exact Subgroup.mem_map.mpr ⟨conjM (k : ↥U), hmemU, rfl⟩
    simpa [conjM] using hmemT
  have hKT : ∀ M ∈ Gh, M ∈ Subgroup.normalizer (T : Set (GL (Fin d) F)) := by
    intro M hM
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro t
    constructor
    · intro ht
      exact hTinv M hM t ht
    · intro ht
      have h1 := hTinv M⁻¹ (Gh.inv_mem hM) (M * t * M⁻¹) ht
      simpa [mul_assoc] using h1
  exact ⟨T, hT2, hTne, hTU, hKT⟩

theorem gen_psi_props {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hS : CFSG.Open.IsQuasisimple ↥S) {d : ℕ} {F : Type} [Field F] [Finite F]
    {U : Subgroup (GL (Fin d) F)} (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj U)
    (ψ : ↥U →* ↥S) (hψ : GLifts θ ψ) :
    Function.Surjective ψ ∧
      ∀ u : ↥U, ψ u = 1 → (u : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
  classical
  let Z : Subgroup ↥S := Subgroup.center ↥S
  let πU : ↥U →* LargeEvenProj U := LargeEvenProjMk U
  let πS : ↥S →* (↥S ⧸ Z) := QuotientGroup.mk' Z
  have hcomp : πS.comp ψ = (θ.symm : LargeEvenProj U ≃* (↥S ⧸ Z)).toMonoidHom.comp πU := by
    ext u
    apply θ.injective
    simpa [πS, πU] using hψ u
  have hsurj : Function.Surjective (πS.comp ψ) := by
    rw [hcomp]
    exact (θ.symm.surjective).comp (QuotientGroup.mk'_surjective _)
  have hrange : ψ.range.map πS = ⊤ := by
    rw [← MonoidHom.range_comp]
    exact MonoidHom.range_eq_top.mpr hsurj
  have hZmap : Z.map πS = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro z hz
    exact (QuotientGroup.eq_one_iff (N := Z) z).mpr hz
  have htop : ψ.range ⊔ Z = ⊤ := by
    have h1 : (ψ.range ⊔ Z).map πS = ⊤ := by
      rw [Subgroup.map_sup, hrange, hZmap, sup_bot_eq]
    have h2 := congrArg (Subgroup.comap πS) h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top, sup_assoc,
      sup_idem] at h2
  have htopsub : (⊤ : Subgroup ↥S) ≤ ψ.range := by
    rw [← hS.1]
    calc ⁅(⊤ : Subgroup ↥S), ⊤⁆ = ⁅ψ.range ⊔ Z, ψ.range ⊔ Z⁆ := by rw [htop]
      _ ≤ ψ.range := commutator_sup_center_le le_rfl
  have hsurjψ : Function.Surjective ψ :=
    MonoidHom.range_eq_top.mp (eq_top_iff.mpr htopsub)
  refine ⟨hsurjψ, ?_⟩
  intro u hu
  have h1 : πU u = 1 := by
    simpa [πU, hu] using (hψ u).symm
  have hmem : u ∈ (LargeEvenProjMk U).ker := MonoidHom.mem_ker.mpr h1
  rw [show (LargeEvenProjMk U).ker =
      (LargeEvenScalars (Fin d) F).subgroupOf U from QuotientGroup.ker_mk' _] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

theorem gen_equivariance {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {d : ℕ} {F : Type}
    [Field F] [Finite F] {U : Subgroup (GL (Fin d) F)} (hU : Group.IsPerfect ↥U)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj U) (ψ : ↥U →* ↥S) (hψ : GLifts θ ψ)
    {b : Ω} (hb : b ∈ Subgroup.normalizer (S : Set Ω)) {A : GL (Fin d) F}
    (hAN : A ∈ Subgroup.normalizer (U : Set (GL (Fin d) F))) (hA : GInduced θ b A) :
    GActs ψ b A := by
  classical
  obtain ⟨φ, hφg, hφi⟩ := hA
  let f₁ : ↥U →* ↥S :=
    { toFun := fun u => ψ ⟨A * (u : GL (Fin d) F) * A⁻¹, mem_normalizer_conj hAN u.2⟩
      map_one' := by
        apply Subtype.ext
        show (ψ ⟨A * 1 * A⁻¹, _⟩ : Ω) = 1
        rw [show (⟨A * 1 * A⁻¹, _⟩ : ↥U) = 1 by
          apply Subtype.ext
          simp]
        simp
      map_mul' := fun u v => by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  let f₂ : ↥U →* ↥S :=
    { toFun := fun u => ⟨b⁻¹ * (ψ u : Ω) * b,
        by
          simpa only [inv_inv] using
            mem_normalizer_conj ((Subgroup.normalizer (S : Set Ω)).inv_mem hb) (ψ u).2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun u v => by
        apply Subtype.ext
        show b⁻¹ * (ψ (u * v) : Ω) * b =
          (b⁻¹ * (ψ u : Ω) * b) * (b⁻¹ * (ψ v : Ω) * b)
        rw [map_mul]
        simp only [Subgroup.coe_mul]
        group }
  have hmod : ∀ u : ↥U, (f₁ u)⁻¹ * f₂ u ∈ Subgroup.center ↥S := by
    intro u
    have hπ : QuotientGroup.mk' (Subgroup.center ↥S) (f₁ u) =
        QuotientGroup.mk' (Subgroup.center ↥S) (f₂ u) := by
      apply θ.injective
      change θ (QuotientGroup.mk (f₁ u)) = θ (QuotientGroup.mk (f₂ u))
      have h1 : θ (QuotientGroup.mk (f₁ u)) =
          LargeEvenProjMk U ⟨A * (u : GL (Fin d) F) * A⁻¹,
            mem_normalizer_conj hAN u.2⟩ := hψ _
      have h2 : θ (QuotientGroup.mk (f₂ u)) = φ (LargeEvenProjMk U u) := by
        have h := hφi (ψ u) (f₂ u) rfl
        rw [hψ u] at h
        exact h.symm
      have h3 : φ (LargeEvenProjMk U u) =
          LargeEvenProjMk U ⟨A * (u : GL (Fin d) F) * A⁻¹,
            mem_normalizer_conj hAN u.2⟩ :=
        hφg u ⟨A * (u : GL (Fin d) F) * A⁻¹, mem_normalizer_conj hAN u.2⟩ rfl
      rw [h1, h2, h3]
    have hmem : (f₁ u)⁻¹ * f₂ u ∈
        (QuotientGroup.mk' (Subgroup.center ↥S)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, inv_mul_cancel]
    rw [QuotientGroup.ker_mk'] at hmem
    exact hmem
  have hf : f₁ = f₂ := hom_eq_of_inv_mul_mem_center hU hmod
  intro u u' hu'
  have heq : f₁ u = f₂ u := DFunLike.congr_fun hf u
  rw [show u' = ⟨A * (u : GL (Fin d) F) * A⁻¹, mem_normalizer_conj hAN u.2⟩ by
    exact Subtype.ext hu']
  change (f₁ u : Ω) = b⁻¹ * (ψ u : Ω) * b
  rw [heq]
  rfl

end CFSG.LocalAnalysis.GLTheoremA.T173A

end

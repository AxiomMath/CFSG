module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMCfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMGhat
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMModel
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped commutatorElement MatrixGroups

private theorem gacts_mul {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type} [Field F]
    {U : Subgroup (GL (Fin d) F)} {ψ : ↥U →* ↥S} {b₁ b₂ : Ω} {A₁ A₂ : GL (Fin d) F}
    (hA₁ : A₁ ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)))
    (hA₂ : A₂ ∈ Subgroup.normalizer (U : Set (GL (Fin d) F)))
    (h₁ : GActs ψ b₁ A₁) (h₂ : GActs ψ b₂ A₂) (hb : b₁ * b₂ = b₂ * b₁) :
    GActs ψ (b₁ * b₂) (A₁ * A₂) := by
  intro u u' hu'
  have hu₂ : A₂ * (u : GL (Fin d) F) * A₂⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp hA₂ (u : GL (Fin d) F)).mp u.2
  let u₂ : ↥U := ⟨A₂ * (u : GL (Fin d) F) * A₂⁻¹, hu₂⟩
  have h₂' : (ψ u₂ : Ω) = b₂⁻¹ * (ψ u : Ω) * b₂ := h₂ u u₂ rfl
  have hu₁ : A₁ * (u₂ : GL (Fin d) F) * A₁⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp hA₁ (u₂ : GL (Fin d) F)).mp u₂.2
  let u₁ : ↥U := ⟨A₁ * (u₂ : GL (Fin d) F) * A₁⁻¹, hu₁⟩
  have h₁' : (ψ u₁ : Ω) = b₁⁻¹ * (ψ u₂ : Ω) * b₁ := h₁ u₂ u₁ rfl
  have hu'_eq : u' = u₁ := by
    apply Subtype.ext
    show (u' : GL (Fin d) F) = A₁ * (u₂ : GL (Fin d) F) * A₁⁻¹
    rw [show (u₂ : GL (Fin d) F) = A₂ * (u : GL (Fin d) F) * A₂⁻¹ from rfl, hu']
    group
  rw [hu'_eq, h₁', h₂', hb]
  group

private theorem gacts_inv {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type} [Field F]
    {U : Subgroup (GL (Fin d) F)} {ψ : ↥U →* ↥S} {b : Ω} {A : GL (Fin d) F}
    (hA : A ∈ Subgroup.normalizer (U : Set (GL (Fin d) F))) (h : GActs ψ b A) :
    GActs ψ b⁻¹ A⁻¹ := by
  intro u u' hu'
  have huu' : (u : GL (Fin d) F) = A * (u' : GL (Fin d) F) * A⁻¹ := by
    rw [hu']
    group
  have h1 : (ψ u : Ω) = b⁻¹ * (ψ u' : Ω) * b := h u' u huu'
  rw [h1]
  group

private theorem gacts_pow {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type} [Field F]
    {U : Subgroup (GL (Fin d) F)} {ψ : ↥U →* ↥S} {b : Ω} {A : GL (Fin d) F}
    (hA : A ∈ Subgroup.normalizer (U : Set (GL (Fin d) F))) (h : GActs ψ b A) :
    ∀ k : ℕ, GActs ψ (b ^ k) (A ^ k) := by
  intro k
  induction k with
  | zero =>
      intro u u' hu'
      have : u' = u := Subtype.ext (by simpa using hu')
      subst this
      simp
  | succ k ih =>
      have hb : b ^ k * b = b * b ^ k := by rw [← pow_succ, ← pow_succ']
      have h' := gacts_mul (Subgroup.pow_mem _ hA k) hA ih h hb
      simpa [pow_succ] using h'

private theorem exists_nat_pow_eq_of_mem_zpowers {G : Type*} [Group G] {g h : G} {n : ℕ}
    (hn : 0 < n) (hg : g ^ n = 1) (hh : h ∈ Subgroup.zpowers g) : ∃ k : ℕ, g ^ k = h := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hh
  refine ⟨(m % (n : ℤ)).toNat, ?_⟩
  have h1 : g ^ (m % (n : ℤ)) = h := by
    rw [← hm]
    exact (zpow_eq_zpow_emod' m hg).symm
  have h2 : ((m % (n : ℤ)).toNat : ℤ) = m % (n : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg m (by exact_mod_cast hn.ne'))
  rw [← zpow_natCast, h2]
  exact h1

theorem uni_K_shape {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} (hcfg : MCfg p S B N D K x) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hpd : p ∣ d)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))
    (ψ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥S) (hψ : GLifts θ ψ) (P : GL (Fin d) F)
    (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) (hB : ∀ b ∈ B, GDiagAct p ψ P b)
    {Gh : Subgroup (GL (Fin d) F)}
    (hGh : ∀ A, A ∈ Gh ↔ A ∈ MGU n d F ∧ ∃ b ∈ B, GInduced θ b A)
    (hmark : UniMarking p S B n d F θ) (hdiag : MDiagAt d F P Gh) :
    ∃ I : Finset (Fin d), 2 ≤ I.card ∧ (I.card ≤ 3 → 2 ≤ n) ∧
      (∀ k : Ω, k ∈ K ↔ ∃ u : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)),
        (P * (u : GL (Fin d) F) * P⁻¹) ∈ UniBlockSet n d F I ∧ (ψ u : Ω) = k) ∧
      ∃ A₀ ∈ Gh, (∃ i₀ ∈ I, ∀ i, i ∈ I ↔ MWt P A₀ i = MWt P A₀ i₀) ∧
        (∀ A ∈ Gh, (∀ i ∈ I, ∀ j ∈ I, MWt P A i = MWt P A j) →
          ∃ (c : Fˣ) (k : ℕ), A = Matrix.GeneralLinearGroup.scalar (Fin d) c * A₀ ^ k) ∧
        (2 ≤ n → ∀ i j : Fin d, i ∉ I → j ∉ I → i ≠ j → MWt P A₀ i ≠ MWt P A₀ j) := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  subst d
  have hp : p.Prime := hcfg.prime
  have hp2 : p ≠ 2 := hcfg.odd
  have hdn : m + 1 = 3 → 2 ≤ n := hmark.2.2.2.1
  have hpq : p ∣ 2 ^ n + 1 := hmark.2.2.2.2.1
  have hBN : B ≤ Subgroup.normalizer (S : Set Ω) := hmark.2.2.2.2.2.1
  obtain ⟨hperfU, hcen, hZc, hoddker⟩ :=
    uni_model_facts (n := n) (d := m + 1) (F := F) hF hn hd hdn
  obtain ⟨hGUiff, hGUN, hGUs, hSUGU⟩ := uni_GU_facts (n := n) (d := m + 1) (F := F) hF
  obtain ⟨hψS, hψker⟩ := gen_psi_props hcfg.qs θ ψ hψ
  have hact : ∀ b ∈ B, ∃ A ∈ MGU n (m + 1) F, GInduced θ b A := by
    intro b hb
    obtain ⟨φ, ⟨A, hAGU, hAφ⟩, hInd⟩ := hmark.2.2.2.2.2.2 b hb
    exact ⟨A, (hGUiff A).2 hAGU, φ, hAφ, hInd⟩
  obtain ⟨Gh', hGh'V, hGh'iff, hscGh', hel', hcard'⟩ :=
    gen_ghat hcfg θ (MGU n (m + 1) F) hGUs hGUN hcen hact
  have hGh_eq : Gh' = Gh := by ext A; rw [hGh'iff A, hGh A]
  have hcard : p * (LargeEvenScalars (Fin (m + 1)) F).relIndex Gh = Nat.card B := by
    rw [← hGh_eq]; exact hcard'
  obtain ⟨y, hyD, hyx⟩ := S171.exists_y hp hcfg.ne_one hcfg.std
  have hyB : y ∈ B := hcfg.std.1 hyD
  have hSx : S ≤ Subgroup.centralizer ({x} : Set Ω) := by
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp
        ((hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)) s hs)
  have hcs : S ⊓ Subgroup.centralizer (D : Set Ω) =
      S ⊓ Subgroup.centralizer ({y} : Set Ω) :=
    S171.L_cs_eq hp hcfg.ne_one hcfg.std hyD hyx hSx
  have hKcomp : CFSG.Assembly.IsComponentOf K
      (S ⊓ Subgroup.centralizer ({y} : Set Ω)) :=
    (CFSG.Assembly.isComponentOf_iff_open).mpr (by
      rw [← hcs]; exact hcfg.std.2.2.2.2.2.1)
  obtain ⟨Ay, hAyMGU, hAyInd⟩ := hact y hyB
  have hAyGh : Ay ∈ Gh := (hGh Ay).2 ⟨hAyMGU, y, hyB, hAyInd⟩
  obtain ⟨Dfun, hDfun⟩ := hdiag Ay hAyGh
  have hPMGU : P ∈ MGU n (m + 1) F := (hGUiff P).2 hP
  have hPN : P ∈ Subgroup.normalizer
      ((LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n) : Subgroup (GL (Fin (m + 1)) F)) :
        Set (GL (Fin (m + 1)) F)) :=
    hGUN hPMGU
  have hPNinv : P⁻¹ ∈ Subgroup.normalizer
      ((LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n) : Subgroup (GL (Fin (m + 1)) F)) :
        Set (GL (Fin (m + 1)) F)) :=
    Subgroup.inv_mem _ hPN
  let cP : MulAut ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n)) :=
    (LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n)).normalizerMonoidHom ⟨P⁻¹, hPNinv⟩
  let ψP : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n)) →* ↥S := ψ.comp cP.toMonoidHom
  let ψΩ : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n)) →* Ω := S.subtype.comp ψP
  have hcP : ∀ u : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n)),
      ((cP u : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n))) : GL (Fin (m + 1)) F) =
        P⁻¹ * (u : GL (Fin (m + 1)) F) * P := by
    intro u
    exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hDne : ∀ i, Dfun i ≠ 0 := by
    intro i hi
    have hdetne : (((P * Ay * P⁻¹ : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F).det) ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero (P * Ay * P⁻¹)
    apply hdetne
    rw [hDfun, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  let δ : Fin (m + 1) → Fˣ := fun i => (Units.mk0 (Dfun i) (hDne i))⁻¹
  have hDδ : CFSG.SectionRank.OddCover.diagHom (m + 1) δ =
      (P * Ay * P⁻¹ : GL (Fin (m + 1)) F)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    apply Units.ext
    ext i j
    simp only [Units.val_mul, Units.val_one]
    rw [← Units.val_mul, ← Units.val_mul, hDfun]
    simp only [CFSG.SectionRank.OddCover.coe_diagHom]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_mul, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      show Dfun i * (((Units.mk0 (Dfun i) (hDne i))⁻¹ : Fˣ) : F) = 1
      calc Dfun i * (((Units.mk0 (Dfun i) (hDne i))⁻¹ : Fˣ) : F)
          = ((Units.mk0 (Dfun i) (hDne i) : Fˣ) : F) *
            (((Units.mk0 (Dfun i) (hDne i))⁻¹ : Fˣ) : F) := rfl
        _ = (((Units.mk0 (Dfun i) (hDne i)) * (Units.mk0 (Dfun i) (hDne i))⁻¹ : Fˣ) : F) := by
              rw [Units.val_mul]
        _ = 1 := by
          simpa using Units.mul_inv (Units.mk0 (Dfun i) (hDne i))
    · simp [Matrix.diagonal_mul, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hDnorm : (P * Ay * P⁻¹ : GL (Fin (m + 1)) F) ∈
      Subgroup.normalizer ((LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n) :
        Subgroup (GL (Fin (m + 1)) F)) : Set (GL (Fin (m + 1)) F)) :=
    hGUN ((MGU n (m + 1) F).mul_mem ((MGU n (m + 1) F).mul_mem hPMGU hAyMGU)
      ((MGU n (m + 1) F).inv_mem hPMGU))
  have hAyN : Ay ∈ Subgroup.normalizer
      ((LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n) :
        Subgroup (GL (Fin (m + 1)) F)) : Set (GL (Fin (m + 1)) F)) :=
    hGUN hAyMGU
  have hAyinvN : Ay⁻¹ ∈ Subgroup.normalizer
      ((LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n) :
        Subgroup (GL (Fin (m + 1)) F)) : Set (GL (Fin (m + 1)) F)) :=
    Subgroup.inv_mem _ hAyN
  have hyN : y ∈ Subgroup.normalizer (S : Set Ω) := hBN hyB
  have hAyActs : GActs ψ y Ay := gen_equivariance hperfU θ ψ hψ hyN hAyN hAyInd
  have hkerψ : ψΩ.ker ≤ Subgroup.center ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n)) := by
    intro u hu
    have hu' : ψ (cP u) = 1 :=
      Subgroup.subtype_injective S (by simpa [ψΩ, ψP, MonoidHom.comp_apply] using hu)
    have hscal : ((cP u : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n))) :
        GL (Fin (m + 1)) F) ∈ LargeEvenScalars (Fin (m + 1)) F := hψker (cP u) hu'
    have hcent : ((cP u : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n))) :
        GL (Fin (m + 1)) F) ∈ Subgroup.center (GL (Fin (m + 1)) F) :=
      CFSG.StandardType.TableB.scalars_le_center hscal
    rw [Subgroup.mem_center_iff]
    intro v
    apply cP.injective
    rw [map_mul, map_mul]
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcent
      (cP v : GL (Fin (m + 1)) F))
  have hrange : ψΩ.range = S := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact (ψ (cP u)).2
    · intro hz
      obtain ⟨u, hu⟩ := hψS ⟨z, hz⟩
      refine ⟨cP.symm u, ?_⟩
      have h1 : ψP (cP.symm u) = ψ u := by simp [ψP, MonoidHom.comp_apply]
      show S.subtype (ψP (cP.symm u)) = z
      rw [h1]
      exact congrArg Subtype.val hu
  have hJ : CFSG.Assembly.IsComponentOf K
      (ψΩ.range ⊓ Subgroup.centralizer ({y} : Set Ω)) := by
    rw [hrange]; exact hKcomp
  have hsups : (y, (P * Ay * P⁻¹ : GL (Fin (m + 1)) F)⁻¹) ∈
      CFSG.StandardType.SUTorus.suPairs ψΩ := by
    refine ⟨Subgroup.inv_mem _ hDnorm, ?_⟩
    intro u v hv
    let w : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n)) :=
      ⟨Ay⁻¹ * (cP u : GL (Fin (m + 1)) F) * Ay,
        (Subgroup.mem_normalizer_iff.mp hAyinvN (cP u)).mp (cP u).2⟩
    have hw : (w : GL (Fin (m + 1)) F) =
        Ay⁻¹ * (cP u : GL (Fin (m + 1)) F) * Ay := rfl
    have hvw : cP v = w := by
      apply Subtype.ext
      rw [hcP v, hw]
      have hv' : (v : GL (Fin (m + 1)) F) =
          (P * Ay * P⁻¹ : GL (Fin (m + 1)) F)⁻¹ * (u : GL (Fin (m + 1)) F) *
            (P * Ay * P⁻¹ : GL (Fin (m + 1)) F) := by simpa using hv
      calc P⁻¹ * (v : GL (Fin (m + 1)) F) * P
          = P⁻¹ * ((P * Ay * P⁻¹ : GL (Fin (m + 1)) F)⁻¹ * (u : GL (Fin (m + 1)) F) *
              (P * Ay * P⁻¹ : GL (Fin (m + 1)) F)) * P := by rw [hv']
        _ = Ay⁻¹ * (P⁻¹ * (u : GL (Fin (m + 1)) F) * P) * Ay := by group
        _ = Ay⁻¹ * (cP u : GL (Fin (m + 1)) F) * Ay := by rw [hcP u]
    have h1 : ((cP u : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n))) :
        GL (Fin (m + 1)) F) = Ay * (w : GL (Fin (m + 1)) F) * Ay⁻¹ := by
      rw [hw]; group
    have hGA := hAyActs w (cP u) h1
    have hψu : (ψΩ u : Ω) = (ψ (cP u) : Ω) := rfl
    have hψv : (ψΩ v : Ω) = (ψ w : Ω) := by rw [← hvw]; rfl
    change y * (ψΩ u : Ω) * y⁻¹ = (ψΩ v : Ω)
    rw [hψu, hψv]
    calc y * (ψ (cP u) : Ω) * y⁻¹
        = y * (y⁻¹ * (ψ w : Ω) * y) * y⁻¹ := by rw [hGA]
      _ = (ψ w : Ω) := by group
  have hsups' : (y, CFSG.SectionRank.OddCover.diagHom (m + 1) δ) ∈
      CFSG.StandardType.SUTorus.suPairs ψΩ := by
    rw [hDδ]; exact hsups
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, hn, by rw [hF, ← pow_mul, Nat.mul_comm]⟩
  obtain ⟨i, hKi⟩ := CFSG.StandardType.SUTorus.exists_le_map_blockSU
    (f := n) (K := F) (m := m) (G := Ω) hUF hp hpq (ψ := ψΩ) hkerψ
    (S := ({y} : Set Ω)) (δ := fun _ => δ) (by
      intro e he
      rw [Set.mem_singleton_iff] at he
      subst he
      exact hsups') hJ
  set I : Finset (Fin (m + 1)) :=
    CFSG.StandardType.LinTorus.diagClass ({y} : Set Ω) (fun _ => δ) i with hIdef
  have hKiI : K ≤ (CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) I).map ψΩ := hKi
  have hI2 : 2 ≤ I.card := by
    by_contra hlt
    push Not at hlt
    have hle1 : I.card ≤ 1 := by omega
    haveI : Nonempty (Fin (m + 1)) := ⟨⟨0, by omega⟩⟩
    obtain ⟨i₀, hi₀⟩ := Finset.card_le_one_iff_subset_singleton.mp hle1
    have hsub : CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) I ≤
        CFSG.StandardType.TableBUE.blockSU (K := F) (n := n)
          ({i₀} : Finset (Fin (m + 1))) :=
      CFSG.StandardType.SUTorus.blockSU_mono hi₀
    have hbot : CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) I = ⊥ := by
      apply le_bot_iff.mp
      rw [← CFSG.StandardType.SUTorus.blockSU_singleton (f := n) (K := F) hUF i₀]
      exact hsub
    have hmapped : (CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) I).map ψΩ = ⊥ := by
      rw [hbot]
      exact Subgroup.map_bot ψΩ
    have hKne : K ≠ ⊥ := by
      intro hbotK
      have h1 : ⁅K, K⁆ = ⊥ := by rw [hbotK, Subgroup.commutator_bot_left]
      exact CFSG.StandardType.commutator_ne_bot_of_isQuasisimple hKcomp.2.2 h1
    exact hKne (le_bot_iff.mp (hKiI.trans (le_of_eq hmapped)))
  have hI3 : I.card ≤ 3 → 2 ≤ n := by
    intro hIcard
    by_contra hn2
    push Not at hn2
    have hn1 : n = 1 := by omega
    subst hn1
    have hk1 : 1 ≤ I.card :=
      Finset.card_pos.mpr ⟨i, by
        rw [hIdef]
        exact CFSG.StandardType.LinTorus.self_mem_diagClass _ _ _⟩
    haveI : Group.IsSolvable ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F I.card) :=
      CFSG.StandardType.WitSU.isSolvable_unitarySU_two_one hUF hk1 hIcard
    let e := CFSG.StandardType.TableBUE.blockSUEquiv (K := F) (n := 1) I hUF
    haveI : Group.IsSolvable ↥(CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I) :=
      Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom)
        (fun x y h => e.symm.injective h)
    have hsolvI : Group.IsSolvable
        ↥((CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I).map ψΩ) := by
      have hres : Group.IsSolvable
          ↥((ψΩ.comp (CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I).subtype).range) :=
        Group.isSolvable_of_surjective
          (f := (ψΩ.comp
            (CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I).subtype).rangeRestrict)
          (MonoidHom.rangeRestrict_surjective _)
      have hrange_eq : (ψΩ.comp
          (CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I).subtype).range =
            (CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I).map ψΩ := by
        ext x
        constructor
        · rintro ⟨u, rfl⟩
          exact Subgroup.mem_map.mpr
            ⟨((CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I).subtype u :
              ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ 1))), u.2, rfl⟩
        · rintro ⟨u, hu, rfl⟩
          exact ⟨⟨u, hu⟩, rfl⟩
      exact hrange_eq ▸ hres
    haveI := hsolvI
    exact CFSG.StandardType.LinSemisimple.false_of_isQuasisimple_of_le_isSolvable
      hKcomp.2.2 hKiI
  have hδconst : ∀ a ∈ I, ∀ b ∈ I, δ a = δ b := by
    intro a ha b hb
    have ha' : a ∈ CFSG.StandardType.LinTorus.diagClass ({y} : Set Ω) (fun _ => δ) i := by
      rw [hIdef] at ha; exact ha
    have hb' : b ∈ CFSG.StandardType.LinTorus.diagClass ({y} : Set Ω) (fun _ => δ) i := by
      rw [hIdef] at hb; exact hb
    exact CFSG.StandardType.LinTorus.eq_of_mem_diagClass ha' hb' (Set.mem_singleton y)
  have hle : (CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) I).map ψΩ ≤
      S ⊓ Subgroup.centralizer ({y} : Set Ω) := by
    refine le_inf ?_ ?_
    · rw [← hrange]; exact Subgroup.map_le_range _ _
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hyc : y ∈ Subgroup.centralizer
          (((CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) I).map ψΩ :
            Subgroup Ω) : Set Ω) :=
        CFSG.StandardType.SUTorus.mem_centralizer_map_blockSU
          (K := F) (f := n) (m := m) (G := Ω) (ψ := ψΩ)
          (d := δ) (e := y) hsups' hδconst
      exact (Subgroup.mem_centralizer_iff.mp hyc) x hx
  have hq : CFSG.Assembly.IsQuasisimple
      ((CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) I).map ψΩ) := by
    by_cases hf2 : 2 ≤ n
    · exact CFSG.StandardType.SURepair.isQuasisimple_map_blockSU_of_two_le
        (f := n) (K := F) (n := m + 1) (G := Ω) hUF hf2 hkerψ hI2
    · have hn1 : n = 1 := by omega
      subst hn1
      have hI4 : 4 ≤ I.card := by
        by_contra hlt
        push Not at hlt
        exact hf2 (hI3 (by omega))
      have hq0 : CFSG.IsQuasisimple
          ↥(CFSG.StandardType.TableBUE.blockSU (K := F) (n := 1) I) :=
        CFSG.StandardType.TableBUE.isQuasisimple_blockSU I hUF hF (by omega)
          (by intro h; exact (by omega : I.card ≠ 3) (Prod.mk.inj h).1)
      exact CFSG.StandardType.SURepair.isQuasisimple_map_of_isQuasisimple hkerψ hq0
  have hKI : K = (CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) I).map ψΩ :=
    CFSG.StandardType.LinTypeAk.eq_of_isComponentOf_of_le hKcomp hKiI hle hq
  have hKfirst : ∀ k : Ω, k ∈ K ↔ ∃ u : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n)),
        (P * (u : GL (Fin (m + 1)) F) * P⁻¹) ∈ UniBlockSet n (m + 1) F I ∧
          (ψ u : Ω) = k := by
    intro k
    rw [hKI]
    constructor
    · intro hk
      obtain ⟨v, hv, hvk⟩ := Subgroup.mem_map.mp hk
      refine ⟨cP v, ?_, ?_⟩
      · have h1 : P * ((cP v : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n))) :
            GL (Fin (m + 1)) F) * P⁻¹ = (v : GL (Fin (m + 1)) F) := by
          rw [hcP v]; group
        rw [h1]
        exact ⟨v.2, fun a b hab => by
          rw [CFSG.StandardType.TableBUE.mem_blockSU.mp hv a b hab, Matrix.one_apply]⟩
      · simpa [ψΩ, ψP, MonoidHom.comp_apply] using hvk
    · rintro ⟨u, hu, huk⟩
      refine Subgroup.mem_map.mpr ⟨cP.symm u, ?_, ?_⟩
      · change CFSG.StandardType.TableBUE.IsBlockOn I
          (((cP.symm u : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n))) :
            GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
        have h1 : ((cP.symm u : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n))) :
            GL (Fin (m + 1)) F) = P * (u : GL (Fin (m + 1)) F) * P⁻¹ := by
          have hh := hcP (cP.symm u)
          rw [MulEquiv.apply_symm_apply] at hh
          rw [hh]
          group
        rw [h1]
        intro a b hab
        rw [Matrix.one_apply]
        exact hu.2 a b hab
      · have h1 : ψΩ (cP.symm u) = (ψ u : Ω) := by
          simp [ψΩ, ψP, MonoidHom.comp_apply]
        rw [h1]; exact huk
  have hMWt : ∀ a : Fin (m + 1), MWt P Ay a = Dfun a := by
    intro a
    show (((P * Ay * P⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F)) a a = Dfun a
    rw [hDfun, Matrix.diagonal_apply_eq]
  have hlev : ∃ i₀ ∈ I, ∀ a, a ∈ I ↔ MWt P Ay a = MWt P Ay i₀ := by
    refine ⟨i, ?_, ?_⟩
    · rw [hIdef]; exact CFSG.StandardType.LinTorus.self_mem_diagClass _ _ _
    · intro a
      rw [hIdef, CFSG.StandardType.LinTorus.mem_diagClass]
      constructor
      · intro ha
        have hδeq : (fun _ => δ) y a = (fun _ => δ) y i := ha y (Set.mem_singleton y)
        rw [hMWt a, hMWt i]
        have hv : (Dfun a)⁻¹ = (Dfun i)⁻¹ := by
          have h1 : (δ a : F) = (δ i : F) := congrArg Units.val hδeq
          simpa [δ] using h1
        exact inv_inj.mp hv
      · intro ha e he
        have hD : Dfun a = Dfun i := by
          rw [hMWt a, hMWt i] at ha; exact ha
        have hδeq : δ a = δ i := by
          apply Units.ext
          rw [show (δ a : F) = (Dfun a)⁻¹ from by simp [δ],
              show (δ i : F) = (Dfun i)⁻¹ from by simp [δ], hD]
        rw [Set.mem_singleton_iff] at he
        subst he
        exact hδeq
  have hDsup : D = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    have hy1 : y ≠ 1 := by
      intro hy1; exact hyx (by rw [hy1]; exact Subgroup.one_mem _)
    have hyp : y ^ p = 1 := hcfg.elem.2 y hyB
    haveI : Fact p.Prime := ⟨hp⟩
    have hordy : orderOf y = p := orderOf_eq_prime hyp hy1
    have hordx : orderOf x = p := orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one
    have hzxD : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hcfg.std.2.2.2.1
    have hzyD : Subgroup.zpowers y ≤ D := Subgroup.zpowers_le.mpr hyD
    have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      by_contra hz1
      rw [Subgroup.mem_inf] at hz
      have hdvd : orderOf z ∣ p := by
        rw [← hordy]; exact orderOf_dvd_of_mem_zpowers hz.2
      have hordz_ne : orderOf z ≠ 1 := by
        intro h1
        exact hz1 (orderOf_eq_one_iff.mp h1)
      have hordz : orderOf z = p := by
        rcases hp.eq_one_or_self_of_dvd (orderOf z) hdvd with h | h
        · exact absurd h hordz_ne
        · exact h
      have hzeq : Subgroup.zpowers z = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz.2)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hordz, hordy])
      have hyz : y ∈ Subgroup.zpowers z := by
        rw [hzeq]; exact Subgroup.mem_zpowers y
      exact hyx ((Subgroup.zpowers_le.mpr hz.1) hyz)
    have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a :=
      fun a ha b hb => IsElemAbelian.comm hcfg.std.2.1 (hzxD ha) (hzyD hb)
    have hcard_sup : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup Ω) = p ^ 2 := by
      obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
        (Subgroup.zpowers x) (Subgroup.zpowers y) hcomm
      have hcardx : Nat.card (Subgroup.zpowers x : Subgroup Ω) = p := by
        rw [Nat.card_zpowers, hordx]
      have hcardy : Nat.card (Subgroup.zpowers y : Subgroup Ω) = p := by
        rw [Nat.card_zpowers, hordy]
      rw [hcardx, hcardy, hinf, Subgroup.card_bot, mul_one] at h1
      simpa [pow_two] using h1
    exact (Subgroup.eq_of_le_of_card_ge (sup_le hzxD hzyD)
      (by rw [hcfg.std.2.2.1, hcard_sup])).symm
  have hconst : ∀ A ∈ Gh, (∀ a ∈ I, ∀ b ∈ I, MWt P A a = MWt P A b) →
      ∃ (c : Fˣ) (k : ℕ),
        A = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c * Ay ^ k := by
    intro A hAGh hAconst
    obtain ⟨hAMGU, b, hbB, hAInd⟩ := (hGh A).1 hAGh
    obtain ⟨DA, hDA⟩ := hdiag A hAGh
    have hDAne : ∀ a, DA a ≠ 0 := by
      intro a ha
      apply Matrix.GeneralLinearGroup.det_ne_zero (P * A * P⁻¹)
      rw [hDA, Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ a) ha
    let σA : Fin (m + 1) → Fˣ := fun a => Units.mk0 (DA a) (hDAne a)
    have hMWtA : ∀ a, MWt P A a = DA a := by
      intro a
      show (((P * A * P⁻¹ : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F)) a a = DA a
      rw [hDA, Matrix.diagonal_apply_eq]
    have hDAhom : (P * A * P⁻¹ : GL (Fin (m + 1)) F) =
        CFSG.SectionRank.OddCover.diagHom (m + 1) σA := by
      apply Units.ext
      rw [CFSG.SectionRank.OddCover.coe_diagHom]
      ext a b
      rw [hDA]
      by_cases hab : a = b
      · subst hab
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        exact (Units.val_mk0 (hDAne a)).symm
      · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab]
    have hσconst : ∀ a ∈ I, ∀ b ∈ I, σA a = σA b := by
      intro a ha b hb
      apply Units.ext
      have hD : DA a = DA b := by
        have := hAconst a ha b hb
        rwa [hMWtA a, hMWtA b] at this
      rw [show (σA a : F) = DA a from Units.val_mk0 (hDAne a),
        show (σA b : F) = DA b from Units.val_mk0 (hDAne b), hD]
    have hbD : b ∈ D := by
      rw [hcfg.std.2.2.2.2.2.2]
      refine Subgroup.mem_inf.mpr ⟨hbB, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [hKI] at hk
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hk
      have hvblock : CFSG.StandardType.TableBUE.IsBlockOn I
          (((v : GL (Fin (m + 1)) F)) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
        CFSG.StandardType.TableBUE.mem_blockSU.mp hv
      have hcommP : (P * A * P⁻¹ : GL (Fin (m + 1)) F) * (v : GL (Fin (m + 1)) F) =
          (v : GL (Fin (m + 1)) F) * (P * A * P⁻¹ : GL (Fin (m + 1)) F) := by
        rw [hDAhom]
        exact CFSG.StandardType.TableBUE.diagHom_mul_comm_of_isBlockOn hσconst hvblock
      have hcommA : A * (cP v) = (cP v) * A := by
        have hcv : ((cP v : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n))) :
            GL (Fin (m + 1)) F) = P⁻¹ * (v : GL (Fin (m + 1)) F) * P := hcP v
        rw [hcv]
        calc A * (P⁻¹ * (v : GL (Fin (m + 1)) F) * P)
            = P⁻¹ * ((P * A * P⁻¹) * (v : GL (Fin (m + 1)) F)) * P := by group
          _ = P⁻¹ * ((v : GL (Fin (m + 1)) F) * (P * A * P⁻¹)) * P := by rw [hcommP]
          _ = (P⁻¹ * (v : GL (Fin (m + 1)) F) * P) * A := by group
      have hAActs : GActs ψ b A :=
        gen_equivariance hperfU θ ψ hψ (hBN hbB) (hGUN hAMGU) hAInd
      have hψc : (ψ (cP v) : Ω) = b⁻¹ * (ψ (cP v) : Ω) * b := by
        have hself : ((cP v : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n))) :
            GL (Fin (m + 1)) F) =
            A * ((cP v : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n))) :
              GL (Fin (m + 1)) F) * A⁻¹ := by
          rw [hcommA]; group
        exact hAActs (cP v) (cP v) hself
      have hcommb : (ψΩ v : Ω) * b = b * (ψΩ v : Ω) := by
        have h2 : b * (ψ (cP v) : Ω) = (ψ (cP v) : Ω) * b := by
          calc b * (ψ (cP v) : Ω) = b * (b⁻¹ * (ψ (cP v) : Ω) * b) := by
                conv_lhs => rw [hψc]
            _ = (ψ (cP v) : Ω) * b := by group
        simpa [ψΩ, ψP, MonoidHom.comp_apply] using h2.symm
      exact hcommb
    have hy1 : y ≠ 1 := by
      intro hy1; exact hyx (by rw [hy1]; exact Subgroup.one_mem _)
    have hyp : y ^ p = 1 := hcfg.elem.2 y hyB
    obtain ⟨c₁, hc₁, k, hk⟩ : ∃ c₁ ∈ Subgroup.zpowers x, ∃ k : ℕ, b = c₁ * y ^ k := by
      letI : CommGroup ↥D :=
        { (inferInstance : Group ↥D) with
          mul_comm := fun a b => Subtype.ext (IsElemAbelian.comm hcfg.std.2.1 a.2 b.2) }
      have htop : (Subgroup.zpowers x).subgroupOf D ⊔ (Subgroup.zpowers y).subgroupOf D =
          (⊤ : Subgroup ↥D) := by
        rw [← Subgroup.subgroupOf_sup
          (Subgroup.zpowers_le.mpr hcfg.std.2.2.2.1) (Subgroup.zpowers_le.mpr hyD),
          hDsup, Subgroup.subgroupOf_self]
      have hmem : (⟨b, hbD⟩ : ↥D) ∈
          (Subgroup.zpowers x).subgroupOf D ⊔ (Subgroup.zpowers y).subgroupOf D := by
        rw [htop]; exact Subgroup.mem_top _
      obtain ⟨c₁, hc₁, c₂, hc₂, hbc⟩ := Subgroup.mem_sup.mp hmem
      have hc₁' : (c₁ : Ω) ∈ Subgroup.zpowers x := Subgroup.mem_subgroupOf.mp hc₁
      have hc₂' : (c₂ : Ω) ∈ Subgroup.zpowers y := Subgroup.mem_subgroupOf.mp hc₂
      obtain ⟨k, hk⟩ := exists_nat_pow_eq_of_mem_zpowers hp.pos hyp hc₂'
      have hbc' : (c₁ : Ω) * (c₂ : Ω) = b := by
        have := congrArg (fun z : ↥D => (z : Ω)) hbc
        simpa using this
      exact ⟨(c₁ : Ω), hc₁', k, by rw [← hbc', hk]⟩
    have hc₁S : c₁ ∈ Subgroup.centralizer (S : Set Ω) :=
      (Subgroup.zpowers_le.mpr ((hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x))) hc₁
    have hbActs : GActs ψ b A :=
      gen_equivariance hperfU θ ψ hψ (hBN hbB) (hGUN hAMGU) hAInd
    have hAyActs_pow : GActs ψ (y ^ k) (Ay ^ k) := gacts_pow hAyN hAyActs k
    have hAypowN : Ay ^ k ∈ Subgroup.normalizer
        ((LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n) :
          Subgroup (GL (Fin (m + 1)) F)) : Set (GL (Fin (m + 1)) F)) := Subgroup.pow_mem _ hAyN k
    have hAyinvpowActs : GActs ψ ((y ^ k)⁻¹) ((Ay ^ k)⁻¹) :=
      gacts_inv hAypowN hAyActs_pow
    have hbcomm : b * (y ^ k)⁻¹ = (y ^ k)⁻¹ * b := by
      have hc₁B : c₁ ∈ B := hcfg.std.1 ((Subgroup.zpowers_le.mpr hcfg.std.2.2.2.1) hc₁)
      have hcomm : c₁ * y ^ k = y ^ k * c₁ :=
        IsElemAbelian.comm hcfg.elem hc₁B (Subgroup.pow_mem _ hyB k)
      calc b * (y ^ k)⁻¹ = (c₁ * y ^ k) * (y ^ k)⁻¹ := by rw [hk]
        _ = c₁ := by group
        _ = (y ^ k)⁻¹ * (c₁ * y ^ k) := by rw [hcomm]; group
        _ = (y ^ k)⁻¹ * b := by rw [hk]
    have hComb : GActs ψ (b * (y ^ k)⁻¹) (A * (Ay ^ k)⁻¹) :=
      gacts_mul (hGUN hAMGU) (Subgroup.inv_mem _ hAypowN) hbActs hAyinvpowActs hbcomm
    have hscalar : A * (Ay ^ k)⁻¹ ∈ LargeEvenScalars (Fin (m + 1)) F := by
      apply hcen
      intro u hu
      have hCN : A * (Ay ^ k)⁻¹ ∈ Subgroup.normalizer
          ((LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n) :
            Subgroup (GL (Fin (m + 1)) F)) : Set (GL (Fin (m + 1)) F)) :=
        Subgroup.mul_mem _ (hGUN hAMGU) (Subgroup.inv_mem _ hAypowN)
      have hwu : (A * (Ay ^ k)⁻¹) * u * (A * (Ay ^ k)⁻¹)⁻¹ ∈
          LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n) :=
        (Subgroup.mem_normalizer_iff.mp hCN u).mp hu
      let uu : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n)) := ⟨u, hu⟩
      let w : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n)) :=
        ⟨(A * (Ay ^ k)⁻¹) * u * (A * (Ay ^ k)⁻¹)⁻¹, hwu⟩
      have hw : (w : GL (Fin (m + 1)) F) =
          (A * (Ay ^ k)⁻¹) * u * (A * (Ay ^ k)⁻¹)⁻¹ := rfl
      have h1 : (ψ w : Ω) = (b * (y ^ k)⁻¹)⁻¹ * (ψ uu : Ω) * (b * (y ^ k)⁻¹) :=
        hComb uu w hw
      have hc₁ψ : (ψ w : Ω) = (ψ uu : Ω) := by
        rw [h1, show b * (y ^ k)⁻¹ = c₁ from by rw [hk]; group]
        have hcomm := Subgroup.mem_centralizer_iff.mp hc₁S (ψ uu) (ψ uu).2
        have hkey : c₁⁻¹ * (ψ uu) * c₁ = (ψ uu) := by
          have := congrArg (fun x : Ω => c₁⁻¹ * x) hcomm
          simpa [mul_assoc] using this
        simpa using hkey
      have hc₁ψ' : ψ w = ψ uu := Subtype.ext hc₁ψ
      have hz1 : ψ (w * uu⁻¹) = 1 := by
        rw [map_mul, map_inv, hc₁ψ', mul_inv_cancel]
      have hsc := hψker (w * uu⁻¹) hz1
      have hval : ((w * uu⁻¹ : ↥(LargeEvenSUGroup (Fin (m + 1)) F (2 ^ n))) :
          GL (Fin (m + 1)) F) =
          (A * (Ay ^ k)⁻¹) * u * (A * (Ay ^ k)⁻¹)⁻¹ * u⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hw]
      show ⁅A * (Ay ^ k)⁻¹, u⁆ ∈ LargeEvenScalars (Fin (m + 1)) F
      simpa only [commutatorElement_def, hval] using hsc
    obtain ⟨c, hc⟩ := by
      have hrange_scalar : A * (Ay ^ k)⁻¹ ∈
          (Matrix.GeneralLinearGroup.scalar (Fin (m + 1))).range := by
        rwa [CFSG.Assembly.largeEvenScalars_def] at hscalar
      exact MonoidHom.mem_range.mp hrange_scalar
    refine ⟨c, k, ?_⟩
    calc A = (A * (Ay ^ k)⁻¹) * Ay ^ k := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c * Ay ^ k := by rw [hc]
  have hsing : 2 ≤ n → ∀ a b : Fin (m + 1), a ∉ I → b ∉ I → a ≠ b →
      MWt P Ay a ≠ MWt P Ay b := by
    intro hn2 a b ha hb hab hw
    have hδaD : δ a = (Units.mk0 (Dfun a) (hDne a))⁻¹ := rfl
    have hδbD : δ b = (Units.mk0 (Dfun b) (hDne b))⁻¹ := rfl
    let L := CFSG.StandardType.LinTorus.diagClass ({y} : Set Ω) (fun _ => δ) a
    have hbL : b ∈ L := by
      rw [show L = CFSG.StandardType.LinTorus.diagClass ({y} : Set Ω) (fun _ => δ) a from rfl,
        CFSG.StandardType.LinTorus.mem_diagClass]
      intro e he
      rw [Set.mem_singleton_iff] at he; subst he
      have hD : Dfun b = Dfun a := by
        have := hw; rw [hMWt a, hMWt b] at this; exact this.symm
      have hδeq : (Units.mk0 (Dfun b) (hDne b))⁻¹ = (Units.mk0 (Dfun a) (hDne a))⁻¹ := by
        congr 1
        exact Units.ext hD
      simpa only [δ] using hδeq
    have hL2 : 2 ≤ L.card := by
      have hsub : ({a, b} : Finset (Fin (m + 1))) ⊆ L := by
        intro c hc
        rw [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl
        · exact CFSG.StandardType.LinTorus.self_mem_diagClass _ _ _
        · exact hbL
      have h2 := Finset.card_le_card hsub
      rwa [Finset.card_pair hab] at h2
    have hLne : L ≠ I := by
      intro hLI
      apply ha
      rw [← hLI]
      exact CFSG.StandardType.LinTorus.self_mem_diagClass _ _ _
    have hdisj : Disjoint L I := by
      rw [Finset.disjoint_left]
      intro c hcL hcI
      apply hLne
      have hca : δ c = δ a := by
        have := (CFSG.StandardType.LinTorus.mem_diagClass.mp hcL) y (Set.mem_singleton y)
        simpa using this
      have hci : δ c = δ i := by
        have hcI' : c ∈ CFSG.StandardType.LinTorus.diagClass ({y} : Set Ω) (fun _ => δ) i := by
          rw [hIdef] at hcI; exact hcI
        have := (CFSG.StandardType.LinTorus.mem_diagClass.mp hcI') y (Set.mem_singleton y)
        simpa using this
      have hδai : δ a = δ i := hca.symm.trans hci
      have hδaid : Dfun a = Dfun i := by
        have h1 : (δ a : F) = (δ i : F) := congrArg Units.val hδai
        have h2 : (Dfun a)⁻¹ = (Dfun i)⁻¹ := by simpa [δ] using h1
        exact inv_inj.mp h2
      ext d
      rw [show L = CFSG.StandardType.LinTorus.diagClass ({y} : Set Ω) (fun _ => δ) a from rfl,
        CFSG.StandardType.LinTorus.mem_diagClass, hIdef,
        CFSG.StandardType.LinTorus.mem_diagClass]
      constructor
      · intro hd e he
        rw [← hδai]
        exact hd e he
      · intro hd e he
        rw [hδai]
        exact hd e he
    let nL : Subgroup Ω := (CFSG.StandardType.TableBUE.blockSU (K := F) (n := n) L).map ψΩ
    have hδL : ∀ e ∈ ({y} : Set Ω),
        (e, CFSG.SectionRank.OddCover.diagHom (m + 1) ((fun _ => δ) e)) ∈
          CFSG.StandardType.SUTorus.suPairs ψΩ := by
      intro e he
      rw [Set.mem_singleton_iff] at he; subst he
      exact hsups'
    have hnLcomp : CFSG.Assembly.IsComponentOf nL (S ⊓ Subgroup.centralizer ({y} : Set Ω)) := by
      refine ⟨?_, ?_, ?_⟩
      · refine le_inf ?_ ?_
        · rw [← hrange]; exact Subgroup.map_le_range _ _
        · intro x hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hyc : y ∈ Subgroup.centralizer ((nL : Subgroup Ω) : Set Ω) :=
            CFSG.StandardType.SUTorus.mem_centralizer_map_blockSU
              (K := F) (f := n) (m := m) (G := Ω) (ψ := ψΩ) (I := L)
              (d := (fun _ => δ) y) (e := y) hsups'
              (fun i hi j hj => by
                have hi' : i ∈ CFSG.StandardType.LinTorus.diagClass
                    ({y} : Set Ω) (fun _ => δ) a := hi
                have hj' : j ∈ CFSG.StandardType.LinTorus.diagClass
                    ({y} : Set Ω) (fun _ => δ) a := hj
                exact CFSG.StandardType.LinTorus.eq_of_mem_diagClass hi' hj'
                  (Set.mem_singleton y))
          exact (Subgroup.mem_centralizer_iff.mp hyc) x hx
      · rw [← hrange]
        exact CFSG.StandardType.SUTorus.isSubnormal_map_blockSU
          (f := n) (K := F) (m := m) (G := Ω) (ψ := ψΩ) (S := ({y} : Set Ω))
          (δ := (fun _ => δ)) hkerψ hδL a
      · exact CFSG.StandardType.SURepair.isQuasisimple_map_blockSU_of_two_le
          (f := n) (K := F) (n := m + 1) (G := Ω) hUF hn2 hkerψ hL2
    have hnLK : nL ≤ K := by
      rw [hcfg.std.2.2.2.2.1, hcs]
      exact le_sSup ((CFSG.Assembly.isComponentOf_iff_open).mp hnLcomp)
    have hnLCK : nL ≤ Subgroup.centralizer (K : Set Ω) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [hKI] at hk
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hk
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
      rw [← map_mul, ← map_mul]
      congr 1
      exact (CFSG.StandardType.Line63.H5.blockSU_commute_of_disjoint hdisj hu hv).symm
    exact CFSG.StandardType.LinSemisimple.false_of_isQuasisimple_of_commute hnLcomp.2.2
      (fun x hx y hy => Subgroup.mem_centralizer_iff.mp (hnLCK hy) x (hnLK hx))
  exact ⟨I, hI2, hI3, hKfirst, Ay, hAyGh, hlev, hconst, hsing⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end

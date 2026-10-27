module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundA0Field
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenKernel
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L J A : Subgroup G} {d b : G} {p N n : ℕ}
variable {K : Type} [Field K] [Finite K]
variable {H : Subgroup (GL (Fin N) K)} {S : Set (GL (Fin N) K)}
variable {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj H}
variable {hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) S,
  LargeEvenInduces θ (conjRel a) φ}
variable {hS : S ⊆ Subgroup.normalizer (H : Set (GL (Fin N) K))}

theorem LiftMap.projConj_mul_eq [Nonempty (Fin N)]
    (M : LiftMap (L := L) (A := A) θ hact hS) (hsetup : Setup p L J A d b) (a b : ↥A) :
    TableB.projConj H ⟨M.mat (a * b), hS (M.mem (a * b))⟩ =
      TableB.projConj H ⟨M.mat a * M.mat b,
        Subgroup.mul_mem _ (hS (M.mem a)) (hS (M.mem b))⟩ := by
  have hAnorm : A ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S11.le_normalizer_of_innerDiag hsetup.idiag
  have hcomm : ((a : ↥A) : G) * ((b : ↥A) : G) = ((b : ↥A) : G) * ((a : ↥A) : G) :=
    IsElemAbelian.comm hsetup.elem a.2 b.2
  have hprod : LargeEvenInduces θ (conjRel ((a : G) * (b : G)))
      (TableB.projConj H ⟨M.mat a, hS (M.mem a)⟩ *
        TableB.projConj H ⟨M.mat b, hS (M.mem b)⟩) :=
    largeEvenInduces_mul (hAnorm a.2) (hAnorm b.2) hcomm (M.ind a) (M.ind b)
  have hprod' : LargeEvenInduces θ (conjRel (((a * b : ↥A) : G)))
      (TableB.projConj H ⟨M.mat a * M.mat b,
        Subgroup.mul_mem _ (hS (M.mem a)) (hS (M.mem b))⟩) := by
    rw [show (⟨M.mat a * M.mat b,
        Subgroup.mul_mem _ (hS (M.mem a)) (hS (M.mem b))⟩ :
        Subgroup.normalizer (H : Set (GL (Fin N) K))) =
        ⟨M.mat a, hS (M.mem a)⟩ * ⟨M.mat b, hS (M.mem b)⟩ from rfl, map_mul]
    simpa only [Subgroup.coe_mul] using hprod
  exact largeEvenInduces_unique (φ := TableB.projConj H
      ⟨M.mat (a * b), hS (M.mem (a * b))⟩) (M.ind (a * b)) hprod'
    (conjRel_total (hAnorm (A.mul_mem a.2 b.2)))

theorem LiftMap.mul_mem_scalars [Nonempty (Fin N)]
    (M : LiftMap (L := L) (A := A) θ hact hS) (hsetup : Setup p L J A d b) (a b : ↥A)
    (hker : ∀ (X : Subgroup.normalizer (H : Set (GL (Fin N) K))),
      TableB.projConj H X = 1 → (X : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K) :
    M.mat (a * b) * (M.mat a * M.mat b)⁻¹ ∈ LargeEvenScalars (Fin N) K := by
  let X : Subgroup.normalizer (H : Set (GL (Fin N) K)) :=
    ⟨M.mat (a * b) * (M.mat a * M.mat b)⁻¹,
      Subgroup.mul_mem _ (hS (M.mem (a * b)))
        (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hS (M.mem a)) (hS (M.mem b))))⟩
  have hX1 : TableB.projConj H X = 1 := by
    have hXdef : X = (⟨M.mat (a * b), hS (M.mem (a * b))⟩ :
        Subgroup.normalizer (H : Set (GL (Fin N) K))) *
        (⟨M.mat a * M.mat b,
          Subgroup.mul_mem _ (hS (M.mem a)) (hS (M.mem b))⟩)⁻¹ := rfl
    rw [hXdef, map_mul, map_inv, M.projConj_mul_eq (L := L) (A := A) (S := S) hsetup a b,
      mul_inv_cancel]
  have h := hker X hX1
  simpa only [X, Subgroup.coe_mk] using h

theorem LiftMap.one_mem_scalars [Nonempty (Fin N)]
    (M : LiftMap (L := L) (A := A) θ hact hS) (hsetup : Setup p L J A d b)
    (hker : ∀ (X : Subgroup.normalizer (H : Set (GL (Fin N) K))),
      TableB.projConj H X = 1 → (X : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K) :
    M.mat (1 : ↥A) ∈ LargeEvenScalars (Fin N) K := by
  have h := M.mul_mem_scalars (L := L) (A := A) (S := S) hsetup (1 : ↥A) (1 : ↥A) hker
  rw [mul_one] at h
  have hv : M.mat (1 : ↥A) * (M.mat (1 : ↥A) * M.mat (1 : ↥A))⁻¹ = (M.mat (1 : ↥A))⁻¹ := by
    group
  rw [hv] at h
  exact inv_mem h

private theorem inv_mul_eq_inv_of_mul_inv_eq_central {Y : Type} [Group Y] {x y z : Y}
    (h : x * y⁻¹ = z) (hc : ∀ g : Y, z * g = g * z) : x⁻¹ * y = z⁻¹ := by
  have hx : x = z * y := by rw [← h]; group
  have hcy : Commute z y := hc y
  calc x⁻¹ * y = (z * y)⁻¹ * y := by rw [hx]
    _ = y⁻¹ * z⁻¹ * y := by rw [mul_inv_rev]
    _ = y⁻¹ * (z⁻¹ * y) := by group
    _ = y⁻¹ * (y * z⁻¹) := by rw [hcy.inv_left.eq]
    _ = z⁻¹ := by group


theorem linFieldTypeA0Bound_holds : LinFieldTypeA0Bound := by
  intro G _ _ p N n L J A d b K _ _ hK hN θ hact hS hsetup M lam hDp hlam A₀ hA₀A hcomm
  classical
  haveI : Fact p.Prime := ⟨hsetup.prime⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  haveI : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hsetup.odd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hsetup.prime).mp h2).symm
  have hker : ∀ X : Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)),
      TableB.projConj (LargeEvenSLGroup (Fin N) K) X = 1 →
        (X : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K :=
    fun X hX => linKernelScalar_of_three_le hN X hX
  set D : GL (Fin N) K := M.mat ⟨d, hsetup.d_mem⟩ with hD
  let C : Subgroup (GL (Fin N) K) := Subgroup.centralizer ({D} : Set (GL (Fin N) K))
  have hDp' : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) lam := by
    rw [hD]; exact hDp
  have hA₀elem : IsElemAbelian p A₀ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hsetup.elem.2 x (hA₀A hx)⟩
    have hc := hsetup.elem.1.is_comm.comm ⟨a.1, hA₀A a.2⟩ ⟨b.1, hA₀A b.2⟩
    exact Subtype.ext (congrArg (Subtype.val : ↥A → G) hc)
  let f : ↥A₀ →* StatedProj C :=
    { toFun := fun a => QuotientGroup.mk
        ⟨M.mat ⟨a.1, hA₀A a.2⟩, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hcomm a a.2⟩
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).mpr
        rw [Subgroup.mem_subgroupOf]
        exact M.one_mem_scalars (L := L) (A := A) (S := Set.univ) hsetup hker
      map_mul' := fun a b => by
        rw [← QuotientGroup.mk_mul]
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        let Aa : ↥A := ⟨a.1, hA₀A a.2⟩
        let Ab : ↥A := ⟨b.1, hA₀A b.2⟩
        have hX := M.mul_mem_scalars (L := L) (A := A) (S := Set.univ) hsetup Aa Ab hker
        obtain ⟨z, hz⟩ := hX
        have hXmem : Matrix.GeneralLinearGroup.scalar (Fin N) z ∈ LargeEvenScalars (Fin N) K :=
          ⟨z, rfl⟩
        have hzeq : M.mat (Aa * Ab) * (M.mat Aa * M.mat Ab)⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin N) z := hz.symm
        have hXc : ∀ T : GL (Fin N) K,
            Matrix.GeneralLinearGroup.scalar (Fin N) z * T =
              T * Matrix.GeneralLinearGroup.scalar (Fin N) z :=
          fun T => ((Subgroup.mem_center_iff.mp (TableB.scalars_le_center hXmem)) T).symm
        have hinv := inv_mul_eq_inv_of_mul_inv_eq_central hzeq hXc
        change (M.mat (Aa * Ab))⁻¹ * (M.mat Aa * M.mat Ab) ∈ LargeEvenScalars (Fin N) K
        rw [hinv]
        exact inv_mem hXmem }
  have hf_inj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have hscal : (M.mat ⟨a.1, hA₀A a.2⟩ : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp ha)
    have hproj : TableB.projConj (LargeEvenSLGroup (Fin N) K)
        ⟨M.mat ⟨a.1, hA₀A a.2⟩, hS (M.mem ⟨a.1, hA₀A a.2⟩)⟩ = 1 :=
      TableB.projConj_of_scalar _ hscal
    have h1 : LargeEvenInduces θ (conjRel a.1) 1 := by
      have h := M.ind ⟨a.1, hA₀A a.2⟩
      rwa [hproj] at h
    have h2 : LargeEvenInduces θ (conjRel (1 : G)) 1 :=
      largeEvenInduces_one (rel := conjRel (1 : G)) fun l l' hl => by
        have hl' : (l' : G) = (l : G) := by simpa [conjRel] using hl
        exact Subtype.ext hl'.symm
    have hAnorm : A ≤ Subgroup.normalizer (L : Set G) :=
      CFSG.LocalAnalysis.GLTheoremA.S11.le_normalizer_of_innerDiag hsetup.idiag
    haveI : Group.IsPerfect ↥L := ⟨hsetup.qs.1⟩
    let α : MulAut ↥L := L.normalizerMonoidHom ⟨a.1, hAnorm (hA₀A a.2)⟩
    have hαapp : ∀ l : ↥L, ((α l : ↥L) : G) = a.1 * (l : G) * a.1⁻¹ := by
      intro l
      rw [show α = L.normalizerMonoidHom ⟨a.1, hAnorm (hA₀A a.2)⟩ from rfl]
      rfl
    have hquot : CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α = 1 := by
      ext x
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) x
      rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
      apply θ.injective
      have hl : conjRel a.1 (α l) l := by
        change (l : G) = a.1⁻¹ * ((α l : ↥L) : G) * a.1
        rw [hαapp]; group
      have h := h1 (α l) l hl
      simpa using h
    have hα1 : α = 1 :=
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_eq_one_imp α hquot
    have hcent : a.1 ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hh : a.1 * l * a.1⁻¹ = l := by
        have h := congrArg (fun f : MulAut ↥L => ((f ⟨l, hl⟩ : ↥L) : G)) hα1
        simpa [hαapp] using h
      calc l * a.1 = a.1 * (a.1⁻¹ * l * a.1) := by group
        _ = a.1 * l := by
            rw [show a.1⁻¹ * l * a.1 = l from by
              calc a.1⁻¹ * l * a.1 = a.1⁻¹ * (a.1 * l * a.1⁻¹) * a.1 := by rw [hh]
                _ = l := by group]
    have hbot : a.1 ∈ (⊥ : Subgroup G) := by
      rw [← hsetup.faithful]
      exact ⟨hA₀A a.2, hcent⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  have htop : IsElemAbelian p (⊤ : Subgroup ↥A₀) := by
    have h := hA₀elem.subgroupOf A₀
    simpa only [Subgroup.subgroupOf_self] using h
  have hE : IsElemAbelian p f.range := by
    have h := IsElemAbelian.map htop f
    simpa only [MonoidHom.range_eq_map] using h
  have hgen := card_le_pow_centralizer_of_scalar_pow hsetup.prime (by omega) hDp' hlam hpK
    hsetup.odd f.range hE
  have hcard : Nat.card ↥A₀ = Nat.card ↥f.range := by
    have h := Subgroup.card_map_of_injective (f := f) (K := ⊤) hf_inj
    have h2 : Subgroup.map f (⊤ : Subgroup ↥A₀) = f.range := (MonoidHom.range_eq_map f).symm
    rw [h2] at h
    simpa using h.symm
  rwa [hcard]

theorem uniFieldTypeA0Bound_holds : UniFieldTypeA0Bound := by
  intro G _ _ p N n L J A d b K _ _ h hN hNq hpq θ hact hS hsetup M lam hDp hlam A₀ hA₀A hcomm
  classical
  haveI : Fact p.Prime := ⟨hsetup.prime⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  haveI : CharP K 2 := h.charP
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hsetup.odd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hsetup.prime).mp h2).symm
  have hker : ∀ X : Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)),
      TableB.projConj (unitarySU 2 n K N) X = 1 →
        (X : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K :=
    fun X hX => uniKernelScalar h hN hNq hsetup.prime hpq X hX
  set D : GL (Fin N) K := M.mat ⟨d, hsetup.d_mem⟩ with hD
  let C : Subgroup (GL (Fin N) K) := Subgroup.centralizer ({D} : Set (GL (Fin N) K))
  have hDp' : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) lam := by
    rw [hD]; exact hDp
  have hA₀elem : IsElemAbelian p A₀ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hsetup.elem.2 x (hA₀A hx)⟩
    have hc := hsetup.elem.1.is_comm.comm ⟨a.1, hA₀A a.2⟩ ⟨b.1, hA₀A b.2⟩
    exact Subtype.ext (congrArg (Subtype.val : ↥A → G) hc)
  let f : ↥A₀ →* StatedProj C :=
    { toFun := fun a => QuotientGroup.mk
        ⟨M.mat ⟨a.1, hA₀A a.2⟩, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hcomm a a.2⟩
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).mpr
        rw [Subgroup.mem_subgroupOf]
        exact M.one_mem_scalars (L := L) (A := A) (S := LargeEvenGUSet (Fin N) K (2 ^ n))
          hsetup hker
      map_mul' := fun a b => by
        rw [← QuotientGroup.mk_mul]
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        let Aa : ↥A := ⟨a.1, hA₀A a.2⟩
        let Ab : ↥A := ⟨b.1, hA₀A b.2⟩
        have hX := M.mul_mem_scalars (L := L) (A := A) (S := LargeEvenGUSet (Fin N) K (2 ^ n))
          hsetup Aa Ab hker
        obtain ⟨z, hz⟩ := hX
        have hXmem : Matrix.GeneralLinearGroup.scalar (Fin N) z ∈ LargeEvenScalars (Fin N) K :=
          ⟨z, rfl⟩
        have hzeq : M.mat (Aa * Ab) * (M.mat Aa * M.mat Ab)⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin N) z := hz.symm
        have hXc : ∀ T : GL (Fin N) K,
            Matrix.GeneralLinearGroup.scalar (Fin N) z * T =
              T * Matrix.GeneralLinearGroup.scalar (Fin N) z :=
          fun T => ((Subgroup.mem_center_iff.mp (TableB.scalars_le_center hXmem)) T).symm
        have hinv := inv_mul_eq_inv_of_mul_inv_eq_central hzeq hXc
        change (M.mat (Aa * Ab))⁻¹ * (M.mat Aa * M.mat Ab) ∈ LargeEvenScalars (Fin N) K
        rw [hinv]
        exact inv_mem hXmem }
  have hf_inj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have hscal : (M.mat ⟨a.1, hA₀A a.2⟩ : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp ha)
    have hproj : TableB.projConj (unitarySU 2 n K N)
        ⟨M.mat ⟨a.1, hA₀A a.2⟩, hS (M.mem ⟨a.1, hA₀A a.2⟩)⟩ = 1 :=
      TableB.projConj_of_scalar _ hscal
    have h1 : LargeEvenInduces θ (conjRel a.1) 1 := by
      have h := M.ind ⟨a.1, hA₀A a.2⟩
      rwa [hproj] at h
    have h2 : LargeEvenInduces θ (conjRel (1 : G)) 1 :=
      largeEvenInduces_one (rel := conjRel (1 : G)) fun l l' hl => by
        have hl' : (l' : G) = (l : G) := by simpa [conjRel] using hl
        exact Subtype.ext hl'.symm
    have hAnorm : A ≤ Subgroup.normalizer (L : Set G) :=
      CFSG.LocalAnalysis.GLTheoremA.S11.le_normalizer_of_innerDiag hsetup.idiag
    haveI : Group.IsPerfect ↥L := ⟨hsetup.qs.1⟩
    let α : MulAut ↥L := L.normalizerMonoidHom ⟨a.1, hAnorm (hA₀A a.2)⟩
    have hαapp : ∀ l : ↥L, ((α l : ↥L) : G) = a.1 * (l : G) * a.1⁻¹ := by
      intro l
      rw [show α = L.normalizerMonoidHom ⟨a.1, hAnorm (hA₀A a.2)⟩ from rfl]
      rfl
    have hquot : CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α = 1 := by
      ext x
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) x
      rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
      apply θ.injective
      have hl : conjRel a.1 (α l) l := by
        change (l : G) = a.1⁻¹ * ((α l : ↥L) : G) * a.1
        rw [hαapp]; group
      have h := h1 (α l) l hl
      simpa using h
    have hα1 : α = 1 :=
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_eq_one_imp α hquot
    have hcent : a.1 ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hh : a.1 * l * a.1⁻¹ = l := by
        have h := congrArg (fun f : MulAut ↥L => ((f ⟨l, hl⟩ : ↥L) : G)) hα1
        simpa [hαapp] using h
      calc l * a.1 = a.1 * (a.1⁻¹ * l * a.1) := by group
        _ = a.1 * l := by
            rw [show a.1⁻¹ * l * a.1 = l from by
              calc a.1⁻¹ * l * a.1 = a.1⁻¹ * (a.1 * l * a.1⁻¹) * a.1 := by rw [hh]
                _ = l := by group]
    have hbot : a.1 ∈ (⊥ : Subgroup G) := by
      rw [← hsetup.faithful]
      exact ⟨hA₀A a.2, hcent⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  have htop : IsElemAbelian p (⊤ : Subgroup ↥A₀) := by
    have h := hA₀elem.subgroupOf A₀
    simpa only [Subgroup.subgroupOf_self] using h
  have hE : IsElemAbelian p f.range := by
    have h := IsElemAbelian.map htop f
    simpa only [MonoidHom.range_eq_map] using h
  have hgen := card_le_pow_centralizer_of_scalar_pow hsetup.prime (by omega) hDp' hlam hpK
    hsetup.odd f.range hE
  have hcard : Nat.card ↥A₀ = Nat.card ↥f.range := by
    have h := Subgroup.card_map_of_injective (f := f) (K := ⊤) hf_inj
    have h2 : Subgroup.map f (⊤ : Subgroup ↥A₀) = f.range := (MonoidHom.range_eq_map f).symm
    rw [h2] at h
    simpa using h.symm
  rwa [hcard]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

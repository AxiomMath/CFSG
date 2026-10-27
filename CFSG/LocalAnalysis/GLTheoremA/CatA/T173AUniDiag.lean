module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs
import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.SignalizerFunctor.SurjectiveSylowLifting

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.SignalizerFunctor.Helpers
open scoped MatrixGroups

private theorem unitaryFieldData_of_uniArith {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : UniArith p n d F) : UnitaryFieldData 2 n F := by
  obtain ⟨hp, hpq, hpd, hcard, hn, hd, hdn⟩ := h
  refine ⟨Nat.prime_two, hn, ?_⟩
  rw [hcard, pow_two, ← pow_add, two_mul]

private theorem mem_uniSU_iff {n d : ℕ} {F : Type} [Field F] [Finite F]
    (hUF : UnitaryFieldData 2 n F) {x : GL (Fin d) F} :
    x ∈ UniSU n d F ↔ x ∈ primeFormUnitary hUF (idGram F d) ∧
      ((x : Matrix (Fin d) (Fin d) F).det = 1) := by
  constructor
  · intro hx
    have hx' : x ∈ unitarySU 2 n F d := hx
    refine ⟨?_, ((mem_unitarySU_iff hUF).mp hx').1⟩
    rw [mem_primeFormUnitary]
    simpa [idGram] using ((mem_unitarySU_iff hUF).mp hx').2
  · rintro ⟨hu, hd⟩
    have hx' : x ∈ unitarySU 2 n F d := by
      rw [mem_unitarySU_iff hUF]
      refine ⟨hd, ?_⟩
      rw [mem_primeFormUnitary] at hu
      simpa [idGram] using hu
    exact hx'

private theorem conj_mem_uniSU {n d : ℕ} {F : Type} [Field F] [Finite F]
    (hUF : UnitaryFieldData 2 n F) {g x : GL (Fin d) F}
    (hg : g ∈ primeFormUnitary hUF (idGram F d)) (hx : x ∈ UniSU n d F) :
    g * x * g⁻¹ ∈ UniSU n d F := by
  obtain ⟨hxU, hxd⟩ := (mem_uniSU_iff hUF).mp hx
  refine (mem_uniSU_iff hUF).mpr ⟨?_, ?_⟩
  · exact mul_mem (mul_mem hg hxU) (inv_mem hg)
  · have hxdU : Matrix.GeneralLinearGroup.det x = 1 := by
      apply Units.ext
      simpa using hxd
    have hdet : Matrix.GeneralLinearGroup.det (g * x * g⁻¹) = 1 := by
      rw [map_mul, map_mul, hxdU, mul_one, map_inv]
      exact mul_inv_cancel _
    exact congrArg Units.val hdet

private theorem conj_inv_mem_uniSU {n d : ℕ} {F : Type} [Field F] [Finite F]
    (hUF : UnitaryFieldData 2 n F) {g x : GL (Fin d) F}
    (hg : g ∈ primeFormUnitary hUF (idGram F d)) (hx : x ∈ UniSU n d F) :
    g⁻¹ * x * g ∈ UniSU n d F := by
  simpa [inv_inv] using conj_mem_uniSU hUF (inv_mem hg) hx

private theorem eq_one_of_mem_scalars_of_pow_prime {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (hUF : UnitaryFieldData 2 n F) (hp : p.Prime) (hpd : ¬ p ∣ d)
    {x : ↥(UniSU n d F)} (hxsc : (x : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F)
    (hpow : ∃ k : ℕ, x ^ p ^ k = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hpow
  obtain ⟨c, hc⟩ := hxsc
  have hcx : (x : GL (Fin d) F) = Matrix.GeneralLinearGroup.scalar (Fin d) c := hc.symm
  have hxdet : ((x : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det = 1 :=
    ((mem_uniSU_iff hUF).mp x.2).2
  have hxdetU : Matrix.GeneralLinearGroup.det (x : GL (Fin d) F) = 1 := by
    apply Units.ext
    simpa using hxdet
  have hcd : c ^ d = 1 := by
    have h : Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin d) c) = 1 := by
      rw [← hcx]
      exact hxdetU
    rwa [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
  have hxd : x ^ d = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hcx, ← map_pow, hcd, map_one]
  have hordd : orderOf x ∣ d := orderOf_dvd_of_pow_eq_one hxd
  have hordp : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (p ^ k) d :=
    Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hpd)
  have hg : orderOf x ∣ Nat.gcd (p ^ k) d := Nat.dvd_gcd hordp hordd
  rw [hcop.gcd_eq_one] at hg
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hg)

theorem uni_exists_frame {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : UniArith p n d F)
    {Q : Type} [Group Q] (θ : Q ≃* UniPSU n d F) {Bbar : Subgroup Q} (hB : IsElemAbelian p Bbar) :
    ∃ (ψ : Q ≃* UniPSU n d F) (A : Subgroup (GL (Fin d) F)), UniDiagFrame p n d F ψ Bbar A := by
  classical
  have hUF : UnitaryFieldData 2 n F := unitaryFieldData_of_uniArith h
  obtain ⟨hp, hpq, hpd, hcard, hn, hd, hdn⟩ := h
  let E : Subgroup (UniPSU n d F) := Bbar.map θ.toMonoidHom
  have hE : IsElemAbelian p E := hB.map θ.toMonoidHom
  let sc : Subgroup (↥(UniSU n d F)) :=
    (LargeEvenScalars (Fin d) F).subgroupOf (UniSU n d F)
  let Ppre : Subgroup (↥(UniSU n d F)) := E.comap (UniMk n d F)
  let f : Ppre →* E :=
    ((UniMk n d F).comp Ppre.subtype).codRestrict E fun x => by
      have hx := x.2
      change (UniMk n d F) (x : ↥(UniSU n d F)) ∈ E at hx
      exact hx
  have hf : Function.Surjective f := by
    intro e
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective sc (e : UniPSU n d F)
    refine ⟨⟨y, ?_⟩, ?_⟩
    · show (UniMk n d F) y ∈ E
      rw [show (UniMk n d F) y = (e : UniPSU n d F) from hy]
      exact e.2
    · apply Subtype.ext
      exact hy
  obtain ⟨A₀, hA₀map⟩ := surjective_pgroup_sylow_lift p hp f hf hE.isPGroup
  let A₁ : Subgroup (↥(UniSU n d F)) := (A₀ : Subgroup Ppre).map Ppre.subtype
  have hA₁p : IsPGroup p A₁ := A₀.isPGroup'.map Ppre.subtype
  have hA₁map : A₁.map (UniMk n d F) = E := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
      exact (f a).2
    · intro e he
      have htop : (⟨e, he⟩ : E) ∈ (A₀ : Subgroup Ppre).map f := by
        rw [hA₀map]
        exact Subgroup.mem_top _
      obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp htop
      refine Subgroup.mem_map.mpr ⟨Ppre.subtype x,
        Subgroup.mem_map_of_mem Ppre.subtype hx, ?_⟩
      exact congrArg Subtype.val hfx
  have hker : A₁ ⊓ (UniMk n d F).ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxker⟩
    have hxsc : (x : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
      have hxsc' : x ∈ sc := by
        simpa [UniMk, LargeEvenProjMk, QuotientGroup.ker_mk'] using hxker
      exact Subgroup.mem_subgroupOf.mp hxsc'
    obtain ⟨k, hk⟩ := hA₁p ⟨x, hxA⟩
    have hkx : x ^ p ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    exact eq_one_of_mem_scalars_of_pow_prime hUF hp hpd hxsc ⟨k, hkx⟩
  have hinj : ∀ x ∈ A₁, ∀ y ∈ A₁, UniMk n d F x = UniMk n d F y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ A₁ ⊓ (UniMk n d F).ker := by
      refine ⟨A₁.mul_mem (A₁.inv_mem hx) hy, ?_⟩
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy, inv_mul_cancel])
    rw [hker] at hmem
    have hone : x⁻¹ * y = 1 := Subgroup.mem_bot.mp hmem
    rwa [inv_mul_eq_one] at hone
  have hA₁e : IsElemAbelian p A₁ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      refine hinj (a.1 * b.1) (A₁.mul_mem a.2 b.2) (b.1 * a.1)
        (A₁.mul_mem b.2 a.2) ?_
      have hma : (UniMk n d F) a.1 ∈ E := by
        rw [← hA₁map]
        exact Subgroup.mem_map_of_mem (UniMk n d F) a.2
      have hmb : (UniMk n d F) b.1 ∈ E := by
        rw [← hA₁map]
        exact Subgroup.mem_map_of_mem (UniMk n d F) b.2
      rw [map_mul, map_mul]
      exact hE.comm hma hmb
    · have hm : (UniMk n d F) x ∈ E := by
        rw [← hA₁map]
        exact Subgroup.mem_map_of_mem (UniMk n d F) hx
      apply hinj (x ^ p) (A₁.pow_mem hx p) 1 A₁.one_mem
      rw [map_pow, map_one]
      exact hE.2 _ hm
  let hSUU : UniSU n d F ≤ primeFormUnitary hUF (idGram F d) := by
    intro x hx
    exact ((mem_uniSU_iff hUF).mp hx).1
  let G : Subgroup (primeFormUnitary hUF (idGram F d)) :=
    A₁.map (Subgroup.inclusion hSUU)
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    intro x hx y hy
    rcases Subgroup.mem_map.mp hx with ⟨x', hx', rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨y', hy', rfl⟩
    apply Subtype.ext
    simpa using congrArg Subtype.val (hA₁e.comm hx' hy')
  have hGpow : ∀ x ∈ G, x ^ p = 1 := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨x', hx', rfl⟩
    apply Subtype.ext
    simpa using congrArg Subtype.val (hA₁e.2 x' hx')
  obtain ⟨P, hPdiag⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag hUF hp hpq G hGcomm hGpow
  let g : GL (Fin d) F := (P : primeFormUnitary hUF (idGram F d))
  have hPg : g ∈ primeFormUnitary hUF (idGram F d) := P.2
  let A1GL : Subgroup (GL (Fin d) F) := A₁.map (UniSU n d F).subtype
  have hA1GLe : IsElemAbelian p A1GL := hA₁e.map (UniSU n d F).subtype
  let A : Subgroup (GL (Fin d) F) :=
    A1GL.map (MulAut.conj g⁻¹).toMonoidHom
  have hGmap : G.map (primeFormUnitary hUF (idGram F d)).subtype = A1GL := by
    dsimp only [G, A1GL]
    rw [Subgroup.map_map]
    rfl
  have hA_le : A ≤ UniSU n d F := by
    intro a ha
    dsimp only [A] at ha
    rcases Subgroup.mem_map.mp ha with ⟨x, hx, rfl⟩
    dsimp only [A1GL] at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    simpa using conj_inv_mem_uniSU hUF hPg y.2
  have hAe : IsElemAbelian p A := by
    dsimp only [A]
    exact hA1GLe.map (MulAut.conj g⁻¹).toMonoidHom
  have hAd : ∀ a ∈ A, ∀ i j : Fin d, i ≠ j →
      (a : Matrix (Fin d) (Fin d) F) i j = 0 := by
    intro a ha i j hij
    dsimp only [A] at ha
    rcases Subgroup.mem_map.mp ha with ⟨x, hx, rfl⟩
    rw [← hGmap] at hx
    rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
    have hd := hPdiag u hu hij
    simpa [g, MulAut.conj_apply] using hd
  let eGL : GL (Fin d) F ≃* GL (Fin d) F := MulAut.conj g⁻¹
  have hmapSU : (UniSU n d F).map (eGL : GL (Fin d) F →* GL (Fin d) F) =
      UniSU n d F := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [eGL] using conj_inv_mem_uniSU hUF hPg hy
    · intro hz
      refine ⟨eGL.symm z, ?_, ?_⟩
      · simpa [eGL, MulAut.conj_symm_apply] using conj_mem_uniSU hUF hPg hz
      · exact MulEquiv.apply_symm_apply eGL z
  let eSU : ↥(UniSU n d F) ≃* ↥(UniSU n d F) :=
    (MulEquiv.subgroupMap eGL (UniSU n d F)).trans (MulEquiv.subgroupCongr hmapSU)
  have heSU_coe : ∀ x : ↥(UniSU n d F),
      ((eSU x : ↥(UniSU n d F)) : GL (Fin d) F) = eGL (x : GL (Fin d) F) := by
    intro x
    rw [show eSU x = (MulEquiv.subgroupCongr hmapSU)
      ((eGL.subgroupMap (UniSU n d F)) x) from rfl]
    rw [MulEquiv.subgroupCongr_apply]
    exact MulEquiv.coe_subgroupMap_apply eGL (UniSU n d F) x
  have heSU_mem : ∀ x : ↥(UniSU n d F), x ∈ sc → eSU x = x := by
    intro x hx
    apply Subtype.ext
    rw [heSU_coe]
    obtain ⟨c, hc⟩ := hx
    have hxc : (x : GL (Fin d) F) = Matrix.GeneralLinearGroup.scalar (Fin d) c := hc.symm
    rw [hxc]
    dsimp only [eGL]
    rw [MulAut.conj_apply]
    calc
      g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin d) c * g
          = g⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin d) c * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * Matrix.GeneralLinearGroup.scalar (Fin d) c) := by
            rw [Matrix.GeneralLinearGroup.scalar_commute c g]
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
            rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hscmap : sc.map eSU.toMonoidHom = sc := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change eSU x ∈ sc
      rw [heSU_mem x hx]
      exact hx
    · intro hy
      exact ⟨y, hy, by
        change eSU y = y
        exact heSU_mem y hy⟩
  let γ : UniPSU n d F ≃* UniPSU n d F :=
    QuotientGroup.congr sc sc eSU hscmap
  let ψ : Q ≃* UniPSU n d F := θ.trans γ
  have hγ_mk : ∀ x : ↥(UniSU n d F), γ (UniMk n d F x) = UniMk n d F (eSU x) := by
    intro x
    exact QuotientGroup.congr_mk' sc sc eSU hscmap x
  have hA_SU : A.subgroupOf (UniSU n d F) = A₁.map eSU.toMonoidHom := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      dsimp only [A] at hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
      dsimp only [A1GL] at hy
      rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
      refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
      apply Subtype.ext
      change ((eSU z : ↥(UniSU n d F)) : GL (Fin d) F) = (x : GL (Fin d) F)
      rw [heSU_coe]
      dsimp only [eGL]
      exact hyx
    · rintro ⟨z, hz, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      dsimp only [A]
      refine Subgroup.mem_map.mpr ⟨(z : GL (Fin d) F),
        Subgroup.mem_map_of_mem (UniSU n d F).subtype hz, ?_⟩
      change eGL (z : GL (Fin d) F) =
        ((eSU z : ↥(UniSU n d F)) : GL (Fin d) F)
      rw [heSU_coe]
  have hA_rel : (A.subgroupOf (UniSU n d F)).map (UniMk n d F) = E.map γ.toMonoidHom := by
    rw [hA_SU, Subgroup.map_map]
    have hcomp : (UniMk n d F).comp eSU.toMonoidHom =
        γ.toMonoidHom.comp (UniMk n d F) := by
      ext x
      exact hγ_mk x
    rw [hcomp, ← Subgroup.map_map, hA₁map]
  have hBbar_rel : Bbar.map ψ.toMonoidHom = E.map γ.toMonoidHom := by
    change Bbar.map (γ.toMonoidHom.comp θ.toMonoidHom) = E.map γ.toMonoidHom
    rw [← Subgroup.map_map]
  exact ⟨ψ, A, hA_le, hAe, hAd, by rw [hBbar_rel, hA_rel]⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end

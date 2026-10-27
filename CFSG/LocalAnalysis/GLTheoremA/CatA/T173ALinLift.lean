module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
import CFSG.Assembly.GL83StatedBridge
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.SignalizerFunctor.SurjectiveSylowLifting

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

private theorem lin_eq_one_of_mem_scalars_of_pow_eq_one {p d : ℕ} {F : Type} [Field F]
    (hp : p.Prime) (hpd : ¬ p ∣ d) {x : ↥(LinSL d F)}
    (hxsc : (x : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F)
    (hpow : ∃ k : ℕ, x ^ p ^ k = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hpow
  obtain ⟨c, hc⟩ := hxsc
  have hcx : (x : GL (Fin d) F) = Matrix.GeneralLinearGroup.scalar (Fin d) c := hc.symm
  have hxdet : ((x : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det = 1 := by
    have hmem : (x : GL (Fin d) F) ∈ StatedSL d F := by
      rw [← largeEvenSLGroup_eq_statedSL]
      exact x.2
    exact StatedAPI.det_of_mem_statedSL hmem
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

theorem lin_lift_torsion {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : LinArith p n d F)
    {B : Subgroup (LinPSL d F)} (hB : IsElemAbelian p B) :
    ∃ A₀ : Subgroup (GL (Fin d) F), A₀ ≤ LinSL d F ∧ IsElemAbelian p A₀ ∧
      (A₀.subgroupOf (LinSL d F)).map (LinMk d F) = B := by
  classical
  obtain ⟨hp, -, -, hpd, -, -, -⟩ := h
  let sc : Subgroup ↥(LinSL d F) := (LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F)
  let Ppre : Subgroup ↥(LinSL d F) := B.comap (LinMk d F)
  let f : Ppre →* B :=
    ((LinMk d F).comp Ppre.subtype).codRestrict B fun x => by
      have hx := x.2
      change (LinMk d F) (x : ↥(LinSL d F)) ∈ B at hx
      exact hx
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective sc (b : LinPSL d F)
    refine ⟨⟨y, ?_⟩, ?_⟩
    · show (LinMk d F) y ∈ B
      rw [show (LinMk d F) y = (b : LinPSL d F) from hy]
      exact b.2
    · apply Subtype.ext
      exact hy
  obtain ⟨A₀, hA₀map⟩ :=
    CFSG.SignalizerFunctor.Helpers.surjective_pgroup_sylow_lift p hp f hf hB.isPGroup
  let A₁ : Subgroup ↥(LinSL d F) := (A₀ : Subgroup Ppre).map Ppre.subtype
  have hA₁p : IsPGroup p A₁ := A₀.isPGroup'.map Ppre.subtype
  have hA₁map : A₁.map (LinMk d F) = B := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases Subgroup.mem_map.mp hx with ⟨a, _, rfl⟩
      exact (f a).2
    · intro b hb
      have htop : (⟨b, hb⟩ : B) ∈ (A₀ : Subgroup Ppre).map f := by
        rw [hA₀map]
        exact Subgroup.mem_top _
      obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp htop
      refine Subgroup.mem_map.mpr ⟨Ppre.subtype x,
        Subgroup.mem_map_of_mem Ppre.subtype hx, ?_⟩
      exact congrArg Subtype.val hfx
  have hker : A₁ ⊓ (LinMk d F).ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxker⟩
    have hxsc : (x : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
      have hxsc' : x ∈ sc := by
        simpa [sc, LinMk, LargeEvenProjMk, QuotientGroup.ker_mk'] using hxker
      exact Subgroup.mem_subgroupOf.mp hxsc'
    obtain ⟨k, hk⟩ := hA₁p ⟨x, hxA⟩
    have hkx : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact lin_eq_one_of_mem_scalars_of_pow_eq_one hp hpd hxsc ⟨k, hkx⟩
  have hinj : ∀ x ∈ A₁, ∀ y ∈ A₁, LinMk d F x = LinMk d F y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ A₁ ⊓ (LinMk d F).ker := by
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
      have hma : (LinMk d F) a.1 ∈ B := by
        rw [← hA₁map]
        exact Subgroup.mem_map_of_mem (LinMk d F) a.2
      have hmb : (LinMk d F) b.1 ∈ B := by
        rw [← hA₁map]
        exact Subgroup.mem_map_of_mem (LinMk d F) b.2
      rw [map_mul, map_mul]
      exact hB.comm hma hmb
    · have hm : (LinMk d F) x ∈ B := by
        rw [← hA₁map]
        exact Subgroup.mem_map_of_mem (LinMk d F) hx
      apply hinj (x ^ p) (A₁.pow_mem hx p) 1 A₁.one_mem
      rw [map_pow, map_one]
      exact hB.2 _ hm
  have hsub : (A₁.map (LinSL d F).subtype).subgroupOf (LinSL d F) = A₁ := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rwa [show y = x from Subtype.ext hyx] at hy
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem (LinSL d F).subtype hx
  exact ⟨A₁.map (LinSL d F).subtype, Subgroup.map_subtype_le A₁, hA₁e.map _, by
    rw [hsub, hA₁map]⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
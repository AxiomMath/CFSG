module

public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.RankThree.PartOne.RF4.Descent

public noncomputable section

namespace CFSG.LieType.AschbacherSeitz

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem exists_eq_inv_mul_finiteReeAut_of_eq_inv {m : ℕ}
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * m + 1))
    {h : adjointGroup ReeTag.F4.tag K}
    (hh : ReeTag.F4.finiteReeAut K m h = h⁻¹) :
    ∃ u : adjointGroup ReeTag.F4.tag K, h = u⁻¹ * ReeTag.F4.finiteReeAut K m u := by
  classical
  let L := AlgebraicClosure K
  haveI : IsAlgClosure K L := inferInstance
  obtain ⟨S₀, hLang, hS₀, -, Frq, hFrq, hsq⟩ :=
    CFSG.RankThree.PartOne.RF4.reeF4_lang_data (K := K) L (a := m) (b := m) (p := 1) hK
      (by omega)
  let S : MulAut (adjointGroup ReeTag.F4.tag L) := S₀
  set ι := adjointBaseChangeHom ReeTag.F4.tag (algebraMap K L) with hιdef
  obtain ⟨y, hy⟩ := hLang (ι h)
  let u : adjointGroup ReeTag.F4.tag L := y
  have hu : ι h = u⁻¹ * S u := hy
  have hS₀h : S (ι h) = (ι h)⁻¹ := by
    have h1 : S (ι h) = ι (ReeTag.F4.finiteReeAut K m h) := by
      have h2 := hS₀ h
      rwa [← CFSG.RankThree.PartOne.RF4.finiteReeAut_eq_pow m] at h2
    rw [h1, hh]
    exact map_inv ι h
  have hSq : S (S u) = u := by
    have h1 : S u = u * ι h := by
      rw [hu]
      group
    calc S (S u) = S (u * ι h) := by rw [h1]
      _ = S u * S (ι h) := map_mul S u (ι h)
      _ = u * ι h * (ι h)⁻¹ := by rw [h1, hS₀h]
      _ = u := by group
  have hfix : Units.map (entrywiseHom Frq) (u : ModGL ReeTag.F4.tag L) =
      (u : ModGL ReeTag.F4.tag L) := by
    have h1 := hsq u
    rw [pow_one] at h1
    change (((S (S u) : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L)) =
      Units.map (entrywiseHom Frq) (u : ModGL ReeTag.F4.tag L) at h1
    rw [hSq] at h1
    exact h1.symm
  let y' : adjointGroup Tag.F4 L := u
  have hy' : Units.map (entrywiseHom Frq) (y' : ModGL Tag.F4 L) = (y' : ModGL Tag.F4 L) := hfix
  obtain ⟨u₀, hu₀, huu₀⟩ :=
    CFSG.RankThree.PartOne.RF4.mem_range_baseChange_of_frobenius_fixed (K := K) L Frq hFrq y' hy'
  have hu_eq : u = ι ⟨u₀, hu₀⟩ := Subtype.ext huu₀.symm
  have hS₀u : S (ι ⟨u₀, hu₀⟩) = ι (ReeTag.F4.finiteReeAut K m ⟨u₀, hu₀⟩) := by
    have h1 := hS₀ ⟨u₀, hu₀⟩
    rwa [← CFSG.RankThree.PartOne.RF4.finiteReeAut_eq_pow m] at h1
  refine ⟨⟨u₀, hu₀⟩, ?_⟩
  have hmain : ι h = ι (⟨u₀, hu₀⟩⁻¹ * ReeTag.F4.finiteReeAut K m ⟨u₀, hu₀⟩) := by
    rw [hu, hu_eq, hS₀u]
    simp only [map_mul, map_inv]
  exact adjointBaseChangeHom_injective ReeTag.F4.tag (algebraMap K L) hmain

theorem exists_eq_conj_mul_finiteReeAut_of_involution {f m : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ f) (hm : f = 2 * m + 1)
    {α : MulAut (adjointGroup ReeTag.F4.tag K)} (hα : α ^ 2 = 1)
    (hout : α ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range) :
    ∃ h : adjointGroup ReeTag.F4.tag K, α = MulAut.conj h * ReeTag.F4.finiteReeAut K m := by
  obtain ⟨-, hNF, -, hinv, -, -, hodd⟩ :=
    even_F4_exact_automorphism_normal_form (f := f) hf K hK
  obtain ⟨⟨h, k⟩, hgk, -⟩ := hNF α
  have hk := hinv α h (k : ℕ) k.2 hgk hα
  obtain ⟨-, hφ, -⟩ := hodd m hm
  rcases hk with hk0 | hkf
  · exfalso
    apply hout
    refine ⟨h, ?_⟩
    rw [show (k : ℕ) = 0 from hk0, pow_zero, mul_one] at hgk
    exact hgk.symm
  · refine ⟨h, ?_⟩
    rw [hkf, hφ] at hgk
    exact hgk

end CFSG.LieType.AschbacherSeitz

end

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni CFSG.LocalAnalysis.GLTheoremA Matrix
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup exists_glaPComponent_map_fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU hct_heldSU_eq_statedSU)

theorem fstdUniLift {K : Type} [Field K] [Finite K] {k d : ℕ} {τ : K ≃+* K}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ k) (hK : Nat.card K = (2 ^ k) ^ 2)
    (hd : 3 ≤ d) (A : GL (Fin d) K) (hA : A ∈ heldGU d K τ hτ)
    (hA3 : ∃ c : K, ((A ^ 3 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      c • (1 : Matrix (Fin d) (Fin d) K))
    (u : MulAut (LargeEvenProj (StatedSU d (2 ^ k) K)))
    (hu : ∀ h h' : ↥(StatedSU d (2 ^ k) K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ k) K) h) = LargeEvenProjMk (StatedSU d (2 ^ k) K) h')
    (J : Subgroup (LargeEvenProj (StatedSU d (2 ^ k) K)))
    (hJ : GLAPComponent 3 (fixSubgroup u) J) :
    ∃ M : Subgroup (GL (Fin d) K),
      CFSG.Open.IsComponentOf M
        (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ heldSU d K τ hτ) ∧
      Nonempty (PSimple 3 J ≃* M ⧸ Subgroup.center M) ∧ Nat.card ↥J ≤ Nat.card ↥M := by
  obtain ⟨c0, hc0⟩ := hA3
  have h2 : (2 : K) = 0 := two_eq_zero_of_card (K := K) (n := k) hK
  have hH : heldSU d K τ hτ = StatedSU d (2 ^ k) K := hct_heldSU_eq_statedSU (a := d) hτQ
  have hnorm : ∀ g : GL (Fin d) K, g ∈ heldGU d K τ hτ →
      ∀ x ∈ StatedSU d (2 ^ k) K, g * x * g⁻¹ ∈ StatedSU d (2 ^ k) K := by
    intro g hg x hx
    rw [← hH] at hx ⊢
    exact heldSU_normal_in_heldGU hτ g hg x hx
  let cA : MulAut ↥(StatedSU d (2 ^ k) K) :=
    uniConjSub (StatedSU d (2 ^ k) K) A (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))
  have hodd : Odd (orderOf A) :=
    odd_orderOf_of_pow_scalar h2 (by omega : 1 ≤ d) A
      (Nat.prime_three.odd_of_ne_two (by norm_num)) hc0
  have hord : ((orderOf A : ℕ) : K) ≠ 0 :=
    cast_orderOf_ne_zero_of_odd h2 A hodd
  obtain ⟨M₀, hM₀, hM₀J⟩ := exists_glaPComponent_map_fixSubgroup
    (LargeEvenProjMk (StatedSU d (2 ^ k) K)) (ker_projMk_uni_le_center (StatedSU d (2 ^ k) K))
    cA u (fun m => (hu m (cA m) rfl).symm) QuotientGroup.mk_surjective Nat.prime_three hJ
  have hMinj : Function.Injective (StatedSU d (2 ^ k) K).subtype := Subtype.val_injective
  have hM' : GLAPComponent 3
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSU d (2 ^ k) K)
      (M₀.map (StatedSU d (2 ^ k) K).subtype) := by
    rw [← map_fixSubgroup_uniConjSub (StatedSU d (2 ^ k) K) A
      (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))]
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff
      Nat.prime_three hMinj).mpr hM₀
  have hcomp : CFSG.Open.IsComponentOf (M₀.map (StatedSU d (2 ^ k) K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSU d (2 ^ k) K) :=
    uniPCompIsComp_holds K (2 ^ k) d 3 τ hτ hτQ hK Nat.prime_three A hA hord _ hM'
  have hcompH : CFSG.Open.IsComponentOf (M₀.map (StatedSU d (2 ^ k) K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ heldSU d K τ hτ) := by
    rw [hH]
    exact hcomp
  let M : Subgroup (GL (Fin d) K) := M₀.map (StatedSU d (2 ^ k) K).subtype
  let e : ↥M₀ ≃* ↥M := Subgroup.equivMapOfInjective M₀ (StatedSU d (2 ^ k) K).subtype hMinj
  have hmemJ : ∀ x : ↥M₀,
      LargeEvenProjMk (StatedSU d (2 ^ k) K) (x : ↥(StatedSU d (2 ^ k) K)) ∈ J := fun x => by
    rw [← hM₀J]
    exact Subgroup.mem_map_of_mem _ x.2
  let fJ : ↥M₀ →* ↥J :=
    MonoidHom.codRestrict ((LargeEvenProjMk (StatedSU d (2 ^ k) K)).comp M₀.subtype) J hmemJ
  have hfJ : Function.Surjective fJ := by
    rintro ⟨y, hy⟩
    rw [← hM₀J] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, rfl⟩
  refine ⟨M, hcompH, ?_, ?_⟩
  · let f : ↥M →* PQuot 3 J :=
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)).comp (fJ.comp e.symm.toMonoidHom)
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J) y
      obtain ⟨w, rfl⟩ := hfJ z
      refine ⟨e w, ?_⟩
      change (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) (fJ (e.symm (e w))) =
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) (fJ w)
      rw [MulEquiv.symm_apply_apply]
    have hker : f.ker ≤ Subgroup.center ↥M :=
      le_center_of_normal_of_isQuasisimple hcomp.2.2 (inferInstance : f.ker.Normal) (by
        intro htop
        have htriv : ∀ x : ↥M, f x = 1 := fun x =>
          MonoidHom.mem_ker.mp (by rw [htop]; exact Subgroup.mem_top x)
        haveI hnt : Nontrivial (PQuot 3 J) :=
          CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial
            (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ)
        obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
        obtain ⟨x, hx⟩ := hf a
        obtain ⟨y, hy⟩ := hf b
        apply hab
        rw [← hx, ← hy, htriv x, htriv y])
    obtain ⟨φ⟩ := center_quot_equiv_of_surjective hcomp.2.2.1 f hf hker
    exact ⟨φ⟩
  · calc Nat.card ↥J ≤ Nat.card ↥M₀ := Nat.card_le_card_of_surjective fJ hfJ
      _ = Nat.card ↥M := Nat.card_congr e.toEquiv

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end

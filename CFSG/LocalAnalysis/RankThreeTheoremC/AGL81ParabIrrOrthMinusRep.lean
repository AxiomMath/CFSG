module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrGeneric
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthMinusKer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus

open Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

local notation "𝕍" => (Fin r ⊕ Fin r → K) × (Fin 2 → K)

theorem flag_of_stable (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hd : OrthCuts r d)
    {α : MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))}
    (hα : ∀ x ∈ orthParab r (minusTailForm K b c) d, α x ∈ orthParab r (minusTailForm K b c) d)
    (S : SemiData K r b c) (hS : S.Induces α) (i : Fin (s + 1)) (v : 𝕍) :
    S.F v ∈ tailFlag K (Fin 2 → K) r (d i) ↔ v ∈ tailFlag K (Fin 2 → K) r (d i) := by
  classical
  haveI : Finite (𝕍 ≃ₗ[K] 𝕍) := finite_orthLinearEquiv
  have hnorm : ∀ u ∈ orthParab r (minusTailForm K b c) d,
      ∃ x ∈ orthParab r (minusTailForm K b c) d, ∀ v,
        ((u : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍) v =
          S.F (((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
            𝕍 ≃ₗ[K] 𝕍) (S.F.symm v)) := by
    intro u hu
    let φ : ↥(orthParab r (minusTailForm K b c) d) → ↥(orthParab r (minusTailForm K b c) d) :=
      fun x => ⟨α x, hα x x.2⟩
    have hinj : Function.Injective φ := fun x y h =>
      Subtype.ext (α.injective (congrArg Subtype.val h))
    obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.1 hinj ⟨u, hu⟩
    refine ⟨x, x.2, fun v => ?_⟩
    have h1 : α (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) = u :=
      congrArg Subtype.val hx
    have h2 := hS (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))))
    rw [h1] at h2
    rw [h2]
    rfl
  exact mem_flag_iff_of_normalizes hirr hd S.hF S.hFQ hnorm i v

theorem isConjBy_semilinConj {α_n α_x α_y : MulAut ↥(orthElementaryGroup (quadTail r
      (minusTailForm K b c)))} (hy : α_y = α_n * α_x * α_n⁻¹) {S : SemiData K r b c}
    (hS : S.Induces α_n) {f : 𝕍 ≃ₗ[K] 𝕍} (hf : IsConjBy α_x f) :
    IsConjBy α_y (semilinConj S.F S.σ S.hF f) := by
  intro g
  have h1 : semilinConj S.F S.σ S.hF
      ((α_n⁻¹ g : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍) =
        (g : 𝕍 ≃ₗ[K] 𝕍) := by
    rw [← hS (α_n⁻¹ g), MulAut.apply_inv_self]
  rw [hy, MulAut.mul_apply, MulAut.mul_apply, hS, hf (α_n⁻¹ g), map_mul, map_mul, map_inv, h1]

variable {A : Type} [Group A] [Finite A] {Y P B N : Subgroup A} {p : ℕ}

theorem autHom_eq_one_of_irred (hp : p.Prime) (hp2 : p ≠ 2) (hr : 3 ≤ r)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hd : OrthCuts r d)
    (C : OmCover Y P r K b c d) (hPY : P ≤ Y)
    (hbig : (∃ l : Fin s, 2 ≤ d l.succ - d l.castSucc) ∨ 1 ≤ r - d (Fin.last s))
    (hB : IsPGroup p ↥B) (hcyc : ¬ IsCyclic ↥B) (hBY : B ≤ Subgroup.normalizer (Y : Set A))
    (hBP : B ≤ Subgroup.normalizer (P : Set A)) (hW : ∀ β ∈ B, WCent P β)
    (hNY : N ≤ Subgroup.normalizer (Y : Set A)) (hNP : N ≤ Subgroup.normalizer (P : Set A))
    (hNB : N ≤ Subgroup.normalizer (B : Set A)) (hirrN : IrredOn N B) (x : ↥B) :
    C.autHom ⟨(x : A), hBY x.2⟩ = 1 := by
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  let αB : ↥B →* MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) :=
    C.autHom.comp (Subgroup.inclusion hBY)
  have hαB : ∀ y : ↥B, αB y = C.autHom ⟨(y : A), hBY y.2⟩ := fun y => rfl
  have hex : ∀ y : ↥B, ∃ f : 𝕍 ≃ₗ[K] 𝕍, IsConjBy (αB y) f ∧ GoodIso b c hd f := by
    intro y
    obtain ⟨k, hk⟩ := hB y
    have hk' : ((⟨(y : A), hBY y.2⟩ : ↥(Subgroup.normalizer (Y : Set A))) : A) ^ p ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    rw [hαB]
    exact exists_isometry hr hirr hd hbig (C.odd_orderOf_autHom _ hp_odd hk')
      (C.omNormFix_autHom hd hr hirr hPY _ (hBP y.2) (hW y y.2))
  choose fl0 hconj hgood using hex
  let fl : ↥B →* (𝕍 ≃ₗ[K] 𝕍) := MonoidHom.mk' fl0 fun y z => by
    refine isometry_unique hr hirr (α := αB (y * z)) (hgood (y * z)).iso (f' := fl0 y * fl0 z)
      (fun v => ?_) (hconj (y * z)) ?_
    · rw [LinearEquiv.mul_apply, (hgood y).iso, (hgood z).iso]
    · rw [map_mul]
      exact (hconj y).mul (hconj z)
  have hflgood : ∀ y, GoodIso b c hd (fl y) := fun y => hgood y
  have hN : NActs B N hd fl := by
    intro n hn
    obtain ⟨S, hS⟩ := exists_semiData hr hirr (C.autHom ⟨n, hNY hn⟩)
    have hflag := flag_of_stable hr hirr hd
      (fun u hu => C.autHom_mem_orthParab ⟨n, hNY hn⟩ (hNP hn) hu) S hS
    refine ⟨S.σ, S.F, S.hF, hflag, fun v => isResPerp_iff S hd.last (hflag (Fin.last s)) v, ?_⟩
    intro y z hyz
    have hzN : (⟨(z : A), hBY z.2⟩ : ↥(Subgroup.normalizer (Y : Set A))) =
        ⟨n, hNY hn⟩ * ⟨(y : A), hBY y.2⟩ * ⟨n, hNY hn⟩⁻¹ := Subtype.ext hyz.symm
    have hαz : αB z = C.autHom ⟨n, hNY hn⟩ * αB y * (C.autHom ⟨n, hNY hn⟩)⁻¹ := by
      rw [hαB, hαB, hzN, map_mul, map_mul, map_inv]
    refine isometry_unique hr hirr (α := αB z) (hgood z).iso ?_ (hconj z)
      (isConjBy_semilinConj hαz hS (hconj y))
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1
      (semilinConj_mem_orthogonalGroup S.F S.σ S.hF S.μ S.hFQ
        (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 (hgood y).iso))
  have h1 := forall_fl_eq_one hp hp2 hirr hB hcyc hirrN hNB hd fl hflgood hN x
  rw [← hαB]
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [hconj x g, show fl0 x = 1 from h1]
  simp

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus

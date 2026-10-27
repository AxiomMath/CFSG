module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292XSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open scoped commutatorElement
open P614K292

namespace P614K292X

section Lifts

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

@[expose] def liftSubgroup (M : LModel L π p f K ν) : Subgroup X where
  carrier := {g | ∃ c : GL (Fin 3) K, IsLiftAt ν g c}
  one_mem' := ⟨1, isLiftAt_one_of_mem_centralizer (one_mem _)⟩
  mul_mem' := by
    rintro _ _ ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, hc.mul M hd⟩
  inv_mem' := by
    rintro _ ⟨c, hc⟩
    exact ⟨c⁻¹, hc.inv⟩

theorem mem_liftSubgroup (M : LModel L π p f K ν) {g : X} :
    g ∈ liftSubgroup M ↔ ∃ c : GL (Fin 3) K, IsLiftAt ν g c :=
  Iff.rfl

theorem commutator_liftSubgroup_le (M : LModel L π p f K ν) :
    ⁅liftSubgroup M, liftSubgroup M⁆ ≤ L ⊔ centralizer (L : Set X) := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨c₁, h₁⟩ := (mem_liftSubgroup M).1 hg₁
  obtain ⟨c₂, h₂⟩ := (mem_liftSubgroup M).1 hg₂
  have h : IsLiftAt ν ⁅g₁, g₂⁆ ⁅c₁, c₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    exact ((h₁.mul M h₂).mul M h₁.inv).mul M h₂.inv
  have hmem : ⁅c₁, c₂⁆ ∈ slPi π 3 (p ^ f) K := by
    rw [mem_slPi_iff M.hπ]
    refine ⟨h.mem, ?_⟩
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _), Units.val_one]
  obtain ⟨l, hl, hlc⟩ := h.exists_of_isInnerMat M ⟨_, hmem, 1, one_mem _, (mul_one _).symm⟩
  have h' := Subgroup.mul_mem_sup hl hlc
  rwa [mul_inv_cancel_left] at h'

theorem derivedSeries_two_le (M : LModel L π p f K ν)
    (hcomm : ∀ g h : X, ∃ c : GL (Fin 3) K, IsLiftAt ν (g * h * g⁻¹ * h⁻¹) c) :
    derivedSeries X 2 ≤ L ⊔ centralizer (L : Set X) := by
  have h1 : derivedSeries X 1 ≤ liftSubgroup M := by
    rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [commutatorElement_def]
    exact hcomm g₁ g₂
  rw [show (2 : ℕ) = 1 + 1 from rfl, derivedSeries_succ]
  exact (Subgroup.commutator_mono h1 h1).trans (commutator_liftSubgroup_le M)

end Lifts

section Normalizer

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X} {B : Subgroup X} {π : Bool}
  {p f : ℕ} {K : Type} [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L} {y : GL (Fin 3) K}
  {v : Fin 3 → K}

theorem le_normalizer_threeFrameIn (M : LModel L π p f K ν) (hν : Function.Injective ν)
    (hlift : IsLiftAt ν x y) (hplane : B = zpowers x ⊔ (center ↥L).map L.subtype)
    (hFy : ∀ e ∈ threeFrame y v, y * e * y⁻¹ ∈ threeFrame y v) :
    B ≤ normalizer (threeFrameIn ν y v : Set X) := by
  rw [hplane]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem fun k hk => ?_
    obtain ⟨t, ht, rfl⟩ := mem_threeFrameIn.1 hk
    rw [hlift.act t (M.conjBy hlift.mem t) (M.coe_conjBy hlift.mem t),
      coe_mem_threeFrameIn_iff hν, M.coe_conjBy]
    exact hFy t ht
  · rintro _ ⟨c, hc, rfl⟩
    exact mem_normalizer_threeFrameIn_of_commute fun l hl =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨l, hl⟩)

theorem isSolvable_normalizer_threeFrameIn (M : LModel L π p f K ν) (hν : Function.Injective ν)
    [L.Normal] (hcent : centralizer (L : Set X) = CFSG.pCore 3 X)
    (hcomm : ∀ g h : X, ∃ c : GL (Fin 3) K, IsLiftAt ν (g * h * g⁻¹ * h⁻¹) c)
    (hFSL : threeFrame y v ≤ slPi π 3 (p ^ f) K) (h9 : Nat.card (threeFrame y v) = 9)
    (hsol : Group.IsSolvable
      ↥(slPi π 3 (p ^ f) K ⊓ normalizer (threeFrame y v : Set (GL (Fin 3) K)))) :
    Group.IsSolvable ↥(normalizer (threeFrameIn ν y v : Set X)) := by
  set N := normalizer (threeFrameIn ν y v : Set X)
  set C := centralizer (L : Set X)
  set S := slPi π 3 (p ^ f) K ⊓ normalizer (threeFrame y v : Set (GL (Fin 3) K))
  haveI : Group.IsSolvable ↥C := by
    rw [hcent]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI := (CFSG.pCore_isPGroup (p := 3) (G := X)).isNilpotent
    infer_instance
  let f₁ : ↥S →* X := L.subtype.comp (ν.comp (Subgroup.inclusion inf_le_left))
  have hcomm₁ : ∀ s c, Commute (f₁ s) (C.subtype c) := fun s c =>
    (Subgroup.mem_centralizer_iff.1 c.2 _ (ν _).2)
  let μ : ↥S × ↥C →* X := f₁.noncommCoprod C.subtype hcomm₁
  haveI : Group.IsSolvable ↥μ.range := Group.isSolvable_of_surjective μ.rangeRestrict_surjective
  have hD : derivedSeries ↥N 2 ≤ μ.range.comap N.subtype := by
    intro d hd
    have hdX : (d : X) ∈ derivedSeries X 2 :=
      map_derivedSeries_le_derivedSeries N.subtype 2 ⟨d, hd, rfl⟩
    obtain ⟨l, hl, c, hc, hlc⟩ := mem_sup_of_normal_left.1 (derivedSeries_two_le M hcomm hdX)
    have hcN : c ∈ N := mem_normalizer_threeFrameIn_of_commute
      (Subgroup.mem_centralizer_iff.1 hc)
    have hlN : l ∈ N := by
      have : l = (d : X) * c⁻¹ := by rw [← hlc, mul_inv_cancel_right]
      rw [this]
      exact mul_mem d.2 (inv_mem hcN)
    obtain ⟨s, hs⟩ := M.surj ⟨l, hl⟩
    have hsl : ((ν s : ↥L) : X) = l := congrArg Subtype.val hs
    have hsN : (s : GL (Fin 3) K) ∈ normalizer (threeFrame y v : Set (GL (Fin 3) K)) :=
      coe_mem_normalizer_threeFrame hν hFSL h9 (by rw [hsl]; exact hlN)
    refine ⟨(⟨s, s.2, hsN⟩, ⟨c, hc⟩), ?_⟩
    rw [MonoidHom.noncommCoprod_apply]
    exact (congrArg (· * c) hsl).trans hlc
  let ψ : ↥(μ.range.comap N.subtype) →* ↥μ.range :=
    (N.subtype.comp (μ.range.comap N.subtype).subtype).codRestrict μ.range fun z => z.2
  have hψ : Function.Injective ψ := fun a b h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  haveI : Group.IsSolvable ↥(μ.range.comap N.subtype) := Group.isSolvable_of_isSolvable_injective hψ
  exact isSolvable_of_derivedSeries_le hD

end Normalizer

end P614K292X

open P614K292X

theorem kD292FrameNormX3_holds : KD292FrameNormX3 := by
  intro h5 X _ _ L x Px B π p f K _ ν y hcfg hS v hv horth
  have M := hS.model
  obtain ⟨hF, hconj, hind, hsol, -⟩ :=
    h5 π p f K y M.piField M.modThree M.two_lt hS.typeThree v hv horth
  haveI := hcfg.setup.normal
  obtain ⟨hFSL, -, hF9, -, hFy⟩ := id hF
  exact ⟨le_normalizer_threeFrameIn M hS.inj hS.lift hS.plane hFy,
    isSolvable_normalizer_threeFrameIn M hS.inj hS.cent hS.comm hFSL hF9 hsol,
    exists_sylow_le_normalizer M hS.inj hF hconj hind⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

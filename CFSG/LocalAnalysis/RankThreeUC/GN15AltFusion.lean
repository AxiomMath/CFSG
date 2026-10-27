module

import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.NaturalOn
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltModData

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThree.PartTwo
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
open Equiv Equiv.Perm
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)} {n : ℕ}
  {g : ↥L →* alternatingGroup (Fin n)}

theorem isMaxElemAbelian_conjSub_of_conjSub_le {A : Subgroup X} (hA : IsMaxElemAbelian T A) {c : X}
    (hcT : B6.conjSub c A ≤ T) : IsMaxElemAbelian T (B6.conjSub c A) := by
  obtain ⟨hAT, hAe, hmax⟩ := hA
  have hmap : B6.conjSub c A = A.map (MulAut.conj c).toMonoidHom := rfl
  have hcard : Nat.card (B6.conjSub c A) = Nat.card A := by
    rw [hmap]
    exact Subgroup.card_map_of_injective (MulAut.conj c).injective
  refine ⟨hcT, ?_, fun B hBT hBe => ?_⟩
  · rw [hmap]
    exact CFSG.Open.IsElemAbelian.map hAe _
  · rw [hcard]
    exact hmax B hBT hBe

omit [Finite X] in
theorem gnAlt_mem_normalizer_of_forall_conj_mem {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  classical
  let f : ↥H → ↥H := fun x => ⟨g * x * g⁻¹, h x x.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    simp only [f] at this
    exact Subtype.ext (by simpa using this)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hinj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  obtain ⟨y, hy⟩ := hsurj ⟨g * x * g⁻¹, hx⟩
  have := congrArg Subtype.val hy
  simp only [f] at this
  have hxy : (y : G) = x := by simpa using this
  rw [← hxy]
  exact y.2

namespace GNAltModData

variable (S : GNAltModData T L g)

theorem exists_mem_T_of_mem_Q_alt (hX : GNSetting X T) (hL : IsComponentOf L ⊤)
    {μ : Perm (Fin n)} (hμQ : μ ∈ S.Q) (hμA : μ ∈ alternatingGroup (Fin n)) :
    ∃ k : X, k ∈ T ∧ ∃ hk : toStar T k ∈ L, (g ⟨toStar T k, hk⟩ : Perm (Fin n)) = μ := by
  classical
  have hSyl : IsSylowTwoOf (gnImg T T ⊓ L) L :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' hL.2.1 (isSylowTwoOf_gnImg_top hX)
  let f₀ : ↥L →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp g
  have hf₀ : Function.Injective f₀ := (alternatingGroup (Fin n)).subtype_injective.comp S.g_bij.1
  have hrange : Subgroup.map f₀ ⊤ = alternatingGroup (Fin n) := by
    ext σ
    constructor
    · rintro ⟨l, -, rfl⟩
      exact (g l).2
    · intro hσ
      obtain ⟨l, hl⟩ := S.g_bij.2 ⟨σ, hσ⟩
      exact ⟨l, Subgroup.mem_top _, by simp [f₀, hl]⟩
  set P₀ : Subgroup (Perm (Fin n)) := Subgroup.map f₀ ((gnImg T T ⊓ L).subgroupOf L) with hP₀
  have hP₀Q : P₀ ≤ S.Q := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy).1
    have hyL : toStar T t ∈ L := by rw [hty]; exact y.2
    have htN : t ∈ Subgroup.normalizer (gnPre T L : Set X) := Subgroup.le_normalizer hyL
    refine ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.2 ⟨ht, htN⟩, ?_⟩
    have h1 := S.ρ_pre ⟨t, hyL⟩ hyL
    show S.ρ ⟨t, htN⟩ = f₀ y
    rw [h1]
    have : (⟨toStar T t, hyL⟩ : ↥L) = y := Subtype.ext hty
    rw [this]
    rfl
  have hP₀A : P₀ ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨y, -, rfl⟩
    exact (g y).2
  have hP₀idx : ¬ 2 ∣ P₀.relIndex (alternatingGroup (Fin n)) := by
    rw [← hrange, Subgroup.relIndex_map_map_of_injective _ _ hf₀, Subgroup.relIndex_top_right]
    exact hSyl.2.2
  have hH2 : IsPGroup 2 ↥(S.Q ⊓ alternatingGroup (Fin n)) := S.sylow.1.to_le inf_le_left
  have hle : P₀ ≤ S.Q ⊓ alternatingGroup (Fin n) := le_inf hP₀Q hP₀A
  have hmul := Subgroup.relIndex_mul_relIndex P₀ (S.Q ⊓ alternatingGroup (Fin n))
    (alternatingGroup (Fin n)) hle inf_le_right
  have hodd : ¬ 2 ∣ P₀.relIndex (S.Q ⊓ alternatingGroup (Fin n)) := fun hd =>
    hP₀idx (hmul ▸ hd.mul_right _)
  have hpow : ∃ k : ℕ, P₀.relIndex (S.Q ⊓ alternatingGroup (Fin n)) = 2 ^ k :=
    hH2.index (P₀.subgroupOf (S.Q ⊓ alternatingGroup (Fin n)))
  obtain ⟨k, hk⟩ := hpow
  have hk0 : k = 0 := by
    by_contra hk0
    exact hodd (by rw [hk]; exact dvd_pow_self 2 hk0)
  have h1 : P₀.relIndex (S.Q ⊓ alternatingGroup (Fin n)) = 1 := by rw [hk, hk0, pow_zero]
  have hmem : μ ∈ P₀ := (Subgroup.relIndex_eq_one.1 h1) ⟨hμQ, hμA⟩
  obtain ⟨y, hy, hyμ⟩ := hmem
  obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy).1
  have hyL : toStar T t ∈ L := by rw [hty]; exact y.2
  refine ⟨t, ht, hyL, ?_⟩
  have : (⟨toStar T t, hyL⟩ : ↥L) = y := Subtype.ext hty
  rw [this]
  exact hyμ

theorem conj_mem_sup_gnC (hX : GNSetting X T) (hL : IsComponentOf L ⊤)
    {l a : X} (hl : toStar T l ∈ L) (haT : a ∈ T)
    (haN : a ∈ Subgroup.normalizer (gnPre T L : Set X))
    (hQ : S.ρ ⟨l, Subgroup.le_normalizer hl⟩ * S.ρ ⟨a, haN⟩ *
      (S.ρ ⟨l, Subgroup.le_normalizer hl⟩)⁻¹ ∈ S.Q) :
    l * a * l⁻¹ ∈ T ⊔ gnC T := by
  classical
  have hlN : l ∈ Subgroup.normalizer (gnPre T L : Set X) := Subgroup.le_normalizer hl
  have haQ : S.ρ ⟨a, haN⟩ ∈ S.Q := ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.2 ⟨haT, haN⟩, rfl⟩
  have hμQ : ⁅S.ρ ⟨l, hlN⟩, S.ρ ⟨a, haN⟩⁆ ∈ S.Q := by
    rw [commutatorElement_def]
    exact S.Q.mul_mem hQ (S.Q.inv_mem haQ)
  have hμA : ⁅S.ρ ⟨l, hlN⟩, S.ρ ⟨a, haN⟩⁆ ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  obtain ⟨k₀, hk₀T, hk₀L, hk₀⟩ := S.exists_mem_T_of_mem_Q_alt hX hL hμQ hμA
  have hcK : l * a * l⁻¹ * a⁻¹ ∈ gnPre T L := by
    have h1 : a * l⁻¹ * a⁻¹ ∈ gnPre T L :=
      (Subgroup.mem_normalizer_iff.1 haN l⁻¹).1 ((gnPre T L).inv_mem hl)
    have := (gnPre T L).mul_mem hl h1
    simpa [mul_assoc] using this
  have hcL : toStar T (l * a * l⁻¹ * a⁻¹) ∈ L := hcK
  have hρc : S.ρ ⟨l * a * l⁻¹ * a⁻¹, Subgroup.le_normalizer hcK⟩ =
      ⁅S.ρ ⟨l, hlN⟩, S.ρ ⟨a, haN⟩⁆ := by
    rw [commutatorElement_def]
    have : (⟨l * a * l⁻¹ * a⁻¹, Subgroup.le_normalizer hcK⟩ :
        ↥(Subgroup.normalizer (gnPre T L : Set X))) =
        ⟨l, hlN⟩ * ⟨a, haN⟩ * ⟨l, hlN⟩⁻¹ * ⟨a, haN⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hg1 := S.ρ_pre ⟨l * a * l⁻¹ * a⁻¹, hcK⟩ hcL
  have hgeq : (g ⟨toStar T (l * a * l⁻¹ * a⁻¹), hcL⟩ : Perm (Fin n)) =
      (g ⟨toStar T k₀, hk₀L⟩ : Perm (Fin n)) := by
    rw [hk₀, ← hρc]
    exact hg1.symm
  have hinj : (⟨toStar T (l * a * l⁻¹ * a⁻¹), hcL⟩ : ↥L) = ⟨toStar T k₀, hk₀L⟩ :=
    S.g_bij.1 (Subtype.ext hgeq)
  have hcq : toStar T (l * a * l⁻¹ * a⁻¹) = toStar T k₀ := congrArg Subtype.val hinj
  have hz : k₀⁻¹ * (l * a * l⁻¹ * a⁻¹) ∈ gnC T := by
    have h := (QuotientGroup.eq (s := gnC T)).1 hcq.symm
    exact h
  have hz' : a⁻¹ * (k₀⁻¹ * (l * a * l⁻¹ * a⁻¹)) * a ∈ gnC T := by
    have := (gnC_normal T).conj_mem _ hz a⁻¹
    simpa using this
  have hmain : l * a * l⁻¹ = (k₀ * a) * (a⁻¹ * (k₀⁻¹ * (l * a * l⁻¹ * a⁻¹)) * a) := by group
  rw [hmain]
  exact Subgroup.mul_mem_sup (T.mul_mem hk₀T haT) hz'

theorem map_conjSub_le_gnImg_thompsonJ (hX : GNSetting X T) (hL : IsComponentOf L ⊤)
    {l : X} (hl : toStar T l ∈ L)
    (hJQ : ∀ j ∈ S.J, S.ρ ⟨l, Subgroup.le_normalizer hl⟩ * j *
      (S.ρ ⟨l, Subgroup.le_normalizer hl⟩)⁻¹ ∈ S.Q)
    {A : Subgroup X} (hA : IsMaxElemAbelian T A) :
    (B6.conjSub l A).map (toStar T) ≤ gnImg T (thompsonJ T) := by
  classical
  have hlN : l ∈ Subgroup.normalizer (gnPre T L : Set X) := Subgroup.le_normalizer hl
  have hAJ : A ≤ thompsonJ T := B6.le_thompsonJ hA
  have hAN : A ≤ Subgroup.normalizer (gnPre T L : Set X) :=
    hAJ.trans ((B6.thompsonJ_le_baum T).trans S.baum_le)
  have hsub : B6.conjSub l A ≤ T ⊔ gnC T := by
    intro x hx
    rw [B6.mem_conjSub] at hx
    have hxa : x = l * (l⁻¹ * x * l) * l⁻¹ := by group
    rw [hxa]
    have haA : l⁻¹ * x * l ∈ A := hx
    have haN := hAN haA
    refine S.conj_mem_sup_gnC hX hL hl (hA.1 haA) haN ?_
    exact hJQ _ ⟨⟨l⁻¹ * x * l, haN⟩, Subgroup.mem_subgroupOf.2 (hAJ haA), rfl⟩
  have hTsyl : IsSylowTwoOf T (T ⊔ gnC T) := B6.isSylowTwoOf_mono hX.sylow le_sup_left le_top
  have h2grp : IsPGroup 2 (B6.conjSub l A) := by
    have hmap : B6.conjSub l A = A.map (MulAut.conj l).toMonoidHom := rfl
    rw [hmap]
    exact (hX.sylow.2.1.to_le hA.1).map _
  obtain ⟨S', hS', hle⟩ := B6.exists_isSylowTwoOf_ge h2grp hsub
  obtain ⟨g', hg'mem, hg'⟩ := B6.isSylowTwoOf_exists_conj hTsyl hS'
  have hBT : B6.conjSub (g'⁻¹ * l) A ≤ T := by
    intro y hy
    rw [B6.mem_conjSub] at hy
    have h1 : g' * y * g'⁻¹ ∈ B6.conjSub l A := by
      rw [B6.mem_conjSub]
      have : l⁻¹ * (g' * y * g'⁻¹) * l = (g'⁻¹ * l)⁻¹ * y * (g'⁻¹ * l) := by group
      rw [this]
      exact hy
    have h2 : g' * y * g'⁻¹ ∈ B6.conjSub g' T := hg' ▸ hle h1
    rw [B6.mem_conjSub] at h2
    have e : g'⁻¹ * (g' * y * g'⁻¹) * g' = y := by group
    rw [e] at h2
    exact h2
  have hBmax : IsMaxElemAbelian T (B6.conjSub (g'⁻¹ * l) A) :=
    isMaxElemAbelian_conjSub_of_conjSub_le hA hBT
  have hBJ : B6.conjSub (g'⁻¹ * l) A ≤ thompsonJ T := B6.le_thompsonJ hBmax
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ T : Set X) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  rintro _ ⟨x, hx, rfl⟩
  have hx' : l⁻¹ * x * l ∈ A := (B6.mem_conjSub).1 hx
  have hy : g'⁻¹ * x * g' ∈ B6.conjSub (g'⁻¹ * l) A := by
    rw [B6.mem_conjSub]
    have : (g'⁻¹ * l)⁻¹ * (g'⁻¹ * x * g') * (g'⁻¹ * l) = l⁻¹ * x * l := by group
    rw [this]
    exact hx'
  have hyJ : g'⁻¹ * x * g' ∈ thompsonJ T := hBJ hy
  have hg'T : toStar T g' ∈ gnImg T T := (mem_sup_gnC_iff T T g').1 hg'mem
  obtain ⟨t, ht, htq⟩ := hg'T
  refine ⟨t * (g'⁻¹ * x * g') * t⁻¹, ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.1 (hTJ ht) (g'⁻¹ * x * g')).1 hyJ
    exact this
  · have htq' : QuotientGroup.mk' (gnC T) t = toStar T g' := htq
    show toStar T (t * (g'⁻¹ * x * g') * t⁻¹) = toStar T x
    rw [map_mul, map_mul, map_inv, htq']
    simp only [map_mul, map_inv]
    group

theorem map_conjSub_thompsonJ_le (hX : GNSetting X T) (hL : IsComponentOf L ⊤)
    {l : X} (hl : toStar T l ∈ L)
    (hJQ : ∀ j ∈ S.J, S.ρ ⟨l, Subgroup.le_normalizer hl⟩ * j *
      (S.ρ ⟨l, Subgroup.le_normalizer hl⟩)⁻¹ ∈ S.Q) :
    (B6.conjSub l (thompsonJ T)).map (toStar T) ≤ gnImg T (thompsonJ T) := by
  have h : B6.conjSub l (thompsonJ T) =
      ⨆ A : Subgroup X, ⨆ _ : IsMaxElemAbelian T A, B6.conjSub l A := by
    unfold thompsonJ
    rw [OrderIso.map_iSup]
    congr 1
    ext A
    rw [OrderIso.map_iSup]
  rw [h, Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hA => S.map_conjSub_le_gnImg_thompsonJ hX hL hl hJQ hA

theorem conj_mem_J_of_conj_J_le_Q (hX : GNSetting X T) (hL : IsComponentOf L ⊤)
    {l : X} (hl : toStar T l ∈ L)
    (hJQ : ∀ j ∈ S.J, S.ρ ⟨l, Subgroup.le_normalizer hl⟩ * j *
      (S.ρ ⟨l, Subgroup.le_normalizer hl⟩)⁻¹ ∈ S.Q) :
    ∀ j ∈ S.J, S.ρ ⟨l, Subgroup.le_normalizer hl⟩ * j *
      (S.ρ ⟨l, Subgroup.le_normalizer hl⟩)⁻¹ ∈ S.J := by
  classical
  intro j hj
  obtain ⟨x, hx, rfl⟩ := hj
  have hxJ : (x : X) ∈ thompsonJ T := Subgroup.mem_subgroupOf.1 hx
  have hlN : l ∈ Subgroup.normalizer (gnPre T L : Set X) := Subgroup.le_normalizer hl
  have hmem : l * (x : X) * l⁻¹ ∈ B6.conjSub l (thompsonJ T) := by
    rw [B6.mem_conjSub]
    have : l⁻¹ * (l * (x : X) * l⁻¹) * l = x := by group
    rw [this]
    exact hxJ
  obtain ⟨y, hy, hyq⟩ := S.map_conjSub_thompsonJ_le hX hL hl hJQ ⟨_, hmem, rfl⟩
  have hyN : y ∈ Subgroup.normalizer (gnPre T L : Set X) :=
    S.baum_le ((B6.thompsonJ_le_baum T) hy)
  have hzN : l * (x : X) * l⁻¹ ∈ Subgroup.normalizer (gnPre T L : Set X) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN x.2) (Subgroup.inv_mem _ hlN)
  have hz : y⁻¹ * (l * (x : X) * l⁻¹) ∈ gnC T := (QuotientGroup.eq (s := gnC T)).1 hyq
  have hzN' : y⁻¹ * (l * (x : X) * l⁻¹) ∈ Subgroup.normalizer (gnPre T L : Set X) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) hzN
  have hρ := S.ρ_C ⟨_, hzN'⟩ hz
  refine ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.2 hy, ?_⟩
  have h3 : (⟨y⁻¹ * (l * (x : X) * l⁻¹), hzN'⟩ : ↥(Subgroup.normalizer (gnPre T L : Set X))) =
      ⟨y, hyN⟩⁻¹ * (⟨l, hlN⟩ * x * ⟨l, hlN⟩⁻¹) := rfl
  rw [h3, map_mul, map_inv, map_mul, map_mul, map_inv] at hρ
  exact inv_mul_eq_one.1 hρ

end GNAltModData

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15


module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiBender
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcInvolution
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevBenderTypes
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCore
import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools CFSG.Open Subgroup

private theorem normalizerMonoidHom_inclusion_eq_one_iff {G : Type} [Group G] {L I : Subgroup G}
    (hIL : I ≤ Subgroup.normalizer (L : Set G)) (x : ↥I) :
    (L.normalizerMonoidHom.comp (Subgroup.inclusion hIL)) x = 1 ↔
      (x : G) ∈ Subgroup.centralizer (L : Set G) := by
  have hφ : ∀ y : ↥L,
      (((L.normalizerMonoidHom.comp (Subgroup.inclusion hIL)) x y : ↥L) : G) =
        (x : G) * y * (x : G)⁻¹ :=
    fun y => Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hIL x) y
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun f : MulAut ↥L => ((f ⟨y, hy⟩ : ↥L) : G)) hx
    simp only [MulAut.one_apply] at h
    rw [hφ] at h
    calc y * x = ((x : G) * y * (x : G)⁻¹) * x := by rw [h]
      _ = x * y := by group
  · intro hx
    ext y
    simp only [MulAut.one_apply]
    rw [hφ]
    have hy := Subgroup.mem_centralizer_iff.mp hx y y.2
    rw [← hy, mul_assoc, mul_inv_cancel, mul_one]

private theorem map_mul_conj_inv_mul_inv_eq_one {I M : Type*} [Group I] [Group M]
    (φ : I →* M) {z i : I} (hcent : ∀ g ∈ φ.range, g * φ z = φ z * g) :
    φ (i * z * i⁻¹ * z⁻¹) = 1 := by
  have hc := hcent (φ i) (MonoidHom.mem_range.mpr ⟨i, rfl⟩)
  simp only [map_mul, map_inv]
  rw [hc]
  group

private theorem exists_range_central_involution {I M : Type*} [Group I] [Group M]
    (φ : I →* M) [Finite φ.range] (hP : IsPGroup 2 φ.range) (hnt : Nontrivial φ.range) :
    ∃ z : I, φ z ≠ 1 ∧ (φ z) ^ 2 = 1 ∧ ∀ g ∈ φ.range, g * φ z = φ z * g := by
  have hnt' : Nontrivial φ.range := hnt
  have hZnt : Nontrivial ↥(Subgroup.center φ.range) := hP.center_nontrivial
  have hZP : IsPGroup 2 (Subgroup.center φ.range) := hP.to_subgroup (Subgroup.center φ.range)
  have hdvd : 2 ∣ Nat.card (Subgroup.center φ.range) :=
    hZP.card_eq_or_dvd.resolve_left (ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr hZnt))
  obtain ⟨ζ, hζord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center φ.range)) 2 hdvd
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp
    (show ((ζ : φ.range) : M) ∈ φ.range from (ζ : φ.range).2)
  have h2 : orderOf (ζ : φ.range) = 2 := (Subgroup.orderOf_coe ζ).trans hζord
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [hz]
    intro h
    have hζeq : (ζ : φ.range) = 1 := Subtype.ext (by simpa using h)
    have h3 : orderOf (ζ : φ.range) = 1 := by rw [hζeq, orderOf_one]
    rw [h2] at h3
    exact absurd h3 (by norm_num)
  · have h2' : (ζ : φ.range) ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
    rw [hz]
    exact congrArg (fun w : φ.range => (w : M)) h2'
  · intro g hg
    rw [hz]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ζ.2 ⟨g, hg⟩)

private theorem conj_mul_conj_eq_of_commute {G : Type} [Group G] {z i c d : G}
    (hdz : i * z * i⁻¹ = d * z) (hcomm : (i * c * i⁻¹) * d = d * (i * c * i⁻¹)) :
    (i * c * i⁻¹) * z * (i * c * i⁻¹)⁻¹ = d⁻¹ * (i * (c * z * c⁻¹) * i⁻¹) := by
  have hz' : z = d⁻¹ * (i * z * i⁻¹) := by rw [hdz]; group
  have hcomm' : (i * c * i⁻¹) * d⁻¹ = d⁻¹ * (i * c * i⁻¹) := by
    rw [mul_inv_eq_iff_eq_mul]
    calc (i * c * i⁻¹) = d⁻¹ * (d * (i * c * i⁻¹)) := by group
      _ = d⁻¹ * ((i * c * i⁻¹) * d) := by rw [← hcomm]
      _ = (d⁻¹ * (i * c * i⁻¹)) * d := by group
  conv_lhs => rw [hz']
  rw [show (i * c * i⁻¹) * (d⁻¹ * (i * z * i⁻¹)) * (i * c * i⁻¹)⁻¹ =
      ((i * c * i⁻¹) * d⁻¹) * (i * z * i⁻¹) * (i * c * i⁻¹)⁻¹ from by group, hcomm']
  group

private theorem exists_central_involution {G : Type} [Group G] [Finite G] {L I : Subgroup G}
    (hI : IsPGroup 2 I) (hIL : I ≤ Subgroup.normalizer (L : Set G))
    (hnot : ¬ I ≤ Subgroup.centralizer (L : Set G)) :
    ∃ z ∈ I, z ∉ Subgroup.centralizer (L : Set G) ∧
      z ^ 2 ∈ Subgroup.centralizer (L : Set G) ∧
      ∀ i ∈ I, i * z * i⁻¹ * z⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  let φ : ↥I →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hIL)
  have hker : ∀ x : ↥I, φ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (L : Set G) :=
    fun x => normalizerMonoidHom_inclusion_eq_one_iff hIL x
  have hnot' : ∃ x : ↥I, φ x ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hnot fun x hx => (hker ⟨x, hx⟩).mp (h ⟨x, hx⟩)
  have hnt : Nontrivial φ.range := by
    obtain ⟨x0, hx0⟩ := hnot'
    exact ⟨⟨φ x0, ⟨x0, rfl⟩⟩, 1, fun h => hx0 (Subtype.ext_iff.mp h)⟩
  have hP : IsPGroup 2 φ.range := hI.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hfin : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨z, hz1, hzsq1, hzcent⟩ := exists_range_central_involution φ hP hnt
  have hzC : (z : G) ∉ Subgroup.centralizer (L : Set G) := fun h => hz1 ((hker z).mpr h)
  have hz2 : (z : G) ^ 2 ∈ Subgroup.centralizer (L : Set G) := by
    have h := (hker (z ^ 2)).mp (by rw [map_pow]; exact hzsq1)
    simpa using h
  have hzcomm : ∀ i ∈ I, i * (z : G) * i⁻¹ * (z : G)⁻¹ ∈
      Subgroup.centralizer (L : Set G) := by
    intro i hi
    refine (hker ((⟨i, hi⟩ : ↥I) * z * (⟨i, hi⟩ : ↥I)⁻¹ * z⁻¹)).mp ?_
    exact map_mul_conj_inv_mul_inv_eq_one φ hzcent
  exact ⟨(z : G), z.2, hzC, hz2, hzcomm⟩

private theorem conj_mem_centralizer_singleton_iff {G : Type} [Group G] {L : Subgroup G}
    {z i c : G} (hicL : i * c * i⁻¹ ∈ L)
    (hd : i * z * i⁻¹ * z⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    i * c * i⁻¹ ∈ Subgroup.centralizer ({z} : Set G) ↔
      c ∈ Subgroup.centralizer ({z} : Set G) := by
  have hdz : i * z * i⁻¹ = (i * z * i⁻¹ * z⁻¹) * z := by group
  have hcomm : (i * c * i⁻¹) * (i * z * i⁻¹ * z⁻¹) =
      (i * z * i⁻¹ * z⁻¹) * (i * c * i⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hd (i * c * i⁻¹) hicL
  have key := conj_mul_conj_eq_of_commute hdz hcomm
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : (i * c * i⁻¹) * z * (i * c * i⁻¹)⁻¹ = z := by rw [h]; group
    have h2 : i * (c * z * c⁻¹) * i⁻¹ = i * z * i⁻¹ := by
      have h3 : (i * z * i⁻¹ * z⁻¹)⁻¹ * (i * (c * z * c⁻¹) * i⁻¹) =
          (i * z * i⁻¹ * z⁻¹)⁻¹ * (i * z * i⁻¹) := by
        rw [← key, h1, hdz]
        group
      exact mul_left_cancel h3
    have h4 : c * z * c⁻¹ = z := by
      simpa using congrArg (fun w => i⁻¹ * w * i) h2
    calc c * z = (c * z * c⁻¹) * c := by group
      _ = z * c := by rw [h4]
  · intro h
    have h1 : c * z * c⁻¹ = z := by rw [h]; group
    have h2 : (i * c * i⁻¹) * z * (i * c * i⁻¹)⁻¹ = z := by
      rw [key, h1, hdz]
      group
    calc (i * c * i⁻¹) * z = ((i * c * i⁻¹) * z * (i * c * i⁻¹)⁻¹) * (i * c * i⁻¹) := by
          group
      _ = z * (i * c * i⁻¹) := by rw [h2]

private theorem le_normalizer_inf_centralizer_singleton {G : Type} [Group G] {L I : Subgroup G}
    {z : G} (hIL : I ≤ Subgroup.normalizer (L : Set G))
    (hzcomm : ∀ i ∈ I, i * z * i⁻¹ * z⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    I ≤ Subgroup.normalizer (L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) := by
  rw [Subgroup.le_set_normalizer_iff]
  intro i hi c hc
  have hicL : i * c * i⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hIL hi) c).mp hc.1
  exact ⟨hicL, (conj_mem_centralizer_singleton_iff hicL (hzcomm i hi)).mpr hc.2⟩

private theorem sup_conj_ne_of_iSup_ne {G : Type} [Group G] {L U I : Subgroup G} {z : G}
    (hIL : I ≤ Subgroup.normalizer (L : Set G)) (hzI : z ∈ I)
    (horb : ∀ A : Subgroup G, IsGomiAtom L U A →
      (⨆ i ∈ I, A.map (MulAut.conj i).toMonoidHom) ≠ L) :
    ∀ A : Subgroup G, IsGomiAtom L U A →
      A ⊔ A.map (MulAut.conj z).toMonoidHom ≠ L := by
  intro A hA heq
  have hsup_le : (⨆ i ∈ I, A.map (MulAut.conj i).toMonoidHom) ≤ L := by
    refine iSup₂_le fun i hi => ?_
    exact (Subgroup.map_mono hA.2.1).trans
      (le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hIL hi)))
  refine horb A hA (le_antisymm hsup_le ?_)
  rw [← heq]
  exact sup_le
    (le_iSup₂_of_le 1 (one_mem I) (by rw [map_one]; exact le_of_eq (Subgroup.map_id (K := A)).symm))
    (le_iSup₂_of_le z hzI le_rfl)

private theorem not_isolated_of_pCoreOf_inf_centralizer_singleton_ne_bot {G : Type}
    [Group G] [Finite G] {L I : Subgroup G} {z : G} (hzI : z ∈ I)
    (hiso : IsPIsolatedOver 2 (L ⊓ Subgroup.centralizer (I : Set G)) ⊥)
    (hI : IsPGroup 2 I)
    (hIC : I ≤ Subgroup.normalizer (L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G))
    (hYne : pCoreOf 2 (L ⊓ Subgroup.centralizer ({z} : Set G)) ≠ ⊥) : False := by
  let C : Subgroup G := L ⊓ Subgroup.centralizer ({z} : Set G)
  have hIY : I ≤ Subgroup.normalizer (pCoreOf 2 C : Set G) :=
    hIC.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 C)
  have hYp : IsPGroup 2 (pCoreOf 2 C) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  set X : Subgroup G := pCoreOf 2 C ⊓ Subgroup.centralizer (I : Set G) with hXdef
  have hXne : X ≠ ⊥ :=
    CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot
      Nat.prime_two hI hYp hYne hIY
  have hXK : X ≤ L ⊓ Subgroup.centralizer (I : Set G) :=
    inf_le_inf_right _ ((CFSG.LieType.BorelTits.pCoreOf_le 2 C).trans inf_le_left)
  have hXp : IsPGroup 2 X := hYp.to_le inf_le_left
  have hCIz : Subgroup.centralizer (I : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hzI)
  have hKC : L ⊓ Subgroup.centralizer (I : Set G) ≤ C :=
    le_inf inf_le_left (inf_le_right.trans hCIz)
  have hKY : L ⊓ Subgroup.centralizer (I : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 C : Set G) :=
    hKC.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C)
  have hKCI : L ⊓ Subgroup.centralizer (I : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (I : Set G) : Set G) :=
    inf_le_right.trans Subgroup.le_normalizer
  have hKX : L ⊓ Subgroup.centralizer (I : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    (le_inf hKY hKCI).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hKbot : L ⊓ Subgroup.centralizer (I : Set G) ≤
      Subgroup.normalizer (⊥ : Subgroup G) := by
    rw [Subgroup.normalizer_eq_top (H := ⊥)]
    exact le_top
  exact hXne (le_bot_iff.mp (hiso.le_of_normal IsPGroup.of_bot bot_le hKbot hXK hXp hKX))

theorem not_isPIsolatedOver_of_gomiChevExcInvolution (hB : GomiBender)
    (hExc : GomiChevExcInvolution) {G : Type} [Group G] [Finite G] {L I U : Subgroup G}
    (hL : IsGomiChevTwo ↥L) (hE : IsGomiChevExceptional (↥L ⧸ center ↥L))
    (h1 : ¬ (IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨
      IsGomiSz (↥L ⧸ center ↥L)))
    (hI : IsPGroup 2 I) (hIL : I ≤ normalizer (L : Set G)) (hU : IsSylowOf 2 U L)
    (hIU : I ≤ normalizer (U : Set G))
    (horb : ∀ A : Subgroup G, IsGomiAtom L U A →
      (⨆ i ∈ I, A.map (MulAut.conj i).toMonoidHom) ≠ L) :
    ¬ IsPIsolatedOver 2 (L ⊓ centralizer (I : Set G)) ⊥ := by
  intro hiso
  by_cases hcase : I ≤ Subgroup.centralizer (L : Set G)
  · have hLle : L ≤ Subgroup.centralizer (I : Set G) := Subgroup.le_centralizer_iff.mp hcase
    rw [inf_eq_left.mpr hLle] at hiso
    exact h1 (isGomiL2_or_isGomiU3_or_isGomiSz_of_isPIsolatedOver hB hL hiso)
  · obtain ⟨z, hzI, hzL, hz2, hzcomm⟩ := exists_central_involution hI hIL hcase
    have hIC : I ≤ Subgroup.normalizer
        (L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) :=
      le_normalizer_inf_centralizer_singleton hIL hzcomm
    have hYne : pCoreOf 2 (L ⊓ Subgroup.centralizer ({z} : Set G)) ≠ ⊥ :=
      hExc G L U z hL hE hU (hIL hzI) (hIU hzI) hzL hz2
        (sup_conj_ne_of_iSup_ne hIL hzI horb)
    exact not_isolated_of_pCoreOf_inf_centralizer_singleton_ne_bot hzI hiso hI hIC hYne

end CFSG.GroupTheory

module

public import CFSG.LargeExtraspecial.S12InspFamDFi
public import CFSG.LargeExtraspecial.S12TriH2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

namespace S12InspP5

theorem map_subtype_commutator_inf_centralizer {Y : Type*} [Group Y] (H : Subgroup Y) (t : H) :
    (commutator H ⊓ centralizer {t}).map H.subtype = ⁅H, H⁆ ⊓ centralizer {(t : Y)} := by
  rw [← map_subtype_commutator H]
  ext y
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, coe_subtype]
  constructor
  · rintro ⟨x, ⟨hxQ, hxt⟩, rfl⟩
    exact ⟨⟨x, hxQ, rfl⟩, congrArg Subtype.val hxt⟩
  · rintro ⟨⟨x, hxQ, rfl⟩, hxt⟩
    exact ⟨x, ⟨hxQ, Subtype.ext hxt⟩, rfl⟩

theorem nonabelian_commutator_of_pair {X : Type} [Group X] {E : Set X}
    (hP : CFSG.Blueprint.Fischer.Pair X E) (hZ : center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) :
    ∃ a b : commutator X, a * b ≠ b * a := by
  by_contra! hc
  have hsol : Group.IsSolvable (commutator X) := Group.isSolvable_of_comm hc
  have hle := fischerQ_le_commutator hP hZ h2 h3
  exact not_isSolvable_fischerQ hP hZ h2 h3
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))

theorem commutatorElement_mul_comm {Y : Type*} [Group Y] {N : Subgroup Y} {y x : Y}
    (hx : ∀ n ∈ N, x⁻¹ * n * x ∈ N) (hy : ∀ n ∈ N, y * n = n * y) :
    ∀ n ∈ N, ⁅y, x⁆ * n = n * ⁅y, x⁆ := by
  intro n hn
  have h1 : y * n * y⁻¹ = n := by rw [hy n hn]; group
  have h2 : y⁻¹ * (x⁻¹ * n * x) * y = x⁻¹ * n * x := by
    rw [mul_assoc, ← hy _ (hx n hn)]; group
  have h3 : ⁅y, x⁆ * n * ⁅y, x⁆⁻¹ = n := by
    rw [commutatorElement_def]
    calc y * x * y⁻¹ * x⁻¹ * n * (y * x * y⁻¹ * x⁻¹)⁻¹
        = y * x * (y⁻¹ * (x⁻¹ * n * x) * y) * x⁻¹ * y⁻¹ := by group
      _ = y * n * y⁻¹ := by rw [h2]; group
      _ = n := h1
  exact mul_inv_eq_iff_eq_mul.mp h3

theorem eq_one_of_commute_commutator {X : Type*} [Group X] (hZ : center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a) {c : X}
    (hc : ∀ n ∈ commutator X, c * n = n * c) : c = 1 := by
  have hZ' : center (commutator X) = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal (center (commutator X)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (mem_center_iff.mp (h ▸ mem_top b) a)
  rw [← mem_bot, ← hZ, mem_center_iff]
  intro x
  have hk : ⁅c, x⁆ ∈ commutator X := by
    rw [_root_.commutator_def]
    exact commutator_mem_commutator (mem_top c) (mem_top x)
  have hkc := commutatorElement_mul_comm (N := commutator X) (x := x) (fun n hn => by
    have h := (inferInstance : (commutator X).Normal).conj_mem n hn x⁻¹
    rwa [inv_inv] at h) hc
  have hk1 : (⟨⁅c, x⁆, hk⟩ : commutator X) = 1 := by
    rw [← mem_bot, ← hZ', mem_center_iff]
    intro n
    exact Subtype.ext (hkc n n.2).symm
  have hk1' : ⁅c, x⁆ = 1 := congrArg Subtype.val hk1
  rw [commutatorElement_eq_one_iff_mul_comm] at hk1'
  exact hk1'.symm

end S12InspP5

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem hyp_Xbar12 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hS : S.S12Standing g t)
    (hdeg : ¬ S.IsNondeg12 g) :
    CFSG.Fischer.Classification.Hyp (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g) ∧
      ∃ a b : commutator (S.Xbar12 g), a * b ≠ b * a := by
  obtain ⟨hclass, hinv, hprod, hgen, hcenter, hsimple⟩ :=
    fischer_data_Xbar12 S12Tri.fischerTrialityInput haQ hne hn ht htA hS hdeg
  have hP : CFSG.Blueprint.Fischer.Pair (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g) :=
    ⟨inferInstance, hclass, hinv, hprod, hgen⟩
  have h2 : ∀ N : Subgroup (S.Xbar12 g), N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hp =>
    s12_normal_pGroup_eq_bot (fun P h1 h2 h3 => noNormalTwo_Xbar12 P h1 h2 h3) N hN hp
  have h3 : ∀ N : Subgroup (S.Xbar12 g), N.Normal → IsPGroup 3 N → N = ⊥ := fun N hN hp =>
    s12_normal_pGroup_eq_bot hS.core3_trivial N hN hp
  exact ⟨⟨hP, hcenter, hsimple⟩, S12InspP5.nonabelian_commutator_of_pair hP hcenter h2 h3⟩

theorem conj_mem_commutator_Xbar12 {g : G} {x : S.O} (hx : x ∈ S.Mbar) {n : S.O}
    (hn : n ∈ ⁅S.Xbar12 g, S.Xbar12 g⁆) : x * n * x⁻¹ ∈ ⁅S.Xbar12 g, S.Xbar12 g⁆ := by
  have h1 : (S.Xbar12 g).map (MulAut.conj x).toMonoidHom = S.Xbar12 g :=
    mem_normalizer_iff_map_conj_eq.mp (Mbar_le_normalizer_Xbar12 hx)
  have h2 : (⁅S.Xbar12 g, S.Xbar12 g⁆ : Subgroup S.O).map (MulAut.conj x).toMonoidHom =
      ⁅S.Xbar12 g, S.Xbar12 g⁆ := by
    rw [map_commutator, h1]
  rw [← h2]
  exact ⟨n, hn, rfl⟩

theorem false_of_triGood_Xbar12 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (htX : t ∈ S.Xbar12 g)
    (h : S12Tri.TriGood (S.Xbar12 g) ⟨t, htX⟩) : False := by
  set C : Subgroup S.O := ⁅S.Xbar12 g, S.Xbar12 g⁆ ⊓ centralizer {t} with hCdef
  have hmap : (commutator (S.Xbar12 g) ⊓ centralizer {(⟨t, htX⟩ : S.Xbar12 g)}).map
      (S.Xbar12 g).subtype = C :=
    S12InspP5.map_subtype_commutator_inf_centralizer _ _
  have hCM : C ≤ S.Mbar := inf_le_left.trans ((commutator_le_self _).trans Xbar12_le_Mbar)
  have hCt : ∀ c ∈ C, c * t = t * c := fun c hc => mem_centralizer_singleton_iff.mp hc.2
  have hcomm : ∀ {x : S.O}, x ∈ S.Lbar g → x * t = t * x := fun {x} hx =>
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨x, hx⟩ ⟨t, ht⟩)
  have hconj : ∀ {ℓ : S.O}, ℓ ∈ S.Lbar g → ∀ c ∈ C, ℓ * c * ℓ⁻¹ ∈ C := by
    intro ℓ hℓ c hc
    refine mem_inf.mpr ⟨conj_mem_commutator_Xbar12 (S.Lbar_le_Mbar g hℓ) (mem_inf.mp hc).1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hct := hCt c hc
    have hℓt := hcomm hℓ
    have hℓt' : ℓ⁻¹ * t = t * ℓ⁻¹ := by
      calc ℓ⁻¹ * t = ℓ⁻¹ * (t * ℓ) * ℓ⁻¹ := by group
        _ = ℓ⁻¹ * (ℓ * t) * ℓ⁻¹ := by rw [hℓt]
        _ = t * ℓ⁻¹ := by group
    calc ℓ * c * ℓ⁻¹ * t = ℓ * c * (ℓ⁻¹ * t) := by group
      _ = ℓ * (c * t) * ℓ⁻¹ := by rw [hℓt']; group
      _ = ℓ * (t * c) * ℓ⁻¹ := by rw [hct]
      _ = (ℓ * t) * c * ℓ⁻¹ := by group
      _ = t * (ℓ * c * ℓ⁻¹) := by rw [hℓt]; group
  have hLC : S.Lbar g ≤ normalizer (C : Set S.O) := fun ℓ hℓ =>
    mem_normalizer_of_conj_le (hconj hℓ) (hconj ((S.Lbar g).inv_mem hℓ))
  have hC2 : S12NoNormalTwo C := hmap ▸ h.2.map_subtype
  have hsol := isSolvable_of_commute_of_le_normalizer haQ hne hn ht htA hCM hCt hLC hC2
  rw [← hmap] at hsol
  exact h.1 (Group.isSolvable_of_isSolvable_injective
    (f := ((commutator (S.Xbar12 g) ⊓ centralizer {(⟨t, htX⟩ : S.Xbar12 g)}).equivMapOfInjective
      (S.Xbar12 g).subtype (S.Xbar12 g).subtype_injective).toMonoidHom) (MulEquiv.injective _))

theorem eq_one_of_commute_commutator_Xbar12 {g : G} {t : S.O} (hS : S.S12Standing g t)
    (hZ : center (S.Xbar12 g) = ⊥) (hsimp : IsSimpleGroup (commutator (S.Xbar12 g)))
    (hna : ∃ a b : commutator (S.Xbar12 g), a * b ≠ b * a) {y : S.O} (hy : y ∈ S.Mbar)
    (hyN : ∀ n ∈ ⁅S.Xbar12 g, S.Xbar12 g⁆, y * n = n * y) : y = 1 := by
  have hmem : y ∈ S.CXbar12 g := by
    refine ⟨hy, mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hxM := Xbar12_le_Mbar hx
    have hc := S12InspP5.commutatorElement_mul_comm (N := ⁅S.Xbar12 g, S.Xbar12 g⁆) (x := x)
      (fun n hn => by
        have h := conj_mem_commutator_Xbar12 (S.Mbar.inv_mem hxM) hn
        rwa [inv_inv] at h) hyN
    have hcX : ⁅y, x⁆ ∈ S.Xbar12 g := by
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp (Mbar_le_normalizer_Xbar12 hy) x).mp hx) (inv_mem hx)
    have h1 : (⟨⁅y, x⁆, hcX⟩ : S.Xbar12 g) = 1 := by
      refine S12InspP5.eq_one_of_commute_commutator hZ hsimp hna fun n hn => Subtype.ext ?_
      have hn' : (n : S.O) ∈ ⁅S.Xbar12 g, S.Xbar12 g⁆ := by
        rw [← map_subtype_commutator]
        exact ⟨n, hn, rfl⟩
      exact hc n hn'
    have h2 : ⁅y, x⁆ = 1 := congrArg Subtype.val h1
    rw [commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  rw [hS.cent, mem_bot] at hmem
  exact hmem

end Setting

end CFSG.LargeExtraspecial

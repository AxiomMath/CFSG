module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.CGT.T75I.CenFacts

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.SectionRank.Ccomm
open scoped Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem exists_coords (hc : Sec6Ctx T T₁ 2 2) :
    Nonempty (↥T ≃* Multiplicative (Fin 4 → ZMod 2)) := by
  have : Finite G := hc.finite
  have hTab := hc.hy.pair.wc.1
  exact nonempty_mulEquiv_of_elementary (p := 2) (n := 4)
    (fun a b => Subtype.ext (elemAbelian_mul_comm hTab a.2 b.2))
    (fun a => Subtype.ext (by simpa [pow_two] using elemAbelian_mul_self hTab a.2))
    (by rw [ctx_card_T hc]; norm_num)

@[expose] noncomputable def actGL (e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2)) :
    ↥(Subgroup.normalizer (T : Set G)) →* GL (Fin 4) (ZMod 2) :=
  (elemAutEquivGL e).toMonoidHom.comp T.normalizerMonoidHom

theorem actGL_mulVec (e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2))
    (n : ↥(Subgroup.normalizer (T : Set G))) (t : ↥T) :
    (actGL e n : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd (e t) =
      Multiplicative.toAdd (e ⟨(n : G) * t * (n : G)⁻¹,
        conj_mem_of_mem_normalizer n.2 t.2⟩) := by
  have := elemAutEquivGL_mulVec e (T.normalizerMonoidHom n) t
  exact this

theorem actGL_eq_one_iff (hC : Subgroup.centralizer (T : Set G) = T)
    (e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2)) (n : ↥(Subgroup.normalizer (T : Set G))) :
    actGL e n = 1 ↔ (n : G) ∈ T := by
  have h1 : actGL e n = 1 ↔ T.normalizerMonoidHom n = 1 := by
    constructor
    · intro h
      exact (elemAutEquivGL e).injective (by rw [map_one]; exact h)
    · intro h
      show (elemAutEquivGL e) (T.normalizerMonoidHom n) = 1
      rw [h, map_one]
  rw [h1, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, hC]

theorem card_fix_eq_card_centralizer (e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2))
    (n : ↥(Subgroup.normalizer (T : Set G))) :
    Nat.card {v : Fin 4 → ZMod 2 //
      (actGL e n : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v} =
      Nat.card ↥(T ⊓ Subgroup.centralizer ({(n : G)} : Set G)) := by
  let Φ : ↥T ≃ (Fin 4 → ZMod 2) := e.toEquiv.trans Multiplicative.toAdd
  have hΦ : ∀ t : ↥T, Φ t = Multiplicative.toAdd (e t) := fun t => rfl
  have h1 : {t : ↥T // (n : G) * t * (n : G)⁻¹ = t} ≃
      {v : Fin 4 → ZMod 2 // (actGL e n : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v} :=
    Equiv.subtypeEquiv Φ (fun t => by
      rw [hΦ, actGL_mulVec, ← hΦ, ← hΦ]
      constructor
      · intro h
        exact congrArg Φ (Subtype.ext h)
      · intro h
        exact congrArg Subtype.val (Φ.injective h))
  have h2 : {t : ↥T // (n : G) * t * (n : G)⁻¹ = t} ≃
      ↥(T ⊓ Subgroup.centralizer ({(n : G)} : Set G)) :=
    { toFun := fun t => ⟨t.1.1, t.1.2, Subgroup.mem_centralizer_singleton_iff.2 (by
        have h := t.2
        calc (t.1 : G) * n = ((n : G) * t.1 * (n : G)⁻¹) * n := by rw [h]
          _ = n * t.1 := by group)⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
        have h := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
        show (n : G) * x.1 * (n : G)⁻¹ = x.1
        calc (n : G) * x.1 * (n : G)⁻¹ = (x.1 * n) * (n : G)⁻¹ := by rw [h]
          _ = x.1 := by group⟩
      left_inv := fun t => rfl
      right_inv := fun x => rfl }
  exact Nat.card_congr (h1.symm.trans h2)

theorem exists_conj_mul_eq_of_card_four [Finite G] (hTab : IsElemAbelian 2 T)
    (hT16 : Nat.card T = 16) {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) (hn2 : n * n ∈ T)
    (hc4 : Nat.card ↥(T ⊓ Subgroup.centralizer ({n} : Set G)) = 4) :
    ∀ c ∈ T, c * n = n * c → ∃ t ∈ T, (n⁻¹ * t * n) * t = c := by
  classical
  have hn' : n⁻¹ ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer (T : Set G)).inv_mem hn
  have hconj : ∀ t : ↥T, n⁻¹ * (t : G) * n ∈ T := fun t => by
    have := conj_mem_of_mem_normalizer hn' t.2
    simpa using this
  let β : ↥T →* ↥T :=
    { toFun := fun t => ⟨(n⁻¹ * (t : G) * n) * t, T.mul_mem (hconj t) t.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hc : (n⁻¹ * (b : G) * n) * (a : G) = (a : G) * (n⁻¹ * (b : G) * n) :=
          elemAbelian_mul_comm hTab (hconj b) a.2
        calc (n⁻¹ * ((a * b : ↥T) : G) * n) * ((a * b : ↥T) : G)
            = ((n⁻¹ * (a : G) * n) * (n⁻¹ * (b : G) * n)) * ((a : G) * b) := by
              simp only [Subgroup.coe_mul]; group
          _ = (n⁻¹ * (a : G) * n) * ((n⁻¹ * (b : G) * n) * (a : G)) * b := by group
          _ = (n⁻¹ * (a : G) * n) * ((a : G) * (n⁻¹ * (b : G) * n)) * b := by rw [hc]
          _ = ((n⁻¹ * (a : G) * n) * (a : G)) * ((n⁻¹ * (b : G) * n) * (b : G)) := by group }
  have hβ : ∀ t : ↥T, ((β t : ↥T) : G) = (n⁻¹ * (t : G) * n) * t := fun t => rfl
  have hker : β.ker = (T ⊓ Subgroup.centralizer ({n} : Set G)).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : (n⁻¹ * (t : G) * n) * t = 1 := by rw [← hβ, h]; rfl
      have ht2 : (t : G) * t = 1 := elemAbelian_mul_self hTab t.2
      refine ⟨t.2, ?_⟩
      have h2 : n⁻¹ * (t : G) * n = (t : G) := by
        have : n⁻¹ * (t : G) * n = (t : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this, elemAbelian_inv hTab t.2]
      calc (t : G) * n = n * (n⁻¹ * (t : G) * n) := by group
        _ = n * t := by rw [h2]
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [hβ]
      have h2 : n⁻¹ * (t : G) * n = (t : G) := by
        calc n⁻¹ * (t : G) * n = n⁻¹ * ((n : G) * t) := by rw [← h]; group
          _ = t := by group
      rw [h2, elemAbelian_mul_self hTab t.2]
      rfl
  have hkcard : Nat.card β.ker = 4 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hc4]
  have hrcard : Nat.card β.range = 4 := by
    have h := Subgroup.card_ker_mul_card_range β
    rw [hkcard, hT16] at h
    omega
  have hrle : β.range ≤ β.ker := by
    rw [hker]
    rintro _ ⟨t, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨(β t).2, ?_⟩
    rw [hβ]
    have hs : ∀ u : ↥T, (n * n) * (u : G) = (u : G) * (n * n) := fun u =>
      elemAbelian_mul_comm hTab hn2 u.2
    have hsw : n * (t : G) * n⁻¹ = n⁻¹ * (t : G) * n := by
      calc n * (t : G) * n⁻¹ = n⁻¹ * ((n * n) * (t : G)) * n⁻¹ := by group
        _ = n⁻¹ * ((t : G) * (n * n)) * n⁻¹ := by rw [hs t]
        _ = n⁻¹ * (t : G) * n := by group
    have hcomm : (t : G) * (n⁻¹ * (t : G) * n) = (n⁻¹ * (t : G) * n) * t :=
      elemAbelian_mul_comm hTab t.2 (hconj t)
    have hu : n * ((n⁻¹ * (t : G) * n) * t) * n⁻¹ = (n⁻¹ * (t : G) * n) * t := by
      calc n * ((n⁻¹ * (t : G) * n) * t) * n⁻¹ = (t : G) * (n * t * n⁻¹) := by group
        _ = (t : G) * (n⁻¹ * (t : G) * n) := by rw [hsw]
        _ = (n⁻¹ * (t : G) * n) * t := hcomm
    calc ((n⁻¹ * (t : G) * n) * t) * n = (n * ((n⁻¹ * (t : G) * n) * t) * n⁻¹) * n := by rw [hu]
      _ = n * ((n⁻¹ * (t : G) * n) * t) := by group
  have hrk : β.range = β.ker := Subgroup.eq_of_le_of_card_ge hrle (by rw [hkcard, hrcard])
  intro c hcT hcn
  have hcker : (⟨c, hcT⟩ : ↥T) ∈ β.range := by
    rw [hrk, hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨hcT, hcn⟩
  obtain ⟨t, ht⟩ := hcker
  have ht' : (n⁻¹ * (t : G) * n) * t = c := by
    have := congrArg Subtype.val ht
    rw [hβ] at this
    exact this
  exact ⟨t, t.2, ht'⟩

theorem exists_involution_of_card_four [Finite G] (hTab : IsElemAbelian 2 T)
    (hT16 : Nat.card T = 16) {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) (hn2 : n * n ∈ T)
    (hc4 : Nat.card ↥(T ⊓ Subgroup.centralizer ({n} : Set G)) = 4) :
    ∃ t ∈ T, (n * t) * (n * t) = 1 := by
  obtain ⟨t, htT, ht⟩ := exists_conj_mul_eq_of_card_four hTab hT16 hn hn2 hc4 (n * n) hn2 (by
    group)
  refine ⟨t, htT, ?_⟩
  calc (n * t) * (n * t) = (n * n) * ((n⁻¹ * t * n) * t) := by group
    _ = (n * n) * (n * n) := by rw [ht]
    _ = 1 := elemAbelian_mul_self hTab hn2

end CFSG.CGT.T75I

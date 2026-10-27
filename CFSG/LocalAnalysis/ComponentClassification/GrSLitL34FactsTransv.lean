module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransvModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelGenBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelModelBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem eightTransvection :
    ∀ (G : Type) [Group G] [Finite G] (J P E : Subgroup G) (a : G), ⁅J, J⁆ = J →
      IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
      IsCyclic ↥(P ⊓ zStarIn J) → Nat.card ↥(P ⊓ zStarIn J) = 4 →
      E ≤ P → IsEightGroup E → E ⊓ zStarIn J = zpowers a →
      ∀ τ : ↥E ≃* ↥E, (∀ y : ↥E, (y : G)⁻¹ * (τ y : G) ∈ zpowers a) →
        ∃ p ∈ P ⊓ normalizer (E : Set G), ∀ y : ↥E, p⁻¹ * (y : G) * p = (τ y : G) := by
  intro G _ _ J P E a hJ hL hP hcyc h4 hEP hE hEa τ hτ
  classical
  have haEZ : a ∈ E ⊓ zStarIn J := hEa ▸ mem_zpowers a
  obtain ⟨haE, haZ⟩ := mem_inf.mp haEZ
  have ha2 : a * a = 1 := hE.1.2 a haE
  by_cases ha1 : a = 1
  · refine ⟨1, mem_inf.mpr ⟨one_mem _, one_mem _⟩, fun y => ?_⟩
    have h1 := hτ y
    rw [ha1, zpowers_one_eq_bot, mem_bot, inv_mul_eq_one] at h1
    rw [inv_one, one_mul, mul_one]
    exact h1
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hJ hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨ζe, -⟩ := exists_zeta hP hqker
  have hkcyc : IsCyclic q.ker := isCyclic_of_surjective ζe.toMonoidHom ζe.surjective
  have hk4 : Nat.card q.ker = 4 := by rw [← Nat.card_congr ζe.toEquiv, h4]
  have haP : a ∈ P := hEP haE
  have hmulP : ∀ {u v : G} (hu : u ∈ P) (hv : v ∈ P),
      jq J ⟨u * v, hP.1 (P.mul_mem hu hv)⟩ = jq J ⟨u, hP.1 hu⟩ * jq J ⟨v, hP.1 hv⟩ :=
    fun hu hv => by rw [← map_mul]; rfl
  have hzZ : ∀ {z : G} (hzP : z ∈ P), z ∈ zStarIn J ↔ jq J ⟨z, hP.1 hzP⟩ ∈ q.ker := by
    intro z hzP
    rw [mem_zStarIn_iff, hqker]
  have hâk : jq J ⟨a, hP.1 haP⟩ ∈ q.ker := (hzZ haP).1 haZ
  have hâ2 : jq J ⟨a, hP.1 haP⟩ * jq J ⟨a, hP.1 haP⟩ = 1 := by
    rw [← hmulP haP haP]
    have : (⟨a * a, hP.1 (P.mul_mem haP haP)⟩ : J) = 1 := Subtype.ext ha2
    rw [this, map_one]
  have hâ1 : jq J ⟨a, hP.1 haP⟩ ≠ 1 := fun h => ha1 (eq_one_of_jq_eq_one hP.1 hP2 haP h)
  have h2E : ∀ {y : G} (hy : y ∈ E),
      q (jq J ⟨y, hP.1 (hEP hy)⟩) * q (jq J ⟨y, hP.1 (hEP hy)⟩) = 1 := by
    intro y hy
    rw [← map_mul, ← hmulP (hEP hy) (hEP hy)]
    have : (⟨y * y, hP.1 (P.mul_mem (hEP hy) (hEP hy))⟩ : J) = 1 := Subtype.ext (hE.1.2 y hy)
    rw [this, map_one, map_one]
  obtain ⟨U, hU, hEU⟩ := exists_U hP.1 hT hEP h2E
  obtain ⟨I, hI, hIU, hIk⟩ := exists_uIdx hU
  have hUc : ∀ {s t : Equiv.Perm (Fin 42)}, s ∈ U → t ∈ U → s * t = t * s := by
    intro s t hs ht
    rcases hU with rfl | rfl
    · exact comm_of_mul_self (U1_mul_self hs) (U1_mul_self ht) (U1_mul_self (U1.mul_mem hs ht))
    · exact comm_of_mul_self (U2_mul_self hs) (U2_mul_self ht) (U2_mul_self (U2.mul_mem hs ht))
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := hE.1.1
  have hza : Nat.card (zpowers a) = 2 := card_zpowers_of_involution ha2 ha1
  obtain ⟨y₁, hy₁E, hy₁a⟩ := Set.not_subset.mp (show ¬ E ≤ zpowers a from fun h => by
    have := Subgroup.card_le_of_le h
    rw [hE.2, hza] at this
    omega)
  have hy₁2 := hE.1.2 y₁ hy₁E
  have hc₁ : Nat.card ↥(zpowers y₁ ⊔ zpowers a) = 4 := by
    rw [card_zpowers_sup_eq hy₁2 (mem_normalizer_of_commute fun y hy =>
      hEc y₁ hy₁E y (zpowers_le.2 haE hy)) hy₁a, hza]
  obtain ⟨y₂, hy₂E, hy₂n⟩ := Set.not_subset.mp (show ¬ E ≤ zpowers y₁ ⊔ zpowers a from
    fun h => by
      have := Subgroup.card_le_of_le h
      rw [hE.2, hc₁] at this
      omega)
  have hy₂2 := hE.1.2 y₂ hy₂E
  have h8 := isEightGroup_of_three ha2 hy₁2 hy₂2 (hEc a haE y₁ hy₁E) (hEc a haE y₂ hy₂E)
    (hEc y₁ hy₁E y₂ hy₂E) ha1 hy₁a hy₂n
  have hgen : zpowers y₂ ⊔ (zpowers y₁ ⊔ zpowers a) = E :=
    eq_of_le_of_card_ge (sup_le (zpowers_le.2 hy₂E) (sup_le (zpowers_le.2 hy₁E)
      (zpowers_le.2 haE))) (by rw [hE.2, h8.2])
  have hker : ∀ {y : G} (hy : y ∈ E), q (jq J ⟨y, hP.1 (hEP hy)⟩) = 1 → y ∈ zpowers a := by
    intro y hy h1
    rw [← hEa]
    exact mem_inf.mpr ⟨hy, (hzZ (hEP hy)).2 h1⟩
  obtain ⟨k₁, hk₁I, hk₁e⟩ := hIU _ (hEU hy₁E)
  obtain ⟨k₂, hk₂I, hk₂e⟩ := hIU _ (hEU hy₂E)
  have hk₁0 : k₁ ≠ 0 := fun h => hy₁a (hker hy₁E (by rw [← hk₁e, h, wordPerm_tg_zero]))
  have hk₂0 : k₂ ≠ 0 := fun h => hy₂n (mem_sup_right (hker hy₂E
    (by rw [← hk₂e, h, wordPerm_tg_zero])))
  have hk₁₂ : k₁ ≠ k₂ := fun h => by
    apply hy₂n
    have hm : y₁⁻¹ * y₂ ∈ zpowers a := by
      refine hker (E.mul_mem (E.inv_mem hy₁E) hy₂E) ?_
      have e1 : (⟨y₁⁻¹ * y₂, hP.1 (hEP (E.mul_mem (E.inv_mem hy₁E) hy₂E))⟩ : J) =
          (⟨y₁, hP.1 (hEP hy₁E)⟩ : J)⁻¹ * ⟨y₂, hP.1 (hEP hy₂E)⟩ := rfl
      rw [e1, map_mul, map_inv, map_mul, map_inv, ← hk₁e, ← hk₂e, h, inv_mul_cancel]
    rw [show y₂ = y₁ * (y₁⁻¹ * y₂) by group]
    exact mul_mem (mem_sup_left (mem_zpowers y₁)) (mem_sup_right hm)
  have hval : ∀ y : ↥E, (y : G)⁻¹ * (τ y : G) = 1 ∨ (y : G)⁻¹ * (τ y : G) = a := fun y =>
    eq_one_or_eq_of_mem_zpowers ha2 (hτ y)
  set b₁ : Bool := decide ((y₁ : G)⁻¹ * (τ ⟨y₁, hy₁E⟩ : G) = a) with hb₁
  set b₂ : Bool := decide ((y₂ : G)⁻¹ * (τ ⟨y₂, hy₂E⟩ : G) = a) with hb₂
  obtain ⟨w, hwI, hw₁, hw₂⟩ := hQ.exists_transv hkcyc hk4 hâk hâ1 hâ2 hI hk₁I hk₂I hk₁0 hk₂0
    hk₁₂ hk₁e.symm hk₂e.symm b₁ b₂
  obtain ⟨hw64, hwU⟩ := hIk w hwI
  obtain ⟨p, hpP, hpJ, hpe⟩ := (hT (l (cv (tw w)))).1
    (by rw [hQ.q_lift hw64]; exact tg_mem_T0 w hw64)
  have hpe' : jq J ⟨p, hP.1 hpP⟩ = l (cv (tw w)) := hpe
  have hcz : ∀ {y : G} (hy : y ∈ E), y⁻¹ * p⁻¹ * y * p ∈ P ⊓ zStarIn J := by
    intro y hy
    have hyP := hEP hy
    have hm : y⁻¹ * p⁻¹ * y * p ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem (P.inv_mem hyP) (P.inv_mem hpP)) hyP) hpP
    refine mem_inf.mpr ⟨hm, (hzZ hm).2 ?_⟩
    have e1 : (⟨y⁻¹ * p⁻¹ * y * p, hP.1 hm⟩ : J) = (⟨y, hP.1 hyP⟩ : J)⁻¹ *
        (⟨p, hP.1 hpP⟩ : J)⁻¹ * ⟨y, hP.1 hyP⟩ * ⟨p, hP.1 hpP⟩ := rfl
    rw [e1, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    have hc := hUc (hEU hy) (show q (jq J ⟨p, hP.1 hpP⟩) ∈ U by
      rw [hpe', hQ.q_lift hw64]
      exact hwU)
    generalize q (jq J ⟨y, hP.1 hyP⟩) = s at hc ⊢
    generalize q (jq J ⟨p, hP.1 hpP⟩) = t at hc ⊢
    rw [mul_assoc s⁻¹ t⁻¹ s, ← mul_assoc, mul_assoc _ s t, hc]
    group
  have hgood : ∀ {y : G} (hy : y ∈ E) (b : Bool),
      b = decide ((y : G)⁻¹ * (τ ⟨y, hy⟩ : G) = a) →
      jq J ⟨y, hP.1 (hEP hy)⟩ * l (cv (tw w)) * (jq J ⟨y, hP.1 (hEP hy)⟩)⁻¹ *
        (l (cv (tw w)))⁻¹ = (if b then jq J ⟨a, hP.1 haP⟩ else 1) →
      y⁻¹ * p⁻¹ * y * p = y⁻¹ * (τ ⟨y, hy⟩ : G) := by
    intro y hy b hb hw
    have hyP := hEP hy
    have hτy : y⁻¹ * (τ ⟨y, hy⟩ : G) ∈ P := P.mul_mem (P.inv_mem hyP) (hEP (τ ⟨y, hy⟩).2)
    apply eq_of_jq_eq hP.1 hP2 (hcz hy).1 hτy
    have e1 : (⟨y⁻¹ * p⁻¹ * y * p, hP.1 (hcz hy).1⟩ : J) = (⟨y, hP.1 hyP⟩ : J)⁻¹ *
        (⟨p, hP.1 hpP⟩ : J)⁻¹ * ⟨y, hP.1 hyP⟩ * ⟨p, hP.1 hpP⟩ := rfl
    rw [e1]
    simp only [map_mul, map_inv]
    rw [hpe']
    have hcen : ∀ g, g * (if b then jq J ⟨a, hP.1 haP⟩ else 1) =
        (if b then jq J ⟨a, hP.1 haP⟩ else 1) * g := by
      intro g
      split_ifs
      · exact mem_center_iff.mp (hQ.ker_le hâk) g
      · rw [mul_one, one_mul]
    rw [inv_comm_eq hcen hw]
    rcases hval ⟨y, hy⟩ with h | h
    · have hb' : b = false := by
        rw [hb]
        exact decide_eq_false fun h' => ha1 (h'.symm.trans h)
      rw [hb']
      simp only [Bool.false_eq_true, ↓reduceIte]
      have e2 : (⟨y⁻¹ * (τ ⟨y, hy⟩ : G), hP.1 hτy⟩ : J) = 1 := Subtype.ext h
      rw [e2, map_one]
    · have hb' : b = true := by
        rw [hb]
        exact decide_eq_true h
      rw [hb']
      simp only [↓reduceIte]
      have e2 : (⟨y⁻¹ * (τ ⟨y, hy⟩ : G), hP.1 hτy⟩ : J) = ⟨a, hP.1 haP⟩ := Subtype.ext h
      rw [e2]
  have h₁ := hgood hy₁E b₁ hb₁ hw₁
  have h₂ := hgood hy₂E b₂ hb₂ hw₂
  let φ : ↥E →* G :=
    { toFun := fun y => (y : G)⁻¹ * p⁻¹ * y * p
      map_one' := by simp
      map_mul' := fun x y => by
        have hc := (comm_of_mem_Z hP (hcz x.2) (P.inv_mem (hEP y.2))).symm
        simp only [Subgroup.coe_mul]
        calc ((x : G) * y)⁻¹ * p⁻¹ * (x * y) * p =
            (y : G)⁻¹ * ((x : G)⁻¹ * p⁻¹ * x * p) * (p⁻¹ * y * p) := by group
          _ = ((x : G)⁻¹ * p⁻¹ * x * p) * (y : G)⁻¹ * (p⁻¹ * y * p) := by rw [hc]
          _ = (x : G)⁻¹ * p⁻¹ * x * p * ((y : G)⁻¹ * p⁻¹ * y * p) := by group }
  let ψ : ↥E →* G :=
    { toFun := fun y => (y : G)⁻¹ * (τ y : G)
      map_one' := by simp
      map_mul' := fun x y => by
        have hxm : (x : G)⁻¹ * (τ x : G) ∈ E := E.mul_mem (E.inv_mem x.2) (τ x).2
        have hc := hEc _ (E.inv_mem y.2) _ hxm
        simp only [Subgroup.coe_mul, map_mul]
        calc ((x : G) * y)⁻¹ * ((τ x : G) * τ y) =
            (y : G)⁻¹ * ((x : G)⁻¹ * (τ x : G)) * (τ y : G) := by group
          _ = ((x : G)⁻¹ * (τ x : G)) * (y : G)⁻¹ * (τ y : G) := by rw [hc]
          _ = (x : G)⁻¹ * (τ x : G) * ((y : G)⁻¹ * (τ y : G)) := by group }
  have hτa : (τ ⟨a, haE⟩ : G) = a := by
    rcases hval ⟨a, haE⟩ with h | h
    · rw [inv_mul_eq_one] at h
      exact h.symm
    · exfalso
      have h1 : (τ ⟨a, haE⟩ : G) = 1 := by
        calc (τ ⟨a, haE⟩ : G) = a * (a⁻¹ * (τ ⟨a, haE⟩ : G)) := by group
          _ = a * a := by rw [h]
          _ = 1 := ha2
      have h2 : τ ⟨a, haE⟩ = 1 := Subtype.ext h1
      rw [← map_one τ] at h2
      exact ha1 (congrArg Subtype.val (τ.injective h2))
  have hφa : φ ⟨a, haE⟩ = ψ ⟨a, haE⟩ := by
    show a⁻¹ * p⁻¹ * a * p = a⁻¹ * (τ ⟨a, haE⟩ : G)
    rw [hτa, inv_mul_cancel, mul_assoc a⁻¹, ← comm_of_mem_Z hP (mem_inf.mpr ⟨haP, haZ⟩)
      (P.inv_mem hpP)]
    group
  have hle : zpowers y₂ ⊔ (zpowers y₁ ⊔ zpowers a) ≤ (MonoidHom.eqLocus φ ψ).map E.subtype :=
    sup_le (zpowers_le.2 ⟨⟨y₂, hy₂E⟩, h₂, rfl⟩)
      (sup_le (zpowers_le.2 ⟨⟨y₁, hy₁E⟩, h₁, rfl⟩) (zpowers_le.2 ⟨⟨a, haE⟩, hφa, rfl⟩))
  have hall : ∀ y : ↥E, φ y = ψ y := by
    intro y
    obtain ⟨y', hy', hyy'⟩ := hle (hgen ▸ y.2 : (y : G) ∈ zpowers y₂ ⊔ (zpowers y₁ ⊔ zpowers a))
    have : y' = y := Subtype.ext hyy'
    rw [← this]
    exact hy'
  have hconj : ∀ y : ↥E, p⁻¹ * (y : G) * p = (τ y : G) := by
    intro y
    have h1 : (y : G)⁻¹ * p⁻¹ * y * p = (y : G)⁻¹ * (τ y : G) := hall y
    rw [show (y : G)⁻¹ * p⁻¹ * y * p = (y : G)⁻¹ * (p⁻¹ * y * p) by group] at h1
    exact mul_left_cancel h1
  refine ⟨p, mem_inf.mpr ⟨hpP, mem_normalizer_of_conj (fun g hg => ?_) (fun g hg => ?_)⟩,
    hconj⟩
  · have h1 := hconj (τ.symm ⟨g, hg⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    have e1 : p * g * p⁻¹ = (τ.symm ⟨g, hg⟩ : G) := by
      calc p * g * p⁻¹ = p * (p⁻¹ * (τ.symm ⟨g, hg⟩ : G) * p) * p⁻¹ := by rw [h1]
        _ = (τ.symm ⟨g, hg⟩ : G) := by group
    rw [e1]
    exact (τ.symm ⟨g, hg⟩).2
  · rw [hconj ⟨g, hg⟩]
    exact (τ ⟨g, hg⟩).2

end CFSG.ComponentClassification.GrSLit.L34Facts

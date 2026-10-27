module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzLift
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzGamma
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzSigma

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open Subgroup CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm

namespace H1

open Sign

@[expose] noncomputable def czL (i : ℕ) : ↥ruM12 :=
  if h : i < 9 then ⟨czImg i, czImg_mem_ruM12 h⟩ else 1

theorem coe_czL {i : ℕ} (hi : i < 9) : (czL i : Pi7) = czImg i := by
  simp [czL, hi]

theorem coe_evalC_czL {w : List ℕ} (hw : ∀ c ∈ w, c < 18) :
    ((evalC czL w : ↥ruM12) : Pi7) = evalC czImg w := by
  change ruM12.subtype (evalC czL w) = _
  rw [Lift.map_evalC]
  exact evalC_congr fun c hc => coe_czL (by have := hw c hc; omega)

theorem wordProd_natWord {K : Type*} [Group K] (x : ℕ → K) (w : List ℕ) :
    CFSG.Sporadic.Bridge.wordProd x (natWord w) = evalC x w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [show natWord (c :: w) = (c / 2, c % 2 == 0) :: natWord w from rfl, wordProd_cons, ih,
      evalC_cons]
    by_cases hc : c % 2 = 0 <;> simp [hc]

theorem evalW_eq_evalC {K : Type*} [Group K] (x : ℕ → K) (w : List ℕ) :
    CzSigma.evalW x w = evalC x w := by
  induction w with
  | nil => rfl
  | cons c w ih => rw [CzSigma.evalW, evalC_cons, ih]

theorem czImg_rels :
    ∀ r ∈ czRels, FreeGroup.lift (fun i : Fin 10 => czImg i.val) (FreeGroup.mk r) = 1 := by
  intro r hr
  have e : FreeGroup.lift (fun i : Fin 10 => czImg i.val) =
      pi0ToPi7.comp (PresentedGroup.mk {r : FreeGroup (Fin 10) | r ∈ czRels.map FreeGroup.mk}) :=
    FreeGroup.ext_hom _ _ fun i => by
      rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply]
      exact (pi0ToPi7_of i).symm
  rw [e, MonoidHom.comp_apply, PresentedGroup.one_of_mem (List.mem_map_of_mem hr), map_one]

theorem czImg_p12 :
    ∀ r ∈ czP12Codes, evalC czImg r = 1 := by
  intro r hr
  have hlt := Lift.czP12Codes_lt r hr
  have h := czImg_rels (wordOfCodes 10 r) (List.mem_map_of_mem (List.mem_append_left _ hr))
  rw [lift_mk_wordOfCodes _ fun c hc => by have := hlt c hc; omega] at h
  rw [← h]
  refine evalC_congr fun c hc => ?_
  have hc' : c / 2 < 10 := by have := hlt c hc; omega
  rw [ofNat_eq_mk hc']

theorem closure_czL :
    closure (Set.range fun i : Fin 9 => czL i.val) = ⊤ := by
  set K := closure (Set.range fun i : Fin 9 => czL i.val)
  have hle : ruM12 ≤ K.map ruM12.subtype := ruM12_eq_closure.trans_le (closure_le _ |>.2 (by
    rintro _ ⟨i, rfl⟩
    exact ⟨czL i.val, subset_closure ⟨i, rfl⟩, coe_czL i.2⟩))
  rw [eq_top_iff]
  intro m _
  obtain ⟨m', hm', e⟩ := hle m.2
  rwa [show m' = m from Subtype.ext e] at hm'

theorem ruA0_le_ruM12 : ruA0 ≤ ruM12 :=
  closure_le _ |>.2 fun _ ⟨w, hw, e⟩ => e ▸ pi7Word_mem_letterSub
    ((show ∀ w ∈ ruA0Words, ∀ p ∈ w, p.1 ∈ ([0, 1, 2, 3, 4] : List (Fin 7)) by decide) w hw)

structure ModelFacts : Prop where
  z12 : ruM12 ≤ centralizer ({ruZ0} : Set Pi7)
  z0 : czImg 0 ^ 2 = ruZ0
  rels : ∀ r ∈ czRelsJ, evalC czImg r = 1
  conjQ : ∀ i < 6, (czImg 6)⁻¹ * czImg i * czImg 6 = evalC czImg (czWq.getD i [])
  conjV : ∀ i < 6, (czImg 7)⁻¹ * czImg i * czImg 7 = evalC czImg (czWv.getD i [])
  conjW : ∀ i < 6, (czImg 8)⁻¹ * czImg i * czImg 8 = evalC czImg (czWw.getD i [])
  card : Nat.card (closure (czImg '' {i | i < 6})) = 2048

namespace ModelFacts

theorem ruZ0_mem (hM : ModelFacts) : ruZ0 ∈ ruM12 :=
  hM.z0 ▸ pow_mem (czImg_mem_ruM12 (by norm_num)) 2

@[expose] noncomputable def z (hM : ModelFacts) : ↥ruM12 := ⟨ruZ0, hM.ruZ0_mem⟩

theorem czL_sq (hM : ModelFacts) : czL 0 ^ 2 = hM.z :=
  Subtype.ext (by rw [SubgroupClass.coe_pow, coe_czL (by norm_num), hM.z0]; rfl)

theorem comm_z (hM : ModelFacts) (m : ↥ruM12) : m * hM.z = hM.z * m :=
  Subtype.ext (mem_centralizer_singleton_iff.1 (hM.z12 m.2))

end ModelFacts

variable {G : Type} [Group G] {A : Subgroup G} {f : G}

@[expose] noncomputable def edgeHom (hM : ModelFacts) (e : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (he : ∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((e m : ↥(normalizer (A : Set G))) : G) = f) :
    ↥ruM12 →* ↥(centralizer ({f} : Set G)) :=
  (((normalizer (A : Set G)).subtype.comp e.toMonoidHom).comp
    (inclusion RuAsm.ruM12_le_ruM2)).codRestrict _ fun m => by
    rw [mem_centralizer_singleton_iff]
    set F := ((normalizer (A : Set G)).subtype.comp e.toMonoidHom).comp
      (inclusion RuAsm.ruM12_le_ruM2)
    have hF : F hM.z = f := he _ rfl
    rw [← hF, ← map_mul, hM.comm_z, map_mul]

theorem coe_edgeHom (hM : ModelFacts) (e : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (he : ∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((e m : ↥(normalizer (A : Set G))) : G) = f)
    (m : ↥ruM12) :
    ((edgeHom hM e he m : ↥(centralizer ({f} : Set G))) : G) =
      ((e (inclusion RuAsm.ruM12_le_ruM2 m) : ↥(normalizer (A : Set G))) : G) := rfl

theorem edgeHom_injective (hM : ModelFacts) (e : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (he : ∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((e m : ↥(normalizer (A : Set G))) : G) = f) :
    Function.Injective (edgeHom hM e he) := fun a b hab => by
  have h := congrArg Subtype.val hab
  rw [coe_edgeHom, coe_edgeHom] at h
  exact inclusion_injective _ (e.injective (Subtype.ext h))

theorem edgeHom_z (hM : ModelFacts) (e : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (he : ∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((e m : ↥(normalizer (A : Set G))) : G) = f) :
    ((edgeHom hM e he hM.z : ↥(centralizer ({f} : Set G))) : G) = f :=
  he _ rfl

section Letters

variable (hM : ModelFacts) (e : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
  (he : ∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((e m : ↥(normalizer (A : Set G))) : G) = f)

theorem evalC_edge (w : List ℕ) :
    evalC (fun i => edgeHom hM e he (czL i)) w = edgeHom hM e he (evalC czL w) :=
  (Lift.map_evalC _ _ _).symm

theorem evalC_edge_eq_one {w : List ℕ} (hw : ∀ c ∈ w, c < 18) (h : evalC czImg w = 1) :
    evalC (fun i => edgeHom hM e he (czL i)) w = 1 := by
  rw [evalC_edge, show evalC czL w = 1 from Subtype.ext ((coe_evalC_czL hw).trans h), map_one]

@[expose] noncomputable def jSub : Subgroup ↥ruM12 := closure (czL '' {i | i < 6})

theorem map_jSub : jSub.map ruM12.subtype = closure (czImg '' {i | i < 6}) := by
  rw [jSub, MonoidHom.map_closure, ← Set.image_comp]
  exact congrArg Subgroup.closure (Set.image_congr fun i hi => coe_czL (by
    have hi' : i < 6 := hi
    omega))

theorem mem_jSub_iff (m : ↥ruM12) : m ∈ jSub ↔ (m : Pi7) ∈ closure (czImg '' {i | i < 6}) := by
  rw [← map_jSub]
  exact (mem_map_iff_mem ruM12.subtype_injective).symm

theorem closure_edge :
    closure ((fun i => edgeHom hM e he (czL i)) '' {i | i < 6}) = jSub.map (edgeHom hM e he) := by
  rw [jSub, MonoidHom.map_closure, ← Set.image_comp]
  rfl

theorem card_closure_edge (hM : ModelFacts) :
    Nat.card (closure ((fun i => edgeHom hM e he (czL i)) '' {i | i < 6})) = 2048 := by
  rw [closure_edge, card_map_of_injective (edgeHom_injective hM e he), ← hM.card, ← map_jSub,
    card_map_of_injective ruM12.subtype_injective]

theorem isLetters
    (σ : ↥(centralizer ({f} : Set G)) →* Equiv.Perm (Fin 5))
    (hker : σ.ker = closure ((fun i => edgeHom hM e he (czL i)) '' {i | i < 6}))
    (h6 : σ (edgeHom hM e he (czL 6)) = Equiv.swap 2 3 * Equiv.swap 3 4)
    (h7 : σ (edgeHom hM e he (czL 7)) = Equiv.swap 2 3)
    (h8 : σ (edgeHom hM e he (czL 8)) = Equiv.swap 1 2) :
    Lift.IsLetters σ fun i => edgeHom hM e he (czL i) := by
  have hone : ∀ {w : List ℕ}, (∀ c ∈ w, c < 18) → evalC czImg w = 1 →
      evalC (fun i => edgeHom hM e he (czL i)) w = 1 := fun hw h => evalC_edge_eq_one hM e he hw h
  have hconj : ∀ {y : ℕ} (hy : y < 9) {W : ℕ → List ℕ} (hW : ∀ i < 6, ∀ c ∈ W i, c < 12)
      (hc : ∀ i < 6, (czImg y)⁻¹ * czImg i * czImg y = evalC czImg (W i)) (i : ℕ) (hi : i < 6),
      (edgeHom hM e he (czL y))⁻¹ * edgeHom hM e he (czL i) * edgeHom hM e he (czL y) =
        evalC (fun i => edgeHom hM e he (czL i)) (W i) := by
    intro y hy W hW hc i hi
    rw [evalC_edge, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [coe_evalC_czL fun c h => by have := hW i hi c h; omega, coe_mul, coe_mul, coe_inv,
      coe_czL hy, coe_czL (by omega), hc i hi]
  refine ⟨fun r hr => hone (fun c hc => by have := Lift.czRelsJ_lt r hr c hc; omega)
    (hM.rels r hr), card_closure_edge e he hM, hker,
    hconj (by norm_num) (fun i hi => (Lift.czW_lt i hi).1) hM.conjQ,
    hconj (by norm_num) (fun i hi => (Lift.czW_lt i hi).2.1) hM.conjV,
    hconj (by norm_num) (fun i hi => (Lift.czW_lt i hi).2.2) hM.conjW,
    fun r hr => hone (Lift.czP12Codes_lt r hr) (czImg_p12 r hr), ?_, h6, h7, h8⟩
  rw [← map_pow, hM.czL_sq, mem_center_iff]
  intro g
  apply Subtype.ext
  rw [coe_mul, coe_mul, edgeHom_z]
  exact mem_centralizer_singleton_iff.1 g.2

end Letters

theorem subgroupOf_eq (hM : ModelFacts) (e : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (he : ∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((e m : ↥(normalizer (A : Set G))) : G) = f)
    {Q : Subgroup G}
    (hQJ : ∀ g : G, g ∈ Q ↔ ∃ m : ↥ruM2, (m : Pi7) ∈ closure (czImg '' {i | i < 6}) ∧
      ((e m : ↥(normalizer (A : Set G))) : G) = g) :
    Q.subgroupOf (centralizer ({f} : Set G)) =
      closure ((fun i => edgeHom hM e he (czL i)) '' {i | i < 6}) := by
  rw [closure_edge]
  ext g
  rw [mem_subgroupOf, hQJ]
  constructor
  · rintro ⟨m, hm, hmg⟩
    have hm12 : (m : Pi7) ∈ ruM12 := (closure_le _).2 (by
      rintro _ ⟨i, hi, rfl⟩
      exact czImg_mem_ruM12 (by have hi' : i < 6 := hi; omega)) hm
    exact ⟨⟨m, hm12⟩, (mem_jSub_iff _).2 hm, Subtype.ext hmg⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨inclusion RuAsm.ruM12_le_ruM2 m, (mem_jSub_iff m).1 hm, rfl⟩

theorem card_centralizer {Q : Subgroup G} (σ : ↥(centralizer ({f} : Set G)) →* Equiv.Perm (Fin 5))
    (hσ : Function.Surjective σ) (hker : σ.ker = Q.subgroupOf (centralizer ({f} : Set G)))
    (hQC : Q ≤ centralizer ({f} : Set G)) (hQ : Nat.card Q = 2 ^ 11) :
    Nat.card (centralizer ({f} : Set G)) = 245760 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective σ hσ).toEquiv, hker,
    Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, hQ, Nat.card_perm,
    Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at h1
  rw [h1]
  rfl

section Main


theorem exists_normCz [Finite G] (hM : ModelFacts) (hR : ∀ (K : Type) [Group K], Lift.RigidHyp K)
    (hN : ∀ (K : Type) [Group K], Lift.NormHyp K) (hC : ∀ (K : Type) [Group K], Lift.Class2Hyp K)
    (hS : ∀ (K : Type) [Group K], Lift.SignHyp K) {Q : Subgroup G}
    (hQC : Q ≤ centralizer ({f} : Set G))
    (σ : ↥(centralizer ({f} : Set G)) →* Equiv.Perm (Fin 5)) (hσ : Function.Surjective σ)
    (hker : σ.ker = Q.subgroupOf (centralizer ({f} : Set G))) (hQ : Nat.card Q = 2 ^ 11)
    (f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (hz₂ : ∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((f₂ m : ↥(normalizer (A : Set G))) : G) = f)
    (hA₂ : ∀ m : ↥ruM2, (m : Pi7) ∈ ruA0 ↔ ((f₂ m : ↥(normalizer (A : Set G))) : G) ∈ A)
    (hQJ : ∀ g : G, g ∈ Q ↔ ∃ m : ↥ruM2, (m : Pi7) ∈ closure (czImg '' {i | i < 6}) ∧
      ((f₂ m : ↥(normalizer (A : Set G))) : G) = g) :
    ∃ f₂' : ↥ruM2 ≃* ↥(normalizer (A : Set G)),
      (∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((f₂' m : ↥(normalizer (A : Set G))) : G) = f) ∧
      (∀ m : ↥ruM2, (m : Pi7) ∈ ruA0 ↔ ((f₂' m : ↥(normalizer (A : Set G))) : G) ∈ A) ∧
      ∃ f₁ : ↥ruM1 ≃* ↥(centralizer ({f} : Set G)), IsNormCz f₁ A ∧
        RuEdgeAgree f₁ f₂' (MonoidHom.id _) := by
  classical
  have hCcard := card_centralizer σ hσ hker hQC hQ
  obtain ⟨f₂g, hf₂g⟩ : ∃ f₂g : ↥ruM2 ≃* ↥(normalizer (A : Set G)), f₂g = czGamma.trans f₂ :=
    ⟨_, rfl⟩
  have hz₂g : ∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((f₂g m : ↥(normalizer (A : Set G))) : G) = f :=
    fun m hm => by rw [hf₂g, MulEquiv.trans_apply, czGamma_z0 m hm]; exact hz₂ m hm
  have hA₂g : ∀ m : ↥ruM2, (m : Pi7) ∈ ruA0 ↔ ((f₂g m : ↥(normalizer (A : Set G))) : G) ∈ A := by
    intro m
    rw [hf₂g, MulEquiv.trans_apply, ← hA₂]
    constructor
    · intro hm
      rw [czGamma_fix_ruA0 m hm]
      exact hm
    · intro hm
      rw [czGamma.injective (czGamma_fix_ruA0 _ hm)] at hm
      exact hm
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ↥(centralizer ({f} : Set G)), k = fun i => edgeHom hM f₂ hz₂ (czL i) :=
    ⟨_, rfl⟩
  obtain ⟨k', hk'⟩ : ∃ k' : ℕ → ↥(centralizer ({f} : Set G)),
      k' = fun i => edgeHom hM f₂g hz₂g (czL i) := ⟨_, rfl⟩
  have hQk : Q.subgroupOf (centralizer ({f} : Set G)) = closure (k '' {i | i < 6}) := by
    rw [hk]; exact subgroupOf_eq hM f₂ hz₂ hQJ
  have hkp12 : ∀ r ∈ czP12Codes, evalC k r = 1 := fun r hr => by
    rw [hk]; exact evalC_edge_eq_one hM f₂ hz₂ (Lift.czP12Codes_lt r hr) (czImg_p12 r hr)
  have hP9 : ∀ r ∈ czP12Codes,
      FreeGroup.lift (fun i : Fin 9 => k i.val) (FreeGroup.mk (wordOfCodes 9 r)) = 1 := by
    intro r hr
    rw [CzSigma.lift_mk_wordOfCodes _ (CzSigma.codes_lt r hr), evalW_eq_evalC, ← hkp12 r hr]
    exact evalC_congr fun c hc => by
      rw [CzSigma.ofNat_eq_mk (by have := CzSigma.codes_lt r hr c hc; omega)]
  have hcard9 : Nat.card (closure (Set.range fun i : Fin 9 => k i.val)) =
      24 * Nat.card (Q.subgroupOf (centralizer ({f} : Set G))) := by
    have e : closure (Set.range fun i : Fin 9 => k i.val) = (⊤ : Subgroup ↥ruM12).map
        (edgeHom hM f₂ hz₂) := by
      rw [← closure_czL, MonoidHom.map_closure, ← Set.range_comp, hk]
      rfl
    rw [e, card_map_of_injective (edgeHom_injective hM f₂ hz₂), Subgroup.card_top, card_ruM12,
      Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, hQ]
    norm_num
  obtain ⟨σ', hσ's, hσ'k, hσ'x⟩ := exists_sigma0 σ hσ hker (fun i : Fin 9 => k i.val) hP9
    (fun i hi => hQk ▸ subset_closure ⟨i.val, hi, rfl⟩) hcard9
  have h6 : σ' (k 6) = Equiv.swap 2 3 * Equiv.swap 3 4 := by
    rw [show k 6 = k (6 : Fin 9).val from rfl, hσ'x]; decide
  have h7 : σ' (k 7) = Equiv.swap 2 3 := by
    rw [show k 7 = k (7 : Fin 9).val from rfl, hσ'x]; decide
  have h8 : σ' (k 8) = Equiv.swap 1 2 := by
    rw [show k 8 = k (8 : Fin 9).val from rfl, hσ'x]; decide
  have hkL : Lift.IsLetters σ' k := by
    rw [hk] at h6 h7 h8 hQk ⊢
    exact isLetters hM f₂ hz₂ σ' (hσ'k.trans hQk) h6 h7 h8
  have hinc : ∀ {i : ℕ} (hi : i < 9), inclusion RuAsm.ruM12_le_ruM2 (czL i) =
      ⟨czImg i, czImg_mem_ruM2 hi⟩ := fun hi => Subtype.ext (coe_czL hi)
  have hk'k : ∀ {i : ℕ} (hi : i < 9) (w : List ℕ), (∀ c ∈ w, c < 18) →
      ((czGamma ⟨czImg i, czImg_mem_ruM2 hi⟩ : ↥ruM2) : Pi7) = evalC czImg w →
      k' i = evalC k w := by
    intro i hi w hw h
    apply Subtype.ext
    have e : czGamma ⟨czImg i, czImg_mem_ruM2 hi⟩ = inclusion RuAsm.ruM12_le_ruM2 (evalC czL w) :=
      Subtype.ext (by rw [h, coe_inclusion, coe_evalC_czL hw])
    rw [hk', hk, evalC_edge, coe_edgeHom, coe_edgeHom, hf₂g, MulEquiv.trans_apply, hinc hi, e]
  have hk'j : ∀ i < 6, k' i = evalC k (c2JCodes.getD i []) := fun i hi =>
    hk'k (by omega) _ (fun c hc => by
      have := (show ∀ i < 6, ∀ c ∈ c2JCodes.getD i [], c < 12 by decide +kernel) i hi c hc
      omega) (by rw [czGamma_j hi, wordProd_natWord])
  have hk'q : k' 6 = k 6 := by
    apply Subtype.ext
    rw [hk', hk, coe_edgeHom, coe_edgeHom, hf₂g, MulEquiv.trans_apply, hinc (by norm_num)]
    congr 2
    exact Subtype.ext czGamma_q
  have htriv : ∀ {y : ℕ} (hy : y < 9), σ' (k' y) = σ' (k y) := by
    intro y hy
    have hw : ∀ c ∈ c2TrivCodes.getD y [], c < 12 :=
      (show ∀ y < 9, ∀ c ∈ c2TrivCodes.getD y [], c < 12 by decide +kernel) y hy
    have e : k' y = evalC k (c2TrivCodes.getD y [] ++ [2 * y]) := by
      refine hk'k hy _ (fun c hc => ?_) ?_
      · rcases List.mem_append.1 hc with hc | hc
        · have := hw c hc; omega
        · rw [List.mem_singleton] at hc; omega
      · rw [czGamma_triv hy, wordProd_natWord, evalC_append, evalC_cons, evalC_nil, mul_one,
          ite_eq_left (by omega), show 2 * y / 2 = y by omega]
    rw [e, evalC_append, map_mul, evalC_cons, evalC_nil, mul_one, ite_eq_left (by omega),
      show 2 * y / 2 = y by omega]
    have h1 : σ' (evalC k (c2TrivCodes.getD y [])) = 1 := by
      rw [← MonoidHom.mem_ker, hkL.ker]
      exact Lift.evalC_mem_closure k fun c hc => hw c hc
    rw [h1, one_mul]
  have hker' : σ'.ker = closure (k' '' {i | i < 6}) := by
    have hle : closure (k' '' {i | i < 6}) ≤ closure (k '' {i | i < 6}) := by
      rw [closure_le]
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i < 6 := hi
      rw [hk'j i hi']
      exact Lift.evalC_mem_closure k fun c hc => by
        have := (show ∀ i < 6, ∀ c ∈ c2JCodes.getD i [], c < 12 by decide +kernel) i hi' c hc
        omega
    have hcard : Nat.card (closure (k '' {i | i < 6})) ≤ Nat.card (closure (k' '' {i | i < 6})) :=
      by rw [hk, hk', card_closure_edge f₂ hz₂ hM, card_closure_edge f₂g hz₂g hM]
    rw [hkL.ker, Subgroup.eq_of_le_of_card_ge hle hcard]
  have hk'L : Lift.IsLetters σ' k' := by
    have h6' : σ' (k' 6) = Equiv.swap 2 3 * Equiv.swap 3 4 := by rw [hk'q, h6]
    have h7' : σ' (k' 7) = Equiv.swap 2 3 := by rw [htriv (by norm_num), h7]
    have h8' : σ' (k' 8) = Equiv.swap 1 2 := by rw [htriv (by norm_num), h8]
    rw [hk'] at h6' h7' h8' hker' ⊢
    exact isLetters hM f₂g hz₂g σ' hker' h6' h7' h8'
  have hQp : IsPGroup 2 (Q.subgroupOf (centralizer ({f} : Set G))) :=
    IsPGroup.of_card (n := 11) (by rw [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, hQ])
  have hy3 : k 6 ^ 3 = 1 := by
    have e := hkp12 [12, 12, 12] (by decide +kernel)
    rw [evalC_cons, evalC_cons, evalC_cons, evalC_nil, ite_eq_left (by norm_num),
      show (12 : ℕ) / 2 = 6 by norm_num, mul_one] at e
    rw [pow_three, e]
  obtain ⟨h, hhk, hσh⟩ := exists_comm_swap σ' hσ's hσ'k hQp (by
    rw [show k 6 = k (6 : Fin 9).val from rfl, hσ'x]; rfl) hy3
  obtain ⟨x, hx, hxgen, hxrel⟩ := Lift.exists_letters hkL hk'L hk'j hk'q hσh hhk
    (hR _) (hN _) (hC _) (hS _) (fun y hrel hgen => card_le_of_eps1 y hrel hgen)
    (fun y hrel hgen => card_le_of_eps2 y hrel hgen)
    (fun y hrel hgen => card_le_of_eps3 y hrel hgen) hCcard
  have hfin := card_pi0_le.1
  obtain ⟨φ, hφ⟩ : ∃ φ : Pi0 →* ↥(centralizer ({f} : Set G)), ∀ i, φ (PresentedGroup.of i) = x i :=
    ⟨PresentedGroup.toGroup (f := x) fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
      exact hxrel w hw, fun i => PresentedGroup.toGroup.of _⟩
  have hφs : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hxgen, closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, hφ i⟩
  have hφb : Function.Bijective φ := hφs.bijective_of_nat_card_le (card_pi0_le.2.trans hCcard.ge)
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : ↥ruM1 ≃* ↥(centralizer ({f} : Set G)),
      f₁ = pi0Equiv.symm.trans (MulEquiv.ofBijective φ hφb) := ⟨_, rfl⟩
  have hf₁x : ∀ {i : ℕ} (hi : i < 10), f₁ ⟨czImg i, czImg_mem_ruM1 hi⟩ = x ⟨i, hi⟩ := by
    intro i hi
    have h1 : pi0Equiv.symm ⟨czImg i, czImg_mem_ruM1 hi⟩ = PresentedGroup.of ⟨i, hi⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (pi0Equiv_of ⟨i, hi⟩).symm
    rw [hf₁, MulEquiv.trans_apply, h1, MulEquiv.ofBijective_apply, hφ]
  obtain ⟨f₂', hz', hA', hx'⟩ : ∃ f₂' : ↥ruM2 ≃* ↥(normalizer (A : Set G)),
      ∃ hz' : (∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((f₂' m : ↥(normalizer (A : Set G))) : G) = f),
      (∀ m : ↥ruM2, (m : Pi7) ∈ ruA0 ↔ ((f₂' m : ↥(normalizer (A : Set G))) : G) ∈ A) ∧
      ∀ i : Fin 10, i.val < 9 → x i = edgeHom hM f₂' hz' (czL i.val) := by
    rcases hx with hx | hx
    · exact ⟨f₂, hz₂, hA₂, fun i hi => by rw [hx i hi, hk]⟩
    · exact ⟨f₂g, hz₂g, hA₂g, fun i hi => by rw [hx i hi, hk']⟩
  have hagree : f₁.toMonoidHom.comp (inclusion RuAsm.ruM12_le_ruM1) = edgeHom hM f₂' hz' := by
    refine MonoidHom.eq_of_eqOn_dense closure_czL ?_
    rintro _ ⟨i, rfl⟩
    have e1 : inclusion RuAsm.ruM12_le_ruM1 (czL i.val) =
        ⟨czImg i.val, czImg_mem_ruM1 (by omega)⟩ := Subtype.ext (coe_czL i.2)
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e1, hf₁x (by omega),
      hx' ⟨i.val, by omega⟩ i.2]
  have hedge : RuEdgeAgree f₁ f₂' (MonoidHom.id _) := fun m =>
    congrArg Subtype.val (DFunLike.congr_fun hagree m)
  refine ⟨f₂', hz', hA', f₁, ⟨fun m hm => ?_, fun m => ⟨fun hmA => ?_, fun hfA => ?_⟩⟩, hedge⟩
  · rw [show m = inclusion RuAsm.ruM12_le_ruM1 hM.z from Subtype.ext hm, hedge]
    exact hz' _ rfl
  · have hm12 : (m : Pi7) ∈ ruM12 := ruA0_le_ruM12 hmA
    rw [show m = inclusion RuAsm.ruM12_le_ruM1 ⟨m, hm12⟩ from rfl, hedge]
    exact (hA' _).1 hmA
  · have hgN : ((f₁ m : ↥(centralizer ({f} : Set G))) : G) ∈ normalizer (A : Set G) :=
      le_normalizer hfA
    have hm' : ((f₂'.symm ⟨_, hgN⟩ : ↥ruM2) : Pi7) ∈ ruA0 :=
      (hA' _).2 (by rw [MulEquiv.apply_symm_apply]; exact hfA)
    have hm'12 := ruA0_le_ruM12 hm'
    have h1 : f₁ (inclusion RuAsm.ruM12_le_ruM1 ⟨_, hm'12⟩) = f₁ m := by
      apply Subtype.ext
      rw [hedge]
      change ((f₂' (f₂'.symm ⟨_, hgN⟩) : ↥(normalizer (A : Set G))) : G) = _
      rw [MulEquiv.apply_symm_apply]
    rw [← f₁.injective h1]
    exact hm'

end Main

end H1

end CFSG.ComponentClassification.GMS78.RuCz

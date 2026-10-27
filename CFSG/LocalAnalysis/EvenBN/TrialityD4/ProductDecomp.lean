module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN1Quot
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCommute
import CFSG.LocalAnalysis.EvenBN.TrialityD4.FieldCaseSylow

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

section Defs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def aOne (K₁ : Subgroup G) : Subgroup G :=
  ⁅⁅K₁, K₁⁆, ⁅K₁, K₁⁆⁆

@[expose] noncomputable def aTwo (d : TrialityD4Data L q) (t : G) (K : Subgroup G) :
    Subgroup G :=
  kThree d t K ⊔ pCoreOf 2 ⁅kFive d t K, kFive d t K⁆

end Defs

namespace ProductDecompAux

section Conj

variable {G : Type*} [Group G]

theorem inv_eq_of_involution {t : G} (ht : t * t = 1) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right ht

theorem mem_conjT_iff {t : G} (ht : t * t = 1) {A : Subgroup G} {x : G} :
    x ∈ Aᵍ[t] ↔ t * x * t ∈ A := by
  rw [mem_map_conj_inv_iff, inv_eq_of_involution ht]

theorem conj_mem_conjT {t : G} (ht : t * t = 1) {A : Subgroup G} {x : G} (hx : x ∈ A) :
    t * x * t ∈ Aᵍ[t] := by
  rw [mem_conjT_iff ht]
  have : t * (t * x * t) * t = x := by
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht]; group
  rw [this]
  exact hx

theorem conjT_conjT {t : G} (ht : t * t = 1) (A : Subgroup G) : (Aᵍ[t])ᵍ[t] = A :=
  map_conj_inv_map_conj_inv ht A

theorem conjT_sup (t : G) (A B : Subgroup G) : (A ⊔ B)ᵍ[t] = Aᵍ[t] ⊔ Bᵍ[t] :=
  Subgroup.map_sup _ _ _

theorem conjT_inf (t : G) (A B : Subgroup G) : (A ⊓ B)ᵍ[t] = Aᵍ[t] ⊓ Bᵍ[t] :=
  Subgroup.map_inf_eq A B _ (MulAut.conj t⁻¹).injective

theorem conjT_bot (t : G) : (⊥ : Subgroup G)ᵍ[t] = ⊥ :=
  Subgroup.map_bot _

theorem conjT_commutator (t : G) (A B : Subgroup G) : (⁅A, B⁆ : Subgroup G)ᵍ[t] = ⁅Aᵍ[t], Bᵍ[t]⁆ :=
  Subgroup.map_commutator _ _ _

theorem card_conjT (t : G) (A : Subgroup G) : Nat.card (Aᵍ[t] : Subgroup G) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective

theorem conjT_eq_of_mem_normalizer {t : G} {A : Subgroup G}
    (ht : t ∈ normalizer (A : Set G)) : Aᵍ[t] = A := by
  ext x
  rw [mem_map_conj_inv_iff]
  exact (mem_normalizer_iff.1 ht x).symm

theorem commutator_eq_bot_iff {A B : Subgroup G} :
    ⁅A, B⁆ = ⊥ ↔ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  rw [commutator_eq_bot_iff_le_centralizer]
  constructor
  · intro h a ha b hb
    exact (mem_centralizer_iff.1 (h ha) b hb).symm
  · intro h a ha
    exact mem_centralizer_iff.2 fun b hb => (h a ha b hb).symm

theorem mem_normalizer_map_conj_of {A : Subgroup G} {g j : G}
    (hj : g * j * g⁻¹ ∈ normalizer (A : Set G)) :
    j ∈ normalizer ((A.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_map_conj_inv_iff, mem_map_conj_inv_iff]
  have e : g * (j * x * j⁻¹) * g⁻¹ = (g * j * g⁻¹) * (g * x * g⁻¹) * (g * j * g⁻¹)⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.1 hj (g * x * g⁻¹)

theorem commutator_sup_sup_eq_bot {A B C D : Subgroup G} (hAC : ⁅A, C⁆ = ⊥) (hAD : ⁅A, D⁆ = ⊥)
    (hBC : ⁅B, C⁆ = ⊥) (hBD : ⁅B, D⁆ = ⊥) : ⁅A ⊔ B, C ⊔ D⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer] at hAC hAD hBC hBD ⊢
  refine sup_le ?_ ?_
  · exact le_centralizer_iff.2 (sup_le (le_centralizer_iff.1 hAC) (le_centralizer_iff.1 hAD))
  · exact le_centralizer_iff.2 (sup_le (le_centralizer_iff.1 hBC) (le_centralizer_iff.1 hBD))

end Conj

section Generic

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_of_forall_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} : x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
        mul_mem' := fun {x y} hx hy => by
          obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
          obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy
          refine ⟨a₁ * a₂, mul_mem ha₁ ha₂, b₁ * b₂, mul_mem hb₁ hb₂, ?_⟩
          have e := h a₂ ha₂ b₁ hb₁
          calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
            _ = a₁ * (b₁ * a₂) * b₂ := by rw [e]
            _ = a₁ * b₁ * (a₂ * b₂) := by group
        one_mem' := ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
        inv_mem' := fun {x} hx => by
          obtain ⟨a, ha, b, hb, rfl⟩ := hx
          refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
          have e := h a ha b hb
          calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
            _ = (a * b)⁻¹ := by rw [e] }
    have hle : A ⊔ B ≤ S := sup_le
      (fun a ha => ⟨a, ha, 1, one_mem _, mul_one a⟩)
      (fun b hb => ⟨1, one_mem _, b, hb, one_mul b⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem inf_sup_eq_of_le_of_commute {A B C : Subgroup G} (hAC : A ≤ C)
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : C ⊓ (A ⊔ B) = A ⊔ (C ⊓ B) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxC, hxAB⟩ := mem_inf.1 hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_forall_commute h).1 hxAB
    have hbC : b ∈ C := by
      have := mul_mem (inv_mem (hAC ha)) hxC
      simpa using this
    exact mul_mem (mem_sup_left ha) (mem_sup_right (mem_inf.2 ⟨hbC, hb⟩))
  · exact sup_le (le_inf hAC le_sup_left)
      (le_inf inf_le_left (inf_le_right.trans le_sup_right))

theorem eq_sup_commutator_of_complement {C O E E' J : Subgroup G}
    (hCO : C ≤ O) (hO2 : IsPGroup 2 O) (hJ : Odd (Nat.card J))
    (hJC : J ≤ normalizer (C : Set G)) (hEC : E ≤ C) (hE'O : E' ≤ O)
    (hE'c : E' ≤ centralizer (O : Set G)) (hJE' : J ≤ centralizer (E' : Set G))
    (hCE' : C ⊓ E' = ⊥) (hCsup : C ⊔ E' = O)
    (hfix : O ⊓ centralizer (J : Set G) ≤ E ⊔ E') :
    C = E ⊔ ⁅O, J⁆ := by
  have hcomm : ∀ X : Subgroup G, X ≤ O → ∀ a ∈ X, ∀ b ∈ E', a * b = b * a := by
    intro X hX a ha b hb
    exact mem_centralizer_iff.1 (hE'c hb) a (hX ha)
  apply le_antisymm
  · intro m hm
    have hNM : ⁅C, J⁆ ≤ C := le_normalizer_iff_commutator_le_left.1 hJC
    have hC2 : IsPGroup 2 C := hO2.to_le hCO
    have hcop : (Nat.card J).Coprime (Nat.card C) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hC2
      rw [hn]
      exact Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hJ)
    have hsolv : Group.IsSolvable C := by
      haveI : Group.IsNilpotent C := hC2.isNilpotent
      infer_instance
    obtain ⟨c, hc, n, hn, rfl⟩ := exists_mem_inf_centralizer_mul_of_coprime hNM
      (normalizer_commutator_ge_left C J) hJC (normalizer_commutator_ge_right C J) hsolv hcop hm
      (fun s hs => by
        have h1 := commutator_mem_commutator (inv_mem hm) hs
        have e : m⁻¹ * (s * m * s⁻¹) = m⁻¹ * s * m⁻¹⁻¹ * s⁻¹ := by group
        rw [e]
        exact h1)
    obtain ⟨hcC, hcJ⟩ := mem_inf.1 hc
    have hcEE' : c ∈ E ⊔ E' := hfix (mem_inf.2 ⟨hCO hcC, hcJ⟩)
    obtain ⟨e, he, e', he', hee⟩ :=
      (mem_sup_of_forall_commute (hcomm E (hEC.trans hCO))).1 hcEE'
    have he'C : e' ∈ C := by
      have h1 : e⁻¹ * c ∈ C := mul_mem (inv_mem (hEC he)) hcC
      have h2 : e⁻¹ * c = e' := by
        rw [← hee]
        group
      rwa [h2] at h1
    have he'1 : e' = 1 := by
      have h1 : e' ∈ C ⊓ E' := mem_inf.2 ⟨he'C, he'⟩
      rw [hCE', mem_bot] at h1
      exact h1
    have hcE : c ∈ E := by
      have : c = e := by
        rw [← hee, he'1, mul_one]
      rwa [this]
    have hnO : n ∈ ⁅O, J⁆ := commutator_mono hCO le_rfl hn
    exact mul_mem (mem_sup_left hcE) (mem_sup_right hnO)
  · refine sup_le hEC (commutator_le.2 fun o ho j hj => ?_)
    show o * j * o⁻¹ * j⁻¹ ∈ C
    have ho' : o ∈ C ⊔ E' := hCsup ▸ ho
    obtain ⟨c, hc, e', he', rfl⟩ := (mem_sup_of_forall_commute (hcomm C hCO)).1 ho'
    have hje : e' * j = j * e' := mem_centralizer_iff.1 (hJE' hj) e' he'
    have h1 : e' * j * e'⁻¹ = j := by
      rw [hje]
      group
    have e1 : c * e' * j * (c * e')⁻¹ * j⁻¹ = c * (j * c⁻¹ * j⁻¹) := by
      calc c * e' * j * (c * e')⁻¹ * j⁻¹ = c * (e' * j * e'⁻¹) * c⁻¹ * j⁻¹ := by group
        _ = c * (j * c⁻¹ * j⁻¹) := by
            rw [h1]
            group
    rw [e1]
    exact mul_mem hc ((mem_normalizer_iff.1 (hJC hj) _).1 (inv_mem hc))

theorem commutator_inf_eq_bot_of_sylow_complement {T V S₀ P₀ : Subgroup G}
    (hVT : V ≤ T) (hVc : V ≤ centralizer (T : Set G)) (hV2 : IsPGroup 2 V)
    (hS : IsSylowOf 2 S₀ T) (hVS : V ⊔ P₀ = S₀) (hVP : V ⊓ P₀ = ⊥) :
    ⁅T, T⁆ ⊓ V = ⊥ := by
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  have hP₀S : P₀ ≤ S₀ := hVS ▸ le_sup_right
  have hS₀T : S₀ ≤ T := hS.le
  have hP₀T : P₀ ≤ T := hP₀S.trans hS₀T
  set V' : Subgroup T := V.subgroupOf T with hV'
  have hcentral : ∀ v ∈ V', ∀ t : T, t * v = v * t := by
    intro v hv t
    exact Subtype.ext (mem_centralizer_iff.1 (hVc hv) t t.2)
  haveI : V'.Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = n := by
      rw [hcentral n hn g]
      group
    rw [e]
    exact hn⟩
  haveI : IsMulCommutative V' := ⟨⟨fun a b => Subtype.ext (hcentral b b.2 a)⟩⟩
  have hV'2 : IsPGroup 2 V' := hV2.comap_subtype
  have hex : ∃ K : Subgroup T, K ≤ (Q : Subgroup T) ∧ V' ⊓ K = ⊥ ∧ V' ⊔ K = (Q : Subgroup T) := by
    refine ⟨P₀.subgroupOf T, ?_, ?_, ?_⟩
    · rw [hQ]
      exact fun x hx => hP₀S hx
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxV, hxP⟩ := mem_inf.1 hx
      have h1 : (x : G) ∈ V ⊓ P₀ := mem_inf.2 ⟨mem_subgroupOf.1 hxV, mem_subgroupOf.1 hxP⟩
      rw [hVP, mem_bot] at h1
      exact mem_bot.2 (Subtype.ext h1)
    · rw [hQ, ← subgroupOf_sup hVT hP₀T, hVS]
  obtain ⟨K', hK'⟩ := (CFSG.Quasithin.gaschutz hV'2 Q).2 hex
  have hsplit : ∀ t : T, ∃ v ∈ V', ∃ k ∈ K', v * k = t := by
    intro t
    have ht : t ∈ V' ⊔ K' := by
      rw [hK'.2]
      exact mem_top t
    exact (mem_sup_of_forall_commute (fun a ha b _ => (hcentral a ha b).symm)).1 ht
  have key : ∀ (v v' k k' : T), (∀ t : T, t * v = v * t) → (∀ t : T, t * v' = v' * t) →
      v * k * (v' * k') * (v * k)⁻¹ * (v' * k')⁻¹ = k * k' * k⁻¹ * k'⁻¹ := by
    intro v v' k k' hv hv'
    have e1 : v * (k * (v' * k') * k⁻¹) * v⁻¹ = k * (v' * k') * k⁻¹ := by
      rw [← hv (k * (v' * k') * k⁻¹)]
      group
    have e2 : v' * (k * k' * k⁻¹ * k'⁻¹) * v'⁻¹ = k * k' * k⁻¹ * k'⁻¹ := by
      rw [← hv' (k * k' * k⁻¹ * k'⁻¹)]
      group
    calc v * k * (v' * k') * (v * k)⁻¹ * (v' * k')⁻¹
        = (v * (k * (v' * k') * k⁻¹) * v⁻¹) * (v' * k')⁻¹ := by group
      _ = (k * (v' * k') * k⁻¹) * (v' * k')⁻¹ := by rw [e1]
      _ = (k * v') * k' * k⁻¹ * k'⁻¹ * v'⁻¹ := by group
      _ = (v' * k) * k' * k⁻¹ * k'⁻¹ * v'⁻¹ := by rw [hv' k]
      _ = v' * (k * k' * k⁻¹ * k'⁻¹) * v'⁻¹ := by group
      _ = k * k' * k⁻¹ * k'⁻¹ := e2
  have hcomm_le : ⁅T, T⁆ ≤ K'.map T.subtype := by
    rw [commutator_le]
    intro x hx y hy
    show x * y * x⁻¹ * y⁻¹ ∈ K'.map T.subtype
    obtain ⟨v, hv, k, hk, hvk⟩ := hsplit ⟨x, hx⟩
    obtain ⟨v', hv', k', hk', hvk'⟩ := hsplit ⟨y, hy⟩
    refine ⟨k * k' * k⁻¹ * k'⁻¹, ?_, ?_⟩
    · exact mul_mem (mul_mem (mul_mem hk hk') (inv_mem hk)) (inv_mem hk')
    · have e := key v v' k k' (hcentral v hv) (hcentral v' hv')
      rw [hvk, hvk'] at e
      rw [← e]
      rfl
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzc, hzV⟩ := mem_inf.1 hz
  obtain ⟨k, hk, hkz⟩ := hcomm_le hzc
  have hkV : k ∈ V' := by
    rw [hV', mem_subgroupOf]
    change T.subtype k ∈ V
    rw [hkz]
    exact hzV
  have hk1 : k ∈ V' ⊓ K' := mem_inf.2 ⟨hkV, hk⟩
  rw [hK'.1, mem_bot] at hk1
  rw [mem_bot, ← hkz, hk1]
  rfl

private theorem aux_G2_exists_mul_of_mem_sup {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ a ∈ A, ∃ b ∈ B, a * b = x)
    ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, x, hx, by simp⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    have := h a₂ ha₂ b₁ hb₁
    calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [this]
      _ = a₁ * b₁ * (a₂ * b₂) := by group
  · rintro _ _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := h a ha b hb
    calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
      _ = (a * b)⁻¹ := by rw [this]

private theorem aux_G2_mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB x]

theorem pCoreOf_eq_inf_of_normal {N T : Subgroup G} (hNT : N ≤ T)
    (hTN : T ≤ normalizer (N : Set G)) : pCoreOf 2 N = N ⊓ pCoreOf 2 T := by
  refine le_antisymm (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 N) ?_) ?_
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 N).trans hNT)
      (fun g hg => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N (hTN hg))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => aux_G2_mem_normalizer_inf (Subgroup.le_normalizer hg)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 T (hNT hg)))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 T).to_le inf_le_right)

theorem mem_normalizer_pCoreOf {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    g ∈ normalizer (pCoreOf 2 H : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H hg

theorem pCoreOf_map_conj (H : Subgroup G) (g : G) :
    pCoreOf 2 (H.map (MulAut.conj g).toMonoidHom) =
      (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom :=
  CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) H

theorem pCoreOf_sup_of_central {A Z : Subgroup G} (hZ : IsPGroup 2 Z)
    (hZc : Z ≤ centralizer ((A ⊔ Z : Subgroup G) : Set G)) :
    pCoreOf 2 (A ⊔ Z) = pCoreOf 2 A ⊔ Z := by
  have hZA : ∀ z ∈ Z, ∀ g ∈ A ⊔ Z, g * z = z * g := fun z hz g hg =>
    Subgroup.mem_centralizer_iff.mp (hZc hz) g hg
  have hAcomm : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a := fun a ha z hz =>
    hZA z hz a (Subgroup.mem_sup_left ha)
  have hZle : Z ≤ pCoreOf 2 (A ⊔ Z) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
      (fun g hg => ?_) hZ
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun z hz => (hZA z hz g hg).symm)
  have hAle : pCoreOf 2 A ≤ pCoreOf 2 (A ⊔ Z) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans le_sup_left) (fun g hg => ?_)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A)
    obtain ⟨a, ha, z, hz, rfl⟩ := aux_G2_exists_mul_of_mem_sup hAcomm hg
    refine mul_mem (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A ha) ?_
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        hAcomm x (CFSG.LieType.BorelTits.pCoreOf_le 2 A hx) z hz)
  refine le_antisymm ?_ (sup_le hAle hZle)
  intro x hx
  obtain ⟨a, ha, z, hz, rfl⟩ := aux_G2_exists_mul_of_mem_sup hAcomm
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (A ⊔ Z) hx)
  have haO : a ∈ pCoreOf 2 (A ⊔ Z) := by
    simpa using mul_mem hx (inv_mem (hZle hz))
  have hAN : A ⊔ Z ≤ normalizer (A : Set G) := by
    refine sup_le Subgroup.le_normalizer (fun z hz => ?_)
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hAcomm a ha z hz)
  have hA : a ∈ pCoreOf 2 A := by
    rw [pCoreOf_eq_inf_of_normal (le_sup_left : A ≤ A ⊔ Z) hAN]
    exact ⟨ha, haO⟩
  exact Subgroup.mul_mem_sup hA hz

theorem le_commutator_sup_of_isQuotientIso {X N : Subgroup G} {T : Type*} [Group T]
    (h : IsQuotientIso X N T) (hT : Group.IsPerfect T) : X ≤ ⁅X, X⁆ ⊔ N := by
  obtain ⟨φ, hφ, hker⟩ := h
  intro x hx
  have hmap : (_root_.commutator X).map φ = ⊤ := by
    rw [_root_.map_commutator_eq, MonoidHom.range_eq_top_of_surjective φ hφ,
      ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
  have hφx : φ ⟨x, hx⟩ ∈ (_root_.commutator X).map φ := by
    rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hφx
  have hyN : (y : G)⁻¹ * x ∈ N := by
    have h1 : y⁻¹ * ⟨x, hx⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hyc : (y : G) ∈ ⁅X, X⁆ := by
    rw [← Subgroup.map_subtype_commutator X]
    exact Subgroup.mem_map_of_mem X.subtype hy
  have := Subgroup.mul_mem_sup hyc hyN
  simpa using this

theorem le_commutator_sup_of_sectionIso {A B A' B' : Subgroup G} (h : SectionIso A B A' B')
    (hA' : ⁅A', A'⁆ = A') : A ≤ ⁅A, A⁆ ⊔ B := by
  obtain ⟨hB, hB', ⟨e⟩⟩ := h
  haveI : Group.IsPerfect ↥A' := Subgroup.isPerfect_iff.mpr hA'
  haveI := hB'
  haveI : Group.IsPerfect (A' ⧸ B'.subgroupOf A') := inferInstance
  have hP : Group.IsPerfect (A ⧸ B.subgroupOf A) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact le_commutator_sup_of_isQuotientIso
    ⟨QuotientGroup.mk' (B.subgroupOf A), QuotientGroup.mk'_surjective _,
      QuotientGroup.ker_mk' _⟩ hP

theorem card_mul_card_of_sectionIso {A B A' B' : Subgroup G} (h : SectionIso A B A' B')
    (hB : B ≤ A) (hB' : B' ≤ A') :
    Nat.card A * Nat.card B' = Nat.card A' * Nat.card B := by
  obtain ⟨_, _, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B'.subgroupOf A')
  have e1 : Nat.card (B.subgroupOf A) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  have e2 : Nat.card (B'.subgroupOf A') = Nat.card B' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB').toEquiv
  have e3 : Nat.card (A ⧸ B.subgroupOf A) = Nat.card (A' ⧸ B'.subgroupOf A') :=
    Nat.card_congr e.toEquiv
  rw [h1, h2, e1, e2, e3]
  ring

end Generic

section Local

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem odd_card_jZeroG {q : ℕ} (d : TrialityD4Data L q) :
    Odd (Nat.card (jZeroG d : Subgroup G)) := by
  unfold jZeroG
  rw [Subgroup.card_map_of_injective L.subtype_injective]
  exact d.odd_card_J₀

theorem jZeroG_le_cLV {q : ℕ} (d : TrialityD4Data L q) :
    (jZeroG d : Subgroup G) ≤ cLV d := by
  unfold jZeroG cLV
  exact Subgroup.map_mono (d.J₀_le_J₆.trans inf_le_right)

theorem vG_mem_normalizer_jZeroG {q : ℕ} (d : TrialityD4Data L q) :
    vG d ∈ normalizer ((jZeroG d : Subgroup G) : Set G) :=
  Setup.coe_mem_normalizer_map d.v_mem_normalizer_J₀

theorem jZeroG_le_normalizer_yamadaP (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (jZeroG d : Subgroup G) ≤ normalizer ((yamadaP d t : Subgroup G) : Set G) := fun x hx =>
  ncs_le_normalizer_yamadaP h d hlay
    ⟨Setup.J₀_map_le_centralizer h d hx, Setup.J₀_map_le_normalizer_S d hx⟩

theorem jZeroG_le_centralizer_t (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q) :
    (jZeroG d : Subgroup G) ≤ centralizer ({t} : Set G) :=
  Setup.J₀_map_le_centralizer h d

theorem uG_mem_cLV {q : ℕ} (d : TrialityD4Data L q) : uG d ∈ cLV d := by
  refine ⟨d.u, mem_centralizer_iff.2 ?_, rfl⟩
  rintro y ⟨a, rfl⟩
  calc d.x₆ a * d.u = d.u * d.x₆ a * d.u * d.u := by rw [d.u_x₆ a]
    _ = d.u * d.x₆ a := by rw [mul_assoc, d.u_mul_self, mul_one]

open scoped commutatorElement in
private theorem aux_L1_Y_le_commutator_S {q : ℕ} (d : TrialityD4Data L q) :
    d.Y ≤ ⁅d.S, d.S⁆ := by
  refine sup_le ?_ ?_
  · rintro _ ⟨c, rfl⟩
    obtain ⟨b, hb⟩ := d.exists_tr_eq c
    have h1 : ⁅d.x₁ 1, d.x₄ b⁆ = d.x₅ (d.tr b) := by rw [d.comm₁₄, one_mul]
    rw [hb] at h1
    rw [← h1]
    exact Subgroup.commutator_mem_commutator (d.U₁_le_S (d.x₁_mem_U₁ 1))
      (d.U₄_le_S (d.x₄_mem_U₄ b))
  · rintro _ ⟨c, rfl⟩
    have h1 : ⁅d.x₂ c, d.x₅ 1⁆ = d.x₆ c := by rw [d.comm₂₅, mul_one]
    rw [← h1]
    exact Subgroup.commutator_mem_commutator (d.U₂_le_S (d.x₂_mem_U₂ c))
      (d.U₅_le_S (d.x₅_mem_U₅ 1))

theorem Y_map_le_commutator_S {q : ℕ} (d : TrialityD4Data L q) :
    d.Y.map L.subtype ≤ ⁅d.S.map L.subtype, d.S.map L.subtype⁆ := by
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono (aux_L1_Y_le_commutator_S d)

open scoped commutatorElement in
private theorem aux_L1_x₆_eq {q : ℕ} (d : TrialityD4Data L q) (c : d.Γ₀) :
    d.x₆ c = ⁅d.x₂ c, d.x₅ 1⁆ := by
  rw [d.comm₂₅, mul_one]

open scoped commutatorElement in
private theorem aux_L1_x₅_eq {q : ℕ} (d : TrialityD4Data L q) (c : d.Γ₀) :
    d.x₅ c = ⁅d.v * d.x₂ c * d.v⁻¹, d.x₆ 1⁆ := by
  have e₅ : ∀ c : d.Γ₀, d.x₅ c = d.v * d.x₆ c * d.v⁻¹ := fun c => by
    rw [d.v_inv, ← d.v_x₅ c]
    calc d.x₅ c = (d.v * d.v) * d.x₅ c * (d.v * d.v) := by rw [d.v_mul_self]; simp
      _ = d.v * (d.v * d.x₅ c * d.v) * d.v := by group
  have e₆' : d.x₆ 1 = d.v * d.x₅ 1 * d.v⁻¹ := by rw [d.v_inv, d.v_x₅]
  calc d.x₅ c = d.v * ⁅d.x₂ c, d.x₅ 1⁆ * d.v⁻¹ := by rw [e₅ c, aux_L1_x₆_eq d c]
    _ = ⁅d.v * d.x₂ c * d.v⁻¹, d.v * d.x₅ 1 * d.v⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    _ = ⁅d.v * d.x₂ c * d.v⁻¹, d.x₆ 1⁆ := by rw [← e₆']

theorem Y_map_le_commutator_of {q : ℕ} (d : TrialityD4Data L q) {T : Subgroup G}
    (hU₂ : d.U₂.map L.subtype ≤ T) (hv : vG d ∈ T) (hY : d.Y.map L.subtype ≤ T) :
    d.Y.map L.subtype ≤ ⁅T, T⁆ := by
  rw [Subgroup.map_le_iff_le_comap]
  have hx₂ : ∀ c : d.Γ₀, ((d.x₂ c : L) : G) ∈ T := fun c => hU₂ ⟨d.x₂ c, d.x₂_mem_U₂ c, rfl⟩
  have hx₅Y : ∀ c : d.Γ₀, ((d.x₅ c : L) : G) ∈ T :=
    fun c => hY ⟨d.x₅ c, d.x₅_mem_Y c, rfl⟩
  have hx₆Y : ∀ c : d.Γ₀, ((d.x₆ c : L) : G) ∈ T :=
    fun c => hY ⟨d.x₆ c, d.x₆_mem_Y c, rfl⟩
  refine sup_le ?_ ?_
  · rintro _ ⟨c, rfl⟩
    have h1 := congrArg L.subtype (aux_L1_x₅_eq d c)
    rw [map_commutatorElement, map_mul, map_mul, map_inv] at h1
    refine Subgroup.mem_comap.2 ?_
    rw [h1]
    exact Subgroup.commutator_mem_commutator (mul_mem (mul_mem hv (hx₂ c)) (inv_mem hv))
      (hx₆Y 1)
  · rintro _ ⟨c, rfl⟩
    have h1 := congrArg L.subtype (aux_L1_x₆_eq d c)
    rw [map_commutatorElement] at h1
    refine Subgroup.mem_comap.2 ?_
    rw [h1]
    exact Subgroup.commutator_mem_commutator (hx₂ c) (hx₅Y 1)

theorem card_Y_map {q : ℕ} (d : TrialityD4Data L q) : Nat.card (d.Y.map L.subtype) = q ^ 2 := by
  rw [Subgroup.card_map_of_injective L.subtype_injective]
  exact d.card_Y

theorem qThree_le_kThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    qThree d t K ≤ kThree d t K := by
  obtain ⟨-, ⟨-, -, -, -, hcard⟩, ⟨-, -, -, -, hEQ, hNorm, -⟩⟩ := A2_sylow h d hp hK
  intro x hx
  have hxN : x ∈ normalizer ((eOne d t K : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEQ).1 hNorm hx
  have hx2 : x ^ (2 ^ (f * 3)) = 1 := by
    have h1 : (⟨x, hx⟩ : ↥(qThree d t K)) ^ Nat.card ↥(qThree d t K) = 1 := pow_card_eq_one'
    rw [hcard, ← pow_mul] at h1
    simpa using congrArg Subtype.val h1
  exact Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, hxN⟩, f * 3, hx2⟩

theorem isPerfect_sl2_Γ₀ (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f) :
    Group.IsPerfect SL(2, d.Γ₀) := by
  refine CFSG.ClassicalInvolution.sl2_isPerfect ?_
  rw [d.card_Γ₀]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem isPerfect_sl2_Γ (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f) :
    Group.IsPerfect SL(2, d.Γ) := by
  refine CFSG.ClassicalInvolution.sl2_isPerfect ?_
  rw [d.card_Γ]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    _ ≤ (2 ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _

private theorem aux_L2a_conj_mem {q : ℕ} {d : TrialityD4Data L q} {K₁ : Subgroup G}
    (hK₁ : IsN1Factor d t K₁) {k' k : G} (hk' : k' ∈ K₁ᵍ[t]) (hk : k ∈ K₁) :
    k' * k * k'⁻¹ ∈ K₁ := by
  have h1 := Subgroup.commutator_mem_commutator hk' hk
  rw [Subgroup.commutator_comm, commutatorElement_def] at h1
  have h2 : k' * k * k'⁻¹ * k⁻¹ ∈ K₁ := hK₁.D₅_le (hK₁.comm_le h1)
  have e : k' * k * k'⁻¹ = (k' * k * k'⁻¹ * k⁻¹) * k := by group
  rw [e]
  exact mul_mem h2 hk

private theorem aux_L2a_conj_le_normalizer {q : ℕ} {d : TrialityD4Data L q} {K₁ : Subgroup G}
    (hK₁ : IsN1Factor d t K₁) : K₁ᵍ[t] ≤ normalizer (K₁ : Set G) := by
  intro k' hk'
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => aux_L2a_conj_mem hK₁ hk' hk, fun hk => ?_⟩
  have h1 := aux_L2a_conj_mem hK₁ (inv_mem hk') hk
  have e : k'⁻¹ * (k' * k * k'⁻¹) * k'⁻¹⁻¹ = k := by group
  rw [e] at h1
  exact h1

theorem nOne_le_normalizer {q : ℕ} {d : TrialityD4Data L q} {K₁ : Subgroup G}
    (hK₁ : IsN1Factor d t K₁) :
    nOne d t ≤ normalizer (K₁ : Set G) ∧ nOne d t ≤ normalizer ((⁅K₁, K₁⁆ : Subgroup G) : Set G) ∧
      nOne d t ≤ normalizer ((⁅⁅K₁, K₁⁆, ⁅K₁, K₁⁆⁆ : Subgroup G) : Set G) := by
  have h1 : nOne d t ≤ normalizer (K₁ : Set G) := by
    rw [hK₁.sup_eq]
    exact sup_le le_normalizer (aux_L2a_conj_le_normalizer hK₁)
  have h2 : nOne d t ≤ normalizer ((⁅K₁, K₁⁆ : Subgroup G) : Set G) :=
    h1.trans (Setup.normalizer_le_normalizer_commutator_C8 K₁)
  exact ⟨h1, h2, h2.trans (Setup.normalizer_le_normalizer_commutator_C8 _)⟩

private theorem aux_L2a_cLV_le_normalizer_D5 (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    cLV d ≤ normalizer ((yamadaD₅ d t : Subgroup G) : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  exact (h.coe_mem_normalizer_yamadaD₅_C9 d (h.yamada_5_6_1 d hlay)
    (Subgroup.centralizer_le_normalizer _ hl)).2.2

theorem cLV_le_nOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    cLV d ≤ nOne d t := by
  have hN := aux_L2a_cLV_le_normalizer_D5 h d hp.layer
  obtain ⟨-, -, ⟨⟨e⟩, -⟩, -⟩ := D1_centralizer_tbar h d hp
  have hperf : Group.IsPerfect ↥(kBar d t) := by
    have := isPerfect_sl2_Γ d hp.two_le
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hk : kBar d t ≤ nOneBar d t :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf _ _ hperf
      subset_normalClosure
  intro x hx
  exact NormalizerQuotient.mem_lift_of_proj_mem (x := ⟨x, hN hx⟩)
    (hk (NormalizerQuotient.proj_mem_bar hx))

theorem card_yamadaV₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 := by
  exact (h.yamada_5_6_2 d hp.layer).2.1

private theorem aux_L2b_card_V_map (d : TrialityD4Data L (2 ^ f)) :
    Nat.card (d.V.map L.subtype) = 2 ^ f := by
  rw [Subgroup.card_map_of_injective L.subtype_injective, d.card_V]

private theorem aux_L2b_V_map_le_cLV (d : TrialityD4Data L (2 ^ f)) :
    d.V.map L.subtype ≤ cLV d :=
  Subgroup.map_mono (d.V_le_S.trans d.S_le_centralizer_V)

theorem card_commutator_K₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    Nat.card (⁅K₁, K₁⁆ : Subgroup G) = 2 ^ f * Nat.card (cLV d) := by
  have hsec := (E2_decomposition h d hp hK₁).1.2.2.2
  have hV₁ := (E3_commutators h d hp hK₁).1.1
  have hc := card_mul_card_of_sectionIso hsec hV₁ (aux_L2b_V_map_le_cLV d)
  rw [aux_L2b_card_V_map d, card_yamadaV₁ h d hp] at hc
  have hpos : 0 < 2 ^ f := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card (⁅K₁, K₁⁆ : Subgroup G) * 2 ^ f = Nat.card (cLV d) * (2 ^ f) ^ 2 := hc
    _ = 2 ^ f * Nat.card (cLV d) * 2 ^ f := by ring

private theorem aux_L2b_isSylowOf_S_cLV (d : TrialityD4Data L (2 ^ f)) :
    IsSylowOf 2 (d.S.map L.subtype) (cLV d) := by
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  have hSyl : IsSylowOf 2 d.S (⊤ : Subgroup L) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hP ▸ P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact d.not_two_dvd_index_S
  exact (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L).2
    (hSyl.of_le d.S_le_centralizer_V le_top)

private theorem aux_L2b_card_cLV (d : TrialityD4Data L (2 ^ f)) :
    ∃ m : ℕ, ¬ 2 ∣ m ∧ Nat.card (cLV d) = m * (2 ^ f) ^ 12 := by
  have hS := aux_L2b_isSylowOf_S_cLV d
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS
  obtain ⟨hle, -, hodd⟩ := hS
  refine ⟨(d.S.map L.subtype).relIndex (cLV d), hodd, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (H := d.S.map L.subtype) (K := cLV d)
  rw [inf_of_le_left hle, Subgroup.card_map_of_injective L.subtype_injective, d.card_S] at h1
  exact h1.symm

private theorem aux_L2b_card_qOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    Nat.card (qOne d t K₁) = (2 ^ f) ^ 13 := by
  obtain ⟨hPsup, hinf, hcomm, -⟩ := (F0_sylow h d hp hL.comp hL.factor).1
  have hP24 : Nat.card (yamadaP d t) = (2 ^ f) ^ 24 :=
    (T4_series_free h d hp).2.2.2.2.2.2.2.2.2.1
  have hV₁ : Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 := card_yamadaV₁ h d hp
  have hV₁Q : yamadaV₁ d t ≤ qOne d t K₁ := hinf ▸ inf_le_left
  have hnorm : (qOne d t K₁)ᵍ[t] ≤ normalizer ((qOne d t K₁ : Subgroup G) : Set G) := by
    intro y hy
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hc := Subgroup.commutator_mem_commutator hy hx
    rw [Subgroup.commutator_comm, commutatorElement_def] at hc
    have h2 : y * x * y⁻¹ * x⁻¹ ∈ qOne d t K₁ := hV₁Q (hcomm hc)
    have e : y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
    rw [SetLike.mem_coe, e]
    exact mul_mem h2 hx
  have hcard := card_sup_mul_card_inf_eq hnorm
  have hQt : Nat.card ((qOne d t K₁)ᵍ[t] : Subgroup G) = Nat.card (qOne d t K₁) :=
    Subgroup.card_map_of_injective (MulEquiv.injective _)
  rw [← hPsup, hinf, hP24, hV₁, hQt] at hcard
  have h13 : (2 ^ f) ^ 13 * (2 ^ f) ^ 13 = Nat.card (qOne d t K₁) * Nat.card (qOne d t K₁) := by
    rw [← hcard]
    ring
  exact (Nat.mul_self_inj.1 h13).symm

theorem isSylowOf_qOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    IsSylowOf 2 (qOne d t K₁) (⁅K₁, K₁⁆ : Subgroup G) := by
  have hQ := aux_L2b_card_qOne h d hp hL
  obtain ⟨m, hm, hcL⟩ := aux_L2b_card_cLV d
  have hK := card_commutator_K₁ h d hp hL.factor
  have hle : qOne d t K₁ ≤ ⁅K₁, K₁⁆ := inf_le_right
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hle, ?_, ?_⟩
  · exact (h.yamada_5_32_of_layerHyp d hp.layer).2.1.to_le inf_le_left
  · have h1 := Subgroup.relIndex_mul_card (H := qOne d t K₁) (K := ⁅K₁, K₁⁆)
    rw [inf_of_le_left hle, hQ, hK, hcL] at h1
    have hpos : 0 < (2 ^ f) ^ 13 := by positivity
    have hrel : (qOne d t K₁).relIndex ⁅K₁, K₁⁆ = m := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [h1]
      ring
    rwa [hrel]

end Local

section Diag

variable {G : Type} [Group G] [Finite G]

@[expose] def dg (A : Subgroup G) (t : G) (hc : ⁅A, Aᵍ[t]⁆ = ⊥) (B : Subgroup G) : Subgroup G :=
  (B.subgroupOf A).map (diagonalHom A t hc)

theorem mem_dg_iff {A : Subgroup G} {t : G} {hc : ⁅A, Aᵍ[t]⁆ = ⊥} {B : Subgroup G} {y : G} :
    y ∈ dg A t hc B ↔ ∃ b : G, b ∈ A ∧ b ∈ B ∧ b * (t⁻¹ * b * t) = y := by
  constructor
  · rintro ⟨⟨b, hbA⟩, hbB, rfl⟩
    exact ⟨b, hbA, hbB, rfl⟩
  · rintro ⟨b, hbA, hbB, rfl⟩
    exact ⟨⟨b, hbA⟩, hbB, rfl⟩

theorem delta_mem_dg {A : Subgroup G} {t : G} {hc : ⁅A, Aᵍ[t]⁆ = ⊥} {B : Subgroup G} {b : G}
    (hbA : b ∈ A) (hbB : b ∈ B) : b * (t⁻¹ * b * t) ∈ dg A t hc B :=
  mem_dg_iff.2 ⟨b, hbA, hbB, rfl⟩

theorem dg_mono {A : Subgroup G} {t : G} {hc : ⁅A, Aᵍ[t]⁆ = ⊥} {B B' : Subgroup G}
    (h : B ≤ B') : dg A t hc B ≤ dg A t hc B' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem diagonalHom_injective_of_inf_eq_bot {A : Subgroup G} {t : G} (hc : ⁅A, Aᵍ[t]⁆ = ⊥)
    (hi : A ⊓ Aᵍ[t] = ⊥) : Function.Injective (diagonalHom A t hc) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 := map_ker_diagonalHom_le hc
  have h2 : (a : G) ∈ (diagonalHom A t hc).ker.map A.subtype := ⟨a, ha, rfl⟩
  have h3 := h1 h2
  rw [hi] at h3
  exact Subtype.ext (mem_bot.1 h3)

theorem eq_of_delta_eq {A : Subgroup G} {t : G} (hc : ⁅A, Aᵍ[t]⁆ = ⊥) (hi : A ⊓ Aᵍ[t] = ⊥)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) (h : a * (t⁻¹ * a * t) = b * (t⁻¹ * b * t)) : a = b := by
  have := diagonalHom_injective_of_inf_eq_bot hc hi (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h
  exact congrArg Subtype.val this

theorem le_of_dg_le {A : Subgroup G} {t : G} {hc : ⁅A, Aᵍ[t]⁆ = ⊥} (hi : A ⊓ Aᵍ[t] = ⊥)
    {B B' : Subgroup G} (hB : B ≤ A) (h : dg A t hc B ≤ dg A t hc B') : B ≤ B' := by
  intro b hb
  have h1 : b * (t⁻¹ * b * t) ∈ dg A t hc B := delta_mem_dg (hB hb) hb
  obtain ⟨b', hb'A, hb'B', hb'⟩ := mem_dg_iff.1 (h h1)
  have := eq_of_delta_eq hc hi hb'A (hB hb) hb'
  rw [this] at hb'B'
  exact hb'B'

theorem card_dg {A : Subgroup G} {t : G} {hc : ⁅A, Aᵍ[t]⁆ = ⊥} (hi : A ⊓ Aᵍ[t] = ⊥)
    {B : Subgroup G} (hB : B ≤ A) : Nat.card (dg A t hc B) = Nat.card B := by
  unfold dg
  rw [Subgroup.card_map_of_injective (diagonalHom_injective_of_inf_eq_bot hc hi)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv

theorem subgroupOf_commutator {A B B' : Subgroup G} (hB : B ≤ A) (hB' : B' ≤ A) :
    (⁅B, B'⁆ : Subgroup G).subgroupOf A = ⁅B.subgroupOf A, B'.subgroupOf A⁆ := by
  have hle : (⁅B, B'⁆ : Subgroup G) ≤ A := by
    refine Subgroup.commutator_le.2 fun g hg h hh => ?_
    rw [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem (hB hg) (hB' hh)) (A.inv_mem (hB hg)))
      (A.inv_mem (hB' hh))
  apply Subgroup.map_injective A.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hle,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hB']

theorem dg_commutator {A : Subgroup G} {t : G} {hc : ⁅A, Aᵍ[t]⁆ = ⊥} {B B' : Subgroup G}
    (hB : B ≤ A) (hB' : B' ≤ A) :
    dg A t hc ⁅B, B'⁆ = ⁅dg A t hc B, dg A t hc B'⁆ := by
  unfold dg
  rw [subgroupOf_commutator hB hB', Subgroup.map_commutator]

theorem dg_eq_inf_centralizer {A : Subgroup G} {t : G} (ht : t * t = 1)
    (hc : ⁅A, Aᵍ[t]⁆ = ⊥) (hi : A ⊓ Aᵍ[t] = ⊥) {B : Subgroup G} (hBA : B ≤ A) :
    dg A t hc B = (B ⊔ Bᵍ[t]) ⊓ centralizer ({t} : Set G) := by
  have hBc : ⁅B, Bᵍ[t]⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hc]
    exact Subgroup.commutator_mono hBA (Subgroup.map_mono hBA)
  have hcomm : ∀ a ∈ B, ∀ b ∈ Bᵍ[t], a * b = b * a := commutator_eq_bot_iff.1 hBc
  have hBi : B ⊓ Bᵍ[t] = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hi]
    exact inf_le_inf hBA (Subgroup.map_mono hBA)
  ext y
  rw [mem_dg_iff, mem_inf]
  constructor
  · rintro ⟨b, hbA, hbB, rfl⟩
    refine ⟨?_, ?_⟩
    · exact mul_mem (mem_sup_left hbB) (mem_sup_right (conj_mem_map_conj_inv t hbB))
    · have := range_diagonalHom_le hc ht ⟨⟨b, hbA⟩, rfl⟩
      exact this
  · rintro ⟨hy, hyt⟩
    obtain ⟨b, hb, c, hc', rfl⟩ := (mem_sup_of_forall_commute hcomm).1 hy
    obtain ⟨b', hb'0, rfl⟩ := hc'
    have hb' : b' ∈ B := hb'0
    have hti : t⁻¹ = t := inv_eq_of_involution ht
    have hcb : (MulEquiv.toMonoidHom (MulAut.conj t⁻¹)) b' = t * b' * t := by
      simp [MulAut.conj_apply, hti]
    rw [hcb] at hyt ⊢
    rw [mem_centralizer_singleton_iff] at hyt
    have hbbA : b ∈ A := hBA hb
    have h1 : b' * (t * b * t) = (t * b * t) * b' :=
      hcomm b' hb' _ (conj_mem_conjT ht hb)
    have hkey : b * (t * b') = b' * (t * b) := by
      have e1 : b * (t * b' * t) * t = t * (b * (t * b' * t)) := hyt
      have e3 : t * (b * (t * b' * t)) = (t * b * t) * b' * t := by
        simp only [mul_assoc]
      have e4 : b * (t * b') = (t * b * t) * b' * t := by
        have := e1.trans e3
        simpa only [mul_assoc, ht, mul_one] using this
      have e5 : (t * b * t) * b' * t = b' * (t * b) := by
        rw [← h1]
        simp only [mul_assoc, ht, mul_one]
      exact e4.trans e5
    have h3 : t * (b⁻¹ * b') * t = b' * b⁻¹ := by
      have h6 : t * b' = b⁻¹ * (b' * (t * b)) := by
        rw [← hkey]; group
      have h7 : b' = t * (b⁻¹ * (b' * (t * b))) := by
        rw [← h6]
        simp only [← mul_assoc, ht, one_mul]
      calc t * (b⁻¹ * b') * t = (t * (b⁻¹ * (b' * (t * b)))) * b⁻¹ := by group
        _ = b' * b⁻¹ := by rw [← h7]
    have h4 : b⁻¹ * b' ∈ B ⊓ Bᵍ[t] := by
      refine mem_inf.2 ⟨B.mul_mem (B.inv_mem hb) hb', (mem_conjT_iff ht).2 ?_⟩
      rw [h3]
      exact B.mul_mem hb' (B.inv_mem hb)
    rw [hBi, mem_bot] at h4
    have h5 : b' = b := by
      have := mul_eq_one_iff_eq_inv.1 h4
      exact (inv_inj.1 this).symm
    refine ⟨b, hbbA, hb, ?_⟩
    rw [h5, hti]

theorem diagonalHom_range_eq_dg {A : Subgroup G} {t : G} (hc : ⁅A, Aᵍ[t]⁆ = ⊥) :
    (diagonalHom A t hc).range = dg A t hc A := by
  unfold dg
  rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]

end Diag

section Phase1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem dg_K3_E1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K)
    (hc : ⁅kThree d t K, (kThree d t K)ᵍ[t]⁆ = ⊥) :
    dg (kThree d t K) t hc (eOne d t K) = d.Y.map L.subtype := by
  have ht2 : t * t = 1 := h.t_mul_t
  obtain ⟨-, -, ⟨hE1, hE2, hE3, hE4, hE5, hE6, hE7⟩⟩ := A2_sylow h d hp hK
  obtain ⟨⟨hK3E, hK3O, hK3Q, hK3Z, hN3, hK3i, hK3c, hN3Q⟩, -, -⟩ := A3_structure h d hp hK
  have hT4Y := (T4_series_free h d hp).2.1
  have hle : dg (kThree d t K) t hc (eOne d t K) ≤ d.Y.map L.subtype := by
    intro y hy
    obtain ⟨e, heK3, heE, rfl⟩ := mem_dg_iff.1 hy
    rw [← hT4Y]
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [hE1]
      exact mul_mem (mem_sup_left heE) (mem_sup_right (conj_mem_map_conj_inv t heE))
    · exact range_diagonalHom_le hc ht2 ⟨⟨e, heK3⟩, rfl⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_dg hK3i hK3E, hE4, card_Y_map d]

theorem E1_le_commutator_K3 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    eOne d t K ≤ ⁅kThree d t K, kThree d t K⁆ ∧ kThree d t K ≤ ⁅kThree d t K, kThree d t K⁆ := by
  have ht2 : t * t = 1 := h.t_mul_t
  obtain ⟨-, -, ⟨hE1, hE2, hE3, hE4, hE5, hE6, hE7⟩⟩ := A2_sylow h d hp hK
  obtain ⟨⟨hK3E, hK3O, hK3Q, hK3Z, hN3, hK3i, hK3c, hN3Q⟩, ⟨hN3X, hLong, hN3M, hv1⟩, -⟩ :=
    A3_structure h d hp hK
  have hΔE := dg_K3_E1 h d hp hK hK3c
  have hT : dg (kThree d t K) t hK3c (kThree d t K) =
      nThree d t ⊓ centralizer ({t} : Set G) := by
    rw [dg_eq_inf_centralizer ht2 hK3c hK3i le_rfl, ← hN3]
  have hU₂ : d.U₂.map L.subtype ≤ dg (kThree d t K) t hK3c (kThree d t K) := by
    rw [hT]
    refine le_inf ?_ ?_
    · exact (Subgroup.map_mono d.U₂_le_leviLong).trans hLong
    · exact (Subgroup.map_subtype_le _).trans (h.L_le_centralizer)
  have hv : vG d ∈ dg (kThree d t K) t hK3c (kThree d t K) := by
    rw [hT]
    refine mem_inf.2 ⟨hLong ⟨d.v, d.v_mem_leviLong, rfl⟩, ?_⟩
    exact h.L_le_centralizer d.v.2
  have hY : d.Y.map L.subtype ≤ dg (kThree d t K) t hK3c (kThree d t K) := by
    rw [← hΔE]
    exact dg_mono hK3E
  have hYc := Y_map_le_commutator_of d hU₂ hv hY
  rw [← dg_commutator le_rfl le_rfl, ← hΔE] at hYc
  have hE1c : eOne d t K ≤ ⁅kThree d t K, kThree d t K⁆ :=
    le_of_dg_le hK3i hK3E hYc
  refine ⟨hE1c, ?_⟩
  have := le_commutator_sup_of_isQuotientIso hK3Q (isPerfect_sl2_Γ₀ d hp.two_le)
  rwa [sup_eq_left.2 hE1c] at this

end Phase1

section Phase2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  refine Subgroup.commutator_le.2 fun g hg k hk => ?_
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hg hk) (H.inv_mem hg)) (H.inv_mem hk)

theorem commutator_self_eq_bot_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    ⁅E, E⁆ = ⊥ := by
  rw [commutator_eq_bot_iff]
  intro a ha b hb
  have := hE.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)

theorem commutator_conjT_self_eq_bot {t : G} (ht : t * t = 1) {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : ⁅Eᵍ[t], Eᵍ[t]⁆ = ⊥ := by
  rw [← conjT_commutator, commutator_self_eq_bot_of_isElemAbelian hE, conjT_bot]

theorem E1t_le_centralizer_K5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    (eOne d t K)ᵍ[t] ≤ centralizer (kFive d t K : Set G) := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  obtain ⟨-, -, ⟨hE1, hE2, hE3, hE4, hE5, hE6, hE7⟩⟩ := A2_sylow h d hp hK
  obtain ⟨⟨hK3E, hK3O, hK3Q, hK3Z, hN3, hK3i, hK3c, hN3Q⟩, -, -⟩ := A3_structure h d hp hK
  obtain ⟨-, ⟨hK5a, hK5b, hK5c⟩, -⟩ := G1_decomposition_mod_Y2 h d hp hL
  obtain ⟨⟨hX1, hX2, hX3, hX4, hX5, hX6⟩, -⟩ := G2_structure_Q1 h d hp hL
  have hE1t_c : ⁅(eOne d t K)ᵍ[t], (eOne d t K)ᵍ[t]⁆ = ⊥ := commutator_conjT_self_eq_bot ht2 hE3
  have key : kFive d t K ≤ centralizer (((eOne d t K)ᵍ[t] : Subgroup G) : Set G) := by
    rw [hK5a]
    refine sup_le ?_ ?_
    ·
      refine le_trans ?_ (Subgroup.centralizer_le (Subgroup.map_mono hK3E))
      exact commutator_eq_bot_iff_le_centralizer.1 hK3c
    · rw [hX3]
      refine sup_le ?_ ?_
      · exact commutator_eq_bot_iff_le_centralizer.1 hX5
      · exact commutator_eq_bot_iff_le_centralizer.1 hE1t_c
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact (mem_centralizer_iff.1 (key hy) x hx).symm

theorem K5_split (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    eOne d t K ≤ ⁅kFive d t K, kFive d t K⁆ ∧ kThree d t K ≤ ⁅kFive d t K, kFive d t K⁆ ∧
      kFive d t K = ⁅kFive d t K, kFive d t K⁆ ⊔ (eOne d t K)ᵍ[t] ∧
      ⁅kFive d t K, kFive d t K⁆ ⊓ (eOne d t K)ᵍ[t] = ⊥ := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  obtain ⟨-, -, ⟨hE1, hE2, hE3, hE4, hE5, hE6, hE7⟩⟩ := A2_sylow h d hp hK
  obtain ⟨⟨hK3E, hK3O, hK3Q, hK3Z, hN3, hK3i, hK3c, hN3Q⟩, -, ⟨-, -, -, hPsyl, -⟩⟩ :=
    A3_structure h d hp hK
  obtain ⟨⟨hG1a, hG1b, hG1c, hG1d, hG1e, hG1f, hG1g⟩, ⟨hK5a, hK5b, hK5c⟩, ⟨hP5a, hP5b⟩⟩ :=
    G1_decomposition_mod_Y2 h d hp hL
  obtain ⟨⟨hX1, hX2, hX3, hX4, hX5, hX6⟩, ⟨hQ1, hQ2, hQ3, hQ4, hQ5, hQ6⟩⟩ :=
    G2_structure_Q1 h d hp hL
  obtain ⟨hE1K3, hK3K3⟩ := E1_le_commutator_K3 h d hp hK
  have hcen := E1t_le_centralizer_K5 h d hp hL
  have hK3K5 : kThree d t K ≤ kFive d t K := by rw [hK5a]; exact le_sup_left
  have hOK5 : pCoreOf 2 (kFive d t K) ≤ kFive d t K := LieType.BorelTits.pCoreOf_le 2 _
  have hE1tO : (eOne d t K)ᵍ[t] ≤ pCoreOf 2 (kFive d t K) := by rw [hX3]; exact le_sup_right
  have hE1tK5 : (eOne d t K)ᵍ[t] ≤ kFive d t K := hE1tO.trans hOK5
  have hE1K5' : eOne d t K ≤ ⁅kFive d t K, kFive d t K⁆ :=
    hE1K3.trans (Subgroup.commutator_mono hK3K5 hK3K5)
  have hK3K5' : kThree d t K ≤ ⁅kFive d t K, kFive d t K⁆ :=
    hK3K3.trans (Subgroup.commutator_mono hK3K5 hK3K5)
  have hlvM : ⁅lvM d, lvM d⁆ = lvM d := (I1_facts d hp.two_le).2.2.2.2.2.2
  have hperf := le_commutator_sup_of_sectionIso hG1d hlvM
  have hK5Y : kFive d t K ≤ ⁅kFive d t K, kFive d t K⁆ ⊔ (eOne d t K)ᵍ[t] := by
    refine hperf.trans (sup_le le_sup_left ?_)
    rw [hE1]
    exact sup_le (hE1K5'.trans le_sup_left) le_sup_right
  have hK5eq : kFive d t K = ⁅kFive d t K, kFive d t K⁆ ⊔ (eOne d t K)ᵍ[t] :=
    le_antisymm hK5Y (sup_le (commutator_self_le _) hE1tK5)
  refine ⟨hE1K5', hK3K5', hK5eq, ?_⟩
  have hE1t2 : IsPGroup 2 ((eOne d t K)ᵍ[t] : Subgroup G) := by
    refine IsPGroup.of_card (n := 2 * f) ?_
    rw [card_conjT, hE4, ← pow_mul, mul_comm]
  have hN2K5 : kFive d t K ≤ nTwo d t := by rw [hG1a]; exact le_sup_left
  have hSyl : IsSylowOf 2 (yamadaP d t ⊓ kFive d t K) (kFive d t K) :=
    hPsyl.inf_of_le_normalizer hN2K5 hG1g
  refine commutator_inf_eq_bot_of_sylow_complement (P₀ := pZero d t K K₁) hE1tK5 hcen hE1t2
    hSyl ?_ ?_
  · rw [hP5a, hX3]
    unfold pZero
    ac_rfl
  · rw [inf_comm]; exact hQ2

theorem kThree_le (d : TrialityD4Data L (2 ^ f)) (t : G) (K : Subgroup G) :
    kThree d t K ≤ K := by
  unfold kThree oTwoPrimeRes
  rw [Subgroup.closure_le]
  rintro x ⟨hx, -⟩
  exact (mem_inf.1 hx).1

theorem jZero_le_centralizer_K (d : TrialityD4Data L (2 ^ f)) {K : Subgroup G}
    (hK : IsLayerComponent d t K) :
    (jZeroG d : Subgroup G) ≤ centralizer (K : Set G) :=
  le_centralizer_iff.1 hK.le

theorem jZero_le_normalizer_kFive (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (jZeroG d : Subgroup G) ≤ normalizer (kFive d t K : Set G) := by
  have hlay := hp.layer
  have hJP := jZeroG_le_normalizer_yamadaP h d hlay
  have hM6 : (jZeroG d : Subgroup G) ≤ normalizer (yamadaM₆ d t : Set G) := fun x hx =>
    (B1_decomposition h d hp hK).2.2.2 (hJP hx)
  have hK3 : (jZeroG d : Subgroup G) ≤ normalizer (kThree d t K : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (kThree_le d t K) (jZero_le_centralizer_K d hK hx))
  have hY2 : (jZeroG d : Subgroup G) ≤ normalizer (yamadaY₂ d t : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.1 (T5_J₀ h d hp).1 hx)
  have hK2 : (jZeroG d : Subgroup G) ≤ normalizer (kTwo d t K : Set G) := fun x hx =>
    Common.mem_normalizer_sup (hK3 hx) (hM6 hx)
  have hK4 : (jZeroG d : Subgroup G) ≤ normalizer (kFour d t K : Set G) := fun x hx =>
    Common.mem_normalizer_sup (Setup.normalizer_le_normalizer_commutator_C8 _ (hK2 hx))
      (hK3 hx)
  intro x hx
  exact Common.mem_normalizer_sup (Common.mem_normalizer_sup
    (Setup.normalizer_le_normalizer_commutator_C8 _ (hK4 hx)) (hK3 hx)) (hY2 hx)

theorem jZero_le_normalizer_xQ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    (jZeroG d : Subgroup G) ≤ normalizer (xQ d t K₁ : Set G) := by
  have hJP := jZeroG_le_normalizer_yamadaP h d hp.layer
  have hJK₁ : (jZeroG d : Subgroup G) ≤ normalizer ((⁅K₁, K₁⁆ : Subgroup G) : Set G) :=
    ((jZeroG_le_cLV d).trans (cLV_le_nOne h d hp)).trans (nOne_le_normalizer hK₁).2.1
  have hQ : (jZeroG d : Subgroup G) ≤ normalizer (qOne d t K₁ : Set G) := fun x hx =>
    Common.mem_normalizer_inf (hJP hx) (hJK₁ hx)
  intro x hx
  refine Common.mem_normalizer_inf (hQ hx) (mem_normalizer_map_conj_of ?_)
  have hv := vG_mem_normalizer_jZeroG (G := G) d
  have : vG d * x * (vG d)⁻¹ ∈ (jZeroG d : Subgroup G) := (mem_normalizer_iff.1 hv x).1 hx
  exact hQ this

theorem pCoreOf_commutator_K5_eq_xQ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    pCoreOf 2 ⁅kFive d t K, kFive d t K⁆ = xQ d t K₁ := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  obtain ⟨hE1K5', hK3K5', hK5eq, hK5inf⟩ := K5_split h d hp hL
  obtain ⟨-, -, ⟨hE1, hE2, hE3, hE4, hE5, hE6, hE7⟩⟩ := A2_sylow h d hp hK
  obtain ⟨-, -, ⟨-, -, -, -, hM6Y⟩⟩ := A3_structure h d hp hK
  obtain ⟨-, ⟨hK5a, hK5b, hK5c⟩, -⟩ := G1_decomposition_mod_Y2 h d hp hL
  obtain ⟨⟨hX1, hX2, hX3, hX4, hX5, hX6⟩, -⟩ := G2_structure_Q1 h d hp hL
  have hcen := E1t_le_centralizer_K5 h d hp hL
  have hT5 := T5_J₀ h d hp
  set O := pCoreOf 2 (kFive d t K) with hO
  have hOK5 : O ≤ kFive d t K := LieType.BorelTits.pCoreOf_le 2 _
  have hE1tO : (eOne d t K)ᵍ[t] ≤ O := by rw [hX3]; exact le_sup_right
  have hE1XQ : eOne d t K ≤ xQ d t K₁ := by rw [← hX2]; exact inf_le_left
  have hXQO : xQ d t K₁ ≤ O := by rw [hX3]; exact le_sup_left
  have hE1O : eOne d t K ≤ O := hE1XQ.trans hXQO
  have hK5N : kFive d t K ≤ normalizer ((⁅kFive d t K, kFive d t K⁆ : Subgroup G) : Set G) :=
    fun x hx => Setup.normalizer_le_normalizer_commutator_C8 _ (le_normalizer hx)
  have hO' : pCoreOf 2 ⁅kFive d t K, kFive d t K⁆ = ⁅kFive d t K, kFive d t K⁆ ⊓ O :=
    pCoreOf_eq_inf_of_normal (commutator_self_le _) hK5N
  have hcomm5 : ∀ a ∈ (⁅kFive d t K, kFive d t K⁆ : Subgroup G), ∀ b ∈ (eOne d t K)ᵍ[t],
      a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (hcen hb) a (commutator_self_le _ ha)
  have hOsup : pCoreOf 2 ⁅kFive d t K, kFive d t K⁆ ⊔ (eOne d t K)ᵍ[t] = O := by
    rw [hO']
    refine le_antisymm (sup_le inf_le_right hE1tO) fun x hx => ?_
    have hx5 : x ∈ ⁅kFive d t K, kFive d t K⁆ ⊔ (eOne d t K)ᵍ[t] := hK5eq ▸ hOK5 hx
    obtain ⟨a, ha, e, he, rfl⟩ := (mem_sup_of_forall_commute hcomm5).1 hx5
    have haO : a ∈ O := by
      have := mul_mem hx (inv_mem (hE1tO he))
      simpa using this
    exact mul_mem (mem_sup_left (mem_inf.2 ⟨ha, haO⟩)) (mem_sup_right he)
  have hJodd := odd_card_jZeroG (G := G) d
  have hJE : (jZeroG d : Subgroup G) ≤ centralizer (((eOne d t K)ᵍ[t] : Subgroup G) : Set G) := by
    refine le_centralizer_iff.1 ?_
    have hE1tY : (eOne d t K)ᵍ[t] ≤ yamadaY₂ d t := by rw [hE1]; exact le_sup_right
    exact hE1tY.trans hT5.1
  have hOM6 : O ≤ yamadaM₆ d t := by rw [hK5b]; exact le_sup_left
  have hfix : O ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) ≤
      eOne d t K ⊔ (eOne d t K)ᵍ[t] := by
    intro x hx
    rw [← hE1, ← hM6Y]
    exact mem_inf.2 ⟨hOM6 hx.1, hx.2⟩
  have hO2 : IsPGroup 2 O := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hE1tc : (eOne d t K)ᵍ[t] ≤ centralizer (O : Set G) := fun x hx =>
    Subgroup.centralizer_le hOK5 (hcen hx)
  have hXQeq : xQ d t K₁ = eOne d t K ⊔ ⁅O, (jZeroG d : Subgroup G)⁆ :=
    eq_sup_commutator_of_complement hXQO hO2 hJodd (jZero_le_normalizer_xQ h d hp hL.factor)
      hE1XQ hE1tO hE1tc hJE hX4 hX3.symm hfix
  have hJO' : (jZeroG d : Subgroup G) ≤
      normalizer ((pCoreOf 2 ⁅kFive d t K, kFive d t K⁆ : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_pCoreOf (Setup.normalizer_le_normalizer_commutator_C8 _
      (jZero_le_normalizer_kFive h d hp hK hx))
  have hO'O : pCoreOf 2 ⁅kFive d t K, kFive d t K⁆ ≤ O := by rw [hO']; exact inf_le_right
  have hE1O' : eOne d t K ≤ pCoreOf 2 ⁅kFive d t K, kFive d t K⁆ := by
    rw [hO']; exact le_inf hE1K5' hE1O
  have hO'inf : pCoreOf 2 ⁅kFive d t K, kFive d t K⁆ ⊓ (eOne d t K)ᵍ[t] = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hK5inf, hO']
    exact inf_le_inf (inf_le_left) le_rfl
  have hO'eq : pCoreOf 2 ⁅kFive d t K, kFive d t K⁆ = eOne d t K ⊔ ⁅O, (jZeroG d : Subgroup G)⁆ :=
    eq_sup_commutator_of_complement hO'O hO2 hJodd hJO' hE1O' hE1tO hE1tc hJE hO'inf hOsup hfix
  rw [hO'eq, hXQeq]

theorem aTwo_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    aTwo d t K = ⁅kFive d t K, kFive d t K⁆ ∧ aTwo d t K = kThree d t K ⊔ xQ d t K₁ := by
  have hK := hL.comp
  obtain ⟨hE1K5', hK3K5', hK5eq, hK5inf⟩ := K5_split h d hp hL
  obtain ⟨-, ⟨hK5a, hK5b, hK5c⟩, -⟩ := G1_decomposition_mod_Y2 h d hp hL
  obtain ⟨⟨hX1, hX2, hX3, hX4, hX5, hX6⟩, -⟩ := G2_structure_Q1 h d hp hL
  have hcen := E1t_le_centralizer_K5 h d hp hL
  have hA : aTwo d t K = kThree d t K ⊔ xQ d t K₁ := by
    unfold aTwo
    rw [pCoreOf_commutator_K5_eq_xQ h d hp hL]
  refine ⟨?_, hA⟩
  have hOK5 : pCoreOf 2 (kFive d t K) ≤ kFive d t K := LieType.BorelTits.pCoreOf_le 2 _
  have hXQK5 : xQ d t K₁ ≤ kFive d t K := by
    refine le_trans ?_ hOK5
    rw [hX3]; exact le_sup_left
  have hK3K5 : kThree d t K ≤ kFive d t K := by rw [hK5a]; exact le_sup_left
  have hXQK5' : xQ d t K₁ ≤ ⁅kFive d t K, kFive d t K⁆ := by
    rw [← pCoreOf_commutator_K5_eq_xQ h d hp hL]
    exact LieType.BorelTits.pCoreOf_le 2 _
  rw [hA]
  refine le_antisymm (sup_le hK3K5' hXQK5') ?_
  rw [Subgroup.commutator_le]
  have hKsup : kFive d t K = (kThree d t K ⊔ xQ d t K₁) ⊔ (eOne d t K)ᵍ[t] := by
    have h1 := hK5a
    rw [hX3] at h1
    exact h1.trans (sup_assoc _ _ _).symm
  have hAK5 : kThree d t K ⊔ xQ d t K₁ ≤ kFive d t K := sup_le hK3K5 hXQK5
  have hcomm : ∀ a ∈ kThree d t K ⊔ xQ d t K₁, ∀ b ∈ (eOne d t K)ᵍ[t], a * b = b * a :=
    fun a ha b hb => mem_centralizer_iff.1 (hcen hb) a (hAK5 ha)
  intro x hx y hy
  rw [hKsup] at hx hy
  obtain ⟨a, ha, e, he, rfl⟩ := (mem_sup_of_forall_commute hcomm).1 hx
  obtain ⟨a', ha', e', he', rfl⟩ := (mem_sup_of_forall_commute hcomm).1 hy
  have hee' : e * e' = e' * e := by
    exact mem_centralizer_iff.1 (hcen he') e (hOK5 ((by rw [hX3]; exact le_sup_right :
      (eOne d t K)ᵍ[t] ≤ pCoreOf 2 (kFive d t K)) he))
  have h1 : a * e * (a' * e') * (a * e)⁻¹ * (a' * e')⁻¹ = a * a' * a⁻¹ * a'⁻¹ := by
    have := commutatorElement_mul_mul_of_commute' (a := a) (b := a') (c := e) (d := e')
      (hcomm a' ha' e he).symm hee'
      (hcomm a ha e' he').symm
    simpa only [commutatorElement_def] using this
  show a * e * (a' * e') * (a * e)⁻¹ * (a' * e')⁻¹ ∈ kThree d t K ⊔ xQ d t K₁
  rw [h1]
  exact mul_mem (mul_mem (mul_mem ha ha') (inv_mem ha)) (inv_mem ha')

end Phase2

section Phase3

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem commutator_K1'_conjT (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    ⁅(⁅K₁, K₁⁆ : Subgroup G), (⁅K₁, K₁⁆ : Subgroup G)ᵍ[t]⁆ = ⊥ := by
  have ht2 : t * t = 1 := h.t_mul_t
  obtain ⟨⟨hV1K, hV1z⟩, ⟨hN1, hcV, hK1', hK1''⟩⟩ := E3_commutators h d hp hK₁
  have hV1t : (yamadaV₁ d t)ᵍ[t] = yamadaV₁ d t :=
    conjT_eq_of_mem_normalizer (h.t_mem_normalizer_yamadaV₁ d)
  generalize (⁅K₁, K₁⁆ : Subgroup G) = K1p at *
  generalize (⁅K1p, K1p⁆ : Subgroup G) = K1pp at *
  have hzc : yamadaV₁ d t ≤ centralizer ((nOne d t : Subgroup G) : Set G) :=
    hV1z.trans inf_le_right
  have hK1'N : K1p ≤ nOne d t := by rw [hN1]; exact le_sup_left
  have hK1'tN : K1pᵍ[t] ≤ nOne d t := by rw [hN1]; exact le_sup_right
  have hK1ppK : K1pp ≤ K1p := hK1'.symm ▸ le_sup_left
  have hK1te : K1pᵍ[t] = K1ppᵍ[t] ⊔ yamadaV₁ d t := by
    have := congrArg (fun A : Subgroup G => Aᵍ[t]) hK1'
    simpa only [conjT_sup, hV1t] using this
  rw [commutator_eq_bot_iff_le_centralizer]
  refine hK1'.le.trans (sup_le ?_ ?_)
  ·
    refine le_centralizer_iff.2 ?_
    rw [hK1te]
    refine sup_le (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hK1'')) ?_
    exact hzc.trans (Subgroup.centralizer_le (hK1ppK.trans hK1'N))
  · exact hzc.trans (Subgroup.centralizer_le hK1'tN)

theorem commutator_aTwo_conjT (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    ⁅aTwo d t K, (aTwo d t K)ᵍ[t]⁆ = ⊥ := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  obtain ⟨-, hA⟩ := aTwo_eq h d hp hL
  obtain ⟨⟨hK3E, hK3O, hK3Q, hK3Z, hN3, hK3i, hK3c, hN3Q⟩, -, -⟩ := A3_structure h d hp hK
  obtain ⟨⟨hX1, hX2, hX3, hX4, hX5, hX6⟩, -⟩ := G2_structure_Q1 h d hp hL
  have hcK1 := commutator_K1'_conjT h d hp hL.factor
  have hXQK1 : xQ d t K₁ ≤ ⁅K₁, K₁⁆ := (inf_le_left : xQ d t K₁ ≤ qOne d t K₁).trans inf_le_right
  have hAD : ⁅kThree d t K, (xQ d t K₁)ᵍ[t]⁆ = ⊥ := by
    have := congrArg (fun A : Subgroup G => Aᵍ[t]) hX6
    simp only [conjT_commutator, conjT_conjT ht2, conjT_bot] at this
    rwa [Subgroup.commutator_comm] at this
  rw [hA, conjT_sup]
  refine commutator_sup_sup_eq_bot hK3c hAD hX6 ?_
  ·
    refine le_bot_iff.1 ?_
    rw [← hcK1]
    exact Subgroup.commutator_mono hXQK1 (Subgroup.map_mono hXQK1)

theorem E1_commute_E1t (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∀ a ∈ eOne d t K, ∀ b ∈ (eOne d t K)ᵍ[t], a * b = b * a := by
  obtain ⟨⟨hK3E, hK3O, hK3Q, hK3Z, hN3, hK3i, hK3c, hN3Q⟩, -, -⟩ := A3_structure h d hp hK
  exact commutator_eq_bot_iff.1 (le_bot_iff.1 (hK3c ▸
    Subgroup.commutator_mono hK3E (Subgroup.map_mono hK3E)))

theorem aTwo_inf_Y2 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    aTwo d t K ⊓ yamadaY₂ d t = eOne d t K := by
  have hK := hL.comp
  obtain ⟨hE1K5', hK3K5', hK5eq, hK5inf⟩ := K5_split h d hp hL
  obtain ⟨hA, -⟩ := aTwo_eq h d hp hL
  obtain ⟨-, -, ⟨hE1, hE2, hE3, hE4, hE5, hE6, hE7⟩⟩ := A2_sylow h d hp hK
  have hE1A : eOne d t K ≤ aTwo d t K := hA ▸ hE1K5'
  have hAE : aTwo d t K ⊓ (eOne d t K)ᵍ[t] = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hK5inf, hA]
  rw [hE1, inf_sup_eq_of_le_of_commute hE1A (E1_commute_E1t h d hp hK), hAE, sup_bot_eq]

theorem aTwo_inf_conjT (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    aTwo d t K ⊓ (aTwo d t K)ᵍ[t] = ⊥ := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  obtain ⟨hA, -⟩ := aTwo_eq h d hp hL
  obtain ⟨-, -, ⟨hE1, hE2, hE3, hE4, hE5, hE6, hE7⟩⟩ := A2_sylow h d hp hK
  obtain ⟨-, ⟨hK5a, hK5b, hK5c⟩, -⟩ := G1_decomposition_mod_Y2 h d hp hL
  obtain ⟨⟨hG1a, hG1b, hG1c, hG1d, hG1e, hG1f, hG1g⟩, -, -⟩ := G1_decomposition_mod_Y2 h d hp hL
  have hY2t : (yamadaY₂ d t)ᵍ[t] = yamadaY₂ d t :=
    conjT_eq_of_mem_normalizer (h.t_mem_normalizer_yamadaY₂ d)
  have h1 := aTwo_inf_Y2 h d hp hL
  have h2 : (aTwo d t K)ᵍ[t] ⊓ yamadaY₂ d t = (eOne d t K)ᵍ[t] := by
    have := congrArg (fun A : Subgroup G => Aᵍ[t]) h1
    simpa only [conjT_inf, hY2t] using this
  have hAK5 : aTwo d t K ≤ kFive d t K := hA ▸ commutator_self_le _
  have hAK5t : (aTwo d t K)ᵍ[t] ≤ (kFive d t K)ᵍ[t] := Subgroup.map_mono hAK5
  refine le_bot_iff.1 ?_
  rw [← hE2]
  refine le_inf ?_ ?_
  · refine le_trans ?_ h1.le
    exact le_inf inf_le_left (le_trans (inf_le_inf hAK5 hAK5t) (hG1b ▸ le_rfl))
  · refine le_trans ?_ h2.le
    exact le_inf inf_le_right (le_trans (inf_le_inf hAK5 hAK5t) (hG1b ▸ le_rfl))

theorem nTwo_eq_aTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    nTwo d t = aTwo d t K ⊔ (aTwo d t K)ᵍ[t] := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  obtain ⟨hE1K5', hK3K5', hK5eq, hK5inf⟩ := K5_split h d hp hL
  obtain ⟨hA, -⟩ := aTwo_eq h d hp hL
  obtain ⟨⟨hG1a, hG1b, hG1c, hG1d, hG1e, hG1f, hG1g⟩, -, -⟩ := G1_decomposition_mod_Y2 h d hp hL
  have hE1A : eOne d t K ≤ aTwo d t K := hA ▸ hE1K5'
  have hK5A : kFive d t K = aTwo d t K ⊔ (eOne d t K)ᵍ[t] := by rw [hA]; exact hK5eq
  have hK5tA : (kFive d t K)ᵍ[t] = (aTwo d t K)ᵍ[t] ⊔ eOne d t K := by
    rw [hK5A, conjT_sup, conjT_conjT ht2]
  have hAK5 : aTwo d t K ≤ kFive d t K := hA ▸ commutator_self_le _
  rw [hG1a]
  refine le_antisymm (sup_le ?_ ?_) (sup_le_sup hAK5 (Subgroup.map_mono hAK5))
  · rw [hK5A]; exact sup_le le_sup_left ((Subgroup.map_mono hE1A).trans le_sup_right)
  · rw [hK5tA]; exact sup_le le_sup_right (hE1A.trans le_sup_left)

theorem pCoreOf_aTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    pCoreOf 2 (aTwo d t K) = xQ d t K₁ ∧ pCoreOf 2 ((aTwo d t K)ᵍ[t]) = (xQ d t K₁)ᵍ[t] := by
  have hA := (aTwo_eq h d hp hL).1
  have h1 : pCoreOf 2 (aTwo d t K) = xQ d t K₁ := by
    rw [hA]; exact pCoreOf_commutator_K5_eq_xQ h d hp hL
  exact ⟨h1, by rw [← h1]; exact pCoreOf_map_conj _ _⟩

theorem yamadaM₆_eq_aTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    yamadaM₆ d t = pCoreOf 2 (aTwo d t K) ⊔ pCoreOf 2 ((aTwo d t K)ᵍ[t]) := by
  have ht2 : t * t = 1 := h.t_mul_t
  obtain ⟨h1, h2⟩ := pCoreOf_aTwo h d hp hL
  obtain ⟨-, ⟨hK5a, hK5b, hK5c⟩, -⟩ := G1_decomposition_mod_Y2 h d hp hL
  obtain ⟨⟨hX1, hX2, hX3, hX4, hX5, hX6⟩, -⟩ := G2_structure_Q1 h d hp hL
  have hE1XQ : eOne d t K ≤ xQ d t K₁ := by rw [← hX2]; exact inf_le_left
  rw [h1, h2, hK5b, pCoreOf_map_conj, hX3, conjT_sup, conjT_conjT ht2]
  show (xQ d t K₁ ⊔ (eOne d t K)ᵍ[t]) ⊔ ((xQ d t K₁)ᵍ[t] ⊔ eOne d t K) = _
  refine le_antisymm
    (sup_le (sup_le le_sup_left ?_) (sup_le le_sup_right (hE1XQ.trans le_sup_left)))
    (sup_le_sup le_sup_left le_sup_left)
  exact (Subgroup.map_mono hE1XQ).trans le_sup_right

theorem pZero_le_yamadaP (d : TrialityD4Data L (2 ^ f)) (t : G) (K K₁ : Subgroup G) :
    pZero d t K K₁ ≤ yamadaP d t := by
  refine sup_le ?_ ?_
  · exact (inf_le_left : qThree d t K ≤ prodX d t).trans
      ((inf_le_left : prodX d t ≤ yamadaD₅ d t).trans (yamadaD₅_le_yamadaP d t))
  · exact (inf_le_left : xQ d t K₁ ≤ qOne d t K₁).trans inf_le_left

theorem pZero_le_aTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    pZero d t K K₁ ≤ aTwo d t K := by
  rw [(aTwo_eq h d hp hL).2]
  exact sup_le_sup_right (qThree_le_kThree h d hp hL.comp) _

theorem yamadaP_inf_aTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    yamadaP d t ⊓ aTwo d t K = pZero d t K K₁ := by
  have hK := hL.comp
  obtain ⟨hE1K5', hK3K5', hK5eq, hK5inf⟩ := K5_split h d hp hL
  obtain ⟨hA, -⟩ := aTwo_eq h d hp hL
  obtain ⟨-, ⟨hK5a, hK5b, hK5c⟩, ⟨hP5a, hP5b⟩⟩ := G1_decomposition_mod_Y2 h d hp hL
  obtain ⟨⟨hX1, hX2, hX3, hX4, hX5, hX6⟩, ⟨hQ1, hQ2, hQ3, hQ4, hQ5, hQ6⟩⟩ :=
    G2_structure_Q1 h d hp hL
  have hP0A := pZero_le_aTwo h d hp hL
  have hAE : aTwo d t K ⊓ (eOne d t K)ᵍ[t] = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hK5inf, hA]
  refine le_antisymm ?_ (le_inf (pZero_le_yamadaP d t K K₁) hP0A)
  intro x hx
  obtain ⟨hxP, hxA⟩ := mem_inf.1 hx
  have hxK5 : x ∈ yamadaP d t ⊓ kFive d t K := by
    refine mem_inf.2 ⟨hxP, ?_⟩
    rw [hA] at hxA
    exact commutator_self_le _ hxA
  have hx2 : x ∈ pZero d t K K₁ ⊔ (eOne d t K)ᵍ[t] := by
    rw [hP5a, hX3] at hxK5
    unfold pZero
    rw [sup_assoc]
    exact hxK5
  have hx3 : x ∈ aTwo d t K ⊓ (pZero d t K K₁ ⊔ (eOne d t K)ᵍ[t]) := mem_inf.2 ⟨hxA, hx2⟩
  rw [inf_sup_eq_of_le_of_commute hP0A (commutator_eq_bot_iff.1 hQ3), hAE, sup_bot_eq] at hx3
  exact hx3

end Phase3

section Phase4

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem yamadaP_eq_pZero_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    yamadaP d t = pZero d t K K₁ ⊔ (pZero d t K K₁)ᵍ[t] := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  have hF1 := (F0_sylow h d hp hK hL.factor).1.1
  have hQ4 := (G2_structure_Q1 h d hp hL).2.2.2.2.1
  have hZP0 : zc (qThree d t K) ≤ pZero d t K K₁ :=
    (inf_le_left : zc (qThree d t K) ≤ qThree d t K).trans le_sup_left
  have hP0P := pZero_le_yamadaP d t K K₁
  have hPt : (yamadaP d t)ᵍ[t] = yamadaP d t :=
    conjT_eq_of_mem_normalizer (h.t_mem_normalizer_yamadaP d hp.layer)
  have hP0tP : (pZero d t K K₁)ᵍ[t] ≤ yamadaP d t := by
    have := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hP0P
    rwa [hPt] at this
  refine le_antisymm ?_ (sup_le hP0P hP0tP)
  have hQ1P0 : qOne d t K₁ ≤ pZero d t K K₁ ⊔ (pZero d t K K₁)ᵍ[t] := by
    rw [hQ4]
    exact sup_le le_sup_left ((Subgroup.map_mono hZP0).trans le_sup_right)
  have hQ1tP0 : (qOne d t K₁)ᵍ[t] ≤ pZero d t K K₁ ⊔ (pZero d t K K₁)ᵍ[t] := by
    have := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hQ1P0
    rw [conjT_sup, conjT_conjT ht2, sup_comm] at this
    exact this
  rw [hF1]
  exact sup_le hQ1P0 hQ1tP0

theorem yamadaP_eq_pZero (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    yamadaP d t = pZero d t K K₁ ⊔ (pZero d t K K₁)ᵍ[t] ∧
      pZero d t K K₁ ⊓ (pZero d t K K₁)ᵍ[t] = ⊥ ∧ ⁅pZero d t K K₁, (pZero d t K K₁)ᵍ[t]⁆ = ⊥ := by
  have hP0A := pZero_le_aTwo h d hp hL
  have h1 := aTwo_inf_conjT h d hp hL
  have h2 := commutator_aTwo_conjT h d hp hL
  refine ⟨yamadaP_eq_pZero_sup h d hp hL, ?_, ?_⟩
  · exact le_bot_iff.1 (h1 ▸ inf_le_inf hP0A (Subgroup.map_mono hP0A))
  · exact le_bot_iff.1 (h2 ▸ Subgroup.commutator_mono hP0A (Subgroup.map_mono hP0A))

theorem dg_aTwo_pZero (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁)
    (hc : ⁅aTwo d t K, (aTwo d t K)ᵍ[t]⁆ = ⊥) :
    dg (aTwo d t K) t hc (pZero d t K K₁) = d.S.map L.subtype := by
  have ht2 : t * t = 1 := h.t_mul_t
  rw [dg_eq_inf_centralizer ht2 hc (aTwo_inf_conjT h d hp hL) (pZero_le_aTwo h d hp hL),
    ← (yamadaP_eq_pZero h d hp hL).1]
  exact (T4_series_free h d hp).2.2.2.2.2.2.1

end Phase4

section Phase5

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem zc_qThree_le_eOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    zc (qThree d t K) ≤ eOne d t K :=
  (A4_u_component h d hp hK).1.1 ▸ inf_le_left

theorem eOne_le_commutator_pZero (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    eOne d t K ≤ ⁅pZero d t K K₁, pZero d t K K₁⁆ := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  have hc := commutator_aTwo_conjT h d hp hL
  have hi := aTwo_inf_conjT h d hp hL
  obtain ⟨hE1K5', hK3K5', hK5eq, hK5inf⟩ := K5_split h d hp hL
  obtain ⟨hA, -⟩ := aTwo_eq h d hp hL
  obtain ⟨-, -, ⟨hE1, hE2, hE3, hE4, hE5, hE6, hE7⟩⟩ := A2_sylow h d hp hK
  have hE1A : eOne d t K ≤ aTwo d t K := hA ▸ hE1K5'
  have hP0A := pZero_le_aTwo h d hp hL
  have hT4Y := (T4_series_free h d hp).2.1
  have h1 : dg (aTwo d t K) t hc (eOne d t K) ≤ d.Y.map L.subtype := by
    intro y hy
    obtain ⟨e, heA, heE, rfl⟩ := mem_dg_iff.1 hy
    rw [← hT4Y]
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [hE1]
      exact mul_mem (mem_sup_left heE) (mem_sup_right (conj_mem_map_conj_inv t heE))
    · exact range_diagonalHom_le hc ht2 ⟨⟨e, heA⟩, rfl⟩
  have h2 : d.Y.map L.subtype ≤ dg (aTwo d t K) t hc ⁅pZero d t K K₁, pZero d t K K₁⁆ := by
    rw [dg_commutator hP0A hP0A, dg_aTwo_pZero h d hp hL hc]
    exact Y_map_le_commutator_S d
  exact le_of_dg_le hi hE1A (h1.trans h2)

theorem eOne_le_aOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    eOne d t K ≤ aOne K₁ := by
  have hQ4 := (G2_structure_Q1 h d hp hL).2.2.2.2.1
  have hP0Q1 : pZero d t K K₁ ≤ qOne d t K₁ := by
    rw [hQ4]; exact le_sup_left
  have hP0K1 : pZero d t K K₁ ≤ ⁅K₁, K₁⁆ := hP0Q1.trans inf_le_right
  exact (eOne_le_commutator_pZero h d hp hL).trans (Subgroup.commutator_mono hP0K1 hP0K1)

theorem commutator_K1_eq_aOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    ⁅K₁, K₁⁆ = aOne K₁ ⊔ (zc (qThree d t K))ᵍ[t] := by
  have hK := hL.comp
  obtain ⟨-, ⟨hN1, hcV, hK1', hK1''⟩⟩ := E3_commutators h d hp hL.factor
  obtain ⟨⟨hZ1, hZ2, hZ3, hZ4⟩, -⟩ := A4_u_component h d hp hK
  have hZA : zc (qThree d t K) ≤ aOne K₁ :=
    (zc_qThree_le_eOne h d hp hK).trans (eOne_le_aOne h d hp hL)
  have : aOne K₁ ⊔ yamadaV₁ d t = ⁅K₁, K₁⁆ := hK1'.symm
  rw [← this, hZ3, ← sup_assoc, sup_eq_left.2 hZA]

theorem zc_qThree_conjT_le_V1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (zc (qThree d t K))ᵍ[t] ≤ yamadaV₁ d t := by
  obtain ⟨⟨hZ1, hZ2, hZ3, hZ4⟩, -⟩ := A4_u_component h d hp hK
  rw [hZ3]
  exact le_sup_right

theorem isPGroup_zc_qThree_conjT (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    IsPGroup 2 ((zc (qThree d t K))ᵍ[t] : Subgroup G) := by
  obtain ⟨⟨hZ1, hZ2, hZ3, hZ4⟩, -⟩ := A4_u_component h d hp hK
  refine IsPGroup.of_card (n := f) ?_
  rw [card_conjT, hZ2]

theorem zc_qThree_conjT_le_centralizer_K1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    (zc (qThree d t K))ᵍ[t] ≤ centralizer ((⁅K₁, K₁⁆ : Subgroup G) : Set G) := by
  obtain ⟨⟨hV1K, hV1z⟩, ⟨hN1, hcV, hK1', hK1''⟩⟩ := E3_commutators h d hp hL.factor
  have hK1'N : (⁅K₁, K₁⁆ : Subgroup G) ≤ nOne d t := by rw [hN1]; exact le_sup_left
  exact (zc_qThree_conjT_le_V1 h d hp hL.comp).trans
    (hV1z.trans ((inf_le_right).trans (Subgroup.centralizer_le hK1'N)))

theorem aOne_inf_Zt (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    aOne K₁ ⊓ (zc (qThree d t K))ᵍ[t] = ⊥ := by
  have hK := hL.comp
  obtain ⟨-, ⟨hN1, hcV, hK1', hK1''⟩⟩ := E3_commutators h d hp hL.factor
  obtain ⟨⟨hV1K, hV1z⟩, -⟩ := E3_commutators h d hp hL.factor
  obtain ⟨-, ⟨hQ1, hQ2, hQ3, hQ4, hQ5, hQ6⟩⟩ := G2_structure_Q1 h d hp hL
  have hZtV := zc_qThree_conjT_le_V1 h d hp hK
  exact commutator_inf_eq_bot_of_sylow_complement (P₀ := pZero d t K K₁)
    (hZtV.trans hV1K) (zc_qThree_conjT_le_centralizer_K1 h d hp hL)
    (isPGroup_zc_qThree_conjT h d hp hK) (isSylowOf_qOne h d hp hL)
    (by rw [sup_comm, hQ4]) (by rw [inf_comm]; exact hQ5)

theorem zc_qThree_commute_conjT (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∀ a ∈ zc (qThree d t K), ∀ b ∈ (zc (qThree d t K))ᵍ[t], a * b = b * a := fun a ha b hb =>
  E1_commute_E1t h d hp hK a (zc_qThree_le_eOne h d hp hK ha) b
    (Subgroup.map_mono (zc_qThree_le_eOne h d hp hK) hb)

theorem aOne_inf_conjT (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    aOne K₁ ⊓ (aOne K₁)ᵍ[t] = ⊥ := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  obtain ⟨⟨hZ1, hZ2, hZ3, hZ4⟩, -⟩ := A4_u_component h d hp hK
  have hE2 := (E2_decomposition h d hp hL.factor).1.2.1
  have hZA : zc (qThree d t K) ≤ aOne K₁ :=
    (zc_qThree_le_eOne h d hp hK).trans (eOne_le_aOne h d hp hL)
  have hAZt := aOne_inf_Zt h d hp hL
  have hV1t : (yamadaV₁ d t)ᵍ[t] = yamadaV₁ d t :=
    conjT_eq_of_mem_normalizer (h.t_mem_normalizer_yamadaV₁ d)
  have h1 : aOne K₁ ⊓ yamadaV₁ d t = zc (qThree d t K) := by
    rw [hZ3, inf_sup_eq_of_le_of_commute hZA (zc_qThree_commute_conjT h d hp hK), hAZt,
      sup_bot_eq]
  have h2 : (aOne K₁)ᵍ[t] ⊓ yamadaV₁ d t = (zc (qThree d t K))ᵍ[t] := by
    have := congrArg (fun A : Subgroup G => Aᵍ[t]) h1
    simpa only [conjT_inf, hV1t] using this
  have hAK1 : aOne K₁ ≤ ⁅K₁, K₁⁆ := commutator_self_le _
  refine le_bot_iff.1 ?_
  rw [← hZ4]
  refine le_inf ?_ ?_
  · refine le_trans ?_ h1.le
    exact le_inf inf_le_left (le_trans (inf_le_inf hAK1 (Subgroup.map_mono hAK1)) hE2.le)
  · refine le_trans ?_ h2.le
    exact le_inf inf_le_right (le_trans (inf_le_inf hAK1 (Subgroup.map_mono hAK1)) hE2.le)

theorem nOne_eq_aOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    nOne d t = aOne K₁ ⊔ (aOne K₁)ᵍ[t] := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  obtain ⟨-, ⟨hN1, hcV, hK1', hK1''⟩⟩ := E3_commutators h d hp hL.factor
  have hZA : zc (qThree d t K) ≤ aOne K₁ :=
    (zc_qThree_le_eOne h d hp hK).trans (eOne_le_aOne h d hp hL)
  have hK1eq := commutator_K1_eq_aOne h d hp hL
  rw [hN1]
  refine le_antisymm (sup_le ?_ ?_) (sup_le_sup (commutator_self_le _)
    (Subgroup.map_mono (commutator_self_le _)))
  · rw [hK1eq]
    exact sup_le le_sup_left ((Subgroup.map_mono hZA).trans le_sup_right)
  · have := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hK1eq.le
    rw [conjT_sup, conjT_conjT ht2] at this
    refine this.trans (sup_le le_sup_right ?_)
    exact hZA.trans le_sup_left

theorem zc_qThree_le_V1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    zc (qThree d t K) ≤ yamadaV₁ d t := by
  obtain ⟨⟨hZ1, hZ2, hZ3, hZ4⟩, -⟩ := A4_u_component h d hp hK
  rw [hZ3]
  exact le_sup_left

theorem isPGroup_zc_qThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    IsPGroup 2 (zc (qThree d t K) : Subgroup G) := by
  obtain ⟨⟨hZ1, hZ2, hZ3, hZ4⟩, -⟩ := A4_u_component h d hp hK
  refine IsPGroup.of_card (n := f) ?_
  rw [hZ2]

theorem yamadaD₅_eq_aOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    yamadaD₅ d t = pCoreOf 2 (aOne K₁) ⊔ pCoreOf 2 ((aOne K₁)ᵍ[t]) := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  obtain ⟨hD5a, -, -, hcM⟩ := (E2_decomposition h d hp hL.factor).2
  obtain ⟨⟨hV1K, hV1z⟩, ⟨hN1, hcV, hK1', hK1''⟩⟩ := E3_commutators h d hp hL.factor
  have hZA : zc (qThree d t K) ≤ aOne K₁ :=
    (zc_qThree_le_eOne h d hp hK).trans (eOne_le_aOne h d hp hL)
  have hK1eq := commutator_K1_eq_aOne h d hp hL
  have hZc := zc_qThree_conjT_le_centralizer_K1 h d hp hL
  have hZt2 := isPGroup_zc_qThree_conjT h d hp hK
  have hOK1 : pCoreOf 2 (⁅K₁, K₁⁆ : Subgroup G) =
      pCoreOf 2 (aOne K₁) ⊔ (zc (qThree d t K))ᵍ[t] := by
    conv_lhs => rw [hK1eq]
    exact pCoreOf_sup_of_central hZt2 (by rw [← hK1eq]; exact hZc)
  have hAN : aOne K₁ ≤ nOne d t := by
    rw [hN1]; exact (commutator_self_le (⁅K₁, K₁⁆ : Subgroup G)).trans le_sup_left
  have hZN : zc (qThree d t K) ≤ centralizer ((nOne d t : Subgroup G) : Set G) :=
    (zc_qThree_le_V1 h d hp hK).trans (hV1z.trans inf_le_right)
  have hZO : zc (qThree d t K) ≤ pCoreOf 2 (aOne K₁) := by
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZA (fun x hx => ?_)
      (isPGroup_zc_qThree h d hp hK)
    exact Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.1 hZN (hAN hx))
  rw [hD5a, hcM, hOK1, conjT_sup, conjT_conjT ht2, pCoreOf_map_conj]
  exact le_antisymm (sup_le (sup_le le_sup_left ((Subgroup.map_mono hZO).trans le_sup_right))
    (sup_le le_sup_right (hZO.trans le_sup_left))) (sup_le_sup le_sup_left le_sup_left)

theorem card_aOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    Nat.card (aOne K₁) = Nat.card (cLV d) := by
  have hK := hL.comp
  obtain ⟨⟨hZ1, hZ2, hZ3, hZ4⟩, -⟩ := A4_u_component h d hp hK
  have hK1eq := commutator_K1_eq_aOne h d hp hL
  have hAZ := aOne_inf_Zt h d hp hL
  have hZc := zc_qThree_conjT_le_centralizer_K1 h d hp hL
  have hAK1 : aOne K₁ ≤ ⁅K₁, K₁⁆ := commutator_self_le _
  have hnorm : (zc (qThree d t K))ᵍ[t] ≤ normalizer ((aOne K₁ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hAK1 (hZc hx))
  have h1 := card_sup_mul_card_inf_eq hnorm
  rw [← hK1eq, hAZ, card_bot, mul_one, card_commutator_K₁ h d hp hL.factor, card_conjT, hZ2] at h1
  have hpos : 0 < 2 ^ f := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1]
  ring

theorem dg_aOne_eq_cLV (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁)
    (hc : ⁅aOne K₁, (aOne K₁)ᵍ[t]⁆ = ⊥) :
    dg (aOne K₁) t hc (aOne K₁) = cLV d := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hi := aOne_inf_conjT h d hp hL
  have hdg := dg_eq_inf_centralizer ht2 hc hi (le_refl (aOne K₁))
  rw [← nOne_eq_aOne h d hp hL] at hdg
  have hcLV : cLV d ≤ dg (aOne K₁) t hc (aOne K₁) := by
    rw [hdg]
    refine le_inf (cLV_le_nOne h d hp) ?_
    exact (Subgroup.map_subtype_le _).trans h.L_le_centralizer
  refine (Subgroup.eq_of_le_of_card_ge hcLV ?_).symm
  rw [card_dg hi (le_refl _), card_aOne h d hp hL]

theorem pZero_inf_centralizer_le_qThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    pZero d t K K₁ ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) ≤ qThree d t K := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  obtain ⟨-, ⟨hX1, hX2, hX3, hX4, hX5⟩, -⟩ := A2_sylow h d hp hK
  have hc := commutator_aTwo_conjT h d hp hL
  have hi := aTwo_inf_conjT h d hp hL
  have hP0A := pZero_le_aTwo h d hp hL
  have hT5P := (T5_J₀ h d hp).2.2.2.2.2.2.2.2.2.2.1
  have hT4P := (T4_series_free h d hp).2.2.2.2.2.2.1
  have hQ3P0 : qThree d t K ≤ pZero d t K K₁ := le_sup_left
  intro p hp'
  obtain ⟨hpP0, hpJ⟩ := mem_inf.1 hp'
  have hδ : p * (t⁻¹ * p * t) ∈ dg (aTwo d t K) t hc (pZero d t K K₁) :=
    delta_mem_dg (hP0A hpP0) hpP0
  rw [dg_aTwo_pZero h d hp hL hc, ← hT4P] at hδ
  obtain ⟨hδP, hδC⟩ := mem_inf.1 hδ
  have hδJ : p * (t⁻¹ * p * t) ∈ centralizer ((jZeroG d : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro j hj
    have hjp : j * p = p * j := mem_centralizer_iff.1 hpJ j hj
    have hjt : j * t = t * j := mem_centralizer_singleton_iff.1 (jZeroG_le_centralizer_t h d hj)
    have hjti : j * t⁻¹ = t⁻¹ * j := by
      calc j * t⁻¹ = t⁻¹ * (t * j) * t⁻¹ := by group
        _ = t⁻¹ * (j * t) * t⁻¹ := by rw [hjt]
        _ = t⁻¹ * j := by group
    calc j * (p * (t⁻¹ * p * t)) = (j * p) * t⁻¹ * p * t := by group
      _ = p * (j * t⁻¹) * p * t := by rw [hjp]; group
      _ = p * t⁻¹ * (j * p) * t := by rw [hjti]; group
      _ = p * t⁻¹ * p * (j * t) := by rw [hjp]; group
      _ = p * t⁻¹ * p * (t * j) := by rw [hjt]
      _ = (p * (t⁻¹ * p * t)) * j := by group
  have hδX : p * (t⁻¹ * p * t) ∈ prodX d t := by
    rw [← hT5P]; exact mem_inf.2 ⟨hδP, hδJ⟩
  have hdgQ := dg_eq_inf_centralizer ht2 hX3 hX2 (le_refl (qThree d t K))
  rw [← hX1] at hdgQ
  have hδQ : p * (t⁻¹ * p * t) ∈ dg (qThree d t K) t hX3 (qThree d t K) := by
    rw [hdgQ]; exact mem_inf.2 ⟨hδX, hδC⟩
  obtain ⟨q, hqQ, hqQ', hq⟩ := mem_dg_iff.1 hδQ
  have := eq_of_delta_eq hc hi (hP0A hpP0) (hP0A (hQ3P0 hqQ)) hq.symm
  rw [← this] at hqQ
  exact hqQ

theorem qThree_le_aOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    qThree d t K ≤ aOne K₁ := by
  have hK := hL.comp
  obtain ⟨-, hKu, hQ3⟩ := A4_u_component h d hp hK
  have hE1A := eOne_le_aOne h d hp hL
  have hu : uG d ∈ normalizer ((aOne K₁ : Subgroup G) : Set G) :=
    (nOne_le_normalizer hL.factor).2.2 (cLV_le_nOne h d hp (uG_mem_cLV d))
  rw [hQ3]
  refine sup_le hE1A ?_
  calc (eOne d t K)ᵍ[uG d] ≤ (aOne K₁)ᵍ[uG d] := Subgroup.map_mono hE1A
    _ = aOne K₁ := conjT_eq_of_mem_normalizer hu

theorem qThree_le_yamadaP (d : TrialityD4Data L (2 ^ f)) (t : G) (K : Subgroup G) :
    qThree d t K ≤ yamadaP d t :=
  (inf_le_left : qThree d t K ≤ prodX d t).trans
    ((inf_le_left : prodX d t ≤ yamadaD₅ d t).trans (yamadaD₅_le_yamadaP d t))

theorem qOne_eq_inf_aOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    qOne d t K₁ = (yamadaP d t ⊓ aOne K₁) ⊔ (zc (qThree d t K))ᵍ[t] := by
  have hK := hL.comp
  have hK1eq := commutator_K1_eq_aOne h d hp hL
  have hZc := zc_qThree_conjT_le_centralizer_K1 h d hp hL
  have hQ4 := (G2_structure_Q1 h d hp hL).2.2.2.2.1
  have hZtQ : (zc (qThree d t K))ᵍ[t] ≤ qOne d t K₁ := by rw [hQ4]; exact le_sup_right
  have hQP : qOne d t K₁ ≤ yamadaP d t := inf_le_left
  have hAK1 : aOne K₁ ≤ ⁅K₁, K₁⁆ := commutator_self_le _
  apply le_antisymm
  · intro x hx
    have hxK1 : x ∈ aOne K₁ ⊔ (zc (qThree d t K))ᵍ[t] := hK1eq ▸ (inf_le_right : qOne d t K₁ ≤ _) hx
    obtain ⟨a, ha, z, hz, rfl⟩ := (mem_sup_of_forall_commute (fun a ha z hz =>
      mem_centralizer_iff.1 (hZc hz) a (hAK1 ha))).1 hxK1
    have haP : a ∈ yamadaP d t := by
      have := mul_mem (hQP hx) (inv_mem (hQP (hZtQ hz)))
      simpa using this
    exact mul_mem (mem_sup_left (mem_inf.2 ⟨haP, ha⟩)) (mem_sup_right hz)
  · have hB0Q : yamadaP d t ⊓ aOne K₁ ≤ qOne d t K₁ :=
      le_inf inf_le_left (inf_le_right.trans hAK1)
    exact sup_le hB0Q hZtQ

theorem jZero_le_normalizer_pZero (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    (jZeroG d : Subgroup G) ≤ normalizer (pZero d t K K₁ : Set G) := by
  have hK := hL.comp
  intro x hx
  refine Common.mem_normalizer_sup ?_ (jZero_le_normalizer_xQ h d hp hL.factor hx)
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le
    ((inf_le_right : qThree d t K ≤ K)) (jZero_le_centralizer_K d hK hx))

theorem yamadaP_inf_aOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    yamadaP d t ⊓ aOne K₁ = pZero d t K K₁ := by
  have hK := hL.comp
  have hlay := hp.layer
  obtain ⟨-, ⟨hQ1, hQ2, hQ3, hQ4, hQ5, hQ6⟩⟩ := G2_structure_Q1 h d hp hL
  have hAK1 : aOne K₁ ≤ ⁅K₁, K₁⁆ := commutator_self_le _
  have hQ1K1 : qOne d t K₁ ≤ ⁅K₁, K₁⁆ := inf_le_right
  have hQ1P : qOne d t K₁ ≤ yamadaP d t := inf_le_left
  have hO2 : IsPGroup 2 (qOne d t K₁) :=
    (h.yamada_5_32_of_layerHyp d hlay).2.1.to_le hQ1P
  have hJodd := odd_card_jZeroG (G := G) d
  have hZtQ : (zc (qThree d t K))ᵍ[t] ≤ qOne d t K₁ := by rw [hQ4]; exact le_sup_right
  have hZc : (zc (qThree d t K))ᵍ[t] ≤ centralizer ((qOne d t K₁ : Subgroup G) : Set G) :=
    (zc_qThree_conjT_le_centralizer_K1 h d hp hL).trans (Subgroup.centralizer_le hQ1K1)
  have hJZ : (jZeroG d : Subgroup G) ≤
      centralizer (((zc (qThree d t K))ᵍ[t] : Subgroup G) : Set G) := by
    refine le_centralizer_iff.1 ?_
    exact (zc_qThree_conjT_le_V1 h d hp hK).trans
      ((Setup.yamadaV₁_le_yamadaY₂ d).trans (T5_J₀ h d hp).1)
  have hfix : qOne d t K₁ ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) ≤
      qThree d t K ⊔ (zc (qThree d t K))ᵍ[t] := by
    intro x hx
    obtain ⟨hxQ, hxJ⟩ := mem_inf.1 hx
    have hxQ' : x ∈ pZero d t K K₁ ⊔ (zc (qThree d t K))ᵍ[t] := hQ4 ▸ hxQ
    obtain ⟨a, ha, z, hz, rfl⟩ := (mem_sup_of_forall_commute (commutator_eq_bot_iff.1 hQ6)).1 hxQ'
    have hzJ : z ∈ centralizer ((jZeroG d : Subgroup G) : Set G) :=
      le_centralizer_iff.1 hJZ hz
    have haJ : a ∈ centralizer ((jZeroG d : Subgroup G) : Set G) := by
      have := mul_mem hxJ (inv_mem hzJ)
      simpa using this
    exact mul_mem (mem_sup_left (pZero_inf_centralizer_le_qThree h d hp hL (mem_inf.2 ⟨ha, haJ⟩)))
      (mem_sup_right hz)
  have hB0Q : yamadaP d t ⊓ aOne K₁ ≤ qOne d t K₁ :=
    le_inf inf_le_left (inf_le_right.trans hAK1)
  have hJB0 : (jZeroG d : Subgroup G) ≤ normalizer ((yamadaP d t ⊓ aOne K₁ : Subgroup G) : Set G) :=
    fun x hx => Common.mem_normalizer_inf (jZeroG_le_normalizer_yamadaP h d hlay hx)
      ((nOne_le_normalizer hL.factor).2.2
        (cLV_le_nOne h d hp (jZeroG_le_cLV d hx)))
  have hB0 := eq_sup_commutator_of_complement (C := yamadaP d t ⊓ aOne K₁) (O := qOne d t K₁)
    (E := qThree d t K) (E' := (zc (qThree d t K))ᵍ[t]) (J := (jZeroG d : Subgroup G))
    hB0Q hO2 hJodd hJB0 (le_inf (qThree_le_yamadaP d t K) (qThree_le_aOne h d hp hL)) hZtQ hZc hJZ
    (le_bot_iff.1 ((inf_le_inf_right _ inf_le_right).trans (aOne_inf_Zt h d hp hL).le))
    (qOne_eq_inf_aOne h d hp hL).symm hfix
  have hP0 := eq_sup_commutator_of_complement (C := pZero d t K K₁) (O := qOne d t K₁)
    (E := qThree d t K) (E' := (zc (qThree d t K))ᵍ[t]) (J := (jZeroG d : Subgroup G))
    (by rw [hQ4]; exact le_sup_left) hO2 hJodd (jZero_le_normalizer_pZero h d hp hL) le_sup_left
    hZtQ hZc hJZ hQ5 hQ4.symm hfix
  rw [hB0, hP0]

end Phase5

end ProductDecompAux

section Statements

open ProductDecompAux

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem H1_decomposition (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    ∃ X : DiagonalPair d t,
      X.A₁ = aOne K₁ ∧ X.A₂ = aTwo d t K ∧ X.P₀ = pZero d t K K₁ ∧
      (nTwo d t = X.A₂ ⊔ X.A₂ᵍ[t] ∧ X.A₂ ⊓ X.A₂ᵍ[t] = ⊥ ∧
        yamadaM₆ d t = pCoreOf 2 X.A₂ ⊔ pCoreOf 2 (X.A₂ᵍ[t]) ∧
        pCoreOf 2 X.A₂ = pCoreOf 2 ⁅kFive d t K, kFive d t K⁆ ∧
        pCoreOf 2 ⁅kFive d t K, kFive d t K⁆ = xQ d t K₁ ∧ yamadaP d t ⊓ X.A₂ = X.P₀) ∧
      (nOne d t = X.A₁ ⊔ X.A₁ᵍ[t] ∧ X.A₁ ⊓ X.A₁ᵍ[t] = ⊥ ∧
        ⁅K₁, K₁⁆ = X.A₁ ⊔ (zc (qThree d t K))ᵍ[t] ∧
        X.A₁ ⊓ (zc (qThree d t K))ᵍ[t] = ⊥ ∧
        yamadaD₅ d t = pCoreOf 2 X.A₁ ⊔ pCoreOf 2 (X.A₁ᵍ[t]) ∧ yamadaP d t ⊓ X.A₁ = X.P₀) ∧
      (yamadaP d t = X.P₀ ⊔ X.P₀ᵍ[t] ∧ X.P₀ ⊓ X.P₀ᵍ[t] = ⊥ ∧ ⁅X.P₀, X.P₀ᵍ[t]⁆ = ⊥) := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK := hL.comp
  have hc₁ : ⁅aOne K₁, (aOne K₁)ᵍ[t]⁆ = ⊥ := (E3_commutators h d hp hL.factor).2.2.2.2
  have hc₂ := commutator_aTwo_conjT h d hp hL
  have hi₁ := aOne_inf_conjT h d hp hL
  have hi₂ := aTwo_inf_conjT h d hp hL
  have hP₀A₁ : pZero d t K K₁ ≤ aOne K₁ := (yamadaP_inf_aOne h d hp hL) ▸ inf_le_right
  have hP₀A₂ := pZero_le_aTwo h d hp hL
  have hrange₁ : (diagonalHom (aOne K₁) t hc₁).range = cLV d := by
    rw [diagonalHom_range_eq_dg]; exact dg_aOne_eq_cLV h d hp hL hc₁
  have hrange₂ : (diagonalHom (aTwo d t K) t hc₂).range = lvM d := by
    rw [diagonalHom_range_eq_dg, dg_eq_inf_centralizer ht2 hc₂ hi₂ le_rfl,
      ← nTwo_eq_aTwo h d hp hL]
    exact (C2_decomposition h d hp hK).2.1.2.2.2.2.2.1
  have hrangeP : (pZero d t K K₁ |>.subgroupOf (aOne K₁)).map (diagonalHom (aOne K₁) t hc₁) =
      d.S.map L.subtype := by
    show dg (aOne K₁) t hc₁ (pZero d t K K₁) = _
    rw [dg_eq_inf_centralizer ht2 hc₁ hi₁ hP₀A₁, ← (yamadaP_eq_pZero h d hp hL).1]
    exact (T4_series_free h d hp).2.2.2.2.2.2.1
  refine ⟨⟨aOne K₁, aTwo d t K, pZero d t K K₁, hc₁, hc₂, hP₀A₁, hP₀A₂,
    diagonalHom_injective_of_inf_eq_bot hc₁ hi₁, diagonalHom_injective_of_inf_eq_bot hc₂ hi₂,
    hrange₁, hrange₂, hrangeP⟩, rfl, rfl, rfl, ?_, ?_, yamadaP_eq_pZero h d hp hL⟩
  · exact ⟨nTwo_eq_aTwo h d hp hL, hi₂, yamadaM₆_eq_aTwo h d hp hL,
      congrArg (pCoreOf 2) (aTwo_eq h d hp hL).1, pCoreOf_commutator_K5_eq_xQ h d hp hL,
      yamadaP_inf_aTwo h d hp hL⟩
  · exact ⟨nOne_eq_aOne h d hp hL, hi₁, commutator_K1_eq_aOne h d hp hL,
      aOne_inf_Zt h d hp hL, yamadaD₅_eq_aOne h d hp hL, yamadaP_inf_aOne h d hp hL⟩

end Statements

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

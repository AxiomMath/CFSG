module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A7Offender
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped Pointwise

section Group

variable {G : Type} [Group G]

open CFSG.Quasithin.BlueprintB2 in

theorem A7NatConfig.exists_offender_F4 (h1229 : Stmt12_2_9_F4) [CFSG.GH74.QTGen4.Finite4 G] (T : Sylow 2 G)
    {L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}
    (hyp : Hyp1223 G (T : Subgroup G) L V)
    (hCZ : centralizer (quasithinOmegaOneCenter (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    (h : A7NatConfig (T : Subgroup G) L V ψ)
    (hTP : ∀ t ∈ (T : Subgroup G), ∃ σ ∈ sevenP, IsCoordAct ψ t σ) :
    ∃ A : Subgroup G, IsMaxElemAbelian (T : Subgroup G) A ∧
      (∀ a ∈ A, ∀ σ, IsCoordAct ψ a σ → InT3 σ) ∧
      ∃ a ∈ A, ∃ σ, IsCoordAct ψ a σ ∧ IsTP σ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ : L = ⁅L, thompsonJ (T : Subgroup G)⁆ := (h1229 G T L V hyp).2 hCZ

  obtain ⟨A, hAmax, hAC⟩ : ∃ A : Subgroup G, IsMaxElemAbelian (T : Subgroup G) A ∧
      ¬ A ≤ centralizer (V : Set G) := by
    by_contra hc
    push Not at hc
    have hJC : thompsonJ (T : Subgroup G) ≤ centralizer (V : Set G) :=
      iSup₂_le fun A hA => hc A hA
    apply h.not_le_centralizer
    rw [hJ, commutator_le]
    intro l hl j hj
    rw [commutatorElement_def]
    exact mul_mem (conj_mem_centralizer_of_mem_normalizer (h.L_le hl) (hJC hj))
      (inv_mem (hJC hj))
  have hAT : A ≤ T := hAmax.1
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans h.T_le
  have hAel : IsElementaryAbelian 2 A := (isElemAbelian_iff_isElementaryAbelian 2).1 hAmax.2.1
  set lamN : normalizer (V : Set G) →* Perm (Fin 7) := coordRep ψ le_rfl h.Nact with hlamN
  set f : A →* Perm (Fin 7) := lamN.comp (inclusion hAN) with hfdef
  have hf_spec : ∀ a : A, IsCoordAct ψ a (f a) := fun a =>
    coordRep_spec ψ le_rfl h.Nact ⟨a, hAN a.2⟩
  have hf_eq : ∀ (a : A) {σ : Perm (Fin 7)}, IsCoordAct ψ a σ → f a = σ := fun a σ hσ =>
    IsCoordAct.unique ψ (hAN a.2) (hf_spec a) hσ
  have hfP : f.range ≤ sevenP := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨σ, hσP, hσ⟩ := hTP a (hAT a.2)
    rw [hf_eq a hσ]
    exact hσP
  have hf2 : ∀ σ ∈ f.range, σ * σ = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have ha2 : a * a = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two]
      exact (isElementaryAbelian_iff.1 hAel).2 a a.2)
    rw [ha2, map_one]

  have hker : f.ker = (centralizer (V : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact coordRep_eq_one_iff ψ le_rfl h.Nact ⟨a, hAN a.2⟩
  have hcardA : (A ⊓ centralizer (V : Set G)).relIndex A = Nat.card f.range := by
    rw [inf_relIndex_left, relIndex, ← hker, index_ker]

  have hcardV : Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) =
      Nat.card (fixE (f.range : Set (Perm (Fin 7)))) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨vec ψ ⟨(x : G), (mem_inf.1 x.2).1⟩,
      ?_, ?_⟩) ⟨?_, ?_⟩)
    · exact (mem_evenWeight).1 (vec_mem ψ _)
    · rintro _ ⟨a, rfl⟩
      have h1 := hf_spec a ⟨(x : G), (mem_inf.1 x.2).1⟩ ⟨(x : G), (mem_inf.1 x.2).1⟩ (by
        show (x : G) = a * x * (a : G)⁻¹
        rw [mem_centralizer_iff.1 (mem_inf.1 x.2).2 a a.2, mul_inv_cancel_right])
      exact h1.symm
    · intro x y hxy
      have h1 : vec ψ ⟨(x : G), (mem_inf.1 x.2).1⟩ = vec ψ ⟨(y : G), (mem_inf.1 y.2).1⟩ :=
        congrArg (fun z : fixE (f.range : Set (Perm (Fin 7))) => (z : Fin 7 → ZMod 2)) hxy
      have h2 : (x : G) = y := congrArg (fun z : V => (z : G)) (vec_injective ψ h1)
      exact Subtype.ext h2
    · rintro ⟨v, hv1, hv2⟩
      obtain ⟨x, hx⟩ := exists_vec_eq ψ (mem_evenWeight.2 hv1)
      refine ⟨⟨x, mem_inf.2 ⟨x.2, ?_⟩⟩, Subtype.ext hx⟩
      rw [mem_centralizer_iff]
      intro a ha
      let y : V := ⟨a * x * a⁻¹, (mem_normalizer_iff.1 (hAN ha) x).1 x.2⟩
      have h1 := hf_spec ⟨a, ha⟩ x y rfl
      rw [hx, hv2 _ ⟨⟨a, ha⟩, rfl⟩, ← hx] at h1
      have h2 : a * (x : G) * a⁻¹ = x := congrArg Subtype.val (vec_injective ψ h1)
      calc a * (x : G) = a * x * a⁻¹ * a := by group
        _ = x * a := by rw [h2]

  have hidx : (V ⊓ centralizer (A : Set G)).relIndex V ≤
      (A ⊓ centralizer (V : Set G)).relIndex A := by
    have hVT : V ≤ T := h.le_T
    have : (V.subgroupOf T).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).2 h.T_le
    have hVel : IsElementaryAbelian 2 V := isElementaryAbelian_of_vec ψ
    have h1 := relIndex_inf_centralizer_le (p := 2) (V := V.subgroupOf T)
      (A := A.subgroupOf T) (isElementaryAbelian_subgroupOf hVel)
      (isElementaryAbelian_subgroupOf hAel) (fun E hE => by
        have h2 := hAmax.2.2 (E.map (T : Subgroup G).subtype) (map_subtype_le E)
          ((isElemAbelian_iff_isElementaryAbelian 2).2 (isElementaryAbelian_map hE _))
        rwa [card_map_of_injective (subtype_injective _), ← card_subgroupOf_eq hAT] at h2)
    rw [centralizer_subgroupOf_eq hAT, centralizer_subgroupOf_eq hVT, ← inf_subgroupOf_eq,
      ← inf_subgroupOf_eq, relIndex_subgroupOf hVT, relIndex_subgroupOf hAT] at h1
    exact h1
  have hoff : 64 ≤ Nat.card f.range * Nat.card (fixE (f.range : Set (Perm (Fin 7)))) := by
    have h1 := relIndex_mul_card (V ⊓ centralizer (A : Set G)) V
    rw [inf_of_le_left inf_le_left, nat_card_of_vec ψ] at h1
    rw [← hcardA, ← hcardV, ← h1]
    exact Nat.mul_le_mul_right _ hidx
  obtain ⟨hT3, hTP3⟩ := offender_spec hfP hf2 hoff
  have hne : f.range ≠ ⊥ := by
    intro hbot
    apply hAC
    intro a ha
    have h1 : f ⟨a, ha⟩ = 1 := by
      have : f ⟨a, ha⟩ ∈ f.range := ⟨⟨a, ha⟩, rfl⟩
      rw [hbot, mem_bot] at this
      exact this
    exact (coordRep_eq_one_iff ψ le_rfl h.Nact ⟨a, hAN ha⟩).1 h1
  obtain ⟨σ, ⟨a, rfl⟩, hσ⟩ := hTP3 hne
  refine ⟨A, hAmax, fun b hb τ hτ => ?_, a, a.2, f a, hf_spec a, hσ⟩
  rw [← hf_eq ⟨b, hb⟩ hτ]
  exact hT3 _ ⟨⟨b, hb⟩, rfl⟩

theorem A7NatConfig.exists_thompsonJ_swap01_F4 (h1229 : Stmt12_2_9_F4) [CFSG.GH74.QTGen4.Finite4 G] (T : Sylow 2 G)
    {L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}
    (hyp : Hyp1223 G (T : Subgroup G) L V)
    (hCZ : centralizer (quasithinOmegaOneCenter (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    (h : A7NatConfig (T : Subgroup G) L V ψ)
    (hTalign : ∀ σ : Perm (Fin 7), (∃ t ∈ (T : Subgroup G), IsCoordAct ψ t σ) ↔
      σ ∈ sevenP ∧ ∃ n ∈ normalizer (V : Set G), IsCoordAct ψ n σ) :
    (∀ σ : Perm (Fin 7), ∃ n ∈ normalizer (V : Set G), IsCoordAct ψ n σ) ∧
      ∃ j ∈ thompsonJ (T : Subgroup G), IsCoordAct ψ j (swap 0 1) := by
  have hTP : ∀ t ∈ (T : Subgroup G), ∃ σ ∈ sevenP, IsCoordAct ψ t σ := by
    intro t ht
    obtain ⟨σ, hσ⟩ := h.Nact t (h.T_le ht)
    exact ⟨σ, ((hTalign σ).1 ⟨t, ht, hσ⟩).1, hσ⟩
  obtain ⟨A, hAmax, hAT3, a₀, ha₀, σ, hσ, hσTP⟩ := h.exists_offender_F4 h1229 T hyp hCZ hTP
  have hall := h.forall_exists_act (hAmax.1.trans h.T_le ha₀) hσ (sign_of_isTP hσTP)
  refine ⟨hall, ?_⟩
  rcases hσTP with rfl | rfl | rfl
  · exact ⟨a₀, (le_iSup₂ (f := fun A (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A hAmax)
      ha₀, hσ⟩
  · exact h.exists_thompsonJ_of_conj T hTalign hAmax hAT3 ha₀ hσ
      (mem_alternatingGroup.2 (by decide)) (by decide) conj23_inT3
  · exact h.exists_thompsonJ_of_conj T hTalign hAmax hAT3 ha₀ hσ
      (mem_alternatingGroup.2 (by decide)) (by decide) conj45_inT3

end Group

end CFSG.Quasithin.H13.A7

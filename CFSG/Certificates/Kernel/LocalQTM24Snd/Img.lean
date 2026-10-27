module

public import CFSG.Certificates.Kernel.LocalQTM24Snd.Ind
public import CFSG.Certificates.Kernel.LocalQTM24Snd.Tr
public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.EK

public section

namespace CFSG.KC.LQT.M24Snd

open Equiv CFSG.KC.LQT CFSG.KC.LQT.Syl.CoreSnd CFSG.KC.LQT.W

variable {n : ℕ}

private theorem aux_img_nilK_iff (l : List ℕ) : CFSG.KC.LQT.M24.nilK l = true ↔ l = [] := by
  cases l <;> simp [CFSG.KC.LQT.M24.nilK]

theorem act_data (hn : n ≤ 32) (eG nG : List (Perm (Fin n)))
    (hle : Subgroup.closure {g | g ∈ nG} ≤
      Subgroup.normalizer ((Subgroup.closure {g | g ∈ eG} : Subgroup (Perm (Fin n))) :
        Set (Perm (Fin n))))
    (ψ : Subgroup.closure {g | g ∈ nG} →* Perm (Subgroup.closure {g | g ∈ eG}))
    (hψ : ∀ (x : Subgroup.closure {g | g ∈ nG}) (e : Subgroup.closure {g | g ∈ eG}),
      ((ψ x e : Subgroup.closure {g | g ∈ eG}) : Perm (Fin n)) = x * e * (x : Perm (Fin n))⁻¹)
    (hE : CFSG.KC.LQT.Syl.eK n (eG.map P.code) = true) :
    ∃ (e : Perm (Subgroup.closure {g | g ∈ eG}) ≃* Perm (Fin 16))
      (Tl : List (Perm (Fin 16))),
      (∀ g : Perm (Fin n), ∀ hg : g ∈ Subgroup.closure {g | g ∈ nG},
        CFSG.KC.LQT.M24.indK n ((lst eG).map P.code) (P.code g) =
          P.code (e (ψ ⟨g, hg⟩))) ∧
      nG.map (fun g => CFSG.KC.LQT.M24.indK n ((lst eG).map P.code) (P.code g)) =
        Tl.map P.code ∧
      (e.toMonoidHom.comp ψ).range = Subgroup.closure {t | t ∈ Tl} := by
  classical
  obtain ⟨-, hB⟩ := CFSG.KC.LQT.Syl.CoreSnd.eK_facts eG hE
  obtain ⟨e, he⟩ := exists_equiv hB
  have hρ : ∀ (x : Subgroup.closure {g | g ∈ nG}) (i : Fin 16),
      (lst eG).getD ((e.toMonoidHom.comp ψ) x i) 1 =
        (x : Perm (Fin n)) * (lst eG).getD i 1 * (x : Perm (Fin n))⁻¹ := by
    intro x i
    have hi' : (i : ℕ) < (lst eG).length := by have := lst_length eG; omega
    have hmem : (lst eG).getD i 1 ∈ Subgroup.closure {g | g ∈ eG} := by
      rw [mem_closure_iff_lst hB, List.getD_eq_getElem _ _ hi']
      exact List.getElem_mem hi'
    have h1 := he (ψ x) i ⟨(lst eG).getD i 1, hmem⟩ rfl
    rw [hψ] at h1
    exact h1
  have hidx : ∀ (g : Perm (Fin n)) (hg : g ∈ Subgroup.closure {g | g ∈ nG}),
      CFSG.KC.LQT.M24.indK n ((lst eG).map P.code) (P.code g) =
        P.code (e (ψ ⟨g, hg⟩)) := by
    intro g hg
    have hgn : g ∈ Subgroup.normalizer ((Subgroup.closure {b | b ∈ eG} :
        Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := hle hg
    obtain ⟨τ', hτ'1, hτ'2⟩ := indK_spec hn hB g hgn
    have h2 : τ' = (e.toMonoidHom.comp ψ) ⟨g, hg⟩ :=
      indK_unique hB g τ' _ hτ'2 (hρ ⟨g, hg⟩)
    rw [hτ'1, h2]
    rfl
  let τ : Perm (Fin n) → Perm (Fin 16) := fun g =>
    if h : g ∈ Subgroup.closure {g | g ∈ nG} then (e.toMonoidHom.comp ψ) ⟨g, h⟩ else 1
  have hτ : ∀ (g : Perm (Fin n)) (hg : g ∈ Subgroup.closure {g | g ∈ nG}),
      τ g = (e.toMonoidHom.comp ψ) ⟨g, hg⟩ := fun g hg => dif_pos hg
  refine ⟨e, nG.map τ, hidx, ?_, ?_⟩
  · rw [List.map_map]
    refine List.map_congr_left fun g hg => ?_
    have hg' : g ∈ Subgroup.closure {g | g ∈ nG} := Subgroup.subset_closure hg
    rw [hidx g hg', Function.comp_apply, hτ g hg']
    rfl
  · refine (range_eq_closure nG (e.toMonoidHom.comp ψ)).trans ?_
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, List.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, hτ g (Subgroup.subset_closure hg)⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, hτ g (Subgroup.subset_closure hg)⟩

theorem imgD_snd (hn : n ≤ 32) (eG nG : List (Perm (Fin n)))
    (hle : Subgroup.closure {g | g ∈ nG} ≤
      Subgroup.normalizer ((Subgroup.closure {g | g ∈ eG} : Subgroup (Perm (Fin n))) :
        Set (Perm (Fin n))))
    (ψ : Subgroup.closure {g | g ∈ nG} →* Perm (Subgroup.closure {g | g ∈ eG}))
    (hψ : ∀ (x : Subgroup.closure {g | g ∈ nG}) (e : Subgroup.closure {g | g ∈ eG}),
      ((ψ x e : Subgroup.closure {g | g ∈ eG}) : Perm (Fin n)) = x * e * (x : Perm (Fin n))⁻¹)
    (C : List CFSG.KC.LQT.L.Lvl) (W : List (List (List ℕ))) (d m : ℕ)
    (hE : CFSG.KC.LQT.Syl.eK n (eG.map P.code) = true)
    (h : CFSG.KC.LQT.M24.imgCK n (eG.map P.code) (nG.map P.code) C W d m = true) :
    Nat.card ψ.range = m := by
  obtain ⟨-, hB⟩ := CFSG.KC.LQT.Syl.CoreSnd.eK_facts eG hE
  obtain ⟨e, Tl, hidx, hT, hrange⟩ := act_data hn eG nG hle ψ hψ hE
  unfold CFSG.KC.LQT.M24.imgCK at h
  simp only [forceN_eq] at h
  rw [CFSG.KC.LQT.Syl.CoreSnd.lstK_code hn eG] at h
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff, and_true] at h
  obtain ⟨-, hC, hI, hS, hm⟩ := h
  have hT' : List.map (CFSG.KC.LQT.M24.indK n ((lst eG).map P.code)) (nG.map P.code) =
      Tl.map P.code := by
    rw [List.map_map, Function.comp_def]
    exact hT
  rw [hT'] at hS
  have hcard := card_closure_of_grpS (by norm_num : 16 ≤ 32) hC hI Tl hS
  have hcardψ : Nat.card ψ.range = Nat.card (e.toMonoidHom.comp ψ).range := by
    rw [MonoidHom.range_comp]
    exact (Subgroup.card_map_of_injective e.injective).symm
  rw [hcardψ, hrange, hcard]
  exact P.beq_iff.1 hm

theorem imgV_snd (hn : n ≤ 32) (eG nG : List (Perm (Fin n)))
    (hle : Subgroup.closure {g | g ∈ nG} ≤
      Subgroup.normalizer ((Subgroup.closure {g | g ∈ eG} : Subgroup (Perm (Fin n))) :
        Set (Perm (Fin n))))
    (ψ : Subgroup.closure {g | g ∈ nG} →* Perm (Subgroup.closure {g | g ∈ eG}))
    (hψ : ∀ (x : Subgroup.closure {g | g ∈ nG}) (e : Subgroup.closure {g | g ∈ eG}),
      ((ψ x e : Subgroup.closure {g | g ∈ eG}) : Perm (Fin n)) = x * e * (x : Perm (Fin n))⁻¹)
    (r : ℕ) (ω : Perm (Fin n)) (hω : ω ∈ Subgroup.closure {g | g ∈ nG})
    (hE : CFSG.KC.LQT.Syl.eK n (eG.map P.code) = true)
    (h : CFSG.KC.LQT.M24.imgVK n (eG.map P.code) (nG.map P.code) (P.code ω) r = true) :
    ψ ⟨ω, hω⟩ ≠ 1 ∧ ψ ⟨ω, hω⟩ ^ 3 = 1 ∧
      ∀ x, ψ x * ψ ⟨ω, hω⟩ = ψ ⟨ω, hω⟩ * ψ x ∨
        ψ x * ψ ⟨ω, hω⟩ = ψ ⟨ω, hω⟩ ^ 2 * ψ x := by
  obtain ⟨-, hB⟩ := CFSG.KC.LQT.Syl.CoreSnd.eK_facts eG hE
  obtain ⟨e, Tl, hidx, hT, hrange⟩ := act_data hn eG nG hle ψ hψ hE
  have hT' : List.map (CFSG.KC.LQT.M24.indK n ((lst eG).map P.code)) (nG.map P.code) =
      Tl.map P.code := by
    rw [List.map_map, Function.comp_def]
    exact hT
  unfold CFSG.KC.LQT.M24.imgVK at h
  simp only [forceN_eq, P.letB_eq] at h
  rw [CFSG.KC.LQT.Syl.CoreSnd.lstK_code hn eG, hT', hidx ω hω] at h
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff, and_true] at h
  obtain ⟨-, hne, hcube, -, hbfs⟩ := h
  rw [bfsC_eq] at hbfs
  obtain ⟨hnil, hallS⟩ := P.andB_iff.1 hbfs
  have hF : (rounds (fun x => (Tl.map P.code).map (CFSG.KC.LQT.P.mul 16 x)) r
      [CFSG.KC.LQT.P.one 16] [CFSG.KC.LQT.P.one 16]).2 = [] := (aux_img_nilK_iff _).1 hnil
  have h16 : (16 : ℕ) ≤ 32 := by norm_num
  have hcl := rounds_closed h16 Tl r _ hF ((P.allL_iff _ _).1 hallS)
  have hne' : e (ψ ⟨ω, hω⟩) ≠ 1 := by
    intro e1
    apply P.notB_iff.1 hne
    rw [e1, ← P.code_one]
    exact Nat.beq_refl _
  have hcube' : e (ψ ⟨ω, hω⟩) ^ 3 = 1 := by
    have h1 := P.beq_iff.1 hcube
    simp only [P.code_mul h16, P.code_one] at h1
    have h2 := P.code_inj h16 h1
    rw [pow_succ, pow_two]
    exact h2
  refine ⟨fun h1 => hne' (by rw [h1, map_one]), ?_, fun x => ?_⟩
  · apply e.injective
    rw [map_pow, map_one]
    exact hcube'
  · have hmem : e (ψ x) ∈ Subgroup.closure {t | t ∈ Tl} := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    rcases P.orB_iff.1 (hcl (e (ψ x)) hmem) with h2 | h2
    · left
      have h3 := P.beq_iff.1 h2
      simp only [P.code_mul h16] at h3
      apply e.injective
      rw [map_mul, map_mul]
      exact P.code_inj h16 h3
    · right
      have h3 := P.beq_iff.1 h2
      simp only [P.code_mul h16] at h3
      apply e.injective
      rw [map_mul, map_mul, map_pow, pow_two]
      exact P.code_inj h16 h3

end CFSG.KC.LQT.M24Snd

end

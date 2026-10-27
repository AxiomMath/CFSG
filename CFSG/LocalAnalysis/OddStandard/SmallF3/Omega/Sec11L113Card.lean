module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Base
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Fin2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint Equiv

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

@[expose] def sec113PhiHom (hm : Sec11Model t L S z K1 K2 T Alt φ) :
    Multiplicative (Fin 6 → ZMod 2) →* G where
  toFun v := φ (Multiplicative.toAdd v)
  map_one' := hm.perm.map_zero
  map_mul' _ _ := hm.perm.mul _ _

theorem sec113_card_ker_phi (hm : Sec11Model t L S z K1 K2 T Alt φ) :
    Nat.card (sec113PhiHom hm).ker = 2 := by
  have h : ((sec113PhiHom hm).ker : Set (Multiplicative (Fin 6 → ZMod 2))) =
      {1, Multiplicative.ofAdd (fun _ => (1 : ZMod 2))} := by
    ext v
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    show φ (Multiplicative.toAdd v) = 1 ↔ _
    rw [hm.perm.ker]
    constructor
    · rintro (h | h)
      · exact Or.inl (Multiplicative.toAdd.injective h)
      · exact Or.inr (Multiplicative.toAdd.injective h)
    · rintro (h | h)
      · exact Or.inl (by rw [h]; rfl)
      · exact Or.inr (by rw [h]; rfl)
  have hne : (1 : Multiplicative (Fin 6 → ZMod 2)) ≠
      Multiplicative.ofAdd (fun _ => (1 : ZMod 2)) := by
    intro h
    have := congrFun (congrArg Multiplicative.toAdd h) 0
    exact absurd this (by decide)
  exact (Nat.card_coe_set_eq _).trans (by rw [h]; exact Set.ncard_pair hne)

theorem sec113_card_A (hm : Sec11Model t L S z K1 K2 T Alt φ) : Nat.card (secA t S L) = 32 := by
  have hr : (sec113PhiHom hm).range = secA t S L := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact hm.perm.mem _
    · intro hx
      obtain ⟨v, rfl⟩ := hm.perm.surj x hx
      exact ⟨Multiplicative.ofAdd v, rfl⟩
  have h := Subgroup.card_ker_mul_card_range (sec113PhiHom hm)
  have hc : Nat.card (Multiplicative (Fin 6 → ZMod 2)) = 64 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 6 → ZMod 2) ≃ _),
      Nat.card_eq_fintype_card]
    simp [Fintype.card_fun]
  rw [sec113_card_ker_phi hm, hr, hc] at h
  omega

@[expose] noncomputable def sec113RhoT (hm : Sec11Model t L S z K1 K2 T Alt φ)
    (hTM : T ≤ secM t S L) : ↥T →* Perm (Fin 6) :=
  hm.perm.rhoHom.comp (Subgroup.inclusion hTM)

@[expose] noncomputable def sec113Tstar (hm : Sec11Model t L S z K1 K2 T Alt φ)
    (hTM : T ≤ secM t S L) : Subgroup (Perm (Fin 6)) :=
  (sec113RhoT hm hTM).range

theorem mem_sec113Tstar (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L)
    {σ : Perm (Fin 6)} : σ ∈ sec113Tstar hm hTM ↔ ∃ x ∈ T, hm.perm.rho x = σ := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem sec113_ker_rhoT (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L) :
    (sec113RhoT hm hTM).ker = (secA t S L).subgroupOf T := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    have h1' : hm.perm.rho (x : G) = 1 := h1
    rw [hm.perm.rho_eq_one_iff (hTM x.2)] at h1'
    refine hm.cenTA x x.2 fun a ha => ?_
    calc (x : G) * a = ((x : G) * a * (x : G)⁻¹) * x := by group
      _ = a * x := by rw [h1' a ha]
  · intro hxA
    exact sec113_rho_of_mem_A hm hxA

theorem sec113_card_Tstar (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L)
    (hAT : secA t S L ≤ T) : 32 * Nat.card (sec113Tstar hm hTM) = Nat.card T := by
  have h := Subgroup.card_ker_mul_card_range (sec113RhoT hm hTM)
  rw [sec113_ker_rhoT hm hTM] at h
  have hA : Nat.card ((secA t S L).subgroupOf T) = 32 := by
    rw [← sec113_card_A hm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv
  rw [hA] at h
  exact h

theorem sec113_card_Tstar' (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L)
    (hAT : secA t S L ≤ T) :
    (Alt = ⊤ → Nat.card (sec113Tstar hm hTM) = 16) ∧
      (Alt ≠ ⊤ → Nat.card (sec113Tstar hm hTM) = 8) := by
  have h := sec113_card_Tstar hm hTM hAT
  refine ⟨fun hA => ?_, fun hA => ?_⟩
  · have := hm.card_T.1 hA
    omega
  · have := hm.card_T.2 hA
    omega

theorem sec113_Tstar_pres (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L)
    {σ : Perm (Fin 6)} (hσ : σ ∈ sec113Tstar hm hTM) :
    (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
  obtain ⟨x, hx, rfl⟩ := (mem_sec113Tstar hm hTM).1 hσ
  exact hm.T_set x hx

theorem sec113_V4_le_Tstar (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L)
    (hQT : secQ K1 K2 ≤ T) : ∀ s ∈ sec11V4, s ∈ sec113Tstar hm hTM := by
  intro s hs
  obtain ⟨q, hq, hact⟩ := hm.Q_act_surj s hs
  exact (mem_sec113Tstar hm hTM).2 ⟨q, hQT hq, hm.perm.rho_eq (hTM (hQT hq)) s hact⟩

theorem sec113_card_le (H : Subgroup (Perm (Fin 6))) (F : Finset (Perm (Fin 6)))
    (hF : ∀ σ ∈ F, σ ∈ H) : F.card ≤ Nat.card H := by
  have h1 : ((F : Set (Perm (Fin 6)))).ncard ≤ (H : Set (Perm (Fin 6))).ncard :=
    Set.ncard_le_ncard (fun σ hσ => hF σ (Finset.mem_coe.mp hσ)) (Set.toFinite _)
  have hH : Nat.card H = (H : Set (Perm (Fin 6))).ncard :=
    Nat.card_coe_set_eq (H : Set (Perm (Fin 6)))
  rw [Set.ncard_coe_finset] at h1
  omega

theorem sec113_exists_not_mem (H : Subgroup (Perm (Fin 6))) (F : Finset (Perm (Fin 6)))
    (hF : F.card < Nat.card H) : ∃ σ ∈ H, σ ∉ F := by
  by_contra hcon
  have hsub : ∀ σ ∈ H, σ ∈ F := fun σ hσ => by
    by_contra h
    exact hcon ⟨σ, hσ, h⟩
  have h1 : (H : Set (Perm (Fin 6))).ncard ≤ ((F : Set (Perm (Fin 6)))).ncard :=
    Set.ncard_le_ncard (fun σ hσ => Finset.mem_coe.mpr (hsub σ hσ)) (Set.toFinite _)
  have hH : Nat.card H = (H : Set (Perm (Fin 6))).ncard :=
    Nat.card_coe_set_eq (H : Set (Perm (Fin 6)))
  rw [Set.ncard_coe_finset] at h1
  omega

theorem sec113_alt_ne_top : alternatingGroup (Fin 6) ≠ ⊤ := by
  intro h
  have h1 : swap (0 : Fin 6) 1 ∈ alternatingGroup (Fin 6) := by
    rw [h]
    exact Subgroup.mem_top _
  rw [Equiv.Perm.mem_alternatingGroup] at h1
  rw [Equiv.Perm.sign_swap (by decide)] at h1
  exact absurd h1 (by decide)

theorem sec113_exists_tau_A (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L)
    (hQT : secQ K1 K2 ≤ T) (hAT : secA t S L ≤ T) (hAlt : Alt = alternatingGroup (Fin 6)) :
    ∃ τ ∈ sec113Tstar hm hTM, Sec113TypeA τ := by
  have hcard : Nat.card (sec113Tstar hm hTM) = 8 :=
    (sec113_card_Tstar' hm hTM hAT).2 (by rw [hAlt]; exact sec113_alt_ne_top)
  obtain ⟨σ, hσT, hσV⟩ := sec113_exists_not_mem (sec113Tstar hm hTM) sec11V4
    (by rw [sec113_cardV4, hcard]; norm_num)
  have hsign : Perm.sign σ = 1 := by
    obtain ⟨x, hx, rfl⟩ := (mem_sec113Tstar hm hTM).1 hσT
    exact Equiv.Perm.mem_alternatingGroup.mp (hAlt.le (hm.perm.rho_mem (hTM hx)))
  have hpow : σ ^ 8 = 1 := by
    have h := pow_card_eq_one' (x := (⟨σ, hσT⟩ : sec113Tstar hm hTM))
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  obtain ⟨v, hv, hty⟩ :=
    sec113_exists_typeA σ hsign (sec113_Tstar_pres hm hTM hσT) hpow hσV
  exact ⟨σ * v, (sec113Tstar hm hTM).mul_mem hσT (sec113_V4_le_Tstar hm hTM hQT v hv), hty⟩

theorem sec113_exists_tau_S (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L)
    (hQT : secQ K1 K2 ≤ T) (hAT : secA t S L ≤ T) (hAlt : Alt = ⊤)
    (h01 : swap 0 1 ∈ sec113Tstar hm hTM) : ∃ τ ∈ sec113Tstar hm hTM, Sec113TypeS τ := by
  have hcard : Nat.card (sec113Tstar hm hTM) = 16 := (sec113_card_Tstar' hm hTM hAT).1 hAlt
  obtain ⟨σ, hσT, hσF⟩ := sec113_exists_not_mem (sec113Tstar hm hTM)
    (sec11V4 ∪ sec11V4.image (fun s => swap 0 1 * s))
    (by rw [sec113_cardF8, hcard]; norm_num)
  have hpow : σ ^ 16 = 1 := by
    have h := pow_card_eq_one' (x := (⟨σ, hσT⟩ : sec113Tstar hm hTM))
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  obtain ⟨ε, hε, v, hv, hty⟩ := sec113_exists_typeS σ (sec113_Tstar_pres hm hTM hσT) hpow hσF
  have hε' : ε ∈ sec113Tstar hm hTM := by
    rcases Finset.mem_insert.1 hε with rfl | h
    · exact (sec113Tstar hm hTM).one_mem
    · rw [Finset.mem_singleton.1 h]
      exact h01
  exact ⟨ε * σ * v, (sec113Tstar hm hTM).mul_mem ((sec113Tstar hm hTM).mul_mem hε' hσT)
    (sec113_V4_le_Tstar hm hTM hQT v hv), hty⟩

end CFSG.OddStandard.SmallF3.Omega

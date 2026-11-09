module

public import CFSG.Certificates.Kernel.LocalQTChainGSound
public import CFSG.Certificates.Kernel.LocalQTSimsSound
public import Certificates.Data.Kernel.LocalQT.Pairs

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S

variable {n : ℕ}

theorem chainFrom_of (hn : n ≤ 32) (f : ℕ → Bool) : ∀ {prev : List ℕ} {C : List Lvl},
    okFrom n C prev = true → chainInj n C = true → ∀ π : Perm (Fin n),
      (∀ σ, InC n C σ → f (P.code (π * σ)) = true) → chainFrom n C f (P.code π) = true
  | _, [], _, _, π, h => by
    have := h 1 (by simp [InC, sift, P.code_one])
    rw [mul_one] at this
    exact this
  | prev, lv :: C, hok, hI, π, h => by
    have hC := chainP_of (lv :: C) prev hok hI
    have hlv := chainP_lvOK hC lv List.mem_cons_self
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.andB _ (Nat.beq (posMask lv n) _))
      (okFrom n C (lv.1 :: prev)) = true at hok
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (Nat.blt 0 lv.2.2.2)
      (Nat.beq (validCnt n lv.2.1) lv.2.2.2)) (chainInj n C) = true at hI
    rw [P.andB_iff] at hok hI
    change P.allN n (fun j => P.impB (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
      (P.letB (P.mul n (P.code π) (getK lv.2.1 j)) (chainFrom n C f))) = true
    rw [P.allN_iff]
    intro j hj
    rw [P.impB_iff, P.notB_iff, P.beq_iff, P.letB_eq]
    intro e
    obtain ⟨⟨τ, hτ⟩, -⟩ := hlv.2.1 j hj e
    rw [← hτ, P.code_mul hn]
    refine chainFrom_of hn f hok.2 hI.2 (π * τ) fun σ hσ => ?_
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσ
    have := h (τ * σ) (by rw [InC, sift_mul_rep hn hC hj τ hτ e hk]; rfl)
    rwa [← mul_assoc] at this

theorem grpC_of_closure (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) (G G' : List (Perm (Fin n))) {W' : List (List (List ℕ))}
    {d' : ℕ} (h1 : ∀ σ, InC n C σ ↔ σ ∈ Subgroup.closure {g | g ∈ G})
    (hg : P.allL (G'.map P.code) (inC n C (chainF C)) = true)
    (hw : wordsC n C (G'.map P.code) W' d' = true) :
    grpC n C (chainF C) (G'.map P.code) W' d' = true := by
  have hCP := chainP_of_ok hok hI
  have hC := chainP_lvOK hCP
  have hg' : ∀ g ∈ G', InC n C g := fun g hg0 => (inC_iff hn hC g).1 ((P.allL_map G' _).1 hg g hg0)
  unfold grpC
  rw [P.andB_iff, P.andB_iff]
  refine ⟨hg, hw, ?_⟩
  unfold allChain
  rw [P.code_one]
  refine chainFrom_of hn _ (by rw [← chainOK_eq]; exact hok) hI 1 fun σ hσ => ?_
  rw [one_mul, P.allL_map]
  intro g hg0
  rw [P.code_mul hn, inC_iff hn hC, h1]
  exact Subgroup.mul_mem _ ((h1 σ).1 hσ) ((h1 g).1 (hg' g hg0))

theorem exists_map_code : ∀ {G : List ℕ}, P.allL G (P.permK n) = true →
    ∃ L : List (Perm (Fin n)), L.map P.code = G
  | [], _ => ⟨[], rfl⟩
  | g :: G, h => by
    rw [P.allL_iff] at h
    obtain ⟨σ, hσ⟩ := P.exists_of_permK (h g List.mem_cons_self)
    obtain ⟨L, hL⟩ := exists_map_code (G := G)
      ((P.allL_iff _ _).2 fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨σ :: L, by rw [List.map_cons, hσ, hL]⟩

theorem grpC_of_grpS (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) {G : List ℕ} {W : List (List (List ℕ))} {d : ℕ}
    (hp : P.allL G (P.permK n) = true)
    (h : CFSG.KC.LQT.PH.grpS n C (chainF C) G W d = true) :
    grpC n C (chainF C) G W d = true := by
  obtain ⟨L, rfl⟩ := exists_map_code hp
  have h3 := h
  unfold CFSG.KC.LQT.PH.grpS at h3
  rw [P.andB_iff, P.andB_iff] at h3
  exact grpC_of_closure hn hok hI L L (grpS_sound hn hok hI L h).1 h3.1 h3.2.1

theorem nrm_of_gens (hn : n ≤ 32) {C : List Lvl} (hok : chainOK n C = true)
    (hI : chainInj n C = true) {G K L : List ℕ} {W : List (List (List ℕ))} {d : ℕ}
    (hpG : P.allL G (P.permK n) = true) (hpK : P.allL K (P.permK n) = true)
    (hpL : P.allL L (P.permK n) = true) (hS : CFSG.KC.LQT.PH.grpS n C (chainF C) G W d = true)
    (hL : P.allL L (inC n C (chainF C)) = true)
    (h : P.allL G (fun q => P.allL K fun k => CFSG.KC.Ord.andB (inC n C (chainF C) (P.conj n k q))
      (inC n C (chainF C) (CFSG.KC.LQT.Pairs.conjI n k q))) = true) :
    P.allL L (fun q => P.allL K fun k => CFSG.KC.Ord.andB (inC n C (chainF C) (P.conj n k q))
      (inC n C (chainF C) (CFSG.KC.LQT.Pairs.conjI n k q))) = true := by
  obtain ⟨LG, rfl⟩ := exists_map_code hpG
  have hC := chainP_lvOK (chainP_of_ok hok hI)
  have h1 := (grpS_sound hn hok hI LG hS).1
  have hm : ∀ τ : Perm (Fin n), inC n C (chainF C) (P.code τ) = true ↔
      τ ∈ Subgroup.closure {g | g ∈ LG} := fun τ => (inC_iff hn hC τ).trans (h1 τ)
  have hcI : ∀ κ τ : Perm (Fin n), CFSG.KC.LQT.Pairs.conjI n (P.code κ) (P.code τ) =
      P.code (κ⁻¹ * τ * κ) := fun κ τ => by
    rw [CFSG.KC.LQT.Pairs.conjI, P.code_inv hn, P.code_mul hn, P.code_mul hn]
  rw [P.allL_iff]
  intro q hq
  obtain ⟨σ, rfl⟩ := P.exists_of_permK ((P.allL_iff _ _).1 hpL q hq)
  rw [P.allL_iff]
  intro k hk
  obtain ⟨κ, rfl⟩ := P.exists_of_permK ((P.allL_iff _ _).1 hpK k hk)
  have hσ := (hm σ).1 ((P.allL_iff _ _).1 hL _ hq)
  set H := Subgroup.closure {g | g ∈ LG}
  have hle : H ≤ H.comap (MulAut.conj κ).toMonoidHom ⊓ H.comap (MulAut.conj κ⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro g hg
    have hg' := (P.allL_iff _ _).1 ((P.allL_map LG _).1 h g hg) _ hk
    rw [P.andB_iff, P.conj_code hn, hcI, hm, hm] at hg'
    simpa using hg'
  have := hle hσ
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv] at this
  rw [P.andB_iff, P.conj_code hn, hcI, hm, hm]
  exact this

end CFSG.KC.LQT.CM

end

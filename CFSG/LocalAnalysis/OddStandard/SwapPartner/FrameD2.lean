module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.FrameD
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.FrameD2Perm
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.FrameD2Comp
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G} {g : G}

private theorem liftS8_swap01 : liftS8 (swap (0 : Fin 8) 1) = swap (0 : Fin 10) 1 := by
  simpa only [r₁', r₁] using liftS8_r₁'

private theorem liftS8_swap23 : liftS8 (swap (2 : Fin 8) 3) = swap (2 : Fin 10) 3 := by
  simpa using liftS8_swap (2 : Fin 8) (3 : Fin 8)

private theorem liftS8_apply_zero (ρ : Perm (Fin 8)) (h : ρ 0 = 0) :
    liftS8 ρ (0 : Fin 10) = 0 := by
  have happ := Equiv.Perm.viaEmbedding_apply (e := ρ)
    (ι := Fin.castLEEmb (by norm_num : 8 ≤ 10)) (0 : Fin 8)
  rw [liftS8, Equiv.Perm.viaEmbeddingHom_apply]
  rw [show (0 : Fin 10) = (Fin.castLEEmb (by norm_num : 8 ≤ 10)) (0 : Fin 8) from rfl]
  rw [happ, h]

private theorem liftS8_apply_one (ρ : Perm (Fin 8)) (h : ρ 1 = 1) :
    liftS8 ρ (1 : Fin 10) = 1 := by
  have happ := Equiv.Perm.viaEmbedding_apply (e := ρ)
    (ι := Fin.castLEEmb (by norm_num : 8 ≤ 10)) (1 : Fin 8)
  rw [liftS8, Equiv.Perm.viaEmbeddingHom_apply]
  rw [show (1 : Fin 10) = (Fin.castLEEmb (by norm_num : 8 ≤ 10)) (1 : Fin 8) from rfl]
  rw [happ, h]

private theorem cD₀_conj_conj (σ : Perm (Fin 10)) :
    cD₀ * (cD₀ * σ * cD₀⁻¹) * cD₀⁻¹ = σ := by
  calc cD₀ * (cD₀ * σ * cD₀⁻¹) * cD₀⁻¹
      = (cD₀ * cD₀) * σ * (cD₀⁻¹ * cD₀⁻¹) := by group
    _ = σ := by rw [cD₀_mul_self, ← mul_inv_rev, cD₀_mul_self, inv_one, one_mul, mul_one]

private theorem cD₀_conj_mem_stab2 {σ : Perm (Fin 10)} (h0 : σ 0 = 0) (h1 : σ 1 = 1) :
    cD₀ * σ * cD₀⁻¹ ∈ stab2 8 9 := by
  rw [mem_stab2]
  constructor
  · change cD₀ (σ (cD₀⁻¹ 8)) = 8
    rw [show cD₀⁻¹ 8 = 0 by decide, h0, show cD₀ 0 = 8 by decide]
  · change cD₀ (σ (cD₀⁻¹ 9)) = 9
    rw [show cD₀⁻¹ 9 = 1 by decide, h1, show cD₀ 1 = 9 by decide]

private theorem swap01_comm {σ : Perm (Fin 10)} (h0 : σ 0 = 0) (h1 : σ 1 = 1) :
    swap (0 : Fin 10) 1 * σ = σ * swap (0 : Fin 10) 1 := by
  ext i
  by_cases hi0 : i = 0
  · subst hi0
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, h0, h1]
  by_cases hi1 : i = 1
  · subst hi1
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, h0, h1]
  · have hs0 : σ i ≠ 0 := fun h => hi0 (σ.injective (h.trans h0.symm))
    have hs1 : σ i ≠ 1 := fun h => hi1 (σ.injective (h.trans h1.symm))
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hi0 hi1, Equiv.swap_apply_of_ne_of_ne hs0 hs1]

private theorem swap01_conj_eq {σ : Perm (Fin 10)} (h0 : σ 0 = 0) (h1 : σ 1 = 1) :
    swap (0 : Fin 10) 1 * σ * (swap (0 : Fin 10) 1)⁻¹ = σ := by
  rw [swap01_comm h0 h1, mul_assoc, mul_inv_cancel, mul_one]

private theorem swap18_comm_liftS8 (ρ' : Perm (Fin 8)) (hρ'1 : ρ' 1 = 1) :
    swap (1 : Fin 10) 8 * liftS8 ρ' = liftS8 ρ' * swap (1 : Fin 10) 8 := by
  have hdisj : Equiv.Perm.Disjoint (swap (1 : Fin 10) 8) (liftS8 ρ') := by
    intro x
    by_cases hx1 : x = 1
    · subst hx1; right; exact liftS8_apply_one ρ' hρ'1
    by_cases hx8 : x = 8
    · subst hx8; right; exact liftS8_apply_eight ρ'
    · left; exact Equiv.swap_apply_of_ne_of_ne hx1 hx8
  exact hdisj.commute.eq

private theorem q_conj_cπ : swap (1 : Fin 10) 8 * (swap (0 : Fin 10) 1 * τ₀) *
    (swap (1 : Fin 10) 8)⁻¹ = cD₀ := by
  decide

private theorem comm_pow_mul {G : Type} [Group G] {a b : G} (h : a * b = b * a) (n : ℕ) :
    a ^ n * b = b * a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, ← pow_succ]

private theorem pi_data {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G} {g : G}
    (hC : CentData z ι) (hg : GElt z ι g) (hg1 : g * g = 1)
    {d : G} {κ : Perm (Fin 10) →* G} (hκ : CentData d κ)
    (hgd : g * d = d * g) (hSig : ∀ ρ : Perm (Fin 8), g * ι (liftS8 ρ) = ι (liftS8 ρ) * g)
    (hτ : κ τ₀ = z) {s : Perm (Fin 10)} (hs : κ s = ι τ₀)
    (P : Perm (Fin 8) → Prop)
    (hlift : ∀ ρ : Perm (Fin 8), P ρ → κ (liftS8 ρ) = ι (liftS8 ρ)) :
    ∃ (π : Perm (Fin 10)) (ε : G), (ε = 1 ∨ ε = d) ∧ g = ε * κ π ∧
      π * π = 1 ∧ (∀ ρ : Perm (Fin 8), P ρ → π * liftS8 ρ = liftS8 ρ * π) ∧
      π * τ₀ * π⁻¹ = s ∧ π * s * π⁻¹ = τ₀ := by
  classical
  obtain ⟨π, hπ⟩ := hκ.cases g (mem_centralizer_singleton_iff.2 hgd)
  let ε : G := if g = κ π then 1 else d
  have hε : ε = 1 ∨ ε = d := by
    by_cases h : g = κ π <;> simp [ε, h]
  have hε2 : ε * ε = 1 := by
    rcases hε with h | h <;> rw [h] <;> simp [hκ.mul_self]
  have hκπ : κ π = ε * g := by
    by_cases h : g = κ π
    · simp [ε, h]
    · have hd : g = d * κ π := by
        rcases hπ with h' | h'
        · exact absurd h' h
        · exact h'
      rw [show ε = d from by simp [ε, h]]
      rw [hd, ← mul_assoc, hκ.mul_self, one_mul]
  have hπε : ε * g = g * ε := by
    rcases hε with h | h
    · rw [h, one_mul, mul_one]
    · rw [h]; exact hgd.symm
  have hcommκ : ∀ x : Perm (Fin 10), ε * κ x = κ x * ε := by
    rcases hε with h | h <;> intro x
    · rw [h, one_mul, mul_one]
    · rw [h]; exact hκ.comm x
  have hsq : (ε * g) * (ε * g) = 1 := by
    calc (ε * g) * (ε * g) = ε * (g * ε) * g := by group
      _ = ε * (ε * g) * g := by rw [← hπε]
      _ = (ε * ε) * (g * g) := by group
      _ = 1 := by rw [hε2, hg1, one_mul]
  have hπ2 : π * π = 1 := by
    apply hκ.inj
    rw [map_mul, map_one, hκπ]
    exact hsq
  have hπcomm : ∀ ρ : Perm (Fin 8), P ρ → π * liftS8 ρ = liftS8 ρ * π := by
    intro ρ hP
    apply hκ.inj
    rw [map_mul, map_mul]
    have hl : κ (liftS8 ρ) = ι (liftS8 ρ) := hlift ρ hP
    calc κ π * κ (liftS8 ρ) = (ε * g) * κ (liftS8 ρ) := by rw [hκπ]
      _ = ε * (g * κ (liftS8 ρ)) := by group
      _ = ε * (κ (liftS8 ρ) * g) := by rw [hl, hSig ρ]
      _ = (ε * κ (liftS8 ρ)) * g := by group
      _ = (κ (liftS8 ρ) * ε) * g := by rw [hcommκ (liftS8 ρ)]
      _ = κ (liftS8 ρ) * (ε * g) := by group
      _ = κ (liftS8 ρ) * κ π := by rw [hκπ]
  have hτrel : π * τ₀ * π⁻¹ = s := by
    apply hκ.inj
    calc κ (π * τ₀ * π⁻¹) = κ π * κ τ₀ * (κ π)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = (ε * g) * z * (ε * g)⁻¹ := by rw [hκπ, hτ]
      _ = ε * (g * z * g⁻¹) * ε⁻¹ := by group
      _ = ε * (ι τ₀) * ε⁻¹ := by rw [hg.conj_z]
      _ = ε * (κ s) * ε⁻¹ := by rw [hs]
      _ = κ s := by rw [hcommκ s]; group
  have hsrel : π * s * π⁻¹ = τ₀ := by
    apply hκ.inj
    calc κ (π * s * π⁻¹) = κ π * κ s * (κ π)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = (ε * g) * (ι τ₀) * (ε * g)⁻¹ := by rw [hκπ, hs]
      _ = ε * (g * ι τ₀ * g⁻¹) * ε⁻¹ := by group
      _ = ε * z * ε⁻¹ := by rw [hg.conj_x₁]
      _ = ε * κ τ₀ * ε⁻¹ := by rw [hτ]
      _ = κ τ₀ := by rw [hcommκ τ₀]; group
  exact ⟨π, ε, hε, by rw [hκπ, ← mul_assoc, hε2, one_mul], hπ2, hπcomm, hτrel, hsrel⟩

private theorem frame_d_of_pi {G : Type} [Group G] [Finite G] {z : G}
    {ι : Perm (Fin 10) →* G} {g : G} {κ₀ : Perm (Fin 10) →* G} (hκ₀ : CentData (ι (swap 0 1)) κ₀)
    (hκ₀lift : ∀ ρ : Perm (Fin 8), κ₀ (liftS8 ρ) = ι (cD₀ * liftS8 ρ * cD₀⁻¹))
    (hκ₀τ : κ₀ τ₀ = z)
    {π₀ : Perm (Fin 10)} (hπ : π₀ = cD₀ ∨ π₀ = swap 0 9 * swap 1 8)
    (hg : g = κ₀ π₀) :
    ∃ ιd : Perm (Fin 10) →* G, CentData (ι (swap 0 1)) ιd ∧ ιd (swap 0 1) = z ∧
      (∀ σ : Perm (Fin 10), σ 0 = 0 → σ 1 = 1 → ιd σ = ι σ) ∧
      g = ιd (swap 0 8 * swap 1 9) := by
  have hbase : frameConj κ₀ cD₀ (swap 0 1) = z := by
    rw [frameConj_apply, cD₀_conj_swap, hκ₀τ]
  have hagree₁ : ∀ σ : Perm (Fin 10), σ 0 = 0 → σ 1 = 1 → frameConj κ₀ cD₀ σ = ι σ := by
    intro σ h0 h1
    rw [frameConj_apply]
    have hmem : cD₀ * σ * cD₀⁻¹ ∈ stab2 8 9 := cD₀_conj_mem_stab2 h0 h1
    obtain ⟨ρ, hρ⟩ := mem_stab2_iff_exists_liftS8.1 hmem
    rw [← hρ, hκ₀lift ρ, hρ, cD₀_conj_conj]
  rcases hπ with h | h
  · refine ⟨frameConj κ₀ cD₀, centData_comp_conj hκ₀ cD₀, hbase, hagree₁, ?_⟩
    rw [hg, h, frameConj_apply]
    congr 1
    decide
  · refine ⟨frameConj (frameConj κ₀ cD₀) (swap 0 1),
      centData_comp_conj (centData_comp_conj hκ₀ cD₀) (swap 0 1), ?_, ?_, ?_⟩
    · rw [frameConj_apply]
      rw [show (swap (0 : Fin 10) 1) * (swap 0 1) * (swap 0 1)⁻¹ = swap 0 1 by decide]
      exact hbase
    · intro σ h0 h1
      rw [frameConj_apply]
      rw [swap01_conj_eq h0 h1]
      exact hagree₁ σ h0 h1
    · rw [hg, h, frameConj_apply, frameConj_apply]
      rw [show cD₀ * (swap (0 : Fin 10) 1 * (swap 0 8 * swap 1 9) * (swap 0 1)⁻¹) * cD₀⁻¹
            = swap (0 : Fin 10) 9 * swap 1 8 by decide]

private theorem frame_mul_step {G : Type} [Group G] {d0 : G} {ιd : Perm (Fin 10) →* G}
    {X Y : Perm (Fin 10)} (hcomm : d0 * ιd X = ιd X * d0) (n : ℕ) :
    ιd X * (d0 ^ n * ιd Y) = d0 ^ n * ιd (X * Y) := by
  calc ιd X * (d0 ^ n * ιd Y)
      = (ιd X * d0 ^ n) * ιd Y := by group
    _ = (d0 ^ n * ιd X) * ιd Y := by rw [← comm_pow_mul hcomm n]
    _ = d0 ^ n * (ιd X * ιd Y) := by group
    _ = d0 ^ n * ιd (X * Y) := by rw [map_mul]

theorem GElt.exists_frame_at_d_eq (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hp : pairOrder (ι τ₀) (ι (swap 0 1)) = N10 1)
    (hg : GElt z ι g) (hg1 : g * g = 1) :
    ∃ ιd : Perm (Fin 10) →* G, CentData (ι (swap 0 1)) ιd ∧ ιd (swap 0 1) = z ∧
      (∀ σ : Perm (Fin 10), σ 0 = 0 → σ 1 = 1 → ιd σ = ι σ) ∧
      g = ιd (swap 0 8 * swap 1 9) := by
  have hSig : ∀ ρ : Perm (Fin 8), g * ι (liftS8 ρ) = ι (liftS8 ρ) * g :=
    (GElt.pairOrder_eq_N10_one_iff hC hg).1 hp
  obtain ⟨κ₀, hκ₀, hκ₀τ, hκ₀lift, -⟩ := exists_frame_at_conj hC hx hP2 cD₀
  obtain ⟨κ₁, hκ₁, hκ₁τ, hκ₁lift, -⟩ := exists_frame_at_conj hC hx hP2 cD₁
  rw [cD₀_conj_τ₀] at hκ₀
  rw [cD₁_conj_τ₀] at hκ₁
  have hκ₀lift' : ∀ ρ : Perm (Fin 8), κ₀ (liftS8 ρ) = ι (cD₀ * liftS8 ρ * cD₀⁻¹) := hκ₀lift hp
  have hκ₁lift' : ∀ ρ : Perm (Fin 8), κ₁ (liftS8 ρ) = ι (cD₁ * liftS8 ρ * cD₁⁻¹) := hκ₁lift hp
  have hκ₀swap : κ₀ (swap 0 1) = ι τ₀ := by
    have h := hκ₀lift' (swap (0 : Fin 8) 1)
    rwa [liftS8_swap01, cD₀_conj_swap] at h
  have hκ₀s23 : κ₀ (swap 2 3) = ι (swap 2 3) := by
    have h := hκ₀lift' (swap (2 : Fin 8) 3)
    rw [liftS8_swap23] at h
    rw [show cD₀ * swap (2 : Fin 10) 3 * cD₀⁻¹ = swap (2 : Fin 10) 3 by decide] at h
    exact h
  have hκ₁swap01 : κ₁ (swap 0 1) = ι (swap 0 1) := by
    have h := hκ₁lift' (swap (0 : Fin 8) 1)
    rw [liftS8_swap01] at h
    rw [show cD₁ * swap (0 : Fin 10) 1 * cD₁⁻¹ = swap (0 : Fin 10) 1 by decide] at h
    exact h
  have hκ₁swap23 : κ₁ (swap 2 3) = ι τ₀ := by
    have h := hκ₁lift' (swap (2 : Fin 8) 3)
    rw [liftS8_swap23] at h
    rw [show cD₁ * swap (2 : Fin 10) 3 * cD₁⁻¹ = τ₀ by decide] at h
    exact h
  have hlift₀ : ∀ ρ : Perm (Fin 8), ρ 0 = 0 → ρ 1 = 1 → κ₀ (liftS8 ρ) = ι (liftS8 ρ) := by
    intro ρ h0 h1
    rw [hκ₀lift' ρ, ← frameConj_apply ι cD₀ (liftS8 ρ),
      frameConj_cD₀_liftS8_of_fixed ι h0 h1]
  have hlift₁ : ∀ ρ : Perm (Fin 8), ρ 2 = 2 → ρ 3 = 3 → κ₁ (liftS8 ρ) = ι (liftS8 ρ) := by
    intro ρ h2 h3
    rw [hκ₁lift' ρ, ← frameConj_apply ι cD₁ (liftS8 ρ),
      frameConj_cD₁_liftS8_of_fixed ι h2 h3]
  have hgd₀ : g * ι (swap 0 1) = ι (swap 0 1) * g := by
    simpa only [liftS8_swap01] using hSig (swap (0 : Fin 8) 1)
  have hgd₁ : g * ι (swap 2 3) = ι (swap 2 3) * g := by
    simpa only [liftS8_swap23] using hSig (swap (2 : Fin 8) 3)
  obtain ⟨π₀, ε₀, hε₀, hgπ₀, hπ₀sq, hπ₀comm, hπ₀τ, hπ₀s⟩ :=
    pi_data hC hg hg1 hκ₀ hgd₀ hSig hκ₀τ hκ₀swap (fun ρ => ρ 0 = 0 ∧ ρ 1 = 1)
      (fun ρ hP => hlift₀ ρ hP.1 hP.2)
  obtain ⟨π₁, ε₁, hε₁, hgπ₁, hπ₁sq, hπ₁comm, hπ₁τ, hπ₁s⟩ :=
    pi_data hC hg hg1 hκ₁ hgd₁ hSig hκ₁τ hκ₁swap23 (fun ρ => ρ 2 = 2 ∧ ρ 3 = 3)
      (fun ρ hP => hlift₁ ρ hP.1 hP.2)
  have hπ₀cls : π₀ = cD₀ ∨ π₀ = swap 0 9 * swap 1 8 :=
    eq_cD₀_or_of_commutes π₀ hπ₀sq (fun ρ h0 h1 => hπ₀comm ρ ⟨h0, h1⟩) hπ₀τ hπ₀s
  have hπ₁cls : π₁ = cD₁ ∨ π₁ = swap 2 9 * swap 3 8 :=
    eq_cD₁_or_of_commutes π₁ hπ₁sq (fun ρ h2 h3 => hπ₁comm ρ ⟨h2, h3⟩) hπ₁τ hπ₁s
  have hπ₀23 : π₀ 2 = 2 ∧ π₀ 3 = 3 := by
    refine ⟨?_, ?_⟩ <;> rcases hπ₀cls with h | h <;> rw [h] <;> decide
  have hπ₁fac : ∃ t₁ t₂ ρ : Perm (Fin 10), π₁ = t₁ * t₂ ∧ ρ * t₁ * ρ⁻¹ = t₂ ∧
      t₁ 0 = 0 ∧ t₁ 1 = 1 ∧ t₂ 0 = 0 ∧ t₂ 1 = 1 ∧ ρ 0 = 0 ∧ ρ 1 = 1 :=
    exists_double_transposition_factors π₁ hπ₁cls
  have hε₀eq : ε₀ = 1 :=
    eq_one_of_two_frames hκ₀ hκ₁ hκ₁swap01 hκ₀s23 hπ₀23 hπ₁fac hε₀ hε₁ (by rw [← hgπ₀, hgπ₁])
  have hg_eq : g = κ₀ π₀ := by rw [hgπ₀, hε₀eq, one_mul]
  obtain ⟨ιd, hCd, hd, hagree, hgeq⟩ := frame_d_of_pi hκ₀ hκ₀lift' hκ₀τ hπ₀cls hg_eq
  exact ⟨ιd, hCd, hd, hagree, hgeq⟩

theorem exists_frame_at_d_of_pairOrder_N10_one (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hp : pairOrder (ι τ₀) (ι (swap 0 1)) = N10 1) :
    ∃ ιd : Perm (Fin 10) →* G, CentData (ι (swap 0 1)) ιd ∧ ιd (swap 0 1) = z ∧
      (∀ σ : Perm (Fin 10), σ 0 = 0 → σ 1 = 1 → ιd σ = ι σ) ∧
      ∀ ρ : Perm (Fin 8), ιd (swap 0 8 * swap 1 9) * ι (liftS8 ρ) =
        ι (liftS8 ρ) * ιd (swap 0 8 * swap 1 9) := by
  obtain ⟨g, hg, hg1⟩ := exists_gElt_sq_one hC hx hP2
  obtain ⟨ιd, hCd, hd, hagree, hge⟩ := GElt.exists_frame_at_d_eq hC hx hP2 hp hg hg1
  refine ⟨ιd, hCd, hd, hagree, fun ρ => ?_⟩
  rw [← hge]
  exact (GElt.pairOrder_eq_N10_one_iff hC hg).1 hp ρ

theorem isConj_gElt_mul_of_pairOrder_N10_one (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hp : pairOrder (ι τ₀) (ι (swap 0 1)) = N10 1)
    (hg : GElt z ι g) (hg1 : g * g = 1) {ρ : Perm (Fin 8)} (hρ : ρ * ρ = 1) :
    IsConj (z * ι τ₀ * ι (liftS8 ρ)) (g * ι (liftS8 ρ)) := by
  obtain ⟨ιd, hCd, hd01, hagree, hge⟩ := GElt.exists_frame_at_d_eq hC hx hP2 hp hg hg1
  have hSig : ∀ ρ : Perm (Fin 8), g * ι (liftS8 ρ) = ι (liftS8 ρ) * g :=
    (GElt.pairOrder_eq_N10_one_iff hC hg).1 hp
  obtain ⟨s, ρ', ε, hρ'2, hρ'0, hρ'1, hsρ⟩ := exists_conj_normal_form ρ hρ
  have hfix0 : liftS8 ρ' (0 : Fin 10) = 0 := liftS8_apply_zero ρ' hρ'0
  have hfix1 : liftS8 ρ' (1 : Fin 10) = 1 := liftS8_apply_one ρ' hρ'1
  have hdρ' : ι (liftS8 ρ') = ιd (liftS8 ρ') := (hagree (liftS8 ρ') hfix0 hfix1).symm
  have hτf0 : τ₀ (0 : Fin 10) = 0 := by decide
  have hτf1 : τ₀ (1 : Fin 10) = 1 := by decide
  have hdτ : ι τ₀ = ιd τ₀ := (hagree τ₀ hτf0 hτf1).symm
  have hzx2 : z * ι τ₀ = ιd (swap 0 1 * τ₀) := by
    calc z * ι τ₀ = ιd (swap 0 1) * ιd τ₀ := by rw [← hd01, hdτ]
      _ = ιd (swap 0 1 * τ₀) := by rw [map_mul]
  have hzt : z * ι (liftS8 s) = ι (liftS8 s) * z := hC.comm (liftS8 s)
  have hτt : ι τ₀ * ι (liftS8 s) = ι (liftS8 s) * ι τ₀ := by
    rw [← map_mul, ← map_mul, liftS8_mul_τ₀ s]
  have hzt_conj : ι (liftS8 s) * z * (ι (liftS8 s))⁻¹ = z := by
    rw [show ι (liftS8 s) * z = z * ι (liftS8 s) from hzt.symm, mul_assoc, mul_inv_cancel, mul_one]
  have hτt_conj : ι (liftS8 s) * ι τ₀ * (ι (liftS8 s))⁻¹ = ι τ₀ := by
    rw [show ι (liftS8 s) * ι τ₀ = ι τ₀ * ι (liftS8 s) from hτt.symm, mul_assoc,
      mul_inv_cancel, mul_one]
  have ht_x2 : ι (liftS8 s) * (z * ι τ₀) * (ι (liftS8 s))⁻¹ = z * ι τ₀ := by
    calc ι (liftS8 s) * (z * ι τ₀) * (ι (liftS8 s))⁻¹
        = (ι (liftS8 s) * z * (ι (liftS8 s))⁻¹) *
          (ι (liftS8 s) * ι τ₀ * (ι (liftS8 s))⁻¹) := by group
      _ = z * ι τ₀ := by rw [hzt_conj, hτt_conj]
  have ht_ρ : ι (liftS8 s) * ι (liftS8 ρ) * (ι (liftS8 s))⁻¹ =
      ι (liftS8 (s * ρ * s⁻¹)) := by
    calc ι (liftS8 s) * ι (liftS8 ρ) * (ι (liftS8 s))⁻¹
        = ι (liftS8 s * liftS8 ρ * (liftS8 s)⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = ι (liftS8 s * liftS8 ρ * liftS8 s⁻¹) := by rw [map_inv]
      _ = ι (liftS8 (s * ρ * s⁻¹)) := by rw [← map_mul, ← map_mul]
  have ht_g : ι (liftS8 s) * g * (ι (liftS8 s))⁻¹ = g := by
    rw [show ι (liftS8 s) * g = g * ι (liftS8 s) from (hSig s).symm, mul_assoc,
      mul_inv_cancel, mul_one]
  have hM : ι (liftS8 (s * ρ * s⁻¹)) = (ι (swap 0 1)) ^ (ε : ℕ) * ιd (liftS8 ρ') := by
    calc ι (liftS8 (s * ρ * s⁻¹))
        = ι (liftS8 (swap 0 1 ^ (ε : ℕ) * ρ')) := by rw [hsρ]
      _ = ι (liftS8 (swap 0 1 ^ (ε : ℕ)) * liftS8 ρ') := by rw [map_mul]
      _ = ι ((liftS8 (swap 0 1)) ^ (ε : ℕ) * liftS8 ρ') := by rw [map_pow]
      _ = ι ((swap 0 1 : Perm (Fin 10)) ^ (ε : ℕ) * liftS8 ρ') := by rw [liftS8_swap01]
      _ = (ι (swap 0 1)) ^ (ε : ℕ) * ι (liftS8 ρ') := by rw [map_mul, map_pow]
      _ = (ι (swap 0 1)) ^ (ε : ℕ) * ιd (liftS8 ρ') := by rw [hdρ']
  have hA' : ι (liftS8 s) * (z * ι τ₀ * ι (liftS8 ρ)) * (ι (liftS8 s))⁻¹ =
      (ι (swap 0 1)) ^ (ε : ℕ) * ιd (swap 0 1 * τ₀ * liftS8 ρ') := by
    calc ι (liftS8 s) * (z * ι τ₀ * ι (liftS8 ρ)) * (ι (liftS8 s))⁻¹
        = (ι (liftS8 s) * (z * ι τ₀) * (ι (liftS8 s))⁻¹) *
          (ι (liftS8 s) * ι (liftS8 ρ) * (ι (liftS8 s))⁻¹) := by group
      _ = (z * ι τ₀) * ι (liftS8 (s * ρ * s⁻¹)) := by rw [ht_x2, ht_ρ]
      _ = ιd (swap 0 1 * τ₀) * ((ι (swap 0 1)) ^ (ε : ℕ) * ιd (liftS8 ρ')) := by
            rw [hzx2, hM]
      _ = (ι (swap 0 1)) ^ (ε : ℕ) * ιd ((swap 0 1 * τ₀) * liftS8 ρ') :=
            frame_mul_step (hCd.comm (swap 0 1 * τ₀)) (ε : ℕ)
  have hB' : ι (liftS8 s) * (g * ι (liftS8 ρ)) * (ι (liftS8 s))⁻¹ =
      (ι (swap 0 1)) ^ (ε : ℕ) * ιd (cD₀ * liftS8 ρ') := by
    calc ι (liftS8 s) * (g * ι (liftS8 ρ)) * (ι (liftS8 s))⁻¹
        = (ι (liftS8 s) * g * (ι (liftS8 s))⁻¹) *
          (ι (liftS8 s) * ι (liftS8 ρ) * (ι (liftS8 s))⁻¹) := by group
      _ = g * ι (liftS8 (s * ρ * s⁻¹)) := by rw [ht_g, ht_ρ]
      _ = ιd (swap 0 8 * swap 1 9) * ((ι (swap 0 1)) ^ (ε : ℕ) * ιd (liftS8 ρ')) := by
            rw [hge, hM]
      _ = (ι (swap 0 1)) ^ (ε : ℕ) * ιd (cD₀ * liftS8 ρ') :=
            frame_mul_step (hCd.comm cD₀) (ε : ℕ)
  have hq_ρ' : swap (1 : Fin 10) 8 * liftS8 ρ' = liftS8 ρ' * swap (1 : Fin 10) 8 :=
    swap18_comm_liftS8 ρ' hρ'1
  have hq_ρ'_conj : swap (1 : Fin 10) 8 * liftS8 ρ' * (swap (1 : Fin 10) 8)⁻¹ =
      liftS8 ρ' := by
    rw [hq_ρ', mul_assoc, mul_inv_cancel, mul_one]
  have hqπx : swap (1 : Fin 10) 8 * (swap 0 1 * τ₀ * liftS8 ρ') *
      (swap (1 : Fin 10) 8)⁻¹ = cD₀ * liftS8 ρ' := by
    calc swap (1 : Fin 10) 8 * (swap 0 1 * τ₀ * liftS8 ρ') * (swap (1 : Fin 10) 8)⁻¹
        = (swap (1 : Fin 10) 8 * (swap 0 1 * τ₀) * (swap (1 : Fin 10) 8)⁻¹) *
          (swap (1 : Fin 10) 8 * liftS8 ρ' * (swap (1 : Fin 10) 8)⁻¹) := by group
      _ = cD₀ * liftS8 ρ' := by rw [q_conj_cπ, hq_ρ'_conj]
  have hCM : ιd (swap (1 : Fin 10) 8) *
      ((ι (swap 0 1)) ^ (ε : ℕ) * ιd (swap 0 1 * τ₀ * liftS8 ρ')) *
      (ιd (swap (1 : Fin 10) 8))⁻¹ =
      (ι (swap 0 1)) ^ (ε : ℕ) * ιd (cD₀ * liftS8 ρ') := by
    calc ιd (swap (1 : Fin 10) 8) *
          ((ι (swap 0 1)) ^ (ε : ℕ) * ιd (swap 0 1 * τ₀ * liftS8 ρ')) *
          (ιd (swap (1 : Fin 10) 8))⁻¹
        = (ιd (swap (1 : Fin 10) 8) * (ι (swap 0 1)) ^ (ε : ℕ)) *
          ιd (swap 0 1 * τ₀ * liftS8 ρ') * (ιd (swap (1 : Fin 10) 8))⁻¹ := by group
      _ = ((ι (swap 0 1)) ^ (ε : ℕ) * ιd (swap (1 : Fin 10) 8)) *
          ιd (swap 0 1 * τ₀ * liftS8 ρ') * (ιd (swap (1 : Fin 10) 8))⁻¹ := by
            rw [← comm_pow_mul (hCd.comm (swap (1 : Fin 10) 8)) (ε : ℕ)]
      _ = (ι (swap 0 1)) ^ (ε : ℕ) *
          (ιd (swap (1 : Fin 10) 8) * ιd (swap 0 1 * τ₀ * liftS8 ρ') *
            (ιd (swap (1 : Fin 10) 8))⁻¹) := by group
      _ = (ι (swap 0 1)) ^ (ε : ℕ) * ιd (swap (1 : Fin 10) 8 *
            (swap 0 1 * τ₀ * liftS8 ρ') * (swap (1 : Fin 10) 8)⁻¹) := by
            rw [← map_mul, ← map_inv, ← map_mul]
      _ = (ι (swap 0 1)) ^ (ε : ℕ) * ιd (cD₀ * liftS8 ρ') := by rw [hqπx]
  refine (isConj_iff.2 ⟨ι (liftS8 s), hA'⟩).trans ?_
  refine (isConj_iff.2 ⟨ιd (swap (1 : Fin 10) 8), hCM⟩).trans ?_
  exact (isConj_iff.2 ⟨ι (liftS8 s), hB'⟩).symm

theorem GElt.not_isConj_z_of_pairOrder_N10_one (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hp : pairOrder (ι τ₀) (ι (swap 0 1)) = N10 1)
    (hg : GElt z ι g) : ¬ IsConj z g := by
  intro hconj
  have hg1 : g * g = 1 := mul_self_of_isConj hC hconj
  have hcx2 : IsConj (z * ι τ₀) g := by
    have h := isConj_gElt_mul_of_pairOrder_N10_one hC hx hP2 hp hg hg1
      (ρ := (1 : Perm (Fin 8))) (by rw [mul_one])
    simpa using h
  exact hP2 (hconj.trans hcx2.symm)

end CFSG.OddStandard.AltStdSec.SwapPartner

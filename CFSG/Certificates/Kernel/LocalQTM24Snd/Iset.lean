module

public import CFSG.Certificates.Kernel.LocalQTM24Snd.HashC
public import CFSG.Certificates.Kernel.LocalQTM24Snd.IsetL
public import CFSG.Certificates.Kernel.LocalQTM24Snd.IsetG
public import CFSG.Certificates.Kernel.LocalQTM24Snd.IsetS
public import CFSG.Certificates.Kernel.LocalQTM24Snd.IsetY

public section

namespace CFSG.KC.LQT.M24Snd

open Equiv CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.KC.LQT.W CFSG.KC.LQT.M24

variable {n : ℕ}

theorem conjBfs_ball (gs : List (Perm (Fin n))) (g0 g1 g2 g3 : Perm (Fin n))
    (pW : List (List ℕ)) (d r : ℕ) :
    (∀ σ : Perm (Fin n), RN.enc σ ∈ conjBfs (RN.enc g0) (RN.enc g1) (RN.enc g2) (RN.enc g3)
        (invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d)) r ↔
      σ ∈ ball (conjP g0 g1 g2 g3)
        {σ | σ ∈ ball (fun σ => (pW.map (evalW gs)).map (σ * ·)) {1} d ∧ σ * σ = 1 ∧ σ ≠ 1} r) ∧
    ∀ x ∈ conjBfs (RN.enc g0) (RN.enc g1) (RN.enc g2) (RN.enc g3)
        (invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d)) r,
      ∃ σ : Perm (Fin n), RN.enc σ = x := by
  have himg : RN.enc '' ball (conjP g0 g1 g2 g3)
      {σ | σ ∈ ball (fun σ => (pW.map (evalW gs)).map (σ * ·)) {1} d ∧ σ * σ = 1 ∧ σ ≠ 1} r =
      ball (conjF (RN.enc g0) (RN.enc g1) (RN.enc g2) (RN.enc g3))
        {y | y ∈ invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d)} r := by
    refine ball_image RN.enc (fun σ => ?_) ?_ r
    · simp only [conjP, conjF, List.map_cons, List.map_nil, RN.enc_mul]
    · ext y
      rw [Set.mem_image, Set.mem_setOf_eq, mem_invSeeds_iff]
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        exact ⟨σ, rfl, hσ.1, hσ.2.1, hσ.2.2⟩
      · rintro ⟨σ, rfl, h1, h2, h3⟩
        exact ⟨σ, ⟨h1, h2, h3⟩, rfl⟩
  refine ⟨fun σ => ?_, fun x hx => ?_⟩
  · rw [mem_conjBfs_iff, ← himg]
    exact ⟨fun ⟨τ, hτ, e⟩ => by rwa [← RN.enc_inj e], fun h => ⟨σ, h, rfl⟩⟩
  · rw [mem_conjBfs_iff, ← himg] at hx
    obtain ⟨τ, -, e⟩ := hx
    exact ⟨τ, e⟩

theorem iset_snd (hn : n ≤ 32) (gs : List (Perm (Fin n))) (g0 g1 g2 g3 : Perm (Fin n))
    (pW : List (List ℕ)) (d r : ℕ) (xW : List ℕ) (c1 c2 c3 c4 c5 : ECert) (Els : List (List ℕ))
    (S : List ℕ) (chs hss : List (List ℕ))
    (hes : allZ [c1.eW, c2.eW, c3.eW, c4.eW, c5.eW] Els (esK n (gs.map codeP)) = true)
    (hpre : isetPre n (gs.map codeP) pW d S = true) (hin : isetIn S chs.flatten = true)
    (hlen : chs.length = hss.length)
    (hch : ∀ j < chs.length, isetChunk n (codeP g0) (codeP g1) (codeP g2) (codeP g3) S r
      (evalWK n (gs.map codeP) xW) Els chs.flatten (chs.getD j []) (hss.getD j []) = true) :
    conjClosed (RN.enc g0) (RN.enc g1) (RN.enc g2) (RN.enc g3) (conjBfs (RN.enc g0) (RN.enc g1)
        (RN.enc g2) (RN.enc g3) (invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d)) r) = true ∧
      (invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d)).all (fun x => (conjBfs (RN.enc g0)
        (RN.enc g1) (RN.enc g2) (RN.enc g3)
        (invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d)) r).contains x) = true ∧
      (conjBfs (RN.enc g0) (RN.enc g1) (RN.enc g2) (RN.enc g3)
        (invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d)) r).toList.all
        (yCheck (evalW (gs.map RN.enc) xW) (c1.Es (gs.map RN.enc)) (c2.Es (gs.map RN.enc))
          (c3.Es (gs.map RN.enc)) (c4.Es (gs.map RN.enc)) (c5.Es (gs.map RN.enc))) = true := by
  have hcP : (codeP : Perm (Fin n) → ℕ) = P.code := rfl
  rw [hcP] at hch hes hpre
  obtain ⟨he1, he2, he3, he4⟩ := iset_entries n (P.code g0) (P.code g1) (P.code g2) (P.code g3) S r
    (evalWK n (gs.map P.code) xW) Els chs hss hin hlen hch
  obtain ⟨hS1, hS2⟩ := iset_seeds hn gs pW d S hpre
  have hseeds : ∀ σ : Perm (Fin n),
      σ ∈ {σ : Perm (Fin n) | σ ∈ ball (fun σ => (pW.map (evalW gs)).map (σ * ·)) {1} d ∧
        σ * σ = 1 ∧ σ ≠ 1} ↔ P.code σ ∈ S := fun σ => (hS1 σ).symm
  obtain ⟨hI1, hI2⟩ := iset_set hn g0 g1 g2 g3 S chs.flatten r _ hseeds hS2 he1 he2 he3
  obtain ⟨hB1, hB2⟩ := conjBfs_ball gs g0 g1 g2 g3 pW d r
  refine ⟨?_, ?_, ?_⟩
  · simp only [conjClosed, List.all_eq_true, Bool.and_eq_true, Std.HashSet.mem_toList,
      Std.HashSet.contains_iff_mem]
    intro x hx
    obtain ⟨σ, rfl⟩ := hB2 x hx
    have hσ := (hB1 σ).1 hx
    obtain ⟨e, he, hec⟩ := List.mem_map.1 ((hI1 σ).2 hσ)
    have key : ∀ τ ∈ conjP g0 g1 g2 g3 σ, RN.enc τ ∈ conjBfs (RN.enc g0) (RN.enc g1) (RN.enc g2)
        (RN.enc g3) (invSeeds (bfsSet (pW.map (evalW (gs.map RN.enc))) d)) r := by
      intro τ hτ
      rw [hB1 τ, ← hI1 τ]
      apply he2 e he (P.code τ)
      rw [hec, cimgK_code hn]
      exact List.mem_map_of_mem hτ
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · have := key (g0 * σ * g2) (by simp [conjP])
      rwa [RN.enc_mul, RN.enc_mul] at this
    · have := key (g1 * σ * g3) (by simp [conjP])
      rwa [RN.enc_mul, RN.enc_mul] at this
    · have := key (g2 * σ * g0) (by simp [conjP])
      rwa [RN.enc_mul, RN.enc_mul] at this
    · have := key (g3 * σ * g1) (by simp [conjP])
      rwa [RN.enc_mul, RN.enc_mul] at this
  · simp only [List.all_eq_true, Std.HashSet.contains_iff_mem]
    intro x hx
    obtain ⟨σ, rfl, h1, h2, h3⟩ := (mem_invSeeds_iff gs pW d x).1 hx
    rw [hB1 σ]
    exact ball_mono (Nat.zero_le r) (mem_ball_zero ⟨h1, h2, h3⟩)
  · simp only [List.all_eq_true, Std.HashSet.mem_toList]
    intro x hx
    obtain ⟨σ, rfl⟩ := hB2 x hx
    have hσ := (hB1 σ).1 hx
    obtain ⟨e, he, hec⟩ := List.mem_map.1 ((hI1 σ).2 hσ)
    have hy := he4 e he
    rw [hec] at hy
    exact ycK_sound hn gs xW c1 c2 c3 c4 c5 Els (by rw [hcP]; exact hes) σ (by rw [hcP]; exact hy)

end CFSG.KC.LQT.M24Snd

end

module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36HS2B
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.HSCoverMain
public import CFSG.Sporadic.SmallOddCore.HSLocal

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

namespace HS2B

open CFSG Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier

theorem t2_facts :
    hsT2 ∈ hsP ∧ orderOf hsT2 = 2 := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨-, ho, hout, -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only at ho hout
  simp only [Bool.false_eq_true, false_iff, not_not] at hout
  exact ⟨hout, ho⟩

theorem t2_mul_self :
    hsT2 * hsT2 = 1 := by
  have h1 : hsT2 ^ orderOf hsT2 = 1 := pow_orderOf_eq_one _
  rw [t2_facts.2, sq] at h1
  exact h1

theorem t2_mem :
    hsT2 ∈ hsP := t2_facts.1

theorem mul_self_eq_of_twoB
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {t : L}
    (ht : orderOf t = 2) (htc : t ∈ center L) (ρ : L →* hsP)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = zpowers t) {W : L} {g : Equiv.Perm (Fin 3850)}
    (hg : g ∈ hsP) (hW : ((ρ W : hsP) : Equiv.Perm (Fin 3850)) = g * hsT2 * g⁻¹) :
    W * W = t := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have hPP : CFSG.QuasithinUnique.Id2519.UHS.PP = hsP := hsP_eq_original.symm
  have hWW : W * W ∈ zpowers t := by
    rw [← hker, MonoidHom.mem_ker]
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, hW, Subgroup.coe_one]
    calc g * hsT2 * g⁻¹ * (g * hsT2 * g⁻¹) = g * (hsT2 * hsT2) * g⁻¹ := by group
      _ = 1 := by rw [t2_mul_self]; group
  rcases HS2B.eq_one_or_eq_of_mem_zpowers ht2 hWW with h | h
  · exfalso
    have hker' : ∀ e, ((ρ e : hsP) : Equiv.Perm (Fin 3850)) = 1 → e = 1 ∨ e = t := by
      intro e he
      have h2 : e ∈ zpowers t := by
        rw [← hker, MonoidHom.mem_ker]
        exact Subtype.ext he
      exact HS2B.eq_one_or_eq_of_mem_zpowers ht2 h2
    have hιt : ((ρ t : hsP) : Equiv.Perm (Fin 3850)) = 1 := by
      have : t ∈ ρ.ker := hker ▸ mem_zpowers t
      rw [MonoidHom.mem_ker.mp this, Subgroup.coe_one]
    let X : CFSG.QuasithinUnique.Ch1.M22Cover.CentralExt L (Equiv.Perm (Fin 3850)) :=
      { φ := hsP.subtype.comp ρ, ζ := t, φ_ζ := hιt, ne_one := ht1, sq := ht2,
        central := fun e => (mem_center_iff.mp htc e).symm, ker := hker' }
    have hφ : ∀ e, X.φ e = ((ρ e : hsP) : Equiv.Perm (Fin 3850)) := fun e => rfl
    have hrange : ∀ y ∈ CFSG.QuasithinUnique.Id2519.UHS.PP, ∃ e, X.φ e = y := by
      intro y hy
      rw [hPP] at hy
      obtain ⟨e, he⟩ := hρ ⟨y, hy⟩
      exact ⟨e, by rw [hφ, he]⟩
    have hφmem : ∀ e, X.φ e ∈ CFSG.QuasithinUnique.Id2519.UHS.PP := fun e => by
      rw [hPP, hφ]
      exact (ρ e).2
    obtain ⟨-, hDcard, hDC2, -, -⟩ := hs_D_facts
    have hDPP : genGroup 3850 hsDGens hsDPerm ≤ CFSG.QuasithinUnique.Id2519.UHS.PP := by
      rw [hPP]
      exact hDC2.trans inf_le_left
    have hK : Nat.card ((genGroup 3850 hsDGens hsDPerm).subgroupOf
        CFSG.QuasithinUnique.Id2519.UHS.PP) = 360 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hDPP).toEquiv, hDcard]
    have hT2PP : hsT2 ∈ CFSG.QuasithinUnique.Id2519.UHS.PP := hPP ▸ t2_mem
    have hT2ne : hsT2 ≠ 1 := fun h1 => by
      have h0 := t2_facts.2
      rw [h1, orderOf_one] at h0
      exact absurd h0 (by norm_num)
    obtain ⟨d, hd, hdc⟩ := CFSG.QuasithinUnique.Ch1.HSCover.exists_conj_hsC ⟨hsT2, hT2PP⟩
      (Subtype.ext t2_mul_self) (fun h1 => hT2ne (congrArg Subtype.val h1))
      ((genGroup 3850 hsDGens hsDPerm).subgroupOf CFSG.QuasithinUnique.Id2519.UHS.PP) hK
      (fun k hk => by
        apply Subtype.ext
        have hkD : (k : Equiv.Perm (Fin 3850)) ∈ genGroup 3850 hsDGens hsDPerm :=
          mem_subgroupOf.mp hk
        have h2 := (mem_inf.mp (hDC2 hkD)).2
        rw [mem_centralizer_singleton_iff] at h2
        exact h2)
    have hcc : CFSG.QuasithinUnique.Id2519.UHS.hsC = CFSG.QuasithinUnique.Ch1.HSCover.cElt := by
      rw [CFSG.QuasithinUnique.Ch1.HSCover.cElt_eq]
      rfl
    have hdc' : CFSG.QuasithinUnique.Ch1.HSCover.cElt = d⁻¹ * hsT2 * d := by
      rw [← hcc]
      have h1 : hsT2 = d * CFSG.QuasithinUnique.Id2519.UHS.hsC * d⁻¹ := hdc
      rw [h1]
      group
    obtain ⟨G, hG⟩ := hrange (g * d) (CFSG.QuasithinUnique.Id2519.UHS.PP.mul_mem (hPP ▸ hg) hd)
    refine CFSG.QuasithinUnique.Ch1.HSCover.hs_no_involution_over_c X hrange hφmem
      (G⁻¹ * W * G) ?_ ?_
    · calc G⁻¹ * W * G * (G⁻¹ * W * G) = G⁻¹ * (W * W) * G := by group
        _ = 1 := by rw [h]; group
    · rw [map_mul, map_mul, map_inv, hG, hφ W, hW, hdc']
      group
  · exact h

theorem twoHSTwoBFact_holds :
    TwoHSTwoBFact := by
  intro Y _ _ hq ⟨e⟩ hZ2 τ hτ hinn K hK hKm
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect Y := hq.1
  let ψ : Y ⧸ center Y ≃* hsP := e.trans hsPermEquiv
  let ρ : Y →* hsP := ψ.toMonoidHom.comp (QuotientGroup.mk' (center Y))
  have hρs : Function.Surjective ρ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ∀ y, ρ y = 1 ↔ y ∈ center Y := by
    intro y
    change ψ (QuotientGroup.mk' (center Y) y) = 1 ↔ _
    rw [map_eq_one_iff _ ψ.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨t, htZ, ht1, hZt⟩ : ∃ t ∈ center Y, t ≠ 1 ∧ ∀ z ∈ center Y, z = 1 ∨ z = t := by
    rw [Nat.card_eq_two_iff' (1 : center Y)] at hZ2
    obtain ⟨y, hy, huniq⟩ := hZ2
    refine ⟨y, y.2, fun h => hy (Subtype.ext h), fun z hz => ?_⟩
    by_cases hz1 : z = 1
    · exact Or.inl hz1
    · exact Or.inr (congrArg Subtype.val (huniq ⟨z, hz⟩ fun h => hz1 (congrArg Subtype.val h)))
  have ht2 : t * t = 1 := by
    rcases hZt (t * t) (mul_mem htZ htZ) with h | h
    · exact h
    · exfalso
      apply ht1
      calc t = t * t * t⁻¹ := by group
        _ = 1 := by rw [h, mul_inv_cancel]
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have hZeq : center Y = zpowers t := by
    apply le_antisymm
    · intro z hz
      rcases hZt z hz with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact mem_zpowers t
    · rw [zpowers_le]
      exact htZ
  have hker : ∀ y, ρ y = 1 → y = 1 ∨ y = t := fun y hy => hZt y ((hρk y).mp hy)
  obtain ⟨W, rfl⟩ := hinn
  rw [← Hin.centralizer_eq_fixedPoints_conj W] at hK ⊢
  have hWWc : W * W ∈ center Y := by
    have h1 : MulAut.conj (W * W) = 1 := by rw [map_mul, ← sq, ← hτ, pow_orderOf_eq_one]
    rw [mem_center_iff]
    intro g
    have h2 : W * W * g * (W * W)⁻¹ = g := by
      have := congrArg (fun φ : MulAut Y => φ g) h1
      simpa only [MulAut.conj_apply, MulAut.one_apply] using this
    calc g * (W * W) = W * W * g * (W * W)⁻¹ * (W * W) := by rw [h2]
      _ = W * W * g := by group
  have hWnc : W ∉ center Y := by
    intro hW
    have h1 : MulAut.conj W = 1 := by
      ext g
      rw [MulAut.conj_apply, MulAut.one_apply, ← mem_center_iff.mp hW g, mul_inv_cancel_right]
    rw [h1, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have hw2 : orderOf ((ρ W : hsP) : Equiv.Perm (Fin 3850)) = 2 := by
    rw [Subgroup.orderOf_coe]
    refine orderOf_eq_prime ?_ fun h => hWnc ((hρk W).mp h)
    rw [sq, ← map_mul]
    exact (hρk _).mpr hWWc
  obtain ⟨r, hr, g, hg, hwg⟩ := hs_reps.2.2.2.2 _ (ρ W).2 hw2
  let ρg : Y →* Equiv.Perm (Fin 3850) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (hsP.subtype.comp ρ)
  have hρg : ∀ y, ρg y = g⁻¹ * ((ρ y : hsP) : Equiv.Perm (Fin 3850)) * g := by
    intro y
    change g⁻¹ * ((ρ y : hsP) : Equiv.Perm (Fin 3850)) * g⁻¹⁻¹ = _
    rw [inv_inv]
  have hρgW : ρg W = r := by
    rw [hρg, hwg]
    group
  have hρgker : ∀ y, ρg y = 1 → y = 1 ∨ y = t := by
    intro y hy
    apply hker
    apply Subtype.ext
    rw [hρg] at hy
    rw [Subgroup.coe_one]
    calc ((ρ y : hsP) : Equiv.Perm (Fin 3850)) =
        g * (g⁻¹ * ((ρ y : hsP) : Equiv.Perm (Fin 3850)) * g) * g⁻¹ := by group
      _ = 1 := by rw [hy]; group
  have hρgC : ∀ c ∈ centralizer ({W} : Set Y),
      ρg c ∈ hsP ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 3850))) := by
    intro c hc
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [hρg]
      exact hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) (ρ c).2) hg
    · rw [mem_centralizer_singleton_iff, ← hρgW, ← map_mul, ← map_mul,
        mem_centralizer_singleton_iff.mp hc]
  have hKcard := card_eq_of_lieModel hKm
  rcases hr with rfl | rfl
  ·
    exfalso
    have h1 := card_dvd_two_mul_of_map_le ht2 ρg hρgker
      (M := hsP ⊓ centralizer ({hsT1} : Set (Equiv.Perm (Fin 3850))))
      fun k hk => hρgC k (hK.1 hk)
    rw [hs_reps.2.2.1, hKcard] at h1
    have h2 : 360 ∣ 2 * 7680 := (Dvd.intro _ rfl).trans h1
    exact absurd h2 (by norm_num)
  ·
    have hWW : W * W = t := mul_self_eq_of_twoB hto htZ ρ hρs
      (by ext y; rw [MonoidHom.mem_ker, hρk, hZeq]) hg hwg
    obtain ⟨⟨hDs, -⟩, hD, hDC, hCD, hcent⟩ := hs_D_facts
    have hWD : ρg W ∈
        centralizer (genGroup 3850 hsDGens hsDPerm : Set (Equiv.Perm (Fin 3850))) := by
      rw [hρgW, mem_centralizer_iff]
      intro d hd
      exact mem_centralizer_singleton_iff.mp (hDC hd).2
    exact nonempty_generalizedFitting_equiv htZ ht1 ht2 ρg hρgker hWW hρgC hs_reps.2.2.2.1 hD
      hDC hCD hcent hWD hK hKm

end HS2B

end CFSG.ComponentClassification.HarrisLit.N36

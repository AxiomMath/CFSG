module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016

open Subgroup


section InnerTwo

variable {Q : Type} [Group Q] [Finite Q]

@[expose] def innerPre (H : Subgroup (MulAut Q)) : Subgroup Q :=
  H.comap (MulAut.conj : Q →* MulAut Q)

theorem conj_apply_eq (α : MulAut Q) (q : Q) :
    MulAut.conj (α q) = α * MulAut.conj q * α⁻¹ := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem innerPre_map_eq {H : Subgroup (MulAut Q)} (α : MulAut Q)
    (hα : ∀ h, h ∈ H ↔ α * h * α⁻¹ ∈ H) :
    (innerPre H).map α.toMonoidHom = innerPre H := by
  apply le_antisymm
  · rintro _ ⟨q, hq, rfl⟩
    show MulAut.conj (α q) ∈ H
    rw [conj_apply_eq]
    exact (hα _).1 hq
  · intro q hq
    refine ⟨α⁻¹ q, ?_, by simp⟩
    show MulAut.conj (α⁻¹ q) ∈ H
    rw [conj_apply_eq]
    apply (hα _).2
    have hq' : MulAut.conj q ∈ H := hq
    convert hq' using 1
    group

theorem exists_inner_two_subgroup {H : Subgroup (MulAut Q)} (hH : IsPGroup 2 H)
    (hinner : ∀ h ∈ H, ∃ x : Q, MulAut.conj x = h) (hH1 : H ≠ ⊥) :
    ∃ R : Subgroup Q, R ≠ ⊥ ∧ IsPGroup 2 R ∧ R ≤ innerPre H ∧
      ∀ α : MulAut Q, (∀ h, h ∈ H ↔ α * h * α⁻¹ ∈ H) → R.map α.toMonoidHom = R := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := innerPre H with hPdef
  let c : ↥P →* ↥H :=
    MonoidHom.codRestrict ((MulAut.conj : Q →* MulAut Q).comp P.subtype) H (fun p => p.2)
  have hc : Function.Surjective c := by
    intro h
    obtain ⟨x, hx⟩ := hinner h.1 h.2
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show MulAut.conj x ∈ H
      rw [hx]
      exact h.2
    · apply Subtype.ext
      exact hx
  set Z : Subgroup ↥P := c.ker with hZdef
  have hZc : Z ≤ Subgroup.center ↥P := by
    intro p hp
    have hp1 : MulAut.conj (p : Q) = 1 := by
      have h := MonoidHom.mem_ker.1 hp
      exact congrArg Subtype.val h
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hcg : (p : Q) * (g : Q) * (p : Q)⁻¹ = g := by
      have := congrArg (fun φ : MulAut Q => φ (g : Q)) hp1
      simpa [MulAut.conj_apply] using this
    show (g : Q) * (p : Q) = (p : Q) * (g : Q)
    exact (mul_inv_eq_iff_eq_mul.1 hcg).symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hH
  have hPZ : Nat.card (↥P ⧸ Z) = 2 ^ k := by
    rw [hZdef, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective c hc).toEquiv, hk]
  have hk1 : k ≠ 0 := by
    intro h0
    apply hH1
    rw [Subgroup.eq_bot_iff_card, hk, h0]
    simp
  have hidx : Z.index = 2 ^ k := hPZ
  have h2P : 2 ∣ Nat.card ↥P := by
    have h := Subgroup.card_mul_index Z
    rw [hidx] at h
    rw [← h]
    exact dvd_mul_of_dvd_right (dvd_pow_self 2 hk1) _
  obtain ⟨R₁⟩ : Nonempty (Sylow 2 ↥P) := inferInstance
  have hnorm : (R₁ : Subgroup ↥P).Normal := sylow_two_normal_of_central Z hZc hPZ R₁
  have hR1 : (R₁ : Subgroup ↥P) ≠ ⊥ := by
    intro hbot
    have h1 := Subgroup.card_mul_index (R₁ : Subgroup ↥P)
    rw [hbot, Subgroup.card_bot, one_mul] at h1
    apply R₁.not_dvd_index
    rw [hbot, Subgroup.index_bot]
    exact h2P
  refine ⟨(R₁ : Subgroup ↥P).map P.subtype, ?_, ?_, ?_, ?_⟩
  · intro hR
    apply hR1
    rw [eq_bot_iff]
    intro x hx
    have hxR : (x : Q) ∈ (R₁ : Subgroup ↥P).map P.subtype := Subgroup.mem_map_of_mem _ hx
    rw [hR, Subgroup.mem_bot] at hxR
    rw [Subgroup.mem_bot]
    exact Subtype.ext hxR
  · exact (R₁.isPGroup').map P.subtype
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  · intro α hα
    have hPα : P.map α.toMonoidHom = P := innerPre_map_eq α hα
    have h1 : ∀ p ∈ P, α p ∈ P := by
      intro p hp
      have : α p ∈ P.map α.toMonoidHom := Subgroup.mem_map_of_mem _ hp
      rwa [hPα] at this
    have h2 : ∀ p ∈ P, α.symm p ∈ P := by
      intro p hp
      have : p ∈ P.map α.toMonoidHom := by rw [hPα]; exact hp
      obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.1 this
      have : α.symm p = q := by
        rw [← hqp]
        simp
      rw [this]
      exact hq
    have key := map_normal_sylow_eq P R₁ hnorm α h1 h2
    calc Subgroup.map α.toMonoidHom (Subgroup.map P.subtype (R₁ : Subgroup ↥P))
        = Subgroup.map (α.toMonoidHom.comp P.subtype) (R₁ : Subgroup ↥P) := by
          rw [Subgroup.map_map]
      _ = Subgroup.map (P.subtype.comp (restrictEquiv P α h1 h2).toMonoidHom)
            (R₁ : Subgroup ↥P) := by
          congr 1
      _ = Subgroup.map P.subtype (Subgroup.map (restrictEquiv P α h1 h2).toMonoidHom
            (R₁ : Subgroup ↥P)) := by
          rw [Subgroup.map_map]
      _ = Subgroup.map P.subtype (R₁ : Subgroup ↥P) := key

end InnerTwo

section PQuotIso

theorem pQuot_mulEquiv_of_surjective {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hf : Function.Surjective f)
    (hK : Nat.Coprime p (Nat.card f.ker)) :
    Nonempty ((X ⧸ CFSG.pPrimeCore p X) ≃* (Y ⧸ CFSG.pPrimeCore p Y)) := by
  classical
  haveI : (CFSG.pPrimeCore p X).Normal := Subgroup.sSup_normal _ fun _ hN => hN.1
  haveI : (CFSG.pPrimeCore p Y).Normal := Subgroup.sSup_normal _ fun _ hN => hN.1
  have himg : (CFSG.pPrimeCore p X).map f ≤ CFSG.pPrimeCore p Y := by
    apply CFSG.le_pPrimeCore_of_normal_coprime
    · exact (inferInstance : (CFSG.pPrimeCore p X).Normal).map f hf
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ f) CFSG.pPrimeCore_coprime_card
  set M : Subgroup X := (CFSG.pPrimeCore p Y).comap f with hMdef
  let φ : ↥M →* Y := f.comp M.subtype
  have hφr : φ.range = CFSG.pPrimeCore p Y := by
    ext y
    constructor
    · rintro ⟨m, rfl⟩
      exact m.2
    · intro hy
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨⟨x, hy⟩, rfl⟩
  have hφk : Nat.card φ.ker = Nat.card f.ker := by
    apply Nat.card_congr
    exact
      { toFun := fun m => ⟨m.1.1, MonoidHom.mem_ker.1 m.2⟩
        invFun := fun k => ⟨⟨k.1, by
          show f k.1 ∈ CFSG.pPrimeCore p Y
          rw [MonoidHom.mem_ker.1 k.2]
          exact Subgroup.one_mem _⟩, by
          show f k.1 = 1
          exact MonoidHom.mem_ker.1 k.2⟩
        left_inv := fun m => by
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := fun k => by
          apply Subtype.ext
          rfl }
  have hcopM : Nat.Coprime p (Nat.card M) := by
    have h := card_ker_mul_card_range φ
    rw [hφk, hφr] at h
    rw [← h]
    exact Nat.coprime_mul_iff_right.2 ⟨hK, CFSG.pPrimeCore_coprime_card⟩
  have hpre : M ≤ CFSG.pPrimeCore p X :=
    CFSG.le_pPrimeCore_of_normal_coprime
      ((inferInstance : (CFSG.pPrimeCore p Y).Normal).comap f) hcopM
  have heq : CFSG.pPrimeCore p X = M := by
    apply le_antisymm
    · intro x hx
      show f x ∈ CFSG.pPrimeCore p Y
      exact himg ⟨x, hx, rfl⟩
    · exact hpre
  let g : X →* Y ⧸ CFSG.pPrimeCore p Y := (QuotientGroup.mk' (CFSG.pPrimeCore p Y)).comp f
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore p Y) z
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, rfl⟩
  have hker : g.ker = CFSG.pPrimeCore p X := by
    rw [heq]
    ext x
    rw [MonoidHom.mem_ker, hMdef, Subgroup.mem_comap]
    simp only [g, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

end PQuotIso

end CFSG.LocalAnalysis.GLTheoremA.I2016

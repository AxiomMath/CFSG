module

public import CFSG.ClassicalInvolution.AschTight.S19QStmt
public import CFSG.ClassicalInvolution.AschTight.S19GG2Inv
public import CFSG.ClassicalInvolution.AschTight.S19GG2Aut
public import CFSG.ClassicalInvolution.AschTight.S19GD4Aut

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Generic
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint

section Transport

variable {K E : Type*} [Group K] [Group E]

@[expose] def FG0Model (R : Subgroup K) : Prop :=
  (∀ y ∈ Subgroup.centralizer (R : Set K), y * y = 1 → y = 1 ∨ y ∈ R) ∧
  (∃ x ∈ R, x ≠ 1 ∧ x * x = 1 ∧
    x ∈ ⁅⁅Subgroup.centralizer (R : Set K), Subgroup.centralizer (R : Set K)⁆,
      ⁅Subgroup.centralizer (R : Set K), Subgroup.centralizer (R : Set K)⁆⁆) ∧
  ∀ α : MulAut K, (∃ n : ℕ, α ^ (2 ^ n) = 1) → (∀ x ∈ R, α x = x) → ∃ g, α = MulAut.conj g

theorem map_centralizer_le (f : K →* E) (R : Subgroup K) :
    (Subgroup.centralizer (R : Set K)).map f ≤ Subgroup.centralizer (R.map f : Set E) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨r, hr, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hy r hr]

theorem fg0_of_transport (f : K →* E) (hf : Function.Bijective f) {R : Subgroup K} {z : E}
    (hz : IsUniqueInvolution (R.map f) z) (hR : FG0Model R) :
    (∀ y ∈ Subgroup.centralizer (R.map f : Set E), y * y = 1 → y = 1 ∨ y = z) ∧
    z ∈ ⁅⁅Subgroup.centralizer (R.map f : Set E), Subgroup.centralizer (R.map f : Set E)⁆,
      ⁅Subgroup.centralizer (R.map f : Set E), Subgroup.centralizer (R.map f : Set E)⁆⁆ ∧
    ∀ φ : MulAut E, IsPGroup 2 (Subgroup.zpowers φ) → (∀ x ∈ R.map f, φ x = x) →
      ∃ y ∈ Subgroup.centralizer (R.map f : Set E), φ = MulAut.conj y := by
  obtain ⟨ha1, ⟨x, hxR, hx1, hx2, hxC⟩, hb⟩ := hR
  set ψ := MulEquiv.ofBijective f hf with hψ
  have hψf : ∀ k, ψ k = f k := fun k => rfl
  have hfψ : ∀ y, f (ψ.symm y) = y := fun y => by rw [← hψf, MulEquiv.apply_symm_apply]
  refine ⟨fun y hy hy2 => ?_, ?_, fun φ hφ hfix => ?_⟩
  ·
    have hy0 : ψ.symm y ∈ Subgroup.centralizer (R : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      apply hf.1
      rw [map_mul, map_mul, hfψ]
      exact Subgroup.mem_centralizer_iff.mp hy (f r) ⟨r, hr, rfl⟩
    have hy02 : ψ.symm y * ψ.symm y = 1 := by rw [← map_mul, hy2, map_one]
    rcases ha1 _ hy0 hy02 with h | h
    · left
      rw [← hfψ y, h, map_one]
    · exact hz.unique y (by rw [← hfψ y]; exact ⟨_, h, rfl⟩) hy2
  ·
    have hfx : f x = z := by
      rcases hz.unique (f x) ⟨x, hxR, rfl⟩ (by rw [← map_mul, hx2, map_one]) with h | h
      · exact absurd (hf.1 (h.trans (map_one f).symm)) hx1
      · exact h
    rw [← hfx]
    have hmem := Subgroup.mem_map_of_mem f hxC
    rw [Subgroup.map_commutator, Subgroup.map_commutator] at hmem
    have hle := map_centralizer_le f R
    exact Subgroup.commutator_mono (Subgroup.commutator_mono hle hle)
      (Subgroup.commutator_mono hle hle) hmem
  ·
    obtain ⟨n, hn⟩ := hφ ⟨φ, Subgroup.mem_zpowers φ⟩
    have hφn : φ ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have hαn : (MulAut.congr ψ.symm φ) ^ (2 ^ n) = 1 := by rw [← map_pow, hφn, map_one]
    have hαx : ∀ k, MulAut.congr ψ.symm φ k = ψ.symm (φ (f k)) := fun k => rfl
    obtain ⟨g, hg⟩ := hb (MulAut.congr ψ.symm φ) ⟨n, hαn⟩ fun r hr => by
      rw [hαx, hfix (f r) ⟨r, hr, rfl⟩, ← hψf, MulEquiv.symm_apply_apply]
    have hφx : ∀ y, φ y = f g * y * (f g)⁻¹ := fun y => by
      have h1 := DFunLike.congr_fun hg (ψ.symm y)
      rw [hαx, hfψ, MulAut.conj_apply] at h1
      rw [← hfψ (φ y), h1, map_mul, map_mul, map_inv, hfψ]
    refine ⟨f g, ?_, MulEquiv.ext fun y => by rw [hφx, MulAut.conj_apply]⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hfix l hl
    rw [hφx] at h1
    calc l * f g = f g * l * (f g)⁻¹ * f g := by rw [h1]
      _ = f g * l := by group

end Transport

section Models

variable {p : ℕ} [Fact p.Prime]

theorem fg0Model_g2 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    {R : Subgroup ↥(adjointGroup .G2 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .G2 (g2Datum (GaloisField p e))) : FG0Model R := by
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e (by omega)]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  exact ⟨fun y hy hy2 => eq_one_or_mem_of_centralizing_g2 hodd hR hy hy2,
    exists_inv_mem_second_derived_g2 hodd hR,
    fun α _ hfix => exists_conj_of_fixes_g2 hp2 he α hR hfix⟩

theorem fg0Model_d4 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    {R : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e))) : FG0Model R :=
  ⟨fun _ hy hy2 => eq_one_or_mem_of_centralizing_d4 hp2 he hR hy hy2,
    exists_inv_mem_second_derived_d4 hp2 he hR,
    fun α ⟨_, hn⟩ hfix => exists_conj_of_fixes_d4 hp2 he α hn hR hfix⟩

end Models

theorem factFG0Core :
    ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ e →
      ∀ (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
        (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ),
          ((t = .G2 ∧ k = 0) ∨ (t = .trialityD4 ∧ k = 0)) →
          Nonempty (CFSG.ClassicalInvolution.Asc77.Ih8Model p e Ω t k e') →
          ∀ L ∈ Ω, ∀ z : E, IsUniqueInvolution L z →
            (∀ y ∈ Subgroup.centralizer (L : Set E), y * y = 1 → y = 1 ∨ y = z) ∧
            z ∈ ⁅⁅Subgroup.centralizer (L : Set E), Subgroup.centralizer (L : Set E)⁆,
              ⁅Subgroup.centralizer (L : Set E), Subgroup.centralizer (L : Set E)⁆⁆ ∧
            ∀ φ : MulAut E, IsPGroup 2 (Subgroup.zpowers φ) → (∀ x ∈ L, φ x = x) →
              ∃ y ∈ Subgroup.centralizer (L : Set E), φ = MulAut.conj y := by
  intro p e _ hp2 _ E _ _ _ Ω t k e' ht ⟨M⟩ L hL z hz
  have he' : 1 ≤ e' := M.admissible.2.1
  have htag : t = .G2 ∨ t = .trialityD4 := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [Or.inl rfl, Or.inr rfl]
  obtain ⟨R, hRcls, rfl⟩ := (M.mem_iff L).mp hL
  have hRfund := M.cls_sub hRcls
  have hinj : Function.Injective M.ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact M.ker_le_center.trans (RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 htag k he').le
  refine fg0_of_transport M.ψ ⟨hinj, M.surj⟩ hz ?_
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact fg0Model_g2 hp2 he' hRfund
  · exact fg0Model_d4 hp2 he' hRfund

theorem factFG0 : S19Q.FactFG0 :=
  factFG0Core

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

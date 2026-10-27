module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE

theorem exists_langDatum_of_toral_untw {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] (f : ℕ) (hf : 1 ≤ f) {p : ℕ} (hpq : Nat.Coprime p (ℓ ^ f))
    {u : ModGL τ L} (hup : u ^ p = 1) (hfix : entrywiseFrobGL τ L ℓ f u = u)
    (hconj : ∃ g ∈ adjointGroup τ L, g⁻¹ * u * g ∈ torusGroup τ L) :
    ∃ D : LangDatum τ L, D.Φ = Units.map (entrywiseHom (iterateFrobenius L ℓ f)) ∧
      D.q = ℓ ^ f ∧ u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom := by
  obtain ⟨g, hg, hgu⟩ := hconj
  have hA : Subgroup.zpowers u ≤ (torusGroup τ L).comap (MulAut.conj g⁻¹).toMonoidHom :=
    Subgroup.zpowers_le.2 (by simpa [MulAut.conj_apply] using hgu)
  obtain ⟨w, g0, hg0, hF, hmem⟩ := exists_lang_torus_of_conj_torus f hf hpq
    (A := Subgroup.zpowers u)
    (fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hup, one_zpow])
    (fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [map_zpow, hfix])
    hg (fun x hx => by simpa [MulAut.conj_apply] using hA hx)
  exact ⟨LangDatum.ofFrobenius (iterateFrobenius L ℓ f) (ℓ ^ f) (iterateFrobenius_def ℓ f) w hg0 hF,
    rfl, rfl, hmem u (Subgroup.mem_zpowers u)⟩

theorem exists_langDatum_of_toral_twisted (t : TwistTag) {L : Type} [Field L] [IsAlgClosed L]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (f : ℕ) (hf : 1 ≤ f) {u : ModGL t.tag L}
    (hfix : twistHom t L (iterateFrobenius L ℓ f) u = u)
    (hconj : ∃ g ∈ adjointGroup t.tag L, g⁻¹ * u * g ∈ torusGroup t.tag L) :
    ∃ D : LangDatum t.tag L, D.Φ = twistHom t L (iterateFrobenius L ℓ f) ∧
      D.q = ℓ ^ f ∧ u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom := by
  obtain ⟨g, hg, hgu⟩ := hconj
  have hA : Subgroup.zpowers u ≤ (torusGroup t.tag L).comap (MulAut.conj g⁻¹).toMonoidHom :=
    Subgroup.zpowers_le.2 (by simpa [MulAut.conj_apply] using hgu)
  obtain ⟨w, g0, hg0, hF, hmem⟩ := exists_lang_torus_of_conj_torus_twisted ℓ t f hf
    (A := Subgroup.zpowers u)
    (fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [map_zpow, hfix])
    hg (fun x hx => by simpa [MulAut.conj_apply] using hA hx)
  exact ⟨LangDatum.ofTwist t (iterateFrobenius L ℓ f) (ℓ ^ f) (iterateFrobenius_def ℓ f) w hg0 hF,
    rfl, rfl, hmem u (Subgroup.mem_zpowers u)⟩

theorem exists_langSetup_of_toral_datum_of_prime {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hf : 1 ≤ f) (D : LangDatum τ L) (hDq : D.q = ℓ ^ f)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ D.q) {p : ℕ}
    (hfin : Finite D.model) {C : Type}
    [Group C] (ι₀ : C →* ModGL τ L) (hι₀ : Function.Injective ι₀)
    (hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom) (β : MulAut C) {u : ModGL τ L}
    (hβ : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹)
    (hmem : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom) (hup : u ^ p = 1) (hu1 : u ≠ 1) :
    ∃ (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ) (ι : C →* ModGL τ L),
      S.D = D ∧ rootDiagUnit τ a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ := by
  classical
  obtain ⟨y, hy, hyu⟩ := hmem
  have hyu' : y = D.g0⁻¹ * u * D.g0 := by
    have h : D.g0 * y * D.g0⁻¹ = u := hyu
    rw [← h]
    group
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hy).1
  have hyp : y ^ p = 1 := by
    have h := conj_pow (a := D.g0⁻¹) (b := u) (i := p)
    rw [inv_inv] at h
    rw [hyu', h, hup]
    group
  have hap : ∀ i, a i ^ p = 1 := by
    have h1 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      have : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p :=
        (rootDiagUnitHom τ L).map_pow a p
      rw [this, ← ha, hyp, CFSG.LieType.Chevalley.rootDiagUnit_one]
    have h2 : a ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have h1 : rootDiagUnit τ a ≠ 1 := by
    intro h
    apply hu1
    rw [← ha, hyu'] at h
    have : u = D.g0 * (D.g0⁻¹ * u * D.g0) * D.g0⁻¹ := by group
    rw [this, h]
    group
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    rw [hDq]
    exact ⟨hℓ.isPrimePow.pow (by omega), (CharP.cast_eq_zero_iff L ℓ _).2
      (dvd_pow_self ℓ (by omega))⟩
  have hpq : ¬ p₀ ∣ D.q := by
    rw [hDq]
    intro h
    exact hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow h))
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ L D
  let ι : C →* ModGL τ L := (MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀
  have hι : ∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0 := fun c => by
    change (MulAut.conj D.g0⁻¹) (ι₀ c) = _
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨D.toSetup p₀ ρ hρ hp₀ hq₀ hqpow hpq hfin, a, ι, rfl, ?_, hap, h1,
    (MulAut.conj D.g0⁻¹).injective.comp hι₀, ?_, fun c => ?_⟩
  · exact ha ▸ hy
  · show ι.range = D.Γ
    rw [hΓ]
    exact MonoidHom.range_comp (MulAut.conj D.g0⁻¹).toMonoidHom ι₀
  · rw [hι, hι, hβ c, ← ha, hyu']
    group

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

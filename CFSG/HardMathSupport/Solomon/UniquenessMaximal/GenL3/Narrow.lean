module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Rank2
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Up
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.RankThree.PartTwo.KFacts
  CFSG.Quasithin.A318P CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.AutL3

theorem card_elemAbelian_le_27 {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    (ε : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 K) (A : Subgroup (MulAut Y))
    (hA : IsElemAbelian 3 A) : Nat.card A ≤ 27 := by
  have : IsCyclic (K ≃+* K) := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) := inferInstance
  set F := l3FrameLinear h3 with hF
  set Φ : MulAut Y →* MulAut (projectiveSL 3 K) :=
    (MulAut.congr ε).toMonoidHom.comp (centerDescend Y) with hΦ
  have hinj : Function.Injective Φ := phi_injective hY ε
  set Ae : Subgroup (MulAut (projectiveSL 3 K)) := A.map Φ with hAe
  have hAeA : IsElemAbelian 3 Ae := isElemAbelian_map Φ hA
  have hcard : Nat.card Ae = Nat.card A := Subgroup.card_map_of_injective hinj
  have hle : Ae ≤ F.E := by
    intro x hx
    have h3x : x ^ 3 = 1 := hAeA.2 x hx
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3x
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
    · have : x = 1 := orderOf_eq_one_iff.1 h1
      rw [this]; exact F.E.one_mem
    · exact F.mem_E.2 (F.three_mem x 1 (by rw [h1]; norm_num))
  set ρ : ↥Ae →* (K ≃+* K) := F.rho.comp (Subgroup.inclusion hle) with hρ
  have hker : ∀ x : ↥Ae, ρ x = 1 ↔ (x : MulAut (projectiveSL 3 K)) ∈ F.D := fun x =>
    F.rho_eq_one_iff ⟨x, hle x.2⟩
  have hcube : ∀ c ∈ ρ.range, c ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : (x : ↥Ae) ^ 3 = 1 := Subtype.ext (hAeA.2 x x.2)
    rw [this, map_one]
  have hrcard : Nat.card ρ.range ≤ 3 :=
    card_le_three_of_pow (fun c => Subtype.ext (by simpa using hcube c c.2))
  have hmul := Subgroup.card_ker_mul_card_range ρ
  set E0 : Subgroup (MulAut (projectiveSL 3 K)) := Ae ⊓ linearAutGroup 3 K with hE0
  have hE0A : IsElemAbelian 3 E0 := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hAeA.2 x hx.1⟩
    exact Subtype.ext (by
      have := hAeA.1.is_comm.comm ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩
      simpa using congrArg Subtype.val this)
  have hE09 : Nat.card E0 ≤ 9 := hD9_L h3 E0 inf_le_right hE0A
  have hkercard : Nat.card ρ.ker ≤ Nat.card E0 := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥ρ.ker => (⟨(x.1 : MulAut (projectiveSL 3 K)), x.1.2, (hker x.1).1 x.2⟩ : ↥E0))
      ?_
    intro x y hxy
    have h := congrArg (fun z : ↥E0 => (z : MulAut (projectiveSL 3 K))) hxy
    exact Subtype.ext (Subtype.ext h)
  rw [← hcard]
  calc Nat.card Ae = Nat.card ρ.ker * Nat.card ρ.range := hmul.symm
    _ ≤ 9 * 3 := Nat.mul_le_mul (hkercard.trans hE09) hrcard

theorem exists_model_of_catalogL364_aux {Q : Type} [Group Q] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hd : IsL364Index (.A r q))
    (e : Q ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 64 ∧
      Nonempty (Q ≃* StatedProj (StatedSL 3 K)) := by
  have hd' : r = 2 ∧ q.p = 2 ∧ q.exponent = 6 := hd
  obtain ⟨rfl, hp, hexp⟩ := hd'
  have hm := CFSG.RankThree.PartTwo.Sec4.Census.lieModel_typeA 2 q hv
  have hcl : StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group .PSL (2 + 1) q.p
      q.exponent := by
    rcases hm.2 with h | h
    · exact h
    · exact absurd h.1 (by norm_num)
  have hrest : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.p ^ q.exponent ∧
      Nonempty ((TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group ≃* StatedProj (StatedSL (2 + 1) K)) :=
    hcl.2
  obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := hrest
  refine ⟨K, hK, hKf, ?_, ⟨e.trans e'⟩⟩
  rw [hcard, hp, hexp]
  norm_num

theorem exists_model_of_catalogL364 {Q : Type} [Group Q] (h : IsCatalogLieIso Q IsL364Index) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 64 ∧
      Nonempty (Q ≃* StatedProj (StatedSL 3 K)) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  cases d <;> first
    | exact exists_model_of_catalogL364_aux _ _ hv hd e
    | exact absurd hd (by simp [IsL364Index])

@[expose] def L364Rank3Gen : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 64 →
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL 3 K)) →
    ∀ A : Subgroup (MulAut Y), IsElemAbelian 3 A → Nat.card A = 27 →
    (∃ α ∈ A, α ≠ 1 ∧ ¬ IsInnDiagThree α) →
      ⊤ ≤ ⨆ (S : Subgroup (MulAut Y)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S), c25Fix S

theorem genL364Narrow_of_rank3 (h27 : L364Rank3Gen) :
    ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
      IsCatalogLieIso (Y ⧸ Subgroup.center Y) IsL364Index →
      ∀ A : Subgroup (MulAut Y), IsElemAbelian 3 A → (∃ α ∈ A, α ≠ 1 ∧ ¬ IsInnDiagThree α) →
        ⊤ ≤ ⨆ (S : Subgroup (MulAut Y)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S), c25Fix S := by
  intro Y _ _ hY hcore hcat A hA hα
  obtain ⟨K, hK, hKf, hcard, ⟨e⟩⟩ := exists_model_of_catalogL364 hcat
  have hL : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL 3 F)) := ⟨K, hK, hKf, ⟨e⟩⟩
  have h3 : 3 ∣ Nat.card K - 1 := by rw [hcard]; norm_num
  have hbound : Nat.card A ≤ 27 := card_elemAbelian_le_27 hY h3 (e.trans (psiO K)) A hA
  have hp : IsPGroup 3 A := fun g => ⟨1, by
    have := hA.2 g g.2
    exact Subtype.ext (by simpa using this)⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hn3 : n ≤ 3 := by
    by_contra hcon
    have : 3 ^ 4 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  ·
    refine le_iSup₂_of_le (⊥ : Subgroup (MulAut Y)) ⟨bot_le, ?_⟩ ?_
    · rw [hn]; simp
    · intro y _ α hα'
      rw [Subgroup.mem_bot.1 hα']
      simp
  · refine le_iSup₂_of_le (⊥ : Subgroup (MulAut Y)) ⟨bot_le, ?_⟩ ?_
    · rw [hn]; simp
    · intro y _ α hα'
      rw [Subgroup.mem_bot.1 hα']
      simp
  · exact gen_card_nine hY hL A hA (by rw [hn]; norm_num) hα
  · exact h27 Y hY hcore K hcard ⟨e⟩ A hA (by rw [hn]; norm_num) hα

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

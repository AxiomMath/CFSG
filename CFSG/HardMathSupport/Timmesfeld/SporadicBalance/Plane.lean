module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open scoped Pointwise

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.ComponentClassification.OuterAutomorphisms

variable {p : ℕ} {S : Type*} [Group S]

theorem gLAPPrimeCoreOf_eq_bot_of_isPGroup [Finite S] (hp : p.Prime) {X : Subgroup S}
    (hX : IsPGroup p X) : GLAPPrimeCoreOf p X = ⊥ := by
  have h := inf_eq_bot_of_coprime_isPGroup hp (coprime_card_GLAPPrimeCoreOf hp X) hX
  rwa [inf_eq_left.mpr (GLAPPrimeCoreOf_le X)] at h

theorem gLAPPrimeCoreOf_eq_bot_of_plane [Finite S] (hp : p.Prime) (s : S) (A : Subgroup S)
    (hAc : ∀ a ∈ A, s * a = a * s) (hA : ∀ a : A, a ^ p = 1) (hcard : Nat.card A = p ^ 2)
    (h : ∀ a ∈ A, a ≠ 1 →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set S) ⊓
        Subgroup.centralizer ({a} : Set S)) = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set S)) = ⊥ := by
  set C := Subgroup.centralizer ({s} : Set S) with hC
  set R := GLAPPrimeCoreOf p C with hR
  have hcop : ¬ p ∣ Nat.card R := (hp.coprime_iff_not_dvd).1 (coprime_card_GLAPPrimeCoreOf hp C)
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hAc a ha).symm
  have hnorm : A ≤ Subgroup.normalizer (R : Set S) := by
    intro a ha
    refine Subgroup.mem_normalizer_iff.2 fun x => ?_
    constructor
    · intro hx
      exact GLAPPrimeCoreOf_conj_mem a (hAC ha) x hx
    · intro hx
      have := GLAPPrimeCoreOf_conj_mem a⁻¹ (C.inv_mem (hAC ha)) _ hx
      simpa [mul_assoc] using this
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p
    hp A R hA hcard hcop hnorm
  refine le_antisymm ?_ bot_le
  calc R = ⨆ (member : A) (_ : member ≠ 1), R ⊓ Subgroup.centralizer ({(member : S)} : Set S) :=
        hgen
    _ ≤ ⊥ := by
      refine iSup_le fun a => iSup_le fun ha => ?_
      have ha1 : (a : S) ≠ 1 := fun e => ha (Subtype.ext e)
      rw [← h a a.2 ha1]
      refine le_GLAPPrimeCoreOf_of_normal (inf_le_inf (GLAPPrimeCoreOf_le C) le_rfl) ?_ ?_
      · intro g hg x hx
        obtain ⟨hgC, hga⟩ := Subgroup.mem_inf.1 hg
        obtain ⟨hxR, hxa⟩ := Subgroup.mem_inf.1 hx
        refine Subgroup.mem_inf.2 ⟨GLAPPrimeCoreOf_conj_mem g hgC x hxR, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hga hxa ⊢
        have e1 : g⁻¹ * (a : S) = a * g⁻¹ := by
          calc g⁻¹ * (a : S) = g⁻¹ * (a * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * a) * g⁻¹ := by rw [hga]
            _ = a * g⁻¹ := by group
        calc g * x * g⁻¹ * (a : S) = g * x * (g⁻¹ * a) := by group
          _ = g * (x * a) * g⁻¹ := by rw [e1]; group
          _ = g * (a * x) * g⁻¹ := by rw [hxa]
          _ = (g * a) * x * g⁻¹ := by group
          _ = (a * g) * x * g⁻¹ := by rw [hga]
          _ = (a : S) * (g * x * g⁻¹) := by group
      · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
          (coprime_card_GLAPPrimeCoreOf hp C)

@[expose] def PlaneCond (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ s : S, orderOf s = p → ∃ A : Subgroup S, IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
    (∀ a ∈ A, s * a = a * s) ∧ ∀ a ∈ A, a ≠ 1 →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set S) ⊓
        Subgroup.centralizer ({a} : Set S)) = ⊥

@[expose] def PlaneCondP (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ s : S, orderOf s = p → ∃ A : Subgroup S, IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
    (∀ a ∈ A, s * a = a * s) ∧ ∀ a ∈ A, a ≠ 1 → IsPGroup p (Subgroup.centralizer ({a} : Set S))

theorem PlaneCondP.planeCond [Finite S] (hp : p.Prime) (h : PlaneCondP p S) : PlaneCond p S := by
  intro s hs
  obtain ⟨A, hA1, hA2, hA3, hA4⟩ := h s hs
  refine ⟨A, hA1, hA2, hA3, fun a ha ha1 => ?_⟩
  exact gLAPPrimeCoreOf_eq_bot_of_isPGroup hp ((hA4 a ha ha1).to_le inf_le_right)

theorem oPrimeCoreTrivialAt_of_planeCond [Finite S] (hp : p.Prime) (h : PlaneCond p S) :
    OPrimeCoreTrivialAt p S := by
  intro s hs
  obtain ⟨A, hA1, hA2, hA3, hA4⟩ := h s hs
  exact gLAPPrimeCoreOf_eq_bot_of_plane hp s A hA3
    (fun a => Subtype.ext (by simpa using hA1.2 a a.2)) hA2 hA4

@[expose] def NoOuterFixesPlane (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ σ : MulAut S, σ ^ 2 = 1 → σ ∉ innerAut S → ∀ E : Subgroup S, IsElemAbelian p E →
    Nat.card E = p ^ 2 → ∃ x ∈ E, σ x ≠ x

theorem noOuterFixesCentralizer_of_planeCond (h : PlaneCond p S) (hK : NoOuterFixesPlane p S) :
    NoOuterFixesCentralizer p S :=
  noOuterFixesCentralizer_of_elemAbelian (k := 2) (fun s hs => by
    obtain ⟨A, hA1, hA2, hA3, -⟩ := h s hs
    exact ⟨A, hA1, hA2, hA3⟩) hK

theorem gLAPPrimeCoreOf_centralizer_conj (g s : S) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({g * s * g⁻¹} : Set S)) = ⊥ ↔
      GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set S)) = ⊥ := by
  have hψ : Function.Injective (MulAut.conj g : S ≃* S).toMonoidHom :=
    (MulAut.conj g : S ≃* S).injective
  have hmap := map_glaPPrimeCoreOf_of_injective p (MulAut.conj g : S ≃* S).toMonoidHom hψ
    (Subgroup.centralizer ({s} : Set S))
  have hc := map_inf_centralizer_of_injective (MulAut.conj g : S ≃* S).toMonoidHom hψ ⊤ s
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ (MulAut.conj g : S ≃* S).surjective,
    top_inf_eq] at hc
  rw [hc] at hmap
  have hs : (MulAut.conj g : S ≃* S).toMonoidHom s = g * s * g⁻¹ := by
    simp [MulAut.conj_apply]
  rw [hs] at hmap
  rw [← hmap, Subgroup.map_eq_bot_iff_of_injective _ hψ]

theorem planeCondP_of_sylow [Finite S] (hp : p.Prime) (T : Sylow p S) (Z : Subgroup S)
    (hZe : IsElemAbelian p Z) (hZ : Nat.card Z = p ^ 2)
    (hZT : ∀ z ∈ Z, ∀ x ∈ (T : Subgroup S), x * z = z * x)
    (hZc : ∀ z ∈ Z, z ≠ 1 → IsPGroup p (Subgroup.centralizer ({z} : Set S))) :
    PlaneCondP p S := by
  have : Fact p.Prime := ⟨hp⟩
  intro s hs
  have hsp : IsPGroup p (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S Q T
  have hsT : g * s * g⁻¹ ∈ (T : Subgroup S) := by
    have h1 : s ∈ (Q : Subgroup S) := hQ (Subgroup.mem_zpowers s)
    have h2 : MulAut.conj g s ∈ (MulAut.conj g • (Q : Set S)) :=
      Set.smul_mem_smul_set h1
    rw [← Sylow.coe_smul, hg] at h2
    have h3 : g * s * g⁻¹ ∈ T := by simpa [MulAut.conj_apply] using h2
    exact h3
  set ψ : S →* S := (MulAut.conj g⁻¹ : S ≃* S).toMonoidHom with hψdef
  have hψ : Function.Injective ψ := (MulAut.conj g⁻¹ : S ≃* S).injective
  have hψapp : ∀ z, ψ z = g⁻¹ * z * g := fun z => by simp [hψdef]
  refine ⟨Z.map ψ, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    apply Subtype.ext
    change ψ x * ψ y = ψ y * ψ x
    have := congrArg Subtype.val (hZe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul]
    exact congrArg ψ this
  · obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hZe.2 z hz, map_one]
  · rw [Subgroup.card_map_of_injective hψ, hZ]
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ha
    rw [hψapp]
    have h1 := hZT z hz _ hsT
    calc s * (g⁻¹ * z * g) = g⁻¹ * ((g * s * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * s * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * z * g) * s := by group
  · intro a ha ha1
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ha
    have hz1 : z ≠ 1 := fun e => ha1 (by rw [e, map_one])
    have hc := map_inf_centralizer_of_injective ψ hψ ⊤ z
    rw [top_inf_eq, Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹ : S ≃* S).surjective,
      top_inf_eq] at hc
    rw [← hc]
    exact (hZc z hz hz1).map ψ

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance

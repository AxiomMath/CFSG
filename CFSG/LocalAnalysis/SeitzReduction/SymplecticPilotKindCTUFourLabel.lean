module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUFourSiegel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignEdge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelPieces

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Block

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {N ε : ℕ} {hσ : ∀ c, σ (σ c) = c}
  {hε : ε ≤ 1}

theorem ctufSiegel_mem_ctuBlock_singleton {k : Fin N} {B : Finset (Fin N)} (hkB : k ∉ B)
    {A : SL(N, F)} (hA : A ∈ blockSpecialLinear B) :
    ctufSiegel σ hσ ε hε A ∈ ctuBlock σ ε ({k} : Finset (Fin N)) :=
  ctufSiegel_mem_ctuBlock (fun p hp => by rw [Finset.mem_singleton.1 hp]; exact hkB) hA

end Block

theorem ctuf_four_le_card {F : Type} {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    4 ≤ Nat.card F := by
  rw [hF]
  have h4 : 4 ≤ 2 ^ f := four_le_two_pow hf
  nlinarith

section Param

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N ε : ℕ}
  {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1} {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}

theorem CtuParam.ctufSiegel_mem_stringCore (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    {k : Fin N} (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k) {B : Finset (Fin N)}
    (hkB : k ∉ B) (hB : 2 ≤ B.card) {A : SL(N, F)} (hA : A ∈ blockSpecialLinear B) :
    P.Φ ⟨ctufSiegel _ (unitaryInvolution_involutive hF) ε hε A,
      ctufSiegel_mem_ctuBlock_singleton hkB hA⟩ ∈ stringCore e B := by
  have hσ := unitaryInvolution_involutive hF
  set S := (blockSpecialLinear (K := F) B).map (ctufSiegel (unitaryInvolution F 2 f) hσ ε hε)
    with hS
  have hSle : S ≤ ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)) := by
    rintro _ ⟨A', hA', rfl⟩
    exact ctufSiegel_mem_ctuBlock_singleton hkB hA'
  set H : Subgroup (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))) :=
    S.subgroupOf _ with hH
  have hHmap : H.map (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))).subtype = S := by
    rw [hH, subgroupOf_map_subtype, inf_eq_left.mpr hSle]
  have hSperf : ⁅S, S⁆ = S := by
    rw [hS, ← Subgroup.map_commutator,
      LinearPilot.commutator_blockSpecialLinear_eq_of_two_le hB (ctuf_four_le_card hF hf)]
  have hHperf : ⁅H, H⁆ = H := by
    apply Subgroup.map_injective
      (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))).subtype_injective
    rw [map_commutator, hHmap, hSperf]
  have hmem : (⟨ctufSiegel _ hσ ε hε A, ctufSiegel_mem_ctuBlock_singleton hkB hA⟩ :
      ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))) ∈ H := ⟨A, hA, rfl⟩
  have hcent : H.map P.Φ ≤ centralizer (modelToG e (stringTorusSp K B) : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨d, ⟨t, ht, rfl⟩, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
    obtain ⟨A', hA', hzA'⟩ := hz
    rw [diagSp_eq_rootTorusHom_mul t k, map_mul, Subgroup.coe_mul]
    have h1 : P.Φ z ∈ centralizer (modelToG e (rootTorusSp K k) : Set G) := by
      have : P.Φ z ∈ neighbourCore e k := P.range_eq ▸ ⟨z, rfl⟩
      exact F4Pilot.centralizerPerfectCore_le_centralizer _ this
    have h2 := mem_centralizer_iff.1 h1 _ (UnitaryPilot.symm_mem_modelToG e ⟨t k, rfl⟩)
    have hd := diagSp_update_mem_spBlock_compl (K := K) t k
    have h3 : ((e.symm (diagSp K N (Function.update t k 1)) : L) : G) =
        P.Φ ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι (diagSp K N (Function.update t k 1)),
          ctuEmbed_mem_ctuBlock_iff.2 hd⟩ := (P.N1 _ hd).symm
    have hzc : (z : SU (unitaryInvolution F 2 f) (2 * N + ε)) *
        ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι (diagSp K N (Function.update t k 1)) =
        ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι (diagSp K N (Function.update t k 1)) * z := by
      have hz' : (z : SU (unitaryInvolution F 2 f) (2 * N + ε)) =
          ctufSiegel (unitaryInvolution F 2 f) hσ ε hε A' := hzA'.symm
      rw [hz']
      refine ctufSiegel_commute_ctuEmbed_diagSp hA' fun i hi j hj => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hkB),
        Function.update_of_ne (ne_of_mem_of_not_mem hj hkB)]
      exact (mem_stringTorusParam.1 ht) i hi j hj
    have h4 : P.Φ ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι
        (diagSp K N (Function.update t k 1)), ctuEmbed_mem_ctuBlock_iff.2 hd⟩ * P.Φ z =
        P.Φ z * P.Φ ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι
          (diagSp K N (Function.update t k 1)), ctuEmbed_mem_ctuBlock_iff.2 hd⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hzc.symm
    rw [h3]
    calc ((e.symm (rootTorusHom K N k (t k)) : L) : G) * P.Φ ⟨_, _⟩ * P.Φ z
        = ((e.symm (rootTorusHom K N k (t k)) : L) : G) * (P.Φ z * P.Φ ⟨_, _⟩) := by
          rw [mul_assoc, h4]
      _ = P.Φ z * (((e.symm (rootTorusHom K N k (t k)) : L) : G) * P.Φ ⟨_, _⟩) := by
          rw [← mul_assoc, h2, mul_assoc]
  have hle : H.map P.Φ ≤ stringCore e B := by
    rw [stringCore_def]
    exact CFSG.Quasithin.le_perfectCore_of_perfect hcent (by rw [← map_commutator, hHperf])
  exact hle ⟨_, hmem, rfl⟩

end Param

section SiegelField

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {N : ℕ} {F : Type}
  [Field F] {e : L ≃* StatedSp N K} {t : G} {ι : K →+* F} {σ : F ≃+* F}

theorem SiegelFieldParam.exists_of_mem_stringCore [Finite G] [Finite F]
    (S : SiegelFieldParam e t ι σ) (hK : 4 ≤ Nat.card K) {B : Finset (Fin N)}
    (hB : 2 ≤ B.card) {g : G} (hg : g ∈ stringCore e B) :
    ∃ A ∈ blockSpecialLinear (K := F) B, S.Φ ⟨leviEmbedSL F N A, A, rfl⟩ = g := by
  rw [S.stringCore_eq_map hK hB] at hg
  obtain ⟨w, hw, rfl⟩ := hg
  rw [SetLike.mem_coe, mem_subgroupOf] at hw
  obtain ⟨A, hA, hAw⟩ := hw
  exact ⟨A, hA, congrArg S.Φ (Subtype.ext hAw)⟩

theorem SiegelFieldParam.eq_of_Φ_eq (S : SiegelFieldParam e t ι σ) {B : Finset (Fin N)}
    {j : Fin N} (hj : j ∉ B) {A A' : SL(N, F)} (hA : A ∈ blockSpecialLinear B)
    (hA' : A' ∈ blockSpecialLinear B)
    (h : S.Φ ⟨leviEmbedSL F N A, A, rfl⟩ = S.Φ ⟨leviEmbedSL F N A', A', rfl⟩) : A = A' := by
  have h1 := S.injective_siegelBlock hj (a₁ := ⟨⟨leviEmbedSL F N A, A, rfl⟩,
    mem_subgroupOf.2 ⟨A, hA, rfl⟩⟩) (a₂ := ⟨⟨leviEmbedSL F N A', A', rfl⟩,
      mem_subgroupOf.2 ⟨A', hA', rfl⟩⟩) h
  exact leviEmbedSL_injective (congrArg (fun x => ((x : siegelLevi F N) : StatedSp N F))
    (congrArg Subtype.val h1))

end SiegelField

section Two

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}
  {t : G} {σ' : F ≃+* F}

omit [Finite K] in
theorem CtuParam.exists_ctufSiegel_eq_of_two (S : SiegelFieldParam e t ι σ')
    (hKc : Nat.card K = 2 ^ f) (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hN : 3 ≤ N)
    {k : Fin N} (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k) {B : Finset (Fin N)}
    (hkB : k ∉ B) (hB2 : B.card = 2) {l : Fin N} (hlk : l ≠ k) (hlB : l ∉ B)
    {T : SL(N, F)} (hT : T ∈ blockSpecialLinear B) :
    ∃ (A : SL(N, F)) (hA : A ∈ blockSpecialLinear B),
      P.Φ ⟨ctufSiegel _ (unitaryInvolution_involutive hF) ε hε A,
        ctufSiegel_mem_ctuBlock_singleton hkB hA⟩ = S.Φ ⟨leviEmbedSL F N T, T, rfl⟩ := by
  have hK : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hσ := unitaryInvolution_involutive hF
  set SB := blockSpecialLinear (K := F) B with hSB
  set φ₁ : SB →* G := P.Φ.comp (((ctufSiegel (unitaryInvolution F 2 f) hσ ε hε).comp
    SB.subtype).codRestrict (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)))
      fun A => ctufSiegel_mem_ctuBlock_singleton (hσ := hσ) (hε := hε) hkB A.2) with hφ₁
  have hkl : k ≠ l := Ne.symm hlk
  have hc3 : ({k} : Finset (Fin N))ᶜ.card = N - 1 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hq : (2 * ({k} : Finset (Fin N))ᶜ.card + ε, 2 ^ f) ≠ (3, 2) := by
    rw [hc3]
    intro h'
    have := (Prod.mk.inj h').1
    omega
  have hinj := P.injective_overlap hF hkl (by rw [hc3]; omega) hq
  have hφ₁inj : Function.Injective φ₁ := by
    intro A A' h
    have hAkl : ctufSiegel (unitaryInvolution F 2 f) hσ ε hε (A : SL(N, F)) ∈
        ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) :=
      ctufSiegel_mem_ctuBlock (fun p hp => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hkB
        · exact hlB) A.2
    have hA'kl : ctufSiegel (unitaryInvolution F 2 f) hσ ε hε (A' : SL(N, F)) ∈
        ctuBlock (unitaryInvolution F 2 f) ε ({k, l} : Finset (Fin N)) :=
      ctufSiegel_mem_ctuBlock (fun p hp => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hkB
        · exact hlB) A'.2
    have h2 := hinj (a₁ := ⟨_, hAkl⟩) (a₂ := ⟨_, hA'kl⟩) h
    have h3 := congrArg Subtype.val h2
    exact Subtype.ext (ctufSiegel_injective h3)
  set φ₂ : SB →* G := S.Φ.comp ((leviEmbedSL F N).rangeRestrict.comp SB.subtype) with hφ₂
  have hrange₁ : φ₁.range ≤ stringCore e B := by
    rintro _ ⟨A, rfl⟩
    exact P.ctufSiegel_mem_stringCore hF hf hkB (by omega) A.2
  have hrange₂ : stringCore e B ≤ φ₂.range := by
    intro g hg
    obtain ⟨A, hA, rfl⟩ := S.exists_of_mem_stringCore hK (by omega) hg
    exact ⟨⟨A, hA⟩, rfl⟩
  have hc₁ : Nat.card φ₁.range = Nat.card SB :=
    (Nat.card_congr (MonoidHom.ofInjective hφ₁inj).toEquiv).symm
  have hc₂ : Nat.card φ₂.range ≤ Nat.card SB :=
    Nat.card_le_card_of_surjective _ φ₂.rangeRestrict_surjective
  have heq₁ : φ₁.range = stringCore e B :=
    Subgroup.eq_of_le_of_card_ge hrange₁ (by
      rw [hc₁]
      exact (Subgroup.card_le_of_le hrange₂).trans hc₂)
  have heq₂ : stringCore e B = φ₂.range :=
    Subgroup.eq_of_le_of_card_ge hrange₂ (by
      rw [← heq₁, hc₁]
      exact hc₂)
  have hmem : φ₂ ⟨T, hT⟩ ∈ φ₁.range := by
    rw [heq₁, heq₂]
    exact ⟨⟨T, hT⟩, rfl⟩
  obtain ⟨⟨A, hA⟩, hAT⟩ := hmem
  exact ⟨A, hA, hAT⟩

end Two

section Label

theorem ctuf_fix_iff {K F : Type} [Field K] [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {ι : K →+* F}
    (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c) (x : F) :
    unitaryInvolution F 2 f x = x ↔ x ∈ Set.range ι := by
  constructor
  · intro hx
    set h := ctua_unitaryFieldData hF hf with hh
    have hmem : ∀ c : K, ι c ∈ h.fixedField := fun c =>
      (h.mem_fixedField).2 (by rw [h.bar_apply, ← unitaryInvolution_apply]; exact hι c)
    have hinj : Function.Injective (fun c : K => (⟨ι c, hmem c⟩ : h.fixedField)) :=
      fun c d hcd => ι.injective (congrArg Subtype.val hcd)
    have : Finite h.fixedField := Subtype.finite
    have hxm : x ∈ h.fixedField :=
      (h.mem_fixedField).2 (by rw [h.bar_apply, ← unitaryInvolution_apply]; exact hx)
    obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le (by rw [hKc, h.card_fixedField])).2 ⟨x, hxm⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  · rintro ⟨c, rfl⟩
    exact hι c

theorem ctuf_map_map {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {N : ℕ}
    (A : SL(N, F)) :
    SpecialLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.map (σ : F →+* F) A) = A := by
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe, hσ]

theorem ctuf_notMem_compl_singleton {N : ℕ} (k : Fin N) : k ∉ ({k} : Finset (Fin N))ᶜ := by
  simp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}
  {t : G}

omit [Finite K] in
theorem CtuParam.exists_siegel_label (S : SiegelFieldParam e t ι (unitaryInvolution F 2 f))
    (hKc : Nat.card K = 2 ^ f) (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hN : 4 ≤ N)
    {k : Fin N} (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k) :
    ∃ b : Bool, ∀ (A : SL(N, F)) (hA : A ∈ blockSpecialLinear ({k} : Finset (Fin N))ᶜ),
      P.Φ ⟨ctufSiegel _ (unitaryInvolution_involutive hF) ε hε A,
        ctufSiegel_mem_ctuBlock_singleton (ctuf_notMem_compl_singleton k) hA⟩ =
        S.Φ ⟨leviEmbedSL F N (bif b then
          SpecialLinearGroup.map (unitaryInvolution F 2 f : F →+* F) A else A), _, rfl⟩ := by
  have hK : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hσ := unitaryInvolution_involutive hF
  set B := ({k} : Finset (Fin N))ᶜ with hBdef
  have hkB : k ∉ B := ctuf_notMem_compl_singleton k
  have hB3 : 3 ≤ B.card := by
    rw [hBdef, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  set SB := blockSpecialLinear (K := F) B with hSB
  set φ₁ : SB →* G := P.Φ.comp (((ctufSiegel (unitaryInvolution F 2 f) hσ ε hε).comp
    SB.subtype).codRestrict (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)))
      fun A => ctufSiegel_mem_ctuBlock_singleton (hσ := hσ) (hε := hε) hkB A.2) with hφ₁
  set φ₂ : SB →* G := S.Φ.comp ((leviEmbedSL F N).rangeRestrict.comp SB.subtype) with hφ₂
  have hφ₂inj : Function.Injective φ₂ := fun A₁ A₂ h => Subtype.ext (S.eq_of_Φ_eq hkB A₁.2 A₂.2 h)
  have hφ₁₂ : ∀ A, φ₁ A ∈ φ₂.range := fun A => by
    obtain ⟨A', hA', h⟩ := S.exists_of_mem_stringCore hK (by omega)
      (P.ctufSiegel_mem_stringCore hF hf hkB (by omega) A.2)
    exact ⟨⟨A', hA'⟩, h⟩
  set τ₀ : SB →* SB :=
    (MonoidHom.ofInjective hφ₂inj).symm.toMonoidHom.comp (φ₁.codRestrict φ₂.range hφ₁₂) with hτ₀def
  have hτ₀ : ∀ A, φ₂ (τ₀ A) = φ₁ A := fun A => by
    have h1 := (MonoidHom.ofInjective hφ₂inj).apply_symm_apply ⟨φ₁ A, hφ₁₂ A⟩
    exact congrArg Subtype.val h1
  have htr : ∀ (i j : Fin N) (hij : i ≠ j) (c : F) (hi : i ∈ B) (hj : j ∈ B),
      ∃ A : SB, τ₀ A = ⟨SpecialLinearGroup.transvection hij c,
        LinearPilot.transvection_mem_blockSpecialLinear hij hi hj c⟩ := by
    intro i j hij c hi hj
    have hT : SpecialLinearGroup.transvection hij c ∈
        blockSpecialLinear (K := F) ({i, j} : Finset (Fin N)) :=
      LinearPilot.transvection_mem_blockSpecialLinear hij (by simp) (by simp) c
    obtain ⟨l, hl, hli, hlj⟩ : ∃ l ∈ B, l ≠ i ∧ l ≠ j := by
      have : 2 < B.card := by omega
      obtain ⟨a, ha, b, hb, c', hc', hab, hac, hbc⟩ := Finset.two_lt_card.1 this
      by_cases hai : a = i
      · by_cases hbj : b = j
        · exact ⟨c', hc', fun h => hac (hai.trans h.symm), fun h => hbc (hbj.trans h.symm)⟩
        · by_cases hbi : b = i
          · exact absurd (hai.trans hbi.symm) hab
          · exact ⟨b, hb, hbi, hbj⟩
      · by_cases haj : a = j
        · by_cases hbi : b = i
          · exact ⟨c', hc', fun h => hbc (hbi.trans h.symm), fun h => hac (haj.trans h.symm)⟩
          · by_cases hbj : b = j
            · exact absurd (haj.trans hbj.symm) hab
            · exact ⟨b, hb, hbi, hbj⟩
        · exact ⟨a, ha, hai, haj⟩
    have hkij : k ∉ ({i, j} : Finset (Fin N)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ne_of_mem_of_not_mem hi hkB |>.symm, ne_of_mem_of_not_mem hj hkB |>.symm⟩
    have hlk : l ≠ k := ne_of_mem_of_not_mem hl hkB
    have hlij : l ∉ ({i, j} : Finset (Fin N)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hli, hlj⟩
    obtain ⟨A, hA, hAT⟩ := P.exists_ctufSiegel_eq_of_two S hKc hF hf (by omega) hkij
      (Finset.card_pair hij) hlk hlij hT
    have hsub : ({i, j} : Finset (Fin N)) ⊆ B := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hj
    refine ⟨⟨A, LinearPilot.blockSpecialLinear_mono hsub hA⟩, hφ₂inj ?_⟩
    rw [hτ₀]
    exact hAT
  have hτsurj : Function.Surjective τ₀ := by
    have hle : blockSpecialLinear (K := F) B ≤ τ₀.range.map SB.subtype := by
      rw [LinearPilot.blockSpecialLinear_eq_closure, Subgroup.closure_le]
      rintro _ ⟨i, j, hij, c, hi, hj, rfl⟩
      obtain ⟨A, hA⟩ := htr i j hij c hi hj
      exact ⟨_, ⟨A, hA⟩, rfl⟩
    intro y
    obtain ⟨z, ⟨x, rfl⟩, hz⟩ := hle y.2
    exact ⟨x, Subtype.ext hz⟩
  have hτinj : Function.Injective τ₀ := Finite.injective_iff_surjective.2 hτsurj
  have hτbij : Function.Bijective τ₀ := ⟨hτinj, hτsurj⟩
  set τ : MulAut SB := MulEquiv.ofBijective τ₀ hτbij with hτdef
  have hσσ : unitaryInvolution F 2 f * unitaryInvolution F 2 f = 1 :=
    RingEquiv.ext fun c => hσ c
  have hfixK : ∀ x : blockSpecialLinear (K := K) B,
      τ ⟨SpecialLinearGroup.map ι x, LinearPilot.map_ringHom_mem_blockSpecialLinear ι x.2⟩ =
        ⟨SpecialLinearGroup.map ι x, LinearPilot.map_ringHom_mem_blockSpecialLinear ι x.2⟩ := by
    intro x
    apply hφ₂inj
    have hττ : τ ⟨SpecialLinearGroup.map ι x, LinearPilot.map_ringHom_mem_blockSpecialLinear ι x.2⟩ =
        τ₀ ⟨SpecialLinearGroup.map ι x, LinearPilot.map_ringHom_mem_blockSpecialLinear ι x.2⟩ := rfl
    rw [hττ, hτ₀]
    change P.Φ ⟨ctufSiegel (unitaryInvolution F 2 f) hσ ε hε (SpecialLinearGroup.map ι x), _⟩ =
      S.Φ ⟨leviEmbedSL F N (SpecialLinearGroup.map ι x), _, rfl⟩
    have hxsp : leviEmbedSL K N (x : SL(N, K)) ∈ spBlock K ({k} : Finset (Fin N))ᶜ :=
      siegelBlock_le_spBlock B ⟨x, x.2, rfl⟩
    have e1 : P.Φ ⟨ctufSiegel (unitaryInvolution F 2 f) hσ ε hε
        (SpecialLinearGroup.map ι (x : SL(N, K))), ctufSiegel_mem_ctuBlock_singleton hkB
          (LinearPilot.map_ringHom_mem_blockSpecialLinear ι x.2)⟩ =
        ((e.symm (leviEmbedSL K N (x : SL(N, K))) : L) : G) :=
      P.N1' hxsp _ (ctufSiegel_map hι (x : SL(N, K)))
    have e2 : S.Φ ⟨spFieldMap N ι (leviEmbedSL K N (x : SL(N, K))),
        spFieldMap_mem_siegelLevi ι ⟨(x : SL(N, K)), rfl⟩⟩ =
        ((e.symm (leviEmbedSL K N (x : SL(N, K))) : L) : G) := S.N1 _ ⟨(x : SL(N, K)), rfl⟩
    have e3 : (⟨leviEmbedSL F N (SpecialLinearGroup.map ι (x : SL(N, K))), _, rfl⟩ :
        siegelLevi F N) = ⟨spFieldMap N ι (leviEmbedSL K N (x : SL(N, K))),
          spFieldMap_mem_siegelLevi ι ⟨(x : SL(N, K)), rfl⟩⟩ :=
      Subtype.ext (spFieldMap_leviEmbedSL ι (x : SL(N, K))).symm
    rw [e3]
    exact e1.trans e2.symm
  rcases LinearPilot.eq_one_or_eq_mapBlock_of_fix_subfield hB3 ι hσσ
    (ctuf_fix_iff hKc hF (by omega) hι) τ hfixK with h | h
  · refine ⟨false, fun A hA => ?_⟩
    have h1 := hτ₀ ⟨A, hA⟩
    have h2 : τ₀ ⟨A, hA⟩ = ⟨A, hA⟩ := h ⟨A, hA⟩
    rw [h2] at h1
    exact h1.symm
  · refine ⟨true, fun A hA => ?_⟩
    have h1 := hτ₀ ⟨A, hA⟩
    have h2 : τ₀ ⟨A, hA⟩ = LinearPilot.mapBlock (unitaryInvolution F 2 f) B ⟨A, hA⟩ :=
      h ⟨A, hA⟩
    rw [h2] at h1
    exact h1.symm

end Label

section Normalize

theorem ctuf_ctuaTwist_one_apply {F : Type} [Field F] {σ : F ≃+* F} {N ε : ℕ} {hε : ε ≤ 1}
    {hσ : ∀ c, σ (σ c) = c} (h1 : σ ((1 : Fˣ) : F) * ((1 : Fˣ) : F) = 1) (b : Bool)
    (x : SU σ (2 * N + ε)) :
    ctuaTwist hε σ hσ 1 h1 b x = bif b then ctuaBarAut σ hσ _ x else x := by
  rw [ctuaTwist, MulAut.mul_apply]
  cases b
  · apply Subtype.ext
    rw [Bool.cond_false, MulAut.one_apply, coe_ctuaConjAut, ctuaTorGL_one, one_mul, inv_one,
      mul_one]
    rfl
  · apply Subtype.ext
    rw [Bool.cond_true, coe_ctuaConjAut, ctuaTorGL_one, one_mul, inv_one, mul_one]
    rfl

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}
  {t : G}

omit [Finite K] in
theorem CtuParam.exists_siegel_normalized
    (S : SiegelFieldParam e t ι (unitaryInvolution F 2 f)) (hKc : Nat.card K = 2 ^ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hN : 4 ≤ N) {k : Fin N}
    (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k) :
    ∃ Q : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k,
      ∀ (A : SL(N, F)) (hA : A ∈ blockSpecialLinear ({k} : Finset (Fin N))ᶜ),
        Q.Φ ⟨ctufSiegel _ (unitaryInvolution_involutive hF) ε hε A,
          ctufSiegel_mem_ctuBlock_singleton (ctuf_notMem_compl_singleton k) hA⟩ =
          S.Φ ⟨leviEmbedSL F N A, A, rfl⟩ := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨b, hb⟩ := P.exists_siegel_label S hKc hF hf hN
  have h1 : unitaryInvolution F 2 f ((1 : Fˣ) : F) * ((1 : Fˣ) : F) = 1 := by
    rw [Units.val_one, map_one, one_mul]
  have hT := ctuaTwist_admissible (N := N) (hε := hε) (ι := ι) (hι := hι) (hσ := hσ) h1 b
  refine ⟨P.twistBy hT, fun A hA => ?_⟩
  rw [CtuParam.twistBy_Φ_apply]
  cases b
  · have heq : hT.restrict {k} ⟨ctufSiegel _ hσ ε hε A,
        ctufSiegel_mem_ctuBlock_singleton (ctuf_notMem_compl_singleton k) hA⟩ =
        ⟨ctufSiegel _ hσ ε hε A, ctufSiegel_mem_ctuBlock_singleton
          (ctuf_notMem_compl_singleton k) hA⟩ := by
      apply Subtype.ext
      rw [CtuaAdmissible.coe_restrict, ctuf_ctuaTwist_one_apply]
      rfl
    rw [heq, hb A hA]
    rfl
  · have hA' : SpecialLinearGroup.map (unitaryInvolution F 2 f : F →+* F) A ∈
        blockSpecialLinear ({k} : Finset (Fin N))ᶜ :=
      LinearPilot.map_ringHom_mem_blockSpecialLinear _ hA
    have heq : hT.restrict {k} ⟨ctufSiegel _ hσ ε hε A,
        ctufSiegel_mem_ctuBlock_singleton (ctuf_notMem_compl_singleton k) hA⟩ =
        ⟨ctufSiegel _ hσ ε hε (SpecialLinearGroup.map (unitaryInvolution F 2 f : F →+* F) A),
          ctufSiegel_mem_ctuBlock_singleton (ctuf_notMem_compl_singleton k) hA'⟩ := by
      apply Subtype.ext
      rw [CtuaAdmissible.coe_restrict, ctuf_ctuaTwist_one_apply]
      exact ctuaBarAut_ctufSiegel A
    rw [heq, hb _ hA']
    congr 2
    exact congrArg (leviEmbedSL F N) (ctuf_map_map hσ A)

end Normalize

end CFSG.SeitzReduction.SymplecticPilot

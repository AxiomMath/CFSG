module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.SporadicJ1
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.SporadicM11Model
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.M11Three
import CFSG.Sporadic.Bridge.M11

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open TauCeti Subgroup

@[expose] def M11Local {H : Type*} [Group H] (R S : Subgroup H) : Prop :=
  Nat.card R = 3 ^ 2 ∧ (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧ (∀ a ∈ R, a ^ 3 = 1) ∧
    Nat.card S = 16 ∧ S ≤ normalizer (R : Set H) ∧
    (∃ a ∈ S, ∃ b ∈ S, orderOf a = 8 ∧ orderOf b = 2 ∧ b * a * b⁻¹ = a ^ 3 ∧
      S = Subgroup.closure {a, b}) ∧
    (∀ a ∈ R, a ≠ 1 → ∀ b ∈ R, b ≠ 1 → ∃ n ∈ normalizer (R : Set H), n * a * n⁻¹ = b)

theorem M11Local.map {H H' : Type*} [Group H] [Group H'] {R S : Subgroup H} (e : H ≃* H')
    (h : M11Local R S) : M11Local (R.map e.toMonoidHom) (S.map e.toMonoidHom) := by
  obtain ⟨hR, hc, h3, hS, hn, ⟨a, ha, b, hb, ha8, hb2, hab, hSc⟩, htr⟩ := h
  have hnorm : normalizer ((R.map e.toMonoidHom : Subgroup H') : Set H') =
      (normalizer (R : Set H)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq R e).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hR]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show e x * e y = e y * e x
    rw [← map_mul, ← map_mul, hc x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    show (e x) ^ 3 = 1
    rw [← map_pow, h3 x hx, map_one]
  · rw [Subgroup.card_map_of_injective e.injective, hS]
  · rw [hnorm]
    exact Subgroup.map_mono hn
  · rw [MulEquiv.orderOf_eq, ha8]
  · rw [MulEquiv.orderOf_eq, hb2]
  · rw [← map_mul, ← map_inv, ← map_mul, ← map_pow, hab]
  · rw [hSc, MonoidHom.map_closure]
    congr 1
    ext z
    simp
  · rintro _ ⟨x, hx, rfl⟩ hx1 _ ⟨y, hy, rfl⟩ hy1
    obtain ⟨n, hnN, hn'⟩ := htr x hx (fun h => hx1 (by rw [h, map_one])) y hy
      (fun h => hy1 (by rw [h, map_one]))
    refine ⟨e n, ?_, ?_⟩
    · rw [hnorm]; exact ⟨n, hnN, rfl⟩
    · show e n * e x * (e n)⁻¹ = e y
      rw [← map_inv, ← map_mul, ← map_mul, hn']

theorem normalizer_card_eq_144 {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 7920)
    {R S : Subgroup X} (hR : Nat.card R = 3 ^ 2) (hS : Nat.card S = 16)
    (hSn : S ≤ normalizer (R : Set X)) (hRn : normalizer (R : Set X) ≠ ⊤) :
    Nat.card (normalizer (R : Set X)) = 144 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card X).factorization 3 = 2 := by
    rw [hX]
    exact CFSG.AGLEmbeddingD2.factorization_eq_of_pow_dvd Nat.prime_three (by norm_num)
      (by norm_num) (by norm_num)
  let R₁ : Sylow 3 X := Sylow.ofCard R (by rw [hR, hfac])
  have hmod := card_sylow_modEq_one 3 X
  have hidx : Nat.card (Sylow 3 X) = (normalizer (R : Set X)).index :=
    Sylow.card_eq_index_normalizer R₁
  rw [hidx] at hmod
  set N := normalizer (R : Set X) with hN
  have h9 : 9 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := R))
    rwa [hR] at this
  have h16 : 16 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hSn
    rwa [hS] at this
  have h144 : 144 ∣ Nat.card N := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 16) h9 h16
    simpa using this
  obtain ⟨m, hm⟩ := h144
  have hprod := N.index_mul_card
  rw [hX, hm] at hprod
  have hpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; simp at hm; exact absurd hm (Nat.card_pos).ne'
    · exact h
  have hring : N.index * (144 * m) = 144 * (N.index * m) := by ring
  have h55 : N.index * m = 55 := by omega
  have hle : N.index ≤ 55 := by
    have : N.index ≤ N.index * m := Nat.le_mul_of_pos_right _ hpos
    omega
  have hne : N.index ≠ 1 := fun h => hRn (Subgroup.index_eq_one.1 h)
  have hmod' : N.index ≡ 1 [MOD 3] := hmod
  have h3 : N.index = 55 := by
    unfold Nat.ModEq at hmod'
    have hd : N.index ∣ 55 := ⟨m, by omega⟩
    interval_cases h : N.index <;> omega
  have : m = 1 := by rw [h3] at h55; omega
  rw [hm, this]

theorem normalizer_eq_sup {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 7920)
    {R S : Subgroup X} (hR : Nat.card R = 3 ^ 2) (hS : Nat.card S = 16)
    (hSn : S ≤ normalizer (R : Set X)) (hRn : normalizer (R : Set X) ≠ ⊤) :
    normalizer (R : Set X) = R ⊔ S := by
  have hN := normalizer_card_eq_144 hX hR hS hSn hRn
  have hle : R ⊔ S ≤ normalizer (R : Set X) := sup_le Subgroup.le_normalizer hSn
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hN]
  have h9 : 9 ∣ Nat.card (R ⊔ S : Subgroup X) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : R ≤ R ⊔ S)
    rwa [hR] at this
  have h16 : 16 ∣ Nat.card (R ⊔ S : Subgroup X) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : S ≤ R ⊔ S)
    rwa [hS] at this
  have h144 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 16) h9 h16
  exact Nat.le_of_dvd Nat.card_pos (by simpa using h144)

theorem actsIrr_of_sup {X : Type*} [Group X] {R S : Subgroup X}
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hN : normalizer (R : Set X) = R ⊔ S)
    (hSn : S ≤ normalizer (R : Set X))
    (htr : ∀ a ∈ R, a ≠ 1 → ∀ b ∈ R, b ≠ 1 → ∃ n ∈ normalizer (R : Set X), n * a * n⁻¹ = b) :
    ActsIrr S R := by
  intro W hWR hSW
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨⟨w, hwW⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hW
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  refine le_antisymm hWR fun r hr => ?_
  by_cases hr1 : r = 1
  · rw [hr1]; exact W.one_mem
  obtain ⟨n, hnN, hn⟩ := htr w (hWR hwW) hw1' r hr hr1
  rw [hN, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left R S hSn] at hnN
  obtain ⟨x, hxR, y, hyS, rfl⟩ := hnN
  have hyw : y * w * y⁻¹ ∈ W := (mem_normalizer_iff.1 (hSW hyS) w).1 hwW
  have hyR : y * w * y⁻¹ ∈ R := hWR hyw
  have : x * y * w * (x * y)⁻¹ = y * w * y⁻¹ := by
    calc x * y * w * (x * y)⁻¹ = x * (y * w * y⁻¹) * x⁻¹ := by group
      _ = y * w * y⁻¹ := by
        rw [hRc x hxR _ hyR, mul_assoc, mul_inv_cancel, mul_one]
  rw [← hn, this]
  exact hyw

theorem gls3ConclusionPlus_M11
    {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hKn : K.Normal) (hiso : Nonempty (↥K ≃* (CFSGIndex.sporadic SporadicName.M11).Group))
    (hKc : Subgroup.centralizer (K : Set X) = ⊥) (P : Sylow 3 X)
    (hP : 2 ≤ CFSG.Open.pRank 3 (P : Subgroup X)) (hΓ : gammaCore 3 1 ⊤ (P : Subgroup X) < ⊤) :
    Gls3ConclusionPlus X K (P : Subgroup X) := by
  have hKF := CFSG.AGLEmbeddingD2.kFactM11Three
  have := hKn
  have hOutK := (hKF K hiso).1
  have hinner : ∀ φ : MulAut ↥K, ∃ k : ↥K, φ = MulAut.conj k := by
    intro φ
    have h1 : (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K).index = 1 := hOutK
    have h2 := Subgroup.index_eq_one.1 h1
    have h3 : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K := by
      rw [h2]; trivial
    obtain ⟨k, hk⟩ := h3
    exact ⟨k, hk.symm⟩
  have htop : K = ⊤ := eq_top_of_forall_inner hinner hKc
  subst htop
  obtain ⟨eK⟩ := hiso
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  let eXG : X ≃* CFSG.Blueprint.NativeSporadic.M11 :=
    Subgroup.topEquiv.symm.trans (eK.trans f.symm)
  have hX : Nat.card X = 7920 := by
    rw [Nat.card_congr eXG.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M11
  obtain ⟨-, hSyl⟩ := hKF X ⟨eXG.trans f⟩
  obtain ⟨hPc, hPC, hPmax⟩ := hSyl P
  obtain ⟨R₀, S₀, hR₀, hc₀, h3₀, hS₀, hn₀, hab₀, htr₀⟩ :=
    M11Model.exists_m11_local_data
  have hloc : M11Local R₀ S₀ := ⟨hR₀, hc₀, h3₀, hS₀, hn₀, hab₀, htr₀⟩
  have hfac : (Nat.card X).factorization 3 = 2 := by
    rw [hX]
    exact CFSG.AGLEmbeddingD2.factorization_eq_of_pow_dvd Nat.prime_three (by norm_num)
      (by norm_num) (by norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let R₁ : Sylow 3 X := Sylow.ofCard (R₀.map eXG.symm.toMonoidHom) (by
    rw [Subgroup.card_map_of_injective eXG.symm.injective, hR₀, hfac])
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X R₁ P
  let ψ : CFSG.Blueprint.NativeSporadic.M11 ≃* X := eXG.symm.trans (MulAut.conj c)
  have hPψ : (P : Subgroup X) = R₀.map ψ.toMonoidHom := by
    have h1 : (P : Subgroup X) =
        (R₀.map eXG.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom := by
      rw [← hc, Sylow.coe_subgroup_smul]
      rfl
    rw [h1, Subgroup.map_map]
    rfl
  have hlocX := hloc.map ψ
  rw [← hPψ] at hlocX
  set Sx : Subgroup X := S₀.map ψ.toMonoidHom with hSx
  obtain ⟨-, hcommX, hcubeX, hSx16, hSxn, hab, htr⟩ := hlocX
  have hNle : normalizer ((P : Subgroup X) : Set X) ≤ gammaCore 3 1 ⊤ (P : Subgroup X) := by
    intro x hx
    refine Subgroup.subset_closure ⟨Subgroup.mem_top x, P, le_rfl, by omega, hx⟩
  have hΓN : gammaCore 3 1 ⊤ (P : Subgroup X) = normalizer ((P : Subgroup X) : Set X) := by
    rcases hPmax _ hNle with h | h
    · exact h
    · exact absurd h hΓ.ne
  have hNne : normalizer ((P : Subgroup X) : Set X) ≠ ⊤ := fun h => hΓ.ne (by rw [hΓN, h])
  have hN := normalizer_eq_sup hX hPc hSx16 hSxn hNne
  have hirr : ActsIrr Sx P := actsIrr_of_sup hcommX hN hSxn htr
  have hbot : Sx ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) = ⊥ := by
    have hcard : Nat.card ↥(Sx ⊓ (P : Subgroup X)) = 1 := by
      have h1 : Nat.card ↥(Sx ⊓ (P : Subgroup X)) ∣ 16 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : Sx ⊓ (P : Subgroup X) ≤ Sx)
        rwa [hSx16] at this
      have h2 : Nat.card ↥(Sx ⊓ (P : Subgroup X)) ∣ 3 ^ 2 := by
        have := Subgroup.card_dvd_of_le (inf_le_right : Sx ⊓ (P : Subgroup X) ≤ P)
        rwa [hPc] at this
      exact Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 16 (3 ^ 2)) h1 h2
    have hb : Sx ⊓ (P : Subgroup X) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
    rw [eq_bot_iff, ← hb]
    exact inf_le_inf_left _ hPC
  unfold Gls3ConclusionPlus
  simp only [inf_top_eq, top_inf_eq]
  refine ⟨hΓ, ?_, ?_⟩
  · intro H hH _
    rcases hPmax H (by rw [← hΓN]; exact hH.le) with h | h
    · exact absurd (hΓN ▸ h ▸ rfl) hH.ne
    · exact h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
    refine ⟨⟨eK⟩, trivial, ⟨⟨⟨fun a b => Subtype.ext (hcommX a a.2 b b.2)⟩⟩, hcubeX⟩,
      by rw [hPc]; norm_num, ?_, Sx, ?_, ?_, hSx16, hab, hbot, hirr⟩
    · rw [hΓN]
    · rw [hΓN]; exact hSxn
    · rw [hΓN, hN]

theorem gls3PlusCase_M11 :
    Gls3PlusCase (.sporadic .M11) := by
  unfold Gls3PlusCase
  intro X _ _ _ K hKn _ _ hiso hKc P hP hΓ
  exact gls3ConclusionPlus_M11 hKn hiso hKc P hP hΓ

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

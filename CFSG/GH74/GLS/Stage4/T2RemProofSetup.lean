module

public import CFSG.GH74.GLS.Stage4.T2Steps
public import CFSG.GH74.GLS.Stage4.T2Norm
public import CFSG.GH74.GLS.Stage4.T2Sylow
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylFwd

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.BNPair CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl CFSG.Blueprint

namespace CFSG.GH74.GLS.Stage4.Rest.Rem

section General

variable {G : Type} [Group G]

theorem conj_mem_of_relIndex_two {K C : Subgroup G} (hKC : K ≤ C) (h : K.relIndex C = 2) :
    ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  intro c hc k hk
  have hn : (K.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two h
  have := hn.conj_mem ⟨k, hKC hk⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨c, hc⟩
  simpa using Subgroup.mem_subgroupOf.1 this

theorem eq_top_of_relIndex_two {K H C : Subgroup G} (hKH : K ≤ H) (hHC : H ≤ C) (h : K.relIndex C = 2)
    (hne : H ≠ K) : H = C := by
  have h1 := Subgroup.relIndex_mul_relIndex K H C hKH hHC
  rw [h] at h1
  have hd : K.relIndex H ∣ 2 := ⟨H.relIndex C, h1.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1' | h2'
  · exfalso
    exact hne (le_antisymm (Subgroup.relIndex_eq_one.1 h1') hKH)
  · rw [h2'] at h1
    have : H.relIndex C = 1 := by omega
    exact le_antisymm hHC (Subgroup.relIndex_eq_one.1 this)

theorem sylow_inf_relIndex_two {K C S : Subgroup G} (hKC : K ≤ C) (hSC : S ≤ C) (h : K.relIndex C = 2)
    (hS : ¬ 2 ∣ S.relIndex C) : (S ⊓ K).relIndex S = 2 := by
  have hSK : ¬ S ≤ K := by
    intro hle
    apply hS
    rw [← Subgroup.relIndex_mul_relIndex S K C hle hKC, h]
    exact dvd_mul_left 2 _
  obtain ⟨x, hxS, hxK⟩ := Set.not_subset.1 hSK
  have hout : ∀ s ∈ S, s ∉ K → s * x ∈ K := by
    intro s hs hsK
    have := t2C_outer_coset h (hSC hs) (C.inv_mem (hSC hxS)) hsK (fun h' => hxK (by simpa using K.inv_mem h'))
    simpa using this
  show ((S ⊓ K).subgroupOf S).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨x, hxS⟩, fun b => ?_⟩
  rcases b with ⟨s, hs⟩
  by_cases hsK : s ∈ K
  · have h1 : (⟨s, hs⟩ : ↥S) ∈ (S ⊓ K).subgroupOf S := Subgroup.mem_subgroupOf.2 ⟨hs, hsK⟩
    have h2 : (⟨s, hs⟩ * ⟨x, hxS⟩ : ↥S) ∉ (S ⊓ K).subgroupOf S := by
      intro h'
      have := (Subgroup.mem_subgroupOf.1 h').2
      exact hxK (by simpa using K.mul_mem (K.inv_mem hsK) this)
    exact Or.inr ⟨h1, h2⟩
  · have h1 : (⟨s, hs⟩ : ↥S) ∉ (S ⊓ K).subgroupOf S := fun h' => hsK (Subgroup.mem_subgroupOf.1 h').2
    have h2 : (⟨s, hs⟩ * ⟨x, hxS⟩ : ↥S) ∈ (S ⊓ K).subgroupOf S :=
      Subgroup.mem_subgroupOf.2 ⟨S.mul_mem hs hxS, hout s hs hsK⟩
    exact Or.inl ⟨h2, h1⟩

theorem factorization_card_sl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)).factorization 2 =
      ((Nat.card F) ^ 2 - 1).factorization 2 := by
  have hq : 0 < Nat.card F := Nat.card_pos
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have hne : (Nat.card F) ^ 2 - 1 ≠ 0 := by
    have : 1 < (Nat.card F) ^ 2 := Nat.one_lt_pow (by norm_num) h1
    omega
  rw [t2C_card_sl2, Nat.factorization_mul hq.ne' hne]
  have hnd : ¬ 2 ∣ Nat.card F := by
    intro h
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  simp [Nat.factorization_eq_zero_of_not_dvd hnd]

end General

section Setup

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem sylow_inf_K (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) {S : Subgroup G}
    (hS : IsSylowOf 2 S (oPrimeResidualOf 2 (centralizer ({z} : Set G)))) :
    (S ⊓ (K₁ ⊔ K₂)).relIndex S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact sylow_inf_relIndex_two hSet.le_residual hS.le hSet.index_two ((isSylowOf_iff).1 hS).2.2

omit [Finite G] in
theorem nonempty_equiv_of_conj {S S₀ : Subgroup G} {k : G} (h : ∀ x, x ∈ S ↔ k⁻¹ * x * k ∈ S₀) :
    Nonempty (↥S ≃* ↥S₀) := by
  have hS : S = S₀.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [h x, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨k⁻¹ * x * k, hx, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨y, hy, rfl⟩
      have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
      simpa [MulAut.conj_apply, e] using hy
  subst hS
  exact ⟨((MulAut.conj k).subgroupMap S₀).symm⟩

theorem isSylowOf_C1 (S : Sylow 2 G) (hSz : ∀ s ∈ (S : Subgroup G), s * z = z * s) :
    IsSylowOf 2 (S : Subgroup G) (oPrimeResidualOf 2 (centralizer ({z} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := le_oPrimeResidualOf_centralizer S.isPGroup' hSz
  refine (isSylowOf_iff).2 ⟨hle, S.isPGroup', ?_⟩
  intro h
  exact S.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hle))

end Setup

section Shape


variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

omit [Finite G] in
theorem exists_shape (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) :
    ∃ (S : Sylow 2 G) (S' : Sylow 2 Gs) (A : Subgroup Gs) (a t y : Gs) (n : ℕ),
      Nonempty (↥(S : Subgroup G) ≃* ↥(S' : Subgroup Gs)) ∧ 2 ≤ n ∧
      ShapeConds (S' : Subgroup Gs) A a t y n ∧
      (Nat.card ↥K₁).factorization 2 = n + 1 ∧ (Nat.card ↥K₂).factorization 2 = n + 1 := by
  obtain ⟨S, S', hSS'⟩ := hSet.S_iso
  obtain ⟨p, f, F, iF, fF, hp, hp2, hL, hF, hs₁, hs₂⟩ := hSet.model
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := Finite.one_lt_card (α := F)
      simp [hF] at this
    · exact h
  have hm : ChevalleyExceptionalModel Gs .G2 p f := by
    rcases hL with ⟨ht, -⟩ | ⟨-, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact hm
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hm.2
  have : Finite Gs := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨A, a, t, y, n, hn, hsc, hval⟩ := g2_sylow_shapeConds_fwd Gs p f hp hp2 hf hL S'
  have := hSet.finite₁
  have := hSet.finite₂
  have hoddF : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have hFv : (Nat.card ↥(StatedSL 2 F)).factorization 2 = n + 1 := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv, factorization_card_sl2 hoddF,
      hF, hval]
  have hK : ∀ (K : Subgroup G) (E : Type) [Field E] [Finite E],
      Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 2) E) →
      (Nat.card ↥(StatedSL 2 E)).factorization 2 = n + 1 → (Nat.card ↥K).factorization 2 = n + 1 := by
    intro K E _ _ ⟨eK⟩ hv
    rw [Nat.card_congr (eK.toEquiv.trans (specialLinearGroupEquivStatedSL 2 E).toEquiv)]
    exact hv
  exact ⟨S, S', A, a, t, y, n, hSS', hn, hsc, hK K₁ F₁ hSet.iso₁ (hs₁.trans hFv),
    hK K₂ F₂ hSet.iso₂ (hs₂.trans hFv)⟩

theorem exists_data (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) :
    ∃ (n : ℕ) (S₀ : Subgroup G) (S' A : Subgroup Gs) (a t y : Gs),
      2 ≤ n ∧ IsSylowOf 2 S₀ (oPrimeResidualOf 2 (centralizer ({z} : Set G))) ∧ z ∈ S₀ ∧
        (∀ s ∈ S₀, s * z = z * s) ∧ Nonempty (↥S₀ ≃* ↥S') ∧ ShapeConds S' A a t y n ∧
        (Nat.card ↥K₁).factorization 2 = n + 1 ∧ (Nat.card ↥K₂).factorization 2 = n + 1 := by
  obtain ⟨S₁, S', A, a, t, y, n, ⟨φ⟩, hn, hsc, hv₁, hv₂⟩ := exists_shape hSet
  obtain ⟨-, S₀, hzS, hSz⟩ := hSet.central
  exact ⟨n, (S₀ : Subgroup G), (S' : Subgroup Gs), A, a, t, y, hn, isSylowOf_C1 S₀ hSz, hzS, hSz,
    ⟨(Sylow.equiv S₀ S₁).trans φ⟩, hsc, hv₁, hv₂⟩

end Shape

section Invol

variable {X : Type*} [Group X]

theorem exists_invol_not_mem_shape {S A : Subgroup X} {a t y : X} {n : ℕ}
    (h : ShapeConds S A a t y n) {N : Subgroup X} (hNS : N ≤ S) (hN : N ≠ S) :
    ∃ s ∈ S, s * s = 1 ∧ s ∉ N := by
  obtain ⟨ha, hA, hab, hcomm, htt, hyy, hty, ht1, hy1, hty', hAty, hyA, hS⟩ := h
  by_contra hcon
  push Not at hcon
  have hAS : A ≤ S := by rw [hS]; exact le_sup_left.trans le_sup_left
  have htS : t ∈ S := by rw [hS]; exact (Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers t)))
  have hyS : y ∈ S := by rw [hS]; exact Subgroup.mem_sup_right (mem_zpowers y)
  have haA : a ∈ A := by rw [hA]; exact Subgroup.mem_sup_left (mem_zpowers a)
  have htN : t ∈ N := hcon t htS htt
  have hyN : y ∈ N := hcon y hyS hyy
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hay : a * y ∈ N := by
    refine hcon (a * y) (S.mul_mem (hAS haA) hyS) ?_
    have := hyA a haA
    calc a * y * (a * y) = a * (y * a * y) := by group
      _ = 1 := by rw [this]; group
  have haN : a ∈ N := by
    have := N.mul_mem hay (N.inv_mem hyN)
    simpa using this
  have hbN : t⁻¹ * a * t ∈ N := N.mul_mem (N.mul_mem (N.inv_mem htN) haN) htN
  have hAN : A ≤ N := by
    rw [hA]
    exact sup_le ((Subgroup.zpowers_le).2 haN) ((Subgroup.zpowers_le).2 hbN)
  have hSN : S ≤ N := by
    rw [hS]
    exact sup_le (sup_le hAN ((Subgroup.zpowers_le).2 htN)) ((Subgroup.zpowers_le).2 hyN)
  exact hN (le_antisymm hNS hSN)

end Invol

section Transport

variable {G : Type} [Group G] {Gs : Type} [Group Gs]

theorem exists_invol_not_mem_of_equiv {S₀ : Subgroup G} {S' A : Subgroup Gs} {a t y : Gs} {n : ℕ}
    (h : ShapeConds S' A a t y n) (φ : ↥S₀ ≃* ↥S') {N : Subgroup G} (hNS : N ≤ S₀) (hN : N ≠ S₀) :
    ∃ s ∈ S₀, s * s = 1 ∧ s ∉ N := by
  set M : Subgroup Gs := (N.subgroupOf S₀).map (S'.subtype.comp φ.toMonoidHom) with hM
  have hMS : M ≤ S' := by
    rintro _ ⟨x, -, rfl⟩
    exact (φ x).2
  have hMne : M ≠ S' := by
    intro hMS'
    apply hN
    refine le_antisymm hNS (fun s hs => ?_)
    have : ((φ ⟨s, hs⟩ : ↥S') : Gs) ∈ M := by rw [hMS']; exact (φ ⟨s, hs⟩).2
    obtain ⟨x, hx, hxs⟩ := this
    have hxs' : φ x = φ ⟨s, hs⟩ := Subtype.ext hxs
    have : x = ⟨s, hs⟩ := φ.injective hxs'
    rw [this] at hx
    exact Subgroup.mem_subgroupOf.1 hx
  obtain ⟨s', hs'S, hs'sq, hs'M⟩ := exists_invol_not_mem_shape h hMS hMne
  refine ⟨((φ.symm ⟨s', hs'S⟩ : ↥S₀) : G), (φ.symm ⟨s', hs'S⟩).2, ?_, ?_⟩
  · have h1 : φ (φ.symm ⟨s', hs'S⟩ * φ.symm ⟨s', hs'S⟩) = 1 := by
      rw [map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext hs'sq
    have h2 : φ.symm ⟨s', hs'S⟩ * φ.symm ⟨s', hs'S⟩ = 1 := by
      apply φ.injective
      rw [h1, map_one]
    have := congrArg Subtype.val h2
    simpa using this
  · intro hsN
    apply hs'M
    refine ⟨φ.symm ⟨s', hs'S⟩, Subgroup.mem_subgroupOf.2 hsN, ?_⟩
    simp

end Transport

section Reduction

@[expose] def Ch6T2RemDiag : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type)
      [Field F₁] [Field F₂], Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ →
        ∀ t : G, t * t = 1 → t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) → t ∉ K₁ ⊔ K₂ →
          (∃ (e : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁) (g : GL (Fin 2) F₁),
            ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : F₁ˣ) : F₁) ∧ ActsAsConj t K₁ e g) ∧
          (∃ (e : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) (g : GL (Fin 2) F₂),
            ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : F₂ˣ) : F₂) ∧ ActsAsConj t K₂ e g)


theorem ch6T2Rem_of_diag (hD : Ch6T2RemDiag) : Ch6T2Rem := by
  intro G _ _ hStd hr Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ hSet
  obtain ⟨n, S₀, S', A, a, t, y, hn, hSyl, hzS, hSz, ⟨φ⟩, hsc, -, -⟩ := exists_data hSet
  have hidx := sylow_inf_K hSet hSyl
  have hN : S₀ ⊓ (K₁ ⊔ K₂) ≠ S₀ := by
    intro h
    rw [h, Subgroup.relIndex_self] at hidx
    omega
  obtain ⟨s, hsS, hss, hsN⟩ := exists_invol_not_mem_of_equiv hsc φ inf_le_left hN
  have hsK : s ∉ K₁ ⊔ K₂ := fun h => hsN ⟨hsS, h⟩
  have hsC : s ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := hSyl.le hsS
  obtain ⟨hd₁, hd₂⟩ := hD G hStd hr Gs q₁ q₂ z K₁ K₂ F₁ F₂ hSet s hss hsC hsK
  refine ⟨s, hSz s hsS, hss, ?_, hd₁, hd₂⟩
  refine eq_top_of_relIndex_two (K := K₁ ⊔ K₂) (H := K₁ ⊔ K₂ ⊔ Subgroup.zpowers s) le_sup_left
    (sup_le hSet.le_residual ((Subgroup.zpowers_le).2 hsC)) hSet.index_two ?_
  intro h
  exact hsK (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers s))

end Reduction

end CFSG.GH74.GLS.Stage4.Rest.Rem

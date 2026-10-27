module

public import CFSG.GH74.GLS.C3.Layer1.Th2Tstar
public import CFSG.GH74.GLS.C3.Layer1.Th2ConnRows
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseI
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5

public section

namespace CFSG.GH74.GLS.Th2.P812

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2

variable {G : Type} [Group G]

theorem isElementaryAbelian_omega1_of_comm {Z : Subgroup G}
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) :
    CFSG.IsElementaryAbelian 2 ↥(omega1 Z) := by
  have hle : omega1 Z ≤ Z := (Subgroup.closure_le Z).2 fun u hu => hu.1
  have hsq : ∀ u ∈ omega1 Z, u * u = 1 := by
    intro u hu
    refine Subgroup.closure_induction (p := fun u _ => u ∈ Z ∧ u * u = 1) ?_ ?_ ?_ ?_ hu |>.2
    · intro u hu
      exact ⟨hu.1, hu.2⟩
    · exact ⟨Z.one_mem, by simp⟩
    · rintro a b - - ⟨haZ, ha⟩ ⟨hbZ, hb⟩
      refine ⟨Z.mul_mem haZ hbZ, ?_⟩
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hZ b hbZ a haZ]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]
    · rintro a - ⟨haZ, ha⟩
      refine ⟨Z.inv_mem haZ, ?_⟩
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [ha]; simp
  exact C3.Layer1.Back.isElementaryAbelian_of_forall
    (fun u hu v hv => hZ u (hle hu) v (hle hv)) hsq

theorem exists_central_involution [Finite G] {H : Subgroup G} (hH : IsPGroup 2 ↥H) (hne : H ≠ ⊥) :
    ∃ z ∈ H, orderOf z = 2 ∧ ∀ h ∈ H, z * h = h * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup G := H ⊓ centralizer (H : Set G) with hZ
  have hZH : Z ≤ H := inf_le_left
  have hZne : Z ≠ ⊥ := by
    intro hZbot
    have hnt : Nontrivial ↥H := by
      rw [← Subgroup.nontrivial_iff_ne_bot] at hne
      exact hne
    have := hH.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center ↥H)
    have hcZ : (c : ↥H).1 ∈ Z := by
      refine Subgroup.mem_inf.2 ⟨(c : ↥H).2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      have := Subgroup.mem_center_iff.1 c.2 ⟨h, hh⟩
      exact congrArg Subtype.val this
    rw [hZbot, Subgroup.mem_bot] at hcZ
    apply hc1
    apply Subtype.ext
    exact Subtype.ext hcZ
  obtain ⟨u, huZ, hu2⟩ := exists_involution_mem (hH.to_le hZH) hZne
  exact ⟨u, huZ.1, hu2, fun h hh => (Subgroup.mem_centralizer_iff.1 huZ.2 h hh).symm⟩

theorem exists_char_elem [Finite G] {H : Subgroup G} (hH : IsPGroup 2 ↥H) (hne : H ≠ ⊥) :
    ∃ V : Subgroup G, V ≤ H ∧ CFSG.IsElementaryAbelian 2 ↥V ∧ V ≠ ⊥ ∧
      normalizer (H : Set G) ≤ normalizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup G := H ⊓ centralizer (H : Set G) with hZ
  have hZH : Z ≤ H := inf_le_left
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 hb.2 a ha.1
  refine ⟨omega1 Z, ?_, isElementaryAbelian_omega1_of_comm hZc, ?_, ?_⟩
  · exact ((Subgroup.closure_le H).2 fun u hu => hZH hu.1)
  · obtain ⟨z, hzH, hz2, hzc⟩ := exists_central_involution hH hne
    intro hbot
    have hzZ : z ∈ Z := Subgroup.mem_inf.2 ⟨hzH, Subgroup.mem_centralizer_iff.2 fun h hh =>
      (hzc h hh).symm⟩
    have hz : z ∈ omega1 Z := Subgroup.subset_closure ⟨hzZ, by
      have := pow_orderOf_eq_one z
      rwa [hz2, sq] at this⟩
    rw [hbot, Subgroup.mem_bot] at hz
    rw [hz, orderOf_one] at hz2
    omega
  · intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
    have hH' : H.map (MulAut.conj g).toMonoidHom = H := hg
    have hZ' : Z.map (MulAut.conj g).toMonoidHom = Z := by
      rw [hZ, ← Th2Tstar.inf_centralizer_map (MulAut.conj g) H H, hH']
    have := Th2Tstar.omega1_map (MulAut.conj g) Z
    rw [hZ'] at this
    exact this.symm

theorem gammaK_le_of_forall_elem [Finite G] {Q M : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (h : ∀ V : Subgroup G, V ≤ Q → CFSG.IsElementaryAbelian 2 ↥V → V ≠ ⊥ →
      normalizer (V : Set G) ≤ M) : gammaK 2 Q 1 ≤ M := by
  unfold gammaK
  refine iSup₂_le fun H hHQ => iSup_le fun hrk => ?_
  have hHne : H ≠ ⊥ := Th2.CaseI.ne_bot_of_one_le_pRank hrk
  obtain ⟨V, hVH, hVel, hVne, hnorm⟩ := exists_char_elem (hQ.to_le hHQ) hHne
  exact hnorm.trans (h V (hVH.trans hHQ) hVel hVne)

theorem exists_conj_sylow_normalizer [Finite G] {Q C : Subgroup G} (hQC : IsSylowOf 2 Q C)
    {V : Subgroup G} (hVQ : V ≤ Q) :
    ∃ g ∈ C, V.map (MulAut.conj g).toMonoidHom ≤ Q ∧
      IsSylowOf 2 (normalizer ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ⊓ Q)
        (normalizer ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ⊓ C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := normalizer (V : Set G) with hN
  have hQ2 : IsPGroup 2 ↥Q := hQC.isPGroup
  have hQ1le : N ⊓ Q ≤ N ⊓ C := inf_le_inf_left _ hQC.le
  have hQ12 : IsPGroup 2 ↥(N ⊓ Q) := hQ2.to_le inf_le_right
  obtain ⟨S₁, hS₁le, hS₁⟩ : ∃ S₁ : Subgroup G, N ⊓ Q ≤ S₁ ∧ IsSylowOf 2 S₁ (N ⊓ C) := by
    have h2 : IsPGroup 2 ↥((N ⊓ Q).subgroupOf (N ⊓ C)) := hQ12.comap_subtype
    obtain ⟨S, hS⟩ := h2.exists_le_sylow
    refine ⟨(S : Subgroup ↥(N ⊓ C)).map (N ⊓ C).subtype, ?_, ⟨S, rfl⟩⟩
    intro q hq
    have := hS (show (⟨q, hQ1le hq⟩ : ↥(N ⊓ C)) ∈ (N ⊓ Q).subgroupOf (N ⊓ C) from hq)
    exact ⟨⟨q, hQ1le hq⟩, this, rfl⟩
  obtain ⟨g, hgC, hgS⟩ := Th2.exists_cj_le_of_isSylowOf hQC (hS₁.le.trans inf_le_right) hS₁.isPGroup
  refine ⟨g, hgC, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hgS ⟨v, hS₁le ⟨Subgroup.le_normalizer hv, hVQ hv⟩, rfl⟩
  · set φ : G →* G := (MulAut.conj g).toMonoidHom with hφ
    have hφinj : Function.Injective φ := (MulAut.conj g).injective
    set V' : Subgroup G := V.map φ with hV'
    have hN' : normalizer (V' : Set G) = N.map φ :=
      (Subgroup.map_normalizer_eq_of_bijective V (MulAut.conj g).bijective).symm
    have hCg : C.map φ = C := cj_eq_of_mem_normalizer (Subgroup.le_normalizer hgC)
    have hNC : normalizer (V' : Set G) ⊓ C = (N ⊓ C).map φ := by
      rw [hN', Subgroup.map_inf _ _ _ hφinj, hCg]
    have hSyl : IsSylowOf 2 (S₁.map φ) (normalizer (V' : Set G) ⊓ C) := by
      rw [hNC]
      refine isSylowOf_of_card (Subgroup.map_mono hS₁.le) ?_
      rw [Subgroup.card_map_of_injective hφinj, Subgroup.card_map_of_injective hφinj]
      exact hS₁.card_eq
    have hS₁N : S₁.map φ ≤ normalizer (V' : Set G) := by
      rw [hN']
      exact Subgroup.map_mono (hS₁.le.trans inf_le_left)
    have hle : S₁.map φ ≤ normalizer (V' : Set G) ⊓ Q := le_inf hS₁N hgS
    have hQ'2 : IsPGroup 2 ↥(normalizer (V' : Set G) ⊓ Q) := hQ2.to_le inf_le_right
    have heq := hSyl.eq_of_le hle (inf_le_inf_left _ hQC.le) hQ'2
    rw [heq]
    exact hSyl

theorem isS_of_isE_rank [Finite G] (hG : C3Hyp G) {X A : Subgroup G} (hAX : A ≤ X)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hA4 : 4 ≤ pRank 2 ↥A) : IsS X A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAc, hAs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hAel
  refine ⟨hAX, hAel, le_antisymm ?_ ?_⟩
  · refine le_of_eq_of_le rfl ?_
    exact le_omega1_of_isElementaryAbelian hAel (le_inf hAX (fun a ha => by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hAc b hb a ha))
  · refine (Subgroup.closure_le A).2 ?_
    rintro u ⟨⟨huX, huC⟩, hu2⟩
    by_contra huA
    have hucomm : ∀ a ∈ A, a * u = u * a := fun a ha =>
      Subgroup.mem_centralizer_iff.1 huC a ha
    have hu1 : u ≠ 1 := fun h => huA (h ▸ A.one_mem)
    have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
    have hzel := isElementaryAbelian_zpowers_of_orderOf_two hu2'
    have hcd : CommDisj A (zpowers u) := by
      refine ⟨fun a ha z hz => ?_, eq_bot_iff.2 fun z hz => ?_⟩
      · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hz
        exact (Commute.zpow_right (hucomm a ha) m).eq
      · rcases mem_zpowers_two hu2' hz.2 with h0 | h0
        · simp [h0]
        · exact absurd (h0 ▸ hz.1) huA
    have hrk := hcd.pRank_sup hAel hzel le_rfl le_rfl
    rw [pRank_zpowers_of_orderOf_two hu2'] at hrk
    have h4 := pRank_le_top' (A ⊔ zpowers u)
    have h5 := hG.pRank_eq_four
    omega

theorem two_le_pRank_of_isS [Finite G] {Q E : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hrk : 2 ≤ pRank 2 ↥Q) (hE : IsS Q E) : 2 ≤ pRank 2 ↥E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hEQ, hEel, hEeq⟩ := hE
  obtain ⟨W, hWQ, hWel, hW4⟩ := Th2.CaseI.exists_elemAbelian_four hrk
  have hQne : Q ≠ ⊥ := Th2.CaseI.ne_bot_of_one_le_pRank (by omega)
  obtain ⟨z, hzQ, hz2, hzc⟩ := exists_central_involution hQ hQne
  have hzE : z ∈ E := by
    rw [hEeq]
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨hzQ, Subgroup.mem_centralizer_iff.2 fun e he =>
      (hzc e (hEQ he)).symm⟩, ?_⟩
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  by_contra hlt
  push Not at hlt
  have hEcard : Nat.card ↥E ≤ 2 := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hEel]
    calc 2 ^ pRank 2 ↥E ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 := by norm_num
  have hzp : zpowers z = E := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hzE) ?_
    rw [Nat.card_zpowers, hz2]
    exact hEcard
  have hWE : W ≤ E := by
    intro w hw
    have hwsq : w * w = 1 := (C3.Layer1.Back.forall_of_isElementaryAbelian hWel).2 w hw
    rw [hEeq]
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨hWQ hw, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩, hwsq⟩
    rw [← hzp] at he
    rcases mem_zpowers_two hz2 he with h0 | h0
    · rw [h0]; simp
    · rw [h0]
      exact hzc w (hWQ hw)
  have := Subgroup.card_le_of_le hWE
  omega

theorem one_le_pRank_of_ne_bot [Finite G] {V : Subgroup G} (hel : CFSG.IsElementaryAbelian 2 ↥V)
    (hne : V ≠ ⊥) : 1 ≤ pRank 2 ↥V := by
  by_contra h
  have h0 : pRank 2 ↥V = 0 := by omega
  have := C3.Layer1.Back.card_eq_two_pow_pRank hel
  rw [h0, pow_zero] at this
  exact hne (Subgroup.eq_bot_of_card_eq V this)

end CFSG.GH74.GLS.Th2.P812

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

@[expose] def B_thm2_p812_NV : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G),
    Th2Std x y K T S → HasL2Model (kBar K) Odd → K ≤ M → T ≤ M →
      IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K) →
        ∀ V : Subgroup G, V ≤ T ⊓ CxK x K → CFSG.IsElementaryAbelian 2 ↥V → V ≠ ⊥ →
          IsSylowOf 2 (normalizer (V : Set G) ⊓ (T ⊓ CxK x K))
            (normalizer (V : Set G) ⊓ CMbar M K) →
          pPrimeCoreOf 2 (normalizer (V : Set G)) ≤ M →
          ∀ U : Subgroup G, IsFourSub (T ⊓ K) U →
            normalizer ((U ⊔ V : Subgroup G) : Set G) ≤ M →
            normalizer (((T ⊓ K) ⊔ (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)) : Subgroup G) :
              Set G) ≤ M →
              normalizer (V : Set G) ≤ M

@[expose] def B_thm2_p812_A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G) (ρ : Th2Row)
    (B : Subgroup G), Th2M2 x y K T S M ρ B → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
      K ≤ M → IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K) →
        ∀ L : Subgroup G, IsMinSubnormalIn K M L → IsPCompIn 2 M L → L = pPrimeCoreOf 2 L ⊔ K →
          2 ≤ pRank 2 ↥(T ⊓ CxK x K) → gammaK 2 (T ⊓ CxK x K) 1 ≤ M

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2.P812

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2

variable {G : Type} [Group G]

theorem l812_row_data [Finite G] (h82 : B_thm2_l82) (hG : C3Hyp G) {x y : G} {K T S M : Subgroup G}
    {ρ : Th2Row} {B : Subgroup G} (h2 : Th2M2 x y K T S M ρ B)
    (hρ : ρ = .r1b ∨ ρ = .r2 ∨ ρ = .r4b ∨ ρ = .r4c) :
    ∃ r : ℕ, r ≤ 3 ∧
      (∀ A' : Subgroup G, A' ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) → CFSG.IsElementaryAbelian 2 ↥A' →
        4 ≤ pRank 2 ↥A' → A' ≤ ρ.Tstar x K T S) ∧
      gammaK 2 (ρ.Tstar x K T S) 4 ≤ M ∧
      (∀ A : Subgroup G, IsE 4 (ρ.Tstar x K T S) A → gammaK 2 A r ≤ M) := by
  have h82' := h82 G hG x y K T S M ρ B h2
  have hRT : (T ⊓ K) ⊔ (T ⊓ CxK x K) ≤ T := sup_le inf_le_left inf_le_left
  rcases hρ with rfl | rfl | rfl | rfl
  · refine ⟨3, le_rfl, fun A' hA'R hel hrk => ?_, h82'.2.1, h82'.2.2.1⟩
    have hmem : A' ∈ Th2Row.r1b.BT x K T S := ⟨isS_of_isE_rank hG hA'R hel hrk, hrk⟩
    exact le_iSup₂_of_le A' hmem le_rfl
  · refine ⟨3, le_rfl, fun A' hA'R hel hrk => ?_, h82'.2.1, h82'.2.2.1⟩
    have hmem : A' ∈ Th2Row.r2.BT x K T S := ⟨isS_of_isE_rank hG hA'R hel hrk, hrk⟩
    exact le_iSup₂_of_le A' hmem le_rfl
  · refine ⟨3, le_rfl, fun A' hA'R hel hrk => ?_, h82'.2.1, h82'.2.2.1⟩
    have hmem : A' ∈ Th2Row.r4b.BT x K T S := ⟨isS_of_isE_rank hG (hA'R.trans hRT) hel hrk, hrk⟩
    exact le_iSup₂_of_le A' hmem le_rfl
  · refine ⟨2, by norm_num, fun A' hA'R hel hrk => ?_, h82'.2.1, h82'.2.2.1⟩
    have hmem : A' ∈ Th2Row.r4c.BT x K T S := ⟨isS_of_isE_rank hG (hA'R.trans hRT) hel hrk, hrk⟩
    exact le_iSup₂_of_le A' hmem le_rfl

end CFSG.GH74.GLS.Th2.P812

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P812

variable {G : Type} [Group G]

theorem l812_rows [Finite G] (hL34 : B_gen4_noL34_elem) (hG : C3Hyp G) {x y : G}
    {K T S M : Subgroup G} {ρ : Th2Row} {B : Subgroup G} (h2 : Th2M2 x y K T S M ρ B)
    (h7 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    HasL2Model (kBar K) Odd ∧ (ρ = .r1b ∨ ρ = .r2 ∨ ρ = .r4b ∨ ρ = .r4c) := by
  have hstd := h2.std
  have hrow := h2.row
  cases ρ with
  | r1a =>
    obtain ⟨hL2, -, h3⟩ := hrow
    have hPr : ∀ q : ℕ, (Odd q ∧ ¬ IsFM9 q) → Odd q := fun q hq => hq.1
    exact (false_of_three_le_rank_Q hG hstd (centerlessBar_of_hasL2Model hPr hL2)
      (rankTwoShape_sylow_L2 hstd.sylow_P (TwoThin.isQuasisimple_hat hstd.comp) hPr hL2) h3).elim
  | r1b =>
    obtain ⟨hL2, -⟩ := hrow
    exact ⟨C3.Layer1.Back.hasL2Model_mono (fun q hq => hq.1) hL2, Or.inl rfl⟩
  | r2 =>
    have hrow' : HasL2Model (kBar K) (fun q => Odd q ∧ IsFM9 q ∧ q ≠ 5) := hrow
    exact ⟨C3.Layer1.Back.hasL2Model_mono (fun q hq => hq.1) hrow', Or.inr (Or.inl rfl)⟩
  | r3a => exact absurd hrow.1 h7
  | r3b => exact absurd hrow.1 h7
  | r3c => exact absurd hrow.1 h7
  | r4a =>
    obtain ⟨hL2, h3⟩ := hrow
    have hPr : ∀ q : ℕ, q = 5 → Odd q := by rintro q rfl; decide
    exact (false_of_three_le_rank_Q hG hstd (centerlessBar_of_hasL2Model hPr hL2)
      (rankTwoShape_sylow_L2 hstd.sylow_P (TwoThin.isQuasisimple_hat hstd.comp) hPr hL2) h3).elim
  | r4b =>
    obtain ⟨hL2, -⟩ := hrow
    have hPr : ∀ q : ℕ, q = 5 → Odd q := by rintro q rfl; decide
    exact ⟨C3.Layer1.Back.hasL2Model_mono hPr hL2, Or.inr (Or.inr (Or.inl rfl))⟩
  | r4c =>
    obtain ⟨hL2, -⟩ := hrow
    have hPr : ∀ q : ℕ, q = 5 → Odd q := by rintro q rfl; decide
    exact ⟨C3.Layer1.Back.hasL2Model_mono hPr hL2, Or.inr (Or.inr (Or.inr rfl))⟩
  | r5 =>
    obtain ⟨hL34', hel, hcard⟩ := hrow
    exact (hL34 G hG.gen4 x K hstd.orderOf_x hstd.comp ⟨hL34', hel, hcard⟩).elim

end CFSG.GH74.GLS

module

public import CFSG.GH74.GLS.Stage4.HexIdentify
public import CFSG.GH74.GLS.Stage4.HexRev
public import CFSG.GH74.GLS.Stage4.HexSL2Defs
public import CFSG.GH74.GLS.Stage4.Main

public noncomputable section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint
  CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.GLS.Stage4.Hex

@[expose] def PStruct (p : ℕ) {G : Type} [Group G] (U : Subgroup G) (root : ℤ → Subgroup G) :
    Prop :=
  (∃ S : Sylow p G, (S : Subgroup G) = U) ∧
    ∀ i : ℤ, 1 ≤ i → i ≤ 6 → IsMulCommutative (root i) ∧ ∀ x ∈ root i, x ^ p = 1

theorem PStruct.of_eq_or_rev {p : ℕ} {G : Type} [Group G] {D D' : RankTwoSystem G 6}
    (h : D' = D ∨ D' = D.rev) (hP : PStruct p D.U D.root) : PStruct p D'.U D'.root := by
  rcases h with rfl | rfl
  · exact hP
  · refine ⟨hP.1, fun i h1 h6 => ?_⟩
    rw [rev_root, revIdx_pos (by omega)]
    exact hP.2 _ (by omega) (by omega)

@[expose] def Ch6LocalRGD2p : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs], IsTwoCentralG2TypeG2 G Gs →
      ∃ (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G)
        (R : RGD2 6 H r₁ r₂ U root), (H ⊔ U) ⊔ R.N = ⊤ ∧ ∃ p q : ℕ, p.Prime ∧ Odd q ∧
          PStruct p U root ∧
          ((5 ≤ q ∧ RootOrdersG2 root q) ∨ (3 ≤ q ∧ RootOrdersD4 root q))

theorem ch6LocalRGD2_of_p (h : Ch6LocalRGD2p) : Ch6LocalRGD2 := by
  intro G _ _ hStd hr Gs _ hG2
  obtain ⟨H, r₁, r₂, U, root, R, hgen, p, q, -, hq, -, hcase⟩ := h G hStd hr Gs hG2
  exact ⟨H, r₁, r₂, U, root, R, hgen, q, hq, hcase⟩

@[expose] def Ch6LocalBNp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs], IsTwoCentralG2TypeG2 G Gs →
      ∃ (D : RankTwoSystem G 6) (p q : ℕ), p.Prime ∧ Odd q ∧ PStruct p D.U D.root ∧
        ((5 ≤ q ∧ RootOrdersG2 D.root q) ∨ (3 ≤ q ∧ RootOrdersD4 D.root q))

theorem ch6LocalBNp_of_rgd2p (h : Ch6LocalRGD2p) : Ch6LocalBNp := by
  intro G _ _ hStd hr Gs _ hG2
  obtain ⟨H, r₁, r₂, U, root, R, hgen, p, q, hp, hq, hP, hcase⟩ := h G hStd hr Gs hG2
  have : IsSimpleGroup G := hStd.kps.1
  exact ⟨(R.toPre hgen).toSystemOfSimple, p, q, hp, hq, hP, hcase⟩

@[expose] def HexMatchG2 :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (D : RankTwoSystem G 6) (q : ℕ),
    Odd q → 5 ≤ q → RootOrdersG2 D.root q →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (hF : 3 ≤ Nat.card F),
        Nat.card F = q ∧ (UMatch (g2ModelSystem F hF) D ∨ UMatch (g2ModelSystem F hF) D.rev)

@[expose] def HexMatchD4 :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (D : RankTwoSystem G 6) (q : ℕ)
    (hq : 3 ≤ q), Odd q →
    (∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card (D.root i) = if i % 2 = 1 then q ^ 3 else q) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
        (hσq : ∀ c, σ c = c ^ q), UMatch (d4ModelSystem σ (by omega) hK hσq) D

@[expose] def HexMatchG2p :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (D : RankTwoSystem G 6) (p q : ℕ),
    p.Prime → Odd q → 5 ≤ q → RootOrdersG2 D.root q → PStruct p D.U D.root →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (hF : 3 ≤ Nat.card F),
        Nat.card F = q ∧ (UMatch (g2ModelSystem F hF) D ∨ UMatch (g2ModelSystem F hF) D.rev)

@[expose] def HexMatchD4p :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (D : RankTwoSystem G 6) (p q : ℕ)
    (hq : 3 ≤ q), p.Prime → Odd q →
    (∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card (D.root i) = if i % 2 = 1 then q ^ 3 else q) →
      PStruct p D.U D.root →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
        (hσq : ∀ c, σ c = c ^ q), UMatch (d4ModelSystem σ (by omega) hK hσq) D

theorem hexMatchG2p_of_match
    (h : HexMatchG2) : HexMatchG2p :=
  fun G _ _ _ D _ q _ hq h5 hD _ => h G D q hq h5 hD

theorem hexMatchD4p_of_match
    (h : HexMatchD4) : HexMatchD4p :=
  fun G _ _ _ D _ q hq _ hodd hD _ => h G D q hq hodd hD

theorem lieModel_g2_of_match
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (D : RankTwoSystem G 6) {q : ℕ} (hq : 3 ≤ q)
    (h : ∃ (F : Type) (_ : Field F) (_ : Finite F) (hF : 3 ≤ Nat.card F),
      Nat.card F = q ∧ (UMatch (g2ModelSystem F hF) D ∨ UMatch (g2ModelSystem F hF) D.rev)) :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f = q ∧ LieModel G .G2 0 p f := by
  obtain ⟨F, _, _, hF, hcard, hm⟩ := h
  have := Fintype.ofFinite F
  obtain ⟨p, -, n, hp, hpn⟩ := FiniteField.card' F
  have hcardp : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hpn]
  have hq' : q = p ^ (n : ℕ) := hcard.symm.trans hcardp
  have hmatch : G2RankTwoData F G hF := hm.elim (fun h => ⟨D, h⟩) (fun h => ⟨D.rev, h⟩)
  exact ⟨p, n, hp, n.pos, hq'.symm, lieModel_g2_of_rankTwoData hp n.pos (hq' ▸ hq) hcardp hmatch⟩

theorem lieModel_d4_of_match
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (D : RankTwoSystem G 6) {q : ℕ} (hq : 2 ≤ q)
    (h : ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
      (hσq : ∀ c, σ c = c ^ q), UMatch (d4ModelSystem σ hq hK hσq) D) :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f = q ∧ LieModel G .trialityD4 0 p f := by
  obtain ⟨K, _, _, σ, hK, hσq, hm⟩ := h
  have := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hpn⟩ := FiniteField.card' K
  have hcardp : q ^ 3 = p ^ (n : ℕ) := by rw [← hK, Nat.card_eq_fintype_card, hpn]
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1
    (show q ∣ p ^ (n : ℕ) from hcardp ▸ Dvd.intro_left _ (by ring : q * q * q = q ^ 3))
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hf
      omega
    · exact h
  exact ⟨p, f, hp, hf1, hf.symm, lieModel_d4_of_rankTwoData hp hf1 hf ⟨D, hm⟩⟩

@[expose] def HexClassG2Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (D : RankTwoSystem G 6) (q : ℕ),
    Odd q → 5 ≤ q → RootOrdersG2 D.root q →
      ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f = q ∧ LieModel G .G2 0 p f

@[expose] def HexClassD4Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (D : RankTwoSystem G 6) (q : ℕ),
    Odd q → 3 ≤ q → RootOrdersD4 D.root q →
      ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f = q ∧ LieModel G .trialityD4 0 p f

@[expose] def HexClassG2p : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (D : RankTwoSystem G 6) (p q : ℕ),
    p.Prime → Odd q → 5 ≤ q → RootOrdersG2 D.root q → PStruct p D.U D.root →
      ∃ p' f : ℕ, p'.Prime ∧ 1 ≤ f ∧ p' ^ f = q ∧ LieModel G .G2 0 p' f

@[expose] def HexClassD4p : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (D : RankTwoSystem G 6) (p q : ℕ),
    p.Prime → Odd q → 3 ≤ q → RootOrdersD4 D.root q → PStruct p D.U D.root →
      ∃ p' f : ℕ, p'.Prime ∧ 1 ≤ f ∧ p' ^ f = q ∧ LieModel G .trialityD4 0 p' f

theorem hexClassG2Odd_of_hexClass (h : HexClassG2) : HexClassG2Odd :=
  fun G _ _ _ D q _ h5 hD => h G D q (by omega) hD

theorem hexClassD4Odd_of_hexClass (h : HexClassD4) : HexClassD4Odd :=
  fun G _ _ _ D q _ h3 hD => h G D q (by omega) hD

theorem hexClassG2p_of_odd (h : HexClassG2Odd) : HexClassG2p :=
  fun G _ _ _ D _ q _ hq h5 hD _ => h G D q hq h5 hD

theorem hexClassD4p_of_odd (h : HexClassD4Odd) : HexClassD4p :=
  fun G _ _ _ D _ q _ hq h3 hD _ => h G D q hq h3 hD

theorem hexClassG2Odd_of_match
    (h : HexMatchG2) : HexClassG2Odd := by
  intro G _ _ _ D q hq h5 hD
  exact lieModel_g2_of_match D (by omega) (h G D q hq h5 hD)

theorem hexClassG2p_of_matchp
    (h : HexMatchG2p) : HexClassG2p := by
  intro G _ _ _ D p q hp hq h5 hD hP
  exact lieModel_g2_of_match D (by omega) (h G D p q hp hq h5 hD hP)

theorem hexClassD4Odd_of_match
    (h : HexMatchD4) : HexClassD4Odd := by
  intro G _ _ _ D q hq h3 hD
  obtain ⟨D', -, hD'⟩ := exists_system_firstOrders D hD
  exact lieModel_d4_of_match D' (by omega) (h G D' q h3 hq hD')

theorem hexClassD4p_of_matchp
    (h : HexMatchD4p) : HexClassD4p := by
  intro G _ _ _ D p q hp hq h3 hD hP
  obtain ⟨D', hD'eq, hD'⟩ := exists_system_firstOrders D hD
  exact lieModel_d4_of_match D' (by omega)
    (h G D' p q h3 hp hq hD' (PStruct.of_eq_or_rev hD'eq hP))

theorem s_ch6_Std_of_bn_odd (hA : Ch6LocalBN) (hG2 : HexClassG2Odd) (hD4 : HexClassD4Odd) :
    S_ch6_Std := by
  intro G _ _ hStd hr hIn
  rcases hIn with hAsc | ⟨Gs, _, hT⟩
  · exact Or.inr (Or.inr (Or.inr hAsc))
  · have hG : IsTwoCentralG2TypeG2 G Gs := IsTwoCentralG2Type.g2 hStd.nonab hT
    obtain ⟨D, q, hqodd, hcase⟩ := hA G hStd hr Gs hG
    have : IsSimpleGroup G := hStd.kps.1
    rcases hcase with ⟨h5, hD⟩ | ⟨h3, hD⟩
    · obtain ⟨p, f, hp, hf, hpf, hL⟩ := hG2 G D q hqodd h5 hD
      exact Or.inr (Or.inl ⟨p, f, hp, prime_ne_two_of_odd_pow hf hpf hqodd, hf, by omega, hL⟩)
    · obtain ⟨p, f, hp, hf, hpf, hL⟩ := hD4 G D q hqodd h3 hD
      exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, prime_ne_two_of_odd_pow hf hpf hqodd, hf, hL⟩))

theorem s_ch6_Std_of_bnp (hA : Ch6LocalBNp) (hG2 : HexClassG2p) (hD4 : HexClassD4p) :
    S_ch6_Std := by
  intro G _ _ hStd hr hIn
  rcases hIn with hAsc | ⟨Gs, _, hT⟩
  · exact Or.inr (Or.inr (Or.inr hAsc))
  · have hG : IsTwoCentralG2TypeG2 G Gs := IsTwoCentralG2Type.g2 hStd.nonab hT
    obtain ⟨D, r, q, hr', hqodd, hP, hcase⟩ := hA G hStd hr Gs hG
    have : IsSimpleGroup G := hStd.kps.1
    rcases hcase with ⟨h5, hD⟩ | ⟨h3, hD⟩
    · obtain ⟨p, f, hp, hf, hpf, hL⟩ := hG2 G D r q hr' hqodd h5 hD hP
      exact Or.inr (Or.inl ⟨p, f, hp, prime_ne_two_of_odd_pow hf hpf hqodd, hf, by omega, hL⟩)
    · obtain ⟨p, f, hp, hf, hpf, hL⟩ := hD4 G D r q hr' hqodd h3 hD hP
      exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, prime_ne_two_of_odd_pow hf hpf hqodd, hf, hL⟩))

theorem s_ch6_Std_of_match
    (hA : Ch6LocalRGD2) (hG2 : HexMatchG2) (hD4 : HexMatchD4) :
    S_ch6_Std :=
  s_ch6_Std_of_bn_odd (ch6LocalBN_of_rgd2 hA) (hexClassG2Odd_of_match hG2)
    (hexClassD4Odd_of_match hD4)

theorem s_ch6_Std_of_bn_match
    (hA : Ch6LocalBN) (hG2 : HexMatchG2) (hD4 : HexMatchD4) :
    S_ch6_Std :=
  s_ch6_Std_of_bn_odd hA (hexClassG2Odd_of_match hG2) (hexClassD4Odd_of_match hD4)

theorem s_ch6_Std_of_matchp
    (hA : Ch6LocalRGD2p) (hG2 : HexMatchG2p) (hD4 : HexMatchD4p) :
    S_ch6_Std :=
  s_ch6_Std_of_bnp (ch6LocalBNp_of_rgd2p hA) (hexClassG2p_of_matchp hG2)
    (hexClassD4p_of_matchp hD4)

theorem s_ch6_Std_of_p (hA : Ch6LocalRGD2p) (hG2 : HexClassG2Odd) (hD4 : HexClassD4Odd) :
    S_ch6_Std :=
  s_ch6_Std_of_bn_odd (ch6LocalBN_of_rgd2 (ch6LocalRGD2_of_p hA)) hG2 hD4

@[expose] def Ch6LocalRGD2s : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs], IsTwoCentralG2TypeG2 G Gs →
      ∃ (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G)
        (R : RGD2 6 H r₁ r₂ U root), (H ⊔ U) ⊔ R.N = ⊤ ∧ ∃ p q : ℕ, p.Prime ∧ Odd q ∧
          PStruct p U root ∧ SL2At H R.N root 1 ∧ SL2At H R.N root 4 ∧
          ((5 ≤ q ∧ RootOrdersG2 root q) ∨ (3 ≤ q ∧ RootOrdersD4 root q))

theorem ch6LocalRGD2p_of_s (h : Ch6LocalRGD2s) : Ch6LocalRGD2p := by
  intro G _ _ hStd hr Gs _ hG2
  obtain ⟨H, r₁, r₂, U, root, R, hgen, p, q, hp, hq, hP, -, -, hcase⟩ := h G hStd hr Gs hG2
  exact ⟨H, r₁, r₂, U, root, R, hgen, p, q, hp, hq, hP, hcase⟩

@[expose] def HexMatchG2s :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (H : Subgroup G) (r₁ r₂ : G)
    (U : Subgroup G) (root : ℤ → Subgroup G) (R : RGD2 6 H r₁ r₂ U root)
    (hgen : (H ⊔ U) ⊔ R.N = ⊤) (p q : ℕ), p.Prime → Odd q → 5 ≤ q → RootOrdersG2 root q →
      PStruct p U root → SL2At H R.N root 1 → SL2At H R.N root 4 →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (hF : 3 ≤ Nat.card F), Nat.card F = q ∧
        (UMatch (g2ModelSystem F hF) (R.toPre hgen).toSystemOfSimple ∨
          UMatch (g2ModelSystem F hF) (R.toPre hgen).toSystemOfSimple.rev)

@[expose] def HexMatchD4s :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (H : Subgroup G) (r₁ r₂ : G)
    (U : Subgroup G) (root : ℤ → Subgroup G) (R : RGD2 6 H r₁ r₂ U root)
    (hgen : (H ⊔ U) ⊔ R.N = ⊤) (p q : ℕ) (hq : 3 ≤ q), p.Prime → Odd q →
      RootOrdersD4 root q → PStruct p U root → SL2At H R.N root 1 → SL2At H R.N root 4 →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
        (hσq : ∀ c, σ c = c ^ q),
        UMatch (d4ModelSystem σ (by omega) hK hσq) (R.toPre hgen).toSystemOfSimple ∨
          UMatch (d4ModelSystem σ (by omega) hK hσq) (R.toPre hgen).toSystemOfSimple.rev

theorem lieModel_d4_of_match_or
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (D : RankTwoSystem G 6) {q : ℕ} (hq : 2 ≤ q)
    (h : ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
      (hσq : ∀ c, σ c = c ^ q), UMatch (d4ModelSystem σ hq hK hσq) D ∨
        UMatch (d4ModelSystem σ hq hK hσq) D.rev) :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f = q ∧ LieModel G .trialityD4 0 p f := by
  obtain ⟨K, _, _, σ, hK, hσq, hm | hm⟩ := h
  · exact lieModel_d4_of_match D hq ⟨K, inferInstance, inferInstance, σ, hK, hσq, hm⟩
  · exact lieModel_d4_of_match D.rev hq ⟨K, inferInstance, inferInstance, σ, hK, hσq, hm⟩

theorem s_ch6_Std_of_matchs
    (hA : Ch6LocalRGD2s) (hG2 : HexMatchG2s) (hD4 : HexMatchD4s) :
    S_ch6_Std := by
  intro G _ _ hStd hr hIn
  rcases hIn with hAsc | ⟨Gs, _, hT⟩
  · exact Or.inr (Or.inr (Or.inr hAsc))
  · have hG : IsTwoCentralG2TypeG2 G Gs := IsTwoCentralG2Type.g2 hStd.nonab hT
    obtain ⟨H, r₁, r₂, U, root, R, hgen, r, q, hr', hqodd, hP, hS1, hS4, hcase⟩ :=
      hA G hStd hr Gs hG
    have : IsSimpleGroup G := hStd.kps.1
    rcases hcase with ⟨h5, hD⟩ | ⟨h3, hD⟩
    · obtain ⟨p, f, hp, hf, hpf, hL⟩ := lieModel_g2_of_match (R.toPre hgen).toSystemOfSimple
        (by omega) (hG2 G H r₁ r₂ U root R hgen r q hr' hqodd h5 hD hP hS1 hS4)
      exact Or.inr (Or.inl ⟨p, f, hp, prime_ne_two_of_odd_pow hf hpf hqodd, hf, by omega, hL⟩)
    · obtain ⟨p, f, hp, hf, hpf, hL⟩ := lieModel_d4_of_match_or (R.toPre hgen).toSystemOfSimple
        (by omega) (hD4 G H r₁ r₂ U root R hgen r q h3 hr' hqodd hD hP hS1 hS4)
      exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, prime_ne_two_of_odd_pow hf hpf hqodd, hf, hL⟩))

end CFSG.GH74.GLS.Stage4.Hex

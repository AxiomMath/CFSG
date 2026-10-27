module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusL34Aux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34AutExp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UPrimeExcL34
public import CFSG.RankThree.PartTwo.KFacts.L34Automizer

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs CFSG.AGLEmbeddingD2
  CFSG.RankThree.PartOne.Census3
  CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

section Main

theorem isoLie_A2_two_two (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hq2 : q.p = 2) (hq3 : q.exponent = 2) (hd : d.1 = .A 2 q) {Y : Type} [Group Y]
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    IsoLie Y (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩) := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  rcases q with ⟨p, k, hp, hk⟩
  simp only at hq2 hq3
  subst hq2 hq3
  exact ⟨hv, ⟨e⟩⟩


theorem gls3ConclusionPlus_lie_L34 (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hq2 : q.p = 2) (hq3 : q.exponent = 2) (hd : d.1 = .A 2 q) {X : Type} [Group X] [Finite X]
    {K : Subgroup X} (hKn : K.Normal) (hiso : Nonempty (↥K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hKc : Subgroup.centralizer (K : Set X) = ⊥) (P : Sylow 3 X)
    (hΓ : gammaCore 3 1 ⊤ (P : Subgroup X) < ⊤) : Gls3ConclusionPlus X K (P : Subgroup X) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hiso
  have hd34 : IsL34Index d := ⟨q, hq2, hq3, hd⟩
  have hlin : IsLinThreeFour ↥K := ⟨d, ⟨q, hq2, hq3, hd⟩, ⟨e⟩⟩
  obtain ⟨θ⟩ := nonempty_equiv_S_of_index hd34 e
  obtain ⟨ι, hι, hιK, hιR⟩ := exists_embedding_l34 hKc θ
  have hXdvd : Nat.card X ∣ 241920 := by
    let ι' : X →* CFSG.ComponentClassification.PSL3Four.R :=
      ι.codRestrict _ (fun x => hιR ⟨x, rfl⟩)
    have hι' : Function.Injective ι' := fun a b h => hι (congrArg Subtype.val h)
    have := Subgroup.card_dvd_of_injective ι' hι'
    rwa [CFSG.ComponentClassification.PSL3Four.card_R] at this
  have hf3 : (Nat.card X).factorization 3 ≤ 3 := by
    by_contra hlt
    have h81 : 3 ^ 4 ∣ Nat.card X :=
      (pow_dvd_pow 3 (by omega : 4 ≤ (Nat.card X).factorization 3)).trans
        (Nat.ordProj_dvd (Nat.card X) 3)
    have := h81.trans hXdvd
    norm_num at this
  have hPcard : Nat.card (P : Subgroup X) = 3 ^ (Nat.card X).factorization 3 :=
    Sylow.card_eq_multiplicity P
  have hP27 : Nat.card (P : Subgroup X) ∣ 27 := by
    rw [hPcard, show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact pow_dvd_pow 3 hf3
  have hPexp : ∀ x ∈ (P : Subgroup X), x ^ 3 = 1 := by
    intro x hx
    have h27 : x ^ 27 = 1 := by
      have h1 : (⟨x, hx⟩ : (P : Subgroup X)) ^ Nat.card (P : Subgroup X) = 1 :=
        pow_card_eq_one'
      obtain ⟨c, hc⟩ := hP27
      have h2 : (⟨x, hx⟩ : (P : Subgroup X)) ^ 27 = 1 := by
        rw [hc, pow_mul, h1, one_pow]
      exact congrArg Subtype.val h2
    have hr : ι x ∈ CFSG.ComponentClassification.PSL3Four.R := hιR ⟨x, rfl⟩
    have h3 : ι x ^ 3 = 1 :=
      KFactProofs.L34AutExp.exp27 (ι x) hr (by rw [← map_pow, h27, map_one])
    exact hι (by rw [map_pow, h3, map_one])
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal (G := X) (p := 3) P (N := K)
  have hmapT : (T : Subgroup ↥K).map K.subtype = (P : Subgroup X) ⊓ K := by
    rw [hT, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr inf_le_right
  set Q : Subgroup X := (P : Subgroup X) ⊓ K with hQ
  have hTd : L34Local.LocalData ↥K (T : Subgroup ↥K) :=
    UPrimeExcL34.localData_of_isLinThreeFour hlin T
  have hTcard : Nat.card (T : Subgroup ↥K) = 9 := hTd.card_eq
  have hQcard : Nat.card Q = 9 := by
    rw [← hmapT, Subgroup.card_map_of_injective K.subtype_injective, hTcard]
  have hQmem : ∀ k : ↥K, (k : X) ∈ Q ↔ k ∈ (T : Subgroup ↥K) := fun k => by
    rw [← hmapT]
    exact Subgroup.mem_map_iff_mem K.subtype_injective
  have hPK : (P : Subgroup X) ≤ K := by
    by_contra hnot
    have hQne : ∃ t ∈ Q, t ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Q = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hcon x hx)
      rw [this, Subgroup.card_bot] at hQcard
      omega
    obtain ⟨A, hAP, hAel, hAc, hAK⟩ := exists_plane_not_le P.isPGroup' hPexp hQne hnot
    have hGLB := kFactL34Outer d hd34 X K hKn hKc ⟨e⟩ A hAel hAc hAK
    exact absurd (gammaCore_eq_top_of_glbCore_le hAP hGLB) (ne_of_lt hΓ)
  have hPQ : (P : Subgroup X) = Q := (inf_eq_left.mpr hPK).symm
  have hPc9 : Nat.card (P : Subgroup X) = 9 := by rw [hPQ]; exact hQcard
  obtain ⟨ε₀⟩ := L34Local.nonempty_equiv_of_isLinThreeFour hlin
  have hKcard : Nat.card ↥K = 20160 := by
    rw [Nat.card_congr ε₀.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL UPrimeExcL34.card_galoisField_two_two
  have hidx : ∃ k : ℕ, K.index = 2 ^ k := by
    have hmul := K.index_mul_card
    rw [hKcard] at hmul
    have hf : (Nat.card X).factorization 3 = 2 := by
      have h : 3 ^ (Nat.card X).factorization 3 = 3 ^ 2 := by rw [← hPcard, hPc9]; norm_num
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
    have hidx12 : K.index ∣ 12 := by
      have h1 : K.index * 20160 ∣ 241920 := hmul ▸ hXdvd
      have h2 : K.index * 20160 ∣ 12 * 20160 := by simpa using h1
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h2
    have hno3 : ¬ 3 ∣ K.index := by
      intro h3
      have h27 : 3 ^ 3 ∣ Nat.card X := by
        rw [← hmul]
        have : 3 ^ 3 ∣ 3 * 20160 := by norm_num
        exact this.trans (Nat.mul_dvd_mul h3 (dvd_refl _))
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h27
      omega
    have h4 : K.index ∣ 4 := by
      have hcop : Nat.Coprime K.index 3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hno3 |>.symm
      have : K.index ∣ 4 * 3 := by simpa using hidx12
      exact hcop.dvd_of_dvd_mul_right this
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show K.index ∣ 2 ^ 2 by simpa using h4)
    exact ⟨k, hk⟩
  have hcomm := L34Local.LocalData.commute_of_card_eq hTd
  have hΓeq : gammaCore 3 1 K Q =
      (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype := by
    have := gammaCore_eq_map_normalizer (K := K) (T : Subgroup ↥K)
      (fun t ht ht1 y hy => mem_normalizer_of_conj_mem_of_ti hcomm hTd.centralizer_le ht ht1 hy)
      (by rw [hTcard]; norm_num)
    rwa [hmapT] at this
  set N : Subgroup ↥K := Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) with hN
  set Γ : Subgroup X := N.map K.subtype with hΓdef
  have hΓK : K ⊓ Subgroup.normalizer (Q : Set X) = Γ := by
    have := inf_normalizer_map_eq (K := K) (T : Subgroup ↥K)
    rwa [hmapT] at this
  have hΓcard : Nat.card Γ = 72 := by
    rw [hΓdef, Subgroup.card_map_of_injective K.subtype_injective, hTd.card_normalizer]
  have hΓle : Γ ≤ K := Subgroup.map_subtype_le _
  obtain ⟨e'⟩ := UPrimeExcL34.nonempty_equiv_projSL hlin
  have hlt : gammaCore 3 1 K Q < K := by
    rw [hΓeq]
    refine lt_of_le_of_ne hΓle ?_
    intro h
    have h2 : Nat.card Γ = Nat.card K := by rw [h]
    rw [hΓcard, hKcard] at h2
    omega
  have hmax : ∀ H : Subgroup X, gammaCore 3 1 K Q < H → H ≤ K → H = K := by
    intro H hΓH hHK
    rw [hΓeq] at hΓH
    have hNY : N ≤ H.subgroupOf K := by
      intro k hk
      exact hΓH.le ⟨k, hk, rfl⟩
    by_cases hYtop : H.subgroupOf K = ⊤
    · refine le_antisymm hHK ?_
      intro x hx
      have : (⟨x, hx⟩ : ↥K) ∈ H.subgroupOf K := hYtop ▸ Subgroup.mem_top _
      exact this
    · exfalso
      have hY := CFSG.RankThree.PartTwo.KFacts.L34Max.eq_normalizer_of_normalizer_le e' hTcard hNY
        hYtop
      have : H = Γ := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hHK, hY]
      exact (ne_of_lt hΓH) this.symm
  have hQcommQ : IsMulCommutative Q :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := Q) (by rw [hQcard]; norm_num)
  have hQel : CFSG.Open.IsElemAbelian 3 Q :=
    ⟨hQcommQ, fun x hx => hPexp x (Subgroup.mem_inf.mp hx).1⟩
  have hdvd8 : 2 ^ 3 ∣ Nat.card N := by rw [hTd.card_normalizer]; norm_num
  obtain ⟨T₀, hT₀c, -, hT₀N⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := ⊥) (L := N) (n := 3) (by simp) hdvd8 bot_le
  set S : Subgroup X := T₀.map K.subtype with hS
  have hScard : Nat.card S = 8 := by
    rw [hS, Subgroup.card_map_of_injective K.subtype_injective, hT₀c]; norm_num
  have hSΓ : S ≤ Γ := Subgroup.map_mono hT₀N
  have hQΓ : Q ≤ Γ := by
    rw [← hmapT]
    exact Subgroup.map_mono Subgroup.le_normalizer
  have hQS : Q ⊓ S = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by rw [hQcard, hScard]; norm_num))
  have hsup : Q ⊔ S = Γ := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hQΓ hSΓ) ?_
    have h1 : Nat.card Q ∣ Nat.card ↥(Q ⊔ S) := Subgroup.card_dvd_of_le le_sup_left
    have h2 : Nat.card S ∣ Nat.card ↥(Q ⊔ S) := Subgroup.card_dvd_of_le le_sup_right
    rw [hQcard] at h1
    rw [hScard] at h2
    have h3 : 9 * 8 ∣ Nat.card ↥(Q ⊔ S) := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
    have h4 : 0 < Nat.card ↥(Q ⊔ S) := Nat.card_pos
    rw [hΓcard]
    exact Nat.le_of_dvd h4 h3
  have hk : Nat.card (GaloisField 2 2) = 4 := UPrimeExcL34.card_galoisField_two_two
  have hQ8 : Nonempty (↥S ≃* QuaternionGroup 2) := by
    set E : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2))
      := (T : Subgroup ↥K).map ε₀.toMonoidHom with hE
    have hEc : Nat.card E = 9 := by
      rw [hE, Subgroup.card_map_of_injective ε₀.injective, hTcard]
    have hEd : L34Local.LocalData
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2)) E :=
      hTd.map ε₀ (fun g => by
        rw [hE]
        exact (Subgroup.mem_map_iff_mem ε₀.injective).symm)
    have hS'N : T₀.map ε₀.toMonoidHom ≤ Subgroup.normalizer (E : Set _) := by
      rw [hE, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hT₀N
    have hS'c : Nat.card (T₀.map ε₀.toMonoidHom) = 8 := by
      rw [Subgroup.card_map_of_injective ε₀.injective, hT₀c]; norm_num
    have hcent : ∀ g : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
        (GaloisField 2 2), (∀ x ∈ E, g * x = x * g) → g ∈ E := by
      intro g hg
      obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : E = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hcon x hx)
        rw [this, Subgroup.card_bot] at hEc
        omega
      exact hEd.centralizer_le x hxE hx1 g (hg x hxE)
    obtain ⟨φ⟩ := nonempty_mulEquiv_quaternion_of_automizer hS'N hS'c hEc hcent
      (CFSG.RankThree.PartTwo.KFacts.L34.nonempty_automizer_of_card_eq_nine hk hEc)
    exact ⟨((Subgroup.equivMapOfInjective T₀ K.subtype K.subtype_injective).symm.trans
      (Subgroup.equivMapOfInjective T₀ ε₀.toMonoidHom ε₀.injective)).trans φ⟩
  have hirr : ActsIrr S Q := by
    intro W hWQ hSW
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    refine le_antisymm hWQ ?_
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
    have hwQ : (w : X) ∈ Q := hWQ w.2
    rw [← hmapT] at hwQ
    obtain ⟨t, ht, htw⟩ := hwQ
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact hw1 (Subtype.ext (by simpa using htw.symm))
    have hQW : Q ≤ Subgroup.normalizer (W : Set X) := by
      intro q hq
      refine Subgroup.mem_normalizer_fintype (fun x hx => ?_)
      have hxQ : x ∈ Q := hWQ hx
      have := congrArg Subtype.val (hQcommQ.is_comm.comm ⟨q, hq⟩ ⟨x, hxQ⟩)
      have h2 : q * x * q⁻¹ = x := by
        calc q * x * q⁻¹ = x * q * q⁻¹ := by rw [show q * x = x * q from this]
          _ = x := by group
      rw [h2]; exact hx
    have hΓW : Γ ≤ Subgroup.normalizer (W : Set X) := by
      rw [← hsup]
      exact sup_le hQW hSW
    intro u hu
    have hu' := hu
    rw [← hmapT] at hu'
    obtain ⟨u', hu'T, rfl⟩ := hu'
    by_cases hu1 : u' = 1
    · subst hu1
      simp
    · obtain ⟨n, hnN, hn⟩ := hTd.trans t ht ht1 u' hu'T hu1
      have hnΓ : (n : X) ∈ Γ := ⟨n, hnN, rfl⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (hΓW hnΓ) (w : X)).mp w.2
      have h2 : (n : X) * (w : X) * (n : X)⁻¹ = (u' : X) := by
        rw [← htw]
        have := congrArg Subtype.val hn
        simpa using this
      rwa [h2] at h1
  have hIso := isoLie_A2_two_two d q hq2 hq3 hd e
  refine ⟨hlt, hmax, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))⟩
  refine ⟨hIso, hidx, hKcard, hQel, hQcard, ?_, S, ?_, hQS, ?_, hQ8, hirr⟩
  · rw [hΓeq, ← hΓK]
  · rw [hΓeq]; exact hSΓ
  · rw [hΓeq]; exact hsup

theorem gls3PlusCase_lie_L34 (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hq2 : q.p = 2) (hq3 : q.exponent = 2) (hd : d.1 = .A 2 q) : Gls3PlusCase (.lie d) := by
  unfold Gls3PlusCase
  intro X _ _ _ K hKn _ _ hiso hKc P _ hΓ
  exact gls3ConclusionPlus_lie_L34 d q hq2 hq3 hd hKn hiso hKc P hΓ

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

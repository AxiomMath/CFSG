module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.NormalizerOutside
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowFrattiniSup
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaPU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.SylowPermute
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34

variable {X : Type*} [Group X] [Finite X]

theorem localData_of_isLinThreeFour {K : Type} [Group K] [Finite K] (hK : IsLinThreeFour K)
    (T : Sylow 3 K) : KFactProofs.L34Local.LocalData K (T : Subgroup K) := by
  obtain ⟨ε₀⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hK
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hK20 : Nat.card K = 20160 := (kFactSmallThreeOrders K).2.1 hK
  have hTcard : Nat.card (T : Subgroup K) = 9 := KFactProofs.L34Local.card_sylow_three hK20 T
  have hP₁ : Nat.card ((T : Subgroup K).map ε₀.toMonoidHom) = 9 := by
    rw [← hTcard]
    exact (Nat.card_congr (ε₀.subgroupMap (T : Subgroup K)).toEquiv).symm
  obtain ⟨g, hg⟩ := exists_eq_map_conj_eZero hk hP₁
  let ε : projectiveSL 3 (GaloisField 2 2) ≃* K := (MulAut.conj g).trans ε₀.symm
  have hεT : ∀ y, y ∈ eZero (GaloisField 2 2) ↔ ε y ∈ (T : Subgroup K) := by
    intro y
    have h1 : ε y ∈ (T : Subgroup K) ↔ g * y * g⁻¹ ∈ (T : Subgroup K).map ε₀.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      rfl
    rw [h1, hg, Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
  exact (KFactProofs.L34Local.localData_eZero hk).map ε hεT

omit [Finite X] in
theorem card_subgroupOf_eq_card_inf {X : Type*} [Group X] (H K : Subgroup X) :
    Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup X) := by
  rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]

theorem eq_of_card_nine_of_le_normalizer {X : Type*} [Group X] [Finite X] {A B L : Subgroup X}
    (hAL : A ≤ L) (hBL : B ≤ L) (hBA : B ≤ Subgroup.normalizer (A : Set X)) (hA9 : Nat.card A = 9)
    (hB9 : Nat.card B = 9) (hL72 : Nat.card L = 72) : B = A := by
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hBA
  rw [hA9, hB9] at h
  have hdvd : Nat.card (A ⊔ B : Subgroup X) ∣ 72 := hL72 ▸ Subgroup.card_dvd_of_le (sup_le hAL hBL)
  have h3 : Nat.card (A ⊓ B : Subgroup X) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hB9]
    exact Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h3
  have hinf9 : Nat.card (A ⊓ B : Subgroup X) = 9 := by
    interval_cases i
    · rw [hieq] at h
      norm_num at h
      rw [h] at hdvd
      norm_num at hdvd
    · rw [hieq] at h
      have h27 : Nat.card (A ⊔ B : Subgroup X) = 27 := by omega
      rw [h27] at hdvd
      norm_num at hdvd
    · rw [hieq]
      norm_num
  have h1 : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hB9, hinf9])
  have h2 : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hA9, hinf9])
  rw [← h1, h2]

theorem normalizer_inf_eq_sup_of_l34 {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {X : Type} [Group X] [Finite X] {K A T : Subgroup X} (hKn : K.Normal)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) (hAK : A ≤ K) (hA9 : Nat.card A = 9)
    (hT : IsSylowTwoOf T (Subgroup.normalizer (A : Set X))) :
    A ⊔ (T ⊓ K) = Subgroup.normalizer (A : Set X) ⊓ K ∧
      Nat.card (Subgroup.normalizer (A : Set X) ⊓ K : Subgroup X) = 72 ∧
      Nat.card (T ⊓ K : Subgroup X) = 8 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : IsLinThreeFour ↥K := isLinThreeFour_of_l34Index hd he
  have hK20 : Nat.card K = 20160 := (kFactSmallThreeOrders ↥K).2.1 hL
  obtain ⟨NA, hNAdef⟩ : ∃ NA : Subgroup X, NA = Subgroup.normalizer (A : Set X) := ⟨_, rfl⟩
  rw [← hNAdef] at hT ⊢
  have hKN : ∀ x : X, x ∈ Subgroup.normalizer (K : Set X) := fun x =>
    Subgroup.mem_normalizer_iff.mpr fun k =>
      ⟨fun hk => hKn.conj_mem k hk x, fun hk => by simpa [mul_assoc] using hKn.conj_mem _ hk x⁻¹⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup ↥K, P = A.subgroupOf K := ⟨_, rfl⟩
  have hPc : Nat.card P = 9 := by
    rw [hPdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA9]
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hPc]; norm_num)
  have hPidx : ¬ 3 ∣ P.index := by
    have h := P.index_mul_card
    rw [hPc, hK20] at h
    have : P.index = 2240 := by omega
    rw [this]
    norm_num
  have hloc := localData_of_isLinThreeFour hL (hPp.toSylow hPidx)
  have hPS : ((hPp.toSylow hPidx : Sylow 3 ↥K) : Subgroup ↥K) = P := IsPGroup.toSylow_coe _ _
  have hNPsub : Subgroup.normalizer (P : Set ↥K) = NA.subgroupOf K := by
    rw [hNAdef, hPdef, Subgroup.subgroupOf_normalizer_eq hAK]
  have hNK : Nat.card (NA ⊓ K : Subgroup X) = 72 := by
    have h1 := hloc.card_normalizer
    rw [hPS, hNPsub, card_subgroupOf_eq_card_inf] at h1
    exact h1
  have hTNA : T ≤ NA := hT.1
  have hTnorm : T ≤ Subgroup.normalizer ((NA ⊓ K : Subgroup X) : Set X) :=
    CFSG.Quasithin.B2F.le_normalizer_inf (hTNA.trans Subgroup.le_normalizer)
      (fun x _ => hKN x)
  have hodd := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.not_two_dvd_relIndex_inf_of_normalizes
    hTNA inf_le_left hTnorm hT.2.2
  have hTK : T ⊓ (NA ⊓ K) = T ⊓ K := by rw [← inf_assoc, inf_eq_left.mpr hTNA]
  rw [hTK] at hodd
  have hTKp : IsPGroup 2 (T ⊓ K : Subgroup X) := hT.2.1.to_le inf_le_left
  have hTKc : Nat.card (T ⊓ K : Subgroup X) = 8 := by
    have hTKle : T ⊓ K ≤ NA ⊓ K := inf_le_inf_right K hTNA
    have h := Subgroup.relIndex_mul_card (T ⊓ K) (NA ⊓ K)
    rw [inf_of_le_left hTKle, hNK] at h
    obtain ⟨k, hk⟩ := hTKp.exists_card_eq
    rw [hk] at h ⊢
    have hk6 : k ≤ 6 := by
      by_contra hlt
      have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < (T ⊓ K).relIndex (NA ⊓ K) := by
        rcases Nat.eq_zero_or_pos ((T ⊓ K).relIndex (NA ⊓ K)) with h0 | h0
        · rw [h0, zero_mul] at h
          omega
        · exact h0
      nlinarith
    interval_cases k <;> omega
  have hTKA : T ⊓ K ≤ Subgroup.normalizer (A : Set X) := hNAdef ▸ (inf_le_left.trans hTNA)
  have hsup := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hTKA
  have hAT : A ⊓ (T ⊓ K) = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by rw [hA9, hTKc]; norm_num)).eq_bot
  rw [hAT, Subgroup.card_bot, mul_one, hA9, hTKc] at hsup
  have hAle : A ≤ NA ⊓ K := le_inf (hNAdef ▸ Subgroup.le_normalizer) hAK
  exact ⟨Subgroup.eq_of_le_of_card_ge (sup_le hAle (inf_le_inf_right K hTNA)) (by rw [hNK, hsup]),
    hNK, hTKc⟩

theorem le_of_normalizer_sylowTwo_le
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {X : Type} [Group X] [Finite X] {K A T Y : Subgroup X} (hKn : K.Normal)
    (hKc : Subgroup.centralizer (K : Set X) = ⊥)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : A ≤ K) (hAel : IsElemAbelian 3 A) (hA9 : Nat.card A = 9)
    (hT : IsSylowTwoOf T (Subgroup.normalizer (A : Set X))) (hTY : T ≤ Y) (hAY : A ≤ Y)
    (hNY : Subgroup.normalizer (T : Set X) ≤ Y) : K ≤ Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : IsLinThreeFour ↥K := isLinThreeFour_of_l34Index hd he
  have hK20 : Nat.card K = 20160 := (kFactSmallThreeOrders ↥K).2.1 hL
  obtain ⟨NA, hNAdef⟩ : ∃ NA : Subgroup X, NA = Subgroup.normalizer (A : Set X) := ⟨_, rfl⟩
  rw [← hNAdef] at hT
  have hKN : ∀ x : X, x ∈ Subgroup.normalizer (K : Set X) := fun x =>
    Subgroup.mem_normalizer_iff.mpr fun k =>
      ⟨fun hk => hKn.conj_mem k hk x, fun hk => by simpa [mul_assoc] using hKn.conj_mem _ hk x⁻¹⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup ↥K, P = A.subgroupOf K := ⟨_, rfl⟩
  have hPc : Nat.card P = 9 := by
    rw [hPdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA9]
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hPc]; norm_num)
  have hPidx : ¬ 3 ∣ P.index := by
    have h := P.index_mul_card
    rw [hPc, hK20] at h
    have : P.index = 2240 := by omega
    rw [this]
    norm_num
  have hloc := localData_of_isLinThreeFour hL (hPp.toSylow hPidx)
  have hPS : ((hPp.toSylow hPidx : Sylow 3 ↥K) : Subgroup ↥K) = P := IsPGroup.toSylow_coe _ _
  have hNPsub : Subgroup.normalizer (P : Set ↥K) = NA.subgroupOf K := by
    rw [hNAdef, hPdef, Subgroup.subgroupOf_normalizer_eq hAK]
  obtain ⟨hNKeq, hNK, -⟩ := normalizer_inf_eq_sup_of_l34 hd hKn he hAK hA9 (hNAdef ▸ hT)
  rw [← hNAdef] at hNKeq hNK
  have hAle : A ≤ NA ⊓ K := le_inf (hNAdef ▸ Subgroup.le_normalizer) hAK
  have hNKY : NA ⊓ K ≤ Y := hNKeq ▸ sup_le hAY (inf_le_left.trans hTY)
  have hPel : IsElemAbelian 3 P := by
    rw [hPdef]
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · show ((a : ↥K) : X) * ((b : ↥K) : X) = ((b : ↥K) : X) * ((a : ↥K) : X)
      exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩)
    · simpa using hAel.2 _ (Subgroup.mem_subgroupOf.mp hx)
  have htopc : Subgroup.centralizer ((⊤ : Subgroup ↥K) : Set ↥K) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzX : (z : X) ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_centralizer_iff.mp hz ⟨y, hy⟩ (Subgroup.mem_top _)
      exact congrArg Subtype.val this
    rw [hKc, Subgroup.mem_bot] at hzX
    exact Subtype.ext hzX
  have hetop : Nonempty ((⊤ : Subgroup ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) :=
    ⟨Subgroup.topEquiv.trans he.some⟩
  have hNPY : Subgroup.normalizer (P : Set ↥K) ≤ Y.subgroupOf K := by
    rw [hNPsub]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hNKY ⟨hx, x.2⟩
  rcases kFactL34Inner d hd ↥K ⊤ Subgroup.normal_top htopc hetop P hPel hPc le_top
      (Y.subgroupOf K) hNPY with hYN | hYtop
  ·
    exfalso
    have hYK : Y ⊓ K = NA ⊓ K := by
      have h := congrArg (fun S : Subgroup ↥K => S.map K.subtype) hYN
      simp only [Subgroup.subgroupOf_map_subtype] at h
      rw [h, hNPsub, Subgroup.subgroupOf_map_subtype]
    have hfr : NA ⊔ K = ⊤ := by
      have h := Sylow.normalizer_sup_eq_top (N := K) (hPp.toSylow hPidx)
      have hmap : ((hPp.toSylow hPidx : Sylow 3 ↥K) : Subgroup ↥K).map K.subtype = A := by
        rw [hPS, hPdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAK]
      rw [hmap, ← hNAdef] at h
      exact h
    have hc2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := K) (B := NA) (fun x _ => hKN x)
    rw [sup_comm, hfr, Subgroup.card_top, inf_comm, hNK, hK20] at hc2
    have hidx : (NA.subgroupOf ⊤).index = 280 := by
      have h := (NA.subgroupOf ⊤).index_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv,
        Nat.card_congr Subgroup.topEquiv.toEquiv] at h
      have hpos : 0 < Nat.card NA := Nat.card_pos
      have h' : (NA.subgroupOf ⊤).index * Nat.card NA * 72 = 280 * Nat.card NA * 72 := by
        rw [h, hc2]
        ring
      have := Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 72) h'
      exact Nat.eq_of_mul_eq_mul_right hpos this
    obtain ⟨s, -, hsT, hsNA, -⟩ :=
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_mem_normalizer_not_mem_of_two_dvd_index
        (H := ⊤) le_top hT (by rw [hidx]; norm_num)
    have hsY : s ∈ Y := hNY hsT
    apply hsNA
    rw [hNAdef]
    apply mem_normalizer_of_map_conj_eq_self
    refine eq_of_card_nine_of_le_normalizer (L := NA ⊓ K) hAle ?_ ?_ hA9 ?_ hNK
    · rintro _ ⟨a, ha, rfl⟩
      rw [← hYK]
      refine ⟨Y.mul_mem (Y.mul_mem hsY (hAY ha)) (Y.inv_mem hsY), ?_⟩
      exact hKn.conj_mem a (hAK ha) s
    · rintro _ ⟨a, ha, rfl⟩
      have hmem : s * a * s⁻¹ ∈ Y ⊓ K :=
        ⟨Y.mul_mem (Y.mul_mem hsY (hAY ha)) (Y.inv_mem hsY), hKn.conj_mem a (hAK ha) s⟩
      rw [hYK] at hmem
      rw [← hNAdef]
      exact hmem.1
    · rw [Subgroup.card_map_of_injective (MulAut.conj s).injective, hA9]
  · intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ Y.subgroupOf K := hYtop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim

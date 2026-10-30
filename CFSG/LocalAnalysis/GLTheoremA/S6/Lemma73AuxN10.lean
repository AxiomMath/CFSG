module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma73AuxCases
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Tools
import CFSG.CharacterTheory.Burnside
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pQuot_primeCore_eq_bot {p : ℕ} (hp : p.Prime) (L : Subgroup G) : GLAPPrimeCore p (PQuot p L) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p

theorem isAltPType_catalogIs {K : Subgroup G} {m : ℕ} (hm : 5 ≤ m) (h : IsAltPType 3 K m) :
    catalogIs (PQuot 3 K ⧸ Subgroup.center (PQuot 3 K)) (isAltN m) := by
  obtain ⟨e⟩ := h
  refine ⟨.alternating m hm, rfl, ⟨?_⟩⟩
  have hc : Subgroup.center (PQuot 3 K) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have hcen : e q ∈ Subgroup.center ↥(alternatingGroup (Fin m)) := by
      rw [Subgroup.mem_center_iff]
      intro g'
      have := Subgroup.mem_center_iff.1 hq (e.symm g')
      have h2 := congrArg e this
      simpa using h2
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    have h4 : 4 ≤ Nat.card (Fin m) := by simp; omega
    rw [alternatingGroup.center_eq_bot h4, Subgroup.mem_bot] at hcen
    simpa using hcen
  exact (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot.trans e)

theorem fullCoverLevel_alt (hc : S6Ctx G 3) (hk : KLevelAltAt) {X K : Subgroup G}
    (hK : GLAPComponent 3 X K) {m : ℕ} (h : IsAltPType 3 K m) (hm : 5 ≤ m) :
    (m = 7 ∨ m = 10 → fullCoverLevel 3 (PQuot 3 K) = 3) ∧ (11 ≤ m → fullCoverLevel 3 (PQuot 3 K) = 4) := by
  have hq := isQuasisimple_pQuot_of_glaPComponent hc.prime hK
  have hb := pQuot_primeCore_eq_bot Nat.prime_three K
  have hcat := isAltPType_catalogIs hm h
  obtain h1 := hk (PQuot 3 K) hq hb
  refine ⟨fun hm' => h1.1 ?_, fun hm' => h1.2 (Or.inl ⟨m, hm', hcat⟩)⟩
  rcases hm' with rfl | rfl
  · exact Or.inl hcat
  · exact Or.inr hcat

theorem fullCoverLevel_He (hc : S6Ctx G 3) (hk : KLevelAltAt) {X K : Subgroup G}
    (hK : GLAPComponent 3 X K) (h : IsSporType 3 K .He) : fullCoverLevel 3 (PQuot 3 K) = 4 :=
  (hk (PQuot 3 K) (isQuasisimple_pQuot_of_glaPComponent hc.prime hK) (pQuot_primeCore_eq_bot Nat.prime_three K)).2
    (Or.inr h)

theorem le_three_of_isSTriple {B K : Subgroup G} {a : G} (hS : IsSTriple 3 B a K)
    (hd : dLevel G 3 = 3) : ¬ IsGStar 3 B K ∧ fullCoverLevel 3 (PQuot 3 K) ≤ 3 := by
  have h := tripleLevel_le_dLevel hS
  rw [hd] at h
  unfold tripleLevel at h
  by_cases hG : IsGStar 3 B K
  · rw [if_pos hG] at h; omega
  · rw [if_neg hG] at h
    exact ⟨hG, by omega⟩

theorem tripleLevel_eq_three {B K : Subgroup G} (hG : ¬ IsGStar 3 B K)
    (h : fullCoverLevel 3 (PQuot 3 K) = 3) : tripleLevel 3 B K = 3 := by
  unfold tripleLevel
  rw [if_neg hG, h]
  rfl

theorem l73_card_B_inf_I (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) (hn : n = 10 ∨ n = 11)
    (hyB : y ∈ B) {a : G} {K T I Sg : Subgroup G} (C : L73Ctx B x L n y J a K T I Sg) :
    Nat.card ↥(B ⊓ I : Subgroup G) = 3 ^ 2 := by
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax hB).1
  have hxB : x ∈ B := (IsSStarMax.essential hB).1
  have hDB : altDxy x y ≤ B := sup_le ((Subgroup.zpowers_le).2 hxB) ((Subgroup.zpowers_le).2 hyB)
  obtain ⟨hBeq, hBinf⟩ := C.ti.B_eq_I hn
  have hB81 : Nat.card ↥B = 3 ^ 4 := l73_card_B hc hB S (by omega)
  have hEB : (B ⊓ I : Subgroup G) ≤ B := inf_le_left
  have hN : (B ⊓ I : Subgroup G) ≤ Subgroup.normalizer ((altDxy x y : Subgroup G) : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd =>
      isElemAbelian_commute hBel (hDB hd) (hEB hg))
  have h1 := card_sup_mul_card_inf_of_le_normalizer hN
  rw [← hBeq, hBinf, Subgroup.card_bot, hB81, S.card_D] at h1
  omega

theorem perfect_le_of_sup_solvable {H : Type*} [Group H] {N C P : Subgroup H} [N.Normal]
    (hC : Group.IsSolvable ↥C) (hP : ⁅P, P⁆ = P) (hPNC : P ≤ N ⊔ C) : P ≤ N := by
  set π := QuotientGroup.mk' N with hπ
  have h1 : ⁅P.map π, P.map π⁆ = P.map π := by
    rw [← Subgroup.map_commutator, hP]
  have hN : N.map π = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨n, hn, rfl⟩
    exact (QuotientGroup.eq_one_iff n).2 hn
  have h2 : P.map π ≤ C.map π := by
    have := Subgroup.map_mono (f := π) hPNC
    rwa [Subgroup.map_sup, hN, bot_sup_eq] at this
  haveI := hC
  haveI hCs : Group.IsSolvable ↥(C.map π) :=
    Group.isSolvable_of_surjective (f := π.subgroupMap C) (MonoidHom.subgroupMap_surjective π C)
  haveI hPs : Group.IsSolvable ↥(P.map π) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h2)
  haveI : Group.IsPerfect ↥(P.map π) := Subgroup.isPerfect_iff.2 h1
  have h3 : P.map π = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(P.map π) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable ↥(P.map π) hPs
  intro g hg
  have : π g ∈ P.map π := ⟨g, hg, rfl⟩
  rw [h3, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff g).1 this

theorem perfect_le_of_quotient_solvable {H : Type*} [Group H] {M P : Subgroup H} [M.Normal]
    (hq : Group.IsSolvable (H ⧸ M)) (hP : ⁅P, P⁆ = P) : P ≤ M := by
  set π := QuotientGroup.mk' M with hπ
  have h1 : ⁅P.map π, P.map π⁆ = P.map π := by
    rw [← Subgroup.map_commutator, hP]
  haveI hPs : Group.IsSolvable ↥(P.map π) := inferInstance
  haveI : Group.IsPerfect ↥(P.map π) := Subgroup.isPerfect_iff.2 h1
  have h3 : P.map π = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(P.map π) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable ↥(P.map π) hPs
  intro g hg
  have : π g ∈ P.map π := ⟨g, hg, rfl⟩
  rw [h3, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff g).1 this

theorem imageMod_perfect {p : ℕ} {L P : Subgroup G} (hPL : P ≤ L) (h : ⁅P, P⁆ = P) :
    ⁅imageMod p L P, imageMod p L P⁆ = imageMod p L P := by
  have h1 : ⁅P.subgroupOf L, P.subgroupOf L⁆ = P.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPL, h]
  unfold imageMod
  rw [← Subgroup.map_commutator, h1]

theorem layer_perfect {p : ℕ} (X : Subgroup G) : ⁅GLAPLayer p X, GLAPLayer p X⁆ = GLAPLayer p X := by
  refine le_antisymm (commutator_le_left_of_normalizes Subgroup.le_normalizer) (sSup_le fun K hK => ?_)
  have hK' : GLAPComponent p X K := hK
  calc K = ⁅K, K⁆ := (glaPComponent_perfect hK').symm
    _ ≤ ⁅GLAPLayer p X, GLAPLayer p X⁆ := Subgroup.commutator_mono (le_sSup hK) (le_sSup hK)

theorem l73_comm_B_ne {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    (hn : n = 10 ∨ n = 11) {a : G} {K T I Sg : Subgroup G} (C : L73Ctx B x L n y J a K T I Sg)
    (hBI : B ⊓ I ≠ ⊥) (hB3 : IsPGroup 3 B) : (⁅Sg, B⁆ : Subgroup G) ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hSB
  have hBC : B ≤ Subgroup.centralizer (Sg : Set G) := by
    rw [Subgroup.commutator_comm] at hSB
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hSB
  set CI : Subgroup ↥I := (Subgroup.centralizer (Sg : Set G)).subgroupOf I with hCI
  haveI hCIn : CI.Normal := by
    refine ⟨fun c hc i => ?_⟩
    rw [hCI, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hiN : (i : G) ∈ Subgroup.normalizer (Sg : Set G) := C.I_norm i.2
    have hs' : (i : G)⁻¹ * s * (i : G) ∈ Sg := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hiN) s).1 hs
      simpa using this
    have h1 := hc _ hs'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc s * ((i : G) * c * (i : G)⁻¹) = (i : G) * (((i : G)⁻¹ * s * (i : G)) * c) * (i : G)⁻¹ := by group
      _ = (i : G) * (c * ((i : G)⁻¹ * s * (i : G))) * (i : G)⁻¹ := by rw [h1]
      _ = (i : G) * c * (i : G)⁻¹ * s := by group
  set B' : Subgroup ↥I := (B ⊓ I).subgroupOf I with hB'
  set Y : Subgroup ↥I := Subgroup.normalClosure (B' : Set ↥I) with hY
  have hYC : Y ≤ CI := Subgroup.normalClosure_le_normal (fun b hb =>
    Subgroup.mem_subgroupOf.2 (hBC (Subgroup.mem_subgroupOf.1 hb).1))
  set O := GLAPPrimeCore 3 ↥I with hO
  let π : ↥I →* PQuot 3 I := QuotientGroup.mk' O
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  obtain ⟨f⟩ := C.ti.I_alt
  have hm : 5 ≤ Nat.card (Fin (n - 4)) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin (n - 4))) := alternatingGroup.isSimpleGroup hm
  haveI : IsSimpleGroup (PQuot 3 I) := f.isSimpleGroup
  haveI : (Y.map π).Normal := Subgroup.Normal.map (Subgroup.normalClosure_normal) π hπs
  have hcopO : Nat.Coprime 3 (Nat.card ↥O) := CFSG.pPrimeCore_coprime_card
  have hYtop : Y.map π = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Y.map π) with h | h
    · exfalso
      obtain ⟨b, hb, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBI |> fun ⟨⟨b, hb⟩, hb1⟩ =>
        (⟨b, hb, fun h => hb1 (Subtype.ext h)⟩ : ∃ b, b ∈ B ⊓ I ∧ b ≠ 1)
      have hbY : (⟨b, hb.2⟩ : ↥I) ∈ Y := Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 hb)
      have hπb : π ⟨b, hb.2⟩ = 1 := by
        have : π ⟨b, hb.2⟩ ∈ Y.map π := ⟨_, hbY, rfl⟩
        rw [h, Subgroup.mem_bot] at this; exact this
      have hbO : (⟨b, hb.2⟩ : ↥I) ∈ O := (QuotientGroup.eq_one_iff _).1 hπb
      obtain ⟨k, hk⟩ := hB3 ⟨b, hb.1⟩
      have h1 : orderOf (⟨b, hb.2⟩ : ↥I) ∣ 3 ^ k :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using congrArg Subtype.val hk))
      have h2 : orderOf (⟨b, hb.2⟩ : ↥I) ∣ Nat.card ↥O := Subgroup.orderOf_dvd_natCard _ hbO
      have := Nat.eq_one_of_dvd_coprimes (hcopO.pow_left k) h1 h2
      exact hb1 (congrArg Subtype.val (orderOf_eq_one_iff.1 this))
    · exact h
  have h3Y : ∀ (g : ↥I) (k : ℕ), g ^ 3 ^ k = 1 → g ∈ Y := by
    intro g k hgk
    haveI : Y.Normal := Subgroup.normalClosure_normal
    let ρ : ↥I →* ↥I ⧸ Y := QuotientGroup.mk' Y
    have hOs : O.map ρ = ⊤ := by
      rw [eq_top_iff]
      rintro z -
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Y z
      have : π w ∈ Y.map π := by rw [hYtop]; exact Subgroup.mem_top _
      obtain ⟨u, hu, hue⟩ := this
      have hwo : u⁻¹ * w ∈ O := by
        rw [← QuotientGroup.ker_mk' O]; show π (u⁻¹ * w) = 1; rw [map_mul, map_inv, hue, inv_mul_cancel]
      refine ⟨u⁻¹ * w, hwo, ?_⟩
      show ρ (u⁻¹ * w) = ρ w
      have hρu : ρ u = 1 := (QuotientGroup.eq_one_iff (N := Y) u).2 hu
      rw [map_mul, map_inv, hρu, inv_one, one_mul]
    have hcard : Nat.card (↥I ⧸ Y) ∣ Nat.card ↥O := by
      have := Subgroup.card_map_dvd O ρ
      rwa [hOs, Subgroup.card_top] at this
    have h1 : orderOf (ρ g) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hgk, map_one])
    have h2 : orderOf (ρ g) ∣ Nat.card ↥O := (orderOf_dvd_natCard (ρ g)).trans hcard
    have := Nat.eq_one_of_dvd_coprimes (hcopO.pow_left k) h1 h2
    exact (QuotientGroup.eq_one_iff g).1 (orderOf_eq_one_iff.1 this)
  have hIC : I ≤ Subgroup.centralizer (Sg : Set G) := by
    have hgen := C.ti.gen
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro g ⟨hgI, hg3⟩
    obtain ⟨k, hk⟩ := hg3 ⟨g, Subgroup.mem_zpowers g⟩
    have hgk : (⟨g, hgI⟩ : ↥I) ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    exact Subgroup.mem_subgroupOf.1 (hYC (h3Y _ k hgk))
  have hbot : (⁅Sg, I⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hIC
  exact C.S_ne (le_bot_iff.1 (C.S_comm.trans hbot.le))

theorem l73_not_Q8 {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    {a : G} {K T I Sg : Subgroup G} (C : L73Ctx B x L n y J a K T I Sg) :
    IsEmpty (↥Sg ≃* QuaternionGroup 2) := by
  refine ⟨fun e => ?_⟩
  have h24 : Nat.card (MulAut ↥Sg) = 24 :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.natCard_mulAut_of_quaternion e
  haveI : Finite (MulAut ↥Sg) := Nat.finite_of_card_ne_zero (by rw [h24]; norm_num)
  haveI : Fintype (MulAut ↥Sg) := Fintype.ofFinite _
  haveI hsolv : Group.IsSolvable (MulAut ↥Sg) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three
      (by norm_num) (a := 3) (b := 1) (by rw [← Nat.card_eq_fintype_card, h24]; norm_num)
  have hIN : I ≤ Subgroup.normalizer (Sg : Set G) := C.I_norm
  let φ : ↥I →* MulAut ↥Sg := Sg.normalizerMonoidHom.comp (Subgroup.inclusion hIN)
  haveI : Group.IsSolvable (↥I ⧸ φ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective φ)
  have hperfI : ⁅I, I⁆ = I := by rw [C.ti.I_eq]; exact layer_perfect _
  have hperf : ⁅(⊤ : Subgroup ↥I), (⊤ : Subgroup ↥I)⁆ = ⊤ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hperfI]
  have hker := perfect_le_of_quotient_solvable (M := φ.ker) inferInstance hperf
  have hcent : I ≤ Subgroup.centralizer (Sg : Set G) := by
    intro i hi
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 : φ ⟨i, hi⟩ = 1 := hker (Subgroup.mem_top _)
    have h2 := congrArg (fun α : MulAut ↥Sg => ((α ⟨s, hs⟩ : ↥Sg) : G)) h1
    have e1 : ((φ ⟨i, hi⟩ ⟨s, hs⟩ : ↥Sg) : G) = i * s * i⁻¹ := rfl
    simp only [MulAut.one_apply] at h2
    rw [e1] at h2
    calc s * i = (i * s * i⁻¹) * i := by rw [h2]
      _ = i * s := by group
  have hbot : (⁅Sg, I⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
  exact C.S_ne (le_bot_iff.1 (C.S_comm.trans hbot.le))

theorem l73_isEssential (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) (hn : n = 10 ∨ n = 11)
    (hyB : y ∈ B) {a : G} {K T I Sg : Subgroup G} (C : L73Ctx B x L n y J a K T I Sg) :
    IsEssential 3 B a := by
  have hxB : x ∈ B := (IsSStarMax.essential hB).1
  have hDB : altDxy x y ≤ B :=
    sup_le ((Subgroup.zpowers_le).2 hxB) ((Subgroup.zpowers_le).2 hyB)
  have hBD : B ≤ Subgroup.centralizer (altDxy x y : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 (fun d hd => isElemAbelian_commute (IsSStarMax.bmax hB).1 (hDB hd) hb)
  have hBS : B ≤ Subgroup.normalizer (Sg : Set G) :=
    C.S_eq ▸ l73_norm_S C.ti.I_eq C.a_mem (C.ti.B_le_N hn) (IsSStarMax.normalizes hB) hBD
  have hBI : B ⊓ I ≠ ⊥ := fun h => by
    have h9 := l73_card_B_inf_I hc hB S hn hyB C
    rw [h, Subgroup.card_bot] at h9
    norm_num at h9
  exact ⟨hDB C.a_mem, C.a_ne, Sg, C.S_le_Ca, C.S_two, hBS,
    l73_comm_B_ne hn C hBI (GLAIsBmax.isPGroup (IsSStarMax.bmax hB)), fun _ => l73_not_Q8 C⟩

theorem glaPLayer_eq_bot_of_solvable_image {p : ℕ} (hp : p.Prime) {L Y : Subgroup G} (hYL : Y ≤ L)
    (hsol : Group.IsSolvable ↥(imageMod p L Y)) : GLAPLayer p Y = ⊥ := by
  have hΛY : GLAPLayer p Y ≤ Y := sSup_le fun M hM => hM.1
  have hΛL : GLAPLayer p Y ≤ L := hΛY.trans hYL
  have hperf : ⁅GLAPLayer p Y, GLAPLayer p Y⁆ = GLAPLayer p Y := layer_perfect Y
  have himg : imageMod p L (GLAPLayer p Y) = ⊥ := by
    haveI := hsol
    have h2 : imageMod p L (GLAPLayer p Y) ≤ imageMod p L Y := imageMod_mono hΛY
    haveI hs : Group.IsSolvable ↥(imageMod p L (GLAPLayer p Y)) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h2)
    haveI : Group.IsPerfect ↥(imageMod p L (GLAPLayer p Y)) :=
      Subgroup.isPerfect_iff.2 (imageMod_perfect hΛL hperf)
    by_contra hne
    haveI : Nontrivial ↥(imageMod p L (GLAPLayer p Y)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable _ hs
  have hbot : GLAPLayer p Y ≤ GLAPPrimeCoreOf p L := (imageMod_eq_bot_iff hΛL).1 himg
  have hgen := genByPElts_layer hp Y
  rw [eq_bot_iff]
  refine hgen.trans ((Subgroup.closure_le _).2 ?_)
  rintro g ⟨hgΛ, hgp⟩
  have hgO : g ∈ GLAPPrimeCoreOf p L := hbot hgΛ
  obtain ⟨m, hm⟩ := isPGroup_zpowers_iff_exists_pow.1 hgp
  have hcop := CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp L
  have hord : orderOf g = 1 := by
    have h1 : orderOf g ∣ p ^ m := orderOf_dvd_of_pow_eq_one hm
    have h2 : orderOf g ∣ Nat.card ↥(GLAPPrimeCoreOf p L) := by
      have h3 : orderOf g = orderOf (⟨g, hgO⟩ : ↥(GLAPPrimeCoreOf p L)) :=
        Subgroup.orderOf_coe (⟨g, hgO⟩ : ↥(GLAPPrimeCoreOf p L))
      rw [h3]
      exact orderOf_dvd_natCard _
    exact (Nat.Coprime.pow_left m hcop |>.coprime_dvd_left h1).eq_one_of_dvd h2
  rw [SetLike.mem_coe, Subgroup.mem_bot]
  exact orderOf_eq_one_iff.1 hord

theorem exists_two_threeCycles {Q : Type} [Group Q] (e : Q ≃* ↥(alternatingGroup (Fin 10))) {F : Subgroup Q}
    (hF : IsElemAbelian 3 F) (h9 : 9 ≤ Nat.card ↥F) :
    ∃ q ∈ F, (permOfQ e q).cycleType = {3, 3} ∨ (permOfQ e q).cycleType = {3, 3, 3} := by
  classical
  by_contra hcon
  push Not at hcon
  let φ : Q →* Equiv.Perm (Fin 10) := (alternatingGroup (Fin 10)).subtype.comp e.toMonoidHom
  have hφinj : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hφ : ∀ q, φ q = permOfQ e q := fun q => rfl
  have hF' : IsElemAbelian 3 (F.map φ) := IsElemAbelian.map hF φ
  have hcard : Nat.card ↥(F.map φ) = Nat.card ↥F := Subgroup.card_map_of_injective hφinj
  have h13 : ∀ q ∈ F, permOfQ e q = 1 ∨ (permOfQ e q).cycleType = {3} := by
    intro q hq
    have h3 : (permOfQ e q) ^ 3 = 1 := by
      have h2 := congrArg φ (hF.2 q hq)
      rw [map_pow, map_one, hφ] at h2
      exact h2
    have hord : orderOf (permOfQ e q) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hall : ∀ m ∈ (permOfQ e q).cycleType, m = 3 := by
      intro m hm
      have h1 : m ∣ 3 := (Equiv.Perm.dvd_of_mem_cycleType hm).trans hord
      have h2 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
      exact ((Nat.dvd_prime Nat.prime_three).1 h1).resolve_left (by omega)
    have hrep : (permOfQ e q).cycleType = Multiset.replicate (Multiset.card (permOfQ e q).cycleType) 3 :=
      Multiset.eq_replicate.2 ⟨rfl, hall⟩
    have hsum : (permOfQ e q).cycleType.sum ≤ 10 := by
      rw [Equiv.Perm.sum_cycleType]
      exact (Finset.card_le_univ _).trans (by simp)
    have hk : Multiset.card (permOfQ e q).cycleType ≤ 3 := by
      have : (permOfQ e q).cycleType.sum = Multiset.card (permOfQ e q).cycleType * 3 := by
        conv_lhs => rw [hrep]
        simp
      omega
    obtain ⟨hne1, hne2⟩ := hcon q hq
    interval_cases hkk : Multiset.card (permOfQ e q).cycleType
    · left
      exact Equiv.Perm.cycleType_eq_zero.1 (by rw [hrep]; simp)
    · right
      rw [hrep]; simp
    · exact absurd (by rw [hrep]; simp) hne1
    · exact absurd (by rw [hrep]; simp) hne2
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (show F ≠ ⊥ by
    intro h
    rw [h, Subgroup.card_bot] at h9
    omega)
  have hσ3 : (permOfQ e (a : Q)).cycleType = {3} := by
    rcases h13 (a : Q) a.2 with h | h
    · exfalso
      apply ha1
      apply Subtype.ext
      apply e.injective
      apply Subtype.ext
      simpa [permOfQ] using h
    · exact h
  set σ := permOfQ e (a : Q) with hσdef
  have hS3 : σ.support.card = 3 := card_support_eq_of_cycleType hσ3
  have hfix : ∀ b ∈ F, ∀ i, i ∉ σ.support → permOfQ e b i = i := by
    intro b hb i hi
    by_contra hbi
    have hcomm : Commute (permOfQ e b) σ := by
      have h1 : b * (a : Q) = (a : Q) * b := congrArg Subtype.val (hF.1.is_comm.comm ⟨b, hb⟩ a)
      have h2 := congrArg (permOfQ e) h1
      rw [permOfQ_mul, permOfQ_mul] at h2
      exact h2
    have hb1 : permOfQ e b ≠ 1 := fun h => hbi (by rw [h]; rfl)
    have hb3 : (permOfQ e b).cycleType = {3} := (h13 b hb).resolve_left hb1
    have hbcyc : (permOfQ e b).IsCycle := (show (permOfQ e b).IsThreeCycle from hb3).isCycle
    have hdisj : Equiv.Perm.Disjoint σ (permOfQ e b) := by
      intro j
      by_contra hj
      push Not at hj
      obtain ⟨hjσ, hjb⟩ := hj
      obtain ⟨k, hk⟩ := hbcyc.sameCycle hjb hbi
      have hcomm' : Commute ((permOfQ e b) ^ k) σ := hcomm.zpow_left k
      have := Equiv.Perm.mem_support_iff_of_commute hcomm' j
      apply hi
      rw [← hk]
      exact this.2 (Equiv.Perm.mem_support.2 hjσ)
    have hmul := hdisj.cycleType_mul
    have hab : permOfQ e ((a : Q) * b) = σ * permOfQ e b := permOfQ_mul e _ _
    have hmem : (a : Q) * b ∈ F := F.mul_mem a.2 hb
    obtain ⟨hne1, hne2⟩ := hcon _ hmem
    apply hne1
    rw [hab, hmul, hσ3, hb3]
    rfl
  have hle := CFSG.Quasithin.H13.A7.card_le_pow_of_fixes (p := 3) (α := Fin 10) 3 σ.support hS3
    (F.map φ) (fun x hx y hy => by
      have := hF'.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this)
    (fun x hx => hF'.2 x hx)
    (by
      rintro _ ⟨b, hb, rfl⟩ i hi
      exact hfix b hb i hi)
  rw [hcard] at hle
  norm_num at hle
  omega

theorem centralizer_solvable_of_two_threeCycles {Q : Type} [Group Q]
    (e : Q ≃* ↥(alternatingGroup (Fin 10))) {q : Q}
    (h : (permOfQ e q).cycleType = {3, 3} ∨ (permOfQ e q).cycleType = {3, 3, 3}) :
    Group.IsSolvable ↥(Subgroup.centralizer ({q} : Set Q)) := by
  classical
  set σ : Equiv.Perm (Fin 10) := permOfQ e q with hσ
  have hsolv : Group.IsSolvable ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 10)))) := by
    have hcard := Equiv.Perm.nat_card_centralizer σ
    rcases h with h | h
    · rw [h] at hcard
      have h432 : Nat.card ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 10)))) = 2 ^ 4 * 3 ^ 3 := by
        rw [hcard]
        simp [Fintype.card_fin, Nat.factorial]
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h432)
    · rw [h] at hcard
      have h162 : Nat.card ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 10)))) = 2 ^ 1 * 3 ^ 4 := by
        rw [hcard]
        simp [Fintype.card_fin, Nat.factorial]
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h162)
  let φ : Q →* Equiv.Perm (Fin 10) := (alternatingGroup (Fin 10)).subtype.comp e.toMonoidHom
  have hφinj : Function.Injective φ := Subtype.val_injective.comp e.injective
  let ψ : ↥(Subgroup.centralizer ({q} : Set Q)) →*
      ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 10)))) :=
    (φ.comp (Subgroup.centralizer ({q} : Set Q)).subtype).codRestrict _ (fun c => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 c.2
      have h2 : φ (c : Q) * φ q = φ q * φ (c : Q) := by rw [← map_mul, ← map_mul, h1]
      exact h2)
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : φ (a : Q) = φ (b : Q) :=
      congrArg (fun z : ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 10)))) =>
        (z : Equiv.Perm (Fin 10))) hab
    exact Subtype.ext (hφinj h1)
  haveI := hsolv
  exact Group.isSolvable_of_isSolvable_injective (f := ψ) hψinj

theorem perm_cent_solvable {Q : Type} [Group Q] (e : Q ≃* ↥(alternatingGroup (Fin 10))) {F : Subgroup Q}
    (hF : IsElemAbelian 3 F) (h9 : 9 ≤ Nat.card ↥F) :
    Group.IsSolvable ↥(Subgroup.centralizer (F : Set Q)) := by
  obtain ⟨q, hqF, hq⟩ := exists_two_threeCycles e hF h9
  haveI := centralizer_solvable_of_two_threeCycles e hq
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hqF)))

theorem l73_not_gstar_ten (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L 10 y J) (hyB : y ∈ B) :
    ¬ IsGStar 3 B L := by
  rintro ⟨E, hEB, hEel, hE27, hne⟩
  rw [closureIn_eq_self (IsSStarMax.normalizes hB)] at hne
  apply hne
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax hB).1
  have hB81 : Nat.card ↥B = 3 ^ 4 := l73_card_B hc hB S (by norm_num)
  have hBL27 : Nat.card ↥(B ⊓ L : Subgroup G) = 3 ^ 3 := l73_card_BL hc hB S (by norm_num)
  have hF9 : 9 ≤ Nat.card ↥(E ⊓ L : Subgroup G) := by
    have hZN : E ≤ Subgroup.normalizer ((B ⊓ L : Subgroup G) : Set G) := fun g hg =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd =>
        isElemAbelian_commute hBel hd.1 (hEB hg))
    have h1 := card_sup_mul_card_inf_of_le_normalizer hZN
    have hle : Nat.card ↥((B ⊓ L : Subgroup G) ⊔ E) ≤ Nat.card ↥B :=
      Subgroup.card_le_of_le (sup_le inf_le_left hEB)
    have heq : ((B ⊓ L : Subgroup G) ⊓ E) = E ⊓ L := by
      ext g
      constructor
      · rintro ⟨⟨-, hgL⟩, hgE⟩
        exact ⟨hgE, hgL⟩
      · rintro ⟨hgE, hgL⟩
        exact ⟨⟨hEB hgE, hgL⟩, hgE⟩
    rw [heq, hBL27, hE27] at h1
    rw [hB81] at hle
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥((B ⊓ L : Subgroup G) ⊔ E) * Nat.card ↥(E ⊓ L : Subgroup G) ≤ 3 ^ 4 * 8 :=
      Nat.mul_le_mul hle (by omega)
    omega
  have hFel : IsElemAbelian 3 (E ⊓ L : Subgroup G) := isElemAbelian_mono hEel inf_le_left
  obtain ⟨hF1, hF2⟩ := imageMod_elemAbelian hc.prime (inf_le_right : E ⊓ L ≤ L) hFel
  obtain ⟨e⟩ := S.alt
  have hsolv := perm_cent_solvable e hF1 (by rw [hF2]; exact hF9)
  have himg : imageMod 3 L (L ⊓ Subgroup.centralizer (E : Set G)) ≤
      Subgroup.centralizer ((imageMod 3 L (E ⊓ L) : Subgroup (PQuot 3 L)) : Set (PQuot 3 L)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨f, hf, rfl⟩
    have hgC := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).2
    have hfE : (f : G) ∈ E := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hf)).1
    have hcomm : (f : G) * (g : G) = (g : G) * (f : G) := Subgroup.mem_centralizer_iff.1 hgC (f : G) hfE
    show QuotientGroup.mk' _ f * QuotientGroup.mk' _ g = QuotientGroup.mk' _ g * QuotientGroup.mk' _ f
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  haveI := hsolv
  exact glaPLayer_eq_bot_of_solvable_image hc.prime inf_le_left
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective himg))

theorem l73_dLevel_three (hc : S6Ctx G 3) (hk : KLevelAltAt) {B : Subgroup G} {x : G} {L : Subgroup G}
    {y : G} {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L 10 y J) (hyB : y ∈ B) :
    dLevel G 3 = 3 := by
  have hnG := l73_not_gstar_ten hc hB S hyB
  have hlev := (fullCoverLevel_alt hc hk (IsSStarMax.component hB) (m := 10) S.alt (by norm_num)).1
    (Or.inr rfl)
  have h := IsSStarMax.level hB
  rw [tripleLevel_eq_three hnG hlev] at h
  exact h.symm


theorem l73_false_of_S_le_core (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} {a : G} {K T I Sg : Subgroup G} (C : L73Ctx B x L n y J a K T I Sg)
    (hS : Sg ≤ GLAPPrimeCoreOf 3 K)
    (hodd : Odd (Nat.card ↥(⁅K, GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))⁆ : Subgroup G))) :
    False := by
  have hIK : I ≤ K := C.ti.I_le_J.trans C.J_le_K
  have hOle : GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) :=
    glaPPrimeCoreOf_le_of_isSubnormal hc.prime C.K_sn
  have hle : Sg ≤ (⁅K, GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))⁆ : Subgroup G) := by
    calc Sg ≤ ⁅Sg, I⁆ := C.S_comm
      _ ≤ ⁅GLAPPrimeCoreOf 3 K, K⁆ := Subgroup.commutator_mono hS hIK
      _ = ⁅K, GLAPPrimeCoreOf 3 K⁆ := Subgroup.commutator_comm _ _
      _ ≤ ⁅K, GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))⁆ := Subgroup.commutator_mono le_rfl hOle
  exact false_of_twoGroup_le_odd C.S_two C.S_ne hle hodd

theorem l73_prod_level (hc : S6Ctx G 3) (hk : KLevelAltAt) (i2prod : I2ProdAt G) {B : Subgroup G} {x : G}
    {L : Subgroup G} {y : G} {J : Subgroup G} (S : AltSetup 3 B x L 10 y J) {a b : G} {M K : Subgroup G}
    (hP : L73Prod b a M K J) : fullCoverLevel 3 (PQuot 3 M) = 3 := by
  obtain ⟨hM, hbM, hbbM, hKeq, hba, hb3, hJK, hJc⟩ := hP
  obtain ⟨φ, ψ₁, -, -, -⟩ := i2prod a b M K J hM hbM hbbM hKeq hba hb3 hJK hJc
  have hJ7 : catalogIs (PSimple 3 J) (isAltN 7) := isAltPType_catalogIs (by norm_num) S.J_alt
  have hM7 : catalogIs (PSimple 3 M) (isAltN 7) := (catalogIs_congr ψ₁).1 hJ7
  exact (hk (PQuot 3 M) (isQuasisimple_pQuot_of_glaPComponent hc.prime hM) (pQuot_primeCore_eq_bot Nat.prime_three M)).1
    (Or.inl hM7)

theorem centralizer_rootAlt_seven {Q : Type} [Group Q] (e : Q ≃* ↥(alternatingGroup (Fin 7))) {H : Subgroup Q}
    (h : IsRootAlt e H 6) : Subgroup.centralizer (H : Set Q) = ⊥ := by
  classical
  obtain ⟨⟨φ⟩, -⟩ := h
  haveI : Finite Q := Finite.of_equiv _ e.toEquiv.symm
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hA7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hH : Nat.card ↥H = 360 := by
    rw [Nat.card_congr φ.toEquiv, hA6]
  have hQ : Nat.card Q = 2520 := by
    rw [Nat.card_congr e.toEquiv, hA7]
  have hZ : H ⊓ Subgroup.centralizer (H : Set Q) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxH, hxC⟩
    have hcen : φ ⟨x, hxH⟩ ∈ Subgroup.center ↥(alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := φ.surjective g
      have hk : (k : Q) * x = x * k := Subgroup.mem_centralizer_iff.1 hxC k.1 k.2
      have hk' : k * (⟨x, hxH⟩ : ↥H) = (⟨x, hxH⟩ : ↥H) * k := Subtype.ext hk
      have := congrArg φ hk'
      rw [map_mul, map_mul] at this
      exact this
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hcen
    have hx1 : (⟨x, hxH⟩ : ↥H) = 1 := φ.injective (hcen.trans (map_one φ).symm)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hx1)
  have hle : Subgroup.centralizer (H : Set Q) ≤ Subgroup.normalizer (H : Set Q) :=
    Subgroup.centralizer_le_normalizer _
  have hcard := card_sup_mul_card_inf_of_le_normalizer hle
  rw [hZ, Subgroup.card_bot, hH, mul_one] at hcard
  have hdvd : 360 * Nat.card ↥(Subgroup.centralizer (H : Set Q)) ∣ 2520 := by
    rw [← hcard, ← hQ]
    exact Subgroup.card_subgroup_dvd_card _
  have h7 : Nat.card ↥(Subgroup.centralizer (H : Set Q)) ∣ 7 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 360) (by simpa using hdvd)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 h7 with h1 | h7'
  · exact Subgroup.card_eq_one.1 h1
  · exfalso
    have hsup : Nat.card ↥(H ⊔ Subgroup.centralizer (H : Set Q)) = 2520 := by
      rw [h7'] at hcard
      omega
    have htop : H ⊔ Subgroup.centralizer (H : Set Q) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hsup, hQ])
    have hN : Subgroup.normalizer (H : Set Q) = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact sup_le Subgroup.le_normalizer hle
    have hnorm : H.Normal := Subgroup.normalizer_eq_top_iff.1 hN
    have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hcardN : Nat.card ↥(H.map e.toMonoidHom) = 360 := by
      rw [Subgroup.card_map_of_injective e.injective, hH]
    haveI : (H.map e.toMonoidHom).Normal := Subgroup.Normal.map hnorm e.toMonoidHom e.surjective
    rcases hsimple.eq_bot_or_eq_top_of_normal (H.map e.toMonoidHom) with hb | ht
    · rw [hb, Subgroup.card_bot] at hcardN
      norm_num at hcardN
    · rw [ht, Subgroup.card_top, hA7] at hcardN
      norm_num at hcardN

theorem l73_two_group_trivial_of_roots (i2013 : I2013At) {P Q₁ Q₂ Q₃ : Type} [Group P] [Group Q₁] [Group Q₂]
    [Group Q₃] (π₁ : P →* Q₁) (π₂ : P →* Q₂) (π₃ : P →* Q₃)
    (hinj : ∀ g : P, π₁ g = 1 → π₂ g = 1 → π₃ g = 1 → g = 1)
    (e₁ : Q₁ ≃* ↥(alternatingGroup (Fin 7))) (e₂ : Q₂ ≃* ↥(alternatingGroup (Fin 7)))
    (e₃ : Q₃ ≃* ↥(alternatingGroup (Fin 7))) {R H : Subgroup P} (hR : IsPGroup 2 R)
    (hHR : H ≤ Subgroup.normalizer (R : Set P))
    (h₁ : IsRootAlt e₁ (H.map π₁) 6) (h₂ : IsRootAlt e₂ (H.map π₂) 6)
    (h₃ : IsRootAlt e₃ (H.map π₃) 6) : R = ⊥ := by
  have key : ∀ {Q : Type} [Group Q] (π : P →* Q) (e : Q ≃* ↥(alternatingGroup (Fin 7))),
      IsRootAlt e (H.map π) 6 → ∀ r ∈ R, π r = 1 := by
    intro Q _ π e h r hr
    have hnorm : H.map π ≤ Subgroup.normalizer ((R.map π : Subgroup Q) : Set Q) :=
      (Subgroup.map_mono hHR).trans (Subgroup.le_normalizer_map π)
    have hcen := i2013 Q 7 6 e (H.map π) (by norm_num) (by norm_num) h (R.map π) (hR.map π) hnorm
    have hle : R.map π ≤ Subgroup.centralizer ((H.map π : Subgroup Q) : Set Q) :=
      Subgroup.le_centralizer_iff.1 hcen
    rw [centralizer_rootAlt_seven e h] at hle
    have := hle (Subgroup.mem_map_of_mem π hr)
    simpa using this
  rw [eq_bot_iff]
  intro r hr
  exact (Subgroup.mem_bot).2 (hinj r (key π₁ e₁ h₁ r hr) (key π₂ e₂ h₂ r hr) (key π₃ e₃ h₃ r hr))

private theorem y5x_isRootAlt_comp_iff {X Y : Type} [Group X] [Group Y] {N : ℕ} (α : X ≃* Y)
    (e₀ : Y ≃* ↥(alternatingGroup (Fin N))) (H : Subgroup X) (m : ℕ) :
    IsRootAlt (α.trans e₀) H m ↔ IsRootAlt e₀ (H.map α.toMonoidHom) m := by
  have hset : {i | ∃ h ∈ H, ((e₀ (α h) : alternatingGroup (Fin N)) : Equiv.Perm (Fin N)) i ≠ i} =
      {i | ∃ h ∈ H.map α.toMonoidHom,
        ((e₀ h : alternatingGroup (Fin N)) : Equiv.Perm (Fin N)) i ≠ i} := by
    ext i
    constructor
    · rintro ⟨h, hh, hi⟩
      exact ⟨α h, ⟨h, hh, rfl⟩, hi⟩
    · rintro ⟨h', ⟨h, hh, rfl⟩, hi⟩
      exact ⟨h, hh, hi⟩
  unfold IsRootAlt MovesExactly movedLettersOf
  refine and_congr ?_ ?_
  · constructor
    · rintro ⟨φ⟩
      exact ⟨(Subgroup.equivMapOfInjective H α.toMonoidHom α.injective).symm.trans φ⟩
    · rintro ⟨φ⟩
      exact ⟨(Subgroup.equivMapOfInjective H α.toMonoidHom α.injective).trans φ⟩
  · simp only [MulEquiv.trans_apply]
    rw [hset]

private theorem y5x_map_map_symm_eq {X Y : Type} [Group X] [Group Y] (α : X ≃* Y) (H : Subgroup X) :
    (H.map α.toMonoidHom).map α.symm.toMonoidHom = H := by
  have hid : α.symm.toMonoidHom.comp α.toMonoidHom = MonoidHom.id X := by
    ext x
    simp
  rw [Subgroup.map_map, hid, Subgroup.map_id]

theorem l73_root_transport {J I : Subgroup G} {Q : Type} [Group Q]
    (eJ : PQuot 3 J ≃* ↥(alternatingGroup (Fin 7))) (hroot : IsRootAlt eJ (imageMod 3 J I) 6)
    (ψ : PSimple 3 J ≃* Q) :
    ∃ e : Q ≃* ↥(alternatingGroup (Fin 7)),
      IsRootAlt e (((imageMod 3 J I).map (QuotientGroup.mk' (Subgroup.center (PQuot 3 J)))).map ψ.toMonoidHom) 6 := by
  classical
  have hc : Subgroup.center (PQuot 3 J) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have hcen : eJ q ∈ Subgroup.center ↥(alternatingGroup (Fin 7)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := Subgroup.mem_center_iff.1 hq (eJ.symm g)
      have h2 := congrArg eJ h1
      simpa using h2
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.2 (eJ.injective (hcen.trans (map_one eJ).symm))
  let θ : PSimple 3 J ≃* PQuot 3 J :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hθ : ∀ q : PQuot 3 J, θ (QuotientGroup.mk' (Subgroup.center (PQuot 3 J)) q) = q :=
    fun q => rfl
  let H' : Subgroup (PSimple 3 J) :=
    (imageMod 3 J I).map (QuotientGroup.mk' (Subgroup.center (PQuot 3 J)))
  have hH' : H'.map θ.toMonoidHom = imageMod 3 J I := by
    have hid : θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (PQuot 3 J))) =
        MonoidHom.id (PQuot 3 J) := by
      ext q
      exact hθ q
    rw [show H'.map θ.toMonoidHom = (imageMod 3 J I).map
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (PQuot 3 J)))) from
        (Subgroup.map_map _ _ _), hid, Subgroup.map_id]
  refine ⟨ψ.symm.trans (θ.trans eJ), ?_⟩
  refine (y5x_isRootAlt_comp_iff ψ.symm (θ.trans eJ) (H'.map ψ.toMonoidHom) 6).2 ?_
  rw [y5x_map_map_symm_eq ψ H']
  exact (y5x_isRootAlt_comp_iff θ eJ H' 6).2 (by rw [hH']; exact hroot)

theorem l73_le_core_of_image_center {K S : Subgroup G} (hSK : S ≤ K) (hS2 : IsPGroup 2 S)
    (h : (imageMod 3 K S).map (QuotientGroup.mk' (Subgroup.center (PQuot 3 K))) = ⊥) :
    S ≤ GLAPPrimeCoreOf 3 K := by
  rw [← imageMod_eq_bot_iff hSK]
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  rw [eq_bot_iff]
  intro q hq
  have hqc : q ∈ Subgroup.center (PQuot 3 K) := h hq
  obtain ⟨g, hg, rfl⟩ := hq
  have hgS : (g : G) ∈ S := hg
  obtain ⟨k, hk⟩ := hS2 ⟨(g : G), hgS⟩
  set q := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) g with hq
  have hq2 : q ^ (2 ^ k) = 1 := by
    have h1 : (g : G) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hk' : g ^ (2 ^ k) = 1 := Subtype.ext (by simpa using h1)
    rw [hq, ← map_pow, hk', map_one]
  have hle : Subgroup.zpowers q ≤ Subgroup.center (PQuot 3 K) := (Subgroup.zpowers_le).2 hqc
  have hnorm : (Subgroup.zpowers q).Normal := by
    refine ⟨fun n hn x => ?_⟩
    have hc : x * n = n * x := Subgroup.mem_center_iff.1 (hle hn) x
    rw [hc, mul_inv_cancel_right]
    exact hn
  have hcop : Nat.Coprime 3 (Nat.card ↥(Subgroup.zpowers q)) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hq2)
      (Nat.Coprime.pow_right k (by norm_num))
  have hbot := (CFSG.pPrimeCore_eq_bot_iff).1 (pQuot_primeCore_eq_bot Nat.prime_three K) _ hnorm hcop
  have hmem : q ∈ Subgroup.zpowers q := Subgroup.mem_zpowers q
  rw [hbot] at hmem
  exact hmem

theorem l73_prod_S_le_core (i2prod : I2ProdAt G) (i2013 : I2013At) {B : Subgroup G} {x : G}
    {L : Subgroup G} {y : G} {J : Subgroup G} (S : AltSetup 3 B x L 10 y J) {a : G} {K T I Sg : Subgroup G}
    (C : L73Ctx B x L 10 y J a K T I Sg) {b : G} {M : Subgroup G} (hP : L73Prod b a M K J) :
    Sg ≤ GLAPPrimeCoreOf 3 K := by
  obtain ⟨hM, hbM, hbbM, hKeq, hba, hb3, hJK, hJc⟩ := hP
  obtain ⟨φ, ψ₁, ψ₂, ψ₃, hdiag⟩ := i2prod a b M K J hM hbM hbbM hKeq hba hb3 hJK hJc
  have hIJ : I ≤ J := C.ti.I_le_J
  have hIK : I ≤ K := hIJ.trans hJK
  have hJ7 : IsAltPType 3 J 7 := S.J_alt
  obtain ⟨eJ⟩ := hJ7
  have hroot : IsRootAlt eJ (imageMod 3 J I) 6 := l73_root_in_J S C.ti (by norm_num) eJ
  obtain ⟨hT2, hnorm⟩ := l72_imageMod_facts (p := 3) hIK C.S_le_K C.S_two C.I_norm
  let zK : PQuot 3 K →* PSimple 3 K := QuotientGroup.mk' (Subgroup.center (PQuot 3 K))
  let zJ : PQuot 3 J →* PSimple 3 J := QuotientGroup.mk' (Subgroup.center (PQuot 3 J))
  let Rk : Subgroup (PSimple 3 K) := (imageMod 3 K Sg).map zK
  let Hk : Subgroup (PSimple 3 K) := (imageMod 3 K I).map zK
  let Ib : Subgroup (PSimple 3 J) := (imageMod 3 J I).map zJ
  let π₁ : PSimple 3 K →* PSimple 3 M := (MonoidHom.fst _ _).comp φ.toMonoidHom
  let π₂ : PSimple 3 K →* PSimple 3 M :=
    ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)).comp φ.toMonoidHom
  let π₃ : PSimple 3 K →* PSimple 3 M :=
    ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)).comp φ.toMonoidHom
  have key : ∀ (π : PSimple 3 K →* PSimple 3 M) (ψ : PSimple 3 J ≃* PSimple 3 M),
      (∀ j : ↥J, π (QuotientGroup.mk (QuotientGroup.mk (⟨(j : G), hJK j.2⟩ : ↥K))) =
        ψ (QuotientGroup.mk (QuotientGroup.mk j))) → Hk.map π = Ib.map ψ.toMonoidHom := by
    intro π ψ hπ
    ext z
    constructor
    · rintro ⟨h, ⟨q, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
      have hgI : (g : G) ∈ I := hg
      refine ⟨_, ⟨_, ⟨⟨(g : G), hIJ hgI⟩, hgI, rfl⟩, rfl⟩, ?_⟩
      exact (hπ ⟨(g : G), hIJ hgI⟩).symm
    · rintro ⟨h, ⟨q, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
      have hgI : (g : G) ∈ I := hg
      refine ⟨_, ⟨_, ⟨⟨(g : G), hJK g.2⟩, hgI, rfl⟩, rfl⟩, ?_⟩
      exact hπ g
  have hH₁ : Hk.map π₁ = Ib.map ψ₁.toMonoidHom := key π₁ ψ₁ fun j => congrArg Prod.fst (hdiag j)
  have hH₂ : Hk.map π₂ = Ib.map ψ₂.toMonoidHom := key π₂ ψ₂ fun j => congrArg (fun r => r.2.1) (hdiag j)
  have hH₃ : Hk.map π₃ = Ib.map ψ₃.toMonoidHom := key π₃ ψ₃ fun j => congrArg (fun r => r.2.2) (hdiag j)
  obtain ⟨e₁, he₁⟩ := l73_root_transport eJ hroot ψ₁
  obtain ⟨e₂, he₂⟩ := l73_root_transport eJ hroot ψ₂
  obtain ⟨e₃, he₃⟩ := l73_root_transport eJ hroot ψ₃
  have hR2 : IsPGroup 2 ((imageMod 3 K Sg).map zK) := hT2.map zK
  have hHR : Hk ≤ Subgroup.normalizer (((imageMod 3 K Sg).map zK : Subgroup (PSimple 3 K)) : Set (PSimple 3 K)) :=
    (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map zK)
  have hinj : ∀ g : PSimple 3 K, π₁ g = 1 → π₂ g = 1 → π₃ g = 1 → g = 1 := by
    intro g h1 h2 h3
    apply φ.injective
    rw [map_one]
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hbot : (imageMod 3 K Sg).map zK = ⊥ :=
    l73_two_group_trivial_of_roots i2013 π₁ π₂ π₃ hinj e₁ e₂ e₃ hR2 hHR (hH₁ ▸ he₁) (hH₂ ▸ he₂) (hH₃ ▸ he₃)
  exact l73_le_core_of_image_center C.S_le_K C.S_two hbot

private theorem y5x_glbConj_le {C A : Subgroup G} {g : G} (hg : g ∈ C) (hA : A ≤ C) :
    GLBConj g A ≤ C := by
  intro y hy
  rw [mem_gLBConj] at hy
  have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
  rw [e]
  exact C.mul_mem (C.mul_mem (C.inv_mem hg) (hA hy)) hg

private theorem y5x_card_glbConj (g : G) (H : Subgroup G) :
    Nat.card ↥(GLBConj g H) = Nat.card ↥H := by
  unfold GLBConj
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

private theorem y5x_glbConj_commutator (M O : Subgroup G) (g : G) (hg : GLBConj g O = O) :
    ⁅GLBConj g M, O⁆ = GLBConj g ⁅M, O⁆ := by
  unfold GLBConj at hg ⊢
  rw [Subgroup.map_commutator, hg]

private theorem y5x_map_conj_glbConj (c x : G) (H : Subgroup G) :
    (GLBConj x H).map (MulAut.conj c).toMonoidHom = GLBConj (x * c⁻¹) H := by
  unfold GLBConj
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem y5x_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hA hB ⊢
  unfold GLBConj at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

private theorem y5x_odd_iSup_of_normalized {O : Subgroup G} {ι : Type} [Finite ι]
    (f : ι → Subgroup G) (hle : ∀ i, f i ≤ O)
    (hn : ∀ i, O ≤ Subgroup.normalizer ((f i : Subgroup G) : Set G))
    (hodd : ∀ i, Odd (Nat.card ↥(f i))) :
    Odd (Nat.card ↥(⨆ i, f i)) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, Odd (Nat.card ↥(s.sup f)) ∧ s.sup f ≤ O ∧
      O ≤ Subgroup.normalizer ((s.sup f : Subgroup G) : Set G) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨by simp, bot_le, fun o _ => ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro h
      simp
    | insert i s hi ih =>
      obtain ⟨hA, hAle, hAn⟩ := ih
      have hBA : f i ≤ Subgroup.normalizer ((s.sup f : Subgroup G) : Set G) := (hle i).trans hAn
      have hcard := card_sup_mul_card_inf_of_le_normalizer hBA
      have hodd2 : Odd (Nat.card ↥(s.sup f ⊔ f i) * Nat.card ↥(s.sup f ⊓ f i)) := by
        rw [hcard]
        exact hA.mul (hodd i)
      rw [Finset.sup_insert]
      refine ⟨?_, sup_le (hle i) hAle, fun o ho => ?_⟩
      · rw [sup_comm]
        exact (Nat.odd_mul.1 hodd2).1
      · rw [sup_comm]
        exact y5x_normalizer_sup (hAn ho) (hn i ho)
  have hall := (key Finset.univ).1
  rw [Finset.sup_univ_eq_iSup] at hall
  exact hall

theorem l73_prod_odd (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {J : Subgroup G}
    (hB : IsSStarMax 3 B x L) {a b : G} (hess : IsEssential 3 B a) (hd : dLevel G 3 = 3)
    {M K : Subgroup G} (hP : L73Prod b a M K J) (hlev : fullCoverLevel 3 (PQuot 3 M) = 3) :
    Odd (Nat.card ↥(⁅K, GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))⁆ : Subgroup G)) := by
  classical
  obtain ⟨hM, -, -, hKeq, hba, -, -, -⟩ := hP
  have hST : IsSTriple 3 B a M := ⟨IsSStarMax.bmax hB, hess, hM⟩
  have hS0 : IsS0 3 B a M :=
    ⟨hST, (tripleLevel_eq_three (le_three_of_isSTriple hST hd).1 hlev).trans hd.symm⟩
  have hodd : Odd (Nat.card ↥(⁅M, GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))⁆ : Subgroup G)) :=
    hc.stage4.1 B a M hS0
  set C := Subgroup.centralizer ({a} : Set G) with hCdef
  set O := GLAPPrimeCoreOf 3 C with hOdef
  have hMC : M ≤ C := hM.1
  have hCO : C ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 C
  have hnormO : ∀ x ∈ C, ∀ o ∈ O, x * o * x⁻¹ ∈ O := fun x hx o ho =>
    (Subgroup.mem_normalizer_iff.1 (hCO hx) o).1 ho
  have hOn : ∀ g ∈ C, GLBConj g O = O := fun g hg => mem_normalizer_iff_gLBConj_eq.1 (hCO hg)
  let f : C → Subgroup G := fun c => ⁅GLBConj (c : G) M, O⁆
  have hGC1 : ∀ c : C, GLBConj (c : G) M ≤ C := fun c => y5x_glbConj_le c.2 hMC
  have hfle : ∀ c : C, f c ≤ O := fun c => by
    refine Subgroup.commutator_le.2 fun x hx o ho => ?_
    rw [commutatorElement_def]
    exact O.mul_mem (hnormO x (hGC1 c hx) o ho) (O.inv_mem ho)
  have hfn : ∀ c : C, O ≤ Subgroup.normalizer ((f c : Subgroup G) : Set G) := fun c =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hfle c)).1
      (normal_subgroupOf_commutator ((hGC1 c).trans hCO))
  have hfodd : ∀ c : C, Odd (Nat.card ↥(f c)) := fun c => by
    show Odd (Nat.card ↥(⁅GLBConj (c : G) M, O⁆ : Subgroup G))
    rw [y5x_glbConj_commutator M O (c : G) (hOn c c.2), y5x_card_glbConj]
    exact hodd
  have hRodd : Odd (Nat.card ↥(⨆ c : C, f c)) :=
    y5x_odd_iSup_of_normalized f hfle hfn hfodd
  set R : Subgroup G := ⨆ c : C, f c with hRdef
  have hRle : R ≤ O := iSup_le hfle
  have hmem : ∀ g ∈ C, ⁅GLBConj g M, O⁆ ≤ R := fun g hg => le_iSup f ⟨g, hg⟩
  have hRC : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    intro c hc
    have hOφ : O.map (MulAut.conj c).toMonoidHom = O := by
      have h1 := y5x_map_conj_glbConj c 1 O
      rw [gLBConj_one, one_mul] at h1
      rw [h1]
      exact hOn c⁻¹ (C.inv_mem hc)
    have hmap : R.map (MulAut.conj c).toMonoidHom ≤ R := by
      rw [hRdef, Subgroup.map_iSup]
      refine iSup_le fun i => ?_
      show (⁅GLBConj (i : G) M, O⁆ : Subgroup G).map (MulAut.conj c).toMonoidHom ≤ R
      rw [Subgroup.map_commutator, y5x_map_conj_glbConj, hOφ]
      exact hmem _ (C.mul_mem i.2 (C.inv_mem hc))
    intro r hr
    exact hmap (Subgroup.mem_map.2 ⟨r, hr, rfl⟩)
  let S : Subgroup G :=
    { carrier := {k | k ∈ C ∧ ∀ o ∈ O, ⁅k, o⁆ ∈ R}
      mul_mem' := by
        rintro k k' ⟨hk, hkO⟩ ⟨hk', hk'O⟩
        refine ⟨C.mul_mem hk hk', fun o ho => ?_⟩
        have e : ⁅k * k', o⁆ = k * ⁅k', o⁆ * k⁻¹ * ⁅k, o⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact R.mul_mem (hRC k hk _ (hk'O o ho)) (hkO o ho)
      one_mem' := ⟨C.one_mem, fun o _ => by simp⟩
      inv_mem' := by
        rintro k ⟨hk, hkO⟩
        refine ⟨C.inv_mem hk, fun o ho => ?_⟩
        have e : ⁅k⁻¹, o⁆ = k⁻¹ * (⁅k, o⁆)⁻¹ * k⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hRC k⁻¹ (C.inv_mem hk) _ (R.inv_mem (hkO o ho)) }
  have hS_mem : ∀ k, k ∈ S ↔ k ∈ C ∧ ∀ o ∈ O, ⁅k, o⁆ ∈ R := fun k => Iff.rfl
  have hMS : M ≤ S := fun m hm => by
    rw [hS_mem]
    refine ⟨hMC hm, fun o ho => ?_⟩
    have h1 : (⁅M, O⁆ : Subgroup G) ≤ R := by
      have h2 := hmem 1 C.one_mem
      rwa [gLBConj_one] at h2
    exact h1 (Subgroup.commutator_mem_commutator hm ho)
  have hbMS : GLBConj b M ≤ S := fun y hy => by
    rw [hS_mem]
    refine ⟨y5x_glbConj_le hba hMC hy, fun o ho => ?_⟩
    exact hmem b hba (Subgroup.commutator_mem_commutator hy ho)
  have hbbMS : GLBConj b (GLBConj b M) ≤ S := fun y hy => by
    rw [hS_mem]
    refine ⟨y5x_glbConj_le hba (y5x_glbConj_le hba hMC) hy, fun o ho => ?_⟩
    have h2 : (⁅GLBConj b (GLBConj b M), O⁆ : Subgroup G) ≤ R := by
      rw [gLBConj_gLBConj]
      exact hmem (b * b) (C.mul_mem hba hba)
    exact h2 (Subgroup.commutator_mem_commutator hy ho)
  have hKS : K ≤ S := by
    rw [hKeq]
    exact sup_le (sup_le hMS hbMS) hbbMS
  have hcomm : ⁅K, O⁆ ≤ R :=
    Subgroup.commutator_le.2 fun k hk o ho => ((hS_mem k).1 (hKS hk)).2 o ho
  exact Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_le hcomm)

theorem l73_n10 (hc : S6Ctx G 3) (i183 : Input18_3_4) (i2013 : I2013At) (i1415 : I1415SevenAt G)
    (hk : KLevelAltAt) (i2prod : I2ProdAt G) {B : Subgroup G} {x : G} {L : Subgroup G} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L 10 y J) (hyB : y ∈ B) {a : G}
    {K T I Sg : Subgroup G} (C : L73Ctx B x L 10 y J a K T I Sg) : False := by
  have hess := l73_isEssential hc hB S (Or.inl rfl) hyB C
  have hd := l73_dLevel_three hc hk hB S hyB
  have hXK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) := kGroup_centralizer hc C.a_ne
  have hsh := l73_shape hc i183 hB S C.a_mem C.a_ne
  rw [← C.K_eq] at hsh
  have hIK : I ≤ K := C.ti.I_le_J.trans C.J_le_K
  rcases hsh with hK | ⟨b, M, hbD, hba, hP⟩
  · obtain ⟨b, hbD, hba, hDab⟩ := exists_pair_of_card_sq hc.prime S.card_D C.a_mem C.a_ne
      S.isElemAbelian_D
    have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := hK.comp.1
    have hJb : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J := by
      rw [← inf_centralizer_D_eq hKa hDab]; exact hK.J_comp
    have hb3 : b ^ 3 = 1 := S.isElemAbelian_D.2 b hbD
    have hbK : b ∈ Subgroup.normalizer (K : Set G) := hK.norm hbD
    have hJ7 : IsAltPType 3 J 7 := S.J_alt
    have hST : IsSTriple 3 B a K := ⟨IsSStarMax.bmax hB, hess, hK.comp⟩
    obtain ⟨hnG, hle3⟩ := le_three_of_isSTriple hST hd
    rcases i1415 (Subgroup.centralizer ({a} : Set G)) K J b hXK hK.comp hbK hb3 hJb hJ7 with
      ⟨k, hKalt⟩ | hHe
    · have hk1 : k ≤ 1 := by
        by_contra hk2
        have := (fullCoverLevel_alt hc hk hK.comp hKalt (by omega)).2 (by omega)
        omega
      have hlev3 : fullCoverLevel 3 (PQuot 3 K) = 3 :=
        (fullCoverLevel_alt hc hk hK.comp hKalt (by omega)).1 (by omega)
      obtain ⟨eK⟩ := hKalt
      obtain ⟨N', e', hN', hroot⟩ := l73_rootK hc S C hK hbD hDab eK (by norm_num)
      have hSO := l73_S_le_core i2013 hIK C.S_le_K C.S_two C.I_norm C.S_comm e' (by norm_num) hN' hroot
      have hS0 : IsS0 3 B a K := ⟨hST, (tripleLevel_eq_three hnG hlev3).trans hd.symm⟩
      exact l73_false_of_S_le_core hc C hSO (hc.stage4.1 B a K hS0)
    · have := fullCoverLevel_He hc hk hK.comp hHe
      omega
  · have hlev := l73_prod_level hc hk i2prod S hP
    exact l73_false_of_S_le_core hc C (l73_prod_S_le_core i2prod i2013 S C hP)
      (l73_prod_odd hc hB hess hd hP hlev)

end CFSG.LocalAnalysis.GLTheoremA

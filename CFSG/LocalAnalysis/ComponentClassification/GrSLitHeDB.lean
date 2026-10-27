module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDL
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm33
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZFacts

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeDB

variable {G : Type} [Group G] [Finite G]

theorem not_odd_card {C J : Subgroup G} (hJC : J ≤ C) (hJ : IsPComponent 2 (J.subgroupOf C)) :
    ¬ Odd (Nat.card J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hodd
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J C hJC).mp hJ
  have htop : pPrimeCore 2 ↥J = ⊤ := by
    refine eq_top_iff.mpr (le_sSup (s := {K : Subgroup ↥J | K.Normal ∧
      Nat.Coprime 2 (Nat.card K)}) ⟨inferInstance, ?_⟩)
    rw [card_top]
    exact Nat.coprime_two_left.mpr hodd
  have hnt := LocalCores.isQuasisimple_nontrivial hq
  have : Subsingleton (↥J ⧸ pPrimeCore 2 ↥J) := QuotientGroup.subsingleton_iff.mpr htop
  exact false_of_nontrivial_of_subsingleton (↥J ⧸ pPrimeCore 2 ↥J)

theorem eq_of_le {C J K : Subgroup G} (hJC : J ≤ C) (hJ : IsPComponent 2 (J.subgroupOf C))
    (hKC : K ≤ C) (hK : IsPComponent 2 (K.subgroupOf C)) (hJK : J ≤ K) : J = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have h := FooteLit.commutator_le_oddCoreIn_of_ne ⟨hJC, hJ⟩ ⟨hKC, hK⟩ hne
  have hperf : Group.IsPerfect ↥J := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hJ
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJC).toMonoidHom)
      (subgroupOfEquivOfLe hJC).surjective
  have hJp : ⁅J, J⁆ = J := isPerfect_iff.mp hperf
  have hJO : J ≤ FooteLit.oddCoreIn C := by
    rw [← hJp]
    exact (commutator_mono le_rfl hJK).trans h
  apply not_odd_card hJC hJ
  have h1 : Nat.card J ∣ Nat.card (FooteLit.oddCoreIn C) := card_dvd_of_le hJO
  have h2 : Odd (Nat.card (FooteLit.oddCoreIn C)) := by
    rw [FooteLit.oddCoreIn, card_map_of_injective C.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact h2.of_dvd_nat h1

theorem exists_eight_le
    {X : Type} [Group X] [Finite X] {a u : X} {L T : Subgroup X}
    (hLa : L ≤ centralizer ({a} : Set X))
    (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He) (huL : u ∈ L) (hu : u * u = 1)
    (hu1 : u ≠ 1) (hTL : T ≤ L)
    (hTau : T ≤ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X))
    (hTp : IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X)))) :
    ∃ B : Subgroup X, B ≤ T ∧ IsElemTwo B ∧ Nat.card B = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT1 : IsPComponent 2 (T.subgroupOf (L ⊓ centralizer ({u} : Set X))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hTL (hTau.trans inf_le_right))
      (inf_le_inf_right _ hLa) hTp
  set u' : ↥L := ⟨u, huL⟩ with hu'
  have hu'2 : u' * u' = 1 := Subtype.ext hu
  set T' : Subgroup ↥L := T.subgroupOf L with hT'
  have hcent : (L ⊓ centralizer ({u} : Set X)).subgroupOf L = centralizer ({u'} : Set ↥L) := by
    ext y
    rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h.2, fun h => ⟨y.2, congrArg Subtype.val h⟩⟩
  have hT'C : T' ≤ centralizer ({u'} : Set ↥L) := by
    rw [← hcent]
    intro y hy
    exact mem_subgroupOf.mpr (le_inf hTL (hTau.trans inf_le_right) hy)
  have hT'p : IsPComponent 2 (T'.subgroupOf (centralizer ({u'} : Set ↥L))) := by
    rw [← hcent, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (X := L) inf_le_left 2
      Nat.prime_two]
    exact hT1
  set Q := ↥L ⧸ pPrimeCore 2 ↥L with hQ
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  have hCmap : (centralizer ({u'} : Set ↥L)).map π = centralizer ({π u'} : Set Q) :=
    (GSThmB.OddQuot.centralizer_singleton_map_eq hu'2).symm
  set Tb := T'.map π with hTb
  have hTbC : Tb ≤ centralizer ({π u'} : Set Q) := hCmap ▸ map_mono hT'C
  have hTbp : IsPComponent 2 (Tb.subgroupOf (centralizer ({π u'} : Set Q))) := by
    have h := GSThmB.OddQuot.isPComponent_map π GSThmB.OddQuot.not_two_dvd_card_ker hT'C hT'p
    rwa [hCmap] at h
  let e' : ↥(⊤ : Subgroup Q) ≃* Blueprint.NativeSporadic.He := Subgroup.topEquiv.trans e
  set K := gsFixedLayer (⊤ : Subgroup Q) (π u') with hK
  have hKeq : K = (pLayer ↥(centralizer ({π u'} : Set Q)) 2).map
      (centralizer ({π u'} : Set Q)).subtype := by
    rw [hK, gsFixedLayer, top_inf_eq]
  have hTbK : Tb ≤ K := by
    rw [hKeq]
    have hle : Tb.subgroupOf (centralizer ({π u'} : Set Q)) ≤
        pLayer ↥(centralizer ({π u'} : Set Q)) 2 := le_sSup hTbp
    intro x hx
    exact ⟨⟨x, hTbC hx⟩, hle (show (⟨x, hTbC hx⟩ : ↥(centralizer ({π u'} : Set Q))) ∈
      Tb.subgroupOf _ from hx), rfl⟩
  have hπu : π u' ≠ 1 := by
    intro h
    have hmem : u' ∈ pPrimeCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h
    have h2 : orderOf (⟨u', hmem⟩ : pPrimeCore 2 ↥L) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [pow_two]; exact hu'2) (fun h => hu1 (congrArg Subtype.val h))
    have h3 := orderOf_dvd_natCard (⟨u', hmem⟩ : pPrimeCore 2 ↥L)
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
      (even_iff_two_dvd.mpr h3)
  have hA : HeldTwoA (⊤ : Subgroup Q) (π u') := by
    refine ⟨mem_top _, orderOf_eq_prime (by rw [pow_two, ← map_mul, hu'2, map_one]) hπu, ?_⟩
    intro hbot
    apply not_odd_card hTbC hTbp
    rw [show Tb = ⊥ from le_bot_iff.mp (hbot ▸ hTbK), card_bot]
    exact odd_one
  have hKp : IsPComponent 2 (K.subgroupOf (centralizer ({π u'} : Set Q))) := by
    have h := isPComponent_gsFixedLayer_of_held e' hA
    rwa [top_inf_eq] at h
  have hKC : K ≤ centralizer ({π u'} : Set Q) := (gsFixedLayer_le_inf _ _).trans inf_le_right
  have hTbK' : Tb = K := eq_of_le hTbC hTbp hKC hKp hTbK
  obtain ⟨hZ4, -, hZc⟩ := heldTwoAKFact Q ⊤ ⟨e'⟩ (π u') hA
  obtain ⟨w, hwK, hw, hwZ, -⟩ := heldTwoAPairFact_of_model HeGS.heldTwoAPairModel Q ⊤ ⟨e'⟩ (π u') hA
  set Z := (center ↥K).map K.subtype with hZdef
  have hZe : IsElemTwo Z := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact congrArg Subtype.val (mem_center_iff.mp hy' x')
    · obtain ⟨x', hx', rfl⟩ := hx
      show (x' : Q) * (x' : Q) = 1
      rcases hZc (x' : Q) (mem_top _) (fun k hk => congrArg Subtype.val
          (mem_center_iff.mp hx' ⟨k, hk⟩).symm) with h | ⟨h, -⟩
      · rw [h, one_mul]
      · have h3 := pow_orderOf_eq_one (x' : Q)
        rw [h.2.1, pow_two] at h3
        exact h3
  have hZcard : Nat.card Z = 4 := by
    rw [hZdef, card_map_of_injective K.subtype_injective]
    exact hZ4
  have hww : w * w = 1 := by
    have h3 := pow_orderOf_eq_one w
    rw [hw.2.1, pow_two] at h3
    exact h3
  have hwZc : ∀ z ∈ Z, z * w = w * z := by
    rintro _ ⟨z, hz, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨w, hwK⟩).symm
  set Bb := Z ⊔ zpowers w with hBb
  have hBbe : IsElemTwo Bb := hZe.sup (isElemTwo_zpowers hww) (fun x hx y hy => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x w from hwZc x hx) i).eq)
  have hBb8 : Nat.card Bb = 8 := by
    have hle : Nat.card Bb ≤ 8 := by
      have hwN : w ∈ normalizer (Z : Set Q) := by
        rw [mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          rw [← hwZc y hy, mul_inv_cancel_right]
          exact hy
        · intro hy
          have h1 := hwZc _ hy
          have h2 : y = w * y * w⁻¹ := by
            calc y = w⁻¹ * (w * y * w⁻¹) * w := by group
              _ = w⁻¹ * (w * (w * y * w⁻¹)) := by rw [mul_assoc, ← h1]
              _ = w * y * w⁻¹ := by group
          rw [h2]
          exact hy
      have h := card_zpowers_sup_le hww hwN
      have h' : Nat.card ↥(Z ⊔ zpowers w) ≤ 2 * Nat.card Z := by rw [sup_comm]; exact h
      rw [hZcard] at h'
      exact h'
    have hge : 8 ≤ Nat.card Bb := by
      have hZB : Z ≤ Bb := le_sup_left
      have hne : Z.subgroupOf Bb ≠ ⊤ := by
        intro h
        have hmem : (⟨w, mem_sup_right (mem_zpowers w)⟩ : Bb) ∈ Z.subgroupOf Bb := h ▸ mem_top _
        exact hwZ hmem
      have hidx : 2 ≤ (Z.subgroupOf Bb).index := by
        have h1 : (Z.subgroupOf Bb).index ≠ 1 := fun h => hne (index_eq_one.mp h)
        have h0 : (Z.subgroupOf Bb).index ≠ 0 := index_ne_zero_of_finite
        omega
      have hcard := card_mul_index (Z.subgroupOf Bb)
      rw [Nat.card_congr (subgroupOfEquivOfLe hZB).toEquiv, hZcard] at hcard
      omega
    omega
  have hBbT : Bb ≤ T'.map π := by
    rw [← hTb, hTbK']
    refine sup_le (map_subtype_le _) (zpowers_le.mpr hwK)
  obtain ⟨Z', hZ'T, -, hZ'e, hZ'card⟩ := HeDL.exists_lift_le hBbe hBbT
  refine ⟨Z'.map L.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hZ'T hz
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hZ'e.1 x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hZ'e.2 x hx)
  · rw [card_map_of_injective L.subtype_injective, hZ'card, hBb8]

end HeDB

end CFSG.ComponentClassification.GrSLit

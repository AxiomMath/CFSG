module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Core2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Iso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem quot_p_trivial {p : ℕ} (hp : p.Prime) {L : Subgroup G} {a : ↥L} (ha : a ^ p = 1)
    (h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥L) a = 1) : a = 1 := by
  by_contra hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf a = p := orderOf_eq_prime ha hne
  have hmem : a ∈ GLAPPrimeCore p ↥L := (QuotientGroup.eq_one_iff a).1 h1
  have hle : Subgroup.zpowers a ≤ GLAPPrimeCore p ↥L := Subgroup.zpowers_le.2 hmem
  have hdvd : Nat.card (Subgroup.zpowers a) ∣ Nat.card (GLAPPrimeCore p ↥L) :=
    Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, hord] at hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥L)) := CFSG.pPrimeCore_coprime_card
  exact ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop) hdvd

theorem isElemAbelian_quot_image {p : ℕ} (hp : p.Prime) {L B : Subgroup G}
    (hBel : IsElemAbelian p B) :
    IsElemAbelian p (((B ⊓ L).subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore p ↥L))) := by
  have hcomm : ∀ u ∈ ((B ⊓ L).subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore p ↥L)),
      ∀ v ∈ ((B ⊓ L).subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore p ↥L)), u * v = v * u := by
    intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hv
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact isElemAbelian_commute hBel (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ha)).1
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hb)).1
  refine ⟨⟨⟨fun u v => Subtype.ext (hcomm u.1 u.2 v.1 v.2)⟩⟩, fun u hu => ?_⟩
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
  rw [← map_pow]
  have h1 : a ^ p = 1 := Subtype.ext (by simpa using hBel.2 _ (Subgroup.mem_inf.1
    (Subgroup.mem_subgroupOf.1 ha)).1)
  rw [h1, map_one]

theorem card_quot_image {p : ℕ} (hp : p.Prime) {L B : Subgroup G} (hBel : IsElemAbelian p B) :
    Nat.card (((B ⊓ L).subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore p ↥L))) =
      Nat.card (B ⊓ L : Subgroup G) := by
  set A : Subgroup ↥L := (B ⊓ L).subgroupOf L with hA
  have hinj : Function.Injective ((QuotientGroup.mk' (GLAPPrimeCore p ↥L)).subgroupMap A) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥L) (a : ↥L) = 1 := congrArg Subtype.val ha
    have haB : ((a : ↥L) : G) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 a.2)).1
    have h3 : (a : ↥L) ^ p = 1 := Subtype.ext (by simpa using hBel.2 _ haB)
    exact Subtype.ext (by simpa using quot_p_trivial hp h3 h2)
  have e1 : ↥A ≃ ↥(A.map (QuotientGroup.mk' (GLAPPrimeCore p ↥L))) :=
    (MulEquiv.ofBijective ((QuotientGroup.mk' (GLAPPrimeCore p ↥L)).subgroupMap A)
      ⟨hinj, (QuotientGroup.mk' (GLAPPrimeCore p ↥L)).subgroupMap_surjective A⟩).toEquiv
  have e2 : ↥A ≃ ↥(B ⊓ L : Subgroup G) :=
    (Subgroup.subgroupOfEquivOfLe (inf_le_right : B ⊓ L ≤ L)).toEquiv
  exact (Nat.card_congr e1).symm.trans (Nat.card_congr e2)

theorem card_inf_of_direct {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {x : G}
    (hBel : IsElemAbelian p B) (hxB : x ∈ B) (hx1 : x ≠ 1) (hdir : IsDirectZpowersInf B x L)
    (hB : Nat.card B = p ^ 4) : Nat.card (B ⊓ L : Subgroup G) = p ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxord : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hBel.2 x hxB) hx1]
  have hnorm : (B ⊓ L : Subgroup G) ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro b hb
    have hbB : b ∈ B := (Subgroup.mem_inf.1 hb).1
    exact normalizer_of_commute fun a ha =>
      isElemAbelian_commute hBel hbB ((Subgroup.zpowers_le.2 hxB) ha)
  have h := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [← hdir.1, hdir.2, Subgroup.card_bot, mul_one, hxord, hB] at h
  have h' : p * Nat.card (B ⊓ L : Subgroup G) = p * p ^ 3 := by
    rw [← h]
    ring
  exact Nat.eq_of_mul_eq_mul_left hp.pos h'

noncomputable def pSimpleEquivQuot {p : ℕ} {L : Subgroup G} (hZ : Subgroup.center (PQuot p L) = ⊥) :
    PSimple p L ≃* PQuot p L :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem catalog_of_pSimpleIsLie {p : ℕ} {L : Subgroup G} {d : TauCeti.LieTypeIndex}
    (hZ : Subgroup.center (PQuot p L) = ⊥) (h : pSimpleIsLie p L d) :
    catalogIs (PQuot p L) (onLie fun d' => d' = d) := by
  obtain ⟨i, hi, ⟨φ⟩⟩ := h
  exact ⟨i, hi, ⟨(pSimpleEquivQuot hZ).symm.trans φ⟩⟩

theorem i81At_of_facts (hA3 : H81FactA3) (hTwA3 : H81FactTwA3) (hB3 : H81FactB3)
    (hTwD4 : H81FactTwD4) (hD4 : H81FactD4) (hDisj : H81FamilyDisjoint) (G : Type) [Group G] [Finite G]
    (p : ℕ) : I81At G p := by
  intro hp hp2 q hq hq2 hqp B x L hT h234
  obtain ⟨⟨hBmax, hxB, hx1, hcomp, hBL, hcm⟩, -⟩ := hT
  have hBel : IsElemAbelian p B := hBmax.1
  rcases h234 with h64 | h34
  ·
    obtain ⟨hcard4, hdir, hZ, Q, hQp, hfam⟩ := h64
    subst hQp
    have hcardBL : Nat.card (B ⊓ L : Subgroup G) = p ^ 3 := card_inf_of_direct hp hBel hxB hx1 hdir hcard4
    rcases hfam with ⟨hA, hdiv⟩ | ⟨hA, hdiv⟩
    · have hH := catalog_of_pSimpleIsLie (d := .A 3 Q) hZ hA
      have hch := hA3 p Q hp hp2 hq2 hdiv (PQuot p L) hH _ (isElemAbelian_quot_image hp hBel)
        ((card_quot_image hp hBel).trans hcardBL)
      obtain ⟨y, hy, hy1, J, E, h1, h2, h3, h4, h5, h6, h7, h8, JH, hJH, ⟨e⟩⟩ :=
        core_of_choice hp hBel hxB hx1 hcomp hBL hcm hZ (IsSL3Type p Q.p) hch
      refine ⟨y, hy, hy1, J, E, h1, h2, h3, h4, h5, h6, h7, h8, fun _ => isSL3Type_of_mulEquiv e hJH,
        fun h34 => ?_⟩
      exfalso
      rcases h34 with h34 | h34
      · obtain ⟨-, -, -, Q', -, hfamB, -⟩ := h34
        have hB' : catalogIs (PQuot p L) (onLie fun d => d = .B 3 Q') ∨
            catalogIs (PQuot p L) (onLie fun d => d = .twistedD 4 Q') := by
          rcases hfamB with h | h
          · exact Or.inl (catalog_of_pSimpleIsLie hZ h)
          · exact Or.inr (catalog_of_pSimpleIsLie hZ h)
        exact hDisj (PQuot p L) Q Q' ⟨Or.inl hH, by
          rcases hB' with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)⟩
      · obtain ⟨-, -, -, Q', -, hD, -⟩ := h34
        exact hDisj (PQuot p L) Q Q' ⟨Or.inl hH, Or.inr (Or.inr (catalog_of_pSimpleIsLie hZ hD))⟩
    · have hH := catalog_of_pSimpleIsLie (d := .twistedA 3 Q) hZ hA
      have hch := hTwA3 p Q hp hp2 hq2 hdiv (PQuot p L) hH _ (isElemAbelian_quot_image hp hBel)
        ((card_quot_image hp hBel).trans hcardBL)
      obtain ⟨y, hy, hy1, J, E, h1, h2, h3, h4, h5, h6, h7, h8, JH, hJH, ⟨e⟩⟩ :=
        core_of_choice hp hBel hxB hx1 hcomp hBL hcm hZ (IsSL3Type p Q.p) hch
      refine ⟨y, hy, hy1, J, E, h1, h2, h3, h4, h5, h6, h7, h8, fun _ => isSL3Type_of_mulEquiv e hJH,
        fun h34 => ?_⟩
      exfalso
      rcases h34 with h34 | h34
      · obtain ⟨-, -, -, Q', -, hfamB, -⟩ := h34
        have hB' : catalogIs (PQuot p L) (onLie fun d => d = .B 3 Q') ∨
            catalogIs (PQuot p L) (onLie fun d => d = .twistedD 4 Q') := by
          rcases hfamB with h | h
          · exact Or.inl (catalog_of_pSimpleIsLie hZ h)
          · exact Or.inr (catalog_of_pSimpleIsLie hZ h)
        exact hDisj (PQuot p L) Q Q' ⟨Or.inr hH, by
          rcases hB' with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)⟩
      · obtain ⟨-, -, -, Q', -, hD, -⟩ := h34
        exact hDisj (PQuot p L) Q Q' ⟨Or.inr hH, Or.inr (Or.inr (catalog_of_pSimpleIsLie hZ hD))⟩
  ·
    rcases h34 with h3 | h4
    · obtain ⟨hcard4, hdir, hZ, Q, hQp, hfam, hdiv⟩ := h3
      subst hQp
      have hcardBL : Nat.card (B ⊓ L : Subgroup G) = p ^ 3 :=
        card_inf_of_direct hp hBel hxB hx1 hdir hcard4
      have hPel := isElemAbelian_quot_image (G := G) hp (L := L) hBel
      have hPc := (card_quot_image hp (L := L) hBel).trans hcardBL
      rcases hfam with hA | hA
      · have hH := catalog_of_pSimpleIsLie (d := .B 3 Q) hZ hA
        have hch := hB3 p Q hp hp2 hq2 hdiv (PQuot p L) hH _ hPel hPc
        obtain ⟨y, hy, hy1, J, E, h1, h2, h3, h4, h5, h6, h7, h8, JH, hJH, ⟨e⟩⟩ :=
          core_of_choice hp hBel hxB hx1 hcomp hBL hcm hZ (IsOmegaType p Q.p) hch
        refine ⟨y, hy, hy1, J, E, h1, h2, h3, h4, h5, h6, h7, h8, fun h64 => ?_,
          fun _ => isOmegaType_of_mulEquiv e hJH⟩
        exfalso
        obtain ⟨-, -, -, Q', -, hfam'⟩ := h64
        have hA' : catalogIs (PQuot p L) (onLie fun d => d = .A 3 Q') ∨
            catalogIs (PQuot p L) (onLie fun d => d = .twistedA 3 Q') := by
          rcases hfam' with h | h
          · exact Or.inl (catalog_of_pSimpleIsLie hZ h.1)
          · exact Or.inr (catalog_of_pSimpleIsLie hZ h.1)
        exact hDisj (PQuot p L) Q' Q ⟨hA', Or.inl hH⟩
      · have hH := catalog_of_pSimpleIsLie (d := .twistedD 4 Q) hZ hA
        have hch := hTwD4 p Q hp hp2 hq2 hdiv (PQuot p L) hH _ hPel hPc
        obtain ⟨y, hy, hy1, J, E, h1, h2, h3, h4, h5, h6, h7, h8, JH, hJH, ⟨e⟩⟩ :=
          core_of_choice hp hBel hxB hx1 hcomp hBL hcm hZ (IsOmegaType p Q.p) hch
        refine ⟨y, hy, hy1, J, E, h1, h2, h3, h4, h5, h6, h7, h8, fun h64 => ?_,
          fun _ => isOmegaType_of_mulEquiv e hJH⟩
        exfalso
        obtain ⟨-, -, -, Q', -, hfam'⟩ := h64
        have hA' : catalogIs (PQuot p L) (onLie fun d => d = .A 3 Q') ∨
            catalogIs (PQuot p L) (onLie fun d => d = .twistedA 3 Q') := by
          rcases hfam' with h | h
          · exact Or.inl (catalog_of_pSimpleIsLie hZ h.1)
          · exact Or.inr (catalog_of_pSimpleIsLie hZ h.1)
        exact hDisj (PQuot p L) Q' Q ⟨hA', Or.inr (Or.inl hH)⟩
    · obtain ⟨-, hcardBL, hZ, Q, hQp, hA, hdiv⟩ := h4
      subst hQp
      have hPel := isElemAbelian_quot_image (G := G) hp (L := L) hBel
      have hPc := (card_quot_image hp (L := L) hBel).trans hcardBL
      have hH := catalog_of_pSimpleIsLie (d := .D 4 Q) hZ hA
      have hch := hD4 p Q hp hp2 hq2 hdiv (PQuot p L) hH _ hPel hPc
      obtain ⟨y, hy, hy1, J, E, h1, h2, h3, h4, h5, h6, h7, h8, JH, hJH, ⟨e⟩⟩ :=
        core_of_choice hp hBel hxB hx1 hcomp hBL hcm hZ (IsOmegaType p Q.p) hch
      refine ⟨y, hy, hy1, J, E, h1, h2, h3, h4, h5, h6, h7, h8, fun h64 => ?_,
        fun _ => isOmegaType_of_mulEquiv e hJH⟩
      exfalso
      obtain ⟨-, -, -, Q', -, hfam'⟩ := h64
      have hA' : catalogIs (PQuot p L) (onLie fun d => d = .A 3 Q') ∨
          catalogIs (PQuot p L) (onLie fun d => d = .twistedA 3 Q') := by
        rcases hfam' with h | h
        · exact Or.inl (catalog_of_pSimpleIsLie hZ h.1)
        · exact Or.inr (catalog_of_pSimpleIsLie hZ h.1)
      exact hDisj (PQuot p L) Q' Q ⟨hA', Or.inr (Or.inr hH)⟩

end CFSG.LocalAnalysis.GLTheoremA.H81

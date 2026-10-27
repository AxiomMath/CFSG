module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263I263

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

theorem t263_sections_of_kGroup {G : Type} [Group G] [Finite G] {X : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (N : Subgroup ↥X) [N.Normal] : t263KGroup (↥X ⧸ N) := hX.quotient N

section Core

variable {G : Type} [Group G] [Finite G]

theorem t263Amb_of_genLt {κ : T263AmbPred} {N : ℕ} (hF : T263GenLt κ N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 4 ≤ GLATwoLocalRank p G) {B L : Subgroup G} (hBmax : GLAIsBmax p B)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hq : CFSG.Open.IsQuasisimple (PQuot p L))
    (hc : IsChevSimple 2 (PSimple p L)) (hlt : Nat.card (PQuot p L) < N)
    (hT : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf p L)
    (hSec : ∀ (N' : Subgroup ↥(L ⊔ B)) [N'.Normal], κ (↥(L ⊔ B) ⧸ N')) :
    IsGStar p B L ∨ (p = 3 ∧ GLAMarking (PQuot 3 L) (fun lab _ _ _ _ _ => lab.n = 1)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hBel, hBcard, -, -, -⟩ :
      CFSG.Open.IsElemAbelian p B ∧ Nat.card ↥B = p ^ GLATwoLocalRank p G ∧
        ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) := hBmax
  set H : Subgroup G := L ⊔ B with hH
  have hLH : L ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  set K₀ : Subgroup ↥H := L.subgroupOf H with hK₀def
  haveI hK₀n : K₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN
  set N₀ : Subgroup ↥H := GLAPPrimeCoreOf p K₀ with hN₀def
  haveI hN₀n : N₀.Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf p K₀
    rw [Subgroup.normalizer_eq_top_iff.2 hK₀n, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  have hNp : ¬ p ∣ Nat.card N₀ := not_dvd_card_glaPPrimeCoreOf hp K₀
  have hNK : N₀ ≤ K₀ := Subgroup.map_subtype_le _
  set π : ↥H →* ↥H ⧸ N₀ := QuotientGroup.mk' N₀ with hπ
  have hker : ¬ p ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hNp
  have hkerπ : π.ker = N₀ := by
    rw [hπ, QuotientGroup.ker_mk']
  set S : Subgroup (↥H ⧸ N₀) := K₀.map π with hSdef
  have hSn : S.Normal := hK₀n.map π (QuotientGroup.mk'_surjective N₀)
  set Bh : Subgroup ↥H := B.subgroupOf H with hBhdef
  have hBhel : CFSG.Open.IsElemAbelian p Bh := isElemAbelian_subgroupOf hBel H
  have hBhp : IsPGroup p Bh := isPGroup_of_isElemAbelian hBhel
  have hBhcard : Nat.card Bh = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  set Bb : Subgroup (↥H ⧸ N₀) := Bh.map π with hBbdef
  have hBbel : CFSG.Open.IsElemAbelian p Bb := CFSG.Open.IsElemAbelian.map hBhel π
  have hBbcard : Nat.card Bb = Nat.card B := by
    rw [hBbdef, CFSG.LocalAnalysis.GLTheoremA.S267.card_map_of_isPGroup hp π hker hBhp, hBhcard]
  obtain ⟨T, hTL, hT2, hBT, hTnot⟩ := hT
  have hTH : T ≤ H := hTL.trans hLH
  set Th : Subgroup ↥H := T.subgroupOf H with hThdef
  have hThK : Th ≤ K₀ := Subgroup.subgroupOf_mono H hTL
  have hTh2 : IsPGroup 2 Th := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  set Tb : Subgroup (↥H ⧸ N₀) := Th.map π with hTbdef
  have hTb2 : IsPGroup 2 Tb := hTh2.map π
  have hTbS : Tb ≤ S := Subgroup.map_mono hThK
  have hTbne : Tb ≠ ⊥ := by
    intro h0
    apply hTnot
    have hle : Th ≤ N₀ := by
      have h1 : Th ≤ π.ker := (Subgroup.map_eq_bot_iff _).1 h0
      rw [hkerπ] at h1
      exact h1
    have hTeq : T = Th.map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hTH).symm
    rw [hTeq, ← map_subtype_glaPPrimeCoreOf_subgroupOf p hLH]
    exact Subgroup.map_mono hle
  have hBhN : Bh ≤ Subgroup.normalizer (Th : Set ↥H) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hb' := Subgroup.mem_normalizer_iff.1 (hBT (Subgroup.mem_subgroupOf.1 hb)) (h : G)
    simp only [hThdef, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hb'
  have hBbN : Bb ≤ Subgroup.normalizer (Tb : Set (↥H ⧸ N₀)) :=
    (Subgroup.map_mono hBhN).trans (Subgroup.le_normalizer_map π)
  have hKB : K₀ ⊔ Bh = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hHQ : H ≤ (K₀ ⊔ Bh).map H.subtype := by
      show L ⊔ B ≤ (K₀ ⊔ Bh).map H.subtype
      apply sup_le
      · exact (Subgroup.map_subgroupOf_eq_of_le hLH).symm.trans_le
          (Subgroup.map_mono le_sup_left)
      · exact (Subgroup.map_subgroupOf_eq_of_le hBH).symm.trans_le
          (Subgroup.map_mono le_sup_right)
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hHQ x.2)
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  have hSB : S ⊔ Bb = ⊤ := by
    rw [hSdef, hBbdef, ← Subgroup.map_sup, hKB]
    exact Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N₀)
  have hOp : GLAPPrimeCore p (↥H ⧸ N₀) = ⊥ :=
    glaPPrimeCore_quot_eq_bot hp K₀ Bh hBhp hKB
  obtain ⟨e₂⟩ := nonempty_pQuot_equiv_subgroupOf p hLH
  obtain ⟨e₃⟩ := nonempty_pQuot_equiv_map_self (p := p) (ψ := π) (K := K₀)
    (by rw [hπ, QuotientGroup.ker_mk', inf_eq_left.2 hNK])
  let e₁ : PQuot p L ≃* ↥S := e₂.symm.trans e₃
  have hSq : CFSG.Open.IsQuasisimple ↥S := hq.of_mulEquiv e₁.symm
  have hSp : GLAPPrimeCore p ↥S = ⊥ := by
    have h1 := CFSG.LocalAnalysis.GLTheoremA.S267.map_glaPPrimeCoreOf hp π hker K₀
    have h2 : GLAPPrimeCoreOf p S = ⊥ := by
      rw [← h1]
      exact (Subgroup.map_eq_bot_iff _).2 (by rw [hkerπ])
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 h2
  have e₆ : PSimple p L ≃* ↥S ⧸ Subgroup.center ↥S :=
    QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)
  have hSchev : IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) := by
    unfold IsChevSimple at hc ⊢
    rcases hc with h | h
    · exact Or.inl ((catalogIs_congr e₆).1 h)
    · exact Or.inr ((catalogIs_congr e₆).1 h)
  have hBbrank : Nat.card Bb = p ^ GLATwoLocalRank p G := hBbcard.trans hBcard
  have hrank : GLATwoLocalRank p (↥H ⧸ N₀) = GLATwoLocalRank p G := by
    apply le_antisymm
    · rw [glaTwoLocal_eq, glaTwoLocal_eq]
      exact twoLocalPrimeRank_quot_le hp hp2 H N₀ hNp
    · have hK : CFSG.Open.IsTwoLocal (Subgroup.normalizer (Tb : Set (↥H ⧸ N₀))) := ⟨Tb, hTbne, hTb2, rfl⟩
      have hk := le_pRank hBbN hBbel hBbrank
      have := le_twoLocal_of_pRank hK hk
      rw [glaTwoLocal_eq]
      exact this
  have hBmaxΩ : GLAIsBmax p Bb :=
    (⟨hBbel, by rw [hrank]; exact hBbrank, Tb, hTbne, hTb2, hBbN⟩ :
      CFSG.Open.IsElemAbelian p Bb ∧ Nat.card ↥Bb = p ^ GLATwoLocalRank p (↥H ⧸ N₀) ∧
        ∃ U : Subgroup (↥H ⧸ N₀), U ≠ ⊥ ∧ IsPGroup 2 U ∧ Bb ≤ Subgroup.normalizer (U : Set (↥H ⧸ N₀)))
  have h4Ω : 4 ≤ GLATwoLocalRank p (↥H ⧸ N₀) := by
    rw [hrank]
    exact hr
  have transport_a : ∀ E : Subgroup (↥H ⧸ N₀), E ≤ Bb → CFSG.Open.IsElemAbelian p E →
      Nat.card E = p ^ 3 → GLAPLayer p (S ⊓ Subgroup.centralizer (E : Set (↥H ⧸ N₀))) ≠ ⊥ →
      IsGStar p B L := by
    intro E hEB hEel hEcard hElay
    set Eh : Subgroup ↥H := Bh ⊓ E.comap π with hEhdef
    have hEhBh : Eh ≤ Bh := inf_le_left
    have hEhel : CFSG.Open.IsElemAbelian p Eh := isElemAbelian_mono hBhel hEhBh
    have hEhp : IsPGroup p Eh := isPGroup_of_isElemAbelian hEhel
    have hEhmap : Eh.map π = E := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hx.2
      · intro e he
        obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.1 (hEB he)
        refine Subgroup.mem_map.2 ⟨b, ⟨hb, ?_⟩, hbe⟩
        exact Subgroup.mem_comap.2 (hbe ▸ he)
    have hEhcard : Nat.card Eh = p ^ 3 := by
      rw [← hEcard, ← hEhmap, CFSG.LocalAnalysis.GLTheoremA.S267.card_map_of_isPGroup hp π hker hEhp]
    set EG : Subgroup G := Eh.map H.subtype with hEGdef
    have hEGB : EG ≤ B :=
      (Subgroup.map_mono hEhBh).trans (Subgroup.map_subgroupOf_eq_of_le hBH).le
    have hEGel : CFSG.Open.IsElemAbelian p EG := CFSG.Open.IsElemAbelian.map hEhel H.subtype
    have hEGcard : Nat.card EG = p ^ 3 := by
      rw [hEGdef, Subgroup.card_map_of_injective H.subtype_injective, hEhcard]
    have hEhN : Eh ≤ Subgroup.normalizer (K₀ : Set ↥H) := by
      rw [Subgroup.normalizer_eq_top_iff.2 hK₀n]
      exact le_top
    have hXmap : (K₀ ⊓ Subgroup.centralizer (Eh : Set ↥H)).map π =
        S ⊓ Subgroup.centralizer (E : Set (↥H ⧸ N₀)) := by
      rw [CFSG.LocalAnalysis.GLTheoremA.S267.map_inf_centralizer hp π hker hEhp hEhN, hEhmap]
    have hK₀L : K₀.map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
    have hXH : (K₀ ⊓ Subgroup.centralizer (Eh : Set ↥H)).map H.subtype =
        L ⊓ Subgroup.centralizer (EG : Set G) := by
      rw [CFSG.LocalAnalysis.GLTheoremA.S267.map_inf_centralizer_inj H.subtype H.subtype_injective K₀ Eh, hK₀L]
    have hkerH : ¬ p ∣ Nat.card H.subtype.ker := by
      rw [(MonoidHom.ker_eq_bot_iff H.subtype).2 H.subtype_injective, Subgroup.card_bot]
      exact hp.not_dvd_one
    have hXne : GLAPLayer p (K₀ ⊓ Subgroup.centralizer (Eh : Set ↥H)) ≠ ⊥ :=
      (CFSG.LocalAnalysis.GLTheoremA.S267.glaPLayer_map_ne_bot_iff hp π hker (K₀ ⊓ Subgroup.centralizer (Eh : Set ↥H))).1
        (by rw [hXmap]; exact hElay)
    have hLayerG : GLAPLayer p (L ⊓ Subgroup.centralizer (EG : Set G)) ≠ ⊥ := by
      rw [← hXH]
      exact (CFSG.LocalAnalysis.GLTheoremA.S267.glaPLayer_map_ne_bot_iff hp H.subtype hkerH _).2 hXne
    refine ⟨EG, hEGB, hEGel, hEGcard, ?_⟩
    rw [closureIn_eq_self_of_le hBN]
    exact hLayerG
  by_cases hC : p ^ 3 ≤ Nat.card ↥(Bb ⊓ Subgroup.centralizer (S : Set (↥H ⧸ N₀)))
  · left
    have hCb : CFSG.Open.IsElemAbelian p (Bb ⊓ Subgroup.centralizer (S : Set (↥H ⧸ N₀))) :=
      isElemAbelian_mono hBbel inf_le_left
    obtain ⟨j, hj⟩ := (isPGroup_of_isElemAbelian hCb).exists_card_eq
    have hdvd : p ^ 3 ∣ Nat.card ↥(Bb ⊓ Subgroup.centralizer (S : Set (↥H ⧸ N₀))) := by
      rw [hj]
      apply pow_dvd_pow
      have h3 : p ^ 3 ≤ p ^ j := hj ▸ hC
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h3
    obtain ⟨K3, hK3⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
    have hEB : K3.map (Bb ⊓ Subgroup.centralizer (S : Set (↥H ⧸ N₀))).subtype ≤ Bb :=
      (Subgroup.map_subtype_le K3).trans inf_le_left
    have hEC : K3.map (Bb ⊓ Subgroup.centralizer (S : Set (↥H ⧸ N₀))).subtype ≤
        Subgroup.centralizer (S : Set (↥H ⧸ N₀)) :=
      (Subgroup.map_subtype_le K3).trans inf_le_right
    have hEel : CFSG.Open.IsElemAbelian p
        (K3.map (Bb ⊓ Subgroup.centralizer (S : Set (↥H ⧸ N₀))).subtype) :=
      isElemAbelian_mono hCb (Subgroup.map_subtype_le K3)
    have hEcard : Nat.card (K3.map (Bb ⊓ Subgroup.centralizer (S : Set (↥H ⧸ N₀))).subtype) = p ^ 3 := by
      rw [Subgroup.card_map_of_injective (Bb ⊓ Subgroup.centralizer (S : Set (↥H ⧸ N₀))).subtype_injective, hK3]
    exact transport_a _ hEB hEel hEcard (layer_centralizes_ne_bot hp hSq hSp hEC)
  · have hC' : Nat.card ↥(Bb ⊓ Subgroup.centralizer (S : Set (↥H ⧸ N₀))) < p ^ 3 := not_le.1 hC
    have hltS : Nat.card ↥S < N := by
      rw [← Nat.card_congr e₁.toEquiv]
      exact hlt
    rcases hF p hp hp2 (↥H ⧸ N₀) (hSec N₀) S Bb hSn hSq hSp hSchev hltS hSB hOp hBmaxΩ h4Ω
        ⟨Tb, hTbne, hTb2, hTbS, hBbN⟩ hC' with ⟨E, hEB, hEel, hEcard, hElay⟩ | ⟨h3, hmk⟩
    · exact Or.inl (transport_a E hEB hEel hEcard hElay)
    · right
      subst h3
      refine ⟨rfl, CFSG.LocalAnalysis.GLTheoremA.Y10F.glaMarking_congr e₁ ?_ hmk⟩
      intro lab R _ I F θ h
      exact h


end Core

end CFSG.LocalAnalysis.GLTheoremA.T263

end

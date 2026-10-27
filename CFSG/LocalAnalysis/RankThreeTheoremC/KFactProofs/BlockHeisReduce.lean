module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisCoreDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsGlue
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedNext3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenFiveDefs
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofCover
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocksAux
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrSmall
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrStableAlternating

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.AGLEmbedding CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {Y : Type} [Group Y]

@[expose] noncomputable def conjOnL (L : Subgroup Y) (E : Subgroup Y)
    (hEN : E ≤ Subgroup.normalizer (L : Set Y)) : E →* MulAut ↥L :=
  MonoidHom.mk' (fun e => heisConjAut L (e : Y) (fun s => by
      have := Subgroup.mem_normalizer_iff.1 (hEN e.2) s
      exact this)) (by
    intro a b
    ext x
    simp only [MulAut.mul_apply, heisConjAut_apply, Submonoid.coe_mul, Subgroup.coe_toSubmonoid,
      mul_inv_rev]
    simp [mul_assoc])

theorem conjOnL_apply (L : Subgroup Y) (E : Subgroup Y)
    (hEN : E ≤ Subgroup.normalizer (L : Set Y))
    (e : E) (x : L) : (conjOnL L E hEN e x : Y) = (e : Y) * x * (e : Y)⁻¹ := rfl

theorem conjOnL_injective (L : Subgroup Y) (E : Subgroup Y)
    (hEN : E ≤ Subgroup.normalizer (L : Set Y))
    (hEC : E ⊓ Subgroup.centralizer (L : Set Y) = ⊥) : Function.Injective (conjOnL L E hEN) := by
  rw [injective_iff_map_eq_one]
  intro e he
  have hc : (e : Y) ∈ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := congrArg (fun f : MulAut ↥L => (f ⟨x, hx⟩ : Y)) he
    simp only [conjOnL_apply] at this
    have h2 : (e : Y) * x * (e : Y)⁻¹ = x := by simpa using this
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  have h1 : (e : Y) ∈ E ⊓ Subgroup.centralizer (L : Set Y) := ⟨e.2, hc⟩
  rw [hEC] at h1
  exact Subtype.ext (Subgroup.mem_bot.1 h1)

theorem false_of_noHeisAut {p : ℕ} (L : Subgroup Y) [Group.IsPerfect ↥L] (E : Subgroup Y)
    (hEN : E ≤ Subgroup.normalizer (L : Set Y))
    (hEC : E ⊓ Subgroup.centralizer (L : Set Y) = ⊥) (hcard : Nat.card E = p ^ 3)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hnab : ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a)
    (h : NoHeisAut p (↥L ⧸ Subgroup.center ↥L)) : False := by
  let ψ : E →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
    (CFSG.RankThree.mulAutQuotientHom (Subgroup.center ↥L)).comp (conjOnL L E hEN)
  have hψ : Function.Injective ψ :=
    (CFSG.RankThree.PartTwo.Sec10.Sec10XProof.mulAutQuotientHom_center_injective).comp
      (conjOnL_injective L E hEN hEC)
  have hcardR : Nat.card ψ.range = p ^ 3 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  have hexpR : ∀ x ∈ ψ.range, x ^ p = 1 := by
    rintro _ ⟨e, rfl⟩
    rw [← map_pow]
    have : e ^ p = 1 := Subtype.ext (hexp e e.2)
    rw [this, map_one]
  have hcomm := h ψ.range hcardR hexpR
  obtain ⟨a, ha, b, hb, hne⟩ := hnab
  apply hne
  have h1 := mul_comm' (⟨ψ ⟨a, ha⟩, ⟨_, rfl⟩⟩ : ψ.range) (⟨ψ ⟨b, hb⟩, ⟨_, rfl⟩⟩ : ψ.range)
  have h2 : ψ (⟨a, ha⟩ * ⟨b, hb⟩) = ψ (⟨b, hb⟩ * ⟨a, ha⟩) := by
    rw [map_mul, map_mul]
    exact congrArg Subtype.val h1
  exact congrArg Subtype.val (hψ h2)

theorem oddRankLeThree_of_pRank {Y : Type} [Group Y] [Finite Y] (H : Subgroup Y)
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q H ≤ 3) : OddRankLeThree ↥H := by
  intro q hq hq2 A hA hAq
  haveI : Fact q.Prime := ⟨hq⟩
  have hpg : IsPGroup q A := fun x => ⟨1, Subtype.ext (by simpa using hAq x x.2)⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  set B : Subgroup Y := A.map H.subtype with hB
  have hBcard : Nat.card B = q ^ k := by
    rw [hB, Subgroup.card_map_of_injective H.subtype_injective, hk]
  have hBle : B ≤ H := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hBel : IsElemAbelian q B := by
    refine ⟨?_, ?_⟩
    · exact hB ▸ Subgroup.map_isMulCommutative A H.subtype
    · rintro _ ⟨a, ha, rfl⟩
      simpa using congrArg H.subtype (hAq a ha)
  have hbdd : BddAbove {k | ∃ E : Subgroup Y, E ≤ H ∧ IsElemAbelian q E ∧ Nat.card E = q ^ k} := by
    refine ⟨Nat.card Y, ?_⟩
    rintro k ⟨E, -, -, hE⟩
    have h1 : q ^ k ≤ Nat.card Y :=
      hE ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card E)
    have h2 : k < q ^ k := Nat.lt_pow_self hq.one_lt
    omega
  have hkle : k ≤ Open.pRank q H := le_csSup hbdd ⟨B, hBle, hBel, hBcard⟩
  rw [hk]
  exact Nat.pow_le_pow_right hq.pos (hkle.trans (h q hq hq2))


section K6

variable {Y : Type} [Group Y]

theorem heis_odd_card_center_of_eq_bot {L : Type} [Group L] (h : Subgroup.center L = ⊥) :
    Odd (Nat.card (Subgroup.center L)) := by
  rw [h]
  simp

theorem heis_dispatch
    (hAlt : HeisCoreAlt) (hSmall : HeisCoreSmall) (hA : HeisCoreOn IdxA)
    (h2A : HeisCoreOn IdxTwistedA) (hB : HeisCoreOn IdxB) (hD : HeisCoreOn IdxD)
    (h2D : HeisCoreOn IdxTwistedD) (hG2 : HeisCoreOn IdxG2)
    {G : Type} [Group G] [Finite G] {M S L : Subgroup G} (hyps : BlockL28Hyps M S L)
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hEN : E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hEC : E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥)
    (hcard : Nat.card E = p ^ 3) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hnab : ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a)
    (hexc : ∀ (_ : CompParab (barM M L) (blockPL M S L)) (d : TauCeti.ValidLieTypeIndex)
      (_ : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* (TauCeti.CFSGIndex.lie d).Group),
      (p = 5 ∧ Subgroup.center ↥(barM M L) = ⊥ ∧
        ∃ q : TauCeti.PrimePower, d.1 = .twistedA 4 q ∧ q.card = 4) → False) : False := by
  have hcomp : CFSG.Open.IsQuasisimple ↥(barM M L) := hyps.2.2.1.component.2.2
  haveI : Group.IsPerfect ↥(barM M L) := ⟨hcomp.1⟩
  haveI : IsSimpleGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hcomp.2
  have hrk : OddRankLeThree ↥(barM M L) := oddRankLeThree_of_pRank _ hrank
  have hnabS : ∃ a b : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L), a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hcomp
  have hnabL : ∃ a b : ↥(barM M L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabS
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L)) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L)) b
    exact ⟨a', b', fun h' => hab (by rw [← map_mul, ← map_mul, h'])⟩
  have contra : NoHeisAut p (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) → False :=
    false_of_noHeisAut (barM M L) E hEN hEC hcard hexp hnab
  have alt1 : ∀ k : ℕ, (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin k)) →
      False := by
    intro k φ
    have hk5 : 5 ≤ k :=
      CFSG.ComponentClassification.UnbalancedCorr.five_le_of_mulEquiv_alternatingGroup hnabS φ
    exact contra (hAlt _ inferInstance hrk k hk5 φ p hp hp5)
  have alt2 : ∀ k : ℕ, (↥(barM M L) ≃* alternatingGroup (Fin k)) → False := by
    intro k φ
    have hZ := center_eq_bot_of_mulEquiv_alternating hnabL φ
    exact alt1 k (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans φ)
  have lie : ∀ (P : TauCeti.LieTypeIndex → Prop), HeisCoreOn P →
      (∀ q : TauCeti.PrimePower, ¬ P (.twistedA 4 q)) →
      Odd (Nat.card (Subgroup.center ↥(barM M L))) → ∀ (d : TauCeti.ValidLieTypeIndex), P d.1 →
      (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* (TauCeti.CFSGIndex.lie d).Group) → False := by
    intro P hcore hP' hodd d hd e
    rcases hcore _ inferInstance hodd hrk inferInstance d hd e p hp hp5 with h | ⟨-, -, q, hdq, -⟩
    · exact contra h
    · exact hP' q (hdq ▸ hd)
  rcases hyps.2.2.2.1 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact hyps.2.2.2.2.1 h1
  ·
    have hCP := compParab_of_blockHyps hyps h2
    have hodd := hCP.odd
    rcases isClassicalTwoOrG2_family_cases hCP.type with ⟨d, hd, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩ |
      ⟨d, hd, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩ | hS
    · exact lie IdxA hA (fun q h => h) hodd d hd e
    · rcases h2A _ inferInstance hodd hrk inferInstance d hd e p hp hp5 with h | hx
      · exact contra h
      · exact hexc hCP d e hx
    · exact lie IdxB hB (fun q h => h) hodd d hd e
    · exact lie IdxD hD (fun q h => h) hodd d hd e
    · exact lie IdxTwistedD h2D (fun q h => h) hodd d hd e
    · exact lie IdxG2 hG2 (fun q h => h) hodd d hd e
    · rcases hS with ⟨k, -, ⟨φ⟩⟩ | ⟨d, hd, ⟨e⟩⟩
      · exact alt1 k φ
      · exact contra (hSmall _ inferInstance d hd e p hp hp5)
  ·
    obtain ⟨-, hO, -⟩ := h3
    have hZ : Subgroup.center ↥(barM M L) = ⊥ :=
      center_eq_bot_of_isOrthogonalTwo inferInstance hnabL hO
    have hodd : Odd (Nat.card (Subgroup.center ↥(barM M L))) := heis_odd_card_center_of_eq_bot hZ
    rcases hO with ⟨d, ⟨m, q, hq, hd⟩, ⟨φ⟩⟩ | ⟨k, -, ⟨φ⟩⟩
    · have hq2 : q.p = 2 := by
        have h2 : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
        exact ((Nat.Prime.pow_eq_iff Nat.prime_two).1 h2).1
      have e := ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans φ
      rcases hd with hd | hd | ⟨-, hd⟩
      · exact lie IdxD hD (fun q h => h) hodd d (by rw [hd]; exact hq2) e
      · exact lie IdxTwistedD h2D (fun q h => h) hodd d (by rw [hd]; exact hq2) e
      · rcases h2A _ inferInstance hodd hrk inferInstance d (by rw [hd]; exact hq2) e p hp hp5 with
          h | ⟨-, -, q', hdq, -⟩
        · exact contra h
        · rw [hd] at hdq
          cases hdq
    · exact alt2 k φ
  · obtain ⟨-, -, ⟨φ⟩, -⟩ := h4
    exact alt1 6 φ
  · obtain ⟨-, ⟨φ⟩, -⟩ := h5
    exact alt2 7 φ
  · obtain ⟨-, n, ⟨φ⟩, -⟩ := h6
    exact alt1 (2 * n) φ
  · obtain ⟨-, n, ⟨φ⟩, -⟩ := h7
    exact alt2 (4 * n) φ
  · obtain ⟨-, N, r, -, -, -, -, -, ⟨φ⟩, -⟩ := h8
    exact alt2 N φ

theorem kFactBlockHeisenbergAut_of_cores
    (hAlt : HeisCoreAlt) (hSmall : HeisCoreSmall) (hA : HeisCoreOn IdxA)
    (h2A : HeisCoreOn IdxTwistedA) (hB : HeisCoreOn IdxB) (hD : HeisCoreOn IdxD)
    (h2D : HeisCoreOn IdxTwistedD) (hG2 : HeisCoreOn IdxG2) (hP : PSU54ParabolicFive) :
    KFactBlockHeisenbergAut := by
  intro G _ _ M S L hyps hQS hrank p hp hp5 _ hidx E hEN hEC hcard hexp hnab
  refine heis_dispatch hAlt hSmall hA h2A hB hD h2D hG2 hyps hrank hp hp5 hEN hEC hcard hexp hnab ?_
  rintro hCP d e ⟨rfl, hZ, q, hdq, hq4⟩
  exact hidx (hP _ (barM M L) (blockPL M S L) hCP hZ d q hdq hq4 e).1

end K6

section K7

variable {Y : Type} [Group Y]

theorem heis_centralizer_conj_mem {L : Subgroup Y} {n c : Y}
    (hn : n ∈ Subgroup.normalizer (L : Set Y)) (hc : c ∈ Subgroup.centralizer (L : Set Y)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : n⁻¹ * x * n ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) x).1 hx
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hc _ hx'
  calc x * (n * c * n⁻¹) = n * ((n⁻¹ * x * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
    _ = n * c * n⁻¹ * x := by group

theorem heis_inner_exists {L R : Subgroup Y} [Group.IsPerfect ↥L]
    (hRN : R ≤ Subgroup.normalizer (L : Set Y)) (r : R)
    (h : (CFSG.RankThree.mulAutQuotientHom (Subgroup.center ↥L)).comp (conjOnL L R hRN) r ∈
      inner (↥L ⧸ Subgroup.center ↥L)) :
    ∃ v ∈ L, (r : Y) * v⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : (CFSG.RankThree.mulAutQuotientHom (Subgroup.center ↥L)) (MulAut.conj v) =
      MulAut.conj (v : ↥L ⧸ Subgroup.center ↥L) := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H y => rfl
  have h2 : conjOnL L R hRN r = MulAut.conj v :=
    CFSG.RankThree.PartTwo.Sec10.Sec10XProof.mulAutQuotientHom_center_injective
      (by rw [h1]; exact hx.symm)
  refine ⟨(v : Y), v.2, ?_⟩
  have h3 : ∀ y ∈ L, (r : Y) * y * (r : Y)⁻¹ = (v : Y) * y * (v : Y)⁻¹ := by
    intro y hy
    have := congrArg (fun f : MulAut ↥L => (f ⟨y, hy⟩ : Y)) h2
    simpa [conjOnL_apply] using this
  have hrN : (r : Y) ∈ Subgroup.normalizer (L : Set Y) := hRN r.2
  have hvN : (v : Y) ∈ Subgroup.normalizer (L : Set Y) := Subgroup.le_normalizer v.2
  have h4 : (v : Y)⁻¹ * (r : Y) ∈ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h6 : (r : Y) * y = (v : Y) * y * (v : Y)⁻¹ * (r : Y) := by
      have := h3 y hy
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    calc y * ((v : Y)⁻¹ * (r : Y)) = (v : Y)⁻¹ * ((v : Y) * y * (v : Y)⁻¹ * (r : Y)) := by group
      _ = (v : Y)⁻¹ * ((r : Y) * y) := by rw [h6]
      _ = (v : Y)⁻¹ * (r : Y) * y := by group
  have h5 := heis_centralizer_conj_mem hvN h4
  simpa [mul_assoc] using h5

theorem heis_five_cube_dvd_of_inner {L R P : Subgroup Y} [Finite Y] [Group.IsPerfect ↥L]
    (hRN : R ≤ Subgroup.normalizer (L : Set Y))
    (hRC : R ⊓ Subgroup.centralizer (L : Set Y) = ⊥)
    (hcardR : Nat.card R = 5 ^ 4) (hLZ : Subgroup.center ↥L = ⊥)
    (hOut : Nat.card (Outer (↥L ⧸ Subgroup.center ↥L)) = 20)
    (hinner : ∀ v ∈ L, (∃ r ∈ R, r * v⁻¹ ∈ Subgroup.centralizer (L : Set Y)) → v ∈ P) :
    5 ^ 3 ∣ Nat.card P := by
  set X := ↥L ⧸ Subgroup.center ↥L
  let ψ₁ : R →* MulAut X :=
    (CFSG.RankThree.mulAutQuotientHom (Subgroup.center ↥L)).comp (conjOnL L R hRN)
  let ψ₂ : R →* Outer X := (QuotientGroup.mk' (inner X)).comp ψ₁
  set K := ψ₂.ker with hK
  have h1 : Nat.card R = Nat.card ψ₂.range * Nat.card K := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [this, hK]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ₂).toEquiv
  have h2 : Nat.card ψ₂.range ∣ 5 := by
    have ha : Nat.card ψ₂.range ∣ 20 := hOut ▸ Subgroup.card_subgroup_dvd_card _
    have hb : Nat.card ψ₂.range ∣ 5 ^ 4 := hcardR ▸ ⟨_, h1⟩
    have hg : Nat.gcd 20 (5 ^ 4) = 5 := by norm_num
    exact hg ▸ Nat.dvd_gcd ha hb
  have h5 : 5 ^ 3 ≤ Nat.card K := by
    have h3 : Nat.card ψ₂.range ≤ 5 := Nat.le_of_dvd (by norm_num) h2
    have hpos : 0 < Nat.card K := Nat.card_pos
    have : 5 ^ 4 ≤ 5 * Nat.card K := by
      calc 5 ^ 4 = Nat.card R := hcardR.symm
        _ = Nat.card ψ₂.range * Nat.card K := h1
        _ ≤ 5 * Nat.card K := Nat.mul_le_mul_right _ h3
    omega
  have hex : ∀ k : K, ∃ v : Y, v ∈ L ∧
      ((k : R) : Y) * v⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
    intro k
    have hk : ψ₂ k = 1 := k.2
    have hin : ψ₁ k ∈ inner X := by
      have h := hk
      rwa [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨v, hv, hvC⟩ := heis_inner_exists hRN (k : R) hin
    exact ⟨v, hv, hvC⟩
  choose f hfL hfC using hex
  have huniq : ∀ (r v w : Y), v ∈ L → w ∈ L → r * v⁻¹ ∈ Subgroup.centralizer (L : Set Y) →
      r * w⁻¹ ∈ Subgroup.centralizer (L : Set Y) → v = w := by
    intro r v w hv hw hvc hwc
    have h1 : w * v⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
      have := (Subgroup.centralizer (L : Set Y)).mul_mem
        ((Subgroup.centralizer (L : Set Y)).inv_mem hwc) hvc
      simpa [mul_assoc] using this
    have h2 : w * v⁻¹ ∈ L := L.mul_mem hw (L.inv_mem hv)
    have h3 : (⟨w * v⁻¹, h2⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h1 g g.2)
    rw [hLZ, Subgroup.mem_bot] at h3
    have h4 : w * v⁻¹ = 1 := congrArg Subtype.val h3
    exact (mul_inv_eq_one.1 h4).symm
  let φ : K →* Y := MonoidHom.mk' f (by
    intro a b
    have hra : ((a : R) : Y) ∈ Subgroup.normalizer (L : Set Y) := hRN (a : R).2
    refine huniq (((a * b : K) : R) : Y) _ _ (hfL _) (L.mul_mem (hfL a) (hfL b)) (hfC _) ?_
    have h3 : (((a * b : K) : R) : Y) * (f a * f b)⁻¹ =
        ((a : R) : Y) * (((b : R) : Y) * (f b)⁻¹) * ((a : R) : Y)⁻¹ *
          (((a : R) : Y) * (f a)⁻¹) := by
      change ((a : R) : Y) * ((b : R) : Y) * (f a * f b)⁻¹ = _
      group
    rw [h3]
    exact (Subgroup.centralizer (L : Set Y)).mul_mem
      (heis_centralizer_conj_mem hra (hfC b)) (hfC a))
  have hφ : ∀ k, φ k = f k := fun k => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : f a = 1 := ha
    have h2 : ((a : R) : Y) ∈ R ⊓ Subgroup.centralizer (L : Set Y) := by
      refine ⟨(a : R).2, ?_⟩
      have := hfC a
      rwa [h1, inv_one, mul_one] at this
    rw [hRC] at h2
    exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.1 h2))
  have hWcard : Nat.card φ.range = Nat.card K :=
    (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have hWP : φ.range ≤ P := by
    rintro _ ⟨k, rfl⟩
    exact hinner (f k) (hfL k) ⟨(k : R), (k : R).2, hfC k⟩
  have hKdvd : Nat.card K ∣ 5 ^ 4 := hcardR ▸ Subgroup.card_subgroup_dvd_card K
  obtain ⟨i, hi, hKi⟩ := (Nat.dvd_prime_pow (by norm_num : (5 : ℕ).Prime)).1 hKdvd
  have h3i : 3 ≤ i := by
    by_contra hlt
    have : 5 ^ i ≤ 5 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 5 ^ 3 ≤ 5 ^ 2 := h5.trans (hKi ▸ this)
    omega
  have hdvdW : 5 ^ 3 ∣ Nat.card φ.range := by
    rw [hWcard, hKi]
    exact pow_dvd_pow 5 h3i
  exact hdvdW.trans (Subgroup.card_dvd_of_le hWP)

theorem heis_primePower_card_four {q : TauCeti.PrimePower} (h : q.card = 4) :
    q.p = 2 ∧ q.exponent = 2 := by
  have h4 : q.p ^ q.exponent = 4 := by rw [← TauCeti.PrimePower.card_def]; exact h
  have hd : q.p ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4]
    exact dvd_pow_self _ (Nat.pos_iff_ne_zero.1 q.exponent_pos)
  have hp2 : q.p = 2 :=
    (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hd)
  refine ⟨hp2, ?_⟩
  rw [hp2] at h4
  exact Nat.pow_right_injective (le_refl 2) (by simpa using h4)

theorem heis_card_outer_psu_five_four {X : Type} [Group X] (q : TauCeti.PrimePower)
    (hq4 : q.card = 4) (hv : (TauCeti.LieTypeIndex.twistedA 4 q).Valid)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 4 q, hv⟩).Group) :
    Nat.card (Outer X) = 20 := by
  obtain ⟨hp2, hf2⟩ := heis_primePower_card_four hq4
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 q hv e
  rw [hp2, hf2] at h
  obtain ⟨K, _, hU3, hq, hn3, ⟨e'⟩⟩ := CFSG.AGLEmbedding.ParabAutIrr.exists_equiv_primeFormP_gen h
  obtain ⟨⟨eP⟩, -, -, hOutT, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order
      hU3 hn3 hq
  obtain ⟨⟨e'', -⟩, -⟩ := CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism e'
  rw [Nat.card_congr e''.toEquiv, hOutT]
  norm_num

theorem kFactBlockHeisenbergInner_of_cores
    (hAlt : HeisCoreAlt) (hSmall : HeisCoreSmall) (hA : HeisCoreOn IdxA)
    (h2A : HeisCoreOn IdxTwistedA) (hB : HeisCoreOn IdxB) (hD : HeisCoreOn IdxD)
    (h2D : HeisCoreOn IdxTwistedD) (hG2 : HeisCoreOn IdxG2) (hP : PSU54ParabolicFive) :
    KFactBlockHeisenbergInner := by
  intro G _ _ M S L hyps hQS hrank p hp hp5 R₁ hR₁N hR₁C hcard hE hinner
  obtain ⟨E, hER, hEcard, hEexp, hnab⟩ := hE
  have hEN : E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hER.trans hR₁N
  have hEC : E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf_right _ hER) hR₁C.le)
  refine heis_dispatch hAlt hSmall hA h2A hB hD h2D hG2 hyps hrank hp hp5 hEN hEC hEcard hEexp
    hnab ?_
  rintro hCP ⟨idx, hv⟩ e ⟨rfl, hZ, q, hdq, hq4⟩
  dsimp only at hdq
  subst hdq
  haveI : Group.IsPerfect ↥(barM M L) := ⟨hyps.2.2.1.component.2.2.1⟩
  have hout := heis_card_outer_psu_five_four q hq4 hv e
  have h5 := heis_five_cube_dvd_of_inner (L := barM M L) (R := R₁) (P := blockPL M S L) hR₁N hR₁C
    hcard hZ hout hinner
  exact (hP _ (barM M L) (blockPL M S L) hCP hZ ⟨_, hv⟩ q rfl hq4 e).2 h5

end K7

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

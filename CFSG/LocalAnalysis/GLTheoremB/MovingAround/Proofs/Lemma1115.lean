module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1114
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Finals

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped MatrixGroups

namespace Lemma1115

variable {G : Type} [Group G]

@[expose] noncomputable def jLayer (a : G) (H : Subgroup G) : Subgroup G :=
  ⨆ g ∈ GLAPLayer 3 H, GLBConj g (GLAPLayer 3 (H ⊓ Cg a))

@[expose] def Input1115Gamma : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) (H : Subgroup G), InHFamily A K a H →
    ∀ B1 : Subgroup G, IsEkIn 3 4 M B1 → B1 ≤ H →
      Covers 3 H (GLBCore 3 2 B1 ⊓ H) (jLayer a H)

@[expose] def Input1115Chain : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) (H : Subgroup G), InHFamily A K a H →
      Covers 3 H M (jLayer a H) → K ≤ M

@[expose] def Input1115TNorm : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) (H : Subgroup G), InHFamily A K a H →
    ∀ T : Subgroup G, IsMaxInvTwoSub H A T → T ≤ GLAPPrimeCoreOf 3 M →
      T ≤ Subgroup.normalizer (jLayer a H : Set G)

@[expose] def Input1115PushUp : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) (H : Subgroup G), InHFamily A K a H →
    ∀ T : Subgroup G, IsMaxInvTwoSub H A T → T ≤ Subgroup.normalizer (jLayer a H : Set G) →
      ∃ T0 : Subgroup G, T0 ≠ ⊥ ∧ IsCharIn T0 T ∧
        Covers 3 H (Subgroup.normalizer (T0 : Set G) ⊓ H) (jLayer a H)

theorem mem_normalizer_of_isCharIn {T T0 : Subgroup G} (hchar : IsCharIn T0 T) {a : G}
    (ha : a ∈ Subgroup.normalizer (T : Set G)) : a ∈ Subgroup.normalizer (T0 : Set G) := by
  have key : ∀ b : G, b ∈ Subgroup.normalizer (T : Set G) → ∀ x ∈ T0, b * x * b⁻¹ ∈ T0 := by
    intro b hb x hx
    let ψ : ↥T ≃* ↥T :=
      { toFun := fun y => ⟨b * y * b⁻¹, (Subgroup.mem_normalizer_iff.1 hb y).1 y.2⟩
        invFun := fun y => ⟨b⁻¹ * y * b⁻¹⁻¹,
          (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb) y).1 y.2⟩
        left_inv := fun y => Subtype.ext (by simp [mul_assoc])
        right_inv := fun y => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun y z => Subtype.ext (by simp [mul_assoc]) }
    exact hchar.2 ψ ⟨x, hchar.1 hx⟩ hx
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => key a ha h hh, fun hh => ?_⟩
  have := key a⁻¹ (Subgroup.inv_mem _ ha) _ hh
  simpa [mul_assoc] using this

theorem exists_sylow_in_inter [Finite G] {M H : Subgroup G}
    (hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 M)))
    (hcov : barX 3 M ⊤ ≤ barX 3 M H) :
    ∃ R : Subgroup G, IsSylowIn 3 M R ∧ R ≤ H := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOM : GLAPPrimeCoreOf 3 M ≤ M := Lemma1114.glaPPrimeCoreOf_le_self' M
  have hMh : M ⊓ H ≤ M := inf_le_left
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥(M ⊓ H)) := inferInstance
  set R : Subgroup G := P.toSubgroup.map (M ⊓ H).subtype with hRdef
  have hRMh : R ≤ M ⊓ H := Subgroup.map_subtype_le _
  have hRM : R ≤ M := hRMh.trans inf_le_left
  have hRH : R ≤ H := hRMh.trans inf_le_right
  have hRp : IsPGroup 3 ↥R := P.isPGroup'.map (M ⊓ H).subtype
  have hRcard : ∃ a : ℕ, Nat.card R = 3 ^ a := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hRp
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hRcard
  have hidx : ¬ 3 ∣ P.toSubgroup.index := P.not_dvd_index
  have hMhdecomp : P.toSubgroup.index * Nat.card P.toSubgroup = Nat.card ↥(M ⊓ H) :=
    Subgroup.index_mul_card _
  have hPcard : Nat.card P.toSubgroup = Nat.card R := by
    rw [hRdef, Subgroup.card_map_of_injective (M ⊓ H).subtype_injective]
  set O := GLAPPrimeCoreOf 3 M with hOdef
  have hMcard : Nat.card M = Nat.card (O ⊓ M : Subgroup G) * Nat.card (barX 3 M M) :=
    card_eq_card_inter_mul_card_barX Nat.prime_three le_rfl
  have hMhcard : Nat.card (M ⊓ H : Subgroup G) =
      Nat.card (O ⊓ (M ⊓ H) : Subgroup G) * Nat.card (barX 3 M (M ⊓ H)) :=
    card_eq_card_inter_mul_card_barX Nat.prime_three hMh
  have hOM' : O ⊓ M = O := inf_eq_left.2 hOM
  have hqeq : barX 3 M (M ⊓ H) = barX 3 M M := by
    apply le_antisymm
    · exact barX_mono (p := 3) (C := M) inf_le_left
    · have h1 : barX 3 M (⊤ : Subgroup G) ≤ barX 3 M (M ⊓ H) := by
        refine hcov.trans ?_
        have h2 := barX_inf_self (p := 3) M H
        rw [inf_comm] at h2
        exact le_of_eq h2.symm
      have h3 : barX 3 M (M : Subgroup G) ≤ barX 3 M (⊤ : Subgroup G) :=
        barX_mono (p := 3) (C := M) le_top
      exact h3.trans h1
  rw [hqeq] at hMhcard
  rw [hOM'] at hMcard
  have hOdvd : Nat.card (O ⊓ (M ⊓ H) : Subgroup G) ∣ Nat.card O :=
    Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨c, hc⟩ := hOdvd
  have hcop3 : Nat.Coprime 3 (Nat.card O) := hcop
  have hcopc : Nat.Coprime 3 c :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ hc.symm) hcop3
  have hMc : Nat.card M = c * Nat.card (M ⊓ H : Subgroup G) := by
    rw [hMcard, hMhcard, hc]; ring
  have hRmax : ∀ R' : Subgroup G, R' ≤ M → IsPGroup 3 ↥R' → R ≤ R' → R' = R := by
    intro R' hR'M hR'p hRR'
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hR'p
    have hdvdM : Nat.card R' ∣ Nat.card M := Subgroup.card_dvd_of_le hR'M
    have hdvdRR : Nat.card R ∣ Nat.card R' := Subgroup.card_dvd_of_le hRR'
    have hcoprime : Nat.Coprime (3 ^ b) (c * P.toSubgroup.index) := by
      apply Nat.Coprime.pow_left
      exact Nat.Coprime.mul_right hcopc ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hidx)
    have h1 : 3 ^ b ∣ 3 ^ a := by
      have hdiv : 3 ^ b ∣ c * P.toSubgroup.index * 3 ^ a := by
        have : c * P.toSubgroup.index * 3 ^ a = Nat.card M := by
          rw [hMc, ← hMhdecomp, hPcard, ha]; ring
        rw [this, ← hb]; exact hdvdM
      exact Nat.Coprime.dvd_of_dvd_mul_left hcoprime hdiv
    have h2 : 3 ^ a ∣ 3 ^ b := by
      have := hdvdRR
      rw [ha, hb] at this
      exact this
    have hab : a = b := by
      have e1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 h1
      have e2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 h2
      omega
    exact (Subgroup.eq_of_le_of_card_ge hRR' (by rw [ha, hb, hab])).symm
  refine ⟨R, ⟨hRM, hRp, fun R' hR'M hR'p hRR' => hRmax R' hR'M hR'p hRR'⟩, hRH⟩

theorem _root_.CFSG.LocalAnalysis.GLTheoremB.MovingAround.lemma1115_iii_of_inputs
    (h1111 : Lemma1111Statement) (h113 : Lemma113_iStatement) (h104v : Lemma104_vStatement)
    (hG : Input1115Gamma) (hC : Input1115Chain) :
    Lemma1115_iiiStatement := by
  intro G _ _ m p B M E A a K h H hH hcov
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨rfl, hA3, -⟩ := h1111 h
  have hsec : Sec11 G m 3 B M E A := h.toCex117Base.toSec11
  have hEM : inD 3 M E := hsec.pair.1.1
  have hm4 : 4 ≤ CFSG.Open.pRank 3 E := h113 hsec h.ha.1 h.ha.2 h.notD
  obtain ⟨E4, hE4E, hE4ab, hE4card⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) hm4
  have hE4M : E4 ≤ M := hE4E.trans hEM.1.1.1
  have hE4p : IsPGroup 3 ↥E4 := CFSG.Open.IsElemAbelian.isPGroup hE4ab
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 M)) :=
    sec11_glaPPrimeCoreOf_coprime M
  obtain ⟨R, hRsyl, hRH⟩ := exists_sylow_in_inter hcop hcov
  obtain ⟨x, hx, S, hSp, hSM, hRS, hES⟩ :=
    exists_conj_le_pGroup' (p := 3) (K := M) (X := R) (Y := E4) hRsyl.1 hRsyl.2.1 hE4M hE4p
  have hSR : S = R := hRsyl.2.2 S hSM hSp hRS
  set B1 : Subgroup G := GLBConj x E4 with hB1
  have hB1R : B1 ≤ R := hES.trans hSR.le
  have hB1M : B1 ≤ M := hB1R.trans hRsyl.1
  have hB1ab : IsElemAbelian 3 B1 := isElemAbelian_GLBConj x hE4ab
  have hB1card : Nat.card B1 = 3 ^ 4 := by
    rw [hB1]
    unfold GLBConj
    rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hE4card]
  have hB1ek : IsEkIn 3 4 M B1 := ⟨hB1M, hB1ab, hB1card⟩
  have hB1ek' : IsEkIn 3 4 R B1 := ⟨hB1R, hB1ab, hB1card⟩
  have h104 := h104v hsec.toSec10Fails hsec.pair (Or.inr hA3) hRsyl
  obtain ⟨hD0, -⟩ := h104
  obtain ⟨-, -, A', hA'D, hB1A'⟩ := hD0 B1 hB1ek'
  have hcoreB1 : GLBCore 3 2 B1 ≤ M := by
    refine le_trans ?_ hA'D.2.clause_d
    unfold GLBCore
    exact sSup_le_sSup (by
      rintro N ⟨Q, hQ, hk, rfl⟩
      exact ⟨Q, hQ.trans hB1A', hk, rfl⟩)
  have hB1H : B1 ≤ H := hB1R.trans hRH
  have hI1 := hG h H hH B1 hB1ek hB1H
  have hcovM : Covers 3 H M (jLayer a H) :=
    le_trans hI1 (barX_mono (p := 3) (C := H) (inf_le_left.trans hcoreB1))
  exact h.notM (hC h H hH hcovM)

end Lemma1115

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end

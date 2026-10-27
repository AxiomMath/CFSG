module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def TwE6U38Centre : Prop :=
  ∀ (S : Type) [Group S], catalogIs S S9.isTE6two → ∀ α : MulAut S, α ^ 3 = 1 → α ≠ 1 →
    ∀ I : Subgroup S, IsComponentOf I (fixSubgroup α) →
      Nat.card (↥I ⧸ Subgroup.center ↥I) = 5515776 → Subgroup.center ↥I = ⊥

@[expose] def TwE6CoverNoSU38 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q → IsPGroup 3 (Subgroup.center Q) →
    catalogIs (Q ⧸ Subgroup.center Q) S9.isTE6two →
    ∀ (P : Type) [Group P] [Finite P], CFSG.Open.IsQuasisimple P → Subgroup.center P ≠ ⊥ →
      catalogIs (P ⧸ Subgroup.center P) S9.isU3eight →
      ∀ ψ : P →* Q, Function.Injective ψ →
        ∀ z ∈ Subgroup.center P, ψ z ∈ Subgroup.center Q → z = 1

theorem twE6_contra {Jg Q Tt : Type} [Group Jg] [Finite Jg] [Group Q] [Finite Q] [Group Tt]
    (hC : TwE6CoverNoSU38) (lam : Jg →* Q) (rho : Q →* Tt) (hker : rho.ker = Subgroup.center Q)
    (hQ : CFSG.Open.IsQuasisimple Q) (hZ3 : IsPGroup 3 (Subgroup.center Q))
    (hQcat : catalogIs (Q ⧸ Subgroup.center Q) S9.isTE6two)
    (hlam : Nat.Coprime 3 (Nat.card lam.ker))
    (hP : CFSG.Open.IsQuasisimple (Jg ⧸ GLAPPrimeCore 3 Jg))
    (hPZ : Subgroup.center (Jg ⧸ GLAPPrimeCore 3 Jg) ≠ ⊥)
    (hPU : catalogIs ((Jg ⧸ GLAPPrimeCore 3 Jg) ⧸ Subgroup.center (Jg ⧸ GLAPPrimeCore 3 Jg))
      S9.isU3eight)
    (I : Subgroup Tt) (hIs : IsSimpleGroup ↥I) (hI3 : 3 ∣ Nat.card ↥I)
    (hIZ : Subgroup.center ↥I = ⊥) (hpiI : ∀ j, rho (lam j) ∈ I)
    (hsurj : ∀ t ∈ I, ∃ j, rho (lam j) = t) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := GLAPPrimeCore 3 Jg with hO
  have hOcop : Nat.Coprime 3 (Nat.card O) := CFSG.pPrimeCore_coprime_card
  let π : Jg →* ↥I := (rho.comp lam).codRestrict I hpiI
  have hπval : ∀ j, ((π j : ↥I) : Tt) = rho (lam j) := fun j => rfl
  have hπs : Function.Surjective π := fun t => by
    obtain ⟨j, hj⟩ := hsurj t t.2
    exact ⟨j, Subtype.ext hj⟩
  have hOπ : ∀ j ∈ O, π j = 1 := by
    intro j hj
    have hN1 : (O.map π).Normal := Subgroup.Normal.map inferInstance π hπs
    have hcop : Nat.Coprime 3 (Nat.card (O.map π)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ π) hOcop
    haveI := hN1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.map π) with h | h
    · have hmem : π j ∈ O.map π := Subgroup.mem_map_of_mem π hj
      rw [h] at hmem
      exact Subgroup.mem_bot.1 hmem
    · exfalso
      rw [h, Subgroup.card_top] at hcop
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop hI3
  have hOlam : ∀ j ∈ O, lam j = 1 := by
    intro j hj
    have h1 : rho (lam j) = 1 := by
      have := congrArg Subtype.val (hOπ j hj)
      rwa [hπval] at this
    have hmem : lam j ∈ Subgroup.center Q := by
      rw [← hker]
      exact h1
    obtain ⟨k, hk⟩ := hZ3 ⟨lam j, hmem⟩
    have hk' : (lam j) ^ (3 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hd1 : orderOf (lam j) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hd2 : orderOf (lam j) ∣ Nat.card O := by
      refine (orderOf_map_dvd lam j).trans ?_
      have := Subgroup.orderOf_dvd_natCard O hj
      exact this
    have hc : Nat.Coprime (3 ^ k) (Nat.card O) := Nat.Coprime.pow_left k hOcop
    have h1' : orderOf (lam j) = 1 := Nat.eq_one_of_dvd_coprimes hc hd1 hd2
    exact orderOf_eq_one_iff.1 h1'
  have hkerO : lam.ker ≤ O := le_sSup ⟨inferInstance, hlam⟩
  let ψ : (Jg ⧸ O) →* Q := QuotientGroup.lift O lam hOlam
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
    have : lam j = 1 := hy
    exact (QuotientGroup.eq_one_iff j).2 (hkerO this)
  have hmain := hC Q hQ hZ3 hQcat (Jg ⧸ O) hP hPZ hPU ψ hψinj
  have hcent : ∀ z ∈ Subgroup.center (Jg ⧸ O), ψ z ∈ Subgroup.center Q := by
    intro z hz
    rw [← hker, MonoidHom.mem_ker]
    obtain ⟨j₀, rfl⟩ := QuotientGroup.mk_surjective z
    have hπc : π j₀ ∈ Subgroup.center ↥I := by
      rw [Subgroup.mem_center_iff]
      intro i
      obtain ⟨j, rfl⟩ := hπs i
      have hcomm : (QuotientGroup.mk j : Jg ⧸ O) * QuotientGroup.mk j₀ =
          QuotientGroup.mk j₀ * QuotientGroup.mk j := (Subgroup.mem_center_iff.1 hz _)
      have hq : (QuotientGroup.mk (j * j₀) : Jg ⧸ O) = QuotientGroup.mk (j₀ * j) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
        exact hcomm
      have hmemO : (j * j₀)⁻¹ * (j₀ * j) ∈ O := QuotientGroup.eq.1 hq
      have h1 := hOπ _ hmemO
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      rw [← map_mul, ← map_mul]
      exact h1
    rw [hIZ] at hπc
    have h1 := congrArg Subtype.val (Subgroup.mem_bot.1 hπc)
    have h2 : rho (lam j₀) = 1 := by simpa [hπval] using h1
    exact h2
  have hz1 : ∀ z ∈ Subgroup.center (Jg ⧸ O), z = 1 := fun z hz => hmain z hz (hcent z hz)
  obtain ⟨z, hz1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hPZ
  exact hz1' (Subtype.ext (hz1 z z.2))

end CFSG.LocalAnalysis.GLTheoremA.I141F

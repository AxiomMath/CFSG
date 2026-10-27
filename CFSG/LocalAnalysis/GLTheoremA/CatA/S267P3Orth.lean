module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Excess
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Iso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3OrthWit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3OrthFix
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.D44
import CFSG.CGT.T75P.SylowSplit
import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ModelA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.RankThree.PartOne.CTP (IsOuterOfOrder)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

private theorem three_dvd_card_sq_sub_one {Q : TauCeti.PrimePower} (hQ3 : Q.p ≠ 3) :
    3 ∣ Q.card ^ 2 - 1 := by
  have h3 : ¬ 3 ∣ Q.card := by
    rw [TauCeti.PrimePower.card_def]
    intro h
    exact hQ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hmod : Q.card ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    have : Q.card % 3 = 1 ∨ Q.card % 3 = 2 := by omega
    rcases this with h | h <;> rw [h]
  omega

section Core

variable {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem inf_centralizer_eq_bot_of_center (hZ : Subgroup.center ↥S = ⊥) :
    S ⊓ Subgroup.centralizer (S : Set Ω) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxS, hxC⟩
  have : (⟨x, hxS⟩ : ↥S) ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext ((Subgroup.mem_centralizer_iff.1 hxC) g g.2)
  rw [hZ, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

theorem P3Hyp.inf_centMod_le_centralizer (H : P3Hyp q S B) :
    B ⊓ centModSubgroup 3 S ≤ Subgroup.centralizer (S : Set Ω) := fun _ hb =>
  Subgroup.mem_centralizer_iff.2 fun _ hs => (H.comm_of_mem_centMod hb.2 hs).symm

theorem P3Hyp.comm_of_mem (H : P3Hyp q S B) {x y : Ω} (hx : x ∈ B) (hy : y ∈ B) :
    x * y = y * x := by
  have := H.elem.1
  exact congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem P3Hyp.le_sup_centralizer (H : P3Hyp q S B)
    (hF : ∀ β : MulAut ↥S, IsOuterOfOrder 3 β → ∃ (M : Type) (_ : Group M) (_ : Finite M),
      3 ≤ GLATwoLocalRank 3 M ∧ Subgroup.center M = ⊥ ∧
        ∃ ψ : M →* ↥S, Function.Injective ψ ∧ ∀ m, β (ψ m) = ψ m) :
    B ≤ S ⊔ Subgroup.centralizer (S : Set Ω) := by
  haveI := H.normal
  by_contra hBN
  obtain ⟨b, hbB, hbN⟩ := SetLike.not_le_iff_exists.1 hBN
  set C : Subgroup Ω := Subgroup.centralizer (S : Set Ω) with hC
  set β : MulAut ↥S := MulAut.conjNormal b with hβdef
  have hb3 : b ^ 3 = 1 := H.elem.2 b hbB
  have hβ3 : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hb3, map_one]
  have hnotinner : ∀ g : ↥S, β ≠ MulAut.conj g := by
    intro g hg
    apply hbN
    have hc : (g : Ω)⁻¹ * b ∈ C := Subgroup.mem_centralizer_iff.2 fun s hs => by
      have := congrArg (fun φ : MulAut ↥S => ((φ ⟨s, hs⟩ : ↥S) : Ω)) hg
      simp only [hβdef, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at this
      calc s * ((g : Ω)⁻¹ * b) = (g : Ω)⁻¹ * ((g : Ω) * s * (g : Ω)⁻¹) * b := by group
        _ = (g : Ω)⁻¹ * (b * s * b⁻¹) * b := by rw [this]
        _ = ((g : Ω)⁻¹ * b) * s := by group
    have e : b = (g : Ω) * ((g : Ω)⁻¹ * b) := by group
    rw [e]
    exact Subgroup.mul_mem_sup g.2 hc
  have hβ1 : β ≠ 1 := fun h => hnotinner 1 (by rw [h, map_one])
  obtain ⟨M, _, _, hW, hZM, ψ, hψ, hfix⟩ :=
    hF β ⟨orderOf_eq_prime hβ3 hβ1, hnotinner⟩
  set K' : Subgroup Ω := (S.subtype.comp ψ).range with hK'
  have hK'inj : Function.Injective (S.subtype.comp ψ) := S.subtype_injective.comp hψ
  let eK : M ≃* ↥K' := MonoidHom.ofInjective hK'inj
  have hbK : ∀ k ∈ K', k * b = b * k := by
    rintro _ ⟨m, rfl⟩
    have h1 := congrArg Subtype.val (hfix m)
    simp only [hβdef, MulAut.conjNormal_apply] at h1
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    calc (ψ m : Ω) * b = (b * ψ m * b⁻¹) * b := by rw [h1]
      _ = b * ψ m := by group
  have hK'S : K' ≤ S := by
    rintro _ ⟨m, rfl⟩
    exact (ψ m).2
  set B₀ : Subgroup Ω := B ⊓ centModSubgroup 3 S with hB₀
  have hB₀C := H.inf_centMod_le_centralizer
  set C' : Subgroup Ω := Subgroup.zpowers b ⊔ B₀ with hC'
  have hC'B : C' ≤ B := sup_le ((Subgroup.zpowers_le).2 hbB) inf_le_left
  have hC'el : IsElemAbelian 3 C' := H.elem.mono hC'B
  have hC'K : C' ≤ Subgroup.centralizer (K' : Set Ω) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_iff.2 hbK
    · intro x hx
      exact Subgroup.mem_centralizer_iff.2 fun k hk =>
        (Subgroup.mem_centralizer_iff.1 (hB₀C hx)) k (hK'S hk)
  have hZK : Subgroup.center ↥K' = ⊥ := by
    rw [← Subgroup.map_center_eq eK, hZM, Subgroup.map_bot]
  have hWK : 3 ≤ GLATwoLocalRank 3 ↥K' := by
    have := CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv eK Nat.prime_three
    change 3 ≤ localRank 3 ↥K'
    rw [← this]
    exact hW
  have h5 := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.le_twoLocalRank_of_central
    Nat.prime_three hC'el hC'K hZK (n := 3) (by norm_num) hWK
  have hb1 : b ≠ 1 := fun h => hbN (h ▸ one_mem _)
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hinf : Subgroup.zpowers b ⊓ B₀ = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers b ⊓ B₀) ∣ 3 := by
      rw [← hbord, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers b ⊓ B₀ = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hbord, h3])
      have hbI : b ∈ Subgroup.zpowers b ⊓ B₀ := by
        rw [heq]
        exact Subgroup.mem_zpowers b
      exact hbN (Subgroup.mem_sup_right (hB₀C hbI.2))
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ B₀, x * y = y * x := fun x hx y hy =>
    H.comm_of_mem ((Subgroup.zpowers_le).2 hbB hx) hy.1
  have hC'c : Nat.card C' = 3 ^ 2 := by
    rw [hC', CFSG.CGT.T75P.card_sup_of_commute hcomm hinf, Nat.card_zpowers, hbord, H.cent]
    norm_num
  have hr := CFSG.HardMathSupport.Solomon.Coordinator.i271_pRank_eq Nat.prime_three hC'el hC'c
  have := H.twoLocalRank_le
  omega

theorem P3Hyp.eq_sup_of_le (H : P3Hyp q S B) (hZ : Subgroup.center ↥S = ⊥)
    (hW : 3 ≤ GLATwoLocalRank 3 ↥S) (hBN : B ≤ S ⊔ Subgroup.centralizer (S : Set Ω)) :
    B = (B ⊓ centModSubgroup 3 S) ⊔ (B ⊓ S) ∧
      (B ⊓ centModSubgroup 3 S) ⊓ (B ⊓ S) = ⊥ := by
  haveI := H.normal
  set C : Subgroup Ω := Subgroup.centralizer (S : Set Ω) with hC
  set B₀ : Subgroup Ω := B ⊓ centModSubgroup 3 S with hB₀
  have hSC := inf_centralizer_eq_bot_of_center hZ
  have hB₀C := H.inf_centMod_le_centralizer
  have hinf : B₀ ⊓ (B ⊓ S) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₀, -, hxS⟩
    have : x ∈ S ⊓ C := ⟨hxS, hB₀C hx₀⟩
    rwa [hSC] at this
  refine ⟨?_, hinf⟩
  set φ : Ω →* Ω ⧸ S := QuotientGroup.mk' S with hφ
  have hker : φ.ker = S := QuotientGroup.ker_mk' S
  have hφS : S.map φ = ⊥ := (Subgroup.map_eq_bot_iff _).2 hker.ge
  have htop : (⊤ : Subgroup Ω).map φ = ⊤ :=
    Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective S)
  have hSCtop : S ⊔ C = ⊤ := top_le_iff.1 (H.sup ▸ sup_le le_sup_left hBN)
  have hmapC : C.map φ = ⊤ := by
    rw [← htop, ← hSCtop, Subgroup.map_sup, hφS, bot_sup_eq]
  have hmapB : B.map φ = ⊤ := by
    rw [← htop, ← H.sup, Subgroup.map_sup, hφS, bot_sup_eq]
  have hpre : ∀ c ∈ C, ∃ b ∈ B, φ b = φ c := fun c _ => by
    have : φ c ∈ B.map φ := by rw [hmapB]; trivial
    obtain ⟨b, hb, he⟩ := this
    exact ⟨b, hb, he⟩
  have hmemS : ∀ x : Ω, φ x = 1 → x ∈ S := fun x hx => by
    rw [← hker]
    exact hx
  have hCel : IsElemAbelian 3 C := by
    refine ⟨⟨⟨fun c₁ c₂ => Subtype.ext ?_⟩⟩, fun c hc => ?_⟩
    · obtain ⟨b₁, hb₁, he₁⟩ := hpre c₁ c₁.2
      obtain ⟨b₂, hb₂, he₂⟩ := hpre c₂ c₂.2
      have hx : ((c₁ : Ω) * c₂) * ((c₂ : Ω) * c₁)⁻¹ ∈ S ⊓ C := by
        refine ⟨hmemS _ ?_, C.mul_mem (C.mul_mem c₁.2 c₂.2) (C.inv_mem (C.mul_mem c₂.2 c₁.2))⟩
        rw [map_mul, map_inv, map_mul, map_mul, ← he₁, ← he₂, ← map_mul, ← map_mul,
          H.comm_of_mem hb₁ hb₂, mul_inv_cancel]
      rw [hSC, Subgroup.mem_bot, mul_inv_eq_one] at hx
      exact hx
    · obtain ⟨b, hb, he⟩ := hpre c hc
      have hx : c ^ 3 ∈ S ⊓ C := by
        refine ⟨hmemS _ ?_, C.pow_mem hc 3⟩
        rw [map_pow, ← he, ← map_pow, H.elem.2 b hb, map_one]
      rw [hSC, Subgroup.mem_bot] at hx
      exact hx
  have hcardC : Nat.card (C.map φ) = Nat.card C := by
    have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker φ C
    rw [hker, inf_comm, hSC, Subgroup.card_bot, mul_one] at h
    exact h
  have hcardB := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker φ B
  rw [hker, hmapB, ← hmapC, hcardC, H.card] at hcardB
  have h4 := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.le_twoLocalRank_of_central
    Nat.prime_three hCel le_rfl hZ (n := 3) (by norm_num) hW
  have h4' := H.twoLocalRank_le
  obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i271_exists_card_eq Nat.prime_three hCel
  have hr := CFSG.HardMathSupport.Solomon.Coordinator.i271_pRank_eq Nat.prime_three hCel hc
  have hc1 : c ≤ 1 := by omega
  have hB₀le : Nat.card B₀ ≤ Nat.card C := Subgroup.card_le_of_le hB₀C
  rw [H.cent, hc] at hB₀le
  have hc1' : c = 1 := by
    rcases (by omega : c = 0 ∨ c = 1) with h0 | h0
    · rw [h0] at hB₀le
      norm_num at hB₀le
    · exact h0
  rw [hc, hc1', pow_one] at hcardB
  have hBS : Nat.card ↥(B ⊓ S) = 3 ^ 3 := by omega
  have hcomm : ∀ x ∈ B₀, ∀ y ∈ B ⊓ S, x * y = y * x := fun x hx y hy =>
    H.comm_of_mem hx.1 hy.1
  have hcard : Nat.card ↥(B₀ ⊔ (B ⊓ S)) = 3 ^ 4 := by
    rw [CFSG.CGT.T75P.card_sup_of_commute hcomm hinf, H.cent, hBS]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left)
    (by rw [hcard, H.card])).symm

theorem P3Hyp.eq_sup (H : P3Hyp q S B) (hZ : Subgroup.center ↥S = ⊥)
    (hW : 3 ≤ GLATwoLocalRank 3 ↥S)
    (hF : ∀ β : MulAut ↥S, IsOuterOfOrder 3 β → ∃ (M : Type) (_ : Group M) (_ : Finite M),
      3 ≤ GLATwoLocalRank 3 M ∧ Subgroup.center M = ⊥ ∧
        ∃ ψ : M →* ↥S, Function.Injective ψ ∧ ∀ m, β (ψ m) = ψ m) :
    B = (B ⊓ centModSubgroup 3 S) ⊔ (B ⊓ S) ∧
      (B ⊓ centModSubgroup 3 S) ⊓ (B ⊓ S) = ⊥ :=
  H.eq_sup_of_le hZ hW (H.le_sup_centralizer hF)

theorem P3Hyp.center_pQuot_eq_bot (H : P3Hyp q S B) (hZ : Subgroup.center ↥S = ⊥) :
    Subgroup.center (PQuot 3 S) = ⊥ := by
  rw [← Subgroup.map_center_eq (pquotEquiv H).symm, hZ, Subgroup.map_bot]

theorem P3Hyp.eq_sup_of_odd (H : P3Hyp q S B) (hZ : Subgroup.center ↥S = ⊥) {n ℓ f : ℕ}
    (hM : StatedClassicalModel ↥S .POmegaOdd n ℓ f) (hℓ3 : ℓ ≠ 3) :
    B = (B ⊓ centModSubgroup 3 S) ⊔ (B ⊓ S) ∧
      (B ⊓ centModSubgroup 3 S) ⊓ (B ⊓ S) = ⊥ := by
  refine H.eq_sup hZ (OrthWit.three_le_twoLocalRank_of_odd hM hℓ3) fun β hβ => ?_
  obtain ⟨M, _, e, hM', ψ, hψ, hfix⟩ :=
    OrthFix.exists_fixed_model_of_odd hM Nat.prime_three (by norm_num) (Ne.symm hℓ3) hβ
  haveI : Finite M := Finite.of_injective ψ hψ
  exact ⟨M, inferInstance, inferInstance, OrthWit.three_le_twoLocalRank_of_odd hM' hℓ3,
    OrthFix.center_eq_bot_of_orth_model (Or.inl rfl) hM', ψ, hψ, hfix⟩

theorem P3Hyp.eq_sup_of_minus (H : P3Hyp q S B) (hZ : Subgroup.center ↥S = ⊥) {n ℓ f : ℕ}
    (hM : StatedClassicalModel ↥S .POmegaMinus n ℓ f) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) :
    B = (B ⊓ centModSubgroup 3 S) ⊔ (B ⊓ S) ∧
      (B ⊓ centModSubgroup 3 S) ⊓ (B ⊓ S) = ⊥ := by
  refine H.eq_sup hZ (OrthWit.three_le_twoLocalRank_of_minus hM hℓ2 hℓ3) fun β hβ => ?_
  obtain ⟨M, _, e, hM', ψ, hψ, hfix⟩ :=
    OrthFix.exists_fixed_model_of_minus hM Nat.prime_three (by norm_num) (Ne.symm hℓ3) hβ
  haveI : Finite M := Finite.of_injective ψ hψ
  exact ⟨M, inferInstance, inferInstance, OrthWit.three_le_twoLocalRank_of_minus hM' hℓ2 hℓ3,
    OrthFix.center_eq_bot_of_orth_model (Or.inr (Or.inr rfl)) hM', ψ, hψ, hfix⟩

end Core

theorem p3At_B3 (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 3 Q).Valid) :
    P3At ⟨.B 3 Q, hv⟩ := by
  intro q Ω _ _ S B H hchar he
  obtain ⟨e⟩ := he
  have hQq : Q.p = q := by simpa using hchar
  have hq2 : Q.p ≠ 2 := hQq ▸ H.two
  have hq3 : Q.p ≠ 3 := hQq ▸ H.three
  have hQ5 : 5 ≤ Q.p ^ Q.exponent := (Q.prime_p.five_le_of_ne_two_of_ne_three hq2 hq3).trans
    (Nat.le_self_pow Q.exponent_pos.ne' _)
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 Q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 Q, hv⟩) =
      Q.p ^ Q.exponent := by
    rw [CFSG.LieType.SeitzGeneration.card_fixedField_eq]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
  have hMd : StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.B 3 Q, hv⟩).Group .POmegaOdd 3 Q.p
      Q.exponent :=
    ⟨⟨Q.prime_p, Q.exponent_pos, le_rfl, hq2⟩, _, inferInstance, inferInstance, hcard,
      ⟨CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd 3 Q hv hq2
        le_rfl⟩⟩
  have hZ : Subgroup.center ↥S = ⊥ := by
    refine H.center_eq_bot_of_multiplier e ?_
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaOdd_row hMd (Or.inl hQ5)
    rw [Nat.card_congr eM.toEquiv]
    have hex : exceptionalOrders .POmegaOdd 3 Q.p Q.exponent = (1, 1) := by
      unfold exceptionalOrders
      split <;> simp_all
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hex,
      Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, genericOrders]
    norm_num
  have hMS : StatedClassicalModel ↥S .POmegaOdd 3 Q.p Q.exponent :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ((psimpleEquiv H hZ).symm.trans e).symm hMd
  obtain ⟨h1, h2⟩ := H.eq_sup_of_odd hZ hMS hq3
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨H.card, h1, h2, H.center_pQuot_eq_bot hZ, Q, hQq,
    Or.inl ⟨.lie ⟨.B 3 Q, hv⟩, rfl, ⟨e⟩⟩, three_dvd_card_sq_sub_one hq3⟩)))

theorem p3At_twistedD4
    (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD 4 Q).Valid) : P3At ⟨.twistedD 4 Q, hv⟩ := by
  intro q Ω _ _ S B H hchar he
  obtain ⟨e⟩ := he
  have hQq : Q.p = q := by simpa using hchar
  have hq2 : Q.p ≠ 2 := hQq ▸ H.two
  have hq3 : Q.p ≠ 3 := hQq ▸ H.three
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD 4 Q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD 4 Q, hv⟩) =
      Q.p ^ Q.exponent := by
    rw [CFSG.LieType.SeitzGeneration.card_fixedField_eq]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
  obtain ⟨b, c, hirr, ⟨eD⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      4 Q hv
  have hMd : StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.twistedD 4 Q, hv⟩).Group .POmegaMinus 4
      Q.p Q.exponent :=
    ⟨⟨Q.prime_p, Q.exponent_pos, le_rfl⟩, _, inferInstance, inferInstance, hcard, b, c, hirr,
      ⟨eD⟩⟩
  have hZ : Subgroup.center ↥S = ⊥ := by
    refine H.center_eq_bot_of_multiplier e ?_
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaMinus_row hMd
    rw [Nat.card_congr eM.toEquiv]
    have hex : exceptionalOrders .POmegaMinus 4 Q.p Q.exponent = (1, 1) := by
      unfold exceptionalOrders
      split <;> simp_all
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hex,
      Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, genericOrders, mul_one]
    intro h3
    have h4 := h3.trans (Nat.gcd_dvd_left 4 _)
    omega
  have hMS : StatedClassicalModel ↥S .POmegaMinus 4 Q.p Q.exponent :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ((psimpleEquiv H hZ).symm.trans e).symm hMd
  obtain ⟨h1, h2⟩ := H.eq_sup_of_minus hZ hMS hq2 hq3
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨H.card, h1, h2, H.center_pQuot_eq_bot hZ, Q, hQq,
    Or.inr ⟨.lie ⟨.twistedD 4 Q, hv⟩, rfl, ⟨e⟩⟩, three_dvd_card_sq_sub_one hq3⟩)))

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end

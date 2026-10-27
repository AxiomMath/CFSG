module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CaseAGen
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.AutModelNoSig
public import CFSG.HardMathSupport.Dickson.I271.SporGen
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def CentGen (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ P : Subgroup S, IsElemAbelian p P → Nat.card P = p ^ 2 →
    Subgroup.closure {σ : S | ∃ e ∈ P, e ≠ 1 ∧ σ * e = e * σ} = ⊤

theorem mem_inner_of_pow_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hO : Nat.card (Outer G) ≤ 2) {ψ : MulAut G} (hψ : ψ ^ p = 1) :
    ψ ∈ inner G := by
  have hfin : Finite (MulAut G) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (Outer G) := Nat.card_pos
  have h1 : (QuotientGroup.mk ψ : Outer G) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hψ, QuotientGroup.mk_one]
  have h3 : orderOf (QuotientGroup.mk ψ : Outer G) ∣ p := orderOf_dvd_of_pow_eq_one h1
  have hle : orderOf (QuotientGroup.mk ψ : Outer G) ≤ 2 :=
    (Nat.le_of_dvd hpos (orderOf_dvd_natCard _)).trans hO
  have h1' : orderOf (QuotientGroup.mk ψ : Outer G) = 1 := by
    rcases (Nat.dvd_prime hp).1 h3 with h | h
    · exact h
    · exfalso
      have h2 := hp.two_le
      omega
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1'
  exact h1'

section Transfer

@[expose] def centSet {S : Type*} [Group S] (P : Subgroup S) : Set S :=
  {σ : S | ∃ e ∈ P, e ≠ 1 ∧ σ * e = e * σ}

theorem centSet_map {S S' : Type*} [Group S] [Group S'] (φ : S ≃* S') (P : Subgroup S) :
    centSet (P.map φ.toMonoidHom) = φ.toMonoidHom '' centSet P := by
  ext σ'
  constructor
  · rintro ⟨e', ⟨e, he, rfl⟩, he1, hc⟩
    refine ⟨φ.symm σ', ⟨e, he, ?_, ?_⟩, by simp⟩
    · rintro rfl
      exact he1 (map_one _)
    · apply φ.injective
      simpa using hc
  · rintro ⟨σ, ⟨e, he, he1, hc⟩, rfl⟩
    refine ⟨φ e, ⟨e, he, rfl⟩, ?_, ?_⟩
    · intro h1
      exact he1 (φ.injective (by simpa using h1))
    · simpa using congrArg φ hc

theorem closure_centSet_map {S S' : Type*} [Group S] [Group S'] (φ : S ≃* S') {P : Subgroup S}
    (h : Subgroup.closure (centSet P) = ⊤) :
    Subgroup.closure (centSet (P.map φ.toMonoidHom)) = ⊤ := by
  rw [centSet_map, ← MonoidHom.map_closure, h, Subgroup.map_top]
  exact MonoidHom.range_eq_top.2 φ.surjective

theorem CentGen.of_mulEquiv {p : ℕ} {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (h : CentGen p S) : CentGen p S' := by
  intro P hPel hPcard
  have hP0el : IsElemAbelian p (P.map e.symm.toMonoidHom) := hPel.map _
  have hP0card : Nat.card (P.map e.symm.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hPcard]
  have := closure_centSet_map e (h _ hP0el hP0card)
  have hP : (P.map e.symm.toMonoidHom).map e.toMonoidHom = P := by
    rw [Subgroup.map_map]
    ext x
    simp
  rw [hP] at this
  exact this

theorem centGen_of_sylow {S : Type*} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hcard : (Nat.card S).factorization p = 2) {P₀ : Subgroup S} (hP₀card : Nat.card P₀ = p ^ 2)
    (hgen : Subgroup.closure (centSet P₀) = ⊤) : CentGen p S := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro P hPel hPcard
  let S₀ : Sylow p S := Sylow.ofCard P₀ (by rw [hP₀card, hcard])
  let S₁ : Sylow p S := Sylow.ofCard P (by rw [hPcard, hcard])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S S₀ S₁
  have hPeq : P = P₀.map (MulAut.conj g).toMonoidHom := by
    have h1 : (S₁ : Subgroup S) = P := Sylow.coe_ofCard _ _
    have h2 : (S₀ : Subgroup S) = P₀ := Sylow.coe_ofCard _ _
    rw [← h1, ← hg, Sylow.coe_subgroup_smul, h2]
    rfl
  rw [hPeq]
  exact closure_centSet_map (MulAut.conj g) hgen

end Transfer

section Conclusion

variable {X : Type} [Group X] [Finite X]

theorem conclusion_of_centGen {p : ℕ} {K B : Subgroup X} (hH : I271Hyp p K B)
    (hN : I271Norm p K B) (hZ : Subgroup.center ↥K = ⊥)
    (hR : AutRankLe2 p (↥K ⧸ Subgroup.center ↥K))
    (hO : Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) ≤ 2)
    (hCG : CentGen p (↥K ⧸ Subgroup.center ↥K)) : I271CaseA p K B := by
  have hp := hH.prime
  have hp2 := hH.odd
  have hBel : IsElemAbelian p B := hH.scp.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hperf : commutator ↥K = ⊤ := hq.1
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hnab : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a :=
    exists_noncomm_of_isQuasisimple hq
  have hcenS : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ :=
    center_eq_bot_of_isSimpleGroup hnab
  have hinj : Function.Injective (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →* MulAut (↥K ⧸ Subgroup.center ↥K)) :=
    conj_injective_of_center_eq_bot hcenS
  obtain ⟨π, hπ⟩ : ∃ π : ↥K →* (↥K ⧸ Subgroup.center ↥K),
      π = QuotientGroup.mk' (Subgroup.center ↥K) := ⟨_, rfl⟩
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro k hk
    rw [hπ] at hk
    have : k ∈ Subgroup.center ↥K := (QuotientGroup.eq_one_iff k).1 hk
    rw [hZ] at this
    exact Subgroup.mem_bot.1 this
  have hπsurj : Function.Surjective π := hπ ▸ QuotientGroup.mk'_surjective _
  have hAel : IsElemAbelian p (imgB B K) := isElemAbelian_imgB hBel
  have hAcard : Nat.card (imgB B K) = autOrderIn B K := card_imgB hperf
  have hA2 : Nat.card (imgB B K) = p ^ 2 := le_antisymm (hR _ hAel) (hAcard ▸ hN.2)
  have hinner : ∀ f ∈ imgB B K, f ∈ (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →*
      MulAut (↥K ⧸ Subgroup.center ↥K)).range := fun f hf =>
    mem_inner_of_pow_eq_one hp hp2 hO (hAel.2 f hf)
  obtain ⟨P, hP⟩ : ∃ P : Subgroup (↥K ⧸ Subgroup.center ↥K),
      P = (imgB B K).comap (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →*
        MulAut (↥K ⧸ Subgroup.center ↥K)) := ⟨_, rfl⟩
  have hPmap : P.map (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →*
      MulAut (↥K ⧸ Subgroup.center ↥K)) = imgB B K := by
    rw [hP, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hinner
  have hPel : IsElemAbelian p P := isElemAbelian_of_map_injective' hinj (hPmap ▸ hAel)
  have hPcard : Nat.card P = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, hA2]
  have hgen := hCG P hPel hPcard
  obtain ⟨U, hUdef⟩ : ∃ U : Set ↥K, U = π ⁻¹'
      {σ : ↥K ⧸ Subgroup.center ↥K | ∃ e ∈ P, e ≠ 1 ∧ σ * e = e * σ} := ⟨_, rfl⟩
  have hU : Subgroup.closure U = ⊤ := by
    apply Subgroup.map_injective hπinj
    rw [MonoidHom.map_closure, hUdef, Set.image_preimage_eq _ hπsurj, hgen,
      Subgroup.map_top, MonoidHom.range_eq_top.2 hπsurj]
  obtain ⟨T, hTdef⟩ : ∃ T : Set X, T = Subtype.val '' U := ⟨_, rfl⟩
  have hTK : Subgroup.closure T = K := by
    have : Subgroup.closure T = (Subgroup.closure U).map K.subtype := by
      rw [hTdef, MonoidHom.map_closure]; rfl
    rw [this, hU, Subgroup.map_top, Subgroup.range_subtype]
  have hc : 2 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)) := by
    have h1 := pRank_le_centralizer_add hp hBel hN.1 (r := 2) (hAcard ▸ hA2.le)
    have h2 := hH.rank_four
    omega
  refine caseA_of_gen hH hN.1 hc T hTK ?_
  intro x hx
  rw [hTdef] at hx
  obtain ⟨k, hkU, rfl⟩ := hx
  rw [hUdef] at hkU
  obtain ⟨e, heP, he1, hek⟩ := hkU
  have hef : MulAut.conj e ∈ imgB B K := by rw [hP] at heP; exact heP
  obtain ⟨b, hb, hbB, hbact⟩ := mem_imgB.1 hef
  refine ⟨b, hbB, ?_, ?_⟩
  · intro hbC
    have hker : (⟨b, hb⟩ : ↥(Subgroup.normalizer (K : Set X))) ∈
        (i271Act K (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K))).ker := by
      rw [ker_i271Act hperf (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K))]
      exact Subgroup.mem_subgroupOf.2 hbC
    rw [MonoidHom.mem_ker, hbact] at hker
    exact he1 (hinj (by rw [hker, map_one]))
  · have h1 : i271Act K (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) ⟨b, hb⟩ (π k) = π k := by
      rw [hbact, MulAut.conj_apply]
      calc e * π k * e⁻¹ = (π k * e) * e⁻¹ := by rw [← hek]
        _ = π k := by group
    have h2 : π (K.normalizerMonoidHom ⟨b, hb⟩ k) = π k := by
      rw [← h1]
      rw [hπ]
      rfl
    have h3 := hπinj h2
    have h4 : b * (k : X) * b⁻¹ = (k : X) := by
      have := congrArg (fun w : ↥K => (w : X)) h3
      simpa using this
    calc b * (k : X) = (b * (k : X) * b⁻¹) * b := by group
      _ = (k : X) * b := by rw [h4]

end Conclusion

@[expose] def SporCentGen (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
      AutRankLe2 p S ∧ Nat.card (Outer S) ≤ 2 ∧ CentGen p S

theorem sporPair_of_centGen {name : TauCeti.SporadicName} {p : ℕ}
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers) (hp5 : 5 ≤ p)
    (h : SporCentGen name p) : SporPair name p := by
  intro X _ _ hX K B hH hN hS _ _
  left
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hZ := center_eq_bot_of_five_le hSpM hH hp5 hS
  obtain ⟨e⟩ := hS
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  obtain ⟨hR, hO, hCG⟩ := h (↥K ⧸ Subgroup.center ↥K) hq.2
    (exists_noncomm_of_isQuasisimple hq) ⟨e⟩
  exact conclusion_of_centGen hH hN hZ hR hO hCG

end CFSG.HardMathSupport.Dickson.I271

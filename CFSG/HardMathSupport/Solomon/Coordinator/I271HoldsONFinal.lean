module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsONBal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ONOuter
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Coprime
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple CFSG.Open Subgroup
  CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

theorem i271on_center_bot {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hcard : ¬ (Nat.card S).Prime) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    letI : CommGroup S :=
      { ‹Group S› with
        mul_comm := fun a b => by
          have hb : b ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top b
          exact Subgroup.mem_center_iff.1 hb a }
    exact hcard (IsSimpleGroup.prime_card (α := S))

section


theorem i271on_exists_q {S : Type} [Group S] (f : S ≃* PON.Group) :
    ∃ q : GM →* S, Function.Surjective q ∧ q.ker = zpowers zG := by
  let q : GM →* S := f.symm.toMonoidHom.comp (piON.comp modelEquiv.symm.toMonoidHom)
  have hq : Function.Surjective q :=
    f.symm.surjective.comp (piON_surjective.comp modelEquiv.symm.surjective)
  refine ⟨q, hq, ?_⟩
  ext g
  rw [MonoidHom.mem_ker]
  show f.symm (piON (modelEquiv.symm g)) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_piON, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← modelEquiv_zF, ← map_zpow, hk, MulEquiv.apply_symm_apply]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, ← modelEquiv_zF, ← map_zpow, MulEquiv.symm_apply_apply]

theorem i271AutBalanceON_holds : I271AutBalanceON := by
  intro S _ _ hS A hA hA81 T hT hAT
  obtain ⟨hS⟩ := hS
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut S) := Finite.of_injective (fun σ : MulAut S => (σ : S → S))
    DFunLike.coe_injective
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  have hSN : S ≃* CFSG.Blueprint.NativeSporadic.Carrier .ONan := hS.trans b'.symm
  have hsimple : IsSimpleGroup S := by
    have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
      CFSG.Sporadic.ON.isSimpleGroup_ON
    exact hSN.isSimpleGroup
  have hcard : Nat.card S = 460815505920 := by
    rw [Nat.card_congr hSN.toEquiv]
    exact CFSG.Sporadic.ON.card_ON
  have hcen : Subgroup.center S = ⊥ :=
    i271on_center_bot (by rw [hcard]; norm_num)
  have hnc : ∃ a b : S, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := exists_ne (1 : S)
    have : g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun y => hcon y g
    rw [hcen, Subgroup.mem_bot] at this
    exact hg this
  have hperf : commutator S = ⊤ := on25_perfect_of_simple hnc
  have hOut : (MulAut.conj : S →* MulAut S).range.index ∣ 2 :=
    onOuterTwo_holds S hperf
      ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans hS⟩
  have hNo := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOuterHolds_ONan_three S ⟨hSN⟩
  obtain ⟨q, hq, hker⟩ := i271on_exists_q (hSN.trans nonempty_equiv_PON.some)
  have hinj := i271on_conj_injective hcen
  have hAle : A ≤ (MulAut.conj : S →* MulAut S).range := fun α hα =>
    i2326o_mem_inner hOut (hA.2 α hα)
  set W : Subgroup S := A.comap (MulAut.conj : S →* MulAut S) with hW
  have hWA : W.map (MulAut.conj : S →* MulAut S) = A := by
    rw [hW, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hAle
  have hWel : IsElemAbelian 3 W := by
    refine ⟨⟨⟨fun y z => ?_⟩⟩, fun y hy => ?_⟩
    · apply Subtype.ext
      apply hinj
      have hy' : (MulAut.conj (y : S) : MulAut S) ∈ A := y.2
      have hz' : (MulAut.conj (z : S) : MulAut S) ∈ A := z.2
      have := congrArg Subtype.val (hA.1.is_comm.comm (⟨_, hy'⟩ : ↥A) ⟨_, hz'⟩)
      simpa [map_mul] using this
    · apply hinj
      have hy' : (MulAut.conj y : MulAut S) ∈ A := hy
      rw [map_pow, hA.2 _ hy', map_one]
  have hWcard : 81 ≤ Nat.card W := by
    have h1 : Nat.card (W.map (MulAut.conj : S →* MulAut S)) = Nat.card W :=
      Subgroup.card_map_of_injective hinj
    rw [hWA] at h1
    rw [← h1]
    simpa using hA81
  have hWT : ∀ y ∈ W, (MulAut.conj y : MulAut S) ∈ Subgroup.normalizer (T : Set (MulAut S)) :=
    fun y hy => hAT hy
  obtain ⟨Ab, hAbW, hAb9, hAbgood⟩ := i271on_good_lifts q hq hker hWel hWcard
  have hAbel : IsElemAbelian 3 Ab := CFSG.Open.IsElemAbelian.mono hWel hAbW
  set Ab' : Subgroup (MulAut S) := Ab.map (MulAut.conj : S →* MulAut S) with hAb'
  have hAb'el : IsElemAbelian 3 Ab' := CFSG.Open.IsElemAbelian.map hAbel _
  haveI : IsElementaryAbelian 3 ↥Ab' :=
    isElementaryAbelian_of_isElemAbelian hAb'el
  have hAb'card : 3 ^ 2 ≤ Nat.card Ab' := by
    rw [hAb', Subgroup.card_map_of_injective hinj, hAb9]
    norm_num
  have hAb'A : Ab' ≤ A := by
    rw [← hWA]
    exact Subgroup.map_mono hAbW
  have hT3 : ¬ 3 ∣ Nat.card T := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hT
  have hgen := le_iSup_centralizer_of_coprime (p := 3) (A := Ab') (U := T) hAb'card hT3
    (hAb'A.trans hAT)
  rw [eq_bot_iff]
  refine hgen.trans (iSup₂_le fun α hα => iSup_le fun hα1 => ?_)
  obtain ⟨y, hyAb, rfl⟩ := hα
  have hy1 : y ≠ 1 := fun h => hα1 (by rw [h, map_one])
  obtain ⟨a, A₀, hA₀, ha, haz, hqa⟩ := hAbgood y hyAb hy1
  have hbot := i271on_R_bot hcen hOut hNo q hq hker hWel hWcard hT hWT hA₀ ha haz
    (hqa ▸ hAbW hyAb)
  rw [hqa] at hbot
  exact hbot.le

end

end CFSG.HardMathSupport.Solomon.Coordinator

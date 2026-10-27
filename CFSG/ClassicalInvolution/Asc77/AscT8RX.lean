module

public import CFSG.ClassicalInvolution.Asc77.AscT8RSyl
public import CFSG.ClassicalInvolution.Asc77.AscT8Min
public import CFSG.ClassicalInvolution.Asc77.AscT8S26ULift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

namespace T8R

section Cert

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem eq_of_isSylow2In_of_le_sylow {M P Q : Subgroup G} (hP : IsSylow2In P M)
    (hQ : IsSylow2In Q M) (hPS : P ≤ (S : Subgroup G)) (hQS : Q ≤ (S : Subgroup G)) : P = Q := by
  have h1 : M ⊓ (S : Subgroup G) = P :=
    hP.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hP.1 hPS)
  have h2 : M ⊓ (S : Subgroup G) = Q :=
    hQ.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hQ.1 hQS)
  exact h1.symm.trans h2

theorem R_ne_T (hs : Std8 p f Ω K J S R T W z t) : R ≠ T := by
  intro h
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K :=
    T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.stand.mem hRΩ hRK
  have h8 := hΩ.eight_le_of_mem_RSet hp hRΩ
  exact hs.hJ.2.1 (hΩ.eq_of_le_of_le hs.hJ.1 hs.stand.mem hRsyl.2.1 (by omega)
    (h ▸ hTJ) hRK)

theorem eq_or_eq_of_mem_RSet_of_le (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {P : Subgroup G} (hP : P ∈ RSet Ω)
    (hPS : P ≤ (S : Subgroup G)) : P = R ∨ P = T := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  by_contra hcon
  push Not at hcon
  obtain ⟨M, hM, hPM⟩ := exists_isSylow2In_of_mem_RSet hP
  have hMK : M ≠ K := by
    rintro rfl
    exact hcon.1 (eq_of_isSylow2In_of_le_sylow hPM hRsyl hPS hRS)
  have hcomm : Commutes P R :=
    l6_7_proved p f hp hq G Ω hΩ S P hP R hRΩ hPS hRS hcon.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hp hRΩ; omega)
  have hPc : P ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx z hzR)
  have hP8 := hΩ.eight_le_of_mem_RSet hp hP
  have hPN : P ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK hM (Ne.symm hMK) hs.hz hPM.1 hPM.2.1
      (by omega) hPc
  have hMnbr : M ∈ omegaNbr Ω K := ⟨hM, hMK, P, hP, hPM.1, hPN⟩
  have hMX : M ≤ omegaNbrGen Ω K :=
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) M hMnbr
  have hJX : J ≤ omegaNbrGen Ω K :=
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have hTX : IsSylow2In T (omegaNbrGen Ω K) := isSylow2In_of_eq_sup_oddCoreOf hJX hX hTsyl
  have hQ2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ omegaNbrGen Ω K) := S.isPGroup'.to_inf_left
  have hQle : Nat.card ↥((S : Subgroup G) ⊓ omegaNbrGen Ω K) ≤ Nat.card T :=
    natCard_le_of_eq_sup_oddCoreOf hJX hX hTsyl inf_le_right hQ2
  have hTQ : T ≤ (S : Subgroup G) ⊓ omegaNbrGen Ω K := le_inf hTS (hTsyl.1.trans hJX)
  have hPQ : P ≤ (S : Subgroup G) ⊓ omegaNbrGen Ω K := le_inf hPS (hPM.1.trans hMX)
  have hQT : (S : Subgroup G) ⊓ omegaNbrGen Ω K = T :=
    (Subgroup.eq_of_le_of_card_ge hTQ hQle).symm
  have hcardP : Nat.card P = Nat.card T := by
    have h1 := hΩ.natCard_isSylow2In hM hPM
    have h2 := hΩ.natCard_isSylow2In hJΩ hTsyl
    rw [h1, h2]
  have hPleT : P ≤ T := hQT ▸ hPQ
  have hPT : P = T := Subgroup.eq_of_le_of_card_ge hPleT (le_of_eq hcardP.symm)
  exact hcon.2 hPT

theorem fix_or_swap (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) :
    (conjSub s R = R ∧ conjSub s T = T) ∨ (conjSub s R = T ∧ conjSub s T = R) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRT := R_ne_T hs
  have hcl := hΩ.conjInvariant
  have hsS' : ∀ P ≤ (S : Subgroup G), conjSub s P ≤ (S : Subgroup G) := by
    intro P hP
    have := conjSub_mono (n := s) hP
    rwa [conjSub_eq_self_of_mem hsS] at this
  have hR' := eq_or_eq_of_mem_RSet_of_le hs hX (RSet.conj hcl hRΩ s) (hsS' R hRS)
  have hT' := eq_or_eq_of_mem_RSet_of_le hs hX (RSet.conj hcl hTΩ s) (hsS' T hTS)
  rcases hR' with hR' | hR'
  · left
    refine ⟨hR', ?_⟩
    rcases hT' with hT' | hT'
    · exact absurd ((conjSub_inj s).mp (hT'.trans hR'.symm)).symm hRT
    · exact hT'
  · right
    refine ⟨hR', ?_⟩
    rcases hT' with hT' | hT'
    · exact hT'
    · exact absurd ((conjSub_inj s).mp (hT'.trans hR'.symm)) (Ne.symm hRT)

theorem conj_zt_of_mem_sylow (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) : s * (z * t) * s⁻¹ = z * t := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hzt : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
  have h8R := hΩ.eight_le_of_mem_RSet hp hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hp hTΩ
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  rcases fix_or_swap hs hX hsS with ⟨hR', hT'⟩ | ⟨hR', hT'⟩
  · have hK' : conjSub s K = K := T8.conjSub_eq_of_conjSub_eq hp hΩ hK hRΩ hRK hR'
    have hJ' : conjSub s J = J := T8.conjSub_eq_of_conjSub_eq hp hΩ hJΩ hTΩ hTJ hT'
    have h1 := hs.hz.conj_eq hK'
    have h2 := hs.ht.conj_eq hJ'
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = z * t := by rw [h1, h2]
  · have hK' : conjSub s K = J := hΩ.eq_of_le_of_le (hcl s K hK) hJΩ hTsyl.2.1 (by omega)
      (hR' ▸ conjSub_mono (n := s) hRK) hTJ
    have hJ' : conjSub s J = K := hΩ.eq_of_le_of_le (hcl s J hJΩ) hK hRsyl.2.1 (by omega)
      (hT' ▸ conjSub_mono (n := s) hTJ) hRK
    have h1 : s * z * s⁻¹ = t := (hs.ht.eq (hK' ▸ hs.hz.conj s)).symm
    have h2 : s * t * s⁻¹ = z := (hs.hz.eq (hJ' ▸ hs.ht.conj s)).symm
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = t * z := by rw [h1, h2]
      _ = z * t := hzt.symm

theorem exists_conj_of_le_of_eq_sup_oddCoreOf {X J₀ L : Subgroup G} (hp : p ≠ 2)
    (hΩ : HypOmegaMod p f Ω) (hJ₀ : J₀ ∈ Ω) (hL : L ∈ Ω) (hJ₀X : J₀ ≤ X) (hLX : L ≤ X)
    (hX : X = J₀ ⊔ oddCoreOf X) : ∃ x ∈ X, conjSub x J₀ = L := by
  obtain ⟨T₀, hT₀, -⟩ := IsSylow2In.exists_ge (P := J₀) (T := ⊥) IsPGroup.of_bot bot_le
  have hT₀R : T₀ ∈ RSet Ω := mem_RSet_of_isSylow2In hJ₀ hT₀
  have h8 := hΩ.eight_le_of_mem_RSet hp hT₀R
  have hTX : IsSylow2In T₀ X := isSylow2In_of_eq_sup_oddCoreOf hJ₀X hX hT₀
  obtain ⟨TL, hTL, -⟩ := IsSylow2In.exists_ge (P := L) (T := ⊥) IsPGroup.of_bot bot_le
  have hcard : Nat.card T₀ = Nat.card TL := by
    rw [hΩ.natCard_isSylow2In hJ₀ hT₀, hΩ.natCard_isSylow2In hL hTL]
  have hTLX : IsSylow2In TL X := hTX.of_natCard_le hTL.2.1 (hTL.1.trans hLX) hcard.le
  obtain ⟨x, hxX, hxT⟩ := Thompson.exists_conj_of_isSylow2In hTX hTLX
  exact ⟨x, hxX, hΩ.eq_of_le_of_le (hΩ.conjInvariant x J₀ hJ₀) hL hTL.2.1 (by omega)
    (hxT ▸ conjSub_mono (n := x) hT₀.1) hTL.1⟩

theorem mul_inv_mem_oddCoreOf_of_mem_omegaNbr (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {L : Subgroup G}
    (hL : L ∈ omegaNbr Ω K) {y : G} (hy : IsUniqueInvolution L y) :
    y * t⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hJX : J ≤ omegaNbrGen Ω K :=
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have hLX : L ≤ omegaNbrGen Ω K :=
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) L hL
  obtain ⟨x, hxX, hLx⟩ := exists_conj_of_le_of_eq_sup_oddCoreOf hp hΩ hs.hJ.1 hL.1 hJX hLX hX
  have hyx : y = x * t * x⁻¹ := hy.eq (hLx ▸ hs.ht.conj x)
  have hN : J ≤ Subgroup.normalizer (oddCoreOf (omegaNbrGen Ω K) : Set G) := fun w hw =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hJX hw))
  have hxX' : x ∈ oddCoreOf (omegaNbrGen Ω K) ⊔ J := by
    rw [sup_comm, ← hX]
    exact hxX
  obtain ⟨o, ho, j, hj, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hN hxX'
  have hjt : j * t * j⁻¹ = t := hs.ht.conj_eq (conjSub_eq_self_of_mem hj)
  have htn := hN hs.ht.mem
  have h1 : t * o⁻¹ * t⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) :=
    (Subgroup.mem_normalizer_iff.mp htn o⁻¹).mp ((oddCoreOf (omegaNbrGen Ω K)).inv_mem ho)
  have h2 : y * t⁻¹ = o * (t * o⁻¹ * t⁻¹) := by
    rw [hyx]
    calc o * j * t * (o * j)⁻¹ * t⁻¹ = o * (j * t * j⁻¹) * o⁻¹ * t⁻¹ := by group
      _ = o * (t * o⁻¹ * t⁻¹) := by rw [hjt]; group
  rw [h2]
  exact (oddCoreOf (omegaNbrGen Ω K)).mul_mem ho h1

theorem conj_zt_mul_inv_mem_oddCoreOf (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {y : G}
    (hy : y ∈ Subgroup.centralizer ({z} : Set G)) :
    y * (z * t) * y⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hyN : y ∈ Subgroup.normalizer (K : Set G) :=
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz hy
  have hyK : conjSub y K = K := mem_normalizer_iff_conjSub_eq.mp hyN
  have hJy : conjSub y J ∈ omegaNbr Ω K := hyK ▸ omegaNbr_conj hΩ.conjInvariant hs.hJ y
  have h1 := mul_inv_mem_oddCoreOf_of_mem_omegaNbr hs hX hJy (hs.ht.conj y)
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hy
    calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [this]
      _ = z := by group
  have hzK : conjSub z K = K := conjSub_eq_self_of_mem hs.hz.mem
  have hzX : z ∈ Subgroup.normalizer ((omegaNbrGen Ω K : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (s26_conjSub_omegaNbrGen hΩ hzK)
  have hzN := mem_normalizer_oddCore_of_mem_normalizer hzX
  have h2 : z * (y * t * y⁻¹ * t⁻¹) * z⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) :=
    (Subgroup.mem_normalizer_iff.mp hzN _).mp h1
  have e : y * (z * t) * y⁻¹ * (z * t)⁻¹ = z * (y * t * y⁻¹ * t⁻¹) * z⁻¹ := by
    calc y * (z * t) * y⁻¹ * (z * t)⁻¹ = (y * z * y⁻¹) * (y * t * y⁻¹) * t⁻¹ * z⁻¹ := by group
      _ = z * (y * t * y⁻¹ * t⁻¹) * z⁻¹ := by rw [hyz]; group
  rw [e]
  exact h2

theorem omegaNbrGen_conjSub (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (g : G) :
    omegaNbrGen Ω (conjSub g K) = conjSub g (omegaNbrGen Ω K) := by
  apply le_antisymm
  · refine iSup₂_le fun M hM => ?_
    have h1 : conjSub g⁻¹ M ∈ omegaNbr Ω K := by
      have := omegaNbr_conj hΩ.conjInvariant hM g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have h2 : conjSub g⁻¹ M ≤ omegaNbrGen Ω K :=
      le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) _ h1
    have := conjSub_mono (n := g) h2
    rwa [conjSub_conjSub_inv] at this
  · show (omegaNbrGen Ω K).map (MulAut.conj g).toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun M' hM' => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω (conjSub g K)) => N) (conjSub g M')
      (omegaNbr_conj hΩ.conjInvariant hM' g)

theorem Std8.symm' (hs : Std8 p f Ω K J S R T W z t) : Std8 p f Ω J K S T R W t z := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  refine ⟨⟨hp, hq, hΩ, hs.stand.below, hs.stand.ih, hs.stand.aEmpty, hs.hJ.1, ?_,
    hs.stand.gen⟩, ?_, hs.ht, ?_, hs.hz, hs.hT, hs.hR, hs.hW⟩
  · intro L hL
    obtain ⟨g, hg⟩ := hs.stand.trans L hL
    obtain ⟨g₀, hg₀⟩ := hs.stand.trans J hs.hJ.1
    refine ⟨g * g₀⁻¹, ?_⟩
    rw [← hg₀, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one, hg]
  · exact fun K' hK' => T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hs.hJ.1 K' hK'
  · exact T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hs.stand.mem hs.hJ.1 hs.hJ

theorem eq_sup_oddCoreOf_swap (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) :
    omegaNbrGen Ω J = K ⊔ oddCoreOf (omegaNbrGen Ω J) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨m, hm⟩ := hs.stand.trans J hs.hJ.1
  have hXJ : omegaNbrGen Ω J = conjSub m (omegaNbrGen Ω K) := by
    rw [← hm]
    exact omegaNbrGen_conjSub hΩ m
  have hJ' : omegaNbrGen Ω J = conjSub m J ⊔ oddCoreOf (omegaNbrGen Ω J) := by
    rw [hXJ, oddCoreOf_conjSub_eq]
    conv_lhs => rw [hX]
    exact conjSub_sup m _ _
  have hmJ : conjSub m J ∈ omegaNbr Ω J := hm ▸ omegaNbr_conj hΩ.conjInvariant hs.hJ m
  have hKJ : K ∈ omegaNbr Ω J := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hK hs.hJ.1 hs.hJ
  obtain ⟨x, hxX, hxK⟩ := exists_conj_of_le_of_eq_sup_oddCoreOf hp hΩ
    (hΩ.conjInvariant m J hs.hJ.1) hK
    (le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω J) => N) _ hmJ)
    (le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω J) => N) _ hKJ) hJ'
  have hxN : x ∈ Subgroup.normalizer ((omegaNbrGen Ω J : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hxX
  have hxO := mem_normalizer_oddCore_of_mem_normalizer hxN
  have h1 : conjSub x (omegaNbrGen Ω J) = omegaNbrGen Ω J := conjSub_eq_self_of_mem hxX
  have h2 : conjSub x (oddCoreOf (omegaNbrGen Ω J)) = oddCoreOf (omegaNbrGen Ω J) :=
    mem_normalizer_iff_conjSub_eq.mp hxO
  calc omegaNbrGen Ω J = conjSub x (omegaNbrGen Ω J) := h1.symm
    _ = conjSub x (conjSub m J ⊔ oddCoreOf (omegaNbrGen Ω J)) := by rw [← hJ']
    _ = K ⊔ oddCoreOf (omegaNbrGen Ω J) := by rw [conjSub_sup, h2, hxK]

end Cert

end T8R

end CFSG.ClassicalInvolution.Asc77

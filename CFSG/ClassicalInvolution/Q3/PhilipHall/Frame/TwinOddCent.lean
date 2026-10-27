module

public import CFSG.ClassicalInvolution.Q3.TL4OddKey
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Balance
open CFSG.Assembly.Dichotomy (involutionOddCore)

namespace TwinOdd

variable {G : Type} [Group G]

theorem conj_mem_oddCent (g : G) {t x : G}
    (hx : x ∈ oddCoreImg (Subgroup.centralizer ({t} : Set G))) :
    g * x * g⁻¹ ∈ oddCoreImg (Subgroup.centralizer ({g * t * g⁻¹} : Set G)) := by
  have h := CFSG.Assembly.Dichotomy.involutionOddCore_map (MulAut.conj g) t
  have hmem : (MulAut.conj g) x ∈ (involutionOddCore t).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [h, MulAut.conj_apply] at hmem
  rw [MulAut.conj_apply] at hmem
  exact hmem

theorem card_oddCent_conj (g t : G) :
    Nat.card (oddCoreImg (Subgroup.centralizer ({g * t * g⁻¹} : Set G))) =
      Nat.card (oddCoreImg (Subgroup.centralizer ({t} : Set G))) := by
  have h := CFSG.Assembly.Dichotomy.involutionOddCore_map (MulAut.conj g) t
  rw [MulAut.conj_apply] at h
  change Nat.card (involutionOddCore (g * t * g⁻¹)) = Nat.card (involutionOddCore t)
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj g).injective]

variable [Finite G]

theorem edge_commute {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {M N : Subgroup G}
    (hMN : N ∈ omegaNbr Ω M) {zM zN : G} (hzM : IsUniqueInvolution M zM)
    (hzN : IsUniqueInvolution N zN) : zN * zM = zM * zN := by
  obtain ⟨hNΩ, -, P, hP, hPN, hPM⟩ := hMN
  have hPs : IsSylow2In P N := Q3CL.Sec7.isSylow2In_of_mem_RSet_of_le hΩ hP hNΩ hPN
  have h1 : 1 < Nat.card ↥P := by
    by_contra h
    push Not at h
    obtain ⟨-, Q, hQ, hQnc⟩ := hΩ.omega1 N hNΩ
    have hQP : Nat.card ↥Q = Nat.card ↥P := hΩ.omega3 N hNΩ N hNΩ Q P hQ hPs
    have hQ1 : Nat.card ↥Q ≤ 1 := hQP ▸ h
    have : Subsingleton ↥Q := Finite.card_le_one_iff_subsingleton.mp hQ1
    exact hQnc ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  have h2 : 2 ∣ Nat.card ↥P := by
    rcases hPs.2.1.card_eq_or_dvd with h | h
    · omega
    · exact h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hy1 : (y : G) ≠ 1 := by
    intro h
    have : y = 1 := by ext; simpa using h
    rw [this, orderOf_one] at hy
    norm_num at hy
  have hy2 : (y : G) * y = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy, pow_two] at this
    have h' := congrArg Subtype.val this
    simpa using h'
  have hzP : zN ∈ P := by
    rcases hzN.unique (y : G) (hPN y.2) hy2 with h | h
    · exact absurd h hy1
    · exact h ▸ y.2
  have hN := hPM hzP
  have hconj : IsUniqueInvolution (conjSub zN M) (zN * zM * zN⁻¹) := hzM.conj zN
  rw [conjSub_eq_of_mem_normalizer hN] at hconj
  have := hzM.eq hconj
  calc zN * zM = zN * zM * zN⁻¹ * zN := by group
    _ = zM * zN := by rw [← this]

theorem oddCent_le_of_alpha {zM zN : G} (hcomm : zM ∈ Subgroup.centralizer ({zN} : Set G))
    (hz2 : zM * zM = 1) (hz1 : zM ≠ 1)
    (hα : alphaOf (Subgroup.closure ({zM, zN} : Set G)) = ⊥)
    (hsec : ∀ L : Subgroup (OddQuot zN), CFSG.IsComponent L →
      oddQuotMk zN ⟨zM, hcomm⟩ ∈ Subgroup.normalizer (L : Set (OddQuot zN)) →
      (∃ y ∈ L, oddQuotMk zN ⟨zM, hcomm⟩ * y ≠ y * oddQuotMk zN ⟨zM, hcomm⟩) →
      Q3NM.AutOddFreeOn ↥L (TL4.IsInducedAut L (oddQuotMk zN ⟨zM, hcomm⟩))) :
    oddCoreImg (Subgroup.centralizer ({zM} : Set G)) ≤
      oddCoreImg (Subgroup.centralizer ({zN} : Set G)) := by
  refine TL4.oddCent_le_oddCent_of_moved hcomm hz2 hz1 ?_ hsec
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact TL4.commute_of_alphaOf_eq_bot hα (Subgroup.subset_closure (by simp)) hz1 hn
    (Subgroup.subset_closure (by simp))

end TwinOdd

open TwinOdd

section Main

variable {G : Type} [Group G] [Finite G] {K₀ : Subgroup G} {z₀ : G}

theorem oddCent_eq_bot_of_steps (hO : classicalInvolutionOddCore G = ⊥)
    (hz₀ : IsUniqueInvolution K₀ z₀)
    (hconn : Disconnected.DConnected (CoreAssembly.conjClass K₀))
    (hstep : ∀ M ∈ CoreAssembly.conjClass K₀, ∀ N ∈ omegaNbr (CoreAssembly.conjClass K₀) M,
      ∀ zM zN : G, IsUniqueInvolution M zM → IsUniqueInvolution N zN →
        oddCoreImg (Subgroup.centralizer ({zM} : Set G)) ≤
          oddCoreImg (Subgroup.centralizer ({zN} : Set G))) :
    oddCoreImg (Subgroup.centralizer ({z₀} : Set G)) = ⊥ := by
  set Ω := CoreAssembly.conjClass K₀ with hΩdef
  have hcard : ∀ M ∈ Ω, ∀ zM : G, IsUniqueInvolution M zM →
      Nat.card (oddCoreImg (Subgroup.centralizer ({zM} : Set G))) =
        Nat.card (oddCoreImg (Subgroup.centralizer ({z₀} : Set G))) := by
    rintro M ⟨g, rfl⟩ zM hzM
    rw [← (hz₀.conj g).eq hzM, card_oddCent_conj]
  have heq : ∀ M ∈ Ω, ∀ N ∈ omegaNbr Ω M, ∀ zM zN : G, IsUniqueInvolution M zM →
      IsUniqueInvolution N zN →
        oddCoreImg (Subgroup.centralizer ({zN} : Set G)) =
          oddCoreImg (Subgroup.centralizer ({zM} : Set G)) := by
    intro M hM N hN zM zN hzM hzN
    symm
    refine Subgroup.eq_of_le_of_card_ge (hstep M hM N hN zM zN hzM hzN) ?_
    rw [hcard M hM zM hzM, hcard N hN.1 zN hzN]
  have hK : K₀ ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hall : ∀ L : Subgroup G, Relation.ReflTransGen (fun M N : Subgroup G =>
      N ∈ Ω ∧ Disconnected.dAdj Ω M N) K₀ L →
      L ∈ Ω ∧ ∀ z : G, IsUniqueInvolution L z →
        oddCoreImg (Subgroup.centralizer ({z} : Set G)) =
          oddCoreImg (Subgroup.centralizer ({z₀} : Set G)) := by
    intro L hpath
    induction hpath with
    | refl => exact ⟨hK, fun z hz => by rw [hz₀.eq hz]⟩
    | @tail M N _ hMN ih =>
      obtain ⟨hMΩ, hM⟩ := ih
      obtain ⟨hNΩ, hadj⟩ := hMN
      refine ⟨hNΩ, fun z hz => ?_⟩
      obtain ⟨g, rfl⟩ := hMΩ
      have hzM : IsUniqueInvolution (conjSub g K₀) (g * z₀ * g⁻¹) := hz₀.conj g
      rcases hadj with h | h
      · rw [heq _ ⟨g, rfl⟩ N h _ z hzM hz, hM _ hzM]
      · rw [← heq N hNΩ _ h z _ hz hzM, hM _ hzM]
  have hconj : ∀ g : G, oddCoreImg (Subgroup.centralizer ({g * z₀ * g⁻¹} : Set G)) =
      oddCoreImg (Subgroup.centralizer ({z₀} : Set G)) := by
    intro g
    have hgK : conjSub g K₀ ∈ Ω := ⟨g, rfl⟩
    exact (hall _ (hconn _ hK _ hgK)).2 _ (hz₀.conj g)
  have hnorm : (oddCoreImg (Subgroup.centralizer ({z₀} : Set G))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [← hconj g]
    exact conj_mem_oddCent g hx
  have hle : oddCoreImg (Subgroup.centralizer ({z₀} : Set G)) ≤ classicalInvolutionOddCore G :=
    le_sSup ⟨hnorm, odd_natCard_oddCoreImg _⟩
  rw [hO] at hle
  exact le_bot_iff.mp hle

theorem oddCent_eq_bot_of_alpha (hΩ : HypOmegaGen (CoreAssembly.conjClass K₀))
    (hO : classicalInvolutionOddCore G = ⊥) (hz₀ : IsUniqueInvolution K₀ z₀)
    (hconn : Disconnected.DConnected (CoreAssembly.conjClass K₀))
    (hα : ∀ M ∈ CoreAssembly.conjClass K₀, ∀ N ∈ omegaNbr (CoreAssembly.conjClass K₀) M,
      ∀ zM zN : G, IsUniqueInvolution M zM → IsUniqueInvolution N zN → zM ≠ zN →
        alphaOf (Subgroup.closure ({zM, zN} : Set G)) = ⊥)
    (hsec : ∀ M ∈ CoreAssembly.conjClass K₀, ∀ N ∈ omegaNbr (CoreAssembly.conjClass K₀) M,
      ∀ zM zN : G, IsUniqueInvolution M zM → IsUniqueInvolution N zN → zM ≠ zN →
        ∀ hcomm : zM ∈ Subgroup.centralizer ({zN} : Set G),
        ∀ L : Subgroup (OddQuot zN), CFSG.IsComponent L →
          oddQuotMk zN ⟨zM, hcomm⟩ ∈ Subgroup.normalizer (L : Set (OddQuot zN)) →
          (∃ y ∈ L, oddQuotMk zN ⟨zM, hcomm⟩ * y ≠ y * oddQuotMk zN ⟨zM, hcomm⟩) →
          Q3NM.AutOddFreeOn ↥L (TL4.IsInducedAut L (oddQuotMk zN ⟨zM, hcomm⟩))) :
    oddCoreImg (Subgroup.centralizer ({z₀} : Set G)) = ⊥ := by
  refine oddCent_eq_bot_of_steps hO hz₀ hconn fun M hM N hN zM zN hzM hzN => ?_
  by_cases he : zM = zN
  · rw [he]
  · have hc := edge_commute hΩ hN hzM hzN
    have hcomm : zM ∈ Subgroup.centralizer ({zN} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hc.symm
    exact oddCent_le_of_alpha hcomm hzM.sq hzM.ne_one (hα M hM N hN zM zN hzM hzN he)
      (hsec M hM N hN zM zN hzM hzN he hcomm)


theorem isPGroup_of_oddCent {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hθ : oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥)
    (h2 : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) : IsPGroup 2 ↥K := by
  have hle : Balance.oddCoreIn K ≤ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
    Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_of_hypOmegaGen hΩ hK hz)
  have hbot : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥ := hθ
  rw [hbot, le_bot_iff] at hle
  have hcore : classicalInvolutionOddCore ↥K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hle
  exact h2.of_equiv ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot)

theorem isPGroup_conjClass_of_oddCent (hΩ : HypOmegaGen (CoreAssembly.conjClass K₀))
    (hz₀ : IsUniqueInvolution K₀ z₀)
    (hθ : oddCoreImg (Subgroup.centralizer ({z₀} : Set G)) = ⊥)
    (h2 : IsPGroup 2 (↥K₀ ⧸ classicalInvolutionOddCore ↥K₀)) :
    ∀ J ∈ CoreAssembly.conjClass K₀, IsPGroup 2 ↥J := by
  have hK := isPGroup_of_oddCent hΩ (CoreAssembly.mem_conjClass_self K₀) hz₀ hθ h2
  rintro _ ⟨g, rfl⟩
  exact isPGroup_conjSub g hK

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIOmegaStep
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactA

public section

namespace CFSG.ClassicalInvolution.Asc77.AscAET

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_conj_fixed_involution_odd {N₀ T : Subgroup G} {u : G} (hT : IsPGroup 2 T)
    (huN : u ∈ N₀) (hu : u * u = 1) (hTN : T ≤ Subgroup.normalizer (N₀ : Set G))
    (hcomm : ∀ x ∈ T, ⁅x, u⁆ ∈ oddCoreOf N₀) :
    ∃ q ∈ oddCoreOf N₀, ∀ x ∈ T, x * (q * u * q⁻¹) * x⁻¹ = q * u * q⁻¹ := by
  set O := oddCoreOf N₀ with hO
  have hOodd : Odd (Nat.card O) := oddCoreOf_odd_natCard N₀
  have huN' : u ∈ Subgroup.normalizer (N₀ : Set G) := Subgroup.le_normalizer huN
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hAN : ∀ a ∈ T, ∀ n ∈ O, a * n * a⁻¹ ∈ O := fun a ha n hn =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (hTN ha) hn
  have hx : ∀ a ∈ T, u⁻¹ * (a * u * a⁻¹) ∈ O := by
    intro a ha
    have h1 := mem_normalizer_oddCoreOf_of_mem_normalizer
      ((Subgroup.normalizer _).inv_mem huN') (hcomm a ha)
    have e : u⁻¹ * (a * u * a⁻¹) = u⁻¹ * ⁅a, u⁆ * u⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h1
  obtain ⟨n, hn, hfix⟩ := Balance.Bootstrap.exists_fixed_mem_coset_of_isPGroup hT hOodd hAN hx
  set h : G := u * n with hh
  have hhh : h * h ∈ O := by
    have e : h * h = (u * n * u⁻¹) * n := by rw [hh, hui]; group
    rw [e]
    exact O.mul_mem (mem_normalizer_oddCoreOf_of_mem_normalizer huN' hn) hn
  have hkodd : Odd (orderOf (h * h)) :=
    hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hhh)
  obtain ⟨j, hj⟩ := hkodd
  set t'' : G := h ^ orderOf (h * h) with ht''
  have ht''sq : t'' * t'' = 1 := by
    rw [ht'', ← (Commute.refl h).mul_pow]
    exact pow_orderOf_eq_one (h * h)
  have ht''eq : t'' = h * (h * h) ^ j := by
    rw [ht'', hj, pow_succ', pow_mul, sq]
  have hut : u * t'' ∈ O := by
    have huh : u * h = n := by rw [hh, ← mul_assoc, hu, one_mul]
    have : u * t'' = n * (h * h) ^ j := by
      rw [ht''eq, ← mul_assoc, huh]
    rw [this]
    exact O.mul_mem hn (O.pow_mem hhh j)
  have hodd2 : Odd (orderOf (u * t'')) :=
    hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hut)
  obtain ⟨k, hk⟩ := T3Core.exists_conj_of_mul_mem_odd hu ht''sq hodd2
  have hqO : (u * t'') ^ k ∈ O := O.pow_mem hut k
  refine ⟨(u * t'') ^ k, hqO, fun x hxT => ?_⟩
  rw [hk]
  have h1 : x * h * x⁻¹ = h := hfix x hxT
  calc x * t'' * x⁻¹ = x * h ^ orderOf (h * h) * x⁻¹ := rfl
    _ = (x * h * x⁻¹) ^ orderOf (h * h) := conj_pow.symm
    _ = t'' := by rw [h1]

theorem exists_weak_transfer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {M J : Subgroup G} {zM zJ : G} (hM : M ∈ Ω) (hv : AViol Ω M J zM zJ) {L : Subgroup G}
    (hLset : L ∈ omegaOfSet Ω (twinSet Ω M)) {c : G} (hcL : IsUniqueInvolution L c) :
    ∃ (J' : Subgroup G) (zJ' : G), AViol Ω M J' zM zJ' ∧ c ∈ trivialOnQuot M ∧
      c ∈ trivialOnQuot J' := by
  obtain ⟨v, Ms, hVU, hVJ, -, hMsM, htw, hvv⟩ :=
    exists_hexagon_data hp hq hΩ hM hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr hv.no_conj
  have hMT : M ∈ twinSet Ω M := ⟨hM, zM, hv.hzK, hv.hzK⟩
  have hMsT : Ms ∈ twinSet Ω M := by rw [htw]; exact Or.inr rfl
  have hMsΩ : Ms ∈ Ω := hMsT.1
  have hzMs : IsUniqueInvolution Ms zM := isUniqueInvolution_of_mem_twinSet hv.hzK hMsT
  have hzJM : zJ ∈ M ⊔ Ms := mem_sup_of_hexagon hp hΩ hv.hzJ hVU hVJ hvv
  have hLΩ : L ∈ Ω := hLset.1
  have hLnbr : L ∈ omegaNbr Ω M := hLset.2 M hMT
  obtain ⟨-, hLM, T, hTR, hTL, hTN⟩ := id hLnbr
  have hTsyl : IsSylow2In T L :=
    Disconnected.AschTight.Sec7.isSylow2In_of_mem_RSet_of_le hp hΩ hTR hLΩ hTL
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have h8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hp hTR
  have hLMs : L ≠ Ms := (hLset.2 Ms hMsT).2.1
  have hTC : T ≤ Subgroup.centralizer ({zM} : Set G) := fun x hx =>
    mem_centralizer_singleton_of_conj_eq
      (hv.hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hTN hx)))
  have hTMs : T ≤ Subgroup.normalizer (Ms : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hMsΩ hLΩ (Ne.symm hLMs) hzMs hTL hT2 (by omega) hTC
  have hcM : ∀ x ∈ T, ∀ m ∈ M, ⁅x, m⁆ ∈ oddCoreOf M := fun x hx m hm =>
    Thompson.comm_le_oddCore_of_isSylow2In (l6_2 p f) hp hq hΩ hM hLΩ (Ne.symm hLM) hv.hzK hcL
      hTsyl hTC (Subgroup.commutator_mem_commutator hx hm)
  have hcMs : ∀ x ∈ T, ∀ m ∈ Ms, ⁅x, m⁆ ∈ oddCoreOf Ms := fun x hx m hm =>
    Thompson.comm_le_oddCore_of_isSylow2In (l6_2 p f) hp hq hΩ hMsΩ hLΩ (Ne.symm hLMs) hzMs hcL
      hTsyl hTC (Subgroup.commutator_mem_commutator hx hm)
  have hMsN : Ms ≤ Subgroup.normalizer (M : Set G) :=
    hΩ.le_normalizer_of_twin hMsΩ hM hMsM hzMs hv.hzK
  have hMN : M ≤ Subgroup.normalizer (Ms : Set G) :=
    hΩ.le_normalizer_of_twin hM hMsΩ (Ne.symm hMsM) hv.hzK hzMs
  have hcN := commutator_mem_oddCore_sup hMsN hMN hcM hcMs
  obtain ⟨q, hqO, hqfix⟩ := exists_conj_fixed_involution_odd (N₀ := M ⊔ Ms) hT2 hzJM hv.hzJ.sq
    (fun x hx => T3CII.mem_normalizer_sup (hTN hx) (hTMs hx)) (fun x hx => hcN x hx zJ hzJM)
  have hqMs : q ∈ M ⊔ Ms := Balance.oddCoreIn_le _ hqO
  have hqN : q ∈ Subgroup.normalizer (M : Set G) :=
    (sup_le Subgroup.le_normalizer hMsN) hqMs
  have hconjM : conjSub q M = M := mem_normalizer_iff_conjSub_eq.mp hqN
  have hzq : q * zM * q⁻¹ = zM := by
    have h1 := hv.hzK.conj q
    rw [hconjM] at h1
    exact h1.eq hv.hzK
  have hv' : AViol Ω M (conjSub q J) zM (q * zJ * q⁻¹) := by
    have h := hv.conj hΩ.conjInvariant q
    rw [hconjM, hzq] at h
    exact h
  have hTC' : T ≤ Subgroup.centralizer ({q * zJ * q⁻¹} : Set G) := fun x hx =>
    mem_centralizer_singleton_of_conj_eq (hqfix x hx)
  have hJ'Ω : conjSub q J ∈ Ω := hv'.mem
  have hLJ' : L ≠ conjSub q J := by
    intro h
    exact hv'.not_nbr (h ▸ hLnbr)
  have hTJ' : T ≤ Subgroup.normalizer ((conjSub q J : Subgroup G) : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hJ'Ω hLΩ (Ne.symm hLJ') hv'.hzJ hTL hT2 (by omega)
      hTC'
  have hcJ' : ∀ x ∈ T, ∀ m ∈ conjSub q J, ⁅x, m⁆ ∈ oddCoreOf (conjSub q J) := fun x hx m hm =>
    Thompson.comm_le_oddCore_of_isSylow2In (l6_2 p f) hp hq hΩ hJ'Ω hLΩ (Ne.symm hLJ') hv'.hzJ hcL
      hTsyl hTC' (Subgroup.commutator_mem_commutator hx hm)
  have hcT : c ∈ T := mem_of_isPGroup hcL hTsyl.1 hT2 (by omega)
  exact ⟨conjSub q J, q * zJ * q⁻¹, hv', ⟨hTN hcT, fun m hm => hcM c hcT m hm⟩,
    ⟨hTJ' hcT, fun m hm => hcJ' c hcT m hm⟩⟩

end CFSG.ClassicalInvolution.Asc77.AscAET

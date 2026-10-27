module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Induction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Statements

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.ProperTwoGeneratedCore.Assembly

theorem IsTwoANine.eq_top_of_normal_of_center_le {J : Type*} [Group J] (hJ : IsTwoANine J)
    {K : Subgroup J} (hK : K.Normal) (hZK : center J ≤ K) (hKZ : ¬ K ≤ center J) : K = ⊤ := by
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv
  have : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  have hKmap : K.map (proj e) = ⊤ := by
    have : (K.map (proj e)).Normal := hK.map (proj e) (proj_surjective e)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map (proj e)) with h | h
    · rw [Subgroup.map_eq_bot_iff, ker_proj] at h
      exact absurd h hKZ
    · exact h
  refine eq_top_iff.mpr fun j _ => ?_
  obtain ⟨k, hk, hkj⟩ : proj e j ∈ K.map (proj e) := by
    rw [hKmap]
    exact mem_top _
  have h := K.mul_mem hk (hZK ((proj_eq_proj_iff e).mp hkj))
  rwa [mul_inv_cancel_left] at h

namespace MinimalCounterexample

variable {X : Type} [Group X] [Finite X] {S : Sylow 2 X} {t : X}
  (hX : MinimalCounterexample X S t)
include hX

theorem ne_one : t ≠ 1 := fun h => by
  have h2 := hX.central.2.1
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem isTwoANine_centralizer : IsTwoANine (centralizer ({t} : Set X)) := by
  have h : CFSG.pPrimeCore 2 (centralizer ({t} : Set X)) = ⊥ := by
    have h0 := hX.oddCentralizer_eq_bot
    rwa [oddCentralizer,
      Subgroup.map_eq_bot_iff_of_injective _ (centralizer ({t} : Set X)).subtype_injective] at h0
  exact hX.twoANine.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot)

theorem zbar_centralizer_eq : zbar (centralizer ({t} : Set X)) = escapingSelf t := by
  refine (hX.isTwoANine_centralizer.eq_zbar_of_mem_center ?_ fun h => hX.ne_one ?_).symm
  · exact Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  · exact congrArg Subtype.val h

theorem normalizer_sylow_le_centralizer :
    normalizer ((S : Subgroup X) : Set X) ≤ centralizer ({t} : Set X) := by
  intro x hx
  have hM := hX.isTwoANine_centralizer
  have hSM := le_centralizer_of_isCentralInvolution hX.central
  have hvS : x * t * x⁻¹ ∈ (S : Subgroup X) :=
    (Subgroup.mem_normalizer_iff.mp hx t).mp hX.central.1
  have hvT : (⟨x * t * x⁻¹, hSM hvS⟩ : centralizer ({t} : Set X)) ∈
      ((S.subtype hSM : Sylow 2 _) : Subgroup (centralizer ({t} : Set X))) := by
    rw [Sylow.coe_subtype]
    exact Subgroup.mem_subgroupOf.mpr hvS
  have hcen := (hM.mem_center_sylow_iff (S.subtype hSM) hvT).mp
    (Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subtype.ext ?_))
  · rcases hM.mem_center_iff.mp hcen with h | h
    · exfalso
      have h1 : x * t * x⁻¹ = 1 := congrArg Subtype.val h
      rw [mul_inv_eq_one, mul_eq_left] at h1
      exact hX.ne_one h1
    · rw [hX.zbar_centralizer_eq] at h
      have h1 : x * t * x⁻¹ = t := congrArg Subtype.val h
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * t = x * t * x⁻¹ * x := by group
        _ = t * x := by rw [h1]
  ·
    have hgS : (((g : centralizer ({t} : Set X)) : X)) ∈ (S : Subgroup X) := g.2
    set s : X := ((g : centralizer ({t} : Set X)) : X)
    have hs' : x⁻¹ * s * x ∈ (S : Subgroup X) := by
      have h := (Subgroup.mem_normalizer_iff.mp ((normalizer _).inv_mem hx) s).mp hgS
      rwa [inv_inv] at h
    have hst := hX.central.2.2 _ hs'
    change s * (x * t * x⁻¹) = x * t * x⁻¹ * s
    calc s * (x * t * x⁻¹) = x * ((x⁻¹ * s * x) * t) * x⁻¹ := by group
      _ = x * (t * (x⁻¹ * s * x)) * x⁻¹ := by rw [hst]
      _ = x * t * x⁻¹ * s := by group

theorem isSimpleGroup : IsSimpleGroup X := by
  have hM := hX.isTwoANine_centralizer
  obtain ⟨g, hgS, hgt⟩ := hX.exists_conj
  have : Nontrivial X := ⟨⟨t, 1, hX.ne_one⟩⟩
  refine ⟨fun N hN => ?_⟩
  by_cases hN1 : N = ⊥
  · exact Or.inl hN1
  right
  have heven : 2 ∣ Nat.card N := by
    by_contra hodd
    have hle := le_pPrimeCore_of_normal hN
      (Nat.not_even_iff_odd.mp fun h => hodd (even_iff_two_dvd.mp h))
    rw [hX.oddCore_eq_bot, le_bot_iff] at hle
    exact hN1 hle
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 heven
  obtain ⟨c, hc⟩ := isConj_iff.mp (hX.isConj (by rwa [Subgroup.orderOf_coe] : orderOf (x : X) = 2))
  have htN : t ∈ N := by
    have h := hN.conj_mem _ x.2 c⁻¹
    rwa [← hc, inv_inv, show c⁻¹ * (c * t * c⁻¹) * c = t by group] at h
  have huN : g⁻¹ * t * g ∈ N := by
    have h := hN.conj_mem t htN g⁻¹
    rwa [inv_inv] at h
  have hSM := le_centralizer_of_isCentralInvolution hX.central
  have hMN : centralizer ({t} : Set X) ≤ N := by
    refine Subgroup.subgroupOf_eq_top.mp (hM.eq_top_of_normal_of_center_le (hN.subgroupOf _)
      (fun z hz => ?_) fun hle => ?_)
    · rcases hM.mem_center_iff.mp hz with rfl | rfl
      · exact one_mem _
      · rw [hX.zbar_centralizer_eq]
        exact Subgroup.mem_subgroupOf.mpr htN
    · have hu := hle (Subgroup.mem_subgroupOf.mpr huN : (⟨g⁻¹ * t * g, hSM hgS⟩ :
        centralizer ({t} : Set X)) ∈ N.subgroupOf _)
      rcases hM.mem_center_iff.mp hu with h | h
      · have h1 : g⁻¹ * t * g = 1 := congrArg Subtype.val h
        exact hX.ne_one (by
          calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
            _ = 1 := by rw [h1]; group)
      · rw [hX.zbar_centralizer_eq] at h
        exact hgt (congrArg Subtype.val h)
  have hfr := Sylow.normalizer_sup_eq_top' S (hSM.trans hMN)
  rw [eq_top_iff, ← hfr]
  exact sup_le (hX.normalizer_sylow_le_centralizer.trans hMN) le_rfl

theorem false_of_janko (hJ9 : NoSimpleCentralizerTwoANine) : False := by
  have hM := hX.isTwoANine_centralizer
  obtain ⟨g, -, hgt⟩ := hX.exists_conj
  refine hJ9 X hX.isSimpleGroup ⟨t, g, fun h => hgt ?_⟩ t hX.central.2.1 hM.perfect
    hM.card_center hM.nonempty_mulEquiv
  rw [mul_assoc, h, inv_mul_cancel_left]

end MinimalCounterexample

theorem isolatedFor_of_forall_lt (hJ9 : NoSimpleCentralizerTwoANine) {X : Type} [Group X]
    [Finite X] (IH : ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < Nat.card X → IsolatedFor Y) :
    IsolatedFor X := by
  intro S t ht hJ g hg
  by_contra hgt
  by_cases hO : CFSG.pPrimeCore 2 X = ⊥
  · refine MinimalCounterexample.false_of_janko ⟨ht, hJ, ⟨g, hg, hgt⟩, hO, fun H hH => IH H ?_⟩ hJ9
    rw [← Subgroup.card_top (G := X)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hH)
  · exact hgt (conj_eq_of_quotient odd_card_pPrimeCore_two S ht hJ
      (IH _ (card_quotient_lt hO)) g hg)

theorem isolatedFor_of_janko (hJ9 : NoSimpleCentralizerTwoANine) (X : Type) [Group X]
    [Finite X] : IsolatedFor X := by
  suffices h : ∀ n : ℕ, ∀ (X : Type) [Group X] [Finite X], Nat.card X = n → IsolatedFor X from
    h _ X rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ hX
    exact isolatedFor_of_forall_lt hJ9 fun Y _ _ hY => ih _ (hX ▸ hY) Y rfl

theorem twoANineCentralizerIsolated_of_janko (hJ9 : NoSimpleCentralizerTwoANine) :
    TwoANineCentralizerIsolated := fun X _ _ S t ht hperf hcard he =>
  isolatedFor_of_janko hJ9 X S t ht ⟨hperf, hcard, he⟩

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

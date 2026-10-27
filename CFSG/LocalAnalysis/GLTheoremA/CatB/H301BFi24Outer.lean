module

public import CFSG.Sporadic.FischerOddCore.Fi24R2Comp
public import Certificates.Certificate15028
import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoB
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi24
public import Certificates.Data.Fi24Rank.KCheck

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Open
open CFSG.Sporadic.Fi24 (R J JR jR tR range_jR index_JR eq_jR_or jR_mem_JR jR_injective jR_smul
  jR_comm_tR)
open CFSG.Sporadic.FischerOddCore (fi24R2 fi24R2_mem_M fi24R2_ne_one fi24C fi24K card_fi24K
  fi24FPt fi24FPt_injective fi24R2_smul_fi24FPt exists_fi24FPt exists_famHom)
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime (fi24Rho fi24Rho_spec
  fi24Rho_range_card fi24Rho_eq_one_iff not_mem_fi24K_of_tR)
open CFSG.LocalAnalysis.GLTheoremA.H1017 (k_hside k_A_mem k_G_mem kRank_parts fi24R2_mul_self)
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24Side (side_conj apply_eq_of_uniqAt iotaP iotaP_mem)
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative (kRA kUniqOK)
open CFSG.Monster.B.Co2 (allLt_iff)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

private theorem exists_outer_commute {G : Type*} [Group G] [Finite G] {N E T : Subgroup G}
    (hN : N.index = 2) (hEN : E ≤ N) (hE : IsPGroup 3 E) (hT : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set G)) {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀N : t₀ ∉ N) :
    ∃ t ∈ T, t ∉ N ∧ ∀ e ∈ E, e * t = t * e := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Type _ := {x : G // x ∈ T ∧ x ∉ N}
  have hcl : ∀ (e : E) (x : S), (e : G) * x * (e : G)⁻¹ ∈ T ∧ (e : G) * x * (e : G)⁻¹ ∉ N :=
    fun e x => ⟨(Subgroup.mem_normalizer_iff.1 (hET e.2) x).1 x.2.1, fun h => x.2.2 (by
      have h' := N.mul_mem (N.mul_mem (N.inv_mem (hEN e.2)) h) (hEN e.2)
      rwa [show (e : G)⁻¹ * ((e : G) * x * (e : G)⁻¹) * e = x by group] at h')⟩
  let _ : MulAction E S :=
    { smul := fun e x => ⟨(e : G) * x * (e : G)⁻¹, hcl e x⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : E) : G) * (x : G) * ((1 : E) : G)⁻¹ = x
        simp)
      mul_smul := fun e f x => Subtype.ext (by
        show ((e * f : E) : G) * (x : G) * ((e * f : E) : G)⁻¹ =
          (e : G) * ((f : G) * (x : G) * (f : G)⁻¹) * (e : G)⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card S = Nat.card ↥(T ⊓ N) := Nat.card_congr
    { toFun := fun x => ⟨t₀⁻¹ * x, Subgroup.mem_inf.2 ⟨T.mul_mem (T.inv_mem ht₀) x.2.1,
        (Subgroup.mul_mem_iff_of_index_two hN).2
          (iff_of_false (fun h => ht₀N (by simpa using N.inv_mem h)) x.2.2)⟩⟩
      invFun := fun y => ⟨t₀ * y, T.mul_mem ht₀ (Subgroup.mem_inf.1 y.2).1, fun h =>
        ht₀N (((Subgroup.mul_mem_iff_of_index_two hN).1 h).2 (Subgroup.mem_inf.1 y.2).2)⟩
      left_inv := fun x => Subtype.ext (mul_inv_cancel_left t₀ x)
      right_inv := fun y => Subtype.ext (inv_mul_cancel_left t₀ y) }
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hT.to_le inf_le_left : IsPGroup 2 ↥(T ⊓ N))
  have hndvd : ¬ 3 ∣ Nat.card S := fun h => by
    rw [hcard, hk] at h
    exact absurd (Nat.le_of_dvd (by norm_num) (Nat.prime_three.dvd_of_dvd_pow h)) (by norm_num)
  obtain ⟨x, hx⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card S hndvd
  refine ⟨x, x.2.1, x.2.2, fun e he => mul_inv_eq_iff_eq_mul.1 ?_⟩
  exact congrArg Subtype.val (hx ⟨e, he⟩)


theorem le_range_jR_of_elemAbelian {E T : Subgroup R} (hEJ : E ≤ jR.range)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 5)
    (hEz : E ≤ Subgroup.centralizer ({jR fi24R2} : Set R)) (hT : IsPGroup 2 T)
    (hTz : T ≤ Subgroup.centralizer ({jR fi24R2} : Set R))
    (hET : E ≤ Subgroup.normalizer (T : Set R)) : T ≤ jR.range := by
  intro t₀ ht₀
  by_contra ht₀J
  rw [range_jR] at ht₀J
  obtain ⟨t, htT, htJ, htE⟩ := exists_outer_commute index_JR (range_jR ▸ hEJ) hE.isPGroup hT
    hET ht₀ ht₀J
  set Z : Subgroup R := Subgroup.centralizer ({jR fi24R2} : Set R) with hZ
  have hZC : ∀ c : J, jR c ∈ Z → c ∈ fi24C := fun c h => by
    have h' := Subgroup.mem_centralizer_singleton_iff.1 h
    rw [← map_mul, ← map_mul] at h'
    exact Subgroup.mem_centralizer_singleton_iff.2 (jR_injective h')
  have htRZ : tR ∈ Z :=
    Subgroup.mem_centralizer_singleton_iff.2 (jR_comm_tR fi24R2_mem_M).symm
  obtain ⟨g, rfl | rfl⟩ := eq_jR_or t
  · exact htJ (jR_mem_JR g)
  have hgZ : jR g ∈ Z := by
    have h := Z.mul_mem (hTz htT) (Z.inv_mem htRZ)
    rwa [mul_inv_cancel_right] at h
  obtain ⟨ρR, hρR⟩ := exists_famHom ((MulAction.toPermHom R (Fin 306936)).comp Z.subtype)
    fi24FPt_injective fun c j => exists_fi24FPt (by
      show fi24R2 • ((c : R) • fi24FPt j) = (c : R) • fi24FPt j
      rw [← jR_smul, smul_smul, ← Subgroup.mem_centralizer_singleton_iff.1 c.2, mul_smul,
        jR_smul, fi24R2_smul_fi24FPt])
  have hρR' : ∀ (c : Z) j, fi24FPt (ρR c j) = (c : R) • fi24FPt j := hρR
  have hρJ : ∀ (c : J) (hc : c ∈ fi24C) (h : jR c ∈ Z), ρR ⟨jR c, h⟩ = fi24Rho ⟨c, hc⟩ :=
    fun c hc h => Equiv.ext fun j => fi24FPt_injective ((hρR' _ j).trans
      ((jR_smul c _).trans (fi24Rho_spec ⟨c, hc⟩ j).symm))
  have hEZ : ∀ e : Z, (e : R) ∈ E → ∃ c : J, ∃ hc : c ∈ fi24C,
      jR c = e ∧ ρR e = fi24Rho ⟨c, hc⟩ := by
    rintro ⟨x, hz⟩ (he : x ∈ E)
    obtain ⟨c, rfl⟩ := hEJ he
    exact ⟨c, hZC c hz, rfl, hρJ c _ hz⟩
  have hEK : (E.subgroupOf Z).map ρR ≤ fi24K := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨c, hc, -, hρ⟩ := hEZ e (Subgroup.mem_subgroupOf.1 he)
    rw [hρ, ← fi24Rho_range_card.1]
    exact ⟨_, rfl⟩
  have hinj : Function.Injective (ρR.comp (E.subgroupOf Z).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨c, hc, hce, hρ⟩ := hEZ (x : Z) (Subgroup.mem_subgroupOf.1 x.2)
    have hx' : fi24Rho ⟨c, hc⟩ = 1 := by
      rw [← hρ]
      exact hx
    rcases (fi24Rho_eq_one_iff _).1 hx' with h1 | h1
    · have h : ((x : Z) : R) = 1 := by
        rw [← hce, show c = 1 from congrArg Subtype.val h1, map_one]
      exact Subtype.ext (Subtype.ext h)
    · have h3 : c ^ 3 = 1 := jR_injective (by
        rw [map_pow, hce, map_one]
        exact hE.2 _ (Subgroup.mem_subgroupOf.1 x.2))
      rw [show c = fi24R2 from congrArg Subtype.val h1, pow_succ, pow_two, fi24R2_mul_self,
        one_mul] at h3
      exact absurd h3 fi24R2_ne_one
  have hE₁c : Nat.card (((E.subgroupOf Z).map ρR).subgroupOf fi24K) = 3 ^ 5 := by
    have e1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at e1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, ← e1,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEz).toEquiv, hEc]
  obtain ⟨κ, hκ⟩ : ∃ κ : Equiv.Perm (Fin 504), ∀ i < 243,
      κ * iotaP 504 (kRA ()) i * κ⁻¹ ∈ (E.subgroupOf Z).map ρR := by
    obtain ⟨k, hk⟩ := (side_conj (m := 2) fi24K k_hside (fun k hk => k_A_mem hk)
      (fun l hl => k_G_mem hl) (by norm_num) (by rw [card_fi24K]; norm_num)
      (Or.inl (by norm_num)) _ (((hE.subgroupOf Z).map ρR).subgroupOf fi24K)).2 hE₁c
    refine ⟨(k : Equiv.Perm (Fin 504)), fun i hi => ?_⟩
    let ιX : fi24K := ⟨iotaP 504 (kRA ()) i, iotaP_mem fi24K (fun k hk => k_A_mem hk) i⟩
    exact Subgroup.mem_subgroupOf.1 ((hk (k * ιX * k⁻¹)).2
      ⟨i, hi, congrArg Subtype.val (show k⁻¹ * (k * ιX * k⁻¹) * k = ιX by group)⟩)
  have key : ∀ (n : ℕ) (σ : Equiv.Perm (Fin 504)), σ ^ 2 ^ n = 1 →
      (∀ i < 243, σ * iotaP 504 (kRA ()) i = iotaP 504 (kRA ()) i * σ) → σ = 1 := by
    intro n
    induction n with
    | zero => exact fun σ h _ => by simpa using h
    | succ n ih =>
      intro σ h hσ
      have h2 : σ * σ = 1 := by
        rw [← pow_two]
        refine ih _ (by rw [← pow_mul, ← pow_succ']; exact h) fun i hi => ?_
        exact (Commute.pow_left (show Commute σ (iotaP 504 (kRA ()) i) from hσ i hi) 2).eq
      have hu := kRank_parts.2.2
      simp only [kUniqOK] at hu
      exact Equiv.ext fun q => apply_eq_of_uniqAt k_hside q.2 (allLt_iff.1 hu q q.2) hσ h2
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = ρR ⟨jR g * tR, hTz htT⟩ := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := hT ⟨jR g * tR, htT⟩
  have hτm : τ ^ 2 ^ m = 1 := by
    rw [hτ, ← map_pow, ← map_one ρR]
    exact congrArg ρR (Subtype.ext (by simpa using congrArg Subtype.val hm))
  have hτ1 : κ⁻¹ * τ * κ = 1 := by
    refine key m _ ?_ fun i hi => ?_
    · have h := conj_pow (i := 2 ^ m) (a := κ⁻¹) (b := τ)
      rwa [inv_inv, hτm, mul_one, inv_mul_cancel] at h
    · obtain ⟨e, he, he'⟩ := hκ i hi
      have hc : τ * (κ * iotaP 504 (kRA ()) i * κ⁻¹) = κ * iotaP 504 (kRA ()) i * κ⁻¹ * τ := by
        rw [← he', hτ, ← map_mul, ← map_mul]
        exact congrArg ρR (Subtype.ext (htE _ (Subgroup.mem_subgroupOf.1 he)).symm)
      calc κ⁻¹ * τ * κ * iotaP 504 (kRA ()) i
          = κ⁻¹ * (τ * (κ * iotaP 504 (kRA ()) i * κ⁻¹)) * κ := by group
        _ = κ⁻¹ * (κ * iotaP 504 (kRA ()) i * κ⁻¹ * τ) * κ := by rw [hc]
        _ = iotaP 504 (kRA ()) i * (κ⁻¹ * τ * κ) := by group
  have hτ' : τ = 1 := by
    calc τ = κ * (κ⁻¹ * τ * κ) * κ⁻¹ := by group
      _ = 1 := by rw [hτ1]; group
  rw [hτ, show (⟨jR g * tR, hTz htT⟩ : Z) = ⟨jR g, hgZ⟩ * ⟨tR, htRZ⟩ from rfl, map_mul,
    hρJ g (hZC g hgZ) hgZ] at hτ'
  refine not_mem_fi24K_of_tR Certificates.certificate15028 (fun j => hρR' ⟨tR, htRZ⟩ j) ?_
  rw [eq_inv_of_mul_eq_one_right hτ', ← fi24Rho_range_card.1]
  exact inv_mem ⟨_, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.H301B

end

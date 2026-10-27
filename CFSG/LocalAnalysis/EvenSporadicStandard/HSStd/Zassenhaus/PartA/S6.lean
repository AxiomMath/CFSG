module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S6Wreath
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S6Cpe
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S6A6

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath
open scoped commutatorElement

section Odd

theorem s6_odd_core (X : Type*) [Group X] [Finite X] : Odd (Nat.card (Open.fusionOddCore X)) := by
  have h : Open.fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold Open.fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

variable {G : Type*} [Group G] [Finite G]

theorem s6_eq_one_of_two_power (H : Subgroup G) {f : ↥H} (h2 : ∃ k : ℕ, f ^ (2 ^ k) = 1)
    (hf : oMk H f = 1) : f = 1 := by
  have hmem : f ∈ Open.fusionOddCore ↥H := (QuotientGroup.eq_one_iff f).1 hf
  obtain ⟨k, hk⟩ := h2
  have hd1 : orderOf f ∣ Nat.card (Open.fusionOddCore ↥H) := Subgroup.orderOf_dvd_natCard _ hmem
  have hd2 : orderOf f ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Open.fusionOddCore ↥H)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 (s6_odd_core ↥H))
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd2 hd1)

end Odd

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem s6_CF_card (a : PA5 L t E z) :
    Nat.card ↥(Open.pCoreOf 2 (Cen a.ub) ⊓ Cen a.y) ≤ (if a.dcase = DCase.d8 then 4 else 2) := by
  classical
  set C : Subgroup G := Cen a.y with hC
  set F : Subgroup G := Open.pCoreOf 2 (Cen a.ub) with hF
  set X : Subgroup G := F ⊓ Cen a.y with hX
  have hub2 : a.ub * a.ub = 1 := by
    have := pow_orderOf_eq_one a.ub
    rwa [a.ub_ord, pow_two] at this
  have hXC : X ≤ C := inf_le_right
  have hXF2 : ∀ f ∈ X, ∃ k : ℕ, f ^ (2 ^ k) = 1 := fun f hf => s6_pCoreOf_two hf.1
  obtain ⟨σ, hσ, hσb⟩ := a.ub_base
  obtain ⟨i, j, hij, rfl⟩ := hσ
  let ub' : ↥C := ⟨a.ub, a.ub_cy⟩
  have hub'2 : ub' * ub' = 1 := Subtype.ext hub2
  let ψ : ↥X →* Wr2 (Equiv.Perm (Fin 5)) := a.ι.comp ((oMk C).comp (Subgroup.inclusion hXC))
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro f hf
    have h1 : oMk C (Subgroup.inclusion hXC f) = 1 :=
      a.ι_inj (show a.ι (oMk C (Subgroup.inclusion hXC f)) = a.ι 1 by
        rw [map_one]; exact MonoidHom.mem_ker.1 hf)
    obtain ⟨k, hk⟩ := hXF2 f.1 f.2
    have h2 : Subgroup.inclusion hXC f = 1 :=
      s6_eq_one_of_two_power C ⟨k, Subtype.ext (by simpa using hk)⟩ h1
    have h3 : f.1 = 1 := congrArg Subtype.val h2
    exact Subtype.ext h3
  have hcard : Nat.card X = Nat.card ψ.range :=
    Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv
  have hrange : ∀ p q : Equiv.Perm (Fin 5), p ^ 3 = 1 → q ^ 3 = 1 → base p q ∈ a.ι.range := by
    intro p q hp hq
    rcases a.ι_range with h | h
    · rw [h]; trivial
    · rw [h, mem_DE4, sgnProd_base, s6_sign_of_pow_three hp, s6_sign_of_pow_three hq, one_mul]
  have h2 : ∀ x ∈ ψ.range, ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨k, hk⟩ := hXF2 f.1 f.2
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : f ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hQ : ∀ x ∈ ψ.range, x * base (Equiv.swap i j) (Equiv.swap i j) =
      base (Equiv.swap i j) (Equiv.swap i j) * x := by
    rintro _ ⟨f, rfl⟩
    have hfub : f.1 * a.ub = a.ub * f.1 := mem_Cen.1 (s6_pCoreOf_le _ f.2.1)
    have hcomm : (Subgroup.inclusion hXC f) * ub' = ub' * (Subgroup.inclusion hXC f) :=
      Subtype.ext hfub
    rw [← hσb]
    show a.ι (oMk C (Subgroup.inclusion hXC f)) * a.ι (oMk C ub') =
      a.ι (oMk C ub') * a.ι (oMk C (Subgroup.inclusion hXC f))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hcomm]
  have hconj : ∀ p q : Equiv.Perm (Fin 5), p ^ 3 = 1 → q ^ 3 = 1 →
      p * Equiv.swap i j = Equiv.swap i j * p → q * Equiv.swap i j = Equiv.swap i j * q →
      ∀ x ∈ ψ.range, base p q * x * (base p q)⁻¹ ∈ ψ.range := by
    intro p q hp hq hpσ hqσ x hx
    obtain ⟨d, hd⟩ := hrange p q hp hq
    have hdc : d * oMk C ub' = oMk C ub' * d := by
      apply a.ι_inj
      rw [map_mul, map_mul, hd, hσb, base_mul_base, base_mul_base, hpσ, hqσ]
    have hmem : d ∈ Subgroup.centralizer ({QuotientGroup.mk' (Open.fusionOddCore ↥C) ub'} :
        Set (OQuot C)) := mem_centralizer_singleton_iff.2 hdc
    rw [← map_centralizer_eq_of_odd (Open.fusionOddCore ↥C) (s6_odd_core ↥C) hub'2] at hmem
    obtain ⟨c, hc, hcd⟩ := hmem
    have hcub : c.1 * a.ub = a.ub * c.1 := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hc)
    obtain ⟨f, rfl⟩ := hx
    have hcF : c.1 * f.1 * c.1⁻¹ ∈ F := s6_pCoreOf_conj (mem_Cen.2 hcub) f.2.1
    have hcy : c.1 * f.1 * c.1⁻¹ ∈ Cen a.y :=
      (Cen a.y).mul_mem ((Cen a.y).mul_mem c.2 f.2.2) ((Cen a.y).inv_mem c.2)
    refine ⟨⟨c.1 * f.1 * c.1⁻¹, hcF, hcy⟩, ?_⟩
    show a.ι (oMk C (⟨c.1 * f.1 * c.1⁻¹, hcy⟩ : ↥C)) = _
    have : (⟨c.1 * f.1 * c.1⁻¹, hcy⟩ : ↥C) = c * Subgroup.inclusion hXC f * c⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    have hcd' : oMk C c = d := hcd
    rw [hcd', hd]
    rfl
  by_cases hd8 : a.dcase = DCase.d8
  · have h4 : (if a.dcase = DCase.d8 then 4 else 2) = 4 := by simp [hd8]
    rw [h4, hcard]
    exact s6_card_le i j hij ψ.range h2 hQ hconj
  · have h2' : (if a.dcase = DCase.d8 then 4 else 2) = 2 := by simp [hd8]
    rw [h2', hcard]
    have hne : a.ι.range ≠ ⊤ := fun h => hd8 (a.dcase_iff.2 h)
    have hDE : a.ι.range = DE4 := a.ι_range.resolve_left hne
    refine s6_card_le_e4 i j hij ψ.range h2 hQ hconj ?_
    rintro _ ⟨f, rfl⟩
    have : ψ f ∈ a.ι.range := ⟨_, rfl⟩
    rw [hDE] at this
    exact mem_DE4.1 this

theorem s6_Abar_comm_ub (hb : PAB G L t E W z) (a : PA5 L t E z) {g : G} (hg : g ∈ a.Abar) :
    g * a.ub = a.ub * g := by
  have hgL : g ∈ L := (a.Abar_le hg).1
  have hgu' : g * a.u = a.u * g := mem_Cen.1 (a.Abar_le hg).2
  have hgt : g * t = t * g := (mem_centralizer_iff.1 hb.t_cent g hgL)
  rcases a.ub_cases with h | h
  · rw [h]; exact hgu'
  · rw [h]
    calc g * (t * a.u) = (g * t) * a.u := (mul_assoc _ _ _).symm
      _ = t * g * a.u := by rw [hgt]
      _ = t * (g * a.u) := mul_assoc _ _ _
      _ = t * (a.u * g) := by rw [hgu']
      _ = t * a.u * g := (mul_assoc _ _ _).symm

theorem s6_ub_mem (a : PA5 L t E z) : a.ub ∈ Open.pCoreOf 2 (Cen a.ub) := by
  have hub2 : a.ub * a.ub = 1 := by
    have := pow_orderOf_eq_one a.ub
    rwa [a.ub_ord, pow_two] at this
  refine s6_le_pCoreOf (N := zpowers a.ub) (zpowers_le.2 (mem_Cen.2 rfl)) ?_ ?_ (mem_zpowers a.ub)
  · intro g hg n hn
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    have hc : Commute g (a.ub ^ k) := Commute.zpow_right (mem_Cen.1 hg) k
    rw [hc.eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers a.ub) k
  · intro n hn
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    refine ⟨1, ?_⟩
    have : a.ub ^ 2 = 1 := by rw [pow_two, hub2]
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, this, one_zpow]

theorem s6_F_facts (hb : PAB G L t E W z) (a : PA5 L t E z) :
    derivedIn a.Abar ≤ centralizer ((Open.pCoreOf 2 (Cen a.ub) : Subgroup G) : Set G) ∧
      Nat.card ↥(Open.pCoreOf 2 (Cen a.ub)) ≤ (if a.dcase = DCase.d8 then 4 else 2) := by
  classical
  set P : Subgroup G := Cen a.ub with hP
  set F : Subgroup G := Open.pCoreOf 2 P with hF
  have hy3 : orderOf a.y = 3 := a.y_ord
  have hyJ : a.y ∈ derivedIn a.Abar := a.y_J
  obtain ⟨A, hAJ, hyA, hAc, hAab, hA3⟩ := s6_exists_sylow a.eAbar hyJ hy3
  have hJA : derivedIn a.Abar ≤ a.Abar := derivedIn_le _
  have hAP : ∀ g ∈ a.Abar, g ∈ P := fun g hg => mem_Cen.2 (s6_Abar_comm_ub hb a hg)
  have hF2 : ∀ f ∈ F, ∃ k : ℕ, f ^ (2 ^ k) = 1 := fun f hf => s6_pCoreOf_two hf
  have hub1 : a.ub ≠ 1 := by
    intro h
    have := a.ub_ord
    rw [h, orderOf_one] at this
    omega
  have hAn : A ≤ normalizer (F : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => s6_pCoreOf_conj (hAP g (hJA (hAJ hg))) hx, fun hx => ?_⟩
    have hginv : g⁻¹ ∈ P := P.inv_mem (hAP g (hJA (hAJ hg)))
    have := s6_pCoreOf_conj (P := P) hginv hx
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [h2] at this
  have hubA : a.ub ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    exact s6_Abar_comm_ub hb a (hJA (hAJ hh))
  have hCF := s6_CF_card a
  have hCF4 : Nat.card ↥(F ⊓ Cen a.y) ≤ 4 := by
    refine hCF.trans ?_
    split_ifs <;> omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ a' ∈ A, a' ≠ 1 → Nat.card ↥(F ⊓ centralizer ({a'} : Set G)) ≤ 4 := by
    intro a' ha' ha1
    have ha3 : orderOf a' = 3 := orderOf_eq_prime (hA3 a' ha') ha1
    obtain ⟨g, hg, hga⟩ := s6_exists_conj a.eAbar hyJ hy3 (hAJ ha') ha3
    have hgP : g ∈ P := hAP g hg
    have hle : F ⊓ centralizer ({a'} : Set G) ≤ (F ⊓ Cen a.y).map (MulAut.conj g).toMonoidHom := by
      intro x hx
      have hxa : x * a' = a' * x := mem_centralizer_singleton_iff.1 hx.2
      have hginv : g⁻¹ ∈ P := P.inv_mem hgP
      have hwF : g⁻¹ * x * g ∈ F := by
        have := s6_pCoreOf_conj (P := P) hginv hx.1
        simpa using this
      refine ⟨g⁻¹ * x * g, ⟨hwF, ?_⟩, ?_⟩
      · rw [SetLike.mem_coe] at *
        show g⁻¹ * x * g ∈ Cen a.y
        rw [mem_Cen]
        rw [← hga] at hxa
        calc g⁻¹ * x * g * a.y = g⁻¹ * (x * (g * a.y * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * a.y * g⁻¹) * x) * g := by rw [hxa]
          _ = a.y * (g⁻¹ * x * g) := by group
      · show g * (g⁻¹ * x * g) * g⁻¹ = x
        group
    refine le_trans (Subgroup.card_le_of_le hle) ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hCF4
  have htriv : F ≤ centralizer (A : Set G) :=
    s6_trivial_action hF2 hAab hA3 hAc hAn (s6_ub_mem a) hub1 hubA hc
  have hFy : F ≤ Cen a.y := by
    intro f hf
    rw [mem_Cen]
    exact (mem_centralizer_iff.1 (htriv hf) a.y hyA).symm
  refine ⟨?_, ?_⟩
  · refine s6_gen_J a.eAbar hyJ hy3 (centralizer (F : Set G)) ?_
    intro a' ha' ha3
    obtain ⟨g, hg, hga⟩ := s6_exists_conj a.eAbar hyJ hy3 ha' ha3
    have hginv : g⁻¹ ∈ P := P.inv_mem (hAP g hg)
    rw [mem_centralizer_iff]
    intro f hf
    have hw : g⁻¹ * f * g ∈ F := by
      have := s6_pCoreOf_conj (P := P) hginv hf
      simpa using this
    have hwy : (g⁻¹ * f * g) * a.y = a.y * (g⁻¹ * f * g) := mem_Cen.1 (hFy hw)
    rw [← hga]
    calc f * (g * a.y * g⁻¹) = g * ((g⁻¹ * f * g) * a.y) * g⁻¹ := by group
      _ = g * (a.y * (g⁻¹ * f * g)) * g⁻¹ := by rw [hwy]
      _ = g * a.y * g⁻¹ * f := by group
  · have : F ⊓ Cen a.y = F := inf_eq_left.2 hFy
    rw [← this]
    exact hCF

theorem s6_O_solvable (a : PA5 L t E z) :
    Group.IsSolvable ↥(Open.fusionOddCoreOf (Cen a.y)) := by
  set O' : Subgroup G := Open.fusionOddCoreOf (Cen a.y) with hO'
  set Y : Subgroup ↥O' := (zpowers a.y).subgroupOf O' with hY
  have hcomm : ⁅(⊤ : Subgroup ↥O'), ⊤⁆ ≤ Y := by
    refine Subgroup.commutator_le.2 (fun g₁ _ g₂ _ => ?_)
    exact a.O_comm g₁ g₁.2 g₂ g₂.2
  have hYc : ⁅Y, Y⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g hg h hh
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hg
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hh
    apply Subtype.ext
    show (h : G) * (g : G) = (g : G) * (h : G)
    have e1 : (g : G) = a.y ^ m := hm.symm
    have e2 : (h : G) = a.y ^ n := hn.symm
    rw [e1, e2]
    exact (Commute.zpow_zpow_self a.y n m).eq
  refine ⟨⟨2, ?_⟩⟩
  rw [derivedSeries_succ, derivedSeries_succ, derivedSeries_zero]
  exact le_bot_iff.1 (hYc ▸ Subgroup.commutator_mono hcomm hcomm)

theorem s6_Z_facts (hb : PAB G L t E W z) (a : PA5 L t E z) :
    Group.IsSolvable ↥(centralizer ((derivedIn a.Abar : Subgroup G) : Set G)) ∧
      (Nat.card ↥(centralizer ((derivedIn a.Abar : Subgroup G) : Set G))).factorization 2 ≤ 3 := by
  classical
  set J : Subgroup G := derivedIn a.Abar with hJ
  set Z : Subgroup G := centralizer (J : Set G) with hZ
  set C : Subgroup G := Cen a.y with hC
  have hy3 : orderOf a.y = 3 := a.y_ord
  have hyJ : a.y ∈ J := a.y_J
  have hJA : J ≤ a.Abar := derivedIn_le _
  obtain ⟨A, hAJ, hyA, hAc, hAab, hA3⟩ := s6_exists_sylow a.eAbar hyJ hy3
  have hy1 : a.y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy3
    omega
  obtain ⟨w, hwA, hgen⟩ := s6_exists_gen hAc hA3 hyA hy1
  have hwy : w ∉ zpowers a.y := by
    intro hw
    have h1 : zpowers a.y ⊔ zpowers w = zpowers a.y := sup_eq_left.2 (zpowers_le.2 hw)
    rw [h1] at hgen
    have h2 : Nat.card A = 3 := by rw [← hgen, Nat.card_zpowers, hy3]
    omega
  have hw1 : w ≠ 1 := fun h => hwy (h ▸ one_mem _)
  have hwJ : w ∈ J := hAJ hwA
  have hwyc : w * a.y = a.y * w := hAab w hwA a.y hyA
  have hwt : w * t = t * w := mem_centralizer_iff.1 hb.t_cent w (a.Abar_le (hJA hwJ)).1
  have hZC : Z ≤ C := by
    intro x hx
    rw [mem_Cen]
    exact (mem_centralizer_iff.1 hx a.y hyJ).symm
  have hZw : ∀ x ∈ Z, x * w = w * x := fun x hx => (mem_centralizer_iff.1 hx w hwJ).symm
  let w' : ↥C := ⟨w, mem_Cen.2 hwyc⟩
  let t' : ↥C := ⟨t, a.t_cy⟩
  have hw'3 : w' ^ 3 = 1 := Subtype.ext (hA3 w hwA)
  have hg3 : (a.ι (oMk C w')) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hw'3, map_one, map_one]
  have hg1 : a.ι (oMk C w') ≠ 1 := by
    intro h
    have h1 : oMk C w' = 1 := a.ι_inj (by rw [h, map_one])
    have h2 : w' ∈ Open.fusionOddCore ↥C := (QuotientGroup.eq_one_iff w').1 h1
    have h3 : w ∈ Open.fusionOddCoreOf C := ⟨w', h2, rfl⟩
    have h4 : w ∈ Open.fusionOddCoreOf C ⊓ Cen t := ⟨h3, mem_Cen.2 hwt⟩
    rw [a.O_cent_t] at h4
    exact hwy h4
  have hgτ : a.ι (oMk C w') * tau = tau * a.ι (oMk C w') := by
    have : w' * t' = t' * w' := Subtype.ext hwt
    rw [← a.ι_t, ← map_mul, ← map_mul, ← map_mul, ← map_mul, this]
  obtain ⟨c, hc3, hc1, hgc⟩ := s6_three_elt _ hg3 hg1 hgτ
  let ψ : ↥Z →* Wr2 (Equiv.Perm (Fin 5)) := a.ι.comp ((oMk C).comp (Subgroup.inclusion hZC))
  have hψle : ψ.range ≤ centralizer ({base c c} : Set (Wr2 (Equiv.Perm (Fin 5)))) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hgc]
    show a.ι (oMk C (Subgroup.inclusion hZC x)) * a.ι (oMk C w') =
      a.ι (oMk C w') * a.ι (oMk C (Subgroup.inclusion hZC x))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    have : Subgroup.inclusion hZC x * w' = w' * Subgroup.inclusion hZC x := Subtype.ext (hZw x.1 x.2)
    rw [this]
  have hsolvR : Group.IsSolvable ↥ψ.range := s6_solvable_of_le hc3 hc1 hψle
  have hcardR : Nat.card ψ.range ∣ 72 := by
    rw [← s6_card_cent c hc3 hc1]
    exact Subgroup.card_dvd_of_le hψle
  have hker : ∀ x : ↥ψ.ker, (x.1.1 : G) ∈ Open.fusionOddCoreOf C := by
    intro x
    have h1 : oMk C (Subgroup.inclusion hZC x.1) = 1 :=
      a.ι_inj (show a.ι (oMk C (Subgroup.inclusion hZC x.1)) = a.ι 1 by
        rw [map_one]; exact MonoidHom.mem_ker.1 x.2)
    exact ⟨Subgroup.inclusion hZC x.1, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  let κ : ↥ψ.ker →* ↥(Open.fusionOddCoreOf C) :=
    { toFun := fun x => ⟨x.1.1, hker x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hκ : Function.Injective κ := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun q : ↥(Open.fusionOddCoreOf C) => (q : G)) h))
  have hOs := s6_O_solvable a
  have : Group.IsSolvable ↥ψ.ker := Group.isSolvable_of_isSolvable_injective hκ
  have hodd : Odd (Nat.card (Open.fusionOddCoreOf C)) := by
    unfold Open.fusionOddCoreOf
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact s6_odd_core ↥C
  have hkodd : Odd (Nat.card ψ.ker) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective κ hκ)
  have hcardZ : Nat.card Z = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  refine ⟨?_, ?_⟩
  · exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; intro x hx; exact ⟨⟨x, hx⟩, rfl⟩)
  · by_contra hcon
    push Not at hcon
    have hpos : Nat.card Z ≠ 0 := Nat.card_pos.ne'
    have h16 : 2 ^ 4 ∣ Nat.card Z :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).2 hcon
    rw [hcardZ] at h16
    have hcop : Nat.Coprime (2 ^ 4) (Nat.card ψ.ker) :=
      Nat.Coprime.pow_left 4 (Nat.coprime_two_left.2 hkodd)
    have h16' : 2 ^ 4 ∣ Nat.card ψ.range := hcop.dvd_of_dvd_mul_right h16
    have h72 : 2 ^ 4 ∣ 72 := h16'.trans hcardR
    norm_num at h72


theorem s6_CPE (hb : PAB G L t E W z) (a : PA5 L t E z) :
    Cen a.ub ⊓ centralizer ((CFSG.GorensteinWalter.componentLayerOf (Cen a.ub) : Subgroup G) :
      Set G) ≤ Open.pCoreOf 2 (Cen a.ub) := by
  have hub1 : a.ub ≠ 1 := by
    intro h
    have := a.ub_ord
    rw [h, orderOf_one] at this
    omega
  have hodd : Open.fusionOddCore ↥(Cen a.ub) = ⊥ := hb.setting.1.oddCore a.ub a.ub_ord
  have hF4 : Nat.card ↥(Open.pCoreOf 2 (Cen a.ub)) ≤ 4 := by
    refine (s6_F_facts hb a).2.trans ?_
    split_ifs <;> omega
  exact s6_cpe (Cen a.ub) hodd (s6_ub_mem a) hub1 (fun p hp => mem_Cen.1 hp) hF4

theorem s6 : StepS6 := by
  intro G _ _ L t E W z hb a
  obtain ⟨hJF, hF⟩ := s6_F_facts hb a
  obtain ⟨hZs, hZ2⟩ := s6_Z_facts hb a
  exact ⟨{ toPA5 := a
           Z_solv := hZs
           Z_two := hZ2
           F_card := hF
           ub_F := s6_ub_mem a
           J_F := hJF
           CPE := s6_CPE hb a }⟩

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

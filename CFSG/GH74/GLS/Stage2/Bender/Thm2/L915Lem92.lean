module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der72a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Elem
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic2
public import CFSG.GH74.GLS.Stage2.Signalizer.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

namespace L915

section Lem92

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem eq_bot_of_cent_bot {R : Subgroup G} {z : G} (hR : IsPGroup 2 ↥R) (hz2 : z * z = 1)
    (hzR : z ∈ normalizer (R : Set G)) (hcen : R ⊓ centralizer ({z} : Set G) = ⊥) : R = ⊥ := by
  classical
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  let f : ↥R → ↥R := fun r => ⟨z * r * z⁻¹, (mem_normalizer_iff.mp hzR r).mp r.2⟩
  have hf : Function.Involutive f := by
    intro r
    apply Subtype.ext
    show z * (z * r * z⁻¹) * z⁻¹ = r
    rw [hzi]
    calc z * (z * (r : G) * z) * z = (z * z) * r * (z * z) := by group
      _ = r := by rw [hz2]; group
  let F : Function.End ↥R := f
  have hF : F ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext r
    exact hf r
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype ↥R := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := F) (p := 2) (n := 1) hF
  have hfix : ∀ r : ↥R, r ∈ F.fixedPoints → r = 1 := by
    intro r hr
    have h1 : z * (r : G) * z⁻¹ = r := congrArg Subtype.val hr
    have h2c : (r : G) * z = z * r := by
      calc (r : G) * z = z * r * z⁻¹ * z := by rw [h1]
        _ = z * r := by group
    have h2 : (r : G) ∈ R ⊓ centralizer ({z} : Set G) :=
      ⟨r.2, Subgroup.mem_centralizer_singleton_iff.mpr h2c⟩
    rw [hcen, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hcard1 : Fintype.card F.fixedPoints = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, ?_⟩, fun r => ?_⟩
    · show f 1 = 1
      apply Subtype.ext
      show z * (1 : G) * z⁻¹ = 1
      group
    · apply Subtype.ext
      exact hfix r.1 r.2
  by_contra hne
  have hRnt : Nat.card ↥R ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  have hdvd : 2 ∣ Nat.card ↥R := by
    rcases hR.card_eq_or_dvd with h | h
    · exact absurd h hRnt
    · exact h
  rw [hcard1] at hmod
  rw [← Nat.card_eq_fintype_card] at hmod
  obtain ⟨c, hc⟩ := hdvd
  unfold Nat.ModEq at hmod
  omega

theorem lemma9_2a (h118 : IG_11_8) (hC : Ctx9 G z k S M p) {X N : Subgroup G} (hXP : X ≤ Op p M)
    (hzX : z ∈ normalizer (X : Set G)) (hXN : normalizer (X : Set G) ≤ N) : Op 2 N = ⊥ := by
  have hp := hC.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := Op 2 N with hRdef
  have hR2 : IsPGroup 2 ↥R := op_isPGroup N
  have hRN : N ≤ normalizer (R : Set G) := le_normalizer_Op' 2 N
  have hzN : z ∈ N := hXN hzX
  have hz2 := hC.z_mul_z
  have hPp : IsPGroup p ↥(Op p M) := hC.P_pgroup
  have hdisj : R ⊓ Op p M = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 2 p (Ne.symm hC.odd) R (Op p M) hR2 hPp)
  set R₁ : Subgroup G := R ⊓ Cen z with hR₁
  have hR₁M : R₁ ≤ M := inf_le_right.trans hC.cen_le
  have hcomm : ∀ u ∈ Op p M ⊓ normalizer (X : Set G), ∀ r ∈ R₁, u * r = r * u := by
    intro u hu r hr
    have huN : u ∈ N := hXN hu.2
    have hrR : r ∈ R := hr.1
    have hrM : r ∈ M := hR₁M hr
    have hc1 : u * r * u⁻¹ * r⁻¹ ∈ R := by
      have h1 : u * r * u⁻¹ ∈ R := (mem_normalizer_iff.mp (hRN huN) r).mp hrR
      exact R.mul_mem h1 (R.inv_mem hrR)
    have hc2 : u * r * u⁻¹ * r⁻¹ ∈ Op p M := by
      have hu' : r * u⁻¹ * r⁻¹ ∈ Op p M :=
        (mem_normalizer_iff.mp (le_normalizer_Op' p M hrM) u⁻¹).mp ((Op p M).inv_mem hu.1)
      have : u * r * u⁻¹ * r⁻¹ = u * (r * u⁻¹ * r⁻¹) := by group
      rw [this]
      exact (Op p M).mul_mem hu.1 hu'
    have hc : u * r * u⁻¹ * r⁻¹ = 1 := by
      have hmem : u * r * u⁻¹ * r⁻¹ ∈ R ⊓ Op p M := ⟨hc1, hc2⟩
      rw [hdisj, Subgroup.mem_bot] at hmem
      exact hmem
    calc u * r = (u * r * u⁻¹ * r⁻¹) * (r * u) := by group
      _ = r * u := by rw [hc, one_mul]
  have hR₁P : R₁ ≤ normalizer ((Op p M : Subgroup G) : Set G) := hR₁M.trans (le_normalizer_Op' p M)
  have hR₁X : R₁ ≤ normalizer (X : Set G) :=
    le_normalizer_of_commutes fun x hx y hy =>
      (hcomm y ⟨hXP hy, Subgroup.le_normalizer hy⟩ x hx).symm
  have hcen : X ⊔ (Op p M ⊓ centralizer (X : Set G)) ≤ centralizer (R₁ : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (hcomm x ⟨hXP hx, Subgroup.le_normalizer hx⟩ r hr).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (hcomm x ⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩ r hr).symm
  have hcop : Nat.Coprime p (Nat.card ↥R₁) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hR2.to_le (inf_le_left : R₁ ≤ R))
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).mpr hC.odd)
  have hPc : Op p M ≤ centralizer (R₁ : Set G) :=
    h118 G p hp R₁ (Op p M) X hPp hcop hR₁P hR₁X hXP hcen
  have hR₁bot : R₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxM : x ∈ M := hR₁M hx
    have hxFm : x ∈ Fm M := by
      refine mem_Fm_of_centralizes_Fs hxM ?_
      rw [hC.fstar]
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hPc hy) x hx).symm
    have hxP : x ∈ Op p M := by
      rw [← hC.fstar]
      exact Fm_le_Fs M hxFm
    have : x ∈ R ⊓ Op p M := ⟨hx.1, hxP⟩
    rw [hdisj] at this
    exact this
  exact eq_bot_of_cent_bot hR2 hz2 (hRN hzN) hR₁bot

@[expose] def Dcore (p : ℕ) (N : Subgroup G) : Subgroup G := ⨆ (q : ℕ) (_ : q.Prime ∧ q ≠ p), Op q N

theorem lemma9_2b (h19 : B_signalizer_19_9) (h118 : IG_11_8) (hC : Ctx9 G z k S M p)
    {X N Y : Subgroup G} (hXP : X ≤ Op p M) (hzX : z ∈ normalizer (X : Set G)) (hN : IsCoatom N)
    (hXN : normalizer (X : Set G) ≤ N) (hY : Y ≤ Op p M ⊓ N) (hYc : ⁅Y, zpowers z⁆ = Y) :
    Y ≤ centralizer (Dcore p N : Set G) := by
  have hp := hC.prime
  have hO2 : Op 2 N = ⊥ := lemma9_2a h118 hC hXP hzX hXN
  have hzN : z ∈ N := hXN hzX
  have hzP : z ∈ normalizer ((Op p M : Subgroup G) : Set G) := le_normalizer_Op' p M hC.z_mem
  have hzPN : z ∈ normalizer ((Op p M ⊓ N : Subgroup G) : Set G) :=
    Thm1.mem_normalizer_inf hzP (Subgroup.le_normalizer hzN)
  set Y₁ : Subgroup G := ⁅Op p M ⊓ N, zpowers z⁆ with hY₁def
  have hYY₁ : Y ≤ Y₁ := by
    conv_lhs => rw [← hYc]
    exact Subgroup.commutator_mono hY le_rfl
  by_cases hY₁0 : Y₁ = ⊥
  · rw [hY₁0, le_bot_iff] at hYY₁
    rw [hYY₁]
    exact bot_le
  have hY₁le : Y₁ ≤ Op p M ⊓ N :=
    commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzPN)
  have hY₁p : IsPGroup p ↥Y₁ := hC.P_pgroup.to_le (hY₁le.trans inf_le_left)
  have hY₁c : ⁅Y₁, zpowers z⁆ = Y₁ :=
    commutator_zpowers_idem hC.orderOf_z hp hC.odd (hC.P_pgroup.to_le inf_le_left) hzPN
  have hsig : Sig4Sub G z N p Y₁ := by
    refine ⟨hN.1, ⟨hp, hC.odd, hzN, hY₁le.trans inf_le_right, hY₁p, hY₁0, ?_, hY₁c⟩⟩
    intro c hcN hcz
    have hcM : c ∈ M := hC.cen_le hcz
    have hcPN : c ∈ normalizer ((Op p M ⊓ N : Subgroup G) : Set G) :=
      Thm1.mem_normalizer_inf (le_normalizer_Op' p M hcM) (Subgroup.le_normalizer hcN)
    exact mem_normalizer_commutator hcPN
      (mem_normalizer_zpowers_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hcz))
  have hcent := (signalizer_sub h19 hC.orderOf_z hsig).1
  refine le_trans hYY₁ ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun q hq => ?_
  rw [← Subgroup.le_centralizer_iff]
  by_cases hq2 : q = 2
  · intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ Op q N := hh
    rw [hq2, hO2, Subgroup.mem_bot] at hh'
    rw [hh', one_mul, mul_one]
  · exact hcent q hq.1 hq2 hq.2

end Lem92

end L915

end CFSG.GH74.GLS.Stage2.Bender.Thm2

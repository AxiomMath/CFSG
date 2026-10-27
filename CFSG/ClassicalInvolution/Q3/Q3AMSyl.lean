module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64P

public section

open Pointwise

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_commutes_of_commutator_mem {A B N : Subgroup G} (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) (hN : Odd (Nat.card N)) (hAN : A ≤ Subgroup.normalizer (N : Set G))
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) (hAB : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ N) :
    ∃ p ∈ N, ∀ a ∈ A, ∀ b ∈ B, a * (p * b * p⁻¹) = (p * b * p⁻¹) * a := by
  classical
  set T : Subgroup G := N ⊔ B with hT
  have hBT : IsSylow2In B T := isSylow2In_of_eq_sup_odd hN hBN le_sup_right hB rfl
  have hNT : N ≤ T := le_sup_left
  have hAT : ∀ a ∈ A, ∀ t ∈ T, a * t * a⁻¹ ∈ T := by
    intro a ha t ht
    have ht' : t ∈ Subgroup.closure ((N : Set G) ∪ (B : Set G)) := by
      rw [← Subgroup.sup_eq_closure]; exact ht
    refine Subgroup.closure_induction (p := fun x _ => a * x * a⁻¹ ∈ T) ?_ ?_ ?_ ?_ ht'
    · intro u hu
      rcases hu with hu | hu
      · exact hNT ((Subgroup.mem_normalizer_iff.mp (hAN ha) u).mp hu)
      · have : a * u * a⁻¹ = ⁅a, u⁆ * u := by simp only [commutatorElement_def]; group
        rw [this]
        exact T.mul_mem (hNT (hAB a ha u hu)) (Subgroup.mem_sup_right hu)
    · simp
    · intro x y _ _ hx hy
      have : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      rw [this]
      exact T.mul_mem hx hy
    · intro x _ hx
      have : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
      rw [this]
      exact T.inv_mem hx
  have hconjT : ∀ a ∈ A, conjSub a T = T := by
    intro a ha
    ext x
    rw [mem_conjSub_iff]
    constructor
    · intro h
      have := hAT a ha _ h
      simpa [mul_assoc] using this
    · intro h
      have := hAT a⁻¹ (A.inv_mem ha) _ h
      simpa [mul_assoc] using this
  set S : Set (Subgroup G) := {B' | ∃ n ∈ N, B' = conjSub n B} with hS
  have hSsyl : ∀ B' ∈ S, IsSylow2In B' T := by
    rintro _ ⟨n, hn, rfl⟩
    have := isSylow2In_conjSub hBT n
    rwa [conjSub_eq_self_of_mem (hNT hn)] at this
  have hAS : ∀ a ∈ A, ∀ B' ∈ S, conjSub a B' ∈ S := by
    intro a ha B' hB'
    have h1 := isSylow2In_conjSub (hSsyl B' hB') a
    rw [hconjT a ha] at h1
    obtain ⟨x, hx, hxB⟩ := exists_conjSub_eq_of_isSylow2In hBT h1
    obtain ⟨n', hn', b0, hb0, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hx
    refine ⟨n', hn', ?_⟩
    rw [← hxB, conjSub_mul, conjSub_eq_self_of_mem hb0]
  let _ : MulAction N (Subgroup G) :=
    MulAction.compHom (Subgroup G) (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  have hsmul : ∀ (o : N) (H : Subgroup G), o • H = conjSub (o : G) H := by
    intro o H
    ext x
    rw [mem_conjSub_iff]
    show x ∈ (ConjAct.toConjAct (o : G)) • H ↔ _
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [ConjAct.smul_def, mul_assoc] using hy
    · intro h
      exact ⟨_, h, by simp [ConjAct.smul_def, mul_assoc]⟩
  have hSorb : S = MulAction.orbit N B := by
    ext B'
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, hsmul _ _⟩
    · rintro ⟨o, rfl⟩
      exact ⟨o, o.2, (hsmul o B).symm⟩
  have hodd : ¬ 2 ∣ Nat.card S := by
    rw [hSorb, Nat.card_coe_set_eq, ← MulAction.index_stabilizer N B]
    have hd : (MulAction.stabilizer N B).index ∣ Nat.card N := Subgroup.index_dvd_card _
    intro h2
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr (h2.trans hd))
  let _ : MulAction A S :=
    { smul := fun x u => ⟨conjSub (x : G) u, hAS x x.2 u u.2⟩
      one_smul := fun u => Subtype.ext (by
        show conjSub ((1 : A) : G) (u : Subgroup G) = u
        rw [Subgroup.coe_one, conjSub_one])
      mul_smul := fun x y u => Subtype.ext (by
        show conjSub ((x * y : A) : G) (u : Subgroup G) = conjSub (x : G) (conjSub (y : G) u)
        rw [Subgroup.coe_mul, conjSub_mul]) }
  obtain ⟨u, hu⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card S hodd
  obtain ⟨n, hn, hun⟩ := u.2
  have hfix : ∀ a ∈ A, conjSub a (u : Subgroup G) = u := fun a ha =>
    congrArg Subtype.val (MulAction.mem_fixedPoints.mp hu ⟨a, ha⟩)
  have hu2 : IsPGroup 2 (u : Subgroup G) := by
    rw [hun]; exact isPGroup_conjSub n hB
  refine ⟨n, hn, fun a ha b hb => ?_⟩
  have hb' : n * b * n⁻¹ ∈ (u : Subgroup G) := by rw [hun]; exact conj_mem_conjSub hb
  have h1 : a * (n * b * n⁻¹) * a⁻¹ ∈ (u : Subgroup G) := by
    have := conj_mem_conjSub (n := a) hb'
    rwa [hfix a ha] at this
  have hcomm_mem : ⁅a, n * b * n⁻¹⁆ ∈ (u : Subgroup G) := by
    have : ⁅a, n * b * n⁻¹⁆ = (a * (n * b * n⁻¹) * a⁻¹) * (n * b * n⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
    rw [this]
    exact (u : Subgroup G).mul_mem h1 ((u : Subgroup G).inv_mem hb')
  have hcommN : ⁅a, n * b * n⁻¹⁆ ∈ N := by
    have e : ⁅a, n * b * n⁻¹⁆ = (a * n * a⁻¹) * ⁅a, b⁆ *
        (b * ((a * n * a⁻¹)⁻¹ * n) * b⁻¹) * n⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hn₂ : a * n * a⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hAN ha) n).mp hn
    have hq : (a * n * a⁻¹)⁻¹ * n ∈ N := N.mul_mem (N.inv_mem hn₂) hn
    have hbq : b * ((a * n * a⁻¹)⁻¹ * n) * b⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hBN hb) _).mp hq
    exact N.mul_mem (N.mul_mem (N.mul_mem hn₂ (hAB a ha b hb)) hbq) (N.inv_mem hn)
  have h1' : ⁅a, n * b * n⁻¹⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd hN hcommN (hu2.to_le (Subgroup.zpowers_le.mpr hcomm_mem))
  have := (commutatorElement_eq_one_iff_mul_comm).mp h1'
  exact this

theorem exists_conj_commutes_of_commutator_mem_centralizer {A B N : Subgroup G} {c : G}
    (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) (hN : Odd (Nat.card N))
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hBN : B ≤ Subgroup.normalizer (N : Set G))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ N) (hAc : ∀ a ∈ A, a * c = c * a)
    (hBc : ∀ b ∈ B, b * c = c * b) :
    ∃ p ∈ N, p * c = c * p ∧ ∀ a ∈ A, ∀ b ∈ B, a * (p * b * p⁻¹) = (p * b * p⁻¹) * a := by
  set N' : Subgroup G := N ⊓ Subgroup.centralizer ({c} : Set G) with hN'
  have hN'odd : Odd (Nat.card N') :=
    hN.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left : N' ≤ N))
  have hnorm : ∀ g : G, g ∈ Subgroup.normalizer (N : Set G) → g * c = c * g →
      ∀ x ∈ N', g * x * g⁻¹ ∈ N' := by
    intro g hg hgc x hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hx.1,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hcg : c * g⁻¹ = g⁻¹ * c := by
      calc c * g⁻¹ = g⁻¹ * (g * c) * g⁻¹ := by group
        _ = g⁻¹ * (c * g) * g⁻¹ := by rw [hgc]
        _ = g⁻¹ * c := by group
    calc (g * x * g⁻¹) * c = g * x * (g⁻¹ * c) := by group
      _ = g * x * (c * g⁻¹) := by rw [← hcg]
      _ = g * (x * c) * g⁻¹ := by group
      _ = g * (c * x) * g⁻¹ := by rw [hxc]
      _ = (g * c) * x * g⁻¹ := by group
      _ = (c * g) * x * g⁻¹ := by rw [hgc]
      _ = c * (g * x * g⁻¹) := by group
  have hnormiff : ∀ g ∈ Subgroup.normalizer (N : Set G), g * c = c * g →
      g ∈ Subgroup.normalizer (N' : Set G) := by
    intro g hg hgc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hnorm g hg hgc x hx, fun hx => ?_⟩
    have hginv : g⁻¹ ∈ Subgroup.normalizer (N : Set G) := (Subgroup.normalizer _).inv_mem hg
    have hgc' : g⁻¹ * c = c * g⁻¹ := by
      calc g⁻¹ * c = g⁻¹ * (c * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * c) * g⁻¹ := by rw [hgc]
        _ = c * g⁻¹ := by group
    have := hnorm g⁻¹ hginv hgc' _ hx
    simpa [mul_assoc] using this
  obtain ⟨p, hp, hcomm⟩ := exists_conj_commutes_of_commutator_mem hA hB hN'odd
    (fun a ha => hnormiff a (hAN ha) (hAc a ha)) (fun b hb => hnormiff b (hBN hb) (hBc b hb))
    (fun a ha b hb => by
      refine ⟨hAB a ha b hb, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hac : Commute a c := hAc a ha
      have hbc : Commute b c := hBc b hb
      have hcomm : Commute ⁅a, b⁆ c := by
        simp only [commutatorElement_def]
        exact ((hac.mul_left hbc).mul_left hac.inv_left).mul_left hbc.inv_left
      exact hcomm.eq)
  exact ⟨p, hp.1, Subgroup.mem_centralizer_singleton_iff.mp hp.2, hcomm⟩

end CFSG.ClassicalInvolution.Q3.Q3AM

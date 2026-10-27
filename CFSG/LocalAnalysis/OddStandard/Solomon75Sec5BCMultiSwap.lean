module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiBase
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiLu
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapMoved

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.LocalCores
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Step5

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

private theorem bcdSwap_perfect {H K : Subgroup X} (h : IsPCompIn 2 H K) : ⁅K, K⁆ = K := by
  have hp : Group.IsPerfect (K.subgroupOf H) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect h.2
  have hp' : Group.IsPerfect K := by
    have e := Subgroup.subgroupOfEquivOfLe h.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Subgroup.isPerfect_iff.mp hp'

private theorem bcdSwap_primeResidual {H K : Subgroup X} (h : IsPCompIn 2 H K) :
    primeResidual 2 ↥K = ⊤ :=
  ((isTwoGenQuasi_subgroupOf_iff h.1).1 (isPComponent_two_iff.1 h.2).2).1

private theorem bcdSwap_cen_fixed (h : Sec5Data X n z Z S) (hZs : Z ≤ centralizer ({s} : Set X))
    (hsC : s ∈ centralizer ({z} : Set X)) {M : Subgroup X}
    (hM : Sec5Comp X n (centralizer ({z} : Set X)) M) :
    ∀ c ∈ M, (∀ m ∈ M, ⁅m, c⁆ ∈ oddCoreOf M) →
      s * c * s⁻¹ * c⁻¹ ∈ oddCoreOf (centralizer ({z} : Set X)) := by
  classical
  intro c hcM hc
  obtain ⟨⟨u₀, hu₀⟩, hMn⟩ := id hM
  obtain ⟨u, huZ, hu⟩ := h.pair.exists_witness_mem hu₀ hMn
  have hcz : c ∈ zStar M := ⟨hcM, Subgroup.le_normalizer hcM,
    mem_normalizer_pPrimeCoreOf_of_mem hcM, fun k hk => hc k hk⟩
  have hc' : c ∈ pPrimeCoreOf 2 M ⊔ Subgroup.zpowers u := hu.zStar_le_sup_zpowers hMn hcz
  have hnorm : Subgroup.zpowers u ≤ normalizer (pPrimeCoreOf 2 M : Set X) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_pPrimeCoreOf_of_mem hu.2.1
  obtain ⟨o, ho, w, hw, rfl⟩ :=
    (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing (pPrimeCoreOf 2 M) (Subgroup.zpowers u)
      hnorm c).1 hc'
  have hwC : w ∈ centralizer ({s} : Set X) :=
    (Subgroup.zpowers_le.2 (hZs huZ)) hw
  have hsw : s * w * s⁻¹ = w := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hwC
    rw [← this]
    group
  have hoO : o ∈ oddCoreOf (centralizer ({z} : Set X)) :=
    oddCoreOf_le_of_isPCompIn hM.isPCompIn ho
  have hso : s * o * s⁻¹ ∈ oddCoreOf (centralizer ({z} : Set X)) :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf _ hsC) o).1 hoO
  have e : s * (o * w) * s⁻¹ * (o * w)⁻¹ = (s * o * s⁻¹) * o⁻¹ := by
    calc s * (o * w) * s⁻¹ * (o * w)⁻¹
        = (s * o * s⁻¹) * (s * w * s⁻¹) * w⁻¹ * o⁻¹ := by group
      _ = (s * o * s⁻¹) * o⁻¹ := by rw [hsw]; group
  rw [e]
  exact Subgroup.mul_mem _ hso (Subgroup.inv_mem _ hoO)

private theorem bcdSwap_comm_diag {C L L₁ : Subgroup X} {t : X} (hL : IsPCompIn 2 C L)
    (hLt : IsPCompIn 2 C (L.map (MulAut.conj t).toMonoidHom)) (hL₁ : IsPCompIn 2 C L₁)
    (hne1 : L₁ ≠ L) (hne2 : L₁ ≠ L.map (MulAut.conj t).toMonoidHom) {d : X}
    (hd : ∃ m ∈ L, d * (m * (t * m * t⁻¹))⁻¹ ∈ oddCoreOf C) :
    ∀ l ∈ L₁, ⁅l, d⁆ ∈ oddCoreOf C := by
  classical
  have hL₁C : L₁ ≤ C := hL₁.1
  set Q : Subgroup X := centralizerSection L₁ (oddCoreOf C) with hQ
  have hcomp : ∀ A : Subgroup X, IsPCompIn 2 C A → L₁ ≠ A → ∀ a ∈ A, a ∈ Q := by
    intro A hA hne a ha
    have hcomm : ∀ l ∈ L₁, ⁅l, a⁆ ∈ oddCoreOf C := fun l hl =>
      commutator_mem_oddCoreOf_of_ne hL₁ hA hne hl ha
    refine ⟨?_, le_normalizer_oddCoreOf C (hA.1 ha), hcomm⟩
    exact (normalizes_isPCompIn_of_comm_mem hL₁ (Subgroup.le_normalizer (hA.1 ha)) hcomm).1
  obtain ⟨m, hm, hmo⟩ := hd
  have hmQ : m ∈ Q := hcomp L hL hne1 m hm
  have hmsQ : t * m * t⁻¹ ∈ Q := hcomp _ hLt hne2 _ ⟨m, hm, rfl⟩
  have hoQ : d * (m * (t * m * t⁻¹))⁻¹ ∈ Q := by
    have hoC : d * (m * (t * m * t⁻¹))⁻¹ ∈ pPrimeCoreOf 2 C := hmo
    refine ⟨pPrimeCoreOf_le_normalizer_of_isPCompIn hL₁ hoC,
      le_normalizer_oddCoreOf C (oddCoreOf_le C hmo), fun l hl => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf C (hL₁C hl)) _).1 hmo
    have h2 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hmo)
    simpa [commutatorElement_def, mul_assoc] using h2
  have hdQ : d ∈ Q := by
    have := Subgroup.mul_mem Q hoQ (Subgroup.mul_mem Q hmQ hmsQ)
    rwa [inv_mul_cancel_right] at this
  exact hdQ.2.2

theorem step5_swap (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) {u : X} (huZ : u ∈ Z)
    (hu1 : u ≠ 1) (hus : u * s = s * u)
    (hu_norm : ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → u ∈ normalizer (B : Set X))
    {L₁ : Subgroup X} (hL₁ : Sec5Comp X n (centralizer ({u} : Set X)) L₁)
    (hsL₁ : s ∈ normalizer (L₁ : Set X)) (hsnt : ¬ CentModOdd L₁ s) :
    ∀ L, Sec5Comp X n (centralizer ({u} : Set X)) L → s ∈ normalizer (L : Set X) := by
  classical
  intro L hL
  by_contra hsL
  have hu' : Sec5Data X n u Z S := h.withPair huZ hu1
  have hZs : Z ≤ centralizer ({s} : Set X) := Z_le_centralizer_of_swap h hs
  have hsCu : s ∈ centralizer ({u} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hus.symm
  have hne : L.map (MulAut.conj s).toMonoidHom ≠ L := fun heq =>
    hsL (mem_normalizer_of_map_conj_eq heq)
  obtain ⟨Δ, hΔle, hΔpc, hcov, hdiag, hq⟩ := exists_diagLift hL.isPCompIn hsCu hs.sq hne
  have hcen := bcdSwap_cen_fixed hu' hZs hsCu hL
  have hD : SwapDiag X n u s L Δ := ⟨hL, hus, hne, hΔle, hΔpc, bcdSwap_perfect hΔpc,
    bcdSwap_primeResidual hΔpc, hq hL.2 hcen, hcov, hcen⟩
  by_cases hnt : ∃ B, Sec5Comp X n (centralizer ({s} : Set X)) B ∧ ∃ d ∈ Δ, ∃ b ∈ B,
      ⁅b, d⁆ ∉ oddCoreOf (centralizer ({s} : Set X))
  ·
    obtain ⟨B, hB, hBu⟩ := exists_moved_of_diag hu' hs hus hD hnt
    exact hBu (map_conj_eq_of_mem_normalizer (hu_norm B hB))
  · push Not at hnt
    have hn : 8 ≤ n := h.maxdeg.1
    obtain ⟨r, hrΔ, hr1, hr2⟩ : ∃ r ∈ Δ, r ≠ 1 ∧ r * r = 1 := by
      obtain ⟨e⟩ := hD.quot
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      have h4 := two_mul_nat_card_alternatingGroup (α := Fin n)
      rw [Nat.card_eq_fintype_card (α := Perm (Fin n)), Fintype.card_perm,
        Fintype.card_fin] at h4
      obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial (show 4 ≤ n by omega)
      have h24 : Nat.factorial 4 = 24 := by decide
      rw [h24] at hk
      have hdvdA : 2 ∣ Nat.card (alternatingGroup (Fin n)) := by omega
      have hdvd : 2 ∣ Nat.card ↥Δ := by
        have h1 : Nat.card (↥Δ ⧸ pPrimeCore 2 ↥Δ) ∣ Nat.card ↥Δ :=
          Subgroup.card_quotient_dvd_card _
        rw [Nat.card_congr e.toEquiv] at h1
        exact hdvdA.trans h1
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Δ) 2 hdvd
      refine ⟨(x : X), x.2, ?_, ?_⟩
      · intro h1
        have : x = 1 := Subtype.ext h1
        rw [this, orderOf_one] at hx
        omega
      · have h2 : orderOf (x : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
        have := pow_orderOf_eq_one (x : X)
        rw [h2, sq] at this
        exact this
    have hrCu : r ∈ centralizer ({u} : Set X) := (hΔle hrΔ).1
    have hrCs : r ∈ centralizer ({s} : Set X) := (hΔle hrΔ).2
    have hrs : r * s = s * r := Subgroup.mem_centralizer_singleton_iff.1 hrCs
    obtain ⟨B, hB, -⟩ := h.exists_comp_centralizer hs
    have hrB : r ∈ centralizerSection B (pPrimeCoreOf 2 B) :=
      normalizes_isPCompIn_of_comm_mem hB.isPCompIn (Subgroup.le_normalizer hrCs)
        (fun b hb => hnt B hB r hrΔ b hb)
    have hne1 : L₁ ≠ L := fun e => hsL (e ▸ hsL₁)
    have hne2 : L₁ ≠ L.map (MulAut.conj s).toMonoidHom := by
      intro e
      apply hne
      have h1 : L₁.map (MulAut.conj s).toMonoidHom = L₁ := map_conj_eq_of_mem_normalizer hsL₁
      have hss : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs.sq
      have h2 : (L.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s).toMonoidHom = L := by
        ext x
        constructor
        · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
          have : s * (s * w * s⁻¹) * s⁻¹ = w := by
            rw [hss]
            calc s * (s * w * s) * s = (s * s) * w * (s * s) := by group
              _ = w := by rw [hs.sq]; group
          show s * (s * w * s⁻¹) * s⁻¹ ∈ L
          rw [this]
          exact hw
        · intro hx
          refine ⟨s * x * s⁻¹, ⟨x, hx, rfl⟩, ?_⟩
          show s * (s * x * s⁻¹) * s⁻¹ = x
          rw [hss]
          calc s * (s * x * s) * s = (s * s) * x * (s * s) := by group
            _ = x := by rw [hs.sq]; group
      rw [e, h2] at h1
      exact h1.symm
    have hLs : IsPCompIn 2 (centralizer ({u} : Set X)) (L.map (MulAut.conj s).toMonoidHom) :=
      (hL.map_conj (Subgroup.le_normalizer hsCu)).isPCompIn
    have hcomm := bcdSwap_comm_diag hL.isPCompIn hLs hL₁.isPCompIn hne1 hne2 (hdiag r hrΔ)
    have hrL₁ : r ∈ centralizerSection L₁ (pPrimeCoreOf 2 L₁) :=
      normalizes_isPCompIn_of_comm_mem hL₁.isPCompIn (Subgroup.le_normalizer hrCu) hcomm
    exact lemmaB h hs hL₁ hsL₁ hsnt hr1 hr2 hrs hrL₁ hB hrB

end Step5

end CFSG.OddStandard.Solomon75

module

public import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.U38

open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Open

theorem glaPPrimeCoreOf_eq_bot_of_plane {M : Type} [Group M] [Finite M] {I E H : Subgroup M}
    {f : M} (hIn : ∀ g x, x ∈ I → g * x * g⁻¹ ∈ I) (hIH : I ≤ H) (hEI : E ≤ I)
    (hEf : ∀ e ∈ E, e * f = f * e) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hbig : 3 < Nat.card E)
    (htor : ∀ b ∈ E, b ≠ 1 → ∀ r ∈ I, Nat.Coprime 3 (orderOf r) → r * b = b * r → r = 1)
    (hheis : ∀ g : M, (∀ e ∈ E, g * e = e * g) → Nat.Coprime 3 (orderOf g) → g = 1) :
    GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({f} : Set M)) = ⊥ := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  set N := GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({f} : Set M)) with hN
  have hNcop : Nat.Coprime 3 (Nat.card N) := coprime_card_GLAPPrimeCoreOf hp _
  have hEC : ∀ e ∈ E, e ∈ H ⊓ Subgroup.centralizer ({f} : Set M) := fun e he =>
    ⟨hIH (hEI he), Subgroup.mem_centralizer_singleton_iff.mpr (hEf e he)⟩
  have hNconj : ∀ e ∈ E, ∀ y ∈ N, e * y * e⁻¹ ∈ N := fun e he y hy =>
    GLAPPrimeCoreOf_conj_mem e (hEC e he) y hy
  set V : Subgroup M := N ⊓ I with hV
  have hVconj : ∀ e ∈ E, ∀ y ∈ V, e * y * e⁻¹ ∈ V := fun e he y hy =>
    ⟨hNconj e he y hy.1, hIn e y hy.2⟩
  have hVcop : ¬ 3 ∣ Nat.card V := by
    have h1 : Nat.card V ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    exact fun h => ((Nat.Prime.coprime_iff_not_dvd hp).mp hNcop) (h.trans h1)
  have hAV : E ≤ Subgroup.normalizer (V : Set M) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => hVconj e he y hy
    · intro hy
      have := hVconj e⁻¹ (E.inv_mem he) _ hy
      simpa [mul_assoc] using this
  have : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  have : CFSG.IsElementaryAbelian 3 E :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hexp x x.2) }
  have : Nontrivial E := by
    exact Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := 3) (A := E)
    (V := V) hAV hVcop
  have hVbot : V = ⊥ := by
    refine le_bot_iff.mp (hgen.trans (iSup₂_le fun B hB => ?_))
    intro x hx
    obtain ⟨hxV, hxC⟩ := hx
    have hBcard : Nat.card B * 3 = Nat.card E := by
      have := B.card_mul_index
      rwa [hB] at this
    obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hBbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
      rw [hBbot, Subgroup.card_bot] at hBcard
      omega
    have hbE : (b : M) ∈ E := b.2
    have hb1' : (b : M) ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hxcop : Nat.Coprime 3 (orderOf x) := by
      refine hNcop.coprime_dvd_right ?_
      exact (Subgroup.orderOf_dvd_natCard V hxV).trans (Subgroup.card_dvd_of_le inf_le_left)
    have hxcomm : (b : M) * x = x * b :=
      Subgroup.mem_centralizer_iff.mp hxC b ⟨b, hbB, rfl⟩
    have := htor b hbE hb1' x hxV.2 hxcop hxcomm.symm
    simp [this]
  refine le_bot_iff.mp fun n hn => ?_
  rw [Subgroup.mem_bot]
  refine hheis n (fun e he => ?_) ?_
  · have h1 : e * n⁻¹ * e⁻¹ ∈ N := hNconj e he n⁻¹ (N.inv_mem hn)
    have h2 : n * e * n⁻¹ * e⁻¹ ∈ V := by
      refine ⟨?_, ?_⟩
      · have := N.mul_mem hn h1
        simpa [mul_assoc] using this
      · exact I.mul_mem (hIn n e (hEI he)) (I.inv_mem (hEI he))
    rw [hVbot, Subgroup.mem_bot] at h2
    have h3 : n * e * n⁻¹ = e := by
      rw [mul_inv_eq_one] at h2
      exact h2
    calc n * e = (n * e * n⁻¹) * n := by group
      _ = e * n := by rw [h3]
  · refine hNcop.coprime_dvd_right ?_
    exact Subgroup.orderOf_dvd_natCard N hn

end CFSG.HardMathSupport.Solomon.Coordinator.U38

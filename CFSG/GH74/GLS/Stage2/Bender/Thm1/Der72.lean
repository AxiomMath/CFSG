module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der72a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section L72

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M V : Subgroup G} {p : ℕ}

theorem V7.le_cen (hV : V7 z S V) : V ≤ Cen z := hV.le_L.trans (LC_le_Cen z)

theorem V7.comm_z (hV : V7 z S V) {v : G} (hv : v ∈ V) : v * z = z * v :=
  Subgroup.mem_centralizer_singleton_iff.mp (hV.le_cen hv)

theorem exists_ne_one_centralizer (h1123 : IG_11_23) (hC : Ctx6 G z k S M p) (hV : V7 z S V)
    {R : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hR : IsPGroup r ↥R)
    (hRn : M ≤ normalizer (R : Set G)) (hR0 : R ≠ ⊥) {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀1 : v₀ ≠ 1) :
    ∃ y ∈ R, y ≠ 1 ∧ y * v₀ = v₀ * y := by
  have : Fact r.Prime := ⟨hr⟩
  have hcop : Nat.Coprime 2 (Nat.card ↥R) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hR
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))
  have hVn : V ≤ normalizer (R : Set G) := (hV.le_cen.trans hC.cen_le).trans hRn
  have hsum := h1123 G 2 Nat.prime_two V R hV.four.1 (by rw [hV.four.2]; norm_num) hcop hVn
  by_contra hno
  push Not at hno
  apply hR0
  rw [eq_bot_iff]
  refine hsum.trans (iSup₂_le fun v₁ hv₁ => ?_)
  rintro y ⟨hyR, hyC⟩
  rw [Subgroup.mem_bot]
  by_contra hy1
  obtain ⟨c, hc, hcv⟩ := hV.conj v₁ hv₁.1 hv₁.2 v₀ hv₀ hv₀1
  have hy' : c * y * c⁻¹ ∈ R := (mem_normalizer_iff.mp (hRn (hC.cen_le hc)) y).mp hyR
  have hyv : y * v₁ = v₁ * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
  refine hno (c * y * c⁻¹) hy' (fun h => hy1 (by simpa using h)) ?_
  rw [← hcv]
  calc c * y * c⁻¹ * (c * v₁ * c⁻¹) = c * (y * v₁) * c⁻¹ := by group
    _ = c * (v₁ * y) * c⁻¹ := by rw [hyv]
    _ = c * v₁ * c⁻¹ * (c * y * c⁻¹) := by group

theorem exists_v0 (h1123 : IG_11_23) (hC : Ctx6 G z k S M p) {Q : Subgroup G} (hQ : QP z p (Op p M) Q)
    (hV : V7 z S V) : ∃ v₀ ∈ V, v₀ ≠ 1 ∧ ¬ Q ⊓ centralizer ({v₀} : Set G) ≤ Cen z := by
  have hp := hC.prime
  by_contra hno
  push Not at hno
  have hQp : IsPGroup p ↥Q := (isPGroup_Op p hp M).to_le hQ.1
  have : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime 2 (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hQp
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hC.p_ne_two))
  have hQn : M ≤ normalizer (Q : Set G) := le_normalizer_QP (le_normalizer_Op p M) hQ
  have hVn : V ≤ normalizer (Q : Set G) := (hV.le_cen.trans hC.cen_le).trans hQn
  have hsum := h1123 G 2 Nat.prime_two V Q hV.four.1 (by rw [hV.four.2]; norm_num) hcop hVn
  have : Q ≤ Cen z := hsum.trans (iSup₂_le fun v hv => hno v hv.1 hv.2)
  exact hQ.2.2.2.2.2 this

theorem lemma7_2_of (h62 : Prop6_2) (h66 : Prop6_6) (h69 : Prop6_9) (hB12 : Bender12)
    (h1123 : IG_11_23) : Lemma7_2 := by
  intro G _ _ z k S M p hC Q V hQ hV
  have hp := hC.prime
  have hQn : M ≤ normalizer (Q : Set G) := le_normalizer_QP (le_normalizer_Op p M) hQ
  have hQp : IsPGroup p ↥Q := (isPGroup_Op p hp M).to_le hQ.1
  obtain ⟨v₀, hv₀, hv₀1, hQv⟩ := exists_v0 h1123 hC hQ hV
  suffices hmain : centralizer ({v₀} : Set G) ≤ M by
    intro v hv hv1
    obtain ⟨c, hc, hcv⟩ := hV.conj v₀ hv₀ hv₀1 v hv hv1
    intro x hx
    have hx' : c⁻¹ * x * c ∈ centralizer ({v₀} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxv : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.mp hx
      rw [← hcv] at hxv
      calc c⁻¹ * x * c * v₀ = c⁻¹ * (x * (c * v₀ * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * v₀ * c⁻¹) * x) * c := by rw [hxv]
        _ = v₀ * (c⁻¹ * x * c) := by group
    have hcM : c ∈ M := hC.cen_le hc
    have h1 : c * (c⁻¹ * x * c) * c⁻¹ ∈ M := M.mul_mem (M.mul_mem hcM (hmain hx')) (M.inv_mem hcM)
    have h2 : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rwa [h2] at h1
  have hz0 : v₀ * z = z * v₀ := hV.comm_z hv₀
  have hzv₀ : z ∈ centralizer ({v₀} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hz0.symm
  set Qv : Subgroup G := Q ⊓ centralizer ({v₀} : Set G) with hQv_def
  have hzQ : z ∈ normalizer (Q : Set G) := hQn hC.z_mem
  have hzQv : z ∈ normalizer (Qv : Set G) := mem_normalizer_inf hzQ (Subgroup.le_normalizer hzv₀)
  set X₀ : Subgroup G := ⁅Qv, zpowers z⁆ with hX₀
  have hX₀Qv : X₀ ≤ Qv := commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzQv)
  have hX₀Q : X₀ ≤ Q := hX₀Qv.trans inf_le_left
  have hX₀0 : X₀ ≠ ⊥ := by
    intro h
    apply hQv
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers z)))
  have hX₀z : z ∈ normalizer (X₀ : Set G) := le_normalizer_commutator_zpowers hzQv (mem_Cen_self z)
  have hX₀c : ⁅X₀, zpowers z⁆ = X₀ :=
    commutator_zpowers_idem (A := Qv) hC.orderOf_z hp hC.p_ne_two (hQp.to_le inf_le_left) hzQv
  have hX₀N : NF z M X₀ := prop6_9_clean h69 hC hQ X₀ hX₀Q hX₀0 hX₀z
  obtain ⟨b, hb, hbp⟩ := exists_prime_ne_of_twoPrimes hC.twoPrimes p
  have hbF : Op b M ≠ ⊥ := Op_ne_bot_of_dvd hb.1 hb.2
  have hb2 : b ≠ 2 := fun h => hbF (h ▸ Op_two_eq_bot hC.hyp hC.mem)
  obtain ⟨y, hyR, hy1, hyv⟩ := exists_ne_one_centralizer h1123 hC hV hb.1 hb2 (isPGroup_Op b hb.1 M)
    (le_normalizer_Op b M) hbF hv₀ hv₀1
  set E₁ : Subgroup G := Ep p M ⊓ centralizer ({v₀} : Set G) with hE₁
  have hE₁0 : E₁ ≠ ⊥ := by
    intro h
    have hyE : y ∈ E₁ := ⟨Op_le_Ep hb.1 hp hbp M hyR, Subgroup.mem_centralizer_singleton_iff.mpr hyv⟩
    rw [h, Subgroup.mem_bot] at hyE
    exact hy1 hyE
  have hzE₁ : z ∈ normalizer (E₁ : Set G) :=
    mem_normalizer_inf (le_normalizer_Ep p M hC.z_mem) (Subgroup.le_normalizer hzv₀)
  have hE₁N : NF z M E₁ := h66 G z k S M p hC E₁ inf_le_left hE₁0 hzE₁
  obtain ⟨N, hN, hCN⟩ : ∃ N : Subgroup G, IsCoatom N ∧ centralizer ({v₀} : Set G) ≤ N := by
    rcases eq_top_or_exists_le_coatom (centralizer ({v₀} : Set G)) with h | h
    · exact absurd h (centralizer_ne_top hC hv₀1)
    · exact h
  have hH : Hyp62 z M N X₀ E₁ p := ⟨hN, hCN hzv₀, hp, (hX₀Qv.trans inf_le_right).trans hCN,
    inf_le_right.trans hCN, hX₀c, hX₀Q.trans hQ.1, hX₀N, inf_le_left, hE₁N⟩
  obtain ⟨⟨hFsN, -⟩, hN2, hc⟩ := h62 G z k S M p hC N X₀ E₁ p hH
  obtain ⟨ha, hb', -⟩ := hB12 G hC.ctx.std.kps N M hN ⊥ bot_le (inf_le_left.trans hFsN)
  have hδ : Fpi {q | q.Prime ∧ q ∣ Nat.card ↥(Fm N)} M ≤ N := by
    rcases hb' with ⟨q, hq, hqP⟩ | h
    · exact absurd (hqP.to_le (Fm_le_Fs N)) (not_isPGroup_of_twoPrimes hN2 hq)
    · exact h
  have hOq : ∀ q : ℕ, q.Prime → Op q M ≤ N := by
    intro q hq
    by_cases hq0 : Op q M = ⊥
    · rw [hq0]
      exact bot_le
    · by_cases hqd : q ∣ Nat.card ↥(Fm N)
      · calc Op q M = Op q (Fm M) := (Op_Fm_eq hq M).symm
          _ ≤ Fpi {q | q.Prime ∧ q ∣ Nat.card ↥(Fm N)} M := le_iSup₂_of_le q ⟨hq, hqd⟩ le_rfl
          _ ≤ N := hδ
      · exfalso
        have hq2 : q ≠ 2 := fun h => hq0 (h ▸ Op_two_eq_bot hC.hyp hC.mem)
        obtain ⟨y, hyR, hy1, hyv⟩ := exists_ne_one_centralizer h1123 hC hV hq hq2 (isPGroup_Op q hq M)
          (le_normalizer_Op q M) hq0 hv₀ hv₀1
        have hyN : y ∈ N := hCN (Subgroup.mem_centralizer_singleton_iff.mpr hyv)
        have hle : Op q M ≤ Fpi {q | q.Prime ∧ ¬ q ∣ Nat.card ↥(Fm N)} M :=
          calc Op q M = Op q (Fm M) := (Op_Fm_eq hq M).symm
            _ ≤ _ := le_iSup₂_of_le q ⟨hq, hqd⟩ le_rfl
        have hyF : y ∈ Fpi {q | q.Prime ∧ ¬ q ∣ Nat.card ↥(Fm N)} M ⊓ N := ⟨hle hyR, hyN⟩
        rw [ha, Subgroup.mem_bot] at hyF
        exact hy1 hyF
  have hFN : Fm M ≤ N := Fm_le_of_forall hOq
  have hMN : Links M N := ⟨⊥, bot_le, inf_le_left.trans ((hC.Fs_eq hC.mem).le.trans hFN)⟩
  have hMeq : M = N := hc hMN
  rw [hMeq]
  exact hCN

end L72

end CFSG.GH74.GLS.Stage2.Bender.Thm1

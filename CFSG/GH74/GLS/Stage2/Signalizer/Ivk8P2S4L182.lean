module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt17
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt18
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L182Act
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L182Fit
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L182Lay
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L182Perf
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L182Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182
open scoped commutatorElement

theorem L182.one_le_pRank_of_involution {Q : Type} [Group Q] [Finite Q] {a : Q}
    (ha : a * a = 1) (h1 : a ≠ 1) : 1 ≤ CFSG.pRank 2 Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : a ^ 2 = 1 := by rw [pow_two]; exact ha
  have hord : orderOf a = 2 := orderOf_eq_prime ha2 h1
  have hel : IsElementaryAbelian 2 ↥(Subgroup.zpowers a) :=
    { is_comm := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2
        apply Subtype.ext
        show (x : Q) ^ 2 = 1
        rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha2, one_zpow] }
  exact RankThree.Coprime.le_pRank_of_isElementaryAbelian one_lt_two hel (k := 1)
    (by rw [Nat.card_zpowers, hord]; norm_num)

theorem lemma18_2_of (h171 : Prop17_1) (h176 : Lemma17_6) (hO2 : O2RankOne)
    (hL31 : Lemma31Narrow) (hSch : P34.GHSchreier) : Lemma18_2 := by
  intro G _ _ z k S M p E t hctx X hXM hXne hinv hXE
  have hfail : Fail17 G z k S M := hctx.base
  have hctx17 : Ctx17 G z k S M := hfail.ctx
  have hctx2 : Stage2Ctx G z k S := hctx17.ctx
  obtain ⟨hMC, -⟩ := h171 G z k S M hctx17 hfail.fail
  have hMtop : M ≠ ⊤ := hctx17.ne_top
  have hzM : z ∈ M := hctx17.cen_le (mem_Cen_self z)
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.odd
  have : Fact p.Prime := ⟨hp⟩
  have hXperf : ⁅X, X⁆ = X := by
    have := Em_perfect X
    rwa [hXE] at this
  have : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.2 hXperf
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).2 hXne
  have hWV : pPrimeCoreOf 2 (Vof M E) ≤ Vof M E := Subgroup.map_subtype_le _
  have hVF : Vof M E ≤ Fm M := inf_le_left
  have hFM : Fm M ≤ M := Subgroup.map_subtype_le _
  have hcommW : ∀ w ∈ pPrimeCoreOf 2 (Vof M E), ∀ x ∈ X, x * w = w * x := by
    intro w hw x hx
    have hwF : w ∈ Fm M := hVF (hWV hw)
    have key := centralizes_of_comm_mem (X := X) (N := Fm M) hXperf
      (fun y hy hyF x hx => fm_inf_central hXM hXE hy hyF hx) (v := w)
      (fun x hx => (Subgroup.mem_normalizer_iff.1 (hinv w hw) x).1 hx)
      (fun x hx => by
        have h1 : w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) := by group
        rw [h1]
        exact (Fm M).mul_mem hwF (Fm_conj_mem M (hXM hx) ((Fm M).inv_mem hwF))) x hx
    exact (mul_inv_eq_iff_eq_mul.1 key).symm
  have hconjW : ∀ w ∈ pPrimeCoreOf 2 (Vof M E), ∀ x ∈ X, x * w * x⁻¹ = w :=
    fun w hw x hx => mul_inv_eq_iff_eq_mul.2 (hcommW w hw x hx)
  have hnonsolv : ¬ Group.IsSolvable ↥(Cen z) := by
    intro hsol
    rw [← hMC] at hsol
    have hXsolv : Group.IsSolvable ↥X :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXM)
    exact Group.IsPerfect.not_isSolvable (G := ↥X) hXsolv
  have hrank : pRank 2 ↥(Op 2 M) = 1 := by
    have := hO2 G z k S hctx2 hnonsolv
    rwa [← hMC] at this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOp2 : ∀ x ∈ X, ∀ y ∈ Op 2 M, x * y * x⁻¹ = y :=
    centralizes_of_pRank_one (isPGroup_Op 2 M) hrank hXperf
      (fun x hx q hq => Op_conj_mem 2 M (hXM hx) hq)
  have hOpQ : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ x ∈ X, ∀ y ∈ Op q M, x * y * x⁻¹ = y := by
    intro q hq hq2 hqp x hx y hy
    have : Fact q.Prime := ⟨hq⟩
    have hT : Op q M ≤ pPrimeCoreOf 2 (Vof M E) := by
      refine le_pPrimeCoreOf_of_odd ?_ ?_ (odd_card_of_isPGroup hq2 (isPGroup_Op q M))
      · refine le_inf (Op_le_Fm q M) ?_
        intro y hy e he
        exact (op_commute_of_ne hq hp hqp M hy (hctx.E_le he)).symm
      · intro v hv n hn
        exact Op_conj_mem q M (hFM (hVF hv)) hn
    exact hconjW y (hT hy) x hx
  have hOpP : ∀ x ∈ X, ∀ y ∈ Op p M, x * y * x⁻¹ = y := by
    have hTle : Op p M ⊓ centralizer (E : Set G) ≤ pPrimeCoreOf 2 (Vof M E) := by
      refine le_pPrimeCoreOf_of_odd ?_ ?_ ?_
      · exact le_inf (inf_le_left.trans (Op_le_Fm p M)) inf_le_right
      · intro v hv n hn
        refine Subgroup.mem_inf.2 ⟨Op_conj_mem p M (hFM (hVF hv)) hn.1, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        have hve : v * e * v⁻¹ = e := mul_inv_eq_iff_eq_mul.2
          ((Subgroup.mem_centralizer_iff.1 hv.2 e he).symm)
        have hne : n * e = e * n := (Subgroup.mem_centralizer_iff.1 hn.2 e he).symm
        calc e * (v * n * v⁻¹) = (v * e * v⁻¹) * (v * n * v⁻¹) := by rw [hve]
          _ = v * (e * n) * v⁻¹ := by group
          _ = v * (n * e) * v⁻¹ := by rw [hne]
          _ = (v * n * v⁻¹) * (v * e * v⁻¹) := by group
          _ = (v * n * v⁻¹) * e := by rw [hve]
      · have hle : Op p M ⊓ centralizer (E : Set G) ≤ Op p M := inf_le_left
        exact odd_card_of_isPGroup hp2 ((isPGroup_Op p M).of_injective (Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle))
    refine centralizes_of_trivial_on_centralizer (E := E) (isPGroup_Op p M) hXperf
      (fun x hx y hy => Op_conj_mem p M (hXM hx) hy) hctx.E_le
      (fun a ha b hb => congrArg Subtype.val
        (hctx.E_elem.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)) ?_
    intro y hyP hyc x hx
    have hyW : y ∈ pPrimeCoreOf 2 (Vof M E) :=
      hTle ⟨hyP, Subgroup.mem_centralizer_iff.2 fun e he => hyc e he⟩
    exact hconjW y hyW x hx
  have hOp : ∀ r : ℕ, r.Prime → ∀ x ∈ X, ∀ y ∈ Op r M, x * y * x⁻¹ = y := by
    intro r hr
    by_cases hr2 : r = 2
    · rw [hr2]; exact hOp2
    · by_cases hrp : r = p
      · rw [hrp]; exact hOpP
      · exact hOpQ r hr hr2 hrp
  have hFm : ∀ x ∈ X, ∀ y ∈ Fm M, x * y * x⁻¹ = y := fm_centralized_of_op hOp
  have hXEm : X ≤ Em M := le_Em_of_perfect hL31 hSch hctx2 hMtop hzM hXM hXperf hFm
  have hEne : Em M ≠ ⊥ := fun h => hXne (le_bot_iff.1 (h ▸ hXEm))
  obtain ⟨⟨hrE, hzE, -⟩, -⟩ := h176 G z k S M hfail hEne
  obtain ⟨u, hu⟩ := exists_orderOf_two_of_perfect (A := ↥X)
  have hu2 : (u : G) * u = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu, pow_two] at this
    exact congrArg Subtype.val this
  have hzord : orderOf z = 2 := hctx2.orderOf_z
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzord, pow_two] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  have hu1 : (u : G) ≠ 1 := by
    intro h
    have : u = 1 := Subtype.ext h
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hucomm : (u : G) * z = z * (u : G) := by
    have huM : (u : G) ∈ Cen z := hMC ▸ hXM u.2
    exact Subgroup.mem_centralizer_singleton_iff.1 huM
  have huz : (u : G) = z := by
    by_contra hne
    have h2 := two_le_pRank_of_involutions (Q := ↥(Em M)) (a := ⟨u, hXEm u.2⟩) (b := ⟨z, hzE⟩)
      (Subtype.ext hu2) (Subtype.ext hz2) (Subtype.ext hucomm)
      (fun h => hu1 (congrArg Subtype.val h)) (fun h => hz1 (congrArg Subtype.val h))
      (fun h => hne (congrArg Subtype.val h))
    omega
  have hzX : z ∈ X := huz ▸ u.2
  refine ⟨le_antisymm ((pRank_le_of_le hXEm).trans hrE.le) ?_, hzX⟩
  exact L182.one_le_pRank_of_involution (Q := ↥X) (a := ⟨z, hzX⟩) (Subtype.ext hz2)
    (fun h => hz1 (congrArg Subtype.val h))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

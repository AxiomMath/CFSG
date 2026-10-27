module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadSyl
public import CFSG.ClassicalInvolution.Q3.Q3DBFuzzyEdge
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3DB
open scoped commutatorElement MatrixGroups

section Structures

variable {G : Type} [Group G]

structure EdgeSetup (K : Subgroup G) (z : G) (M N : Subgroup G) (a t : G) : Prop where
  member : IsClassicalMember3 K z
  intrinsic : IsIntrinsicU (.sl2 3 1) K z
  hypΩ : HypOmegaGen (CoreAssembly.conjClass K)
  memM : M ∈ CoreAssembly.conjClass K
  nbr : N ∈ omegaNbr (CoreAssembly.conjClass K) M
  invM : IsClassicalMember3 M a
  invN : IsClassicalMember3 N t
  ne : a ≠ t

structure SylowPair (M N : Subgroup G) (a t : G) (R R' : Subgroup G) : Prop where
  syl_R : IsSylow2In R N
  syl_R' : IsSylow2In R' M
  card_R : Nat.card R = 8
  card_R' : Nat.card R' = 8
  mem_t : t ∈ R
  mem_a : a ∈ R'
  norm_R : R ≤ Subgroup.normalizer (M : Set G)
  norm_R' : R' ≤ Subgroup.normalizer (N : Set G)
  commutes : Commutes R R'
  inf_eq_bot : R ⊓ R' = ⊥
  card_sup : Nat.card ↥(R ⊔ R') = 64
  invol : ∀ x ∈ R ⊔ R', x * x = 1 → x = 1 ∨ x = a ∨ x = t ∨ x = a * t

end Structures


section Edge

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {M N : Subgroup G} {a t : G}

theorem ne_of_not_centralizes (ht : IsClassicalMember3 N t)
    (hbad : ¬ ∀ x ∈ oddCoreOf N, a * x = x * a) : a ≠ t := by
  intro hat
  apply hbad
  intro x hx
  have hxN : x ∈ N := oddCoreIn_le N hx
  have hxc : x ∈ Subgroup.centralizer ({t} : Set G) := isSubnormal_le ht.subnormal hxN
  rw [hat]
  exact (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm

namespace EdgeSetup

theorem memN (h : EdgeSetup K z M N a t) : N ∈ CoreAssembly.conjClass K := h.nbr.1

theorem ne_MN (h : EdgeSetup K z M N a t) : N ≠ M := h.nbr.2.1

theorem uniqueM (h : EdgeSetup K z M N a t) : IsUniqueInvolution M a :=
  (IsClassicalMemberU.ofQ3 h.invM).isUniqueInvolution (MemberType.cert_sl2 3 1)

theorem uniqueN (h : EdgeSetup K z M N a t) : IsUniqueInvolution N t :=
  (IsClassicalMemberU.ofQ3 h.invN).isUniqueInvolution (MemberType.cert_sl2 3 1)

theorem intrinsic' (h : EdgeSetup K z M N a t) :
    oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K :=
  h.intrinsic (MemberType.isSolvableType_sl2.mpr (by norm_num))

theorem oddCoreIn_M (h : EdgeSetup K z M N a t) :
    oddCoreIn M = oddCoreIn (Subgroup.centralizer ({a} : Set G)) :=
  oddCoreIn_eq_of_intrinsic3 h.invM
    (oddCoreIn_centralizer_le_of_mem_conjClass h.member h.intrinsic' h.memM h.invM)

theorem oddCoreIn_N (h : EdgeSetup K z M N a t) :
    oddCoreIn N = oddCoreIn (Subgroup.centralizer ({t} : Set G)) :=
  oddCoreIn_eq_of_intrinsic3 h.invN
    (oddCoreIn_centralizer_le_of_mem_conjClass h.member h.intrinsic' h.memN h.invN)

theorem exists_sylowPair (h : EdgeSetup K z M N a t) :
    ∃ R R' : Subgroup G, SylowPair M N a t R R' := by
  obtain ⟨R, hRsyl, hR8, hRM⟩ := exists_sylow_of_mem_omegaNbr h.member h.nbr
  have hUM := h.uniqueM
  have hUN := h.uniqueN
  have htR : t ∈ R := mem_of_isSylow2In_of_isUniqueInvolution hUN hRsyl
  obtain ⟨R', hR'syl, hRnorm'⟩ := badEdge_exists_isSylow2In_normalized hRsyl.2.1 hRM
  obtain ⟨e⟩ := h.invM.nonempty_equiv
  have hR'8 : Nat.card R' = 8 := Q3T6.natCard_sylow_eq_eight e hR'syl
  have haR' : a ∈ R' := mem_of_isSylow2In_of_isUniqueInvolution hUM hR'syl
  have hfuzz := fuzzy_symm_of_mem_omegaNbr h.member h.nbr h.invM h.invN
  have htc : ∀ s ∈ R', t * s = s * t := by
    intro s hs
    have h1 : t * s * t⁻¹ ∈ R' := (Subgroup.mem_normalizer_iff.mp (hRnorm' htR) s).mp hs
    have h2 : ⁅t, s⁆ ∈ oddCoreOf M := hfuzz.2 s (hR'syl.1 hs)
    have h3 : ⁅t, s⁆ ∈ R' := by
      have e1 : ⁅t, s⁆ = (t * s * t⁻¹) * s⁻¹ := commutatorElement_def t s
      rw [e1]
      exact R'.mul_mem h1 (R'.inv_mem hs)
    have h4 : ⁅t, s⁆ = 1 := by
      have hs2 : IsPGroup 2 (Subgroup.zpowers ⁅t, s⁆) :=
        hR'syl.2.1.to_le (Subgroup.zpowers_le.mpr h3)
      exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard M) h2 hs2
    exact commutatorElement_eq_one_iff_mul_comm.mp h4
  have hR'N : R' ≤ Subgroup.normalizer (N : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer h.hypΩ h.memN h.memM h.ne_MN hUN hR'syl.1
      hR'syl.2.1 (by omega)
      (fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (htc s hs).symm)
  have hbot : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ M → P ≤ N → P = ⊥ :=
    fun P hP hPM hPN => badEdge_eq_bot_of_le_inf hUM hUN h.ne hP hPM hPN
  have hcomm : Commutes R R' := by
    intro r hr s hs
    have h1 : r * s * r⁻¹ ∈ R' := (Subgroup.mem_normalizer_iff.mp (hRnorm' hr) s).mp hs
    have hcR' : ⁅r, s⁆ ∈ R' := by
      have e1 : ⁅r, s⁆ = (r * s * r⁻¹) * s⁻¹ := commutatorElement_def r s
      rw [e1]
      exact R'.mul_mem h1 (R'.inv_mem hs)
    have hcN : ⁅r, s⁆ ∈ N := by
      have hsN : s * r⁻¹ * s⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hR'N hs) r⁻¹).mp (N.inv_mem (hRsyl.1 hr))
      have e1 : ⁅r, s⁆ = r * (s * r⁻¹ * s⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e1]
      exact N.mul_mem (hRsyl.1 hr) hsN
    have hzp : IsPGroup 2 (Subgroup.zpowers ⁅r, s⁆) :=
      hR'syl.2.1.to_le (Subgroup.zpowers_le.mpr hcR')
    have hzb : Subgroup.zpowers ⁅r, s⁆ = ⊥ :=
      hbot _ hzp (Subgroup.zpowers_le.mpr (hR'syl.1 hcR')) (Subgroup.zpowers_le.mpr hcN)
    have hc1 : ⁅r, s⁆ = 1 := by
      have hmem : ⁅r, s⁆ ∈ Subgroup.zpowers ⁅r, s⁆ := Subgroup.mem_zpowers _
      rw [hzb] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hc1
  have hinf : R ⊓ R' = ⊥ :=
    hbot _ (hRsyl.2.1.to_le inf_le_left) (inf_le_right.trans hR'syl.1)
      (inf_le_left.trans hRsyl.1)
  have hcard : Nat.card ↥(R ⊔ R') = 64 := by
    have h1 := badEdge_natCard_sup_mul_natCard_inf hRnorm'
    rw [inf_comm, hinf, Subgroup.card_bot, hR'8, hR8] at h1
    rw [sup_comm]
    omega
  have hinvol : ∀ x ∈ R ⊔ R', x * x = 1 → x = 1 ∨ x = a ∨ x = t ∨ x = a * t := by
    intro x hx hx2
    obtain ⟨r, hr, s, hs, rfl⟩ := badEdge_exists_mul_of_mem_sup hcomm hx
    have hrs : r * s = s * r := hcomm r hr s hs
    have h2 : r * r * (s * s) = 1 := by
      calc r * r * (s * s) = r * (r * s) * s := by group
        _ = r * (s * r) * s := by rw [hrs]
        _ = r * s * (r * s) := by group
        _ = 1 := hx2
    have hrr : r * r ∈ R' := by
      have : r * r = (s * s)⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [this]
      exact R'.inv_mem (R'.mul_mem hs hs)
    have hrr1 : r * r = 1 := by
      have hmem : r * r ∈ R ⊓ R' := ⟨R.mul_mem hr hr, hrr⟩
      rw [hinf] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hss1 : s * s = 1 := by
      rw [hrr1, one_mul] at h2
      exact h2
    have hta : t * a = a * t := hcomm t htR a haR'
    rcases hUN.unique r (hRsyl.1 hr) hrr1 with hr1 | hr1 <;>
      rcases hUM.unique s (hR'syl.1 hs) hss1 with hs1 | hs1
    · left
      rw [hr1, hs1, one_mul]
    · right; left
      rw [hr1, hs1, one_mul]
    · right; right; left
      rw [hr1, hs1, mul_one]
    · right; right; right
      rw [hr1, hs1, hta]
  exact ⟨R, R', ⟨hRsyl, hR'syl, hR8, hR'8, htR, haR', hRM, hR'N, hcomm, hinf, hcard, hinvol⟩⟩

theorem symm (h : EdgeSetup K z M N a t) : EdgeSetup K z N M t a := by
  obtain ⟨R, R', hp⟩ := h.exists_sylowPair
  refine ⟨h.member, h.intrinsic, h.hypΩ, h.memN, ?_, h.invN, h.invM, h.ne.symm⟩
  exact (show M ∈ CoreAssembly.conjClass K ∧ M ≠ N ∧ ∃ P ∈ RSet (CoreAssembly.conjClass K),
      P ≤ M ∧ P ≤ Subgroup.normalizer (N : Set G) from
    ⟨h.memM, h.ne_MN.symm, R', mem_RSet_of_isSylow2In h.memM hp.syl_R', hp.syl_R'.1,
      hp.norm_R'⟩)

theorem theta_le_centralizer (h : EdgeSetup K z M N a t) :
    N ⊔ M ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.centralizer ({t} : Set G) :=
  sup_le (isSubnormal_le h.invN.subnormal) inf_le_right

theorem theta_le_normalizer_oddCore (h : EdgeSetup K z M N a t) :
    N ⊔ M ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (oddCoreOf N : Set G) := by
  have h1 : Subgroup.normalizer (oddCoreOf N : Set G) =
      Subgroup.normalizer (oddCoreIn (Subgroup.centralizer ({t} : Set G)) : Set G) := by
    show Subgroup.normalizer (oddCoreIn N : Set G) = _
    rw [h.oddCoreIn_N]
  rw [h1]
  exact h.theta_le_centralizer.trans (normalizer_oddCoreIn _)

end EdgeSetup

namespace SylowPair

variable {R R' : Subgroup G}

theorem commutator_le_oddCore (hp : SylowPair M N a t R R') (hM : IsClassicalMember3 M a) :
    ∀ k ∈ M, ∀ r ∈ R, ⁅r, k⁆ ∈ oddCoreOf M := by
  obtain ⟨e⟩ := hM.nonempty_equiv
  exact badEdge_centSylow_three_modOdd (V := R) e hp.syl_R'
    (fun y hy => mem_normalizer_iff_conjSub_eq.mp (hp.norm_R hy))
    (fun r' hr' v hv => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hp.commutes v hv r' hr')]
      exact (oddCoreOf M).one_mem)

theorem isPGroup_sup (hp : SylowPair M N a t R R') : IsPGroup 2 ↥(R ⊔ R') :=
  IsPGroup.of_card (n := 6) (by rw [hp.card_sup]; norm_num)

end SylowPair

end Edge

section Theta

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {M N : Subgroup G} {a t : G}

theorem SylowPair.commutator_centM_mem_oddCore (h : EdgeSetup K z M N a t)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hBelow : CIT3Below (Nat.card G)) {R R' : Subgroup G}
    (hp : SylowPair M N a t R R') :
    ∀ x ∈ M ⊓ Subgroup.centralizer ({t} : Set G), ∀ r ∈ R, ⁅x, r⁆ ∈ oddCoreOf N := by
  intro x hx r hr
  have hxM : x ∈ M := hx.1
  have hxc : x ∈ Subgroup.centralizer ({t} : Set G) := hx.2
  have h1 : ⁅r, x⁆ ∈ oddCoreOf M := hp.commutator_le_oddCore h.invM x hxM r hr
  have hNle : N ≤ Subgroup.centralizer ({t} : Set G) := isSubnormal_le h.invN.subnormal
  have hrc : r ∈ Subgroup.centralizer ({t} : Set G) := hNle (hp.syl_R.1 hr)
  have h2 : ⁅r, x⁆ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [commutatorElement_def]
    exact (Subgroup.centralizer ({t} : Set G)).mul_mem
      ((Subgroup.centralizer ({t} : Set G)).mul_mem
        ((Subgroup.centralizer ({t} : Set G)).mul_mem hrc hxc)
        ((Subgroup.centralizer ({t} : Set G)).inv_mem hrc))
      ((Subgroup.centralizer ({t} : Set G)).inv_mem hxc)
  have h3 : ⁅r, x⁆ ∈ Subgroup.centralizer ({t} : Set G) ⊓ oddCoreIn M := ⟨h2, h1⟩
  have h4 := centralizer_inf_oddCoreIn_le_of_mem_omegaNbr hnab h.member h.intrinsic hBelow
    h.symm.nbr h.invN h.invM h3
  have h5 : ⁅r, x⁆ ∈ oddCoreIn N := by
    rw [h.oddCoreIn_N]
    exact h4
  have hinv : ⁅x, r⁆ = ⁅r, x⁆⁻¹ := (commutatorElement_inv (g₁ := r) (g₂ := x)).symm
  rw [hinv]
  exact (oddCoreOf N).inv_mem h5

namespace EdgeSetup

theorem conjSub_eq_of_mem_centM (h : EdgeSetup K z M N a t) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hBelow : CIT3Below (Nat.card G)) :
    ∀ x ∈ M ⊓ Subgroup.centralizer ({t} : Set G), conjSub x N = N := by
  obtain ⟨R, R', hp⟩ := h.exists_sylowPair
  intro x hx
  have hconjR : conjSub x R ≤ N := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have hcm : ⁅x, x⁻¹ * y * x⁆ ∈ oddCoreOf N :=
      hp.commutator_centM_mem_oddCore h hnab hBelow x hx _ hy
    have e1 : y = ⁅x, x⁻¹ * y * x⁆ * (x⁻¹ * y * x) := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    exact N.mul_mem (oddCoreIn_le N hcm) (hp.syl_R.1 hy)
  have hA2 : IsPGroup 2 (conjSub x R) := isPGroup_conjSub x hp.syl_R.2.1
  have hA8 : Nat.card (conjSub x R) = 8 :=
    (Nat.card_congr
      (Subgroup.equivMapOfInjective R (MulAut.conj x).toMonoidHom
        (MulAut.conj x).injective).toEquiv).symm.trans hp.card_R
  have hN' : conjSub x N ∈ CoreAssembly.conjClass K := h.hypΩ.conjInvariant x N h.memN
  have hAN' : conjSub x R ≤ conjSub x N := conjSub_mono hp.syl_R.1
  exact (Sec6Gen.eq_of_le_of_le h.hypΩ h.memN hN' hA2 (by omega) hconjR hAN').symm

theorem commutator_centM_le_oddCore (h : EdgeSetup K z M N a t)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hBelow : CIT3Below (Nat.card G)) :
    ∀ x ∈ M ⊓ Subgroup.centralizer ({t} : Set G), ∀ n ∈ N, ⁅x, n⁆ ∈ oddCoreOf N := by
  obtain ⟨R, R', hp⟩ := h.exists_sylowPair
  obtain ⟨e⟩ := h.invN.nonempty_equiv
  intro x hx n hn
  exact badEdge_centSylow_three_modOdd (V := M ⊓ Subgroup.centralizer ({t} : Set G)) e hp.syl_R
    (fun y hy => h.conjSub_eq_of_mem_centM hnab hBelow y hy)
    (fun r hr v hv => hp.commutator_centM_mem_oddCore h hnab hBelow v hv r hr) n hn x hx

theorem conjSub_eq_of_mem_centN (h : EdgeSetup K z M N a t) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hBelow : CIT3Below (Nat.card G)) :
    ∀ x ∈ N ⊓ Subgroup.centralizer ({a} : Set G), conjSub x M = M :=
  h.symm.conjSub_eq_of_mem_centM hnab hBelow

theorem commutator_centN_le_oddCore (h : EdgeSetup K z M N a t)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hBelow : CIT3Below (Nat.card G)) :
    ∀ x ∈ N ⊓ Subgroup.centralizer ({a} : Set G), ∀ m ∈ M, ⁅x, m⁆ ∈ oddCoreOf M :=
  h.symm.commutator_centM_le_oddCore hnab hBelow

theorem theta_le_normalizer (h : EdgeSetup K z M N a t) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hBelow : CIT3Below (Nat.card G)) :
    N ⊔ M ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N : Set G) :=
  sup_le Subgroup.le_normalizer
    (fun x hx => mem_normalizer_iff_conjSub_eq.mpr (h.conjSub_eq_of_mem_centM hnab hBelow x hx))

theorem exists_mul_centM (h : EdgeSetup K z M N a t) :
    ∀ x ∈ M, ∃ i ∈ M ⊓ Subgroup.centralizer ({t} : Set G), ∃ n ∈ oddCoreOf M, x = i * n :=
  eq_mul_of_mem_omegaNbr h.member h.intrinsic h.symm.nbr h.invN h.invM

theorem oddCore_inf_eq (h : EdgeSetup K z M N a t) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hBelow : CIT3Below (Nat.card G)) :
    oddCoreOf M ⊓ oddCoreOf N = oddCoreOf M ⊓ Subgroup.centralizer ({t} : Set G) ∧
      oddCoreOf M ⊓ oddCoreOf N = oddCoreOf N ⊓ Subgroup.centralizer ({a} : Set G) := by
  have hNc : N ≤ Subgroup.centralizer ({t} : Set G) := isSubnormal_le h.invN.subnormal
  have hMc : M ≤ Subgroup.centralizer ({a} : Set G) := isSubnormal_le h.invM.subnormal
  have hAM : oddCoreOf M ≤ M := oddCoreIn_le M
  have hTN : oddCoreOf N ≤ N := oddCoreIn_le N
  refine ⟨le_antisymm (le_inf inf_le_left (inf_le_right.trans (hTN.trans hNc))) ?_,
    le_antisymm (le_inf inf_le_right (inf_le_left.trans (hAM.trans hMc))) ?_⟩
  · intro x hx
    have hxm : x ∈ Subgroup.centralizer ({t} : Set G) ⊓ oddCoreIn M := ⟨hx.2, hx.1⟩
    have h1 := centralizer_inf_oddCoreIn_le_of_mem_omegaNbr hnab h.member h.intrinsic hBelow
      h.symm.nbr h.invN h.invM hxm
    refine ⟨hx.1, ?_⟩
    have h2 : x ∈ oddCoreIn N := by
      rw [h.oddCoreIn_N]
      exact h1
    exact h2
  · intro x hx
    have hxm : x ∈ Subgroup.centralizer ({a} : Set G) ⊓ oddCoreIn N := ⟨hx.2, hx.1⟩
    have h1 := centralizer_inf_oddCoreIn_le_of_mem_omegaNbr hnab h.member h.intrinsic hBelow
      h.nbr h.invM h.invN hxm
    refine ⟨?_, hx.1⟩
    have h2 : x ∈ oddCoreIn M := by
      rw [h.oddCoreIn_M]
      exact h1
    exact h2

theorem card_oddCore_eq (h : EdgeSetup K z M N a t) :
    Nat.card ↥(oddCoreOf M) = Nat.card ↥(oddCoreOf N) := by
  obtain ⟨g, hg0⟩ := h.memM
  obtain ⟨g', hg0'⟩ := h.memN
  have hg : conjSub g K = M := hg0
  have hg' : conjSub g' K = N := hg0'
  have hcard : ∀ (g : G) (X : Subgroup G), Nat.card ↥(conjSub g X) = Nat.card ↥X := fun g X =>
    (Nat.card_congr (Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm
  show Nat.card ↥(oddCoreIn M) = Nat.card ↥(oddCoreIn N)
  rw [← hg, ← hg', Bootstrap.oddCoreIn_conjSub_eq, Bootstrap.oddCoreIn_conjSub_eq,
    hcard, hcard]

theorem centralizes_iff_oddCore_eq (h : EdgeSetup K z M N a t) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hBelow : CIT3Below (Nat.card G)) :
    (∀ x ∈ oddCoreOf N, a * x = x * a) ↔ oddCoreOf M = oddCoreOf N := by
  refine (oddCoreIn_le_oddCoreIn_iff hnab h.member h.intrinsic hBelow h.memM h.nbr h.invM
    h.invN).symm.trans ?_
  constructor
  · intro hle
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq h.card_oddCore_eq)).symm
  · intro heq
    exact heq.symm.le

theorem not_le_of_not_centralizes (h : EdgeSetup K z M N a t) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hBelow : CIT3Below (Nat.card G)) (hbad : ¬ ∀ x ∈ oddCoreOf N, a * x = x * a) :
    ¬ oddCoreOf N ≤ oddCoreOf M ∧ ¬ oddCoreOf M ≤ oddCoreOf N ∧
      ∃ x ∈ oddCoreOf M, t * x ≠ x * t := by
  have h1 : ¬ oddCoreOf N ≤ oddCoreOf M := fun hle =>
    hbad ((oddCoreIn_le_oddCoreIn_iff hnab h.member h.intrinsic hBelow h.memM h.nbr h.invM
      h.invN).mp hle)
  have h2 : ¬ oddCoreOf M ≤ oddCoreOf N := by
    intro hle
    have heq : oddCoreOf M = oddCoreOf N :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq h.card_oddCore_eq.symm)
    exact h1 heq.symm.le
  refine ⟨h1, h2, ?_⟩
  by_contra hcon
  push Not at hcon
  exact h2 ((oddCoreIn_le_oddCoreIn_iff hnab h.member h.intrinsic hBelow h.symm.memM
    h.symm.nbr h.invN h.invM).mpr hcon)

end EdgeSetup

end Theta

end CFSG.ClassicalInvolution.Q3.Q3AM

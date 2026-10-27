module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QSide
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QFive
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Normal
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QH0

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

structure PairCtx (X : Type) [Group X] [Finite X] (n : ℕ) (z s : X) (A A' : Subgroup X)
    (M : AhatModel X n A) (M' : AhatModel X n A') : Prop where
  hn : 8 ≤ n
  hz : orderOf z = 2
  hs : orderOf s = 2
  hzs : z * s = s * z
  hzA : z ∈ A
  hsA : s ∈ A'
  hAz : A ≤ centralizer ({z} : Set X)
  hNz : centralizer ({z} : Set X) ≤ normalizer (A : Set X)
  hAs : A' ≤ centralizer ({s} : Set X)
  hNs : centralizer ({s} : Set X) ≤ normalizer (A' : Set X)
  hz52 : ∀ r ∈ centralizer ({z} : Set X), orderOf r = 2 → CentModOdd A r →
    centralizer ({r} : Set X) = oddCoreOf (centralizer ({r} : Set X)) ⊔
      (centralizer ({z} : Set X) ⊓ centralizer ({r} : Set X))
  hs52 : ∀ r ∈ centralizer ({s} : Set X), orderOf r = 2 → CentModOdd A' r →
    centralizer ({r} : Set X) = oddCoreOf (centralizer ({r} : Set X)) ⊔
      (centralizer ({s} : Set X) ⊓ centralizer ({r} : Set X))
  hfix : fixCount (M.permX s) ≤ 3
  hfix' : fixCount (M'.permX z) ≤ 3
  htr : transCount (M.permX s) ≠ 3
  htr' : transCount (M'.permX z) ≠ 3
  hsgn : sign (M.permX s) = 1
  hsgn' : sign (M'.permX z) = 1

section QOf

variable {X : Type} [Group X]

theorem conj_mem_QOf {A : Subgroup X} {g c : X} (hg : g ∈ normalizer (A : Set X))
    (hc : c ∈ QOf A) : g * c * g⁻¹ ∈ QOf A := by
  obtain ⟨hcN, hcm⟩ := mem_QOf_iff.1 hc
  refine mem_QOf_iff.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hcN) (Subgroup.inv_mem _ hg),
    fun a ha => ?_⟩
  have h1 : g⁻¹ * a * g ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) a).1 ha
    simpa using this
  have e1 : ⁅a, g * c * g⁻¹⁆ = g * ⁅g⁻¹ * a * g, c⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e1]
  have h2 := hcm _ h1
  have hgO := mem_normalizer_oddCoreOf_of_mem_normalizer hg
  have := (Subgroup.mem_normalizer_iff.1 hgO _).1 h2
  simpa using this

end QOf

namespace PairCtx

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z s : X} {A A' : Subgroup X}
  {M : AhatModel X n A} {M' : AhatModel X n A'}

theorem swap (h : PairCtx X n z s A A' M M') : PairCtx X n s z A' A M' M :=
  ⟨h.hn, h.hs, h.hz, h.hzs.symm, h.hsA, h.hzA, h.hAs, h.hNs, h.hAz, h.hNz, h.hs52, h.hz52,
    h.hfix', h.hfix, h.htr', h.htr, h.hsgn', h.hsgn⟩

@[expose] def Qz (_ : PairCtx X n z s A A' M M') : Subgroup X :=
  centralizer ({z} : Set X) ⊓ QOf A

@[expose] def Qs (_ : PairCtx X n z s A A' M M') : Subgroup X :=
  centralizer ({s} : Set X) ⊓ QOf A'

@[expose] def R (h : PairCtx X n z s A A' M M') : Subgroup X := centralizer ({z} : Set X) ⊓ h.Qs

@[expose] def P (h : PairCtx X n z s A A' M M') : Subgroup X := centralizer ({s} : Set X) ⊓ h.Qz

theorem mem_Qz_iff (h : PairCtx X n z s A A' M M') {c : X} :
    c ∈ h.Qz ↔ c ∈ centralizer ({z} : Set X) ∧ CentModOdd A c :=
  ⟨fun hc => ⟨hc.1, (mem_QOf_iff.1 hc.2).2⟩,
    fun hc => ⟨hc.1, mem_QOf_iff.2 ⟨h.hNz hc.1, hc.2⟩⟩⟩

theorem mem_Qs_iff (h : PairCtx X n z s A A' M M') {c : X} :
    c ∈ h.Qs ↔ c ∈ centralizer ({s} : Set X) ∧ CentModOdd A' c :=
  h.swap.mem_Qz_iff

theorem mem_R_iff (h : PairCtx X n z s A A' M M') {c : X} :
    c ∈ h.R ↔ c ∈ centralizer ({z} : Set X) ∧ c ∈ centralizer ({s} : Set X) ∧
      CentModOdd A' c := by
  rw [R, Subgroup.mem_inf, h.mem_Qs_iff]

theorem mem_P_iff (h : PairCtx X n z s A A' M M') {c : X} :
    c ∈ h.P ↔ c ∈ centralizer ({s} : Set X) ∧ c ∈ centralizer ({z} : Set X) ∧
      CentModOdd A c :=
  h.swap.mem_R_iff

theorem s_mem_C (h : PairCtx X n z s A A' M M') : s ∈ centralizer ({z} : Set X) :=
  Subgroup.mem_centralizer_singleton_iff.2 h.hzs.symm

theorem z_mem_C (h : PairCtx X n z s A A' M M') : z ∈ centralizer ({s} : Set X) :=
  Subgroup.mem_centralizer_singleton_iff.2 h.hzs

theorem sq_s (h : PairCtx X n z s A A' M M') : s * s = 1 := by
  have := pow_orderOf_eq_one s
  rwa [h.hs, sq] at this

theorem sq_z (h : PairCtx X n z s A A' M M') : z * z = 1 := h.swap.sq_s

theorem s_mem_R (h : PairCtx X n z s A A' M M') : s ∈ h.R := by
  rw [mem_R_iff]
  refine ⟨h.s_mem_C, Subgroup.mem_centralizer_singleton_iff.2 rfl, fun a ha => ?_⟩
  have : ⁅a, s⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 (h.hAs ha))
  rw [this]
  exact one_mem _

theorem fixCount_one' (n : ℕ) : fixCount (1 : Perm (Fin n)) = n := by
  simp [fixCount]

theorem no_involution (h : PairCtx X n z s A A' M M') {r : X} (hrz : r ∈ h.Qz) (hrs : r ∈ h.Qs)
    (hr : orderOf r = 2) : False := by
  have hrz' := h.mem_Qz_iff.1 hrz
  have hrs' := h.mem_Qs_iff.1 hrs
  have hr2 : r * r = 1 := by
    have := pow_orderOf_eq_one r
    rwa [hr, sq] at this
  have hrsc : r * s = s * r := Subgroup.mem_centralizer_singleton_iff.1 hrs'.1
  have hsup := h.hs52 r hrs'.1 hr hrs'.2
  have hcs := comm_mem_oddCoreOf_of_sup hrsc hsup
  have hcm : CentModOdd A s :=
    centModOdd_of_comm_oddCore (h.hNz hrz'.1) (h.hNz h.s_mem_C) hr2 hrsc hrz'.2 hcs
  have h1 : M.permX s = 1 := (M.permX_eq_one_iff h.hn (h.hNz h.s_mem_C)).2 hcm
  have h2 := h.hfix
  rw [h1, fixCount_one'] at h2
  have := h.hn
  omega

theorem fixCount_le_of_mem_R (h : PairCtx X n z s A A' M M') {r : X} (hr : r ∈ h.R)
    (hr2 : orderOf r = 2) : fixCount (M.permX r) ≤ 3 := by
  obtain ⟨hrz, hrs, hrm⟩ := h.mem_R_iff.1 hr
  have hrsc : r * s = s * r := Subgroup.mem_centralizer_singleton_iff.1 hrs
  have hsq : r * r = 1 := by
    have := pow_orderOf_eq_one r
    rwa [hr2, sq] at this
  have hsup := h.hs52 r hrs hr2 hrm
  have hcs := comm_mem_oddCoreOf_of_sup hrsc hsup
  by_contra hF
  push Not at hF
  have hfx := M.fixed_of_comm_oddCore h.hn (h.hNz hrz) (h.hNz h.s_mem_C) hsq hrsc hcs (by omega)
  have hsub : (Finset.univ.filter fun i => M.permX r i = i) ⊆
      Finset.univ.filter fun i => M.permX s i = i := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hfx i hi
  have h1 := Finset.card_le_card hsub
  have h2 := h.hfix
  unfold fixCount at hF h2
  omega

@[expose] noncomputable def psi (h : PairCtx X n z s A A' M M') :
    ↥(centralizer ({z} : Set X)) →* Perm (Fin n) :=
  (M.permHom h.hn).comp (Subgroup.inclusion h.hNz)

theorem psi_apply (h : PairCtx X n z s A A' M M') (c : ↥(centralizer ({z} : Set X))) :
    h.psi c = M.permX c := (M.permX_of_mem (h.hNz c.2)).symm

@[expose] noncomputable def Rbar (h : PairCtx X n z s A A' M M') : Subgroup (Perm (Fin n)) :=
  (h.R.subgroupOf (centralizer ({z} : Set X))).map h.psi

theorem mem_Rbar_iff (h : PairCtx X n z s A A' M M') {t : Perm (Fin n)} :
    t ∈ h.Rbar ↔ ∃ r ∈ h.R, M.permX r = t := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, (h.psi_apply r).symm⟩
  · rintro ⟨r, hr, rfl⟩
    have hrz : r ∈ centralizer ({z} : Set X) := (h.mem_R_iff.1 hr).1
    exact ⟨⟨r, hrz⟩, hr, h.psi_apply ⟨r, hrz⟩⟩

theorem permX_pow (h : PairCtx X n z s A A' M M') {c : X} (hc : c ∈ normalizer (A : Set X))
    (k : ℕ) : M.permX (c ^ k) = (M.permX c) ^ k := by
  induction k with
  | zero => simp [M.permX_one h.hn]
  | succ k ih => rw [pow_succ, M.permX_mul h.hn (Subgroup.pow_mem _ hc k) hc, ih, pow_succ]

theorem ker_two (h : PairCtx X n z s A A' M M') {r : X} (hr : r ∈ h.R) (h1 : M.permX r = 1)
    {j : ℕ} (hj : r ^ (2 ^ j) = 1) : r = 1 := by
  by_contra hne
  obtain ⟨i, hi⟩ := exists_involution_pow hj hne
  have hw : r ^ (2 ^ i) ∈ h.R := Subgroup.pow_mem _ hr _
  obtain ⟨hwz, hws, hwm⟩ := h.mem_R_iff.1 hw
  refine h.no_involution (r := r ^ (2 ^ i)) ?_ ?_ hi
  · rw [h.mem_Qz_iff]
    refine ⟨hwz, ?_⟩
    rw [← M.permX_eq_one_iff h.hn (h.hNz hwz), h.permX_pow (h.hNz (h.mem_R_iff.1 hr).1), h1,
      one_pow]
  · exact h.mem_Qs_iff.2 ⟨hws, hwm⟩

theorem fixCount_le_of_involution_Rbar (h : PairCtx X n z s A A' M M') {t : Perm (Fin n)}
    (ht : t ∈ h.Rbar) (ht2 : t * t = 1) (ht1 : t ≠ 1) : fixCount t ≤ 3 := by
  obtain ⟨r₀, hr₀, rfl⟩ := h.mem_Rbar_iff.1 ht
  have hr₀z : r₀ ∈ centralizer ({z} : Set X) := (h.mem_R_iff.1 hr₀).1
  obtain ⟨r, hr, hr2, hr1, hrt⟩ := exists_involution_lift h.psi
    (R := h.R.subgroupOf (centralizer ({z} : Set X)))
    (fun r hr hf j hj => by
      have hj' : (r : X) ^ (2 ^ j) = 1 := by
        have := congrArg (fun w : ↥(centralizer ({z} : Set X)) => (w : X)) hj
        rw [Subgroup.coe_pow, Subgroup.coe_one] at this
        exact this
      have : (r : X) = 1 :=
        h.ker_two (Subgroup.mem_subgroupOf.1 hr) (by rw [← h.psi_apply]; exact hf) hj'
      exact Subtype.ext this)
    (r₀ := ⟨r₀, hr₀z⟩) hr₀ (by rw [h.psi_apply]; exact ht2) (by rw [h.psi_apply]; exact ht1)
  have hr2' : (r : X) * r = 1 := by simpa using congrArg Subtype.val hr2
  have hr1' : (r : X) ≠ 1 := fun e => hr1 (Subtype.ext e)
  have hord : orderOf (r : X) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hr2') hr1'
  have h3 := h.fixCount_le_of_mem_R (Subgroup.mem_subgroupOf.1 hr) hord
  have hpr : M.permX r₀ = M.permX (r : X) := by
    rw [← h.psi_apply ⟨r₀, hr₀z⟩, ← hrt, h.psi_apply]
  rw [hpr]
  exact h3

theorem R_conj (h : PairCtx X n z s A A' M M') {u r : X} (hu : u ∈ centralizer ({z} : Set X))
    (hus : u ∈ centralizer ({s} : Set X)) (hr : r ∈ h.R) : u * r * u⁻¹ ∈ h.R := by
  obtain ⟨hrz, hrs, hrm⟩ := h.mem_R_iff.1 hr
  rw [h.mem_R_iff]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hrz) (Subgroup.inv_mem _ hu),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hus hrs) (Subgroup.inv_mem _ hus), ?_⟩
  have := conj_mem_QOf (h.hNs hus) (mem_QOf_iff.2 ⟨h.hNs hrs, hrm⟩)
  exact (mem_QOf_iff.1 this).2

@[expose] def RCore (h : PairCtx X n z s A A' M M') : Prop :=
  ∀ x ∈ h.R, (∃ j : ℕ, x ^ (2 ^ j) = 1) → M.permX x = 1 ∨ M.permX x = M.permX s

theorem twoElts_of_ge_six (h : PairCtx X n z s A A' M M')
    (hk : 6 ≤ transCount (M.permX s)) : h.RCore := by
  classical
  have hsN : s ∈ normalizer (A : Set X) := h.hNz h.s_mem_C
  have hσ : M.permX s * M.permX s = 1 := by
    rw [← M.permX_mul h.hn hsN hsN, h.sq_s, M.permX_one h.hn]
  obtain ⟨k, hk'⟩ := involution_support_even hσ
  have hkk : transCount (M.permX s) = k := by
    unfold transCount
    rw [hk']
    omega
  rw [hkk] at hk
  have key := rbar_twoElts_of_ge_six (R := h.Rbar) hσ hk' hk (h.mem_Rbar_iff.2 ⟨s, h.s_mem_R, rfl⟩)
    (fun t ht => by
      obtain ⟨r, hr, rfl⟩ := h.mem_Rbar_iff.1 ht
      have hrc : r * s = s * r := Subgroup.mem_centralizer_singleton_iff.1 (h.mem_R_iff.1 hr).2.1
      rw [← M.permX_mul h.hn (h.hNz (h.mem_R_iff.1 hr).1) hsN,
        ← M.permX_mul h.hn hsN (h.hNz (h.mem_R_iff.1 hr).1), hrc])
    (fun a c ha hc hca hcb t ht => by
      obtain ⟨r, hr, rfl⟩ := h.mem_Rbar_iff.1 ht
      have hind := M.induces_perm h.hn s hsN
      rw [← M.permX_of_mem hsN] at hind
      obtain ⟨x, hx, hxδ⟩ := hind.dblSwap_mem_map_fixSub hσ a c ha hc hca hcb
      obtain ⟨u, hu, hsu, hux⟩ := M.exists_lift_cent hsN h.sq_s (AhatData.mem_fixSub.1 hx)
      have hδ : M.permX u = Equiv.swap a (M.permX s a) * Equiv.swap c (M.permX s c) := by
        rw [M.permX_of_mem_A h.hn hu, hux, hxδ]
      have hu_z : u ∈ centralizer ({z} : Set X) := h.hAz hu
      have hu_s : u ∈ centralizer ({s} : Set X) :=
        Subgroup.mem_centralizer_singleton_iff.2 hsu.symm
      refine h.mem_Rbar_iff.2 ⟨u * r * u⁻¹, h.R_conj hu_z hu_s hr, ?_⟩
      rw [M.permX_conj h.hn (h.hNz hu_z) (h.hNz (h.mem_R_iff.1 hr).1), hδ])
    (fun t ht ht2 ht1 => h.fixCount_le_of_involution_Rbar ht ht2 ht1)
  intro x hx ⟨j, hj⟩
  refine key _ (h.mem_Rbar_iff.2 ⟨x, hx, rfl⟩) ⟨j, ?_⟩
  rw [← h.permX_pow (h.hNz (h.mem_R_iff.1 hx).1), hj, M.permX_one h.hn]

theorem H0_lift (h : PairCtx X n z s A A' M M') (hσ8 : (M.permX s).support.card = 8) :
    ∀ g ∈ H0 (M.permX s), ∃ u ∈ A, s * u = u * s ∧ M.permX u = g := by
  intro g hg
  have hsN : s ∈ normalizer (A : Set X) := h.hNz h.s_mem_C
  have hσ : M.permX s * M.permX s = 1 := by
    rw [← M.permX_mul h.hn hsN hsN, h.sq_s, M.permX_one h.hn]
  have hind := M.induces_perm h.hn s hsN
  rw [← M.permX_of_mem hsN] at hind
  have : Finite M.K := Finite.of_equiv _ M.e.toEquiv
  obtain ⟨x, hx, hxg⟩ := H0_le_map_fixSub h.hn hind hσ hσ8 h.hsgn hg
  obtain ⟨u, hu, hsu, hux⟩ := M.exists_lift_cent hsN h.sq_s (AhatData.mem_fixSub.1 hx)
  exact ⟨u, hu, hsu, by rw [M.permX_of_mem_A h.hn hu, hux, hxg]⟩

end PairCtx

end CFSG.OddStandard.Solomon75

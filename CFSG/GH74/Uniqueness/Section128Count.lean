module

public import CFSG.GH74.Uniqueness.Section128Index
public import CFSG.GH74.Uniqueness.Section128Bender
public import CFSG.GH74.Uniqueness.Section126Dihedral
public import CFSG.GH74.Uniqueness.Section122Inv

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {c : Ctx12 Z M} {n i : ℕ}

namespace Sec128

theorem not_mem_Z (S : ZDSetup X Z M) {t : X} (htM : t ∉ M) {u : X}
    (hu : u ∈ M ⊓ conjugate M t) : u ∉ Z := by
  intro huZ
  obtain ⟨β, -, huniq⟩ := S.prodDisc.existsUnique_fixed_point S.invariant huZ
  have hMω : M ∈ omega M := self_mem_omega M
  have hCω : conjugate M t ∈ omega M := ⟨t, rfl⟩
  have h1 := huniq M ⟨hMω, (S.prodDisc.conjugate_eq_iff_mem hMω).mpr (Subgroup.mem_inf.mp hu).1⟩
  have h2 := huniq (conjugate M t)
    ⟨hCω, (S.prodDisc.conjugate_eq_iff_mem hCω).mpr (Subgroup.mem_inf.mp hu).2⟩
  have h3 : conjugate M t = M := h2.trans h1.symm
  apply htM
  rw [← S.prodDisc.normalizer_eq_self]
  exact conjugate_eq_iff_mem_normalizer.mp h3

theorem not_mem_Z_of_isConj (S : ZDSetup X Z M) (c : Ctx12 Z M) {u v : X} (huD : u ∈ c.D)
    (hv : IsConj u v) : v ∉ Z :=
  fun hvZ => not_mem_Z S c.htM huD (S.invariant.isConj_mem hvZ hv)

omit [Finite X] in
theorem mem_zpowers_conj {a w : X} (g : X) (hw : w ∈ zpowers a) :
    g⁻¹ * w * g ∈ zpowers (g⁻¹ * a * g) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := conj_zpow (a := g⁻¹) (b := a) (i := k)
  rw [inv_inv] at this
  exact this

omit [Finite X] in
theorem orderOf_conj' (x g : X) : orderOf (g⁻¹ * x * g) = orderOf x :=
  (orderOf_eq_of_isConj (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩)).symm

omit [Finite X] in
theorem ne_one_of_two {x : X} (hx : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem mem_Z_of_mem_zHull (h : LData c n i) {y : X} (hy : y ∈ zHull Z M) (hy1 : y ≠ 1) :
    y ∈ Z := by
  have : y ∈ zM Z M := by
    rw [h.zM_eq]
    exact ⟨hy, hy1⟩
  exact this.1

theorem ncard_inter_centralizer (h : LData c n i) (v : X) :
    (Z ∩ ((centralizer ({v} : Set X) ⊓ M : Subgroup X) : Set X)).ncard = qU Z M v - 1 := by
  have hset : Z ∩ ((centralizer ({v} : Set X) ⊓ M : Subgroup X) : Set X) =
      ((centralizer ({v} : Set X) ⊓ zHull Z M : Subgroup X) : Set X) \ {1} := by
    ext x
    constructor
    · rintro ⟨hxZ, hxCM⟩
      obtain ⟨hxC, hxM⟩ := Subgroup.mem_inf.mp hxCM
      have hx : x ∈ zM Z M := ⟨hxZ, hxM⟩
      rw [h.zM_eq] at hx
      exact ⟨Subgroup.mem_inf.mpr ⟨hxC, hx.1⟩, hx.2⟩
    · rintro ⟨hxCM, hx1⟩
      obtain ⟨hxC, hxH⟩ := Subgroup.mem_inf.mp hxCM
      have hx : x ∈ zM Z M := by
        rw [h.zM_eq]
        exact ⟨hxH, hx1⟩
      exact ⟨hx.1, Subgroup.mem_inf.mpr ⟨hxC, hx.2⟩⟩
  rw [hset, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _), ← Nat.card_coe_set_eq]
  rfl

theorem dihedral_core (S : ZDSetup X Z M) (h : LData c n i) {u : X} (huD : u ∈ c.D)
    (hu2 : orderOf u = 2) {v s w : X} (hv : IsConj u v) (hs : s ∈ Z) (hw2 : orderOf w = 2)
    (hw : w ∈ zpowers (v * s)) (hwZ : w ∉ Z) :
    ∃ k : ℕ, Odd k ∧ orderOf (v * s) = 2 * k ∧ w = (v * s) ^ k ∧ v * w ∈ Z := by
  have hv2 : orderOf v = 2 := (orderOf_eq_of_isConj hv).symm.trans hu2
  have hvZ : v ∉ Z := not_mem_Z_of_isConj S c huD hv
  have hz2 : orderOf c.z = 2 := S.invariant.1 c.z c.hz
  obtain ⟨g, hg⟩ := isConj_iff.mp (S.prodDisc.isConj_of_mem S.invariant c.hz hs)
  have hsz : g⁻¹ * s * g = c.z := by rw [← hg]; group
  have hv'2 : orderOf (g⁻¹ * v * g) = 2 := (orderOf_conj' v g).trans hv2
  have hv'Z : g⁻¹ * v * g ∉ Z := by
    intro h'
    apply hvZ
    have := S.invariant.2 _ h' g⁻¹
    rwa [show g⁻¹⁻¹ * (g⁻¹ * v * g) * g⁻¹ = v by group] at this
  have he : g⁻¹ * v * g * c.z = g⁻¹ * (v * s) * g := by rw [← hsz]; group
  have hw' : g⁻¹ * w * g ∈ zpowers (g⁻¹ * v * g * c.z) := by
    rw [he]
    exact mem_zpowers_conj g hw
  have hord : orderOf (v * s) = orderOf (g⁻¹ * v * g * c.z) := by
    rw [he, orderOf_conj']
  obtain ⟨hcard, hsec⟩ := h.dihedral (g⁻¹ * v * g) hv'2 hv'Z
  have hcard2 := card_closure_pair_eq_two_mul_orderOf
    (mul_self_eq_one_of_orderOf_eq_two hv'2) (mul_self_eq_one_of_orderOf_eq_two hz2)
    (ne_one_of_two hv'2) (ne_one_of_two hz2)
  have hw'2 : orderOf (g⁻¹ * w * g) = 2 := (orderOf_conj' w g).trans hw2
  rcases hcard with h8 | ⟨k, hk, hk4⟩
  · exfalso
    obtain ⟨hle, -, -⟩ := hsec _ hw' hw'2 h8
    have hw'M : g⁻¹ * w * g ∈ zHull Z M := hle (subset_closure (Set.mem_insert _ _))
    have hw'Z := mem_Z_of_mem_zHull h hw'M (ne_one_of_two hw'2)
    apply hwZ
    have := S.invariant.2 _ hw'Z g⁻¹
    rwa [show g⁻¹⁻¹ * (g⁻¹ * w * g) * g⁻¹ = w by group] at this
  · have hk2 : orderOf (v * s) = 2 * k := by omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact absurd hk (by decide)
    have hwk : w = (v * s) ^ k := (mem_zpowers_iff_eq_pow_half hk2 hk0 hw2).mp hw
    obtain ⟨x, -, hx⟩ := exists_conj_mul_pow_of_odd_half
      (mul_self_eq_one_of_orderOf_eq_two hv2) (S.invariant.mul_self_eq_one hs) hk2 hk
    refine ⟨k, hk, hk2, hwk, ?_⟩
    rw [hwk, ← hx]
    exact S.invariant.2 s hs x

theorem thompsonPairCount_eq_zero (S : ZDSetup X Z M) (h : LData c n i)
    (h127 : Lemma127Stmt Z M) {u : X} (huD : u ∈ c.D) (hu2 : orderOf u = 2) {w : X}
    (hw2 : orderOf w = 2) (hwu : ¬ IsConj u w) (hwz : ¬ IsConj c.z w) :
    thompsonPairCount u c.z w = 0 := by
  have hempty : thompsonPairs u c.z w = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨v, s⟩ ⟨hv, hs, hw⟩
    have hv' : IsConj u v := hv
    have hs' : IsConj c.z s := hs
    have hw' : w ∈ zpowers (v * s) := hw
    have hsZ : s ∈ Z := S.invariant.isConj_mem c.hz hs'.symm
    by_cases hwZ : w ∈ Z
    · exact hwz (S.prodDisc.isConj_of_mem S.invariant c.hz hwZ)
    · obtain ⟨k, -, -, -, hvw⟩ := dihedral_core S h huD hu2 hv' hsZ hw2 hw' hwZ
      have hvv := mul_self_eq_one_of_isConj (mul_self_eq_one_of_orderOf_eq_two hu2) hv'
      have hss := S.invariant.mul_self_eq_one hsZ
      have hcomm : Commute v w := commute_of_mem_zpowers (conj_mul_left_eq_inv hvv hss) hw'
        (mul_self_eq_one_of_orderOf_eq_two hw2)
      have h1 := (h127 c n i h u huD hu2).2 v (v * w) hv'
        (S.prodDisc.isConj_of_mem S.invariant c.hz hvw)
        (by rw [mul_assoc v w v, ← hcomm.eq])
      apply hwu
      rwa [← mul_assoc, hvv, one_mul] at h1
  rw [thompsonPairCount, hempty]
  simp

theorem thompsonPairCount_self (S : ZDSetup X Z M) (h : LData c n i) (h127 : Lemma127Stmt Z M)
    {u : X} (huD : u ∈ c.D) (hu2 : orderOf u = 2) {m j e : ℕ}
    (hB : BenderSub Z M (cenHull Z u) m j e) :
    thompsonPairCount u c.z u =
      {p : X × X | p.1 ∈ cenHull Z u ∧ orderOf p.1 = 2 ∧ p.2 ∈ cenHull Z u ∧
        orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))}.ncard := by
  set A := {p : X × X | p.1 ∈ cenHull Z u ∧ orderOf p.1 = 2 ∧ p.2 ∈ cenHull Z u ∧
    orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} with hA
  have huu := mul_self_eq_one_of_orderOf_eq_two hu2
  have huZ : u ∉ Z := not_mem_Z S c.htM huD
  have hcen : ∀ y ∈ cenHull Z u, y * u = u * y := fun y hy =>
    mem_centralizer_singleton_iff.mp (Cor713.zHull_le _ hy)
  have himage : (fun p : X × X => (u * p.1, p.2)) '' A = thompsonPairs u c.z u := by
    ext ⟨v, s⟩
    constructor
    · rintro ⟨⟨r, s'⟩, ⟨hr, hr2, hs, hs2, hodd⟩, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hrZ : r ∈ Z := hB.invol r hr hr2
      have hsZ : s' ∈ Z := hB.invol s' hs hs2
      refine ⟨?_, ?_, ?_⟩
      · exact (h127 c n i h u huD hu2).2 u r (IsConj.refl u)
          (S.prodDisc.isConj_of_mem S.invariant c.hz hrZ) (hcen r hr).symm
      · exact S.prodDisc.isConj_of_mem S.invariant c.hz hsZ
      · show u ∈ zpowers (u * r * s')
        obtain ⟨k, hk⟩ := hodd
        have hc : Commute u (r * s') := by
          show u * (r * s') = r * s' * u
          rw [← mul_assoc, ← (hcen r hr), mul_assoc, ← (hcen s' hs), mul_assoc]
        refine Subgroup.mem_zpowers_iff.mpr ⟨((2 * k + 1 : ℕ) : ℤ), ?_⟩
        rw [zpow_natCast, mul_assoc, hc.mul_pow, ← hk, pow_orderOf_eq_one, mul_one, hk,
          pow_succ, pow_mul, sq, huu, one_pow, one_mul]
    · rintro ⟨hv, hs, hu⟩
      have hv' : IsConj u v := hv
      have hs' : IsConj c.z s := hs
      have hu' : u ∈ zpowers (v * s) := hu
      have hsZ : s ∈ Z := S.invariant.isConj_mem c.hz hs'.symm
      obtain ⟨k, hk, -, huk, hvu⟩ := dihedral_core S h huD hu2 hv' hsZ hu2 hu' huZ
      have hvv := mul_self_eq_one_of_isConj huu hv'
      have hss := S.invariant.mul_self_eq_one hsZ
      have hvc : Commute v u := commute_of_mem_zpowers (conj_mul_left_eq_inv hvv hss) hu' huu
      have hsc : Commute s u := commute_of_mem_zpowers (conj_mul_right_eq_inv hvv hss) hu' huu
      have hrZ : u * v ∈ Z := by rw [← hvc.eq]; exact hvu
      have hrC : u * v ∈ centralizer ({u} : Set X) := by
        rw [mem_centralizer_singleton_iff]
        rw [mul_assoc, ← hvc.eq, ← mul_assoc]
      have hsC : s ∈ centralizer ({u} : Set X) := mem_centralizer_singleton_iff.mpr hsc.eq
      refine ⟨(u * v, s), ⟨subset_closure ⟨hrZ, hrC⟩, S.invariant.1 _ hrZ,
        subset_closure ⟨hsZ, hsC⟩, S.invariant.1 _ hsZ, ?_⟩, ?_⟩
      ·
        have hcs : Commute u (v * s) := (hvc.symm.mul_right hsc.symm)
        have hpow : (u * v * s) ^ k = 1 := by
          obtain ⟨j, hj⟩ := hk
          rw [mul_assoc, hcs.mul_pow, ← huk, hj, pow_succ, pow_mul, sq, huu, one_pow, one_mul,
            huu]
        exact Odd.of_dvd_nat hk (orderOf_dvd_of_pow_eq_one hpow)
      · show (u * (u * v), s) = (v, s)
        rw [← mul_assoc, huu, one_mul]
  rw [thompsonPairCount, ← himage, Nat.card_coe_set_eq,
    Set.ncard_image_of_injective _ (fun p q hpq => by
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext (mul_left_cancel hpq.1) hpq.2)]

theorem mem_thompsonPairs_z_iff (S : ZDSetup X Z M) (h : LData c n i) {u : X} (huD : u ∈ c.D)
    (hu2 : orderOf u = 2) {v s : X} :
    (v, s) ∈ thompsonPairs u c.z c.z ↔
      IsConj u v ∧ v * c.z = c.z * v ∧ s ∈ zHull Z M ∧ (v * s) ^ 2 = c.z := by
  have hzz : c.z * c.z = 1 := S.invariant.mul_self_eq_one c.hz
  have hz2 : orderOf c.z = 2 := S.invariant.1 c.z c.hz
  have huu := mul_self_eq_one_of_orderOf_eq_two hu2
  have hzH : c.z ∈ zHull Z M := subset_closure ⟨c.hz, c.hzM⟩
  constructor
  · rintro ⟨hv, hs, hzmem⟩
    have hv' : IsConj u v := hv
    have hs' : IsConj c.z s := hs
    have hzmem' : c.z ∈ zpowers (v * s) := hzmem
    have hvv : v * v = 1 := mul_self_eq_one_of_isConj huu hv'
    have hss : s * s = 1 := mul_self_eq_one_of_isConj hzz hs'
    have hc := mem_centralizer_of_mem_thompsonPairs huu hzz hzz
      (show (v, s) ∈ thompsonPairs u c.z c.z from ⟨hv', hs', hzmem'⟩)
    have hvz : v * c.z = c.z * v := mem_centralizer_singleton_iff.mp hc.1
    have hCM := S.prodDisc.centralizer_le_of_mem c.hz c.hzM
    have hvM : v ∈ M := hCM hc.1
    have hsM : s ∈ M := hCM hc.2
    have hsZ : s ∈ Z := S.invariant.isConj_mem c.hz hs'.symm
    have hsH : s ∈ zHull Z M := subset_closure ⟨hsZ, hsM⟩
    refine ⟨hv', hvz, hsH, ?_⟩
    have hsq : (v * s) ^ 2 ∈ zHull Z M := by
      have e : (v * s) ^ 2 = (v * s * v⁻¹) * s := by
        rw [sq, inv_eq_of_mul_eq_one_right hvv]; group
      rw [e]
      exact (zHull Z M).mul_mem (h.m_normal v hvM s hsH) hsH
    have h4 : (v * s) ^ 4 = 1 := by
      have := h.m_abelian.2 _ hsq
      rwa [← pow_mul] at this
    have hvs : ¬ IsConj v s := fun hc' =>
      not_mem_Z_of_isConj S c huD hv' (S.invariant.isConj_mem hsZ hc')
    obtain ⟨d, hd0, hd⟩ := exists_orderOf_mul_eq_two_mul hvv hss hvs
    have hdz : c.z = (v * s) ^ d := (mem_zpowers_iff_eq_pow_half hd hd0 hz2).mp hzmem'
    have hd4 : 2 * d ∣ 4 := hd ▸ orderOf_dvd_of_pow_eq_one h4
    have hd12 : d = 1 ∨ d = 2 := by
      have hd2 : d ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (by simpa using hd4)
      rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
      · exact Or.inl h1
      · exact Or.inr h2
    rcases hd12 with rfl | rfl
    · exfalso
      have hv' : v = c.z * s := by rw [hdz, pow_one, mul_assoc, hss, mul_one]
      have hvH : v ∈ zHull Z M := hv' ▸ (zHull Z M).mul_mem hzH hsH
      have hv1 : v ≠ 1 := ne_one_of_two ((orderOf_eq_of_isConj hv).symm.trans hu2)
      exact not_mem_Z_of_isConj S c huD hv (mem_Z_of_mem_zHull h hvH hv1)
    · exact hdz.symm
  · rintro ⟨hv, -, hsH, hsq⟩
    have hvv : v * v = 1 := mul_self_eq_one_of_isConj huu hv
    have hs1 : s ≠ 1 := by
      rintro rfl
      apply ne_one_of_two hz2
      rw [← hsq, mul_one, sq, hvv]
    have hsZ : s ∈ Z := mem_Z_of_mem_zHull h hsH hs1
    refine ⟨hv, S.prodDisc.isConj_of_mem S.invariant c.hz hsZ, ?_⟩
    show c.z ∈ zpowers (v * s)
    rw [← hsq]
    exact Subgroup.npow_mem_zpowers _ 2

theorem thompsonPairCount_z_eq_zero (S : ZDSetup X Z M) (h : LData c n i) {u : X} (huD : u ∈ c.D)
    (hu2 : orderOf u = 2) (hcent : u ∈ centralizer (zHull Z M : Set X)) :
    thompsonPairCount u c.z c.z = 0 := by
  have huM : u ∈ M := (Subgroup.mem_inf.mp huD).1
  have hempty : thompsonPairs u c.z c.z = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨v, s⟩ hp
    obtain ⟨hv, hvz, hsH, hsq⟩ := (mem_thompsonPairs_z_iff S h huD hu2).mp hp
    have hvM : v ∈ M := S.prodDisc.centralizer_le_of_mem c.hz c.hzM
      (mem_centralizer_singleton_iff.mpr hvz)
    obtain ⟨g, hg, rfl⟩ := exists_conj_of_isConj S huM hu2 hvM hv
    have hgs : g * s * g⁻¹ ∈ zHull Z M := h.m_normal g hg s hsH
    have hcs : g * s * g⁻¹ * u = u * (g * s * g⁻¹) := mem_centralizer_iff.mp hcent _ hgs
    have hvs : g⁻¹ * u * g * s = s * (g⁻¹ * u * g) := by
      calc g⁻¹ * u * g * s = g⁻¹ * (u * (g * s * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * s * g⁻¹ * u) * g := by rw [hcs]
        _ = s * (g⁻¹ * u * g) := by group
    have huu := mul_self_eq_one_of_orderOf_eq_two hu2
    have hss : s * s = 1 := by
      have := h.m_abelian.2 s hsH
      rwa [sq] at this
    apply ne_one_of_two (S.invariant.1 c.z c.hz)
    rw [← hsq, sq]
    calc g⁻¹ * u * g * s * (g⁻¹ * u * g * s)
        = g⁻¹ * u * g * (s * (g⁻¹ * u * g)) * s := by group
      _ = g⁻¹ * u * g * (g⁻¹ * u * g * s) * s := by rw [hvs]
      _ = g⁻¹ * (u * u) * g * (s * s) := by group
      _ = 1 := by rw [huu, hss]; group
  rw [thompsonPairCount, hempty]
  simp

theorem ncard_fiber (h : LData c n i) {v : X} (hvM : v ∈ M) (hvv : v * v = 1)
    (hvz : v * c.z = c.z * v) {m : ℕ} (hq : qU Z M v = 2 ^ m) (hn : n = 2 * m) :
    {s : X | s ∈ zHull Z M ∧ (v * s) ^ 2 = c.z}.ncard = 2 ^ m := by
  set H := zHull Z M with hH
  have hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.m_abelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq1 : ∀ x ∈ H, x * x = 1 := fun x hx => by
    have := h.m_abelian.2 x hx
    rwa [sq] at this
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hconjH : ∀ s ∈ H, v * s * v ∈ H := fun s hs => by
    have := h.m_normal v hvM s hs
    rwa [hvinv] at this
  have hsqH : ∀ s ∈ H, (v * s) ^ 2 ∈ H := fun s hs => by
    rw [sq, show v * s * (v * s) = (v * s * v) * s by group]
    exact H.mul_mem (hconjH s hs) hs
  let φ : H →* H :=
    { toFun := fun s => ⟨(v * s) ^ 2, hsqH s s.2⟩
      map_one' := by
        apply Subtype.ext
        show (v * 1) ^ 2 = 1
        rw [mul_one, sq, hvv]
      map_mul' := fun a b => by
        apply Subtype.ext
        show (v * ((a : X) * b)) ^ 2 = (v * a) ^ 2 * (v * b) ^ 2
        have hab : (v * b * v) * (a : X) = a * (v * b * v) := hcomm _ (hconjH b b.2) a a.2
        calc (v * ((a : X) * b)) ^ 2 = v * a * (v * v) * b * v * a * b := by
              rw [hvv, mul_one, sq]; simp only [mul_assoc]
          _ = (v * a * v) * ((v * b * v) * a) * b := by group
          _ = (v * a * v) * (a * (v * b * v)) * b := by rw [hab]
          _ = (v * a) ^ 2 * (v * b) ^ 2 := by rw [sq, sq]; group }
  have hφ : ∀ s : H, (φ s : X) = (v * s) ^ 2 := fun s => rfl
  have hker : ∀ s : H, s ∈ φ.ker ↔ (s : X) * v = v * s := by
    intro s
    rw [MonoidHom.mem_ker, Subtype.ext_iff, hφ]
    show (v * s) ^ 2 = 1 ↔ _
    have hs1 := hsq1 s s.2
    constructor
    · intro h1
      rw [sq] at h1
      calc (s : X) * v = (s : X) * v * ((v * s) * (v * s)) := by rw [h1, mul_one]
        _ = (s : X) * (v * v) * s * v * s := by group
        _ = v * s := by rw [hvv, mul_one, hs1, one_mul]
    · intro h1
      rw [sq]
      calc v * (s : X) * (v * s) = v * ((s : X) * v) * s := by group
        _ = v * (v * s) * s := by rw [h1]
        _ = 1 := by rw [← mul_assoc, hvv, one_mul, hs1]
  have hkerCard : Nat.card φ.ker = 2 ^ m := by
    rw [← hq]
    have e : φ.ker = (centralizer ({v} : Set X) ⊓ H).subgroupOf H := by
      ext s
      rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff]
      exact ⟨fun h1 => ⟨h1, s.2⟩, fun h1 => h1.1⟩
    rw [e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hrange : Nat.card φ.range = 2 ^ m := by
    have h1 := φ.ker.card_mul_index
    rw [Subgroup.index_ker, hkerCard, h.m_card, hn, pow_mul', sq] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hle : φ.range ≤ φ.ker := by
    rintro _ ⟨s, rfl⟩
    rw [hker, hφ]
    have hs := s.2
    have e1 : (v * s) ^ 2 = (v * s * v) * s := by rw [sq]; group
    rw [e1]
    have hc := hcomm _ (hconjH s hs) s hs
    calc (v * s * v) * (s : X) * v = v * (s * (v * (s : X) * v)) := by group
      _ = v * ((v * s * v) * s) := by rw [← hc]
  have heq : φ.range = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hkerCard])
  have hzH : c.z ∈ H := subset_closure ⟨c.hz, c.hzM⟩
  have hzker : (⟨c.z, hzH⟩ : H) ∈ φ.ker := by
    rw [hker]
    exact hvz.symm
  rw [← heq] at hzker
  obtain ⟨s₀, hs₀⟩ := hzker
  have hfib : {s : X | s ∈ H ∧ (v * s) ^ 2 = c.z} =
      Subtype.val '' (φ ⁻¹' {φ s₀}) := by
    ext s
    constructor
    · rintro ⟨hs, hsz⟩
      refine ⟨⟨s, hs⟩, ?_, rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff, hs₀]
      exact Subtype.ext hsz
    · rintro ⟨s', hs', rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff, hs₀] at hs'
      exact ⟨s'.2, congrArg Subtype.val hs'⟩
  rw [hfib, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq,
    Nat.card_congr (MonoidHom.fiberEquivKer φ s₀), hkerCard]

theorem thompsonPairCount_z (S : ZDSetup X Z M) (h : LData c n i) {u : X} (huD : u ∈ c.D)
    (hu2 : orderOf u = 2) {m : ℕ} (hq : qU Z M u = 2 ^ m) (hn : n = 2 * m) :
    thompsonPairCount u c.z c.z = {v : X | IsConj u v ∧ v * c.z = c.z * v}.ncard * 2 ^ m := by
  have huM : u ∈ M := (Subgroup.mem_inf.mp huD).1
  have huu := mul_self_eq_one_of_orderOf_eq_two hu2
  have hset : thompsonPairs u c.z c.z =
      {p : X × X | p.1 ∈ {v : X | IsConj u v ∧ v * c.z = c.z * v} ∧
        p.2 ∈ (fun v : X => {s : X | s ∈ zHull Z M ∧ (v * s) ^ 2 = c.z}) p.1} := by
    ext ⟨v, s⟩
    rw [mem_thompsonPairs_z_iff S h huD hu2]
    simp only [Set.mem_ofPred_eq]
    tauto
  rw [thompsonPairCount, hset, Nat.card_coe_set_eq]
  refine ncard_pairs_eq_mul {v : X | IsConj u v ∧ v * c.z = c.z * v}
    (fun v : X => {s : X | s ∈ zHull Z M ∧ (v * s) ^ 2 = c.z}) (2 ^ m) fun v hv => ?_
  obtain ⟨hvc, hvz⟩ := hv
  have hvM : v ∈ M := S.prodDisc.centralizer_le_of_mem c.hz c.hzM
    (mem_centralizer_singleton_iff.mpr hvz)
  obtain ⟨g, hg, rfl⟩ := exists_conj_of_isConj S huM hu2 hvM hvc
  refine ncard_fiber h hvM (mul_self_eq_one_of_isConj huu hvc) hvz ?_ hn
  rw [qU_conj h hg, hq]

theorem ncard_V_mul (S : ZDSetup X Z M) (h : LData c n i) {u : X} (huD : u ∈ c.D)
    (hu2 : orderOf u = 2) {m : ℕ} (hq : qU Z M u = 2 ^ m) :
    {v : X | IsConj u v ∧ v * c.z = c.z * v}.ncard * (2 ^ n - 1) =
      {v : X | ∃ g ∈ M, g⁻¹ * u * g = v}.ncard * (2 ^ m - 1) := by
  have huM : u ∈ M := (Subgroup.mem_inf.mp huD).1
  set V := {v : X | IsConj u v ∧ v * c.z = c.z * v} with hV
  set UM := {v : X | ∃ g ∈ M, g⁻¹ * u * g = v} with hUM
  set B : X → Set X := fun v => {w : X | w ∈ Z ∩ (M : Set X) ∧ v * w = w * v} with hB
  set B' : X → Set X := fun w => {v : X | v ∈ UM ∧ v * w = w * v} with hB'
  have h1 : {p : X × X | p.1 ∈ UM ∧ p.2 ∈ B p.1}.ncard = UM.ncard * (2 ^ m - 1) := by
    refine ncard_pairs_eq_mul UM B (2 ^ m - 1) fun v hv => ?_
    obtain ⟨g, hg, rfl⟩ := hv
    have e : B (g⁻¹ * u * g) =
        Z ∩ ((centralizer ({g⁻¹ * u * g} : Set X) ⊓ M : Subgroup X) : Set X) := by
      ext w
      simp only [hB, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_inf,
        mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨⟨hwZ, hwM⟩, hc⟩
        exact ⟨hwZ, hc.symm, hwM⟩
      · rintro ⟨hwZ, hc, hwM⟩
        exact ⟨⟨hwZ, hwM⟩, hc.symm⟩
    rw [e, ncard_inter_centralizer h, qU_conj h hg, hq]
  have h2 : {p : X × X | p.1 ∈ Z ∩ (M : Set X) ∧ p.2 ∈ B' p.1}.ncard =
      (Z ∩ (M : Set X)).ncard * V.ncard := by
    refine ncard_pairs_eq_mul (Z ∩ (M : Set X)) B' V.ncard fun w hw => ?_
    obtain ⟨g, hg, rfl⟩ := S.prodDisc.exists_conj_mem S.invariant c.hz c.hzM hw.1 hw.2
    have hVz : B' c.z = V := by
      ext v
      simp only [hB', hUM, hV, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨k, -, rfl⟩, hc⟩
        exact ⟨isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]⟩, hc⟩
      · rintro ⟨hvc, hc⟩
        have hvM : v ∈ M := S.prodDisc.centralizer_le_of_mem c.hz c.hzM
          (mem_centralizer_singleton_iff.mpr hc)
        exact ⟨exists_conj_of_isConj S huM hu2 hvM hvc, hc⟩
    have himg : B' (g⁻¹ * c.z * g) = (fun v => g⁻¹ * v * g) '' B' c.z := by
      ext v
      simp only [hB', hUM, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨⟨k, hk, rfl⟩, hc⟩
        refine ⟨g * (k⁻¹ * u * k) * g⁻¹, ⟨⟨k * g⁻¹, M.mul_mem hk (M.inv_mem hg), by group⟩, ?_⟩,
          by group⟩
        calc g * (k⁻¹ * u * k) * g⁻¹ * c.z
            = g * ((k⁻¹ * u * k) * (g⁻¹ * c.z * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * c.z * g) * (k⁻¹ * u * k)) * g⁻¹ := by rw [hc]
          _ = c.z * (g * (k⁻¹ * u * k) * g⁻¹) := by group
      · rintro ⟨v', ⟨⟨k, hk, rfl⟩, hc⟩, rfl⟩
        refine ⟨⟨k * g, M.mul_mem hk hg, by group⟩, ?_⟩
        calc g⁻¹ * (k⁻¹ * u * k) * g * (g⁻¹ * c.z * g)
            = g⁻¹ * ((k⁻¹ * u * k) * c.z) * g := by group
          _ = g⁻¹ * (c.z * (k⁻¹ * u * k)) * g := by rw [hc]
          _ = g⁻¹ * c.z * g * (g⁻¹ * (k⁻¹ * u * k) * g) := by group
    rw [himg, Set.ncard_image_of_injective _ (fun a b hab => by
      simpa using hab), hVz]
  have h3 : {p : X × X | p.1 ∈ UM ∧ p.2 ∈ B p.1}.ncard =
      {p : X × X | p.1 ∈ Z ∩ (M : Set X) ∧ p.2 ∈ B' p.1}.ncard := by
    have e : Prod.swap '' {p : X × X | p.1 ∈ UM ∧ p.2 ∈ B p.1} =
        {p : X × X | p.1 ∈ Z ∩ (M : Set X) ∧ p.2 ∈ B' p.1} := by
      ext ⟨w, v⟩
      simp only [Set.mem_image, Set.mem_ofPred_eq, hB, hB', Prod.exists, Prod.swap_prod_mk,
        Prod.mk.injEq]
      constructor
      · rintro ⟨a, b, ⟨ha, hb, hab⟩, rfl, rfl⟩
        exact ⟨hb, ha, hab⟩
      · rintro ⟨hw, hv, hvw⟩
        exact ⟨v, w, ⟨hv, hw, hvw⟩, rfl, rfl⟩
    rw [← e, Set.ncard_image_of_injective _ Prod.swap_injective]
  rw [h3, h2, A2.ncard_zM h] at h1
  rw [mul_comm]
  exact h1

end Sec128

end CFSG.GH74.Uniqueness

module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightSLJ
public import CFSG.CGT.PushingUpLit.CGT6.SixFiveJ

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree CFSG.CGT.PushingUpLit.EightOneRel
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem isPGroup_of_sq_mem {R S : Subgroup G} (hR2 : IsPGroup 2 R) (h : ∀ z ∈ S, z ^ 2 ∈ R) :
    IsPGroup 2 S := by
  intro z
  obtain ⟨m, hm⟩ := hR2 ⟨(z : G) ^ 2, h z z.2⟩
  refine ⟨m + 1, Subtype.ext ?_⟩
  have : ((z : G) ^ 2) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  rw [pow_succ', pow_mul]
  exact this

@[expose] def stabSub (V D : Subgroup G) : Subgroup G where
  carrier := {x | (∀ v ∈ V, ⁅x, v⁆ ∈ D) ∧ ∀ d ∈ D, x * d = d * x}
  one_mem' := ⟨fun v _ => by simp, fun d _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxV, hxD⟩ ⟨hyV, hyD⟩
    refine ⟨fun v hv => ?_, fun d hd => ?_⟩
    · have e : ⁅x * y, v⁆ = x * ⁅y, v⁆ * x⁻¹ * ⁅x, v⁆ := by
        simp only [commutatorElement_def]
        group
      have h1 : x * ⁅y, v⁆ * x⁻¹ = ⁅y, v⁆ := by
        rw [hxD _ (hyV v hv)]
        group
      rw [e, h1]
      exact D.mul_mem (hyV v hv) (hxV v hv)
    · calc x * y * d = x * (y * d) := mul_assoc _ _ _
        _ = x * (d * y) := by rw [hyD d hd]
        _ = (x * d) * y := (mul_assoc _ _ _).symm
        _ = (d * x) * y := by rw [hxD d hd]
        _ = d * (x * y) := mul_assoc _ _ _
  inv_mem' := by
    rintro x ⟨hxV, hxD⟩
    refine ⟨fun v hv => ?_, fun d hd => ?_⟩
    · have e : ⁅x⁻¹, v⁆ = x⁻¹ * ⁅x, v⁆⁻¹ * x := by
        simp only [commutatorElement_def]
        group
      have h1 : x⁻¹ * ⁅x, v⁆⁻¹ * x = ⁅x, v⁆⁻¹ := by
        have := hxD _ (D.inv_mem (hxV v hv))
        calc x⁻¹ * ⁅x, v⁆⁻¹ * x = x⁻¹ * (⁅x, v⁆⁻¹ * x) := mul_assoc _ _ _
          _ = x⁻¹ * (x * ⁅x, v⁆⁻¹) := by rw [this]
          _ = ⁅x, v⁆⁻¹ := by group
      rw [e, h1]
      exact D.inv_mem (hxV v hv)
    · have := hxD d hd
      calc x⁻¹ * d = x⁻¹ * (d * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * d) * x⁻¹ := by rw [this]
        _ = d * x⁻¹ := by group

theorem sq_centralizes_of_mem_stabSub {V D : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)
    (hDV : D ≤ V) {x : G} (hx : x ∈ stabSub V D) {v : G} (hv : v ∈ V) :
    x ^ 2 * v = v * x ^ 2 := by
  obtain ⟨hxV, hxD⟩ := hx
  set d : G := ⁅x, v⁆ with hd
  have hdD : d ∈ D := hxV v hv
  have h1 : x * v * x⁻¹ = d * v := by rw [hd]; simp only [commutatorElement_def]; group
  have h2 : x * d * x⁻¹ = d := by rw [hxD d hdD]; group
  have hd2 : d * d = 1 := by
    rw [← pow_two]
    exact hV.2 d (hDV hdD)
  have h3 : x * x * v * (x * x)⁻¹ = v := by
    calc x * x * v * (x * x)⁻¹ = x * (x * v * x⁻¹) * x⁻¹ := by group
      _ = x * (d * v) * x⁻¹ := by rw [h1]
      _ = (x * d * x⁻¹) * (x * v * x⁻¹) := by group
      _ = d * (d * v) := by rw [h2, h1]
      _ = (d * d) * v := by group
      _ = v := by rw [hd2]; group
  rw [pow_two]
  calc x * x * v = (x * x * v * (x * x)⁻¹) * (x * x) := by group
    _ = v * (x * x) := by rw [h3]

theorem isPGroup_sup_of_quad {V R K K' D : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)
    (hR2 : IsPGroup 2 R) (hRC : ∀ x : G, (∀ v ∈ V, x * v = v * x) → x ∈ R)
    (hRV : ∀ r ∈ R, ∀ v ∈ V, r * v = v * r) (hDV : D ≤ V)
    (hK : K ≤ stabSub V D) (hK' : K' ≤ stabSub V D) : IsPGroup 2 ↥(K ⊔ K' ⊔ R) := by
  have hRs : R ≤ stabSub V D := fun r hr =>
    ⟨fun v hv => by
      have : ⁅r, v⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact hRV r hr v hv
      rw [this]
      exact D.one_mem, fun d hd => hRV r hr d (hDV hd)⟩
  refine isPGroup_of_sq_mem hR2 fun z hz => ?_
  exact hRC _ fun v hv => sq_centralizes_of_mem_stabSub hV hDV (sup_le (sup_le hK hK') hRs hz) hv

theorem sq_mem_sup_of_comm_mod {R K K' : Subgroup G} [R.Normal] (hK2 : ∀ x ∈ K, x ^ 2 ∈ R)
    (hK2' : ∀ x ∈ K', x ^ 2 ∈ R) (hK : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ R)
    (hK' : ∀ x ∈ K', ∀ y ∈ K', ⁅x, y⁆ ∈ R) (hKK' : ∀ x ∈ K, ∀ y ∈ K', ⁅x, y⁆ ∈ R) :
    ∀ z ∈ K ⊔ K' ⊔ R, z ^ 2 ∈ R := by
  classical
  let π : G →* G ⧸ R := QuotientGroup.mk' R
  have hcomm : ∀ a b : G, ⁅a, b⁆ ∈ R → π a * π b = π b * π a := by
    intro a b hab
    have : π ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hab
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hX : CFSG.Open.IsElemAbelian 2 (K.map π) := by
    refine isElemAbelian_of_forall' ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact hcomm x y (hK x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hK2 x hx)
  have hY : CFSG.Open.IsElemAbelian 2 (K'.map π) := by
    refine isElemAbelian_of_forall' ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact hcomm x y (hK' x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hK2' x hx)
  have hXY : CFSG.Open.IsElemAbelian 2 (K.map π ⊔ K'.map π) := by
    refine isElemAbelian_sup' hX hY ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hcomm x y (hKK' x hx y hy)
  intro z hz
  have hzπ : π z ∈ K.map π ⊔ K'.map π := by
    have hz' : z ∈ (K ⊔ K') ⊔ R := hz
    obtain ⟨w, hw, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hz'
    have hπr : π r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    have : π (w * r) = π w := by
      rw [map_mul, hπr, mul_one]
    rw [this, ← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem _ hw
  have h2 := hXY.2 (π z) hzπ
  rw [← map_pow] at h2
  exact (QuotientGroup.eq_one_iff _).mp h2

theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem comm_of_conj_comm {a b g : G}
    (h : (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹)) : a * b = b * a := by
  have e1 : (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
  have e2 : (g * b * g⁻¹) * (g * a * g⁻¹) = g * (b * a) * g⁻¹ := by group
  rw [e1, e2] at h
  exact mul_left_cancel (mul_right_cancel h)

theorem conj_comm_of_comm {a b g : G} (h : a * b = b * a) :
    (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) := by
  have e1 : (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
  have e2 : (g * b * g⁻¹) * (g * a * g⁻¹) = g * (b * a) * g⁻¹ := by group
  rw [e1, e2, h]

@[expose] def QuadSub (V R K : Subgroup G) : Prop :=
  (∀ x ∈ K, x ∉ R → V ⊓ Subgroup.centralizer ({x} : Set G) = V ⊓ Subgroup.centralizer (K : Set G)) ∧
    ∀ x ∈ K, ∀ v ∈ V, ⁅x, v⁆ ∈ Subgroup.centralizer (K : Set G)

theorem QuadSub.conjugate {V R K : Subgroup G} [V.Normal] [R.Normal] (hK : QuadSub V R K) (g : G) :
    QuadSub V R (conjugate K g) := by
  refine ⟨fun x' hx' hxR => ?_, fun x' hx' v hv => ?_⟩
  · have hx : g * x' * g⁻¹ ∈ K := mem_conjugate_iff'.mp hx'
    have hxR' : g * x' * g⁻¹ ∉ R := fun h => hxR (by
      have := (inferInstance : R.Normal).conj_mem _ h g⁻¹
      simpa [mul_assoc] using this)
    apply le_antisymm
    · intro v hv
      obtain ⟨hvV, hvx⟩ := Subgroup.mem_inf.mp hv
      have hxv : x' * v = v * x' := Subgroup.mem_centralizer_iff.mp hvx x' (Set.mem_singleton x')
      have hw : g * v * g⁻¹ ∈ V := (inferInstance : V.Normal).conj_mem v hvV g
      have hw1 : g * v * g⁻¹ ∈ V ⊓ Subgroup.centralizer ({g * x' * g⁻¹} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hw, Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff.mp hy]
          exact conj_comm_of_comm hxv⟩
      rw [hK.1 _ hx hxR'] at hw1
      refine Subgroup.mem_inf.mpr ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun k' hk' => ?_⟩
      exact comm_of_conj_comm (Subgroup.mem_centralizer_iff.mp hw1.2 _ (mem_conjugate_iff'.mp hk'))
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx'))
  · have hx : g * x' * g⁻¹ ∈ K := mem_conjugate_iff'.mp hx'
    have hw : g * v * g⁻¹ ∈ V := (inferInstance : V.Normal).conj_mem v hv g
    have h1 := hK.2 _ hx _ hw
    have e : g * ⁅x', v⁆ * g⁻¹ = ⁅g * x' * g⁻¹, g * v * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [← e] at h1
    refine Subgroup.mem_centralizer_iff.mpr fun k' hk' => ?_
    exact comm_of_conj_comm (Subgroup.mem_centralizer_iff.mp h1 _ (mem_conjugate_iff'.mp hk'))

theorem isPGroup_sup_of_quadSub {V R K K' : Subgroup G} [V.Normal] [R.Normal]
    (hV : CFSG.Open.IsElemAbelian 2 V) (hR2 : IsPGroup 2 R)
    (hRC : ∀ x : G, (∀ v ∈ V, x * v = v * x) → x ∈ R) (hRV : ∀ r ∈ R, ∀ v ∈ V, r * v = v * r)
    (hK : QuadSub V R K) (hK' : QuadSub V R K') {x b r : G} (hx : x ∈ K) (hxR : x ∉ R)
    (hb : b ∈ K') (hr : r ∈ R) (hxb : x = b * r) : IsPGroup 2 ↥(K ⊔ K' ⊔ R) := by
  have hbR : b ∉ R := fun h => hxR (by rw [hxb]; exact R.mul_mem h hr)
  have hxb' : V ⊓ Subgroup.centralizer ({x} : Set G) = V ⊓ Subgroup.centralizer ({b} : Set G) := by
    ext v
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨hvV, hv⟩
      refine ⟨hvV, ?_⟩
      have h2 : r * v = v * r := hRV r hr v hvV
      rw [hxb] at hv
      have e1 : (b * r) * v = (b * v) * r := by rw [mul_assoc, h2, ← mul_assoc]
      have e2 : v * (b * r) = (v * b) * r := by rw [mul_assoc]
      exact mul_right_cancel (e1.symm.trans (hv.trans e2))
    · rintro ⟨hvV, hv⟩
      refine ⟨hvV, ?_⟩
      have h2 : r * v = v * r := hRV r hr v hvV
      rw [hxb]
      have e1 : (b * r) * v = (b * v) * r := by rw [mul_assoc, h2, ← mul_assoc]
      have e2 : v * (b * r) = (v * b) * r := by rw [mul_assoc]
      rw [e1, e2, hv]
  have hDD : V ⊓ Subgroup.centralizer (K : Set G) = V ⊓ Subgroup.centralizer (K' : Set G) := by
    rw [← hK.1 x hx hxR, ← hK'.1 b hb hbR, hxb']
  have hDV : V ⊓ Subgroup.centralizer (K : Set G) ≤ V := inf_le_left
  have hKs : K ≤ stabSub V (V ⊓ Subgroup.centralizer (K : Set G)) := by
    intro y hy
    refine ⟨fun v hv => Subgroup.mem_inf.mpr ⟨?_, hK.2 y hy v hv⟩, fun d hd =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 y hy⟩
    have e : ⁅y, v⁆ = (y * v * y⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact V.mul_mem ((inferInstance : V.Normal).conj_mem v hv y) (V.inv_mem hv)
  have hKs' : K' ≤ stabSub V (V ⊓ Subgroup.centralizer (K : Set G)) := by
    intro y hy
    rw [hDD]
    refine ⟨fun v hv => Subgroup.mem_inf.mpr ⟨?_, hK'.2 y hy v hv⟩, fun d hd =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 y hy⟩
    have e : ⁅y, v⁆ = (y * v * y⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact V.mul_mem ((inferInstance : V.Normal).conj_mem v hv y) (V.inv_mem hv)
  exact isPGroup_sup_of_quad hV hR2 hRC hRV hDV hKs hKs'

section Nine

variable [Finite G]

theorem eight_sl_nine {Y R : Subgroup G} {T : Sylow 2 G} (h : EightCtx Y T R) {n : ℕ} (hn : 1 ≤ n)
    (hnat : IsNaturalSLTwoModule ↥Y n) :
    ∃ A : Subgroup G, IsMaxElemAbelian (T : Subgroup G) A ∧ ¬ A ≤ centralizerModCore Y ∧
      jIn (T : Subgroup G) ≤ A ⊔ R ∧ jIn (T : Subgroup G) ≤ Y ⊔ R ∧
      (A ⊓ R).relIndex A = Nat.card (GaloisField 2 n) ∧
      (∀ x ∈ jIn (T : Subgroup G), ∀ y ∈ jIn (T : Subgroup G), ⁅x, y⁆ ∈ R) ∧
      (∀ x ∈ jIn (T : Subgroup G), x ^ 2 ∈ R) ∧
      (∃ x ∈ jIn (T : Subgroup G), x ∉ R) ∧
      (∀ g : G, (∃ x ∈ jIn (T : Subgroup G), x ∉ R ∧
          ∃ b ∈ conjugate (jIn (T : Subgroup G)) g, ∃ r ∈ R, x = b * r) →
        conjugate (jIn (T : Subgroup G)) g = jIn (T : Subgroup G)) ∧
      (∀ g : G, (∀ x ∈ jIn (T : Subgroup G), ∀ y ∈ conjugate (jIn (T : Subgroup G)) g,
          ⁅x, y⁆ ∈ R) → conjugate (jIn (T : Subgroup G)) g = jIn (T : Subgroup G)) := by
  classical
  have := h.hRn
  have : (omegaOneCenterIn R).Normal := h.V_normal
  obtain ⟨A, hA, hnot, hJA, hJY, hrel, hN1, hN2⟩ := eight_sl_J h hn hnat
  set J : Subgroup G := jIn (T : Subgroup G) with hJ
  have hTtop : IsSylowOf 2 (T : Subgroup G) ⊤ :=
    ⟨le_top, T.isPGroup', by simpa [Subgroup.relIndex_top_right] using T.not_dvd_index⟩
  have hV := isElemAbelian_omegaOneCenterIn R
  have hR2 := h.hR2
  have hRC : ∀ x : G, (∀ v ∈ omegaOneCenterIn R, x * v = v * x) → x ∈ R := by
    intro x hx
    rw [← h.hC]
    exact Subgroup.mem_centralizer_iff.mpr fun v hv => (hx v hv).symm
  have hRV : ∀ r ∈ R, ∀ v ∈ omegaOneCenterIn R, r * v = v * r := fun r hr v hv =>
    (mem_omegaOneCenterIn_iff.mp hv).2.1 r hr
  have hRconj : ∀ (g z : G), g * z * g⁻¹ ∈ R → z ∈ R := fun g z hz => by
    have := (inferInstance : R.Normal).conj_mem _ hz g⁻¹
    simpa [mul_assoc] using this
  let π : G →* G ⧸ R := QuotientGroup.mk' R
  have hπR : ∀ r ∈ R, π r = 1 := fun r hr => (QuotientGroup.eq_one_iff r).mpr hr
  have hJcomm : ∀ x ∈ J, ∀ y ∈ J, ⁅x, y⁆ ∈ R := by
    intro x hx y hy
    obtain ⟨a, haA, r, hrR, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hJA hx)
    obtain ⟨a', haA', r', hrR', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hJA hy)
    have h1 : π (a * r) = π a := by rw [map_mul, hπR r hrR, mul_one]
    have h2 : π (a' * r') = π a' := by rw [map_mul, hπR r' hrR', mul_one]
    have h3 : ⁅a, a'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (isElemAbelian_comm' hA.2.1 haA haA')
    have : π ⁅a * r, a' * r'⁆ = 1 := by
      rw [map_commutatorElement, h1, h2, ← map_commutatorElement, h3, map_one]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hJsq : ∀ x ∈ J, x ^ 2 ∈ R := by
    intro x hx
    obtain ⟨a, haA, r, hrR, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hJA hx)
    have h1 : π (a * r) = π a := by rw [map_mul, hπR r hrR, mul_one]
    have : π ((a * r) ^ 2) = 1 := by
      rw [map_pow, h1, ← map_pow, hA.2.1.2 a haA, map_one]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hJq : QuadSub (omegaOneCenterIn R) R J := ⟨hN1, hN2⟩
  have hAJ : A ≤ J := by
    rw [hJ, jIn_eq_thompsonJ]
    exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A hA
  have hJbot : ∃ x ∈ J, x ∉ R := by
    by_contra hcon
    push Not at hcon
    exact hnot (fun a ha => h.R_le_centralizerModCore (hcon a (hAJ ha)))
  have hsup : ∀ g : G, jIn (T : Subgroup G) ≤ J ⊔ conjugate J g ⊔ R := fun g =>
    le_sup_left.trans le_sup_left
  refine ⟨A, hA, hnot, hJA, hJY, hrel, hJcomm, hJsq, hJbot, ?_, ?_⟩
  · rintro g ⟨x, hx, hxR, b, hb, r, hr, hxb⟩
    have hS := isPGroup_sup_of_quadSub hV hR2 hRC hRV hJq (hJq.conjugate g) hx hxR hb hr hxb
    have h1 := jIn_eq_of_le_isPGroup hTtop (hsup g) hS
    have h2 := jIn_eq_conjugate_of_le_isPGroup hTtop g
      (le_sup_right.trans le_sup_left : conjugate (jIn (T : Subgroup G)) g ≤ J ⊔ conjugate J g ⊔ R) hS
    exact h2.symm.trans h1
  · intro g hcomm
    have hJ2' : ∀ x ∈ conjugate J g, x ^ 2 ∈ R := fun x hx => by
      apply hRconj g
      have := hJsq _ (mem_conjugate_iff'.mp hx)
      simpa [mul_assoc, pow_two] using this
    have hJc' : ∀ x ∈ conjugate J g, ∀ y ∈ conjugate J g, ⁅x, y⁆ ∈ R := fun x hx y hy => by
      apply hRconj g
      have := hJcomm _ (mem_conjugate_iff'.mp hx) _ (mem_conjugate_iff'.mp hy)
      have e : g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact this
    have hsq := sq_mem_sup_of_comm_mod hJsq hJ2' hJcomm hJc' hcomm
    have hS := isPGroup_of_sq_mem hR2 hsq
    have h1 := jIn_eq_of_le_isPGroup hTtop (hsup g) hS
    have h2 := jIn_eq_conjugate_of_le_isPGroup hTtop g
      (le_sup_right.trans le_sup_left : conjugate (jIn (T : Subgroup G)) g ≤ J ⊔ conjugate J g ⊔ R) hS
    exact h2.symm.trans h1

end Nine

end CFSG.CGT.PushingUpLit.CGT6

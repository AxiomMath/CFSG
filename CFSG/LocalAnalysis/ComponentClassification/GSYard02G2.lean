module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylMain

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup

namespace G2Four

variable {X : Type} [Group X]

abbrev kleinOf {g z : X} (hg : g * g = 1) (hz : z * z = 1) (hgz : Commute g z) : Subgroup X :=
  CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions g z hg hz hgz

theorem mem_kleinOf {g z x : X} (hg : g * g = 1) (hz : z * z = 1) (hgz : Commute g z) :
    x ∈ kleinOf hg hz hgz ↔ x = g * z ∨ x = g ∨ x = z ∨ x = 1 := by
  show x ∈ ({g * z, g, z, 1} : Set X) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem isKleinFour_kleinOf {g z : X} (hg : g * g = 1) (hz : z * z = 1) (hg1 : g ≠ 1)
    (hz1 : z ≠ 1) (hgz : g ≠ z) (hcomm : Commute g z) : IsKleinFour (kleinOf hg hz hcomm) :=
  CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions g z hg hz hg1 hz1 hgz hcomm

theorem mem_centralizer_kleinOf {h z x : X} (hh : h * h = 1) (hz : z * z = 1)
    (hhz : Commute h z) (hxh : Commute x h) (hxz : Commute x z) :
    x ∈ centralizer ((kleinOf hh hz hhz : Subgroup X) : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  rcases (mem_kleinOf hh hz hhz).mp hk with rfl | rfl | rfl | rfl
  · exact (Commute.mul_right hxh hxz).symm.eq
  · exact hxh.symm.eq
  · exact hxz.symm.eq
  · exact (Commute.one_right x).symm.eq

theorem kleinOf_le_centralizer {K : Set X} {g z : X} (hg : g * g = 1) (hz : z * z = 1)
    (hgz : Commute g z) (hgK : g ∈ centralizer K) (hzK : z ∈ centralizer K) :
    kleinOf hg hz hgz ≤ centralizer K := by
  intro x hx
  rcases (mem_kleinOf hg hz hgz).mp hx with rfl | rfl | rfl | rfl
  · exact mul_mem hgK hzK
  · exact hgK
  · exact hzK
  · exact one_mem _

theorem exists_ne_one_ne_of_kleinFour {V : Subgroup X} (hV : IsKleinFour V) (v : X) :
    ∃ w ∈ V, w ≠ 1 ∧ w ≠ v := by
  by_contra h
  have hsub : (V : Set X) ⊆ {1, v} := by
    intro w hw
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · by_cases hwv : w = v
      · exact Or.inr hwv
      · exact (h ⟨w, hw, hw1, hwv⟩).elim
  have h1 : Nat.card V ≤ 2 := by
    calc Nat.card V = Nat.card ↥(V : Set X) := rfl
      _ = (V : Set X).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, v} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({v} : Set X).ncard + 1 := Set.ncard_insert_le 1 {v}
      _ = 2 := by rw [Set.ncard_singleton]
  rw [hV.card_four] at h1
  omega

theorem commFourAdj_kleinOf {g h z : X} (hg : g * g = 1) (hh : h * h = 1) (hz : z * z = 1)
    (hg1 : g ≠ 1) (hh1 : h ≠ 1) (hz1 : z ≠ 1) (hgz : g ≠ z) (hhz : h ≠ z)
    (hcgz : Commute g z) (hchz : Commute h z) (hgh : Commute g h) :
    CommFourAdj X (kleinOf hg hz hcgz) (kleinOf hh hz hchz) :=
  ⟨isKleinFour_kleinOf hg hz hg1 hz1 hgz hcgz, isKleinFour_kleinOf hh hz hh1 hz1 hhz hchz,
    kleinOf_le_centralizer hg hz hcgz (mem_centralizer_kleinOf hh hz hchz hgh hcgz)
      (mem_centralizer_kleinOf hh hz hchz hchz.symm (Commute.refl z))⟩

theorem comm_sup_zpowers {a b : X} (hab : a * b = b * a) :
    ∀ u ∈ zpowers a ⊔ zpowers b, ∀ v ∈ zpowers a ⊔ zpowers b, u * v = v * u := by
  have hC : zpowers a ⊔ zpowers b ≤ centralizer ({a, b} : Set X) := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_iff]
      intro h hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with rfl | rfl
      · rfl
      · exact hab.symm
    · rw [mem_centralizer_iff]
      intro h hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with rfl | rfl
      · exact hab
      · rfl
  intro u hu v hv
  have hu' : ∀ h ∈ ({a, b} : Set X), h * u = u * h := mem_centralizer_iff.mp (hC hu)
  have hD : zpowers a ⊔ zpowers b ≤ centralizer ({u} : Set X) := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hu' a (by simp)).symm
    · rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hu' b (by simp)).symm
  exact mem_centralizer_iff.mp (hD hv) u (Set.mem_singleton u)

def mulSubgroup {A V : Subgroup X} (hV : ∀ w ∈ V, ∀ u ∈ A, w * u * w⁻¹ ∈ A) : Subgroup X where
  carrier := {x | ∃ u ∈ A, ∃ w ∈ V, x = u * w}
  one_mem' := ⟨1, one_mem A, 1, one_mem V, by simp⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    obtain ⟨u', hu', w', hw', rfl⟩ := hy
    exact ⟨u * (w * u' * w⁻¹), mul_mem hu (hV w hw u' hu'), w * w', mul_mem hw hw', by group⟩
  inv_mem' := by
    intro x hx
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    exact ⟨w⁻¹ * u⁻¹ * w⁻¹⁻¹, hV w⁻¹ (inv_mem hw) u⁻¹ (inv_mem hu), w⁻¹, inv_mem hw, by group⟩

theorem mem_mulSubgroup {A V : Subgroup X} {hV : ∀ w ∈ V, ∀ u ∈ A, w * u * w⁻¹ ∈ A}
    {x : X} : x ∈ mulSubgroup hV ↔ ∃ u ∈ A, ∃ w ∈ V, x = u * w :=
  Iff.rfl

theorem g2_core {S A : Subgroup X} {a b t y : X} {k : ℕ} (hk : 0 < k) (hord : orderOf a = 2 * k)
    (hA : A = zpowers a ⊔ zpowers b) (hdisj : zpowers a ⊓ zpowers b = ⊥) (hab : a * b = b * a)
    (hσa : t * a * t = b) (ht2 : t * t = 1) (hy2 : y * y = 1) (hty : Commute t y)
    (hy1 : y ≠ 1) (htne : t ≠ y) (hAtv : A ⊓ (zpowers t ⊔ zpowers y) = ⊥)
    (hinv : ∀ x ∈ A, y * x * y = x⁻¹) (hS : S = A ⊔ zpowers t ⊔ zpowers y)
    (E F : Subgroup X) (hE : IsKleinFour E) (hES : E ≤ S) (hF : IsKleinFour F) (hFS : F ≤ S) :
    Relation.ReflTransGen (CommFourAdj X) E F := by
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hy_inv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hbA : b ∈ A := by
    rw [hA]
    exact Subgroup.mem_sup_right (mem_zpowers b)
  have haA : a ∈ A := by
    rw [hA]
    exact Subgroup.mem_sup_left (mem_zpowers a)
  have hσb : t * b * t = a := by
    rw [← hσa]
    calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
      _ = a := by rw [ht2]; simp
  have hσA : ∀ u ∈ A, t * u * t ∈ A := by
    have hle : zpowers a ⊔ zpowers b ≤ A.comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · rw [Subgroup.mem_comap]
        show t * a * t⁻¹ ∈ A
        rw [ht_inv, hσa]
        exact hbA
      · rw [Subgroup.mem_comap]
        show t * b * t⁻¹ ∈ A
        rw [ht_inv, hσb]
        exact haA
    intro u hu
    rw [hA] at hu
    have h' : t * u * t⁻¹ ∈ A := Subgroup.mem_comap.mp (hle hu)
    rwa [ht_inv] at h'
  have hAcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := by
    rw [hA]
    exact comm_sup_zpowers hab
  have hbpow : ∀ j : ℕ, b ^ j = t * a ^ j * t := by
    intro j
    rw [← hσa]
    have h := map_pow (MulAut.conj t) a j
    simp only [MulAut.conj_apply] at h
    rw [ht_inv] at h
    exact h.symm
  obtain ⟨p, hp⟩ : ∃ p : X, p = a ^ k := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : X, q = b ^ k := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : X, z = p * q := ⟨_, rfl⟩
  have hpA : p ∈ A := by
    rw [hp]
    exact pow_mem haA k
  have hqA : q ∈ A := by
    rw [hq]
    exact pow_mem hbA k
  have hzA : z ∈ A := by
    rw [hz]
    exact mul_mem hpA hqA
  have hp2 : p * p = 1 := by
    rw [hp, ← pow_add, (by rw [hord]; omega : k + k = orderOf a)]
    exact pow_orderOf_eq_one a
  have hp1 : p ≠ 1 := by
    rw [hp]
    exact pow_ne_one_of_lt_orderOf hk.ne' (by rw [hord]; omega)
  have hq' : q = t * p * t := by
    rw [hq, hbpow, hp]
  have hσp : t * p * t = q := hq'.symm
  have hσq : t * q * t = p := by
    calc t * q * t = t * (t * p * t) * t := by rw [hq']
      _ = (t * t) * p * (t * t) := by group
      _ = p := by rw [ht2]; simp
  have hq2 : q * q = 1 := by
    rw [hq']
    calc t * p * t * (t * p * t) = t * p * (t * t) * p * t := by group
      _ = t * (p * p) * t := by rw [ht2]; group
      _ = 1 := by rw [hp2, mul_one, ht2]
  have hq1 : q ≠ 1 := by
    intro h
    apply hp1
    calc p = (t * t) * p * (t * t) := by rw [ht2, one_mul, mul_one]
      _ = t * (t * p * t) * t := by group
      _ = 1 := by rw [← hq', h, mul_one, ht2]
  have hpq : p * q = q * p := hAcomm p hpA q hqA
  have hz2 : z * z = 1 := by
    rw [hz]
    calc p * q * (p * q) = p * (q * p) * q := by group
      _ = p * (p * q) * q := by rw [← hpq]
      _ = (p * p) * (q * q) := by group
      _ = 1 := by rw [hp2, hq2, mul_one]
  have hz1 : z ≠ 1 := by
    intro h
    have hqp : q = p := by
      calc q = (p * p) * q := by rw [hp2, one_mul]
        _ = p * (p * q) := by rw [mul_assoc]
        _ = p := by rw [← hz, h, mul_one]
    have hqa : q ∈ zpowers a := by
      rw [hqp, hp]
      exact pow_mem (mem_zpowers a) k
    have hqb : q ∈ zpowers b := by
      rw [hq]
      exact pow_mem (mem_zpowers b) k
    have hmem : q ∈ zpowers a ⊓ zpowers b := Subgroup.mem_inf.mpr ⟨hqa, hqb⟩
    rw [hdisj] at hmem
    exact hq1 (Subgroup.mem_bot.mp hmem)
  have hpz_ne : p ≠ z := by
    intro h
    apply hq1
    have hpq1 : p * q = p := by rw [← hz, ← h]
    calc q = (p * p) * q := by rw [hp2, one_mul]
      _ = p * (p * q) := by rw [mul_assoc]
      _ = p * p := by rw [hpq1]
      _ = 1 := hp2
  have hpz : Commute p z := by
    rw [hz]
    exact Commute.mul_right (Commute.refl p) (show Commute p q from hpq)
  have hyc : ∀ u ∈ A, u * u = 1 → y * u = u * y := by
    intro u hu hu2
    have h1 : y * u * y = u := by
      rw [hinv u hu, inv_eq_of_mul_eq_one_right hu2]
    calc y * u = y * u * y * y := by rw [mul_assoc (y * u) y y, hy2, mul_one]
      _ = u * y := by rw [h1]
  have hyu : ∀ u ∈ A, y * u = u⁻¹ * y := by
    intro u hu
    calc y * u = y * u * y * y := by rw [mul_assoc (y * u) y y, hy2, mul_one]
      _ = u⁻¹ * y := by rw [hinv u hu]
  have hyp : Commute y p := hyc p hpA hp2
  have hyq : Commute y q := hyc q hqA hq2
  have hyz : Commute y z := by
    rw [hz]
    exact Commute.mul_right hyp hyq
  have htzt : t * z * t = z := by
    rw [hz]
    have e : t * (p * q) * t = (t * p * t) * (t * q * t) := by
      calc t * (p * q) * t = t * p * (t * t) * q * t := by rw [ht2]; group
        _ = (t * p * t) * (t * q * t) := by group
    rw [e, hσp, hσq]
    exact hpq.symm
  have htz : Commute t z := by
    show t * z = z * t
    calc t * z = t * z * t * t := by rw [mul_assoc, ht2, mul_one]
      _ = z * t := by rw [htzt]
  have hyA : y ∉ A := by
    intro h
    have hmem : y ∈ A ⊓ (zpowers t ⊔ zpowers y) :=
      Subgroup.mem_inf.mpr ⟨h, Subgroup.mem_sup_right (mem_zpowers y)⟩
    rw [hAtv] at hmem
    exact hy1 (Subgroup.mem_bot.mp hmem)
  have hty1 : t * y ≠ 1 := by
    intro h
    apply htne
    rw [eq_inv_of_mul_eq_one_right h, ht_inv]
  have htyA : t * y ∉ A := by
    intro h
    have hmem : t * y ∈ A ⊓ (zpowers t ⊔ zpowers y) :=
      Subgroup.mem_inf.mpr ⟨h, mul_mem (Subgroup.mem_sup_left (mem_zpowers t))
        (Subgroup.mem_sup_right (mem_zpowers y))⟩
    rw [hAtv] at hmem
    exact hty1 (Subgroup.mem_bot.mp hmem)
  have uyA : ∀ u ∈ A, u * y ∉ A := by
    intro u hu h
    apply hyA
    simpa using mul_mem (inv_mem hu) h
  have hSz : S ≤ centralizer ({z} : Set X) := by
    rw [hS]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro u hu
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hAcomm z hzA u hu
    · refine zpowers_le.mpr ?_
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact htz.symm.eq
    · refine zpowers_le.mpr ?_
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hyz.symm.eq
  have hzS : ∀ s ∈ S, z * s = s * z := fun s hs =>
    mem_centralizer_iff.mp (hSz hs) z (Set.mem_singleton z)
  obtain ⟨V₀, hV₀⟩ : ∃ V : Subgroup X, V = kleinOf ht2 hy2 hty := ⟨_, rfl⟩
  have hV₀mem : ∀ w, w ∈ V₀ ↔ (w = t * y ∨ w = t ∨ w = y ∨ w = 1) := by
    intro w
    rw [hV₀]
    exact mem_kleinOf ht2 hy2 hty
  have hV₀N : ∀ w ∈ V₀, ∀ u ∈ A, w * u * w⁻¹ ∈ A := by
    intro w hw u hu
    rcases (hV₀mem w).mp hw with rfl | rfl | rfl | rfl
    · have e : t * y * u * (t * y)⁻¹ = t * (y * u * y) * t := by
        rw [mul_inv_rev, hy_inv, ht_inv]
        group
      rw [e, hinv u hu]
      exact hσA _ (inv_mem hu)
    · rw [ht_inv]
      exact hσA u hu
    · rw [hy_inv, hinv u hu]
      exact inv_mem hu
    · simpa using hu
  have hSM : S ≤ mulSubgroup hV₀N := by
    rw [hS]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro u hu
      exact mem_mulSubgroup.mpr ⟨u, hu, 1, one_mem V₀, by simp⟩
    · exact zpowers_le.mpr (mem_mulSubgroup.mpr
        ⟨1, one_mem A, t, (hV₀mem t).mpr (Or.inr (Or.inl rfl)), by simp⟩)
    · exact zpowers_le.mpr (mem_mulSubgroup.mpr
        ⟨1, one_mem A, y, (hV₀mem y).mpr (Or.inr (Or.inr (Or.inl rfl))), by simp⟩)
  have hnf : ∀ x ∈ S, ∃ u ∈ A, ∃ w ∈ V₀, x = u * w := fun x hx =>
    mem_mulSubgroup.mp (hSM hx)
  have chainA : ∀ x ∈ A, ∀ (hx2 : x * x = 1) (hcx : Commute x z), x ≠ 1 → x ≠ z →
      Relation.ReflTransGen (CommFourAdj X) (kleinOf hx2 hz2 hcx) (kleinOf hp2 hz2 hpz) := by
    intro x hx hx2 hcx hx1 hxz
    exact Relation.ReflTransGen.single
      (commFourAdj_kleinOf hx2 hp2 hz2 hx1 hp1 hz1 hxz hpz_ne hcx hpz (hAcomm x hx p hpA))
  have chainB : ∀ u ∈ A, ∀ (hx2 : u * y * (u * y) = 1) (hcx : Commute (u * y) z),
      u * y ≠ 1 → u * y ≠ z →
      Relation.ReflTransGen (CommFourAdj X) (kleinOf hx2 hz2 hcx) (kleinOf hp2 hz2 hpz) := by
    intro u hu hx2 hcx hx1 hxz
    exact Relation.ReflTransGen.single
      (commFourAdj_kleinOf hx2 hp2 hz2 hx1 hp1 hz1 hxz hpz_ne hcx hpz
        (Commute.mul_left (show Commute u p from hAcomm u hu p hpA) hyp))
  have chainC : ∀ u ∈ A, ∀ (hx2 : u * t * (u * t) = 1) (hcx : Commute (u * t) z),
      u * t ≠ 1 → u * t ≠ z →
      Relation.ReflTransGen (CommFourAdj X) (kleinOf hx2 hz2 hcx) (kleinOf hp2 hz2 hpz) := by
    intro u hu hx2 hcx hx1 hxz
    have hσu : t * u * t = u⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      calc u * (t * u * t) = u * t * (u * t) := by group
        _ = 1 := hx2
    have hL : u * t * (t * y) = u * y := by
      rw [mul_assoc, ← mul_assoc t t y, ht2, one_mul]
    have hσu' : t * u⁻¹ * t = u := by
      calc t * u⁻¹ * t = t * (t * u * t) * t := by rw [hσu]
        _ = (t * t) * u * (t * t) := by group
        _ = u := by rw [ht2]; simp
    have hR : t * y * (u * t) = u * y := by
      calc t * y * (u * t) = t * (y * u) * t := by group
        _ = t * (u⁻¹ * y) * t := by rw [hyu u hu]
        _ = t * u⁻¹ * (y * t) := by group
        _ = t * u⁻¹ * (t * y) := by rw [← hty.eq]
        _ = (t * u⁻¹ * t) * y := by group
        _ = u * y := by rw [hσu']
    have hgh : Commute (u * t) (t * y) := by
      show u * t * (t * y) = t * y * (u * t)
      rw [hL, hR]
    have hty2 : t * y * (t * y) = 1 := by
      calc t * y * (t * y) = t * (y * t) * y := by group
        _ = t * (t * y) * y := by rw [← hty.eq]
        _ = (t * t) * (y * y) := by group
        _ = 1 := by rw [ht2, hy2, one_mul]
    have hcty : Commute (t * y) z :=
      Commute.mul_left (show Commute t z from htz) (show Commute y z from hyz)
    have htyz_ne : t * y ≠ z := fun h => htyA (by rw [h]; exact hzA)
    have hyz_ne : y ≠ z := fun h => hyA (by rw [h]; exact hzA)
    have hty_y : Commute (t * y) y := Commute.mul_left hty (Commute.refl y)
    have s1 := commFourAdj_kleinOf hx2 hty2 hz2 hx1 hty1 hz1 hxz htyz_ne hcx hcty hgh
    have s2 := commFourAdj_kleinOf hty2 hy2 hz2 hty1 hy1 hz1 htyz_ne hyz_ne hcty hyz hty_y
    have s3 := commFourAdj_kleinOf hy2 hp2 hz2 hy1 hp1 hz1 hyz_ne hpz_ne hyz hpz hyp
    exact (Relation.ReflTransGen.single s1).trans
      ((Relation.ReflTransGen.single s2).trans (Relation.ReflTransGen.single s3))
  have chainD : ∀ u ∈ A, ∀ (hx2 : u * (t * y) * (u * (t * y)) = 1)
      (hcx : Commute (u * (t * y)) z), u * (t * y) ≠ 1 → u * (t * y) ≠ z →
      Relation.ReflTransGen (CommFourAdj X) (kleinOf hx2 hz2 hcx) (kleinOf hp2 hz2 hpz) := by
    intro u hu hx2 hcx hx1 hxz
    have hxinv : (u * (t * y))⁻¹ = u * (t * y) := inv_eq_of_mul_eq_one_right hx2
    have hxinv' : (u * (t * y))⁻¹ = y * t * u⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hy_inv, ht_inv]
    have hx_eq : u * (t * y) = y * t * u⁻¹ := hxinv.symm.trans hxinv'
    have hcomm' : u * t = t * u := by
      calc u * t = u * (t * (y * y)) := by rw [hy2, mul_one]
        _ = u * (t * y) * y := by group
        _ = (y * t * u⁻¹) * y := by rw [hx_eq]
        _ = t * y * u⁻¹ * y := by rw [← hty.eq]
        _ = t * (y * u⁻¹ * y) := by group
        _ = t * u := by rw [hinv u⁻¹ (inv_mem hu), inv_inv]
    have e1 : u * (t * y) * (u * y) = t := by
      calc u * (t * y) * (u * y) = (u * t) * (y * u * y) := by group
        _ = (u * t) * u⁻¹ := by rw [hinv u hu]
        _ = (t * u) * u⁻¹ := by rw [hcomm']
        _ = t := by group
    have e2 : u * y * (u * (t * y)) = t := by
      calc u * y * (u * (t * y)) = u * (y * u) * (t * y) := by group
        _ = u * (u⁻¹ * y) * (t * y) := by rw [hyu u hu]
        _ = y * (t * y) := by group
        _ = (y * t) * y := by group
        _ = (t * y) * y := by rw [← hty.eq]
        _ = t := by rw [mul_assoc, hy2, mul_one]
    have hgh : Commute (u * (t * y)) (u * y) := e1.trans e2.symm
    have huy2 : u * y * (u * y) = 1 := by
      calc u * y * (u * y) = u * (y * u) * y := by group
        _ = u * (u⁻¹ * y) * y := by rw [hyu u hu]
        _ = y * y := by group
        _ = 1 := hy2
    have huy1 : u * y ≠ 1 := fun h => uyA u hu (by rw [h]; exact one_mem A)
    have huyz : u * y ≠ z := fun h => uyA u hu (by rw [h]; exact hzA)
    have hcuy : Commute (u * y) z :=
      Commute.mul_left (show Commute u z from hAcomm u hu z hzA) (show Commute y z from hyz)
    have s1 := commFourAdj_kleinOf hx2 huy2 hz2 hx1 huy1 hz1 hxz huyz hcx hcuy hgh
    have s2 := commFourAdj_kleinOf huy2 hp2 hz2 huy1 hp1 hz1 huyz hpz_ne hcuy hpz
      (Commute.mul_left (show Commute u p from hAcomm u hu p hpA) hyp)
    exact (Relation.ReflTransGen.single s1).trans (Relation.ReflTransGen.single s2)
  have chain : ∀ x ∈ S, ∀ (hx2 : x * x = 1) (hcx : Commute x z), x ≠ 1 → x ≠ z →
      Relation.ReflTransGen (CommFourAdj X) (kleinOf hx2 hz2 hcx) (kleinOf hp2 hz2 hpz) := by
    intro x hxS hx2 hcx hx1 hxz
    obtain ⟨u, hu, w, hw, hxw⟩ := hnf x hxS
    rcases (hV₀mem w).mp hw with rfl | rfl | rfl | rfl
    · subst hxw
      exact chainD u hu hx2 hcx hx1 hxz
    · subst hxw
      exact chainC u hu hx2 hcx hx1 hxz
    · subst hxw
      exact chainB u hu hx2 hcx hx1 hxz
    · exact chainA x (by rw [hxw, mul_one]; exact hu) hx2 hcx hx1 hxz
  have hEH : ∀ E' : Subgroup X, IsKleinFour E' → E' ≤ S →
      Relation.ReflTransGen (CommFourAdj X) E' (kleinOf hp2 hz2 hpz) := by
    intro E' hE' hES'
    obtain ⟨e, heE, he1, hez⟩ := exists_ne_one_ne_of_kleinFour hE' z
    have he2 : e * e = 1 := by
      rw [← pow_two]
      exact FooteLit.sq_eq_one_of_isKleinFour hE' heE
    have hcez : Commute e z := (hzS e (hES' heE)).symm
    have hEc : e ∈ centralizer (E' : Set X) :=
      mem_centralizer_iff.mpr fun k hk => FooteLit.commute_of_sq_eq_one
        (fun x hx => FooteLit.sq_eq_one_of_isKleinFour hE' hx) hk heE
    have hzc : z ∈ centralizer (E' : Set X) :=
      mem_centralizer_iff.mpr fun k hk => (hzS k (hES' hk)).symm
    have hadj : CommFourAdj X (kleinOf he2 hz2 hcez) E' :=
      ⟨isKleinFour_kleinOf he2 hz2 he1 hz1 hez hcez, hE',
        kleinOf_le_centralizer he2 hz2 hcez hEc hzc⟩
    exact (Relation.ReflTransGen.single (commFourAdj_symm hadj)).trans
      (chain e (hES' heE) he2 hcez he1 hez)
  exact (hEH E hE hES).trans (reflTransGen_commFourAdj_symm (hEH F hF hFS))

end G2Four

open G2Four in
theorem g2_fourGroups_joined {X : Type} [Group X] {S A : Subgroup X} {a t y : X} {n : ℕ}
    (hn : 2 ≤ n) (hsh : CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Shape S A a t y n)
    (E F : Subgroup X) (hE : IsKleinFour E) (hES : E ≤ S) (hF : IsKleinFour F) (hFS : F ≤ S) :
    Relation.ReflTransGen (CommFourAdj X) E F := by
  obtain ⟨hord, hA, hdisj, hcomm, ht2, hy2, hty, _, hy1, htne, hAtv, hinv, hS⟩ := hsh
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  refine G2Four.g2_core (k := 2 ^ m) (pow_pos (by norm_num) m) ?_ hA hdisj hcomm ?_ ht2 hy2
    hty hy1 htne hAtv hinv hS E F hE hES hF hFS
  · rw [hord]
    ring
  · rw [ht_inv]

theorem leafG2_holds :
    LeafG2 := by
  intro X _ _ _ _ p f hp hp2 hf hmod S E F hE hES hF hFS
  obtain ⟨A, a, t, y, n, hn, hsh, -⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.g2_sylow_shape_fwd X p f hp hp2 (by omega) hmod S
  exact g2_fourGroups_joined hn hsh E F hE hES hF hFS

end CFSG.ComponentClassification.Sol76.Sig.GSYard02

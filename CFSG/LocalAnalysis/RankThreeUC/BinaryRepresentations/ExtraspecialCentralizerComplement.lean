module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.ExtraspecialHyperplaneVocabulary
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace BinaryRepresentations

namespace ExtraspecialCentralizerComplement

open Subgroup

open scoped commutatorElement

namespace Aux

variable {K : Type*} [Group K]

@[expose] def cmap (hK : ∀ a b : K, ⁅a, b⁆ ∈ Subgroup.center K) (x : K) : K →* Subgroup.center K where
  toFun a := ⟨⁅a, x⁆, hK a x⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    have h1 : ⁅b, x⁆ * a = a * ⁅b, x⁆ := (Subgroup.mem_center_iff.mp (hK b x) a).symm
    show ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆
    have h2 : ⁅a, x⁆ * ⁅b, x⁆ = ⁅b, x⁆ * ⁅a, x⁆ := (Subgroup.mem_center_iff.mp (hK a x) _).symm
    simp only [commutatorElement_def] at *
    calc a * b * x * (a * b)⁻¹ * x⁻¹ = a * (b * x * b⁻¹ * x⁻¹) * x * a⁻¹ * x⁻¹ := by group
      _ = (a * (b * x * b⁻¹ * x⁻¹)) * x * a⁻¹ * x⁻¹ := rfl
      _ = ((b * x * b⁻¹ * x⁻¹) * a) * x * a⁻¹ * x⁻¹ := by rw [← h1]
      _ = (b * x * b⁻¹ * x⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
      _ = _ := h2.symm

@[expose] def psi (hK : ∀ a b : K, ⁅a, b⁆ ∈ Subgroup.center K) (x y : K) :
    K →* Subgroup.center K × Subgroup.center K := (cmap hK x).prod (cmap hK y)

lemma mem_ker_psi (hK : ∀ a b : K, ⁅a, b⁆ ∈ Subgroup.center K) (x y a : K) :
    a ∈ (psi hK x y).ker ↔ ⁅a, x⁆ = 1 ∧ ⁅a, y⁆ = 1 := by
  simp only [MonoidHom.mem_ker, psi, MonoidHom.prod_apply, Prod.mk_eq_one]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Subtype.ext h1, Subtype.ext h2⟩

section

variable (hK : ∀ a b : K, ⁅a, b⁆ ∈ Subgroup.center K) (x y : K)

@[expose] def cc : Subgroup.center K := ⟨⁅x, y⁆, hK x y⟩

lemma psi_x : psi hK x y x = (1, cc hK x y) := by
  ext <;> simp [psi, cmap, cc]

lemma psi_y : psi hK x y y = ((cc hK x y)⁻¹, 1) := by
  ext <;> simp [psi, cmap, cc, commutatorElement_inv]

lemma psi_surj_pre {p : ℕ} [Fact p.Prime] (hZ : Nat.card (Subgroup.center K) = p)
    (hc : ⁅x, y⁆ ≠ 1) (z : Subgroup.center K × Subgroup.center K) :
    ∃ i j : ℤ, psi hK x y (y ^ i * x ^ j) = z := by
  have hc' : cc hK x y ≠ 1 := fun h => hc (congrArg Subtype.val h)
  have htop := zpowers_eq_top_of_prime_card hZ hc'
  obtain ⟨i, hi⟩ : z.1 ∈ Subgroup.zpowers (cc hK x y) := by rw [htop]; trivial
  obtain ⟨j, hj⟩ : z.2 ∈ Subgroup.zpowers (cc hK x y) := by rw [htop]; trivial
  refine ⟨-i, j, ?_⟩
  rw [map_mul, map_zpow, map_zpow, psi_x, psi_y]
  ext <;> simp [hi, hj]

end

end Aux

variable {G : Type} [Group G]

theorem complement_exists {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (H : Subgroup G) (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (hcard : Nat.card H = p ^ (1 + 2 * n)) (hn : 1 < n)
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    ∃ L : Subgroup G, L ≤ H ⊓ centralizer (X : Set G) ∧
      H ⊓ centralizer (X : Set G) = X ⊔ L ∧ Disjoint X L ∧
      CFSG.IsExtraspecialPGroup p L ∧ Monoid.exponent L = p ∧
      Nat.card L = p ^ (1 + 2 * (n - 1)) ∧ centerIn L = centerIn H := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨hPg, hcomm, hfratt, hcenter⟩ := hH
  have hK : ∀ a b : H, ⁅a, b⁆ ∈ Subgroup.center H := by
    intro a b
    rw [← hcomm, commutator_def]
    exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
  have hcenterIn : Nat.card (centerIn H) = p := by
    rw [centerIn, Subgroup.card_map_of_injective H.subtype_injective]; exact hcenter
  haveI : Finite (centerIn H) := Nat.finite_of_card_ne_zero (by rw [hcenterIn]; exact hp.ne_zero)
  haveI : Fact (Nat.Prime (Nat.card X)) := ⟨hXp ▸ hp⟩
  obtain ⟨x, hxX, hXeq⟩ : ∃ x ∈ X, X = Subgroup.zpowers x := by
    obtain ⟨g, hg⟩ := (isCyclic_of_prime_card hXp : IsCyclic X)
    refine ⟨g, g.2, ?_⟩
    apply le_antisymm
    · intro z hz
      obtain ⟨k, hk⟩ := hg ⟨z, hz⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]; exact g.2
  have hxH : x ∈ H := hXH hxX
  set x' : H := ⟨x, hxH⟩ with hx'
  have hx'c : x' ∉ Subgroup.center H := by
    intro hxc
    apply hXZ
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcenterIn, hXp])
    rw [hXeq, Subgroup.zpowers_le]
    exact ⟨x', hxc, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : H, ⁅x', y'⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hx'c
    rw [Subgroup.mem_center_iff]
    intro g
    exact (commutatorElement_eq_one_iff_mul_comm.mp (hcon g)).symm
  set ψ := Aux.psi hK x' y' with hψ
  set y : G := (y' : G) with hy
  set L : Subgroup G := H ⊓ centralizer ({x, y} : Set G) with hL
  have hLH : L ≤ H := inf_le_left
  have hLmem : ∀ h : H, (h : G) ∈ L ↔ h ∈ ψ.ker := by
    intro h
    rw [hψ, Aux.mem_ker_psi, hL, Subgroup.mem_inf, mem_centralizer_iff,
      commutatorElement_eq_one_iff_mul_comm, commutatorElement_eq_one_iff_mul_comm]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, hx', hy,
      Subtype.ext_iff, Subgroup.coe_mul]
    simp only [h.2, true_and]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩
  have hLker : ψ.ker = L.subgroupOf H := by
    ext h; rw [Subgroup.mem_subgroupOf, hLmem]
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨i, j, hij⟩ := Aux.psi_surj_pre hK x' y' hcenter hy' z
    exact ⟨_, hij⟩
  have hLcard : Nat.card L = p ^ (1 + 2 * (n - 1)) := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective hsurj
    rw [Nat.card_prod, hcenter, hLker, hcard] at h1
    have h2 : Nat.card (L.subgroupOf H) = Nat.card L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv
    rw [h2] at h1
    have h3 : p ^ (1 + 2 * n) = p ^ (1 + 2 * (n - 1)) * (p * p) := by
      rw [← pow_two, ← pow_add]; congr 1; omega
    rw [h3] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hp.pos hp.pos) h1
  have hxcomm : ∀ l ∈ L, x * l = l * x := fun l hl =>
    mem_centralizer_iff.mp (Subgroup.mem_inf.mp hl).2 x (by simp)
  have hycomm : ∀ l ∈ L, y * l = l * y := fun l hl =>
    mem_centralizer_iff.mp (Subgroup.mem_inf.mp hl).2 y (by simp)
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    intro a ha b hb
    rw [hXeq] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact (Commute.zpow_zpow_self x i j).eq
  have hLX : L ≤ centralizer (X : Set G) := by
    intro l hl
    rw [mem_centralizer_iff]
    intro g hg
    rw [hXeq] at hg
    obtain ⟨k, rfl⟩ := hg
    exact (Commute.zpow_left (show Commute x l from hxcomm l hl) k).eq
  have hLle : L ≤ H ⊓ centralizer (X : Set G) := le_inf hLH hLX
  have hxp : x' ^ p = 1 := by
    have := Monoid.pow_exponent_eq_one x'
    rwa [hexp] at this
  have hc' : Aux.cc hK x' y' ≠ 1 := fun h => hy' (congrArg Subtype.val h)
  have hc'p : orderOf (Aux.cc hK x' y') = p := by
    have h1 : orderOf (Aux.cc hK x' y') ∣ p := hcenter ▸ orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc'
    · exact h
  have hψx : ∀ j : ℤ, ψ (x' ^ j) = (1, (Aux.cc hK x' y') ^ j) := by
    intro j
    rw [map_zpow, hψ, Aux.psi_x]
    simp
  have hsup : H ⊓ centralizer (X : Set G) = X ⊔ L := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgH, hgc⟩ := Subgroup.mem_inf.mp hg
      set h : H := ⟨g, hgH⟩ with hh
      have hhx : ⁅h, x'⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        apply Subtype.ext
        exact (mem_centralizer_iff.mp hgc x hxX).symm
      have hψh : ψ h = (1, (ψ h).2) := by
        refine Prod.ext (Subtype.ext ?_) rfl
        exact hhx
      have htop := zpowers_eq_top_of_prime_card hcenter hc'
      obtain ⟨j, hj⟩ : (ψ h).2 ∈ Subgroup.zpowers (Aux.cc hK x' y') := by rw [htop]; trivial
      have h1 : (x' ^ j)⁻¹ * h ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hψx, hψh, ← hj]
        simp
      have h2 := (hLmem _).mpr h1
      have h3 : (((x' ^ j)⁻¹ * h : H) : G) = (x ^ j)⁻¹ * g := by simp [hx', hh]
      have h3' : g = x ^ j * (((x' ^ j)⁻¹ * h : H) : G) := by rw [h3, mul_inv_cancel_left]
      rw [h3']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (by rw [hXeq]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _))
        (Subgroup.mem_sup_right h2)
    · refine sup_le (le_inf hXH ?_) hLle
      intro g hg
      rw [mem_centralizer_iff]
      exact fun b hb => hXcomm b hb g hg
  have hdisj : Disjoint X L := by
    rw [Subgroup.disjoint_def]
    intro g hgX hgL
    have hgH : g ∈ H := hXH hgX
    rw [hXeq] at hgX
    obtain ⟨k, rfl⟩ := hgX
    have hg1 : (⟨x ^ k, hgH⟩ : H) = x' ^ k := by apply Subtype.ext; simp [hx']
    have h1 := (hLmem ⟨x ^ k, hgH⟩).mp hgL
    rw [hg1, MonoidHom.mem_ker, hψx] at h1
    have h2 : (Aux.cc hK x' y') ^ k = 1 := (Prod.mk.inj h1).2
    have h3 : (p : ℤ) ∣ k := by rw [← hc'p]; exact orderOf_dvd_iff_zpow_eq_one.mpr h2
    obtain ⟨m, rfl⟩ := h3
    have : x' ^ ((p : ℤ) * m) = 1 := by
      rw [zpow_mul, zpow_natCast, hxp, one_zpow]
    have := congrArg Subtype.val this
    simpa [hx'] using this
  haveI : Finite L := Nat.finite_of_card_ne_zero (by rw [hLcard]; exact pow_ne_zero _ hp.ne_zero)
  have hexpL : Monoid.exponent L = p := by
    have h1 : Monoid.exponent L ∣ Monoid.exponent H := by
      have := Monoid.exponent_dvd_of_monoidHom (Subgroup.inclusion hLH) (Subgroup.inclusion_injective hLH)
      exact this
    rw [hexp] at h1
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exfalso
      have hall : ∀ g : L, g = 1 := fun g => by simpa [h] using Monoid.pow_exponent_eq_one g
      haveI : Subsingleton L := ⟨fun a b => by rw [hall a, hall b]⟩
      have h2 := Nat.card_of_subsingleton (1 : L)
      rw [hLcard] at h2
      have := (Nat.pow_eq_one.mp h2)
      rcases this with h | h
      · exact hp.ne_one h
      · omega
    · exact h
  have hcenterEq : centerIn L = centerIn H := by
    ext g
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hlc : ∀ k ∈ L, k * (l : G) = l * k := fun k hk => by
        have := Subgroup.mem_center_iff.mp hl ⟨k, hk⟩
        exact congrArg Subtype.val this
      refine ⟨⟨(l : G), hLH l.2⟩, ?_, rfl⟩
      refine Subgroup.mem_center_iff.mpr (fun h => ?_)
      obtain ⟨i, j, hij⟩ := Aux.psi_surj_pre hK x' y' hcenter hy' (ψ h)
      have hm : (y' ^ i * x' ^ j)⁻¹ * h ∈ ψ.ker := by
        have hij' : ψ (y' ^ i * x' ^ j) = ψ h := hij
        rw [MonoidHom.mem_ker, map_mul, map_inv, hij']; simp
      have h2 := (hLmem _).mpr hm
      set m : G := (((y' ^ i * x' ^ j)⁻¹ * h : H) : G) with hmdef
      have hdec : (h : G) = y ^ i * x ^ j * m := by
        simp only [hmdef, hx', hy, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow,
          Subgroup.coe_mk]
        group
      have hxl : Commute (x ^ j) (l : G) :=
        Commute.zpow_left (show Commute x (l : G) from hxcomm l l.2) j
      have hyl : Commute (y ^ i) (l : G) :=
        Commute.zpow_left (show Commute y (l : G) from hycomm l l.2) i
      apply Subtype.ext
      show (h : G) * l = l * h
      calc (h : G) * l = (y ^ i * x ^ j) * (m * l) := by rw [hdec, mul_assoc]
        _ = (y ^ i * x ^ j) * (l * m) := by rw [hlc m h2]
        _ = ((y ^ i * x ^ j) * l) * m := by simp only [mul_assoc]
        _ = (l * (y ^ i * x ^ j)) * m := by rw [(hyl.mul_left hxl).eq]
        _ = l * (y ^ i * x ^ j * m) := by simp only [mul_assoc]
        _ = l * h := by rw [← hdec]
    · rintro ⟨z, hz, rfl⟩
      have hzL : (z : G) ∈ L := by
        refine (hLmem z).mpr ?_
        rw [hψ, Aux.mem_ker_psi]
        exact ⟨commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz x').symm,
          commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz y').symm⟩
      refine ⟨⟨z, hzL⟩, ?_, rfl⟩
      refine Subgroup.mem_center_iff.mpr (fun k => ?_)
      apply Subtype.ext
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hLH k.2⟩)
      exact this
  have hcenterL : Nat.card (Subgroup.center L) = p := by
    have : Nat.card (centerIn L) = p := by rw [hcenterEq]; exact hcenterIn
    rwa [centerIn, Subgroup.card_map_of_injective L.subtype_injective] at this
  have hcommle : _root_.commutator L ≤ Subgroup.center L := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h1 : (⁅(a : G), (b : G)⁆) ∈ centerIn L := by
      rw [hcenterEq]
      exact ⟨⁅(⟨a, hLH a.2⟩ : H), ⟨b, hLH b.2⟩⁆, hK _ _, rfl⟩
    obtain ⟨l, hl, hle⟩ := h1
    have : l = ⁅a, b⁆ := Subtype.ext hle
    rw [← this]; exact hl
  have hnotab : _root_.commutator L ≠ ⊥ := by
    intro h
    rw [commutator_eq_bot_iff_center_eq_top] at h
    have h1 := hcenterL
    rw [h, Subgroup.card_top, hLcard] at h1
    have h2 : p ^ (1 + 2 * (n - 1)) = p ^ 1 := by rw [h1, pow_one]
    have := Nat.pow_right_injective hp.two_le h2
    omega
  have hcommL : _root_.commutator L = Subgroup.center L := by
    have h1 : Nat.card (_root_.commutator L) ∣ p := hcenterL ▸ Subgroup.card_dvd_of_le hcommle
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hnotab
    · exact Subgroup.eq_of_le_of_card_ge hcommle (by rw [h, hcenterL])
  haveI : Fact (IsPGroup p L) := ⟨IsPGroup.of_card hLcard⟩
  have hfrL : frattini L = _root_.commutator L := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := p)]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ (h | ⟨a, rfl⟩)
      · exact h
      · have := Monoid.pow_exponent_eq_one a
        rw [hexpL] at this
        show a ^ p ∈ _
        rw [this]; exact Subgroup.one_mem _
    · exact fun g hg => Subgroup.subset_closure (Or.inl hg)
  exact ⟨L, hLle, hsup, hdisj, ⟨IsPGroup.of_card hLcard, hcommL, hfrL.trans hcommL, hcenterL⟩,
    hexpL, hLcard, hcenterEq⟩

end ExtraspecialCentralizerComplement

end BinaryRepresentations

end CFSG.LocalAnalysis.RankThreeUC

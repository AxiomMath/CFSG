module

public import CFSG.ClassicalInvolution.Q3.Q3T6YDiag
public import CFSG.ClassicalInvolution.Q3.Q3T6YDichot
public import CFSG.ClassicalInvolution.Q3.Q3T6BDiagSub

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6B
  CFSG.ClassicalInvolution.Q3.Q3T6X
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem exists_pow_conj_of_involutions {e e' : G} (he : e * e = 1) (he' : e' * e' = 1)
    (hodd : Odd (orderOf (e * e'))) :
    ∃ n : ℕ, e = (e * e') ^ n * e' * ((e * e') ^ n)⁻¹ := by
  obtain ⟨j, hj⟩ := hodd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have he'i : e'⁻¹ = e' := inv_eq_of_mul_eq_one_right he'
  have hinv : e' * (e * e') * e'⁻¹ = (e * e')⁻¹ := by
    rw [he'i]
    calc e' * (e * e') * e' = e' * e * (e' * e') := by group
      _ = e' * e := by rw [he', mul_one]
      _ = (e * e')⁻¹ := by rw [mul_inv_rev, hei, he'i]
  have hw1 : (e * e') ^ (2 * j + 1) = 1 := hj ▸ pow_orderOf_eq_one (e * e')
  refine ⟨j + 1, ?_⟩
  have hc1 : e' * (e * e') ^ (j + 1) * e' = ((e * e') ^ (j + 1))⁻¹ := by
    have := conj_pow (i := j + 1) (a := e') (b := e * e')
    rw [hinv, inv_pow, he'i] at this
    exact this.symm
  have hc2 : e' * ((e * e') ^ (j + 1))⁻¹ * e' = (e * e') ^ (j + 1) := by
    calc e' * ((e * e') ^ (j + 1))⁻¹ * e' = (e' * (e * e') ^ (j + 1) * e')⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, he'i, mul_assoc]
      _ = (((e * e') ^ (j + 1))⁻¹)⁻¹ := by rw [hc1]
      _ = (e * e') ^ (j + 1) := inv_inv _
  have hc3 : e' * ((e * e') ^ (j + 1))⁻¹ = (e * e') ^ (j + 1) * e' := by
    calc e' * ((e * e') ^ (j + 1))⁻¹ = e' * ((e * e') ^ (j + 1))⁻¹ * (e' * e') := by
          rw [he', mul_one]
      _ = (e' * ((e * e') ^ (j + 1))⁻¹ * e') * e' := by rw [mul_assoc _ e' e']
      _ = (e * e') ^ (j + 1) * e' := by rw [hc2]
  calc e = (e * e') * e' := by rw [mul_assoc, he', mul_one]
    _ = (e * e') ^ (j + 1) * (e * e') ^ (j + 1) * e' := by
        rw [← pow_add, show j + 1 + (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, hw1, one_mul]
    _ = (e * e') ^ (j + 1) * e' * ((e * e') ^ (j + 1))⁻¹ := by
        rw [mul_assoc _ e', hc3, mul_assoc]

theorem mem_of_odd_of_mul_central {H : Subgroup G} {δ x g : G} (hδ : δ ∈ H) (hx2 : x * x = 1)
    (hxc : x * δ = δ * x) (hg : g = δ * x) (hodd : Odd (orderOf g)) : g ∈ H := by
  obtain ⟨j, hj⟩ := hodd
  have hg2 : g * g = δ * δ := by
    rw [hg]
    calc δ * x * (δ * x) = δ * (x * δ) * x := by group
      _ = δ * (δ * x) * x := by rw [hxc]
      _ = δ * δ * (x * x) := by group
      _ = δ * δ := by rw [hx2, mul_one]
  have h1 : g ^ (2 * j + 1) = 1 := hj ▸ pow_orderOf_eq_one g
  have h2 : g = (δ * δ) ^ (j + 1) := by
    calc g = g ^ (2 * j + 2) := by
          rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, pow_succ, h1, one_mul]
      _ = (g * g) ^ (j + 1) := by rw [← pow_two, ← pow_mul]; ring_nf
      _ = (δ * δ) ^ (j + 1) := by rw [hg2]
  rw [h2]
  exact H.pow_mem (H.mul_mem hδ hδ) _

end Group

variable {F : Type} [Group F] [Finite F]

section XSide

variable {X : Subgroup F} {x y : F}

theorem y_mem_Cz (hs : Swap X x y) : y ∈ Cz x :=
  Subgroup.mem_centralizer_singleton_iff.mpr hs.comm

theorem zb_comm (z : F) (a : Qz z) : a * zb z = zb z * a := by
  have : a ∈ Subgroup.centralizer ({zb z} : Set (Qz z)) := by
    rw [centralizer_zb]
    exact Subgroup.mem_top a
  exact Subgroup.mem_centralizer_singleton_iff.mp this

theorem zpowers_y_comm (hs : Swap X x y) : ∀ k ∈ Subgroup.zpowers y, k * x = x * k := by
  intro k hk
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  exact Commute.zpow_left (show Commute y x from hs.comm) n

theorem twinProd_zpowers_le_Cz (hs : Swap X x y) : twinProd (Subgroup.zpowers y) X ≤ Cz x :=
  twinProd_le_centralizer' hs.member (zpowers_y_comm hs)

theorem deltaStar_le_Cz (hs : Swap X x y) : deltaStar X y ≤ Cz x :=
  (oddClosure_le _).trans (inf_le_left.trans (twinProd_zpowers_le_Cz hs))

theorem twinProd_zpowers_le_sup (hs : Swap X x y) :
    twinProd (Subgroup.zpowers y) X ≤ X ⊔ conjSub y X := by
  have hy2 : y * y = 1 := hs.sq
  have hpow : ∀ n : ℤ, y ^ n = 1 ∨ y ^ n = y := by
    intro n
    rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, zpow_two, hy2, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, hy2, one_zpow, one_mul]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨k, hk, rfl⟩ := hL
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  rcases hpow n with h | h
  · rw [h, conjSub_one]
    exact le_sup_left
  · rw [h]
    exact le_sup_right

theorem swap_imgz (hs : Swap X x y) :
    Swap (imgz x X) (zb x) (piz x ⟨y, y_mem_Cz hs⟩) where
  member := Mem3.imgz hs.member
  sq := by
    rw [← map_mul]
    have : (⟨y, y_mem_Cz hs⟩ * ⟨y, y_mem_Cz hs⟩ : ↥(Cz x)) = 1 := Subtype.ext hs.sq
    rw [this, map_one]
  comm := zb_comm x (piz x ⟨y, y_mem_Cz hs⟩)
  moves := by
    intro h
    have hXC : X ≤ Cz x := hs.member.le_centralizer
    have hO : oddCoreOf (Cz x) ≤ X := oddCoreOf_Cz_le hs.member
    rw [imgz_conjSub x X ⟨y, y_mem_Cz hs⟩] at h
    exact hs.moves (eq_of_imgz_eq x (conjSub_le_Cz hXC ⟨y, y_mem_Cz hs⟩) hXC
      (oddCoreOf_Cz_le_conjSub hO ⟨y, y_mem_Cz hs⟩) hO h)

theorem piz_deltaStar_mem (hs : Swap X x y) {k : F} (hk : k ∈ deltaStar X y) :
    ∃ hC : k ∈ Cz x, piz x ⟨k, hC⟩ ∈ diagGroupOf (swap_imgz hs) (exAt_zb x) := by
  have hyC := y_mem_Cz hs
  have hs' := swap_imgz hs
  have hex := exAt_zb x
  have hx2 : zb x * zb x = 1 := zb_mul_self x hs.member.mul_self
  have hne : X ≠ conjSub y X := fun h => hs.moves h.symm
  have hXN : X ≤ Subgroup.normalizer (conjSub y X : Set F) :=
    (hs.member.twin_facts hs.twin hne).2.1
  have hXC : X ≤ Cz x := hs.member.le_centralizer
  have hX'C : conjSub y X ≤ Cz x := conjSub_le_Cz hXC ⟨y, hyC⟩
  have hk' : k ∈ Subgroup.closure {g : F | g ∈ swapFix X y ∧ Odd (orderOf g)} := hk
  refine Subgroup.closure_induction
    (p := fun k _ => ∃ hC : k ∈ Cz x, piz x ⟨k, hC⟩ ∈ diagGroupOf hs' hex) ?_ ?_ ?_ ?_ hk'
  · rintro g ⟨⟨hgE, hgy⟩, hgodd⟩
    have hgC : g ∈ Cz x := twinProd_zpowers_le_Cz hs hgE
    refine ⟨hgC, ?_⟩
    have hgsup := twinProd_zpowers_le_sup hs hgE
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X (conjSub y X) hXN]
      at hgsup
    obtain ⟨a, ha, b, hb, hab⟩ := hgsup
    have haC : a ∈ Cz x := hXC ha
    have hbC : b ∈ Cz x := hX'C hb
    have hπg : piz x ⟨g, hgC⟩ = piz x ⟨a, haC⟩ * piz x ⟨b, hbC⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hab.symm
    have h1 : piz x ⟨g, hgC⟩ ∈ imgz x X ⊔ conjSub (piz x ⟨y, hyC⟩) (imgz x X) := by
      rw [hπg]
      refine Subgroup.mul_mem_sup (piz_mem_imgz haC ha) ?_
      rw [imgz_conjSub x X ⟨y, hyC⟩]
      exact piz_mem_imgz hbC hb
    have h2 : piz x ⟨g, hgC⟩ * piz x ⟨y, hyC⟩ = piz x ⟨y, hyC⟩ * piz x ⟨g, hgC⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgy)
    obtain ⟨c, hcX, hc⟩ := fixed_decomp hs' hex h1 h2
    have hodd : Odd (orderOf (piz x ⟨g, hgC⟩)) := by
      refine hgodd.of_dvd_nat ?_
      have := orderOf_map_dvd (piz x) (⟨g, hgC⟩ : ↥(Cz x))
      rwa [Subgroup.orderOf_mk] at this
    rcases hc with hc | hc
    · rw [hc]
      exact diag_mem_diagGroupOf hs' hex hcX
    · exact mem_of_odd_of_mul_central (diag_mem_diagGroupOf hs' hex hcX) hx2
        (zb_comm x _).symm hc hodd
  · refine ⟨(Cz x).one_mem, ?_⟩
    have : (⟨1, (Cz x).one_mem⟩ : ↥(Cz x)) = 1 := rfl
    rw [this, map_one]
    exact Subgroup.one_mem _
  · rintro k₁ k₂ - - ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    refine ⟨(Cz x).mul_mem h₁ h₂, ?_⟩
    have : (⟨k₁ * k₂, (Cz x).mul_mem h₁ h₂⟩ : ↥(Cz x)) = ⟨k₁, h₁⟩ * ⟨k₂, h₂⟩ := rfl
    rw [this, map_mul]
    exact Subgroup.mul_mem _ h₁' h₂'
  · rintro k₁ - ⟨h₁, h₁'⟩
    refine ⟨(Cz x).inv_mem h₁, ?_⟩
    have : (⟨k₁⁻¹, (Cz x).inv_mem h₁⟩ : ↥(Cz x)) = (⟨k₁, h₁⟩)⁻¹ := rfl
    rw [this, map_inv]
    exact Subgroup.inv_mem _ h₁'

theorem diag_piz_mem_imgz (hs : Swap X x y) {a : F} (ha : a ∈ X) :
    diag (piz x ⟨y, y_mem_Cz hs⟩) (piz x ⟨a, hs.member.le_centralizer ha⟩) ∈
      imgz x (deltaStar X y) := by
  have hyC := y_mem_Cz hs
  have haC : a ∈ Cz x := hs.member.le_centralizer ha
  obtain ⟨w, hw, o, ho, hwo⟩ := exists_diag_eq_mul hs ha
  have hwC : w ∈ Cz x := deltaStar_le_Cz hs hw
  obtain ⟨hoC, hπo⟩ := (mem_oddCoreOf_Cz_iff x).mp ((oddCoreOf_eq_Cz hs.member) ▸ ho)
  have hay : a * (y * a * y⁻¹) ∈ Cz x :=
    (Cz x).mul_mem haC ((Cz x).mul_mem ((Cz x).mul_mem hyC haC) ((Cz x).inv_mem hyC))
  have e1 : diag (piz x ⟨y, hyC⟩) (piz x ⟨a, haC⟩) = piz x ⟨a * (y * a * y⁻¹), hay⟩ := by
    unfold diag
    have : (⟨a * (y * a * y⁻¹), hay⟩ : ↥(Cz x)) =
        ⟨a, haC⟩ * (⟨y, hyC⟩ * ⟨a, haC⟩ * (⟨y, hyC⟩ : ↥(Cz x))⁻¹) := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv]
  have e2 : piz x ⟨a * (y * a * y⁻¹), hay⟩ = piz x ⟨w, hwC⟩ := by
    have : (⟨a * (y * a * y⁻¹), hay⟩ : ↥(Cz x)) = ⟨w, hwC⟩ * ⟨o, hoC⟩ := Subtype.ext hwo
    rw [this, map_mul, hπo, mul_one]
  rw [e1, e2]
  exact piz_mem_imgz hwC hw

theorem sq_eq_of_diag_involution (hs : Swap X x y) (hex : ExAt x) {c : F} (hcX : c ∈ X)
    (hd2 : diag y c * diag y c = 1) (hd1 : diag y c ≠ 1) : c * c = x := by
  have hx2 : x * x = 1 := hs.member.mul_self
  have hmul : diag y (c * c) = diag y c * diag y c := diag_mul_of_mem hs hex hcX hcX
  rcases diag_eq_one hs hex (X.mul_mem hcX hcX) (hmul.trans hd2) with h | h
  · exfalso
    apply hd1
    rcases hs.member.isUniqueInvolution.unique c hcX h with h2 | h2
    · rw [h2]
      simp [diag]
    · rw [h2]
      unfold diag
      have : y * x * y⁻¹ = x := by rw [hs.comm]; group
      rw [this, hx2]
  · exact h

theorem exists_conj_diag_involution (hs : Swap X x y) {d : F} (hdK : d ∈ deltaStar X y)
    (hd2 : d * d = 1) (hd1 : d ≠ 1) {q : F} (hqX : q ∈ X) (hq2 : q * q = x)
    (hqc : q * (y * q * y⁻¹) = (y * q * y⁻¹) * q) :
    ∃ c ∈ deltaStar X y, ∃ k ∈ deltaStar X y,
      q * (y * q * y⁻¹) = c * (k * d * k⁻¹) * c⁻¹ := by
  classical
  have hX := hs.member
  have hyC := y_mem_Cz hs
  have hs' := swap_imgz hs
  have hex := exAt_zb x
  have hXC : X ≤ Cz x := hX.le_centralizer
  have hdC : d ∈ Cz x := deltaStar_le_Cz hs hdK
  have hqC : q ∈ Cz x := hXC hqX
  obtain ⟨hdC', hdbΔ⟩ := piz_deltaStar_mem hs hdK
  obtain ⟨cb, hcbX, hdb⟩ := (mem_diagGroupOf_iff hs' hex).mp hdbΔ
  have hdb2 : diag (piz x ⟨y, hyC⟩) cb * diag (piz x ⟨y, hyC⟩) cb = 1 := by
    rw [← hdb, ← map_mul]
    have : (⟨d, hdC⟩ * ⟨d, hdC⟩ : ↥(Cz x)) = 1 := Subtype.ext hd2
    rw [this, map_one]
  have hdb1 : diag (piz x ⟨y, hyC⟩) cb ≠ 1 := by
    rw [← hdb]
    exact piz_ne_one_of_orderOf_eq_two x hdC
      (orderOf_eq_prime (by rw [pow_two]; exact hd2) hd1)
  have hcb2 : cb * cb = zb x := sq_eq_of_diag_involution hs' hex hcbX hdb2 hdb1
  have hqbX : piz x ⟨q, hqC⟩ ∈ imgz x X := piz_mem_imgz hqC hqX
  have hqb2 : piz x ⟨q, hqC⟩ * piz x ⟨q, hqC⟩ = zb x := by
    rw [← map_mul]
    have : (⟨q, hqC⟩ * ⟨q, hqC⟩ : ↥(Cz x)) = ⟨x, self_mem_Cz x⟩ := Subtype.ext hq2
    rw [this]
    rfl
  obtain ⟨ab, habX, habconj⟩ := Mem3.exists_conj_in_member hs'.member hcbX hqbX hcb2 hqb2
  obtain ⟨a, haC, haX, rfl⟩ := (mem_imgz_iff x).mp habX
  have hdiag : diag (piz x ⟨y, hyC⟩) (piz x ⟨q, hqC⟩) =
      diag (piz x ⟨y, hyC⟩) (piz x ⟨a, haC⟩) * diag (piz x ⟨y, hyC⟩) cb *
        (diag (piz x ⟨y, hyC⟩) (piz x ⟨a, haC⟩))⁻¹ := by
    rw [← habconj]
    exact diag_conj_of_mem hs' hex habX hcbX
  obtain ⟨k, hkC, hkK, hkπ⟩ := (mem_imgz_iff x).mp (diag_piz_mem_imgz hs haX)
  have hyy : y * y = 1 := hs.sq
  have he2 : (q * (y * q * y⁻¹)) * (q * (y * q * y⁻¹)) = 1 :=
    diag_mul_self hX.mul_self hs.comm hq2 hqc
  have he'2 : (k * d * k⁻¹) * (k * d * k⁻¹) = 1 := by
    calc (k * d * k⁻¹) * (k * d * k⁻¹) = k * (d * d) * k⁻¹ := by group
      _ = 1 := by rw [hd2]; group
  have heK : q * (y * q * y⁻¹) ∈ deltaStar X y := diag_mem_deltaStar hs hqX hqc
  have he'K : k * d * k⁻¹ ∈ deltaStar X y :=
    (deltaStar X y).mul_mem ((deltaStar X y).mul_mem hkK hdK) ((deltaStar X y).inv_mem hkK)
  have heC : q * (y * q * y⁻¹) ∈ Cz x := deltaStar_le_Cz hs heK
  have he'C : k * d * k⁻¹ ∈ Cz x := deltaStar_le_Cz hs he'K
  have hπe : piz x ⟨q * (y * q * y⁻¹), heC⟩ = diag (piz x ⟨y, hyC⟩) (piz x ⟨q, hqC⟩) := by
    unfold diag
    have : (⟨q * (y * q * y⁻¹), heC⟩ : ↥(Cz x)) =
        ⟨q, hqC⟩ * (⟨y, hyC⟩ * ⟨q, hqC⟩ * (⟨y, hyC⟩ : ↥(Cz x))⁻¹) := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv]
  have hπe' : piz x ⟨k * d * k⁻¹, he'C⟩ = diag (piz x ⟨y, hyC⟩) (piz x ⟨q, hqC⟩) := by
    rw [hdiag, ← hkπ, ← hdb]
    have : (⟨k * d * k⁻¹, he'C⟩ : ↥(Cz x)) = ⟨k, hkC⟩ * ⟨d, hdC⟩ * (⟨k, hkC⟩ : ↥(Cz x))⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  have hprod : q * (y * q * y⁻¹) * (k * d * k⁻¹) ∈ oddCoreOf (Cz x) := by
    have hpC : q * (y * q * y⁻¹) * (k * d * k⁻¹) ∈ Cz x := (Cz x).mul_mem heC he'C
    refine (mem_oddCoreOf_Cz_iff x).mpr ⟨hpC, ?_⟩
    have : (⟨q * (y * q * y⁻¹) * (k * d * k⁻¹), hpC⟩ : ↥(Cz x)) =
        ⟨q * (y * q * y⁻¹), heC⟩ * ⟨k * d * k⁻¹, he'C⟩ := rfl
    rw [this, map_mul, hπe, ← hπe', ← map_mul]
    have : (⟨k * d * k⁻¹, he'C⟩ * ⟨k * d * k⁻¹, he'C⟩ : ↥(Cz x)) = 1 := Subtype.ext he'2
    rw [this, map_one]
  have hodd : Odd (orderOf (q * (y * q * y⁻¹) * (k * d * k⁻¹))) :=
    (oddCoreOf_odd_natCard (Cz x)).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hprod)
  obtain ⟨n, hn⟩ := exists_pow_conj_of_involutions he2 he'2 hodd
  exact ⟨(q * (y * q * y⁻¹) * (k * d * k⁻¹)) ^ n,
    (deltaStar X y).pow_mem ((deltaStar X y).mul_mem heK he'K) n, k, hkK, hn⟩

end XSide

end CFSG.ClassicalInvolution.Q3.Q3T6Y

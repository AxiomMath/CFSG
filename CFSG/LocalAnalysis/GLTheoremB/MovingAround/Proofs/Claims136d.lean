module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims136c

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims136d

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open scoped commutatorElement

section General

variable {Q : Type*} [Group Q]

theorem isPGroup_zpowers_of_pow {w : Q} {n : ℕ} (hw : w ^ (3 ^ n) = 1) :
    IsPGroup 3 ↥(Subgroup.zpowers w) := by
  rintro ⟨y, hy⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨n, Subtype.ext ?_⟩
  show (w ^ i) ^ (3 ^ n) = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]

theorem zpowers_le_centralizer {x y : Q} (hxy : x * y = y * x) :
    Subgroup.zpowers x ≤ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup Q) : Set Q) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact ((Commute.zpow_zpow (show Commute x y from hxy) i j).eq).symm

theorem isPGroup_sup3 {x y z : Q} (hx : IsPGroup 3 ↥(Subgroup.zpowers x))
    (hy : IsPGroup 3 ↥(Subgroup.zpowers y)) (hz : IsPGroup 3 ↥(Subgroup.zpowers z))
    (hxy : x * y = y * x) (hxz : x * z = z * x) (hyz : y * z = z * y) :
    IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers z) := by
  have h1 : IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    IsPGroup.to_sup_of_normal_right' hx hy
      ((zpowers_le_centralizer hxy).trans (Subgroup.centralizer_le_normalizer _))
  refine IsPGroup.to_sup_of_normal_right' h1 hz ?_
  exact (sup_le (zpowers_le_centralizer hxz) (zpowers_le_centralizer hyz)).trans
    (Subgroup.centralizer_le_normalizer _)

theorem mem_center_of_conj_eq_one {z : Q} (h : MulAut.conj z = 1) : z ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg (fun φ : MulAut Q => φ g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc g * z = (z * g * z⁻¹) * z := by rw [h1]
    _ = z * g := by group

theorem exists_pGroup_lift {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X] (f : X →* Q)
    (hf : Function.Surjective f) (T : Subgroup Q) (hT : IsPGroup p ↥T) :
    ∃ P : Subgroup X, IsPGroup p ↥P ∧ P.map f = T := by
  classical
  set U : Subgroup X := T.comap f with hU
  set fU : ↥U →* ↥T := (f.comp U.subtype).codRestrict T (fun u => u.2) with hfU
  have hfUs : Function.Surjective fU := by
    rintro ⟨t, ht⟩
    obtain ⟨m, hm⟩ := hf t
    exact ⟨⟨m, show f m ∈ T by rw [hm]; exact ht⟩, Subtype.ext hm⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow p ↥U) := inferInstance
  have h1 := (S₀.mapSurjective hfUs).is_maximal' (hT.to_subgroup ⊤) le_top
  rw [Sylow.coe_mapSurjective] at h1
  refine ⟨(S₀ : Subgroup ↥U).map U.subtype, S₀.isPGroup'.map _, ?_⟩
  have h2 : ((S₀ : Subgroup ↥U).map fU).map T.subtype = T := by
    rw [← h1, Subgroup.map_top, Subgroup.range_subtype]
  rw [← h2, Subgroup.map_map, Subgroup.map_map]
  rfl

end General

section Central

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)

theorem comm_of_le_normalizer {L P S : Subgroup G} (eL : barOf 3 L ≃* alternatingGroup (Fin 7))
    (hPel : IsElemAbelian 3 P) (hPL : P ≤ L) (hP9 : 9 ≤ Nat.card ↥P) (hS : IsPGroup 3 ↥S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hPS : P ≤ S) {s y : G} (hs : s ∈ S) (hy : y ∈ P) :
    s * y = y * s := by
  have hsN := hSN hs
  by_cases hσ : barAut 3 L ⟨s, hsN⟩ = 1
  · have hyL := hPL hy
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL
    have hcL : s * y * s⁻¹ * y⁻¹ ∈ L := by
      have h1 : s * y * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hsN y).1 hyL
      exact L.mul_mem h1 (L.inv_mem hyL)
    have hcS : s * y * s⁻¹ * y⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem (S.mul_mem hs (hPS hy)) (S.inv_mem hs)) (S.inv_mem (hPS hy))
    have hcN : s * y * s⁻¹ * y⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hcL
    have h1 : barAut 3 L ⟨s * y * s⁻¹ * y⁻¹, hcN⟩ = 1 := by
      have e : (⟨s * y * s⁻¹ * y⁻¹, hcN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          ⟨s, hsN⟩ * ⟨y, hyN⟩ * (⟨s, hsN⟩)⁻¹ * (⟨y, hyN⟩)⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hσ]
      group
    have h2 := Claims136.eq_one_of_barAut_eq_one eL hS hcL hcS hcN h1
    calc s * y = (s * y * s⁻¹ * y⁻¹) * (y * s) := by group
      _ = y * s := by rw [h2, one_mul]
  · have hP9' : 9 ≤ Nat.card ↥(P ⊓ L) := by rwa [inf_eq_left.2 hPL]
    obtain ⟨-, -, -, -, -, -, -, -, hcomm⟩ :=
      Claims136.exists_bd_complement eL hPel hS hPS hs hsN hσ hP9'
    exact (hcomm y ⟨hy, hPL hy⟩).symm

end Central

section Lift

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)

theorem lift_comm (h111 : Prop111Statement) {m : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) (eL : barOf 3 L ≃* alternatingGroup (Fin 7))
    (hML : M ≤ Subgroup.normalizer (L : Set G)) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    {A₀ : Subgroup G} (hA₀B : A₀ ≤ B) (hA₀C : A₀ ≤ Cg d) (hA₀c : Nat.card ↥A₀ = 9)
    {b b₁ : G} (hbA : b ∈ A₀) (hbL : b ∈ L) (hb1 : b ≠ 1) (hb₁B : b₁ ∈ B) (hb₁L : b₁ ∈ L)
    (hb₁C : b₁ ∈ Cg d) (hb₁b : b₁ ∉ Subgroup.zpowers b)
    {U : Subgroup (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d))} (hUp : IsPGroup 3 ↥U)
    (hUA : ∀ a (ha : a ∈ A₀), ∀ u ∈ U, QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨a, hA₀C ha⟩ * u =
      u * QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨a, hA₀C ha⟩)
    (hUν : ∀ u ∈ U, QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨b₁, hb₁C⟩ * u *
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨b₁, hb₁C⟩)⁻¹ ∈ U)
    {u : ↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d)} (hu : u ∈ U) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨b₁, hb₁C⟩ * u =
      u * QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨b₁, hb₁C⟩ := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set mk := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) with hmk
  have hBel : IsElemAbelian 3 B := h.uniq.elemAbelian
  have hBM : B ≤ M := h.uniq.le
  have hA₀el : IsElemAbelian 3 A₀ := CFSG.Open.IsElemAbelian.mono hBel hA₀B
  have hA₀p : IsPGroup 3 ↥A₀ := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hA₀el.2 g.1 g.2)⟩
  have hA₀rk : 2 ≤ CFSG.Open.pRank 3 A₀ :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hA₀el (by rw [hA₀c]; norm_num)
  have hNA₀ : Subgroup.normalizer (A₀ : Set G) ≤ M := by
    have h1 : Subgroup.normalizer (A₀ : Set G) ≤ GLBCore 3 2 B := le_sSup ⟨A₀, hA₀B, hA₀rk, rfl⟩
    exact h1.trans h.uniq.clause_d
  have hCA₀ : Subgroup.centralizer (A₀ : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer _).trans hNA₀
  have hXqM : GLAPPrimeCoreOf 3 (Cg d) ≤ M := h111 h.toSec11 hdA hd1
  set Ut' : Subgroup G := (U.comap mk).map (Cg d).subtype with hUt'
  have hmemUt' : ∀ z, z ∈ Ut' ↔ ∃ hz : z ∈ Cg d, mk ⟨z, hz⟩ ∈ U := by
    intro z
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨hz, hz'⟩
      exact ⟨⟨z, hz⟩, hz', rfl⟩
  have hUt'X : Ut' ≤ Cg d := Subgroup.map_subtype_le _
  have hAN : A₀ ≤ Subgroup.normalizer (Cg d : Set G) := fun a ha => Subgroup.le_normalizer (hA₀C ha)
  have hUt'M : Ut' ≤ M := by
    intro z hz
    obtain ⟨hzX, hzU⟩ := (hmemUt' z).1 hz
    obtain ⟨v, hvO, hv⟩ := Claims136b.exists_lift_centralizer hA₀p hAN ⟨z, hzX⟩ (fun a ha => by
      rw [Claims136.barAut_eq_conj (hA₀C ha) (hAN ha), MulAut.conj_apply]
      show mk ⟨a, hA₀C ha⟩ * mk ⟨z, hzX⟩ * (mk ⟨a, hA₀C ha⟩)⁻¹ = mk ⟨z, hzX⟩
      rw [hUA a ha _ hzU, mul_inv_cancel_right])
    have hzvC : z * v ∈ Subgroup.centralizer (A₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have := hv a ha
      calc a * (z * v) = (a * (z * v) * a⁻¹) * a := by group
        _ = (z * v) * a := by rw [this]
    have e : z = (z * v) * v⁻¹ := by group
    rw [e]
    exact M.mul_mem (hCA₀ hzvC) (M.inv_mem (hXqM hvO))
  have hnorm : ∀ g (hg : g ∈ Cg d), g ^ 3 = 1 → (∀ k ∈ U, mk ⟨g, hg⟩ * k * (mk ⟨g, hg⟩)⁻¹ ∈ U) →
      g ∈ Subgroup.normalizer ((Ut' : Subgroup G) : Set G) := by
    intro g hg hg3 hgU
    set gb := mk ⟨g, hg⟩ with hgb
    have hgb3 : gb ^ 3 = 1 := by
      rw [hgb, ← map_pow]
      have : (⟨g, hg⟩ : ↥(Cg d)) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
      rw [this, map_one]
    have hgUi : ∀ k ∈ U, gb⁻¹ * k * gb ∈ U := by
      intro k hk
      have h3 : gb * gb * gb = 1 := by rw [mul_assoc, ← pow_three]; exact hgb3
      have e1 : gb * gb = gb⁻¹ := eq_inv_of_mul_eq_one_left h3
      have e2 : gb * (gb * k * gb⁻¹) * gb⁻¹ = gb⁻¹ * k * gb := by
        calc gb * (gb * k * gb⁻¹) * gb⁻¹ = (gb * gb) * k * (gb * gb)⁻¹ := by group
          _ = gb⁻¹ * k * gb := by rw [e1, inv_inv]
      rw [← e2]
      exact hgU _ (hgU k hk)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨hzX, hzU⟩ := (hmemUt' z).1 hz
      have hgz : g * z * g⁻¹ ∈ Cg d := (Cg d).mul_mem ((Cg d).mul_mem hg hzX) ((Cg d).inv_mem hg)
      refine (hmemUt' _).2 ⟨hgz, ?_⟩
      have e : mk ⟨g * z * g⁻¹, hgz⟩ = gb * mk ⟨z, hzX⟩ * gb⁻¹ := by
        rw [hgb, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact hgU _ hzU
    · intro hz
      obtain ⟨hgzX, hgzU⟩ := (hmemUt' _).1 hz
      have hzX : z ∈ Cg d := by
        have := (Cg d).mul_mem ((Cg d).mul_mem ((Cg d).inv_mem hg) hgzX) hg
        simpa [mul_assoc] using this
      refine (hmemUt' z).2 ⟨hzX, ?_⟩
      have e : mk ⟨z, hzX⟩ = gb⁻¹ * mk ⟨g * z * g⁻¹, hgzX⟩ * gb := by
        rw [hgb, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        show z = g⁻¹ * (g * z * g⁻¹) * g
        group
      rw [e]
      exact hgUi _ hgzU
  have hbB : b ∈ B := hA₀B hbA
  have hbC : b ∈ Cg d := hA₀C hbA
  have hbN : b ∈ Subgroup.normalizer ((Ut' : Subgroup G) : Set G) :=
    hnorm b hbC (hBel.2 b hbB) (fun k hk => by rw [hUA b hbA k hk, mul_inv_cancel_right]; exact hk)
  have hb₁N : b₁ ∈ Subgroup.normalizer ((Ut' : Subgroup G) : Set G) :=
    hnorm b₁ hb₁C (hBel.2 b₁ hb₁B) hUν
  set P : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers b₁ with hP
  have hPB : P ≤ B := sup_le ((Subgroup.zpowers_le).2 hbB) ((Subgroup.zpowers_le).2 hb₁B)
  have hPL : P ≤ L := sup_le ((Subgroup.zpowers_le).2 hbL) ((Subgroup.zpowers_le).2 hb₁L)
  have hPN : P ≤ Subgroup.normalizer ((Ut' : Subgroup G) : Set G) :=
    sup_le ((Subgroup.zpowers_le).2 hbN) ((Subgroup.zpowers_le).2 hb₁N)
  have hPc : Nat.card ↥P = 9 := Claims136c.card_plane hBel hbB hb₁B hb1 hb₁b
  have hPel : IsElemAbelian 3 P := CFSG.Open.IsElemAbelian.mono hBel hPB
  have hPp : IsPGroup 3 ↥P := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hPel.2 g.1 g.2)⟩
  set W : Subgroup G := Ut' ⊔ P with hW
  have hWM : W ≤ M := sup_le hUt'M (hPB.trans hBM)
  have hWN : W ≤ Subgroup.normalizer ((Ut' : Subgroup G) : Set G) := sup_le Subgroup.le_normalizer hPN
  obtain ⟨S0, hS0p, hS0map⟩ := exists_pGroup_lift mk (QuotientGroup.mk'_surjective _) U hUp
  set R : Subgroup G := S0.map (Cg d).subtype with hR
  have hRU : R ≤ Ut' := by
    rintro _ ⟨s, hs, rfl⟩
    refine (hmemUt' _).2 ⟨s.2, ?_⟩
    rw [← hS0map]
    exact ⟨s, hs, rfl⟩
  have hRp : IsPGroup 3 ↥R := hS0p.map _
  obtain ⟨w, hwW, S, hSp, hSW, hPS, hRS⟩ := exists_conj_le_pGroup' (K := W) le_sup_right hPp
    (hRU.trans le_sup_left) hRp
  obtain ⟨x₁, hx₁⟩ := QuotientGroup.mk_surjective u
  have hx₁' : mk x₁ = u := hx₁
  have hx₁U : (x₁ : G) ∈ Ut' := (hmemUt' _).2 ⟨x₁.2, by
    show mk x₁ ∈ U
    rw [hx₁']
    exact hu⟩
  have hwX : w ∈ Cg d := by
    have hWX : W ≤ Cg d := sup_le hUt'X
      (sup_le ((Subgroup.zpowers_le).2 hbC) ((Subgroup.zpowers_le).2 hb₁C))
    exact hWX hwW
  have hwN := hWN hwW
  have hwx₁ : w * x₁ * w⁻¹ ∈ Ut' := (Subgroup.mem_normalizer_iff.1 hwN _).1 hx₁U
  obtain ⟨hwx₁X, hwx₁U⟩ := (hmemUt' _).1 hwx₁
  rw [← hS0map] at hwx₁U
  obtain ⟨s, hs, hsx⟩ := hwx₁U
  have hx'X : w⁻¹ * (s : G) * w ∈ Cg d :=
    (Cg d).mul_mem ((Cg d).mul_mem ((Cg d).inv_mem hwX) s.2) hwX
  have hx'S : w⁻¹ * (s : G) * w ∈ S := hRS (mem_gLBConj.2 (by
    have : w * (w⁻¹ * (s : G) * w) * w⁻¹ = s := by group
    rw [this]
    exact ⟨s, hs, rfl⟩))
  have hx'img : mk ⟨w⁻¹ * (s : G) * w, hx'X⟩ = u := by
    have e1 : (⟨w⁻¹ * (s : G) * w, hx'X⟩ : ↥(Cg d)) = (⟨w, hwX⟩ : ↥(Cg d))⁻¹ * s * ⟨w, hwX⟩ :=
      Subtype.ext rfl
    have e2 : mk s = mk ⟨w, hwX⟩ * mk x₁ * (mk ⟨w, hwX⟩)⁻¹ := by
      rw [hsx, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1, map_mul, map_mul, map_inv, e2, hx₁']
    group
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := hSW.trans (hWM.trans hML)
  have hcomm := comm_of_le_normalizer eL hPel hPL (by rw [hPc]) hSp hSN hPS hx'S
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers b₁))
  rw [← hx'img, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hcomm.symm

end Lift

section Normal

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)

theorem le_normalizer_of_card_bStar (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (h135 : Lemma135_iiStatement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    (hN : D ≤ Subgroup.normalizer (L : Set G)) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb1 : barAut 3 L ⟨b, hbN⟩ ≠ 1)
    (hBs : Nat.card ↥(Lemma136c.bStarOf B L D b) ≤ 9) :
    M ≤ Subgroup.normalizer (L : Set G) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLsn : IsSubnormal L M := hLc.2.1
  have hDA : D ≤ A := h.hD.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDM : D ≤ M := hDA.trans hAM
  have hBM : B ≤ M := h.uniq.le
  have hBel : IsElemAbelian 3 B := h.uniq.elemAbelian
  have hP3 : IsPGroup 3 ↥(A ⊔ B) := h.hAB
  obtain ⟨-, eM, -⟩ := Lemma136.l136_gamma hP95 h111 h121 hcomp h
  have hall : ∀ g : ↥M ⧸ GLAPPrimeCore 3 ↥M,
      g ∈ Subgroup.normalizer ((barX 3 M L : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    by_contra hcon
    have hDL : barX 3 M D ≤ Subgroup.normalizer ((barX 3 M L : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
      Lemma136.l136_bar_normalizes fun x hx q hq => (Subgroup.mem_normalizer_iff.1 (hN hx) q).1 hq
    have hne : ¬ barX 3 M L ≤ ⊥ := by
      intro hle
      have h1 : Nat.card ↥(barX 3 M L) = 1 := by
        rw [le_bot_iff.1 hle]
        exact Subgroup.card_bot
      rw [Claims136.card_of_alt7 eM] at h1
      exact absurd h1 (by norm_num)
    have h2 := h135 h hDL ⟨hne, hcon⟩
    set X : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M) := barX 3 M B ⊓ Subgroup.centralizer
      ((barX 3 M D ⊔ barX 3 M L : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) with hX
    have hBbel : IsElemAbelian 3 (barX 3 M B) :=
      CFSG.SectionRank.isElemAbelian_map (CFSG.Open.IsElemAbelian.subgroupOf hBel _) _
    have hXel : IsElemAbelian 3 X := CFSG.Open.IsElemAbelian.mono hBbel inf_le_left
    have hX9 : 9 ≤ Nat.card ↥X := by
      rw [Claims136.card_eq_pow_pRank3 hXel]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ CFSG.Open.pRank 3 X := Nat.pow_le_pow_right (by norm_num) h2
    set Y : Subgroup G := centBar 3 B L ⊓ Subgroup.centralizer (D : Set G) with hY
    have hXY : X ≤ barX 3 M Y := by
      intro y hy
      obtain ⟨hyB, hyC⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨c', hc'B, rfl⟩ := (mem_barX_iff 3 _).1 hyB
      have hc'C : ∀ z ∈ barX 3 M D ⊔ barX 3 M L,
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) c' * z = z * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) c' :=
        fun z hz => ((Subgroup.mem_centralizer_iff.1 hyC) z hz).symm
      have hc'D : (c' : G) ∈ Subgroup.centralizer (D : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        have hgbar : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨g, hDM hg⟩ : ↥M) ∈ barX 3 M D :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg)
        exact (Lemma136b.commute_of_bar c'.2 (hDM hg) hP3 (Subgroup.mem_sup_right hc'B)
          (Subgroup.mem_sup_left (hDA hg)) (hc'C _ (Subgroup.mem_sup_left hgbar))).symm
      have hc'cent : (c' : G) ∈ centBar 3 ⊤ L :=
        Lemma136.l136_centBar_of_centralizes hp hLsn c'.2 (hBN hc'B) fun q hq =>
          hc'C q (Subgroup.mem_sup_right hq)
      exact (mem_barX_iff 3 _).2 ⟨c', ⟨⟨hc'cent.1, hc'B⟩, hc'D⟩, rfl⟩
    have hYB : Y ≤ B := inf_le_left.trans inf_le_right
    have hYp : IsPGroup 3 ↥Y := hP3.to_le (hYB.trans le_sup_right)
    have hYc : Nat.card ↥(barX 3 M Y) = Nat.card ↥Y := card_barX_of_isPGroup hp hYp (hYB.trans hBM)
    have hY9 : 9 ≤ Nat.card ↥Y := hYc ▸ hX9.trans (Subgroup.card_le_of_le hXY)
    have hYBs : Y ≤ Lemma136c.bStarOf B L D b := le_sup_right
    have hYeq : Y = Lemma136c.bStarOf B L D b := Subgroup.eq_of_le_of_card_ge hYBs (by omega)
    have hbY : b ∈ Y := by
      rw [hYeq]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
    exact hb1 ((Lemma129.mem_centBar_top_iff hbN).1 ⟨hbY.1.1, Subgroup.mem_top b⟩)
  intro g hg
  exact Lemma136.l136_mem_normalizer_of_bar hLc ⟨g, hg⟩ (hall _)

end Normal

section Weak

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)

theorem weak_false (hI191 : Lemma129.Input19_1_two) {m : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) {d : G} (hd1 : d ≠ 1) {Bs B1 S0 : Subgroup G}
    (hBsB : Bs ≤ B) (hEk : IsEkIn 3 2 (Cg d) Bs) {b : G} (hbBs : b ∈ Bs) (hb1 : b ≠ 1)
    (hB1B : B1 ≤ B) (hB1C : B1 ≤ Cg d) (hB1N : B1 ≤ Subgroup.normalizer (S0 : Set G))
    (hS0 : IsPGroup 2 ↥S0) (hS1Δ : ⁅B1, S0⁆ ≤ localDeltaTwoIn (Cg d) Bs)
    {K : Subgroup G} (hK : GLAPComponent 3 (Cg d) K)
    (hnot : ¬ ⁅K, ⁅B1, S0⁆⁆ ≤ GLAPPrimeCoreOf 3 (Cg d))
    (hBsK : Bs ≤ Subgroup.normalizer (K : Set G)) (hcent : centBar 3 Bs K = ⊥)
    (hweak : ∀ B' : Subgroup (MulAut (barOf 3 K)), IsElemAbelian 3 B' → 3 ^ 2 ≤ Nat.card ↥B' →
      IsWeaklyLocallyOTwoBalanced 3 2 B')
    (hB1K : B1 ≤ Subgroup.normalizer (K : Set G)) : False := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup G := h.standing.simple
  have hX : Cg d ≠ ⊤ := Lemma136c.l136c_centralizer_ne_top h.standing.nonabelian hd1
  obtain ⟨⟨h1, -⟩, h3⟩ := hI191 G h.standing.kProper 3 hp (by norm_num) (Cg d) hX 2 Bs
    (by norm_num) hEk
  set Δ : Subgroup G := Lemma129.deltaTwo (Cg d) Bs with hΔ
  have hΔeq : Δ = localDeltaTwoIn (Cg d) Bs := rfl
  have hΔX : Δ ≤ Cg d := Claims136.localDeltaTwoIn_le hbBs hb1
  have hS1Δ' : ⁅B1, S0⁆ ≤ Δ := hS1Δ
  have hS1X : ⁅B1, S0⁆ ≤ Cg d := hS1Δ'.trans hΔX
  have hnc : ¬ barX 3 (Cg d) Δ ≤
      Subgroup.centralizer (barX 3 (Cg d) K : Set (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d))) := by
    intro hc
    exact hnot (Claims136.commutator_le_of_barX_le_centralizer hK.1 hS1X
      ((Lemma129.barX_mono129 hS1Δ').trans hc))
  obtain ⟨-, -, -, hW⟩ := h3 K hK hnc
  have hΔK : Δ ≤ Subgroup.normalizer (K : Set G) := Lemma129.le_normalizer_of_barX hp hK hΔX (h1 K hK)
  set B₂ : Subgroup G := Bs ⊔ B1 with hB₂
  have hB₂B : B₂ ≤ B := sup_le hBsB hB1B
  have hB₂C : B₂ ≤ Cg d := sup_le hEk.1 hB1C
  have hB₂K : B₂ ≤ Subgroup.normalizer (K : Set G) := sup_le hBsK hB1K
  have hB₂el : IsElemAbelian 3 B₂ := CFSG.Open.IsElemAbelian.mono h.uniq.elemAbelian hB₂B
  set Ab := autBar 3 B₂ K with hAb
  have hAbel : IsElemAbelian 3 Ab := Lemma129.isElemAbelian_autBar hB₂K hB₂el
  have hD'E : IsEkIn 3 2 ⊤ (autBar 3 Bs K) := Lemma136c.l136c_isEkIn_autBar hEk hBsK hcent
  have hD'Ab : autBar 3 Bs K ≤ Ab := Lemma129.autBar_mono 3 le_sup_left
  have hD' : IsEkIn 3 2 Ab (autBar 3 Bs K) := ⟨hD'Ab, hD'E.2.1, hD'E.2.2⟩
  have hAb9 : 3 ^ 2 ≤ Nat.card ↥Ab := hD'E.2.2 ▸ Subgroup.card_le_of_le hD'Ab
  set H := innerAut (barOf 3 K) ⊔ autBar 3 Δ K with hH
  have hB₂Δ : B₂ ≤ Subgroup.normalizer (Δ : Set G) :=
    Lemma129.le_normalizer_deltaTwo ⟨3, hB₂el⟩ le_sup_left hB₂C
  have hAbH : Ab ≤ Subgroup.normalizer (H : Set (MulAut (barOf 3 K))) := by
    refine Lemma129.le_normalizer_of_conj_mem fun β hβ x hx => ?_
    obtain ⟨a', ha'K, ha'A, hba⟩ := Lemma129.mem_autBar_iff.1 hβ
    have hW' : ∀ y ∈ autBar 3 Δ K, β * y * β⁻¹ ∈ autBar 3 Δ K := by
      intro y hy
      obtain ⟨g, hgK, hgΔ, hyg⟩ := Lemma129.mem_autBar_iff.1 hy
      have hg' : a' * g * a'⁻¹ ∈ Δ := (Subgroup.mem_normalizer_iff.1 (hB₂Δ ha'A) g).1 hgΔ
      have hg'K : a' * g * a'⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ ha'K hgK) (Subgroup.inv_mem _ ha'K)
      refine Lemma129.mem_autBar_iff.2 ⟨a' * g * a'⁻¹, hg'K, hg', ?_⟩
      have : (⟨a' * g * a'⁻¹, hg'K⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⟨a', ha'K⟩ * ⟨g, hgK⟩ * ⟨a', ha'K⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hba, hyg]
    have key : H.map (MulAut.conj β).toMonoidHom ≤ H := by
      rw [hH, Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact Lemma129.conj_mem_innerAut β hy
      · rintro _ ⟨y, hy, rfl⟩
        exact hW' y hy
    have := key ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using this
  have hc := hweak Ab hAbel hAb9 (autBar 3 Bs K) hD' H le_sup_left hAbH
  have hcomm1 : ∀ s ∈ ⁅B1, S0⁆, ∀ x ∈ B1, ⁅s, x⁆ ∈ centBar 3 ⊤ K := by
    intro s hs x hx
    have hsK := hΔK (hS1Δ' hs)
    have hxK := hB1K hx
    have h1' : barAut 3 K ⟨s, hsK⟩ ∈ autBar 3 Δ K := Lemma129.barAut_mem_autBar (hS1Δ' hs) hsK
    have h2' : barAut 3 K ⟨x, hxK⟩ ∈ Ab := Lemma129.barAut_mem_autBar (Subgroup.mem_sup_right hx) hxK
    have h3' := Subgroup.commutator_mem_commutator (hW h1') h2'
    rw [hc, Subgroup.mem_bot] at h3'
    have hcN : ⁅s, x⁆ ∈ Subgroup.normalizer (K : Set G) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hsK hxK)
        (Subgroup.inv_mem _ hsK)) (Subgroup.inv_mem _ hxK)
    rw [Lemma129.mem_centBar_top_iff hcN]
    have e : (⟨⁅s, x⁆, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨s, hsK⟩ * ⟨x, hxK⟩ * ⟨s, hsK⟩⁻¹ * ⟨x, hxK⟩⁻¹ := Subtype.ext (commutatorElement_def s x)
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [commutatorElement_def] at h3'
    exact h3'
  have hB1p : IsPGroup 3 ↥B1 := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (h.uniq.elemAbelian.2 g.1 (hB1B g.2))⟩
  have hcop : Nat.Coprime (Nat.card ↥B1) (Nat.card ↥S0) := by
    obtain ⟨i, hi⟩ := IsPGroup.iff_card.1 hB1p
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hS0
    rw [hi, hj]
    exact Nat.Coprime.pow i j (by norm_num)
  have hS1eq : ⁅B1, S0⁆ = ⁅⁅B1, S0⁆, B1⁆ := by
    rw [Subgroup.commutator_comm B1 S0]
    exact (CFSG.HardMathSupport.Solomon.Coordinator.coprime_commutator_commutator_eq' hB1N hcop).symm
  have hS1c : ⁅B1, S0⁆ ≤ centBar 3 ⊤ K := hS1eq.le.trans ((Subgroup.commutator_le).2 hcomm1)
  exact hnot (Claims136.commutator_le_of_barX_le_centralizer hK.1 hS1X
    (Lemma129.barX_le_centralizer_of_le_centBar hp hK hS1X hS1c))

end Weak

section Moved

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)

theorem moved_false (h111 : Prop111Statement) {m : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) (eL : barOf 3 L ≃* alternatingGroup (Fin 7))
    (hML : M ≤ Subgroup.normalizer (L : Set G)) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    {Bs : Subgroup G} (hBsB : Bs ≤ B) (hBsC : Bs ≤ Cg d) (hBs9 : Nat.card ↥Bs = 9)
    {b b₁ : G} (hbBs : b ∈ Bs) (hbL : b ∈ L) (hb1 : b ≠ 1) (hb₁B : b₁ ∈ B) (hb₁L : b₁ ∈ L)
    (hb₁C : b₁ ∈ Cg d) (hb₁b : b₁ ∉ Subgroup.zpowers b)
    {K : Subgroup G} (hK : GLAPComponent 3 (Cg d) K) (hBsK : Bs ≤ Subgroup.normalizer (K : Set G))
    (hcent : centBar 3 Bs K = ⊥) (hinn : autBar 3 Bs K ≤ innerAut (barOf 3 K))
    (hb₁K : b₁ ∉ Subgroup.normalizer (K : Set G)) : False := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI : Finite (barOf 3 K) := by unfold barOf; infer_instance
  have hBel : IsElemAbelian 3 B := h.uniq.elemAbelian
  have hBcomm : ∀ y ∈ B, ∀ y' ∈ B, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hBel.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  set mk := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) with hmk
  set e := Claims136c.embBar hK with he
  have hei : Function.Injective e := Claims136c.embBar_injective hK
  set ν := mk ⟨b₁, hb₁C⟩ with hν
  have hν3 : ν ^ 3 = 1 := by
    rw [hν, ← map_pow]
    have : (⟨b₁, hb₁C⟩ : ↥(Cg d)) ^ 3 = 1 := Subtype.ext (by simpa using hBel.2 b₁ hb₁B)
    rw [this, map_one]
  set c : (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d)) →* (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d)) :=
    (MulAut.conj ν⁻¹).toMonoidHom with hc
  have hcapp : ∀ y, c y = ν⁻¹ * y * ν := fun y => by
    show MulAut.conj ν⁻¹ y = ν⁻¹ * y * ν
    rw [MulAut.conj_apply, inv_inv]
  have hc3 : ∀ y, c (c (c y)) = y := by
    intro y
    rw [hcapp, hcapp, hcapp]
    have h1 : ν * ν * ν = 1 := by rw [mul_assoc, ← pow_three]; exact hν3
    calc ν⁻¹ * (ν⁻¹ * (ν⁻¹ * y * ν) * ν) * ν = (ν * ν * ν)⁻¹ * y * (ν * ν * ν) := by group
      _ = y := by rw [h1, inv_one, one_mul, mul_one]
  have hνc : ∀ y, ν * c y * ν⁻¹ = y := fun y => by rw [hcapp]; group
  have hcν : ∀ y, c (ν * y * ν⁻¹) = y := fun y => by rw [hcapp]; group
  have hνcc : ∀ y, ν * y * ν⁻¹ = c (c y) := fun y => by
    conv_rhs => rw [← hcν y]
    rw [hc3]
  have hKbar : IsComponentOf (barX 3 (Cg d) K) ⊤ := hK.2.2.1
  have hneK : barX 3 (Cg d) K ≠ GLBConj ν (barX 3 (Cg d) K) := by
    intro heq
    apply hb₁K
    exact Lemma136.l136_mem_normalizer_of_bar hK ⟨b₁, hb₁C⟩
      (mem_normalizer_iff_gLBConj_eq.2 heq.symm)
  have hcomm : ∀ u v, e u * c (e v) = c (e v) * e u := by
    intro u v
    rw [hcapp]
    refine CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.components_commute hKbar
      (isComponentOf_gLBConj hKbar ν) hneK _ (Claims136c.embBar_mem hK u) _ ?_
    rw [mem_gLBConj]
    have e' : ν * (ν⁻¹ * e v * ν) * ν⁻¹ = e v := by group
    rw [e']
    exact Claims136c.embBar_mem hK v
  have h13 : ∀ u v, e u * c (c (e v)) = c (c (e v)) * e u := Claims136c.diag_comm13 e c hc3 hcomm
  have h23 : ∀ u v, c (e u) * c (c (e v)) = c (c (e v)) * c (e u) :=
    Claims136c.diag_comm23 e c hcomm
  have hEy : ∀ a (haC : a ∈ Cg d) (ha : a ∈ Bs) (u : barOf 3 K),
      mk ⟨a, haC⟩ * e u * (mk ⟨a, haC⟩)⁻¹ = e (barAut 3 K ⟨a, hBsK ha⟩ u) :=
    fun a haC ha u => Claims136c.embBar_barAut hK haC (hBsK ha) u
  have hyν : ∀ a (haC : a ∈ Cg d), a ∈ Bs → Commute (mk ⟨a, haC⟩) ν := by
    intro a haC ha
    show mk ⟨a, haC⟩ * ν = ν * mk ⟨a, haC⟩
    rw [hν, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBcomm a (hBsB ha) b₁ hb₁B)
  have hyc : ∀ a (haC : a ∈ Cg d), a ∈ Bs → ∀ y,
      mk ⟨a, haC⟩ * c y * (mk ⟨a, haC⟩)⁻¹ = c (mk ⟨a, haC⟩ * y * (mk ⟨a, haC⟩)⁻¹) := by
    intro a haC ha y
    have h1 := hyν a haC ha
    rw [hcapp, hcapp]
    calc mk ⟨a, haC⟩ * (ν⁻¹ * y * ν) * (mk ⟨a, haC⟩)⁻¹ =
        (mk ⟨a, haC⟩ * ν⁻¹) * y * (ν * (mk ⟨a, haC⟩)⁻¹) := by group
      _ = (ν⁻¹ * mk ⟨a, haC⟩) * y * ((mk ⟨a, haC⟩)⁻¹ * ν) := by
        rw [h1.inv_right.eq, ← h1.inv_left.eq]
      _ = ν⁻¹ * (mk ⟨a, haC⟩ * y * (mk ⟨a, haC⟩)⁻¹) * ν := by group
  have hinn' : ∀ a (ha : a ∈ Bs), ∃ ka : barOf 3 K, MulAut.conj ka = barAut 3 K ⟨a, hBsK ha⟩ := by
    intro a ha
    obtain ⟨ka, hka⟩ := hinn (Lemma129.barAut_mem_autBar ha (hBsK ha))
    exact ⟨ka, hka⟩
  have hfixZ : ∀ a (ha : a ∈ Bs), ∀ z ∈ Subgroup.center (barOf 3 K),
      barAut 3 K ⟨a, hBsK ha⟩ z = z := by
    intro a ha z hz
    obtain ⟨ka, hka⟩ := hinn' a ha
    rw [← hka, MulAut.conj_apply, Subgroup.mem_center_iff.1 hz ka]
    group
  obtain ⟨k, hk⟩ := hinn' b hbBs
  have hknc : k ∉ Subgroup.center (barOf 3 K) := by
    intro hkz
    have h1 : barAut 3 K ⟨b, hBsK hbBs⟩ = 1 := by
      rw [← hk]
      ext z
      rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.1 hkz z]
      group
    have hmem : b ∈ centBar 3 Bs K := ⟨⟨⟨b, hBsK hbBs⟩, h1, rfl⟩, hbBs⟩
    rw [hcent] at hmem
    exact hb1 (Subgroup.mem_bot.1 hmem)
  have hk3 : k ^ 3 ∈ Subgroup.center (barOf 3 K) := by
    apply mem_center_of_conj_eq_one
    rw [map_pow, hk, ← map_pow]
    have : (⟨b, hBsK hbBs⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hBel.2 b (hBsB hbBs))
    rw [this, map_one]
  have hZp : IsPGroup 3 ↥(Subgroup.center (barOf 3 K)) :=
    SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot hp (glaPPrimeCore_quotient_eq_bot hp)
  obtain ⟨n, hn⟩ := hZp ⟨k ^ 3, hk3⟩
  have hkn : k ^ (3 ^ (n + 1)) = 1 := by
    have h1 : (k ^ 3) ^ (3 ^ n) = 1 := congrArg Subtype.val hn
    rw [← pow_mul, ← pow_succ'] at h1
    exact h1
  have hza : ∀ a (ha : a ∈ Bs) (ka : barOf 3 K), MulAut.conj ka = barAut 3 K ⟨a, hBsK ha⟩ →
      ka * k * ka⁻¹ * k⁻¹ ∈ Subgroup.center (barOf 3 K) ∧ (ka * k * ka⁻¹ * k⁻¹) ^ 3 = 1 := by
    intro a ha ka hka
    have hzc : ka * k * ka⁻¹ * k⁻¹ ∈ Subgroup.center (barOf 3 K) := by
      apply mem_center_of_conj_eq_one
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hka, hk, ← map_inv, ← map_inv, ← map_mul,
        ← map_mul, ← map_mul]
      have : (⟨a, hBsK ha⟩ : ↥(Subgroup.normalizer (K : Set G))) * ⟨b, hBsK hbBs⟩ *
          (⟨a, hBsK ha⟩)⁻¹ * (⟨b, hBsK hbBs⟩)⁻¹ = 1 := by
        apply Subtype.ext
        show a * b * a⁻¹ * b⁻¹ = 1
        rw [hBcomm a (hBsB ha) b (hBsB hbBs)]
        group
      rw [this, map_one]
    refine ⟨hzc, ?_⟩
    set z := ka * k * ka⁻¹ * k⁻¹ with hz
    have h1 : ka * k * ka⁻¹ = z * k := by rw [hz]; group
    have h2 : ka * k ^ 3 * ka⁻¹ = k ^ 3 := by
      rw [Subgroup.mem_center_iff.1 hk3 ka]
      group
    have h3 : (z * k) ^ 3 = z ^ 3 * k ^ 3 :=
      (show Commute z k from (Subgroup.mem_center_iff.1 hzc k).symm).mul_pow 3
    have h4 : z ^ 3 * k ^ 3 = 1 * k ^ 3 := by
      rw [← h3, ← h1, conj_pow, h2, one_mul]
    exact mul_right_cancel h4
  set Cbar : Subgroup (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d)) :=
    Subgroup.centralizer ((barX 3 (Cg d) Bs : Subgroup (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d))) :
      Set (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d))) with hCbar
  have hmemB : ∀ a (ha : a ∈ Bs), mk ⟨a, hBsC ha⟩ ∈ barX 3 (Cg d) Bs := fun a ha =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ha)
  have hCbarν : ∀ u ∈ Cbar, ν * u * ν⁻¹ ∈ Cbar := by
    intro u hu
    rw [hCbar, Subgroup.mem_centralizer_iff] at hu ⊢
    rintro _ ⟨⟨a, haC⟩, ha, rfl⟩
    have htu : Commute (mk ⟨a, haC⟩) u := hu _ ⟨⟨a, haC⟩, ha, rfl⟩
    have htν := hyν a haC (Subgroup.mem_subgroupOf.1 ha)
    exact ((htν.mul_right htu).mul_right htν.inv_right).eq
  have key : ∀ (w₀ : barOf 3 K) (j : ℕ), w₀ ^ (3 ^ j) = 1 → ∀ u,
      u ∈ (Subgroup.zpowers (e w₀) ⊔ Subgroup.zpowers (c (e w₀)) ⊔
        Subgroup.zpowers (c (c (e w₀)))) ⊓ Cbar → ν * u = u * ν := by
    intro w₀ j hw₀ u hu
    have hw3 : (e w₀) ^ (3 ^ j) = 1 := by rw [← map_pow, hw₀, map_one]
    have hcw3 : (c (e w₀)) ^ (3 ^ j) = 1 := by rw [← map_pow, hw3, map_one]
    have hccw3 : (c (c (e w₀))) ^ (3 ^ j) = 1 := by rw [← map_pow, hcw3, map_one]
    have hJp : IsPGroup 3 ↥(Subgroup.zpowers (e w₀) ⊔ Subgroup.zpowers (c (e w₀)) ⊔
        Subgroup.zpowers (c (c (e w₀)))) :=
      isPGroup_sup3 (isPGroup_zpowers_of_pow hw3) (isPGroup_zpowers_of_pow hcw3)
        (isPGroup_zpowers_of_pow hccw3) (hcomm w₀ w₀) (h13 w₀ w₀) (h23 w₀ w₀)
    have hJν : ∀ y ∈ Subgroup.zpowers (e w₀) ⊔ Subgroup.zpowers (c (e w₀)) ⊔
        Subgroup.zpowers (c (c (e w₀))), ν * y * ν⁻¹ ∈ Subgroup.zpowers (e w₀) ⊔
          Subgroup.zpowers (c (e w₀)) ⊔ Subgroup.zpowers (c (c (e w₀))) := by
      have hle : Subgroup.zpowers (e w₀) ⊔ Subgroup.zpowers (c (e w₀)) ⊔
          Subgroup.zpowers (c (c (e w₀))) ≤ (Subgroup.zpowers (e w₀) ⊔ Subgroup.zpowers (c (e w₀)) ⊔
            Subgroup.zpowers (c (c (e w₀)))).comap (MulAut.conj ν).toMonoidHom := by
        refine sup_le (sup_le ?_ ?_) ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
          show MulAut.conj ν (e w₀) ∈ _
          rw [MulAut.conj_apply, hνcc]
          exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
        · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
          show MulAut.conj ν (c (e w₀)) ∈ _
          rw [MulAut.conj_apply, hνc]
          exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
          show MulAut.conj ν (c (c (e w₀))) ∈ _
          rw [MulAut.conj_apply, hνc]
          exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      intro y hy
      have h1 := hle hy
      rw [Subgroup.mem_comap] at h1
      exact h1
    exact lift_comm h111 h eL hML hdA hd1 hBsB hBsC hBs9 hbBs hbL hb1 hb₁B hb₁L hb₁C hb₁b
      (hJp.to_le inf_le_left)
      (fun a ha u' hu' => Subgroup.mem_centralizer_iff.1 hu'.2 _ (hmemB a ha))
      (fun u' hu' => ⟨hJν u' hu'.1, hCbarν u' hu'.2⟩) hu
  have hstep1 : ∀ a (ha : a ∈ Bs) (ka : barOf 3 K), MulAut.conj ka = barAut 3 K ⟨a, hBsK ha⟩ →
      c (e (ka * k * ka⁻¹ * k⁻¹)) = e (ka * k * ka⁻¹ * k⁻¹) := by
    intro a ha ka hka
    obtain ⟨hzc, hz3⟩ := hza a ha ka hka
    set z := ka * k * ka⁻¹ * k⁻¹ with hz
    have hmemC : e z ∈ Cbar := by
      rw [hCbar, Subgroup.mem_centralizer_iff]
      rintro _ ⟨⟨a', ha'C⟩, ha', rfl⟩
      have h1 := hEy a' ha'C (Subgroup.mem_subgroupOf.1 ha') z
      rw [hfixZ a' (Subgroup.mem_subgroupOf.1 ha') z hzc] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
    have h1 := key z 1 (by simpa using hz3) (e z)
      ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)), hmemC⟩
    rw [hcapp]
    calc ν⁻¹ * e z * ν = ν⁻¹ * (e z * ν) := by group
      _ = ν⁻¹ * (ν * e z) := by rw [h1]
      _ = e z := by group
  set x := e k * (c (e k))⁻¹ with hx
  have hxC : x ∈ Cbar := by
    rw [hCbar, Subgroup.mem_centralizer_iff]
    rintro _ ⟨⟨a, haC⟩, ha, rfl⟩
    have ha' : a ∈ Bs := Subgroup.mem_subgroupOf.1 ha
    obtain ⟨ka, hka⟩ := hinn' a ha'
    obtain ⟨hzc, -⟩ := hza a ha' ka hka
    have h2a := hstep1 a ha' ka hka
    set z := ka * k * ka⁻¹ * k⁻¹ with hz
    have h1 : mk ⟨a, haC⟩ * e k * (mk ⟨a, haC⟩)⁻¹ = e z * e k := by
      rw [hEy a haC ha' k, ← hka, MulAut.conj_apply, ← map_mul]
      congr 1
      rw [hz]
      group
    have h2 : mk ⟨a, haC⟩ * c (e k) * (mk ⟨a, haC⟩)⁻¹ = e z * c (e k) := by
      rw [hyc a haC ha' (e k), h1, map_mul, h2a]
    have hzk : Commute (e z) (e k) := by
      show e z * e k = e k * e z
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hzc k]
    have hzck : Commute (e z) (c (e k)) := hcomm z k
    have h3 : mk ⟨a, haC⟩ * x * (mk ⟨a, haC⟩)⁻¹ = x := by
      calc mk ⟨a, haC⟩ * x * (mk ⟨a, haC⟩)⁻¹ = (mk ⟨a, haC⟩ * e k * (mk ⟨a, haC⟩)⁻¹) *
          (mk ⟨a, haC⟩ * c (e k) * (mk ⟨a, haC⟩)⁻¹)⁻¹ := by rw [hx]; group
        _ = (e z * e k) * (e z * c (e k))⁻¹ := by rw [h1, h2]
        _ = (e z * e k) * (c (e k))⁻¹ * (e z)⁻¹ := by group
        _ = (e k * e z) * (c (e k))⁻¹ * (e z)⁻¹ := by rw [hzk.eq]
        _ = e k * (e z * (c (e k))⁻¹) * (e z)⁻¹ := by group
        _ = e k * ((c (e k))⁻¹ * e z) * (e z)⁻¹ := by rw [hzck.inv_right.eq]
        _ = x := by rw [hx]; group
    exact mul_inv_eq_iff_eq_mul.1 h3
  have hνx := key k (n + 1) hkn x
    ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))),
      hxC⟩
  have hx2 : e k * (c (e k))⁻¹ = c (c (e k)) * (e k)⁻¹ := by
    have h1 : ν * x * ν⁻¹ = c (c (e k)) * (e k)⁻¹ := by
      calc ν * x * ν⁻¹ = (ν * e k * ν⁻¹) * (ν * c (e k) * ν⁻¹)⁻¹ := by rw [hx]; group
        _ = c (c (e k)) * (e k)⁻¹ := by rw [hνcc, hνc]
    rw [← hx, ← h1, hνx]
    group
  have hXY : Commute (e k) (c (e k)) := hcomm k k
  have hYW : Commute (c (e k)) (c (c (e k))) := h23 k k
  have hsq : e k * e k = c (c (e k)) * c (e k) := by
    calc e k * e k = c (e k) * ((c (e k))⁻¹ * e k * e k) := by group
      _ = c (e k) * (e k * (c (e k))⁻¹ * e k) := by rw [← hXY.inv_right.eq]
      _ = c (e k) * (c (c (e k)) * (e k)⁻¹ * e k) := by rw [hx2]
      _ = c (e k) * c (c (e k)) := by group
      _ = c (c (e k)) * c (e k) := hYW.eq
  have hk2 : k * k ∈ Subgroup.center (barOf 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro v
    apply hei
    have h5 : e (k * k) = c (c (e k)) * c (e k) := by rw [map_mul, hsq]
    rw [map_mul e v (k * k), map_mul e (k * k) v, h5]
    have hWv : Commute (c (c (e k))) (e v) := (show Commute (e v) (c (c (e k))) from h13 v k).symm
    have hYv : Commute (c (e k)) (e v) := (show Commute (e v) (c (e k)) from hcomm v k).symm
    exact ((hWv.mul_left hYv).eq).symm
  apply hknc
  have e1 : k = k ^ 3 * (k * k)⁻¹ := by rw [pow_three]; group
  rw [e1]
  exact Subgroup.mul_mem _ hk3 (Subgroup.inv_mem _ hk2)

end Moved

section Assembly

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)

theorem iiHardCaseLieMain_of_inputs (hI191 : Lemma129.Input19_1_two) (hP95 : Prop95)
    (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement)
    (h133 : Lemma133Statement) (h135 : Lemma135_iiStatement) : Claims136b.IIHardCaseLieMain := by
  intro G _ _ m B M E A D T L h hN d hd hd1 hfix b B1 hP hS r _hr hEk K hK hnot hBsN hcent _hnb hLie
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hr2, -, hinn, hweak⟩ := hLie
  subst hr2
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLM : L ≤ M := hLc.1
  have hLsn : IsSubnormal L M := hLc.2.1
  have hdA : d ∈ A := h.hD.1 hd
  have hBel : IsElemAbelian 3 B := h.uniq.elemAbelian
  have hBcomm : ∀ y ∈ B, ∀ y' ∈ B, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hBel.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  obtain ⟨hbBL, hσb, hB1BL, hB1b, -⟩ := hP
  have hBsB : Lemma136c.bStarOf B L D b ≤ B :=
    sup_le ((Subgroup.zpowers_le).2 hbBL.1) (inf_le_left.trans inf_le_right)
  have hbBs : b ∈ Lemma136c.bStarOf B L D b := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hbBL.2
  obtain ⟨-, eM, -⟩ := Lemma136.l136_gamma hP95 h111 h121 hcomp h
  have eL : barOf 3 L ≃* alternatingGroup (Fin 7) := (quotEquivBarX hp hLM hLsn).trans eM
  have hd3 : d ^ 3 = 1 := h.hD.2.1.2 d hd
  have hσ3 : barAut 3 L ⟨d, hN hd⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hN hd⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext (by simp [hd3])
    rw [this, map_one]
  obtain ⟨hσd1, -⟩ := Claims136.exists_klein eL _ hσ3 hfix
  have hσb1 : barAut 3 L ⟨b, hbN⟩ ≠ 1 := by rw [hσb hbN]; exact hσd1
  have hb1 : b ≠ 1 := by
    intro h1
    apply hσb1
    have : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) = 1 := Subtype.ext h1
    rw [this, map_one]
  obtain ⟨-, hcgI⟩ := Claims136b.conj_comp hcomp h M.one_mem
  rw [gLBConj_one] at hcgI
  obtain ⟨-, hBN, -, -, hrk⟩ := (h133 h.toSec13).2 L hcgI
  have h9 : 9 ≤ Nat.card ↥(B ⊓ L) := by
    have h2 := Claims136.two_le_pRank_of_alt7 eL
    have hBLel : IsElemAbelian 3 (B ⊓ L) := CFSG.Open.IsElemAbelian.mono hBel inf_le_left
    rw [Claims136.card_eq_pow_pRank3 hBLel, hrk]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 L := Nat.pow_le_pow_right (by norm_num) h2
  obtain ⟨-, -, -, -, -, -, -, -, hBLd⟩ := Claims136.exists_bd_complement eL hBel h.hAB le_sup_right
    (Subgroup.mem_sup_left hdA) (hN hd) hσd1 h9
  have hBLC : B ⊓ L ≤ Cg d := fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hBLd y hy)
  have hML : M ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_card_bStar hP95 h111 h121 hcomp h135 h hN hBN hbN hσb1
      (by rw [hEk.2.2]; norm_num)
  by_cases hB1K : B1 ≤ Subgroup.normalizer (K : Set G)
  ·
    have hS0 : IsPGroup 2 ↥(Subgroup.centralizer (Lemma136c.bStarOf B L D b : Set G) ⊓
        pCoreOf 2 (L ⊓ Cg d)) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊓ Cg d)).to_le inf_le_right
    have hB1N : B1 ≤ Subgroup.normalizer ((Subgroup.centralizer (Lemma136c.bStarOf B L D b : Set G) ⊓
        pCoreOf 2 (L ⊓ Cg d) : Subgroup G) : Set G) := by
      intro x hx
      have hxBL := hB1BL hx
      have hxC : x ∈ Subgroup.centralizer (Lemma136c.bStarOf B L D b : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact hBcomm z (hBsB hz) x hxBL.1
      exact Claims136b.mem_normalizer_inf' (Subgroup.le_normalizer hxC)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ ⟨hxBL.2, hBLC hxBL⟩)
    exact weak_false hI191 h hd1 hBsB hEk hbBs hb1 (hB1BL.trans inf_le_left) (hB1BL.trans hBLC) hB1N
      hS0 hS.2.2.1 hK hnot hBsN hcent hweak hB1K
  ·
    obtain ⟨b₁, hb₁B1, hb₁K⟩ := Set.not_subset.1 hB1K
    have hb₁BL := hB1BL hb₁B1
    have hb₁b : b₁ ∉ Subgroup.zpowers b := by
      intro hm
      have h1 : b₁ ∈ B1 ⊓ Subgroup.zpowers b := ⟨hb₁B1, hm⟩
      rw [hB1b, Subgroup.mem_bot] at h1
      exact hb₁K (h1 ▸ Subgroup.one_mem _)
    exact moved_false h111 h eL hML hdA hd1 hBsB hEk.1 (by rw [hEk.2.2]; norm_num) hbBs hbBL.2 hb1
      hb₁BL.1 hb₁BL.2 (hBLC hb₁BL) hb₁b hK hBsN hcent hinn hb₁K

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims136d

end

module

public import CFSG.GH74.Uniqueness.Section13Dict

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

section Preimage

variable {F : Subgroup X}

omit [Finite X] in
theorem A6.mem_preimage_iff {B : Subgroup (↥F ⧸ center ↥F)} {x : X} :
    x ∈ (B.comap (QuotientGroup.mk' (center ↥F))).map F.subtype ↔
      ∃ hx : x ∈ F, QuotientGroup.mk' (center ↥F) ⟨x, hx⟩ ∈ B := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hxB⟩
    exact ⟨⟨x, hx⟩, hxB, rfl⟩

omit [Finite X] in
theorem A6.comm_of_mk_comm (hodd : Odd (Nat.card (center ↥F))) {a y : X} (haF : a ∈ F)
    (hyF : y ∈ F) (hy : y * y = 1)
    (hcomm : QuotientGroup.mk' (center ↥F) ⟨a, haF⟩ * QuotientGroup.mk' (center ↥F) ⟨y, hyF⟩ =
      QuotientGroup.mk' (center ↥F) ⟨y, hyF⟩ * QuotientGroup.mk' (center ↥F) ⟨a, haF⟩) :
    a * y = y * a := by
  have hmem : a * y * a⁻¹ ∈ F := F.mul_mem (F.mul_mem haF hyF) (F.inv_mem haF)
  have h1 : QuotientGroup.mk' (center ↥F) ⟨y, hyF⟩ =
      QuotientGroup.mk' (center ↥F) ⟨a * y * a⁻¹, hmem⟩ := by
    have e1 : (⟨a * y * a⁻¹, hmem⟩ : ↥F) = ⟨a, haF⟩ * ⟨y, hyF⟩ * ⟨a, haF⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, hcomm, map_inv, mul_inv_cancel_right]
  have hy2 : (⟨y, hyF⟩ : ↥F) ^ 2 ^ 1 = 1 := Subtype.ext (by rw [pow_one, sq]; exact hy)
  have hc2 : (⟨a * y * a⁻¹, hmem⟩ : ↥F) ^ 2 ^ 1 = 1 := by
    apply Subtype.ext
    rw [pow_one, sq]
    change a * y * a⁻¹ * (a * y * a⁻¹) = 1
    calc a * y * a⁻¹ * (a * y * a⁻¹) = a * (y * y) * a⁻¹ := by group
      _ = 1 := by rw [hy]; group
  have h2 := A6.eq_of_inv_mul_mem_two hodd le_rfl hy2 hc2 (QuotientGroup.eq.mp h1)
  have h3 : y = a * y * a⁻¹ := congrArg Subtype.val h2
  calc a * y = (a * y * a⁻¹) * a := by group
    _ = y * a := by rw [← h3]

end Preimage

structure A6.AData (Z : Set X) (M F : Subgroup X) (c : Ctx12 Z M) (htF : c.t ∈ F)
    (Tb : Sylow 2 (↥F ⧸ center ↥F)) (A H : Subgroup X) : Prop where
  le_H : A ≤ H
  H_le_F : H ≤ F
  H_le_M : H ≤ M
  odd : Odd (Nat.card A)
  comm_L : ∀ a ∈ A, ∀ y ∈ c.L, a * y = y * a
  exists_ne : ∃ a ∈ A, ∃ haF : a ∈ F, QuotientGroup.mk' (center ↥F) ⟨a, haF⟩ ∈
      Bender.cartan (Tb : Subgroup (↥F ⧸ center ↥F)) (QuotientGroup.mk' (center ↥F) ⟨c.t, htF⟩) ∧
    QuotientGroup.mk' (center ↥F) ⟨a, haF⟩ ≠ 1
  norm : ∀ g ∈ H, ∀ a ∈ A, g * a * g⁻¹ ∈ A
  surj : ∀ d ∈ Bender.cartan (Tb : Subgroup (↥F ⧸ center ↥F))
      (QuotientGroup.mk' (center ↥F) ⟨c.t, htF⟩),
    ∃ g : X, ∃ hgF : g ∈ F, g ∈ H ∧ QuotientGroup.mk' (center ↥F) ⟨g, hgF⟩ = d

theorem A6.odd_one_lt_e {n : ℕ} (hn : 2 ≤ n) :
    Odd ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) ∧ 1 < (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) := by
  have hodd : Odd (2 ^ n + 1) := by
    have : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
    exact this.add_one
  have hg3 : Nat.gcd 3 (2 ^ n + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
  have hmul := Nat.div_mul_cancel (Nat.gcd_dvd_right 3 (2 ^ n + 1))
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨Odd.of_dvd_nat hodd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right 3 _)), ?_⟩
  by_contra hle
  have := Nat.mul_le_mul (not_lt.mp hle) hg3
  omega

theorem A6.exists_aData
    {c : Ctx12 Z M} {n i e : ℕ} (S : ZDSetup X Z M) (hL : LData c n i)
    {F T : Subgroup X} {Tb : Sylow 2 (↥F ⧸ center ↥F)} (h : A6.Dict Z M F n e Tb T)
    (hLF : c.L ≤ F) :
    ∃ A H : Subgroup X, A6.AData Z M F c (hLF c.t_mem_L) Tb A H := by
  set π := QuotientGroup.mk' (center ↥F) with hπ
  have htF : c.t ∈ F := hLF c.t_mem_L
  obtain ⟨htb, htbQ⟩ := h.tbar S htF c.ht c.htM
  set tb := π ⟨c.t, htF⟩ with htbdef
  have hc := h.bsub.bender.benderCore Tb htb htbQ
  set Db := Bender.cartan (Tb : Subgroup (↥F ⧸ center ↥F)) tb with hDb
  set D2b := Bender.fixCartan (Tb : Subgroup (↥F ⧸ center ↥F)) tb with hD2b
  have hD2le : D2b ≤ Db := Bender.fixCartan_le_cartan _ _
  set A : Subgroup X := (D2b.comap π).map F.subtype with hA
  set H : Subgroup X := (Db.comap π).map F.subtype with hH
  have hodd := h.odd
  have he : e = (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) := by
    rcases h.bsub.bender.cases' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, he, -⟩
    · omega
    · omega
    · exact he
  have hn : 2 ≤ n := hL.hn
  obtain ⟨heodd, he1⟩ := A6.odd_one_lt_e hn
  rw [← he] at heodd he1
  have hHM : H ≤ M := by
    intro g hg
    obtain ⟨hgF, hgD⟩ := A6.mem_preimage_iff.mp hg
    exact (A2.mk_mem_normalizer_iff S h.bsub h.borel ⟨g, hgF⟩).mp
      (Bender.cartan_le_borel _ _ hgD)
  have hzM : c.z ∈ zHull Z M := Cor713.mem_zHull_of_mem c.hz c.hzM
  refine ⟨A, H, ?_⟩
  refine
    { le_H := Subgroup.map_mono (Subgroup.comap_mono hD2le)
      H_le_F := map_subtype_le _
      H_le_M := hHM
      odd := ?_
      comm_L := ?_
      exists_ne := ?_
      norm := ?_
      surj := ?_ }
  ·
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    obtain ⟨haF, haD⟩ := A6.mem_preimage_iff.mp a.2
    have ha2 : orderOf (a : X) = 2 := by rw [Subgroup.orderOf_coe]; exact ha
    have haa : (⟨(a : X), haF⟩ : ↥F) * ⟨a, haF⟩ = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← sq, ← ha2, pow_orderOf_eq_one]; rfl)
    have hπa : π ⟨a, haF⟩ = 1 := by
      have hD2odd : Odd (Nat.card D2b) := by rw [hc.card_fixCartan]; exact heodd
      have h1 : π ⟨a, haF⟩ * π ⟨a, haF⟩ = 1 := by rw [← map_mul, haa, map_one]
      have h2 : orderOf (π ⟨a, haF⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
      have h3 : orderOf (π ⟨a, haF⟩) ∣ Nat.card D2b := Subgroup.orderOf_dvd_natCard D2b haD
      have h4 : Nat.Coprime 2 (Nat.card D2b) := Nat.coprime_two_left.mpr hD2odd
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 h4) h3)
    have hcen : (⟨a, haF⟩ : ↥F) ∈ center ↥F := (QuotientGroup.eq_one_iff _).mp hπa
    have ho : orderOf (⟨a, haF⟩ : ↥F) = 2 := by rw [Subgroup.orderOf_mk]; exact ha2
    exact CFSG.OddInversion.notMem_of_odd_card hodd ho hcen
  ·
    intro a ha y hy
    obtain ⟨haF, haD⟩ := A6.mem_preimage_iff.mp ha
    set P : Subgroup X := ((centralizer ({π ⟨a, haF⟩} : Set (↥F ⧸ center ↥F))).comap π).map
      F.subtype with hP
    have hcommP : ∀ g (hgF : g ∈ F), π ⟨g, hgF⟩ * π ⟨a, haF⟩ = π ⟨a, haF⟩ * π ⟨g, hgF⟩ →
        g ∈ P := by
      intro g hgF hcomm
      refine A6.mem_preimage_iff.mpr ⟨hgF, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact hcomm
    have hLP : c.L ≤ P := by
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [zpowers_le]
        refine hcommP c.z (hLF c.z_mem_L) ?_
        have hzR : π ⟨c.z, hLF c.z_mem_L⟩ ∈ Bender.rootCenter (Tb : Subgroup (↥F ⧸ center ↥F)) :=
          (h.mem_zHull_iff S hL (hL.m_le.trans hLF) (h.zHull_le S hL (hL.m_le.trans hLF) hzM)).mp hzM
        have hac : π ⟨a, haF⟩ ∈ centralizer
            (Bender.rootCenter (Tb : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F)) := by
          rw [hc.centralizer_rootCenter_eq]
          exact mem_sup_right haD
        exact (mem_centralizer_iff.mp hac _ hzR)
      · rw [zpowers_le]
        refine hcommP c.t htF ?_
        have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp haD).2
        exact h1.symm
      · intro k hk
        have hk' : k ∈ c.D ⊓ c.L := by rw [← hL.k_eq']; exact hk
        obtain ⟨hkD, hkL⟩ := mem_inf.mp hk'
        obtain ⟨hkM, hkt⟩ := mem_inf.mp hkD
        have hkF := hLF hkL
        refine hcommP k hkF ?_
        have hkDb : π ⟨k, hkF⟩ ∈ Db := by
          refine mem_inf.mpr ⟨(A2.mk_mem_normalizer_iff S h.bsub h.borel _).mpr hkM, ?_⟩
          rw [Bender.mem_conjugate_iff_mul_inv]
          have htk : c.t * k * c.t⁻¹ ∈ F := F.mul_mem (F.mul_mem htF hkF) (F.inv_mem htF)
          have e1 : tb * π ⟨k, hkF⟩ * tb⁻¹ = π ⟨c.t * k * c.t⁻¹, htk⟩ := by
            rw [htbdef, ← map_inv, ← map_mul, ← map_mul]
            rfl
          rw [e1]
          exact (A2.mk_mem_normalizer_iff S h.bsub h.borel _).mpr ((mem_conjugate_iff).mp hkt)
        exact hc.cartan_comm hkDb (hD2le haD)
    have hgen : c.L ≤ centralizer ({a} : Set X) := by
      calc c.L = zHull Z c.L := (IsProductDisconnected.zHull_lSubgroup S.invariant c.ht c.hz M).symm
        _ ≤ centralizer ({a} : Set X) := by
          refine (closure_le _).mpr fun w hw => ?_
          have hwF : w ∈ F := hLF hw.2
          obtain ⟨hwF', hwc⟩ := A6.mem_preimage_iff.mp (hLP hw.2)
          rw [mem_centralizer_singleton_iff] at hwc
          have h1 := A6.comm_of_mk_comm hodd haF hwF' (S.invariant.mul_self_eq_one hw.1) hwc.symm
          rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
          exact h1.symm
    exact (mem_centralizer_singleton_iff.mp (hgen hy)).symm
  ·
    have hne : D2b ≠ ⊥ := by
      intro hbot
      have := hc.card_fixCartan
      rw [← hD2b, hbot, Subgroup.card_bot] at this
      omega
    obtain ⟨d, hd, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne |> fun ⟨d, hd1⟩ =>
      (⟨d, d.2, fun h1 => hd1 (Subtype.ext h1)⟩ : ∃ d ∈ D2b, d ≠ 1)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (center ↥F) d
    exact ⟨a, A6.mem_preimage_iff.mpr ⟨a.2, hd⟩, a.2, hD2le hd, hd1⟩
  ·
    intro g hg a ha
    obtain ⟨hgF, hgD⟩ := A6.mem_preimage_iff.mp hg
    obtain ⟨haF, haD⟩ := A6.mem_preimage_iff.mp ha
    have hmem : g * a * g⁻¹ ∈ F := F.mul_mem (F.mul_mem hgF haF) (F.inv_mem hgF)
    refine A6.mem_preimage_iff.mpr ⟨hmem, ?_⟩
    have e1 : π ⟨g * a * g⁻¹, hmem⟩ = π ⟨g, hgF⟩ * π ⟨a, haF⟩ * (π ⟨g, hgF⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1, hc.cartan_comm hgD (hD2le haD), mul_inv_cancel_right]
    exact haD
  ·
    intro d hd
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center ↥F) d
    exact ⟨g, g.2, A6.mem_preimage_iff.mpr ⟨g.2, hd⟩, rfl⟩

end CFSG.GH74.Uniqueness

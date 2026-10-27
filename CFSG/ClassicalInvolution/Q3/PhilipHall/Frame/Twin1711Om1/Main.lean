module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.Overgroup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.FixSet
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.Index
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.Involutions
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.Quat
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.R0Card
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf2Cls
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Quat

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
open CFSG.ClassicalInvolution.Generic

set_option linter.unusedSectionVars false

theorem IsUniqueInvolution.comm {G : Type} [Group G] {K : Subgroup G} {u : G}
    (h : IsUniqueInvolution K u) {k : G} (hk : k ∈ K) : k * u = u * k := by
  have hm : k * u * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk h.mem) (K.inv_mem hk)
  have hs : k * u * k⁻¹ * (k * u * k⁻¹) = 1 := by
    calc k * u * k⁻¹ * (k * u * k⁻¹) = k * (u * u) * k⁻¹ := by group
      _ = 1 := by rw [h.sq, mul_one, mul_inv_cancel]
  rcases h.unique _ hm hs with h1 | h1
  · exfalso
    apply h.ne_one
    have : u = k⁻¹ * (k * u * k⁻¹) * k := by group
    rw [this, h1]
    group
  · calc k * u = k * u * k⁻¹ * k := by group
      _ = u * k := by rw [h1]

theorem coreData_conj {G : Type} [Group G] {R : Subgroup G} {t : G}
    (hC : CoreData (⊤ : Subgroup G) R t) (g : G) :
    CoreData (⊤ : Subgroup G) (conjSub g R) (g * t * g⁻¹) := by
  let ψ : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  have hψ : Function.Injective ψ := (MulAut.conj g⁻¹).injective
  have hr : ψ.range = ⊤ := MonoidHom.range_eq_top.2 (MulAut.conj g⁻¹).surjective
  have ht : ψ (g * t * g⁻¹) = t := by
    simp only [ψ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  rw [← hr] at hC
  have h := hC.comap hψ ht
  have hR : R.comap ψ = conjSub g R := by
    ext x
    simp only [Subgroup.mem_comap, ψ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      mem_conjSub_iff]
  rwa [hR] at h

theorem not_twinFail {G : Type} [Group G] {R : Subgroup G} {t : G}
    (hC : CoreData (⊤ : Subgroup G) R t) {x y : G} (hx : x ∈ R) (hy : y ∈ R)
    (hxx : x * x = t) (hR : ∀ r ∈ R, ∃ k : ℕ, r = x ^ k ∨ r = y * x ^ k) {s : G}
    (hs : s * t = t * s) :
    ¬ ((∃ g ∈ ({x, y} : Set G), ∀ k < 4, s * g * s⁻¹ ≠ x ^ k ∧ s * g * s⁻¹ ≠ y * x ^ k) ∧
      ∃ a ∈ ({x, y} : Set G), ∃ b ∈ ({x, y} : Set G), a * (s * b * s⁻¹) ≠ (s * b * s⁻¹) * a) := by
  rintro ⟨⟨g, hg, hgk⟩, a, ha, b, hb, hab⟩
  have hgR : g ∈ R := by
    rcases hg with rfl | rfl
    · exact hx
    · exact hy
  have haR : a ∈ R := by
    rcases ha with rfl | rfl
    · exact hx
    · exact hy
  have hbR : b ∈ R := by
    rcases hb with rfl | rfl
    · exact hx
    · exact hy
  have hx4 : x ^ 4 = 1 := by
    have h2 : x ^ 2 = t := by rw [pow_two, hxx]
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, pow_two, hC.inv.sq]
  have hred : ∀ k : ℕ, x ^ k = x ^ (k % 4) := by
    intro k
    conv_lhs => rw [← Nat.mod_add_div k 4, pow_add, pow_mul, hx4, one_pow, mul_one]
  have hnot : ¬ (s * g * s⁻¹ ∈ R) := by
    intro hm
    obtain ⟨k, hk | hk⟩ := hR _ hm
    · exact (hgk (k % 4) (Nat.mod_lt _ (by norm_num))).1 (by rw [hk, hred])
    · exact (hgk (k % 4) (Nat.mod_lt _ (by norm_num))).2 (by rw [hk, hred])
  have hs' : s ∈ (⊤ : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) :=
    ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.2 hs⟩
  rcases hC.twins s hs' with h | h
  · apply hnot
    rw [← h]
    exact conj_mem_conjSub hgR
  · exact hab (h a haR _ (conj_mem_conjSub hbR))

theorem card_quat_eight {G : Type} [Group G] {R : Subgroup G} (e : ↥R ≃* QuaternionGroup 2) :
    Nat.card R = 8 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem isPGroup_quat {G : Type} [Group G] {R : Subgroup G} (e : ↥R ≃* QuaternionGroup 2) :
    IsPGroup 2 R :=
  IsPGroup.of_card (n := 3) (by rw [card_quat_eight e]; norm_num)

theorem conj_eq_of_comm' {G : Type} [Group G] {x u : G}
    (hx : x ∈ Subgroup.centralizer ({u} : Set G)) : x * u * x⁻¹ = u := by
  rw [Subgroup.mem_centralizer_singleton_iff.1 hx, mul_assoc, mul_inv_cancel, mul_one]


theorem exists_conj_core {R : Subgroup WP} {u : WP} (hC : CoreData (⊤ : Subgroup WP) R u)
    {S : Subgroup WP} (hS : S ≤ Subgroup.centralizer {u}) {k m : ℕ} (hSc : Nat.card S = 2 ^ k)
    (hCc : Nat.card (Subgroup.centralizer {u}) ∣ 2 ^ k * m) (hm : Odd m) :
    ∃ h ∈ Subgroup.centralizer {u}, conjSub h R ≤ S ∧
      CoreData (⊤ : Subgroup WP) (conjSub h R) u := by
  obtain ⟨e⟩ := hC.q8
  have hRC : R ≤ Subgroup.centralizer {u} := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.2 (Om1.IsUniqueInvolution.comm hC.inv hr)
  obtain ⟨h, hh, hle⟩ := OmGen.exists_conj_le_of_card hS hRC (isPGroup_quat e) hSc hCc hm
  have hhu : h * u = u * h := Subgroup.mem_centralizer_singleton_iff.1 hh
  exact ⟨h, hh, hle, OmGen.CoreData.conj_of_comm hC hhu⟩

theorem ident_of_conj {R : Subgroup WP} {t : WP} (x : WP) (ht : x * t * x⁻¹ = t0)
    (hR : conjSub x R = R0) : ∃ α : WP ≃* WP, α t = t0 ∧ R.map α.toMonoidHom = R0 :=
  ⟨MulAut.conj x, by simpa [MulAut.conj_apply] using ht, hR⟩

theorem conj_eq_of_comm {x u : WP} (hx : x ∈ Subgroup.centralizer ({u} : Set WP)) :
    x * u * x⁻¹ = u := by
  rw [Subgroup.mem_centralizer_singleton_iff.1 hx, mul_assoc, mul_inv_cancel, mul_one]

theorem centralizer_tb : Subgroup.centralizer ({tb} : Set WP) = Subgroup.centralizer {ta} := by
  ext x
  simp only [Subgroup.mem_centralizer_singleton_iff, tb_eq]
  constructor
  · intro h
    have h2 : zW * (x * ta) = zW * (ta * x) := by
      rw [← mul_assoc, ← zW_comm x, mul_assoc, h, mul_assoc]
    exact mul_left_cancel h2
  · intro h
    rw [← mul_assoc, zW_comm x, mul_assoc, h, mul_assoc]

theorem coreData_ident (R : Subgroup WP) (t : WP) (hC : CoreData (⊤ : Subgroup WP) R t) :
    ∃ α : WP ≃* WP, α t = t0 ∧ R.map α.toMonoidHom = R0 := by
  have htz : t ≠ zW := by
    intro h
    apply hC.noncentral
    intro x _
    rw [h]
    exact zW_comm x
  obtain ⟨g, hg⟩ := exists_conj_rep t hC.inv.sq hC.inv.ne_one htz
  have hC1 := coreData_conj hC g
  rcases hg with h0 | ha | hb | hc
  ·
    rw [h0] at hC1
    obtain ⟨hT, -, hTc, hS0c, -, hS0T, -⟩ := classPkg0
    obtain ⟨h, hh, hle, hC2⟩ := exists_conj_core hC1 (S := closureW wS0) (k := 12) (m := 27)
      hS0T (by rw [hS0c]; norm_num) (by rw [hTc]; norm_num) ⟨13, rfl⟩
    obtain ⟨e⟩ := hC2.q8
    obtain ⟨x, y, hx, hy, hxx, hyy, hyx, hRxy⟩ := exists_quat_gens e hC2.inv
    have hcard : Nat.card (conjSub h (conjSub g R)) = 8 := card_quat_eight e
    have hgen : ∀ {K : Subgroup WP}, x ∈ K → y ∈ K → conjSub h (conjSub g R) ≤ K := by
      intro K hxK hyK r hr
      obtain ⟨k, hk | hk⟩ := hRxy r hr
      · rw [hk]; exact K.pow_mem hxK k
      · rw [hk]; exact K.mul_mem hyK (K.pow_mem hxK k)
    have hht : (h * g) * t * (h * g)⁻¹ = t0 := by
      rw [show (h * g) * t * (h * g)⁻¹ = h * (g * t * g⁻¹) * h⁻¹ by group, h0,
        conj_eq_of_comm hh]
    rcases q8_S0 (hle hx) (hle hy) hxx hyy hyx with ⟨hx0, hy0⟩ | ⟨hx0, hy0⟩ | ⟨s, hs, hfail⟩
    · have heq : conjSub h (conjSub g R) = R0 :=
        Subgroup.eq_of_le_of_card_ge (hgen hx0 hy0) (by rw [hcard]; exact card_R0_le)
      exact ident_of_conj (h * g) hht (by rw [conjSub_mul, heq])
    · have heq : conjSub h (conjSub g R) = R0' :=
        Subgroup.eq_of_le_of_card_ge (hgen hx0 hy0) (by rw [hcard]; exact card_R0'_le)
      have hs1 : s1 ∈ T0 := Subgroup.mem_centralizer_singleton_iff.2
        (comm_t0_of_mem (w := wS1) (by simp))
      refine ident_of_conj (s1⁻¹ * (h * g)) ?_ ?_
      · rw [show (s1⁻¹ * (h * g)) * t * (s1⁻¹ * (h * g))⁻¹ =
          s1⁻¹ * ((h * g) * t * (h * g)⁻¹) * s1⁻¹⁻¹ by group, hht,
          conj_eq_of_comm (T0.inv_mem hs1)]
      · rw [conjSub_mul, conjSub_mul, heq, R0', conjSub_inv_conjSub]
    · exfalso
      have hsT : s ∈ T0 := hT ▸ hs
      exact not_twinFail hC2 hx hy hxx hRxy (Subgroup.mem_centralizer_singleton_iff.1 hsT) hfail
  ·
    exfalso
    rw [ha] at hC1
    obtain ⟨hCa, hSac, hSaC⟩ := classPkgA
    obtain ⟨h, -, hle, hC2⟩ := exists_conj_core hC1 (k := 11) (m := 45) hSaC hSac hCa ⟨22, rfl⟩
    obtain ⟨e⟩ := hC2.q8
    obtain ⟨x, y, hx, hy, hxx, hyy, hyx, -⟩ := exists_quat_gens e hC2.inv
    exact q8_Sa (hle hx) (hle hy) hxx hyy hyx
  ·
    exfalso
    rw [hb] at hC1
    obtain ⟨hCa, hSac, hSaC⟩ := classPkgA
    obtain ⟨h, -, hle, hC2⟩ := exists_conj_core hC1 (k := 11) (m := 45)
      (by rw [centralizer_tb]; exact hSaC) hSac (by rw [centralizer_tb]; exact hCa) ⟨22, rfl⟩
    obtain ⟨e⟩ := hC2.q8
    obtain ⟨x, -, hx, -, hxx, -⟩ := exists_quat_gens e hC2.inv
    exact sq_Sa_ne (hle hx) hxx
  ·
    exfalso
    rw [hc] at hC1
    obtain ⟨hCc, hCcc, hScc, hScC⟩ := classPkgC
    obtain ⟨h, -, hle, hC2⟩ := exists_conj_core hC1 (k := 10) (m := 3) hScC hScc (by rw [hCcc]) ⟨1, rfl⟩
    obtain ⟨e⟩ := hC2.q8
    obtain ⟨x, y, hx, hy, hxx, hyy, hyx, hRxy⟩ := exists_quat_gens e hC2.inv
    obtain ⟨s, hs, hfail⟩ := q8_Sc (hle hx) (hle hy) hxx hyy hyx
    have hsC : s ∈ Subgroup.centralizer ({tc} : Set WP) := hCc ▸ hs
    exact not_twinFail hC2 hx hy hxx hRxy (Subgroup.mem_centralizer_singleton_iff.1 hsC) hfail

theorem no_sandwich_R0 (B : Set (Subgroup WP)) (N : Subgroup WP)
    (hR : IsUniqueInvolution R0 t0) (hS : SandwichData (⊤ : Subgroup WP) R0 t0 B N) : False := by
  have hT : (⊤ : Subgroup WP) ⊓ Subgroup.centralizer ({t0} : Set WP) = T0 := top_inf_eq _
  have hM : T0 ≤ blockStab (⊤ : Subgroup WP) B := hT ▸ hS.twins_le_blockStab
  have hMt : blockStab (⊤ : Subgroup WP) B ≠ ⊤ := hS.blockStab_ne
  have hov := overgroup hM hMt
  have hD : ∀ x : WP, x * t0 * x⁻¹ ∈ N → x * t0 * x⁻¹ = t0 ∨ x * t0 * x⁻¹ = t0 * zW := by
    intro x hx
    have := OmGen.conj_mem_of_blockStab_le hS hR le_rfl (Zt := {t0, t0 * zW})
      (fun m hm => hov m hm) (Subgroup.mem_top x) hx
    simpa using this
  have hs1 : s1 ∈ (⊤ : Subgroup WP) ⊓ Subgroup.centralizer ({t0} : Set WP) :=
    ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.2
      (comm_t0_of_mem (w := wS1) (by simp))⟩
  have h1 : (1 : WP) ∈ (⊤ : Subgroup WP) ⊓ Subgroup.centralizer ({t0} : Set WP) := one_mem _
  have hR0'B : R0' ∈ B := hS.twins s1 hs1
  have hfix := card_fixSet_le hS.mem hR0'B
  have hidx := hS.index
  rw [hT] at hidx
  have hNle : N ≤ T0 := hT ▸ hS.le
  have hNn : (N.subgroupOf T0).Normal := hT ▸ hS.normal
  have hR0N : R0 ≤ N := by
    have := hS.twins_le 1 h1
    rwa [show conjSub (1 : WP) R0 = R0 by ext x; simp [mem_conjSub_iff]] at this
  have hR0'N : R0' ≤ N := hS.twins_le s1 hs1
  have hcard := card_le_of_avoid hNle hNn hR0N hR0'N hD
  have hT0 : Nat.card T0 = 110592 := classPkg0.2.2.1
  have hmul : N.relIndex T0 * Nat.card N = Nat.card T0 := by
    have := Subgroup.relIndex_mul_card N T0
    rwa [inf_eq_left.2 hNle] at this
  rw [hT0] at hmul
  have : N.relIndex T0 ≤ 192 := hidx.trans hfix
  nlinarith

theorem noSandwichIn_wPlus : NoSandwichIn ModOm1 :=
  noSandwichIn_of_ident R0 t0 coreData_ident no_sandwich_R0

theorem om1_proved : NoSandwichAt ModOm1 :=
  noSandwichAt_of_in noSandwichIn_wPlus

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1

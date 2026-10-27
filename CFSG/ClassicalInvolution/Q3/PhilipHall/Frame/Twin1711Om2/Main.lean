module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.Overgroup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.Index
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.Involutions
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.Quat
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.Pairing
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.Main

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Generic

set_option linter.unusedSectionVars false

section Transport

variable {H : Type} [Group H] [Finite H]

theorem sandwichSizeTwoIn_of_ident (R0 : Subgroup H) (x0 : H)
    (hid : ∀ (R : Subgroup H) (t : H), CoreData (⊤ : Subgroup H) R t →
      ∃ α : H ≃* H, α t = x0 ∧ R.map α.toMonoidHom = R0)
    (h4 : ∀ (B : Set (Subgroup H)) (N : Subgroup H),
      IsUniqueInvolution R0 x0 → SandwichData (⊤ : Subgroup H) R0 x0 B N → B.ncard = 2) :
    SandwichSizeTwoIn H := by
  intro R t B N hC hS
  obtain ⟨α, hαt, hαR⟩ := hid R t hC
  let ψ : H →* H := α.symm.toMonoidHom
  have hψ : Function.Injective ψ := α.symm.injective
  have hr : ψ.range = ⊤ := MonoidHom.range_eq_top.2 α.symm.surjective
  have ht' : ψ x0 = t := by simp [ψ, ← hαt]
  have hRle : R ≤ ψ.range := by rw [hr]; exact le_top
  rw [← hr] at hC hS
  have hC' := hC.comap hψ ht'
  have hS' := hS.comap hC.le hψ ht'
  have hRc : R.comap ψ = R0 := by
    rw [← hαR]
    ext y
    simp only [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨_, hy, by simp [ψ]⟩
    · rintro ⟨r, hr', rfl⟩
      simpa [ψ] using hr'
  rw [hRc] at hC' hS'
  have h2 := h4 _ _ hC'.inv hS'
  rw [Set.InjOn.ncard_image] at h2
  · exact h2
  · intro J1 hJ1 J2 hJ2 h12
    exact comap_injOn (block_le_range hS hC.le hJ1) (block_le_range hS hC.le hJ2) h12

theorem pairingIn_of_ident (R0 : Subgroup H) (x0 : H)
    (hid : ∀ (R : Subgroup H) (t : H), CoreData (⊤ : Subgroup H) R t →
      ∃ α : H ≃* H, α t = x0 ∧ R.map α.toMonoidHom = R0)
    (hp : IsUniqueInvolution R0 x0 → (commNbrs (⊤ : Subgroup H) R0).ncard = 4 ∧
      ∀ J ∈ commNbrs (⊤ : Subgroup H) R0, ∀ J' ∈ commNbrs (⊤ : Subgroup H) R0, J ≠ J' →
        ∀ u u' : H, IsUniqueInvolution J u → IsUniqueInvolution J' u' →
          u ≠ u' ∧ ∀ x ∈ (⊤ : Subgroup H), x * (u * u') = (u * u') * x) :
    PairingIn H := by
  intro R t hC
  obtain ⟨α, hαt, hαR⟩ := hid R t hC
  let ψ : H →* H := α.symm.toMonoidHom
  have hψ : Function.Injective ψ := α.symm.injective
  have hr : ψ.range = ⊤ := MonoidHom.range_eq_top.2 α.symm.surjective
  have hRc : R.comap ψ = R0 := by
    rw [← hαR]
    ext y
    simp only [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨_, hy, by simp [ψ]⟩
    · rintro ⟨r, hr', rfl⟩
      simpa [ψ] using hr'
  have hRle : R ≤ ψ.range := by rw [hr]; exact le_top
  have ht' : ψ x0 = t := by simp [ψ, ← hαt]
  have hC' : CoreData (⊤ : Subgroup H) (R.comap ψ) x0 := by
    have hC0 := hC
    rw [← hr] at hC0
    exact hC0.comap hψ ht'
  rw [hRc] at hC'
  have hcn := commNbrs_comap hRle hψ
  rw [hRc, hr] at hcn
  obtain ⟨h4, hpair⟩ := hp hC'.inv
  rw [hcn] at h4 hpair
  have hinj : Set.InjOn (Subgroup.comap ψ) (commNbrs (⊤ : Subgroup H) R) :=
    fun J1 _ J2 _ h12 => comap_injOn (show J1 ≤ ψ.range by rw [hr]; exact le_top)
      (show J2 ≤ ψ.range by rw [hr]; exact le_top) h12
  rw [hinj.ncard_image] at h4
  refine ⟨h4, ?_⟩
  intro J hJ J' hJ' hne u u' hu hu'
  have hJle : J ≤ ψ.range := by rw [hr]; exact le_top
  have hJ'le : J' ≤ ψ.range := by rw [hr]; exact le_top
  obtain ⟨u0, hu0⟩ := hJle hu.mem
  obtain ⟨u0', hu0'⟩ := hJ'le hu'.mem
  obtain ⟨hne', hcomm⟩ := hpair (J.comap ψ) ⟨J, hJ, rfl⟩ (J'.comap ψ) ⟨J', hJ', rfl⟩
    (fun h12 => hne (comap_injOn hJle hJ'le h12)) u0 u0'
    (uniqueInv_of_comap hψ hu hu0) (uniqueInv_of_comap hψ hu' hu0')
  refine ⟨fun h12 => hne' (hψ (by rw [hu0, hu0']; exact h12)), ?_⟩
  intro x _
  obtain ⟨x0', rfl⟩ : x ∈ ψ.range := by rw [hr]; exact Subgroup.mem_top _
  have := congrArg ψ (hcomm x0' (Subgroup.mem_top _))
  simp only [map_mul, hu0, hu0'] at this
  exact this

end Transport

theorem sandwichSizeTwoAt_of_equiv {H H' : Type} [Group H] [Group H']
    (h : SandwichSizeTwoAt H') (f : H ≃* H') : SandwichSizeTwoAt H := by
  intro G _ _ X R t B N ⟨e⟩ hC hS
  exact h G X R t B N ⟨e.trans f⟩ hC hS

theorem pairingAt_of_equiv {H H' : Type} [Group H] [Group H'] (h : PairingAt H') (f : H ≃* H') :
    PairingAt H := by
  intro G _ _ X R t ⟨e⟩ hC
  exact h G X R t ⟨e.trans f⟩ hC

theorem exists_conj_coreY {R : Subgroup HY} {u : HY} (hC : CoreData (⊤ : Subgroup HY) R u)
    {S : Subgroup HY} (hS : S ≤ Subgroup.centralizer {u}) {k m : ℕ} (hSc : Nat.card S = 2 ^ k)
    (hCc : Nat.card (Subgroup.centralizer {u}) ∣ 2 ^ k * m) (hm : Odd m) :
    ∃ h ∈ Subgroup.centralizer {u}, conjSub h R ≤ S ∧
      CoreData (⊤ : Subgroup HY) (conjSub h R) u := by
  obtain ⟨e⟩ := hC.q8
  have hRC : R ≤ Subgroup.centralizer {u} := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.2 (Om1.IsUniqueInvolution.comm hC.inv hr)
  obtain ⟨h, hh, hle⟩ := OmGen.exists_conj_le_of_card hS hRC (Om1.isPGroup_quat e) hSc hCc hm
  have hhu : h * u = u * h := Subgroup.mem_centralizer_singleton_iff.1 hh
  exact ⟨h, hh, hle, OmGen.CoreData.conj_of_comm hC hhu⟩

theorem coreData_identY (R : Subgroup HY) (t : HY) (hC : CoreData (⊤ : Subgroup HY) R t) :
    ∃ α : HY ≃* HY, α t = t0Y ∧ R.map α.toMonoidHom = R0Y := by
  have hnc : t ∉ Subgroup.center HY := by
    intro h
    apply hC.noncentral
    intro x _
    exact (Subgroup.mem_center_iff.1 h x)
  obtain ⟨g, hg⟩ := exists_conj_repY t hC.inv.sq hnc
  have hC1 := Om1.coreData_conj hC g
  rcases hg with h0 | hc
  · rw [h0] at hC1
    obtain ⟨hT, -, hTc, hS0c, -, hS0T, -⟩ := classPkg0Y
    obtain ⟨h, hh, hle, hC2⟩ := exists_conj_coreY hC1 (S := closureY wS0) (k := 12) (m := 27)
      hS0T (by rw [hS0c]; norm_num) (by rw [hTc]; norm_num) ⟨13, rfl⟩
    obtain ⟨e⟩ := hC2.q8
    obtain ⟨x, y, hx, hy, hxx, hyy, hyx, hRxy⟩ := exists_quat_gens e hC2.inv
    have hcard : Nat.card (conjSub h (conjSub g R)) = 8 := Om1.card_quat_eight e
    rcases q8_S0Y (hle hx) (hle hy) hxx hyy hyx with ⟨hx0, hy0⟩ | ⟨s, hs, hfail⟩
    · have hle0 : conjSub h (conjSub g R) ≤ R0Y := by
        intro r hr
        obtain ⟨k, hk | hk⟩ := hRxy r hr
        · rw [hk]; exact R0Y.pow_mem hx0 k
        · rw [hk]; exact R0Y.mul_mem hy0 (R0Y.pow_mem hx0 k)
      have heq : conjSub h (conjSub g R) = R0Y :=
        Subgroup.eq_of_le_of_card_ge hle0 (by rw [hcard]; exact card_R0Y_le)
      refine ⟨MulAut.conj (h * g), ?_, ?_⟩
      · simp only [MulAut.conj_apply]
        rw [show h * g * t * (h * g)⁻¹ = h * (g * t * g⁻¹) * h⁻¹ by group, h0,
          Om1.conj_eq_of_comm' hh]
      · show conjSub (h * g) R = R0Y
        rw [conjSub_mul, heq]
    · exfalso
      have hsT : s ∈ T0Y := hT ▸ hs
      exact Om1.not_twinFail hC2 hx hy hxx hRxy (Subgroup.mem_centralizer_singleton_iff.1 hsT)
        hfail
  · exfalso
    rw [hc] at hC1
    obtain ⟨hCc, hScc, hScC, hCcC⟩ := classPkgCY
    obtain ⟨h, -, hle, hC2⟩ := exists_conj_coreY hC1 (k := 10) (m := 3) hScC hScc hCc ⟨1, rfl⟩
    obtain ⟨e⟩ := hC2.q8
    obtain ⟨x, y, hx, hy, hxx, hyy, hyx, hRxy⟩ := exists_quat_gens e hC2.inv
    obtain ⟨s, hs, hfail⟩ := q8_ScY (hle hx) (hle hy) hxx hyy hyx
    exact Om1.not_twinFail hC2 hx hy hxx hRxy
      (Subgroup.mem_centralizer_singleton_iff.1 (hCcC hs)) hfail

theorem conjSub_R0Y_eq_iff (hR : IsUniqueInvolution R0Y t0Y) {a b : HY} :
    conjSub a R0Y = conjSub b R0Y ↔ a * t0Y * a⁻¹ = b * t0Y * b⁻¹ := by
  constructor
  · intro h
    have h1 : conjSub (b⁻¹ * a) R0Y = R0Y := by
      rw [conjSub_mul, h, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have h2 := (normalizer_R0Y hR _).1 h1
    have h3 := Om1.conj_eq_of_comm' h2
    calc a * t0Y * a⁻¹ = b * ((b⁻¹ * a) * t0Y * (b⁻¹ * a)⁻¹) * b⁻¹ := by group
      _ = b * t0Y * b⁻¹ := by rw [h3]
  · intro h
    have h1 : b⁻¹ * a ∈ T0Y := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc b⁻¹ * a * t0Y = b⁻¹ * (a * t0Y * a⁻¹) * a := by group
        _ = b⁻¹ * (b * t0Y * b⁻¹) * a := by rw [h]
        _ = t0Y * (b⁻¹ * a) := by group
    have h2 := (normalizer_R0Y hR _).2 h1
    calc conjSub a R0Y = conjSub b (conjSub (b⁻¹ * a) R0Y) := by
          rw [← conjSub_mul, mul_inv_cancel_left]
      _ = conjSub b R0Y := by rw [h2]

theorem fuse0_mem_of_conj {M : Subgroup HY} (hM : T0Y ≤ M) {m : HY} (hm : m ∈ M) {k : ℕ}
    (hk : k < 3) (h : m * t0Y * m⁻¹ = t0Y * cK k) : fuse0 k ∈ M := by
  have h1 : (fuse0 k)⁻¹ * m ∈ T0Y := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hf := fuse0_conj hk
    calc (fuse0 k)⁻¹ * m * t0Y = (fuse0 k)⁻¹ * (m * t0Y * m⁻¹) * m := by group
      _ = (fuse0 k)⁻¹ * (fuse0 k * t0Y * (fuse0 k)⁻¹) * m := by rw [h, hf]
      _ = t0Y * ((fuse0 k)⁻¹ * m) := by group
  have h2 := hM h1
  have : fuse0 k = m * ((fuse0 k)⁻¹ * m)⁻¹ := by group
  rw [this]
  exact M.mul_mem hm (M.inv_mem h2)

theorem conjSub_fuse0_ne_R0Y (hR : IsUniqueInvolution R0Y t0Y) {k : ℕ} (hk : k < 3) :
    conjSub (fuse0 k) R0Y ≠ R0Y := by
  intro h
  have h1 := (conjSub_R0Y_eq_iff hR).1 (h.trans (conjSub_one R0Y).symm)
  rw [fuse0_conj hk, one_mul, inv_one, mul_one] at h1
  exact cK_ne_one hk (mul_left_cancel (h1.trans (mul_one t0Y).symm))

theorem sandwich_R0Y (B : Set (Subgroup HY)) (N : Subgroup HY)
    (hR : IsUniqueInvolution R0Y t0Y) (hS : SandwichData (⊤ : Subgroup HY) R0Y t0Y B N) :
    B.ncard = 2 := by
  have hT : (⊤ : Subgroup HY) ⊓ Subgroup.centralizer ({t0Y} : Set HY) = T0Y := top_inf_eq _
  set M := blockStab (⊤ : Subgroup HY) B with hMdef
  have hM : T0Y ≤ M := hT ▸ hS.twins_le_blockStab
  have hMt : M ≠ ⊤ := hS.blockStab_ne
  have hov := overgroupY hM hMt
  have hBorb := hS.eq_orbit_blockStab
  have hNle : N ≤ T0Y := hT ▸ hS.le
  have hNn : (N.subgroupOf T0Y).Normal := hT ▸ hS.normal
  have h1 : (1 : HY) ∈ (⊤ : Subgroup HY) ⊓ Subgroup.centralizer ({t0Y} : Set HY) := one_mem _
  have hR0N : R0Y ≤ N := by
    have := hS.twins_le 1 h1
    rwa [conjSub_one] at this
  have hidx := hS.index
  rw [hT] at hidx
  have hT0 : Nat.card T0Y = 110592 := classPkg0Y.2.2.1
  have hmul : N.relIndex T0Y * Nat.card N = Nat.card T0Y := by
    have := Subgroup.relIndex_mul_card N T0Y
    rwa [inf_eq_left.2 hNle] at this
  rw [hT0] at hmul
  have hmemB : ∀ J, J ∈ B ↔ J = R0Y ∨ ∃ k < 3, fuse0 k ∈ M ∧ J = conjSub (fuse0 k) R0Y := by
    intro J
    rw [hBorb]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rcases hov m hm with h0 | ⟨k, hk, hkm⟩
      · left
        have h2 := conjSub_R0Y_eq_iff hR (a := m) (b := 1)
        rw [conjSub_one] at h2
        rw [h2, h0]
        group
      · right
        refine ⟨k, hk, fuse0_mem_of_conj hM hm hk hkm, ?_⟩
        rw [conjSub_R0Y_eq_iff hR, hkm, fuse0_conj hk]
    · rintro (rfl | ⟨k, hk, hkM, rfl⟩)
      · exact ⟨1, M.one_mem, conjSub_one _⟩
      · exact ⟨fuse0 k, hkM, rfl⟩
  by_cases hall : ∀ k < 3, fuse0 k ∈ M
  ·
    exfalso
    have hB4 : ∀ k < 3, conjSub (fuse0 k) R0Y ∈ B := fun k hk =>
      (hmemB _).2 (Or.inr ⟨k, hk, hall k hk, rfl⟩)
    have hfix := card_fixSet_le4 hS.mem hB4
    have hD : ∀ x : HY, x * t0Y * x⁻¹ ∈ N → x * t0Y * x⁻¹ = t0Y ∨
        ∃ k < 3, x * t0Y * x⁻¹ = t0Y * cK k := by
      intro x hx
      have := OmGen.conj_mem_of_blockStab_le hS hR le_rfl
        (Zt := {u | u = t0Y ∨ ∃ k < 3, u = t0Y * cK k}) (fun m hm => hov m hm)
        (Subgroup.mem_top x) hx
      exact this
    have hcard := card_le_of_avoid4 hNle hNn hR0N hD
    have : N.relIndex T0Y ≤ 6 := hidx.trans hfix
    nlinarith
  · push_neg at hall
    obtain ⟨k0, hk0, hk0M⟩ := hall
    by_cases hnone : ∀ k < 3, fuse0 k ∉ M
    ·
      exfalso
      have hfix := card_fixSet_le1 hS.mem
      have hD : ∀ x : HY, x * t0Y * x⁻¹ ∈ N → x * t0Y * x⁻¹ = t0Y := by
        intro x hx
        have := OmGen.conj_mem_of_blockStab_le hS hR le_rfl (Zt := {t0Y})
          (fun m hm => by
            rcases hov m hm with h0 | ⟨k, hk, hkm⟩
            · exact h0
            · exact absurd (fuse0_mem_of_conj hM hm hk hkm) (hnone k hk))
          (Subgroup.mem_top x) hx
        exact this
      have hcard := card_le_of_avoid1 hNle hNn hR0N hD
      have : N.relIndex T0Y ≤ 6912 := hidx.trans hfix
      nlinarith
    · push_neg at hnone
      obtain ⟨k1, hk1, hk1M⟩ := hnone
      have huniq : ∀ k < 3, fuse0 k ∈ M → k = k1 := by
        intro k hk hkM
        by_contra hne
        obtain ⟨k2, hk2, hprod⟩ := mul_cK_mem hk hk1 hne
        have hm : fuse0 k * fuse0 k1 ∈ M := M.mul_mem hkM hk1M
        have hswap : fuse0 k * (t0Y * cK k1) * (fuse0 k)⁻¹ =
            fuse0 k * t0Y * (fuse0 k)⁻¹ * cK k1 := by
          calc fuse0 k * (t0Y * cK k1) * (fuse0 k)⁻¹ = fuse0 k * t0Y * (cK k1 * (fuse0 k)⁻¹) := by
                group
            _ = fuse0 k * t0Y * ((fuse0 k)⁻¹ * cK k1) := by rw [cK_comm k1 (fuse0 k)⁻¹]
            _ = fuse0 k * t0Y * (fuse0 k)⁻¹ * cK k1 := by group
        have hconj : fuse0 k * fuse0 k1 * t0Y * (fuse0 k * fuse0 k1)⁻¹ = t0Y * cK k2 := by
          rw [show fuse0 k * fuse0 k1 * t0Y * (fuse0 k * fuse0 k1)⁻¹ =
              fuse0 k * (fuse0 k1 * t0Y * (fuse0 k1)⁻¹) * (fuse0 k)⁻¹ by group,
            fuse0_conj hk1, hswap, fuse0_conj hk, mul_assoc, hprod]
        have hk2M := fuse0_mem_of_conj hM hm hk2 hconj
        have hall3 : ∀ k' < 3, fuse0 k' ∈ M := by
          intro k' hk'
          have : k' = k ∨ k' = k1 ∨ k' = k2 := by
            have h01 : k ≠ k1 := hne
            have h02 : k2 ≠ k := by
              intro h
              rw [h] at hprod
              exact cK_ne_one hk1 (mul_left_cancel (hprod.trans (mul_one _).symm))
            have h12 : k2 ≠ k1 := by
              intro h
              rw [h] at hprod
              exact cK_ne_one hk (mul_right_cancel (hprod.trans (one_mul _).symm))
            omega
          rcases this with rfl | rfl | rfl
          · exact hkM
          · exact hk1M
          · exact hk2M
        exact hk0M (hall3 k0 hk0)
      have hB : B = {R0Y, conjSub (fuse0 k1) R0Y} := by
        ext J
        rw [hmemB]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro (h | ⟨k, hk, hkM, rfl⟩)
          · exact Or.inl h
          · right
            rw [huniq k hk hkM]
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨k1, hk1, hk1M, h⟩
      rw [hB, Set.ncard_pair (conjSub_fuse0_ne_R0Y hR hk1).symm]

theorem sandwichSizeTwoIn_HY : SandwichSizeTwoIn HY :=
  sandwichSizeTwoIn_of_ident R0Y t0Y coreData_identY sandwich_R0Y

theorem pairingIn_HY : PairingIn HY :=
  pairingIn_of_ident R0Y t0Y coreData_identY pairing_R0Y

theorem om2_proved : SandwichSizeTwoAt ModOm2 :=
  sandwichSizeTwoAt_of_equiv (sandwichSizeTwoAt_of_in sandwichSizeTwoIn_HY) hopfEquivY

theorem om2p_proved : PairingAt ModOm2 :=
  pairingAt_of_equiv (pairingAt_of_in pairingIn_HY) hopfEquivY

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

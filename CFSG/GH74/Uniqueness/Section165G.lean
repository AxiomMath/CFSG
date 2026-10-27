module

public import CFSG.GH74.Uniqueness.Section165B0

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec165

theorem exists_mem_ne_of_not_solvable
    (S : ZDSetup X Z M) (c : Ctx16 Z M) {w : X}
    (hw2 : orderOf w = 2) (hwM : ¬ centralizer ({w} : Set X) ≤ M) (hzw : c.z * w = w * c.z)
    (hns : ¬ Group.IsSolvable ↥(cenHull Z w)) :
    ∃ y ∈ Z, y ∈ cenHull Z w ∧ y ∈ M ∧ y ≠ c.z := by
  obtain ⟨-, -, n, hn, hcard⟩ := S.corollary713Extra (centralizer ({w} : Set X))
    (S.cor714_centralizer_ne_top hw2) hwM
    ⟨c.z, c.hz, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hzw, c.hzM⟩⟩ hns
  have h1 : 1 < (Z ∩ ((centralizer ({w} : Set X) ⊓ M : Subgroup X) : Set X)).ncard := by
    rw [hcard]
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨y, hy, hyz⟩ := Set.exists_ne_of_one_lt_ncard h1 c.z
  exact ⟨y, hy.1, subset_closure ⟨hy.1, (mem_inf.mp hy.2).1⟩, (mem_inf.mp hy.2).2, hyz⟩

theorem not_solvable_of_commute_t (h163 : Lemma163Stmt Z M) (c : Conf16 Z M) {w : X}
    (hwM : w ∈ M) (hw2 : orderOf w = 2) (hwt : w * c.t = c.t * w) :
    ¬ Group.IsSolvable ↥(cenHull Z w) := fun hsol =>
  c.htM ((h163 c).2.2.2 w hwM hw2 hsol (mem_centralizer_singleton_iff.mpr hwt.symm))

theorem false_of_kGrp_le_B0
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M) (c : Conf16 Z M)
    (hK : kGrp M c.t ≤ c.B0) : False := by
  have hL : lSubgroup M c.z c.t ≤ c.B0 :=
    sup_le (sup_le (zpowers_le.mpr (Sec164.z_mem_B0 c)) (zpowers_le.mpr (Sec164.t_mem_B0 c))) hK
  rw [h121 c.t c.z c.ht c.htM c.hz c.hzM c.hD] at hL
  apply S.cor714_centralizer_ne_top c.hu2
  rw [eq_top_iff]
  exact hL.trans (Sec164.B0_le_B c)

theorem kGrp_inf_facts (S : ZDSetup X Z M) (c : Ctx16 Z M) {w : X} (hwt : w * c.t = c.t * w) :
    centralizer ({w} : Set X) ⊓ kGrp M c.t ≤ M ⊓ conjugate M c.t ∧
      Odd (Nat.card ↥(centralizer ({w} : Set X) ⊓ kGrp M c.t)) ∧
      c.t ∈ normalizer ((centralizer ({w} : Set X) ⊓ kGrp M c.t : Subgroup X) : Set X) := by
  obtain ⟨hKodd, htK, -⟩ := commutator_zpowers_kGrp M S.invariant c.ht
  exact ⟨inf_le_right.trans (Sec164.kGrp_le_D S.invariant c.ht),
    Odd.of_dvd_nat hKodd (card_dvd_of_le inf_le_right),
    Sec164.mem_normalizer_inf (Sec164.mem_normalizer_centralizer hwt.symm) htK⟩

theorem case_16G
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (h163 : Lemma163Stmt Z M)
    (c : Conf16 Z M) {w : X} (hwD : w ∈ c.D) (hw2 : orderOf w = 2) (huw : c.u * w = w * c.u)
    (hwt : w * c.t = c.t * w) (hwz : w * c.z = c.z * w) :
    ⁅zpowers c.t, centralizer ({w} : Set X) ⊓ kGrp M c.t⁆ ≤ c.B0 ∨
      ∃ huN : c.u ∈ normalizer (cenHull Z w : Set X), ∃ k : ℕ, 1 ≤ k ∧
        Bender.BenderType ↥(cenHull Z w) (2 * k) 1 1 ∧
        (¬ ∃ g : ↥(cenHull Z w), ∀ x : ↥(cenHull Z w), conjAut huN x = g * x * g⁻¹) ∧
        Nonempty (Bender.autFixed (conjAut huN) ≃* CFSG.Theory.Comparator.PSL2Model k) := by
  have hwM : w ∈ M := (mem_inf.mp hwD).1
  have hns := not_solvable_of_commute_t h163 c hwM hw2 hwt
  have hCM : ¬ centralizer ({w} : Set X) ≤ M := fun h =>
    c.htM (h (mem_centralizer_singleton_iff.mpr hwt.symm))
  have hne := exists_mem_ne_of_not_solvable S c.toCtx16 hw2 hCM hwz.symm hns
  obtain ⟨n', i', e', hBw⟩ := S.benderSub_exists (S.cor714_centralizer_ne_top hw2) hCM
    ⟨c.z, c.hz, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hwz.symm, c.hzM⟩⟩ hns
  have hzF : c.z ∈ cenHull Z w :=
    subset_closure ⟨c.hz, mem_centralizer_singleton_iff.mpr hwz.symm⟩
  have htF : c.t ∈ cenHull Z w :=
    subset_closure ⟨c.ht, mem_centralizer_singleton_iff.mpr hwt.symm⟩
  obtain ⟨hA, hAodd, htA⟩ := kGrp_inf_facts S c.toCtx16 hwt
  have hle := Sec164.commutator_le_fZero S h162 c.toCtx16 hw2 hwz.symm hwt.symm hne hA inf_le_left
    hAodd htA
  have huC : c.u ∈ centralizer ({w} : Set X) := mem_centralizer_singleton_iff.mpr huw
  have huN : c.u ∈ normalizer (cenHull Z w : Set X) := le_normalizer_zHull S.invariant _ huC
  have hut : c.u * c.t = c.t * c.u := (mem_centralizer_singleton_iff.mp c.ht_B).symm
  have huz : c.u * c.z = c.z * c.u := (mem_centralizer_singleton_iff.mp (Sec164.z_mem_B c)).symm
  have hfix : ∀ x : ↥(cenHull Z w), (x : X) = c.z ∨ (x : X) = c.t → conjAut huN x = x := by
    rintro x (hx | hx)
    · exact conjAut_fix huN (by rw [hx]; exact huz)
    · exact conjAut_fix huN (by rw [hx]; exact hut)
  have hB0of : ∀ y ∈ Z, y * c.u = c.u * y → y ∈ c.B0 := fun y hyZ hyu =>
    subset_closure ⟨hyZ, mem_centralizer_singleton_iff.mpr hyu⟩
  obtain ⟨m, hm, ⟨hF, hBT⟩ | ⟨-, -, -, hb3⟩⟩ :=
    h162 c.toCtx16 (cenHull Z w) (Sec164.cenHull_ne_top S hw2) hzF htF hne (zHull_zHull _)
  swap
  · left
    refine hle.trans ?_
    have hzh : zHull Z (M ⊓ cenHull Z w) ≤ c.B0 := by
      refine (closure_le _).mpr ?_
      rintro g ⟨hgZ, hgMF⟩
      have hgF := (mem_inf.mp hgMF).2
      have hgf : g ∈ fZero Z M (cenHull Z w) c.t :=
        subset_closure (Or.inl (subset_closure ⟨hgZ, hgMF⟩))
      have h1 := congrArg Subtype.val (hb3 (conjAut huN) (conjAut_mul_self huN c.u_mul_self) hfix
        ⟨g, hgF⟩ hgf)
      rw [conjAut_apply] at h1
      refine hB0of g hgZ ?_
      calc g * c.u = (c.u * g * c.u⁻¹) * c.u := by rw [h1]
        _ = c.u * g := by group
    show closure ((zHull Z (M ⊓ cenHull Z w) : Set X) ∪ {c.t}) ≤ c.B0
    refine (closure_le _).mpr ?_
    rintro y (hy | rfl)
    · exact hzh hy
    · exact Sec164.t_mem_B0 c
  · by_cases huF : c.u ∈ centralizer (cenHull Z w : Set X)
    · left
      refine hle.trans ?_
      rw [hF]
      refine (closure_le _).mpr ?_
      rintro g ⟨hgZ, hgC⟩
      have hgF : g ∈ cenHull Z w := subset_closure ⟨hgZ, hgC⟩
      exact hB0of g hgZ ((mem_centralizer_iff.mp huF) g hgF)
    · right
      rcases hBT with hL | hSz
      · have hni := not_inner_conjAut S hL hBw.invol c.hz c.hzM hzF c.htM htF huN c.u_mul_self
          huz hut huF
        obtain ⟨k, hmk, hiso, -⟩ :=
          hL.fixed_linear (conjAut huN) (conjAut_mul_self huN c.u_mul_self) hni
        exact ⟨huN, k, by omega, hmk ▸ hL, hni, hiso⟩
      · exfalso
        obtain ⟨g, -, hg⟩ := hSz.exists_inner_of_sq_eq_one_suzuki (conjAut huN)
          (conjAut_mul_self huN c.u_mul_self)
        exact not_inner_conjAut S hSz hBw.invol c.hz c.hzM hzF c.htM htF huN c.u_mul_self huz hut
          huF ⟨g, hg⟩

theorem exists_16H
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M) (h161 : Lemma161Stmt Z M)
    (h162 : Lemma162Stmt Z M) (h163 : Lemma163Stmt Z M) (c : Conf16 Z M) {v : X}
    (hvD : v ∈ c.D) (hv2 : v * v = 1) (hv1 : v ≠ 1) (hvu : v ≠ c.u)
    (huv : c.u * v = v * c.u) (hvt : v * c.t = c.t * v) (hvz : v * c.z = c.z * v) :
    ∃ w : X, w ∈ c.D ∧ w * w = 1 ∧ w ≠ 1 ∧ w ≠ c.u ∧ c.u * w = w * c.u ∧ w * c.t = c.t * w ∧
      w * c.z = c.z * w ∧
      ∃ huN : c.u ∈ normalizer (cenHull Z w : Set X), ∃ k : ℕ, 1 ≤ k ∧
        Bender.BenderType ↥(cenHull Z w) (2 * k) 1 1 ∧
        (¬ ∃ g : ↥(cenHull Z w), ∀ x : ↥(cenHull Z w), conjAut huN x = g * x * g⁻¹) ∧
        Nonempty (Bender.autFixed (conjAut huN) ≃* CFSG.Theory.Comparator.PSL2Model k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hut : c.u * c.t = c.t * c.u := (mem_centralizer_singleton_iff.mp c.ht_B).symm
  have huz : c.u * c.z = c.z * c.u := (mem_centralizer_singleton_iff.mp (Sec164.z_mem_B c)).symm
  have huvD : c.u * v ∈ c.D := mul_mem c.hu hvD
  have huv2 : (c.u * v) * (c.u * v) = 1 := by
    calc (c.u * v) * (c.u * v) = c.u * (v * c.u) * v := by group
      _ = c.u * (c.u * v) * v := by rw [huv]
      _ = (c.u * c.u) * (v * v) := by group
      _ = 1 := by rw [c.u_mul_self, hv2, one_mul]
  have huv1 : c.u * v ≠ 1 := fun h => hvu (by
    have := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right c.u_mul_self])
  have huvu : c.u * v ≠ c.u := fun h => hv1 (by
    have := congrArg (c.u⁻¹ * ·) h
    simpa using this)
  have hu_uv : c.u * (c.u * v) = (c.u * v) * c.u := by
    calc c.u * (c.u * v) = c.u * (v * c.u) := by rw [huv]
      _ = (c.u * v) * c.u := by group
  have huvt : (c.u * v) * c.t = c.t * (c.u * v) := by
    calc (c.u * v) * c.t = c.u * (v * c.t) := by group
      _ = c.u * (c.t * v) := by rw [hvt]
      _ = (c.u * c.t) * v := by group
      _ = (c.t * c.u) * v := by rw [hut]
      _ = c.t * (c.u * v) := by group
  have huvz : (c.u * v) * c.z = c.z * (c.u * v) := by
    calc (c.u * v) * c.z = c.u * (v * c.z) := by group
      _ = c.u * (c.z * v) := by rw [hvz]
      _ = (c.u * c.z) * v := by group
      _ = (c.z * c.u) * v := by rw [huz]
      _ = c.z * (c.u * v) := by group
  have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  have huvo : orderOf (c.u * v) = 2 := orderOf_eq_prime (by rw [sq]; exact huv2) huv1
  rcases case_16G S h162 h163 c hvD hvo huv hvt hvz with hv' | hv'
  · rcases case_16G S h162 h163 c huvD huvo hu_uv huvt huvz with huv' | huv'
    · exfalso
      have hu' : ⁅zpowers c.t, centralizer ({c.u} : Set X) ⊓ kGrp M c.t⁆ ≤ c.B0 := by
        obtain ⟨y, hy, hyz⟩ := Sec164.exists_mem_gamma_ne S c
        obtain ⟨hA, hAodd, htA⟩ := kGrp_inf_facts S c.toCtx16 hut
        have h := Sec164.commutator_le_fZero S h162 c.toCtx16 c.hu2
          (mem_centralizer_singleton_iff.mp (Sec164.z_mem_B c))
          (mem_centralizer_singleton_iff.mp c.ht_B)
          ⟨y, hy.1, subset_closure ⟨hy.1, (mem_inf.mp hy.2).1⟩, (mem_inf.mp hy.2).2, hyz⟩
          hA inf_le_left hAodd htA
        rw [Sec164.fZero_B0] at h
        exact h.trans (Sec164.Bzero_le_B0 c)
      have hW4 : Nat.card (fourSub c.u v c.u_mul_self hv2 huv) = 4 :=
        card_fourSub c.u_ne_one hv1 (Ne.symm hvu)
      have hWD : fourSub c.u v c.u_mul_self hv2 huv ≤ c.D := fourSub_le c.hu hvD
      have hWt : fourSub c.u v c.u_mul_self hv2 huv ≤ centralizer ({c.t} : Set X) :=
        fourSub_le (mem_centralizer_singleton_iff.mpr hut) (mem_centralizer_singleton_iff.mpr hvt)
      have hWK : fourSub c.u v c.u_mul_self hv2 huv ≤ normalizer (kGrp M c.t : Set X) :=
        fun w hw => Sec164.mem_normalizer_kGrp (hWD hw) (mem_centralizer_singleton_iff.mp (hWt hw))
      have hKgen := h161 c.toCtx16 _ hW4 mul_self_of_mem_fourSub hWK hWt
      apply false_of_kGrp_le_B0 S h121 c
      rw [hKgen]
      refine iSup₂_le ?_
      rintro w ⟨hwW, hw1⟩
      rcases hwW with rfl | rfl | rfl | rfl
      · exact absurd (Set.mem_singleton _) hw1
      · exact hu'
      · exact hv'
      · exact huv'
    · exact ⟨c.u * v, huvD, huv2, huv1, huvu, hu_uv, huvt, huvz, huv'⟩
  · exact ⟨v, hvD, hv2, hv1, hvu, huv, hvt, hvz, hv'⟩

end Sec165

end CFSG.GH74.Uniqueness

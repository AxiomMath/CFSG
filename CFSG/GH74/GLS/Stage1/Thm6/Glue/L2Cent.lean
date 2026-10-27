module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2P

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
  {F : Type} [Field F] [Finite F] {e : ↥Kb ≃* IVK.L2 F} {N : IVK.L2Notation e} {T : Subgroup G}

theorem dvd_two_of_dvd_pow_two_of_dvd_two_mul {d M a : ℕ} (hM : Odd M) (h1 : d ∣ 2 ^ a)
    (h2 : d ∣ 2 * M) : d ∣ 2 := by
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  by_cases hb : b ≤ 1
  · calc 2 ^ b ∣ 2 ^ 1 := pow_dvd_pow 2 hb
      _ = 2 := by norm_num
  · exfalso
    have h4 : 2 ^ 2 ∣ 2 * M := (pow_dvd_pow 2 (by omega)).trans h2
    have : 2 ∣ M := by
      have : 2 * 2 ∣ 2 * M := by simpa using h4
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 this
    exact (Nat.not_even_iff_odd.2 hM) (even_iff_two_dvd.2 this)

variable [Finite G]

theorem Ox_odd (x : G) : ¬ 2 ∣ Nat.card (Ox x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := pPrimeCore_coprime_card (p := 2) (G := ↥(Cx x))
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 this

omit [Kb.Normal] in
theorem NP_dihedral (hF : IVK.L2Field F) (h12c : IVK.IVK_1_2c) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥N.P ≃* DihedralGroup (2 ^ m)) := by
  obtain ⟨n, hn⟩ := h12c F hF ↥Kb e N
  obtain ⟨m, hm, -, he⟩ := isDihedralTwoGroup_equiv hn
  exact ⟨m, hm, he⟩

omit [Kb.Normal] [Finite G] in
theorem NP_mem_iff {a : MulAut ↥Kb} :
    a ∈ N.P ↔ a ∈ (N.T : Subgroup (MulAut ↥Kb)) ∧ a ∈ IVK.innAut ↥Kb := Iff.rfl

theorem cent_decomp (h : SitFacts x Kb e N T) (h12c : IVK.IVK_1_2c) (h14j : IVK.IVK_1_4j) {t : G}
    (htC : t ∈ Cx x) (hcent : ∀ p ∈ Pg x Kb T, t * p = p * t) :
    ∃ z₁ ∈ N.P, z₁ * z₁ = 1 ∧ ∃ e₁ ∈ IVK.fieldAutSub e, ∃ M : ℕ, Odd M ∧ orderOf e₁ ∣ 2 * M ∧
      z₁ * e₁ = e₁ * z₁ ∧ phig x Kb t = z₁ * e₁ := by
  obtain ⟨E, -, hEF, ⟨M, hModd, hEcard⟩, hcentN, -, -⟩ := h14j F h.hF ↥Kb e N
  have hcN : phig x Kb t ∈ Subgroup.centralizer (N.P : Set (MulAut ↥Kb)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨p, hp, rfl⟩ := (h.hPN a).1 ha
    have hpC : p ∈ Cx x := h.T_le_C hp.1
    rw [← phig_mul x Kb hpC htC, ← phig_mul x Kb htC hpC, hcent p hp]
  rw [hcentN] at hcN
  set Z : Subgroup (MulAut ↥Kb) := (Subgroup.center ↥N.P).map N.P.subtype with hZ
  have hZP : Z ≤ N.P := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hEc : ∀ b ∈ E, ∀ a ∈ N.P, b * a = a * b := by
    intro b hb a ha
    have : b ∈ Subgroup.centralizer (N.P : Set (MulAut ↥Kb)) := by
      rw [hcentN]; exact mem_sup_right hb
    exact ((Subgroup.mem_centralizer_iff.1 this) a ha).symm
  have hcomm : ∀ a ∈ Z, ∀ b ∈ E, a * b = b * a := fun a ha b hb => (hEc b hb a (hZP ha)).symm
  obtain ⟨z₁, hz₁, e₁, he₁, hte⟩ := (mem_sup_iff_of_comm hcomm).1 hcN
  refine ⟨z₁, hZP hz₁, ?_, e₁, hEF he₁, M, hModd, ?_, hcomm z₁ hz₁ e₁ he₁, hte⟩
  · obtain ⟨z₀, hz₀, rfl⟩ := hz₁
    obtain ⟨m', hm', ⟨e₀⟩⟩ := NP_dihedral (e := e) (N := N) h.hF h12c
    have hk : 2 ∣ 2 ^ m' := dvd_pow_self 2 (by omega)
    have : NeZero (2 ^ m') := ⟨by positivity⟩
    have h0 : z₀ * z₀ = 1 := Dihedral.central_sq_of_equiv e₀ hk
      (fun y => ((Subgroup.mem_center_iff.1 hz₀) y).symm)
    have := congrArg Subtype.val h0
    simpa using this
  · have h1 := Subgroup.orderOf_dvd_natCard E he₁
    rcases hEcard with hc | hc
    · rw [hc] at h1; exact h1.trans (Dvd.intro_left 2 rfl)
    · rw [hc] at h1; exact h1

theorem ip_cent_P_exp (h : SitFacts x Kb e N T) (h12c : IVK.IVK_1_2c) (h14j : IVK.IVK_1_4j) :
    IP_cent_P_exp T (Pg x Kb T) (Qg x Kb T) := by
  intro t ht hcent
  have htC : t ∈ Cx x := h.T_le_C ht
  obtain ⟨z₁, -, hz₁2, e₁, -, M, hM, hord, hzc, hte⟩ := cent_decomp h h12c h14j htC hcent
  obtain ⟨n, hn⟩ := h.sylow.2.1 ⟨t, ht⟩
  have htn : t ^ (2 ^ (n + 1)) = 1 := by
    have : t ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    rw [pow_succ, pow_mul, this, one_pow]
  have h1 : (phig x Kb t) ^ (2 ^ (n + 1)) = 1 := by
    rw [← phig_pow x Kb htC, htn, phig_one]
  rw [hte, (commute_of_mul_eq hzc).mul_pow] at h1
  have hz1 : z₁ ^ (2 ^ (n + 1)) = 1 := by
    rw [pow_succ', pow_mul, pow_two, hz₁2, one_pow]
  rw [hz1, one_mul] at h1
  have hd : orderOf e₁ ∣ 2 :=
    dvd_two_of_dvd_pow_two_of_dvd_two_mul hM (orderOf_dvd_of_pow_eq_one h1) hord
  have he2 : e₁ ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hd
  refine ⟨T.mul_mem ht ht, mul_mem htC htC, ?_⟩
  rw [phig_mul x Kb htC htC, hte]
  calc z₁ * e₁ * (z₁ * e₁) = z₁ * z₁ * (e₁ * e₁) := by
        rw [mul_assoc, ← mul_assoc e₁ z₁, ← hzc]; simp only [mul_assoc]
    _ = 1 := by rw [hz₁2, ← pow_two, he2, mul_one]

theorem ip_cent_Rd (h : SitFacts x Kb e N T) (h12c : IVK.IVK_1_2c) (h14j : IVK.IVK_1_4j) :
    IP_cent_Rd (Pg x Kb T) (Qg x Kb T) (Rdg x Kb e T) := by
  intro d hd hcent
  obtain ⟨hdT, hdC, hdD⟩ := hd
  obtain ⟨z₁, hz₁, -, e₁, he₁, -, -, -, -, hde⟩ := cent_decomp h h12c h14j hdC hcent
  have hz₁D : z₁ ∈ IVK.innDiagSub e := IVK.innAut_le_innDiagSub e ((NP_mem_iff.1 hz₁).2)
  have he₁D : e₁ ∈ IVK.innDiagSub e := by
    have : e₁ = z₁⁻¹ * phig x Kb d := by rw [hde]; group
    rw [this]; exact mul_mem (inv_mem hz₁D) hdD
  have he₁1 : e₁ = 1 := by
    have : e₁ ∈ IVK.innDiagSub e ⊓ IVK.fieldAutSub e := ⟨he₁D, he₁⟩
    rw [IVK.innDiagSub_inf_fieldAutSub e] at this
    exact this
  rw [he₁1, mul_one] at hde
  obtain ⟨p, hp, hpd⟩ := (h.hPN z₁).1 hz₁
  have hpC : p ∈ Cx x := h.T_le_C hp.1
  have hq : p⁻¹ * d ∈ Qg x Kb T := ⟨T.mul_mem (T.inv_mem hp.1) hdT, mul_mem (inv_mem hpC) hdC, by
    rw [phig_mul x Kb (inv_mem hpC) hdC, phig_inv x Kb hpC, hpd, hde, inv_mul_cancel]⟩
  have hdd : d = p * (p⁻¹ * d) := by group
  rw [hdd]
  exact mul_mem (mem_sup_left hp) (mem_sup_right hq)

theorem ip_Rd_cyclic (h : SitFacts x Kb e N T) (h12e : IVK.IVK_1_2e) :
    IP_Rd_cyclic T (Rdg x Kb e T) := by
  have hD : (IVK.innDiagSub e).Normal := IVK.innDiagSub_normal e
  have hcycFl : IsCyclic ↥(IVK.fieldAutSub e) := (h12e F h.hF ↥Kb e).1
  let π : MulAut ↥Kb →* MulAut ↥Kb ⧸ IVK.innDiagSub e := QuotientGroup.mk' _
  have hsurj : Function.Surjective (π.comp (IVK.fieldAutSub e).subtype) := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have ha : a ∈ IVK.innDiagSub e ⊔ IVK.fieldAutSub e := by
      rw [IVK.innDiagSub_sup_fieldAutSub e]; exact Subgroup.mem_top a
    obtain ⟨d, hd, f, hf, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 ha
    refine ⟨⟨f, hf⟩, ?_⟩
    show (QuotientGroup.mk f : MulAut ↥Kb ⧸ IVK.innDiagSub e) = QuotientGroup.mk (d * f)
    rw [QuotientGroup.eq]
    have := hD.conj_mem d hd f⁻¹
    simpa [mul_assoc] using this
  have hcycQ : IsCyclic (MulAut ↥Kb ⧸ IVK.innDiagSub e) := isCyclic_of_surjective _ hsurj
  let χ : ↥T →* MulAut ↥Kb ⧸ IVK.innDiagSub e :=
    π.comp ((phiC x Kb).comp (Subgroup.inclusion h.T_le_C))
  obtain ⟨g, hg⟩ := (inferInstance : IsCyclic ↥χ.range).exists_generator
  obtain ⟨b, hb⟩ := g.2
  refine ⟨b.1, b.2, fun t ht => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨χ ⟨t, ht⟩, ⟨_, rfl⟩⟩)
  refine ⟨k, ?_⟩
  have hu : χ ((b ^ k)⁻¹ * ⟨t, ht⟩) = 1 := by
    rw [map_mul, map_inv, map_zpow, hb, mul_eq_one_iff_inv_eq, inv_inv]
    have := congrArg Subtype.val hk
    simpa using this
  have htC := h.T_le_C ht
  have hbC := h.T_le_C b.2
  refine ⟨T.mul_mem (T.inv_mem (T.zpow_mem b.2 k)) ht, mul_mem (inv_mem (zpow_mem hbC k)) htC, ?_⟩
  have hmem : (⟨(b.1 ^ k)⁻¹ * t, T.mul_mem (T.inv_mem (T.zpow_mem b.2 k)) ht⟩ : ↥T) =
      (b ^ k)⁻¹ * ⟨t, ht⟩ := rfl
  have := (QuotientGroup.eq_one_iff _).1 hu
  rw [phig_of_mem x Kb (mul_mem (inv_mem (zpow_mem hbC k)) htC)]
  exact this

theorem ip_P_conj (h : SitFacts x Kb e N T) (h12g : IVK.IVK_1_2g) {z : G}
    (hz : HZ T (Pg x Kb T) z) : IP_P_conj x z (Pg x Kb T) := by
  intro a ha ha2 ha1
  have hzP := hz.z_mem_P
  have haC : a ∈ Cx x := ((mem_Kg x Kb).1 ha.2).1
  have hzC : z ∈ Cx x := ((mem_Kg x Kb).1 hzP.2).1
  have hphia : phig x Kb a ∈ N.P := (h.hPN _).2 ⟨a, ha, rfl⟩
  have hphiz : phig x Kb z ∈ N.P := (h.hPN _).2 ⟨z, hzP, rfl⟩
  have hord : ∀ g ∈ Pg x Kb T, g * g = 1 → g ≠ 1 → orderOf (phig x Kb g) = 2 := by
    intro g hg hg2 hg1
    have hgC : g ∈ Cx x := ((mem_Kg x Kb).1 hg.2).1
    refine orderOf_eq_prime ?_ ?_
    · rw [← phig_pow x Kb hgC, pow_two, hg2, phig_one]
    · intro h1
      apply hg1
      apply h.phig_inj_P hg (Pg x Kb T).one_mem
      rw [h1, phig_one]
  obtain ⟨c, hc, hca⟩ := (h12g F h.hF ↥Kb e N).1 _ hphia _ hphiz (hord a ha ha2 ha1)
    (hord z hzP hz.z_sq hz.z_ne_one)
  obtain ⟨k, rfl⟩ := hc
  have hconj := IVK.conj_injective_of_L2 e
  set ka : ↥Kb := ⟨pr x a, ((mem_Kg x Kb).1 ha.2).2⟩ with hka
  set kz : ↥Kb := ⟨pr x z, ((mem_Kg x Kb).1 hzP.2).2⟩ with hkz
  have h1 : k * ka * k⁻¹ = kz := by
    apply hconj
    rw [map_mul, map_mul, map_inv, ← phig_eq_conj x Kb ha.2, ← phig_eq_conj x Kb hzP.2]
    exact hca
  have h2 : (k : CentralizerBar x) * pr x a * (k : CentralizerBar x)⁻¹ = pr x z := by
    have := congrArg Subtype.val h1
    simpa [hka, hkz] using this
  have hbar : IsConj (QuotientGroup.mk (⟨a, haC⟩ : ↥(Cx x)) : CentralizerBar x)
      (QuotientGroup.mk (⟨z, hzC⟩ : ↥(Cx x)) : CentralizerBar x) := by
    rw [isConj_iff]
    refine ⟨(k : CentralizerBar x), ?_⟩
    rw [← pr_of_mem x haC, ← pr_of_mem x hzC]
    exact h2
  obtain ⟨c, hc⟩ := exists_conj_of_conj_mk (Ox x) (Ox_odd x) (a := ⟨a, haC⟩) (z := ⟨z, hzC⟩)
    (Subtype.ext ha2) (Subtype.ext hz.z_sq) hbar
  exact ⟨c.1, c.2, congrArg Subtype.val hc⟩

end CFSG.GH74.GLS.Stage1.Thm6.Glue

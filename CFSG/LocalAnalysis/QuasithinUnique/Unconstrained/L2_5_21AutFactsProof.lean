module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21AutFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinL2p
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary

public section

namespace CFSG.QuasithinUnique.Out21

open CFSG.Open CFSG.GorensteinWalter

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem congr_mem_innerAut_iff (e : X ≃* Y) (α : MulAut X) :
    MulAut.congr e α ∈ innerAut Y ↔ α ∈ innerAut X := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    ext x
    have h1 : y * e x * y⁻¹ = e (α x) := by
      have := congrArg (fun φ : MulAut Y => φ (e x)) hy
      simpa [congr_apply', MulAut.conj_apply] using this
    apply e.injective
    simpa [MulAut.conj_apply] using h1
  · rintro ⟨x, hx⟩
    refine ⟨e x, ?_⟩
    ext y
    have : (MulAut.congr e α) y = e (α (e.symm y)) := rfl
    rw [this, ← hx]
    simp [MulAut.conj_apply]

end Transport

section PSL2

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

theorem even_card_psl2 (K : Type) [Field K] [Finite K] (hodd : IsOddPrimePower (Nat.card K)) :
    Even (Nat.card (PSL2 K)) := by
  rw [psl2_card_formula K hodd]
  have hQodd : Odd (Nat.card K) := by
    obtain ⟨r, n, hr, hrodd, hn, hQ⟩ := hodd
    rw [hQ]
    exact hrodd.pow
  obtain ⟨k, hk⟩ := hQodd
  have h1 : Nat.card K ^ 2 - 1 = 2 * (2 * k ^ 2 + 2 * k) := by
    have : Nat.card K ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by rw [hk]; ring
    omega
  have h2 : Nat.card K * (Nat.card K ^ 2 - 1) / 2 = Nat.card K * (2 * k ^ 2 + 2 * k) := by
    rw [h1, show Nat.card K * (2 * (2 * k ^ 2 + 2 * k)) =
      2 * (Nat.card K * (2 * k ^ 2 + 2 * k)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [h2]
  exact ⟨Nat.card K * (k ^ 2 + k), by ring⟩

theorem not_sq_dvd_card_psl2 (hp7 : 7 ≤ p) (hF : Nat.card F = p) :
    ¬ p ^ 2 ∣ Nat.card (PSL2 F) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [psl2_card_formula F (hodd_of hp7 hF), hF]
  obtain ⟨k, hk⟩ := hpodd
  have h1 : p ^ 2 - 1 = 2 * (2 * k ^ 2 + 2 * k) := by
    have : p ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by rw [hk]; ring
    omega
  have h2 : p * (p ^ 2 - 1) / 2 = p * (2 * k ^ 2 + 2 * k) := by
    rw [h1, show p * (2 * (2 * k ^ 2 + 2 * k)) = 2 * (p * (2 * k ^ 2 + 2 * k)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [h2]
  intro h
  have h3 : p ∣ 2 * k ^ 2 + 2 * k := by
    have : p * p ∣ p * (2 * k ^ 2 + 2 * k) := by rwa [← pow_two]
    exact (Nat.mul_dvd_mul_iff_left (Fact.out : p.Prime).pos).mp this
  have h4 : p ∣ p ^ 2 - 1 := by
    rw [h1]
    exact Dvd.dvd.mul_left h3 2
  have h5 : p ∣ 1 := by
    have h6 : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
    have h7 : p ^ 2 - 1 + 1 = p ^ 2 :=
      Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
    exact (Nat.dvd_add_right h4).mp (h7 ▸ h6)
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h5)

theorem sq_inner_psl2 (hp7 : 7 ≤ p) (hF : Nat.card F = p) (α : MulAut (PSL2 F)) :
    α * α ∈ innerAut (PSL2 F) := by
  have := finite_pgl2 (F := F)
  rw [mem_innerAut_iff hp7 hF, map_mul]
  exact Subgroup.mul_self_mem_of_index_two (pgl2_psl2Range_index_eq_two F (hodd_of hp7 hF)) _

theorem outer_conj_psl2 (hp7 : 7 ≤ p) (hF : Nat.card F = p) (α β : MulAut (PSL2 F))
    (hα2 : α * α = 1) (hβ2 : β * β = 1) (hα : α ∉ innerAut (PSL2 F))
    (hβ : β ∉ innerAut (PSL2 F)) : ∃ φ : MulAut (PSL2 F), φ * α * φ⁻¹ = β := by
  have := finite_pgl2 (F := F)
  set e := autEquiv hp7 hF with he
  have hodd := hodd_of hp7 hF
  have hcard := three_lt hp7 hF
  set J : Subgroup (PGL2 F) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hJdef
  have hJcomm : commutator (PGL2 F) = J :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three F hodd hcard
  set g := e.symm α with hg
  set h := e.symm β with hh
  have hg2 : g * g = 1 := by
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, hα2, map_one]
  have hh2 : h * h = 1 := by
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, hβ2, map_one]
  have hgJ : g ∉ J := fun h' => hα ((mem_innerAut_iff hp7 hF α).mpr h')
  have hhJ : h ∉ J := fun h' => hβ ((mem_innerAut_iff hp7 hF β).mpr h')
  have hg1 : g ≠ 1 := fun h' => hgJ (h' ▸ J.one_mem)
  have hh1 : h ≠ 1 := fun h' => hhJ (h' ▸ J.one_mem)
  have hconj : IsConj g h :=
    pgl2_outer_involutions_conjugate F hodd hcard ⟨hg1, by rw [pow_two]; exact hg2⟩
      ⟨hh1, by rw [pow_two]; exact hh2⟩ (by rw [hJcomm]; exact hgJ) (by rw [hJcomm]; exact hhJ)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  refine ⟨e c, ?_⟩
  apply e.symm.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, ← hg, ← hh, ← hc]

theorem odd_pair_psl2
    (hp7 : 7 ≤ p) (hF : Nat.card F = p) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {a b : PSL2 F} (ha : orderOf a = q) (hb : orderOf b = q) (hab : a * b = b * a) :
    b ∈ Subgroup.zpowers a := by
  classical
  by_contra hnot
  have : Fact q.Prime := ⟨hq⟩
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have haq : a ^ q = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hbq : b ^ q = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hcommute : Commute a b := hab
  set H : Subgroup (PSL2 F) := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hH
  have hHq : ∀ h ∈ H, h ^ q = 1 := by
    intro h hh
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup_of_commute (A := Subgroup.zpowers a)
      (B := Subgroup.zpowers b) (fun x hx y hy => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (hcommute.zpow_zpow i j).eq) hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute (a ^ i) (b ^ j) := hcommute.zpow_zpow i j
    rw [hc.mul_pow]
    have h1 : (a ^ i) ^ q = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, haq, one_zpow]
    have h2 : (b ^ j) ^ q = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbq, one_zpow]
    rw [h1, h2, one_mul]
  have hHpg : IsPGroup q ↥H := fun h => ⟨1, by
    apply Subtype.ext
    simpa using hHq h h.2⟩
  obtain ⟨k, hk⟩ := hHpg.exists_card_eq
  have hzcard : Nat.card ↥(Subgroup.zpowers a) = q := by rw [Nat.card_zpowers, ha]
  have hk2 : 2 ≤ k := by
    by_contra hk2
    push Not at hk2
    have hle : Nat.card ↥H ≤ q := by
      rw [hk]
      calc q ^ k ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos (by omega)
        _ = q := pow_one q
    have hzeq : Subgroup.zpowers a = H :=
      Subgroup.eq_of_le_of_card_ge (le_sup_left : Subgroup.zpowers a ≤ H) (by rw [hzcard]; exact hle)
    apply hnot
    rw [hzeq]
    exact (le_sup_right : Subgroup.zpowers b ≤ H) (Subgroup.mem_zpowers b)
  have hdvdH : Nat.card ↥H ∣ Nat.card (PSL2 F) := Subgroup.card_subgroup_dvd_card H
  have hqk : q ^ 2 ≤ Nat.card ↥H := by
    rw [hk]
    exact Nat.pow_le_pow_right hq.pos hk2
  have hqk2 : 4 ≤ Nat.card ↥H := le_trans (by nlinarith [hq.two_le]) hqk
  have hpH : ¬ p ∣ Nat.card ↥H := by
    intro hpd
    have hpq : p = q :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).mp
        (Nat.Prime.dvd_of_dvd_pow (Fact.out : p.Prime) (hk ▸ hpd))
    subst hpq
    exact not_sq_dvd_card_psl2 hp7 hF ((pow_dvd_pow p hk2).trans (hk ▸ hdvdH))
  have hcyc : IsCyclic ↥H → False := by
    intro hc
    obtain ⟨g, hg⟩ := hc.exists_generator
    have hgq : g ^ q = 1 := by
      apply Subtype.ext
      simpa using hHq g g.2
    have hord : orderOf g = Nat.card ↥H := orderOf_eq_card_of_forall_mem_zpowers hg
    have hdvd : Nat.card ↥H ∣ q := hord ▸ orderOf_dvd_of_pow_eq_one hgq
    have h1 : Nat.card ↥H ≤ q := Nat.le_of_dvd hq.pos hdvd
    nlinarith [hq.two_le]
  have hHodd : Odd (Nat.card ↥H) := by
    rw [hk]
    exact hqodd.pow
  have hcard12 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hcard60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hcard24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification (p := p) (f := 1)
      (by rw [pow_one]; exact hF) H with
    helem | hcyclic | hdihedral | hA4 | hS4 | hA5 | hsemi | hPSL | hPGL
  · obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      omega
    exact hpH (hm ▸ dvd_pow_self p hm0)
  · obtain ⟨_, _, _, hHc⟩ := hcyclic
    exact hcyc hHc
  · obtain ⟨z, _, hcard, _⟩ := hdihedral
    rw [hcard] at hHodd
    exact (Nat.not_even_iff_odd.mpr hHodd) (even_two_mul z)
  · obtain ⟨_, ⟨e⟩⟩ := hA4
    have := Nat.card_congr e.toEquiv
    rw [hcard12] at this
    rw [this] at hHodd
    exact absurd hHodd (by decide)
  · obtain ⟨_, ⟨e⟩⟩ := hS4
    have := Nat.card_congr e.toEquiv
    rw [hcard24] at this
    rw [this] at hHodd
    exact absurd hHodd (by decide)
  · obtain ⟨_, ⟨e⟩⟩ := hA5
    have := Nat.card_congr e.toEquiv
    rw [hcard60] at this
    rw [this] at hHodd
    exact absurd hHodd (by decide)
  · obtain ⟨m, t, -, -, N, C, -, -, hNcard, hCcyc, -, -, hjoin⟩ := hsemi
    by_cases hm0 : m = 0
    · have hNbot : N = ⊥ := Subgroup.eq_bot_of_card_eq N (by rw [hNcard, hm0, pow_zero])
      have hCtop : C = ⊤ := by
        rw [hNbot, bot_sup_eq] at hjoin
        exact hjoin
      apply hcyc
      rw [hCtop] at hCcyc
      exact (MulEquiv.isCyclic (Subgroup.topEquiv (G := ↥H))).mp hCcyc
    · have hNdvd : Nat.card ↥N ∣ Nat.card ↥H := Subgroup.card_subgroup_dvd_card N
      exact hpH ((hNcard ▸ dvd_pow_self p hm0).trans hNdvd)
  · obtain ⟨m, hm, -, ⟨e⟩⟩ := hPSL
    have hGF : IsOddPrimePower (Nat.card (GaloisField p m)) :=
      ⟨p, m, Fact.out, hpodd, Nat.one_le_iff_ne_zero.mpr hm, GaloisField.card p m hm⟩
    have h1 := Nat.card_congr e.toEquiv
    have h2 := even_card_psl2 (GaloisField p m) hGF
    rw [← h1] at h2
    exact (Nat.not_even_iff_odd.mpr hHodd) h2
  · obtain ⟨m, hm, hmdiv, -⟩ := hPGL
    have := Nat.le_of_dvd one_pos hmdiv
    omega

end PSL2

theorem outAutFacts_of_l2p
    {X : Type} [Group X] [Finite X] (hX : IsL2pType X) :
    OutAutFacts X := by
  obtain ⟨F, _, _, p, hpF, hp7, hF, -, ⟨e⟩⟩ := model_of_isL2pType hX
  refine ⟨fun α => ?_, fun α β hα hβ hαi hβi => ?_, fun q hq hq2 a b ha hb hab => ?_⟩
  · rw [← congr_mem_innerAut_iff e, map_mul]
    exact sq_inner_psl2 hp7 hF _
  · obtain ⟨φ', hφ'⟩ := outer_conj_psl2 hp7 hF (MulAut.congr e α) (MulAut.congr e β)
      (by rw [← map_mul, hα, map_one]) (by rw [← map_mul, hβ, map_one])
      (fun h => hαi ((congr_mem_innerAut_iff e α).mp h))
      (fun h => hβi ((congr_mem_innerAut_iff e β).mp h))
    refine ⟨(MulAut.congr e).symm φ', ?_⟩
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hφ'
  · have h1 := odd_pair_psl2 hp7 hF hq hq2 (a := e a) (b := e b)
      (by rw [MulEquiv.orderOf_eq]; exact ha) (by rw [MulEquiv.orderOf_eq]; exact hb)
      (by rw [← map_mul, ← map_mul, hab])
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, e.injective ?_⟩
    rw [map_zpow]
    exact hn

end CFSG.QuasithinUnique.Out21

module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21C1
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Cl1A8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Cl1Ord
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinL2p

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers CFSG.GorensteinWalter

section Claim1

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G}

theorem Lv2520.conjAct_mem_autOn_centralizer_t (h : Lv2520 N t zK) {x : G}
    (hx : x ∈ Subgroup.centralizer ({t} : Set G)) :
    conjAct N.K ⟨x, h.centralizer_t_le_normalizer hx⟩ ∈ autOn N.H N.K := by
  set Hx : Subgroup G := ((autOn N.H N.K).comap (conjAct N.K)).map
    (Subgroup.normalizer (N.K : Set G)).subtype with hHx
  have hK : N.K ≤ Hx := by
    intro k hk
    refine Subgroup.mem_map.mpr ⟨⟨k, Subgroup.le_normalizer hk⟩, ?_, rfl⟩
    exact Setup.mem_autOn_iff.mpr ⟨⟨k, Subgroup.le_normalizer hk⟩, N.K_le_H hk, rfl⟩
  have hS : N.S ≤ Hx := by
    intro s hs'
    refine Subgroup.mem_map.mpr ⟨⟨s, h.S_le_normalizer hs'⟩, ?_, rfl⟩
    exact Setup.mem_autOn_iff.mpr ⟨⟨s, h.S_le_normalizer hs'⟩, N.S_le_H hs', rfl⟩
  have hE : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G) ≤ Hx := by
    intro e he
    have heK : e ∈ Subgroup.centralizer (N.K : Set G) := by
      have := he.2
      rwa [h.hK0] at this
    have heN : e ∈ Subgroup.normalizer (N.K : Set G) := Subgroup.centralizer_le_normalizer _ heK
    refine Subgroup.mem_map.mpr ⟨⟨e, heN⟩, ?_, rfl⟩
    have h1 : conjAct N.K ⟨e, heN⟩ = 1 := by
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      rw [Setup.coe_conjAct_apply]
      show e * (v : G) * e⁻¹ = v
      have := Subgroup.mem_centralizer_iff.mp heK v v.2
      calc e * (v : G) * e⁻¹ = (v : G) * e * e⁻¹ := by rw [← this]
        _ = v := by group
    show conjAct N.K ⟨e, heN⟩ ∈ autOn N.H N.K
    rw [h1]
    exact (autOn N.H N.K).one_mem
  have hle : Subgroup.centralizer ({t} : Set G) ≤ Hx := by
    calc Subgroup.centralizer ({t} : Set G) =
        N.K0 ⊔ N.S ⊔ (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G)) :=
          h.concl2518.2.1
      _ ≤ Hx := sup_le (sup_le (by rw [h.hK0]; exact hK) hS) hE
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle hx)
  have hyy : y = ⟨x, h.centralizer_t_le_normalizer hx⟩ := Subtype.ext hyx
  rw [← hyy]
  exact hy

omit [Finite G] in
theorem coe_conjAct_pow_apply (K : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G))
    (n : ℕ) (v : ↥K) :
    ((((conjAct K ⟨x, hx⟩) ^ n) v : ↥K) : G) = x ^ n * (v : G) * (x ^ n)⁻¹ := by
  rw [← map_pow]
  exact Setup.coe_conjAct_apply (⟨x, hx⟩ ^ n) v

theorem prime_le_seven_of_dvd {p : ℕ} (hp : p.Prime) (h : p ∣ 20160) : p ≤ 7 := by
  have h' : p ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
    · exact (Nat.le_of_dvd (by norm_num) h2).trans (by norm_num)
  · exact Nat.le_of_dvd (by norm_num) h1

theorem Lv2520.false_of_a8 (h : Lv2520 N t zK) (hfam : OutFamily N.K N.H) {Ki : Subgroup G}
    (φ : ↥Ki ≃* ↥(alternatingGroup (Fin 8))) {a b : Fin 8} (hab : a ≠ b)
    (hind : InducesAut t Ki φ (MulAut.conjNormal (Equiv.swap a b)))
    (hK : N.K = perfectResidualOf (Ki ⊓ Subgroup.centralizer ({t} : Set G))) : False := by
  obtain ⟨x, hxX, hx6, ⟨k2, hk2, hk2nc⟩, ⟨k3, hk3, hk3nc⟩, h360, h20160⟩ :=
    Cl1.a8_transposition_facts φ hab hind
  rw [← hK] at hk2 hk3 h360 h20160
  have hxC : x ∈ Subgroup.centralizer ({t} : Set G) := hxX.2
  have hxN : x ∈ Subgroup.normalizer (N.K : Set G) := h.centralizer_t_le_normalizer hxC
  set α : MulAut ↥N.K := conjAct N.K ⟨x, hxN⟩ with hα
  have hαmem : α ∈ autOn N.H N.K := h.conjAct_mem_autOn_centralizer_t hxC
  have hα6 : α ^ 6 = 1 := by
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    rw [coe_conjAct_pow_apply N.K hxN 6 v, hx6]
    simp
  have hα2 : α ^ 2 ≠ 1 := by
    intro h1
    apply hk2nc
    have h2 := congrArg (fun β : MulAut ↥N.K => ((β ⟨k2, hk2⟩ : ↥N.K) : G)) h1
    simp only [hα] at h2
    rw [coe_conjAct_pow_apply N.K hxN 2 ⟨k2, hk2⟩] at h2
    simpa using h2
  have hα3 : α ^ 3 ≠ 1 := by
    intro h1
    apply hk3nc
    have h2 := congrArg (fun β : MulAut ↥N.K => ((β ⟨k3, hk3⟩ : ↥N.K) : G)) h1
    simp only [hα] at h2
    rw [coe_conjAct_pow_apply N.K hxN 3 ⟨k3, hk3⟩] at h2
    simpa using h2
  rcases hfam with hX | ⟨-, hM⟩
  · obtain ⟨F, _, _, p, _, hp7, hF, -, ⟨e⟩⟩ := Out21.model_of_isL2pType hX
    have hpK : p ∣ Nat.card ↥N.K := Out21.prime_dvd_card_of_equiv hp7 hF e
    have hp : p.Prime := Fact.out
    have hp7' : p = 7 := le_antisymm (prime_le_seven_of_dvd hp (hpK.trans h20160)) hp7
    have hcard : Nat.card ↥N.K = 168 := by
      rw [Nat.card_congr e.toEquiv, psl2_card_formula F (Out21.hodd_of hp7 hF), hF, hp7']
      norm_num
    rw [hcard] at h360
    omega
  · refine Out21.A6.false_of_order_six hM (α := (⟨α, hαmem⟩ : ↥(autOn N.H N.K))) ?_ ?_ ?_
    · apply Subtype.ext
      simpa using hα6
    · intro h1
      apply hα2
      simpa using congrArg Subtype.val h1
    · intro h1
      apply hα3
      simpa using congrArg Subtype.val h1

end Claim1

theorem caseCClaim1 : CaseCClaim1 := by
  intro G _ _ T M hs N t zK R h hfam hp i hiSC hi1 hi2
  by_contra hnc
  have hK0 := h.hK0
  have hiS : i ∈ N.S := hiSC.1
  have hiC : i ∈ Subgroup.centralizer (N.K : Set G) := by
    have := hiSC.2
    rwa [hK0] at this
  obtain ⟨-, -, Ki, -, hcases, hfour⟩ := h.concl2519 i (Subgroup.mem_inf.mpr ⟨hiS, hiC⟩) hi1
    (by rwa [pow_two]) hnc
  have hf := h.facts2511
  rcases hfour with ⟨hzK, -⟩ | ⟨-, φ, a, b, hab, hind⟩
  ·
    have htK : t ∈ N.K := by
      have h1 : t = N.z * zK⁻¹ := by rw [hp.hz]; group
      rw [h1]
      exact N.K.mul_mem hzK (N.K.inv_mem (hK0 ▸ hf.zK_mem))
    exact hf.t_ne_one (h.K_inf_SC_eq_bot_mem htK hf.t_mem)
  ·
    have hKperf : N.K = perfectResidualOf (Ki ⊓ Subgroup.centralizer ({t} : Set G)) := by
      rcases hcases with ⟨hne, -⟩ | ⟨hKp, -⟩
      · exact absurd (BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hind.1).symm hne
      · exact hKp
    exact h.false_of_a8 hfam φ hab hind hKperf

end CFSG.QuasithinUnique

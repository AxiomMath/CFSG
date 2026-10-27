module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421MonoGood
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinGL
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421AbsProof

open K421MonoProof K421OrbProof K421LinProof CFSG.Open

theorem smul_zero_V3 : ∀ u : V3, (0 : ZMod 3) • u = 0 := by decide +kernel

theorem smul_one_V3 : ∀ u : V3, (1 : ZMod 3) • u = u := by decide +kernel

theorem smul_two_V3 : ∀ u : V3, (2 : ZMod 3) • u = u + u := by decide +kernel

theorem zmod3_cases : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide

variable {G : Type} [Group G] (D : Mono81 G)

@[expose] def IsType (e : G) (t : Fin 3) : Prop := ∃ n : G, n * e * n⁻¹ = D.av (rep t)

theorem av_smul_mem {H : Subgroup G} {u : V3} (hu : D.av u ∈ H) (c : ZMod 3) :
    D.av (c • u) ∈ H := by
  rcases zmod3_cases c with rfl | rfl | rfl
  · rw [smul_zero_V3, D.av_zero]
    exact H.one_mem
  · rw [smul_one_V3]
    exact hu
  · rw [smul_two_V3, D.av_add]
    exact H.mul_mem hu hu

theorem av_span_mem {H : Subgroup G} {u v : V3} (hu : D.av u ∈ H) (hv : D.av v ∈ H)
    (c d : ZMod 3) : D.av (c • u + d • v) ∈ H := by
  rw [D.av_add]
  exact H.mul_mem (av_smul_mem D hu c) (av_smul_mem D hv d)

theorem orderOf_av {u : V3} (hu : u ≠ 0) : orderOf (D.av u) = 3 :=
  orderOf_eq_prime (D.av_pow_three u) (fun h => hu (D.av_inj (h.trans D.av_zero.symm)))

theorem av_mem_zpowers {u v : V3} (h : v = 0 ∨ v = u ∨ v = -u) :
    D.av v ∈ Subgroup.zpowers (D.av u) := by
  rcases h with rfl | rfl | rfl
  · rw [D.av_zero]
    exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _
  · rw [D.av_neg]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

theorem exists_indep [Finite G] {H : Subgroup G} (hHA : H ≤ D.A0) (h9 : Nat.card H = 9) :
    ∃ u v : V3, Indep u v ∧ D.av u ∈ H ∧ D.av v ∈ H := by
  obtain ⟨h, hhH, hh1⟩ : ∃ h ∈ H, h ≠ 1 := by
    by_contra hcon
    have hall : ∀ x ∈ H, x = 1 := fun x hx => by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
    have hbot : H = ⊥ := (Subgroup.eq_bot_iff_forall H).2 hall
    rw [hbot, Subgroup.card_bot] at h9
    omega
  obtain ⟨u, rfl⟩ := D.mem_A0_iff.1 (hHA hhH)
  have hu0 : u ≠ 0 := fun h0 => hh1 (by rw [h0, D.av_zero])
  have hnot : ¬ H ≤ Subgroup.zpowers (D.av u) := by
    intro hle
    have h3 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_av D hu0, h9] at h3
    omega
  obtain ⟨h', hh'H, hh'n⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨v, rfl⟩ := D.mem_A0_iff.1 (hHA hh'H)
  have hv0 : v ≠ 0 := fun h0 => hh'n (av_mem_zpowers D (Or.inl h0))
  have hvu : v ≠ u := fun h0 => hh'n (av_mem_zpowers D (Or.inr (Or.inl h0)))
  have hvnu : v ≠ -u := fun h0 => hh'n (av_mem_zpowers D (Or.inr (Or.inr h0)))
  exact ⟨u, v, indep_of u v hu0 hv0 hvu hvnu, hhH, hh'H⟩

variable {D}

theorem isType_of_conj (hSP : SignedPerms D) {e g : G} {x : V3} (hx0 : x ≠ 0)
    (hge : g * e * g⁻¹ = D.av x) : ∃ t : Fin 3, nz x = t.val + 1 ∧ IsType D e t := by
  obtain ⟨t, π, ε, hnz, hπ⟩ := exists_act_rep x hx0
  obtain ⟨n, hn⟩ := hSP π ε
  refine ⟨t, hnz, n * g, ?_⟩
  calc n * g * e * (n * g)⁻¹ = n * (g * e * g⁻¹) * n⁻¹ := by group
    _ = n * D.av x * n⁻¹ := by rw [hge]
    _ = D.av (act π ε x) := hn x
    _ = D.av (rep t) := by rw [hπ]

variable [Finite G] {k : ℕ}

theorem exists_type (hk3 : ¬ 3 ∣ k) (hk : Nat.card G = 81 * k) (hSP : SignedPerms D) {e : G}
    (he : orderOf e = 3) : ∃ t : Fin 3, IsType D e t := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : IsElemAbelian 3 (Subgroup.zpowers e) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    have hx3 : (⟨x, hx⟩ : Subgroup.zpowers e) ^ Nat.card (Subgroup.zpowers e) = 1 :=
      pow_card_eq_one'
    rw [Nat.card_zpowers, he] at hx3
    simpa using congrArg Subtype.val hx3
  obtain ⟨g, hg⟩ := D.exists_conj_le_A0' hk3 hk hE
  have heA : g * e * g⁻¹ ∈ D.A0 := by
    have := hg (Subgroup.mem_map.2 ⟨e, Subgroup.mem_zpowers e, rfl⟩)
    simpa [MulAut.conj_apply] using this
  obtain ⟨x, hx⟩ := D.mem_A0_iff.1 heA
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, D.av_zero] at hx
    have he1 : e = 1 := by
      have h1 : e = g⁻¹ * (g * e * g⁻¹) * g := by group
      rw [h1, hx]
      group
    rw [he1, orderOf_one] at he
    omega
  obtain ⟨t, -, ht⟩ := isType_of_conj hSP hx0 hx
  exact ⟨t, ht⟩

theorem exists_types_of_card_nine (hk3 : ¬ 3 ∣ k) (hk : Nat.card G = 81 * k) (hSP : SignedPerms D)
    {E : Subgroup G} (hE : IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    (∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ b ≠ 1 ∧ ∃ t₁ t₂ : Fin 3, t₁ ≠ t₂ ∧ IsType D a t₁ ∧ IsType D b t₂) ∧
    (∃ c ∈ E, c ≠ 1 ∧ ∃ t : Fin 3, t ≠ 1 ∧ IsType D c t) := by
  obtain ⟨g, hg⟩ := D.exists_conj_le_A0' hk3 hk hE
  have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h9]
  obtain ⟨u, v, huv, hu, hv⟩ := exists_indep D hg hcard
  have key : ∀ x : V3, x ≠ 0 → D.av x ∈ E.map (MulAut.conj g).toMonoidHom →
      ∃ e ∈ E, e ≠ 1 ∧ ∃ t : Fin 3, nz x = t.val + 1 ∧ IsType D e t := by
    intro x hx0 hxH
    obtain ⟨e, heE, hex⟩ := Subgroup.mem_map.1 hxH
    have hge : g * e * g⁻¹ = D.av x := by simpa [MulAut.conj_apply] using hex
    refine ⟨e, heE, ?_, isType_of_conj hSP hx0 hge⟩
    intro he1
    rw [he1] at hge
    have : D.av x = 1 := by rw [← hge]; group
    exact hx0 (D.av_inj (this.trans D.av_zero.symm))
  constructor
  · obtain ⟨c₁, d₁, c₂, d₂, hx0, hy0, hne⟩ := exists_two_weights u v huv
    obtain ⟨a, haE, ha1, t₁, hnz₁, hty₁⟩ := key _ hx0 (av_span_mem D hu hv c₁ d₁)
    obtain ⟨b, hbE, hb1, t₂, hnz₂, hty₂⟩ := key _ hy0 (av_span_mem D hu hv c₂ d₂)
    refine ⟨a, haE, b, hbE, ha1, hb1, t₁, t₂, ?_, hty₁, hty₂⟩
    intro h12
    apply hne
    rw [hnz₁, hnz₂, h12]
  · obtain ⟨c₁, d₁, hodd⟩ := exists_odd_weight u v huv
    have hx0 : c₁ • u + d₁ • v ≠ 0 := by
      intro h0
      have := (nz_eq_zero_iff _).2 h0
      omega
    obtain ⟨c, hcE, hc1, t, hnz, hty⟩ := key _ hx0 (av_span_mem D hu hv c₁ d₁)
    refine ⟨c, hcE, hc1, t, ?_, hty⟩
    intro ht1
    subst ht1
    simp at hnz
    omega

end K421AbsProof

end CFSG.LocalAnalysis.RankThreeUC.S15

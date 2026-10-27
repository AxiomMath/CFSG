module

public import CFSG.GH74.GLS.Bg.Local.Lemma1621
public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Group
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourExistence
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Bg.L1621

variable {G : Type*} [Group G]

theorem card_Us_four {V : Subgroup G} (hV : IsFour V) : Nat.card (Us V) = 3 := by
  have h4 : Nat.card ↥V = 4 := hV.2
  have e : Us V ≃ {v : ↥V // v ≠ 1} :=
    { toFun := fun v => ⟨⟨v.1, v.2.1⟩, fun h => v.2.2 (by simpa using congrArg Subtype.val h)⟩
      invFun := fun v => ⟨v.1.1, v.1.2, fun h => v.2 (Subtype.ext h)⟩
      left_inv := fun v => rfl
      right_inv := fun v => rfl }
  rw [Nat.card_congr e]
  classical
  have : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  have := Fintype.ofFinite ↥V
  rw [Nat.card_eq_fintype_card] at h4 ⊢
  simp [Fintype.card_subtype_compl, h4]

theorem normalizer_of_normalIn {S V : Subgroup G} (hN : NormalIn V S) :
    S ≤ normalizer (V : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    exact hN.2 s hs v hv
  · intro hv
    have h1 := hN.2 s⁻¹ (S.inv_mem hs) _ hv
    have e : s⁻¹ * (s * v * s⁻¹) * s⁻¹⁻¹ = v := by group
    rwa [e] at h1

noncomputable def actHom (S V : Subgroup G) (hN : NormalIn V S) : ↥S →* Equiv.Perm (Us V) :=
  (MulAction.toPermHom (normalizer (V : Set G)) (Us V)).comp
    (Subgroup.inclusion (normalizer_of_normalIn hN))

theorem actHom_coe (S V : Subgroup G) (hN : NormalIn V S) (s : ↥S) (v : Us V) :
    (((actHom S V hN s) v : Us V) : G) = (s : G) * v * (s : G)⁻¹ := by
  unfold actHom
  exact phi_coe V _ v

theorem actHom_eq_one_iff (S V : Subgroup G) (hN : NormalIn V S) (r : ↥S) :
    actHom S V hN r = 1 ↔ (r : G) ∈ centralizer (V : Set G) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h v hv
    by_cases hv1 : v = 1
    · subst hv1; simp
    · have e1 := congrArg (fun σ : Equiv.Perm (Us V) => ((σ ⟨v, hv, hv1⟩ : Us V) : G)) h
      simp only [actHom_coe, Equiv.Perm.coe_one, id_eq] at e1
      calc v * (r : G) = (r : G) * v * (r : G)⁻¹ * r := by rw [e1]
        _ = r * v := by group
  · intro h
    refine Equiv.ext fun v => Subtype.ext ?_
    rw [actHom_coe]
    simp only [Equiv.Perm.coe_one, id_eq]
    rw [← h v v.2.1]
    group

theorem four_action_index [Finite G] {S V : Subgroup G} (hS : IsPGroup 2 ↥S) (hV : IsFour V)
    (hN : NormalIn V S) {s t : G} (hs : s ∈ S) (ht : t ∈ S)
    (hs' : s ∉ centralizer (V : Set G)) (ht' : t ∉ centralizer (V : Set G)) :
    s⁻¹ * t ∈ centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  set σ := actHom S V hN with hσ
  have hfin : Finite (Us V) := Nat.finite_of_card_ne_zero (by rw [card_Us_four hV]; norm_num)
  let s' : ↥S := ⟨s, hs⟩
  let t' : ↥S := ⟨t, ht⟩
  have h1 : σ s' ≠ 1 := fun h => hs' ((actHom_eq_one_iff S V hN s').mp h)
  have h2 : σ t' ≠ 1 := fun h => ht' ((actHom_eq_one_iff S V hN t').mp h)
  have h3 : σ s' ≠ σ t' := by
    intro h
    apply hcon
    refine (actHom_eq_one_iff S V hN (s'⁻¹ * t')).mp ?_
    rw [map_mul, map_inv, h]
    exact inv_mul_cancel _
  have hR : IsPGroup 2 ↥σ.range := hS.of_surjective σ.rangeRestrict σ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
  have hge : 3 ≤ Nat.card ↥σ.range := by
    let f : Fin 3 → ↥σ.range := ![1, ⟨σ s', ⟨s', rfl⟩⟩, ⟨σ t', ⟨t', rfl⟩⟩]
    have hf : Function.Injective f := by
      intro i j hij
      have e01 : (1 : ↥σ.range) ≠ ⟨σ s', ⟨s', rfl⟩⟩ := fun e => h1 (by simpa using (congrArg Subtype.val e).symm)
      have e02 : (1 : ↥σ.range) ≠ ⟨σ t', ⟨t', rfl⟩⟩ := fun e => h2 (by simpa using (congrArg Subtype.val e).symm)
      have e12 : (⟨σ s', ⟨s', rfl⟩⟩ : ↥σ.range) ≠ ⟨σ t', ⟨t', rfl⟩⟩ := fun e => h3 (congrArg Subtype.val e)
      fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [f] at hij; tauto)
    simpa using Nat.card_le_card_of_injective f hf
  have hdvd : Nat.card ↥σ.range ∣ 6 := by
    have := Subgroup.card_subgroup_dvd_card σ.range
    rwa [Nat.card_perm, card_Us_four hV] at this
  rw [hk] at hge hdvd
  have hk2 : 2 ≤ k := by
    by_contra hlt
    interval_cases k <;> omega
  have : 4 ∣ 2 ^ k := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
    exact ⟨2 ^ m, by ring⟩
  have h46 : 4 ∣ 6 := this.trans hdvd
  omega

theorem not_two_dvd_index_of_isSylow2In' {X : Type*} [Group X] {P : Subgroup X}
    (hP : IsSylow2In P ⊤) : ¬ 2 ∣ P.index := by
  simpa [Subgroup.relIndex_top_right] using hP.2.2

theorem exists_normal_four_of_rank_three [Finite G] {S E : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hES : E ≤ S) (hE : IsElemAb2 E) (hcard : Nat.card E = 8) :
    ∃ U : Subgroup G, IsFour U ∧ NormalIn U S := by
  have hcomm : IsMulCommutative ↥(E.subgroupOf S) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (by
      have := (hE a.1.1 a.2).2 b.1.1 b.2
      exact this))⟩⟩
  have hE' : CFSG.Open.IsElemAbelian 2 (E.subgroupOf S) :=
    ⟨hcomm, fun a ha => Subtype.ext (by
      have := (hE a.1 ha).1
      simpa [pow_two] using this)⟩
  have hcard' : Nat.card ↥(E.subgroupOf S) = 2 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv, hcard]; norm_num
  have hrank : 3 ≤ CFSG.Open.twoRank ↥S :=
    CFSG.SectionRank.le_pRank (by norm_num) (le_top) hE' hcard'
  obtain ⟨V, hVn, hVe, hVc⟩ :=
    CFSG.ProperTwoGeneratedCore.high_two_rank_normal_four ↥S hS hrank
  refine ⟨V.map S.subtype, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro a ⟨v, hv, rfl⟩
    refine ⟨?_, ?_⟩
    · have h2 : v ^ 2 = 1 := hVe.2 v hv
      have : (v * v : ↥S) = 1 := by simpa [pow_two] using h2
      simpa using congrArg Subtype.val this
    · rintro b ⟨w, hw, rfl⟩
      have := hVe.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩
      exact congrArg (fun z : ↥V => ((z : ↥S) : G)) this
  · rw [Subgroup.card_map_of_injective S.subtype_injective, hVc]
  · rintro a ⟨v, _, rfl⟩
    exact v.2
  · rintro s hs n ⟨v, hv, rfl⟩
    have := hVn.conj_mem v hv ⟨s, hs⟩
    exact ⟨_, this, by simp⟩

theorem simple_nonabelian_no_cyclic_two_quotient {G : Type*} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) {x : G}
    (N : Subgroup G) [N.Normal] (hcyc : IsCyclic (G ⧸ N)) (hxN : x ∉ N) : False := by
  rcases hsimple.eq_bot_or_eq_top_of_normal N with h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    have hcomm : IsMulCommutative (G ⧸ N) := inferInstance
    have h1 : (QuotientGroup.mk a : G ⧸ N) * QuotientGroup.mk b =
        QuotientGroup.mk b * QuotientGroup.mk a := hcomm.is_comm.comm _ _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, h, Subgroup.mem_bot] at h1
    exact hab (by
      have := inv_mul_eq_one.mp h1
      exact this)
  · exact hxN (h ▸ Subgroup.mem_top x)

theorem exists_setup {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {x : G} (hx : x * x = 1) (hx1 : x ≠ 1)
    (hrk : ∃ E : Subgroup G, E ≤ centralizer ({x} : Set G) ∧ IsElemAb2 E ∧ Nat.card E = 8) :
    ∃ S : Subgroup G, IsSylow2In S ⊤ ∧ x ∈ S ∧
      IsSylow2In (S ⊓ centralizer ({x} : Set G)) (centralizer ({x} : Set G)) ∧
      ∃ U : Subgroup G, IsFour U ∧ NormalIn U S ∧ U ≤ centralizer ({x} : Set G) := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({x} : Set G) with hC
  have hxC : x ∈ C := mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh]
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [card_zpowers_of_sq hx hx1]; norm_num)
  obtain ⟨T₀, hT₀, hxT₀⟩ := exists_sylow2_ge hzp (Subgroup.zpowers_le.mpr hxC)
  obtain ⟨S₀, hS₀, hT₀S₀⟩ := exists_sylow2_ge hT₀.2.1 (le_top : T₀ ≤ ⊤)
  have hx₀ : x ∈ S₀ := hT₀S₀ (hxT₀ (Subgroup.mem_zpowers x))
  have hext₀ : S₀ ⊓ C = T₀ :=
    sylow2_eq_of_le hT₀ (hS₀.2.1.to_le inf_le_left) (le_inf hT₀S₀ hT₀.1) inf_le_right
  have hext₀' : IsSylow2In (S₀ ⊓ C) C := by rw [hext₀]; exact hT₀
  obtain ⟨E, hEC, hE, hEcard⟩ := hrk
  have hEp : IsPGroup 2 ↥E := IsPGroup.of_card (n := 3) (by rw [hEcard]; norm_num)
  obtain ⟨T₁, hT₁, hET₁⟩ := exists_sylow2_ge hEp hEC
  obtain ⟨c, _, hc⟩ := sylow2_exists_conj hT₀ hT₁
  have hE'T₀ : Hconj c⁻¹ E ≤ T₀ := by
    intro a ha
    have h1 : c⁻¹ * a * c⁻¹⁻¹ ∈ E := ha
    have h2' := hET₁ h1
    rw [hc, mem_Hconj] at h2'
    have e : c * (c⁻¹ * a * c⁻¹⁻¹) * c⁻¹ = a := by group
    rwa [e] at h2'
  obtain ⟨U₀, hU₀, hN₀⟩ := exists_normal_four_of_rank_three hS₀.2.1 (hE'T₀.trans hT₀S₀)
    (hE.hconj c⁻¹) (by rw [Hconj_card, hEcard])
  have hS₀le := normalizer_of_normalIn hN₀
  by_cases hxU : x ∈ centralizer (U₀ : Set G)
  · refine ⟨S₀, hS₀, hx₀, hext₀', U₀, hU₀, hN₀, fun u hu => ?_⟩
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (mem_centralizer_iff.mp hxU u hu).symm
  ·
    have hidx := not_two_dvd_index_of_isSylow2In' hS₀
    have hres := CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) (P := S₀)
      (Q := S₀ ⊓ centralizer (U₀ : Set G)) (u := x) hS₀.2.1 hidx
      (fun t ht q hq => ⟨S₀.mul_mem (S₀.mul_mem ht hq.1) (S₀.inv_mem ht), by
        show t * q * t⁻¹ ∈ centralizer (U₀ : Set G)
        rw [mem_centralizer_iff]
        intro w hw
        have hq' := mem_centralizer_iff.mp hq.2
        have hw' : t⁻¹ * w * t ∈ U₀ := by
          have := hN₀.2 t⁻¹ (S₀.inv_mem ht) w hw
          simpa using this
        have := hq' _ hw'
        calc w * (t * q * t⁻¹) = t * ((t⁻¹ * w * t) * q) * t⁻¹ := by group
          _ = t * (q * (t⁻¹ * w * t)) * t⁻¹ := by rw [this]
          _ = t * q * t⁻¹ * w := by group⟩)
      (by
        refine ⟨x, hx₀, fun t ht => ?_⟩
        by_cases htQ : t ∈ S₀ ⊓ centralizer (U₀ : Set G)
        · exact ⟨0, by simpa using htQ⟩
        · refine ⟨1, ?_⟩
          have htc : t ∉ centralizer (U₀ : Set G) := fun h => htQ ⟨ht, h⟩
          have := four_action_index hS₀.2.1 hU₀ hN₀ hx₀ ht hxU htc
          simpa using And.intro (S₀.mul_mem (S₀.inv_mem hx₀) ht) this)
      hx₀ (fun h => hxU h.2)
      (fun g k hmem => by
        have hxk : x ^ (2 * k) = 1 := by
          rw [pow_mul]
          have : x ^ 2 = 1 := by simpa [pow_two] using hx
          rw [this, one_pow]
        rw [hxk]
        simp)
      (fun g hg hext => by
        by_cases hyQ : g⁻¹ * x * g ∈ S₀ ⊓ centralizer (U₀ : Set G)
        · exact Or.inl hyQ
        · right
          have hyc : g⁻¹ * x * g ∉ centralizer (U₀ : Set G) := fun h => hyQ ⟨hg, h⟩
          have := four_action_index hS₀.2.1 hU₀ hN₀ hx₀ hg hxU hyc
          exact ⟨S₀.mul_mem (S₀.inv_mem hx₀) hg, this⟩)
    rcases hres with ⟨N, hN, hcyc, _, hxN⟩ | ⟨g, hgQ, hgext, _⟩
    · exact (simple_nonabelian_no_cyclic_two_quotient hsimple hnonab N hcyc hxN).elim
    ·
      have hxg : g⁻¹ * x * g ∈ S₀ := hgQ.1
      have hxgc : g⁻¹ * x * g ∈ centralizer (U₀ : Set G) := hgQ.2
      have hSsyl : IsSylow2In (Hconj g⁻¹ S₀) ⊤ := by
        have := sylow2_conj hS₀ g⁻¹
        have e : Hconj g⁻¹ (⊤ : Subgroup G) = ⊤ := by ext a; simp
        rwa [e] at this
      have hCx : Hconj g⁻¹ (centralizer ({g⁻¹ * x * g} : Set G)) = centralizer ({x} : Set G) := by
        rw [Hconj_centralizer]
        have e : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
        rw [e]
      have hext' : IsSylow2In (Hconj g⁻¹ S₀ ⊓ centralizer ({x} : Set G)) (centralizer ({x} : Set G)) := by
        have := sylow2_conj (show IsSylow2In (S₀ ⊓ centralizer ({g⁻¹ * x * g} : Set G))
          (centralizer ({g⁻¹ * x * g} : Set G)) from hgext) g⁻¹
        rwa [Hconj_inf, hCx] at this
      refine ⟨Hconj g⁻¹ S₀, hSsyl, ?_, hext', Hconj g⁻¹ U₀, ⟨hU₀.1.hconj g⁻¹, by
        rw [Hconj_card]; exact hU₀.2⟩, ⟨Hconj_le_Hconj hN₀.1, fun s hs n hn => ?_⟩, fun n hn => ?_⟩
      · show g⁻¹ * x * g⁻¹⁻¹ ∈ S₀
        simpa using hxg
      · have hs' : g⁻¹ * s * g⁻¹⁻¹ ∈ S₀ := hs
        have hn' : g⁻¹ * n * g⁻¹⁻¹ ∈ U₀ := hn
        have := hN₀.2 _ hs' _ hn'
        show g⁻¹ * (s * n * s⁻¹) * g⁻¹⁻¹ ∈ U₀
        have e : g⁻¹ * (s * n * s⁻¹) * g⁻¹⁻¹ =
            (g⁻¹ * s * g⁻¹⁻¹) * (g⁻¹ * n * g⁻¹⁻¹) * (g⁻¹ * s * g⁻¹⁻¹)⁻¹ := by group
        rw [e]
        exact this
      · have hn' : g⁻¹ * n * g⁻¹⁻¹ ∈ U₀ := hn
        have h1 := mem_centralizer_iff.mp hxgc _ hn'
        rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        have e1 : g⁻¹ * (x * n) * g = g⁻¹ * (n * x) * g := by
          calc g⁻¹ * (x * n) * g = (g⁻¹ * x * g) * (g⁻¹ * n * g) := by group
            _ = (g⁻¹ * n * g) * (g⁻¹ * x * g) := by
                have := h1
                simpa using this.symm
            _ = g⁻¹ * (n * x) * g := by group
        have := mul_left_cancel (mul_right_cancel e1)
        exact this

end CFSG.GH74.GLS.Stage1.Thm6.Sec12

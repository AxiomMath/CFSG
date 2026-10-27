module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverWalk
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSFusion
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs

public section

namespace CFSG.QuasithinUnique.Ch1.HSCover

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.Id2519.UHS
open CFSG.QuasithinUnique.Ch1.M22Cover
open CFSG.Sporadic.Schreier

section Gaschuetz

theorem false_of_section {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {G : Type*}
    [Group G] (X : CentralExt E G) {M Sg : Subgroup G}
    (hrange : ∀ y ∈ M, ∃ e : E, X.φ e = y) (hφmem : ∀ e, X.φ e ∈ M)
    (hodd : Nat.Coprime (Sg.subgroupOf M).index 2) (s : Sg →* E)
    (hs : ∀ g : Sg, X.φ (s g) = (g : G)) : False := by
  classical
  let V : Subgroup E := X.φ.ker
  let P : Subgroup E := Sg.comap X.φ
  let K : Subgroup E := s.range
  have hVφ : ∀ v ∈ V, X.φ v = 1 := fun v hv => hv
  have hζV : X.ζ ∈ V := X.φ_ζ
  have hVcard : Nat.card V = 2 := by
    rw [Nat.card_eq_two_iff' (1 : V)]
    refine ⟨⟨X.ζ, hζV⟩, ?_, ?_⟩
    · intro h
      exact X.ne_one (congrArg Subtype.val h)
    · intro y hy
      rcases X.ker y.1 y.2 with h | h
      · exact absurd (Subtype.ext h) hy
      · exact Subtype.ext h
  have hrangeφ : X.φ.range = M := by
    ext y
    constructor
    · rintro ⟨e, rfl⟩
      exact hφmem e
    · intro hy
      exact hrange y hy
  have hPidx : P.index = (Sg.subgroupOf M).index := by
    have h := Subgroup.index_comap Sg X.φ
    rw [hrangeφ] at h
    exact h
  have hVP : V ≤ P := fun v hv => by
    show X.φ v ∈ Sg
    rw [hVφ v hv]
    exact Sg.one_mem
  have hKP : K ≤ P := by
    rintro _ ⟨g, rfl⟩
    show X.φ (s g) ∈ Sg
    rw [hs g]
    exact g.2
  have hVcentral : ∀ v ∈ V, ∀ e : E, v * e = e * v := by
    intro v hv e
    rcases X.ker v hv with rfl | rfl
    · simp
    · exact X.central e
  have hVK : V ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyV, g, rfl⟩
    have h1 : g = 1 := by
      apply Subtype.ext
      have := hVφ _ hyV
      rw [hs g] at this
      exact this
    rw [h1, map_one]
    exact Subgroup.one_mem _
  have hVKP : V ⊔ K = P := by
    apply le_antisymm (sup_le hVP hKP)
    intro p hp
    have hpS : X.φ p ∈ Sg := hp
    have hmem : p * (s ⟨X.φ p, hpS⟩)⁻¹ ∈ V := by
      show X.φ _ = 1
      rw [map_mul, map_inv, hs ⟨X.φ p, hpS⟩]
      simp
    have hK' : s (⟨X.φ p, hpS⟩ : Sg) ∈ K := ⟨_, rfl⟩
    have := Subgroup.mul_mem_sup hmem hK'
    simpa using this
  have hVn : V.Normal := inferInstanceAs X.φ.ker.Normal
  have hVcomm : IsMulCommutative V :=
    ⟨⟨fun a b => Subtype.ext (hVcentral a a.2 b)⟩⟩
  have hcop : Nat.Coprime P.index (Nat.card V) := by
    rw [hPidx, hVcard]
    exact hodd
  obtain ⟨D', -, hVD, hsupD⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting V P K hcop hVK hVKP
  have hDn : D'.Normal := by
    refine ⟨fun d hd g => ?_⟩
    have hg : g ∈ V ⊔ D' := by rw [hsupD]; trivial
    obtain ⟨v, hv, d₀, hd₀, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    have h1 : v * d₀ * d * (v * d₀)⁻¹ = v * (d₀ * d * d₀⁻¹) * v⁻¹ := by group
    have h2 : v * (d₀ * d * d₀⁻¹) * v⁻¹ = d₀ * d * d₀⁻¹ := by
      rw [hVcentral v hv, mul_inv_cancel_right]
    rw [h1, h2]
    exact D'.mul_mem (D'.mul_mem hd₀ hd) (D'.inv_mem hd₀)
  have hcomm' : ∀ a b : E ⧸ D', a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | _ a =>
      induction b using QuotientGroup.induction_on with
      | _ b =>
        have ha : a ∈ V ⊔ D' := by rw [hsupD]; trivial
        have hb : b ∈ V ⊔ D' := by rw [hsupD]; trivial
        obtain ⟨v₁, hv₁, d₁, hd₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 ha
        obtain ⟨v₂, hv₂, d₂, hd₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hb
        have e1 : ((v₁ * d₁ : E) : E ⧸ D') = (v₁ : E ⧸ D') := by
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff d₁).2 hd₁, mul_one]
        have e2 : ((v₂ * d₂ : E) : E ⧸ D') = (v₂ : E ⧸ D') := by
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff d₂).2 hd₂, mul_one]
        rw [e1, e2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hVcentral v₁ hv₁ v₂]
  have : IsMulCommutative (E ⧸ D') := ⟨⟨hcomm'⟩⟩
  have hsub : Subsingleton (E ⧸ D') := inferInstance
  have hζD : X.ζ ∈ D' := (QuotientGroup.eq_one_iff _).1 (Subsingleton.elim _ _)
  have : X.ζ ∈ V ⊓ D' := ⟨hζV, hζD⟩
  rw [hVD] at this
  exact X.ne_one ((Subgroup.mem_bot).1 this)

end Gaschuetz

section Halving

theorem exists_halving_of_pgroup {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y}
    (hN : N ≤ Subgroup.center Y) (hp : IsPGroup 2 N) (hne : N ≠ ⊥) :
    ∃ (H : Subgroup Y) (n : Y), H ≤ N ∧ n ∈ N ∧ n ∉ H ∧ n * n ∈ H ∧
      ∀ k ∈ N, k ∈ H ∨ n * k ∈ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hp
  have hm1 : 1 ≤ m := by
    by_contra h
    have h0 : m = 0 := by omega
    rw [h0, pow_zero] at hm
    exact hne (Subgroup.card_eq_one.mp hm)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥N) 2 (n := m - 1)
    (by rw [hm]; exact pow_dvd_pow 2 (Nat.sub_le m 1))
  have hKn : K.Normal := by
    refine ⟨fun k hk g => ?_⟩
    have h1 := Subgroup.mem_center_iff.mp (hN g.2) k.1
    have h3 : g * k * g⁻¹ = k := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
    rw [h3]
    exact hk
  have hcardq : Nat.card (↥N ⧸ K) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [hm, hK, show (2 : ℕ) ^ m = 2 ^ (m - 1) * 2 by
      rw [← pow_succ]; congr 1; omega] at h
    have hpos : 0 < 2 ^ (m - 1) := by positivity
    exact (Nat.eq_of_mul_eq_mul_left hpos (by linarith [h])).symm
  obtain ⟨n', hn'⟩ : ∃ e : ↥N, e ∉ K := by
    by_contra h
    have hK' : K = ⊤ := eq_top_iff.mpr fun e _ => by_contra fun hn => h ⟨e, hn⟩
    have h1 : Nat.card K = Nat.card N := by rw [hK']; exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hK, hm] at h1
    have : (2 : ℕ) ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hq2 : ∀ q : ↥N ⧸ K, q = 1 ∨ q = (n' : ↥N ⧸ K) := by
    intro q
    obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥N ⧸ K)).1 hcardq
    by_cases h1 : q = 1
    · exact Or.inl h1
    · refine Or.inr ?_
      have ha : (n' : ↥N ⧸ K) ≠ 1 := fun h => hn' ((QuotientGroup.eq_one_iff n').1 h)
      exact (huniq q h1).trans (huniq _ ha).symm
  have haa : (n' : ↥N ⧸ K) * (n' : ↥N ⧸ K) = 1 := by
    have h := pow_card_eq_one' (G := ↥N ⧸ K) (x := (n' : ↥N ⧸ K))
    rw [hcardq, pow_two] at h
    exact h
  refine ⟨K.map N.subtype, (n' : Y), Subgroup.map_subtype_le K, n'.2, ?_, ?_, ?_⟩
  · rintro ⟨k, hk, hkn⟩
    exact hn' (by have : k = n' := Subtype.ext hkn; rwa [this] at hk)
  · have h1 : n' * n' ∈ K := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      exact haa
    exact ⟨n' * n', h1, rfl⟩
  · intro k hk
    rcases hq2 (⟨k, hk⟩ : ↥N) with h | h
    · exact Or.inl ⟨⟨k, hk⟩, (QuotientGroup.eq_one_iff _).1 h, rfl⟩
    · refine Or.inr ?_
      have h1 : n' * (⟨k, hk⟩ : ↥N) ∈ K := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, h]
        exact haa
      exact ⟨n' * ⟨k, hk⟩, h1, rfl⟩

theorem exists_quotExt' {K : Type*} [Group K] {G : Type*} [Group G] (φ : K →* G)
    (H : Subgroup K) [H.Normal] (n : K) (hHφ : ∀ h ∈ H, φ h = 1) (hnφ : φ n = 1)
    (hnH : n ∉ H) (hnn : n * n ∈ H) (hnc : ∀ k, n * k = k * n)
    (hker : ∀ k, φ k = 1 → k ∈ H ∨ n * k ∈ H) :
    ∃ X : CentralExt (K ⧸ H) G, ∀ k : K, X.φ (k : K ⧸ H) = φ k := by
  refine ⟨⟨QuotientGroup.lift H φ (fun h hh => hHφ h hh), (n : K ⧸ H), ?_, ?_, ?_, ?_, ?_⟩,
    fun k => rfl⟩
  · exact hnφ
  · intro h
    exact hnH ((QuotientGroup.eq_one_iff n).1 h)
  · rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).2 hnn
  · intro e
    induction e using QuotientGroup.induction_on with
    | _ k => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hnc k]
  · intro e he
    induction e using QuotientGroup.induction_on with
    | _ k =>
      have hk : φ k = 1 := he
      rcases hker k hk with h | h
      · exact Or.inl ((QuotientGroup.eq_one_iff k).2 h)
      · refine Or.inr ?_
        have h1 : (n : K ⧸ H) * (k : K ⧸ H) = 1 := by
          rw [← QuotientGroup.mk_mul]
          exact (QuotientGroup.eq_one_iff _).2 h
        have h2 : (n : K ⧸ H) * (n : K ⧸ H) = 1 := by
          rw [← QuotientGroup.mk_mul]
          exact (QuotientGroup.eq_one_iff _).2 hnn
        exact mul_left_cancel (h1.trans h2.symm)

end Halving

section Components

theorem normal_le_center_or_eq_top' {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (N : Subgroup Q) [N.Normal] :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  have := hperf
  have := hs
  let quotient := QuotientGroup.mk' (Subgroup.center Q)
  have hnormal : (N.map quotient).Normal :=
    Subgroup.Normal.map inferInstance quotient (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hkernel : N ≤ quotient.ker := N.map_eq_bot_iff.mp hbot
    change N ≤ (QuotientGroup.mk' (Subgroup.center Q)).ker at hkernel
    simpa only [QuotientGroup.ker_mk'] using hkernel
  · right
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq quotient N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hderived
    exact top_unique hderived

theorem subnormal_le_center_or_eq_top' {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (N : Subgroup Q) (hN : N.IsSubnormal) :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  rcases Subgroup.IsSubnormal.lt_normal hN with htop | ⟨K, hKnorm, hNK, hKlt⟩
  · exact Or.inr htop
  · left
    rcases normal_le_center_or_eq_top' hperf hs K with hKc | hKtop
    · exact hNK.trans hKc
    · exact absurd hKtop hKlt.ne

theorem isA6_facts {G : Type} [Group G] {K : Subgroup G} (hA6 : IsA6 K) :
    IsSimpleGroup ↥K ∧ (∃ a b : ↥K, a * b ≠ b * a) ∧ Nat.card ↥K = 360 := by
  obtain ⟨e⟩ := hA6
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num [Nat.card_eq_fintype_card])
  have hs : IsSimpleGroup ↥K := e.isSimpleGroup
  have h360 : Nat.card ↥K = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  refine ⟨hs, ?_, h360⟩
  by_contra hnc
  push Not at hnc
  let _ : CommGroup ↥K := { (inferInstance : Group ↥K) with mul_comm := fun a b => hnc a b }
  have hp := IsSimpleGroup.prime_card (α := ↥K)
  rw [h360] at hp
  exact absurd hp (by norm_num)

theorem t_not_central {G : Type} [Group G] [Finite G] {X K : Subgroup G} {t : G} (htX : t ∈ X)
    (hXq : CFSG.IsQuasisimple ↥X)
    (hK : IsComponentIn K (X ⊓ Subgroup.centralizer ({t} : Set G))) (hA6 : IsA6 K)
    (hcard : 360 < Nat.card ↥X) : (⟨t, htX⟩ : ↥X) ∉ Subgroup.center ↥X := by
  intro hc
  have hXC : X ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨x, hx⟩)
  rw [inf_eq_left.2 hXC] at hK
  obtain ⟨hKX, -, hKsn⟩ := hK
  obtain ⟨-, hnc, hK360⟩ := isA6_facts hA6
  rcases subnormal_le_center_or_eq_top' hXq.1 hXq.2.1 (K.subgroupOf X) hKsn with h | h
  · obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have h1 := Subgroup.mem_center_iff.1 (h (show (⟨a.1, hKX a.2⟩ : ↥X) ∈ K.subgroupOf X from a.2))
      ⟨b.1, hKX b.2⟩
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2.symm
  · have hXK : X ≤ K := Subgroup.subgroupOf_eq_top.1 h
    have hKeq : K = X := le_antisymm hKX hXK
    rw [hKeq] at hK360
    omega

end Components

section Class

theorem exists_conj_hsC
    (s : PP) (hs2 : s * s = 1) (hs1 : s ≠ 1) (K : Subgroup PP)
    (hK : Nat.card K = 360) (hKc : ∀ k ∈ K, k * s = s * k) :
    ∃ d ∈ PP, (s : Equiv.Perm (Fin 3850)) = d * UHS.hsC * d⁻¹ := by
  have hord : orderOf (s : Equiv.Perm (Fin 3850)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  rcases hs_invol_cover s.2 hord with h | h
  · exfalso
    obtain ⟨c, hc, hce⟩ := hsE1_conj _ h
    have hconj : IsConj (⟨hsGen 0, hsGen_mem 0 (by norm_num)⟩ : PP) s :=
      isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hce.symm⟩
    have h1 := card_centralizer_of_isConj hconj
    rw [card_centralizer_a0] at h1
    have hKle : K ≤ Subgroup.centralizer ({s} : Set PP) := fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.2 (hKc k hk)
    have h2 := Subgroup.card_dvd_of_le hKle
    rw [hK, ← h1] at h2
    norm_num at h2
  · obtain ⟨c, hc, hce⟩ := hsE2_conj _ h
    exact ⟨c, hc, hce⟩

end Class

end CFSG.QuasithinUnique.Ch1.HSCover

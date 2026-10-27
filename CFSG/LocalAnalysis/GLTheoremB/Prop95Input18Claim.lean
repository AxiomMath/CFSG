module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18Comp
public import CFSG.LocalAnalysis.SignalizerFunctor.ActionCommutators
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Pcore

variable {X : Type} [Group X] [Finite X]

theorem le_pCoreOf_of_normal {C N : Subgroup X} (hNC : N ≤ C)
    (hn : ∀ c ∈ C, ∀ x ∈ N, c * x * c⁻¹ ∈ N) (hN : IsPGroup 2 N) : N ≤ pCoreOf 2 C := by
  have hN'n : (N.subgroupOf C).Normal := ⟨fun n hn' g => Subgroup.mem_subgroupOf.2 (by
    have := hn (g : X) g.2 (n : X) (Subgroup.mem_subgroupOf.1 hn')
    simpa using this)⟩
  have hN'p : IsPGroup 2 (N.subgroupOf C) :=
    hN.of_equiv (Subgroup.subgroupOfEquivOfLe hNC).symm
  have hle : N.subgroupOf C ≤ CFSG.pCore 2 ↥C := le_sSup ⟨hN'n, hN'p⟩
  intro x hx
  exact ⟨⟨x, hNC hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem centralizer_conj_mem {B : Subgroup X} {g c : X} (hg : g ∈ Subgroup.normalizer (B : Set X))
    (hc : c ∈ Subgroup.centralizer (B : Set X)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (B : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro b hb
  obtain ⟨u, hu⟩ : ∃ u, u = g⁻¹ * b * g⁻¹⁻¹ := ⟨_, rfl⟩
  have huB : u ∈ B := by
    rw [hu]
    exact (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) b).1 hb
  have hcu : u * c = c * u := hc u huB
  have hb2 : b = g * u * g⁻¹ := by rw [hu]; group
  rw [hb2]
  calc g * u * g⁻¹ * (g * c * g⁻¹) = g * (u * c) * g⁻¹ := by group
    _ = g * (c * u) * g⁻¹ := by rw [hcu]
    _ = g * c * g⁻¹ * (g * u * g⁻¹) := by group

theorem pCoreOf_centralizer_conj_le {B : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (B : Set X)) :
    (pCoreOf 2 (Subgroup.centralizer (B : Set X))).map (MulAut.conj g).toMonoidHom ≤
      pCoreOf 2 (Subgroup.centralizer (B : Set X)) := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (B : Set X) := Subgroup.inv_mem _ hg
  refine le_pCoreOf_of_normal ?_ ?_ ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact centralizer_conj_mem hg (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hd)
  · rintro c hc _ ⟨d, hd, rfl⟩
    have e : g⁻¹ * c * g⁻¹⁻¹ ∈ Subgroup.centralizer (B : Set X) :=
      centralizer_conj_mem hg' hc
    have hdn := Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ e) d
    refine Subgroup.mem_map.2 ⟨(g⁻¹ * c * g⁻¹⁻¹) * d * (g⁻¹ * c * g⁻¹⁻¹)⁻¹, hdn.1 hd, ?_⟩
    show g * ((g⁻¹ * c * g⁻¹⁻¹) * d * (g⁻¹ * c * g⁻¹⁻¹)⁻¹) * g⁻¹ = c * (g * d * g⁻¹) * c⁻¹
    group
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).map _

theorem mem_normalizer_pCoreOf_centralizer {B : Subgroup X} {q : X}
    (hq : q ∈ Subgroup.normalizer (B : Set X)) :
    q ∈ Subgroup.normalizer
      ((pCoreOf 2 (Subgroup.centralizer (B : Set X)) : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have h := pCoreOf_centralizer_conj_le hq ⟨z, hz, rfl⟩
    exact h
  · intro hz
    have h : q⁻¹ * (q * z * q⁻¹) * q⁻¹⁻¹ ∈
        pCoreOf 2 (Subgroup.centralizer (B : Set X)) :=
      pCoreOf_centralizer_conj_le (Subgroup.inv_mem _ hq) ⟨_, hz, rfl⟩
    have e : q⁻¹ * (q * z * q⁻¹) * q⁻¹⁻¹ = z := by group
    rw [e] at h
    exact h

end Pcore

section Strict

variable {X : Type} [Group X] [Finite X]

theorem pgroup_normalizer_strict {p : ℕ} [hpF : Fact p.Prime] {Y B : Subgroup X}
    (hY : IsPGroup p Y) (hBY : B ≤ Y)
    (h : ∀ y ∈ Y, y ∈ Subgroup.normalizer (B : Set X) → y ∈ B) : Y ≤ B := by
  by_contra hne
  haveI : Group.IsNilpotent ↥Y := hY.isNilpotent
  have htop : B.subgroupOf Y ≠ ⊤ := by
    intro e
    apply hne
    intro y hy
    have hmem : (⟨y, hy⟩ : ↥Y) ∈ B.subgroupOf Y := by
      rw [e]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem
  have hlt := normalizerCondition_of_isNilpotent (G := ↥Y) (B.subgroupOf Y)
    (lt_top_iff_ne_top.2 htop)
  obtain ⟨y, hyN, hyB⟩ := SetLike.exists_of_lt hlt
  have hconj : ∀ b ∈ B, (y : X) * b * (y : X)⁻¹ ∈ B := by
    intro b hb
    have h1 := (Subgroup.mem_normalizer_iff.1 hyN ⟨b, hBY hb⟩).1 (Subgroup.mem_subgroupOf.2 hb)
    simpa using Subgroup.mem_subgroupOf.1 h1
  have hconj' : ∀ b ∈ B, (y : X)⁻¹ * b * (y : X)⁻¹⁻¹ ∈ B := by
    intro b hb
    have hyN' : y⁻¹ ∈ Subgroup.normalizer (B.subgroupOf Y) := Subgroup.inv_mem _ hyN
    have h1 := (Subgroup.mem_normalizer_iff.1 hyN' ⟨b, hBY hb⟩).1 (Subgroup.mem_subgroupOf.2 hb)
    simpa using Subgroup.mem_subgroupOf.1 h1
  have hyX : (y : X) ∈ Subgroup.normalizer (B : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hconj z hz
    · intro hz
      have e : (y : X)⁻¹ * ((y : X) * z * (y : X)⁻¹) * (y : X)⁻¹⁻¹ = z := by group
      have h2 := hconj' _ hz
      rwa [e] at h2
  exact hyB (Subgroup.mem_subgroupOf.2 (h y.1 y.2 hyX))

end Strict

section Action

variable {X : Type} [Group X] [Finite X]

theorem coprime_normal_criterion {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q D N : Subgroup X}
    (hQp : IsPGroup p Q) (hD2 : IsPGroup 2 D) (hQD : Q ≤ Subgroup.normalizer (D : Set X))
    (hi : ∀ d ∈ D, ∀ q ∈ Q, d⁻¹ * (q * d * q⁻¹) ∈ N)
    (hii : ∀ x ∈ D, (∀ q ∈ Q, q * x = x * q) → x ∈ N) : D ≤ N := by
  classical
  have conjmem : ∀ (q : ↥Q) (d : ↥D), (q : X) * (d : X) * (q : X)⁻¹ ∈ D := fun q d =>
    (Subgroup.mem_normalizer_iff.1 (hQD q.2) (d : X)).1 d.2
  letI act : MulDistribMulAction ↥Q ↥D :=
    { smul := fun q d => ⟨(q : X) * (d : X) * (q : X)⁻¹, conjmem q d⟩
      one_smul := fun d => Subtype.ext (by
        show (1 : X) * (d : X) * (1 : X)⁻¹ = (d : X)
        group)
      mul_smul := fun q1 q2 d => Subtype.ext (by
        show ((q1 : X) * (q2 : X)) * (d : X) * ((q1 : X) * (q2 : X))⁻¹ =
          (q1 : X) * ((q2 : X) * (d : X) * (q2 : X)⁻¹) * (q1 : X)⁻¹
        group)
      smul_one := fun q => Subtype.ext (by
        show (q : X) * (1 : X) * (q : X)⁻¹ = 1
        group)
      smul_mul := fun q d1 d2 => Subtype.ext (by
        show (q : X) * ((d1 : X) * (d2 : X)) * (q : X)⁻¹ =
          ((q : X) * (d1 : X) * (q : X)⁻¹) * ((q : X) * (d2 : X) * (q : X)⁻¹)
        group) }
  have hcop : Nat.Coprime p (Nat.card ↥D) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hD2
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have key := CFSG.SignalizerFunctor.Helpers.coprime_action_commutator_factorization
    (ActorType := ↥Q) (GroupType := ↥D) p hp hQp hcop
  have hcomm : CFSG.SignalizerFunctor.Helpers.actionCommutator (ActorType := ↥Q) (GroupType := ↥D)
      ≤ N.comap D.subtype := by
    unfold CFSG.SignalizerFunctor.Helpers.actionCommutator
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨q, d, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    exact hi d d.2 q q.2
  have hfix : FixedPoints.subgroup ↥Q ↥D ≤ N.comap D.subtype := by
    intro d hd
    rw [FixedPoints.mem_subgroup] at hd
    rw [Subgroup.mem_comap]
    apply hii (d : X) d.2
    intro q hq
    have h1 := congrArg Subtype.val (hd ⟨q, hq⟩)
    have h2 : (q : X) * (d : X) * (q : X)⁻¹ = (d : X) := h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  have htop : (⊤ : Subgroup ↥D) ≤ N.comap D.subtype := by
    rw [← key]
    exact sup_le hcomm hfix
  intro d hd
  exact htop (Subgroup.mem_top (⟨d, hd⟩ : ↥D))

end Action

section Claim

variable {X : Type} [Group X] [Finite X]

theorem claim_card {p : ℕ} [hpF : Fact p.Prime] (hp2 : p ≠ 2) (hO : GLAPPrimeCore p X = ⊥) :
    ∀ n : ℕ, ∀ B : Subgroup X, IsPGroup p B → Nat.card X - Nat.card B = n →
      ∀ K : Subgroup X, IsComponentOf K ⊤ →
        pCoreOf 2 (Subgroup.centralizer (B : Set X)) ≤ Subgroup.normalizer (K : Set X) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hB hn K hK
  obtain ⟨Ts, hBT⟩ := hB.exists_le_sylow
  have hT : CFSG.Open.fusionIsSylowIn p (Ts : Subgroup X) ⊤ :=
    ⟨le_top, Ts.isPGroup', fun P _ hP hTP => Ts.is_maximal' hP hTP⟩
  have hEn : ((compE X).subgroupOf ⊤).Normal := by
    haveI := compE_normal (X := X)
    infer_instance
  have hE_conj : ∀ g : X, ∀ e ∈ compE X, g * e * g⁻¹ ∈ compE X := fun g e he =>
    (compE_normal (X := X)).conj_mem e he g
  set TE : Subgroup X := (Ts : Subgroup X) ⊓ compE X with hTEdef
  have hTT : ∀ x ∈ TE, x ∈ (Ts : Subgroup X) := fun x hx => (Subgroup.mem_inf.1 hx).1
  have hTEE : ∀ x ∈ TE, x ∈ compE X := fun x hx => (Subgroup.mem_inf.1 hx).2
  have hBTE : ∀ b ∈ B, ∀ t ∈ TE, b * t * b⁻¹ ∈ TE := fun b hb t ht =>
    Subgroup.mem_inf.2 ⟨(Ts : Subgroup X).mul_mem ((Ts : Subgroup X).mul_mem (hBT hb) (hTT t ht))
      ((Ts : Subgroup X).inv_mem (hBT hb)), hE_conj b t (hTEE t ht)⟩
  have hTEf : CFSG.Open.fusionIsSylowIn p TE (compE X) := fusion_inf_normal hT le_top hEn
  set Q : Subgroup X := TE ⊓ Subgroup.normalizer (B : Set X) with hQdef
  have hQT : ∀ q ∈ Q, q ∈ (Ts : Subgroup X) := fun q hq => hTT q (Subgroup.mem_inf.1 hq).1
  have hQE : ∀ q ∈ Q, q ∈ compE X := fun q hq => hTEE q (Subgroup.mem_inf.1 hq).1
  have hQN : ∀ q ∈ Q, q ∈ Subgroup.normalizer (B : Set X) := fun q hq => (Subgroup.mem_inf.1 hq).2
  have hQp : IsPGroup p Q := Ts.isPGroup'.to_le (fun q hq => hQT q hq)
  have hD2 : IsPGroup 2 (pCoreOf 2 (Subgroup.centralizer (B : Set X))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  by_cases hQB : Q ≤ B
  ·
    let Y : Subgroup X :=
      { carrier := {y | ∃ b ∈ B, ∃ t ∈ TE, y = b * t}
        mul_mem' := by
          rintro _ _ ⟨b1, hb1, t1, ht1, rfl⟩ ⟨b2, hb2, t2, ht2, rfl⟩
          exact ⟨b1 * b2, B.mul_mem hb1 hb2, b2⁻¹ * t1 * b2⁻¹⁻¹ * t2,
            TE.mul_mem (hBTE b2⁻¹ (B.inv_mem hb2) t1 ht1) ht2, by group⟩
        one_mem' := ⟨1, B.one_mem, 1, TE.one_mem, by group⟩
        inv_mem' := by
          rintro _ ⟨b, hb, t, ht, rfl⟩
          exact ⟨b⁻¹, B.inv_mem hb, b * t⁻¹ * b⁻¹, hBTE b hb t⁻¹ (TE.inv_mem ht), by group⟩ }
    have hYT : Y ≤ (Ts : Subgroup X) := by
      rintro y ⟨b, hb, t, ht, rfl⟩
      exact (Ts : Subgroup X).mul_mem (hBT hb) (hTT t ht)
    have hYp : IsPGroup p Y := Ts.isPGroup'.to_le hYT
    have hBY : B ≤ Y := fun b hb => ⟨b, hb, 1, TE.one_mem, by group⟩
    have hYB : Y ≤ B := pgroup_normalizer_strict hYp hBY (by
      rintro y ⟨b, hb, t, ht, rfl⟩ hyN
      have htN : t ∈ Subgroup.normalizer (B : Set X) := by
        have h1 := (Subgroup.normalizer (B : Set X)).mul_mem
          ((Subgroup.normalizer (B : Set X)).inv_mem (Subgroup.le_normalizer hb)) hyN
        simpa using h1
      exact B.mul_mem hb (hQB (Subgroup.mem_inf.2 ⟨ht, htN⟩)))
    have hTEB : TE ≤ B := fun t ht => hYB ⟨1, B.one_mem, t, ht, by group⟩
    have hstep : ∀ g ∈ pCoreOf 2 (Subgroup.centralizer (B : Set X)), ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
      intro g hg k hk
      have hgC : g ∈ Subgroup.centralizer (B : Set X) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hg
      by_contra hgk
      have hK' := isComponentOf_conj hK g
      have hne : K.map (MulAut.conj g).toMonoidHom ≠ K := by
        intro heq
        apply hgk
        have hmem : (MulAut.conj g).toMonoidHom k ∈ K.map (MulAut.conj g).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hk
        rw [heq] at hmem
        exact hmem
      have hcentral : ∀ s ∈ TE ⊓ K, ∀ y ∈ K, s * y = y * s := by
        intro s hs y hy
        have hsB : s ∈ B := hTEB (Subgroup.mem_inf.1 hs).1
        have hgs : g * s = s * g := ((Subgroup.mem_centralizer_iff.1 hgC) s hsB).symm
        have hsK' : s ∈ K.map (MulAut.conj g).toMonoidHom := by
          refine Subgroup.mem_map.2 ⟨s, (Subgroup.mem_inf.1 hs).2, ?_⟩
          show g * s * g⁻¹ = s
          rw [hgs]
          group
        exact comp_comm hK' hK hne hsK' hy
      have hKE : K ≤ compE X := le_compE hK
      have hKn : (K.subgroupOf (compE X)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKE).2 (compE_normalizes hK)
      have hTK := fusion_inf_normal hTEf hKE hKn
      obtain ⟨P, hP⟩ := CFSG.Goldschmidt.SStarTransport.exists_sylow_of_isSylowIn hTK
      refine not_central_sylow hO hK P ?_
      intro x hx y
      have hx' : (x : X) ∈ TE ⊓ K := by
        have hx2 : x ∈ (TE ⊓ K).subgroupOf K := by
          rw [← hP]
          exact hx
        exact Subgroup.mem_subgroupOf.1 hx2
      exact Subtype.ext (hcentral (x : X) hx' (y : X) y.2)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact fun hk => hstep g hg k hk
    · intro hk
      have h1 := hstep g⁻¹ ((pCoreOf 2 (Subgroup.centralizer (B : Set X))).inv_mem hg) _ hk
      have e : g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k := by group
      rwa [e] at h1
  ·
    have hBR : B < Q ⊔ B := by
      refine lt_of_le_of_ne le_sup_right ?_
      intro heq
      apply hQB
      have h1 : Q ≤ Q ⊔ B := le_sup_left
      rw [← heq] at h1
      exact h1
    have hRT : Q ⊔ B ≤ (Ts : Subgroup X) := sup_le (fun q hq => hQT q hq) hBT
    have hRp : IsPGroup p ((Q ⊔ B : Subgroup X)) := Ts.isPGroup'.to_le hRT
    have hc1 : Nat.card B < Nat.card ↥(Q ⊔ B) := Subgroup.card_lt_of_lt hBR
    have hc2 : Nat.card ↥(Q ⊔ B) ≤ Nat.card X := Subgroup.card_le_card_group _
    have hlt : Nat.card X - Nat.card ↥(Q ⊔ B) < n := by omega
    have IH := ih (Nat.card X - Nat.card ↥(Q ⊔ B)) hlt (Q ⊔ B) hRp rfl K hK
    refine coprime_normal_criterion hpF.out hp2 hQp hD2 ?_ ?_ ?_
    · intro q hq
      exact mem_normalizer_pCoreOf_centralizer (hQN q hq)
    · intro d hd q hq
      have hqE := hQE q hq
      have e : d⁻¹ * (q * d * q⁻¹) = (d⁻¹ * q * d⁻¹⁻¹) * q⁻¹ := by group
      have hmem : d⁻¹ * (q * d * q⁻¹) ∈ compE X := by
        rw [e]
        exact (compE X).mul_mem ((compE_normal (X := X)).conj_mem q hqE d⁻¹)
          ((compE X).inv_mem hqE)
      exact compE_normalizes hK hmem
    · intro x hx hxQ
      have hRC : Subgroup.centralizer ((Q ⊔ B : Subgroup X) : Set X) ≤
          Subgroup.centralizer (B : Set X) :=
        Subgroup.centralizer_le (fun b hb => Subgroup.mem_sup_right hb)
      set M' : Subgroup X := pCoreOf 2 (Subgroup.centralizer (B : Set X)) ⊓
        Subgroup.centralizer ((Q : Subgroup X) : Set X) with hM'
      have hM'R : M' ≤ Subgroup.centralizer ((Q ⊔ B : Subgroup X) : Set X) := by
        intro m hm
        obtain ⟨hmD, hmQ⟩ := Subgroup.mem_inf.1 hm
        have hmC : m ∈ Subgroup.centralizer (B : Set X) :=
          CFSG.LieType.BorelTits.pCoreOf_le 2 _ hmD
        have hsub : Q ⊔ B ≤ Subgroup.centralizer ({m} : Set X) := by
          refine sup_le ?_ ?_
          · intro q hq
            exact Subgroup.mem_centralizer_singleton_iff.2
              ((Subgroup.mem_centralizer_iff.1 hmQ) q hq)
          · intro b hb
            exact Subgroup.mem_centralizer_singleton_iff.2
              ((Subgroup.mem_centralizer_iff.1 hmC) b hb)
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        exact Subgroup.mem_centralizer_singleton_iff.1 (hsub hr)
      have hM'norm : ∀ c ∈ Subgroup.centralizer ((Q ⊔ B : Subgroup X) : Set X),
          ∀ m ∈ M', c * m * c⁻¹ ∈ M' := by
        intro c hc m hm
        obtain ⟨hmD, hmQ⟩ := Subgroup.mem_inf.1 hm
        have hcC : c ∈ Subgroup.centralizer (B : Set X) := hRC hc
        have hcQ : c ∈ Subgroup.centralizer ((Q : Subgroup X) : Set X) :=
          Subgroup.centralizer_le (fun q hq => Subgroup.mem_sup_left hq) hc
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hcC) m).1 hmD
        · exact (Subgroup.centralizer ((Q : Subgroup X) : Set X)).mul_mem
            ((Subgroup.centralizer ((Q : Subgroup X) : Set X)).mul_mem hcQ hmQ)
            ((Subgroup.centralizer ((Q : Subgroup X) : Set X)).inv_mem hcQ)
      have hM'2 : IsPGroup 2 M' := hD2.to_le inf_le_left
      have hM'le : M' ≤ pCoreOf 2 (Subgroup.centralizer ((Q ⊔ B : Subgroup X) : Set X)) :=
        le_pCoreOf_of_normal hM'R hM'norm hM'2
      have hxM' : x ∈ M' :=
        Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_centralizer_iff.2 hxQ⟩
      exact IH (hM'le hxM')

end Claim

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18

module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18Claim
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
  CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18

section Lemmas

variable {X : Type} [Group X] [Finite X]

theorem lstar_coprime_criterion {p : ℕ} [hpF : Fact p.Prime] {Q D N : Subgroup X}
    (hQp : IsPGroup p Q) (hcop : Nat.Coprime p (Nat.card D))
    (hQD : Q ≤ Subgroup.normalizer (D : Set X))
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
  have key := CFSG.SignalizerFunctor.Helpers.coprime_action_commutator_factorization
    (ActorType := ↥Q) (GroupType := ↥D) p hpF.out hQp hcop
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

theorem lstar_normalizer_centralizer {p : ℕ} {B : Subgroup X} {q : X}
    (hq : q ∈ Subgroup.normalizer (B : Set X)) :
    q ∈ Subgroup.normalizer
      ((GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) : Subgroup X) : Set X) := by
  have hC : GLBConj q (Subgroup.centralizer (B : Set X)) = Subgroup.centralizer (B : Set X) := by
    ext y
    rw [mem_gLBConj]
    constructor
    · intro hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro b hb
      have hh := hy (q * b * q⁻¹) ((Subgroup.mem_normalizer_iff.1 hq b).1 hb)
      calc b * y = q⁻¹ * ((q * b * q⁻¹) * (q * y * q⁻¹)) * q := by group
        _ = q⁻¹ * ((q * y * q⁻¹) * (q * b * q⁻¹)) * q := by rw [hh]
        _ = y * b := by group
    · intro hy
      exact centralizer_conj_mem hq hy
  have h := glaPPrimeCoreOf_gLBConj p q (Subgroup.centralizer (B : Set X))
  rw [hC] at h
  exact mem_normalizer_iff_gLBConj_eq.2 h.symm

theorem lstar_centralizer_normalizes_of_TE_le {p : ℕ} [hpF : Fact p.Prime]
    (hO : GLAPPrimeCore p X = ⊥) {T B : Subgroup X} (hT : CFSG.Open.fusionIsSylowIn p T ⊤)
    (hTE : T ⊓ compE X ≤ B) {K : Subgroup X} (hK : IsComponentOf K ⊤) {g : X}
    (hg : g ∈ Subgroup.centralizer (B : Set X)) : g ∈ Subgroup.normalizer (K : Set X) := by
  have hEn : ((compE X).subgroupOf ⊤).Normal := by
    haveI := compE_normal (X := X)
    infer_instance
  have hTEf : CFSG.Open.fusionIsSylowIn p (T ⊓ compE X) (compE X) :=
    fusion_inf_normal hT le_top hEn
  have hKE : K ≤ compE X := le_compE hK
  have hKn : (K.subgroupOf (compE X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKE).2 (compE_normalizes hK)
  have hTK := fusion_inf_normal hTEf hKE hKn
  have hstep : ∀ h ∈ Subgroup.centralizer (B : Set X), ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    intro h hh k hk
    by_contra hhk
    have hK' := isComponentOf_conj hK h
    have hne : K.map (MulAut.conj h).toMonoidHom ≠ K := by
      intro heq
      apply hhk
      have hmem : (MulAut.conj h).toMonoidHom k ∈ K.map (MulAut.conj h).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hk
      rw [heq] at hmem
      exact hmem
    have hcentral : ∀ s ∈ (T ⊓ compE X) ⊓ K, ∀ y ∈ K, s * y = y * s := by
      intro s hs y hy
      have hsB : s ∈ B := hTE (Subgroup.mem_inf.1 hs).1
      have hgs : h * s = s * h := ((Subgroup.mem_centralizer_iff.1 hh) s hsB).symm
      have hsK' : s ∈ K.map (MulAut.conj h).toMonoidHom := by
        refine Subgroup.mem_map.2 ⟨s, (Subgroup.mem_inf.1 hs).2, ?_⟩
        show h * s * h⁻¹ = s
        rw [hgs]
        group
      exact comp_comm hK' hK hne hsK' hy
    obtain ⟨P, hP⟩ := CFSG.Goldschmidt.SStarTransport.exists_sylow_of_isSylowIn hTK
    refine not_central_sylow hO hK P ?_
    intro x hx y
    have hx' : (x : X) ∈ (T ⊓ compE X) ⊓ K := by
      have hx2 : x ∈ ((T ⊓ compE X) ⊓ K).subgroupOf K := by
        rw [← hP]
        exact hx
      exact Subgroup.mem_subgroupOf.1 hx2
    exact Subtype.ext (hcentral (x : X) hx' (y : X) y.2)
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact fun hk => hstep g hg k hk
  · intro hk
    have h1 := hstep g⁻¹ (Subgroup.inv_mem _ hg) _ hk
    have e : g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k := by group
    rwa [e] at h1

theorem lstar_TE_le_of_Q_le {p : ℕ} [hpF : Fact p.Prime] {T B : Subgroup X} (hTp : IsPGroup p T)
    (hBT : B ≤ T) (hQ : ∀ t ∈ T ⊓ compE X, t ∈ Subgroup.normalizer (B : Set X) → t ∈ B) :
    T ⊓ compE X ≤ B := by
  set TE : Subgroup X := T ⊓ compE X with hTEdef
  have hTT : ∀ x ∈ TE, x ∈ T := fun x hx => (Subgroup.mem_inf.1 hx).1
  have hTEE : ∀ x ∈ TE, x ∈ compE X := fun x hx => (Subgroup.mem_inf.1 hx).2
  have hBTE : ∀ b ∈ B, ∀ t ∈ TE, b * t * b⁻¹ ∈ TE := fun b hb t ht =>
    Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem (hBT hb) (hTT t ht)) (T.inv_mem (hBT hb)),
      (compE_normal (X := X)).conj_mem t (hTEE t ht) b⟩
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
  have hYT : Y ≤ T := by
    rintro y ⟨b, hb, t, ht, rfl⟩
    exact T.mul_mem (hBT hb) (hTT t ht)
  have hYp : IsPGroup p Y := hTp.to_le hYT
  have hBY : B ≤ Y := fun b hb => ⟨b, hb, 1, TE.one_mem, by group⟩
  have hYB : Y ≤ B := pgroup_normalizer_strict hYp hBY (by
    rintro y ⟨b, hb, t, ht, rfl⟩ hyN
    have htN : t ∈ Subgroup.normalizer (B : Set X) := by
      have h1 := (Subgroup.normalizer (B : Set X)).mul_mem
        ((Subgroup.normalizer (B : Set X)).inv_mem (Subgroup.le_normalizer hb)) hyN
      simpa using h1
    exact B.mul_mem hb (hQ t ht htN))
  intro t ht
  exact hYB ⟨1, B.one_mem, t, ht, by group⟩

theorem lstar_glaPPrimeCoreOf_le (p : ℕ) (H : Subgroup X) : GLAPPrimeCoreOf p H ≤ H := by
  unfold GLAPPrimeCoreOf
  exact Subgroup.map_subtype_le _

theorem lstar_caseB {p : ℕ} [hpF : Fact p.Prime] {B Q : Subgroup X}
    (hQp : IsPGroup p Q) (hQN : Q ≤ Subgroup.normalizer (B : Set X))
    (hQE : ∀ q ∈ Q, q ∈ compE X) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (IH : GLAPPrimeCoreOf p (Subgroup.centralizer ((Q ⊔ B : Subgroup X) : Set X)) ≤
      Subgroup.normalizer (K : Set X)) :
    GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ≤ Subgroup.normalizer (K : Set X) := by
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)))) :=
    (Nat.Prime.coprime_iff_not_dvd hpF.out).2
      (not_dvd_card_glaPPrimeCoreOf hpF.out (Subgroup.centralizer (B : Set X)))
  refine lstar_coprime_criterion hQp hcop ?_ ?_ ?_
  · intro q hq
    exact lstar_normalizer_centralizer (hQN hq)
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
    set M' : Subgroup X := GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ⊓
      Subgroup.centralizer ((Q : Subgroup X) : Set X) with hM'
    have hM'R : M' ≤ Subgroup.centralizer ((Q ⊔ B : Subgroup X) : Set X) := by
      intro m hm
      obtain ⟨hmD, hmQ⟩ := Subgroup.mem_inf.1 hm
      have hmC : m ∈ Subgroup.centralizer (B : Set X) :=
        lstar_glaPPrimeCoreOf_le p _ hmD
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
      · exact (Subgroup.mem_normalizer_iff.1
          (le_normalizer_glaPPrimeCoreOf p _ hcC) m).1 hmD
      · exact (Subgroup.centralizer ((Q : Subgroup X) : Set X)).mul_mem
          ((Subgroup.centralizer ((Q : Subgroup X) : Set X)).mul_mem hcQ hmQ)
          ((Subgroup.centralizer ((Q : Subgroup X) : Set X)).inv_mem hcQ)
    have hNorm : Subgroup.centralizer ((Q ⊔ B : Subgroup X) : Set X) ≤
        Subgroup.normalizer (M' : Set X) := by
      intro c hc
      rw [Subgroup.mem_normalizer_iff]
      intro m
      constructor
      · exact fun hm => hM'norm c hc m hm
      · intro hm
        have h1 := hM'norm c⁻¹ (Subgroup.inv_mem _ hc) _ hm
        have e : c⁻¹ * (c * m * c⁻¹) * c⁻¹⁻¹ = m := by group
        rwa [e] at h1
    have hn : (M'.subgroupOf (Subgroup.centralizer ((Q ⊔ B : Subgroup X) : Set X))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hM'R).2 hNorm
    have hS : IsSubnormal M' (Subgroup.centralizer ((Q ⊔ B : Subgroup X) : Set X)) :=
      IsSubnormal.step hM'R hn (IsSubnormal.refl _)
    have hcopM' : Nat.Coprime p (Nat.card M') :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop
    have hM'le : M' ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ((Q ⊔ B : Subgroup X) : Set X)) :=
      le_glaPPrimeCoreOf_of_coprime hpF.out hS hcopM'
    have hxM' : x ∈ M' := Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_centralizer_iff.2 hxQ⟩
    exact IH (hM'le hxM')

theorem lstar_claim {p : ℕ} [hpF : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥) :
    ∀ n : ℕ, ∀ B : Subgroup X, IsPGroup p B → Nat.card X - Nat.card B = n →
      ∀ K : Subgroup X, IsComponentOf K ⊤ →
        GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ≤ Subgroup.normalizer (K : Set X) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hB hn K hK
  obtain ⟨Ts, hBT⟩ := hB.exists_le_sylow
  have hT : CFSG.Open.fusionIsSylowIn p (Ts : Subgroup X) ⊤ :=
    ⟨le_top, Ts.isPGroup', fun P _ hP hTP => Ts.is_maximal' hP hTP⟩
  set TE : Subgroup X := (Ts : Subgroup X) ⊓ compE X with hTEdef
  set Q : Subgroup X := TE ⊓ Subgroup.normalizer (B : Set X) with hQdef
  have hQT : ∀ q ∈ Q, q ∈ (Ts : Subgroup X) := fun q hq =>
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hq).1).1
  have hQE : ∀ q ∈ Q, q ∈ compE X := fun q hq =>
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hq).1).2
  have hQN : Q ≤ Subgroup.normalizer (B : Set X) := fun q hq => (Subgroup.mem_inf.1 hq).2
  have hQp : IsPGroup p Q := Ts.isPGroup'.to_le (fun q hq => hQT q hq)
  by_cases hQB : Q ≤ B
  ·
    have hTE : TE ≤ B :=
      lstar_TE_le_of_Q_le Ts.isPGroup' hBT (fun t ht hN => hQB (Subgroup.mem_inf.2 ⟨ht, hN⟩))
    have hC : Subgroup.centralizer (B : Set X) ≤ Subgroup.normalizer (K : Set X) :=
      fun g hg => lstar_centralizer_normalizes_of_TE_le hO hT hTE hK hg
    exact (lstar_glaPPrimeCoreOf_le p _).trans hC
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
    exact lstar_caseB hQp hQN hQE hK IH

end Lemmas

end CFSG.LocalAnalysis.GLTheoremA

module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Norm

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem conj_central_left' {A : Type*} [Group A] {z : A} (hz : z ∈ Subgroup.center A) (g : A) :
    z * g * z⁻¹ = g := by
  rw [← Subgroup.mem_center_iff.1 hz g]
  group

theorem commutatorElement_mul_central' {A : Type*} [Group A] {c d : A}
    (hc : c ∈ Subgroup.center A) (hd : d ∈ Subgroup.center A) (x y : A) :
    ⁅c * x, d * y⁆ = ⁅x, y⁆ := by
  have hdx : x * d = d * x := Subgroup.mem_center_iff.1 hd x
  rw [commutatorElement_def, commutatorElement_def]
  calc c * x * (d * y) * (c * x)⁻¹ * (d * y)⁻¹
      = c * (x * d * y * x⁻¹) * c⁻¹ * (d * y)⁻¹ := by group
    _ = (x * d * y * x⁻¹) * (d * y)⁻¹ := by rw [conj_central_left' hc]
    _ = d * (x * y * x⁻¹ * y⁻¹) * d⁻¹ := by rw [hdx]; group
    _ = x * y * x⁻¹ * y⁻¹ := conj_central_left' hd _

theorem not_central_sylow_of_dvd {p : ℕ} [hpF : Fact p.Prime] {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hdvd : p ∣ Nat.card ↥K) (P : Sylow p ↥K)
    (hP : ∀ x ∈ (P : Subgroup ↥K), ∀ y : ↥K, x * y = y * x) : False := by
  have hPn : (P : Subgroup ↥K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have e : g * n * g⁻¹ = n := by
      rw [← hP n hn g, mul_inv_cancel_right]
    rw [e]
    exact hn
  haveI := hPn
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := (P : Subgroup ↥K)) (Sylow.card_coprime_index P)
  have hPidx : Nat.card H = (P : Subgroup ↥K).index := hH.symm.index_eq_card.symm
  have hsup : (P : Subgroup ↥K) ⊔ H = ⊤ := hH.sup_eq_top
  have hHn : H.Normal := by
    refine ⟨fun h hh g => ?_⟩
    have hg : g ∈ (P : Subgroup ↥K) ⊔ H := by
      rw [hsup]
      exact Subgroup.mem_top g
    obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_left).1 hg
    rw [← hyz]
    have hyw := hP y hy (z * h * z⁻¹)
    have e : y * z * h * (y * z)⁻¹ = y * (z * h * z⁻¹) * y⁻¹ := by group
    rw [e]
    have e2 : y * (z * h * z⁻¹) * y⁻¹ = z * h * z⁻¹ := by
      rw [hyw]; group
    rw [e2]
    exact H.mul_mem (H.mul_mem hz hh) (H.inv_mem hz)
  have hcomm : ∀ a b : ↥K, ⁅a, b⁆ ∈ H := by
    intro a b
    obtain ⟨y₁, hy₁, z₁, hz₁, rfl⟩ := (Subgroup.mem_sup_of_normal_left).1
      (show a ∈ (P : Subgroup ↥K) ⊔ H by rw [hsup]; exact Subgroup.mem_top a)
    obtain ⟨y₂, hy₂, z₂, hz₂, rfl⟩ := (Subgroup.mem_sup_of_normal_left).1
      (show b ∈ (P : Subgroup ↥K) ⊔ H by rw [hsup]; exact Subgroup.mem_top b)
    have hc₁ : y₁ ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.2 fun g => (hP y₁ hy₁ g).symm
    have hc₂ : y₂ ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.2 fun g => (hP y₂ hy₂ g).symm
    rw [commutatorElement_mul_central' hc₁ hc₂]
    exact H.mul_mem (H.mul_mem (H.mul_mem hz₁ hz₂) (H.inv_mem hz₁)) (H.inv_mem hz₂)
  have hHtop : H = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : k ∈ commutator ↥K := by rw [hK.2.2.1]; exact Subgroup.mem_top k
    exact (commutator_def ↥K ▸ Subgroup.commutator_le.2 (fun a _ b _ => hcomm a b)) hk
  have hidx : (P : Subgroup ↥K).index = Nat.card ↥K := by
    rw [← hPidx, hHtop, Subgroup.card_top]
  exact Sylow.not_dvd_index P (by rw [hidx]; exact hdvd)

theorem claim_card_dvd {p : ℕ} [hpF : Fact p.Prime] (hp2 : p ≠ 2) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hdvd : p ∣ Nat.card ↥K) :
    ∀ n : ℕ, ∀ B : Subgroup X, IsPGroup p B → Nat.card X - Nat.card B = n →
      pCoreOf 2 (Subgroup.centralizer (B : Set X)) ≤ Subgroup.normalizer (K : Set X) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hB hn
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
      refine not_central_sylow_of_dvd hK hdvd P ?_
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
    have IH := ih (Nat.card X - Nat.card ↥(Q ⊔ B)) hlt (Q ⊔ B) hRp rfl
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

theorem pCoreOf_centralizer_le_normalizer_of_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hdvd : p ∣ Nat.card ↥K)
    {B : Subgroup X} (hB : IsPGroup p B) :
    pCoreOf 2 (Subgroup.centralizer (B : Set X)) ≤ Subgroup.normalizer (K : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact claim_card_dvd hp2 hK hdvd _ B hB rfl

theorem pCoreOf_centralizer_singleton_le_normalizer_of_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hdvd : p ∣ Nat.card ↥K) {d : X}
    (hd : d ^ p = 1) :
    pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X) := by
  have hB : IsPGroup p (Subgroup.zpowers d) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hd)
  have hCB : Subgroup.centralizer ((Subgroup.zpowers d : Subgroup X) : Set X) =
      Subgroup.centralizer ({d} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have := pCoreOf_centralizer_le_normalizer_of_dvd hp hp2 hK hdvd hB
  rwa [hCB] at this

theorem le_centralizer_of_not_mem_normalizer' {p : ℕ} (hp : p.Prime)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) {d : X}
    (hd : d ^ p = 1) (hdK : d ∉ Subgroup.normalizer (K : Set X))
    (hTN : pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X))
    {T : Subgroup X} (hT : T ≤ pCoreOf 2 (Subgroup.centralizer ({d} : Set X))) :
    T ≤ Subgroup.centralizer (K : Set X) := by
  set T₀ := pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) with hT₀
  refine le_trans hT ?_
  intro t ht
  have htN : t ∈ Subgroup.normalizer (K : Set X) := hTN ht
  have htC : t ∈ Subgroup.centralizer ({d} : Set X) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ ht
  have hdt : t * d = d * t := Subgroup.mem_centralizer_singleton_iff.1 htC
  set δ : ↥K →* X := diagHom hp hK hd hdK with hδ
  have hδapp : ∀ k : ↥K, δ k = diagProd d p (k : X) := fun k => rfl
  have hδC : ∀ k : ↥K, δ k ∈ Subgroup.centralizer ({d} : Set X) := by
    intro k
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := diagProd_comm_d hp hK hd hdK k.2
    have h2 : d * δ k = δ k * d := by
      calc d * δ k = (d * δ k * d⁻¹) * d := by group
        _ = δ k * d := by rw [hδapp, h1]
    exact h2.symm
  have hδT : ∀ k : ↥K, ∀ x ∈ T₀, δ k * x * (δ k)⁻¹ ∈ T₀ := fun k x hx =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ (hδC k)) x).1 hx
  let tk : ↥K → ↥K := fun k =>
    ⟨t * (k : X) * t⁻¹, (Subgroup.mem_normalizer_iff.1 htN k).1 k.2⟩
  have htk_mul : ∀ k k' : ↥K, tk (k * k') = tk k * tk k' := fun k k' =>
    Subtype.ext (by simp only [tk, Subgroup.coe_mul]; group)
  let u : ↥K → ↥K := fun k => tk k * k⁻¹
  have hδtk : ∀ k : ↥K, δ (tk k) = t * δ k * t⁻¹ := by
    intro k
    show diagProd d p (t * (k : X) * t⁻¹) = t * diagProd d p (k : X) * t⁻¹
    exact (diagProd_conj hdt p k).symm
  have hδu : ∀ k : ↥K, δ (u k) ∈ T₀ := by
    intro k
    have h1 : δ (u k) = t * (δ k * t⁻¹ * (δ k)⁻¹) := by
      show δ (tk k * k⁻¹) = _
      rw [map_mul, map_inv, hδtk]; group
    rw [h1]
    exact T₀.mul_mem ht (hδT k t⁻¹ (T₀.inv_mem ht))
  let L : Subgroup ↥K := Subgroup.closure (Set.range u)
  have hLδ : L ≤ T₀.comap δ := (Subgroup.closure_le _).2 (by
    rintro _ ⟨k, rfl⟩
    exact hδu k)
  have hLn : L.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : L ≤ L.comap (MulAut.conj g).toMonoidHom := (Subgroup.closure_le _).2 (by
      rintro _ ⟨k, rfl⟩
      show g * u k * g⁻¹ ∈ L
      have : g * u k * g⁻¹ = (u g)⁻¹ * u (g * k) := by
        simp only [u, htk_mul]; group
      rw [this]
      exact L.mul_mem (L.inv_mem (Subgroup.subset_closure ⟨g, rfl⟩))
        (Subgroup.subset_closure ⟨g * k, rfl⟩))
    exact hle hn
  let Z : Subgroup ↥K := Subgroup.center ↥K
  let Lb : Subgroup (↥K ⧸ Z) := L.map (QuotientGroup.mk' Z)
  haveI : Lb.Normal := hLn.map _ (QuotientGroup.mk'_surjective Z)
  have hLb2 : IsPGroup 2 Lb := by
    intro x
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.1 x.2
    have hδl : δ l ∈ T₀ := hLδ hl
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (Subgroup.centralizer ({d} : Set X))) ⟨δ l, hδl⟩
    refine ⟨n, ?_⟩
    have h1 : δ (l ^ (2 ^ n)) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hn
    have hZl : l ^ (2 ^ n) ∈ Z := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext
        (commute_of_diagProd_eq_one hp hK hd hdK (l ^ (2 ^ n)).2 h1 g g.2).symm
    apply Subtype.ext
    have : ((x : ↥K ⧸ Z)) ^ (2 ^ n) = 1 := by
      rw [← hlx, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hZl
    simpa using this
  haveI : IsSimpleGroup (↥K ⧸ Z) := hK.2.2.2
  have hnab : ∃ a b : ↥K ⧸ Z, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have h1 : ∀ k : ↥K, (QuotientGroup.mk k : ↥K ⧸ Z) = 1 := by
      intro k
      have hk : k ∈ commutator ↥K := by rw [hK.2.2.1]; exact Subgroup.mem_top k
      have hle : commutator ↥K ≤ (QuotientGroup.mk' Z).ker := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcon _ _
      exact (MonoidHom.mem_ker.1 (hle hk))
    have : Subsingleton (↥K ⧸ Z) := by
      constructor
      intro a b
      induction a using QuotientGroup.induction_on
      induction b using QuotientGroup.induction_on
      rw [h1, h1]
    exact not_subsingleton (↥K ⧸ Z) this
  have hLb : Lb = ⊥ := CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb.eq_bot_of_normal_isPGroup
    hnab Lb hLb2
  have hucen : ∀ k : ↥K, u k ∈ Z := by
    intro k
    have : (QuotientGroup.mk' Z) (u k) ∈ Lb := Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨k, rfl⟩)
    rw [hLb, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  have hu_mul : ∀ k k' : ↥K, u (k * k') = u k * u k' := by
    intro k k'
    have hc := Subgroup.mem_center_iff.1 (hucen k') (tk k * k⁻¹)
    calc u (k * k') = tk k * (tk k' * k'⁻¹) * k⁻¹ := by simp only [u, htk_mul]; group
      _ = (tk k * k⁻¹) * (k * (tk k' * k'⁻¹) * k⁻¹) := by group
      _ = (tk k * k⁻¹) * (tk k' * k'⁻¹) := by
        congr 1
        have := Subgroup.mem_center_iff.1 (hucen k') k
        calc k * (tk k' * k'⁻¹) * k⁻¹ = (k * u k') * k⁻¹ := rfl
          _ = (u k' * k) * k⁻¹ := by rw [this]
          _ = u k' := mul_inv_cancel_right _ _
          _ = tk k' * k'⁻¹ := rfl
  let ψ : ↥K →* ↥K :=
    { toFun := u
      map_one' := by simp [u, tk]
      map_mul' := hu_mul }
  have hψ : ∀ k, ψ k = 1 := by
    have hle : commutator ↥K ≤ ψ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 (hucen a) (ψ b)).symm
    intro k
    have hk : k ∈ commutator ↥K := by rw [hK.2.2.1]; exact Subgroup.mem_top k
    exact MonoidHom.mem_ker.1 (hle hk)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : tk ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹ = 1 := hψ ⟨k, hk⟩
  have h2 : tk ⟨k, hk⟩ = ⟨k, hk⟩ := mul_inv_eq_one.1 h1
  have h3 : t * k * t⁻¹ = k := congrArg Subtype.val h2
  calc k * t = (t * k * t⁻¹) * t := by rw [h3]
    _ = t * k := by group

theorem pCoreOf_le_centralizer_of_mem_centralizer {K : Subgroup X} (hK : IsComponentOf K ⊤) {d : X}
    (hd : d ∈ Subgroup.centralizer (K : Set X))
    (hTN : pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X)) :
    pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.centralizer (K : Set X) := by
  have hKC : K ≤ Subgroup.centralizer ({d} : Set X) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hd k hk
  have hS2 : ∀ s ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set X)), ∃ m : ℕ, s ^ (2 ^ m) = 1 :=
    fun s hs => by
      obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
        (Subgroup.centralizer ({d} : Set X))) ⟨s, hs⟩
      exact ⟨m, congrArg Subtype.val hm⟩
  exact le_centralizer_of_normalized_by hK hS2 hTN (fun k hk s hs =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ (hKC hk)) s).1 hs)

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

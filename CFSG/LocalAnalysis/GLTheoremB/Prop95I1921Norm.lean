module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18Claim
public import CFSG.LocalAnalysis.GLTheoremB.Prop95NonAbDiag
public import CFSG.LocalAnalysis.GLTheoremB.BlockDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18

variable {X : Type} [Group X] [Finite X]

theorem not_central_sylow_K {p : ℕ} [hpF : Fact p.Prime] {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hOK : GLAPPrimeCore p ↥K = ⊥) (P : Sylow p ↥K)
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
  have hndvd : ¬ p ∣ Nat.card H := by
    rw [hPidx]
    exact Sylow.not_dvd_index P
  have hHn : H.Normal := by
    refine ⟨fun h hh g => ?_⟩
    have hg : g ∈ (P : Subgroup ↥K) ⊔ H := by
      rw [hH.sup_eq_top]
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
  have hcop : Nat.Coprime p (Nat.card H) := (Nat.Prime.coprime_iff_not_dvd hpF.out).2 hndvd
  have hHle : H ≤ CFSG.pPrimeCore p ↥K := le_sSup ⟨hHn, hcop⟩
  have hOK' : CFSG.pPrimeCore p ↥K = ⊥ := hOK
  rw [hOK'] at hHle
  have hH1 : H = ⊥ := eq_bot_iff.2 hHle
  have hcardH1 : Nat.card H = 1 := by rw [hH1, Subgroup.card_bot]
  have hPtop : (P : Subgroup ↥K) = ⊤ := by
    have h1 : (P : Subgroup ↥K).index = 1 := by
      rw [← hPidx, hcardH1]
    exact Subgroup.index_eq_one.1 h1
  have hcen : Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro g
    exact (hP x (by rw [hPtop]; exact Subgroup.mem_top x) g).symm
  have hsubsing : Subsingleton (↥K ⧸ Subgroup.center ↥K) := by
    constructor
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rw [QuotientGroup.eq, hcen]
    exact Subgroup.mem_top _
  obtain ⟨_, hs⟩ := hK.2.2
  exact not_subsingleton (↥K ⧸ Subgroup.center ↥K) hsubsing

theorem claim_card_K {p : ℕ} [hpF : Fact p.Prime] (hp2 : p ≠ 2) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hOK : GLAPPrimeCore p ↥K = ⊥) :
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
      refine not_central_sylow_K hK hOK P ?_
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


theorem pCoreOf_centralizer_le_normalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hO : GLAPPrimeCore p ↥K = ⊥)
    {B : Subgroup X} (hB : IsPGroup p B) :
    pCoreOf 2 (Subgroup.centralizer (B : Set X)) ≤ Subgroup.normalizer (K : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact claim_card_K hp2 hK hO _ B hB rfl

theorem pCoreOf_centralizer_singleton_le_normalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hO : GLAPPrimeCore p ↥K = ⊥) {d : X}
    (hd : d ^ p = 1) :
    pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X) := by
  have hB : IsPGroup p (Subgroup.zpowers d) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hd)
  have hCB : Subgroup.centralizer ((Subgroup.zpowers d : Subgroup X) : Set X) =
      Subgroup.centralizer ({d} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have := pCoreOf_centralizer_le_normalizer hp hp2 hK hO hB
  rwa [hCB] at this


section Diag

@[expose] def cpow (d : X) (i : ℕ) (k : X) : X := d ^ i * k * (d ^ i)⁻¹

theorem cpow_mul (d : X) (i : ℕ) (k k' : X) : cpow d i (k * k') = cpow d i k * cpow d i k' := by
  simp only [cpow]; group

theorem cpow_one' (d : X) (i : ℕ) : cpow d i 1 = 1 := by simp [cpow]

theorem cpow_zero (d k : X) : cpow d 0 k = k := by simp [cpow]

theorem cpow_succ (d : X) (i : ℕ) (k : X) : d * cpow d i k * d⁻¹ = cpow d (i + 1) k := by
  simp only [cpow, pow_succ']; group

theorem cpow_self {p : ℕ} {d : X} (hd : d ^ p = 1) (k : X) : cpow d p k = k := by
  simp [cpow, hd]

theorem cpow_conj {d t : X} (hdt : t * d = d * t) (i : ℕ) (k : X) :
    t * cpow d i k * t⁻¹ = cpow d i (t * k * t⁻¹) := by
  have h : t * d ^ i * t⁻¹ = d ^ i := by
    have := (Commute.pow_right (show Commute t d from hdt) i).eq
    rw [mul_inv_eq_iff_eq_mul]; exact this
  have h' : t * (d ^ i)⁻¹ * t⁻¹ = (d ^ i)⁻¹ := by
    calc t * (d ^ i)⁻¹ * t⁻¹ = (t * d ^ i * t⁻¹)⁻¹ := by group
      _ = (d ^ i)⁻¹ := by rw [h]
  simp only [cpow]
  calc t * (d ^ i * k * (d ^ i)⁻¹) * t⁻¹
      = (t * d ^ i * t⁻¹) * (t * k * t⁻¹) * (t * (d ^ i)⁻¹ * t⁻¹) := by group
    _ = d ^ i * (t * k * t⁻¹) * (d ^ i)⁻¹ := by rw [h, h']

theorem list_prod_map_mul {α : Type*} [Group α] (f g : ℕ → α) :
    ∀ l : List ℕ, l.Nodup → (∀ i ∈ l, ∀ j ∈ l, i ≠ j → Commute (g i) (f j)) →
      (l.map (fun i => f i * g i)).prod = (l.map f).prod * (l.map g).prod := by
  intro l
  induction l with
  | nil => intros; simp
  | cons i l ih =>
    intro hnd hc
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.prod_cons]
    rw [ih hnd.2 (fun a ha b hb hab =>
      hc a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab)]
    have hcomm : Commute (g i) ((l.map f).prod) := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact hc i List.mem_cons_self j (List.mem_cons_of_mem _ hj) (fun h => hnd.1 (h ▸ hj))
    calc f i * g i * ((l.map f).prod * (l.map g).prod)
        = f i * (g i * (l.map f).prod) * (l.map g).prod := by group
      _ = f i * ((l.map f).prod * g i) * (l.map g).prod := by rw [hcomm.eq]
      _ = f i * (l.map f).prod * (g i * (l.map g).prod) := by group

@[expose] def diagProd (d : X) (p : ℕ) (k : X) : X :=
  ((List.range p).map (fun i => cpow d i k)).prod

theorem diagProd_succ (d : X) (q : ℕ) (k : X) :
    diagProd d (q + 1) k = k * ((List.range q).map (fun i => cpow d (i + 1) k)).prod := by
  simp only [diagProd]
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, cpow_zero]
  rfl

theorem map_cpow_succ {p : ℕ} {d : X} (hd : d ^ p = 1) (hp : 1 ≤ p) (k : X) :
    ((List.range p).map (fun i => d * cpow d i k * d⁻¹)).prod =
      ((List.range (p - 1)).map (fun i => cpow d (i + 1) k)).prod * k := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [cpow_succ, Nat.add_sub_cancel]
  rw [List.range_succ, List.map_append, List.prod_append]
  simp [cpow_self hd]

variable {p : ℕ}

theorem map_conj_ne (hp : p.Prime) {K : Subgroup X} {d : X} (hd : d ^ p = 1)
    (hdK : d ∉ Subgroup.normalizer (K : Set X)) {i j : ℕ} (hij : i < j) (hjp : j < p) :
    K.map (MulAut.conj (d ^ i)).toMonoidHom ≠ K.map (MulAut.conj (d ^ j)).toMonoidHom := by
  intro h
  obtain ⟨m, hm⟩ : ∃ m, j = i + m := ⟨j - i, by omega⟩
  have hm0 : 0 < m := by omega
  have hmp : m < p := by omega
  have hjm : d ^ j = d ^ i * d ^ m := by rw [← pow_add, hm]
  have hg : d ^ m ∈ Subgroup.normalizer (K : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : d ^ j * x * (d ^ j)⁻¹ ∈ K.map (MulAut.conj (d ^ j)).toMonoidHom := ⟨x, hx, rfl⟩
      rw [← h] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have hyx' : d ^ i * y * (d ^ i)⁻¹ = d ^ i * (d ^ m * x * (d ^ m)⁻¹) * (d ^ i)⁻¹ := by
        have this : d ^ i * y * (d ^ i)⁻¹ = d ^ j * x * (d ^ j)⁻¹ := hyx
        rw [this, hjm]; group
      have : y = d ^ m * x * (d ^ m)⁻¹ := by
        have h2 := mul_left_cancel (mul_right_cancel hyx')
        exact h2
      rw [← this]; exact hy
    · intro hx
      have h1 : d ^ j * x * (d ^ j)⁻¹ ∈ K.map (MulAut.conj (d ^ i)).toMonoidHom :=
        ⟨d ^ m * x * (d ^ m)⁻¹, hx, by
          show d ^ i * (d ^ m * x * (d ^ m)⁻¹) * (d ^ i)⁻¹ = d ^ j * x * (d ^ j)⁻¹
          rw [hjm]; group⟩
      rw [h] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have hyx' : d ^ j * y * (d ^ j)⁻¹ = d ^ j * x * (d ^ j)⁻¹ := hyx
      have : y = x := mul_left_cancel (mul_right_cancel hyx')
      rw [← this]; exact hy
  have hord : orderOf d = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hd) with h1 | h1
    · exact absurd (by rw [orderOf_eq_one_iff.1 h1]; exact Subgroup.one_mem _) hdK
    · exact h1
  have hcop : Nat.Coprime m (orderOf d) := by
    rw [hord]
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun hdv =>
      absurd (Nat.le_of_dvd hm0 hdv) (by omega))))
  obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime hcop
  apply hdK
  rw [← hs]
  exact Subgroup.pow_mem _ hg s

theorem commute_cpow (hp : p.Prime) {K : Subgroup X} (hK : IsComponentOf K ⊤) {d : X}
    (hd : d ^ p = 1) (hdK : d ∉ Subgroup.normalizer (K : Set X)) {i j : ℕ} (hip : i < p)
    (hjp : j < p) (hij : i ≠ j) {k k' : X} (hk : k ∈ K) (hk' : k' ∈ K) :
    Commute (cpow d i k) (cpow d j k') := by
  have key : ∀ {i j : ℕ}, i < j → j < p → ∀ {k k' : X}, k ∈ K → k' ∈ K →
      cpow d i k * cpow d j k' = cpow d j k' * cpow d i k := by
    intro i j hij hjp k k' hk hk'
    have hKi := isComponentOf_conj hK (d ^ i)
    have hKj := isComponentOf_conj hK (d ^ j)
    exact comp_comm hKi hKj (map_conj_ne hp hd hdK hij hjp) ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact key h hjp hk hk'
  · exact (key h hip hk' hk).symm

end Diag

section Diag2

variable {p : ℕ}

theorem diagProd_one (d : X) (p : ℕ) : diagProd d p 1 = 1 := by
  simp [diagProd, cpow_one']

theorem diagProd_mul (hp : p.Prime) {K : Subgroup X} (hK : IsComponentOf K ⊤) {d : X}
    (hd : d ^ p = 1) (hdK : d ∉ Subgroup.normalizer (K : Set X)) {k k' : X} (hk : k ∈ K)
    (hk' : k' ∈ K) : diagProd d p (k * k') = diagProd d p k * diagProd d p k' := by
  unfold diagProd
  have h1 : (List.range p).map (fun i => cpow d i (k * k')) =
      (List.range p).map (fun i => cpow d i k * cpow d i k') :=
    List.map_congr_left (fun i _ => cpow_mul d i k k')
  rw [h1]
  exact list_prod_map_mul (fun i => cpow d i k) (fun i => cpow d i k') (List.range p)
    List.nodup_range (fun i hi j hj hij =>
      commute_cpow hp hK hd hdK (List.mem_range.1 hi) (List.mem_range.1 hj) hij hk' hk)

theorem diagProd_comm_d (hp : p.Prime) {K : Subgroup X} (hK : IsComponentOf K ⊤) {d : X}
    (hd : d ^ p = 1) (hdK : d ∉ Subgroup.normalizer (K : Set X)) {k : X} (hk : k ∈ K) :
    d * diagProd d p k * d⁻¹ = diagProd d p k := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have h1 : d * diagProd d p k * d⁻¹ =
      ((List.range p).map (fun i => d * cpow d i k * d⁻¹)).prod := by
    have h := map_list_prod (MulAut.conj d) ((List.range p).map (fun i => cpow d i k))
    simp only [MulAut.conj_apply, List.map_map] at h
    exact h
  rw [h1, map_cpow_succ hd hp1 k]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [diagProd_succ, Nat.add_sub_cancel]
  have hcomm : Commute k ((List.range q).map (fun i => cpow d (i + 1) k)).prod := by
    apply Commute.list_prod_right
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have := commute_cpow hp hK hd hdK (by omega : 0 < q + 1)
      (by have := List.mem_range.1 hi; omega : i + 1 < q + 1) (by omega : 0 ≠ i + 1) hk hk
    rwa [cpow_zero] at this
  exact hcomm.symm.eq

theorem commute_of_diagProd_eq_one (hp : p.Prime) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    {d : X} (hd : d ^ p = 1) (hdK : d ∉ Subgroup.normalizer (K : Set X)) {k : X} (hk : k ∈ K)
    (h : diagProd d p k = 1) : ∀ k' ∈ K, k * k' = k' * k := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  rw [diagProd_succ] at h
  intro k' hk'
  have hkM : k = (((List.range q).map (fun i => cpow d (i + 1) k)).prod)⁻¹ :=
    eq_inv_of_mul_eq_one_left h
  have hMc : Commute ((List.range q).map (fun i => cpow d (i + 1) k)).prod k' := by
    apply Commute.list_prod_left
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have := commute_cpow hp hK hd hdK (by have := List.mem_range.1 hi; omega : i + 1 < q + 1)
      (by omega : 0 < q + 1) (by omega : i + 1 ≠ 0) hk hk'
    rwa [cpow_zero] at this
  rw [hkM]
  exact hMc.inv_left.eq

@[expose] noncomputable def diagHom (hp : p.Prime) {K : Subgroup X} (hK : IsComponentOf K ⊤) {d : X}
    (hd : d ^ p = 1) (hdK : d ∉ Subgroup.normalizer (K : Set X)) : ↥K →* X where
  toFun k := diagProd d p (k : X)
  map_one' := diagProd_one d p
  map_mul' k k' := diagProd_mul hp hK hd hdK k.2 k'.2

end Diag2

section B2

variable {p : ℕ}

theorem diagProd_conj {d t : X} (hdt : t * d = d * t) (p : ℕ) (k : X) :
    t * diagProd d p k * t⁻¹ = diagProd d p (t * k * t⁻¹) := by
  unfold diagProd
  have h := map_list_prod (MulAut.conj t) ((List.range p).map (fun i => cpow d i k))
  simp only [MulAut.conj_apply, List.map_map] at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i _
  exact cpow_conj hdt i k

theorem le_centralizer_of_not_mem_normalizer (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hO : GLAPPrimeCore p ↥K = ⊥) {d : X}
    (hd : d ^ p = 1) (hdK : d ∉ Subgroup.normalizer (K : Set X)) {T : Subgroup X}
    (hT : T ≤ pCoreOf 2 (Subgroup.centralizer ({d} : Set X))) :
    T ≤ Subgroup.centralizer (K : Set X) := by
  set T₀ := pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) with hT₀
  refine le_trans hT ?_
  intro t ht
  have htN : t ∈ Subgroup.normalizer (K : Set X) :=
    pCoreOf_centralizer_singleton_le_normalizer hp hp2 hK hO hd ht
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

end B2

section B3

theorem normal_two_subgroup_le_center {K : Subgroup X} (hK : IsComponentOf K ⊤)
    {M : Subgroup ↥K} [M.Normal] (hM : ∀ m ∈ M, ∃ n : ℕ, m ^ (2 ^ n) = 1) :
    M ≤ Subgroup.center ↥K := by
  let Z : Subgroup ↥K := Subgroup.center ↥K
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
  let Mb : Subgroup (↥K ⧸ Z) := M.map (QuotientGroup.mk' Z)
  haveI : Mb.Normal := (inferInstance : M.Normal).map _ (QuotientGroup.mk'_surjective Z)
  have hMb2 : IsPGroup 2 Mb := by
    intro x
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨n, hn⟩ := hM m hm
    refine ⟨n, Subtype.ext ?_⟩
    have : ((x : ↥K ⧸ Z)) ^ (2 ^ n) = 1 := by
      rw [← hmx, ← map_pow, hn, map_one]
    simpa using this
  have hMb : Mb = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb.eq_bot_of_normal_isPGroup hnab Mb hMb2
  intro m hm
  have : (QuotientGroup.mk' Z) m ∈ Mb := Subgroup.mem_map_of_mem _ hm
  rw [hMb, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff _).1 this

theorem centralizes_of_commutators_central {K : Subgroup X} (hK : IsComponentOf K ⊤) {t : X}
    (htN : t ∈ Subgroup.normalizer (K : Set X))
    (hcen : ∀ k ∈ K, ∀ k' ∈ K, (t * k * t⁻¹ * k⁻¹) * k' = k' * (t * k * t⁻¹ * k⁻¹)) :
    t ∈ Subgroup.centralizer (K : Set X) := by
  let tk : ↥K → ↥K := fun k =>
    ⟨t * (k : X) * t⁻¹, (Subgroup.mem_normalizer_iff.1 htN k).1 k.2⟩
  have htk_mul : ∀ k k' : ↥K, tk (k * k') = tk k * tk k' := fun k k' =>
    Subtype.ext (by simp only [tk, Subgroup.coe_mul]; group)
  let u : ↥K → ↥K := fun k => tk k * k⁻¹
  have hucen : ∀ k k' : ↥K, u k * k' = k' * u k := fun k k' =>
    Subtype.ext (hcen k k.2 k' k'.2)
  have hu_mul : ∀ k k' : ↥K, u (k * k') = u k * u k' := by
    intro k k'
    calc u (k * k') = tk k * (tk k' * k'⁻¹) * k⁻¹ := by simp only [u, htk_mul]; group
      _ = (tk k * k⁻¹) * (k * (tk k' * k'⁻¹) * k⁻¹) := by group
      _ = (tk k * k⁻¹) * (tk k' * k'⁻¹) := by
        congr 1
        have := hucen k' k
        calc k * (tk k' * k'⁻¹) * k⁻¹ = (k * u k') * k⁻¹ := rfl
          _ = (u k' * k) * k⁻¹ := by rw [← this]
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
      exact hucen a (ψ b)
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

theorem le_centralizer_of_normalized_by {K : Subgroup X} (hK : IsComponentOf K ⊤)
    {S : Subgroup X} (hS2 : ∀ s ∈ S, ∃ n : ℕ, s ^ (2 ^ n) = 1)
    (hSN : S ≤ Subgroup.normalizer (K : Set X)) (hKS : ∀ k ∈ K, ∀ s ∈ S, k * s * k⁻¹ ∈ S) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  let M : Subgroup ↥K := S.subgroupOf K
  haveI : M.Normal := ⟨fun m hm g => by
    have hmS : (m : X) ∈ S := hm
    show ((g * m * g⁻¹ : ↥K) : X) ∈ S
    simpa using hKS g g.2 m hmS⟩
  have hMc : M ≤ Subgroup.center ↥K := normal_two_subgroup_le_center hK (fun m hm => by
    obtain ⟨n, hn⟩ := hS2 m hm
    exact ⟨n, Subtype.ext (by simpa using hn)⟩)
  intro s hs
  refine centralizes_of_commutators_central hK (hSN hs) ?_
  intro k hk k' hk'
  have hksK : s * k * s⁻¹ * k⁻¹ ∈ K := by
    refine K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hSN hs) k).1 hk) (K.inv_mem hk)
  have hksS : s * k * s⁻¹ * k⁻¹ ∈ S := by
    have h1 : k * s⁻¹ * k⁻¹ ∈ S := hKS k hk s⁻¹ (S.inv_mem hs)
    have : s * k * s⁻¹ * k⁻¹ = s * (k * s⁻¹ * k⁻¹) := by group
    rw [this]; exact S.mul_mem hs h1
  have hmem : (⟨s * k * s⁻¹ * k⁻¹, hksK⟩ : ↥K) ∈ M := hksS
  have := Subgroup.mem_center_iff.1 (hMc hmem) ⟨k', hk'⟩
  exact (congrArg Subtype.val this).symm

end B3

section B4

theorem mem_inducedAutGroup {W K : Subgroup X} {φ : MulAut ↥K} :
    φ ∈ inducedAutGroup W K ↔ ∃ (w : X) (hw : w ∈ Subgroup.normalizer (K : Set X)),
      w ∈ W ∧ K.normalizerMonoidHom ⟨w, hw⟩ = φ := by
  unfold inducedAutGroup
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨⟨w, hw⟩, hwW, rfl⟩
    exact ⟨w, hw, hwW, rfl⟩
  · rintro ⟨w, hw, hwW, rfl⟩
    exact ⟨⟨w, hw⟩, hwW, rfl⟩

theorem normalizerMonoidHom_apply_coe' {K : Subgroup X} {w : X}
    (hw : w ∈ Subgroup.normalizer (K : Set X)) (k : ↥K) :
    ((K.normalizerMonoidHom ⟨w, hw⟩ k : ↥K) : X) = w * k * w⁻¹ := rfl

theorem normalizerMonoidHom_eq_one_iff {K : Subgroup X} {w : X}
    (hw : w ∈ Subgroup.normalizer (K : Set X)) :
    K.normalizerMonoidHom ⟨w, hw⟩ = 1 ↔ w ∈ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : ↥K) : X)) h
    simp only [normalizerMonoidHom_apply_coe', MulAut.one_apply] at this
    calc k * w = (w * k * w⁻¹) * w := by rw [this]
      _ = w * k := by group
  · intro h
    ext k
    rw [normalizerMonoidHom_apply_coe', MulAut.one_apply]
    calc w * (k : X) * w⁻¹ = (k : X) * w * w⁻¹ := by rw [← h k k.2]
      _ = k := by group

theorem inducedAutGroup_eq_bot_iff {W K : Subgroup X}
    (hW : W ≤ Subgroup.normalizer (K : Set X)) :
    inducedAutGroup W K = ⊥ ↔ W ≤ Subgroup.centralizer (K : Set X) := by
  constructor
  · intro h w hw
    have hmem : K.normalizerMonoidHom ⟨w, hW hw⟩ ∈ inducedAutGroup W K :=
      mem_inducedAutGroup.2 ⟨w, hW hw, hw, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact (normalizerMonoidHom_eq_one_iff (hW hw)).1 hmem
  · intro h
    rw [eq_bot_iff]
    intro φ hφ
    obtain ⟨w, hw, hwW, rfl⟩ := mem_inducedAutGroup.1 hφ
    rw [Subgroup.mem_bot]
    exact (normalizerMonoidHom_eq_one_iff hw).2 (h hwW)

end B4

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

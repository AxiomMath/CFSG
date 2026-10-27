module

public import CFSG.CGT.PushingUpLit.Orth.OrthL1
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.CGT.PushingUpLit.Orth

open Equiv

variable {G : Type*} [Group G] {M Q : Subgroup G}

theorem exists_mem_normalizer_of_lt' [Finite G] {V W : Subgroup G} (hW : IsPGroup 2 W)
    (hVW : V < W) : ∃ w ∈ W, w ∉ V ∧ w ∈ Subgroup.normalizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent W := hW.isNilpotent
  have hlt : V.subgroupOf W < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hVW.ne (le_antisymm hVW.le ?_)
    intro w hw
    have : (⟨w, hw⟩ : W) ∈ V.subgroupOf W := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨w, hwN, hwV⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨w, w.2, fun h => hwV (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    have := (Subgroup.mem_normalizer_iff.mp hwN ⟨r, hVW.le hr⟩).mp
      (Subgroup.mem_subgroupOf.mpr hr)
    exact Subgroup.mem_subgroupOf.mp this
  · intro hr
    have hrW : r ∈ W := by
      have h1 : (w : G) * r * (w : G)⁻¹ ∈ W := hVW.le hr
      have : r = (w : G)⁻¹ * ((w : G) * r * (w : G)⁻¹) * w := by group
      rw [this]
      exact W.mul_mem (W.mul_mem (W.inv_mem w.2) h1) w.2
    have := (Subgroup.mem_normalizer_iff.mp hwN ⟨r, hrW⟩).mpr (Subgroup.mem_subgroupOf.mpr hr)
    exact Subgroup.mem_subgroupOf.mp this

def prodSub (K P T : Subgroup G) (hP : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P) (hT : T ≤ K) :
    Subgroup G where
  carrier := {x | ∃ p ∈ P, ∃ t ∈ T, x = p * t}
  mul_mem' := by
    rintro _ _ ⟨p, hp, t, ht, rfl⟩ ⟨p', hp', t', ht', rfl⟩
    refine ⟨p * (t * p' * t⁻¹), P.mul_mem hp (hP t (hT ht) p' hp'), t * t', T.mul_mem ht ht', ?_⟩
    group
  one_mem' := ⟨1, P.one_mem, 1, T.one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨p, hp, t, ht, rfl⟩
    refine ⟨t⁻¹ * p⁻¹ * (t⁻¹)⁻¹, ?_, t⁻¹, T.inv_mem ht, ?_⟩
    · exact hP t⁻¹ (K.inv_mem (hT ht)) p⁻¹ (P.inv_mem hp)
    · group

theorem P_le_prodSub {K P T : Subgroup G} {hP : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P} {hT : T ≤ K} :
    P ≤ prodSub K P T hP hT := fun p hp => ⟨p, hp, 1, T.one_mem, by simp⟩

theorem T_le_prodSub {K P T : Subgroup G} {hP : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P} {hT : T ≤ K} :
    T ≤ prodSub K P T hP hT := fun t ht => ⟨1, P.one_mem, t, ht, by simp⟩

theorem prodSub_eq_sup {K P T : Subgroup G} {hP : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P}
    {hT : T ≤ K} : prodSub K P T hP hT = P ⊔ T := by
  apply le_antisymm
  · rintro _ ⟨p, hp, t, ht, rfl⟩
    exact (P ⊔ T).mul_mem (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right ht)
  · exact sup_le P_le_prodSub T_le_prodSub

theorem isPGroup_prodSub {K P T : Subgroup G} {hP : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P}
    {hT : T ≤ K} (hPp : IsPGroup 2 P) (hTp : IsPGroup 2 T) :
    IsPGroup 2 (prodSub K P T hP hT) := by
  rw [prodSub_eq_sup]
  refine hPp.to_sup_of_normal_left' hTp ?_
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · exact fun hp => hP t (hT ht) p hp
  · intro h
    have := hP t⁻¹ (K.inv_mem (hT ht)) _ h
    simpa [mul_assoc] using this

theorem chain_le {K P H : Subgroup G} {z : G} (hP : IsO2 K P)
    (hC : K ⊓ Subgroup.centralizer (P : Set G) ≤ P) (hz2 : z * z = 1)
    (hzK : ∀ k ∈ K, k * z * k⁻¹ = z) (hHK : H ≤ K)
    (hcomm : ∀ p ∈ P, ∀ h ∈ H, p * h * p⁻¹ * h⁻¹ = 1 ∨ p * h * p⁻¹ * h⁻¹ = z) : H ≤ P := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hmul : ∀ c₁ c₂ : G, (c₁ = 1 ∨ c₁ = z) → (c₂ = 1 ∨ c₂ = z) →
      (c₁ * c₂ = 1 ∨ c₁ * c₂ = z) := by
    rintro c₁ c₂ (rfl | rfl) (rfl | rfl)
    · left; simp
    · right; simp
    · right; simp
    · left; exact hz2
  have hconj : ∀ k ∈ K, ∀ c : G, (c = 1 ∨ c = z) → (k * c * k⁻¹ = 1 ∨ k * c * k⁻¹ = z) := by
    intro k hk c hc
    rcases hc with rfl | rfl
    · left; group
    · right; exact hzK k hk
  have hinv : ∀ c : G, (c = 1 ∨ c = z) → (c⁻¹ = 1 ∨ c⁻¹ = z) := by
    rintro c (rfl | rfl)
    · left; simp
    · right; exact hzinv
  let C₁ : Subgroup G :=
    { carrier := {k | k ∈ K ∧ ∀ p ∈ P, p * k * p⁻¹ * k⁻¹ = 1 ∨ p * k * p⁻¹ * k⁻¹ = z}
      mul_mem' := by
        rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
        refine ⟨K.mul_mem haK hbK, fun p hp => ?_⟩
        have e : p * (a * b) * p⁻¹ * (a * b)⁻¹ =
            (p * a * p⁻¹ * a⁻¹) * (a * (p * b * p⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact hmul _ _ (ha p hp) (hconj a haK _ (hb p hp))
      one_mem' := ⟨K.one_mem, fun p _ => Or.inl (by group)⟩
      inv_mem' := by
        rintro a ⟨haK, ha⟩
        refine ⟨K.inv_mem haK, fun p hp => ?_⟩
        have e : p * a⁻¹ * p⁻¹ * (a⁻¹)⁻¹ = (a⁻¹ * (p * a * p⁻¹ * a⁻¹) * a)⁻¹ := by group
        rw [e]
        apply hinv
        have := hconj a⁻¹ (K.inv_mem haK) _ (ha p hp)
        simpa using this }
  have hC₁K : C₁ ≤ K := fun k hk => hk.1
  have hC₁norm : ∀ k ∈ K, ∀ c ∈ C₁, k * c * k⁻¹ ∈ C₁ := by
    intro k hk c hc
    refine ⟨K.mul_mem (K.mul_mem hk hc.1) (K.inv_mem hk), fun p hp => ?_⟩
    have e : p * (k * c * k⁻¹) * p⁻¹ * (k * c * k⁻¹)⁻¹ =
        k * ((k⁻¹ * p * k) * c * (k⁻¹ * p * k)⁻¹ * c⁻¹) * k⁻¹ := by group
    rw [e]
    have hp' : k⁻¹ * p * k ∈ P := by
      have := hP.normal k⁻¹ (K.inv_mem hk) p hp
      simpa using this
    exact hconj k hk _ (hc.2 _ hp')
  have hC₁p : IsPGroup 2 C₁ := by
    intro c
    have hcsq : (c : G) * (c : G) ∈ P := by
      apply hC
      refine ⟨K.mul_mem c.2.1 c.2.1, ?_⟩
      show (c : G) * (c : G) ∈ Subgroup.centralizer (P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have h1 := c.2.2 p hp
      have e : p * ((c : G) * c) * p⁻¹ * ((c : G) * c)⁻¹ =
          (p * c * p⁻¹ * (c : G)⁻¹) * ((c : G) * (p * c * p⁻¹ * (c : G)⁻¹) * (c : G)⁻¹) := by
        group
      have h2 : p * ((c : G) * c) * p⁻¹ * ((c : G) * c)⁻¹ = 1 := by
        rw [e]
        rcases h1 with h1 | h1
        · rw [h1]; group
        · have : (c : G) * z * (c : G)⁻¹ = z := hzK c c.2.1
          rw [h1, this, hz2]
      calc p * ((c : G) * c) = (p * ((c : G) * c) * p⁻¹ * ((c : G) * c)⁻¹) * ((c : G) * c) * p := by
            group
        _ = (c : G) * c * p := by rw [h2]; group
    obtain ⟨j, hj⟩ := hP.pgroup ⟨(c : G) * c, hcsq⟩
    refine ⟨j + 1, ?_⟩
    apply Subtype.ext
    have h3 : ((c : G) * c) ^ (2 ^ j) = 1 := congrArg Subtype.val hj
    show (c : G) ^ (2 ^ (j + 1)) = 1
    rw [pow_succ', pow_mul, pow_two]
    exact h3
  have hle := hP.max C₁ hC₁K hC₁norm hC₁p
  intro h hh
  exact hle ⟨hHK hh, fun p hp => hcomm p hp h hh⟩

namespace OrthCfg

variable (C : OrthCfg G M Q)

include C

theorem T_le_pre_H2 : C.T ≤ C.pre H2 := C.pre_mono (Subgroup.zpowers_le.2 tau_mem_H2)

theorem inf_M_eq_pre {v : Vec5} (hv : v = v2 ∨ v = v3) :
    Subgroup.centralizer ({C.elt v} : Set G) ⊓ M = C.pre H2 := by
  ext x
  constructor
  · rintro ⟨hxK, hxM⟩
    refine C.mem_pre.2 ⟨hxM, ?_⟩
    have := (C.mem_centralizer_elt_iff hxM v).1 hxK
    rcases hv with rfl | rfl
    · exact (permAct_v2 _).1 this
    · exact (permAct_v3 _).1 this
  · intro hx
    refine Subgroup.mem_inf.2 ⟨?_, C.pre_le_M _ hx⟩
    have hH : isH2 (C.th x) := C.th_mem_of_mem_pre hx
    rw [C.mem_centralizer_elt_iff (C.pre_le_M _ hx)]
    rcases hv with rfl | rfl
    · exact (permAct_v2 _).2 hH
    · exact (permAct_v3 _).2 hH

theorem conj_Q1_of_normalizer_T {w : G} (hw : w ∈ Subgroup.normalizer (C.T : Set G)) {y : G}
    (hy : y ∈ C.Q1) : w * y * w⁻¹ ∈ C.Q1 := by
  have hwT : ∀ t, t ∈ C.T ↔ w * t * w⁻¹ ∈ C.T := fun t => Subgroup.mem_normalizer_iff.1 hw t
  refine Subgroup.mem_inf.2 ⟨(hwT y).1 (Subgroup.mem_inf.1 hy).1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have ht' : w⁻¹ * t * w ∈ C.T := by
    apply (hwT (w⁻¹ * t * w)).2
    have : w * (w⁻¹ * t * w) * w⁻¹ = t := by group
    rw [this]; exact ht
  have h := C.Q1_comm_T hy ht'
  calc t * (w * y * w⁻¹) = w * ((w⁻¹ * t * w) * y) * w⁻¹ := by group
    _ = w * (y * (w⁻¹ * t * w)) * w⁻¹ := by rw [h]
    _ = w * y * w⁻¹ * t := by group

theorem mem_normalizer_Q1_of_normalizer_T {w : G} (hw : w ∈ Subgroup.normalizer (C.T : Set G)) :
    w ∈ Subgroup.normalizer (C.Q1 : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨C.conj_Q1_of_normalizer_T hw, fun hy => ?_⟩
  have hw' : w⁻¹ ∈ Subgroup.normalizer (C.T : Set G) := Subgroup.inv_mem _ hw
  have := C.conj_Q1_of_normalizer_T hw' hy
  have e : w⁻¹ * (w * y * w⁻¹) * w⁻¹⁻¹ = y := by group
  rwa [e] at this

theorem normalizer_T_le_M [Finite G]
    (hrig : ∀ v : Vec5, Rigid v → Subgroup.centralizer ({C.elt v} : Set G) ≤ M) {w : G}
    (hw : w ∈ Subgroup.normalizer (C.T : Set G)) : w ∈ M :=
  C.normalizer_Q1_le hrig (C.mem_normalizer_Q1_of_normalizer_T hw)

theorem witness_structure [Finite G]
    (hrig : ∀ v : Vec5, Rigid v → Subgroup.centralizer ({C.elt v} : Set G) ≤ M)
    {v : Vec5} (hv : v = v2 ∨ v = v3) {P : Subgroup G}
    (hP : IsO2 (Subgroup.centralizer ({C.elt v} : Set G)) P)
    (hC : Subgroup.centralizer ({C.elt v} : Set G) ⊓ Subgroup.centralizer (P : Set G) ≤ P)
    (hKM : ¬ Subgroup.centralizer ({C.elt v} : Set G) ≤ M) :
    P ≤ C.T ∧ P ≠ C.T ∧ ¬ P ≤ Q ∧ P ⊓ Q = C.Q1 ∧ C.Q1.relIndex P = 2 := by
  set K := Subgroup.centralizer ({C.elt v} : Set G) with hK
  have hKpre : K ⊓ M = C.pre H2 := C.inf_M_eq_pre hv
  have hQK : Q ≤ K := C.Q_le_centralizer_of_mem (C.elt_mem v)
  have hpreK : ∀ x ∈ C.pre H2, x ∈ K ∧ x ∈ M := fun x hx => by
    have : x ∈ K ⊓ M := hKpre ▸ hx
    exact this
  have hTK : C.T ≤ K := fun t ht => (hpreK t (C.T_le_pre_H2 ht)).1
  have hPM : P ⊓ M ≤ C.T := by
    apply C.le_T_of_normal (N := P ⊓ M)
    · intro x hx
      rw [← hKpre]
      exact ⟨hP.le hx.1, hx.2⟩
    · intro k hk n hn
      obtain ⟨hkK, hkM⟩ := hpreK k hk
      exact ⟨hP.normal k hkK n hn.1, M.mul_mem (M.mul_mem hkM hn.2) (M.inv_mem hkM)⟩
    · exact hP.pgroup.to_le inf_le_left
  have hPT : P ≤ C.T := by
    by_contra hPT
    have hPT' := prodSub K P C.T hP.normal hTK
    set PT := prodSub K P C.T hP.normal hTK with hPTd
    have hPTp : IsPGroup 2 PT := isPGroup_prodSub hP.pgroup C.isPGroup_T
    have hlt : C.T < PT := by
      refine lt_of_le_of_ne T_le_prodSub (fun h => hPT ?_)
      rw [h]
      exact P_le_prodSub
    obtain ⟨w, hwPT, hwT, hwN⟩ := exists_mem_normalizer_of_lt' hPTp hlt
    have hwM : w ∈ M := C.normalizer_T_le_M hrig hwN
    obtain ⟨p, hp, t, ht, rfl⟩ := hwPT
    have hpM : p ∈ M := by
      have := M.mul_mem hwM (M.inv_mem (C.T_le_M ht))
      simpa using this
    have hpT : p ∈ C.T := hPM ⟨hp, hpM⟩
    exact hwT (C.T.mul_mem hpT ht)
  have hPneT : P ≠ C.T := by
    intro h
    apply hKM
    intro k hk
    apply C.normalizer_T_le_M hrig
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [← h]
    exact ⟨fun ht => hP.normal k hk t ht, fun ht => by
      have := hP.normal k⁻¹ (K.inv_mem hk) _ ht
      simpa [mul_assoc] using this⟩
  have hPQ : ¬ P ≤ Q := by
    intro hPQ
    have hQP : Q ≤ P := le_trans (le_inf hQK (fun y hy => Subgroup.mem_centralizer_iff.2
      (fun p hp => C.Q_comm (hPQ hp) hy))) hC
    have hPeq : P = Q := le_antisymm hPQ hQP
    apply hKM
    intro k hk
    have hkN : k ∈ Subgroup.normalizer (Q : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [← hPeq]
      exact ⟨fun hy => hP.normal k hk y hy, fun hy => by
        have := hP.normal k⁻¹ (K.inv_mem hk) _ hy
        simpa [mul_assoc] using this⟩
    rw [C.normalizer_Q] at hkN
    exact hkN
  have hQ1P : C.Q1 ≤ P := le_trans (le_inf (fun y hy => hQK (C.Q1_le_Q hy)) (fun y hy =>
    Subgroup.mem_centralizer_iff.2 (fun p hp => C.Q1_comm_T hy (hPT hp)))) hC
  have hPQ1 : P ⊓ Q = C.Q1 := by
    have hle : C.Q1 ≤ P ⊓ Q := le_inf hQ1P C.Q1_le_Q
    rcases C.eq_or_eq_of_between_Q1_Q hle inf_le_right with h | h
    · exact h
    · exfalso
      have hQP : Q ≤ P := by
        have := inf_le_left (a := P) (b := Q)
        rwa [h] at this
      rcases C.eq_or_eq_of_between_Q_T hQP hPT with h' | h'
      · exact hPQ (h' ▸ le_refl _)
      · exact hPneT h'
  refine ⟨hPT, hPneT, hPQ, hPQ1, ?_⟩
  have := C.relIndex_inf_Q hPT hPQ
  rwa [hPQ1] at this

theorem centralizer_le_M_of_conj {v w : Vec5} {m : G} (hm : m ∈ M) (h : m * C.elt v * m⁻¹ = C.elt w)
    (hv : Subgroup.centralizer ({C.elt v} : Set G) ≤ M) :
    Subgroup.centralizer ({C.elt w} : Set G) ≤ M := by
  intro x hx
  have h1 : m⁻¹ * x * m ∈ Subgroup.centralizer ({C.elt v} : Set G) := by
    apply mem_centralizer_of_conj_eq
    have hx' := Subgroup.mem_centralizer_iff.1 hx (C.elt w) (Set.mem_singleton _)
    calc m⁻¹ * x * m * C.elt v * (m⁻¹ * x * m)⁻¹
        = m⁻¹ * (x * (m * C.elt v * m⁻¹) * x⁻¹) * m := by group
      _ = C.elt v := by
        rw [h]
        have : x * C.elt w * x⁻¹ = C.elt w := by
          calc x * C.elt w * x⁻¹ = (C.elt w * x) * x⁻¹ := by rw [hx']
            _ = C.elt w := by group
        rw [this, ← h]; group
  have := M.mul_mem (M.mul_mem hm (hv h1)) (M.inv_mem hm)
  simpa [mul_assoc] using this

theorem centralizer_le_M_v2 [Finite G]
    (hrig : ∀ v : Vec5, Rigid v → Subgroup.centralizer ({C.elt v} : Set G) ≤ M)
    (h5 : ∀ v : Vec5, v ≠ 0 → ∃ P : Subgroup G,
      IsO2 (Subgroup.centralizer ({C.elt v} : Set G)) P ∧
        Subgroup.centralizer ({C.elt v} : Set G) ⊓ Subgroup.centralizer (P : Set G) ≤ P) :
    Subgroup.centralizer ({C.elt v2} : Set G) ≤ M := by
  by_contra hKM
  obtain ⟨P, hP, hC⟩ := h5 v2 (by decide)
  obtain ⟨hPT, hPneT, hPQ, -, -⟩ := C.witness_structure hrig (Or.inl rfl) hP hC hKM
  set K := Subgroup.centralizer ({C.elt v2} : Set G) with hK
  have hQK : Q ≤ K := C.Q_le_centralizer_of_mem (C.elt_mem v2)
  have hQP : Q ≤ P := by
    refine chain_le (z := C.elt v2) hP hC (C.elt_mul_self v2) (fun k hk => ?_) hQK
      (fun p hp h hh => ?_)
    · have := Subgroup.mem_centralizer_iff.1 hk (C.elt v2) (Set.mem_singleton _)
      calc k * C.elt v2 * k⁻¹ = (C.elt v2 * k) * k⁻¹ := by rw [this]
        _ = C.elt v2 := by group
    · obtain ⟨u, rfl⟩ := (C.mem_Q_iff h).1 hh
      have hpT := C.mem_T.1 (hPT hp)
      have e : p * C.elt u * p⁻¹ * (C.elt u)⁻¹ = C.elt (permAct (C.th p) u + u) := by
        rw [C.conj_elt hpT.1, C.elt_inv, C.elt_add]
      rw [e]
      rcases hpT.2 with h1 | h1
      · left
        rw [h1, permAct_one, add_self_vec, C.elt_zero]
      · rcases permAct_tau_add u with h2 | h2
        · left
          rw [h1, h2, C.elt_zero]
        · right
          rw [h1, h2]
  rcases C.eq_or_eq_of_between_Q_T hQP hPT with h | h
  · exact hPQ h.le
  · exact hPneT h

theorem centralizer_le_M_wt2 [Finite G]
    (hrig : ∀ v : Vec5, Rigid v → Subgroup.centralizer ({C.elt v} : Set G) ≤ M)
    (h5 : ∀ v : Vec5, v ≠ 0 → ∃ P : Subgroup G,
      IsO2 (Subgroup.centralizer ({C.elt v} : Set G)) P ∧
        Subgroup.centralizer ({C.elt v} : Set G) ⊓ Subgroup.centralizer (P : Set G) ≤ P)
    {w : Vec5} (hw : wt w = 2) : Subgroup.centralizer ({C.elt w} : Set G) ≤ M := by
  obtain ⟨m, hm, h⟩ := C.exists_conj_of_wt_eq (v := v2) (w := w) (by rw [wt_v2, hw])
  exact C.centralizer_le_M_of_conj hm h (C.centralizer_le_M_v2 hrig h5)

end OrthCfg

end CFSG.CGT.PushingUpLit.Orth

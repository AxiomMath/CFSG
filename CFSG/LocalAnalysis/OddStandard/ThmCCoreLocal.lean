module

public import CFSG.LocalAnalysis.OddStandard.ThmCCoreQuot
public import CFSG.LocalAnalysis.OddStandard.ThmCTAmbient

public section

namespace CFSG.OddStandard.ThmC.Core

open CFSG Subgroup CFSG.OddStandard.ThmC CFSG.OddStandard.ThmC.T
open CFSG.GH74.GLS.Bg.TwoGroups

theorem frattini_mul {G : Type*} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    (P : Sylow 2 G) (hP : ((P : Subgroup G).map (QuotientGroup.mk' K)).Normal) (g : G) :
    ∃ n ∈ normalizer ((P : Subgroup G) : Set G), ∃ k ∈ K, g = n * k := by
  set N : Subgroup G := ((P : Subgroup G).map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K)
    with hN
  have : N.Normal := hP.comap _
  have hPN : (P : Subgroup G) ≤ N := Subgroup.le_comap_map _ _
  have htop : normalizer ((P : Subgroup G) : Set G) ⊔ N = ⊤ :=
    Sylow.normalizer_sup_eq_top' (N := N) P hPN
  have hg : g ∈ normalizer ((P : Subgroup G) : Set G) ⊔ N := by rw [htop]; trivial
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hg
  obtain ⟨n, hn, u, hu, rfl⟩ := hg
  have hu' : QuotientGroup.mk' K u ∈ (P : Subgroup G).map (QuotientGroup.mk' K) := hu
  obtain ⟨x, hx, hxu⟩ := hu'
  refine ⟨n * x, (normalizer ((P : Subgroup G) : Set G)).mul_mem hn
    (Subgroup.le_normalizer hx), x⁻¹ * u, ?_, by group⟩
  rw [← QuotientGroup.ker_mk' K, MonoidHom.mem_ker, map_mul, map_inv, hxu, inv_mul_cancel]

theorem alt2_action {Y : Type*} [Group Y] [Finite Y] (P : Subgroup Y) [P.Normal]
    (hcomm : ∀ b ∈ P, ∀ c ∈ P, b * c = c * b)
    (hquot : Nonempty (Y ⧸ P ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (Y ⧸ P ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5)))
    (htrans : ∀ u ∈ P, ∀ v ∈ P, u ≠ 1 → v ≠ 1 → ∃ g : Y, g⁻¹ * u * g = v)
    (N : Subgroup Y) [N.Normal] (hNodd : ∀ n ∈ N, ∃ j : ℕ, Odd j ∧ n ^ j ∈ P) {n : Y} (hn : n ∈ N) :
    (∀ p ∈ P, n * p * n⁻¹ = p) ∨
      ((∀ p ∈ P, n * p * n⁻¹ = p → p = 1) ∧ ∀ p ∈ P, n ^ 3 * p * (n ^ 3)⁻¹ = p) := by
  classical
  have key : ∀ θ : Y →* alternatingGroup (Fin 5), Function.Surjective θ → P ≤ θ.ker →
      ∀ m ∈ N, θ m = 1 := by
    intro θ hθ hPθ m hm
    have hnorm : (N.map θ).Normal := Subgroup.Normal.map inferInstance θ hθ
    rcases hnorm.eq_bot_or_eq_top with hbot | htop
    · have : θ m ∈ N.map θ := ⟨m, hm, rfl⟩
      rw [hbot] at this
      exact this
    · exfalso
      have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
        rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)), Fintype.card_perm,
          Fintype.card_fin, show Nat.factorial 5 = 120 from rfl] at h
        omega
      obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 5)) 2
        (by rw [hcard]; norm_num)
      have ha' : a ∈ N.map θ := by rw [htop]; trivial
      obtain ⟨m', hm', rfl⟩ := ha'
      obtain ⟨j, hj, hjP⟩ := hNodd m' hm'
      have h1 : (θ m') ^ j = 1 := by rw [← map_pow]; exact hPθ hjP
      have h2 : orderOf (θ m') ∣ j := orderOf_dvd_of_pow_eq_one h1
      rw [ha] at h2
      exact (Nat.not_even_iff_odd.2 hj) (even_iff_two_dvd.2 h2)
  have finish : (∀ y : Y, y * n * y⁻¹ * n⁻¹ ∈ P) → n ^ 3 ∈ P → 
      (∀ p ∈ P, n * p * n⁻¹ = p) ∨
        ((∀ p ∈ P, n * p * n⁻¹ = p → p = 1) ∧ ∀ p ∈ P, n ^ 3 * p * (n ^ 3)⁻¹ = p) := by
    intro hcent hcube
    by_cases hfix : ∃ p₀ ∈ P, p₀ ≠ 1 ∧ n * p₀ * n⁻¹ = p₀
    · left
      obtain ⟨p₀, hp₀, hp₀1, hnp₀⟩ := hfix
      intro p hp
      by_cases hp1 : p = 1
      · rw [hp1]; group
      · obtain ⟨g, hg⟩ := htrans p₀ hp₀ p hp hp₀1 hp1
        have ha : g * n * g⁻¹ * n⁻¹ ∈ P := hcent g
        set a := g * n * g⁻¹ * n⁻¹ with ha_def
        have hgn : n * g⁻¹ = g⁻¹ * (a * n) := by
          rw [ha_def]; group
        calc n * p * n⁻¹ = n * (g⁻¹ * p₀ * g) * n⁻¹ := by rw [hg]
          _ = (n * g⁻¹) * p₀ * (n * g⁻¹)⁻¹ := by group
          _ = g⁻¹ * (a * (n * p₀ * n⁻¹) * a⁻¹) * g := by rw [hgn]; group
          _ = g⁻¹ * (a * p₀ * a⁻¹) * g := by rw [hnp₀]
          _ = g⁻¹ * p₀ * g := by
            rw [show a * p₀ * a⁻¹ = p₀ from by
              rw [hcomm a ha p₀ hp₀]; group]
          _ = p := hg
    · right
      refine ⟨fun p hp hnp => ?_, fun p hp => ?_⟩
      · by_contra hp1
        exact hfix ⟨p, hp, hp1, hnp⟩
      · have := hcomm (n ^ 3) hcube p hp
        calc n ^ 3 * p * (n ^ 3)⁻¹ = (n ^ 3 * p) * (n ^ 3)⁻¹ := rfl
          _ = (p * n ^ 3) * (n ^ 3)⁻¹ := by rw [this]
          _ = p := by group
  rcases hquot with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  ·
    set ρ : Y →* alternatingGroup (Fin 5) := φ.toMonoidHom.comp (QuotientGroup.mk' P) with hρ
    have hρsurj : Function.Surjective ρ :=
      φ.surjective.comp (QuotientGroup.mk'_surjective P)
    have hPρ : P ≤ ρ.ker := fun x hx => by
      show ρ x = 1
      simp only [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
      rw [(QuotientGroup.eq_one_iff x).2 hx, map_one]
    have h1 := key ρ hρsurj hPρ n hn
    have hnP : n ∈ P := by
      have : φ (QuotientGroup.mk' P n) = 1 := h1
      have h2 := φ.map_eq_one_iff.1 this
      exact (QuotientGroup.eq_one_iff n).1 h2
    left
    intro p hp
    have := hcomm n hnP p hp
    calc n * p * n⁻¹ = (n * p) * n⁻¹ := rfl
      _ = (p * n) * n⁻¹ := by rw [this]
      _ = p := by group
  · set ρ : Y →* Multiplicative (ZMod 3) × alternatingGroup (Fin 5) :=
      φ.toMonoidHom.comp (QuotientGroup.mk' P) with hρ
    have hρsurj : Function.Surjective ρ :=
      φ.surjective.comp (QuotientGroup.mk'_surjective P)
    have hker : ∀ x, ρ x = 1 ↔ x ∈ P := fun x => by
      simp only [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [← map_one φ, φ.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    have hsurj2 : Function.Surjective ((MonoidHom.snd _ _).comp ρ) :=
      (Prod.snd_surjective).comp hρsurj
    have hP2 : P ≤ ((MonoidHom.snd (Multiplicative (ZMod 3)) (alternatingGroup (Fin 5))).comp
        ρ).ker := fun x hx => by
      simp [(hker x).2 hx]
    have h1 := key _ hsurj2 hP2 n hn
    have h1' : (ρ n).2 = 1 := h1
    have hρn : ρ n = ((ρ n).1, 1) := Prod.ext rfl h1'
    have hcom3 : ∀ a b : Multiplicative (ZMod 3), a * b * a⁻¹ * b⁻¹ = 1 := by decide
    apply finish
    · intro y
      rw [← hker, map_mul, map_mul, map_mul, map_inv, map_inv]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul, Prod.fst_inv]
        exact hcom3 _ _
      · simp [h1']
    · have hc : ∀ c : Multiplicative (ZMod 3), c ^ 3 = 1 := by decide
      rw [← hker, map_pow, hρn, Prod.pow_mk, hc, one_pow]
      rfl

section Local

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem image_le_pCore {Q : Subgroup X} (hQ2 : IsPGroup 2 Q) :
    (Q.subgroupOf (nzr Q)).map (projN Q) ≤ pCore 2 (QuotN Q) := by
  have hnorm : (Q.subgroupOf (nzr Q)).Normal := Subgroup.normal_in_normalizer
  have hn : ((Q.subgroupOf (nzr Q)).map (projN Q)).Normal :=
    hnorm.map _ (projN_surjective Q)
  have hp : IsPGroup 2 ((Q.subgroupOf (nzr Q)).map (projN Q)) := by
    have : IsPGroup 2 (Q.subgroupOf (nzr Q)) := hQ2.comap_subtype
    exact this.map _
  exact le_sSup ⟨hn, hp⟩

theorem projN_injOn_Q {Q : Subgroup X} (hQ2 : IsPGroup 2 Q) {x y : X} (hx : x ∈ Q) (hy : y ∈ Q)
    (hxy : projN Q ⟨x, Subgroup.le_normalizer hx⟩ = projN Q ⟨y, Subgroup.le_normalizer hy⟩) :
    x = y :=
  projN_injOn hQ2 (Subgroup.le_normalizer (H := Q)) hx hy hxy

omit [Finite X] in
theorem projN_mem_image {Q : Subgroup X} {q : X} (hq : q ∈ Q) :
    projN Q ⟨q, Subgroup.le_normalizer hq⟩ ∈ (Q.subgroupOf (nzr Q)).map (projN Q) :=
  ⟨⟨q, Subgroup.le_normalizer hq⟩, hq, rfl⟩

theorem frattini_of_normal {Q : Subgroup X} (T : Sylow 2 X) (hTH : (T : Subgroup X) ≤ nzr Q)
    (hnorm : (((T : Subgroup X).subgroupOf (nzr Q)).map (projN Q)).Normal) {h : X}
    (hh : h ∈ nzr Q) :
    ∃ m ∈ normalizer ((T : Subgroup X) : Set X), m ∈ nzr Q ∧
      ∃ k ∈ oddCoreIn (nzr Q), h = m * k := by
  have : (pPrimeCore 2 (nzr Q)).Normal := pPrimeCore_normal
  have hP : (((T.subtype hTH : Sylow 2 (nzr Q)) : Subgroup (nzr Q)).map
      (QuotientGroup.mk' (pPrimeCore 2 (nzr Q)))).Normal := by
    rw [Sylow.coe_subtype]
    exact hnorm
  obtain ⟨n, hn, k, hk, hnk⟩ := frattini_mul (pPrimeCore 2 (nzr Q)) (T.subtype hTH) hP ⟨h, hh⟩
  have hmem : ∀ x : X, ∀ hx : x ∈ nzr Q,
      (⟨x, hx⟩ : nzr Q) ∈ ((T.subtype hTH : Sylow 2 (nzr Q)) : Subgroup (nzr Q)) ↔
        x ∈ (T : Subgroup X) := fun x hx => by
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
  refine ⟨(n : X), ?_, n.2, (k : X), ⟨k, hk, rfl⟩, congrArg Subtype.val hnk⟩
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨t, hTH ht⟩).1 ((hmem t (hTH ht)).2 ht)
    exact (hmem _ _).1 h1
  · intro ht
    have hn' := Subgroup.mem_normalizer_iff.1 (inv_mem hn)
    have h1 := (hn' ⟨_, hTH ht⟩).1 ((hmem _ (hTH ht)).2 ht)
    have h2 := (hmem _ _).1 h1
    simpa [mul_assoc] using h2

theorem localStructure (hS2 : O2Structure) (T : Sylow 2 X) (hT : IsT (T : Subgroup X))
    {Z A B : Subgroup X} (hTA : TAmbient (T : Subgroup X) Z A B)
    (Q : Subgroup X) (hQ1 : Q ≠ ⊥) (hQT : Q ≤ T) (hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) :
    (∀ h ∈ nzr Q, ∃ m ∈ normalizer ((T : Subgroup X) : Set X), m ∈ nzr Q ∧
        ∃ k ∈ oddCoreIn (nzr Q), h = m * k) ∨
    ((Q = A ∨ Q = B) ∧ ∀ N : Subgroup X, N ≤ nzr Q → (∀ h ∈ nzr Q, ∀ n ∈ N, h * n * h⁻¹ ∈ N) →
      Q ≤ N → (∀ n ∈ N, ∃ j : ℕ, Odd j ∧ n ^ j ∈ Q) →
      ∀ g ∈ N, (∀ q ∈ Q, g * q * g⁻¹ = q) ∨
        ((∀ q ∈ Q, g * q * g⁻¹ = q → q = 1) ∧ ∀ q ∈ Q, g ^ 3 * q * (g ^ 3)⁻¹ = q)) := by
  have hTH : (T : Subgroup X) ≤ nzr Q := le_nzr_of_normalizes hQn
  have hQ2 : IsPGroup 2 Q := T.isPGroup'.to_le hQT
  have hconcl := concl_quotN hS2 T hT hQ1 hQT hQn
  unfold Concl at hconcl
  obtain ⟨-, h1 | h2⟩ := hconcl
  ·
    left
    intro h hh
    have hnorm : (((T : Subgroup X).subgroupOf (nzr Q)).map (projN Q)).Normal := by
      have := pCore_normal (p := 2) (G := QuotN Q)
      rw [h1.1, coe_sylowBar] at this
      exact this
    exact frattini_of_normal T hTH hnorm hh
  ·
    right
    obtain ⟨hPT, hP16, hPsq, hPcomm, hquot, htrans⟩ := h2
    set P : Subgroup (QuotN Q) := pCore 2 (QuotN Q) with hP
    have hPn : P.Normal := pCore_normal
    set πQ : Subgroup (QuotN Q) := (Q.subgroupOf (nzr Q)).map (projN Q) with hπQ
    have hπQP : πQ ≤ P := image_le_pCore hQ2
    have hπQn : πQ.Normal := (Subgroup.normal_in_normalizer (H := Q)).map _ (projN_surjective Q)
    have hπQ1 : πQ ≠ ⊥ := by
      intro hbot
      apply hQ1
      rw [eq_bot_iff]
      intro q hq
      have hmem := projN_mem_image hq
      rw [← hπQ, hbot, Subgroup.mem_bot] at hmem
      exact Subgroup.mem_bot.2 (eq_one_of_mem_inf_oddCore hQ2 hq
        ((projN_eq_one_iff Q _).1 hmem))
    have hPπQ : P ≤ πQ := by
      intro u hu
      by_cases hu1 : u = 1
      · rw [hu1]; exact one_mem _
      · obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hπQ1
        obtain ⟨g, hg⟩ := htrans v (hπQP hv) u hu (fun h => hv1 (Subtype.ext h)) hu1
        rw [← hg]
        have := hπQn.conj_mem v hv g⁻¹
        simpa using this
    have hPeq : P = πQ := le_antisymm hPπQ hπQP
    have hQsq : ∀ q ∈ Q, q * q = 1 := by
      intro q hq
      have hq2 : q * q ∈ Q := Q.mul_mem hq hq
      have h3 := hPsq _ (hπQP (projN_mem_image hq))
      have h4 : projN Q ⟨q * q, Subgroup.le_normalizer hq2⟩ = 1 := by
        have : projN Q ⟨q * q, Subgroup.le_normalizer hq2⟩ =
            projN Q ⟨q, Subgroup.le_normalizer hq⟩ * projN Q ⟨q, Subgroup.le_normalizer hq⟩ := by
          rw [← map_mul]; rfl
        rw [this]; exact h3
      exact eq_one_of_mem_inf_oddCore hQ2 hq2 ((projN_eq_one_iff Q _).1 h4)
    have hQcomm : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q := by
      intro q hq q' hq'
      have hqq' : q * q' ∈ Q := Q.mul_mem hq hq'
      have hq'q : q' * q ∈ Q := Q.mul_mem hq' hq
      have h3 := hPcomm _ (hπQP (projN_mem_image hq)) _ (hπQP (projN_mem_image hq'))
      apply projN_injOn_Q hQ2 hqq' hq'q
      have e1 : projN Q ⟨q * q', Subgroup.le_normalizer hqq'⟩ =
          projN Q ⟨q, Subgroup.le_normalizer hq⟩ * projN Q ⟨q', Subgroup.le_normalizer hq'⟩ := by
        rw [← map_mul]; rfl
      have e2 : projN Q ⟨q' * q, Subgroup.le_normalizer hq'q⟩ =
          projN Q ⟨q', Subgroup.le_normalizer hq'⟩ * projN Q ⟨q, Subgroup.le_normalizer hq⟩ := by
        rw [← map_mul]; rfl
      rw [e1, e2, h3]
    have hQcard : Nat.card Q = 16 := by
      rw [← hP16, hPeq]
      let f : Q → πQ := fun q => ⟨projN Q ⟨q, Subgroup.le_normalizer q.2⟩, projN_mem_image q.2⟩
      have hf : Function.Bijective f := by
        constructor
        · intro a b hab
          have := congrArg Subtype.val hab
          exact Subtype.ext (projN_injOn_Q hQ2 a.2 b.2 this)
        · rintro ⟨y, x, hx, rfl⟩
          exact ⟨⟨x, hx⟩, rfl⟩
      exact Nat.card_congr (Equiv.ofBijective f hf)
    refine ⟨?_, ?_⟩
    · rcases hTA.elemAb_le Q hQT hQsq hQcomm with hQA | hQB
      · left
        exact Subgroup.eq_of_le_of_card_ge hQA (by rw [hTA.card_A, hQcard])
      · right
        exact Subgroup.eq_of_le_of_card_ge hQB (by rw [hTA.card_B, hQcard])
    · intro N hNH hNn hQN hNodd g hg
      set NH : Subgroup (nzr Q) := N.subgroupOf (nzr Q) with hNH_def
      have hNHn : NH.Normal := ⟨fun n hn h => by
        rw [hNH_def, Subgroup.mem_subgroupOf] at hn ⊢
        exact hNn h h.2 n hn⟩
      set Ñ : Subgroup (QuotN Q) := NH.map (projN Q) with hÑ_def
      have hÑn : Ñ.Normal := hNHn.map _ (projN_surjective Q)
      have hÑodd : ∀ n ∈ Ñ, ∃ j : ℕ, Odd j ∧ n ^ j ∈ P := by
        rintro _ ⟨n, hn, rfl⟩
        obtain ⟨j, hj, hjQ⟩ := hNodd (n : X) hn
        refine ⟨j, hj, ?_⟩
        rw [hPeq, ← map_pow]
        exact ⟨n ^ j, hjQ, rfl⟩
      have hgÑ : projN Q ⟨g, hNH hg⟩ ∈ Ñ := ⟨⟨g, hNH hg⟩, hg, rfl⟩
      have hact := alt2_action P hPcomm hquot htrans Ñ hÑodd hgÑ
      have hconj : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun q hq => by
        have := (Subgroup.mem_normalizer_iff.1 (hNH hg) q).1 hq
        exact this
      have hπconj : ∀ (j : ℕ) (q : X) (hq : q ∈ Q) (hq' : g ^ j * q * (g ^ j)⁻¹ ∈ Q),
          projN Q ⟨g ^ j * q * (g ^ j)⁻¹, Subgroup.le_normalizer hq'⟩ =
            projN Q ⟨g, hNH hg⟩ ^ j * projN Q ⟨q, Subgroup.le_normalizer hq⟩ *
              (projN Q ⟨g, hNH hg⟩ ^ j)⁻¹ := by
        intro j q hq hq'
        rw [← map_pow, ← map_inv, ← map_mul, ← map_mul]
        rfl
      have hconjpow : ∀ (j : ℕ) (q : X), q ∈ Q → g ^ j * q * (g ^ j)⁻¹ ∈ Q := by
        intro j
        induction j with
        | zero => intro q hq; simpa using hq
        | succ j ih =>
          intro q hq
          have := hconj _ (ih q hq)
          have e : g * (g ^ j * q * (g ^ j)⁻¹) * g⁻¹ = g ^ (j + 1) * q * (g ^ (j + 1))⁻¹ := by
            group
          rwa [e] at this
      rcases hact with hfix | ⟨hfpf, hcube⟩
      · left
        intro q hq
        have hq' := hconjpow 1 q hq
        simp only [pow_one] at hq'
        have := hfix _ (hπQP (projN_mem_image hq))
        have h5 := hπconj 1 q hq (by simpa using hq')
        simp only [pow_one] at h5
        apply projN_injOn_Q hQ2 hq' hq
        rw [h5]
        exact this
      · right
        refine ⟨fun q hq hgq => ?_, fun q hq => ?_⟩
        · have hq' := hconjpow 1 q hq
          simp only [pow_one] at hq'
          have h5 := hπconj 1 q hq (by simpa using hq')
          simp only [pow_one] at h5
          have h6 : projN Q ⟨q, Subgroup.le_normalizer hq⟩ = 1 := by
            apply hfpf _ (hπQP (projN_mem_image hq))
            rw [← h5]
            congr 1
            exact Subtype.ext hgq
          exact eq_one_of_mem_inf_oddCore hQ2 hq ((projN_eq_one_iff Q _).1 h6)
        · have hq' := hconjpow 3 q hq
          have h5 := hπconj 3 q hq hq'
          have := hcube _ (hπQP (projN_mem_image hq))
          apply projN_injOn_Q hQ2 hq' hq
          rw [h5]
          exact this

end Local

end CFSG.OddStandard.ThmC.Core

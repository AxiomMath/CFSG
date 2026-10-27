module

public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.LyonsUnitaryFour

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_sylow_of_le {p : ℕ} [Fact p.Prime] (S : Sylow p G) {H : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) {t : G} (ht : t ∈ H) (htp : ∃ k : ℕ, t ^ (p ^ k) = 1) :
    ∃ h ∈ H, h * t * h⁻¹ ∈ (S : Subgroup G) := by
  classical
  let t' : H := ⟨t, ht⟩
  obtain ⟨k, hk⟩ := htp
  have hp : IsPGroup p (Subgroup.zpowers t') := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have : t' ^ (p ^ k) = 1 := Subtype.ext (by simpa [t'] using hk)
    rw [this, one_zpow]
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H T (S.subtype hSH)
  have htT : t' ∈ (T : Subgroup H) := hT (Subgroup.mem_zpowers t')
  have hmem : MulAut.conj c t' ∈ ((c • T : Sylow p H) : Subgroup H) := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ htT
  rw [hc, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
  refine ⟨c, c.2, ?_⟩
  simpa [t'] using hmem

theorem exists_conj_le_sylow_of_le {p : ℕ} [Fact p.Prime] (P : Sylow p G) {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) {Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsPGroup p Q) :
    ∃ c ∈ H, ∀ q ∈ Q, c * q * c⁻¹ ∈ (P : Subgroup G) := by
  classical
  have hp : IsPGroup p (Q.subgroupOf H) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H T (P.subtype hPH)
  refine ⟨c, c.2, fun q hq => ?_⟩
  have hqT : (⟨q, hQH hq⟩ : H) ∈ (T : Subgroup H) := hT (Subgroup.mem_subgroupOf.mpr hq)
  have hmem : MulAut.conj c (⟨q, hQH hq⟩ : H) ∈ ((c • T : Sylow p H) : Subgroup H) := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hqT
  rw [hc, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

theorem weak_closure_central_fusion {p : ℕ} [Fact p.Prime] (S : Sylow p G) {Q : Subgroup G}
    (hQS : Q ≤ (S : Subgroup G))
    (hweak : ∀ g : G, Q.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      Q.map (MulAut.conj g).toMonoidHom = Q)
    {z f g : G} (hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s)
    (hf : ∀ q ∈ Q, q * f = f * q) (hg : g * z * g⁻¹ = f) :
    ∃ n ∈ Subgroup.normalizer (Q : Set G), n * z * n⁻¹ = f := by
  classical
  set C := Subgroup.centralizer ({f} : Set G) with hC
  have hSC : ((g • S : Sylow p G) : Subgroup G) ≤ C := by
    intro x hx
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      at hx
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ← hg]
    have h := hzS _ hx
    simp only [MulAut.smul_def, MulAut.conj_inv_apply] at h
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * x := by group
  have hQC : Q ≤ C := by
    intro q hq
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact hf q hq
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_sylow_of_le (g • S) hSC hQC (S.isPGroup'.to_le hQS)
  set m := g⁻¹ * c with hm
  have hmap : Q.map (MulAut.conj m).toMonoidHom ≤ (S : Subgroup G) := by
    rintro _ ⟨q, hq, rfl⟩
    have h := hc q hq
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      at h
    simp only [MulAut.smul_def, MulAut.conj_inv_apply] at h
    simpa [hm, mul_assoc] using h
  have hmQ := hweak m hmap
  have hmN : m ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      rw [← hmQ]
      exact ⟨q, hq, by simp⟩
    · intro hq
      rw [← hmQ] at hq
      obtain ⟨q', hq', heq⟩ := hq
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at heq
      have : q' = q := by
        have := congrArg (fun x => m⁻¹ * x * m) heq
        simpa [mul_assoc] using this
      rw [← this]; exact hq'
  refine ⟨m⁻¹, (Subgroup.normalizer (Q : Set G)).inv_mem hmN, ?_⟩
  have hcf : c * f = f * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  calc m⁻¹ * z * m⁻¹⁻¹ = c⁻¹ * (g * z * g⁻¹) * c := by rw [hm]; group
    _ = c⁻¹ * f * c := by rw [hg]
    _ = f := by rw [mul_assoc, ← hcf, ← mul_assoc, inv_mul_cancel, one_mul]

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {E : Subgroup G} {g : G}
    (h : E.map (MulAut.conj g).toMonoidHom = E) : g ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, by simp⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, heq⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at heq
    have : y = x := by
      have := congrArg (fun w => g⁻¹ * w * g) heq
      simpa [mul_assoc] using this
    rw [← this]; exact hy

theorem central_sylow_involution_set_strong_embedding (S : Sylow 2 G) (E : Subgroup G)
    (hES : E ≤ (S : Subgroup G)) (hEZ : ∀ e ∈ E, ∀ s ∈ (S : Subgroup G), s * e = e * s)
    (hEexp : ∀ e ∈ E, e ^ 2 = 1) (hEnt : E ≠ ⊥)
    (hinv : ∀ t ∈ (S : Subgroup G), t ^ 2 = 1 → t ∈ E) (hnotnormal : ¬ E.Normal)
    (hcent : ∀ e ∈ E, e ≠ 1 →
      Subgroup.centralizer ({e} : Set G) = Subgroup.centralizer (E : Set G)) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (Subgroup.normalizer (E : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (E : Set G) with hM
  have hSM : (S : Subgroup G) ≤ M := by
    intro s hs
    rw [hM, Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      rw [hEZ e he s hs, mul_inv_cancel_right]; exact he
    · intro he
      have h := hEZ _ he s hs
      have : e = s * e * s⁻¹ := by
        calc e = s⁻¹ * ((s * e * s⁻¹) * s) := by group
          _ = s⁻¹ * (s * (s * e * s⁻¹)) := by rw [← h]
          _ = s * e * s⁻¹ := by group
      rw [this]; exact he
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => hEZ b hb a (hES ha)
  have htwo : ∀ t : G, t ^ 2 = 1 → ∃ k : ℕ, t ^ (2 ^ k) = 1 := fun t ht => ⟨1, by simpa using ht⟩
  have hMinv : ∀ t ∈ M, t ^ 2 = 1 → t ∈ E := by
    intro t ht ht2
    obtain ⟨m, hm, hmt⟩ := exists_conj_mem_sylow_of_le S hSM ht (htwo t ht2)
    have hmt2 : (m * t * m⁻¹) ^ 2 = 1 := by
      rw [show (m * t * m⁻¹) ^ 2 = m * t ^ 2 * m⁻¹ by rw [sq, sq]; group, ht2]; group
    have hE := hinv _ hmt hmt2
    have hmN : m⁻¹ ∈ M := M.inv_mem hm
    have := (Subgroup.mem_normalizer_iff.mp hmN (m * t * m⁻¹)).mp hE
    simpa [mul_assoc] using this
  have hCinv : ∀ e ∈ E, e ≠ 1 → ∀ t ∈ Subgroup.centralizer ({e} : Set G), t ^ 2 = 1 →
      t ∈ E := by
    intro e he he1 t ht ht2
    have hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hEZ e he s hs
    obtain ⟨c, hc, hct⟩ := exists_conj_mem_sylow_of_le S hSC ht (htwo t ht2)
    have hct2 : (c * t * c⁻¹) ^ 2 = 1 := by
      rw [show (c * t * c⁻¹) ^ 2 = c * t ^ 2 * c⁻¹ by rw [sq, sq]; group, ht2]; group
    have hE := hinv _ hct hct2
    rw [hcent e he he1] at hc
    have hcomm := Subgroup.mem_centralizer_iff.mp hc _ hE
    have : t = c * t * c⁻¹ := by
      calc t = c⁻¹ * ((c * t * c⁻¹) * c) := by group
        _ = c⁻¹ * (c * (c * t * c⁻¹)) := by rw [hcomm]
        _ = c * t * c⁻¹ := by group
    rw [this]; exact hE
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply hnotnormal
    rw [hM, Subgroup.normalizer_eq_top_iff] at htop
    exact htop
  ·
    obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEnt
    have he2 : orderOf (e : G) = 2 := orderOf_eq_prime (hEexp e e.2)
      (fun h => he1 (Subtype.ext h))
    have h2 : 2 ∣ Nat.card M := by
      rw [← he2, ← Subgroup.orderOf_mk (e : G) (hSM (hES e.2))]
      exact orderOf_dvd_natCard _
    exact even_iff_two_dvd.mpr h2
  · intro g hg
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom))
      2 h2
    have ht2 : (t : G) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
    have ht1 : (t : G) ≠ 1 := by
      intro h1
      have : t = 1 := Subtype.ext h1
      rw [this, orderOf_one] at ht
      norm_num at ht
    have htE : (t : G) ∈ E := hMinv t t.2.1 ht2
    obtain ⟨u, hu, hut⟩ := t.2.2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hut
    have hu2 : u ^ 2 = 1 := by
      have : u = g⁻¹ * t * g := by rw [← hut]; group
      rw [this, show (g⁻¹ * (t : G) * g) ^ 2 = g⁻¹ * (t : G) ^ 2 * g by rw [sq, sq]; group, ht2]
      group
    have huE : u ∈ E := hMinv u hu hu2
    have hEg : E.map (MulAut.conj g).toMonoidHom ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      apply hCinv (t : G) htE ht1
      · rw [Subgroup.mem_centralizer_singleton_iff, ← hut]
        have h := hEcomm x hx u huE
        calc g * x * g⁻¹ * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
          _ = g * (u * x) * g⁻¹ := by rw [h]
          _ = g * u * g⁻¹ * (g * x * g⁻¹) := by group
      · rw [show (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ by rw [sq, sq]; group, hEexp x hx]; group
    have hEgeq : E.map (MulAut.conj g).toMonoidHom = E :=
      Subgroup.eq_of_le_of_card_ge hEg
        (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
    exact hg (mem_normalizer_of_map_conj_eq hEgeq)

theorem alperinSubgroup_eq_of_central_involutions (S : Sylow 2 G)
    (hinvcent : ∀ x ∈ (S : Subgroup G), x ^ 2 = 1 → ∀ s ∈ (S : Subgroup G), s * x = x * s)
    (hcomm : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), (a⁻¹ * b⁻¹ * a * b) ^ 2 = 1)
    {Q : Subgroup G} (hQ : CFSG.RankTwoShapes.IsAlperinSubgroup 2 (S : Subgroup G) Q) :
    Q = (S : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQS, -, hcentric, hrad⟩ := hQ
  set Sg := (S : Subgroup G) with hSg
  let E : Subgroup G :=
    { carrier := {x | x ∈ Sg ∧ x ^ 2 = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨Sg.mul_mem ha hb, ?_⟩
        have hab : Commute a b := (hinvcent a ha ha2 b hb).symm
        rw [hab.mul_pow, ha2, hb2, one_mul]
      one_mem' := ⟨Sg.one_mem, one_pow 2⟩
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        exact ⟨Sg.inv_mem ha, by rw [inv_pow, ha2, inv_one]⟩ }
  have hmemE : ∀ x, x ∈ E ↔ x ∈ Sg ∧ x ^ 2 = 1 := fun x => Iff.rfl
  have hcommE : ∀ a ∈ Sg, ∀ b ∈ Sg, a⁻¹ * b⁻¹ * a * b ∈ E := fun a ha b hb =>
    ⟨Sg.mul_mem (Sg.mul_mem (Sg.mul_mem (Sg.inv_mem ha) (Sg.inv_mem hb)) ha) hb,
      hcomm a ha b hb⟩
  have hEcent : ∀ e ∈ E, ∀ s ∈ Sg, s * e = e * s := fun e he => hinvcent e he.1 he.2
  have hEQ : E ≤ Q := by
    intro e he
    apply hcentric
    refine ⟨?_, he.1⟩
    show e ∈ Subgroup.centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hEcent e he q (hQS hq))
  have hQnormal : ∀ s ∈ Sg, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q := by
    intro s hs q hq
    have h := hEQ (hcommE q (hQS hq) s⁻¹ (Sg.inv_mem hs))
    have : s * q * s⁻¹ = q * (q⁻¹ * s⁻¹⁻¹ * q * s⁻¹) := by group
    rw [this]
    exact Q.mul_mem hq h
  let R : Subgroup G :=
    { carrier := {n | n ∈ Subgroup.normalizer (Q : Set G) ∧ (∀ e ∈ E, n * e * n⁻¹ = e) ∧
        ∀ q ∈ Q, q⁻¹ * (n * q * n⁻¹) ∈ E}
      mul_mem' := by
        rintro a b ⟨haN, haE, haQ⟩ ⟨hbN, hbE, hbQ⟩
        refine ⟨Subgroup.mul_mem _ haN hbN, fun e he => ?_, fun q hq => ?_⟩
        · rw [show a * b * e * (a * b)⁻¹ = a * (b * e * b⁻¹) * a⁻¹ by group, hbE e he, haE e he]
        · have hbq : b * q * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hbN q).mp hq
          have h1 := haQ _ hbq
          have h2 := hbQ q hq
          have : q⁻¹ * (a * b * q * (a * b)⁻¹) =
              (q⁻¹ * (b * q * b⁻¹)) * ((b * q * b⁻¹)⁻¹ * (a * (b * q * b⁻¹) * a⁻¹)) := by group
          rw [this]
          exact E.mul_mem h2 h1
      one_mem' := ⟨Subgroup.one_mem _, fun e _ => by group, fun q _ => by
        rw [show q⁻¹ * (1 * q * 1⁻¹) = 1 by group]; exact E.one_mem⟩
      inv_mem' := by
        rintro a ⟨haN, haE, haQ⟩
        refine ⟨Subgroup.inv_mem _ haN, fun e he => ?_, fun q hq => ?_⟩
        · have h := haE e he
          have h1 : a * e = e * a := by
            calc a * e = a * e * a⁻¹ * a := by group
              _ = e * a := by rw [h]
          calc a⁻¹ * e * a⁻¹⁻¹ = a⁻¹ * (e * a) := by group
            _ = a⁻¹ * (a * e) := by rw [h1]
            _ = e := by group
        · have hq' : a⁻¹ * q * a ∈ Q := by
            have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) q).mp hq
            simpa using this
          have h := haQ _ hq'
          have h' : (a⁻¹ * q * a)⁻¹ * q ∈ E := by
            simpa [mul_assoc] using h
          have : q⁻¹ * (a⁻¹ * q * a⁻¹⁻¹) = ((a⁻¹ * q * a)⁻¹ * q)⁻¹ := by group
          rw [this]
          exact E.inv_mem h' }
  have hmemR : ∀ n, n ∈ R ↔ n ∈ Subgroup.normalizer (Q : Set G) ∧ (∀ e ∈ E, n * e * n⁻¹ = e) ∧
      ∀ q ∈ Q, q⁻¹ * (n * q * n⁻¹) ∈ E := fun n => Iff.rfl
  set C := Subgroup.centralizer (Q : Set G) with hC
  have hCN : C ≤ Subgroup.normalizer (Q : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro q
    have h := Subgroup.mem_centralizer_iff.mp hc
    constructor
    · intro hq
      rw [← h q hq, mul_inv_cancel_right]; exact hq
    · intro hq
      have h2 := h _ hq
      have : q = c * q * c⁻¹ := by
        calc q = c⁻¹ * ((c * q * c⁻¹) * c) := by group
          _ = c⁻¹ * (c * (c * q * c⁻¹)) := by rw [h2]
          _ = c * q * c⁻¹ := by group
      rw [this]; exact hq
  have hEstable : ∀ m ∈ Subgroup.normalizer (Q : Set G), ∀ e ∈ E, m * e * m⁻¹ ∈ E := by
    intro m hm e he
    have hq : m * e * m⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hm e).mp (hEQ he)
    refine ⟨hQS hq, ?_⟩
    rw [show (m * e * m⁻¹) ^ 2 = m * e ^ 2 * m⁻¹ by rw [sq, sq]; group, he.2]; group
  have hQCR : Q ⊔ C ≤ R := by
    apply sup_le
    · intro q hq
      refine ⟨Subgroup.le_normalizer hq, fun e he => ?_, fun q' hq' => ?_⟩
      · rw [hEcent e he q (hQS hq), mul_inv_cancel_right]
      · have := hcommE q' (hQS hq') q⁻¹ (Sg.inv_mem (hQS hq))
        simpa [mul_assoc] using this
    · intro c hc
      refine ⟨hCN hc, fun e he => ?_, fun q hq => ?_⟩
      · rw [← Subgroup.mem_centralizer_iff.mp hc e (hEQ he), mul_inv_cancel_right]
      · rw [← Subgroup.mem_centralizer_iff.mp hc q hq, mul_inv_cancel_right, inv_mul_cancel]
        exact E.one_mem
  have hRN : R ≤ Subgroup.normalizer (Q : Set G) := fun r hr => hr.1
  have hconjR : ∀ m ∈ Subgroup.normalizer (Q : Set G), ∀ r ∈ R, m * r * m⁻¹ ∈ R := by
    intro m hm r hr
    obtain ⟨hrN, hrE, hrQ⟩ := hr
    have hm' : m⁻¹ ∈ Subgroup.normalizer (Q : Set G) := Subgroup.inv_mem _ hm
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hrN) hm', fun e he => ?_, fun q hq => ?_⟩
    · have he' := hEstable m⁻¹ hm' e he
      rw [inv_inv] at he'
      have h := hrE _ he'
      calc m * r * m⁻¹ * e * (m * r * m⁻¹)⁻¹ = m * (r * (m⁻¹ * e * m) * r⁻¹) * m⁻¹ := by group
        _ = e := by rw [h]; group
    · have hq' : m⁻¹ * q * m ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp hm' q).mp hq
        simpa using this
      have h := hrQ _ hq'
      have h2 := hEstable m hm _ h
      have : q⁻¹ * (m * r * m⁻¹ * q * (m * r * m⁻¹)⁻¹) =
          m * ((m⁻¹ * q * m)⁻¹ * (r * (m⁻¹ * q * m) * r⁻¹)) * m⁻¹ := by group
      rw [this]; exact h2
  have hNR : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (R : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · exact hconjR m hm r
    · intro h
      have := hconjR m⁻¹ (Subgroup.inv_mem _ hm) _ h
      simpa [mul_assoc] using this
  have hsq : ∀ r ∈ R, r ^ 2 ∈ C := by
    intro r hr
    obtain ⟨hrN, hrE, hrQ⟩ := hr
    rw [hC, Subgroup.mem_centralizer_iff]
    intro q hq
    have he := hrQ q hq
    set e := q⁻¹ * (r * q * r⁻¹) with hedef
    have hrq : r * q * r⁻¹ = q * e := by rw [hedef]; group
    have hre : r * e * r⁻¹ = e := hrE e he
    have h2 : r ^ 2 * q * (r ^ 2)⁻¹ = q := by
      calc r ^ 2 * q * (r ^ 2)⁻¹ = r * (r * q * r⁻¹) * r⁻¹ := by rw [sq]; group
        _ = r * (q * e) * r⁻¹ := by rw [hrq]
        _ = (r * q * r⁻¹) * (r * e * r⁻¹) := by group
        _ = q * e * e := by rw [hrq, hre, mul_assoc]
        _ = q := by rw [mul_assoc, ← sq, he.2, mul_one]
    calc q * r ^ 2 = r ^ 2 * q * (r ^ 2)⁻¹ * r ^ 2 := by rw [h2]
      _ = r ^ 2 * q := by group
  have hNQC : R ≤ Subgroup.normalizer ((Q ⊔ C : Subgroup G) : Set G) := by
    intro r hr
    have hrN := hRN hr
    apply mem_normalizer_of_map_conj_eq
    rw [Subgroup.map_sup]
    have hQm : Q.map (MulAut.conj r).toMonoidHom = Q := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hrN y).mp hy
      · intro hx
        refine ⟨r⁻¹ * x * r, ?_, by simp [mul_assoc]⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrN) x).mp hx
        simpa using this
    have hCm : C.map (MulAut.conj r).toMonoidHom = C := by
      have hle : ∀ n ∈ Subgroup.normalizer (Q : Set G), ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
        intro n hn c hc
        rw [hC, Subgroup.mem_centralizer_iff]
        intro q hq
        have hq' : n⁻¹ * q * n ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) q).mp hq
          simpa using this
        have h := Subgroup.mem_centralizer_iff.mp hc _ hq'
        calc q * (n * c * n⁻¹) = n * ((n⁻¹ * q * n) * c) * n⁻¹ := by group
          _ = n * (c * (n⁻¹ * q * n)) * n⁻¹ := by rw [h]
          _ = n * c * n⁻¹ * q := by group
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hle r hrN y hy
      · intro hx
        refine ⟨r⁻¹ * x * r, ?_, by simp [mul_assoc]⟩
        have := hle r⁻¹ (Subgroup.inv_mem _ hrN) x hx
        simpa using this
    rw [hQm, hCm]
  have hidx : ∃ k : ℕ, ((Q ⊔ C).subgroupOf R).index = 2 ^ k := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hNQC
    have hp : IsPGroup 2 (R ⧸ (Q ⊔ C).subgroupOf R) := by
      intro x
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective x
      refine ⟨1, ?_⟩
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact (le_sup_right : C ≤ Q ⊔ C) (hsq r r.2)
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    exact ⟨k, hk⟩
  have hReq := hrad R hQCR hRN hNR hidx
  have hSR : Sg ≤ R := by
    intro s hs
    refine ⟨?_, fun e he => ?_, fun q hq => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro q
      constructor
      · exact hQnormal s hs q
      · intro h
        have := hQnormal s⁻¹ (Sg.inv_mem hs) _ h
        simpa [mul_assoc] using this
    · rw [hEcent e he s hs, mul_inv_cancel_right]
    · have := hcommE q (hQS hq) s⁻¹ (Sg.inv_mem hs)
      simpa [mul_assoc] using this
  apply le_antisymm hQS
  intro s hs
  have hsQC : s ∈ Q ⊔ C := hReq ▸ hSR hs
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left Q C hCN
  have hs' : s ∈ ((Q ⊔ C : Subgroup G) : Set G) := hsQC
  rw [hset] at hs'
  obtain ⟨q, hq, c, hc, rfl⟩ := hs'
  have hcS : c ∈ Sg := by
    have := Sg.mul_mem (Sg.inv_mem (hQS hq)) hs
    simpa using this
  have hcQ : c ∈ Q := hcentric ⟨hc, hcS⟩
  exact Q.mul_mem hq hcQ

omit [Finite G] in
theorem AlperinDecomposition.mem_normalizer_of_unique {p : ℕ} {S P : Subgroup G} {c : G}
    (huniq : ∀ Q : Subgroup G, CFSG.RankTwoShapes.IsAlperinSubgroup p S Q → Q = S)
    (h : CFSG.RankTwoShapes.AlperinDecomposition p S P c) :
    c ∈ Subgroup.normalizer (S : Set G) := by
  induction h with
  | one => exact Subgroup.one_mem _
  | @step c n Q _ hQ _ hn ih =>
    have hQS := huniq Q hQ
    subst hQS
    exact Subgroup.mul_mem _ ih hn

theorem class_two_normalizer_fusion (S : Sylow 2 G)
    (hinvcent : ∀ x ∈ (S : Subgroup G), x ^ 2 = 1 → ∀ s ∈ (S : Subgroup G), s * x = x * s)
    (hcomm : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), (a⁻¹ * b⁻¹ * a * b) ^ 2 = 1)
    {P : Subgroup G} (hP : P ≤ (S : Subgroup G)) {g : G}
    (hg : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G)) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), ∀ x ∈ P, n⁻¹ * x * n = g⁻¹ * x * g := by
  obtain ⟨c, hc, hcg⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hP hg
  exact ⟨c, AlperinDecomposition.mem_normalizer_of_unique
    (fun Q hQ => alperinSubgroup_eq_of_central_involutions S hinvcent hcomm hQ) hc, hcg⟩

end CFSG.LyonsUnitaryFour

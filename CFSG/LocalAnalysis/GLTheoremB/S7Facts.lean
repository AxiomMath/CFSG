module

public import CFSG.LocalAnalysis.GLTheoremB.S7Decide
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open Equiv Equiv.Perm CFSG.Open

namespace S7

@[expose] def V : Subgroup S := Subgroup.zpowers x ⊔ Subgroup.zpowers y

@[expose] def V' : Subgroup S := Subgroup.zpowers u ⊔ Subgroup.zpowers w

@[expose] def T : Subgroup S := Subgroup.zpowers a ⊔ Subgroup.zpowers b

theorem isPGroup_sup_zpowers {q : ℕ} {g h : S} (hgh : g * h = h * g) (hg : g ^ q = 1)
    (hh : h ^ q = 1) : IsPGroup q ↥(Subgroup.zpowers g ⊔ Subgroup.zpowers h) := by
  have hcomm : ∀ i j : ℤ, Commute (g ^ i) (h ^ j) := fun i j =>
    Commute.zpow_zpow (show Commute g h from hgh) i j
  have hc : Subgroup.zpowers g ≤
      Subgroup.centralizer ((Subgroup.zpowers h : Subgroup S) : Set S) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ((hcomm i j).eq).symm
  intro z
  obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, hz⟩ := exists_mul_of_mem_sup hc z.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (z : S) ^ (q ^ 1) = 1
  rw [hz, pow_one, (hcomm i j).mul_pow]
  have h1 : (g ^ i) ^ q = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  have h2 : (h ^ j) ^ q = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hh, one_zpow]
  rw [h1, h2, one_mul]

abbrev Alt7 : Subgroup S := alternatingGroup (Fin 7)

theorem x_mem_V : x ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)

theorem y_mem_V : y ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

theorem u_mem_V' : u ∈ V' := Subgroup.mem_sup_left (Subgroup.mem_zpowers u)

theorem w_mem_V' : w ∈ V' := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)

theorem a_mem_T : a ∈ T := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)

theorem b_mem_T : b ∈ T := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)

theorem V_le_Alt7 : V ≤ Alt7 :=
  sup_le ((Subgroup.zpowers_le).2 x_mem) ((Subgroup.zpowers_le).2 y_mem)

theorem V'_le_Alt7 : V' ≤ Alt7 :=
  sup_le ((Subgroup.zpowers_le).2 u_mem) ((Subgroup.zpowers_le).2 w_mem)

theorem V_le_centralizer : V ≤ Subgroup.centralizer ({a} : Set S) :=
  sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 a_mul_x.symm))
    ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 a_mul_y.symm))

theorem V'_le_centralizer : V' ≤ Subgroup.centralizer ({b} : Set S) :=
  sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 b_mul_u.symm))
    ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 b_mul_w.symm))

theorem isPGroup_V : IsPGroup 2 ↥V :=
  isPGroup_sup_zpowers x_mul_y (by rw [pow_two]; exact x_mul_x) (by rw [pow_two]; exact y_mul_y)

theorem isPGroup_V' : IsPGroup 2 ↥V' :=
  isPGroup_sup_zpowers u_mul_w (by rw [pow_two]; exact u_mul_u) (by rw [pow_two]; exact w_mul_w)

theorem isPGroup_T : IsPGroup 3 ↥T := isPGroup_sup_zpowers a_mul_b a_pow_three b_pow_three

theorem V_ne_bot : V ≠ ⊥ := by
  intro h
  have : x ∈ (⊥ : Subgroup S) := h ▸ x_mem_V
  rw [Subgroup.mem_bot] at this
  revert this
  decide

theorem V'_ne_bot : V' ≠ ⊥ := by
  intro h
  have : u ∈ (⊥ : Subgroup S) := h ▸ u_mem_V'
  rw [Subgroup.mem_bot] at this
  revert this
  decide

theorem conj_mem_sup_zpowers {g h c v : S}
    (hg : c * g * c⁻¹ ∈ Subgroup.zpowers g ⊔ Subgroup.zpowers h)
    (hh : c * h * c⁻¹ ∈ Subgroup.zpowers g ⊔ Subgroup.zpowers h)
    (hv : v ∈ Subgroup.zpowers g ⊔ Subgroup.zpowers h) :
    c * v * c⁻¹ ∈ Subgroup.zpowers g ⊔ Subgroup.zpowers h := by
  have hle : (Subgroup.zpowers g ⊔ Subgroup.zpowers h).map (MulAut.conj c).toMonoidHom ≤
      Subgroup.zpowers g ⊔ Subgroup.zpowers h := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le ((Subgroup.zpowers_le).2 hg) ((Subgroup.zpowers_le).2 hh)
  exact hle ⟨v, hv, rfl⟩

theorem mem_normalizer_V_of_comm {c : S} (h : c * a = a * c) :
    c ∈ Subgroup.normalizer (V : Set S) := by
  have key : ∀ {c : S}, c * a = a * c → ∀ v ∈ V, c * v * c⁻¹ ∈ V := by
    intro c h v hv
    refine conj_mem_sup_zpowers ?_ ?_ hv
    · rcases conj_x_of_comm_a h with h1 | h1 | h1 <;> rw [h1]
      · exact x_mem_V
      · exact y_mem_V
      · exact V.mul_mem x_mem_V y_mem_V
    · rcases conj_y_of_comm_a h with h1 | h1 | h1 <;> rw [h1]
      · exact x_mem_V
      · exact y_mem_V
      · exact V.mul_mem x_mem_V y_mem_V
  refine Subgroup.mem_normalizer_iff.2 fun v => ⟨key h v, fun hv => ?_⟩
  have h' : c⁻¹ * a = a * c⁻¹ := by
    calc c⁻¹ * a = c⁻¹ * (a * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * a) * c⁻¹ := by rw [h]
      _ = a * c⁻¹ := by group
  have := key h' _ hv
  simpa [mul_assoc] using this

theorem mem_normalizer_V'_of_comm {c : S} (h : c * b = b * c) :
    c ∈ Subgroup.normalizer (V' : Set S) := by
  have key : ∀ {c : S}, c * b = b * c → ∀ v ∈ V', c * v * c⁻¹ ∈ V' := by
    intro c h v hv
    refine conj_mem_sup_zpowers ?_ ?_ hv
    · rcases conj_u_of_comm_b h with h1 | h1 | h1 <;> rw [h1]
      · exact u_mem_V'
      · exact w_mem_V'
      · exact V'.mul_mem u_mem_V' w_mem_V'
    · rcases conj_w_of_comm_b h with h1 | h1 | h1 <;> rw [h1]
      · exact u_mem_V'
      · exact w_mem_V'
      · exact V'.mul_mem u_mem_V' w_mem_V'
  refine Subgroup.mem_normalizer_iff.2 fun v => ⟨key h v, fun hv => ?_⟩
  have h' : c⁻¹ * b = b * c⁻¹ := by
    calc c⁻¹ * b = c⁻¹ * (b * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * b) * c⁻¹ := by rw [h]
      _ = b * c⁻¹ := by group
  have := key h' _ hv
  simpa [mul_assoc] using this

theorem T_le_normalizer_V : T ≤ Subgroup.normalizer (V : Set S) := by
  refine sup_le ((Subgroup.zpowers_le).2 (mem_normalizer_V_of_comm rfl))
    ((Subgroup.zpowers_le).2 ?_)
  have key : ∀ v ∈ V, b * v * b⁻¹ ∈ V := by
    intro v hv
    refine conj_mem_sup_zpowers ?_ ?_ hv
    · rcases b_conj_x with h1 | h1 | h1 <;> rw [h1]
      · exact x_mem_V
      · exact y_mem_V
      · exact V.mul_mem x_mem_V y_mem_V
    · rcases b_conj_y with h1 | h1 | h1 <;> rw [h1]
      · exact x_mem_V
      · exact y_mem_V
      · exact V.mul_mem x_mem_V y_mem_V
  refine Subgroup.mem_normalizer_iff.2 fun v => ⟨key v, fun hv => ?_⟩
  have hinv : b⁻¹ = b * b := inv_eq_of_mul_eq_one_right (by
    have := b_pow_three
    rwa [pow_succ, pow_two, mul_assoc] at this)
  have h2 := key _ (key _ hv)
  have h3 : b * (b * (b * v * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * v * (b * b * b)⁻¹ := by group
  rw [h3] at h2
  have h4 : b * b * b = 1 := by
    have := b_pow_three
    rwa [pow_succ, pow_two, mul_assoc] at this
  simpa [h4] using h2

theorem card_S : Nat.card S = 5040 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem nine_le_card_T : 9 ≤ Nat.card ↥T := by
  have hinj : Function.Injective (fun p : Fin 3 × Fin 3 => a ^ p.1.val * b ^ p.2.val) := by
    decide
  let f : Fin 3 × Fin 3 → ↥T := fun p =>
    ⟨a ^ p.1.val * b ^ p.2.val, T.mul_mem (T.pow_mem a_mem_T _) (T.pow_mem b_mem_T _)⟩
  have hf : Function.Injective f := fun p q h => hinj (congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem card_le_nine {P : Subgroup S} (hP : IsPGroup 3 ↥P) : Nat.card ↥P ≤ 9 := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : Nat.card ↥P ∣ 5040 := card_S ▸ Subgroup.card_subgroup_dvd_card P
  rw [hk] at hdvd ⊢
  by_contra hlt
  have hk3 : 3 ≤ k := by
    by_contra h
    interval_cases k <;> simp at hlt
  have h3 : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 hk3
  have h27 : 27 ∣ 5040 := (show (27 : ℕ) = 3 ^ 3 by norm_num) ▸ h3.trans hdvd
  omega

theorem card_T : Nat.card ↥T = 9 := le_antisymm (card_le_nine isPGroup_T) nine_le_card_T

open Pointwise in
theorem mem_conj_smul_iff {P : Subgroup S} {g r : S} :
    r ∈ (MulAut.conj g) • P ↔ g⁻¹ * r * g ∈ P := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]

@[expose] noncomputable def sylowT : Sylow 3 S :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  isPGroup_T.toSylow (by
    have h := Subgroup.card_mul_index T
    rw [card_T, card_S] at h
    omega)

theorem coe_sylowT : (sylowT : Subgroup S) = T := rfl

theorem mem_map_conj {P : Subgroup S} {g n : S} :
    n ∈ P.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * n * g ∈ P := by
  have h : n ∈ P.map (MulAut.conj g).toMonoidHom ↔ (MulAut.conj g).symm n ∈ P :=
    Subgroup.mem_map_equiv (f := MulAut.conj g) (K := P) (x := n)
  rw [h]
  simp [MulAut.conj_symm_apply]

theorem exists_conj_le_T {R : Subgroup S} (hR : IsPGroup 3 ↥R) :
    ∃ g : S, ∀ r ∈ R, g⁻¹ * r * g ∈ T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S sylowT Q
  refine ⟨g, fun r hr => ?_⟩
  have hrQ : r ∈ (Q : Subgroup S) := hRQ hr
  rw [← hg, Sylow.coe_subgroup_smul] at hrQ
  exact mem_conj_smul_iff.1 hrQ

open Pointwise in
theorem exists_conj_eq_T {R : Subgroup S} (hR : Nat.card ↥R = 9) :
    ∃ g : S, ∀ r : S, r ∈ R ↔ g⁻¹ * r * g ∈ T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR3 : IsPGroup 3 ↥R := IsPGroup.of_card (n := 2) (by rw [hR]; norm_num)
  obtain ⟨Q, hRQ⟩ := hR3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S sylowT Q
  have hQ : (Q : Subgroup S) = (MulAut.conj g) • T := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hRQ' : R = (Q : Subgroup S) :=
    Subgroup.eq_of_le_of_card_ge hRQ (by rw [hR]; exact card_le_nine Q.isPGroup')
  refine ⟨g, fun r => ?_⟩
  rw [hRQ', hQ]
  exact mem_conj_smul_iff

theorem six_orbit (i : Fin 7) : ∃ h ∈ V ⊔ V', h 6 = i := by
  have hx : x ∈ V ⊔ V' := le_sup_left (a := V) (b := V') x_mem_V
  have hy : y ∈ V ⊔ V' := le_sup_left (a := V) (b := V') y_mem_V
  have hu : u ∈ V ⊔ V' := le_sup_right (a := V) (b := V') u_mem_V'
  have hw : w ∈ V ⊔ V' := le_sup_right (a := V) (b := V') w_mem_V'
  fin_cases i
  · exact ⟨u * w, (V ⊔ V').mul_mem hu hw, by decide⟩
  · exact ⟨w, hw, by decide⟩
  · exact ⟨u, hu, by decide⟩
  · exact ⟨x * y, (V ⊔ V').mul_mem hx hy, by decide⟩
  · exact ⟨y, hy, by decide⟩
  · exact ⟨x, hx, by decide⟩
  · exact ⟨1, (V ⊔ V').one_mem, by decide⟩

theorem alternatingGroup_le_sup : Alt7 ≤ V ⊔ V' := by
  have hpre : MulAction.IsPretransitive ↥(V ⊔ V') (Fin 7) := by
    rw [MulAction.isPretransitive_iff_base (6 : Fin 7)]
    intro i
    obtain ⟨h, hh, hi⟩ := six_orbit i
    exact ⟨⟨h, hh⟩, hi⟩
  have hprim : MulAction.IsPreprimitive ↥(V ⊔ V') (Fin 7) := by
    refine MulAction.IsPreprimitive.of_prime_card ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
    (g := (x * u) ^ 2) threeCycle
    ((V ⊔ V').pow_mem ((V ⊔ V').mul_mem (le_sup_left (a := V) (b := V') x_mem_V)
      (le_sup_right (a := V) (b := V') u_mem_V')) 2)

theorem isPGroup_map_conj {q : ℕ} {N : Subgroup S} (hN : IsPGroup q ↥N) (g : S) :
    IsPGroup q ↥(N.map (MulAut.conj g).toMonoidHom) :=
  hN.map _

theorem map_conj_le_Alt7 {N : Subgroup S} (hN : N ≤ Alt7) (g : S) :
    N.map (MulAut.conj g).toMonoidHom ≤ Alt7 := by
  rintro _ ⟨n, hn, rfl⟩
  exact Subgroup.Normal.conj_mem inferInstance n (hN hn) g

theorem exists_normalizes {R : Subgroup S} (hR : IsPGroup 3 ↥R) :
    ∃ N : Subgroup S, N ≤ Alt7 ∧ N ≠ ⊥ ∧ IsPGroup 2 ↥N ∧ R ≤ Subgroup.normalizer (N : Set S) := by
  obtain ⟨g, hg⟩ := exists_conj_le_T hR
  refine ⟨V.map (MulAut.conj g).toMonoidHom, map_conj_le_Alt7 V_le_Alt7 g, ?_, ?_, ?_⟩
  · intro h
    exact V_ne_bot ((Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj g).toMonoidHom) V
      (MulAut.conj g).injective).1 h)
  · exact isPGroup_map_conj isPGroup_V g
  · intro r hr
    refine Subgroup.mem_normalizer_iff.2 fun n => ?_
    rw [mem_map_conj, mem_map_conj]
    have ht := T_le_normalizer_V (hg r hr)
    have h := Subgroup.mem_normalizer_iff.1 ht (g⁻¹ * n * g)
    have e : g⁻¹ * (r * n * r⁻¹) * g = (g⁻¹ * r * g) * (g⁻¹ * n * g) * (g⁻¹ * r * g)⁻¹ := by
      group
    rw [e]
    exact h

@[expose] def cA (σ : S) : Subgroup ↥Alt7 :=
  (Subgroup.centralizer ({σ} : Set S)).subgroupOf Alt7

theorem mem_cA {σ : S} {c : ↥Alt7} : c ∈ cA σ ↔ (c : S) * σ = σ * c := by
  unfold cA
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]

theorem le_pCoreOf_subgroupOf {N H : Subgroup S} (hNA : N ≤ Alt7) (hNH : N ≤ H)
    (hN2 : IsPGroup 2 ↥N) (hnorm : ∀ c ∈ Alt7, c ∈ H → c ∈ Subgroup.normalizer (N : Set S)) :
    N.subgroupOf Alt7 ≤ pCoreOf 2 (H.subgroupOf Alt7) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun y hy => hNH hy) ?_
    (hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNA).symm)
  intro c hc
  refine Subgroup.mem_normalizer_iff.2 fun y => ?_
  have h := Subgroup.mem_normalizer_iff.1 (hnorm c c.2 hc) (y : S)
  simpa [Subgroup.mem_subgroupOf] using h

theorem top_le_iSup_pCoreOf {R : Subgroup S} (hR : Nat.card ↥R = 9) :
    (⊤ : Subgroup ↥Alt7) ≤ ⨆ σ ∈ R, ⨆ (_ : σ ≠ 1), pCoreOf 2 (cA σ) := by
  obtain ⟨g, hg⟩ := exists_conj_eq_T hR
  set J : Subgroup ↥Alt7 := ⨆ σ ∈ R, ⨆ (_ : σ ≠ 1), pCoreOf 2 (cA σ) with hJ
  have key : ∀ (P : Subgroup S) (c : S), P ≤ Alt7 → P ≤ Subgroup.centralizer ({c} : Set S) →
      IsPGroup 2 ↥P → (∀ z : S, z * c = c * z → z ∈ Subgroup.normalizer (P : Set S)) → c ∈ T →
      c ≠ 1 → (P.map (MulAut.conj g).toMonoidHom).subgroupOf Alt7 ≤ J := by
    intro P c hPA hPc hP2 hnorm hcT hc1
    have hσR : g * c * g⁻¹ ∈ R := (hg _).2 (by simpa [mul_assoc] using hcT)
    have hσ1 : g * c * g⁻¹ ≠ 1 := by
      intro h
      apply hc1
      have := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using this
    refine le_trans ?_ (le_iSup₂_of_le (g * c * g⁻¹) hσR (le_iSup_of_le hσ1 le_rfl))
    refine le_pCoreOf_subgroupOf (map_conj_le_Alt7 hPA g) ?_ (isPGroup_map_conj hP2 g) ?_
    · rintro _ ⟨p, hp, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have hpc := Subgroup.mem_centralizer_singleton_iff.1 (hPc hp)
      show g * p * g⁻¹ * (g * c * g⁻¹) = g * c * g⁻¹ * (g * p * g⁻¹)
      calc g * p * g⁻¹ * (g * c * g⁻¹) = g * (p * c) * g⁻¹ := by group
        _ = g * (c * p) * g⁻¹ := by rw [hpc]
        _ = g * c * g⁻¹ * (g * p * g⁻¹) := by group
    · intro z _ hz
      have hz' := Subgroup.mem_centralizer_singleton_iff.1 hz
      have hcomm : (g⁻¹ * z * g) * c = c * (g⁻¹ * z * g) := by
        have h1 : z * (g * c * g⁻¹) = g * c * g⁻¹ * z := hz'
        calc (g⁻¹ * z * g) * c = g⁻¹ * (z * (g * c * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * c * g⁻¹ * z) * g := by rw [h1]
          _ = c * (g⁻¹ * z * g) := by group
      have hn := hnorm _ hcomm
      refine Subgroup.mem_normalizer_iff.2 fun n => ?_
      rw [mem_map_conj, mem_map_conj]
      have h := Subgroup.mem_normalizer_iff.1 hn (g⁻¹ * n * g)
      have e : g⁻¹ * (z * n * z⁻¹) * g =
          (g⁻¹ * z * g) * (g⁻¹ * n * g) * (g⁻¹ * z * g)⁻¹ := by group
      rw [e]
      exact h
  have h1 := key V a V_le_Alt7 V_le_centralizer isPGroup_V
    (fun z hz => mem_normalizer_V_of_comm hz) a_mem_T (by decide)
  have h2 := key V' b V'_le_Alt7 V'_le_centralizer isPGroup_V'
    (fun z hz => mem_normalizer_V'_of_comm hz) b_mem_T (by decide)
  intro z _
  have hz : (z : S) ∈ (V ⊔ V').map (MulAut.conj g).toMonoidHom := by
    rw [mem_map_conj]
    exact alternatingGroup_le_sup (by
      have := Subgroup.Normal.conj_mem (inferInstance : Alt7.Normal) (z : S) z.2 g⁻¹
      simpa using this)
  rw [Subgroup.map_sup] at hz
  have hzs : z ∈ ((V.map (MulAut.conj g).toMonoidHom ⊔ V'.map (MulAut.conj g).toMonoidHom)
      ).subgroupOf Alt7 := hz
  rw [Subgroup.subgroupOf_sup (map_conj_le_Alt7 V_le_Alt7 g) (map_conj_le_Alt7 V'_le_Alt7 g)]
    at hzs
  exact sup_le h1 h2 hzs

end S7

end CFSG.LocalAnalysis.GLTheoremB






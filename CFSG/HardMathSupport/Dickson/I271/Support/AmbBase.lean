module

public import CFSG.HardMathSupport.Dickson.I271.Support.Action
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.Dickson.I271.Amb

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Dickson.I271

section Fixed

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_of_isElemAbelian {p : ℕ} {B : Subgroup X} (hB : IsElemAbelian p B) :
    IsPGroup p B := fun g => ⟨1, by
  rw [pow_one]
  exact Subtype.ext (by simpa using hB.2 g g.2)⟩

theorem exists_pElement_centralized {p : ℕ} (hp : p.Prime) {Q E : Subgroup X} (hQ : IsPGroup p Q)
    (hQE : Q ≤ Subgroup.normalizer (E : Set X)) (hpE : p ∣ Nat.card E) :
    ∃ e ∈ E, e ≠ 1 ∧ e ^ p = 1 ∧ ∀ q ∈ Q, q * e = e * q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hmem : ∀ (q : Q) (e : E), (q : X) * (e : X) * (q : X)⁻¹ ∈ E := fun q e =>
    (Subgroup.mem_normalizer_iff.1 (hQE q.2) e).1 e.2
  letI : MulAction Q E :=
    { smul := fun q e => ⟨(q : X) * (e : X) * (q : X)⁻¹, hmem q e⟩
      one_smul := fun e => Subtype.ext (by
        show ((1 : Q) : X) * (e : X) * ((1 : Q) : X)⁻¹ = e
        simp)
      mul_smul := fun q q' e => Subtype.ext (by
        show ((q * q' : Q) : X) * (e : X) * ((q * q' : Q) : X)⁻¹ =
          (q : X) * ((q' : X) * (e : X) * (q' : X)⁻¹) * (q : X)⁻¹
        simp [mul_assoc]) }
  have hmod := hQ.card_modEq_card_fixedPoints E
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints Q E) := by
    have h1 : Nat.card E ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).2 hpE
    exact (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans h1)
  have hcard : Nat.card (E ⊓ Subgroup.centralizer (Q : Set X) : Subgroup X) =
      Nat.card (MulAction.fixedPoints Q E) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨⟨c.1, c.2.1⟩, ?_⟩
        invFun := fun f => ⟨f.1.1, f.1.2, ?_⟩
        left_inv := fun c => rfl
        right_inv := fun f => rfl }
    · rw [MulAction.mem_fixedPoints]
      intro q
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.1 c.2.2 (q : X) q.2
      show (q : X) * (c.1 : X) * (q : X)⁻¹ = c.1
      rw [this]
      group
    · refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
      have := congrArg Subtype.val (MulAction.mem_fixedPoints.1 f.2 ⟨q, hq⟩)
      change q * (f.1 : X) * q⁻¹ = f.1 at this
      calc q * (f.1 : X) = (q * (f.1 : X) * q⁻¹) * q := by group
        _ = (f.1 : X) * q := by rw [this]
  rw [← hcard] at hdvd
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := (E ⊓ Subgroup.centralizer (Q : Set X) :
    Subgroup X)) p hdvd
  refine ⟨c, c.2.1, ?_, ?_, fun q hq => ?_⟩
  · intro h1
    have : c = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hc
    exact hp.one_lt.ne hc
  · have := pow_orderOf_eq_one c
    rw [hc] at this
    exact congrArg Subtype.val this
  · exact Subgroup.mem_centralizer_iff.1 c.2.2 q hq

theorem mem_of_comm_of_isSCp {p : ℕ} {B : Subgroup X} (hB : IsSCp p ⊤ B) {x : X} (hx : x ^ p = 1)
    (hc : ∀ b ∈ B, b * x = x * b) : x ∈ B := by
  have hE : IsElemAbelian p (B ⊔ Subgroup.zpowers x) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hB.2.1 (CFSG.Open.isElemAbelian_zpowers hx)
      (fun b hb z hz => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact (Commute.zpow_right (hc b hb) n).eq)
  have hEB : B ⊔ Subgroup.zpowers x = B := hB.2.2 _ le_top hE le_sup_left
  have : x ∈ B ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rwa [hEB] at this

theorem exists_mem_inf_of_isSCp {p : ℕ} (hp : p.Prime) {K B : Subgroup X} (hB : IsSCp p ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hpK : p ∣ Nat.card K) :
    ∃ x ∈ B, x ∈ K ∧ x ≠ 1 ∧ x ^ p = 1 := by
  obtain ⟨e, heK, he1, hep, hec⟩ :=
    exists_pElement_centralized hp (isPGroup_of_isElemAbelian hB.2.1) hBN hpK
  exact ⟨e, mem_of_comm_of_isSCp hB hep hec, heK, he1, hep⟩

theorem exists_comm_outside_zpowers {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {E₀ : Subgroup K} (hE₀ : IsElemAbelian p E₀) (h2 : p ^ 2 ≤ Nat.card E₀) {P₀ : Sylow p K}
    (hEP : E₀ ≤ P₀) (hPN : (P₀ : Subgroup K) ≤ Subgroup.normalizer (E₀ : Set K)) {x : K}
    (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    ∃ y : K, y ^ p = 1 ∧ y ∉ Subgroup.zpowers x ∧ y * x = x * y := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hxpg : IsPGroup p (Subgroup.zpowers x) :=
    isPGroup_of_isElemAbelian (CFSG.Open.isElemAbelian_zpowers hx)
  obtain ⟨P, hxP⟩ := hxpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P₀ P
  have hxP' : x ∈ (P : Subgroup K) := hxP (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxP'
  set x' : K := g⁻¹ * x * g with hx'
  have hx'P : x' ∈ (P₀ : Subgroup K) := by simpa [hx', MulAut.smul_def] using hxP'
  have hx'p : x' ^ p = 1 := by
    have : x' ^ p = g⁻¹ * x ^ p * g := by
      rw [hx']
      have := conj_pow (a := g⁻¹) (b := x) (i := p)
      simpa using this
    rw [this, hx]; group
  have hx'1 : x' ≠ 1 := by
    intro h
    apply hx1
    have : x = g * x' * g⁻¹ := by rw [hx']; group
    rw [this, h]; group
  have core : ∃ y' : K, y' ^ p = 1 ∧ y' ∉ Subgroup.zpowers x' ∧ y' * x' = x' * y' := by
    have hEpg : IsPGroup p E₀ := isPGroup_of_isElemAbelian hE₀
    obtain ⟨k, hk⟩ := hEpg.exists_card_eq
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      have h3 : p ^ 2 ≤ p ^ 1 := by rw [← hk] at this; exact h2.trans this
      have h4 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
    have hpE₀ : p ∣ Nat.card E₀ := by
      rw [hk]; exact dvd_pow_self p (by omega)
    have hQN : Subgroup.zpowers x' ≤ Subgroup.normalizer (E₀ : Set K) := by
      rw [Subgroup.zpowers_le]; exact hPN hx'P
    obtain ⟨e, heE, he1, hep, hec⟩ := exists_pElement_centralized hp
      (isPGroup_of_isElemAbelian (CFSG.Open.isElemAbelian_zpowers hx'p)) hQN hpE₀
    by_cases hez : e ∈ Subgroup.zpowers x'
    ·
      have hzz : Subgroup.zpowers e = Subgroup.zpowers x' := by
        have hcard : Nat.card (Subgroup.zpowers x') = p := by
          rw [Nat.card_zpowers]; exact orderOf_eq_prime hx'p hx'1
        refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hez) ?_)
        rw [hcard, Nat.card_zpowers, orderOf_eq_prime hep he1]
      have hx'E : x' ∈ E₀ := by
        have : x' ∈ Subgroup.zpowers e := hzz ▸ Subgroup.mem_zpowers x'
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 this
        rw [← hn]; exact E₀.zpow_mem heE n
      have hnle : ¬ E₀ ≤ Subgroup.zpowers x' := by
        intro hle
        have hcard : Nat.card (Subgroup.zpowers x') = p := by
          rw [Nat.card_zpowers]; exact orderOf_eq_prime hx'p hx'1
        have := Subgroup.card_le_of_le hle
        rw [hcard] at this
        have h5 : p < p ^ 2 := by
          calc p = p ^ 1 := (pow_one p).symm
            _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
        omega
      obtain ⟨y', hy'E, hy'z⟩ := Set.not_subset.1 hnle
      refine ⟨y', hE₀.2 y' hy'E, hy'z, ?_⟩
      have := hE₀.1.is_comm.comm ⟨y', hy'E⟩ ⟨x', hx'E⟩
      exact congrArg Subtype.val this
    · exact ⟨e, hep, hez, (hec x' (Subgroup.mem_zpowers x')).symm⟩
  obtain ⟨y', hy'p, hy'z, hy'c⟩ := core
  refine ⟨g * y' * g⁻¹, ?_, ?_, ?_⟩
  · have : (g * y' * g⁻¹) ^ p = g * y' ^ p * g⁻¹ := conj_pow
    rw [this, hy'p]; group
  · intro hmem
    apply hy'z
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    have h1 : g * y' * g⁻¹ = x ^ n := hn.symm
    have h2 : x' ^ n = g⁻¹ * x ^ n * g := by
      rw [hx']
      have := conj_zpow (a := g⁻¹) (b := x) (i := n)
      simpa using this
    rw [h2, ← h1]; group
  · have h1 : y' * x' = x' * y' := hy'c
    calc g * y' * g⁻¹ * x = g * y' * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * (y' * x') * g⁻¹ := by rw [← hx']; group
      _ = g * (x' * y') * g⁻¹ := by rw [h1]
      _ = x * (g * y' * g⁻¹) := by rw [hx']; group

end Fixed

section Theta

variable {X : Type} [Group X]

theorem actHom_of_mem (K : Subgroup X) {k : X} (hk : k ∈ K) :
    actHom K ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K) := by
  ext z
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
  rw [actHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1

theorem actHom_eq_one_iff {K : Subgroup X} (hperf : commutator ↥K = ⊤) {a : X}
    (haN : a ∈ Subgroup.normalizer (K : Set X)) :
    actHom K ⟨a, haN⟩ = 1 ↔ a ∈ Subgroup.centralizer (K : Set X) := by
  have hker : (actHom K).ker =
      (Subgroup.centralizer (K : Set X)).subgroupOf (Subgroup.normalizer (K : Set X)) :=
    ker_i271Act hperf (MulEquiv.refl _)
  rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]

theorem eq_one_of_mem_centralizer {K : Subgroup X} (hZ : Subgroup.center ↥K = ⊥) {w : X}
    (hwK : w ∈ K) (hwC : w ∈ Subgroup.centralizer (K : Set X)) : w = 1 := by
  have hw : (⟨w, hwK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hwC (g : X) g.2)
  rw [hZ, Subgroup.mem_bot] at hw
  exact congrArg Subtype.val hw

theorem exists_inner_of_actHom_mem_innerAut' {K : Subgroup X} (hperf : commutator ↥K = ⊤) {a : X}
    (haN : a ∈ Subgroup.normalizer (K : Set X))
    (h : actHom K ⟨a, haN⟩ ∈ innerAut (↥K ⧸ Subgroup.center ↥K)) :
    ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X) := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective s
  refine ⟨k', k'.2, ?_⟩
  have hk : actHom K ⟨k', Subgroup.le_normalizer k'.2⟩ =
      MulAut.conj (QuotientGroup.mk k' : ↥K ⧸ Subgroup.center ↥K) := actHom_of_mem K k'.2
  have h1 : actHom K (⟨k', Subgroup.le_normalizer k'.2⟩⁻¹ * ⟨a, haN⟩) = 1 := by
    rw [map_mul, map_inv, hk, hs]
    exact inv_mul_cancel _
  have := (actHom_eq_one_iff hperf (a := (k' : X)⁻¹ * a)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer k'.2)) haN)).1 h1
  exact this

end Theta

section Bridge

variable {X : Type} [Group X] [Finite X]

theorem isStronglyBalancedIn_of_autImage {p : ℕ} {B K : Subgroup X} (hperf : commutator ↥K = ⊤)
    (hbal : ∀ T : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)), Nat.Coprime p (Nat.card T) →
      autImage B K ≤ Subgroup.normalizer (T : Set (MulAut (↥K ⧸ Subgroup.center ↥K))) →
        T = ⊥) :
    IsStronglyBalancedIn p B K := by
  intro S0 hS0N hcop hnorm
  set N : Subgroup X := Subgroup.normalizer (K : Set X) with hN
  set θ := actHom K with hθ
  have hker : θ.ker = (Subgroup.centralizer (K : Set X)).subgroupOf N :=
    ker_i271Act hperf (MulEquiv.refl _)
  set T : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)) := (S0.subgroupOf N).map θ with hT
  have hTcop : Nat.Coprime p (Nat.card T) := by
    have hcard : Nat.card (S0.subgroupOf N) = Nat.card S0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0N).toEquiv
    refine Nat.Coprime.coprime_dvd_right ?_ (hcard ▸ hcop)
    exact Subgroup.card_map_dvd _ _
  have hAT : autImage B K ≤ Subgroup.normalizer (T : Set (MulAut (↥K ⧸ Subgroup.center ↥K))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxn : x ∈ Subgroup.normalizer ((S0.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hx' : (x : X) ∈ B ⊓ N := hx
      have := Subgroup.mem_normalizer_iff.1 (hnorm hx') (h : X)
      simpa [Subgroup.mem_subgroupOf] using this
    exact Subgroup.le_normalizer_map θ (Subgroup.mem_map_of_mem θ hxn)
  have hTbot : T = ⊥ := hbal T hTcop hAT
  intro s hs
  have hsN : s ∈ N := hS0N hs
  have h1 : θ ⟨s, hsN⟩ ∈ T := Subgroup.mem_map_of_mem θ ((Subgroup.mem_subgroupOf).2 hs)
  rw [hTbot, Subgroup.mem_bot] at h1
  have h2 : (⟨s, hsN⟩ : ↥N) ∈ θ.ker := h1
  rw [hker, Subgroup.mem_subgroupOf] at h2
  exact h2

end Bridge

section Cyclic

variable {X : Type} [Group X] [Finite X]

theorem exists_zpow_mul_mem_centralizer {p : ℕ} (hp : p.Prime) {K B : Subgroup X}
    (hBel : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hcard : autOrderIn B K = p) {x : X} (hxB : x ∈ B)
    (hxC : x ∉ Subgroup.centralizer (K : Set X)) :
    ∀ b ∈ B, ∃ i : ℤ, (x ^ i)⁻¹ * b ∈ Subgroup.centralizer (K : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup ↥B := (Subgroup.centralizer (K : Set X)).subgroupOf B with hD
  haveI : D.Normal := ⟨fun n hn g => by
    have hc : (g : X) * n = n * g := by
      have := hBel.1.is_comm.comm g ⟨(n : X), n.2⟩
      exact congrArg Subtype.val this
    have : g * n * g⁻¹ = n := Subtype.ext (by
      show (g : X) * (n : X) * (g : X)⁻¹ = n
      rw [hc]; group)
    rw [this]; exact hn⟩
  have hidx : D.index = p := by
    have : autOrderIn B K = D.index := by
      unfold autOrderIn
      rw [inf_of_le_left hBN]
      rfl
    rw [← this, hcard]
  have hq : Nat.card (↥B ⧸ D) = p := by rw [← Subgroup.index_eq_card]; exact hidx
  set x' : ↥B ⧸ D := QuotientGroup.mk (⟨x, hxB⟩ : ↥B) with hx'
  have hx'1 : x' ≠ 1 := by
    intro h
    apply hxC
    have := (QuotientGroup.eq_one_iff _).1 h
    exact Subgroup.mem_subgroupOf.1 this
  have htop : Subgroup.zpowers x' = ⊤ := zpowers_eq_top_of_prime_card hq hx'1
  intro b hb
  have hmem : (QuotientGroup.mk (⟨b, hb⟩ : ↥B) : ↥B ⧸ D) ∈ Subgroup.zpowers x' := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
  refine ⟨i, ?_⟩
  have h1 : (QuotientGroup.mk (((⟨x, hxB⟩ : ↥B) ^ i)⁻¹ * (⟨b, hb⟩ : ↥B)) : ↥B ⧸ D) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, ← hx', hi]
    group
  have h2 := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
  simpa using h2

theorem cyclic_contra {p : ℕ} (hp : p.Prime) {K B : Subgroup X} (hB : IsSCp p ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hZ : Subgroup.center ↥K = ⊥)
    (hcard : autOrderIn B K = p) {x y : X} (hxB : x ∈ B) (hxK : x ∈ K) (hx1 : x ≠ 1)
    (hyK : y ∈ K) (hyp : y ^ p = 1) (hyx : y * x = x * y) (hyn : y ∉ Subgroup.zpowers x) :
    False := by
  have hxC : x ∉ Subgroup.centralizer (K : Set X) := fun h =>
    hx1 (eq_one_of_mem_centralizer hZ hxK h)
  have hcyc := exists_zpow_mul_mem_centralizer hp hB.2.1 hBN hcard hxB hxC
  have hyB : y ∈ B := by
    refine mem_of_comm_of_isSCp hB hyp fun b hb => ?_
    obtain ⟨i, hi⟩ := hcyc b hb
    set c : X := (x ^ i)⁻¹ * b with hc
    have hb' : b = x ^ i * c := by rw [hc]; group
    have hyxi : y * x ^ i = x ^ i * y := (Commute.zpow_right hyx i).eq
    have hyc : c * y = y * c := (Subgroup.mem_centralizer_iff.1 hi y hyK).symm
    rw [hb']
    calc x ^ i * c * y = x ^ i * (c * y) := by group
      _ = x ^ i * (y * c) := by rw [hyc]
      _ = (x ^ i * y) * c := by group
      _ = (y * x ^ i) * c := by rw [hyxi]
      _ = y * (x ^ i * c) := by group
  obtain ⟨j, hj⟩ := hcyc y hyB
  have hjK : (x ^ j)⁻¹ * y ∈ K :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hxK j)) hyK
  have h1 := eq_one_of_mem_centralizer hZ hjK hj
  apply hyn
  exact Subgroup.mem_zpowers_iff.2 ⟨j, by
    have := congrArg (fun w => x ^ j * w) h1
    simpa using this.symm⟩

end Cyclic

section CenterBot

theorem conj_injective_of_center_bot {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro g g' h
  have hc : g'⁻¹ * g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun x => by
    have hx := DFunLike.congr_fun h x
    simp only [MulAut.conj_apply] at hx
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
      _ = g'⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

@[expose] noncomputable def mulEquivOfCenterBot {K Q : Type} [Group K] [Group Q]
    (hZ : Subgroup.center K = ⊥) (e : K ⧸ Subgroup.center K ≃* Q) : K ≃* Q :=
  MulEquiv.ofBijective (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
    ⟨fun a b hab => by
      have h1 : (QuotientGroup.mk a : K ⧸ Subgroup.center K) = QuotientGroup.mk b := e.injective hab
      have h2 := QuotientGroup.eq.1 h1
      rw [hZ, Subgroup.mem_bot] at h2
      exact inv_mul_eq_one.1 h2,
     e.surjective.comp (QuotientGroup.mk'_surjective _)⟩

end CenterBot

end CFSG.HardMathSupport.Dickson.I271.Amb

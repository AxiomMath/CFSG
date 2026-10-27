module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4Assembly
public import CFSG.LieType.Chevalley.RootHyperplaneGenerationR
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311e
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311d2
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Abstract
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Lang
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5SigmaStd
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Std
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.FrameLines

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311n

open CFSG.Open CFSG.LieType.SeitzGeneration
open CFSG.LieType.Chevalley (hyperRSet)


section Generic

variable {G : Type*} [Group G]

theorem exists_rPart_mul_n {g : G} (hg : orderOf g ≠ 0) {r : ℕ} (hr : r.Prime) (m : ℕ) :
    ∃ u v : G, g = u * v ∧ u ∈ Subgroup.zpowers g ∧ (∃ n : ℕ, u ^ r ^ n = 1) ∧
      v ∈ Subgroup.zpowers (g ^ r ^ m) := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hg r hr.ne_one
  have hcop : Nat.Coprime (r ^ m) b :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hr).2 hb)
  obtain ⟨x, z, hxz⟩ := (Nat.isCoprime_iff_coprime.2 hcop : IsCoprime ((r ^ m : ℕ) : ℤ) (b : ℤ))
  refine ⟨g ^ (z * (b : ℤ)), g ^ (x * ((r ^ m : ℕ) : ℤ)), ?_, Subgroup.mem_zpowers_iff.2 ⟨_, rfl⟩,
    ⟨a, ?_⟩, Subgroup.mem_zpowers_iff.2 ⟨x, ?_⟩⟩
  · rw [← zpow_add]
    conv_lhs => rw [← zpow_one g]
    congr 1
    linarith
  · rw [← zpow_natCast, ← zpow_mul]
    have e : z * (b : ℤ) * ((r ^ a : ℕ) : ℤ) = ((orderOf g : ℕ) : ℤ) * z := by
      rw [hab]
      push_cast
      ring
    rw [e, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · rw [← zpow_natCast, ← zpow_mul, mul_comm]

theorem exists_mem_pow_eq_of_mul_n {X : Subgroup G} {k k₀ g : G} (hg : g ∈ X) (hk : k = k₀ * g)
    (hkX : ∀ z ∈ X, k⁻¹ * z * k ∈ X) : ∀ j : ℕ, ∃ x ∈ X, k₀ ^ j = k ^ j * x := by
  have hk₀ : k₀ = k * g⁻¹ := by rw [hk]; group
  intro j
  induction j with
  | zero => exact ⟨1, X.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨x, hx, hj⟩ := ih
    refine ⟨k⁻¹ * x * k * g⁻¹, X.mul_mem (hkX x hx) (X.inv_mem hg), ?_⟩
    rw [pow_succ, hj, pow_succ, hk₀]
    group

theorem exists_rElement_mul_of_mul_n {X : Subgroup G} {k k₀ g : G} {r m : ℕ} (hr : r.Prime)
    (hk₀ : orderOf k₀ ≠ 0) (hg : g ∈ X) (hk : k = k₀ * g) (hkX : ∀ z ∈ X, k⁻¹ * z * k ∈ X)
    (hkr : k ^ r ^ m = 1) :
    ∃ u v : G, k₀ = u * v ∧ u ∈ Subgroup.zpowers k₀ ∧ (∃ n : ℕ, u ^ r ^ n = 1) ∧ v ∈ X := by
  obtain ⟨u, v, huv, hu, hur, hv⟩ := exists_rPart_mul_n hk₀ hr m
  obtain ⟨x, hx, hpow⟩ := exists_mem_pow_eq_of_mul_n hg hk hkX (r ^ m)
  rw [hkr, one_mul] at hpow
  refine ⟨u, v, huv, hu, hur, ?_⟩
  have hle : Subgroup.zpowers (k₀ ^ r ^ m) ≤ X := by
    rw [Subgroup.zpowers_le, hpow]
    exact hx
  exact hle hv

theorem mem_closure_hyperRSet_of_commute_pair_n {Y : Type*} [Group Y] {p r : ℕ} [hp : Fact p.Prime]
    {E : Subgroup Y} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) {y e : Y}
    (hy : y ∈ E) (he : e ∈ E) (hy1 : y ≠ 1) (hey : e ∉ Subgroup.zpowers y) {k : Y}
    (hky : k * y = y * k) (hke : k * e = e * k) (hkr : ∃ n : ℕ, k ^ r ^ n = 1) :
    k ∈ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ E r p) := by
  classical
  have hFE : Subgroup.closure {y, e} ≤ E := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [hy, he]
  have hye : y * e = e * y := congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨e, he⟩)
  have hyp : y ^ p = 1 := hE.2 y hy
  have hep : e ^ p = 1 := hE.2 e he
  have hcardF : Nat.card (Subgroup.closure ({y, e} : Set Y)) = p ^ 2 := by
    have : NeZero p := ⟨hp.out.ne_zero⟩
    have hle := CFSG.HardMathSupport.Lang.TwE6Step3.card_closure_pair_le_sq hye hyp hep
    have hzy : Nat.card (Subgroup.zpowers y) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hyp hy1]
    have hlt : Subgroup.zpowers y < Subgroup.closure {y, e} := by
      refine lt_of_le_of_ne ?_ fun h => hey ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
      · rw [h]
        exact Subgroup.subset_closure (by simp)
    have hfinE : Finite E :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
    have : Finite (Subgroup.closure ({y, e} : Set Y)) :=
      Finite.of_injective (Subgroup.inclusion hFE) (Subgroup.inclusion_injective hFE)
    have hgt := Subgroup.card_lt_of_lt hlt
    have hdvd : Nat.card (Subgroup.closure ({y, e} : Set Y)) ∣ p ^ 3 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hFE
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    rw [hk'] at hle hgt ⊢
    rw [hzy] at hgt
    have h2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle
    have h1 : 1 < k := by
      by_contra hk1
      push Not at hk1
      interval_cases k
      · simp at hgt
        exact absurd hgt (by have := hp.out.one_lt; omega)
      · simp at hgt
    have : k = 2 := by omega
    rw [this]
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _, hkr, Subgroup.closure {y, e}, hFE,
    CFSG.HardMathSupport.Malle.SeitzCube.relIndex_eq_of_card hFE hp.out.pos hcardF hcard, ?_⟩
  have hc : Subgroup.closure {y, e} ≤ Subgroup.centralizer {k} := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hx with rfl | rfl
    exacts [hky.symm, hke.symm]
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  exact Subgroup.mem_centralizer_singleton_iff.1 (hc hf)

theorem commute_of_mem_zpowers_n {u k₀ e : G} (hu : u ∈ Subgroup.zpowers k₀) (h : k₀ * e = e * k₀) :
    u * e = e * u := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  exact (Commute.zpow_left (h : Commute k₀ e) j).eq

theorem mem_closure_hyperRSet_of_commute_cube_n {p r : ℕ} [hp : Fact p.Prime] {E : Subgroup G}
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) {y : G} (hy : y ∈ E) (hy1 : y ≠ 1) {u : G}
    (hu : ∀ e ∈ E, u * e = e * u) (hur : ∃ n : ℕ, u ^ r ^ n = 1) :
    u ∈ Subgroup.closure (hyperRSet ⊤ E r p) := by
  classical
  have hEfin : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hEc]; exact pow_ne_zero _ hp.out.ne_zero)
  obtain ⟨e, he, hey⟩ : ∃ e ∈ E, e ∉ Subgroup.zpowers y := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers y := fun e he => hcon e he
    have hzf : Finite (Subgroup.zpowers y) := by
      have : Subgroup.zpowers y ≤ E := Subgroup.zpowers_le.2 hy
      exact Finite.of_injective _ (Subgroup.inclusion_injective this)
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime (hE.2 y hy) hy1, hEc] at h1
    have h2 : p < p ^ 3 := by
      have := hp.out.one_lt
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right this (by norm_num)
    omega
  exact mem_closure_hyperRSet_of_commute_pair_n hE hEc hy he hy1 hey (hu y hy) (hu e he) hur

end Generic

section LayerR

open CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7 (catTwistedAFive_center_eq_bot not_dvd_of_dvd_phiSix
  ne_two_of_dvd_phiSix)


theorem layer_le_closure_hyperRSet_of_plane_n {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid)
    (hpq : p ∣ q.card ^ 2 - q.card + 1)
    (E : Subgroup G) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3)
    {y : G} (hyE : y ∈ E) (hy1 : y ≠ 1) (L : Subgroup G) (hLperf : Group.IsPerfect L)
    (hLy : ∀ l ∈ L, l * y = y * l)
    (ρ : L →* Cat ⟨.twistedA 5 q, hv⟩) (hρ : Function.Surjective ρ)
    (hρker : ∀ z ∈ ρ.ker, ∀ u : L, z * u = u * z)
    (β : E →* Cat ⟨.twistedA 5 q, hv⟩) (hβy : β ⟨y, hyE⟩ = 1) (hβcard : Nat.card β.range = p ^ 2)
    (hcomm : ∀ (e : E) (l : L), ρ l * β e = β e * ρ l → (l : G) * e = e * (l : G)) :
    L ≤ Subgroup.closure (hyperRSet ⊤ E q.p p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero 3 hp.ne_zero)
  obtain ⟨hn0, -, -⟩ := not_dvd_of_dvd_phiSix hp hp3 hpq
  have hp2 := ne_two_of_dvd_phiSix hpq
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · subst h
      exact absurd hp (by norm_num)
    · exact h
  set N : Subgroup G := Subgroup.closure (hyperRSet ⊤ E q.p p) with hN
  have hnotmem : ∀ e : E, β e ≠ 1 → (e : G) ∉ Subgroup.zpowers y := by
    intro e he1 hyz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hyz
    apply he1
    have : e = (⟨y, hyE⟩ : E) ^ m := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
    rw [this, map_zpow, hβy, one_zpow]
  have hcenter := catTwistedAFive_center_eq_bot hv
  have hconjinj : Function.Injective
      (MulAut.conj : Cat ⟨.twistedA 5 q, hv⟩ →* MulAut (Cat ⟨.twistedA 5 q, hv⟩)) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have : a ∈ Subgroup.center (Cat ⟨.twistedA 5 q, hv⟩) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun m : MulAut _ => m g) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rwa [hcenter, Subgroup.mem_bot] at this
  let φ : E →* MulAut (Cat ⟨.twistedA 5 q, hv⟩) :=
    (MulAut.conj : Cat ⟨.twistedA 5 q, hv⟩ →* MulAut (Cat ⟨.twistedA 5 q, hv⟩)).comp β
  let E' : Subgroup (MulAut (Cat ⟨.twistedA 5 q, hv⟩)) := φ.range
  have hE'card : Nat.card E' = p ^ 2 := by
    have : E' = β.range.map (MulAut.conj : Cat ⟨.twistedA 5 q, hv⟩ →*
        MulAut (Cat ⟨.twistedA 5 q, hv⟩)) := MonoidHom.range_comp _ _
    rw [this, Subgroup.card_map_of_injective hconjinj, hβcard]
  have hE'el : IsElemAbelian p E' := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨a, ha⟩ := u.2
      obtain ⟨b, hb⟩ := v.2
      apply Subtype.ext
      show (u : MulAut (Cat ⟨.twistedA 5 q, hv⟩)) * v = v * u
      rw [← ha, ← hb, ← map_mul, ← map_mul, hE.1.is_comm.comm a b]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (hE.2 a a.2)
      rw [this, map_one]
  have hinner : InnerPlane ⟨.twistedA 5 q, hv⟩ p E' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨β a, rfl⟩
  have hpd : p ≠ (⟨.twistedA 5 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic := by
    intro h
    have h' : p = q.p := by simpa using h
    apply hn0
    rw [h']
    have : q.p ∣ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne'
    exact Dvd.dvd.pow this two_ne_zero
  have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p (TauCeti.LieTypeIndex.twistedA 5 q) := by
    rintro (⟨h3, _⟩ | ⟨_, h | h⟩)
    · exact hp3 h3
    · cases h
    · cases h
  have hcpf : CentralPrimeFree p (TauCeti.LieTypeIndex.twistedA 5 q) := by
    rintro ⟨-, h6⟩
    have h6' : p ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    interval_cases p
    · norm_num at h6
    · norm_num at hp
  have hgen : Inputs2311c.UniPlaneGen q.p E' := by
    have h := Inputs2311e.uniSeitzPlanes_unitary_inner_five
      Inputs2311d.uniClosure_unitarySU_of_dvd_add_one Inputs2311d.uniClosure_unitarySU_nonsplit
      ⟨.twistedA 5 q, hv⟩ p hp hp2 hpd hex E' hE'el hE'card ⟨hinner, hp5, ⟨5, q, rfl⟩, hcpf⟩
    simpa using h
  set M : Subgroup L := N.comap L.subtype with hM
  have hMmap : M.map ρ = ⊤ := by
    rw [eq_top_iff, ← hgen, Inputs2311c.uniPlaneClosure, Subgroup.closure_le]
    rintro s ⟨ε, ⟨a, rfl⟩, hε1, hεs, n, hn⟩
    obtain ⟨l, rfl⟩ := hρ s
    have ha1 : β a ≠ 1 := fun h => hε1 (by simp [φ, h])
    have hlo : orderOf l ≠ 0 := (orderOf_pos l).ne'
    obtain ⟨u, v, huv, -, hur, hv⟩ := exists_rPart_mul_n hlo q.prime_p n
    have hρv : ρ v = 1 := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      rw [map_zpow, map_pow, hn, one_zpow]
    have hρu : ρ u = ρ l := by rw [huv, map_mul, hρv, mul_one]
    have hcu : ρ u * β a = β a * ρ u := by
      rw [hρu]
      have h : β a * ρ l * (β a)⁻¹ = ρ l := hεs
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    have huN : (u : G) ∈ N := by
      refine mem_closure_hyperRSet_of_commute_pair_n hE hEcard hyE a.2 hy1 (hnotmem a ha1)
        (hLy u u.2) (hcomm a u hcu) ?_
      obtain ⟨n', hn'⟩ := hur
      exact ⟨n', by rw [← Subgroup.coe_pow, hn', Subgroup.coe_one]⟩
    exact ⟨u, huN, hρu⟩
  have hsup : M ⊔ Subgroup.center L = ⊤ := by
    rw [eq_top_iff]
    intro l _
    have hmem : ρ l ∈ M.map ρ := by rw [hMmap]; exact Subgroup.mem_top _
    obtain ⟨m, hm, hml⟩ := Subgroup.mem_map.1 hmem
    have hz : m⁻¹ * l ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := hρker (m⁻¹ * l) (by rw [MonoidHom.mem_ker, map_mul, map_inv, hml, inv_mul_cancel]) g
      exact h.symm
    have hl : l = m * (m⁻¹ * l) := by group
    rw [hl]
    exact Subgroup.mul_mem_sup hm hz
  have hMtop : M = ⊤ := Inputs2311c.eq_top_of_sup_center (Group.isPerfect_def.1 hLperf) hsup
  intro l hl
  have : (⟨l, hl⟩ : L) ∈ M := by rw [hMtop]; exact Subgroup.mem_top _
  exact this

end LayerR

section AbstractR

open CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7 (catTwistedAFive_center_eq_bot exists_hom_sup_of_centralizing
  exists_split_of_fixed exists_central_mul_of_pow_prime commute_of_decomp)


theorem exists_ker_not_mem_zpowers_of_card_ne_n {G C : Type*} [Group G] [Group C] {p : ℕ} (hpp : p.Prime)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) {y : G} (hy : y ∈ E) (hy1 : y ≠ 1)
    (β : E →* C) (hβy : β ⟨y, hy⟩ = 1) (hcard : Nat.card β.range ≠ p ^ 2) :
    ∃ e : E, (e : G) ∉ Subgroup.zpowers y ∧ β e = 1 := by
  classical
  have : Fact p.Prime := ⟨hpp⟩
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; exact pow_ne_zero 3 hpp.ne_zero)
  have hmul := Subgroup.card_ker_mul_card_range β
  obtain ⟨i, hi3, hi⟩ := (Nat.dvd_prime_pow hpp).1 (Subgroup.card_range_dvd β |>.trans
    (by rw [hEc]))
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  have hyker : (⟨y, hy⟩ : E) ∈ β.ker := hβy
  have hpker : p ∣ Nat.card β.ker := by
    have h1 : orderOf (⟨y, hy⟩ : E) = p := by
      rw [← hyo, ← Subgroup.orderOf_coe]
    have h2 := orderOf_dvd_natCard (⟨⟨y, hy⟩, hyker⟩ : β.ker)
    rw [Subgroup.orderOf_mk, h1] at h2
    exact h2
  have hi2 : i ≤ 1 := by
    by_contra hgt
    have h3 : i ≤ 3 := hi3
    have : i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl
    · exact hcard hi
    · rw [hi, show p ^ 3 = Nat.card E from hEc.symm] at hmul
      have : Nat.card β.ker = 1 := by
        have hp3pos : 0 < p ^ 3 := pow_pos hpp.pos 3
        nlinarith
      rw [this] at hpker
      exact hpp.one_lt.ne' (Nat.dvd_one.1 hpker)
  have hkerge : p ^ 2 ≤ Nat.card β.ker := by
    have h1 : Nat.card β.range ≤ p := by
      rw [hi]
      calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hpp.pos hi2
        _ = p := pow_one p
    have h2 : p ^ 3 = Nat.card β.ker * Nat.card β.range := by rw [← hEc, ← hmul]
    have : p ^ 3 ≤ Nat.card β.ker * p := by
      calc p ^ 3 = Nat.card β.ker * Nat.card β.range := h2
        _ ≤ Nat.card β.ker * p := Nat.mul_le_mul_left _ h1
    have hp0 : 0 < p := hpp.pos
    have : p ^ 2 * p ≤ Nat.card β.ker * p := by rwa [← pow_succ]
    exact Nat.le_of_mul_le_mul_right this hp0
  by_contra hno
  push Not at hno
  have hsub : β.ker ≤ Subgroup.zpowers (⟨y, hy⟩ : E) := by
    intro e he
    by_contra hnot
    have := hno e (fun hmem => hnot (by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
      exact Subgroup.mem_zpowers_iff.2 ⟨m, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm)⟩))
    exact this he
  have hcardle : Nat.card β.ker ≤ Nat.card (Subgroup.zpowers (⟨y, hy⟩ : E)) :=
    Subgroup.card_le_of_le hsub
  rw [Nat.card_zpowers] at hcardle
  have h1 : orderOf (⟨y, hy⟩ : E) = p := by
    rw [← hyo, ← Subgroup.orderOf_coe]
  rw [h1] at hcardle
  have : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
  omega

theorem mem_closure_hyperRSet_of_a5_plane_n
    {G M : Type*} [Group G] [Finite G] [Group M] (θ : M →* M) {H Q P : Subgroup M} {p : ℕ}
    (hpp : p.Prime) (hp3 : 3 < p)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid)
    (hpq : p ∣ q.card ^ 2 - q.card + 1)
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hHQ : H ≤ Subgroup.normalizer (Q : Set M))
    (hθH : ∀ h ∈ H, θ h ∈ H) (hθQ : ∀ g ∈ Q, θ g ∈ Q)
    (hlang : ∀ s ∈ H ⊓ Q, ∃ t ∈ H ⊓ Q, t⁻¹ * θ t = s)
    (hΓ : ∀ g ∈ Q, θ g = g → ∃ s ∈ H ⊓ Q, θ s = s ∧ ∃ x ∈ P, g = s * x)
    (hPQ : P ≤ Q)
    (ρ : P →* Cat ⟨.twistedA 5 q, hv⟩) (hρ : Function.Surjective ρ)
    (hkc : ∀ z ∈ ρ.ker, ∀ u : P, z * u = u * z)
    (hPperf : Group.IsPerfect P)
    (hPnorm : ∀ m ∈ H ⊔ Q, θ m = m → ∀ u ∈ P, m * u * m⁻¹ ∈ P)
    (ψ : G →* M) (hψ : Function.Injective ψ) (E : Subgroup G) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) (hψE : ∀ e ∈ E, ψ e ∈ H)
    {y : G} (hy : y ∈ E) (hy1 : y ≠ 1) (hψy : ∀ g ∈ Q, ψ y * g = g * ψ y)
    (hψN : ∀ k : G, k * y = y * k → ψ k ∈ H ⊔ Q ∧ θ (ψ k) = ψ k)
    (hPψ : ∀ u ∈ P, ∃ g : G, ψ g = u)
    (β : E →* Cat ⟨.twistedA 5 q, hv⟩) (hβy : β ⟨y, hy⟩ = 1) (hcard : Nat.card β.range = p ^ 2)
    (hcommβ : ∀ (e : E) (l : G) (hl : ψ l ∈ P), ρ ⟨ψ l, hl⟩ * β e = β e * ρ ⟨ψ l, hl⟩ →
      l * e = e * l)
    {k : G} (hk : k * y = y * k) {n₀ : ℕ} (hn₀ : k ^ q.p ^ n₀ = 1) :
    k ∈ Subgroup.closure (hyperRSet ⊤ E q.p p) := by
  classical
  have : Fact p.Prime := ⟨hpp⟩
  have hp3' : p ≠ 3 := by omega
  set N : Subgroup G := Subgroup.closure (hyperRSet ⊤ E q.p p) with hN
  set L : Subgroup G := P.comap ψ with hL
  let ρL : L →* Cat ⟨.twistedA 5 q, hv⟩ := ρ.comp (ψ.subgroupComap P)
  have hρL : Function.Surjective ρL := by
    intro c
    obtain ⟨u, rfl⟩ := hρ c
    obtain ⟨g, hg⟩ := hPψ u u.2
    refine ⟨⟨g, Subgroup.mem_comap.2 (by rw [hg]; exact u.2)⟩, ?_⟩
    show ρ ⟨ψ g, _⟩ = ρ u
    congr 1
    exact Subtype.ext hg
  have hLy : ∀ l ∈ L, l * y = y * l := by
    intro l hl
    apply hψ
    rw [map_mul, map_mul]
    exact (hψy (ψ l) (hPQ hl)).symm
  have hcomm : ∀ (e : E) (l : L), ρL l * β e = β e * ρL l → (l : G) * e = e * (l : G) :=
    fun e l h => hcommβ e l l.2 h
  have hψLbij : Function.Bijective (ψ.subgroupComap P : L →* P) := by
    refine ⟨fun a b hab => Subtype.ext (hψ (congrArg Subtype.val hab)), fun u => ?_⟩
    obtain ⟨g, hg⟩ := hPψ u u.2
    exact ⟨⟨g, Subgroup.mem_comap.2 (by rw [hg]; exact u.2)⟩, Subtype.ext hg⟩
  have hLperf : Group.IsPerfect L := by
    haveI := hPperf
    exact Group.IsPerfect.ofSurjective (f := (MulEquiv.ofBijective _ hψLbij).symm.toMonoidHom)
      (MulEquiv.ofBijective _ hψLbij).symm.surjective
  have hρLker : ∀ z ∈ ρL.ker, ∀ u : L, z * u = u * z := by
    intro z hz u
    have h := hkc (ψ.subgroupComap P z) hz (ψ.subgroupComap P u)
    apply Subtype.ext
    apply hψ
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val h
  have hLN : L ≤ N := layer_le_closure_hyperRSet_of_plane_n hpp hp3' hv hpq E hE hEc hy hy1 L hLperf hLy
    ρL hρL hρLker β hβy hcard hcomm
  obtain ⟨hmN, hθm⟩ := hψN k hk
  obtain ⟨a, haH, -, x, hxP, hax⟩ := exists_split_of_fixed θ hH hHQ hθH hθQ hlang hΓ hmN hθm
  obtain ⟨g, hg⟩ := hPψ x hxP
  have hgL : g ∈ L := Subgroup.mem_comap.2 (by rw [hg]; exact hxP)
  have ha' : ψ (k * g⁻¹) = a := by
    rw [map_mul, map_inv, hg, hax]; group
  have hk₀E : ∀ e ∈ E, (k * g⁻¹) * e = e * (k * g⁻¹) := by
    intro e he
    apply hψ
    rw [map_mul ψ (k * g⁻¹) e, map_mul ψ e (k * g⁻¹), ha']
    exact hH a haH _ (hψE e he)
  have hkL : ∀ z ∈ L, k⁻¹ * z * k ∈ L := by
    intro z hz
    have hz' : ψ z ∈ P := hz
    have hm' : (ψ k)⁻¹ ∈ H ⊔ Q := inv_mem hmN
    have hθm' : θ (ψ k)⁻¹ = (ψ k)⁻¹ := by rw [map_inv, hθm]
    have h := hPnorm _ hm' hθm' _ hz'
    rw [inv_inv] at h
    show ψ (k⁻¹ * z * k) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact h
  obtain ⟨u, v, huv, hu, hur, hvL⟩ := exists_rElement_mul_of_mul_n q.prime_p (orderOf_pos _).ne' hgL
    (show k = (k * g⁻¹) * g by group) hkL hn₀
  have huE : ∀ e ∈ E, u * e = e * u := fun e he => commute_of_mem_zpowers_n hu (hk₀E e he)
  have huN : u ∈ N := mem_closure_hyperRSet_of_commute_cube_n hE hEc hy hy1 huE hur
  have hkuv : k = u * (v * g) := by
    have h1 : k = (k * g⁻¹) * g := by group
    rw [h1, huv, mul_assoc]
  rw [hkuv]
  exact N.mul_mem huN (hLN (L.mul_mem hvL hgL))

theorem mem_closure_hyperRSet_of_abstract_a5_n
    {G M : Type*} [Group G] [Finite G] [Group M] (θ : M →* M) {H Q P : Subgroup M} {p : ℕ}
    (hpp : p.Prime) (hp3 : 3 < p)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid)
    (hpq : p ∣ q.card ^ 2 - q.card + 1)
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hHQ : H ≤ Subgroup.normalizer (Q : Set M))
    (hθH : ∀ h ∈ H, θ h ∈ H) (hθQ : ∀ g ∈ Q, θ g ∈ Q)
    (hθZ : ∀ z ∈ H, (∀ q ∈ Q, z * q = q * z) → ∀ q ∈ Q, θ z * q = q * θ z)
    (hlang : ∀ s ∈ H ⊓ Q, ∃ t ∈ H ⊓ Q, t⁻¹ * θ t = s)
    (hΓ : ∀ g ∈ Q, θ g = g → ∃ s ∈ H ⊓ Q, θ s = s ∧ ∃ x ∈ P, g = s * x)
    (hPQ : P ≤ Q) (hPfix : ∀ x ∈ P, θ x = x)
    (hfree : ∀ m ∈ H ⊔ Q, (∀ u ∈ P, m * u = u * m) → m ∈ H ∧ ∀ g ∈ Q, m * g = g * m)
    (h4 : ∀ t ∈ H, θ t = t → ∃ z ∈ H, (∀ q ∈ Q, z * q = q * z) ∧ ∃ s ∈ H ⊓ Q, t ^ 6 = z * s)
    (h5 : ∀ f ∈ H ⊓ Q, (∀ q ∈ Q, f * q = q * f) → f ^ 6 = 1)
    (h6 : ∀ g ∈ Q, θ g = g → g ^ 6 ∈ P)
    (ρ : P →* Cat ⟨.twistedA 5 q, hv⟩) (hρ : Function.Surjective ρ)
    (hkc : ∀ z ∈ ρ.ker, ∀ u : P, z * u = u * z) (hkcard : Nat.card ρ.ker ∣ 6)
    (hPperf : Group.IsPerfect P)
    (hPnorm : ∀ m ∈ H ⊔ Q, θ m = m → ∀ u ∈ P, m * u * m⁻¹ ∈ P)
    (ψ : G →* M) (hψ : Function.Injective ψ) (E : Subgroup G) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) (hψE : ∀ e ∈ E, ψ e ∈ H ∧ θ (ψ e) = ψ e)
    {y : G} (hy : y ∈ E) (hy1 : y ≠ 1) (hψy : ∀ g ∈ Q, ψ y * g = g * ψ y)
    (hψN : ∀ k : G, k * y = y * k → ψ k ∈ H ⊔ Q ∧ θ (ψ k) = ψ k)
    (hPψ : ∀ u ∈ P, ∃ g : G, ψ g = u) {k : G} (hk : k * y = y * k)
    (hkr : ∃ n : ℕ, k ^ q.p ^ n = 1) :
    k ∈ Subgroup.closure (hyperRSet ⊤ E q.p p) := by
  classical
  have : Fact p.Prime := ⟨hpp⟩
  set Z₀ : Subgroup M := H ⊓ MonoidHom.eqLocus θ (MonoidHom.id M) ⊓
    Subgroup.centralizer (Q : Set M) with hZ₀
  have hmemZ₀ : ∀ z, z ∈ Z₀ ↔ z ∈ H ∧ θ z = z ∧ ∀ g ∈ Q, z * g = g * z := by
    intro z
    simp only [hZ₀, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
    change (z ∈ H ∧ θ z = z) ∧ _ ↔ _
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, fun g hg => (h3 g hg).symm⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun g hg => (h3 g hg).symm⟩
  have hZP : ∀ z ∈ Z₀, ∀ u ∈ P, z * u = u * z := fun z hz u hu =>
    ((hmemZ₀ z).1 hz).2.2 u (hPQ hu)
  have hcenter := catTwistedAFive_center_eq_bot hv
  have hZker : ∀ (w : M) (hw : w ∈ P), w ∈ Z₀ → ρ ⟨w, hw⟩ = 1 := by
    intro w hw hwZ
    have : ρ ⟨w, hw⟩ ∈ Subgroup.center (Cat ⟨.twistedA 5 q, hv⟩) := by
      rw [Subgroup.mem_center_iff]
      intro c
      obtain ⟨u, rfl⟩ := hρ c
      rw [← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext (hZP w hwZ u u.2).symm)
    rwa [hcenter, Subgroup.mem_bot] at this
  obtain ⟨ρ', hρ'P, hρ'Z⟩ := exists_hom_sup_of_centralizing hZP ρ hZker
  have hdec : ∀ e ∈ E, ∃ z ∈ Z₀, ∃ x ∈ P, ψ e = z * x := by
    intro e he
    obtain ⟨hψeH, hψeθ⟩ := hψE e he
    have hpow : (ψ e) ^ p = 1 := by rw [← map_pow, hE.2 e he, map_one]
    obtain ⟨z, hzH, hzθ, hzc, x, hxP, hx⟩ := exists_central_mul_of_pow_prime θ hp3 hpp hH hθH hθQ
      hθZ h4 h5 h6 hψeH hψeθ hpow
    exact ⟨z, (hmemZ₀ z).2 ⟨hzH, hzθ, hzc⟩, x, hxP, hx⟩
  have hmemM : ∀ e : E, ψ e ∈ Z₀ ⊔ P := by
    intro e
    obtain ⟨z, hz, x, hx, h⟩ := hdec e e.2
    rw [h]
    exact (Z₀ ⊔ P).mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hx)
  let β : E →* Cat ⟨.twistedA 5 q, hv⟩ :=
    ρ'.comp ((ψ.comp E.subtype).codRestrict (Z₀ ⊔ P) hmemM)
  have hβ : ∀ (e : E) (z x : M) (hz : z ∈ Z₀) (hx : x ∈ P), ψ e = z * x → β e = ρ ⟨x, hx⟩ := by
    intro e z x hz hx h
    have : ((ψ.comp E.subtype).codRestrict (Z₀ ⊔ P) hmemM e) =
        ⟨z, Subgroup.mem_sup_left hz⟩ * ⟨x, Subgroup.mem_sup_right hx⟩ := Subtype.ext h
    show ρ' ((ψ.comp E.subtype).codRestrict (Z₀ ⊔ P) hmemM e) = _
    rw [this, map_mul, hρ'Z z hz, one_mul, hρ'P x hx]
  have hψyZ : ψ y ∈ Z₀ := (hmemZ₀ _).2 ⟨(hψE y hy).1, (hψE y hy).2, hψy⟩
  have hβy : β ⟨y, hy⟩ = 1 := by
    show ρ' ((ψ.comp E.subtype).codRestrict (Z₀ ⊔ P) hmemM ⟨y, hy⟩) = 1
    have : ((ψ.comp E.subtype).codRestrict (Z₀ ⊔ P) hmemM ⟨y, hy⟩) =
        ⟨ψ y, Subgroup.mem_sup_left hψyZ⟩ := rfl
    rw [this]
    exact hρ'Z _ hψyZ
  obtain ⟨n₀, hn₀⟩ := hkr
  by_cases hcard : Nat.card β.range = p ^ 2
  · refine mem_closure_hyperRSet_of_a5_plane_n θ hpp hp3 hv hpq hH hHQ hθH hθQ hlang hΓ hPQ ρ hρ hkc hPperf
      hPnorm ψ hψ E hE hEc (fun e he => (hψE e he).1) hy hy1 hψy hψN hPψ β hβy hcard ?_ hk hn₀
    intro e l hl h
    obtain ⟨z, hz, x, hx, hψe⟩ := hdec e e.2
    have hβe := hβ e z x hz hx hψe
    have hpow : (ψ e) ^ p = 1 := by rw [← map_pow, hE.2 e e.2, map_one]
    have h' : ρ ⟨x, hx⟩ * ρ ⟨ψ l, hl⟩ = ρ ⟨ψ l, hl⟩ * ρ ⟨x, hx⟩ := by
      rw [← hβe]; exact h.symm
    have := commute_of_decomp hpp hp3 ρ hkc hkcard hZP hZker hψe hz hx hl hpow h'
    apply hψ
    rw [map_mul, map_mul]
    exact this.symm
  ·
    obtain ⟨e, hey, hβe⟩ := exists_ker_not_mem_zpowers_of_card_ne_n hpp hE hEc hy hy1 β hβy hcard
    obtain ⟨z, hz, x, hx, hψe⟩ := hdec e e.2
    have hρx : ρ ⟨x, hx⟩ = 1 := by rw [← hβ e z x hz hx hψe]; exact hβe
    have hxker : (⟨x, hx⟩ : P) ∈ ρ.ker := hρx
    have hxZ : x ∈ Z₀ := by
      have hfr := hfree x (Subgroup.mem_sup_right (hPQ hx)) (fun u hu => by
        have := hkc ⟨x, hx⟩ hxker ⟨u, hu⟩
        exact congrArg Subtype.val this)
      exact (hmemZ₀ x).2 ⟨hfr.1, hPfix x hx, fun g hg => hfr.2 g hg⟩
    have heZ : ψ e ∈ Z₀ := by rw [hψe]; exact Z₀.mul_mem hz hxZ
    obtain ⟨hmN, -⟩ := hψN k hk
    have hcent : H ⊔ Q ≤ Subgroup.centralizer {ψ e} := by
      refine sup_le (fun h hh m hm => ?_) (fun g hg m hm => ?_)
      · rw [Set.mem_singleton_iff.1 hm]
        exact (hH _ ((hmemZ₀ _).1 heZ).1 h hh)
      · rw [Set.mem_singleton_iff.1 hm]
        exact ((hmemZ₀ _).1 heZ).2.2 g hg
    have hke : k * e = e * k := by
      apply hψ
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hmN)
    exact mem_closure_hyperRSet_of_commute_pair_n hE hEc hy e.2 hy1 hey hk hke ⟨n₀, hn₀⟩

end AbstractR

section A5LineR

open Matrix CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L
  CFSG.RankThree.Classical2 CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
open scoped MatrixGroups commutatorElement Pointwise

set_option linter.unusedSectionVars false


theorem mem_closure_hyperRSet_of_a5_line_n
    {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p (-1)) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1)
    {c : adjointGroup .E7 K} {E : Subgroup (adjointGroup .E7 K)} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3)
    (hT : ∀ x ∈ E, psiC F.g0 c x ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {y : adjointGroup .E7 K} (hy : y ∈ E) (hy1 : y ≠ 1) (v : WeylGroup Tag.E7)
    (hker : ∀ b : Fin Tag.E7.rank → Lˣ, rootDiagUnit .E7 b = psiC F.g0 c y →
      rootCharKernel b = (fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7))
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        (v⁻¹ * weylQuotientHom Tag.E7 L ⟨F.n, F.hnm⟩ * v) • α = u • ((-1 : ℤ) • α))
    {k : adjointGroup .E7 K} (hk : k * y = y * k) (hkr : ∃ n : ℕ, k ^ ℓ ^ n = 1) :
    k ∈ Subgroup.closure (hyperRSet ⊤ E ℓ p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL Tag.E7 L →* ModGL Tag.E7 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr : ∀ x, Fr x = x ^ Nat.card K := fun x => by
    rw [hK]; exact iterateFrobenius_def ℓ f x
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun z => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq z (show 0 < Nat.card K by
      rw [hK]; exact pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  have hKq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hε : ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) := Or.inr rfl
  have h2 : 2 < ℓ ^ f := by
    rw [← hK]
    exact e7T3_q_gt_two hp3 rfl hKq hpf rfl
  have hstab := e7T3_stabHyp F hK hp hp3 hε hpf
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  have hhy : F.g0⁻¹ * adjEmb .E7 K L (c * y * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    simpa [psiC_apply] using hT y hy
  obtain ⟨b, hb, hap, hb1, hbh, -⟩ := e7_three_prelim F hp hyo c hhy
  have hbψ : rootDiagUnit .E7 b = psiC F.g0 c y := by rw [psiC_apply]; exact hbh
  have hSeq := hker b hbψ
  set V : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E7 L := canonicalRep_mem_monomialSubgroup L v
  have hVadj : V ∈ adjointGroup Tag.E7 L := canonicalRep_mem_adjointGroup _ L v
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrbij) v
    have h2 : (RingEquiv.ofBijective Fr hFrbij).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  have hnC : F.n ∈ adjointGroup Tag.E7 L := monomialSubgroup_le_adjointGroup' F.hnm
  set n' : ModGL Tag.E7 L := V⁻¹ * F.n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVm) F.hnm) hVm
  have hn'adj : n' ∈ adjointGroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVadj) hnC) hVadj
  have hπV : weylQuotientHom Tag.E7 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E7 L ⟨F.n, F.hnm⟩ * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E7 L) =
        ⟨V, hVm⟩⁻¹ * ⟨F.n, F.hnm⟩ * ⟨V, hVm⟩ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV]
  have hact' : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ • α = u • ((-1 : ℤ) • α) := by
    obtain ⟨u, hu, hact⟩ := hcert
    exact ⟨u, hu, fun α hα => by rw [hπn']; exact hact α hα⟩
  have halg := isAlgebraic_zmod_of_card (ℓ := ℓ) (L := L) hK
  obtain ⟨u, hu, hu'⟩ := hact'
  obtain ⟨hwS, hwS'⟩ := perm_of_act hu hu'
  have hnw' : MapsRootLines n' (weylQuotientHom Tag.E7 L ⟨n', hn'm⟩) :=
    mapsRootLines_weylQuotientHom ⟨n', hn'm⟩
  let q : TauCeti.PrimePower := ⟨ℓ, f, hℓ, hf⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid := by
    simp
  obtain ⟨Φ', hΦ', hfin, hqs, ρ, hρs, hρc, hρd⟩ :=
    exists_a5Std_data hf halg n' hn'm ⟨u, hu, hu'⟩ (q := q) rfl rfl hv
  let P' : Subgroup (ModGL Tag.E7 L) := (fixSubgroup Φ').map (a5Frame L)
  set Γ' : Subgroup (ModGL Tag.E7 L) :=
    rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
      twistedFixedPoints n' Φ with hΓ'
  have hPeq : ⁅Γ', Γ'⁆ = P' := commutator_Gamma Fr n' Φ' hΦ' hqs
  have hstd := a5_sigmaFactor_std hf halg h2 n' hn'm hn'adj ⟨u, hu, hu'⟩
  have hstd' : SigmaFactor n' Fr (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) (fun _ : Unit => P')
      (Subgroup.normalizer
        (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : Set (ModGL Tag.E7 L))) := by
    rw [← hPeq]; exact hstd
  have hroots : ∀ r ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7), IsRoot Tag.E7 r := fun r hr => hr.1
  have htr := SigmaFactor.transport Fr hFrbij v F.n hroots hstd'
  set c₀ : ModGL Tag.E7 L →* ModGL Tag.E7 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hQ : (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7))).map c₀ =
      rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) :=
    map_conj_rootSpan v hroots
  have hR : (twistedFixedPoints n' Φ).map c₀ = twistedFixedPoints F.n Φ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hcapp]
      exact (mem_twistedFixedPoints_conj hΦV).1 hx
    · intro hy
      refine ⟨V⁻¹ * y * V, (mem_twistedFixedPoints_conj hΦV).2 ?_, ?_⟩
      · have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
        rw [e]
        exact hy
      · rw [hcapp]
        group
  have hΓeq : Γ'.map c₀ = rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7
      (a5Nodes Tag.E7)) ⊓ twistedFixedPoints F.n Φ := by
    rw [hΓ', Subgroup.map_inf _ _ c₀ (MulAut.conj V).injective, hQ, hR]
  have hPeq' : P'.map c₀ = ⁅Γ'.map c₀, Γ'.map c₀⁆ := by
    rw [← hPeq, Subgroup.map_commutator]
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [CFSG.RankThree.Chevalley.rootChar_neg', hα.2, inv_one]⟩
  have hPfin : ∀ i : Unit, Finite (P'.map c₀) := fun _ => htr.finite ()
  have hPq : ∀ i : Unit, CFSG.IsQuasisimple (P'.map c₀) := fun _ => htr.quasi ()
  have hPQ : ∀ i : Unit, P'.map c₀ ≤ rootSpan Tag.E7 L (rootCharKernel b) := fun _ => by
    rw [hSeq]; exact htr.le_root ()
  have hPR : ∀ i : Unit, P'.map c₀ ≤ twistedFixedPoints F.n Φ := fun _ => htr.le_fix ()
  have hPadj : ∀ i : Unit, P'.map c₀ ≤ adjointGroup Tag.E7 L := fun _ => htr.le_adj ()
  have hPnorm : ∀ i : Unit, ∀ y ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L (rootCharKernel b),
      y ∈ twistedFixedPoints F.n Φ → ∀ u ∈ P'.map c₀, y * u * y⁻¹ ∈ P'.map c₀ := by
    intro _ y hy hyR u hu
    rw [hSeq] at hy
    have hyN : y ∈ Subgroup.normalizer
        (rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) :
          Set (ModGL Tag.E7 L)) :=
      sup_le (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan (fun γ hγ => by
        obtain ⟨α, hα, rfl⟩ := hγ
        exact IsRoot.smul hα.1 v)) (Subgroup.le_normalizer) hy
    rw [hPeq', hΓeq] at hu ⊢
    refine conj_mem_commutator_of_normalizes (fun γ hγ => ?_) hu
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hyN γ).1 hγ.1,
      mul_mem (mul_mem hyR hγ.2) (inv_mem hyR)⟩
  have hPcent : ∀ y ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L (rootCharKernel b),
      y ∈ twistedFixedPoints F.n Φ → (∀ i : Unit, ∀ u ∈ P'.map c₀, y * u = u * y) →
      y ∈ subtorusSigma F.n Φ (rootCharKernel b) := by
    intro y hy hyR hc
    rw [hSeq] at hy ⊢
    obtain ⟨hyH, hyC⟩ := htr.thetaFree y hy (fun i u hu => hc i u hu)
    exact Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hyC⟩
  obtain ⟨hcS, hkerZ⟩ := e7_perx_hc_hkerZ (K := K) Fr F.g0 hbh hhy (S := rootCharKernel b) rfl
  obtain ⟨ψS, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, -⟩ := sigma_embedding_data_of_stab
    (adjEmb .E7 K L) adjEmb_injective adjEmb_mem Φ (adjEmb_frobenius Fr hFr) F.n F.g0 F.hg0C
    F.hg0 F.hperf hp (fun a hap ha1 haT => hstab a hap ha1 haT) (fun α hα => hα.1) hSn
    (fun _ : Unit => P'.map c₀) hPfin hPq hPQ hPR hPadj hPnorm hPcent hyo c hcS hkerZ
  have hInvH : ∀ {t : ModGL Tag.E7 L}, t ∈ torusGroup Tag.E7 L →
      V⁻¹ * t * V ∈ torusGroup Tag.E7 L := by
    intro t ht
    have h := (Subgroup.mem_normalizer_iff.1
      (inv_mem (canonicalRep_mem_normalizer (R := L) v)) t).1 ht
    rwa [inv_inv] at h
  have hVconj : ∀ g ∈ rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7
      (a5Nodes Tag.E7)), V⁻¹ * g * V ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) := by
    intro g hg
    rw [← hQ] at hg
    obtain ⟨q', hq', rfl⟩ := hg
    rw [hcapp]
    have e : V⁻¹ * (V * q' * V⁻¹) * V = q' := by group
    rw [e]
    exact hq'
  have hVconj' : ∀ g ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)),
      V * g * V⁻¹ ∈ rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7
        (a5Nodes Tag.E7)) := by
    intro g hg
    rw [← hQ, ← hcapp]
    exact Subgroup.mem_map_of_mem _ hg
  let θ : ModGL Tag.E7 L →* ModGL Tag.E7 L := (MulAut.conj n').toMonoidHom.comp Φ
  have hθapp : ∀ x, θ x = n' * Φ x * n'⁻¹ := fun x => by simp [θ, MulAut.conj_apply]
  let ψ₁ : adjointGroup .E7 K →* ModGL Tag.E7 L :=
    (MulAut.conj V⁻¹).toMonoidHom.comp (psiC F.g0 c)
  have hψ₁ : ∀ x, ψ₁ x = V⁻¹ * psiC F.g0 c x * V := fun x => by
    simp [ψ₁, MulAut.conj_apply]
  have hθfix : ∀ m : ModGL Tag.E7 L, F.n * Φ m * F.n⁻¹ = m → θ (V⁻¹ * m * V) = V⁻¹ * m * V := by
    intro m hm
    have := (mem_twistedFixedPoints_conj (Φ := Φ) (n := F.n) hΦV (x := V⁻¹ * m * V)).2
      (by have e : V * (V⁻¹ * m * V) * V⁻¹ = m := by group
          rw [e]; exact hm)
    rw [hθapp]
    exact this
  have hWσ : (∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
      weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ • α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7)) := hwS
  have hθQeq := map_theta_rootSpan_eq hFrbij hn'm hnw' (fun α hα => hα.1) hwS hwS'
  have hKq' : 2 ≤ Nat.card K := hKq
  have hFr' : ∀ x, Fr x = x ^ Nat.card K := hFr
  have hpq : p ∣ q.card ^ 2 - q.card + 1 := by
    have hqc : q.card = Nat.card K := by
      rw [hK]
      simp [q, TauCeti.PrimePower.card_def]
    rw [hqc]
    have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow two_ne_zero _
    have : ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 +
        (-1 : ℤ) * (Nat.card K : ℤ) + 1 := by
      push_cast [Nat.cast_sub hle]
      ring
    exact Int.natCast_dvd_natCast.1 (by rw [this]; exact hpf)
  refine mem_closure_hyperRSet_of_abstract_a5_n (G := adjointGroup .E7 K) θ hp hp3 hv hpq
    (H := torusGroup Tag.E7 L) (Q := rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)))
    (P := P')
    (fun a ha b hb => torusGroup_comm ha hb)
    (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan (fun α hα => hα.1))
    (fun h hh => by rw [hθapp]; exact theta_mem_torusGroup_of_monomial hFrbij hn'm hh)
    (fun g hg => by
      have : θ g ∈ (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7))).map θ :=
        Subgroup.mem_map_of_mem _ hg
      rw [hθQeq] at this
      exact this)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ρ hρs hρc hρd ?_ ?_ ψ₁ ?_ E hE hEc ?_ hy hy1 ?_ ?_ ?_ hk hkr
  ·
    intro z hz hc g hg
    have hmem : g ∈ (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7))).map θ := by
      rw [hθQeq]; exact hg
    obtain ⟨g', hg', rfl⟩ := hmem
    rw [← map_mul, ← map_mul, hc g' hg']
  ·
    intro s hs
    obtain ⟨t, ht, h⟩ := lang_torus_inf_rootSpan hKq' hFr' hn'm hwS s hs
    exact ⟨t, ht, by rw [hθapp]; exact h⟩
  ·
    intro g hg hθg
    obtain ⟨s, hs, hθs, x, hx, hgx⟩ := exists_split_fixed_Q hFrbij hKq' hFr' hn'm hnw' hwS hwS'
      Φ' hΦ' hg (by rw [← hθapp]; exact hθg)
    exact ⟨s, hs, by rw [hθapp]; exact hθs, x, hx, hgx⟩
  ·
    rintro _ ⟨X, hX, rfl⟩
    rw [← subsystemGroup_eq_rootSpan, ← range_a5Frame]
    exact ⟨X, rfl⟩
  ·
    rintro _ ⟨X, hX, rfl⟩
    rw [hθapp, hΦ' X, (mem_fixSubgroup Φ').1 hX]
  ·
    intro m hm hc
    obtain ⟨hmH, hmC⟩ := hstd'.thetaFree m hm (fun _ u hu => hc u hu)
    exact ⟨hmH, fun g hg => (Subgroup.mem_centralizer_iff.1 hmC g hg).symm⟩
  · exact fun t ht _ => exists_pow_six_eq_mul ht
  · exact fun f hf hc => pow_six_eq_one_of_centralizes hf hc
  · exact fun g hg hθg => pow_six_mem_of_fixed Fr n' Φ' hΦ' hg (by rw [← hθapp]; exact hθg)
  ·
    exact (hstd'.quasi ()).1
  ·
    intro m hm hθm u hu
    rw [← hPeq] at hu ⊢
    refine conj_mem_commutator_of_normalizes (fun γ hγ => ?_) hu
    have hmN : m ∈ Subgroup.normalizer
        (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : Set (ModGL Tag.E7 L)) :=
      sup_le (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan (fun α hα => hα.1))
        Subgroup.le_normalizer hm
    have hmR : m ∈ twistedFixedPoints n' Φ := (hθapp m).symm.trans hθm
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hmN γ).1 hγ.1,
      mul_mem (mul_mem hmR hγ.2) (inv_mem hmR)⟩
  ·
    exact (MulAut.conj V⁻¹).injective.comp (psiC_injective F.g0 c)
  ·
    intro e he
    obtain ⟨hHm, hFix⟩ := mem_twistedTorusOf.1 (hT e he)
    rw [hψ₁]
    exact ⟨hInvH hHm, hθfix _ hFix⟩
  ·
    intro g hg
    have hS : (fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7) ⊆ rootCharKernel b := by
      rw [hSeq]
    have hcent := rootSpan_le_centralizer (K := L) b hS (hVconj' g hg)
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hcent
    rw [hψ₁, ← hbψ]
    calc V⁻¹ * rootDiagUnit .E7 b * V * g
        = V⁻¹ * (rootDiagUnit .E7 b * (V * g * V⁻¹)) * V := by group
      _ = V⁻¹ * ((V * g * V⁻¹) * rootDiagUnit .E7 b) * V := by rw [h1]
      _ = g * (V⁻¹ * rootDiagUnit .E7 b * V) := by group
  ·
    intro k' hk'
    have hkC : k' ∈ Subgroup.centralizer ({y} : Set (adjointGroup .E7 K)) :=
      Subgroup.mem_centralizer_singleton_iff.2 hk'
    have h1 := hψHQ ⟨k', hkC⟩
    have h2 := hψR ⟨k', hkC⟩
    have h3 : ψS ⟨k', hkC⟩ = psiC F.g0 c k' := by rw [hψ, psiC_apply]
    rw [h3, hSeq] at h1
    rw [h3] at h2
    refine ⟨?_, ?_⟩
    · rw [hψ₁]
      have hle : torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L ((fun γ => v • γ) ''
          parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ≤ (torusGroup Tag.E7 L ⊔
          rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7))).comap
          (MulAut.conj V⁻¹).toMonoidHom := by
        refine sup_le (fun t ht => ?_) (fun g hg => ?_)
        · rw [Subgroup.mem_comap]
          have : (MulAut.conj V⁻¹).toMonoidHom t = V⁻¹ * t * V := by
            simp [MulAut.conj_apply]
          rw [this]
          exact Subgroup.mem_sup_left (hInvH ht)
        · rw [Subgroup.mem_comap]
          have : (MulAut.conj V⁻¹).toMonoidHom g = V⁻¹ * g * V := by
            simp [MulAut.conj_apply]
          rw [this]
          exact Subgroup.mem_sup_right (hVconj g hg)
      have := hle h1
      rw [Subgroup.mem_comap] at this
      simpa [MulAut.conj_apply] using this
    · rw [hψ₁]
      exact hθfix _ h2
  ·
    intro u hu
    have hmem : V * u * V⁻¹ ∈ P'.map c₀ := Subgroup.mem_map.2 ⟨u, hu, hcapp u⟩
    obtain ⟨d, hd⟩ := hPψ () hmem
    refine ⟨(d : adjointGroup .E7 K), ?_⟩
    have h3 : ψS d = psiC F.g0 c (d : adjointGroup .E7 K) := by rw [hψ, psiC_apply]
    rw [hψ₁, ← h3, hd]
    group

end A5LineR

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311n

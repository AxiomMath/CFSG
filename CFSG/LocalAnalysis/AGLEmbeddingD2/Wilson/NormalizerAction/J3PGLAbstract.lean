module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerFrame

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup
open scoped commutatorElement

@[expose] def prodSubgroup {G : Type*} [Group G] (M K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (M : Set G)) : Subgroup G where
  carrier := {g | ∃ m ∈ M, ∃ k ∈ K, g = m * k}
  one_mem' := ⟨1, M.one_mem, 1, K.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨m1, hm1, k1, hk1, rfl⟩ ⟨m2, hm2, k2, hk2, rfl⟩
    have hc : k1 * m2 * k1⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hK hk1) m2).mp hm2
    refine ⟨m1 * (k1 * m2 * k1⁻¹), M.mul_mem hm1 hc, k1 * k2, K.mul_mem hk1 hk2, ?_⟩
    group
  inv_mem' := by
    rintro _ ⟨m, hm, k, hk, rfl⟩
    have hc : k⁻¹ * m⁻¹ * k⁻¹⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp (hK (K.inv_mem hk)) m⁻¹).mp (M.inv_mem hm)
    refine ⟨k⁻¹ * m⁻¹ * k, ?_, k⁻¹, K.inv_mem hk, ?_⟩
    · simpa using hc
    · group

@[expose] def IsPGL29 {G : Type*} [Group G] (H I : Subgroup G) : Prop :=
  I ≤ H ∧ Nonempty (↥I ≃* alternatingGroup (Fin 6)) ∧ (I.subgroupOf H).Normal ∧
    (I.subgroupOf H).index = 2 ∧ (∃ x ∈ H, orderOf x = 8) ∧ ∃ j ∈ H, j ∉ I ∧ j ^ 2 = 1

variable {X : Type*} [Group X] [Finite X]

theorem map_conj_eq_of_le {u : X} {K : Subgroup X}
    (h : K.map (MulAut.conj u).toMonoidHom ≤ K) : K.map (MulAut.conj u).toMonoidHom = K := by
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [Subgroup.card_map_of_injective (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective]

theorem mem_map_conj_iff_of_eq {u x : X} {K : Subgroup X} (hK : K.map (MulAut.conj u).toMonoidHom = K) :
    u * x * u⁻¹ ∈ K ↔ x ∈ K := by
  constructor
  · intro hx
    rw [← hK] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have : z = x := by
      have h1 : u * z * u⁻¹ = u * x * u⁻¹ := hzx
      simpa using h1
    rw [← this]; exact hz
  · intro hx
    rw [← hK]
    exact ⟨x, hx, rfl⟩

theorem map_conj_eq_of_mem_normalizer {u : X} {K : Subgroup X}
    (hu : u ∈ Subgroup.normalizer (K : Set X)) : K.map (MulAut.conj u).toMonoidHom = K := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hu z).1 hz
  · intro hx
    refine ⟨u⁻¹ * x * u, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hu) x).1 hx
    simpa using this

theorem map_conj_centralizer {u : X} {D : Subgroup X} (hu : u ∈ Subgroup.normalizer (D : Set X)) :
    (Subgroup.centralizer (D : Set X)).map (MulAut.conj u).toMonoidHom =
      Subgroup.centralizer (D : Set X) := by
  apply map_conj_eq_of_le
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : u⁻¹ * d * u ∈ D := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hu) d).1 hd
    simpa using this
  have hxd := Subgroup.mem_centralizer_iff.1 hx _ hd'
  show d * (u * x * u⁻¹) = u * x * u⁻¹ * d
  calc d * (u * x * u⁻¹) = u * ((u⁻¹ * d * u) * x) * u⁻¹ := by group
    _ = u * (x * (u⁻¹ * d * u)) * u⁻¹ := by rw [hxd]
    _ = u * x * u⁻¹ * d := by group

theorem centralizer_le_normalizer' (D : Subgroup X) :
    Subgroup.centralizer (D : Set X) ≤ Subgroup.normalizer (D : Set X) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro d
  have hc := Subgroup.mem_centralizer_iff.1 hx
  constructor
  · intro hd
    have := hc d hd
    have e : x * d * x⁻¹ = d := by
      calc x * d * x⁻¹ = (x * d) * x⁻¹ := rfl
        _ = (d * x) * x⁻¹ := by rw [this]
        _ = d := by group
    rw [e]; exact hd
  · intro hd
    have hx' := Subgroup.mem_centralizer_iff.1 (inv_mem hx) (x * d * x⁻¹) hd
    have h2 : x⁻¹ * (x * d * x⁻¹) = d * x⁻¹ := by group
    rw [h2] at hx'
    have e : x * d * x⁻¹ = d := mul_right_cancel hx'
    rw [e] at hd
    exact hd

theorem card_normalizer_zpowers_le {q : X} (hq : orderOf q = 3) :
    Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers q : Subgroup X) : Set X)) ≤
      2 * Nat.card ↥(Subgroup.centralizer ({q} : Set X)) := by
  set H : Subgroup X := Subgroup.zpowers q with hH
  set N : Subgroup X := Subgroup.normalizer (H : Set X) with hN
  haveI : IsCyclic H := inferInstance
  have hH3 : Nat.card H = 3 := by rw [hH, Nat.card_zpowers, hq]
  have hAut : Nat.card (MulAut H) = 2 := by
    rw [IsCyclic.card_mulAut, hH3]
    exact Nat.totient_prime Nat.prime_three
  have hker : H.normalizerMonoidHom.ker = (Subgroup.centralizer (H : Set X)).subgroupOf N :=
    Subgroup.normalizerMonoidHom_ker H
  have hcenH : Subgroup.centralizer (H : Set X) = Subgroup.centralizer ({q} : Set X) := by
    ext x
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro h g hg
      exact h g (by rw [Set.mem_singleton_iff] at hg; rw [hg]; exact Subgroup.mem_zpowers q)
    · intro h g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      have := h q rfl
      exact ((Commute.zpow_left (show Commute q x from this) n)).eq
  have hCN : Subgroup.centralizer (H : Set X) ≤ N := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro d
    have hc := Subgroup.mem_centralizer_iff.1 hx
    constructor
    · intro hd
      have e : x * d * x⁻¹ = d := by rw [← hc d hd]; group
      rw [e]; exact hd
    · intro hd
      have hx' := Subgroup.mem_centralizer_iff.1 (inv_mem hx) (x * d * x⁻¹) hd
      have h2 : x⁻¹ * (x * d * x⁻¹) = d * x⁻¹ := by group
      rw [h2] at hx'
      have e : x * d * x⁻¹ = d := mul_right_cancel hx'
      rw [e] at hd
      exact hd
  have hk : Nat.card H.normalizerMonoidHom.ker = Nat.card ↥(Subgroup.centralizer ({q} : Set X)) := by
    rw [hker, hcenH, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hcenH ▸ hCN)).toEquiv]
  have := Subgroup.card_ker_mul_card_range H.normalizerMonoidHom
  have hr : Nat.card H.normalizerMonoidHom.range ≤ 2 := by
    rw [← hAut]; exact Nat.card_le_card_of_injective _ Subtype.val_injective
  calc Nat.card N = Nat.card H.normalizerMonoidHom.ker * Nat.card H.normalizerMonoidHom.range :=
        this.symm
    _ ≤ Nat.card ↥(Subgroup.centralizer ({q} : Set X)) * 2 := by rw [hk]; exact Nat.mul_le_mul_left _ hr
    _ = 2 * Nat.card ↥(Subgroup.centralizer ({q} : Set X)) := by ring

theorem isPGL29_of_normalizing {D I : Subgroup X} {u : X}
    (hIC : I ≤ Subgroup.centralizer (D : Set X)) (hperf : ⁅I, I⁆ = I)
    (hImax : ∀ P : Subgroup X, P ≤ Subgroup.centralizer (D : Set X) → ⁅P, P⁆ = P → P ≤ I)
    (hDI : Disjoint D I) (hCeq : D ⊔ I = Subgroup.centralizer (D : Set X)) (hD9 : Nat.card D = 9)
    (hu8 : orderOf u = 8) (huN : u ∈ Subgroup.normalizer (D : Set X))
    (huC : u ∉ Subgroup.centralizer (D : Set X))
    (hN : Nat.card ↥(Subgroup.normalizer (D : Set X)) ≤
      2 * Nat.card ↥(Subgroup.centralizer (D : Set X)))
    (eI : ↥I ≃* alternatingGroup (Fin 6))
    (hτ : ∃ τ ∈ Subgroup.normalizer (D : Set X), τ ∉ Subgroup.centralizer (D : Set X) ∧
      τ ^ 2 = 1) :
    IsPGL29 (I ⊔ Subgroup.zpowers u) I := by
  set C : Subgroup X := Subgroup.centralizer (D : Set X) with hC
  set N : Subgroup X := Subgroup.normalizer (D : Set X) with hNdef
  have hCN : C ≤ N := centralizer_le_normalizer' D
  have hcomm : ∀ x ∈ C, ∀ d ∈ D, x * d = d * x := fun x hx d hd =>
    (Subgroup.mem_centralizer_iff.1 hx d hd).symm
  have hIu : I.map (MulAut.conj u).toMonoidHom = I := by
    apply map_conj_eq_of_le
    apply hImax
    · calc I.map (MulAut.conj u).toMonoidHom ≤ C.map (MulAut.conj u).toMonoidHom :=
            Subgroup.map_mono hIC
        _ = C := map_conj_centralizer huN
    · rw [← Subgroup.map_commutator, hperf]
  have huI : u ∉ I := fun h => huC (hIC h)
  have hdvd : Nat.card C ∣ Nat.card N := Subgroup.card_dvd_of_le hCN
  have hne : Nat.card N ≠ Nat.card C := by
    intro h
    have heq : C = N := Subgroup.eq_of_le_of_card_ge hCN (by rw [h])
    exact huC (heq ▸ huN)
  obtain ⟨m, hm⟩ := hdvd
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hm2 : m = 2 := by
    have hNpos : 0 < Nat.card N := Nat.card_pos
    have hle2 : Nat.card C * m ≤ 2 * Nat.card C := hm ▸ hN
    have hm_le : m ≤ 2 := by nlinarith
    have hm_ne0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      omega
    have hm_ne1 : m ≠ 1 := by
      rintro rfl
      rw [mul_one] at hm
      exact hne hm
    omega
  have hidx : (C.subgroupOf N).index = 2 := by
    have h1 := Subgroup.card_mul_index (C.subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv, hm, hm2] at h1
    exact Nat.eq_of_mul_eq_mul_left hCpos h1
  have hmulC : ∀ a b : X, a ∈ N → b ∈ N → a ∉ C → b ∉ C → a * b ∈ C := by
    intro a b ha hb haC hbC
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).2
      (iff_of_false (fun h => haC (Subgroup.mem_subgroupOf.1 h))
        (fun h => hbC (Subgroup.mem_subgroupOf.1 h)))
    exact Subgroup.mem_subgroupOf.1 this
  have hu2C : u * u ∈ C := by
    have := Subgroup.mul_self_mem_of_index_two hidx (⟨u, huN⟩ : N)
    exact Subgroup.mem_subgroupOf.1 this
  have hu2I : u * u ∈ I := by
    obtain ⟨d, hd, i, hi, hdi⟩ := (mem_sup_of_commute (H := D) (K := I)
      (fun x hx y hy => (hcomm y (hIC hy) x hx).symm)).1 (hCeq ▸ hu2C)
    have hcm : Commute d i := (hcomm i (hIC hi) d hd).symm
    have h4 : (u * u) ^ 4 = 1 := by
      have : (u * u) ^ 4 = u ^ 8 := by rw [← pow_two, ← pow_mul]
      rw [this]; exact hu8 ▸ pow_orderOf_eq_one u
    rw [← hdi, hcm.mul_pow] at h4
    have hd4 : d ^ 4 = 1 := by
      have hd4D : d ^ 4 ∈ D := Subgroup.pow_mem _ hd 4
      have hd4I : d ^ 4 ∈ I := by
        have : d ^ 4 = (i ^ 4)⁻¹ := eq_inv_of_mul_eq_one_left h4
        rw [this]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hi 4)
      exact Subgroup.disjoint_def.1 hDI hd4D hd4I
    have hd9 : d ^ 9 = 1 := by
      have := pow_card_eq_one' (x := (⟨d, hd⟩ : D))
      rw [hD9] at this
      exact congrArg Subtype.val this
    have hdo : orderOf d ∣ 1 := by
      have h1 := orderOf_dvd_of_pow_eq_one hd4
      have h2 := orderOf_dvd_of_pow_eq_one hd9
      have := Nat.dvd_gcd h1 h2
      simpa using this
    have hd1 : d = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdo)
    rw [← hdi, hd1, one_mul]; exact hi
  have huNI : u ∈ Subgroup.normalizer (I : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact (mem_map_conj_iff_of_eq hIu).symm
  have hHle : I ⊔ Subgroup.zpowers u ≤ Subgroup.normalizer (I : Set X) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 huNI)
  refine ⟨le_sup_left, ⟨eI⟩, (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHle,
    ?_, ⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u), hu8⟩, ?_⟩
  ·
    show I.relIndex (I ⊔ Subgroup.zpowers u) = 2
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u), huI, ?_⟩
    intro b hb
    have hK : Subgroup.zpowers u ≤ Subgroup.normalizer (I : Set X) :=
      Subgroup.zpowers_le.2 huNI
    have hle : I ⊔ Subgroup.zpowers u ≤ prodSubgroup I (Subgroup.zpowers u) hK :=
      sup_le (fun m hm => ⟨m, hm, 1, Subgroup.one_mem _, by simp⟩)
        (fun k hk => ⟨1, Subgroup.one_mem _, k, hk, by simp⟩)
    obtain ⟨i, hi, k, hk, rfl⟩ := hle hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hsq : ∀ q : ℤ, u ^ (2 * q) ∈ I := by
      intro q
      have : u ^ (2 * q) = (u * u) ^ q := by rw [zpow_mul, zpow_two]
      rw [this]
      exact Subgroup.zpow_mem _ hu2I q
    obtain ⟨q, hq | hq⟩ := Int.even_or_odd' n
    · right
      rw [hq]
      exact Subgroup.mul_mem _ hi (hsq q)
    · left
      have h2 : u ^ (2 * (q + 1)) = u ^ (2 * q + 1) * u := by
        rw [← zpow_add_one]
        congr 1
        ring
      have : i * u ^ n * u = i * u ^ (2 * (q + 1)) := by
        rw [h2, hq, mul_assoc]
      rw [this]
      exact Subgroup.mul_mem _ hi (hsq (q + 1))
  · obtain ⟨τ, hτN, hτC, hτ2⟩ := hτ
    have hu'C : u⁻¹ ∉ C := fun h => huC (by simpa using Subgroup.inv_mem _ h)
    have hu'N : u⁻¹ ∈ N := Subgroup.inv_mem _ huN
    have h1 : u⁻¹ * τ ∈ C := hmulC _ _ hu'N hτN hu'C hτC
    obtain ⟨d, hd, i, hi, hdi⟩ := (mem_sup_of_commute (H := D) (K := I)
      (fun x hx y hy => (hcomm y (hIC hy) x hx).symm)).1 (hCeq ▸ h1)
    have hd' : u * d * u⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 huN d).1 hd
    have hτeq : τ = (u * d * u⁻¹) * (u * i) := by
      have : τ = u * (u⁻¹ * τ) := by group
      rw [this, ← hdi]; group
    have hiN : u * i ∈ N := Subgroup.mul_mem _ huN (hCN (hIC hi))
    have hH : u * i ∈ I ⊔ Subgroup.zpowers u :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
        (Subgroup.mem_sup_left hi)
    refine ⟨u * i, hH, ?_, ?_⟩
    · intro h
      apply huI
      have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ hi)
      simpa using this
    · have hsqI : (u * i) * (u * i) ∈ I := by
        have h2 : (u * i) * (u * i) = (u * i * u⁻¹) * (u * u) * i := by group
        rw [h2]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ((mem_map_conj_iff_of_eq hIu).2 hi) hu2I) hi
      have hsqD : (u * i) * (u * i) ∈ D := by
        have hconj : (u * i) * (u * d * u⁻¹) * (u * i)⁻¹ ∈ D :=
          (Subgroup.mem_normalizer_iff.1 hiN _).1 hd'
        have e : (u * i) * (u * i) = ((u * d * u⁻¹) * ((u * i) * (u * d * u⁻¹) * (u * i)⁻¹))⁻¹ := by
          have h0 : τ * τ = 1 := by rw [← pow_two]; exact hτ2
          rw [hτeq] at h0
          set dd := u * d * u⁻¹
          set hh := u * i
          have : hh * hh = (dd * (hh * dd * hh⁻¹))⁻¹ := by
            apply eq_inv_of_mul_eq_one_right
            calc dd * (hh * dd * hh⁻¹) * (hh * hh) = (dd * hh) * (dd * hh) := by group
              _ = 1 := h0
          exact this
        rw [e]
        exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hd' hconj)
      have : (u * i) * (u * i) = 1 := Subgroup.disjoint_def.1 hDI hsqD hsqI
      rw [pow_two]; exact this

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

module

public import CFSG.HardMathSupport.Foote.E27.Defs

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

theorem dvd81_card_inf_centralizer_of_cover {G : Type*} [Group G] [Finite G] (T R A : Subgroup G)
    (x : G) (hx : orderOf x = 3) (hRT : R ≤ T) (hAT : A ≤ T) (hR : Nat.card R = 243)
    (hRcomm : ⁅R, R⁆ ≤ zpowers x) (hxR : ∀ r ∈ R, x * r = r * x) (hA : Nat.card A = 81)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcover : ∀ y ∈ T, orderOf y = 3 → y ∈ R ∨ y ∈ A) {s : G} (hs : s ∈ T) (hs3 : orderOf s = 3) :
    81 ∣ Nat.card ↥(T ⊓ centralizer ({s} : Set G)) := by
  rcases hcover s hs hs3 with hsR | hsA
  ·
    have hcm : ∀ r ∈ R, s * r * s⁻¹ * r⁻¹ ∈ zpowers x := fun r hr =>
      hRcomm (Subgroup.commutator_mem_commutator hsR hr)
    have hxz : ∀ r ∈ R, ∀ k : ℤ, x ^ k * r = r * x ^ k := fun r hr k =>
      ((Commute.zpow_left (hxR r hr) k : Commute (x ^ k) r)).eq
    have hcz : ∀ r ∈ R, ∀ c ∈ zpowers x, c * r = r * c := fun r hr c hc => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
      exact hxz r hr k
    let φ : ↥R →* ↥(zpowers x) :=
      { toFun := fun r => ⟨s * r * s⁻¹ * (r : G)⁻¹, hcm r r.2⟩
        map_one' := by ext; simp
        map_mul' := by
          intro a b
          ext
          have hb := hcz a a.2 (s * b * s⁻¹ * (b : G)⁻¹) (hcm b b.2)
          change s * ((a : G) * b) * s⁻¹ * ((a : G) * b)⁻¹ =
            (s * a * s⁻¹ * (a : G)⁻¹) * (s * b * s⁻¹ * (b : G)⁻¹)
          calc s * ((a : G) * b) * s⁻¹ * ((a : G) * b)⁻¹
              = (s * a * s⁻¹ * (a : G)⁻¹) * ((a : G) * (s * b * s⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by
                group
            _ = (s * a * s⁻¹ * (a : G)⁻¹) * (s * b * s⁻¹ * (b : G)⁻¹) := by
                rw [← hb]; group }
    have hker : ∀ r : ↥R, r ∈ φ.ker → s * (r : G) = r * s := by
      intro r hr
      have h1 : s * (r : G) * s⁻¹ * (r : G)⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hr)
      calc s * (r : G) = (s * r * s⁻¹ * (r : G)⁻¹) * ((r : G) * s) := by group
        _ = r * s := by rw [h1, one_mul]
    have hmul := φ.ker.card_mul_index
    have hidx : φ.ker.index ∣ 3 := by
      rw [Subgroup.index_ker]
      have := Subgroup.card_subgroup_dvd_card φ.range
      rwa [Nat.card_zpowers, hx] at this
    have hcase : φ.ker.index = 1 ∨ φ.ker.index = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hidx with h | h <;> simp [h]
    have h81 : 81 ∣ Nat.card φ.ker := by
      rcases hcase with h | h
      · rw [h, mul_one, hR] at hmul; rw [hmul]; norm_num
      · rw [h, hR] at hmul; omega
    have hle : φ.ker.map R.subtype ≤ T ⊓ centralizer ({s} : Set G) := by
      rintro _ ⟨r, hr, rfl⟩
      exact ⟨hRT r.2, mem_centralizer_singleton_iff.mpr (hker r hr).symm⟩
    have hcard : Nat.card (φ.ker.map R.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective R.subtype_injective
    exact h81.trans (hcard ▸ Subgroup.card_dvd_of_le hle)
  · have hle : A ≤ T ⊓ centralizer ({s} : Set G) := by
      intro a ha
      exact ⟨hAT ha, mem_centralizer_singleton_iff.mpr (hAc a ha s hsA)⟩
    exact hA ▸ Subgroup.card_dvd_of_le hle

theorem dvd81_card_inf_centralizer_of_threeLocal {G : Type*} [Group G] [Finite G]
    (T R A : Subgroup G) (x : G) (hx : orderOf x = 3) (hRT : R ≤ T) (hAT : A ≤ T)
    (hR : Nat.card R = 243) (hcomm : ⁅R, R⁆ = zpowers x)
    (hcenter : R ⊓ centralizer (R : Set G) = zpowers x) (hA : Nat.card A = 81)
    [IsMulCommutative ↥A] (hcover : ∀ y ∈ T, orderOf y = 3 → y ∈ R ∨ y ∈ A) {s : G}
    (hs : s ∈ T) (hs3 : orderOf s = 3) : 81 ∣ Nat.card ↥(T ⊓ centralizer ({s} : Set G)) := by
  refine dvd81_card_inf_centralizer_of_cover T R A x hx hRT hAT hR (le_of_eq hcomm) ?_ hA ?_
    hcover hs hs3
  · intro r hr
    have : x ∈ R ⊓ centralizer (R : Set G) := by
      rw [hcenter]; exact mem_zpowers x
    exact ((mem_centralizer_iff.mp this.2) r hr).symm
  · intro a ha b hb
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem commutator_closure_pair_eq_self {M : Type*} [Group M] (a b : M) (ha : a ^ 2 = 1)
    (hb : b ^ 3 = 1) (hab : (a * b) ^ 5 = 1) :
    ⁅closure {a, b}, closure {a, b}⁆ = closure {a, b} := by
  set D : Subgroup M := closure {a, b} with hD
  have haD : a ∈ D := subset_closure (Set.mem_insert _ _)
  have hbD : b ∈ D := subset_closure (Set.mem_insert_of_mem _ rfl)
  let f : ↥D →* Abelianization ↥D := Abelianization.of
  let a' : ↥D := ⟨a, haD⟩
  let b' : ↥D := ⟨b, hbD⟩
  have h1 : f a' = 1 ∧ f b' = 1 := by
    have h2 : (f a') ^ 2 = 1 := by
      rw [← map_pow]; exact (congrArg f (Subtype.ext (by simpa using ha))).trans (map_one f)
    have h3 : (f b') ^ 3 = 1 := by
      rw [← map_pow]; exact (congrArg f (Subtype.ext (by simpa using hb))).trans (map_one f)
    have h4 : (f a' * f b') ^ 5 = 1 := by
      rw [← map_mul, ← map_pow]
      exact (congrArg f (Subtype.ext (by simpa using hab))).trans (map_one f)
    rw [mul_pow] at h4
    have h5 : f a' ^ 5 = f a' := by
      calc f a' ^ 5 = (f a' ^ 2) ^ 2 * f a' := by group
        _ = f a' := by rw [h2]; simp
    have h6 : f b' ^ 5 = f b' ^ 2 := by
      calc f b' ^ 5 = f b' ^ 3 * f b' ^ 2 := by group
        _ = f b' ^ 2 := by rw [h3]; simp
    rw [h5, h6] at h4
    have h7 : f a' = f b' := by
      have : f a' = (f b' ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h4
      rw [this]
      calc (f b' ^ 2)⁻¹ = f b' ^ 3 * (f b' ^ 2)⁻¹ := by rw [h3, one_mul]
        _ = f b' := by group
    have h8 : f b' = 1 := by
      have : f b' ^ 2 = 1 := by rw [← h7]; exact h2
      calc f b' = f b' ^ 3 * (f b' ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, this]; simp
    exact ⟨h7.trans h8, h8⟩
  have hker : (⊤ : Subgroup ↥D) ≤ f.ker := by
    have hgen := Subgroup.closure_closure_coe_preimage (k := ({a, b} : Set M))
    rw [← hgen, closure_le]
    intro x hx
    rcases hx with hx | hx
    · have : x = a' := Subtype.ext hx
      rw [this]; exact h1.1
    · have : x = b' := Subtype.ext (Set.mem_singleton_iff.mp hx)
      rw [this]; exact h1.2
  have hcomm : commutator ↥D = ⊤ := by
    rw [eq_top_iff]
    intro x hx
    have := hker hx
    rwa [Abelianization.ker_of] at this
  have hmap : (⊤ : Subgroup ↥D).map D.subtype = D := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  calc ⁅D, D⁆ = ⁅(⊤ : Subgroup ↥D).map D.subtype, (⊤ : Subgroup ↥D).map D.subtype⁆ := by
        rw [hmap]
    _ = (⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆).map D.subtype :=
        (Subgroup.map_commutator _ _ _).symm
    _ = D := by
      change (_root_.commutator ↥D).map D.subtype = D
      rw [hcomm, hmap]

theorem exists_perfect_of_pair {M : Type*} [Group M] (P x a b : M) (hax : a * x = x * a)
    (hbx : b * x = x * b) (ha : a ^ 2 = 1) (hb : b ^ 3 = 1) (hab : (a * b) ^ 5 = 1) (hb1 : b ≠ 1) :
    ∃ D : Subgroup M, D ≤ centralizer ({P * x * P⁻¹} : Set M) ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D ∧
      (∀ J : Subgroup M, P ∈ J → a ∈ J → b ∈ J → D ≤ J) := by
  have ha' : (P * a * P⁻¹) ^ 2 = 1 := by simp only [conj_pow, ha]; group
  have hb' : (P * b * P⁻¹) ^ 3 = 1 := by simp only [conj_pow, hb]; group
  have hab' : (P * a * P⁻¹ * (P * b * P⁻¹)) ^ 5 = 1 := by
    have : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by group
    rw [this, conj_pow, hab]; group
  refine ⟨closure {P * a * P⁻¹, P * b * P⁻¹}, ?_, commutator_closure_pair_eq_self _ _ ha' hb' hab',
    ?_, ?_⟩
  · rw [closure_le]
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      calc P * a * P⁻¹ * (P * x * P⁻¹) = P * (a * x) * P⁻¹ := by group
        _ = P * (x * a) * P⁻¹ := by rw [hax]
        _ = P * x * P⁻¹ * (P * a * P⁻¹) := by group
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      calc P * b * P⁻¹ * (P * x * P⁻¹) = P * (b * x) * P⁻¹ := by group
        _ = P * (x * b) * P⁻¹ := by rw [hbx]
        _ = P * x * P⁻¹ * (P * b * P⁻¹) := by group
  · have hb'1 : P * b * P⁻¹ ≠ 1 := by
      intro e'
      apply hb1
      have : P * b * P⁻¹ = P * 1 * P⁻¹ := by simpa using e'
      simpa using this
    have hord : orderOf (P * b * P⁻¹) = 3 := orderOf_eq_prime hb' hb'1
    have hmemD : P * b * P⁻¹ ∈ closure ({P * a * P⁻¹, P * b * P⁻¹} : Set M) :=
      subset_closure (Set.mem_insert_of_mem _ rfl)
    have := orderOf_dvd_natCard
      (⟨P * b * P⁻¹, hmemD⟩ : closure ({P * a * P⁻¹, P * b * P⁻¹} : Set M))
    rwa [Subgroup.orderOf_mk _ hmemD, hord] at this
  · intro J hP ha hb
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact J.mul_mem (J.mul_mem hP ha) (J.inv_mem hP)
    · exact J.mul_mem (J.mul_mem hP hb) (J.inv_mem hP)

theorem exists_equiv_map_sylow {G H : Type*} [Group G] [Group H] [Finite H]
    (e : G ≃* H) (T : Subgroup H) (hT : Nat.card T = 3 ^ (Nat.card H).factorization 3)
    (S₀ : Sylow 3 G) {z : G} (hz : z ∈ (S₀ : Subgroup G)) :
    ∃ ψ : H ≃* G, T.map ψ.toMonoidHom = (S₀ : Subgroup G) ∧ ∃ w ∈ T, ψ w = z := by
  have : Finite G := Finite.of_equiv H e.symm.toEquiv
  let T' : Subgroup G := T.comap e.toMonoidHom
  have hcardGH : Nat.card G = Nat.card H := Nat.card_congr e.toEquiv
  have hT' : Nat.card T' = 3 ^ (Nat.card G).factorization 3 := by
    rw [hcardGH, ← hT]
    exact Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => Iff.rfl)
  let P : Sylow 3 G := Sylow.ofCard T' hT'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S₀
  have hmemS : ∀ v : G, v ∈ (S₀ : Subgroup G) ↔ g⁻¹ * v * g ∈ T' := by
    intro v
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    exact Iff.rfl
  let ψ : H ≃* G := e.symm.trans (MulAut.conj g)
  have hψ : ∀ y : H, ψ y = g * e.symm y * g⁻¹ := fun y => rfl
  have hψS : ∀ y : H, ψ y ∈ (S₀ : Subgroup G) ↔ y ∈ T := by
    intro y
    rw [hmemS, hψ]
    have : g⁻¹ * (g * e.symm y * g⁻¹) * g = e.symm y := by group
    rw [this]
    show e (e.symm y) ∈ T ↔ y ∈ T
    rw [MulEquiv.apply_symm_apply]
  refine ⟨ψ, ?_, e (g⁻¹ * z * g), (hmemS z).mp hz, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hψS y).mpr hy
    · intro hx
      refine ⟨ψ.symm x, ?_, by simp⟩
      exact (hψS (ψ.symm x)).mp (by simpa using hx)
  · rw [hψ, MulEquiv.symm_apply_apply]; group

theorem dvd81_card_sylow_inf_centralizer_of_equiv {G H : Type*} [Group G] [Group H] [Finite H]
    (e : G ≃* H) (T : Subgroup H) (hT : Nat.card T = 3 ^ (Nat.card H).factorization 3)
    (hprop : ∀ s ∈ T, orderOf s = 3 → 81 ∣ Nat.card ↥(T ⊓ centralizer ({s} : Set H)))
    (S₀ : Sylow 3 G) {z : G} (hz : z ∈ (S₀ : Subgroup G)) (hz3 : orderOf z = 3) :
    81 ∣ Nat.card ↥((S₀ : Subgroup G) ⊓ centralizer ({z} : Set G)) := by
  obtain ⟨ψ, hψT, w, hwT, hwz⟩ := exists_equiv_map_sylow e T hT S₀ hz
  have hw3 : orderOf w = 3 := by rw [← hz3, ← hwz, MulEquiv.orderOf_eq]
  have hbound := hprop w hwT hw3
  have hequiv : ↥(T ⊓ centralizer ({w} : Set H)) ≃
      ↥((S₀ : Subgroup G) ⊓ centralizer ({z} : Set G)) :=
    Equiv.subtypeEquiv ψ.toEquiv (fun y => by
      simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff]
      refine and_congr ?_ ?_
      · rw [← hψT]
        exact ⟨fun h => ⟨y, h, rfl⟩, fun ⟨x, hx, hxy⟩ => (ψ.injective hxy) ▸ hx⟩
      · rw [← hwz]
        constructor
        · intro h
          have := congrArg ψ h
          simpa [map_mul] using this
        · intro h
          apply ψ.injective
          simpa [map_mul] using h)
  rw [← Nat.card_congr hequiv]
  exact hbound

theorem exists_perfect_of_equiv {G H : Type*} [Group G] [Group H] (ψ : H ≃* G) {w : H} {z : G}
    (hwz : ψ w = z) {D : Subgroup H} (hD : D ≤ centralizer ({w} : Set H)) (hDp : ⁅D, D⁆ = D)
    (h3 : 3 ∣ Nat.card D) :
    ∃ D' : Subgroup G, D' ≤ centralizer ({z} : Set G) ∧ ⁅D', D'⁆ = D' ∧ 3 ∣ Nat.card D' := by
  refine ⟨D.map ψ.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hwz]
    have := mem_centralizer_singleton_iff.mp (hD hd)
    simpa [← map_mul] using congrArg ψ this
  · rw [← Subgroup.map_commutator, hDp]
  · rw [Subgroup.card_map_of_injective ψ.injective]
    exact h3

theorem sylow_kill_of_equiv {G H : Type*} [Group G] [Group H] [Finite H]
    (e : G ≃* H) (T : Subgroup H) (hT : Nat.card T = 3 ^ (Nat.card H).factorization 3)
    (hprop : ∀ w ∈ T, orderOf w = 3 → 81 ∣ Nat.card ↥(T ⊓ centralizer ({w} : Set H)) ∨
      ∃ D : Subgroup H, D ≤ centralizer ({w} : Set H) ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D)
    (S₀ : Sylow 3 G) {z : G} (hz : z ∈ (S₀ : Subgroup G)) (hz3 : orderOf z = 3) :
    81 ∣ Nat.card ↥((S₀ : Subgroup G) ⊓ centralizer ({z} : Set G)) ∨
      ∃ D : Subgroup G, D ≤ centralizer ({z} : Set G) ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  obtain ⟨ψ, hψT, w, hwT, hwz⟩ := exists_equiv_map_sylow e T hT S₀ hz
  have hw3 : orderOf w = 3 := by rw [← hz3, ← hwz, MulEquiv.orderOf_eq]
  rcases hprop w hwT hw3 with h1 | ⟨D, hD, hDp, hD3⟩
  · left
    have hequiv : ↥(T ⊓ centralizer ({w} : Set H)) ≃
        ↥((S₀ : Subgroup G) ⊓ centralizer ({z} : Set G)) :=
      Equiv.subtypeEquiv ψ.toEquiv (fun y => by
        simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff]
        refine and_congr ?_ ?_
        · rw [← hψT]
          exact ⟨fun h => ⟨y, h, rfl⟩, fun ⟨x, hx, hxy⟩ => (ψ.injective hxy) ▸ hx⟩
        · rw [← hwz]
          constructor
          · intro h
            have := congrArg ψ h
            simpa [map_mul] using this
          · intro h
            apply ψ.injective
            simpa [map_mul] using h)
    rw [← Nat.card_congr hequiv]
    exact h1
  · right
    exact exists_perfect_of_equiv ψ hwz hD hDp hD3

theorem card_inf_centralizer_subgroupOf {W : Type*} [Group W] (J T : Subgroup W) (hTJ : T ≤ J)
    (w : ↥J) :
    Nat.card ↥(T.subgroupOf J ⊓ centralizer ({w} : Set ↥J)) =
      Nat.card ↥(T ⊓ centralizer ({(w : W)} : Set W)) := by
  refine Nat.card_congr ⟨fun x => ⟨(x.1 : W), ?_, ?_⟩, fun y => ⟨⟨y.1, hTJ ?_⟩, ?_, ?_⟩,
    fun x => rfl, fun y => rfl⟩
  · exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp x.2).1
  · have := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
    exact mem_centralizer_singleton_iff.mpr (by simpa using congrArg Subtype.val this)
  · exact (Subgroup.mem_inf.mp y.2).1
  · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp y.2).1
  · have := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).2
    exact mem_centralizer_singleton_iff.mpr (Subtype.ext (by simpa using this))

theorem sylow_kill_of_equiv_ambient {G W : Type*} [Group G] [Group W] (J : Subgroup W) [Finite J]
    (e : G ≃* ↥J) (T : Subgroup W) (hTJ : T ≤ J)
    (hT : Nat.card T = 3 ^ (Nat.card J).factorization 3)
    (hprop : ∀ s ∈ T, s ^ 3 = 1 → s ≠ 1 →
      81 ∣ Nat.card ↥(T ⊓ centralizer ({s} : Set W)) ∨
        ∃ D : Subgroup W, D ≤ centralizer ({s} : Set W) ∧ D ≤ J ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D)
    (S₀ : Sylow 3 G) {z : G} (hz : z ∈ (S₀ : Subgroup G)) (hz3 : orderOf z = 3) :
    81 ∣ Nat.card ↥((S₀ : Subgroup G) ⊓ centralizer ({z} : Set G)) ∨
      ∃ D : Subgroup G, D ≤ centralizer ({z} : Set G) ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  refine sylow_kill_of_equiv e (T.subgroupOf J) ?_ ?_ S₀ hz hz3
  · rw [← hT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv
  · intro w hwT hw3
    have hw1 : (w : W) ≠ 1 := fun h1 => by
      have : w = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hw3; omega
    have hw3' : (w : W) ^ 3 = 1 := by
      have : w ^ 3 = 1 := by rw [← hw3]; exact pow_orderOf_eq_one w
      simpa using congrArg Subtype.val this
    rcases hprop (w : W) (Subgroup.mem_subgroupOf.mp hwT) hw3' hw1 with
      h1 | ⟨D, hD, hDJ, hDp, hD3⟩
    · left
      rw [card_inf_centralizer_subgroupOf J T hTJ w]
      exact h1
    · right
      refine ⟨D.subgroupOf J, ?_, ?_, ?_⟩
      · intro x hx
        have h1 := mem_centralizer_singleton_iff.mp (hD (Subgroup.mem_subgroupOf.mp hx))
        exact mem_centralizer_singleton_iff.mpr (Subtype.ext (by simpa using h1))
      · apply Subgroup.map_injective J.subtype_injective
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hDJ, hDp]
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDJ).toEquiv]
        exact hD3

end CFSG.HardMathSupport.Foote.E27

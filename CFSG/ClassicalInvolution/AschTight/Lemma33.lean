module

public import CFSG.LocalAnalysis.ZStar
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.ClassicalInvolution.TwoGroupCase.SylowOf

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution

variable {G : Type} [Group G]

def conjByMembers (K : Subgroup G) (t : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (K : Set G) ∧ ∃ k ∈ K, g * t * g⁻¹ = k * t * k⁻¹}
  mul_mem' := by
    rintro g h ⟨hg, k, hk, hgk⟩ ⟨hh, k', hk', hhk⟩
    refine ⟨Subgroup.mul_mem _ hg hh, g * k' * g⁻¹ * k,
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hg k').mp hk') hk, ?_⟩
    calc g * h * t * (g * h)⁻¹ = g * (h * t * h⁻¹) * g⁻¹ := by group
      _ = g * (k' * t * k'⁻¹) * g⁻¹ := by rw [hhk]
      _ = (g * k' * g⁻¹) * (g * t * g⁻¹) * (g * k' * g⁻¹)⁻¹ := by group
      _ = (g * k' * g⁻¹) * (k * t * k⁻¹) * (g * k' * g⁻¹)⁻¹ := by rw [hgk]
      _ = g * k' * g⁻¹ * k * t * (g * k' * g⁻¹ * k)⁻¹ := by group
  one_mem' := ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, by group⟩
  inv_mem' := by
    rintro g ⟨hg, k, hk, hgk⟩
    have hg' : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hg
    have ha : g⁻¹ * k * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp hg' k).mp hk
      simpa using this
    refine ⟨hg', (g⁻¹ * k * g)⁻¹, Subgroup.inv_mem _ ha, ?_⟩
    have ht : g⁻¹ * (k * t * k⁻¹) * g = t := by rw [← hgk]; group
    calc g⁻¹ * t * g⁻¹⁻¹
        = (g⁻¹ * k * g)⁻¹ * (g⁻¹ * (k * t * k⁻¹) * g) * (g⁻¹ * k * g) := by group
      _ = (g⁻¹ * k * g)⁻¹ * t * (g⁻¹ * k * g)⁻¹⁻¹ := by rw [ht]; group

theorem exists_conj_eq_of_mem_sup {K : Subgroup G} {t : G}
    (htN : t ∈ Subgroup.normalizer (K : Set G)) {g : G} (hg : g ∈ K ⊔ Subgroup.zpowers t) :
    ∃ k ∈ K, g * t * g⁻¹ = k * t * k⁻¹ := by
  have hle : K ⊔ Subgroup.zpowers t ≤ conjByMembers K t := by
    refine sup_le (fun k hk => ⟨Subgroup.le_normalizer hk, k, hk, rfl⟩) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨htN, 1, Subgroup.one_mem _, by group⟩
  exact (hle hg).2

theorem mul_comm_of_mem_zpowers {K : Subgroup G} {z : G} (hz : ∀ k ∈ K, k * z = z * k)
    {k y : G} (hk : k ∈ K) (hy : y ∈ Subgroup.zpowers z) : k * y = y * k := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_right (hz k hk : Commute k z) n).eq

theorem mul_comm_of_mem_zpowers_zpowers {z a b : G} (ha : a ∈ Subgroup.zpowers z)
    (hb : b ∈ Subgroup.zpowers z) : a * b = b * a := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow_self z m n).eq

theorem commutator_mul {t k k' : G}
    (hk' : k * (k' * t * k'⁻¹ * t⁻¹) = (k' * t * k'⁻¹ * t⁻¹) * k) :
    k * k' * t * (k * k')⁻¹ * t⁻¹ = (k' * t * k'⁻¹ * t⁻¹) * (k * t * k⁻¹ * t⁻¹) := by
  calc k * k' * t * (k * k')⁻¹ * t⁻¹ = (k * (k' * t * k'⁻¹ * t⁻¹)) * t * k⁻¹ * t⁻¹ := by group
    _ = ((k' * t * k'⁻¹ * t⁻¹) * k) * t * k⁻¹ * t⁻¹ := by rw [hk']
    _ = (k' * t * k'⁻¹ * t⁻¹) * (k * t * k⁻¹ * t⁻¹) := by group

theorem commutator_inv {t k : G}
    (hk : k⁻¹ * (k * t * k⁻¹ * t⁻¹)⁻¹ = (k * t * k⁻¹ * t⁻¹)⁻¹ * k⁻¹) :
    k⁻¹ * t * k⁻¹⁻¹ * t⁻¹ = (k * t * k⁻¹ * t⁻¹)⁻¹ := by
  calc k⁻¹ * t * k⁻¹⁻¹ * t⁻¹ = (k⁻¹ * (k * t * k⁻¹ * t⁻¹)⁻¹) * k := by group
    _ = ((k * t * k⁻¹ * t⁻¹)⁻¹ * k⁻¹) * k := by rw [hk]
    _ = (k * t * k⁻¹ * t⁻¹)⁻¹ := by group

def twistedCentralizer (K : Subgroup G) (t z : G) (hz : ∀ k ∈ K, k * z = z * k) :
    Subgroup G where
  carrier := {k | k ∈ K ∧ k * t * k⁻¹ * t⁻¹ ∈ Subgroup.zpowers z}
  mul_mem' := by
    rintro k k' ⟨hk, hkz⟩ ⟨hk', hk'z⟩
    refine ⟨Subgroup.mul_mem _ hk hk', ?_⟩
    rw [commutator_mul (mul_comm_of_mem_zpowers hz hk hk'z)]
    exact Subgroup.mul_mem _ hk'z hkz
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  inv_mem' := by
    rintro k ⟨hk, hkz⟩
    refine ⟨Subgroup.inv_mem _ hk, ?_⟩
    rw [commutator_inv (mul_comm_of_mem_zpowers hz (Subgroup.inv_mem _ hk)
      (Subgroup.inv_mem _ hkz))]
    exact Subgroup.inv_mem _ hkz

def delta (K : Subgroup G) (t z : G) (hz : ∀ k ∈ K, k * z = z * k) :
    twistedCentralizer K t z hz →* Subgroup.zpowers z where
  toFun k := ⟨(k : G) * t * (k : G)⁻¹ * t⁻¹, k.2.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' k k' := by
    apply Subtype.ext
    change (k : G) * k' * t * ((k : G) * k')⁻¹ * t⁻¹ =
      ((k : G) * t * (k : G)⁻¹ * t⁻¹) * ((k' : G) * t * (k' : G)⁻¹ * t⁻¹)
    rw [commutator_mul (mul_comm_of_mem_zpowers hz k.2.1 k'.2.2)]
    exact mul_comm_of_mem_zpowers_zpowers k'.2.2 k.2.2

theorem commutator_eq_one_of_mem_zpowers [Finite G] {K R : Subgroup G} {t z : G}
    (hz : ∀ k ∈ K, k * z = z * k) (hz2 : orderOf z = 2) (hR : IsSylow2Of R K)
    (htR : ∀ r ∈ R, r * t = t * r) {k : G} (hk : k ∈ K)
    (hkt : k * t * k⁻¹ * t⁻¹ ∈ Subgroup.zpowers z) : k * t * k⁻¹ * t⁻¹ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  set C := twistedCentralizer K t z hz with hCdef
  have hCK : C ≤ K := fun x hx => hx.1
  have hRtriv : ∀ r ∈ R, r * t * r⁻¹ * t⁻¹ = 1 := by
    intro r hr
    rw [htR r hr]
    group
  have hRC : R ≤ C := fun r hr => ⟨hR.1 hr, by rw [hRtriv r hr]; exact Subgroup.one_mem _⟩
  have hRker : R.subgroupOf C ≤ (delta K t z hz).ker := by
    intro r hr
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hRtriv r (Subgroup.mem_subgroupOf.mp hr)
  have hrange : Nat.card (delta K t z hz).range = 2 := by
    have hdvd : Nat.card (delta K t z hz).range ∣ 2 := by
      have := Subgroup.card_subgroup_dvd_card (delta K t z hz).range
      rwa [Nat.card_zpowers, hz2] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exfalso
      have hbot := Subgroup.eq_bot_of_card_eq _ h1
      have hmem : (delta K t z hz) ⟨k, hk, hkt⟩ ∈ (delta K t z hz).range :=
        MonoidHom.mem_range.mpr ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hne (congrArg Subtype.val hmem)
    · exact h2
  have hker : (delta K t z hz).ker.index = 2 := by rw [Subgroup.index_ker, hrange]
  have h2C : 2 ∣ R.relIndex C := by
    rw [← hker]
    exact Subgroup.index_dvd_of_le hRker
  have h2K : 2 ∣ R.relIndex K := by
    rw [← Subgroup.relIndex_mul_relIndex R C K hRC hCK]
    exact Dvd.dvd.mul_right h2C _
  obtain ⟨T, hT⟩ := hR.exists_sylow
  have hRT : R.subgroupOf K = (T : Subgroup K) := by
    rw [← hT]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  exact T.not_dvd_index (by rw [← hRT]; exact h2K)

theorem mul_comm_of_unique_involution {K : Subgroup G} {z : G} (hz2 : orderOf z = 2)
    (hzK : z ∈ K) (hU : ∀ x ∈ K, orderOf x = 2 → x = z) {k : G} (hk : k ∈ K) :
    k * z = z * k := by
  have hmem : k * z * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hzK) (K.inv_mem hk)
  have hord : orderOf (k * z * k⁻¹) = 2 := by
    have := (MulAut.conj k).orderOf_eq z
    simpa [MulAut.conj_apply, hz2] using this
  have h := hU _ hmem hord
  calc k * z = k * z * k⁻¹ * k := by group
    _ = z * k := by rw [h]

theorem commutator_mem_of_mem_normalizer {K : Subgroup G} {t : G}
    (htN : t ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) :
    k * t * k⁻¹ * t⁻¹ ∈ K := by
  have h1 : t * k⁻¹ * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htN k⁻¹).mp (K.inv_mem hk)
  have h2 : k * (t * k⁻¹ * t⁻¹) ∈ K := K.mul_mem hk h1
  simpa [mul_assoc] using h2

theorem commutator_mul_self_eq_one {t k : G} (htt : t * t = 1)
    (hc : (k * t * k⁻¹) * t = t * (k * t * k⁻¹)) :
    (k * t * k⁻¹ * t⁻¹) * (k * t * k⁻¹ * t⁻¹) = 1 := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hcc : (k * t * k⁻¹) * (k * t * k⁻¹) = 1 := by
    calc (k * t * k⁻¹) * (k * t * k⁻¹) = k * (t * t) * k⁻¹ := by group
      _ = 1 := by rw [htt]; group
  rw [htinv]
  calc k * t * k⁻¹ * t * (k * t * k⁻¹ * t)
      = (k * t * k⁻¹) * (t * (k * t * k⁻¹)) * t := by group
    _ = (k * t * k⁻¹) * ((k * t * k⁻¹) * t) * t := by rw [← hc]
    _ = ((k * t * k⁻¹) * (k * t * k⁻¹)) * (t * t) := by group
    _ = 1 := by rw [hcc, htt, one_mul]

theorem commutator_mem_oddCore_of_centralizes_sylow [Finite G] {K R : Subgroup G} {z t : G}
    (hz2 : orderOf z = 2) (hzK : z ∈ K) (hU : ∀ x ∈ K, orderOf x = 2 → x = z)
    (ht : orderOf t = 2) (htN : t ∈ Subgroup.normalizer (K : Set G))
    (hR : IsSylow2Of R K) (htR : ∀ r ∈ R, r * t = t * r) {k : G} (hk : k ∈ K) :
    k * t * k⁻¹ * t⁻¹ ∈ (classicalInvolutionOddCore K).map K.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzc : ∀ k ∈ K, k * z = z * k := fun k hk => mul_comm_of_unique_involution hz2 hzK hU hk
  have htt : t * t = 1 := by
    rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht
  let X : Subgroup G := K ⊔ Subgroup.zpowers t
  have : Fintype X := Fintype.ofFinite X
  have htX : t ∈ X := (le_sup_right : Subgroup.zpowers t ≤ X) (Subgroup.mem_zpowers t)
  have hkX : k ∈ X := (le_sup_left : K ≤ X) hk
  let t' : X := ⟨t, htX⟩
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have ht'2 : t' * t' = 1 := Subtype.ext htt
  have hiso : ∀ g : X, (g * t' * g⁻¹) * t' = t' * (g * t' * g⁻¹) → g * t' * g⁻¹ = t' := by
    intro g hg
    obtain ⟨k, hk, hgk⟩ := exists_conj_eq_of_mem_sup htN g.2
    have hc : (k * t * k⁻¹) * t = t * (k * t * k⁻¹) := by
      have h := congrArg Subtype.val hg
      change (g : G) * t * (g : G)⁻¹ * t = t * ((g : G) * t * (g : G)⁻¹) at h
      rwa [hgk] at h
    have hmz : k * t * k⁻¹ * t⁻¹ ∈ Subgroup.zpowers z := by
      by_cases hm1 : k * t * k⁻¹ * t⁻¹ = 1
      · rw [hm1]
        exact Subgroup.one_mem _
      · have hord : orderOf (k * t * k⁻¹ * t⁻¹) = 2 :=
          orderOf_eq_prime (by rw [pow_two]; exact commutator_mul_self_eq_one htt hc) hm1
        rw [hU _ (commutator_mem_of_mem_normalizer htN hk) hord]
        exact Subgroup.mem_zpowers z
    have hm := commutator_eq_one_of_mem_zpowers hzc hz2 hR htR hk hmz
    apply Subtype.ext
    change (g : G) * t * (g : G)⁻¹ = t
    rw [hgk]
    calc k * t * k⁻¹ = k * t * k⁻¹ * t⁻¹ * t := by group
      _ = t := by rw [hm, one_mul]
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar X t' ht'1 ht'2 hiso
  let N' : Subgroup K := (N.map X.subtype).subgroupOf K
  have hN'n : N'.Normal := by
    refine ⟨fun n hn c => ?_⟩
    obtain ⟨n₀, hn₀, hn₀e⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hn)
    have hcX : (c : G) ∈ X := (le_sup_left : K ≤ X) c.2
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr
      ⟨⟨c, hcX⟩ * n₀ * ⟨c, hcX⟩⁻¹, hNn.conj_mem _ hn₀ _, ?_⟩)
    simpa using hn₀e
  have hN'odd : Odd (Nat.card N') := by
    have hle : N'.map K.subtype ≤ N.map X.subtype := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_le_left
    have h1 : Nat.card N' = Nat.card (N'.map K.subtype) :=
      Nat.card_congr (N'.equivMapOfInjective K.subtype K.subtype_injective).toEquiv
    have h2 : Nat.card (N.map X.subtype) = Nat.card N :=
      (Nat.card_congr (N.equivMapOfInjective X.subtype X.subtype_injective).toEquiv).symm
    rw [h1]
    exact hNodd.of_dvd_nat (h2 ▸ Subgroup.card_dvd_of_le hle)
  have hle : N' ≤ classicalInvolutionOddCore K :=
    CFSG.ComponentClassification.OddCore.maximal K N' hN'n hN'odd
  refine ⟨⟨k * t * k⁻¹ * t⁻¹, commutator_mem_of_mem_normalizer htN hk⟩, hle ?_, rfl⟩
  refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨_, hN ⟨k, hkX⟩, ?_⟩)
  simp [t']

end CFSG.ClassicalInvolution.Disconnected.AschTight

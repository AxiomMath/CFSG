module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.CGT.Foote81L6.Basic
public import CFSG.LocalAnalysis.GH72.Vocabulary

public section

namespace CFSG.GH72

open Subgroup

namespace G4c

section Basic

variable {G : Type*} [Group G]

abbrev cj (g : G) : G →* G := (MulAut.conj g).toMonoidHom

theorem cj_apply (g x : G) : cj g x = g * x * g⁻¹ := rfl

theorem cj_injective (g : G) : Function.Injective (cj g) := (MulAut.conj g).injective

theorem map_cj_cj_inv (g : G) (K : Subgroup G) : (K.map (cj g)).map (cj g⁻¹) = K := by
  rw [map_map]
  convert map_id K using 2
  ext x
  simp [mul_assoc]

theorem map_cj_inv_cj (g : G) (K : Subgroup G) : (K.map (cj g⁻¹)).map (cj g) = K := by
  simpa using map_cj_cj_inv g⁻¹ K

theorem mem_map_cj {g x : G} {K : Subgroup G} : x ∈ K.map (cj g) ↔ g⁻¹ * x * g ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [cj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩

theorem map_cj_le_iff {g : G} {K L : Subgroup G} : K.map (cj g) ≤ L ↔ K ≤ L.map (cj g⁻¹) := by
  constructor
  · intro h x hx
    rw [mem_map_cj, inv_inv]
    exact h ⟨x, hx, rfl⟩
  · intro h
    rintro _ ⟨x, hx, rfl⟩
    have := h hx
    rw [mem_map_cj, inv_inv] at this
    simpa [cj_apply, mul_assoc] using this

theorem map_cj_eq_of_mem_normalizer {g : G} {K : Subgroup G} (hg : g ∈ normalizer (K : Set G)) :
    K.map (cj g) = K := by
  ext x
  rw [mem_map_cj]
  have := (mem_normalizer_iff.mp hg) (g⁻¹ * x * g)
  rw [this]
  simp [mul_assoc]

theorem mem_normalizer_of_map_cj_eq {g : G} {K : Subgroup G} (hg : K.map (cj g) = K) :
    g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hg]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← hg, mem_map_cj] at hh
    simpa [mul_assoc] using hh

theorem map_cj_normalizer (g : G) (K : Subgroup G) :
    (normalizer (K : Set G)).map (cj g) = normalizer ((K.map (cj g) : Subgroup G) : Set G) :=
  map_equiv_normalizer_eq K (MulAut.conj g)

theorem map_cj_le_normalizer {g : G} {K L : Subgroup G} (h : L ≤ normalizer (K : Set G)) :
    L.map (cj g) ≤ normalizer ((K.map (cj g) : Subgroup G) : Set G) := by
  rw [← map_cj_normalizer]
  exact map_mono h

theorem map_cj_C (g a : G) : (C a).map (cj g) = C (g * a * g⁻¹) := by
  ext x
  rw [mem_map_cj, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (g * a * g⁻¹) = g * ((g⁻¹ * x * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * a * g⁻¹ * x := by group
  · intro h
    calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a * g⁻¹ * x) * g := by rw [h]
      _ = a * (g⁻¹ * x * g) := by group

theorem map_cj_commutator (g : G) (K L : Subgroup G) :
    (⁅K, L⁆ : Subgroup G).map (cj g) = ⁅K.map (cj g), L.map (cj g)⁆ :=
  map_commutator K L (cj g)

theorem map_cj_sup (g : G) (K L : Subgroup G) :
    (K ⊔ L).map (cj g) = K.map (cj g) ⊔ L.map (cj g) :=
  map_sup K L (cj g)

theorem map_cj_inf (g : G) (K L : Subgroup G) :
    (K ⊓ L).map (cj g) = K.map (cj g) ⊓ L.map (cj g) :=
  map_inf K L (cj g) (cj_injective g)

theorem card_map_cj (g : G) (K : Subgroup G) : Nat.card (K.map (cj g)) = Nat.card K :=
  card_map_of_injective (cj_injective g)

theorem O_le (H : Subgroup G) : O H ≤ H := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem card_O (H : Subgroup G) : Nat.card (O H) = Nat.card (CFSG.oddCore H) :=
  card_map_of_injective H.subtype_injective

theorem odd_card_O [Finite G] (H : Subgroup G) : Odd (Nat.card (O H)) := by
  rw [card_O]
  exact CFSG.ABGLocalTools.odd_card_oddCore

theorem le_normalizer_O (H : Subgroup G) : H ≤ normalizer (O H : Set G) :=
  CFSG.ABGLocalTools.le_normalizer_map_subtype H (CFSG.oddCore H)

theorem le_O_of_le_normalizer {H K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ normalizer (K : Set G)) (hK : Odd (Nat.card K)) : K ≤ O H := by
  have hn : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHK
  have hc : Odd (Nat.card (K.subgroupOf H)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv]
  have h := CFSG.ABGLocalTools.le_oddCore_of_normal hn hc
  calc K = (K.subgroupOf H).map H.subtype := (map_subgroupOf_eq_of_le hKH).symm
    _ ≤ O H := map_mono h

theorem map_cj_O_le [Finite G] (g : G) (H : Subgroup G) :
    (O H).map (cj g) ≤ O (H.map (cj g)) :=
  le_O_of_le_normalizer (map_mono (O_le H)) (map_cj_le_normalizer (le_normalizer_O H))
    (by rw [card_map_cj]; exact odd_card_O H)

theorem map_cj_O [Finite G] (g : G) (H : Subgroup G) :
    (O H).map (cj g) = O (H.map (cj g)) := by
  refine le_antisymm (map_cj_O_le g H) ?_
  have h := map_cj_O_le g⁻¹ (H.map (cj g))
  rw [map_cj_cj_inv] at h
  have h' := map_mono (f := cj g) h
  rwa [map_cj_inv_cj] at h'

theorem O_le_O [Finite G] {H K : Subgroup G} (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G)) :
    O K ≤ O H := by
  refine le_O_of_le_normalizer ((O_le K).trans hKH) ?_ (odd_card_O K)
  intro h hh
  refine mem_normalizer_of_map_cj_eq ?_
  rw [map_cj_O, map_cj_eq_of_mem_normalizer (hHK hh)]

theorem conj_mem_O {H : Subgroup G} {h x : G} (hh : h ∈ H) (hx : x ∈ O H) :
    h * x * h⁻¹ ∈ O H :=
  (mem_normalizer_iff.mp (le_normalizer_O H hh) x).mp hx

theorem odd_card_of_le [Finite G] {K L : Subgroup G} (hKL : K ≤ L) (hL : Odd (Nat.card L)) :
    Odd (Nat.card K) :=
  hL.of_dvd_nat (card_dvd_of_le hKL)

theorem odd_orderOf_of_mem [Finite G] {K : Subgroup G} (hK : Odd (Nat.card K)) {x : G}
    (hx : x ∈ K) : Odd (orderOf x) := by
  have h : orderOf (⟨x, hx⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h
  exact hK.of_dvd_nat h

theorem inf_eq_bot_of_odd_of_isPGroup [Finite G] {K P : Subgroup G} (hK : Odd (Nat.card K))
    (hP : IsPGroup 2 P) : K ⊓ P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← card_eq_one]
  have h₁ : Nat.card (K ⊓ P : Subgroup G) ∣ Nat.card K := card_dvd_of_le inf_le_left
  have h₂ : IsPGroup 2 (K ⊓ P : Subgroup G) := hP.to_le inf_le_right
  obtain ⟨n, hn⟩ := h₂.exists_card_eq
  rw [hn] at h₁ ⊢
  rcases n with _ | n
  · rfl
  · exact absurd (hK.of_dvd_nat (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero n)) h₁))
      (by decide)

theorem card_dvd_of_surjective {H K : Type*} [Group H] [Group K] [Finite H] (f : H →* K)
    (hf : Function.Surjective f) : Nat.card K ∣ Nat.card H := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h
  exact ⟨_, h⟩

theorem odd_card_sup [Finite G] {K N : Subgroup G} (hN : Odd (Nat.card N))
    (hK : Odd (Nat.card K)) (hKN : K ≤ normalizer (N : Set G)) :
    Odd (Nat.card (N ⊔ K : Subgroup G)) := by
  set L := N ⊔ K with hL
  have hNL : N ≤ L := le_sup_left
  have hKL : K ≤ L := le_sup_right
  have hnorm : (N.subgroupOf L).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hKN)
  let f : K →* L ⧸ N.subgroupOf L := (QuotientGroup.mk' (N.subgroupOf L)).comp (inclusion hKL)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf L) q
    obtain ⟨n, hn, k, hk, rfl⟩ := (CFSG.CGT.Foote81L6.mem_sup_iff_of_le_normalizer hKN).mp hl
    refine ⟨⟨k, hk⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, mem_subgroupOf]
    have hk' : k⁻¹ * n * k⁻¹⁻¹ ∈ N := (mem_normalizer_iff.mp (hKN (K.inv_mem hk)) n).mp hn
    simpa [mul_assoc] using hk'
  have hcard := card_eq_card_quotient_mul_card_subgroup (N.subgroupOf L)
  have h1 : Nat.card (L ⧸ N.subgroupOf L) ∣ Nat.card K := card_dvd_of_surjective f hsurj
  have h2 : Nat.card (N.subgroupOf L) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe hNL).toEquiv
  rw [hcard, h2]
  exact (hK.of_dvd_nat h1).mul hN

theorem O2_le (H : Subgroup G) : O2 H ≤ H := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_O2_of_odd [Finite G] {H : Subgroup G} {x : G} (hx : x ∈ H) (hodd : Odd (orderOf x)) :
    x ∈ O2 H :=
  CFSG.GorensteinWalter.mem_pResidualOf_of_order_coprime H 2 Nat.prime_two hx
    (Nat.coprime_two_left.mpr hodd)

theorem le_O2_of_odd [Finite G] {H K : Subgroup G} (hKH : K ≤ H) (hK : Odd (Nat.card K)) :
    K ≤ O2 H := fun _ hx => mem_O2_of_odd (hKH hx) (odd_orderOf_of_mem hK hx)

theorem O_le_O2 [Finite G] (H : Subgroup G) : O H ≤ O2 H := le_O2_of_odd (O_le H) (odd_card_O H)

theorem le_normalizer_O2 [Finite G] (H : Subgroup G) : H ≤ normalizer (O2 H : Set G) := by
  have : ((O2 H).subgroupOf H).Normal :=
    CFSG.GorensteinWalter.pResidualOf_subgroupOf_normal H 2
  have h := CFSG.ABGLocalTools.le_normalizer_map_subtype H ((O2 H).subgroupOf H)
  rwa [map_subgroupOf_eq_of_le (O2_le H)] at h

theorem O2_le_of_relIndex [Finite G] {H N : Subgroup G} (hNH : N ≤ H)
    (hHN : H ≤ normalizer (N : Set G)) {n : ℕ} (hidx : N.relIndex H = 2 ^ n) : O2 H ≤ N := by
  have h := CFSG.GorensteinWalter.pResidualOf_le_of_normal_index H 2 (N.subgroupOf H)
    (normal_subgroupOf_of_le_normalizer hHN) ⟨n, hidx⟩
  rwa [map_subgroupOf_eq_of_le hNH] at h

theorem exists_relIndex_O2 [Finite G] (H : Subgroup G) : ∃ n : ℕ, (O2 H).relIndex H = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ :=
    (CFSG.GorensteinWalter.isPGroup_quotient_pResidualOf H 2 Nat.prime_two).exists_card_eq
  exact ⟨n, by rw [relIndex, index_eq_card]; exact hn⟩

theorem exists_eq_two_pow_of_dvd {m n : ℕ} (h : m ∣ 2 ^ n) : ∃ k : ℕ, m = 2 ^ k := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact ⟨k, hk⟩

theorem O2_mono [Finite G] {H K : Subgroup G} (hKH : K ≤ H) : O2 K ≤ O2 H := by
  obtain ⟨n, hn⟩ := exists_relIndex_O2 H
  have hdvd : (O2 H ⊓ K).relIndex K ∣ 2 ^ n := by
    rw [inf_relIndex_right, ← hn, ← relIndex_subgroupOf hKH]
    have : ((O2 H).subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer (le_normalizer_O2 H)
    exact relIndex_dvd_index_of_normal _ _
  obtain ⟨k, hk⟩ := exists_eq_two_pow_of_dvd hdvd
  refine (O2_le_of_relIndex inf_le_right ?_ hk).trans inf_le_left
  exact le_trans (le_inf (hKH.trans (le_normalizer_O2 H)) le_normalizer)
    (inf_normalizer_le_normalizer_inf)

theorem subsingleton_of_isPGroup_of_commutator_eq_top {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hc : commutator Q = ⊤) : Subsingleton Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  rw [not_subsingleton_iff_nontrivial] at hne
  have : Group.IsPerfect Q := ⟨hc⟩
  exact Group.IsPerfect.not_isNilpotent Q hQ.isNilpotent

theorem map_subtype_commutator (K : Subgroup G) :
    (commutator K).map K.subtype = ⁅K, K⁆ := by
  rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]

theorem commutator_subgroupOf (K : Subgroup G) : (⁅K, K⁆ : Subgroup G).subgroupOf K = commutator K := by
  rw [← map_subtype_commutator, subgroupOf, comap_map_eq_self_of_injective K.subtype_injective]

theorem O2_eq_self_of_odd_relIndex [Finite G] {K : Subgroup G}
    (hK : Odd ((⁅K, K⁆ : Subgroup G).relIndex K)) : O2 K = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup K := (O2 K).subgroupOf K with hN
  have : N.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_O2 K)
  obtain ⟨n, hn⟩ := exists_relIndex_O2 K
  have hQ : IsPGroup 2 (K ⧸ N) := by
    refine IsPGroup.of_card (n := n) ?_
    rw [← index_eq_card]
    exact hn
  have hsurj := QuotientGroup.mk'_surjective N
  have hcQ : commutator (K ⧸ N) = (commutator K).map (QuotientGroup.mk' N) := by
    rw [commutator_def, commutator_def, map_commutator,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top_of_surjective _ hsurj]
  have hidx : (commutator (K ⧸ N)).index ∣ (commutator K).index := by
    rw [hcQ]
    exact index_map_dvd _ hsurj
  have hodd : Odd (commutator (K ⧸ N)).index := by
    refine Odd.of_dvd_nat ?_ hidx
    rwa [← commutator_subgroupOf, ← relIndex]
  have h2 : (commutator (K ⧸ N)).index ∣ 2 ^ n := by
    rw [← hn, relIndex, index_eq_card]
    exact index_dvd_card _
  obtain ⟨k, hk⟩ := exists_eq_two_pow_of_dvd h2
  have hk0 : k = 0 := by
    rcases k with _ | k
    · rfl
    · rw [hk] at hodd
      exact absurd hodd (by rw [Nat.not_odd_iff_even]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩))
  rw [hk0, pow_zero, index_eq_one] at hk
  have hsub := subsingleton_of_isPGroup_of_commutator_eq_top hQ hk
  have htop : N = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  apply le_antisymm (O2_le K)
  intro x hx
  have : (⟨x, hx⟩ : K) ∈ N := htop ▸ mem_top _
  exact this

theorem subgroupOf_le_iff_le_map {H K : Subgroup G} (hKH : K ≤ H) {N : Subgroup H} :
    K.subgroupOf H ≤ N ↔ K ≤ N.map H.subtype := by
  constructor
  · intro h x hx
    exact ⟨⟨x, hKH hx⟩, h hx, rfl⟩
  · intro h x hx
    obtain ⟨y, hy, hyx⟩ := h hx
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

theorem bar_mono {H K L : Subgroup G} (h : K ≤ L) : bar H K ≤ bar H L :=
  map_mono (comap_mono h)

theorem bar_eq_bot_iff {H K : Subgroup G} (hKH : K ≤ H) : bar H K = ⊥ ↔ K ≤ O H := by
  rw [bar, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', subgroupOf_le_iff_le_map hKH]

theorem bar_O (H : Subgroup G) : bar H (O H) = ⊥ := (bar_eq_bot_iff (O_le H)).mpr le_rfl

theorem bar_self (H : Subgroup G) : bar H H = ⊤ := by
  rw [bar, subgroupOf_self, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem subgroupOf_sup_of_le {H K L : Subgroup G} (hK : K ≤ H) (hL : L ≤ H) :
    (K ⊔ L).subgroupOf H = K.subgroupOf H ⊔ L.subgroupOf H := by
  apply map_injective H.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hK, map_subgroupOf_eq_of_le hL,
    map_subgroupOf_eq_of_le (sup_le hK hL)]

theorem bar_sup {H K L : Subgroup G} (hK : K ≤ H) (hL : L ≤ H) :
    bar H (K ⊔ L) = bar H K ⊔ bar H L := by
  rw [bar, subgroupOf_sup_of_le hK hL, Subgroup.map_sup]
  rfl

theorem bar_sup_O {H K : Subgroup G} (hK : K ≤ H) : bar H (K ⊔ O H) = bar H K := by
  rw [bar_sup hK (O_le H), bar_O, sup_bot_eq]

theorem commutator_le_of_le {H K L : Subgroup G} (hK : K ≤ H) (hL : L ≤ H) : ⁅K, L⁆ ≤ H := by
  rw [commutator_le]
  intro k hk l hl
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hK hk) (hL hl)) (H.inv_mem (hK hk))) (H.inv_mem (hL hl))

theorem subgroupOf_commutator_of_le {H K L : Subgroup G} (hK : K ≤ H) (hL : L ≤ H) :
    (⁅K, L⁆ : Subgroup G).subgroupOf H = ⁅K.subgroupOf H, L.subgroupOf H⁆ := by
  apply map_injective H.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le hK, map_subgroupOf_eq_of_le hL,
    map_subgroupOf_eq_of_le (commutator_le_of_le hK hL)]

theorem bar_commutator {H K L : Subgroup G} (hK : K ≤ H) (hL : L ≤ H) :
    bar H ⁅K, L⁆ = ⁅bar H K, bar H L⁆ := by
  rw [bar, subgroupOf_commutator_of_le hK hL, map_commutator]
  rfl

theorem bar_le_normalizer {H K L : Subgroup G} (h : L ≤ normalizer (K : Set G)) :
    bar H L ≤ normalizer (bar H K : Set (Bar H)) := by
  refine le_trans (map_mono ?_) (le_normalizer_map _)
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  rw [mem_subgroupOf, mem_subgroupOf]
  exact (mem_normalizer_iff.mp (h hx)) y

theorem card_subgroupOf_dvd (H K : Subgroup G) : Nat.card (K.subgroupOf H) ∣ Nat.card K := by
  have h : Nat.card (K.subgroupOf H) = Nat.card (K ⊓ H : Subgroup G) := by
    rw [← subgroupOf_map_subtype, card_map_of_injective H.subtype_injective]
  rw [h]
  exact card_dvd_of_le inf_le_left

theorem odd_card_bar {H K : Subgroup G} (hK : Odd (Nat.card K)) : Odd (Nat.card (bar H K)) :=
  (hK.of_dvd_nat (card_subgroupOf_dvd H K)).of_dvd_nat (card_map_dvd _ _)

theorem isPGroup_bar {p : ℕ} {H P : Subgroup G} (hP : IsPGroup p P) : IsPGroup p (bar H P) :=
  (hP.comap_subtype (K := H)).map _

theorem map_cj_O2_le [Finite G] (g : G) (H : Subgroup G) :
    O2 (H.map (cj g)) ≤ (O2 H).map (cj g) := by
  obtain ⟨n, hn⟩ := exists_relIndex_O2 H
  refine O2_le_of_relIndex (map_mono (O2_le H)) (map_cj_le_normalizer (le_normalizer_O2 H))
    (n := n) ?_
  rw [relIndex_map_map_of_injective _ _ (cj_injective g), hn]

theorem map_cj_O2 [Finite G] (g : G) (H : Subgroup G) : (O2 H).map (cj g) = O2 (H.map (cj g)) := by
  refine le_antisymm ?_ (map_cj_O2_le g H)
  have h := map_cj_O2_le g⁻¹ (H.map (cj g))
  rw [map_cj_cj_inv] at h
  have h' := map_mono (f := cj g) h
  rwa [map_cj_inv_cj] at h'

theorem exists_mem_map_cj_le [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) {H Q : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) (hQH : Q ≤ H) (hQ : IsPGroup p Q) :
    ∃ c ∈ H, Q.map (cj c) ≤ P := by
  let P' : Sylow p H := P.subtype hPH
  have hQ' : IsPGroup p (Q.subgroupOf H) := hQ.comap_subtype
  obtain ⟨T, hT⟩ := hQ'.exists_le_sylow
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq H T P'
  refine ⟨d, d.2, ?_⟩
  have hdT : ((d • T : Sylow p H) : Subgroup H) =
      (T : Subgroup H).map (MulAut.conj d).toMonoidHom := rfl
  rw [hd] at hdT
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (⟨x, hQH hx⟩ : H) ∈ (T : Subgroup H) := hT hx
  have hmem : (MulAut.conj d) ⟨x, hQH hx⟩ ∈ (P' : Subgroup H) := by
    rw [hdT]
    exact ⟨_, hx', rfl⟩
  rw [Sylow.coe_subtype, mem_subgroupOf] at hmem
  exact hmem

theorem oddCore_bar_eq_bot [Finite G] (H : Subgroup G) : CFSG.oddCore (Bar H) = ⊥ := by
  set N := CFSG.oddCore (Bar H)
  set f := QuotientGroup.mk' (CFSG.oddCore H)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  set Np := N.comap f
  have hker : f.ker ≤ Np := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    show f x ∈ N
    rw [hx]
    exact N.one_mem
  have : (f.ker.subgroupOf Np).Normal := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hcard : Nat.card Np = Nat.card N * Nat.card (CFSG.oddCore H) := by
    let φ : Np →* N := (f.comp Np.subtype).codRestrict N (fun x => x.2)
    have hφ : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨⟨x, hy⟩, rfl⟩
    have hk : φ.ker = f.ker.subgroupOf Np := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker, ← Subtype.coe_inj]
      rfl
    have h := card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hk,
      Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv, QuotientGroup.ker_mk'] at h
    exact h
  have hNp : Odd (Nat.card Np) := by
    rw [hcard]
    exact CFSG.ABGLocalTools.odd_card_oddCore.mul CFSG.ABGLocalTools.odd_card_oddCore
  have hNpn : Np.Normal := (inferInstance : N.Normal).comap f
  have hle : Np ≤ CFSG.oddCore H := CFSG.ABGLocalTools.le_oddCore_of_normal hNpn hNp
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  have : x ∈ CFSG.oddCore H := hle hy
  rw [← QuotientGroup.ker_mk' (CFSG.oddCore H), MonoidHom.mem_ker] at this
  rw [mem_bot]
  exact this

theorem eq_bot_of_normal_of_odd_bar [Finite G] {H : Subgroup G} {N : Subgroup (Bar H)}
    (hN : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have h := CFSG.ABGLocalTools.le_oddCore_of_normal hN hodd
  rwa [oddCore_bar_eq_bot, le_bot_iff] at h

theorem isPGroup_of_forall_le_centralizer {X : Type*} [Group X] [Finite X]
    (hO : CFSG.oddCore X = ⊥) {T : Subgroup X} (hT : T.Normal)
    (hc : ∀ Q : Subgroup X, Q ≤ T → IsPGroup 2 Q → T ≤ centralizer (Q : Set X)) :
    IsPGroup 2 T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 T))
  have hPc : normalizer ((P : Subgroup T) : Set T) ≤ centralizer ((P : Subgroup T) : Set T) := by
    intro g _
    rw [mem_centralizer_iff]
    intro h hh
    have hQ : IsPGroup 2 ((P : Subgroup T).map T.subtype) := P.isPGroup'.map _
    have := hc _ (by
      rintro _ ⟨y, -, rfl⟩
      exact y.2) hQ g.2
    rw [mem_centralizer_iff] at this
    have hh' := this h ⟨h, hh, rfl⟩
    exact Subtype.ext hh'
  set N := (MonoidHom.transferSylow P hPc).ker with hNdef
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hPc
  have hNodd : Odd (Nat.card N) := by
    have h1 := hcomp.card_mul
    have h2 := card_mul_index (P : Subgroup T)
    have hidx : ¬ 2 ∣ (P : Subgroup T).index := P.not_dvd_index
    have hpos : 0 < Nat.card (P : Subgroup T) := Nat.card_pos
    have : Nat.card N = (P : Subgroup T).index := by
      have h3 : Nat.card N * Nat.card (P : Subgroup T) =
          Nat.card (P : Subgroup T) * (P : Subgroup T).index := by rw [h1, h2]
      rw [mul_comm (Nat.card (P : Subgroup T))] at h3
      exact Nat.eq_of_mul_eq_mul_right hpos h3
    rw [this, Nat.odd_iff]
    omega
  have hNn : N.Normal := MonoidHom.normal_ker _
  have hall : ∀ K : Subgroup T, Odd (Nat.card K) → K ≤ N := by
    intro K hK x hx
    have hxo : Odd (orderOf x) := odd_orderOf_of_mem hK hx
    set y := MonoidHom.transferSylow P hPc x
    have hy2 : IsPGroup 2 (P : Subgroup T) := P.isPGroup'
    obtain ⟨k, hk⟩ := hy2 y
    have hdvd : orderOf y ∣ orderOf x := orderOf_map_dvd _ x
    have hy1 : y = 1 := by
      have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      rcases j with _ | j
      · rw [pow_zero, orderOf_eq_one_iff] at hj
        exact hj
      · exact absurd (hxo.of_dvd_nat (hj ▸ hdvd)) (by
          rw [Nat.not_odd_iff_even]
          exact (Nat.even_pow.mpr ⟨even_two, by omega⟩))
    exact hy1
  set N' : Subgroup X := N.map T.subtype with hN'
  have hN'T : N' ≤ T := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hN'odd : Odd (Nat.card N') := by
    rwa [hN', card_map_of_injective T.subtype_injective]
  have hN'n : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgn : g * n * g⁻¹ ∈ T := hT.conj_mem n (hN'T hn) g
    set K : Subgroup X := N'.map (MulAut.conj g).toMonoidHom
    have hKT : K ≤ T := by
      rintro _ ⟨m, hm, rfl⟩
      exact hT.conj_mem m (hN'T hm) g
    have hKodd : Odd (Nat.card (K.subgroupOf T)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hKT).toEquiv,
        card_map_of_injective (MulAut.conj g).injective]
      exact hN'odd
    have hle := hall _ hKodd
    have : (⟨g * n * g⁻¹, hgn⟩ : T) ∈ K.subgroupOf T := by
      rw [mem_subgroupOf]
      exact ⟨n, hn, rfl⟩
    exact ⟨_, hle this, rfl⟩
  have hN'bot : N' = ⊥ := by
    have h := CFSG.ABGLocalTools.le_oddCore_of_normal hN'n hN'odd
    rwa [hO, le_bot_iff] at h
  have hNbot : N = ⊥ := by
    rw [hN'] at hN'bot
    exact (map_eq_bot_iff_of_injective _ T.subtype_injective).mp hN'bot
  have hPtop : (P : Subgroup T) = ⊤ := by
    have h1 := hcomp.card_mul
    rw [← hNdef, hNbot, card_bot, one_mul] at h1
    exact (card_eq_iff_eq_top _).mp h1
  have : IsPGroup 2 (⊤ : Subgroup T) := hPtop ▸ P.isPGroup'
  exact IsPGroup.of_equiv this topEquiv

end Basic

end G4c

end CFSG.GH72

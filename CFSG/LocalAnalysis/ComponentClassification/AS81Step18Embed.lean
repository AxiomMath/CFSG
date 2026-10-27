module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Classes
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Holt
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_conj_le_normalizer {L : Subgroup G} {x l : G}
    (hl : l ∈ normalizer (L : Set G)) (hx : centralizer ({x} : Set G) ≤ normalizer (L : Set G)) :
    centralizer ({l * x * l⁻¹} : Set G) ≤ normalizer (L : Set G) := by
  intro c hc
  have h1 : l⁻¹ * c * l ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hc ⊢
    calc l⁻¹ * c * l * x = l⁻¹ * (c * (l * x * l⁻¹)) * l := by group
      _ = l⁻¹ * (l * x * l⁻¹ * c) * l := by rw [hc]
      _ = x * (l⁻¹ * c * l) := by group
  have h2 := (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).mul_mem hl (hx h1))
    ((normalizer (L : Set G)).inv_mem hl)
  rwa [show l * (l⁻¹ * c * l) * l⁻¹ = c by group] at h2

omit [Finite G] in
theorem mem_normalizer_rightConjugate_iff {L : Subgroup G} {k x : G} :
    x ∈ normalizer (rightConjugate L k : Set G) ↔ k * x * k⁻¹ ∈ normalizer (L : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h w
    have h1 := h (k⁻¹ * w * k)
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff] at h1
    rwa [show k * (k⁻¹ * w * k) * k⁻¹ = w by group,
      show k * (x * (k⁻¹ * w * k) * x⁻¹) * k⁻¹ = k * x * k⁻¹ * w * (k * x * k⁻¹)⁻¹ by group] at h1
  · intro h y
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff, h (k * y * k⁻¹),
      show k * x * k⁻¹ * (k * y * k⁻¹) * (k * x * k⁻¹)⁻¹ = k * (x * y * x⁻¹) * k⁻¹ by group]

section Action

variable {L : Subgroup G} {Ω : Type} [Group Ω] [Finite Ω] {M : Subgroup Ω}
  {φ : normalizer (L : Set G) →* Ω}

omit [Finite G] [Finite Ω] in
theorem exists_conj_of_map_conj (hφ : IsActionHom L M φ) (hZ : Odd (Nat.card (center ↥L)))
    {x y : G} (hx : x ∈ L) (hy : y ∈ L) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) {m : Ω} (hm : m ∈ M)
    (h : φ ⟨y, le_normalizer hy⟩ = m * φ ⟨x, le_normalizer hx⟩ * m⁻¹) :
    ∃ l ∈ L, y = l * x * l⁻¹ := by
  obtain ⟨l, hl, hlm⟩ := hφ.exists_eq m hm
  set x' := l * x * l⁻¹ with hx'
  have hx'L : x' ∈ L := L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
  have hφx' : φ ⟨x', le_normalizer hx'L⟩ = φ ⟨y, le_normalizer hy⟩ := by
    have e : (⟨x', le_normalizer hx'L⟩ : normalizer (L : Set G)) =
        ⟨l, le_normalizer hl⟩ * ⟨x, le_normalizer hx⟩ * ⟨l, le_normalizer hl⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hlm, h]
  set d := x'⁻¹ * y with hd
  have hdL : d ∈ L := L.mul_mem (L.inv_mem hx'L) hy
  have hdC : d ∈ centralizer (L : Set G) := by
    have h1 : φ (⟨x', le_normalizer hx'L⟩⁻¹ * ⟨y, le_normalizer hy⟩) = 1 := by
      rw [map_mul, map_inv, hφx', inv_mul_cancel]
    exact (hφ.eq_one_iff _).mp h1
  have hcomm : Commute x' d := mem_centralizer_iff.mp hdC x' hx'L
  have hx'2 : x' ^ 2 = 1 := by
    rw [hx', sq, show l * x * l⁻¹ * (l * x * l⁻¹) = l * (x * x) * l⁻¹ by group, ← sq, hx2]
    group
  have hyd : y = x' * d := by rw [hd]; group
  have hd2 : d ^ 2 = 1 := by
    have h1 := hcomm.mul_pow 2
    rw [← hyd, hy2, hx'2, one_mul] at h1
    exact h1.symm
  have hd1 : d = 1 := by
    obtain ⟨k, hk⟩ := odd_orderOf_of_mem_inf hZ hdL hdC
    have h2 : orderOf d ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hd2)
    exact orderOf_eq_one_iff.mp (by omega)
  exact ⟨l, hl, by rw [hyd, hd1, mul_one]⟩

omit [Finite G] [Finite Ω] in
theorem centralizer_le_normalizer_of_mem (hD2 : InvolutionTwoClasses M)
    (hφ : IsActionHom L M φ) (hZ3 : Nat.card (center ↥L) ∣ 3)
    (hCL : Odd (Nat.card (centralizer (L : Set G)))) {z r : G} (hz : orderOf z = 2) (hzL : z ∈ L)
    (hzN : centralizer ({z} : Set G) ≤ normalizer (L : Set G)) (hr : orderOf r = 2) (hrL : r ∈ L)
    (hrN : centralizer ({r} : Set G) ≤ normalizer (L : Set G))
    (hzr : ∀ l ∈ L, r ≠ l * z * l⁻¹) {y : G} (hy : orderOf y = 2) (hyL : y ∈ L) :
    centralizer ({y} : Set G) ≤ normalizer (L : Set G) := by
  have hZ : Odd (Nat.card (center ↥L)) := Odd.of_dvd_nat (by decide) hZ3
  have sq2 : ∀ {a : G}, orderOf a = 2 → a ^ 2 = 1 := fun h => by rw [← h, pow_orderOf_eq_one]
  have hφz := orderOf_actionHom hφ hCL (r := ⟨z, le_normalizer hzL⟩) hz
  have hφr := orderOf_actionHom hφ hCL (r := ⟨r, le_normalizer hrL⟩) hr
  have hφy := orderOf_actionHom hφ hCL (r := ⟨y, le_normalizer hyL⟩) hy
  rcases hD2 _ (hφ.map_mem z hzL) _ (hφ.map_mem r hrL) _ (hφ.map_mem y hyL) hφz hφr hφy with
    ⟨m, hm, h⟩ | ⟨m, hm, h⟩ | ⟨m, hm, h⟩
  · obtain ⟨l, hl, rfl⟩ := exists_conj_of_map_conj hφ hZ hzL hyL (sq2 hz) (sq2 hy) hm h
    exact centralizer_conj_le_normalizer (le_normalizer hl) hzN
  · obtain ⟨l, hl, rfl⟩ := exists_conj_of_map_conj hφ hZ hrL hyL (sq2 hr) (sq2 hy) hm h
    exact centralizer_conj_le_normalizer (le_normalizer hl) hrN
  · obtain ⟨l, hl, hlr⟩ := exists_conj_of_map_conj hφ hZ hzL hrL (sq2 hz) (sq2 hr) hm h
    exact absurd hlr (hzr l hl)

theorem rightConjugate_eq_of_centralizer_le {T : Subgroup Ω} (hD : FusionModel M T)
    (hφ : IsActionHom L M φ) (hφT : φ.range ≤ T) (hZ3 : Nat.card (center ↥L) ∣ 3)
    (hCL : Odd (Nat.card (centralizer (L : Set G)))) {z : G} (hz : orderOf z = 2)
    (hzL : centralizer ({z} : Set G) ≤ normalizer (L : Set G)) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hSz : S ≤ centralizer ({z} : Set G)) {y : G} (hy : orderOf y = 2)
    (hyN : centralizer ({y} : Set G) ≤ normalizer (L : Set G)) {c : G}
    (hc : y ∈ normalizer (rightConjugate L c : Set G)) : rightConjugate L c = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfus : ∀ g : G, z ∈ normalizer (rightConjugate L g : Set G) → rightConjugate L g = L :=
    fun g hg => rightConjugate_eq_of_fusionModel hD hφ hφT hZ3 hCL hz hzL hS hSz hg
  set N' := normalizer (rightConjugate L c : Set G) with hN'
  have hSc : rightConjugate S c ≤ N' :=
    rightConjugate_le_normalizer_rightConjugate (hSz.trans hzL) c
  have hScG : IsSylowOf 2 (rightConjugate S c) ⊤ := by
    have h := AschbacherTheorem3.isSylowOf_rightConjugate hS c
    rwa [rightConjugate_top] at h
  have hNodd : ¬ 2 ∣ N'.relIndex ⊤ := by
    have h1 := hScG
    rw [isSylowOf_iff] at h1
    intro h2
    apply h1.2.2
    rw [← relIndex_mul_relIndex _ N' ⊤ hSc le_top]
    exact h2.mul_left _
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 N'
  obtain ⟨a, haN, hay⟩ := AS76b.exists_conj_mem_of_isSylowOf hQ hc (n := 1)
    (by rw [pow_one, ← hy, pow_orderOf_eq_one])
  have hPN : IsSylowOf 2 (rightConjugate Q a) N' := by
    have h := AschbacherTheorem3.isSylowOf_rightConjugate hQ a
    rwa [(rightConjugate_eq_self_iff N' a).mpr (le_normalizer haN)] at h
  have hyP : y ∈ rightConjugate Q a := (mem_rightConjugate_iff _ _ _).mpr hay
  have hPG : IsSylowOf 2 (rightConjugate Q a) ⊤ := by
    rw [isSylowOf_iff] at hPN ⊢
    refine ⟨le_top, hPN.2.1, fun h2 => ?_⟩
    rw [← relIndex_mul_relIndex _ N' ⊤ hPN.1 le_top] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hPN.2.2 h
    · exact hNodd h
  obtain ⟨k, -, hk⟩ := hS.exists_mem_conj hPG
  have hzS : z ∈ S := (mem_centerIn_of_le_centralizer hS hz hSz).1
  have hz'P : k * z * k⁻¹ ∈ rightConjugate Q a :=
    (hk _).mpr (by rwa [show k⁻¹ * (k * z * k⁻¹) * k = z by group])
  have hz'y : k * z * k⁻¹ ∈ centralizer ({y} : Set G) := by
    have h1 := mem_centralizer_singleton_iff.mp (hSz ((hk y).mp hyP))
    rw [mem_centralizer_singleton_iff]
    calc k * z * k⁻¹ * y = k * (z * (k⁻¹ * y * k)) * k⁻¹ := by group
      _ = k * (k⁻¹ * y * k * z) * k⁻¹ := by rw [h1]
      _ = y * (k * z * k⁻¹) := by group
  have hkN : k ∈ normalizer (L : Set G) :=
    (rightConjugate_eq_self_iff L k).mp (hfus k (mem_normalizer_rightConjugate_iff.mpr (hyN hz'y)))
  have h3 : rightConjugate (rightConjugate L c) k = L := by
    have h4 : z ∈ normalizer (rightConjugate (rightConjugate L c) k : Set G) :=
      mem_normalizer_rightConjugate_iff.mpr (hPN.le hz'P)
    rw [rightConjugate_mul] at h4 ⊢
    exact hfus _ h4
  calc rightConjugate L c = rightConjugate (rightConjugate (rightConjugate L c) k) k⁻¹ :=
        (rightConjugate_rightConjugate_inv_cancel _ _).symm
    _ = rightConjugate L k⁻¹ := by rw [h3]
    _ = L := (rightConjugate_eq_self_iff L k⁻¹).mpr (inv_mem hkN)

theorem index_subgroupOf_eq_two {T : Subgroup Ω} (hD : FusionModel M T) {t : Ω} (ht : t ∈ T)
    (htM : t ∉ M) : (M.subgroupOf T).index = 2 := by
  have h := (M.subgroupOf T).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hD.le).toEquiv] at h
  have hM : 0 < Nat.card M := Nat.card_pos
  have h1 : (M.subgroupOf T).index ≠ 1 := by
    rw [Ne, index_eq_one, subgroupOf_eq_top]
    exact fun hle => htM (hle ht)
  have h0 : (M.subgroupOf T).index ≠ 0 := index_ne_zero_of_finite
  have h2 : (M.subgroupOf T).index ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have := hD.index
    rw [← h] at this
    nlinarith
  omega

theorem mem_of_mem_normalizer {H : Subgroup G} (hHs : IsSimpleGroup ↥H)
    (hHnab : ∃ a b : ↥H, a * b ≠ b * a) {T : Subgroup Ω} (hD : FusionModel M T)
    (hφ : IsActionHom L M φ) (hφT : φ.range ≤ T)
    (hCL : Odd (Nat.card (centralizer (L : Set G)))) {S : Subgroup G}
    (hSH : IsSylowOf 2 (S ⊓ H) H) (hSN : S ≤ normalizer (L : Set G))
    (hinv : ∀ y ∈ L, orderOf y = 2 → ∀ c : G, y ∈ normalizer (rightConjugate L c : Set G) →
      rightConjugate L c = L)
    {x : G} (hxH : x ∈ H) (hxN : x ∈ normalizer (L : Set G)) (hx : orderOf x = 2) : x ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have sq2 : ∀ {a : G}, orderOf a = 2 → a ^ 2 = 1 := fun h => by rw [← h, pow_orderOf_eq_one]
  have key : ∀ x ∈ S ⊓ H, orderOf x = 2 → x ∈ L := by
    intro x hxSH hx2
    by_contra hxL
    have hxN : x ∈ normalizer (L : Set G) := hSN hxSH.1
    have hφx : φ ⟨x, hxN⟩ ∉ M := fun h => hxL (mem_of_actionHom_mem hφ hCL hxN (sq2 hx2) h)
    have hidx := index_subgroupOf_eq_two hD (hφT ⟨_, rfl⟩) hφx
    set I : Subgroup G := (M.comap φ).map (normalizer (L : Set G)).subtype with hI
    have hmemI : ∀ (w : G) (hw : w ∈ normalizer (L : Set G)), w ∈ I ↔ φ ⟨w, hw⟩ ∈ M := by
      intro w hw
      constructor
      · rintro ⟨n, hn, hnw⟩
        have : n = ⟨w, hw⟩ := Subtype.ext hnw
        rw [← this]
        exact hn
      · intro h
        exact ⟨⟨w, hw⟩, h, rfl⟩
    obtain ⟨Q, hQ⟩ := hSH.exists_sylow_eq_subgroupOf
    set U : Subgroup ↥H := (Q : Subgroup ↥H) ⊓ I.subgroupOf H with hU
    have hQS : ∀ q : ↥H, q ∈ (Q : Subgroup ↥H) → (q : G) ∈ normalizer (L : Set G) := by
      intro q hq
      rw [hQ, mem_subgroupOf] at hq
      exact hSN hq.1
    have hxQ : (⟨x, hxSH.2⟩ : ↥H) ∈ (Q : Subgroup ↥H) := by
      rw [hQ, mem_subgroupOf]
      exact hxSH
    have hxU : (⟨x, hxSH.2⟩ : ↥H) ∉ U := fun h => hφx ((hmemI x hxN).mp h.2)
    have hUidx : U.relIndex (Q : Subgroup ↥H) = 2 := by
      rw [relIndex, index_eq_two_iff]
      refine ⟨⟨⟨x, hxSH.2⟩, hxQ⟩, fun b => ?_⟩
      have hbN := hQS b b.2
      have hmul : φ ⟨(b : G) * x, (normalizer (L : Set G)).mul_mem hbN hxN⟩ ∈ M ↔
          ¬ φ ⟨(b : G), hbN⟩ ∈ M := by
        have e : (⟨(b : G) * x, (normalizer (L : Set G)).mul_mem hbN hxN⟩ :
            normalizer (L : Set G)) = ⟨(b : G), hbN⟩ * ⟨x, hxN⟩ := rfl
        have h1 := mul_mem_iff_of_index_two hidx (a := ⟨_, hφT ⟨⟨(b : G), hbN⟩, rfl⟩⟩)
          (b := ⟨_, hφT ⟨⟨x, hxN⟩, rfl⟩⟩)
        rw [mem_subgroupOf, mem_subgroupOf] at h1
        rw [e, map_mul]
        exact h1.trans ⟨fun h hb => hφx (h.mp hb), fun h => iff_of_false h hφx⟩
      have hbU : (b : ↥H) ∈ U ↔ φ ⟨(b : G), hbN⟩ ∈ M :=
        ⟨fun h => (hmemI _ hbN).mp h.2, fun h => ⟨b.2, (hmemI _ hbN).mpr h⟩⟩
      have hbxU : ((b * ⟨⟨x, hxSH.2⟩, hxQ⟩ : ↥(Q : Subgroup ↥H)) : ↥H) ∈ U ↔
          φ ⟨(b : G) * x, (normalizer (L : Set G)).mul_mem hbN hxN⟩ ∈ M :=
        ⟨fun h => (hmemI _ _).mp h.2,
          fun h => ⟨(b * ⟨⟨x, hxSH.2⟩, hxQ⟩).2, (hmemI _ _).mpr h⟩⟩
      rw [mem_subgroupOf, mem_subgroupOf, hbxU, hbU, hmul]
      by_cases hb : φ ⟨(b : G), hbN⟩ ∈ M
      · exact Or.inr ⟨hb, fun h => h hb⟩
      · exact Or.inl ⟨hb, hb⟩
    have hmin : ∀ w ∈ (Q : Subgroup ↥H), w ∉ U → orderOf (⟨x, hxSH.2⟩ : ↥H) ≤ orderOf w := by
      intro w _ hwU
      rw [Subgroup.orderOf_mk, hx2]
      have h1 : orderOf w ≠ 1 := fun h => hwU (orderOf_eq_one_iff.mp h ▸ U.one_mem)
      have h0 := orderOf_pos w
      omega
    have hconj : ∀ k : ↥H, k⁻¹ * ⟨x, hxSH.2⟩ * k ∉ U := by
      intro k hk
      set y : G := (k : G)⁻¹ * x * k with hy
      have hyI : y ∈ I := hk.2
      have hyN : y ∈ normalizer (L : Set G) := by
        obtain ⟨n, -, hn⟩ := hyI
        rw [← hn]
        exact n.2
      have hyM : φ ⟨y, hyN⟩ ∈ M := (hmemI y hyN).mp hyI
      have hy2 : orderOf y = 2 := by
        rw [hy, show (k : G)⁻¹ * x * k = MulAut.conj (k : G)⁻¹ x by
          rw [MulAut.conj_apply, inv_inv], MulEquiv.orderOf_eq, hx2]
      have hyL : y ∈ L := mem_of_actionHom_mem hφ hCL hyN (sq2 hy2) hyM
      have hyc : y ∈ normalizer (rightConjugate L k : Set G) := by
        rw [mem_normalizer_rightConjugate_iff, hy, show (k : G) * ((k : G)⁻¹ * x * k) * (k : G)⁻¹ =
          x by group]
        exact hxN
      have hkN := (rightConjugate_eq_self_iff L k).mp (hinv y hyL hy2 k hyc)
      apply hxL
      have h1 : (k : G) * y * (k : G)⁻¹ ∈ L := (mem_normalizer_iff.mp hkN y).mp hyL
      rwa [hy, show (k : G) * ((k : G)⁻¹ * x * k) * (k : G)⁻¹ = x by group] at h1
    obtain ⟨N₂, hN₂, hN₂idx⟩ := ThompsonIndexTwo.exists_normal_index_two_of_thompson
      Q.isPGroup' Q.not_dvd_index inf_le_left hUidx hxQ hxU hmin hconj
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N₂ with h | h
    · rw [h, index_bot] at hN₂idx
      have : IsCyclic ↥H := isCyclic_of_prime_card hN₂idx
      obtain ⟨a, b, hab⟩ := hHnab
      exact hab (mul_comm' a b)
    · rw [h, index_top] at hN₂idx
      exact absurd hN₂idx (by norm_num)
  have hSHN : IsSylowOf 2 (S ⊓ H) (H ⊓ normalizer (L : Set G)) :=
    hSH.of_le (le_inf inf_le_right (inf_le_left.trans hSN)) inf_le_left
  obtain ⟨a, haHN, hax⟩ := AS76b.exists_conj_mem_of_isSylowOf hSHN ⟨hxH, hxN⟩ (n := 1)
    (by rw [pow_one]; exact sq2 hx)
  have h1 := key _ hax (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact hx)
  have h2 : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ ∈ L :=
    (mem_normalizer_iff.mp ((normalizer (L : Set G)).inv_mem haHN.2) _).mp h1
  rwa [show a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x by group] at h2

omit [Finite Ω] in
theorem fusionStronglyEmbedded_normalizer {H : Subgroup G}
    (hNH : (normalizer (L : Set G)).subgroupOf H ≠ ⊤) {z : G} (hzH : z ∈ H)
    (hzN : z ∈ normalizer (L : Set G)) (hz : orderOf z = 2)
    (hinvL : ∀ x ∈ H, x ∈ normalizer (L : Set G) → orderOf x = 2 → x ∈ L)
    (hinv : ∀ y ∈ L, orderOf y = 2 → ∀ c : G, y ∈ normalizer (rightConjugate L c : Set G) →
      rightConjugate L c = L) :
    fusionStronglyEmbedded ((normalizer (L : Set G)).subgroupOf H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set NH := (normalizer (L : Set G)).subgroupOf H with hNHdef
  refine ⟨hNH, ?_, fun h hh => ?_⟩
  · have hzNH : (⟨z, hzH⟩ : ↥H) ∈ NH := hzN
    have h2 := Subgroup.orderOf_dvd_natCard NH hzNH
    rw [Subgroup.orderOf_mk, hz] at h2
    exact even_iff_two_dvd.mpr h2
  · by_contra hodd
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hodd
    obtain ⟨hy1, hy2⟩ := mem_inf.mp y.2
    have hyN : (((y : ↥H) : G)) ∈ normalizer (L : Set G) := hy1
    have hyo : orderOf ((y : ↥H) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
    have hyL := hinvL _ (y : ↥H).2 hyN hyo
    have hyc : ((y : ↥H) : G) ∈ normalizer (rightConjugate L h : Set G) := by
      obtain ⟨n, hn, hny⟩ := hy2
      have e : ((y : ↥H) : G) = (h : G)⁻¹ * (n : G) * h := by
        rw [← hny]
        simp
      rw [mem_normalizer_rightConjugate_iff, e,
        show (h : G) * ((h : G)⁻¹ * n * h) * (h : G)⁻¹ = n by group]
      exact hn
    exact hh ((rightConjugate_eq_self_iff L h).mp (hinv _ hyL hyo h hyc))

theorem false_of_frame18 {A R : Subgroup G} {g : G}
    {E F : Subgroup G} (hF : Frame G A A R g E F)
    (hHA : normalClosure (A : Set G) = CFSG.generalizedFitting G)
    (hFs : IsSimpleGroup (CFSG.generalizedFitting G)) {z : G} (hz : orderOf z = 2)
    (hzR : ∀ x : G, z ∉ rightConjugate R x) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hSz : S ≤ centralizer ({z} : Set G)) (hRz : R ≤ centralizer ({z} : Set G))
    {T : Subgroup Ω} (hD : FusionModel M T) (hD2 : InvolutionTwoClasses M)
    (hφ : IsActionHom L M φ) (hφT : φ.range ≤ T) (hZ3 : Nat.card (center ↥L) ∣ 3)
    (hCL : Odd (Nat.card (centralizer (L : Set G))))
    (hzL : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hAL : normalizer (A : Set G) ≤ normalizer (L : Set G))
    (hLH : L ≤ CFSG.generalizedFitting G) {W : Subgroup G} (hW : W ≠ ⊥)
    (hWL : W ≤ centralizer (L : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hFs
  have hB := hF.base
  have hstd := hB.hyp.standard
  have hq : Open.IsQuasisimple ↥A := hstd.1
  have hK := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hRK : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hAH : A ≤ CFSG.generalizedFitting G := hHA ▸ subset_normalClosure
  have hHn : (CFSG.generalizedFitting G).Normal := hHA ▸ normalClosure_normal
  have hzLm : z ∈ L := mem_of_fusionModel hD hφ hφT hCL hz hzL hS hSz
  have hzH : z ∈ CFSG.generalizedFitting G := hLH hzLm
  have hzN : z ∈ normalizer (L : Set G) := hzL (mem_centralizer_singleton_iff.mpr rfl)
  have hRN : R ≤ normalizer (L : Set G) := hRz.trans hzL
  obtain ⟨r, ⟨hrR, hrL⟩, hr1⟩ :=
    exists_mem_inf_of_fusionModel hD hφ hφT hCL hRN hF.elemR hF.cardR
  have hr2 : r ^ 2 = 1 := hF.elemR.2 r hrR
  have hro : orderOf r = 2 := orderOf_eq_prime hr2 hr1
  have hCr : centralizer ({r} : Set G) ≤ normalizer (L : Set G) := by
    intro c hc
    refine hAL ?_
    rw [← hNK]
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hK (hRK hrR) hr1 hr2
      (mem_centralizer_singleton_iff.mp hc)
  have hzr : ∀ l ∈ L, r ≠ l * z * l⁻¹ := fun l _ h =>
    hzR l ((mem_rightConjugate_iff _ _ _).mpr (h ▸ hrR))
  have hinv : ∀ y ∈ L, orderOf y = 2 → ∀ c : G, y ∈ normalizer (rightConjugate L c : Set G) →
      rightConjugate L c = L := fun y hyL hy c hc =>
    rightConjugate_eq_of_centralizer_le hD hφ hφT hZ3 hCL hz hzL hS hSz hy
      (centralizer_le_normalizer_of_mem hD2 hφ hZ3 hCL hz hzLm hzL hro hrL hCr hzr hy hyL) hc
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hZ : center ↥A = ⊤ := eq_top_iff.mpr fun x _ =>
      mem_center_iff.mpr fun y => Subtype.ext (hcon y y.2 x x.2)
    have : Nontrivial (↥A ⧸ center ↥A) := hq.2.toNontrivial
    obtain ⟨u, hu⟩ := exists_ne (1 : ↥A ⧸ center ↥A)
    apply hu
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
    rw [QuotientGroup.eq_one_iff, hZ]
    exact mem_top a
  have hnab : ∃ x y : ↥(CFSG.generalizedFitting G), x * y ≠ y * x :=
    ⟨⟨a, hAH ha⟩, ⟨b, hAH hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hZH : center ↥(CFSG.generalizedFitting G) = ⊥ :=
    RankThree.PartTwo.Sec21.center_eq_bot_of_simple hnab
  set NH : Subgroup ↥(CFSG.generalizedFitting G) :=
    (normalizer (L : Set G)).subgroupOf (CFSG.generalizedFitting G) with hNHdef
  have hNH : NH ≠ ⊤ := by
    intro htop
    have hLn : (L.subgroupOf (CFSG.generalizedFitting G)).Normal := by
      refine ⟨fun n hn h => ?_⟩
      have hh : (h : G) ∈ normalizer (L : Set G) := by
        have : h ∈ NH := htop ▸ mem_top h
        exact this
      rw [mem_subgroupOf] at hn ⊢
      have := (mem_normalizer_iff.mp hh n).mp hn
      simpa using this
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.subgroupOf (CFSG.generalizedFitting G))
      with h | h
    · have hz1 : z = 1 := Subgroup.disjoint_def.mp (subgroupOf_eq_bot.mp h) hzLm hzH
      rw [hz1, orderOf_one] at hz
      exact absurd hz (by norm_num)
    · have hHL : CFSG.generalizedFitting G ≤ L := subgroupOf_eq_top.mp h
      apply hW
      rw [eq_bot_iff]
      intro w hw
      have hwC : w ∈ centralizer (CFSG.generalizedFitting G : Set G) :=
        centralizer_le hHL (hWL hw)
      have hwH : w ∈ CFSG.generalizedFitting G := CFSG.centralizer_generalizedFitting_le G hwC
      have hwZ : (⟨w, hwH⟩ : ↥(CFSG.generalizedFitting G)) ∈
          center ↥(CFSG.generalizedFitting G) :=
        mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp hwC y y.2)
      rw [hZH, mem_bot] at hwZ
      exact (mem_bot).mpr (congrArg Subtype.val hwZ)
  have hSH : IsSylowOf 2 (S ⊓ CFSG.generalizedFitting G) (CFSG.generalizedFitting G) :=
    hS.inf_of_le_normalizer le_top (fun x _ => by
      rw [mem_normalizer_iff]
      intro y
      exact ⟨fun hy => hHn.conj_mem y hy x, fun hy => by
        have := hHn.conj_mem _ hy x⁻¹
        simpa [mul_assoc] using this⟩)
  have hinvL : ∀ x ∈ CFSG.generalizedFitting G, x ∈ normalizer (L : Set G) → orderOf x = 2 →
      x ∈ L := fun x hxH hxN hx =>
    mem_of_mem_normalizer hFs hnab hD hφ hφT hCL hSH (hSz.trans hzL) hinv hxH hxN hx
  have hse : fusionStronglyEmbedded NH :=
    fusionStronglyEmbedded_normalizer hNH hzH hzN hz hinvL hinv
  have hsol : Group.IsSolvable ↥NH :=
    AschbacherStrongEmbedding.strongly_embedded_solvable ↥(CFSG.generalizedFitting G) NH hse
      (two_le_twoRank_of_frame hF hAH)
  have hf₀ : ∀ x : ↥A, inclusion hAH x ∈ NH := fun x => by
    show (x : G) ∈ normalizer (L : Set G)
    exact hAL (le_normalizer x.2)
  have hinj : Function.Injective ((inclusion hAH).codRestrict NH hf₀) := fun x y hxy =>
    inclusion_injective hAH (congrArg Subtype.val hxy)
  have : Group.IsSolvable ↥A := Group.isSolvable_of_isSolvable_injective hinj
  exact not_isSolvable_of_isQuasisimple hq this

end Action

end CFSG.ComponentClassification.AS81

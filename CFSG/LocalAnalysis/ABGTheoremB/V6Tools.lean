module

public import CFSG.LocalAnalysis.ABGTheoremB.V56Inputs
import CFSG.LocalAnalysis.ABGTheoremB.IV1

public section

namespace CFSG.ABGTheoremB.V56

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G]

private theorem conj_mem_centralizer_of_mem_normalizer {K : Type*} [Group K] {T : Subgroup K}
    {g c : K} (hg : g ∈ Subgroup.normalizer (T : Set K))
    (hc : c ∈ Subgroup.centralizer (T : Set K)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (T : Set K) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro t ht
  have h := hc _ ((Subgroup.mem_normalizer_iff''.mp hg t).mp ht)
  calc t * (g * c * g⁻¹) = g * ((g⁻¹ * t * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * t * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * t := by group

private theorem normalizer_le_normalizer_centralizer_v6 {K : Type*} [Group K] (T : Subgroup K) :
    Subgroup.normalizer (T : Set K) ≤
      Subgroup.normalizer (Subgroup.centralizer (T : Set K) : Set K) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨conj_mem_centralizer_of_mem_normalizer hg, fun hc => ?_⟩
  have h := conj_mem_centralizer_of_mem_normalizer ((Subgroup.normalizer _).inv_mem hg) hc
  have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rwa [e] at h

private theorem mem_normalizer_inf_of_mem {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (hA y) (hB y)

private theorem mul_pow_three_mem_centralizer {T : Subgroup G} {g m : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) (hg3 : g ^ 3 ∈ Subgroup.centralizer (T : Set G))
    (hm : m ∈ Subgroup.centralizer (T : Set G)) :
    (m * g) ^ 3 ∈ Subgroup.centralizer (T : Set G) := by
  have e : (m * g) ^ 3 = m * (g * m * g⁻¹) * ((g * g) * m * (g * g)⁻¹) * g ^ 3 := by
    rw [pow_three]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hm
    (conj_mem_centralizer_of_mem_normalizer hg hm))
    (conj_mem_centralizer_of_mem_normalizer (Subgroup.mul_mem _ hg hg) hm)) hg3

private theorem eq_one_of_mem_of_mem_of_odd_v6 [Finite G] {A B : Subgroup G}
    (hA : IsPGroup 2 A) (hB : Odd (Nat.card B)) {g : G} (hgA : g ∈ A) (hgB : g ∈ B) :
    g = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA ⟨g, hgA⟩
  have h1 : orderOf g = 2 ^ k := by rw [← Subgroup.orderOf_mk g hgA]; exact hk
  have h2 : orderOf g ∣ Nat.card B := Subgroup.orderOf_dvd_natCard B hgB
  rw [h1] at h2
  have hk0 : k = 0 := by
    by_contra hk0
    exact hB.not_two_dvd_nat ((dvd_pow_self 2 hk0).trans h2)
  rw [hk0, pow_zero] at h1
  exact orderOf_eq_one_iff.mp h1

private theorem mem_centralizer_of_mem_normalizer_of_mem_sup {O T : Subgroup G}
    (hTO : T ≤ Subgroup.normalizer (O : Set G)) (hbot : ∀ x ∈ T, x ∈ O → x = 1)
    (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {m : G}
    (hmN : m ∈ Subgroup.normalizer (T : Set G)) (hmY : m ∈ O ⊔ T) :
    m ∈ Subgroup.centralizer (T : Set G) := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left O T hTO] at hmY
  obtain ⟨a, ha, b, hb, rfl⟩ := hmY
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h1 : a * b * t * (a * b)⁻¹ * t⁻¹ ∈ T :=
    T.mul_mem ((Subgroup.mem_normalizer_iff.mp hmN t).mp ht) (T.inv_mem ht)
  have h2 : a * b * t * (a * b)⁻¹ * t⁻¹ ∈ O := by
    have e : a * b * t * (a * b)⁻¹ * t⁻¹ = a * (t * a⁻¹ * t⁻¹) := by
      calc a * b * t * (a * b)⁻¹ * t⁻¹ = a * (b * t) * b⁻¹ * a⁻¹ * t⁻¹ := by group
        _ = a * (t * b) * b⁻¹ * a⁻¹ * t⁻¹ := by rw [hTab b hb t ht]
        _ = a * (t * a⁻¹ * t⁻¹) := by group
    rw [e]
    exact O.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hTO ht) a⁻¹).mp (O.inv_mem ha))
  have h3 := hbot _ h1 h2
  calc t * (a * b) = (a * b * t * (a * b)⁻¹ * t⁻¹)⁻¹ * (a * b) * t := by group
    _ = a * b * t := by rw [h3, inv_one, one_mul]

private theorem exists_of_three_dvd_automizerIndex_v6 {K : Type*} [Group K] [Finite K]
    {T : Subgroup K} (h : 3 ∣ automizerIndex T) :
    ∃ g ∈ Subgroup.normalizer (T : Set K), g ^ 3 ∈ Subgroup.centralizer (T : Set K) ∧
      g ∉ Subgroup.centralizer (T : Set K) := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have hCN : Ct ≤ Nt := Subgroup.centralizer_le_normalizer _
  have : (Ct.subgroupOf Nt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (normalizer_le_normalizer_centralizer_v6 T)
  have h3 : 3 ∣ Nat.card (Nt ⧸ Ct.subgroupOf Nt) := by
    rw [← Subgroup.index_eq_card]
    exact h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, g.2, ?_, ?_⟩
  · have : ((g ^ 3 : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := by
      rw [QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
    simpa using this
  · intro hg
    have : ((g : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := (QuotientGroup.eq_one_iff _).mpr hg
    rw [this, orderOf_one] at hq
    exact absurd hq (by norm_num)

private theorem three_dvd_automizerIndex_of_v6 {K : Type*} [Group K] [Finite K]
    {T : Subgroup K} {g : K} (hg : g ∈ Subgroup.normalizer (T : Set K))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (T : Set K))
    (h1 : g ∉ Subgroup.centralizer (T : Set K)) : 3 ∣ automizerIndex T := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have hCN : Ct ≤ Nt := Subgroup.centralizer_le_normalizer _
  have : (Ct.subgroupOf Nt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (normalizer_le_normalizer_centralizer_v6 T)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ((⟨g, hg⟩ : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 3 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using h3
    · rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact h1
  have := orderOf_dvd_natCard ((⟨g, hg⟩ : Nt) : Nt ⧸ Ct.subgroupOf Nt)
  rw [hord, ← Subgroup.index_eq_card] at this
  exact this

private theorem mem_normalizer_subgroupOf_iff_v6 {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.normalizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.normalizer (T : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hTH, Subgroup.mem_subgroupOf]

private theorem mem_centralizer_subgroupOf_iff_v6 {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.centralizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.centralizer (T : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf]
  constructor
  · intro h t ht
    exact congrArg Subtype.val (h ⟨t, hTH ht⟩ ht)
  · intro h t ht
    exact Subtype.ext (h _ ht)

private theorem exists_of_three_dvd_automizerIndex_subgroupOf_v6 [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) (h : 3 ∣ automizerIndex (T.subgroupOf H)) :
    ∃ g ∈ H, g ∈ Subgroup.normalizer (T : Set G) ∧ g ^ 3 ∈ Subgroup.centralizer (T : Set G) ∧
      g ∉ Subgroup.centralizer (T : Set G) := by
  obtain ⟨g, hgN, hg3, hg1⟩ := exists_of_three_dvd_automizerIndex_v6 h
  refine ⟨g, g.2, (mem_normalizer_subgroupOf_iff_v6 hTH).mp hgN, ?_, ?_⟩
  · simpa using (mem_centralizer_subgroupOf_iff_v6 hTH).mp hg3
  · exact fun h' => hg1 ((mem_centralizer_subgroupOf_iff_v6 hTH).mpr h')

private theorem three_dvd_automizerIndex_subgroupOf_of_v6 [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) {g : G} (hgH : g ∈ H) (hg : g ∈ Subgroup.normalizer (T : Set G))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (T : Set G))
    (h1 : g ∉ Subgroup.centralizer (T : Set G)) :
    3 ∣ automizerIndex (T.subgroupOf H) :=
  three_dvd_automizerIndex_of_v6 (g := ⟨g, hgH⟩) ((mem_normalizer_subgroupOf_iff_v6 hTH).mpr hg)
    ((mem_centralizer_subgroupOf_iff_v6 hTH).mpr (by simpa using h3))
    (fun h' => h1 ((mem_centralizer_subgroupOf_iff_v6 hTH).mp h'))

private theorem exists_mem_conj_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime]
    {P P' K : Subgroup G} (h : IsSylowOf p P K) (h' : IsSylowOf p P' K) :
    ∃ k ∈ K, ∀ x : G, x ∈ P' ↔ k⁻¹ * x * k ∈ P := by
  obtain ⟨Q, rfl⟩ := h
  obtain ⟨Q', rfl⟩ := h'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  have key : ∀ y : K, y ∈ (Q' : Subgroup K) ↔ g⁻¹ * y * g ∈ (Q : Subgroup K) := by
    intro y
    rw [← hg]
    change y ∈ MulAut.conj g • (Q : Subgroup K) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g⁻¹ * y * g, (key y).mp hy, by simp⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : (z : G) = (g : G)⁻¹ * x * g := hzx
    have hx : x = (g : G) * z * (g : G)⁻¹ := by rw [hzx']; group
    have hxK : x ∈ K := by
      rw [hx]
      exact K.mul_mem (K.mul_mem g.2 z.2) (K.inv_mem g.2)
    refine ⟨⟨x, hxK⟩, (key _).mpr ?_, rfl⟩
    have : g⁻¹ * ⟨x, hxK⟩ * g = z := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hzx'.symm)
    rw [this]
    exact hz

private theorem exists_isSylowOf_ge_v6 {p : ℕ} {Q K : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ P : Subgroup G, IsSylowOf p P K ∧ Q ≤ P := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K) : IsPGroup p (Q.subgroupOf K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, ?_⟩
  intro q hq
  exact ⟨⟨q, hQK hq⟩, hS (show (⟨q, hQK hq⟩ : K) ∈ Q.subgroupOf K from hq), rfl⟩

private theorem inf_centerOf_ne_bot_v6 [Finite G] {p : ℕ} [Fact p.Prime] {P X : Subgroup G}
    (hP : IsPGroup p P) (hXP : X ≤ P) (hnorm : P ≤ Subgroup.normalizer (X : Set G))
    (hX : X ≠ ⊥) : X ⊓ centerOf P ≠ ⊥ := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have : (X.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXP).mpr hnorm
  have hY : X.subgroupOf P ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot, disjoint_of_le_iff_left_eq_bot hXP]
    exact hX
  intro hbot
  apply Group.IsNilpotent.inf_center_ne_bot_of_normal hY
  rw [eq_bot_iff]
  rintro a ⟨haX, haZ⟩
  have hmem : (a : G) ∈ X ⊓ centerOf P := by
    refine ⟨haX, a.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp haZ ⟨g, hg⟩)
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact Subtype.ext hmem

private theorem exists_orderOf_eq_two_mem_centralizer [Finite G] {D X : Subgroup G}
    (hD2 : IsPGroup 2 D) (hDX : D ≤ Subgroup.normalizer (X : Set G))
    (heven : Even (Nat.card X)) :
    ∃ z ∈ X, z ∈ Subgroup.centralizer (D : Set G) ∧ orderOf z = 2 := by
  have hYX : X ⊔ D ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hDX
  obtain ⟨S', hS', hDS'⟩ := exists_isSylowOf_ge_v6 (le_sup_right : D ≤ X ⊔ D) hD2
  have hQ : IsSylowOf 2 (S' ⊓ X) X := hS'.inf_of_le_normalizer le_sup_left hYX
  have hQne : S' ⊓ X ≠ ⊥ := by
    intro hbot
    have h1 := (isSylowOf_iff.mp hQ).2.2
    rw [hbot, Subgroup.relIndex_bot_left] at h1
    exact h1 (even_iff_two_dvd.mp heven)
  have hS'Q : S' ≤ Subgroup.normalizer ((S' ⊓ X : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf_of_mem (Subgroup.le_normalizer hg) (hYX (hS'.le hg))
  have hW := inf_centerOf_ne_bot_v6 hS'.isPGroup inf_le_left hS'Q hQne
  have hW2 : IsPGroup 2 (S' ⊓ X ⊓ centerOf S' : Subgroup G) :=
    hS'.isPGroup.to_le (inf_le_left.trans inf_le_left)
  have h2 : 2 ∣ Nat.card (S' ⊓ X ⊓ centerOf S' : Subgroup G) :=
    hW2.card_eq_or_dvd.resolve_left (fun h => hW (Subgroup.card_eq_one.mp h))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hwm := w.2
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at hwm
  obtain ⟨⟨-, hwX⟩, hwZ⟩ := hwm
  refine ⟨w, hwX, ?_, by rw [Subgroup.orderOf_coe]; exact hw⟩
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hwZ).2) d (hDS' hd)

theorem three_dvd_automizerIndex_of_subset_mul [Finite G] {K M O H T : Subgroup G}
    (hOK : O ≤ K) (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hO : Odd (Nat.card O))
    (hcov : (K : Set G) ⊆ (O : Set G) * (M : Set G)) (hMK : M ≤ K) (hMH : M ≤ H)
    (hTM : T ≤ M) (hT2 : IsPGroup 2 T) (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (h3 : 3 ∣ automizerIndex (T.subgroupOf K)) : 3 ∣ automizerIndex (T.subgroupOf H) := by
  have hTK : T ≤ K := hTM.trans hMK
  have hTO : T ≤ Subgroup.normalizer (O : Set G) := hTK.trans hKO
  have hbot : ∀ x ∈ T, x ∈ O → x = 1 := fun x hxT hxO =>
    eq_one_of_mem_of_mem_of_odd_v6 hT2 hO hxT hxO
  have hKOM : (K : Set G) = (O : Set G) * (M : Set G) :=
    hcov.antisymm (Set.mul_subset_iff.mpr fun a ha b hb => K.mul_mem (hOK ha) (hMK hb))
  obtain ⟨g, hgK, hgN, hg3, hg1⟩ := exists_of_three_dvd_automizerIndex_subgroupOf_v6 hTK h3
  have hgOM : g ∈ (O : Set G) * (M : Set G) := by
    rw [← hKOM]
    exact hgK
  obtain ⟨o, ho, u, hu, rfl⟩ := hgOM
  have hTA : T ≤ Subgroup.normalizer ((M ⊓ O : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf_of_mem (Subgroup.le_normalizer (hTM ht)) (hTO ht)
  have hTsyl : IsSylowOf 2 T (M ⊓ O ⊔ T) := by
    refine isSylowOf_iff.mpr ⟨le_sup_right, hT2, ?_⟩
    rw [relIndex_sup_eq_relIndex_of_le_normalizer hTA]
    intro h2
    exact (hO.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)).not_two_dvd_nat
      (h2.trans (Dvd.intro _ (Subgroup.relIndex_mul_card T (M ⊓ O))))
  have hmemP' : ∀ t : G, u * t * u⁻¹ ∈ T.map (MulAut.conj u).toMonoidHom ↔ t ∈ T := fun t =>
    Subgroup.mem_map_iff_mem (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective
  have hP'X : T.map (MulAut.conj u).toMonoidHom ≤ M ⊓ O ⊔ T := by
    rintro _ ⟨t, ht, rfl⟩
    change u * t * u⁻¹ ∈ M ⊓ O ⊔ T
    have ht' : o * u * t * (o * u)⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hgN t).mp ht
    have ha : u * t * u⁻¹ * (o * u * t * (o * u)⁻¹)⁻¹ ∈ M ⊓ O := by
      refine Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem (M.mul_mem hu (hTM ht)) (M.inv_mem hu))
        (M.inv_mem (hTM ht')), ?_⟩
      have e : u * t * u⁻¹ * (o * u * t * (o * u)⁻¹)⁻¹ =
          o⁻¹ * ((o * u * t * (o * u)⁻¹) * o * (o * u * t * (o * u)⁻¹)⁻¹) := by group
      rw [e]
      exact O.mul_mem (O.inv_mem ho) ((Subgroup.mem_normalizer_iff.mp (hTO ht') o).mp ho)
    have e : u * t * u⁻¹ =
        (u * t * u⁻¹ * (o * u * t * (o * u)⁻¹)⁻¹) * (o * u * t * (o * u)⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right ht')
  have hP'syl : IsSylowOf 2 (T.map (MulAut.conj u).toMonoidHom) (M ⊓ O ⊔ T) := by
    refine isSylowOf_of_card hP'X ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj u).injective]
    exact hTsyl.card_eq
  obtain ⟨k, hkX, hk⟩ := exists_mem_conj_of_isSylowOf hTsyl hP'syl
  have hkM : k ∈ M := (sup_le inf_le_left hTM : M ⊓ O ⊔ T ≤ M) hkX
  have hkOT : k ∈ O ⊔ T := (sup_le_sup_right inf_le_right T : M ⊓ O ⊔ T ≤ O ⊔ T) hkX
  have hnN : k⁻¹ * u ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have e : k⁻¹ * u * t * (k⁻¹ * u)⁻¹ = k⁻¹ * (u * t * u⁻¹) * k := by group
    rw [e, ← hk, hmemP']
  have hm : k⁻¹ * u * (o * u)⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
    refine mem_centralizer_of_mem_normalizer_of_mem_sup hTO hbot hTab
      ((Subgroup.normalizer _).mul_mem hnN ((Subgroup.normalizer _).inv_mem hgN)) ?_
    have e : k⁻¹ * u * (o * u)⁻¹ = k⁻¹ * o⁻¹ := by group
    rw [e]
    exact (O ⊔ T).mul_mem ((O ⊔ T).inv_mem hkOT) (Subgroup.mem_sup_left (O.inv_mem ho))
  have hn : k⁻¹ * u = (k⁻¹ * u * (o * u)⁻¹) * (o * u) := by group
  refine three_dvd_automizerIndex_subgroupOf_of_v6 (hTM.trans hMH)
    (hMH (M.mul_mem (M.inv_mem hkM) hu)) hnN ?_ ?_
  · rw [hn]
    exact mul_pow_three_mem_centralizer hgN hg3 hm
  · intro hnC
    rw [hn] at hnC
    exact hg1 ((Subgroup.mul_mem_cancel_left _ hm).mp hnC)

theorem exists_ne_one_mem_T_of_even [Finite G] {σ : Setting G} (hσ : σ.IsValid)
    (hC : CStructure σ) {X : Subgroup G} (hDX : σ.D ≤ Subgroup.normalizer (X : Set G))
    (heven : Even (Nat.card X)) : ∃ t ∈ σ.T, t ≠ 1 ∧ t ∈ X := by
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  obtain ⟨z, hzX, hzD, hzord⟩ := exists_orderOf_eq_two_mem_centralizer hD2 hDX heven
  have hzC : z ∈ σ.C := Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (σ.T_le_D hσ)) hzD
  have hCeq := hC.C_eq
  have homega := hC.omega
  generalize hF : σ.D ⊓ Subgroup.centralizer (σ.T : Set G) = F₀ at hCeq homega
  have hF₀D : F₀ ≤ σ.D := by rw [← hF]; exact inf_le_left
  have hF₀C : F₀ ≤ σ.C := by rw [← hF]; exact inf_le_right
  have hF₀2 : IsPGroup 2 F₀ := hD2.to_le hF₀D
  have hF₀syl : IsSylowOf 2 F₀ σ.C := by
    refine isSylowOf_iff.mpr ⟨hF₀C, hF₀2, ?_⟩
    have h1 := relIndex_sup_eq_relIndex_of_le_normalizer
      (hF₀C.trans (le_normalizer_oddCoreIn σ.C))
    rw [hCeq] at h1
    rw [h1]
    intro h2
    exact (odd_card_oddCoreIn σ.C).not_two_dvd_nat
      (h2.trans (Dvd.intro _ (Subgroup.relIndex_mul_card F₀ (oddCoreIn σ.C))))
  have hzF₀ : z ∈ F₀ := by
    have hzc : z ∈ Subgroup.centralizer (F₀ : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hF₀D) hzD
    have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (F₀ : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hzc)
    have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord, pow_one])
    have hle : F₀ ⊔ Subgroup.zpowers z ≤ σ.C := sup_le hF₀C (Subgroup.zpowers_le.mpr hzC)
    have heq := hF₀syl.eq_of_le le_sup_left hle (hF₀2.to_sup_of_normal_left' hz2 hzN)
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  refine ⟨z, homega z hzF₀ ?_, ?_, hzX⟩
  · rw [← hzord]
    exact pow_orderOf_eq_one z
  · rintro rfl
    rw [orderOf_one] at hzord
    exact absurd hzord (by norm_num)

end CFSG.ABGTheoremB.V56

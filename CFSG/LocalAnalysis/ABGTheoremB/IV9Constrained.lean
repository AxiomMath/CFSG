module

public import CFSG.LocalAnalysis.ABGTheoremB.IV1
public import CFSG.LocalAnalysis.ABGTheoremB.Statements
public import CFSG.LocalAnalysis.ABGTheoremB.IV9Defs
import CFSG.LocalAnalysis.ABGTheoremB.IV2
import CFSG.LocalAnalysis.ABGTheoremB.IV6
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ThompsonPQ
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGQGroups
open scoped Pointwise commutatorElement

universe u

section General

variable {G : Type u} [Group G]

private theorem sup_inf_eq_of_le_normalizer {A B C : Subgroup G} (hAC : A ≤ C)
    (hB : B ≤ Subgroup.normalizer (A : Set G)) : (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx, hxC⟩ := Subgroup.mem_inf.mp hx
    have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hB] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    have hbC : b ∈ C := by
      have := C.mul_mem (C.inv_mem (hAC ha)) hxC
      simpa using this
    exact Subgroup.mul_mem_sup ha ⟨hb, hbC⟩
  · exact sup_le (le_inf le_sup_left hAC) (inf_le_inf_right C le_sup_right)

private theorem exists_mul_of_mem_sup {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hB] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

private theorem exists_mul_of_mem_sup' {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ B ⊔ A) :
    ∃ b ∈ B, ∃ a ∈ A, x = b * a := by
  have hx' : x ∈ ((B ⊔ A : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right B A hB] at hx'
  obtain ⟨b, hb, a, ha, rfl⟩ := hx'
  exact ⟨b, hb, a, ha, rfl⟩

private theorem conj_mem_of_mem_normalizer {X : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hx : x ∈ X) : g * x * g⁻¹ ∈ X :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

private theorem mem_normalizer_of_characteristic {P Q : Subgroup G} (hQP : Q ≤ P)
    (hchar : (Q.subgroupOf P).Characteristic) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) : g ∈ Subgroup.normalizer (Q : Set G) := by
  have key : ∀ h : G, h ∈ Subgroup.normalizer (P : Set G) → ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := by
    intro h hh q hq
    have hPh : P.map (MulAut.conj h).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hh
    let φ : P ≃* P := ((MulAut.conj h).subgroupMap P).trans (MulEquiv.subgroupCongr hPh)
    have hφ : ((φ ⟨q, hQP hq⟩ : P) : G) = h * q * h⁻¹ := rfl
    have hmem : (⟨q, hQP hq⟩ : P) ∈ Q.subgroupOf P := hq
    have := (Subgroup.characteristic_iff_le_comap.mp hchar) φ hmem
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at this
    rw [← hφ]
    exact this
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · exact key g hg q
  · intro hq
    have := key g⁻¹ (inv_mem hg) _ hq
    simpa [mul_assoc] using this

private theorem mem_of_coprime_orderOf_relIndex [Finite G] {A B : Subgroup G} (hAB : A ≤ B)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) {g : G} (hg : g ∈ B)
    (hcop : Nat.Coprime (orderOf g) (A.relIndex B)) : g ∈ A := by
  have : (A.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mpr hBA
  set y : B ⧸ A.subgroupOf B := ((⟨g, hg⟩ : B) : B ⧸ A.subgroupOf B)
  have h1 : orderOf y ∣ orderOf g := by
    rw [← Subgroup.orderOf_mk g hg]
    exact orderOf_map_dvd (QuotientGroup.mk' (A.subgroupOf B)) _
  have h2 : orderOf y ∣ A.relIndex B := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard y
  have h3 : orderOf y = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  exact h3

private theorem inf_eq_bot_of_isPGroup_of_coprime [Finite G] {p : ℕ} [Fact p.Prime]
    {A B : Subgroup G} (hA : IsPGroup p A) (hB : Nat.Coprime p (Nat.card B)) : A ⊓ B = ⊥ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
  rw [hk]
  exact Nat.Coprime.pow_left k hB

private theorem inf_eq_bot_of_isPGroup_two_of_odd [Finite G] {A B : Subgroup G}
    (hA : IsPGroup 2 A) (hB : Odd (Nat.card B)) : A ⊓ B = ⊥ :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  inf_eq_bot_of_isPGroup_of_coprime hA (Nat.coprime_two_left.mpr hB)

private theorem odd_card_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup p P) : Odd (Nat.card P) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk]
  exact (hp.eq_two_or_odd'.resolve_left hp2).pow

private theorem exists_orderOf_eq_pow_of_mem [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) {g : G} (hg : g ∈ P) : ∃ k : ℕ, orderOf g = p ^ k := by
  have h := (IsPGroup.iff_orderOf (p := p)).mp hP ⟨g, hg⟩
  rwa [Subgroup.orderOf_mk] at h

private theorem mem_map_conj_iff {K : Subgroup G} {g y : G} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

private theorem isSylowOf_map_conj [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (hP : IsSylowOf p P K) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) K := by
  refine isSylowOf_of_card (fun y hy => ?_) ?_
  · rw [mem_map_conj_iff] at hy
    have h := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mp (hP.le hy)
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP.card_eq]

private theorem exists_mem_normalizer_mul_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup G} (hP : IsSylowOf p P K) {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    ∃ n ∈ Subgroup.normalizer (P : Set G), ∃ k ∈ K, x = n * k := by
  obtain ⟨k, hk, hconj⟩ := hP.exists_mem_conj (isSylowOf_map_conj hP (inv_mem hx))
  refine ⟨x * k, ?_, k⁻¹, inv_mem hk, by group⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h := hconj (k * y * k⁻¹)
  rw [mem_map_conj_iff, inv_inv, show k⁻¹ * (k * y * k⁻¹) * k = y by group] at h
  rw [show x * k * y * (x * k)⁻¹ = x * (k * y * k⁻¹) * x⁻¹ by group]
  exact h.symm

private theorem normalizer_le_normalizer_centralizer (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    have hy' : g⁻¹ * y * g ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
      simpa using this
    have h := hc _ hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * y := by group
  · intro hc y hy
    have hy' : g * y * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    have h := hc _ hy'
    calc y * c = g⁻¹ * ((g * y * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h]
      _ = c * y := by group

private theorem exists_of_three_dvd_automizerIndex {K : Type*} [Group K] [Finite K]
    {T : Subgroup K} (h : 3 ∣ automizerIndex T) :
    ∃ g ∈ Subgroup.normalizer (T : Set K), g ^ 3 ∈ Subgroup.centralizer (T : Set K) ∧
      g ∉ Subgroup.centralizer (T : Set K) := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have hCN : Ct ≤ Nt := Subgroup.centralizer_le_normalizer _
  have : (Ct.subgroupOf Nt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (normalizer_le_normalizer_centralizer T)
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

private theorem three_dvd_automizerIndex_of {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    {g : K} (hg : g ∈ Subgroup.normalizer (T : Set K))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (T : Set K))
    (h1 : g ∉ Subgroup.centralizer (T : Set K)) : 3 ∣ automizerIndex T := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have hCN : Ct ≤ Nt := Subgroup.centralizer_le_normalizer _
  have : (Ct.subgroupOf Nt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (normalizer_le_normalizer_centralizer T)
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

private theorem mem_normalizer_subgroupOf_iff {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.normalizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.normalizer (T : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hTH, Subgroup.mem_subgroupOf]

private theorem mem_centralizer_subgroupOf_iff {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.centralizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.centralizer (T : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf]
  constructor
  · intro h t ht
    exact congrArg Subtype.val (h ⟨t, hTH ht⟩ ht)
  · intro h t ht
    exact Subtype.ext (h _ ht)

private theorem exists_of_three_dvd_automizerIndex_subgroupOf [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) (h : 3 ∣ automizerIndex (T.subgroupOf H)) :
    ∃ g ∈ H, g ∈ Subgroup.normalizer (T : Set G) ∧ g ^ 3 ∈ Subgroup.centralizer (T : Set G) ∧
      g ∉ Subgroup.centralizer (T : Set G) := by
  obtain ⟨g, hgN, hg3, hg1⟩ := exists_of_three_dvd_automizerIndex h
  refine ⟨g, g.2, (mem_normalizer_subgroupOf_iff hTH).mp hgN, ?_, ?_⟩
  · simpa using (mem_centralizer_subgroupOf_iff hTH).mp hg3
  · exact fun h' => hg1 ((mem_centralizer_subgroupOf_iff hTH).mpr h')

private theorem three_dvd_automizerIndex_subgroupOf_of [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) {g : G} (hgH : g ∈ H) (hg : g ∈ Subgroup.normalizer (T : Set G))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (T : Set G)) (h1 : g ∉ Subgroup.centralizer (T : Set G)) :
    3 ∣ automizerIndex (T.subgroupOf H) :=
  three_dvd_automizerIndex_of (g := ⟨g, hgH⟩) ((mem_normalizer_subgroupOf_iff hTH).mpr hg)
    ((mem_centralizer_subgroupOf_iff hTH).mpr (by simpa using h3))
    (fun h' => h1 ((mem_centralizer_subgroupOf_iff hTH).mp h'))

private theorem three_dvd_automizerIndex_mono [Finite G] {T H₁ H₂ : Subgroup G}
    (hTH : T ≤ H₁) (hH : H₁ ≤ H₂) (h : 3 ∣ automizerIndex (T.subgroupOf H₁)) :
    3 ∣ automizerIndex (T.subgroupOf H₂) := by
  obtain ⟨g, hg, hgN, hg3, hg1⟩ := exists_of_three_dvd_automizerIndex_subgroupOf hTH h
  exact three_dvd_automizerIndex_subgroupOf_of (hTH.trans hH) (hH hg) hgN hg3 hg1

private theorem exists_mem_inv_mul_mem_centralizer_of_odd {M : Subgroup G}
    (hM : Odd (Nat.card M)) {x k : G} (hx : x * x = 1) (hk : k * x * k⁻¹ * x⁻¹ ∈ M) :
    ∃ m ∈ M, m⁻¹ * k ∈ Subgroup.centralizer ({x} : Set G) := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hcI : k * x * k⁻¹ * x⁻¹ ∈ OddInversion.invertedSet M x := by
    rw [OddInversion.mem_invertedSet]
    refine ⟨hk, ?_⟩
    rw [show x * (k * x * k⁻¹ * x⁻¹) * x⁻¹ = x * k * x * k⁻¹ * (x⁻¹ * x⁻¹) by group,
      show (k * x * k⁻¹ * x⁻¹)⁻¹ = x * k * x⁻¹ * k⁻¹ by group, hxinv, hx, mul_one]
  obtain ⟨d, hd, hd2⟩ := OddInversion.exists_sq_eq_of_mem_invertedSet hM hcI
  rw [OddInversion.mem_invertedSet] at hd
  refine ⟨d, hd.1, ?_⟩
  have e1 : x * d⁻¹ * x⁻¹ = d := by
    rw [show x * d⁻¹ * x⁻¹ = (x * d * x⁻¹)⁻¹ by group, hd.2, inv_inv]
  have key : d * x * d⁻¹ = k * x * k⁻¹ := by
    calc d * x * d⁻¹ = d * (x * d⁻¹ * x⁻¹) * x := by group
      _ = d ^ 2 * x := by rw [e1, pow_two]
      _ = k * x * k⁻¹ := by rw [hd2]; group
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc d⁻¹ * k * x = d⁻¹ * (k * x * k⁻¹) * k := by group
    _ = d⁻¹ * (d * x * d⁻¹) * k := by rw [key]
    _ = x * (d⁻¹ * k) := by group

private theorem eq_one_of_mul_self_eq_one_of_odd {Y : Subgroup G} (hY : Odd (Nat.card Y))
    {b : G} (hb : b ∈ Y) (h : b * b = 1) : b = 1 := by
  have h1 : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have h2 : Odd (orderOf b) := hY.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hb)
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at h2
    exact absurd h2 (by decide)

private theorem exists_mem_inv_mul_mem_centralizer_of_coprime [Finite G] {p : ℕ} [Fact p.Prime]
    {P W : Subgroup G} (hP : IsPGroup p P) (hW : Nat.Coprime p (Nat.card W))
    (hPW : P ≤ Subgroup.normalizer (W : Set G)) {g : G}
    (hg : ∀ a ∈ P, a * g * a⁻¹ * g⁻¹ ∈ W) :
    ∃ w ∈ W, w⁻¹ * g ∈ Subgroup.centralizer (P : Set G) := by
  have hbot : W ⊓ P = ⊥ := by rw [inf_comm]; exact inf_eq_bot_of_isPGroup_of_coprime hP hW
  have hcomm : ∀ a ∈ P, g * a * g⁻¹ * a⁻¹ ∈ W := by
    intro a ha
    have := W.inv_mem (hg a ha)
    rwa [show (a * g * a⁻¹ * g⁻¹)⁻¹ = g * a * g⁻¹ * a⁻¹ by group] at this
  have hcard : Nat.card (W ⊔ P : Subgroup G) = Nat.card W * Nat.card P := by
    have h := card_sup_mul_card_inf_of_le_normalizer hPW
    rwa [hbot, Subgroup.card_bot, mul_one] at h
  have hPX : P ≤ W ⊔ P := le_sup_right
  have hsyl : IsSylowOf p P (W ⊔ P) := by
    rw [isSylowOf_iff]
    refine ⟨hPX, hP, ?_⟩
    have h := Subgroup.relIndex_mul_card P (W ⊔ P)
    rw [inf_eq_left.mpr hPX, hcard] at h
    have hidx : P.relIndex (W ⊔ P) = Nat.card W :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos h
    rw [hidx]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hW
  have hP'X : P.map (MulAut.conj g).toMonoidHom ≤ W ⊔ P := by
    rintro _ ⟨a, ha, rfl⟩
    change g * a * g⁻¹ ∈ W ⊔ P
    rw [show g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a by group]
    exact Subgroup.mul_mem_sup (hcomm a ha) ha
  have hsyl' : IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) (W ⊔ P) := by
    refine isSylowOf_of_card hP'X ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hsyl.card_eq]
  obtain ⟨k, hk, hconj⟩ := hsyl.exists_mem_conj hsyl'
  obtain ⟨w, hw, a₀, ha₀, rfl⟩ := exists_mul_of_mem_sup hPW hk
  refine ⟨w, hw, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 : w⁻¹ * g * a * (w⁻¹ * g)⁻¹ ∈ P := by
    have hga : g * a * g⁻¹ ∈ P.map (MulAut.conj g).toMonoidHom := ⟨a, ha, rfl⟩
    have h0 := (hconj _).mp hga
    have h2 := P.mul_mem (P.mul_mem ha₀ h0) (P.inv_mem ha₀)
    convert h2 using 1
    group
  have h2 : w⁻¹ * g * a * (w⁻¹ * g)⁻¹ * a⁻¹ ∈ W := by
    have e : w⁻¹ * g * a * (w⁻¹ * g)⁻¹ * a⁻¹ =
        w⁻¹ * (g * a * g⁻¹ * a⁻¹) * (a * w * a⁻¹) := by group
    rw [e]
    exact W.mul_mem (W.mul_mem (W.inv_mem hw) (hcomm a ha))
      (conj_mem_of_mem_normalizer (hPW ha) hw)
  have h3 : w⁻¹ * g * a * (w⁻¹ * g)⁻¹ * a⁻¹ ∈ P := P.mul_mem h1 (P.inv_mem ha)
  have h4 : w⁻¹ * g * a * (w⁻¹ * g)⁻¹ * a⁻¹ = 1 := by
    have h5 : w⁻¹ * g * a * (w⁻¹ * g)⁻¹ * a⁻¹ ∈ W ⊓ P := ⟨h2, h3⟩
    rw [hbot] at h5
    exact h5
  have h6 : w⁻¹ * g * a * (w⁻¹ * g)⁻¹ = a := mul_inv_eq_one.mp h4
  rw [mul_inv_eq_iff_eq_mul] at h6
  calc a * (w⁻¹ * g) = w⁻¹ * g * a := h6.symm

private theorem conj_mul_conj_inv_mem_of_inv_mul_mem_sup {T Z : Subgroup G}
    (hTZ : T ≤ Subgroup.normalizer (Z : Set G)) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    {g n : G} (hnZ : n ∈ Subgroup.normalizer (Z : Set G)) (hy : n⁻¹ * g ∈ T ⊔ Z) {t : G}
    (ht : t ∈ T) : g * t * g⁻¹ * (n * t * n⁻¹)⁻¹ ∈ Z := by
  obtain ⟨t', ht', z, hz, he⟩ := exists_mul_of_mem_sup' hTZ hy
  have hg : g = n * (t' * z) := by rw [← he]; group
  subst hg
  have h1 : z * t * z⁻¹ * t⁻¹ ∈ Z := by
    have h0 : t * z⁻¹ * t⁻¹ ∈ Z := conj_mem_of_mem_normalizer (hTZ ht) (Z.inv_mem hz)
    have h2 := Z.mul_mem hz h0
    simpa [mul_assoc] using h2
  have h2 := conj_mem_of_mem_normalizer hnZ (conj_mem_of_mem_normalizer (hTZ ht') h1)
  have hc : t' * t = t * t' := hT t' ht' t ht
  have e : t'⁻¹ * t⁻¹ = t⁻¹ * t'⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hc]
  have e2 : n * (t' * z) * t * (n * (t' * z))⁻¹ * (n * t * n⁻¹)⁻¹ =
      n * (t' * (z * t * z⁻¹ * t⁻¹) * t'⁻¹) * n⁻¹ := by
    calc n * (t' * z) * t * (n * (t' * z))⁻¹ * (n * t * n⁻¹)⁻¹
        = n * t' * z * t * z⁻¹ * (t'⁻¹ * t⁻¹) * n⁻¹ := by group
      _ = n * t' * z * t * z⁻¹ * (t⁻¹ * t'⁻¹) * n⁻¹ := by rw [e]
      _ = n * (t' * (z * t * z⁻¹ * t⁻¹) * t'⁻¹) * n⁻¹ := by group
  rw [e2]
  exact h2

private theorem pow_three_mem_centralizer_of_agree {T Z : Subgroup G}
    (hTZ : T ≤ Subgroup.normalizer (Z : Set G)) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hTZb : T ⊓ Z = ⊥) {g n : G} (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hnZ : n ∈ Subgroup.normalizer (Z : Set G)) (hnT : n ∈ Subgroup.normalizer (T : Set G))
    (hy : n⁻¹ * g ∈ T ⊔ Z) (h3 : ∀ t ∈ T, g ^ 3 * t * (g ^ 3)⁻¹ * t⁻¹ ∈ Z)
    (h1 : ∃ t ∈ T, g * t * g⁻¹ * t⁻¹ ∉ Z) :
    n ^ 3 ∈ Subgroup.centralizer (T : Set G) ∧ n ∉ Subgroup.centralizer (T : Set G) := by
  have hpow : ∀ k : ℕ, ∀ t ∈ T, g ^ k * t * (g ^ k)⁻¹ * (n ^ k * t * (n ^ k)⁻¹)⁻¹ ∈ Z := by
    intro k
    induction k with
    | zero => intro t _; simp
    | succ k ih =>
      intro t ht
      have htk : n ^ k * t * (n ^ k)⁻¹ ∈ T :=
        conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).pow_mem hnT k) ht
      have hb := conj_mul_conj_inv_mem_of_inv_mul_mem_sup hTZ hT hnZ hy htk
      have h0 := Z.mul_mem (conj_mem_of_mem_normalizer hgZ (ih t ht)) hb
      convert h0 using 1
      rw [pow_succ', pow_succ']
      group
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hZ : n ^ 3 * t * (n ^ 3)⁻¹ * t⁻¹ ∈ Z := by
      have h0 := Z.mul_mem (Z.inv_mem (hpow 3 t ht)) (h3 t ht)
      convert h0 using 1
      group
    have hTm : n ^ 3 * t * (n ^ 3)⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem (conj_mem_of_mem_normalizer
        ((Subgroup.normalizer (T : Set G)).pow_mem hnT 3) ht) (T.inv_mem ht)
    have h0 : n ^ 3 * t * (n ^ 3)⁻¹ * t⁻¹ ∈ T ⊓ Z := ⟨hTm, hZ⟩
    rw [hTZb, Subgroup.mem_bot] at h0
    have h5 : n ^ 3 * t * (n ^ 3)⁻¹ = t := mul_inv_eq_one.mp h0
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5.symm
  · intro hn
    obtain ⟨t, ht, hnot⟩ := h1
    apply hnot
    have h0 := hpow 1 t ht
    have hnt : n * t * n⁻¹ = t := by
      rw [mul_inv_eq_iff_eq_mul]
      exact ((Subgroup.mem_centralizer_iff.mp hn) t ht).symm
    simpa [hnt] using h0

private theorem mem_centralizer_of_stabilizes {X Y : Subgroup G} {t : G} (ht : t * t = 1)
    (hY : Odd (Nat.card Y)) (hXY : ∀ a ∈ X, t * a * t⁻¹ * a⁻¹ ∈ Y)
    (htY : t ∈ Subgroup.centralizer (Y : Set G)) : t ∈ Subgroup.centralizer (X : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  set b := t * a * t⁻¹ * a⁻¹ with hbdef
  have hb : b ∈ Y := hXY a ha
  have htb : t * b * t⁻¹ = b := by
    rw [mul_inv_eq_iff_eq_mul]
    exact ((Subgroup.mem_centralizer_iff.mp htY) b hb).symm
  have hta : t * a * t⁻¹ = b * a := by rw [hbdef]; group
  have hbb : b * b = 1 := by
    have e1 : a = t * (t * a * t⁻¹) * t⁻¹ := by
      rw [show t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t * t)⁻¹ by group, ht]
      group
    have e2 : t * (t * a * t⁻¹) * t⁻¹ = b * b * a := by
      rw [hta, show t * (b * a) * t⁻¹ = (t * b * t⁻¹) * (t * a * t⁻¹) by group, htb, hta]
      group
    have e3 : a = b * b * a := e1.trans e2
    have e4 := congrArg (· * a⁻¹) e3
    simpa using e4.symm
  have hb1 : b = 1 := eq_one_of_mul_self_eq_one_of_odd hY hb hbb
  have h5 : t * a * t⁻¹ = a := by rw [hta, hb1, one_mul]
  rw [mul_inv_eq_iff_eq_mul] at h5
  exact h5.symm

private theorem mul_mem_centralizer_of_odd_of_two {X : Subgroup G} {o c : G}
    (ho : Odd (orderOf o)) (hoX : o ∈ Subgroup.normalizer (X : Set G))
    (hc : c ∈ Subgroup.centralizer (X : Set G)) {k : ℕ} (hd : (o * c) ^ (2 ^ k) = 1) :
    o * c ∈ Subgroup.centralizer (X : Set G) := by
  have hagree : ∀ m : ℕ, ∀ x ∈ X, (o * c) ^ m * x * ((o * c) ^ m)⁻¹ = o ^ m * x * (o ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x _; simp
    | succ m ih =>
      intro x hx
      have hy : o ^ m * x * (o ^ m)⁻¹ ∈ X :=
        conj_mem_of_mem_normalizer ((Subgroup.normalizer (X : Set G)).pow_mem hoX m) hx
      have hcy : c * (o ^ m * x * (o ^ m)⁻¹) * c⁻¹ = o ^ m * x * (o ^ m)⁻¹ := by
        rw [mul_inv_eq_iff_eq_mul]
        exact ((Subgroup.mem_centralizer_iff.mp hc) _ hy).symm
      calc (o * c) ^ (m + 1) * x * ((o * c) ^ (m + 1))⁻¹
          = (o * c) * ((o * c) ^ m * x * ((o * c) ^ m)⁻¹) * (o * c)⁻¹ := by
            rw [pow_succ', mul_inv_rev, mul_inv_rev]; simp only [mul_assoc]
        _ = o * (c * (o ^ m * x * (o ^ m)⁻¹) * c⁻¹) * o⁻¹ := by
            rw [ih x hx, mul_inv_rev]; simp only [mul_assoc]
        _ = o ^ (m + 1) * x * (o ^ (m + 1))⁻¹ := by
            rw [hcy, pow_succ', mul_inv_rev]; simp only [mul_assoc]
  have ho2 : o ^ (2 ^ k) ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h0 := hagree (2 ^ k) x hx
    rw [hd, one_mul, inv_one, mul_one] at h0
    have h5 : o ^ (2 ^ k) * x * (o ^ (2 ^ k))⁻¹ = x := h0.symm
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5.symm
  have hcop : Nat.Coprime (2 ^ k) (orderOf o) := (Nat.coprime_two_left.mpr ho).pow_left k
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hoC : o ∈ Subgroup.centralizer (X : Set G) := by
    rw [← hm]
    exact Subgroup.pow_mem _ ho2 m
  exact Subgroup.mul_mem _ hoC hc

private theorem isPGroup_sup_of_le_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    {A B : Subgroup G} (hA : IsPGroup p A) (hB : IsPGroup p B)
    (h : B ≤ Subgroup.normalizer (A : Set G)) : IsPGroup p (A ⊔ B : Subgroup G) := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hA
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hB
  have hdvd : Nat.card (A ⊔ B : Subgroup G) ∣ p ^ (a + b) := by
    rw [pow_add, ← ha, ← hb, ← card_sup_mul_card_inf_of_le_normalizer h]
    exact Dvd.intro _ rfl
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  exact IsPGroup.of_card hc

private theorem mul_self_eq_one_of_kleinFour {T₁ : Subgroup G} (hT₁ : IsKleinFour T₁) {t : G}
    (ht : t ∈ T₁) : t * t = 1 := by
  have h := Monoid.pow_exponent_eq_one (⟨t, ht⟩ : T₁)
  rw [IsKleinFour.exponent_two] at h
  have h' := congrArg Subtype.val h
  simpa [pow_two] using h'

private theorem inf_centralizer_le_sup_pPrimeCoreIn [Finite G] {r : ℕ} [Fact r.Prime]
    {O U : Subgroup G} (hO : Odd (Nat.card O)) (hU : IsSylowOf r U O)
    (hUn : O ≤ Subgroup.normalizer (U : Set G)) :
    O ⊓ Subgroup.centralizer (U : Set G) ≤ U ⊔ pPrimeCoreIn r O := by
  have hUO : U ≤ O := hU.le
  set U' : Subgroup O := U.subgroupOf O with hU'def
  have hU'n : U'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUO).mpr hUn
  have hU'p : IsPGroup r U' := hU.isPGroup.comap_subtype
  have hU'syl : IsSylowOf r U' (⊤ : Subgroup O) := by
    rw [← isSylowOf_map_subtype_iff O, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUO,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hU
  have hU'X : U' ≤ CFSG.Op_p'p r O := by
    apply le_Op_p'p_of_normal hU'n
    intro x hx
    obtain ⟨k, hk⟩ := hU'p ⟨x, hx⟩
    refine ⟨k, ?_⟩
    have hk' : x ^ r ^ k = 1 := congrArg Subtype.val hk
    rw [hk']
    exact Subgroup.one_mem _
  have hsyl : IsSylowOf r U' (CFSG.Op_p'p r O) := hU'syl.of_le hU'X le_top
  obtain ⟨Tsyl, hTsyl⟩ := hsyl
  have hsolv : Group.IsSolvable O := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hO
  have hHH := CFSG.centralizer_sylow_subgroup_le_op_p_prime_p_of_solvable hsolv r Tsyl
  rw [hTsyl] at hHH
  set N := CFSG.pPrimeCore r O with hNdef
  set Y : Subgroup O := U' ⊔ N with hYdef
  have hYn : Y.Normal := Subgroup.sup_normal U' N
  have hNX : N ≤ CFSG.Op_p'p r O := pPrimeCore_le_Op_p'p
  have hXY : CFSG.Op_p'p r O ≤ Y := by
    have hXnorm : CFSG.Op_p'p r O ≤ Subgroup.normalizer (Y : Set O) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hYn]
      exact le_top
    have h1 : Y.relIndex (CFSG.Op_p'p r O ⊔ Y) = Y.relIndex (CFSG.Op_p'p r O) :=
      relIndex_sup_right_of_le_normalizer hXnorm
    have h2 : Y.relIndex (CFSG.Op_p'p r O) ∣ N.relIndex (CFSG.Op_p'p r O) :=
      Subgroup.relIndex_dvd_of_le_left _ le_sup_right
    have h3 : IsPGroup r ((CFSG.Op_p'p r O).map (QuotientGroup.mk' N)) := by
      refine (CFSG.pCore_isPGroup (p := r) (G := O ⧸ N)).to_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp h3
    have h4 : N.relIndex (CFSG.Op_p'p r O) = r ^ a := by
      rw [← ha, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
    rw [h4] at h2
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow (Fact.out : r.Prime)).mp h2
    have h5 : Y.relIndex (CFSG.Op_p'p r O ⊔ Y) ∣ U'.index :=
      (Subgroup.relIndex_dvd_index_of_le le_sup_right).trans (Subgroup.index_dvd_of_le le_sup_left)
    have h6 : ¬ r ∣ U'.index := by
      have := (isSylowOf_iff.mp hU'syl).2.2
      rwa [Subgroup.relIndex_top_right] at this
    have hb0 : b = 0 := by
      by_contra hb0
      apply h6
      rw [h1, hb] at h5
      exact (dvd_pow_self r hb0).trans h5
    rw [hb, hb0, pow_zero] at h1
    have h7 : CFSG.Op_p'p r O ⊔ Y ≤ Y := Subgroup.relIndex_eq_one.mp (h1.trans rfl)
    exact le_sup_left.trans h7
  intro c hc
  obtain ⟨hcO, hcU⟩ := Subgroup.mem_inf.mp hc
  have hc' : (⟨c, hcO⟩ : O) ∈ Subgroup.centralizer (U' : Set O) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hcU) u hu)
  have hmem := Subgroup.mem_map_of_mem O.subtype (hXY (hHH hc'))
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUO] at hmem
  exact hmem

private theorem exists_surjective_restrict {Q : Type*} [Group Q] {L O M : Subgroup G}
    (ψ : L →* Q) (hψ : Function.Surjective ψ) (hker : ψ.ker = O.subgroupOf L) (hOL : O ≤ L)
    (hML : M ≤ L) (hMO : M ≤ Subgroup.normalizer (O : Set G)) (hsup : L ≤ O ⊔ M) :
    ∃ ψ' : M →* Q, Function.Surjective ψ' ∧ ψ'.ker = (M ⊓ O).subgroupOf M := by
  refine ⟨ψ.comp (Subgroup.inclusion hML), ?_, ?_⟩
  · intro z
    obtain ⟨l, rfl⟩ := hψ z
    obtain ⟨o, ho, m, hm, hlm⟩ := exists_mul_of_mem_sup hMO (hsup l.2)
    refine ⟨⟨m, hm⟩, ?_⟩
    have hoK : (⟨o, hOL ho⟩ : L) ∈ ψ.ker := by rw [hker]; exact ho
    have e : (Subgroup.inclusion hML ⟨m, hm⟩ : L) = (⟨o, hOL ho⟩ : L)⁻¹ * l := by
      apply Subtype.ext
      simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hlm]
      group
    rw [MonoidHom.comp_apply, e, map_mul, map_inv, MonoidHom.mem_ker.mp hoK, inv_one, one_mul]
  · ext m
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact ⟨fun h => ⟨m.2, h⟩, fun h => h.2⟩

private theorem isSylowOf_sup_of_coprime [Finite G] {p : ℕ} [Fact p.Prime] {P W : Subgroup G}
    (hP : IsPGroup p P) (hW : Nat.Coprime p (Nat.card W))
    (hPW : P ≤ Subgroup.normalizer (W : Set G)) : IsSylowOf p P (W ⊔ P) := by
  have hbot : W ⊓ P = ⊥ := by rw [inf_comm]; exact inf_eq_bot_of_isPGroup_of_coprime hP hW
  have hcard : Nat.card (W ⊔ P : Subgroup G) = Nat.card W * Nat.card P := by
    have h := card_sup_mul_card_inf_of_le_normalizer hPW
    rwa [hbot, Subgroup.card_bot, mul_one] at h
  have hPX : P ≤ W ⊔ P := le_sup_right
  rw [isSylowOf_iff]
  refine ⟨hPX, hP, ?_⟩
  have h := Subgroup.relIndex_mul_card P (W ⊔ P)
  rw [inf_eq_left.mpr hPX, hcard] at h
  have hidx : P.relIndex (W ⊔ P) = Nat.card W := Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  rw [hidx]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hW

private theorem normalizer_le_normalizer_pPrimeCoreIn (r : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (pPrimeCoreIn r X : Set G) := by
  intro g hg
  have hchar : ((pPrimeCoreIn r X).subgroupOf X).Characteristic := by
    have e : (pPrimeCoreIn r X).subgroupOf X = CFSG.pPrimeCore r X := by
      rw [pPrimeCoreIn, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    rw [e]
    infer_instance
  exact mem_normalizer_of_characteristic (pPrimeCoreIn_le r X) hchar hg

private theorem coprime_card_pPrimeCoreIn [Finite G] {r : ℕ} [Fact r.Prime] (X : Subgroup G) :
    Nat.Coprime r (Nat.card (pPrimeCoreIn r X)) := by
  rw [pPrimeCoreIn, Subgroup.card_map_of_injective X.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

private theorem sup_inf_eq_of_le_normalizer' {A B C : Subgroup G} (hAC : A ≤ C)
    (hA : A ≤ Subgroup.normalizer (B : Set G)) : (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx, hxC⟩ := Subgroup.mem_inf.mp hx
    have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hA] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    have hbC : b ∈ C := by
      have := C.mul_mem (C.inv_mem (hAC ha)) hxC
      simpa using this
    exact Subgroup.mul_mem_sup ha ⟨hb, hbC⟩
  · exact sup_le (le_inf le_sup_left hAC) (inf_le_inf_right C le_sup_right)

private theorem oddCoreIn_eq_inf_of_le_sup [Finite G] {H K : Subgroup G} (hKH : K ≤ H)
    (hsup : H ≤ oddCoreIn H ⊔ K) : oddCoreIn K = oddCoreIn H ⊓ K := by
  have hKO : K ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
    hKH.trans (le_normalizer_oddCoreIn H)
  apply le_antisymm
  · refine le_inf ?_ (oddCoreIn_le K)
    have hodd : Odd (Nat.card (oddCoreIn H ⊔ oddCoreIn K : Subgroup G)) :=
      odd_card_sup_of_le_normalizer_of_odd ((oddCoreIn_le K).trans hKO) (odd_card_oddCoreIn H)
        (odd_card_oddCoreIn K)
    have hnorm : H ≤ Subgroup.normalizer ((oddCoreIn H ⊔ oddCoreIn K : Subgroup G) : Set G) := by
      refine hsup.trans (sup_le ?_ ?_)
      · exact fun o ho => Subgroup.le_normalizer (Subgroup.mem_sup_left ho)
      · exact (le_inf hKO (le_normalizer_oddCoreIn K)).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact le_sup_right.trans
      (le_oddCoreIn (sup_le (oddCoreIn_le H) ((oddCoreIn_le K).trans hKH)) hnorm hodd)
  · exact le_oddCoreIn inf_le_right
      ((le_inf hKO Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf)
      ((odd_card_oddCoreIn H).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))

private theorem le_oddCoreIn_sup_inf_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    {H U₀ : Subgroup G} (hU₀ : IsSylowOf p U₀ (oddCoreIn H)) :
    H ≤ oddCoreIn H ⊔ (H ⊓ Subgroup.normalizer (U₀ : Set G)) := by
  intro h hh
  obtain ⟨n, hn, k, hk, rfl⟩ :=
    exists_mem_normalizer_mul_of_isSylowOf hU₀ (le_normalizer_oddCoreIn H hh)
  have hnH : n ∈ H := by
    have := H.mul_mem hh (H.inv_mem (oddCoreIn_le H hk))
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hnH, hn⟩) (Subgroup.mem_sup_left hk)

private theorem le_normalizer_commutator_self {M A : Subgroup G}
    (h : A ≤ Subgroup.normalizer (M : Set G)) :
    A ≤ Subgroup.normalizer ((⁅M, M⁆ : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (h ha)]

private theorem commutator_self_le (M : Subgroup G) : ⁅M, M⁆ ≤ M :=
  Subgroup.commutator_le.mpr fun _ ha _ hb =>
    M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)

private theorem le_normalizer_solvRadIn (H : Subgroup G) :
    H ≤ Subgroup.normalizer (solvRadIn H : Set G) := by
  have : (CFSG.solvableRadical H).Normal := CFSG.ABGLocalTools.solvableRadical_normal
  exact le_normalizer_map_subtype H _

private theorem mem_centralizer_of_isPGroup_fixingSubgroup [Finite G] {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) {U : Subgroup G} {D₁ : Subgroup U}
    (hfix : IsPGroup r (fixingSubgroup (MulAut U) (D₁ : Set U))) {y : G}
    (hyU : y ∈ Subgroup.normalizer (U : Set G)) {k : ℕ} (hy2 : y ^ (2 ^ k) = 1)
    (hyD : y ∈ Subgroup.centralizer ((D₁.map U.subtype : Subgroup G) : Set G)) :
    y ∈ Subgroup.centralizer (U : Set G) := by
  have hUy : U.map (MulAut.conj y).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyU
  let φ : MulAut U := ((MulAut.conj y).subgroupMap U).trans (MulEquiv.subgroupCongr hUy)
  have hφ : ∀ u : U, ((φ u : U) : G) = y * u * y⁻¹ := fun _ => rfl
  have hφpow : ∀ m : ℕ, ∀ u : U, (((φ ^ m) u : U) : G) = y ^ m * u * (y ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro u; simp
    | succ m ih =>
      intro u
      rw [pow_succ, MulAut.mul_apply, ih, hφ, pow_succ]
      group
  have hφfix : φ ∈ fixingSubgroup (MulAut U) (D₁ : Set U) := by
    rw [mem_fixingSubgroup_iff]
    intro d hd
    apply Subtype.ext
    change ((φ d : U) : G) = d
    rw [hφ]
    have h1 := (Subgroup.mem_centralizer_iff.mp hyD) (d : G) ⟨d, hd, rfl⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  have hφ2 : φ ^ (2 ^ k) = 1 := by
    ext u
    rw [hφpow, hy2, one_mul, inv_one, mul_one]
    rfl
  obtain ⟨j, hj⟩ := hfix ⟨φ, hφfix⟩
  have hj' : φ ^ (r ^ j) = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hord : orderOf φ = 1 := by
    have h1 : orderOf φ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hφ2
    have h2 : orderOf φ ∣ r ^ j := orderOf_dvd_of_pow_eq_one hj'
    have hcop : Nat.Coprime (2 ^ k) (r ^ j) :=
      Nat.Coprime.pow k j ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hr2))
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rw [orderOf_eq_one_iff] at hord
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have h1 : ((φ ⟨u, hu⟩ : U) : G) = u := by rw [hord]; rfl
  rw [hφ] at h1
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

private theorem lt_inf_normalizer_of_lt [Finite G] {r : ℕ} [Fact r.Prime] {R₀ R : Subgroup G}
    (hR : IsPGroup r R) (hlt : R₀ < R) : R₀ < R ⊓ Subgroup.normalizer (R₀ : Set G) := by
  have hle : R₀ ≤ R := hlt.le
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  have hlt' : R₀.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hlt.ne
    apply le_antisymm hle
    intro y hy
    have : (⟨y, hy⟩ : R) ∈ R₀.subgroupOf R := htop ▸ Subgroup.mem_top _
    exact this
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := R) _ hlt'
  rw [← Subgroup.subgroupOf_normalizer_eq hle] at hnorm
  obtain ⟨⟨n, hnR⟩, hnN, hnF⟩ := IsConcreteLE.exists_of_lt hnorm
  refine lt_of_le_of_ne (le_inf hle Subgroup.le_normalizer) fun heq => hnF ?_
  have : n ∈ R ⊓ Subgroup.normalizer (R₀ : Set G) := ⟨hnR, hnN⟩
  rw [← heq] at this
  exact this

private theorem semidihedral_exists_noncomm {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : CFSG.Open.SemidihedralGroup n, a ^ 2 ≠ 1 ∧ b ^ 2 ≠ 1 ∧ a * b ≠ b * a := by
  have h3 : 3 ≤ n := by omega
  refine ⟨CFSG.Semidihedral.element n h3 1 0, CFSG.Semidihedral.element n h3 1 1, ?_, ?_, ?_⟩
  · intro h
    rw [CFSG.Semidihedral.element_rotation_pow, CFSG.Semidihedral.element_eq_one_iff] at h
    have h2 : ((2 : ℕ) : ZMod (CFSG.Semidihedral.modulus n)) = 0 := by
      rw [← h.1, two_nsmul]; norm_num
    rw [ZMod.natCast_eq_zero_iff] at h2
    have h4 : 4 ≤ CFSG.Semidihedral.modulus n := by
      rw [CFSG.Semidihedral.modulus]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · intro h
    rw [CFSG.Semidihedral.element_reflection_sq, CFSG.Semidihedral.element_eq_one_iff,
      mul_one] at h
    exact CFSG.Semidihedral.half_residue_ne_zero n h3 h.1
  · intro h
    rw [CFSG.Semidihedral.element_rotation_mul, CFSG.Semidihedral.element_reflection_mul,
      CFSG.Semidihedral.element_eq_iff, mul_one] at h
    exact CFSG.Semidihedral.twist_ne_one n hn (add_left_cancel h.1).symm

private theorem wreath_exists_noncomm {n : ℕ} (hn : 2 ≤ n) :
    ∃ a b : CFSG.Wreathed.Wreath (2 ^ n), a ^ 2 ≠ 1 ∧ b ^ 2 ≠ 1 ∧ a * b ≠ b * a := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : Fact (1 < 2 ^ n) := ⟨by omega⟩
  have hinj : ∀ a b c d : ZMod (2 ^ n), ∀ e f : ZMod 2,
      CFSG.Wreathed.element _ a b e = CFSG.Wreathed.element _ c d f →
        a = c ∧ b = d ∧ e = f := by
    intro a b c d e f h
    have h' := @CFSG.Wreathed.element_injective (2 ^ n) (a, b, e) (c, d, f) h
    simp only [Prod.mk.injEq] at h'
    exact h'
  refine ⟨CFSG.Wreathed.element _ 1 0 0, CFSG.Wreathed.element _ 1 0 1, ?_, ?_, ?_⟩
  · intro h
    rw [CFSG.Wreathed.element_base_pow, ← CFSG.Wreathed.element_zero] at h
    have h' := (hinj _ _ _ _ _ _ h).1
    have h2 : ((2 : ℕ) : ZMod (2 ^ n)) = 0 := by rw [← h', two_nsmul]; norm_num
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · intro h
    rw [CFSG.Wreathed.element_swap_sq, ← CFSG.Wreathed.element_zero] at h
    have h' := (hinj _ _ _ _ _ _ h).1
    rw [add_zero] at h'
    exact one_ne_zero h'
  · intro h
    rw [CFSG.Wreathed.element_base_mul, CFSG.Wreathed.element_swap_mul] at h
    have h' := (hinj _ _ _ _ _ _ h).2.1
    rw [add_zero, zero_add] at h'
    exact zero_ne_one h'

private theorem comm_of_le_dihedralSylow {A : Type*} [Group A] [Finite A] {K₁ X : Subgroup A}
    (hK₁ : CFSG.GorensteinWalter.HasDihedralSylowTwo K₁) (hXK : X ≤ K₁) (hX : IsPGroup 2 X)
    {a b : A} (ha : a ∈ X) (hb : b ∈ X) (ha2 : a ^ 2 ≠ 1) (hb2 : b ^ 2 ≠ 1) :
    a * b = b * a := by
  have hX' : IsPGroup 2 (X.subgroupOf K₁) := hX.comap_subtype
  obtain ⟨S₁, hS₁⟩ := hX'.exists_le_sylow
  obtain ⟨m, -, ⟨e⟩⟩ := hK₁ S₁
  have hmem : ∀ c (hc : c ∈ X), (⟨c, hXK hc⟩ : K₁) ∈ (S₁ : Subgroup K₁) := fun c hc => hS₁ hc
  have key : ∀ c (hc : c ∈ X), c ^ 2 ≠ 1 →
      ∃ i, e ⟨⟨c, hXK hc⟩, hmem c hc⟩ = DihedralGroup.r i := by
    intro c hc hc2
    rcases h : e ⟨⟨c, hXK hc⟩, hmem c hc⟩ with i | i
    · exact ⟨i, rfl⟩
    · exfalso
      apply hc2
      have h1 : e ((⟨⟨c, hXK hc⟩, hmem c hc⟩ : S₁) ^ 2) = 1 := by
        rw [map_pow, h, pow_two, DihedralGroup.sr_mul_self]
      rw [MulEquiv.map_eq_one_iff] at h1
      have h2 := congrArg (fun x : S₁ => ((x : K₁) : A)) h1
      simpa using h2
  obtain ⟨i, hi⟩ := key a ha ha2
  obtain ⟨j, hj⟩ := key b hb hb2
  have hab : e ((⟨⟨a, hXK ha⟩, hmem a ha⟩ : S₁) * ⟨⟨b, hXK hb⟩, hmem b hb⟩) =
      e ((⟨⟨b, hXK hb⟩, hmem b hb⟩ : S₁) * ⟨⟨a, hXK ha⟩, hmem a ha⟩) := by
    rw [map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
  have h2 := congrArg (fun x : S₁ => ((x : K₁) : A)) (e.injective hab)
  simpa using h2

private theorem comm_of_le_abelianSylow {A : Type*} [Group A] [Finite A] {K₁ X : Subgroup A}
    (hK₁ : ∀ P : Sylow 2 K₁, IsMulCommutative P) (hXK : X ≤ K₁) (hX : IsPGroup 2 X)
    {a b : A} (ha : a ∈ X) (hb : b ∈ X) : a * b = b * a := by
  have hX' : IsPGroup 2 (X.subgroupOf K₁) := hX.comap_subtype
  obtain ⟨S₁, hS₁⟩ := hX'.exists_le_sylow
  have hmem : ∀ c (hc : c ∈ X), (⟨c, hXK hc⟩ : K₁) ∈ (S₁ : Subgroup K₁) := fun c hc => hS₁ hc
  have h1 := (hK₁ S₁).is_comm.comm (⟨⟨a, hXK ha⟩, hmem a ha⟩ : S₁) ⟨⟨b, hXK hb⟩, hmem b hb⟩
  have h2 := congrArg (fun x : S₁ => ((x : K₁) : A)) h1
  simpa using h2

private theorem exists_noncomm_of_isQDGroup [Finite G] {Y : Subgroup G} (hY : IsQDGroup Y) :
    ∃ X : Subgroup G, X ≤ Y ∧ IsPGroup 2 X ∧
      ∃ a ∈ X, ∃ b ∈ X, a ^ 2 ≠ 1 ∧ b ^ 2 ≠ 1 ∧ a * b ≠ b * a := by
  obtain ⟨h, hh⟩ := hY.sylow
  obtain ⟨S⟩ : Nonempty (Sylow 2 Y) := inferInstance
  obtain ⟨M, _, φ, hφ, a₀, b₀, ha₀, hb₀, hab₀⟩ : ∃ (M : Type) (_ : Group M) (φ : M →* S),
      Function.Injective φ ∧ ∃ a₀ b₀ : M, a₀ ^ 2 ≠ 1 ∧ b₀ ^ 2 ≠ 1 ∧ a₀ * b₀ ≠ b₀ * a₀ := by
    rcases hh with ⟨-, n, hn, hSD⟩ | ⟨hn, hW⟩
    · obtain ⟨f⟩ := hSD S
      obtain ⟨a₀, b₀, h1, h2, h3⟩ := semidihedral_exists_noncomm hn
      exact ⟨_, _, f.toMonoidHom, f.injective, a₀, b₀, h1, h2, h3⟩
    · obtain ⟨g⟩ := hW S
      obtain ⟨a₀, b₀, h1, h2, h3⟩ := wreath_exists_noncomm hn
      exact ⟨_, _, g.symm.toMonoidHom, g.symm.injective, a₀, b₀, h1, h2, h3⟩
  set ψ : M →* G := Y.subtype.comp ((S : Subgroup Y).subtype.comp φ) with hψdef
  have hψ : Function.Injective ψ :=
    Y.subtype_injective.comp ((Subgroup.subtype_injective _).comp hφ)
  refine ⟨(S : Subgroup Y).map Y.subtype, Subgroup.map_subtype_le _, S.isPGroup'.map _, ψ a₀,
    ⟨φ a₀, (φ a₀).2, rfl⟩, ψ b₀, ⟨φ b₀, (φ b₀).2, rfl⟩, ?_, ?_, ?_⟩
  · rw [← map_pow]
    exact fun h1 => ha₀ (hψ (h1.trans (map_one ψ).symm))
  · rw [← map_pow]
    exact fun h1 => hb₀ (hψ (h1.trans (map_one ψ).symm))
  · rw [← map_mul, ← map_mul]
    exact fun h1 => hab₀ (hψ h1)

private theorem not_isQDGroup_of_le_isDGroup [Finite G] {H Y : Subgroup G} (hYH : Y ≤ H)
    (hD : IsDGroup H) : ¬ IsQDGroup Y := by
  intro hY
  obtain ⟨X, hXY, hX2, a, ha, b, hb, ha2, hb2, hab⟩ := exists_noncomm_of_isQDGroup hY
  rcases hD with ⟨hDih, -⟩ | ⟨K₀, hK₀⟩
  · exact hab (comm_of_le_dihedralSylow hDih (hXY.trans hYH) hX2 ha hb ha2 hb2)
  · have : K₀.Normal := hK₀.normal
    set K₀G := K₀.map H.subtype with hK₀G
    have hHK : H ≤ Subgroup.normalizer (K₀G : Set G) := le_normalizer_map_subtype H K₀
    have hidx : K₀G.relIndex H = 2 := by
      rw [Subgroup.relIndex, hK₀G, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      exact hK₀.index_eq_two
    have hdvd : K₀G.relIndex Y ∣ 2 := by
      rw [← relIndex_sup_right_of_le_normalizer (hYH.trans hHK), ← hidx]
      exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right
        (sup_le hYH (Subgroup.map_subtype_le _)))
    have hne2 : K₀G.relIndex Y ≠ 2 := hY.noIndexTwo (K₀G.subgroupOf Y)
    have h1 : K₀G.relIndex Y = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · exact absurd h hne2
    have hYK : Y ≤ K₀G := Subgroup.relIndex_eq_one.mp h1
    have hX'K : X.subgroupOf H ≤ K₀ := by
      intro x hx
      obtain ⟨k, hk, hkx⟩ := hYK (hXY hx)
      have hkx' : k = x := Subtype.ext hkx
      rw [← hkx']
      exact hk
    have hX'2 : IsPGroup 2 (X.subgroupOf H) := hX2.comap_subtype
    have ha' : (⟨a, hYH (hXY ha)⟩ : H) ∈ X.subgroupOf H := ha
    have hb' : (⟨b, hYH (hXY hb)⟩ : H) ∈ X.subgroupOf H := hb
    have hsq : ∀ c (hc : c ∈ H), c ^ 2 ≠ 1 → (⟨c, hc⟩ : H) ^ 2 ≠ 1 := fun c hc h h1 =>
      h (by simpa using congrArg Subtype.val h1)
    rcases hK₀.sylow with ⟨n, -, hDihK⟩ | ⟨n, -, habK⟩
    · have h2 := comm_of_le_dihedralSylow hDihK hX'K hX'2 ha' hb' (hsq a _ ha2) (hsq b _ hb2)
      exact hab (by simpa using congrArg Subtype.val h2)
    · have h2 := comm_of_le_abelianSylow habK hX'K hX'2 ha' hb'
      exact hab (by simpa using congrArg Subtype.val h2)

end General


section LinearType

variable {G : Type u} [Group G]

@[expose] def IsLinearTypeWrt (T H : Subgroup G) (q₁ : ℕ) : Prop :=
  ∃ L₁ : Subgroup G, oddCoreIn H ≤ L₁ ∧ L₁ ≤ H ∧ H ≤ Subgroup.normalizer (L₁ : Set G) ∧
    T ≤ L₁ ∧
    (∀ Y : Subgroup G, Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) → oddCoreIn H ≤ Y → T ≤ Y →
      L₁ ≤ Y) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q₁ ∧ Odd q₁ ∧
      ∃ ψ : L₁ →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = (oddCoreIn H).subgroupOf L₁

private theorem isLinearTypeWrt_of_le_sup [Finite G] {T H K : Subgroup G} {q₁ : ℕ}
    (hKH : K ≤ H) (hsup : H ≤ oddCoreIn H ⊔ K) (hOK : oddCoreIn K = oddCoreIn H ⊓ K)
    (hTK : T ≤ K) (hlin : IsLinearTypeWrt T H q₁) : IsLinearTypeWrt T K q₁ := by
  obtain ⟨L₁, hOL, hLH, hHL, hTL, hmin, F, hF, hFin, hq, hodd, ψ, hψ, hker⟩ := hlin
  have hKO : K ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
    hKH.trans (le_normalizer_oddCoreIn H)
  refine ⟨L₁ ⊓ K, ?_, inf_le_right, ?_, le_inf hTL hTK, ?_, F, hF, hFin, hq, hodd, ?_⟩
  · rw [hOK]
    exact inf_le_inf_right K hOL
  · exact (le_inf (hKH.trans hHL) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  · intro Y hYK hKY hOY hTY
    have hY'H : Y ⊔ oddCoreIn H ≤ H := sup_le (hYK.trans hKH) (oddCoreIn_le H)
    have hHY' : H ≤ Subgroup.normalizer ((Y ⊔ oddCoreIn H : Subgroup G) : Set G) := by
      refine hsup.trans (sup_le ?_ ?_)
      · exact fun o ho => Subgroup.le_normalizer (Subgroup.mem_sup_right ho)
      · exact (le_inf hKY hKO).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hL := hmin _ hY'H hHY' le_sup_right (hTY.trans le_sup_left)
    calc L₁ ⊓ K ≤ (Y ⊔ oddCoreIn H) ⊓ K := inf_le_inf_right K hL
      _ = Y ⊔ (oddCoreIn H ⊓ K) := sup_inf_eq_of_le_normalizer' hYK (hYK.trans hKO)
      _ = Y := by rw [← hOK]; exact sup_eq_left.mpr hOY
  · have hsupL : L₁ ≤ oddCoreIn H ⊔ (L₁ ⊓ K) := by
      intro l hl
      obtain ⟨o, ho, k, hk, rfl⟩ := exists_mul_of_mem_sup hKO (hsup (hLH hl))
      have hkL : k ∈ L₁ := by
        have := L₁.mul_mem (L₁.inv_mem (hOL ho)) hl
        simpa using this
      exact Subgroup.mul_mem_sup ho ⟨hkL, hk⟩
    obtain ⟨ψ', hψ', hker'⟩ := exists_surjective_restrict ψ hψ hker hOL inf_le_left
      (inf_le_right.trans hKO) hsupL
    refine ⟨ψ', hψ', ?_⟩
    have e : (L₁ ⊓ K) ⊓ oddCoreIn H = oddCoreIn H ⊓ K :=
      le_antisymm (le_inf inf_le_right (inf_le_left.trans inf_le_right))
        (le_inf (le_inf (inf_le_left.trans hOL) inf_le_right) inf_le_left)
    rw [hker', e, hOK]

private theorem exists_centralizer_section [Finite G] {T₀ K U₀ : Subgroup G} {q₁ : ℕ}
    (hT₀K : T₀ ≤ K) (hT₀U : T₀ ≤ Subgroup.centralizer (U₀ : Set G))
    (hKU : K ≤ Subgroup.normalizer (U₀ : Set G)) (hlin : IsLinearTypeWrt T₀ K q₁) :
    ∃ M : Subgroup G, M ≤ K ∧ K ≤ Subgroup.normalizer (M : Set G) ∧
      M ≤ Subgroup.centralizer (U₀ : Set G) ∧ T₀ ≤ M ∧
      oddCoreIn K ⊓ Subgroup.centralizer (U₀ : Set G) ≤ M ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q₁ ∧ Odd q₁ ∧
        ∃ ψ : M →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
          ψ.ker = (M ⊓ oddCoreIn K).subgroupOf M := by
  obtain ⟨L₁, hOL, hLK, hKL, hTL, hmin, F, hF, hFin, hq, hodd, ψ, hψ, hker⟩ := hlin
  set K₁ := K ⊓ Subgroup.centralizer (U₀ : Set G) with hK₁
  have hKK₁ : K ≤ Subgroup.normalizer (K₁ : Set G) :=
    (le_inf Subgroup.le_normalizer (hKU.trans (normalizer_le_normalizer_centralizer U₀))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hK₁O : K₁ ≤ Subgroup.normalizer (oddCoreIn K : Set G) :=
    inf_le_left.trans (le_normalizer_oddCoreIn K)
  have hLsup : L₁ ≤ K₁ ⊔ oddCoreIn K :=
    hmin _ (sup_le inf_le_left (oddCoreIn_le K))
      ((le_inf hKK₁ (le_normalizer_oddCoreIn K)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _))
      le_sup_right (le_sup_of_le_left (le_inf hT₀K hT₀U))
  refine ⟨K₁ ⊓ L₁, inf_le_left.trans inf_le_left, ?_, inf_le_left.trans inf_le_right,
    le_inf (le_inf hT₀K hT₀U) hTL, ?_, F, hF, hFin, hq, hodd, ?_⟩
  · exact (le_inf hKK₁ hKL).trans Subgroup.inf_normalizer_le_normalizer_inf
  · exact le_inf (inf_le_inf_right _ (oddCoreIn_le K)) (inf_le_left.trans hOL)
  · have hsupL : L₁ ≤ oddCoreIn K ⊔ (K₁ ⊓ L₁) := by
      intro l hl
      have hl' : l ∈ oddCoreIn K ⊔ K₁ := by rw [sup_comm]; exact hLsup hl
      obtain ⟨o, ho, k, hk, rfl⟩ := exists_mul_of_mem_sup hK₁O hl'
      have hkL : k ∈ L₁ := by
        have := L₁.mul_mem (L₁.inv_mem (hOL ho)) hl
        simpa using this
      exact Subgroup.mul_mem_sup ho ⟨hk, hkL⟩
    exact exists_surjective_restrict ψ hψ hker hOL inf_le_right (inf_le_left.trans hK₁O) hsupL

private theorem exists_automizer_element_of_le [Finite G] {r : ℕ} {T₀ K U₀ : Subgroup G}
    {q₁ : ℕ} (hT₀ : IsPGroup 2 T₀) (hT₀c : ∀ a ∈ T₀, ∀ b ∈ T₀, a * b = b * a)
    (hT₀K : T₀ ≤ K) (hT₀U : T₀ ≤ Subgroup.centralizer (U₀ : Set G))
    (hKU : K ≤ Subgroup.normalizer (U₀ : Set G)) (hlin : IsLinearTypeWrt T₀ K q₁)
    (h3 : 3 < q₁)
    (h58 : ∀ (J W A : Subgroup G) (F : Type) [Field F] [Finite F], W ≤ J →
      J ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card W) → Odd (Nat.card F) →
      3 < Nat.card F →
      (∃ ψ : J →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = W.subgroupOf J) →
      T₀ ≤ J → IsPGroup r A → A ≤ Subgroup.normalizer (J : Set G) →
      A ≤ Subgroup.normalizer (W : Set G) → A ≤ Subgroup.centralizer (T₀ : Set G) →
        ∃ g ∈ J, (∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ W) ∧
          g ∈ Subgroup.normalizer ((T₀ ⊔ W : Subgroup G) : Set G) ∧
          (∀ t ∈ T₀, g ^ 3 * t * (g ^ 3)⁻¹ * t⁻¹ ∈ W) ∧ ∃ t ∈ T₀, g * t * g⁻¹ * t⁻¹ ∉ W) :
    ∃ n ∈ K ⊓ Subgroup.centralizer (U₀ : Set G), n ∈ Subgroup.normalizer (T₀ : Set G) ∧
      n ^ 3 ∈ Subgroup.centralizer (T₀ : Set G) ∧ n ∉ Subgroup.centralizer (T₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hMK, hKM, hMU, hT₀M, -, F, hF, hFin, hq, hodd, ψ, hψ, hker⟩ :=
    exists_centralizer_section hT₀K hT₀U hKU hlin
  set Z := M ⊓ oddCoreIn K with hZdef
  have hZM : Z ≤ M := inf_le_left
  have hMZ : M ≤ Subgroup.normalizer (Z : Set G) :=
    (le_inf Subgroup.le_normalizer (hMK.trans (le_normalizer_oddCoreIn K))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hZodd : Odd (Nat.card Z) :=
    (odd_card_oddCoreIn K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨g, hgM, -, hgN, hg3, hg1⟩ := h58 M Z ⊥ F hZM hMZ hZodd (hq ▸ hodd) (hq ▸ h3)
    ⟨ψ, hψ, hker⟩ hT₀M IsPGroup.of_bot bot_le bot_le bot_le
  have hT₀Z : T₀ ≤ Subgroup.normalizer (Z : Set G) := hT₀M.trans hMZ
  have hsyl : IsSylowOf 2 T₀ (Z ⊔ T₀) :=
    isSylowOf_sup_of_coprime hT₀ (Nat.coprime_two_left.mpr hZodd) hT₀Z
  have hgN' : g ∈ Subgroup.normalizer ((Z ⊔ T₀ : Subgroup G) : Set G) := by
    rw [sup_comm]; exact hgN
  obtain ⟨n, hn, k, hk, hgnk⟩ := exists_mem_normalizer_mul_of_isSylowOf hsyl hgN'
  have hkM : k ∈ M := sup_le hZM hT₀M hk
  have hnM : n ∈ M := by
    have := M.mul_mem hgM (M.inv_mem hkM)
    rwa [hgnk, mul_inv_cancel_right] at this
  have hk' : n⁻¹ * g ∈ T₀ ⊔ Z := by
    rw [hgnk, inv_mul_cancel_left, sup_comm]; exact hk
  have hTZ : T₀ ⊓ Z = ⊥ := inf_eq_bot_of_isPGroup_two_of_odd hT₀ hZodd
  obtain ⟨hn3, hn1⟩ := pow_three_mem_centralizer_of_agree hT₀Z hT₀c hTZ (hMZ hgM) (hMZ hnM) hn
    hk' hg3 hg1
  exact ⟨n, ⟨hMK hnM, hMU hnM⟩, hn, hn3, hn1⟩

private theorem exists_automizer_element_of_ne_nine [Finite G] {r : ℕ} [Fact r.Prime]
    {T₀ K U₀ P₀ : Subgroup G} {q₁ : ℕ} (hT₀ : IsPGroup 2 T₀)
    (hT₀c : ∀ a ∈ T₀, ∀ b ∈ T₀, a * b = b * a) (hT₀K : T₀ ≤ K)
    (hKU : K ≤ Subgroup.normalizer (U₀ : Set G)) (hU₀ : IsSylowOf r U₀ (oddCoreIn K))
    (hU₀P : U₀ ≤ P₀) (hP₀ : IsPGroup r P₀) (hP₀K : P₀ ≤ K)
    (hT₀P : T₀ ≤ Subgroup.centralizer (P₀ : Set G)) (hlin : IsLinearTypeWrt T₀ K q₁)
    (h3 : 3 < q₁) (h9 : q₁ ≠ 9)
    (h56 : ∀ (M Z W : Subgroup G) (F : Type) [Field F] [Finite F], Z ≤ M → W ≤ Z →
      M ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card Z) → ⁅Z, M⁆ ≤ W →
      Odd (Nat.card F) → 3 < Nat.card F → Nat.card F ≠ 9 →
      (∃ ψ : M →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = Z.subgroupOf M) →
        ⁅M, M⁆ ⊓ Z ≤ W ∧ ⁅M, M⁆ ⊔ Z = M)
    (h58 : ∀ (J W A : Subgroup G) (F : Type) [Field F] [Finite F], W ≤ J →
      J ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card W) → Odd (Nat.card F) →
      3 < Nat.card F →
      (∃ ψ : J →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = W.subgroupOf J) →
      T₀ ≤ J → IsPGroup r A → A ≤ Subgroup.normalizer (J : Set G) →
      A ≤ Subgroup.normalizer (W : Set G) → A ≤ Subgroup.centralizer (T₀ : Set G) →
        ∃ g ∈ J, (∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ W) ∧
          g ∈ Subgroup.normalizer ((T₀ ⊔ W : Subgroup G) : Set G) ∧
          (∀ t ∈ T₀, g ^ 3 * t * (g ^ 3)⁻¹ * t⁻¹ ∈ W) ∧ ∃ t ∈ T₀, g * t * g⁻¹ * t⁻¹ ∉ W) :
    ∃ n ∈ K ⊓ Subgroup.centralizer (P₀ : Set G), n ∈ Subgroup.normalizer (T₀ : Set G) ∧
      n ^ 3 ∈ Subgroup.centralizer (T₀ : Set G) ∧ n ∉ Subgroup.centralizer (T₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₀U : T₀ ≤ Subgroup.centralizer (U₀ : Set G) :=
    hT₀P.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hU₀P))
  obtain ⟨M, hMK, hKM, hMU, hT₀M, hOUM, F, hF, hFin, hq, hodd, ψ, hψ, hker⟩ :=
    exists_centralizer_section hT₀K hT₀U hKU hlin
  set O := oddCoreIn K with hOdef
  set W := pPrimeCoreIn r O with hWdef
  set Z := M ⊓ O with hZdef
  have hOK : O ≤ K := oddCoreIn_le K
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_oddCoreIn K
  have hWO : W ≤ O := pPrimeCoreIn_le r O
  have hKW : K ≤ Subgroup.normalizer (W : Set G) :=
    hKO.trans (normalizer_le_normalizer_pPrimeCoreIn r O)
  have hWcop : Nat.Coprime r (Nat.card W) := coprime_card_pPrimeCoreIn O
  have hWodd : Odd (Nat.card W) :=
    (odd_card_oddCoreIn K).of_dvd_nat (Subgroup.card_dvd_of_le hWO)
  have hZodd : Odd (Nat.card Z) :=
    (odd_card_oddCoreIn K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hHH : O ⊓ Subgroup.centralizer (U₀ : Set G) ≤ U₀ ⊔ W :=
    inf_centralizer_le_sup_pPrimeCoreIn (odd_card_oddCoreIn K) hU₀ (hOK.trans hKU)
  have hU₀W : U₀ ≤ Subgroup.normalizer (W : Set G) := hU₀.le.trans (hOK.trans hKW)
  have hMW : M ≤ Subgroup.normalizer (W : Set G) := hMK.trans hKW
  have hMZ : M ≤ Subgroup.normalizer (Z : Set G) :=
    (le_inf Subgroup.le_normalizer (hMK.trans hKO)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hWU : W ≤ Subgroup.centralizer (U₀ : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : w * u * w⁻¹ * u⁻¹ ∈ U₀ :=
      U₀.mul_mem (conj_mem_of_mem_normalizer (hKU (hOK (hWO hw))) hu) (U₀.inv_mem hu)
    have h2 : w * u * w⁻¹ * u⁻¹ ∈ W := by
      have h0 := W.mul_mem hw (conj_mem_of_mem_normalizer (hU₀W hu) (W.inv_mem hw))
      simpa [mul_assoc] using h0
    have hbot : U₀ ⊓ W = ⊥ := inf_eq_bot_of_isPGroup_of_coprime hU₀.isPGroup hWcop
    have h3' : w * u * w⁻¹ * u⁻¹ ∈ U₀ ⊓ W := ⟨h1, h2⟩
    rw [hbot, Subgroup.mem_bot] at h3'
    have h4 : w * u * w⁻¹ = u := mul_inv_eq_one.mp h3'
    rw [mul_inv_eq_iff_eq_mul] at h4
    exact h4.symm
  have hWZ : W ≤ Z := le_inf (hOUM.trans' (le_inf hWO hWU)) hWO
  have hZMW : ⁅Z, M⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro z hz m hm
    have hzU : z ∈ U₀ ⊔ W := hHH ⟨hz.2, hMU hz.1⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_mul_of_mem_sup' hU₀W hzU
    have hmu : u * m = m * u := (Subgroup.mem_centralizer_iff.mp (hMU hm)) u hu
    have e : ⁅u * w, m⁆ = u * (w * (m * w⁻¹ * m⁻¹)) * u⁻¹ := by
      rw [commutatorElement_def]
      have hmu' : m * u⁻¹ * m⁻¹ = u⁻¹ := by
        have h0 : m * u⁻¹ = u⁻¹ * m := by
          calc m * u⁻¹ = u⁻¹ * (u * m) * u⁻¹ := by group
            _ = u⁻¹ * (m * u) * u⁻¹ := by rw [hmu]
            _ = u⁻¹ * m := by group
        rw [h0]
        group
      calc u * w * m * (u * w)⁻¹ * m⁻¹ = u * (w * (m * w⁻¹ * m⁻¹)) * (m * u⁻¹ * m⁻¹) := by
            group
        _ = u * (w * (m * w⁻¹ * m⁻¹)) * u⁻¹ := by rw [hmu']
    rw [e]
    exact conj_mem_of_mem_normalizer (hU₀W hu)
      (W.mul_mem hw (conj_mem_of_mem_normalizer (hMW hm) (W.inv_mem hw)))
  obtain ⟨hcomZ, hcomsup⟩ := h56 M Z W F inf_le_left hWZ hMW hZodd hZMW (hq ▸ hodd)
    (hq ▸ h3) (hq ▸ h9) ⟨ψ, hψ, hker⟩
  set J := ⁅M, M⁆ ⊔ W with hJdef
  have hJM : J ≤ M := sup_le (commutator_self_le M) (hWZ.trans inf_le_left)
  have hJZ : J ⊓ Z = W := by
    apply le_antisymm
    · rw [hJdef, sup_comm, sup_inf_eq_of_le_normalizer hWZ ((commutator_self_le M).trans hMW)]
      exact sup_le le_rfl hcomZ
    · exact le_inf le_sup_right hWZ
  have hMJ : M ≤ Subgroup.normalizer (J : Set G) :=
    (le_inf (le_normalizer_commutator_self Subgroup.le_normalizer) hMW).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hP₀J : P₀ ≤ Subgroup.normalizer (J : Set G) :=
    (le_inf (le_normalizer_commutator_self (hP₀K.trans hKM)) (hP₀K.trans hKW)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hMsup : M ≤ Z ⊔ J := by
    rw [← hcomsup, sup_comm]
    exact sup_le_sup_left le_sup_left Z
  obtain ⟨ψJ, hψJ, hkerJ⟩ := exists_surjective_restrict ψ hψ hker inf_le_left hJM
    (hJM.trans hMZ) hMsup
  rw [hJZ] at hkerJ
  have hT₀J : T₀ ≤ J := by
    intro t ht
    apply mem_of_coprime_orderOf_relIndex hJM hMJ (hT₀M ht)
    obtain ⟨k, hk⟩ := exists_orderOf_eq_pow_of_mem hT₀ ht
    rw [hk]
    apply Nat.Coprime.pow_left
    apply Nat.coprime_two_left.mpr
    have hidx : J.relIndex M = J.relIndex Z := by
      have e : M = Z ⊔ J := le_antisymm hMsup (sup_le inf_le_left hJM)
      rw [e]
      exact relIndex_sup_right_of_le_normalizer (inf_le_left.trans hMJ)
    rw [hidx]
    exact hZodd.of_dvd_nat (Subgroup.relIndex_dvd_card _ _)
  obtain ⟨g, hgJ, hgP, hgN, hg3, hg1⟩ := h58 J W P₀ F le_sup_right
    (hJM.trans hMW) hWodd (hq ▸ hodd) (hq ▸ h3) ⟨ψJ, hψJ, hkerJ⟩ hT₀J hP₀ hP₀J
    (hP₀K.trans hKW) (Subgroup.le_centralizer_iff.mp hT₀P)
  have hgK : g ∈ K := hMK (hJM hgJ)
  obtain ⟨w, hw, hc⟩ := exists_mem_inv_mul_mem_centralizer_of_coprime hP₀ hWcop
    (hP₀K.trans hKW) hgP
  set c := w⁻¹ * g with hcdef
  have hT₀W : T₀ ≤ Subgroup.normalizer (W : Set G) := hT₀K.trans hKW
  have hcN : c ∈ Subgroup.normalizer ((T₀ ⊔ W : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer (Subgroup.mem_sup_right hw)))
      hgN
  set X₂ := (T₀ ⊔ W) ⊓ Subgroup.centralizer (P₀ : Set G) with hX₂def
  have hcX₂ : c ∈ Subgroup.normalizer (X₂ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hcN, normalizer_le_normalizer_centralizer P₀
        (Subgroup.centralizer_le_normalizer _ hc)⟩
  have hsylW : IsSylowOf 2 T₀ (W ⊔ T₀) :=
    isSylowOf_sup_of_coprime hT₀ (Nat.coprime_two_left.mpr hWodd) hT₀W
  have hsyl : IsSylowOf 2 T₀ X₂ :=
    hsylW.of_le (le_inf le_sup_left hT₀P) (inf_le_left.trans (le_of_eq (sup_comm T₀ W)))
  obtain ⟨n, hn, y, hy, hcny⟩ := exists_mem_normalizer_mul_of_isSylowOf hsyl hcX₂
  have hnc : n = c * y⁻¹ := by rw [hcny]; group
  have hyK : y ∈ K := sup_le hT₀K (hWO.trans hOK) hy.1
  have hnK : n ∈ K := by
    rw [hnc]
    exact K.mul_mem (K.mul_mem (K.inv_mem (hOK (hWO hw))) hgK) (K.inv_mem hyK)
  have hnP : n ∈ Subgroup.centralizer (P₀ : Set G) := by
    rw [hnc]
    exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hy.2)
  have hng : n⁻¹ * g ∈ T₀ ⊔ W := by
    have e : n⁻¹ * g = y * (g⁻¹ * w * g) := by rw [hnc, hcdef]; group
    rw [e]
    refine Subgroup.mul_mem _ hy.1 (Subgroup.mem_sup_right ?_)
    have h0 := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ (hKW hgK)) hw
    simpa using h0
  have hTW : T₀ ⊓ W = ⊥ := inf_eq_bot_of_isPGroup_two_of_odd hT₀ hWodd
  obtain ⟨hn3, hn1⟩ := pow_three_mem_centralizer_of_agree hT₀W hT₀c hTW (hKW hgK) (hKW hnK) hn
    hng hg3 hg1
  exact ⟨n, ⟨hnK, hnP⟩, hn, hn3, hn1⟩

end LinearType

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

section Basic

private theorem isPGroup_two_T (hσ : σ.IsValid) : IsPGroup 2 σ.T :=
  σ.S.isPGroup'.to_le (σ.T_le_S hσ)

omit [Finite G] in
private theorem isPGroup_two_D : IsPGroup 2 σ.D :=
  σ.S.isPGroup'.to_le σ.D_le_S

private theorem T_comm (hσ : σ.IsValid) : ∀ a ∈ σ.T, ∀ b ∈ σ.T, a * b = b * a :=
  fun a ha _ hb => (Subgroup.mem_centralizer_iff.mp (σ.T_le_C hσ hb)) a ha

private theorem x₂_not_mem_centerOf_D (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) :
    σ.x₂ ∉ centerOf σ.D := by
  intro h
  rw [← hII.center_S_eq_center_D] at h
  exact hσ.x_ne_x₂ (hσ.center_involution σ.x₂ h hσ.x₂_order).symm

private theorem exists_mem_not_mem_centerOf_D_of_kleinFour (hσ : σ.IsValid)
    (hII : σ.ChapterIIFacts) {T₁ : Subgroup G} (hT₁ : IsKleinFour T₁) :
    ∃ u ∈ T₁, u ∉ centerOf σ.D := by
  by_contra hcon'
  have hcon : ∀ u ∈ T₁, u ∈ centerOf σ.D := fun u hu => by_contra fun h => hcon' ⟨u, hu, h⟩
  have hinv : ∀ u ∈ T₁, u ≠ 1 → u = σ.x := by
    intro u hu hu1
    have hu2 : orderOf u = 2 := by
      have hexp := Monoid.order_dvd_exponent (⟨u, hu⟩ : T₁)
      rw [IsKleinFour.exponent_two, Subgroup.orderOf_mk] at hexp
      rcases (Nat.dvd_prime Nat.prime_two).mp hexp with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hu1
      · exact h
    have hZ := hcon u hu
    rw [← hII.center_S_eq_center_D] at hZ
    exact hσ.center_involution u hZ hu2
  have hle : T₁ ≤ Subgroup.zpowers σ.x := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]; exact Subgroup.one_mem _
    · rw [hinv u hu hu1]; exact Subgroup.mem_zpowers _
  have hcard := Subgroup.card_le_of_le hle
  rw [IsKleinFour.card_four, Nat.card_zpowers, hσ.x_order] at hcard
  omega

private theorem prime_ne_two_of_hyp {r : ℕ} (hr : σ.HypIV7 r) : r ≠ 2 :=
  σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON

private theorem odd_card_of_isPGroup_hyp {r : ℕ} (hr : σ.HypIV7 r) {X : Subgroup G}
    (hX : IsPGroup r X) : Odd (Nat.card X) :=
  odd_card_of_isPGroup hr.prime (σ.prime_ne_two_of_hyp hr) hX

private theorem P_le_normalizer_Q {r : ℕ} (d : σ.IV7Data r) :
    d.P ≤ Subgroup.normalizer (d.Q : Set G) :=
  fun _ hp => mem_normalizer_of_characteristic d.Q_le d.Q_characteristic
    (Subgroup.le_normalizer hp)

private theorem D_le_normalizer_Q {r : ℕ} (d : σ.IV7Data r) :
    σ.D ≤ Subgroup.normalizer (d.Q : Set G) :=
  fun _ hg => mem_normalizer_of_characteristic d.Q_le d.Q_characteristic (d.P_D hg)

private theorem T_le_centralizer_P {r : ℕ} (d : σ.IV7Data r) :
    σ.T ≤ Subgroup.centralizer (d.P : Set G) :=
  Subgroup.le_centralizer_iff.mp d.P_sylow.le

private theorem isPGroup_P {r : ℕ} (d : σ.IV7Data r) : IsPGroup r d.P :=
  d.P_sylow.isPGroup

omit [Finite G] in
private theorem centerOf_eq_map_center (X : Subgroup G) :
    centerOf X = (Subgroup.center X).map X.subtype := by
  ext g
  constructor
  · rintro ⟨hgX, hgC⟩
    refine ⟨⟨g, hgX⟩, Subgroup.mem_center_iff.mpr fun h => Subtype.ext ?_, rfl⟩
    exact ((Subgroup.mem_centralizer_iff.mp hgC) h h.2)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)

theorem centerOf_D_le_zpowers_x (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (hqd : σ.height = 1) : centerOf σ.D ≤ Subgroup.zpowers σ.x := by
  rw [← hII.center_S_eq_center_D]
  have hsyl := hσ.sylow
  rw [hqd] at hsyl
  obtain ⟨n, hn, hSD⟩ : ∃ n, 4 ≤ n ∧ ∀ S : Sylow 2 G,
      Nonempty (CFSG.Open.SemidihedralGroup n ≃* S) := by
    rcases hsyl with ⟨-, n, hn, hSD⟩ | ⟨h2, -⟩
    · exact ⟨n, hn, hSD⟩
    · omega
  obtain ⟨f⟩ := hSD σ.S
  have hcard : Nat.card (centerOf (σ.S : Subgroup G)) = 2 := by
    rw [centerOf_eq_map_center, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      ← Nat.card_congr (Subgroup.centerCongr f).toEquiv, CFSG.Semidihedral.center_card n hn]
  have hle : Subgroup.zpowers σ.x ≤ centerOf (σ.S : Subgroup G) :=
    Subgroup.zpowers_le.mpr hσ.x_mem_center
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_zpowers, hσ.x_order])
  exact heq.symm.le

end Basic

section NormalizerQ

theorem normalizer_Q_mem_familyMstar {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r)
    (h81 : σ.LemmaIV81) (h83 : σ.LemmaIV83) :
    Subgroup.normalizer (d.Q : Set G) ∈ σ.familyMstar r := by
  have hM := h81 r hr d
  obtain ⟨hD, hodd, -⟩ := h83 r hr d _ hM
  exact ⟨hM.1, hM.2.1, hD, hodd⟩

theorem T_le_centralizer_of_not_constrained (hσ : σ.IsValid) {r : ℕ}
    (hr : σ.HypIV7 r)
    (h92 : ∀ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K) ↔
      ∃ X : Subgroup G, IsSylowOf r X (oddCoreIn K) ∧ σ.T ≤ Subgroup.normalizer (X : Set G) ∧
        ¬ σ.T ≤ Subgroup.centralizer (X : Set G))
    {K : Subgroup G} (hK : K ∈ σ.familyMstar r)
    (hnot : ¬ PConstrainedWithin r K (CFSG.oddCore K)) {Y : Subgroup G}
    (hYO : Y ≤ oddCoreIn K) (hY : IsPGroup r Y) (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) :
    σ.T ≤ Subgroup.centralizer (Y : Set G) := by
  have hTK : σ.T ≤ K := (σ.T_le_D hσ).trans hK.2.1
  obtain ⟨X, hX, hYX, hTX⟩ := exists_isSylowOf_normalized_ge_of_odd hr.prime
    (σ.isPGroup_two_T hσ) (hTK.trans (le_normalizer_oddCoreIn K)) (odd_card_oddCoreIn K) hYO
    hY hTY
  have hTC : σ.T ≤ Subgroup.centralizer (X : Set G) := by
    by_contra hC
    exact hnot ((h92 K hK).mpr ⟨X, hX, hTX, hC⟩)
  exact hTC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hYX))

theorem lemmaIV95_ii (hσ : σ.IsValid) {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r)
    (hQ : ¬ PConstrainedWithin r (Subgroup.normalizer (d.Q : Set G))
      (CFSG.oddCore (Subgroup.normalizer (d.Q : Set G))))
    (h81 : σ.LemmaIV81) (h83 : σ.LemmaIV83)
    (h92 : ∀ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K) ↔
      ∃ X : Subgroup G, IsSylowOf r X (oddCoreIn K) ∧ σ.T ≤ Subgroup.normalizer (X : Set G) ∧
        ¬ σ.T ≤ Subgroup.centralizer (X : Set G)) :
    IsSylowOf r (d.P ⊓ oddCoreIn (Subgroup.normalizer (d.Q : Set G)))
      (oddCoreIn (Subgroup.normalizer (d.Q : Set G))) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  set H := Subgroup.normalizer (d.Q : Set G) with hHdef
  have hHM := σ.normalizer_Q_mem_familyMstar hr d h81 h83
  have hPH : d.P ≤ H := σ.P_le_normalizer_Q d
  have hTH : σ.T ≤ H := (σ.T_le_D hσ).trans hHM.2.1
  have hPO : d.P ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
    hPH.trans (le_normalizer_oddCoreIn H)
  have hodd : Odd (Nat.card (oddCoreIn H ⊔ d.P : Subgroup G)) :=
    odd_card_sup_of_le_normalizer_of_odd hPO (odd_card_oddCoreIn H)
      (σ.odd_card_of_isPGroup_hyp hr (σ.isPGroup_P d))
  have hTnorm : σ.T ≤ Subgroup.normalizer ((oddCoreIn H ⊔ d.P : Subgroup G) : Set G) :=
    (le_inf (hTH.trans (le_normalizer_oddCoreIn H))
      ((σ.T_le_D hσ).trans d.P_D)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨Y, hY, hPY, hTY⟩ := exists_isSylowOf_normalized_ge_of_odd hr.prime
    (σ.isPGroup_two_T hσ) hTnorm hodd le_sup_right (σ.isPGroup_P d)
    ((σ.T_le_D hσ).trans d.P_D)
  have hXsyl : IsSylowOf r (Y ⊓ oddCoreIn H) (oddCoreIn H) :=
    hY.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hPO)
  have hTX : σ.T ≤ Subgroup.normalizer ((Y ⊓ oddCoreIn H : Subgroup G) : Set G) :=
    (le_inf hTY (hTH.trans (le_normalizer_oddCoreIn H))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hTC : σ.T ≤ Subgroup.centralizer ((Y ⊓ oddCoreIn H : Subgroup G) : Set G) :=
    σ.T_le_centralizer_of_not_constrained hσ hr h92 hHM hQ inf_le_right hXsyl.isPGroup hTX
  have hXC : Y ⊓ oddCoreIn H ≤ σ.C := Subgroup.le_centralizer_iff.mp hTC
  have hPX : d.P ⊔ (Y ⊓ oddCoreIn H) ≤ Y := sup_le hPY inf_le_left
  have heq := d.P_sylow.eq_of_le le_sup_left (sup_le d.P_sylow.le hXC)
    (hY.isPGroup.to_le hPX)
  have hXP : Y ⊓ oddCoreIn H ≤ d.P := by rw [← heq]; exact le_sup_right
  have heq2 := hXsyl.eq_of_le (le_inf hXP inf_le_right) inf_le_right
    (σ.isPGroup_P d).to_inf_left
  rw [heq2]
  exact hXsyl

theorem mem_centerOf_D_of_mem_solvRadIn_N (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {u : G} (huD : u ∈ σ.D) (hu : u ∈ solvRadIn σ.N) : u ∈ centerOf σ.D := by
  rw [hII.N_solvRad] at hu
  have hZN : centerOf (σ.S : Subgroup G) ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (inf_le_left.trans (σ.S_le_N hσ)).trans σ.N_le_normalizer_ON
  obtain ⟨o, ho, z, hz, rfl⟩ := exists_mul_of_mem_sup hZN hu
  have hoS : o ∈ (σ.S : Subgroup G) := by
    have h1 := (σ.S : Subgroup G).mul_mem (σ.D_le_S huD) ((σ.S : Subgroup G).inv_mem hz.1)
    simpa using h1
  have hbot := inf_eq_bot_of_isPGroup_two_of_odd σ.S.isPGroup' σ.odd_card_ON
  have ho1 : o = 1 := by
    have h1 : o ∈ (σ.S : Subgroup G) ⊓ σ.ON := ⟨hoS, ho⟩
    rw [hbot] at h1
    exact h1
  rw [ho1, one_mul, ← hII.center_S_eq_center_D]
  exact hz

private theorem not_mem_centralizer_QR (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) (d : σ.IV7Data r) (hc : σ.Constrained r) {u : G} (huD : u ∈ σ.D)
    (hu : u ∉ centerOf σ.D) :
    u ∉ Subgroup.centralizer
      (((d.Q ⊔ d.R) ⊓ Subgroup.normalizer (d.Q : Set G) : Subgroup G) : Set G) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  intro huC
  have hQX : d.Q ≤ (d.Q ⊔ d.R) ⊓ Subgroup.normalizer (d.Q : Set G) :=
    le_inf le_sup_left Subgroup.le_normalizer
  have hRX : d.R ⊓ Subgroup.centralizer (d.Q : Set G) ≤
      (d.Q ⊔ d.R) ⊓ Subgroup.normalizer (d.Q : Set G) :=
    le_inf (inf_le_left.trans le_sup_right)
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have huQ : u ∈ Subgroup.centralizer (d.Q : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQX) huC
  have huRQ : u ∈ Subgroup.centralizer
      ((d.R ⊓ Subgroup.centralizer (d.Q : Set G) : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRX) huC
  have hQr : IsPGroup r d.Q := (σ.isPGroup_P d).to_le d.Q_le
  have hRr : IsPGroup r d.R := d.R_sylow.isPGroup
  obtain ⟨k, hk⟩ := exists_orderOf_eq_pow_of_mem σ.isPGroup_two_D huD
  have hcop : Nat.Coprime r (Nat.card (Subgroup.zpowers u)) := by
    rw [Nat.card_zpowers, hk]
    exact Nat.Coprime.pow_right k
      ((Nat.coprime_primes hr.prime Nat.prime_two).mpr (σ.prime_ne_two_of_hyp hr))
  have hpq := CFSG.GorensteinWalter.ThompsonPQ.thompson_p_times_q d.Q (Subgroup.zpowers u) d.R
    hQr hRr hcop (d.Q_le.trans d.R_P) (Subgroup.zpowers_le.mpr (d.R_D huD))
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr huQ)))
    (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr huRQ))
  have huR : u ∈ Subgroup.centralizer (d.R : Set G) :=
    Subgroup.zpowers_le.mp
      (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hpq))
  have hCN := (σ.constrained_iff_centralizer_le hσ hII hr.prime hr.dvd_ON d.R_sylow).mp hc
  exact hu (σ.mem_centerOf_D_of_mem_solvRadIn_N hσ hII huD
    (hCN ⟨σ.D_le_N hσ huD, huR⟩))

private theorem isPGroup_Q_sup_R {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r) :
    IsPGroup r (d.Q ⊔ d.R : Subgroup G) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  rw [sup_comm]
  exact isPGroup_sup_of_le_normalizer d.R_sylow.isPGroup ((σ.isPGroup_P d).to_le d.Q_le)
    (d.Q_le.trans d.R_P)

private theorem D_le_normalizer_QR {r : ℕ} (d : σ.IV7Data r)
    (hDH : σ.D ≤ Subgroup.normalizer (d.Q : Set G)) :
    σ.D ≤ Subgroup.normalizer
      (((d.Q ⊔ d.R) ⊓ Subgroup.normalizer (d.Q : Set G) : Subgroup G) : Set G) := by
  have h1 : σ.D ≤ Subgroup.normalizer ((d.Q ⊔ d.R : Subgroup G) : Set G) :=
    (le_inf (σ.D_le_normalizer_Q d) d.R_D).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact (le_inf h1 (hDH.trans Subgroup.le_normalizer)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

private theorem D_le_centralizer_of_simple (hσ : σ.IsValid) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r)
    (hQ : ¬ PConstrainedWithin r (Subgroup.normalizer (d.Q : Set G))
      (CFSG.oddCore (Subgroup.normalizer (d.Q : Set G))))
    (h81 : σ.LemmaIV81) (h83 : σ.LemmaIV83)
    (h92 : ∀ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K) ↔
      ∃ X : Subgroup G, IsSylowOf r X (oddCoreIn K) ∧ σ.T ≤ Subgroup.normalizer (X : Set G) ∧
        ¬ σ.T ≤ Subgroup.centralizer (X : Set G))
    (hsimple : ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (d.Q : Set G) →
      Subgroup.normalizer (d.Q : Set G) ≤ Subgroup.normalizer (Y : Set G) →
      oddCoreIn (Subgroup.normalizer (d.Q : Set G)) ≤ Y →
        Y = oddCoreIn (Subgroup.normalizer (d.Q : Set G)) ∨
          Y = Subgroup.normalizer (d.Q : Set G))
    {Z₀ : Subgroup G} (hZ₀O : Z₀ ≤ oddCoreIn (Subgroup.normalizer (d.Q : Set G)))
    (hZ₀ : IsPGroup r Z₀) (hDZ₀ : σ.D ≤ Subgroup.normalizer (Z₀ : Set G)) :
    σ.D ≤ Subgroup.centralizer (Z₀ : Set G) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  set H := Subgroup.normalizer (d.Q : Set G) with hHdef
  have hHM := σ.normalizer_Q_mem_familyMstar hr d h81 h83
  have hDH : σ.D ≤ H := hHM.2.1
  obtain ⟨U', hU', hZU', hDU'⟩ := exists_isSylowOf_normalized_ge_of_odd hr.prime
    σ.isPGroup_two_D (hDH.trans (le_normalizer_oddCoreIn H)) (odd_card_oddCoreIn H) hZ₀O hZ₀
    hDZ₀
  have hTU' : σ.T ≤ Subgroup.centralizer (U' : Set G) :=
    σ.T_le_centralizer_of_not_constrained hσ hr h92 hHM hQ hU'.le hU'.isPGroup
      ((σ.T_le_D hσ).trans hDU')
  set Y₀ := oddCoreIn H ⊔ (H ⊓ Subgroup.centralizer (U' : Set G)) with hY₀
  have hY₀H : Y₀ ≤ H := sup_le (oddCoreIn_le H) inf_le_left
  have hHY₀ : H ≤ Subgroup.normalizer (Y₀ : Set G) := by
    intro h hh
    obtain ⟨n, hn, k, hk, rfl⟩ :=
      exists_mem_normalizer_mul_of_isSylowOf hU' (le_normalizer_oddCoreIn H hh)
    have hnH : n ∈ H := by
      have h1 := H.mul_mem hh (H.inv_mem (oddCoreIn_le H hk))
      simpa using h1
    have hn1 : n ∈ Subgroup.normalizer (Y₀ : Set G) :=
      normalizer_inf_normalizer_le_normalizer_sup _ _
        ⟨le_normalizer_oddCoreIn H hnH, Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hnH, normalizer_le_normalizer_centralizer U' hn⟩⟩
    exact Subgroup.mul_mem _ hn1 (Subgroup.le_normalizer (le_sup_left (a := oddCoreIn H) hk))
  have hTY₀ : σ.T ≤ Y₀ :=
    le_sup_of_le_right (le_inf ((σ.T_le_D hσ).trans hDH) hTU')
  have hY₀eq : Y₀ = H := by
    rcases hsimple Y₀ hY₀H hHY₀ le_sup_left with h | h
    · exfalso
      have hxO : σ.x ∈ σ.T ⊓ oddCoreIn H := ⟨σ.x_mem_T, h ▸ hTY₀ σ.x_mem_T⟩
      rw [inf_eq_bot_of_isPGroup_two_of_odd (σ.isPGroup_two_T hσ) (odd_card_oddCoreIn H),
        Subgroup.mem_bot] at hxO
      have h2 := hσ.x_order
      rw [hxO, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact h
  have hDU'C : σ.D ≤ Subgroup.centralizer (U' : Set G) := by
    intro e he
    have heY : e ∈ Y₀ := hY₀eq ▸ hDH he
    obtain ⟨o, ho, c, hc, rfl⟩ := exists_mul_of_mem_sup
      (inf_le_left.trans (le_normalizer_oddCoreIn H)) heY
    have hoN : o ∈ Subgroup.normalizer (U' : Set G) := by
      have h1 := Subgroup.mul_mem _ (hDU' he)
        (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hc.2))
      simpa using h1
    have hodd : Odd (orderOf o) :=
      (odd_card_oddCoreIn H).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ho)
    obtain ⟨k, hk⟩ := exists_orderOf_eq_pow_of_mem σ.isPGroup_two_D he
    have hpow : (o * c) ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
    exact mul_mem_centralizer_of_odd_of_two hodd hoN hc.2 hpow
  exact hDU'C.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZU'))

theorem lemmaIV95_i (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) (hc : σ.Constrained r)
    (hQ : ¬ PConstrainedWithin r (Subgroup.normalizer (d.Q : Set G))
      (CFSG.oddCore (Subgroup.normalizer (d.Q : Set G))))
    (h81 : σ.LemmaIV81) (h83 : σ.LemmaIV83)
    (h92 : ∀ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K) ↔
      ∃ X : Subgroup G, IsSylowOf r X (oddCoreIn K) ∧ σ.T ≤ Subgroup.normalizer (X : Set G) ∧
        ¬ σ.T ≤ Subgroup.centralizer (X : Set G))
    (h_II34 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      (∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.T ≤ Subgroup.normalizer (X : Set G) →
          X ≤ oddCoreIn H) ∨
        ((∀ Y : Subgroup G, Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) → oddCoreIn H ≤ Y →
            Y = oddCoreIn H ∨ Y = H) ∧
          ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.D ≤ Subgroup.normalizer (X : Set G) →
            ∃ T₁ : Subgroup G, T₁ ≤ σ.D ∧ IsKleinFour T₁ ∧ ⁅X, T₁⁆ ≤ oddCoreIn H) ∨
        (σ.height = 1 ∧ ∃ q₁ : ℕ, 3 < q₁ ∧ IsLinearTypeWrt σ.T H q₁)) :
    σ.height = 1 ∧
      ∃ q₁ : ℕ, 3 < q₁ ∧ IsLinearTypeWrt σ.T (Subgroup.normalizer (d.Q : Set G)) q₁ := by
  have : Fact r.Prime := ⟨hr.prime⟩
  set H := Subgroup.normalizer (d.Q : Set G) with hHdef
  have hHM := σ.normalizer_Q_mem_familyMstar hr d h81 h83
  have hDH : σ.D ≤ H := hHM.2.1
  set X := (d.Q ⊔ d.R) ⊓ H with hXdef
  have hXH : X ≤ H := inf_le_right
  have hXr : IsPGroup r X := (σ.isPGroup_Q_sup_R hr d).to_inf_left
  have hXodd : Odd (Nat.card X) := σ.odd_card_of_isPGroup_hyp hr hXr
  have hDX : σ.D ≤ Subgroup.normalizer (X : Set G) := σ.D_le_normalizer_QR d hDH
  rcases h_II34 H hDH hHM.2.2.1 with hPGL | ⟨hsimple, hA7⟩ | hlin
  · exfalso
    have hXO := hPGL X hXH hXodd ((σ.T_le_D hσ).trans hDX)
    have hTX := σ.T_le_centralizer_of_not_constrained hσ hr h92 hHM hQ hXO hXr
      ((σ.T_le_D hσ).trans hDX)
    exact σ.not_mem_centralizer_QR hσ hII hr d hc (σ.T_le_D hσ σ.x₂_mem_T)
      (σ.x₂_not_mem_centerOf_D hσ hII) (hTX σ.x₂_mem_T)
  · exfalso
    obtain ⟨T₁, hT₁D, hT₁, hXT₁⟩ := hA7 X hXH hXodd hDX
    have hDZ₀ : σ.D ≤ Subgroup.normalizer ((X ⊓ oddCoreIn H : Subgroup G) : Set G) :=
      (le_inf hDX (hDH.trans (le_normalizer_oddCoreIn H))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hDC := σ.D_le_centralizer_of_simple hσ hr d hQ h81 h83 h92 hsimple inf_le_right
      hXr.to_inf_left hDZ₀
    obtain ⟨u, huT₁, hu⟩ := σ.exists_mem_not_mem_centerOf_D_of_kleinFour hσ hII hT₁
    apply σ.not_mem_centralizer_QR hσ hII hr d hc (hT₁D huT₁) hu
    refine mem_centralizer_of_stabilizes (mul_self_eq_one_of_kleinFour hT₁ huT₁)
      ((odd_card_oddCoreIn H).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)) ?_
      (hDC (hT₁D huT₁))
    intro a ha
    refine ⟨X.mul_mem (conj_mem_of_mem_normalizer (hDX (hT₁D huT₁)) ha) (X.inv_mem ha), ?_⟩
    have h1 := (oddCoreIn H).inv_mem (hXT₁ (Subgroup.commutator_mem_commutator ha huT₁))
    rw [commutatorElement_def] at h1
    have e : u * a * u⁻¹ * a⁻¹ = (a * u * a⁻¹ * u⁻¹)⁻¹ := by group
    show u * a * u⁻¹ * a⁻¹ ∈ oddCoreIn H
    rw [e]
    exact h1
  · exact hlin

theorem lemmaIV95_iii (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) (hc : σ.Constrained r)
    (hQ : ¬ PConstrainedWithin r (Subgroup.normalizer (d.Q : Set G))
      (CFSG.oddCore (Subgroup.normalizer (d.Q : Set G))))
    (h81 : σ.LemmaIV81) (h83 : σ.LemmaIV83)
    (h92 : ∀ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K) ↔
      ∃ X : Subgroup G, IsSylowOf r X (oddCoreIn K) ∧ σ.T ≤ Subgroup.normalizer (X : Set G) ∧
        ¬ σ.T ≤ Subgroup.centralizer (X : Set G))
    (h_II34 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      (∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.T ≤ Subgroup.normalizer (X : Set G) →
          X ≤ oddCoreIn H) ∨
        ((∀ Y : Subgroup G, Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) → oddCoreIn H ≤ Y →
            Y = oddCoreIn H ∨ Y = H) ∧
          ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.D ≤ Subgroup.normalizer (X : Set G) →
            ∃ T₁ : Subgroup G, T₁ ≤ σ.D ∧ IsKleinFour T₁ ∧ ⁅X, T₁⁆ ≤ oddCoreIn H) ∨
        (σ.height = 1 ∧ ∃ q₁ : ℕ, 3 < q₁ ∧ IsLinearTypeWrt σ.T H q₁))
    (h_II57 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      IsLinearTypeWrt σ.T H 9 → H ⊓ Subgroup.centralizer (σ.T : Set G) ≤ σ.T ⊔ oddCoreIn H)
    (h_II56 : ∀ (M Z W : Subgroup G) (F : Type) [Field F] [Finite F], Z ≤ M → W ≤ Z →
      M ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card Z) → ⁅Z, M⁆ ≤ W →
      Odd (Nat.card F) → 3 < Nat.card F → Nat.card F ≠ 9 →
      (∃ ψ : M →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = Z.subgroupOf M) →
        ⁅M, M⁆ ⊓ Z ≤ W ∧ ⁅M, M⁆ ⊔ Z = M)
    (h_II58 : ∀ (J W A : Subgroup G) (F : Type) [Field F] [Finite F], W ≤ J →
      J ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card W) → Odd (Nat.card F) →
      3 < Nat.card F →
      (∃ ψ : J →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = W.subgroupOf J) →
      σ.T ≤ J → IsPGroup r A → A ≤ Subgroup.normalizer (J : Set G) →
      A ≤ Subgroup.normalizer (W : Set G) → A ≤ Subgroup.centralizer (σ.T : Set G) →
        ∃ g ∈ J, (∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ W) ∧
          g ∈ Subgroup.normalizer ((σ.T ⊔ W : Subgroup G) : Set G) ∧
          (∀ t ∈ σ.T, g ^ 3 * t * (g ^ 3)⁻¹ * t⁻¹ ∈ W) ∧ ∃ t ∈ σ.T, g * t * g⁻¹ * t⁻¹ ∉ W) :
    IsDGroupWrt (σ.T.subgroupOf
      (Subgroup.normalizer (d.Q : Set G) ⊓ Subgroup.centralizer (d.P : Set G))) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hqd, q₁, h3q, hlin⟩ := σ.lemmaIV95_i hσ hII hr d hc hQ h81 h83 h92 h_II34
  have hU₀ := σ.lemmaIV95_ii hσ hr d hQ h81 h83 h92
  set H := Subgroup.normalizer (d.Q : Set G) with hHdef
  set U₀ := d.P ⊓ oddCoreIn H with hU₀def
  have hHM := σ.normalizer_Q_mem_familyMstar hr d h81 h83
  have hDH : σ.D ≤ H := hHM.2.1
  have hTH : σ.T ≤ H := (σ.T_le_D hσ).trans hDH
  have hPH : d.P ≤ H := σ.P_le_normalizer_Q d
  have hTP := σ.T_le_centralizer_P d
  set K₀ := H ⊓ Subgroup.normalizer (U₀ : Set G) with hK₀def
  have hsup : H ≤ oddCoreIn H ⊔ K₀ := le_oddCoreIn_sup_inf_normalizer hU₀
  have hOK : oddCoreIn K₀ = oddCoreIn H ⊓ K₀ := oddCoreIn_eq_inf_of_le_sup inf_le_left hsup
  have hTU : σ.T ≤ Subgroup.centralizer (U₀ : Set G) :=
    hTP.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))
  have hTK : σ.T ≤ K₀ := le_inf hTH (hTU.trans (Subgroup.centralizer_le_normalizer _))
  have hlinK := isLinearTypeWrt_of_le_sup inf_le_left hsup hOK hTK hlin
  have hKU : K₀ ≤ Subgroup.normalizer (U₀ : Set G) := inf_le_right
  have hU₀K₀ : U₀ ≤ K₀ := le_inf (inf_le_left.trans hPH) Subgroup.le_normalizer
  have hU₀K : IsSylowOf r U₀ (oddCoreIn K₀) :=
    hU₀.of_le (hOK ▸ le_inf inf_le_right hU₀K₀) (hOK ▸ inf_le_left)
  have hPK : d.P ≤ K₀ :=
    le_inf hPH ((le_inf Subgroup.le_normalizer (hPH.trans (le_normalizer_oddCoreIn H))).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
  have hT₂ := σ.isPGroup_two_T hσ
  have hTc := σ.T_comm hσ
  obtain ⟨n, hn, hnT, hn3, hn1⟩ : ∃ n ∈ K₀ ⊓ Subgroup.centralizer (d.P : Set G),
      n ∈ Subgroup.normalizer (σ.T : Set G) ∧ n ^ 3 ∈ Subgroup.centralizer (σ.T : Set G) ∧
        n ∉ Subgroup.centralizer (σ.T : Set G) := by
    by_cases hPO : d.P ≤ oddCoreIn H
    · have hUP : U₀ = d.P := inf_eq_left.mpr hPO
      have h := exists_automizer_element_of_le hT₂ hTc hTK hTU hKU hlinK h3q h_II58
      rw [hUP] at h
      exact h
    · have h9 : q₁ ≠ 9 := by
        rintro rfl
        apply hPO
        intro a ha
        have haC := h_II57 H hDH hHM.2.2.1 hlin ⟨hPH ha, d.P_sylow.le ha⟩
        have hTO : σ.T ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
          hTH.trans (le_normalizer_oddCoreIn H)
        refine mem_of_coprime_orderOf_relIndex le_sup_right
          (sup_le hTO Subgroup.le_normalizer) haC ?_
        rw [relIndex_sup_right_of_le_normalizer hTO]
        obtain ⟨k, hk⟩ := exists_orderOf_eq_pow_of_mem (σ.isPGroup_P d) ha
        obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT₂
        have hdvd : (oddCoreIn H).relIndex σ.T ∣ 2 ^ m := hm ▸ Subgroup.relIndex_dvd_card _ _
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
        rw [hk, hj]
        exact Nat.Coprime.pow k j
          ((Nat.coprime_primes hr.prime Nat.prime_two).mpr (σ.prime_ne_two_of_hyp hr))
      exact exists_automizer_element_of_ne_nine hT₂ hTc hTK hKU hU₀K inf_le_left
        (σ.isPGroup_P d) hPK hTP hlinK h3q h9 h_II56 h_II58
  have hnHC : n ∈ H ⊓ Subgroup.centralizer (d.P : Set G) := ⟨hn.1.1, hn.2⟩
  have hTHC : σ.T ≤ H ⊓ Subgroup.centralizer (d.P : Set G) := le_inf hTH hTP
  have h3T := three_dvd_automizerIndex_subgroupOf_of hTHC hnHC hnT hn3 hn1
  rcases hII.qd_or_d_of_three _ hTHC (Or.inr hqd) h3T with hQD | hDg
  · exact absurd hQD (not_isQDGroup_of_le_isDGroup inf_le_left hHM.2.2.1.1)
  · exact hDg

theorem lemmaIV95_qd (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) (hc : σ.Constrained r)
    (hQ : ¬ PConstrainedWithin r (Subgroup.normalizer (d.Q : Set G))
      (CFSG.oddCore (Subgroup.normalizer (d.Q : Set G))))
    (h81 : σ.LemmaIV81) (h83 : σ.LemmaIV83)
    (h92 : ∀ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K) ↔
      ∃ X : Subgroup G, IsSylowOf r X (oddCoreIn K) ∧ σ.T ≤ Subgroup.normalizer (X : Set G) ∧
        ¬ σ.T ≤ Subgroup.centralizer (X : Set G))
    (h_II34 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      (∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.T ≤ Subgroup.normalizer (X : Set G) →
          X ≤ oddCoreIn H) ∨
        ((∀ Y : Subgroup G, Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) → oddCoreIn H ≤ Y →
            Y = oddCoreIn H ∨ Y = H) ∧
          ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.D ≤ Subgroup.normalizer (X : Set G) →
            ∃ T₁ : Subgroup G, T₁ ≤ σ.D ∧ IsKleinFour T₁ ∧ ⁅X, T₁⁆ ≤ oddCoreIn H) ∨
        (σ.height = 1 ∧ ∃ q₁ : ℕ, 3 < q₁ ∧ IsLinearTypeWrt σ.T H q₁))
    (h_II57 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      IsLinearTypeWrt σ.T H 9 → H ⊓ Subgroup.centralizer (σ.T : Set G) ≤ σ.T ⊔ oddCoreIn H)
    (h_II56 : ∀ (M Z W : Subgroup G) (F : Type) [Field F] [Finite F], Z ≤ M → W ≤ Z →
      M ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card Z) → ⁅Z, M⁆ ≤ W →
      Odd (Nat.card F) → 3 < Nat.card F → Nat.card F ≠ 9 →
      (∃ ψ : M →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = Z.subgroupOf M) →
        ⁅M, M⁆ ⊓ Z ≤ W ∧ ⁅M, M⁆ ⊔ Z = M)
    (h_II58 : ∀ (J W A : Subgroup G) (F : Type) [Field F] [Finite F], W ≤ J →
      J ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card W) → Odd (Nat.card F) →
      3 < Nat.card F →
      (∃ ψ : J →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = W.subgroupOf J) →
      σ.T ≤ J → IsPGroup r A → A ≤ Subgroup.normalizer (J : Set G) →
      A ≤ Subgroup.normalizer (W : Set G) → A ≤ Subgroup.centralizer (σ.T : Set G) →
        ∃ g ∈ J, (∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ W) ∧
          g ∈ Subgroup.normalizer ((σ.T ⊔ W : Subgroup G) : Set G) ∧
          (∀ t ∈ σ.T, g ^ 3 * t * (g ^ 3)⁻¹ * t⁻¹ ∈ W) ∧ ∃ t ∈ σ.T, g * t * g⁻¹ * t⁻¹ ∉ W) :
    (σ.height = 1 ∧
        ∃ q₁ : ℕ, 3 < q₁ ∧ IsLinearTypeWrt σ.T (Subgroup.normalizer (d.Q : Set G)) q₁) ∧
      IsSylowOf r (d.P ⊓ oddCoreIn (Subgroup.normalizer (d.Q : Set G)))
        (oddCoreIn (Subgroup.normalizer (d.Q : Set G))) ∧
      IsDGroupWrt (σ.T.subgroupOf
        (Subgroup.normalizer (d.Q : Set G) ⊓ Subgroup.centralizer (d.P : Set G))) :=
  ⟨σ.lemmaIV95_i hσ hII hr d hc hQ h81 h83 h92 h_II34, σ.lemmaIV95_ii hσ hr d hQ h81 h83 h92,
    σ.lemmaIV95_iii hσ hII hr d hc hQ h81 h83 h92 h_II34 h_II57 h_II56 h_II58⟩

end NormalizerQ

section NormalizerR

theorem normalizer_R_mem_familyL (hσ : σ.IsValid) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) : Subgroup.normalizer (d.R : Set G) ∈ σ.familyL r :=
  σ.normalizer_mem_familyL hσ hr.prime hr.dvd_ON d.R_sylow d.R_D

theorem lemmaIV96 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) (hc : σ.Constrained r) :
    Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (d.R : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G)) ∧
      solvRadIn (Subgroup.normalizer (d.R : Set G)) =
        oddCoreIn (Subgroup.normalizer (d.R : Set G)) ⊔ centerOf σ.D := by
  set K := Subgroup.normalizer (d.R : Set G) with hKdef
  have hKL := σ.normalizer_R_mem_familyL hσ hr d
  obtain ⟨-, hfac, -, -, ⟨-, hON2⟩, -⟩ := σ.familyL_properties hσ hII hr.prime hr.dvd_ON hKL
  have hDK : σ.D ≤ K := hKL.2.2.1
  have hO : oddCoreIn K ≠ ⊥ :=
    oddCoreIn_ne_bot_of_isPLocal hr.prime (σ.prime_ne_two_of_hyp hr) hKL.1
  have hS : solvRadIn K = oddCoreIn K ⊔ centerOf σ.D := hII.qgroup_solvRad K hDK hO hKL.2.1
  refine ⟨?_, hS⟩
  intro c hcmem
  obtain ⟨hcK, hcR⟩ := Subgroup.mem_inf.mp hcmem
  have hxK : σ.x ∈ K := hDK (σ.T_le_D hσ σ.x_mem_T)
  have hxR : σ.x ∈ Subgroup.centralizer (d.R : Set G) := σ.x_mem_centralizer_of_le_ON d.R_sylow.le
  set M₀ := oddCoreIn K ⊓ Subgroup.centralizer (d.R : Set G) with hM₀
  have hM₀odd : Odd (Nat.card M₀) :=
    (odd_card_oddCoreIn K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hcx : c * σ.x * c⁻¹ * σ.x⁻¹ ∈ M₀ := by
    refine ⟨?_, ?_⟩
    · have hcK' : c ∈ oddCoreIn K ⊔ (K ⊓ σ.N) := hfac.symm ▸ hcK
      obtain ⟨o, ho, n, hn, rfl⟩ :=
        exists_mul_of_mem_sup (inf_le_left.trans (le_normalizer_oddCoreIn K)) hcK'
      have hnx : n * σ.x = σ.x * n := (σ.mem_N_iff n).mp hn.2
      have e : o * n * σ.x * (o * n)⁻¹ * σ.x⁻¹ = o * (σ.x * o⁻¹ * σ.x⁻¹) := by
        calc o * n * σ.x * (o * n)⁻¹ * σ.x⁻¹ = o * (n * σ.x) * n⁻¹ * o⁻¹ * σ.x⁻¹ := by group
          _ = o * (σ.x * n) * n⁻¹ * o⁻¹ * σ.x⁻¹ := by rw [hnx]
          _ = o * (σ.x * o⁻¹ * σ.x⁻¹) := by group
      rw [e]
      exact (oddCoreIn K).mul_mem ho
        (conj_mem_of_mem_normalizer (le_normalizer_oddCoreIn K hxK) ((oddCoreIn K).inv_mem ho))
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcR hxR)
        (Subgroup.inv_mem _ hcR)) (Subgroup.inv_mem _ hxR)
  have hxx : σ.x * σ.x = 1 := by rw [← pow_two, ← hσ.x_order, pow_orderOf_eq_one]
  obtain ⟨m, hm, hmc⟩ := exists_mem_inv_mul_mem_centralizer_of_odd hM₀odd hxx hcx
  have hc'N : m⁻¹ * c ∈ σ.N := hmc
  have hc'R : m⁻¹ * c ∈ Subgroup.centralizer (d.R : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hm.2) hcR
  have hCN := (σ.constrained_iff_centralizer_le hσ hII hr.prime hr.dvd_ON d.R_sylow).mp hc
  have hc'S : m⁻¹ * c ∈ σ.ON ⊔ centerOf (σ.S : Subgroup G) :=
    hII.N_solvRad ▸ hCN ⟨hc'N, hc'R⟩
  have hZN : centerOf (σ.S : Subgroup G) ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (inf_le_left.trans (σ.S_le_N hσ)).trans σ.N_le_normalizer_ON
  obtain ⟨o, ho, z, hz, hoz⟩ := exists_mul_of_mem_sup hZN hc'S
  have hzD : z ∈ centerOf σ.D := hII.center_S_eq_center_D ▸ hz
  have hzK : z ∈ K := hDK hzD.1
  have hmK : m ∈ K := oddCoreIn_le K hm.1
  have hoK : o ∈ K := by
    have h1 : o = m⁻¹ * c * z⁻¹ := by rw [hoz]; group
    rw [h1]
    exact K.mul_mem (K.mul_mem (K.inv_mem hmK) hcK) (K.inv_mem hzK)
  have hoO : o ∈ oddCoreIn K := hON2 ⟨ho, hoK⟩
  have hc' : m⁻¹ * c ∈ solvRadIn K := by
    rw [hS, hoz]
    exact Subgroup.mul_mem_sup hoO hzD
  have hcm : c = m * (m⁻¹ * c) := by group
  rw [hcm]
  exact Subgroup.mul_mem _ (hS ▸ Subgroup.mem_sup_left hm.1) hc'

theorem mem_centerOf_D_of_mem_solvRadIn_K (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r) (hc : σ.Constrained r) {u : G}
    (huD : u ∈ σ.D) (hu : u ∈ solvRadIn (Subgroup.normalizer (d.R : Set G))) :
    u ∈ centerOf σ.D := by
  set K := Subgroup.normalizer (d.R : Set G) with hKdef
  have hDK : σ.D ≤ K := d.R_D
  rw [(σ.lemmaIV96 hσ hII hr d hc).2] at hu
  have hZO : centerOf σ.D ≤ Subgroup.normalizer (oddCoreIn K : Set G) :=
    (inf_le_left.trans hDK).trans (le_normalizer_oddCoreIn K)
  obtain ⟨o, ho, z, hz, rfl⟩ := exists_mul_of_mem_sup hZO hu
  have hoD : o ∈ σ.D := by
    have h1 := σ.D.mul_mem huD (σ.D.inv_mem hz.1)
    simpa using h1
  have hbot := inf_eq_bot_of_isPGroup_two_of_odd σ.isPGroup_two_D (odd_card_oddCoreIn K)
  have ho1 : o = 1 := by
    have h1 : o ∈ σ.D ⊓ oddCoreIn K := ⟨hoD, ho⟩
    rw [hbot] at h1
    exact h1
  rw [ho1, one_mul]
  exact hz

theorem nonempty_IV9UV (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) (hc : σ.Constrained r) : Nonempty (σ.IV9UV d) := by
  classical
  set K := Subgroup.normalizer (d.R : Set G) with hKdef
  set 𝓢 : Set (Subgroup G) := {X | K ≤ Subgroup.normalizer (X : Set G) ∧ X ≤ d.R ∧
    K ⊓ Subgroup.centralizer (X : Set G) ≤ solvRadIn K} with h𝓢
  have hR𝓢 : d.R ∈ 𝓢 := ⟨le_rfl, le_rfl, (σ.lemmaIV96 hσ hII hr d hc).1⟩
  obtain ⟨U, hU⟩ := 𝓢.toFinite.exists_minimal ⟨d.R, hR𝓢⟩
  obtain ⟨hUn, hUR, hUC⟩ := hU.prop
  have hUmin : ∀ X : Subgroup G, K ≤ Subgroup.normalizer (X : Set G) → X < U →
      ¬ K ⊓ Subgroup.centralizer (X : Set G) ≤ solvRadIn K := by
    intro X hXn hXU hXC
    exact (not_le_of_gt hXU) (hU.le_of_le ⟨hXn, hXU.le.trans hUR, hXC⟩ hXU.le)
  have hUbot : U ≠ ⊥ := by
    rintro rfl
    have hx₂K : σ.x₂ ∈ K := d.R_D (σ.T_le_D hσ σ.x₂_mem_T)
    have hx₂C : σ.x₂ ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
      rw [hh, one_mul, mul_one]
    exact σ.x₂_not_mem_centerOf_D hσ hII (σ.mem_centerOf_D_of_mem_solvRadIn_K hσ hII hr d hc
      (σ.T_le_D hσ σ.x₂_mem_T) (hUC ⟨hx₂K, hx₂C⟩))
  by_cases hab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a
  · set 𝓥 : Set (Subgroup G) := {X | K ≤ Subgroup.normalizer (X : Set G) ∧ X < U} with h𝓥
    have hbot𝓥 : (⊥ : Subgroup G) ∈ 𝓥 := by
      refine ⟨fun g _ => ?_, bot_lt_iff_ne_bot.mpr hUbot⟩
      rw [Subgroup.mem_normalizer_iff]
      intro h
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl; group
      · intro h1
        have h2 : h = g⁻¹ * (g * h * g⁻¹) * g := by group
        rw [h2, h1]
        group
    obtain ⟨V, hV⟩ := 𝓥.toFinite.exists_maximal ⟨⊥, hbot𝓥⟩
    obtain ⟨hVn, hVU⟩ := hV.prop
    refine ⟨⟨U, hUn, hUR, hUC, hUmin, V, hVn, hVU, ?_, ?_⟩⟩
    · intro _ X hXn hVX hXU
      by_cases hXeq : X = U
      · exact Or.inr hXeq
      · exact Or.inl (le_antisymm (hV.le_of_ge ⟨hXn, lt_of_le_of_ne hXU hXeq⟩ hVX) hVX)
    · intro h
      exact absurd hab h
  · have hZn : K ≤ Subgroup.normalizer ((centerOf U : Subgroup G) : Set G) :=
      (le_inf hUn (hUn.trans (normalizer_le_normalizer_centralizer U))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hZU : centerOf U < U := by
      refine lt_of_le_of_ne inf_le_left fun h => hab ?_
      intro a ha b hb
      have hb' : b ∈ centerOf U := by rw [h]; exact hb
      exact ((Subgroup.mem_centralizer_iff.mp hb'.2) a ha)
    refine ⟨⟨U, hUn, hUR, hUC, hUmin, centerOf U, hZn, hZU, ?_, fun _ => rfl⟩⟩
    intro h
    exact absurd h hab

theorem L₀_inf_le_sup_solvRadIn_K (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) (d : σ.IV7Data r) (hc : σ.Constrained r) {Y : Subgroup G}
    (hYK : Y ≤ Subgroup.normalizer (d.R : Set G))
    (hKY : Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (hY : ¬ Y ≤ solvRadIn (Subgroup.normalizer (d.R : Set G))) :
    σ.L₀ ⊓ Subgroup.normalizer (d.R : Set G) ≤
      Y ⊔ solvRadIn (Subgroup.normalizer (d.R : Set G)) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  set K := Subgroup.normalizer (d.R : Set G) with hKdef
  have hKL := σ.normalizer_R_mem_familyL hσ hr d
  obtain ⟨-, hfac, -, -, ⟨-, hON2⟩, -⟩ := σ.familyL_properties hσ hII hr.prime hr.dvd_ON hKL
  have hDK : σ.D ≤ K := hKL.2.2.1
  have hSK : solvRadIn K = oddCoreIn K ⊔ centerOf σ.D := (σ.lemmaIV96 hσ hII hr d hc).2
  have hSN : solvRadIn σ.N = σ.ON ⊔ centerOf σ.D := by
    rw [hII.N_solvRad, hII.center_S_eq_center_D]
  have hZK : centerOf σ.D ≤ K := inf_le_left.trans hDK
  have hZN : centerOf σ.D ≤ σ.N := inf_le_left.trans (σ.D_le_N hσ)
  have hOKS : oddCoreIn K ≤ solvRadIn K := hSK ▸ le_sup_left
  have hZS : centerOf σ.D ≤ solvRadIn K := hSK ▸ le_sup_right
  have hKSN : ∀ m ∈ K, m ∈ σ.ON ⊔ centerOf σ.D → m ∈ solvRadIn K := by
    intro m hmK hm
    obtain ⟨o, ho, z, hz, rfl⟩ :=
      exists_mul_of_mem_sup (hZN.trans σ.N_le_normalizer_ON) hm
    have hoK : o ∈ K := by
      have := K.mul_mem hmK (K.inv_mem (hZK hz))
      simpa using this
    exact Subgroup.mul_mem _ (hOKS (hON2 ⟨ho, hoK⟩)) (hZS hz)
  set A := (Y ⊔ solvRadIn K) ⊓ σ.N with hAdef
  set X := A ⊔ σ.ON with hXdef
  have hAK : A ≤ K := inf_le_left.trans (sup_le hYK (solvRadIn_le K))
  have hXN : X ≤ σ.N := sup_le inf_le_right σ.ON_le_N
  have hNfr : σ.N ≤ σ.ON ⊔ (σ.N ⊓ K) := le_oddCoreIn_sup_inf_normalizer d.R_sylow
  have hNX : σ.N ≤ Subgroup.normalizer (X : Set G) := by
    refine hNfr.trans (sup_le (fun o ho => Subgroup.le_normalizer (Subgroup.mem_sup_right ho)) ?_)
    have h1 : σ.N ⊓ K ≤ Subgroup.normalizer (A : Set G) :=
      (le_inf (inf_le_right.trans ((le_inf hKY (le_normalizer_solvRadIn K)).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)))
        (inf_le_left.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    exact (le_inf h1 (inf_le_left.trans σ.N_le_normalizer_ON)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hXS : ¬ X ≤ solvRadIn σ.N := by
    intro hle
    apply hY
    intro y hy
    have hyK : y ∈ oddCoreIn K ⊔ (K ⊓ σ.N) := hfac.symm ▸ hYK hy
    obtain ⟨o, ho, n, hn, rfl⟩ :=
      exists_mul_of_mem_sup (inf_le_left.trans (le_normalizer_oddCoreIn K)) hyK
    have hnA : n ∈ A := by
      refine ⟨?_, hn.2⟩
      have h1 : n = o⁻¹ * (o * n) := by group
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hOKS (inv_mem ho)))
        (Subgroup.mem_sup_left hy)
    have hnS : n ∈ solvRadIn K := hKSN n hn.1 (hSN ▸ hle (Subgroup.mem_sup_left hnA))
    exact Subgroup.mul_mem _ (hOKS ho) hnS
  have hL := hII.N_minimalNormal X hXN hNX hXS
  intro l hl
  obtain ⟨hlL, hlK⟩ := Subgroup.mem_inf.mp hl
  have hlX : l ∈ A ⊔ (σ.ON ⊔ centerOf σ.D) := by
    have h1 := hL hlL
    rw [hSN] at h1
    have h2 : X ⊔ (σ.ON ⊔ centerOf σ.D) ≤ A ⊔ (σ.ON ⊔ centerOf σ.D) :=
      sup_le (sup_le le_sup_left (le_sup_of_le_right le_sup_left)) le_sup_right
    exact h2 h1
  have hAS : A ≤ Subgroup.normalizer ((σ.ON ⊔ centerOf σ.D : Subgroup G) : Set G) := by
    rw [← hSN]
    exact inf_le_right.trans (le_normalizer_solvRadIn σ.N)
  obtain ⟨a, ha, m, hm, rfl⟩ := exists_mul_of_mem_sup' hAS hlX
  have hmK : m ∈ K := by
    have := K.mul_mem (K.inv_mem (hAK ha)) hlK
    simpa using this
  exact Subgroup.mul_mem _ ha.1 (Subgroup.mem_sup_right (hKSN m hmK hm))

end NormalizerR

section UV

variable {σ}

private theorem IV9UV.isPGroup_U {r : ℕ} {d : σ.IV7Data r} (e : σ.IV9UV d) : IsPGroup r e.U :=
  d.R_sylow.isPGroup.to_le e.U_le

private theorem IV9UV.V_le_U {r : ℕ} {d : σ.IV7Data r} (e : σ.IV9UV d) : e.V ≤ e.U :=
  e.V_lt.le

private theorem IV9UV.P_le_normalizer_U {r : ℕ} {d : σ.IV7Data r} (e : σ.IV9UV d) :
    d.P ≤ Subgroup.normalizer (e.U : Set G) :=
  d.R_P.trans e.U_normal

private theorem IV9UV.P_le_normalizer_V {r : ℕ} {d : σ.IV7Data r} (e : σ.IV9UV d) :
    d.P ≤ Subgroup.normalizer (e.V : Set G) :=
  d.R_P.trans e.V_normal

private theorem IV9UV.x_mem_centralizer_U {r : ℕ} {d : σ.IV7Data r} (e : σ.IV9UV d) :
    σ.x ∈ Subgroup.centralizer (e.U : Set G) :=
  σ.x_mem_centralizer_of_le_ON (e.U_le.trans d.R_sylow.le)

private theorem inf_eq_C_inf_of_le_R {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r)
    {X : Subgroup G} (hXR : X ≤ d.R) (hPX : d.P ≤ Subgroup.normalizer (X : Set G)) :
    d.P ⊓ X = σ.C ⊓ X := by
  have : Fact r.Prime := ⟨hr.prime⟩
  apply le_antisymm (inf_le_inf_right X d.P_sylow.le)
  have hPCX : d.P ≤ Subgroup.normalizer ((σ.C ⊓ X : Subgroup G) : Set G) :=
    (le_inf (d.P_sylow.le.trans Subgroup.le_normalizer) hPX).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hgrp : IsPGroup r ((σ.C ⊓ X) ⊔ d.P : Subgroup G) :=
    isPGroup_sup_of_le_normalizer (d.R_sylow.isPGroup.to_le (inf_le_right.trans hXR))
      (σ.isPGroup_P d) hPCX
  have heq := d.P_sylow.eq_of_le le_sup_right (sup_le inf_le_left d.P_sylow.le) hgrp
  have hle : σ.C ⊓ X ≤ d.P := by rw [← heq]; exact le_sup_left
  exact le_inf hle inf_le_right

theorem lemmaIV97_ii {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r) (e : σ.IV9UV d) :
    d.P ⊓ e.U = σ.C ⊓ e.U ∧ d.P ⊓ e.V = σ.C ⊓ e.V :=
  ⟨inf_eq_C_inf_of_le_R hr d e.U_le e.P_le_normalizer_U,
    inf_eq_C_inf_of_le_R hr d (e.V_le_U.trans e.U_le) e.P_le_normalizer_V⟩

theorem IV9UV.not_mem_centralizer_U (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) {d : σ.IV7Data r} (hc : σ.Constrained r) (e : σ.IV9UV d) {u : G}
    (huD : u ∈ σ.D) (hu : u ∉ centerOf σ.D) : u ∉ Subgroup.centralizer (e.U : Set G) :=
  fun huC => hu (σ.mem_centerOf_D_of_mem_solvRadIn_K hσ hII hr d hc huD
    (e.U_centralizer ⟨d.R_D huD, huC⟩))

theorem IV9UV.U_ne_bot (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) {d : σ.IV7Data r} (hc : σ.Constrained r) (e : σ.IV9UV d) :
    e.U ≠ ⊥ := by
  intro hU
  apply e.not_mem_centralizer_U hσ hII hr hc (σ.T_le_D hσ σ.x₂_mem_T)
    (σ.x₂_not_mem_centerOf_D hσ hII)
  rw [hU, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
  rw [hh, one_mul, mul_one]

theorem IV9UV.eq_U_of_not_mem_centralizer (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : σ.HypIV7 r) {d : σ.IV7Data r} (hc : σ.Constrained r) (hqd : σ.height = 1)
    (e : σ.IV9UV d) {y : G} (hyD : y ∈ σ.D) (hyL : y ∈ σ.L₀) {W : Subgroup G}
    (hWn : Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G))
    (hWU : W ≤ e.U) (hy : y ∉ Subgroup.centralizer (W : Set G)) : W = e.U := by
  by_contra hne
  set K := Subgroup.normalizer (d.R : Set G) with hKdef
  have hDK : σ.D ≤ K := d.R_D
  have hlt : W < e.U := lt_of_le_of_ne hWU hne
  have hnot := e.U_minimal W hWn hlt
  set A := K ⊓ Subgroup.centralizer (W : Set G) with hAdef
  have hKA : K ≤ Subgroup.normalizer (A : Set G) :=
    (le_inf Subgroup.le_normalizer (hWn.trans (normalizer_le_normalizer_centralizer W))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hyA := σ.L₀_inf_le_sup_solvRadIn_K hσ hII hr d hc inf_le_left hKA hnot ⟨hyL, hDK hyD⟩
  rw [(σ.lemmaIV96 hσ hII hr d hc).2] at hyA
  have hZA : centerOf σ.D ≤ A := by
    refine le_inf (inf_le_left.trans hDK) ((σ.centerOf_D_le_zpowers_x hσ hII hqd).trans ?_)
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWU) e.x_mem_centralizer_U
  have hyB : y ∈ oddCoreIn K ⊔ A := by
    have h1 : A ⊔ (oddCoreIn K ⊔ centerOf σ.D) ≤ oddCoreIn K ⊔ A :=
      sup_le le_sup_right (sup_le le_sup_left (hZA.trans le_sup_right))
    exact h1 hyA
  have hOA : oddCoreIn K ≤ Subgroup.normalizer (A : Set G) := (oddCoreIn_le K).trans hKA
  have hyA' : y ∈ A := by
    apply mem_of_coprime_orderOf_relIndex le_sup_right
      (sup_le hOA Subgroup.le_normalizer) hyB
    rw [relIndex_sup_right_of_le_normalizer hOA]
    obtain ⟨k, hk⟩ := exists_orderOf_eq_pow_of_mem σ.isPGroup_two_D hyD
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr
      ((odd_card_oddCoreIn K).of_dvd_nat (Subgroup.relIndex_dvd_card _ _)))
  exact hy hyA'.2

private theorem IV9UV.exponent_and_class (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) {d : σ.IV7Data r} (hc : σ.Constrained r) (hqd : σ.height = 1)
    (e : σ.IV9UV d) {y : G} (hyD : y ∈ σ.D) (hyL : y ∈ σ.L₀) (hyZ : y ∉ centerOf σ.D) :
    (∀ u ∈ e.U, u ^ r = 1) ∧ ⁅e.U, e.U⁆ ≤ centerOf e.U := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have hr2 := σ.prime_ne_two_of_hyp hr
  have hnt : Nontrivial e.U := (Subgroup.nontrivial_iff_ne_bot _).mpr (e.U_ne_bot hσ hII hr hc)
  have hUp : IsPGroup r e.U := e.isPGroup_U
  obtain ⟨D₁, hD₁char, -, hD₁comm, hD₁exp, hD₁fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (P := e.U) hr2 hUp
  set W := D₁.map e.U.subtype with hWdef
  have hWU : W ≤ e.U := Subgroup.map_subtype_le _
  have hWsub : W.subgroupOf e.U = D₁ := by
    rw [hWdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective e.U.subtype_injective]
  have hWn : Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) := by
    intro g hg
    have hchar : (W.subgroupOf e.U).Characteristic := by rw [hWsub]; exact hD₁char
    exact mem_normalizer_of_characteristic hWU hchar (e.U_normal hg)
  have hyW : y ∉ Subgroup.centralizer (W : Set G) := by
    intro hyC
    obtain ⟨k, hk⟩ := exists_orderOf_eq_pow_of_mem σ.isPGroup_two_D hyD
    have hy2 : y ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
    exact e.not_mem_centralizer_U hσ hII hr hc hyD hyZ
      (mem_centralizer_of_isPGroup_fixingSubgroup hr2 hD₁fix (e.U_normal (d.R_D hyD)) hy2 hyC)
  have hWeq := e.eq_U_of_not_mem_centralizer hσ hII hr hc hqd hyD hyL hWn hWU hyW
  refine ⟨?_, ?_⟩
  · intro u hu
    rw [← hWeq] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    have h1 := congrArg Subtype.val (hD₁exp v hv)
    simpa using h1
  · rw [← hWeq]
    have hmap : ⁅W, W⁆ ≤ (⁅D₁, (⊤ : Subgroup e.U)⁆).map e.U.subtype := by
      rw [Subgroup.map_commutator, ← hWdef]
      apply Subgroup.commutator_mono le_rfl
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hWU
    refine hmap.trans ?_
    rintro _ ⟨c, hc', rfl⟩
    obtain ⟨hcD, hcC⟩ := hD₁comm hc'
    refine ⟨⟨c, hcD, rfl⟩, ?_⟩
    show (c : G) ∈ Subgroup.centralizer (W : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hcC) w hw)

theorem exists_sylow_two_le_normalizer_R (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r) :
    ∃ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) ∧
      (S₁ : Subgroup G) ≤ Subgroup.normalizer (d.R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.normalizer (d.R : Set G) with hKdef
  have hKL := σ.normalizer_R_mem_familyL hσ hr d
  obtain ⟨-, -, -, ⟨P₂, hP₂⟩, -⟩ := σ.familyL_properties hσ hII hr.prime hr.dvd_ON hKL
  have hDK : σ.D ≤ K := d.R_D
  obtain ⟨Q, hQ⟩ := (σ.isPGroup_two_D.comap_subtype (K := K)).exists_le_sylow
  set S₁' := (Q : Subgroup K).map K.subtype with hS₁'
  have hS₁'K : IsSylowOf 2 S₁' K := ⟨Q, rfl⟩
  have hP₂K : IsSylowOf 2 (P₂ : Subgroup G) K :=
    isSylowOf_iff.mpr ⟨hP₂.trans inf_le_left, P₂.isPGroup', fun hdvd =>
      P₂.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le
        (hP₂.trans inf_le_left)))⟩
  have hcard : Nat.card S₁' = 2 ^ (Nat.card G).factorization 2 := by
    rw [hS₁'K.card_eq, ← hP₂K.card_eq, Sylow.card_eq_multiplicity]
  refine ⟨Sylow.ofCard S₁' hcard, ?_, ?_⟩
  · rw [Sylow.coe_ofCard, hS₁', ← Subgroup.map_subgroupOf_eq_of_le hDK]
    exact Subgroup.map_mono hQ
  · rw [Sylow.coe_ofCard]
    exact Subgroup.map_subtype_le _

private theorem IV9UV.P_inf_U_ne_bot (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) {d : σ.IV7Data r} (hc : σ.Constrained r) (e : σ.IV9UV d) {y : G}
    (hyD : y ∈ σ.D) (hyZ : y ∉ centerOf σ.D)
    (hys : ∀ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) →
      ∃ s ∈ (S₁ : Subgroup G), y = σ.x₂ * (s * σ.x₂ * s⁻¹)) :
    d.P ⊓ e.U ≠ ⊥ := by
  intro hbot
  set K := Subgroup.normalizer (d.R : Set G) with hKdef
  obtain ⟨S₁, hDS₁, hS₁K⟩ := σ.exists_sylow_two_le_normalizer_R hσ hII hr d
  obtain ⟨s, hsS₁, hys'⟩ := hys S₁ hDS₁
  have hsK : s ∈ K := hS₁K hsS₁
  have hCU : σ.C ⊓ e.U = ⊥ := by rw [← (lemmaIV97_ii hr d e).1]; exact hbot
  have hx₂D : σ.x₂ ∈ σ.D := σ.T_le_D hσ σ.x₂_mem_T
  have hfix : e.U ⊓ Subgroup.centralizer ({σ.x₂} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have huC : u ∈ σ.C := by
      rw [Setting.C, σ.mem_centralizer_T_iff]
      refine ⟨?_, (Subgroup.mem_centralizer_singleton_iff.mp hu.2).symm⟩
      exact ((Subgroup.mem_centralizer_iff.mp e.x_mem_centralizer_U) u hu.1).symm
    have h1 : u ∈ σ.C ⊓ e.U := ⟨huC, hu.1⟩
    rwa [hCU] at h1
  have hUodd : Odd (Nat.card e.U) := σ.odd_card_of_isPGroup_hyp hr e.isPGroup_U
  have hinv : ∀ u ∈ e.U, σ.x₂ * u * σ.x₂⁻¹ = u⁻¹ := by
    intro u hu
    have hdec := (odd_fixed_mul_inverted hUodd hσ.x₂_order (e.U_normal (d.R_D hx₂D))).1
    have hu' : u ∈ (e.U : Set G) := hu
    rw [hdec, hfix] at hu'
    obtain ⟨a, ha, b, hb, rfl⟩ := hu'
    rw [SetLike.mem_coe, Subgroup.mem_bot] at ha
    beta_reduce
    rw [ha, one_mul]
    exact (OddInversion.mem_invertedSet.mp hb).2
  apply hyZ
  apply σ.mem_centerOf_D_of_mem_solvRadIn_K hσ hII hr d hc hyD
  apply e.U_centralizer
  refine ⟨d.R_D hyD, ?_⟩
  show y ∈ Subgroup.centralizer (e.U : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hsu : s⁻¹ * u * s ∈ e.U := by
    have := conj_mem_of_mem_normalizer (e.U_normal (K.inv_mem hsK)) hu
    simpa using this
  have h1 : (s * σ.x₂ * s⁻¹) * u * (s * σ.x₂ * s⁻¹)⁻¹ = u⁻¹ := by
    calc (s * σ.x₂ * s⁻¹) * u * (s * σ.x₂ * s⁻¹)⁻¹
        = s * (σ.x₂ * (s⁻¹ * u * s) * σ.x₂⁻¹) * s⁻¹ := by group
      _ = s * (s⁻¹ * u * s)⁻¹ * s⁻¹ := by rw [hinv _ hsu]
      _ = u⁻¹ := by group
  have h2 : y * u * y⁻¹ = u := by
    rw [hys']
    calc σ.x₂ * (s * σ.x₂ * s⁻¹) * u * (σ.x₂ * (s * σ.x₂ * s⁻¹))⁻¹
        = σ.x₂ * ((s * σ.x₂ * s⁻¹) * u * (s * σ.x₂ * s⁻¹)⁻¹) * σ.x₂⁻¹ := by group
      _ = σ.x₂ * u⁻¹ * σ.x₂⁻¹ := by rw [h1]
      _ = (σ.x₂ * u * σ.x₂⁻¹)⁻¹ := by group
      _ = u := by rw [hinv u hu, inv_inv]
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

omit [Finite G] in
private theorem isKleinFour_T_of_subgroupOf {H : Subgroup G} (hTH : σ.T ≤ H)
    (h : IsKleinFour (σ.T.subgroupOf H)) : IsKleinFour σ.T := by
  let e : σ.T.subgroupOf H ≃* σ.T := Subgroup.subgroupOfEquivOfLe hTH
  exact ⟨by rw [← Nat.card_congr e.toEquiv]; exact h.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact h.exponent_two⟩

private theorem IV9UV.P_inf_V_eq_bot (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) {d : σ.IV7Data r} (hc : σ.Constrained r) (hqd : σ.height = 1)
    (e : σ.IV9UV d)
    (h95 : IsDGroupWrt (σ.T.subgroupOf
      (Subgroup.normalizer (d.Q : Set G) ⊓ Subgroup.centralizer (d.P : Set G)))) :
    d.P ⊓ e.V = ⊥ := by
  by_contra hne
  set Y := d.P ⊓ e.V with hYdef
  set H₂ := Subgroup.normalizer (Y : Set G) with hH₂def
  set K := Subgroup.normalizer (d.R : Set G) with hKdef
  have hYr : IsPGroup r Y := (σ.isPGroup_P d).to_inf_left
  have hloc : IsPLocal r H₂ := ⟨Y, hne, hYr, rfl⟩
  have hCY : Subgroup.centralizer (d.P : Set G) ≤ H₂ :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hTP := σ.T_le_centralizer_P d
  have hT : σ.T ≤ H₂ := hTP.trans hCY
  have hTHC : σ.T ≤ Subgroup.normalizer (d.Q : Set G) ⊓ Subgroup.centralizer (d.P : Set G) :=
    le_inf ((σ.T_le_D hσ).trans (σ.D_le_normalizer_Q d)) hTP
  have h3 : 3 ∣ automizerIndex (σ.T.subgroupOf H₂) :=
    three_dvd_automizerIndex_mono hTHC (inf_le_right.trans hCY) h95.2.2
  have hKlein : IsKleinFour σ.T := σ.isKleinFour_T_of_subgroupOf hTHC h95.2.1
  set X := K ⊓ Subgroup.centralizer (e.V : Set G) with hXdef
  have hXH₂ : X ≤ H₂ :=
    inf_le_right.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hKX : K ≤ Subgroup.normalizer (X : Set G) :=
    (le_inf Subgroup.le_normalizer
      (e.V_normal.trans (normalizer_le_normalizer_centralizer e.V))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hXS : ¬ X ≤ solvRadIn K := e.U_minimal e.V e.V_normal e.V_lt
  have hKL := σ.normalizer_R_mem_familyL hσ hr d
  obtain ⟨-, -, -, -, ⟨hON1, -⟩, -⟩ := σ.familyL_properties hσ hII hr.prime hr.dvd_ON hKL
  have hDK : σ.D ≤ K := hKL.2.2.1
  have hxK : σ.x ∈ K := hDK (σ.T_le_D hσ σ.x_mem_T)
  have hxX : σ.x ∈ X :=
    ⟨hxK, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (e.V_le_U)) e.x_mem_centralizer_U⟩
  have hZX : centerOf σ.D ≤ X :=
    (σ.centerOf_D_le_zpowers_x hσ hII hqd).trans (Subgroup.zpowers_le.mpr hxX)
  have hOX : oddCoreIn K ≤ Subgroup.normalizer (X : Set G) := (oddCoreIn_le K).trans hKX
  have hL₀K : σ.L₀ ⊓ K ≤ X ⊔ oddCoreIn K := by
    have h1 := σ.L₀_inf_le_sup_solvRadIn_K hσ hII hr d hc inf_le_left hKX hXS
    rw [(σ.lemmaIV96 hσ hII hr d hc).2] at h1
    exact h1.trans (sup_le le_sup_left (sup_le le_sup_right (hZX.trans le_sup_left)))
  have hxx : σ.x * σ.x = 1 := by rw [← pow_two, ← hσ.x_order, pow_orderOf_eq_one]
  have hcov : (σ.L₀ : Set G) ⊆ (H₂ : Set G) * (σ.ON : Set G) := by
    intro l hl
    obtain ⟨k, hk, o, ho, rfl⟩ := hKL.2.1 hl
    have hkL : k ∈ σ.L₀ := by
      have := σ.L₀.mul_mem hl (σ.L₀.inv_mem (hσ.ON_le_L₀ ho))
      simpa using this
    obtain ⟨a, ha, o₁, ho₁, rfl⟩ := exists_mul_of_mem_sup hOX (hL₀K ⟨hkL, hk⟩)
    have hkN : a * o₁ ∈ σ.N := hσ.L₀_le_N hkL
    have hxk : σ.x * (a * o₁) * σ.x⁻¹ = a * o₁ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact ((σ.mem_N_iff _).mp hkN).symm
    have hxO : σ.x ∈ Subgroup.normalizer (oddCoreIn K : Set G) := le_normalizer_oddCoreIn K hxK
    have hcX : a⁻¹ * (σ.x * a * σ.x⁻¹) ∈ X :=
      X.mul_mem (X.inv_mem ha) (conj_mem_of_mem_normalizer (hKX hxK) ha)
    have hcO : a⁻¹ * (σ.x * a * σ.x⁻¹) ∈ oddCoreIn K := by
      have e1 : a⁻¹ * (σ.x * a * σ.x⁻¹) = o₁ * (σ.x * o₁ * σ.x⁻¹)⁻¹ := by
        have h2 : σ.x * a * σ.x⁻¹ * (σ.x * o₁ * σ.x⁻¹) = a * o₁ := by
          rw [← hxk]; group
        calc a⁻¹ * (σ.x * a * σ.x⁻¹)
            = a⁻¹ * (σ.x * a * σ.x⁻¹ * (σ.x * o₁ * σ.x⁻¹)) * (σ.x * o₁ * σ.x⁻¹)⁻¹ := by group
          _ = a⁻¹ * (a * o₁) * (σ.x * o₁ * σ.x⁻¹)⁻¹ := by rw [h2]
          _ = o₁ * (σ.x * o₁ * σ.x⁻¹)⁻¹ := by group
      rw [e1]
      exact (oddCoreIn K).mul_mem ho₁
        ((oddCoreIn K).inv_mem (conj_mem_of_mem_normalizer hxO ho₁))
    set O₂ := X ⊓ oddCoreIn K with hO₂def
    have hO₂odd : Odd (Nat.card O₂) :=
      (odd_card_oddCoreIn K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    have hO₂n : a ∈ Subgroup.normalizer (O₂ : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer ha, le_normalizer_oddCoreIn K ha.1⟩
    have hax : a * σ.x * a⁻¹ * σ.x⁻¹ ∈ O₂ := by
      have h1 := conj_mem_of_mem_normalizer hO₂n (O₂.inv_mem ⟨hcX, hcO⟩)
      convert h1 using 1
      group
    obtain ⟨m, hm, hmC⟩ := exists_mem_inv_mul_mem_centralizer_of_odd hO₂odd hxx hax
    have ha' : m⁻¹ * a ∈ X := X.mul_mem (X.inv_mem hm.1) ha
    have ho' : (m⁻¹ * a)⁻¹ * (a * o₁) ∈ σ.ON := by
      apply hON1
      refine ⟨?_, ?_⟩
      · have e2 : (m⁻¹ * a)⁻¹ * (a * o₁) = (a⁻¹ * m * a) * o₁ := by group
        have hm' := conj_mem_of_mem_normalizer (le_normalizer_oddCoreIn K (K.inv_mem ha.1)) hm.2
        rw [inv_inv] at hm'
        rw [e2]
        exact (oddCoreIn K).mul_mem hm' ho₁
      · exact σ.N.mul_mem (σ.N.inv_mem hmC) hkN
    refine ⟨m⁻¹ * a, hXH₂ ha', (m⁻¹ * a)⁻¹ * (a * o₁) * o, σ.ON.mul_mem ho' ho, ?_⟩
    group
  have hO₂ : oddCoreIn H₂ ≠ ⊥ :=
    oddCoreIn_ne_bot_of_isPLocal hr.prime (σ.prime_ne_two_of_hyp hr) hloc
  obtain ⟨hq, -⟩ := hII.cover_qgroup H₂ hT hO₂ hcov
  exact hII.qgroup_no_three H₂ hq.1 σ.T hT hKlein h3

theorem lemmaIV97_i (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    {d : σ.IV7Data r} (hc : σ.Constrained r) (hqd : σ.height = 1) (e : σ.IV9UV d)
    (h_y : σ.height = 1 → ∃ y ∈ σ.D, y ∉ centerOf σ.D ∧ y ∈ σ.L₀ ∧
      ∀ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) →
        ∃ s ∈ (S₁ : Subgroup G), y = σ.x₂ * (s * σ.x₂ * s⁻¹)) :
    (∀ u ∈ e.U, u ^ r = 1) ∧ ⁅e.U, e.U⁆ ≤ centerOf e.U := by
  obtain ⟨y, hyD, hyZ, hyL, -⟩ := h_y hqd
  exact e.exponent_and_class hσ hII hr hc hqd hyD hyL hyZ

theorem lemmaIV97_iii (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    {d : σ.IV7Data r} (hc : σ.Constrained r)
    (hQ : ¬ PConstrainedWithin r (Subgroup.normalizer (d.Q : Set G))
      (CFSG.oddCore (Subgroup.normalizer (d.Q : Set G))))
    (h81 : σ.LemmaIV81) (h83 : σ.LemmaIV83)
    (h92 : ∀ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K) ↔
      ∃ X : Subgroup G, IsSylowOf r X (oddCoreIn K) ∧ σ.T ≤ Subgroup.normalizer (X : Set G) ∧
        ¬ σ.T ≤ Subgroup.centralizer (X : Set G))
    (h_II34 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      (∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.T ≤ Subgroup.normalizer (X : Set G) →
          X ≤ oddCoreIn H) ∨
        ((∀ Y : Subgroup G, Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) → oddCoreIn H ≤ Y →
            Y = oddCoreIn H ∨ Y = H) ∧
          ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.D ≤ Subgroup.normalizer (X : Set G) →
            ∃ T₁ : Subgroup G, T₁ ≤ σ.D ∧ IsKleinFour T₁ ∧ ⁅X, T₁⁆ ≤ oddCoreIn H) ∨
        (σ.height = 1 ∧ ∃ q₁ : ℕ, 3 < q₁ ∧ IsLinearTypeWrt σ.T H q₁))
    (h_II57 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      IsLinearTypeWrt σ.T H 9 → H ⊓ Subgroup.centralizer (σ.T : Set G) ≤ σ.T ⊔ oddCoreIn H)
    (h_II56 : ∀ (M Z W : Subgroup G) (F : Type) [Field F] [Finite F], Z ≤ M → W ≤ Z →
      M ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card Z) → ⁅Z, M⁆ ≤ W →
      Odd (Nat.card F) → 3 < Nat.card F → Nat.card F ≠ 9 →
      (∃ ψ : M →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = Z.subgroupOf M) →
        ⁅M, M⁆ ⊓ Z ≤ W ∧ ⁅M, M⁆ ⊔ Z = M)
    (h_II58 : ∀ (J W A : Subgroup G) (F : Type) [Field F] [Finite F], W ≤ J →
      J ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card W) → Odd (Nat.card F) →
      3 < Nat.card F →
      (∃ ψ : J →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = W.subgroupOf J) →
      σ.T ≤ J → IsPGroup r A → A ≤ Subgroup.normalizer (J : Set G) →
      A ≤ Subgroup.normalizer (W : Set G) → A ≤ Subgroup.centralizer (σ.T : Set G) →
        ∃ g ∈ J, (∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ W) ∧
          g ∈ Subgroup.normalizer ((σ.T ⊔ W : Subgroup G) : Set G) ∧
          (∀ t ∈ σ.T, g ^ 3 * t * (g ^ 3)⁻¹ * t⁻¹ ∈ W) ∧ ∃ t ∈ σ.T, g * t * g⁻¹ * t⁻¹ ∉ W)
    (e : σ.IV9UV d)
    (h_y : σ.height = 1 → ∃ y ∈ σ.D, y ∉ centerOf σ.D ∧ y ∈ σ.L₀ ∧
      ∀ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) →
        ∃ s ∈ (S₁ : Subgroup G), y = σ.x₂ * (s * σ.x₂ * s⁻¹)) :
    d.P ⊓ e.U ≠ ⊥ ∧ d.P ⊓ e.V = ⊥ := by
  have hqd := (σ.lemmaIV95_i hσ hII hr d hc hQ h81 h83 h92 h_II34).1
  obtain ⟨y, hyD, hyZ, -, hys⟩ := h_y hqd
  have h95 := σ.lemmaIV95_iii hσ hII hr d hc hQ h81 h83 h92 h_II34 h_II57 h_II56 h_II58
  exact ⟨e.P_inf_U_ne_bot hσ hII hr hc hyD hyZ hys, e.P_inf_V_eq_bot hσ hII hr hc hqd h95⟩

private theorem IV9UV.not_T_le_centralizer_normalizer (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : σ.HypIV7 r) {d : σ.IV7Data r} (hc : σ.Constrained r) (e : σ.IV9UV d) :
    ¬ σ.T ≤ Subgroup.centralizer
      ((e.U ⊓ Subgroup.normalizer ((d.P ⊓ e.U : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have hPU : d.P ⊓ e.U = σ.C ⊓ e.U := (lemmaIV97_ii hr d e).1
  have hlt : d.P ⊓ e.U < e.U := by
    refine lt_of_le_of_ne inf_le_right fun heq => ?_
    apply e.not_mem_centralizer_U hσ hII hr hc (σ.T_le_D hσ σ.x₂_mem_T)
      (σ.x₂_not_mem_centerOf_D hσ hII)
    have hUC : e.U ≤ σ.C := by
      rw [← heq, hPU]
      exact inf_le_left
    exact (Subgroup.le_centralizer_iff.mp hUC) σ.x₂_mem_T
  have hgrow := lt_inf_normalizer_of_lt e.isPGroup_U hlt
  intro hT
  apply (lt_iff_le_not_ge.mp hgrow).2
  intro a ha
  have haC : a ∈ σ.C := (Subgroup.le_centralizer_iff.mp hT) ha
  rw [hPU]
  exact ⟨haC, ha.1⟩

theorem IV9UV.C_inf_K_le_H₁ {r : ℕ} (hr : σ.HypIV7 r) {d : σ.IV7Data r}
    (e : σ.IV9UV d) : σ.C ⊓ Subgroup.normalizer (d.R : Set G) ≤ e.H₁ := by
  intro g hg
  rw [IV9UV.H₁, (lemmaIV97_ii hr d e).1]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hg.1, e.U_normal hg.2⟩

theorem IV9UV.C_inf_L_subset (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) {d : σ.IV7Data r} (e : σ.IV9UV d) :
    ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
      (e.H₁ : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.normalizer (d.R : Set G) with hKdef
  have hKL := σ.normalizer_R_mem_familyL hσ hr d
  have hDK : σ.D ≤ K := hKL.2.2.1
  have hTK : σ.T ≤ K := (σ.T_le_D hσ).trans hDK
  have hcov := σ.L_subset_inf_N_mul_ON_of_cover hσ hII hDK hKL.2.1
  rintro c ⟨hcC, hcL⟩
  obtain ⟨k, hk, o, ho, rfl⟩ := hcov hcL
  set W := K ⊓ σ.ON with hWdef
  have hWodd : Odd (Nat.card W) := σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hTW : σ.T ≤ Subgroup.normalizer (W : Set G) :=
    (le_inf (hTK.trans Subgroup.le_normalizer) ((σ.T_le_N hσ).trans σ.N_le_normalizer_ON)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hcomm : ∀ a ∈ σ.T, a * (k * o) = (k * o) * a :=
    fun a ha => (Subgroup.mem_centralizer_iff.mp hcC) a ha
  have hkg : ∀ a ∈ σ.T, a * k * a⁻¹ * k⁻¹ ∈ W := by
    intro a ha
    refine ⟨K.mul_mem (K.mul_mem (K.mul_mem (hTK ha) hk.1) (K.inv_mem (hTK ha))) (K.inv_mem hk.1),
      ?_⟩
    have haN : a ∈ σ.N := σ.T_le_N hσ ha
    have hkN : k ∈ σ.N := hk.2
    have e1 : a * k * a⁻¹ * k⁻¹ = (k * o) * (a * o⁻¹ * a⁻¹ * o) * (k * o)⁻¹ * (k * o * k⁻¹) *
        (k * o * k⁻¹)⁻¹ := by
      have h1 : a * (k * o) * a⁻¹ = k * o := by
        rw [hcomm a ha]; group
      calc a * k * a⁻¹ * k⁻¹ = (a * (k * o) * a⁻¹) * (a * o⁻¹ * a⁻¹) * k⁻¹ := by group
        _ = (k * o) * (a * o⁻¹ * a⁻¹) * k⁻¹ := by rw [h1]
        _ = (k * o) * (a * o⁻¹ * a⁻¹ * o) * (k * o)⁻¹ * (k * o * k⁻¹) * (k * o * k⁻¹)⁻¹ := by
            group
    rw [e1, mul_inv_cancel_right]
    have hin : a * o⁻¹ * a⁻¹ * o ∈ σ.ON :=
      σ.ON.mul_mem (conj_mem_of_mem_normalizer (σ.N_le_normalizer_ON haN) (σ.ON.inv_mem ho)) ho
    exact conj_mem_of_mem_normalizer
      (σ.N_le_normalizer_ON (σ.N.mul_mem hkN (σ.ON_le_N ho))) hin
  obtain ⟨w, hw, hwk⟩ := exists_mem_inv_mul_mem_centralizer_of_coprime (σ.isPGroup_two_T hσ)
    (Nat.coprime_two_left.mpr hWodd) hTW hkg
  refine ⟨w⁻¹ * k, e.C_inf_K_le_H₁ hr ⟨hwk, K.mul_mem (K.inv_mem hw.1) hk.1⟩,
    (w⁻¹ * k)⁻¹ * (k * o), ⟨?_, ?_⟩, by group⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hwk) hcC
  · have e2 : (w⁻¹ * k)⁻¹ * (k * o) = (k⁻¹ * w * k) * o := by group
    rw [e2]
    have h0 := conj_mem_of_mem_normalizer (σ.N_le_normalizer_ON (σ.N.inv_mem hk.2)) hw.2
    exact σ.ON.mul_mem (by simpa using h0) ho

theorem lemmaIV97 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    {d : σ.IV7Data r} (hc : σ.Constrained r)
    (hQ : ¬ PConstrainedWithin r (Subgroup.normalizer (d.Q : Set G))
      (CFSG.oddCore (Subgroup.normalizer (d.Q : Set G))))
    (h81 : σ.LemmaIV81) (h83 : σ.LemmaIV83)
    (h92 : ∀ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K) ↔
      ∃ X : Subgroup G, IsSylowOf r X (oddCoreIn K) ∧ σ.T ≤ Subgroup.normalizer (X : Set G) ∧
        ¬ σ.T ≤ Subgroup.centralizer (X : Set G))
    (h_II34 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      (∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.T ≤ Subgroup.normalizer (X : Set G) →
          X ≤ oddCoreIn H) ∨
        ((∀ Y : Subgroup G, Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) → oddCoreIn H ≤ Y →
            Y = oddCoreIn H ∨ Y = H) ∧
          ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.D ≤ Subgroup.normalizer (X : Set G) →
            ∃ T₁ : Subgroup G, T₁ ≤ σ.D ∧ IsKleinFour T₁ ∧ ⁅X, T₁⁆ ≤ oddCoreIn H) ∨
        (σ.height = 1 ∧ ∃ q₁ : ℕ, 3 < q₁ ∧ IsLinearTypeWrt σ.T H q₁))
    (h_II57 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      IsLinearTypeWrt σ.T H 9 → H ⊓ Subgroup.centralizer (σ.T : Set G) ≤ σ.T ⊔ oddCoreIn H)
    (h_II56 : ∀ (M Z W : Subgroup G) (F : Type) [Field F] [Finite F], Z ≤ M → W ≤ Z →
      M ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card Z) → ⁅Z, M⁆ ≤ W →
      Odd (Nat.card F) → 3 < Nat.card F → Nat.card F ≠ 9 →
      (∃ ψ : M →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = Z.subgroupOf M) →
        ⁅M, M⁆ ⊓ Z ≤ W ∧ ⁅M, M⁆ ⊔ Z = M)
    (h_II58 : ∀ (J W A : Subgroup G) (F : Type) [Field F] [Finite F], W ≤ J →
      J ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card W) → Odd (Nat.card F) →
      3 < Nat.card F →
      (∃ ψ : J →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = W.subgroupOf J) →
      σ.T ≤ J → IsPGroup r A → A ≤ Subgroup.normalizer (J : Set G) →
      A ≤ Subgroup.normalizer (W : Set G) → A ≤ Subgroup.centralizer (σ.T : Set G) →
        ∃ g ∈ J, (∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ W) ∧
          g ∈ Subgroup.normalizer ((σ.T ⊔ W : Subgroup G) : Set G) ∧
          (∀ t ∈ σ.T, g ^ 3 * t * (g ^ 3)⁻¹ * t⁻¹ ∈ W) ∧ ∃ t ∈ σ.T, g * t * g⁻¹ * t⁻¹ ∉ W)
    (e : σ.IV9UV d)
    (h_y : σ.height = 1 → ∃ y ∈ σ.D, y ∉ centerOf σ.D ∧ y ∈ σ.L₀ ∧
      ∀ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) →
        ∃ s ∈ (S₁ : Subgroup G), y = σ.x₂ * (s * σ.x₂ * s⁻¹)) :
    ((∀ u ∈ e.U, u ^ r = 1) ∧ ⁅e.U, e.U⁆ ≤ centerOf e.U) ∧
      (d.P ⊓ e.U = σ.C ⊓ e.U ∧ d.P ⊓ e.V = σ.C ⊓ e.V) ∧
      (d.P ⊓ e.U ≠ ⊥ ∧ d.P ⊓ e.V = ⊥) :=
  ⟨σ.lemmaIV97_i hσ hII hr hc (σ.lemmaIV95_i hσ hII hr d hc hQ h81 h83 h92 h_II34).1 e h_y,
    lemmaIV97_ii hr d e,
    σ.lemmaIV97_iii hσ hII hr hc hQ h81 h83 h92 h_II34 h_II57 h_II56 h_II58 e
      h_y⟩

theorem lemmaIV98 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    {d : σ.IV7Data r} (hc : σ.Constrained r)
    (hQ : ¬ PConstrainedWithin r (Subgroup.normalizer (d.Q : Set G))
      (CFSG.oddCore (Subgroup.normalizer (d.Q : Set G))))
    (h81 : σ.LemmaIV81) (h83 : σ.LemmaIV83)
    (h92 : ∀ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K) ↔
      ∃ X : Subgroup G, IsSylowOf r X (oddCoreIn K) ∧ σ.T ≤ Subgroup.normalizer (X : Set G) ∧
        ¬ σ.T ≤ Subgroup.centralizer (X : Set G))
    (h_II34 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      (∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.T ≤ Subgroup.normalizer (X : Set G) →
          X ≤ oddCoreIn H) ∨
        ((∀ Y : Subgroup G, Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) → oddCoreIn H ≤ Y →
            Y = oddCoreIn H ∨ Y = H) ∧
          ∀ X : Subgroup G, X ≤ H → Odd (Nat.card X) → σ.D ≤ Subgroup.normalizer (X : Set G) →
            ∃ T₁ : Subgroup G, T₁ ≤ σ.D ∧ IsKleinFour T₁ ∧ ⁅X, T₁⁆ ≤ oddCoreIn H) ∨
        (σ.height = 1 ∧ ∃ q₁ : ℕ, 3 < q₁ ∧ IsLinearTypeWrt σ.T H q₁))
    (h_II57 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      IsLinearTypeWrt σ.T H 9 → H ⊓ Subgroup.centralizer (σ.T : Set G) ≤ σ.T ⊔ oddCoreIn H)
    (h_II56 : ∀ (M Z W : Subgroup G) (F : Type) [Field F] [Finite F], Z ≤ M → W ≤ Z →
      M ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card Z) → ⁅Z, M⁆ ≤ W →
      Odd (Nat.card F) → 3 < Nat.card F → Nat.card F ≠ 9 →
      (∃ ψ : M →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = Z.subgroupOf M) →
        ⁅M, M⁆ ⊓ Z ≤ W ∧ ⁅M, M⁆ ⊔ Z = M)
    (h_II58 : ∀ (J W A : Subgroup G) (F : Type) [Field F] [Finite F], W ≤ J →
      J ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card W) → Odd (Nat.card F) →
      3 < Nat.card F →
      (∃ ψ : J →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = W.subgroupOf J) →
      σ.T ≤ J → IsPGroup r A → A ≤ Subgroup.normalizer (J : Set G) →
      A ≤ Subgroup.normalizer (W : Set G) → A ≤ Subgroup.centralizer (σ.T : Set G) →
        ∃ g ∈ J, (∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ W) ∧
          g ∈ Subgroup.normalizer ((σ.T ⊔ W : Subgroup G) : Set G) ∧
          (∀ t ∈ σ.T, g ^ 3 * t * (g ^ 3)⁻¹ * t⁻¹ ∈ W) ∧ ∃ t ∈ σ.T, g * t * g⁻¹ * t⁻¹ ∉ W)
    (e : σ.IV9UV d)
    (h_y : σ.height = 1 → ∃ y ∈ σ.D, y ∉ centerOf σ.D ∧ y ∈ σ.L₀ ∧
      ∀ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) →
        ∃ s ∈ (S₁ : Subgroup G), y = σ.x₂ * (s * σ.x₂ * s⁻¹))

    (h_II52 : ∀ H : Subgroup G, σ.T ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ¬ Odd (Nat.card (pPrimeCoreIn r H)) → σ.T ≤ pPrimeCoreIn r H) :
    e.H₁ ∈ σ.familyMstar r ∧ d.P ≤ e.H₁ ∧
      ¬ σ.T ≤ Subgroup.centralizer
        ((e.U ⊓ Subgroup.normalizer ((d.P ⊓ e.U : Subgroup G) : Set G) : Subgroup G) :
          Set G) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have hqd := (σ.lemmaIV95_i hσ hII hr d hc hQ h81 h83 h92 h_II34).1
  have h95 := σ.lemmaIV95_iii hσ hII hr d hc hQ h81 h83 h92 h_II34 h_II57 h_II56 h_II58
  have hne := (σ.lemmaIV97_iii hσ hII hr hc hQ h81 h83 h92 h_II34 h_II57 h_II56 h_II58 e h_y).1
  have h3 := e.not_T_le_centralizer_normalizer hσ hII hr hc
  have hPH₁ : d.P ≤ e.H₁ :=
    (le_inf Subgroup.le_normalizer e.P_le_normalizer_U).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hDH₁ : σ.D ≤ e.H₁ :=
    (le_inf d.P_D (d.R_D.trans e.U_normal)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hTH₁ : σ.T ≤ e.H₁ := (σ.T_le_D hσ).trans hDH₁
  have hloc : IsPLocal r e.H₁ := ⟨d.P ⊓ e.U, hne, (σ.isPGroup_P d).to_inf_left, rfl⟩
  have hTP := σ.T_le_centralizer_P d
  have hTHC : σ.T ≤ Subgroup.normalizer (d.Q : Set G) ⊓ Subgroup.centralizer (d.P : Set G) :=
    le_inf ((σ.T_le_D hσ).trans (σ.D_le_normalizer_Q d)) hTP
  have hCH₁ : Subgroup.centralizer (d.P : Set G) ≤ e.H₁ :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have h3A : 3 ∣ automizerIndex (σ.T.subgroupOf e.H₁) :=
    three_dvd_automizerIndex_mono hTHC (inf_le_right.trans hCH₁) h95.2.2
  have hO : oddCoreIn e.H₁ ≠ ⊥ :=
    oddCoreIn_ne_bot_of_isPLocal hr.prime (σ.prime_ne_two_of_hyp hr) hloc
  have hDg : IsDGroupWrt (σ.T.subgroupOf e.H₁) := by
    rcases hII.qd_or_d_of_three e.H₁ hTH₁ (Or.inl hDH₁) h3A with hQD | hD
    · exact absurd hQD (hII.not_qd_of_cover e.H₁ hTH₁ hO (e.C_inf_L_subset hσ hII hr))
    · exact hD
  refine ⟨⟨hloc, hDH₁, hDg, ?_⟩, hPH₁, h3⟩
  by_contra hev
  have hTO := h_II52 e.H₁ hTH₁ hDg hev
  apply h3
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have haH : a ∈ e.H₁ := ha.2
  have h1 : t * a * t⁻¹ * a⁻¹ ∈ e.U :=
    e.U.mul_mem (conj_mem_of_mem_normalizer (e.U_normal (d.R_D (σ.T_le_D hσ ht))) ha.1)
      (e.U.inv_mem ha.1)
  have h2 : t * a * t⁻¹ * a⁻¹ ∈ pPrimeCoreIn r e.H₁ := by
    have h0 := conj_mem_of_mem_normalizer (le_normalizer_map_subtype e.H₁ _ haH)
      ((pPrimeCoreIn r e.H₁).inv_mem (hTO ht))
    have e1 : t * a * t⁻¹ * a⁻¹ = t * (a * t⁻¹ * a⁻¹) := by group
    rw [e1]
    exact (pPrimeCoreIn r e.H₁).mul_mem (hTO ht) h0
  have hbot : e.U ⊓ pPrimeCoreIn r e.H₁ = ⊥ :=
    inf_eq_bot_of_isPGroup_of_coprime e.isPGroup_U (coprime_card_pPrimeCoreIn e.H₁)
  have h4 : t * a * t⁻¹ * a⁻¹ ∈ e.U ⊓ pPrimeCoreIn r e.H₁ := ⟨h1, h2⟩
  rw [hbot, Subgroup.mem_bot] at h4
  have h5 : t * a * t⁻¹ = a := mul_inv_eq_one.mp h4
  rw [mul_inv_eq_iff_eq_mul] at h5
  exact h5.symm

end UV

end Setting

end CFSG.ABGTheoremB

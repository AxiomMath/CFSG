module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step44Model
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4NXAct
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step42
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Hexa CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native HeSylow

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem eq_xor_of_lt16 : ∀ v < 16, v = (v % 4) ^^^ (4 * (v / 4)) := by decide

theorem mem_oval0_of_lt4 : ∀ a < 4, a ∈ hexaOval[0]! := by decide

theorem mem_oval1_of_lt16 : ∀ v < 16, 4 * (v / 4) ∈ hexaOval[1]! := by decide

theorem lt4_of_mem_oval0 : ∀ a ∈ hexaOval[0]!, a < 4 := by decide

theorem lt16_of_mem_oval1 : ∀ b ∈ hexaOval[1]!, b < 16 := by decide

section Coord

variable (hD : PlaneData G A R g E F) {rep : Fin 64 → G}
  (hc : HexaCoord E R (pointsIn R E) rep)
  (hRg : ∀ v, rep v ∈ rightConjugate R g ↔ v.val ∈ hexaOval[1]!)

include hD hc hRg

theorem rep_mem_inf_iff (v : Fin 64) : rep v ∈ E ⊓ F ↔ v.val < 16 := by
  rw [hD.frame.inf_eq]
  constructor
  · intro hv
    obtain ⟨r, hr, r', hr', he⟩ := exists_mul_of_mem_sup hD.commE hD.frame.R_le_E
      (hD.Rg_le.trans inf_le_left) hv
    obtain ⟨a, rfl⟩ := hc.surj r (hD.frame.R_le_E hr)
    obtain ⟨b, rfl⟩ := hc.surj r' ((hD.Rg_le.trans inf_le_left) hr')
    have ha := lt4_of_mem_oval0 _ ((hc.R_iff a).1 hr)
    have hb := lt16_of_mem_oval1 _ ((hRg b).1 hr')
    rw [← hc.add] at he
    rw [hc.inj he, val_xorF]
    exact Nat.xor_lt_two_pow (n := 4) (by omega) hb
  · intro hv
    have he := eq_xor_of_lt16 v.val hv
    have ha : v.val % 4 < 64 := by omega
    have hb : 4 * (v.val / 4) < 64 := by omega
    have hv' : v = xorF ⟨v.val % 4, ha⟩ ⟨4 * (v.val / 4), hb⟩ := Fin.ext he
    rw [hv', hc.add]
    exact mul_mem
      (mem_sup_left ((hc.R_iff _).2 (mem_oval0_of_lt4 _ (Nat.mod_lt _ (by norm_num)))))
      (mem_sup_right ((hRg _).2 (mem_oval1_of_lt16 _ hv)))

end Coord

theorem card_v0Grp_le (hc15 : hexaCheck = true) (h44 : step44Check = true) :
    Nat.card v0Grp ≤ 4 := by
  have hsub : (v0Grp : Set (Equiv.Perm (Fin 64))) ⊆ Set.range (fun i : Fin 4 => v0P i.val) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (mem_v0Grp_iff hc15 h44).1 hx
    exact ⟨⟨i, hi⟩, rfl⟩
  calc Nat.card v0Grp = Nat.card (v0Grp : Set (Equiv.Perm (Fin 64))) := rfl
    _ ≤ Nat.card (Set.range (fun i : Fin 4 => v0P i.val)) := Nat.card_mono (Set.finite_range _) hsub
    _ ≤ Nat.card (Fin 4) := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = 4 := by simp

section PsiF

variable (hc15 : hexaCheck = true) (hS : hexaStabCheck = true) (h44 : step44Check = true)
  (hD : PlaneData G A R g E F) {rep : Fin 64 → G} (hc : HexaCoord E R (pointsIn R E) rep)
  (hRg : ∀ v, rep v ∈ rightConjugate R g ↔ v.val ∈ hexaOval[1]!)

include hc15 hS h44 hD hc hRg

theorem psi_mem_v0Grp {f : G} (hf : f ∈ F) : hc.psi ⟨f, hD.F_le_normalizer hf⟩ ∈ v0Grp := by
  have hfix : ∀ v : Fin 64, v.val < 16 → hc.psi ⟨f, hD.F_le_normalizer hf⟩ v = v := by
    intro v hv
    apply hc.inj
    rw [hc.rep_psi]
    have hvF : rep v ∈ F := ((rep_mem_inf_iff hD hc hRg v).2 hv).2
    show f * rep v * f⁻¹ = rep v
    rw [hD.commF f hf _ hvF, mul_inv_cancel_right]
  obtain ⟨i, hi, he⟩ := exists_v0P_of_fix hc15 h44 (hc.psi_mem_hexaM hc15 hS _) hfix
  exact (mem_v0Grp_iff hc15 h44).2 ⟨i, hi, he⟩

theorem exists_mem_F_psi_eq {i : ℕ} (hi : i < 4) :
    ∃ f, ∃ hf : f ∈ F, hc.psi ⟨f, hD.F_le_normalizer hf⟩ = v0P i := by
  let ψF : ↥F →* Equiv.Perm (Fin 64) := hc.psi.comp (inclusion hD.F_le_normalizer)
  have hle : ψF.range ≤ v0Grp := by
    rintro _ ⟨f, rfl⟩
    exact psi_mem_v0Grp hc15 hS h44 hD hc hRg f.2
  have hker : ψF.ker = (E ⊓ F).subgroupOf F := by
    ext f
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    change hc.psi (inclusion hD.F_le_normalizer f) = 1 ↔ _
    rw [hc.psi_eq_one_iff]
    constructor
    · intro hC
      refine ⟨?_, f.2⟩
      have hC' : (f : G) ∈ E ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) := hD.centralizer_eq ▸ hC
      exact mem_of_mem_sup_odd (hD.isPGroup_sup.to_le le_sup_left) (AS76b.odd_card_oddCoreIn _)
        (hD.centralizer_eq ▸ le_sup_right) hC' (hD.sqF _ f.2)
    · rintro ⟨hE, -⟩
      exact mem_centralizer_iff.mpr fun x hx => hD.commE x hx _ hE
  have hcard : Nat.card ψF.range = 4 := by
    have h1 := Subgroup.card_ker_mul_card_range ψF
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : E ⊓ F ≤ F)).toEquiv,
      card_inf_of_frame hD.frame, hD.frame.cardF] at h1
    omega
  have heq : ψF.range = v0Grp :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact card_v0Grp_le hc15 h44)
  have hmem : v0P i ∈ ψF.range := heq ▸ (mem_v0Grp_iff hc15 h44).2 ⟨i, hi, rfl⟩
  obtain ⟨f, hf⟩ := hmem
  exact ⟨f, f.2, hf⟩

theorem mem_normalizer_sup_iff (n : ↥(normalizer (E : Set G))) :
    (n : G) ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) ↔
      hc.psi n ∈ normalizer (v0Grp : Set (Equiv.Perm (Fin 64))) := by
  constructor
  · intro hn
    have hnF := hD.mem_normalizer_F hn n.2
    refine mem_normalizer_of_map_conj_le' ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (mem_v0Grp_iff hc15 h44).1 hx
    obtain ⟨f, hf, hfe⟩ := exists_mem_F_psi_eq hc15 hS h44 hD hc hRg hi
    have hf' : (n : G) * f * (n : G)⁻¹ ∈ F := (mem_normalizer_iff.mp hnF f).mp hf
    have e : (MulAut.conj (hc.psi n)).toMonoidHom (v0P i) =
        hc.psi ⟨(n : G) * f * (n : G)⁻¹, hD.F_le_normalizer hf'⟩ := by
      rw [← hfe]
      show hc.psi n * hc.psi ⟨f, _⟩ * (hc.psi n)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact psi_mem_v0Grp hc15 hS h44 hD hc hRg hf'
  · intro hn
    refine mem_normalizer_of_map_conj_le ?_
    rw [Subgroup.map_le_iff_le_comap, sup_le_iff]
    constructor
    · intro x hx
      show (n : G) * x * (n : G)⁻¹ ∈ E ⊔ F
      exact mem_sup_left ((mem_normalizer_iff.mp n.2 x).mp hx)
    · intro f hf
      show (n : G) * f * (n : G)⁻¹ ∈ E ⊔ F
      have hf'N : (n : G) * f * (n : G)⁻¹ ∈ normalizer (E : Set G) :=
        mul_mem (mul_mem n.2 (hD.F_le_normalizer hf)) (inv_mem n.2)
      have hψ : hc.psi ⟨_, hf'N⟩ ∈ v0Grp := by
        have e : hc.psi ⟨_, hf'N⟩ = hc.psi n * hc.psi ⟨f, hD.F_le_normalizer hf⟩ * (hc.psi n)⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          rfl
        rw [e]
        exact (mem_normalizer_iff.mp hn _).mp (psi_mem_v0Grp hc15 hS h44 hD hc hRg hf)
      obtain ⟨i, hi, hie⟩ := (mem_v0Grp_iff hc15 h44).1 hψ
      obtain ⟨f', hf', hf'e⟩ := exists_mem_F_psi_eq hc15 hS h44 hD hc hRg hi
      have hk : (⟨f', hD.F_le_normalizer hf'⟩ : ↥(normalizer (E : Set G)))⁻¹ * ⟨_, hf'N⟩ ∈
          hc.psi.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hie, hf'e, inv_mul_cancel]
      have hC : f'⁻¹ * ((n : G) * f * (n : G)⁻¹) ∈ centralizer (E : Set G) :=
        (hc.psi_eq_one_iff _).1 hk
      rw [hD.centralizer_eq] at hC
      have hmem : (n : G) * f * (n : G)⁻¹ ∈ (E ⊔ F) ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) := by
        have e : (n : G) * f * (n : G)⁻¹ = f' * (f'⁻¹ * ((n : G) * f * (n : G)⁻¹)) := by group
        rw [e]
        refine mul_mem (mem_sup_left (mem_sup_right hf')) ?_
        have hle : E ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) ≤
            (E ⊔ F) ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) :=
          sup_le (le_sup_left.trans le_sup_left) le_sup_right
        exact hle hC
      have hsq : (n : G) * f * (n : G)⁻¹ * ((n : G) * f * (n : G)⁻¹) = 1 := by
        rw [show (n : G) * f * (n : G)⁻¹ * ((n : G) * f * (n : G)⁻¹) = (n : G) * (f * f) * (n : G)⁻¹
          by group, hD.sqF f hf, mul_one, mul_inv_cancel]
      exact mem_of_mem_sup_odd hD.isPGroup_sup (AS76b.odd_card_oddCoreIn _)
        hD.oddCore_le_centralizer hmem hsq

theorem psi_mem_v0Grp_of_mem_sup {x : G}
    (hx : x ∈ (E ⊔ F) ⊔ AS76b.oddCoreIn (centralizer (A : Set G)))
    (hxN : x ∈ normalizer (E : Set G)) : hc.psi ⟨x, hxN⟩ ∈ v0Grp := by
  have hOE : AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (E : Set G) :=
    hD.centralizer_eq ▸ le_sup_right
  have hN1 : E ⊔ F ≤ normalizer (AS76b.oddCoreIn (centralizer (A : Set G)) : Set G) :=
    fun y hy => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun o ho =>
      (mem_centralizer_iff.mp (hD.oddCore_le_centralizer ho) y hy).symm)
  have hx' : x ∈ (((E ⊔ F) ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) : Subgroup G) : Set G) :=
    hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hN1] at hx'
  obtain ⟨y, hy, o, ho, rfl⟩ := hx'
  have hFE : F ≤ normalizer (E : Set G) := hD.F_le_normalizer
  have hy' : y ∈ ((E ⊔ F : Subgroup G) : Set G) := hy
  rw [coe_mul_of_right_le_normalizer_left E F hFE] at hy'
  obtain ⟨e, he, f, hf, rfl⟩ := hy'
  have heN : e ∈ normalizer (E : Set G) := le_normalizer he
  have hoN : o ∈ normalizer (E : Set G) := Subgroup.centralizer_le_normalizer _ (hOE ho)
  have hsplit : (⟨e * f * o, hxN⟩ : ↥(normalizer (E : Set G))) =
      ⟨e, heN⟩ * ⟨f, hFE hf⟩ * ⟨o, hoN⟩ := rfl
  rw [hsplit, map_mul, map_mul]
  have h1 : hc.psi ⟨e, heN⟩ = 1 :=
    (hc.psi_eq_one_iff _).2 (mem_centralizer_iff.mpr fun z hz => hD.commE z hz e he)
  have h2 : hc.psi ⟨o, hoN⟩ = 1 := (hc.psi_eq_one_iff _).2 (hOE ho)
  rw [h1, h2, one_mul, mul_one]
  exact psi_mem_v0Grp hc15 hS h44 hD hc hRg hf

end PsiF

@[expose] noncomputable def kPrime {rep : Fin 64 → G} (hc : HexaCoord E R (pointsIn R E) rep) :
    Subgroup G :=
  (k36.comap hc.psi).map (normalizer (E : Set G)).subtype

omit [Finite G] in
theorem mem_kPrime_iff {rep : Fin 64 → G} (hc : HexaCoord E R (pointsIn R E) rep) {x : G} :
    x ∈ kPrime hc ↔ ∃ hx : x ∈ normalizer (E : Set G), hc.psi ⟨x, hx⟩ ∈ k36 := by
  constructor
  · rintro ⟨⟨y, hy⟩, hk, rfl⟩
    exact ⟨hy, hk⟩
  · rintro ⟨hx, hk⟩
    exact ⟨⟨x, hx⟩, hk, rfl⟩

omit [Finite G] in
theorem kPrime_le_normalizer {rep : Fin 64 → G} (hc : HexaCoord E R (pointsIn R E) rep) :
    kPrime hc ≤ normalizer (E : Set G) := by
  rintro _ ⟨⟨y, hy⟩, -, rfl⟩
  exact hy

section KPrime

variable (hc15 : hexaCheck = true) (hS : hexaStabCheck = true) (h44 : step44Check = true)
  (hD : PlaneData G A R g E F) {rep : Fin 64 → G} (hc : HexaCoord E R (pointsIn R E) rep)
  (hRg : ∀ v, rep v ∈ rightConjugate R g ↔ v.val ∈ hexaOval[1]!)

include hc15 hS h44 hD hc hRg

theorem kPrime_le_normalizer_sup :
    kPrime hc ≤ normalizer ((E ⊔ F : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨hxN, hk⟩ := (mem_kPrime_iff hc).1 hx
  exact (mem_normalizer_sup_iff hc15 hS h44 hD hc hRg ⟨x, hxN⟩).2
    (k36_le_normalizer hc15 h44 hk)

theorem sup_le_kPrime : E ⊔ F ≤ kPrime hc := by
  intro x hx
  have hxN : x ∈ normalizer (E : Set G) :=
    (sup_le le_normalizer hD.F_le_normalizer : E ⊔ F ≤ normalizer (E : Set G)) hx
  refine (mem_kPrime_iff hc).2 ⟨hxN, v0Grp_le_k36 ?_⟩
  exact psi_mem_v0Grp_of_mem_sup hc15 hS h44 hD hc hRg (mem_sup_left hx) hxN

omit [Finite G] hc15 hS h44 hD hRg in
theorem centralizer_le_kPrime : centralizer (E : Set G) ≤ kPrime hc := by
  intro x hx
  have hxN : x ∈ normalizer (E : Set G) := Subgroup.centralizer_le_normalizer _ hx
  refine (mem_kPrime_iff hc).2 ⟨hxN, ?_⟩
  rw [(hc.psi_eq_one_iff ⟨x, hxN⟩).2 hx]
  exact one_mem _

omit [Finite G] hS hD hc hRg in
theorem conj_mem_k36 {m k : Equiv.Perm (Fin 64)} (hm : m ∈ hexaM)
    (hn : m ∈ normalizer (v0Grp : Set (Equiv.Perm (Fin 64)))) (hk : k ∈ k36) :
    m * k * m⁻¹ ∈ k36 := by
  refine mem_k36_of hc15 h44 (mul_mem (mul_mem hm (k36_le_hexaM hc15 h44 hk)) (inv_mem hm))
    (mul_mem (mul_mem hn (k36_le_normalizer hc15 h44 hk)) (inv_mem hn)) ?_
  rw [conj_pow]
  exact (mem_normalizer_iff.mp hn _).mp (pow_nine_mem_v0Grp hc15 h44 hk)

theorem normalizer_sup_le_normalizer_kPrime :
    normalizer ((E ⊔ F : Subgroup G) : Set G) ≤ normalizer (kPrime hc : Set G) := by
  intro n hn
  refine mem_normalizer_of_map_conj_le ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨hkN, hkK⟩ := (mem_kPrime_iff hc).1 hk
  have hkS : k ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) :=
    kPrime_le_normalizer_sup hc15 hS h44 hD hc hRg hk
  have hkF := hD.mem_normalizer_F hkS hkN
  show n * k * n⁻¹ ∈ kPrime hc
  have hnkS : n * k * n⁻¹ ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) :=
    mul_mem (mul_mem hn hkS) (inv_mem hn)
  have hψconj : ∀ (hnN : n ∈ normalizer (E : Set G)) (hnk : n * k * n⁻¹ ∈ normalizer (E : Set G)),
      hc.psi ⟨n * k * n⁻¹, hnk⟩ = hc.psi ⟨n, hnN⟩ * hc.psi ⟨k, hkN⟩ * (hc.psi ⟨n, hnN⟩)⁻¹ := by
    intro hnN hnk
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rcases hD.conj_eq_or_eq (inv_mem hn) with hE | hE
  ·
    have hnE : n ∈ normalizer (E : Set G) :=
      (normalizer (E : Set G)).inv_mem_iff.mp ((rightConjugate_eq_self_iff E n⁻¹).mp hE)
    have hnk : n * k * n⁻¹ ∈ normalizer (E : Set G) := mul_mem (mul_mem hnE hkN) (inv_mem hnE)
    refine (mem_kPrime_iff hc).2 ⟨hnk, ?_⟩
    rw [hψconj hnE hnk]
    exact conj_mem_k36 hc15 h44 (hc.psi_mem_hexaM hc15 hS _)
      ((mem_normalizer_sup_iff hc15 hS h44 hD hc hRg ⟨n, hnE⟩).1 hn) hkK
  ·
    have hE' : rightConjugate E n = F := by
      rcases hD.conj_eq_or_eq hn with h | h
      · exfalso
        have hnE := (rightConjugate_eq_self_iff E n).mp h
        rw [(rightConjugate_eq_self_iff E n⁻¹).mpr (inv_mem hnE)] at hE
        exact hD.frame.ne hE
      · exact h
    have hF1 : ∀ x, x ∈ F ↔ n * x * n⁻¹ ∈ E := fun x => by
      rw [← hE', mem_rightConjugate_iff]
    have hF2 : ∀ x, x ∈ F ↔ n⁻¹ * x * n ∈ E := fun x => by
      rw [← hE, mem_rightConjugate_iff, inv_inv]
    have hnk : n * k * n⁻¹ ∈ normalizer (E : Set G) := by
      refine mem_normalizer_of_map_conj_le ?_
      rintro _ ⟨e, he, rfl⟩
      show n * k * n⁻¹ * e * (n * k * n⁻¹)⁻¹ ∈ E
      have h1 : n⁻¹ * e * n ∈ F := (hF1 _).2 (by simpa [mul_assoc] using he)
      have h2 : k * (n⁻¹ * e * n) * k⁻¹ ∈ F := (mem_normalizer_iff.mp hkF _).mp h1
      have h3 := (hF1 _).1 h2
      simpa [mul_assoc] using h3
    refine (mem_kPrime_iff hc).2 ⟨hnk, ?_⟩
    refine mem_k36_of hc15 h44 (hc.psi_mem_hexaM hc15 hS _)
      ((mem_normalizer_sup_iff hc15 hS h44 hD hc hRg ⟨_, hnk⟩).1 hnkS) ?_
    obtain ⟨i, hi, hki⟩ := (mem_v0Grp_iff hc15 h44).1 (pow_nine_mem_v0Grp hc15 h44 hkK)
    obtain ⟨f, hf, hfi⟩ := exists_mem_F_psi_eq hc15 hS h44 hD hc hRg hi
    have hc9 : f⁻¹ * k ^ 9 ∈ centralizer (E : Set G) := by
      have : (⟨f, hD.F_le_normalizer hf⟩ : ↥(normalizer (E : Set G)))⁻¹ * ⟨k, hkN⟩ ^ 9 ∈
          hc.psi.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hki, hfi, inv_mul_cancel]
      exact (hc.psi_eq_one_iff _).1 this
    have hsplit : n * k ^ 9 * n⁻¹ = (n * f * n⁻¹) * (n * (f⁻¹ * k ^ 9) * n⁻¹) := by group
    have hmem : n * k ^ 9 * n⁻¹ ∈ (E ⊔ F) ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) := by
      rw [hsplit]
      refine mul_mem (mem_sup_left (mem_sup_left ((hF1 f).1 hf))) ?_
      have hcF : n * (f⁻¹ * k ^ 9) * n⁻¹ ∈ centralizer (F : Set G) := by
        rw [mem_centralizer_iff]
        intro y hy
        have hy' := (hF2 y).1 hy
        have := mem_centralizer_iff.mp hc9 _ hy'
        calc y * (n * (f⁻¹ * k ^ 9) * n⁻¹) =
            n * ((n⁻¹ * y * n) * (f⁻¹ * k ^ 9)) * n⁻¹ := by group
          _ = n * ((f⁻¹ * k ^ 9) * (n⁻¹ * y * n)) * n⁻¹ := by rw [this]
          _ = n * (f⁻¹ * k ^ 9) * n⁻¹ * y := by group
      rw [hD.centralizer_eq'] at hcF
      have hle : F ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) ≤
          (E ⊔ F) ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) :=
        sup_le (le_sup_right.trans le_sup_left) le_sup_right
      exact hle hcF
    have hk9 : n * k ^ 9 * n⁻¹ ∈ normalizer (E : Set G) := by
      rw [← conj_pow]
      exact pow_mem hnk 9
    have e : (⟨n * k * n⁻¹, hnk⟩ : ↥(normalizer (E : Set G))) ^ 9 = ⟨n * k ^ 9 * n⁻¹, hk9⟩ :=
      Subtype.ext (by simp only [SubmonoidClass.coe_pow, conj_pow])
    rw [← map_pow, e]
    exact psi_mem_v0Grp_of_mem_sup hc15 hS h44 hD hc hRg hmem hk9

end KPrime

theorem isSylowOf_map_of_hom {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ}
    [Fact p.Prime] {P B : Subgroup X} (h : IsSylowOf p P B) (φ : X →* Y) :
    IsSylowOf p (P.map φ) (B.map φ) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (φ.subgroupMap_surjective B), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

omit [Finite G] in
theorem rightConjugate_le_normalizer' {P T : Subgroup G} (h : P ≤ normalizer (T : Set G))
    (x : G) : rightConjugate P x ≤ normalizer (rightConjugate T x : Set G) := by
  intro y hy
  rw [mem_rightConjugate_iff] at hy
  rw [mem_normalizer_iff]
  intro z
  rw [mem_rightConjugate_iff, mem_rightConjugate_iff]
  have e : x * (y * z * y⁻¹) * x⁻¹ = (x * y * x⁻¹) * (x * z * x⁻¹) * (x * y * x⁻¹)⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.mp (h hy) _

theorem isSylowOf_rightConjugate {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (h : IsSylowOf p P K) {x : G} (hx : x ∈ normalizer (K : Set G)) :
    IsSylowOf p (rightConjugate P x) K := by
  have h' := isSylowOf_map_of_hom h (MulAut.conj x⁻¹).toMonoidHom
  change IsSylowOf p (rightConjugate P x) (rightConjugate K x) at h'
  rwa [(rightConjugate_eq_self_iff K x).2 hx] at h'

section Sylow

variable (hc15 : hexaCheck = true) (hS : hexaStabCheck = true) (h44 : step44Check = true)
  (hD : PlaneData G A R g E F) (hD' : PlaneData G A R g F E) {rep : Fin 64 → G}
  (hc : HexaCoord E R (pointsIn R E) rep)
  (hRg : ∀ v, rep v ∈ rightConjugate R g ↔ v.val ∈ hexaOval[1]!)

include hc15 hS h44 hD hD' hc hRg

omit hRg in
theorem map_psi_kPrime :
    ((kPrime hc).subgroupOf (normalizer (E : Set G))).map hc.psi = k36 := by
  have h1 : (kPrime hc).subgroupOf (normalizer (E : Set G)) = k36.comap hc.psi :=
    comap_map_eq_self_of_injective (normalizer (E : Set G)).subtype_injective _
  rw [h1, map_comap_eq, PlaneData.psi_range hc15 hS hD hD' hc,
    inf_eq_right.mpr (k36_le_hexaM hc15 h44)]

omit hRg in
theorem card_kPrime : Nat.card (kPrime hc) = 36 * Nat.card (centralizer (E : Set G)) := by
  have h := card_eq_card_inf_ker_mul_card_map hc.psi
    ((kPrime hc).subgroupOf (normalizer (E : Set G)))
  have hker : hc.psi.ker = (centralizer (E : Set G)).subgroupOf (normalizer (E : Set G)) := by
    ext n
    rw [MonoidHom.mem_ker, mem_subgroupOf, hc.psi_eq_one_iff]
  have hle : hc.psi.ker ≤ (kPrime hc).subgroupOf (normalizer (E : Set G)) := by
    intro n hn
    rw [mem_subgroupOf]
    exact centralizer_le_kPrime hc ((hc.psi_eq_one_iff n).1 hn)
  rw [inf_eq_right.mpr hle, map_psi_kPrime hc15 hS h44 hD hD' hc, card_k36 h44, hker,
    Nat.card_congr (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer _)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (kPrime_le_normalizer hc)).toEquiv] at h
  rw [h, mul_comm]

theorem isSylowOf_sup_kPrime : IsSylowOf 2 (E ⊔ F) (kPrime hc) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card (sup_le_kPrime hc15 hS h44 hD hc hRg) ?_
  rw [hD.card_sup, card_kPrime hc15 hS h44 hD hD' hc,
    Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.coe_add, Pi.add_apply,
    hD.factorization_card_centralizer, show (36 : ℕ) = 2 ^ 2 * 3 ^ 2 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.coe_add, Pi.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by norm_num)]
  norm_num


omit hc15 hS hD hD' hc hRg in
theorem isSylowOf_om9 : IsSylowOf 3 om9 k36 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isSylowOf_of_card om9_le_k36 ?_
  rw [card_om9 h44, card_k36 h44, show (36 : ℕ) = 2 ^ 2 * 3 ^ 2 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.coe_add, Pi.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by norm_num)]
  norm_num

omit hRg in
theorem isSylowOf_map_psi {T : Subgroup G} (hT : IsSylowOf 3 T (kPrime hc)) :
    IsSylowOf 3 ((T.subgroupOf (normalizer (E : Set G))).map hc.psi) k36 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT' : IsSylowOf 3 (T.subgroupOf (normalizer (E : Set G)))
      ((kPrime hc).subgroupOf (normalizer (E : Set G))) := by
    rw [← isSylowOf_map_subtype_iff (normalizer (E : Set G)), subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_eq_left.mpr (hT.le.trans (kPrime_le_normalizer hc)),
      inf_eq_left.mpr (kPrime_le_normalizer hc)]
    exact hT
  have h := isSylowOf_map_of_hom hT' hc.psi
  rwa [map_psi_kPrime hc15 hS h44 hD hD' hc] at h

omit hS hD hD' hc hRg in
theorem exists_v0P_conj_om9 {X : Subgroup (Equiv.Perm (Fin 64))} (hX : IsSylowOf 3 X k36) :
    ∃ i < 4, ∀ x, x ∈ X ↔ v0P i * x * v0P i ∈ om9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, hkx⟩ := (isSylowOf_om9 h44).exists_mem_conj hX
  obtain ⟨i, hi, hik⟩ := exists_v0P_mul_mem_om9 hc15 h44 hk
  have hvv := v0P_mul_self hc15 h44 hi
  refine ⟨i, hi, fun x => ?_⟩
  rw [hkx]
  have e : k⁻¹ * x * k = (v0P i * k)⁻¹ * (v0P i * x * v0P i) * (v0P i * k) := by
    rw [mul_inv_rev]
    have hinv : (v0P i)⁻¹ = v0P i := inv_eq_of_mul_eq_one_right hvv
    rw [hinv]
    calc k⁻¹ * x * k = k⁻¹ * (v0P i * v0P i) * x * (v0P i * v0P i) * k := by rw [hvv]; group
      _ = _ := by group
  rw [e]
  constructor
  · intro h
    have := mul_mem (mul_mem hik h) (inv_mem hik)
    simpa [mul_assoc] using this
  · intro h
    exact mul_mem (mul_mem (inv_mem hik) h) hik

theorem exists_conj_om9 {T : Subgroup G} (hT : IsSylowOf 3 T (kPrime hc)) :
    ∃ f ∈ F, IsSylowOf 3 (rightConjugate T f) (kPrime hc) ∧
      ((rightConjugate T f).subgroupOf (normalizer (E : Set G))).map hc.psi = om9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, hi, hX⟩ := exists_v0P_conj_om9 hc15 h44 (isSylowOf_map_psi hc15 hS h44 hD hD' hc hT)
  obtain ⟨f, hf, hfi⟩ := exists_mem_F_psi_eq hc15 hS h44 hD hc hRg hi
  have hfN : f ∈ normalizer (E : Set G) := hD.F_le_normalizer hf
  have hfK : f ∈ kPrime hc := sup_le_kPrime hc15 hS h44 hD hc hRg (mem_sup_right hf)
  have hvv := v0P_mul_self hc15 h44 hi
  have hinv : (v0P i)⁻¹ = v0P i := inv_eq_of_mul_eq_one_right hvv
  have hvyv : ∀ y, v0P i * (v0P i * y * v0P i) * v0P i = y := fun y => by
    calc v0P i * (v0P i * y * v0P i) * v0P i = (v0P i * v0P i) * y * (v0P i * v0P i) := by group
      _ = y := by rw [hvv]; group
  refine ⟨f, hf, isSylowOf_rightConjugate hT (le_normalizer hfK), ?_⟩
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    replace hn : f * (n : G) * f⁻¹ ∈ T := (mem_rightConjugate_iff T f n).1 hn
    have hm : (⟨f, hfN⟩ * n * ⟨f, hfN⟩⁻¹ : ↥(normalizer (E : Set G))) ∈
        T.subgroupOf (normalizer (E : Set G)) := hn
    have hX' := (hX (hc.psi (⟨f, hfN⟩ * n * ⟨f, hfN⟩⁻¹))).1 (Subgroup.mem_map_of_mem hc.psi hm)
    rwa [map_mul, map_mul, map_inv, hfi, hinv, hvyv] at hX'
  · intro hy
    have hX' : v0P i * y * v0P i ∈ (T.subgroupOf (normalizer (E : Set G))).map hc.psi := by
      rw [hX, hvyv]
      exact hy
    obtain ⟨m, hm, hme⟩ := hX'
    refine ⟨⟨f, hfN⟩⁻¹ * m * ⟨f, hfN⟩, ?_, ?_⟩
    · show _ ∈ rightConjugate T f
      rw [mem_rightConjugate_iff]
      have e : (f : G) * ((⟨f, hfN⟩⁻¹ * m * ⟨f, hfN⟩ : ↥(normalizer (E : Set G))) : G) * f⁻¹ =
          m := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have h' : (f : G) * ((⟨f, hfN⟩⁻¹ * m * ⟨f, hfN⟩ : ↥(normalizer (E : Set G))) : G) * f⁻¹ ∈
          T := by
        rw [e]
        exact hm
      exact h'
    · rw [map_mul, map_mul, map_inv, hfi, hme, hinv, hvyv]

omit hS hD hD' hc hRg in
theorem v0P_injOn {i j : ℕ} (hi : i < 4) (hj : j < 4) (h : v0P i = v0P j) : i = j := by
  have h1 : v0P (i ^^^ j) = 1 := by
    rw [← v0P_mul hc15 h44 hi hj, h, v0P_mul_self hc15 h44 hj]
  have hxor : ∀ a < 4, ∀ b < 4, a ^^^ b = 0 → a = b := by decide
  by_contra hne
  exact v0P_ne_one hc15 h44 (Nat.xor_lt_two_pow (n := 2) hi hj)
    (fun h0 => hne (hxor i hi j hj h0)) h1

omit hD' in
theorem eq_one_of_forall_comm {T : Subgroup G}
    (hT : (T.subgroupOf (normalizer (E : Set G))).map hc.psi = om9) {x : G} (hx : x ∈ E ⊔ F)
    (hxT : ∀ t ∈ T, t * x = x * t) : x = 1 := by
  have hxN : x ∈ normalizer (E : Set G) :=
    (sup_le le_normalizer hD.F_le_normalizer : E ⊔ F ≤ normalizer (E : Set G)) hx
  have hconj : ∀ n : ↥(normalizer (E : Set G)), (n : G) ∈ T →
      hc.psi n * hc.psi ⟨x, hxN⟩ * (hc.psi n)⁻¹ = hc.psi ⟨x, hxN⟩ := by
    intro n hn
    have e : n * ⟨x, hxN⟩ * n⁻¹ = (⟨x, hxN⟩ : ↥(normalizer (E : Set G))) :=
      Subtype.ext (by
        show (n : G) * x * (n : G)⁻¹ = x
        rw [hxT n hn, mul_inv_cancel_right])
    rw [← map_inv, ← map_mul, ← map_mul, e]
  have hmu : muP ∈ (T.subgroupOf (normalizer (E : Set G))).map hc.psi := hT ▸ muP_mem_om9
  obtain ⟨t₂, ht₂, ht₂e⟩ := hmu
  have homega : omegaP ∈ (T.subgroupOf (normalizer (E : Set G))).map hc.psi :=
    hT ▸ omegaP_mem_om9
  obtain ⟨t₁, ht₁, ht₁e⟩ := homega
  obtain ⟨i, hi, hxi⟩ := (mem_v0Grp_iff hc15 h44).1
    (psi_mem_v0Grp_of_mem_sup hc15 hS h44 hD hc hRg (mem_sup_left hx) hxN)
  have h2 := hconj t₂ ht₂
  rw [ht₂e, hxi, muP_conj_v0P hc15 h44 hi] at h2
  have hfix : ∀ a < 4, hexaMuPi[a]! = a → a = 0 := by decide
  have hi0 : i = 0 := hfix i hi (v0P_injOn hc15 h44 (muPi_lt h44 hi) hi h2)
  subst hi0
  rw [v0P_zero hc15 h44] at hxi
  have hxC : x ∈ centralizer (E : Set G) := (hc.psi_eq_one_iff _).1 hxi
  have hE2 : IsPGroup 2 (E ⊔ F : Subgroup G) := hD.isPGroup_sup
  obtain ⟨k, hk⟩ := hE2 ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [hD.centralizer_eq] at hxC
  have hxE : x ∈ E := mem_of_mem_sup_odd' (hE2.to_le le_sup_left) (AS76b.odd_card_oddCoreIn _)
    (hD.centralizer_eq ▸ le_sup_right) hxC hk'
  obtain ⟨v, rfl⟩ := hc.surj x hxE
  have h3 : rep (omegaP v) = rep v := by
    rw [← ht₁e, hc.rep_psi, hxT t₁ ht₁, mul_inv_cancel_right]
  rw [eq_zero_of_omegaP_fix hc15 h44 (hc.inj h3), hc.rep_zero]

omit hD' in
theorem mem_sup_of_mul_self {x : G} (hx : x ∈ kPrime hc) (hx2 : x * x = 1) : x ∈ E ⊔ F := by
  obtain ⟨hxN, hk⟩ := (mem_kPrime_iff hc).1 hx
  have h9 := pow_nine_mem_v0Grp hc15 h44 hk
  have hsq : hc.psi ⟨x, hxN⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have e : (⟨x, hxN⟩ : ↥(normalizer (E : Set G))) ^ 2 = 1 := Subtype.ext (by simp [sq, hx2])
    rw [e, map_one]
  have e9 : hc.psi ⟨x, hxN⟩ ^ 9 = hc.psi ⟨x, hxN⟩ := by
    rw [show 9 = 2 * 4 + 1 by norm_num, pow_add, pow_mul, hsq, one_pow, one_mul, pow_one]
  rw [e9] at h9
  obtain ⟨i, hi, hie⟩ := (mem_v0Grp_iff hc15 h44).1 h9
  obtain ⟨f, hf, hfi⟩ := exists_mem_F_psi_eq hc15 hS h44 hD hc hRg hi
  have hker : (⟨f, hD.F_le_normalizer hf⟩ : ↥(normalizer (E : Set G)))⁻¹ * ⟨x, hxN⟩ ∈
      hc.psi.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hie, hfi, inv_mul_cancel]
  have hC : f⁻¹ * x ∈ centralizer (E : Set G) := (hc.psi_eq_one_iff _).1 hker
  rw [hD.centralizer_eq] at hC
  have hmem : x ∈ (E ⊔ F) ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) := by
    have e : x = f * (f⁻¹ * x) := by group
    rw [e]
    refine mul_mem (mem_sup_left (mem_sup_right hf)) ?_
    have hle : E ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) ≤
        (E ⊔ F) ⊔ AS76b.oddCoreIn (centralizer (A : Set G)) :=
      sup_le (le_sup_left.trans le_sup_left) le_sup_right
    exact hle hC
  exact mem_of_mem_sup_odd hD.isPGroup_sup (AS76b.odd_card_oddCoreIn _)
    hD.oddCore_le_centralizer hmem hx2

omit hD' in
theorem odd_card_inf_normalizer {T : Subgroup G} (hT3 : IsPGroup 3 T) (hTK : T ≤ kPrime hc)
    (hC : ∀ x ∈ E ⊔ F, (∀ t ∈ T, t * x = x * t) → x = 1) :
    Odd (Nat.card (kPrime hc ⊓ normalizer (T : Set G) : Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hST : (E ⊔ F) ⊓ T = ⊥ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hT3
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hD.card_sup, hn]
    exact Nat.Coprime.pow _ _ (by norm_num)
  rw [Nat.odd_iff]
  by_contra h2
  have h2' : 2 ∣ Nat.card (kPrime hc ⊓ normalizer (T : Set G) : Subgroup G) := by omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2'
  have hx2 : (x : G) * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx, sq] at this
    exact congrArg Subtype.val this
  have hxS : (x : G) ∈ E ⊔ F := mem_sup_of_mul_self hc15 hS h44 hD hc hRg x.2.1 hx2
  have hx1 : (x : G) = 1 := by
    refine hC x hxS fun t ht => ?_
    have h1 : (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ T :=
      mul_mem ((mem_normalizer_iff.mp x.2.2 t).mp ht) (inv_mem ht)
    have htN : t ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) :=
      kPrime_le_normalizer_sup hc15 hS h44 hD hc hRg (hTK ht)
    have h2 : (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ E ⊔ F := by
      have h4 : t * (x : G)⁻¹ * t⁻¹ ∈ E ⊔ F := (mem_normalizer_iff.mp htN _).mp (inv_mem hxS)
      have e : (x : G) * t * (x : G)⁻¹ * t⁻¹ = x * (t * (x : G)⁻¹ * t⁻¹) := by group
      rw [e]
      exact mul_mem hxS h4
    have h3 : (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ (E ⊔ F) ⊓ T := ⟨h2, h1⟩
    rw [hST, mem_bot] at h3
    calc t * (x : G) = ((x : G) * t * (x : G)⁻¹ * t⁻¹)⁻¹ * (x * t) := by group
      _ = x * t := by rw [h3, inv_one, one_mul]
  have hx1' : x = 1 := Subtype.ext hx1
  rw [hx1', orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem exists_complement {S₁ : Subgroup G}
    (hS₁ : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    ∃ W T : Subgroup G, W ≤ S₁ ∧ W ⊓ (E ⊔ F) = ⊥ ∧ Nat.card W * 2 ^ 8 = Nat.card S₁ ∧
      W ≤ normalizer (T : Set G) ∧ T ≤ kPrime hc ∧ IsPGroup 3 T ∧
      (T.subgroupOf (normalizer (E : Set G))).map hc.psi = om9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKS : kPrime hc ≤ normalizer ((E ⊔ F : Subgroup G) : Set G) :=
    kPrime_le_normalizer_sup hc15 hS h44 hD hc hRg
  have hSK : E ⊔ F ≤ kPrime hc := sup_le_kPrime hc15 hS h44 hD hc hRg
  have hSS₁ : E ⊔ F ≤ S₁ := hD.sup_le_sylow hS₁
  have hNK : normalizer ((E ⊔ F : Subgroup G) : Set G) ≤ normalizer (kPrime hc : Set G) :=
    normalizer_sup_le_normalizer_kPrime hc15 hS h44 hD hc hRg
  obtain ⟨T₁, hT₁⟩ := exists_isSylowOf 3 (kPrime hc)
  obtain ⟨f₁, -, hT₀, hT₀ψ⟩ := exists_conj_om9 hc15 hS h44 hD hD' hc hRg hT₁
  generalize rightConjugate T₁ f₁ = T₀ at hT₀ hT₀ψ
  have hodd := odd_card_inf_normalizer hc15 hS h44 hD hc hRg hT₀.isPGroup hT₀.le
    fun x hx hxT => eq_one_of_forall_comm hc15 hS h44 hD hc hRg hT₀ψ hx hxT
  obtain ⟨H, hH⟩ : ∃ H, H = S₁ ⊔ kPrime hc := ⟨_, rfl⟩
  have hHN : H ≤ normalizer ((E ⊔ F : Subgroup G) : Set G) := hH ▸ sup_le hS₁.le hKS
  have hHK : H ≤ normalizer (kPrime hc : Set G) := hHN.trans hNK
  have hKH : kPrime hc ≤ H := hH ▸ le_sup_right
  have hS₁H : IsSylowOf 2 S₁ H := hS₁.of_le (hH ▸ le_sup_left) hHN
  obtain ⟨N, hN⟩ : ∃ N, N = H ⊓ normalizer (T₀ : Set G) := ⟨_, rfl⟩
  have hfr : kPrime hc ⊔ N = H := by
    refine le_antisymm (sup_le hKH (hN ▸ inf_le_left)) ?_
    intro h hh
    have hT' : IsSylowOf 3 (rightConjugate T₀ h⁻¹) (kPrime hc) :=
      isSylowOf_rightConjugate hT₀ (inv_mem (hHK hh))
    obtain ⟨k, hk, hkx⟩ := hT₀.exists_mem_conj hT'
    have hn : k⁻¹ * h ∈ N := by
      rw [hN]
      refine ⟨mul_mem (hKH (inv_mem hk)) hh, mem_normalizer_of_map_conj_le ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      show k⁻¹ * h * y * (k⁻¹ * h)⁻¹ ∈ T₀
      have h1 : h * y * h⁻¹ ∈ rightConjugate T₀ h⁻¹ := by
        rw [mem_rightConjugate_iff]
        have e : h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y := by group
        rw [e]
        exact hy
      have h2 := (hkx _).1 h1
      have e : k⁻¹ * h * y * (k⁻¹ * h)⁻¹ = k⁻¹ * (h * y * h⁻¹) * k := by group
      rw [e]
      exact h2
    have e : h = k * (k⁻¹ * h) := by group
    rw [e]
    exact mul_mem (mem_sup_left hk) (mem_sup_right hn)
  have hKS₁ : kPrime hc ⊓ S₁ = E ⊔ F :=
    (isSylowOf_sup_kPrime hc15 hS h44 hD hD' hc hRg).eq_of_le (le_inf hSK hSS₁) inf_le_left
      (hS₁.isPGroup.to_le inf_le_right)
  have hc1 : Nat.card H * 2 ^ 8 = Nat.card (kPrime hc) * Nat.card S₁ := by
    have h := card_sup_mul_card_inf (H := kPrime hc) (R := S₁) (hS₁.le.trans hNK)
    rwa [hKS₁, hD.card_sup, sup_comm, ← hH] at h
  have hc2 : Nat.card H * Nat.card (kPrime hc ⊓ N : Subgroup G) =
      Nat.card (kPrime hc) * Nat.card N := by
    have h := card_sup_mul_card_inf (H := kPrime hc) (R := N) ((hN ▸ inf_le_left).trans hHK)
    rwa [hfr] at h
  have hoddN : Odd (Nat.card (kPrime hc ⊓ N : Subgroup G)) :=
    hodd.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_inf_left _ (hN ▸ inf_le_right)))
  have hkey : Nat.card S₁ * Nat.card (kPrime hc ⊓ N : Subgroup G) = Nat.card N * 2 ^ 8 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := kPrime hc))
    calc Nat.card (kPrime hc) * (Nat.card S₁ * Nat.card (kPrime hc ⊓ N : Subgroup G))
        = (Nat.card (kPrime hc) * Nat.card S₁) * Nat.card (kPrime hc ⊓ N : Subgroup G) := by ring
      _ = (Nat.card H * 2 ^ 8) * Nat.card (kPrime hc ⊓ N : Subgroup G) := by rw [hc1]
      _ = (Nat.card H * Nat.card (kPrime hc ⊓ N : Subgroup G)) * 2 ^ 8 := by ring
      _ = (Nat.card (kPrime hc) * Nat.card N) * 2 ^ 8 := by rw [hc2]
      _ = Nat.card (kPrime hc) * (Nat.card N * 2 ^ 8) := by ring
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 N
  have hPcard : Nat.card P * 2 ^ 8 = Nat.card S₁ := by
    have h1 : (Nat.card S₁ * Nat.card (kPrime hc ⊓ N : Subgroup G)).factorization 2 =
        (Nat.card N * 2 ^ 8).factorization 2 := by rw [hkey]
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.coe_add, Pi.add_apply,
      Finsupp.coe_add, Pi.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hoddN)
        (even_iff_two_dvd.mpr h)), Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same, hS₁.card_eq, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same] at h1
    rw [hP.card_eq, hS₁.card_eq, ← pow_add]
    exact congrArg (fun n => 2 ^ n) (by omega)
  have hPS : P ⊓ (E ⊔ F) = ⊥ :=
    two_subgroup_of_odd_eq_bot (P ⊓ (E ⊔ F)) (kPrime hc ⊓ N) (hP.isPGroup.to_le inf_le_left)
      hoddN (le_inf (inf_le_right.trans hSK) (inf_le_left.trans hP.le))
  have hPN : P ≤ normalizer ((E ⊔ F : Subgroup G) : Set G) :=
    hP.le.trans ((hN ▸ inf_le_left).trans hHN)
  have hc3 : Nat.card ((E ⊔ F) ⊔ P : Subgroup G) = 2 ^ 8 * Nat.card P := by
    have h := card_sup_mul_card_inf (H := E ⊔ F) (R := P) hPN
    rwa [inf_comm, hPS, Subgroup.card_bot, mul_one, hD.card_sup] at h
  have hSPH : IsSylowOf 2 ((E ⊔ F) ⊔ P) H := by
    refine isSylowOf_of_card (sup_le (hSS₁.trans (hH ▸ le_sup_left))
      (hP.le.trans (hN ▸ inf_le_left))) ?_
    rw [hc3, ← hS₁H.card_eq, ← hPcard, mul_comm]
  obtain ⟨k, hkH, hk⟩ := hSPH.exists_mem_conj hS₁H
  have hT₂ : IsSylowOf 3 (rightConjugate T₀ k⁻¹) (kPrime hc) :=
    isSylowOf_rightConjugate hT₀ (inv_mem (hHK hkH))
  obtain ⟨f, hf, hT, hTψ⟩ := exists_conj_om9 hc15 hS h44 hD hD' hc hRg hT₂
  have hfS₁ : f ∈ S₁ := hSS₁ (mem_sup_right hf)
  refine ⟨rightConjugate (rightConjugate P k⁻¹) f, rightConjugate (rightConjugate T₀ k⁻¹) f,
    ?_, ?_, ?_, ?_, hT.le, hT.isPGroup, hTψ⟩
  · intro x hx
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff, inv_inv] at hx
    have h1 : f * x * f⁻¹ ∈ S₁ := (hk _).2 (mem_sup_right hx)
    have e : x = f⁻¹ * (f * x * f⁻¹) * f := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hfS₁) h1) hfS₁
  · rw [eq_bot_iff]
    intro x hx'
    obtain ⟨hx, hxS⟩ := Subgroup.mem_inf.mp hx'
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff, inv_inv] at hx
    have hfN : f ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) := le_normalizer (mem_sup_right hf)
    have h1 : f * x * f⁻¹ ∈ E ⊔ F := (mem_normalizer_iff.mp hfN x).mp hxS
    have h2 : k⁻¹ * (f * x * f⁻¹) * k ∈ E ⊔ F := by
      have h3 := (mem_normalizer_iff.mp (inv_mem (hHN hkH)) _).mp h1
      rwa [inv_inv] at h3
    have h3 : k⁻¹ * (f * x * f⁻¹) * k ∈ P ⊓ (E ⊔ F) := ⟨hx, h2⟩
    rw [hPS, mem_bot] at h3
    rw [mem_bot]
    calc x = f⁻¹ * k * (k⁻¹ * (f * x * f⁻¹) * k) * k⁻¹ * f := by group
      _ = 1 := by rw [h3]; group
  · rw [rightConjugate_card, rightConjugate_card, hPcard]
  · exact rightConjugate_le_normalizer'
      (rightConjugate_le_normalizer' (hP.le.trans (hN ▸ inf_le_right)) _) _

end Sylow

end CFSG.ComponentClassification.AS81

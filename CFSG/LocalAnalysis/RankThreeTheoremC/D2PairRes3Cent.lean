module

public import CFSG.Foundations.Basic
import CFSG.RankThree.PartOne.S11d.OutCentral
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
public import CFSG.Assembly.Defs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

variable {Y : Type*} [Group Y]

theorem normalizer_le_normalizer_centralizer_res3 (L : Subgroup Y) :
    Subgroup.normalizer (L : Set Y) ≤
      Subgroup.normalizer (Subgroup.centralizer (L : Set Y) : Set Y) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
    (Subgroup.normal_subgroupOf_centralizer_normalizer _)

theorem pow_mem_mul_of_mem_normalizer {L : Subgroup Y} {r l : Y}
    (hr : r ∈ Subgroup.normalizer (L : Set Y)) (hl : l ∈ L) (n : ℕ) :
    ∃ l' ∈ L, (r * l) ^ n = r ^ n * l' := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', hn⟩ := ih
    have hinv : r⁻¹ * l' * r ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hr) l').mp hl'
      simpa using this
    refine ⟨(r⁻¹ * l' * r) * l, L.mul_mem hinv hl, ?_⟩
    rw [pow_succ, hn, pow_succ]
    group

theorem commutative_of_central_by_three [Finite Y] {D N₀ : Subgroup Y} (hN₀D : N₀ ≤ D)
    (hN₀c : ∀ n ∈ N₀, ∀ d ∈ D, n * d = d * n) (h3 : ∀ d ∈ D, ∃ k : ℕ, d ^ 3 ^ k ∈ N₀)
    (hab : ∀ T : Subgroup Y, T ≤ D → IsPGroup 3 T → ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N' : Subgroup D := N₀.subgroupOf D with hN'
  have hN'c : ∀ n ∈ N', ∀ d : D, n * d = d * n := fun n hn d =>
    Subtype.ext (hN₀c n (Subgroup.mem_subgroupOf.mp hn) d d.2)
  have : N'.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := by rw [← hN'c n hn g]; group
    rw [this]; exact hn⟩
  have hq : IsPGroup 3 (D ⧸ N') := by
    intro g
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := h3 d d.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hk
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hq)
  obtain ⟨P⟩ : Nonempty (Sylow 3 D) := inferInstance
  have hidx : ((P : Subgroup D) ⊔ N').index = 1 := by
    have h1 : ((P : Subgroup D) ⊔ N').index ∣ (P : Subgroup D).index :=
      Subgroup.index_dvd_of_le le_sup_left
    have h2 : ((P : Subgroup D) ⊔ N').index ∣ N'.index := Subgroup.index_dvd_of_le le_sup_right
    have h3' : N'.index = 3 ^ n := by rw [Subgroup.index_eq_card, hn]
    rw [h3'] at h2
    have hcop : Nat.Coprime ((P : Subgroup D) ⊔ N').index (3 ^ n) := by
      refine Nat.Coprime.pow_right n ?_
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      exact fun hd => P.not_dvd_index (hd.trans h1)
    exact Nat.Coprime.eq_one_of_dvd hcop h2
  have htop : (P : Subgroup D) ⊔ N' = ⊤ := Subgroup.index_eq_one.mp hidx
  have hP : ∀ p p' : D, p ∈ P → p' ∈ P → (p : Y) * p' = p' * p := by
    intro p p' hp hp'
    refine hab ((P : Subgroup D).map D.subtype) ?_ (P.isPGroup'.map D.subtype) (p : Y)
      ⟨p, hp, rfl⟩ (p' : Y) ⟨p', hp', rfl⟩
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hdec : ∀ a ∈ D, ∃ p : D, p ∈ P ∧ ∃ m ∈ N₀, a = (p : Y) * m := by
    intro a ha
    have : (⟨a, ha⟩ : D) ∈ (P : Subgroup D) ⊔ N' := htop ▸ Subgroup.mem_top _
    obtain ⟨p, hp, m, hm, hpm⟩ := Subgroup.mem_sup_of_normal_right.mp this
    exact ⟨p, hp, (m : Y), Subgroup.mem_subgroupOf.mp hm, by
      have := congrArg Subtype.val hpm
      simpa using this.symm⟩
  intro a ha b hb
  obtain ⟨p, hp, m, hm, rfl⟩ := hdec a ha
  obtain ⟨p', hp', m', hm', rfl⟩ := hdec b hb
  have hmp' : m * (p' : Y) = (p' : Y) * m := hN₀c m hm p' p'.2
  have hm'p : m' * (p : Y) = (p : Y) * m' := hN₀c m' hm' p p.2
  have hmm' : m * m' = m' * m := hN₀c m hm m' (hN₀D hm')
  calc (p : Y) * m * ((p' : Y) * m') = (p : Y) * ((p' : Y) * m) * m' := by
        rw [mul_assoc, ← hmp']
        group
    _ = (p' : Y) * (p : Y) * m * m' := by rw [← hP p p' hp hp']; group
    _ = (p' : Y) * m' * ((p : Y) * m) := by
        calc (p' : Y) * (p : Y) * m * m' = (p' : Y) * (p : Y) * (m * m') := by group
          _ = (p' : Y) * (p : Y) * (m' * m) := by rw [hmm']
          _ = (p' : Y) * ((p : Y) * m') * m := by group
          _ = (p' : Y) * (m' * (p : Y)) * m := by rw [hm'p]
          _ = (p' : Y) * m' * ((p : Y) * m) := by group

omit [Group Y] in
theorem pRank_coe_eq_open {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (T : Subgroup Y) : CFSG.pRank p ↥T = Open.pRank p T := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← pRank_map_of_injective p hp T.subtype
    T.subtype_injective ⊤, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutative_of_isPGroup_of_pRank_le_one [Finite Y] {T : Subgroup Y} (hT : IsPGroup 3 T)
    (hr : Open.pRank 3 T ≤ 1) : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
  have hcyc : IsCyclic T := CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three
    (by norm_num) le_rfl hT (by rw [pRank_coe_eq_open Nat.prime_three]; exact hr)
  intro a ha b hb
  exact congrArg Subtype.val ((IsCyclic.isMulCommutative (α := T)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem card_dvd_three_of_isElemAbelian_of_pRank_le_one [Finite Y] {T : Subgroup Y}
    (hel : IsElemAbelian 3 T) (hT : IsPGroup 3 T) (hr : Open.pRank 3 T ≤ 1) :
    Nat.card T ∣ 3 := by
  have hcyc : IsCyclic T := CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three
    (by norm_num) le_rfl hT (by rw [pRank_coe_eq_open Nat.prime_three]; exact hr)
  obtain ⟨t₀, ht₀⟩ := hcyc.exists_generator
  rw [← orderOf_eq_card_of_forall_mem_zpowers ht₀]
  exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hel.2 _ t₀.2))

theorem commute_of_normal_card_dvd_three [Finite Y] {P W : Subgroup Y} (hP : IsPGroup 3 P)
    (hWP : W ≤ P) (hW : Nat.card W ∣ 3) (hn : ∀ x ∈ P, ∀ w ∈ W, x * w * x⁻¹ ∈ W) :
    ∀ w ∈ W, ∀ x ∈ P, x * w = w * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro w hw x hx
  rcases (Nat.dvd_prime Nat.prime_three).mp hW with h1 | h3
  · have : W = ⊥ := Subgroup.eq_bot_of_card_eq W h1
    rw [this, Subgroup.mem_bot] at hw
    rw [hw]
    simp
  · have : Fact (IsPGroup 3 P) := ⟨hP⟩
    set W' : Subgroup P := W.subgroupOf P with hW'
    have : W'.Normal := ⟨fun n hn' g =>
      Subgroup.mem_subgroupOf.mpr (hn g g.2 n (Subgroup.mem_subgroupOf.mp hn'))⟩
    have hcard : Nat.card W' = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWP).toEquiv, h3]
    have hcent := CFSG.normal_subgroup_card_eq_prime_le_center (p := 3) W' hcard
    have hwW' : (⟨w, hWP hw⟩ : P) ∈ W' := Subgroup.mem_subgroupOf.mpr hw
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcent hwW') ⟨x, hx⟩)

theorem exists_zpowers_sup_centralizer [Finite Y] {L E : Subgroup Y}
    (hEN : E ≤ Subgroup.normalizer (L : Set Y)) (hEL : E ≤ L ⊔ Subgroup.centralizer (L : Set Y))
    (hZ : ¬ 3 ∣ Nat.card (L ⊓ Subgroup.centralizer (L : Set Y) : Subgroup Y))
    (hE3 : IsPGroup 3 E) (hL1 : Open.pRank 3 L ≤ 1) :
    ∃ g ∈ E, E ≤ Subgroup.zpowers g ⊔ Subgroup.centralizer (L : Set Y) := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  set N := Subgroup.normalizer (L : Set Y) with hNdef
  set C := Subgroup.centralizer (L : Set Y) with hCdef
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  set D : Subgroup Y := L ⊓ (E ⊔ C) with hDdef
  have hDN : D ≤ N := inf_le_left.trans hLN
  set C' : Subgroup N := C.subgroupOf N
  have hC'n : C'.Normal := Subgroup.normal_subgroupOf_centralizer_normalizer _
  set D' : Subgroup N := D.subgroupOf N
  set f := QuotientGroup.mk' C'
  set E' : Subgroup N := E.subgroupOf N
  have hmapD : D'.map N.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDN
  have hD' : Open.pRank 3 D' = Open.pRank 3 D := by
    rw [← pRank_map_of_injective 3 h3 N.subtype N.subtype_injective D', hmapD]
  have hmap : E'.map f ≤ D'.map f := by
    rintro _ ⟨e, he, rfl⟩
    have heLC : (e : Y) ∈ ((L ⊔ C : Subgroup Y) : Set Y) := hEL he
    have hNC : N ≤ Subgroup.normalizer (C : Set Y) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L C (hLN.trans hNC)] at heLC
    obtain ⟨l, hl, c, hc, hlc⟩ := heLC
    have hlE : l ∈ E ⊔ C := by
      have : l = (e : Y) * c⁻¹ := by rw [← hlc]; group
      rw [this]
      exact (E ⊔ C).mul_mem (Subgroup.mem_sup_left he) ((E ⊔ C).inv_mem
        (Subgroup.mem_sup_right hc))
    refine ⟨⟨l, hLN hl⟩, ⟨hl, hlE⟩, ?_⟩
    have hcN : (⟨c, hCN hc⟩ : N) ∈ C' := hc
    have he' : e = ⟨l, hLN hl⟩ * ⟨c, hCN hc⟩ := Subtype.ext hlc.symm
    have hfc : f ⟨c, hCN hc⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hcN
    rw [he', map_mul, hfc, mul_one]
  have h2 : Open.pRank 3 (D'.map f) ≤ Open.pRank 3 D' := by
    have hkerD : ¬ 3 ∣ Nat.card (f.comp D'.subtype).ker := by
      intro hdvd
      apply hZ
      set K := (f.comp D'.subtype).ker
      have hinj : Function.Injective (N.subtype.comp D'.subtype) :=
        N.subtype_injective.comp D'.subtype_injective
      have hcard : Nat.card (K.map (N.subtype.comp D'.subtype)) = Nat.card K :=
        Subgroup.card_map_of_injective hinj
      refine hdvd.trans (hcard ▸ Subgroup.card_dvd_of_le ?_)
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨(x.2 : (x : N) ∈ D').1, ?_⟩
      have : ((x : N) : N) ∈ C' := (QuotientGroup.eq_one_iff _).mp hx
      exact this
    have := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd h3 (f.comp D'.subtype) hkerD ⊤
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    calc Open.pRank 3 (D'.map f) ≤ Open.pRank 3 (⊤ : Subgroup D') := this
      _ = Open.pRank 3 D' := by
        rw [← pRank_map_of_injective 3 h3 D'.subtype D'.subtype_injective ⊤,
          ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hDL : Open.pRank 3 D ≤ Open.pRank 3 L := pRank_mono 3 h3 inf_le_left
  have hS3 : IsPGroup 3 (E'.map f) := by
    have : IsPGroup 3 E' := hE3.comap_subtype
    exact this.map f
  have hSr : Open.pRank 3 (E'.map f) ≤ 1 :=
    (pRank_mono 3 h3 hmap).trans (h2.trans (hD'.le.trans (hDL.trans hL1)))
  have hcyc : IsCyclic (E'.map f) := CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one h3
    (by norm_num) le_rfl hS3 (by rw [pRank_coe_eq_open h3]; exact hSr)
  obtain ⟨⟨s, hs⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥(E'.map f))
  obtain ⟨e₀, he₀, rfl⟩ := hs
  refine ⟨(e₀ : Y), Subgroup.mem_subgroupOf.mp he₀, fun e he => ?_⟩
  have hfe : f ⟨e, hEN he⟩ ∈ E'.map f := ⟨⟨e, hEN he⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨f ⟨e, hEN he⟩, hfe⟩)
  have hk' : f e₀ ^ k = f ⟨e, hEN he⟩ := congrArg Subtype.val hk
  have hfx : f ((⟨e, hEN he⟩ : N) * e₀ ^ (-k)) = 1 := by
    rw [map_mul, map_zpow, zpow_neg, hk']
    exact mul_inv_cancel _
  have hker : (⟨e, hEN he⟩ : N) * e₀ ^ (-k) ∈ C' := (QuotientGroup.eq_one_iff _).mp hfx
  have hc : e * (e₀ : Y) ^ (-k) ∈ C := by
    have := Subgroup.mem_subgroupOf.mp hker
    simpa using this
  have : e = (e * (e₀ : Y) ^ (-k)) * (e₀ : Y) ^ k := by group
  rw [this, sup_comm]
  exact Subgroup.mul_mem_sup hc (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k)

end CFSG.LocalAnalysis.RankThreeTheoremC

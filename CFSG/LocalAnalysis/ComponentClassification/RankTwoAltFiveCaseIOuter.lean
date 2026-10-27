module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseIH
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools CFSG.GorensteinWalter
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoAlt

variable {G : Type} [Group G] [Finite G]

namespace CaseICoords

variable {A B R T : Subgroup G} (c : CaseICoords A B R T)

abbrev Hbar : Type := c.H ⧸ CFSG.pPrimeCore 2 c.H

@[expose] def barOf {M : Subgroup G} (hM : M ≤ c.H) : M →* c.Hbar :=
  (QuotientGroup.mk' (CFSG.pPrimeCore 2 c.H)).comp (inclusion hM)

omit [Finite G] in
theorem barOf_apply {M : Subgroup G} (hM : M ≤ c.H) (m : M) :
    c.barOf hM m = ((⟨m, hM m.2⟩ : c.H) : c.Hbar) := rfl

theorem odd_card_core : Odd (Nat.card (CFSG.pPrimeCore 2 c.H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp CFSG.pPrimeCore_coprime_card))

omit [Finite G] in
theorem mk_eq_one_iff (h : c.H) : (h : c.Hbar) = 1 ↔ (h : G) ∈ c.O := by
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hh
    exact ⟨h, hh, rfl⟩
  · rintro ⟨y, hy, hye⟩
    rwa [← Subtype.ext hye]

theorem barOf_injective {M : Subgroup G} (hM : M ≤ c.H) (e : M ≃* A5) :
    Function.Injective (c.barOf hM) := by
  have : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup M := e.isSimpleGroup
  rcases (c.barOf hM).normal_ker.eq_bot_or_eq_top with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    have hle : M ≤ c.O := fun m hm => by
      have h1 : (⟨m, hm⟩ : M) ∈ (c.barOf hM).ker := h ▸ mem_top _
      exact (c.mk_eq_one_iff ⟨m, hM hm⟩).mp h1
    have hd := Subgroup.card_dvd_of_le hle
    rw [Nat.card_congr e.toEquiv, card_A5] at hd
    exact (Nat.not_even_iff_odd.mpr c.odd_card_O) (even_iff_two_dvd.mpr
      ((show (2 : ℕ) ∣ 60 by norm_num).trans hd))

omit [Finite G] in
theorem range_le_of_mem {M : Subgroup G} (hM : M ≤ c.H) (e : M ≃* A5) {L : Subgroup c.Hbar}
    [L.Normal] {m : M} (hm : m ≠ 1) (hmL : c.barOf hM m ∈ L) : (c.barOf hM).range ≤ L := by
  have : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup M := e.isSimpleGroup
  have hn : (L.comap (c.barOf hM)).Normal := Subgroup.Normal.comap inferInstance _
  rcases hn.eq_bot_or_eq_top with h | h
  · have hm' : m ∈ L.comap (c.barOf hM) := mem_comap.mpr hmL
    rw [h, mem_bot] at hm'
    exact absurd hm' hm
  · rintro _ ⟨y, rfl⟩
    exact mem_comap.mp (h ▸ mem_top y)

theorem mem_of_mul_self {L : Subgroup c.Hbar} [hLn : L.Normal] (hLi : Odd L.index) {h : c.Hbar}
    (hh : h * h = 1) : h ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (zpowers h) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hh) : orderOf h ∣ 2 ^ 1)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  exact subgroup_le_of_isPGroup_coindex_odd L hLn hLi _ hP (mem_zpowers h)

@[expose] def Rbar : Subgroup c.Hbar := (c.barOf c.R_le_H).range

theorem barOf_R_injective : Function.Injective (c.barOf c.R_le_H) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have hrO : (r : G) ∈ c.O := (c.mk_eq_one_iff _).mp hr
  have hr2 : (r : G) * r = 1 := c.mul_self_of_mem_R r.2
  have hodd : Odd (orderOf (r : G)) := by
    have h1 : orderOf (r : G) ∣ Nat.card c.O := by
      rw [← Subgroup.orderOf_mk (r : G) hrO]
      exact orderOf_dvd_natCard _
    exact c.odd_card_O.of_dvd_nat h1
  have hd : orderOf (r : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hr2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact Subtype.ext (orderOf_eq_one_iff.mp h)
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem card_Rbar : Nat.card c.Rbar = 4 := by
  rw [Rbar, ← Nat.card_congr (MonoidHom.ofInjective c.barOf_R_injective).toEquiv,
    c.pair.card_R]

theorem mul_self_of_mem_Rbar {q : c.Hbar} (hq : q ∈ c.Rbar) : q * q = 1 := by
  obtain ⟨r, rfl⟩ := hq
  rw [← map_mul, show r * r = 1 from Subtype.ext (c.mul_self_of_mem_R r.2), map_one]

theorem isKleinFour_Rbar : IsKleinFour c.Rbar := by
  refine ⟨c.card_Rbar, ?_⟩
  have hsq : ∀ y : c.Rbar, y ^ 2 = 1 := fun y =>
    Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact c.mul_self_of_mem_Rbar y.2)
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton c.Rbar := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : c.Rbar)
    have := c.card_Rbar
    omega
  · exact h

theorem Rbar_le {L : Subgroup c.Hbar} [L.Normal] (hLi : Odd L.index) : c.Rbar ≤ L :=
  fun _ hq => c.mem_of_mul_self hLi (c.mul_self_of_mem_Rbar hq)

theorem exists_mem_R : ∃ s : c.H, (s : G) ∈ R ∧ (s : G) ≠ 1 ∧ (s : c.Hbar) ≠ 1 ∧
    (s : c.Hbar) ∈ c.Rbar ∧ (s : c.Hbar) * s = 1 := by
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp c.pair.R_ne_bot
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hne : c.barOf c.R_le_H ⟨r, hr⟩ ≠ 1 := fun h =>
    hr1 (c.barOf_R_injective (by rw [h, map_one]))
  refine ⟨⟨r, c.R_le_H hr⟩, hr, hr1', hne, ⟨⟨r, hr⟩, rfl⟩, ?_⟩
  exact c.mul_self_of_mem_Rbar ⟨⟨r, hr⟩, rfl⟩

theorem eq_one_of_commute_of_odd
    {L : Subgroup c.Hbar} {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hL : Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K)) (hRL : c.Rbar ≤ L) {s : c.H}
    (hs : (s : G) ∈ R) (hs1 : (s : G) ≠ 1) {q : c.Hbar} (hqL : q ∈ L)
    (hq : (s : c.Hbar) * q = q * s) (hodd : Odd (orderOf q)) : q = 1 := by
  have hs2 : s * s = 1 := Subtype.ext (c.mul_self_of_mem_R hs)
  obtain ⟨y, rfl, hys⟩ := exists_lift_commute c.odd_card_core hs2 q hq
  have hyodd : Odd (orderOf (y : G)) := by
    rw [Subgroup.orderOf_coe]
    exact odd_orderOf_of_odd_mk c.odd_card_core hodd
  have hyB := c.mem_centralizer_of_odd hs hs1 y.2 (congrArg Subtype.val hys).symm hyodd
  have hC : (y : c.Hbar) ∈ centralizer (c.Rbar : Set c.Hbar) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨r, rfl⟩
    rw [barOf_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp hyB r (c.pair.R_le r.2))
  have hV : (y : c.Hbar) ∈ c.Rbar := by
    rw [← inf_centralizer_eq_of_linear hK hL hRL c.isKleinFour_Rbar]
    exact ⟨hqL, hC⟩
  have h2 := c.mul_self_of_mem_Rbar hV
  have hd : orderOf (y : c.Hbar) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

@[expose] def Bx : Subgroup G := B.map (MulAut.conj c.x).toMonoidHom

theorem Bx_le_H : c.Bx ≤ c.H := by
  rintro _ ⟨b, hb, rfl⟩
  exact (mem_normalizer_iff.mp c.x_mem_normalizer b).mp (c.B_le_H hb)

@[expose] noncomputable def equivBx : c.Bx ≃* A5 :=
  (B.equivMapOfInjective _ (MulAut.conj c.x).injective).symm.trans c.ψB.symm

theorem false_of_range_le (h : (c.barOf c.Bx_le_H).range ≤ (c.barOf c.B_le_H).range) : False := by
  have hBinj := c.barOf_injective c.B_le_H c.ψB.symm
  have hdec : ∀ b' ∈ c.Bx, ∃ b ∈ B, b⁻¹ * b' ∈ c.O := by
    intro b' hb'
    obtain ⟨⟨b, hb⟩, hbe⟩ := h ⟨⟨b', hb'⟩, rfl⟩
    refine ⟨b, hb, ?_⟩
    have h1 : ((⟨b⁻¹ * b', mul_mem (inv_mem (c.B_le_H hb)) (c.Bx_le_H hb')⟩ : c.H) : c.Hbar) =
        1 := by
      have : (⟨b⁻¹ * b', mul_mem (inv_mem (c.B_le_H hb)) (c.Bx_le_H hb')⟩ : c.H) =
          (⟨b, c.B_le_H hb⟩ : c.H)⁻¹ * ⟨b', c.Bx_le_H hb'⟩ := rfl
      rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [barOf_apply, barOf_apply] at hbe
      rw [hbe, inv_mul_cancel]
    exact (c.mk_eq_one_iff _).mp h1
  have hBO : ∀ g ∈ B, g ∈ c.O → g = 1 := by
    intro g hg hgO
    have h1 : c.barOf c.B_le_H ⟨g, hg⟩ = 1 := (c.mk_eq_one_iff ⟨g, c.B_le_H hg⟩).mpr hgO
    exact congrArg Subtype.val (hBinj (h1.trans (map_one _).symm))
  have hOodd : ∀ o ∈ c.O, o * o = 1 → o = 1 := by
    intro o ho ho2
    have hodd : Odd (orderOf o) := by
      have h1 : orderOf o ∣ Nat.card c.O := by
        rw [← Subgroup.orderOf_mk o ho]
        exact orderOf_dvd_natCard _
      exact c.odd_card_O.of_dvd_nat h1
    have hd : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ho2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h' | h'
    · exact orderOf_eq_one_iff.mp h'
    · rw [h'] at hodd
      exact absurd hodd (by decide)
  have hBxN : c.Bx ≤ normalizer (B : Set G) := by
    intro b' hb'
    obtain ⟨b, hb, ho⟩ := hdec b' hb'
    have : b' = b * (b⁻¹ * b') := by group
    rw [this]
    exact mul_mem (le_normalizer hb)
      (Subgroup.centralizer_le_normalizer _ (c.O_le_centralizer ho))
  have hinv : ∀ b' ∈ c.Bx, b' * b' = 1 → b' ∈ B := by
    intro b' hb' h2
    obtain ⟨b, hb, ho⟩ := hdec b' hb'
    set o := b⁻¹ * b' with ho_def
    have hbo : b * o = o * b := mem_centralizer_iff.mp (c.O_le_centralizer ho) b hb
    have hb' : b' = b * o := by rw [ho_def]; group
    have h3 : (b * b) * (o * o) = 1 := by
      rw [← h2, hb']
      calc b * b * (o * o) = b * (b * o) * o := by group
        _ = b * (o * b) * o := by rw [hbo]
        _ = b * o * (b * o) := by group
    have h4 : o * o ∈ c.O := mul_mem ho ho
    have h5 : (b * b) = (o * o)⁻¹ := eq_inv_of_mul_eq_one_left h3
    have h6 : b * b = 1 := hBO _ (mul_mem hb hb) (h5 ▸ inv_mem h4)
    have h7 : o * o = 1 := by rw [h6, one_mul] at h3; exact h3
    rw [hb', hOodd o ho h7, mul_one]
    exact hb
  have hBxB : c.Bx ≤ B := by
    have : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup c.Bx := c.equivBx.isSimpleGroup
    have hn : ((B ⊓ c.Bx).subgroupOf c.Bx).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨hnB, hnBx⟩ := mem_inf.mp hn
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hBxN g.2) n).mp hnB,
        mul_mem (mul_mem g.2 hnBx) (inv_mem g.2)⟩
    obtain ⟨s, hs, hs1, -, -, -⟩ := c.exists_mem_R
    have hsB : (s : G) ∈ B := c.pair.R_le hs
    set s' : G := c.x * s * c.x⁻¹ with hs'
    have hs'Bx : s' ∈ c.Bx := ⟨s, hsB, rfl⟩
    have hs'2 : s' * s' = 1 := by
      calc s' * s' = c.x * ((s : G) * s) * c.x⁻¹ := by rw [hs']; group
        _ = 1 := by rw [c.mul_self_of_mem_R hs, mul_one, mul_inv_cancel]
    have hs'1 : s' ≠ 1 := fun h' => hs1 (by
      have : (s : G) = c.x⁻¹ * s' * c.x := by rw [hs']; group
      rw [this, h', mul_one, inv_mul_cancel])
    rcases hn.eq_bot_or_eq_top with h' | h'
    · exfalso
      have hmem : (⟨s', hs'Bx⟩ : c.Bx) ∈ (B ⊓ c.Bx).subgroupOf c.Bx :=
        mem_subgroupOf.mpr (mem_inf.mpr ⟨hinv s' hs'Bx hs'2, hs'Bx⟩)
      rw [h', mem_bot] at hmem
      exact hs'1 (congrArg Subtype.val hmem)
    · intro b' hb'
      have hmem : (⟨b', hb'⟩ : c.Bx) ∈ (B ⊓ c.Bx).subgroupOf c.Bx := h' ▸ mem_top _
      exact (mem_inf.mp (mem_subgroupOf.mp hmem)).1
  have hxN : c.x ∈ normalizer (B : Set G) :=
    RankTwoAlt.mem_normalizer_of_conj_le fun b hb => hBxB ⟨b, hb, rfl⟩
  have hxN' : c.x⁻¹ ∈ normalizer (B : Set G) := inv_mem hxN
  set t : G := (c.ψA k1 : G) with ht
  have hkT : ∀ k ∈ P0, ((c.ψA k : A) : G) ∈ T := fun k hk => by
    have h' : c.ψA k ∈ T.subgroupOf A := c.mapA ▸ mem_map_of_mem _ hk
    exact mem_subgroupOf.mp h'
  have htT : t ∈ T := hkT k1 (by decide)
  have htC : t ∈ centralizer (B : Set G) := c.pair.sylowT.le htT
  have hm : c.x * t * c.x⁻¹ ∈ A ⊓ centralizer (B : Set G) := by
    refine mem_inf.mpr ⟨mul_mem (mul_mem c.x_mem (c.ψA k1).2) (inv_mem c.x_mem), ?_⟩
    rw [mem_centralizer_iff]
    intro b hb
    have hb' : c.x⁻¹ * b * c.x ∈ B := by
      have := (mem_normalizer_iff.mp hxN' b).mp hb
      rwa [inv_inv] at this
    have h1 := mem_centralizer_iff.mp htC _ hb'
    calc b * (c.x * t * c.x⁻¹) = c.x * ((c.x⁻¹ * b * c.x) * t) * c.x⁻¹ := by group
      _ = c.x * (t * (c.x⁻¹ * b * c.x)) * c.x⁻¹ := by rw [h1]
      _ = c.x * t * c.x⁻¹ * b := by group
  have hmN := c.pair.inf_centralizer_le hm
  apply not_norm_x0_k1
  intro q hq
  have hqT : ((c.ψA q : A) : G) ∈ T := hkT q (mem_P0.mpr hq)
  have h1 := (mem_normalizer_iff.mp hmN _).mp hqT
  have h2 : c.ψA (x0 * k1 * x0⁻¹ * q * (x0 * k1 * x0⁻¹)⁻¹) ∈ T.subgroupOf A := by
    rw [mem_subgroupOf]
    simpa [ht, x, map_mul, map_inv] using h1
  rw [← c.mapA] at h2
  obtain ⟨q', hq', hq'e⟩ := h2
  rw [← c.ψA.injective hq'e]
  exact mem_P0.mp hq'

theorem false_of_card_sixty {L : Subgroup c.Hbar} [L.Normal] (hLi : Odd L.index)
    (hL : Nat.card L = 60) : False := by
  apply c.false_of_range_le
  obtain ⟨s, hs, hs1, -, -, -⟩ := c.exists_mem_R
  have hsB : (s : G) ∈ B := c.pair.R_le hs
  have hs2 : (s : G) * s = 1 := c.mul_self_of_mem_R hs
  have hBL : (c.barOf c.B_le_H).range ≤ L := by
    refine c.range_le_of_mem c.B_le_H c.ψB.symm (m := ⟨s, hsB⟩)
      (fun h => hs1 (congrArg Subtype.val h)) (c.mem_of_mul_self hLi ?_)
    rw [← map_mul, show (⟨s, hsB⟩ : B) * ⟨s, hsB⟩ = 1 from Subtype.ext hs2, map_one]
  have hBcard : Nat.card (c.barOf c.B_le_H).range = 60 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (c.barOf_injective c.B_le_H c.ψB.symm)).toEquiv,
      Nat.card_congr c.ψB.symm.toEquiv, card_A5]
  have hBeq : (c.barOf c.B_le_H).range = L :=
    eq_of_le_of_card_ge hBL (by rw [hBcard, hL])
  set s' : G := c.x * s * c.x⁻¹ with hs'
  have hs'Bx : s' ∈ c.Bx := ⟨s, hsB, rfl⟩
  have hs'2 : s' * s' = 1 := by
    calc s' * s' = c.x * ((s : G) * s) * c.x⁻¹ := by rw [hs']; group
      _ = 1 := by rw [hs2, mul_one, mul_inv_cancel]
  have hs'1 : (⟨s', hs'Bx⟩ : c.Bx) ≠ 1 := fun h => hs1 (by
    have h1 : s' = 1 := congrArg Subtype.val h
    have : (s : G) = c.x⁻¹ * s' * c.x := by rw [hs']; group
    rw [this, h1, mul_one, inv_mul_cancel])
  rw [hBeq]
  refine c.range_le_of_mem c.Bx_le_H c.equivBx hs'1 (c.mem_of_mul_self hLi ?_)
  rw [← map_mul, show (⟨s', hs'Bx⟩ : c.Bx) * ⟨s', hs'Bx⟩ = 1 from Subtype.ext hs'2, map_one]

theorem range_B_le {L : Subgroup c.Hbar} [L.Normal] (hLi : Odd L.index) :
    (c.barOf c.B_le_H).range ≤ L := by
  obtain ⟨s, hs, hs1, -, -, -⟩ := c.exists_mem_R
  have hsB : (s : G) ∈ B := c.pair.R_le hs
  refine c.range_le_of_mem c.B_le_H c.ψB.symm (m := ⟨s, hsB⟩)
    (fun h => hs1 (congrArg Subtype.val h)) (c.mem_of_mul_self hLi ?_)
  rw [← map_mul, show (⟨s, hsB⟩ : B) * ⟨s, hsB⟩ = 1 from Subtype.ext (c.mul_self_of_mem_R hs),
    map_one]

theorem card_range_B : Nat.card (c.barOf c.B_le_H).range = 60 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (c.barOf_injective c.B_le_H c.ψB.symm)).toEquiv,
    Nat.card_congr c.ψB.symm.toEquiv, card_A5]

theorem not_eight_dvd (hS : IsSylowOf 2 R c.H) : ¬ 8 ∣ Nat.card c.Hbar := by
  intro h8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : 2 ^ 3 ∣ Nat.card c.H := by
    rw [card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore 2 c.H)]
    exact Dvd.dvd.mul_right h8 _
  have hpos : Nat.card c.H ≠ 0 := Nat.card_pos.ne'
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos] at hH
  have hfac := hS.card_eq
  rw [c.pair.card_R] at hfac
  have h2 : (2 : ℕ) ^ 2 = 2 ^ (Nat.card c.H).factorization 2 := by rw [← hfac]; norm_num
  have := Nat.pow_right_injective le_rfl h2
  omega

theorem hasDihedralSylowTwo (hS : IsSylowOf 2 R c.H) : HasDihedralSylowTwo c.H := by
  obtain ⟨S, hS⟩ := hS
  have hcard : Nat.card (S : Subgroup c.H) = 4 := by
    rw [← card_map_of_injective c.H.subtype_injective, hS, c.pair.card_R]
  have hsq : ∀ y : (S : Subgroup c.H), y ^ 2 = 1 := by
    intro y
    have hy : ((y : c.H) : G) ∈ (S : Subgroup c.H).map c.H.subtype := ⟨y, y.2, rfl⟩
    rw [hS] at hy
    apply Subtype.ext
    apply Subtype.ext
    simpa [sq] using c.mul_self_of_mem_R hy
  have hK : IsKleinFour (S : Subgroup c.H) := by
    refine ⟨hcard, ?_⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
      h | h
    · have : Subsingleton (S : Subgroup c.H) := Monoid.exp_eq_one_iff.mp h
      have := Nat.card_of_subsingleton (1 : (S : Subgroup c.H))
      omega
    · exact h
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := (S : Subgroup c.H)) (G₂ := DihedralGroup 2)
  exact hasDihedralSylowTwo_of_equiv S (m := 1) le_rfl e

theorem card_eq_three_or_five
    (h8 : ¬ 8 ∣ Nat.card c.Hbar) {L : Subgroup c.Hbar} [L.Normal] (hLi : Odd L.index)
    {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K)) (e : L ≃* PSL2 K) :
    Nat.card K = 3 ∨ Nat.card K = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVL : c.Rbar ≤ L := c.Rbar_le hLi
  obtain ⟨s, hs, hs1, hsb1, hsV, hsb2⟩ := c.exists_mem_R
  set sb := (s : c.Hbar) with hsb
  have hsbL : sb ∈ L := hVL hsV
  set t := e ⟨sb, hsbL⟩ with ht_def
  have ht : orderOf t = 2 := by
    rw [ht_def, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hsb2) hsb1
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hK
  have hqodd : Odd (Nat.card K) := by rw [hq]; exact hpodd.pow
  have key : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → (Nat.card K : ℤ) ≡ ε [ZMOD 4] →
      (Nat.card K : ℤ) - ε = 4 := by
    intro ε hε1 hε
    obtain ⟨m, hm, ⟨d⟩⟩ :=
      CFSG.ABGDGroups.psl2_centralizer_involution_dihedral ⟨p, n, hp, hpodd, hn, hq⟩ hε hε1 ht
    have hcardC : Nat.card (centralizer ({t} : Set (PSL2 K))) = 2 * m := by
      rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
    have hdvd : 2 * m ∣ Nat.card c.Hbar := by
      have h1 := Subgroup.card_subgroup_dvd_card (centralizer ({t} : Set (PSL2 K)))
      rw [hcardC, ← Nat.card_congr e.toEquiv] at h1
      exact h1.trans (Subgroup.card_subgroup_dvd_card L)
    have h4 : ¬ 4 ∣ m := fun h => h8 ((Nat.mul_dvd_mul_left 2 h).trans hdvd)
    have hmε : (4 : ℤ) ∣ (Nat.card K : ℤ) - ε := hε.symm.dvd
    have hm2 : m % 2 = 0 := by omega
    by_contra hne
    have hm_ne : m ≠ 2 := fun h => hne (by rw [← hm, h]; norm_num)
    set z : centralizer ({t} : Set (PSL2 K)) := d.symm (DihedralGroup.r 1 ^ 2) with hz_def
    have hz : orderOf z = m / 2 := by
      rw [hz_def, MulEquiv.orderOf_eq, orderOf_pow' _ two_ne_zero, DihedralGroup.orderOf_r_one,
        Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero hm2)]
    set yL : L := e.symm (z : PSL2 K) with hyL
    have hyc : sb * (yL : c.Hbar) = (yL : c.Hbar) * sb := by
      have hzt : (z : PSL2 K) * t = t * z := mem_centralizer_singleton_iff.mp z.2
      have hte : e.symm t = ⟨sb, hsbL⟩ := by rw [ht_def, MulEquiv.symm_apply_apply]
      have := congrArg e.symm hzt
      rw [map_mul, map_mul, hte] at this
      have := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at this
      exact this.symm
    have hyord : orderOf (yL : c.Hbar) = m / 2 := by
      rw [Subgroup.orderOf_coe, hyL, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hz]
    have hyodd : Odd (orderOf (yL : c.Hbar)) := by
      rw [hyord]
      exact Nat.odd_iff.mpr (by omega)
    have h1 := c.eq_one_of_commute_of_odd ⟨p, n, hp, hpodd, hn, hq⟩ (Or.inl ⟨e⟩) hVL hs hs1
      yL.2 hyc hyodd
    rw [h1, orderOf_one] at hyord
    omega
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hqodd) with h | h
  · have := key 1 (Or.inl rfl) (by show (Nat.card K : ℤ) % 4 = 1 % 4; omega)
    right; omega
  · have := key (-1) (Or.inr rfl) (by show (Nat.card K : ℤ) % 4 = (-1) % 4; omega)
    left; omega

theorem false_of_isSylowOf
    (hS : IsSylowOf 2 R c.H) : False := by
  have h8 := c.not_eight_dvd hS
  rcases gw_cases (c.hasDihedralSylowTwo hS) with h2 | hA | ⟨K, _, _, hK, L, hLn, hLi, hLm⟩
  ·
    have hinj := c.barOf_injective c.B_le_H c.ψB.symm
    obtain ⟨k, hk⟩ := h2 (c.barOf c.B_le_H (c.ψB y0))
    have h3 : c.barOf c.B_le_H (c.ψB y0) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, ← orderOf_y0, pow_orderOf_eq_one, map_one, map_one]
    have h1 := eq_one_of_pow_three h3 hk
    have : y0 = 1 := c.ψB.injective (hinj (by rw [h1, map_one, map_one]))
    exact absurd this (by decide)
  · obtain ⟨eA⟩ := hA
    apply h8
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · have hodd : Odd (Nat.card K) := by
      obtain ⟨p, n, -, hpodd, -, hq⟩ := hK
      rw [hq]
      exact hpodd.pow
    rcases hLm with hL | hL
    · obtain ⟨e⟩ := hL
      have h60 : 60 ≤ Nat.card L := by
        rw [← c.card_range_B]
        exact Subgroup.card_le_of_le (c.range_B_le hLi)
      rcases c.card_eq_three_or_five h8 hLi hK e with h3 | h5
      · rw [Nat.card_congr e.toEquiv, psl2_card_formula K hK, h3] at h60
        norm_num at h60
      · exact c.false_of_card_sixty hLi
          (by rw [Nat.card_congr e.toEquiv, psl2_card_formula K hK, h5]; norm_num)
    · obtain ⟨e⟩ := hL
      apply h8
      have h1 : 8 ∣ Nat.card L := by
        rw [Nat.card_congr e.toEquiv, pgl2_card_formula]
        exact Dvd.dvd.mul_left (Nat.eight_dvd_sq_sub_one_of_odd hodd) _
      exact h1.trans (Subgroup.card_subgroup_dvd_card L)

theorem isSylowOf_R (h : ∀ u ∈ c.H ⊓ normalizer (R : Set G), (∃ k : ℕ, u ^ 2 ^ k = 1) →
    ∀ hu : u ∈ normalizer (A : Set G), Perm.sign (autPerm c.ψA.symm ⟨u, hu⟩) ≠ -1) :
    IsSylowOf 2 R c.H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := (c.pair.isPGroup_R.comap_subtype (K := c.H)).exists_le_sylow
  set S := (S' : Subgroup c.H).map c.H.subtype
  have hS : IsSylowOf 2 S c.H := ⟨S', rfl⟩
  have hRS : R ≤ S := fun y hy => ⟨⟨y, c.R_le_H hy⟩, hS' (mem_subgroupOf.mpr hy), rfl⟩
  by_cases hSR : S ≤ R
  · have hSeq : S = R := le_antisymm hSR hRS
    rw [hSeq] at hS
    exact hS
  exfalso
  obtain ⟨a, haS, haN, haR⟩ := exists_mem_normalizer_of_not_le hS.isPGroup hRS hSR
  have haH : a ∈ c.H := hS.le haS
  obtain ⟨k, hk⟩ := hS.isPGroup ⟨a, haS⟩
  have hak : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have haA : a ∈ normalizer (A : Set G) := c.pair.normalizer_R_le haN
  have hsign : Perm.sign (autPerm c.ψA.symm ⟨a, haA⟩) = 1 := by
    rcases Int.units_eq_one_or (Perm.sign (autPerm c.ψA.symm ⟨a, haA⟩)) with h' | h'
    · exact h'
    · exact absurd h' (h a ⟨haH, haN⟩ ⟨k, hak⟩ haA)
  set σ := autPerm c.ψA.symm ⟨a, haA⟩ with hσ
  have hσk : σ ^ 2 ^ k = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨a, haA⟩ : normalizer (A : Set G)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hak)
    rw [this, map_one]
  have hy3 : (y0 : Perm (Fin 5)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← orderOf_y0, pow_orderOf_eq_one, Subgroup.coe_one]
  have hσ3 : σ ^ 3 = 1 := by
    rcases eq_of_commute_y0 σ (c.autPerm_commute haH haA) hsign with h1 | h1 | h1
    · rw [h1, one_pow]
    · rw [h1, hy3]
    · rw [h1, ← sq, ← pow_mul, mul_comm, pow_mul, hy3, one_pow]
  have haK : a ∈ centralizer (A : Set G) :=
    (autPerm_eq_one_iff c.ψA.symm _).mp (eq_one_of_pow_three hσ3 hσk)
  have hQp : IsPGroup 2 (S ⊓ centralizer (A : Set G) : Subgroup G) :=
    hS.isPGroup.to_le inf_le_left
  have h4 := Seven.card_le_card_of_isSylowOf c.pair.sylowR inf_le_right hQp
  have hlt : R < S ⊓ centralizer (A : Set G) :=
    lt_of_le_of_ne (le_inf hRS c.pair.sylowR.le) fun h' => haR (h' ▸ mem_inf.mpr ⟨haS, haK⟩)
  exact absurd (card_lt_of_lt hlt) (not_lt.mpr h4)

theorem exists_outer :
    ∃ u ∈ c.H ⊓ normalizer (R : Set G), (∃ k : ℕ, u ^ 2 ^ k = 1) ∧
      ∃ hu : u ∈ normalizer (A : Set G), Perm.sign (autPerm c.ψA.symm ⟨u, hu⟩) = -1 := by
  by_contra hno
  push Not at hno
  exact c.false_of_isSylowOf (c.isSylowOf_R hno)

end CaseICoords

end CFSG.ComponentClassification.RankTwoAltFive

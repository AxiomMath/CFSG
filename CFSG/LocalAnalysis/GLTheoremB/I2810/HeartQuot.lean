module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport
import CFSG.LargeExtraspecial.S7Perm

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.HeartQuot

section Abstract
variable {G : Type*} [Group G]

theorem mem_zpowers_two {x z : G} (hx : x ^ 2 = 1) (hz : z ∈ Subgroup.zpowers x) :
    z = 1 ∨ z = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hx' : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; simpa [pow_two] using hx
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, hx', one_zpow]
  · right
    rw [zpow_add, zpow_mul, hx', one_zpow, one_mul, zpow_one]

theorem card_sup_le_of_le_normalizer [Finite G] (S T : Subgroup G)
    (h : S ≤ Subgroup.normalizer (T : Set G)) : Nat.card ↥(S ⊔ T) ≤ Nat.card S * Nat.card T := by
  have hco := Subgroup.coe_mul_of_left_le_normalizer_right S T h
  let f : ↥S × ↥T → ↥(S ⊔ T) := fun p => ⟨(p.1 : G) * p.2, Subgroup.mul_mem _
    (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    have : g ∈ (↑(S ⊔ T) : Set G) := hg
    rw [hco] at this
    obtain ⟨s, hs, t, ht, rfl⟩ := this
    exact ⟨(⟨s, hs⟩, ⟨t, ht⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod] at this

theorem s3_of_gen [Finite G] (N : Subgroup G) [N.Normal] (x y : G)
    (hx2 : x ^ 2 ∈ N) (hxN : x ∉ N) (hy3 : y ^ 3 ∈ N) (hyN : y ∉ N)
    (hxy : x * y * x⁻¹ * y ∈ N)
    (hgen : ∀ H : Subgroup G, N ≤ H → x ∈ H → y ∈ H → H = ⊤) :
    Nat.card (G ⧸ N) = 6 ∧ Nonempty ((G ⧸ N) ≃* Equiv.Perm (Fin 3)) := by
  classical
  have hx2' : ((x : G ⧸ N)) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 hx2
  have hy3' : ((y : G ⧸ N)) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 hy3
  have hx1 : (x : G ⧸ N) ≠ 1 := fun h => hxN ((QuotientGroup.eq_one_iff _).1 h)
  have hy1 : (y : G ⧸ N) ≠ 1 := fun h => hyN ((QuotientGroup.eq_one_iff _).1 h)
  have hxy' : (x : G ⧸ N) * y * (x : G ⧸ N)⁻¹ = (y : G ⧸ N)⁻¹ := by
    have := (QuotientGroup.eq_one_iff _).2 hxy
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    exact eq_inv_of_mul_eq_one_left this
  set x' : G ⧸ N := (x : G ⧸ N) with hx'
  set y' : G ⧸ N := (y : G ⧸ N) with hy'
  have hox : orderOf x' = 2 := orderOf_eq_prime hx2' hx1
  have hoy : orderOf y' = 3 := orderOf_eq_prime hy3' hy1
  have hE : Subgroup.zpowers x' ⊔ Subgroup.zpowers y' = ⊤ := by
    have h := hgen ((Subgroup.zpowers x' ⊔ Subgroup.zpowers y').comap (QuotientGroup.mk' N))
      (fun n hn => by
        rw [Subgroup.mem_comap, show QuotientGroup.mk' N n = 1 from (QuotientGroup.eq_one_iff n).2 hn]
        exact one_mem _)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers x'))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y'))
    rw [eq_top_iff]
    intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have : g ∈ (Subgroup.zpowers x' ⊔ Subgroup.zpowers y').comap (QuotientGroup.mk' N) :=
      h ▸ Subgroup.mem_top g
    exact this
  have hxi : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx2')
  have hfwd : ∀ w ∈ Subgroup.zpowers y', x' * w * x'⁻¹ ∈ Subgroup.zpowers y' := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← conj_zpow, hxy']
    exact Subgroup.zpow_mem _ (inv_mem (Subgroup.mem_zpowers y')) k
  have hxn : Subgroup.zpowers x' ≤
      Subgroup.normalizer ((Subgroup.zpowers y' : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hfwd g
    · intro hk
      have := hfwd _ hk
      have h2 : x' * (x' * g * x'⁻¹) * x'⁻¹ = g := by
        calc x' * (x' * g * x'⁻¹) * x'⁻¹ = (x' * x') * g * (x' * x')⁻¹ := by group
          _ = g := by rw [← pow_two, hx2']; group
      rwa [h2] at this
  have hcard_le : Nat.card (G ⧸ N) ≤ 6 := by
    have h1 := card_sup_le_of_le_normalizer (Subgroup.zpowers x') (Subgroup.zpowers y') hxn
    rw [hE, Subgroup.card_top, Nat.card_zpowers, Nat.card_zpowers, hox, hoy] at h1
    exact h1
  have h6 : 6 ∣ Nat.card (G ⧸ N) := by
    have h2 : 2 ∣ Nat.card (G ⧸ N) := hox ▸ orderOf_dvd_natCard x'
    have h3 : 3 ∣ Nat.card (G ⧸ N) := hoy ▸ orderOf_dvd_natCard y'
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hcard : Nat.card (G ⧸ N) = 6 :=
    le_antisymm hcard_le (Nat.le_of_dvd Nat.card_pos h6)
  refine ⟨hcard, ?_⟩
  refine CFSG.LargeExtraspecial.S7.nonempty_mulEquiv_perm_three hcard
    (T := Subgroup.zpowers x') (by rw [Nat.card_zpowers, hox]) ?_
  intro hn
  have hmem := hn.conj_mem x' (Subgroup.mem_zpowers x') y'
  have hmem' : y' * x' * y'⁻¹ ∈ Subgroup.zpowers x' := hmem
  have hxsq : x' ^ 2 = 1 := hx2'
  rcases mem_zpowers_two hxsq hmem' with h1 | h1
  · apply hx1
    have := congrArg (fun u => y'⁻¹ * u * y') h1
    simpa [mul_assoc] using this
  · have hc : x' * y' = y' * x' := by
      calc x' * y' = (y' * x' * y'⁻¹) * y' := by rw [h1]
        _ = y' * x' := by group
    have h2 : y' = y'⁻¹ := by
      calc y' = x' * y' * x'⁻¹ := by rw [hc]; group
        _ = y'⁻¹ := hxy'
    have h3 : y' ^ 2 = 1 := by
      rw [pow_two]; nth_rewrite 1 [h2]; exact inv_mul_cancel y'
    have h4 : y' ^ Nat.gcd 2 3 = 1 := pow_gcd_eq_one.mpr ⟨h3, hy3'⟩
    exact hy1 (by simpa using h4)

end Abstract

section Concrete
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem sq_mem {a : X} (hS2 : ∀ s ∈ S, s ∈ kerAct W K S ∨ a⁻¹ * s ∈ kerAct W K S) (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) : a ^ 2 ∈ kerAct W K S := by
  rcases hS2 (a ^ 2) (S.pow_mem haS 2) with h | h
  · exact h
  · exfalso
    apply hna
    have : a⁻¹ * a ^ 2 = a := by rw [pow_two]; group
    rwa [this] at h

theorem relIndex_two (hR : Red28 W K S) {a : X} (haS : a ∈ S) (hna : a ∉ kerAct W K S)
    (hS2 : ∀ s ∈ S, s ∈ kerAct W K S ∨ a⁻¹ * s ∈ kerAct W K S) :
    ((kerAct W K S).subgroupOf S).index = 2 := by
  have ha2 : a ^ 2 ∈ kerAct W K S := sq_mem hS2 haS hna
  have haN : a ∈ K ⊔ S := Subgroup.mem_sup_right haS
  refine Subgroup.index_eq_two_iff.mpr ⟨⟨a, haS⟩, fun b => ?_⟩
  obtain ⟨s, hs⟩ := b
  by_cases hsW : s ∈ kerAct W K S
  · right
    refine ⟨Subgroup.mem_subgroupOf.mpr hsW, fun hba => hna ?_⟩
    have hba' : s * a ∈ kerAct W K S := Subgroup.mem_subgroupOf.mp hba
    have := (kerAct W K S).mul_mem ((kerAct W K S).inv_mem hsW) hba'
    simpa using this
  · left
    refine ⟨?_, fun h' => hsW (Subgroup.mem_subgroupOf.mp h')⟩
    rcases hS2 s hs with h | h
    · exact absurd h hsW
    · rw [Subgroup.mem_subgroupOf]
      have h1 : s * a = (a * (a⁻¹ * s) * a⁻¹) * a ^ 2 := by rw [pow_two]; group
      show s * a ∈ kerAct W K S
      rw [h1]
      exact (kerAct W K S).mul_mem (hR.w1_nrm a haN _ h) ha2

theorem quot_aux (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) (hS2 : ∀ s ∈ S, s ∈ kerAct W K S ∨ a⁻¹ * s ∈ kerAct W K S)
    {p : X} (hp : p ∈ K) (hp3 : p ^ 3 = 1) (hpn : p ∉ kerAct W K S)
    (hpa : a * p * a⁻¹ * p ∈ kerAct W K S) :
    CFSG.QuasithinUnique.IsSylowTwoOf S (S ⊔ Subgroup.zpowers p) ∧
      CFSG.QuasithinUnique.CharTwo (S ⊔ Subgroup.zpowers p) ∧
      pCoreOf 2 (S ⊔ Subgroup.zpowers p) = kerAct W K S ∧
      Nonempty (↥(S ⊔ Subgroup.zpowers p) ⧸ CFSG.pCore 2 ↥(S ⊔ Subgroup.zpowers p) ≃*
        Equiv.Perm (Fin 3)) := by
  classical
  set Y : Subgroup X := S ⊔ Subgroup.zpowers p with hY
  have hSY : S ≤ Y := le_sup_left
  have hpY : p ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers p)
  have hYN : Y ≤ K ⊔ S :=
    sup_le le_sup_right (Subgroup.zpowers_le.2 (Subgroup.mem_sup_left hp))
  have hW₁Y : kerAct W K S ≤ Y := hR.w1_S.trans hSY
  set N₁ : Subgroup ↥Y := (kerAct W K S).subgroupOf Y with hN₁
  haveI hN₁n : N₁.Normal :=
    ⟨fun n hn g => by
      rw [hN₁, Subgroup.mem_subgroupOf] at hn ⊢
      have := hR.w1_nrm (g : X) (hYN g.2) (n : X) hn
      simpa using this⟩
  have ha2 : a ^ 2 ∈ kerAct W K S := sq_mem hS2 haS hna
  have hsq := s3_of_gen N₁ (⟨a, hSY haS⟩ : ↥Y) (⟨p, hpY⟩ : ↥Y)
    (by rw [hN₁, Subgroup.mem_subgroupOf]; exact ha2)
    (by rw [hN₁, Subgroup.mem_subgroupOf]; exact hna)
    (by
      rw [hN₁, Subgroup.mem_subgroupOf]
      show p ^ 3 ∈ kerAct W K S
      rw [hp3]; exact one_mem _)
    (by rw [hN₁, Subgroup.mem_subgroupOf]; exact hpn)
    (by rw [hN₁, Subgroup.mem_subgroupOf]; exact hpa)
    (by
      intro H hNH hxH hyH
      have hSH : S ≤ H.map Y.subtype := by
        intro s hs
        rcases hS2 s hs with h1 | h1
        · exact ⟨⟨s, hSY hs⟩, hNH (by rw [hN₁, Subgroup.mem_subgroupOf]; exact h1), rfl⟩
        · have hmem : (⟨a⁻¹ * s, hSY (S.mul_mem (S.inv_mem haS) hs)⟩ : ↥Y) ∈ H :=
            hNH (by rw [hN₁, Subgroup.mem_subgroupOf]; exact h1)
          refine ⟨⟨a, hSY haS⟩ * ⟨a⁻¹ * s, hSY (S.mul_mem (S.inv_mem haS) hs)⟩,
            H.mul_mem hxH hmem, ?_⟩
          simp
      have hpH : Subgroup.zpowers p ≤ H.map Y.subtype :=
        Subgroup.zpowers_le.2 ⟨⟨p, hpY⟩, hyH, rfl⟩
      have hYH : Y ≤ H.map Y.subtype := sup_le hSH hpH
      rw [eq_top_iff]
      intro g _
      obtain ⟨g', hg', hgg'⟩ := hYH g.2
      have : g' = g := Subtype.ext hgg'
      rwa [this] at hg')
  obtain ⟨hcard6, ⟨eQ⟩⟩ := hsq
  have hN₁2 : IsPGroup 2 ↥N₁ :=
    (h.hS.to_le hR.w1_S).of_equiv (Subgroup.subgroupOfEquivOfLe hW₁Y).symm
  have hpc : CFSG.pCore 2 ↥Y = N₁ := by
    apply le_antisymm
    · intro g hg
      have hnorm : ((CFSG.pCore 2 ↥Y).map (QuotientGroup.mk' N₁)).Normal :=
        (CFSG.pCore_normal).map _ (QuotientGroup.mk'_surjective N₁)
      have hP : IsPGroup 2 ↥((CFSG.pCore 2 ↥Y).map (QuotientGroup.mk' N₁)) :=
        CFSG.pCore_isPGroup.map _
      have hbot := CFSG.Semidihedral.Local.normal_isPGroup_two_eq_bot eQ _ hnorm hP
      have hmem : (QuotientGroup.mk' N₁ g) ∈ (CFSG.pCore 2 ↥Y).map (QuotientGroup.mk' N₁) :=
        Subgroup.mem_map_of_mem _ hg
      rw [hbot, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff g).1 hmem
    · exact le_sSup ⟨hN₁n, hN₁2⟩
  have hcore : pCoreOf 2 Y = kerAct W K S := by
    unfold pCoreOf
    rw [hpc, hN₁, Subgroup.map_subgroupOf_eq_of_le hW₁Y]
  have hidxS := relIndex_two hR haS hna hS2
  have hcardY : Nat.card ↥Y = 6 * Nat.card ↥(kerAct W K S) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N₁, hcard6]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₁Y).toEquiv
  have hcardS : Nat.card ↥S = 2 * Nat.card ↥(kerAct W K S) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((kerAct W K S).subgroupOf S)]
    have : Nat.card (↥S ⧸ (kerAct W K S).subgroupOf S) = 2 := hidxS
    rw [this]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR.w1_S).toEquiv
  refine ⟨⟨hSY, h.hS, ?_⟩, ?_, hcore, ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans eQ⟩⟩
  · intro h2
    have hmul := Subgroup.card_mul_index (S.subgroupOf Y)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv, hcardS, hcardY] at hmul
    have hpos : 0 < Nat.card ↥(kerAct W K S) := Nat.card_pos
    have h3 : (S.subgroupOf Y).index = 3 := by
      have : (S.subgroupOf Y).index * 2 * Nat.card ↥(kerAct W K S) =
          3 * 2 * Nat.card ↥(kerAct W K S) := by
        calc (S.subgroupOf Y).index * 2 * Nat.card ↥(kerAct W K S)
            = 2 * Nat.card ↥(kerAct W K S) * (S.subgroupOf Y).index := by ring
          _ = 6 * Nat.card ↥(kerAct W K S) := hmul
          _ = 3 * 2 * Nat.card ↥(kerAct W K S) := by ring
      have := Nat.eq_of_mul_eq_mul_right (by positivity) this
      omega
    rw [h3] at h2
    omega
  · unfold CFSG.QuasithinUnique.CharTwo
    rw [hcore]
    exact inf_le_right.trans hR.w1_cent

end Concrete

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.HeartQuot

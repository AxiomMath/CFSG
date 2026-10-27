module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7LocA9P
public import CFSG.GH74.Generic.BProg.B3.S3T2A7WS
public import CFSG.GH74.Generic.AltCerts
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.GlueAut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Elementary
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.SignalizerPerm

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7Loc

open CFSG CFSG.Blueprint CFSG.GH74 Subgroup Equiv
open CFSG.ProperTwoGeneratedCore.Lemma37 CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

theorem mem_of_centralizer_of_sq_mem {Y : Type} [Group Y] [Finite Y]
    (hY : SectionalTwoRankLE Y 4) {L : Subgroup Y}
    (hc3 : Generic.RankCertified (↥L ⧸ center ↥L) 3)
    {c : Y} (hcL : c ∈ centralizer (L : Set Y)) (hc2 : c * c ∈ L) : c ∈ L := by
  by_contra hc
  set M : Subgroup Y := L ⊔ zpowers c with hMdef
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl => mem_centralizer_iff.mp hcL l hl
  have hMc : ∀ m ∈ M, m * c = c * m := by
    intro m hm
    have hle : M ≤ centralizer ({c} : Set Y) := sup_le
      (fun l hl => mem_centralizer_singleton_iff.mpr (hLc l hl))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    exact mem_centralizer_singleton_iff.mp (hle hm)
  set N : Subgroup Y := L ⊓ centralizer (L : Set Y) with hNdef
  have hNc : ∀ x ∈ N, ∀ m ∈ M, m * x = x * m := by
    intro x hx m hm
    have hle : M ≤ centralizer ({x} : Set Y) := sup_le
      (fun l hl => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx.2 l hl))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hLc x hx.1).symm))
    exact mem_centralizer_singleton_iff.mp (hle hm)
  have hNn : (N.subgroupOf M).Normal := ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    rw [coe_mul, coe_mul, coe_inv, hNc x hx g g.2, mul_inv_cancel_right]
    exact hx⟩
  let π : ↥M →* ↥M ⧸ N.subgroupOf M := QuotientGroup.mk' _
  let cM : ↥M := ⟨c, mem_sup_right (mem_zpowers c)⟩
  let K : Subgroup (↥M ⧸ N.subgroupOf M) := (L.subgroupOf M).map π
  let ψ : ↥L →* ↥K := (π.comp (inclusion (le_sup_left : L ≤ M))).codRestrict K fun l =>
    ⟨inclusion le_sup_left l, (mem_subgroupOf).mpr l.2, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, mem_subgroupOf.mp hx⟩, rfl⟩
  have hker : ψ.ker = center ↥L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hl g
      have h1 : π (inclusion le_sup_left l) = 1 := congrArg Subtype.val hl
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      exact Subtype.ext (mem_centralizer_iff.mp h1.2 g g.2)
    · intro hl
      apply Subtype.ext
      change π (inclusion le_sup_left l) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
      refine ⟨l.2, mem_centralizer_iff.mpr fun g hg => ?_⟩
      exact congrArg Subtype.val (hl ⟨g, hg⟩)
  have hK3 : Generic.RankCertified ↥K 3 := hc3.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))
  have hcc : ∀ x : ↥M ⧸ N.subgroupOf M, x * π cM = π cM * x := by
    intro x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hMc m m.2))
  have hc2' : π cM * π cM = 1 := by
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    refine ⟨hc2, mem_centralizer_iff.mpr fun g hg => ?_⟩
    change g * (c * c) = c * c * g
    rw [← mul_assoc, hLc g hg, mul_assoc, hLc g hg, ← mul_assoc]
  have hcK : π cM ∉ K := by
    rintro ⟨x, hx, hxc⟩
    apply hc
    have h1 : x⁻¹ * cM ∈ N.subgroupOf M := by
      have h0 : π (x⁻¹ * cM) = 1 := by rw [map_mul, map_inv, hxc, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h0
    have hx' : (x : Y) ∈ L := hx
    have h1' : (x : Y)⁻¹ * c ∈ N := h1
    have h2 : (x : Y) * ((x : Y)⁻¹ * c) ∈ L := L.mul_mem hx' h1'.1
    rwa [mul_inv_cancel_left] at h2
  have hM4 : Generic.RankCertified ↥M 4 :=
    (Generic.RankCertified.of_central_involution hcc hc2' hcK hK3).of_quotient (N.subgroupOf M)
  exact hM4.of_subgroup.not_sectionalTwoRankLE hY

theorem mem_alternatingGroup_of_odd {σ : Perm (Fin 9)} (h : Odd (orderOf σ)) :
    σ ∈ alternatingGroup (Fin 9) := by
  rw [Perm.mem_alternatingGroup]
  rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
  · exact h1
  · exfalso
    have h2 := congrArg Perm.sign (pow_orderOf_eq_one σ)
    rw [map_pow, h1, map_one, h.neg_one_pow] at h2
    exact absurd h2 (by decide)

theorem cell125_alt9 (hF : Generic.GenericKnownFacts) : S3T2A7.Cell125 S3T2A7.Alt9 := by
  intro Y _ _ L B X₀ z hs hL _ hcut
  classical
  obtain ⟨e⟩ := hL
  have hc3 : Generic.RankCertified (↥L ⧸ center ↥L) 3 :=
    (Generic.rankCertified_alternating (n := 9) (by norm_num)).of_mulEquiv e.symm
  have hzL : z ∈ L := S3T2A7.mem_of_rankCertified_three hs hc3
  have hnorm := S3T2A7.normal_of_rankCertified hs.sec4 hs.comp (hc3.mono (by norm_num))
  have hLn : L.Normal := ⟨fun l hl g => (mem_normalizer_iff.mp (hnorm g) l).mp hl⟩
  have hzc : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp hs.z_cent g)
  have hZne : center ↥L ≠ ⊥ := fun h => by
    rw [h, mem_bot] at hzc
    exact hs.z_ne (congrArg Subtype.val hzc)
  have hP2 : IsPGroup 2 ↥(center ↥L) := GLS.isPGroup_two_center_of_subnormal hs.core hs.comp.2
  have hle2 := hF.alt_cover 9 (by norm_num) (by norm_num) ↥L hs.comp.1 hP2 ⟨e⟩
  have hcard2 : Nat.card (center ↥L) = 2 := by
    have := (one_lt_card_iff_ne_bot _).mpr hZne
    omega
  have hJ : IsTwoANine ↥L := ⟨hs.comp.1.1, hcard2, ⟨e⟩⟩
  set ρ : Y →* Perm (Fin 9) := conjPerm e with hρ
  have hkerρ : ∀ m, ρ m = 1 → m ∈ centralizer (L : Set Y) := fun m hm =>
    mem_centralizer_of_conjPerm_eq_one hJ.perfect e hm
  have hBel := hs.B_el
  have hsqB : ∀ b ∈ B, b * b = 1 := fun b hb => by
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) b hb
    rwa [sq] at this
  have hcommB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥B) ⟨b, hb⟩)
  have hcardB : Nat.card ↥B = 16 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.IsElementaryAbelian.isPGroup 2 ↥B)
    have hr := CFSG.pRank_eq_of_card_eq_pow one_lt_two hk
    rw [hk, ← hr, hs.B_rank]
    norm_num
  have hmemL : ∀ b : Y, b * b = 1 → ρ b ∈ alternatingGroup (Fin 9) → b ∈ L := by
    intro b hb2 hbA
    obtain ⟨l, hl⟩ := TwoANine.proj_surjective e ⟨ρ b, hbA⟩
    have hρl : ρ (l : Y) = ρ b := by rw [hρ, conjPerm_coe, hl]
    set c : Y := (l : Y)⁻¹ * b with hcdef
    have hρc : ρ c = 1 := by rw [hcdef, map_mul, map_inv, hρl, inv_mul_cancel]
    have hcC := hkerρ c hρc
    have hlc : (l : Y) * c = c * l := mem_centralizer_iff.mp hcC l l.2
    have hb : (l : Y) * c = b := by rw [hcdef, mul_inv_cancel_left]
    have hcc : c * c ∈ L := by
      have h1 : (l : Y) * l * (c * c) = 1 := by
        calc (l : Y) * l * (c * c) = (l : Y) * (l * c) * c := by group
          _ = (l : Y) * (c * l) * c := by rw [hlc]
          _ = ((l : Y) * c) * ((l : Y) * c) := by group
          _ = 1 := by rw [hb, hb2]
      rw [eq_inv_of_mul_eq_one_right h1]
      exact L.inv_mem (L.mul_mem l.2 l.2)
    rw [← hb]
    exact L.mul_mem l.2 (mem_of_centralizer_of_sq_mem hs.sec4 hc3 hcC hcc)
  have hBL : B ≤ L := by
    intro b₀ hb₀
    by_contra hb₀L
    have hodd : Perm.sign (ρ b₀) = -1 := by
      rcases Int.units_eq_one_or (Perm.sign (ρ b₀)) with h | h
      · exact absurd (hmemL b₀ (hsqB b₀ hb₀) (Perm.mem_alternatingGroup.mpr h)) hb₀L
      · exact h
    let χ : ↥B →* ℤˣ := Perm.sign.comp (ρ.comp B.subtype)
    have hχ : Function.Surjective χ := by
      intro u
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact ⟨1, map_one χ⟩
      · exact ⟨⟨b₀, hb₀⟩, hodd⟩
    have hcardK : Nat.card χ.ker = 8 := by
      have h1 := Subgroup.card_mul_index χ.ker
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hχ, card_top,
        Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int, hcardB] at h1
      omega
    let B₀ : Subgroup Y := χ.ker.map B.subtype
    have hB₀B : B₀ ≤ B := map_subtype_le _
    have hB₀L : B₀ ≤ L := by
      rintro _ ⟨b, hb, rfl⟩
      exact hmemL b (hsqB b b.2) (Perm.mem_alternatingGroup.mpr hb)
    let E₀ : Subgroup ↥L := B₀.subgroupOf L
    have hE₀card : Nat.card E₀ = 8 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hB₀L).toEquiv,
        card_map_of_injective B.subtype_injective, hcardK]
    have hE₀2 : ∀ x ∈ E₀, x ^ 2 = 1 := fun x hx =>
      Subtype.ext (by rw [sq, coe_mul, coe_one]; exact hsqB _ (hB₀B hx))
    have hF₀ : 2 < Nat.card (E₀.map (TwoANine.proj e)) := by
      have h1 := hJ.card_comap_proj e (E₀.map (TwoANine.proj e))
      have h2 : Nat.card E₀ ≤ Nat.card ((E₀.map (TwoANine.proj e)).comap (TwoANine.proj e)) :=
        card_le_of_le (le_comap_map _ _)
      omega
    refine false_of_odd_involution_commute (IsTwoANine.isPGroup_map_proj e hE₀2)
      (fun g hg hg1 => hJ.cycleType_of_mem_map_proj e hE₀2 hg hg1) hF₀
      (by rw [← map_mul, hsqB b₀ hb₀, map_one]) hodd ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← conjPerm_coe, ← map_mul, ← map_mul]
    exact congrArg (conjPerm e) (hcommB _ (hB₀B hx) b₀ hb₀)
  obtain ⟨f, hfB, -, -, n, hn, -, hnc⟩ := hcut
  set O : Subgroup Y := CFSG.Assembly.Dichotomy.involutionOddCore f with hOdef
  have hOodd : Odd (Nat.card O) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hOdef, CFSG.Assembly.Dichotomy.involutionOddCore,
      card_map_of_injective (subtype_injective _), CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hBO : ∀ b ∈ B, ∀ o ∈ O, b * o * b⁻¹ ∈ O := by
    intro b hb o ho
    obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
    have hbC : b ∈ centralizer ({f} : Set Y) :=
      mem_centralizer_singleton_iff.mpr (hcommB b hb f hfB)
    exact mem_map.mpr ⟨⟨b, hbC⟩ * o' * ⟨b, hbC⟩⁻¹,
      (CFSG.Assembly.oddCore_normal _).conj_mem o' ho' _, rfl⟩
  set K₀ : Subgroup (Perm (Fin 9)) := O.map ρ with hK₀def
  have hK₀odd : Odd (Nat.card K₀) := Odd.of_dvd_nat hOodd (card_map_dvd O ρ)
  have hK₀A : K₀ ≤ alternatingGroup (Fin 9) := fun k hk =>
    mem_alternatingGroup_of_odd (Odd.of_dvd_nat hK₀odd (Subgroup.orderOf_dvd_natCard K₀ hk))
  set K : Subgroup (alternatingGroup (Fin 9)) := K₀.comap (alternatingGroup (Fin 9)).subtype
  have hKodd : Odd (Nat.card K) := by
    have hmap : K.map (alternatingGroup (Fin 9)).subtype = K₀ :=
      map_comap_eq_self (by rwa [range_subtype])
    rw [← hmap, card_map_of_injective (subtype_injective _)] at hK₀odd
    exact hK₀odd
  let E : Subgroup ↥L := B.subgroupOf L
  have hEcard : Nat.card E = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBL).toEquiv, hcardB]
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := fun x hx =>
    Subtype.ext (by rw [sq, coe_mul, coe_one]; exact hsqB _ hx)
  obtain ⟨p, hp, -⟩ := hJ.existsUnique_forall_apply_eq_of_card_eq e hE2 hEcard
  have hconj : ∀ x ∈ E, ∀ k ∈ K, TwoANine.proj e x * k * (TwoANine.proj e x)⁻¹ ∈ K := by
    intro x hx k hk
    obtain ⟨o, ho, hok⟩ := mem_map.mp (show (k : Perm (Fin 9)) ∈ K₀ from hk)
    show ((TwoANine.proj e x * k * (TwoANine.proj e x)⁻¹ : alternatingGroup (Fin 9)) :
      Perm (Fin 9)) ∈ K₀
    rw [coe_mul, coe_mul, coe_inv, ← conjPerm_coe, ← hok, ← map_inv, ← map_mul, ← map_mul]
    exact mem_map_of_mem ρ (hBO _ hx o ho)
  have hFK : E.map (TwoANine.proj e) ≤ normalizer (K : Set (alternatingGroup (Fin 9))) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_normalizer_iff]
    intro k
    refine ⟨hconj x hx k, fun hk => ?_⟩
    have h1 := hconj x⁻¹ (E.inv_mem hx) _ hk
    simpa [mul_assoc] using h1
  have hKbot := eq_bot_of_odd_of_regular_le_normalizer (F := E.map (TwoANine.proj e)) (K := K)
    (p := p)
    (fun g hg => IsTwoANine.sq_eq_one_of_mem_map_proj e hE2 hg) hp
    (fun i j hi hj => hJ.existsUnique_mem_map_proj_apply_eq e hE2 hEcard hp hi hj) hKodd hFK
  have hρn : ρ n = 1 := by
    have hn' : ρ n ∈ K₀ := mem_map_of_mem ρ hn
    have hnK : (⟨ρ n, hK₀A hn'⟩ : alternatingGroup (Fin 9)) ∈ K := hn'
    rw [hKbot, mem_bot] at hnK
    exact congrArg Subtype.val hnK
  exact hnc (hkerρ n hρn)

end CFSG.GH74.Generic.BProg.B3.S3T2A7Loc

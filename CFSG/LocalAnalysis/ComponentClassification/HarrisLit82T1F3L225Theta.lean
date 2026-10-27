module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L225Core

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open scoped commutatorElement Pointwise

namespace F3L225

theorem le_pPrimeCore_of_isSubnormal_of_odd {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : S.IsSubnormal) (hodd : Odd (Nat.card S)) : S ≤ pPrimeCore 2 X := by
  have key := F3L221.map_pPrimeCore_eq_inf hS
  have htop : pPrimeCore 2 ↥S = ⊤ := by
    apply top_unique
    unfold pPrimeCore
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    rw [Subgroup.card_top]
    exact Nat.coprime_two_left.mpr hodd
  rw [htop, ← MonoidHom.range_eq_map, range_subtype] at key
  exact inf_eq_left.mp key.symm

variable {Q : Type} [Group Q] [Finite Q]

theorem commute_of_three {L M : Subgroup Q} {t : Q} (hLs : L.IsSubnormal)
    (hLq : IsQuasisimple ↥L) (ht : orderOf t = 2) (htL : t ∈ L)
    (hM : IsSolvableTwoComponentIn M (centralizer {t})) (hMN : M ≤ normalizer (L : Set Q))
    (h2 : ∀ s ∈ M, (∃ n : ℕ, s ^ 2 ^ n = 1) → ∀ l ∈ L, s * l = l * s)
    (hnot : ¬ ∀ s ∈ M, (∃ n : ℕ, s ^ 2 ^ n = 1) → s ∈ L)
    (hθ : IsThetaBalanced (↥L ⧸ center ↥L)) :
    ∀ y ∈ M, (∃ n : ℕ, y ^ 3 ^ n = 1) → ∀ l ∈ L, y * l = l * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases htc : ∀ l ∈ L, t * l = l * t
  · intro y hy _ l hl
    exact F3L221.commute_of_centralizes hLs hLq htc hM y hy l hl
  push Not at htc
  obtain ⟨l₀, hl₀, hl₀t⟩ := htc
  have hMU := centralizes_centralInvolutions htL hM hMN hnot
  set U := centralInvolutions L with hU
  have hLp : Group.IsPerfect ↥L := hLq.1
  set H := L ⊔ M with hH
  have hLH : L ≤ H := le_sup_left
  have hMH : M ≤ H := le_sup_right
  have hHN : H ≤ normalizer (L : Set Q) := sup_le le_normalizer hMN
  have hHmul : ∀ {h : Q}, h ∈ H → ∃ l ∈ L, ∃ m ∈ M, h = l * m := by
    intro h hh
    have hhs : h ∈ ((L ⊔ M : Subgroup Q) : Set Q) := hh
    rw [coe_mul_of_right_le_normalizer_left L M hMN] at hhs
    obtain ⟨l, hl, m, hm, hlm⟩ := hhs
    exact ⟨l, hl, m, hm, hlm.symm⟩
  have hHU : ∀ h ∈ H, ∀ u ∈ U, h * u = u * h := by
    intro h hh u hu
    obtain ⟨l, hl, m, hm, rfl⟩ := hHmul hh
    have h1 : l * u = u * l := (hu.2.1 l hl).symm
    have h3 : m * u = u * m := hMU m hm u hu
    calc l * m * u = l * (u * m) := by rw [mul_assoc, h3]
      _ = u * (l * m) := by rw [← mul_assoc, h1, mul_assoc]
  set C := (centralizer (L : Set Q)).subgroupOf H with hCdef
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [mem_subgroupOf, mem_centralizer_iff] at hc ⊢
    intro l hl
    have hgN := hHN g.2
    have hl' : (g : Q)⁻¹ * l * g ∈ L := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hgN) l).mp hl
      rwa [inv_inv] at h1
    have h1 := hc _ hl'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc l * ((g : Q) * c * (g : Q)⁻¹) = g * (((g : Q)⁻¹ * l * g) * c) * (g : Q)⁻¹ := by group
      _ = g * (c * ((g : Q)⁻¹ * l * g)) * (g : Q)⁻¹ := by rw [h1]
      _ = (g : Q) * c * (g : Q)⁻¹ * l := by group
  set π := QuotientGroup.mk' C with hπ
  have hπ1 : ∀ x : ↥H, π x = 1 ↔ (x : Q) ∈ centralizer (L : Set Q) := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hCdef, mem_subgroupOf]
  set Lt := (L.subgroupOf H).map π with hLt
  have hLHn : (L.subgroupOf H).Normal := by
    refine ⟨fun l hl g => ?_⟩
    rw [mem_subgroupOf] at hl ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.mp (hHN g.2) l).mp hl
  have hLtn : Lt.Normal := hLHn.map π (QuotientGroup.mk'_surjective C)
  let ψ : ↥L →* ↥Lt :=
    { toFun := fun l => ⟨π ⟨l, hLH l.2⟩, ⟨⟨l, hLH l.2⟩, l.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp only [OneMemClass.coe_one]
        exact map_one π
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul π ⟨a, hLH a.2⟩ ⟨b, hLH b.2⟩ }
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hψk : ψ.ker = center ↥L := by
    ext l
    rw [MonoidHom.mem_ker, mem_center_iff]
    constructor
    · intro h g
      have h1 : π ⟨l, hLH l.2⟩ = 1 := congrArg Subtype.val h
      rw [hπ1, mem_centralizer_iff] at h1
      exact Subtype.ext (h1 g g.2)
    · intro h
      apply Subtype.ext
      change π ⟨l, hLH l.2⟩ = 1
      rw [hπ1, mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (h ⟨g, hg⟩)
  let eL : ↥L ⧸ center ↥L ≃* ↥Lt :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have : IsSimpleGroup (↥L ⧸ center ↥L) := hLq.2.1
  have hLts : IsSimpleGroup ↥Lt := eL.symm.isSimpleGroup
  have hLtab : ∃ a b : ↥Lt, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hLq.2.2
    refine ⟨eL a, eL b, fun h => hab ?_⟩
    apply eL.injective
    rw [map_mul, map_mul, h]
  have hCL : centralizer (Lt : Set (↥H ⧸ C)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h, rfl⟩ : ∃ h, π h = x := QuotientGroup.mk'_surjective C x
    rw [mem_bot, hπ1]
    rw [mem_centralizer_iff] at hx
    have hcomm : ∀ l ∈ L, ∀ m ∈ L, (l * (h : Q) * l⁻¹ * (h : Q)⁻¹) * m =
        m * (l * (h : Q) * l⁻¹ * (h : Q)⁻¹) := by
      intro l hl m hm
      have h1 := hx (π ⟨l, hLH hl⟩) ⟨⟨l, hLH hl⟩, hl, rfl⟩
      have h2 : π (⟨l, hLH hl⟩ * h * ⟨l, hLH hl⟩⁻¹ * h⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      rw [hπ1, mem_centralizer_iff] at h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      exact (h2 m hm).symm
    have h3 := F3L226.commute_of_commutator_mem_center hLp (hHN h.2) hcomm
    rw [mem_centralizer_iff]
    intro l hl
    exact h3 l hl
  have hF : Open.genFittingFStar (↥H ⧸ C) = Lt :=
    ClassicalInvolution.genFittingFStar_eq_of_normal_simple Lt hLtab hCL
  have hFiso : Nonempty (↥(Open.genFittingFStar (↥H ⧸ C)) ≃* (↥L ⧸ center ↥L)) :=
    ⟨(MulEquiv.subgroupCongr hF).trans eL.symm⟩
  set t' : ↥H := ⟨t, hLH htL⟩ with ht'
  set tt := π t' with htt
  have htt1 : tt ≠ 1 := by
    intro h
    rw [htt, hπ1, mem_centralizer_iff] at h
    exact hl₀t (h l₀ hl₀).symm
  have htt2 : orderOf tt = 2 := by
    apply orderOf_eq_prime _ htt1
    rw [htt, ← map_pow]
    have h1 : t' ^ 2 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one, ht']
      rw [← ht, pow_orderOf_eq_one]
    rw [h1, map_one]
  have hθH := hθ (↥H ⧸ C) hFiso tt htt2
  set P := (centralizer ({tt} : Set (↥H ⧸ C))).comap π with hP
  set CH := centralizer ({t'} : Set ↥H) with hCH
  have hCHP : CH ≤ P := by
    intro q hq
    rw [hP, mem_comap, mem_centralizer_singleton_iff, htt, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp hq]
  have hcommU : ∀ p ∈ P, (p : Q) * t * (p : Q)⁻¹ * t⁻¹ ∈ U := by
    intro p hp
    rw [hP, mem_comap, mem_centralizer_singleton_iff] at hp
    have hζC : (p : Q) * t * (p : Q)⁻¹ * t⁻¹ ∈ centralizer (L : Set Q) := by
      have h1 : π (p * t' * p⁻¹ * t'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← htt]
        calc π p * tt * (π p)⁻¹ * tt⁻¹ = (π p * tt) * ((π p)⁻¹ * tt⁻¹) := by group
          _ = (tt * π p) * ((π p)⁻¹ * tt⁻¹) := by rw [hp]
          _ = 1 := by group
      rw [hπ1] at h1
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, ht'] using h1
    have hζL : (p : Q) * t * (p : Q)⁻¹ * t⁻¹ ∈ L := by
      refine mul_mem ?_ (inv_mem htL)
      exact (mem_normalizer_iff.mp (hHN p.2) t).mp htL
    refine ⟨hζL, fun l hl => ((mem_centralizer_iff.mp hζC) l hl).symm, ?_⟩
    have hζt : ((p : Q) * t * (p : Q)⁻¹ * t⁻¹) * t = t * ((p : Q) * t * (p : Q)⁻¹ * t⁻¹) :=
      ((mem_centralizer_iff.mp hζC) t htL).symm
    have htt' : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
    calc ((p : Q) * t * (p : Q)⁻¹ * t⁻¹) * ((p : Q) * t * (p : Q)⁻¹ * t⁻¹)
        = (p : Q) * (t * t) * (p : Q)⁻¹ * t⁻¹ * t⁻¹ := by
          calc ((p : Q) * t * (p : Q)⁻¹ * t⁻¹) * ((p : Q) * t * (p : Q)⁻¹ * t⁻¹)
              = ((p : Q) * t * (p : Q)⁻¹ * t⁻¹) * (((p : Q) * t * (p : Q)⁻¹ * t⁻¹) * t) * t⁻¹ :=
                by group
            _ = ((p : Q) * t * (p : Q)⁻¹ * t⁻¹) * (t * ((p : Q) * t * (p : Q)⁻¹ * t⁻¹)) * t⁻¹ := by
                rw [hζt]
            _ = (p : Q) * (t * t) * (p : Q)⁻¹ * t⁻¹ * t⁻¹ := by group
      _ = 1 := by
          rw [htt', mul_one, mul_inv_cancel, one_mul, ← mul_inv_rev, htt', inv_one]
  have hCHn : (CH.subgroupOf P).Normal := by
    refine ⟨fun q hq p => ?_⟩
    rw [mem_subgroupOf] at hq ⊢
    rw [mem_centralizer_singleton_iff] at hq ⊢
    have hq' : (q : ↥H) * t' = t' * q := hq
    have hζ₂ := hcommU p⁻¹ (inv_mem p.2)
    set ζ₂ := ((p⁻¹ : ↥P) : ↥H) * t' * ((p⁻¹ : ↥P) : ↥H)⁻¹ * t'⁻¹ with hζ₂def
    have hζ₂U : (ζ₂ : Q) ∈ U := by
      simpa only [hζ₂def, Subgroup.coe_mul, Subgroup.coe_inv, ht'] using hζ₂
    have hqζ : (q : ↥H) * ζ₂ = ζ₂ * q := Subtype.ext (hHU _ (q : ↥H).2 _ hζ₂U)
    have hpζ : ((p : ↥P) : ↥H) * ζ₂ = ζ₂ * p := Subtype.ext (hHU _ (p : ↥H).2 _ hζ₂U)
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have key : ((p : ↥H) * q * (p : ↥H)⁻¹) * t' = t' * ((p : ↥H) * q * (p : ↥H)⁻¹) := by
      have hpt : (p : ↥H)⁻¹ * t' * p = ζ₂ * t' := by
        rw [hζ₂def]
        simp only [InvMemClass.coe_inv]
        group
      have hrel : t' = (p : ↥H) * (ζ₂ * t') * (p : ↥H)⁻¹ := by
        rw [← hpt]
        group
      calc ((p : ↥H) * q * (p : ↥H)⁻¹) * t'
          = (p : ↥H) * q * ((p : ↥H)⁻¹ * t' * p) * (p : ↥H)⁻¹ := by group
        _ = (p : ↥H) * (q * (ζ₂ * t')) * (p : ↥H)⁻¹ := by rw [hpt]; group
        _ = (p : ↥H) * ((ζ₂ * t') * q) * (p : ↥H)⁻¹ := by
            have hqz : (q : ↥H) * (ζ₂ * t') = (ζ₂ * t') * q := by
              rw [← mul_assoc, hqζ, mul_assoc, hq', ← mul_assoc]
            rw [hqz]
        _ = ((p : ↥H) * (ζ₂ * t') * (p : ↥H)⁻¹) * ((p : ↥H) * q * (p : ↥H)⁻¹) := by group
        _ = t' * ((p : ↥H) * q * (p : ↥H)⁻¹) := by rw [← hrel]
    exact congrArg Subtype.val key
  have hMHs : ((M.subgroupOf H).subgroupOf CH).IsSubnormal := by
    have hCHeq : CH = (H ⊓ centralizer ({t} : Set Q)).subgroupOf H := by
      ext x
      rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      constructor
      · intro h
        exact ⟨x.2, congrArg Subtype.val h⟩
      · rintro ⟨-, h⟩
        exact Subtype.ext h
    rw [hCHeq, GroupTheory.isSubnormal_subgroupOf_subgroupOf_iff inf_le_left]
    exact F3L226.isSubnormal_subgroupOf_mono inf_le_right
      (show (M.subgroupOf (centralizer {t})).IsSubnormal from hM.2.1)
  have hMCH : M.subgroupOf H ≤ CH := by
    intro m hm
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hM.1 hm)
  have hMPs : ((M.subgroupOf H).subgroupOf P).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hMCH hCHP hMHs hCHn.isSubnormal
  set Mt := (M.subgroupOf H).map π with hMt
  have hMtC : Mt ≤ centralizer ({tt} : Set (↥H ⧸ C)) := by
    rintro _ ⟨m, hm, rfl⟩
    exact hCHP (hMCH hm)
  let πP : ↥P →* ↥(centralizer ({tt} : Set (↥H ⧸ C))) :=
    { toFun := fun p => ⟨π p, p.2⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun a b => Subtype.ext (map_mul π _ _) }
  have hπPs : Function.Surjective πP := by
    rintro ⟨x, hx⟩
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective C x
    exact ⟨⟨h, hx⟩, rfl⟩
  have hMts : (Mt.subgroupOf (centralizer ({tt} : Set (↥H ⧸ C)))).IsSubnormal := by
    have h1 := hMPs.map hπPs
    have h2 : ((M.subgroupOf H).subgroupOf P).map πP =
        Mt.subgroupOf (centralizer ({tt} : Set (↥H ⧸ C))) := by
      ext ⟨x, hx⟩
      constructor
      · rintro ⟨p, hp, hpx⟩
        rw [mem_subgroupOf]
        refine ⟨p, hp, ?_⟩
        exact congrArg Subtype.val hpx
      · intro h
        rw [mem_subgroupOf] at h
        obtain ⟨m, hm, hmx⟩ := h
        refine ⟨⟨m, hCHP (hMCH hm)⟩, hm, ?_⟩
        exact Subtype.ext hmx
    rw [← h2]
    exact h1
  have hMtodd : Odd (Nat.card ↥(Mt.subgroupOf (centralizer ({tt} : Set (↥H ⧸ C))))) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2d
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2d
    have hxM : ((x : ↥(centralizer ({tt} : Set (↥H ⧸ C)))) : ↥H ⧸ C) ∈ Mt := x.2
    obtain ⟨m, hm, hmx⟩ := hxM
    have hm0 : orderOf m ≠ 0 := (orderOf_pos m).ne'
    obtain ⟨k, b, hb, hkb⟩ := Nat.exists_eq_two_pow_mul_odd hm0
    have hs2 : (m ^ b) ^ 2 ^ k = 1 := by
      rw [← pow_mul, mul_comm, ← hkb, pow_orderOf_eq_one]
    have hsC : π (m ^ b) = 1 := by
      rw [hπ1, mem_centralizer_iff]
      intro l hl
      have hsM : ((m ^ b : ↥H) : Q) ∈ M := pow_mem hm b
      have hsn : ((m ^ b : ↥H) : Q) ^ 2 ^ k = 1 := by
        simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hs2
      have h1 := h2 _ hsM ⟨k, hsn⟩ l hl
      exact h1.symm
    have hxx : x ^ 2 = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    have hxb : x ^ b = x := by
      obtain ⟨c, rfl⟩ := hb
      rw [pow_succ, pow_mul, hxx, one_pow, one_mul]
    have hx1 : x = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [← hxb]
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hmx, ← map_pow, hsC]
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hMtO := le_pPrimeCore_of_isSubnormal_of_odd hMts hMtodd
  intro y hy ⟨n, hyn⟩ l hl
  have hyH : y ∈ H := hMH hy
  set w : ↥(centralizer ({tt} : Set (↥H ⧸ C))) := ⟨π ⟨y, hyH⟩, hMtC ⟨⟨y, hyH⟩, hy, rfl⟩⟩ with hw
  have hwO : w ∈ pPrimeCore 2 ↥(centralizer ({tt} : Set (↥H ⧸ C))) :=
    hMtO (show (w : ↥H ⧸ C) ∈ Mt from ⟨⟨y, hyH⟩, hy, rfl⟩)
  have h1 := orderOf_dvd_natCard (⟨w, hwO⟩ : ↥(pPrimeCore 2 ↥(centralizer ({tt} : Set (↥H ⧸ C)))))
  have h2 : orderOf (⟨w, hwO⟩ : ↥(pPrimeCore 2 ↥(centralizer ({tt} : Set (↥H ⧸ C))))) ∣ 3 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hw]
    rw [← map_pow]
    have h3 : (⟨y, hyH⟩ : ↥H) ^ 3 ^ n = 1 := Subtype.ext (by simpa using hyn)
    rw [h3, map_one]
  have hcop : Nat.Coprime (3 ^ n) (Nat.card ↥(pPrimeCore 2 ↥(centralizer ({tt} : Set (↥H ⧸ C)))))
      := Nat.Coprime.pow_left _ hθH.symm
  have h4 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
  rw [orderOf_eq_one_iff] at h4
  have h5 : π ⟨y, hyH⟩ = 1 :=
    congrArg (fun v : ↥(pPrimeCore 2 ↥(centralizer ({tt} : Set (↥H ⧸ C)))) =>
      ((v : ↥(centralizer ({tt} : Set (↥H ⧸ C)))) : ↥H ⧸ C)) h4
  rw [hπ1, mem_centralizer_iff] at h5
  exact (h5 l hl).symm

end F3L225

end CFSG.ComponentClassification.HarrisLit.T1

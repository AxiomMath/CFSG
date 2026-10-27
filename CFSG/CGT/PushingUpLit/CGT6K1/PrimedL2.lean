module

public import CFSG.CGT.PushingUpLit.CGT6K1.Cases
public import CFSG.CGT.PushingUpLit.CGT6X.End3L2
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M2
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Main
public import CFSG.CGT.PushingUpLit.CGT6X.End3Irr
public import CFSG.CGT.PushingUpLit.CGT6X.End3L2Model
public import CFSG.CGT.PushingUpLit.CGT6X.End3L2Prof
public import CFSG.CGT.PushingUpLit.CGT6X.End3L2Z
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6M
  CFSG.CGT.PushingUpLit.CGT6X.End3

theorem end413_of'
    (hM2 : H1NaturalSL2) (hM3 : L2SmallModules) : End413' := by
  intro V _ _ hV G T Y cfg f hf hY hout hm
  classical
  have hperf : ⁅Y, Y⁆ = Y := cfg.adm.hperf
  have hYG : Y ≤ G ⊓ Subgroup.centralizer (T : Set (MulAut V)) := cfg.adm.hYC
  have hLG : CGT6.conjClosure Y G ≤ G := CGT6.conjClosure_le (hYG.trans inf_le_left)
  have hYL : Y ≤ CGT6.conjClosure Y G := CGT6.le_conjClosure
  set L := CGT6.conjClosure Y G with hL
  have hLperf : Group.IsPerfect ↥L := ⟨cfg.quasi.1⟩
  have hmL : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2
      (2 * f) := hm
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_model hLperf (by omega) hmL
  obtain ⟨hmod, ⟨eSL⟩⟩ := model_of_center_bot hZ hmL
  obtain ⟨t, htT, ht2, htL⟩ := hout
  have htG : t ∈ G := cfg.adm.hTG htT
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut V)) := normalizer_conjClosure htG
  have ht2' : t ^ 2 = 1 := by
    rw [← ht2]
    exact pow_orderOf_eq_one t
  let τ : MulAut ↥L := conjOn L t htN
  have hαout : τ ∉ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rintro ⟨l, hl⟩
    have hconj : ∀ x : ↥L, (l : MulAut V) * (x : MulAut V) * (l : MulAut V)⁻¹ =
        t * (x : MulAut V) * t⁻¹ := by
      intro x
      have := congrArg (fun φ : MulAut ↥L => ((φ x : ↥L) : MulAut V)) hl
      simpa [τ, conjOn_apply, MulAut.conj_apply] using this
    have hsG : (l : MulAut V)⁻¹ * t ∈ G := mul_mem (inv_mem (hLG l.2)) htG
    have hs : ∀ x ∈ L, ((l : MulAut V)⁻¹ * t) * x = x * ((l : MulAut V)⁻¹ * t) := by
      intro x hx
      have h1 := hconj ⟨x, hx⟩
      calc (l : MulAut V)⁻¹ * t * x = (l : MulAut V)⁻¹ * (t * x * t⁻¹) * t := by group
        _ = (l : MulAut V)⁻¹ * ((l : MulAut V) * x * (l : MulAut V)⁻¹) * t := by
          rw [show t * x * t⁻¹ = (l : MulAut V) * x * (l : MulAut V)⁻¹ from h1.symm]
        _ = x * ((l : MulAut V)⁻¹ * t) := by group
    have hsL : (l : MulAut V)⁻¹ * t ∈ L := centralizer_le_of_cfg cfg _ hsG hs
    apply htL
    have : t = (l : MulAut V) * ((l : MulAut V)⁻¹ * t) := by group
    rw [this]
    exact mul_mem l.2 hsL
  have hτne : τ ≠ 1 := fun h1 => hαout ⟨1, by rw [map_one, h1]⟩
  have hτ2 : orderOf τ = 2 := orderOf_eq_prime (conjOn_sq L t htN ht2') hτne
  let Y' : Subgroup ↥L := Y.subgroupOf L
  have hYfix : ∀ y ∈ Y', τ y = y := by
    intro y hy
    apply conjOn_fixes L t htN y
    exact Subgroup.mem_centralizer_iff.mp (hYG (show (y : MulAut V) ∈ Y from hy)).2 t htT
  have hYcard : Nat.card ↥Y' = 2 ^ f * (2 ^ (2 * f) - 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv]
    exact YSL.card_eq (by omega) hY
  obtain ⟨g, hgen', c, ⟨hcY', hcg'⟩, hcodd0, hcgt0⟩ :=
    exists_gen_cartan hf hmod τ hτ2 hαout Y' hYfix hYcard
  let g' : MulAut V := (g : MulAut V)
  have hmapY : Y'.map L.subtype = Y := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hYL
  have hmapYg : (Y'.map (MulAut.conj g).toMonoidHom).map L.subtype =
      Y.map (MulAut.conj g').toMonoidHom := by
    rw [Subgroup.map_map]
    have : L.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj g').toMonoidHom.comp L.subtype := by
      ext x
      simp [g']
    rw [this, ← Subgroup.map_map, hmapY]
  have hgenV : Y ⊔ Y.map (MulAut.conj g').toMonoidHom = L := by
    have h1 := congrArg (Subgroup.map L.subtype) hgen'
    rw [Subgroup.map_sup, hmapY, hmapYg, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1
  have hcY : (c : MulAut V) ∈ Y := hcY'
  have hcg : (c : MulAut V) ∈ Y.map (MulAut.conj g').toMonoidHom := by
    obtain ⟨y, hy, hyc⟩ := hcg'
    refine ⟨(y : MulAut V), hy, ?_⟩
    have := congrArg (fun z : ↥L => (z : MulAut V)) hyc
    simpa [g', MulAut.conj_apply] using this
  have hcodd : Odd (orderOf (c : MulAut V)) := by rwa [Subgroup.orderOf_coe]
  have hcgt : 1 < orderOf (c : MulAut V) := by rwa [Subgroup.orderOf_coe]
  have hcL : (c : MulAut V) ∈ L := c.2
  have hLirr : ∀ A : Subgroup V, GInv L A → A = ⊥ ∨ A = ⊤ := fun A hA =>
    irreducible_of_cfg hV cfg hA
  have hcommL : commV L = ⊤ := by
    rcases hLirr (commV L) (fun x hx a ha => commV_invariant hx ha) with h | h
    · exfalso
      have hc1 : (c : MulAut V) = 1 := by
        ext v
        have : (c : MulAut V) v * v⁻¹ ∈ commV L := Subgroup.subset_closure ⟨c, hcL, v, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        simpa using mul_inv_eq_one.mp this
      rw [hc1, orderOf_one] at hcgt
      omega
    · exact h
  have hcount := card_mul_commSub_le hgenV hcommL hcY hcg
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hq : (2 : ℕ) ^ (2 * f) = (2 ^ f) ^ 2 := by rw [pow_mul']
  have h4 : (2 : ℕ) ^ (2 * (2 * f)) = ((2 : ℕ) ^ f) ^ 4 := by
    rw [← pow_mul]
    congr 1
    ring
  have h4' : (2 : ℕ) ^ (4 * f) = ((2 : ℕ) ^ f) ^ 4 := by
    rw [← pow_mul]
    congr 1
    ring
  have hqpos : 0 < (2 : ℕ) ^ f := by positivity
  rcases profile hM2 hV hperf cfg.hcls2 hf hY with ⟨hX, Cc, hU, hCc, hlow, hup⟩ | ⟨hU, hup⟩
  ·
    have hr := hlow _ hcY hcodd hcgt
    have hr2 := hup _ hcY hcodd
    rw [hU] at hcount
    set q : ℕ := 2 ^ f with hqdef
    have h1 : Nat.card V * q ^ 2 ≤ Cc ^ 2 * q ^ 2 * q ^ 2 := by
      calc Nat.card V * q ^ 2 ≤ Nat.card V * Nat.card ↥(commSub (c : MulAut V)) := by
            rw [← hq]; exact Nat.mul_le_mul_left _ hr
        _ ≤ (Cc * 2 ^ (2 * f)) ^ 2 := hcount
        _ = Cc ^ 2 * q ^ 2 * q ^ 2 := by rw [hq]; ring
    have h2 : Nat.card V ≤ Cc ^ 2 * q ^ 2 := by
      have hq2 : 0 < q ^ 2 := by positivity
      exact Nat.le_of_mul_le_mul_right h1 hq2
    have hCc2 : Cc ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hCc 2
    have hVle : Nat.card V ≤ 2 ^ (2 * (2 * f)) := by
      rw [h4]
      calc Nat.card V ≤ Cc ^ 2 * q ^ 2 := h2
        _ ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ hCc2
        _ = q ^ 4 := by ring
    obtain ⟨hVeq, hΩ⟩ := m3_cases hM3 hV hf eSL hLirr hVle hcL hcodd hcgt
      hr2
    have hCc' : Cc = q := by
      apply le_antisymm hCc
      by_contra hlt
      push Not at hlt
      have h3 : Cc ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
      have h5 : q ^ 4 ≤ Cc ^ 2 * q ^ 2 := by rw [← h4', ← hVeq] ; exact h2
      have h6 : Cc ^ 2 * q ^ 2 < q ^ 2 * q ^ 2 := Nat.mul_lt_mul_of_pos_right h3 (by positivity)
      have : q ^ 2 * q ^ 2 = q ^ 4 := by ring
      omega
    have hU3 : Nat.card ↥(commV Y) = 2 ^ (3 * f) := by
      rw [hU, hCc', hq, ← pow_mul, ← pow_add]
      congr 1
      ring
    have hΩ' : IsNatSectionBy (omegaMinusAct f) L (commV L) ⊥ := by
      rw [hcommL]
      exact hΩ
    have hnorm : (L.subgroupOf G).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).2
        (CGT6.le_normalizer_conjClosure (Y := Y) (Xt := G))
    exact cfg.nolift ⟨L, hYL, hLG, hnorm.isSubnormal, Or.inr ⟨f, hf, Or.inr hΩ',
      Or.inr ⟨hX, hY, hU3⟩⟩⟩
  ·
    have hr2 := hup _ hcY hcodd
    have hr : 2 ≤ Nat.card ↥(commSub (c : MulAut V)) :=
      two_le_card_commSub (fun h1 => by rw [h1, orderOf_one] at hcgt; omega)
    rw [hU] at hcount
    have h1 : Nat.card V * 2 ≤ 2 ^ (2 * (2 * f)) := by
      calc Nat.card V * 2 ≤ Nat.card V * Nat.card ↥(commSub (c : MulAut V)) :=
            Nat.mul_le_mul_left _ hr
        _ ≤ (2 ^ (2 * f)) ^ 2 := hcount
        _ = 2 ^ (2 * (2 * f)) := by rw [← pow_mul, mul_comm]
    have hVle : Nat.card V ≤ 2 ^ (2 * (2 * f)) := by omega
    obtain ⟨hVeq, -⟩ := m3_cases hM3 hV hf eSL hLirr hVle hcL hcodd hcgt hr2
    have : 2 ^ (4 * f) = 2 ^ (2 * (2 * f)) := by congr 1; ring
    omega

theorem end413_holds' :
    End413' :=
  end413_of' h1NaturalSL2_holds l2SmallModules_holds

end CFSG.CGT.PushingUpLit.CGT6K1

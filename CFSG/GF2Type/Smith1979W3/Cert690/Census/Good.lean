module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Elt
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Conj

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

@[expose] def GoodElt (minus : Bool) (L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (e : V₀)
    (x : V₀ ≃ₗ[ZMod 2] V₀) : Prop :=
  x ∈ O₀ minus ∧ (x e = e ↔ x ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))) ∧
    (x ∈ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) → x ^ 128 = 1)

theorem b0Of_lt (minus : Bool) : b0Of minus < 64 := by
  unfold b0Of
  by_cases h : 0 < (singOf minus).size
  · rw [array_getElem!_eq_getElem h]
    have hmem : (singOf minus)[0] ∈ (singOf minus).toList := array_getElem_mem_toList h
    simp only [singOf, List.toList_toArray, List.mem_filter, List.mem_range] at hmem
    exact hmem.1
  · rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getD_getElem?]
    simp [h]

noncomputable def censusN (minus : Bool) (L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (e : V₀) :
    Subgroup (V₀ ≃ₗ[ZMod 2] V₀) :=
  O₀ minus ⊓ MulAction.stabilizer (V₀ ≃ₗ[ZMod 2] V₀) e ⊓
    Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))

theorem mem_censusN {minus : Bool} {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {e : V₀}
    {n : V₀ ≃ₗ[ZMod 2] V₀} :
    n ∈ censusN minus L e ↔
      n ∈ O₀ minus ∧ n e = e ∧ n ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
  rw [censusN, Subgroup.mem_inf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    LinearEquiv.smul_def]
  exact and_assoc

theorem normalizesIdx_iff {minus : Bool} {D : GrpData} (hD : GrpFacts minus D) {LA : Array ℕ}
    (hLA : ∀ j ∈ LA, j < D.O.size) {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (hL : ∀ x, x ∈ L ↔ InIdx D LA x) {a : ℕ} (ha : a < D.O.size) :
    normalizesIdx D LA a = true ↔
      hD.elt a ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
  have hpoint : ∀ x ∈ LA,
      (let p := Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]!
       let y := D.idx.getD p D.O.size
       y < D.O.size && D.O[y]! == p && LA.contains y) = true ↔
        hD.elt a * hD.elt x * (hD.elt a)⁻¹ ∈ L := by
    intro x hx
    have hxlt := hLA x hx
    constructor
    · intro hcheck
      change (D.idx.getD (Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]!) D.O.size <
        D.O.size && D.O[D.idx.getD (Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]!)
        D.O.size]! == Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]! &&
        LA.contains (D.idx.getD (Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]!)
          D.O.size)) = true at hcheck
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
      obtain ⟨⟨hylt, hDy⟩, hyA⟩ := hcheck
      have hcode : Code.HasCode ((hD.elt a * hD.elt x * (hD.elt a)⁻¹ :
          V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
          (Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]!) :=
        hD.hasCode_conj ha hxlt
      have hconjelt : hD.elt a * hD.elt x * (hD.elt a)⁻¹ = hD.elt (D.idx.getD
          (Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]!) D.O.size) :=
        hD.eq_elt_of_hasCode hylt (by rw [beq_iff_eq.mp hDy]; exact hcode)
      rw [hconjelt]
      exact (hL _).mpr ⟨_, Array.contains_iff_mem.mp hyA, hylt,
        hD.hasCode_elt hylt⟩
    · intro hmem
      obtain ⟨k, hkA, hklt, hkcode⟩ := hD.inIdx_iff.mp ((hL _).mp hmem)
      let p := Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]!
      have hcodek : Code.HasCode ((hD.elt a * hD.elt x * (hD.elt a)⁻¹ :
          V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) D.O[k]! := by
        rw [← hkcode]
        exact hD.hasCode_elt hklt
      have hp : p = D.O[k]! :=
        Code.HasCode.code_eq (hD.hasCode_conj ha hxlt) hcodek
          (Code.mul_lt _ _) (hD.code_lt hklt)
      have hidx : D.idx.getD p D.O.size = k := by
        rw [hp]
        exact hD.idx k hklt
      change (D.idx.getD p D.O.size < D.O.size && D.O[D.idx.getD p D.O.size]! == p &&
        LA.contains (D.idx.getD p D.O.size)) = true
      rw [hidx]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hklt, beq_iff_eq.mpr hp.symm⟩, Array.contains_iff_mem.mpr hkA⟩
  constructor
  · intro hnorm
    have hforall : ∀ x ∈ LA,
        (let p := Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]!
         let y := D.idx.getD p D.O.size
         y < D.O.size && D.O[y]! == p && LA.contains y) = true := by
      have h' := hnorm
      simp only [normalizesIdx, ha, decide_true, Bool.true_and,
        Array.all_eq_true_iff_forall_mem] at h'
      exact h'
    have hmap_le : L.map (MulAut.conj (hD.elt a)).toMonoidHom ≤ L := by
      rintro z ⟨y, hy, rfl⟩
      change hD.elt a * y * (hD.elt a)⁻¹ ∈ L
      obtain ⟨j, hjA, hjlt, hjy⟩ := hD.inIdx_iff.mp ((hL y).mp hy)
      rw [← hjy]
      exact (hpoint j hjA).mp (hforall j hjA)
    have hmap : L.map (MulAut.conj (hD.elt a)).toMonoidHom = L := by
      refine eq_of_le_of_natCard hmap_le ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj (hD.elt a)).injective]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  · intro hnorm
    have hforall : ∀ x ∈ LA,
        (let p := Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]!
         let y := D.idx.getD p D.O.size
         y < D.O.size && D.O[y]! == p && LA.contains y) = true := by
      intro x hx
      refine (hpoint x hx).mpr ?_
      exact (Subgroup.mem_normalizer_iff.mp hnorm (hD.elt x)).mp
        ((hL _).mpr ⟨x, hx, hLA x hx, hD.hasCode_elt (hLA x hx)⟩)
    rw [normalizesIdx]
    simp only [ha, decide_true, Bool.true_and]
    exact Array.all_eq_true_iff_forall_mem.mpr hforall

theorem goodArr_iff {minus : Bool} {D : GrpData} (hD : GrpFacts minus D) {LA : Array ℕ}
    (hLA : ∀ j ∈ LA, j < D.O.size) {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (hL : ∀ x, x ∈ L ↔ InIdx D LA x) {b : ℕ} (hb : b < 64) {i : ℕ} (hi : i < D.O.size) :
    (goodArr D minus LA b ())[i]! = true ↔ GoodElt minus L (Code.vec b) (hD.elt i) := by
  have hget : (goodArr D minus LA b ())[i]! = goodAt D minus b LA i := by
    rw [array_getElem!_eq_getElem_of_lt (by simpa [goodArr] using hi)]
    simp [goodArr]
  rw [hget]
  have hfixnor : ((Code.act D.O[i]! b == b) == normalizesIdx D LA i) = true ↔
      (hD.elt i (Code.vec b) = Code.vec b ↔
        hD.elt i ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))) := by
    rw [beq_iff_eq, Bool.eq_iff_iff, beq_iff_eq, ← hD.elt_vec_eq_iff hi hb,
      normalizesIdx_iff hD hLA hL hi]
  have hcen : (LA.all fun x => Code.mul D.O[i]! D.O[x]! ==
        Code.mul D.O[x]! D.O[i]!) = true ↔
      hD.elt i ∈ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
    rw [Array.all_eq_true_iff_forall_mem]
    constructor
    · intro hall
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨j, hjA, hjlt, hjy⟩ := hD.inIdx_iff.mp ((hL y).mp hy)
      have hc := hall j hjA
      rw [beq_iff_eq] at hc
      rw [← hjy]
      exact (hD.mul_comm_iff hi hjlt).mp hc |>.symm
    · intro hcen x hx
      have hxlt := hLA x hx
      exact beq_iff_eq.mpr ((hD.mul_comm_iff hi hxlt).mpr
        ((Subgroup.mem_centralizer_iff.mp hcen (hD.elt x)
          ((hL _).mpr ⟨x, hx, hxlt, hD.hasCode_elt hxlt⟩)).symm))
  have hpow : ((if LA.all (fun x => Code.mul D.O[i]! D.O[x]! ==
        Code.mul D.O[x]! D.O[i]!) then codePow D.O[i]! 128 == Code.one else true) = true) ↔
      (hD.elt i ∈ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) →
        hD.elt i ^ 128 = 1) := by
    by_cases hc : (LA.all fun x => Code.mul D.O[i]! D.O[x]! ==
        Code.mul D.O[x]! D.O[i]!) = true
    · rw [if_pos hc]
      constructor
      · intro hp _
        exact (hD.codePow_eq_one_iff hi 128).mp (beq_iff_eq.mp hp)
      · intro h
        exact beq_iff_eq.mpr ((hD.codePow_eq_one_iff hi 128).mpr (h (hcen.mp hc)))
    · rw [if_neg hc]
      constructor
      · intro _ hcent
        exact absurd (hcen.mpr hcent) hc
      · intro _
        rfl
  rw [goodAt]
  simp only [hi, decide_true, Bool.true_and]
  rw [Bool.and_eq_true, hfixnor, hpow, GoodElt]
  constructor
  · rintro ⟨hiff, hpower⟩
    exact ⟨hD.elt_mem_O₀ hi, hiff, hpower⟩
  · rintro ⟨_, hiff, hpower⟩
    exact ⟨hiff, hpower⟩

theorem elt_mem_censusN_of_contains_n0Of {minus : Bool} {D : GrpData} (hD : GrpFacts minus D)
    {LA : Array ℕ} (hLA : ∀ j ∈ LA, j < D.O.size) {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (hL : ∀ x, x ∈ L ↔ InIdx D LA x) {b : ℕ} (hb : b < 64) {i : ℕ}
    (hi : (n0Of D LA b ()).contains i = true) :
    i < D.O.size ∧ hD.elt i ∈ censusN minus L (Code.vec b) := by
  have hiList : i ∈ (n0Of D LA b ()).toList :=
    Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hi)
  rw [n0Of] at hiList
  simp only [List.toList_toArray, List.mem_filter, List.mem_range] at hiList
  obtain ⟨hilt, hpred⟩ := hiList
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpred
  obtain ⟨hact, hnor⟩ := hpred
  refine ⟨hilt, ?_⟩
  rw [mem_censusN]
  exact ⟨hD.elt_mem_O₀ hilt, (hD.elt_vec_eq_iff hilt hb).mpr hact,
    (normalizesIdx_iff hD hLA hL hilt).mp hnor⟩

theorem goodElt_of_censusCond {minus : Bool} {H L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {e : V₀}
    (hH : H ≤ O₀ minus) (hC : CensusCond minus H L e) {h : V₀ ≃ₗ[ZMod 2] V₀} (hh : h ∈ H) :
    GoodElt minus L e h := by
  obtain ⟨hLH, hfixL, hinvL, hcardL, hnorfix, h2grp⟩ := hC
  refine ⟨hH hh, (hnorfix h hh).symm, ?_⟩
  intro hcen
  have hsub : h ∈ H ⊓ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := ⟨hh, hcen⟩
  have hdvd : orderOf h ∣ Nat.card (O₀ minus) :=
    (Subgroup.orderOf_dvd_natCard _ hsub).trans
      (Subgroup.card_dvd_of_le (inf_le_left.trans hH))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2grp.exists_orderOf_eq_pow
    (⟨h, hsub⟩ : ↥(H ⊓ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))))
  have hk' : orderOf h = 2 ^ k := (Subgroup.orderOf_coe _).trans hk
  have h128 : orderOf h ∣ 128 := by
    cases minus
    · have hd : 2 ^ k ∣ 40320 := by
        rw [hk'] at hdvd
        rw [natCard_O₀] at hdvd
        simpa using hdvd
      have hcop : Nat.Coprime (2 ^ k) 315 :=
        (show Nat.Coprime 2 315 by norm_num).pow_left k
      have hd' : 2 ^ k ∣ 128 * 315 := by simpa using hd
      rw [hk']
      simpa using hcop.dvd_of_dvd_mul_right hd'
    · have hd : 2 ^ k ∣ 51840 := by
        rw [hk'] at hdvd
        rw [natCard_O₀] at hdvd
        simpa using hdvd
      have hcop : Nat.Coprime (2 ^ k) 405 :=
        (show Nat.Coprime 2 405 by norm_num).pow_left k
      have hd' : 2 ^ k ∣ 128 * 405 := by simpa using hd
      rw [hk']
      simpa using hcop.dvd_of_dvd_mul_right hd'
  exact orderOf_dvd_iff_pow_eq_one.mp h128

theorem goodElt_conj {minus : Bool} {L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {e : V₀}
    {n : V₀ ≃ₗ[ZMod 2] V₀} (hn : n ∈ censusN minus L e) {x : V₀ ≃ₗ[ZMod 2] V₀}
    (hx : GoodElt minus L e x) : GoodElt minus L e (n⁻¹ * x * n) := by
  obtain ⟨hnO, hne, hnnor⟩ := mem_censusN.mp hn
  obtain ⟨hxO, hxfix, hxpow⟩ := hx
  have hneinv : n⁻¹ e = e := by
    calc
      n⁻¹ e = n⁻¹ (n e) := by rw [hne]
      _ = (n⁻¹ * n) e := (LinearEquiv.mul_apply _ _ _).symm
      _ = e := by simp
  have hval : (n⁻¹ * x * n) e = n⁻¹ (x e) := by
    simp [LinearEquiv.mul_apply, hne]
  have hfixiff : (n⁻¹ * x * n) e = e ↔ x e = e := by
    rw [hval]
    constructor
    · intro h
      have := congrArg (fun v => n v) h
      simpa [hne] using this
    · intro h
      rw [h, hneinv]
  have hconjSub : conjSub L n = L := by
    rw [conjSub]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hnnor
  have hnormiff : x ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) ↔
      n⁻¹ * x * n ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
    rw [← mem_normalizer_conjSub_iff (L := L) (g := n) (h := x), hconjSub]
  have hceniff : x ∈ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) ↔
      n⁻¹ * x * n ∈ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
    have hc : conjSub (Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))) n =
        Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
      rw [← centralizer_conjSub, hconjSub]
    rw [← mem_conjSub (H := Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)))
      (g := n) (x := x), hc]
  refine ⟨mul_mem (mul_mem (inv_mem hnO) hxO) hnO,
    hfixiff.trans (hxfix.trans hnormiff), ?_⟩
  intro hc
  have hpx : x ^ 128 = 1 := hxpow (hceniff.mpr hc)
  have hpow : (n⁻¹ * x * n) ^ 128 = n⁻¹ * x ^ 128 * n := by
    simpa using conj_pow (a := n⁻¹) (b := x) (i := 128)
  rw [hpow, hpx]
  simp

end CFSG.GF2Type.Smith1979W3.Cert690

end

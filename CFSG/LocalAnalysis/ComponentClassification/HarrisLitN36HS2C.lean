module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporHS
public import Certificates.Certificate22619

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts CFSG.Blueprint CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native

theorem mem_of_pow_eq_one_of_coprime {H : Type*} [Group H] [Finite H] {N : Subgroup H}
    [N.Normal] {x : H} {p : ℕ} (hx : x ^ p = 1) (hcop : Nat.Coprime p N.index) : x ∈ N := by
  rw [← QuotientGroup.eq_one_iff]
  have h1 : (QuotientGroup.mk x : H ⧸ N) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  have h2 : (QuotientGroup.mk x : H ⧸ N) ^ N.index = 1 := by
    rw [Subgroup.index_eq_card]
    exact pow_card_eq_one'
  have h5 : orderOf (QuotientGroup.mk x : H ⧸ N) ∣ 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)

theorem le_card_of_big {A : Array Table} {cap N : ℕ} (h : HS2C.big A cap N = true)
    {K : Subgroup (Equiv.Perm (Fin 3850))} (hK : ∀ l < A.size, tp 3850 A[l]! ∈ K) :
    N ≤ Nat.card K := by
  have hn : (3850 : ℕ) < 2 ^ 32 := by norm_num
  simp only [HS2C.big, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hperm, htree⟩, hkeys⟩, hN⟩ := h
  rw [Array.all_eq_true] at hperm
  have hga : ∀ l < A.size, Rep 3850 A[l]! (tp 3850 A[l]!) ∧ tp 3850 A[l]! ∈ K := fun l hl =>
    ⟨rep_tp (by rw [getElem!_pos A l hl]; exact hperm l hl), hK l hl⟩
  have hE := mulTreeOK_spec hn K (gg := fun l => tp 3850 A[l]!) hga htree
  set E := (mulClosureH 3850 A cap).1
  have hErep : ∀ k < E.size, Rep 3850 E[k]! (tablePerm 3850 E[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := hE k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have hnodup := nodup_of_hkeysDistinct (forall₂_tablePerm hErep) hkeys
  have hmem : ∀ g ∈ E.toList.map (tablePerm 3850), g ∈ K := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hErep hg
    obtain ⟨c, hcK, hrep⟩ := hE k hk
    rw [tablePerm_eq hrep]
    exact hcK
  have hlen := length_le_card_of_nodup hnodup hmem
  rw [List.length_map, Array.length_toList] at hlen
  omega

theorem exists_model
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* NativeSporadic.HS) {σ : MulAut Y}
    (hσ : orderOf σ = 2) (hcard : Nat.card ↥(fixedPoints σ) = 40320)
    (L : Subgroup ↥(fixedPoints σ)) (hLn : L.Normal) :
    ∃ L₀ : Subgroup (Equiv.Perm (Fin 3850)),
      L₀ ≤ hsP ⊓ centralizer ({tp 3850 (hsCentTbl 21)} : Set (Equiv.Perm (Fin 3850))) ∧
      Nat.card ↥L₀ = Nat.card ↥L ∧
      (L₀.subgroupOf (hsP ⊓ centralizer ({tp 3850 (hsCentTbl 21)} :
        Set (Equiv.Perm (Fin 3850))))).Normal ∧
      Nat.card ↥(hsP ⊓ centralizer ({tp 3850 (hsCentTbl 21)} :
        Set (Equiv.Perm (Fin 3850)))) = 40320 ∧
      closure (tp 3850 '' {x | x ∈ ([hsCentTbl 22, hsCentTbl 23, hsCentTbl 24, hsCentTbl 25] :
        List Table).toArray}) = hsP ⊓ centralizer ({tp 3850 (hsCentTbl 21)} :
        Set (Equiv.Perm (Fin 3850))) := by
  classical
  set ψ : Y ≃* ↥hsP := e.trans hsPermEquiv with hψ
  set σ' := MulAut.congr ψ σ with hσ'
  have hA := hs_autModel
  obtain ⟨x, hxR, hxσ⟩ := hA.surj σ'
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := hs_involution_centralizers
  have hσ'2 : orderOf σ' = 2 := by rw [hσ', orderOf_congr]; exact hσ
  have hx2 : orderOf x = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · apply hA.inj (x ^ 2) (hsR.pow_mem hxR 2)
      intro p hp
      have hsq : σ' * σ' = 1 := by rw [← pow_two, ← hσ'2, pow_orderOf_eq_one]
      have h1 : (((σ' * σ') ⟨p, hp⟩ : ↥hsP) : Equiv.Perm (Fin 3850)) = p := by rw [hsq]; rfl
      rw [MulAut.mul_apply, hxσ, hxσ] at h1
      have h1' : x * (x * p * x⁻¹) * x⁻¹ = p := h1
      have h2 : x ^ 2 * p * (x ^ 2)⁻¹ = p := by
        rw [pow_two, mul_inv_rev]
        calc x * x * p * (x⁻¹ * x⁻¹) = x * (x * p * x⁻¹) * x⁻¹ := by simp only [mul_assoc]
          _ = p := h1'
      calc x ^ 2 * p = x ^ 2 * p * (x ^ 2)⁻¹ * x ^ 2 := by group
        _ = p * x ^ 2 := by rw [h2]
    · rintro rfl
      have h1 : σ' = 1 := by
        ext p
        rw [hxσ]
        simp
      rw [h1, orderOf_one] at hσ'2
      exact absurd hσ'2 (by norm_num)
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover x hxR hx2
  obtain ⟨-, -, -, hrC, hrcard, -⟩ := hrows r hr
  set C₀ := hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) with hC₀
  have hθmem : ∀ y : ↥(fixedPoints σ),
      g⁻¹ * ((ψ (y : Y) : ↥hsP) : Equiv.Perm (Fin 3850)) * g ∈ C₀ := by
    intro y
    have hy : σ (y : Y) = y := y.2
    have hfix : σ' (ψ (y : Y)) = ψ (y : Y) := by
      rw [hσ', MulAut.congr_apply]
      simp [hy]
    have hcomm : x * ((ψ (y : Y) : ↥hsP) : Equiv.Perm (Fin 3850)) * x⁻¹ =
        ((ψ (y : Y) : ↥hsP) : Equiv.Perm (Fin 3850)) := by
      rw [← hxσ, hfix]
    refine ⟨hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) (ψ (y : Y)).2) hg,
      mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hxg] at hcomm
    calc g⁻¹ * ((ψ (y : Y) : ↥hsP) : Equiv.Perm (Fin 3850)) * g * tp 3850 r.rep
        = g⁻¹ * ((g * tp 3850 r.rep * g⁻¹) * ((ψ (y : Y) : ↥hsP) : Equiv.Perm (Fin 3850)) *
          (g * tp 3850 r.rep * g⁻¹)⁻¹) * g * tp 3850 r.rep := by rw [hcomm]
      _ = tp 3850 r.rep * (g⁻¹ * ((ψ (y : Y) : ↥hsP) : Equiv.Perm (Fin 3850)) * g) := by group
  let θ : ↥(fixedPoints σ) →* Equiv.Perm (Fin 3850) :=
    { toFun := fun y => g⁻¹ * ((ψ (y : Y) : ↥hsP) : Equiv.Perm (Fin 3850)) * g
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul, map_mul, Subgroup.coe_mul]
        group }
  have hθinj : Function.Injective θ := by
    intro a b hab
    have h1 : ((ψ (a : Y) : ↥hsP) : Equiv.Perm (Fin 3850)) =
        ((ψ (b : Y) : ↥hsP) : Equiv.Perm (Fin 3850)) := by
      have := congrArg (fun z => g * z * g⁻¹) hab
      simpa [θ, mul_assoc] using this
    exact Subtype.ext (ψ.injective (Subtype.ext h1))
  have hθle : θ.range ≤ C₀ := by
    rintro _ ⟨y, rfl⟩
    exact hθmem y
  have hθcard : Nat.card ↥θ.range = 40320 := by
    rw [← hcard]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).symm.toEquiv
  have hC₀card : Nat.card ↥C₀ = r.centOrder := hrcard
  have hge : 40320 ≤ r.centOrder := by
    rw [← hC₀card, ← hθcard]
    exact Subgroup.card_le_of_le hθle
  have hrow : r.rep = hsCentTbl 21 ∧
      r.centGens = [hsCentTbl 22, hsCentTbl 23, hsCentTbl 24, hsCentTbl 25] ∧
      r.centOrder = 40320 := by
    simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact absurd hge (by decide)
    · exact absurd hge (by decide)
    · refine ⟨?_, ?_, ?_⟩ <;> dsimp only
    · exact absurd hge (by decide)
  have h40 : Nat.card ↥C₀ = 40320 := hC₀card.trans hrow.2.2
  have hθrange : θ.range = C₀ := Subgroup.eq_of_le_of_card_ge hθle (le_of_eq (by
    rw [hθcard, h40]))
  rw [← hrow.1, ← hrow.2.1]
  refine ⟨L.map θ, (map_le_range θ L).trans hθle, ?_, ?_, ?_, ?_⟩
  · exact Nat.card_congr (L.equivMapOfInjective θ hθinj).symm.toEquiv
  · refine ⟨fun n hn c => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨l, hl, hln⟩ := hn
    have hc : (c : Equiv.Perm (Fin 3850)) ∈ θ.range := by rw [hθrange]; exact c.2
    obtain ⟨y, hy⟩ := hc
    refine ⟨y * l * y⁻¹, hLn.conj_mem l hl y, ?_⟩
    rw [map_mul, map_mul, map_inv, hy, hln]
    rfl
  · exact h40
  · exact hrC

theorem hs2CNormalFact_holds :
    HS2CNormalFact := by
  intro Y _ _ _ ⟨e⟩ σ hσ _ hcard L hLn
  have hn : (3850 : ℕ) < 2 ^ 32 := by norm_num
  have hcheck := Certificates.certificate22619
  simp only [HS2C.hs2CCheck, Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht, h23⟩, h25⟩, hy7p⟩, hy7s⟩, hy7c⟩, hy7o⟩, hy5p⟩, hy5s⟩, hy5c⟩,
    hy5o⟩, hg7p⟩, hg7i⟩, hg5p⟩, hg5i⟩, hbig7⟩, hbig5⟩ := hcheck
  obtain ⟨L₀, hL₀C, hL₀card, hL₀n, hC₀card, hC⟩ := exists_model e hσ hcard L hLn
  set t := tp 3850 (hsCentTbl 21) with htdef
  set C₀ := hsP ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 3850))) with hC₀
  have hT : Rep 3850 HS2C.t2C t := rep_tp ht
  have hmemC : ∀ {T : Table} (hp : permOK 3850 T = true), hsSift T = true →
      commTT 3850 T HS2C.t2C = true → tp 3850 T ∈ C₀ := by
    intro T hp hs hc
    exact ⟨(hs_groupData.sift T _ (rep_tp hp)).mp hs,
      mem_centralizer_singleton_iff.mpr ((commTT_iff (rep_tp hp) hT).mp hc)⟩
  have hgen : ∀ k : ℕ, hsCentTbl k ∈ ([hsCentTbl 22, hsCentTbl 23, hsCentTbl 24, hsCentTbl 25] :
      List Table).toArray → tp 3850 (hsCentTbl k) ∈ C₀ :=
    fun k hk => hC ▸ subset_closure ⟨hsCentTbl k, hk, rfl⟩
  have h24 : tp 3850 HS2C.g7 ∈ C₀ := hgen 24 (by
    exact List.mem_toArray.mpr (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have h23' : tp 3850 (hsCentTbl 23) ∈ C₀ := hgen 23 (by
    exact List.mem_toArray.mpr (List.Mem.tail _ (List.Mem.head _)))
  have h25' : tp 3850 (hsCentTbl 25) ∈ C₀ := hgen 25 (by
    exact List.mem_toArray.mpr
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  have hy7C := hmemC hy7p hy7s hy7c
  have hy5C := hmemC hy5p hy5s hy5c
  have hg5rep : Rep 3850 HS2C.g5 (tp 3850 (hsCentTbl 25) * tp 3850 (hsCentTbl 23)) :=
    Rep.compT (rep_tp h25) (rep_tp h23)
  have hg5eq : tp 3850 HS2C.g5 = tp 3850 (hsCentTbl 25) * tp 3850 (hsCentTbl 23) :=
    rep_unique (rep_tp hg5p) hg5rep
  have hg5C : tp 3850 HS2C.g5 ∈ C₀ := hg5eq ▸ C₀.mul_mem h25' h23'
  have hconjC : ∀ {g y x : Table}, permOK 3850 g = true → invOK 3850 g (invT 3850 g) = true →
      permOK 3850 y = true → permOK 3850 x = true →
      x = compT 3850 (compT 3850 g y) (invT 3850 g) → tp 3850 g ∈ C₀ → tp 3850 y ∈ C₀ →
      tp 3850 x = tp 3850 g * tp 3850 y * (tp 3850 g)⁻¹ ∧ tp 3850 x ∈ C₀ := by
    intro g y x hgp hgi hyp hxp hx hgC hyC
    have hrep : Rep 3850 x (tp 3850 g * tp 3850 y * (tp 3850 g)⁻¹) := by
      rw [hx]
      exact Rep.compT (Rep.compT (rep_tp hgp) (rep_tp hyp)) (rep_invT (rep_tp hgp) hgi)
    have heq := rep_unique (rep_tp hxp) hrep
    exact ⟨heq, heq ▸ C₀.mul_mem (C₀.mul_mem hgC hyC) (C₀.inv_mem hgC)⟩
  have hb7 := hbig7
  have hb5 := hbig5
  simp only [HS2C.big, Bool.and_eq_true] at hb7 hb5
  have hx7p : permOK 3850 HS2C.x7 = true := by
    have := (Array.all_eq_true.mp hb7.1.1.1) 1 (by decide)
    simpa using this
  have hx5p : permOK 3850 HS2C.x5 = true := by
    have := (Array.all_eq_true.mp hb5.1.1.1) 1 (by decide)
    simpa using this
  obtain ⟨hx7eq, hx7C⟩ := hconjC hg7p hg7i hy7p hx7p rfl h24 hy7C
  obtain ⟨hx5eq, hx5C⟩ := hconjC hg5p hg5i hy5p hx5p rfl hg5C hy5C
  have hy7pow : tp 3850 HS2C.y7 ^ 7 = 1 :=
    (tblEq_idT_iff hn (Rep.powT hn (rep_tp hy7p) 7)).mp hy7o
  have hy5pow : tp 3850 HS2C.y5 ^ 5 = 1 :=
    (tblEq_idT_iff hn (Rep.powT hn (rep_tp hy5p) 5)).mp hy5o
  have hx7pow : tp 3850 HS2C.x7 ^ 7 = 1 := by
    rw [hx7eq, conj_pow, hy7pow, mul_one, mul_inv_cancel]
  have hx5pow : tp 3850 HS2C.x5 ^ 5 = 1 := by
    rw [hx5eq, conj_pow, hy5pow, mul_one, mul_inv_cancel]
  have hmemL : ∀ {z : Equiv.Perm (Fin 3850)} {p : ℕ}, z ∈ C₀ → z ^ p = 1 →
      Nat.Coprime p (L₀.subgroupOf C₀).index → z ∈ L₀ := by
    intro z p hzC hz hcop
    have : (⟨z, hzC⟩ : ↥C₀) ∈ L₀.subgroupOf C₀ :=
      mem_of_pow_eq_one_of_coprime (Subtype.ext (by simpa using hz)) hcop
    exact Subgroup.mem_subgroupOf.mp this
  have hindex : (L₀.subgroupOf C₀).index * Nat.card ↥L₀ = 40320 := by
    have h1 := Subgroup.card_mul_index (L₀.subgroupOf C₀)
    rw [hC₀card] at h1
    rw [← h1, mul_comm]
    congr 1
    exact (Nat.card_congr (subgroupOfEquivOfLe hL₀C).toEquiv).symm
  refine ⟨fun h168 => ?_, fun h360 => ?_⟩
  · rw [hL₀card, h168] at hindex
    have hidx : (L₀.subgroupOf C₀).index = 240 := by omega
    have hcop : Nat.Coprime 7 (L₀.subgroupOf C₀).index := by rw [hidx]; norm_num
    have hle := le_card_of_big hbig7 (K := L₀) (fun l hl => by
      have hl2 : l < 2 := by simpa using hl
      interval_cases l
      · simpa using hmemL hy7C hy7pow hcop
      · simpa using hmemL hx7C hx7pow hcop)
    rw [hL₀card, h168] at hle
    omega
  · rw [hL₀card, h360] at hindex
    have hidx : (L₀.subgroupOf C₀).index = 112 := by omega
    have hcop : Nat.Coprime 5 (L₀.subgroupOf C₀).index := by rw [hidx]; norm_num
    have hle := le_card_of_big hbig5 (K := L₀) (fun l hl => by
      have hl2 : l < 2 := by simpa using hl
      interval_cases l
      · simpa using hmemL hy5C hy5pow hcop
      · simpa using hmemL hx5C hx5pow hcop)
    rw [hL₀card, h360] at hle
    omega

end CFSG.ComponentClassification.HarrisLit.N36

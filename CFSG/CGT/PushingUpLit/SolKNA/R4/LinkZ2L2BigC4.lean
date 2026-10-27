module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigC3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigPi
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big18
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrHyp51

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big.C264

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.ClassicalInvolution.Asc77.T8 (XMem ne_of_mem_omegaNbr)
open CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
open CFSG.Blueprint

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem card_uSet (hr : 2 ≤ r) (hs : Z2SetR r n R S t J u R₀ T₀ P) {U : Subgroup Y}
    (hU : U ∈ USet (CoreAssembly.conjClass (tightCore R))) : Nat.card ↥U = 2 ^ (r - 1) := by
  obtain ⟨R', -, J', hJ', hR'J', -, -, hcard, -⟩ :=
    Sec6Gen.exists_data_of_mem_USet hs.large.datum.hypOmegaGen hU
  rw [card_eq_of_sylow hr (TightLargeHypR.typeRFam hs.large) hJ' hR'J'] at hcard
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rw [pow_succ] at hcard
  omega

private theorem actsTriv_one {Y : Type} [Group Y] (Λ : Subgroup Y) : ActsTriv Λ 1 := by
  intro z hz
  simpa using (oddCoreOf Λ).one_mem

theorem star_of_pi (hr : 4 ≤ r) (hs : Z2SetR r n R S t J u R₀ T₀ P) {p f : ℕ}
    (hm : Z2BigLinkModel r ↥(linkGrp R t) p f) (hCyc : Z2BigModelPiCyc r) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {y : Y} (hy : IsUniqueInvolution L y)
    (h4 : 2 < Nat.card ↥(L ⊓ (P : Subgroup Y))) : y = t ∨ y = u := by
  classical
  have hΩ := hs.large.datum.hypOmegaGen
  have ht := hs.large.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ P
  have hηG : η ∈ etaG (CoreAssembly.conjClass (tightCore R)) := ⟨P, hη, hinv⟩
  have hηS : ∀ V ∈ η, V ≤ (P : Subgroup Y) := fun V hV => (hη.1 hV).2
  have hWab := (Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hη hinv).1
  have hWP : (⨆ U ∈ η, U) ≤ (P : Subgroup Y) := iSup₂_le fun V hV => hηS V hV
  have hinvW : ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ m : Y, IsUniqueInvolution M m →
      2 < Nat.card ↥(M ⊓ (P : Subgroup Y)) → m ∈ ⨆ U ∈ η, U := by
    intro M hM m hm hc
    have hMW := Sec6Gen.l6_11Gen Y _ hΩ P η hηG hηS M hM hc
    have hU := (hη.1 hMW).1
    exact (T3.mem_of_isPGroup hm inf_le_left (Sec6Gen.isPGroup_of_mem_USet hΩ hU)
      (by rw [card_uSet (by omega : 2 ≤ r) hs hU]
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega))).2
  have hcardR : ∀ {M Q : Subgroup Y}, M ∈ CoreAssembly.conjClass (tightCore R) →
      IsSylow2In Q M → Q ≤ (P : Subgroup Y) →
        2 < Nat.card ↥(M ⊓ (P : Subgroup Y)) := by
    intro M Q hM hQ hQP
    have h2r : 2 < 2 ^ r := by
      calc 2 = 2 ^ 1 := by norm_num
        _ < 2 ^ r := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have := Subgroup.card_le_of_le (le_inf hQ.1 hQP)
    rw [card_eq_of_sylow (by omega : 2 ≤ r) (TightLargeHypR.typeRFam hs.large) hM hQ] at this
    omega
  have htW := hinvW _ hK t ht (hcardR hK hs.hR₀ hs.hR₀P)
  have huW := hinvW _ hs.hJ.1 u hs.hu (hcardR hs.hJ.1 hs.hT₀ hs.hT₀P)
  have hLW := Sec6Gen.l6_11Gen Y _ hΩ P η hηG hηS L hL h4
  have hU := (hη.1 hLW).1
  have hUcard : Nat.card ↥(L ⊓ ⨆ U ∈ η, U) = 2 ^ (r - 1) :=
    card_uSet (by omega : 2 ≤ r) hs hU
  obtain ⟨-, -, -, -, -, -, hcyc, -, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(L ⊓ ⨆ U ∈ η, U))
  have hgo : orderOf (g : Y) = 2 ^ (r - 1) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hUcard]
  have hgL : (g : Y) ∈ L := g.2.1
  have hgW : (g : Y) ∈ ⨆ U ∈ η, U := g.2.2
  have hgA : (g : Y) ∈ edgeCent (P : Subgroup Y) t u :=
    ⟨⟨hWP hgW, Subgroup.mem_centralizer_singleton_iff.mpr (hWab _ hgW _ htW)⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (hWab _ hgW _ huW)⟩
  have hg4 : (g : Y) ^ 2 ^ (r - 1) = 1 := by rw [← hgo]; exact pow_orderOf_eq_one _
  have ctu := hs.comm_t_u
  have htP : t ∈ (P : Subgroup Y) := hs.hR₀P hs.t_mem_R₀
  have huP : u ∈ (P : Subgroup Y) := hs.hT₀P hs.u_mem_T₀
  have htA : t ∈ edgeCent (P : Subgroup Y) t u :=
    ⟨⟨htP, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr ctu⟩
  have huA : u ∈ edgeCent (P : Subgroup Y) t u :=
    ⟨⟨huP, Subgroup.mem_centralizer_singleton_iff.mpr ctu.symm⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hEA : Subgroup.closure ({t, u} : Set Y) ≤ edgeCent (P : Subgroup Y) t u :=
    Subgroup.closure_le _ |>.mpr (Set.insert_subset_iff.mpr ⟨htA, Set.singleton_subset_iff.mpr huA⟩)
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have htΛ : t ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
    hs.R₀_le_linkLayerAt hs.t_mem_R₀
  have huΛ : u ∈ linkLayer R t := hs.T₀_le_linkLayer hs.u_mem_T₀
  have hΛt : ∀ y ∈ linkLayer R t, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)).symm
  have hΛu : ∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u, u * y = y * u :=
    fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)).symm
  let w : Y := (g : Y) ^ 2 ^ (r - 2)
  have hwA : w ∈ edgeCent (P : Subgroup Y) t u :=
    (edgeCent (P : Subgroup Y) t u).pow_mem hgA (2 ^ (r - 2))
  have hsub : r - 1 - 1 = r - 2 := by omega
  have hE : padicValNat 2 f + 2 ≤ r := hm.padicValNat_f_add_two_le hr
  have hKlt : padicValNat 2 f < r - 1 := by omega
  have h1t : ActsTriv (linkLayer R t) ((g : Y) ^ 2 ^ (r - 1)) := by
    rw [hg4]; exact actsTriv_one _
  have h1u : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
      ((g : Y) ^ 2 ^ (r - 1)) := by
    rw [hg4]; exact actsTriv_one _
  have hsq : w ∈ Subgroup.closure ({t, u} : Set Y) := by
    have key : ∀ e ∈ Subgroup.closure ({t, u} : Set Y),
        ActsTriv (linkLayer R t) (w * e) →
        ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (w * e) →
          w ∈ Subgroup.closure ({t, u} : Set Y) := by
      intro e he h1 h2
      have h3 := hs.eq_one_of_actsTriv
        ((edgeCent (P : Subgroup Y) t u).mul_mem hwA (hEA he)) h1 h2
      rw [eq_inv_of_mul_eq_one_left h3]
      exact Subgroup.inv_mem _ he
    by_cases hwt : ActsTriv (linkLayer R t) w
    · by_cases hwu : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) w
      · exact key 1 (Subgroup.one_mem _) (by rw [mul_one]; exact hwt)
          (by rw [mul_one]; exact hwu)
      · have h2u : ¬ ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
            ((g : Y) ^ 2 ^ (r - 1 - 1)) := by
          simpa [w, hsub] using hwu
        have hulike : ActsLike (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) w t := by
          simpa [w, hsub] using hs.pi_u_cyc hr hCyc hm hgA (K := r - 1) hKlt h1u h2u
        exact key t htE (actsTriv_mul_of_comm hΛt hwt)
          (actsTriv_mul_of_actsLike htΛ ht.sq hulike)
    · have h2t : ¬ ActsTriv (linkLayer R t) ((g : Y) ^ 2 ^ (r - 1 - 1)) := by
        simpa [w, hsub] using hwt
      have htlike : ActsLike (linkLayer R t) w u := by
        simpa [w, hsub] using hs.pi_t_cyc hr hCyc hm hgA (K := r - 1) hKlt h1t h2t
      by_cases hwu : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) w
      · exact key u huE (actsTriv_mul_of_actsLike huΛ hs.hu.sq htlike)
          (actsTriv_mul_of_comm hΛu hwu)
      · have h2u : ¬ ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
            ((g : Y) ^ 2 ^ (r - 1 - 1)) := by
          simpa [w, hsub] using hwu
        have hulike : ActsLike (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) w t := by
          simpa [w, hsub] using hs.pi_u_cyc hr hCyc hm hgA (K := r - 1) hKlt h1u h2u
        refine key (u * t) (Subgroup.mul_mem _ huE htE) ?_ ?_
        · rw [← mul_assoc]
          exact actsTriv_mul_of_comm hΛt (actsTriv_mul_of_actsLike huΛ hs.hu.sq htlike)
        · rw [← ctu, ← mul_assoc]
          exact actsTriv_mul_of_comm hΛu (actsTriv_mul_of_actsLike htΛ ht.sq hulike)
  have hgy : w = y := by
    have hw2 : w * w = 1 := by
      have he : 2 ^ (r - 2) * 2 = 2 ^ (r - 1) := by
        rw [← pow_succ]
        congr 1
        omega
      calc w * w = ((g : Y) ^ 2 ^ (r - 2)) ^ 2 := by rw [pow_two]
        _ = (g : Y) ^ (2 ^ (r - 2) * 2) := by rw [pow_mul]
        _ = (g : Y) ^ 2 ^ (r - 1) := by rw [he]
        _ = 1 := hg4
    rcases hy.unique w (L.pow_mem hgL (2 ^ (r - 2))) hw2 with h | h
    · exfalso
      have hdvd := orderOf_dvd_of_pow_eq_one h
      rw [hgo] at hdvd
      have hlt : 2 ^ (r - 2) < 2 ^ (r - 1) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      exact absurd (Nat.le_of_dvd (by positivity) hdvd) (not_le.mpr hlt)
    · exact h
  rw [hgy] at hsq
  rcases Thompson.eq_of_mem_closure_pair ht.sq hs.hu.sq ctu hsq with h | h | h | h
  · exact absurd h hy.ne_one
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    obtain ⟨c, rfl⟩ := hL
    have hc : y = c * t * c⁻¹ := hy.eq (ht.conj c)
    apply hs.tu_not_conj c⁻¹
    rw [← h, hc]
    group

theorem z2BigStar_of_models (hArith : Z2BigModelArith r) (hCyc : Z2BigModelPiCyc r) :
    Z2BigStar r n := by
  intro hr Y _ _ R S t J u R₀ T₀ P hs L hL y hy h4
  obtain ⟨p, f, hm⟩ := hs.exists_linkModel hr hArith
  exact star_of_pi hr hs hm hCyc hL hy h4

theorem z2BigC264One_of_star (hStar : Z2BigStar r n) : Z2BigC264One r n := by
  intro hr hNo h4 Y _ _ R S t J u R₀ T₀ P hs
  exact c264One_of_secInO2_star hr h4 hs (hStar hr Y R S t J u R₀ T₀ P hs)
    (secInO2_of_edge hr h4 hNo hs.large hs.hJ hs.hu)

theorem z2BigC264One_of_arith (hArith : Z2BigModelArith r) : Z2BigC264One r n :=
  z2BigC264One_of_star (z2BigStar_of_models hArith (z2BigModelPiCyc_holds r))

theorem z2BigC264One_holds : Z2BigC264One r n :=
  z2BigC264One_of_arith (z2BigModelArith_holds r)

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big.C264

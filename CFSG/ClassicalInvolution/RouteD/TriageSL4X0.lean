module

public import CFSG.ClassicalInvolution.RouteD.TriageSL4Chart
public import CFSG.ClassicalInvolution.RouteD.TriageSL4Local

public section

namespace CFSG.ClassicalInvolution.RouteD

open scoped MatrixGroups commutatorElement
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL2)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem x0_chain {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hshape : LocalShapeT p f 2 .PSL 4 (conjClass K) z) {β : Subgroup G}
    (hβ : β ∈ conjClass K) {t : G} (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {j₁ j₂ T : Subgroup G}
    (hj₁ : j₁ ∈ conjClass K) (hj₂ : j₂ ∈ conjClass K) (hT : T ∈ conjClass K)
    (hKj₁ : Commutes K j₁) (hKj₂ : Commutes K j₂) (hKT : Commutes K T)
    (hβj₁ : Commutes β j₁) (hβj₂ : Commutes β j₂) (hj₁₂ : Commutes j₁ j₂)
    (hTj₁ : Commutes T j₁) (hTj₂ : T ≠ j₂) {x₀ : G} (hx₀ : IsClassicalMember p f j₁ x₀) :
    ∃ Θ : SL(3 + 1, GaloisField p f) →* locQuot (conjClass K) x₀,
      Θ.ker ≤ Subgroup.center SL(3 + 1, GaloisField p f) ∧
      Θ.range = ⨆ k, locImg (conjClass K) x₀ (![K, β, T] k) ∧
      (∀ k : Fin 3, (blockSL2 (GaloisField p f) 3 k).range.map Θ =
        locImg (conjClass K) x₀ (![K, β, T] k)) ∧
      ∀ N ∈ centralizingMembers (conjClass K) {x₀}, N ≠ j₁ → N ≠ j₂ →
        locImg (conjClass K) x₀ N ≤ Θ.range := by
  classical
  have hΩ : InClass p f (conjClass K) := S.inClass
  have hex := S.exact
  have hsingle : ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g K := single_class K
  have hKΩ : K ∈ conjClass K := mem_conjClass_self K
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    have hf : f ≠ 0 := by
      have := S.five
      rintro rfl
      simp at this
    rw [GaloisField.card p f hf]
    exact ((Fact.out : p.Prime).odd_of_ne_two S.odd).pow
  obtain ⟨c⟩ := TCtx.nonempty_A3 S.odd S.five hΩ hex hKΩ S.cls S.p1 hshape
  obtain ⟨cx⟩ := Gaps.exists_ctx_member c hsingle hshape hj₁ hx₀
  obtain ⟨W, hW⟩ := hKβ
  have hnc : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKβne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hKx : K ∈ centralizingMembers (conjClass K) {x₀} :=
    mem_centralizingMembers_of_commutes hKΩ hx₀.mem hKj₁
  have hβx : β ∈ centralizingMembers (conjClass K) {x₀} :=
    mem_centralizingMembers_of_commutes hβ hx₀.mem hβj₁
  have hj₂x : j₂ ∈ centralizingMembers (conjClass K) {x₀} :=
    mem_centralizingMembers_of_commutes hj₂ hx₀.mem hj₁₂.symm
  have hTx : T ∈ centralizingMembers (conjClass K) {x₀} :=
    mem_centralizingMembers_of_commutes hT hx₀.mem hTj₁
  have hne : ∀ {A B : Subgroup G}, A ∈ conjClass K → Commutes A B → A ≠ B := by
    intro A B hA hAB hAeq
    subst hAeq
    exact not_commutes_self_of_mem hΩ hA hAB
  have hKj₁ne : K ≠ j₁ := hne hKΩ hKj₁
  have hKj₂ne : K ≠ j₂ := hne hKΩ hKj₂
  have hβj₁ne : β ≠ j₁ := hne hβ hβj₁
  have hTj₁ne : T ≠ j₁ := hne hT hTj₁
  have hj₂j₁ne : j₂ ≠ j₁ := (hne hj₁ hj₁₂).symm
  have hβK : β ≠ K := hKβne.symm
  have hKQ : ¬ locImg (conjClass K) x₀ K ≤ cx.d.Q₁ := fun hQ =>
    hnc (cx.commutes_T_of_ne hKx hQ hβx hβK)
  obtain ⟨R_K, hR_K, hKR⟩ := cx.exists_fund_of_ne hKx hKj₁ne hKQ
  have hβQ : ¬ locImg (conjClass K) x₀ β ≤ cx.d.Q₁ := fun hQ =>
    hnc (cx.commutes_T_of_ne hβx hQ hKx hKβne).symm
  obtain ⟨R_β, hR_β, hβR⟩ := cx.exists_fund_of_ne hβx hβj₁ne hβQ
  have hj₂Q : locImg (conjClass K) x₀ j₂ ≤ cx.d.Q₁ := by
    by_contra hQ
    obtain ⟨R₂, hR₂, hj₂R⟩ := cx.exists_fund_of_ne hj₂x hj₂j₁ne hQ
    have c₁ : Commutes R₂ R_K :=
      (cx.commutes_iff_fund hj₂x hKx hR₂ hj₂R hKR).mp hKj₂.symm
    have c₂ : Commutes R₂ R_β :=
      (cx.commutes_iff_fund hj₂x hβx hR₂ hj₂R hβR).mp hβj₂.symm
    have hne₁ : R_K ≠ R₂ := fun h =>
      hKj₂ne (cx.eq_of_locImg_eq hKx hj₂x (by rw [hKR, hj₂R, h]))
    have hne₂ : R_β ≠ R₂ := fun h =>
      (hne hβ hβj₂) (cx.eq_of_locImg_eq hβx hj₂x (by rw [hβR, hj₂R, h]))
    have := fund_sl4_eq_of_commutes S.odd hR₂ hR_K hR_β hne₁ hne₂ c₁ c₂
    exact hKβne (cx.eq_of_locImg_eq hKx hβx (by rw [hKR, hβR, this]))
  have hTQ : ¬ locImg (conjClass K) x₀ T ≤ cx.d.Q₁ := fun hQ =>
    hTj₂ (cx.eq_of_locImg_le_Q₁ hTx hj₂x hQ hj₂Q)
  obtain ⟨R_T, hR_T, hTR⟩ := cx.exists_fund_of_ne hTx hTj₁ne hTQ
  have hKTne : K ≠ T := hne hKΩ hKT
  have hTβne : T ≠ β := fun h => hnc (h ▸ hKT)
  have hKR_T : Commutes R_K R_T := (cx.commutes_iff_fund hKx hTx hR_K hKR hTR).mp hKT
  have hTβnc : ¬ Commutes T β := by
    intro hTβ
    have c₂ : Commutes R_T R_β := (cx.commutes_iff_fund hTx hβx hR_T hTR hβR).mp hTβ
    have hne₁ : R_K ≠ R_T := fun h =>
      hKTne (cx.eq_of_locImg_eq hKx hTx (by rw [hKR, hTR, h]))
    have hne₂ : R_β ≠ R_T := fun h =>
      hTβne (cx.eq_of_locImg_eq hTx hβx (by rw [hTR, hβR, h]))
    have := fund_sl4_eq_of_commutes S.odd hR_T hR_K hR_β hne₁ hne₂ hKR_T.symm c₂
    exact hKβne (cx.eq_of_locImg_eq hKx hβx (by rw [hKR, hβR, this]))
  have htx : t * x₀ * t⁻¹ = x₀ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hβj₁ t ht.mem x₀ hx₀.mem
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hj₁t : conjSub t j₁ = j₁ := conjSub_eq_of_mem_of_commutes ht.mem hβj₁
  have hj₂t : conjSub t j₂ = j₂ := conjSub_eq_of_mem_of_commutes ht.mem hβj₂
  have hTt : conjSub t T = T := by
    have hmem : conjSub t T ∈ centralizingMembers (conjClass K) {x₀} := by
      have := centralizingMembers_conj hΩ.conjInvariant t x₀
      rw [htx] at this
      rw [this]
      exact ⟨T, hTx, rfl⟩
    have hne1 : conjSub t T ≠ j₁ := fun h =>
      hTj₁ne (conjSub_injective t (h.trans hj₁t.symm))
    have hne2 : conjSub t T ≠ j₂ := fun h => hTj₂ (conjSub_injective t (h.trans hj₂t.symm))
    have hQ : ¬ locImg (conjClass K) x₀ (conjSub t T) ≤ cx.d.Q₁ := fun hQ =>
      hne2 (cx.eq_of_locImg_le_Q₁ hmem hj₂x hQ hj₂Q)
    obtain ⟨R', hR', hR'img⟩ := cx.exists_fund_of_ne hmem hne1 hQ
    have hKT' : Commutes K (conjSub t T) := by
      have := (commutes_conjSub_iff (K := K) (L := T) t).mpr hKT
      rwa [hKt] at this
    have c₁ : Commutes R_K R' := (cx.commutes_iff_fund hKx hmem hR_K hKR hR'img).mp hKT'
    have hne₁ : R' ≠ R_K := fun h =>
      (hne hKΩ hKT') (cx.eq_of_locImg_eq hKx hmem (by rw [hKR, hR'img, h]))
    have hne₂ : R_T ≠ R_K := fun h =>
      hKTne (cx.eq_of_locImg_eq hKx hTx (by rw [hKR, hTR, h]))
    have := fund_sl4_eq_of_commutes S.odd hR_K hR' hR_T hne₁ hne₂ c₁ hKR_T
    exact cx.eq_of_locImg_eq hmem hTx (by rw [hR'img, hTR, this])
  obtain ⟨zT, hzT⟩ := hΩ.classical T hT
  have hu₁ := ConnectedA2.isUniqueInvolution_locImg hex hKx
    (isUniqueInvolution_of_exact hodd (hex K hKΩ) S.cls)
  have hu₂ := ConnectedA2.isUniqueInvolution_locImg hex hβx
    (isUniqueInvolution_of_exact hodd (hex β hβ) ht)
  have hu₃ := ConnectedA2.isUniqueInvolution_locImg hex hTx
    (isUniqueInvolution_of_exact hodd (hex T hT) hzT)
  rw [hKR] at hu₁
  rw [hβR] at hu₂
  rw [hTR] at hu₃
  have htY : t ∈ locLayer (conjClass K) x₀ := le_centralizingLayer hβx ht.mem
  have hnorm : ∀ {N : Subgroup G} {R : Subgroup (modelUniv .PSL 4 p f Fact.out).K},
      conjSub t N = N → locImg (conjClass K) x₀ N = R.map cx.d.ψ →
      conjSub (locMk (conjClass K) x₀ ⟨t, htY⟩) (R.map cx.d.ψ) = R.map cx.d.ψ := by
    intro N R hN hNR
    have h := locImg_conjSub_layer (Ω := conjClass K) (x := x₀) N ⟨t, htY⟩
    rw [show ((⟨t, htY⟩ : ↥(locLayer (conjClass K) x₀)) : G) = t from rfl, hN] at h
    rw [← hNR]
    exact h.symm
  have hadm : StatedLieAdmissible .PSL 4 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr (by
      have := S.five
      rintro rfl
      simp at this), by show 2 ≤ 4; omega,
      fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  have hs := chainSign_of_lifts_norm S.odd S.five (Or.inl rfl) hadm cx.d.ψ cx.d.ker_le hR_K hR_β
    hR_T hu₁ hu₂ hu₃ (hnorm hKt hKR) (hnorm hTt hTR)
    (by rw [← hKR, ← hTR]; exact commutes_locImg_of_commutes hKT)
    (fun h => hKβne (cx.eq_of_locImg_eq hKx hβx (by rw [hKR, hβR, h])))
    (fun h => hTβne (cx.eq_of_locImg_eq hTx hβx (by rw [hTR, hβR, h])))
    (fun h => hnc ((commutes_iff_locImg hΩ cx.hP1 hKx hβx).mpr (by rw [hKR, hβR]; exact h)))
    (fun h => hTβnc ((commutes_iff_locImg hΩ cx.hP1 hTx hβx).mpr (by rw [hTR, hβR]; exact h)))
  rw [← hKR, ← hβR, ← hTR] at hs
  have hβT : ∃ W, LinearBlockStandardPair (GaloisField p f) W β T :=
    linear_of_chainSign_images S.odd S.five hΩ cx.hP1 hKx hβx hTx hs ⟨W, hW⟩
  have hψ : ∀ N ∈ centralizingMembers (conjClass K) {x₀}, N ≠ j₁ → N ≠ j₂ →
      locImg (conjClass K) x₀ N ≤ cx.d.ψ.range := by
    intro N hN h1 h2
    have hQ : ¬ locImg (conjClass K) x₀ N ≤ cx.d.Q₁ := fun hQ =>
      h2 (cx.eq_of_locImg_le_Q₁ hN hj₂x hQ hj₂Q)
    obtain ⟨R, -, hR⟩ := cx.exists_fund_of_ne hN h1 hQ
    rw [hR]
    exact Subgroup.map_le_range _ _
  obtain ⟨Θ, hker, hrangeψ, hrange, hnodes⟩ := exists_chart_of_chain
    (by have := S.five; omega) hΩ hex cx.d.ψ (L := ![K, β, T])
    (fun k => by fin_cases k <;> simp [hKx, hβx, hTx])
    (fun k => by
      fin_cases k
      · exact hψ K hKx hKj₁ne hKj₂ne
      · exact hψ β hβx hβj₁ne (hne hβ hβj₂)
      · exact hψ T hTx hTj₁ne hTj₂)
    (by simpa using hKT) (by simpa using ⟨W, hW⟩) (by simpa using hβT)
  exact ⟨Θ, hker, hrange, hnodes, fun N hN h1 h2 => by rw [hrangeψ]; exact hψ N hN h1 h2⟩

end CFSG.ClassicalInvolution.RouteD

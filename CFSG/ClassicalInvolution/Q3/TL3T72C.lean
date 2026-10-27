module

public import CFSG.ClassicalInvolution.Q3.TL3T72B
public import CFSG.ClassicalInvolution.Q3.TL3T79
public import CFSG.ClassicalInvolution.Q3.TL3T42

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CSetting

variable {K J : Subgroup G} (hS : CSetting 3 IH Ω K J)
include hS

theorem eq_of_comm_pSpan_of_five_le {n : ℕ} (hn : 5 ≤ n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    (I' : AEIdent (orbOf (TC.nbrAdj Ω) J K) n) {Ks : Subgroup G}
    (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K) (hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x)
    {M : Subgroup G} (hM : M ∈ Ω)
    (hc : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ m ∈ M, x * m = m * x) : M = K ∨ M = Ks := by
  by_cases hn8 : n = 8
  · subst hn8
    exact hS.eq_of_comm_pSpan_eight I hKs hKsK hKsπ hz hKsX hM hc
  · exact hS.toCHyp.eq_of_comm_pSpan' (by omega) I' hKs hKsK hKsπ hz hKsX hM hc

theorem eq_of_mem_omegaNbr_of_five_le {n : ℕ} (hn : 5 ≤ n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) (I' : AEIdent (orbOf (TC.nbrAdj Ω) J K) n)
    {Ks : Subgroup G} (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x)
    {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) : M ∈ orbOf (TC.nbrAdj Ω) K J ∨ M = Ks := by
  by_cases hn8 : n = 8
  · subst hn8
    exact hS.eq_of_mem_omegaNbr_eight I hKs hKsK hKsπ hz hKsX hM
  · exact hS.toCHyp.eq_of_mem_omegaNbr' (by omega) I' hKs hKsK hKsπ hz hKsX hM

theorem trans_centMembers' {n : ℕ} (hn : 5 ≤ n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) {Ks : Subgroup G}
    (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x)
    {u : G} (hu1 : u ≠ 1) (hXu : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), x * u = u * x)
    (hKu : ¬ ∀ k ∈ K, k * u = u * k) (hKsu : ¬ ∀ k ∈ Ks, k * u = u * k) :
    ∀ L ∈ centMembers Ω u, ∀ L' ∈ centMembers Ω u,
      ∃ x ∈ pSpan (centMembers Ω u), conjSub x L = L' := by
  have hC := hS.toCHyp
  have hD := hS.cex.toThmDHyp
  obtain ⟨I'⟩ := hC.nonempty_aeIdent_swap I
  have hPΩ : centMembers Ω u ⊆ Ω := fun _ h => h.1
  have hπY : orbOf (TC.nbrAdj Ω) K J ⊆ centMembers Ω u := fun M hM =>
    ⟨hC.orb_subset_omega hM, fun m hm => hXu m (le_pSpan hM hm)⟩
  have hXY : pSpan (orbOf (TC.nbrAdj Ω) K J) ≤ pSpan (centMembers Ω u) :=
    pSpan_le fun M hM => le_pSpan (hπY hM)
  have hlt := hS.card_pSpan_centMembers_lt hu1
  have hinv : ∀ L ∈ centMembers Ω u, ∀ x ∈ pSpan (centMembers Ω u),
      conjSub x L ∈ centMembers Ω u := fun L hL x hx => hS.conjSub_mem_centMembers u hL hx
  have hconjJ : ∀ L ∈ centMembers Ω u, ∃ x ∈ pSpan (centMembers Ω u), conjSub x J = L := by
    intro L hL
    by_contra hnc
    have hcomm : ∀ M ∈ orbOf (TC.nbrAdj Ω) K J, ∀ a ∈ L, ∀ b ∈ M, a * b = b * a := by
      intro M hM
      refine comm_of_not_conj_span hD hS.d1 hPΩ hlt hinv hL (hπY hM) ?_
      rintro ⟨x, hx, hxL⟩
      obtain ⟨a, ha, haM⟩ := orbOf_subset_gen hC.graphFam'.graph hC.adj hM
      apply hnc
      refine ⟨x⁻¹ * a, mul_mem (inv_mem hx) (hXY ha), ?_⟩
      rw [conjSub_mul, haM, ← hxL, conjSub_inv_conjSub]
    have hc : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ m ∈ L, x * m = m * x := by
      have hle : pSpan (orbOf (TC.nbrAdj Ω) K J) ≤ Subgroup.centralizer (L : Set G) :=
        pSpan_le fun M hM b hb => Subgroup.mem_centralizer_iff.mpr fun a ha =>
          hcomm M hM a ha b hb
      intro x hx m hm
      exact (Subgroup.mem_centralizer_iff.mp (hle hx) m hm).symm
    rcases hS.eq_of_comm_pSpan_of_five_le hn I I' hKs hKsK hKsπ hz hKsX hL.1 hc with rfl | rfl
    · exact hKu hL.2
    · exact hKsu hL.2
  intro L hL L' hL'
  obtain ⟨x, hx, rfl⟩ := hconjJ L hL
  obtain ⟨x', hx', rfl⟩ := hconjJ L' hL'
  exact ⟨x' * x⁻¹, mul_mem hx' (inv_mem hx), by rw [conjSub_mul, conjSub_inv_conjSub]⟩

theorem exists_aeIdent_centMembers' {n : ℕ} (hn : 5 ≤ n)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) {Ks : Subgroup G}
    (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x)
    {u : G} (hu1 : u ≠ 1) (hXu : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), x * u = u * x)
    (hKu : ¬ ∀ k ∈ K, k * u = u * k) (hKsu : ¬ ∀ k ∈ Ks, k * u = u * k) :
    ∃ m : ℕ, 5 ≤ m ∧ Nonempty (AEIdent (centMembers Ω u) m) := by
  have hn5 : 5 ≤ n := hn
  have hC := hS.toCHyp
  have hD := hS.cex.toThmDHyp
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hD.card L hL]; norm_num
  have hK : K ∈ Ω := hS.adj.1
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hC.oddCore_orb_eq_bot
  have hPΩ : centMembers Ω u ⊆ Ω := fun _ h => h.1
  have hπY : orbOf (TC.nbrAdj Ω) K J ⊆ centMembers Ω u := fun M hM =>
    ⟨hC.orb_subset_omega hM, fun m hm => hXu m (le_pSpan hM hm)⟩
  have hXY : pSpan (orbOf (TC.nbrAdj Ω) K J) ≤ pSpan (centMembers Ω u) :=
    pSpan_le fun M hM => le_pSpan (hπY hM)
  have hlt := hS.card_pSpan_centMembers_lt hu1
  have hinv : ∀ L ∈ centMembers Ω u, ∀ x ∈ pSpan (centMembers Ω u),
      conjSub x L ∈ centMembers Ω u := fun L hL x hx => hS.conjSub_mem_centMembers u hL hx
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have htrans := hS.trans_centMembers' hn I hKs hKsK hKsπ hz hKsX hu1 hXu hKu hKsu
  have hns : ∃ L ∈ centMembers Ω u, ∃ L' ∈ centMembers Ω u, L ≠ L' := by
    obtain ⟨δ, hδ, b, hlab⟩ := I.label J hJπ
    obtain ⟨J', hJ', hlab'⟩ := I.label_surj δ hδ (!b)
    refine ⟨J, hπY hJπ, J', hπY hJ', fun e => ?_⟩
    rw [← e, hlab] at hlab'
    cases b
    · exact AE.memBar_true_ne_false hn5 δ hδ hlab'.symm
    · exact AE.memBar_true_ne_false hn5 δ hδ hlab'
  obtain ⟨x, hx5, w, hxw⟩ := I.exists_pow_five_not_comm hn5 hk
  have h5 : ∃ x ∈ pSpan (centMembers Ω u), x ^ 5 = 1 ∧
      ∃ w ∈ pSpan (centMembers Ω u), x * w ≠ w * x :=
    ⟨x, hXY x.2, by simpa using congrArg Subtype.val hx5, w, hXY w.2,
      fun h => hxw (Subtype.ext h)⟩
  have hinvπ : ∀ L ∈ orbOf (TC.nbrAdj Ω) K J, ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J),
      conjSub x L ∈ orbOf (TC.nbrAdj Ω) K J := fun L hL x hx =>
    CSetting.conjSub_mem_orb hK (hC.pSpan_orb_le hx) hL
  obtain ⟨y, hy3, hyJ, hyc⟩ := I.exists_pow_three_norm hD.hyp hD.two hC.orb_subset_omega hinvπ
    hn5 hk hJπ
  have h3 : ∃ L ∈ centMembers Ω u, ∃ y ∈ pSpan (centMembers Ω u), y ^ 3 = 1 ∧
      conjSub y L = L ∧ ¬ ∀ l ∈ L, y * l = l * y :=
    ⟨J, hπY hJπ, y, hXY y.2, by simpa using congrArg Subtype.val hy3, hyJ, hyc⟩
  exact exists_aeIdent_span hD hS.cex.below h8 hPΩ hlt htrans hinv hns h5 h3

end CSetting

end CFSG.ClassicalInvolution.Q3.TC.Thin

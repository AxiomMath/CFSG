module

public import CFSG.ClassicalInvolution.ModelFacts.LinearAutMain
public import CFSG.ClassicalInvolution.RouteD.GapsAut
public import CFSG.ClassicalInvolution.RouteD.GapsD4AAmbient
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.ModelFacts.LinearAut
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

section Middle

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem ACtx.exists_middle_three (c : ACtx p f 3 Ω K z) (nd : Nodes c) (hMFZ : FundNoncentral p)
    (hshape : LocalShapeA p f 3 Ω z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember p f β t)
    (hnK : ¬ Commutes K β)
    (hpair : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfirst : ¬ Commutes β (nd.j 0)) (hlast : Commutes β (nd.j 2)) :
    ∃ N : Subgroup G, N ∈ centralizingMembers Ω {z} ∧ N ≠ K ∧ Commutes β N ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (nd.j 0) N) ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W N (nd.j 2)) := by
  classical
  have h2 := c.two_ne_zero
  have hΩ := c.hΩ
  have hex := c.hex
  have hconj := hΩ.conjInvariant
  obtain ⟨W, hW⟩ := hpair
  have hz2 : orderOf z = 2 := c.hz.orderOf_eq_two
  have ht2 : orderOf t = 2 := hwβ.orderOf_eq_two
  have hzt : z * t = t * z := standardPair_involutions_commute h2 hW c.hz.mem hwβ.mem hz2 ht2
  have htz : t * z * t⁻¹ = z := by rw [mul_inv_eq_iff_eq_mul]; exact hzt.symm
  have htt : t * t = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one t
    rwa [ht2] at this
  obtain ⟨D, hDcard, i₀, i₁, hne01, ht₀, hr₀, ht₁, hr₁⟩ := hshape
  obtain ⟨h, hh⟩ := hsingle β hβ
  have ht_eq : t = h * z * h⁻¹ :=
    unique_involution_of_isClassicalMember h2 (hex β hβ) hwβ (hh ▸ c.hz.conj h)
  have hP1t : LocalOddCentral Ω {t} := by
    rw [ht_eq]; exact localOddCentral_conj hconj h z c.hP1
  obtain ⟨Dt, -⟩ := exists_lieSystemData_conj hconj h z D
  have attach : ∀ N : Subgroup G, N ∈ Ω → Commutes N K →
      (Commutes N β ↔ N ≤ Subgroup.centralizer ({t} : Set G)) := by
    intro N hN hNK
    rw [ht_eq] at hwβ ⊢
    exact commutes_iff_le_centralizer hMFZ hΩ hex (by rw [← ht_eq]; exact hP1t) Dt hβ hwβ hN hNK hnK
  have hconj_t : centralizingMembers Ω {z} = conjSub t '' centralizingMembers Ω {z} := by
    have := centralizingMembers_conj hconj t z
    rwa [htz] at this
  have hmemΩz : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} := by
    intro L hL
    have : conjSub t L ∈ conjSub t '' centralizingMembers Ω {z} := ⟨L, hL, rfl⟩
    rwa [← hconj_t] at this
  set σ := locAut hconj htz with hσdef
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hconj htz htt
  set ψ := c.d.ψ with hψ
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨c.hK, le_centralizer_of_isClassicalMember c.hz⟩
  have hi₀ : ∀ i : Fin D.card, D.tag i = .PSL → D.rank i = 2 → i = i₀ := by
    intro i hti hri
    by_contra hne
    have hi : i = i₁ := by
      have h1 := i.isLt
      have h2' := i₀.isLt
      have h3 := i₁.isLt
      have h4 : i.val ≠ i₀.val := fun e => hne (Fin.ext e)
      have h5 : i₀.val ≠ i₁.val := fun e => hne01 (Fin.ext e)
      exact Fin.ext (by omega)
    rw [hi, hr₁] at hri
    omega
  have hKt : conjSub t K = K := by
    have hcK : IsClassicalMember p f (conjSub t K) z := by
      have := c.hz.conj t
      rwa [htz] at this
    have hmem : conjSub t K ∈ centralizingMembers Ω {z} :=
      ⟨hconj t K c.hK, le_centralizer_of_isClassicalMember hcK⟩
    obtain ⟨ia, hta, hra, hia⟩ := locImg_eq_range_of_involution hMFZ D hKz c.hz
    obtain ⟨ib, htb, hrb, hib⟩ := locImg_eq_range_of_involution hMFZ D hmem hcK
    have e1 := hi₀ ia hta hra
    have e2 := hi₀ ib htb hrb
    subst e1 e2
    exact locImg_injOn hΩ c.hP1 hmem hKz (hib.trans hia.symm)
  have hKt' : conjSub t⁻¹ K = K := by
    have := congrArg (conjSub t⁻¹) hKt
    rw [conjSub_inv_conjSub] at this
    exact this.symm
  have hconjne : ∀ L, conjSub t L ≠ K ↔ L ≠ K := by
    intro L
    constructor
    · intro hne heq
      apply hne
      rw [heq, hKt]
    · intro hne heq
      apply hne
      have := congrArg (conjSub t⁻¹) heq
      rwa [conjSub_inv_conjSub, hKt'] at this
  have hstab : ∀ x, σ (ψ x) ∈ ψ.range := by
    have hS : (⨆ R ∈ longRootSet (K := GaloisField p f) c.hn, R) ≤
        (ψ.range).comap (σ.toMonoidHom.comp ψ) := by
      refine iSup₂_le fun R hR y hy => ?_
      obtain ⟨L, hL, hLK, hLR⟩ :=
        exists_member_of_root c.hm c.hodd hΩ c.hK c.hz c.hP1 c.d hR
      have hyL : ψ y ∈ locImg Ω z L := by rw [hLR]; exact ⟨y, hy, rfl⟩
      have h1 : σ (ψ y) ∈ locImg Ω z (conjSub t L) := by
        rw [← locAut_locImg hconj htz L]; exact ⟨_, hyL, rfl⟩
      obtain ⟨R', -, hR'⟩ := exists_root_of_ne c.hm c.hodd hΩ hex c.hK c.hz c.hP1 c.d
        (hmemΩz L hL) ((hconjne L).mpr hLK)
      rw [hR'] at h1
      obtain ⟨y', -, hy'⟩ := h1
      exact ⟨y', hy'⟩
    intro x
    have hx : x ∈ ⨆ R ∈ longRootSet (K := GaloisField p f) c.hn, R := by
      rw [iSup_longRootSet_eq_top h2 c.hn]; exact Subgroup.mem_top x
    exact hS hx
  have himg : ∀ a (ha : a < 3), locImg Ω z (nd.j a) =
      (blockSL2 (GaloisField p f) 3 ⟨a, ha⟩).range.map ψ := fun a ha => by
    rw [nd.img a ha, blockSL2_range_eq_Lc h2 ha]
  have hfix : ∀ A : SL(2, GaloisField p f),
      σ (ψ (blockSL2 (GaloisField p f) 3 ⟨2, by omega⟩ A)) =
        ψ (blockSL2 (GaloisField p f) 3 ⟨2, by omega⟩ A) := by
    intro A
    have hle : nd.j 2 ≤ Subgroup.centralizer ({t} : Set G) := fun n hn => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hlast t hwβ.mem n hn).symm
    exact (locAut_fixed_iff hΩ c.hP1 htz (nd.mem 2 (by omega))).mp hle _
      (by rw [himg 2 (by omega)]; exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hmove : ∃ A : SL(2, GaloisField p f),
      σ (ψ (blockSL2 (GaloisField p f) 3 ⟨0, by omega⟩ A)) ≠
        ψ (blockSL2 (GaloisField p f) 3 ⟨0, by omega⟩ A) := by
    by_contra hcon
    push Not at hcon
    have hfx : ∀ a ∈ locImg Ω z (nd.j 0), σ a = a := by
      intro a ha
      rw [himg 0 (by omega)] at ha
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
      exact hcon A
    have hle := (locAut_fixed_iff hΩ c.hP1 htz (nd.mem 0 (by omega))).mpr hfx
    exact hfirst (commutes_symm
      ((attach (nd.j 0) (nd.mem 0 (by omega)).1 (commutes_symm (nd.commK 0 (by omega)))).mpr hle))
  obtain ⟨g, hg0, hg2, hgσ⟩ := partner_chart_three_amb c.hodd c.h5
    (linearAutClassification c.hp2 c.hq (by norm_num)) ψ c.d.ker_le σ hσ2 hstab hfix hmove
  set α : SL(3 + 1, GaloisField p f) ≃* SL(3 + 1, GaloisField p f) :=
    slConjugation (3 + 1) (GaloisField p f) g with hα
  have hroot : ∀ T : Pair (3 + 1), IsLongRootSL2 c.hn
      ((Lc (GaloisField p f) T).map α.toMonoidHom) (α (zElt (GaloisField p f) T)) := fun T =>
    isLongRootSL2_map_aut c.hp2 c.hq c.hn α (isLongRootSL2_Lc h2 c.hn T)
  have hα0 : (Lc (GaloisField p f) (nodePair 3 0 (by omega))).map α.toMonoidHom =
      Lc (GaloisField p f) (nodePair 3 0 (by omega)) := by
    have := hg0
    rwa [blockSL2_range_eq_Lc h2 (by omega : 0 < 3)] at this
  have hα2 : (Lc (GaloisField p f) (nodePair 3 2 (by omega))).map α.toMonoidHom =
      Lc (GaloisField p f) (nodePair 3 2 (by omega)) := by
    rw [← blockSL2_range_eq_Lc h2 (by omega : 2 < 3), ← MonoidHom.range_comp]
    congr 1
    exact MonoidHom.ext fun A => hg2 A
  have hR1 : (Lc (GaloisField p f) (nodePair 3 1 (by omega))).map α.toMonoidHom ∈
      longRootSet (K := GaloisField p f) c.hn := ⟨_, hroot _⟩
  obtain ⟨N, hN, hNK, hNR⟩ := exists_member_of_root c.hm c.hodd hΩ c.hK c.hz c.hP1 c.d hR1
  have hfixN : ∀ a ∈ locImg Ω z N, σ a = a := by
    intro a ha
    rw [hNR] at ha
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := ha
    have hx' : x ∈ (blockSL2 (GaloisField p f) 3 ⟨1, by omega⟩).range := by
      rw [blockSL2_range_eq_Lc h2 (by omega : 1 < 3)]; exact hx
    obtain ⟨A, rfl⟩ := hx'
    have hd : partnerEnt 3 (1 : (GaloisField p f)ˣ) (⟨1, by omega⟩ : Fin 3).castSucc =
        partnerEnt 3 (1 : (GaloisField p f)ˣ) (⟨1, by omega⟩ : Fin 3).succ := by
      simp [partnerEnt]
    have hfixed1 := slConjugation_diagGL_blockSL2 (partnerEnt 3 (1 : (GaloisField p f)ˣ))
      ⟨1, by omega⟩ hd A
    have := hgσ (blockSL2 (GaloisField p f) 3 ⟨1, by omega⟩ A)
    unfold partnerDiag at this
    rw [hfixed1] at this
    exact this
  have hNK' : Commutes N K :=
    (commutes_K_of_ne c.hm c.hodd hΩ hex c.hK c.hz c.hP1 c.d hN hNK).symm
  have hle := (locAut_fixed_iff hΩ c.hP1 htz hN).mpr hfixN
  have hcβ : Commutes β N := commutes_symm ((attach N hN.1 hNK').mpr hle)
  have hcomm : ∀ T T' : Pair (3 + 1), Commute (α (zElt (GaloisField p f) T))
      (α (zElt (GaloisField p f) T')) := fun T T' => by
    show α _ * α _ = α _ * α _
    rw [← map_mul, ← map_mul, signGroup_comm (zElt_mem_signGroup T) (zElt_mem_signGroup T')]
  have hne : ∀ a b : ℕ, (ha : a < 3) → (hb : b < 3) → a ≠ b →
      α (zElt (GaloisField p f) (nodePair 3 a ha)) ≠
        α (zElt (GaloisField p f) (nodePair 3 b hb)) := by
    intro a b ha hb hab h
    have := (nodePair_eq_iff ha hb).mp (zElt_injective h2 (α.injective h))
    exact hab this
  have hnc : ∀ a : ℕ, (ha : a + 2 < 3 + 1) →
      ¬ Commutes ((Lc (GaloisField p f) (nodePair 3 a (by omega))).map α.toMonoidHom)
        ((Lc (GaloisField p f) (nodePair 3 (a + 1) (by omega))).map α.toMonoidHom) := by
    intro a ha hc'
    exact not_commutes_Lc_overlap h2 c.hn3 (i := ⟨a, by omega⟩) (j := ⟨a + 1, by omega⟩)
      (k := ⟨a + 2, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]) ((commutes_map_iff α.toMonoidHom α.injective).mp hc')
  obtain ⟨W₁, hW₁⟩ := c.stdpair_of_root (nd.mem 0 (by omega)) hN (hroot (nodePair 3 0 (by omega)))
    (hroot (nodePair 3 1 (by omega))) (by rw [hα0, nd.img 0 (by omega)]) hNR (hcomm _ _)
    (hne 0 1 (by omega) (by omega) (by omega)) (hnc 0 (by omega))
  obtain ⟨W₂, hW₂⟩ := c.stdpair_of_root hN (nd.mem 2 (by omega)) (hroot (nodePair 3 1 (by omega)))
    (hroot (nodePair 3 2 (by omega))) hNR (by rw [hα2, nd.img 2 (by omega)]) (hcomm _ _)
    (hne 1 2 (by omega) (by omega) (by omega)) (hnc 1 (by omega))
  exact ⟨N, hN, hNK, hcβ, ⟨W₁, hW₁⟩, ⟨W₂, hW₂⟩⟩

end Middle

end CFSG.ClassicalInvolution.RouteD

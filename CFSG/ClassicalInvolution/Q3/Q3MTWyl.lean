module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuTab
public import CFSG.ClassicalInvolution.Asc77.AscMuTabNonab

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6.Mu
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem mem_omegaNbr_of_commutes
  le_centralizer_of_commute commute_conjSub exists_sylow2In)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

section Frame

variable (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) (rep : ↥(muGroup Ω W) → Rep Ω W)
  (hrep : ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)))

include hP hW hrep

theorem rep_K_ne {x y : ↥(muGroup Ω W)} (hx : x ∈ muDelta Ω W) (hy : y ∈ muDelta Ω W)
    (hne : x ≠ y) : (rep x).K ≠ (rep y).K := by
  intro h
  apply hne
  have := ctx_img_eq_of_K_eq (Q3CL.T8.ctxOf hP hW) (rep x) (rep y) h
  rw [hrep x hx, hrep y hy] at this
  exact Subtype.ext this

theorem rep_omega {x y : ↥(muGroup Ω W)} (hx : x ∈ muDelta Ω W) (hy : y ∈ muDelta Ω W)
    (hne : x ≠ y) (hcomm : x * y = y * x) : (rep y).K ∈ omegaNbr Ω (rep x).K := by
  refine ctx_omega_of_comm (Q3CL.T8.ctxOf hP hW) (rep x) (rep y)
    (rep_K_ne hP hW rep hrep hx hy hne) ?_
  rw [hrep x hx, hrep y hy]
  exact congrArg Subtype.val hcomm

theorem not_mem_closure {x : ↥(muGroup Ω W)} (hx : x ∈ muDelta Ω W)
    {S : Set ↥(muGroup Ω W)} (hS : ∀ s ∈ S, s ∈ muDelta Ω W ∧ x ≠ s ∧ x * s = s * x) :
    x ∉ Subgroup.closure S := by
  intro hxS
  set L : Set G := {g | ∃ s ∈ S, g = (rep s).r} with hL
  have hLN : L ⊆ Subgroup.normalizer (W : Set G) := by
    rintro _ ⟨s, -, rfl⟩
    exact (rep s).r_mem_normalizer
  have hq' : (x : NQuot (W ⊔ OCW W)) ∈ Subgroup.closure (piG W '' L) := by
    have h1 := Subgroup.mem_map_of_mem (muGroup Ω W).subtype hxS
    rw [MonoidHom.map_closure] at h1
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨(rep s).r, ⟨s, hs, rfl⟩, hrep s (hS s hs).1⟩
  obtain ⟨g, hg, hgx⟩ := exists_mem_closure_of_mem_closure_piG hLN hq'
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := ((Subgroup.closure_le _).mpr hLN) hg
  obtain ⟨hRW, -, hcyc, h4, -⟩ :=
    Q3CL.Thompson.inf_W_of_mem_D hP.hyp hW (rep x).hR (rep x).hK (rep x).hRK
  obtain ⟨v, hvU, hv2⟩ := exists_sq_ne_one hcyc (by omega)
  have hvKW : v ∈ (rep x).K ⊓ W := by rw [← hRW]; exact hvU
  have hgv : g * v * g⁻¹ = v := by
    have hcl : Subgroup.closure L ≤ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨hsΔ, hxs, hcomm⟩ := hS s hs
      have hnbr := rep_omega hP hW rep hrep hsΔ hx hxs.symm hcomm.symm
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact Q3CL.Thompson.centralizes_inf_W_of_mem_omegaNbr Sec6Gen.l6_2Gen hP.hyp hW
        (rep s).hK (rep x).hK hnbr.2.1.symm (rep s).hR (rep x).hR (rep s).hRK (rep x).hRK hnbr
        (rep s).hr hvKW
    have := Subgroup.mem_centralizer_singleton_iff.mp (hcl hg)
    rw [this]
    group
  have h1 : (rep x).r * v * (rep x).r⁻¹ = v⁻¹ :=
    Q3CL.Thompson.conj_eq_inv_of_mem_inf_W hP.hyp hW (rep x).hK (rep x).hR (rep x).hRK
      (rep x).hr (rep x).hrW hvKW
  have h2 : (rep x).r * v * (rep x).r⁻¹ = g * v * g⁻¹ := by
    refine Q3CL.Thompson.conj_eq_of_piG_eq hP.hyp hW hgN (rep x).r_mem_normalizer ?_ hvKW.2
    rw [hgx]
    exact (hrep x hx).symm
  rw [h1, hgv] at h2
  apply hv2
  calc v * v = v⁻¹ * v := congrArg (· * v) h2.symm
    _ = 1 := inv_mul_cancel v

theorem two_pow_card_le_closure (S : Finset ↥(muGroup Ω W))
    (hS : ∀ x ∈ S, x ∈ muDelta Ω W)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    2 ^ S.card ≤ Nat.card ↥(Subgroup.closure (↑S : Set ↥(muGroup Ω W))) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty, pow_zero, Finset.coe_empty]
    exact Nat.card_pos
  | insert x S₀ hx ih =>
    have hS₀ : ∀ y ∈ S₀, y ∈ muDelta Ω W := fun y hy => hS y (Finset.mem_insert_of_mem hy)
    have hcomm₀ : ∀ y ∈ S₀, ∀ z ∈ S₀, y * z = z * y := fun y hy z hz =>
      hcomm y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz)
    have ih' := ih hS₀ hcomm₀
    have hxΔ : x ∈ muDelta Ω W := hS x (Finset.mem_insert_self x S₀)
    have hnot : x ∉ Subgroup.closure (↑S₀ : Set ↥(muGroup Ω W)) :=
      not_mem_closure hP hW rep hrep hxΔ fun s hs =>
        ⟨hS₀ s hs, fun e => hx (e ▸ hs), hcomm x (Finset.mem_insert_self x S₀) s
          (Finset.mem_insert_of_mem hs)⟩
    have hle : Subgroup.closure (↑S₀ : Set ↥(muGroup Ω W)) ≤
        Subgroup.closure (↑(insert x S₀) : Set ↥(muGroup Ω W)) :=
      Subgroup.closure_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
    have hne : Subgroup.closure (↑S₀ : Set ↥(muGroup Ω W)) ≠
        Subgroup.closure (↑(insert x S₀) : Set ↥(muGroup Ω W)) := fun e =>
      hnot (e ▸ Subgroup.subset_closure (by rw [Finset.coe_insert]; exact Set.mem_insert _ _))
    have := two_mul_card_le_of_le_of_ne hle hne
    rw [Finset.card_insert_of_notMem hx, pow_succ]
    omega

end Frame

section Shapes

variable (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)

include hP hW

theorem muIsoWylD4_of_cent (hnc : ¬ DbarConnected Ω W) (ρ : Rep Ω W)
    (hk : (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 4) : MuIsoWylD4 Ω W := by
  classical
  have hTT := isTT_muDelta hP hW
  have hS := isStar_muDelta (Q3CL.T8.ctxOf hP hW)
  obtain ⟨a, ha, hconn⟩ := exists_not_conn_at hP hW hnc (muTabElt ρ)
  have hd := muTabElt_mem ρ
  have hcfg : Star3T.Cfg (muDelta Ω W) (muTabElt ρ) a := ⟨hTT, hS, hd, ha, hconn⟩
  obtain ⟨rep, hrep⟩ : ∃ rep : ↥(muGroup Ω W) → Rep Ω W,
      ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)) := by
    have hex : ∀ x ∈ muDelta Ω W, ∃ ρ : Rep Ω W, ρ.img = (x : NQuot (W ⊔ OCW W)) := by
      rintro x ⟨R, hR, r, hr, hrW, hxr⟩
      obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
      exact ⟨⟨K, R, r, hK, hR, hRK, hr, hrW⟩, hxr.symm⟩
    have : Nonempty (Rep Ω W) := ⟨ρ⟩
    choose! rep hrep using hex
    exact ⟨rep, hrep⟩
  have hfin : (Star3T.cent (muDelta Ω W) (muTabElt ρ)).Finite := Set.toFinite _
  have hSc : hfin.toFinset.card = 4 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, hk]
  have hΔ : ∀ x ∈ hfin.toFinset, x ∈ muDelta Ω W := fun x hx =>
    ((Set.Finite.mem_toFinset hfin).mp hx).1
  have hcomm : ∀ x ∈ hfin.toFinset, ∀ y ∈ hfin.toFinset, x * y = y * x := fun x hx y hy =>
    hcfg.comm_cent ((Set.Finite.mem_toFinset hfin).mp hx) ((Set.Finite.mem_toFinset hfin).mp hy)
  have h16 := two_pow_card_le_closure hP hW rep hrep hfin.toFinset hΔ hcomm
  rw [hSc, Set.Finite.coe_toFinset] at h16
  exact Star3T.nonempty_mulEquiv_of_card_four hTT hS hd ha hconn hk (by simpa using h16)
    (M := coxeterD4) (fun i j => by fin_cases i <;> fin_cases j <;> rfl)
    coxeterD4.toCoxeterSystem

theorem muIsoWylD4_of_shape (hle : ∀ K ∈ Ω, (omegaNbr Ω K).ncard ≤ 3) (K : Fin 4 → Subgroup G)
    (hK : ∀ i, K i ∈ Ω) (hinj : Function.Injective K)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, a * b = b * a)
    (hcomp : ∃ M ∈ Ω, dComp Ω M ≠ dstarComp Ω M) : MuIsoWylD4 Ω W := by
  obtain ⟨M, hM, hne⟩ := hcomp
  have hnc := not_dbarConnected_of_shape hP hW hM hne
  choose R hR using fun i => exists_sylow2In (K i)
  have hRle : ∀ i j, i ≠ j → R i ≤ Subgroup.centralizer (R j : Set G) := fun i j hij =>
    le_centralizer_of_commute fun a ha b hb => hcomm i j hij a ((hR i).1 ha) b ((hR j).1 hb)
  have hN : ∀ {A B : Subgroup G}, A ≤ Subgroup.centralizer (B : Set G) →
      A ≤ Subgroup.normalizer (B : Set G) := fun h => h.trans (Subgroup.centralizer_le_normalizer _)
  have h01 : IsPGroup 2 ↥(R 0 ⊔ R 1) :=
    (hR 0).2.1.to_sup_of_normal_right' (hR 1).2.1 (hN (hRle 0 1 (by decide)))
  have h012 : IsPGroup 2 ↥(R 0 ⊔ R 1 ⊔ R 2) :=
    h01.to_sup_of_normal_right' (hR 2).2.1
      (hN (sup_le (hRle 0 2 (by decide)) (hRle 1 2 (by decide))))
  have hQ : IsPGroup 2 ↥(R 0 ⊔ R 1 ⊔ R 2 ⊔ R 3) :=
    h012.to_sup_of_normal_right' (hR 3).2.1
      (hN (sup_le (sup_le (hRle 0 3 (by decide)) (hRle 1 3 (by decide)))
        (hRle 2 3 (by decide))))
  obtain ⟨g, hg⟩ := exists_rep_of_member_sylow hP hW K R hK hR (R 0 ⊔ R 1 ⊔ R 2 ⊔ R 3) hQ (by
    intro i; fin_cases i
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right)
  choose ρ hρ using hg
  have hKne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := fun i j hij h => by
    rw [hρ i, hρ j] at h
    exact hij (hinj ((conjSub_inj g).mp h))
  have hdinj : Function.Injective fun i => muTabElt (ρ i) := fun i j h =>
    by_contra fun hij => hKne i j hij ((muTabElt_eq_iff hP hW _ _).mp h)
  have hmem : ∀ i, i ≠ 0 → (ρ i).K ∈ omegaNbr Ω (ρ 0).K := fun i hi =>
    mem_omegaNbr_of_commutes (ρ i).hK (hKne i 0 hi) (by
      rw [hρ 0, hρ i]
      exact commute_conjSub (hcomm 0 i (Ne.symm hi)) g)
  have hsub : Set.range (fun i => muTabElt (ρ i)) ⊆
      Star3T.cent (muDelta Ω W) (muTabElt (ρ 0)) := by
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = 0
    · subst hi
      exact Star3T.self_mem_cent (muTabElt_mem _)
    · exact ⟨muTabElt_mem _, ((muTab_commute_iff hP hW (ρ 0) (ρ i)
        (Ne.symm (hKne i 0 hi))).mpr (hmem i hi)).symm⟩
  refine muIsoWylD4_of_cent hP hW hnc (ρ 0) ?_
  have hge : 4 ≤ (Star3T.cent (muDelta Ω W) (muTabElt (ρ 0))).ncard := by
    have h4 : (Set.range fun i => muTabElt (ρ i)).ncard = 4 := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ hdinj, Set.ncard_univ]
      simp
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hle' := ncard_cent_le hP hW (ρ 0) (n := 3) (hle _ (ρ 0).hK)
  omega

end Shapes

end CFSG.ClassicalInvolution.Q3.Q3MT

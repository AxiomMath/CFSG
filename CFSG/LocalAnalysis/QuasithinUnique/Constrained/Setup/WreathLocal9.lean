module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLocal8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sel2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLocal6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLocal7

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

omit [Finite H] in
theorem map_quotient_iso_eq
    {Φ : (↥(oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⧸
      CFSG.pCore 2 ↥(oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)) ≃* ↥h.B}
    (hΦ : ∀ x : ↥(oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R),
      ((Φ (QuotientGroup.mk x) : ↥h.B) : MulAut ↥W) = h.rho x)
    (hcent : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊓
      Subgroup.centralizer (W : Set H) =
        blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R))
    {K : Subgroup H} {i : Fin r} (hKN : K ≤ oddOrderSubgroup (⊤ : Subgroup H))
    (hK : K.map h.rho = h.Dat i) :
    (((K ⊔ blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)).subgroupOf
      (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(oddOrderSubgroup (⊤ : Subgroup H) ⊔
          elemBaumannIn 2 R)))).map Φ.toMonoidHom = (h.Dat i).subgroupOf h.B := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    show ((Φ (QuotientGroup.mk x) : ↥h.B) : MulAut ↥W) ∈ h.Dat i
    rw [hΦ x]
    exact (h.mem_sup_Q0_iff hcent hKN hK x.2).mp (Subgroup.mem_subgroupOf.mp hx)
  · intro hy
    have hyK : (y : MulAut ↥W) ∈ K.map h.rho := hK ▸ Subgroup.mem_subgroupOf.mp hy
    obtain ⟨k, hk, hky⟩ := hyK
    have hkNS : k ∈ oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R :=
      Subgroup.mem_sup_left (hKN hk)
    refine ⟨QuotientGroup.mk' _ ⟨k, hkNS⟩, ⟨⟨k, hkNS⟩, ?_, rfl⟩, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hk)
    · apply Subtype.ext
      show ((Φ (QuotientGroup.mk ⟨k, hkNS⟩) : ↥h.B) : MulAut ↥W) = _
      rw [hΦ]
      exact hky

theorem A3_family_exists (hchar : CharTwo (⊤ : Subgroup H)) (hnoChar : NoCharNormal R ⊤) :
    ∃ K : Fin r → Subgroup H, A3FamilyConclusion h K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := oddOrderSubgroup (⊤ : Subgroup H) with hN
  set S := elemBaumannIn 2 R with hS
  set Q0 := blockQ (N ⊔ S) with hQ0
  have hNn : N.Normal := WreathHyp.oddOrderSubgroup_top_normal (H := H)
  let i0 : Fin r := ⟨0, h.r_pos⟩
  obtain ⟨P1, hSP, hPY, hPM, hmin⟩ := h.exists_P i0
  have hP : h.IsSelected i0 P1 := ⟨hSP, hPY, hPM, hmin⟩
  have C := hP.conclusion hchar hnoChar
  obtain ⟨ρ', ψ, hsurj, hequiv, hkerρ, hcard, hψker⟩ := C.rep
  have hsel := hP.a3SelHyp hchar hnoChar
  set K := oddOrderSubgroup P1 with hK
  have hψs : Function.Surjective ψ.toMonoidHom := ψ.surjective
  obtain ⟨hPL, hshort, hcard3, hLJ⟩ :=
    hsel.L_facts C.reduced ρ' hsurj ψ.toMonoidHom hψs hequiv hψker C.J_nontrivial
  have hsub3 := hsel.a3SubHyp_of_facts ⟨hPL, hshort, hcard3, hLJ⟩
  obtain ⟨r', Lf, E⟩ := exists_conjEnum R K
  have h7 := selected_natural_A3_parabolic_faithful_module hsel C.reduced ρ' hsurj ψ.toMonoidHom
    hψs hequiv hψker C.J_nontrivial E
  obtain ⟨-, hN7, -, -, -, ⟨hU7, -, -, -⟩, hCent7, -⟩ := h7
  have hKN : K ≤ N := Subgroup.closure_mono fun x hx => ⟨Subgroup.mem_top _, hx.2⟩
  have hρK : K.map h.rho = h.Dat i0 := hP.map_rho_odd
  have hcore : blockQ K = I i0 := by
    obtain ⟨hEq, hU4, -, -, -⟩ := short_order_three_is_alternating_four hshort hcard3
    exact hP.blockQ_odd_eq (by rw [hEq]; exact hU4)
  have hSt : ∀ t ∈ R, S.map (MulAut.conj t).toMonoidHom = S := fun t ht =>
    GammaExtra.map_conj_eq_self_of_mem_normalizer (le_normalizer_elemBaumannIn R ht)
  have hUW : (⨆ j, blockQ (Lf j) : Subgroup H) = W := by
    apply le_antisymm
    · refine iSup_le fun j => ?_
      obtain ⟨t, ht, hj⟩ := E.mem j
      rw [hj, h.blockQ_map_conj hcore t]
      exact h.I_le _
    · rw [← h.I_sup]
      refine iSup_le fun l => ?_
      obtain ⟨x, hx, hxl⟩ := h.transitive_R i0 l
      obtain ⟨j, hj⟩ := E.all x hx
      have h1 : blockQ (Lf j) = I l := by
        rw [← hj, h.blockQ_map_conj hcore x, ← h.map_conj_plane x i0]
        exact hxl
      rw [← h1]
      exact le_iSup (fun j => blockQ (Lf j)) j
  have hQN : ⁅Q0, N⁆ = W := hU7.symm.trans hUW
  have hcentW : (N ⊔ S) ⊓ Subgroup.centralizer (W : Set H) = Q0 := by
    rw [← hQN]
    exact hCent7
  have hsub : (((K ⊔ Q0).subgroupOf (N ⊔ S)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(N ⊔ S)))).IsSubnormal :=
    (h.isSubnormal_sup_Q0 hcentW hKN hρK).map (QuotientGroup.mk'_surjective _)
  obtain ⟨hN12, hind, hcomm, hnormal, hsubn, hperm, htrans, hblk, hU12, hX12⟩ :=
    subnormal_A3_quotient_actor_residual_family hsub3 h.S_ne_bot hsub E
  have hex : ∀ j, ∃ l, blockQ (Lf j) = I l := fun j => by
    obtain ⟨t, ht, hj⟩ := E.mem j
    exact ⟨h.piH t i0, by rw [hj, h.blockQ_map_conj hcore t]⟩
  choose e he using hex
  have he_inj : Function.Injective e := by
    intro j j' hjj'
    by_contra hne
    have hd : Disjoint (Lf j) (Lf j') := hind.pairwiseDisjoint hne
    have hQ : blockQ (Lf j) = blockQ (Lf j') := by rw [he, he, hjj']
    have hbot : blockQ (Lf j) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ blockQ (Lf j') := hQ ▸ hx
      exact Subgroup.mem_bot.mpr
        (Subgroup.disjoint_def.mp hd (blockQ_le_self _ hx) (blockQ_le_self _ hx'))
    have h4 := h.I_card (e j)
    rw [← he j, hbot, Subgroup.card_bot] at h4
    omega
  have he_surj : Function.Surjective e := by
    intro l
    obtain ⟨x, hx, hxl⟩ := h.transitive_R i0 l
    obtain ⟨j, hj⟩ := E.all x hx
    refine ⟨j, h.I_injective ?_⟩
    rw [← he j, ← hj, h.blockQ_map_conj hcore x, ← h.map_conj_plane x i0]
    exact hxl
  let eqv : Fin r' ≃ Fin r := Equiv.ofBijective e ⟨he_inj, he_surj⟩
  let Kf : Fin r → Subgroup H := fun l => Lf (eqv.symm l)
  have hKfcore : ∀ l, blockQ (Kf l) = I l := fun l => by
    have h1 := he (eqv.symm l)
    have h2 : e (eqv.symm l) = l := eqv.apply_symm_apply l
    rw [h2] at h1
    exact h1
  have hN7' : N = ⨆ j, Lf j := hN7
  have hLfN : ∀ j, Lf j ≤ N := fun j => by
    rw [hN7']
    exact le_iSup Lf j
  have hconj : ∀ l, ∃ t ∈ R, Kf l = K.map (MulAut.conj t).toMonoidHom ∧ h.piH t i0 = l := by
    intro l
    obtain ⟨t, ht, hj⟩ := E.mem (eqv.symm l)
    refine ⟨t, ht, hj, ?_⟩
    have h1 : blockQ (K.map (MulAut.conj t).toMonoidHom) = I (h.piH t i0) :=
      h.blockQ_map_conj hcore t
    rw [← hj] at h1
    exact h.I_injective (h1.symm.trans (hKfcore l))
  have hρKf : ∀ l, (Kf l).map h.rho = h.Dat l := by
    intro l
    obtain ⟨t, ht, hj, hpi⟩ := hconj l
    rw [hj, h.map_rho_conj, hρK, h.map_conj_rho_Dat, hpi]
  have hKfN : ∀ l, Kf l ≤ N := fun l => hLfN _
  have hNSn : ((N ⊔ S)).Normal := h.NS_normal
  refine ⟨Kf, ?_⟩
  exact
    { cent_V := by rw [← h.centralizer_W_eq_V]; exact hcentW
      cent_W := hcentW
      quotient_iso := by
        obtain ⟨Φ, hΦ⟩ := h.exists_quotient_iso hcentW
        exact ⟨Φ, hΦ, fun l => map_quotient_iso_eq h hΦ hcentW (hKfN l) (hρKf l)⟩
      card_D := fun l => h.card_Dat l
      K_le_N := hKfN
      N_eq := hN7'.trans (Equiv.iSup_comp (g := fun j => Lf j) eqv.symm).symm
      indep := hind.comp eqv.symm.injective
      commute := fun i j hij => hcomm _ _ (fun hh => hij (eqv.symm.injective hh))
      alt4 := fun l => (hblk (eqv.symm l)).1
      core := hKfcore
      rho_K := hρKf
      normal_QN := fun l => hnormal (eqv.symm l)
      QN_normal := by
        refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp fun g _ => ?_)
        exact mem_normalizer_sup'
          (C1.mem_normalizer_blockQ (WreathHyp.normal_le_normalizer' hNSn ⊤ (Subgroup.mem_top g)))
          (WreathHyp.normal_le_normalizer' hNn ⊤ (Subgroup.mem_top g))
      chi0 := fun l => (hblk (eqv.symm l)).2.1
      permuted := fun t ht l => by
        obtain ⟨j, hj⟩ := hperm t ht (eqv.symm l)
        exact ⟨eqv j, by simpa [Kf] using hj⟩
      transitive := fun l l' => by
        obtain ⟨t, ht, hj⟩ := htrans (eqv.symm l) (eqv.symm l')
        exact ⟨t, ht, by simpa [Kf] using hj⟩
      perfect_S := fun l => (hblk (eqv.symm l)).2.2
      perfect_J := fun l => by
        rw [← thompsonJ_baumann_eq R]
        exact (hblk (eqv.symm l)).2.2
      subnormal := fun l =>
        (h.isSubnormal_sup_Q0 hcentW (hKfN l) (hρKf l)).map (QuotientGroup.mk'_surjective _)
      S_sylow := hX12.2
      H_eq := h.odd_sup_R
      NS_normal := hNSn
      W_eq := hQN
      W_prod := by
        simp_rw [hKfcore]
        exact h.I_sup.symm
      W_le_center := hQN ▸ hU12.2.2.2.2.1
      center_le_S := hU12.2.2.2.2.2
      S_le_R := elemBaumannIn_le 2 R
      local_i := fun l => by
        obtain ⟨t, ht, hj, hpi⟩ := hconj l
        have hsel' : h.IsSelected l (P1.map (MulAut.conj t).toMonoidHom) := hpi ▸ hP.conj ht
        have hP1 : P1.map (MulAut.conj t).toMonoidHom = Kf l ⊔ S := by
          rw [hPL, Subgroup.map_sup, ← hj, hSt t ht]
        rw [← hP1]
        exact hsel'.conclusion hchar hnoChar }

end Finite

end CFSG.QuasithinUnique.Setup.Wreath

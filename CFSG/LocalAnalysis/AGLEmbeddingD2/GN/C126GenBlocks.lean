module

public import CFSG.Quasithin.Background.E2SolvBaumann

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B2F CFSG.Quasithin.E2

variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} {hV : IsElemAbelian 2 V}
  {H T M : Subgroup G} {𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))}

@[expose] def fixPt {W : Type*} [CommGroup W] (U : Subgroup W) : Subgroup (MulAut W) where
  carrier := {φ | ∀ u ∈ U, φ u = u}
  one_mem' := fun u _ => rfl
  mul_mem' := fun {a b} ha hb u hu => by rw [MulAut.mul_apply, hb u hu, ha u hu]
  inv_mem' := fun {a} ha u hu => by
    rw [MulAut.inv_apply]
    exact a.symm_apply_eq.2 (ha u hu).symm

theorem fixV_twoResidual_inf_gen (B : Blocks hV H 𝓗 I) :
    fixV (autI hV (twoResidual H)) ⊓ ⨆ L ∈ I, commSub (⊤ : Subgroup (IntMod V hV)) L = ⊥ := by
  classical
  have key : ∀ J : Finset (Subgroup (MulAut (IntMod V hV))), J ⊆ I → ∀ w : IntMod V hV,
      w ∈ fixV (autI hV (twoResidual H)) →
      w ∈ ⨆ L ∈ J, commSub (⊤ : Subgroup (IntMod V hV)) L → w = 1 := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro _ w _ hw
      simpa using hw
    | insert L₀ J hL₀J ih =>
      intro hJI w hwK hw
      have hL₀I : L₀ ∈ I := hJI (Finset.mem_insert_self _ _)
      have hJI' : J ⊆ I := fun x hx => hJI (Finset.mem_insert_of_mem hx)
      rw [Finset.iSup_insert] at hw
      obtain ⟨u, hu, w', hw', rfl⟩ := Subgroup.mem_sup.1 hw
      obtain ⟨f, hfL, hfK, hf3⟩ := B.exists_orderOf_eq_three hL₀I
      have hle : (⨆ L ∈ J, commSub (⊤ : Subgroup (IntMod V hV)) L) ≤
          fixV (Subgroup.zpowers f) := by
        refine iSup₂_le fun L hL v hv x hx => ?_
        exact B.hb.triv L₀ (B.sub hL₀I) L (B.sub (hJI' hL)) (fun h => hL₀J (h ▸ hL)) x
          (Subgroup.zpowers_le.2 hfL hx) v hv
      have hfw' : f w' = w' := hle hw' f (Subgroup.mem_zpowers f)
      have hfu : f u = u := by
        have := hwK f hfK
        rw [map_mul, hfw'] at this
        exact mul_right_cancel this
      have hu1 : u = 1 := B.eq_one_of_orderOf_eq_three hL₀I hfL hf3 hu hfu
      rw [hu1, one_mul] at hwK ⊢
      exact ih hJI' w' hwK hw'
  rw [eq_bot_iff]
  rintro w ⟨hwK, hwL⟩
  exact (Subgroup.mem_bot).2 (key I le_rfl w hwK hwL)

theorem fixV_twoResidual_gen (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    fixV (autI hV (twoResidual H)) = fixV (autI hV (thompsonJ H)) := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hKJ : autI hV (twoResidual H) ≤ autI hV (thompsonJ H) :=
    autI_mono hV (twoResidual_le_thompsonJ h hred hJ)
  refine le_antisymm (fun v hv => ?_) (B1.fixV_le_fixV hKJ)
  have hdec := B.hb.decomp hW I B.sub
  rw [← B.eq] at hdec
  have hv' : v ∈ fixV (autI hV (thompsonJ H)) ⊔ ⨆ L ∈ I, commSub ⊤ L := by
    rw [hdec.1]
    exact Subgroup.mem_top v
  obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup.mp hv'
  have hcK : c ∈ fixV (autI hV (twoResidual H)) := B1.fixV_le_fixV hKJ hc
  have hwK : w ∈ fixV (autI hV (twoResidual H)) := by
    have := (fixV (autI hV (twoResidual H))).mul_mem
      ((fixV (autI hV (twoResidual H))).inv_mem hcK) hv
    simpa using this
  have hw1 : w = 1 := by
    have hmem : w ∈ fixV (autI hV (twoResidual H)) ⊓ ⨆ L ∈ I, commSub ⊤ L := ⟨hwK, hw⟩
    rw [fixV_twoResidual_inf_gen B, Subgroup.mem_bot] at hmem
    exact hmem
  rw [hw1, mul_one]
  exact hc

theorem rk_biSup_commSub (B : Blocks hV H 𝓗 I)
    (A : Subgroup (MulAut (IntMod V hV)) → Subgroup (IntMod V hV))
    (hA : ∀ L ∈ I, A L ≤ commSub (⊤ : Subgroup (IntMod V hV)) L) :
    ∀ J : Finset (Subgroup (MulAut (IntMod V hV))), J ⊆ I →
      rk ↥(⨆ L ∈ J, A L) = ∑ L ∈ J, rk ↥(A L) := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  intro J
  induction J using Finset.induction_on with
  | empty =>
    intro _
    have e : (⨆ L ∈ (∅ : Finset (Subgroup (MulAut (IntMod V hV)))), A L) = ⊥ := by simp
    rw [e, rk_bot]
    simp
  | insert L₀ J hL₀J ih =>
    intro hJI
    have hL₀I : L₀ ∈ I := hJI (Finset.mem_insert_self _ _)
    have hJI' : J ⊆ I := fun x hx => hJI (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert, Finset.sum_insert hL₀J]
    have h := rk_sup_add_rk_inf (A L₀) (⨆ L ∈ J, A L)
    have hinf : A L₀ ⊓ ⨆ L ∈ J, A L = ⊥ := by
      refine le_bot_iff.1 ?_
      calc A L₀ ⊓ ⨆ L ∈ J, A L
          ≤ commSub (⊤ : Subgroup (IntMod V hV)) L₀ ⊓
            ⨆ L ∈ 𝓗, ⨆ (_ : L ≠ L₀), commSub (⊤ : Subgroup (IntMod V hV)) L := by
            refine inf_le_inf (hA L₀ hL₀I) (iSup₂_le fun L hL => ?_)
            have hne : L ≠ L₀ := fun he => hL₀J (he ▸ hL)
            exact (hA L (hJI' hL)).trans (le_iSup₂_of_le (f := fun (K : Subgroup (MulAut
              (IntMod V hV))) (_ : K ∈ 𝓗) => ⨆ (_ : K ≠ L₀),
                commSub (⊤ : Subgroup (IntMod V hV)) K) L (B.sub (hJI' hL))
              (le_iSup (fun _ : L ≠ L₀ => commSub (⊤ : Subgroup (IntMod V hV)) L) hne))
        _ = ⊥ := B.hb.commSub_inf_biSup_ne_eq_bot hW (B.sub hL₀I)
    rw [hinf, rk_bot] at h
    have ih' := ih hJI'
    omega

theorem two_mul_rkIdx_le_gen (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    2 * rkIdx (fixV (autI hV (thompsonJ T))) ≤ rkIdx (fixV (autI hV (twoResidual H))) := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hT := h.isSylow
  set F := fixV (autI hV (twoResidual H)) with hF
  set C := fixV (autI hV (thompsonJ T)) with hC
  obtain ⟨c, hc⟩ := B.exists_fix_thompsonJ hT hsolv hred hJ
  have hdec := B.hb.decomp hW I B.sub
  rw [← B.eq, ← fixV_twoResidual_gen B h hred hJ] at hdec
  have hrk4 : ∀ L ∈ I, rk ↥(commSub (⊤ : Subgroup (IntMod V hV)) L) = 2 := fun L hL => by
    unfold rk
    rw [B.hb.card_comm L (B.sub hL), show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have hrkc : ∀ L ∈ I, rk ↥(Subgroup.zpowers (c L)) = 1 := fun L hL => by
    unfold rk
    rw [Nat.card_zpowers, orderOf_eq_prime (hW _) (hc L hL).2.1]
    simp
  have hFC : F ≤ C := by
    rw [hF, fixV_twoResidual_gen B h hred hJ]
    exact B1.fixV_le_fixV (autI_mono hV (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT))
  have h1 := rk_add_rkIdx F
  have h2 := rk_add_rkIdx C
  set W := ⨆ L ∈ I, commSub (⊤ : Subgroup (IntMod V hV)) L with hWdef
  set Z := ⨆ L ∈ I, Subgroup.zpowers (c L) with hZdef
  have hrW : rk ↥W = 2 * I.card := by
    rw [hWdef, rk_biSup_commSub B (fun L => commSub (⊤ : Subgroup (IntMod V hV)) L)
      (fun L _ => le_rfl) I le_rfl, Finset.sum_congr rfl hrk4]
    simp [mul_comm]
  have hrZ : rk ↥Z = I.card := by
    rw [hZdef, rk_biSup_commSub B (fun L => Subgroup.zpowers (c L))
      (fun L hL => Subgroup.zpowers_le.2 (hc L hL).1) I le_rfl, Finset.sum_congr rfl hrkc]
    simp
  have hZW : Z ≤ W := iSup₂_le fun L hL => (Subgroup.zpowers_le.2 (hc L hL).1).trans
    (le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV))) (_ : K ∈ I) =>
      commSub (⊤ : Subgroup (IntMod V hV)) K) L hL le_rfl)
  have e1 := rk_sup_add_rk_inf F W
  rw [hdec.1, hdec.2, rk_top, rk_bot] at e1
  have hinfZ : F ⊓ Z = ⊥ := le_bot_iff.1 (hdec.2 ▸ inf_le_inf_left F hZW)
  have e2 := rk_sup_add_rk_inf F Z
  rw [hinfZ, rk_bot] at e2
  have e3 : rk ↥(F ⊔ Z) ≤ rk ↥C :=
    rk_mono (sup_le hFC (iSup₂_le fun L hL => Subgroup.zpowers_le.2 (hc L hL).2.2))
  omega

end CFSG.AGLEmbeddingD2.GN

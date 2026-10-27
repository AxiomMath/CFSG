module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLinNat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilpA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLinCore

public section

universe v

namespace CFSG.QuasithinUnique.Setup.Wreath

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.Quasithin.B6
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

section Assembly

variable {H T M N A : Subgroup (V ≃ₗ[k] V)} {r : ℕ} {g : Fin r → V ≃ₗ[k] V}

theorem B_sup_T_eq [Finite V] (hnat : NaturalS3Factors H N A g) (hAne : A ≠ ⊥)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hO2 : ∀ N' : Subgroup (V ≃ₗ[k] V), N' ≤ H → (N'.subgroupOf H).Normal → IsPGroup 2 N' →
      N' = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M) : natB H N A ⊔ T = H := by
  have hBH : natB H N A ≤ H := hnat.B_le
  have hle : natB H N A ⊔ T ≤ H := sup_le hBH hT.1
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    have hBM : natB H N A ≤ M := le_sup_left.trans (hmax _ le_sup_right hlt)
    have hodd := normal_le_max_odd hO2 hT hTn hTM hMH hmax (natB H N A) hBH hnat.B_normal hBM
    have hAB : A ≤ natB H N A := le_sup_right.trans hnat.LA_le_B
    have h2 : 2 ∣ Nat.card ↥A := two_dvd_card_of_elem hAel hAne
    have hdvd : Nat.card ↥A ∣ Nat.card ↥(natB H N A) := Subgroup.card_dvd_of_le hAB
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hdvd))
  · exact heq

theorem natA_comm' (hnat : NaturalS3Factors H N A g) :
    ∀ i j, ∀ a ∈ natA A g i, ∀ b ∈ natA A g j, a * b = b * a := by
  have hsq : ∀ i, ∀ a ∈ natA A g i, a * a = 1 := by
    intro i a ha
    have h2 : Nat.card ↥(natA A g i) = 2 := hnat.card_A i
    have := pow_card_eq_one' (G := ↥(natA A g i)) (x := ⟨a, ha⟩)
    rw [h2, pow_two] at this
    exact congrArg Subtype.val this
  intro i j a ha b hb
  by_cases hij : i = j
  · subst hij
    have hab : a * b ∈ natA A g i := (natA A g i).mul_mem ha hb
    have h1 := hsq i a ha
    have h2 := hsq i b hb
    have h3 := hsq i _ hab
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h3).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [inv_eq_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right h2]
  · exact hnat.S_comm i j hij a ((le_sup_right : natA A g i ≤ natS N A g i) ha) b
      ((le_sup_right : natA A g j ≤ natS N A g j) hb)

theorem natA_sq_eq_one (hnat : NaturalS3Factors H N A g) :
    ∀ i, ∀ a ∈ natA A g i, a * a = 1 := by
  intro i a ha
  have h2 : Nat.card ↥(natA A g i) = 2 := hnat.card_A i
  have := pow_card_eq_one' (G := ↥(natA A g i)) (x := ⟨a, ha⟩)
  rw [h2, pow_two] at this
  exact congrArg Subtype.val this

theorem odd_mem_natD (hnat : NaturalS3Factors H N A g) (hT : IsSylowTwoOf T H)
    (hsup : natB H N A ⊔ T = H) : ∀ h ∈ H, Odd (orderOf h) → h ∈ natD N A g := by
  intro h hh hodd
  have h1 : h ∈ natB H N A :=
    odd_mem_of_sup_eq hnat.B_le hnat.B_normal hT.1 hT.2.1 hsup h hh hodd
  set C2 : Subgroup (V ≃ₗ[k] V) := ⨆ i, natA A g i with hC2
  have hBeq : natB H N A = natD N A g ⊔ C2 := by
    rw [hnat.B_eq]
    show ⨆ i, (natL N A g i ⊔ natA A g i) = (⨆ i, natL N A g i) ⊔ ⨆ i, natA A g i
    exact iSup_sup_eq
  have hDB : natD N A g ≤ natB H N A := by rw [hBeq]; exact le_sup_left
  have hC2B : C2 ≤ natB H N A := by rw [hBeq]; exact le_sup_right
  have hDH : natD N A g ≤ H := hDB.trans hnat.B_le
  have hDn : ((natD N A g).subgroupOf (natB H N A)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hDB]
    intro d b hd hb
    exact (Subgroup.normal_subgroupOf_iff hDH).1 hnat.D_normal d b hd (hnat.B_le hb)
  have hC2pg : IsPGroup 2 ↥C2 := isPGroup_two_iSup (natA A g) (natA_comm' hnat) (natA_sq_eq_one hnat)
  exact odd_mem_of_sup_eq hDB hDn hC2B hC2pg hBeq.symm h h1 hodd

theorem natD_eq_N (hnat : NaturalS3Factors H N A g) (hT : IsSylowTwoOf T H)
    (hsup : natB H N A ⊔ T = H) (hNH : N ≤ H) (hNodd : Odd (Nat.card N)) :
    natD N A g = N := by
  apply le_antisymm hnat.D_le_N
  intro x hx
  exact odd_mem_natD hnat hT hsup x (hNH hx)
    (Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hx))

theorem N_eq_closure (hnat : NaturalS3Factors H N A g) (hT : IsSylowTwoOf T H)
    (hsup : natB H N A ⊔ T = H) (hNH : N ≤ H) (hNodd : Odd (Nat.card N)) :
    N = Subgroup.closure {h | h ∈ H ∧ Odd (orderOf h)} := by
  apply le_antisymm
  · intro x hx
    exact Subgroup.subset_closure ⟨hNH hx, Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hx)⟩
  · refine (Subgroup.closure_le N).2 ?_
    rintro h ⟨hh, ho⟩
    rw [← natD_eq_N hnat hT hsup hNH hNodd]
    exact odd_mem_natD hnat hT hsup h hh ho

theorem exists_actsAs_of_mem (hnat : NaturalS3Factors H N A g) {x : V ≃ₗ[k] V} (hx : x ∈ H) :
    ∃ σ : Equiv.Perm (Fin r), ActsAs (natI N A g) x σ :=
  exists_actsAs (natI_injective hnat) fun i => by
    obtain ⟨j, -, -, hj⟩ := hnat.S_perm x hx i
    exact ⟨j, hj⟩

theorem s3Wreath_of_natural [Finite V] (hnat : NaturalS3Factors H N A g) (hF : ConjFamily H N A g)
    (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal) (hNodd : Odd (Nat.card N))
    (hAne : A ≠ ⊥) (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hO2 : ∀ N' : Subgroup (V ≃ₗ[k] V), N' ≤ H → (N'.subgroupOf H).Normal → IsPGroup 2 N' →
      N' = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M) : S3Wreath H T N := by
  classical
  have hsup := B_sup_T_eq hnat hAne hAel hO2 hT hTn hTM hMH hmax
  have hND : natD N A g = N := natD_eq_N hnat hT hsup hNH hNodd
  have hBH : natB H N A ≤ H := hnat.B_le
  have hTnorm : T ≤ Subgroup.normalizer (natB H N A : Set (V ≃ₗ[k] V)) :=
    hT.1.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hBH).1 hnat.B_normal)
  have hWinv : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) H (commGL N ⊤) :=
    isInvariant_commGL hNH hNn
  have hWeq : commGL N ⊤ = ⨆ i, natI N A g i := by
    have h := hnat.W_eq
    have e : natW N A g = commGL (natD N A g) ⊤ := rfl
    rw [e, hND] at h
    exact h
  have hWN : natW N A g = commGL N ⊤ := by
    show commGL (natD N A g) ⊤ = _
    rw [hND]
  have hpos : 1 ≤ r := by
    obtain ⟨i, -⟩ := hF.all 1 H.one_mem
    exact Fin.pos i
  have hP2 : IsPGroup 2 ↥(permImage H (natI N A g)) := by
    intro σ'
    obtain ⟨x, hxH, hx⟩ := mem_permImage.1 σ'.2
    have hx' : x ∈ natB H N A ⊔ T := by rw [hsup]; exact hxH
    obtain ⟨b, hb, t, ht, rfl⟩ := mem_sup_mul hTnorm hx'
    have hbact : ActsAs (natI N A g) b 1 := actsAs_one_of_mem_B hnat hb
    have htact : ActsAs (natI N A g) t (σ' : Equiv.Perm (Fin r)) := by
      have := (hbact.inv).mul hx
      simpa using this
    obtain ⟨n, hn⟩ := hT.2.1 ⟨t, ht⟩
    refine ⟨n, ?_⟩
    have ht1 : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have htpow := htact.pow (2 ^ n)
    rw [ht1] at htpow
    have := ActsAs.unique (natI_injective hnat) htpow (ActsAs.one (natI N A g))
    apply Subtype.ext
    simpa using this
  have hPtrans : ∀ i j : Fin r, ∃ σ ∈ permImage H (natI N A g), σ i = j := by
    intro i j
    obtain ⟨x, hxH, -, -, hI⟩ := hnat.S_trans i j
    obtain ⟨σ, hσ⟩ := exists_actsAs_of_mem hnat hxH
    refine ⟨σ, mem_permImage.2 ⟨x, hxH, hσ⟩, ?_⟩
    have h1 := (actsAs_iff_map.1 hσ) i
    exact natI_injective hnat (h1.symm.trans hI)
  have hfaith : ∀ h ∈ H, (∀ w ∈ commGL N ⊤, h w = w) → h = 1 := by
    let K : Subgroup (V ≃ₗ[k] V) := H ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (commGL N ⊤)
    have hKH : K ≤ H := inf_le_left
    have hKn : (K.subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hKH]
      intro k0 h hk0 hh
      refine ⟨H.mul_mem (H.mul_mem hh hk0.1) (H.inv_mem hh), fun w hw => ?_⟩
      have hw' : h⁻¹ w ∈ commGL N ⊤ := hWinv h⁻¹ (H.inv_mem hh) w hw
      have h1 : k0 (h⁻¹ w) = h⁻¹ w := hk0.2 _ hw'
      show h (k0 (h⁻¹ w)) = w
      rw [h1, gl_apply_inv]
    have hKp : IsPGroup 2 ↥K := by
      intro x
      obtain ⟨n, hn⟩ := pow_two_pow_mem_of_sup_eq hBH hnat.B_normal hT.1 hT.2.1 hsup x (hKH x.2)
      refine ⟨n, Subtype.ext ?_⟩
      have h1 : ((x : V ≃ₗ[k] V)) ^ 2 ^ n = 1 := by
        apply eq_one_of_mem_B_fix_W hnat hn
        intro w hw
        rw [hWN] at hw
        exact (K.pow_mem x.2 (2 ^ n)).2 w hw
      simpa using h1
    have hKbot := hO2 K hKH hKn hKp
    intro h hh hfix
    have : h ∈ K := ⟨hh, hfix⟩
    rw [hKbot] at this
    exact Subgroup.mem_bot.1 this
  refine ⟨hnat.card_k, r, hpos, natL N A g, natS N A g, natI N A g,
    permImage H (natI N A g), ?_⟩
  refine
    { L_le := fun i => (le_iSup (natL N A g) i).trans (hND.le)
      card_L := hnat.card_L
      I_eq := fun i => rfl
      finrank_I := hnat.finrank_I
      L_comm := hnat.L_comm
      L_indep := hnat.L_indep
      N_eq := hND
      S_le := fun i => (hnat.S_le_B i).trans hBH
      S_iso := fun i => by
        obtain ⟨hW, hbij⟩ := hnat.S_action i
        have e1 : ↥(natS N A g i) ≃* (↥(natI N A g i) ≃ₗ[k] ↥(natI N A g i)) :=
          MulEquiv.ofBijective _ hbij
        have : Module.Finite k ↥(natI N A g i) := Module.Finite.of_finite
        obtain ⟨e2⟩ := nonempty_mulEquiv_gl (k := k) (hnat.finrank_I i)
        exact ⟨e1.trans e2⟩
      S_comm := hnat.S_comm
      S_indep := hnat.S_indep
      B_normal := by rw [← hnat.B_eq]; exact hnat.B_normal
      B_derived := by rw [← hnat.B_eq]; exact hnat.B_derived.trans hND
      H_eq := by rw [← hnat.B_eq]; exact hsup
      N_odd_gen := N_eq_closure hnat hT hsup hNH hNodd
      S_action := hnat.S_action
      S_fix_I := hnat.S_fix_I
      S_fix_C := fun i => by
        have h := hnat.S_fix_C i
        rw [hND] at h
        exact h
      I_indep := hnat.I_indep
      V_compl := by
        have h := hnat.V_compl
        rw [hnat.W_eq, hND] at h
        exact h
      S_subnormal := fun i =>
        isSubnormal_trans (hnat.S_le_B i) hBH (hnat.S_normal_B i).isSubnormal
          hnat.B_normal.isSubnormal
      T_perm := fun t ht i => hnat.S_perm t (hT.1 ht) i
      T_trans := ?_
      W_eq := hWeq
      faithful := hfaith
      P_two := hP2
      P_trans := hPtrans
      image_eq := ⟨hWinv, ?_⟩
      r_pow := exists_two_pow_of_transitive hpos hP2 hPtrans }
  ·
    intro i j
    obtain ⟨x, hxH, hS, hL, hI⟩ := hnat.S_trans i j
    have hx' : x ∈ natB H N A ⊔ T := by rw [hsup]; exact hxH
    obtain ⟨b, hb, t, ht, rfl⟩ := mem_sup_mul hTnorm hx'
    have hbinv : b⁻¹ ∈ natB H N A := (natB H N A).inv_mem hb
    have e : ∀ X : Subgroup (V ≃ₗ[k] V), conjSub t X = conjSub b⁻¹ (conjSub (b * t) X) := by
      intro X
      rw [← conjSub_mul, inv_mul_cancel_left]
    refine ⟨t, ht, ?_, ?_, ?_⟩
    · rw [e, hS]
      exact (conjSub_eq_of_mem_B hnat hbinv j).1
    · rw [e, hL]
      exact (conjSub_eq_of_mem_B hnat hbinv j).2
    · have hbact := actsAs_one_of_mem_B hnat hb
      rw [map_eq_iff] at hI ⊢
      intro v
      have h1 := hI v
      have h2 := hbact j (t v)
      have h3 : ((1 : Equiv.Perm (Fin r)) j) = j := rfl
      rw [h3] at h2
      exact h2.symm.trans h1
  ·
    ext gW
    constructor
    · rintro ⟨h, rfl⟩
      obtain ⟨σ, hσ⟩ := exists_actsAs_of_mem hnat h.2
      refine ⟨σ, mem_permImage.2 ⟨h, h.2, hσ⟩, fun i w => ?_⟩
      rw [resSub_apply]
      exact hσ i w
    · rintro ⟨σ, hσP, hg⟩
      obtain ⟨x, hxH, hx⟩ := mem_permImage.1 hσP
      let gx : ↥(commGL N ⊤) ≃ₗ[k] ↥(commGL N ⊤) :=
        resSub (MonoidHom.id (V ≃ₗ[k] V)) H (commGL N ⊤) hWinv ⟨x, hxH⟩
      have hgx : ∀ w : ↥(commGL N ⊤), ((gx w : ↥(commGL N ⊤)) : V) = x w := fun w =>
        resSub_apply _ _ _ _ _ _
      let g' : ↥(commGL N ⊤) ≃ₗ[k] ↥(commGL N ⊤) := gW * gx⁻¹
      have hg' : ∀ i, ∀ w : ↥(commGL N ⊤),
          ((g' w : ↥(commGL N ⊤)) : V) ∈ natI N A g i ↔ (w : V) ∈ natI N A g i := by
        intro i w
        have hgw : g' w = gW (gx⁻¹ w) := rfl
        have hxw : x ((gx⁻¹ w : ↥(commGL N ⊤)) : V) = (w : V) := by
          rw [← hgx, gl_apply_inv]
        have e1 : σ (σ⁻¹ i) = i := σ.apply_symm_apply i
        have h1 := hg (σ⁻¹ i) (gx⁻¹ w)
        have h2 := hx (σ⁻¹ i) ((gx⁻¹ w : ↥(commGL N ⊤)) : V)
        rw [e1] at h1 h2
        rw [hgw, h1, ← h2, hxw]
      obtain ⟨b, hb, hbg⟩ := exists_base_agree hnat hWeq g' hg'
      refine ⟨⟨b * x, H.mul_mem (hBH hb) hxH⟩, ?_⟩
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      rw [resSub_apply]
      have e1 : gW w = g' (gx w) := by
        show gW w = gW (gx⁻¹ (gx w))
        rw [gl_inv_apply]
      rw [e1, hbg (gx w), hgx w]
      rfl

end Assembly

end CFSG.QuasithinUnique.Setup.Wreath

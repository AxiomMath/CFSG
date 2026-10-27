module

public import CFSG.CGT.PushingUpLit.BHS5.FiveSixLift
public import CFSG.CGT.PushingUpLit.BHS5.FiveSixGen
public import CFSG.CGT.PushingUpLit.BHS5.FiveSixFinal
public import CFSG.CGT.PushingUpLit.BHS5.FiveSixAlt
public import CFSG.CGT.PushingUpLit.BHS5.FiveSixGrp
public import CFSG.CGT.PushingUpLit.BHS5.FiveSixNC
public import CFSG.CGT.PushingUpLit.BHS5.FiveFive

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.CGT.PushingUpLit.BHS

variable {V : Type} [CommGroup V] [Finite V] {P T M : Subgroup (MulAut V)}

theorem five_six_of_cl (hV : ∀ v : V, v ^ 2 = 1) (hmin : MinPar P T M)
    {W : Set (Subgroup (MulAut (V ⧸ fixOp P)))}
    (hWconj : ∀ E' ∈ W, ∀ g ∈ (⊤ : Subgroup ↥P).map (quotHom P), conjSub g E' ∈ W)
    (hWcomm : ∀ E' ∈ W, ∀ E'' ∈ W, E' ≠ E'' → commV E' ≤ fixV E'')
    {E' : Subgroup (MulAut (V ⧸ fixOp P))} (hE' : E' ∈ W) {E₀ : Subgroup (MulAut V)}
    (hE₀ : E₀ ≤ liftQ P E')
    (hgen : E₀ ≤ Subgroup.closure {x | x ∈ E₀ ∧ Odd (orderOf x)})
    (hcl : ∃ u₁ ∈ commV E₀,
      u₁ ∈ fixV (T ⊓ Subgroup.normalizer (liftQ P E' : Set (MulAut V))) ∧ u₁ ∉ fixV E₀) :
    ∃ g ∈ P, ∃ u ∈ fixV T, g u ≠ u := by
  obtain ⟨u₁, hu₁c, hu₁T, hu₁E⟩ := hcl
  have hTP : T ≤ P := hmin.T_le
  have hE₀P : E₀ ≤ P := hE₀.trans (liftQ_le E')
  obtain ⟨g, hg, u, hu, hne⟩ := exists_fixed_of_orbit (T := T) (E₀ := E₀)
    (E := liftQ P E') (u₁ := u₁) (fun t ht htn => hu₁T t ⟨ht, htn⟩)
    (by
      by_contra h
      push Not at h
      exact hu₁E fun g hg => h g hg)
    (by
      intro t ht htn
      have htP : t ∈ P := hTP ht
      have hρt : quotHom P ⟨t, htP⟩ ∈ (⊤ : Subgroup ↥P).map (quotHom P) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_top _)
      have hE'' : conjSub (quotHom P ⟨t, htP⟩) E' ∈ W := hWconj E' hE' _ hρt
      have hne : conjSub (quotHom P ⟨t, htP⟩) E' ≠ E' := by
        intro heq
        apply htn
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        have : conjSub t (liftQ P E') = liftQ P E' := by rw [conjSub_liftQ htP, heq]
        exact this
      have hXle : conjSub t E₀ ≤ liftQ P (conjSub (quotHom P ⟨t, htP⟩) E') := by
        rw [← conjSub_liftQ htP]
        exact conjSub_mono t hE₀
      refine commV_le_fixV_of_quot hV (X := conjSub t E₀) (Y := E₀)
        (hXle.trans (liftQ_le _)) hE₀P hgen ?_ (map_mem_commV_conj E₀ t hu₁c)
      have hX : (((conjSub t E₀).subgroupOf P).map (quotHom P)) ≤
          conjSub (quotHom P ⟨t, htP⟩) E' := by
        rintro _ ⟨y, hy, rfl⟩
        exact (mem_liftQ.1 (hXle (Subgroup.mem_subgroupOf.1 hy))).2
      have hY : (E₀.subgroupOf P).map (quotHom P) ≤ E' := by
        rintro _ ⟨y, hy, rfl⟩
        exact (mem_liftQ.1 (hE₀ (Subgroup.mem_subgroupOf.1 hy))).2
      exact (B19.commV_mono hX).trans ((hWcomm _ hE'' E' hE' hne).trans (fixV_anti hY)))
  exact ⟨g, hE₀P hg, u, hu, hne⟩

section Common

omit [Finite V] in
theorem liftQ_top : liftQ P ((⊤ : Subgroup ↥P).map (quotHom P)) = P := by
  ext x
  rw [mem_liftQ]
  constructor
  · rintro ⟨hx, -⟩
    exact hx
  · intro hx
    exact ⟨hx, Subgroup.mem_map_of_mem _ (Subgroup.mem_top _)⟩

omit [Finite V] in
theorem conjSub_eq_of_mem_normalizer_liftQ {E' : Subgroup (MulAut (V ⧸ fixOp P))}
    (hE' : E' ≤ (⊤ : Subgroup ↥P).map (quotHom P)) {t : MulAut V} (ht : t ∈ P)
    (htn : t ∈ Subgroup.normalizer (liftQ P E' : Set (MulAut V))) :
    conjSub (quotHom P ⟨t, ht⟩) E' = E' := by
  have h1 : liftQ P (conjSub (quotHom P ⟨t, ht⟩) E') = liftQ P E' := by
    rw [← conjSub_liftQ ht]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1 htn
  have hρt : quotHom P ⟨t, ht⟩ ∈ (⊤ : Subgroup ↥P).map (quotHom P) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_top _)
  have hle : conjSub (quotHom P ⟨t, ht⟩) E' ≤ (⊤ : Subgroup ↥P).map (quotHom P) := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hρt (hE' he))
      (Subgroup.inv_mem _ hρt)
  calc conjSub (quotHom P ⟨t, ht⟩) E'
      = ((liftQ P (conjSub (quotHom P ⟨t, ht⟩) E')).subgroupOf P).map (quotHom P) :=
        (quotImg_liftQ hle).symm
    _ = ((liftQ P E').subgroupOf P).map (quotHom P) := by rw [h1]
    _ = E' := quotImg_liftQ hE'

omit [Finite V] in
theorem card_liftQ (hinj : Function.Injective (quotHom P)) {X : Subgroup (MulAut (V ⧸ fixOp P))}
    (hX : X ≤ (⊤ : Subgroup ↥P).map (quotHom P)) : Nat.card (liftQ P X) = Nat.card X := by
  have h1 := Nat.card_congr (quotImgEquiv hinj (liftQ_le X)).toEquiv
  rw [quotImg_liftQ hX] at h1
  exact h1

omit [Finite V] in
theorem good_E0 (hinj : Function.Injective (quotHom P)) {T : Subgroup (MulAut V)} (hTP : T ≤ P)
    {E' : Subgroup (MulAut (V ⧸ fixOp P))} (hE' : E' ≤ (⊤ : Subgroup ↥P).map (quotHom P)) :
    liftQ P (opResidual 2 E') ≤ liftQ P E' ∧
      liftQ P (opResidual 2 E') ≤
        Subgroup.closure {x | x ∈ liftQ P (opResidual 2 E') ∧ Odd (orderOf x)} ∧
      ∀ t ∈ T ⊓ Subgroup.normalizer (liftQ P E' : Set (MulAut V)),
        conjSub t (liftQ P (opResidual 2 E')) = liftQ P (opResidual 2 E') := by
  have hO : opResidual 2 E' ≤ (⊤ : Subgroup ↥P).map (quotHom P) := (opResidual_le 2 E').trans hE'
  refine ⟨liftQ_mono (opResidual_le 2 E'), ?_, ?_⟩
  · refine le_closure_odd_of_quot hinj (liftQ_le _) ?_
    rw [quotImg_liftQ hO]
    exact opResidual_le_closure_odd E'
  · rintro t ⟨htT, htn⟩
    have htP : t ∈ P := hTP htT
    rw [conjSub_liftQ htP, ← opResidual_conjSub,
      conjSub_eq_of_mem_normalizer_liftQ hE' htP htn]

end Common

section CL

theorem cl_sym_three (hV : ∀ v : V, v ^ 2 = 1) (hmin : MinPar P T M)
    (hinj : Function.Injective (quotHom P)) {E' : Subgroup (MulAut (V ⧸ fixOp P))}
    (hE' : E' ≤ (⊤ : Subgroup ↥P).map (quotHom P)) (θ : ↥E' ≃* Equiv.Perm (Fin 3)) :
    ∃ u₁ ∈ commV (liftQ P (opResidual 2 E')),
      u₁ ∈ fixV (T ⊓ Subgroup.normalizer (liftQ P E' : Set (MulAut V))) ∧
      u₁ ∉ fixV (liftQ P (opResidual 2 E')) := by
  obtain ⟨-, -, hconj⟩ := good_E0 hinj hmin.T_le hE'
  have hO : opResidual 2 E' ≤ (⊤ : Subgroup ↥P).map (quotHom P) := (opResidual_le 2 E').trans hE'
  have hcard : Nat.card (liftQ P (opResidual 2 E')) = 3 := by
    rw [card_liftQ hinj hO, ← altOf_eq_opResidual θ, Nat.card_congr (altEquiv θ).toEquiv,
      Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  refine exists_fixed_commV_odd hV (by rw [hcard]; decide) ?_
    (hmin.syl.2.1.to_le inf_le_left) fun t ht x hx => ?_
  · intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  · have := mem_conjSub_of_mem (g := t) hx
    rwa [hconj t ht] at this

theorem cl_alt (hV : ∀ v : V, v ^ 2 = 1) (hmin : MinPar P T M)
    (hinj : Function.Injective (quotHom P)) {E' : Subgroup (MulAut (V ⧸ fixOp P))}
    (hE' : E' ≤ (⊤ : Subgroup ↥P).map (quotHom P)) {m : ℕ} (D : SymDat E' m) (h5 : 5 ≤ m)
    (hsub : CFSG.Open.IsSubnormal (liftQ P (opResidual 2 E')) P) {A : Subgroup (MulAut V)}
    (hAP : A ≤ P) (hA : IsOff A) (hEA : ⁅liftQ P (opResidual 2 E'), A⁆ ≠ ⊥) :
    ∃ u₁ ∈ commV (liftQ P (opResidual 2 E')),
      u₁ ∈ fixV (T ⊓ Subgroup.normalizer (liftQ P E' : Set (MulAut V))) ∧
      u₁ ∉ fixV (liftQ P (opResidual 2 E')) := by
  obtain ⟨-, hgen, hconj⟩ := good_E0 hinj hmin.T_le hE'
  have hO : opResidual 2 E' ≤ (⊤ : Subgroup ↥P).map (quotHom P) := (opResidual_le 2 E').trans hE'
  obtain ⟨k, hk⟩ := D.odd
  have hnat : IsAltNatSection (liftQ P (opResidual 2 E')) (commV (liftQ P (opResidual 2 E')))
      (commV (liftQ P (opResidual 2 E')) ⊓ fixV (liftQ P (opResidual 2 E'))) m := by
    refine isAltNatSection_of_quot hV hinj (liftQ_le _) hgen ?_
    rw [quotImg_liftQ hO, ← altOf_eq_opResidual D.θ]
    exact D.isAltNatSection_altOf
  subst hk
  exact exists_fixed_commV_alt hV (by omega) (liftQ_le _ |>.trans le_rfl) hsub hAP hA hnat hEA
    (hmin.syl.2.1.to_le inf_le_left) fun t ht x hx => by
      have := mem_conjSub_of_mem (g := t) hx
      rwa [hconj t ht] at this

theorem cl_sl (hV : ∀ v : V, v ^ 2 = 1) (hmin : MinPar P T M)
    (hinj : Function.Injective (quotHom P)) {E' : Subgroup (MulAut (V ⧸ fixOp P))}
    (hE' : E' ≤ (⊤ : Subgroup ↥P).map (quotHom P)) {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsSLNatSection E' (commV E') (commV E' ⊓ fixV E') n)
    (hsub : CFSG.Open.IsSubnormal (liftQ P E') P)
    (hS : IsSylowOf 2 (liftQ P E' ⊓ T) (liftQ P E')) {A : Subgroup (MulAut V)}
    (hAP : A ≤ P) (hA : IsOff A) (hEA : ⁅liftQ P E', A⁆ ≠ ⊥) :
    ∃ u₁ ∈ commV (liftQ P (opResidual 2 E')),
      u₁ ∈ fixV (T ⊓ Subgroup.normalizer (liftQ P E' : Set (MulAut V))) ∧
      u₁ ∉ fixV (liftQ P (opResidual 2 E')) := by
  rw [IsSLNatSection.opResidual_eq hn hnat]
  obtain ⟨-, hgen, -⟩ := good_E0 hinj hmin.T_le hE'
  rw [IsSLNatSection.opResidual_eq hn hnat] at hgen
  have hnatV : IsSLNatSection (liftQ P E') (commV (liftQ P E'))
      (commV (liftQ P E') ⊓ fixV (liftQ P E')) n := by
    refine isSLNatSection_of_quot hV hinj (liftQ_le _) hgen ?_
    rw [quotImg_liftQ hE']
    exact hnat
  obtain ⟨u, hu, huT, huE⟩ := exists_fixed_commV_sl hV hn (liftQ_le E') hsub hAP hA hnatV hEA hS
    (hmin.syl.2.1.to_le inf_le_left) inf_le_right fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨ht.2, Subgroup.le_normalizer ht.1⟩
  exact ⟨u, hu, huT, huE⟩

end CL

section Chain

omit [Finite V] in
theorem isSubnormal_liftQ {E' G' : Subgroup (MulAut (V ⧸ fixOp P))}
    (hE' : E' ≤ (⊤ : Subgroup ↥P).map (quotHom P)) (hG' : G' ≤ (⊤ : Subgroup ↥P).map (quotHom P))
    (hEG : E' ≤ G') (hGE : G' ≤ Subgroup.normalizer (E' : Set (MulAut (V ⧸ fixOp P))))
    (hPG : (⊤ : Subgroup ↥P).map (quotHom P) ≤
      Subgroup.normalizer (G' : Set (MulAut (V ⧸ fixOp P)))) :
    CFSG.Open.IsSubnormal (liftQ P E') P := by
  have h1 : (liftQ P E').subgroupOf (liftQ P G') |>.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (liftQ_mono hEG)).2
      ((le_normalizer_liftQ_iff hE' hG').2 hGE)
  have h2 : ((liftQ P G').subgroupOf P).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (liftQ_le G')).2 ?_
    have := (le_normalizer_liftQ_iff hG' (le_refl _)).2 hPG
    rwa [liftQ_top] at this
  exact CFSG.Open.IsSubnormal.step (liftQ_mono hEG) h1
    (CFSG.Open.IsSubnormal.step (liftQ_le G') h2 (CFSG.Open.IsSubnormal.refl P))

theorem isSylowOf_liftQ (hmin : MinPar P T M) {E' G' : Subgroup (MulAut (V ⧸ fixOp P))}
    (hE' : E' ≤ (⊤ : Subgroup ↥P).map (quotHom P)) (hG' : G' ≤ (⊤ : Subgroup ↥P).map (quotHom P))
    (hEG : E' ≤ G') (hGE : G' ≤ Subgroup.normalizer (E' : Set (MulAut (V ⧸ fixOp P))))
    (hPG : (⊤ : Subgroup ↥P).map (quotHom P) ≤
      Subgroup.normalizer (G' : Set (MulAut (V ⧸ fixOp P)))) :
    IsSylowOf 2 (liftQ P E' ⊓ T) (liftQ P E') := by
  have hPn : P ≤ Subgroup.normalizer (liftQ P G' : Set (MulAut V)) := by
    have := (le_normalizer_liftQ_iff hG' (le_refl _)).2 hPG
    rwa [liftQ_top] at this
  have h1 : IsSylowOf 2 (liftQ P G' ⊓ T) (liftQ P G') :=
    FourTwoTools.isSylowOf_inf_of_le_normalizer hmin.syl (liftQ_le G') hPn
  have h2 : IsSylowOf 2 (liftQ P E' ⊓ (liftQ P G' ⊓ T)) (liftQ P E') :=
    FourTwoTools.isSylowOf_inf_of_le_normalizer h1 (liftQ_mono hEG)
      ((le_normalizer_liftQ_iff hE' hG').2 hGE)
  rwa [← inf_assoc, inf_eq_left.2 (liftQ_mono hEG)] at h2

omit [Finite V] in
theorem exists_noncomm_liftQ {X : Subgroup (MulAut (V ⧸ fixOp P))}
    (hX : X ≤ (⊤ : Subgroup ↥P).map (quotHom P)) (h : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a) :
    ∃ a ∈ liftQ P X, ∃ b ∈ liftQ P X, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  obtain ⟨y, -, rfl⟩ := hX ha
  obtain ⟨z, -, rfl⟩ := hX hb
  refine ⟨(y : MulAut V), mem_liftQ.2 ⟨y.2, ha⟩, (z : MulAut V), mem_liftQ.2 ⟨z.2, hb⟩, ?_⟩
  intro h'
  apply hab
  have : y * z = z * y := Subtype.ext h'
  rw [← map_mul, ← map_mul, this]

end Chain

section Main

theorem five_six (hsym : BHSSymType) (hV : ∀ v : V, v ^ 2 = 1)
    (hmin : MinPar P T M) (ho2 : pCoreOf 2 P = ⊥)
    (hoff : ∃ A : Subgroup (MulAut V), A ≤ P ∧ IsOff A) :
    ∃ g ∈ P, ∃ u ∈ fixV T, g u ≠ u := by
  classical
  have hinj := quotHom_injective hV hmin ho2
  have hH := hyp51_quot hV hmin ho2 hoff
  have hVq := quot_sq_eq_one hV (fixOp P)
  have hF := five_five hsym hH hVq
  obtain ⟨W, hW⟩ : ∃ W, W = compSet ((⊤ : Subgroup ↥P).map (quotHom P))
      ((M.subgroupOf P).map (quotHom P)) := ⟨_, rfl⟩
  rw [← hW] at hF
  have hWle : ∀ E' ∈ W, E' ≤ (⊤ : Subgroup ↥P).map (quotHom P) :=
    fun E' hE' => hF.le_P hH hVq hE'
  have hgenD_le : genD ((⊤ : Subgroup ↥P).map (quotHom P)) ≤ (⊤ : Subgroup ↥P).map (quotHom P) :=
    genD_le hH hVq
  have hPtn : (⊤ : Subgroup ↥P).map (quotHom P) ≤
      Subgroup.normalizer (genD ((⊤ : Subgroup ↥P).map (quotHom P)) : Set _) :=
    le_normalizer_genD hH hVq
  by_cases h3 : ∃ E' ∈ W, Nonempty (↥E' ≃* Equiv.Perm (Fin 3))
  ·
    obtain ⟨E', hE', ⟨θ⟩⟩ := h3
    obtain ⟨hle, hgen, -⟩ := good_E0 hinj hmin.T_le (hWle E' hE')
    exact five_six_of_cl hV hmin hF.conj_mem hF.commV_le hE' hle hgen
      (cl_sym_three hV hmin hinj (hWle E' hE') θ)
  · push Not at h3
    have hnonab : ∀ E' ∈ W, ∃ a ∈ opResidual 2 E', ∃ b ∈ opResidual 2 E', a * b ≠ b * a := by
      intro E' hE'
      rcases hF.type E' hE' with ⟨n, hn2, hnat, -, -⟩ | ⟨m, θ, β, hm, h3', -⟩
      · rw [IsSLNatSection.opResidual_eq hn2 hnat]
        exact IsSLNatSection.exists_noncomm hn2 hnat
      · have h5 : 5 ≤ m := by
          obtain ⟨k, hk⟩ := hm
          by_contra hlt
          have : m = 3 := by omega
          subst this
          exact (h3 E' hE').false θ
        rw [← altOf_eq_opResidual θ]
        exact exists_noncomm_altOf h5 θ
    obtain ⟨A₀, hA₀P, hA₀⟩ := hoff
    obtain ⟨k, hk, hkle⟩ := Glauberman.exists_conj_le_of_isSylowOf hmin.syl
      (isPGroup_of_isElemAbelian2 hA₀.2.2.1) hA₀P
    have hAT : conjSub k A₀ ≤ T := hkle
    have hAoff : IsOff (conjSub k A₀) := hA₀.conj k
    have hAP : conjSub k A₀ ≤ P := hAT.trans hmin.T_le
    set S : Set (Subgroup (MulAut V)) := (fun E' => liftQ P (opResidual 2 E')) '' W with hS
    set Y : Subgroup (MulAut V) := ⨆ X ∈ S, X with hY
    have hYn : P ≤ Subgroup.normalizer (Y : Set (MulAut V)) := by
      refine le_normalizer_iSup fun X hX g hg => ?_
      obtain ⟨E', hE', rfl⟩ := hX
      have hρ : quotHom P ⟨g, hg⟩ ∈ (⊤ : Subgroup ↥P).map (quotHom P) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_top _)
      refine ⟨conjSub (quotHom P ⟨g, hg⟩) E', hF.conj_mem E' hE' _ hρ, ?_⟩
      show liftQ P (opResidual 2 (conjSub (quotHom P ⟨g, hg⟩) E')) =
        conjSub g (liftQ P (opResidual 2 E'))
      rw [conjSub_liftQ hg, opResidual_conjSub]
    have hYO : Y ≤ opResidual 2 P := by
      refine iSup₂_le fun X hX => ?_
      obtain ⟨E', hE', rfl⟩ := hX
      obtain ⟨-, hgen, -⟩ := good_E0 hinj hmin.T_le (hWle E' hE')
      refine hgen.trans ((Subgroup.closure_le _).2 fun x hx => ?_)
      exact mem_opResidual_of_coprime (liftQ_le _ hx.1) (Nat.coprime_two_right.2 hx.2)
    have hYab : ∃ a ∈ Y, ∃ b ∈ Y, a * b ≠ b * a := by
      obtain ⟨E₁, hE₁⟩ := hF.nonempty
      obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_liftQ
        ((opResidual_le 2 E₁).trans (hWle E₁ hE₁)) (hnonab E₁ hE₁)
      exact ⟨a, le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ S) => X)
        (liftQ P (opResidual 2 E₁)) ⟨E₁, hE₁, rfl⟩ le_rfl ha, b,
        le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ S) => X)
        (liftQ P (opResidual 2 E₁)) ⟨E₁, hE₁, rfl⟩ le_rfl hb, hab⟩
    obtain ⟨a, haA, y, hyY, hay⟩ := exists_noncomm_of_nonabelian hmin ho2 hYn hYO hYab hAT
      hAoff.2.1
    obtain ⟨E', hE', y', hy', hay'⟩ :
        ∃ E' ∈ W, ∃ y' ∈ liftQ P (opResidual 2 E'), a * y' ≠ y' * a := by
      by_contra hcon
      push Not at hcon
      have hYc : Y ≤ Subgroup.centralizer ({a} : Set (MulAut V)) := by
        refine iSup₂_le fun X hX => ?_
        obtain ⟨E', hE', rfl⟩ := hX
        intro y' hy'
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        rw [Set.mem_singleton_iff] at hc
        rw [hc]
        exact hcon E' hE' y' hy'
      exact hay (Subgroup.mem_centralizer_iff.1 (hYc hyY) a (Set.mem_singleton a))
    have hEA : ⁅liftQ P (opResidual 2 E'), conjSub k A₀⁆ ≠ ⊥ := by
      intro h
      have := Subgroup.commutator_mem_commutator hy' haA
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact hay' this.symm
    obtain ⟨hle, hgen, -⟩ := good_E0 hinj hmin.T_le (hWle E' hE')
    refine five_six_of_cl hV hmin hF.conj_mem hF.commV_le hE' hle hgen ?_
    have hsubE : CFSG.Open.IsSubnormal (liftQ P E') P :=
      isSubnormal_liftQ (hWle E' hE') hgenD_le (hF.le_genD hE') (hF.genD_le_normalizer hE') hPtn
    rcases hF.type E' hE' with ⟨n, hn2, hnat, -, -⟩ |
      ⟨m, θ, β, hm, h3', hinv, hsurj, hker, hequiv, htop, hD, hpt⟩
    · rw [IsSLNatSection.opResidual_eq hn2 hnat] at hEA
      exact cl_sl hV hmin hinj (hWle E' hE') hn2 hnat hsubE
        (isSylowOf_liftQ hmin (hWle E' hE') hgenD_le (hF.le_genD hE') (hF.genD_le_normalizer hE')
          hPtn) hAP hAoff hEA
    · have h5 : 5 ≤ m := by
        obtain ⟨k, hk⟩ := hm
        by_contra hlt
        have : m = 3 := by omega
        subst this
        exact (h3 E' hE').false θ
      have hOE : opResidual 2 E' ≤ (⊤ : Subgroup ↥P).map (quotHom P) :=
        (opResidual_le 2 E').trans (hWle E' hE')
      have hEn : E' ≤ Subgroup.normalizer (opResidual 2 E' : Set (MulAut (V ⧸ fixOp P))) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (opResidual_le 2 E')).1
          (opResidual_normal 2 E')
      have hsub0 : CFSG.Open.IsSubnormal (liftQ P (opResidual 2 E')) P :=
        CFSG.Open.IsSubnormal.step (liftQ_mono (opResidual_le 2 E'))
          ((Subgroup.normal_subgroupOf_iff_le_normalizer (liftQ_mono (opResidual_le 2 E'))).2
            ((le_normalizer_liftQ_iff hOE (hWle E' hE')).2 hEn)) hsubE
      exact cl_alt hV hmin hinj (hWle E' hE') ⟨θ, β, hm, h3', hinv, hsurj, hker, hequiv, htop⟩ h5
        hsub0 hAP hAoff hEA

end Main

end CFSG.CGT.PushingUpLit.BHS5

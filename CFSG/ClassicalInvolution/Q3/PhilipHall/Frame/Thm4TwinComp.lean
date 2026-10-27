module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinThmA
public import CFSG.ClassicalInvolution.Q3.TL4SepCompo

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace Thm4Twin

section Aux

variable {G : Type} [Group G]

theorem isPGroup_zpowers_mul {x y : G} (hxy : Commute x y) (hx : IsPGroup 2 (Subgroup.zpowers x))
    (hy : IsPGroup 2 (Subgroup.zpowers y)) : IsPGroup 2 (Subgroup.zpowers (x * y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hx) ⟨x, Subgroup.mem_zpowers x⟩
  obtain ⟨l, hl⟩ := (IsPGroup.iff_orderOf.mp hy) ⟨y, Subgroup.mem_zpowers y⟩
  rw [Subgroup.orderOf_mk] at hk hl
  have hdvd : orderOf (x * y) ∣ 2 ^ (max k l) := by
    refine hxy.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd ?_ ?_)
    · rw [hk]; exact pow_dvd_pow 2 (le_max_left _ _)
    · rw [hl]; exact pow_dvd_pow 2 (le_max_right _ _)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

end Aux

section ThreeSix

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem twinGroup_le_centralizer_of_isSubnormal (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) {A : Subgroup Y}
    (hAC : CFSG.Open.IsSubnormal A (Subgroup.centralizer ({t} : Set Y)))
    (hA : CFSG.Open.IsQuasisimple ↥A) : twinGroup R ≤ Subgroup.centralizer (A : Set Y) := by
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  set T := twinGroup R with hT
  have huniq := Q8Datum.isUniqueInvolution_core hd
  have hTC : T ≤ C := by
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨-, z, hzK, hzJ⟩ := hJ
    have hz : z = t := hzK.eq huniq
    rw [hz] at hzJ
    exact isUniqueInvolution_le_centralizer hzJ
  have hCN : C ≤ Subgroup.normalizer (T : Set Y) := by
    intro d hdC
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => conj_mem_twinGroup hd hΩ hdC hx, fun hx => ?_⟩
    have := conj_mem_twinGroup hd hΩ (Subgroup.inv_mem _ hdC) hx
    simpa [mul_assoc] using this
  have hcomm : ⁅GorensteinWalter.componentLayerOf C, T⁆ = ⊥ :=
    GorensteinWalter.componentLayerOf_centralizes_solvable_of_le_normalizer _ T hTC
      (twinGroup_isSolvable hd hΩ)
      ((GorensteinWalter.componentLayerOf_isNormalIn _).1.trans hCN)
  have hTE : T ≤ Subgroup.centralizer (GorensteinWalter.componentLayerOf C : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hcomm)
  have hEA : A ≤ GorensteinWalter.componentLayerOf C :=
    le_sSup (isComponentOf_of_open ⟨le_of_isSubnormal hAC, hAC, hA⟩)
  exact fun _ hr => Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hEA) (hTE hr)

end ThreeSix

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

omit [Finite G] in
theorem TwinT4Hyp.le_normalizer_of_le_centralizer (h : TwinT4Hyp r G Δ) {K J : Subgroup G}
    (hK : K ∈ Δ) (hJ : J ∈ Δ) (hKJ : K ≠ J) {z : G} (hz : IsUniqueInvolution K z)
    (hJz : J ≤ Subgroup.centralizer ({z} : Set G)) : J ≤ Subgroup.normalizer (K : Set G) := by
  have hc : ∀ x ∈ J, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hJz hx)
  rw [← h.gen hJ, Subgroup.closure_le]
  rintro v ⟨hvJ, hv2⟩
  by_cases hvc : ∀ w ∈ J, v * w = w * v
  · obtain ⟨-, P, hP, hPnc⟩ := h.hyp.omega1 J hJ
    have hab : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact hPnc ⟨⟨fun a b => Subtype.ext (hcon a a.2 b b.2)⟩⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hab
    have haJ : a ∈ J := hP.1 ha
    have ha2 : IsPGroup 2 (Subgroup.zpowers a) := hP.2.1.to_le (Subgroup.zpowers_le.mpr ha)
    have hanc : ¬ ∀ w ∈ J, a * w = w * a := fun hh => hab (hh b (hP.1 hb))
    have hwnc : ¬ ∀ w ∈ J, (v * a) * w = w * (v * a) := by
      intro hh
      apply hanc
      intro w hw
      have h1 := hh w hw
      have h2 := hvc w hw
      calc a * w = v⁻¹ * (v * a * w) := by group
        _ = v⁻¹ * (w * (v * a)) := by rw [h1]
        _ = v⁻¹ * w * v * a := by group
        _ = w * a := by
          have : v⁻¹ * w * v = w := by
            rw [mul_assoc, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [this]
    have hcom : Commute v a := hvc a haJ
    have hw2 : IsPGroup 2 (Subgroup.zpowers (v * a)) := isPGroup_zpowers_mul hcom hv2 ha2
    have hwz : (v * a) * z = z * (v * a) := by
      rw [mul_assoc, hc a haJ, ← mul_assoc, hc v hvJ, mul_assoc]
    have hwN := h.hyp.omega5 K hK J hJ hKJ z hz (v * a) (J.mul_mem hvJ haJ) hwnc hw2 hwz
    have haN := h.hyp.omega5 K hK J hJ hKJ z hz a haJ hanc ha2 (hc a haJ)
    have : v = (v * a) * a⁻¹ := by group
    rw [this]
    exact (Subgroup.normalizer (K : Set G)).mul_mem hwN
      ((Subgroup.normalizer (K : Set G)).inv_mem haN)
  · exact h.hyp.omega5 K hK J hJ hKJ z hz v hvJ hvc hv2 (hc v hvJ)

theorem odd_card_inf {K J : Subgroup G} {z t : G} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z ≠ t) : Odd (Nat.card ↥(K ⊓ J)) := by
  by_contra hcon
  have h2 : 2 ∣ Nat.card ↥(K ⊓ J) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hcon)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨w, hw⟩, hw2⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hwo : orderOf w = 2 := by
    rw [← Subgroup.orderOf_mk w hw]
    exact hw2
  have hww : w * w = 1 := by rw [← pow_two, ← hwo, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hwo
    omega
  have h1 : w = z := (hz.unique w hw.1 hww).resolve_left hw1
  have h2' : w = t := (ht.unique w hw.2 hww).resolve_left hw1
  exact hzt (h1.symm.trans h2')

theorem TwinT4Hyp.component_normal (hA : Thm4TwinThmA r) (h : TwinT4Hyp r G Δ)
    (hgen : omegaGen Δ = ⊤) (hno : TL4.NoInvO2 Δ) {L : Subgroup G} (hL : CFSG.IsComponent L) :
    L.Normal := by
  have hle : omegaGen Δ ≤ Subgroup.normalizer (L : Set G) := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨z, hz⟩ := (h.hyp.omega1 K hK).1
    intro x hx
    exact mem_normalizer_iff_conjSub_eq.mpr (hA G Δ h K hK z hz (hno K hK z hz) L hL x hx)
  rw [hgen] at hle
  exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hle)

theorem TwinT4Hyp.exists_component (hA : Thm4TwinThmA r) (h : TwinT4Hyp r G Δ)
    (hgen : omegaGen Δ = ⊤) (hno : TL4.NoInvO2 Δ) {J : Subgroup G} (hJ : J ∈ Δ) {u : G}
    (hu : IsUniqueInvolution J u) :
    ∃ L : Subgroup G, CFSG.IsComponent L ∧ L.Normal ∧ u ∈ L := by
  have huE := h.mem_layer hJ hu (hno J hJ u hu)
  have hex : ∃ L : Subgroup G, CFSG.IsComponent L ∧ ¬ ∀ x ∈ L, x * u = u * x := by
    by_contra hcon
    push Not at hcon
    have hle : layer G ≤ Subgroup.centralizer ({u} : Set G) :=
      sSup_le fun L hL x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcon L hL x hx)
    have hC : u ∈ Subgroup.centralizer (layer G : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    exact hno J hJ u hu ⟨_, TightA.centerLayer_normal, TightA.centerLayer_isPGroup h.odd, huE, hC⟩
  obtain ⟨L, hL, hLu⟩ := hex
  have hLn := h.component_normal hA hgen hno hL
  refine ⟨L, hL, hLn, ?_⟩
  by_contra huL
  exact hLu fun x hx =>
    Subgroup.mem_centralizer_iff.mp (h.le_centralizer_of_not_mem hJ hu hLn huL hu.mem) x hx

theorem TwinT4Hyp.le_centralizer_component (hA : Thm4TwinThmA r) (h : TwinT4Hyp r G Δ)
    (hgen : omegaGen Δ = ⊤) (hno : TL4.NoInvO2 Δ) {K : Subgroup G} (hK : K ∈ Δ) {z : G}
    (hz : IsUniqueInvolution K z) {M : Subgroup G} (hM : CFSG.IsComponent M) (hzM : z ∉ M) :
    K ≤ Subgroup.centralizer (M : Set G) :=
  h.le_centralizer_of_not_mem hK hz (h.component_normal hA hgen hno hM) hzM

theorem TwinT4Hyp.not_mem_component_of_ne (h : TwinT4Hyp r G Δ) (hno : TL4.NoInvO2 Δ)
    {K : Subgroup G} (hK : K ∈ Δ) {z : G} (hz : IsUniqueInvolution K z) {L M : Subgroup G}
    (hL : CFSG.IsComponent L) (hM : CFSG.IsComponent M) (hLM : L ≠ M) (hzL : z ∈ L) :
    z ∉ M := by
  intro hzM
  have hzZ := TightA.mem_centerLayer_of_mem_center hL hzL fun y hy =>
    comm_of_ne hL hM hLM hy hzM
  exact hno K hK z hz ⟨_, TightA.centerLayer_normal, TightA.centerLayer_isPGroup h.odd, hzZ⟩

theorem TwinT4Hyp.le_centralizer_component_of_le (h : TwinT4Hyp r G Δ) {J : Subgroup G}
    (hJ : J ∈ Δ) {u : G} (hu : IsUniqueInvolution J u) {L : Subgroup G}
    (hL : CFSG.IsComponent L) (hLn : L.Normal) (hLu : L ≤ Subgroup.centralizer ({u} : Set G)) :
    J ≤ Subgroup.centralizer (L : Set G) := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  have hsub : CFSG.Open.IsSubnormal L (Subgroup.centralizer ({u} : Set G)) :=
    CFSG.Open.IsSubnormal.step hLu inferInstance (CFSG.Open.IsSubnormal.refl _)
  have hT := twinGroup_le_centralizer_of_isSubnormal (h.q8Datum hJ hu S)
    (h.hypOmegaGen_conjClass hJ) hsub ⟨hL.1.1.commutator_eq_top, hL.1.2.1⟩
  have hJT : J ≤ twinGroup J := by
    have := tightCore_le_twinGroup (h.q8Datum hJ hu S)
    rwa [h.tightCore_eq hJ] at this
  exact hJT.trans hT

theorem TwinT4Hyp.commutes_of_not_mem_component (hA : Thm4TwinThmA r) (h : TwinT4Hyp r G Δ)
    (hgen : omegaGen Δ = ⊤) (hno : TL4.NoInvO2 Δ) {K J : Subgroup G} (hK : K ∈ Δ) (hJ : J ∈ Δ)
    {z t : G} (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) {L : Subgroup G}
    (hL : CFSG.IsComponent L) (hzL : z ∈ L) (htL : t ∉ L) : Commutes K J := by
  have hLn := h.component_normal hA hgen hno hL
  obtain ⟨L', hL', hL'n, htL'⟩ := h.exists_component hA hgen hno hJ ht
  have hne : L ≠ L' := fun e => htL (e ▸ htL')
  have hLt : L ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_ne hL hL' hne hx htL')
  have hL'z : L' ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_ne hL' hL hne.symm hx hzL)
  have hJL := h.le_centralizer_component_of_le hJ ht hL hLn hLt
  have hKL' := h.le_centralizer_component_of_le hK hz hL' hL'n hL'z
  have hzt : z ≠ t := fun e => htL (e ▸ hzL)
  have hKJne : K ≠ J := fun e => hzt (hz.eq (e ▸ ht))
  have hJz : J ≤ Subgroup.centralizer ({z} : Set G) := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hJL hj)) z hzL).symm
  have htK : K ≤ Subgroup.centralizer ({t} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hKL' hk)) t htL').symm
  have hJN : J ≤ Subgroup.normalizer (K : Set G) :=
    h.le_normalizer_of_le_centralizer hK hJ hKJne hz hJz
  have hKN : K ≤ Subgroup.normalizer (J : Set G) :=
    h.le_normalizer_of_le_centralizer hJ hK hKJne.symm ht htK
  have hcard := odd_card_inf hz ht hzt
  have hKJ : ∀ c ∈ K, c ∈ J → c = 1 := by
    intro c hcK hcJ
    have hodd : Odd (orderOf c) := by
      refine hcard.of_dvd_nat ?_
      have := orderOf_dvd_natCard (⟨c, Subgroup.mem_inf.mpr ⟨hcK, hcJ⟩⟩ : ↥(K ⊓ J))
      rwa [Subgroup.orderOf_mk] at this
    have hle : layer G ≤ Subgroup.centralizer ({c} : Set G) := by
      refine sSup_le fun M hM => ?_
      by_cases hML : M = L
      · subst hML
        exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hJL hcJ)) x hx)
      · have hzM := h.not_mem_component_of_ne hno hK hz hL hM (Ne.symm hML) hzL
        have hKM := h.le_centralizer_component hA hgen hno hK hz hM hzM
        exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hKM hcK)) x hx)
    have hcE : c ∈ Subgroup.centralizer (layer G : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    have hFZ := h.le_center_of_normal_two hgen hno fittingSubgroup_normal
      (TL4.isPGroup_fittingSubgroup h.odd)
    have hcF : c ∈ Subgroup.centralizer (fittingSubgroup G : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => (Subgroup.mem_center_iff.mp (hFZ hy) c).symm
    have hcC : c ∈ Subgroup.centralizer (generalizedFitting G : Set G) :=
      TL4.le_centralizer_sup (Subgroup.zpowers_le.mpr hcF) (Subgroup.zpowers_le.mpr hcE)
        (Subgroup.mem_zpowers c)
    have hcFs : c ∈ generalizedFitting G := centralizer_generalizedFitting_le G hcC
    exact eq_one_of_isPGroup_of_mem_odd (A := Subgroup.zpowers c)
      (by rw [Nat.card_zpowers]; exact hodd) (Subgroup.mem_zpowers c)
      (((TL4.isPGroup_center_fstar h.odd)).to_le (Subgroup.zpowers_le.mpr ⟨hcFs, hcC⟩))
  intro k hk j hj
  have hc1 : k * j * k⁻¹ * j⁻¹ ∈ J :=
    J.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN hk) j).mp hj) (J.inv_mem hj)
  have hc2 : k * j * k⁻¹ * j⁻¹ ∈ K := by
    have h1 : j * k⁻¹ * j⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hJN hj) k⁻¹).mp (K.inv_mem hk)
    have h2 := K.mul_mem hk h1
    rwa [show k * (j * k⁻¹ * j⁻¹) = k * j * k⁻¹ * j⁻¹ by group] at h2
  have h1 := hKJ _ hc2 hc1
  calc k * j = k * j * k⁻¹ * j⁻¹ * (j * k) := by group
    _ = j * k := by rw [h1, one_mul]

variable {J L : Subgroup G}

theorem TwinT4Min.inv_mem_component (hA : Thm4TwinThmA r)
    (hm : TwinT4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L)
    (hgen : omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤)
    (hno : TL4.NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L)) :
    ∃ L₀ : Subgroup G, CFSG.IsComponent L₀ ∧
      ∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ z : G,
        IsUniqueInvolution K z → z ∈ L₀ := by
  obtain ⟨u, hu⟩ := (hm.hyp.hyp.omega1 J hm.memJ).1
  obtain ⟨v, hv⟩ := (hm.hyp.hyp.omega1 L hm.memL).1
  obtain ⟨L₀, hL₀, hL₀n, huL₀⟩ := hm.hyp.exists_component hA hgen hno hm.memJ hu
  have hvL₀ : v ∈ L₀ := by
    by_contra hvL₀
    exact hm.notComm (hm.hyp.commutes_of_not_mem_component hA hgen hno hm.memJ hm.memL hu hv hL₀
      huL₀ hvL₀)
  refine ⟨L₀, hL₀, ?_⟩
  rintro K (⟨g, rfl⟩ | ⟨g, rfl⟩) z hz
  · rw [hz.eq (hu.conj g)]
    exact hL₀n.conj_mem u huL₀ g
  · rw [hz.eq (hv.conj g)]
    exact hL₀n.conj_mem v hvL₀ g

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

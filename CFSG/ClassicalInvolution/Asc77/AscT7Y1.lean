module

public import CFSG.ClassicalInvolution.Asc77.AscT7L9
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace T7Y

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

section Algebra

omit [Finite G] in
theorem eq_one_of_sq_eq_one_of_mem_odd {N : Subgroup G} [Finite N] (hN : Odd (Nat.card N))
    {o : G} (ho : o ∈ N) (ho2 : o * o = 1) : o = 1 := by
  have h1 : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ho2)
  have h2 : orderOf o ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N ho
  have h3 : orderOf o ∣ Nat.gcd 2 (Nat.card N) := Nat.dvd_gcd h1 h2
  have h4 : Nat.gcd 2 (Nat.card N) = 1 := Nat.coprime_two_left.mpr hN
  rw [h4] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

omit [Finite G] in
theorem commute_of_alphaOf_eq_bot {a : G} {A : Subgroup G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hα : alphaOf A = ⊥) {n x : G} (hn : n ∈ oddCoreOf (Subgroup.centralizer ({a} : Set G)))
    (hx : x ∈ A) : n * x = x * n := by
  have h1 : ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆ ≤ alphaOf A := by
    unfold alphaOf
    refine le_trans ?_ le_sup_left
    refine le_trans ?_ (le_iSup₂ (f := fun (a : G) (_ : a ∈ A) =>
      ⨆ (_ : a ≠ 1), ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆) a haA)
    exact le_iSup (fun _ : a ≠ 1 => ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆) ha1
  have h2 : ⁅n, x⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆ :=
    Subgroup.commutator_mem_commutator hn hx
  have h3 := h1 h2
  rw [hα] at h3
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h3)

omit [Finite G] in
theorem comm_e_of_comm_u_ue (hu2 : u * u = 1) {c : G} (hcu : c * u = u * c)
    (hcue : c * (u * e) = (u * e) * c) : c * e = e * c := by
  have he : e = u * (u * e) := by rw [← mul_assoc, hu2, one_mul]
  calc c * e = c * (u * (u * e)) := by rw [← he]
    _ = (c * u) * (u * e) := (mul_assoc c u (u * e)).symm
    _ = (u * c) * (u * e) := by rw [hcu]
    _ = u * (c * (u * e)) := mul_assoc u c (u * e)
    _ = u * ((u * e) * c) := by rw [hcue]
    _ = (u * (u * e)) * c := (mul_assoc u (u * e) c).symm
    _ = e * c := by rw [← he]

end Algebra

theorem sup_centralizer_eq_top [IsSimpleGroup G] (hE : ThmEWithSylow p f) (htr : C23_2_trans p f)
    (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤ := by
  have hstd : StdCent Ω K
      (Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G)) z :=
    hs.stdCent_of_twin le_sup_right fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
      obtain ⟨c, hcz, hcu⟩ := c23_2_fuse G Ω K K' z hs W hd.hW hd.hzW u hd.hu hd.huW hd.hu1
        hd.huz hd.hu2 L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
      intro a ha
      have ha' : a * (x * y) = (x * y) * a := Subgroup.mem_centralizer_singleton_iff.mp ha
      have hu' : u = c⁻¹ * (x * y) * c := by rw [← hcu]; group
      have hcomm : (c⁻¹ * a * c) * u = u * (c⁻¹ * a * c) := by
        have e1 : c⁻¹ * (a * (x * y)) * c = c⁻¹ * ((x * y) * a) * c := by rw [ha']
        calc (c⁻¹ * a * c) * u = c⁻¹ * (a * (x * y)) * c := by rw [hu']; group
          _ = c⁻¹ * ((x * y) * a) * c := e1
          _ = u * (c⁻¹ * a * c) := by rw [hu']; group
      have hcH : c ∈ Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_sup_right hcz
      have ha'H : c⁻¹ * a * c ∈
          Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
      have : a = c * (c⁻¹ * a * c) * c⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcH ha'H) (Subgroup.inv_mem _ hcH)
  exact thmE_apply hE hs.stand hs.hz hs.hK' hs.hne hstd
    (htr G Ω K K' z hs W hd.hW hd.hzW u hd.hu hd.huW hd.hu1 hd.huz hd.hu2)

theorem alphaOf_eq_bot [IsSimpleGroup G]
    (hG : Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤)
    (hΓu : Subgroup.centralizer ({u} : Set G) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)))
    (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ := by
  obtain ⟨hodd, halpha⟩ := T7K.c23_5X_one_proved hs hd
  have hΓz := T7K.centralizer_z_le_gamma2 hs hd
  have hN : Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hG]
    exact sup_le (hΓu.trans (gamma2_le_normalizer_alphaOf halpha _))
      (hΓz.trans (gamma2_le_normalizer_alphaOf halpha _))
  exact T7B.eq_bot_of_normalizer_eq_top hodd hN (T7B.two_dvd_natCard hs.hz)

theorem le_centralizer_e [IsSimpleGroup G] (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    {L : Subgroup G} (hLΩ : L ∈ Ω) (hzL : IsUniqueInvolution L z) {R : Subgroup G}
    (hR : IsSylow2In R L) (hRN : R ≤ Subgroup.normalizer (W : Set G)) :
    L ≤ Subgroup.centralizer ({e} : Set G) := by
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hcl : IsClassicalMember p f L z := isClassicalMember_of_twin hΩ hLΩ hzL
  have he2 : IsPGroup 2 (Subgroup.zpowers e) := isPGroup_zpowers_of_mul_self_eq_one hd.he2 hd.he1
  have hetq : e ∈ trivialOnQuot L :=
    (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ he2 hLΩ).mpr
      ⟨R, hR, fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (T7K.comm_e hd (hRN hr))⟩
  obtain ⟨hzB, huB, heB⟩ := T7K.generators_mem_B z u e
  have hze : z ≠ e := fun h => T7K.e_not_mem_sup hs hd (h ▸ Subgroup.mem_sup_left hs.hz.mem)
  have hA : IsElemAbelian2 (Subgroup.closure ({z, e} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hs.hz.sq hd.he2 hs.hz.ne_one hd.he1 hze
      (T7K.comm_e_of_mem_W hd hd.hzW)
  have hAB : Subgroup.closure ({z, e} : Set G) ≤ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hzB
    · exact heB
  obtain ⟨-, halpha⟩ := T7K.c23_5X_one_proved hs hd
  have hαA : alphaOf (Subgroup.closure ({z, e} : Set G)) = ⊥ := (halpha _ hAB hA).trans hα
  intro ℓ hℓ
  obtain ⟨i, hi, n, hn, rfl⟩ := exactCore_cover hcl he2 hetq ℓ hℓ
  refine Subgroup.mul_mem _ (exactCore_le_centralizer e L hi) ?_
  have hnO : n ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
    oddCoreIn_le_of_isSubnormal (T7A.isSubnormal_centralizer hΩ hLΩ hzL) hn
  have hnz : n * e = e * n :=
    commute_of_alphaOf_eq_bot (Subgroup.subset_closure (by simp)) hs.hz.ne_one hαA hnO
      (Subgroup.subset_closure (by simp))
  exact Subgroup.mem_centralizer_singleton_iff.mpr hnz

theorem exists_mul_centralizer_u [IsSimpleGroup G] (htcf : TwinCentralFact p)
    (hgen : E4TwinGen p) (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    {h : G} (hh : h ∈ Subgroup.centralizer ({u} : Set G)) :
    ∃ y ∈ exactLayer Ω u, ∃ c ∈ Subgroup.centralizer ({u} : Set G) ⊓
      Subgroup.centralizer ({u * e} : Set G), h = y * c := by
  classical
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hBelow : CITBelowU p f (Nat.card G) := hst.below f hq
  obtain ⟨a₂, b₂, v', ha₂Y, hb₂Y, hv'Y, htY, hv'z, hS, hlt, T, hconj⟩ := T7L.layer_u_frame hs hd
  obtain ⟨-, hCI⟩ := T7L.twinSection_gen_conj htcf hgen hp hq hBelow hlt hS T
  have hBel := T7K.B_isElemAbelian hs hd
  obtain ⟨hzB, huB, heB⟩ := T7K.generators_mem_B z u e
  have htB : u * e ∈ Subgroup.closure ({u * e, u, z} : Set G) := Subgroup.mul_mem _ huB heB
  have sq : ∀ x ∈ Subgroup.closure ({u * e, u, z} : Set G), x * x = 1 := fun x hx => by
    have := hBel.2 x hx
    rwa [pow_two] at this
  obtain ⟨⟨ht1, htu⟩, -⟩ := T7L.B_ne hs hd
  have hYH : exactLayer Ω u ≤ Subgroup.centralizer ({u} : Set G) := exactLayer_le_centralizer Ω u
  obtain ⟨B₀, hB₀, hmem, huniq⟩ := hconj h hh
  obtain ⟨yb, hyb⟩ := hCI B₀ hB₀ _ huniq
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
  have hcongr := T7L.mem_oddCore_of_mk_conj htY hmem y hyb
  exact T7L.eq_mul_of_conj_mod hYH (oddCoreIn_le _) (oddCoreOf_odd_natCard _)
    (fun y hy => normalizer_oddCoreIn _ hy) htY (sq _ htB) ht1 hh y.2 hcongr

end T7Y

end CFSG.ClassicalInvolution.Asc77

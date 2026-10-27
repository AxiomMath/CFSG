module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4Pl
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4Lift
public import CFSG.GH74.GLS.Stage2.OddAut.CoprimeFixed

public section

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists CFSG
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.PartTwo.KFacts
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4

variable {K : Type} [Field K]

theorem proj_ne_one_of_pow {m : ℕ} (hm : Odd m) {x : StatedSp 2 K} (hx : x ^ m = 1) (hx1 : x ≠ 1) :
    proj 2 K x ≠ 1 := by
  intro h
  apply hx1
  apply eq_of_proj_eq_odd hm hx (one_pow m)
  rw [h, map_one]

theorem plane_step [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hcen : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥)
    (hHP : ∀ P : Submodule K (Fin 2 ⊕ Fin 2 → K), Module.finrank K P = 2 → P ⊓ orth P = ⊥ →
      ∀ r : ℕ, NoOddNormal ((HP P).map (proj 2 K)) r)
    {r : ℕ} {V Z : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (h2 : N2Cfg (StatedProj (StatedSp 2 K)) r V Z) (h3 : N3Full (StatedProj (StatedSp 2 K)) V Z)
    (hrK : (r : K) ≠ 0) {x : StatedSp 2 K} (hx : x ^ r = 1) (hx1 : x ≠ 1) (hne : fixSp x ≠ ⊥)
    (hxV : MulAut.conj (proj 2 K x) ∈ V) {z : MulAut (StatedProj (StatedSp 2 K))} (hz : z ∈ Z)
    (A : gsp 2 K) (σ : K ≃+* K) (hzAσ : z = conjAut 2 K A * fieldAut 2 K σ) :
    σ = 1 ∧ ∀ w ∈ fixSp x, w ≠ 0 → ∃ l : K, semi A σ w = l • w ∧
      l ^ 2 = ((multiplier 2 K A : Kˣ) : K) := by
  classical
  have hrodd : Odd r := h2.2.1
  obtain ⟨hPd, hPo⟩ := fixSp_plane hx hrK hx1 hne
  set P := fixSp x with hP
  have hxfix : ∀ q ∈ P, act x q = q := fun q hq => mem_fixSp.mp hq
  have hv1 : MulAut.conj (proj 2 K x) ≠ 1 := by
    intro h
    exact proj_ne_one_of_pow hrodd hx hx1
      ((mulAut_conj_injective_of_center_bot hcen) (by rw [h, map_one]))
  have hzx : ∀ z' ∈ Z, z' (proj 2 K x) = proj 2 K x := fun z' hz' =>
    fix_of_commute_conj hcen (h2.2.2.2.2.2.2.2.2 _ hxV z' hz')
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  set M : Subgroup (StatedProj (StatedSp 2 K)) := (HP P).map (proj 2 K) with hM
  have hMle : M ≤ fixSub (MulAut.conj (proj 2 K x)) := by
    rintro _ ⟨h, hh, rfl⟩
    rw [mem_fixSub, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
      ← commute_of_fix_HP hPo hxfix hh, mul_assoc, mul_inv_cancel, mul_one]
  have hMinv : ∀ z' ∈ Z, ∀ c ∈ M, z' c ∈ M := by
    intro z' hz' c hc
    obtain ⟨h, hh, rfl⟩ := hc
    obtain ⟨A', σ', hz'eq⟩ := psp4_odd_automorphism_normal_form hodd z'
    have hcfx : cf A' σ' x = x := by
      apply eq_of_proj_eq_odd hrodd
      · rw [cf_pow, hx, map_one]
      · exact hx
      · rw [← conjAut_fieldAut_proj, ← hz'eq]; exact hzx z' hz'
    have hΦP : ∀ v ∈ P, semi A' σ' v ∈ P := by
      intro v hv
      rw [hP, mem_fixSp] at hv ⊢
      have := cf_mulVec_semi A' σ' x v
      rw [hcfx] at this
      exact this.trans (by rw [show mx (x : GL _ K) *ᵥ v = act x v from rfl, hv])
    refine ⟨cf A' σ' h, cf_mem_HP A' σ' hΦP hh, ?_⟩
    rw [hz'eq]
    exact (conjAut_fieldAut_proj A' σ' h).symm
  have hMno : NoOddNormal M r := hHP P hPd hPo r
  have hfix := fix_step hcen h2 h3 hxV hv1 hMle hMinv hMno
  have hzcf : ∀ w ∈ P, ∀ t : K, cf A σ (tvS w t) = tvS w t := by
    intro w hw t
    have h1 := hfix z hz _ ⟨tvS w t, tvS_mem_HP hw t, rfl⟩
    rw [hzAσ, conjAut_fieldAut_proj] at h1
    apply eq_of_proj_eq (p := p)
    · rw [cf_pow, pow_char_tvS, map_one]
    · exact pow_char_tvS w t
    · exact h1
  obtain ⟨w0, hw0P, hw00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨l0, hl0, hl02, hσ⟩ := fix_tvS A σ hw00 ⊤ (fun t _ => hzcf w0 hw0P t)
  have hσ1 : σ = 1 := RingEquiv.ext fun c => hσ c trivial
  refine ⟨hσ1, fun w hw hw0 => ?_⟩
  obtain ⟨l, hl, hl2, -⟩ := fix_tvS A σ hw0 ⊤ (fun t _ => hzcf w hw t)
  exact ⟨l, hl, hl2⟩


theorem caseB [Finite K] {p n : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ n)
    (hcen : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥)
    (hHP : ∀ P : Submodule K (Fin 2 ⊕ Fin 2 → K), Module.finrank K P = 2 → P ⊓ orth P = ⊥ →
      ∀ r : ℕ, NoOddNormal ((HP P).map (proj 2 K)) r)
    {r : ℕ} (hrp : r ≠ p) {V Z : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (h2 : N2Cfg (StatedProj (StatedSp 2 K)) r V Z) (h3 : N3Full (StatedProj (StatedSp 2 K)) V Z)
    (hVinn : ∀ v ∈ V, ∃ g : StatedProj (StatedSp 2 K), MulAut.conj g = v) : False := by
  classical
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hr : r.Prime := h2.1
  have : Fact r.Prime := ⟨hr⟩
  have hrodd : Odd r := h2.2.1
  have hVe : IsElementaryAbelian r ↥V := h2.2.2.1
  have hVc : Nat.card ↥V = r ^ 2 := h2.2.2.2.1
  have hrK : ¬ r ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr (Fact.out : p.Prime)).mp (hr.dvd_of_dvd_pow h))
  have hrK0 : (r : K) ≠ 0 := fun h =>
    hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hr).mp
      ((CharP.cast_eq_zero_iff K p r).mp h)).symm
  have hinj := mulAut_conj_injective_of_center_bot hcen
  set V0 : Subgroup (StatedProj (StatedSp 2 K)) :=
    V.comap (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))) with hV0
  have hV0mem : ∀ g, g ∈ V0 ↔ MulAut.conj g ∈ V := fun g => Iff.rfl
  have hV0card : Nat.card ↥V0 = r ^ 2 := by
    rw [← hVc]
    refine Nat.card_congr (Equiv.ofBijective
      (fun g : ↥V0 => (⟨MulAut.conj (g : StatedProj (StatedSp 2 K)), g.2⟩ : ↥V)) ⟨?_, ?_⟩)
    · intro g h hgh
      exact Subtype.ext (hinj (congrArg Subtype.val hgh))
    · rintro ⟨v, hv⟩
      obtain ⟨g, rfl⟩ := hVinn v hv
      exact ⟨⟨g, hv⟩, rfl⟩
  have hV0pow : ∀ g : ↥V0, g ^ r = 1 := by
    intro g
    apply Subtype.ext
    apply hinj
    have := elemPow_eq_one_of_isElementaryAbelian (p := r) (A := V) _ g.2
    simpa [map_pow] using this
  have hV0e : IsElementaryAbelian r ↥V0 :=
    { is_comm := ⟨fun a b => by
        apply Subtype.ext
        apply hinj
        have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥V)).comm
          ⟨MulAut.conj (a : StatedProj (StatedSp 2 K)), a.2⟩
          ⟨MulAut.conj (b : StatedProj (StatedSp 2 K)), b.2⟩)
        simpa [map_mul] using this⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hV0pow }
  have h2' := h2
  have := hV0e
  set lift : ↥V0 →* StatedSp 2 K := liftHom hrodd with hlift
  have hmulcomm : ∀ a b : ↥V0, a * b = b * a := fun a b =>
    (IsMulCommutative.is_comm (M := ↥V0)).comm a b
  have hcomm : ∀ a b : ↥V0, lift a * lift b = lift b * lift a := fun a b => by
    rw [← map_mul, ← map_mul, hmulcomm]
  let ρ : ↥V0 →* GL (Fin 2 ⊕ Fin 2) K := (StatedSp 2 K).subtype.comp lift
  have htopne : (⊤ : Submodule K (Fin 2 ⊕ Fin 2 → K)) ≠ ⊥ := by
    intro h
    have h1 := (Submodule.eq_bot_iff _).mp h (Pi.single (Sum.inl 0) 1) Submodule.mem_top
    have h2 := congrFun h1 (Sum.inl 0)
    simp at h2
  obtain ⟨a, ha1, u, -, hu0, hau⟩ := exists_fixed_vec_of_coprime (r := r) (K := K) hrK
    (A := ↥V0) (by rw [hV0card]) ρ ⊤ htopne (fun _ _ _ => Submodule.mem_top)
  set x := lift a with hx
  have hxr : x ^ r = 1 := liftHom_pow hrodd a
  have hx1 : x ≠ 1 := fun h => ha1 (liftHom_injective hrodd (h.trans (map_one lift).symm))
  have hne : fixSp x ≠ ⊥ := by
    intro h
    have : u ∈ fixSp x := mem_fixSp.mpr hau
    rw [h, Submodule.mem_bot] at this
    exact hu0 this
  have hxV : MulAut.conj (proj 2 K x) ∈ V := by
    rw [hx, hlift, proj_liftHom hrodd a]
    exact a.2
  obtain ⟨hPd, hPo⟩ := fixSp_plane hxr hrK0 hx1 hne
  set P := fixSp x with hP
  set Q := orth P with hQ
  have hQd : Module.finrank K Q = 2 := by rw [hQ, finrank_orth, hPd]
  have hQo : Q ⊓ orth Q = ⊥ := by rw [hQ, orth_orth, inf_comm]; exact hPo
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h] at hQd
    simp at hQd
  have hPstab : ∀ b : ↥V0, ∀ q ∈ P, act (lift b) q ∈ P := by
    intro b q hq
    rw [hP, mem_fixSp] at hq ⊢
    calc act x (act (lift b) q) = act (x * lift b) q := (act_mul _ _ _).symm
      _ = act (lift b * x) q := by rw [hx, hcomm a b]
      _ = act (lift b) (act x q) := act_mul _ _ _
      _ = act (lift b) q := by rw [hq]
  have hQstab : ∀ b : ↥V0, ∀ v ∈ Q, act (lift b) v ∈ Q := by
    intro b v hv
    rw [hQ, mem_orth]
    intro q hq
    have h1 : spForm 2 K q (act (lift b) v) = spForm 2 K (act (lift b)⁻¹ q) v := by
      conv_lhs => rw [← act_act_inv (lift b) q]
      rw [spForm_act]
    rw [h1]
    have h3 : act (lift b)⁻¹ q ∈ P := by
      rw [← map_inv]
      exact hPstab b⁻¹ q hq
    exact (mem_orth.mp hv) _ h3
  obtain ⟨b, hb1, w0, hw0Q, hw00, hbw⟩ := exists_fixed_vec_of_coprime (r := r) (K := K) hrK
    (A := ↥V0) (by rw [hV0card]) ρ Q hQne (fun c w hw => hQstab c w hw)
  set y := lift b with hy
  have hyr : y ^ r = 1 := liftHom_pow hrodd b
  have hy1 : y ≠ 1 := fun h => hb1 (liftHom_injective hrodd (h.trans (map_one lift).symm))
  have hyQ : ∀ v ∈ Q, act y v = v :=
    eq_id_on_plane hQd hQo hyr hrK0 (hQstab b) hw0Q hw00 hbw
  have hyne : fixSp y ≠ ⊥ := by
    intro h
    have : w0 ∈ fixSp y := mem_fixSp.mpr hbw
    rw [h, Submodule.mem_bot] at this
    exact hw00 this
  obtain ⟨hP'd, -⟩ := fixSp_plane hyr hrK0 hy1 hyne
  have hfixy : fixSp y = Q :=
    (Submodule.eq_of_le_of_finrank_eq (fun v hv => mem_fixSp.mpr (hyQ v hv))
      (by rw [hP'd, hQd])).symm
  have hyV : MulAut.conj (proj 2 K y) ∈ V := by
    rw [hy, hlift, proj_liftHom hrodd b]
    exact b.2
  obtain ⟨-, -, -, -, -, hZodd, hZcop, hZbot, -⟩ := h2'
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
  obtain ⟨A, σ, hzAσ⟩ :=
    psp4_odd_automorphism_normal_form hodd (z : MulAut (StatedProj (StatedSp 2 K)))
  obtain ⟨hσ1, hPev⟩ := plane_step hp2 hcen hHP h2 h3 hrK0 hxr hx1 hne hxV z.2 A σ hzAσ
  obtain ⟨-, hQev⟩ := plane_step hp2 hcen hHP h2 h3 hrK0 hyr hy1 hyne hyV z.2 A σ hzAσ
  rw [hfixy] at hQev
  subst hσ1
  have hA1 : ∀ w, semi A 1 w = mx (A : GL _ K) *ᵥ w := fun w => rfl
  obtain ⟨l1, hl1⟩ := exists_scalar_of_forall_eigen (mx (A : GL _ K)) P (fun w hw hw0 => by
    obtain ⟨l, hl, -⟩ := hPev w hw hw0
    exact ⟨l, by rw [← hA1]; exact hl⟩)
  obtain ⟨l2, hl2⟩ := exists_scalar_of_forall_eigen (mx (A : GL _ K)) Q (fun w hw hw0 => by
    obtain ⟨l, hl, -⟩ := hQev w hw hw0
    exact ⟨l, by rw [← hA1]; exact hl⟩)
  have hl1sq : l1 ^ 2 = ((multiplier 2 K A : Kˣ) : K) := by
    obtain ⟨w, hwP, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨l, hl, hlsq⟩ := hPev w hwP hw0
    rw [hA1, hl1 w hwP] at hl
    have := smul_left_injective K hw0 hl
    rw [this]
    exact hlsq
  have hl2sq : l2 ^ 2 = ((multiplier 2 K A : Kˣ) : K) := by
    obtain ⟨w, hwQ, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQne
    obtain ⟨l, hl, hlsq⟩ := hQev w hwQ hw0
    rw [hA1, hl2 w hwQ] at hl
    have := smul_left_injective K hw0 hl
    rw [this]
    exact hlsq
  have hAA : mx (A : GL _ K) * mx (A : GL _ K) =
      ((multiplier 2 K A : Kˣ) : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    by_contra hne'
    obtain ⟨v, hv⟩ := OddAut.exists_mulVec_ne_zero (sub_ne_zero.mpr hne')
    apply hv
    have hvtop : v ∈ P ⊔ Q := by rw [hQ, sup_orth_eq_top hPo]; exact Submodule.mem_top
    obtain ⟨p', hp', q', hq', rfl⟩ := Submodule.mem_sup.mp hvtop
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_add, hl1 p' hp', hl2 q' hq', Matrix.mulVec_smul,
      Matrix.mulVec_smul, hl1 p' hp', hl2 q' hq', smul_smul, smul_smul, ← pow_two, ← pow_two,
      hl1sq, hl2sq, smul_add, sub_self]
  have hA2 : (A ^ 2 : gsp 2 K) = ⟨GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2)
      (multiplier 2 K A), scalar_mem_gsp _⟩ := by
    apply Subtype.ext
    apply Units.ext
    have e1 : mx (((A ^ 2 : gsp 2 K) : GL _ K)) = mx (A : GL _ K) * mx (A : GL _ K) := by
      rw [pow_two]; rfl
    show mx (((A ^ 2 : gsp 2 K) : GL _ K)) = _
    rw [e1, hAA]
    simp only [GeneralLinearGroup.coe_scalar]
    rw [smul_one_eq_diagonal]
    rfl
  have hzsq : (z : MulAut (StatedProj (StatedSp 2 K))) ^ 2 = 1 := by
    rw [hzAσ, map_one, mul_one, ← map_pow, hA2]
    exact conjAut_scalar_eq_one _
  have hdvd : orderOf (z : MulAut (StatedProj (StatedSp 2 K))) ∣ Nat.card ↥Z := by
    have := orderOf_dvd_natCard z
    rwa [← Subgroup.orderOf_coe] at this
  have hodd' : Odd (orderOf (z : MulAut (StatedProj (StatedSp 2 K)))) := Odd.of_dvd_nat hZodd hdvd
  have h2dvd : orderOf (z : MulAut (StatedProj (StatedSp 2 K))) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hzsq
  have h1 : orderOf (z : MulAut (StatedProj (StatedSp 2 K))) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2dvd with h | h
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  exact hz1 (Subtype.ext (orderOf_eq_one_iff.mp h1))

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4

module

public import CFSG.GH74.GLS.Stage4.T2Bad3
public import CFSG.GH74.GLS.Stage4.T2Leaves
public import CFSG.GH74.GLS.Stage4.T2HOdd9
public import CFSG.GH74.GLS.Stage4.T2P51
public import CFSG.GH74.GLS.Stage4.T2P52Done

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Lifted
  CFSG.Assembly.LowTwoRank

section Aut

theorem t2G_pow_fix {Q : Type} [Group Q] (ρ : MulAut Q) {P : Subgroup Q} (hfix : ∀ p ∈ P, ρ p = p)
    (k : ℕ) : ∀ p ∈ P, (ρ ^ k) p = p := by
  intro p hp
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hfix p hp, ih]

theorem t2G_trivial_of_odd_right {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (P : Sylow 2 Q) (ρ : MulAut Q) (hρ : Odd (orderOf ρ)) (hfix : ∀ p ∈ (P : Subgroup Q), ρ p = p)
    (hσ : (gammaOf hodd h3 (MulAut.congr e ρ)).right = 1) : ρ = 1 := by
  have hαo : orderOf (MulAut.congr e ρ) = orderOf ρ := MulEquiv.orderOf_eq (MulAut.congr e) ρ
  have hγo : orderOf (gammaOf hodd h3 (MulAut.congr e ρ)) ∣ orderOf (MulAut.congr e ρ) :=
    orderOf_map_dvd (gammaOf hodd h3) _
  have hγ : gammaOf hodd h3 (MulAut.congr e ρ) =
      SemidirectProduct.inl (gammaOf hodd h3 (MulAut.congr e ρ)).left :=
    SemidirectProduct.ext rfl (by simpa using hσ)
  have hlo : orderOf (gammaOf hodd h3 (MulAut.congr e ρ)).left =
      orderOf (gammaOf hodd h3 (MulAut.congr e ρ)) := by
    conv_rhs => rw [hγ]
    exact (orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective _).symm
  have hleft : (gammaOf hodd h3 (MulAut.congr e ρ)).left ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    t2H_pgl_odd_mem hodd _ (by rw [hlo]; exact Odd.of_dvd_nat (by rw [hαo]; exact hρ) hγo)
  obtain ⟨s, hs⟩ := (mem_inn_iff hodd h3 (MulAut.congr e ρ)).2 ⟨hσ, hleft⟩
  have hcomm : ∀ p ∈ (P : Subgroup Q), s * e p = e p * s := by
    intro p hp
    have h1 : MulAut.congr e ρ (e p) = e p := by
      show e (ρ (e.symm (e p))) = e p
      rw [MulEquiv.symm_apply_apply, hfix p hp]
    rw [← hs, MulAut.conj_apply] at h1
    calc s * e p = (s * e p * s⁻¹) * s := by group
      _ = e p * s := by rw [h1]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 ↥((P : Subgroup Q).map e.toMonoidHom) := P.isPGroup'.map e.toMonoidHom
  have hidx : ¬ 2 ∣ ((P : Subgroup Q).map e.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective e.bijective]
    exact P.not_dvd_index
  have key := t2C_cent_sylow_sl2 hodd _ hP' hidx s (by
    rintro _ ⟨p, hp, rfl⟩
    exact hcomm p hp)
  have hscen : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (t2C_center_sl2 s).2 key
  have hs1 : (MulAut.conj s : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) = 1 := by
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hscen g]
    group
  exact (MulAut.congr e).injective (by rw [← hs, hs1, map_one])

theorem t2G_oddAut_pow3 {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F] [Finite F] {n a b : ℕ}
    (hF : Nat.card F = 3 ^ n) (hn : n = 2 ^ a * 3 ^ b) (h3 : 3 < Nat.card F)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) (P : Sylow 2 Q) (ρ : MulAut Q)
    (hρ : Odd (orderOf ρ)) (hfix : ∀ p ∈ (P : Subgroup Q), ρ p = p) : ρ ^ (3 ^ b) = 1 := by
  have hodd : Odd (Nat.card F) := by rw [hF]; exact Odd.pow (by decide)
  have hdvd1 : orderOf (gammaOf hodd h3 (MulAut.congr e ρ)).right ∣ orderOf ρ := by
    calc orderOf (gammaOf hodd h3 (MulAut.congr e ρ)).right
        ∣ orderOf (gammaOf hodd h3 (MulAut.congr e ρ)) :=
          orderOf_map_dvd (SemidirectProduct.rightHom) _
      _ ∣ orderOf (MulAut.congr e ρ) := orderOf_map_dvd (gammaOf hodd h3) _
      _ = orderOf ρ := MulEquiv.orderOf_eq (MulAut.congr e) ρ
  have hdvd2 : orderOf (gammaOf hodd h3 (MulAut.congr e ρ)).right ∣ n := by
    have := pow_card_eq_one' (G := F ≃+* F) (x := (gammaOf hodd h3 (MulAut.congr e ρ)).right)
    rw [CFSG.GH74.GLS.IVK.card_ringAut F 3 n Nat.prime_three hF] at this
    exact orderOf_dvd_of_pow_eq_one this
  have hodd' : Odd (orderOf (gammaOf hodd h3 (MulAut.congr e ρ)).right) :=
    Odd.of_dvd_nat hρ hdvd1
  rw [hn] at hdvd2
  have hσ_ord : orderOf (gammaOf hodd h3 (MulAut.congr e ρ)).right ∣ 3 ^ b :=
    (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd')).dvd_of_dvd_mul_left hdvd2
  have hσk : (gammaOf hodd h3 (MulAut.congr e ρ)).right ^ (3 ^ b) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 hσ_ord
  refine t2G_trivial_of_odd_right hodd h3 e P (ρ ^ (3 ^ b)) ?_ ?_ ?_
  · exact Odd.of_dvd_nat hρ (orderOf_pow_dvd _)
  · exact t2G_pow_fix ρ hfix _
  · rw [map_pow, map_pow]
    have := map_pow SemidirectProduct.rightHom (gammaOf hodd h3 (MulAut.congr e ρ)) (3 ^ b)
    rw [SemidirectProduct.rightHom_eq_right] at this
    simpa [SemidirectProduct.rightHom_eq_right] using this.trans hσk

end Aut

section Cent

variable {G : Type} [Group G]

theorem t2G_aut_pow_coe {K : Subgroup G} (ρ : MulAut ↥K) (f : G)
    (hρ : ∀ y : ↥K, ((ρ y : ↥K) : G) = f * y * f⁻¹) (k : ℕ) :
    ∀ y : ↥K, (((ρ ^ k) y : ↥K) : G) = f ^ k * y * (f ^ k)⁻¹ := by
  induction k with
  | zero => intro y; simp
  | succ k ih =>
    intro y
    rw [pow_succ, MulAut.mul_apply, ih, hρ]
    group

variable {K S : Subgroup G} {F : Type} [Field F] [Finite F]

theorem t2_odd_cent_pow3_gen {n a b : ℕ} (hF : Nat.card F = 3 ^ n) (hn : n = 2 ^ a * 3 ^ b)
    (h3 : 3 < Nat.card F) (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hS2 : IsPGroup 2 ↥S)
    (hSK : ¬ 2 ∣ (S ⊓ K).relIndex K) [Finite G] {f : G} (hfn : ∀ x ∈ K, f * x * f⁻¹ ∈ K)
    (hodd : Odd (orderOf f)) (hfS : ∀ s ∈ S, f * s = s * f) :
    ∀ y ∈ K, f ^ (3 ^ b) * y * (f ^ (3 ^ b))⁻¹ = y := by
  have hfm : f ∈ normalizer (K : Set G) := Subgroup.mem_normalizer_fintype hfn
  let ρ : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨f, hfm⟩
  have hρ : ∀ y : ↥K, ((ρ y : ↥K) : G) = f * y * f⁻¹ := fun y => rfl
  have hρodd : Odd (orderOf ρ) := by
    have hdvd := orderOf_map_dvd K.normalizerMonoidHom (⟨f, hfm⟩ : Subgroup.normalizer (K : Set G))
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat hodd hdvd
  have hP : IsPGroup 2 ↥((S ⊓ K).subgroupOf K) := (hS2.to_le inf_le_left).comap_subtype
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥K := hP.toSylow hSK
  have hPcoe : (P : Subgroup ↥K) = (S ⊓ K).subgroupOf K := IsPGroup.toSylow_coe hP hSK
  have hfix : ∀ p ∈ (P : Subgroup ↥K), ρ p = p := by
    intro p hp
    rw [hPcoe] at hp
    apply Subtype.ext
    rw [hρ]
    have := hfS (p : G) (Subgroup.mem_subgroupOf.1 hp).1
    calc f * (p : G) * f⁻¹ = (p : G) * f * f⁻¹ := by rw [this]
      _ = p := by group
  have h1 : ρ ^ (3 ^ b) = 1 := t2G_oddAut_pow3 hF hn h3 e P ρ hρodd hfix
  intro y hy
  have h4 := t2G_aut_pow_coe ρ f hρ (3 ^ b) ⟨y, hy⟩
  rw [h1, MulAut.one_apply] at h4
  exact h4.symm

theorem t2G_three_elt_mem {C : Subgroup G} (hKC : K ≤ C) (hKn : ∀ c ∈ C, ∀ x ∈ K, c * x * c⁻¹ ∈ K)
    [Finite G] (P₀ : Sylow 3 G) (hP₀ : (P₀ : Subgroup G) ≤ K) {f : G} (hfC : f ∈ C) {m : ℕ}
    (hf3 : f ^ (3 ^ m) = 1) : f ∈ K := by
  classical
  have hP₀C : (P₀ : Subgroup G) ≤ C := hP₀.trans hKC
  let P' : Sylow 3 ↥C := P₀.subtype hP₀C
  let x : ↥C := ⟨f, hfC⟩
  have hx : IsPGroup 3 ↥(Subgroup.zpowers x) := by
    refine IsPGroup.of_card_dvd_pow (n := m) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hf3))
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C P' Q
  have hxQ : x ∈ (Q : Subgroup ↥C) := hQ (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul] at hxQ
  obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hxQ
  have hyP : (y : G) ∈ (P₀ : Subgroup G) := hy
  have hfe : f = (g : G) * (y : G) * (g : G)⁻¹ := by
    have := congrArg Subtype.val hyx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this.symm
  rw [hfe]
  exact hKn g g.2 y (hP₀ hyP)

end Cent

section Main

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2_C_eq_C₁_smooth
    {n a b : ℕ} (hn : n = 2 ^ a * 3 ^ b)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hBad : Ch6Bad3 G) :
    centralizer ({z} : Set G) ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
  obtain ⟨N, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ :=
    ch6T2P51 G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ t hSet hRem rfl
  obtain ⟨F, hF5⟩ :=
    ch6T2P52 G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
  have ctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨P₀, hP₀⟩ := t2_bad3 hSet hBad
  have := hSet.finite₁
  have := hSet.finite₂
  have h3₁ : 3 < Nat.card F₁ := by rw [hSet.card₁]; have := hSet.five; omega
  have h3₂ : 3 < Nat.card F₂ := by rw [hSet.card₂]; have := hSet.five; have := hSet.le; omega
  subst hz hK₁ hK₂
  obtain ⟨⟨e₁, -⟩, ⟨e₂, -⟩⟩ := t2C_coords hSet
  obtain ⟨hs₁, hs₂⟩ := t2C_sylow_inf_K hSet hRem ctx.Sctx
  have hF1 : ∀ f ∈ F, f = 1 := by
    intro f hf
    have hodd : Odd (orderOf f) := hF5.F_odd f hf
    have hfS : ∀ s ∈ N.S, f * s = s * f := by
      intro s hs
      have hfC : f ∈ centralizer (N.S : Set G) := by
        rw [hF5.centS]; exact Subgroup.mem_sup_right hf
      exact (Subgroup.mem_centralizer_iff.1 hfC s hs).symm
    have hfz : f * N.z = N.z * f := hfS N.z hLoc.z_mem_S
    have hfC' : f ∈ centralizer ({N.z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hfz
    obtain ⟨hn₁, hn₂⟩ := t2Ctx_odd_normK ctx hfz hodd
    have hc₁ := t2_odd_cent_pow3_gen hSet.card₁ hn h3₁ e₁ ctx.Sctx.S2 hs₁ hn₁ hodd hfS
    have hc₂ := t2_odd_cent_pow3_gen hSet.card₂ hn h3₂ e₂ ctx.Sctx.S2 hs₂ hn₂ hodd hfS
    have hfk : f ^ (3 ^ b) = 1 := by
      refine t2C_R_odd_trivial hSet hRem ctx (f ^ (3 ^ b)) (Subgroup.pow_mem _ hfC' _)
        (Odd.of_dvd_nat hodd (orderOf_pow_dvd _)) ?_
      intro k hk
      obtain ⟨a', ha, b', hb, rfl⟩ := (mem_sup_iff_of_comm hSet.comm k).1 hk
      have e1 := hc₁ a' ha
      have e2 := hc₂ b' hb
      calc f ^ (3 ^ b) * (a' * b')
          = (f ^ (3 ^ b) * a' * (f ^ (3 ^ b))⁻¹) * (f ^ (3 ^ b) * b' * (f ^ (3 ^ b))⁻¹) *
              f ^ (3 ^ b) := by group
        _ = a' * b' * f ^ (3 ^ b) := by rw [e1, e2]
    have hfK : f ∈ N.K₁ ⊔ N.K₂ :=
      t2G_three_elt_mem hSet.le_centralizer (fun c hc x hx => ctx.Kn c hc x hx) P₀ hP₀ hfC' hfk
    have hfzp := t2C_cent_K hSet hRem ctx.Sctx f hfK hfS
    rcases t2C_zpowers_cases (t2C_zz hSet) hfzp with h1 | h1
    · exact h1
    · exfalso
      rw [h1, hSet.central.1] at hodd
      exact absurd hodd (by decide)
  intro c hc
  have h1 := hF5.C_le hc
  have h2 : c ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := by
    have hFb : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hF1
    rw [hFb, sup_bot_eq] at h1
    exact h1
  rw [← ctx.KS]
  exact h2

end Main

section Leaf

theorem t2_smooth_23 {n : ℕ} (hn : n ≠ 0) (h : ∀ r : ℕ, r.Prime → r ∣ n → r = 2 ∨ r = 3) :
    ∃ a b : ℕ, n = 2 ^ a * 3 ^ b := by
  obtain ⟨a, m, hm2, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 2 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hnm
    exact hn hnm
  obtain ⟨b, m', hm3, hmm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by norm_num)
  have hm1 : m' = 1 := by
    by_contra hne
    have hp : (Nat.minFac m').Prime := Nat.minFac_prime hne
    have hdvd : Nat.minFac m' ∣ n := by
      rw [hnm, hmm]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Nat.minFac_dvd m') _) _
    rcases h _ hp hdvd with h2 | h3
    · apply hm2
      rw [hmm]
      exact Dvd.dvd.mul_left (h2 ▸ Nat.minFac_dvd m') _
    · apply hm3
      exact h3 ▸ Nat.minFac_dvd m'
  exact ⟨a, b, by rw [hnm, hmm, hm1, mul_one]⟩

@[expose] def Ch6T2F1PrimeGe5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (n : ℕ), 3 ≤ n → (∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ n) →
      IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n) → Ch6Bad3 G →
        ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂],
          Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ →
            centralizer ({z} : Set G) ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G))

theorem ch6T2F1Gt9_of_leaf
    (hRemL : Ch6T2Rem) (h : Ch6T2F1PrimeGe5) : Ch6T2F1Gt9 := by
  intro G _ _ hStd hr Gs _ n hn hAt hBad z K₁ K₂ F₁ F₂ _ _ hSet
  by_cases hr5 : ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ n
  · exact h G hStd hr Gs n hn hr5 hAt hBad z K₁ K₂ F₁ F₂ hSet
  · push Not at hr5
    have h23 : ∀ r : ℕ, r.Prime → r ∣ n → r = 2 ∨ r = 3 := by
      intro r hrp hrn
      by_contra hne
      push Not at hne
      have h4 : r ≠ 4 := by
        rintro rfl
        norm_num at hrp
      have h5 : 5 ≤ r := by
        have := hrp.two_le
        omega
      exact absurd hrn (hr5 r hrp h5)
    obtain ⟨a, b, hab⟩ := t2_smooth_23 (by omega) h23
    obtain ⟨t, hRem⟩ := hRemL G hStd hr Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ hSet
    exact t2_C_eq_C₁_smooth hab hSet hRem hBad

end Leaf

end CFSG.GH74.GLS.Stage4.Rest

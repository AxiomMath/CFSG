module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Cfg
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81AutSL2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx66
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx16

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

section Generic

variable {A : Type*} [Group A] [Finite A]

theorem cen_of_card_inf {X Y : Subgroup A} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hinf : Nat.card ↥(X ⊓ Y) = 2) (hcen : Nat.card ↥(center ↥X) = 2) :
    ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) → x ∈ Y := by
  have hle : (X ⊓ Y).subgroupOf X ≤ center ↥X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (hc a a.2 x hx.2)
  have hcard : Nat.card ↥(center ↥X) ≤ Nat.card ↥((X ⊓ Y).subgroupOf X) := by
    rw [hcen, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : X ⊓ Y ≤ X)).toEquiv, hinf]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  intro x hx hxc
  have hxZ : (⟨x, hx⟩ : ↥X) ∈ center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (hxc a a.2).symm
  rw [← heq, Subgroup.mem_subgroupOf] at hxZ
  exact hxZ.2

theorem card_inf_le_two_pow_val {X : Subgroup A} (Y : Subgroup A) (hX : IsPGroup 2 ↥X) :
    Nat.card ↥(X ⊓ Y) ≤ 2 ^ (Nat.card ↥Y).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 ((hX.to_le inf_le_left : IsPGroup 2 ↥(X ⊓ Y)))
  have hdvd : Nat.card ↥(X ⊓ Y) ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le inf_le_right
  rw [hk] at hdvd ⊢
  have hY0 : Nat.card ↥Y ≠ 0 := Nat.card_pos.ne'
  exact Nat.pow_le_pow_right (by norm_num)
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hY0).1 hdvd)

theorem val_card_of_equiv_sl2 {X : Type*} [Group X] {F : Type} [Field F] [Finite F]
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) :
    (Nat.card X).factorization 2 = 3 := by
  rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  exact factorization_two_card_sl2 _ hmod

theorem prod_of_card {K₁ K₂ S : Subgroup A} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hinf : Nat.card ↥(K₁ ⊓ K₂) = 2) (hS2 : IsPGroup 2 ↥S) (hz : ∃ z, z ∈ S ∧ z ∈ K₁ ⊓ K₂ ∧ z ≠ 1)
    (hc₁ : Nat.card ↥(S ⊓ K₁) = 8) (hc₂ : Nat.card ↥(S ⊓ K₂) = 8)
    (hv₁ : (Nat.card ↥K₁).factorization 2 = 3) (hv₂ : (Nat.card ↥K₂).factorization 2 = 3) :
    S ⊓ (K₁ ⊔ K₂) = (S ⊓ K₁) ⊔ (S ⊓ K₂) := by
  have hXY : (S ⊓ K₁) ⊔ (S ⊓ K₂) ≤ S ⊓ (K₁ ⊔ K₂) :=
    sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
  refine (Subgroup.eq_of_le_of_card_ge hXY ?_).symm
  have hXc : ∀ a ∈ S ⊓ K₁, ∀ b ∈ S ⊓ K₂, a * b = b * a := fun a ha b hb => hc a ha.2 b hb.2
  have h1 := Basic.card_sup_mul_card_inf' (A := S ⊓ K₁) (B := S ⊓ K₂)
    (Basic.le_normalizer_of_commute' hXc)
  have hinf' : Nat.card ↥((S ⊓ K₁) ⊓ (S ⊓ K₂)) = 2 := by
    have hle : Nat.card ↥((S ⊓ K₁) ⊓ (S ⊓ K₂)) ≤ 2 := by
      rw [← hinf]
      exact Subgroup.card_le_of_le (inf_le_inf inf_le_right inf_le_right)
    have hge : 2 ≤ Nat.card ↥((S ⊓ K₁) ⊓ (S ⊓ K₂)) := by
      obtain ⟨z, hzS, hz12, hz1⟩ := hz
      have hne : (S ⊓ K₁) ⊓ (S ⊓ K₂) ≠ ⊥ := by
        intro hbot
        have hzm : z ∈ (S ⊓ K₁) ⊓ (S ⊓ K₂) := ⟨⟨hzS, hz12.1⟩, ⟨hzS, hz12.2⟩⟩
        rw [hbot, Subgroup.mem_bot] at hzm
        exact hz1 hzm
      have := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
      omega
    omega
  rw [hc₁, hc₂, hinf'] at h1
  have hsup32 : Nat.card ↥((S ⊓ K₁) ⊔ (S ⊓ K₂)) = 32 := by omega
  have h2 := Basic.card_sup_mul_card_inf' (A := K₁) (B := K₂) (Basic.le_normalizer_of_commute' hc)
  rw [hinf] at h2
  have hK₁0 : Nat.card ↥K₁ ≠ 0 := Nat.card_pos.ne'
  have hK₂0 : Nat.card ↥K₂ ≠ 0 := Nat.card_pos.ne'
  have hM0 : Nat.card ↥(K₁ ⊔ K₂) ≠ 0 := Nat.card_pos.ne'
  have h2fac : (Nat.factorization 2) 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  have hv : (Nat.card ↥(K₁ ⊔ K₂)).factorization 2 = 5 := by
    have h3 : (Nat.card ↥(K₁ ⊔ K₂) * 2).factorization 2 =
        (Nat.card ↥K₁ * Nat.card ↥K₂).factorization 2 := by rw [h2]
    rw [Nat.factorization_mul hM0 two_ne_zero, Nat.factorization_mul hK₁0 hK₂0] at h3
    simp only [Finsupp.add_apply, hv₁, hv₂, h2fac] at h3
    omega
  have h4 := card_inf_le_two_pow_val (K₁ ⊔ K₂) hS2
  rw [hv] at h4
  rw [hsup32]
  simpa using h4

end Generic

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Fin81

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem imgBar_le_of_le {P Q : Subgroup G} (hQC : Q ≤ Cz z) (hPQ : P ≤ Q) :
    imgBar z P ≤ imgBar z Q := by
  intro y hy
  obtain ⟨k, hk, rfl⟩ := (mem_imgBar (hPQ.trans hQC)).1 hy
  exact piC_mem_imgBar hQC (hPQ hk)

theorem piC_inj_of_mem {S : Subgroup G} (hSC : S ≤ Cz z) (hS2 : IsPGroup 2 ↥S) {x y : G}
    (hx : x ∈ S) (hy : y ∈ S) (h : piC z ⟨x, hSC hx⟩ = piC z ⟨y, hSC hy⟩) : x = y := by
  have hbot : S ⊓ Oz z = ⊥ := M.inf_eq_bot_of_pgroup_odd hS2 card_Oz_odd
  have h1 : (⟨x, hSC hx⟩ : ↥(Cz z))⁻¹ * ⟨y, hSC hy⟩ ∈ pPrimeCore 2 ↥(Cz z) := QuotientGroup.eq.1 h
  have h2 : x⁻¹ * y ∈ Oz z := ⟨_, h1, rfl⟩
  have h3 : x⁻¹ * y ∈ S ⊓ Oz z := ⟨S.mul_mem (S.inv_mem hx) hy, h2⟩
  rw [hbot, Subgroup.mem_bot] at h3
  exact inv_mul_eq_one.1 h3

omit [Finite G] in
theorem isPGroup_imgBar_of {S : Subgroup G} (hSC : S ≤ Cz z) (hS2 : IsPGroup 2 ↥S) :
    IsPGroup 2 ↥(imgBar z S) := by
  rintro ⟨y, hy⟩
  obtain ⟨s, hs, rfl⟩ := (mem_imgBar hSC).1 hy
  obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h2 : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
  show (piC z ⟨s, hSC hs⟩) ^ 2 ^ k = 1
  rw [← map_pow]
  have : (⟨s, hSC hs⟩ : ↥(Cz z)) ^ 2 ^ k = 1 := Subtype.ext h2
  rw [this, map_one]

theorem card_imgBar_eq_of_le {S P : Subgroup G} (hSC : S ≤ Cz z) (hS2 : IsPGroup 2 ↥S) (hPS : P ≤ S) :
    Nat.card ↥(imgBar z P) = Nat.card ↥P := by
  have hPC : P ≤ Cz z := hPS.trans hSC
  symm
  refine Nat.card_eq_of_bijective
    (fun x : ↥P => (⟨piC z ⟨x, hPC x.2⟩, piC_mem_imgBar hPC x.2⟩ : ↥(imgBar z P))) ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (piC_inj_of_mem hSC hS2 (hPS x.2) (hPS y.2) (congrArg Subtype.val hxy))
  · rintro ⟨y, hy⟩
    obtain ⟨k, hk, rfl⟩ := (mem_imgBar hPC).1 hy
    exact ⟨⟨k, hk⟩, rfl⟩

omit [Finite G] in
theorem zbar_comm (x : CentralizerBar z) :
    x * piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ =
      piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ * x := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  show piC z c * piC z ⟨z, _⟩ = piC z ⟨z, _⟩ * piC z c
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.1 c.2)

theorem card_inf_bar_eq_eight {S K : Subgroup G} (hSC : S ≤ Cz z) (hS2 : IsPGroup 2 ↥S) (hKC : K ≤ Cz z)
    (hP8 : Nat.card ↥(S ⊓ K) = 8) {F : Type} [Field F] [Finite F]
    (e : ↥(imgBar z K) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) :
    Nat.card ↥(imgBar z S ⊓ imgBar z K) = 8 := by
  have hv : (Nat.card ↥(imgBar z K)).factorization 2 = 3 := val_card_of_equiv_sl2 e hmod
  have hle : Nat.card ↥(imgBar z S ⊓ imgBar z K) ≤ 8 := by
    have h1 := card_inf_le_two_pow_val (imgBar z K) (isPGroup_imgBar_of hSC hS2)
    rw [hv] at h1
    simpa using h1
  have hge : 8 ≤ Nat.card ↥(imgBar z S ⊓ imgBar z K) := by
    have h3 := card_imgBar_eq_of_le hSC hS2 (inf_le_left : S ⊓ K ≤ S)
    have h4 : imgBar z (S ⊓ K) ≤ imgBar z S ⊓ imgBar z K :=
      le_inf (imgBar_le_of_le hSC inf_le_left) (imgBar_le_of_le hKC inf_le_right)
    have := Subgroup.card_le_of_le h4
    omega
  omega

namespace Fused8

theorem card_center_bar (h44 : II4_44) (hf : Fused8 G z S K₁ K₂)
    {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) : Nat.card ↥(center ↥(imgBar z K)) = 2 := by
  have hc := hf.std.comp_isPCompIn hK
  have hsl := h44 G hf.std.simple z hf.std.orderOf_z K hc (hf.std.comp_pRank hK)
  obtain ⟨e⟩ := imgBar_equiv hc
  have := Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rw [hsl.2] at this
  exact this.symm

theorem normal_imgBar_sup (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    (imgBar z K₁ ⊔ imgBar z K₂).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [← hf.map_L hII] at hn ⊢
  obtain ⟨l, hl, rfl⟩ := hn
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨c * l * c⁻¹, ?_, ?_⟩
  · have hl' : (l : G) ∈ K₁ ⊔ K₂ ⊔ Oz z := hl
    show ((c * l * c⁻¹ : ↥(Cz z)) : G) ∈ K₁ ⊔ K₂ ⊔ Oz z
    have := hf.L_norm hII c c.2 l hl'
    simpa using this
  · rw [map_mul, map_mul, map_inv]
    rfl

end Fused8

namespace Setup8

variable {W₁ W₂ U : Subgroup G} {u h : G}

theorem fusedCfg_bar (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h44 : II4_44) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS7 : Nat.card ↥S = 2 ^ 7) {F : Type} [Field F] [Finite F]
    (e₁ : ↥(imgBar z K₁) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (e₂ : ↥(imgBar z K₂) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) :
    FusedCfg (imgBar z K₁) (imgBar z K₂) (imgBar z S) F := by
  have _hS7 := hS7
  have _hodd := hodd
  have hf := hs.fused
  have hSC : S ≤ Cz z := hs.S_le_C hII
  have hS2 : IsPGroup 2 ↥S := hs.S_pgroup hII
  have hK₁C : K₁ ≤ Cz z := (hf.m4 hII).K₁_le
  have hK₂C : K₂ ≤ Cz z := (hf.m4 hII).K₂_le
  have hP8' : Nat.card ↥(Pof S K₂) = 8 := (hs.cases8_aux hII hq hrec hP8).1
  have hcomm := imgBar_comm hII hf
  have hcomm' : ∀ a ∈ imgBar z K₂, ∀ b ∈ imgBar z K₁, a * b = b * a :=
    fun a ha b hb => (hcomm b hb a ha).symm
  have hinf := imgBar_inf_card hII h44 hf
  have hinf' : Nat.card ↥(imgBar z K₂ ⊓ imgBar z K₁) = 2 := by rw [inf_comm]; exact hinf
  have hcard₁ : Nat.card ↥(imgBar z S ⊓ imgBar z K₁) = 8 :=
    card_inf_bar_eq_eight hSC hS2 hK₁C hP8 e₁ hmod
  have hcard₂ : Nat.card ↥(imgBar z S ⊓ imgBar z K₂) = 8 :=
    card_inf_bar_eq_eight hSC hS2 hK₂C hP8' e₂ hmod
  have hz := zbar_facts hII hf
  have hzS : piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ ∈ imgBar z S :=
    piC_mem_imgBar hSC (hs.z_mem_S hII)
  have hS2bar : IsPGroup 2 ↥(imgBar z S) := isPGroup_imgBar_of hSC hS2
  refine
    { e₁ := ⟨e₁⟩
      e₂ := ⟨e₂⟩
      comm := hcomm
      card_inf := hinf
      cen₁ := cen_of_card_inf hcomm hinf (hf.card_center_bar h44 (Or.inl rfl))
      cen₂ := cen_of_card_inf hcomm' hinf' (hf.card_center_bar h44 (Or.inr rfl))
      pgroup := hS2bar
      norm := ?_
      card₁ := hcard₁
      card₂ := hcard₂
      prod := prod_of_card hcomm hinf hS2bar ⟨_, hzS, hz.1, hz.2⟩ hcard₁ hcard₂
        (val_card_of_equiv_sl2 e₁ hmod) (val_card_of_equiv_sl2 e₂ hmod)
      z_ex := ?_ }
  · rw [Subgroup.normalizer_eq_top_iff.2 (hf.normal_imgBar_sup hII)]
    exact le_top
  · refine ⟨piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩, hz.1, ?_, hzS, fun s _ => zbar_comm s⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ hz.2
    rw [← map_pow]
    have : (⟨z, mem_centralizer_singleton_iff.2 rfl⟩ : ↥(Cz z)) ^ 2 = 1 :=
      Subtype.ext (by simpa [pow_two] using hs.z_sq)
    rw [this, map_one]

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8

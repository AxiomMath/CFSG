module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTenCenter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTenCL

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G] {z : G} {fr : JankoFrame G z}

namespace Hyp

omit [Finite G] in
theorem EF_le_F (fr : JankoFrame G z) : fr.EF ≤ fr.F := by
  rw [fr.EF_eq]; exact inf_le_right

omit [Finite G] in
theorem N₁_le_C₁ (fr : JankoFrame G z) : fr.M ⊔ fr.EF ≤ centralizer (fr.P₁ : Set G) :=
  sup_le (M_le_C₁ fr) ((EF_le_F fr).trans fr.F_le_centralizer)

omit [Finite G] in
theorem t_mem_normalizer_EF (fr : JankoFrame G z) : fr.t ∈ normalizer (fr.EF : Set G) := by
  have htL : fr.t ∈ fr.L := by rw [fr.L_eq]; exact subset_closure (by simp)
  rw [fr.EF_eq]
  exact inf_mem_normalizer (fr.K_le_normalizer (fr.L_le_K htL)) fr.t_mem_normalizer_F

theorem t_mem_normalizer_N₁ (fr : JankoFrame G z) :
    fr.t ∈ normalizer ((fr.M ⊔ fr.EF : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨t_mem_normalizer_M fr, t_mem_normalizer_EF fr⟩

omit [Finite G] in
theorem mem_normalizer_N₁ (fr : JankoFrame G z) {g : G} (hg : g ∈ centralizer (fr.P₁ : Set G))
    (hgE : g ∈ normalizer (fr.EF : Set G)) :
    g ∈ normalizer ((fr.M ⊔ fr.EF : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨C₁_le_normalizer_M fr hg, hgE⟩

theorem card_N₁
    (h : Hyp fr) : Nat.card (fr.M ⊔ fr.EF : Subgroup G) = 3 ^ 7 := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    ((EF_le_F fr).trans (F_le_normalizer_M fr)) ?_, card_M h, fr.card_EF]
  · norm_num
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hxM, hxE⟩
  have : x ∈ fr.M ⊓ fr.F := ⟨hxM, EF_le_F fr hxE⟩
  rwa [M_inf_F h] at this

theorem card_C₁
    (h : Hyp fr) : Nat.card (centralizer (fr.P₁ : Set G)) = 3 ^ 7 * 80 := by
  rw [centralizer_P₁_eq h, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    (F_le_normalizer_M fr) (disjoint_iff.mpr (M_inf_F h)), card_M h, fr.card_F]
  norm_num

theorem center_N₁ (h : Hyp fr) (hZM : fr.M ⊓ centralizer (fr.M : Set G) = fr.P₁) :
    (fr.M ⊔ fr.EF) ⊓ centralizer ((fr.M ⊔ fr.EF : Subgroup G) : Set G) = fr.P₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf ((P₁_le_M fr).trans le_sup_left) fun _ hp =>
    mem_centralizer_iff.mpr fun _ hn => commute_of_mem_C₁ fr (N₁_le_C₁ fr hn) hp)
  have hxCM : x ∈ centralizer (fr.M : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hx.2
  rw [← hZM]
  exact ⟨centralizer_M_le h ⟨hxCM, N₁_le_C₁ fr hx.1⟩, hxCM⟩

theorem exists_sylow_N₁
    (h : Hyp fr) (hZM : fr.M ⊓ centralizer (fr.M : Set G) = fr.P₁) :
    ∃ N₀ : Sylow 3 G, (N₀ : Subgroup G) = fr.M ⊔ fr.EF := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN₁3 : IsPGroup 3 (fr.M ⊔ fr.EF : Subgroup G) := IsPGroup.of_card (card_N₁ h)
  obtain ⟨S, hS⟩ := hN₁3.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt := lt_inf_normalizer_of_lt S.isPGroup' (lt_of_le_of_ne hS (Ne.symm hne))
  set R := (S : Subgroup G) ⊓ normalizer ((fr.M ⊔ fr.EF : Subgroup G) : Set G)
  have hR3 : IsPGroup 3 R := S.isPGroup'.to_inf_left
  have hRP₁ : R ≤ normalizer (fr.P₁ : Set G) := by
    intro x hx
    have := inf_mem_normalizer hx.2 (mem_normalizer_centralizer hx.2)
    rwa [center_N₁ h hZM] at this
  have hRC₁ : R ≤ centralizer (fr.P₁ : Set G) := by
    rw [fr.P₁_eq] at hRP₁ ⊢
    exact le_centralizer_of_isPGroup fr.orderOf_s₁ hR3 hRP₁
  have hRdvd : Nat.card R ∣ 3 ^ 7 * 80 := card_C₁ h ▸ Subgroup.card_dvd_of_le hRC₁
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR3
  rw [hk] at hRdvd
  have hk7 : 3 ^ k ∣ 3 ^ 7 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 3 80)).dvd_of_dvd_mul_right hRdvd
  have hk7' : k ≤ 7 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hk7
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [card_N₁ h, hk] at hcard
  have : 7 < k := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hcard
  omega

@[expose] def Ysub (fr : JankoFrame G z) (N : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ fr.M ∧ ∀ n ∈ N, n * x * n⁻¹ * x⁻¹ ∈ fr.P₁}
  mul_mem' {a b} ha hb := ⟨fr.M.mul_mem ha.1 hb.1, fun n hn => by
    have hp := hb.2 n hn
    have hcomm := commute_of_mem_C₁ fr (M_le_C₁ fr ha.1) hp
    have : n * (a * b) * n⁻¹ * (a * b)⁻¹ =
        (n * a * n⁻¹ * a⁻¹) * (a * (n * b * n⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [this, hcomm, mul_inv_cancel_right]
    exact fr.P₁.mul_mem (ha.2 n hn) hp⟩
  one_mem' := by
    refine ⟨fr.M.one_mem, fun n _ => ?_⟩
    rw [mul_one, mul_inv_cancel, inv_one, mul_one]
    exact fr.P₁.one_mem
  inv_mem' {a} ha := ⟨fr.M.inv_mem ha.1, fun n hn => by
    have hp := ha.2 n hn
    have hcomm := commute_of_mem_C₁ fr (M_le_C₁ fr ha.1) (fr.P₁.inv_mem hp)
    have : n * a⁻¹ * n⁻¹ * a⁻¹⁻¹ = a⁻¹ * ((n * a * n⁻¹ * a⁻¹)⁻¹ * a) := by group
    rw [this, ← hcomm, inv_mul_cancel_left]
    exact fr.P₁.inv_mem hp⟩

omit [Finite G] in
theorem mem_Ysub {N : Subgroup G} {x : G} :
    x ∈ Ysub fr N ↔ x ∈ fr.M ∧ ∀ n ∈ N, n * x * n⁻¹ * x⁻¹ ∈ fr.P₁ :=
  Iff.rfl

theorem mem_normalizer_Ysub {N : Subgroup G} {g : G} (hgM : g ∈ normalizer (fr.M : Set G))
    (hgN : g ∈ normalizer (N : Set G)) (hgP : g ∈ normalizer (fr.P₁ : Set G)) :
    g ∈ normalizer (Ysub fr N : Set G) :=
  Walter.J1.mem_normalizer_of_conj_mem fun x hx => mem_Ysub.mpr
    ⟨conj_mem_of_le_normalizer le_rfl hgM hx.1, fun n hn => by
      have hn' : g⁻¹ * n * g ∈ N := by
        have := conj_mem_of_le_normalizer le_rfl (inv_mem hgN) hn
        rwa [inv_inv] at this
      have : n * (g * x * g⁻¹) * n⁻¹ * (g * x * g⁻¹)⁻¹ =
          g * ((g⁻¹ * n * g) * x * (g⁻¹ * n * g)⁻¹ * x⁻¹) * g⁻¹ := by group
      rw [this]
      exact conj_mem_of_le_normalizer le_rfl hgP (hx.2 _ hn')⟩

theorem exists_mem_M_central (h : Hyp fr) {N : Subgroup G} (hN : IsPGroup 3 N)
    (hMN : fr.M ≤ N) (hNC : N ≤ centralizer (fr.P₁ : Set G)) :
    ∃ m ∈ fr.M, m ∉ fr.P₁ ∧ ∀ n ∈ N, n * m * n⁻¹ * m⁻¹ ∈ fr.P₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P' := fr.P₁.subgroupOf N
  have : P'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((P₁_le_M fr).trans hMN)).mpr (hNC.trans (C₁_le_normalizer_P₁ fr))
  have hQ3 : IsPGroup 3 (N ⧸ P') := hN.to_quotient P'
  have : Group.IsNilpotent (N ⧸ P') := hQ3.isNilpotent
  have hM'n : (fr.M.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMN).mpr (hNC.trans (C₁_le_normalizer_M fr))
  set H := (fr.M.subgroupOf N).map (QuotientGroup.mk' P')
  have : H.Normal := hM'n.map _ (QuotientGroup.mk'_surjective P')
  obtain ⟨m₀, hm₀M, hm₀P⟩ : ∃ m ∈ fr.M, m ∉ fr.P₁ := by
    by_contra hcon
    push Not at hcon
    exact M_ne_P₁ h (le_antisymm hcon (P₁_le_M fr))
  have hH : H ≠ ⊥ := by
    intro hH
    have hmem : QuotientGroup.mk' P' ⟨m₀, hMN hm₀M⟩ ∈ H := ⟨⟨m₀, hMN hm₀M⟩, hm₀M, rfl⟩
    rw [hH, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hm₀P hmem
  obtain ⟨⟨x, hxH, hxZ⟩, hx1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hH)
  obtain ⟨m, hmM, rfl⟩ := hxH
  refine ⟨m, hmM, fun hmP => hx1 (Subtype.ext ?_), fun n hn => ?_⟩
  · change QuotientGroup.mk' P' m = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmP
  · have hc := Subgroup.mem_center_iff.mp hxZ (QuotientGroup.mk' P' ⟨n, hn⟩)
    have : ((⟨n, hn⟩ : N) * m * (⟨n, hn⟩ : N)⁻¹ * m⁻¹ : N) ∈ P' := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      simp only [QuotientGroup.mk'_apply] at hc
      rw [hc]
      group
    exact this

omit [Finite G] in
theorem z_mem_normalizer_EF (fr : JankoFrame G z) : z ∈ normalizer (fr.EF : Set G) :=
  Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun _ he =>
    mem_centralizer_singleton_iff.mp (fr.F_le (EF_le_F fr he)))

omit [Finite G] in
theorem ℓ_mem_normalizer_EF (fr : JankoFrame G z) : fr.ℓ ∈ normalizer (fr.EF : Set G) := by
  have hℓ : fr.ℓ ∈ fr.EF ⊔ fr.L₁ := mem_sup_right (by rw [fr.L₁_eq]; exact mem_zpowers _)
  rw [← fr.normalizer_EF] at hℓ
  exact hℓ.1

theorem exists_q (h : Hyp fr) :
    ∃ q ∈ fr.At, q ≠ 1 ∧ ∀ n ∈ fr.M ⊔ fr.EF, n * q * n⁻¹ * q⁻¹ ∈ fr.P₁ := by
  set Y := Ysub fr (fr.M ⊔ fr.EF)
  have hYM : Y ≤ fr.M := fun _ hx => hx.1
  have hP₁Y : fr.P₁ ≤ Y := fun p hp => ⟨P₁_le_M fr hp, fun n hn => by
    rw [commute_of_mem_C₁ fr (N₁_le_C₁ fr hn) hp, mul_inv_cancel_right, mul_inv_cancel]
    exact fr.P₁.one_mem⟩
  have hN₁3 : IsPGroup 3 (fr.M ⊔ fr.EF : Subgroup G) := IsPGroup.of_card (card_N₁ h)
  obtain ⟨m, hmM, hmP, hm⟩ := exists_mem_M_central h hN₁3 le_sup_left (N₁_le_C₁ fr)
  have hnorm : ∀ g ∈ centralizer (fr.P₁ : Set G), g ∈ normalizer (fr.EF : Set G) →
      g ∈ normalizer (Y : Set G) := fun g hg hgE =>
    mem_normalizer_Ysub (C₁_le_normalizer_M fr hg) (mem_normalizer_N₁ fr hg hgE)
      (C₁_le_normalizer_P₁ fr hg)
  have key := card_eq_of_le_M h hP₁Y hYM
    (mem_normalizer_Ysub (t_mem_normalizer_M fr) (t_mem_normalizer_N₁ fr)
      (t_mem_normalizer_P₁ fr)) (hnorm z (z_mem_C₁ fr) (z_mem_normalizer_EF fr))
  rw [card_inf_tz_eq fr (hnorm _ (pow_mem (ℓ_mem_C₁ fr) 2)
    (pow_mem (ℓ_mem_normalizer_EF fr) 2))] at key
  by_contra hcon
  have hbot : Y ⊓ centralizer ({fr.t} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    by_contra hx1
    exact hcon ⟨x, ⟨hx.1.1, hx.2⟩, hx1, hx.1.2⟩
  rw [hbot, card_bot] at key
  have hY : Y = fr.P₁ :=
    (Subgroup.eq_of_le_of_card_ge hP₁Y (by rw [key, card_P₁])).symm
  exact hmP (hY ▸ (⟨hmM, hm⟩ : m ∈ Y))

omit [Finite G] in
theorem card_centralizer_q (hZM : fr.M ⊓ centralizer (fr.M : Set G) = fr.P₁)
    {q : G} (hqA : q ∈ fr.At) (hq1 : q ≠ 1)
    (hqY : ∀ n ∈ fr.M ⊔ fr.EF, n * q * n⁻¹ * q⁻¹ ∈ fr.P₁) :
    Nat.card ((fr.M ⊔ fr.EF) ⊓ centralizer ({q} : Set G) : Subgroup G) * 3 =
      Nat.card (fr.M ⊔ fr.EF : Subgroup G) := by
  set N₁ := fr.M ⊔ fr.EF
  let ψ : N₁ →* G :=
    { toFun := fun n => (n : G) * q * (n : G)⁻¹ * q⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have hpb := hqY b b.2
        have h1 := commute_of_mem_C₁ fr (N₁_le_C₁ fr a.2) hpb
        have h2 := commute_of_mem_C₁ fr (P₁_le_C₁ fr (hqY a a.2)) hpb
        calc ((a * b : N₁) : G) * q * ((a * b : N₁) : G)⁻¹ * q⁻¹ =
            (a : G) * ((b : G) * q * (b : G)⁻¹ * q⁻¹) * q * (a : G)⁻¹ * q⁻¹ := by
              simp only [Subgroup.coe_mul]; group
          _ = ((b : G) * q * (b : G)⁻¹ * q⁻¹) * a * q * (a : G)⁻¹ * q⁻¹ := by rw [h1]
          _ = ((b : G) * q * (b : G)⁻¹ * q⁻¹) * ((a : G) * q * (a : G)⁻¹ * q⁻¹) := by group
          _ = _ := h2.symm }
  have hker : ψ.ker = (centralizer ({q} : Set G)).subgroupOf N₁ := by
    ext n
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_singleton_iff]
    change (n : G) * q * (n : G)⁻¹ * q⁻¹ = 1 ↔ (n : G) * q = q * n
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  have hrange : Nat.card ψ.range = 3 := by
    have hle : ψ.range ≤ fr.P₁ := by rintro _ ⟨n, rfl⟩; exact hqY n n.2
    have hdvd : Nat.card ψ.range ∣ 3 := card_P₁ fr ▸ Subgroup.card_dvd_of_le hle
    have hne : ψ.range ≠ ⊥ := by
      have hqZ : q ∉ fr.M ⊓ centralizer (fr.M : Set G) := by
        rw [hZM]
        intro hqP
        have : q ∈ fr.P₁ ⊓ centralizer ({fr.t} : Set G) := ⟨hqP, hqA.2⟩
        rw [P₁_inf_centralizer_t, mem_bot] at this
        exact hq1 this
      have hex : ¬ ∀ m ∈ fr.M, m * q = q * m := fun hall =>
        hqZ ⟨hqA.1, mem_centralizer_iff.mpr hall⟩
      push Not at hex
      obtain ⟨m, hmM, hmq⟩ := hex
      intro hbot
      have h1 : ψ ⟨m, le_sup_left (a := fr.M) hmM⟩ ∈ ψ.range := ⟨_, rfl⟩
      rw [hbot, mem_bot] at h1
      change m * q * m⁻¹ * q⁻¹ = 1 at h1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact hmq h1
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hne
    · exact h3
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker] at hcard
  have hsub : Nat.card ((centralizer ({q} : Set G)).subgroupOf N₁) =
      Nat.card (N₁ ⊓ centralizer ({q} : Set G) : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective N₁.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [hsub] at hcard
  rw [hcard, mul_comm]

theorem M_comm
    (h : Hyp fr) : ∀ a ∈ fr.M, ∀ b ∈ fr.M, a * b = b * a := by
  by_contra hnc
  have hZM := center_M_eq h hnc
  obtain ⟨N₀, hN₀⟩ := exists_sylow_N₁ h hZM
  obtain ⟨q, hqA, hq1, hqY⟩ := exists_q h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq3 : orderOf q = 3 := orderOf_eq_prime (pow_three_of_mem_At h hqA) hq1
  have hN₁3 : IsPGroup 3 (fr.M ⊔ fr.EF : Subgroup G) := IsPGroup.of_card (card_N₁ h)
  have hqt : fr.t ∈ centralizer ({q} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hqA.2).symm
  exact false_of_sylow h N₀ fr.s₁ (IsConj.refl _) (by rw [hN₀, center_N₁ h hZM, fr.P₁_eq])
    (zpowers q) ((zpowers_le).mpr hqA) (by rw [Nat.card_zpowers, hq3])
    ((fr.M ⊔ fr.EF) ⊓ centralizer ({q} : Set G)) hN₁3.to_inf_left
    (inf_le_left.trans ((N₁_le_C₁ fr).trans (C₁_le_normalizer_P₁ fr)))
    (inf_le_right.trans ((centralizer_singleton_le q).trans
      (Subgroup.centralizer_le_normalizer _)))
    (inf_mem_normalizer (t_mem_normalizer_N₁ fr) (Subgroup.le_normalizer hqt))
    (by rw [hN₀]; exact card_centralizer_q hZM hqA hq1 hqY)

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen

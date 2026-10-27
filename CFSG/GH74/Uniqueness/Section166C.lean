module

public import CFSG.GH74.Uniqueness.Section166A
public import CFSG.GH74.Uniqueness.Section12BenderDict

public section

namespace CFSG.GH74.Uniqueness.Cor166

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem isPGroup_zpowers_of_mul_self {G : Type*} [Group G] {a : G} (ha : a * a = 1) :
    IsPGroup 2 (zpowers a) := by
  have hdvd : orderOf a ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq, ha])
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem exists_conj_mem_of_isSylowOf {T K : Subgroup X} (hT : ABGLocalTools.IsSylowOf 2 T K)
    {y : X} (hyK : y ∈ K) (hy : y * y = 1) : ∃ k ∈ K, k * y * k⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', rfl⟩ := hT
  have hp : IsPGroup 2 (zpowers (⟨y, hyK⟩ : ↥K)) :=
    isPGroup_zpowers_of_mul_self (Subtype.ext hy)
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥K R T'
  refine ⟨k, k.2, ?_⟩
  have hyR : y ∈ (R : Subgroup ↥K).map K.subtype := ⟨⟨y, hyK⟩, hR (mem_zpowers _), rfl⟩
  have := mem_map_smul R k hyR
  rwa [hk] at this

theorem exists_central_involution {S : Subgroup X} (hS : IsPGroup 2 S) {a : X} (ha : a ∈ S)
    (ha2 : orderOf a = 2) : ∃ c ∈ S, orderOf c = 2 ∧ ∀ x ∈ S, x * c = c * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥S := by
    refine ⟨⟨⟨a, ha⟩, 1, fun h => ?_⟩⟩
    have h1 : a = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have hcent : Nontrivial (center ↥S) := hS.center_nontrivial
  have h2 : 2 ∣ Nat.card (center ↥S) := by
    rcases (hS.to_subgroup (center ↥S)).card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr hcent).ne'
    · exact h
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨((c : ↥S) : X), (c : ↥S).2, ?_, fun x hx => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  · have := Subgroup.mem_center_iff.mp c.2 ⟨x, hx⟩
    exact congrArg Subtype.val this

theorem eq_of_isPGroup_of_comm {S : Subgroup X} (hS : IsPGroup 2 S)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b)
    {a b : X} (ha : a ∈ S) (hb : b ∈ S) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : a = b := by
  obtain ⟨c, hcS, hc2, hcc⟩ := exists_central_involution hS ha ha2
  rw [hcomm a ha c hcS ha2 hc2 (hcc a ha), hcomm b hb c hcS hb2 hc2 (hcc b hb)]

theorem comm_of_isPGroup_of_comm {S : Subgroup X} (hS : IsPGroup 2 S)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b)
    {a : X} (ha : a ∈ S) (ha2 : orderOf a = 2) : ∀ x ∈ S, x * a = a * x := by
  obtain ⟨c, hcS, hc2, hcc⟩ := exists_central_involution hS ha ha2
  rw [hcomm a ha c hcS ha2 hc2 (hcc a ha)]
  exact hcc

theorem eq_of_comm_of_pRank {A : Subgroup X} (hA : Open.pRank 2 A = 1) :
    ∀ a ∈ A, ∀ b ∈ A, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b := by
  intro a ha b hb ha2 hb2 hab
  by_contra hne
  have := two_le_pRank_of_commuting ha2 hb2 ha hb hne hab
  omega

omit [Finite X] in
theorem orderOf_conj' (g y : X) : orderOf (g * y * g⁻¹) = orderOf y := by
  have h : SemiconjBy g y (g * y * g⁻¹) := by
    unfold SemiconjBy
    group
  exact (SemiconjBy.orderOf_eq _ h).symm

theorem exists_conj_of_invol_benderSub {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) {a b : X} (ha : a ∈ F) (hb : b ∈ F) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) : ∃ h ∈ F, h * a * h⁻¹ = b := by
  have hodd := benderSub_odd_card_center hB
  have hsq : ∀ x : ↥F, orderOf x = 2 → x * x = 1 := fun x hx => by
    have := pow_orderOf_eq_one x
    rwa [hx, sq] at this
  have hne : ∀ x : ↥F, orderOf x = 2 → (x : ↥F ⧸ center ↥F) ≠ 1 := by
    intro x hx h1
    have hxc : x ∈ center ↥F := (QuotientGroup.eq_one_iff x).mp h1
    have h2 : orderOf (⟨x, hxc⟩ : center ↥F) ∣ Nat.card (center ↥F) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hx] at h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  let a' : ↥F := ⟨a, ha⟩
  let b' : ↥F := ⟨b, hb⟩
  have ha'2 : orderOf a' = 2 := by rw [Subgroup.orderOf_mk]; exact ha2
  have hb'2 : orderOf b' = 2 := by rw [Subgroup.orderOf_mk]; exact hb2
  have hconj := hB.bender.lemma_3_4_a (u := (a' : ↥F ⧸ center ↥F)) (v := (b' : ↥F ⧸ center ↥F))
    (by rw [← QuotientGroup.mk_mul, hsq a' ha'2]; rfl) (hne a' ha'2)
    (by rw [← QuotientGroup.mk_mul, hsq b' hb'2]; rfl) (hne b' hb'2)
  obtain ⟨h, hh⟩ := exists_conj_of_isConj_mk hodd (hsq a' ha'2) (hsq b' hb'2) hconj
  exact ⟨h, h.2, congrArg Subtype.val hh⟩

section Conf

variable (c : Conf16 Z M)

theorem exists_conj_of_invol_D (h165 : Prop165Stmt Z M) {w : X} (hw : w ∈ c.D)
    (hw2 : orderOf w = 2) : ∃ d ∈ c.D, w = d⁻¹ * c.u * d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := eq_of_comm_of_pRank (h165 c)
  obtain ⟨Su, hSu, huSu⟩ := exists_isSylowOf_ge_of_le (Subgroup.zpowers_le.mpr c.hu)
    (isPGroup_zpowers_of_mul_self (u_mul_self c))
  obtain ⟨Sw, hSw, hwSw⟩ := exists_isSylowOf_ge_of_le (Subgroup.zpowers_le.mpr hw)
    (isPGroup_zpowers_of_mul_self (by
      have := pow_orderOf_eq_one w
      rwa [hw2, sq] at this))
  obtain ⟨d, hdD, hd⟩ := exists_conj_of_isSylowOf hSu hSw
  have hmem : d⁻¹ * c.u * d ∈ Sw := by
    rw [← hd, mem_conjugate_iff]
    have : d * (d⁻¹ * c.u * d) * d⁻¹ = c.u := by group
    rw [this]
    exact huSu (mem_zpowers _)
  refine ⟨d, hdD, eq_of_isPGroup_of_comm hSw.isPGroup
    (fun a ha b hb => hcomm a (hSw.le ha) b (hSw.le hb)) (hwSw (mem_zpowers _)) hmem hw2 ?_⟩
  have := orderOf_conj' d⁻¹ c.u
  rw [inv_inv] at this
  rw [this, c.hu2]

theorem odd_card_conj_u (h165 : Prop165Stmt Z M) :
    Odd (Nat.card {x : X // ∃ d ∈ c.D, x = d⁻¹ * c.u * d}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := eq_of_comm_of_pRank (h165 c)
  obtain ⟨Su, hSu, huSu⟩ := exists_isSylowOf_ge_of_le (Subgroup.zpowers_le.mpr c.hu)
    (isPGroup_zpowers_of_mul_self (u_mul_self c))
  have hSC : Su ≤ centralizer ({c.u} : Set X) ⊓ c.D := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hSu.le hx⟩
    exact comm_of_isPGroup_of_comm hSu.isPGroup
      (fun a ha b hb => hcomm a (hSu.le ha) b (hSu.le hb)) (huSu (mem_zpowers _)) c.hu2 x hx
  rw [card_conj_orbit, ← Subgroup.inf_relIndex_right]
  have h1 := Subgroup.relIndex_mul_relIndex Su (centralizer ({c.u} : Set X) ⊓ c.D) c.D hSC
    inf_le_right
  have h2 := (ABGLocalTools.isSylowOf_iff.mp hSu).2.2
  rw [← h1] at h2
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => h2 (dvd_mul_of_dvd_right h _))

end Conf

theorem exists_conj_commute_of_odd' {D : Subgroup X} {u y : X}
    (hodd : Odd (Nat.card {x : X // ∃ d ∈ D, x = d⁻¹ * u * d})) (hy2 : y * y = 1)
    (hmem : ∀ d ∈ D, ∃ d' ∈ D, y * (d⁻¹ * u * d) * y⁻¹ = d'⁻¹ * u * d') :
    ∃ d ∈ D, y * (d⁻¹ * u * d) = (d⁻¹ * u * d) * y := by
  classical
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hmem' : ∀ x : {x : X // ∃ d ∈ D, x = d⁻¹ * u * d},
      ∃ d ∈ D, y * (x : X) * y⁻¹ = d⁻¹ * u * d := by
    rintro ⟨x, d, hd, rfl⟩
    exact hmem d hd
  let f : {x : X // ∃ d ∈ D, x = d⁻¹ * u * d} → {x : X // ∃ d ∈ D, x = d⁻¹ * u * d} :=
    fun x => ⟨y * x * y⁻¹, hmem' x⟩
  have hf : Function.Involutive f := by
    intro x
    apply Subtype.ext
    change y * (y * (x : X) * y⁻¹) * y⁻¹ = x
    rw [hyi]
    calc y * (y * (x : X) * y) * y = (y * y) * x * (y * y) := by group
      _ = x := by rw [hy2]; group
  have : Fintype {x : X // ∃ d ∈ D, x = d⁻¹ * u * d} := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hndvd : ¬ 2 ∣ Fintype.card {x : X // ∃ d ∈ D, x = d⁻¹ * u * d} := by
    rw [Fintype.card_eq_nat_card]
    exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hσ : (hf.toPerm f) ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    exact Equiv.ext fun x => hf x
  obtain ⟨⟨x, d, hd, rfl⟩, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hndvd hσ
  refine ⟨d, hd, ?_⟩
  have hx' : y * (d⁻¹ * u * d) * y⁻¹ = d⁻¹ * u * d := congrArg Subtype.val hx
  calc y * (d⁻¹ * u * d) = y * (d⁻¹ * u * d) * y⁻¹ * y := by group
    _ = (d⁻¹ * u * d) * y := by rw [hx']

theorem exists_conj_comm_ne
    (S : ZDSetup X Z M) {u : X}
    (hu2 : orderOf u = 2) : ∃ g : X, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) ∧ g * u * g⁻¹ ≠ u := by
  by_contra hcon
  push Not at hcon
  have hsimp : IsSimpleGroup X := S.theorem1_unconditional.1
  have : Fintype X := Fintype.ofFinite X
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, sq] at this
  obtain ⟨N, hN, hNodd, hNu⟩ := CFSG.ZStar.glauberman_zStar X u hu1 huu hcon
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · have hcent : u ∈ center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := hNu g
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
      calc g * u = g * u * g⁻¹ * g := by group
        _ = u * g := by rw [h1]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with hc | hc
    · rw [hc, Subgroup.mem_bot] at hcent
      exact hu1 hcent
    · apply S.exists_not_commute
      intro a b
      have hb : b ∈ center X := by rw [hc]; exact Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.mp hb a)
  · have h1 : Odd (Nat.card X) := by
      rw [← Subgroup.card_top, ← htop]
      exact hNodd
    have h2 : 2 ∣ Nat.card X := hu2 ▸ orderOf_dvd_natCard u
    exact (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr h2)

section Main

theorem exists_conj_uz_of_mul_mem_Q
    (S : ZDSetup X Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) {y : X} (hyT1 : y ∈ c.T1) (hy2 : y * y = 1)
    (hyQ : y * c.u ∈ c.Q) (hyu : y * c.u ≠ 1) : ∃ h : X, h * y * h⁻¹ = c.u * c.z := by
  have hyB : y * c.u = c.u * y := comm_u_of_mem_B c (T1_le_B c hyT1)
  have hq2 : orderOf (y * c.u) = 2 := by
    refine orderOf_eq_prime ?_ hyu
    rw [sq]
    calc y * c.u * (y * c.u) = y * (c.u * y) * c.u := by group
      _ = y * (y * c.u) * c.u := by rw [hyB]
      _ = (y * y) * (c.u * c.u) := by group
      _ = 1 := by rw [hy2, u_mul_self c, one_mul]
  have hz2 : orderOf c.z = 2 := S.invariant.1 c.z c.hz
  obtain ⟨h, hhF, hh⟩ := exists_conj_of_invol_benderSub hB (Q_le_B0 c hyQ) (z_mem_B0 c) hq2 hz2
  refine ⟨h, ?_⟩
  have hhu : h * c.u * h⁻¹ = c.u := by
    rw [comm_u_of_mem_B c (B0_le_B c hhF)]
    group
  have hui := u_inv c
  calc h * y * h⁻¹ = (h * (y * c.u) * h⁻¹) * (h * c.u⁻¹ * h⁻¹) := by group
    _ = c.z * c.u := by rw [hh, hui, hhu]
    _ = c.u * c.z := z_comm_u c

theorem cor166c_conj
    (S : ZDSetup X Z M) (c : Conf16 Z M) (h163 : Lemma163Stmt Z M)
    (h164 : Lemma164Stmt Z M) (h165 : Prop165Stmt Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) : IsConj c.u (c.u * c.z) := by
  by_contra hcon
  obtain ⟨g, hgc, hgne⟩ := exists_conj_comm_ne S c.hu2
  set y := g * c.u * g⁻¹ with hydef
  have hyB : y ∈ c.B := Subgroup.mem_centralizer_singleton_iff.mpr hgc
  have hy2 : y * y = 1 := by
    rw [hydef]
    calc g * c.u * g⁻¹ * (g * c.u * g⁻¹) = g * (c.u * c.u) * g⁻¹ := by group
      _ = 1 := by rw [u_mul_self c]; group
  have hyu : IsConj c.u y := isConj_iff.mpr ⟨g, rfl⟩
  obtain ⟨b, hbB, hbT⟩ := exists_conj_mem_of_isSylowOf (h163 c).2.2.1 hyB hy2
  set y' := b * y * b⁻¹ with hy'def
  have hy'2 : y' * y' = 1 := by
    rw [hy'def]
    calc b * y * b⁻¹ * (b * y * b⁻¹) = b * (y * y) * b⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hy'u : IsConj c.u y' := hyu.trans (isConj_iff.mpr ⟨b, rfl⟩)
  have hy'ord : orderOf y' = 2 := by
    rw [hy'def, hydef, orderOf_conj', orderOf_conj', c.hu2]
  rcases mem_or_mul_mem_Q S c h164 h165 hB hbT hy'2 with hQ | hQ
  · exact u_not_mem_Z c S (S.invariant.isConj_mem (hB.invol y' (Q_le_B0 c hQ) hy'ord) hy'u)
  · by_cases hq1 : y' * c.u = 1
    · apply hgne
      have hy'eq : y' = c.u := by
        calc y' = y' * c.u * c.u := by rw [mul_assoc, u_mul_self c, mul_one]
          _ = c.u := by rw [hq1, one_mul]
      have hbu : b * c.u * b⁻¹ = c.u := by
        rw [comm_u_of_mem_B c hbB]
        group
      calc y = b⁻¹ * y' * b := by rw [hy'def]; group
        _ = b⁻¹ * (b * c.u * b⁻¹) * b := by rw [hy'eq, hbu]
        _ = c.u := by group
    · obtain ⟨h, hh⟩ := exists_conj_uz_of_mul_mem_Q S c hB hbT hy'2 hQ hq1
      exact hcon (hy'u.trans (isConj_iff.mpr ⟨h, hh⟩))

theorem cor166c_invol
    (S : ZDSetup X Z M) (c : Conf16 Z M) (h163 : Lemma163Stmt Z M)
    (h164 : Lemma164Stmt Z M) (h165 : Prop165Stmt Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) {y : X} (hy2 : orderOf y = 2) :
    IsConj c.z y ∨ IsConj c.u y := by
  have hsimp : IsSimpleGroup X := S.theorem1_unconditional.1
  have hyy : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2, sq] at this
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  obtain ⟨γ, hγ, hyγ⟩ : ∃ γ ∈ omega M, y ∉ γ := by
    by_contra hall
    push Not at hall
    have hcore : y ∈ M.normalCore := Subgroup.mem_carrier.mp fun b => by
      have := hall (conjugate M b) ⟨b, rfl⟩
      rwa [mem_conjugate_iff] at this
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M.normalCore with h | h
    · rw [h, Subgroup.mem_bot] at hcore
      exact hy1 hcore
    · exact S.prodDisc.1 (top_le_iff.mp (by rw [← h]; exact M.normalCore_le))
  set δ := conjugate γ y with hδdef
  have hδ : δ ∈ omega M := conjugate_mem_omega hγ y
  have hγδ : γ ≠ δ := fun h => hyγ ((S.prodDisc.conjugate_eq_iff_mem hγ).mp h.symm)
  obtain ⟨g, hg1, hg2⟩ := S.theorem4.1 γ hγ δ hδ hγδ M (self_mem_omega M) (conjugate M c.t)
    ⟨c.t, rfl⟩ (conjugate_ne_self S c.htM)
  set y₁ := g⁻¹ * y * g with hy₁def
  have hy₁M : conjugate M y₁ = conjugate M c.t := by
    calc conjugate M y₁ = conjugate (conjugate γ g) y₁ := by rw [hg1]
      _ = conjugate δ g := by
        rw [conjugate_conjugate, hδdef, conjugate_conjugate]
        congr 1
        rw [hy₁def]
        group
      _ = conjugate M c.t := hg2
  have hy₁Mt : conjugate (conjugate M c.t) y₁ = M := by
    calc conjugate (conjugate M c.t) y₁ = conjugate (conjugate δ g) y₁ := by rw [hg2]
      _ = conjugate γ g := by
        rw [conjugate_conjugate, hδdef, conjugate_conjugate]
        congr 1
        rw [hy₁def]
        calc y * (g * (g⁻¹ * y * g)) = (y * y) * g := by group
          _ = g := by rw [hyy, one_mul]
      _ = M := hg1
  have hy₁N : y₁ ∈ normalizer (c.D : Set X) := by
    rw [← conjugate_eq_iff_mem_normalizer]
    change conjugate (M ⊓ conjugate M c.t) y₁ = M ⊓ conjugate M c.t
    rw [conjugate_inf, hy₁M, hy₁Mt, inf_comm]
  have hy₁2 : y₁ * y₁ = 1 := by
    rw [hy₁def]
    calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
      _ = 1 := by rw [hyy]; group
  obtain ⟨d, hdD, hdcomm⟩ := exists_conj_commute_of_odd' (odd_card_conj_u c h165) hy₁2
    (fun d hd => by
      have hmem : y₁ * (d⁻¹ * c.u * d) * y₁⁻¹ ∈ c.D :=
        (Subgroup.mem_normalizer_iff.mp hy₁N _).mp
          (c.D.mul_mem (c.D.mul_mem (c.D.inv_mem hd) c.hu) hd)
      have hord : orderOf (y₁ * (d⁻¹ * c.u * d) * y₁⁻¹) = 2 := by
        rw [orderOf_conj', show d⁻¹ * c.u * d = d⁻¹ * c.u * d⁻¹⁻¹ by rw [inv_inv], orderOf_conj',
          c.hu2]
      obtain ⟨d', hd', h⟩ := exists_conj_of_invol_D c h165 hmem hord
      exact ⟨d', hd', h⟩)
  set y₂ := d * y₁ * d⁻¹ with hy₂def
  have hy₂B : y₂ ∈ c.B := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc c.u * y₂ = d * ((d⁻¹ * c.u * d) * y₁) * d⁻¹ := by rw [hy₂def]; group
      _ = d * (y₁ * (d⁻¹ * c.u * d)) * d⁻¹ := by rw [← hdcomm]
      _ = y₂ * c.u := by rw [hy₂def]; group
  have hy₂2 : y₂ * y₂ = 1 := by
    rw [hy₂def]
    calc d * y₁ * d⁻¹ * (d * y₁ * d⁻¹) = d * (y₁ * y₁) * d⁻¹ := by group
      _ = 1 := by rw [hy₁2]; group
  obtain ⟨b, -, hbT⟩ := exists_conj_mem_of_isSylowOf (h163 c).2.2.1 hy₂B hy₂2
  set y₃ := b * y₂ * b⁻¹ with hy₃def
  have hyy₃ : IsConj y y₃ := by
    refine isConj_iff.mpr ⟨b * d * g⁻¹, ?_⟩
    rw [hy₃def, hy₂def, hy₁def]
    group
  have hy₃2 : y₃ * y₃ = 1 := by
    rw [hy₃def]
    calc b * y₂ * b⁻¹ * (b * y₂ * b⁻¹) = b * (y₂ * y₂) * b⁻¹ := by group
      _ = 1 := by rw [hy₂2]; group
  have hy₃ord : orderOf y₃ = 2 := by
    rw [hy₃def, hy₂def, hy₁def, orderOf_conj', orderOf_conj',
      show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj', hy2]
  rcases mem_or_mul_mem_Q S c h164 h165 hB hbT hy₃2 with hQ | hQ
  · left
    have hy₃Z : y₃ ∈ Z := hB.invol y₃ (Q_le_B0 c hQ) hy₃ord
    obtain ⟨z₀, hz₀, hZeq⟩ := S.theorem1_unconditional.2.2.1
    have hz₀z : IsConj z₀ c.z := by
      have : c.z ∈ {y : X | IsConj z₀ y} := hZeq ▸ c.hz
      exact this
    have hz₀y₃ : IsConj z₀ y₃ := by
      have : y₃ ∈ {y : X | IsConj z₀ y} := hZeq ▸ hy₃Z
      exact this
    exact (hz₀z.symm.trans hz₀y₃).trans hyy₃.symm
  · right
    by_cases hq1 : y₃ * c.u = 1
    · have hy₃eq : y₃ = c.u := by
        calc y₃ = y₃ * c.u * c.u := by rw [mul_assoc, u_mul_self c, mul_one]
          _ = c.u := by rw [hq1, one_mul]
      rw [← hy₃eq]
      exact hyy₃.symm
    · obtain ⟨h, hh⟩ := exists_conj_uz_of_mul_mem_Q S c hB hbT hy₃2 hQ hq1
      exact ((cor166c_conj S c h163 h164 h165 hB).trans (isConj_iff.mpr ⟨h, hh⟩).symm).trans
        hyy₃.symm

end Main

end CFSG.GH74.Uniqueness.Cor166

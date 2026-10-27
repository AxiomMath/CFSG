module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KstLift
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KstPerm2

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N.P4 Equiv

variable {Γ : Type*} [Group Γ] [Finite Γ] {U K : Subgroup Γ} {x v t : Γ}

namespace KSetup

theorem part1 (h : KSetup U K x v t) : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U := by
  intro k hk u hu
  obtain ⟨f, rfl⟩ := h.evG_surj (mem_sup_left hu)
  have hf : ∑ i, f i = 0 := (h.evG_mem_U_iff f).1 hu
  rw [h.conj_evG hk, h.evG_mem_U_iff, Equiv.sum_comp (h.permOf hk).symm f]
  exact hf

theorem K_le_normalizer (h : KSetup U K x v t) : K ≤ normalizer (U : Set Γ) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro u
  refine ⟨h.part1 k hk u, fun hku => ?_⟩
  have := h.part1 k⁻¹ (inv_mem hk) _ hku
  simpa [mul_assoc] using this

theorem part6 (h : KSetup U K x v t) :
    ∀ a ∈ U, ∀ b ∈ U, a ≠ 1 → b ≠ 1 → ∃ k ∈ K, k * a * k⁻¹ = b := by
  intro a ha b hb ha1 hb1
  obtain ⟨p, q, hpq, rfl⟩ := h.exists_pair ha ha1
  obtain ⟨p', q', hpq', rfl⟩ := h.exists_pair hb hb1
  obtain ⟨g, ⟨k, rfl⟩, hgp, hgq⟩ := h.sixData.two_trans p p' q q' hpq hpq'
  refine ⟨k, k.2, ?_⟩
  have e1 := h.dd_rho k p
  have e2 := h.dd_rho k q
  rw [hgp] at e1
  rw [hgq] at e2
  calc (k : Γ) * (h.dd p * h.dd q) * (k : Γ)⁻¹
      = ((k : Γ) * h.dd p * (k : Γ)⁻¹) * ((k : Γ) * h.dd q * (k : Γ)⁻¹) := by group
    _ = h.dd p' * h.dd q' := by rw [← e1, ← e2]

theorem invol_perm (h : KSetup U K x v t) {y : Γ} (hy : y ∈ K) (hy2 : y * y = 1)
    (hy0 : y ∉ U ⊔ zpowers t) :
    h.permOf hy * h.permOf hy = 1 ∧ h.permOf hy ≠ 1 ∧
      (fixCount (h.permOf hy) = 0 ∨ fixCount (h.permOf hy) = 2) := by
  have e : h.permOf hy = h.rho ⟨y, hy⟩ := rfl
  have h1 : h.rho ⟨y, hy⟩ * h.rho ⟨y, hy⟩ = 1 := by
    rw [← map_mul]
    have : (⟨y, hy⟩ * ⟨y, hy⟩ : ↥K) = 1 := Subtype.ext hy2
    rw [this, map_one]
  have h2 : h.rho ⟨y, hy⟩ ≠ 1 := fun e1 => hy0 ((h.rho_eq_one_iff _).1 e1)
  have h3 : h.rho ⟨y, hy⟩ ∈ h.rho.range := ⟨_, rfl⟩
  refine ⟨e ▸ h1, e ▸ h2, ?_⟩
  rw [e]
  exact h.sixData.fixCount_invol h3 h2 h1

theorem part3 (h : KSetup U K x v t) :
    ∀ y ∈ K, y * y = 1 → y ∉ U ⊔ zpowers t →
      Nat.card ↥⁅U, zpowers y⁆ = 4 ∧ Nat.card ↥(U ⊓ centralizer ({y} : Set Γ)) = 4 := by
  classical
  intro y hy hy2 hy0
  obtain ⟨hσ, -, hf⟩ := h.invol_perm hy hy2 hy0
  have hC := h.card_centralizer_U hy hσ hf
  have hcomm := card_commutator_mul h.hF.comm h.hF.sq hy2 (h.part1 y hy)
  rw [hC, h.hF.card] at hcomm
  exact ⟨by omega, hC⟩

theorem inverts_x (h : KSetup U K x v t) {z : Γ} (hz : z = v ^ 2 ∨ z = t * v ^ 2) :
    z * x * z⁻¹ = x⁻¹ := by
  have h1 : v ^ 2 * x * (v ^ 2)⁻¹ = x⁻¹ := h.hF.sq_conj
  rcases hz with rfl | rfl
  · exact h1
  · have htx' : t * x⁻¹ = x⁻¹ * t := by
      have := (Commute.inv_right (show Commute t x from h.htx)).eq
      exact this
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.htt
    calc t * v ^ 2 * x * (t * v ^ 2)⁻¹ = t * (v ^ 2 * x * (v ^ 2)⁻¹) * t⁻¹ := by group
      _ = t * x⁻¹ * t⁻¹ := by rw [h1]
      _ = x⁻¹ := by rw [htx', htinv, mul_assoc, h.htt, mul_one]

theorem part4 (h : KSetup U K x v t) :
    ∀ B : Subgroup Γ, B ≤ K → IsElemAbelian 2 B →
      4 ≤ (B ⊓ (U ⊔ zpowers t)).relIndex B →
        ∃ y ∈ B, y ∉ U ⊔ zpowers t ∧
          ∃ k ∈ K, (k * y * k⁻¹) * x * (k * y * k⁻¹)⁻¹ = x⁻¹ := by
  classical
  intro B hBK hB hrel
  let ψ : ↥B →* Perm (Fin 6) := h.rho.comp (Subgroup.inclusion hBK)
  have hker : ψ.ker = (B ⊓ (U ⊔ zpowers t)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    show h.rho ⟨b, hBK b.2⟩ = 1 ↔ _
    rw [h.rho_eq_one_iff]
    exact ⟨fun hb => ⟨b.2, hb⟩, fun hb => hb.2⟩
  have hrel' : (B ⊓ (U ⊔ zpowers t)).relIndex B = Nat.card ψ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hRG : ψ.range ≤ h.rho.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBK b.2⟩, rfl⟩
  have hsq : ∀ g ∈ ψ.range, g * g = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (hB.mul_self_eq_one b.2)
    rw [this, map_one]
  have hcomm : ∀ g ∈ ψ.range, ∀ k ∈ ψ.range, g * k = k * g := by
    rintro _ ⟨b₁, rfl⟩ _ ⟨b₂, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hB.comm b₁.2 b₂.2)
  have hle4 := h.sixData.card_elemAb_le hRG hsq hcomm
  have hcard4 : Nat.card ψ.range = 4 := by
    rw [hrel'] at hrel
    omega
  obtain ⟨g, ⟨b, rfl⟩, hg1, hgf⟩ := h.sixData.klein_even hRG hsq hcomm hcard4
  set y : Γ := (b : Γ) with hy_def
  have hyB : y ∈ B := b.2
  have hyK : y ∈ K := hBK hyB
  have hy2 : y * y = 1 := hB.mul_self_eq_one hyB
  have hρy : ψ b = h.rho ⟨y, hyK⟩ := rfl
  have hy0 : y ∉ U ⊔ zpowers t := fun hy0 => hg1 (by rw [hρy]; exact (h.rho_eq_one_iff _).2 hy0)
  have hvK := h.v_mem_K
  set b₀ := h.rho ⟨v, hvK⟩ with hb₀
  have hg'mem : b₀ ^ 2 ∈ h.rho.range := pow_mem (show b₀ ∈ h.rho.range from ⟨⟨v, hvK⟩, rfl⟩) 2
  have hg'1 : b₀ ^ 2 ≠ 1 := h.sixData.b_two
  have hg'g' : b₀ ^ 2 * b₀ ^ 2 = 1 := by
    rw [← pow_add]
    exact h.sixData.b_four
  have hgmem : ψ b ∈ h.rho.range := hRG ⟨b, rfl⟩
  obtain ⟨c, ⟨k₀, rfl⟩, hc⟩ := h.sixData.invol_conj hgmem hg'mem hg1 hg'1 (hsq _ ⟨b, rfl⟩) hg'g' hgf
    h.sixData.fixCount_b_sq
  set κ : ↥K := k₀ * ⟨y, hyK⟩ * k₀⁻¹ with hκ
  have hκcoe : (κ : Γ) = (k₀ : Γ) * y * (k₀ : Γ)⁻¹ := rfl
  have hρκ : h.rho κ = b₀ ^ 2 := by
    rw [hκ, map_mul, map_mul, map_inv, ← hρy, ← hc]
  have hκ2 : (κ : Γ) * κ = 1 := by
    rw [hκcoe]
    calc (k₀ : Γ) * y * (k₀ : Γ)⁻¹ * ((k₀ : Γ) * y * (k₀ : Γ)⁻¹) = k₀ * (y * y) * (k₀ : Γ)⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hν : ((⟨v, hvK⟩ : ↥K) ^ 2 : ↥K) = ⟨v ^ 2, pow_mem hvK 2⟩ := rfl
  have hw : (v ^ 2)⁻¹ * (κ : Γ) ∈ U ⊔ zpowers t := by
    have hone : h.rho ((⟨v, hvK⟩ : ↥K) ^ 2)⁻¹ * h.rho κ = 1 := by
      rw [map_inv, map_pow, hρκ]
      exact inv_mul_cancel _
    have := (h.rho_eq_one_iff (((⟨v, hvK⟩ : ↥K) ^ 2)⁻¹ * κ)).1 (by rw [map_mul]; exact hone)
    simpa using this
  have hv2K : v ^ 2 ∈ K := pow_mem hvK 2
  have hcardC := (h.part3 (v ^ 2) hv2K h.hF.sq_mul_self h.v_sq_not_mem).2
  obtain ⟨c', hc'U, hc'⟩ := h.lift_invol hκ2 hw hcardC
  refine ⟨y, hyB, hy0, (c' : Γ) * (k₀ : Γ), mul_mem (h.U_le_K hc'U) k₀.2, ?_⟩
  have : (c' * (k₀ : Γ)) * y * (c' * (k₀ : Γ))⁻¹ = c' * (κ : Γ) * c'⁻¹ := by
    rw [hκcoe]
    group
  rw [this]
  exact h.inverts_x hc'

theorem part2 (h : KSetup U K x v t) :
    ∀ E : Subgroup Γ, E ≤ K → IsElemAbelian 2 E →
      Nat.card E ≤ 32 ∧ (Nat.card E = 32 → E = U ⊔ zpowers t) := by
  classical
  intro E hEK hE
  let ψ : ↥E →* Perm (Fin 6) := h.rho.comp (Subgroup.inclusion hEK)
  have hker : ψ.ker = (E ⊓ (U ⊔ zpowers t)).subgroupOf E := by
    ext b
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    show h.rho ⟨b, hEK b.2⟩ = 1 ↔ _
    rw [h.rho_eq_one_iff]
    exact ⟨fun hb => ⟨b.2, hb⟩, fun hb => hb.2⟩
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : E ⊓ (U ⊔ zpowers t) ≤ E)).toEquiv] at hcard
  have hRG : ψ.range ≤ h.rho.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hEK b.2⟩, rfl⟩
  have hsq : ∀ g ∈ ψ.range, g * g = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (hE.mul_self_eq_one b.2)
    rw [this, map_one]
  have hcomm : ∀ g ∈ ψ.range, ∀ k ∈ ψ.range, g * k = k * g := by
    rintro _ ⟨b₁, rfl⟩ _ ⟨b₂, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hE.comm b₁.2 b₂.2)
  have hle4 := h.sixData.card_elemAb_le hRG hsq hcomm
  by_cases hex : ∃ e : ↥E, ψ e ≠ 1
  ·
    obtain ⟨e₁, he₁⟩ := hex
    set y₁ : Γ := (e₁ : Γ) with hy₁
    have hy₁E : y₁ ∈ E := e₁.2
    have hy₁K : y₁ ∈ K := hEK hy₁E
    have hy₁2 : y₁ * y₁ = 1 := hE.mul_self_eq_one hy₁E
    have hψ₁ : ψ e₁ = h.permOf hy₁K := rfl
    have hy₁0 : y₁ ∉ U ⊔ zpowers t := fun hy0 => he₁ (by rw [hψ₁]; exact (h.rho_eq_one_iff ⟨y₁, hy₁K⟩).2 hy0)
    obtain ⟨hσ₁, hσ₁1, hf₁⟩ := h.invol_perm hy₁K hy₁2 hy₁0
    have hD8 : Nat.card ↥(E ⊓ (U ⊔ zpowers t)) ≤ 8 := by
      have h8 := h.card_centralizer_U0 hy₁K hσ₁ hf₁
      rw [← h8]
      apply Subgroup.card_le_of_le
      intro d hd
      rw [mem_inf] at hd ⊢
      refine ⟨hd.2, mem_centralizer_singleton_iff.2 ?_⟩
      exact hE.comm hd.1 hy₁E
    by_cases hall : ∀ r ∈ ψ.range, r = 1 ∨ r = ψ e₁
    · have hR2 : Nat.card ψ.range ≤ 2 := by
        have hz : ψ.range ≤ zpowers (ψ e₁) := by
          intro r hr
          rcases hall r hr with rfl | rfl
          · exact one_mem _
          · exact mem_zpowers _
        have h2 : orderOf (ψ e₁) = 2 := by
          apply orderOf_eq_prime
          · rw [pow_two]; exact hsq _ ⟨e₁, rfl⟩
          · exact he₁
        calc Nat.card ψ.range ≤ Nat.card (zpowers (ψ e₁)) := Subgroup.card_le_of_le hz
          _ = 2 := by rw [Nat.card_zpowers, h2]
      have : Nat.card E ≤ 16 := by
        rw [← hcard]
        calc Nat.card ↥(E ⊓ (U ⊔ zpowers t)) * Nat.card ψ.range ≤ 8 * 2 := Nat.mul_le_mul hD8 hR2
          _ = 16 := by norm_num
      exact ⟨by omega, fun h32 => by omega⟩
    · push Not at hall
      obtain ⟨r, hr, hr1, hr2⟩ := hall
      obtain ⟨e₂, rfl⟩ := hr
      set y₂ : Γ := (e₂ : Γ) with hy₂
      have hy₂E : y₂ ∈ E := e₂.2
      have hy₂K : y₂ ∈ K := hEK hy₂E
      have hy₂2 : y₂ * y₂ = 1 := hE.mul_self_eq_one hy₂E
      have hψ₂ : ψ e₂ = h.permOf hy₂K := rfl
      have hy₂0 : y₂ ∉ U ⊔ zpowers t := fun hy0 => hr1 (by rw [hψ₂]; exact (h.rho_eq_one_iff ⟨y₂, hy₂K⟩).2 hy0)
      obtain ⟨hσ₂, hσ₂1, hf₂⟩ := h.invol_perm hy₂K hy₂2 hy₂0
      have hcm : h.permOf hy₁K * h.permOf hy₂K = h.permOf hy₂K * h.permOf hy₁K := by
        rw [← hψ₁, ← hψ₂]
        exact hcomm _ ⟨e₁, rfl⟩ _ ⟨e₂, rfl⟩
      have hne : h.permOf hy₁K ≠ h.permOf hy₂K := by
        rw [← hψ₁, ← hψ₂]
        exact fun e => hr2 e.symm
      have hmem : h.permOf hy₁K * h.permOf hy₂K ∈ h.rho.range :=
        mul_mem ⟨⟨y₁, hy₁K⟩, rfl⟩ ⟨⟨y₂, hy₂K⟩, rfl⟩
      have hsq12 : h.permOf hy₁K * h.permOf hy₂K * (h.permOf hy₁K * h.permOf hy₂K) = 1 := by
        calc h.permOf hy₁K * h.permOf hy₂K * (h.permOf hy₁K * h.permOf hy₂K)
            = h.permOf hy₁K * (h.permOf hy₂K * h.permOf hy₁K) * h.permOf hy₂K := by group
          _ = h.permOf hy₁K * (h.permOf hy₁K * h.permOf hy₂K) * h.permOf hy₂K := by rw [hcm]
          _ = (h.permOf hy₁K * h.permOf hy₁K) * (h.permOf hy₂K * h.permOf hy₂K) := by group
          _ = 1 := by rw [hσ₁, hσ₂, one_mul]
      have hne12 : h.permOf hy₁K * h.permOf hy₂K ≠ 1 := by
        intro e
        apply hne
        have h3 : h.permOf hy₁K = (h.permOf hy₂K)⁻¹ := eq_inv_of_mul_eq_one_left e
        rw [h3]
        exact inv_eq_of_mul_eq_one_right hσ₂
      have hf12 := h.sixData.fixCount_invol hmem hne12 hsq12
      have hD4 : Nat.card ↥(E ⊓ (U ⊔ zpowers t)) ≤ 4 := by
        have h4 := h.card_centralizer_U0_inter_le hy₁K hy₂K hσ₁ hσ₂ hcm hne hσ₁1 hσ₂1 hf₁ hf₂ hf12
        refine le_trans (Subgroup.card_le_of_le ?_) h4
        intro d hd
        rw [mem_inf] at hd
        rw [mem_inf, mem_inf]
        exact ⟨⟨hd.2, mem_centralizer_singleton_iff.2 (hE.comm hd.1 hy₁E)⟩,
          mem_centralizer_singleton_iff.2 (hE.comm hd.1 hy₂E)⟩
      have : Nat.card E ≤ 16 := by
        rw [← hcard]
        calc Nat.card ↥(E ⊓ (U ⊔ zpowers t)) * Nat.card ψ.range ≤ 4 * 4 := Nat.mul_le_mul hD4 hle4
          _ = 16 := by norm_num
      exact ⟨by omega, fun h32 => by omega⟩
  ·
    push Not at hex
    have hEU : E ≤ U ⊔ zpowers t := fun e he =>
      (h.rho_eq_one_iff ⟨e, hEK he⟩).1 (hex ⟨e, he⟩)
    refine ⟨?_, fun h32 => ?_⟩
    · calc Nat.card E ≤ Nat.card ↥(U ⊔ zpowers t) := Subgroup.card_le_of_le hEU
        _ = 32 := h.U0_data.2
    · exact Subgroup.eq_of_le_of_card_ge hEU (by rw [h.U0_data.2, h32])

theorem part5 (h : KSetup U K x v t) :
    ∀ N : Subgroup (MulAut ↥U), N ≤ imgIn U K →
      (∀ g ∈ imgIn U K, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → actFun U x ∈ N → Even (Nat.card N) := by
  classical
  intro N hNim hNn hxN
  have hKN := h.K_le_normalizer
  let θ : ↥K →* MulAut ↥U := (conjActHom U).comp (Subgroup.inclusion hKN)
  have hθ : ∀ k : ↥K, θ k = actFun U (k : Γ) := fun k => (actFun_of_mem U (hKN k.2)).symm
  have hker : θ.ker = (U ⊔ zpowers t).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, mem_subgroupOf, hθ, actFun_eq_one_iff U (hKN k.2), mem_centralizer_iff]
    constructor
    · intro hc
      exact h.centralizer_U k.2 (fun u hu => (hc u hu).symm)
    · intro hk u hu
      exact h.U0_comm (mem_sup_left hu) hk
  have hθmem : ∀ k : ↥K, θ k ∈ imgIn U K := fun k =>
    (mem_imgIn_iff U K).2 ⟨k, k.2, hKN k.2, (hθ k).symm⟩
  have hsurj : ∀ n ∈ N, ∃ k : ↥K, θ k = n := by
    intro n hn
    obtain ⟨g, hg, hgN, rfl⟩ := (mem_imgIn_iff U K).1 (hNim hn)
    exact ⟨⟨g, hg⟩, by rw [hθ]⟩
  set Ñ : Subgroup ↥K := N.comap θ with hÑ
  have hÑnorm : ∀ k : ↥K, ∀ n ∈ Ñ, k * n * k⁻¹ ∈ Ñ := by
    intro k n hn
    show θ (k * n * k⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNn _ (hθmem k) _ hn
  have hxK : (⟨x, h.x_mem_K⟩ : ↥K) ∈ Ñ := by
    show θ ⟨x, h.x_mem_K⟩ ∈ N
    rw [hθ]
    exact hxN
  obtain ⟨i, hi⟩ : ∃ i : Fin 6, h.rho ⟨x, h.x_mem_K⟩ i ≠ i := by
    obtain ⟨i, hi⟩ := exists_ne h.base
    exact ⟨i, h.sixData.a_fpf i hi⟩
  have htr : ∀ p q : Fin 6, ∃ n ∈ Ñ, h.rho n p = q := by
    intro p q
    by_cases hpq : p = q
    · exact ⟨1, one_mem _, by simp [hpq]⟩
    · obtain ⟨g, ⟨k, rfl⟩, hgi, hgj⟩ :=
        h.sixData.two_trans i p (h.rho ⟨x, h.x_mem_K⟩ i) q hi.symm hpq
      refine ⟨k * ⟨x, h.x_mem_K⟩ * k⁻¹, hÑnorm k _ hxK, ?_⟩
      have h1 : (h.rho k)⁻¹ p = i := by
        rw [← hgi]
        simp
      rw [map_mul, map_mul, map_inv]
      show h.rho k (h.rho ⟨x, h.x_mem_K⟩ ((h.rho k)⁻¹ p)) = q
      rw [h1]
      exact hgj
  letI : MulAction ↥Ñ (Fin 6) := MulAction.compHom (Fin 6) (h.rho.comp Ñ.subtype)
  haveI : MulAction.IsPretransitive ↥Ñ (Fin 6) := ⟨fun p q => by
    obtain ⟨n, hn, hnpq⟩ := htr p q
    exact ⟨⟨n, hn⟩, hnpq⟩⟩
  have hcs : Nat.card (MulAction.stabilizer ↥Ñ h.base) * 6 = Nat.card Ñ := by
    have h1 := MulAction.index_stabilizer_of_transitive ↥Ñ h.base
    have h2 := Subgroup.card_mul_index (MulAction.stabilizer ↥Ñ h.base)
    have h6 : Nat.card (Fin 6) = 6 := by simp
    rw [h1, h6] at h2
    exact h2
  set W : Subgroup ↥K := (U ⊔ zpowers t).subgroupOf K with hW
  have hWN : W ≤ Ñ := by
    intro k hk
    have : θ k = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hk
    show θ k ∈ N
    rw [this]
    exact one_mem _
  have hWcard : Nat.card W = 32 := by
    rw [hW, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.U0_le_K).toEquiv]
    exact h.U0_data.2
  have hdvd : 32 ∣ Nat.card (MulAction.stabilizer ↥Ñ h.base) := by
    have hle : W.subgroupOf Ñ ≤ MulAction.stabilizer ↥Ñ h.base := by
      intro n hn
      rw [mem_subgroupOf] at hn
      rw [MulAction.mem_stabilizer_iff]
      have : h.rho (n : ↥K) = 1 := (h.rho_eq_one_iff _).2 hn
      show h.rho (n : ↥K) h.base = h.base
      rw [this]
      rfl
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWN).toEquiv, hWcard] at this
  have hÑcard : Nat.card Ñ = 32 * Nat.card N := by
    let θÑ : ↥Ñ →* MulAut ↥U := θ.comp Ñ.subtype
    have h1 := Subgroup.card_ker_mul_card_range θÑ
    have hkerÑ : θÑ.ker = θ.ker.subgroupOf Ñ := by
      ext n
      simp [θÑ, MonoidHom.mem_ker, mem_subgroupOf]
    have hker_le : θ.ker ≤ Ñ := by
      rw [hker]
      exact hWN
    have hrange : θÑ.range = N := by
      ext n
      constructor
      · rintro ⟨⟨m, hm⟩, rfl⟩
        exact hm
      · intro hn
        obtain ⟨k, rfl⟩ := hsurj n hn
        exact ⟨⟨k, hn⟩, rfl⟩
    rw [hkerÑ, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.U0_le_K).toEquiv, h.U0_data.2] at h1
    exact h1.symm
  obtain ⟨m, hm⟩ := hdvd
  exact ⟨3 * m, by omega⟩

end KSetup

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst

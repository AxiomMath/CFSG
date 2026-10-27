module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestUOne
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterMuOneCoords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1NextCentral

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

theorem outerRest_chi_mul_right (hcf : U3C1OuterConf G L f t T R₂ D V k) {x : G}
    (hxV : ∀ r ∈ V, x * r * x⁻¹ ∈ V) {r r' : G} (hr : r ∈ V) (hr' : r' ∈ V) :
    (r * r')⁻¹ * (x * (r * r') * x⁻¹) = (r⁻¹ * (x * r * x⁻¹)) * (r'⁻¹ * (x * r' * x⁻¹)) := by
  have hcx : r⁻¹ * (x * r * x⁻¹) ∈ V := mul_mem (inv_mem hr) (hxV r hr)
  have e1 : r'⁻¹ * (r⁻¹ * (x * r * x⁻¹)) = (r⁻¹ * (x * r * x⁻¹)) * r'⁻¹ :=
    hcf.comm _ (inv_mem hr') _ hcx
  calc (r * r')⁻¹ * (x * (r * r') * x⁻¹) = r'⁻¹ * (r⁻¹ * (x * r * x⁻¹)) * (x * r' * x⁻¹) := by
        group
    _ = (r⁻¹ * (x * r * x⁻¹)) * r'⁻¹ * (x * r' * x⁻¹) := by rw [e1]
    _ = _ := by group

omit [Finite G] in
theorem outerRest_chi_mul_left (x x' r : G) :
    r⁻¹ * (x * x' * r * (x * x')⁻¹) =
      (r⁻¹ * (x * r * x⁻¹)) * (x * (r⁻¹ * (x' * r * x'⁻¹)) * x⁻¹) := by
  group

theorem outerRest_conj_V₁ (hcf : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hk : 2 ≤ k) {d : G} (hC : U3C1Cartan L T D d)
    (htrU : ∀ b ∈ szA₁ (szT₁ L T), ∃ x ∈ u3C1U L T V t, outerRestPt t k x = b)
    {U₁ : Subgroup G} (hU₁U : U₁ ≤ u3C1U L T V t)
    (hUU₁ : u3C1U L T V t ≤ normalizer (U₁ : Set G)) (hsup : U₁ ⊔ zpowers t = u3C1U L T V t)
    (hinf : U₁ ⊓ szR (szT₁ L T) V t = szT₁ L T ⊔ V) (hdU₁ : d ∈ normalizer (U₁ : Set G)) :
    ∀ x ∈ U₁, ∀ r ∈ V, r⁻¹ * (x * r * x⁻¹) ∈ szA₁ (szT₁ L T) := by
  classical
  obtain ⟨-, hA₁card, -, -, -, hsqA₁, -⟩ := h.facts_of_card_sylow hS2
  have hf : 2 ≤ f := h.two_le
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hdD := hC.mem
  have hdL : d ∈ L := hC.le hdD
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  have hdT : d ∈ normalizer (szT₁ L T : Set G) := hC.le_normalizer hdD
  have hdY : d ∈ normalizer (szR (szT₁ L T) V t : Set G) :=
    mem_normalizer_szR_of hdT (hcf.D_le hdD) hdt
  have hdV : d ∈ normalizer (V : Set G) := hcf.D_le hdD
  have hdA : d ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
    normalizer_le_normalizer_inf_centralizer _ hdT
  have hA₁comm : ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), b * b' = b' * b :=
    fun b hb b' hb' => mem_centralizer_iff.mp (mem_szA₁.mp hb').2 b (szA₁_le _ hb)
  have hdA' : ∀ b ∈ szA₁ (szT₁ L T), d⁻¹ * b * d ∈ szA₁ (szT₁ L T) := fun b hb =>
    (mem_normalizer_iff''.mp hdA b).mp hb
  have h3 : 2 < Nat.card (szA₁ (szT₁ L T)) := by
    rw [hA₁card]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨b₀, hb₀, -, -, hb₀1, -, -⟩ := exists_two_ne_one h3
  obtain ⟨K, _, _, _, v, μ, hK, hcv, hμ⟩ :=
    U3C1.exists_u3A₁Coords_of_trans hA₁comm hsqA₁ hdA' hC.trans ⟨b₀, hb₀, hb₀1⟩
  rw [hA₁card] at hK
  have hv1 : v 1 = 0 := hcv.v_one
  have hveq : ∀ b ∈ szA₁ (szT₁ L T), v b = 0 → b = 1 := fun b hb h0 =>
    hcv.inj b hb 1 (one_mem _) (by rw [h0, hv1])
  have hUY : ∀ x ∈ U₁, x ∈ normalizer (szR (szT₁ L T) V t : Set G) := fun x hx => (hU₁U hx).1
  have hUA : ∀ x ∈ U₁, ∀ b ∈ szA₁ (szT₁ L T), x * b * x⁻¹ = b := fun x hx b hb =>
    U3Start.conj_szA₁_of_mem_u3C1U (hU₁U hx) hb
  have hxV : ∀ x ∈ U₁, ∀ r ∈ V, x * r * x⁻¹ ∈ V := fun x hx r hr =>
    (mem_normalizer_iff.mp (hcf.normalizer_szR_le h hS2 hk (hUY x hx)).2.1 r).mp hr
  have hχ : ∀ x ∈ U₁, ∀ r ∈ V,
      r⁻¹ * (x * r * x⁻¹) ∈ V ∧ (r⁻¹ * (x * r * x⁻¹)) ^ 2 ^ k = 1 := fun x hx r hr =>
    hcf.outerRest_chi_pow h hS2 hk (hU₁U hx) hr
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hkj : k - 1 = j := by omega
  have hpowj : ∀ c ∈ V, c ^ 2 ^ k = 1 → (c ^ 2 ^ j) ^ 2 = 1 := fun c _ hc1 => by
    rw [← pow_mul, ← pow_succ, ← hj, hc1]
  have hχA : ∀ x ∈ U₁, ∀ r ∈ V, (r⁻¹ * (x * r * x⁻¹)) ^ 2 ^ j ∈ szA₁ (szT₁ L T) :=
    fun x hx r hr => hcf.omega _ (pow_mem (hχ x hx r hr).1 _)
      (hpowj _ (hχ x hx r hr).1 (hχ x hx r hr).2)
  set M : G → G → K := fun x r => v ((r⁻¹ * (x * r * x⁻¹)) ^ 2 ^ j) with hMdef
  set S : G → K := fun x => v (outerRestPt t k x) with hSdef
  set X : G → K := fun r => v (r ^ 2 ^ k) with hXdef
  have hXmul : ∀ r ∈ V, ∀ r' ∈ V, X (r * r') = X r + X r' := fun r hr r' hr' => by
    simp only [hXdef]
    rw [(Commute.mul_pow (hcf.comm _ hr _ hr') _),
      hcv.mul _ (hcf.outerRest_pow_mem_szA₁ hr) _ (hcf.outerRest_pow_mem_szA₁ hr')]
  have hXsurj : ∀ b : K, ∃ r ∈ V, X r = b := by
    intro b
    obtain ⟨a, ha, hab⟩ := hcv.surj b
    obtain ⟨r, hr, hra⟩ := hcf.outerRest_exists_pow_eq h hS2 ha
    exact ⟨r, hr, by simp only [hXdef]; rw [hra, hab]⟩
  have hXconj : ∀ r ∈ V, X (d⁻¹ * r * d) = μ * X r := fun r hr => by
    simp only [hXdef]
    rw [show d⁻¹ * r * d = d⁻¹ * r * d⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv,
      hcv.conj _ (hcf.outerRest_pow_mem_szA₁ hr)]
  have hXeq : ∀ r ∈ V, ∀ r' ∈ V, X r = X r' → ∃ s ∈ V, r' = r * s ^ 2 := by
    intro r hr r' hr' hX
    have h1 : r ^ 2 ^ k = r' ^ 2 ^ k :=
      hcv.inj _ (hcf.outerRest_pow_mem_szA₁ hr) _ (hcf.outerRest_pow_mem_szA₁ hr') hX
    have h2 : (r⁻¹ * r') ^ 2 ^ k = 1 := by
      rw [(Commute.mul_pow (hcf.comm _ (inv_mem hr) _ hr') _), inv_pow, h1, inv_mul_cancel]
    obtain ⟨s, hs, hs2⟩ := hcf.outerRest_exists_sq h hS2 (mul_mem (inv_mem hr) hr') h2
    exact ⟨s, hs, by rw [hs2]; group⟩
  have hπhom : ∀ x ∈ U₁, ∀ x' ∈ U₁, outerRestPt t k (x * x') =
      outerRestPt t k x' * outerRestPt t k x := fun x hx x' hx' =>
    hcf.outerRestPt_mul_of_conj h hS2 hk (hUY x hx) (hUY x' hx') (hUA x hx)
  have hSmul : ∀ x ∈ U₁, ∀ x' ∈ U₁, S (x * x') = S x + S x' := fun x hx x' hx' => by
    simp only [hSdef]
    rw [hπhom x hx x' hx', hcv.mul _ (hcf.outerRestPt_mem h hS2 hk (hUY x' hx')) _
      (hcf.outerRestPt_mem h hS2 hk (hUY x hx)), add_comm]
  have htU : t ∈ u3C1U L T V t := hcf.szR_le_u3C1U h hS2 (mem_szR_right _ _ _)
  have hSsurj : ∀ s : K, ∃ x ∈ U₁, S x = s := by
    intro s
    obtain ⟨a, ha, has⟩ := hcv.surj s
    obtain ⟨u, hu, hua⟩ := htrU a ha
    have htN : t ∈ normalizer (U₁ : Set G) := hUU₁ htU
    have hu' : u ∈ U₁ ⊔ zpowers t := by rw [hsup]; exact hu
    rcases outerStep_mem_or_mul_mem ht2 htN hu' with h1 | h1
    · exact ⟨u, h1, by simp only [hSdef]; rw [hua, has]⟩
    · refine ⟨u * t, h1, ?_⟩
      simp only [hSdef]
      rw [hcf.outerRestPt_mul_of_conj h hS2 hk hu.1 htU.1
        (fun b hb => U3Start.conj_szA₁_of_mem_u3C1U hu hb), outerRestPt_of_comm rfl, one_mul,
        hua, has]
  have hSker : ∀ x ∈ U₁, S x = 0 → x ∈ szT₁ L T ⊔ V := by
    intro x hx h0
    have h1 : outerRestPt t k x = 1 := hveq _ (hcf.outerRestPt_mem h hS2 hk (hUY x hx)) h0
    have hxR : x ∈ szR (szT₁ L T) V t := by
      rw [← hcf.outerRest_u3C1U_inf_stab h hS2 hk]
      exact mem_inf.mpr ⟨hU₁U hx, (hcf.mem_outerRestStab_iff h hS2 hk).mpr ⟨hUY x hx, h1⟩⟩
    rw [← hinf]
    exact mem_inf.mpr ⟨hx, hxR⟩
  have hπd1 : outerRestPt t k d = 1 := outerRestPt_of_comm hdt
  have hπd2 : outerRestPt t k d⁻¹ = 1 := outerRestPt_of_comm (Commute.inv_left hdt).eq
  have hSconj : ∀ x ∈ U₁, S (d⁻¹ * x * d) = μ * S x := by
    intro x hx
    have hπd : outerRestPt t k (d⁻¹ * x * d) = d⁻¹ * outerRestPt t k x * d := by
      rw [mul_assoc, hcf.outerRestPt_mul h hS2 hk (inv_mem hdY) (mul_mem (hUY x hx) hdY),
        hcf.outerRestPt_mul h hS2 hk (hUY x hx) hdY, hπd1, hπd2]
      group
    simp only [hSdef]
    rw [hπd, hcv.conj _ (hcf.outerRestPt_mem h hS2 hk (hUY x hx))]
  have hMr : ∀ x ∈ U₁, ∀ r ∈ V, ∀ r' ∈ V, M x (r * r') = M x r + M x r' := by
    intro x hx r hr r' hr'
    simp only [hMdef]
    rw [hcf.outerRest_chi_mul_right (hxV x hx) hr hr',
      (Commute.mul_pow (hcf.comm _ (hχ x hx r hr).1 _ (hχ x hx r' hr').1) _),
      hcv.mul _ (hχA x hx r hr) _ (hχA x hx r' hr')]
  have hMsq : ∀ x ∈ U₁, ∀ s ∈ V, M x (s ^ 2) = 0 := by
    intro x hx s hs
    simp only [hMdef]
    rw [sq s, hcf.outerRest_chi_mul_right (hxV x hx) hs hs, ← sq, ← pow_mul, ← pow_succ', ← hj,
      (hχ x hx s hs).2, hv1]
  have hMX : ∀ x ∈ U₁, ∀ r ∈ V, ∀ r' ∈ V, X r = X r' → M x r = M x r' := by
    intro x hx r hr r' hr' hX
    obtain ⟨s, hs, rfl⟩ := hXeq r hr r' hr' hX
    rw [hMr x hx r hr _ (pow_mem hs 2), hMsq x hx s hs, add_zero]
  have hMx : ∀ x ∈ U₁, ∀ x' ∈ U₁, ∀ r ∈ V, M (x * x') r = M x r + M x' r := by
    intro x hx x' hx' r hr
    simp only [hMdef]
    obtain ⟨hcV, hc1⟩ := hχ x' hx' r hr
    obtain ⟨s, hs, hs2⟩ := hcf.outerRest_exists_sq h hS2 hcV hc1
    have hχc : ((r⁻¹ * (x' * r * x'⁻¹))⁻¹ * (x * (r⁻¹ * (x' * r * x'⁻¹)) * x⁻¹)) ^ 2 ^ j = 1 := by
      rw [← hs2, sq s, hcf.outerRest_chi_mul_right (hxV x hx) hs hs, ← sq, ← pow_mul,
        ← pow_succ', ← hj, (hχ x hx s hs).2]
    have hχcV := (hχ x hx _ hcV).1
    have hxc : x * (r⁻¹ * (x' * r * x'⁻¹)) * x⁻¹ = (r⁻¹ * (x' * r * x'⁻¹)) *
        ((r⁻¹ * (x' * r * x'⁻¹))⁻¹ * (x * (r⁻¹ * (x' * r * x'⁻¹)) * x⁻¹)) := by group
    rw [outerRest_chi_mul_left x x' r, hxc,
      (Commute.mul_pow (hcf.comm _ (hχ x hx r hr).1 _ (mul_mem hcV hχcV)) _),
      (Commute.mul_pow (hcf.comm _ hcV _ hχcV) _), hχc, mul_one,
      hcv.mul _ (hχA x hx r hr) _ (hχA x' hx' r hr)]
  have hMker : ∀ x ∈ szT₁ L T ⊔ V, ∀ r ∈ V, M x r = 0 := by
    intro x hx r hr
    simp only [hMdef]
    rw [hcf.commute_of_mem_sup hx hr, mul_inv_cancel_right, inv_mul_cancel, one_pow, hv1]
  have hMconj : ∀ x ∈ U₁, ∀ r ∈ V, M (d⁻¹ * x * d) (d⁻¹ * r * d) = μ * M x r := by
    intro x hx r hr
    simp only [hMdef]
    rw [show (d⁻¹ * r * d)⁻¹ * ((d⁻¹ * x * d) * (d⁻¹ * r * d) * (d⁻¹ * x * d)⁻¹) =
      d⁻¹ * (r⁻¹ * (x * r * x⁻¹)) * d⁻¹⁻¹ by group, conj_pow, inv_inv,
      hcv.conj _ (hχA x hx r hr)]
  choose sec hsecV hsecX using hXsurj
  obtain ⟨Dm, hD'⟩ := exists_addMonoidHom₂_of_hom (M := U₁) (S := S)
    (Φ := fun x b => M x (sec b)) hSmul hSsurj
    (fun x hx y hy b => hMx x hx y hy _ (hsecV b))
    (fun x hx b b' => by
      show M x (sec (b + b')) = M x (sec b) + M x (sec b')
      rw [hMX x hx _ (hsecV (b + b')) _ (mul_mem (hsecV b) (hsecV b'))
        (by rw [hsecX, hXmul _ (hsecV b) _ (hsecV b'), hsecX, hsecX]),
        hMr x hx _ (hsecV b) _ (hsecV b')])
    (fun x hx h0 b => hMker x (hSker x hx h0) _ (hsecV b))
  have hM : ∀ x ∈ U₁, ∀ r ∈ V, M x r = Dm (S x) (X r) := by
    intro x hx r hr
    rw [hMX x hx r hr (sec (X r)) (hsecV _) (hsecX _).symm]
    exact hD' x hx _
  obtain ⟨C, hCw⟩ := bilinear_eq_mul_sqrt_of_equivariant hK (by omega) Dm hμ fun s b => by
    obtain ⟨x, hx, rfl⟩ := hSsurj s
    rw [← hsecX b]
    have hdx : d⁻¹ * x * d ∈ U₁ := (mem_normalizer_iff''.mp hdU₁ x).mp hx
    have hdr : d⁻¹ * sec b * d ∈ V := (mem_normalizer_iff''.mp hdV _).mp (hsecV b)
    have e1 := hM _ hdx _ hdr
    rw [hMconj x hx _ (hsecV b), hSconj x hx, hXconj _ (hsecV b)] at e1
    rw [← e1, hM x hx _ (hsecV b)]
  have hinvA : ∀ b ∈ szA₁ (szT₁ L T), b⁻¹ = b := fun b hb =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsqA₁ b hb)
  have hx2 : ∀ x ∈ U₁, ∀ w ∈ V, x * (x * w * x⁻¹) * x⁻¹ = w := by
    intro x hx w hw
    have h1 := hcf.commute_of_mem_sup (hcf.outerRest_sq_mem_sup h hS2 hk (hU₁U hx)) hw
    calc x * (x * w * x⁻¹) * x⁻¹ = x ^ 2 * w * (x ^ 2)⁻¹ := by rw [sq]; group
      _ = w := by rw [h1, mul_inv_cancel_right]
  have hidem : ∀ x ∈ U₁, ∀ r ∈ V, Dm (S x) (X r) = Dm (S x) (Dm (S x) (X r)) := by
    intro x hx r hr
    obtain ⟨hcV, hc1⟩ := hχ x hx r hr
    obtain ⟨s, hs, hs2⟩ := hcf.outerRest_exists_sq h hS2 hcV hc1
    have e1 := SzC1.chi_sq_mul_chi_chi (hx2 x hx r hr)
    rw [← hs2, sq s, hcf.outerRest_chi_mul_right (hxV x hx) hs hs,
      ← sq (s⁻¹ * (x * s * x⁻¹)), ← sq s, hs2] at e1
    have e2 : (r⁻¹ * (x * r * x⁻¹)) ^ 2 = ((s⁻¹ * (x * s * x⁻¹)) ^ 2)⁻¹ :=
      eq_inv_of_mul_eq_one_left e1
    obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hsA : (s⁻¹ * (x * s * x⁻¹)) ^ 2 ^ (i + 1) ∈ szA₁ (szT₁ L T) := by
      rw [← hi]; exact hχA x hx s hs
    have hMeq : M x r = M x s := by
      simp only [hMdef]
      rw [hi, pow_succ', pow_mul, e2, inv_pow, ← pow_mul, ← pow_succ', hinvA _ hsA]
    have hXs : X s = M x r := by
      simp only [hXdef, hMdef]
      rw [hj, pow_succ', pow_mul, hs2]
    calc Dm (S x) (X r) = M x r := (hM x hx r hr).symm
      _ = M x s := hMeq
      _ = Dm (S x) (X s) := hM x hx s hs
      _ = Dm (S x) (M x r) := by rw [hXs]
      _ = Dm (S x) (Dm (S x) (X r)) := by rw [hM x hx r hr]
  have hC0 : C = 0 := by
    obtain ⟨x₁, hx₁, hS₁⟩ := hSsurj 1
    refine SzC1.eq_zero_of_idem hK hf fun b => ?_
    have e := hidem x₁ hx₁ (sec b) (hsecV b)
    rw [hsecX, hS₁, hCw, hCw, one_mul, one_mul] at e
    exact e.symm
  intro x hx r hr
  have hk1 : ∀ w ∈ V, (w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ j = 1 := by
    intro w hw
    refine hveq _ (hχA x hx w hw) ?_
    show M x w = 0
    rw [hM x hx w hw, hCw, hC0, zero_mul]
  have h4 : ∀ w ∈ V, ∃ s ∈ V, w⁻¹ * (x * w * x⁻¹) = s ^ 4 := by
    intro w hw
    obtain ⟨z, hz, hzw⟩ := pushUp_exists_pow_eq hcf.comm (pow_pos (by norm_num) f) hcf.card
      hcf.pow hcf.omega (le_of_eq hA₁card) (show j ≤ k + 1 by omega) (hχ x hx w hw).1 (hk1 w hw)
    refine ⟨z, hz, ?_⟩
    rw [← hzw, show k + 1 - j = 2 by omega]
    norm_num
  have hsq := SzC1.sq_chi_eq_one hcf.comm hcf.pow (fun w hw => hxV x hx w hw) (hx2 x hx) h4 r hr
  exact hcf.omega _ (hχ x hx r hr).1 hsq

end U3C1OuterConf

end CFSG.SeitzReduction.RankOne

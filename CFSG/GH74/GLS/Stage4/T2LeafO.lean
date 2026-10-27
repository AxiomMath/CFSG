module

public import CFSG.GH74.GLS.Stage4.T2LeafOA
public import CFSG.GH74.GLS.Stage4.T2Interfaces
public import CFSG.GH74.GLS.Stage4.T2P52

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Lifted

section NotCent2

variable {G : Type} {Gs : Type} [Group G] [Group Gs] {q₁ q₂ : ℕ} {z t : G} {K₁ K₂ : Subgroup G}
  {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2C_not_cent_K₂ (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hC : T2Comp z K₁ K₂) {x : G} (hx : x ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)))
    (hxK : x ∉ K₁ ⊔ K₂) (hcent : ∀ y ∈ K₂, x * y = y * x) : False := by
  have hgen := hRem.gen
  have hidx := hSet.index_two
  have htC₁ : t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rw [← hgen]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htK : t ∉ K₁ ⊔ K₂ := by
    intro htK
    have hle : oPrimeResidualOf 2 (centralizer ({z} : Set G)) ≤ K₁ ⊔ K₂ := by
      rw [← hgen]; exact sup_le le_rfl (Subgroup.zpowers_le.2 htK)
    have h1 : (K₁ ⊔ K₂).relIndex (oPrimeResidualOf 2 (centralizer ({z} : Set G))) = 1 :=
      Subgroup.relIndex_eq_one.2 hle
    rw [h1] at hidx
    exact absurd hidx (by norm_num)
  have hxt : x * t⁻¹ ∈ K₁ ⊔ K₂ := t2C_outer_coset hidx hx htC₁ hxK htK
  obtain ⟨e, g, hns, hact⟩ := hRem.diag₂
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_comm hC.comm _).1 hxt
  have hxe : ∀ y₀ ∈ K₂, t * y₀ * t⁻¹ = b⁻¹ * y₀ * b := by
    intro y₀ hy₀
    have h1 := hcent y₀ hy₀
    have hx' : x = (a * b) * t := by rw [← hab]; group
    rw [hx'] at h1
    have h2 : t * y₀ * t⁻¹ = (a * b)⁻¹ * y₀ * (a * b) := by
      calc t * y₀ * t⁻¹ = (a * b)⁻¹ * ((a * b) * t * y₀) * t⁻¹ := by group
        _ = (a * b)⁻¹ * (y₀ * ((a * b) * t)) * t⁻¹ := by rw [h1]
        _ = (a * b)⁻¹ * y₀ * (a * b) := by group
    rw [h2]
    have hay : a⁻¹ * y₀ * a = y₀ := by
      have := hC.comm a ha y₀ hy₀
      calc a⁻¹ * y₀ * a = a⁻¹ * (y₀ * a) := by group
        _ = a⁻¹ * (a * y₀) := by rw [this]
        _ = y₀ := by group
    calc (a * b)⁻¹ * y₀ * (a * b) = b⁻¹ * (a⁻¹ * y₀ * a) * b := by group
      _ = b⁻¹ * y₀ * b := by rw [hay]
  apply hns
  have hbinv : (e ⟨b⁻¹, K₂.inv_mem hb⟩)⁻¹ = e ⟨b, hb⟩ := by
    rw [← map_inv]
    exact congrArg e (Subtype.ext (by simp))
  refine t2C_isSquare_of_slConj_eq_inner g (e ⟨b⁻¹, K₂.inv_mem hb⟩) ?_
  intro s
  obtain ⟨y₀, rfl⟩ := e.surjective s
  obtain ⟨y, hy1, hy2⟩ := hact y₀
  have hy : y = ⟨b⁻¹, K₂.inv_mem hb⟩ * y₀ * ⟨b, hb⟩ := by
    apply Subtype.ext
    rw [hy1]
    exact hxe y₀ y₀.2
  apply Subtype.ext
  rw [coe_slConj, ← hy2, hy, hbinv, map_mul, map_mul]

end NotCent2

section Twist

variable {G : Type} [Group G]

theorem t2L_odd_central_twist {m s z : G} (hmz : m * z = z * m) (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hodd : Odd (orderOf m)) (h : m * s * m⁻¹ = z * s) : False := by
  have hmzj : ∀ j : ℕ, m * z ^ j * m⁻¹ = z ^ j := by
    intro j
    have : Commute m (z ^ j) := (Commute.eq hmz : m * z = z * m) |> fun hc => (Commute.pow_right hc j)
    rw [this.eq]; group
  have hiter : ∀ j : ℕ, m ^ j * s * (m ^ j)⁻¹ = z ^ j * s := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : m ^ (j + 1) * s * (m ^ (j + 1))⁻¹ = m * (m ^ j * s * (m ^ j)⁻¹) * m⁻¹ := by
        rw [pow_succ']; generalize m ^ j = w; group
      rw [e, ih]
      calc m * (z ^ j * s) * m⁻¹ = (m * z ^ j * m⁻¹) * (m * s * m⁻¹) := by group
        _ = z ^ j * (z * s) := by rw [hmzj, h]
        _ = z ^ (j + 1) * s := by rw [pow_succ]; group
  have h1 := hiter (orderOf m)
  rw [pow_orderOf_eq_one] at h1
  obtain ⟨k, hk⟩ := hodd
  have hzN : z ^ orderOf m = z := by
    rw [hk, pow_succ, pow_mul, sq, hzz, one_pow, one_mul]
  rw [hzN] at h1
  have h2 : z * s = 1 * s := by simpa using h1.symm
  exact hz1 (mul_right_cancel h2)

end Twist

section Factor

variable {G : Type} [Group G] [Finite G]

theorem t2L_oddcent_factor (hOC5 : T2OC5) (hOC3 : T2OC3) {K S : Subgroup G} {F : Type} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (hF3 : 3 ≤ Nat.card F) (e : ↥K ≃* Hex.SL2 F)
    (hP : IsPGroup 2 ↥((S ⊓ K).subgroupOf K)) (hPidx : ¬ 2 ∣ ((S ⊓ K).subgroupOf K).index)
    (hS2 : IsPGroup 2 ↥S) (hSK : ∀ s ∈ S, ∀ x ∈ K, s * x * s⁻¹ ∈ K)
    (hlin : ∀ h3 : 3 < Nat.card F, ∀ s ∈ S, ∃ hs : s ∈ normalizer (K : Set G),
      (gammaOf hodd h3 (MulAut.congr e (Subgroup.normalizerMonoidHom K ⟨s, hs⟩))).right = 1)
    (hout : ∃ s₀ ∈ S, ¬ ∃ k ∈ K, ∀ x ∈ K, s₀ * x * s₀⁻¹ = k * x * k⁻¹) {m : G}
    (hmodd : Odd (orderOf m)) (hmK : ∀ x ∈ K, m * x * m⁻¹ ∈ K) (hmS : ∀ s ∈ S, m * s * m⁻¹ ∈ S) :
    ∀ s ∈ S, ∀ x ∈ K, (m * s * m⁻¹ * s⁻¹) * x = x * (m * s * m⁻¹ * s⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSn : S ≤ normalizer (K : Set G) := fun s hs => Subgroup.mem_normalizer_fintype (hSK s hs)
  have hmn : m ∈ normalizer (K : Set G) := Subgroup.mem_normalizer_fintype hmK
  let ρN : ↥(normalizer (K : Set G)) →* MulAut ↥K := Subgroup.normalizerMonoidHom K
  have hρN : ∀ (y : ↥(normalizer (K : Set G))) (x : ↥K), ((ρN y x : ↥K) : G) = (y : G) * x * (y : G)⁻¹ :=
    fun y x => rfl
  let M : Subgroup (MulAut ↥K) := (S.subgroupOf (normalizer (K : Set G))).map ρN
  have hM2 : IsPGroup 2 ↥M := (hS2.comap_subtype).map ρN
  have hmemM : ∀ s (hs : s ∈ normalizer (K : Set G)), s ∈ S → ρN ⟨s, hs⟩ ∈ M :=
    fun s hs hsS => ⟨⟨s, hs⟩, Subgroup.mem_subgroupOf.2 hsS, rfl⟩
  let P₀ : Sylow 2 ↥K := hP.toSylow hPidx
  have hP₀ : (P₀ : Subgroup ↥K) = (S ⊓ K).subgroupOf K := IsPGroup.toSylow_coe hP hPidx
  have hconj : (P₀ : Subgroup ↥K).map (MulAut.conj : ↥K →* MulAut ↥K) ≤ M := by
    rintro _ ⟨p, hp, rfl⟩
    rw [hP₀] at hp
    have hpS : (p : G) ∈ S := (Subgroup.mem_subgroupOf.1 hp).1
    have hpn : (p : G) ∈ normalizer (K : Set G) := Subgroup.le_normalizer p.2
    have : (MulAut.conj : ↥K →* MulAut ↥K) p = ρN ⟨(p : G), hpn⟩ := by
      ext x; rfl
    rw [this]
    exact hmemM _ hpn hpS
  have hξ : ∃ ξ ∈ M, ξ ∉ (MulAut.conj : ↥K →* MulAut ↥K).range := by
    obtain ⟨s₀, hs₀S, hs₀⟩ := hout
    refine ⟨ρN ⟨s₀, hSn hs₀S⟩, hmemM _ _ hs₀S, ?_⟩
    rintro ⟨k, hk⟩
    apply hs₀
    refine ⟨(k : G), k.2, fun x hx => ?_⟩
    have := congrArg (fun r : MulAut ↥K => ((r ⟨x, hx⟩ : ↥K) : G)) hk
    simpa [hρN, MulAut.conj_apply] using this.symm
  let ρ : MulAut ↥K := ρN ⟨m, hmn⟩
  have hρodd : Odd (orderOf ρ) := by
    have h1 : orderOf ρ ∣ orderOf (⟨m, hmn⟩ : ↥(normalizer (K : Set G))) := orderOf_map_dvd ρN _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hmodd h1
  have hnorm : ∀ φ ∈ M, ρ * φ * ρ⁻¹ ∈ M := by
    rintro _ ⟨a, ha, rfl⟩
    have hs : (a : G) ∈ S := Subgroup.mem_subgroupOf.1 ha
    have hms : m * (a : G) * m⁻¹ ∈ S := hmS _ hs
    have hmsn : m * (a : G) * m⁻¹ ∈ normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hmn a.2) (Subgroup.inv_mem _ hmn)
    have : ρ * ρN a * ρ⁻¹ = ρN ⟨m * (a : G) * m⁻¹, hmsn⟩ := by
      show ρN ⟨m, hmn⟩ * ρN a * (ρN ⟨m, hmn⟩)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact hmemM _ hmsn hms
  have hcomm : ∀ φ ∈ M, ρ * φ = φ * ρ := by
    by_cases h3 : Nat.card F = 3
    · exact hOC3 ↥K F h3 e P₀ M hM2 hconj hξ ρ hρodd hnorm
    · have h3' : 3 < Nat.card F := lt_of_le_of_ne hF3 (Ne.symm h3)
      refine hOC5 ↥K F hodd h3' e P₀ M hM2 hconj ?_ hξ ρ hρodd hnorm
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨hs', h⟩ := hlin h3' (a : G) (Subgroup.mem_subgroupOf.1 ha)
      exact h
  intro s hs x hx
  have hsn : s ∈ normalizer (K : Set G) := hSn hs
  have hcn : m * s * m⁻¹ * s⁻¹ ∈ normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hmn hsn) (Subgroup.inv_mem _ hmn))
      (Subgroup.inv_mem _ hsn)
  have hρc : ρN ⟨m * s * m⁻¹ * s⁻¹, hcn⟩ = ρ * ρN ⟨s, hsn⟩ * ρ⁻¹ * (ρN ⟨s, hsn⟩)⁻¹ := by
    show ρN ⟨m * s * m⁻¹ * s⁻¹, hcn⟩ = ρN ⟨m, hmn⟩ * ρN ⟨s, hsn⟩ * (ρN ⟨m, hmn⟩)⁻¹ * (ρN ⟨s, hsn⟩)⁻¹
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have h1 : ρ * ρN ⟨s, hsn⟩ = ρN ⟨s, hsn⟩ * ρ := hcomm _ (hmemM s hsn hs)
  have h2 : ρN ⟨m * s * m⁻¹ * s⁻¹, hcn⟩ = 1 := by
    rw [hρc, h1]; group
  have h3 := congrArg (fun r : MulAut ↥K => ((r ⟨x, hx⟩ : ↥K) : G)) h2
  have h4 : (m * s * m⁻¹ * s⁻¹) * x * (m * s * m⁻¹ * s⁻¹)⁻¹ = x := by
    simpa [hρN] using h3
  calc (m * s * m⁻¹ * s⁻¹) * x = ((m * s * m⁻¹ * s⁻¹) * x * (m * s * m⁻¹ * s⁻¹)⁻¹) *
        (m * s * m⁻¹ * s⁻¹) := by group
    _ = x * (m * s * m⁻¹ * s⁻¹) := by rw [h4]

end Factor

theorem ch6T2OddCent_of
    (hOC5 : T2OC5) (hOC3 : T2OC3) : Ch6T2OddCent := by
  intro G _ _ Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord m hmodd hmC
    hmS
  have ctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  subst hz hK₁ hK₂ hq₁ hq₂
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨hs₁, hs₂⟩ := t2C_sylow_inf_K hSet hRem ctx.Sctx
  obtain ⟨⟨e₁, hze₁⟩, ⟨e₂, hze₂⟩⟩ := t2C_coords hSet
  have hmz : m * N.z = N.z * m := Subgroup.mem_centralizer_singleton_iff.1 hmC
  obtain ⟨hmn₁, hmn₂⟩ := t2Ctx_odd_normK ctx hmz hmodd
  obtain ⟨hn₁, hn₂⟩ := t2C_C₁_normalizes hRem hSet.comm
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  have hSK₁ : ∀ s ∈ N.S, ∀ x ∈ N.K₁, s * x * s⁻¹ ∈ N.K₁ := fun s hs => hn₁ s (ctx.SC₁ hs)
  have hSK₂ : ∀ s ∈ N.S, ∀ x ∈ N.K₂, s * x * s⁻¹ ∈ N.K₂ := fun s hs => hn₂ s (ctx.SC₁ hs)
  have hP₁ : IsPGroup 2 ↥((N.S ⊓ N.K₁).subgroupOf N.K₁) :=
    (ctx.Sctx.S2.to_le inf_le_left).comap_subtype
  have hP₂ : IsPGroup 2 ↥((N.S ⊓ N.K₂).subgroupOf N.K₂) :=
    (ctx.Sctx.S2.to_le inf_le_left).comap_subtype
  have hgen : N.K₁ ⊔ N.K₂ ⊔ Subgroup.zpowers t =
      oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) := hRem.gen
  have hlin₁ : ∀ h3 : 3 < Nat.card F₁, ∀ s ∈ N.S, ∃ hs : s ∈ normalizer (N.K₁ : Set G),
      (gammaOf hodd₁ h3 (MulAut.congr e₁ (Subgroup.normalizerMonoidHom N.K₁ ⟨s, hs⟩))).right = 1 := by
    intro h3 s hs
    exact t2L_lin_gen hodd₁ h3 e₁ hSet.comm (fun c hc => hn₁ c (hgen ▸ hc))
      (by obtain ⟨e, g, -, hact⟩ := hRem.diag₁; exact ⟨e, g, hact⟩) s
      (by rw [hgen]; exact ctx.SC₁ hs)
  have hlin₂ : ∀ h3 : 3 < Nat.card F₂, ∀ s ∈ N.S, ∃ hs : s ∈ normalizer (N.K₂ : Set G),
      (gammaOf hodd₂ h3 (MulAut.congr e₂ (Subgroup.normalizerMonoidHom N.K₂ ⟨s, hs⟩))).right = 1 := by
    intro h3 s hs
    exact t2L_lin_gen (K' := N.K₁) hodd₂ h3 e₂ (fun x hx y hy => (hSet.comm y hy x hx).symm)
      (fun c hc => hn₂ c (by rw [sup_comm N.K₂ N.K₁, hgen] at hc; exact hc))
      (by obtain ⟨e, g, -, hact⟩ := hRem.diag₂; exact ⟨e, g, hact⟩) s
      (by rw [sup_comm N.K₂ N.K₁, hgen]; exact ctx.SC₁ hs)
  obtain ⟨s₀, hs₀S, hs₀K⟩ : ∃ s₀ ∈ N.S, s₀ ∉ N.K₁ ⊔ N.K₂ := by
    by_contra hcon
    push Not at hcon
    have hSK : N.S ≤ N.K₁ ⊔ N.K₂ := fun s hs => hcon s hs
    have h1 : (N.S ⊓ (N.K₁ ⊔ N.K₂)).relIndex N.S = 1 := by
      rw [Subgroup.relIndex_eq_one]
      exact fun x hx => ⟨hx, hSK hx⟩
    have h2 := ctx.Sctx.SK
    rw [h1] at h2
    exact absurd h2 (by norm_num)
  have hkC₁ : ∀ k ∈ N.K₁ ⊔ N.K₂, k ∈ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) :=
    fun k hk => hSet.le_residual hk
  have hout₁ : ∃ s₀ ∈ N.S, ¬ ∃ k ∈ N.K₁, ∀ x ∈ N.K₁, s₀ * x * s₀⁻¹ = k * x * k⁻¹ := by
    refine ⟨s₀, hs₀S, ?_⟩
    rintro ⟨k, hk, hkx⟩
    have hyC₁ : k⁻¹ * s₀ ∈ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hkC₁ k (Subgroup.mem_sup_left hk))) (ctx.SC₁ hs₀S)
    have hyK : k⁻¹ * s₀ ∉ N.K₁ ⊔ N.K₂ := by
      intro h
      apply hs₀K
      have : s₀ = k * (k⁻¹ * s₀) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) h
    exact t2C_not_cent_K₁ hSet hRem ctx.C hyC₁ hyK (fun x hx => by
      have := hkx x hx
      calc k⁻¹ * s₀ * x = k⁻¹ * (s₀ * x * s₀⁻¹) * s₀ := by group
        _ = k⁻¹ * (k * x * k⁻¹) * s₀ := by rw [this]
        _ = x * (k⁻¹ * s₀) := by group)
  have hout₂ : ∃ s₀ ∈ N.S, ¬ ∃ k ∈ N.K₂, ∀ x ∈ N.K₂, s₀ * x * s₀⁻¹ = k * x * k⁻¹ := by
    refine ⟨s₀, hs₀S, ?_⟩
    rintro ⟨k, hk, hkx⟩
    have hyC₁ : k⁻¹ * s₀ ∈ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hkC₁ k (Subgroup.mem_sup_right hk))) (ctx.SC₁ hs₀S)
    have hyK : k⁻¹ * s₀ ∉ N.K₁ ⊔ N.K₂ := by
      intro h
      apply hs₀K
      have : s₀ = k * (k⁻¹ * s₀) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) h
    exact t2C_not_cent_K₂ hSet hRem ctx.C hyC₁ hyK (fun x hx => by
      have := hkx x hx
      calc k⁻¹ * s₀ * x = k⁻¹ * (s₀ * x * s₀⁻¹) * s₀ := by group
        _ = k⁻¹ * (k * x * k⁻¹) * s₀ := by rw [this]
        _ = x * (k⁻¹ * s₀) := by group)
  have hd₁ := t2L_oddcent_factor hOC5 hOC3 (F := F₁) hodd₁
    (by rw [hSet.card₁]; have := hSet.five; omega) e₁ hP₁ hs₁ ctx.Sctx.S2 hSK₁ hlin₁ hout₁ hmodd
    hmn₁ hmS
  have hd₂ := t2L_oddcent_factor hOC5 hOC3 (F := F₂) hodd₂
    (by rw [hSet.card₂]; have := hLoc.q₂_ge; omega) e₂ hP₂ hs₂ ctx.Sctx.S2 hSK₂ hlin₂ hout₂ hmodd
    hmn₂ hmS
  intro s hs
  have hdS : m * s * m⁻¹ * s⁻¹ ∈ N.S := N.S.mul_mem (hmS s hs) (N.S.inv_mem hs)
  have hdK : ∀ k ∈ N.K₁ ⊔ N.K₂, (m * s * m⁻¹ * s⁻¹) * k = k * (m * s * m⁻¹ * s⁻¹) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hSet.comm x).1 hx
    have h1 := hd₁ s hs a ha
    have h2 := hd₂ s hs b hb
    calc (m * s * m⁻¹ * s⁻¹) * (a * b) = ((m * s * m⁻¹ * s⁻¹) * a) * b := by group
      _ = (a * (m * s * m⁻¹ * s⁻¹)) * b := by rw [h1]
      _ = a * ((m * s * m⁻¹ * s⁻¹) * b) := by group
      _ = a * (b * (m * s * m⁻¹ * s⁻¹)) := by rw [h2]
      _ = (a * b) * (m * s * m⁻¹ * s⁻¹) := by group
  have hdz : m * s * m⁻¹ * s⁻¹ ∈ Subgroup.zpowers N.z :=
    t2C_centK_C₁ hSet hRem ctx.C _ (ctx.SC₁ hdS) hdK
  rcases t2C_zpowers_cases ctx.zz hdz with h | h
  · calc m * s = (m * s * m⁻¹ * s⁻¹) * s * m := by group
      _ = s * m := by rw [h]; group
  · exfalso
    refine t2L_odd_central_twist hmz ctx.zz ctx.z_ne hmodd (s := s) ?_
    calc m * s * m⁻¹ = (m * s * m⁻¹ * s⁻¹) * s := by group
      _ = N.z * s := by rw [h]

end CFSG.GH74.GLS.Stage4.Rest

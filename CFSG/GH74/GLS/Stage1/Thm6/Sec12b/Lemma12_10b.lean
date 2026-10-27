module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_10a
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Transport
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type*} [Group G] [Finite G] {x z : G} {S T P Q Rd F U : Subgroup G}

omit [Finite G] in
theorem omega1_mono {A B : Subgroup G} (h : A ≤ B) : omega1 A ≤ omega1 B :=
  Subgroup.closure_mono (fun _ hu => ⟨h hu.1, hu.2⟩)

omit [Finite G] in
theorem phi2_mono {A B : Subgroup G} (h : A ≤ B) : phi2 A ≤ phi2 B :=
  Subgroup.closure_mono (fun s hs => by
    obtain ⟨d, hd, rfl⟩ := hs
    exact ⟨d, h hd, rfl⟩)

theorem omega1_phi_conj (h : HBase G x S T P Q Rd F) (hout : IP_outer x T Rd)
    (hcf : IP_cent_four T P Q Rd) (g : G) {V : Subgroup G} (hVP : V ≤ Hconj g P) (hV : IsFour V)
    {A : Subgroup G} (hAT : A ≤ Hconj g T)
    (hAc : ∀ a ∈ A, ∀ e ∈ V ⊔ Subgroup.zpowers (g⁻¹ * x * g), e * a = a * e) :
    omega1 (phi2 A) ≤ Subgroup.zpowers (g⁻¹ * x * g) := by
  have h' := hbase_conj h g
  have := (lemma_12_2 h' (ipOuter_conj hout g) (ipCentFour_conj hcf g)).2 V hVP hV
  refine le_trans (omega1_mono (phi2_mono ?_)) this
  intro a ha
  exact ⟨hAT ha, Subgroup.mem_centralizer_iff.2 (fun e he => hAc a ha e he)⟩

omit [Finite G] in
theorem isElemAb2_of_sq {A : Subgroup G} (hsq : ∀ t ∈ A, t * t = 1) : IsElemAb2 A := by
  intro t ht
  refine ⟨hsq t ht, fun s hs => ?_⟩
  have h1 : (t * s) * (t * s) = 1 := hsq _ (A.mul_mem ht hs)
  have h2 : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hsq t ht)
  have h3 : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hsq s hs)
  have h4 : t * s = (t * s)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [mul_inv_rev, h2, h3] at h4
  exact h4

theorem EV_isSylow (h : HBase G x S T P Q Rd F) (h127 : After127 G x z S T P Q Rd F)
    (hout : IP_outer x T Rd) (hcf : IP_cent_four T P Q Rd) (hclosed : IP_P_closed x T P)
    (hf3 : IP_f3 x P) (hzV : IP_z_V z P) {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V) {a : G}
    (haS : a ∈ S) (haT : a ∉ T)
    (haN : a ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) :
    IsSylow2In (V ⊔ Subgroup.zpowers x)
      (Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) := by
  obtain ⟨f, y, c⟩ := exists_ctx h h127 hf3 hzV hVP hV haS haT haN
  have haiN : a⁻¹ ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
    inv_mem haN
  obtain ⟨f', y', c'⟩ := exists_ctx h h127 hf3 hzV hVP hV (S.inv_mem haS)
    (fun hh => haT (by simpa using T.inv_mem hh)) haiN
  obtain ⟨u0, hu0V, hu01, hu0⟩ := c'.struct
  have hu0' : a⁻¹ * x * a = x * u0 := by simpa using hu0
  have hxc : ∀ v ∈ V, x * v = v * x := fun v hv => h.x_central v (h.P_le_T (hVP hv))
  have hE8 := card_E h hVP hV
  have hEab := isElemAb2_sup_zpowers hV h.x_sq hxc
  have hxE : x ∈ V ⊔ Subgroup.zpowers x := Ctx.x_mem_E
  have hED : V ⊔ Subgroup.zpowers x ≤
      Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
    fun e he => Subgroup.mem_centralizer_iff.2 (fun e' he' => ((hEab e' he').2 e he))
  have hEp : IsPGroup 2 ↥(V ⊔ Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 3) (by rw [hE8]; norm_num)
  obtain ⟨TV, hTV, hETV⟩ := exists_sylow2_ge hEp hED
  have hTVpg : IsPGroup 2 ↥TV := hTV.2.1
  have hTVc : ∀ t ∈ TV, ∀ e ∈ V ⊔ Subgroup.zpowers x, e * t = t * e :=
    fun t ht e he => Subgroup.mem_centralizer_iff.1 (hTV.1 ht) e he
  have hTVC : TV ≤ Subgroup.centralizer ({x} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.2 (hTVc t ht x hxE).symm
  have hxaE : a⁻¹ * x * a ∈ V ⊔ Subgroup.zpowers x := by
    have := Ctx.conjE haiN hxE
    simpa using this
  have hxa2 : (a⁻¹ * x * a) * (a⁻¹ * x * a) = 1 := by
    calc (a⁻¹ * x * a) * (a⁻¹ * x * a) = a⁻¹ * (x * x) * a := by group
      _ = 1 := by rw [h.x_sq]; group
  have hA : omega1 (phi2 TV) ≤ Subgroup.zpowers x := by
    obtain ⟨T', hT', hTVT'⟩ := exists_sylow2_ge hTVpg hTVC
    obtain ⟨c0, hc0C, hc0T⟩ := sylow2_exists_conj h.T_sylow hT'
    have hcx : c0⁻¹ * x * c0 = x := by
      have hh := Subgroup.mem_centralizer_singleton_iff.1 hc0C
      calc c0⁻¹ * x * c0 = c0⁻¹ * (x * c0) := by group
        _ = c0⁻¹ * (c0 * x) := by rw [hh]
        _ = x := by group
    have hVP' : V ≤ Hconj c0 P := by
      intro v hv
      rw [mem_Hconj]
      have hvT : v ∈ T' := hTVT' (hETV (Subgroup.mem_sup_left hv))
      rw [hc0T, mem_Hconj] at hvT
      exact hclosed c0 hc0C v (hVP hv) hvT
    have := omega1_phi_conj h hout hcf c0 hVP' hV (A := TV) (hc0T ▸ hTVT')
      (fun t ht e he => by rw [hcx] at he; exact hTVc t ht e he)
    rwa [hcx] at this
  have hB : omega1 (phi2 TV) ≤ Subgroup.zpowers (a⁻¹ * x * a) := by
    have hTVCa : TV ≤ Subgroup.centralizer ({a⁻¹ * x * a} : Set G) := fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.2 (hTVc t ht _ hxaE).symm
    obtain ⟨T'', hT'', hTVT''⟩ := exists_sylow2_ge hTVpg hTVCa
    have hsyl := sylow2_conj h.T_sylow a
    rw [Hconj_centralizer] at hsyl
    obtain ⟨k, hkC, hkT⟩ := sylow2_exists_conj hsyl hT''
    have hkx := Subgroup.mem_centralizer_singleton_iff.1 hkC
    have hg : T'' = Hconj (a * k) T := by rw [hkT, Hconj_mul]
    have hgx : (a * k)⁻¹ * x * (a * k) = a⁻¹ * x * a := by
      calc (a * k)⁻¹ * x * (a * k) = k⁻¹ * (a⁻¹ * x * a) * k := by group
        _ = k⁻¹ * (k * (a⁻¹ * x * a)) := by rw [hkx]; group
        _ = a⁻¹ * x * a := by group
    have hc1 : a * k * a⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * k * a⁻¹ * x = a * (k * (a⁻¹ * x * a)) * a⁻¹ := by group
        _ = a * ((a⁻¹ * x * a) * k) * a⁻¹ := by rw [hkx]
        _ = x * (a * k * a⁻¹) := by group
    have hVP'' : V ≤ Hconj (a * k) P := by
      intro v hv
      rw [mem_Hconj]
      have hvT : v ∈ T'' := hTVT'' (hETV (Subgroup.mem_sup_left hv))
      rw [hg, mem_Hconj] at hvT
      have hav : a * v * a⁻¹ ∈ V := c.a_V hv
      have e : a * k * v * (a * k)⁻¹ = (a * k * a⁻¹) * (a * v * a⁻¹) * (a * k * a⁻¹)⁻¹ := by group
      have hvT' : (a * k * a⁻¹) * (a * v * a⁻¹) * (a * k * a⁻¹)⁻¹ ∈ T := by rw [← e]; exact hvT
      rw [e]
      exact hclosed _ hc1 _ (hVP hav) hvT'
    have hsup : V ⊔ Subgroup.zpowers (a⁻¹ * x * a) ≤ V ⊔ Subgroup.zpowers x :=
      sup_le le_sup_left ((Subgroup.zpowers_le).2 hxaE)
    have := omega1_phi_conj h hout hcf (a * k) hVP'' hV (A := TV) (hg ▸ hTVT'')
      (fun t ht e he => by
        rw [hgx] at he
        exact hTVc t ht e (hsup he))
    rwa [hgx] at this
  have hbot : omega1 (phi2 TV) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have h1 := hA hu
    have h2 := hB hu
    have hne : x ≠ a⁻¹ * x * a := by
      rw [hu0']
      intro hh
      exact hu01 (by simpa using (congrArg (fun t => x⁻¹ * t) hh).symm)
    have hinf := zpowers_inf_zpowers h.x_sq hxa2 hne
    have hu' : u ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers (a⁻¹ * x * a) := ⟨h1, h2⟩
    rw [hinf] at hu'
    exact hu'
  have hsq : ∀ t ∈ TV, t * t = 1 := by
    intro t ht
    by_contra ht1
    have hmem : t * t ∈ phi2 TV := Subgroup.subset_closure ⟨t, ht, rfl⟩
    have hne : phi2 TV ≠ ⊥ := fun hb => ht1 (by rw [hb] at hmem; exact Subgroup.mem_bot.1 hmem)
    have hle : phi2 TV ≤ TV := (Subgroup.closure_le TV).2 (fun s hs => by
      obtain ⟨d, hd, rfl⟩ := hs
      exact TV.mul_mem hd hd)
    have hpg : IsPGroup 2 ↥(phi2 TV) :=
      hTVpg.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    obtain ⟨u, hu, hu1, hu2⟩ := exists_involution_of_ne_bot hpg hne
    have : u ∈ omega1 (phi2 TV) := Subgroup.subset_closure ⟨hu, hu2⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hu1 this
  have hTVab : IsElemAb2 TV := isElemAb2_of_sq hsq
  have hcard : Nat.card TV ≤ 8 := by
    have := h.rank_le TV hTVC hTVab
    norm_num at this
    exact this
  have hEq : V ⊔ Subgroup.zpowers x = TV :=
    Subgroup.eq_of_le_of_card_ge hETV (by rw [hE8]; exact hcard)
  rw [← hEq] at hTV
  exact hTV

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b

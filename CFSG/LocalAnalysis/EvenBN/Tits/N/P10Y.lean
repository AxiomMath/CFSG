module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P10Cnt
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P2bQ2
public import CFSG.LocalAnalysis.EvenBN.Tits.S56V2

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup

section Generic

variable {Γ : Type*} [Group Γ]

theorem node10_mem_normalizer_of_order_five {x : Γ} (hx : orderOf x = 5) {H : Subgroup Γ}
    (h : ∀ g ∈ H, x * g * x⁻¹ ∈ H) : x ∈ normalizer (H : Set Γ) := by
  have hx5 : x ^ 5 = 1 := by simpa [hx] using pow_orderOf_eq_one x
  have hiter : ∀ n : ℕ, ∀ g ∈ H, x ^ n * g * (x ^ n)⁻¹ ∈ H := by
    intro n
    induction n with
    | zero => intro g hg; simpa using hg
    | succ n ih =>
      intro g hg
      have e : x ^ (n + 1) * g * (x ^ (n + 1))⁻¹ = x ^ n * (x * g * x⁻¹) * (x ^ n)⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact ih _ (h g hg)
  rw [mem_normalizer_iff]
  intro g
  refine ⟨h g, fun hg => ?_⟩
  have h4 := hiter 4 _ hg
  have e : x ^ 4 * (x * g * x⁻¹) * (x ^ 4)⁻¹ = g := by
    have h5 : x ^ 4 * x = 1 := by rw [← pow_succ]; exact hx5
    calc x ^ 4 * (x * g * x⁻¹) * (x ^ 4)⁻¹ = (x ^ 4 * x) * g * (x ^ 4 * x)⁻¹ := by group
      _ = g := by rw [h5]; group
  rwa [e] at h4

theorem node10_psi_card [Finite Γ] {x z : Γ} (hx : orderOf x = 5) {V E : Subgroup Γ}
    (hxV : x ∈ normalizer (V : Set Γ)) (hV : Nat.card V = 2 ^ 10) (hE : Nat.card E = 2 ^ 5)
    (ψ : V →* Γ) (hψE : ∀ v, ψ v ∈ E)
    (hequiv : ∀ (v : V) (hv : x * (v : Γ) * x⁻¹ ∈ V), ψ ⟨x * v * x⁻¹, hv⟩ = x * ψ v * x⁻¹)
    (hfix : ∀ v : V, x * (v : Γ) = v * x → ψ v = 1) (hz2 : orderOf z = 2)
    (hxz : x * z = z * x) (hEfix : ∀ c ∈ E, x * c = c * x → c = 1 ∨ c = z) :
    z ∉ ψ.range ∧ (Nat.card ψ.range = 1 ∨ Nat.card ψ.range = 16) := by
  classical
  have hxVmem : ∀ v : Γ, v ∈ V → x * v * x⁻¹ ∈ V := fun v hv =>
    ((mem_normalizer_iff.1 hxV) v).1 hv
  set K : Subgroup Γ := ψ.ker.map V.subtype with hK
  have hKV : K ≤ V := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hmemK : ∀ g : Γ, g ∈ K ↔ ∃ h : g ∈ V, ψ ⟨g, h⟩ = 1 := by
    intro g
    rw [hK, Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨h, h1⟩
      exact ⟨⟨g, h⟩, h1, rfl⟩
  have hcardK : Nat.card ψ.ker = Nat.card K :=
    (Nat.card_congr (ψ.ker.equivMapOfInjective V.subtype (subtype_injective V)).toEquiv)
  have hxK : x ∈ normalizer (K : Set Γ) := by
    refine node10_mem_normalizer_of_order_five hx fun g hg => ?_
    obtain ⟨hgV, hg1⟩ := (hmemK g).1 hg
    have h2 := hxVmem g hgV
    refine (hmemK _).2 ⟨h2, ?_⟩
    rw [hequiv ⟨g, hgV⟩ h2, hg1]
    group
  have hmod : Nat.card V ≡ Nat.card K [MOD 5] :=
    S56.card_modEq_of_centralizer_le hx hKV le_rfl hxK hxV fun c hc hxc =>
      (hmemK c).2 ⟨hc, hfix ⟨c, hc⟩ hxc⟩
  have hRE : ψ.range ≤ E := by
    rintro _ ⟨v, rfl⟩
    exact hψE v
  obtain ⟨k, -, hk⟩ : ∃ k, k ≤ 10 ∧ Nat.card K = 2 ^ k :=
    (Nat.dvd_prime_pow Nat.prime_two).1 (hV ▸ Subgroup.card_dvd_of_le hKV)
  obtain ⟨r, hr5, hr⟩ : ∃ r, r ≤ 5 ∧ Nat.card ψ.range = 2 ^ r :=
    (Nat.dvd_prime_pow Nat.prime_two).1 (hE ▸ Subgroup.card_dvd_of_le hRE)
  have hprod := Subgroup.card_ker_mul_card_range ψ
  rw [hcardK, hk, hr, hV, ← pow_add] at hprod
  have hkr : k + r = 10 := Nat.pow_right_injective (le_refl 2) hprod
  have hmod' : 2 ^ 10 ≡ 2 ^ k [MOD 5] := by
    rw [← hV, ← hk]
    exact hmod
  have hcases : r = 0 ∨ r = 4 := by
    interval_cases r
    · exact Or.inl rfl
    · obtain rfl : k = 9 := by omega
      exact absurd hmod' (by decide)
    · obtain rfl : k = 8 := by omega
      exact absurd hmod' (by decide)
    · obtain rfl : k = 7 := by omega
      exact absurd hmod' (by decide)
    · exact Or.inr rfl
    · obtain rfl : k = 5 := by omega
      exact absurd hmod' (by decide)
  have hcard : Nat.card ψ.range = 1 ∨ Nat.card ψ.range = 16 := by
    rcases hcases with rfl | rfl
    · exact Or.inl (by rw [hr]; rfl)
    · exact Or.inr (by rw [hr]; rfl)
  refine ⟨fun hzR => ?_, hcard⟩
  have hxR : x ∈ normalizer (ψ.range : Set Γ) := by
    refine node10_mem_normalizer_of_order_five hx fun g hg => ?_
    obtain ⟨v, rfl⟩ := hg
    exact ⟨⟨x * v * x⁻¹, hxVmem v v.2⟩, hequiv v (hxVmem v v.2)⟩
  have hxZ : x ∈ normalizer ((zpowers z : Subgroup Γ) : Set Γ) := by
    refine node10_mem_normalizer_of_order_five hx fun g hg => ?_
    obtain ⟨n, rfl⟩ := hg
    have hc : Commute x z := hxz
    have e : x * z ^ n * x⁻¹ = z ^ n := by
      rw [(hc.zpow_right n).eq]
      group
    rw [e]
    exact zpow_mem_zpowers z n
  have hmodR := S56.card_modEq_of_centralizer_le hx (E := zpowers z) (K := ψ.range)
    (P := ψ.range) (zpowers_le.2 hzR) le_rfl hxZ hxR fun c hc hxc => by
      rcases hEfix c (hRE hc) hxc with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
  rw [Nat.card_zpowers, hz2] at hmodR
  rcases hcard with h1 | h1
  · rw [h1] at hmodR
    exact absurd hmodR (by decide)
  · rw [h1] at hmodR
    exact absurd hmodR (by decide)

end Generic

section Tits

open CFSG.Sporadic.Schreier.Tits

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem node10_y_cent_A (hd : d.Hyp) {y : G} (hy : IsV5 d y) :
    y ∈ centralizer (d.A : Set G) := by
  rw [CA_eq_A_sup_of_IsV5 hd hy]
  exact mem_sup_right (mem_zpowers _)

theorem node10_y_comm_E (hd : d.Hyp) {y : G} (hy : IsV5 d y) {e : G} (he : e ∈ d.E) :
    y * e = e * y :=
  (mem_centralizer_iff.1 (node10_y_cent_A hd hy) e (Data.s56_E_le_A d he)).symm

theorem node10_y_comm_t (hd : d.Hyp) {y : G} (hy : IsV5 d y) : y * d.t = d.t * y :=
  (mem_centralizer_iff.1 (node10_y_cent_A hd hy) d.t d.s56_t_mem_A).symm

theorem node10_y_comm_x5 (hd : d.Hyp) {y : G} (hy : IsV5 d y) : y * d.x₅ = d.x₅ * y := by
  obtain ⟨hyC, hyρ⟩ := hy
  have hXD : Model.hatX ∈ titsD := titsH_le_titsD Model.hatX_facts.1
  refine (hd.commute_lift_iff hyC hXD).2 ?_
  rw [hyρ]
  exact Model.hatX_facts.2.2.2.1

theorem node10_y_conj_pv7 (hd : d.Hyp) {y : G} (hy : IsV5 d y) :
    y * d.pv 7 * y⁻¹ = d.pv 7 * d.pv 11 := by
  obtain ⟨hyC, hyρ⟩ := hy
  have hv7F : Model.parrottV 7 ∈ Model.parrottF := Model.parrottV_mem_parrottF (by simp)
  have hv7D : Model.parrottV 7 ∈ titsD := Model.parrottF_le_titsD hv7F
  have hv11D : Model.parrottV 11 ∈ titsD :=
    Model.parrottF_le_titsD Model.parrottV_eleven_mem_parrottF
  have hrel : (d.ρ ⟨y, hyC⟩ : Equiv.Perm (Fin 1755)) * Model.parrottV 7 =
      (Model.parrottV 7 * Model.parrottV 11) * d.ρ ⟨y, hyC⟩ := by
    rw [hyρ]
    calc Model.parrottV 5 * Model.parrottV 7
        = (Model.parrottV 5 * Model.parrottV 7 * (Model.parrottV 5)⁻¹) * Model.parrottV 5 := by
          group
      _ = (Model.parrottV 7 * Model.parrottV 11) * Model.parrottV 5 := by
          rw [Model.parrottV_five_conj_seven]
  have h := hd.conj_lift_eq hyC hv7D (mul_mem hv7D hv11D) hrel
  rw [d.lift_mul hv7D hv11D] at h
  exact h

theorem node10_eps_conj {y : G} (hyt : y * d.t = d.t * y) (v : G) :
    d.s56Eps (y * v * y⁻¹) = y * d.s56Eps v * y⁻¹ := by
  have h1 : y⁻¹ * d.t * y = d.t := by
    calc y⁻¹ * d.t * y = y⁻¹ * (d.t * y) := by group
      _ = y⁻¹ * (y * d.t) := by rw [hyt]
      _ = d.t := by group
  show d.t * (y * v * y⁻¹ * d.t * (y * v * y⁻¹)⁻¹) = y * (d.t * (v * d.t * v⁻¹)) * y⁻¹
  calc d.t * (y * v * y⁻¹ * d.t * (y * v * y⁻¹)⁻¹)
      = d.t * (y * v * (y⁻¹ * d.t * y) * v⁻¹ * y⁻¹) := by group
    _ = d.t * (y * v * d.t * v⁻¹ * y⁻¹) := by rw [h1]
    _ = (d.t * y) * (v * d.t * v⁻¹) * y⁻¹ := by group
    _ = (y * d.t) * (v * d.t * v⁻¹) * y⁻¹ := by rw [hyt]
    _ = y * (d.t * (v * d.t * v⁻¹)) * y⁻¹ := by group

theorem node10_psi_mem_E (h49 : d.Thm49Statement) (hd : d.Hyp) {y : G} (hy : IsV5 d y)
    {v : G} (hv : v ∈ d.s56V) : y * v * y⁻¹ * v⁻¹ ∈ d.E := by
  have hyM : y ∈ d.M := Data.s56_centralizer_A_le_M d (node10_y_cent_A hd hy)
  have hg : y * v * y⁻¹ ∈ d.s56V := hd.s56_V_conj_mem h49 hyM hv
  have hεv : d.s56Eps v ∈ d.E := hd.s56_V_eps_mem_E hv
  have hε : d.s56Eps (y * v * y⁻¹) = d.s56Eps v := by
    rw [node10_eps_conj (node10_y_comm_t hd hy) v, node10_y_comm_E hd hy hεv]
    group
  have hvQ2 : v ∈ d.s56Q2 := Data.s56_V_le_Q2 d hv
  have hgQ2 : y * v * y⁻¹ ∈ d.s56Q2 := Data.s56_V_le_Q2 d hg
  have h1 : d.s56Eps (y * v * y⁻¹ * v⁻¹) = 1 := by
    rw [hd.s56_eps_mul_Q2' hgQ2 (inv_mem hvQ2), hε, hd.s56_eps_inv_Q2 hvQ2]
    exact hd.s56_E_sq hεv
  exact (hd.s56_V_eps_eq_one_iff h49 (mul_mem hg (inv_mem hv))).1 h1

theorem node10_psi_mul (h49 : d.Thm49Statement) (hd : d.Hyp) {y : G} (hy : IsV5 d y)
    {v w : G} (hv : v ∈ d.s56V) (hw : w ∈ d.s56V) :
    y * (v * w) * y⁻¹ * (v * w)⁻¹ = (y * v * y⁻¹ * v⁻¹) * (y * w * y⁻¹ * w⁻¹) := by
  have hc : v * (y * w * y⁻¹ * w⁻¹) = (y * w * y⁻¹ * w⁻¹) * v :=
    Data.s56_V_comm_E hv (node10_psi_mem_E h49 hd hy hw)
  calc y * (v * w) * y⁻¹ * (v * w)⁻¹
      = (y * v * y⁻¹ * v⁻¹) * (v * (y * w * y⁻¹ * w⁻¹) * v⁻¹) := by group
    _ = (y * v * y⁻¹ * v⁻¹) * (y * w * y⁻¹ * w⁻¹) := by rw [hc]; group

theorem node10_t_mul_not_central (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) {v : G} (hv : v ∈ d.s56V)
    (hcen : ∀ u ∈ d.s56V, d.t * v * u = u * (d.t * v)) : False := by
  have hnot : ∃ e ∈ d.E, e ∉ zpowers d.z := by
    by_contra hall
    push_neg at hall
    have hle : d.E ≤ zpowers d.z := hall
    have := Subgroup.card_dvd_of_le hle
    rw [hd.A_facts.1, hd.s56_card_zpowers_z] at this
    norm_num at this
  obtain ⟨e, he, hez⟩ := hnot
  obtain ⟨u, hu, hue⟩ := hd.s56_V_eps_surj h49 hz e he
  apply hez
  have h1 := hcen u hu
  have hc := hd.s56_V_comm_mem h49 hz hv hu
  have e1 : u * d.t * u⁻¹ = d.t * (v * u * v⁻¹ * u⁻¹) := by
    calc u * d.t * u⁻¹ = (u * (d.t * v)) * v⁻¹ * u⁻¹ := by group
      _ = (d.t * v * u) * v⁻¹ * u⁻¹ := by rw [h1]
      _ = d.t * (v * u * v⁻¹ * u⁻¹) := by group
  have e2 : d.s56Eps u = v * u * v⁻¹ * u⁻¹ := by
    show d.t * (u * d.t * u⁻¹) = _
    rw [e1]
    calc d.t * (d.t * (v * u * v⁻¹ * u⁻¹)) = (d.t * d.t) * (v * u * v⁻¹ * u⁻¹) := by group
      _ = _ := by rw [hd.t_mul_self, one_mul]
  rw [← hue, e2]
  exact hc

theorem node10_mem_E_of_comm_t (h49 : d.Thm49Statement) (hd : d.Hyp) {v : G}
    (hv : v ∈ d.s56V) (hvt : v * d.t = d.t * v) : v ∈ d.E := by
  have h1 : v * d.t * v⁻¹ = d.t := by
    calc v * d.t * v⁻¹ = d.t * v * v⁻¹ := by rw [hvt]
      _ = d.t := by group
  refine (hd.s56_V_eps_eq_one_iff h49 hv).1 ?_
  show d.t * (v * d.t * v⁻¹) = 1
  rw [h1]
  exact hd.t_mul_self

theorem node10_y_comm_V (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    {y : G} (hy : IsV5 d y) (hyz : y * z₀ = z₀ * y) : ∀ v ∈ d.s56V, y * v = v * y := by
  have hyM : y ∈ d.M := Data.s56_centralizer_A_le_M d (node10_y_cent_A hd hy)
  have hyx := node10_y_comm_x5 hd hy
  let ψ : d.s56V →* G := MonoidHom.mk' (fun v => y * (v : G) * y⁻¹ * (v : G)⁻¹) fun v w => by
    have := node10_psi_mul h49 hd hy v.2 w.2
    simpa using this
  have hψ : ∀ v : d.s56V, ψ v = y * (v : G) * y⁻¹ * (v : G)⁻¹ := fun v => rfl
  have hψE : ∀ v : d.s56V, ψ v ∈ d.E := fun v => node10_psi_mem_E h49 hd hy v.2
  have hequiv : ∀ (v : d.s56V) (hv : d.x₅ * (v : G) * d.x₅⁻¹ ∈ d.s56V),
      ψ ⟨d.x₅ * v * d.x₅⁻¹, hv⟩ = d.x₅ * ψ v * d.x₅⁻¹ := by
    intro v hv
    rw [hψ, hψ]
    calc y * (d.x₅ * (v : G) * d.x₅⁻¹) * y⁻¹ * (d.x₅ * (v : G) * d.x₅⁻¹)⁻¹
        = (y * d.x₅) * (v : G) * (y * d.x₅)⁻¹ * d.x₅ * (v : G)⁻¹ * d.x₅⁻¹ := by group
      _ = (d.x₅ * y) * (v : G) * (d.x₅ * y)⁻¹ * d.x₅ * (v : G)⁻¹ * d.x₅⁻¹ := by rw [hyx]
      _ = d.x₅ * (y * (v : G) * y⁻¹ * (v : G)⁻¹) * d.x₅⁻¹ := by group
  have hz₀ : z₀ ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.2 hyz.symm
  have hzy : d.z ∈ centralizer ({y} : Set G) :=
    mem_centralizer_singleton_iff.2 (node10_y_comm_E hd hy hd.s56_z_mem_E).symm
  have hle : zpowers d.z ⊔ zpowers z₀ ≤ centralizer ({y} : Set G) :=
    sup_le (zpowers_le.2 hzy) (zpowers_le.2 hz₀)
  have hfix : ∀ v : d.s56V, d.x₅ * (v : G) = v * d.x₅ → ψ v = 1 := by
    intro v hxv
    have hvc : (v : G) ∈ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      rintro g ⟨n, rfl⟩
      exact (Commute.zpow_left (show Commute d.x₅ (v : G) from hxv) n).eq
    have hmem : (v : G) ∈ d.s56Q ⊓ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) :=
      mem_inf.2 ⟨v.2.1, hvc⟩
    rw [hd.s56_CQX_eq h49 hz.mem_Q hz.mem_Q2 hz.eps hz.comm_x hz.dich] at hmem
    have h1 : (v : G) * y = y * v := mem_centralizer_singleton_iff.1 (hle hmem)
    rw [hψ]
    calc y * (v : G) * y⁻¹ * (v : G)⁻¹ = (v : G) * y * y⁻¹ * (v : G)⁻¹ := by rw [← h1]
      _ = 1 := by group
  have hEfix : ∀ c ∈ d.E, d.x₅ * c = c * d.x₅ → c = 1 ∨ c = d.z := fun c hc hxc =>
    hd.s56_mem_zpowers_z (hd.s56_E_cent_x5 hc hxc.symm)
  obtain ⟨hzR, hcard⟩ := node10_psi_card hd.s56_orderOf_x5
    (hd.s56_M_le_normalizer_V h49 hd.s56_x5_mem_M) (hd.s56_card_V h49 hz)
    (by rw [hd.A_facts.1]; norm_num) ψ hψE hequiv hfix hd.s56_orderOf_z hd.s56_x5_comm_z hEfix
  have hv7Q0 : d.pv 7 ∈ d.s56Q0 := hd.s56_Q_le_Q0 (hd.s56_F_le_Q h49 hd.s56_pv7_mem_F)
  have hv7M : d.pv 7 ∈ d.M := hd.s56_Q0_le_M h49 hv7Q0
  have hv7L : d.pv 7 ∈ d.L := Data.s56_F_le_L d hd.s56_pv7_mem_F
  have hv11E : d.pv 11 ∈ d.E := Data.s56_pv11_mem_E d
  have hRH : ψ.range ≤ d.E ⊓ centralizer ({d.pv 7} : Set G) := by
    rintro _ ⟨v, rfl⟩
    refine mem_inf.2 ⟨hψE v, mem_centralizer_singleton_iff.2 ?_⟩
    have hw : (d.pv 7)⁻¹ * (v : G) * (d.pv 7) ∈ d.s56V := by
      simpa using hd.s56_V_conj_mem h49 (inv_mem hv7M) v.2
    have hconj : (d.pv 7)⁻¹ * y * d.pv 7 = d.pv 11 * y := by
      have h := node10_y_conj_pv7 hd hy
      calc (d.pv 7)⁻¹ * y * d.pv 7 = (d.pv 7)⁻¹ * (y * d.pv 7 * y⁻¹) * y := by group
        _ = d.pv 11 * y := by rw [h]; group
    have hconj' : (d.pv 7)⁻¹ * y⁻¹ * d.pv 7 = (d.pv 11 * y)⁻¹ := by
      rw [← hconj]
      group
    have hcomm11 : d.pv 11 * (y * ((d.pv 7)⁻¹ * (v : G) * d.pv 7) * y⁻¹) =
        (y * ((d.pv 7)⁻¹ * (v : G) * d.pv 7) * y⁻¹) * d.pv 11 := by
      have hg : y * ((d.pv 7)⁻¹ * (v : G) * d.pv 7) * y⁻¹ ∈ d.s56V := by
        simpa [mul_assoc] using hd.s56_V_conj_mem h49 hyM hw
      exact (Data.s56_V_comm_E hg hv11E).symm
    have hkey : (d.pv 7)⁻¹ * ψ v * d.pv 7 = ψ ⟨(d.pv 7)⁻¹ * (v : G) * d.pv 7, hw⟩ := by
      rw [hψ, hψ]
      show (d.pv 7)⁻¹ * (y * (v : G) * y⁻¹ * (v : G)⁻¹) * d.pv 7 =
        y * ((d.pv 7)⁻¹ * (v : G) * d.pv 7) * y⁻¹ * ((d.pv 7)⁻¹ * (v : G) * d.pv 7)⁻¹
      calc (d.pv 7)⁻¹ * (y * (v : G) * y⁻¹ * (v : G)⁻¹) * d.pv 7
          = ((d.pv 7)⁻¹ * y * d.pv 7) * ((d.pv 7)⁻¹ * (v : G) * d.pv 7) *
              ((d.pv 7)⁻¹ * y⁻¹ * d.pv 7) * ((d.pv 7)⁻¹ * (v : G) * d.pv 7)⁻¹ := by group
        _ = (d.pv 11 * y) * ((d.pv 7)⁻¹ * (v : G) * d.pv 7) * (d.pv 11 * y)⁻¹ *
              ((d.pv 7)⁻¹ * (v : G) * d.pv 7)⁻¹ := by rw [hconj, hconj']
        _ = d.pv 11 * (y * ((d.pv 7)⁻¹ * (v : G) * d.pv 7) * y⁻¹) * (d.pv 11)⁻¹ *
              ((d.pv 7)⁻¹ * (v : G) * d.pv 7)⁻¹ := by group
        _ = y * ((d.pv 7)⁻¹ * (v : G) * d.pv 7) * y⁻¹ *
              ((d.pv 7)⁻¹ * (v : G) * d.pv 7)⁻¹ := by rw [hcomm11]; group
    have hr' : (d.pv 7)⁻¹ * ψ v * d.pv 7 ∈ ψ.range := by
      rw [hkey]
      exact ⟨_, rfl⟩
    have hc1 : (d.pv 7)⁻¹ * ψ v * d.pv 7 * (ψ v)⁻¹ ∈ zpowers d.z := by
      have h := ((hd.s56_mem_Q0_iff h49).1 (inv_mem hv7Q0)).2 _ (hψE v)
      simpa using h
    have hc2 : (d.pv 7)⁻¹ * ψ v * d.pv 7 * (ψ v)⁻¹ ∈ ψ.range :=
      mul_mem hr' (inv_mem ⟨v, rfl⟩)
    have hc3 : (d.pv 7)⁻¹ * ψ v * d.pv 7 * (ψ v)⁻¹ = 1 := by
      rcases hd.s56_mem_zpowers_z hc1 with h | h
      · exact h
      · exact absurd (h ▸ hc2) hzR
    calc ψ v * d.pv 7 = d.pv 7 * ((d.pv 7)⁻¹ * ψ v * d.pv 7 * (ψ v)⁻¹) * ψ v := by group
      _ = d.pv 7 * ψ v := by rw [hc3]; group
  have hHcard : Nat.card (d.E ⊓ centralizer ({d.pv 7} : Set G) : Subgroup G) ≤ 16 := by
    have hne : d.E ⊓ centralizer ({d.pv 7} : Set G) ≠ d.E := by
      intro h
      have hEc : ∀ e ∈ d.E, e * d.pv 7 = d.pv 7 * e := fun e he =>
        mem_centralizer_singleton_iff.1
          (mem_inf.1 (by rw [h]; exact he : e ∈ d.E ⊓ centralizer ({d.pv 7} : Set G))).2
      have hv7A : d.pv 7 ∈ centralizer (d.A : Set G) :=
        (hd.s56_mem_centralizer_A_iff).2 ⟨hEc, hd.L_comm_t hv7L⟩
      exact hd.s56_pv7_not_mem_E (hd.s56_C_inf_L hv7A hv7L)
    obtain ⟨j, hj5, hj⟩ : ∃ j, j ≤ 5 ∧
        Nat.card (d.E ⊓ centralizer ({d.pv 7} : Set G) : Subgroup G) = 2 ^ j :=
      (Nat.dvd_prime_pow Nat.prime_two).1
        ((hd.A_facts.1 ▸ Subgroup.card_dvd_of_le inf_le_left : _ ∣ 32))
    by_contra hgt
    have hj' : j = 5 := by
      by_contra hne5
      have : j ≤ 4 := by omega
      have : 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
      omega
    apply hne
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [hd.A_facts.1, hj, hj']
    norm_num
  have hzH : d.z ∈ d.E ⊓ centralizer ({d.pv 7} : Set G) :=
    mem_inf.2 ⟨hd.s56_z_mem_E, mem_centralizer_singleton_iff.2 (hd.s56_M_comm_z hv7M).symm⟩
  have hR1 : Nat.card ψ.range = 1 := by
    rcases hcard with h | h
    · exact h
    · exfalso
      have hEq : ψ.range = d.E ⊓ centralizer ({d.pv 7} : Set G) :=
        Subgroup.eq_of_le_of_card_ge hRH (by omega)
      exact hzR (hEq ▸ hzH)
  have hbot : ψ.range = ⊥ := Subgroup.eq_bot_of_card_eq _ hR1
  intro v hv
  have h1 : ψ ⟨v, hv⟩ = 1 := by
    have : ψ ⟨v, hv⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have h2 : y * v * y⁻¹ * v⁻¹ = 1 := h1
  calc y * v = (y * v * y⁻¹ * v⁻¹) * (v * y) := by group
    _ = v * y := by rw [h2, one_mul]

theorem node10_part_C (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (ht9 : d.t ∉ sylT d ⊓ centralizer ({z₀} : Set G)) :
    ∀ y, IsV5 d y → y ∈ sylT d → y * z₀ = z₀ * y →
      (∀ q ∈ d.s56Q2, y * q = q * y) ∧
        (Subgroup.center ↥d.s56Q2).map d.s56Q2.subtype = d.E ⊔ zpowers y := by
  intro y hy hyT hyz
  have hQ := node10_Q2_eq_Â h49 hd hz hy
  have hy2 : y * y = d.z := P2b.y_sq hd hz hy hyT hyz ht9
  have hcV := node10_y_comm_V h49 hd hz hy hyz
  have hyc : ∀ q ∈ d.s56Q2, y * q = q * y := by
    intro q hq
    have hle : d.s56Q2 ≤ centralizer ({y} : Set G) := by
      rw [hQ]
      refine sup_le (sup_le (fun v hv => mem_centralizer_singleton_iff.2 (hcV v hv).symm) ?_) ?_
      · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 (node10_y_comm_t hd hy).symm)
      · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
    exact (mem_centralizer_singleton_iff.1 (hle hq)).symm
  refine ⟨hyc, le_antisymm ?_ ?_⟩
  ·
    rintro _ ⟨⟨q, hq⟩, hqc, rfl⟩
    have hcent : ∀ u ∈ d.s56Q2, u * q = q * u := fun u hu =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hqc ⟨u, hu⟩)
    have htQ2 : d.t ∈ d.s56Q2 := t_mem_Q2 hd
    show q ∈ d.E ⊔ zpowers y
    rcases P2b.Q2_cases_top h49 hd hQ hyc hy2 hq with hv | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ |
        ⟨v, hv, rfl⟩
    · exact mem_sup_left (node10_mem_E_of_comm_t h49 hd hv (hcent d.t htQ2).symm)
    · exact (node10_t_mul_not_central h49 hd hz hv fun u hu =>
        (hcent u (Data.s56_V_le_Q2 d hu)).symm).elim
    · refine mul_mem (mem_sup_right (mem_zpowers y)) (mem_sup_left ?_)
      refine node10_mem_E_of_comm_t h49 hd hv ?_
      have h1 := hcent d.t htQ2
      have h2 : y * (d.t * v) = y * (v * d.t) := by
        calc y * (d.t * v) = (y * d.t) * v := by group
          _ = (d.t * y) * v := by rw [node10_y_comm_t hd hy]
          _ = d.t * (y * v) := by group
          _ = y * v * d.t := h1
          _ = y * (v * d.t) := by group
      exact (mul_left_cancel h2).symm
    · refine (node10_t_mul_not_central h49 hd hz hv fun u hu => ?_).elim
      have h1 := hcent u (Data.s56_V_le_Q2 d hu)
      have h2 : y * (d.t * v * u) = y * (u * (d.t * v)) := by
        calc y * (d.t * v * u) = y * (d.t * v) * u := by group
          _ = u * (y * (d.t * v)) := h1.symm
          _ = (u * y) * (d.t * v) := by group
          _ = (y * u) * (d.t * v) := by rw [(hcV u hu).symm]
          _ = y * (u * (d.t * v)) := by group
      exact mul_left_cancel h2
  ·
    have hyQ2 : y ∈ d.s56Q2 := (Data.s56_mem_Q2_iff).2
      ⟨Data.s56_centralizer_A_le_M d (node10_y_cent_A hd hy),
        fun e he => (node10_y_comm_E hd hy he).symm⟩
    refine sup_le (fun e he => ?_) (zpowers_le.2 ?_)
    · refine ⟨⟨e, hd.s56_E_le_Q2 he⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
      exact Subtype.ext (((Data.s56_mem_Q2_iff).1 g.2).2 e he).symm
    · refine ⟨⟨y, hyQ2⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
      exact Subtype.ext (hyc g g.2).symm

end Tits

end CFSG.LocalAnalysis.EvenBN.Tits.N

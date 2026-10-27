module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenRep
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenTransl
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenWire
import CFSG.ClassicalInvolution.Asc77.AscP1SevenCliqueEng

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem two_mul_card_le_of_le_of_ne {Q : Type*} [Group Q] [Finite Q] {H₀ H₁ : Subgroup Q}
    (hle : H₀ ≤ H₁) (hne : H₀ ≠ H₁) : 2 * Nat.card H₀ ≤ Nat.card H₁ := by
  exact T8V.two_mul_card_le_of_le_of_neE hle hne

@[expose] def Ctx.U4 (c : Ctx p f Ω W) (ρ : Rep Ω W) : Subgroup G := ρ.K ⊓ c.W4

@[expose] def Ctx.UU (c : Ctx p f Ω W) {ι : Type*} (ρ : ι → Rep Ω W) (S : Set ι) : Subgroup G :=
  Subgroup.closure {x | ∃ s ∈ S, x ∈ c.U4 (ρ s)}

private theorem cliqueHooks (c : Ctx p f Ω W) : T8V.CliqueHooks Ω W c.W4 where
  toRepHooks := T8V.RepHooks.ofCtx c
  W4_le := c.W4_le
  conj_mem_W4 := fun hr => fun hx => c.conj_mem_W4 hr hx
  img_eq_of_K_eq := fun ρ σ h => c.img_eq_of_K_eq ρ σ h
  K_eq_of_img_eq := fun ρ σ h => c.K_eq_of_img_eq ρ σ h
  omega_of_comm := fun ρ σ hne hcomm => c.omega_of_comm ρ σ hne hcomm
  comm_of_omega := fun ρ σ h => c.comm_of_omega ρ σ h
  comm_mem := fun ρ σ hne => fun hv => c.comm_mem ρ σ hne hv
  conjInv := fun g K hK => c.hΩ.conjInvariant g K hK
  conjD := fun hR => fun hn => conjSub_mem_D c.hΩ hR hn

namespace Ctx

variable (c : Ctx p f Ω W)

theorem mem_U4 {ρ : Rep Ω W} {x : G} : x ∈ c.U4 ρ ↔ x ∈ ρ.K ∧ x ∈ W ∧ x ^ 4 = 1 := Iff.rfl

theorem U4_le_W (ρ : Rep Ω W) : c.U4 ρ ≤ W :=
  T8V.U4_le_WE (cliqueHooks c) ρ

theorem mem_inf_of_mem_U4 {ρ : Rep Ω W} {x : G} (hx : x ∈ c.U4 ρ) : x ∈ ρ.K ⊓ W :=
  T8V.mem_inf_of_mem_U4E (cliqueHooks c) hx

theorem U4_le_UU {ι : Type*} (ρ : ι → Rep Ω W) {S : Set ι} {s : ι} (hs : s ∈ S) :
    c.U4 (ρ s) ≤ c.UU ρ S :=
  T8V.U4_le_UUE (cliqueHooks c) ρ hs

theorem UU_le_W4 {ι : Type*} (ρ : ι → Rep Ω W) (S : Set ι) : c.UU ρ S ≤ c.W4 := by
  exact T8V.UU_le_W4E (cliqueHooks c) ρ S

theorem conj_mem_U4 (ρ σ : Rep Ω W) {x : G} (hx : x ∈ c.U4 σ) :
    ρ.r * x * ρ.r⁻¹ ∈ c.U4 ρ ⊔ c.U4 σ := by
  exact T8V.conj_mem_U4E (cliqueHooks c) ρ σ hx

theorem normalizes_UU {ι : Type*} (ρ : ι → Rep Ω W) {S : Set ι} {s : ι} (hs : s ∈ S) :
    (ρ s).r ∈ Subgroup.normalizer ((c.UU ρ S : Subgroup G) : Set G) := by
  exact T8V.normalizes_UUE (cliqueHooks c) ρ hs

theorem exists_mul_of_mem_UU_insert {ι : Type*} (ρ : ι → Rep Ω W) {B : Set ι} {a : ι} {g : G}
    (hg : g ∈ c.UU ρ (insert a B)) :
    ∃ x ∈ c.U4 (ρ a), ∃ a₁ ∈ c.UU ρ B, g = x * a₁ := by
  exact T8V.exists_mul_of_mem_UU_insertE (cliqueHooks c) ρ hg

section Frame

variable (rep : ↥(muGroup Ω W) → Rep Ω W)
  (hrep : ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)))
include c hrep

theorem rep_K_ne {x y : ↥(muGroup Ω W)} (hx : x ∈ muDelta Ω W) (hy : y ∈ muDelta Ω W)
    (hne : x ≠ y) : (rep x).K ≠ (rep y).K := by
  exact T8V.rep_K_neE (cliqueHooks c) rep hrep hx hy hne

theorem rep_omega {x y : ↥(muGroup Ω W)} (hx : x ∈ muDelta Ω W) (hy : y ∈ muDelta Ω W)
    (hne : x ≠ y) (hcomm : x * y = y * x) : (rep y).K ∈ omegaNbr Ω (rep x).K := by
  exact T8V.rep_omegaE (cliqueHooks c) rep hrep hx hy hne hcomm

theorem rep_noncomm {x y : ↥(muGroup Ω W)} (hx : x ∈ muDelta Ω W) (hy : y ∈ muDelta Ω W)
    (hnc : x * y ≠ y * x) : (rep x).K ≠ (rep y).K ∧ (rep y).K ∉ omegaNbr Ω (rep x).K := by
  exact T8V.rep_noncommE (cliqueHooks c) rep hrep hx hy hnc

theorem centralizes_UU {x : ↥(muGroup Ω W)} (hx : x ∈ muDelta Ω W) {S : Set ↥(muGroup Ω W)}
    (hS : ∀ s ∈ S, s ∈ muDelta Ω W ∧ x ≠ s ∧ x * s = s * x) :
    ∀ g ∈ c.UU rep S, (rep x).r * g * (rep x).r⁻¹ = g := by
  exact T8V.centralizes_UUE (cliqueHooks c) rep hrep hx hS

theorem U4_le_UU_of_generates {a d : ↥(muGroup Ω W)} {B : Finset ↥(muGroup Ω W)}
    (hBΔ : (↑B : Set ↥(muGroup Ω W)) ⊆ muDelta Ω W) (haΔ : a ∈ muDelta Ω W) (hdB : d ∈ B)
    (hgen : Subgroup.closure (insert a (↑B : Set ↥(muGroup Ω W))) = ⊤)
    (hconj : ∀ y ∈ muDelta Ω W, ∃ q : ↥(muGroup Ω W), y = q * d * q⁻¹)
    {y : ↥(muGroup Ω W)} (hy : y ∈ muDelta Ω W) :
    c.U4 (rep y) ≤ c.UU rep (insert a (↑B : Set ↥(muGroup Ω W))) := by
  exact T8V.U4_le_UU_of_generatesE (cliqueHooks c) rep hrep hBΔ haΔ hdB hgen hconj hy

theorem clique_subset {a d P : ↥(muGroup Ω W)} {B : Finset ↥(muGroup Ω W)}
    (hcfg : Star3T.Cfg (muDelta Ω W) d a)
    (hBC : (↑B : Set ↥(muGroup Ω W)) ⊆ Star3T.cent (muDelta Ω W) d) (hdB : d ∈ B)
    (hgen : Subgroup.closure (insert a (↑B : Set ↥(muGroup Ω W))) = ⊤)
    (hP : P ∈ Star3T.cent (muDelta Ω W) d) (hPB : P ∉ B) :
    ∀ P' ∈ Star3T.cent (muDelta Ω W) d, P' ≠ P → P' ∈ B := by
  intro P' hP' hne
  by_contra hP'B
  have hBΔ : (↑B : Set ↥(muGroup Ω W)) ⊆ muDelta Ω W := fun x hx => (hBC hx).1
  have haΔ := hcfg.mem_a
  have hconj := hcfg.tt.exists_conj_of_not_conn hcfg.mem_d hcfg.mem_a hcfg.not_conn
  have hPΔ : P ∈ muDelta Ω W := hP.1
  have hP'Δ : P' ∈ muDelta Ω W := hP'.1
  obtain ⟨u, huRW, hu4⟩ := exists_orderOf_four c.hp c.hq c.hΩ c.hW (rep P).hR
  obtain ⟨hRW, -, -, -, -⟩ := inf_W_of_mem_D c.hp c.hq c.hΩ c.hW (rep P).hR (rep P).hK (rep P).hRK
  have huKW : u ∈ (rep P).K ⊓ W := by rw [← hRW]; exact huRW
  have hu_pow : u ^ 4 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu4] at this
  have hu2 : u * u ≠ 1 := fun h => by
    have h1 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hu4] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have huW : u ∈ W := huKW.2
  obtain ⟨z, hz⟩ := c.hΩ.exists_uniqueInvolution c.hp c.hq (rep P).hK
  have h4' : (u * u) * (u * u) = 1 := by
    calc (u * u) * (u * u) = u ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hu_pow
  have hzu : u * u = z :=
    (hz.unique (u * u) ((rep P).K.mul_mem huKW.1 huKW.1) h4').resolve_left hu2
  have huW₀ : u ∈ c.UU rep (insert a (↑B : Set ↥(muGroup Ω W))) :=
    c.U4_le_UU_of_generates rep hrep hBΔ haΔ hdB hgen hconj hPΔ ⟨huKW.1, huW, hu_pow⟩
  obtain ⟨x, hx, a₁, ha₁, hu_eq⟩ := c.exists_mul_of_mem_UU_insert rep huW₀
  have hxW : x ∈ W := c.U4_le_W _ hx
  have ha₁W : a₁ ∈ W := c.W4_le (c.UU_le_W4 rep _ ha₁)
  have hpA : ∀ g ∈ c.UU rep (↑B : Set ↥(muGroup Ω W)),
      (rep P).r * g * (rep P).r⁻¹ = g :=
    c.centralizes_UU rep hrep hPΔ (fun s hs => ⟨hBΔ hs, fun e => hPB (e ▸ hs),
      hcfg.comm_cent hP (hBC hs)⟩)
  have h1 : (rep P).r * u * (rep P).r⁻¹ = u⁻¹ := c.conj_inv (rep P) huKW
  have h2 : (rep P).r * a₁ * (rep P).r⁻¹ = a₁ := hpA a₁ ha₁
  have hx_eq : x = u * a₁⁻¹ := by rw [hu_eq]; group
  have hpx : (rep P).r * x * (rep P).r⁻¹ = u⁻¹ * a₁⁻¹ := by
    calc (rep P).r * x * (rep P).r⁻¹ = (rep P).r * (u * a₁⁻¹) * (rep P).r⁻¹ := by rw [← hx_eq]
      _ = ((rep P).r * u * (rep P).r⁻¹) * ((rep P).r * a₁ * (rep P).r⁻¹)⁻¹ := by group
      _ = u⁻¹ * a₁⁻¹ := by rw [h1, h2]
  obtain ⟨za, hza⟩ := c.hΩ.exists_uniqueInvolution c.hp c.hq (rep a).hK
  have hPa : P * a ≠ a * P := hcfg.noncomm_a hP
  obtain ⟨hKPa, hnotPa⟩ := c.rep_noncomm rep hrep hPΔ haΔ hPa
  have hx2 : x * x = 1 := by
    by_contra hx2
    have hxx4 : (x * x) * (x * x) = 1 := by
      calc (x * x) * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := hx.2.2
    have hxza : x * x = za :=
      (hza.unique (x * x) ((rep a).K.mul_mem hx.1 hx.1) hxx4).resolve_left hx2
    have hc : Commute u a₁⁻¹ := c.comm_W u huW a₁⁻¹ (W.inv_mem ha₁W)
    have hu2inv : (u ^ 2)⁻¹ = u ^ 2 := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add]
      exact hu_pow
    have hpxx : (rep P).r * (x * x) * (rep P).r⁻¹ = x * x := by
      calc (rep P).r * (x * x) * (rep P).r⁻¹
          = ((rep P).r * x * (rep P).r⁻¹) * ((rep P).r * x * (rep P).r⁻¹) := by group
        _ = (u⁻¹ * a₁⁻¹) * (u⁻¹ * a₁⁻¹) := by rw [hpx]
        _ = (u⁻¹) ^ 2 * (a₁⁻¹) ^ 2 := by rw [← pow_two, hc.inv_left.mul_pow]
        _ = u ^ 2 * (a₁⁻¹) ^ 2 := by rw [inv_pow, hu2inv]
        _ = (u * a₁⁻¹) * (u * a₁⁻¹) := by rw [← pow_two, hc.mul_pow]
        _ = x * x := by rw [← hx_eq]
    have hconj_za := c.conj_involution (rep P) (rep a) hKPa hnotPa hz hza
    rw [← hxza, hpxx, hxza] at hconj_za
    have : z = 1 := by
      have h3 : z * za = 1 * za := by rw [← hconj_za, one_mul]
      exact mul_right_cancel h3
    exact hz.ne_one this
  have hx1 : x ≠ 1 := by
    intro hx1
    have hu_a : u = a₁ := by rw [hu_eq, hx1, one_mul]
    have h3 : (rep P).r * u * (rep P).r⁻¹ = u := by rw [hu_a]; exact hpA a₁ ha₁
    rw [h3] at h1
    apply hu2
    calc u * u = u⁻¹ * u := congrArg (· * u) h1
      _ = 1 := inv_mul_cancel u
  have hxza : x = za := (hza.unique x hx.1 hx2).resolve_left hx1
  obtain ⟨z', hz'⟩ := c.hΩ.exists_uniqueInvolution c.hp c.hq (rep P').hK
  have hP'a : P' * a ≠ a * P' := hcfg.noncomm_a hP'
  obtain ⟨hKP'a, hnotP'a⟩ := c.rep_noncomm rep hrep hP'Δ haΔ hP'a
  have hnbr : (rep P).K ∈ omegaNbr Ω (rep P').K :=
    c.rep_omega rep hrep hP'Δ hPΔ hne (hcfg.comm_cent hP' hP)
  have hy_u : (rep P').r * u * (rep P').r⁻¹ = u := by
    have := c.centralizes (rep P') (rep P) hnbr huKW
    rw [this]
    group
  have hy_a : (rep P').r * a₁ * (rep P').r⁻¹ = a₁ :=
    c.centralizes_UU rep hrep hP'Δ (fun s hs => ⟨hBΔ hs, fun e => hP'B (e ▸ hs),
      hcfg.comm_cent hP' (hBC hs)⟩) a₁ ha₁
  have hy_za := c.conj_involution (rep P') (rep a) hKP'a hnotP'a hz' hza
  have hu_za : u = za * a₁ := by rw [hu_eq, hxza]
  have h5 : (rep P').r * u * (rep P').r⁻¹ = (z' * za) * a₁ := by
    calc (rep P').r * u * (rep P').r⁻¹
        = ((rep P').r * za * (rep P').r⁻¹) * ((rep P').r * a₁ * (rep P').r⁻¹) := by
          rw [hu_za]; group
      _ = (z' * za) * a₁ := by rw [hy_za, hy_a]
  rw [hy_u, hu_za] at h5
  have h6 : z' * za = za := mul_right_cancel h5.symm
  exact hz'.ne_one (mul_eq_right.mp h6)

theorem not_mem_closure {x : ↥(muGroup Ω W)} (hx : x ∈ muDelta Ω W)
    {S : Set ↥(muGroup Ω W)} (hS : ∀ s ∈ S, s ∈ muDelta Ω W ∧ x ≠ s ∧ x * s = s * x) :
    x ∉ Subgroup.closure S := by
  intro hxS
  set L : Set G := {g | ∃ s ∈ S, g = (rep s).r} with hL
  have hLN : L ⊆ Subgroup.normalizer (W : Set G) := by
    rintro _ ⟨s, -, rfl⟩
    exact (rep s).r_mem_normalizer
  have hq' : (x : NQuot (W ⊔ OCW W)) ∈ Subgroup.closure (piG W '' L) := by
    have h1 := Subgroup.mem_map_of_mem (muGroup Ω W).subtype hxS
    rw [MonoidHom.map_closure] at h1
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨(rep s).r, ⟨s, hs, rfl⟩, hrep s (hS s hs).1⟩
  obtain ⟨g, hg, hgx⟩ := exists_mem_closure_of_mem_closure_piG hLN hq'
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := ((Subgroup.closure_le _).mpr hLN) hg
  obtain ⟨hRW, -, hcyc, h4, -⟩ :=
    inf_W_of_mem_D c.hp c.hq c.hΩ c.hW (rep x).hR (rep x).hK (rep x).hRK
  obtain ⟨v, hvU, hv2⟩ := exists_sq_ne_one hcyc (by omega)
  have hvKW : v ∈ (rep x).K ⊓ W := by rw [← hRW]; exact hvU
  have hgv : g * v * g⁻¹ = v := by
    have hcl : Subgroup.closure L ≤ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨hsΔ, hxs, hcomm⟩ := hS s hs
      have hnbr := c.rep_omega rep hrep hsΔ hx hxs.symm hcomm.symm
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact c.centralizes (rep s) (rep x) hnbr hvKW
    have := Subgroup.mem_centralizer_singleton_iff.mp (hcl hg)
    rw [this]
    group
  have h1 : (rep x).r * v * (rep x).r⁻¹ = v⁻¹ := c.conj_inv (rep x) hvKW
  have h2 : (rep x).r * v * (rep x).r⁻¹ = g * v * g⁻¹ := by
    refine conj_eq_of_piG_eq c.hp c.hq c.hΩ c.hW hgN (rep x).r_mem_normalizer ?_ hvKW.2
    rw [hgx]
    exact (hrep x hx).symm
  rw [h1, hgv] at h2
  apply hv2
  calc v * v = v⁻¹ * v := congrArg (· * v) h2.symm
    _ = 1 := inv_mul_cancel v

theorem two_pow_card_le_closure (S : Finset ↥(muGroup Ω W))
    (hS : ∀ x ∈ S, x ∈ muDelta Ω W)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    2 ^ S.card ≤ Nat.card ↥(Subgroup.closure (↑S : Set ↥(muGroup Ω W))) := by
  exact T8V.two_pow_card_le_closureE (fun hx => fun hS => c.not_mem_closure rep hrep hx hS) S hS
    hcomm

end Frame

end Ctx

end Thompson

variable {p f : ℕ} [Fact p.Prime]

theorem thompsonClique : ThompsonClique p f := by
  classical
  intro G _ _ Ω hP W hW hnc d hd
  have hp : p ≠ 2 := hP.1
  have hq : 5 ≤ p ^ f := hP.2.1
  have hΩ : HypOmegaMod p f Ω := hP.2.2.1
  let c : Thompson.Ctx p f Ω W := ⟨hp, hq, hΩ, hW, thompsonKey G Ω hP W hW, hP.2.2.2⟩
  have hTT := Thompson.isTT_muDelta hp hq hΩ hW (thompsonCube G Ω hP W hW)
  have hS := Thompson.isStar_muDelta hp hq hΩ hW (thompsonStar G Ω hP W hW)
  obtain ⟨d₀, hd₀, a₀, ha₀, hn₀⟩ := Thompson.exists_not_conn_of_not_connected hp hq hΩ hW hnc
  obtain ⟨a, haΔ, hna⟩ : ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) d a := by
    by_cases h : Star3T.Conn (muDelta Ω W) d d₀
    · exact ⟨a₀, ha₀, fun h' => hn₀ (h.symm.trans h')⟩
    · exact ⟨d₀, hd₀, h⟩
  have hcfg : Star3T.Cfg (muDelta Ω W) d a := ⟨hTT, hS, hd, haΔ, hna⟩
  obtain ⟨n, B, hcard, hBC, hdB, hBn, hgen⟩ := hcfg.exists_generating_family
  obtain ⟨rep, hrep⟩ : ∃ rep : ↥(muGroup Ω W) → Thompson.Rep Ω W,
      ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)) := by
    have hex : ∀ x ∈ muDelta Ω W, ∃ ρ : Thompson.Rep Ω W, ρ.img = (x : NQuot (W ⊔ OCW W)) := by
      rintro x ⟨R, hR, r, hr, hrW, hxr⟩
      obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
      exact ⟨⟨K, R, r, hK, hR, hRK, hr, hrW⟩, hxr.symm⟩
    have : Nonempty (Thompson.Rep Ω W) := by
      obtain ⟨ρ, -⟩ := hex d hd
      exact ⟨ρ⟩
    choose! rep hrep using hex
    exact ⟨rep, hrep⟩
  have hpow : ∀ k : ℕ, 2 * (k + 1) ≤ 2 ^ (k + 1) := fun k => by
    have := Nat.lt_two_pow_self (n := k)
    rw [pow_succ]
    omega
  have hn : n ≤ 2 := by
    by_contra hn3
    push Not at hn3
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h2k := hpow k
    by_cases hall : ∀ P ∈ Star3T.cent (muDelta Ω W) d, P ∈ B
    · have h1 : (Star3T.cent (muDelta Ω W) d).ncard ≤ B.card := by
        calc (Star3T.cent (muDelta Ω W) d).ncard ≤ (↑B : Set ↥(muGroup Ω W)).ncard :=
              Set.ncard_le_ncard (fun P hP => Finset.mem_coe.mpr (hall P hP)) (Set.toFinite _)
          _ = B.card := Set.ncard_coe_finset B
      rw [hcard, hBn] at h1
      omega
    · push Not at hall
      obtain ⟨P, hP, hPB⟩ := hall
      have hsub := c.clique_subset rep hrep hcfg hBC hdB hgen hP hPB
      have h1 : (Star3T.cent (muDelta Ω W) d).ncard ≤ B.card + 1 := by
        calc (Star3T.cent (muDelta Ω W) d).ncard
            ≤ (↑(insert P B) : Set ↥(muGroup Ω W)).ncard := by
              refine Set.ncard_le_ncard (fun P' hP' => ?_) (Set.toFinite _)
              by_cases h : P' = P
              · rw [h]
                exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
              · exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (hsub P' hP' h))
          _ = (insert P B).card := Set.ncard_coe_finset _
          _ ≤ B.card + 1 := Finset.card_insert_le _ _
      rw [hcard, hBn] at h1
      omega
  interval_cases n
  · left
    rw [hcard]
    norm_num
  · right
    left
    rw [hcard]
    norm_num
  · right
    right
    refine ⟨by rw [hcard]; norm_num, ?_⟩
    have hfin : (Star3T.cent (muDelta Ω W) d).Finite := Set.toFinite _
    have hSc : hfin.toFinset.card = 4 := by
      rw [← Set.ncard_eq_toFinset_card _ hfin, hcard]
      norm_num
    have hΔ : ∀ x ∈ hfin.toFinset, x ∈ muDelta Ω W := fun x hx =>
      ((Set.Finite.mem_toFinset hfin).mp hx).1
    have hcomm : ∀ x ∈ hfin.toFinset, ∀ y ∈ hfin.toFinset, x * y = y * x := fun x hx y hy =>
      hcfg.comm_cent ((Set.Finite.mem_toFinset hfin).mp hx) ((Set.Finite.mem_toFinset hfin).mp hy)
    have h16 := c.two_pow_card_le_closure rep hrep hfin.toFinset hΔ hcomm
    rw [hSc, Set.Finite.coe_toFinset] at h16
    simpa using h16

theorem l7_10_proved : L7_10 p f := l7_10_of_inputs thompsonCube thompsonStar thompsonClique

theorem l7_12_of_sub (h4 : ThompsonSub p f) : L7_12 p f :=
  l7_12_of_inputs thompsonCube thompsonStar thompsonClique h4

end CFSG.ClassicalInvolution.Asc77

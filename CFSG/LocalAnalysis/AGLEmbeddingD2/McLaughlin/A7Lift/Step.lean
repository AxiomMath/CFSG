module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Lift.Ctx
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.C126Over
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.BlockQ
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.Escape
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.MinParLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Parabolic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Lift

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.GN CFSG.AGLEmbeddingD2.McLaughlin.A7Six Equiv Equiv.Perm
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

namespace SevenCtx0

private theorem eq_one_of_mem_pow_mul_eq_one (c : SevenCtx0 T L)
    {Rs : Subgroup (X ⧸ gnC T)} (hRp : IsPGroup 2 Rs) {k m : X ⧸ gnC T}
    (hkR : k ∈ Rs) (hmL : m ∈ L) (hkc : ∀ l ∈ L, k * l * k⁻¹ = l) {n : ℕ}
    (hpow : m ^ (2 * n + 1) * k ^ (2 * n + 1) = 1) : k = 1 := by
  have hkn : k ^ (2 * n + 1) ∈ L := by
    have : k ^ (2 * n + 1) = (m ^ (2 * n + 1))⁻¹ := eq_inv_of_mul_eq_one_right hpow
    rw [this]
    exact L.inv_mem (L.pow_mem hmL _)
  have hkn1 : k ^ (2 * n + 1) = 1 := by
    refine c.eq_one_of_mem_center hkn fun l hl => ?_
    have h1 : ∀ j : ℕ, k ^ j * l * (k ^ j)⁻¹ = l := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc k ^ (j + 1) * l * (k ^ (j + 1))⁻¹ =
            k ^ j * (k * l * k⁻¹) * (k ^ j)⁻¹ := by group
          _ = l := by rw [hkc l hl, ih]
    have := h1 (2 * n + 1)
    calc k ^ (2 * n + 1) * l = k ^ (2 * n + 1) * l * (k ^ (2 * n + 1))⁻¹ *
          k ^ (2 * n + 1) := by group
      _ = l * k ^ (2 * n + 1) := by rw [this]
  obtain ⟨j, hj⟩ := hRp ⟨k, hkR⟩
  have hj' : k ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hcop : Nat.Coprime (2 ^ j) (2 * n + 1) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
  have hg : k ^ Nat.gcd (2 ^ j) (2 * n + 1) = 1 := pow_gcd_eq_one.2 ⟨hj', hkn1⟩
  rwa [hcop.gcd_eq_one, pow_one] at hg

private theorem normalizer_wP_of_le_img (c : SevenCtx0 T L) {R : Subgroup X}
    (hRL : R ≤ nL T L) {P : Subgroup (Perm (Fin 7))} (hQP : c.img R ≤ P) :
    R.map (QuotientGroup.mk' (gnC T)) ≤
      Subgroup.normalizer (c.wP P : Set (X ⧸ gnC T)) := by
  classical
  set π := QuotientGroup.mk' (gnC T)
  set Rs : Subgroup (X ⧸ gnC T) := R.map π with hRs
  have hRLs : Rs ≤ nLs T L := by
    rintro _ ⟨r, hr, rfl⟩
    exact hRL hr
  have hQ : c.imgS Rs = c.img R := c.imgS_map R hRL
  have hRQ : ∀ r (hr : r ∈ Rs), c.θs ⟨r, hRLs hr⟩ ∈ c.img R := fun r hr =>
    hQ ▸ ⟨⟨r, hRLs hr⟩, hr, rfl⟩
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ Rs, ∀ w ∈ c.wP P, g * w * g⁻¹ ∈ c.wP P := by
    intro g hg w hw
    obtain ⟨hwL, hwP⟩ := (c.mem_wP).1 hw
    have hgw : g * w * g⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hRLs hg) w).1 hwL
    refine (c.mem_wP).2 ⟨hgw, ?_⟩
    rw [c.hθs ⟨g, hRLs hg⟩ ⟨w, hwL⟩ ⟨_, hgw⟩ rfl]
    exact P.mul_mem (P.mul_mem (hQP (hRQ g hg)) hwP) (P.inv_mem (hQP (hRQ g hg)))
  intro w
  constructor
  · exact key r hr w
  · intro h
    have := key r⁻¹ (Rs.inv_mem hr) _ h
    simpa [mul_assoc] using this

private theorem sign_theta_eq_one_of_odd_order (c : SevenCtx0 T L) {W Rs : Subgroup (X ⧸ gnC T)}
    (hHL : W ⊔ Rs ≤ nLs T L) {h : X ⧸ gnC T} (hh : h ∈ W ⊔ Rs)
    (hho : Odd (orderOf h)) :
    Equiv.Perm.sign (c.θs ⟨h, hHL hh⟩) = 1 := by
  have hord : Odd (orderOf (c.θs ⟨h, hHL hh⟩)) := by
    refine Odd.of_dvd_nat hho ?_
    exact (orderOf_map_dvd c.θs ⟨h, hHL hh⟩).trans (by rw [Subgroup.orderOf_mk])
  have h1 : (Equiv.Perm.sign (c.θs ⟨h, hHL hh⟩)) ^ orderOf (c.θs ⟨h, hHL hh⟩) = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (c.θs ⟨h, hHL hh⟩)) with h | h
  · exact h
  · rw [h, hord.neg_one_pow] at h1
    exact absurd h1 (by decide)

private theorem odd_base (c : SevenCtx0 T L) {R : Subgroup X} (hRL : R ≤ nL T L)
    {P : Subgroup (Perm (Fin 7))}
    (hRLs : R.map (QuotientGroup.mk' (gnC T)) ≤ nLs T L) (hQP : c.img R ≤ P)
    {h : X ⧸ gnC T} (hh : h ∈ c.wP P ⊔ R.map (QuotientGroup.mk' (gnC T)))
    (hho : Odd (orderOf h)) :
    ∃ (w r : X ⧸ gnC T), w ∈ c.wP P ∧ r ∈ R.map (QuotientGroup.mk' (gnC T)) ∧
      h = w * r ∧ ∀ (hr : r ∈ R.map (QuotientGroup.mk' (gnC T))),
        c.θs ⟨r, hRLs hr⟩ ∈ c.img R ⊓ alternatingGroup (Fin 7) := by
  classical
  set π := QuotientGroup.mk' (gnC T)
  set Rs : Subgroup (X ⧸ gnC T) := R.map π with hRs
  set W : Subgroup (X ⧸ gnC T) := c.wP P with hW
  have hWL : W ≤ nLs T L := (c.wP_le_L P).trans Subgroup.le_normalizer
  have hHL : W ⊔ Rs ≤ nLs T L := sup_le hWL hRLs
  have hRW : Rs ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)) := by
    rw [hRs]
    exact c.normalizer_wP_of_le_img hRL hQP
  have hmul : ((W : Set (X ⧸ gnC T)) * (Rs : Set (X ⧸ gnC T))) =
      ((W ⊔ Rs : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left W Rs hRW).symm
  have hdecomp : ∀ h ∈ W ⊔ Rs, ∃ w ∈ W, ∃ r ∈ Rs, h = w * r := by
    intro h hh
    have : h ∈ ((W : Set (X ⧸ gnC T)) * (Rs : Set (X ⧸ gnC T))) := by rw [hmul]; exact hh
    obtain ⟨w, hw, r, hr, rfl⟩ := this
    exact ⟨w, hw, r, hr, rfl⟩
  obtain ⟨w, hw, r, hr, rfl⟩ := hdecomp h hh
  obtain ⟨hwL, -⟩ := (c.mem_wP).1 hw
  have hθ : c.θs ⟨w * r, hHL (Subgroup.mul_mem _ (Subgroup.mem_sup_left hw)
      (Subgroup.mem_sup_right hr))⟩ = c.θs ⟨w, hWL hw⟩ * c.θs ⟨r, hRLs hr⟩ := by
    have e : (⟨w * r, hHL (Subgroup.mul_mem _ (Subgroup.mem_sup_left hw)
        (Subgroup.mem_sup_right hr))⟩ : ↥(nLs T L)) = ⟨w, hWL hw⟩ * ⟨r, hRLs hr⟩ := rfl
    rw [e, map_mul]
  have hsign := c.sign_theta_eq_one_of_odd_order hHL
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hr)) hho
  have hθw : c.θs ⟨w, hWL hw⟩ = c.eL ⟨w, hwL⟩ := c.θs_of_mem_L hwL
  have hrA : c.θs ⟨r, hRLs hr⟩ ∈ c.img R ⊓ alternatingGroup (Fin 7) := by
    refine ⟨?_, Equiv.Perm.mem_alternatingGroup.mpr ?_⟩
    exact (c.imgS_map R hRL) ▸ ⟨⟨r, hRLs hr⟩, hr, rfl⟩
    have h1 := hsign
    rw [hθ, map_mul, hθw, Equiv.Perm.mem_alternatingGroup.mp (c.eL ⟨w, hwL⟩).2,
      one_mul] at h1
    exact h1
  exact ⟨w, r, hw, hr, rfl, fun _ => hrA⟩

private theorem odd_reduction (c : SevenCtx0 T L) {R : Subgroup X} (hRL : R ≤ nL T L)
    {P : Subgroup (Perm (Fin 7))}
    (hRLs : R.map (QuotientGroup.mk' (gnC T)) ≤ nLs T L)
    (hQL : ∀ σ ∈ c.img R ⊓ alternatingGroup (Fin 7), ∃ (t : X) (ht : t ∈ R),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c.θ ⟨t, hRL ht⟩ = σ)
    {h w r : X ⧸ gnC T} (hw : w ∈ c.wP P)
    (hr : r ∈ R.map (QuotientGroup.mk' (gnC T))) (hwr : h = w * r)
    (hrA : ∀ (hr : r ∈ R.map (QuotientGroup.mk' (gnC T))),
      c.θs ⟨r, hRLs hr⟩ ∈ c.img R ⊓ alternatingGroup (Fin 7))
    (hho : Odd (orderOf h)) :
    ∃ (k m : X ⧸ gnC T), k ∈ R.map (QuotientGroup.mk' (gnC T)) ∧ m ∈ L ∧
      (∀ l ∈ L, k * l * k⁻¹ = l) ∧ m * k = k * m ∧
      h = m * k ∧ Odd (orderOf (m * k)) := by
  classical
  set π := QuotientGroup.mk' (gnC T)
  set Rs : Subgroup (X ⧸ gnC T) := R.map π with hRs
  set W : Subgroup (X ⧸ gnC T) := c.wP P with hW
  obtain ⟨t, ht, htL, htθ⟩ := hQL _ (hrA hr)
  let y : X ⧸ gnC T := π t
  have hyR : y ∈ Rs := ⟨t, ht, rfl⟩
  have hyL : y ∈ L := htL
  have hyθ : c.θs ⟨y, hRLs hyR⟩ = c.θs ⟨r, hRLs hr⟩ := by
    change c.θ ⟨t, hRL ht⟩ = c.θs ⟨r, hRLs hr⟩
    exact htθ
  set k := y⁻¹ * r with hk
  have hkR : k ∈ Rs := Rs.mul_mem (Rs.inv_mem hyR) hr
  have hkθ : c.θs ⟨k, hRLs hkR⟩ = 1 := by
    have e : (⟨k, hRLs hkR⟩ : ↥(nLs T L)) = (⟨y, hRLs hyR⟩)⁻¹ * ⟨r, hRLs hr⟩ := rfl
    rw [e, map_mul, map_inv, hyθ, inv_mul_cancel]
  have hkc0 := (c.hθs1 ⟨k, hRLs hkR⟩).1 hkθ
  have hkc : ∀ l ∈ L, k * l * k⁻¹ = l := fun l hl => hkc0 l hl
  obtain ⟨hwL, -⟩ := (c.mem_wP).1 hw
  set m := w * y with hm
  have hmL : m ∈ L := L.mul_mem hwL hyL
  have hmk : m * k = k * m := by
    have h := hkc m hmL
    calc m * k = (k * m * k⁻¹) * k := by rw [h]
      _ = k * m := by group
  have hwry : w * r = m * k := by rw [hm, hk]; group
  have hm_eq : h = m * k := hwr.trans hwry
  exact ⟨k, m, hkR, hmL, hkc, hmk, hm_eq, hm_eq ▸ hho⟩


private theorem odd_mem_L_of_mem_wP_sup (c : SevenCtx0 T L) {R : Subgroup X}
    (hRL : R ≤ nL T L) (hRp : IsPGroup 2 (R.map (QuotientGroup.mk' (gnC T))))
    {P : Subgroup (Perm (Fin 7))} (hQP : c.img R ≤ P)
    (hQL : ∀ σ ∈ c.img R ⊓ alternatingGroup (Fin 7), ∃ (t : X) (ht : t ∈ R),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c.θ ⟨t, hRL ht⟩ = σ)
    {h : X ⧸ gnC T} (hh : h ∈ c.wP P ⊔ R.map (QuotientGroup.mk' (gnC T)))
    (hho : Odd (orderOf h)) : h ∈ L := by
  classical
  set π := QuotientGroup.mk' (gnC T)
  set Rs : Subgroup (X ⧸ gnC T) := R.map π with hRs
  have hRLs : Rs ≤ nLs T L := by
    rintro _ ⟨r, hr, rfl⟩
    exact hRL hr
  obtain ⟨w, r, hw, hr, hwr, hrA⟩ := odd_base c hRL hRLs hQP hh hho
  obtain ⟨k, m, hkR, hmL, hkc, hmk, hm_eq, hm_odd⟩ :=
    odd_reduction c hRL hRLs hQL hw hr hwr hrA hho
  obtain ⟨n, hn⟩ := hm_odd
  have hpow : (m * k) ^ (2 * n + 1) = 1 := by
    rw [← hn]
    exact pow_orderOf_eq_one _
  have hpow' : m ^ (2 * n + 1) * k ^ (2 * n + 1) = 1 := by
    rw [← (Commute.mul_pow hmk)]
    exact hpow
  have hk1 := c.eq_one_of_mem_pow_mul_eq_one hRp hkR hmL hkc hpow'
  rw [hm_eq, hk1, mul_one]
  exact hmL
private theorem false_of_block (c : SevenCtx0 T L) (hX : GNSetting X T) {R : Subgroup X}
    (hRL : R ≤ nL T L) (hRT : R ≤ T) (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R)
    {P : Subgroup (Perm (Fin 7))} (hQP : c.img R ≤ P) (hPQ : P ≠ c.img R)
    (hQL : ∀ σ ∈ c.img R ⊓ alternatingGroup (Fin 7), ∃ (t : X) (ht : t ∈ R),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c.θ ⟨t, hRL ht⟩ = σ)
    {H : Subgroup X} (hRH : R ≤ H)
    (hmap : H.map (QuotientGroup.mk' (gnC T)) = c.wP P ⊔ R.map (QuotientGroup.mk' (gnC T)))
    (himg : c.imgS (c.wP P ⊔ R.map (QuotientGroup.mk' (gnC T))) = P)
    (hDL : gnD T ⊓ lT T L ≤ gnC T) {K : Subgroup X} (hKb : IsBlock2 H K)
    (hHK : H = R ⊔ conjClosure K R) : False := by
  classical
  set π := QuotientGroup.mk' (gnC T)
  set Rs : Subgroup (X ⧸ gnC T) := R.map π with hRs
  have hRp : IsPGroup 2 Rs := (hX.sylow.2.1.to_le hRT).map π
  have hne : c.wP P ⊔ Rs ≠ Rs := by
    intro h
    have h1 : c.imgS (c.wP P ⊔ Rs) = c.imgS Rs := by rw [h]
    rw [himg, c.imgS_map R hRL] at h1
    exact hPQ h1
  have hKC : ¬ K ≤ gnC T := by
    intro hKC
    apply hne
    apply le_antisymm _ le_sup_right
    rw [← hmap, hHK, Subgroup.map_sup]
    refine sup_le le_rfl ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxC : x ∈ gnC T := by
      refine (conjClosure_le fun t _ k hk => ?_) hx
      exact (gnC_normal T).conj_mem k (hKC hk) t
    rw [show π x = 1 from (QuotientGroup.eq_one_iff x).2 hxC]
    exact Rs.one_mem
  have hKD : K ≤ gnD T := le_gnD_of_isBlock2' hX (hQR.trans hRH) hKb hKC
  have hodd' : ∀ h ∈ c.wP P ⊔ Rs, Odd (orderOf h) → h ∈ L := fun h hh hho =>
    c.odd_mem_L_of_mem_wP_sup hRL hRp hQP hQL hh hho
  have hKL : K ≤ lT T L := by
    refine (CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.le_closure_odd_of_isShort2 hKb.1).trans
      ((Subgroup.closure_le _).2 fun x hx => ?_)
    show π x ∈ L
    have hxH : π x ∈ c.wP P ⊔ Rs := by
      rw [← hmap]
      exact ⟨x, hKb.2.1 hx.1, rfl⟩
    exact hodd' _ hxH (Odd.of_dvd_nat hx.2 (orderOf_map_dvd π x))
  exact hKC ((le_inf hKD hKL).trans hDL)

theorem escape_of_concl1Gen (c : SevenCtx0 T L) (hX : GNSetting X T)
    {C₁ C₂ : Subgroup X} (hDL : gnD T ⊓ lT T L ≤ gnC T) {R : Subgroup X} (hRL : R ≤ nL T L)
    (hRT : R ≤ T) (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R) {P : Subgroup (Perm (Fin 7))}
    (hQP : c.img R ≤ P) (hPQ : P ≠ c.img R)
    (hQL : ∀ σ ∈ c.img R ⊓ alternatingGroup (Fin 7), ∃ (t : X) (ht : t ∈ R),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c.θ ⟨t, hRL ht⟩ = σ)
    {H M : Subgroup X} (hmin : MinParabolic H R M) (hRH : R ≤ H)
    (hmap : H.map (QuotientGroup.mk' (gnC T)) = c.wP P ⊔ R.map (QuotientGroup.mk' (gnC T)))
    (himg : c.imgS (c.wP P ⊔ R.map (QuotientGroup.mk' (gnC T))) = P)
    (hker : ∀ y : ↥(nLs T L), (y : X ⧸ gnC T) ∈ c.wP P ⊔ R.map (QuotientGroup.mk' (gnC T)) →
      c.θs y = 1 → (y : X ⧸ gnC T) ∈ R.map (QuotientGroup.mk' (gnC T)))
    (hC : Concl1Gen C₁ C₂ H R) :
    c.wP P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c.wP P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)) := by
  classical
  set π := QuotientGroup.mk' (gnC T)
  have hWH : c.wP P ≤ gnImg T H := by
    show c.wP P ≤ H.map π
    rw [hmap]
    exact le_sup_left
  rcases hC with h1 | h2 | h3
  · exact Tits.GN516.escape_of_le_gnImg hWH (Or.inl h1)
  · exact Tits.GN516.escape_of_le_gnImg hWH (Or.inr h2)
  · obtain ⟨K, hKχ, -, hHK⟩ := h3
    exact (c.false_of_block hX hRL hRT hQR hQP hPQ hQL hRH hmap himg hDL hKχ.1 hHK).elim

private structure StepData (c : SevenCtx0 T L) {R : Subgroup X}
    {P : Subgroup (Perm (Fin 7))} where
  Rs : Subgroup (X ⧸ gnC T)
  hRs : Rs = R.map (QuotientGroup.mk' (gnC T))
  hRLs : Rs ≤ nLs T L
  hRp : IsPGroup 2 Rs
  hminWs : MinParabolic (c.wP P ⊔ Rs) Rs (c.wP (c.img R) ⊔ Rs)
  himg : c.imgS (c.wP P ⊔ Rs) = P
  hker : ∀ y : ↥(nLs T L), (y : X ⧸ gnC T) ∈ c.wP P ⊔ Rs → c.θs y = 1 →
    (y : X ⧸ gnC T) ∈ Rs
  hHL : c.wP P ⊔ Rs ≤ nLs T L
  hne : c.wP P ⊔ Rs ≠ Rs
  hPQ : P ≠ c.img R

private noncomputable def step_data (c : SevenCtx0 T L) (hX : GNSetting X T)
    {R : Subgroup X} (hRL : R ≤ nL T L) (hRT : R ≤ T)
    {P : Subgroup (Perm (Fin 7))} (hQP : c.img R ≤ P)
    (hcard : Nat.card P = 3 * Nat.card (c.img R))
    (hodd : P ≤ alternatingGroup (Fin 7) ∨ ∃ q ∈ c.img R, q ∉ alternatingGroup (Fin 7))
    (hnn : ∃ g ∈ P ⊓ alternatingGroup (Fin 7), ∃ e ∈ c.img R, g * e * g⁻¹ ∉ c.img R)
    (hQL : ∀ σ ∈ c.img R ⊓ alternatingGroup (Fin 7), ∃ (t : X) (ht : t ∈ R),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c.θ ⟨t, hRL ht⟩ = σ) :
    StepData (R := R) (P := P) c := by
  classical
  set π := QuotientGroup.mk' (gnC T)
  set Rs : Subgroup (X ⧸ gnC T) := R.map π with hRs
  have hRLs : Rs ≤ nLs T L := by
    rintro _ ⟨r, hr, rfl⟩
    exact hRL hr
  have hRp : IsPGroup 2 Rs := (hX.sylow.2.1.to_le hRT).map π
  have hQ : c.imgS Rs = c.img R := c.imgS_map R hRL
  have hQL' : ∀ σ ∈ c.img R ⊓ alternatingGroup (Fin 7), ∃ (y : X ⧸ gnC T)
      (hy : y ∈ Rs ⊓ L), c.θs ⟨y, hRLs hy.1⟩ = σ := by
    intro σ hσ
    obtain ⟨t, ht, htL, htσ⟩ := hQL σ hσ
    exact ⟨π t, ⟨⟨t, ht, rfl⟩, htL⟩, htσ⟩
  have hQp : IsPGroup 2 (c.img R) :=
    ((hX.sylow.2.1.to_le hRT).of_equiv (Subgroup.subgroupOfEquivOfLe hRL).symm).map c.θ
  have hrel : (c.img R).relIndex P = 3 := by
    have h := Subgroup.relIndex_mul_card (c.img R) P
    rw [inf_eq_left.mpr hQP, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hSylP : IsSylowTwoOf (c.img R) P := by
    refine ⟨hQP, hQp, ?_⟩
    show ¬ 2 ∣ (c.img R).relIndex P
    rw [hrel]
    decide
  have hN : ¬ P ≤ Subgroup.normalizer (c.img R : Set (Perm (Fin 7))) := by
    intro hle
    obtain ⟨g, ⟨hgP, -⟩, e, he, hge⟩ := hnn
    exact hge ((Subgroup.mem_normalizer_iff.1 (hle hgP) e).1 he)
  have hminQ : MinParabolic P (c.img R) (c.img R) :=
    CFSG.Quasithin.H13.A5.minParabolic_of_relIndex_three hSylP hrel hN
  obtain ⟨hminWs, himg, hker⟩ := c.minParabolic_wP_gen hRLs hRp hQ hminQ hodd hQL'
  have hHL : c.wP P ⊔ Rs ≤ nLs T L :=
    sup_le ((c.wP_le_L P).trans Subgroup.le_normalizer) hRLs
  have hne : c.wP P ⊔ Rs ≠ Rs := by
    intro h
    have h1 : c.imgS (c.wP P ⊔ Rs) = c.imgS Rs := by rw [h]
    rw [himg, c.imgS_map R hRL] at h1
    have h2 : Nat.card P = Nat.card (c.img R) := by rw [h1]
    have hpos : 0 < Nat.card (c.img R) := Nat.card_pos
    omega
  have hPQ : P ≠ c.img R := by
    intro heq
    have h2 := hcard
    rw [heq] at h2
    have hpos : 0 < Nat.card (c.img R) := Nat.card_pos
    omega
  exact ⟨Rs, hRs, hRLs, hRp, hminWs, himg, hker, hHL, hne, hPQ⟩

private theorem step_solvable (c : SevenCtx0 T L) (hX : GNSetting X T)
    {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂) (hDL : gnD T ⊓ lT T L ≤ gnC T)
    {R : Subgroup X} (hRL : R ≤ nL T L) (hRT : R ≤ T) (hCR : T ⊓ gnC T ≤ R)
    (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R) (hbR : baum R = baum T)
    (h1R : C₁ ≤ omegaOneCenterOf R) {P : Subgroup (Perm (Fin 7))} (hQP : c.img R ≤ P)
    (hQL : ∀ σ ∈ c.img R ⊓ alternatingGroup (Fin 7), ∃ (t : X) (ht : t ∈ R),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c.θ ⟨t, hRL ht⟩ = σ)
    (hsolvP : Group.IsSolvable ↥P) (d : StepData (R := R) (P := P) c) :
    c.wP P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c.wP P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)) := by
  classical
  set π := QuotientGroup.mk' (gnC T)
  have hminWs : MinParabolic (c.wP P ⊔ R.map π) (R.map π) (c.wP (c.img R) ⊔ R.map π) := by
    rw [← d.hRs]
    exact d.hminWs
  have himg : c.imgS (c.wP P ⊔ R.map π) = P := by
    rw [← d.hRs]
    exact d.himg
  have hker : ∀ y : ↥(nLs T L), (y : X ⧸ gnC T) ∈ c.wP P ⊔ R.map π →
      c.θs y = 1 → (y : X ⧸ gnC T) ∈ R.map π := by
    rw [← d.hRs]
    exact d.hker
  have hsolvs : Group.IsSolvable ↥(c.wP P ⊔ d.Rs) := by
    let g : ↥(c.wP P ⊔ d.Rs) →* ↥P :=
      (c.θs.comp (Subgroup.inclusion d.hHL)).codRestrict P (fun h => by
        have hmem : c.θs ⟨h, d.hHL h.2⟩ ∈ c.imgS (c.wP P ⊔ d.Rs) :=
          ⟨⟨h, d.hHL h.2⟩, h.2, rfl⟩
        rwa [d.himg] at hmem)
    let f : ↥(d.Rs.subgroupOf (c.wP P ⊔ d.Rs)) →* ↥(c.wP P ⊔ d.Rs) :=
      (d.Rs.subgroupOf (c.wP P ⊔ d.Rs)).subtype
    have hRs2 : IsPGroup 2 ↥(d.Rs.subgroupOf (c.wP P ⊔ d.Rs)) :=
      d.hRp.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
    have := hRs2.isNilpotent
    refine Group.isSolvable_of_ker_le_range f g fun h hh => ?_
    have h1 : c.θs ⟨h, d.hHL h.2⟩ = 1 := congrArg Subtype.val hh
    exact ⟨⟨h, d.hker ⟨h, d.hHL h.2⟩ h.2 h1⟩, rfl⟩
  obtain ⟨H, M, hminH, hF, hRH, hmap⟩ :=
    Tits.GN516.exists_minParabolic_lift_of_le hX hRT hCR hQR hminWs
  have hmap' : H.map π = c.wP P ⊔ d.Rs := by
    rw [hmap, d.hRs]
  have hsolv : Group.IsSolvable ↥H :=
    isSolvable_of_minParabolic hminH (hmap' ▸ hsolvs) (by
      rw [hmap]
      rw [← d.hRs]
      exact d.hne)
  have hpc : perfectCore H ≤ Subgroup.centralizer (VZ R H : Set X) := by
    rw [(isSolvable_iff_perfectCore_eq_bot H).1 hsolv]
    exact bot_le
  exact c.escape_of_concl1Gen hX hDL hRL hRT hQR hQP d.hPQ hQL hminH hRH hmap himg hker
    (concl1_over hP hbR h1R hminH hF hpc)

theorem step (c : SevenCtx0 T L) (hX : GNSetting X T) {C₁ C₂ : Subgroup X}
    (hP : IsC118Pair T C₁ C₂) (hDL : gnD T ⊓ lT T L ≤ gnC T) {R : Subgroup X}
    (hRL : R ≤ nL T L) (hRT : R ≤ T) (hCR : T ⊓ gnC T ≤ R)
    (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R) (hbR : baum R = baum T)
    (h1R : C₁ ≤ omegaOneCenterOf R) {P : Subgroup (Perm (Fin 7))} (hQP : c.img R ≤ P)
    (hcard : Nat.card P = 3 * Nat.card (c.img R))
    (hodd : P ≤ alternatingGroup (Fin 7) ∨ ∃ q ∈ c.img R, q ∉ alternatingGroup (Fin 7))
    (hnn : ∃ g ∈ P ⊓ alternatingGroup (Fin 7), ∃ e ∈ c.img R, g * e * g⁻¹ ∉ c.img R)
    (hQL : ∀ σ ∈ c.img R ⊓ alternatingGroup (Fin 7), ∃ (t : X) (ht : t ∈ R),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c.θ ⟨t, hRL ht⟩ = σ)
    (hsolvP : Group.IsSolvable ↥P) :
    c.wP P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c.wP P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)) := by
  classical
  exact step_solvable c hX hP hDL hRL hRT hCR hQR hbR h1R hQP hQL hsolvP
    (step_data c hX hRL hRT hQP hcard hodd hnn hQL)
end SevenCtx0

end CFSG.AGLEmbeddingD2.McLaughlin.A7Lift

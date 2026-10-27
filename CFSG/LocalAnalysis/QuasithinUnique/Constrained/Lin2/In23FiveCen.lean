module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Block

public section

namespace CFSG.QuasithinUnique.Lin2.Five

open CFSG.Open CFSG.Quasithin

section Lin2

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem mul_inv_mem_S {x y : G} (hx : x ∈ T) (hxS : x ∉ S) (hy : y ∈ T) (hyS : y ∉ S) :
    y * x⁻¹ ∈ S := by
  have hidx : (S.subgroupOf T).index = 2 := E.idxTS hcfg
  have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨y, hy⟩) (b := ⟨x⁻¹, T.inv_mem hx⟩)).mpr
    ⟨fun h => absurd h hyS, fun h => absurd (inv_inv x ▸ S.inv_mem (show x⁻¹ ∈ S from h)) hxS⟩
  exact h

theorem mul_self_mem_S {x : G} (hx : x ∈ T) : x * x ∈ S := by
  have hidx : (S.subgroupOf T).index = 2 := E.idxTS hcfg
  exact Subgroup.mul_self_mem_of_index_two hidx ⟨x, hx⟩

omit E in
theorem conjR_Ls_eq {s σ : G} (hσS : σ ∈ S) (hσs : σ * s = s * σ) :
    conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) σ = L ⊓ Subgroup.centralizer ({s} : Set G) := by
  rw [conjR_inf, conjR_eq_of_mem_normalizer (hcfg.S_le_normalizer hσS),
    conjR_eq_of_mem_normalizer
      (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hσs))]

theorem conjR_Ks_of_mem_S {s x σ : G} (hxT : x ∈ T) (hxs : x * s = s * x) (hσS : σ ∈ S)
    (hσs : σ * s = s * σ) :
    conjR (L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
        conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x) σ =
      L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
        conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x := by
  have hσ' : x * σ * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (E.TnS hcfg hxT) σ).mp hσS
  have hxs' : x⁻¹ * s = s * x⁻¹ := comm_inv_of_comm hxs
  have hσ's : (x * σ * x⁻¹) * s = s * (x * σ * x⁻¹) := by
    calc x * σ * x⁻¹ * s = x * σ * (x⁻¹ * s) := by group
      _ = x * σ * (s * x⁻¹) := by rw [hxs']
      _ = x * (σ * s) * x⁻¹ := by group
      _ = x * (s * σ) * x⁻¹ := by rw [hσs]
      _ = (x * s) * σ * x⁻¹ := by group
      _ = (s * x) * σ * x⁻¹ := by rw [hxs]
      _ = s * (x * σ * x⁻¹) := by group
  rw [conjR_sup, conjR_conjR, conjR_Ls_eq hcfg hσS hσs]
  congr 1
  have e : x * σ = (x * σ * x⁻¹) * x := by group
  rw [e, ← conjR_conjR, conjR_Ls_eq hcfg hσ' hσ's]

theorem conjR_Ks_x {s x : G} (hxT : x ∈ T) (hxs : x * s = s * x) :
    conjR (L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
        conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x) x =
      L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
        conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x := by
  have hxx : x * x ∈ S := mul_self_mem_S E hcfg hxT
  have hxxs : (x * x) * s = s * (x * x) := by
    calc x * x * s = x * (x * s) := by group
      _ = x * (s * x) := by rw [hxs]
      _ = (x * s) * x := by group
      _ = (s * x) * x := by rw [hxs]
      _ = s * (x * x) := by group
  rw [conjR_sup, conjR_conjR, conjR_Ls_eq hcfg hxx hxxs, sup_comm]

theorem mem_normalizer_Ks {s x t : G} (hxT : x ∈ T) (hxS : x ∉ S) (hxs : x * s = s * x)
    (ht : t ∈ T) (hts : t * s = s * t) :
    t ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
        conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x : Subgroup G) : Set G) := by
  rw [← conjR_eq_self_iff]
  by_cases htS : t ∈ S
  · exact conjR_Ks_of_mem_S E hcfg hxT hxs htS hts
  · have hσ : t * x⁻¹ ∈ S := mul_inv_mem_S E hcfg hxT hxS ht htS
    have hxs' : x⁻¹ * s = s * x⁻¹ := comm_inv_of_comm hxs
    have hσs : (t * x⁻¹) * s = s * (t * x⁻¹) := by
      calc t * x⁻¹ * s = t * (x⁻¹ * s) := by group
        _ = t * (s * x⁻¹) := by rw [hxs']
        _ = (t * s) * x⁻¹ := by group
        _ = (s * t) * x⁻¹ := by rw [hts]
        _ = s * (t * x⁻¹) := by group
    calc conjR (L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
          conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x) t
        = conjR (L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
          conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x) ((t * x⁻¹) * x) := by
          rw [inv_mul_cancel_right]
      _ = conjR (conjR (L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
          conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x) (t * x⁻¹)) x :=
          (conjR_conjR _ _ _).symm
      _ = conjR (L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
          conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x) x := by
          rw [conjR_Ks_of_mem_S E hcfg hxT hxs hσ hσs]
      _ = _ := conjR_Ks_x E hcfg hxT hxs

theorem centerOf_Ls_eq {s : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1)
    (hc : centerOf L ≠ ⊥) (h4 : 4 < 2 ^ n) :
    centerOf (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      centerOf L ⊓ Subgroup.centralizer ({s} : Set G) := by
  have hn3 : 3 ≤ n := three_le_of_four_lt_two_pow h4
  obtain ⟨hblk, hO, -⟩ := E.block_s hcfg hs hsR hs2
  obtain ⟨m, hm, -, hshort, hlin, hUs⟩ : ∃ m : ℕ, n = 2 * m ∧ 1 < m ∧
      IsShort2 (L ⊓ Subgroup.centralizer ({s} : Set G)) ∧
      IsLin2Type (L ⊓ Subgroup.centralizer ({s} : Set G)) m ∧
      blockU L ⊓ Subgroup.centralizer ({s} : Set G) =
        blockU (L ⊓ Subgroup.centralizer ({s} : Set G)) := by
    rcases hblk with h | ⟨hn2, -⟩
    · exact h
    · exact absurd hn2 (by omega)
  have hZs : blockZ (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      centerOf (L ⊓ Subgroup.centralizer ({s} : Set G)) :=
    blockZ_eq_centerOf hshort.2.1 (hO.trans hUs)
  have hcardU : Nat.card (blockU (L ⊓ Subgroup.centralizer ({s} : Set G))) =
      2 ^ (2 * m) * Nat.card (blockZ (L ⊓ Subgroup.centralizer ({s} : Set G))) :=
    lin2_card_U hlin
  obtain ⟨x₀, hx₀, hx₀S⟩ := hcfg.exists_mem_T_not_mem_S
  have hUsval := ((E.U_s_values hcfg hs hsR hs2 hx₀ hx₀S).2 hc).1
  have hcardZs : Nat.card (centerOf (L ⊓ Subgroup.centralizer ({s} : Set G))) = 2 ^ m := by
    rw [← hZs]
    have h1 : 2 ^ (2 * m) * Nat.card (blockZ (L ⊓ Subgroup.centralizer ({s} : Set G))) =
        2 ^ (3 * n / 2) := by
      rw [← hcardU, ← hUs, hUsval]
    have h2 : 3 * n / 2 = 2 * m + m := by omega
    rw [h2, pow_add] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hz : lin2Z L (thompsonJ S) = centerOf L := by simp [lin2Z, hc]
  have hZc : Nat.card (centerOf L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) = 2 ^ m := by
    have h := E.card_Z_inf_centralizer hcfg (Z := lin2Z L (thompsonJ S)) rfl hs hsR hs2
    rw [hz] at h
    rw [h]
    congr 1
    omega
  have hle : centerOf L ⊓ Subgroup.centralizer ({s} : Set G) ≤
      centerOf (L ⊓ Subgroup.centralizer ({s} : Set G)) := by
    intro z hz'
    obtain ⟨hzZ, hzC⟩ := Subgroup.mem_inf.mp hz'
    obtain ⟨hzL, hzcent⟩ := Subgroup.mem_inf.mp hzZ
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hzL, hzC⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hzcent ⊢
    intro g hg
    exact hzcent g (Subgroup.mem_inf.mp hg).1
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hZc, hcardZs])).symm

theorem centralizer_Ks {s x : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1)
    (hc : centerOf L ≠ ⊥) (h4 : 4 < 2 ^ n)
    (hx : x ∈ T ⊓ Subgroup.centralizer ({s} : Set G)) (hxS : x ∉ S) :
    T ⊓ Subgroup.centralizer ({s} : Set G) ⊓
        Subgroup.centralizer ((L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
          conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x : Subgroup G) : Set G) =
      Subgroup.zpowers s := by
  have hn3 : 3 ≤ n := three_le_of_four_lt_two_pow h4
  obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hxs' : x⁻¹ * s = s * x⁻¹ := comm_inv_of_comm hxs
  have hs2' : s * s = 1 := by rw [← pow_two]; exact hs2
  have hUR : blockU L ≤ thompsonJ S := by rw [(E.RUU hcfg hxT hxS).1]; exact le_sup_left
  have hz : lin2Z L (thompsonJ S) = centerOf L := by simp [lin2Z, hc]
  have hKsC := Ks_le_centralizer (L := L) hxs
  apply le_antisymm
  · intro y hy
    obtain ⟨hyTC, hyK⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hyT, hyC⟩ := Subgroup.mem_inf.mp hyTC
    have hys : y * s = s * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hyLs : ∀ l ∈ L ⊓ Subgroup.centralizer ({s} : Set G), l * y = y * l := fun l hl =>
      Subgroup.mem_centralizer_iff.mp hyK l (Subgroup.mem_sup_left hl)
    have hyLsx : ∀ l ∈ conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x, l * y = y * l :=
      fun l hl => Subgroup.mem_centralizer_iff.mp hyK l (Subgroup.mem_sup_right hl)
    have hyS : y ∈ S := by
      by_contra hyS
      have hσ : y * x⁻¹ ∈ S := mul_inv_mem_S E hcfg hxT hxS hyT hyS
      have hUy : conjR (blockU L) y = conjR (blockU L) x := by
        calc conjR (blockU L) y = conjR (blockU L) ((y * x⁻¹) * x) := by
              rw [inv_mul_cancel_right]
          _ = conjR (conjR (blockU L) (y * x⁻¹)) x := (conjR_conjR _ _ _).symm
          _ = conjR (blockU L) x := by
              rw [conjR_eq_of_mem_normalizer (E.S_le_normalizer_U hcfg hσ)]
      have hsub : blockU L ⊓ Subgroup.centralizer ({s} : Set G) ≤
          centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({s} : Set G) := by
        intro u hu
        obtain ⟨huU, huC⟩ := Subgroup.mem_inf.mp hu
        have huLs : u ∈ L ⊓ Subgroup.centralizer ({s} : Set G) :=
          Subgroup.mem_inf.mpr ⟨blockU_le L huU, huC⟩
        have hyu : u * y = y * u := hyLs u huLs
        have hu1 : u ∈ conjR (blockU L) y := by
          rw [mem_conjR]
          have : y * u * y⁻¹ = u := by
            calc y * u * y⁻¹ = (u * y) * y⁻¹ := by rw [hyu]
              _ = u := by group
          rw [this]
          exact huU
        rw [hUy] at hu1
        have hmem : u ∈ blockU L ⊓ conjR (blockU L) x := Subgroup.mem_inf.mpr ⟨huU, hu1⟩
        rw [(E.RUU hcfg hxT hxS).2] at hmem
        exact Subgroup.mem_inf.mpr ⟨hmem, huC⟩
      have hcard := Subgroup.card_le_of_le hsub
      obtain ⟨-, h2⟩ := E.U_s_values hcfg hs hsR hs2 hxT hxS
      obtain ⟨h21, h22⟩ := h2 hc
      rw [h21, h22] at hcard
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard
      omega
    have hsU : s ∈ Subgroup.normalizer (blockU L : Set G) := E.S_le_normalizer_U hcfg hs
    have hyU : y ∈ Subgroup.normalizer (blockU L : Set G) := E.S_le_normalizer_U hcfg hyS
    have hyW : ∀ w ∈ blockU L, s * w * s⁻¹ = w → y * w * y⁻¹ = w := by
      intro w hw hsw
      have hwC : w ∈ Subgroup.centralizer ({s} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc w * s = (s * w * s⁻¹) * s := by rw [hsw]
          _ = s * w := by group
      have hwLs : w ∈ L ⊓ Subgroup.centralizer ({s} : Set G) :=
        Subgroup.mem_inf.mpr ⟨blockU_le L hw, hwC⟩
      have hyw : w * y = y * w := hyLs w hwLs
      calc y * w * y⁻¹ = (w * y) * y⁻¹ := by rw [hyw]
        _ = w := by group
    have hsq := sq_conj_eq_self (E.elemU hcfg hxT hxS).1 hs2' hsU hyU hys.symm hyW
    have hyyH : y * y ∈ H := H.mul_mem (hcfg.S_le_H hyS) (hcfg.S_le_H hyS)
    have hyyc : y * y ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haU : a ∈ blockU L := by rw [E.UQ hcfg]; exact ha
      have h' : (y * y) * a * (y * y)⁻¹ = a := by
        calc (y * y) * a * (y * y)⁻¹ = y * (y * a * y⁻¹) * y⁻¹ := by group
          _ = a := hsq a haU
      calc a * (y * y) = ((y * y) * a * (y * y)⁻¹) * (y * y) := by rw [h']
        _ = (y * y) * a := by group
    have hyyU : y * y ∈ blockU L := by
      have := hcfg.cs.charTwo (Subgroup.mem_inf.mpr ⟨hyyH, hyyc⟩)
      rwa [← E.UQ hcfg] at this
    obtain ⟨F, hFcyc, hFS, hRF, hRFS, -⟩ := E.exists_F hcfg
    have hSR : S ≤ Subgroup.normalizer (thompsonJ S : Set G) := hcfg.S_le_T.trans (E.TnR hcfg)
    have hy2R : y ^ 2 ∈ thompsonJ S := by rw [pow_two]; exact hUR hyyU
    have hKs : ∀ l ∈ L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
        conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x, l * s = s * l := fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hKsC hl)
    obtain ⟨r, hrR, hrC, hrLs, hrLsx, hyr⟩ : ∃ r ∈ thompsonJ S, r ∈ Subgroup.centralizer ({s} : Set G) ∧
        (∀ l ∈ L ⊓ Subgroup.centralizer ({s} : Set G), l * r = r * l) ∧
        (∀ l ∈ conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x, l * r = r * l) ∧
        (y = r ∨ y = s * r) := by
      rcases mem_or_inv_mul_mem_of_sq_mem hSR hFS hFcyc hRF hRFS hs hsR hs2 hyS hy2R with hyR | hsyR
      · exact ⟨y, hyR, hyC, hyLs, hyLsx, Or.inl rfl⟩
      · refine ⟨s⁻¹ * y, hsyR, ?_, ?_, ?_, Or.inr (by group)⟩
        · rw [Subgroup.mem_centralizer_singleton_iff]
          calc s⁻¹ * y * s = s⁻¹ * (y * s) := by group
            _ = s⁻¹ * (s * y) := by rw [hys]
            _ = s * (s⁻¹ * y) := by group
        · intro l hl
          have hls := hKs l (Subgroup.mem_sup_left hl)
          have hls' : l * s⁻¹ = s⁻¹ * l := by
            calc l * s⁻¹ = s⁻¹ * (s * l) * s⁻¹ := by group
              _ = s⁻¹ * (l * s) * s⁻¹ := by rw [hls]
              _ = s⁻¹ * l := by group
          calc l * (s⁻¹ * y) = (l * s⁻¹) * y := by group
            _ = (s⁻¹ * l) * y := by rw [hls']
            _ = s⁻¹ * (l * y) := by group
            _ = s⁻¹ * (y * l) := by rw [hyLs l hl]
            _ = (s⁻¹ * y) * l := by group
        · intro l hl
          have hls := hKs l (Subgroup.mem_sup_right hl)
          have hls' : l * s⁻¹ = s⁻¹ * l := by
            calc l * s⁻¹ = s⁻¹ * (s * l) * s⁻¹ := by group
              _ = s⁻¹ * (l * s) * s⁻¹ := by rw [hls]
              _ = s⁻¹ * l := by group
          calc l * (s⁻¹ * y) = (l * s⁻¹) * y := by group
            _ = (s⁻¹ * l) * y := by rw [hls']
            _ = s⁻¹ * (l * y) := by group
            _ = s⁻¹ * (y * l) := by rw [hyLsx l hl]
            _ = (s⁻¹ * y) * l := by group
    have hrs : r * s = s * r := Subgroup.mem_centralizer_singleton_iff.mp hrC
    have hrLs' : r ∈ L ⊓ Subgroup.centralizer ({s} : Set G) :=
      Subgroup.mem_inf.mpr ⟨(E.Rsyl hcfg).1 hrR, hrC⟩
    have hcZ : r ∈ centerOf (L ⊓ Subgroup.centralizer ({s} : Set G)) :=
      Subgroup.mem_inf.mpr ⟨hrLs', Subgroup.mem_centralizer_iff.mpr (fun l hl => hrLs l hl)⟩
    rw [centerOf_Ls_eq E hcfg hs hsR hs2 hc h4] at hcZ
    have hxrx : x * r * x⁻¹ ∈ L ⊓ Subgroup.centralizer ({s} : Set G) := by
      have h1 : x * r * x⁻¹ ∈ thompsonJ S :=
        (Subgroup.mem_normalizer_iff.mp (E.TnR hcfg hxT) r).mp hrR
      have h2 : x * r * x⁻¹ ∈ Subgroup.centralizer ({s} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc x * r * x⁻¹ * s = x * r * (x⁻¹ * s) := by group
          _ = x * r * (s * x⁻¹) := by rw [hxs']
          _ = x * (r * s) * x⁻¹ := by group
          _ = x * (s * r) * x⁻¹ := by rw [hrs]
          _ = (x * s) * r * x⁻¹ := by group
          _ = (s * x) * r * x⁻¹ := by rw [hxs]
          _ = s * (x * r * x⁻¹) := by group
      exact Subgroup.mem_inf.mpr ⟨(E.Rsyl hcfg).1 h1, h2⟩
    have hcZx : x * r * x⁻¹ ∈ centerOf (L ⊓ Subgroup.centralizer ({s} : Set G)) := by
      refine Subgroup.mem_inf.mpr ⟨hxrx, Subgroup.mem_centralizer_iff.mpr (fun l hl => ?_)⟩
      have hl' : x⁻¹ * l * x ∈ conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x := by
        rw [mem_conjR]
        have : x * (x⁻¹ * l * x) * x⁻¹ = l := by group
        rw [this]
        exact hl
      have h' := hrLsx _ hl'
      calc l * (x * r * x⁻¹) = x * ((x⁻¹ * l * x) * r) * x⁻¹ := by group
        _ = x * (r * (x⁻¹ * l * x)) * x⁻¹ := by rw [h']
        _ = (x * r * x⁻¹) * l := by group
    rw [centerOf_Ls_eq E hcfg hs hsR hs2 hc h4] at hcZx
    have hr1 : r = 1 := by
      have hrZ : r ∈ centerOf L := (Subgroup.mem_inf.mp hcZ).1
      have hrZx : r ∈ conjR (centerOf L) x := by
        rw [mem_conjR]
        exact (Subgroup.mem_inf.mp hcZx).1
      rcases E.Zcases hcfg (Z := lin2Z L (thompsonJ S)) rfl hxT hxS with ⟨hc0, -⟩ | ⟨-, -, hZ⟩
      · exact absurd hc0 hc
      · rw [hz] at hZ
        have : r ∈ centerOf L ⊓ conjR (centerOf L) x := Subgroup.mem_inf.mpr ⟨hrZ, hrZx⟩
        rw [hZ] at this
        exact Subgroup.mem_bot.mp this
    rcases hyr with rfl | rfl
    · rw [hr1]
      exact Subgroup.one_mem _
    · rw [hr1, mul_one]
      exact Subgroup.mem_zpowers s
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hcfg.S_le_T hs,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKsC hk)

end Lin2

end CFSG.QuasithinUnique.Lin2.Five

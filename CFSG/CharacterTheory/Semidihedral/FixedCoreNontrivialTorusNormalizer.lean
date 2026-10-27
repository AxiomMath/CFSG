module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusStep
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusBasic

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.GorensteinWalter

variable {G : Type} [Group G] {t s d : G} {J B W : Subgroup G}

theorem le_normalizer_of_core_eq [Finite G] {F : Subgroup G}
    (hF : (CFSG.pPrimeCore 2 F).map F.subtype = W) : F ≤ Subgroup.normalizer (W : Set G) := by
  intro f hf
  apply mem_normalizer_of_conj_mem
  intro x hx
  rw [← hF] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨f, hf⟩ * y * ⟨f, hf⟩⁻¹,
    (CFSG.pPrimeCore_normal (p := 2) (G := F)).conj_mem y hy ⟨f, hf⟩, rfl⟩

theorem mem_normalizer_centralizer [Finite G] {X : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (X : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro y hy
  have hy' : x⁻¹ * y * x⁻¹⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp hy
  rw [inv_inv] at hy'
  have h1 := hc _ hy'
  calc y * (x * c * x⁻¹) = x * ((x⁻¹ * y * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * y * x)) * x⁻¹ := by rw [h1]
    _ = x * c * x⁻¹ * y := by group

theorem centralizer_singleton_eq_zpowers (w : G) :
    Subgroup.centralizer ({w} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

namespace LocalData

variable (h : LocalData t s d J B W)
include h

theorem dihedral_card [Finite G] :
    Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers s : Subgroup G) = 8 := by
  obtain ⟨eD⟩ := MatrixFourGroupNormalizer.generatedDihedral_equiv d s h.d_orderOf
    (by rw [pow_two]; exact h.s_sq) h.s_d_inv h.s_not_mem_zpowers_d
  exact (Nat.card_congr eD.toEquiv).trans DihedralGroup.nat_card

theorem dihedral_isPGroup [Finite G] :
    IsPGroup 2 (Subgroup.zpowers d ⊔ Subgroup.zpowers s : Subgroup G) :=
  IsPGroup.of_card (n := 3) (by rw [h.dihedral_card]; norm_num)

theorem exists_sylow_of_le_normalizer [Finite G] (S : Sylow 2 G)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t})
    (hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t)
    (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) (hne : W₀ ≠ ⊥) (F : Subgroup G)
    (hPF : Subgroup.zpowers d ⊔ Subgroup.zpowers s ≤ F)
    (hFN : F ≤ Subgroup.normalizer (W₀ : Set G)) :
    ∃ P : Sylow 2 F, (P : Subgroup F).map F.subtype = Subgroup.zpowers d ⊔ Subgroup.zpowers s := by
  have hdP : d ∈ (Subgroup.zpowers d ⊔ Subgroup.zpowers s : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  refine exists_sylow_eq_of_maximal S hSC hS4 F _ hPF h.dihedral_isPGroup hdP h.d_orderOf
    (by rw [pow_two]; exact h.d_sq) fun T hT hPT hTC => ?_
  exact h.eq_of_isPGroup_of_le W₀ hW₀ hne hT (hTC.trans (inf_le_inf_left _ hFN)) hPT

theorem exists_inv_ne (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) (hne : W₀ ≠ ⊥) :
    ∃ w ∈ W₀, w⁻¹ ≠ w := by
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hw1' : w ≠ 1 := fun h' => hw1 (Subtype.ext h')
  exact ⟨w, hw, ne_inv_of_odd (h.W_odd w (hW₀ hw)) hw1'⟩

theorem d_inv_of_le (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) : ∀ x ∈ W₀, d * x * d⁻¹ = x⁻¹ :=
  fun x hx => h.d_inv x (hW₀ hx)

theorem centralizer_sup_index (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) (hne : W₀ ≠ ⊥) :
    Subgroup.centralizer (W₀ : Set G) ⊔ Subgroup.zpowers d ≤
        Subgroup.normalizer (W₀ : Set G) ∧
      (Subgroup.centralizer (W₀ : Set G)).relIndex
        (Subgroup.centralizer (W₀ : Set G) ⊔ Subgroup.zpowers d) = 2 := by
  refine ⟨sup_le (Subgroup.centralizer_le_normalizer _)
    (Subgroup.zpowers_le.mpr (h.d_mem_normalizer W₀ hW₀)), ?_⟩
  exact (Principal.relIndex_centralizer_eq_two_of_dichotomy
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)) (h.d_inv_of_le W₀ hW₀)
    (h.exists_inv_ne W₀ hW₀ hne) fun x hx => dichotomy_of_mem_sup (h.d_inv_of_le W₀ hW₀) hx).1

theorem normalizer_eq_sup [Finite G] (hW1 : W ≠ ⊥)
    (hVK : Subgroup.zpowers t ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer (W : Set G))
    (P : Sylow 2 (Subgroup.normalizer (W : Set G)))
    (hP : (P : Subgroup _).map (Subgroup.normalizer (W : Set G)).subtype =
      Subgroup.zpowers d ⊔ Subgroup.zpowers s) :
    Subgroup.normalizer (W : Set G) = Subgroup.centralizer (W : Set G) ⊔ Subgroup.zpowers d := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := Subgroup.normalizer (W : Set G)
  let K := Subgroup.centralizer (W : Set G)
  let FW := K ⊔ Subgroup.zpowers d
  have hKH : K ≤ H := Subgroup.centralizer_le_normalizer _
  have hdH : d ∈ H := h.d_mem_normalizer W le_rfl
  have hFWH : FW ≤ H := sup_le hKH (Subgroup.zpowers_le.mpr hdH)
  have hWcyc := h.W_cyclic
  have hFWn : (FW.subgroupOf H).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hc := commutator_mem_centralizer_of_isCyclic hWcyc y.2 (hFWH hx)
    have heq : ((y * x * y⁻¹ : H) : G) = ((y : G) * x * (y : G)⁻¹ * (x : G)⁻¹) * x := by
      push_cast
      group
    rw [heq]
    exact FW.mul_mem (Subgroup.mem_sup_left hc) hx
  have hsK : s ∈ K := hVK (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have hP₀FW : Subgroup.zpowers d ⊔ Subgroup.zpowers s ≤ FW :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hsK))
  have hPN : (P : Subgroup H) ≤ FW.subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    apply hP₀FW
    rw [← hP]
    exact ⟨x, hx, rfl⟩
  have htop := Sylow.normalizer_sup_eq_top' P hPN
  have hWK : W ≤ K := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => h.W_comm y hy w hw
  have hNP : Subgroup.normalizer ((P : Subgroup H) : Set H) ≤ FW.subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxN : (x : G) ∈ Subgroup.normalizer
        ((Subgroup.zpowers d ⊔ Subgroup.zpowers s : Subgroup G) : Set G) := by
      apply mem_normalizer_of_conj_mem
      intro y hy
      rw [← hP] at hy ⊢
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨x * z * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx z).mp hz, rfl⟩
    have hxt := conj_sq_eq_of_mem_normalizer h.d_orderOf h.s_sq h.s_d_inv hxN
    rw [h.d_sq] at hxt
    have hxC : (x : G) ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x : G) * t = (x : G) * t * (x : G)⁻¹ * x := by group
        _ = t * x := by rw [hxt]
    have hmem : (x : G) ∈ W ⊔ B ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers s) := by
      rw [← h.centralizer_inf_normalizer_eq W le_rfl hW1]
      exact ⟨hxC, x.2⟩
    exact (sup_le (sup_le (hWK.trans le_sup_left) (h.B_le_centralizer_W.trans le_sup_left))
      hP₀FW) hmem
  apply le_antisymm _ hFWH
  intro x hx
  have hxtop : (⟨x, hx⟩ : H) ∈ (⊤ : Subgroup H) := Subgroup.mem_top _
  rw [← htop] at hxtop
  exact Subgroup.mem_subgroupOf.mp ((sup_le hNP le_rfl) hxtop)

theorem centralizer_centralizer_eq
    (hsup : Subgroup.zpowers t ⊔ Subgroup.zpowers s ⊔ W =
      Subgroup.centralizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) : Set G))
    {g : G} (hgt : g * t * g⁻¹ = s) (hgs : g * s * g⁻¹ = t * s)
    (hgW : g ∈ Subgroup.centralizer (W : Set G)) :
    Subgroup.centralizer ((Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) = W := by
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s with hVdef
  have hWCV : W ≤ Subgroup.centralizer (V : Set G) := hsup ▸ le_sup_right
  have hVK : V ≤ Subgroup.centralizer (W : Set G) := Subgroup.le_centralizer_iff.mpr hWCV
  have hWCK : W ≤ Subgroup.centralizer
      ((Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp hk w hw).symm
  apply le_antisymm _ hWCK
  intro x hx
  have hxV : x ∈ Subgroup.centralizer (V : Set G) := Subgroup.centralizer_le hVK hx
  rw [← hsup] at hxV
  have hVW : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    Subgroup.mem_centralizer_iff.mp (hWCV hw) v hv
  obtain ⟨v, hv, w, hw, rfl⟩ := exists_mul_of_mem_sup hVW hxV
  have hvC : v ∈ Subgroup.centralizer
      ((Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
    have h1 : v = v * w * w⁻¹ := by group
    rw [h1]
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hWCK hw))
  have hgv : g * v * g⁻¹ = v := by
    have h1 := Subgroup.mem_centralizer_iff.mp hvC g hgW
    rw [h1]
    group
  have hgts : g * (t * s) * g⁻¹ = t := by
    have h1 := h.conj_inv_of_three_cycle hgt hgs
    calc g * (t * s) * g⁻¹ = g * (g⁻¹ * t * g⁻¹⁻¹) * g⁻¹ := by rw [h1]
      _ = t := by group
  rcases h.mem_V_cases hv with hv1 | hv1 | hv1 | hv1
  · rw [hv1, one_mul]
    exact hw
  · exfalso
    rw [hv1, hgt] at hgv
    exact h.s_ne hgv
  · exfalso
    rw [hv1, hgs] at hgv
    apply h.t_ne_one
    calc t = t * s * s⁻¹ := by group
      _ = 1 := by rw [hgv, mul_inv_cancel]
  · exfalso
    rw [hv1, hgts] at hgv
    apply h.s_ne_one
    calc s = t⁻¹ * (t * s) := by group
      _ = 1 := by rw [← hgv, inv_mul_cancel]

theorem torus_normalizer
    [Finite G]
    (hV : IsKleinFour (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G))
    (hWodd : Odd (Nat.card W)) (hW1 : W ≠ ⊥)
    (hsup : Subgroup.zpowers t ⊔ Subgroup.zpowers s ⊔ W =
      Subgroup.centralizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) : Set G))
    (hconf : ∀ u ∈ B, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t} : Set G))
    {g : G} (hgt : g * t * g⁻¹ = s) (hgs : g * s * g⁻¹ = t * s)
    (hgW : g ∈ Subgroup.centralizer (W : Set G))
    (S : Sylow 2 G) (hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t})
    (hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t) :
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    H = K ⊔ Subgroup.zpowers d ∧ K.relIndex H = 2 ∧
      (∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧ d ∉ K ∧
      (CFSG.pPrimeCore 2 H).map H.subtype = W ∧ (CFSG.pPrimeCore 2 K).map K.subtype = W ∧
      (∃ P : Sylow 2 K,
        (P : Subgroup K).map K.subtype = Subgroup.zpowers t ⊔ Subgroup.zpowers s) ∧
      (∀ W₀ : Subgroup G, W₀ ≤ W → W₀ ≠ ⊥ → Subgroup.normalizer (W₀ : Set G) = H) ∧
      (∀ w ∈ W, w ≠ 1 → Subgroup.centralizer {w} = K) ∧
      (∃ P : Sylow 2 H,
        (P : Subgroup H).map H.subtype = Subgroup.zpowers d ⊔ Subgroup.zpowers s) ∧
      Subgroup.centralizer ({t} : Set G) ⊓ H =
        W ⊔ B ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers s) ∧
      ∃ (F' : Type) (_ : Field F') (_ : Finite F')
        (φ : H ⧸ CFSG.pPrimeCore 2 H ≃* PGL2 F'),
        IsOddPrimePower (Nat.card F') ∧ (Nat.card F' % 8 = 3 ∨ Nat.card F' % 8 = 5) ∧
        (3 < Nat.card F' →
          ((K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 H))).map φ.toMonoidHom =
            (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range) := by
  intro H K
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s with hVdef
  have hWCV : W ≤ Subgroup.centralizer (V : Set G) := hsup ▸ le_sup_right
  have hVK : V ≤ K := Subgroup.le_centralizer_iff.mpr hWCV
  have hWK : W ≤ K := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => h.W_comm y hy w hw
  have hKH : K ≤ H := Subgroup.centralizer_le_normalizer _
  have hdH : d ∈ H := h.d_mem_normalizer W le_rfl
  have hsK : s ∈ K := hVK (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have hP₀H : Subgroup.zpowers d ⊔ Subgroup.zpowers s ≤ H :=
    sup_le (Subgroup.zpowers_le.mpr hdH) (Subgroup.zpowers_le.mpr (hKH hsK))
  obtain ⟨PH, hPH⟩ := h.exists_sylow_of_le_normalizer S hSC hS4 W le_rfl hW1 H hP₀H le_rfl
  have hHeq : H = K ⊔ Subgroup.zpowers d := h.normalizer_eq_sup hW1 hVK PH hPH
  have hdich : ∀ x ∈ H, (∀ w ∈ W, x * w * x⁻¹ = w) ∨ (∀ w ∈ W, x * w * x⁻¹ = w⁻¹) :=
    fun x hx => dichotomy_of_mem_sup h.d_inv (hHeq ▸ hx)
  obtain ⟨hKH2, hinvH, hdK⟩ := Principal.relIndex_centralizer_eq_two_of_dichotomy hdH h.d_inv
    (h.exists_inv_ne W le_rfl hW1) hdich
  obtain ⟨hOH, F', hF', hF'fin, φ, hF'K, hmod, hpsl⟩ := h.dgroup_step hV hWodd hsup hconf hgt hgs
    hgW W H le_rfl hW1 le_rfl hKH hdH hKH2 PH hPH
  have hCK := h.centralizer_centralizer_eq hsup hgt hgs hgW
  have hCW₀ : ∀ W₀ : Subgroup G, W₀ ≤ W → W₀ ≠ ⊥ → Subgroup.centralizer (W₀ : Set G) = K := by
    intro W₀ hW₀ hne
    obtain ⟨hFN, hidx⟩ := h.centralizer_sup_index W₀ hW₀ hne
    have hdF : d ∈ Subgroup.centralizer (W₀ : Set G) ⊔ Subgroup.zpowers d :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
    have hCW : K ≤ Subgroup.centralizer (W₀ : Set G) := Subgroup.centralizer_le hW₀
    have hP₀F : Subgroup.zpowers d ⊔ Subgroup.zpowers s ≤
        Subgroup.centralizer (W₀ : Set G) ⊔ Subgroup.zpowers d :=
      sup_le (Subgroup.zpowers_le.mpr hdF)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (hCW hsK)))
    obtain ⟨P, hP⟩ := h.exists_sylow_of_le_normalizer S hSC hS4 W₀ hW₀ hne _ hP₀F hFN
    obtain ⟨hO, -⟩ := h.dgroup_step hV hWodd hsup hconf hgt hgs hgW W₀ _ hW₀ hne hFN le_sup_left
      hdF hidx P hP
    have hF₀H := le_normalizer_of_core_eq hO
    apply le_antisymm _ hCW
    intro x hx
    by_contra hxK
    obtain ⟨w, hw, hwinv⟩ := h.exists_inv_ne W₀ hW₀ hne
    have hxw : x * w * x⁻¹ = w := by
      rw [← Subgroup.mem_centralizer_iff.mp hx w hw, mul_inv_cancel_right]
    exact hwinv ((hinvH x (hF₀H (Subgroup.mem_sup_left hx)) hxK w (hW₀ hw)).symm.trans hxw)
  have hNW₀ : ∀ W₀ : Subgroup G, W₀ ≤ W → W₀ ≠ ⊥ → Subgroup.normalizer (W₀ : Set G) = H := by
    intro W₀ hW₀ hne
    apply le_antisymm
    · intro x hx
      have hxK : x ∈ Subgroup.normalizer (K : Set G) := by
        have h1 := mem_normalizer_centralizer hx
        rwa [hCW₀ W₀ hW₀ hne] at h1
      have h2 := mem_normalizer_centralizer hxK
      rwa [hCK] at h2
    · intro x hx
      rcases hdich x hx with hc | hi
      · refine LocalData.mem_normalizer_of_commute W₀ hW₀ fun w hw => ?_
        calc x * w = x * w * x⁻¹ * x := by group
          _ = w * x := by rw [hc w hw]
      · exact LocalData.mem_normalizer_of_inv W₀ hW₀ hi
  have hCw : ∀ w ∈ W, w ≠ 1 → Subgroup.centralizer {w} = K := by
    intro w hw hw1
    have hz : Subgroup.zpowers w ≤ W := Subgroup.zpowers_le.mpr hw
    have hzne : Subgroup.zpowers w ≠ ⊥ := by
      intro hb
      apply hw1
      have h1 := Subgroup.mem_zpowers w
      rw [hb] at h1
      exact Subgroup.mem_bot.mp h1
    rw [centralizer_singleton_eq_zpowers, hCW₀ _ hz hzne]
  have hOK : (CFSG.pPrimeCore 2 K).map K.subtype = W := by
    apply le_antisymm
    · exact h.oddCore_le W le_rfl hW1 K (Subgroup.centralizer_le_normalizer _) hVK hV.card_four
        hgW (K.inv_mem hgW) hgt (h.conj_inv_of_three_cycle hgt hgs)
        (h.mem_normalizer_V_of_three_cycle hgt hgs) (hKH hgW) (hKH (K.inv_mem hgW)) hconf
    · intro w hw
      have hWn : (W.subgroupOf K).Normal := by
        refine ⟨fun x hx k => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        have hc := Subgroup.mem_centralizer_iff.mp k.2 x hx
        have heq : ((k * x * k⁻¹ : K) : G) = x := by
          push_cast
          rw [← hc]
          group
        rw [heq]
        exact hx
      have hle : W.subgroupOf K ≤ CFSG.pPrimeCore 2 K := le_sSup ⟨hWn, by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv]
        exact Nat.coprime_two_left.mpr hWodd⟩
      exact ⟨⟨w, hWK hw⟩, hle (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
  have hVSyl : ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = V := by
    have hPHcard : Nat.card (PH : Subgroup H) = 8 := by
      rw [← Subgroup.card_map_of_injective H.subtype_injective, hPH, h.dihedral_card]
    have hHcard := (PH : Subgroup H).card_mul_index
    rw [hPHcard] at hHcard
    have hodd : ¬ 2 ∣ (PH : Subgroup H).index := PH.not_dvd_index
    have hKcard : Nat.card K * 2 = Nat.card H := by
      have h1 := (K.subgroupOf H).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at h1
      rw [show (K.subgroupOf H).index = 2 from hKH2] at h1
      exact h1
    have hVcard : Nat.card (V.subgroupOf K) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv]
      exact hV.card_four
    have hVidx := (V.subgroupOf K).card_mul_index
    rw [hVcard] at hVidx
    have hp : IsPGroup 2 (V.subgroupOf K) := IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num)
    have hidx : ¬ 2 ∣ (V.subgroupOf K).index := by
      intro h2
      apply hodd
      have h3 : (V.subgroupOf K).index = (PH : Subgroup H).index := by omega
      rwa [← h3]
    refine ⟨hp.toSylow hidx, ?_⟩
    change (V.subgroupOf K).map K.subtype = V
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVK]
  exact ⟨hHeq, hKH2, hinvH, hdK, hOH, hOK, hVSyl, hNW₀, hCw, ⟨PH, hPH⟩,
    h.centralizer_inf_normalizer_eq W le_rfl hW1, F', hF', hF'fin, φ, hF'K, hmod, hpsl⟩

end LocalData

end CFSG.Semidihedral.FixedCoreNontrivial

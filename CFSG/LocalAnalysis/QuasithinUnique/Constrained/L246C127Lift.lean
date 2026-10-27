module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Cent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Kernel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Block

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace L246C127

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem hXQ' (X : Subgroup G) : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X

namespace Setting

variable {X T P K : Subgroup G} (S : Setting X T P K)

include S

theorem hXV : X ≤ Subgroup.normalizer (VZ T X : Set G) := S.hred.2.1

theorem hgen : K ≤ Subgroup.closure (oddPPow K) := le_closure_oddPPow S.short.1

@[expose] def cQVS : Subgroup G := cQV X (pCoreOf 2 X) (VZ T X) S.hXV (hXQ' X)

theorem Q_le_C : pCoreOf 2 X ≤ Subgroup.centralizer (VZ T X : Set G) :=
  L246.pCoreOf_le_centralizer_VZ S.charTwo S.sylow

theorem Q_le_normalizer : pCoreOf 2 X ≤ Subgroup.normalizer (K : Set G) :=
  le_normalizer_of_isSubnormal S.subnormal (S.Q_le_T.trans S.TP) S.normal_Q
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) S.hgen

theorem K_le_cQV (hUV : blockU K ≤ VZ T X) : K ≤ S.cQVS := by
  intro k hk
  refine ⟨S.PX (S.KP hk), fun q hq => ?_⟩
  have h1 : ⁅q, k⁆ ∈ (⁅pCoreOf 2 X, K⁆ : Subgroup G) := Subgroup.commutator_mem_commutator hq hk
  have h2 := hUV (S.comm_Q_le h1)
  have : ⁅k, q⁆ = ⁅q, k⁆⁻¹ := (commutatorElement_inv q k).symm
  rw [this]
  exact (VZ T X).inv_mem h2

theorem cQV_inf_centralizer_le_pCoreOf :
    S.cQVS ⊓ Subgroup.centralizer (VZ T X : Set G) ≤
      pCoreOf 2 X := by
  set Y := S.cQVS with hY
  have hXC : X ≤ Subgroup.normalizer (Subgroup.centralizer (VZ T X : Set G) : Set G) :=
    B2F.le_normalizer_centralizer S.hXV
  have hD2 : IsPGroup 2 (Y ⊓ Subgroup.centralizer (VZ T X : Set G) : Subgroup G) := by
    have := inf_centralizer_le_pCoreOf (X := X) (L := Y) (V := VZ T X) S.charTwo (cQV_le _ _)
      S.hXV (fun y hy q hq => hy.2 q hq)
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le this
  have hXD : X ≤ Subgroup.normalizer ((Y ⊓ Subgroup.centralizer (VZ T X : Set G) : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨conj_mem_cQV S.hXV (hXQ' X) hg hx1, (Subgroup.mem_normalizer_iff.1 (hXC hg) x).1 hx2⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.1 (hXC hg) x).2 hx2⟩
      have h1 := conj_mem_cQV S.hXV (hXQ' X) (X.inv_mem hg) hx1
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rw [e] at h1
      exact h1
  exact C1.le_pCoreOf_of_normalized (inf_le_left.trans (cQV_le _ _)) hXD hD2

theorem inf_centralizer_le_normalizer (hUV : blockU K ≤ VZ T X) :
    X ⊓ Subgroup.centralizer (VZ T X : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  have hcQ := S.cQV_inf_centralizer_le_pCoreOf
  set Y := S.cQVS with hY
  have hKY : K ≤ Y := S.K_le_cQV hUV
  have hXC : X ≤ Subgroup.normalizer (Subgroup.centralizer (VZ T X : Set G) : Set G) :=
    B2F.le_normalizer_centralizer S.hXV
  have hQ2 : IsPGroup 2 (pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have key : ∀ c ∈ X ⊓ Subgroup.centralizer (VZ T X : Set G), ∀ x ∈ oddPPow K, c * x * c⁻¹ ∈ K := by
    intro c hc x hx
    have hxK : x ∈ K := hx.1
    have hxX : x ∈ X := S.PX (S.KP hxK)
    have hd : c * x * c⁻¹ * x⁻¹ ∈ Y ⊓ Subgroup.centralizer (VZ T X : Set G) := by
      refine ⟨Y.mul_mem (conj_mem_cQV S.hXV (hXQ' X) hc.1 (hKY hxK)) (Y.inv_mem (hKY hxK)), ?_⟩
      have h1 : x * c⁻¹ * x⁻¹ ∈ Subgroup.centralizer (VZ T X : Set G) :=
        (Subgroup.mem_normalizer_iff.1 (hXC hxX) c⁻¹).1
          ((Subgroup.centralizer (VZ T X : Set G)).inv_mem hc.2)
      have e : c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) := by group
      rw [e]
      exact (Subgroup.centralizer (VZ T X : Set G)).mul_mem hc.2 h1
    have hdQ : c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 X := hcQ hd
    have hodd : Odd (orderOf (c * x * c⁻¹ * x⁻¹ * x)) := by
      have e : c * x * c⁻¹ * x⁻¹ * x = c * x * c⁻¹ := by group
      rw [e]
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rw [this]
      exact odd_orderOf_of_mem_oddPPow hx
    have hM : K ⊔ pCoreOf 2 X ≤ Subgroup.normalizer (K : Set G) :=
      sup_le Subgroup.le_normalizer S.Q_le_normalizer
    have hKM : (K.subgroupOf (K ⊔ pCoreOf 2 X)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hM
    have := mul_mem_of_odd_orderOf (H := K) (M := K ⊔ pCoreOf 2 X) (N := pCoreOf 2 X)
      le_sup_left hKM le_sup_right hQ2 hxK hdQ hodd
    have e : c * x * c⁻¹ * x⁻¹ * x = c * x * c⁻¹ := by group
    rwa [e] at this
  have hfwd : ∀ c ∈ X ⊓ Subgroup.centralizer (VZ T X : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
    intro c hc k hk
    have hk' := S.hgen hk
    clear hk
    induction hk' using Subgroup.closure_induction with
    | mem x hx => exact key c hc x hx
    | one => simp
    | mul x y _ _ hx hy =>
      have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
      rw [e]
      exact K.mul_mem hx hy
    | inv x _ hx =>
      have e : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
      rw [e]
      exact K.inv_mem hx
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact hfwd c hc k hk
  · intro hk
    have := hfwd c⁻¹ ((X ⊓ Subgroup.centralizer (VZ T X : Set G)).inv_mem hc) _ hk
    simpa [mul_assoc] using this

section Lift

variable {L₀ : Subgroup G}

omit [Finite G] S in
theorem conjClosure_le_L₀ {K L₀ : Subgroup G} (hKL₀ : K ≤ L₀) : conjClosure K L₀ ≤ L₀ :=
  conjClosure_le fun _ hh _ hz => L₀.mul_mem (L₀.mul_mem hh (hKL₀ hz)) (L₀.inv_mem hh)

omit [Finite G] S in
theorem isSubnormal_conjClosure {K L₀ X : Subgroup G} (hKL₀ : K ≤ L₀) (hL₀ : IsSubnormal L₀ X) :
    IsSubnormal (conjClosure K L₀) X :=
  A3.subnormal_trans (A3.subnormal_of_normal (conjClosure_le_L₀ hKL₀)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (conjClosure_le_L₀ hKL₀)).2
      (le_normalizer_conjClosure K L₀))) hL₀

theorem conjClosure_le_closure_odd (L₀ : Subgroup G) :
    conjClosure K L₀ ≤ Subgroup.closure {y | y ∈ conjClosure K L₀ ∧ Odd (orderOf y)} := by
  rw [conjClosure, Subgroup.closure_le]
  rintro x ⟨h, hh, z, hz, rfl⟩
  have hz' := S.hgen hz
  clear hz
  induction hz' using Subgroup.closure_induction with
  | mem z₀ hz₀ =>
    refine Subgroup.subset_closure ⟨mem_conjClosure hh hz₀.1, ?_⟩
    have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective z₀
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [this]
    exact odd_orderOf_of_mem_oddPPow hz₀
  | one => simp
  | mul a b _ _ ha hb =>
    have e : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

omit [Finite G] S in
theorem noTwoQuotient_of_le_closure_odd {L : Subgroup G}
    (h : L ≤ Subgroup.closure {y | y ∈ L ∧ Odd (orderOf y)}) :
    ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤ := by
  intro N _ hN
  have hgen : ∀ y ∈ L, Odd (orderOf y) → y ∈ N.map L.subtype := by
    intro y hy hodd
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hN (QuotientGroup.mk ⟨y, hy⟩)
    have h1 : orderOf (QuotientGroup.mk (s := N) (⟨y, hy⟩ : ↥L)) ∣ orderOf y := by
      have := orderOf_map_dvd (QuotientGroup.mk' N) (⟨y, hy⟩ : ↥L)
      rwa [Subgroup.orderOf_mk] at this
    rw [hk] at h1
    have hcop : Nat.Coprime (2 ^ k) (orderOf y) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
    have h2 : 2 ^ k = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl h1
    have h3 : QuotientGroup.mk (s := N) (⟨y, hy⟩ : ↥L) = 1 := by
      rw [← orderOf_eq_one_iff, hk, h2]
    exact (QuotientGroup.eq_one_iff _).1 h3
  have hle : L ≤ N.map L.subtype := by
    refine h.trans ((Subgroup.closure_le _).2 ?_)
    rintro y ⟨hy, hodd⟩
    exact hgen y hy hodd
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, hn, hnx⟩ := hle x.2
  have : n = x := Subtype.ext hnx
  rwa [← this]

omit S in
theorem charTwo_of_isSubnormal {L X : Subgroup G} (h : IsSubnormal L X) (hX : CharTwo X) :
    CharTwo L := by
  induction h with
  | refl => exact hX
  | step hle hN _ ih => exact CharTwo.of_normal (ih hX) hle hN

theorem comm_Q_conjClosure_le {W : Subgroup G} (hL₀X : L₀ ≤ X) (hKL₀ : K ≤ L₀)
    (hW : L₀ ≤ Subgroup.normalizer (W : Set G)) (hKW : blockU K ≤ W) :
    ⁅pCoreOf 2 X, conjClosure K L₀⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro q hq y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, hh, z, hz, rfl⟩ := hx
    have hhX : h ∈ X := hL₀X hh
    have hq' : h⁻¹ * q * h ∈ pCoreOf 2 X := by
      have := (Subgroup.mem_normalizer_iff.1 (hXQ' X (X.inv_mem hhX)) q).1 hq
      simpa using this
    have h1 : ⁅h⁻¹ * q * h, z⁆ ∈ blockU K :=
      S.comm_Q_le (Subgroup.commutator_mem_commutator hq' hz)
    have e : ⁅q, h * z * h⁻¹⁆ = h * ⁅h⁻¹ * q * h, z⁆ * h⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hW hh) _).1 (hKW h1)
  | one => simp
  | mul y y' hy hy' ihy ihy' =>
    have hyL₀ : y ∈ L₀ := conjClosure_le_L₀ hKL₀ hy
    have e : ⁅q, y * y'⁆ = ⁅q, y⁆ * (y * ⁅q, y'⁆ * y⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem ihy ((Subgroup.mem_normalizer_iff.1 (hW hyL₀) _).1 ihy')
  | inv y hy ihy =>
    have hyL₀ : y ∈ L₀ := conjClosure_le_L₀ hKL₀ hy
    have e : ⁅q, y⁻¹⁆ = y⁻¹ * ⁅q, y⁆⁻¹ * y := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.1 (hW (L₀.inv_mem hyL₀)) _).1 (W.inv_mem ihy)
    simpa [mul_assoc] using this

theorem inf_centralizer_conjClosure (hUV : blockU K ≤ VZ T X) (hL₀X : L₀ ≤ X) (hKL₀ : K ≤ L₀)
    (hL₀ : IsSubnormal L₀ X) :
    conjClosure K L₀ ⊓ Subgroup.centralizer (VZ T X : Set G) = pCoreOf 2 (conjClosure K L₀) := by
  have hLX : conjClosure K L₀ ≤ X := (conjClosure_le_L₀ hKL₀).trans hL₀X
  have hLsub : IsSubnormal (conjClosure K L₀) X := isSubnormal_conjClosure hKL₀ hL₀
  have hLY : conjClosure K L₀ ≤ S.cQVS :=
    conjClosure_le_cQV S.hXV (hXQ' X) (S.K_le_cQV hUV) hL₀X
  apply le_antisymm
  · exact inf_centralizer_le_pCoreOf S.charTwo hLX S.hXV fun y hy q hq => (hLY hy).2 q hq
  · intro x hx
    refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx, ?_⟩
    exact S.Q_le_C (A4.pCoreOf_le_of_subnormal 2 hLsub hx)

theorem blockU_conjClosure_le {W : Subgroup G} (hL₀X : L₀ ≤ X) (hKL₀ : K ≤ L₀)
    (hL₀ : IsSubnormal L₀ X) (hW : L₀ ≤ Subgroup.normalizer (W : Set G)) (hKW : blockU K ≤ W) :
    blockU (conjClosure K L₀) ≤ W := by
  have hLsub : IsSubnormal (conjClosure K L₀) X := isSubnormal_conjClosure hKL₀ hL₀
  refine le_trans (Subgroup.commutator_mono ?_ le_rfl) (S.comm_Q_conjClosure_le hL₀X hKL₀ hW hKW)
  exact A4.pCoreOf_le_of_subnormal 2 hLsub

theorem blockU_le_blockU_conjClosure (hUV : blockU K ≤ VZ T X) (hL₀X : L₀ ≤ X) (hKL₀ : K ≤ L₀) :
    blockU K ≤ blockU (conjClosure K L₀) := by
  have hKL : K ≤ conjClosure K L₀ := le_conjClosure K L₀
  have hLX : conjClosure K L₀ ≤ X := (conjClosure_le_L₀ hKL₀).trans hL₀X
  have hUQ : blockU K ≤ pCoreOf 2 X := hUV.trans (le_pCoreOf_of_isTwoReducedIn S.hred)
  have hUL : blockU K ≤ pCoreOf 2 (conjClosure K L₀) := by
    have hD : (conjClosure K L₀ ⊓ pCoreOf 2 X : Subgroup G) ≤ pCoreOf 2 (conjClosure K L₀) :=
      C1.le_pCoreOf_of_normalized inf_le_left
        (B2F.le_normalizer_inf Subgroup.le_normalizer (hLX.trans (hXQ' X)))
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_right)
    exact fun u hu => hD ⟨hKL (C1GN.blockU_le_self K hu), hUQ hu⟩
  calc blockU K = ⁅blockU K, K⁆ := (C1.commutator_blockU S.short).symm
    _ ≤ ⁅pCoreOf 2 (conjClosure K L₀), conjClosure K L₀⁆ := Subgroup.commutator_mono hUL hKL

end Lift

omit [Finite G] S in
theorem L₀_le_normalizer_of_le {L₀ W L : Subgroup G} (hWV : W ≤ VZ T X)
    (hL₀L : ∀ l₀ ∈ L₀, ∃ l ∈ L, ∃ c ∈ X ⊓ Subgroup.centralizer (VZ T X : Set G), l₀ = l * c)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : L₀ ≤ Subgroup.normalizer (W : Set G) := by
  have key : ∀ l₀ ∈ L₀, ∀ w ∈ W, l₀ * w * l₀⁻¹ ∈ W := by
    intro l₀ hl₀ w hw
    obtain ⟨l, hl, c, hc, rfl⟩ := hL₀L l₀ hl₀
    have hcw : c * w = w * c := (Subgroup.mem_centralizer_iff.1 hc.2 w (hWV hw)).symm
    have e : l * c * w * (l * c)⁻¹ = l * w * l⁻¹ := by
      calc l * c * w * (l * c)⁻¹ = l * (c * w) * c⁻¹ * l⁻¹ := by group
        _ = l * (w * c) * c⁻¹ * l⁻¹ := by rw [hcw]
        _ = l * w * l⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hLW hl) w).1 hw
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (L₀.inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem isShort2_conjClosure (hUV : blockU K ≤ VZ T X) {L₀ : Subgroup G} (hL₀X : L₀ ≤ X)
    (hKL₀ : K ≤ L₀) (hL₀ : IsSubnormal L₀ X)
    (hL₀L : ∀ l₀ ∈ L₀, ∃ l ∈ conjClosure K L₀,
      ∃ c ∈ X ⊓ Subgroup.centralizer (VZ T X : Set G), l₀ = l * c)
    (hq : CFSG.IsQuasisimple (↥(conjClosure K L₀) ⧸ CFSG.pCore 2 ↥(conjClosure K L₀)) ∨
      Nat.card (↥(conjClosure K L₀) ⧸ CFSG.pCore 2 ↥(conjClosure K L₀)) = 3) :
    IsShort2 (conjClosure K L₀) := by
  set L := conjClosure K L₀ with hL
  have hLX : L ≤ X := (conjClosure_le_L₀ hKL₀).trans hL₀X
  have hLsub : IsSubnormal L X := isSubnormal_conjClosure hKL₀ hL₀
  have hKL : K ≤ L := le_conjClosure K L₀
  have hUVL : blockU L ≤ VZ T X :=
    S.blockU_conjClosure_le hL₀X hKL₀ hL₀ (hL₀X.trans S.hXV) hUV
  have hVab := S.hred.2.2.1
  refine ⟨noTwoQuotient_of_le_closure_odd (S.conjClosure_le_closure_odd L₀),
    charTwo_of_isSubnormal hLsub S.charTwo, ⟨?_, ?_⟩, hq, ⟨?_, ?_⟩⟩
  ·
    intro u hu
    refine Subgroup.mem_inf.2 ⟨CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing
      (blockQ L) L (C1.le_normalizer_blockQ L) hu, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq'
    have hqC : q ∈ Subgroup.centralizer (VZ T X : Set G) :=
      S.Q_le_C (A4.pCoreOf_le_of_subnormal 2 hLsub hq')
    exact (Subgroup.mem_centralizer_iff.1 hqC u (hUVL hu)).symm
  · intro u hu
    simpa [pow_two] using hVab.2 u (hUVL hu)
  ·
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    have hKU : blockU K ≤ blockU L := S.blockU_le_blockU_conjClosure hUV hL₀X hKL₀
    have hUC : blockU L ≤ Subgroup.centralizer (L : Set G) := by
      rw [← h]; exact inf_le_right
    have h1 : ⁅blockU K, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact fun x hx => Subgroup.centralizer_le hKL (hUC (hKU hx))
    rw [C1.commutator_blockU S.short] at h1
    have h2 : blockZ K < blockU K := S.short.2.2.2.2.1
    rw [h1] at h2
    exact absurd h2 (not_lt_of_ge bot_le)
  ·
    intro W hZW hWU hWn
    by_cases hWZ : W = blockZ L
    · exact Or.inl hWZ
    right
    refine le_antisymm hWU ?_
    obtain ⟨w, hwW, hwZ⟩ : ∃ w ∈ W, w ∉ blockZ L := by
      by_contra hcon
      push Not at hcon
      exact hWZ (le_antisymm (fun w hw => hcon w hw) hZW)
    have hwU : w ∈ blockU L := hWU hwW
    have hWV : W ≤ VZ T X := hWU.trans hUVL
    have hL₀W : L₀ ≤ Subgroup.normalizer (W : Set G) := L₀_le_normalizer_of_le hWV hL₀L hWn
    have hex : ¬ ∀ h ∈ L₀, ∀ z ∈ K, (h * z * h⁻¹) * w = w * (h * z * h⁻¹) := by
      intro hall
      apply hwZ
      refine ⟨hwU, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      have hLC : L ≤ Subgroup.centralizer ({w} : Set G) := by
        rw [hL, conjClosure, Subgroup.closure_le]
        rintro x ⟨h, hh, z, hz, rfl⟩
        exact Subgroup.mem_centralizer_iff.2 fun t ht => by
          rw [Set.mem_singleton_iff.1 ht]
          exact (hall h hh z hz).symm
      exact (Subgroup.mem_centralizer_iff.1 (hLC hy) w (Set.mem_singleton w)).symm
    push Not at hex
    obtain ⟨h, hh, z, hz, hne⟩ := hex
    set w' := h⁻¹ * w * h with hw'
    have hw'W : w' ∈ W := by
      have := (Subgroup.mem_normalizer_iff.1 (hL₀W (L₀.inv_mem hh)) w).1 hwW
      simpa using this
    have hcomm : ¬ z * w' = w' * z := by
      intro heq
      apply hne
      calc h * z * h⁻¹ * w = h * (z * (h⁻¹ * w * h)) * h⁻¹ := by group
        _ = h * (w' * z) * h⁻¹ := by rw [← hw', heq]
        _ = w * (h * z * h⁻¹) := by rw [hw']; group
    set W₁ : Subgroup G := W ⊓ blockU K with hW₁
    have hKW : K ≤ Subgroup.normalizer (W : Set G) := fun k hk => hWn (hKL hk)
    have hKU : K ≤ Subgroup.normalizer (blockU K : Set G) := fun k hk =>
      C1.mem_normalizer_blockU (Subgroup.le_normalizer hk)
    have hKW₁ : K ≤ Subgroup.normalizer (W₁ : Set G) := B2F.le_normalizer_inf hKW hKU
    have hZnorm : K ≤ Subgroup.normalizer (blockZ K : Set G) := fun g hg =>
      C1.mem_normalizer_blockZ (Subgroup.le_normalizer hg)
    have hW₁norm : K ≤ Subgroup.normalizer ((W₁ ⊔ blockZ K : Subgroup G) : Set G) := fun g hg =>
      C1.mem_normalizer_sup (hKW₁ hg) (hZnorm hg)
    have hZU : blockZ K ≤ blockU K := inf_le_left
    have hcases := S.short.2.2.2.2.2 (W₁ ⊔ blockZ K) le_sup_right
      (sup_le inf_le_right hZU) hW₁norm
    have hKWU : blockU K ≤ W := by
      rcases hcases with h1 | h1
      · exfalso
        have hW2 : IsPGroup 2 W := S.V_isPGroup.to_le hWV
        have hWK1 : ⁅W, K⁆ ≤ W₁ := by
          rw [Subgroup.commutator_le]
          intro x hx k hk
          refine ⟨?_, S.comm_V_le (Subgroup.commutator_mem_commutator (hWV hx) hk)⟩
          have := (Subgroup.mem_normalizer_iff.1 (hKW hk) x⁻¹).1 (W.inv_mem hx)
          have e : ⁅x, k⁆ = x * (k * x⁻¹ * k⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact W.mul_mem hx this
        have hW₁Z : W₁ ≤ blockZ K := le_sup_left.trans h1.le
        have h2 : ⁅W₁, K⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          exact hW₁Z.trans inf_le_right
        have h3 : ⁅⁅W, K⁆, K⁆ = ⊥ :=
          le_bot_iff.1 ((Subgroup.commutator_mono hWK1 le_rfl).trans h2.le)
        have h4 : ⁅W, K⁆ ≤ ⁅⁅W, K⁆, K⁆ := commutator_le_commutator_commutator_two hW2 hKW S.hgen
        rw [h3] at h4
        have h5 : ⁅w', z⁆ ∈ (⁅W, K⁆ : Subgroup G) := Subgroup.commutator_mem_commutator hw'W hz
        have h6 := le_bot_iff.1 h4
        rw [h6, Subgroup.mem_bot] at h5
        exact hcomm (commutatorElement_eq_one_iff_mul_comm.1 h5 |>.symm)
      · exact (blockU_le_of_sup_eq S.short hKW₁ inf_le_right h1).trans inf_le_left
    exact S.blockU_conjClosure_le hL₀X hKL₀ hL₀ hL₀W hKWU

omit [Finite G] S in
theorem exists_mul_centralizer {V : Subgroup G} (hV : IsElemAbelian 2 V) {A M : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hAM : autI hV A ≤ autI hV M) {a : G} (ha : a ∈ A) :
    ∃ m ∈ M, m⁻¹ * a ∈ Subgroup.centralizer (V : Set G) := by
  have hmem : convI hV ⟨a, hAN ha⟩ ∈ autI hV M := hAM (convI_mem_autI hV ha (hAN ha))
  obtain ⟨g, hgM, hg⟩ := (mem_autI hV).1 hmem
  refine ⟨(g : G), hgM, ?_⟩
  have h1 : convI hV (g⁻¹ * ⟨a, hAN ha⟩) = 1 := by
    rw [map_mul, map_inv, hg]; group
  have h2 := (convI_eq_one_iff hV (g⁻¹ * ⟨a, hAN ha⟩)).1 h1
  simpa using h2

omit [Finite G] S in
theorem isSubnormal_subgroupOf {L X : Subgroup G} (h : IsSubnormal L X) :
    (L.subgroupOf X).IsSubnormal := by
  have h1 := A3.subnormal_comap X.subtype h
  have e2 : X.comap X.subtype = ⊤ := by ext x; simp
  rw [e2] at h1
  exact A3.subnormal_top_iff.1 h1

omit [Finite G] S in
theorem normal_autI_subgroupOf {V : Subgroup G} (hV : IsElemAbelian 2 V) {L L₀ : Subgroup G}
    (hN : L₀ ≤ Subgroup.normalizer (L : Set G)) :
    ((autI hV L).subgroupOf (autI hV L₀)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨l, hl, hln⟩ := (mem_autI hV).1 hn
  obtain ⟨g₀, hg₀, hgg⟩ := (mem_autI hV).1 g.2
  have e : ((g * n * g⁻¹ : ↥(autI hV L₀)) : MulAut (IntMod V hV)) = convI hV (g₀ * l * g₀⁻¹) := by
    simp [← hln, ← hgg, map_mul, map_inv]
  rw [e]
  refine (mem_autI hV).2 ⟨g₀ * l * g₀⁻¹, ?_, rfl⟩
  have := (Subgroup.mem_normalizer_iff.1 (hN hg₀) (l : G)).1 hl
  simpa using this

theorem exists_block_lift (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X)
    {Lstar : Subgroup (MulAut (IntMod (VZ T X) hV))}
    (hLX : Lstar ≤ autI hV X) (hsub : IsSubnormal Lstar (autI hV X))
    (hK : autI hV K ≤ Lstar) (hq : CFSG.IsQuasisimple ↥Lstar ∨ Nat.card ↥Lstar = 3)
    (hnc : ∀ N : Subgroup (MulAut (IntMod (VZ T X) hV)), N ≤ Lstar →
      (N.subgroupOf Lstar).Normal → autI hV K ≤ N → N = Lstar) :
    ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧ blockU K ≤ blockU L ∧ blockU L ≤ VZ T X ∧
      autI hV L = Lstar ∧ L ⊓ Subgroup.centralizer (VZ T X : Set G) = pCoreOf 2 L ∧
      (autI hV K = Lstar → L = K) := by
  have hXV := S.hXV
  set L₀ : Subgroup G := preI hV X hXV Lstar with hL₀def
  have hL₀X : L₀ ≤ X := preI_le hV
  have hL₀aut : autI hV L₀ = Lstar := autI_preI hV hLX
  have hKL₀ : K ≤ L₀ := by
    intro k hk
    have hkX : k ∈ X := S.PX (S.KP hk)
    refine (mem_preI hV).2 ⟨hkX, ?_⟩
    rw [convHom_apply]
    exact hK (convI_mem_autI hV hk (hXV hkX))
  have hL₀sub : IsSubnormal L₀ X := by
    have h1 := A3.subnormal_comap (convHom hV X hXV) hsub
    have e : (autI hV X).comap (convHom hV X hXV) = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      rw [Subgroup.mem_comap, ← range_convHom hV X hXV]
      exact ⟨x, rfl⟩
    rw [e] at h1
    have h2 := A3.subnormal_map X.subtype h1
    rw [Subgroup.map_top, Subgroup.range_subtype] at h2
    exact h2
  set L := conjClosure K L₀ with hL
  have hKL : K ≤ L := le_conjClosure K L₀
  have hLL₀ : L ≤ L₀ := conjClosure_le_L₀ hKL₀
  have hLX' : L ≤ X := hLL₀.trans hL₀X
  have hLsub : IsSubnormal L X := isSubnormal_conjClosure hKL₀ hL₀sub
  have hLN : L ≤ Subgroup.normalizer (VZ T X : Set G) := hLX'.trans hXV
  have hL₀N : L₀ ≤ Subgroup.normalizer (VZ T X : Set G) := hL₀X.trans hXV
  have hautL : autI hV L = Lstar := by
    have hNle : autI hV L ≤ Lstar := (autI_mono hV hLL₀).trans hL₀aut.le
    refine le_antisymm hNle ?_
    have hnorm := normal_autI_subgroupOf hV (le_normalizer_conjClosure K L₀)
    rw [hL₀aut] at hnorm
    exact (hnc (autI hV L) hNle hnorm (autI_mono hV hKL)).ge
  have hL₀L : ∀ l₀ ∈ L₀, ∃ l ∈ L, ∃ c ∈ X ⊓ Subgroup.centralizer (VZ T X : Set G), l₀ = l * c := by
    intro l₀ hl₀
    obtain ⟨m, hm, hc⟩ := exists_mul_centralizer hV hL₀N (A := L₀) (M := L)
      (by rw [hL₀aut, hautL]) hl₀
    exact ⟨m, hm, m⁻¹ * l₀, ⟨X.mul_mem (X.inv_mem (hLX' hm)) (hL₀X hl₀), hc⟩, by group⟩
  have hLC : L ⊓ Subgroup.centralizer (VZ T X : Set G) = pCoreOf 2 L :=
    S.inf_centralizer_conjClosure hUV hL₀X hKL₀ hL₀sub
  have hpc : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
    have h1 := L246.blockQ_eq_map L
    show (blockQ L).subgroupOf L = _
    rw [h1]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hker : (convHom hV L hLN).ker = CFSG.pCore 2 ↥L := by
    rw [ker_convHom, hLC, hpc]
  have hrange : (convHom hV L hLN).range = Lstar := (range_convHom hV L hLN).trans hautL
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥Lstar :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange (convHom hV L hLN))).trans
      (MulEquiv.subgroupCongr hrange)
  have hq' : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 :=
    hq.imp (fun h => CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h)
      (fun h => by rw [Nat.card_congr e.toEquiv]; exact h)
  have hshort : IsShort2 L := S.isShort2_conjClosure hUV hL₀X hKL₀ hL₀sub hL₀L hq'
  refine ⟨L, ⟨hshort, hLX', isSubnormal_subgroupOf hLsub⟩, hKL,
    S.blockU_le_blockU_conjClosure hUV hL₀X hKL₀,
    S.blockU_conjClosure_le hL₀X hKL₀ hL₀sub hL₀N hUV, hautL, hLC, ?_⟩
  intro hKe
  refine le_antisymm (conjClosure_le fun h hh z hz => ?_) hKL
  obtain ⟨m, hm, hc⟩ := exists_mul_centralizer hV hL₀N (A := L₀) (M := K)
    (by rw [hL₀aut, hKe]) hh
  have hcX : m⁻¹ * h ∈ X := X.mul_mem (X.inv_mem (S.PX (S.KP hm))) (hL₀X hh)
  have hcN := S.inf_centralizer_le_normalizer hUV ⟨hcX, hc⟩
  have hz' := (Subgroup.mem_normalizer_iff.1 hcN z).1 hz
  have e2 : h * z * h⁻¹ = m * ((m⁻¹ * h) * z * (m⁻¹ * h)⁻¹) * m⁻¹ := by group
  rw [e2]
  exact K.mul_mem (K.mul_mem hm hz') (K.inv_mem hm)

end Setting

end L246C127

end CFSG.QuasithinUnique

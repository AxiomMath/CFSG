module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg3

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace Lin2Hyp0

section N

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem card_centerOf_R_inf_centralizer_le (hc : centerOf L ≠ ⊥) {x : G} (hx : x ∈ T)
    (hxS : x ∉ S) {a : G} (haS : a ∈ S) (haR : a ∉ thompsonJ S) (ha2 : a ^ 2 = 1) :
    Nat.card (centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ≤ 2 ^ n := by
  set Z := lin2Z L (thompsonJ S) with hZdef
  have hRlt : thompsonJ S < S :=
    lt_of_le_of_ne (thompsonJ_le_self S) (fun h => haR (by rw [h]; exact haS))
  obtain ⟨-, hZS⟩ := (E.Zbasic hcfg hZdef).2
  rcases E.Zcases hcfg (Z := Z) hZdef hx hxS with ⟨hc', -⟩ | ⟨-, hZR2, hZinf⟩
  · exact absurd hc' hc
  have hZR : Z ≤ centerOf (thompsonJ S) := lin2Z_le_centerOf E.h16 hcfg hZdef
  have hZxR : conjR Z x ≤ centerOf (thompsonJ S) := by rw [hZR2]; exact le_sup_right
  have haZ : ∀ y ∈ Z, a * y * a⁻¹ ∈ Z := fun y hy =>
    (Subgroup.mem_normalizer_iff.1 (hZS haS) y).1 hy
  have haZx : ∀ y ∈ conjR Z x, a * y * a⁻¹ ∈ conjR Z x := by
    intro y hy
    rw [mem_conjR] at hy ⊢
    have h1 := haZ _ hy
    have e : x * (a * y * a⁻¹) * x⁻¹ = (x * a * x⁻¹) * (x * y * x⁻¹) * (x * a * x⁻¹)⁻¹ := by
      group
    rw [e]
    have hax : x * a * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (E.TnS hcfg hx) a).1 haS
    exact (Subgroup.mem_normalizer_iff.1 (hZS hax) _).1 hy
  have hcomm : ∀ y ∈ conjR Z x, ∀ z ∈ Z, y * z = z * y := fun y hy z hz =>
    (Subgroup.mem_centralizer_iff.1 (hZxR hy).2 z (hZR hz).1).symm
  have hle : centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({a} : Set G) ≤
      (Z ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ (conjR Z x ⊓ Subgroup.centralizer ({a} : Set G)) := by
    intro y hy
    have hy' : y ∈ Z ⊔ conjR Z x := hZR2 ▸ hy.1
    obtain ⟨z, hz, z', hz', rfl⟩ := (mem_sup_iff_of_le_normalizer
      (N := Z) (H := conjR Z x) (le_normalizer_of_commute fun z hz y hy => (hcomm y hy z hz).symm)).1 hy'
    have hya : z * z' * a = a * (z * z') := Subgroup.mem_centralizer_singleton_iff.1 hy.2
    have e : (a * z * a⁻¹) * (a * z' * a⁻¹) = z * z' := by
      calc (a * z * a⁻¹) * (a * z' * a⁻¹) = a * (z * z') * a⁻¹ := by group
        _ = z * z' := by rw [← hya]; group
    obtain ⟨e1, e2⟩ := unique_decomp hZinf (haZ z hz) hz (haZx z' hz') hz' e
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hz, ?_⟩) (Subgroup.mem_sup_right ⟨hz', ?_⟩)
    · show z ∈ Subgroup.centralizer ({a} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * a = (a * z * a⁻¹) * a := by rw [e1]
        _ = a * z := by group
    · show z' ∈ Subgroup.centralizer ({a} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z' * a = (a * z' * a⁻¹) * a := by rw [e2]
        _ = a * z' := by group
  have hA : Nat.card (Z ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = 2 ^ (n / 2) :=
    E.card_Z_inf_centralizer hcfg hRlt hZdef haS haR ha2
  obtain ⟨ha'S, ha'R, ha'2⟩ := E.conj_involution_mem hcfg haS haR ha2 hx
  have hA' : Nat.card (Z ⊓ Subgroup.centralizer ({x * a * x⁻¹} : Set G) : Subgroup G) =
      2 ^ (n / 2) := E.card_Z_inf_centralizer hcfg hRlt hZdef ha'S ha'R ha'2
  have hB : Nat.card (conjR Z x ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ≤ 2 ^ (n / 2) := by
    rw [← hA']
    refine Nat.card_le_card_of_injective (fun y => ⟨x * (y : G) * x⁻¹, ?_⟩) ?_
    · refine ⟨mem_conjR.1 y.2.1, ?_⟩
      show x * (y : G) * x⁻¹ ∈ Subgroup.centralizer ({x * a * x⁻¹} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hya : (y : G) * a = a * y := Subgroup.mem_centralizer_singleton_iff.1 y.2.2
      calc x * (y : G) * x⁻¹ * (x * a * x⁻¹) = x * ((y : G) * a) * x⁻¹ := by group
        _ = x * (a * y) * x⁻¹ := by rw [hya]
        _ = (x * a * x⁻¹) * (x * (y : G) * x⁻¹) := by group
    · intro y y' h
      apply Subtype.ext
      have := congrArg Subtype.val h
      simpa using this
  have hN : (Z ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      Subgroup.normalizer ((conjR Z x ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun y hy z hz => hcomm y hy.1 z hz.1
  have h1 := card_sup_mul_card_inf hN
  have h2 : 0 < Nat.card (Z ⊓ Subgroup.centralizer ({a} : Set G) ⊓
      (conjR Z x ⊓ Subgroup.centralizer ({a} : Set G)) : Subgroup G) := Nat.card_pos
  have h3 := Subgroup.card_le_of_le hle
  have h4 : Nat.card (Z ⊓ Subgroup.centralizer ({a} : Set G) ⊔
      (conjR Z x ⊓ Subgroup.centralizer ({a} : Set G)) : Subgroup G) ≤
      2 ^ (n / 2) * 2 ^ (n / 2) := by
    calc _ ≤ Nat.card (Z ⊓ Subgroup.centralizer ({a} : Set G) ⊔
          (conjR Z x ⊓ Subgroup.centralizer ({a} : Set G)) : Subgroup G) *
          Nat.card (Z ⊓ Subgroup.centralizer ({a} : Set G) ⊓
            (conjR Z x ⊓ Subgroup.centralizer ({a} : Set G)) : Subgroup G) :=
          Nat.le_mul_of_pos_right _ h2
      _ = _ := h1
      _ ≤ _ := by rw [hA]; exact Nat.mul_le_mul le_rfl hB
  calc _ ≤ _ := h3
    _ ≤ 2 ^ (n / 2) * 2 ^ (n / 2) := h4
    _ = 2 ^ (n / 2 + n / 2) := (pow_add _ _ _).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem not_commutative_of_mem_S_ne (hc : centerOf L ≠ ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S)
    {a : G} (haS : a ∈ S) (haR : a ∉ thompsonJ S) (ha2 : a ^ 2 = 1) :
    ¬ ∀ i ∈ thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G),
      ∀ j ∈ thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G), i * j = j * i := by
  intro hcomm
  obtain ⟨hRU, hUV⟩ := E.RUU hcfg hx hxS
  obtain ⟨hUe, hVe, hmax⟩ := E.elemU hcfg hx hxS
  have hUR : blockU L ≤ thompsonJ S := by rw [hRU]; exact le_sup_left
  have hVR : conjR (blockU L) x ≤ thompsonJ S := by rw [hRU]; exact le_sup_right
  have haU : a ∈ Subgroup.normalizer (blockU L : Set G) := E.S_le_normalizer_U hcfg haS
  have haV : a ∈ Subgroup.normalizer (conjR (blockU L) x : Set G) := by
    rw [conjR_normalizer, mem_conjR]
    apply E.S_le_normalizer_U hcfg
    exact (Subgroup.mem_normalizer_iff.1 (E.TnS hcfg hx) a).1 haS
  have hbound := E.card_centerOf_R_inf_centralizer_le hcfg hc hx hxS haS haR ha2
  have hZcard : Nat.card (centerOf L) = 2 ^ n := by
    have h := (E.Zbasic hcfg (Z := lin2Z L (thompsonJ S)) rfl).2.1
    rw [lin2_Z_eq_centerOf hc (Z := lin2Z L (thompsonJ S)) rfl] at h
    exact h
  have hUcard : Nat.card (blockU L) = 2 ^ (3 * n) := by
    rw [E.card_U' hcfg, hZcard, ← pow_add]; congr 1; omega
  have hVcard : Nat.card (conjR (blockU L) x) = 2 ^ (3 * n) := by
    rw [card_conjR, hUcard]
  have hgU := card_le_sq_card_centralizer hUe
    (fun v hv => (Subgroup.mem_normalizer_iff.1 haU v).1 hv) ha2
  have hgV := card_le_sq_card_centralizer hVe
    (fun v hv => (Subgroup.mem_normalizer_iff.1 haV v).1 hv) ha2
  rw [hUcard] at hgU
  rw [hVcard] at hgV
  have hn := hcfg.one_lt
  have hgt : ∀ k : ℕ, 2 ^ (3 * n) ≤ k ^ 2 → 2 ^ n < k := by
    intro k hk
    by_contra hle
    push Not at hle
    have h1 : k ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hle 2
    have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
    have h3 : 2 ^ (2 * n) < 2 ^ (3 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hU2n := hgt _ hgU
  have hV2n := hgt _ hgV
  have hAel : IsElemAbelian 2 ((blockU L ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
      (conjR (blockU L) x ⊓ Subgroup.centralizer ({a} : Set G))) :=
    isElemAbelian_sup_commute (IsElemAbelian.mono inf_le_left hUe)
      (IsElemAbelian.mono inf_le_left hVe)
      (fun a' ha' b' hb' => hcomm a' ⟨hUR ha'.1, ha'.2⟩ b' ⟨hVR hb'.1, hb'.2⟩)
  have hAR : (blockU L ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
      (conjR (blockU L) x ⊓ Subgroup.centralizer ({a} : Set G)) ≤ thompsonJ S :=
    sup_le (inf_le_left.trans hUR) (inf_le_left.trans hVR)
  rcases hmax _ hAR hAel with hAU | hAV
  · have hle : conjR (blockU L) x ⊓ Subgroup.centralizer ({a} : Set G) ≤
        centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({a} : Set G) := fun y hy =>
      ⟨by rw [← hUV]; exact ⟨hAU (Subgroup.mem_sup_right hy), hy.1⟩, hy.2⟩
    have := Subgroup.card_le_of_le hle
    omega
  · have hle : blockU L ⊓ Subgroup.centralizer ({a} : Set G) ≤
        centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({a} : Set G) := fun y hy =>
      ⟨by rw [← hUV]; exact ⟨hy.1, hAV (Subgroup.mem_sup_left hy)⟩, hy.2⟩
    have := Subgroup.card_le_of_le hle
    omega

theorem exists_le_conjR_T_of_delta (hc : centerOf L ≠ ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S)
    {u : G} (hu : u ∈ lin2Delta (thompsonJ S) (lin2Z L (thompsonJ S)) x) {g a : G}
    (hg : a = g⁻¹ * u * g) {P : Subgroup G} (hP : P ≤ Subgroup.centralizer ({a} : Set G))
    (hP2 : IsPGroup 2 ↥P) :
    ∃ m ∈ M, P ≤ conjR T (m * g) ∧ conjR (thompsonJ S) (m * g) = conjR (thompsonJ S) g := by
  obtain ⟨h2, -, h4, -, -, -⟩ :=
    (E.h20 G T M H S L D n hcfg (lin2Z L (thompsonJ S)) rfl hc).2 x hx hxS
  have hPM : P ≤ conjR M g := by
    intro y hy
    rw [mem_conjR]
    apply (h2 u hu).2.1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.1 (hP hy)
    rw [hg] at hya
    calc g * y * g⁻¹ * u = g * (y * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * y) * g⁻¹ := by rw [hya]
      _ = u * (g * y * g⁻¹) := by group
  have hP0 : conjR P g⁻¹ ≤ M := by rw [conjR_le_iff, inv_inv]; exact hPM
  obtain ⟨m, hmM, hmT⟩ := exists_le_conjR_of_isSylowTwoOf hcfg.cs.setting.isSylowTwoOf_M hP0
    ((isPGroup_conjR_iff 2).2 hP2)
  refine ⟨m, hmM, ?_, ?_⟩
  · have := conjR_mono hmT g
    rwa [conjR_inv_conjR, conjR_conjR] at this
  · rw [← conjR_conjR, conjR_eq_of_mem_normalizer (h4 hmM)]

end N

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2

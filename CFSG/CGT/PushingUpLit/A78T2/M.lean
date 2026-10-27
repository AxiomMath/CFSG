module

public import CFSG.CGT.PushingUpLit.A78T2.K2

public section

namespace CFSG.CGT.PushingUpLit.A78T2

open CFSG.Assembly CFSG.ABGLocalTools
open CFSG.CGT.PushingUpLit.A78Sp4 (cj ElemAb2 mul_mem_cj mem_normalizer_of_cj elemAb2_cj card_cj
  cj_mono mem_cj_iff cj_cj exists_conj_le_of_isSylowOf exists_isSylowOf_ge
  exists_eq_cj_of_isSylowOf isSylowOf_cj mem_of_commute_involution cj_eq_of_mem_normalizer_set)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L L₂ V V₂ Z J T S M M₂ : Subgroup G} {e : ℕ}

theorem T2Loc.exists_central_Z (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) :
    ∃ z ∈ Z, z ≠ 1 ∧ ∀ s ∈ S, s * z = z * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z₀, ⟨hz₀, hz₀1⟩, hfix⟩ := CFSG.CGT.PushingUpLit.A78Sp4.exists_fixed_conj_of_not_dvd
    (p := 2) h.base.isPGroup_S (X := {x : G | x ∈ Z ∧ x ≠ 1})
    (fun s hs x hx => ⟨h.base.conj_Z hs hx.1, fun h1 => hx.2 (by
      have : x = s⁻¹ * (s * x * s⁻¹) * s := by group
      rw [this, h1]; group)⟩) (by
      have hX : {x : G | x ∈ Z ∧ x ≠ 1} = (Z : Set G) \ {1} := by
        ext x; simp
      rw [hX, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem Z.one_mem,
        ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, h.base.card_Z]
      have h2 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by have := h.base.two_le; omega)
      have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
      omega)
  refine ⟨z₀, hz₀, hz₀1, fun s hs => ?_⟩
  have := hfix s hs
  calc s * z₀ = s * z₀ * s⁻¹ * s := by group
    _ = z₀ * s := by rw [this]

omit [Finite G] in
theorem cj_le_centralizer_of {S : Subgroup G} {z₀ : G}
    (hS : ∀ s ∈ S, s * z₀ = z₀ * s) (l : G) :
    cj l S ≤ Subgroup.centralizer ({l * z₀ * l⁻¹} : Set G) := by
  intro x hx
  rw [mem_cj_iff] at hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := hS _ hx
  have e1 : x = l * (l⁻¹ * x * l) * l⁻¹ := by group
  rw [e1]
  calc l * (l⁻¹ * x * l) * l⁻¹ * (l * z₀ * l⁻¹) = l * ((l⁻¹ * x * l) * z₀) * l⁻¹ := by group
    _ = l * (z₀ * (l⁻¹ * x * l)) * l⁻¹ := by rw [h1]
    _ = l * z₀ * l⁻¹ * (l * (l⁻¹ * x * l) * l⁻¹) := by group

theorem T2Loc.exists_conj_S_le_centralizer (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) {x : G}
    (hx : x ∈ J) (hxx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ m : G, cj m S ≤ Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨z₀, hz₀, hz₀1, hcen⟩ := h.exists_central_Z
  rcases h.base.inv_mem x hx hxx with hxV | hxV₂
  · obtain ⟨l, -, hl⟩ := h.side₁.trans z₀ (h.base.Z_le_V hz₀) hz₀1 x hxV hx1
    exact ⟨l, hl ▸ cj_le_centralizer_of hcen l⟩
  · obtain ⟨l, -, hl⟩ := h.side₂.trans z₀ (h.base.Z_le_V₂ hz₀) hz₀1 x hxV₂ hx1
    exact ⟨l, hl ▸ cj_le_centralizer_of hcen l⟩

omit [Finite G] in
theorem T2Side.exists_line (hs : T2Side G L V Z J T M e) (hZV : Z ≤ V) {z₀ : G} (hz₀ : z₀ ∈ Z)
    (hz₀1 : z₀ ≠ 1) {y : G} (hy : y ∈ V) (hy1 : y ≠ 1) :
    ∃ k ∈ L, y ∈ cj k Z ∧ cj k Z ≤ V := by
  obtain ⟨l, hl, hly⟩ := hs.trans z₀ (hZV hz₀) hz₀1 y hy hy1
  refine ⟨l, hl, hly ▸ mul_mem_cj l hz₀, ?_⟩
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := by
    rw [← hs.M_eq]; exact hs.L_le_M hl
  calc cj l Z ≤ cj l V := cj_mono l hZV
    _ = V := cj_eq_of_mem_normalizer_set hlN

omit [Finite G] in
theorem normalizer_cj (k : G) (H : Subgroup G) :
    Subgroup.normalizer (cj k H : Set G) = cj k (Subgroup.normalizer (H : Set G)) := by
  ext n
  rw [mem_cj_iff, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hn x
    have h1 := hn (k * x * k⁻¹)
    rw [CFSG.CGT.PushingUpLit.A78Sp4.mul_mem_cj_iff, mem_cj_iff] at h1
    rw [h1]
    have e1 : k⁻¹ * (n * (k * x * k⁻¹) * n⁻¹) * k = k⁻¹ * n * k * x * (k⁻¹ * n * k)⁻¹ := by group
    rw [e1]
  · intro hn x
    rw [mem_cj_iff, hn, mem_cj_iff]
    have e1 : k⁻¹ * n * k * (k⁻¹ * x * k) * (k⁻¹ * n * k)⁻¹ = k⁻¹ * (n * x * n⁻¹) * k := by group
    rw [e1]

omit [Finite G] in
theorem two_mul_lt_two_pow {e : ℕ} (he : 3 ≤ e) : 2 * e < 2 ^ e := by
  induction e with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> omega
    · have := ih hn
      rw [pow_succ]
      omega

theorem isSylowOf_cj_top {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (g : G) :
    IsSylowOf 2 (cj g S) ⊤ := by
  have := isSylowOf_cj hS g
  rwa [show cj g (⊤ : Subgroup G) = ⊤ from
    Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at this

theorem T2Loc.strongClosure (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) {a : G} (haS : a ∈ S)
    (haa : a * a = 1) {g : G} (hag : g⁻¹ * a * g ∈ J) : a ∈ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra haJ
  have ha1 : a ≠ 1 := fun h1 => haJ (h1 ▸ J.one_mem)
  have hx1 : g⁻¹ * a * g ≠ 1 := fun h1 => ha1 (by
    have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [this, h1]; group)
  have hxx : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [haa]; group
  obtain ⟨m, hm⟩ := h.exists_conj_S_le_centralizer hag hxx hx1
  set C := Subgroup.centralizer ({a} : Set G) with hC
  have hgm : cj (g * m) S ≤ C := by
    rw [← cj_cj]
    have h1 := cj_mono g hm
    rw [CFSG.CGT.PushingUpLit.A78Sp4.cj_centralizer_singleton] at h1
    have e1 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rw [e1] at h1
    exact h1
  have hSyl : IsSylowOf 2 (cj (g * m) S) C :=
    (isSylowOf_cj_top h.base.sylow (g * m)).of_le hgm le_top
  have hSC2 : IsPGroup 2 ↥(S ⊓ C) := h.base.isPGroup_S.to_le inf_le_left
  obtain ⟨R, hR, hSCR⟩ := exists_isSylowOf_ge hSC2 inf_le_right
  obtain ⟨c₀, -, hRc⟩ := exists_eq_cj_of_isSylowOf hSyl hR
  set h' := c₀ * (g * m) with hh'
  have hReq : R = cj h' S := by rw [hRc, cj_cj]
  have hRC : R ≤ C := hR.le
  have haR : a ∈ R := hSCR ⟨haS, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hJ'R : cj h' J ≤ R := hReq ▸ cj_mono h' h.base.J_le_S
  have hVa : ∀ U : Subgroup G, ElemAb2 U → Nat.card U = 2 ^ (2 * e) → U ≤ J → a ∈ cj h' U := by
    intro U hU hUc hUJ
    refine mem_of_commute_involution (elemAb2_cj hU h') ((card_cj h' U).trans hUc) h.base.rank
      haa fun v hv => ?_
    have hvC := hRC (hJ'R (cj_mono h' hUJ hv))
    exact (Subgroup.mem_centralizer_singleton_iff.1 hvC).symm
  have haV' := hVa V h.base.elem_V h.base.card_V h.base.V_le_J
  have haV₂' := hVa V₂ h.base.elem_V₂ h.base.card_V₂ h.base.V₂_le_J
  obtain ⟨y, hyJ, hyC, hyJ', hyy, hy1⟩ : ∃ y ∈ J, y ∈ C ∧ y ∈ cj h' J ∧ y * y = 1 ∧ y ≠ 1 := by
    set X := J ⊓ C ⊓ cj h' J with hX
    have hXp : IsPGroup 2 X := (h.base.isPGroup_S.to_le h.base.J_le_S).to_le
      (inf_le_left.trans inf_le_left)
    have hXne : X ≠ ⊥ := by
      intro hbot
      have hle : J ⊓ C ≤ R := fun x hx => hSCR ⟨h.base.J_le_S hx.1, hx.2⟩
      have hidx : (cj h' J).relIndex R ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h1 := Subgroup.relIndex_le_of_le_right hle hidx
      have h2 : (cj h' J).relIndex (J ⊓ C) = Nat.card ↥(J ⊓ C) := by
        rw [← Subgroup.inf_relIndex_right, inf_comm, ← hX, hbot, Subgroup.relIndex_bot_left]
      have h3 : (cj h' J).relIndex R = J.relIndex S := by
        rw [hReq]
        exact Subgroup.relIndex_map_map_of_injective J S (MulAut.conj h').injective
      have h4 : 2 ^ e ≤ Nat.card ↥(J ⊓ C) := h.field.card_CJ a haS haJ haa
      have h5 := h.base.index_J
      have h6 : 2 * e < 2 ^ e := two_mul_lt_two_pow h.three_le
      rw [h2, h3] at h1
      omega
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hXp
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hXne (Subgroup.card_eq_one.1 (by simpa using hk))
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
    have hxo : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    refine ⟨x, x.2.1.1, x.2.1.2, x.2.2, ?_, ?_⟩
    · rw [← pow_two, ← hxo]; exact pow_orderOf_eq_one _
    · intro h1
      rw [h1, orderOf_one] at hxo
      exact absurd hxo (by norm_num)
  obtain ⟨z₀, hz₀, hz₀1, -⟩ := h.exists_central_Z
  have hy'J : h'⁻¹ * y * h' ∈ J := (mem_cj_iff h' J y).1 hyJ'
  have hy'1 : h'⁻¹ * y * h' ≠ 1 := fun h1 => hy1 (by
    have : y = h' * (h'⁻¹ * y * h') * h'⁻¹ := by group
    rw [this, h1]; group)
  have hy'y : (h'⁻¹ * y * h') * (h'⁻¹ * y * h') = 1 := by
    calc (h'⁻¹ * y * h') * (h'⁻¹ * y * h') = h'⁻¹ * (y * y) * h' := by group
      _ = 1 := by rw [hyy]; group
  obtain ⟨U', hU'el, hU'card, hU'a, k', hY'y, hY'U'⟩ : ∃ U' : Subgroup G, ElemAb2 U' ∧
      Nat.card U' = 2 ^ (2 * e) ∧ a ∈ U' ∧ ∃ k' : G, y ∈ cj k' Z ∧ cj k' Z ≤ U' := by
    rcases h.base.inv_mem _ hy'J hy'y with hV | hV
    · obtain ⟨l, -, hly, hlV⟩ := h.side₁.exists_line h.base.Z_le_V hz₀ hz₀1 hV hy'1
      refine ⟨cj h' V, elemAb2_cj h.base.elem_V h', (card_cj h' V).trans h.base.card_V, haV',
        h' * l, ?_, ?_⟩
      · rw [← cj_cj, mem_cj_iff]; exact hly
      · rw [← cj_cj]; exact cj_mono h' hlV
    · obtain ⟨l, -, hly, hlV⟩ := h.side₂.exists_line h.base.Z_le_V₂ hz₀ hz₀1 hV hy'1
      refine ⟨cj h' V₂, elemAb2_cj h.base.elem_V₂ h', (card_cj h' V₂).trans h.base.card_V₂,
        haV₂', h' * l, ?_, ?_⟩
      · rw [← cj_cj, mem_cj_iff]; exact hly
      · rw [← cj_cj]; exact cj_mono h' hlV
  obtain ⟨k, hYy, hkL⟩ : ∃ k : G, y ∈ cj k Z ∧ ∀ x : G, k⁻¹ * x * k ∈ J → x ∈ S → x ∈ J := by
    rcases h.base.inv_mem y hyJ hyy with hV | hV
    · obtain ⟨l, hl, hly, -⟩ := h.side₁.exists_line h.base.Z_le_V hz₀ hz₀1 hV hy1
      refine ⟨l, hly, fun x hx hxS => ?_⟩
      have hxL : x ∈ L := by
        have h1 := h.side₁.conj_mem_L (h.side₁.L_le_M hl) (h.side₁.J_le_L hx)
        have e1 : l * (l⁻¹ * x * l) * l⁻¹ = x := by group
        rwa [e1] at h1
      have hxT : x ∈ T := by rw [← h.base.S_inf_M]; exact ⟨hxS, h.side₁.L_le_M hxL⟩
      rw [← h.side₁.T_inf_L]
      exact ⟨hxT, hxL⟩
    · obtain ⟨l, hl, hly, -⟩ := h.side₂.exists_line h.base.Z_le_V₂ hz₀ hz₀1 hV hy1
      refine ⟨l, hly, fun x hx hxS => ?_⟩
      have hxL : x ∈ L₂ := by
        have h1 := h.side₂.conj_mem_L (h.side₂.L_le_M hl) (h.side₂.J_le_L hx)
        have e1 : l * (l⁻¹ * x * l) * l⁻¹ = x := by group
        rwa [e1] at h1
      have hxT : x ∈ T := by rw [← h.base.S_inf_M₂]; exact ⟨hxS, h.side₂.L_le_M hxL⟩
      rw [← h.side₂.T_inf_L]
      exact ⟨hxT, hxL⟩
  have hYY : cj k' Z = cj k Z := by
    have hne : Z ⊓ cj (k⁻¹ * k') Z ≠ ⊥ := by
      intro hbot
      have hmem : k⁻¹ * y * k ∈ Z ⊓ cj (k⁻¹ * k') Z := by
        refine ⟨(mem_cj_iff k Z y).1 hYy, ?_⟩
        show k⁻¹ * y * k ∈ cj (k⁻¹ * k') Z
        rw [mem_cj_iff]
        have e1 : (k⁻¹ * k')⁻¹ * (k⁻¹ * y * k) * (k⁻¹ * k') = k'⁻¹ * y * k' := by group
        rw [e1]
        exact (mem_cj_iff k' Z y).1 hY'y
      rw [hbot, Subgroup.mem_bot] at hmem
      apply hy1
      have : y = k * (k⁻¹ * y * k) * k⁻¹ := by group
      rw [this, hmem]; group
    have h1 := h.ti _ hne
    rw [← cj_cj] at h1
    have h2 : cj k (cj k⁻¹ (cj k' Z)) = cj k Z := by rw [h1]
    rwa [cj_cj, mul_inv_cancel, CFSG.CGT.PushingUpLit.A78Sp4.cj_eq_self_of_mem (Subgroup.one_mem _)]
      at h2
  have hYU' : cj k Z ≤ U' := hYY ▸ hY'U'
  set K := Subgroup.normalizer ((cj k Z : Subgroup G) : Set G) with hK
  have hU'K : U' ≤ K := fun u hu => mem_normalizer_of_conj_mem fun x hx => by
    have hux : u * x = x * u := (hU'el u hu x (hYU' hx)).1
    rw [show u * x * u⁻¹ = x by rw [hux]; group]
    exact hx
  have hkS : IsSylowOf 2 (cj k S) K := by
    have hle : cj k S ≤ K := by
      rw [hK, normalizer_cj]
      exact cj_mono k h.base.S_le_normalizer_Z
    exact (isSylowOf_cj_top h.base.sylow k).of_le hle le_top
  obtain ⟨n, hnK, hn⟩ := exists_conj_le_of_isSylowOf hkS hU'K hU'el.isPGroup
  have h1 : cj (k⁻¹ * n) U' ≤ S := by
    have h5 := cj_mono k⁻¹ hn
    have e2 : cj k⁻¹ (cj k S) = S := by
      rw [cj_cj, inv_mul_cancel]
      exact CFSG.CGT.PushingUpLit.A78Sp4.cj_eq_self_of_mem (Subgroup.one_mem _)
    rw [e2, cj_cj] at h5
    exact h5
  have h2 : cj (k⁻¹ * n) U' ≤ J := by
    rcases h.base.A_S _ h1 (elemAb2_cj hU'el _) ((card_cj _ _).trans hU'card) with h3 | h3
    · rw [h3]; exact h.base.V_le_J
    · rw [h3]; exact h.base.V₂_le_J
  have h3 : k⁻¹ * a * k ∈ J := by
    have hna : (k⁻¹ * n) * a * (k⁻¹ * n)⁻¹ ∈ J := h2 (mul_mem_cj _ hU'a)
    have hnk : k⁻¹ * n * k ∈ Subgroup.normalizer (J : Set G) := by
      apply h.normalizer_Z_le
      rw [hK, normalizer_cj, mem_cj_iff] at hnK
      simpa using hnK
    have e1 : k⁻¹ * a * k =
        (k⁻¹ * n * k)⁻¹ * ((k⁻¹ * n) * a * (k⁻¹ * n)⁻¹) * (k⁻¹ * n * k) := by group
    rw [e1]
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnk) _).1 hna
    simpa using this
  exact haJ (hkL a h3 haS)

end CFSG.CGT.PushingUpLit.A78T2

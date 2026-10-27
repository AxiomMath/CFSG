module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroLayer
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroHeis

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open scoped Pointwise commutatorElement

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem heisLike_sylowJ₀ : HeisLike d.sylowJ₀ q := by
  have := d.finite
  have hmem2 : ∀ a, d.x₂ a ∈ d.sylowJ₀ := fun a =>
    d.mem_sylowJ₀_iff.2 ⟨a, 0, 0, by rw [d.x₅_zero, d.x₆_zero, mul_one, mul_one]⟩
  have hmem5 : ∀ b, d.x₅ b ∈ d.sylowJ₀ := fun b =>
    d.mem_sylowJ₀_iff.2 ⟨0, b, 0, by rw [d.x₂_zero, d.x₆_zero, mul_one, one_mul]⟩
  have hmem6 : ∀ c, d.x₆ c ∈ d.sylowJ₀ := fun c =>
    d.mem_sylowJ₀_iff.2 ⟨0, 0, c, by rw [d.x₂_zero, d.x₅_zero, one_mul, one_mul]⟩
  have h := heisLike_of_roots (K := d.Γ₀) d.add_self_Γ₀ (x := d.x₂) (y := d.x₅) (w := d.x₆)
    d.x₂_add d.x₅_add d.x₆_add (fun c a => (d.commute₂₆ a c).eq.symm)
    (fun c b => (d.commute₅₆ b c).eq.symm)
    (fun a b => by rw [← d.comm₂₅, commutatorElement_def]; group) d.x₆_injective
    hmem2 hmem5 hmem6
    (fun s hs => by
      obtain ⟨a, b, c, rfl⟩ := d.mem_sylowJ₀_iff.1 hs
      refine ⟨a, b, c, ?_⟩
      rw [mul_assoc, (d.commute₅₆ b c).eq, ← mul_assoc, (d.commute₂₆ a c).eq, mul_assoc])
    (by rw [d.card_sylowJ₀, d.card_Γ₀])
  rwa [d.card_Γ₀] at h

end TrialityD4Data

theorem heisLike_projUnitriangular {F : Type*} [Field F] [Finite F] [CharP F 2] :
    HeisLike (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projUnitriangular 3 F)
      (Nat.card F) := by
  set R := (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projRoots (K := F)) with hR
  have hcard : Nat.card R.S = Nat.card F ^ 3 :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_projUnitriangular 3
  have hw := injective_of_card_roots_D4 R.x_mem R.y_mem R.w_mem R.mem_S hcard
  exact heisLike_of_roots CharTwo.add_self_eq_zero R.x_add R.y_add R.w_add R.w_mul_x R.w_mul_y
    R.x_mul_y hw R.x_mem R.y_mem R.w_mem R.mem_S hcard

theorem eq_one_of_mem_oddCore_of_pow_D4 {Y : Type*} [Group Y] [Finite Y] {y : Y}
    (hy : y ∈ CFSG.oddCore Y) {k : ℕ} (hk : y ^ 2 ^ k = 1) : y = 1 := by
  have hO := CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore Y
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf y ∣ Nat.card (CFSG.oddCore Y) := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : CFSG.oddCore Y)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : Nat.Coprime (2 ^ k) (Nat.card (CFSG.oddCore Y)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hO)
  exact orderOf_eq_one_iff.1 ((h3.coprime_dvd_left h1).eq_one_of_dvd h2)

theorem factorization_two_mul_of_odd_D4 {a b : ℕ} (ha : Odd a) (hb : b ≠ 0) :
    (a * b).factorization 2 = b.factorization 2 := by
  rw [Nat.factorization_mul (Nat.pos_of_ne_zero (by rintro rfl; exact (Nat.not_odd_zero ha))).ne'
    hb, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd ha.not_two_dvd_nat, zero_add]

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

theorem inf_centralizer_eq_of_le_jZeroLayer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {X : Subgroup G}
    (hXE : X ≤ jZeroLayer d) (hXp : IsPGroup 2 X) (htX : t ∈ normalizer (X : Set G))
    (hPX : d.sylowJ₀.map L.subtype ≤ X) :
    X ⊓ centralizer ({t} : Set G) = d.sylowJ₀.map L.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [h.card_zpowers_t, pow_one])
  have hT0 : IsPGroup 2 (zpowers t ⊔ X : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hz hXp ((zpowers_le).2 htX)
  have hEH : jZeroLayer d ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    map_subtype_le _
  have hQ := (h.isSylowOf_sylowJ₀_sup_zpowers d).1
  have heq := hQ.eq_of_le (Q := (zpowers t ⊔ X) ⊓ (centralizer ((d.J₀.map L.subtype :
      Subgroup G) : Set G) ⊓ centralizer ({t} : Set G)))
    (le_inf (sup_le (hPX.trans le_sup_right) le_sup_left) hQ.le) inf_le_right
    (hT0.to_le inf_le_left)
  have htE := h.t_not_mem_jZeroLayer d hlay
  apply le_antisymm
  · intro y hy
    have hy' : y ∈ (zpowers t ⊔ X) ⊓ (centralizer ((d.J₀.map L.subtype : Subgroup G) :
        Set G) ⊓ centralizer ({t} : Set G)) :=
      ⟨mem_sup_right hy.1, hEH (hXE hy.1), hy.2⟩
    rw [heq] at hy'
    rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hy' with h1 | h1
    · exact h1
    · exfalso
      apply htE
      have := mul_mem (hXE (hPX h1)) (inv_mem (hXE hy.1))
      rwa [mul_inv_cancel_right] at this
  · exact le_inf hPX ((map_subtype_le _).trans h.L_le_centralizer)

end Setup

theorem sylowShape_of_isSylowOf_layer_D4 {Y : Type} [Group Y] [Finite Y] {s : Y}
    (hs : s * s = 1) {Kc : Subgroup (Y ⧸ CFSG.oddCore Y)} (hKc : CFSG.IsComponent Kc)
    (hZ : center Kc = ⊥)
    (hEmap : (CFSG.layer Y).map (QuotientGroup.mk' (CFSG.oddCore Y)) =
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom)
    {f : ℕ} (hf : 1 ≤ f)
    (hcase : (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom = Kc ∧
        LieModel Kc .PSL 3 2 (2 * f)) ∨
      (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom⁆ = ⊥))
    {X P : Subgroup Y} (hX : IsSylowOf 2 X (CFSG.layer Y)) (hsX : s ∈ normalizer (X : Set Y))
    (hPX : P ≤ X) (hCs : X ⊓ centralizer ({s} : Set Y) = P) (hP : HeisLike P (2 ^ f))
    {a b : Y} (ha : a ∈ P) (hb : b ∈ P) (hab : a * b ≠ b * a) :
    SylowShape X P (2 ^ f) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.oddCore Y with hO
  set π := QuotientGroup.mk' O with hπ
  set sb := π s with hsb
  set Kc' := Kc.map (MulAut.conj sb).toMonoidHom with hKc'
  have hsb2 : sb * sb = 1 := by rw [hsb, ← map_mul, hs, map_one]
  have hsbinv : sb⁻¹ = sb := inv_eq_of_mul_eq_one_right hsb2
  have hinj : ∀ x ∈ X, π x = 1 → x = 1 := by
    intro x hx hπx
    have hxO : x ∈ O := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπx
      exact hπx
    obtain ⟨k, hk⟩ := hX.isPGroup ⟨x, hx⟩
    exact eq_one_of_mem_oddCore_of_pow_D4 hxO (k := k) (by
      have := congrArg Subtype.val hk
      simpa using this)
  suffices hshape : SylowShape (X.map π) (P.map π) (2 ^ f) from
    (SylowShape.map_iff π hinj hPX).1 hshape
  have hPbar : HeisLike (P.map π) (2 ^ f) :=
    (HeisLike.map_iff π (fun x hx => hinj x (hPX hx))).2 hP
  have habbar : π a * π b ≠ π b * π a := by
    rw [← map_mul, ← map_mul]
    exact fun e => hab (eq_of_map_eq_D4 π hinj (mul_mem (hPX ha) (hPX hb))
      (mul_mem (hPX hb) (hPX ha)) e)
  have hXEb : X.map π ≤ Kc ⊔ Kc' := by
    rw [← hEmap]
    exact map_mono hX.le
  have hXsyl : IsSylowOf 2 (X.map π) (Kc ⊔ Kc') := by
    refine isSylowOf_of_card hXEb ?_
    rw [card_map_of_injOn_D4 π hinj le_rfl, hX.card_eq]
    have hk := Subgroup.card_ker_mul_card_range (π.domRestrict (CFSG.layer Y))
    rw [MonoidHom.domRestrict_range, hEmap, MonoidHom.ker_domRestrict, hπ,
      QuotientGroup.ker_mk'] at hk
    have hodd : Odd (Nat.card (O.subgroupOf (CFSG.layer Y))) := by
      have e : Nat.card (O.subgroupOf (CFSG.layer Y)) =
          Nat.card (O ⊓ CFSG.layer Y : Subgroup Y) := by
        rw [← subgroupOf_map_subtype, card_map_of_injective (CFSG.layer Y).subtype_injective]
      rw [e]
      exact Odd.of_dvd_nat (CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore Y)
        (card_dvd_of_le inf_le_left)
    rw [← hk, factorization_two_mul_of_odd_D4 hodd Nat.card_pos.ne']
  have hCbar : X.map π ⊓ centralizer ({sb} : Set (Y ⧸ O)) = P.map π := by
    apply le_antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxc⟩
      have h1 : π (x * s * x⁻¹ * s⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hsb,
          (mem_centralizer_singleton_iff.1 hxc), mul_inv_cancel_right, mul_inv_cancel]
      have h2 : x * s * x⁻¹ * s⁻¹ ∈ X := by
        rw [show x * s * x⁻¹ * s⁻¹ = x * (s * x⁻¹ * s⁻¹) by group]
        exact mul_mem hx ((mem_normalizer_iff.1 hsX x⁻¹).1 (inv_mem hx))
      have h3 := hinj _ h2 h1
      have h4 : x * s = s * x := by
        calc x * s = x * s * x⁻¹ * s⁻¹ * (s * x) := by group
          _ = s * x := by rw [h3, one_mul]
      exact ⟨x, hCs ▸ ⟨hx, mem_centralizer_singleton_iff.2 h4⟩, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxs : x ∈ centralizer ({s} : Set Y) := (hCs ▸ hx : x ∈ X ⊓ _).2
      refine ⟨⟨x, hPX hx, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
      rw [hsb, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hxs]
  rcases hcase with ⟨heq, hlie⟩ | ⟨hne, hcomm⟩
  ·
    have hsup : Kc ⊔ Kc' = Kc := by rw [heq, sup_idem]
    rw [hsup] at hXsyl
    obtain ⟨F, hFf, hFfin, hF, ⟨ψ⟩⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hlie
    have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hF
    obtain ⟨S, hS⟩ := hXsyl.exists_sylow_eq_subgroupOf
    obtain ⟨U, hU⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_projUnitriangular
      (K := F) 2 (n := 3) (by norm_num)
    set S' : Sylow 2 (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
      S.mapSurjective (f := ψ.toMonoidHom) ψ.surjective with hS'
    obtain ⟨g, hg⟩ : ∃ g : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F,
        g • U = S' := MulAction.exists_smul_eq _ U S'
    have hUh : HeisLike (U : Subgroup
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) (Nat.card F) := by
      rw [hU]
      exact heisLike_projUnitriangular
    have hS'h : HeisLike (S' : Subgroup
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) (Nat.card F) := by
      rw [← hg]
      exact (HeisLike.map_iff (MulAut.conj g).toMonoidHom fun x _ hx =>
        (MulAut.conj g).injective (hx.trans (map_one _).symm)).2 hUh
    have hSh : HeisLike (S : Subgroup Kc) (Nat.card F) := by
      have e : (S' : Subgroup
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) =
            (S : Subgroup Kc).map ψ.toMonoidHom := rfl
      rw [e] at hS'h
      exact (HeisLike.map_iff ψ.toMonoidHom fun x _ hx =>
        ψ.injective (hx.trans (map_one _).symm)).1 hS'h
    have hXbar : HeisLike (X.map π) (Nat.card F) := by
      have e : (S : Subgroup Kc).map Kc.subtype = X.map π := by
        rw [hS, subgroupOf_map_subtype, inf_eq_left.2 hXsyl.le]
      rw [← e]
      exact (HeisLike.map_iff Kc.subtype fun x _ hx => Subtype.ext hx).2 hSh
    have hF' : Nat.card F = (2 ^ f) ^ 2 := by rw [hF, ← pow_mul, mul_comm]
    rw [hF'] at hXbar
    exact hXbar.sylowShape (map_mono hPX) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ habbar
  ·
    have hKc'c : CFSG.IsComponent Kc' := CFSG.LocalCores.isComponent_map_mulEquiv _ hKc
    have hKcc : ∀ x ∈ Kc, ∀ y ∈ Kc', x * y = y * x := fun x hx y hy => by
      have := commutator_mem_commutator hx hy
      rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hKcinf : Kc ⊓ Kc' = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyc : (⟨y, hy.1⟩ : Kc) ∈ center Kc :=
        mem_center_iff.2 fun x => Subtype.ext (hKcc x x.2 y hy.2)
      rw [hZ, mem_bot] at hyc
      exact mem_bot.2 (congrArg Subtype.val hyc)
    have hNKc : Kc ⊔ Kc' ≤ normalizer (Kc : Set (Y ⧸ O)) :=
      sup_le le_normalizer (fun y hy => mem_normalizer_fintype fun x hx => by
        rw [← hKcc x hx y hy, mul_inv_cancel_right]
        exact hx)
    have hNKc' : Kc ⊔ Kc' ≤ normalizer (Kc' : Set (Y ⧸ O)) :=
      sup_le (fun y hy => mem_normalizer_fintype fun x hx => by
        rw [hKcc y hy x hx, mul_inv_cancel_right]
        exact hx) le_normalizer
    set A := X.map π ⊓ Kc with hA
    set B := X.map π ⊓ Kc' with hB
    have hAsyl : IsSylowOf 2 A Kc := hXsyl.inf_of_le_normalizer le_sup_left hNKc
    have hBsyl : IsSylowOf 2 B Kc' := hXsyl.inf_of_le_normalizer le_sup_right hNKc'
    have hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx y hy => hKcc x hx.2 y hy.2
    have hinfAB : A ⊓ B = ⊥ :=
      le_bot_iff.1 (hKcinf ▸ inf_le_inf inf_le_right inf_le_right)
    have hXAB : X.map π = A ⊔ B := by
      symm
      refine eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
      have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB).1
      rw [hinfAB, card_bot, mul_one] at h1
      have h2 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Kc Kc' hKcc).1
      rw [hKcinf, card_bot, mul_one] at h2
      rw [h1, hXsyl.card_eq, hAsyl.card_eq, hBsyl.card_eq, h2,
        Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, pow_add]
    have hsbX : sb ∈ normalizer ((X.map π : Subgroup _) : Set (Y ⧸ O)) := by
      refine mem_normalizer_fintype fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨s * x * s⁻¹, (mem_normalizer_iff.1 hsX x).1 hx, ?_⟩
      rw [map_mul, map_mul, map_inv]
    have hBA : B = A.map (MulAut.conj sb).toMonoidHom := by
      show X.map π ⊓ Kc' = (X.map π ⊓ Kc).map (MulAut.conj sb).toMonoidHom
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj sb).injective, Setup.map_conj_eq_self_D4 hsbX]
    have hdiag : (A ⊔ B) ⊓ centralizer ({sb} : Set (Y ⧸ O)) = P.map π := by
      rw [← hXAB]
      exact hCbar
    have hAh : HeisLike A (2 ^ f) :=
      heisLike_of_swap_diag hsb2 hBA hAB hinfAB (hdiag ▸ hPbar)
    have hsh := sylowShape_of_swap hsb2 hAh hBA hAB hinfAB
    rw [hdiag, ← hXAB] at hsh
    exact hsh

namespace Setup

theorem sylowShape_of_isSylowOf_jZeroLayer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {X : Subgroup G}
    (hX : IsSylowOf 2 X (jZeroLayer d)) (htX : t ∈ normalizer (X : Set G))
    (hPX : d.sylowJ₀.map L.subtype ≤ X) :
    X ⊓ centralizer ({t} : Set G) = d.sylowJ₀.map L.subtype ∧
      SylowShape X (d.sylowJ₀.map L.subtype) (2 ^ f) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCt := h.inf_centralizer_eq_of_le_jZeroLayer d hlay hX.le hX.isPGroup htX hPX
  refine ⟨hCt, ?_⟩
  obtain ⟨Kc, hKc, hZ, -, -, -, hEmap, -, hcase⟩ := hlay
  have hEH : jZeroLayer d ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    map_subtype_le _
  have hXH := hX.le.trans hEH
  have hP₀H := hPX.trans hXH
  have hXmap : (X.subgroupOf (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)).subtype = X := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 hXH]
  have hPmap : ((d.sylowJ₀.map L.subtype).subgroupOf
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)).subtype =
        d.sylowJ₀.map L.subtype := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 hP₀H]
  have hPHX : (d.sylowJ₀.map L.subtype).subgroupOf
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) ≤
        X.subgroupOf (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) :=
    fun x hx => hPX hx
  rw [← hXmap, ← hPmap]
  refine (SylowShape.map_iff _ (fun x _ hx => Subtype.ext hx) hPHX).2 ?_
  have hXl : IsSylowOf 2 (X.subgroupOf (centralizer ((d.J₀.map L.subtype : Subgroup G) :
      Set G))) (CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) := by
    have := hX
    rw [← hXmap] at this
    exact (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff _).1 this
  have hs : (⟨t, h.t_mem_centralizer_J₀ d⟩ :
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) * ⟨t, h.t_mem_centralizer_J₀ d⟩ =
        1 := Subtype.ext h.t_mul_t
  have hsX : (⟨t, h.t_mem_centralizer_J₀ d⟩ :
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) ∈
        normalizer ((X.subgroupOf (centralizer ((d.J₀.map L.subtype : Subgroup G) :
          Set G)) : Subgroup _) : Set _) :=
    mem_normalizer_fintype fun x hx => (mem_normalizer_iff.1 htX x).1 hx
  have hCs : X.subgroupOf (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) ⊓
      centralizer ({(⟨t, h.t_mem_centralizer_J₀ d⟩ :
        centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))} : Set _) =
      (d.sylowJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) := by
    ext x
    rw [mem_inf, mem_subgroupOf, mem_subgroupOf, mem_centralizer_singleton_iff, ← hCt,
      mem_inf, mem_centralizer_singleton_iff]
    exact and_congr_right fun _ => ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩
  have hPh : HeisLike ((d.sylowJ₀.map L.subtype).subgroupOf
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) (2 ^ f) := by
    have h1 : HeisLike (d.sylowJ₀.map L.subtype) (2 ^ f) :=
      (HeisLike.map_iff L.subtype fun x _ hx => Subtype.ext hx).2 d.heisLike_sylowJ₀
    rw [← hPmap] at h1
    exact (HeisLike.map_iff _ fun x _ hx => Subtype.ext hx).1 h1
  have h2 : d.x₂ 1 ∈ d.sylowJ₀ :=
    d.mem_sylowJ₀_iff.2 ⟨1, 0, 0, by rw [d.x₅_zero, d.x₆_zero, mul_one, mul_one]⟩
  have h5 : d.x₅ 1 ∈ d.sylowJ₀ :=
    d.mem_sylowJ₀_iff.2 ⟨0, 1, 0, by rw [d.x₂_zero, d.x₆_zero, mul_one, one_mul]⟩
  refine sylowShape_of_isSylowOf_layer_D4 hs hKc hZ hEmap h.one_le hcase hXl hsX hPHX hCs hPh
    (a := ⟨d.x₂ 1, hP₀H ⟨_, h2, rfl⟩⟩) (b := ⟨d.x₅ 1, hP₀H ⟨_, h5, rfl⟩⟩) ⟨_, h2, rfl⟩
    ⟨_, h5, rfl⟩ ?_
  intro e
  have e1 : ((d.x₂ 1 : L) : G) * d.x₅ 1 = d.x₅ 1 * d.x₂ 1 := congrArg Subtype.val e
  have e' : (d.x₂ 1 : L) * d.x₅ 1 = d.x₅ 1 * d.x₂ 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact e1)
  have h6 := d.comm₂₅ 1 1
  rw [commutatorElement_eq_one_iff_mul_comm.2 e', mul_one] at h6
  exact one_ne_zero (d.x₆_injective (h6.symm.trans d.x₆_zero.symm))

theorem le_normalizer_jZeroLayer {q : ℕ} (d : TrialityD4Data L q) :
    centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ≤
      normalizer ((jZeroLayer d : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_fintype fun n hn => ?_
  obtain ⟨e, he, rfl⟩ := hn
  have hN : (CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).Normal := by
    have := CFSG.LocalCores.layer_characteristic
      (G := centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))
    exact normal_of_characteristic _
  exact ⟨⟨x, hx⟩ * e * (⟨x, hx⟩ : centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))⁻¹,
    hN.conj_mem e he _, rfl⟩

theorem normalizer_le_normalizer_jZeroLayer {q : ℕ} (d : TrialityD4Data L q) :
    normalizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ≤
      normalizer ((jZeroLayer d : Subgroup G) : Set G) := by
  intro g hg
  have hgH : g ∈ normalizer ((centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :
      Subgroup G) : Set G) := mem_normalizer_fintype fun c hc => by
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro j hj
    have hj' : g⁻¹ * j * g ∈ d.J₀.map L.subtype := by
      have := (mem_normalizer_iff.1 (inv_mem hg) j).1 hj
      rwa [inv_inv] at this
    have hjc := mem_centralizer_iff.1 hc _ hj'
    calc j * (g * c * g⁻¹) = g * ((g⁻¹ * j * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * j * g)) * g⁻¹ := by rw [hjc]
      _ = g * c * g⁻¹ * j := by group
  set φ := (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)).normalizerMonoidHom
    ⟨g, hgH⟩ with hφ
  have hc := (Subgroup.characteristic_iff_map_eq.1 (CFSG.LocalCores.layer_characteristic
    (G := centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) φ
  refine mem_normalizer_fintype fun n hn => ?_
  obtain ⟨e, he, rfl⟩ := hn
  have he' : φ e ∈ CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) :=
    hc ▸ ⟨e, he, rfl⟩
  exact ⟨φ e, he', rfl⟩

theorem center_inf_centralizer_eq_V (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {X : Subgroup G}
    (hX : IsSylowOf 2 X (jZeroLayer d)) (htX : t ∈ normalizer (X : Set G))
    (hPX : d.sylowJ₀.map L.subtype ≤ X) :
    X ⊓ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) = d.V.map L.subtype := by
  obtain ⟨hCt, hsh⟩ := h.sylowShape_of_isSylowOf_jZeroLayer d hlay hX htX hPX
  apply le_antisymm
  · rintro z ⟨⟨hzX, hzc⟩, hzt⟩
    have hzP : z ∈ d.sylowJ₀.map L.subtype := hCt ▸ (⟨hzX, hzt⟩ : z ∈ X ⊓ _)
    obtain ⟨z', hz', rfl⟩ := hzP
    refine ⟨z', ?_, rfl⟩
    rw [← d.sylowJ₀_inf_centralizer]
    refine ⟨hz', mem_centralizer_iff.2 fun p hp => Subtype.ext ?_⟩
    exact mem_centralizer_iff.1 hzc _ (hPX ⟨p, hp, rfl⟩)
  · have hVP : d.V.map L.subtype ≤ d.sylowJ₀.map L.subtype := by
      rw [← d.sylowJ₀_inf_centralizer]
      exact map_mono inf_le_left
    refine le_inf ((le_inf (hVP.trans hPX) ?_).trans hsh.inf_centralizer_le)
      ((hVP.trans (map_subtype_le _)).trans h.L_le_centralizer)
    rw [← le_centralizer_iff]
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ d.sylowJ₀ ⊓ centralizer (d.sylowJ₀ : Set L) := d.sylowJ₀_inf_centralizer ▸ hv
    exact (congrArg Subtype.val (mem_centralizer_iff.1 hv'.2 p hp)).symm

theorem eq_sup_zpowers_of_isSylowOf_centralizer_J₀ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
    (hQT : d.sylowJ₀.map L.subtype ⊔ zpowers t ≤ T) :
    T = (T ⊓ jZeroLayer d) ⊔ zpowers t ∧ Nat.card (T ⊓ jZeroLayer d : Subgroup G) = (2 ^ f) ^ 6 ∧
      Nat.card T = 2 * (2 ^ f) ^ 6 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEH : jZeroLayer d ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    map_subtype_le _
  have htT : t ∈ T := hQT (mem_sup_right (mem_zpowers t))
  have htE := h.t_not_mem_jZeroLayer d hlay
  have hP₀E : d.sylowJ₀.map L.subtype ≤ jZeroLayer d :=
    (map_mono d.sylowJ₀_le_leviJ₀).trans (h.leviJ₀_map_le_jZeroLayer d hlay)
  set X := T ⊓ jZeroLayer d with hXdef
  have hXsyl : IsSylowOf 2 X (jZeroLayer d) :=
    hT.inf_of_le_normalizer hEH (le_normalizer_jZeroLayer d)
  have htX : t ∈ normalizer (X : Set G) :=
    mem_normalizer_fintype fun x hx => Subgroup.mem_inf.2 ⟨mul_mem (mul_mem htT hx.1) (inv_mem htT),
      (mem_normalizer_iff.1 (le_normalizer_jZeroLayer d (h.t_mem_centralizer_J₀ d)) x).1 hx.2⟩
  have hPX : d.sylowJ₀.map L.subtype ≤ X := le_inf (le_sup_left.trans hQT) hP₀E
  obtain ⟨hCt, hsh⟩ := h.sylowShape_of_isSylowOf_jZeroLayer d hlay hXsyl htX hPX
  have hZt := h.center_inf_centralizer_eq_V d hlay hXsyl htX hPX
  have hcardX : Nat.card X = Nat.card (X ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
    rw [hCt, card_map_of_injective L.subtype_injective, d.card_sylowJ₀, hsh.card_eq]
    ring
  have hcardZ : Nat.card (X ⊓ centralizer (X : Set G) : Subgroup G) =
      Nat.card (X ⊓ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
    rw [hZt, card_map_of_injective L.subtype_injective, d.card_V, hsh.card_center]
  have hCT : T ⊓ centralizer ({t} : Set G) ≤ d.sylowJ₀.map L.subtype ⊔ zpowers t := by
    have hQ := (h.isSylowOf_sylowJ₀_sup_zpowers d).1
    have heq := hQ.eq_of_le (Q := T ⊓ (centralizer ((d.J₀.map L.subtype : Subgroup G) :
        Set G) ⊓ centralizer ({t} : Set G))) (le_inf hQT hQ.le) inf_le_right
      (hT.isPGroup.to_le inf_le_left)
    intro y hy
    rw [← heq]
    exact ⟨hy.1, hT.le hy.1, hy.2⟩
  have hXt : X ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyX, hyt⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hyt
    rcases h.zpow_eq_one_or_eq k with h1 | h1
    · rw [h1]
      exact one_mem _
    · exact absurd (h1 ▸ hyX.2) htE
  set M := X ⊔ zpowers t with hM
  have hMset : (M : Set G) = (X : Set G) * (zpowers t : Set G) :=
    coe_mul_of_right_le_normalizer_left X (zpowers t) ((zpowers_le).2 htX)
  have hMT : M ≤ T := sup_le inf_le_left ((zpowers_le).2 htT)
  have hTM : T = M := by
    by_contra hne
    have hlt : M.subgroupOf T < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hne (le_antisymm (fun x hx => ?_) hMT)
      have : (⟨x, hx⟩ : T) ∈ M.subgroupOf T := htop ▸ mem_top _
      exact this
    have : Group.IsNilpotent T := hT.isPGroup.isNilpotent
    obtain ⟨y, hyN, hyM⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    apply hyM
    have hyt : (y : G) * t * (y : G)⁻¹ ∈ M := by
      have := (mem_normalizer_iff.1 hyN ⟨t, htT⟩).1 (mem_sup_right (mem_zpowers t))
      exact this
    have hyt' : (y : G) * t * (y : G)⁻¹ ∈ (X : Set G) * (zpowers t : Set G) := hMset ▸ hyt
    obtain ⟨x₁, hx₁, s, hs, hxs⟩ := hyt'
    have hxs : x₁ * s = (y : G) * t * (y : G)⁻¹ := hxs
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hs
    have hyH : (y : G) ∈ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := hT.le y.2
    rcases h.zpow_eq_one_or_eq k with h1 | h1
    · exfalso
      rw [h1, mul_one] at hxs
      apply htE
      have := (mem_normalizer_iff.1 (le_normalizer_jZeroLayer d (inv_mem hyH)) _).1
        (hxs ▸ hx₁.2)
      simpa [mul_assoc] using this
    · rw [h1] at hxs
      have hy₁ : t * x₁ * t ∈ X := conj_mem_D4 htX h.t_mul_t hx₁
      have hinv : t * (t * x₁ * t) * (t * (t * x₁ * t)) = 1 := by
        have e : t * (t * x₁ * t) = (y : G) * t * (y : G)⁻¹ := by
          rw [← hxs, ← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
        rw [e, show (y : G) * t * (y : G)⁻¹ * ((y : G) * t * (y : G)⁻¹) =
          (y : G) * (t * t) * (y : G)⁻¹ by group, h.t_mul_t, mul_one, mul_inv_cancel]
      obtain ⟨c, hc, hct⟩ := exists_conj_eq_of_sq_eq_one_D4 h.t_mul_t htX hsh.center_mul_self
        hsh.mul_self_mem hcardX hcardZ hy₁ hinv
      have e2 : (y : G) * t * (y : G)⁻¹ = c * t * c⁻¹ := by
        rw [← hct, ← hxs, ← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
      have hcy : c⁻¹ * y ∈ T ⊓ centralizer ({t} : Set G) := by
        refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hc.1) y.2,
          mem_centralizer_singleton_iff.2 ?_⟩
        calc c⁻¹ * y * t = c⁻¹ * ((y : G) * t * (y : G)⁻¹) * y := by group
          _ = c⁻¹ * (c * t * c⁻¹) * y := by rw [e2]
          _ = t * (c⁻¹ * y) := by group
      have hP₀M : d.sylowJ₀.map L.subtype ⊔ zpowers t ≤ M := sup_le (hPX.trans le_sup_left)
        le_sup_right
      have h2 : c⁻¹ * (y : G) ∈ M := hP₀M (hCT hcy)
      show (y : G) ∈ M
      rw [show (y : G) = c * (c⁻¹ * y) by group]
      exact mul_mem (mem_sup_left hc) h2
  refine ⟨hTM, hsh.card_eq, ?_⟩
  have h1 := ncard_mul_mul_card_inf X (zpowers t)
  rw [hXt, card_bot, mul_one, h.card_zpowers_t, hsh.card_eq, ← hMset, ← Nat.card_coe_set_eq]
    at h1
  rw [hTM]
  exact h1.trans (mul_comm _ _)

theorem card_le_two_mul_card_inf_jZeroLayer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {P Q : Subgroup G}
    (hPQ : P ≤ Q) (hQH : Q ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))
    (hQ : IsPGroup 2 Q) (hP₀Q : d.sylowJ₀.map L.subtype ⊔ zpowers t ≤ Q) :
    Nat.card P ≤ 2 * Nat.card (P ⊓ jZeroLayer d : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := centralizer ((d.J₀.map L.subtype : Subgroup G) :
    Set G))).exists_le_sylow
  set T := (S : Subgroup _).map (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)).subtype
    with hTdef
  have hT : IsSylowOf 2 T (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) := ⟨S, rfl⟩
  have hQT : Q ≤ T := fun x hx => ⟨⟨x, hQH hx⟩, hS hx, rfl⟩
  obtain ⟨-, hX, hTc⟩ := h.eq_sup_zpowers_of_isSylowOf_centralizer_J₀ d hlay hT
    (hP₀Q.trans hQT)
  have hPT : P ≤ T := hPQ.trans hQT
  have h1 := ncard_mul_mul_card_inf P (T ⊓ jZeroLayer d)
  have hinf : P ⊓ (T ⊓ jZeroLayer d) = P ⊓ jZeroLayer d := by
    rw [← inf_assoc, inf_eq_left.2 hPT]
  rw [hinf] at h1
  have h2 : ((P : Set G) * ((T ⊓ jZeroLayer d : Subgroup G) : Set G)).ncard ≤ Nat.card T := by
    calc ((P : Set G) * ((T ⊓ jZeroLayer d : Subgroup G) : Set G)).ncard ≤ (T : Set G).ncard := by
          refine Set.ncard_le_ncard ?_ (Set.toFinite _)
          rintro _ ⟨x, hx, y, hy, rfl⟩
          exact mul_mem (hPT hx) hy.1
      _ = Nat.card T := (Nat.card_coe_set_eq (T : Set G)).symm
  have hpos : 0 < (2 ^ f) ^ 6 := by positivity
  have h3 : Nat.card P * (2 ^ f) ^ 6 ≤ 2 * Nat.card (P ⊓ jZeroLayer d : Subgroup G) * (2 ^ f) ^ 6 :=
    calc Nat.card P * (2 ^ f) ^ 6 = ((P : Set G) * ((T ⊓ jZeroLayer d : Subgroup G) :
          Set G)).ncard * Nat.card (P ⊓ jZeroLayer d : Subgroup G) := by rw [← hX]; exact h1.symm
      _ ≤ Nat.card T * Nat.card (P ⊓ jZeroLayer d : Subgroup G) := Nat.mul_le_mul_right _ h2
      _ = 2 * Nat.card (P ⊓ jZeroLayer d : Subgroup G) * (2 ^ f) ^ 6 := by rw [hTc]; ring
  exact Nat.le_of_mul_le_mul_right h3 hpos

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4

module

public import CFSG.LargeExtraspecial.AS35DSixThreeB
public import CFSG.LargeExtraspecial.AS35DFourFive

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Asc77 CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_centralizer_eq_ncard (P : Subgroup G) (t : G) :
    (centralizer ({t} : Set G)).relIndex P = {x | ∃ p ∈ P, p * t * p⁻¹ = x}.ncard := by
  let _ : MulAction P G :=
    { smul := fun p x => (p : G) * x * (p : G)⁻¹
      one_smul := fun x => by
        change (1 : G) * x * 1⁻¹ = x
        group
      mul_smul := fun a b x => by
        change (a * b : G) * x * (a * b : G)⁻¹ = a * (b * x * (b : G)⁻¹) * (a : G)⁻¹
        group }
  have hstab : MulAction.stabilizer P t = (centralizer ({t} : Set G)).subgroupOf P := by
    ext p
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, mem_centralizer_singleton_iff]
    change (p : G) * t * (p : G)⁻¹ = t ↔ _
    constructor
    · intro h
      calc (p : G) * t = p * t * (p : G)⁻¹ * p := by group
        _ = t * p := by rw [h]
    · intro h
      rw [h]
      group
  have horb : MulAction.orbit P t = {x | ∃ p ∈ P, p * t * p⁻¹ = x} := by
    ext x
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  have h := MulAction.index_stabilizer (G := P) (x := t)
  rw [hstab, horb] at h
  exact h

omit [Finite G] in
theorem card_eq_relIndex_mul (P C : Subgroup G) :
    Nat.card P = C.relIndex P * Nat.card ↥(P ⊓ C) := by
  have h := Subgroup.card_mul_index (C.subgroupOf P)
  have he : Nat.card (C.subgroupOf P) = Nat.card ↥(P ⊓ C) := by
    rw [← Subgroup.inf_subgroupOf_left, inf_comm,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : C ⊓ P ≤ P)).toEquiv, inf_comm]
  rw [he] at h
  change Nat.card ↥(P ⊓ C) * C.relIndex P = Nat.card P at h
  rw [← h, mul_comm]

namespace SixThreeCtx

variable {S : Setting G} (c : SixThreeCtx S)

theorem false_of_aFive (hA : IsAFiveAt S.z c.N) : False := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨_, _, hcard, hcomm, -, -, hsurj⟩ := hA
  set Ω := S.zConj c.N with hΩ
  have hzΩ : S.z ∈ Ω := self_mem_conjIn _ _
  have htΩ : c.t ∈ Ω := c.t_mem_zConj
  have htz := c.t_ne_z
  have hnle := c.not_le_centralizer_t
  have hcqt := c.cqt_le
  have htt := c.t_mul_self
  have htQ := c.t_not_mem_QG
  have hzt : IsConj S.z c.t := isConj_iff.mpr ⟨c.g, rfl⟩
  generalize c.t = t at htΩ htz hnle hcqt htt htQ hzt
  have hconjσ : ∀ σ : Equiv.Perm Ω, Equiv.Perm.sign σ = 1 →
      ∃ h ∈ c.N, ∀ q : Ω, h * (q : G) * h⁻¹ = σ q := by
    intro σ hσ
    obtain ⟨h, hh⟩ := hsurj σ hσ
    exact ⟨h, h.2, fun q => by rw [← hh]; rfl⟩
  have hsign : ∀ {a b d e : Ω}, a ≠ b → d ≠ e →
      Equiv.Perm.sign (Equiv.swap a b * Equiv.swap d e) = 1 := by
    intro a b d e h1 h2
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h1, Equiv.Perm.sign_swap h2]
    decide
  obtain ⟨p, hpP, hpt⟩ : ∃ p ∈ c.P, p * t * p⁻¹ ≠ t := by
    by_contra! h
    refine hnle fun q hq => mem_centralizer_singleton_iff.mpr ?_
    calc q * t = q * t * q⁻¹ * q := by group
      _ = t * q := by rw [h q hq]
  have hpQ : p ∈ S.QG := (mem_inf.mp hpP).1
  have hqz : ∀ q ∈ S.QG, q * S.z * q⁻¹ = S.z := fun q hq => by
    rw [S.z_comm_QG hq]
    group
  set a := p * t * p⁻¹ with ha
  have haΩ : a ∈ Ω := conj_mem_conjIn_of_mem (c.hPN hpP) htΩ
  have haz : a ≠ S.z := by
    intro h
    apply htz
    calc t = p⁻¹ * a * p := by rw [ha]; group
      _ = S.z := by
          rw [h]
          have := hqz p⁻¹ (inv_mem hpQ)
          rwa [inv_inv] at this
  have hsub : ({S.z, t, a} : Set G) ⊆ Ω := by
    rintro x (rfl | rfl | rfl)
    · exact hzΩ
    · exact htΩ
    · exact haΩ
  have h3 : ({S.z, t, a} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm htz, Ne.symm haz⟩), Set.ncard_pair (Ne.symm hpt)]
  have hdiff : (Ω \ {S.z, t, a}).ncard = 2 := by
    rw [Set.ncard_sdiff hsub, hcard, h3]
  obtain ⟨b, d, hbd, hdbd⟩ := Set.ncard_eq_two.mp hdiff
  have hbΩ : b ∈ Ω \ {S.z, t, a} := by rw [hdbd]; exact Or.inl rfl
  have hdΩ : d ∈ Ω \ {S.z, t, a} := by rw [hdbd]; exact Or.inr rfl
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hbΩ hdΩ
  obtain ⟨hbΩ, hbz, hbt, hba⟩ := hbΩ
  obtain ⟨hdΩ, hdz, hdt, hda⟩ := hdΩ
  set Z : Ω := ⟨S.z, hzΩ⟩
  set T : Ω := ⟨t, htΩ⟩
  set A : Ω := ⟨a, haΩ⟩
  set B : Ω := ⟨b, hbΩ⟩
  set D : Ω := ⟨d, hdΩ⟩
  have hne : ∀ {x y : Ω}, (x : G) ≠ y → x ≠ y := fun h h' => h (congrArg Subtype.val h')
  have hTA : T ≠ A := hne (Ne.symm hpt)
  have hTB : T ≠ B := hne (Ne.symm hbt)
  have hTD : T ≠ D := hne (Ne.symm hdt)
  have hTZ : T ≠ Z := hne htz
  have hAB : A ≠ B := hne (Ne.symm hba)
  have hAD : A ≠ D := hne (Ne.symm hda)
  have hBD : B ≠ D := hne hbd
  have hZA : Z ≠ A := hne (Ne.symm haz)
  have hZB : Z ≠ B := hne (Ne.symm hbz)
  have hZD : Z ≠ D := hne (Ne.symm hdz)
  obtain ⟨h, hhN, hh⟩ := hconjσ _ (hsign hAB hBD)
  have ehz : h * S.z * h⁻¹ = S.z := by
    have := hh Z
    rwa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hZB hZD,
      Equiv.swap_apply_of_ne_of_ne hZA hZB] at this
  have eht : h * t * h⁻¹ = t := by
    have := hh T
    rwa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hTB hTD,
      Equiv.swap_apply_of_ne_of_ne hTA hTB] at this
  have eha : h * a * h⁻¹ = b := by
    have := hh A
    rwa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hAB hAD,
      Equiv.swap_apply_left] at this
  have ehb : h * b * h⁻¹ = d := by
    have := hh B
    rwa [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne
      (Ne.symm hAD) (Ne.symm hBD)] at this
  have hhz : h * S.z = S.z * h := by
    calc h * S.z = h * S.z * h⁻¹ * h := by group
      _ = S.z * h := by rw [ehz]
  have hth : h⁻¹ * t * h = t := by
    calc h⁻¹ * t * h = h⁻¹ * (h * t * h⁻¹) * h := by rw [eht]
      _ = t := by group
  have hconjconj : ∀ q : G, (h * q * h⁻¹) * t * (h * q * h⁻¹)⁻¹ =
      h * (q * (h⁻¹ * t * h) * q⁻¹) * h⁻¹ := fun q => by group
  have hp₁P : h * p * h⁻¹ ∈ c.P := c.conj_mem_P hhN hhz hpP
  have hp₁t : (h * p * h⁻¹) * t * (h * p * h⁻¹)⁻¹ = b := by
    rw [hconjconj, hth, ← ha, eha]
  have hp₂P : h * (h * p * h⁻¹) * h⁻¹ ∈ c.P := c.conj_mem_P hhN hhz hp₁P
  have hp₂t : (h * (h * p * h⁻¹) * h⁻¹) * t * (h * (h * p * h⁻¹) * h⁻¹)⁻¹ = d := by
    rw [hconjconj, hth, hp₁t, ehb]
  set O := {x | ∃ q ∈ c.P, q * t * q⁻¹ = x} with hO
  have hOsub : O ⊆ Ω \ {S.z} := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨conj_mem_conjIn_of_mem (c.hPN hq) htΩ, fun h' => htz ?_⟩
    have h'' : q * t * q⁻¹ = S.z := h'
    calc t = q⁻¹ * (q * t * q⁻¹) * q := by group
      _ = S.z := by
          rw [h'']
          have := hqz q⁻¹ (inv_mem (mem_inf.mp hq).1)
          rwa [inv_inv] at this
  have hOsup : ({t, a, b, d} : Set G) ⊆ O := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact ⟨1, one_mem _, by group⟩
    · exact ⟨p, hpP, rfl⟩
    · exact ⟨_, hp₁P, hp₁t⟩
    · exact ⟨_, hp₂P, hp₂t⟩
  have h4 : ({t, a, b, d} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm hpt, Ne.symm hbt, Ne.symm hdt⟩),
      Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm hba, Ne.symm hda⟩),
      Set.ncard_pair hbd]
  have hΩz : (Ω \ {S.z}).ncard = 4 := by
    rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr hzΩ), hcard, Set.ncard_singleton]
  have hOcard : O.ncard = 4 := le_antisymm (hΩz ▸ Set.ncard_le_ncard hOsub (Set.toFinite _))
    (h4 ▸ Set.ncard_le_ncard hOsup (Set.toFinite _))
  have hQP : Nat.card S.QG = 2 * Nat.card c.P := by
    have h1 := card_eq_relIndex_mul S.QG (S.QG ⊓ centralizer ({c.u} : Set G))
    rw [S.relIndex_centralizer_eq_two c.huQ c.hu1 c.huz, ← inf_assoc, inf_idem] at h1
    exact h1
  have hPt : Nat.card c.P = 4 * Nat.card ↥(S.QG ⊓ centralizer ({t} : Set G)) := by
    have h1 := card_eq_relIndex_mul c.P (centralizer ({t} : Set G))
    rw [relIndex_centralizer_eq_ncard, ← hO, hOcard] at h1
    have heq : c.P ⊓ centralizer ({t} : Set G) = S.QG ⊓ centralizer ({t} : Set G) := by
      refine le_antisymm (inf_le_inf_right _ inf_le_left) fun x hx => ?_
      exact mem_inf.mpr ⟨hcqt hx, (mem_inf.mp hx).2⟩
    rw [heq] at h1
    exact h1
  have hk : Nat.card S.QG = 2 ^ 3 * Nat.card ↥(S.QG ⊓ centralizer ({t} : Set G)) := by
    rw [hQP, hPt]
    ring
  have htM : t ∈ S.M := S.mem_M_iff.mpr (hcomm t htΩ S.z hzΩ)
  have hpos : 0 < Nat.card ↥(S.QG ⊓ centralizer ({t} : Set G)) := Nat.card_pos
  have hconjt : IsConj t (t * S.z) := by
    rcases S.fourFive htM htt htQ with ⟨hA', hk', -⟩ | ⟨-, -, -, hc'⟩ |
      ⟨-, -, -, hc'⟩
    · exfalso
      rw [hk] at hk'
      have hm := Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right hpos hk')
      have hev := even_finrank_commSpace_of_forall_eq_zero S.q_nondegenerate
        (S.rhoL_mem htM) (S.rhoL_mul_self htM htt) hA'.2.2.2.2
      rw [← hm] at hev
      exact absurd hev (by decide)
    · exact hc'
    · rwa [← hcomm t htΩ S.z hzΩ] at hc'
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hxQ : t * a ∈ S.QG := by
    rw [ha, show t * (p * t * p⁻¹) = (t * p * t⁻¹) * p⁻¹ by rw [htinv]; group]
    exact S.QG.mul_mem (S.conj_mem_QG htM hpQ) (S.QG.inv_mem hpQ)
  have hxz : t * a ≠ S.z := by
    intro hx
    obtain ⟨h', -, hh'⟩ := hconjσ _ (hsign hZB hBD)
    have e1 := hh' T
    have e2 := hh' A
    have e3 := hh' Z
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hTB hTD,
      Equiv.swap_apply_of_ne_of_ne hTZ hTB] at e1
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hAB hAD,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hZA) hAB] at e2
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hZB hZD,
      Equiv.swap_apply_left] at e3
    apply hbz
    calc b = h' * S.z * h'⁻¹ := e3.symm
      _ = h' * (t * a) * h'⁻¹ := by rw [hx]
      _ = (h' * t * h'⁻¹) * (h' * a * h'⁻¹) := by group
      _ = t * a := by rw [e1, e2]
      _ = S.z := hx
  obtain ⟨h'', -, hh''⟩ := hconjσ _ (hsign (Ne.symm hZA) hBD)
  have e1 := hh'' T
  have e2 := hh'' A
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hTB hTD,
    Equiv.swap_apply_of_ne_of_ne hTA hTZ] at e1
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hAB hAD, Equiv.swap_apply_left] at e2
  have hxconj : h'' * (t * a) * h''⁻¹ = t * S.z := by
    calc h'' * (t * a) * h''⁻¹ = (h'' * t * h''⁻¹) * (h'' * a * h''⁻¹) := by group
      _ = t * S.z := by rw [e1, e2]
  have hzx : IsConj S.z (t * a) :=
    (hzt.trans hconjt).trans (isConj_iff.mpr ⟨h''⁻¹, by
      rw [← hxconj]
      group⟩)
  obtain ⟨k, hk⟩ := isConj_iff.mp hzx
  exact hxz (hk ▸ c.hW k (hk ▸ hxQ))

end SixThreeCtx

end Setting

end CFSG.LargeExtraspecial

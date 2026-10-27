module

public import CFSG.GF2Type.Smith1980Orth.S2Basic
public import CFSG.LargeExtraspecial.FS77Orth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module Equiv CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.Open

theorem card_le_two_of_mul_self {T : Subgroup (Perm (Fin 3))} (hT : ∀ x ∈ T, x * x = 1) :
    Nat.card T ≤ 2 := by
  have hp : IsPGroup 2 T := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hT x x.2)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hdvd : Nat.card T ∣ Nat.card (Perm (Fin 3)) := Subgroup.card_subgroup_dvd_card T
  have h6 : Nat.card (Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rw [hn, h6] at hdvd
  have hn1 : n ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h4 : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 hlt
    have := dvd_trans h4 hdvd
    norm_num at this
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    _ = 2 := by norm_num

theorem exists_prod_decomp {Y : Type*} [Group Y] [Finite Y] {Xs : Subgroup Y} (n : ℕ)
    (hrank : ∀ E : Subgroup Y, E ≤ Xs → (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 2 ^ n)
    {Λ : Subgroup (Perm (Fin 3) × Y)} (hΛ : ∀ l ∈ Λ, l * l = 1) (hΛX : ∀ l ∈ Λ, l.2 ∈ Xs)
    (hcard : Nat.card Λ = 2 ^ (n + 1)) :
    ∃ τ : Perm (Fin 3), τ ≠ 1 ∧ τ * τ = 1 ∧ ∃ P : Subgroup Y, P ≤ Xs ∧ Nat.card P = 2 ^ n ∧
      (∀ x ∈ P, x * x = 1) ∧ ∀ σ x, (σ, x) ∈ Λ ↔ (σ = 1 ∨ σ = τ) ∧ x ∈ P := by
  set T : Subgroup (Perm (Fin 3)) := Λ.map (MonoidHom.fst _ _) with hT
  set P : Subgroup Y := Λ.map (MonoidHom.snd _ _) with hP
  have hT2 : ∀ x ∈ T, x * x = 1 := by
    rintro _ ⟨l, hl, rfl⟩
    simpa using congrArg Prod.fst (hΛ l hl)
  have hP2 : ∀ x ∈ P, x * x = 1 := by
    rintro _ ⟨l, hl, rfl⟩
    simpa using congrArg Prod.snd (hΛ l hl)
  have hPX : P ≤ Xs := by
    rintro _ ⟨l, hl, rfl⟩
    exact hΛX l hl
  have hTc := card_le_two_of_mul_self hT2
  have hPc := hrank P hPX hP2
  have hle : Λ ≤ T.prod P := fun l hl => ⟨⟨l, hl, rfl⟩, ⟨l, hl, rfl⟩⟩
  have hcardp : Nat.card (T.prod P) = Nat.card T * Nat.card P := by
    rw [Nat.card_congr (Subgroup.prodEquiv T P).toEquiv, Nat.card_prod]
  have hΛle : Nat.card Λ ≤ Nat.card (T.prod P) := Subgroup.card_le_of_le hle
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, mul_comm]
  have h32 : Nat.card T * Nat.card P = 2 ^ (n + 1) := by
    have := Nat.mul_le_mul hTc hPc
    rw [hpow] at hcard ⊢
    omega
  have hT2c : Nat.card T = 2 ∧ Nat.card P = 2 ^ n := by
    rw [hpow] at h32
    rcases (by omega : Nat.card T = 1 ∨ Nat.card T = 2) with h | h
    · rw [h] at h32
      omega
    · rw [h] at h32
      omega
  have hΛeq : Λ = T.prod P := Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hTne : T ≠ ⊥ := fun h => by
    have := hT2c.1
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨τ, hτT⟩, hτ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hTne
  have hτ1' : τ ≠ 1 := fun h => hτ1 (Subtype.ext h)
  have hττ : τ * τ = 1 := hT2 τ hτT
  have hTeq : zpowers τ = T := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hτT) ?_
    rw [S7.card_zpowers_of_mul_self hττ hτ1', hT2c.1]
  refine ⟨τ, hτ1', hττ, P, hPX, hT2c.2, hP2, fun σ x => ?_⟩
  rw [hΛeq, Subgroup.mem_prod, ← hTeq, Setting.mem_zpowers_iff_of_mul_self hττ]

section Orthogonal

open CFSG.RankThree.OrthogonalInvolutions
open CFSG.ClassicalGroups.Orthogonal (eichler)
open TauCeti.QuadraticMap (orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] [Finite V]
  {q : QuadraticForm (ZMod 2) V}

private theorem eq_bot_of_normalized_omega (hq : q.polarBilin.Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP2 : ∀ x ∈ P, x * x = 1)
    (hP : ∀ ω ∈ omegaGroup q hq, ω ∈ normalizer (P : Set (V ≃ₗ[ZMod 2] V))) : P = ⊥ := by
  have hpg : IsPGroup 2 P := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hP2 x x.2)⟩
  let F : Submodule (ZMod 2) V :=
    { carrier := {v | ∀ x ∈ P, x v = v}
      add_mem' := fun {a b} ha hb x hx => by rw [map_add, ha x hx, hb x hx]
      zero_mem' := fun x _ => map_zero _
      smul_mem' := fun c v hv x hx => by rw [map_smul, hv x hx] }
  have hF : ∀ s u, q s = 0 → QuadraticMap.polar q s u = 0 → ∀ v ∈ F, eichler q s u v ∈ F := by
    intro s u _ _ v hv x hx
    have hω : eichler q s u ∈ omegaGroup q hq := FS77.eichler_mem_omegaGroup hq s u
    have hx' : (eichler q s u)⁻¹ * x * eichler q s u ∈ P := by
      have := (mem_normalizer_iff.mp (hP _ (inv_mem hω)) x).mp hx
      simpa using this
    have h1 := hv _ hx'
    have e : x * eichler q s u = eichler q s u * ((eichler q s u)⁻¹ * x * eichler q s u) := by
      group
    calc x (eichler q s u v) = (x * eichler q s u) v := (LinearEquiv.mul_apply _ _ _).symm
      _ = (eichler q s u * ((eichler q s u)⁻¹ * x * eichler q s u)) v := by rw [e]
      _ = eichler q s u (((eichler q s u)⁻¹ * x * eichler q s u) v) := LinearEquiv.mul_apply _ _ _
      _ = eichler q s u v := by rw [h1]
  rcases FS77.eichler_invariant_submodule hq h3 F hF with h | h
  · exfalso
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    obtain ⟨u, -, hu0, hfix⟩ := S4.exists_fixed_ne_zero hpg P.subtype (U := ⊤)
      (fun _ _ _ => Submodule.mem_top) top_ne_bot
    have hu : u ∈ F := fun x hx => hfix ⟨x, hx⟩
    rw [h] at hu
    exact hu0 ((Submodule.mem_bot _).mp hu)
  · refine eq_bot_iff.mpr fun x hx => ?_
    have hall : ∀ v, x v = v := fun v => (show v ∈ F by rw [h]; trivial) x hx
    exact mem_bot.mpr (LinearEquiv.ext hall)

private theorem eq_one_of_conj_mem_normalizer (hq : q.polarBilin.Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) {X P : Subgroup (V ≃ₗ[ZMod 2] V)} (hXO : X ≤ orthogonalGroup q)
    (hΩX : omegaGroup q hq ≤ X) (hP2 : ∀ x ∈ P, x * x = 1) (hP1 : P ≠ ⊥)
    (hNN : ∀ C : Subgroup (V ≃ₗ[ZMod 2] V), C ≤ X → (∀ u ∈ X, ∀ c ∈ C, u * c * u⁻¹ ∈ C) →
      (∀ c ∈ C, c * c = 1) → C = ⊥)
    {c : V ≃ₗ[ZMod 2] V} (hcX : c ∈ X)
    (hc : ∀ u ∈ X, u⁻¹ * c * u ∈ normalizer (P : Set (V ≃ₗ[ZMod 2] V))) : c = 1 := by
  let C : Subgroup (V ≃ₗ[ZMod 2] V) :=
    { carrier := {c | c ∈ X ∧ ∀ u ∈ X, u⁻¹ * c * u ∈ normalizer (P : Set (V ≃ₗ[ZMod 2] V))}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun u hu => by
        have e : u⁻¹ * (a * b) * u = (u⁻¹ * a * u) * (u⁻¹ * b * u) := by group
        rw [e]
        exact mul_mem (ha.2 u hu) (hb.2 u hu)⟩
      one_mem' := ⟨one_mem _, fun u hu => by simpa using one_mem _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun u hu => by
        have e : u⁻¹ * a⁻¹ * u = (u⁻¹ * a * u)⁻¹ := by group
        rw [e]
        exact inv_mem (ha.2 u hu)⟩ }
  have hCX : C ≤ X := fun c hc => hc.1
  have hCn : ∀ u ∈ X, ∀ c ∈ C, u * c * u⁻¹ ∈ C := by
    intro u hu c hc
    refine ⟨mul_mem (mul_mem hu hc.1) (inv_mem hu), fun w hw => ?_⟩
    have e : w⁻¹ * (u * c * u⁻¹) * w = (u⁻¹ * w)⁻¹ * c * (u⁻¹ * w) := by group
    rw [e]
    exact hc.2 _ (mul_mem (inv_mem hu) hw)
  have : IsSimpleGroup (omegaGroup q hq) := S45Q.isSimpleGroup_omegaGroup_of_six_le hq h6
  have hKn : (C.subgroupOf (omegaGroup q hq)).Normal := by
    refine ⟨fun k hk ω => ?_⟩
    rw [mem_subgroupOf] at hk ⊢
    exact hCn _ (hΩX ω.2) _ hk
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.subgroupOf (omegaGroup q hq)) with hK | hK
  · have hC2 : ∀ c ∈ C, c * c = 1 := by
      intro c hcC
      have hsq : c * c ∈ omegaGroup q hq := FS77.sq_mem_omegaGroup hq (hXO (hCX hcC))
      have hmem : (⟨c * c, hsq⟩ : omegaGroup q hq) ∈ C.subgroupOf (omegaGroup q hq) :=
        mem_subgroupOf.mpr (mul_mem hcC hcC)
      rw [hK] at hmem
      exact congrArg Subtype.val (mem_bot.mp hmem)
    have hCbot := hNN C hCX hCn hC2
    have hcC : c ∈ C := ⟨hcX, hc⟩
    rw [hCbot] at hcC
    exact mem_bot.mp hcC
  · exfalso
    refine hP1 (eq_bot_of_normalized_omega hq (by omega) hP2 fun ω hω => ?_)
    have hmem : (⟨ω, hω⟩ : omegaGroup q hq) ∈ C.subgroupOf (omegaGroup q hq) := by
      rw [hK]
      exact mem_top _
    have := (mem_subgroupOf.mp hmem).2 1 (one_mem X)
    simpa using this

end Orthogonal

section Coord

variable {G : Type} [Group G] [Finite G] {S : Setting G}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private instance instFiniteLinearEquivZMod2 [Finite V] : Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective

structure Coord (S : Setting G) (X : Subgroup (V ≃ₗ[ZMod 2] V)) where
  ι : S.Mbar →* Perm (Fin 3) × (V ≃ₗ[ZMod 2] V)
  inj : Function.Injective ι
  snd_mem : ∀ m, (ι m).2 ∈ X
  surj : ∀ (σ : Perm (Fin 3)) (y : V ≃ₗ[ZMod 2] V), y ∈ X → ∃ m, ι m = (σ, y)

noncomputable def Coord.ofEquiv {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    (e : S.Mbar ≃* Perm (Fin 3) × X) : Coord S X where
  ι := (MonoidHom.prodMap (MonoidHom.id _) X.subtype).comp e.toMonoidHom
  inj := fun a b h => by
    have h' : ((e a).1, ((e a).2 : V ≃ₗ[ZMod 2] V)) = ((e b).1, ((e b).2 : V ≃ₗ[ZMod 2] V)) := h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact e.injective (Prod.ext h1 (Subtype.ext h2))
  snd_mem := fun m => (e m).2.2
  surj := fun σ y hy => ⟨e.symm (σ, ⟨y, hy⟩), by simp⟩

variable {X : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem Coord.eq_bot_of_normal (K : Coord S X) {C : Subgroup (V ≃ₗ[ZMod 2] V)} (hCX : C ≤ X)
    (hCn : ∀ u ∈ X, ∀ c ∈ C, u * c * u⁻¹ ∈ C) (hC2 : ∀ c ∈ C, c * c = 1) : C = ⊥ := by
  let D : Subgroup S.Mbar := ((⊥ : Subgroup (Perm (Fin 3))).prod C).comap K.ι
  have hDmem : ∀ m, m ∈ D ↔ (K.ι m).1 = 1 ∧ (K.ι m).2 ∈ C := fun m => by
    simp [D, Subgroup.mem_prod]
  have hDn : D.Normal := ⟨fun d hd m => by
    rw [hDmem] at hd ⊢
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, hd.1, mul_one,
        mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv]
      exact hCn _ (K.snd_mem m) _ hd.2⟩
  have hD2 : IsPGroup 2 D := fun d => ⟨1, Subtype.ext (by
    have hd := (hDmem d).mp d.2
    have h : ((d : S.Mbar)) * d = 1 := K.inj (by
      rw [map_mul, map_one]
      exact Prod.ext (by rw [Prod.fst_mul, hd.1, mul_one]; rfl) (hC2 _ hd.2))
    simpa [pow_two] using h)⟩
  have hle : D ≤ CFSG.pCore 2 S.Mbar := le_sSup ⟨hDn, hD2⟩
  rw [S.pCore_Mbar_eq_bot] at hle
  refine eq_bot_iff.mpr fun c hc => ?_
  obtain ⟨m, hm⟩ := K.surj 1 c (hCX hc)
  have hmD : m ∈ D := (hDmem m).mpr ⟨by rw [hm], by rw [hm]; exact hc⟩
  have hm1 : m = 1 := mem_bot.mp (hle hmD)
  rw [mem_bot]
  have := congrArg Prod.snd hm
  rw [hm1, map_one] at this
  exact this.symm

theorem Coord.exists_decomp (K : Coord S X) [Finite V] {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (m : ℕ)
    (hrank : ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ X → (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 2 ^ m)
    (hcard : Nat.card (S.Lbar g) = 2 ^ (m + 1)) :
    ∃ τ : Perm (Fin 3), τ ≠ 1 ∧ τ * τ = 1 ∧ ∃ P : Subgroup (V ≃ₗ[ZMod 2] V), P ≤ X ∧
      Nat.card P = 2 ^ m ∧ (∀ x ∈ P, x * x = 1) ∧
      ∀ m : S.Mbar, (m : S.O) ∈ S.Lbar g ↔
        ((K.ι m).1 = 1 ∨ (K.ι m).1 = τ) ∧ (K.ι m).2 ∈ P := by
  let Λ : Subgroup (Perm (Fin 3) × (V ≃ₗ[ZMod 2] V)) := ((S.Lbar g).subgroupOf S.Mbar).map K.ι
  have hmem : ∀ m : S.Mbar, K.ι m ∈ Λ ↔ (m : S.O) ∈ S.Lbar g := by
    intro m
    constructor
    · rintro ⟨m', hm', hmm⟩
      rw [K.inj hmm] at hm'
      exact mem_subgroupOf.mp hm'
    · intro h
      exact ⟨m, mem_subgroupOf.mpr h, rfl⟩
  have hΛcard : Nat.card Λ = 2 ^ (m + 1) := by
    rw [Subgroup.card_map_of_injective K.inj, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S.Lbar_le_Mbar g)).toEquiv
  have hΛ2 : ∀ l ∈ Λ, l * l = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (S4.mul_self_of_mem_Lbar S haQ (mem_subgroupOf.mp hm))
    rw [this, map_one]
  have hΛX : ∀ l ∈ Λ, l.2 ∈ X := by
    rintro _ ⟨m, -, rfl⟩
    exact K.snd_mem m
  obtain ⟨τ, hτ1, hττ, P, hPX, hPc, hP2, hP⟩ := exists_prod_decomp m hrank hΛ2 hΛX hΛcard
  exact ⟨τ, hτ1, hττ, P, hPX, hPc, hP2, fun m => (hmem m).symm.trans (hP (K.ι m).1 (K.ι m).2)⟩

theorem Coord.exists_Lbar_conj (K : Coord S X) {g : G} {τ : Perm (Fin 3)}
    {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hL : ∀ m : S.Mbar, (m : S.O) ∈ S.Lbar g ↔
      ((K.ι m).1 = 1 ∨ (K.ι m).1 = τ) ∧ (K.ι m).2 ∈ P)
    {u : V ≃ₗ[ZMod 2] V} (hu : u ∈ X) :
    ∃ h : S.M, ∀ s : S.Mbar, (s : S.O) ∈ S.Lbar ((h : G) * g) ↔
      ((K.ι s).1 = 1 ∨ (K.ι s).1 = τ) ∧ u⁻¹ * (K.ι s).2 * u ∈ P := by
  obtain ⟨m₀, hm₀⟩ := K.surj 1 u hu
  obtain ⟨h, hh⟩ : ∃ h : S.M, S.ρ h = (m₀ : S.O) := MonoidHom.mem_range.mp m₀.2
  refine ⟨h, fun s => ?_⟩
  rw [S4.mem_Lbar_mul_iff S h g]
  have hs' : (S.ρ h)⁻¹ * (s : S.O) * S.ρ h = ((m₀⁻¹ * s * m₀ : S.Mbar) : S.O) := by
    rw [hh]
    rfl
  have e1 : (K.ι (m₀⁻¹ * s * m₀)).1 = (K.ι s).1 := by
    simp only [map_mul, map_inv, hm₀, Prod.fst_mul, Prod.fst_inv, inv_one, one_mul, mul_one]
  have e2 : (K.ι (m₀⁻¹ * s * m₀)).2 = u⁻¹ * (K.ι s).2 * u := by
    simp only [map_mul, map_inv, hm₀, Prod.snd_mul, Prod.snd_inv]
  rw [hs', hL, e1, e2]

theorem card_Lbar_mul (h : S.M) (g : G) :
    Nat.card (S.Lbar ((h : G) * g)) = Nat.card (S.Lbar g) := by
  rw [Lbar_mul S h g]
  exact Subgroup.card_map_of_injective (MulAut.conj (S.ρ h)).injective

theorem mem_normalizer_of_forall {X P : Subgroup (V ≃ₗ[ZMod 2] V)} (hPX : P ≤ X)
    {w : V ≃ₗ[ZMod 2] V} (hw : w ∈ X) (h : ∀ x ∈ X, x ∈ P ↔ w * x * w⁻¹ ∈ P) :
    w ∈ normalizer (P : Set (V ≃ₗ[ZMod 2] V)) := by
  rw [mem_normalizer_iff]
  intro x
  by_cases hx : x ∈ X
  · exact h x hx
  · refine ⟨fun hxP => absurd (hPX hxP) hx, fun hxP => absurd ?_ hx⟩
    have h1 : w⁻¹ * (w * x * w⁻¹) * w ∈ X := mul_mem (mul_mem (inv_mem hw) (hPX hxP)) hw
    simpa [mul_assoc] using h1

theorem Coord.Rbar_ne_Lbar (K : Coord S X) {g : G} {τ : Perm (Fin 3)}
    {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hPX : P ≤ X)
    (hL : ∀ m : S.Mbar, (m : S.O) ∈ S.Lbar g ↔
      ((K.ι m).1 = 1 ∨ (K.ι m).1 = τ) ∧ (K.ι m).2 ∈ P)
    {T : S.Mbar} (hT : K.ι T = (τ, 1)) (hy : ∃ y ∈ X, ∃ x ∈ P, y * x * y⁻¹ ∉ P) :
    Rbar S g (T : S.O) ≠ S.Lbar g := by
  obtain ⟨y, hyX, x, hxP, hyx⟩ := hy
  obtain ⟨h, hh⟩ := K.exists_Lbar_conj hL hyX
  have hTy : (T : S.O) ∈ S.Lbar ((h : G) * g) := by
    rw [hh T, hT]
    exact ⟨Or.inr rfl, by simpa using one_mem P⟩
  intro hR
  have hle : S.Lbar ((h : G) * g) ≤ S.Lbar g := hR ▸ S4.Lbar_mul_le_Rbar hTy
  have heq : S.Lbar ((h : G) * g) = S.Lbar g :=
    Subgroup.eq_of_le_of_card_ge hle (card_Lbar_mul h g).ge
  obtain ⟨s, hs⟩ := K.surj 1 (y * x * y⁻¹) (mul_mem (mul_mem hyX (hPX hxP)) (inv_mem hyX))
  have hs1 : (s : S.O) ∈ S.Lbar ((h : G) * g) := by
    rw [hh s, hs]
    refine ⟨Or.inl rfl, ?_⟩
    have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    show y⁻¹ * (y * x * y⁻¹) * y ∈ P
    rw [e]
    exact hxP
  rw [heq, hL s, hs] at hs1
  exact hyx hs1.2

private theorem Coord.Nbar_le (K : Coord S X) [Finite V] [FiniteDimensional (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} (hq : q.polarBilin.Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) (hXO : X ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hΩX : CFSG.RankThree.OrthogonalInvolutions.omegaGroup q hq ≤ X)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    {τ : Perm (Fin 3)} (hτ1 : τ ≠ 1) (hττ : τ * τ = 1) {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hPX : P ≤ X) (hP2 : ∀ x ∈ P, x * x = 1) (hP1 : P ≠ ⊥)
    (hL : ∀ m : S.Mbar, (m : S.O) ∈ S.Lbar g ↔
      ((K.ι m).1 = 1 ∨ (K.ι m).1 = τ) ∧ (K.ι m).2 ∈ P)
    {T : S.Mbar} (hT : K.ι T = (τ, 1)) : Nbar S g (T : S.O) ≤ zpowers (T : S.O) := by
  intro n hn
  have hnM : n ∈ S.Mbar := S4.Rbar_le_Mbar hn.1
  obtain ⟨m, hm⟩ : ∃ m : S.Mbar, (m : S.O) = n := ⟨⟨n, hnM⟩, rfl⟩
  have hcomm : m * T = T * m := by
    have hc0 := S4.commute_of_mem_Rbar haQ hn.1
    rw [← hm] at hc0
    exact Subtype.ext hc0
  have hσ : (K.ι m).1 = 1 ∨ (K.ι m).1 = τ := by
    have h1 := congrArg (fun z => (K.ι z).1) hcomm
    simp only [map_mul, Prod.fst_mul, hT] at h1
    exact S7.perm_three_eq_of_comm_inv _ _ hττ hτ1 h1
  have hw : (K.ι m).2 = 1 := by
    refine eq_one_of_conj_mem_normalizer hq h6 hXO hΩX hP2 hP1
      (fun C hCX hCn hC2 => K.eq_bot_of_normal hCX hCn hC2) (K.snd_mem m) ?_
    intro u hu
    obtain ⟨h, hh⟩ := K.exists_Lbar_conj hL hu
    have hTu : (T : S.O) ∈ S.Lbar ((h : G) * g) := by
      rw [hh T, hT]
      exact ⟨Or.inr rfl, by simpa using one_mem P⟩
    have hnorm := S4.Nbar_le_normalizer haQ hne (S4.Lbar_mul_mem_Dset hTu) hn
    refine mem_normalizer_of_forall hPX (mul_mem (mul_mem (inv_mem hu) (K.snd_mem m)) hu)
      fun x hx => ?_
    obtain ⟨s, hs⟩ := K.surj 1 (u * x * u⁻¹) (mul_mem (mul_mem hu hx) (inv_mem hu))
    have h1 := mem_normalizer_iff.mp hnorm (s : S.O)
    have hcoe : ((m * s * m⁻¹ : S.Mbar) : S.O) = n * (s : S.O) * n⁻¹ := by
      rw [← hm]
      rfl
    rw [← hcoe, hh s, hh (m * s * m⁻¹)] at h1
    have hs1 : (K.ι s).1 = 1 := by rw [hs]
    have hs2 : (K.ι s).2 = u * x * u⁻¹ := by rw [hs]
    have hms1 : (K.ι (m * s * m⁻¹)).1 = 1 := by
      simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, hs1, mul_one, mul_inv_cancel]
    have hms2 : (K.ι (m * s * m⁻¹)).2 = (K.ι m).2 * (u * x * u⁻¹) * ((K.ι m).2)⁻¹ := by
      simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, hs2]
    have e1 : u⁻¹ * (u * x * u⁻¹) * u = x := by group
    have e2 : u⁻¹ * ((K.ι m).2 * (u * x * u⁻¹) * ((K.ι m).2)⁻¹) * u =
        (u⁻¹ * (K.ι m).2 * u) * x * (u⁻¹ * (K.ι m).2 * u)⁻¹ := by group
    rw [hs1, hs2, hms1, hms2, e1, e2] at h1
    simpa using h1
  have hι : K.ι m = ((K.ι m).1, 1) := Prod.ext rfl hw
  rcases hσ with h | h
  · have hm1 : m = 1 := K.inj (Prod.ext (by simp [h]) (by simp [hw]))
    rw [← hm, hm1]
    exact one_mem _
  · have hmT : m = T := K.inj (Prod.ext (by rw [h, hT]) (by rw [hw, hT]))
    rw [← hm, hmT]
    exact mem_zpowers _

theorem perm_commutator_mem_alternating (σ τ : Perm (Fin 3)) :
    σ * τ * σ⁻¹ * τ⁻¹ ∈ alternatingGroup (Fin 3) := by
  have key : ∀ a b : ℤˣ, a * b * a⁻¹ * b⁻¹ = 1 := fun a b => by
    rw [← commutatorElement_def]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm a b)
  rw [Equiv.Perm.mem_alternatingGroup]
  simp only [map_mul, map_inv]
  exact key _ _

private theorem Coord.obar (K : Coord S X) {g : G} (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (h4 : 4 < S.width) {τ : Perm (Fin 3)} {T : S.Mbar} (hT : K.ι T = (τ, 1)) :
    Nat.card (S7.Obar S) = 3 ∧ ∀ x ∈ S.Mbar, x * (T : S.O) * x⁻¹ * (T : S.O)⁻¹ ∈ S7.Obar S := by
  let A : Subgroup (Perm (Fin 3) × (V ≃ₗ[ZMod 2] V)) := (alternatingGroup (Fin 3)).prod ⊥
  let D : Subgroup S.Mbar := A.comap K.ι
  have hDmem : ∀ m, m ∈ D ↔ (K.ι m).1 ∈ alternatingGroup (Fin 3) ∧ (K.ι m).2 = 1 := fun m => by
    simp [D, A, Subgroup.mem_prod]
  have hDn : D.Normal := ⟨fun d hd m => by
    rw [hDmem] at hd ⊢
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv]
      exact (inferInstance : (alternatingGroup (Fin 3)).Normal).conj_mem _ hd.1 _
    · rw [map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, hd.2]
      group⟩
  have hAle : A ≤ K.ι.range := by
    rintro ⟨σ, y⟩ hσy
    rw [Subgroup.mem_prod, mem_bot] at hσy
    obtain ⟨m, hm⟩ := K.surj σ 1 (one_mem X)
    refine ⟨m, ?_⟩
    rw [hm]
    exact Prod.ext rfl hσy.2.symm
  have hDcard : Nat.card D = 3 := by
    have h1 : Nat.card (D.map K.ι) = Nat.card D := Subgroup.card_map_of_injective K.inj
    rw [Subgroup.map_comap_eq_self hAle] at h1
    rw [← h1]
    show Nat.card ((alternatingGroup (Fin 3)).prod ⊥) = 3
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot,
      mul_one, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hDle : D ≤ timmesfeldOddCore S.Mbar := le_sSup ⟨hDn, by rw [hDcard]; decide⟩
  have hdvd := S5.card_oddCore_dvd_three H hNo C h4
  have h3 : 3 ∣ Nat.card (timmesfeldOddCore S.Mbar) := hDcard ▸ Subgroup.card_dvd_of_le hDle
  have hOcard : Nat.card (timmesfeldOddCore S.Mbar) = 3 := Nat.dvd_antisymm hdvd h3
  refine ⟨by rw [S7.card_Obar, hOcard], fun x hx => ?_⟩
  obtain ⟨x', hx'⟩ : ∃ x' : S.Mbar, (x' : S.O) = x := ⟨⟨x, hx⟩, rfl⟩
  have hmemD : x' * T * x'⁻¹ * T⁻¹ ∈ D := by
    rw [hDmem]
    refine ⟨?_, ?_⟩
    · simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, hT]
      exact perm_commutator_mem_alternating _ _
    · simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, hT]
      group
  exact ⟨x' * T * x'⁻¹ * T⁻¹, hDle hmemD, by rw [← hx']; rfl⟩

private theorem Coord.exists_data (K : Coord S X) [Finite V] [FiniteDimensional (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} (hq : q.polarBilin.Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) (hXO : X ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hΩX : CFSG.RankThree.OrthogonalInvolutions.omegaGroup q hq ≤ X)
    (hrank : ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ X → (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 16)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (h4 : 4 < S.width) (hcard : Nat.card (S.Lbar g) = 32) :
    ∃ t : S.O, t ∈ S.Lbar g ∧ t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g ∧ Nbar S g t = zpowers t ∧
      Nat.card (S7.Obar S) = 3 ∧ ∀ x ∈ S.Mbar, x * t * x⁻¹ * t⁻¹ ∈ S7.Obar S := by
  obtain ⟨τ, hτ1, hττ, P, hPX, hPc, hP2, hL⟩ := K.exists_decomp haQ 4
    (fun E hE hE2 => (hrank E hE hE2).trans (by norm_num)) (by rw [hcard]; norm_num)
  have hP1 : P ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hPc
    norm_num at hPc
  obtain ⟨T, hT⟩ := K.surj τ 1 (one_mem X)
  have htL : (T : S.O) ∈ S.Lbar g :=
    (hL T).mpr ⟨by rw [hT]; exact Or.inr rfl, by rw [hT]; exact one_mem P⟩
  have ht1 : (T : S.O) ≠ 1 := fun h => hτ1 (by
    have hT1 : T = 1 := Subtype.ext h
    have := congrArg Prod.fst hT
    rw [hT1, map_one] at this
    exact this.symm)
  have hy : ∃ y ∈ X, ∃ x ∈ P, y * x * y⁻¹ ∉ P := by
    by_contra hcon
    push Not at hcon
    exact hP1 (K.eq_bot_of_normal hPX (fun u hu c hc => hcon u hu c hc) hP2)
  obtain ⟨hO3, hc⟩ := K.obar H hNo C h4 hT
  exact ⟨T, htL, ht1, K.Rbar_ne_Lbar hPX hL hT hy,
    le_antisymm (K.Nbar_le hq h6 hXO hΩX haQ hne hτ1 hττ hPX hP2 hP1 hL hT)
      (zpowers_le.mpr (S6.self_mem_Nbar H htL)), hO3, hc⟩

end Coord

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem timmesfeldOmega_le_isometries {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (q : V → ZMod 2) : timmesfeldOmega q ≤ timmesfeldIsometries q :=
  (Subgroup.closure_le _).mpr fun _ hg => hg.1

private theorem rank_transfer {n : ℕ} (hn : n = 6)
    (hrank : ∀ (q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2)), timmesfeldNondegenerate q →
      ∀ E : Subgroup ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)),
        E ≤ timmesfeldIsometries q → (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 16)
    (q : QuadraticForm (ZMod 2) (Fin n → ZMod 2)) (hq : timmesfeldNondegenerate q)
    (E : Subgroup ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))) (hE : E ≤ timmesfeldIsometries q)
    (hE2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 16 := by
  subst hn
  exact hrank q hq E hE hE2

private theorem exists_s2Data_six_of_coord [IsSimpleGroup G] (I : TimInputs) (O : OrthData S)
    (hw : S.width = 6)
    {X : Subgroup ((Fin S.width → ZMod 2) ≃ₗ[ZMod 2] (Fin S.width → ZMod 2))}
    (hXI : X ≤ timmesfeldIsometries O.q) (hΩX : timmesfeldOmega O.q ≤ X) (K : Coord S X)
    (hrank : ∀ E : Subgroup ((Fin S.width → ZMod 2) ≃ₗ[ZMod 2] (Fin S.width → ZMod 2)),
      E ≤ timmesfeldIsometries O.q → (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 16) :
    Nonempty (S2Data S) := by
  obtain ⟨g, haQ, hne⟩ := O.exists_conj_mem_Q I.hAS (by omega)
  have hirr := O.not_isReducible I.hDW (by omega) haQ hne
  have hnoAll := O.noA2All I (by omega)
  have hno := hnoAll g haQ hne
  have H := S14.hyp4_of I.hTI (by omega) haQ hne hno hirr
  have C := S14.cons311_of I.hTI (by omega) haQ hne hno hirr
  have hNo : NoA2 S g := S14.noA2_of hno
  have hcard : Nat.card (S.Lbar g) = 32 := by
    rw [C.card_Lbar, hw]
    norm_num
  have hq := O.polarBilin_nondegenerate
  have hfin : finrank (ZMod 2) (Fin S.width → ZMod 2) = 6 := by
    rw [Module.finrank_fin_fun]
    exact hw
  have hXO : X ≤ TauCeti.QuadraticMap.orthogonalGroup O.q := by
    rw [← S7.timmesfeldIsometries_eq]
    exact hXI
  have hΩX' : CFSG.RankThree.OrthogonalInvolutions.omegaGroup O.q hq ≤ X := by
    rw [← S7.timmesfeldOmega_eq O.q hq]
    exact hΩX
  obtain ⟨t, ht, ht1, hR, hN, hO3, hc⟩ := K.exists_data hq (by omega) hXO hΩX'
    (fun E hE => hrank E (hE.trans hXI)) haQ hne H hNo C (by omega) hcard
  obtain ⟨hVQ, hΩ, hwV, -⟩ := S7.timmesfeld_7_6 I.hCE H hNo C ht ht1 hR hN (by omega)
  have hG : GoodT S g t := ⟨⟨H, hNo, C, ht, ht1, hR, hVQ, hN, hirr, hnoAll⟩, hΩ⟩
  exact exists_s2Data_of_obar hG (by omega) hwV hO3 hc

theorem exists_s2Data_six [IsSimpleGroup G] (I : TimInputs) (O : OrthData S) (hw : S.width = 6)
    (hrank : ∀ (q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2)),
      CFSG.Open.timmesfeldNondegenerate q →
      ∀ E : Subgroup ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)),
        E ≤ CFSG.Open.timmesfeldIsometries q → (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 16) :
    Nonempty (S2Data S) := by
  have hrank' : ∀ E : Subgroup ((Fin S.width → ZMod 2) ≃ₗ[ZMod 2] (Fin S.width → ZMod 2)),
      E ≤ timmesfeldIsometries O.q → (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 16 :=
    fun E hE hE2 => rank_transfer hw hrank O.q O.nondeg E hE hE2
  rcases O.iso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact exists_s2Data_six_of_coord I O hw (timmesfeldOmega_le_isometries _) le_rfl
      (Coord.ofEquiv e) hrank'
  · exact exists_s2Data_six_of_coord I O hw le_rfl (timmesfeldOmega_le_isometries _)
      (Coord.ofEquiv e) hrank'

end CFSG.GF2Type.Smith1980Orth

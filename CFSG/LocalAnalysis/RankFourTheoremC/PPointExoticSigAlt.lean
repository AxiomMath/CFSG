module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticDefs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Equiv Subgroup

namespace SigAlt

theorem dvd_card_of_orbit_ncard {H Ω : Type*} [Group H] [MulAction H Ω] [Fintype Ω]
    [DecidableEq Ω] {S : Finset Ω} {n : ℕ} (hS : ∀ (h : H) (x : Ω), x ∈ S → h • x ∈ S)
    (hn : ∀ x ∈ S, (MulAction.orbit H x).ncard = n) : n ∣ S.card := by
  classical
  let q : Ω → MulAction.orbitRel.Quotient H Ω := Quotient.mk''
  rw [Finset.card_eq_sum_card_fiberwise (f := q) (t := S.image q)
    (fun x hx => Finset.mem_image_of_mem q hx)]
  refine Finset.dvd_sum fun c hc => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
  have hfib : S.filter (fun a => q a = q x) = (MulAction.orbit H x).toFinset := by
    ext a
    simp only [Finset.mem_filter, Set.mem_toFinset]
    constructor
    · rintro ⟨-, ha⟩
      exact MulAction.orbitRel_apply.1 (Quotient.exact' ha)
    · intro ha
      refine ⟨?_, Quotient.sound' (MulAction.orbitRel_apply.2 ha)⟩
      obtain ⟨h, rfl⟩ := ha
      exact hS h x hx
  rw [hfib, ← Set.ncard_eq_toFinset_card', hn x hx]

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_moved_of_card (hΩ : Fintype.card Ω = 10) {B : Subgroup (Perm Ω)}
    (hB : Nat.card B = 25) (ω : Ω) : ∃ β ∈ B, β ω ≠ ω := by
  by_contra hfix
  push Not at hfix
  have hle : B ≤ MulAction.stabilizer (Perm Ω) ω := fun β hβ =>
    MulAction.mem_stabilizer_iff.2 (hfix β hβ)
  have h1 := Subgroup.card_dvd_of_le hle
  have h2 := Subgroup.index_mul_card (MulAction.stabilizer (Perm Ω) ω)
  rw [MulAction.index_stabilizer_of_transitive, Nat.card_perm] at h2
  have hΩ' : Nat.card Ω = 10 := by rw [Nat.card_eq_fintype_card, hΩ]
  rw [hΩ'] at h2
  rw [hB] at h1
  have h3 : Nat.card (MulAction.stabilizer (Perm Ω) ω) = 362880 := by
    have : Nat.factorial 10 = 3628800 := by decide
    omega
  rw [h3] at h1
  norm_num at h1

theorem ncard_orbit_five (hΩ : Fintype.card Ω = 10) {B : Subgroup (Perm Ω)}
    (hB : Nat.card B = 25) (ω : Ω) : (MulAction.orbit B ω).ncard = 5 := by
  have h1 := Subgroup.index_mul_card (MulAction.stabilizer B ω)
  rw [MulAction.index_stabilizer, hB] at h1
  have h2 : (MulAction.orbit B ω).ncard ≤ 10 := by
    have := Set.ncard_le_card (MulAction.orbit B ω)
    rwa [Nat.card_eq_fintype_card, hΩ] at this
  have h3 : (MulAction.orbit B ω).ncard ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h
    obtain ⟨β, hβ, hne⟩ := exists_moved_of_card hΩ hB ω
    have h4 : ((⟨β, hβ⟩ : B) • ω) ∈ MulAction.orbit B ω := MulAction.mem_orbit ω _
    have h5 : ω ∈ MulAction.orbit B ω := MulAction.mem_orbit_self ω
    rw [ha, Set.mem_singleton_iff] at h4 h5
    exact hne (h4.trans h5.symm)
  generalize (MulAction.orbit B ω).ncard = o at *
  generalize Nat.card (MulAction.stabilizer B ω) = s at *
  interval_cases o <;> omega

theorem exists_ne_one_fixing (hΩ : Fintype.card Ω = 10) {B : Subgroup (Perm Ω)}
    (hB : Nat.card B = 25) (a : Ω) : ∃ β ∈ B, β ≠ 1 ∧ β a = a := by
  have h1 := Subgroup.index_mul_card (MulAction.stabilizer B a)
  rw [MulAction.index_stabilizer, ncard_orbit_five hΩ hB a, hB] at h1
  have h5 : Nat.card (MulAction.stabilizer B a) = 5 := by omega
  have hne : MulAction.stabilizer B a ≠ ⊥ := by
    intro h
    rw [h] at h5
    simp at h5
  obtain ⟨⟨β, hβ⟩, hβ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  exact ⟨β, β.2, fun h => hβ1 (Subtype.ext (Subtype.ext h)), MulAction.mem_stabilizer_iff.1 hβ⟩

theorem five_dvd_card_of_stable (hΩ : Fintype.card Ω = 10) {B : Subgroup (Perm Ω)}
    (hB : Nat.card B = 25) {S : Finset Ω} (hS : ∀ β ∈ B, ∀ x ∈ S, β x ∈ S) : 5 ∣ S.card :=
  dvd_card_of_orbit_ncard (H := B) (fun h x hx => hS h h.2 x hx)
    (fun x _ => ncard_orbit_five hΩ hB x)

theorem orbit_apply_eq_image {Y : Subgroup (Perm Ω)} {β : Perm Ω}
    (hβ : β ∈ normalizer (Y : Set (Perm Ω))) (ω : Ω) :
    MulAction.orbit Y (β ω) = β '' MulAction.orbit Y ω := by
  have h1 := Subgroup.mem_set_normalizer_iff''.1 hβ
  have h2 := Subgroup.mem_set_normalizer_iff.1 hβ
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    refine ⟨(β⁻¹ * y * β) ω, ⟨⟨β⁻¹ * y * β, (h1 y).1 hy⟩, rfl⟩, ?_⟩
    simp [Perm.mul_apply]
  · rintro ⟨u, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    refine ⟨⟨β * y * β⁻¹, (h2 y).1 hy⟩, ?_⟩
    simp [Perm.mul_apply]

theorem apply_eq_of_orbit_two {Y : Subgroup (Perm Ω)} {β : Perm Ω}
    (himg : ∀ ω, MulAction.orbit Y (β ω) = β '' MulAction.orbit Y ω) {x : Ω}
    (h2 : (MulAction.orbit Y x).ncard = 2) (hx : β x = x) {y : Perm Ω} (hy : y ∈ Y) :
    β (y x) = y x := by
  by_cases hyx : y x = x
  · rw [hyx, hx]
  have himg_x : β '' MulAction.orbit Y x = MulAction.orbit Y x := by rw [← himg, hx]
  have hu : y x ∈ MulAction.orbit Y x := ⟨⟨y, hy⟩, rfl⟩
  have hv : β (y x) ∈ MulAction.orbit Y x := by
    rw [← himg_x]
    exact ⟨_, hu, rfl⟩
  have hvx : β (y x) ≠ x := fun h => hyx (β.injective (h.trans hx.symm))
  have hcard : (MulAction.orbit Y x \ {x}).ncard = 1 := by
    rw [Set.ncard_diff_singleton_of_mem (MulAction.mem_orbit_self x), h2]
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hcard
  have e1 : y x ∈ MulAction.orbit Y x \ {x} := ⟨hu, hyx⟩
  have e2 : β (y x) ∈ MulAction.orbit Y x \ {x} := ⟨hv, hvx⟩
  rw [ha, Set.mem_singleton_iff] at e1 e2
  exact e2.trans e1.symm

theorem eq_bot_of_card_ten (hΩ : Fintype.card Ω = 10) {B Y : Subgroup (Perm Ω)}
    (hB : Nat.card B = 25) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hY : Nat.Coprime 5 (Nat.card Y)) (hBY : B ≤ normalizer (Y : Set (Perm Ω))) : Y = ⊥ := by
  classical
  by_contra hne
  obtain ⟨⟨y₀, hy₀⟩, hy₁⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hy₀1 : y₀ ≠ 1 := fun h => hy₁ (Subtype.ext h)
  obtain ⟨ω₀, hω₀⟩ : ∃ ω, y₀ ω ≠ ω := by
    by_contra h
    push Not at h
    exact hy₀1 (Equiv.ext h)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Ω → ℕ, ∀ ω, ρ ω = (MulAction.orbit Y ω).ncard :=
    ⟨fun ω => (MulAction.orbit Y ω).ncard, fun _ => rfl⟩
  have hρ_dvd : ∀ ω, ρ ω ∣ Nat.card Y := fun ω => by
    have h1 := Subgroup.index_mul_card (MulAction.stabilizer Y ω)
    rw [MulAction.index_stabilizer] at h1
    rw [hρ]
    exact Dvd.intro _ h1
  have hρ_B : ∀ β ∈ B, ∀ ω, ρ (β ω) = ρ ω := fun β hβ ω => by
    rw [hρ, hρ, orbit_apply_eq_image (hBY hβ), Set.ncard_image_of_injective _ β.injective]
  have hρ_Y : ∀ y ∈ Y, ∀ ω, ρ (y ω) = ρ ω := fun y hy ω => by
    rw [hρ, hρ]
    exact congrArg Set.ncard (MulAction.orbit_smul (⟨y, hy⟩ : Y) ω)
  obtain ⟨m, hm⟩ : ∃ m, m = ρ ω₀ := ⟨_, rfl⟩
  have hm2 : 2 ≤ m := by
    have : 1 < (MulAction.orbit Y ω₀).ncard :=
      (Set.one_lt_ncard_iff).2 ⟨ω₀, y₀ ω₀, MulAction.mem_orbit_self ω₀,
        ⟨⟨y₀, hy₀⟩, rfl⟩, fun h => hω₀ h.symm⟩
    rw [hm, hρ]
    exact this
  obtain ⟨S, hmem⟩ : ∃ S : Finset Ω, ∀ ω, ω ∈ S ↔ ρ ω = m :=
    ⟨Finset.univ.filter (fun ω => ρ ω = m), fun ω => by simp⟩
  have h5 : 5 ∣ S.card := five_dvd_card_of_stable hΩ hB fun β hβ x hx => by
    rw [hmem] at hx ⊢
    rw [hρ_B β hβ, hx]
  have hmS : m ∣ S.card :=
    dvd_card_of_orbit_ncard (H := Y)
      (fun h x hx => by
        rw [hmem] at hx ⊢
        exact (hρ_Y h h.2 x).trans hx)
      (fun x hx => (hρ x).symm.trans ((hmem x).1 hx))
  have hcop : Nat.Coprime 5 m := hY.coprime_dvd_right (hm ▸ hρ_dvd ω₀)
  have h5m : 5 * m ∣ S.card := hcop.mul_dvd_of_dvd_of_dvd h5 hmS
  have hSpos : 0 < S.card := Finset.card_pos.2 ⟨ω₀, (hmem ω₀).2 hm.symm⟩
  have hSle : S.card ≤ 10 := hΩ ▸ Finset.card_le_univ S
  have hm_eq : m = 2 := by
    have := Nat.le_of_dvd hSpos h5m
    omega
  have h10 : 10 ∣ S.card := by
    have : 5 * m = 10 := by omega
    rwa [this] at h5m
  have hSuniv : S = Finset.univ := by
    refine Finset.eq_univ_of_card S ?_
    have := Nat.le_of_dvd hSpos h10
    omega
  have hρ2 : ∀ ω, (MulAction.orbit Y ω).ncard = 2 := fun ω => by
    have := (hmem ω).1 (hSuniv ▸ Finset.mem_univ ω)
    rw [← hρ, this, hm_eq]
  obtain ⟨β, hβB, hβ1, hβa⟩ := exists_ne_one_fixing hΩ hB ω₀
  obtain ⟨T, hTmem⟩ : ∃ T : Finset Ω, ∀ x, x ∈ T ↔ β x = x :=
    ⟨Finset.univ.filter (fun x => β x = x), fun x => by simp⟩
  have hT5 : 5 ∣ T.card := five_dvd_card_of_stable hΩ hB fun γ hγ x hx => by
    rw [hTmem] at hx ⊢
    have hc := hBc β hβB γ hγ
    calc β (γ x) = (β * γ) x := rfl
      _ = (γ * β) x := by rw [hc]
      _ = γ x := by rw [Perm.mul_apply, hx]
  have himg : ∀ ω, MulAction.orbit Y (β ω) = β '' MulAction.orbit Y ω :=
    orbit_apply_eq_image (hBY hβB)
  have hT2 : 2 ∣ T.card :=
    dvd_card_of_orbit_ncard (H := Y)
      (fun h x hx => by
        rw [hTmem] at hx ⊢
        exact apply_eq_of_orbit_two himg (hρ2 x) hx h.2)
      (fun x _ => hρ2 x)
  have hTpos : 0 < T.card := Finset.card_pos.2 ⟨ω₀, (hTmem ω₀).2 hβa⟩
  have hTle : T.card ≤ 10 := hΩ ▸ Finset.card_le_univ T
  have hT10 : 10 ∣ T.card :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 2) hT5 hT2
  have hTuniv : T = Finset.univ := by
    refine Finset.eq_univ_of_card T ?_
    have := Nat.le_of_dvd hTpos hT10
    omega
  refine hβ1 (Equiv.ext fun x => ?_)
  exact (hTmem x).1 (hTuniv ▸ Finset.mem_univ x)

end SigAlt

theorem signalizerAutAt_alt {p : ℕ} (h : 5 ≤ 2 * p) (hp : p = 5) :
    SignalizerAutAt p (.alternating (2 * p) h) := by
  subst hp
  intro K _ _ hK B Y hB hBc hY hBY _
  obtain ⟨e⟩ := hK
  have e' : K ≃* alternatingGroup (Fin (2 * 5)) := e
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj (2 * 5)
    (by norm_num) (by norm_num)
  let Λ : MulAut K ≃* Perm (Fin (2 * 5)) :=
    (MulAut.congr e').trans
      (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin (2 * 5)))) hbij).symm
  have hΛ : Function.Injective Λ.toMonoidHom := Λ.injective
  have hmem : ∀ (L : Subgroup (MulAut K)) (x : MulAut K), Λ x ∈ L.map Λ.toMonoidHom ↔ x ∈ L :=
    fun L x => Subgroup.mem_map_iff_mem hΛ
  have hY1 : Y = ⊥ := by
    refine (Subgroup.map_eq_bot_iff_of_injective Y (f := Λ.toMonoidHom) Λ.injective).1 ?_
    refine SigAlt.eq_bot_of_card_ten (Ω := Fin (2 * 5)) (by simp) (B := B.map Λ.toMonoidHom)
      ?_ ?_ ?_ ?_
    · rw [Subgroup.card_map_of_injective Λ.injective, hBc]
      norm_num
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have := congrArg Subtype.val (isMulCommutative_iff.1 hB.1 ⟨a, ha⟩ ⟨b, hb⟩)
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
      exact congrArg Λ this
    · rwa [Subgroup.card_map_of_injective Λ.injective]
    · rintro _ ⟨b, hb, rfl⟩
      refine Subgroup.mem_set_normalizer_iff.2 fun n => ?_
      obtain ⟨m, rfl⟩ := Λ.surjective n
      have h1 := Subgroup.mem_set_normalizer_iff.1 (hBY hb) m
      have e : Λ.toMonoidHom b * Λ m * (Λ.toMonoidHom b)⁻¹ = Λ (b * m * b⁻¹) := by simp
      rw [SetLike.mem_coe, SetLike.mem_coe, e, hmem, hmem]
      exact h1
  intro b _
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  rw [hY1] at hy
  rw [Subgroup.mem_bot.1 hy, one_mul, mul_one]

end CFSG.LocalAnalysis.RankFourTheoremC

module

public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremB.InputPiGenProof

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Equiv Equiv.Perm MulAction CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator GL83 GL83.CompFam
open scoped commutatorElement

section AltDiv

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {p : ℕ} [Fact p.Prime]

theorem i271h_comm_of_mem_elemAbelian {A : Subgroup (Perm Ω)} (hA : IsElemAbelian p A) {a b : Perm Ω}
    (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have := hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem i271h_isPGroup_of_elemAbelian {A : Subgroup (Perm Ω)} (hel : IsElemAbelian p A) :
    IsPGroup p A := fun g => ⟨1, by
  rw [pow_one]; exact Subtype.ext (by simpa using hel.2 g g.2)⟩

theorem i271h_perm_orbit_translation_mem {A : Subgroup (Perm Ω)}
    (hA : IsSCp p (⊤ : Subgroup (Perm Ω)) A) {δ ω : Ω}
    (hω : ∀ a ∈ A, a δ ≠ ω) (hstab : ∀ a ∈ A, a δ = δ → a ω = ω) : ∀ t ∈ A, t ω = ω := by
  classical
  obtain ⟨-, hel, hmax⟩ := hA
  intro t ht
  set O : Set Ω := {x | ∃ a ∈ A, a δ = x} with hOdef
  have hO : ∀ s ∈ A, ∀ x, s x ∈ O ↔ x ∈ O := by
    intro s hs x
    constructor
    · rintro ⟨a, ha, hax⟩
      refine ⟨s⁻¹ * a, A.mul_mem (A.inv_mem hs) ha, ?_⟩
      show s⁻¹ (a δ) = x
      rw [hax]; simp
    · rintro ⟨a, ha, rfl⟩
      exact ⟨s * a, A.mul_mem hs ha, rfl⟩
  have hωO : ω ∉ O := fun ⟨a, ha, h⟩ => hω a ha h
  let z : Perm Ω := Equiv.Perm.ofSubtype (t.subtypePerm (hO t ht) : Perm {x // x ∈ O})
  have hz1 : ∀ x ∈ O, z x = t x := fun x hx => Equiv.Perm.ofSubtype_apply_of_mem _ hx
  have hz2 : ∀ x, x ∉ O → z x = x := fun x hx => Equiv.Perm.ofSubtype_apply_of_not_mem _ hx
  have hzp : z ^ p = 1 := by
    have h1 : z ^ p = Equiv.Perm.ofSubtype
        ((t.subtypePerm (hO t ht) : Perm {x // x ∈ O}) ^ p) := (map_pow _ _ _).symm
    have h2 : ((t.subtypePerm (hO t ht) : Perm {x // x ∈ O}) ^ p) = 1 := by
      rw [Equiv.Perm.subtypePerm_pow]
      ext x
      have ht' : t ^ p = 1 := hel.2 t ht
      simp [ht']
    rw [h1, h2, map_one]
  have hcomm : ∀ a ∈ A, a * z = z * a := by
    intro a ha
    ext x
    by_cases hx : x ∈ O
    · have hax : a x ∈ O := (hO a ha x).2 hx
      simp only [Perm.mul_apply]
      rw [hz1 x hx, hz1 (a x) hax]
      have := i271h_comm_of_mem_elemAbelian hel ha ht
      exact (congrArg (fun f : Perm Ω => f x) this)
    · have hax : a x ∉ O := fun h => hx ((hO a ha x).1 h)
      simp only [Perm.mul_apply]
      rw [hz2 x hx, hz2 (a x) hax]
  have hE : IsElemAbelian p (A ⊔ Subgroup.zpowers z) :=
    GL83.PiGen.isElemAbelian_sup hel (GL83.PiGen.isElemAbelian_zpowers hzp)
      (fun a ha k hk => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        exact ((Commute.zpow_right (hcomm a ha) n)).eq)
  have hEA : A ⊔ Subgroup.zpowers z = A := hmax _ le_top hE le_sup_left
  have hzA : z ∈ A := by
    have : z ∈ A ⊔ Subgroup.zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    rwa [hEA] at this
  have hδO : δ ∈ O := ⟨1, A.one_mem, rfl⟩
  have h3 : (t⁻¹ * z) δ = δ := by
    simp only [Perm.mul_apply]
    rw [hz1 δ hδO]; simp
  have h4 := hstab (t⁻¹ * z) (A.mul_mem (A.inv_mem ht) hzA) h3
  simp only [Perm.mul_apply] at h4
  rw [hz2 ω hωO] at h4
  have h5 : t (t⁻¹ ω) = t ω := by rw [h4]
  simpa using h5.symm

theorem i271h_perm_no_fixed_point {A : Subgroup (Perm Ω)} (hA : IsSCp p (⊤ : Subgroup (Perm Ω)) A)
    (hp : p ∣ Fintype.card Ω) (ω : Ω) : ∃ a ∈ A, a ω ≠ ω := by
  classical
  by_contra hfix
  push Not at hfix
  obtain ⟨-, hel, hmax⟩ := hA
  have hpg : IsPGroup p A := i271h_isPGroup_of_elemAbelian hel
  have hmod := hpg.card_modEq_card_fixedPoints Ω
  set Fx : Set Ω := MulAction.fixedPoints A Ω with hFx
  have hmem : ∀ x, x ∈ Fx ↔ ∀ a ∈ A, a x = x := by
    intro x
    rw [hFx, MulAction.mem_fixedPoints]
    constructor
    · intro h a ha
      exact h ⟨a, ha⟩
    · intro h a
      exact h a a.2
  have hωF : ω ∈ Fx := (hmem ω).2 hfix
  have hdvd : p ∣ Nat.card Fx := by
    have h1 : Nat.card Ω ≡ 0 [MOD p] := by
      rw [Nat.card_eq_fintype_card]
      exact (Nat.modEq_zero_iff_dvd).2 hp
    exact (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans h1)
  have hpos : 0 < Nat.card Fx := by
    haveI : Nonempty Fx := ⟨⟨ω, hωF⟩⟩
    exact Nat.card_pos
  have hple : p ≤ Nat.card Fx := Nat.le_of_dvd hpos hdvd
  have hS : ∃ S : Finset Ω, (∀ x ∈ S, x ∈ Fx) ∧ S.card = p := by
    have hcardF : Fx.toFinset.card = Nat.card Fx := by
      rw [Nat.card_eq_fintype_card, Set.toFinset_card]
    obtain ⟨S, hSF, hSc⟩ := Finset.exists_subset_card_eq (hcardF ▸ hple : p ≤ Fx.toFinset.card)
    exact ⟨S, fun x hx => by simpa using hSF hx, hSc⟩
  obtain ⟨S, hSF, hSc⟩ := hS
  have hdvdS : p ∣ Fintype.card (Perm {x // x ∈ S}) := by
    rw [Fintype.card_perm, Fintype.card_coe, hSc]
    exact Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card p hdvdS
  let ĉ : Perm Ω := Equiv.Perm.ofSubtype c
  have hĉ1 : ∀ x (hx : x ∈ S), ĉ x = (c ⟨x, hx⟩ : Ω) := fun x hx =>
    Equiv.Perm.ofSubtype_apply_of_mem c hx
  have hĉ2 : ∀ x, x ∉ S → ĉ x = x := fun x hx => Equiv.Perm.ofSubtype_apply_of_not_mem c hx
  have hĉp : ĉ ^ p = 1 := by
    have : ĉ ^ p = Equiv.Perm.ofSubtype (c ^ p) := (map_pow _ _ _).symm
    rw [this, ← hc, pow_orderOf_eq_one, map_one]
  have hĉS : ∀ x, x ∈ S → ĉ x ∈ S := by
    intro x hx
    rw [hĉ1 x hx]
    exact (c ⟨x, hx⟩).2
  have hcomm : ∀ a ∈ A, a * ĉ = ĉ * a := by
    intro a ha
    ext x
    simp only [Perm.mul_apply]
    by_cases hx : x ∈ S
    · have hax : a x = x := (hmem x).1 (hSF x hx) a ha
      have hcx : a (ĉ x) = ĉ x := (hmem (ĉ x)).1 (hSF _ (hĉS x hx)) a ha
      rw [hax, hcx]
    · have hax : a x ∉ S := by
        intro h
        have h1 : a (a x) = a x := (hmem (a x)).1 (hSF _ h) a ha
        have h2 : a x = x := a.injective h1
        exact hx (h2 ▸ h)
      rw [hĉ2 x hx, hĉ2 (a x) hax]
  have hE : IsElemAbelian p (A ⊔ Subgroup.zpowers ĉ) :=
    GL83.PiGen.isElemAbelian_sup hel (GL83.PiGen.isElemAbelian_zpowers hĉp)
      (fun a ha k hk => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        exact ((Commute.zpow_right (hcomm a ha) n)).eq)
  have hEA : A ⊔ Subgroup.zpowers ĉ = A := hmax _ le_top hE le_sup_left
  have hĉA : ĉ ∈ A := by
    have : ĉ ∈ A ⊔ Subgroup.zpowers ĉ := Subgroup.mem_sup_right (Subgroup.mem_zpowers ĉ)
    rwa [hEA] at this
  have hc1 : c = 1 := by
    ext ⟨x, hx⟩
    have h1 : ĉ x = x := (hmem x).1 (hSF x hx) ĉ hĉA
    rw [hĉ1 x hx] at h1
    simp [h1]
  rw [hc1, orderOf_one] at hc
  exact (Fact.out : p.Prime).one_lt.ne hc


theorem i271h_perm_coprime_normalized_eq_bot {A T : Subgroup (Perm Ω)}
    (hA : IsSCp p (⊤ : Subgroup (Perm Ω)) A) (hp : p ∣ Fintype.card Ω)
    (hT : Nat.Coprime p (Nat.card T)) (hAT : A ≤ Subgroup.normalizer (T : Set (Perm Ω))) :
    T = ⊥ := by
  classical
  have hel : IsElemAbelian p A := hA.2.1
  have hconj : ∀ a ∈ A, ∀ t ∈ T, a * t * a⁻¹ ∈ T := fun a ha t ht =>
    (Subgroup.mem_normalizer_iff.1 (hAT ha) t).1 ht
  have hconj' : ∀ a ∈ A, ∀ t ∈ T, a⁻¹ * t * a ∈ T := fun a ha t ht => by
    simpa using hconj a⁻¹ (A.inv_mem ha) t ht
  suffices h : ∀ ω, ∀ t ∈ T, t ω = ω by
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    ext ω
    exact h ω t ht
  intro ω
  set Δ : Set Ω := {x | ∃ t ∈ T, t ω = x} with hΔ
  have hωΔ : ω ∈ Δ := ⟨1, T.one_mem, rfl⟩
  have hK1 : ∀ a ∈ A, ∀ t ∈ T, ∃ t' ∈ T, a (t ω) = t' (a ω) := by
    intro a ha t ht
    refine ⟨a * t * a⁻¹, hconj a ha t ht, ?_⟩
    simp [Perm.mul_apply]
  let D : Subgroup (Perm Ω) :=
    { carrier := {a | a ∈ A ∧ a ω ∈ Δ}
      mul_mem' := by
        rintro a b ⟨ha, ⟨u, hu, hau⟩⟩ ⟨hb, ⟨s, hs, hbs⟩⟩
        refine ⟨A.mul_mem ha hb, ?_⟩
        obtain ⟨s', hs', hs'e⟩ := hK1 a ha s hs
        refine ⟨s' * u, T.mul_mem hs' hu, ?_⟩
        simp only [Perm.mul_apply]
        rw [← hbs, hs'e, ← hau]
      one_mem' := ⟨A.one_mem, by simpa using hωΔ⟩
      inv_mem' := by
        rintro a ⟨ha, ⟨u, hu, hau⟩⟩
        refine ⟨A.inv_mem ha, ⟨a⁻¹ * u⁻¹ * a, hconj' a ha _ (T.inv_mem hu), ?_⟩⟩
        simp only [Perm.mul_apply]
        have : u⁻¹ (a ω) = ω := by rw [← hau]; simp
        rw [this] }
  have hDA : ∀ d ∈ D, d ∈ A := fun d hd => hd.1
  have hDΔ : ∀ d ∈ D, ∀ x ∈ Δ, d x ∈ Δ := by
    rintro d ⟨hd, ⟨u, hu, hdu⟩⟩ x ⟨t, ht, rfl⟩
    obtain ⟨t', ht', he⟩ := hK1 d hd t ht
    exact ⟨t' * u, T.mul_mem ht' hu, by simp only [Perm.mul_apply]; rw [hdu, he]⟩
  have hDfix : ∃ ω' ∈ Δ, ∀ d ∈ D, d ω' = ω' := by
    letI : MulAction D Δ :=
      { smul := fun d x => ⟨(d : Perm Ω) x.1, hDΔ d d.2 x.1 x.2⟩
        one_smul := fun x => Subtype.ext rfl
        mul_smul := fun d e x => Subtype.ext rfl }
    have hpgD : IsPGroup p D := fun g => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa using hel.2 g (hDA g g.2))⟩
    have hmod := hpgD.card_modEq_card_fixedPoints Δ
    have hcop : ¬ p ∣ Nat.card Δ := by
      intro hd
      have hor : (MulAction.orbit T ω) = Δ := by
        ext x
        simp only [MulAction.mem_orbit_iff, hΔ, Set.mem_setOf_eq]
        constructor
        · rintro ⟨g, rfl⟩; exact ⟨g, g.2, rfl⟩
        · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩
      have h1 : Nat.card Δ ∣ Nat.card T := by
        have e1 : (MulAction.stabilizer T ω).index = (MulAction.orbit T ω).ncard :=
          MulAction.index_stabilizer T ω
        have e2 : Nat.card Δ = (MulAction.orbit T ω).ncard := by
          rw [hor]; exact Nat.card_coe_set_eq Δ
        rw [e2, ← e1]
        exact Subgroup.index_dvd_card _
      exact (Fact.out : p.Prime).one_lt.ne' (hT.eq_one_of_dvd (hd.trans h1))
    by_contra hno
    push Not at hno
    haveI : IsEmpty (MulAction.fixedPoints D Δ) := ⟨fun ⟨x, hx⟩ => by
      obtain ⟨d, hd, hne⟩ := hno x.1 x.2
      have := MulAction.mem_fixedPoints.1 hx ⟨d, hd⟩
      exact hne (congrArg Subtype.val this)⟩
    have h0 : Nat.card (MulAction.fixedPoints D Δ) = 0 := Nat.card_of_isEmpty
    exact hcop ((Nat.modEq_zero_iff_dvd).1 (hmod.trans (by rw [h0])))
  obtain ⟨ω', hω'Δ, hω'fix⟩ := hDfix
  have hK5 : ∀ δ ∈ Δ, ∀ a ∈ A, a δ = δ → a ω' = ω' := by
    rintro δ ⟨t, ht, rfl⟩ a ha hat
    obtain ⟨t', ht', he⟩ := hK1 a ha t ht
    have h1 : t ω = t' (a ω) := by rw [← hat, he]
    have haΔ : a ω ∈ Δ := ⟨t'⁻¹ * t, T.mul_mem (T.inv_mem ht') ht, by
      simp only [Perm.mul_apply]; rw [h1]; simp⟩
    exact hω'fix a ⟨ha, haΔ⟩
  have hall : ∀ δ ∈ Δ, δ = ω' := by
    intro δ hδ
    have hex : ∃ a ∈ A, a δ = ω' := by
      by_contra hno
      push Not at hno
      have := i271h_perm_orbit_translation_mem hA (δ := δ) (ω := ω') (fun a ha => hno a ha) (hK5 δ hδ)
      obtain ⟨a, ha, hne⟩ := i271h_perm_no_fixed_point hA hp ω'
      exact hne (this a ha)
    obtain ⟨a, ha, haδ⟩ := hex
    obtain ⟨t₁, ht₁, rfl⟩ := hδ
    obtain ⟨t₂, ht₂, ht₂e⟩ := hω'Δ
    obtain ⟨t₁', ht₁', he⟩ := hK1 a ha t₁ ht₁
    have haω : a ω ∈ Δ := ⟨t₁'⁻¹ * t₂, T.mul_mem (T.inv_mem ht₁') ht₂, by
      simp only [Perm.mul_apply]; rw [ht₂e, ← haδ, he]; simp⟩
    have haD : a ω' = ω' := hω'fix a ⟨ha, haω⟩
    exact a.injective (haδ.trans haD.symm)
  intro t ht
  exact (hall (t ω) ⟨t, ht, rfl⟩).trans (hall ω hωΔ).symm

end AltDiv

section Bridge

variable {X : Type} [Group X] [Finite X]

open GL83.PiGen in
theorem i271h_permHom_apply_of_mem_K {K A : Subgroup X} (hA : A ≤ Subgroup.normalizer (K : Set X))
    {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) (a : A) (k : K) (hak : (a : X) = k) :
    permHom hA hn hn6 e a = (e (QuotientGroup.mk k) : Perm (Fin n)) := by
  have hinj : Function.Injective
      (MulAut.conjNormal : Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).1
  apply hinj
  rw [conjNormal_permHom hA hn hn6 e a]
  refine MulEquiv.ext fun z => Subtype.ext ?_
  obtain ⟨x0, rfl⟩ := e.surjective z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x0
  obtain ⟨y, hy, hact⟩ := actHom_mk hA a x
  have hyk : y = k * x * k⁻¹ := Subtype.ext (by rw [hy, hak]; rfl)
  have h1 : (MulAut.congr e (actHom hA a)) (e (QuotientGroup.mk x)) = e (QuotientGroup.mk y) := by
    simp [MulAut.congr_apply, hact]
  rw [h1, hyk, MulAut.conjNormal_apply]
  simp [QuotientGroup.mk_mul, map_mul]

open GL83.PiGen in
theorem i271h_map_permHom_isSCp {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup X}
    [Group.IsPerfect K] (hBsc : IsSCp p ⊤ B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : Subgroup.center K = ⊥) (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    IsSCp p (⊤ : Subgroup (Perm (Fin n)))
      ((B.subgroupOf (Subgroup.normalizer (K : Set X))).map
        (permHom (le_refl (Subgroup.normalizer (K : Set X))) hn hn6 e)) := by
  classical
  have hBel : IsElemAbelian p B := hBsc.2.1
  obtain ⟨π, hπ⟩ : ∃ π : ↥(Subgroup.normalizer (K : Set X)) →* Perm (Fin n),
      π = permHom (le_refl (Subgroup.normalizer (K : Set X))) hn hn6 e := ⟨_, rfl⟩
  rw [← hπ]
  refine ⟨le_top, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map
      (i271_isElemAbelian_subgroupOf (Subgroup.normalizer (K : Set X)) hBel) π
  · intro E _ hE hAE
    refine le_antisymm ?_ hAE
    intro σ hσ
    have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
    have hσp : σ ^ p = 1 := hE.2 σ hσ
    have hsign : Equiv.Perm.sign σ = 1 := by
      have h1 : Equiv.Perm.sign σ ^ p = 1 := by rw [← map_pow, hσp, map_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · exact h
      · rw [h, hodd.neg_one_pow] at h1
        exact absurd h1 (by decide)
    have hσA : σ ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.2 hsign
    obtain ⟨x0, hx0⟩ := e.surjective ⟨σ, hσA⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x0
    have hkσ : (e (QuotientGroup.mk k) : Perm (Fin n)) = σ := congrArg Subtype.val hx0
    have hKN : K ≤ Subgroup.normalizer (K : Set X) := Subgroup.le_normalizer
    have hkp : (k : X) ^ p = 1 := by
      have h1 : e (QuotientGroup.mk (k ^ p)) = 1 := by
        have : (QuotientGroup.mk (k ^ p) : K ⧸ Subgroup.center K) = (QuotientGroup.mk k) ^ p := rfl
        rw [this, map_pow, hx0]
        apply Subtype.ext
        simpa using hσp
      have h2 : (QuotientGroup.mk (k ^ p) : K ⧸ Subgroup.center K) = 1 :=
        (e.map_eq_one_iff).1 h1
      have h3 : k ^ p ∈ Subgroup.center K := (QuotientGroup.eq_one_iff _).1 h2
      rw [hZ, Subgroup.mem_bot] at h3
      exact congrArg Subtype.val h3
    have hcomm : ∀ b ∈ B, b * (k : X) = (k : X) * b := by
      intro b hb
      have hbN : b ∈ Subgroup.normalizer (K : Set X) := hBN hb
      have hπb : π ⟨b, hbN⟩ ∈ E :=
        hAE ⟨⟨b, hbN⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
      obtain ⟨y, hy, hspec⟩ :=
        permHom_spec (le_refl (Subgroup.normalizer (K : Set X))) hn hn6 e ⟨b, hbN⟩ k
      rw [← hπ] at hspec
      have hcom : π ⟨b, hbN⟩ * σ = σ * π ⟨b, hbN⟩ := by
        have := hE.1.is_comm.comm ⟨π ⟨b, hbN⟩, hπb⟩ ⟨σ, hσ⟩
        exact congrArg Subtype.val this
      rw [hkσ, hcom, mul_inv_cancel_right] at hspec
      have hye : e (QuotientGroup.mk y) = e (QuotientGroup.mk k) :=
        Subtype.ext (hspec.symm.trans hkσ.symm)
      have hyk : (QuotientGroup.mk y : K ⧸ Subgroup.center K) = QuotientGroup.mk k :=
        e.injective hye
      have h3 : y⁻¹ * k ∈ Subgroup.center K := QuotientGroup.eq.1 hyk
      rw [hZ, Subgroup.mem_bot] at h3
      have hyk' : y = k := inv_mul_eq_one.1 h3
      subst hyk'
      have hy' : b * (y : X) * b⁻¹ = y := hy.symm
      calc b * (y : X) = b * (y : X) * b⁻¹ * b := by group
        _ = (y : X) * b := by rw [hy']
    have hEl : IsElemAbelian p (B ⊔ Subgroup.zpowers (k : X)) :=
      GL83.PiGen.isElemAbelian_sup hBel (GL83.PiGen.isElemAbelian_zpowers hkp)
        (fun b hb z hz => by
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
          exact (Commute.zpow_right (hcomm b hb) m).eq)
    have hEB : B ⊔ Subgroup.zpowers (k : X) = B := hBsc.2.2 _ le_top hEl le_sup_left
    have hkB : (k : X) ∈ B := by
      have : (k : X) ∈ B ⊔ Subgroup.zpowers (k : X) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      rwa [hEB] at this
    refine ⟨⟨(k : X), hKN k.2⟩, Subgroup.mem_subgroupOf.2 hkB, ?_⟩
    rw [hπ, i271h_permHom_apply_of_mem_K (le_refl _) hn hn6 e ⟨(k : X), hKN k.2⟩ k rfl, hkσ]

end Bridge

section Assembly

variable {X : Type} [Group X] [Finite X]

theorem i271h_center_eq_bot_of_ne_six {K : Type} [Group K] [Finite K]
    [Group.IsPerfect K] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcore : GLAPPrimeCore p K = ⊥)
    (hn : 5 ≤ n) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) (hn6 : n ≠ 6)
    (h73 : ¬ (p = 3 ∧ n = 7)) : Subgroup.center K = ⊥ := by
  by_contra hZ
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  by_cases hp3' : p = 3
  · subst hp3'
    rcases CFSG.AGLEmbedding.eq_six_or_seven_of_center hn e hp hp2 hZ (isPGroup_center hp hcore)
      with h | h
    · exact hn6 h
    · exact h73 ⟨rfl, h⟩
  · have hp5 : 3 < p := by omega
    have hnd := CFSG.RankThree.PartOne.Mult.alternating_center_small_primes hn e hp hp5
    have hZ1 : Nat.card (Subgroup.center K) ≠ 1 := fun h => hZ (Subgroup.eq_bot_of_card_eq _ h)
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hZ1
    exact hnd ((prime_eq_of_dvd_card_center hp hcore hq hqd) ▸ hqd)

open GL83.PiGen in
theorem i271AltDiv_holds : I271AltDiv := by
  intro X _ _ hXK p K B hH hNorm n hn he hpn
  obtain ⟨hBN, hp2⟩ := hNorm
  have hp : p.Prime := hH.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : p ≠ 2 := hH.odd
  have hBel : IsElemAbelian p B := hH.scp.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  obtain ⟨e0⟩ := he
  have e : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n) := e0
  by_cases hn6 : n = 6
  · subst hn6
    have hp3 : p = 3 := by
      have h6 : p ∣ 2 * 3 := hpn
      rcases (Nat.Prime.dvd_mul hp).1 h6 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hpodd
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
    subst hp3
    exact isStronglyBalancedIn_of_autBalanced hBel hq.1 e hp2 i271AutBalanceAltSix_holds
  · have hOK : GLAPPrimeCore p ↥K = ⊥ := i271h_primeCore_eq_bot hH.core hH.comp
    have h73 : ¬ (p = 3 ∧ n = 7) := by
      rintro ⟨rfl, rfl⟩
      omega
    have hZ : Subgroup.center ↥K = ⊥ := i271h_center_eq_bot_of_ne_six hp hpodd hOK hn e hn6 h73
    have hAsc := i271h_map_permHom_isSCp hp hpodd hH.scp hBN hZ hn hn6 e
    set N := Subgroup.normalizer (K : Set X) with hN
    set π := permHom (le_refl N) hn hn6 e with hπ
    have hdvdn : p ∣ Fintype.card (Fin n) := by simpa using hpn
    intro S hSN hcop hBS
    have hBNB : B ⊓ N = B := inf_of_le_left hBN
    rw [hBNB] at hBS
    set T : Subgroup (Perm (Fin n)) := (S.subgroupOf N).map π with hT
    set A : Subgroup (Perm (Fin n)) := (B.subgroupOf N).map π with hA
    have hTcop : Nat.Coprime p (Nat.card T) := by
      have hcard : Nat.card (S.subgroupOf N) = Nat.card S :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
      refine Nat.Coprime.coprime_dvd_right ?_ (hcard ▸ hcop)
      exact Subgroup.card_map_dvd _ _
    have hAT : A ≤ Subgroup.normalizer (T : Set (Perm (Fin n))) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxn : x ∈ Subgroup.normalizer ((S.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        have := Subgroup.mem_normalizer_iff.1 (hBS (Subgroup.mem_subgroupOf.1 hx)) (h : X)
        simpa [Subgroup.mem_subgroupOf] using this
      exact Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hxn)
    have hTbot : T = ⊥ := i271h_perm_coprime_normalized_eq_bot hAsc hdvdn hTcop hAT
    intro s hs
    have hsN : s ∈ N := hSN hs
    have h1 : π ⟨s, hsN⟩ ∈ T := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hs)
    rw [hTbot, Subgroup.mem_bot] at h1
    have h2 := (permHom_eq_one_iff (le_refl N) hn hn6 e ⟨s, hsN⟩).1 h1
    exact Subgroup.mem_centralizer_iff.2 fun x hx => (h2 ⟨x, hx⟩).symm

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator

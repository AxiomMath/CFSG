module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Glue
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Iso
public import CFSG.GH74.Generic.BProg.B3.SolvStab

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup
open CFSG.ComponentClassification.Burgoyne (oddCoreIn)
open scoped MatrixGroups

namespace SolvKG

@[expose] def SL23Type (I : Type) [Group I] : Prop :=
  ∃ π : I →* SL(2, ZMod 3), Function.Surjective π ∧ Odd (Nat.card π.ker)

@[expose] def KGAut (T : Type) [Group T] : Prop :=
  ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
    ∀ t ∈ B, orderOf t = 2 → ∀ (I : Type) [Group I] [Finite I], SL23Type I →
      ∀ ψ : I →* MulAut T, (∀ i, ψ i ∈ B ⊓ centralizer ({t} : Set (MulAut T))) →
        ∀ a : I, (∃ k : ℕ, a ^ (2 ^ k) = 1) → ∀ y ∈ oddCoreIn B t, ψ a * y = y * ψ a

variable {M : Type} [Group M]

theorem commute_of_isCyclic {I : Type} [Group I] (hI : SL23Type I) {Y : Subgroup M}
    (hY : IsCyclic ↥Y) (ψ : I →* M) (hψ : ∀ i, ψ i ∈ normalizer (Y : Set M)) {a : I} {k : ℕ}
    (ha : a ^ (2 ^ k) = 1) : ∀ y ∈ Y, ψ a * y = y * ψ a := by
  obtain ⟨π, hπs, hπo⟩ := hI
  set Nn : Subgroup M := normalizer (Y : Set M) with hNn
  set Y' : Subgroup ↥Nn := Y.subgroupOf Nn with hY'
  have hYle : Y ≤ Nn := Subgroup.le_normalizer
  have : Y'.Normal := Subgroup.normal_in_normalizer
  have hcyc : IsCyclic ↥Y' :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hYle).symm.toMonoidHom
      (MulEquiv.surjective _)
  let φ : I →* MulAut ↥Y' := (MulAut.conjNormal (H := Y')).comp (ψ.codRestrict Nn hψ)
  have hcomm : ∀ a b : MulAut ↥Y', a * b = b * a := fun a b =>
    (IsCyclic.mulAutMulEquiv (G := ↥Y')).injective (by rw [map_mul, map_mul, mul_comm])
  have h1 : φ a = 1 := SolvStab.map_two_element_eq_one π hπs hπo φ hcomm ha
  intro y hy
  set ρ : ↥Y' := ⟨⟨y, hYle hy⟩, Subgroup.mem_subgroupOf.2 hy⟩ with hρ
  have h4 : φ a ρ = ρ := by rw [h1]; rfl
  have h5 := congrArg (fun z : ↥Y' => (((z : ↥Nn)) : M)) h4
  have h6 : ψ a * y * (ψ a)⁻¹ = y := by
    simpa [φ, MulAut.conjNormal_apply, hρ] using h5
  calc ψ a * y = ψ a * y * (ψ a)⁻¹ * ψ a := by group
    _ = y * ψ a := by rw [h6]

theorem mem_normalizer_oddCoreIn {B : Subgroup M} {t g : M}
    (hg : g ∈ B ⊓ centralizer ({t} : Set M)) :
    g ∈ normalizer ((oddCoreIn B t : Subgroup M) : Set M) := by
  rw [mem_normalizer_iff]
  intro y
  have hn : (pPrimeCore 2 ↥(B ⊓ centralizer ({t} : Set M))).Normal := pPrimeCore_normal
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨g, hg⟩ * z * ⟨g, hg⟩⁻¹, hn.conj_mem z hz _, ?_⟩
    simp
  · rintro ⟨z, hz, hzy⟩
    refine ⟨⟨g, hg⟩⁻¹ * z * ⟨g, hg⟩, ?_, ?_⟩
    · have := hn.conj_mem z hz (⟨g, hg⟩⁻¹)
      simpa using this
    · have e : (z : M) = g * y * g⁻¹ := hzy
      change g⁻¹ * (z : M) * g = y
      rw [e]
      group

theorem kgAut_of_oddCoreCyclic {T : Type} [Group T]
    (h : Stage2.Bender.Thm2.P911.OddCoreCyclic T) : KGAut T := by
  intro B hB t htB ht I _ _ hI ψ hψ a ⟨k, hk⟩ y hy
  exact commute_of_isCyclic hI (h B hB t htB ht) ψ (fun i => mem_normalizer_oddCoreIn (hψ i)) hk y hy

theorem kgAut_of_oddCoreIn_eq_bot {T : Type} [Group T]
    (h : ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
      ∀ t ∈ B, orderOf t = 2 → oddCoreIn B t = ⊥) : KGAut T := by
  intro B hB t htB ht I _ _ _ ψ _ a _ y hy
  rw [h B hB t htB ht, Subgroup.mem_bot] at hy
  rw [hy, one_mul, mul_one]

theorem oddCoreIn_eq_bot_of_xform {T : Type} [Group T] [Finite T] (hc : center T = ⊥)
    (hY : ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X) [S.Normal], Nonempty (S ≃* T) →
      centralizer (S : Set X) = ⊥ → ∀ t : X, orderOf t = 2 →
        CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥)
    (B : Subgroup (MulAut T)) (hinn : (MulAut.conj : T →* MulAut T).range ≤ B) (t : MulAut T)
    (htB : t ∈ B) (ht : orderOf t = 2) : oddCoreIn B t = ⊥ := by
  have : ((MulAut.conj : T →* MulAut T).range).Normal := Stage2.Bender.Thm2.P911.conj_range_normal
  let S : Subgroup ↥B := (MulAut.conj : T →* MulAut T).range.subgroupOf B
  have : S.Normal := Subgroup.Normal.subgroupOf inferInstance _
  let e : S ≃* T := (Subgroup.subgroupOfEquivOfLe hinn).trans
    (MonoidHom.ofInjective (Stage2.Bender.Thm2.P911.conj_injective_of_center_eq_bot hc)).symm
  have hC : centralizer (S : Set ↥B) = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    rw [Subgroup.mem_centralizer_iff] at hφ
    refine Subgroup.mem_bot.mpr (Subtype.ext (Stage2.Bender.Thm2.P911.eq_one_of_commute_conj hc
      fun g => ?_))
    have hs' : (⟨MulAut.conj g, hinn ⟨g, rfl⟩⟩ : ↥B) ∈ S := Subgroup.mem_subgroupOf.mpr ⟨g, rfl⟩
    have := hφ _ hs'
    exact (congrArg Subtype.val this).symm
  let t' : ↥B := ⟨t, htB⟩
  have ht' : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  have hodd := hY ↥B S ⟨e⟩ hC t' ht'
  set C : Subgroup ↥B := centralizer ({t'} : Set ↥B) with hCdef
  set P : Subgroup (MulAut T) := oddCoreIn B t with hP
  have hPC : ∀ y ∈ P, y ∈ B ∧ y * t = t * y := by
    rintro _ ⟨z, -, rfl⟩
    exact ⟨(mem_inf.1 z.2).1, mem_centralizer_singleton_iff.1 (mem_inf.1 z.2).2⟩
  set PC : Subgroup ↥C := ((P.subgroupOf B).subgroupOf C) with hPCdef
  have hPCle : P.subgroupOf B ≤ C := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (hPC _ hx).2
  have hnorm : PC.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
    have hgC : ((g : ↥B) : MulAut T) ∈ B ⊓ centralizer ({t} : Set (MulAut T)) := by
      have := g.2
      rw [mem_centralizer_singleton_iff] at this
      refine Subgroup.mem_inf.2 ⟨(g : ↥B).2, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val this
    exact (mem_normalizer_iff.1 (mem_normalizer_oddCoreIn hgC) _).1 hn
  have hcardP : Odd (Nat.card ↥P) := by
    have h1 : Nat.card ↥P = Nat.card ↥(pPrimeCore 2 ↥(B ⊓ centralizer ({t} : Set (MulAut T)))) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [h1]
    exact Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hcardPC : Nat.card ↥PC = Nat.card ↥P := by
    refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPCle).toEquiv).trans ?_
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun y hy => (hPC y hy).1)).toEquiv
  have hle : PC ≤ CFSG.oddCore ↥C :=
    CFSG.ABGLocalTools.le_oddCore_of_normal hnorm (hcardPC ▸ hcardP)
  rw [hodd, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro y hy
  have hyB := (hPC y hy).1
  have hyC : (⟨y, hyB⟩ : ↥B) ∈ C := hPCle (Subgroup.mem_subgroupOf.2 hy)
  have hmem : (⟨⟨y, hyB⟩, hyC⟩ : ↥C) ∈ PC := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hy
  rw [hle, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.2 (congrArg (fun z : ↥C => ((z : ↥B) : MulAut T)) hmem)

section Transport

variable {T T' : Type} [Group T] [Group T']

theorem congr_conj' (e : T ≃* T') (g : T) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem oddCoreIn_map {N N' : Type} [Group N] [Group N'] (Φ : N ≃* N') (B : Subgroup N) (t : N) :
    (oddCoreIn B t).map Φ.toMonoidHom = oddCoreIn (B.map Φ.toMonoidHom) (Φ t) := by
  have hC : (B ⊓ centralizer ({t} : Set N)).map Φ.toMonoidHom =
      B.map Φ.toMonoidHom ⊓ centralizer ({Φ t} : Set N') := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzB, hzt⟩ := Subgroup.mem_inf.1 hz
      refine Subgroup.mem_inf.2 ⟨⟨z, hzB, rfl⟩, ?_⟩
      rw [mem_centralizer_singleton_iff] at hzt ⊢
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hzt]
    · intro hy
      obtain ⟨⟨z, hzB, rfl⟩, hzt⟩ := Subgroup.mem_inf.1 hy
      refine ⟨z, Subgroup.mem_inf.2 ⟨hzB, ?_⟩, rfl⟩
      rw [mem_centralizer_singleton_iff] at hzt ⊢
      simp only [MulEquiv.coe_toMonoidHom] at hzt
      rw [← map_mul, ← map_mul] at hzt
      exact Φ.injective hzt
  set C : Subgroup N := B ⊓ centralizer ({t} : Set N) with hCdef
  set C' : Subgroup N' := B.map Φ.toMonoidHom ⊓ centralizer ({Φ t} : Set N') with hC'def
  let ψ : ↥C ≃* ↥C' := (Φ.subgroupMap C).trans (MulEquiv.subgroupCongr hC)
  have h := pPrimeCore_map_iso 2 ψ
  unfold oddCoreIn
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem kgAut_of_mulEquiv (e : T ≃* T') (h : KGAut T) : KGAut T' := by
  intro B' hB' t' htB' ht' I _ _ hI ψ' hψ' a ha y' hy'
  set Φ : MulAut T ≃* MulAut T' := MulAut.congr e with hΦ
  set B : Subgroup (MulAut T) := B'.map Φ.symm.toMonoidHom with hB
  have hBB' : B.map Φ.toMonoidHom = B' := by
    rw [hB, Subgroup.map_map]
    convert Subgroup.map_id B'
    ext x
    simp
  have hinn : (MulAut.conj : T →* MulAut T).range ≤ B := by
    rintro _ ⟨g, rfl⟩
    refine ⟨MulAut.conj (e g), hB' ⟨e g, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.symm_apply_eq, hΦ, congr_conj']
  set t : MulAut T := Φ.symm t' with ht
  have htB : t ∈ B := ⟨t', htB', rfl⟩
  have hto : orderOf t = 2 := by rw [ht, MulEquiv.orderOf_eq]; exact ht'
  set ψ : I →* MulAut T := Φ.symm.toMonoidHom.comp ψ' with hψdef
  have hψ : ∀ i, ψ i ∈ B ⊓ centralizer ({t} : Set (MulAut T)) := by
    intro i
    obtain ⟨hiB, hit⟩ := Subgroup.mem_inf.1 (hψ' i)
    refine Subgroup.mem_inf.2 ⟨⟨ψ' i, hiB, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff] at hit ⊢
    simp only [hψdef, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, ht]
    rw [← map_mul, ← map_mul, hit]
  have hy : Φ.symm y' ∈ oddCoreIn B t := by
    have hmap := oddCoreIn_map Φ B t
    have htt : Φ t = t' := by rw [ht, MulEquiv.apply_symm_apply]
    rw [hBB', htt] at hmap
    rw [← hmap] at hy'
    obtain ⟨y, hy, hyy⟩ := hy'
    have : y = Φ.symm y' := by rw [← hyy]; simp
    rw [← this]
    exact hy
  have h1 := h B hinn t htB hto I hI ψ hψ a ha _ hy
  simp only [hψdef, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at h1
  rw [← map_mul, ← map_mul] at h1
  exact Φ.symm.injective h1

end Transport

end SolvKG

end CFSG.GH74.Generic.BProg.B3
